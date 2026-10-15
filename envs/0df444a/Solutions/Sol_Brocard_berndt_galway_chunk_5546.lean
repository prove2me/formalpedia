-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5546
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:13:27.61769+00:00
-- url     : https://prove2.me/submissions/d5e4783e-231d-4096-95da-89a1d7d1830b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 997302158 ≤ n < 997482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 997303408 1250 997302158 997302223
    0x80301150c12030c0c0c0603050106080a1802011101140903090f010e15071403160b0f19020c0708060103140606010521060109030618030306141e15040305 68
    0x16800a00741520b020156102c0c00e1280e08040c010300601d2800c019201003a5448400c204016007040c404261a50010f000c801d40c041032550b40041c2903c418001850010002e40006000010203410081805e042d4a440807003500240c11120020019501d00d140910301a81c9070f800c802e0030207108002c1c1c44d80300c5c8950344c402c0b0000981540d000703000032490f042d1a441082e051b800b0304002ca0f01e408211940c14a4440d003400907003681c44813452081c0e8610014a0181810900100070040c046086818041309104024440580700780318140140c0d82c0250b075101c1c41c80c18541d5071107508148102800070080002014802442c0e034194030403104280c4500b001034995000b098000700042280c0c001c0702904001c0401c1d00c642000c0c060400b903400300e881340c44030002c0c0c402d0014030481541820061004050b450300c1024010881ca80010100301206000594182c000302c03510181008015075280361550f43e44600c00b00070000201d240c0da25550f9140c03994a6844280400102c04a40c19291a594184 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 997304658 1250 997303408 997303427
    0x180f0908030711160e0a0e0a080f12182a030a05070503010606020303011a070c0504090803090c0103060810050402041407020d031103150907090f0f211e1e08030115 72
    0x501d1105da000d9595442c04200806144203200441e201d040017400c0480d40c0c1d500186101d4141e840c0050751003440010355920018050b103810701900c080f1882c1c0506440106001c451251412400403000c2ca9659400c42c2c0c1a803541c0283e40e041c0911340c0c04200b00300c00054040d046480c00d80090021a0b41d9040598030b0b40000d2180c400a01c0e4019042a64046900c008284140c8207219000c445900d80c408030f001c844e40c5441c00c58010600109111001004000c210411002444c00740000d40c1880b04064845074130904030080151620045000c540d00e40c1c2002e06124400c00101c143c0f403400440003960381c0d00b003051440100b481c04040002c0003080b0344c1103c1c42a00b04a04031009050560180801480010014810000c50391008929906403440d0400203000b11090040f0b21800c2c2400c1c0004002c4129030a601d4441101d00400016154400030a01542011002d10f0254980c288054180c40c4201000c20f171741110b2149500f00200e50f070186068a400610881005d580f078002038440841 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 997305908 1250 997304658 997304669
    0x902040f020a03050a020a09030b04150204120201031a0310020d14090105100f030c0605030c1b030a0e03011415031507031a03030310030b0a0f0908030103050610180f090803071116 79
    0x141e001c07080c00802e1240303c92b82d8029104442413003c2c580e6408282e4100c1e0441d402011030002190703029000d42d07900d400b030340042040300480002054900030010780d5494000782c00d00141a008940345443e40c11550285200c003481412030080d07850030300aa10300800003100c0c20301c40d42c040b00070082140c102c0d0300c3c800010340382e00c01c0142104030305000054480703410042c00200c8800d030400038103800d98450000c03c541610241d004581f1801200006040400d09070f41441c00303603240180030807003001641d100d40e42210a040c104048042400d02180c203264121140120940d284020300c244242e044d0b0091741490702044605240800301e904060f1240320640700c0742c1005103404818408500e861800c00d130084154440011080001300010058444000066070180350100041041c4002884196803242c4d5000b5040d41c0c0030b04101c0d450300030305041c00480030b0096441c10309440580142d401090a42c1e04a055203071240b8003124000c000c20302e0401006028000e000e090034400203041000300036681d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 997307158 1250 997305908 997305917
    0x3070b0f01061b0618110915060403060c301802030c040e0f0a14070602011e0510090e0d0905010813030c0f02090103051c020309100e040902040f020a03050a020a 71
    0x2c1000c07010100d0701030004016203100e50340300d00c0c0e44035003080b07030785444001481000146e40c01600302082144101000b0b015000d90030310016070006d6582c50004032020f60303030721103000280c0000d588811108030003850b5002420001e56020316201d00c03c424055820032180c000240078420308125000c45902201000942541c0801400f01c1c0b1403400303421082442d140c160842e00c610140c1342c48079141c010600026a030702c100c005180034603d04144035500240074030380002d1111b10314110071408040d1510110340030069840b00440e80e20700141d600c44000b441101c205000041c1c01c01d0034503440c1c464060510020800525001400303500501c203c902c11207021041c5520010140c40540381c110400034212204202d2030140001030f034806900c2c1d4040c50045004215129080c000b4881150307400804406650083c025140d6a83d43c0920b203460664003460104450481030005c113003d0000d03500004d62082c180f01038006161750682c040d10700c041e40b5980902492f12440c078010700320320441c4454030014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 997308408 1250 997307158 997307177
    0x602070807120209040605061f0c11090c0403031d03240f1b0f040308030702060603190f1103010b03070303080603070e010f0504050c0d14071e09090c050d060803070b0f0106 76
    0x40051f402103a001c0005040d540380c184604102c1c2d6414600d10100c5004200c20303844080a00c40001c080149048003a42c0216460800d8007000c041c500aa01c8006c042000400c140245400110300300d110000020f0f08491403580200340c8110b8400c00d00d275020380e0601c81e078800216120307070901ca0309010340001c0ca18038103101440f1081856580c001041500010020000000000c00c00f800852150701d03903601400766030400d6000c2504002c00d13041c40002c3c0e45d00b0032400d50041000b01b200e034244150b00041da02d1595900360301103805000d1040c80c0c03170303814050800000700b03054008080c1d5100302030407001c1c1c60049481d0f0700c40d8010745101303005049034101314507000c0c843d50816078040342d045914804d0071406c00da201c1c0c46c90025036800c4c04c48840c00d501030005000d006900700d120302c111040350079080181080010001041c5003000d129040202e52038030240711615000703074211a140d4580300000d0000a884031140340e903980c000c0004482003204540054180a00700341a94181c82142e614007110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 997309658 1250 997308408 997308413
    0xc02032a010603051204090c0801032a0b0d0c030c21020f0f180108160e100e0d060e060a090f1106090a12020108070203092b0b01060207080712020904 66
    0x30102048484115640c0c812001c0701080c02044480710360310b100c10b500b6039140e0500400d00140c076040320242060000d180c00500c00108441e450092025800c0c0d071694064070842810240142c50394000c0031f0a000001c0e8458a5507400d812083d0031080ca61414040c1c4544006c0460703c00c40031144030540904410510787c1c0344c034241d03001010055800b08109060220f03001c002192030348070344c1d00390688002d0100070310001e50704000165400a402106511200c00c01d04001e00b810401e040303454400c00ca180b0724506181c2c026072400307119010152131010b88500d00e00d0107100078034035610001e19501c503240006041c4211405680744440d440140c0b4543c62205030b030b5015006850313070f00e02d5a10a0701400b000215440d81042c50004180c00240c01042000c2e60001401c822005460301d002c6400401002d00d954881000480c2480d483c1401c051040b45800e0b2006c0301010040c10051410201000014405900254210584516109440d43c00303545400c140030905c1e01d1076000b900300c40e2420001c2c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 997310908 1250 997309658 997309717
    0x100e0903041206020c01020a170f0606030a090303060b0d09061a01091e080d0f17062b02130b100c0b0c0f120405010204090e060108070e04140708060402040c0203 71
    0x1810301c180405170a01c0307100101142079030480d1100d030b00000e0000c031205041e003001e800d02c83d402c0310304291075040f141487c3c00070500c6880010141500c0980301ca04500c01c15100e580007100a2205101c841d03101c601b010005401f40940c10000e42d1118103010480e10741c1811301a0840c0301035016140c010405240c050311a420301605000c210012001a400103402072003413140741c24030040380c0d50f40c0440650350b00d8084d0034407044c00002910b9201100c00c200b016216894201110045500000d40e01e008041d210101400ad014000750400c84045050030682c0080c3c101e0315680d2421149004000800c2c80708803a0420245009003054451402241a15940328000c0c0180d10b00303413262501c2c112181d00c0c0c40900380c20545007102e107a03500160400c1818018452520490003550207400c00e9403401504994444550081d00c80c510003540128013000880034034030592040d0142514609681e66604540f1031500701d80a0707029a040c0b0480c104102e101000301e580c2d6800c1c030883c0d60140009141c80c0e05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 997312158 1250 997310908 997310939
    0xc0203030c090d0c18021c0c2a0807050604050c0d0b041b0503030a23090f0906040b10050c192a360603052a0414100e090304 55
    0xb1184c04061002059041220b03110301e11005100c1d00144c0c5e14500d4007041d0a403c1318411302071a04174540341c41e00140c0c2c0d9101d68240c0003402080380200841841000301c025040c3c600100820503000051901c0c1082000301300c05202c1c9000c2d8050340d0040e00d50805200303940349140d80040000001c0b0000800290000e460700c240302d00d1104d140b100b410780301c4003c02d15680c4140c0e4188086202200f00c0309500d810b00c5050060361180f215520b04000008022a0341180031403800d0788121500c000283d00c2c2d840c0d9500119036560020100746421710080005021a480248100348030f000d0910700e20001811945400041c075807200c0b070412280c0d50315154003820303804014811510802c000c000200b02c045407440600a5895100d5105020042e56000381c09010400c0c07451021401d00c0c1c0b0402c0421804510250491242e150001c1c0041001c6040031150860461599110341707428218408000c044101512620303400c00c8034915036441e813003034521010044820010b907600420003880703444a0300001d007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 997313408 1250 997312158 997312163
    0x709020424020705120c1e1003050a02091c060b0d0c03080304170a09050315010f1a0904020703030914010515040e010615050c150702030406030b0105070b0711010c0203030c090d 78
    0xd90101e501c43c40000c1d10b0340d51071607070f503181c031b6001120714a2a4640105c4072010320800750080500900900e012811510442010070107040d510000102d4103130803501100c4220100500b0104100810188030002a19013070090b20624a0401c08070314600741841c41d140f4080d0081c290404551031503903404a184e100800480d43c101c40502c120f41880c41000140603506526114607401d03508250515203401e084a01c901c441800d664010003590301411140d0003600c031007282000050065681d00162807040e4403e8a8116100140c08814150b1640c0150022880b0b8101c40c4a4050340403450f900b6180180d078040b2403008410400c0c080c502c0d003a40300c4500c01c0b06160003c01ca081d568000074030324403e043c650034040b9a001035640c0c1021421307c9017288000801d149003105080803140259a4040d6014460a1560301e07a00c0301110fa00600550b400168044800d90491a110800400c0d020100b1580400c96082c507071028815800401501d20030f42d83d1489903414545a101001292848a41d06 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 997314658 1250 997313408 997313413
    0x1d030304170a12060b030105100c0b0a090c080a051f090b0708060a03060f021e0301062307060507020106030303150302010203030f2805190b061909120f05070902042402 74
    0x43c00241610f80503441c0148481901e4607102e6240401780140c0e104017000c0c600420032030369421000111031951454219000d41d00029010000d840d0410241c030b0550843c0c0001d100d00c030049000c0050000c0c06080f4540707403500d01303010454008060020b5610391440188025403501c00540740f14030801c0025400200100981d41071943ca80321501202c86034414101d030190009100e1207506081d80111503503814010160b865589042c0004148000342035841e00c0750070b04021107410942c592410360f9603840d0403403030030803450500d100081d0090055103c105c0c003003810403a20b41845800c1d5403502d400c80303170180c001e5490b44d074500741d50b5045c45800030101158104400240d4500300170f443c822044034031010400084608200600b028a075049a619402c0d0f0303800c00d6000e04003a03c0d84025240c1c074000c5000a5004000d03d0801070b164007503180c01002a41182c0d8528005002c800e442400c4510b028101f5110a0303916510818160303c41c3c0e02850200e4411849c3c81c5854400000710058449242d105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 997315908 1250 997314658 997314677
    0x160609140109032406050a08103209060606030405030d0b0609130506010e120c01050f1909030b0a0903050f1308010509030715020306010206160e0306010906080105160206070e0a030c0602011d030304170a 89
    0x207801d40c0380390200d1600c804101440bc0003401c0c00200301080d00300108a400c00d08529282c0d032859038078801d05607105000c0d6154070a542e00303034071290300f90703203035010000e0021040c607060440200080c00101c5103540001d540e0030300d030f00650901c00149034450020401410343c00420000548030b50344a04400192104104460281d9407039141c1c12000744181c661341c0310422441c50a0920000e60050403608000f85401250000a900001103030307451041001c40070384403d280640c07003040c101103502c601519400c1900708105150301000404c1202c0c480d485a480c08441610030b042240012944140541d10000c00b04081c4005045d0000000e103242c5000d04411242c440801d0030440203034006601141c68000900500000707000e81648400c0d08031600480302d001c0700c4029600c0501a11007405e00085004074041611881100e50155802c42c151842c0c8950300c000090082074101c41162400c0c03503817207c10901120110880303001d5500544c0984640c14002e40d1618660b20006e01c001c18000e1100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 997317158 1250 997315908 997315961
    0x10e010c020f010e1906030c080a180f0f2003010c03020304020d0201200312070e03011802040506040209030304080604050d090806040602030c0d1508160609140109032406050a0810 79
    0x35034000140101e55070104408101203000327807003084080c060310003072410190241410b42e14a40c0e120701c5160401e0220b80303000c08900b05070104045000b000f802c25500502c40c0ba21124201038601107400c010f400070070006601c0c0c6021005c07400140c2e0000d40c00400c1e20301034405584554464010413a626108030440c0c10140706142c91a0b000c000803040e4178562130100000707a0341140d11000000402e90080c02032031180084d00101503448000213100d25960381c00302d0359648465060351000c1101504481d030f140e40380d03000075640b09001c61301141c583c03103120040d41c1c510384504e5481c000c0320070301c4006006030340311643c615000c2d4000600c0d69840313100502c07284680fa0f690b07000e40c0c80826a081819164103003003044842c10035001e01000e02d440c0c5050300c0100030503980203001c503084401205d100409040c00c074004071500b0b034107907101070581c900010204180341100c40746400c0b40c4042010401449a448003409900481d0740309109490f04880044804200d0a40000c1101c030a60540c4200825594 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 997318408 1250 997317158 997317199
    0x70c0b0f071b030c0c06080f131e03030504021c12030221040f020108092d0c030303250815061e0a03060f12020a03021210020d0902010e010c020f010e 66
    0x6210580025511384901014841e4900030180074102c6481c01c1c00d0149000f10003007190f80001b8010f0007900b4100504003050203c05540400c13400c2c0030100011440c1c069050007000f0f04011307201a171103460b18001000b07900e08001c25000c003840d4044418440c0f041c0031a4150020341100d0700e00f00e035444101000d00c080c1b002590407607108070711440b2219107000383c2c0d00004003510002450440c1d503038001034460100f0515201c514061401c200b9007000c110080041030307400e05440812440d050b10010044c000442c5403c0b106900701c03039161b20340504032a403008040701c40b01d200792284034084d40a0030090f80142080001003841c01501111f000e6045600c00d03000640341c1c0580c0c10b16000070b6840c030050085040c820300f100001c1c03080003013001c1c540701141c0008446030064400284211101c0815140c17406c2c09102c0d21045039402d040864882d001401080041d00264108038001a0007240c0000b056019008840f1400e0b00a441c8010100300702c401554400d07425801180d001d2100c006001c00a282c6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 997319658 1250 997318408 997318457
    0x150409020f03073b0a090f02091504050603071d100503180c28090203040809090610210b040221010b03010e0a020d0905100b0306070c0b0f07 62
    0x11902903a5a0314040c50000c140c15050311800000040d00b03071a03990380a034141321907900303200300c0c0b4110690000c0c004005228658654041e81c411170404503d40c00ca5650f07075000d045001c0007a030ba801c3c0c420640b08860300686c0b01e603009055006c601800803c040c00d2088030000e9500030000310002101c02100005130700400007040384000a00300004004a107105a03252544884400008004c191005030014801c6515a2200940003022040181c0c030380c510500399000524540c5030071540ea0815040140039640a03980d07d074059525500400c41a06103083c030001086c007296900341600c00003925090112600048946404e03850720001c4405e80d0707841c401440b0348182000400d41c3d259020008429101d0160302007402c070315050004004600190583c0d5a1250701c1450041c0c0e10100c000142009105000c1d0140c00c0303200d0001d540404181c9940800804002202102d01684d03d85408076082202c1071001014010b03e13034040350281c800456440d40204640c10441407140c43d412014650208 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 997320908 1250 997319658 997319677
    0x1e20060a060f080318100504030b07020715051603030b040b03070e010311030c0303030f100f06080711010203090c012109050304030c050f0d1e081b060105031b15040902 74
    0x5496904102d00041050a000180300040c069401d14900401c0c004491804a40041c0606109441218424850800c90300659070001c60184107017030000c4001c2d035600d01409405404041d60900c4202d0501a030150b48220021010145020543d40e4040380505000401940c00c0b40c1c6078180c210303155505020550140c81200140c0c0d009615500b03100341e12160942519000e03070003c1c2c01002e210b880100440e81d00c1109070820610544603003104540d8000c403580105024084080007051065100d801c041c05107803d0358130018001965860385081b8401a03a60307001d2503006110032005940604c0c062025104807020303500503420b07090802c806561000340116107503000040d050080000c40341e61000a410141d511500103110003011034404150040007034058403524600c0d0614180140100100591008039181c6800010981840d040c196001164090055900216003402c000501580e440b008003451003c484110003400103444c040c000e6904411010000840c5011041c0020241c291 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 997322158 1250 997320908 997320911
    0x5220213020318071d04080c070f060302190801140d1109160f0e010801050603131709100e03120310030602040e01090605040516030b030309040e0d0905011e20060a 72
    0x1a00c0350701c150801c11141c04c45c9030880c40c00c44811180e00306641c4210351042d880007009545480c02225680303080055802928180d0040e1000320f042540340c0c01130840000284140c0b070710522008015110f0b40070900a80d0241140c8106040c402d242405007900c0440c0501c214034505406130001c0703902ca81c0c0868002c0420110b030702e58001d1480d48010121720800e10362419444a804540000388020011701c100f40c41500080042074003090584e0b6000000c9034001c0503c03000030103071040940e4540080c1c04481c0b050100285171010315000c0e20106030701840c001d02819402105881e44981c41e0000b601d450086002010080005580fa10040024203c4160202260340c905900401501c54503004a405681040c09110f0140c1d03810344c4001d00d04029003004107031418a1804240386015603480e03542e0250419500e88130058000c00c2e0f1783e81c8010307641c3d51030600340c1d00c4c0d900558904030b01010742c40d00b581155031406500c500c01c0749201c02e2030548a0280c6031201808001c1ca1404100742d40501d0380c00e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 997323408 1250 997322158 997322191
    0x70c050616080c04060903080a0509061611031513240504050c010c020d03030b240c0709020a0503011e0902190905030f19020a080607050d0f052202130203 68
    0x1c0e00b004005030300401004400d4075060074588000d12861443c07100600700c150204611011600401c02d0751840d03c00546100e031a04e850400050100c1d002c20b905407000f42e001c0d407129002e401c0125501042c6c088020b20f030010354541414800c0c94074410310040e00c509030346a400f04500c1000034028280078040d0700700840c040c1060704000d420700d000054020b0502810301e00d00001a150f03030031400d0b0402e802d400d00007040755843d4086075640340c0e820322140c0845950340240c00032a00d00c034003800c084c0a000d000c0f00e05e00d40c0c0b10035001089200d681c0c040e0001c5402400100240000650f2900a40b0303440781c040c03540c8659503500002a6084443c100c0020310803464244131195101252400908c022001860705c1c812580c05641c45181c0325030307003602d0591311401c88402e64031000c50640081c684a030845040d0302c1e010301c00030708942103c43d95410142c01c0c4408520041c0c035a0017200e01945101941320701a400210f0503902c1e05450f480101d0f00b1043c84600940010b5641c4044d62040c10200c4084030b10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 997324658 1250 997323408 997323451
    0x405010617060306070f0818011d070f031a090a02040903030b12061b090a080a050606010909050c04090504030216060801080d0903051207050f010207050714031504060203070c0506 79
    0x4100030302c0d107400b0394080010001d00c5e580c000b02140d904030060501e2075658440d81d207100c24600035186104070960906d01a00c4500c1c0c400359000b60455030000994980ea40c60341940e8014442ea4400035044a81c0070100f0641c01c800030b92101c2e0400820340407500803800c1d0f07501107410340d0501201900800e940740b005090b2070070916110744080b011200500254a4445203250a824460000d03e021200210340c4080c0c0d505c9941c030410140800c90103c811540c1580303440356403403a04686213400515a070000107901101c13801002c0c010761400100070304060600d14042c004040045c000d0b41140b007510011415400a103141b030010b000340340d035491215810000d42070b25107044401c000041060214080010880208414161001d8070851541d188140e041c17503440d0800300c1c0e203004000c2d440010b00340e040240018561003240c010442d540c02c40d105907010103458007060320200d00c03c086404002400a60503900550b4040e0303140c01c001e05810303480c0d00d580303240c45012140200c800c482c1c0b920310340741e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 997325908 1250 997324658 997324697
    0x30127062705040f0b0721051f06020307030c031b0f02040e0a0b04060b0d081206010201150b0d1e150e2a030606070b13060c030203010f06140904050106 67
    0xc081096414402c60406564000c1042180748002d03000d1880000411003880c81078501074514100d0302062500d92001141e0320005001c151000c079030a0241600e072040712a03420b9035030403c5a9880d0099400e09203551002e5501d40744404044040080140030340300421700384211660411301820311042a1500c0d841072008494120395a4182c5a0140245d0800a0350305609194090350041000c0b80d01056913000c41e40346290302d000100308031000300c3d4201d4058490b054003072040300300b6030080c003900d000e0030240c0c1e0120b01c150040142c4020304001007001682150000140b8100c00c0b410004400d00840e506c004a81c41c0d100c0500010a40102c03c11241800040054100c20840455107500b034070141d00500281c40031031040a50103022002445943d11130302641d968540042142d40b440c40e100d84450024602d0b200100c0d080c5160266044685100e4401d07039050b0b40700019554049401c1400940340e00c49410494000c00303004111000d1251528041c07540202400c0e161200c01c005038286200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 997327158 1250 997325908 997325969
    0x1a0a020901022a210a030f17040f110f1c021503090a020108040f0f0b01080609010903090b0f07150212090a030e100201150806060a091103012706 64
    0x2500302c43d590b03112403868041409002100008440d04c424440d259400b2800c90140c02450000a000d840c190350107058009070f610040f44443d50751107140741d0881951281802007654090f00c0d40e000c600725100016100b801801c2e030385c00000c20f0703881d030303660588006907a10072200c50200e44901c0700280c040c03c500b010100a408502440c0190b070035490205002c44c0e031909040f4010741002220008582800700d084100c0310f426030080400305210710203051103904801c00b0700c10074409100e864005414824103210f0406916810382d80c4160003850300307160348016041103145080010702000140f0004920a90450f00340100080243e1030b004251010002254014080412504140070040c0041e40c452000f0200b01412100b42c0301c00116440c04034010011403586081c01b1501c90320109034401c0000340340d4840c0c0300032200146600d8031080c1c8801a52842484000d0641042c4014403403100691030740310800c1d08081d010080e13159600140300541d00c5a0340300b20050307070904030f030707007445040c10001c81 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 997328408 1250 997327158 997327183
    0x90b01020f0a06020a14040b18040b0907030e070b030906070206070c05030a0c0c2610152913050f012a050106050d1401060e010513091a0a02090102 65
    0x800352003242501e00c1d51290b18030000181259800198072a4007401100b0142d50303070030b40d80c0d04181c8450b1a00b0340c0c038646502001ca1a0407140c6100100348842c503080c0200c0c02981c001421409103912590f13405c1d0080c01c20341007030421a01407600e01040701d10300f50020354400c1c1c00e030000805003410040800b07420078401508100810120700c55003800300e01c00100b100c55420282c41c1c0000c0c503003120b04040a1500461b04492510b00c0392002c21459140c1c01d0075450400d8071881c00751043c02940e200d803c011540b401d11207801014400d1030805c03134640c06c40c0d145228001d0541e03c440f400c0980740b03201070305507002c1748451000b4400d0b001c05007c0380c03c04000e005001c80007820010b40350080c5101c1e095900c41c10700301d4441800854944c2c1c138100301081d00030400501000c2c1c04007030580071510b46640366a40c0480500250b61070500006200000b40b0003d80c100c0380040d11f00000745e0001c6112070045d0007009420b60710615280980242148114182841100521030060300d03403034410002800e185200101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 997329658 1250 997328408 997328413
    0x2130f05010f140d110a02010b0301060b090312030402150c150a11030c0a0201320a1104052803080316030b03030405040f0615111608100903020a0b040606090b0102 72
    0x81141d01504000c040664283e0951115118103000c1c02d1200680380d000311100740d001000c5070701c0a025405401102c609001207000f401040d4a035a40d00e102030003152091703a4180e118000d8107443e001040021900603001a10f0060001c062046004940e8415214000d15a10036a405071f0302c004511034903604841140014050180703245115400d40c000607003a03503000310000803030740725090003507102c05159005e42480251020754604a00c4c240d1502211031100c00c24142e0019500d0b000070f204c1d503510180d40d0303a101c0d0b081c207082506000c10304846450707100c00320502000081018119000d4440214401d00e011a030307910f022203030f6001e00c01a901c0d0b001c080c075082451203030f0039a4010064405580041e40d0010f11050300104030005018164402100001880d002690b07556104d9012000407203400220b80d014401074410004500e507a104005491300905040002d1061a80240c2c6229010748119040030360b450f00c6210b1546800d95040300c01e10f07541d23102040401c01c1390081c03c7c2c03041024000f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 997330908 1250 997329658 997329677
    0x10203040f0201080c13060e0319051203060d0f081e0a090e090304230a08120f0313021e030c0f0102030f030a11040803040f09090f060e030d02130f0501 67
    0x1145034108140c541d0003414008200006a41480340c3c81c161501161100d56640c42590b8499015003074480600d4040d00a0140c4403100c24a030510b11020644264018002d28508600c810314500503000039001a600c10400c078042004901c1c043c00c0403015901030b81c0320603644c507120241101c503400442c40807001030409002d44101d154204d5a140d048510b08050754078030b6502c81101900307500c101e4001c00580c80401e40c1c0201c03032041c100d0081c1507c0000b07444852020340c581005aa41c0c01c401c581c1d0f500e8501081048241c4035150001564004030317000840f0300c002e034941c2e0002d20612401001c50f41241e810300320814052034200081d40c01c071001070b14008500c00030540001d40364130540109908911000010809071450359001e1450100420401c030384841e2111809910380e4003074030036081022415440402c0d6540d5031300c2156006640403150320400c0c03105035510300c041c100307171940391915003c00c0c40200d00f031240c5400108541c508812541182500f4103030780c44c600c0406034000c01c1c1007000091 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 997332158 1250 997330908 997330913
    0x109061409010804030e030115030c0b190315090219120b01091a040815191a0d030c02031207051513030813020d060e061f05010e19030b0405060901020304 68
    0x20450749440c10a191150584d0340c0c500b0705403a0104009070682c0c0640c43c200c1e503100c41c0c0c480307106100107483c441e8040032460380c2da8040302c0c1c03124007070034081d5400d64203440b01e0560041d00039070000040719001040403c115954010380c008a030000303020b54035109102c0790f04054469001d1283d440804140f1000c0040780d14400001300710000500035101c2000c2440e0100c41c031003009000703a0b8014200c280403030384880b00301605400103800075204c1014910300240529201c2d88140260764950744c0c80f48130060150300a100b00030422051803400e50510030305140100c05a24148001d04400010b00102c83e69044985030080c584038001100301c00840111040c014503580340e000d0b0503012a00361500c003c10f900c5640402c403901d0440031000f50700810f041c486004000c426044040003000f03000070344090b50f0720100160050000c050f40300e05406010b1030b060001c0d40c0070304e581101c400380203441d40320403041c0d4640710a00075a43d60001d075a11142c1c141000100034041000710303441440e01c8000d500311b08155 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 997333408 1250 997332158 997332197
    0x2d081504110a0e130606091d13080703170c04330e03030d022b0b0a0608190509011a03070e0105040b180403030903030c170c0d0213080309010906 64
    0x500907100b00181c1c044049115550105290414020349504001440d65014040e0034281544901008d0368000c04160310100c2190404510034a1518003540040c29150344952881e03122070750460502842000300c45c2c000c460010710703d1007a4583c02c1d20b140e4841c1000342c000b500280c41e00c1100c0c102d1300c0d41058014400b1b10380500801c1c42c600e60400c0100078043c180081d00311700480201c00344c050306c049010f100a40407002c0005410551074000c0c100200c101d4100c50903504071032035454111407280f800304840c0d4800ea0009512801410349041caa074007582130b24090b01c0090f56240c4c0705a44a118035040100c0005c940b4000d100308400600c81c00c2d00c0e110b20132980e05014410070344526a1101900120b48031080c849005460022004496240c40d19026000f0007100d6026000030789414034200c1041d0144ed014204151030040d8681c16685041c01c04a041e0701c1541d04c0401190203100c5011000403890314030018003184800385448100c141c00042c5500101d80c0600b04001c102c0144e28402040d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 997334658 1250 997333408 997333417
    0x1011090d03090b180103150320011803030203030a0e03040e04030507020d0f0303020c100c0e041d0703050d020114070539011e0c020304062d08150411 66
    0x3510111545401414152044007483e4032000c1800d900065075540310300300707010101038a6001d8804102044141d603c04900485d14080140302c0190303164802000140d500000740140c805240c0143c490311004e95104a6071101d502c218050380c404800d00003a035041d8080c580303021008000660605180510303810240700080c0010b01803150001300310085d501d840760603801494010480100700300e00c0d850020020350002c1d42040300c5000342030018400712134a0055000d8134505a440c2c0b0054450402048001c10140c07400d43c030015441101d6a00c06ca90030b01c50388000b103001e94050030205c4c010078006030130b40d8001251981c0a403044010410401e4011094444012020100726200c85101ca002c90100d07a1401058054130404000041c10140540100c540c00301081c000300200038202e8200b109455481002d0400768005000600009104001ba0406450041c40361200401c0c0505c500c202a03400b0400e0100003101403003001046440c00b003000c40b041c2001c1d2010080c03c1c10230f45014000d8041d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 997335908 1250 997334658 997334677
    0x801060e0a020d0b1908100212070f0c0b10090f090203031b0c12060f010608010501080705180a150306080c130c05041e030303061d0a0b03072402330c1207030903021011 74
    0x40d520000354bd5510450b50039a90950100b150703011801c0c800300d40e1140801a104c1e000700e5500340090424100c0490082d140050388c044c00860501c640100d03045d903983c03100c088409045c41f41c1900c4040aa48400c0c600c00fa800300c0201604003030030000c0ba000d000342c805030042400c0c444280c0040000382d912030500d5920110034a0503503190400201060062031001c500241c0c009209140400c0003000640c485c110200e99480070002c2943e40d40b8820785400c04c1c5242298400e0b40383e00403044c11107151304070000d1080039103401c5180c6034841e500304803000c403500085a607a40e07810b02c0500c1050780612807c8042d1031880c0c4412a40a22101c14100e1080000c1001c000300b61100081c00c401c3d00c0c00c01050010b071080b0491045805101c5590307d1494030200b489000611130140c0d6191600041100501d0105c55294031911040325201f402c0562100030f040f901c041c1c0320400c0110030700b01502c0e2005001c2c0040d035902103501119410020300d8280d2651450a82528200741d410600400c18100d49c2041ca = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 997337158 1250 997335908 997335917
    0x3110d1202071104050907050438030f070e1f0305101a0607060e0c04020703200309040f020309010e16120c05030f03130801060e0a020d0b190810021207 67
    0xa0162410640c03150750f900241da046424207017407090b5010f0108409041e2142581d08100081407200400d00b017400005400c4140f08c581d83c0d00e0f0000b0450301614641204010301111070042d10110814584040da60180c07048504d5402807141c1c1500910000310005503003030400040b541540c44a03502e41c450424036200d8a130355203100c41d01d0480708900c001c0306848000c05041d150b44203030500102501e80e980c420b00301b50148a0404005141610030341c4c3c002a0140d9a034103c4911005940d0070b08081d02014070010f100c00e1201e0070700c079901c900908903c002810340242e200c0c24850030140c01d460302c40d101090650000403c008900b00142c0c8d503041256003e0688051100f00703810f01c00204801508060381600401004110942c0d00100604002c034034000c091485a80d1022a182280c00502840c10b01d2540000400d1466800b034001e00ba0b4184840700004840b191f49001604403540d41c8100d40d4020f20f4042c080200160500207404c1c5100c2e06281985040000000d00342082c0c2c1c014450b00a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 997338408 1250 997337158 997337167
    0x90907050c070f0909060b030d0e09070203040e0103140607080402060d1a030111040303080702030702090714190f1d3d0306030c051806040e160e010303110d1202 71
    0x20700401c215801886503910748411143c0b00c011080240c02444400e603090b6007800002038182c14000b9000e034104c809a0340b18440e10351608100107007990f019007a941184001e0002240320012200014000c6204000d110398001c2401d03540b50510100400312030070710100340100005611443c0480340d5401d228800021400228884060f2404455840c250103619040f2201a1200b114000f0429280651554845540d80710700c12039581c400d0640003904407090001040c2d540e03000308074203030550b06a907a007e403c060009603400d0340200ca40045200144603066480301b81c0e40c0140182d20200c0c1c1c1c040240381c08100c41400728401c01408242c102c88030340100300500800c18982c0c41046056141e1030305a85403058080010301502e4076002c1940c80186d0039800041d549032249032240f42c0750171b00e041213550b0380d15602000010038994403991413a01442112400440040c04040040d1810222500480d41182001842c00510805d4050700d54800480c2d904c00d184c1002c1d011030305415031900560349 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 997339658 1250 997338408 997338427
    0x21509010206190f1d0712120f14030f0106030518030f09060f0c060103031704030e04110f0f030a0f020f12070320120c090a050906060c07120302010605010509090705 73
    0x415034071070600502c43c5011710403100c0440f94520b81101c81c01c0c80c1c04880030591240a40102404c00c000024002624040d20390a2907001341e5807175240801604186043c00720308030075900d441e0300854503100d5400392007005101c010342612400d60814082c0304080c0407001c0360410240d49218440d0300d0b80d49101c2c0420410701950302d500840703560700b0f0003080c505c2d01d6001c0a0080381c0d035080d0a000403000b044070b15000d0a0340300000c0140502c616016581c0e9051400c04000b408014000548542a0041b0800201162410200040c0120744619000c1543c3e85400200c07941120711a90890000c0d90040000e4681494081c0c20b50700c0041d06200c01c039041d5298010103800500881480303201409421514030b08442150b406002c041c1c1200600400551741c0341c21405462260300001540101190410b00042c105141010741c00380c0041c101d28a02858070b400b1600c1c10030315910003010444039445070070402d03074203000f500010082030a1450414682d600098418200200001e08102d800700c2c08180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 997340908 1250 997339658 997339661
    0x708030f0f0d060f031a100b0c25081b01020303011502010f0908180a0e070c030509030105040b0103152003070e192603040312181202150901020619 65
    0x1d42c4804400400c0301503540e132201d0400d03148610040e41d581b41c5d00945442c0f58420110018850f034181e6081c240303481d060500084140d04568881105440340413148100320080d680740034141000300304182c03001443c1000061a1903001041c2c040c11310b08006900403a030f60000141c906440c800004902d21080310314040740104111902501564100f603210010300039803000508407103002040903120801c104d814810441442d1168101e1410f000300002c060501c11445080c0c07446c407d14100e45803410303800020b825250151405c0c4c0c2c242614170010810005200c64889900741042014482070b565a90311440d0050652114100400c00100061100d031080b00005009003000301f41c1500b108241e05c02c603c4119482c05403094004070300105030390401c1150360311020700142100441c9001e0540e900c210683c064900c580e014071004089101404101c485400044d24009011203c0141d0034010010301d10b014608001c114071040008139400c5e6408504d10398450ba502c00321544405185032240d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 997342158 1250 997340908 997340917
    0xb1509060d1d0d172d371d0303010501031e0f0c03050c090a0b0a091512050c030f0601080405030d02041e080c09070c080d060b09040c020708030f0f 65
    0xd0342405191a50440b454021101942c180b414014040f000d649107020304003103a0012801845011890812001d81000000172560044052240000503140b481c1c8040300001002135602007441075840c4c4501183e40c921401d002d0500000850404110314001c480d03c921041c05900d04040d12442549e11150b01a0700f1081904040c2100300100310210380d000c0010a800c900400c0005d0420011a8030321440005440c540c42d0001c083c03083e00342c81c054002485074001010380c800d00454506c009980d05403541c10089101440d11845000240740b00c10302c0403541c008000c80b000c07010600070701007010506528035078000300078203001c000307500d85e402c1c00c6103580a096541c0481c0b500000b004283c1d10141c288004203021201034a800e01621480000d880b0107819074a03503001106c010004212034401c51003002482d008892044c50002e500c200e5100741c9580e900002c0c42407030f0004843d0340ca800e06124800320080d441c03014000441c2084903440d00c82c8200a50782654440c0030034020702d40c4100c0340494 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 997343408 1250 997342158 997342211
    0x15011d1503161409030304140d050313140a03110d170c070509010e090c09040f021e1c0c05060c0f1615090e07032a030b1509060d 57
    0x180d4481c54141c00c0d8854810008032282d000402e820421500c2c109403000342e4486550041c061800e06050024903a4203040e80034003a60300441c41c1031240e02055042c0010300c2c6d03d41801c42c041200741e0074020f0410b00719141c8001140150b40340039040021888400f490a000304040b6901113208040d0309010225101c03d0355041110f401c0099225510000000c0715030880da8181c803030540d207030b0365800600c2501100702c034040d5140d044010a400107240071191164000d10600c400441a81d0030780100d0075291160200601d000144481802c0629100d03060b40114218901e28201c09102681c49a286040c144141409040041124074034210244065400b40040d0700460b601c2d041e8405c18801c80e042c1502c07903030f91503003d10040842d5051150301800f0503103a002655503003d4842c0c0b4821001004c540c81c0c00c1c03201a4102c0d4980604411514802c100c13246141d80200b0003460003820007128130198440310140c08020468000561a02001c0e12050a242000062102c001660910346c4100e101d444 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 997344658 1250 997343408 997343449
    0x90b0a050d0e0105090d0c0809040c0504031415090307020a270f05060f06040f03020907210501060f03090201120e030c0604140601140607020405070201200d0515011d 73
    0x14440585415400640300e0b40c404021110320054146c03003a50070050a0b2400b40ca41842081407540d41d0600790817480c2510002d2500500d0320ba5252141c2601c46c905107003e8011750026510410000c918001ca01c1d000b41c0c1d800003840c68481d85034005041300312148a80c105000d94441101c0c200e007103015003030402c25060301007031000144000001c002030500f220b040e84180700402002d040fa08265095905a40e242c401d40040e09085400b040980c6400a0603c01044460a039030812003002180480300c0d40107107a40440e0715410140c01820282448d0b941100301481e00c400000940e03441408480b1446050b100044c04041c2c104110f411441a0030308044c00740b00e0641844204601c04134104141000f440503a8282c0e601c2d00c10341d10703454003980512540a40144180400f61400303a10545c0c2100c004d000018441c5c6846494921042c60511010f403960f4000c14181340320320290140550041144000d214030381c0c0c0368000a04495804001441c45500d44420702003140c0b2401050b01e410324031001c0e07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 997345908 1250 997344658 997344671
    0x50d060e010e0316020405072a080904061203080105060c031e040e130b0c03150f130c0f02011b0c080703050405040203010b0c0c01080f13030e0d050102070506010f0303090b0a050d 79
    0xc518107003108134032040340110302e0000014001c030b00c5250500c25800b0900403c0100c00001e400c20011700c1400030040e6101d032000c002c4900b26658501c1004020224030701d030710700200e0030390901804020050388414081c0d5020000200b9070b040100485481e45142186100090004c0c81030001c9805181c0281000f06a1801408504c0421150050010744246a00721450f40c544c0840b000f0b50209452142844000100c03405280c5010001c011140b40043d0410443c8441c40b00f80d01d080e22803508550010400b41103548004a90a01411505ca0007082075509010f0011100070305030a160b084c0605000000309007035041610960441c2c004020081c425501c958640d0030342491a800400401c0c40c51042c0f0010b4402c03035000314859407040f800300d450030030f03d40d91783c0c110604060480764046040022000d070303040c00e270781d543c50f559240313640294001a00c809081c80c10380d28010040e0802401038504c03160801c006a440071241c0191844401c04648a80500c3d105451500590f680111a5418800c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 997347158 1250 997345908 997345927
    0x309050a0b090918060721050420010c050a08070f170306011106270307050a20031f0c17041208060f010507060905150c07030207060801050d060e010e03 67
    0xe03021180c0e0840e0f8030340003515014200c402e8030f00d07040d42d500019007201d80000e444a004d12202c400540b084150304100200c200c00410403107204440071244120360516a0310480394801c100d0000c10707000e0825048114064403000d5840c048444020702d9079000041a804020300090a542c4d291790201990745101140020106290421122940040c094109141c82c641000582d90b0280b034170443c401a203504000d540c80443c0040084180651204119240000360104110030030355004800c070703c20010041d010111140100c541440c0300750300074221840d102a40b220080f05005d404940050110066182503c1c003c09039a801c54501e0801c00400c020700c0710699030701d80301d031500780d88180150b03803032508100c203900302c80024034001401402071400158596100000311405030f0121410b0600d889000c408801e0101d5a120420101042c0030041640400c0140050403da0038613100c00d40c108000b00710403103101c0d100989400d403141c2003100c5440d000c0d40310340340e000714500c140c035510401c09 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 997348408 1250 997347158 997347179
    0x20f07030306060e090c1c11040f0915150e010912300f1103070804060c2006073302040602060a2309100203150f010819090309050a 58
    0x2c1c80b50f14041000c41050900c5490302d00c0440b44103145500003541066070031007a4103020007140f1800071449548002d000c6100c824000684001c0c81c401803034502c207d05202003102565280d011901040303d541c04140f00d60341003181400c590005600d00f40c3e42041c403460048900b82c00701c0d0b00607031200140000840034054078035500b0f038110f0348010101d9024403091011070150080918140001248407400300c1d440b074070414043e4040840b42003200d04082c0035482c0d0900b961711561045000c030304112001e40402c182c0c2054002081013624844502c0703004030011814038855104000c00c40003600d031001e41d0210002840c040760402d81e00380e0690268250714548020341c45402140050710806000580240c49406080341c0210780020000ca01852001001d0048102a02d0a0240c0c002c0a510144908040c4043c5110340d008100403100c030f4070b00324144035090101c544070504000c0d0f1101045004802c44031204c50400d060a40000c074030015040c03c441d01c2442c1e81060350702258011001400e107000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 997349658 1250 997348408 997348421
    0x6120b0a06050a110c1f0917160e010b0406030207050f060c09030c042304030203190f030c02030a08042003031303050f1f020a050c1501030b071719020f070303 70
    0x19900c400c0744074074a02c049965580340e000c0c121980003200c0300e0031803101d06e0020311001201455041140e41c2a458001a202142540c40999000d92051900c41020b4100d84400c00c014001d441d8611615414000c00400c2c3e4810f0380110824550005020810407404111100110f1002d4083d209907040403d5402c0d45503002c4040389200e0300c5051404e4440b842c191040d10400c800601c0c205c00076030707450340401d00e920000030400e0741035000510020001003690990400c061459950b8010b100c0c2c20800041d04448040301101d003150b0080c421074091036000b40c000f94016070003d90380c84c01b0910404d82c1c204100f1b041c80c80c0e070b901404086001c200c0804c400b000001601c0c45202902d0055004134400d55070b810391451150030000907404030440b030480039070041000e55402d203011898446103008140c035002c6140c01c1e1500c00d118820041091200345100c1542010041c80d00103071140d014400d44000c40301c094880c52101c2c0015001c0285510b0660495460004d40840e03542c48600c141000307002002c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 997350908 1250 997349658 997349677
    0xe0f011404021201210c0609091a060703111011090f0d1505070306031a1009021c1107020d08040303172202032b03060504060501050406120b0a0605 65
    0x11240c511140d645414000d48030400c0030340c0d032a1442a840d003611040c51810441407a82d40714044582c0b000825000b12440003c1c00840e11030a501a161001d030800b21030342d0040c8080484001303c07030070186035110011a400950075203403050003407203100030941c1031040d0400ba03a5142c900d001c0b5900e40ca07040000c040c0505080449103245d0040100d0180401501d1101c4000e2420807810748000c02c0d1000c682c80103400000514001070059126a10711410304280100c504103440c1803410401c0c0c02042058030341c0134180c0f516055081c820807915a141d5980184100000d55440748000781c0300c0b080b024259212150010002014180e060403c4219680503020a90004203400d1000b02248050064580140b101d2a04145504525010764030820b00016013280c0c18051400c3d480c208840f03e1300030441d210740c0325001c42c4031a90b400f60054200c1e9100c1c0c0c08140550305051080000b030f80c11000783c40454032282032910794030010210700001080d40c40c0245074048003250012414075400386c050000802c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 997352158 1250 997350908 997350929
    0x406060806011401090f061b050109050a03030f050a1a01050d0e1b01080108070f1401021e01020406021e06010603270309030b07030b1521090f0705090705031308040e0f01 75
    0x907241e218211a0351a9030050038085024423a0721086440302409841203240600000140e980d140c0d81d44500349503c0b2481540065100c019070b2101c071055208803500558404010000034145000000c05100340d420241e0601402180480d59103555811006c94501d111040e102e000423103c0f0143d07240240c9400150024011000109030b208000441d0b0090342e500d6240344480e580350165801c1c00c4022a400d003030440c0101071006500346804440c111401034800c00140e01d0b10304288000b403600e1102035000c0020034222140201d140d43c003007540b6043d91b1151802260b0840d41c17555034840304a50035449064049000441c03010301d0b92244e031200c15a8814001e0141e180c0310400110160344203610103035444030304510501001c000300b4004104c2c2240036080c202910303040002c1001040350447c2c0022140e08060323408244d40c8414481c41001d4201211002c50750308100340001e002f400024008055900d05a40b210b00344101070083e03600408604990001600e13002e0001da000200a1184034040f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 997353408 1250 997352158 997352177
    0xb0420031204030317130210050702100314060a12260a02060f011205032d130302120f100e070b0712030e010c0c0f060608030a0804110901030f0305030406060806011401 74
    0x40c11000c401e240181404090007218030346c66020003c0003008034403250284481046a41d00680780c1441c450b82e111141d80f800201015440124070507407200400c9039124440d90032003407103948015903c2d58641038000d5802104250010300f03c00c0d0007072003503440340030746000440e91514481c2c0c0011414400e695603103d40d10180d80e20006034040440c8064010080c1d002031080308c00180c00300d03980854140d41c1c1e8400340b0040300b19070380c4170403e0b030f00c1100500d5400d0103900e81803040d8248038064405454040000f4440301e151a410280c54030840170341492050344403005a070002000304010f0025004280050390344071140c0c03400245004030048800c01007400e00c81c8072410a8810b1240c240070440d1030302c540301100741e15035550340410300f10f01d400c959150780c960000c6410300c02000a4100919261103500c035070b08082c103050f21040b0914090500c10640c0000500009119158201110760301d42025a1692a24a4100054650b64200e12110302c54000001b45d0420b46a9040190724020389841148 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 997354658 1250 997353408 997353437
    0xe0c0d0603082701171e01090902190e16110d0e0915010504060513031a1e01050a140d050610140d08041505430b04200312040303 57
    0x1224070f886a0b07180460344c0b410009100b95139482015910804102030203141981c4445889041c44080e080501c00a640da4044802c608000300e04040f0070540c841c4050a5510300312032103000501c001c03c0755075880185580c44481c01d0045c003000e5805041202501c01d130300c4590710000c05089410050340d119079000d0f400300702c58420310807000700b0000044c3e6400e403615041c101c00f6112079012180004411412500c001702007041200164061110f4003412285420024948030782129004000f40451001400400c00390362403464031030484524560304413903030303080d140042c0f0361844a600c05465030013801e0802c4020340710184004150f0741d440500c00d40c0409540c003440007440010900804c00c9a0400007403040a080c802c090940050f98988140340410b103107000c09031400680d10510301d000070140c0b48072202d901d811074503181c003000c805120426001d0782c44400c001c03003011708060b01e440895010040001903a0280c010700b900050101c0d40501d001c1301261005030b01c00d04c0141c00060054000d01d10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 997355908 1250 997354658 997354717
    0x40302040b03070b0f1306031b0f0912120908070f030213090f060e0708032505071a0c0106061e0305150a080304090509150712021201080d14130e0c0d060308 69
    0x4032510085444089803109c00c003d6a90190f152400414000e1040d03000841c40524010f203c907940c8541125009000d020402400c000c0594204003402d07040444244014504040c01d5411241c04403001c2c0207401c0080d007030500400707450a020301015000000c1005101003a00401040b0b10043c04441d6032503650302e00d1580fa400380007a0020982804800c005035018030480380d00300203000e9810381b541d0302d42d41c0c00380500400a00e100c0c03030140340022a11004600c0c0a20a08000b401c007814103920100d00c1d50300000c11f00c545202c4180c10f15a81d100400c0c03203203001c021421142240904129000b5449207111a542d0700203115180c0c90b141080b0024510840c003042107180c109107a8059101a00c0d4002e0580d80803250903d94901107900f8005801e840f44800800d80c001c00c8008042c01c0c1c4410042c070700400201035104007565056042050034041c1a05200e00c130201c1c3c990300310203141520b500108155038407a9150f038481003810180003009000060004084d0a650b08480000c804414a11340c1c0c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 997357158 1250 997355908 997355921
    0x20c0a05060f0f092806020d0906050a02010e0708010915180b07020a0615140406030b1b0408030a090e0f0c040e09010b1f11010e03040302040b03070b0f130603 70
    0x19048102800340501c07100c0750001400200001800660800743e130540810144a035169610382851459800e00081c41402c040d41c80c0640190b01c0a0041c0e110315210150007900c40b03104039820802d00044400d0704920070350100d60309008240548111aa0380c0341c4080c0602406141905c10844055025000c030790540328800701026580040c81900d901903c40c4020243c00400e40001d40c0103107459440000d8a03031280099507051100711030002402c050082c14007070070501c0044d000e540f8001c014000704e00301203402648a04c10306100080c400f014420b41c40580283d90100d01144404039000c100d00c2d0308100d0810503204071002018007580c64041c5420f0b41d00040d100ca044e440300801c014010300340001d40c4250701038184800802c03213100c1000441d40700300350320035030851100ba900d0f4410062544040c003400c00315000300003031101682c0d00104588a00c00e62000901ca6075640345400540d460521203800105202541552110b030003c2c0780c0d5900da40224040c004030442d007034010170071900911072003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 997358408 1250 997357158 997357169
    0x20901081c1d12190b100603180b06030a0b041a1b0406140f0d06150903020a0e04060e0304060819020a08270304060203090406080c100807030f051303020c0a 69
    0xc10402602c0903c001c1030101e808400c80c1d4000d64203c040100d00324809600003520a203032004d010f1800300007606000c80c942e0000405c050401c5c20400e403c100c242a110718442d04228000c0e4141c5031580040c1c9400c401d000010f01c03000b111020002844200d560f8886611250380103000d10740c0c1c075032901c0c0b005910260140f0307003d800144000d000342032081825414a20418440c0e0b0301d84001646890303181e0b0001c190384420389031500c60a002242c0324155403041107070207003003c040c00d80c20356000600b40318090241c8820030b02c81c040081c2c2885691740011892109000c1079960b41ca1700c0d07c03001881e01c00c045814894010020441e0720b90041c1d41d100f160092541540d46440d1070311860301211410b5494418012028580c07100160440701c180020801800e1540013513a17903551030030901c4207075019940080d4458100000d140091b445500d50701550382c4207031900142545d141d542c20b600814054000100743c0d8030701001c21440741545960101b02034000d1b021075000034040f80c1041150012070289 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 997359658 1250 997358408 997358447
    0x8062a0f030f220f122607210e07050f1509060f1204140a03090605070f020a08030a0e03060408040302010c03110a142e090c0e0c2a0c1c020901081c 65
    0xc6c031004541c0b81c20300c160410210300e4908480220030f40301c2440c4804160740903609980d40e07880d04005120412040004100603140103d0b003040a400050020307005502a007132007000090f0480050340c44c0b00c01c035006482907221b0315484500020015210410440d030481d0560f880d040e075100d03403190000d42c00003000d5056a810f00781c14201081111190071000044a271540881c0141c4016500c0f04214005007100c2001580c41d4010114002c00c0e440d529072090780070350820001e01020650490807541a40c2d020700f000200a10075180498002419080380307403040c0100e051900800101c1807100c89040c265400b100c9a10350003000c45a084450300d22440b00d0315041a03083ca000f540c0300e400c400c8140303014103010380865940da00000706a01040342c1c0480c01c0c090001d10b44405d0304d0074854500c09440d403051201c0843e420282c0b80d50381c842c0668a41031003964817881761031413401c000c3d04810f90346034060142499543c1d601544d50b507940d00301e0080720201450b8008012054450320100c0c0e07124940400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 997360908 1250 997359658 997359707
    0x110714010b01091d280603141612020105031902160201030b2e09090e010203010f080304030c03031808030705010c030c1704060905010608062a0f030f220f12 69
    0x14113000000d1803170419081da030302c041070400d4145114821440114001d5403402800b0b0340c0c410107141400c007401503e4212072840030b0309101c1c0d0780501d06444500350707080c00c28a81d02d4445416421403d054582c0c441c45550002481e074111042d21000c400500d0310030389040c842154000104076070148054840c107501c602501c034280380b003414100c01540e41c0c0c4881c2005034000c2d803601d8005050350249a09074046a4001004002d00510b40d00030390300819284c000313036081c5415551000c1911520744000b40030031082031030b83ca40400c0c1c2006150014600081140c0d5148203900e0400d020b444254070410100f403804030f00c070240900515080304007070516480e000c8540d8880d99001e004103444030042c0e807290369600001c605c450382006101d001d4500d03a451003080da400c0750060100306000d0304581c20711540600504010410078025240c2243c0381090250341551042c00001620420700c00c0041c500c030341c80200c07005000885c903075207403141c2c0a51404550750301030040035540611080f45c102c0d0301111204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 997362158 1250 997360908 997360921
    0x61104030b060409061d01051f03050d030e10020c15061903020405040501090b0c1306181716090e0609060115110c0a150e01080702030d110714010b01091d 68
    0x4d00c03c1041c20720a5000092268820440401800c04d01044070003980d5a0018000030402c08114015010b00b610840082d01c1e007035035501521000f0300c2d5000001c0c9511594500c410030340502c001c04032580c18000464861403001011599080020b144141920402c1c0215115080c4070040124902223082e4001016140d5401d220003000000c0050b201c070355940d02d113940000c1d1018102405241841541925002507045200d1882072552103042800000061058000300d1f01d82d40c800bc440380c114075071a4084600c40c180c1d06011004d4102c00d5a0042c9120104142001d540500700404407031302180e510307039140e600c41942c50300280203682071920030030314009000b8810481454105501d1050310080711109004c2130034540d843d0000c2c4540c6169408501c411f07907001d085008018001d07c0c1c100514103280324040d4691280070300081c40c1d90b03225070b421245100b0b900201c40005a00501c5840d00310300019140c0e00800103001035a000690a072800645040440030441e501e0b60101800e0104d5100d03038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 997363408 1250 997362158 997362161
    0xd1104330e1206010303090617070c080703170c0a03060905010302150906040b030412030b01080f040221120a020f0706080604050402012610381312061104030b0604 72
    0x1180065808100c00c00e0992002c44180031260003188a0303140c8040403070801c00c2c0641400d200000d90600210700307804009001354401d4910211507045071507242d940d0700d80d0404564501700c00500761940941032080c00588542000145090103081c0d03020000c40e6210388025060b5503007072102a42c0040c00141d40d00704d041031080240a02c0030000d202510b0155521f5400200340c20448090300d46100c0e42ca4407000c5241c042c02203400585092914064514005040440404020340049c0c045c0c0c600880c16031003c0d68490024203010502d0f821a05003000c045103401440d440440d80c407005014450113110301440008502054580b40d4039082c400d03a4898042c08014000100b00b0307410400283c0c1015072803a10050000c00d40c5890303030160031403860400d5020105a41c5640003103c540301f00100b07083c1e03040f41c5034810084200c842d011140301c4044032502030800d00072100f0302444021000400507050301c112600e00d00262081e60244001c1001c400100070500441c4405440e1240c0c1100060252509 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 997364658 1250 997363408 997363427
    0x11070308181f15050307081f0b1815030717071a0f070203070b030f10080f0a031209021002030309070e01030206040e090a1707060f0203060a1a0d110433 67
    0x95403441461035583e0000038a0224147e000c00c8860b00104401040141c2641f0449402001c1d00e03810300c035081c0c8003030100e42618605942d0301c0700750004c0800b03e4480141c58240c041050f00081c12500310030707200e0255007a040304407096040c0700e2042000c00107082d41c18440f0450312071804088e19041c0144403441060b543e00443d0100c1e494001c400d0049031000d04080603500a468620391900c03a45400ba070560615015030304102c00359840078000710071902c0f0006628015550600d09040070381070611142d030291000a400070360005c010106968800e500001541c800c250318002ca03507406030342d1422540f1155080c04081d4200341c0c01c004c140300008010782117a400810b106c00303c58903d00e05032a8140d8951a103613108d03140250024009050204500504078429641c0700f086203103040990014101040c1840780c0003075020b0300c891000c20480382c1c0c0f05849044a021a00b44000d84908402e01c3c0154401d003d000325605000310280700e25440d0b5003425a1591084072a251506254442581c0c602c04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 997365908 1250 997364658 997364681
    0xf0606040615052215020d02060f06120109020907051218030405060a2d0e03070e06090415020c0601050405330a090603060b0102012009060a0311070308181f 69
    0x90340c0c42c02c49681c3c4c1001c03000300c0080892103000300040f40111002400c1a80c00d84242045510160901c40c8074440410301d0364014000b00d42c1d04000c00803161140e4050085044041d5002000780100a20b80e034000004041c40030717504141d10003039565098455455501000e544003564014003040c045401c00d2802480b042c4040d0415552000120b450000c0d001c0080d8008d0301c84d62900000c50741d805410189440107900114041c21440f401c24102212011004000030301c180803c9011805100d03801107000c07501000e01c0015595107410b0072107295036100a01c604c0b8001c1d40b0f010001030446d5401c040141c0c44560521010f180c86001c1e5946401d18504842104e034020701410001840010502c030b2070b001148034a5000c165140d283d000642100d8200024040b10742c010540120f511410104480751010200c5061b511607458081c200d00a050742c1d00342030204a0000707201d400f49a04900107a102d4060489091070381415841110386480700500c0072126036400e240240c0381c0000c560414465880c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 997367158 1250 997365908 997365937
    0x150414040506070c2f01021b011b06021224100e010305061203121f051011031303060e0d021f0504050f250f0605030103060203040c05040e0f060604061505 68
    0x2004010540828407180491700e454005840c05c920f0b841d40c0511900c0030000c08440020250200b940020704082c246520440354110b10428000c04c100c82903061b40c070f0250076401980d110307140405000c9500799072403d040204107000c01903202e03145001c22484c1c41e0400c4a987e245000000d030001940a00780c080c280e13580c803c400c0d00781e1031005001003001d8441c140b088940070b00396040514a0440007001d400c01180d00c00303640f01041c840c03a10780c442c3c2045c10701030364640281e41010b607240e01411805030140d000002e50b08044004103000312034028001142c2100103a803100004541c041e41c0d45c070501140e14030846114403100c42484e8441e4085030f401750040040e20000c40200000c58280400c0c1c00804006510f15140300c1103014051030b90350090902502c078120780750301741a4081c00c28001440000d10107500000000c003000500c000076001840c001c0c000f170211000d40140c03da2913202401d1808814400c0000091003840e103805204100c840034295404068500740741151103602a009800051 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 997368408 1250 997367158 997367183
    0xc0818040e01020a08090c030718020910030911032e060503030c150c0405030622060603080d0b010e06043615060309121803060203150414040506070c 66
    0x280c890340034585120000100050780c80000d03680281800070041d001481a50000e415603210f918005100802d0300c2c80032604200107801408401c02030710034101c003a904100f00700280300140d07405070800048544966403c0203402100000e05650703000c0741c007410f0310194a4102861a00200e58146490410511008900e40b42c4640c0071038503680c841c04612605502c403c02c50b80307610003000c800a40140c4404003081c6420700c0c010001e551a42d0242c101400e50000c0c540064184813062407954a1a5000c40d041c0142c0ea40e80c20031016a401080780b403c1e1071800c1105881540d84900c0449292000c020416800d05041c110302c003c440c035142100c00d0001800700504a89150560131940c00320b01c40d1840418900b03440c0c01b186281140c03580c0f20704181410040d10500103a258486c581c00c42c1c10342d1405140881c459900c0e81360490701c0e13a00c0030b841580300200748208200d01120b15050604151028030180380c9120041040c03003012940904180c000d140070070b01c400d116440010416003e500e0072001c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 997369658 1250 997368408 997368457
    0x303060d11030f0a0f02040b03060403020c1c0b0708150105070c03080903010908120a1a0603040b060a090c0305010f050111032508160506240f0316151407030c08 71
    0x1030a668500c140c4806200c0405c0608500d001c2c01004d00202082d4042d201074240781c0d4010f503648520015880c403400b0501c448803800c0001011910f03441da00081a2411030400c0d110252103208152100b50502c4414048910a940124100c0e03080075405404007500c140746444927000c64120b2554a54103548030f40c846004070b0700c0d80c0d015200c540202e182846040c20030030603031002c030303440540410319030b54511218600a65804065940c880e40018440c0c0e166510100050310501168106004961074041e034408800d526501c0a0f050311045041e080e2600e4451005440c840f24402e08000325030b204200300a0002095030b200503680300f500381c02070103840496803007800c41c3e0003d01082c000d810b100761840c1d003404010400b0395042150222020362030b0480071403503c0001a032441860103a440c500000704c3c591801c002c0050705080c080c44040700780352a4401d0b0001c0c5007aa05803000001c02441c24841c0c00f1015000701d404a503070644074200ca003030680e0307111030160b0440360311201d0b81460742000150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 997370908 1250 997369658 997369663
    0x1c05161e0302030c0706020105130609030309060203150915100f090f0e060f1f030902030312070e01120615080a0b0d0b07090e0f0c1c060b0405120303060d11030f 71
    0x18a4420b80285407181c01000c0038031300e401603561040c41160304140510500e100c00380c400350422604200c0219a030600d5045c190060151481c2c024009440001042810344005412004601045800b03400c40c0d203a0804d02201d005885640d103502c0104e080041a2650150000988003e56410324030401d40d9540c1810142c1203031036004617240c040c6481009000e01e07040140111100c0d0403180301100c0401c001c812100744140d00078010906503a804013000350f40d003c00c20784150100130710f007440300e0789804880189880e80c40285503010a061203c4803111aa1902500040e21a07000044841000e82c46003103c40000241266004640c0c4800c50329464807080d0000180074041c000a50b060700b0000c10050006260b6842803643e5132444040c000551148003510b074004054034009034460488106444101c0307600780d6003485040c60301c180050f01c21511405401190012030740e884500e01c195444a8503403104484165004200f804100c002810f6004103c110b010054110f6072182900c1071000d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 997372158 1250 997370908 997370963
    0xc090f03051e010c1d04060e1e0708090c0d0c12050c0f04090503040b031503030a0e040c03020909042a0b0301091b05030a0e0a080a111c0516 62
    0x101c4640040039001d00701c4103100070b00031550000034000c10640d01860b41c02410419003034984000b10100c80c0321041699500d400c40310191a02102029840c1406500014031100c03043c0f894424540850005000074003400b003c1b4401c11440003d8070983c1040c0d070030054004245402265500701341007000c180800000741458451744a200100703981c945c070404200d040500208550700c0b0700e00700700490000074000b00c1900c007103c404248003901c9071510f14050202c40b40401a450f0144000702d80490ba0681c00880303c2a02d080648041021040800f400c40503442203010b00c5804c400c904020600258412850f91900c0d02c41d000c1c0315940780120541140b0450480d4030031440d1241c04401442504158419144d0103071150803100d4141495000c0980343d03020040101d0f4800d607680c0306a00000c0410300030217080d1944406000d80c0d03000307545009410f1b120380b54450041c622800229060840860f00c500c40f44001c1390300d80505042e0b850a011265417200ca5044071030800a800090300014040703070b4807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 997373408 1250 997372158 997372163
    0x91a041a270307051b062512050d0b090f07050a0c151d03041514040518150f031c05070c0f08060a060e04060906021c02031b030f0601030c090f03 64
    0x2c0d50b60b08120f0400034076060001401c845d90308850082001244c1d40c51044440300e40f14440750000c0c1824140c0a081c94452422000d0500400d000c2580c50300d41d0701200802505410b000d04016600c40c00707090216140c41102d254081c44075070741c04511a18041c1d4041c112503012880c3c1030500c000c0759603034101c0e190740c5c00301942e0f5415200c2e0065203540d045400d40140c455017503c025402d007443c16000d1700c02c11100510407014130111075030000b000c202d80b0003190040c1401400b8055841d140050a01c0510f004941ba5401d030750750105000b403e40743ca05407012504000500130017110880c2454400b212001709090018040204412000191041501e0008101c480e103154015440e001140d03041c464001c20080e41540f034040203000c40a07044000580083e000280054040c0d01c600e4030303c0c000d2060b91044a1015604201c440325400b06400440c840d2140c80004061420465000c0625000683c0c8114107112144001003065100b54000c11038010b00c1c0c40e10340301c1c450343c1e498904107603049034005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 997374658 1250 997373408 997373413
    0x302040f0213092910081009050c1201120b0106050d0f0f0c03050f011512021c0506150703020309091302210105061509010309080d02040801091a041a27 67
    0x20f54254a901c030140d421300303090f070802800041c0c612400141d11051009403035020300c01184045520081c0c0440c05401420307019100304223604144899000b20b070840c840b03807815200c082d000401c40b03044182e565815540e024070204026400c05030143c2e0150840055104010387d0352201c00c0324550f050280c0284204007103800521401901e00003801d407900180400446402c1d1801044407260361048000204041d02d80070001d00308810307a01001e0b10616074403c4080b81b4840031000068426071105029900445652805c80c40808011145d4001d4800203000360308148020041c2d03013030500120381d01c00f0703156401456075106a4001240c1004034016180b40c114441e201401d87c3c01c0911440d904813108a80f060300109010f61404601d00c26a02418109920703429010200801403040c0c800745650500c095480341d0321240424000d11901d4070949481c50781500b0091409459099a03005e5070300202041e428442300031001402074806045005132500c00c840d641012a5600c480e0b1078611180c601 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 997375908 1250 997374658 997374671
    0x30c06120405010f27020415080c010215150603090c0301060e07090506090a05060d06051f030f06152012120603010501050306070c050f0a0c18020903070302040f021309 74
    0x78481e00b1207803040040142c8620b4000d20780e4176200425040c8402c07064410000003244190320106001e00030a01941d00115242140481e903242d010810b02d880640aa003143e007011154401e451008100b580c1c4481c1c0d10320166031512050034080c0085078050005011159092a4140402d0840d16907a020000422441d000d0111056105200c00000c040469a00b0705142c1080300050150105108480c070400380020080d007500d800f07030004801000024070012100503408503580c1e0607403818010500203480d03c0301c80451015184150400d40316400c7c6044a0666904010380d0300c0c20490464050002c0c1041d0400e050700e2040003000c200d400074254040d2030750001d00401440c0400500481d1190b41003900500c4503031400220681d000d1850711b418070381140760741446801d1544401d0300b0b200d5030207100584818040040039100846801c005a01c6243d402d0b0b0388108201e0240c2800c5c83d81c142c100040c10400342c609600b0102c22102884001850702810800c01c3c0d407a600300780d0098585c070780c4584 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 997377158 1250 997375908 997375913
    0x10315060e0303040816081b03060f0604200406021204140f01020708030f180409030c1e0b0103061a01020f030a2307050d03050112030903060e070315090210091d06030c061204 77
    0x34055188d000c00307011403078209220006500d07110000d0400481092000000750f01c0c3da01c07508100c9036204030340801076094041100c011421380c00340c001e81c00544502864180c202e400340040310101d40310482c0441c1400c0489080207c000b0050841c5ca045100d00c2d000400e416100748002d01011810b02e280355a140300307064420021081a44105210381d151038002e0f0701081e000005184060f40c000c0d82240d542480c109540390b02c000d0b001b4050429000c000c004010015182d014540170301908113009000d40f0400012030780c0e00220020300e140381c0c10a110035550749000e03105820000c2003904c0c0f081c0d01e100c420000301046030000c4e8815103244c2d2000002010440d058445c060152090340500102400282c4010308030030103512005080c01e540e000200100d400c1408101c0c05903910504c040160110a24a80050b001c80c0b1002e86c0300e1444054000c1485008600702c1e01242c105961080034211050a0f400030382c13000820340c60701409010103003a01e56542000800840403d070b5000d60060401c0d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 997378408 1250 997377158 997377163
    0x15140a050105190b09010f03023009010524030304150807090608280b030307080706050901050f27030a020a1e0804121a01030809040b010315060e030304081608 70
    0x10140080c8140030f01c40c0600011807000c3c11602c0300e80e4203082c5804034040c0d000c3c04400031301c1980702000b101072110720f002c3d07000380045c07031208090003149060504070b48962031007500f00e50b01030f1504161044a21119003141d100c60300710041d07512009050342c0c00c1c65503941e91042d8444683d1000b800040011041141403a0840d10010240000e490000e03401c0c17170583c2890202015178403110b640c118100c01c1c0c841000a440c2c02044940c04090241d036100c0380c4030b00d482080c0707400c0340504503441c030300384400141c00640c1440f85c10300c2002d03256074001841d20b504011145021640280001201801c8100720101004100800d0380c111254000c00b44816182000d505c2030140c1032140c1102c50030f00307100708085031405003500e040c1d440c155411000b40d5003502d4480c1010307161a42c7d404603141008000000c1c0144c0101400b030010042e5421711146501000440882d01010481c1c5e41112108100740001c0380300319252243c010002d4100c07403415458040141c54006942c0210f2a654810802131191007401d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 997379658 1250 997378408 997378429
    0x60c08010521071205070801060b0309100506030a062f0a020d030b06041716060e040612020a0b0f09041401170f1f0f0207050c01030501060e0d15140a050105 69
    0x401040e48000402800c030701d511001d540c8502186108104d064a090103800e004580050108400810030301d81d50f0a00780030140c00448000d00140202c070f20983d443c040c0e40c000c86101e070000501800c010015942c1d144c0c000c090341c1c020004112006101d00c42c015103825841c44001a2440007107480b02a2094000d2030050083c1401d0201410094140e00c141c559a0035141a5003d404c0f045c01417141c0030700078601d007208506080001e983e51680008440b5000b00b04ca40c0165000d482c24041035803140c0f0b1501e109002c03900001d40101c10750100300322210014001d032240c030070b103a20014500204040083d041d1030a81042d000b17450724480c010411b0b1038401c25091204c40500d0050300c8403420301c0148a48480740840385a10400312910202e502c0d040c2c0780d020059903020b5040c21500c3c1c0340300e81003250f034451804e2451800b007440c2000210702140503d03610001e01d01c0040078801815845da0301c01d4446411102001603468440242c0d0750841b8450481e20b03c41e80d000e020000d46585000108142c0382c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 997380908 1250 997379658 997379689
    0x70f0c0b070816140717161202010f0e041a120c060a031a10170609130f0c03020418060b010806060307030506031f0f061a1e07060c080105 61
    0x908001d5a4001691501640c0a403100360340e11840c0d02c9042c1c10302c0c400b4901125214a82406440720118003450903404e9807640300308100841d0f54134442603030031194401d410300070090080207078a07003800150b110b6520b1441c10140c03850100803110110b4049001c0d104441180c0400e002d090400760310504140742100c4240801600030320b1411520401310381c01d4840c590b100c2c13040648800c000c05210101c801818800403000e001e40c81c0b0700c07000d076000904000035000ca59658800d202d02080030362038465201070052607100600081c200b4686e650075042d40d082c29044400020200c030000c05030b950b80c03190a0540d5010708442c88400c005290907400c4400105000d0305121160b41440855100d080550381e104105003000039040d140d100000f490400c04003000074011110b08400400341c4541c0c0c00c041001003ea00061280350b03162204442001340080c0b0036180d0b440144522070040307055131003822124000b200d0075440c01c82c1d55119142500d02030000c500125030342ea0010052828540d000c3c0f5000e50 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 997382158 1250 997380908 997380929
    0x2103040510180201030b1f051e040b090108150901090f11040801020a08010b03190c030b190504060f030203100518070305030703120b03060a020901020312010807050315090c04051506070f0c 83
    0x503107887c08141c3d004210301c85d10030040b0101e011005144c0600c00c40c450b00f02c92542254440c1e90702d04240b170f010b42c400b00c14130340000c1d50040403400e1101c000791425810720f002070142010384e080c41603070001404002840d024840d150380f801321111540d00000d03c090b0001500160340ca0708403120280408606034000b03542c8100070000c03c00c00301e20103085811401c080481c046807005c4040c03002c81c0502a00c8882c9644030365100c2c10000341c8841d0f20301040031103200f80e40c14419580d40b00300043c102c42c100c0c403010b90950040ca1340351032002c010b681700c15405090381e1428503142e101074903070030310740303111038204884a07400051044181500140b140c9403c404000c2c051188908040c013090f164072003d00503e0741d07507802060740170301c0b60300910981e8000100c00c499440c0035039454002c0d076620403a40c45034a0090150811083c2d07002e018980c464854403541c0002c1a01c1000103080c880102001071070b5261b14401803078213058a41d582c1e4000c001d100e001c0c81c1110703281c071018181341034030178102c0d44443d00fa80c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 997383408 1250 997382158 997382179
    0x7020a0315060609140f01050f030f01031122090f050f06190606020c0f010516150f02070c03110a0e0a0f06082a04020c03041212022103040510180201030b 68
    0x2003098082004541c10a0f00c2c2c00181082c284012380d528050f03e110f880d2060800310800c6050418648190b04980c040d501c03043c01c43c001d240a1100003462201c41c4207000f0485400b54041a6054004002c0c0c01d11031585101c0060b00c54a51604108a0310101c08054001c1e0f800c5c0501d4044000550300711514031030742003210b2450700c10069916403040340c5d001d001d02c2544480000c0c036809101581d61140010385031074241e10040c500600340d43c5502134054406071400c031003245480303007a10135103030b031aa484601070401d10304507100c80320070b544596811544070322400f10109100074240c803402c1c0500081da00102e014103042104c081514801d8101c3e9a0700c2d480928046400c40701302c40164022809102d1201d036611010002c20041e125034285005144800213000918103118000c8520b1540500c0c80041100001e03001213840314040812100c000103921002501214004001d40c0c006100310704403543e4038000380b0500140c2e4041d80d8400303034620701004100d0075542c00d401b0b04a02c290701180c408820 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 997384658 1250 997383408 997383419
    0xb040f2306040314060f13021314161e050708031015030c02010c0804351308070b1305042705010c1b05060f040317040f110616110607020a0315060609 66
    0x3000884034064412000a51801c0a404041e42b00b00d448640c0c074164030a040ca05040c88958400b1801140d2001840044111840310b02e50040e079114080785030b5410389006101d450320b0b4501e805c054540827210031b50b14000100c90a00b481c100b01803410343d480c042030b921020b507006407c50782200303901c03800d03c80703030381d041000141401d07017010303450f144100c241021403656607050400d4801c40100000003400000c5c040d0074512411500c041110070140441d00c456232950503543c5075001c0d01c0d103540041c4a2186051005141c00e400003404440414002e00c4110500c0d2018034040308560400c2e40d00f43d6640e8905034596500c1601541c1c2201c0100e040c40003075440e659020340e1a00000c2010882511210120701018800c840c2d0b03080791410350308481e525040500f451401c03149907070300403204108501e03c007040508200054410011001e0141c0e9152002078490030521110b071548194041c0c02000000010f03a84c4e500188040e5001c0d807140c902c0b41c0d004000e00c400321400b030b0300305805008140104005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 997385908 1250 997384658 997384681
    0xd090c15080a050907030c0f08161203030513020402180103050105060702130c050f0d060e01050409050d0804061b0201050604051003020d30030c090b040f2306040314060f 75
    0x42002c88090005001e40c0c0d2982c055003031400d03030b40005118298840001030a0f11030400b159068902036000d03643d600c802d40040e6200317110170744906c21244007451b1120000c2800b96020903408444142c1c5d8000c440e00c1580083d04a9000c00c140030100000d03956411501e5070b040c4100750240c50151102450800e0036000100320300c1001c8081490552181d40c02035125228001f0b035825603000300986074030b80e00700c030410102400403401840c00400f0b036040006100d00c2c0a02403000802d811001601321500c4452044843e1000184190303442925942e100c0c94045a00ca9400b160032140d40c0009140c1c00c186080200340c90014101c1c1c3c025409144d41400907035a4269025840f5520014030818441003c081c10582d20b240e509406d100078511b904250504d404d504000c42c441c0b41580c60209940d2965800011030040303001d0030348034101c1c060081c03150003d0401d80810b1011040051420130510b02d0000b102c5501a410840d212410742280844c440c004000680e040745d0000c07403228661901e00c591a4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 997387158 1250 997385908 997385911
    0xc011a01050d0b060702040509070317070201050307030b0a0b0d1413080a1d0a1d0a050c0d0c110a05010b090903040b03070e01110a050f07230d0c08030d090c1508 71
    0x10b299030b80f000d081031940c40e80c1c00c0760f04040d4007030b100784024500701000d1170301ca400a100c25500f080c195188a18108104002c440c000c40c3d0584480c2c1c115180c1040480080008200043d00602120b0f00032941e42003d41c05030031506240c0c00041034508400c840c81d04c808030040c2c2003140c003552502d00c00d8001806d02c01079554500d0305140011054104032401000c0348048181030360007100707000c4089051482141e608208103e20300700e417a020340783d4141d000d01b2683c0031039070406042d40c18014195040701581040c1107402c02490101c4171100f40000e6141480d09140e000c9915030b5407041c06a0141c00c04401791544012804003950406192034003440b010306c4010305070410001862481c00ca240c1c01450005e070800c90050032900c3d00c500c0c1c0d2074402e82da10001245042c06201d01440041e240703034062008564500c0b010f01000b10300d0145414001300783c03118207044400344540040480c200e2820400740c541d203000700d00086110151810071640311426034100c15400101400c1c0c0c0b5030304503044079500d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 997388408 1250 997387158 997387177
    0xf0603020c0313080109030f08250203040810020a1e0f180e04050106091a0114280503191a210703050616091d1f03080c011a0105 57
    0x980d898401185aa082d0f100d4a00c4515100c859a40d0209841005600c280c038058030035100c03401101c01d00c180940b0b2048045905145641054001c0c0000d51442e01010401c42c540d4011242081e80354030a0504103580210001c2d540342d800309600c110280d104822980481e0040c003180c10780c1220900041010715404101070600c69072425204811043c1c00c038000041c00c510100b002c0350705043c51700720b02914841c42030799840c504001c2c0c0600403259081d01d407900008140c40b8042680c40441d26a442c1d5004404c03100464042e0f4540d140d400c1c405d14503c0c403000e00d002ea4510b40c2c0c0c2c1c45c250a00043c42c105100c0c25841c035134a84240e03168108500e40c480b849086003210260741d162024410408000f520f1400e42041d4010084004200a4000342981c02003009562041c0031542594040718001150f1240000e5094042c80340b0b1400340c51260466000340c44030f59140d06840541c40440c42070081c40d44200c0e000c0d0300004011051003800e102d00581890300a420340107203400380d0f00003405070080314003d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 997389658 1250 997388408 997388411
    0x40f330c0504080a380601030b091e220b0708090312060d06110f0a08090d0206040201050706020702100903060c082403030405030d08180a02130518072309010f0603 72
    0x6040e609400d02100c043c00101740142e0225003a059050400a0799003942c120380428280365004d650713417412078855442160304004024468101002d02c02040d100500240b07a468000109030f251880c00c010040303619070040c0e12022aa00305803030010020240184402145d40081c4000c01141100c1007000e604200200d455058443c428140480201908900c958210200145c4c005800300410302031720850410b52038015490761414400758031200c910690b000143c000500003001513025101904141e401003100500781001c60340841c40d05180b0507200d0700460034004c001c004005550143c01039140c228a045a03803800c0000e00900312170040f440c0c590136003404d07916101403a10700708140c500500c401801c070f4800c640e03181d0024004400a82e19140481c545116007004900001809004550302a003030800c41000e03929000001c0101074460a070200003100c0101105404100500245c1003289041b01c1801000f800408448030001c039a46c00344040070300411910501d500c0d908110351040c00c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 997390908 1250 997389658 997389683
    0xb0705071403150907140315040f1a0c0d0e0f061501020111030a0903110a12080402061b16060903111e030a0305040501021014040f330c0504080a 64
    0x81e040525a001c15102c0000785400c01009420020383d480482d61603820703c6e105c10020400303054030b4100c02c100c12400120a040481c0000e00c11580700c001c0680a01c0d01c2d80441d4a850740c10103c0d01c1001d0744d4004907001d0100d40307091000307864401c5003c2c1030300d031000410011000c0f504003a2078100040c40e59482c1248410325603a182d000f9000b6101900b0180f640d5517a07486e12450342c4008051190081d0f0001d40b43c5c40740c002c0c500c08002000c0041d550404c41c441c8001810010442e41e01c000208200e820160a005885041b03150002036009605280042c4c007a14280500703a1030211113a50240040294188040011602500424510903015256400d01d030b81007a00c114251407004103519090b1280200040a040d80b1001500c02e5075000da0a07240d4010811080c035041d902208441007015641c980418002880d652005000da0b102c0c6040981c1c0745002c400d0756004407520078280d09151611040b0203c40c20b040d118204800d203080c24500d0516090a0788e00f50742d94014100200003000014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 997392158 1250 997390908 997390949
    0xf0813030c02120703140705060f1602010c0f03021b1c030309020a030c0b0d0e0601060e12010e01331203051b060c0c0606041b0e190f0305070b070507 66
    0x2441d103043d02d00e41011112510b50b07920b4041500180d210203088140500c54000c40c1518100048441824640d070002d828009450701080c000203c103141281440700200c1410001030004043c84030382802078020f0003000d1001c841021000004820440c406c1180c59004d1102c40710b104080c003540b542500e000280711000d0b01c0824101501a0030291092440b1100000e40c2d5803038070018143d000700d00c0b070709208081c44140c2242d034908007805020b0100380745003041c5042e820b09820000c02000c290b00085580c04450078600c1c21641c8890102c000f08088808020340011024010200c0d000c0c0d0b4444540951318003032142101a458120040c10081c1c002841d10b445104200d01c5140f4410304002e40749107080040ca603166541c00500e6201c2d02d40142c1000420518040c42185050010501f40498200980078101c41d0740c000c0c0d503601d0754802402c100c040c0c1c09468800201015040020149001e242581401840c02080d40e010082050f0308000441c0050303c007285074000c03030340c3d034900020b04010384a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 997393408 1250 997392158 997392169
    0x321090b040b1305060d090510090b0f07050d060801020405030106062f0a1202061e0f16050c07121406071d211c05040303021b1507030504060f0813030c02 68
    0x1640401c4d81728401103505001c1010a501c014081442801201c032480700311070344a0203039600000e002d40388a83c98070024411050500ea4103230702410038900f10745824004004030003111003c3d004090303940c0d80410b0074052401e0900c10803014215078141340d044501781d0002e000282d00914101c40c10854042c0310301000da9020400c400400358000c03901d00480c03981140007980ea15040707512070300d038499445113108445080328a05015070450303c2007100950f00c0030168109240d6a04242040184c00c004542514405100b14809810711b41550400c503821810a04907410b03442c0e240c40c03032540040d02803003109500080741d43c013620b07070301c588280d4000800c030b001400f60b000c2d01b44849200b41c2d046119200c003840100d20703c04500000c90f000104140c1c0d840c0101d4090146000050140c0d0041004181d00e1040c03541284012500903d00e1010541800d00e022154101c180304801154000c58107200c01500b0104054010140d490002c000b0b1400400101640c50510000703001d110340c500390007042d5102d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 997394658 1250 997393408 997393447
    0x1f02090604081005040219060e09181204050405070e0a120204090b1312030c0518030111040807150c0f03110703060501120501050c070506070f0e0301060321090b040b 73
    0x10300c0180c410f42e16080419201074501190b040b4828006444400c05080b444042d020581c0c0450f0348401d00d101c08081842450940504000c400724141480300f250309034100201c141d8401c0c542c003025200c9203400b0070b202c2079510140049080c0400103d01c0075160301d54200c900122040407041944250b00c2d0f00204004041120000e04503a800320100113003048181030b50240f1611030a038084454050704d100b05c0869148803d1400003a0041054030601c1d00c192100d007652550080002814081114003a0000d0303002e64019400e9400c8400200715032484122028550180e0b410885603244541e91914844c9a0b90b80d001424001184006070b1120b1040000202559100c00100b00c00c3d40c680c0ba01600091130300404660f20b41c00c203400141060a80c1d01a11003050344071004220f541c44000d000c1c0c42c0101c001d4605010051482115940f07980c003401201c0040d4062480340004d4030040302009203100014640800340114090100151045101103504440c142c3c8012900c1e400c0041e003d4203044207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 997395908 1250 997394658 997394669
    0x150608010c08041214031b1b151b03040803072c040e010902090406021c1505090702030c250b130e131203110d0510030201020606031f02090604 63
    0xe0510044603450304440b0b1540918090540ca20b03224809480c00c0313400f10240d2101100300c00085c004280401c808104400c4d141200101c1070b130030140398411450345205100030403401c2e40c3c040031400c0e01c21680e0b4000035801c1390010b65103148a0320050391000792488050001040076000200060032640308201c181c680e4000941650600402c0b00b840d8038002d452224113a00c0b4034503098610651b031805100d00103529038080d007154001d41c0c81e501c1e6071009401c001c611000c0c1c0b150030740295801d0038641c41102c005541c00200c0c0e040d02e904007020700c5249040142400c080d5481004503481100d070018800002e650440845440d045504001d00b0080c003441c0d0048500443c01308441c8020715903034942d113050702c0c0e0031000002d0741c0da1810b00041500c1c6082c80040c0c858285c0c000c100d44c00610a40110807001f9002d00098641580d90182d202201e00480b02064124941d4400344210740e8180305503170300507908500810040c54a030360381e0131180310051440e04281c0d90000e90a0040e44480090707038024007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 997397158 1250 997395908 997395911
    0x603190c020d02100b0d080915040905190203220c1206021b01020a0f050d090816230d0c0c0518010e09070f0303260a1a0603011215060801 61
    0x540000042d41d03500c62801c1c200094043d154922444210a00c61034030b5420004294001804d201d440d02c1c0101d41c0422002c542221062940300c21030008600103100911894000240902c2d00000510030a44808100004075004006102035002d004018268070f00320200602c55031075003494104519200e41d400501e00100240125082c0501170f1301900e04d21032510090548000c1c4a10458200e100701c05502021a9881084030040303840340d006843d015062000000312801c10351200100340d007040c3d10343c9004606201020b8100001c40d100b4101d003c0301c804030761840c000303802c880316111000b001440d810400200c02003c24480e00328812760040a01a042404260010325148101d440c24095010020003110114a17465000a8504215a8418603040140e400c640d0100c07904035014110190340581644514000a41401194002c05e10308038001607c0200c0050f924101000703010070b9201d036030280010031180010f591000325603a800050347c4040e440c02e6818800800d2140c1092100c2d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 997398408 1250 997397158 997397171
    0x8130b0d1518240b090109090b0a0b071b0b07050d1404090902010509100203030402031203090d030b03032703070f0806070e030a0602072d0309170705090a0207021c0506010302060319 80
    0x1e08010000c3c211180203031f99441e0260313200c02000003582c1d010410140c003d4030003001004010013110241a0712446040d0340c00110319590741800300c608142c0c021700e400407000a00300041103c01c0100800103025802c000780d1100040703a1038010790041d441410b260549642c3c0171401c6a1042088030008200100711021401840400070355913041218101c0c00b0f8420b140540400d03640e000140c2e841200ba9034020100c0c04082c2104a018102c02e0810540500c07080c0104004190044010001184d1021080041c0718003901014a80b043d0303a0300c00800d10070880401d0040c00c401090050f848049402e000300c050307003183d02092a221080c0c401500d0079101041d44030401000304401000781039251008915004281402c1005142a050080200ea40c03400300300703c040d40c6144804e03000d170030550944180300c2da5440414244e6200b01c2c2e1004400c0c1d80058214110f1502c50141c14031000041c00c42e6800c09016902c0c603030b443c0810700020384914408800161002411400106d21400d240d200784642c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 997399658 1250 997398408 997398419
    0x1103103213080931050105030304030b04061515110c010c1104090f0c0f03050105160206160e030703030305010807141c0c09060902030a1118010c08130b0d151824 71
    0x20b400004c0020000d080c04000140d5145c0041610240c03500440909010f46555442c0002000d0b1440b600d40300544c0c92000145070152290081600281501c83c83c41d00c04c0d058003a1410000398500890603c9210104440801e908145031510404c060b100000d8044407414040455141c00f04018036022141c1804240200c0c0540307540122403050000b403256807600c0060042001c102d2402d000140e00003c00181500c11883d0f0780d08000c44281000e41c121b1b6074600106e800c0a80c2a0003c0e0082600c17a0010003115908015900040c00c840b0740c03004200303110800040300c00e42d1200300d010b00105160100414410a098808024040520200072a960b50010003000c6e420884800c01c40b1494a98401c070324001c01400c41c1d041078184644002041c84100c01510070a00c0c0d0101038415800502090145084502c24200540384a00c2c0c420340f2410200c0145003581e10650201410302500e8104100d034601c0401e283c280040003000c08100080702c00c0c0a408600200c00810940803080c1100080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 997400908 1250 997399658 997399729
    0x5010f0608071e030818011106090123060105120a06050d03110115050303030c0a0e0349141306050912060f0411031032130809 56
    0x45804141c00e034841000d0fa103440c070a1080c0b80f40704c0036020540030482c9990b54812a103040e82c40003c141040540184245840d41c03a140341214840810781d0b5904182c856044540c007019041100c40d00000b5803490030030002031187c000e403980c59600807080300c085820017065402c620043c04000d002c1303045001103410001c0c04080d80902d242110351901c150300078408003c5001c4401d44501030021031554a840182c0c8040781c0c480c0170701e00200443c0510708a1166420b004401d5081941c402c0c1106c207524941c2c000d0f2901305a04a82805a00b540304407c0c1c0001c00074542c8130003281d680c01c0004540c0c1d0381a14070300301072041c1d45102e04928008003000c0746241d0400042c0903802c1c800d5503c00c194150401c3c0303040d43c0701c3c0c0691320803080042a04c000340c0003960034905c610000401809840605401078451000c3d07909501e41c180c1c8000d02c095034060910706120f49115030001da5081c000759814065004850803000d42409800f43c00d00055103400c40d120405440c01b07810f0b040c40b8813005119041305010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 997402158 1250 997400908 997400923
    0xd06410d1a13061404020d030f0c020402030a141303080103030e06070219060206071d3c010e0d0317040c17030316030605150915031e0901180b0405010f0608 69
    0x440c0d840c070b07186584d03c0f41003020101c80d21482d406400b1120129141d2029076551525000c004204003241701c100c00143c0300c60003e980501c612010114014503560100440300740c008000940310640e03041c4803c04268800c0703080e411270741c00d4200080c0030200300c4c005c20900d02c030b410300107500540e4201c0d5901e000b194100c2560200c0301d1a60903600e1a40702d08104484610100004980600b40d4407548205480c0c90740d030a50509024400707100700e841e000d907004402c0b4008420b481101d0850302c01c954171256085107031103284240459461651031080e41e0301400740820010f041107074001a00008081100700741402e40034206002031031600000341a100f0340d4962040310407400e4031007a640c9059005000b07020710010359500412440200d60700c14200646500185da009522021444844100b00b0050005500031201c20001c80090a40c2240300142e0850107044000b26a141482098100507c200d440d030700181d02141919003a1281d041c80740c09404240a15100d1619091001441041c00103828 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 997403408 1250 997402158 997402163
    0x30207230a08030301081b0406031e200d060902010c051b18150d11190501031407091520060103120e01020318060d06410d1a13 56
    0x454095440381040b649a000c207100e5184540d100000100c5924000030140221840241000030219601d844015100500d0b0721607c0c0c5c00f403013070ba0b071810910100560500d02c04228142e078950201c0881c001c2070307201016410181000f0750782c14404c0d085a100c1d070714000d007107034006044400900c019010381c0c1c1c507500740a040600c200845400c0c3c280d0104c0c10b0001621410b10b4201d501403080c20481030141ca900100c008652440400c4a0380d19142d45545d41c1940025002d404030021506150014080300c0540c64245110348604013040122584000b005042e21320910040c0c1c0014036448040e04c040c68007001002013081400e1501659610000307400f4101d07030103030a030490040078401c01902c40408c240d01d80350041e0410000c1ca4411040e4000b04400b00001900c490714120103407116104540315500702c284946000ca82c0f003d00000f41c0036660700c901450030881e5030681c5156490303117810700910341c00c0341c05045a5031102003800b0310001203034200b610503001d01007585000590700b02c2c24001d00e03604 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 997404658 1250 997403408 997403419
    0x130e0a1e0614030109050c12030415120b06160809010e0307030501050f0c030f0c090d050f0a0c050a0807120204090b070e010306090c20030d1d060c03060603040b0403020723 76
    0x10010320b014061401301c0b46d045009450400000704c1030004140c858034040d0120f104c00c0000099410220384189004002683c17010081c0340c0144c49481902c070300d00340c0c140c40345a003488080480c0382080d00a00501d0303030007000644d50741c046500503100c02c81070f85806039143c0103000d000028400190040ca00c02e0108041866543e40c52510800060001b07035003078220828024009a02d00407510001c0124001c010a001c4080c0107030f607611132034080e1244c124410f50b00010400810044500889005400d0840300c010341c1a04246990b9a184040e2080150350098155158155100c0340d10140c00c040e0040d0820b9885e1601703203000343c5402000115240001e1400710001407140c114030030380045007a40c2d41c0b00c100529441d4400200e0410040201110f4007040100b810212124810161000410841d08103a6040010a2820198000e013900300f10f0340100200300b4960b6548045950244e0700015404640d20745003000c81c54400c41e900860000c0c2081007403800f112601846100c9001001c449 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 997405908 1250 997404658 997404689
    0x506070b060f04020f040b0c191209060f120b150f03040c051507030507030207170f060a020301080c010c08040e0a0207050f0109030503070c020d0206070605100605130e0a1e06 77
    0x3c0c44203c0c450450f0512410070140020310415140c1030040c10f080d10460110381c5488103030040701c000c40e02d400c042201c51000251940031016000740c03000c8000c0c400c07401d1240f034034038800e80d01070480b2045129124240d5502c010b40501542d55642100d5020081d800d01c60f02c07174500e40500f8085074070540b07064400d0540c0280000d01d40c948004482040107035401e801c0e0030100d4958064820380c010301011025030240070030101c0ea44900001091083c440701d0010001c4000342c100143c20008050320f00381e0160300401c0140b1891200095903082038200307281c165a42049410080421b00880c0c001c4070070880040284551850190098400d141c024015210f62252008100e400c0324581440240407403c1800040e880038041c0964840841c005000d032104003107a9070002d091035215420440c3c0301682d0f001403000395440500407101030321190400514020015400e14000130992169118005420002540b514201d070072a85428030b40706003158100407445c8000c000f03000c1c90700070003000440c4582c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 997407158 1250 997405908 997405939
    0x3030503060319080f0702061b010519060f1a0c03030c21060901061404030b130501050912040513060503101a01030c0909020a0c050f100c0f1d03070506070b06 70
    0x210303080c3c201070744400d885150201308540b08059400c40758043c1c1e8070000c00d0000c030038030301411854440d000c007054000081a141c800c1e075814044070701100000800340380c40d02c103100e81403010791903109403140207000601c3d2440c0c1d51404400c521800038102031500010090100001720000030302007000800030052001840307803041d40c1c110041250701c607070310035101d00041044c1800f520000d50450440c00388240f620303481c2c0d00c400509200a441d440c041e0ba071041c100e01c080c808203200306604610400080e000c0222081c0c44400b072402980102d91060319016191201000306501c2000105409030aa8529203845104c0c140180034000100e10301d0382c1c80d286c100b101f5621038898801d10045d1742c1c44000a40f4148a4040002d41140115000f4020118024004602e04200c0d1030345603002103004002c280d00351040710042e108d0080104040c805444001031100340c000d071207046000210855200d0201602000070718100a503403045410a200040c0b00d010f10042c081124031070001a54010007209605 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 997408408 1250 997407158 997407193
    0x110a032f030f070203041a070b0f07090e070203120117120a0203070f050a06020f0301080d1704020d02010c0c0b0c150108121c021315020d020705120a0c030305030603 73
    0x280c05840c1003030082000416548245102035084016803040300e0405407100c1e1a0850410a0000d408120300003051020070094a020402c0d40418000c1d040a603500300100082c00c103403001d000b06414803124800080001d8400c0041c2d4500c0c2c100e0008040031541e540503500e01c1c5107882d40c0c5201450080d40d5440e0244001a012121034000660042d07151018946440081000c8842c08039810b01407880d01c0008580c1d02e0002d89041020011400e54a52601c5811072800004c0c000c0c0c2410710a405480d00903e44500010f10340c016010303035540404074141e200403030700c10719070540c02030003e101c11f00c02081c19031074600030304031400c80c91007112481e411010003089400c030300b482070303104030352021018508824000b03004d080c1490085505001c0c0280c2d4803959401d1340c100d10004590f41070411400c10034440503c0301740c3c1146500b400500b080a40d003200007074454040b40252070062902a003104000d0108005419200342c11580c0b68a0441e03c82c5001412036000b980c0c824824071071101c0088114240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 997409658 1250 997408408 997408481
    0x150e1e01092a230c070e060109060903080406030527010506040b240a11011e060e0f1b09120307030201061a1215040903121a030a020603060301110a03 66
    0x81c0c4039205107216403060300d504850711210784207800744103004c41095030108100100150005c003200103840e2519000040c9551500da00078020000180ca0420118138410b0458099901529000c03429980e10545401c03001044604241443c8040032400410b040640c440c60040d24100c3c0c3c20311014503980c04000c0406510201c801c00c0e131100c00d02d2041070000303882c02003c0c070040c0c9042c105200a9410fa1003030840d03004c884526140a62100c0c40d1740c030040944a0100a00340468600e142c7e801d0040e0440075603840103150300c910720707241795800380302681c036205440441000515400040c0e03503000481d51240c22040048000d5800c0990100300c0e04444103220140b000c2940100342000103c503800342c4001c10250048426801e000540284c40d102d0340200002030707009440d960042c8200c8101ca50444000401c83ca41814900d024030000360b5020a4500e00c0ca60103c0e003150302da481d10400640100048115800a18030018490803003d815420112950840c1075001202030b03407548490046074278 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 997410908 1250 997409658 997409741
    0x10506041a060d020a02010608060f0403090b0a020c0120070906030209071b03052a01020315011d0411040504051311030102030c090405091c020708070801150e1e0109 73
    0x70709001007441c020013540906100c0c1c1041c8004100c095480c45014180902034901c290341d040140c041009050700982c90100914440c40810318100c40b807103000b52030381d0b160080c45040204501e03556aa032040c82c426611040b9215003650021507907801d0010003800e107407100324003c0c19598009140b15000740213401e04032010310740d20003850040b9602107646501c40703e82c00c0c48640c0840a11a0300306083c00c41c0e03601c10800180010303036a08150b0640002400d4001380c2c2030400c05050b070b9030614070356028003d05c0450001d4402142140404115400c0c90103150040c1d82c000c2c1c90702040101a96540d00d410304000c0c0980324000340098410145801c1c1d100c2150340308030400c1c04205500380b50405500856004a142050360451030100f0b101c201800e110a040b00010381c0000c90a11a159061050324028030640000300180e0029900350414210948035210b000d040715000106032606007004001d001c0e2961908505640c2c66460490040a030b00704c0500e064140402d0034140c440c10392600e00e03002d81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 997412158 1250 997410908 997410919
    0x60609060303022b1101060b040303080403021b0f040c090801020703020d1706010c140a061505150c100b15040b03071409030604020f01170a0b1203280e030a05010506041a 75
    0x940b4640190380d040c0107485d9083c141d44d640c0000081c10515100039001440c4250354004480c03c06007402842c2c40c2006130601e0302c40042011000441c0d5807907107142e020302da05440100326080d801a080e80c1c006059405180554000181b00040540c0400c0c0012001030640700c1e0300000001c05440254440110b070814003007150722020f10301150000b0042d2000c003040e5821580f00c5e81180d60b500741075416190203241c0e031000001d018440ca20f01804c1c0b4124248080280c24201386120391240ea0781c18005d410740078003594480d52440b00340c0b43e68019180d294800107042c2e03501c40d40c52000700c1d019442195041c00040c0c0032400b00da1101b1301c06084401ca0000280241181d44440c1c00700015221504030306810310442e0b03d0080c03004105030a0440c842c0240110004000b00d000701441700d50108000d030701ca0030f5041040030380030040c0039441380011b46100c82c0d1b4080b10114064810b48484002c2c005540c2d05201d142940c004111054124074445c600030744040c4000c015001c01e00100c46841c1001c5540310 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 997413408 1250 997412158 997412233
    0xb040f0b07240b0321090d060b1c0c05090103031e022a0a05061201141324081606140d2c0a120e0a0306060906030302 52
    0xa58082014101d03590003a11a0403061500b0003407401c89990118115000c40d0f00d415840446280034061440c44170041c41c109050b101034500340388071601c030304a03030030340304006040ea4034044c0402e9620841c1c0c10a006043c04103009051860521906a0fa00c802c50780d899181002081e28102408800d040382e0345510340510f08807501a83c50f1220241031401411441340030481d03141c9200c0420349040048201441034004610340301030007800109030700501d018500420108105501031401141128003c0301040301e14101031000448039008040f0b407030f4003681084c21411b402c484800010140340c020a130031082040ea210034981d1a1801c07031708801d0b414201c0010030883c20380610010441c810b2500501460581c00341ca52000300c41410b4602d050300d0b034a10351803080d80717820070342c0062002d0612401004d0940141d541d80030604031141c3d074802003200d07d0022151a8407041d56100213150b00000501400c0c2c1c640c0c001800074040c1d4441078005208841c1240c0b20445400c3e184000c0c48840703030307082660 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 997414658 1250 997413408 997413419
    0x9050604051b010e0603041511041802040e0c0703020c0402030f0901051510030f02160501020307180312121401090c02160f0e061f05040504110c0c0f060c060c130b040f 74
    0x85420090023551014120355145660349100e2040310b45920101400f6522036052013007540f40543d50641d0254a5441003206002d0300e00c12450b416404090300d0a80b960750078041c50104d003451035521505400600210030711a450503806131180c420090749008100c655146820841125030b100c68194100d00f2a03d04084a907120f42c00c44a101c003000c8001501e8080c4014190205800d10700301a505650302100340201c190b07010751480d1360f0024205681103120305545403040304440c0e004040c07007404a610441400036406030411055400070440c070880940c0e4905481016004100c1590700500442380504641c401013104081a2803013600000031541c1031481905a0410207444036603c02050800d41210843e80b88003070300310702111390301d858581346000184401ea076030b81455540c070100140035008690000007024070b4581c00454100c0082540d010224402d403044081e4078441c2d00510b0200a00781c0c0420004180040010340200d030383c00d40e90741d0b14816500450154890b68030072604104070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 997415908 1250 997414658 997414669
    0x3150108270a02121c180b090424030209070215010e06060c07030305090306100509040b04060f02040b0418060608011e09020c0c1e010207050d0c0909050604051b010e 73
    0xd88030315074001c640c149030064001500f03d900e0310800c0c19181d40000320724004848483c04800c407008480c1049403480c1d002d140d201c0e850840c42d008403424600007084012841d0341d15048a425041298131052100e404600712085038030f214001a402420740a01240c4528400140503c2c04028000c0c5005164201400c0b01c0c21603201a01d4607500c40303000d000d070010010041c030140c0000c41c40790b120180e0310f6500805050070850010203c80301d6880e18841044a40c9070030310303415441540071a0400b01c543c0e0718608500184035000402d101a4030114010032000c04020040058448110884210f900c481e141142550014040c510000c0c0b040c5004012868a600c03612000c001c105060111890303d9140361800c0f6000540c0440d52079201485804443c04c107440003104a003800c0050703544c000d1010740042d6a4a58030700c00d0341e0081d08005090800d0103402c0401502503c51110240400010350400c103a0b60315055506841031300980d1000300c0c10007185c14054a1010040c2c54951042c0b014808114 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 997417158 1250 997415908 997415971
    0x509130605040606031b060815060703050a03110c1014090a02010f030f020a0e0906120705100905090906180604020a032306010e2a030112140d0503150108 68
    0x883e044d403580c070044006004418180320b14605a9010700455180040052054030007922550112181244200c030607110001103c1d269601410590f41e55249000304070300501451842c40030310600824a2040c0310000704180d004401c2d00030081c03100c81c42e03500c00090151000d80d14a140d95002c81000d40055000d030010b000491203e09000400e45020000b950aaa0001001100040c045061a50146001441503400141c1614410542d10284068541e5080c141c010148a001112501e0710070510400c4880040e00b030192003007606003044074040d56514070998610303240c0740401804034003205000407058881d40e0010070200000745940c8a050520b484110b0050707901841011000d40d20f0742c20400d1038000d002c100d480d01c8084c9407000c400d18850414002c10840d1004803151075004030b21035030550f419251a11001c4070208090b2502c1d40d034841e10100c0c5403100f406040080340a80382c000d40514071074581c4803001c1584070401c0c0011103040d00216000070030b491032000844400c2e40c1e06603201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 997418408 1250 997417158 997417163
    0x92823031e070315050403030e0d02100b0a0f0806100533090409030804050d03060608040209061212040f05120a030e030c041811010e011e1707020309010207050913060504 75
    0x50b00410348945500c59495803101103c0ba441d5203c506010030075030f00d4401d80000d14101809002080b402d014001d4481c2c0c942c0e00d001e02182d03210b20941175180c4c2d42c00b8014008240241041101907561f401194444508860311000c24180480c002103508101d5160564010002c40911041d040c21406440e000498a060000072405200d40401d64072103100d450a820b0007516003410034030f824507081d40350103140b029142c101411701c0c80800011340c1220005401a9044454010f140e690001080d1125011034030600a489058070304140c00308200d00910590700100c03c1c2406145d2100d00303110003c42081c804520030b03484001c08002081c031a1404c01048400241943c065061420014055407200201c100c807440c400d03440c8e1b004015a1202c5045828400e00b068000f003000300c4c0c0042c00f018901c500c0800a80049160701d8135184c8910b0900f446040d072241c0300701a80c107080100030b58079003002500c6800b41c440c428003c947c074a80000564887c600c0c408400303e481c0c01a035100406818050b008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 997419658 1250 997418408 997418413
    0x110906041518060e03070b0f0409020c03160b071404061b0507030c09020405121203040b0c0412030819050c0a030209031f0e070e0f0a02092823031e 65
    0x342040c2c4264003030b5010062105699201e4890244401c160401c49503030321088084904001c040140d036010000c0d00d045414011006848019882c2e079541984505803049002190703102b090800c010240302c0e001c0c024649562807803a02420040130100a105501844011035040d240110307240f22060280402644900150798105a803652010f0000d03019030448107a2a801160502190500000d8140800d040384002c1c144451200241400e510000d080a0401d81c034001c00224140e12020890740100a00407180320852081d00380103110308001c0d42c158160450420003400c10b00d02ea402918003e1716410052454100000c000780c0003984100036460709800b074030240c10300c0803050700c07180705c41e90140b00c0c408111508000c8d002802d081050300101141e601c14414171664030507040440c2d51042e02d0342c800590b0307101607000286604146c18120074208110040c140c8180030340843c0c080445a505a200c8509040c0700c0346010140074805006400d079003c24900010b501548581254135001d1000f03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 997420908 1250 997419658 997419677
    0x30924042315090607030e01060b07081608070f11011115100803030a05160f0c020103020f0c010903270303020c0409110a03050706020d08060f0d0510021206041109060415 75
    0x5410340d84082215900500d804c19001c00c000c0d00c0d054000c1d0701070138086000820115040c441034901d580101c003405404d004020807040c0c40c3d2122080780c0b040c503640060029858030031a180c403685401d0340040c2141c9400c0c541da44140b940d4080c14001c1500e5400c0000307401c0d40320782c00f40102e600000081881c6a650541000042c2c0000c041c0300650141c412850b002c2400d00c0e21004100f0480d2580300801e042000703c0c04402030055010300c400060603424600076a44003824941007180d4001d011030b0814a51a00c41c2c0c140401d44c00a0040c951642e0765400440c0035503c10070020582d070310301e100c09000740e045085860068641a0302019400b44501e10100c9089540004902249050782084400c1e5010310f40034040c8640403c4000369090103403401d0407140c40c184001c11030481020a074140100304803030580741003080900c070b2072035170342001501192910511070740414620001e440441c046c5140826441301390040b803040f101400c0028003082c1c9003510300f0350001e0381e8154040c401020003041d0207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 997422158 1250 997420908 997420933
    0x60f0a031104110f270a0915080a080a1115090a0c091a0d06020d06060c150203070e0d031106100302090112050303040305030901060324050a090c090c0c080309240423 73
    0x10039180a0408001d0004200300781100422155415410142c201c2e4081c1d00c032b24001440c81411240284580d10f00149201c4803020143d00e0b006040b200210094002c40801031014000189030b44158011f0b601009120313601e900d820200c40b90780d204405c4189600100300300c10700302905145205d0f48124001464805451648401c45420b03400400000e08010004001d0055407021803200015900c2c00714035508200c2005050745d07103138140e464003030900c41c40e450041c07501406500360300d02c3c2103a003591494900b41358441103240460200324441c01c040400440e02104400c0d9020b8190b034400021407454546031025256a080205450303095922400040001030200c0e50303010807030207480044d09001e03101805040994400401c0080314900e03001311a00800c411604034021034940050001e0040e04113007045581800200001d0f02c13109001060001812000032040484045040c4040a141d00300c0019410000240c401405008082c2c0c420101c0700c08502140120440c2c840444112000c0030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 997423408 1250 997422158 997422169
    0xa081819031806031d0d0903020f011206090f0f0e0706081009060608070809060402010e0111161202041808030109050a06030f0308040b011202090f060f0a031104110f27 74
    0x190400c50010740c940c2038074417400005007094900300324104050700d00c010754003800400c110070b20f22029203d4802641e10058070790080c620900360b01d0410105101c5140c4031b05000c0090502c0002c42014036192840e0a51580c4240c4503843d40e27004910003074100a894070f082100d1202c4050400c0056101000002503800d00314890100240a541c45125540c5801e0001a052090051142c8030704e400c4041003200517030b44140b40801c142401d09040e640da011a1a0992030210b100203000341940f1043c0d800720f4505d6000f103a150300d4038401c5500f480074a0700902240350300320460700020003402d41403006108090041e00b229034001000302c0001040c5a0300d4541d05070b03443c100c010640200300ca070410310091003000251a03014003e0904624030407105640071a135414002041c2404c40400c80020a002e550b074a031940038419001402c44681580344c1c2816148039061400f1030740b00307915241d0749950f440328000030344100e0b4944460050401d10100c0307070303041c00409107440d40c81902110031080c9055900c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 997424658 1250 997423408 997423457
    0x5060702040e1609110c0c150405042a0201060f090f0b0a0b0c071a0d150b030709060f0815060307021f0c030f110703110f010c050a08181903 62
    0x2003a0f124280743ca0072501604507900e410311004440c03030030401686240400500c62a8600065848a040d07400c0000e880c8034500554200a84c8103090171140c60b9042d580d140d241560301c204415420418003036070410390032500340d031041102514000c00200440142ca50010f0f905808040010949080000010319504000c1c0c000c064030100c0840d01170700e042e204202e802c014081c500c6106c040c0c0000c0b1001181c1900603e1444024180c0300c062051444029106880042c1840802c2c503880b42041d260203444400706000701c41c00a442c080c026481c2e140700341040e0340103e00003a0035240c03c0c13443c2c60920440b0f42c0b0040070300056114a1222561400003800384010004c041c0c800098600800100203080d034031212070425055007003100b042c900d03034408011a08110761600f0004025064030540605105070000001c503a54030384014400d0b0240c00100502e002e641d2035403000c45554510700e00016142012a0204255100c0044c2c0310701c46010039510380c819406400c2280a2000c4000c2c05010302c01ca = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 997425908 1250 997424658 997424683
    0x408060106030e16030b01170a0501020f0a020607020111040e4206030408040b1b0f0102030402040b010c24020903031305040617060403030906091a0f0c0c03030105060702040e 77
    0x2d40b0b86442804000038818003442c4610301058041c13040c038640701c214499a060141d400d00288600c221f20a81104208807502d0341c0d4428020f64036209030900c9100150010407454000d4002c0d000000c1400c1c1c030600ca2a441c0b640f811512a007014200b030002c5502d404000e240d441c0708848401803070902c0d203641c511101c1c504030106c40314072a10030200d01c01c1c2c0d0300710a003410140601e80c14030620002519260555042c2d0f000301c0c0746180c90320741001c41282c620035081e0303094107240142558800e803407506400039031145d4000d413010b1000100e5040111095941c0c4280540904001d91044030501400e4802140481808401504003860240020f0840d0b02080c500310480940c00c80401c080e003418086c0710000c285865042070b448180500c881d885400040005040666070881700382040038661000591a400c005031494042c010f210990328108146c0b117601d41244003c00040403050800212844400f005014608503444c10003441070f2600328007000c90b031164941e002a041240e042207007003c1d481 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 997427158 1250 997425908 997425911
    0x20904022101050109080c03070909110a030605150f06031306200301030c05030105220309030f12140c070905040c0506070b0a060f141011240a05060a0308030c040806010603 76
    0x140f601c0000b6120041c55400f00c215508012080c05041d940402c4140486a84400100d00086145040800803600340d05603a4094001ea8001c010302c0511b5000f14030036940e40c0a20503481d441681040104401c400c0d40b55070020041000824440d10840403481c03080c403d18021070820304040400f03c00c50051040b401d82c403a0084010420b00100c0c0f83d0603c000c00d070a07002000a81086440f0380d604150400314031320150150f201c01c2c0e0806104100c580010b61b000444007011040924215542248112550002458004030b42d1080c00c030490464091040c000000c00d15a4a081b81c5100034002c01442540d29050740369000a0300c1c0ca50000400300c00380b29010040c00c3d40350000c01b020407120310380c12046100d03590480034484107001000310781001c1401c94560b202003880c3c41040707505000c0c0800100090141d1001120383e48040e0b5849801c1004a1401c01480d582d450351000444d0002c40306150710910f00e80c01080414500f8004641100360314030307401c0c60161520a00c07403800303100b03070702141c0080d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 997428408 1250 997427158 997427161
    0x503010e010f18080405060c0c0613090b03070e01090902042705070e100e28060602012d020a2d09120c0e0712060f0e01080303040302100209040221 65
    0xc2d0600c0c4108807080e0096160368106400719156912140154001d0501901002076540b06564003003100302c403010300080c03a45540380380c00742030003c540c080d503c11f001d291424122a000b241c42c2c0800d0b4070040c3d8200d004415a1070b071030704241c01c02030300c5a188160b07000b0340d4034179070f044180c504942c0d5410340c112001d810400c4101240350003490400940d12a040704003d58091240114480460300125100b0717141000301500c500054440a1702c2800810240c510380c032090303143c0350045810030300403544175070002c0081c0196145400303040d083c44e03469191000312042c0211600c42e0540c1c040d08003400185400c0c1c010013125114681c455036405100c0208034180d40c2200055540943e000000c1c052074080020180307203613038075012aa9802e028240303d500d607500c00203900c0b0344100c403410041d04c29500180002c0e907807450200b030140010300071103950040501c008582d80d100041160702490b4903030300820401603091f541100a401620640380d009400300600340a1080e6540012089000343c031a00300503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 997429658 1250 997428408 997428431
    0x903060f04030e01030c030b0603072a02150a0302120f0609070e030a11121e06060d0803040618061b030e0d0f0c0f08041205010c021b040e01060503010e01 68
    0x202280108040d030389190000070000003a510100c1c01000300400c2c00c0108440d0310601040d40500004d4219980102d008000c000d80ea90f484017001d02c2d011605c1507006600c031420880d000f41c03101101000303900004003010362031000c4e0b6140c0080c0120001c41c0780042c206140e82121500d000c0c07041d0340c00c0700d11200c071205005092405200503508456142040004003002c003020946480202c1d00207811150141d0340d111007a03c07500420401078442106558025008100f020403a440041d0031940c03a03c65440040d0b10390515128580010790404015410346c1c3d6a90744000241490b259a0080710401c0c0d14800c000814500075107001421343c0b030801706a081d5540c0300a040b114a001403240a5204120440015402c5800003c0402c03440c9840c0010004038100149820620305000701150000200080c0e0300d006180d07016030b6184501e009011302200d841c2d00720f80c0c0e03d12142c1e9540c07000f440c0c80c0c980f0b03080e071038298084116001c1060000c1b030b48a0f5610002400c603402d00d1881d12280c0d441c1e80c1c05101c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 997430908 1250 997429658 997429663
    0x906020601050a050f10090e100f08030903070b0f070602070c032a05120c0612010503160602030f090d0c06081509040803010e191506081509070e0a0f0b0903 69
    0x1d00b00c280c2d41c83d50700c18680800201101c0b030007075240340a140703140490103005110351500c2010342007000980700141404100c080c880b6070a4410606d07000300f80c58001c954201d002c0f048a9240b03034001e000700512410f188185629900080060130451020080c007000544180080d1a03501c0c010039580250901d0340c203025000081450314145030031780444411a170034890215440a95100355440d20311050030040407403401c0c003413440159103c03501188450404868801c1d25050380c4003541a40e01080c03d2003048100e600c00760182c4800b5030400d004c40500c0e580d5400c090400c05078010851070b946642c0340c48030b0030155059002400001d0008082040c1c40303040c0903000e0300000068400420794907040c0c40e001214041030140c250040380ca000845c8083c0f0350041c03c03c1e40d102d00d220081003044410765529400010b1445244041400000001c003410b108249642c41218040c1859040c1c0d5502036044070035090380b9a80e0390b40104a400041350703450000e5000b00c003902c2c880050a81e1540361000305031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 997432158 1250 997430908 997430911
    0x30b010206070210020c03090904390302190b0a0807020705100207031b030b09030304050c060c0a0f03031508010e0106050a080709020304020f0d06050a0501090e070b071106040609060206 82
    0x1815503000e1000d00810550005041240d20100040140c40e00d100050441c19403052102903075000241c0d50a000c2440f16070044030205194410210f1402800d032401030500076000842006454000c040400250500702008080021f441480340146615500032031400e42008035041d00260b00c100c1001100c513010810b080183c901202c0e035004001c00190000d560325641c0c040202814122881c0e002807a5511450380040d56100b00321916919101185a649400c21101506c062042c0b807480b445034284001150b00d824121340207081c0c0c01e411034a601d600481040411020142e030340c01e0110f00f0b018000d400f00c0c080c107c14000400c0f6116440012420340e10642c028910030f88070321404110540c4002a2442140e01d802d03c05078490f952400000d1a01038216120303600300c4052071400c8100a00d6a010030b10a0b61809002c22982e42c803401441c00f00c07682c10085007605da000e26420300c51440b025001e010010b01c1403a60410b1280c408010a1954020f075001d1004180c06020611507075805010302d6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 997433408 1250 997432158 997432181
    0x40f060f02090906151e070f0506100f0f0501050304050a0c0815010518131e03031d060103051e07030c08030903070e061f030e010515041104080c04050709030b0708040303 75
    0x4a1740403001c070207040f00d0320409a101d900041702c6c0600d040c4404454080d14140c50700104690b000c003281d801c0c00d0351106000c840742101035012003800304d256910700c061001034503004840b22100c1e41c140001590560300c0079009070307940c0c801c0c607018400090700106044040c000c2c8a029020f1800c5a041c80b00c0f8810060b00b08034820940303800c5a1910414883c10141c5c4400041c60200035224030b420034150726015510340b44030361040c1307a0b8050203040e0150480440041040c04607502c2c407654a60241c0c0311042800014020780151402d40c40000c00300039010030240da50015108400d079241d0712044401a030303034483c10180d0808a2803940c50321b0700b8018100103114070012400705103000b0002400c060b1124440135151502401e501e00342c00d10030b610001d64040b811000700164100384503001007260010102a02c65401c0007484003241d22000c090f14112403000004004107a2034808010207803d00810542c1040310210703002000c03d040c401481c0c01044079403100000c034206410024150744420020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 997434658 1250 997433408 997433419
    0x4060c1230060501020c03030327030a030b0a0b0a320d05061c05190f050d0e03010e0102040308070204051807030f0b060d0312050c0c160e0f07090e040f060f02090906 73
    0x186c407031b103003c41107036800b0003c409480c5000d03800780000d016000701d002110045100c0402e000b02d00e15007543c880d6424007006c407845d9144503070b80c9841c0c0070b1621582a20a000818001c180400c41c42c004007a5408620202d24142408030b0254034403009400000d01c1c0100680c9450922a50b400c0418409103060348840c4904900842030712440d1341d840000ca03408400b80001c144800c20711007250002020240c1c00004c3e101c4107101210010201500c0c000e0680c425444e0103547c840d9000144215000c683d0f02c040c45608002c0076408100017800021701e00d401c545103811150100b08801d120309006140310f2810303000c501040e81401080503000410180c002c220644410b008a504841c031030b00803581c50200402c09949400b6400400c0c042c0d0f41c0c2d6030000d40b05000e05000c0104001c500c20042d55a8416200b4513a074412014440d4544d0030750700d18000c2441644d042c841c904004c9a4258400e015161000c01c0d000c1c0d681d99581250680380d00c1c09811a80820781e00e00601d0070840c3c964000400b01e56 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 997435908 1250 997434658 997434673
    0x30a020c10090b0a0c03030f0c0c02030c04020316030b061315170f0103020f030109020a0b0c100539030a0509010b0a08030d0c0c08130e010b04060c123006050102 71
    0xb40c191a03100c2c4407002c0b41481751a40601007018800d4004013200b0341c00c6982400031440003100038120000c100c404a201e800340b003450041c5403e091003600d2251032019036030952440e03c02400c2d0000e040d8a000703140c010710b08121401d060491303103190710000c2108102d92425001c2c40380d402829000c0ca0510b0f594008002d4090004c0c510090001710b046d60313012510b2903100001c000000c0e00611000340c00a42010010b20700040f50b2010b140600840d0071010309a5400200240c1e508048403021200c00d0410984000f040c004408100c1e03144142400102a40c22103440b443d5006089400464401c00b000b9120b01c01c22100a001307024854810000391403d642aa00740b41005461703008100d08030b80c005c0e07911011000600d12511228245030380102c0e145903035009003a5420003003402d9005240049081a00000d84170020700103e60440d011555081d854202e1950b6404880380804c40c03690801500c110992400c1c90412823075103040c3d4260040b250b0500162038507405882d9a80d00c9141550405003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 997437158 1250 997435908 997435919
    0x16060809011802010509130e01050a0f06051e18010b030114040c0806120a1e050d110a031808061006030f0903050316090e16140c0307150e030a020c1009 67
    0x1445100c0b01642402c0c40f9440c0d14207000842c0c00c00303070804c0c400c0c5c8425007007050590113079a041d488140200c90040e414051341c004d41c500b020585a03141310306604505104101c0e820b40e00030411100002200800d6200007840c0081c070094136882c283c2088070310400000c0108041c103990000c000322020141c03000c0c0304c0d030701501c40040c0011800501980c02900180c81c8018405070511641d04407981c040303d0780c00301c242c6820400c400e0301e20550007121140300308892031444034098008a40e41ca40ea085c000c0c00303111255a0110790703410140c201411590f900200110b00118144181c5110f200c1e020f04c0b41c071a07940341400060581c1d0304040c1c048403a6107060309417804032764020210380e400880b4804c0c107070b0b100f0000344084483d41540e84c00800354808001c18001034100500c9910000d604035075072540c03113110305004c3c00f000e03129141300301071540d104115100028042c000b98118814007c540080c0820903102c035a819980155071800041c0c010207480c54052601c0e403010f1207101c04c1484c100740c01c0c90409 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 997438408 1250 997437158 997437191
    0x170a060b030a0504020118270e0318010203160308040201090e0c1e2a06060108161101140702010f05091209011211070c1701050f0106031a031606080901 67
    0x30707088030440c2d030701d540000302135900039181100ca502c8400c00c80c1044a03541d10014100400d0802e402c007001c3d00d0400707806e0301c2c10305030300401101504176000741d80307008036003c403450464400816482c10750005101c544050198844208010b43c066140c4562920741413000400482464006030074884500090050403d03000c020340341d81e1201030241808200280d08079402a01600c441404501c40240010150404116042032020311280448941c1e40365000151007151007101c0c00190024000d0480e10381e9403060710b0420107005201c00001e64500000d806451856040b114000940c0d150f6002c40c014048500c9000d0780001d09001411104044004100040c0300c0d00494034108440009050f800754000e40c80b180c0203480300c1103ca40c0d20295840d00e00c0c940001c40c03060041140443d00310541e420410300415229114020903020160b0801d81d09900601240710071080d520704c95184c0c3c0142c0e4504000b40e0500c505080c80d903d6480385026401400314500414404a5074140100240f601e000c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 997439658 1250 997438408 997438411
    0x304110a1a0904090c080f1506090a021804090809010e01020c0f01030905070807031a010501180312050f030f2d0106030c031b031a010c1709040b090403170a060b03 72
    0x31560755454008200040250418071000762400740f40c2900050171030000100e4001240c007180640703e035907500302e0704c141904601701c0b101030b0401c010f40b0003d010240700d6401046200312130b108d00c505502850002c54210b8020034030448920300e0026040e1129030f0000c0e4401c01e005c4d070034401005040c98400c0031420003d0400b18050505848421f10010800c0500441d409001c071704003143c9a4566034100100c8500002a20028000708000040307143d521440d1000c01c618103100400d2841132a50342c545007034080121012041140034040580c0044000004602a807080340307021520f410614003100e402504114982c03060b051088645031501d66403a01c80d411100e0900300010f4a02d80c003001078001d800046004440b2002011030450700701d03055800909940701b0080d001028450b45401910f0166800d030003d0100004501040c0000b41040c0c002d0013901b5015101180394100400400c031041c8064900b1808200c840c1a48400461481010b40c6d2090782d0030f170180442442d0030880c0026100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 997440908 1250 997439658 997439699
    0x52505070609210207030210050a052b061e0504020c1507200a03021501050d0807021801030f0b0705090108220b07030f2307080709080a06020304110a 66
    0x1c8628422060000001200e03203d03a80d0f01d036407050690107032400203445525034081284100d40002440c0200c6100d94142c400b07205103502ca06203011941e841c0700c2681c881084045428072000008010000d005004160007000c1d45114104594282042014814529001103000d648180130099503040000380810b00761a0031640d954190303c1e8144c0846480386201458005a403610080095041000070442d42c4030f40a642500c1d0740c1c8900c03284c101d13103504081c4a20769000160305913070b0001ca2010001030850510051500381041401c5501483d80070f0241c6c01590003000108915003441520016184d005120b480d04034584034000e00003074030500028000e440c5501807540c400c180808003462011250390898401882890700e940010090004d010b0389158041c10325040e04440d140b0742c030f24422048007115038070603241c0d1a04400c5030b03005002050034041112402c4005401c0c1001e00603140c0d0f4902603c405a0750740b915049c0f030420400c2d8580c0c014024260000108020700420740b03461420749 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 997442158 1250 997440908 997440911
    0xf04140607050624030706320d1d0d0c050706030213090f0e060411030f1c030b01140403050c01140909010b0c030903150612061b0d020c010c02010525050706 69
    0x20000c541380082265107054071905803060107000b0901c65009010400302c5004451090451607048510401900e1039000003e6041d0041c865810002801c2e00b00601a81800c8181d5250302d0405010302c0c07074081ca60044201080403002460b0500c80c061107084041d1105050035440c100790840782d400c04032001e214200c400c594941c41404441c619810118403155044211421400c060800b02c41009140a2040c8280b01d092078010740c820000caa40d140c4402c286041031420207070708005078003500c070100302c143c104203221455160742e40d01800648003640c011702c0100b541c1424a40054007420b1a42110300c02c1d0b82003440305100301e83e145800356064610424400d5183c40079000390344d00d1400380ca00c00780d605014541400b005c6107043c08500e0300c0f0f11400c4036229100c0d03d4400c525611044192515011074861078880d02c1d1450154009207444107078010014645913550101a00311138a000818005035110000e10010038483c1c9520217139540411032015001600380c4010b0310512404900400c0d26 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 997443408 1250 997442158 997442191
    0x6111306081b18102109030206040206030a150906030507050d02061b0c18060a0b03040f0f1b081e190f080705010501080307051212040b06030709020f041406070506 72
    0x5400d0510301100c52401928006604c01c1c240c401914a0000310008075100301510075910000606001c0c1141c401c0c0c154014000c40c1d1255028450150b000070321a014040c1c0f02c65121700c0050011030420300070300a602000841d40e01354a481e604183c5035506c118401c28038081c0e42c001681c0c980b022038503405000202407900750b040c18410381c2495036030080180c0c4070604249292903604c5020f03485103d02e41c22210006580e8460100c00d210380802d0314058a603c4034002908006001111a2200e80d405000c901c40c0c02c4200e950001ca1522417a00910003d41000c41c000815074803a10442040c4518036001d810098a2508195120300c01000b01600042c4092812001d02c48401c003140e8001ea0004000c3c001c640e121174950382c0d03a0b4013440c0c04440074440d21410180030045001543d105d2010305001c25420f88554442c010380c0701028010315450f004045000607400c1c103910041c10503030300d900011900c40f480c000344a40d0501100368401c1c0030b001c04210356000101c005c00e015511070b04548000418 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 997444658 1250 997443408 997443427
    0x4050111010b1e03010f0c0c14100c09050f0a0510050f04211b03020919140f091e0712030c0f03080a0b0409021003110706111306081b 59
    0x5041c500b41d6040e007298943c0b08203c0715041c50344022410b02c03c150000e01115038101548421103000e4860400015601c68801002460402c3e5222450200d1001c541d0a17050344080b44003203401100080c004074000580400850801300031b132284081c0221340c0ea0740050300d0580403d00054291858900f04030001800042c3d1000b0042a14045c01901140f50561507440d00c81c41d515042d085000d0b100000e18488141480544a4000f4207403580a4401d5200f44c0f40c00c0545903161105034191344072141c0301e0790640004104c001e01c00d8032813020340400250b01d0070070020a1b8204000f145405030202c8181806d03106804002940344110342c040007000407200300c0c2c1c1c20121200454041e0042030078480781d02d5101450f80c406e10140c02103400700010081c005440c4100300869012800003074000c91703c84e140400c103901903804034050164042ca0940f51505a98440301210280d0a001d080d03420040303610002c030407414881078050099405c101580c1c3c01c0810005401c0075114040c99407000d00001c0c014034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 997445908 1250 997444658 997444661
    0x3010203160e010c05060c0c160b0a0c06090b09010f1b1d01020307080d05061c020927240709123f1107120204050c12010e0403090f0b0405011101 64
    0x41d50740c02c0300c246e801500b803100e6600c0031548100c1c1050b505220724240d014191101900360011102102c500c0d41c9482c803002020303210019442c0b001e980856a50304214003042c031403602039103e802d0341000012000c1c3d800ba02d072011600c0500303900c8900540001911405500102c0d1180000502c0200300404040080100d28501c40d060008040107800300b201e101c099200c0c0c2205010b0282242e02d1050710310510101c406c0c0c4419100041e5120400001007600760340101807086100d00807840300310b1404040c46030a86403c5852900d541e1580010380e10a00800650006c1d07600b08c480c0340f90100780355107010400d07480d000e003100c0d0140c984213200b110080c0c410803008010800341d003543e107006080003541003021001b0b80b00c0310070240800da52240c500f420f0030010520900791072074841031300d01c15095030302404000c11004060416480341040700c40c0e01c4c0303840d0091045c020000c03440c006480c3d01d070529000304601030700c0e0f100703400b0320a20704420b214104c0c800c029541960b000780381062003110400901c90 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 997447158 1250 997445908 997445927
    0x100f17060d17190c020916020f12130b0705030f0a0302160605011d0405120a0509090112020a0b040302060304060b030114011e0b1e0a0210050c120603010203160e01 72
    0x102910526000010b0b0b040c035003406800e2a00d081c00c0c107192901c0900700140c0742005000c00c02580311a0b51000914080d5400400078076190191044801d09c40c08002c1e6189003082504104090040114038950900a030380b96600240105042450407d040303035483d1960381c0110301a03038104080c0800d2420482e442507050340d441c2c01e2a8031043e10615001d00705400107000038010103242c01e44842c03140f000201d0300c1e40b01502503035004001f4118036406000c2e41210760000884001040001c005035442a84e50040d110701a01d118202c3c0e01e0400034510403c102203c0075030102c0350091b030510007000540c0e15030003070b43d40c03158002d5004608249804002070040041c1e260400403880c2050000c0b81c0c2c0402440c1c181c0118040c0c050755a0a2511113a0000940c0240950f6848070400460b0511211070040003829000c0100e004803880920a0b19000701900d0f000c5030910394284001c650443e4404401903404d0f00054103500031842d60614070745079100c080ca266034210601c08035404a140f564425082c24 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 997448408 1250 997447158 997447163
    0xa06030c0210021207030f1a040506010507050f010e0c010c0302060402040218090f040210090f211e0c0501090308090f1c0b09100c081603110711100f17060d 69
    0x4541d80d42c203141c030301340d1191825100100040e2600042d403118443c0b43c480d40780c11050035030300e000c41c0b800810200701c00b600005041c1810400207111100c00280100305000b185040d0800100c0d07082410300031b0600c1d060191400c1410480e1007212100400d80114115800940580b005070751281040001809829031a06064010820f40c00300001d419020410314041c0e4402c4400051031540c0400864080d41d5502601c104d00c00c000c02d017004581c0c0320a40200e10b503194071082d01c4400703425807034106c8480044081d501500d002e100482c020480c620405201400b001d0800c0500241151101c1300306028001d03106005d54401e101c03400a0b6920401f0201e0100c0a041e10300c07443c1507503880d054242040c140c81401051250f01c1111001034500e018421441641e541d0340009580e400303014880e403a41380c0c0c014009250392400c0768018200c007500200300a40c019410020550740c040203004000381c090f0f08400c200a0404e130f1000702113600c032040c3c0c0303215008016610b446448160000c0d20607841c44400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 997449658 1250 997448408 997448411
    0x3030918060b0409090308250e0d0b100608010e191d0f0304060908010b03151e151002010b3712170304030c0f1b0f1505090a06030c0210 60
    0x2a208040d81202c4a558883d544d032007016228000100038143c623902c00b01c0041d12010201210380c61265041c1c240000340244036a20a005640302c421400d40d05a408082410079244e00f886803d400c2001c113401008140f070301d030074586030148000000450b40b0345025000d0341c407440c042e054040c2000d420608000050b09807101e41122003001d43e520340c4144112000b14601c0d50001585000c18420048000ca015014108a080442400c02400350007400c80310900103a170b010400f0300f018070709064032851120700481c144842d403004000480d054015081300b16814404055600c3c0c9907a0140c40e4440403080c0c1e20f040c02002d820080e01500401c0900300703218254001c0c000344500004082c82e12441c0200d040120034a408000b1491910003100c0140c007060346e00c42e100c80022095100c821003940119071284001001902c01c0c0760405c12036000c190700b144070500506c0380e006003504940030030b01c0900b0b00c41d01c1e102000010130b0405449110360828581d4460b501d590290090040826407200d1810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 997450908 1250 997449658 997449667
    0x80301151412191505041a0d030e0a0801020a02010209120109120e01200a1406070207050d0212101d070501020705060705070e04051609020301140f04021b0a020f03060103030918060b 80
    0x14921020104ca10409102d01e060105141960000f8402c2c3c001c250005407108001200360307103007542c0d1000400d6400b0f030401820107000581c2c900a102034140390040354000f590703600304c0740100121a00301c8d02982c0a0b59140190110029070140c060801c809a81d05140d000305155000699504010018042010502c072440c0320403600c02081c9245214480d8070070f441c08201d6085400d41d280350846011015a1101c08140901e19118501805280c4020416000041c0e00c01c92142018000020502e200351952440701880d508001050050300703d220061400c640b0341070000b0b42da14110b00c036103030180c42c000030b010f000d1000510500000c0c0c50a489462103d05003440d085070f80f00c0d04c460118540c4001580c010414840c00d0007164120f41c003000040c3c1d114047da01c2080040340c184068140d10540c02c1010a209483d0410154200403415010700b44011030750050041080314030214900c02c0d0095001440000c1c0c1080740c54040d10010207000b21501e000c89680360003081d80da001816001400304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 997452158 1250 997450908 997450931
    0x2212a10030e0d1e0f020d0c08070f0506040c080303100314010e0115090f02040f09020a0210110903010e010b0117151921030207140411030408030115141219 69
    0x10303c0082246403180400020402d501d400f104c900303904030012001601f100680001c00791080c811240c0720b034012a1558501501a9140c0c0d0484c0400b8004481c103822190401040c003409864090080c0340c10405035256180c140d02c0210552682e002c0205502d91461a80e0403070328095000f41500400c0308020400014907107109018140540708074941e0700d050880800c1e0030481e90007554110342c81603590380c6200f410a403504001e9041218081c0461040414014070010342e405282124a0fa10081a968000110500d42918110100380c1c2c91603040208010150f68405074040c84034044940b8503030030f0b4552001c1c1400007000912895070151031001141c032041703081c1c41e83c0822240f0118240c400c00500c3c069241501c1d0035200064096040040c1c00c200c0e0030542c0034030f02d640c0c54000304000354109414541400e65001900c2c00d460600d004401400030b100d1031071414804280b00c0c102580c00b6040041015680d1144a0a0124901d1034002140308854940764000107888044002d010040d07001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 997453408 1250 997452158 997452167
    0x2190320010603020907030e0c011224141206040221010c0e04270303151206090b07053c0d09112d0d02212a10030e0d 52
    0xb40003e030300c294031700c90210b00818000e2060407907008031040038065030860440191880020b0401d0f4441035a1180c3c1501ca0030320f401a507002c504086c0a41c880801400c2118a601d010f200102050080e80c03002c24a9581e540300188241d442941100c2c051010b0301070050f80c82c01d6216290402c0015820401402a921f4112600d0301c150b28040e03500708154080c032139507075049850314200c60020b4011241c07030f280440d1107a00a0326100004110a6503096510b1002a045110044d01a80c8241d59050108200950103100c41e8024659141c5079040241510b007607520b500300c0c07401865010180260300c40c036004440c0404031044900b61509600e480000300400054902c03220101d490110705011103005e0315141d00c00d00c907600344c0b88520a803c3e119908481505a01d203c4480758400d4851a208005980303e40141002041c030b0743c4408180300d0350003507592034910017000120040314100d82c40c0320b02220351096070311f03101001c4900c0c90301041180030543c018520001d0011050069080e00031003190403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 997454658 1250 997453408 997453421
    0x60c07020f09060d0204051f0608010f090527070504240b040b09061305090711010e06070c0609020109050a0902090f031501060c080f07110108090705010219032001 72
    0x94030981c8181c29414208810158100d41c1990f02040c040101000f505060344080c0c0d22818016208810400101c803414000625500c140c00180c2850014440b8040c01c2c00100e004100c00e04050003e0f081c03008000780d24205040b00c2202c0c840700d10028944203c0c04220550007410054000c124205000314586101070548008501584040e5030004400d04000700302c50440d6241c00c502c90518101e00200f101d50b80c800038409007094200c00700070459a664201039405500c041c1c5580d80c000014410560a544e200c80240845401020802281641024510a03040d50100d0009030081942c40140c6030015103401c0190800c621190200c1c86580603801000d5640c4201d803010b0440390728108041c0d80d00d01400c0016000e803058401041001d01602c0d400c02101d10540105040071001480d000b0960008142a5600415040900b4103542c00c16102508a000b140140c4002418030740040d548200940100e4000c004c040c1b99035051600c41c41444440c46500c1201d100003031880c07e1000d028203903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 997455908 1250 997454658 997454663
    0x3170301060e01020f0d0c050111210112030806151605100e0a0213020c030d0e0105011d100b0a090f0f03110913170d051003050606041e0c11060c07 65
    0xa8402020b4065800094800d00a480d440000d2200e8094080c0403180062183d101301d50540d02c2d10b202c8240c0f5503c00000e40700340c100040d10340c1346d00d01c0400c01c040102c02042c0d1040c86840185c00364030021070760094450380e0151050318907880100c121909255240700c4c038100760800e252034411200411030b012030b010105006840003802680c2100d600c0700d8450390360301e4000b5804480780e101c0c41d552400700c2e000342c00d10026a40580b4100350024280711700b903440e0359441d0030442e550ba5005000c1c04403421103402c00200c21517003135007240c90290b0342c50004183da07000b0382250703941c080794407003080e4403402290f40a0410a100303040050b6031500300707034a0890740d03004c1220510764190740380720503061520000744600301034114412040016101c12a400449072414241c0340700410807003c1d062564000c03540620042e5460512151a40c1401410b000d4003410841c031840c02d0841500c15101c005142d404000c0c55000001031030b428150095801400c401c844002c98054041005441e50009016261050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 997457158 1250 997455908 997455917
    0x23060c0f070f141b0d1203060302090c07020a150e0f1504061101050703090305190e090411030105060108151504080604150e030a050414042a02010b06030f0105090c040317030106 78
    0x190100d08504e04607514005035600400e4241c9540045403c8500002000500c0c4c02c00184280c3c486d000306203510390495181c0700c1450001115011410000c61400090078a15000564035090040003020358042c088014031402840c280024559501002c500251070100c02c51a9126079408001e0700111b03045c928002c0c0c5502e0000020047c9029014000317400350300d550b03144e1a020403514942549110112a0f40c100000400030780881e80302d424102e806103009207401c402d4200170804160945e000201102c1c100064030301031001c0d0100881e40d00c0402c4008640d0015040c0b481714540b9080d014651040e60940700e0f142c1804141300e141d041443d50880d510303005000c0251120107a82da2445101010800a1410041001042000d0071300b4130760742c0b10080010404219255604c500d41340780c56052032842c1c4014100c0d504041c0c0911510004c0042a6102c0e41140b620034461980c6280510445009401c1c410026044988040895000d140e121079441c10100d0382032240000c0740c00c00d000700000718 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 997458408 1250 997457158 997457173
    0xe06010f03020a030b1918050c03070f090c05090d06020c071e06050901120903021c080c030c030912070f031214161b05060423060c0f070f14 62
    0x2046803032046001d40360003402d0030704018a10740d5003d140300c41c010010340070300180c80b001d401c0706140b03806142404910500900c480400b5400c0c000c1c100750741501c441d071190344040020407c05141300310340811901c1081c800240a00c9030715043d0790038820744880f0396100400403184c0e01007140f10350140a00300c0c50f5034100c4000c00d4441c80811b8850040c81d200b0b0013403020060040011522540c0204038159062502d07401c2c40d07841e05420702c00e03140e05000031005038019180429549c0a400d01608004001e450481030702c1c103000340f002c20b81d0b1002408034a01040c000000950a8000300401081405035403002079503001d06003001c3d1032980d01003108400040d1401990b03c1c1d8000c1c10300502806110043c80e001c015240d9805c4602185020b2039500c050160344200300a42c2c0b150713400d2007030421f0b0244014046901d01403608640360341a22559a88031040380401c1402c01c40001403950788202d000042d1907a41ea1132500c030301424010000010a1005006583e4041006030007410ad101842c0c5030448210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 997459658 1250 997458408 997458419
    0x6030e190f0b0c0a0c0b0711160e092e060515030603150f0a0c120c350c07080d0603081e0301210c380703120504020f0a06030e0601 58
    0x41c1d04c60440081d00140ba4a03020f0404100c03036240d00c5411514500302180f480c0040301e14181000042e005014400c003080508111141100c084c0b80c2d03001e4200805003114540b003459442030b1650000a03038400500041c40700140310001c0c2c3c4034401811000380345410005515019041036441140c080e4007901446440e07280d884405150030340945855800a1480d5642007000c00c0240004180901040110120068542e417984103170140024256503801c0c0c1c505e000241058544501106843c00141901c8200c03210300700d2540117904a403202804523603822881c1400001406031921107000a8500b000c00802c00100b83c1c003c040860100507500c08040710346c605a030803800244070340403001203142c890280d864a00100c9030340b460320400071403007041c0d141c422075440c80a00300341e03c070052030101c40701c40020041c894034580e5405802080c145007040d19900140700c856104031a90613251034801050456403251556555100094001c00303200c0d40d0340d10000c010745a0400c02110a009010002c200c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 997460908 1250 997459658 997459681
    0x90b0307180f1b1806080c07150c050406090506040303050304120207050a12120309020a091d03040602150c0307021b040905060f0a1a0a05010f050403050604050c0a06031506030e190f0b 81
    0x440c0e165403a00801076030740a0481d81c00d60312611301141d400c441002c0c0ca12780e40c2e0041c440c10f01660030503540c6c84c0c0c440d030504401a10744015031300480e11414043c002000040c0d40802201d41c400ea01115110040600310b1050380b40214030740001d94415001000810f2140b05001420b00540c001d9240c110800e07d00e040540c1110140000a034102018020610040707050340c00011000800f002d4031080c2003201000c076400d580050f0001030060300900c50344006040f00d9503003260412480c415407891824660000707035544851010580c00b160407031064080039641ea80c000124550407000350303150352402258056411900b110040034951800342d25070031440440c250b101d82c42e40c029246820b500c0c100780046d01c03c2c104420f015030401c0340810000c40000c00900c001800b0b5489a80100b1445412404006d0744582c541c000408248c41c0003035448003003e40c0c0070081d04071201c5040005c1c4031701341295114105150807000c0189086911002000c11801c1111803034518091500e850480e100c1034140b02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 997462158 1250 997460908 997460957
    0x609110402090a051203120c0c0f0319030c091707080601090c0806130204050d08250201020c0d14070e0a0e0303010617090109021003090b01090b0307180f1b 69
    0x29003082c000c810500c49800c203145002d00705c0c04910106c0b4148500d1201e056084102120514001c2c00085140005440100110b03229601c03c8405581801c0c0c03003960402c0098050300c112010562224601c8100e14041d100c440c000e05100e03038181303440710181e0101c035603100c5580c0304400c094400c01c0c2c00040d450b0218410041002495a02c4003a141c070b031313042005980103d41361490307203042d130030080010241d44111340002c1c11440307480561384030120071440c1d0342001c102c0440080031380c51b0b4420810041c1c0e40443e502810700802c4841d81011041c43c2071003a080181c400422949206007440480c0e1801601b510074411004e01305d0a01461b4400071680341c89000a10803000800c0c900d880e04400c8200c89072420b51f00103030120001520201704d03000240128600400301001c00c0c0c0e1060b0034018010302004160141a40200c188198080080403d80e511400d00c40c182150310741340203910f10341000d41c1241c40680b810010911820885908685003251150380c040041001503681038014007101c140c2c40c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 997463408 1250 997462158 997462177
    0x1505100b1602010e06030c1c0b2206050405060a060c05120a11160605191107090f0b180601030207151103240a03121b0605010906062109050a0506040609110402 70
    0x21410608d41020600740b0301180c0300c0e411841074845034a03620b182c86404074034181c941c3c011513260043e030241c92000122200c0d90080f6014508260401c4029141c40003500708507409864a403a030540340b803d000c0d062070501e20400c900c9420000b605032020354092040280c03000340320152024108201d0480300b0381c4900748691004124184400c01c02c10003120707902c0e050381016081150700a00c1c1d2400301ea0405050b900040403407a500d440c041e42e0f8444520036030b460358400703807181000540c0e4a1303080501e1a1000b4103a50425400290080030090f150030404582c0801c00ca003032040d0700900030f40c40100c2d00111403440914038140084089140280c1402407011406004d1100e000d041d138861170704107000d940b4104140040203d005040c900c01f140b14807519800303010001204e504001c030310780668203242e219800f009215403401010608180c0840580350304010b0024080b01e80740f42050600500c0d0340c015005001c0e43d0108428040303143c01c1044a9031041c00492034030169031040200702d001d00d0384403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 997464658 1250 997463408 997463431
    0xb030f15011203120e100605030109020f040c0c0b0415051012260310060e0d0215090d0b0c030901150602060403030911030f070503010b0d1505100b1602010e0603 71
    0x401254158100c82032610f8020301d4024034810200c0c2003c8259600806004011780c0100300c001c3c58044184076480c09004210000d015018a40d000a0580c2c03074108000c902c81d541d2050960001805001d00803002035001d21012003d107050308104203403c000740f0090f45010309100000e0000c901c0790110340b094440c0e0030340c1c0c543d001015031201e031410740c0b14007031f0079030007507098040c0682c00135030705006d1071081d40c40401d00c811142c1059401000c3c9052120002d00840c0c5d01a0302c0303401a81d07141d21096502119007036842d210400c09000560352500800081d0a1400c4034080c03002d4040c000008501c11180c010090054804d10b9a00f410007401038450742006801480105001078840d070025a90507000e6400c0b0724040b001c8800017030414228444414555100800400181c03c0038051601c24540c200e480c2d0354840c40079100c040740c09181c11503444455603100c0c009142c21406522800107054185105078450084122030380400c00007003002d80c04260100c1a000741898220100c80c46412015603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 997465908 1250 997464658 997464661
    0x30b09070b13140f0901080105060112060f120602090a1d24010f120614180106080c07050a170301031a0402130209040b060a05030f07140f180a090b030f15 68
    0xc00ca09201c3d01403169038440d103016007025895984200850181c403000c800040e0720f0510a0014001c1c1100248076482c060408104001000e1f11040c190f045841c60301540380c00742c4240c903002c4024860f84030003a0b882640d814000c180101505103610280844289100c4a602c410603050f00c901c14821420300c0440007810555101e500c500107200c810200e40c14444041d04134211942d05481c43d60300800049074403619031040c00c0c41c001ca0340c07842042e403100400f5125410050300408003040205516920710001503080c0400108004803208107801c1407401e5039100c0f01780c030007407403e5000788410784c0d4144a800042a102c042c04150b203005590062075040000580e0b0502c0c2d010303400c02024543e002d40d83c0c00300c1402c40d4491030000d10004915543d5a42d82e86003043c0d045018030400390021040007040f8075200d4500c0b00302000c441c501d14904103038945502c40510907005042c258481160000407082002802c500a5088909031100c1103083e5205031410442282e958040c0e1340642c0380c4400b1440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 997467158 1250 997465908 997465919
    0x160c0b0d1e2a1806272607170601180219030e100603120f11031e0408030c10050c09090402040c0e090f10050a03031d06040f030b09070b13 61
    0x141e1001e4014030341881d55030321180302801031182183c2c3e4822808501751018948084051014a000340400d500100043d035040c805511005107807080001031443c1d503135562007000f95040090030024414106120941004664402e407980d20038800d1805030f881c1d044540706401c03d54002ea44030100c07950404048408030440c110090403045060005034007136042050758100540c02110003a50240c482d41100100c4054000d03c000140541981000300100c0030f03140151021048400140054482c0074840207481e107400d0300c0348242da008001034440080c8524500c0f50100b6001d40352101c10904022a941d40e400a00882c481d828503280d014800c00c0010300189002e500482462880345001a080f0185902007010640140c401c40707050907006042100104110030f15501800c4240e0713800a99904d581c1c0d000c1c2c21001039004c042a000b42800001075251210400e440080c10003c1c0c2031000144c0d80c2c01c240c2c001810070b44848d0054004c0890200340c0102c04001c64144101d0307004001d240300e242c40e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 997468408 1250 997467158 997467221
    0x61106010b18090a180f140303010515030c19080a140709090f09020d0308090d0f1d1219030e09060a0b1c140f160203160c0b0d1e 57
    0x138060103c0c1e66907104114061401c641c00c072030740b06110b500c005c0000d4220b420940425000c8041c1994039610400046c441e5031160783c402d941c54580c907010242c5036229000c1201c0a40107000d00e00e90b48050340c0c5002100203501500c0c640c000c8100c0f410070807801c410502415085501200c403240810004e0004100a418a80c850f1003100b03141c1c080056012060b0340000c83c1c0c642103c200760006003216040c003640310003d005030820103403d81440030010a0041e0f000d400f01d11392001a4224603205032707001601c0e803079503142541c0144011301aa400d402c1e0704201c09402400340082900010711035800012030341000160399000d10001401c0600c810310b0301031221102e5002d80c8900610644502c52000702c12000c1c040e0014060180c00a04001d1800c214050383d403030300c01040e5009401e06e04c5480400d180d0040200c44403c0e0105d05c1c4140300f480d1034204241000416402482031000c0068502d50107100c0b580000e500290021002110081a00075007050303845141a10105814071031584218582c01c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 997469658 1250 997468408 997468411
    0x11b12050702040204151e0306060905010c230615091e1015050a0f030212061c08030901091221020a0c060903170105010507050703200a061106010b1809 67
    0x1c10151405c3d803a03043c89020050003c4070003021954420320074200440f440c1c8090303070300e00c3c00d0f00e0100800c52810200401022003849010705010007480b0800500c4942450210488420815100d440c0b0702c0404096850f0021544904050040e0350701e5152403400f468107602480074039803110451000d140d44051441c030042e0450742c6120321000000f0350080d02c2d400600600e41d4031340f81d00e51111580c030b1000d4922010b0310644410988100112690441c03445010b0350802c40503500c003100142040b8199106501343c40020f01f00b248007000304201007074150408002140700d4140e0310701c2a840340d00c080d00c0c117008030111181c60720030003c9902121401039002d0121714809140503e41c484442d11500226041a041540040c3c1590754a440755190085518014a802e2a000d8a08400390f15441e4481c5e1460100505102d140c1c00300070750344052001c00e420380260003416520003d42c2c0300f401912051034509042c65070b0103845d000080180b0001d00351000b450801d011f51420f0300288042090340c060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 997470908 1250 997469658 997469663
    0x81f080123011d01150c051e070e010e0a0b1302040b070c0905070206150a050d050d02060106050a0909050402060d0513030e0f010909050405070e1f050d020a06050a1707030902011b120507 82
    0x10346000400400c0d41040408c4c80d1481383c00c003c6d08030005105070103091040c0c4c2c1c5c00030782459111200410070030544e641c4542d0b001c050b220340096141500b200082011a03410030090185001103070100b02400340e07200400845105a8a40780502d6880c2c000e881581c8048030002e01680000380081c000700782500b80543c01c11002068181c80ca074640d000910f1404005400340e440e0307805081a00200d9804028960142032607081c01400c00300b44840041c03d80003103000c0d1400d240c0c0c0780c101140854503a90150b40c105401c440307050100e4070f41030070142500410698242c0c0004c0c0b281c2d0030f030451402d042e80c52140002040e5039200c649420512821701401014004a626200d404400182c1c3e1907001011800f4501d040c42c2108150f0030780f011156081a5034003d14420f10f0850290f500590700c40584500301d07803150910903180c03071026a040e40e04518036451481001150b208014240381d040d0304c00c240c407a00c00d80760007840c1140107018191140321490300070081d5282e140300400d41c0e4010300c00f910840d40f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 997472158 1250 997470908 997470917
    0x601051b1f05180604020f060c070f0b1908100e041104090308070905060405030d0807231306050903100b0409020303131d07081f080123011d0115 64
    0x15814540c41e07440390000101034040340e600c40501c00006180c40307804404008003002404581415000500c511001d9603025115250015580841d0f800900005005100055110303225550321201003016a020780c007001803983e0f944008503d002c1c001c040c11409102404e107080030082c28111800854400034100f940e291110102d401a65901c60150740c8810f4803e50310b2010a040c40800941441c030541c00040c82581301740024402030f10000741c0c036194006c1600d080c0401d40c4400200783c850241d070720301142c04807003ca07034580d40c507002c064002c00701505070403030b11841c0c0d03550b0720012105030065201056150f08a10708042c54256640c1101a2642000f0000a4270b6446580042c0c40c5500c1150698409030282404104401c49480711000310319a0003d140018904450020040311009008e500301039641c000a100b160b1011800301c0250043c000200025442d54400c2e43c80f004200f074008140c0000320001040120803904079580c204048040d0b00300e036900b0310300d0040800541c02424400c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 997473408 1250 997472158 997472173
    0xe010c06021602040506040b06030402130908040f0609050d0f060c0e180a0f090b131a0108011406011e0e1c0b190b010c0308100b0c01230601051b 64
    0x1403014402480400d804081000042c1841d1041c081a100010051403007940340c4030f0303e03181139101c22041300c0e80268100c894180700807a01e00b0b140010500000d0250888402050201d18070b400c0f400308406a035480d85890380d89564178000c0105494410780000c1034510500c15001c00101d203608001100503250400c5031456403a640826401c42d9505c440d119150958018801000030500c10520030300fa07481c0c41030041c1d40e015124580b5108015044202c5040780a288005000d14040f1107201901030301c0140c2c21a594982c2170703902030401c40389a649048001030210385c0c69805408201e45a000f844040c2250640201050340d114913920310044e00320305101c0080540608404518044622071940075a07141032030034580f001d81082c41d03c1541e4840c80e00074640c03442d80c3c00456071072110398589001c181960b140980302d805d48415500c80001004085215206510103400c0051444869034245645203080e02c034030302484000f501d949002c070b8400c00c1035039075901003101030710640c050442c120740c10f5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 997474658 1250 997473408 997473413
    0x10c0c02060a1103160309080c0f10030f02070807021e0a090c020a0606090c0818120901020307020901080c030d02060417090102070e2404290a08070f03020306100e0105010e010c 78
    0xa691105d60100d0404911000d4802055007041344540030f0305001008050079420040030981c1079480d0381c1c030648514800510407251512907040000c080001a40a6486400f1807800304595080001d08901c203524000010705a00e00c0c4607407140441800030300380803a00d85001e01107030041035650417480840c010519504003080709801540010f00740003000107201c80f40c0010090460038081e1450003140c030a0700d9488074145c00007031045044403c40308469503850240c40180e2171031040b604001c0d0402800000042c1d05d1801182c80d040710380701941a20790005034124102e880d4241141d00403c044c90b000303010381061800401801301c0703079010300489204d9602d91056180e402407c4a41001c3c6000c20b440a0401c1d401d203c039142550202500c040c41120880c0304103200c50040005030204440714140040440c1c2c1d1601550320040010307400380c1d41711a88404440c01c00c40024003090380a44a040042a0a8148140102c080314814070310f40c05541d00b000011130314480c514040c00c2c10440070290201c00f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 997475908 1250 997474658 997474663
    0x206041112060c0403050d0f050909061c0506100909030917070308070b0601120e030702040903030609020403050c102a0302071d040c0603110d0209030a05012408010c0c02060a11 78
    0x480f14800c1c065101e5285280403403418a00101076030030040040e280e20840d5030000155803000804a4403020b059659a0101c0c080c6112015005141d04026501074240400883c54a0041c820405060034040d11144041e0a83e85100b00040c0007815502042100244491046000a2424058480d420b6480d15580d0b0309800024041d5403c03203a0105100003981c01000014110aa01d0000d0000651021603031f0348038000d0b17501c080e01881e103d285050030140301e030744a040500b060704011500c2c1d40c4c481c145240d80342e00c01c08881d0701901003010b00b81d0b6400c1c060340000200340c4424400c400c400080303140150b0402840c4404405600c94140702141400d00d6074011010302040100301b408501c0c203820000704005a0794006402d1615084840800311b020750102c1e03400d00e03414031004da0345600c00804a40b51120441c8081c110754a803812519612540d030200504036a4105501444580ca9404013030803200040790020106071484c1e408001414039601900303800c00c06041100008000c0f480d6a030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 997477158 1250 997475908 997475911
    0x18020c070e0f0a230a05090a082709061f02160909050c100206131b03060b0910080705041e0627110d021e1215030c01020604111206 58
    0x140326110842000620040c0307119240e000d51440040c03400c096501d80e4100d02e0000f000e40317840d068070348803c000f42a04008001c0d925150383d01c130303c030700d0380d1000310201203440d102080601081c3c00107810545c200c0d1385405031145020f0f54000b006224184043d1070b1140c0c0c00788141d50550150b000d8480300900c0c0d000c07400031200051101c01d0010403819403901d0810304040e8894030140c401c4090703102c4d5185003640002c505a1102c240c01100786000006c0c140500756448080c42442d01e0038910001200b00500354218854040c02620290003540f202c00300a98038071401d00503080d241c0d000400c100550714141e0003103080e0002d081804103070040035045100c2a9041134024a1100c211021880d00030380c02d13418103a0340c0903d20541005018817105041d1110702c58402c1e04107807281c020031418042c090003104222444174504c0d00ca5a2503000345a00b03650382c070b8100e80d088003090303208a074101e4504010605425201050f8094482a81da40e0789040c0c010f803110310101d420103228000e42c6034200040101a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 997478408 1250 997477158 997477171
    0x1203050403170f010e01060c03080103060e15091608030403120f030e0a050a022b390518060102030a030f020408190b01090b092a0f130503060118020c070e 68
    0xc043c00d6040c03412904030102c041c0d00240400045e0000c0300c01196110310000d0640351301c40740100b00702d0b44221102d0f25000eaa0303481802e09401400600c101503c001469000e00301c803851300800156924411182c9030300480c40050010010200f078140300758458100a2460a168100014020a4042c805107000e50221003245c01ea40301c0d40a107002e614104980d60701801c40d0b03403403030107080414520704251030810000081c5540b80c0241100e448110449491141c911b444031100003101a910b0041c48003404c9115a84c041d08441092443d50364074912820712038101a0000d5140002c0d41c0c1c01140107210020070a045190b0034000443c500600f4014061141c07190340c10303444840c400d410000d02507001a400744a00c1c41c5003181401150f01c0703158031181e02c43c21801c1888007981c268031602d844540c5055038058080c5001440c084070035100409001c50034425072002e0a4079450320280b503034510013030064881000380308540f6403949000f81c00910844508005403401640e4410880c0c00716001515803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 997479658 1250 997478408 997478431
    0x60c0305060906120304090e01141f092c0c060a0e04110301030507050d0501090b011502061008190212070e180309090a0c02010b0306010803190309120305040317 71
    0x10300201e032400100b09504500200d4041403041081c02c0440e569201d40d110340322205481c1e40880c40c400d6029440003804501c280441c1d40c0518240c0c01c18414002200c0400001c031008030f07008140000d0501c140240c08c8081e240940f0b0901c1502c10f50324108110f19a202c0c22482103d1a581e0b168880c24003030300a6210035100c40040300380307001c100400c3d41c02054540c080404180010008642d00144003001c488041e01d400c401405141070213030140107445006032840301160b0000504684090001070441031580c01d9032069100e4410603c44032009101d5048036500000451050114610035003000a200900f01444501100380c41030408400750320010003d807004003004143e056030b11300c03414091400b0020310b1504981c0c00000c1c0005c41301a00d041890380ea203035940d507201750007544480c15081c0d006049444c1036944200b480da503588071a14000300b1103003d003182c85c2030354040e000c3c21000592000411110b01c92541d070880050600070410303010800d84507004240480480c0120380180a000346 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 997480908 1250 997479658 997479661
    0x402130c031a0102010b0303070b0403121104051002061b032e1d100311040e0a1101030f0606021e0c1002010608011b051602310e0309010921060c0305 66
    0xc1102c6914040026415641403810f078400f95500402118902c986c001503c585070388550504507150282500c08818030b618010a441d6100040720190007202e05c125000e00711511510401c9840301c3e000e0700c24002c6442045000b07000307041e149006d03541c440c114104080e00c01c605562042d0041d20442c010b811a4040100c0a0180c0300750000c454810003040c0e91030104600f0101020004010244005040040340030b0210066035101e40140d50030001d82802c0f40c1403006076061151404500f81d0a060100c4d291110300d960340580c40c05000b0454007140c028004200300c0040d012041d00c1c02010b450303070034001c401140340e82e80d1b2101580d1701040b0f200d80c000903180d0700303000711142190302120007814540e8040e401c146107140d10508841c0307600702044403240200b0052002c42c418080c2400c0994207d400b198010034031280e14500884001d1800078180540c1042110352038981c03089080560000f41842d405001c03031841512034000c03503950044900c02c22003860702e61340c04591101c41c541c00001d4481e070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 997482014 1106 997480908 997480931
    0x303160c021203030a060504061401050d0209030105160824011803020402031e060906181b030c120601020607020d030908090d110a12050d080402130c03 67
    0x205030205400c0c0d62070420f6120307081150405d00c013628110f80040e203860503024500403108000e5a02d2643c1c0e181d5401143d20303134820351b007440c5000d80800c50010940c03070910415104120440c4401000c54003244010f00495000d4200c0c0003040211059140384400b42241450b10482401c008a0003440a0340c00c00c841d5809078070103540a0b201104004003110030380d0301c0695449070b21074880e020350344500811144150994016411001a20860007008620388c61039802c030304010b5220440c0090742e904280f1b2940200c030b44112204010840d45155040329403d1a0440f5003400078028918000e18025900c0c25030048170020980ca6480c840107001240e41100c0030748401400c032507410039803414804021040741e41c0300740c001d03507a1500014001100800c0010100c0d40710024140703500348e20300110b42c191406801a0b80c8003141003483c2130810f03824230070712440c4482520041101507144 = true := by decide +kernel

theorem cover : BRFrame.Cov 997302158 997482014 := by
  have h0 := BRFrame.cov_init 997302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 997302158 ≤ n) (h2 : n < 997482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
