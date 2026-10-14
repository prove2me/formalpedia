-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0282
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:57:12.366554+00:00
-- url     : https://prove2.me/submissions/8cff6b3e-dd95-4149-9687-009d20ea4401

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 50539572 ≤ n < 50719428 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 50540822 1250 50539572 50539597
    0x708030c0d0e010216110406081009030203070606030303200315040b06130308130e060d0f05071a03061c050c04020a110304030807050d020a0c0513022503080106020c06 74
    0x80c0078810141207070010050941000e00031500d40d200760046010455480b902280d202042401400151070207105c0e00c02030358803d070700502403410005042c100500001c41c0075008c0d88424006080000c01c20f000d6407002e14800c1ea80403c5c507884000003003400e014500c4021400e520207004000c00454154003e0f21068411039002c560f40d240a00403803210b00c58420303001c140e45003150010061003841d40041c039110008c05142c0394502da450750000510001607442d113902c1080103810101194404045c410345500071000e0f02c00c415525614002c1c21710b41e5100d04080c56030040100442d80c80c010303410558122030400d40342c04070075a82d5681610740413800d0a1034480c1d076000c903540c2c0b0501d1003000704554007060481180c0d9101d40b0390600c416076401100c0708072180e104d00d58a070100d8601c0411454607041c1c3c0045030860003418041003201e00006d1400c0e5517682a424460400502c0a1510b20b003181032890a490040c5110341c20000c000d414141c11190541d803040b06250065200d00c0c0880d100042d030724 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 50542072 1250 50540822 50540827
    0x1050d120e060904050403030e0c0409030c0b040215120a0b010905010e010311090303040e0a0509071203050304051018060b061305151b030d230f06030715030b09010b0708030c 77
    0xc1c001a25400340028240d0000d207030004020030140c0541c01403000f143d0042c01c80780401e540c41c04000940d100c602c802000151440e24650008100c2d100440d0030500c000c240c1340041a245258624541210711041080030043c828000c0742c400780e1260906046080c81c00070941c504100002e844209c1e24568181055aa500a030b407541c200401aaa4803010040c1502d98440c0d65140d800311003082600c1c801c00709490300001c500e03c42000544641212101c1c00e034140c5d185450388040c1d032903800c0108152200d014100040250720705612136803128983c9003048030b91440007820a882110700c080784e00e40c001e443c02c1004181078403c800305d46084403c101c812441441c05a08002242e0140d03d03600c3d0510540c016402da01400c000c405065841c26040040056040b103582000820410051006090b205407010581c440205c0c010031b54040006421545959501d07030481c1845c0d09020500c0c00029543c144804940c0f4100340c2031070040c146015680d040a02070b846607803085c4400f919000c0f059030300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 50543322 1250 50542072 50542097
    0xe0708070903050601080c040b0d02010c0206030408070605040c1d07051c02070210050714060c070605090c03060a1a0102030301180c1b050a020a06020625141c0501050d12 75
    0x40c1c181c04042c5074090300765031440d40e45401c0750f41e44188005815106509040c01c840711030810000898546030140c0d80e8860500306078007841025480588152810b400412011022440034058240914070032041d07040441e1524000101d0940b8240e000700004000f0400d00412a50140540e80d2035030281c407616850126150310360707000b4894610000c3d0840302410200100c90740040107040c403903000300900c00480c8401000703203450712030445200d54074407402c1c8010302c0071a0f480e5012641c84606501102d0004120360002440c0c00350445422031001d8860039140c0740c3c0c0022200900e1400002c0c00114215410190510610b003822480041442d54468000040c00e1107442e013018003070200c00540d40940d429040c4241c85003106c0e04168000c0032295000140030f880010002c2c0301d03110342d8000389015254200b17406814007609182404100b14440420030b0001c8100007890f0084034150420b00c007594081e0b640040d108140c0c0301c44e2051004900c44000300310786500e0f440b118803c44ca809800e4858 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 50544572 1250 50543322 50543327
    0x40303080a022a01061a0408010e0a050607080a06080307061a03070b03181c0302041a0405010c021003020c030d06050a08030f040b0306010306090f020705010609021806090d020612011802040e070807 87
    0xb002c1e4002e10f070300d915080a0040b11540c00380280243c48011000780f0800e1012040cac00c1c3c0d1101c0038036005003990b21a0340010f24251144014030741050030302101107a115907800899266401102080e50103a5031003100104d0180e040c0d10080c500c190680c09412114500b84505c42240401005402140841c0c0d100c40124442840010301c0030b020100c0340480d4082c084c0c8002c00039006406081a0074618039541e4449202e88000e507821900c2c142e58070743d0000b64907800d0084c0c03808000200406d00d902400101c0c410b100a0002c1c00681c0101140020000d1400b01080100140d60780499002d40040001081c0c80c00800d04036801c2d11944450300c5c1d42d030740300c0b600100c000305001c0c2c0c8942505890400b4100641c0340d180c00900313a550158000380126504c0340300c0442284100849000d400654201030241e6080c1880500502a4014805c842803481c81c1c0119032680e00030071180c100e5410240c010b1001100302e8500c4160809040011400c0c6070601e010748a000602815410510070b007800050b84261 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 50545822 1250 50544572 50544581
    0x180b040c0f03050a06050a0b061c0b0913020f060306010e101b060903030e0c0a050d03020a081201051f0c020f0d0f030e030712050d0302070c080105010b040303080a022a01 75
    0x40740c0520360030075940d040203516508804012030701c490a0401054001d09180034030070b01e2400090095142020703c801c1c00101034200708031480c0386501c50b201171905688a60349030b481000540440214400b080c41001041b200c00c00f07110f4071802d814418840f05da64441c09844102c80155409103808884036000c3d203e44480301c48098401c004a140f010401801d50042c40c0800c1c46620b003030080b5075960700c507640c4400e00031000070740284506c2410421380c83c141c01c82c03811690107401611070b03107441c9450300c020f01e500901c0c5002204544a00404ca02c0c01d00002d04085031901000d5810a000f815800800319071000384068801c02c0812418461981d840d000c000b2007542c40300d130712981074165180c0686030f84401112079229008400300020b2800001e40700706040c0d0b0b40a405482d003000461802e074025004070800303584c00c800c0c00001040265017403188901801514034525266803841ca0010100d0200a11009a00d40103101d841c5ca54581e1600214030305040c4903c038040d5540d0079000302e0040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 50547072 1250 50545822 50545829
    0x80409050406090c06030e0c09181608060601050a08040b06010509030615040606090e0c0c030c0706020616091409040204020904020d090b070819020c0705090703020913180b040c 78
    0x6614040501c030802046510803608a489940d0b144081a034884081c0c04980700d00c0d441c4503d94212410301c08940c40c0185940341d00c520a11501d000d03200d0000d405a01d0300342090b100d0811041c944c03605000d60f507401c03c982a40080c00346811480e00000340720040410a005d00700800b03843d14100030800c40c1c1e0058043e55038082c0b0140480314140360030414245002c25000b0703540e00640c41c1c41c80100b0306601c40d01d40001594060710768900303142c8844000300810303408100e402c4a640010711100c940740308103101c0b000051450740d00511050030001104005154404854401c1c03010810082007050303090001941c3d91402158000c03200e540e01c1c000300300030703210302c10384540d2043c070000b980301c07401440394031900c034050059000103000e07694200b041c1e400f4039003a5502013181042d01250440440180c000b049a044c18109541c94580c0d10000b0a0b441042520034002203900410b018016082070301102c601010840d1703043c8050900203804059901440d60040d121608090004040c850740d03042c0308008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 50548322 1250 50547072 50547089
    0x4230d150504060b0f1011120403030503100b0703140a0909020d09050f010b0108160c020d03031b09030c1e0308070b01060807110619140703050604060f030c0902070804 74
    0x211110100c00c0c000d000844040710442e140c84d00c0032030142403d460220512001428010101c440a00191420f512020703489180380b041d0028500c0c04000c03580a04020740c42a124141c07282425031500503441e80e640c10118840d003042c01305d00042135200d4404a6a20925602141d4422400000b1900340f10302d9040154803d000160f81555040d041d441429058003800542d49910415040c031400c2e20190205d072400070303c4070000318084100c1c5550b8904250000c0c14201e60040c1ca5902007104204102c0c4180c0200e03a0b50520310f0302c0316011441c805071000721482c0c01118141160b44258000c00140211512800d02d0a00c00c5802c04583c00210042c60700050f00035110032061038407078204c0c00240035040004d4095404038103010300450381c2050341d921309409408030307070344000b039403031200c8121255054016298841201246038404429002d0301c01d9943c01b0403503103400020b12056079015409210342041407041003002c241c5501c078070380030744200e9040582d560711181805d10190040d5000b80e440e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 50549572 1250 50548322 50548343
    0x703020c0d09090f02130905101502060109060b03040c0e0a0207050102070b01080d18030210030b04020a020d020607050c060f04030c0b0709050406050a030816050316050c041104230d 80
    0x103600c0c1c005500400702ca010f80d01c01c2c080644051942000e0380901507464040d151020420f1080b0b403038a40107103034805ca0101c030580702c50360b40361014030360b42c3c0e8401844005600074900500c080302c59806804058820000070500e141000e030740341304801c0490700c41c42c4500c2071090041054603030b07d501254041e07a0000002c0d900c80320b103810499070503c400e1003904624031079465608a900c0c01509250a603648121050450910395000c1c40340103000c103c42c0c00105175031880414580d50703d500c09401c01c0030485d0b00a0142c0c030341920703000c0c0c42c011010300700380309124060080300e41c0c03400001503060b031080041441ea10251954074059440401c1c2c090018180346070a000c0110143e4800c2084048500464084c40f040d5038450034070245080c24000074190910800008800490104601141c03a00c80c9045a10701150604c00202802842e6011500c94106a224031002c0c40c281c05035507003a40c0322640c00351a00e440e010002c0b10000c81c102580e000c040403000c2d82d04650b40e0304807070705444e203421a00b9031380f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 50550822 1250 50549572 50549593
    0xd060b06070515010e0c041a07080706020a0e0108090d1103041d07030609140a0504030e041a0f0306070f0f0c06050c0304060c0306150e060d0903020c1008100e0703020c 74
    0x80d10f07544641c240301d450710115000080d01ea00003583c141e00821026171a9032030203081c008006455128841c02154480082003480005a007400080c0940ac0c05000c0041c1c80364443ca8000f400d41188081e01ca0400810206001c40038401045440600c03501c4c3c240208542c081e64001800c40c02030350f10400c00c0344001c0c51012100398078622072520952140c0d80400c8035030f03190a081400c40f6100c104d009003101c140000145640210350001e900036010341050001d210b407801c002403d448000541c1c0b45e864031a40d09035000d03404d00d40c00701c21485004030050b040f82c2c81d2095000b4603c1c03120500c1c0313100300a0700a400240d110700403100c3d6981e09402c0030081c0304620f000c40080d4a43d51040d01c0841c1c1e403a29048851500340e1003481103100b511102c9024a00b0030041441c100c41004082d004c2c182e1010040015981c500f01034458030003020b201e80c0140c580c00e500b4404100050340d0346035000c01404012030811400360320f000c1c414415505141c4103c0710544a00d90218000c1c052014020124401c196074130 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 50552072 1250 50550822 50550833
    0x1091401020f01020c010e070806010b0f091903061a01080903070201030203280b01080c0a02060606090102011104030c0509090f030307120902040903020a17090d060209040b0d031e030605030c0d060b0607 89
    0xa007c4c01800803500c041d90b0711400359503140024801c09900450030b1100845250b0f80380c0041c40c41e01e800520845400b00e0b0310b000008203403c2584111034056940115045002001208611051090902c10b078a031070460b07031440c0c5030300c200c80d0020304041d8008006a8bd29540c000741c41014894120401c500c0c140e001200301c0107019490000b070108a2090003c0d1200c002c50080300d4440c001e0f1b602810103a03c407202030007442d41000e00d15606554071030300088100d045100c0034000460082801190030352a1030288540607501030407950598201c41c07114065070b000003007225008813540c9060368a5440302128030703004156281c0003d60160a0904a170107040d80010744004403405004a03020401002030081214400c20f00c605410200420102700410000d034084c0023000310242000c0f030a2082e40b40051071076407090100301e0102d80720a00100402c1d03030f00801090360240760f00701003000d40e00b0000082c0d5901c003008165441101d004040000300606504540c01005028004603110507051818 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 50553322 1250 50552072 50552081
    0x2030f13060e0d050c040c0504090e010f0606020d0f050d1107060903080a050603070308090d0c06050406030605040203060a030b061504090e0c0910030201050a0e090a0204090b0f01091401020f01020c01 88
    0x7040700041c5103030340003505890004204030049501c1002084207519010510000c1e00922500000340302d428080010f91003018014180d06150070710000691001b101006400c07640a90004811507000c0483c5405298014001d06040344603420b051380c940703841c5124031000e440c8044804000040106000b006c0ac00c02d608a080024403944400c0c185903100703601c10003225400c90306154164041c0d4006c0010541603070051404a801500344c070f440c1c003415140d80c0255120b541c400e00005200040412a40368140b00303820291004403000d514508101000845510f014000907003801c24400204000759103034020640345440140b02203440b690f886034010020004000d0307071005401102c0e0048100c1c80c0224a00e482095900e0300c1c3c0c00c2c03c034196001145c80d0340004030f400080c0581810703400d038140d4460004030301c207045140c2c01595880c10101d1480556444000d01c90140401d4141c0c048640e81002c414419034400782d80b0641011000f900403450555668101c50079540b000a00d2021214107402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 50554572 1250 50553322 50553329
    0x902030703050708040b0106050d110301080a0b09010908040e060409020a0905150420070305040317070201110312060f030111070b0a06051e01050a090302130e120403020303120702030f13 82
    0x1010055540c9256044d215210211001072140c0744030b40052207101e004101814420650a00001d8101c1d48a409103d02d40d10a820000095000107481c0040259010701c141d480081d010090003142240da50340050380c0980d00074120900706150000e507503920380340e00800510b50020028510907580b1300107000200320688065402c580764500e03c0c0503d05241c00783c010395101c0440303809091219104c00c00340d03d030010501281000780030800003001c95041c01d40720807014004594075541710b07482d1001520780c55a6a90114481c1c2080c0319040c01900718500c0550b10a0003602d0284201100f080000d0042044000c0c1c0d8142071408250700080c8004069074502c0358903805d004020882d00c1c1d800708411041c0545004000744200c0b80c00400c90352080c03020b01440c028600f044c0c110070781c07660300080c0000c1d030040c801026640e5920401c004048204803076031604c070816051034501810b41c0c001c02d403a48140140e600d01c00d50501c02180364244200101c6086111241c1074a48490039250300d9541442a80b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 50555822 1250 50554572 50554577
    0x1020703110601080a030504030803040201050c030406170f090a0308060a080f0102040317040302090c07020a090903031406010906050702010503090312070c0312060f090504060b040c020a0b0c090d03210609020307 93
    0x40040b4411300c0c00a038651700c003038054544500b40743c03941c0c3c0c1e08182680f0052040b03042040600800c04440020006003000e03201c59125030280912038241442e031210002d0a0006190007c01406030ba544081180c5044a03054505002159101804118010340039400b90819118042c40580703401c0c010f501400540c1e1059240c0f000b0030008940c0c0b10158003680c00080d5000b2054000b2400d509080e00041496a2018001007202d6541750b40c02411510369400030360121f2f890314600960881c14030b2045501010900f06403200f1170400c9002400e500454100034140040007011400c85041042070b2a010407030000b20501030b2400b07546c010070200c0d4442c000c60100d050303454046141c10b81400341009480840ba464501c130f51038100703400040c0c003002d40250751459407245211003030348cc1c5000f020214655500103000d500020b00c1c001480080c010056068440c0c02c1c00443c42c1c1c1d6507030803413000741250903123407010003681841b00340d40d00c902c0c0340c20080e16843e1600308000f0b60f880301d54019610408994 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 50557072 1250 50555822 50555833
    0xb01180e07151e05030126030a080703051008030d020a091205030702120102090303030c070609020307090501080c0919240306140a0c09030314040e1005030601150e0f010e030102070311 81
    0x1c0c449840460300d02c2e10781e50128905000500c1075105076030001e0141f211029155111844440590f41144e0142c001000021030003400c1064040d0140141504a0f00d40c5a4406100f450284400d49a008010034003000d650005101030b442c610465091024020740072420303200b030340907280c4150349901c1f046040b4003914a03d450040e207440184240d81024401502840c0781d947d80c165a804280d20080f4203d9055550700030300d1000d40c40800044010307200e615000101c5505100c45586490758444000d0710480000080280030b4100310f041494890280350701090030104150005d030b00380c801c46100303500407088450010910840f038100782c11000240392905082e4851810210a0b52482c000d20004030700e1030001000080d104c1c804045181e1440315203503040c552131300f03030917081c4407000c2d1588148403ca02030240100d207824441c0c1401030030101203034003540f0075140300905280070710301040348038000100d6040200c0e4018a0044031684c0024000c5558000c20301e0081c0100c502d4020a141c944501d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 50558322 1250 50557072 50557097
    0x204050301150812030a02040b030a060f0906050303160512070305090f040c08240301020406020a02040b0103151e0308030f0708070219082a030307080f040b01180e0715 74
    0x1c072141c00343c07225180506240f4282014042c11a800545800ca409908000c00100c0c40180b00145015115510300400d1442ca01803000c10100031310f81028861030704d4000d08114642d8004100c1d0400d80b204410401c030301e000d50501c80c0c285495441406104c001c009080710805900600900924008072010000da1141c08280011600110190b1005c10046800b003505103001c4110300182443e1008a0429030124901207030981e00154400c81c0036a0080a11208500c2c3c24041c050405400b807078208103504102464a01d0303075200748141040290000071010143d0790807483c0501442c8c100c5502d075139a0404602c12000e45004680b00b40000c3c4403540410b452910102c1c64020b031039410381d11a00c98015540703504401d44c0c4001001e410641405c100b014544040c52440d619015070b00d00a9074407407600c1d0401034108032004004c5004041c00408000000708944005415a06510124214406a03542100040c0080c0d83c0380c181a10940000290400d80100e24a450081030380c3d40b41d812065 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 50559572 1250 50558322 50558351
    0x30c0b04030c060302030a290901090b0109120804050a06050306100201140c090307050d060203040b090102040b12131502040f09090506060f13050702010501061d01020a080d06030212010204050301 86
    0x66001c01042d05072204010032189102e07402440c3c002e1100900020785014030007040002030800034401305c00f90486c0c0e00c00100d0745030030009140107210040f000c0c00004c81c020300081500c00c43d801401d84a20b000c000c0001401500320a540103443d0203007010a980f03441d080043e025810032a40030b407186903103812440c005841070040018800b28142c0d1121540c4031a01d1484c0f680d004000d10a40521941800107813503610005107488040c0107200041e52820507003051600c2c4440107100001036030042100b042943c6072602213401d1301a01c0c4604010680b119021007094080184002c0c200b0841039601d02c2010290361f000b00104d48403244450152651520403c05855540101500582000001415a0400514105070210014180d81901d40703900825812143e00381e44480042c0c1d9240014401c0603004041d01d9045045000c0a40840c030000303000035580c107030f0341d40014070b01000410300c0e01d2119095080b04010f564010000345c591140146121b000350014400c0f81e1280d8200020092841d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 50560822 1250 50559572 50559577
    0x50102032503090b0c0f2b060509010f03121101021305040e1612050a150b03060105060319110f0d1e0e0307030309030203091003050915101e05040501030309030c0b 72
    0x354424403000322540d071144130780c1171600240000050300c001000f4010803107408408544030000e40303065014410200100040031a8040e40045028196010041c4a60b4840d01c0c0c0c0c100440381c2c0284104000104801c0c100c40c9055000140d066540c000f03c0c03035180f034221400c502400d5410903181044070f0a000d481480d80d612800040140300c0d804000c0901c6060b10300d540701800c03540030303c080f1071000c015030740e0f418109503030140b6035100d0303564403142040141741c20700c982801803004a0740c460460501034007194400b120405407046066a0b1540040c035107030302c50182c0340b200c890325208581340d000500601000d49001c0201000301e180d44a08461038540ca4440c410032094440019030814003a650154001d289204095066203c14130120b459a914440c01e0000c2d40304a07a00030403c0c2c207248205a180183b4031300100e00c0d4840071010805002c070b81000c548121400c015802803040121943d08a80006540102d41c202d0704000000c000d241c3c0008c000350440344240b03035469440355a210b502c141070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 50562072 1250 50560822 50560841
    0x9200108091b0621010e0a0f05070e09040f080426060103030207030308100b0706090b090604020603060d03050705070b1b16060807120c0819020405090402010c030c050102032503 78
    0x25003415504181c42c3c103056000d07180040102c0040780e05443e030b42c6401c0100601c00d903c00b01d8083c0c01802000307014910741c06644495080d010050102c0d040c5907c014025160300d403003641c000c441c40e600040c1400320b400020b404050b000741a0030b582d1511032140c034118100300100d280c82402c0341d551242074000300080d4a8101d94141d406040d0041c00c41e603040712410009001400d02c070702c01840c0410b1102c0604010029075118810005091b11149401c00c00104010300b10202c5822400c20032001d82ca900c000c59512142c02c03201441400d80d140344c20780d400d0007a601c01800d107200740e03c3c2c0400c9480b4800000c050f00380c00c44564105409201c0081d6a6940085800c0100003264100401049001f90305007a000080303801c003415042c0c0303010fa042080710f000c00650341c0060141000d1144480e800c11041c240884d080205519240c01c20004c01c0320702e50b020f440241080700407880391050612880c41007030120741c0300000b9035603414265400c002020246000380240100b140c4000401406885000c040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 50563322 1250 50562072 50562103
    0x9010b0d0210051c0c0f030605010c2102010f0e060915070f05030a1e090b060114090d020f03070f152f01110a0207030b01090603080403080307030920010809 69
    0x40310b480d000443d0290404041c003100d0703400d84440c400340803446000706803110055135100950800c52007401002d5075107590145e4148003882c456100070519079441480004002c0c603c41e00c0d101d50f41a000c80c0103265000c2d8941210389044809152001d010400c40d0007400502d00b240c100d440c1c50000c85644201c2030390070b5400315040c0340d03e00c1221070240001c1c560100344e22100141d160400c01082c8805180c803250503403407994402c10f400c20071200180b40c580040702880c0510806400111a903640c1c4542d012140c031031000003402404565030000b6039061840c01030203039120503a84080400800c00f05001d400d180103903101d100a5003601c64002d1207140368040d0b1040c41c904010f8007081003040204151181d0079500d82c610b142c0f01c0c2c1d1b19000200f801803036039030080c41c2c0c81b4918204170714481d006030000c200792410042c0800104407000280ca041d070390449a025660b80382d034003054004101d0400014803c844403091041c1e85245008100700403030007a00c0d80b135150703a1600720311074680c881c100f600301d40e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 50564572 1250 50563322 50563339
    0x10506070f170c010203180606010c020f0301060b1605010507020606010c030c050f1213090207080304080f090307060e0405060103150605070602040314010b150304050c0f061201030b09010b0d02 85
    0x215120311440400107000d400107400d0000102d8800b80d41da400340c168a40300c0d030f40000500804042c03182c151000e90440c0b502500890904400007021034003190000f03440b41604004944103a0303000c0d807045000b40205950156100300844c0c1d0861080e0980605407065441c2c40c002030f001500108400744940760595810102c0d5030590783c10f071b801c068095025034071840b40f00904a81600704000403085101d00c408125140c204201c1c066400e004244c00c01c41d02ca50061010000056801065a0b086540242d500742c50761220038400752140140d0381e00c0c1750f151145210000d002030b0050094500c910003a18148074a80d80c400c015401e032008846444640b4055420400005120780040c00700e05129040252070700d540ca07155604841c4825440d0740d1240d640384091440740c41d10514400d203030244090300d141149400d8507019103650340301039814007800405c00c80764015912002125003940d80d0300d404c105256180e090000700c12030704842e0035200d90f180203107007400e511385041190243c5600500303100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 50565822 1250 50564572 50564587
    0x5011d07020d0e060a021c0302090a060207050d060509030c030a0806151602010806181806012408130204050910060902090f0409030905090c070201140a1209050708030a08040b06030303010506 84
    0x4c00d07a214a4060b000c6000c0c1c40340400c2c5080c0c05040d0184070070040c4d900541c48042500412030720720550361290080d0341c04910b0801858031200249042c0340c0d0003a50000380c0790354200d04d035800c500c2a1400100d49020028981d0030051f00440c403207000e0070701690103010342d1000c21412107052107103240440c00038818102107001503201d54000c0d0b0f031180000d448414800c907007580313040d5140340c20350380718030005c0c1440da1000040c1c004004a5005041440e0b44803426407440d810201040c0000c45400d040041607000188240340c29282804402d80c042c00c200101d180c100d820544511910002c4040241403020010760007c260003a00c500400041690789850b030710804000003800ca1402c00c409124480c000003440e6603840d100148118010311000e541c032084c901c0014550155901d84046c1c070f90052000712400c1d03074401d2614003005905c074400101354074182807007442c0403269800501d0341e101c0000d072441c00fa58410340e994011481090a14401d0711103404041e201d01090003550f811078024018030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 50567072 1250 50565822 50565829
    0x6070e060306010e10020c040213050f0102010b13091a07050d052d04020d0501020304050604030e0d0b01030f06110a200604050307020d080903060f091b0102060c130905011d07020d0e 80
    0xc0d17450101401242d000c02e440401050a03604005030400c1d142d08041d004000078140503d00d25611902403008111422000000590b021440ca110100781c5a0303c1405504001985000e000c12440c2603110045034a440302d0014000d034002d0031041100c1c1d08003004207000d41c000403a000c0761026600c04c041d40e054070700540b0003d040c00c02041070b60b01c0020550301a010400070700c002d60041c1d01035009810686410b08000d004080e8101c5124054401116030002151000b50460f06681d0b21210007050340b406802c2c0f50300909407000f50304400c04000690541c949822034205c0030211104001842240414440261200002ca5016005070003c00c040c1c8011b28201e0980008180700e80b10042c103040101001c00d150500c05c49001703000310030000c03d100610030200403900306010418119400c40684000003500c40b0b00160a82002a2000c81e01701402002036610070041c2804400400c16980d5422440c401c421040d40e00030800c06084010800142c808204180c082c68980c44854040a1640a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 50568322 1250 50567072 50567089
    0x80402091801060902040b0306180f0f0403020c0a0e0106120219030e031e040e090609070e0703060909080d05090312010506070305070f060905240f0702010605090906070e060306010e 80
    0x62603555543d4450206942d10f052003d0006441b0016003a031b101c1c40d0101c03c0c441c3d611464244013848803031010410425447d007000700780d4002c0d62042e4080700c584462405030b00c0c00740004601603001104c0c0f176000c2036507116030003c0350480d0001c0c0c2d02e000d0a04100307074040e0100d12030203094141101404002000e440d000b500f01c404d58074806003c03680380c20122180700c4140d5011034460222400001002c001c1c001e0603405c15500800130320050702c02401c7c01a402540c0e030b001d51090f008150740d22030005907403074003c0d448000200460202488440141e2030031101c99403000c0c0710703550210300d0080031442d4082e0002c1541d5491100c4045031400b41d0815003002183d8000c01c07021010400704001d00c0000030451071451558034820b60000c83d031407185150450a066001c1302e401d186171070410241841d4500b06034203d4105408900c00e52498031050822405025140c004581145640090042480d0005100c0340b0030803141d41e500104880c1402000114801524140e000440c4c8494030540c600c0c01484 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 50569572 1250 50568322 50568361
    0x30c15041703120703060503010b120c13020409060609081510030b0c040b0a020604050d0e0102030901180e0903130e0103030c24180201090803092d03100b01020d08040209 75
    0x490381031003030100d404441c3d82d0b000c4514900080d111720040006040c24065901c42080440704003601400c0c11402c01da4035401d80c011244030700d0040f00070070784c200215411a400b070140c881c0c0c00d110300c68030b40f000504440003c2c890130601d44101401202c050f003842c62000d010f201c1503a40100c0c4549161034112247e80003600104461208010000c0c620000c00028001045140c02620030b0340340c981400c81c1000c020891000501c460b00b05c00e042e4903a404400c84000100034203160103d4220710b001e0340304c0c42481d9004401e0303100c4034406001c2c1801d0000301810f11152680038401080d503c0c1c88031611000001e100040202e040360102400054002c3c1480188604500e448101001e1000c06001900c0d003c006c1381c01c100c40c1603034034002556400100c1c50042d111031401140307801054000b20381e84002a107034032440040ca82690441c943c0f085812801c3c210f000074100c8620000701220340b0010f1030742c200080c1c054811b820108030380d140074120b82c500c0f407034008080c0b80341680c0c0d50880d80c500340381621 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 50570822 1250 50569572 50569619
    0x5030307230303010306061d0709060f030e01090606051c020303120703020c07060503060a061106040305070f051005150409030f0509150d0501060305060109030503091e1e030c1504 79
    0x8240c2030745103404002031070003907018120104100745010f10788203035002a000d0111505c00c00108200311181c20072610801c84060b85401d204014600004500030495440100442c1d4244040d600030702040d5042a01695401c079200304081840e400b0b801116032200d00300035016082441400460251401c80703951000c0b0350309016181c40403883c180c50404400781c001c400401c4010080c0f2100d81403400c07800c40541014208039105040407080300b0b5035070710001c100400700540043c1c481e0030445441856415180d209044a4401d01c22100e00b4024140490f9101200c45d0603544032039040c03070302e40184030f0113035019103e10101000300c038011502c65021016443e0880400c841403240404400c0051001c900d03810f200041c95410b01c0001419210301422182c1005126401070011a10101c1290b00100007102d8070983c8903120303c0300d26404840c3c19a05980070001ca900d074000b0700034144410462207412401e542c0e201000c4000c2110040108a418031520001d2209014080c00c0f090041c08084411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 50572072 1250 50570822 50570873
    0xd02032502010908030a020709150e060d2f01021009020612151519090509070c03020709050108010c08060102070609092a180e0f0a02090a0306021b0c090105030307 72
    0x12132205103140c6c040c407130b8000140c1c030584080040b00380314030a80303640c3c0c5059480042018600901404ea4240140c80d2900c9541065145e10070010021041c0660701034140081400b00c50040b000418007a031011711a000d130040c045214210001846900001540104100e00304400307091000d103e0000102003010b2082c40200300b00c60380d80c1d4040010741c400b4030140e4807a51009030144043c0c442d00610041c006102c1220350912140d6544030700d16034006000d251016610102d414101d01d0140b090780500c00c4146003030004107544034190091850142d841e1103140072615440012070b621450340c031401000450104c02800a20200d421402c6904000b03118540380c01c9801088011102100c900780010848103000c0d480b014800c12180002049100c0d1519040c1c40d00f0b43c0880200d000081507041c5540c3d000400340b005544400414010f190009021074403514031020a00311038000d105030030b144d88501901008249400507849042e250054081c44c1007134813030707030b00c0d82941804c0f0809048040001e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 50573322 1250 50572072 50572079
    0x8070e010c0212010204030303150b0405011407020a12051b03060a021605010f051006110a06090201111509011107050a0609050307240606030c020606090601140f09030d020325020109 80
    0xc280b0380c3c09207201d8200006130b481d8514076000d803c44040c00c84108000341202001c101c0025000103403821070b01c0c20708115245004e03030704d001c0d00700d845600c200961156102c0700200d81690900011000741c0e108501300c940d002c0314440e02e0001c2d40107620600c1c3d0b05500c114006124050180c010703207a00000342100c600310040d0f65482d0303030030b49142440e054556542d800800c070900318808144001444c56040050080001307107400c6456030384256024120a0312440c580d000c46e441030003602344a1141030152401c200390031421a001c8030b000d840c03002c0d4560034000504d00b035504080407101c8281d4444001c00218105a8440010f041030000503201b1b0300040c081c40380071031090084a0f281c5c4100d0900c0449804484524100701d0b1815008201003503c0d0424180701141c0011b80c103500040300f204c4201c20741c0d44d4240100d0744103c010014001c02c14010586848e4080104c0103040c14030070031800d540300040748003405c9039240582c10307030107108c03c0046c018848481e6183d8036110310a4010316112240949 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 50574572 1250 50573322 50573329
    0xf12021e0a031404350a05060405010c02120403020405090304081006050a0e040f1b1205030322030f2307080706060b0313060203090c030706020a150204030308070e010c02 75
    0x1112445507401040e00c400030554020f00c22400e41030065601800c4c5414100d1000380c9660700000316030704102901c440841120182a10f503c0d00b010101190402c003520302d44281c8400003502d0448440d802d00c4041e012007800800d2801443c400300c0e581c1402d10f80b443d000c00c40944005895038105000800000c601c02c041032000480c01c1451035400305040346003105000c09660350350301c0500c04054800030b01c00018800907070340d40100e40140c00d10710300c101c4000c80101d2035030b01c0360301541c103081c0342c6400f0604004c0088040c5d8850303440c0d9400a01030100d02640101486440f0000400056810900d0700c0e046000f04083d51481c3c02081c1c81401e0780c3c07041001c0e19040c0e8482c04013610300c0329000c543d14081117814000e58024000003624030f8154201200300c48400c1c404217400520744e5801100007240003c0c00c00c1007000c0d0320001001c0b501111780d520406516140841c00658501c00807420070014840940211412243d00d5503810310315076a080c0b411250a00d501c00440c4c1045603030b4006401594 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 50575822 1250 50574572 50574613
    0xa0e010c060f0501060c150506060415030f020a090503010e061e09010905030f040905130201120f0f09080a09060203070809100c050f0d09080c060706110408030c0c010807020105040f1202 82
    0x120b03841c1c03c90540c106e03092800600000b0b00c0003902d91828081007024588a401c2a0340445080c20100c1060f0f44d50450154040d26035001031001caa4030202d20001100c0d84014800101c502c150020040955400031143d203a180c00c503410150a110320540240744c404080c40e141e444100040005003003181030b0781d22429030348048184601c850340407070f050041540134482c0c00d8100c410304580103402e0145a0000c1d2403540b81500c0600740a5648400d00a04400d58128403040c10b050a81001055104e280003034103500f002101500061600780b011580900000495280c1c603040040c690a0200c401f0070400000344507140541004440c28181c4001707682040014240710100e0058400c0181841e00106400e466500400c0a82c2c0110641000c9884030021508050f4100802040300400c0358104140e9100c1c0d64000401480001100d80c401d4001048108496001766140710701a2900c800890a0740c0342a40e020300150180b410440010b080340d491080706490300d0040d0758001000030282607814 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 50577072 1250 50575822 50575829
    0x30b0103030509030f03070f1103150604020c150c0a0f090605030606090d08031603150f21050a060506010f090e0a0e0c030a030306050f040509060a09170d020901030e01020a0e010c060f0501 83
    0x604848d60341c081013a0401103200941041e4024200c0f629030841581030750f003014110501a980c00111004451000e015a00c0d07061404005c2d0f90039400c14504144045d4040b1054a001540000c484c90300701c1d02c04c800c0907044a150b5900c60f07056880e940e0400030140d00800e80641c2c070180b141c03161000640d0300c0014602c110f2030b001e01c140c4800710b4141c000e400ea80e0702003440700010f64001c00a02221390950034080a0b43c9641000c6108c034405c0e540820440075100c14058403900c40c0c011100300700503150308207e11560b001c0c3d030b60344959240403609582c0e0035005d00802d09044080380002e8225100b642c082d004401240c0d08650025102da00402d080400b6078909800081c0c0303c07081400315050640c030b0742d6145c0f441910200118903080c102036407504405840c80c122a6285e41200d81400410403e0802d00c01c1c4101000350342d040090302d524000d520218000f808a820030403c20b0b191003041c82900c01d03074441901c491110100b02ea00440c0d20341315000c0101c41c4550742e07094032802445d0341c0c0300c0c0714042e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 50578322 1250 50577072 50577083
    0xf0a0c0e09070509120f030f0306040e0313030507060f0507030806030c12010902030c15030615040302041d010518030a031e0203090109020306130c0302010825020d09050a030b0103030509030f0307 86
    0x12049608180605d25030101094001030b8418220032000d00c0c400011168598946100f660b102c2c0c03120b00008010b440c0440e0b07848298800410b00c0d24680000b090360604980c842c0b811034a40c40d0351000142d07298403074441e422022802c18004040841d004000da5584102c004081d05c100c04415000503001480342000220079a5644069904600f01082440c203e404102c3d40d000c9412904805241a07200091003a400303501c0349000c0000c038503003050654001c1c0d89c1c010007e204c901200856842800355034522010709600b4400841d041c0c090104d20742440302240c0c0c0c0038500e0400c40c40015006440755107042c440c1d580c0401428100c060070f0380301841c01000707000000306544450340101890000058400d50001d05200032103800902c2908055003106d90a007030804091f5a80c50b0410801c01c4044450005585626842c540007036001c40c50783d030719507001c1d2142c10b6031940310030a001003983c20780030040c08120810014004680160f01421100f0402000c0307070408080150b9030b5081d034000c0c41040300d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 50579572 1250 50578322 50578327
    0x60e120c07090513080a0903150b090105010c03090e0c070203071404060e10060c031106040b06010206130803060603060424050108010e04050a2a06050d0c03050f0a0c0e090705 77
    0x35a0342440444000d1500c18424461410300c2c00d0a0703106440941da00030034071100012030500350341c0a0b01c045402190045540168015060102d00c0900780b0302c1c02d0180304014400020450350700401d0b4080445ea00343d96002c1c251400e010303046604a50161124030704500030b201c440010b81e0b0400041d0068104149034445401000c0284410740e9802d4003e113190105500400661205070409001113490a180140900c60a410140d900000206000c4141e0141c00e04001c10720030240d080c40e00a26080c0c4c02c40d14070750b40e00c45110382038401c05070004115100402c00702d01d0515040c405181c01c082c0041000440304201e081207030000105244852254031921401c1007075607003000d81c00c2d00401511207402c2a5141070b58410b62285c0c000b8070014080488546031030089040c0d42e81488000c6060707500780c01c003070b521800d000e0616000b114001d01454141484c500c2428881e001b014010440000f10001ca0780b20a81c449020742440c480000400c00c4d01c24034024144c0e21029141c0c002c41d9140c03940da6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 50580822 1250 50579572 50579587
    0x8091c03182006160303090c0f080d0e040c0504090e0717060108010e010b0d03081b03011403061003020306040803131703090c0307060e061b01020301240f0801060309060e12 76
    0x4802d40c081040c9072003404180034520400656030041400c050345460000fa42030b6041c60181c0f602c0c500e40e00105044011103002003408000020220302c840ca132034071864641c02140d8100f00588080414100c0040c000b80000c1002207281e070814406240c42c401500c400e1519028451030580020b124100d560f0300c82001080780f13500070721890030ba50b8405c0340288840c80891011a02c0440c03c404000d04000c001c0d000158592008451404500c0720500c020f51b036541e4511400e0024408170070b00e03034464001d900100750350440c00b5094400302c07940a00901110758071030301c800d811030b00018400c441c0c2e540c20302081c9000031100982138040381103052055499041a8402c580307401841002c01d8081d46c410007040c418a50858812074a010b13088540c290340300c900c09014141c41490314911a004d600220010824000403111092000c445060101d101c1c4403070001211203440c071103800740c0802c01c035900600411744250080d9100d50f00a031b4000c42d003240344590441c0f40c041c940c00b40803000e440c04248035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 50582072 1250 50580822 50580863
    0x3030a050714070501300e0102130603020313030c0305070b07020a1112150702030903060103050a03080c070309050f0a0819060e0304060905240a0305090c0108091c0318 74
    0x9090100202d0080820504050000e48240c2c0c420840d4000b01254003403100da0030050070101450aa1040e50901103200604551800303500301d070709095008508810041a240d00c01c0c400d403407041550701050318030242c42c1c0d14151703844030390207500344d0030000100954800304960707a4071030703004490035402071440507034a0500d17641c81c103c1000d80920401000325146550080003900da41e0600c09070f00044440e858440b803c0e40307184960340849405000e0040000705021020a689602074000d8440c04855610250042040e1044500090200c0c1a07241c0900050030000a8404000382c05454901600e8a461446190012542c031490001c0d0020300c3d140b0420041d03000c0e002c0d0811901d4005e50402d406d105000e03110882500940e8051407501c450882c8400c00041440c3c43c80020a0445541e09008007004000d40f1084a543c41c152260040691180d4811420704c0d10800750398002c1c1030414001141c01d50002c0d00b8158a03000c1603107130b00304445a031681e0032044079410b220b8030310360030f80d91072402c2103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 50583322 1250 50582072 50582093
    0x306040506060c1e07120803091209011704030306170c130213050603060d0605070f021b0109050405090a02060301150908060403020307022103030a140603010501030809040213030203030a0507 84
    0x498003030030b8280400b8071903c03000901c8011421607403c09124091192850600e440c3c4c1640c030400265640c0740300030044c4950b0030010760040035240305480c0c041c0c4801a164a9902c10780707854500044002e149810f4100142002680052092401013034481d0307100b8404030007101e540740c1019507820440c0a03411502d401644c0009088403100d041d41809035139883d4a03a9025184a01800340c003000002400c80c0d5160782c8001c2210341d0043c010455801d01c4007005250080d0040000d015119148607100c4a14044800d610610301c165141e0003d00d0810b814403015020181040507203108040c400301c010b0b03581c01c0180d8041d02040c40c45041206e01e0760001002c000e02940304882c560003540c1070101003030340031040f50344003601a00c001000c081c120310514802a1581392603619404044207028882049801802d0041140c00b8841850786994040600300c6800388002001000208040201400c254003d000840160711000710802c1c0c3eaa00443d003182e115204110010b040051135100f002819801c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 50584572 1250 50583322 50583331
    0x7020c010c050c04090809040c02240f0610033c0509030708030c070c03050303040209150a090e100603150e0a0b040816080c0d0206130206040e040206040f030803060405 74
    0x1e1000c0c800803035480300c94855038030741e00150140c1d072501d0b44c0d003050141c00b008a41041001800c1041801000c0328001e444107142d10300d1401042440802407043e040e00b499040c0507100080340c041c5240c581c00100568488503044140502d43c40304ea040c02d0801e8121803100b11031100e5105003c0e00914440c0140e003050403068088191403520f014442e801e400001910300160748004111303540d840d109a80c04490040e6600140104c0d0600008802c00001101660107030b8800c1ea42c816030350300c48003102d01c40103440803401e54001c024084104001491340e0443d24220340c950042c1c2d43e0402000d0714550550f041c0c0c4d08184c442d50b00b9441c00360701c520a503200d84011820444d0140c22205099910300c242010f000e44090040807020811000c05250000c04c040740070385c404a030341c2d47c44803a00e00c0c0507110301c1440721290141c001c0b14000f8134911000807026100c0e9500070002860141080680e58034044c02800c00c3c1d8010350248801300305134840d041d440c00514040c190054503441d0080410080d40e40042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 50585822 1250 50584572 50584577
    0x5041415010c0c0302061b191104020301080a1101050c0d02010b030c01030b03070303050c010f06090c020115080703080d0605190f0602010c0c0f15020a0c02041a0102121e0a0807020c01 81
    0x2c0000715004034211000d4a03812508699a0840440b021801251030810034102c0e00817207130200d0019030242d55004200384a01c8504990103002010842240003d1143e40c1c107a4010702066070020f880310114405c0341505040c20350410a000d0690b514041c881014400940e6460320b0003400d038074040044441c651030910381030280c12800c9021035218951880b006050040104907604611000c1d008003094000301e800800c041543d0b080160094180200e003c00507500c1d1030b0710b41414200c00a8584162980b51000381402d80c919921400c095100c0002e100040756210000f045a43d10003601c05030000019250086050a0048010a00354154080d8056a02d004417a0785281c0d04000a1541b0540040424480041b00d00b8003031507803414208081c0e000751000600c02c241e82d410003001c2e018607000780c9041109600040b8070320851807225807a1800343c1c0c0110640145a9100f00c01040c1050b00b2050302002c924500740c1041850300305007090341c0428072003410003285650400060f4000002403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 50587072 1250 50585822 50585837
    0x3180607031d0d05190c0501090602041d0603030a0c1b1401020601060203090913020102010902280902040e040605040314070303051b07020f040f0908040f030302010b01080f0703050403090504141501 87
    0x40c000130b80644202c8100a00e0004100c80b030303100c1c05002e51840c84403503420000034080d0000900d0010025403260003881d01541109506060081407000014490007000e4020f500d01614000141c2e10a21600800c0368080c48441625010022000c00600200046820141465054000a8241807051304460210341c4280030391b0850765649400140c1001c0030b8011000c01090f1400100d0140c81208030103500700c225010141c04200090043c280c844403200031110500da100d26407142644594820844014031090119001c94400c1d841681c0061090400d024042c650700e0f0007480365004044240c000c65580c204006160030000e083c07004940c00c80108500d402da01f9030005607402c915184450180d5901e1407171440c1c01146a0007805519000a10f0b1620f465072826000340860300d60100b10015402c0a0f00910710354003841250707001e1500882d6407886540d0719007040b0010400104207400708101c42000182a0f21240f2441412210300d00072800309181908245c4521307409401110f0400200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 50588322 1250 50587072 50587093
    0xf01020a03020a020d02060f130609080a0302060f061801080c03010513210509150d060e0f04080702010504050d11030607050f0d020f04170706030f0603020604060503180607031d 78
    0x3081811a9990445d5420340480c500d0011500d18050006c8019401c8000150240c40d196080c085408443c45651001034107900e90310b4142d1101b4034050000c0c05a0b03c554042a0007c2c1102040d691189000e4180c8100e06d00224035000703040030a03405903860741c11580700c6140f1800c0c28000c441d4040c01313600c00d0402541c00c030f9276101c1040c425140c02511400846aa50410034804c0044134841040285420411503200301c40c07107129401030b030175503244900c0d01600142003000680454420a114000b03c0c580d5940c0703885e4441c013588401d004038104981080017040755900d4549507a13030701e406008036a101c64201420300d0b01d01203010380200207110f01442180120700e90382040711070f122903808000d42c661815809501e414000c941025084503100b10349051801030004031001195035940c1d05020111705a404a012500d9500000e0340140c0100414000751340200000c5802480804080b4140703001d00c860b6509000058480790006038031410441010440c12040c41411007800000c0d0044801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 50589572 1250 50588322 50588327
    0x30f080a030605090910141005012106061115040809040e21070c140d020402070321021c02031003030f1103040e06130c08040b06040207080f04050f01020a03 69
    0x5044006242640006000104520a4204400804000c3d1182d912420801c00d1305445900788610512400d203406900300003c000f504c2407034041c1d0801c455a0140c14181401142e040b82901620201d0a0000c8103d04240c5003511822008244540d40d081c4503102410a00703041260320071034080340100040500000c100400101c443d040011500003805d2030f41d1000d80c50601c44000c0c0c0081c10926000c81c0c010040381040010310b9110302c070300c9604050b1600c0c0d8074134000c0100410542c0303810480a014081c0141000d40c01402114040e05001e03c0307690080c0d040420480360080740500d0240c01003804902c014000207403c0140c00142c0d42175003580b62500c54907030080e40c548000b130200010900d0380c6d003800b0701030700599050000c1a03065a60352511100104603009058440c28083c050070700c2890000200c40c403c007081007180360384090450710740303407188a00f2070b82c003800041e481071b401c001c045d000444420043c5012400347d03411540711850312040200b1000e842e075406040d500001070400020b075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 50590822 1250 50589572 50589593
    0x61908150303091003051306060b0901020c0a03080406120b0409030207150e1305040f020303030906090607050405061b010f0e01231e0705090d05011a03070803040521030a0503040b0a020403 83
    0x2615250001d101c0e031f14101901480401254050a000d1401c00042800c0c88002e0041c0b590039001c0e022185206600010701c620300002d4030000d01036542c00d000c28030a083c07094841440c02c04803210003040526054000400b1901c100e40b013240982d2100d00d04200034031307407079202607c110303424141181c09a07020808989210a107000444446035140c0014081001426101c009150043c0031603844e4508062041c1d03596900340c450300c2d5180f1403140041c240c1842907088078181c0750007038070302070601d21700001c4805000350426007220300f03540311084d05040190314450810342c5a001750021a20480d42e0203070b6035103250b4958400036000c0d201c40c100145041d104c030701d40c2d44028a079040c12020f50f8499800f11138a0040d0300e00b8030b50003003220b102e400078054150000302c140c061a501d540c0150205404144d6100c2c60303480f80074520340090000304918981a9021340ca010880d1014060715a4a9402542076a00c007042d8213020030000301c1400144602168145e5000c40141c02c00c5203805d0440e2900450070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 50592072 1250 50590822 50590849
    0x70f0509011d03071a0304050601080c06070303020c0f030309150108030c0d120f0f060501031a010905010c170c0d020d020106030305030c0703050702090103080c010c0201060e0705030606190815030309 88
    0xc542c0e4a42c05405841c10004000200350481e02c1c10700c2070601124240e9280c2c010f903400e840b148039260000c80d0096020651443c0c45078010042407030051255030550181d00302d0181c0441c2d500982c8000c50402800703200840c0304010000142c00f032400e640042c1c101110041e04041303810b03841400020744400d40041c2e01c45c00c811103030030301c0203201440700300260180c510fa540040c0351505120781f0740c00031400c540048098500988040c404485501a09504042410b001da400160141c4c010407282d4040c1c1c4c0c00d902e10320300680e6103000010340b0712559007060307110502003851a0b11101c141060580d061103104907003801440240066440d54900070b003d400058181110f0a600046003000c060241701110740c417a0b03000e04020762039a502d0811000319000b07000d40341c00035424400300d1100d651042c4a204140e41c0032201c00300554840041c03ca1301500020075403a00a5010042c00c0d003002c03000035610f0107d0f24036958240aa1502c0201ea0780c0310711002040790701940c400d024000140d81c03066200b0411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 50593322 1250 50592072 50592107
    0x11d060f0c04150504090e030a0e041d01050408070606061407060f2a0e0103090b19141006021009080d0e010b0604030c050406050303040e010612060518070f050901 72
    0x290301c1c0c04560280501c40c1d548514a040c1d200e08040c000981c00c01d014000700e40031401c081151104248201d03480e1311400343c003140018140c0d400c441d2286000c0c1e126810764a00760030700c113080c02d480c801c0141c212401640c09444488012400404001c80d034003500c3c000e0f00780e0340307401f01c000a1042c45000b800d01450303400078141e981b03031050012800000d40c001080d05883c4500d150521483c200e8140d10038060360a01c2e400200d6541c4403030f5082d40a8007490010a6000b60000840e0f03132600c0c0361402441e59030b030009185e1500c41c0581003014406450160042401d8008402d44902c2c1c54806440c1c00c10785110720001904094140300030448001c05d83d82c034680208004101880810200e80c0107004012000354082d00205000c4140503040f68000150f660a54041207541d44401c105030390703805144641015070401c1070060081d03d01c200c1070b20840031409030010920a40303a600080c00c4403040703481c04181441c401c04120007280d00c143c0e41c42022546040c201e19018071038000078100822413864154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 50594572 1250 50593322 50593351
    0xc1e050615040915090309080d0905060c01020403080403050d0801050906060301060809120c010e07090b0d0201140706020403060b040f0e0616020f03041e0e01050105071e0605010e09011d06 83
    0x480d20b468010404095000c00700408004554041d5402002034900550008000f0540400e9141c40000d400c140e45005441c2c20100318a00f004010f0a6801880d40c81e03030350754017804004006002c007405000618800d5000c2c110300300700c04000811102c8164009403050045405102c855191002124191080da192a01303d507075440004030301c2e00038942401a2019070000e1101002d410640c0b11084c07014101c010784a000d0350720905081580e0250400d50b40c001d203002c0e070000056004281140520308600c1005050240540f2043c00f207030060740c425a407460315507a01030210324152064030080c5404000804c0b0000032030344225911040102203109a031001c1181c11101c600030001c85040b881c04608580e602c1e0b4807001c52000e11b441603140007052242c0c800d030204030b5800c55074005051fa10180e640a040c848c003500d801000d1844c50400908811a1100365404180a4010903010307111011001b456406c29240050071282021401c0303880d11050308044443c10004580b060b00304004500c2043c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 50595822 1250 50594572 50594611
    0xc0b1f1a09030a1506120b010e06190e071403090c01050913050a09020f0d03020606060a1101230108011e09020a08190218070219050f010c0c1e0506 65
    0xa0720441c03680650610888000c101046400010802442031041c07090040c141e59800c0740c1c0c0c0c1d0030b240301c100a204941d00c80041c000c1c42240e500b01da5009000078600500f070340040c806085813602075000002182030380c03000c005505412418020a4400c00380c00c00340307180f40048000e0303201c05021a58904014001481891a940d80b9043c6a00401c3d920010019414a019003100501d00c04100300e000f00703000080d024042c503101080801442c0c0507000b40c462035031514104022540800c0c244014014600e020040307100091082502e01c0a070300701e03d40e01c0555035915045013100305034080311480c0c0c10f086020800312007290071104810f00c0c08034045880882c910010f90050b50b5038114417007a00c21054540c3e40c0b18100c014403545103000355101b090101c10750740b424812900c02c4402e0360159001c03404154111303444540c2c1c03041e2580610141c8040c0f410002420742036884106401c000158148220303400c0c0b003d04040055880ca00c0c01182890314540e0350380d5030302c0c0d610003070400c44614805200903 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 50597072 1250 50595822 50595869
    0x2011d0103060f0807030c050306100608091207030e01030b0406060e040b0d0b0429010f0302060d0f060f0f0506030709031506030602070308090105100b19050c0303070c0b1f 76
    0xb01c01520f504100003804503120460030342d0b5070303481d88400e07183d000551200240900300031500ca40034100c2844000f0256046c100151a604000b0b4207800c1c0300d10580d510540e00055800181c00058880e40e5000b000300d60b00340004080d500580c501a00c241e10b0000f0800c0350941000240c07102c2c88040d9001f00d180d1901800080c0400f59510002e070040443d03404000c03c015221030050a098403d13420155403442a445488040e070f424041d1102000e034400c414405860410040c10314081d62590128001e60b40b0103420702035070225445444a4243c1c0c00003403007070903141c2d041c2e030010701000d8030704038214500060000d02180b2140b1010780344201a054020015038030340c1003240515000201950b1780e10641c5001000c0100032500e50700309504e09000314154501254008088801046c941c5080038401500541502c04110020f0140802000b00c1c400828060021f10303c500d40c1522035076441121820180000d000041041c0c24050810701c14890000705404100103940050050914008400ca0071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 50598322 1250 50597072 50597081
    0x60a0e070f0801060e07050c06040b090a0c0608090d230901050f070503040311040c020604120c061103090111041802090103020f030a0b031b0303090603040201020c120a060b0d02011d0103 82
    0x1c01d41221810502040552054001c2c2041700d5241c0440411030f035807198201d5950003a812501c8068000f400400e001ca80b10303c0c0d00ca44c10180703000503540309403569554065042c404d5400b10000c00c2c508410022002c0c0e050182d9030040706c01c0e00f08184510400c80c441e0300301140008152125020108603154103900c15000d556009224440107662840641001a503d400a04c0100d69001046803064510b0425019141c08130000313800403c01910b841e940c42c0c030043c0c91900f480080007564840040424000d00814102c8207000c0c40c0b041e03490403e41c800d01c0c02e40b4221603030900340110800040100304c4100440c0c061a00480000507251880b00b40124007910801131523104550300030090103541030f01d0360301480240d981107048900c4480a04a4181311038040c50005074103070024000c1c0842d600f801c000039a4000c7c414030546d20140909000601c25042040000d55550b0114003000308005840c41b501e07111003000c80e04c80040e03200b030354002000000c8a0081d9000011101d00c800c2069020b03810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 50599572 1250 50598322 50598329
    0x30f03050705030a020f0607030209060a08071107030c05030105090c0108161e050a11011503020112021e03040302061e040807110307182712110a0303230702060a0e07 73
    0x7036139070714948040000d56400c001400a141d6001e904042800360b4041e100710b07181c5020140c502810304d401b549095a0a001c001e00410074000203000301c030318000c01803112502541c171409171509058200b8051500b118401403090220354003052000140340c1c0c010406c1c541c0600041000051103100d0031045400d24014820300c4000302415128650240e0000090641050350395140485c000c07070840b04a00340e070a1110a2a10074500c1201400954821404200d00c0b440e004009450308801403a4035420900c203c4500c10070603000f105000815605100554200c010001600c40358a28148420101c21021f04001c10074100007900e001000700709040c0c1111254020b041d2502c6595801a495a800c04555244c0c88640b801c407005c0f11040e160028140d1544070000f103030400c0d05840e80c81440368480115102c050118100c0c00000e100740822910302914800d64001ca610341c542038080540c0b0880444c3c0c40b5188848108202d806580042c166602c0000c0200202d14919024402414110300d0340 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 50600822 1250 50599572 50599583
    0x60b12040510050a05150121020a090b071101110d0909020c010b03070608071115070c020303160c0e090a030206040303150e0901020a020606060c070302010309020406120f020901140a030f030507 85
    0x20800039070304215446948181403040792030031b804074107000440c1e40c0b050404016110100b001100540b600e170580c060064084a410700e5050191204010302c5c0c01e80103540c08503450f1901500508295a024441400e40d01282004260b480101d503000350590003140075401c00d03541d01003060081607400350002c66000c140501660b8185072a00c0c2d000b002d00c0e00484445001c100080b69141180c480020300e111510380e0600300103450303202c2410440e45002045400c1ea850b100c02e00007400380310f86030800d0740c0301180301d03002c17000c001841c0c80400850380b00c000301803a80036004002e444010a4010507070b281c0c407503814500050104c124810000c0f102419811110825400303808002c18000158000c00b200c50b91602141c080d0b035030750340030082c0611031245503682c1900008001c00045d4065044030568920041c4081101e507112010514440c0b124201910401c1c8040d00c1d100035400d04400b01c0303000d451071610f03aa171004000740105035107544522005000c10004910102403610070380030ba5001da50b014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 50602072 1250 50600822 50600831
    0x602070c03150606030b12060c0307051207020f0c0607031704021c03080603010b0a050a0e0910020d0c120c0c0f080f0304030801081605010807050306030a081b10060b12040510 77
    0x40342c400051401c1d00940303001c6407422244060b5464a030010781e200002d81e1008094598a5486c0001541c0001d000c0c00140001407180e000140984d001c19449480c443d40242600c0703188000403840c144d4070308611805074008115203404680e01074200200031162000403541c5489600c0880c100c14480c08100e46004c10034803070700040550001a40d40588002c074000e00400603420700304241840702e48601a40480141d01c10413000381041d144a5016811034142d41134025164454801d03603114207810703034008da507410611010740e40040202484c02218801040340c81600d10020f0070364450307094003616180300c0203516410466030f941115034a050002e00745407281010715018010040a00640001c0e0003040c1c540139110019140762000c484050f0344544c1162903100058800b41d1002d042950180100c0c0d100d2004960301c48014610110b000e0310320320101241414280c200485401040c03a100d0a1141c1003100c041c4550640300c0c41c0225849082131074480e803402d0751410500202014405051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 50603322 1250 50602072 50602103
    0x8070903061a0f0301020903030405010c111507050105090106050a1703160b2706060906040b030a080409060506090d0201111e1b010c0c03200603010b0a02070b0f070602070c03 77
    0x240c03a02c504120026a80100400304032002c2500740d008191615802d40d0061004108a41c801d4044030a0b2500681c0482c0000300550b0201d15a694610745410340c6110004510007008024440c09074440741100c0208801800d01000408035100c0e031080d03c0318071202108044043c501402107170906140d021030000c54200314034260000c00701c11200c080c4030307500c51164051840c407010142d1807402c03403a001030185550b8010420032040006000b5036041039450741000015101081110003841c014804a80c03600e1a03d50b1078816030300c40d40c2001c3d0240da800d00c641803040c0c9a40d5082d0b154590309082c07408506030821003041c80d24000441d106c00d04a03440f0b500080d036a4010407a5641e5043c40c110000c501c41d4403100540b0030382200d200080444101c21001c1000c900608902103060410340360501080707444070001100e40e0000c1c0c1000d640c050b00010300e407503882e80401c6a2402407042c00c0006080107100b44901d941d5010f0b203800a02a00c0d000140a0100222800b2600186500c0305011400085 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 50604572 1250 50603322 50603351
    0x1a040806090706090605040e130f061a09010602010c021207030e03070609080c01080f0a050411100503150a061d01020709020d1e05060d0f1b15080c0301030b070807090306 75
    0x12144501d0020550004e40800c61500c6a8121402d4541020f810f144644454030043d0802c08140020f07900702c006420500005182c9005040d802080f00d03000070001440c040c04c000c541501070b44541d0a5a1406800994968004c200c1008404015200741c1c0c0700e01190400b135689541b08000140d041c00344143c041440351300040f00d041545c039003104981814076120300566040c601541d010b140b1610100000e0480c441c04d4010b694030901c42c0903641c0c030205907017001c505690002242c90000c10004410415000c403400744022a140c42195024581072610b103001d00491205401407070f003082e240107441d204d80d000700700507c0106001001107550b480140c005200034903060841c2110840010480c40c0b980b410340c081c040c0100c1c002820050b290805036101c801507503400c90111031000c10030742d19092a1070058104802040c050304400f141008603440101011401894603080190500041c4003184030042d24039801350090038080200c0c2c9480d02c09a510a1140d880208030134203045554030403c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 50605822 1250 50604572 50604583
    0x2090a14010f08010f1a1003090c181107080703110c0d03090305150c1b0c09040506070f0f02030a03050603030d0903030b0111010b0d0605060d05060c120c09010206011a04080609 78
    0x50904000f0001c05c84010013076070540742e0815411040c0d604140b10701c4200e01d06030a400304801d20500700061130721016519031000c14a079500541d24040300406800480241e4060b4002c01c00359145141e1408170710740e94901c034a0003401806010002010344151082e20100202001e4407401480103012601500c6c0041c0030f10b2807404115554010440e04d038a903101b28115280c081c10f0300c441282d0409406184110503c1103c0304104c100c0d12801e00801c1302c2d40c80f842203441c000d50140e0302030031980c0360902d0058500d8440700100c0741001601460100304540c04800d0780d1540e0007529020a05885040001e0b180d070240c0d80d4402c2502e0304d0003142104240d0103510400ca990b000f078036901d10f180681c03108503003280c034400d0344250084580e40341200082c40790b600182e48207134024a140025042e64072420710304041207800d03000b8920002080000003c0700000254044014100b003803802c010600003e40b65281881b50101c54510301101020300a00d0100740d07009000b511049549138030b45244000d9481 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 50607072 1250 50605822 50605829
    0x28030c090c0f0f0923060c0c030c0a0e01090506060415021011120a18050304090605090114030309040f020f070b01030b06030a0c12020103021c0f0e1902090a14010f 72
    0x1d00904911100c42d0b002c3c100301e40040c49142c40e04801c2d945420b050280103c456aa0030401080c408131020300d6680340750180c03451048010041482c241c01c1428545421003420001b441100752110070001c1da100423a0380d43c10340703c1130329010801d0b8445101143c118051074205c8244528800c03d403410095002031000c80120722800f090209580021488455106184000c0d04d801001e000045c0c0c1034009400c00400100445c0900007108019141d40d07046801680003140400e0311104100090318105a843d40940311036249503c000442800290743c9204904480d4000d40d15005000c80050059060b54065800001400d541c0d400500c1c08031040e04003400216244945400464000d0a0001e50800001d501c04103da414508128070050030891600b8100c0c1015020011015071040d041d060f1200c50112410215400328205c0e501d40a850502c031540c0c665500c034110035078104101c280c07080906901620080a281c4849044902412005140b1100c0c280040c0000600701c58800c0c8941c00c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 50608322 1250 50607072 50607077
    0x140303040f0e24030d03240b0a030f0204051008040201020a08030a0e011a0f1e0303070305090f01030b101404030206030f0103050d0201020405030a0210170108030a031a28030c090c 79
    0x3c00ca007070545491001504191190154040301c0700702c0b190380c026030000e03800c030022810700e074401102d01445914413000c51f005680803410100c0c0072039400c0d13011f0260340d07900c0c070b0309000c298100760600c004600a104000070003401c00c907882c0d01041c15a4003e010b440b03122074000005659a10784211000060034210b81123910310f610300141440e50134218895604500002088660480d010404200b9108080e080c07403000c800508801201c0e0365010001468554032a48850740c032030f1024003c2190300000a030440781494102040840c25680b92100c8040d6400c1508000703c0f0120400303441c92540c055a08001c0d00102c0001c1885000036000c55114100c80c41a811109201c401c144101c0c280c0c0201c0c458950142e0043c03ca0300c0040c5084a0b100070116290724002007404142c0c030301d4030500c0d0402e81c801076190300001401403040340e00d4001e072070700e0740d41c403440741001141071402050104085502d04890007914040345d100c0d01007030802c202c0096401509540c03c150720b0780840f4004029040c2000301 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 50609572 1250 50608322 50608351
    0x611030a21053111040b01050d050702010c1e09090510050a030c0905010506070506040f030e0d03081911030f0a06180c1d060304060f06080a05070806090601080304140303040f0e 78
    0xb44240c650b8980f0840e01c2c1d0210704c1d0118440020203000c041d01001c1c0c0c109052084c1030002c0001d030061881030750301c9119241d001240c100d0507520058040c4c07412803030075801340b050803400001160300a42031000302c81d00b80200254966039058866040d11180c0c11181d0302c06a0342500109006d540144681998101c0804220700d0341e8600801c0014840c4c054014000c3d040b84000402084a50040500803400790900b02458520b00f400100c181413160400c0b40414903440500c50110004010b010480b07028000401081c02c9032103443e00d9074040103058034203c0e102d082c0001c2407003504e608818000d1860031203100710000c08600f102d0240030b0200c1d41d0400101114110300807502440c44820740a600a8a92071540c0c03540d484134030203000c0d82d5950100c1c0c55125840001c00b4842081030a41c1c050003a8050014207082c444c6940c145030001d1304d107000b144d00580040c84025004000c84049490301c0750000c40744248907010900310f000d594030003849100b0089000a000d00a00c08552041c6400010240c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 50610822 1250 50609572 50609641
    0x1080703020d031103040f0b0a0e0f0609040902060702040e0304060807050f030601120603021002030703020c030705090705030709030b0709080f01110d020711040c0c0308010611030a2105 82
    0x25a96002440081d6010280b0b03a8a01c002c2030040120018901c00401620b20340360b210038108110151030f51102e02c050030005448454154000400307841c2d1078084501e00c0f000c82403d00020000e00a01d84014402c9a5400b455001c6688031000c4482059000d4414003520094031040354403a0400d11515000c10410400203141a2060382207501000303101e820582580c468200440b80d001d00708107a08c800aa4804021001d0b82d1010704540722010b040c0e0085949980f10720b030090414011604032400f030362080d0024000d554861069035481030305850312948940e00c0040c1140d03540030550015044110400a10540c540d0050700070099608000840d0104c05840c40c40c02c6c01ca5050444a01d0300b41d10501c010f1107a4032098004084582c0240c143ca40400745900005084070007180c0900046106e100034a000c040d044030342c45005000d28244003030301e116104405c580f603220350150202000000410408901ca8940c8031980f0aa0741c440100700c24178181081e4121443d03100b44c8e10054962144914 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 50612072 1250 50610822 50610839
    0x206090703050a060e03070215030a06271e0e070608010608070e010f030b06041203030608030309030d0504020126010f0801060501120c09030b0c030f0c030103021c02031e011401 78
    0xd80449500500034403c0100c1611070100408103591519003a0004020183c09644d6009403d40c61070b450100d141d03600e0801c058100112031080d40410060101e02d880e880f2013408660940c11075030800c0601185085200640066400500305a80000c41c504007030301200540c001401d00c01e40d04140c40e0031510780d072a020181c81151084454900140035052001141d52040100b510580814100403403aa80d2480003d459904160403040900e40058408402e040d03040c01484000c000e824051451030070302c4408079441e0710581d0421451a034a403400325045900c00c0300e41c1421325400d03006240d03540c0740c02d122411004c40203114040b0031140000c40403e40d480b040c4035070411a40161170305c18844450888a90140ca8001340f43d4060144580000000c24105800d95100c0d018100c080b80c0d481c50001c1d502a45510040c2c030b00d80e840c620a00c01400180c4444600007504503408010784150900b0b032000031300d010121410141c10101c100f008800e803810540000044070305000c92040d843c5e8a40141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 50613322 1250 50612072 50612083
    0xc0306050618060f12070803120a24031205070605010b03040510050123031c0903061506090302060912120d05150102060c070c15050c0c040911060901020102160b010303020609 77
    0x200c0e40702130400d0b100d40c0c4c1c51610303074190021408080705807019643e850303410360b04503004403141c8050580320404000c40450607106601401d006164805829082100c0c400300002c89404010079445880d0416400b10303000c1c205039015294003240a0025684600001c00c06410a581c111800d11403034061602e4885103001c0c5a040c1c554080c04450b02413585020402210860030059400d0b004e1140303100c0108510854101c10b610807038131800d0280c1c0c0303189044000c030346a05010207003040c0a18030520020f6407060000301220780464001e07440c1c201d0320700003901d945240561010903108860605c03260320000300c09491021051076003080507543c1c1841900015111814280c0103800000000d08480c07400700142c10224001c041c0301014a4070344541c00c1401c0811034030b00e40440c00101d60003076800800c02410030054402e80b014007414826170380d07811651960903502e9100f504c0200d44085664030035415500c0440d000d480d2680103207024200105c1c003070400e0100f81c0040c0a003000103420780c84001007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 50614572 1250 50613322 50613331
    0x501020d2c040f0911090907030c151e02010c0e0303030f0609090f060705070b0106020c0d02041e0204091505030304080d0507020a08030310140f01051e04030c0306050618 75
    0x841861020741071060768042001c04481d076025035281e4a44040701c0b058819014000d1003524044544080382c000c0081070080108150350304e03442036605000190408818204880701e09100040c4102c1901003540c545111001321034002d0291181903211aa0541001c103403400651540c0f48040081c505040d201d101c1114440c10690340407010603051305010480303642c800c034107006544070442100210382c02d000080d43c000300003d0b8081140d40c2400001112a40108814001840110900e03030200381c0704859900081e00c21a078421094412650402200d0204140c4942c1159515142d2a1040c02401a54541c036061080d003200440e450800008640944030b03c0c0c0c00818030036103100c1c0308880d84d0b8040c24040780c10500940740014141410005140940c0942c03144c1706581d424803451803220746121049900c01d0981c000003181b00d903040811601440b1400c07881c4071f210810290200300c40d00c60b40c1c0c40108000300c8030b40008103101c11039001c14001c0000b111424804502205508102101904c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 50615822 1250 50614572 50614607
    0x10b0703020309060f13080109051b0d03081008010f0203010f09020309060408090a05090414060a0b0a0b030a0e0a03051b070303050f070303060b0c1e03040b0a1404090903090501020d 80
    0x301446003864440e02416251100d01301c2c0a01e1b0038000b1650381c2c00c8105a070b0001070541e440d01041001c000d41484802d03a0703c2d01d0b02000140e0b09170840c1c0040c6100e02055030250510000c00041031603907013207944000c042c105000003403181174013042402e0020340c0244200300f00c02c030406202042030111402181c6c05185601d009151544030358983c0b409642c080d03543c241d4400c3c1038000010301c54665400c013034800d9004124040e004191704078800d040030700040c040c0180921300080d00360b6691b26070309034805541e45084803c3d16540d038104960000c0211800000103842005059000c00d0b901c00002c0c0a6131204080c000c40648000c006650744030032030b0000a010520605c418840360103420003900000d0300a2034040b070055920740340303d0b150b40e00c00354903804c0c981c0002d00a906501c00001050304a21601c2005502c2d02d49000c1608017540921469403082285601c1c1100995100d0400d40d030280078818002c0140940d03130310700580021414030405016014085030142c01500541612401e0001d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 50617072 1250 50615822 50615827
    0x6171b0309070315020703030e070605040b0a0905030604380103030c0201050d090b06030c0315180a0c1e060206101403030d05040803010503010506030d1715060315010305010b07030203 81
    0x12968015240c1005004011522071108008040b845008a01420581d50f500050303490700141001016910020394441a03540205410082c160b445012034088a003003c02468a80c005210102c5910316640d004907230501c00d00c0140410322400c100d024032000e000c01c6210341ca000c040c403010240c8031704c160105009200140b004102081c01420300e05c0a09105140552401c10005414000c0310b0300e41ca000d03649144500300704081820b082044c0020201b0490040540c40035550b8414403d80004108400c411ba40c80c7c0c16007180081044a42041a400003d01e06543e40b0303a151580741000600c0707101d5480c9181100000c0d000d0001c6001e5025007918002c51069500303004084500520b50450f80d90184000c1016848116040c4103071750040c1c3c440c88030940d80303501d018109400d450010300080e201c2c0d000340d5022138034142c21031b00000200c0d040c070380ca400740d0340c1d80e45140c1c4545252041d03070150807280020800c1102e040c09440654040803d0b01c00300000e9807030b10a4201a80664039009000d81e004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 50618322 1250 50617072 50617111
    0x3060522030807142106010e0102030403050a02040b0301020903071503060501080601120903121d0c01020d050315010905040203180d0509130209030304050604030c08061f0323030309070617 83
    0x188040131015195040d0b11460072000070b0700c0741c441e03100121017802600c1034542030040c2c2c0c1d81e000a043c0980d0a00b4030003113080c14190b450309034075103032050f45c001d118581d529483c11060b1420340580d0b4005100a068481140c0d03907000e4000e8600c250810302000a00c0c0003000b040310741c040d039a00c500921044e503900d02609982c850490003050308003429401c1c0940c104080c1500c0080780036081402c1c005c166050840c200c01c031300533454049200c4242c0d041d900b10f504030410382079001c41900d902800d00c4a00172420014040162180611a0423540e00503000104204640e0000004014010300080840e400001038550450b1107024003022240d104420701251101e0b805240c028008501c4020156071030304d5074541c006a41c81d4440da000301e50500e02d003001002041c1d01480b071503520502040e941041c0c007422103d502ca855686000080020051400d0001c4016050911003090301c7c00a040300ea680c181030081c659921994442c0d0790000ea032001d000004a01100740d1180030b42c003e01c007442e212110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 50619572 1250 50618322 50618327
    0x506040203100e101e030c0b0901051c11030f011403010b030c0105070201170403110601150c060203040609021206160e03060105091305030d020d060902070203070e1e0103060522030807 81
    0x6071813607030054290035010072140c0114004400c612a003ca008800c1d0707185141854404040794840200b18500b0b100018144c2d030008200c0d68280044c4c44410303c102c803c4040b0318003c01e107400744450061f201008203c4104d04522035039041e03c80501d41110f0480341718041500383e59000314801e416400001280442d5401040030344216481410b01551194090002211a031001c913816800143c08400164002e002880b44502424140f422540c0c0b800048030064a0300a810500030945030703000001601b0301c0b10310342c00148415801004031011020090501d651030300b0070b54021414009905488004602540d041103900c20050701420860303103840200001c140303004010b623000004460001000400030700c021311005040050050b01c0b400400501000c60380507802c49800607104003e000051ba500203100c40032120115080c010b02d0342c9500b905940d024240d8088000901100300100070400c090700b18602c289040e04203180f03034002804404070070745162a4007401250603440420510b61 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 50620822 1250 50619572 50619599
    0x90308030604090b04050604120c11010f03020d020307110106060914040f1b02030a200a060b060c0307030809010b040b0604090903140a020c0f03010c0f18050d08040603050604020310 80
    0x1e0700800c0007603800101c0d22a013054540031102111a90015020001000061030140c1c06c6110649443c0401d1400c50383e42c20780982c80c00c2c00480c14030142e0607040002c944240c04441601001c01d90540d140d080050f4003030a141e44100b1452400c1d400c0890100c0d105106007030b40c208482c0b882226615019018041c44024415903c174207207071540301d40701c1c120020640051444e80300140d0303001315914001c0c400c0082403050510890140c0143c3d010b00178030301100c0003416542054010030b0000b03c2680c0d490000d0414819690340d00d0035808007140a034240b541200c200741c07045070210300034001003440702c0c04c2204803014100c0301a40f1003c00c1c0b005118a10065110182e007503c83d0a1440b1461034002060b03031503170090542c0000503804400e100102d4105105050b1044c80241d00901c8003442c070780005070881c07680c0200002001406080c200003000c05441d04002003c0180c04100c80c1c50741c2e400c14181d00d500c60b01906c03022900300000f00350241014405c90340324220103001145080d041084d40070408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 50622072 1250 50620822 50620831
    0x1104030f06110406050301180615080901090b0c0d050105040c14070503070b0406050105040b041505010f0c080a090e16050406080403031d0d1b0b150a030503030a020702041b09030803 80
    0x660342c0e07600a409845030503005101812032900ca054a941c03500180c2003c444200c101411038504081080001c1600d55001950f41080350410090b15640c19401c10b005100000c4094441511380c4140400d041061005040c2c00113580420b0002c3d03030325481844107554045c210303140010408542c40f01e000c007c0d24041c100da00d02c0390055a01d400d0300c41d2501e424005082d1000d840541d0f544d00100414a070074466002c41a4060754180045803035050300c8000016144a128188903201031000310300d5100c0d01c000d0740310070b078040307515034486140b041c000f481c00446001d0392103085002004104901d8030201001c2142c041503950524142c01c10000f00e800140c050400ca0134103840b240e40000740800c008500c200c101229004054101c04151300030151120001c802c0d21441007009041f0104841c040400d505c44071140001c48210300d1003010603004011640060445c0c00040140014014141c004103a400d008036001c0c0000d10f1494503222101c040b001d0b0b00f00c00f040c040c036400c01c0016401000f07164807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 50623322 1250 50622072 50622083
    0x30402150409053c061c021201151a070303021c0c0309120e03060a0209030c060c2407020607030e010b1009050a0807030507061107150c05060a1104030f 67
    0x102075072078560105035034080d59402e0209074980d001315040b04500040030b9480c014008001c01000101008039501440030340103074002d4001c1c0304844000707138420f122461441d0340030749426040a040d00307a5a00030706a0f0100c102000d4960000090085621000102034540c080d81c80d515040f03140d9020740003540315246c10050014101043d21104c0c2961280c0786031815251000301c1c42000c5890500c1441003180d42c01000e06c000d03000c030a001c50f200060000d90022000c140144d03117406850000746440d010405040d4070a0000030300744c0c55a2000b01c3c07411407039030702000a5801c0d55880100306079040b90441e55003005030300c61030001ea082d921170340101c0c58250200f00001004540d05e4040341c81c2c1d10320080c3c80804600601c10411080c10511400c1c801060072101603c030300d80c01c0d581e4990711910584581402c019990401e86284141408164003c101d2034802c10000c05603008050284030440001303550394015040010513078407083c0240031407140b203440e03607a04e050305650781c20300c6002c00b5520aa45 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 50624572 1250 50623322 50623327
    0x3060a030c0b0703020111030705160507170d0201050106030c08220209163519050103060c020105060306060a0501050a1e020304030203070902180103020d02130603020a030608011103040215 83
    0x11561850307020001e06441c4000c07a54580c028180a42910a520034428181008004110030594040d054034200c0c891058036070824003480c103100b0320b8003207150401c030180c035810006640580000551a1080102078000748040ea0303850001354200c804c1c001c8150042548140003581140c2295659100d401c103207854501c01c2410b50300480e991034000c4401e207031151100001c03100c032a41c11044901c2a05020b54101105c850b22807070800c0440540840104400038a4010820004000d0582c1c601122641010886580d40b810110050701e41000000003551900d0042901820023289030b504c5140c02900711490785140100450300c1d50702c0000f469040003444202d0500a2a84000400c0101419401580c0f154103500415050480c90350002004a1040003140d43d10851042d8101a42d00c1c2400c0040c0c0710061002d500010b07100352a41a1030311107603d6404111143c155011300b01c0c0a4041c0c1d01007250a40328001c1c942201c240d040c908580d95420310002d80149003150224030342202c80e140d006e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 50625822 1250 50624572 50624579
    0x3040b06030a12110c030a170a0c0f0b0103060f0209031c020c0901080a0b13210c06020d06061b05031b0102120c0d0c090506090d110d08041404020304021503060a 71
    0x43c0c250f215142c80d40001106044519200841000141c60501c0114007800601040d9a40c0b14140c02400b202c604a203035000c1181c0b00120b00549502c2466170700200e0081c0508841d14002600c20030074003089030a81d06d0060040c022254a1007624200b400150080c403005800014103d034044400d40e000d000c40c4103006010329541c44800800380206030b41c90082018100a19082050074001080002d42030340d00700340c80c13011580780c1e5003642d200744030110b40d6801e4500e081c000302e40d0100c4152000d803085000181c9100c503e46c0c16800f80c01110401d503948044850900b42450b1013107000d10011780141d005100142614044001069810340b10000042c175000c01c51144d607600c881d0441300b102c01e07980042501206147c041c0150040d03284980b4042c901c050610000403818041d80d0300150042e040003505d10100f14120020030b1120740003c0403540340011134076001c0299030007401003100b0704044100800c944d00f85402a0f82c01640c1c000c040d20840e4600c40e01c426003e40000308000da120151100c0003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 50627072 1250 50625822 50625833
    0xe0c0f0d1509140613090c091e0501030b15010203040f060513050d030c152a03090512090f031204050904050a0b010902180a0b041802040513020a02060f070503040b06030a 75
    0x11050400782007903d0f01e14092040003221083c442d031083e02c0b41c0c14045028002000505141e09603102c000380090f512550094414005880c04907414045103040c0020060144100034244605440c400b110000344903040126241d00452107500012800c4801c00d2086602800107040010040c0c84aa03640315500c000180705070701070001c03d80c04074100c01091000e100c4103a64170b00d411004800c1c1030105841c1d03c07408198055021807511000341c009032800420300c1c440c1d04103003000ba4002044032040a010040c2400d1540403a03000c0707110340103c0e5500326003801c0124000b81d06441001e807007400c01d807404062110b107620081007101e641c0154000350000402164010f806440c42b0040142c8844400368651002c1c0c06000060703104080100c010000440240225400d43d8110b00342c10310800780d054007050190045406c0f96522082680540c4002415540a020555280d900300c540c03d49801d8190407003114251101400600e04000103000f08019100681d0010301c0901107890380390554486 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 50628322 1250 50627072 50627081
    0x80117030c12040f090504050c040f090203010606030608070e100918050a030c170306090408180a0e0702010c08070507020d02010504050d0b0109060f1212021204030c0e0c0f0d1509 79
    0x100700b4210408241401004038a000c0280030f01410b0104000e6820940c4410340d0301c0caa40c4014512554481810780140e0310309400072108990302400a011440d2110400780c0075280764002e018052180180000e071a04000c17201c1406010511490110345040803000301c00b40c81c80e210700300d02042d1014010340003d80100b1801030101e000f030f42c0c4d80202e00340c9031600c2152001c9150b800408204140180300c11503480c0c41940f80c005a21201141d0f0f00d5242c0c9600d05842c1050200040c0c1c4080b5140b80054003a2030500594400c07003503a0f0082004075403261054491040c1601d81c00d0006000b44a81801810321340ca00c0040346005040407820b04d41d6410002d40030101003441115038504940040202620500070503000e0308044c602c0d80c1803e8101045180e41c41501080075149442c1200180345490080c0012001c05e0100204595120344034200040c01c0a06407140c0b0b13001522000003c1e613102c0c202c000380c5095120140e021460041d100040c10f02402184c188403a8040c51080b001403000b103c0e108 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 50629572 1250 50628322 50628343
    0x31606050408060c0901020309010f0908070303080f070206011a160b13030306080705012102090405040819140901030e0705120a02011205010b0912010f0c0801031b030201080117030c 80
    0x3152561141040145420488050001d41811200344503503021681c011003a108462000e00e030068001e24081421a042e074003641c8080e106000b650008418558400c21040c85840701140c854001e0729002d504a9496009110784040c01040780a00c14441d02c044d0003d04c2c600c0a2038160410554090b01d5241004c0070583c1e40c1e025000022640b0b004050b0140161070080c05404042c00c04213181c640045c10310115010000c494114042c00001c2459160341030340c001140150040280b4981840d00c1909603100402c1160404c0d610401310111510454800048a050850040c100301c0c0517801034000d0520240b200c02c1c01d0203010310200d500d807501007240742c4800c148801000284440e00000d04291041003104070400e0500005014070000134088441600382514540e0107098045282401800c84854001950341000c0104070400d90100700a4140d9004c3d680d40c00340c182c4c02e000044600c410600c070082c0403c42c828010030103900d4a045440c2030500c02d1040d6403130021207030b0290382001901e40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 50630822 1250 50629572 50629577
    0x807080d0c12060f090213030c03050109020a0e130609050a050d02030a030f0501080a0807050a0f0813060e0d120c080309011b02060702031206060d0f0605091308070b0402031606 78
    0xa441c000559002000d060344010a4004210b440d003010085140d50031240580f00c1c2141c0c00040e01d40031213595481c024004c40d04800c003980800d4691803d140a0030101303106a01c0fa940031100403c00702c00dc05001c0340200305c0102c2500080015559200285c1030025041e2040e00030501c111010030310a2295481190380f03940a190748021080d00902243c02e21135903401e0701031a02c2c0040c0305482c0c001442d044020b420100f10f81d01d40d401c6103001d91800f800054001e0a10380300c09406c504029035000500280100034080f005003503214542145ca842d13900100d658044092041c0c80041182f820010102070f080e4a004c04044205070bc81451913841035600030038981d0f440c0c118285c0b68039980b8600c0b950002606c09070a007814620402981e0b40100321961600c00307444030208106a07681000c880101d09101030900c0030b096021802e40c0200340c03a205082c0605000400035080c1c020309213412080356030050b00542412043c0d25050440c000041040740c0510900600c9068413024a0b4078000030125907 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 50632072 1250 50630822 50630831
    0xb07080403080a0b0319050a050d030203060f04090503031504020c030f0d0f0e0703080f1306230f0403060504020d0203150a0c2c04061710060e060a0506070807080d 72
    0x28900140140d07802810f00c0005840c1c059041e000d5680814040e0288400261200d40c0a40a0a019003000b059960042c40c9108a07042c1001c3c8580680103944142d00c11500c403410300d01c007541400180c0d8800d0f00010401e0b0070820002d0351501c0c4141c10f41c5540d0070064001030400c4040340d191840c40d8404102c00400c001c0200d0601c51425250003019103440b528441802164142c941c02e584d103107078a000007401c00b0004111086880d0148040d143c030f00788407118080b829a0b035880064000b1118464104c020041d59485540c03c0000381d040794129929030244518051441d10713071000521010308206e034014800d08c0c00d400543d0f810040790301200b8421078808024102100c44504440110310142c051024810313107144090032004040712003a6a8072941d2071620100b00000d0004c15041d0458030003100c1c8080e926042c400c00242c00d1000d9a01c0c08070400c005a100c00c10b050000ac02107512035071000c0640000c0c04282080b40c0600000ca120741c0b401410030310740d962101142c3d00003100c0d140032076944 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 50633322 1250 50632072 50632081
    0xf25090e0a06210b04120302070b1611070b09010e03070504020a031b0e06030c0703032004080d080603071a0409020c10050f07020a20120d03110c0d030f02070b0708 72
    0x10000310103c1d43c4a007201041d082040c5640d50014610001c0c0081c110303d00955044544a00940445858980c4080c1102031450100e19840400e20110f4070040012220718080e480440c0024175001503030900080b240c18881e10000440b120850031180d250140145100024580c80c1ea001500f021501c58901085111000b83d10028071041d620310a020444512021040794984008030394101e2990301d100c0da40d41d4600e0a00b034001d0540114561628602140041382c245034080282055a81100907034400c030081810072101c1e1031041d92840d5242d0001031b0100300184410900c40400000800074500f407a544e055090200c1e0403014114802d0341040c000c1c0c4410054511506074001d18084001540f820b050800a40c1d03a0b0410708020110f11a0400d03450301c00c804002d1480c031043c0014900056a500d07403c009480d9144800e9200210381406003d01d1510344d80c0c0d060b203080c071030762100904030003580d020110003400c980c2440004640c0e08201c0c140c0440c0c5183c0c00244030b021243c8a22805041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 50634572 1250 50633322 50633339
    0x6080703020f0303040608130204090b09161e09020307140a020c09130f06090203031902010902030105090d050d02030606090a03060203040b070914010e12010c020a0b0f25090e0a06 79
    0x801229209400401046c40b050b500700e801e2980005c40a00b1416210b440b41c40490010700c03090728040c05a4900b0001c0169181c40000c190581c981c070400700041c000c1da10454940d9a075104543c01a6444c0180024012461b181c1d0145a100f9440c0c42c007401813090300e501803402680022840030050700800020074690074684021a0001e00270300c3c101d9103078107081c0c542c00110803599100810b84c6445100038005d41da810410b550701e0a00c0c000f4551025210090040d0082410304001c034002d50900c40000c00c18007010610740008400c1d5203815240001c0e102100000b940300400140e84420140040400fa0700d52800a0010718422440117030740b410b01d400d0181e0240c00003840701081013400b0b28140205200b8011504030003001b800c3c0381c041030f101040055403c40c140421355010f58641808514206e60024038201024082c20301d00415855501040c0141d40b0119a101610500d4840f030000031000c0c00c194010b010840d141c281002130b2292000114050f0980ba45a25280c480302c0501540c0e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 50635822 1250 50634572 50634589
    0x80315090c220b0702010309021807030e010605041a0d17070305040305101e0e0c0d0602091e03070e04031704050c010201060618031101090305120a0f050903070519090608070302 78
    0x81120701410b503240c0c03802d0a400c07800d124040d402410140c42c0c008107411034840b0080d03448000f40c1a9440b040c00c0c5007030440100101044000c00c2059820141c0000e05803c10f44600d41410a114a074005202d54074406e0002d010191001100d280040c2d0007400012003102000c1c1c0072003882030399840d503203900d1402c01d0391601e560a00116221403410034645500d0a118502082d1486203100100d0500c0591181905021400b0101038112065040241c00c00240da0f0040c09030220884100301c9219400e006015242d01d074802e159055444140c040c00380200c1d0340d5005621500c02d240072481240d90403110b1440c04030a440c11652580807480c511160b60702030141d800601480d01d007018140042200c21018041d07a0b1002418813022100e04040326449409450003650304013013141d03a4100307041d90311052980301480141c00640d01d0071001d00300e10b2140c4111144050300500401909040c10f040120b081011402601c4189050400007100d000c68095140105450400350000500c0c2d40184000300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 50637072 1250 50635822 50635867
    0x41b0503060601081b09090108030904150608010902160503131a0c0a080a0207080f03070302010c03060e0f070e0d0506250813050102070c0323010605010c080315090c 73
    0x29001803042040b1a680540015401040e1100c02d80e92685004030801380d61282042c01c58101444800120b0701110000050207604e1058400300b0443c41c0c43c05c0320300b0800a00d4080d07140025503a0f401001007400680250500b01e03122402c001d0314403803031f5590518544c08001a000201b10800341008810641002101176080440c0340300d180811401c041c035100c228440000740710304004540da1095a1017000000042c00380a0110381071082404c000d02da83c0d80140d08228015802c0190360840d0301e00c04d020f42001c66060f084400401e464000780303010901c2005085008012500d80340c0a000d90b03840083c80e283e0750242d0090700c041d007003041e1814401c217200250040000e4600c041c50807055402140c80c0d91004120801c40745041540c82c26501a1040d0311f0301074040c8050b00e0003c41070040300d0440c1012181c00742c10701584828a02c140c14203881c0144941408103006241c1400072850f21070045500c44c125000a95411300f90800140d40f40c2c400356000081c04030003041c0114410100700184a44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 50638322 1250 50637072 50637079
    0x4060603020406050d05040c08061906060903020d1e021302040608090c010509090405030d060608010806060a0b09060f04030f0602030405060a0204050a0302010e031e0c01180e0f060a0b03041b05 85
    0x2060f003002000f41080c8120105180029a07800000e42800400b0310840082c08400e0240c80a600300480e43e03551662110203103c00da90315248002841074001c5018004682c2d01401076101914183c540035031480d0341800b002000c40b034007040040140da40e40041c00440214110040e01c86080460040500e60024a20042e07540181c038981d00507a044403e4601c84c0c0b00482d1501c21558451520701d065002c4d001d05040c10608204c804038407035403c05170041c1032f150b0072821144035a6508003045180030f41489502c81850040107284203a04110004050707130303092203252518040e52a526412480c0c0c142001327407011076010090108000d0180042500a000c81109604141c284000152010b00c0f40c0f00090601c102039025906a44052000d072012240d00c546000d4542c0c0c100c14659200e80c08a003003940050b4084a800840b0441000e1742e0b401e503545200c15140e10b03a250801c8a0340003c02a10700c580c040da540c0307000203802d94841c004602c03a611484a2100071030494003407807602d44654020034403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 50639572 1250 50638322 50638327
    0x10504080d02071e0b0106030e03030f01090b0f030f010204060906090b09090403111005070908010204030c0e06010201140a02071a010e04150b030703140607020d0203030a09051204060e0406060302 86
    0x8150104190780c1e48201c40500143d4070380d00d514201c15001d140c04c0f60742592003e045504028000f0204800c0d04941c2c480d14180602c00001002584074481243d0301000304404000500410b41541e20840d400304000d81092030310404940000d191241c03003410503040360340004040c05401c3d889003502000300b0303440c10400030701400c000c054441c030f009424248d4000c0446200283c241031080c01d00d5131581e059042036502100b54122040060081210b030180404e0b4035040001d041ca1052080320b080342e07008800c420180f82003000c0e130080ca0030080d0030281103648642c07102c11515810032499000d1035400c0f000507510b01c4c030b61a000e2402008074441d50801c004400040040041c2414025800b540c403200150003450744602203030051840c140200d03054810100003002700017009940c10a10251002122140d40d10030b1000ca03618143c407064003006030003c3c808600d41c1f002c5074100440d51845041502c070345110400000d40650025401103001980e5010307414000d0906100300005400c0504e015132 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 50640822 1250 50639572 50639581
    0xb161101030b130c0c0602030c0c0607110a060b0d05030307110601050105070809100c0602040612050a02070c0506030901110a030b13140c090a0503010c020c0111010b010e011d0d050f0f0105 83
    0x146840118280183c206849031124248248158840702e45640c0c886011922410720000a802e03030f41150501451a10626010610a1340a0110400f000c02420001c280c0c013601a9604c4018241c0d8048042e0810284000c507000030702c040c030107035100301c1103590380c0d0441c000e44041842c6018410b922150600004028a0340860b1a2404559400354103461456500e08400c0303080301c000710015030140c8901e02c007290118050340e000c00c1207005111400d4083c012030700c0f1030200e0001c078031590000819400d44d250301009907007030400181d6482301c00f84000080c1d69076001c1100d0002c0e0b010325011000a90b071040031444920344002008980003d2940c20081180400c0014151080c080c4c101003600c0b01c0840c41c000c00b80c0e5010740300700180c0f1018009011940400d1070207075480e080c5d0300c12503000c50a666040440c1c3c01052182a824240503540d5a0040c5088001503070380d924030031204121220341c40700070b054a0300c600c00044102403084c4002d007a800c00c049862400e140704408524031a905000c20310 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 50642072 1250 50640822 50640829
    0x30f04030801290a020c03010f05060307090509030d0902031f0b09070503160806030a1e1419060b0a030219030201020d14180a0509010e09150702100b0a0b161101030b 73
    0x39400340b1503500303c180d607002d405500740e00c0d00383c081d0080d40d410b41c02c2147c8407a060b2901e07040180200420b40c00c940406841711103000580f601140c034078007958000d11460218006039042003a2840c0050b0940b14208402c62500340f001101200341641c0a4590110b4200d03800c01449460340103140d07140603030642c280401200c8400451340c0079801000440c0c8040ba8007a030301401940c6101d5448101c8040d409003004600949131200802903992000309804000d00c0746c0c001c07460904c9412002c1501e01a03541c2555180020140d000f486c54010012080200040c0c079501e0712804056001e815001005281d440024a0401e071858420204a0390540c0e8455801d00c50095a00540b4007003070000b03140c0c2e03000c408038042040c264419613200082500004011052208142c0503a00c50416603c00300c10803540c404041c2c00a807450401a8404501070380e88240b558021618420002c1c01000c2c21680c0b411700490b5600310461107030301c0d02c0340c050f0004204a04170324050744002003800c00380041d8040e80b000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 50643322 1250 50642072 50642129
    0x150901080a03120c170c091801090606050901050d05040602090d0b060405070207061407081306080910020a0c060b03070509070509030c0913021002010f02040605040e0f0609011a040803030f04030801 87
    0x70b010300400300c0000308500740c00001c187c0743c86020190520703040d810f00100240341490203200c0c0041c3c45207448070118960344102c0c00c0703c0752868103848241c039040c04801c60fa0000d010041041c2c404580c20310655841e5605c80d410528058000c0034034032810306204041008543e006084607003035500c501020050b85030401c04840059482c0031415881c0c007000d08011041d846120310600d404144048041015500710048a00600b03000d01115542541240f0050132403240b12020404034655a10800010b140c60700140800c10007c0c055804095a0b04040b80c01d620b0292840c801186c008607050300c4604041000c02100002154000344a040441c400544e00c807031800041e0003041c0c0e448642d071119000750012002403420800840d9a07542e0b6003401000c540047c0942403020010501190b05107903001c003500e0107403400030a1844940d19150010301500800000e2035105142031000180281c001c0c00518825030b2010450310711484c061130002c0025205800c0600141a02400c1c551101109201d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 50644572 1250 50643322 50643347
    0x5070306080d0e0d08040303200d05120a090606080102040501170613020306060705070311093d090203100504050f09030703053912070218150901080a03120c 69
    0x410207a55140c0f80d002c10607207000e040c00a0720013000002c00000301580000d07240b001e480d60202101120290065290300c460800c080321002850602080400690f14402140c000c0c004010008107041141d030f50405070391003503000f60b140b654003150800003560000607ca0998a001c0300081c0b0307a01e0505c000403d41700c4034080416407a940800001c45580310071080f00c010a40080c111841d05c1e5aa1a0200c1c038a2050007120b4001c884d50b00105100d078201010561980080014a507040003400090468010050550f0b0603c0e030740307010700000e445000d071000354082e8180d440b001503118103000034081926800f928000346c0029400070001d8108012040e2801c450f0b00d80f408aa50b0417034800c0d400300001d0105107134040c01c07140d980d210000d0013100d850f07003180401910a43e031903003161551804290040c4000a500451300401c4402d400f40088400e5900060040b01c2541c402e04940104500380400d070054812640540002028181c10411444154040110500c2030200214004100103c8400f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 50645822 1250 50644572 50644577
    0x606080a0e031905040b0301090506030c0405160f0203130b09030d05040515030603010209100309022b14030d0603030c0308090a020a0e0403120c0905010e06040b0a0503092404030305070306080d 85
    0x8443d41c94144a902114014907400d0342d015181d5840305802c0f0700a08094414078030910600444c0441400d003400350500c2400b098a012a116107103800540700b040035074010100f140401c000c2e00740076100d02484003000d0300e90712501d1525840842c041c50301e072103154000c074028000240420440c035600c000044a4952100e000d90303849880700004240039004038002148e001e42040c840d1102d580d4541d000d00304550007101c28000f4200ca01188038114032203900748505c90b8a04454040102e401c0c0e42e0280823520506040303030b103030981030022202110201d40044000a05000031007043c550700004058000304c1a0300a0701c810a0b0a50001d08e84000521070070710b000c40c102c40054140741c051960b81c90007080010040c0440034840c2c82c01001854180a40c070b011a40d4101414500e05221050f1001e40703009100943c9400c51001080e1601c0c0c1000f405a0454843d12048a52010b803030301020401c0c07203d84900d110b1038101450b0160648038010203000405203020b104002140001400f03000c008101e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 50647072 1250 50645822 50645857
    0x403050c0d032109060b0a0f121103060405070807060509060306010e0d0203010504060204150903110409050a080c01090b0106030b030a1202012a11060c040312120f0606080a0e03 78
    0x1441e040e20219800e41e84100c3c411000c0080060400403a0005280c1e103104041c10400100381d0000c02030070a81900900d91a44101c7d4001d20425400107140400e0794014160809130240c404002850414103c40480c0e25400640003044804000c108110140c40d0b9030400c01d0501d43c0c0320020803201d010040020707040102505c3c01c42c10b103454201907459181d401030000d200c180b07844d0500a020754018447c1000a01c848106c0c015600e220301c07003080550b0790102740e442d04521248100030140015100c195550f000d0b20303a441d80040c038000010002c100d00c0d80b00118000101c0d06050201c210160700110505007825001c0c1c0c0e0656001c0b51811032140e11800c011144410080120b0041c22040c458002800c1d620700400000e070458900040301c1c0403030782d8820601280e0340e10304548451086d24200c21042d070030701042c00016030858031b4400400140c0380c400a901000e009942c142c0701e0112282d88481e6444105000060f4018101d0341d011550034418011403000c1d50703080d960b07031094010711000e15911 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 50648322 1250 50647072 50647099
    0x50a020906130e07080d030209030c120111030a0b01030609060b1902030f041205060105040b0108011205011103040b09060c09220f02040308040f0f030f080d1103090c030709020403050c 81
    0x39100e6484484011890801c002ca901122956588900e8003545c2d2441c0f0958100515041c424003c566000c0406409050700c1030328101403103c650443c802c600d245540390348504645412200185104120406020400300056000502110782c035030032141ca40b5041c840203000142e01030007140d4034503903c841401012034221a04074150302a05404110000d800140001c0306414108445900ea001c0c809031074860340e0b203504000444c0d1941000c0d43c081010003004100042002e084030445034042c40022404200b403002c1d441c01c079801284e080312180008414042c100004004150b40000301c62074162910102a00041e550103812001009140854206c1c42c85104075400410750070610240554840b40c80b032401d524940c020303004400b000e0310f60800004408019101c0701c42260780004000c0ca601c1202e4454402681c0312140b00d01a040c4c8503641e607a12010528025072140090300050306890380716108040c14210642e00c40401103005000c10300105401040310301071705000b03c45c05d0041514 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 50649572 1250 50648322 50648329
    0x30412020d1506060908010e06010501021c02030c06130b0f040b0c0c210403030f091413150306060914060906010c02180424090f06150b0c07060305070c050a020906 72
    0x2c40c1041e44041c141003583c00a50a40c000d1503480503079146d4002480340250800145a0b900000d2080d103006a01c02c0d4210300240340000d150060141035441500d14000401440a00e425000e175000762022015801d400d0512842c0501c0c01c0c1c010108034921015414552543d212020b4042c0c50320b1511540010701008070320042200000f1741d0102070303100d48030150840b194541c42c1c01520003640070800c940b042d40701c0203206840490607a140302402651400c100e800780f15040340101c2d65442450360314a401648450030602d0f0900951081101042244c205030100058030400c0342031038660309030708013401a60340d00e011105030301110a280100c0004103600020b800b074264413011081c2d064116050000780b000a9900002400e07900340b0304e5000d2031038121500b0840e5510341003e0051080854900c00003511500003500c2c1814182c030040540c1d07119030800d071050340b151550740b4442e4010141003103240d4040c080c9541c003007076906202c05840400d03195282c58a5190000078424804a0009000e503039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 50650822 1250 50649572 50649593
    0x16031a0a061b051b0306011a0d020304110d05010c02010605030705090f0403020a14030a09050108070c1211031c06050103150b0a0c0803280501060518040209040c020604060e030412020d 81
    0x143c2103c126100c007449410702c1d94040c88000c0b03c59020380640c0e800410f184240841c042d15007007142d01c4041ca410001a114402500080c000b02c4415030b2140400c002780e615155011301c21802000009441c1000c1c0f00041c1c21a001075000c1f0b80650002c51042040c0d40c0c4001c1d5040c2c0c400003070400076100d81e0340c41c94100e0520001c0d11006100e40c45051940700c0c1c101c00000a804030021a40f100c10655407200c006440c03401c0304440c070f1400a4010512600000c0c00c1e8544409130b000e403814450940a04108024110340162000c0201c1c44410561690400c60070b010b641e004203402e090810415090a03051058929240280d040f001030010307041214502ca440882d481c15080703051f9030f8036418041c2c2c90f5880c200c0361000118030407200614a480417842481882d040750240c2e00d40c0e52401c1401d0000d2203000101004a80e84581c2c00d0204c0526900c0358080e01600d0101c541c007a0800b03140170325200e0125400044c0342150356000303000520008003408401607151740c0444c1c40041018070340c9465010003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 50652072 1250 50650822 50650877
    0xc03050109080705010b0603011802070c0f060309060f0b01020d110c040204030605060f010212030a0b060c0604080310090c05030105010c0809040603140c04021e091816031a0a06 78
    0x103600c1c050820003840305450161070781522510003405248906070800c2418082800b60340041d80d0000c00e107207031189a59000b410418401c8180d59000c80d901e080d1840e4003c8540e00102c0401d442c0c1d600d400800480b0310900f07801c4e0008007010001d4840200000799070f00050a144402d000010420480100f010481c200000200a0042d03544070345921f00384000e0613040da0b98500410480c2c100540640c00400d1100f1035817517114503c0d045030743d041603c0c4003611440d800c0c00e0304200304101c079a2a00d44280b1942c0e118501070b0310a0359a03414034900c1e800f004e112660142c13a2251906130107100d04c645c407204880c1120400d10344440d41d0741c06820704400c0c074414021001e601a190000c0003003084445d00b0f00d079950415650a0b24911f28210050009134450498940384103001050003245150f001400303002103080140c6a0003901008602e0752904200541d000d4009030f022640c1d101a03190300d40203c200400d80403000c80480c2c0036000106100c810b2500400c400d005080d91901e484000440000440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 50653322 1250 50652072 50652083
    0xf0f070311010f120c0e0f030a0215030604090501150f0f080723030313151403060405040501090b070e100f0e040506040219080f090304050108040b07020a1202030a08011415070c03 79
    0x40e11700709000504002c5080141ca4001c100c1c1000d800454a80854180c60701a000b40c80c4038500d0100103040e010951009108651040d5242310880104100b4440c1e030407030403c15555a0000c07410502d2642c00681c01c0c1e070140e0550340d4142014071000390007041400c1111b4103440c80c2ca00c003601d070300c0402e05500921003100c0e030540702c041481c2c1c40181030003440c14221440c012072005210254441211021121407108a1004c01040800c00e40d0420740e002c1d40d03106000d000000340608165070350901241c130030340d02407000489502030310395185050420782d040d208140c107040c001a6078400c8080c00601c1100d00c47e504c11a5a440015141d485603012101c5c240d1521892560341100b43d24044c1511a0544213008842000d00002c0c466400000480d425604140c60300c00c125540c6a0710f80c108c01c28010b1040c42103000c0e00d00032030300040c020340007002c200f0074580156454105552000b019101c0580c04111811411541400191180940152842c2d03d05800340d96810030cc0c10285400c5002d907100425 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 50654572 1250 50653322 50653331
    0x503040606030b07170a020414130b0d05100e060f0a0c0c020909160911120403090e0c1b0604031b0201090e09061008010510181d0f0f070311010f12 65
    0x50760f1000c0f148001710181c0e00c00341d8481e00d60319040002c07070207140107850f14102a2103003c0c03054076003042000700c0420100f4002c80e8a44c901c60100c0d003852074030802118541d001001080c41840c09014002c07500d0b08550003083c3e540382c91681d01d1142c01000c0e05a0540c1662408500030361441404030b00d03541034015040707141c5800c02088507940c41c0c100d24104404880f0b1028041000300b81406030f83c160385011a00d1a0414500b030100300a4244060012400e000308440d0024031a28282907040c801d009201d07482ea2170310303d0f9002d15628009802880032007038024200308030002e90081c0f80d01006c0d00340d200c00b01c516074040344016203200401c1d402101030042c541c410880c01c1400010420300c50b5900d4070203c03110699880115081e604e0a80d00d2200300c1003c40d50034801e888806c140800510f01805000c2440400d45013a0341d2035a85440400400c1d4101c0494801c00010810100400d00280c0b0000c01c0b1051541d1a541d00310145100303a18100401e00c03256244035031042da0700c4064078480480801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 50655822 1250 50654572 50654581
    0xc04050c04090b090103020607080f130609030c060c12030c0c050a1112030a02070504090c03021804140307030203043f050706031a1909060303030504150506030d0503040606030b 78
    0x4000350414424820b00a0404546589609008900504a80c1e001e0012420301c01aa922030b00c040e080042e40c005079010600200c9001d40020304210010401703a10350215550650400404c3c1410036040003052000300c1c200c0c040043c84011a0540d4080301307141c0050400c0090f40d00300c840300b20240001e8140d11070040c800052140d02000d201012100300c80040c0e6105602080d0761b00ca0140d07403106005a00806001c00890825412a04a507442280c00400031504c3e60f0020314003643d20100c20440c216000c040204000a0700e24440c614117240004608003082550000d58a22450082d560703a050301314184041c01d400301e502d07155481c02018403001d03e98500c0240b1240c80c0d030101c1b0281c6803403140304c100180c1d04c1c0c02403281d003084910303800e0025841e02000052101c5010991045540d1031040d501c005550300b040c0c424400590b100e6580896281017038101400b00c0d102140703018981c80c1c6880284416a540020034080c3c03240d85091207034a0f980d0740c2c105880100703030f10703070010781305580240412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 50657072 1250 50655822 50655841
    0x2061b030405120102120f04020306040f030507120e01030b0604051c060b04020712031a010f08130506090703030e0906060301030b0414030d0c17060312070c0b0f1e090901090209030c0405 82
    0x1011a402442e0040704039540303601240c40c7c409010b40f4042c0d01a000500460041461500d0398010f0501a082c0346240c5a8207035541d06141420811340d000054030050348208940e418040d804140c042107887c141003e0821001452140310110750a00104124243c2010401a5081030441c00c8004104645030710035400e085603000043c202c80c0b40020b26103018540e20b100107200c652002841a910a81c0180c01c07094240d40d00d0348003400700c0040300c0b04c0b00c424500207041004868420703507255018001041ca146005442c401341c0b11400761180e080d90702002015152581034904598010155126903103e5050a00d0103911000010146000001d5102c101c10141c3e000400141040c1d9903142d480c482d0b28400c0b203529081a244642d0607003240f4035400681d0203d40280c21002c0c0101503400806a40704441d46807035001100c011350880c4045a10780302d60600304d0200b00d0f00111182c3d483d15052080001410074041400398400413640455003c0c2c450328200455021900094001c01446c04c00d0280c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 50658322 1250 50657072 50657077
    0x30114120316020a0f031509050a21021204031101050a120507081e091005060609090108061602030c0601150c0210080a0b010207051305061909050a050604020702061b030405120102 79
    0x43c0d008454644000846070302d1213031410100ea4002180540d1031015400b01e10107003910b5070741039546102e17408890003c1880100c04008540a00441c4209045210740c042c0c101001518443c1d50b0040034801000421540c5017500c605681c00d103415980c4402d207000c20344484881242c0281c8a501d000100104580c00c100424042c404810402c2c4841000d5008102c65074400c03901d00c030050304413048034134031040c9607004603800a400420040c00d10400c4404580a50401d9000d451198030803018000b00c50321203500d01d0002e44107071002d5442c0106810700542d4503481803203080c898900ba100000307402440346e8003041c0440c2d4018248a20804030900050020000740da0a0307203414504042d4003659170001405034101c4001400001c6282d107100310800040c40001c0200745c0050311420050301402020410b0006040054000501340c00c25104071030450700c00514850185104011190243e66545c0540f040c09003a1403018109103400028142180034550085412000c1c94401d500d2105040d000b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 50659572 1250 50658322 50658367
    0x105040b030c0406140a0c02040b040209040e0304170105010e0c030703110409050412091d060a03140d02010506030736050a06080609030f07080c071802040510080403050301141203 79
    0x2c0d01080c443d485a51400300381b24070124000441c031030129000050030b081d000301c0100e13140280014184114031001c1803d454081c88031550b5a000000d0510850302e080a00e980d0805080b0003c000075070602002c070001c1c0758042c101c3d210302c441c00700001c4c1d1254403903000315078891a02503059850355540d01c11807000d01810b071801c80c1c00c00c0f145050100e03070610440000003240c030b00840c20311161880b0b03542c07145004009002d158101d60403080110110300901240195010b080004101465030150000e00311071011700028401d4110300c80c01c00c10500d440030414400c903031b090003403492043d2042c1d08140d8402c1103400c041800d803c102c10040075181c581e00010031a904103054550320781d21801e985450744941209007444660910044003c01c05000240402c030001c2c000703c0341605d403141c01d03ca5041414030b401d000b0381c0340c00040900150400c20190800f41301142004480d6007416078014006003c140601001d41c102c2009503803040c0d0315581140015050041543ea84044584074000ca480c51001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 50660822 1250 50659572 50659577
    0x204020d0b0f03061909020a0b030f011d040c05090711150a060602060c031f12150b060a0c03030f061d01030b13200114030a0c020f0307020604140105040b030c0406 72
    0x1e0b1001d8103040214145214011040c800c1d15200090b000b0360b401031820240a03030f0810040d01010a0080d4820002c1d40100d50f800c99003601580b40650802000c0450240c20f0302c028243d10a200000d264032900c2400d0322070884048880e0340d0f401c0ca040350072000d444911059441041d00180025040e000513034060700001c5020700009440341b0b416030b607414080d100c08030174010802c0041d039900ca010007403c208081260b1281b050b21b0755908001741461485130f06035107009079102c20104120861181c1d011183c819070302c950802c1c50488015000100c0303054041c0034140c17200b401140003041d95101901920410140600d509981e40590300d000303009000446290810502040d000d2050304490101a40d0000701c100440031800d20900700d40c5480351001d4144580106100d81c03581182003c1c61080381c04180028954890090007442c0c80a0a188000c090300200142c40260300d4047c111000c1c1c9030513004281c410381f28840100c825110300d60154100d401c02105022514507070f03800400440340c0c1c41e03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 50662072 1250 50660822 50660839
    0x90b040b010314071202190e01080303090d0e010c0611040506180918030301030f0c050901030303020d060603150302040b0a030803090a110105030c0a11010b040608070317070807080d090204020d0b 86
    0x200020784d80c1055001d00d070801e6064200c07100c01460001c0c1d003045045140d40b5802101c641d29001d0091407039082c0c01101481e000881001803110080000a5041e40c040c03a0428240080c0300000e08861402c901c0600207a8484000c04005040c030400c8400505010701096503c04010310002d518150240f0682d11074070480d404100b0211001d4601c81e40402307840065441c2d64616650840c070080f031003400702c0c0c10039030012000403142e6035a2103541c000e5000785c0740542e9070007481d0100c4040f42c0c000e801a400741440c0c402c1c6c4500d02d4801e80c4140064079816034000036109819070020f41c1c941d07040d500050900d10004104000020085601070f8214800c100010480781d200c0c1c010b4425002c1242c204110034024407401c030300380344a049804106603412000050a21301000802c0544d00c07142c010b20301e10f9000303800802c10400010214150384c001c0e5111141060881c0d0345140c540c0c450200d001d0800789001c18003a000450070303446036403020b50041c421555805c2802c0b041c005885c040c8825071262055 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 50663322 1250 50662072 50662103
    0x903080f040201090608040507050d11040e071404020f0d0626070308030a0b01030b030a080a020712200303040909050a0b0c12070813020a1d060303040605120703090b040b0103 77
    0xe200c0340c0c00350750b0503110184500c1c00c100007243c1c0148010010b851510400d200003500d0703150030200f0400180160703061804840141c0510041d036400000c03140c0740b1341c08428204050000344500c250720120444016965040034441d1600b140101d004404110b40b524000241c0080c002e1030029244003544240d903489401002c0b610b40760300b41440003800c0180c04000080c0390404940c0400721890301414001201510640400e04c1d200c10400101d4403541c0c00100d58000700c0d0100640b900501e03182d00036a2106010b565020711a403280b01010318140d04040b41c42040d56000e0040e58041d100c0c41c80100302d000505c0c02c0860351400000820f8034294407560101e202d0001c400c0407510007a45650030250f035030b150341000719040b550080c0303200404440c041034840140d5840c600c000007040d2313079000f900002241a200040030000500445e00c658410082005150340020a0700c1c803c04a41d0001005a511044107502514031040c0041110880404010402c030200c0340c214140ea00440c2200c1c40403da = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 50664572 1250 50663322 50663341
    0x5150907050a03080d0504020607060203040f060e0a02010e060a020106240e040209090f04020a05060a03051806010f06050309070512010f060b1c020c010b0612041a0f0606030a09080d090308 83
    0xe9901000d000b41108000c48030100d13105c1c1d081700d40c10900c0540814074101d500d454100480e00103072011035450030000c01500600120380110303000c0303280240190100c0340c50f41d40007070305259402d1b0700c00e4092800810b0009016000303500500083c082d04400000960041501d000040c010024100c0424035142c0d03107030b00b64100f038400e49503c0c02c0054100d041c50b03101d50004240c0c0e6680107004907481407807584042455240c001c05401c2080c0c0540300403881c3d0811400e00c100c14250b007440310125511042c010050303040c2d01e01001c0c04039400da04295a0300d0f100c0001c03e5041040c0c40c1c000941000c542070071240403100c158440403005450810401903551038002500340c901c184202800c10007660f85e51401001080da008010119000000041140381c0401150158000c0001c07951780c50010030802090010781403101915051400c042c15103450b003c00410904031010340320501402c80400010182405035010051554108041c907840300041107a80700a4078009400301c0001d460030300450148074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 50665822 1250 50664572 50664589
    0x20d0f030605150903121303020a0905040f0b070318031e09050102070501210608060f0901090308010303080414010516020d11070b0708040e070207050f180705160515090705 76
    0x100000c1ca80a034203034444662000f69000542ca195146c041c3d01e00c0311740848040700060900701100c51101c2c005501d1801006908445036016840940c2058104000502c0f6280d07000541988481050b201782c980c3d500403001014052112018040f001c0310440500d50800030725080c24040b030b8402c0b003141f04582c50440e51219180305140c0942d0000384103001540c010103108034060b903468500345007074014a03506420346070b013540490b4154104505000d2a0000a4035556010020740028440708d001968001c101007414400034040000b104040b5042042c9070041e01000392101000b400103090680b035000d4010700805541c40944541004103101901030202500480b1403400585640703481c100394400507134844c0744210b40c3c811040002281100c04603020740d01039581d950040400e2401c001c04d0200381c0305c200c43e00c2807041c1000300000c0c500c00f495501859001180340f40c4a501c1d01d1208298032490780a5500c018040d00502d41901218181c00c5601403040e050001283d10303043da80e100380103020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 50667072 1250 50665822 50665829
    0xb15010e0307090e010e01050a150e01060905040504020a170d0206010f0608041401110d02040f0b03010521030d0e0a0b0c1905210403020a0b0f0c09090402040f0606020d0f0306 77
    0x41d0040a0200908010784d80b143d41c1d1a81c4050012400c1860f0802185c21544102e0f8948444c0b6590300800d1800c4405100b0308000e0864000101159414018082c1c8400c030f6510a9134455a112400107045403502412940208004140c603e4003c00d40104a070700c0350081010640140b00e070800001d14032004c0c04001085801c00d8035000d040d900e441e00d400303221030604840c40300c2940d01e580510340c1e1400902d004002000745002c0050316941020781c20413286585a00000348110700303000501103aa90001d101b00c1811810366080303a503950211070603040d402440100844d4500e00094504611404220030271224401e401c9010b141d0b4401e407075200c1034020303032010000241c240802c2401c5240908000d010300d00d0300300700b80800000149142d00b40c040040b602140107801c500c205078200890a10440d4000c05a0080110689000f07000c1800e24024144098400c1e40a070011800303545030740d400346210101520051020b90303240c10005c0d65406003941034000003074242882114292107441103500b913 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 50668322 1250 50667072 50667079
    0x31503120405150705010603140706030c0e1309170d020d0b060a0c200301050703061e030201020303061e13020a0f0c02030a11060d0c091502120a030e0f06040b15010e 73
    0x30350060098120a44c0040c4c00c211a0f540d40e904012010030207441a8082c2010385030010a2024148000142500e00140d628001d000c0c18400491240e511b410703c04400c1c084600d40013a542d883e0b4103046000001d600240821410002103801d20420150002d12001101d08000c2c0301c0107500c40705000c954400c646644002448400c02d500010303210700c2e940c1c058006d484142098403a055070011703085130350a132013103000b00f03980b1882080006206000ca0f0141041c00065018041c40c0d90000703912440002c00f1540705800c015050645190f412140c120004d40141c080c0648002e0684481e000398000d40d5450040344000c0542d10540384150380c03035072015901402901c4a290540e0707440c0d11641001c050aa88014248002c3d1100c40321031003076981d03118240d80c4802c82c0314074000805070340f04254585001103400c112814910f40c10316104030741104101307160004030500050302ca42d040c01d0100251784410f001c0d80e018041401311800d07040d40075541e060700c45c81030340f0250401910000802811144c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 50669572 1250 50668322 50668339
    0x203070b0c07050a1202010501091812050a1209060b01020c0d050d050304061e05100519170a0c080606130218010c2303120c04060207031e0602031503120405 69
    0x60381070140241105522a00071035410b100c0c95501d02c1e010b1411218001d0041c2e54480040100760054014500f428420007070030103201d00c0c171740c840344500001c9443e00c900340800010754510951140f6203802071140707615410092140613281075005054100ca030700d4014451000000c1d00c91034991a00841aa4060300170b1142090404040c1c2d143d0300010800d440c00c66035000c60f8485940310b001c0b0764900c4040c8001c0059039151800900c42e80d509607030412802000c076109200d1103c42807034900d005581c0444100400707030b40d01001031845c280303880c2e00092103201c1840000880400004400740101c20032640c81c0114800b6120000490040108090002d55030b81c40401d42c55004e62030382d80006014103003e086014640c00291840c062090145006500c0060048500e030560b02078580c1051030788103503504c0e061600b98001c2d503459050001420401d0401c40007405520318580c080c010a5001500355140d1810300c14a40b8428001d86860b4080d0140780b107000480c80c4500222815118000e050350b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 50670822 1250 50669572 50669581
    0x20c0d030c170c0f04080d080106020102031306090510091208010602030a09090b0f090903040314060105030706050a11060106031e050c0301120f02041a1809060705071a0a020405040b010203070b 85
    0x221128006040443c1092003040100740e0030072800014400f41c541403008011301e10318a50004d2050205134004011644144140110310460400001d406900100085481d42003402c0040c14512003c2c0418000e0f40341100420420840d00d80804241585480d450140da9840009984a07c00d4030062400101410400e000c00016540034003201c60000e401c205007800c94901040d02940c040c1c50483e0b5030783c000b0504100300805200071100c4074002c00050145545407a0109503110f110303000ea5428800e0215005028074481d81c002c02d03580e40d076171085885959460001030b0007812021400c8011549150101300c0346580e82c007901d40a03090300609685140c0c80c01c10002442409210103c80e405c54400415000d607a450064042c1340c802d10004c10301c0521030008118100c00b05040680c40034001008218801101169482d80300301d075810310540d240c08916041c0d06060b0307542404084911000103106000c41203034082c20a48900341e0b02000156020341c01a0303628001c454008142c0c150480005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 50672072 1250 50670822 50670857
    0x806090c07030903170d060603270803070f0507081306090e090607030c0e0603010b0301050f100206070302090a05031c11070f03020d020411160c0609030203030307030b0102071503020c0d030c 84
    0x85c90349410320303500b4048410415400e40c2c5d183d41c032a0300000d4980c16807560481d82d2503005000134500521810f140c221f550740d4801d0b01d0000401080a01c1010410240d149000b030341115801640b09030115605c0420082c0d00002d90528060017000914240b00801c4038000541068000d0314020000c00495643c81401c4000d003800e2504201004a41d950080c2c0a4560a000e10b000e0705882c010151a0340c1428244840030520390348092217070140b81405e071281030700400d0032a0405468900980c0d2000c15101080085c6029400a50540705001c20491884000074501240c04450790700c120844803040b0712580d840c40c0034000c1d00c000020744041000145422541004982d10140000c181c0511044011341c0541046a0298964030785442c040f081120f21051f14010308040d0038400b000c00e08540220b6030741d010082064051507a00c540d10701550303000300424001460241300001c4c0840030440c2c0200690070502c400a0b042c42101191031000d4064060042114070720342d0b80418030340c040d8401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 50673322 1250 50672072 50672093
    0x30605010b0a1e1101090b06030606030a080a0e1804030203030f0709060f110f0102030903040f05010906120b0a03050f010e01050a0501030206030c0d02121501080906011a0c0708010207030806090c07030903 90
    0x804240494204c0b250350800d400e005000e61140507064450131403820005060074000c0c003c1906100341c01c014418400100c40800b640c84a07182450048907a0361001d02091005074900029081650010108020154004000c43c0704d801070341d10414032070f11040019507581c18180a12404503c3c1000010a51881600025207540c21b02c0c04913061800744400d0b09003280e0007075803414582d410010301841050254841000200301c2031910b20f00291801100420101b40c00451402050f107403400b9414664888a400c8051074016080e601c084083c000b10a0081c10034031100181365003803000042616140d813141c1d82c101c0c4d0b0040c150302d00d0f683d5032100e0141c460b40425210842c1aa090209000c4804164020391007041c2241216180807580750001d002900018003c2e0380652113480140b0403900d015142d6018050b5903001186c17120300300140c490815495400c45032141d8408926201807550064940c0c1c01490300303507034040c0c5648480175a458032380b05e8004c010300400c001080810014103007005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 50674572 1250 50673322 50673377
    0x16050a17030d0501030c031a010b030a05040f14010501061d03030714030c060c0901110105060d080a0e04050a02180d0b07080a0b19031401060609030803060402040b0c07030605010b0a 80
    0x940c0c0c6441c20b240800d0089070802e070400c1e62a000103100600400c104010f680940070320410303540303040d589891a181014400100f00070040c54075080410100300c00382109084099003c084100d03050004d040b0903000308401d104100000d4030b542500040c1103100400c5070000c90004d070185190602e21b4075260000944c2c581c2e410120b110800c00c1c0e0b00e10050600c070850103598044035887d80c0d1914100010034284188010000e164540340c144002680c41d04041441c003540094003d407164a6030600f0746040d0100d810050f0403a050004011203210240d004100061500f901c0f14a00e4010101b0310a0142c94800d005048042c4100400c40107401060200d910048844010405078501d002145100901220610b6181a20002030042010030342c2070980f10301c0b0303903402000240d1500d40e00a14443c000d01c00a030170745400001203602500d658044074054201c070f000444d6200e02800180c1c0d40da800500c800d070340d02d52421300040781455a8208840c040c0016594521004146040082c001c810144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 50675822 1250 50674572 50674619
    0x1b08070c05030a030203030916080613080d020c06061005030708130f02041e0f0506060702040e102301080a020f04020d0b040e0a0b0108070510120207080f07020316050a 74
    0x20016180c1d404016601405109034051512403c000804510704540d00440034000003640d80d040c2b08241d0001803803070744a4203011150b42c036046e4a0500106501c40d040c94540b030305000042d00c0c000c4000010740720b40a07144c00c3e901c0c2c0d070b118107642c0400c8846000581d5904000744143c0c1c003044201400c2c90b045000d442c000c01c40350607102a0f5a000800703e840e000207007100407852414030701c50244648102c6002503a40c10061105240480000d5010300c15540002d2180303586070909600861700300b1210b0903e41d5180c0041140440c002e80c03885100c42e0072024403613140c4101e000864826400b00f50340d00040e038054490b842103103041c01008060f420040020545640c0c401c1c040c18196144e0185001c41d500c5038010341844d82c0d1500704a5801da405810043c55a40007841c200f0107238580614110708074449103041801c000805188501912030751002034080c00e0003003468903c001c6101c00618442d171084007262190f0000c1142134803041814850b4991041040d2402c1200a50984d07542d04a4a8100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 50677072 1250 50675822 50675843
    0xb1003060e0f0c090d0c0b1c1b0f140903070602032805040303030b041404060f0b120c01030c09030c06080f0105030109051209010504030206120f010e040b0a0b0109030812070f1b0807 80
    0x400401340d0980103181000c040040d8142c5490391240c807880303502c40b040754521402d0307414500303040081e1207201d0410b18400bc20040c14510310500515205507411203800500751042e2982c0c80d0002540c0f40c0064102508000f02485401c04150990010790040b10407929a1130034a4a0741c0c800341e00070a91840c5141d00651208401040c1200b6006590300c914452540050704000700d840d1441110480b2904a006100440c01c0050383d04000070380390403009092074081400710140c102226846000d504c010314040c01c02e0b901080c0c858000340041d100d541c11007401d0605a80e240101030a0312a002006412a0400f03d4541412040140184183c0d001810440c0c5001d5407680032880e5640144040841625000180010030340f40c11305041c0180590b0000f01d903181010303210907542c0070001d006c05a8403aa00c010444d40342c0d028440c040000c41d005400540c58040650124040c110304a4519000850300c3c5a0400c2c0c0d10300980c54142c181d146902186a2010241e0390990294080d280c00d03610100b22 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 50678322 1250 50677072 50677079
    0xe04110111030a02100c02071202040504080f04030809100806130e011113050306011d150109090207030507020a0b0415050c0705030703051b060712120b1003060e0f0c090d0c 76
    0x400007083c2400107a401440a000450340c844100c644210841c1c00f150410001042030200e150000c1c908540c044400050325111840c0c94005840b425568216044000c5000020310a84c0e0000d01402082510350799500741205c0c500300d0f0100000c84450780c3c0a9040207401784041c0d40d17030740415a00000003000180d408900d030b100301881e4000c4802c01410311000c0005100303508091100b14010010041462906902c2181703810442100034024041480d41c9010440c080e803180750b101c0024104003400310340e2200241030050281e403100300103a0051801a90018001c4d0840c81111704a840d030101802072700c40f80c00003c94095006d160082c1044c400d5440c0405c2c20794091124400951103040144400d080407441c0441032410760a90b140300b900240144d0380424030b02840d103065401c4a2410541200401c1506d40040c08500d041580003140304038041c09807a010b50050040d2407801e260511a55a0900b40b5a003100f411190039459074414005940756081907070513004424805c0d0900c0500548 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 50679572 1250 50678322 50678357
    0x7030c110a17010f0203060a0b0d0f0504030e0319020609060a0306030203070803030108120a090b0d020706050411040b06030c090103090203031b0607080a0c02070b1602030f030403030311040e041101 87
    0x840d9045220301c4000c1800c44281c408091298a200ca400d046045d811440c203400090200382983c490800984c200049002c0f4505141d0700c400860703494008100710340c0c14241030040041a40001240c000d02c503200b0900d504a00c2c003807080444c25802400e180c078181c041424401e031604010650000e040c1c59220100043e030f030a100000c068038001c00116142e600d403140503841c0403680422446003400801402e5161a84002040300740c42e04c1c000c62640d1a6044a80b042c0244034101000d841c0a14240510041007003002c240c003101c02c01140c09120310074a4604010f40e92105544d45022154100308680165000750003011801c1e000409481c14000c004101640c0807010025a9845030450b1003005020380e00015515000642c80c101044643c60803403020b980c0d0081800b81443c026008200711640280013010703075003035070780c01b030191f5910340000c03441503a0f03980040c001100030a00382000b28081104030420b8400f1904200122442c585582d1104895200c101000d24100a400c08007500360b13a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 50680822 1250 50679572 50679589
    0x603010e04060605090714031b0a03060602010605060a090e06030f06070905011e081b1605100b0105070c0b090102160e060306060405071218020901060c0b010906030807030c11 77
    0xd012082003100340307070074600001202e40c81d40040e4482d04c210700600c0110380c0e000300c0f0100e042510820b07290341c07921502c0b881042000b1200b01d4044600c0001080001258550402c0c0101c846c2a0001d00100383c0700c504010890055600000c001102120200f1000f1500661107030800400303030944100220315920306090002c01c94080c030201b91844010011568440c1c14950600c0e1403801c000b901c040381b581c004150b600050700c81d900042401c0b0758004040c9405d4221101c10174204885810000b00d481c01c0398652004044110415282c41c1200c0419401007046540c441d60180c00700030707111305002d07941c550303070308840709150444c0b1a02c0303150012405640c620300043e005a6515032880e28100c2d08243c41c106005218501403030902041c00856604943c4101544030f9070080490448003050310b00208008011010354411406000040c00d140c1120003601001e001d084140c26603a2a503814000342c5040344001414801e04020711008a48100c144005181c492103414080c88620303800501c244 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 50682072 1250 50680822 50680829
    0x210f0f03011710060b0702040e01110a03060303030b03210706020702060313121e110c0613150c050c040c1101051503010e06040507030201140d0606020109060b0d05070302041a060301 80
    0x64600c1e5072102000a0411288000a102c3da80600005007800d51554260192410013070141d40c440390b07400700d00c00e02900000400e81d036a002c640e4a40024501c003c02a1020384003c1d80468034040e07825140b400c020903c2907103503120220340d580343c0348803114140d001d522402c0151810b40d070030320209006990701030040d4012200900b40ca040081c407401c106040008001124050068100a580030484c201810100725222420b0980141c1d542c00d1400c0e0030701505d151001ea10950005142e800048003c4e610001d0b240425088008090707120402c1c1d6443e20b112101601c20390080d41b2401c2d0901c1d0540001589000c1751600080b40c8035030f06009429940152503008201c00070f045500f00364102481101d04602d08500180500c0c1401d0312001d07105c0b05039001c080d04002c501a00030511420000841d268401d80c000300304801580c03224001e0090002010480340d407800d01c8008440d034074100c04000f000070b0b000000313000701d14a035500308001401c0b0991841c4503035094200c4a0900d1b5a00c0020754000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 50683322 1250 50682072 50682089
    0x60108030910170c0d0204030b0405010f0e2b0903050d020c13060b0304110402070503040824010308090136090b030106061e181214210f0f0301 63
    0x19241c1e038000b08a0040034111000080010082440d80030020414101c1d42101d01c61401d80c3e5142c5074080b40401034815504090807200e081d000b840304000c4154041100041c1084003000030402c40d81020740c494840d5000d441110796947c45502c2d01d62030b07031130100f8419001814440344441d96661240e003403140495000016030070102c2035800c01d0410000140403020446410080941088510381c0d0354000900b0141031400460321088880d2203d6040320f55080e00301045035116a6030b50103681c0c0d215403610805036041d1055a020b0308170050206001d0580342d0110066003040403103c011522a03000250180c080c10441044041d50344403e0001003060004d296444850b6081420b03d40a54800d10640d50207a03242034020842140d01102e05400d06207101c41a144650f10358004945c420094849114120305010703000511202505551303c8883c031444440c000720000c440199100c6c0f501603030307000158110f0081100c0385d5103110020034214540c1030100c0e08120340e0003a51f06031a00240c201042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 50684572 1250 50683322 50683327
    0x60f0309071d07020606120d12091b081507080105040e0c10030213080d0c080f0c010f0b030f0d02191505070201060320060403170c01091b050306040b0c03041406010803 74
    0x1c4240e418421194012025107c1a185c031029001550350343d1318400c111010011414882c8100c0c0600c1d80000b0002038120710111100c0c0280800b6003866186c0748252803180c42802c002c0008510354a2525200d64425202d15401d60318010900c40a04040d40300310219014980758000f199664882541240d03020f544d0042c0c4501800300d202544400603000310080d03a100003400f490842e8444002d0b500c0f10b510403c2c20b07440f05440b0071940f0b0580690b02034820f40b5420070080c88501c14450b0b001c002d003400d04400722409280940794040d1074041d2401c00c0801030f0000414610061403980d0214000c922840310b280e420348125011408841017640c4410050f5102ca03003c01c01e10900210326076920070301340b03140c0c854100c4000029040b03120724403008103030220108040c5e00b40400c2009540013100030500a1081450600d03041c505d64101a00808400b195030801248604001a05522560f0310022800c80307916900b141c144984c03c0100115800000801c00c8584a81c00b844094024412b4078003d64 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 50685822 1250 50684572 50684581
    0x1020c1609060e040206070602090d1401020307080a09111203070206070605010e06121b040b04020d0b12030405090f13021f0f0509031914030f03090705030309060f0309071d 76
    0x1019195943c0c00000f10340110024000965a068101d4800640c01800107a5a030001c0c4e020401ca810782c800040c00042585244850185064000714850b510540d50a25655905000041228a0200c019040c615601d1031003a00b0f080c6100e04101c2054130104a03030800400381e0015006034800c90003241c086403203000421190403c6c00029402c04421640e5000040c0b8040300c496881d883c50b21041c1403400100010426519107034085000400041d1007550760b500714841400142c03040040e102c0c02002d000c541810305079400b01c169016103900400d10000d41c3c8521640042d1203002801c000325400f540b650280050703840c280d401c058407564048050031403040c010054061484245e40c2000d0043c200f01c40c3c000c540d00800c14a0380e02211605096038200c031820140c5100c5501d00301ca104504c0005034a4074601080740141d0720030f100400c1152032031906e6100b4141c4900543d036040da0002000d00c8203a00518130f900c00f451740f02e0300d40c03001c841600359590040050000c9901e4100c94284d000310901 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 50687072 1250 50685822 50685839
    0x10210110c0709111603050702120102120705130302010804020a0e040b0106021903080c030405010f0f150f05091911041202040e060405070603110c0d020c090a0603020d0f02010201020c16 82
    0x51004003c0000100003050b0051843c4689200d01e00380b0b0400d01e07200c041004100740c09001a25202c9401400c80c02c049850316089500139170005080c1140142d0000006102d14030420407a24102c29501c1c02d0000d00303185a00564001d03001070400c987c080606200441c600380613104a61085004003100701295143c0341019051804c025840e2084009118003080030a400c01501c41e0003128048036242d5070703a1641040380c0101800301d54022528240000fa00d4000e200e9003040c02500382c4001760302c0b40c0035690050074452a00521031f0a0700720202d880020f024180b4000503011a80c0d0105012400b411036000c9120f29901a41001416054001510702941018403030502a14054030040c8a44e081c80e4031803982d1681c092046204045d141c42c40c8410402000c8140c0d20181030304c00413500c02000c6004042c0d11600042e207001e018800e8000007a00031070700c601840003166009010070903202100d44a80340302035910003080c2c0c1559002c20a4141182082040150034002031003040461070810340b0741d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 50688322 1250 50687072 50687083
    0x51605040b0f0f071a13020307030f02040b04090b010f0803070519020d081210080604021e03030c0a0b0106082202010f05040e0406090b09031e0d090b04030302030403140406020c0f010210110c 84
    0x440070451081d000300c8006848c00240001038036002071002203882854400580500a6100750a400500b861300150401610380f100506076801550100c3c072058980ca4425501d000315003000d0301603480f81c0b052060742080d40200c02d44850001d0a10b00c0000305648690700d1a6001500d4150b06811110801807901c40f0010200054010240941020301300354002a5038001c0c07108010103803001c0b2a00c0c0d001e2a42d001c0080711180503480b0260b0f040720202e400d040303404503004d02c181b10109004800040000c40c2c2040030b284c1d2045851004940c407030498004444c0c641040b5911802e1143c104004128050855400c0d071040c0d12810011562034280d02d4240741980e000340094080368018854506004041603600311400c900031107240d196041440020090004560058820700303c1e0000e000525a045c2c006521403030098880304020724608820788891b205a1184500503000010481043d2510307210500c5640c40510480b1121050780c07032140115141e9071070541c11200001100c40e1903134000e010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 50689572 1250 50688322 50688331
    0x8030a0206100b03040b070e040609020403060b0907020d0e010909020c0f1501060e150403061b020c0102070f030b07110d110c03031e030a060e040b060301051605040b0f0f071a 77
    0x10110b040e40e2414906000ba0300020704005c140025420001c2c0c40c3c01d01c1a5a02c1c045400020020310070256940740c01e60080d4890b00050b6801401c011090603075050079003d0300e001d21611390050080b48130ba01ca08541080600154a0401200c90350010742c400050002e4800d1011b030201400c2c100308045596842c1600c5843c107541030410308c800420a00f0f030002d002c0154904113072394801d80f9101c1101c02c884240b00d00e4000400b01c0f4601803c07002090248611401080c802e6000c03264460f007d50010380c0d50388882d2240f0880d4140038482400003c540c45800c030780000403828211f10b040307502403000b1b00384030380c9224000005100441c500c42e03c0078200050245114141d0155181030940300e50340c41481202c134207426000c44008007007200c041c59503000c03800600313540150040b03904207072800c002002000c0c0d030030511960070200410384507c00a6140c941d0007070152101d900c0c01d46410302078800f42e040003221065902007400340084401ca601c0041c01c0703007803181038400660075416a02195680c070160 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 50690822 1250 50689572 50689591
    0x90c151107030b0604020903010f0203010e0709090911040b030102070b0403050c0d0806030606040e0a05061e0c03060904020108070c0203100504060e03040b0904020706270c1202030c09100b0408030a0206 89
    0x12010004070b4010742c03c03240c1140c03042e200980d6a44c40040400c0c05400400c4d5454813140c80040002119a0610700c00381c02004a9070762041c0b4030b55180e80d40717400d8a000410143c45c07916220140340c400d1a259008041e500f00c0a0000350401740317103488010f00d0b40d50840d000d40224000140c015080c15040c440b44514074480c0c10304d07007440c6c1803410200f692200000d008500881d0740d20520280c0000401c03184601d694070004443c654540f01c884001039146041c0581c0c504c2d16448080b42034503894105032440340901a100e2803451b1780355001104d4860b4080c040d0418040e4452485016803014446000c42d4004c41e040440e0034181858014129030324170b0103003840d13504240030902c410a403d404844181104660141e1682c1442c00c24000501170b003031251034010385000f0440b458011a81901840501800c20780400307603941c0d0148074111410810083d4107030024607490449140000819401440e00d01001a13981d45680311103250794070a405c154402c1e44013007020783d003499041104035800100d02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 50692072 1250 50690822 50690833
    0x6010912030e030105090a0f02060a090b0a050a03060504050405030703031e1418070e07050a120c020d08161209060615050301080601080d0f05181c030e0a05090705070501090c1511 79
    0x180c4411821002038034000744156400910901d0078cd210300c020201032325811804580d555540c0354041d129500050f03405010078140640000c182c0f900d84907851089401c08080c51401d00f55a80c00c0300206000032260341074030400721203400024000d120714040680c0c1e601c0b6181d00f50901502c2c01300300602c500441c0030654080311050104031040d1811075041415824050784503510b015054030003060f01c5456801c142d00d0004020501d5600250808103414941c030340d113265456207000700d00750b10074950b00480420411038652180021590101040d01d009110004641c0e8941101c40b9544050941c46030000700f020006000926040c060240142000d000400007109403400c040c0c1180340030030b0b04105022012620507e034103a8443c034400e406100a01d85081c4c903090619403024180354200030f50020760141480c0c030403414000348010640d90010501c2d6080c1c1d0b40c111049443e1b5001c0d1a003103541355201c000c0500003503040070001c8042c0200034500504000b020f080203144000c1480c0310b9601c5d502c0b0707 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 50693322 1250 50692072 50692093
    0x605030303040c05060c3c01060806060f010201020403060f140f01030312020a0c02030d1d03010203090712290115050310050f03030c0604050309010806012606010912030e03010509 79
    0x51066010880d28151780c00e035103a01a0b10f40b4603003400c0c0360305a05580c04c800850f400d004880003060b101c5030802404080601e80b070032030122608803212401150000e074020b01c0895450720b05003c094540038414070025140076142d0740d9005c00e851084104c030242a4990216550055580807401e511008002866020b985140c034010b000446051b00d01440940c005011050700b8030844a100c01c06402030203c400c00341181c00028030713104041e16010303c036a0b00c100f050085441c041c02140d018102c440001c260300ba00b030501d036001e034a003c030307a0403103407001e180280b21040ea0100b8108501c2c0d400082100c84250324040e000a07000c82140c144d882081f0342002080500241c1c5a03008060740c00c02c0e1400c10030b41001b000402e286124840102d601c43c443c820410041007000002003000c9c0c503083ea9000d110f910fa60707006541c240d0300e18910302c851803d1049208e41d0329451114480d80b0000514246d10940e6944810348a0140e48070300550005615002d5141282802d000c3c0c00d401001c1c6034028240c8824 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 50694572 1250 50693322 50693333
    0xd0302030403020105032211091008061602030c0d020705090601030c120e01020405150408011d06010e0901060510030b01200a020607060b0402031806090102030103080306090a090c06030f060503030304 88
    0x7550200078140032000c0b01144045060843e0800c9102d000c8241800e2204035007071103044102c0d50300c2114800c1158200080e180b83d044800c01084504507001840075450302c150040c50305246c8107100013184001c0c00121041c07101004034002c10b00d00e0390068610076062005110b00400000c080606250070400c031255102c0e4008042101003001c00c400084160b5296421400b9104941c09180d12583d400c01c07010414044034000c4c412210528000c01c84000f103251a6100c2c1c0010001000342604102c0c01000a404408103071544a41040000036103640c40300c0c00141070380c2002683d4000681d641c3c07106982542c01103c0611034002903400d0407180e5078085001581d030b4070780c03090090054802081d40000c1000c150444003c800c0d0091041d912490b150000d01602d80054100310344034800c500c08503003008010b02c2243d040ea608032003914070b0340d5124414040040e00241c00301c1115982c0c0c0d0386500114120001c03c101504060342e003c6020342c918034614090b11fa06400c298031942081050000148 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 50695822 1250 50694572 50694577
    0x6050d03030c090302101706090f16110a0309140d021005070305091c051509100b0d051c02010b0303040506030f0402060d0c0201140c1e0306030a0c08011a0d030203 72
    0x550514011451242c044000c6802c0d0055a10007500003004403a19081c845d00010700124032003c9a0b4070032000e5845404000340020155103c03002e688404d800700302c0c0d00700070110b510f40c00d65007810500c2d400800e80c482e03607107002180b60b000d40014881100601c2810782c01c00f010142c5038002c40d00150044070703640001c0c5094005110310800d000d80090580101402401130f10494940100951000858a085146502c0e68420200e54070b0040e5240f941100c0c0310010b0f40d03030180a010340148514803000000c400140800c0d580756621542e05090b21000400c10405e882052500501078600221543e001901b51110081180c0c8240c0040c001400a500c1700005d40340c0c4403c41c000c030100310307895500110303916210382000c0502d180c0c104102c4543c81034054101c2d124a05019100303500668501120910502611442480c4600d1181c03c144151a1030b00c00786820000c02001d460115200350740b0443d01c143c07643d1142156945500940414811401102d0303400001580d40d000b0b00715181e9002074a80c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 50697072 1250 50695822 50695849
    0xf0e030705042004081c0f12020a03020702060c0f1e030d0b040603020d0f0201081803090f04150e01080705180a0e030d0222090615030b03010b0405010f090c030605 72
    0x20755a0701c031640c030082100d92403c3c80b0001c89600c0c0690355074031000302d6501d42101c0c0010032884083c03410300007501e902c00c01c60298100925690480315000c50f41c3d024010350b01001a0000b019000d100340f50160751a5801019400c0d601c01c01020900074411042d820102c40410700768141d540c4d104e08280b03e41300170085400c55900150000741048030940028010324098002942020321200a40200f02402c00c16040da54006d88809003255103413650031030700b912155850300c800c0d0424400c40c0b82d00c1c20115100285188010404500640490840b00c42e0b00d006500807075083e07022000401c0464030500508010b8601550005c2c00b080c807410407040b80c06c1024090701c081e5030352070400c406005030500c103803a510000c01200355994603510540075041224403600d95102c22204da03000800205500c02c2104039000368140401020300c0d86400c0d4000d020090065806548410860038269160f10413107000c2e025030140c00254505203000441124150076000c0c040c14a4114184210350710920860302d803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 50698322 1250 50697072 50697079
    0x201020a020a030c1a0906010306051f050405100302060c010b040e0c091810020307030b090709060e04090602070602040807031a0405071502031201060801080d0903020d03051608031302010f0e030705 87
    0x2000760b4606170035440d400907144240780741c15506012003000081130b001d0480303006443c10b001c1d98480c0940704009203000e030101036060034039410411081c149a00082e500104a201002580c1e0360ba170041045503000120303a9080365510440141c0603e441c1c40381417501d01e160390040c015458175101107814a040500001446951144a0500740804000050f0a110881e6056489003406400030b80648050707410584281d0100c0d00280300c1c07502c1440b080303003110301c2035a40d24880110b0b00180f04c010920500142c0c1c40b90f8080000d0008100d490006200414915009100e41459414000041241d460380d2155820051040c000402e80004008044e9403202282841415000605a10354803d0325410000c00d044d0100005a0302d4018143c94100c48005040c1d03017269070700c52400c4400003640e00000703602c550030088a01c003180c030400c042c01a260b84840d40001007441511081919003044900c0303802c45055070081000c43d64007203001980448241040d0001c1c0042000080c0c9401d01401210300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 50699572 1250 50698322 50698337
    0x50904061104081009120203030907060509040204170d030501170607141c060302030d0203040b04120302030c06041b14011d0102030d06080304050a0f060c080d0209100e040c0201020a020a03 83
    0x3500c1d00740400315002400400100c9283d900c400802c0c00107000c50800a490540e204d041c0701a103e4004400c484c46000d01c00050101c40f414410280e4258103c0742d5003a400650034130001c90f10600d01c441014900c40300c240140b00c1134424140c01410344005030080c51100c000d041c956a10000d0009800d90459840d09084511121801d01c5180078001e1601b0101d840c400e2031050b601e00c400b140e1101040ea8003d6042d111040121602a80c7c5c038451031240c0f036814241084104242c40c103001c0345c4000c4601c68411740c2c0c98154410303840c1c0c2c076100f400c1c0d03030070360b4230101a0000c1d521408051143c04000c10740d007840100034030101400600030303148001d0b00b43e24031007801c4003a01c0940c0c4280203e413402511144100b08158540440075507035005401f500c0d024446100300814400d1014041300b04940c4295509103c89005a80e07061050f00b28241c060030300c9409200d80032460780c2d91040020006481c0d80c1da03e0064a040040006641d0104200000d41e4810403803004042e0380400c203480340c140c05040421 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 50700822 1250 50699572 50699591
    0x2040e101a21160f0810051908010908040609050a0b0406120e06010602030a120b09040206070302030c01020f03070e0103051504090203030f030a1b08100330050d1505090406 76
    0xc036800c2d840c512000c90035000c40108009410441c4010901d0352070759880d04007200c11000150b981ca43c0684902c2c4039481200800c000a192880b25255050207100c0200076065944003a0f0782903451010301111a9103000c1801c1c4217441e0b102407408000d0401b01c8601181c64540a28406a44582e0040d90100300344035800400706a0141c100d483c0e0f40041100329040ca694441300207440e500a081490001420361588004920050044180781d2800510710700300c3d501e40360b0800802d6400440d0807800d50009009a15401c0c000b84040c0c11f503031034001d00e1f0350b9a0f880e11260007840c42107180859810315140c017041c0a048141901000320840060301d00154000b40c0c0e0000900e14020642c86004d401c41c00010400b00000c107400000402c04003141c0900c0e50340e0041c0c41070b2003108049803a00c0300140c802004002159008408100c440c641d41034a4262028580d181c1e10b19007807040101c40800c4000600c0c84000303c162042400c8440424110540c50b0300344000035100541c0904054641912010040d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 50702072 1250 50700822 50700847
    0x1f05030406021b0d050c010b010c0b06090603100e011a03010903080a0b0a03140a0b01290307051b06040203070f080705310603050c04020702060304020d110d0602040e101a 75
    0x50f65074a6042140c03491694400000c10a80c00699180346950a04a1000c7c0035400f81c00e81071209a401a0700391081c2da280020702c828254020101a810b109a6003d03495103d00c51192002c141000c00c004510040da1083d0f9828506c010b400c4a0700a030314100140e004298030607c1c141c0c114a01340340214ac086611000141040120780020f0001c10444c190281400310004544080381e1007842d051070306030b076156003850000c080889012503201034002202622200d010045600c5841801c100e0b052510700600d24003460882c02140c0d003507a000c42d00384000d44c0b80400801d4001c0040c540c410244c2c41c2001051343d224021031007840d015151300c1d031580b5841421815640000210710b880d540ea40c0c00c0300c623015000b030706091005841d2401440000805418540211003c0300d40140c4240d00d5602c859080c03003035a111080007a99040034840700002c50341d0790643c00b040280e00452005d40c4490a0240321400080041c1201810400c0003004100c160b04004601c10f441d9005844542c0791907013580320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 50703322 1250 50702072 50702107
    0x5070c050d140405150d0501090e030a1209170a031d071701020c0d02060a0605030a030f0804050f061602060f04020f090a06080d0306080606010e0901150c02060c010603021f0503040602 81
    0xa0303503c00d005100040905d003aa001401c1c45c818080c0060145036078488200e0200c0d50102d0b0324540f65001040019011400781c0981030540350650b10000c2d50500304c0e16000030110400842d580480c1002070100a010f515008040303a0002d0b03040d0152022945442c8180c2d950100d101b001444002c0c80d01d02c0204c00000e6040ea00440591000e0f00c4614600f290000d489240482e0008080c43c60418042824240040d103090143c0d03058035000d84440d1315490950744000003c200719214843c203824188200703030622009010700c040c0801c0f40e950306844080681484402080010540046010000580d4910200c200b010200b541c00e540292184481400a070410742c01001c01481041550f83e1681e501d503010204484a040c00c1e91195144c4100466502e04901807142d480601000180b1116a0307071400c40d80d0101c0b150610b0906002240d000c84c620790810812501c1a0350f41e80e00400950034216030303000900c000c003180402805450799001d006408080d001a00c01a40440c25034000c0d10046071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 50704572 1250 50703322 50703329
    0x9040b040f0903020f0d0504030519060f0c0f0908010e0c090c040320040c021f020c0102120c0304050f030307020d081e0412030f020703020c0f010302040f0b0304050105070c050d1404 80
    0x1e0501c0495070a00300a591018020010002c0388208000b0110036481481941c098942c4030024124458100d152080c4d0741c00e40076400e407980b6940d003105824a910340d12500c6811012602c9100e030240121030050b101224580c0510302690400c4a20031841b00702282c10b041c0e0700812140d65440703880e500e00809035800785d50401070090b050740502d03902c0c110610003078010303580c022a400e00051041840481e260680303603241040754480d4200c00605080c068000d015031085120005060031a074102000c1e10312015034000d15070200020074481800703010b04c25580a030200c0c1300158070790f0400706402955148013035504010800240086a20755440f4440100ca0080f0320f10691014280790a04c015074119031003000d4003107072605110b940400400d000340c4d18050b030103402804550b504c10092003181e071511400c071410942d0800010840300b00d950b0030b20000d8040034105640f80d251030300e0a14210b400c027400c4c0c5000c0c03102d1098003070b0006a00180c44981c520f040d02d003600f41e01036107a905d00c810740555007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 50705822 1250 50704572 50704601
    0x19020f062a06040501290d17040b09030706030c0507030507020d0209070509040c03060803040902030a06050402070302100c02010204030f1209080d0f08010509040803010e1009060609080c041109040b04 88
    0x1e0421404940010180c1c000c501500c001c001d40c1c202580700c90003071441400031842c0341144102a85251402840d04240c1c54010300c42582c06450030209002d10307611a801011b9400d10106640080c1c3c1020030900c4090985810704214a00301800301038054060310703d0080410000141d42411522101020200e5a034040d100c052681814540905143c0042d09414007070380c6405800c4c000756100e80a45002c8030b0078035001d949018144510100a980b000f0104c3d80580d4903200001166140e42c4020b12009000754040d040c0b6111000100c015100001d01181c01c5a00501003030021401c40194401d8155216a00d0b40c13000340441303000d9075141035541c001501800768040507100d85400540c10313000041541e03214136250381c8420800c1101001640c000c4c0290390240014040580a51440368015022118210500740d464001000b0340d035994001c03000250481108000031681003040d030f040c00d0401c45052210640c0000f480410f8010103095601c00c5440324101c402940f42e0754130038140042801c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 50707072 1250 50705822 50705887
    0x4081f020903160e06040c050a0c020303160f0302060c120c07030c021009050a0905011503020306031609150509061e0411031005011407110d031b060e19020f06 70
    0x483e180ca02d40790841c45800c49290b04240010954a80362142031410300a9032a8507040c4840514215860030349004c0072030301403104103c070b1120aa00319410802c082c0c031801d40580b4400e1245030013410a0340142c03200074014010b101d01c11a442000d00b034290720040c0c0c2460542c45030703024101110350300c0d040c40d0017a40000f006180941141d5205942405a40c0c0560f880300c00203940783d080d141110700902c21a001e00101684800d6a58841d800450304204000e0440d2804100d2880c0c0a40c1200c1c0c84d48000721180d683c0340074003209031503440044002c060458400640703240c000080340d000960225507079440d041c0e0040000040d5941d9100f0891850410300294a03850041c560400306030040c01070b1804150000801e0101d00b03902812240340c140d000303414541000051082c400c00c0e03505410200c0a0000035541e0302d00e414070908c2d400c100d003802204c0126503c9503c4105a081110040b1705000ba03024200c071039005030700c8031030b800740e51a0810380b2865524031504104041e2850242c18000100070003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 50708322 1250 50707072 50707093
    0x3021009090e06060a30060b030d08060306010f050d0b0a0f0c0c0c0503010207020618180c03060f030319050d0b0312030a051e0604021b1c0801090204081f020903 71
    0x48042c402c4c0416100e510116480d10442c4075440c8002000014025080c1070b034040c0d59803094a01c0c40170a00c0768402085c60407404000034280383c01d00c03007034400007841e490130044030b450100405401000c5200035400482c6c1800c0120301e855401c1103014001060880102c6c00c402116407041034550b00100f805c01c80410892002404200860f03010303103c0840d140008109849c1c1031088840f0b555005000501d0f100c024041e219144107025100d81d4440c0038041050051b40c030441550b071040c0700101005036203280c0070b401c0020312021b0300301c554007a610a0000111510f00150500e051380f0035410f000b921643c512510030b014020074012143c00d800756030302c05122100c07400003450140c00c038100103100b107503a080f034031200001740c844070140f0050ba10001320b901c505107030f030080c003510700e04402c4c0c40041801750325800d10384040302455042c52121584007003c4281d100c00644c1c0940f484042c15481d00d032400c0050b95590718898100c0100183e034001c014048001035040300c004810103020751f03044510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 50709572 1250 50708322 50708351
    0x70203071a0d11030f0402010f020a05120403150501050f0f0301110703030e0d02030310232d061908130b040303020a0e040c121d0102070b0603160303090302100909 72
    0x200e914a10014180f82c40c80c0b80c078140a000780c81c441e406442040c9516610b42d00110b407051f0070540500c0c19130050600b0316000c12400c3c4180c0780c1804208a401d503503946540340c41601184031802c9411700a241c0001480b5940c3c400950802011046500c801d00d003480700002401040300c501003003614100051880101501900304111020022081d41d400380351842003a43c40384803ca8050603004200802031120401139461020f1014807100552544486400410240e804032801482c29550601c1c2d002d0b10401011955450750009580a03800c0640d01d820011441c0716050118040c02141d50014546802c01464400718640011011043d03003414140a0000e40c01128941c0c0040c2940c000c1d501c043c1042c0c01094141c1e482eaa270340f04400411f840f0050014030241301c10701d140311001422801075131001d001810740c81d0700800a10900d130404104140c9880750040c852110801146020800b00346c21242c0300048039010307112032901d1402203100711004001034203d4292140362546880c01041d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 50710822 1250 50709572 50709577
    0xc040f15090c08060a0f1e05030f0718110909060303160606080606011e0305070513061d01110607120207080403050a0c050108090705150405151201050411070305070203071a 76
    0x2c0b09a140d00b00c50780c5840c070038095103004502480e040b041060000f082449400c0c06600c1008101405d100c18898585000905003a0001c00b89100f542c4420400d2118004030840c100c1c203581110000c100c0c800c10010503515a0051031180e9200703460890019403181c4040c000c403491640c400c1c00880906c085440d0100050410740074034455482000e0002e01a5405500d0303900d0745c038642c0d003900800c070202850b089014140c000d01500403c00140802810802c01c1c481e80d80207040c0c40d07101c14609140b082c90300031080b42e03860031042c10002c2d03802180c3e081840c007141031a0440305a203011082224808c942c00080d121303441e40103011403000103001061140c00304140768600e11452546429640e680011a500002070b501c5400d01d030040c501c104540e142c078070419a0b070900405215070409030b5a10000b170200781c10f401c41641035840041c10b02208912001000d000d44811101003000c071380354601c001001c4c0242c02c1c00400340a000503030f050a5540070000c040c02002c0704509030510030003580c00c3c0521074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 50712072 1250 50710822 50710841
    0x102041706010603050103030c0821070504090b0a03120f020a0804090501060206160905190f03081b011406040203041a040c0512030403021f11120415020f0c040f1509 73
    0x5000d00c100100f4564800d0141034101d94142d40e8400c3c174601e031030320b40c201c0540c80554040264030455000c6c50341420550040da10036400c54441585440c50800d242c0c040d600d84d0100c3c6071003030500c0d40050000800740640c1002000151900018509a2503402d9281c00b0400380c1c0035146050201e40080e00b00b000f0b800081c182c8480ba420f4032440d44640e0110320140c0180030a0b00c0c04941c240c0814890b905100450380d5418040c82190701c0f1090f0380d01000a0420120f40080d500d000001800c824103000500d4481c020403440030017040380c04040c0381c0c00203800d00041d11680c42a0307000400700f030134040003840c0d90b000e070449901c03c07512900781807800b0368100310030b403040b14000c035110721740512420004001c0c0e5040300d030058800d0032400c1d070030030307440742d68001080603102031000e008000002800200700190819a03840030a999030303418203d05505104a82042a0031540120240080b242d404109514480003d44020595804604016020300082c0c1e0340382a41a0250b00009000b03029604040c04d003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 50713322 1250 50712072 50712119
    0x5031f091a01030b010c110f0d060912050a121a030d02070905060d080f030a02070c0e010305070e01180c021f020301051509031f09060903050a09060306050f0f040e010204 75
    0x10060000c1c01542550500d400060108203140249800304031001d28924450f01d00a20540c0410000320001c0d0954542100607104965114030400c100003005d0031b00d603410401420f0207400c0444004000f0003403410203141294090b158602004c60719110000006460340050940703a50440b60a002559039080d03108400c100b07400c02c000706003941040c18110740303c0c40c2c00204552510700d1001000c09958005481d0344502a0b00f003255034080780d00c3e0784108016291012900ea0154514103000781f234903640d504103242898291004010010b4030311080d182000f05100081010120040c7c1a418800c0040010001312078540c000842850f4550085050f1381c411541c5082403400c1c42c06405060041c0307203000742c052340314000e05500c03c9218810440d070140c00e914046482c0c0080d40da4503054404e1414100c011601c04a048100d8a4105101002a040e02e14041000c2441c00000902150b41103810a0190403151100d44050311035420990b00f90311000007c0d9903903139642c510003d40002280e940d541 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 50714572 1250 50713322 50713361
    0x108030c0709020a0509060903030d1b03050a020a0804060c0e0613170a0327080a0c0303030f05060a05010e0a03080a091706010605070602031e04060506030705040e0303040305031f09 80
    0x610303030300520030713034004403141d40da5142071400c40300900074140c0c449004e01e640b521040c0f05803480c1000d98011845c0e00319251a01d003041c160319100c040d041d9200a0b1038036100c1070040c84044241503024202c0c991081d000040898011148201070303444a09220145400001c0040c080500180e50b484a80465640504004800803100c0300c240e1181e2142c1d070700a00140d140c05103002012110720a45129801810011541560310540c55103021165601224100b440c440100700381a09031103411041c86203c842481585000c000040c003040c000c4c05562305002c071007480070006468500103000a1a8070050040d55220789200150010180748240e03041d011510106280c00c83c4003141c030b01d0484e111030319000d0800c400c0740c3d500c1000e904003e0080000c0890022040c041513845100769000f14020f0a0000c0c01e801d18900f410704008041e044240594244420f440c0b001200100300c80d070180d05880c0c030903101d40f6070304844002d01301c40800c0c0060b05c0d400b1210101d01c1e034100e07a010000c5060780c0b041c01305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 50715822 1250 50714572 50714579
    0x409210f020708030c030a140409020406081905040f03050c030906030f040209180d050d020705030a030c140403020d1119030b06100908100906020d14060a090209060a030c030b06030108030c07 84
    0x50384ca01c2182011400e40c0c1042c84024142402480064000051903401a00b0701c0e454601c20422a0031a0784014001503a00e07062000b082d01c1c405095820502c204004d00962a00d81c0720b2801b4054030f100000c00304000052005080602070050b40c20500009007800c4d0b50381000030000c50307101c1d8140e83c20380c03160350b41c0004074610346e4405040789200034480014010356402e5500913103254000f08000d8040d04e80030460f9100244084c4018024980185c400013004541408002c0c4403200303403001920908010802400585c1c0e84a000c1c003411580001c003507009400c02008a94580c0403945404403c585000f004401c2280141400c1d02c194800d84036220b08040240c804c07201d1350060320412425800a65602c00c1440d20368100101071801404007502d0310000360311944c00c0b5180418200068000740c002d1103002e1a000000c80010f041c059025800c000c2000d00140243c400d0f05200d000341541c5e0008220414029048804000703002404a0b8032580d60b104002d407242d00c003c1c9016a58043c2540c0130 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 50717072 1250 50715822 50715839
    0xa090f0e0f0a14070b03040b070207170c041a03030f040602012f070501091e050106090b0105160c0803070b0f0f0121051609020415080402010e0409210f0207 69
    0x101c0c1c01d18000402070401050603111058100300d400d4a0040d41d0184a0002c5200c521420007117001e184a070307211106510300104001d090803c1030700002003509945203c1003816400184c030587c5ca071170032500010900d100003c1440c040610710680d0341c150001042228890050760080e20803100540c000b400034101c40c29000616601e131242046445244908c042049031406001c0d0680700c0c450400000c29510b181c44010500c02c42c2d421091208140c0c0c1203e500300142070140c81d00a00000506002030010100003034068052011001c41c911030094180050000c200b510000400040d403c2c2d941c0d41015082000200300200d800c81350b141011008294400306840401c2e0407600410150b08091403980c0c483d800f03102079100d01765007078420180420b04c425000d900709402418401001a41c4601c0d04445040d0414039540300c50502409108100c0580d0300418407500c0d4590481c0e000848000510780072221140c050030b10070311503001c3c0c800603204036001510030190b1201034086503d86651030204 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 50718322 1250 50717072 50717083
    0xf0b102304050603160201020c0a1212050c160302160b041a09091b0408061003120f0e0409030306030807060504021203270409050307050115061412070207050a090f0e 73
    0x240b54029504000081e07051503054103a02228805100240c50501554000e918000420000340c0c0c02208802e2214030494000110a501c12801d12040c0000d1a110716500c403980500c04600b41c24040c4070a41400b014400d0000d041c540800c0002e01c054035460345600d06103504203000c0d091139808140c0c0e008004075002810b5a503016401411040c440e922003c855000e06960010f94201c10014000842c03400800d0040314401c0d000c1094010f4002d1075803d00c00401d48060341c10710b0910000809100c01d40380c0c01841003040f0359040c0c4000ca14880d8616080300140b41d5503001602071040400c03908100442604070310300172402185c0c440b240012116040351644107000304503a00710202000b05842c281108106a41070300c00520000c0c049002d03441e458155805040300325861b95481d0100d00c5001e069004c071002800c2285492082d044e004000007100b44140200004001140c0000905880c0308001e5500036280180c4001e80507a990045c52010b003003142d450a6155040414045206078006503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 50719428 1106 50718322 50718329
    0x1e0318241206010f08010b0a05070b07050702030f1212090304030605041b270518071701141015030905010504080a0e0f03100f0b102304 60
    0x4030700c860400412060502401d220320144055001002d40c0c1582c006c6100d441c1c1d070384c0030501c064a8502a5020040110301d08204001d025540480a40340140c403d40446104d801441902a1150611744150003c0b120510407151050310300e01c01380b90400d41c0c42081e6071900740c481e01d4400948100f04c90541d01c090702d130f000440c02d00800150f2000140111015000340ba412440d804043e40f00da01da2001c4a00c0d110400706020064107000307085140c03180012505030540d03810290340b41480800a801d5035504e00b030f45a548004188011034810382e52810004803141c24083d120302070aa0400500e03081540c0c0b0f800f410300241091003454007650141010b1030311158000c100404c0d925907141c1030b0b40509070000d004000f039100055a101c01c0da0000340003180c41d80c42c0c118900002c004032100315900c0342c12121141d0b15182c00c24085148034001000400d451a50250079850320300c942d20 = true := by decide +kernel

theorem cover : BRFrame.Cov 50539572 50719428 := by
  have h0 := BRFrame.cov_init 50539572
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 50539572 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 50539572 ≤ n) (h2 : n < 50719428) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
