-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4677
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:22:57.468024+00:00
-- url     : https://prove2.me/submissions/7ac4779d-3fb2-4ed5-9d7c-fbaf02bb8bba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 841007194 ≤ n < 841187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 841008444 1250 841007194 841007197
    0xd0b04050601090c14070311031c0609050106021f02090a0b1801020114070e010e130c0305070912030507140111040308030603280f080d0207061d060601080f0405010b15 74
    0xa8910a44c3c5813010031803c0710f1217121510001004150654a080d4050f1030031a441a085120062076000801910007081510700a0200c0302c20000d0010820520340740c10401259016408101503400000c7e4200c9041c1804c0c4c10750a085884000c0140c552044c000441c0c4c221025412108a034180010f20300101d0200240c3d6000c180f109a00a0101414460304038a0f008010b94216001c103001d51020005036010b20284044801c0182030720989402c2c0341840800e035005540c001c000f00780e451080c06103080e4441e0380580604030160780d0011900007550020720f03a10500001510032240411914100d04081d00403c0520100e4480d4a0711580c803410300c01c000303a000740c869501c02d2242c25110074030415200c101a0003041c2c42407503c0011034a079110240d001015100c1107038002000c0106840b0078910707101a092140c0181c10001c0e140e40482c135000040c00c484012000d965003c10304028043e80d1000ca8541c2c40405e040c980007941d2214a0803501500142c010181d1207030340360958000502180c0b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 841009694 1250 841008444 841008449
    0x7050d03030b1903020d03080402030c060406031407180911130e01060e15120702010609110c07080c10050a050d020301091a2409010c02060408030c070618140d0b04050601 75
    0xb03e40030201890007040c0c051490b49444000d400040c401b00300000f10340146107055001b40090140e031084890b030713400204c099000c0d40000380402d0380c4007924455202850401548803249007030080b1481b990100c46601c03542c2034401c003000d0302c3d115002402490b501806850100e5010444505600d40310004016003034024004c80b0002002021022a41e24040f90b40c0d071400c900041100f45045414111942541c400520780c405541d25030100103501c046600c40c80c46843e181600c059200c2900300000c40c01d0544a0344203d003c0d505ca8903590704c40342e5445400581c0d648035070034040d42d00d81c2c00580031b85050081d050004102031010000041008440e0460350360f940c040d08403407a1101d2001c0c200302403900000c140c41c600c11180c00202488440710001000c00040504000080201603400202141c0c010307001241e0540002c02d0f1110000c01c100540c0e000780c145805c0c820341651030381004d0680c0900d14407440e01d1810810004920030f882d80c200304004540c000c3c100e20124a45814044d994040a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 841010944 1250 841009694 841009699
    0xb01080f010c05040504391b1e14010606031b11070303260411121f23180f070b030c070302010605061b06060d0201021e07050d03030b 59
    0x441100d2803044040c440d06461802075224076080c40d082805001c001d0a400e08400d070781030501e940c00d14240080d24075a851941010300c0443c00c01ca0040001484e02c0c0d050719410b03944445603d40c100018880e001500841c1c6803045003111030180c981840d5005c48203c07482c50100b5481c0000100e0b0056140c1c000d62118000501c0c5400c1c00560300c030041b078160902c1c4071a02d0b0190030000c02030001921900c00104001c0481c040e030150303c84202900c50001d08160b80446e00e04004800c01c0c21182030821030300c0111024180540300b1610400d4030b040701c404002a500383ca455895444030160310760382c01c0d104465484184041203510f880c8850540c1c04074524182c00140c032405400e51542d00c1c000550340c003558120701400e425a02c41c00506030154002d0403084083d95220301d13001c515500d40001500c030305030502201455a10401c40e030103040074406004c04c3e002c0e04540c0d54aa0150360000b4030b50500c0c522803208031800314181c2820300e04000403034001a91000d0304d01c1403842403503819003250301002d504 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 841012194 1250 841010944 841010953
    0xc0909060403090b030c03070315090e0a1103010b0307090905011409030909180a031422090605091e060a05030d09140301020a0f11070e0f010603053105030c03070b0108 74
    0x8131308800f4120301044070a00c412000820000364100d20030f4101103c240200c800c03101c11591986600c00603584003007a6280d80c1c0e801704500800380306021003401000301058000300030012200c0c0201c1e4880380079004101a47c0d1300d41e0b52803020450254401d41050245081025403820204080754480e0b2084a0040c41140da110109030750901a001c02c4920f5202000200000c8070720ba50207070703901c180d0000d9503910f604040c0720400034005004070150902c209144640682410000c14004440990700f1144c0241c10130307000c102d0940c0704c0001d0503503410000d042103045039441e50006001e050090704260f4043c000c0800d40c07440990801c0c444000e49407030103001244040d030f403014103080340604138460740054080b03149d08040e14000c02c0c51400304111203094030303509070b2660740910240b00e00b5100a000d012599004100c80d82d410320456820042014241a40a071003e1300046150100000c852044015044e954100a810070413210811074800940e034a91006040170218606c0901c20b98815004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 841013444 1250 841012194 841012199
    0x26120304120e10200d0503061005070209150d05010608030910020a050a1205160804090c020a330e03040314121e09060705100b04020408060c09030c090906040309 71
    0x180c8038051103040701510303c40d848442c1c5a0201d80b004c2101d1a1a15411014843c1c91a86102403080340c81d00c841d60340700c5913528104042402020350340c4c050003808002007801443d005a03201325149811444114500300c0d400d242c940000c9a00c410010b0003400c030b6281800003e018000400640345014080759409490509580207036125440d2160003002da41200c1c105d01e00041481c1d2104104000924009091060401c0880800c003201c3c1010303520184003107001c2080c60298000d0850b81c0c1c01910280c6000c004507a280d0080ea210800046418181d60b40c0c04800c1c441060341c4a5040140d4007824000e5412a080e0640c507940640820b030f44095074803560750048003000078640c06a00c0c030321100f01e241049901c4c0502c01620500422610400c081016852603611180a00505805000078051206002400341c040310303c0502003600450061004002211000c140603074041d04031608240d465401600190a0030410950a503121520005102e1283da0005c1da09100d40d101c1d071241b02c100358 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 841014694 1250 841013444 841013447
    0x213030204050618132a0801200304060f0e0703060902030c0a211a010e0f07020105060105040504050c070b041a010504020909042a08010225030203042612030412 71
    0x300c02c000210345070348109005c0f07002d06a00e00c0d000d0600b03070301881c9103c9580c400c40600c1c034901d411010b000b80c0140000142031001203130a1050f40025403640300e00e1007c034040c0a595441c5408000c00140100f956050941000003044c0c0180762280c4040d01a42d09590302c9280c4030000300b82d0040184d01a206072818104241806420781050728881c1d2070190016680312070348409040c641800700e44600d09201c548010300b0031a04903a001e00b01c02120040549814011110b0088006095004582c104428032840b41d030000102d4080d0b42041d40c0124155a81100046282c8a40c81c0700600c05000c4400f04001d1210b070341ca2007504104c51903840743c45640e850082105078060a20115440740250004ca40000c00f440450340480b0400d00030031300d2603024240c188003400b031141c1c40f60100c1d135000a0006210511510150440c400ba401005850801610025503900450203500c0039110302c0c58049014044c0700c2d2a0004c210300340800c07910048000704002045401c16a4101c0386a40441110760712607 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 841015944 1250 841014694 841014709
    0xc0e03060106021f090206030a020a020c01080f16090b03100302010f051e090f1302090301060b270607080d0c090608040b04200303130303021911210102130302040506 73
    0x260100c0c1d00820b01002160601200c3d11502c007059401301d03598008800042e1600e0001d5071040212007801a214440012b0207030900080724016410800c84608101c110399414154079040720306000c0a100644018406580c0000c00c0d400c4121102c001008010f5280c558421520a8034402c1c2d840c41080d400d845c505031024024100405100822620f0303d8209101c540054003103102c1c0207000484502c000d5000c1074054143c0e0f0000c02c2015000106280241800d0081d80000c0164101c4d540c500714160050030600403042e80c4900103050500000031b00c0c0d68030142036581080e0007080650b03403031000940c464000e100e80c800714030114000c0000010981d01440c060392159400c91110002642c1e183d8900010300b250305415074150320742e220820320584080018000040409080385001400d40c1006454407030440c084121072021000101c0021b80e649a82100c1000146c0e60003064801c0ca401d0281514104182e841d410340c804107030922011003104000040f28000da80400c09601c5540038090741 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 841017194 1250 841015944 841015949
    0xc0c0120300109020d0204090216020a140f0646090b0714011e091e05032b050a050a0b1203120a0905030a020706170f0c0318010e010c0e030601 63
    0x69401000040140402d1900205401c1702a07800042c509900c400000c03040340c0144108020b482c40e800c80b07010450610441c400080c114281c030100f002500c0342c00003403024001c0c2e49414054071011074607024611a10716030000310911440900c910b5410304072071515510501c401200c0003480c2c0003041813100d0250b0b07131102c1640c00411103145800e600762208254195003010b6209a9035943d5024100c00a51414030306420740300030300201c0d031841141400d62180401d61f01540403a16010307118800180000122024103644c0b031495000500c0088031120040000c00750664401d04200810524000580c00588900346e401350400040443d1024440e001400c562107034480e61042080c41101b0703a2440501d03501403025803000ca81480169110360540d084849000096403080f00203000703007600002440c00810351003202005030700d060301c1c10114401009d4010b02503080c000003c95100e2240e01203c0030b8900c038000c0240f0041c900a00340d0b078000d10080e108400010044a540c030307401d02d00490351604 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 841018444 1250 841017194 841017277
    0x2090418150b01090e15040501090b01021c08011203300e06060907050c07081606090e13020621041101020f0f070501142104020a1205060c0c0120 64
    0x3011810b180c00c3ca0a05d80d0040d00401000300300c1040c1540d990344031b00806020b441a204045107411071440060b10300040781c1c4d15800342404560b20101202d6010300068119001500410800409404c00341c460181103003001c0b0b190316101d0742099100d003c1b269101c90040000d10100800000401c060307880d05001d840d80c40d400f03600c54021400c0300b0701c5203010340707295403012054804165861910510340841d800c0c03120801c40700f58104004098004042e5802000c1400f144141440c00c1c0c0c0c244010303aa4070b900300a124880100300c258013140d28480700f01101c07000407900f022604080c00c3c13109461490941243c014850384030580654800411680300854415004001680c1071400651302843c070f03001c1c5584021810300842d660071190401621820340400c4490401c0d050600510440b805280c11240300d10200641c9400054000621140c0c442c441d024217035151807014007200d000d001d190315030114081d0403441e07600440000f1320003070001c0c0007880340c20317825489240616503110034004038002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 841019694 1250 841018444 841018457
    0x9050f120315222f093a0b1006020a11060a03022122030815010e0907030c02060114060706150f030503040e060301050f2a03190606020f030a030f02090418150b01 71
    0x8054100714801c2080f0341d8441b40003100050000040d190910007100401e0f95144116028402840c04044100780a4216413000c2c1510302810384030112806000200c5a000d91000198480318a109a040d10180d04c1c0300214590010740e00803200e104420166002c0440f104011401d455070180d80050041099040e161700c01140d880d220900a04800c5d038402d00d0510013884001c00003941c82d0024103106104a4900107000c0420f80380003464a007050f0440e21310210049078401c0e5a60700d800580d0a059400840800c039000d040c00191000002a4000030009807004804400c104c0c001c009002503d13180603840c2802e540b59010942030700d00c240c0355103444c5000d07140400c00c001084240d42800e054140805c080701c4544591114856000303e4018013483c0940320740080445c100e0180e140100b420303100a2a42c50a14013082d51688580c50b1071109240d5500416024001c080e01520044440288200402a14405100c0a5401541d01100c040c0c81a80310074154004502c500341c41040c040e034070070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 841020944 1250 841019694 841019719
    0x106031a010219021318030f170c071112100621081207020312011409090f0d051606060b03041a010308040513020d09050f120315222f09 60
    0x10742220b800850b0f00d085a102c14000301b080342d070001c2102e120392095581007510742c1035450061080440089804c0c0218541d070a12a23480d0024043e511500c1d0006010b030448901c0300001003104401e808100514041d099400c80002d0559000c03008603810384492015850080310142080c03220f061004000c0001405180c00c952907580000da440b1405004881c035100d4040c0701e22104000036071190048403411030740c0e119a03080517081503030000e20a00003021f900c030301a07107070329124041c0306131440030402c02045a540c0302c00d0080120b000035422580801c0230640700e90b810511640f08950a903000300e0481041d401e0040340c864128100c0340c04c64945824503062400300001c0b80120f4200500f5644c00740312030a40040203102d8429100e2084005000ca440403518107802d02e001c00c0c00842c0207040a008000c00505080a400780c2e468003200c403281048218100c1143c2680c4402c002c641c618a000040c041072014401030104096041140f119200111440d641081c855101105d81008400954 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 841022194 1250 841020944 841020949
    0x5100c031b08100e190b010e0a05040b06090a0e060a150806040203040609080d0603020f0402070b01121407090915021804090809030d0203091c0c18140106031a01021902 74
    0x498200044640c03c00c3d4081d5903121013000340000b40c0d00c0c0c0400040190460380c00c43c103140305401c00c0341020708042c1c40c840c5060700021659940744c41041d02079521800e0454499448108590740200010b182c1001640c039000c0700050440d084070100e0062a424401154441880310500120750b102d55071048156030f50b20a02000c1d42002d0402c550003a03c0322070704400200079401400146004c100000380c01451401009590640000300c640182e10410100000c5030341c0145803410b40f500d0b0565400c820442d49041c02c240c3c0c2c0e00e0340d05002c0d140035407180801c2114103900900d541500442d480e50b08104c0d4400108128410301d841c03241503581881010030241010741000c4801402040010704003500f04c008241080004844a001600300188107101840c08022840d0300c854144920716200b0400c1d034501c0350340300c0240242d140c3d0481045082c881c20000303400c003840d52408603074030407403d5039924009030103070031265403082c0071002803042c2e501c0342c1d4400600038902281d079541c0e55805120b25006d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 841023444 1250 841022194 841022207
    0x40b161b1a0c03070f03020309150405131805011812030203010b0a0c031103031315110a1101020903150403020105240418020306101e0501080f06190305100c031b 71
    0x218408103003c1482490701141a0004204510b0f01903005950749603000707010092802051104414501c41c241f0040c40980c64030216896095520390b00011006450034185200501c5140010255030030122400d41100740d25542d03602d0a0320030035828920300e140c1003064003070b40002d0041c0001c810041c002c00d54054800c0e440c560019000b030501c458821403aa00141c2194011030341c24020728400034107a02000030240385168290028501003100d10080d00c1c46040710700c01d031001d600810039409025485d015081d41121011071009085904070308544a42d0307406114100c4083d405075190100061106030720242181031001c0c041203489207200f8000402c00144034011080030b881d440c0580c030500580b420441ca5020710520300503500300b14505611041c0541d09040c0013082100303880010046030740c0000c00c0c0c540121003100f22141c80d6950b1404510208001c80050000c400d4071000001030001c04100c0b4200041d130a2414442d0095481040c3d090303500d05400740b00101c2040d48400c1c080c920524 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 841024694 1250 841023444 841023457
    0x80702012f070c0f05030705010c0822080a060504030e1206070513170f0705060421020d050a11031b01051c0b030f010e070e01050f1302040b161b1a 65
    0x907109007403045503281c010903450a03421108012001513028003251500b0000c80c1c008041c240382620402d0b484e40d840c45018040c044541481100f21414020540050700b1341001074402c09003128000c03900c03800e0040240074181c4051340170405140c03800c1d156050840e5130000580d80c0400406c2680c07100d1300c0884050b4000100d0b60a0910401c5001c40c0d440d07003084030704c1040c0789810700400188104820003410079110340d21a0784182030800c003c118000c82c0d10311240c81c1820903080f03409511442d0001c5100405001c070006c006010b4040300108028112004901800054040f14550020f03450f4811407010f00b0006107000c00e00c24400b000d0070301458050010140302881c0007246082482c004a440c1801d414840b0300b00d40d444556140018008204d07076401021030401c200610352424000c07031000c4028074910303401038640014480d0403068580483d00109a01404540e40b414400e60a180c000d1000004480005001d03a5010803001c0165a5806030303418030b01e800802d4514042c25006590044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 841025944 1250 841024694 841024781
    0xd0f050c030f0705090c130b09060904050a090c0902030c0702090402040b041107060c050301060c0311010908040f0f050303070b13052508010c110c0607150e0d08070201 74
    0xe480300c04103840c18080320716070954010040c01c40030f0070602084041c0c800242082d0200320240038400118211074040d40c111509103a10f155103a140e40c0100c3c540303100340074907543c000f4180414044110550b501c0621464082c0d00101e0120303803104990401c2e440300340c5000b034030030505001460251915100c81504a1720081002500c814541d002c03d0954050942d041200840891010144415402444000c01091410078910340c14480046e01501822801804220101e941c80d06004000d5100454080c1c0105440c0c3c0c465682d5020844146154004c01d180c4800c144c0303001a49080c0003040c2c82015501c0900b164681c0e07122668501d0243d40c400e0b082d2914400c5000030045503c08034039192100c421120142c514a080600031400d490340e50320074034100500200102108080400c10054544003201d006d6964003250404201480d03a6a18200d119440c1c0501c07040100000240c0f82d540910907100c90b009556043c1007070342203640340451111050302031484070181c82c81100380300c0f4118142 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 841027194 1250 841025944 841025953
    0x1b021f0204050301050f06120f06010b21100501030f0b0f040905190f06060e070e062b02040f08120915070605160306050a050303191e1d040b0d0f05 65
    0x124000a425220180c40e07481c401680d5070180316103410091700e285542342400c00241030016032103001c95540c1405200c0c207810713100c1c00705d55220404640c40a002c52201e480507140058100110010303e010b50794841c0e903001c40d1903c510381c0c0194000b40100106c3c0000208048240c14400d81400003524803604115400d005040310009808c2c0f41e2092018114020540030080b88118030342501100c490f07400c8884c61000150401840c0d651107090603c50341e8041d03c845071076080181180c8005450f811320f110001e144090303254500640c0c1d90140c02110340010b01703c0d03880c41d5150101521802c5009100f84840410049143ca03800c0c08100100c00407104040d16181405a840b4501115020396050f258002001c3d0381002450381070003942c016040403261022201d1401000070f64a1080c021840c400c11840224604e5140c040c2c500c50b8501c0b0060111800da40300c030b07100000c1410b00945d42400712681101c2d400310180c10700c4d1082c40b100400280c40c5e0704801c0c6581e12a014414100d141c112420b208 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 841028444 1250 841027194 841027199
    0x415020313030c291606060f0303080f0705040b0a030c020a06110712020613030e0f060c1612080703050d2004080f010c082403011a0102011b021f0204 66
    0x100450340d40040d4003d41910061900b03040200300b41c1155842814141c0c3c4040c0e10510340300070410f0440d1200d00f4220007100c02c100e070b6032810201520440c2e1150004840c0303180d0000c20305401107103240c8508013014240680c0d55903140d042e613840c0998050664100c105000b8112541d001c0c0d803152104078110700460b01d00401a507108810382c0c06010080c20164800b180250400081d803102d04182c1016001603c2280341920303d2060b054807002d13000d010860b80c41030620f250f44411410101031840500919a55140c6002071696825000c400301c0409500c0d0100145501c221401c20101c1c0d588080d003245056000d40341114143c0008000c1000c0c641c5c1c8500300300c40091401d0030040d5000d0050003d645552400441d2400c180201d01d0741c41c02641404507401e40240c2c45038489e030f03100f0b44c0446000380e02c2e85a00760103003280326103c9525400d50b10700003058800319407031034845410070b409a0092114071b42c0320303401e4207a1b509600e00c0000543d00403202d000910882c4800b00c0c0342c43c04c841c840181041c1c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 841029694 1250 841028444 841028467
    0x10e0604020607150507120e010b0108070e1f0c150905060a020c250f080c0a15051908060a080f0a03030f0b0d080c01111204021e030307060b101404150203 68
    0x200150303000c6c4080b4a060303612280e1a01640a01090341c103010000b0440c00e100c3d000041c020850041c8080200300c022200160306961f0207030418003590307100050300707010100403c000d050100401015114560041c07031510303031894140500725000754060064181600d5010028019421200c6040514010280c01460380090082c05500c03071052001c080c40240c7c036040d03008400780f441c0e405c41d41c4a034100041005042d2039004e01c080c02c8070020b24071348030312590341c0388126a107010b42c0039806c2d12118190090303407180384e11400b0180154011290300f0b1100e0b035603001c050f544440d2007030451a182c0000c200c1101003070007584805990b01d44502c000c25809510070018103840c0c000c040c1150781c2140442c3c070440d0360400344903801c6400c280380c4460340b40c80d410010740e07064000011720091040c05080c0c05010320303028202004403050b1002d070460342c50350794610300f00d0043c14070204018050301003000000401441506108000401c980c0a10310382820010074803c040d80744003003d004c0d880100f006c580f006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 841030944 1250 841029694 841029701
    0x3050a1d12210406091401050f1b0c040b131d07030506221e020105090a0905240604090b0a150f0206010501020304050a141807020a050c03010e060402060715 69
    0x140c180300081c0000d2100c42c034000076002c1c007035050150303155400d03c0b0500c106034100d10300500740c415600c94032602080810040b01c40c0d01c905103103403403440e00101b0b07460403289140c8000440050900141d071141d0787c40c40180000c41c1d4000c0234417540504513802e1244200030740e0340400f000902000d895200d9001400503c1c1c600074043d0300c11602a4400b50070000d2460b030b810401d4030344424000d10303040d4844843c0c880d0074070703041030460b0f2989004007603299400710f80c050710494031010f00152840e0000340d1764100b120028002159805a40f60070b00301c401d0040b01c031260700202039200080c03441d800c150800d40707514002e140c0d41d015107810668250010400000769100d681d508001655098420804c502d0300a0901d40103034405170566005000901007a0350307079441c11055070404130201d810700800100069042c0d0300c2c540e080b112004014180080c0369400302d4180c1d403ca0240301110340d110031410506080750440d20385c1c2c20349504104086801480e005009200c283c0c014440650b65a01000c0e4034000c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 841032194 1250 841030944 841030969
    0x109020303193213090f0903030e061014030106090e0a052e05070203071407080c090618090f01020c011a0105070c05040e030705070b04050414010303050a1d 69
    0x42e485140441c00c000b50b0280140244102a40007112080c00480d2408030401c4030310f25640e2020004162540180401a00745005050580c0140046800345040e01c004080020054000905103145800e41200014802e8060051701007224106850144c80110700035940400c584d0654940200090500c018040c8914490000d0083c103803107807541c54800e191a01e1800e0740451038030b1011250703002041d80c0d0300d00c00c5201c4c448680403a0580e200c030b50490452003458001028240340001c280e11017000007543c0c07416108004112100d0044010810102c21000c03a0030b20b0307000c1071100500c02c2641c1455809030700310005000300c5105007881c1c04060b003a41c01510450403180c0d9240f01c10700c01d4501c0842222500d540c2828481d00d44003540d00d81f604002924080c4901803600d507498003942c03120401c122640b16400505880006031a06014610359001d4802c1034071440c20000d00050203030000108a040343da15441d15881d09052036001d488696106180034040030445004502617109c0c02102c010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 841033444 1250 841032194 841032217
    0x6030b0f150c1b0f0306130201050d240905090c030709020c070f120203190206030601030c090b070b0108010b0a29040b040305010912050a0f050c2b0e0d020108070e030109020303 78
    0x140465150140304c0e41400050741c0d40d20a9102c0b2081c0405500320000c1420011f030280b81696550f42c40c201950702800d0044000d10340f0003807042c4414801814081030000b81c4640034424086511003a0303145543d00e9a28403415455040410100240c81640d070091129141000c2941d41155980c500e801190000d0741c00040404c9444414030700318035040c441c144c04400303500401c11370b1083d5500420031a00000307043c181815030392a5181c1c4014024140f0300e000308200314103d40e40b00042e01c0c096098140a01c28804c241d801d29071003041514101d02c103d0191140003100042d01c2020300c020348a5021810740c0000b6111041102060150490300200003070740c00b6100108041400d440d00340a00d101030114002040010702031079400c40d0b44000040079081c0186001512010581c0743c8604000c445a21440100c3c0f281d20075904200c50300030716060504054030783c506a5412841444060855507400a000070060b1001035a498056111724031000c40140c0000381c5015281d0219103150700c4105940d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 841034694 1250 841033444 841033483
    0x30a290f070210091502042c070504290307020d0206010b0307021f0603051504110f100c0302010f050103050609060109050705030a050a20040f050604030203030a0e0d0b0115030606030b0f150c 84
    0x21000091416240b440c602030740c008c0c0c1440e180ca000020300c00e0055010701c50700501c801043c4482694030040c900f080c0541c0c12141503480c2001c0307034017a5481003021b4000025020b08000012200c0008060301e116200b20303006000340004141138412582680002003031803a55410011005c24001c00c030980303055052001c043c00c1e50406040000300b40700c401950900c10b002403d41c11201c0d8039107000016a140e8641068480c80c0700714982603015045a18503001030910f417600000c20710034009425400341d01240e0076518140d80710f445000a4404c22210480454410404101c0c0201250311039540310451103030001d06444175140503141c1c0c0328101041c0d20070000c08101441481e041c21907800c021700c0202e407120300e060300d0743d400b081d1030b4001d03440c40901344141c1220480f519143c9110254100e42d000d245142190b03110703440c010100e00d004002c83c000900e00003000c203105010f4420244070b10001024180c507101440c04200700303400100304a80118500340101100aa01081400340ca980c0381c16200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 841035944 1250 841034694 841034729
    0x2030a0221030a03050a140709061101180f0b06100e0118030b071e18030206070602090a0e191802090606040801060b09030d14070602030402030a290f07021009150204 73
    0x1010749202c02d4801071f003e001d0b142840090764005156400b1110181400002c002da5499814010000c4030f04c01c416040c1224a030b1b404008046e4200074440303214020b81e40c0c0c41e4845505102c182d075080b11210b0041240081d141580b503001d1071440d481d880043c0c50b81640640c07203582e07100020600341c07290401705a1503d0a42c43c0c48250011041561500380750000e03505001c0906510300c2d450380d200c041d0041c4000103460007813041c40c2d0101d0354041d030060302c0c06c84003503601c8446a41d407000445120f00719151f01411804050102d0242a420b002c1c40030950096084980810900410140009074080400c20000400040a020300802051640011511500e500e0b0506041034809041d03003042201c1000031003024980103003900c0355140c001c000180c4a54451000c00c1c90010110405820b100201c40d130b000c3c0400d0410b40d50300c3c50601c0c00d40c826030141c48030b5240b802c039940c0940c0c03290f0250f00100c4261040340303a1640505103460140500c031885180c08401c100803030740075800207901d80001d071814 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 841037194 1250 841035944 841035961
    0xa17010204150c11120a061104031202060103050d0c11060901020a020907030903091d010b071b2c04020a06050a090302091302091f0911120c18010c02030a0221030a0305 74
    0x100010000c1502c11200303803407003901006d4035202a901c008051681e280c5040140d50030110544029650103100c041c8600c0240d1000703540d84009110440f0148551a100701259201d1160747c100180d101c140034410101d05d500f0032031103400c6081030604500c5100316030000740c0e60b0800400d00800803600c0c002001c000505004021100982024a031010211030026690010354240381c1103504101055490b42140d1414403402c16404480003200700e102080415244031054128840441d004840c1d000c2202d0030240300c80d19001250060b620000142c401c01c140340c05100141640701203450007841c460386a0b40025034a10b0207032a8030000c00c1069580ca404c60900c001740640010500c1d20a07810004185540700d0010000c0c000c0403451900c480c8038900100900054a4907880c804560604616184005200c07a8224810289060b040c002c5000f010394042d11145803115005030250403e000e8039024007007040c41c80c0c1d1880180300a1861413115019042c0040e00c0340d200f4560b0086a2814007000c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 841038444 1250 841037194 841037213
    0x90601031e020d060b190f020f0102040e01180c080f07120e010203070f020303040b06150f0c0609071703040b0708040f08030c0106090c020a060f0b15090913020a17010204150c 77
    0x1005c02514010810301c80c0345c0074002e50a00540c01903107010407812600c5902207041603d40107a21801d0b60012030080782d01080a90390074140d4840d1801c800d01d0160030500b900a0b1040b0040f40d07004500048041910b521006c980355502070000d0605450380b40c107c564801c11924005c8007810541d41c0803060101541d4031001c4034000f05c09a100075070840c00c0a031200801d0242c082d096620038070301400301450701f407440c4094503400c03520000411340302c0c0c0c01b24a003284c0303415080f20142800d000341d21011030076004c40400c007000c1b803000c10f004604003070401222030b9850b880800141c1d460801800b0004441d02c481c0100000707848980060340d10b400720140d440c0d00b9240f10f03400081c0e1460400e402d05070b480b40d000400c0310319503400a0b0046040444007200318010030b0600740312a00321a0740100e904403503243c10024030540740f050300e8846d150f40d83c1448160103c1d050440003580321812100402807080007400344045203010600051401d60756154024035412000d1203000815546104c40c03040c04810030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 841039694 1250 841038444 841038449
    0xc06040204140108060c0304050a0c030f141b0402070219080d12050106171312050a08220807051203010f0801050a0b3d02060115030b060702090601031e020d06 70
    0x3240c2c04095040010035900c84e070b0020001d954030080440090103001040001c00310094200312038a20480c0c990510321101c1805400680d00303402c9050307a449403200000307030420b000c0700d606074041c1280f070b00301d07003000040e5210210a07613020070800c0c2c020144498810f04c100c0100307040c600811b40c4801c1030340e02522004081042d0141107103042e004115181c3c1201d40209040f40c10003058030b5681d0746c64070000ea643d842d100c014012198951003030f2a80394000c4005d145c282c0068032107941c2e81d034a04004a8000d240c14401d480b64641b05000000080c0d0403401600b4818420700a0310242407144c0d2403081c258000342d1100840b481c5d902d50420000000b0321402d0780146101c8800e0010b04850300c0403840382d1202c00c42000c01141407510803008158080042c9540702e215148000302402802c400940da01420701480750100301008400700040e0180c815603080050180410f0305043c901d030208090040024010303818581c50f2848544403005800100b441a507420400584551107103c960007194401d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 841040944 1250 841039694 841039721
    0x60612070803090f010c15020406141312020a0b0d06090e01051e061219020f010f09120c08060a0606020105060117010b073e01050a20120c06040204 65
    0x150060050501c08421100801015511512200f0303400300121001a00400301420360010010200c400d030301d1741d17001041180c5943da0340201c50600d50301c0e00e80940c4602586201714158980080000e09054564816241d000920344281c442d0b892940ea0f003240d0059103141e60840d03554100740b210149601c03600c404440d424008203d9442c10a40300c26140c015140783d0b1031503507400c1c000a80955102c1c0543c1d515180c10100b660145502e8425490000400a00c124414a0b031003200f002039501c10307a00e00c401034699648007003080d8540352500302d60342e2034501c040d5a414014500410611801c000c81401140b14103000a451403614000908541010b04070301e040008810b4003004410410b03811906642d20800a19038a4000b45805100c480c0d200c450086a0305210b041d0700c003280c848148202003001e000d031205070100812001114241300306403000d0f02003204101e0100141c42c48d8202208841d5084044455401e500c48038000710380c01140421440b940014100021810940540c01c412200d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 841042194 1250 841040944 841040953
    0x5300a140a0506120d05090a12080301061107090504050d0f03021624180501060504230403110708031305030c0609090a2012091b010c0c03080c060612 66
    0x15412440e803040805050310907195100c41c00b0a82d16079440e44020401c003120000c90704031240c59040030701190062a40940300d230310406000100d461011440d140544d5120320341d035246a00381031b01980e15600d25001d401d000c0c031030003001080540c04c0d88034290040e409180248109000850300030812102180d0200805005001d0401205142039a2801803548410801c42040006580f002e0904413a9180b40c0344034208a01c0204d0003411058011400d8040c1c070003805000c1d1280c0030700c800e50301510000c00415400588000400c20343c3d041e9150440d100c0d03c1d080184030b07000d040551501c2c4a81c0c20500c3c01e5040000c0c1c002c04007900d051004000d1200f07a0281c15246481c0000514a0048000240c012607200b40000c01810081d031001c0700da905080003001c0b621142c59140501d6400c8005480182e100f000c010803098200017858103500c019100d1000a90411580111000c1810402c200d8120782c003004080001250384000e031070003c10a40080c4000e10b48441000001000d40070120000e400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 841043444 1250 841042194 841042211
    0xb070318351c112506080112061806050a0c02160f0b03041506031109090303040f0212030d051603110c12090604090f0c090f0509010306050705300a 65
    0x1e010580c0552040001d03160304605281010580300c01c585064a00164020607540305903507028800c4240080e00c203007401c034400980303035030301611708540030b000c0c1d03c11501c10602684005180c54014080f6032400c09130102c0b00903855611f1209561090759412403090329504003c8040390304000410001034103943c1c0309001858100c4085241455003d014140400040041c00344040c00346680082c510503201001745a07600e00b8040c0002c0044030b0142d102da0341c0080403584801c8000162030080380c204400c00c11042040d420070070000c40e110b084407098001440200e0000c101403013583e200712210040c43d01a1309070f40c980141103401c11b500c2850381e140b06004020148900042035030f1a41107070300249030342d0038100c80081c0c090300030350303011010f110705011051007104e180790428022824640c813042c82c0c40da2226446615580035004898022401400400c0030804d00e41050b40c000880303007441403400b20042d100006200300da140100c00d000c2d900100030703000000e926509038040c0c0005000c202c01d14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 841044694 1250 841043444 841043549
    0x4152109030806060304110a080307021801081c02120a080906060102011b120b0607050a0c0f0506070b15120a111c0f02010908030a030e07140a0b070318 67
    0x100143c04140110004030000d01001004030f500104d10400402501941d665441c40545d20307403050304102c0c020070400d182901854004908103058540c07000250aa48900e11040310941030401111070841c89082001798000440703d0080a01c05442d035500702c00c0d480c0215401d841c00b8400f0341290f04681c9443c0e02da4040c2a41030f0001d80300340806140c00c1e5024030f0700321088800b80510340c1146500060001710030003044070014400c4171080c480d0003c1c2c81403940c0d603510340c800005117100c0e158002504103c05c0300001c03003003502164007001c500e5000e1801d108880120712100b8841d15501010b41c050500fa000380b05030381c0c16000c84030200b101c030600d5000802d054030203000350000b0028002402c0b604c070074046a015072544030191075100100d9880320103900c401009440481c0e6082158003c0460125a240c92038001521110000c1c0c00c0d00e10092601900c10181c0d07100c64400d50800c10904049220190011a40c0c3c0003401010305407218030781c409403000e000741e00800c85080310404a44410a82c034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 841045944 1250 841044694 841044707
    0x3090c15050a20060c0909090a0201020d110f010c0e2b06110c011a0109081501030b07020a05030403080306100c0209010902030613141f1410050415210903 68
    0x20310b10389008040344020241e901400800030030141200e01800341001048105400500b48514003142d500d1220344512407140c0c0c41c2c021030131000e070050704003034030b02d00320240100080c40768503e4031000ca6090ba40140e2a140c21502c0341c10f0000c00044201f13181c002e640c41e08040c0400b501c00c0d081c0400c00304440521086402302810900101503544803140310043c42c7c400c1c420346000440c6074009000c0400c00300c820450611036030188501040d5450342c0400c0e413000000b40c001d05070850105050003039007980c03111600701000402034070031441100704113000180c05201400080d4458111161242040810003015450384039145082000340c1200c80c0142e079404000c17504445000c00d0040c1d803510340c14003048110301204801c540c00d600789840e0090015280d540709114403420714403d1074140c143d10707004054481c03d20840365043c0c0e04080003078040c94984001c0b40d40035442d090032440c242d40e0304640c907100110189184003240d4554089540800000b002000d0441d529104200c041d1283c0d5016020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 841047194 1250 841045944 841045957
    0x3020d1a0106020f0a120e041404020a090e03070b150312040303090e041e020321040e06040b0a060e1c03020d030e01181b030b010b03010810090210121b03090c1505 72
    0x600311b000d901d110209024034481c0c2c100c060040c0091100400303a9015500c180760542e4100c0c05544052400a42030f80c00b4400e86205c03045000195141061f903803250301c103401015007010301e219070b200319021407681c0c01c019a28110307a80a04098980c0d2841c140074007c0c416130fa004440c959494002c210014076075659000101843c440c100644a6660020a103041c82c08020100800e0004c0109080050048040d00480d1040c514aa00640e10202404260341c5400d2003540c04c010822401d0150501580c005122100301a0480c0c07044803140040c860015005842a07000d40c1000e0040381299605004500380e030080d03007000384180d0700b1604000c26440c002100291001c0ca0040100c17028000070010301c0b0096422501d1900296112889050719600a1068034044e11814025140030a40b6004084086400400e2900c44d000018815900740401c0c0d20034001c5195122001c1d00c6d80503818181220716242650000ba5170415450b00382c0c0e1040d4940c000014100781d8400a100c0d1940c4101100c00c07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 841048444 1250 841047194 841047203
    0xb090c0d081b150711010f0902090c0f070204050a091101080106051909050307060306060215060603040312180302010b0f040603320102030910060b16060c02030403020d1a0106020f0a 80
    0x28503028502c1e00c2410031080c1c400051030314002c04180b2031070580c451754810710342c0c038000003c02c19034000d541942d00b1581c1600c4025000605400090341d02542040500019800920f65034034010340b5034000360440341c0448402c10813907a00d00d0b0810a00621540941c0400340a0808026650504074050002e028811500008440c2103526040f00e904c60340c4030074010140601185c00481d12000080e016040714064040144548080c1007001145040d4680c00b401c405414140742d0744072610300b151000c0003402d0500760140c503009042400c03403442081840541c002c4e80000b40b40500c00c8200000c0620036080d407841503050940501c04103082e0070350500c1c0e1106500c1d1030000b0408052601780c80395000303004103c0c1540302008120b80c0c0c0c440490886500d0817100300400065440745a030040600075110f540089110044c0c03c0b034001141d0b81d111002d07811450049a00300356031b03540000d80801900e5001c80d80168801203502928078280300144c00f40560f40040d044c01d00078000a15610039811a000d407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 841049694 1250 841048444 841048477
    0xb0c090904110f190608060109153005010e0702010e03091e060a020309040c030212190213081c09120f02130f0903020f010c0c0b061201090b090c0d08 66
    0x2002d035180b0100c0f00c540382014202c10b04400840f114191801c001384034405c040f42e031b0300b00054910340c4581125010b50b40f4030342c20b0f50b81a000070743c0101c8841c0000d02a100040b00e03a00003078600a0180300d0760419421705039402244a6041204d5207584aa01134240815a8140050fa22545001000b175400e030070b80640d000c080c8483c0034014100050034041e5610b070044c9001580c1050ba96002c4018525064140c405110704036003034074210103d10855200e2000e080307066001c1740300d060f00601c0c0782d00f00903921000581004102c8003241441c40490b4007040e0180e004108511300c2041120491350303c2c1c00c6a0401004681c0340024002120200c08001040d110003220904119507640701404c022050b141c0081040c00d00c560200300040441880940251254000101c00100140101c2e003a11516907220315030042c10340e840110146c40074122039801500f01d400c09011070400d1040d603c14a004d1540d0300c50a00744031000030b0602c240e0500c40b50103001e07a8070f9201e001c220b101c8200c44c03011040c4000e00e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 841050944 1250 841049694 841049723
    0x709090b030c0907230f0304080c10021306120218010f18030c030201021606140c0f060f060108150913020f0a0e07030f020315040e031e03040b0c090904 67
    0xd003011240c420150b44202d40106220005500c02005116132401300340c8568140c1d00508011111b00407174811000c0e2210800028001554000c042c1007030f01c0000c01207422541c110f0f0030700011b82c2c02072813610b2180c0b07601100810003154030800d001d0441500c0032045140080c540940070606091001260522881d40c1a00f010244900f000e0b6040340020700c1040900c1d0740b60f01c0d2290307410710a840140d0051003414800c100e15003071920a001100d409403036500c0c850075040d49420407900002a01030441c0140040d0b81c181550074081d0ba442000244003401c40762400c0740c005400f810026103e124549000b01a5000e075132122500315801101d1410f807401e41080d07500c00521000e011400c001e4002652140002d80361010300d40d241c0c0203140c0c1d03440a0007130900448801c0304038081203900c00079a00184040e0aa10304107036201c20f1100044005403490a48140c200100c100c00c00700d903000c40d1000001c01c110900c4403d4a86603000794910151030700c0c1c200c1c288002a1001005000035081d8100051035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 841052194 1250 841050944 841050949
    0x130b060a03080409090311030a2a0204050c040f1a030712110d05011a090102060c07081e07120302031e090106081f060608060d200a170d080709090b 65
    0x2220000e542c001c809950300c60300d400c00500a410704441c00c9011951581810004200c04019204401901d6603907200c007141c0008040c002d403503091f4040c0c40018040d44d4000c00b68035107003c4c244c0b04400300e0000300e13525464030080c100307486030301d82c0003071006a1501948003106040000302c0388c111205c0e280c0703815815600b021039001401c0041c9039170741b0000c00251030320110119801840c100d41e01180c41864030348000c0d400c0d284911503181d01358016004040050013812a98000e1310056000740c80460401c41074401701e0070226041950b9021010300403d09038104801e8001e000a6501c1c41c0ca000d50440c284402e08810103089118501404081540050f22407103095104000400ca81c0d0704840a5024200c103006803a5101040441401c0c04c0210200b40580201700c4203010f104042c1030ba07100d180007038855040701d040c01103543c401c5110f10b4040306210341e1384e00e080e2405440c5889003136087d056a0305c5004d14040303250300c111003032000b43c0041100d0306070003458403800c0b5603c50102055000e4403c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 841053444 1250 841052194 841052209
    0x90e01030b150d03021c1103090915061204050606010903080306040e1c03140f04030203070803100e0f06100906020304170307050109060e060a020403050d0e12070e070e09130b06 78
    0x2c40a4201140c141c00c0070626500182c1074043c8281000300c1e0f441d00c442d00100311840140b2a01c0594158000c11991110703040c01e504440d4080040070394821380d8071501c40080c04641c001c0040c0c4e1280e04544040c0000e200043c8443c079000042400d02480052940c1c2d5512600e02000344042e1046a45155059003403a0034040002052182c603800103801003c541c000d4003c10601c03003502025a5030030001450420511000303030056801d60021820300003950780d5840e242e40000c0645030000e011460000728a49000030203030003400320225101c980e2600b0402c0c0081005203180c0c10b020020b0b01d210420440d50080221420340305100c00c04011003864604440c0f542c03045980c003c0c955841c0c010500140216507000321070728141e0030103440c0340341c44454502050340140c1c00081c100c0d4114181c00d103e03140c0924464090404040c0001e048112001c413942e040107a1544070280c01e01c112030812031103960000c2c7d83e804e40a0b00300d50046031810035415050152009041c02170000c4040f401050300b5076a0020f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 841054694 1250 841053444 841053481
    0x30709092901180b040810021c1808040608061c02090601080717130302250504150509070f0906020a170c1f0903080a14062e0903020a06090e01030b 65
    0x403d000d0b07a6060201d070b0640c000d104000550152000e0000144414002c03130f01036480300b841d02e80b84001d5490003640146100401060081d0440e541e1500084c910070141c00148215240c4449510f41001405101200c13070000080542d1403184060042c3e450701c2510350000000c0c03034031190030783c1c61040680360b010303a00c0380901c1640d1554041016030303440c0c01410011944070764242e410000d01802c01d40e4000f41a03108001c400700c8000c1c2c1c1804141055400301898444403014520265516400714000c1c01c0d06488080000744440e41c4e261402c1d8108485500528003480100101d44154482140c199400da4420144400014075005942020000c0c031100c55582d4016606071007014002c8401020600c10480104d46100001000e013003840c42180402180202d564010341e0721601048030507400751100c444030300c0c20441e8002e66150300981078009460362b0f8480003005800c5004005a08040c0e80c40b40301080058203090110480070301100e41100c1d8460076400103501c401e000d9420700c54650 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 841055944 1250 841054694 841054727
    0x50c0c2a030a0f020a0608090718060302090a020a0e0906100c0c030605010e1e0c16170d0209120109021c03021213061d010504150c0204090503030709092901 69
    0xc00060000d680d40780c0c00f050b0701c210744a054a603510b10064898040455410703140c1d42100200300b10402c0200300e05200000030541c00200740783c5079070009075036040c03d440c0703c0040350303000c108035050030780003800b0041c2d2020869802c0c1d401c0c5080000105c03040d440524031820403801e0a04001000009050400510740c820800d002c030f9a11480143e04620084078545240041e140d0210407545858491900802c02041d505280c1000b00c2c00b52007a205445400719810041c006049140340d81d400b000d0320010001007805695210071804028983c10031007614035030360340340c007404c0001a603c01440142c00988000c102c4005821402c0c1623040100282841e2034520700080c0c0c2082a070315042c0350030143c800ba038643c61000101144c101c0c003100309501e04240401c408000034000d40300441280d035000d118500e08400d051841c1c0c0c0c041015204481d4040714240e001005001d50b42e9040300c07604020b00031215003040071300300c108800b03461541c1c89001039059104204481d01d050b44a0220342c3c0040804 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 841057194 1250 841055944 841055953
    0x30c030902130e060703020705151e0f060f010207080d031503061113060f09033302071a100e0c0706020c0f24041401230a050c0c2a03 59
    0x80c10b0140c0e01030840350040d91014018500090302c4c2ea40a40700360740e0002d030400000c055003000b0b44540190180090b000081036064495514098401c107010a4400d0101000b529402d040c07007428000c4041d042c20285041d5001000c0501c152040041d00d100c0c43c01d40c901c1d020490540360f41c14801c0e0304500350006041c0724200544815102e6261008140c0d589081d00344201155940750101c90202206140c200010340c61082040401c401000080a40c1c06c0c5050128909042158072010410b506030040720164020030700c0700c01e0000d1140002404801c0c0e6038001e0403450030301c102c0201e20881d4092000701d410800d0205684039001e0080d540b0351540404110b544030903001d9101c4d510701c00c0e0603400210744111000003c85c2e00801d404107200c3d950301841100f40761140d90f82c01d8450100e166440e0190344d42c0b80e0f0441d403d04026002030000301c2d01718120300c040741011440305064030001400c000c3c5041c0c042203d070092400000364020b507000904201064490a11154665030780c0041445905115 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 841058444 1250 841057194 841057219
    0x7030207050c0d14101418030315031618060b0c06180309090a0f0c021c0509030109020901030c06020f01051b070507051e03010515030d110f060411091e07030c030902 73
    0x120f54003100f031500d40400b8100140d547d00c034001001c41c0500501d03003269081030021445604000d4107842203e840101a903807200684110000002280d82c0f02c1c00001c41142006141c00c030306446858082c1c001d841c4036521b8078060a2085644130b2020780400d20307418555140c14031401080c800e8410008005001c0c5842d801c18185a034050f0204200c070307140451918041411a500004102040c80b65100c1c01011410005509407402c2d00034143c0b450f095505d0b1050840141d40380d00a5034060340c0708a080d08895828920000d1600742c0f400010201f0380c0c90070b4280100b000280381404502c40303032144420317034440d6039140c0780c0e040900b542e01c019044804c1c800d0000c0d1b00040e920031401d542c030341035001704500d0340d070403980b440d504800b80307030032900354100003a1646180d1017503003d460303201c8207401218600c55032524860310b403a0040703809890254812000e40e103a8680030090a40110010045509610f2080007280c5015005071000c0c040c540c0d81c82907014a03c1c065003154403499001001c0a02008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 841059694 1250 841058444 841058473
    0x140603150907090801021801020d082205150c070c06020a0f02062a0f0f010204030b0112211d2d1c0b0109050606120a090201110d02070e07030207050c0d14 68
    0x141ca022180c00750107505600c44001c0c0c480d952040c443c11810533039000c03494004080c644840794012003640e2900504006c1c1c0312040824950324020300100206c45d42c2e620307150500c030440142503000001190041344080010940140c024654290111015503036180130b0300c151400b60041d800302c000f592544440d500c018403800b141d45c0340c1c0c1c1584031b401d031a419034050313190350300300c0c42517020007481c0b9046039005202169154501003c1e1600c20b0205125981e25010101e0001124003040741c00aa51424403452020f051180601c1500c8199480c488410307c2100e0480d4400900c40890300c4242000b102d9020795494000c015100c64014015a5001010742801c0d5001c01c0c09004200085042002184441c20720f107049440d452143e422084050b119144182c008c3c00303070a0001d9040080284010070543c0d020700001500100f2030300182030403450880760701c3c403000000b08150300f45481842020085000803c8001030120308585003a030402807460089503102c2540000b550500c41e10340c4a100741c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 841060944 1250 841059694 841059727
    0x5061f140d1803020f0c06030406090602071e020f0405130308281a0607032307020405190e030f07290906070e0a03030c03211514060315090709080102 66
    0x450181d401e0321019001c17415000d903036003030749031030190481d50400004022403542e520000d0854450310001d03242c040f041e243d808400d00202c1d9880c004082a0896000718a41000190300607002a9000d00040c6014150303c4017903003c1d008050140070000001900ba040400c664400b69038010070944081f4600c81d0141c00103251404501a40b44101c3d81c1001c8240b40042c160341c0b030694555640002c003070610114003102d07115440e02182c0c0ca501030000c14010707500c1c0d02071248214041410b0351204040d60700076005860703850700d00d844541c004002e03060070020604200c4486603000005c2d02070740c40842c80040c43c005000c2e052145094400c0003030268034880440e1850041c0010758450400031080000c200340c102d181d110040100d105074250320300090040f0700641c0c208903174000724106d01c0300414080054881c540d41391194100b030081d050001540e03001c04140d1003c415511242503250110091514110422107a48070f00da60b08002140c0602c1101108042c115020089d901c0c0e0b2490011340d441c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 841062194 1250 841060944 841060991
    0x20912070816140901171c0e0f092509030b04060207030f050f0a1d0a17010c03050c0304032d0c030e03030316050c0f0708070905061f140d 61
    0x4030040050000f03103954201601080c15000140a03144592902000340203803182c569a0100502540c5030f52803814184602100c0356038002e480750950302150008004211001100075031184601d2001e01c4262540303000325a00b000e6414200c8200c0400c100b00664400034254002082074100341c0801080081503000f074050544607450b034200e08594403000f620b441c0201b41032241c8040062004441c4140f00e6020a0f240c48801c09424003841e0090740410382e494803540001e450052200c0700180340440c01d11800172500071030310341006241403500b00d0078018803019002504200c003e880440c0030b500c801d1034101007220707000d4000002402280c80501111800c0800360080340d1007080014940c02e003c801c036440307002c002c0e050b4011800b85400980d056000006148958850181d4240d10000304100780300140682c41c0c014524207140140c3c41e802c3d200010403240c010903004092101e0342c020501e8444544586043c001c039103184003c40100c00d4017820100c41d140c60304160b034802901c0d00140d03120760f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 841063444 1250 841062194 841062223
    0x3120516030221252d03110703030c09080703020d08210114040609270309090e010522020306070c060b06030c0702010f021902060f0d110d0c14030a0209120708 70
    0x48040c0c204130141c65401140f10003683c040041210b4981000c06148494441c061070301700003074003116200c0000c030250003600703045001ca0342e42e00c46510007903000b00c000d0001344103107c0105000d0f411a030104202c1010040001c00c0c088020035400a40c04401c4548074126100041c41c0609695407022144005950f0000a0041d45003070b01c0821503101e80c0c01142c1e51a40340f0a5140e6031201a4060900308100c41281541001111030000c9030068440c0100a25a04658008100c604150102429200c6c21a4800543d01d01c3c0a00c3c0e040147c0340450001e61001c1d03141445c51200c403040c10201c0c050800c005c101ca5014000008005511541e03034041d00c510380c003c0c0e032201442501c848042e47c0e12001c41c0c401c0c1c404445082462001454140700600d000000014424207080000c4100c1054840280e90b40465020215181006050070b02c2040044c424529114425210503401c10171036100240424446070340004464809458060305441c1180c15281200c030b041e5952502c1540725594480a0790 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 841064694 1250 841063444 841063501
    0xf1d07170d0903020d0312020d06031b03020d031404150306150c0803060f1201061d091b010e061e0301090b0f031c02101803120516030221 61
    0x48110400114540540d9040d101c0000b024210340070001c0980f0304001c100c0070019140000d0780084c1150020b0058400d400300041442403c1d40f40c40d48a5501d00b1001c128402c40c40710080016030380310491418405d0305410160300c0fa10750510803003003034807641e0003560324140e44001c40504254980d0200c0121440c000e454241c1e0103194400b118205048107015200c04400d002240281c0b611440c000115100142810403640b4642189403e41b240380e40404890001d504502c0030616150520907808110440503152840403603540c1c2c3d92035465461b501e410031541c03a200980d592504001c5800c00140b8106808040707044441c85c00640c0c4c400d0182d2404141401601ca503581021002d0b410210001005450070000c0190640b451240076907440d0114802d03250001507074a810b225a000f0404400202490f1104500b0003401e85075907801e00030b000910f4a03080012107040d1071008071441049140c0540d81c0d2380845007008001c94a00407444046401d0300034800b41c0490380300c3c0e100d8816109030100c4c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 841065944 1250 841064694 841064729
    0x30f03030c051c1505120106030b0106050a021b0616060e0d140405040c0c0f081e030601021c02071e260a14150a02090102070503010c0c03030f1d07 65
    0x100c40710700503c165a003640300d90340c0701d83e1a410390390f03008100040300b4003050425480e6141d0001c0d944080040180c5d5050355500d106106100401d20500c2c09842182881890b08180c40c40095550944158518540b40c408107104400d6070780c0c40c101c030943c0e46c421110710845101c600704800107140c0014000220300c5818031941e21a801a1100c00585541e090356900709840c20051101074041c0300116020404002c1c0d90f40d0000b600d05d41e2403400e060086e24806c1c0c44d00d1802c4000d18020f81c07040505140c041042c01009020382c0d0010341040c03041c510407082c1100002004041e490000e4a8000c41c11040c2c4100c0203e0b60101000d50050031201c03545080b080112080c1704013001628081c01c040b4143d00070000c44004038074200d00803c60318403508200c0e00c1c208400c202c020402001940e01c01011600007412220303170744e4100b04000c040d107402c078001c003c08410000082c000ca0f50b192001000e150310b45206e488050129804000403040340d140c1078009440d101c80c3c590306d83c130540c020000030154222070b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 841067194 1250 841065944 841065947
    0x402070b19110a1106010f0f090e010e01060b03010f0902030c04091d01020307020c1906052a060115081b04090b0d02031509120a0e060c030d14090c040207120c0c0e01030f03030c 78
    0x140c41218420b8008c0719000e420031201c1d0b0081e05100d4080c01256480340300e11100380c0424898480100f0803d200603842e0750400c1c4a0300d5070a10b85178807040d8030303500510500540c408508116011540c002070002804031610404410b01020011704102652011041012160b0045120500e43d8011201c6845c028900003240c000c0303820500445002075002d02882d6032444090b4200ca01954012074011030506c0403852240c9010000d07041441820750800f940352441c0d4003d00c55a07040340940c0303010b20003001c1070710303800100c0d010794440c1881807034846048019540300c0b00700b25009250040c0990310300c000d0780b81b02c510008409071044042441990500c16017041d0a10a0312556031240e907403c40b650b2002402c2051716003020301203564a010030041c884050101c2c3c410000a064480740c900000c9c43c106140710f040a800d20740301401203004009803c00182018014411030000f820220380494850820300e4203001c00390885440050400008400e01601038070200031184039590501000204c06030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 841068444 1250 841067194 841067219
    0xb04180216030f050d0c02101a0f040b01050706141e01030b070507150c0207030c0f06020a200d0605270c0405250c050601050402070b19110a110601 65
    0x31a1802071001820704400a8860030f485540c000c603038035005040902c11128603045484800f40d407130160b4400d0354803160038400c0d8007a40e042c540903004007104000080005c5010024880c20702413181e030b5140f2000c51540c2c0203400362080740c0c2e00b059080054a503080c4914081d20340c15100f240a1009452610000c000c1450710b040c16240d00ca4103c100c1c0c0d0712195001d981682040c60210784a02c2c00c4100c66541c091076214503000e40b512a401404100d02c0c5040035030f030418a03604544031130b0300d91650601c80103400092200b00c065115046421748ac0e01d40c0101c02100c1410660540e101c01011504418040709800c420f024102904c4484210400c4016a02104010b20a0201c180d000b0740101c420074607250380855170041d46040103c000f81400c410b07041354285090124400315600c0012242400401c016240c0942030650b02140792007001d490310851604000c1c48180914a4240c8108980307408d600440d5804034040f51294030383e800e018000d8005820070082d0f00320b5103e20b10000410000c0201e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 841069694 1250 841068444 841068457
    0x60307050a031509060b04180210050c19050f19110402040f060809010b150a080903090d2415150206010501050d0b0414090f0d08070f0c02010c0c0b041802 68
    0x398060030700710030f0b4007860281034038001c16200c45584d039610380c0864840d0300460f0800c40d42e440764a0400810b80c81040b0f102e59078a00c2c0c040030010309000b0001e80724000180e82250100000803080c2848030b07450030502c0c0005c503609039075940c0513484d001c0003010399090025621510421402024205a078140000c9016502c00c0d0300d100301e0f02e04001c0007414002e6803400e0300302110308000314000c081507011904034140d42410081080c00094a0b01707030b49070322050040d002180710000d145006101c0d40082d000e8114204040c0015101002d130707541c1041c640d101d00100d40c10f850401d0000a07107091780c100703140c0720b6482006200510b02c0000208a40701044440c140c94058603400c1c1422041c40030b0300001e041c2c24600c42d412540e11403c881581356800c0045200b42019801455200d614004590826212000c03610a00030020140110150402000ca0101c00b8924084851040900049500c40006a00071b4251a40060040303240c0340c0300d00081c0706807450644110302800079046014120f10811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 841070944 1250 841069694 841069703
    0x190f0915050706020a0c050d0801060e040603050a080c030c160302180402031f0624090e0405032209020304060b0405010f0e06040504020a03140d0e010c15240806060307050a03 77
    0xb003100b4000540729501070002203e8a2400d0019120166241803034500d4070071030320740820b03c4440100200c990040018282c0b51041e1800c0c0100303441c59940f19680c6c0015600200f41600100e0038129400d0304000f070728070071781c44030040f6442261814184085041c8501040c2d00400441440091100c0c2141c549401698054000c050903004440c940460203203505c4401d200c6601c0c0d0340000b030440402c00711a51212031640c2454030325205644050300d40000b660000040aa00d1410070011442c0030007036034001500070f501d5000380790040c00c40c54202c00082d04000ca8140c404001e2100f032125030342c000c1038240011799082140d6602c90441a1400b170007403040017030380e01c0302c5000101142000c2e080180c200e840a4034840d8403507160340e1810151140da081140381944481101d500b951390050b034404080e00203082482c2561440e07118003180c0301c4e0341072400c0c444a884818021000032810b4035140900d280d564004031007510381480390340360071058031098401d00c21340d0070203d060f207003036810401108e611 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 841072194 1250 841070944 841070947
    0x10309080909370b0a0f0b0f09180601110c030706110a080a050c121602121e0d020c06181207050d12020f01051515190f091505 56
    0x404000c070341e000007008001a44005060f18100011001c441c651100c00e034414040300c1c15000c5240c4045a100645540c4611107050042240d40c001e101e403c0143e50742540701d1544c2ea014810500c070948115a411303074106110920f44c59090032801075050254500340d031a072420070341030383c500e542c0d480c508042543e00d03401c00c020802906000d1502c6195659903142650300201c0c04c0d45401c0e445802548008010410000d0540e84e11300c17080c0068800e07080400c8146080c803a42e071010303046202e103e0a00902401031202c0b40701c4050f504110780160392000d00c040b08031940d50220700304c0d03d400d14020ae18015200f228600844c42c50282d068458030078141aa6000703001e03005041000b19980c040c0d90810b58013841c007000c600c58031032a035a030134507a001e08070411100492401c0280383c501e2340040012203904d01001d04c0386080c2051013081804038129102d2891900d1540c08801c140300d140b451404001c0c001c41000080d680200c40103901e046141c0358041b10a54039400c00091410050311180040d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 841073444 1250 841072194 841072207
    0xb0301050f161e02030a09060302070b0601030905031c020a0306050102010e03030403230c0304031109130b090309130e0606030303010305150a1d070f060323070201021603030605010e01030908 84
    0xc81111410408580c0d1920004403400300c034074403e1031603803039a50200607040020164500f40c2c009021500801e294901103240c10410b0b110820301d040c015040d681056103031035110040c81801c2042d5070340d44c1c008c8982407190a440c82e0903603000358801d24801e0301080c01d01e40001900d41c0103109140d207902458003c2c40c9113903100d990440d048078140c1c5804c03135030040c038081800c1c00c0c00c0030402812504940200560f03841381981090090410181c030342912540a650800000340c02c204a0030304060b5000a9120050700c48002440c154003402034a0341d00b04800d403610281d514440c1d003085004480c0311003a0341c0d40351180003d15450748024000a8810391200301d04030b03146100c405000364021150300b00002d01d03000342d40e020720301030054551004140e0f205010912040138084075580040209007000c00001d0004804500100c1200d2232181070942000c00150083e07000303404941800c02030b080d6204144005180c082c0081c10240102800203c510350094941d501078400d1080054204001c0e60424a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 841074694 1250 841073444 841073461
    0x5010503060f061213020109090e0a030f03020f0d022205011e0309020a0b0304050c0415174e04050d02030703080315090c1318110a0c05010b0301050f 66
    0x48403030700346030001e5040061512582c00c136030110b07010b0401e0201036500c04400b8000103001100e260441101107107402110405807100144e0000f20a516013040313508158011780660003030050f28075504102d84009006480c44016a0007000c604014401588803400c070000d030500b01c811507004071800310b442d070007110001803003e2100240a070120300e0081010310103540840d0701d160280d8405002c140b0044280803c001080c8068280880706450030030003005c504001d038103125040e00c42d03264074004060b07280100c40c0080c003204000d208038483d0440c031040b44c0908401c090400d42186203012124504071416860704003500c1814103914044981014148010060041b400c1001283e043c0300e0341c1800000100c2100180d44070307980c0701c01c0c1c80c15000440d01c244400740b1401000c1c0030008004002d400c4030001110100c0080d54081c51480c0304402844140394005e00701d0a036100f14450000c22200c81d1103600c580e0032551039108000a0140c202014141404e81c0c0381580c800c4400307101000090000b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 841075944 1250 841074694 841074709
    0x61d0603010618080a0b15090609070c110d0f02010f08040213020c0f0604080301090e0a02150f16150f05150105090411120108061308121e0a06140301060501050306 72
    0x20300a4200c0b00340e81135034880a00d4036044419108644011180080140e43c11300148900c000142c240c2d100400e0740340481c005060410002d01401c2440441400501440030889588120000107032102030341d0021400c0c00c42221807080002c9000a00101c0e041013518441c903e014060b0382e02a00b00703c0300c0c00e00303d00c08101a4001c0110b013507a5100740700c280240582d0800126000702d004d240003545ea541001c10b20070507590900c58801441d400856440010f0316400540c560f416507014085440e4410300045804903c81c16080c540c01c0b40c820507048003803200d800704901e000d1048007020000d45070306040200688200b10345503004000e41c800d80705910750080006109200c00100009403850300106141015001301e8540300c02803140c0700041c04803040400186130001820754001d118004150348801440c0b0585c00b41d0480c440440004c1030b0203e00e40398101e90f41a0240c00b03d24958584000114001e00140c85540d19111a684409490f0f04040c4030748000c0c1c440680d611860350f0356007010312103c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 841077194 1250 841075944 841075967
    0xf11240c0412060f020c0a210203210709050a0605040e0601080408071502090a0b03040b01050904051b310b19090506060705010504240204240309060f06061d06030106 73
    0xa41d03020070111408010912844040f07a112320408003040c07050408181e0744075034250301070055510402c50b500c0810007504107110308408000c00c085c11603944c21000c40310140b540e0f10132900302c1c07180180840c5482d0844082c00640d8455068000103940c2c101c01195102030580c1d024290500802411001c55030440052409200b08030015250086a00104203003501ca603000c2100d600d800710070f02c000c00c007500095034010705084071a40310909194032040e441e005c1c14080f03c00a01c0004010600c02e407034031740b048100748100c113080712601e1030310780003102440d19542c000c141c3c241e1511010352071230301c3d245900108458000b104854084e0901101c0c00c0200805030181d036029006000110000d0f45c24041c2d00d02c2035200d500c06640f030400040c128854220301c0024003050300d005200c02e01c4a41041e650710482c862418080342151680400203600510f0207010107402d560802000d00d40a4495402c6002101c0302a80c82c0518442c00400f410740103065240320b550701c88010001040403d00c220300030003e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 841078444 1250 841077194 841077221
    0x9110702040b063a052203090509150301050a0c09050909190b01080c0a03080a030c0525020907081b0a11010501060206061c150905030c010e010c030e010902100f11240c041206 77
    0x11070340c03109c0000350b1900003101c0012101c403d100014102c0c0c2401c0c00b446401504113001401590202a0082e101d02a02d0080718040c00c40000028031046040000540b01d07508400390304441e800da4244404000c0007401852558400d10088a100d810018103910480750807000e5642441d8460f1011000340c00400f8041c4c08001c03040c410401c002038107503400d03c0304132038a01903440d82c54510700c1844100d0340014040c20600c04844200850300103040c60396140d4a00e082240c0d90b444110220544454034240314a15840d072a290000c601c0940010342c00d40600c0c03003210001e4401c0f040b960151801412407000070711207490039019030340c2039600390000541d0500c10019a0705050071100750030b003150802c561280f942e0391601900407005806128505c0d440020000074403021655401040035400c03650214030801c8000c00c03401c1041403240321804d0b507042d880025250a0080d05050301c0301420110440800018060045101c1001c603904030750466180341c1000c90940d80a4642800802d411501000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 841079694 1250 841078444 841078457
    0x24501110c031e1c050a140f0c0a03020705040908090904140d170106091410050f0a030b040b0d0506070807050f03070807030609110702040b063a052203 67
    0x20010b0750280300b400482e00f41e40081c6aa4003941c02c95891504854031070b540344001d10202c4e9010410b5003e400c80300030001601381003d501e460480704c1c10f092312406094a40c1d1403004901b0240094012400d8241c06019508403035565441b2400c1204481c411100200b008a04000024080c200349551691040c007035007582040400f0003d1680c2031822440740d80300002c10304160b14041c203484148141c05000185080340407103041032411035018a034039148600ca40320000050511520032030807610f02080780745025071501da0f41030000d0050000328080ca48203608144c400121382c2841b00000d10042e81103001007a03036031030781c0200f0b850209018200ea410090104449588480c840300114000c0e402c40e5209055850011401811a50745030040c1a84038140400380075003a000e4401e0740c804c3d90301154002240380306400060018820380d54021010003000c80202116141c0140c8588030144400c031100d601440d644080c0102e40040f00c03416128107802c04880070f100d04160a15403010310900701034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 841080944 1250 841079694 841079713
    0xa03050d200c011409040902121006091116061803080f160e121603060b1c08040b0a1205010e010f0803030903091203040902450111 58
    0x150411060080903404508140a0000050405401480e000780c4050280407076014810000b840354039080380201d1894004901c002d140d50303859008401c4a54014030400e100c07600d06180c40c1d04c40d00c1054101840da46800000200e040e02401449c0c09000a04291490141c0380c0003079001c00c2060f54010303250240d840105d16070507114007000c000118002d44800c402407802c103004012050b00108401c420030300c84108415103c1d00b21440c01c805e20422103010400d62262401c4524240c410b84102402042c048000810300c5420390004208400035600000d04a103038026900801808060042103500d080100300032401000b40501004074562515401d400728680b0714106907502070b0410000b03000307400e00421004032643d039154000c1c100d80020303600b18074000268039101d000750010a070158a041817001d01c40d100600454029201c0041c00315119903401ca868150b40c1021803000c20681202c81c2d5015501e2101c2500c0004804041076071560000304100450341e0821000c481e10042c4a5507900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 841082194 1250 841080944 841080953
    0x1103010302060a050322151d1e03090a1d06030307031d040209041a0324040b06220e1902300d0c06150e180c0a0303120c02190b04020a03 60
    0x1500079005043c0b900301c140c0f0660a01c001c44081e8022403c0b4000010b4a0b820648c02c04140b620440e40346410909010b242224201e0642c890420541c2e400042c0728070108100000c102207800c0b00c078858001c0c0b0942d40d03504d003c0c19501d00c6440800340215a02c0103891810005080b00800604000f400140c00d00c2d49650110341900c101048203920428003840c40381711410b040007904481c02c0b00f000381c24082e600d1403000ca12801d0b000380020300310010300f0f8005090f980b01c419800c0c00382400a1168805804a2055040140300c018103090042c06007000005805071240d6070800103640050006400c1c1144c1640b8034920355102c601c0c140b2002d103900800a1a010511815680b6440c94a86040d126501d00e426070440328421842c0c50301030000141484020051000d059014641e109007643c0e5072081e040d103e1502d0a1420a150310400d0342002100701580142100032941c00c00781c040c0020b181003001070340c0310b0f02d40d060644004c2600e036802c1400f0544c2c010b8000d40150018040072070041e2642c6a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 841083444 1250 841082194 841082251
    0x306020a12050c160f0f23060a021c23130201031116170903010c050a081b1801090509010b030417030f0f04110d12031103010302060a0503 61
    0x30030104810810605204503940240340d407021920b441c80e0300e010540421400790200360440a08030320f100e501d0000c100b003481d1200804007038010041e589003584049102c2c01c108804040242117009480c00304d040c1d0901d900035503220120000b08101c503000303002c2d9194028108405006001d6061070425506a0003d4440354064200392800300746072843c82c0009410f07144a04a000c0001c581002952404d420148101c00c8081e488401740e00c1241c0c100003003040d540126540c2d194194a00010051000c0d001001025012202d4980040d40c1d40c1c3d0f41d0381b5040011411101080f441c00030004a0002e44100c07a206964003014100303050019160b40200c1c0508500b41c102e0f02c44c0481c0001400240b18179494400070508140c0300b194514608020b4100d240540034102c1c04000781c0d5680400c0c2000040c4100c2d0303100e05800360200c911240c01c4d0401c3d10003164103080400100c0e01e0072a0000f81e01ca0136408903410f8a070041c010526210003800101c400b0740c0700034001c042101c0b040d0064a960120030302d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 841084694 1250 841083444 841083457
    0x8070203070204050924060a170d0c021207060c06050a0c020715030914010b040e0a080904090606090509151003110d03050c0f48040f0c05070b13020108150109030602 73
    0x2006c251082c42c2007000d0040c0c0a00700d03000f519580304051103c0b5849840041c404414010300d251030070b0000c001d0f102141c000c20740d50004d50040c2c0940c9401240d11079108403030f1420039010b10402d20650300c444548030119400e020030100140c0005200b40400d0160380250307500c614092400068000c0d803501c801e242c4024410740c602659440d00420200c0d4641030040e0151848a04090f0240e0b80c11951810b100d40300d91484907005036202eaa04805021080d4030180080400f40c0c0305000906e0861442500d03201d03102e02c1070400650301c00102d00d80952440c0e0f039030140c9602522084c0917012401c00c00c800e5640c0c862048081200c00c00c031850030001c003030010050500c4003000814501216003810a41c507800818282c07490131703500381c1103100100d40c1c03d840500c501415498401c0c021924010070b001e030003c0c20603005005e050662001106600c400180081801285c509050b078940c01e2510020010b1118081d00180c43e03400803511044c02c151100300c5121050500b00d98141c0d49a441c0700980c0c2155 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 841085944 1250 841084694 841084753
    0x90f03050d0c1407080609210a1206030c0e0717013f0804030605070201020a050901120b1518040b06120a060f0314100e030a050a0339080702030702040509 68
    0xb05001f61000c08001038509401d5211a4020940c550244112a4060740d464502080040244255000c050f5440040a1074108113046081515580103502650041d02d0200004220512803c0348048411819040e00c0004040c10f44038400710007032240014100c00f15402c004c00000160985041c8041410001446182c04644491642c01c01c02e08a1b10003c02484c25a40100558080306030310500303c851910342401e04061400081c0308080c010001010f26981240003040300b80242c00244000c1c051030744103071030326000c40c030140002d01c000e503212500c000c3d402c06018412919815000d40085920445070540082e03032603910280c4207a0350001d44e10941d0300c03003020781803504407500501c266200000c1507081808945621034840d9030b64450300820004204002c03840c40c040d1842a0040359003149413030202140c0750140400740c501101101c282040051007100c2e10f258460051072440d103e225160099030601c1e1003034003440047c01004041d420240a044030301880301c0429a02c44d880d00100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 841087194 1250 841085944 841085953
    0x60c010507080c030907030f061b080117070f09020f0d020d021c0528060b030a06090501120809060d020405031903020d0504080304090209120307050607090f03050d0c140708 76
    0x141d4050040701028007803e078441d908000300f0403070030300008510302125401041c841c407400b881c0c14401d0007092001040220fa0710354a8600e04590b502004503416940845010700346030b08901c1820380d607090030303120311509840c0c520810031071415660301505000c00501c01c02803415494400350381c100d038058113191101503400f10310b404a82d650301c01c10003600c221901040040f030a14140e60550300980c004000c01560402511802e101d02c56040000200f14004241d5200c0c24007469036000380800e401901c1d4004e1801000082070f032030481d5120703060341c3c00906040c501400c00080c05421350041c5103203c0b206401308400607894900704400c4601c8050285a201e0407501c038980282055180213444040040900c814881303002c0100c200c0d4100c1312851801a030f1440c60101240c044851482226068080400d609091000c0402e00030300c601d00b1a981c280e001c1d500d070008003120b0340c0301e030001418560000151009550244800f00307030b850f00074481d08040e403400c221180d280403180e41011003103800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 841088444 1250 841087194 841087201
    0xc1404060806012d0303052b0e0c090a020a0f050a0e210d0908100504060902090106050c0c010302040b040e1317180d020105070210050c0109080a1b02030303060409020f060c0105 78
    0x2c8149007a0f8416404444c40c6a2451510014414018103501580d003041840e69042079855645c144044108186c13814001c0302121041c403a01c0c1c401d0350107901c2c052a11040042d500206520840d02909001c0e1501900400d5116003124144c0000603410b01f44290324507458543d680c3c400005104900c0c043c1925a41145131000c90b0401f41e0484002d4140f0010450034800d0035404554a03c44080c91500000c2696584c21300c0303005410746000c080e40004044001190841d84000240048196601103c580740204401141244035038401c0b03d5001a01340400e22101130100310403604000095140f00740341806444011008910160007040301d000003400007400c4c4550308034040c42520407503009294031429000a012441000b070001c4c401c40e422100d0b40a218004d00503101070200841c0208846a200d1400e0b1140d40d00040044001ca48074201169440c0031081c00314406c00e5010300a5811901c41c10180300252501c00360480c0d001003000700f000d44507100c400180c44814031010012a8504 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 841089694 1250 841088444 841088489
    0xf120a0614030c0a090207050c10030e0f0d0e040e010e07091e06141504080a03080f09060603070b0315060f0a0e0a03080a050904021903050103031107030c140406080601 74
    0x50711400741d019422140c0b81c009195a07000312401120414800135a652102e45040c0741408100c2485681c460311003844110707580e5240c0c1c086002511200308540d594910449000d589202c104400030004100e02d02c0a0854140307a08041c09601140700081845100c001e5000c1c00c0203066081a00580d55031000c540c021142070303081581007641ca0400700030041c108101c0040f034032a83c240700ca014510020f01c04190124000444008282c4201650852041840c00500340300c000d03200800da0510010108104410205d4203038068900200113059051401400f4003003a00001c0c9900303110043e82c0c030304000f50784a001c001c112400e0356800c071503038400b00c001d00900f850b03900e210154000d840b80c041c148000395180302103665035811820041d031141100d9001402038482c07200c0800481107400507128040360190801e80c10380e0302c25112003000b15440400309584595904c8040c0111013501d07401c001152030b8040e240c02190b0007400100710703203884401d000c1c03400c0b10070380c00801508007458076010b0303a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 841090944 1250 841089694 841089719
    0xa120c061a13020a0c300c06110903061f15020106030605070305040818042706050702030c07060c052407020f011109060d151503110a0906050f120a06 66
    0x58008100440c18070400c084010680014905c004002c040b203034407401d090900345401c4203000c42c5070009644000100000052004000e04002c0381c00a050030001d00b40340388000c0540780050b401030014401642c2c0c8044081320080310b0032000d4645080f5080c082101e03002d0a60b03e410505803a000450090b00d1480c1450496000600d010201440d0001b4040061100303002c50705100e40704203256a400a83c900003030700030000201004d01e4281c416801305226824900903500d00380c0036100400c90380d80d407503000342e803207116407104010180c1014506001107030207642c50100b110b0107041100c1c4002c0403150b280903101d1180c2d643e24407483c0745400f0019125810040394010480c540003d000c40d5007a0501c0b4074040c051548154030407400442c00d02603003802c3d42d118020884401000386903680d959071000c449503001000c0940028101140202c3d0300280c031049866182c4103584400c00280f83c10401ca03401c1c0c101080303030103401c642008144030003201c100150b4008c209003c800680646008034110b01c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 841092194 1250 841090944 841090969
    0x1060c030809070b0301060503040303060806010303110c01080709051002030903030d200f0f0c010f11090f040608030f07030522150c0515100512070e0105120a120c061a 74
    0x280c2d006400c2800100d0135042980d04484c164102251680c6031458250301130b0141ea080703007a07a0702c103403800001450360008154642e80102800c3d1800f140d4410011590b403241182c0340800305508450801c00b5040c11718205406101a1050341c0c10440b0302c030002402d6030b004030b070708040f4a9141d611000721409400e083d5626120560f80280c034004c542400310160f4010400c004084010100329100041403c2d040800000d1903000100403140a51207120090380103411154001c442400381406141400e00c119410b8803d144011414160810744038201a84a131004a04000f03040c804400c01c0006540308506000c1c0021940340c80c2401c292141d101c03000396041c103404000400b411078002c268080f0340442c040100708050505035a56901d00c2c40981000d5100c1600410000507507505440041000c205035040e9451903803060740d9030740030080041c0c00071701e0068150b04002035100000d084209143c00244240c03c042c54034031115180c90342280d440f031802c410a560130200342201c92520b01d280800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 841093444 1250 841092194 841092211
    0x8120c07030c0605061c0c030b0105060a0e0d03030b0a0b0702010e061c0c361d13020a0e0106050c0c0910050d0615080f07120206070b0a1401060c0308 66
    0x401819481c0240201c0603600c002d460f46a072840414071544440000d182d1071904030942e90150f00451409104091842c403058401c06040340c000304803480e101040301e00381900d954910309040d02070b00400c20745480d488411002e0560f1040f0300495504c40c421040000c20b42c442e03c0b582c60b05031a00014081624000800d449070b202001816101c07108202c17421200c111800e0700041401041d40142c0364080390044500d9034001c0e00400004003074075050241641e514030340c1d0039660550344455130000d50320280d0700303010154020b50000768800c0c0d28401180c4041d000620f800507403940c580740b0307070610107083e041603000803000168003015007420060100305040541e92034020b40381042845e2445500e03030140921a040306481c9800380912034000380341601e107009800c102c0550750544280c0e1103080e9542414540180c00d0005201c0c90b081800e800001c2d0042c0005103440065038807504806d6000700b568000b1a41d0340140000b2542d801191400390400d900c0304a2817640604000d006164010183c0a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 841094694 1250 841093444 841093447
    0x6041208090c090a0209040609050c0414060901020d1805040c0933030b060d020d060609080a05060c0c0a0f050309241210030b2d0906070509130908120c 67
    0x103002e07031a559801d03680030b00c00385401078031654032100143c05482103600c80e1103080d0814007480301c10000c17407000b003044405020049504103041414408580030301c156460160300020a0000c18a0280940c0304c2d44e4070008101c0089661100700150403111031080010008100c0b500030f04c810391440100080a9002110340031007035208683c403448901035094800d04050700c824041016841d004155100b1080d211415529910b041881c900180800d04caa01c1c001040c0071000900300c84041140c40c2d0668122015002e2580d601620790034681c01825409020301c40c403040b01010900543c40000018410b01c003031551240303140100040d452442d4050072400248146078841e948560080302c800902c2c245a50700e9603541c00c1d0b51101751011a44c0701614140c140801c200d581040d0341c00c12a107040780303061402100b00170444603807410312007100c080d0000e50003800402c0c20741e4085c0c0003a00e0201c0c0002c209124149007480c00e58150380702588111111034021843c48070307140b0b1415903190b010004da008036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 841095944 1250 841094694 841094713
    0x30705071a0106231303021909060b0c07051905040902121005090c150409151d0916080c0d14120d0e0c0d060f0f18020f15040603050c04080604120809 66
    0x29000965203110091040000c2000600d5948074030f0402310041002038420031105581c1da501c020a0703401840c0c144424060340c840400d0b9803a003140c01c003060721041c40c10543d41c241401e040c84010680510107907840820034a076000710000420842d00c035140c9040002c2194203006041a10340414804e81502c10003241c0421502c2c0d0408409607012036500c003101140b00c8500f040c6142d09180300750000c5036014503c0d01e09030881c1c104000e445015416010495150380020002a1903044544c0030782c2c2000d0300700c186640b5582c58091498055540585c000e10144605100420310300708038814540c95088000c129048030b801580315114181d001d0002403c054100313080017802c6031648440081500c1c4d43c0740c00036070040305260702824080c92115070402121102c100c0e8861343d050700c0b060481c440c84281d0303402c1146080030b03002c00c6402d0010b080110705050a000d01903002e00340080c01c090044c030080c000042d806c0010001c1c64041e900544c00c018050207a103800400c080d500030105800c60703002030b860 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 841097194 1250 841095944 841095967
    0x80d0203120a02090d0317010e060f04020307120507020c01021501030b07141909030b1f12061b0503010e07110309011d0901090b030f06010308030705071a010623 71
    0x12524401d00c4107440c60515a11401004000e0140fa03407210f411042458000e01010f030080501c1c1040d202c50b4070342400a03a80c648540b48240030480b8200e400071000242c11b05117041503005076030021410300344003001d000b04030440c2c8102c4000700c44000040e0700c00c1c000c1007010b5030148440929843e4008080e1102c0d07040d516000000b80c0c001d4500d2040082e15035500f42d060000c1800d403209010f04007580342c0102c0d0358a000a020403450b00041d50004d62600105251024403204104110304141c016107010381340009814070b01d507030204242d40003a101c21031008650000c04209007901c040d62101034513941844088010038400400007000d100380561084040e01c40002500c880510034a80301060400c450700d1400c5038400881d8054000d00d1141c00495640310741d400a040607001a0122042880c942d6502581c6000a12001c0c081000420204100a00c514014402c1b94003c815151104592000b203507201d0800364041d10004840584800c80c540034036500c0041e244055010b40e0038208034100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 841098444 1250 841097194 841097197
    0x3150f1119261008010c1206081504111302030c190f140a03141801110403030e0d1a07020a110a05132c030712091206050c1c0b0406080d0203 62
    0x204010180c1c20b00d0b00041102c10405114005401840000e10420b140b205000e4008040f00b00d10000f01350511074080303140000002c1908544403500d04101013622180c840c02c00c111448030116401c01d540245101d0400506d0001310b0045800060700b030764402d8501031920105104401d181c00b0000d108562502603a4031000c421081c0ca0055417480da107021080b03080d070061800711880c414a255101c100001c0c0c0e20f1207043c02d44150500307070090003945407541c008100f5128a020040200d0034020901c2c1e280c5c00d08071054207400d4814020382c0906102d1400511000f01d044a400340140d01102d03c02d4100a01010881d501c0030082d80d03454122824000020b504104902c0244905a542c40500c400c085000e40707c030f24032005d083c00ca08504e2400789241c5450342d020344800d81d000705074690705141c041c1c8240f0410046404004040d40c858503659a2040034140160503040743d41c0c001c2c800d201406d06191101c00c58403801290000e07403040c10342e00703004c00c1c1c690a03030002419030010141c00412980100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 841099694 1250 841098444 841098497
    0x360c0f09030a0b0901051f2d030b041b090b09060d0c051e03120301060f0c060608060109020408012a0c0203070e07030509121303150f1119 61
    0x10041038032100c064020030300e4100c2150019046101d03c80a00144003c198003944c0990360000d2203c01030100d012400c44141643e100f4804030805071501041c890219507400a452600004401852540c0c1d45070f40b42d40d0794099405035140440c10100046d56442d0315413290041072804001d00030101208009644040010240740c014004554483c1c2000800070004000d404002c0c445104511010340322001000001724007406440749628a003407440000701a0390482e0041daa0790f074100a50760b002200c1240985108a17003158559901046105041c1701243c080d1a07840c1d401600c9925141c00b01d400c0d6a2180100c01881d03000c501e900340c404518080d0121403d02c103040405060210384040303840d043c83c80d4051451404200e0a020403254143c1009005d0028541200c0071144210780c10900d501c108000041000140d001c100000383e20180d20440c80d41d1201c400140e60092268404161802c03103001d03600d41d4400107646894130b46d6900e006c0d00c0b2181d01c1d28141a41e90780c030003200180082074a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 841100944 1250 841099694 841099717
    0x81507050708070506090601140405130807080403120c0317040c1a040506030903030402030c01210f020c030a0c020423060d080405031903020114070507031805360c 72
    0x14888082c45070000841d42ca103a44001166a40d103000c903c0c2c0c0d85c9504082c0185110601500f05899043c902401150f0041402002000700100d413942e8011542d8800c903021203031241c041c0000400309162500a050240309078607031903039580f10303458000c00c581c0001001807220071007882484049029540440c06880310400c9100400e800c0340c0c64035000340602c0d1b0040350301100000820000100c0400614083c1d0f00c00d404a5104045080055500e0310080000c11040c010381c0a0426030a00c0d20b40080c0c01d0104001001031421490116080c1150311800b2610040b401600012003182401d00c00c4d440a03400c1c611007000b0318954407000c0703004140050840b0784980031142c40035007400827003c1110028034005048540e01c415000c80900038069504054001d9482c000e802000c0c080202d012500c100525951503182060664090328125616515000d800751601c1c808521038480d60706c002c003004010f070b02d007004040c1088800e541241c0e200c51408036400007241408400c480000076a00d040b0307501c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 841102194 1250 841100944 841100947
    0x1c051206010e220e030c10050c040509130507140d020f1302030f1015140c01060f060306090b030c010f110307020405040f1406040c151e020706080108150705 69
    0x188001240d00949251405511800c90310743c804044114120b0301d60319208075402441001075254807640c41c0c1c000c079000500c650b00013180d50325190102c1c1e0b1001e50700c180342002c40d40c1869207800c0031480191003195510300c880703d0044920280b01040094900802050002c65948851280821040c18018130028000d10425000c1c101507900e05450400740d242403c001c5413645400c0e4501d421003101a140b4160007140008081900301300d400720140c03100e04a890783c0d480010700c4800031099a10821414007255a00c070400302f85110840d195034014080c0355804106181080340c0d0200715920390b104140b003607120403038840191342c21007898042c0000ca420044032003030341041e10b80c0c03c5110f000002903015181904100c1089410b0104020703582c011076000110710b44800030207a83d0f800644010300341031440f200402c90203088600c80702410400d440e000001c1c14185c1c80c6201030300f2200780441c0241c4c01c400b1091000a0303001e42014010140040201005000c2c801e280d049000042c0121080200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 841103444 1250 841102194 841102201
    0x93305090a0305010c020c0111010c020a0807020402070606080102030711010605031507091220090403200304030f0f050c06071212020f0a030506010f03020c060f180f0a051c0512 78
    0x4512070100001c40c1c00c680240b00d40351850034001e4695000e2120240400d80c1c1c0390740055401414070131100030411580090071850f135640c07500480303a0001d0720102ea125800b0031041d80094040d0180b003006100000000d6100c3c2000040500420848500c10f03640c2c0c2c0c9044010004c940d00021510240e100907081c07480e05445810b800c0f0340c40492038020300c2000d5000703044074003000080246140345400c2100900c020076982c40c10000c21300000d42d03024000440ca1824a460054500d031480d000c104004100c1c0c0c07500d82d480d03031140c0000a03042c200f550b08100c0484600c080c40014001c0c7c820b5414111801890288207543e07604070015a0000c040410215814400c0031510560483d00324030200c001445c0c68104060009000d01400c0750700b1800158400d500140e854024000d640c4a1011b00700606000d41d14200b40845d820b10003400c901580b0b001c0c105141c100d8209021040415442d60050850400e11b8200545000c0030220204100e4000d5105003184c01d500105582140c929000f115130aa20b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 841104694 1250 841103444 841103449
    0x72115020f1b07090c030501240e0d03110607020309060706051b1209010e01021309020702040b120d020f0a0c030201030507170108010c0201060915120606031209330509 74
    0x260400d500745908400b4503841d9901002440c5011542400c0041c0301c80080280c085055840a200701504550700745084a01c40a1051140920210601e8096182d114400c00a44c0501c0350000540224440d0701c0b419441800900850b03500592500045d440e008085011807418802d1000c00361004e90740e20007160321800b90204803500800000001c5481d464903504c228085c110030f44401c003696103004100a0015018026503e40408036100921454507086901010b54072440c01281e110340d41d13000603106a610385203000150b03109000182501c1040f01406031410301c45002c82e00c0e440e0701c020615000924115860130030781c3d5082c60082526102c60380c0a6a101520003000344548039204004181e80c001540000f4407042280d00034041c2965590300402200d4442c1c1040122038400c0e0001d004110640308030581d00c0c0d1054000050700c582d2911442008840c512103403001a5400800304618001004160003141707601000309503000001c0c0c40d1011801520700901c0c1070110209916040741d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 841105944 1250 841104694 841104697
    0x5101206080d03020a0f0f140f0c030a031e0218060715051503392106010f05040b09061e0603090f210301060309170a02072115020f 58
    0xd041c0782080714480807400d41e0140c082e42090450000140034443c4040030148a03100180c0c0781c0c451a1a00000c140d000c41c0c220202d43d1050031006080481008034000c1c08204000400700d00c04c41c0d54000490b6040b400f074241d030502a4503c00044140140300c914a20b107102e055004561404481685d40d4801c0707803034803842c407100011417004400d14203070402845c10680314426407980d000310160b4078404c100100b521100c050345040e0071040102d94124420041000902c1d000d8550001d00044d02844031268012050580c050042c50a802a100401c500c1040d1640d0002405041f1000d00040b410710021900d0703c1030040409102c0c5400d1071244182100709443c2c008120340150010f0754070b15054540c95070713401c01441d00000328440d801d501e00550038140c400122400070401803604d1a441c01004801408403884159046592044079244101001d8003c00e85c031111a0045c040701403800791008108480c0001451031449004207510001d80b0307580500b002d4001c1c2050044e2156001a0401240d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 841107194 1250 841105944 841105949
    0x30501050f10052b061407020a03020a1b03050703030906031d2e0e060906011406031501171825030f0813060203040824040201050a020a1704091505101206 68
    0x10720080000130074080e4070340188010b521013408209094036100022030780e8110a00c40607005030400c3d07170320348002884002814020b980c41c1202d401c140b82c0342e454031420b000d01d5900c12400308041c00d00400c0b1003601801500c24100c80c0c0c6000d007603035500a005854549031403c0b255010385821440035004100490709030300f4a4002d0301c10401c840c000504c0b520b0b560301403d64601c55980720350000020b0307001450255000805000d81241d0541d141c91210680c1c2e401d0103040181840803070091807003100c04074004180300c2d50520041030511120031001500300704808a050120b0015586004002242095602e040b241c1c41400380500d500e4504004a09008003400140403001503000029660b070f000025206659600b4150381116407a10b50740b0001c540844d00303003804a01c520f40000c000d580190042e104058150040d04d080400340d5440411043c0c066042d641d1560000c00c0a000040745032154251137841e8bc000d5040c9241480d0014441c004041401c104010000036030241d070300e4884c0c100200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 841108444 1250 841107194 841107259
    0xc01030615111f1d0a0c0b0c07030206031e070f0801170f07150906050313030305041a070f020f070b041203110d03020d14130b07020102130b04030501050f1005 70
    0x3d0840b5040002000390400c0200012485201d00c00e02c100700101094420340e095100c400403a500f4601034190032260441900d1140c0c41c05402c0700000036844410055100f400d0006002d10780e42ca078642074461340c05c000b815800401c800e642d014142145c000504906681e842e2710129103103088001c0c00c92900c4030354040c8505034000c6c84000200e43e80c607030b0b08070348545d103035034a41200c00303600c90004541c54001203618400308140c0c11100301c00729000c0d600c0316821a0168040e0708070840580e030860070540c000d49c0c10000054101d1070449130940d040c04400510304150000c0e003105440c03e880c0c038010f4000c0380100014903d43c181c14008242c05105881408503502c0305448a00e0a61213000e002500a000444003140c00c0440c0701a03405052030407248654019107030002d200751140c4804011840041100080d9075080100703680e10003140c0301c8000280102d614290b61a4203514140d400d51704c0c0509480d200324064000c0c03103108400d038130500050b14815161880e00c1d98044e040c60300080c450410740c14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 841109694 1250 841108444 841108483
    0x210050c19060507020f030f0403020904060f1e061a19110a06020a0e2e050f0f0306150c1903020703060e0105040c050102070b091c0816050c0103061511 67
    0x2030030480342c0d070030080c86030303002d502036030750448079a40c0260b142d100d4051140c400080411041c401880d00443c01034000b801000b0008510000070080c50494044d1b1280c17031502114807072000c419503030600444014101103488480481c2c2641103001c0d031402403040c130082e009202041007040c6407040d680305021002c0601103955894003410010025404407080000041d1024000c0e031060038044104240300c0845c40c4007200c4142407121040c00e40780c001c0c0d214800c2000410808000d502d00384050070080384028030340c5540c0d0410b0010880b0700d800d250918580d080080c86508003078100400c162403650042102c100401c00c8030316040303003084104c2d040105014500600030445003030540c00070b23200d648990080695280c03128010380c0d07074000c21311900f42c80e07000c200100900b505000d2001c2c1e0f50456a902e48114409aa0369450303480d8004082030701d0003010581c51501400300c1000b01e16810302003800e00300b001c9400c04240203107100079507010740140a90303071407007281905080098034800d46e072000c203c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 841110944 1250 841109694 841109743
    0x1305131b09080c06040608010618050a060906080a09050d0c290106020d1106071d040513020a0902040608010b03180f070f1d01090e1906090c0b070210050c 68
    0x142915840d40590210b900c503614210a03030b4207042e400c80d01600e190391200051a0320b42034045030740091000d4200d0900720a90300010352912030440e020f01500042d21401c03012400d080000780240001090007911a0400786100b0100300c01041c980c0c0c0b4580c07281b50402410206042944044a20240a00c484401284020091910303d841f56060710450b038251540e184801200316031103c15012810385680111020882e00e40c0900490b4481080161591411140181c0081c00702c0304200e035a0b512881854000b0b038214039088050b2009001c054804500345410160300038400803050007004041d10001000c00c44051540040801014030b150844541040341d64806484060500c0364080d0411600b0b40440c03071560b04620075010108040c07440c10180e00c6c15002c100903001000f00c1c00d1003401100e8514006042c0440840001d0340281004074034800b951510b20003556841d40980c1c3d401030280140c0005a45205146042000303c0c03a003552205130790401e040c02e00d05601d110b04600b110b82c0505 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 841112194 1250 841110944 841110947
    0xf06030b060f0412030816120e07080102030a1a18010513020c060a240602280b09010902010207060f05071103010f0218030c04110409020a031e0e0d051305131b 70
    0x552613018829a00c9100503114170100084102101440c0404070f0060120103115507080e601100380400c00340d0480d00f12075540d0b455142264000d442c00e41c411034680b00701740454070400481d0003900b4020796554480210341003444503891418003d441c42002c09030001302c80120300350140c130307034407400c04098500508013444441d00500b181c441c3c0e074084c1d50341e1990b070002206001271300600300c4100341c026110565034540c400c200c400070f906800c10440551143e00e030104089816403881090446c0000443c0642070001a10704150769001408110200510900c0d10341d214083c1c8800551020a1403820205500003038098450551687d2403d0700c0800c8548400b50310207a58007a680c819400d0f9500c05c0c021001303001c15207052502c081b8088508000030049401654002c4c282070a8a00d80001ea43d24072000c0000c1d440c0d81c16a01081140c2c6829900c1242c2100780080550340a083c00c00360310380312039030f400c94199000034071a2a00c41c0d0004000d40c0740c648000d400032200c0b01070010301d80c5000442e0703c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 841113444 1250 841112194 841112219
    0x60301090c0602012414090a02070b07180906060f0c050a0b0a0c1418090a0b090106090303120606020c040c0306050904030903050f0307050c0d0302010e16090b03070f06030b060f04 79
    0x2a6041c3c071664102a581c0c100c0700c100c5c482080c1e07100080c000500ea845841484072074030000d4041d00119900704003903802301b0300705402c40c1c1c0203035410741d01e00107400710710041451400380d40d400c400750f01480d01d202042034582002058083c041c1038109100300c5260f03820a0780c24000000f50141c044540d581c20051090000d6000d02e1a0381015201c001800c158540105802e00505038135000c140800307010080245070000c1c48640c050b03100740c1d0124958144601007040305c102a4000004504802d0040c020184c11010b0907204103d007160030400c0c0d900c1c1460003540c84458280440c05180d490341c400f850140b007a001030029003005400c100c0141003d01e0014a46c110500c41074850340030701e009190080d8804001c071a01540c001009048092550040011303803400440120190742d60782c0707408501381c601402860746440600340417110741441c0006800c180c4484109607407180d003201405200a0002c600d1120980d909444c6c0080c0304031110340031400622940b001030100000c04200015842d14610 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 841114694 1250 841113444 841113461
    0x9060b041107020a0902280302040e0603190b10080102120405071d04200301050a090209150a0b070c0f0b0a0f090617070504090903020102070209010503150f060301090c060201 77
    0x15000c00074040c0d2242039a1072801118802548401503000400400c80700c0c2c0c029003000d41944200d40074882440c0700001070080b0495001001c6900130404120000c203060301650700c46002e074040e10b8804102c0503141003001074100c1c024500510b000215520a11490a02c00a405900004c554850450b59084002182110120761501c1215404141d10507000c14590604410354001212074840b9170364812a80c80711100152490b0303a0111440b4030759000d00656015044290002450342458018851502c41c02004512486c0c0d110031081202d0722644100d400301c6002882c074036100c1c001441d201c0d44080b090381c000610b8480503040800c044001030010710480d449178544000c005800941903034007507510301c24180456100740380c0d502c0400503c07100a900c0780082c81d01603d056181e42c00340302210030900080c0c00507940460801c0443c10050400c6002d17000440c02000c002c3c154000201d00040000c00e40c8144c643c80b10082441503d0940241a801d94404c54102c8426200c1200a0003000ca85 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 841115944 1250 841114694 841114699
    0x7030506090f19063b0112151113090506010c030c061b050a1233080d050c06100b03510d110103020915030a05101a040e04110409060b 59
    0x49002d9554917901c221034505180403421581c1d9903030710304410849030b14032540c010f4803035460942d541c02040d0300b1403180350b545a440701d1100f501c41e446512460000405504012180352030003080c00440d82c1c211540d10b500725414500702c0760f0b440c1c242c40c00901406202e110920100342102070124608d070080058405111140d0314015501c1680e090407083e9803010070a4910482c2428100301041158032402100211b2500226021559141040e240a1450121000087c0042001c032172011080c404203800600710100405400d003801c0d4030200e684400b9000405000800d40c403503c4102200e0035141d40c040c2c0713a08040003031004d1325611a40161001c43c40765000130090211034034a1400092075a9016040112200c3d03040e10000150020362216210507030102c038184c3c11030780322022500290311a91f001600841d071404c041d50b0b510b61101441d0815000110092607059116150500791021070300990018101d580b6141412000c0b01d0743c0b220029005414001c0100a03c401d9402c01c0c10741c0b0106 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 841117194 1250 841115944 841115999
    0x6030f0b0a051303080702031c0e0c04090209070e0d12080604050a0e060c0307020c090901020909090d0c02060d09050f0c310c0e06040f05040507030506090f1906 71
    0x1c0661030021500c2c101c5000d012481c102c0030500c0802d100c1c1c40e050b54402c64600443e171810b98103200c06040f0046026081074400d40301c8e400c609910f98284031310007a0004c01d4805008220503a80010481c000042c004000c21151a03008031955640c01000e80c0c101e904400d0300107034044405c600401901003122403500840c20314002c1020b00c0d0841c4a40d0704003421400107420304d0f4a41880e10b120075032014140c0c4045118010a0703c00640e169054203001c0c001c134100041c0e036146000c00b4030288000007404404a0740041e08030340b000070b0f002940c842c2e0040c0c0c1251165905c003045d03460f860040c030a11b04064014816525080003035403001454102841048554666442d1001c1c01d0320b540c1d1001f1104404030002d1f0001d41c03914400d0940115600044908205100e08201c03000304444d50403590100100b000c0a0700d040145084c1440340c01e800450600d4280003514020000c12050071001e040f00c61582600300011700411050707100d030030442d412a941800740c165103480394640300011840c40303421800b8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 841118444 1250 841117194 841117201
    0x4180b0108060616030c022403040c0e07090303030b1c1b15050d0f0b1c060e01020f070b040c0317071406090a02011d0409080c0c220f0207050106030f0b 67
    0x28100113a66030400442d901c140a01c0f02a0303421154002e502d002241c1210025000c2c082c1d1002c00110f0350480407010142545030f14050401040d1003060358030071100389581c0750030302881c554080001401d803a014180450901c080c000420003080c02071b4120510706010040350820003d401052a00d28201c1c0c40070043c0060702c13490224000307141c8080490210f08200304071920752503c1d0b0801c800b000c0b0500700010705112194042481141540e07800c980ba0072060380b0303410411440d40703d9000c0148080d8021801c01012110800980c440c600000e40414880400541044410f42c4020055a4843c2003640340f082044a24030042d0040f010850702d000c42c441201d00d0f60303100066000d00c564940001030040c0394468006486d1030490761010074008142035410300c69600e45010f4040706500c20843c4664171000591114101806c01ca00d55201d0940020121020000700114040c0c07007281610006501c01d29201e040024410180e0040c155401c8c004004107112404640c100c4172802041d0b03006160b903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 841119694 1250 841118444 841118449
    0x3020a08030c09040b031b0f040f0203041a0a05010609030f210504060e190e07140703020601150c0c0308090d0611191806030902270403020f030c101104180b010806 72
    0x2a004040c81044054030011070040d207132041c0e40c408e41c810050b2002910304005056001640c1c81103a041d5040a24080400c0c803140d410500306074458800d040800441d418010020040342591201500104010180c00c0a01c9070003002c00740e079281b4200070004030100250001e000c58000d44104e10114041c6441314001e030500d6401d2070381c1e10076025203071108103007031022006241130090302480030001900c642d98951301e4400c00034500740740642c00800d00e6601d130882d07022110007542a40340030080c460070300600081549141c14162903200e001d03242ca4100a00100d99200301c0014040c00c1d0909058210100c0c2e040b0300c00800c910201041128a01805088181d88005a0085141c00c81640141c204506407195000d074044a00c00ac08039503981d0035101d544d03001c4040c40311403042c406929405000c01c16404100090400b0350001c0514201000051441c1c0c0301e101c046515944a45c85800404d040c4450320111000380603c0219881c1d008400d2500c0d0004140d8412100e0104d41d50f00301151192 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 841120944 1250 841119694 841119703
    0x604120504050f240a08160c0b040b151809070b07050a031b060e0313090b0f0f030c100215060f0607020f0d021302180901060e06030403020a08030c09040b03 69
    0x852014040c0031808010b4014040d080110400380c4da01004d16001d110040d0120b44000c010343e0320580c3e00c44803282080144110018010010001401914007041000488410b0300b9588543c0020008082d9518034402e4030341d041e03042504a901808408445413916080034036103015503985012107410a4840316905440d1203141400f070043d40c000c02c44040028419880744004181c00344c8115000d90b43d9a5510303081d81e0401c41c00d80c04076000810740c54900c550b4070b10030100821501c0002e008035560030010034084c20800c1d2103117000d80c809481c0c80809450400c4824426140038060054a447c5800001d440303002c8400c4408000c22031300701189280c03401510000311044000d10b4285080d60503420041281060401c0d203030480d50010b058005603a90003008001035010300c0015a450840104454680f60310821040c171400c02507006001e141e40c442401101d507101a18141c1c3d5903241c2d4181645800c903407000c02880c54000004101504000e08081c1c501081e0035142404000b0f0f9910815844 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 841122194 1250 841120944 841120949
    0x80a06061505030c0d0212010902040602190213020c010615230702220b0a06051309110d05090a1415091f0507121a18041212060509090604120504 64
    0x78400f8404030f00d07441c28640003003046a403869801454001150000420b52000368080f400c1594081810452150140070100540d590b07850f410110b040c265002400790041030100007160740e80400d48003460b041c2544041c02402800c5110004983d409000410301c40b05428440b0b0725941310030b40740302c0200400003070b00c0090b940100041c8522000703410302000700402090200083e9220850f070b8105446542451011b058a80d0300c0c1075136544245a01420080543d001e00316451400d9400c08100084c0d9050712090301c012103000c146a2079560307400c1c0c42c2c504c0084020341500c0c41c0c1c4a00308103c113400a0000c000b0700e254a003000b0380d552607103c0aa21100c0c030b10102144104840c42d0745405c031156a1003d030344198142003452403007231160381050450303c0790000c4110240030f00c80c20f8800343c6040c2c015540c54001c2e8541c10318861416a0312058500751a09008050002c1100c0c10400f81c002038014801070400649168032a10b00041d00e40c2da81d8005076000d480e04541c0c41070500c01548214100c805 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 841123444 1250 841122194 841122197
    0x312111e1207111014070b040311070b160201050f0d050610030b1c021207060801090e03091f2102030703050606042904080106060908010b01050a0c0f140304080a060615 74
    0x21242d0780d901c1480113007a00c028081007040902050032580c500303002c0207050054001c1401111700d01c0e01d450050012040007903080c200d9440341008000b80f00c2d005046583e200040032250741d06030351603c010384490181c800314540c02e20010544d964500e45030b520176032040304220350301c11000c20a100150220f80302c2040c0c040c6c1008210a200052981d031044915209101074440144030340704510305c1d42480342d5034120b40002807140703004000c0305200c3e001d600e4100399004055480c1ca00700c08001283c0304072014501c21ba400c0b107002ea04c00cac1c40b806a0307028500d01640c0490752100f0341e1f100107080c0095004483d1080480e01e0200412005c0c207110050f42d044c0c40e4404644446103001c40e0414983c4449504100080d08042202041074042801010b00406003a00d50408150034602400e003542c003d1814141040f4051200c1c11460707910107020035503941c000c901042d07007890500b0484444401c00d045014a4400000d0000700ca1500040c00d40d002d6000e58820848d140d140e5904000c04440c403840c840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 841124694 1250 841123444 841123463
    0x11103190f1d0603060f130203070e150a0207150507120908060a060f141909090b07080c0f030a0902030114010f1428082e0e070312111e1207 62
    0x5519050611100d51b5422006000710060b00f20591440b050740d00464011000504003428142c40d420031190fa40005070b400795101f401c100d0b040d08001e42d80c2c6c105110300c20700301c038039400d9030f08025000d40211450f01e85c02c081c045c0b52400060308050b010040d030780300d103450522a44c0001880e29085101e0b0800356408400d0750510185403100f140c00c02e8405c448400e6000b800d10720071664000f43c50b06594010621040c010940c9103107410a00b1550100825000500130030788100070580366202c04840c00200380f01b40180d12074a03035410180043c101001c00a405610b001403042c038191648000074129207014100c43d0f01039032200c207103c880100c00d021543d044080c1c2c01034100e4028248611060500e0f03c10502c015031561444201e01d41010581c0e400201c1801c9122500805d090720b00d189424407020006000400f42406029035851191101070460070501d081b1040030f501c1034035610707654101c070801ca544400001440c0b400341e4a0f40300148a180c465460300c1c88012030100c06503640f00c2c0d002078181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 841125944 1250 841124694 841124701
    0x801020a2115030605060a06021603061503050114090606010e0d08090f03030d060608060a140d030216091508010c32040602010e060f09030405011103190f1d0603 71
    0x2410a070300058118212921900e039280702d00d441c9400c50340198080e140103c0c0f40d003030000510007145039542010f002c540201c1c0c03040d0320022032900201c003141e078084400580d1159020400d83e0300f502d1340d00020119402e011540e00c0c07289070380700054011400d01058a0180c1c4400c401541c02405103580c850b040203208031000041804100a0282420702404808003421528000707030660b0302c450710143c0000c3d40c444042c44000c2c1e0044800e644408160341c1da41100d4100501a0190300408002074800c440b10750008041510038841c25403083c2002d0002c908458a4403000c10103070001d05000326420040400c0040c40041c14040c00a41810503110180140403060118101503d04640c2201202e00d17414649030400c016001480145080d5000140602c140c454060910f40040c0102616101c18014402030b80804001c07101102c0382400c10014101040c608030381140a81800010260000020505119007007050015500070940d900100c841408202032107800e03041403101e40048061000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 841127194 1250 841125944 841125977
    0x7050a030813030c0609080c0a030b1305012901172707030503211315090302011407050c1e0303190906152c04060510030c030c0f0801020a 61
    0x818400581048141d6880e40f6034a48184034401a800500021000c003000c03c620142801103400d5518100da48401c814a5510380022035000a021102c08602500d0401e04120096014045c03d444010303940e40c2c205464400201030821820207540400c1801002517040c8100070b964a00c111030a860008400f102c0010720041d01e10900c0104025104401001c400300d0001c03c060416424a8095400c1c0d440180402511103100505000c0c211010141900d00041c40d0502c0b16400d00b01d02000020221801d0504078050400540a0314042c100c110034406040d074000d00820200546c003040b10304c05038840b102c12038013101c0030451070340540081c80400c0f0a0410108400440d030714502010400d240d058640c1d41c100c9134000c0117051a1000c5480800108800452800c0f913501d40c50754a011941500e45c4889040c0001880140f04a6480700010000f0b80d02c140d455001d946c000081007107042d100c0c03a12002148417401072403140d01000c500020f0391001400ac840481166545108842400085 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 841128444 1250 841127194 841127197
    0x70b0103110d0c080c040c0c0323090904050a02010f020a0b0610031b0801080d0905400f0b150a03051005030f0309090a05010e13050a1e03030b0307050a0308 69
    0x64a510804850b0907030085100d06030810301424445001e441d40c144044100b004441440c0c0f0040203006004011801003500507004500c2e4a04410060b0192010b60000d102e09108140203681d100403008148000c1c414009022032490340b007a2503940001e112010300340d0791040346080c0140000807000009400d0705220488000c80710090070f0201c0c0516050701e001e0b909424100f08040080c0c01000100a002400c00c4014400050b5042c80e0300a01c0c1080049007600d5401c00e40706401d03505002865246010101d490030310501000c000581c00c03e40c580181015141d8102680d407003500f1b00040c070460345405211024460741e014000d038903120303030305a0590181a0081a03800a2035407160000358a803018080c1032403110340103010f181d032140f221b41040307151640a40701450840c5060014401c155000e1420354014490103080c140740900351800c0c5c2d25100740ba0030000d00011340c03d0f01a0810317110002c0d9080d14507210340c5082c010042d00744141655826030784115a40600340c80701c1000824400070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 841129694 1250 841128444 841128473
    0x6030112020d060614010909050c0a08060315011508010b090105120603011515030e071514090a03030509330a0201150806040309210b06030c0d060b030f0102070b0103 73
    0x18042800b0451a440b190110361151380701c15a00490f03659040300f5503034094640d1016102c406070070400d40c102051940721a010301031200c01405800c03c0420342d04e650802582d80344052049101e20305686458012140c443c01c807080e880860180000404c490000100303503000240c06a54180c2000f1001007492001e1802510440d099540c8803481082082120610b001400008040d0641d614004000a04039000c03983c2c04030164100040901982140401c00a2004c0340780c40d000340602d011420b030b2103003440340f61050756000140707810020030181c004019020408086510859006008110f0a0340224054011940d0300e20381713008911090701c0d080600b8084030b040c80000f0b1641030102c2c0054209519401034005c5910120400c41090f40c050541e20180c440300c52411589600150600304442c08110010300c0c86603040005003454a080107242d102c0c004c024000600c0000e00e0900200400d01d20340300764040d0040903041c89003c0b10500813602e1036039008071a00c40741d81c40c545a84080d29542c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 841130944 1250 841129694 841129699
    0x801120b072001060321030203241503092a0102071a0408070803070203061e07030903032703030c020118060b010302071b080c0d020102030307080c09030a0308060a140603011202 78
    0x2440c0e100c04402c0074800c00010b184522048190000586801a078100450860104050042007000780200c00030052004070314040000265401000c0001076510107811412980e2407400f100704415a1030001d101000d03072001c9003070200c2c00f8600d4203004010b4603106030901d0141c0d1110740d0030040148001001c510fa910b082c0d1543e07003402d460b02c04890a007210b56011050311742c4081100403c0d031a09104080d000704010315032100d4058901c0c12040035513001040101410742d511545020305000750008205603840f94001c680c4d5001311013204103000704048082e00080e29010030384203094014801e0301c420740701c40c5201002440c1e880e03541002070626645041e040540910000740041d400503401141c20184030381900703c25090440c002d141110034000c0c030b03101c0c01c0312911010150740c0100440723810150358503140c042903507500d11039000b42c490030f17071000c0e0584500c0d540030052552042d80b0900842d001c9174021042e55580206d60500c3c03220440341d5502c084100010803c0c150008000243c2c24801f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 841132194 1250 841130944 841130987
    0x151503011409090705030304060e04110307081612140403170907090e12040b07060b0619050c0a080d09050705040b0141030604050a0c050d0b0a031b060801120b07 71
    0x841700404c2c1580c1003079120760302140c00c43c60582a00d03c0c09024161990501c25101d50540c500703d04010a5040060528a8034220941d421300c0814410400080f840100c50420304c200c8e05c134060103120103003003200d040e0001400344c05100310140550720042d00800e00d503802800150b007406400c500030b140300314982c00144282c0c000404c0c103541d07000c0a04010300326074081c591101d0311400c1220a4580100006105a4080008428050000303c01403482145882c0803034031140000803280c60000390150140503e08049001604110b06400c210b0a07030b0711440950324019941c070140010307101d45410007400324600511400c1c540c00103918400f48100c0c8107100384002c3e0fa0200314800125007400d28224040400803c001c0a81080c0c000d050b086082034200b0000190140c00c02000b074080d0504092003a9101c0c1d68071103440e681d036403442c4051038000304044042c1442d00740301000c14a191180c04c0c003280f8882e0000030101040206251441e420080c3c00b891a61180b60460320f0740038110245800c03604 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 841133444 1250 841132194 841132199
    0x6010f06121b020c1005040e13050f010e1b010806150a050f1c0b0d0b0f1518010501030624030b0a09020c01050403020c1c08030703141515030114090907 67
    0x2120b01507824031501c540240c0151690791040c8103c84c400d8492680a0110800c0208481250010b200e9480141d41183d2258401c242c40c29500301a00d45a110b050340d801c20503400c40f1a11f001c10440c9980da01c6042e218002100540192018042201e01c1a0321103a08403910230f05070400ca0050074244901d1030140d03d405180460303c07109410008040c1c0040b1a80c0c01d1040c561030240c85280240341c000c8451880d54105035860207102c0e4001055210040540b8020a04000803d00030616125004cc0f4a41c101080001c480740030031000d104003400241005000500918281c4280d0a0705000f6003c40c6c2d86018001130903170181001c0d40c013003a04a0902180022140c0c01c034400340c900610220300220745070400e03044c001e180a403180c511911074103440d9074034800c1c0c2d910a61178030f0741154058445070312550742d0035080e802040000c034032200b01c4007100100032101c207000e0703803110a055040f82d0360143c0302e11280c0e500300113000074010010b8100c1e64518005461070202d4800e41d00040c42c0381141d40168 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 841134694 1250 841133444 841133471
    0x207030203060c090a170309100201060906121a190c0c08030408190203040602033c131239140103050109020a081603060803040f0806070206010f0612 66
    0x20b0116106410f103500440c0c44411480c2035055078000b0310a82c00d18451084171160410f880e0b12a50110300d2080e0100a0b403140881c0c001e410050040090607010041325923035003003800c80d00c80481030840c3d50315039201e01c0c060814102000305006801e00707034490003040c0c0e0307603441c00008184c070031411814032403d038000c8000501c0030700041d4030a40c890729030503840304860100c0c030002c041c1c40103030700055410601090002035400000ea0b10064107070301c407602d86814a102c1500c03e02000c01c1807503a00a08400911000c6250400281510040096070035811669080b44950b0340e450003c00510086807484000c94400440b000003200d08841e03200b01c410400b0280302c0e115003d450ba4801c0040b4842c0380c2543c1e1041da0144900c900501202c001035103402502c4000610350a40144445e034031707030100181816180e10940c0f00c00301a0078840304996446891f03110984000100303204070141c0388610f0002030381e035900c00b0480c18100c42c1d5200000c03100c1400d101003034900621030b4040d00159aa0394444582c0d24 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 841135944 1250 841134694 841134703
    0x6190902040f2a0e130608010905070302031216060518060a0b100810060819090804090f1e0c11030714062404090c0305030d06090501050a0e04060207030207030203 72
    0x20300340c04000102001c8040d02400989100f0381c0c100c024540482c6a41c1c40183c208811398071100040720301040b0542c1d09041100101441d8001560a600c2d1400e450200300001454100381e03130003141160404540348070302410381d1041c1c40c1f0381c0042c0080300e0030450005000f0740042d900032909081051030b0362035014100780781c0f80e02107030f0b0200741030b0300e640303d0840b42c0c142031081c10000d10305403030b0003400c2d4500401b6509800784140320304410040000009000c0d008550300410744c5403144441888522802e0a0104042d00700c0d000310251145403908051408005100d0b031610700ea40d07102c12980307513404140740340b008140c4800c041c801d000c9440c8041014803020710040281c0e0348100d0f11414142498000b0514000c8010102e688265640707140075034030f8115a40081e1013000840c0d01144207406480c21a402c0750055000402900c00070400c150001d4494001e0070658240c2002040180c0e03a4008002d4411241d00c1018201506600410003060f0395400030000d29001c1e004843c00140c0c0da5000c0b9141 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 841137194 1250 841135944 841135961
    0x5062d090d030b06121003060b0609030606100e031501030c090203220312021b010b04181103032802100c0c080d0212040305040e150f060319021602011806020619090204 74
    0x120746d1114000d1040108911400c060064141c0304103003000980c40c0800da50f40d00140025204a446803100c0145902c5111310300903200c401780981d0741031144e15284840003a0203000481c0c03018030780d0f800440c81202510a40c0d02c036902807c0c040300b0607c1c562002408009111005070100b007a0307030b5440080e00540d40014916901e032115040e00320070712040980c0c215240035901502c1181000c81e0035880c07040b004414203405070080c045035400003007000000d2541c4140d14003036194003464201c0185959500e0b0b195a010071650b002d0700d1110008954603422190340c1c17110307480401d03560224103020a1045003c2e003204810100c00500d0b00e940907583c840009000c0701c04030001403000a051011101025103030340c0000c400e818012100507841c0c0000d980c0003008013941d000b40400300c0001e824007080080d140c6001c41c06101151344440e100000c2c1038018228400f603001ca031601e1302003001040e1400c9094100c850640c00b0f0407041c0c4070030840010a10011002e000c065844071a40b101507900c03131140009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 841138444 1250 841137194 841137211
    0xc1005090f07090b0d1b1d1f0602060c0d06090612023a06020702040507023a0503041506060f110109020121020705062d090d030b0612 59
    0x29680c80076035855103031603500d401c100c0510f42030410001242d191600103200391584100c9100e035202e19400420210076596101e240c3c8030b4412929185484004a0020300889604a40050001c445288000000c03001d10130000168003190005814080e10700241403003240d80c03030b4046042551000703080282d888a030440042011401d051800714900a5000321000b41844445e524141c0300301c0007100104861490356070441502a1100304100c000d40c114dc9a40317074020010851828580c000130b44d1000c003041da4200084011204148141c540701c00d22075190394004aa09580880003003c4449030000341c011607100480700f04d102545125409042e014010340e56403041208071107180145203140d4102e200400d64074102c000009070741e0000300f030150303d542c8030480c22144480b041e0080092007039001c0504140594403c6c00200b0303803121080c4415a072444020401003505055082d2040c80690b09102d1541c040c4010070100c900a07003050030400d070700800741810600200708290030644111200f45 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 841139694 1250 841138444 841138453
    0x120301090c030b01090f05041802060c0604020418201518040501060f08160504090623040b090708090a1e150608151008010c08040c08010b090103020103020c100509 72
    0x1104990b151080c40c0c0c0c03440091a049800a01d0b085502c400b81c440c6010302400340d61210079181000c0021001075981640c00360419a0b079030309900746c858407100b0030307501240b1a42c20019101c0c50403194140e5420810f8001081c0c5051040d900a1030031000d04240c48160020401c81110207815001d0380078091800500000c0d10a00d00207000300812250160444d80900c10400001c1c40c44a91110215500640c1c6111005071401d203c2816104e07401107502980000d414030a001c00c0f1580c0c5081100481d0039074400b00702000741200100020f81e0201c0c200f0503006500c0c840007544c028458110240c10410401c15510000c049071101071041c0783d040b00c0101c0700030311141c8290800200030080344540d4040901004000c0c1058012611b07405104803810000c102000464030801c1e584a9a0004098a50080001c03010850340a000024115020ba5501c80c00d001c3c0020308000c180030722640084024540b241a80c25a4010f4001790840c61081085115032880002c40008a100b141e014810820050 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 841140944 1250 841139694 841139711
    0x109050609070f1a0a0e15040f08010605150304020925030504050f0f0303060105091201020724060f061103091009080d02031e0f0705060403050d0501053012030109 72
    0x62a0b400c02d41c0e4042605001076001642200c903840040c0d4221713034442e1030a0051196503000090f410340c00e43c20a584d01c448005800540c80c017243c0c0a40c01154100002031240c540d58404004141c80740340f045000003041000000c006180515001c5c2d80095801c2e24203040c0e040721450000350b032109404182c003081e40c0e00700344010307c04100801504014503074010320040341e10360640c2e5164000909880d060100c00b180d42e0740e030740d03440308048880c980300c0c50002c640b580010309000c2100c907004170400401c40120342c500003090754503016841c10b5440c0111301c0c0c501d503854050100c42c4507920190b044217501046c071400b8416901c3e100c07582c9918255a41b02120315042c2003403541486000d0200c141994800c01030400040113184c9886a04d00e40001d20640710380030442044050f03c90301c0740003003103401014100300825805c403029100c001402041003120340c2e01c071003c1c0a0302000003085084089440c01e0750600c0d00a5404040c4610a4103805403805032521036041001c5130020782110540540300d2541 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 841142194 1250 841140944 841140959
    0xa09090c0303170601120e03073512070819330303140705070305060a0e1002030103050604060510090e0c1e0919021b0a11030705060f0c010905060907 66
    0x51488101c0070f0000c2e00650801c04000b820f050081081c5c48091034071202c0503180c0d40024400d1b02c1ca03007a04601b04503000c2040d80500301414050300d03000c5e03100c15101c1e658032640d0f140b9541580d084810101e0141d0181d100d4000580340004000d012442001f14811051100d800c5802450f8480c0c4401d040300c00b00e034050381c100c6854a18021071401c00c214171003a081000c0396012440709001c2c404000e14544e0f40100b17007416402d0075026000503210f44108003d10803021125400461649902c0301521070401c03d6400c1c0f03131705031302c402e00c40901135a20090204001c644241e1000ea0000b5001b50030071a41e95680d1035060940d0b00c44416441545c0100c0039000d010b040c01c8818170382d103601640701480782021400000c1e40d04440900003900742244c2003505414258654115460051a4050030142c54041c034041d0f0355544402c10700300c03084a00d4440c41c6030603080000e4203105848006000d1030034000f01e0303101400e883d0030810411001c0c0d92207040340f401050007400228000c0b926039020f8401039003071291 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 841143444 1250 841142194 841142207
    0x150d080306100e0d020111010e0d09030b0601020624010e100f08010b16030f020c041b110607091703090901030b01030b1605030406090218010905090c060c070b03060a09090c0303 78
    0x54000f88039403640c01c0a46661103400d046001c90342400e000f030f00300c0420902140100702d81c4040e40c84034800d116031076199030303004280401224800c90403c50181c1d41c20004a13282d04083d1515044406039181c0d416048004c0c01c10b4168801d070600d48842840c0b62031001410a80e2021035583c0403904400d00441d0310355001312007501500308114500d2600a000b5440e240040c440b0320042d0401076001d9075804014402e00880785021402001070000314520500328000c03030000051000800d04504040d00461004581984980c150340c0f5a2849545819103078131521402c848003528501040000d020540c2e102d05042d0301840c001d000d414050360551070a912600c101501451413144804c0c91a1140c65004049a40c403983c420008194250144045135140c1420510f148151b03e140c400400d1800e041e90180f8805c140c1c81040340c940303400d10303000e00c8850b00c600442d46c0b00325080305000f403144000c4100111f40040d00548501b00866035414500304441280000f214a031038660410401c0c1680090b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 841144694 1250 841143444 841143469
    0x9070815011d19030c0e01050f1f0e130617010b0105040b040302041104180905251e0506030a02040311060f07261206030f0c010c0b150d080306 63
    0x9003010700104207010000304615600c40d042c4250300d058a03022061403a00f81860055620038510030b941a1108442c0f40d03405d4090103100d000705582120041d080c40d0001d5000ca40329000820698095030035402212107281c2403a10035041001c0400b140e40070361003403085500800841c5200b81944842c0080182950710941c01e050401c44188014844091402c00f11400c4a9048800060b080244151072056000700c0d408020313209440c1034004441031040d08554000c6200314241c402001040c002404428031200c602c00f4030500c3c1c40400c0c44104280070224000d02c245100780c90300035940d0310008816900032181c070803c00f90080340820810111281d841c00c0644201d6100b800c12054501c109041d0280c3c3d00c01a01c85868003101c451001c9606a000c0174110f40c901400741c2c0e0300e44104a007003049100f6540305000384154130f1054800c02c0c001c904003100000507590f12880c100951203200c5401d201034050b2185542410000f506982c900c0c598100003881009003586a161901c1044414204007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 841145944 1250 841144694 841144697
    0x106050312070308221502120a06060c031b1704230114070f060c090806181905120d1b020604150c090e13050d05070203060105010309030e0907081501 66
    0xb848100e000075045014150b04c210741c500258081c0400703120907414070310383c2d50300a4034181140e0400c1c017218103907030000e1240070109040ca49080d1284c01c540c20442c0c04500c18000041c820100e6900024880d0885070440700341401c2c040d0880d22203803076690324144002d010007042600000c7c00c1182c3c100346051700c09200844480c96607560300780070028080310b022500c1d2490904001a03400c040182e140300c208a2950060000c0014404010014002507400d0149503401c1c8120340014640385230310941101c00b00400e5005c0c207040382c000e1150061469003444121800c0c0103580840301c41d040c1030030180680c0400e1490104488402503031384883e600c628143c2d2011500304000304800703d0441c003c9136080d079140c040d002450050036102240c8840c1240c000007059440f034403d020311f0060003000850f0041c007400c10b5508001d0041019610742c071944400070341503005400100100e40c002c0e804099086e02a04014079142c04110020380184022140300000c918584180b01190190750384191102d0700030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 841147194 1250 841145944 841145947
    0xc04080d0e03120f21180a0507260706030b18160e131410080f070e090f010e0318030a20040209100c1416031209150809061005060304151d0106050312 66
    0x94980b69299621400303102c031110700607400d8042b002d0010411030440e03040d01042d0f814268582c0d4000f000381c82c4540c03180d88108100740f41c024612a02c408614041c0034150002c42c1c00c040d40040c140d070001204140f130740d8009c44035140c0c68400c040b180110100c105410310041c0161500300c42040d06827810b600841c402d41c1c818245200d05140010380396090300d89841324180c281c0c0d6500c4d20580f91403075400c0c3c08001365003041d20361011114000054000300c0704c0344a01036450200403060694600190501a20f04080c41000b80c102c90350031504402100d6000d000907190461840102c0c5d00c058003014600c000405002c400c100744543c442508a090380e2072030103002041e40030f1403d9012445580805000c0c000904c0c1040c42181c010a0800010b00c9081c189516480c941c003400b600c2c2c15401c40340025640610f80000390014041e01e200815104010f002c06c0c1035840d00c1d107d1110f520700c045642030b240f0360ba030040310615030544951320000640100c000300d00c65041a052508010400501031030f420380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 841148444 1250 841147194 841147213
    0x40305030d060b0c34080c040e03091f03060302091512060702101a030d09030c150915090302060c030903070e0c032d0c04080d0e03120f2118 62
    0x1010402e021241c0703010044103050940307441c0c00c981c880320300e2400c043e0b0b140e0f50717030300c00240c400c404a1209003403501180c04000341a6041112a201c0c0300c0c101000e60310081c5030030407015554078130359001102481490b000421a80302c0c0e001c1482e0b0641641c05030b030303401c000a0b070030701d010b107000341c0122000507403a8098842828034030710103595a00c046040700101c5440343e900c00c4020081c0c6481040b400402001c4818170034250001524070641030009451483c154000840ca450300104e1031880384001d6650001d40902d020440e10300800f4400080d010440304040c0080965201000391608034828000786680d25404400c02d8507021039544410000d100c07940400020480e000c0c01e517a44990010b008010000c82c401415001542410b41081c460200005122880042d6400740068603c41c40403501001100a004d42d020b03500d4411040e4194015a4400c0d19000502c0140402000240d842410b100c4100040300050380401901464070b00080f0401000c04a80d24050030a1010319001d0000b480 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 841149694 1250 841148444 841148467
    0x1a0a0e0106031203091b031a010801060302010203040b03091006060203220f090504050a0510050a060b0309071a0f07120f081509070c06020a0e100306240311040305030d060b 76
    0x25024407070f042c14503940e0800702c000c0c003840c0403540145070704041100501c01d03180d240522180320f01000590503841000c001141c0004144510b01c00c1d650140c00441c00c3c24034056495200da480140f43e481d070b90203010400b1001c141140034030b50140549030051900c4600158450240a880c50001010700b24962010041e82886a00110907203001c114081030365030756410400e2400001c054010708902c41c1c0041c070200000c81c5d5011601648540d50140849a41c801504031070340400e4609030003c0e008880200b02c04211031061881c040c041e00802c1d03041080f0304101c0c0c00c543e00800700c2542c80100d5600700c0320080783d100724803101700119030400414909181134103456181032058a42e000e24114804110100e010f001090f141079440103055669560280e030040203020702c03000650088100781d60b41401c46001c3d006807400e8543c1c59941800c41481c003c07440394460007001011052580d6039482c41780e45691800288065401040211364808010304071008071105507100c88410113080c4101000c02c4c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 841150944 1250 841149694 841149713
    0x6181e0910120f02030106031a090c0f03030a030e071e030c09021306031a091e06032a120f0708060907060e010806040608030c0706140c1e0a1a0a0e010603 68
    0x82c1e4024940d4075461881d0303c0400d004008640001d010070307661800c018041c1c074605c00382500c210786101c251a14860b24400340200d03c01c03c02c12056140e00140500046c0b02e00c254050541490701004a615495440c000030b030350303c0002c030540c1c840c000281c8000d005000c80b174803035080201404601185054811810440000d030207018200c2019101c8001c080c400340c0c00484410083c3c1c0003131030703000395060822015034a000041c0c0001c8000362058001011341c500812855000354601e001001090000c8045461074038050f1015948014040c10456444400f0070940600c0c100035002400024100170708c0711300d010b600600b101090b0303008200511040c0d5011030107501c0c0b40004c0c01c2010030780e00c0d90400203001d000c460304412107520001c620244d0360040081e081c403c6458580f03411002c215101d0403504584222410032590341d000c00c1d801525491075040c801c1d00800d40009550464209a84003024180404a00608504000700f0303c052001140302c1d0071401280c8800030050545559182e5101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 841152194 1250 841150944 841150979
    0x5090f0a0503030910031b030c170705030c0a0c290c0406021509010914030306040606050309061302130c0c110108090d0e0102100e0a17070503070206181e0910 70
    0xd54030500d0005d007814002c0e000720600c4400314a2506000c0030306000200148040c1ca07405c40003d12501c2c43c0d80d410100b4504d0203000d924160b64075843d582c0e41c0340c046144e42d40411a400100f09440d030950000c0758515400049404040c03009103203100740344110008114000c2c00d403480300b0300100810804550006145803050411041c0c4611130f41e14617170a41e0041c1503000d4060000c0300c40800c070540841001c8005c62050808840420105807180c2d8111182d020460f80c070300031580325001054020b2a01c0421070748180c8000c1c0240303c10001460301d17000b038031440c002a002040078504520b08001c4408480c1d0003d650038038010342e20b40743c0114582d90f0703415880490020b0200d03070905040d499109110fa054000c4910070244640c036440880c0545c1c681c100c01d01554250341041a4900d074144001c01c0f42e0b580da07046401181414619000c0065540c004c061040c030350b2010306403070b00c030b1611800c96445d0111384034480d01c0d0300011b100007400060b060003400030709801c0c146a0700703110310700350400603190 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 841153444 1250 841152194 841152199
    0x60e2d0a0513050d0c030f09050f04090f08120a0506010c0b0403231b0c010212030106030203070917061905061c0510021b12040b0f0304021f05090f0a05030309 70
    0x4854a074040b0040d0028100304000c0d200f07008642181c1060ba0704406003940492080e91400380d0000c0ca6041280c84100c240035031544030000207081509494981c210007d030038040c0075131400c0c2803a25a140c40c0d040d4491140000012003150400c40c04010502c64164400d000f800c1980c01c1100568030503031226002440202440768119609200c010707942c4808400345040d462903030b0344889800307030040d1400c80c1c0f0390920030a200b110f8120120794030100d4403116000b01103181c1415039080000030340203034100602020810079141c40020b901655503900900d013944443c00707804075041c13004146c5010b108480c18820b00504010500070b0700c0e1106400d810000400c041c14244034407892800170300300442d907a14050350500105051126004a81010030f01b51003942c21148103140300000207034103024501c01d0145284040c04540d5280c62550021580f092004200c0070390342c0107800d0b042500e41a2220140d0000d440031555144604107800c010944010440340e07100517a2411002a40e2841003026060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 841154694 1250 841153444 841153451
    0x60518040c080f010e0601050a080a121815020d03090b151c030e1206010f120203010b0927161a0d140609011d0103081b01060e2d0a 58
    0x40c148804004040060902ea0060724540350b002c418040c080e0030021a100914080c680000480b07280c03810001d03040303c1d598409011000c141c0d4446811000601c51003200740300c0c40303081e000d8207480500c5075203005c1d00300781800d041d0036618aa0000d181940d114102e40a161800d41c00c1d8000c1003840516a9010311228014403115134818082aa61360b8100250041d8201201040e0b040507008003009d0081e200590300e0611600f1280d8a2035614007080c0310300001e01c92820418408a03d40203420406c1c00c0c0040c0001c0340c000320f42800300d4000d6000b1121281020443c15050303101d07400300485031415003401c4004141c07001c0c6e02e8161030744030801c504c81e40070410804445007100080d00300641d81c02c84030721001000300104075541c641c060b06045030034038032602c0b081001085d84401ea503c000d401c442c0c1c40300c201c22142e0075540c1e040015808142c542d801c54042100c5515000c200340100005070542143c0c640190400544010040c030300710510307034150350403d07540314026450801c003079603c421841c43c0070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 841155944 1250 841154694 841154701
    0x40c090e0105131104090f050105090f1f1a0303030f07090902041d1302030f0a0203010b010c030e0111030d18021c080f0d0b060c030307080a0510090908040905130c09060518 76
    0x4c0c00801040704e0007013241200103c000e00780311044d400280715200d2f00d0103079400b51104074406912903540100761b8000c81044055135650300300650040a00780d1280203400805054800000e00c1c580080780d04a134201500010800e007158090b80c13210041c04982000e604240c2012284131410312000380d2421141a008000341c02100b0301003202011940186c02c0d03400d0504403441035500c505508506902940c2444d1403031046521a4045c8012985c0603a0b070301c8681b046200044a060043c681d84008602c0b00f481100040c24261080e84005002c032502040341300c003244184000b507003c134180c190402e412880c60030041095070080318403078203031481c040d0342e41c0e86c0d0344802000074003030204003582141011800410260000009500500e51900c80640c2560303840e0488060700e0701140c003000c2400c46a80d080000c0611900b1502c8400d10500c0402d09107900c80403202c003201c0d070031a60f8660340c1d281e031200003042c8190b500c42480504071003d000d111407400d00c00480d040840040000c05050f1515001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 841157194 1250 841155944 841155949
    0x20f0309060d0e0a0f03091d040809040c0e0a090c0e0411040501050c01090602030a06090e070311040b01050d11030103020a06110c10050d29060418050717040c090e01051311 76
    0x741100c41703510180d88000550b007410020880c501c18001c3c0e00003180003d00700041000e20503181445190b20000c420701d004070446c184009050038100382001d11403040e03c0b13a0300d155100d820440140154000c0081c00c1c0b03c0c140e800600d2080300b4078145004901d066902c0110320039400c112000d541080c20140ea6900800c0002c07801028100c10203085148007002380113100e4695040301048591640007805850030f518055600e4180610006000c2c0494040d04030303250501c2c0d000a0b100000c141000c0d4107081107030031482c0607141e00410100c20000c1c000018030443c0f50103100784000c2c0c105031401c1030081040b1004030381d680c141d0ad4000e6214950820045031071500c228115903460404c040c1c14410f04696184030303640c041507070065020a02c0c14089500391801c00105480403240400c0c10201c2c0b030904418500010400a810700d405c01214401d0b020003480c4a20016008078451842003800318039058000d022607142940c04d41041e418401403241a025075101011213581000d040310849002400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 841158444 1250 841157194 841157203
    0x10302010e13111306021605040f06030c090204050102060c03011a130314010501180209030606060c07050d030f02282409030207050f0a05090103080d02090d080703020f0309060d0e 79
    0x102c0d001103041048094aa00788000a4003444044000d1030340b11588543c000d9840e40102c0190726071031001c24000308007030f01d03041c0c1001250400001000484c581c6a860b25540312006401041c001600042c0c104a81c0d64108100765112041d0711036582594140b1a03600780c03c01c550404c418841c000071420001000362004100000d41c1d2000d240319003c500300d14060b0113072009128070006601445d8048007040c040b4021602c143e480100a05070a90303600d801c120b00da0304012450728240c4141c407400314460701d9046008600c54000d0b1030f11452041d009100038645007c4061200c51031406891188040c405039050300405680502111000601080d0000307000240305c07040d888a03803c1007002024141c022070800140d401c182d450194002041051258001a40c4583d80e00040a100100082640c00c405080f800302c00d90005441c2c000c400700080e4880c800c506040c2c6283c80300140c1d840400d5010040d45981006e100007860610609200003003284c05950380c0c00d20b0302a282d1800c004455400c1c40b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 841159694 1250 841158444 841158469
    0xc06050f0d0e0c0a0b0415120b0607050313090c05030a021b0105012c060307260106060503010503011425031e060e07080c0d0b0d0b09010c030f02030402030303010302010e 75
    0x142045215941180e01d6582e82071101864007403241a44041485040d0104482c1a285440b070147c40c0038200f20822501c0000c1c121341c090550740c0d81d1601c4410340d520003000307010160040300115210b14604000703201c002c000398030146401d0300d03200000c2c500d10f401c038040c0d9900c0303100782c11300588542c03558207250305e00c1207141c1c01011907518000c004035a00c803120088464403000500510003001070b0740c01c28500418107035a210f074982d01021040090039401d104440303250441d502c40d54090701a107081d260030360300140c01510202c0c030048014007131420244601104400810740020180c02c255103012240790315100c2190603503828503201c2c03600c1c500036041241707488840d4100f0903401c0710442120b0000c1ca03042c000c089502200c0d001203540580300b21040350096661a070601c0c9030005e0702c007030f002c010000c002c40580c1000324440c4000c04a1600b400581c41010040c00210b58042d0192008040f900c1c04103010070030030710510521015840000690341501c0d4203003050700d10501e041c000259101c0180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 841160944 1250 841159694 841159717
    0x304050109150302071a01091107020f281203030f14060415030f050a0501050708090327060d09140a030504261e19030c0b310c0b070c06050f 62
    0x10401419440e40c102c44842c120792183c0c8e1700b004411588855440144120540a940b00d6a0784404841a140150780c070511000b0043d0245031030000003142c15039040b1240d101c888554002000d40080c96014021140b020b407031110708101120844451940603080a000680a02da84041038130b41d4911911204000d16000401a00501c41d540740a907074480c8502000c90302c070f50828000c200c1460049800744c3c01025810082c505210301600380110040e980c1e150030607602100e0465820586903803000300362100b1503c901154034445410607100942d2000c000c1e2803144d10404140300400c1d80502950159800c21031410798038900c0800920799000c0641c0e0080c00750140c0030300781e0a90703607041c6000c0b4038545400090b204901c4420f100390444508812000c0d001c5100d40d8492000100a101034590180301b040c1c0180648203002e05c8030313841c60811080020680010030b01c2d0b40500100d035030604020005003060501c0c0081682c4d8445460504d0300c220801d2040115842c1c2c000c0218100b96217a040c4a03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 841162194 1250 841160944 841160963
    0x18040b040e060406110c0a0f020f1e0a060e13090c032405070305010605030a090c150f090b07021012090209100e0f040c17030c0703080306010f02030405010915030207 73
    0x507100c1141c0c6401e41940c0c210f0300c0d10b00e0f044601d810103412006440d0074810071000b81c170040c5400c0e2207448445414100c02c031f9208074038188240d15a907c140c8c0780075101c3d950303442c0700c0d00e0039003c030041c0100e01030290400342c00d000c1d8203c2040c0301e41d92106a2070314202031107180414205000e161200003550030360001400c1003140b98a10258190b6614204019020103d0502480d260f600c001c0d4125030f400c3c020080059800c000113072140f070b05900445c0c920f500c20606040300903542c4621b440030387c014039a030f8000145000c1c000804264062000c41c090101c2908461403c90326074001203900660080b20402e000c844481603400d0180c03580822461a005003003250311b4a000010f079006c1d0101801000744041545021410040341c690354207108a078003a601c400c41604284100a2420b0081c218002d14401045141041c0900f803000d000110300c0b42d16480d40360700f4484005001540d0041c0d00e8811940301748410081d41e81d0104101d000c46600d01c400d007001d21030451084000e1302c01c280f4003801101d41d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 841163444 1250 841162194 841162211
    0x10180b0c010b10031a010804151a04510605092d3109020a15090e071b03090305060105060f0d0b01031409010501180507020318040b04 59
    0x381900801d64002045480b00d42c500400c820039021a1403549114816018611040c001c1e9402141555003150084050000c0c880706e01031110160b030f11444948821740c40c420007084c09420a40210701034444640d104070966140c04602c5071b05c07100402c011f080707036013000d030000c461009219069511982040f8003d8100716116000a41507520a83d5000d0003a034102c08241c2c0c50442401c40003819255032210480044054403c0041201407200e420f8103425130700e40d00d0040c00c08610301601106002a00100340040c3c0c1e801040881c864039404a103040d2009e100714401542d0018645041d610311402c3e140581d1102038085810890701c100495458450164500502d03400590060459100c1c1c003c0b50705a81c5c845040c4041c1c1d0261403038036001d049042c440c1888156650f00540402041031500041c0a030f0200c406070b8207544113580c040d141d65910300044c41580135070903d040c41400004410700c00d608004e50000d6803880b80e01000083d444c003107458190203580d035401c1003c07414170007441440800c0307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 841164694 1250 841163444 841163467
    0x3070f1b1202090106090e28140108070506030c071218030303021b012018040501033c0f020d02040c0908070f05010903080a12050420090610180b 64
    0x3070300544240c0c812652200000307580e43c400c0c0100815515400b940014036150b0700040d19800d816580c0c3c68900c0c64412019500d800f21620038001d41401900210180e035140000381070401c081c0742c011a00440341001005142142c080072501c2d00d95106003400806160800e044420080c9403c51458240007032100006040c4d15030040c0c507170000d40001500415864a054a00b21101c0b4496410390b01400c5003c54010402c0d1700142641214070004450188402c2c000a011600d00344c008444900504081c00703500c000f2050320705036582c42c11020300507526419801c0559440b81c15401803603000081003e00454444090550583e80e0180c002d010313441d1042d8000c0d011414074014550356204001c0700040e074004068207501204c206854045602d41940c8030b4018550105a04105100780105c0001240c601d6106c0c8600c900d00508122800904131003440344140c45c4031101d144a01c01340014400190380715001d1041d68160350078591508002420b04c1181484c982c0c5c0403107400103022450400b040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 841165944 1250 841164694 841164719
    0x2010c03081b070605040201082511100c03020c07060305060f0f01110d09081615081315090b1e01230607050601030c15080106030507030b0603070c030801090e03070f1b 74
    0x1b24801d0b00d5a520395940ca06a005100d450020000103258401d41c01d010400d0051024030140c030a501d0079503a000604503448c2d0140c0d80015440700c0040d138005805003410300184041d50142840d072600380007034144040081c8003814410400303071286003205481200c41c0c0c040d80c0400180b451010135212621a040c001a040710224401d40f02c42d400381d9401e84400780e401d104c184c0240c07140e40d812140e01003608403040350100c0004101340d8402070120b45550200320301c0f0403208520300c0200004500721140c1d15009200c14805041b54403141c42c016a800000400c00d080c0c2d90640720f2402c90f0802200c0e0901c81307650703200d01c400388a40c0c0184d0009207907020700001081c6681601e0041054400301655840c1805039000d6103142c002c0043c560b40c006001c5035100381c01550b00200d02e403401003030030465580013500a50042c1c4080001c5800465140f041503000320005005188aa50402000c000c1842c41520780c0303e410801480c0500562406e8208250f01c00d850044025024200c03880c1e544603078006480c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 841167194 1250 841165944 841165951
    0x1704060f060e100509010f0e13020a121b050d2102011104090608010c0e0a06111609020c010f0b0f06070c09110a030b040b010f0c06060801021617040302010c03081b070605 75
    0x52240e103000807c3c1c240f10305500c0d608860340b98894605a41d1081d00c101b0a02c00040c6080342d00004a0100040c1c404805031941c0216014403a000030a1202003001c1044a8290303100a01031500301e039902c80403420502025040035560540c01d1071801d000388049004150500342c02c020540082008120a0403a0340000140d81581e402080f00c03400c20300007524400d030341c003885c03030740c46550341d070b010b21071036119841504110031003000715200b0210740140e0101c003030080d411141c4401c0c0d011940310030341c100074001d61004100c00c0b202000b070781004601148010517640c070018007034000006c0c96810007006890071030040c00d1140d000c101c2c00c0c0c0002c002180c140c1c03010b514100024140843c160803031501e8440c9410150f81612081078104828005481000070007034255501c503a144400248008280018a000020414280c101400c1e6140141c7c004501030061900928148802e00050760450498007440d0b0300360030000c0483e55403540074407007000f4603c4812107092000c07558400300b00b8241c011902 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 841168444 1250 841167194 841167199
    0x4120b060418080a020102190804050c0a061e1b060e150f01050409030302090a0e101208040b0304020a0815041502030f060603090a0f05030a0f1704060f060e1005 71
    0x195a21844200310035108421140780b03942c1015640c150001c1e52100c000c25070304405000146c2044070030440a414030441411071380101f0004001c001c200002030048461540d001c0398074a0407141800d1006224030307040341c5202030145050280001c414018500407035401c0245003000d1000c2141e180c81d00240884180c415410b10400403413031201141d440101d480b071144842c182c002fa80c0782108000280103022070035000d00d40e0030040c1015035120440900c000d80084c4412103070078101030581c001205460341c42941400c00050342035000940070301c1100c0407510b582c070711213869032901e00004030b1041096220302080d205100f5528003042070741c2d41d524452070003801c04450034071a00c09a43c1c00c0c2d100803121174a203000218001805407400d6800345170003170070342412a140d004003aa107102501306251016115035101051280c0788950040c05052060040c0c9030000c9244460207070880051400b0748010032035030311008041d4502c00301d0390000f4000e20071100105100e042000406050302d640380900c50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 841169694 1250 841168444 841168463
    0x50a0f0c0509040807021504090e0a0b07020c0a090e1e0d1404080a0b0411030f060402040b060405210102190f030c0801180902030307080a080a050901050402010c1b09020412 76
    0xd924500702c080c05100e43c0d00f051405103028001d03403c20008100d400e6604142c44400d00c800319031101a4450801d8140d41c1a0003020301d01340c5410320518040005181c0f1085500845c1c44031950f031244480901220010207000c1640e030044082c913828098280c03152008010440d9240d000d03108001554202240140c44482e0801440c52a44045201340d02400b212540400968400581c0030600117a1050195000021810340b0b040005d0820242a01280c1103500c800700744010352801d480b40040c14030084410500c1e003894a408038044a12401c581c0705900241d050788000084207404813030642d0110603c01c3c00c2d00d000805c02828980e800040d002c000703482e1602c0d1810290141d21214183c8240f010001904001c2c01c2811000d001391020498242c00244094000101d09502900480d24203445040462501f222810200c941c024101340843e810035040c8030150b60480060071045401299000300c28060b50500282c0003445c0d84400303840c5100080008803074144004404030b442c41051f201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 841170944 1250 841169694 841169699
    0x270f010503030403020108011701290f04150b0304050a0c090608151b0703051b01061a07020105041418090d03060603290d050a08040302150c28050a0f0c 67
    0x41d40c2e400b65000003804548120010301280030710b0003048080ca9802e0002103001002e804c080d102c20040c10b21140440c0c94075044410992400c0c00c0d10b02c2c0f482e00c007620b041006008141500803414064031070501c60b04000000303d806c0c400e0910035282d643e0b411607000c802503503992200400401c0030344240c0c4150f001d8414800201c3d840800084e003c2c405500d01c601100b245104400001c1d4889c4c0012410b2080400c42020b103400f14113203064102011310700005007146020014020390048440d03002c2030321801c0110500607a000740a480c00e440c0030000e00458130b00742c480460302100000820186988400c010419a2400000c0001041095660512685545503000d030182c03a60890061780090303042d82d26544082644640000c1e20b80002c00300d0104032000c0d100c950901d6a4510140c81d80e040016052040d03041c0b12b20031400041c9000e0304c851500219036811601c1e000c84c0b80160016a10760502880c03128be01c05003012005030000c0903100303000818a0000074034010320004445003214407500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 841172194 1250 841170944 841170949
    0x160f020f041b0e010c0203150105100525030509120f010b01021605130219030902181302040902030c040e1c0f020307060507170c0c010b0a180b270f0105 67
    0x2c030020001c58881d008500424403034283c800b11a03d0044504102d0107000e5400035a03000c0000701c11800d030b07131120781102d541400c00f4045112a10800c04060110030401d00344241c488610720300d8130350f03130802041051008612b4111040e115010200b5808100d030060715800700f00c04152583e440040b100200005040f0b1700041ea125034501c1c0411815091029080000c0d0801075036141c000c000e17a410042c41c0234102c5803400d620540c9048000006580e4000c030000f10f051503805c1d01944c500420b0a2000d07860005121841c07403000da10003c0c0596240c000040031524104540f900014005000348501e140d543c50303d940d1994003007081001c1441040402d0340c45405000c04e200103090ba0750266142441549074100907010240038601080030644d849012400100c003403500612040c17541c2552000c10141035800d4601003002e42d4030940b030a0504100300080c2d58031100c18007401203000308041080d0000502e8519000d42c20f4800342c600c40b00c440401240e02d4030f4140c42224000c1030400a66280d00c107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 841173444 1250 841172194 841172201
    0x51305070f032d0f0c090e0702032a2803030f050103020a060c1110050c0f0705102312061801030206030403030906090f030207080c1504030f030203160f020f04 70
    0x400c86200c0b001480301000701c50505035249024444840220b030751041110704c0011200d44003100c0000803079503401804171201c10020140c0002c0184021400c3c2500e213061240c3c250842c18500c0f03510210300344042e6031001d0030f00409101c6480105101107a221480e40402010241032041b00082e26220444289401c03912440381a030390044c2c00c0701d40381c03801d022040d5501c40040b00161241081c0504090f91076032041e440c260740d9403413695115115400c042c2c802c1d1800000341d070b41d506550400941030015031240134010500c0002d9151409102c8264172980e5074280e10015200440d00002030111400300c0d008031043d00480080c0c1d1403c0c4a0340004001c52030f017032001e0000075444441040402d0200303100e500300030100ca003d20380c00901917800703640d003505440c070b448802c9000da04088810400030105004101703048030240ea91440c10341c0300d01e01d207054a201e2800000c000700840e25403e0140351081045c0c0d220907240407062105441c403420070810400007410102c1c03181d2218410305119061600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 841174694 1250 841173444 841173461
    0x301080d020312041713090b0f0f030d0f0315090c17090c01050904060b0309060a18020a1505090603330105031305010e010f0e01050f010609150306051305070f03 71
    0x982c21001d9115035440c00c1c035803082118281405c00e01404884110403000c40c00000414034001d00040103030340c203030602c01240d1301c0041c81885810035180401164802103501f92040041c0e02d1300d904608144101134000f020344401c2907410700407006000c01d2100703140e032000c01000d9058a4001086944215032808040d08480c80e561942200346802220b5005001a2140300001400401c409848204030500f41e001220f640d101035128038140001071126218440b580008034410b61441c035800d4000c0745040145205441c4420150003860380800d2060382950104240104550341da400c0507c00ca603407038403440a10080a0f50f1101442c5040d0003c20041c0a11500603182c542c00d5580c4d5100b059517225044100fa651552184110700c0900428480c441614010100010705810001109421100300a0040103030800090052040365088030b13520302110001c03c0d02c2414040c4c1c9000803009401d0b982d120b1074000c100e098010317040032081e40209108040964417a4802c04131410210141c85010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 841175944 1250 841174694 841174717
    0x20c1e010c1709010b0d05100515010f0c050c090408031e100521010203100801050c0c15090f06010b030f060a030c0504021312050105091c0207140111070b0301080d0203 74
    0x4416148850b039420a699001040c0c0000003001c078692004210300c41080300c02102c1a41051a0030718030604a84161500400100091f1a00d0214440040d003d2042e400282c000e000c4200c15580410800300200041d00e8005402e5100342d0409180150301f40d0000c2d0b40c1c4034120005403004000c500702014071984150500310350001502e1030841800000c4062416100d070b0003110406808031880240011801001100340385400700e413a0048042c01c40d003024000c0744950000700043c0e1a101c40010700c80300408912000300e140c0784c443b1680b1501d0412030074a149001c3c01008000030340c50780b105000d1482041c0c11440b100036a07032800c042020305445800001d20b0021405410301c041e040c182c2c081c0c0390b82e00c0070a003215005900d542d49400310502001045441c4c1c1e448408000805005208010503c513107400c82e208c01021268001e908c4030000c3c05442e404080903075012402e0380c46503402980061306c01301507a0b80180c4464007501c15034024000d058a920501c3c140e1054030380b00004864125458 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 841177194 1250 841175944 841175957
    0xa060219020d1d13050c0406090501081006080c19050a0305070201231e090c0f0102120313030302120f040c080f0601030b091c02010204050a0f050f0f13020c1e010c 72
    0x1072406010b0103146100929013000500c1804022040284121802071101c3d1030f66503140c0740b40c003000070722020094000a04001c000003e100b00c012041c00001c1c1941ca02c0c1c1001201c550741c1840020a42c0607081d0020240380f84201e145c4492030300f050042460703650554092006a071494030690a03a4404000c0f66010741c80c01c4400c0ca40490140080d070380000c0001c805032070510101100140a120640d0001c503650070080f0320404510702405440300300002030029240121090307a0000d014040204401c80140c090750f211030825100c0d60403a606040440380e0610b5030b0504295500c1c6840049030b0884403844010f9000c503440c0000281c0c422802e00d0600100441da0035540e40001d0600003421082d00380c40381712480c40d40103000514986070051103034001070300c551030303c02001000d100c9640442000e4030000e20600280c0c071181400c03074049905441e0111031381e0300500403c401542103480038100d9840810042041500810200b4244c4d01e48001c083c038500c00180090b080340e40070060640032941 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 841178444 1250 841177194 841177217
    0x3020a0b16021e03010603050309031011070f170d02030402031e03090103200c0d021011090609130e1f050628180c1806020322080a060219020d 63
    0x7031038240340074a00f003031030400d0303049009260100342990056007048900e03400100b04032102f8101040b00192461a10350213008490a00c948024103100381070000e000741c0e0242029405015101680340344181d01c07484100d030380301491030000000b5001a14100e00c6401214400400501c1920301500b940310a403000d1031400041c075005500070400c0c407039648406c104141c40300000c25201400b404000480b440a00324200090300006d050150014101078880d1a01d600704440b6140d82054600800b0150b070801c1d9a0070b80e80300012032002900365503042e11800c0c18900c0e101c8031000725242460303003200d0a0700084000c000080000340d5808540c41da8000c1d140a10b500ca0381398600703c80700000072542c141e0710f10043d2564568500d04031103500000c64103464448050b50345901200294854464a845038011810700780c00070b480b03114448241050a40c00300040c054031010022203401405040219a00e000c1385140c00006904100030610071069445818005075002041012285d030660350380c004010b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 841179694 1250 841178444 841178449
    0x381b0f0c0415080a030f1205093a120c03290a03050d080f0f19020c0c1206100b04140114070206120910060e0a02070807080d020403020a0b1602 63
    0x3a40c0402e140c0350716542c260008990009020303c0074420302a9480e030344001c140c4070f8081c010940000351100b00074074000c108903813000b0105190104000e0601129128484580039203101d146c081000c61500ca03000b4110301a264000309414941c1c0c00e60708040c00290480002902151561603071880c008900d208540c00c5080c10a10304640d40c0d0000303000343c0320070391240ca6042c0341040003034049000c640c422060203c1c1400c041ca1032940816008040d03041c03844c00f4481001d00902d545070210550f50080340350310407040240010120460b01601c941807058110041c50380e5510203454086010740c45000215102480904440a0311101028282161442030044490301409034042003c0c0b2401d0280d140140d40e414020480f5803034608034400d0505000c503c040c100303461103c1031310710640b900d6010420420015101c9500c6000814010386800042c10401c80500c5040d000030402c11000900303c08848807a030203001035a00035500720400b01d4540407594058860b1251030458200480c44180061 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 841180944 1250 841179694 841179701
    0x40f051f0b120408071b12021309051903141210050306010515130302090906151c0b1807031505010618050402090d02030d02070e0f0f01381b0f0c04 65
    0x803440307040d40500c003005c1006c2000c81c01d6015080f111000d50b0f460a2041940f420003c9114006100d00080041c040f40b03a40e8542d807800b0002c650000c00c0701c0c540f0104180f5014403000151030348542440c82e603950a2030141c015840341150500e0f68000c0351040450076080015200e0b040c1d40015041c03008150090b410901d40c6c1e0080c4801114810b0601c1c03012005880d039090040c0500d14110003003646051075800d051443c0e10401c07200380108a038102d40c2c0c07182d01002241040040d041725032000d064650104010100f00b418403006618440c5010020400100c00b4103181c824048500c04c003c2032341c07150800c0b60040504540c2c241e2540c4080f40c10b21951415500410100a000380101c0c24040b9a07030100381001e154188000251b000004100701c0300c4480c010ba41d0b40640122401d0000385010500303581040700c18080d01c10300746c1301e00c04020461344000035900d4600c2d05c071000040403007410b0104e4000c00d900140745c1e01d03205085107100741c03403002e40040c4405034420624041c0403d52003520622005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 841182194 1250 841180944 841180957
    0xd062115020c0d050d0f1a041112040b061203130b093706050415030e10060801060501090603050411060c0a060f0b0f0a030506040b06040f051f0b120408 67
    0x211075082010a50101c010424602034003d1512003076144d210504800c002c9804060180c184a41020004245840510082d50343d000080b200040c6000012803601614000c282a075003414800d041408148450101b1107881100c084070100150100d0441701d58590050f003c50103460305c600c0405102c0d00c1c1001c0094003805c1009411003030102040d443c4110722145a0b10b520040c5500c021810344036552840d24900070717040904229140501c2c080c81c46150460100400c8201036955450303c0185106100d1800c2440451b6014440c4a44461004d8000c0034a4810389000c1b40c1c1040c00010901d019010703803803040b40c21041e00040c0078203510920409901c5422008018010207030328400007138039882480302100c000000025413680000600a00c8208004160701c60316041008000060000a0b95503010794070101c800c60640b2a480420003403c9070707103070b1502d185041804000031001c0203600c101d250050b012071000c1059859454050a01c0340d0549200c4101c00080080c01190004006110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 841183444 1250 841182194 841182233
    0x501110d15081c140a090f0909050316020d081308060105040c021507020c06040906050a05040209090a0f020d06090905010b0604361d0c09071b050c0301050c0d0621 72
    0x113140f419140f1340c0b1440d0305c000b00c900040f84810405103c040e1600061344080c0c4002c3d0f004104a101c0ca4849903520b00079030202c4009030200f03100140440d1155602e0240043d07008010b0303038840440f8042d2811072301031401502c4d0349200d5100000b03640e1510703004100c00600301c1d801070111181940070800c6802002490302d400d522451110342c2c02034071400001c000a140b03100c00041d080707003002d081006040341903012a100303600600c841005565020602c3d0f8001c9203d040009084141d041004042d001e0300401e03134070303951801e000095980803075005039a00d0342c0305030003c0140300500b40803c4150300075070041070341609080c1707412030f03810b0700c149080700c9209101900340c1c3e8450600400003040d5000411341000120890f94050041c1c441040520103000e0112000c80e00c0d8605076100074080b00042000b41c80709100501500c0a0001c1440340c4e034181000a4002d00c0306c7e1421009810f9690321060200003814038041c1e00003500080300107001107080c60307070b080d1035240051074482e00880da0718400404c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 841184694 1250 841183444 841183457
    0xf060f060c0b2208030703140a2306090711070b070b041a0103081603121505120109080a0f050c0a050c0f0306010302100c020a09140403080f1603020c01090501110d15081c 75
    0x143d000303034210041c5102c3c0c50168404a02b0f14a850500c011004a4900b0303070f40203000305014000c072035550800044e4029094980740385101001d400c128078140123031b400501c0688000416000b840141c003603003881180100b500b4031120b01242c181c2c0c840b51a00340f0025021070010701c0058031200741c04018980c0a402842d05481d030005140441040343d04031050308030b120144100070800c600346a03a43c0003802111000030040305001361151101446811070340707070800c5448010584807501440c1520030b00c000031421600341d41181e18240d640d5142c01c1000920540352218070003028034000a107103050300e5002d4980750440099040a50b4441718281c0b00f02c0e44a089060080749011152182c4068000c80309810360090400d42405400c1c004050080706202c1559800c0141107490b0010034102020103140041e9036407840507040b4010002c11800034000d500b00b4040348207104080010301901d80c41014104074160f400060b40004080c20310502200da00a841e100c004040c0607000c403c041c011508115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 841185944 1250 841184694 841184711
    0x703030e060f1207030e1b090709090f05220c03112b03080c0304020d02010c21020c030c011e12090c06031505150d0f060f060c0b2208030703 62
    0x100059000f071801e18100d40f8000003001400b55150090f0101140110058207905400b0542c008504100c04441c80c019582c0e003010500b20761044ca6050001c08000c10100065200b900051010389010303641ca815140810750f0b01d511100c062010620380c5540144410380080c51540d0f075490203da60414564003040c0402c0c1e02c180010203c001220300b041e01080110080102d01c1d0240c0031881c081c10a140900062007000010b840f4401031030851030302401c0c040b0fa40e5501c0d103018010100c007900d113210714040210008407242d80014840c0130a0700101c0c203035096031031302000440716a000b1804440e000340c46c541c0c60014040c0071b20076003581c0c041d000c000400c3e4103c15803510410b031b100c250b014000080d5515450700484134810180e00190908980d6900b0305c1c0c6144168005d680180c04d03014540c40d5407482d20588214155000c10018519440e031030300125660600505442c90b58242544c0c00c40f030b900000f130b43c5a1560080c20042c2d0290800300c104249441c5c8880041344c00c000c02e25001e040d03844140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 841187050 1106 841185944 841185967
    0x31103130b0411040c030b03060105180115051e0403060b1207090b01020a0507030507170613030e01020c030a08130e0c1204020a15050409060b0c0703030e06 69
    0x384201d589030350614140400a80901c1c642c8246422010381003503416800460300e81c42d0442c00d96440d81e0b82c0700d05118440b0b074001100e6120f064070400600c110328001a10b5542c100842c50010b0918801d01d180000c0c07610344000c2030503402c8000c24100b040050501402000c01c03010340750344001e04401c01005550700800c0c020015141c0d200c81c50307900264820098416256004000c4a03041d40d030f2400c0540c0c850100c1c5c01080f56a200b81c01c001140c080d40005c00311f020f03201e401d002c60299003007520f0132214400079280890450003001e81c030000940d01003020036100ca00410f5444e594486181c05030b0940706542c0d1054020140d00c50820260221402c2500c1d80417055a540300c1c8035a90303a10014004101b02c0d04076100740048031070007180b02540480540309440340d00d00c0420206071a058030301290702032a80d101c801c55200460030301c00a84070391141c050b0000c020344103a080201e400c14 = true := by decide +kernel

theorem cover : BRFrame.Cov 841007194 841187050 := by
  have h0 := BRFrame.cov_init 841007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 841007194 ≤ n) (h2 : n < 841187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
