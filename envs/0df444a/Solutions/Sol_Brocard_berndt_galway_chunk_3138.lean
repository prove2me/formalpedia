-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3138
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:46:00.751913+00:00
-- url     : https://prove2.me/submissions/0b5749ed-030a-4293-ab2c-1793908ea42c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 564208633 ≤ n < 564388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 564209883 1250 564208633 564208637
    0xb0c011b2a170a030b040608070501050304080903010b12101104080613021f0e0f03032505100e06060103060509090a29100f090213140307032a0806040201 68
    0x3002030700d45030a100e281a1128202c07004120903820444405080c00940b000d00542d607000207042d50f895080c0421a600707500b11b14035542c4078043c200403a0303030302c54100c035402907018110503280c041f0030021074090500e999a2940c4514500b000359881c14000901c8041d05091000134840c000340c17446203540c603110390300500f0660340001e03000445440080114507440d0344003910b418a02c3c44224016030150240c4881d82c00007491014107080c40e4508100d80100e0f0090813006149803d614528000d02018840e11610000120001b41c8003400428040f1940ea0132007841d0510148862812540d15060222035081c0482d01d02840800d090818050940c0b1602034000100004142d540340c070800d6800409074800007400d98618180a50702c0d1140c071501a1100600d046c400b11706041c020300040c1c0c400c0d01312840182c41802000821000b00c8084812a803800c0350415044150710007003400c103080d41c3c101620403064650108030301d00d8500300032541000160225144507440f0081c87c1d0302e8100644001e40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 564211133 1250 564209883 564209927
    0x80f0c04030f0602031512070e0c12180309030106060306080607030e0c0d1b03050a02030d2a1a0c090a0503071505030c1605011d010504031e090b0c011b 67
    0x100107043e9038000e5801c00084492022640000c00000b18a0004120090304070b0f0801c00c420403030040c008907410340004400042c00e090031034080b0201136010009124007850900c540181206140c203008541a41c100035009202d80750300c401300500074003041e12404209104840010320f1481c400d00c075010070056050007401040c00c1c007208122458400f117006840525182c00b034443c1404c80410590300861051740541070503401030041505240f541031443c0c050003010f890700d1280810001e01c1401504001c0103400103800036003401603500d032014028240610b40c450030b10544009000107001ca03240111412008075444405040d211043c030312070b54111380300c0c2059850f40b090040024560240031804500e0a0080b440d1030705002400001d41943d03180d554943c950900404100841c0c02144640000d00c0b01d0b00703060750020000380449086c107180711072011141810701d100c1ca6204004000c1c080d030f0591100c5c03074428107600801282d80440388541261011448040c05456002414020060141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 564212383 1250 564211133 564211163
    0x903070603020d0b0a0906031b080c090a09050a1a010906031104050a0b030a12140a050304151b020f150c250c0311030c010327020f10080f0c0403 64
    0x81e02940010503d0861507071650100125900e807601c131071000706250240812440d10314109072403850300f000c060b49a40250f803a4140200d10f40000c01070a81d440540c0c412090f0390b1130102840040c50395800c000c0c018010035100764244214401c0b030f40300e009040c580415442c1da82d16100030495500e48401446075806a040311744601c0c269001d2a40031316920340201e80c40c5031010009040080900d800c0b03800c0800c411400440c10b502c101c02d915001229100d0b24a090544000034185000c0100000c0c00141007142203004046c4640000c1800e514840d180285e6485600000c1c0d140d00c0f0000e00b280052150300c0307400420b4120f54032030b103000d103103045402490040c407c80c0341d885100804012074485602000c003140040e0080000300c00450048011040b020007103000c240c00c0a98074892a8109420402c50580620803c41d4160b0303081078000f013040c20101c080c404124030420341a4200d5109410071480c20f003a0f9088090940f08078041c82c01e011248d81d0708030a0f0032981c002c40c000034180b2240340c1c902d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 564213633 1250 564212383 564212387
    0x60b01120c0912020d0602070506091006060507020f0a0f1502100504030c12090b0a0509040c03060f091d030d0504021c0308070c11090411030c0405041502070222020304120509030706 80
    0x403550f00c0d002900c0c540c524a4103840e400c042e07030320240c0112075650290041101114003441100b498010b0b8000034813003289003140052660040c8140a0722540c594031008100365030f454085001424400700146403250b554081c50045030b9600c20b040c0141c090303d6801020700c0054894140308a9164440088880340ea0b03e070b00c5800541d011540b001d0001d1040040386002c00c05014082c1050700d0b50f40c01e690344000c6000d100a50702c6e05a134242c1410305004041c0550600d01026070241c400583e0001218909000800300201c80d1410000ca10b0100048040c0300411036001284901d00036552903074011408030362485581200c03000034001490700404140404d124201100e402030144a918603a0070680c000900c0300801528115506140300c03000400505040c40b006140c1c4c1000c550411152405440702c018141d07000d281d0b4403410307500094000c1150f84400c0c1130f180303044081c600105a2002134510341c000f9032080e02c09a8040346c80d414080d0005200310f08407a2190030140240c00803078541081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 564214883 1250 564213633 564213659
    0xc0503040203030a140d3207020607050a0e0904120e0a24030204032a1a07060c05120f06043803011d0303010e010f0b0403080903100207060b01120c09 66
    0x880740700c5481003100036101b911a004000030300c50a40703807000e0955011034075005191807403481d24204685c920300b000966034022480a07400500c50820984e030b0032544070121100c040602d051030b4000306070b500340b2040c000850f50042c05a5103540390100700c039040000304a15481c052144690440071010050380a01500103104a0195541005410703c0d44036560307001140c1c1c030071129040100c00c82c20a9132003c1c0d0f40d11b01c210010040c10f4802e5240c080048c8681801c0d00c180e90000c0c081d6519072080c0c5680a12550440d9039a604461080e0a24186840160400441500e1070f0740b250382407070f03050610700841e03890001018609421401003d0502201e0b2030a0503a20074102c0d6155680b81c4d5241100d2990021982222010401866032903040071050745819806801c10300344021540b03400d1103800024400c41e01507035040b400407601e4010b01000a45011a03600d150088030f4004606142000300303a0b04282090032003603c1d91001091420008021a1110b414100020f4034080c0204614a0444a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 564216133 1250 564214883 564214907
    0x91118062b03050901141602041b091a1b0a050f071401110109150e06010f0506040b0f190504050f04290f0d0309150503090304090515100509040c0503040203030a 71
    0x40000e910015040c1c0c0d0552a0010104051501f588640e0700e011442c080c4240c14294049410031004210b1702c050081c03c0200030300a104000d100d40704400b600140f40ca041c3c9100052021175110b20341c07980e00380d0310303151038885200f150103126800710070308800d40201d5240240c034000b1000b800703960b5141e001102c070b02e0500ba050644a540e55843c0c1c0c008680b81181c8102600d030003070800b28418040c490124500003050388507020f5560502c1050211303507030310805c56040300e944840d441d40324201d92403540360610a00c0e00c2c0045040300407410b4075540b90011701600031030794110f522480d81e00c43c84080c001994800380034544040c124000420003500c50030a04000f0300009054030b15030022910101d21408000c01041d4045a16035204100c3c0300e04008996840700301d14034280c1d003582001194a07540e0f01650060011194a071000950b5404644c01c0d100348114006140401944814801400941c020382c0868000c1e420100b034502064001d10440340580c1e80070b0029403400035114411292480b03062 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 564217383 1250 564216133 564216137
    0xb04301d0105070b0c09010e0301090b04080310080f070f06050306011e050c03282307140a06090c0b0c070b07020418050d020705090903030703091118062b03050901 72
    0x4401c6070b01044139528501d02c614100b5022a6943d00d80c0000545105018030919100b07a050071203e01c0019801e0041036000b03640060f52030340740d480b030302e06d800008011a003143d012813207101800140f43d10009071b400e08441c100345441007015103900f8111914801182c9060205480030f4038141080341c5020900c4007400070b80b901a05048515100500b103610a01600000003064280003444042c80c81405942e1466406d00707000c1d1030550105502c0e0110341e03040c3e800d0020750100b036030018080c2c10206440d9642844054407810580d51900d180142030000e0243c411080d100300108803403604000305c035036107070000c0024446ca5190040280036580900c0382207801580ba40c0d041c160748030106030349042d00c5100d04042e1052440600b0001c1c90084039502045c480c11001c001e00201940101c1220303004000c51402141521042c188002802c43c4901016000100d80b85452003044400e051280245011240c1c046810a148000a22000c001c00d500c405980c4801c01200000e00030070003003291203018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 564218633 1250 564217383 564217387
    0x50402010e10141612180b0711060d0e0c240f0910020714090f0f060102120a05180a0e010b032a07020102010c21020c0a0b04301d0105 59
    0x7020650a16400c40e080100e4400383c6044c000d010480d0030401c44446595a00e0081c0004152010a00c1010f101e44110140c02c0c0d400074411044c44100d610304110040081e2116680e005034440843c01040381c048000320380d0155072281202c51400711040c0c1101340c3c1020288807181c0d102d02c4401c1c002c1e0301408030952052070030001c6055075100c0140a511407891500607086040c03078038500543e070790b1005115910941c40942084202d059035400150488051807107940340380d4822b00180d25010050a45040c00c41010400c618050340c014000c0c00071992181140d46169000b000b480000480c03030043ca05070564900041c401302102e50041c40e4480c400050700040074001c2c400f201d05c4c44c00204141c80307400710005042400d650302402462040c080360b1412000ea500ca0f0040032906101041c012443e00343c00040c16011050100100c0065a4000400d400b05003040e19010460308a4441a80c000e817400b801c10132001070120500900302e4640d40c0f10580c640c00d050400420034062056128140682 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 564219883 1250 564218633 564218657
    0x60f1f0609150c0c03030e01020609060105011d0117040c1502010b030a060e0a080c031b03161118090d030c08090a02101b030f090f080a0611040e090619050402010e10 73
    0xd00d982c1c1400646c0241c40d080e40e035403014400241402001001c105056000400410070b0740d9000d4041c682030b00d0441d070010410f800410040728605841c15402001810030701c2070205104c041d9810608450760b050f80580801d18040043c5e00b81d81c107014002e42c1c1f40c1c010407070803000301e50142c000d0b17201864079206480410010380d9030031005802004400c0d07540d0b0700100b00104995081440a64015030b80e000543c109002501180b00240034620005e0091462068411603600e58900c092404e860440c020441d92400ca50b805039109000c82d910300001b802d00c50b104107010b01030b5000c14080d1710203030060040d02e03103981c09000b16802020110301c2000b4001003208005014074101d1840c0341d12a07a0342c4c07036050003812070042c028506504142040d00500c0c800700104040043d42d000800c1e401003000c9401000544045081e000307942c040304a241c0258204800b00e0b80201c1c0503842025139a007180c5500000313600580498034211402804140e800c5030580d89450901000c42186901d440d0007550321107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 564221133 1250 564219883 564219893
    0x50607020f120d09050109290c030a1d010306030f0f030203090d06050a05150d142d100b06090d062901080c0705031c020c060f1f0609150c 61
    0x4100c440c2c64489070000442184031039880a118002003030246045d40b822420808c0880b546091020302e02030030340e00003a0f0203d160b004402034400c500842030913240c48000350b000c007a000d01c03804070100a40c5440301402074071f2580a031040000340d0350469207101c650f89203581c03150801c03413181c0f034181c00358403082c81000020359a51311403204051042d40003007261704101d00954162000034103c00d00040b01d20800000684400507416503c03070300320308a20003440c40410002d041c880ca15080c8248600103120a1002040311400500c0c010481e0080300ea0178403400c910201142ea000f01c4075503000004104040c45450240c0d0b03040c11050180c000011502801c207001440445a2a003840701c604013050b00c0e030712540e00b082c0c0c03035980219040016445e140495450680342d1091300c100c00f020700c07006525013248544c2641030325460000e0390b0860300d050410611660803140104da00320145844035044c0d07100c2201c0c414101d000c032001d0780c80c0c1812050504030b9064a16103444160000c115503003540101041d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 564222383 1250 564221133 564221149
    0x6041b08030703120509060405121803060106080403080c030103020604120305120108070609050904050c090405103917072c010e18150d1a18010c050301050607020f 72
    0x1e0300c03030f8075030135241200c04910074261003005044076034a400600802001ca40041140317444c00e00f201a00990324401030040d26504114400c0043c1c042c815200007003041078201e201180150f020392140403c907919490302c42c69500c8240802500844240000c22800400994554a4522a04205052a0003d6442d00e0102400d902007020369000d42c00800145070828602d0300648400e13101e408881c50540c5a0741d550740c00c001c42c07030cd000b00c1d80c8400240601005100300220401c094006011040070110007800202d41c101c40d66070800d00480c00d07002d00604100401d102007003143caa42c2104504803031140340300d5800500401c1801540340d4100c1801c4141c0c0e4519079400030864010303201d400140001480715004149103030080408a9000810b0141950701c0c030f902000801d240c210410000001c11440d84c44514020440d50341200c40c01d84200b00c02040790301c141115614a500011004840340c02da80e103040b050808100100018405420b0903c010b205484c0080c01d000b065900d03960109d0030035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 564223633 1250 564222383 564222397
    0xa02040608280309051f12060b160602040305030c070e06010f1e02100906060e0f01030803360f0d034805041d150103020a03091e06050c0c06041b0803 66
    0x400048021622004c0e0800c20480c03030004c400381c0810145049c0101100386215914901140c010302c80c0c617000411056404407400703183d001003503a40f1f5040a06031550b444c10503024200d005080031001610651080c008010b0560450b619014280c3e0012445284500d01c40d010604502a02c1c00070750010510b03028947c0130a00c54100003415034503200280c0c04c0900046c0135940d00d611070348010004519084162900a840c0c8a40300d100e4040412109003050210f00c00312151141c40c80e0b2105201d400400c9507202d10190405a851003484035204804995068444003201074025400d141061400601c0c1206e4064020541507843d080002c6c0083c84180b030101c0000081e00002c092116801c6400a0300703010030003042c5404c15050a401e540880824252480e0401d035001c00c0c600d16040c8039403c40d0642c1c98100030070001094042d22420454855040152800d6003041c2c0403c141c8100340044a280c4650100900b030f154469035501d035100460300304c0c2d03040c04500300c0d200802c85e21400d0000b440b0f5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 564224883 1250 564223633 564223669
    0x190803061f0906080c040510050c0c0d0c051e06040603200c2b0f0c08220503011d0d08130c08011d01020a090509060a090603050a0204060828030905 65
    0x100610f4650000c00c041c00051400903003203020302c002c0040c2d07100d16410403140320440c10a684c0340ca0380c181500e0310308102a00d80944c4030314181e02800500c07168050740000c1d00c1003660440c0d440c03a0000102c60034000c144030b4480d08100104802c1113000d100b03a02c60140b6211a404400c00600c0c41000001300e500035140c0f980241e0011642146c00b604203606414400d540c80c00401b180e4185000d028003180446e038005024130025201c481d0401860070100da000024416050429802000007685141554010135000c0c0d072030700c9011442c1c0c118904d050b2425403849402042000d45240c802c03038002d41c0143c202191070840d004007600203206107180801a1991030000125911707410384050742050b1003c1c079000164030401c0010320065008d40040c040c0d88042d0b40718074668580d540442c00c08282d80d030000200500d000c5001c020044042004060140216001e0041a49500480d91951040c3d00290603101ca4001c0342100c5050880c4c02075250b82c06814882201c90781c401c0481c5207011038481ca000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 564226133 1250 564224883 564224897
    0x9060405130e01050615040915081f0b06093007030f02010e01050c0c0f010210020a05030105092503050403020102070605010e071d130e0f0307080318190803061f 71
    0x1030400b4244203c0b80d015004444d040000201792032101181e11990050400340b42d11004680d103481c0c01081030700010101c2a0803113010380c41001458aa154204003e040024104140e401061070044140e5800c41001081030f8044040ea02541c20b0100040d0084000e00000d03050100d409201408480001c0d80200700c503000150b1301d44001051054446d100b1410301c1b00c00d0040c2c041056000603000c103000070a0301d50041070100c1a006070b10705807200300701030348850001540e060700552140c0514100e403410f40b4174150940300c201c1602c1c07545428083c0c01d40889840d020b8464098030a81041c0c0e00b290090000529041c074544606003620400d81291080c03449450a100d200c45d071150511502e40380090103001200c244e00000781d011080280d546481603109c072051a400b800501a03054041c1d6400c04883d513540240c9003521190300304581c155107080104031208036400c40481c1710028003074545202c15500c402540d4805403a00060489038100c0001e141d400b100034441030113007844181c1074403149 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 564227383 1250 564226133 564226151
    0x1404060e091b030d050711150c030a12060812310302120106030b0c1e04080610210f15060e0a20030106081b16060e1b060906040513 58
    0x9030301041c0c1c024046000344c2c011100041c0096001e0700399810240e100b800c641c2c9178842840021200082008080c107118000070b08000c0c640760010003844500703070307588800c1d181c1d81c4c03103902103011268544500b010503001040e0b15104551070300c008049400b5400410b003103e411091001c408007040304060701d174442c034102c4c040c41035140040c0000405080500240126403d5030341c0c05d0fa0308580a40440350080003c0303100955504055650340240010398186516950307111000360392030314107803a00340c0038041261000c143c24282800c2d0074814502c2400b0180001e10b9035603506800184c1e15030030798100d002410501c680325114002c8000034a045908001c3d00c2c206000f549084858002c0d01034800380c8409000199141ca9105aa045503a9410103184039a00d1049018461981c86103a4030f95007400581e40200c1c07011402400c00082c0254402c010b90f0800d10f81080d80d458a038807000541d0401c16024030b0803860800001c16020001030300b86410903039100c0204820800004504298540300d0482c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 564228633 1250 564227383 564227413
    0x11031c050a08011e060509011b1a0f0705120a0908030a0b0a0b070317090f1c080a0c020309040e0304080718050708010302010c0b0a11030405160e060a1404060e09 71
    0xa07409050205100b501035013000b1a000c0a0303640134802e01003403020209140d200703a070082c041104106003483c4806024209441c2800e40c0d0f0071b0f0f080e18031403400103980c00310704010780461019104402580f24140340801480200d052610b0090196113465160040d0b200081c00e0b903070146000f0300b810100403c200618200f00f0200303609942041c0130000084c00310304042035120680751210344540708401e0503516215805810076168000034000762003407414088400500344052009a9001e6444600a44590004000750f60903d0b407031740c0040e4810300010703a09252076440404d1801181085907e0f04c0d9a4a01c52800d00c03a495000c00d2807821007924004004165006441d4040c4841c54a03184640c1140c3c0040e006a0f02d2040140c50305c0807100001c2c02000150b401505504500c181190712450309151240d80c901061030401e8600c000c104d030010b9210900c0e21880d00a000c01400c0c0074240d420b2004045c40700e9004606541d10a44030080000d8201098810500a1000e4000f40610031030410003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 564229883 1250 564228633 564228647
    0x51b0f1b0c030c010804060b0301020f0c010b06040e01060827070302011202070b01060513030c1202040c2109080d0f0b10020304060c08030a0b03010c08150603040f11031c050a 77
    0x206120358010758400909541d003c100007a501509091803040c07901c4030704104000b82584503c1c03070b8043d880081c4440d040b40e04003010345414010304000344103c0c0218003d000b15030140e840303160258003080b00140116802074082d243c2c044d001412040001402c24050401c66014a44483d52500281d00c14000d40d40d02c20038860381220741000c21351520034995610700640c44148611020080013007413626070034990b8060a402141c012104260309034031420700240384e039003041c000c038821480d10601a85944c0504030010300c486480710102d1106422036030b0400500345160b0115003803c010001c1042c0c4501900c00e600c0c20300c401c10400243c0c042c00c2400e101c1c1204882e210f1038250f5100307110800005030700080b000122640804445e8817500e4102022015200320801d003035065003403040010240341d101c02d00d6071250103d42180903038201148240704d03107448144c43c064402603100002c5408907504c2c2e4107447c0e811030094100c40007a000305020f04050350b080c080c408001200000c04500065218103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 564231133 1250 564229883 564229927
    0x90a03060501170a080f28030b0a140306010e070302120903070c060206090d0f0c0204020703080f060604120206300f0a050601051902100e010617031c051b0f 69
    0xc0185079003813807912004aa030207103414101200b10002095087c00400c459003162080340f0704030280e40d1640c0000050094004412200c0c040c02c003140c40000c20301901c41c0d0050310740b10044e018200c140d00300f42e010080000c00400d10010b040e02080785203d5000e98101c51440b0341501000b96440701c00d5498514141042030784520b003158020001c0c0300e100b01d004264030014440500780045406040c160079101d82107a038901960280c8040340c01000d15420900142c401d02a01180781040e6403400100107a50085008640002ea4072401c0d01005060820043c601151100c0e0102c82c2d03000c08007000150004070600010000c17003884203201049800d15441508021030a03024007903403500c100024414002c40d0704090501031602c1000b41c1540c024014820801c1d100f8009006000006840b80c0c041e201901c520b908290002030980701e1044040b081c0d9000031035a40e4880c841c80c0301007054201414015024070b4024510003c015441c10300c000003441011840082580c44012044101c170134410400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 564232383 1250 564231133 564231179
    0x5010902090c0a1b06061503021b031c0e031315030c0c020f04051e07030e070510051909080d200729130603020c0601060905031b06090a03060501 64
    0x1100c0003220503000f030744d81440b10001e60905611030241e418560058a420b07441000d240c819402c008210f6a850f800a0442000305400300240c0b07405203001e65900e1040244080c29540301003000c0003041a00e40200456081d002e040740c3c141100701e00020f0140c01c0c01d60107005d07840045035892422607018000e01c4c510b1501e82c10700c85c20780b0103e41c0100d807480230070101e0b9500c581e03600c40008407044032a0310099040340190348180120f01c1d1909014000b03282002e1807030b000e449a030710700090500d0024640d05504d2481d0782e07003070b0030b2410464801c0300408186110310709118856401090b0380c1001c014510301c1c5d005903503c0310882018100e40700c1001065006454542d00010004d100554001c0859203900028420400da650782001c03010380140200340025090400668001410f664160050200c901020342901d101d0399a600040d5907104842c400d803605030700401c0300f940003242c0b0b903e503081160201420892030314485000185e011030040d08100c40480d551001030040c1103100214842c4040b1f95 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 564233633 1250 564232383 564232387
    0x90f1a011d0105061206130e030c070b040b0414010c08030408070c0b0c1507090314010e15041101080705070602070f11060f0412030e0607030806011407030f120e0a05010902090c 78
    0x1c04111144070b0004040805e50b80340000c900c0c140c4800d141c0c00d076044d03044e283c10402c130081d0380020341e102d43c4189100d0246101d02000410300c914500100e43c215032451240502c0c052078084494036005031b844045061040107014100402e0301c500045201c3c612407940b140d502c144d0341c80c18030078840d05608100342c401800e01030300e0a940c500040c600d4030815100c10300c10030755440c1841199000410b030401803005000501a51f1101d2054000140d049030020035680003107400a110300365002c040701c002d004205c0c100294401c9500441c1c04640054003032900b1403811815454160903640714020488020f90b400c801241031200740c54170301d8405c1c3e07812913039a031900c40e058100d0070150040d401500711640c0b60000480426000307003200c100076040508032644920050601070328403901201e0060204022544a81811740300000300e590550345a1145840c8641880303080320161240030a202c151561203c06940c061002c0115003001c501c210000702e949001441802001e240c003401a01240a003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 564234883 1250 564233633 564233639
    0x11509030b0703050a110f0c010c113c0a020a08071406030a020d050c030a06080a0c0b030a112b020313020d03030b1815090106050d090f1a011d01 64
    0x807054250360880050714001c00c41c0d40364954040002d0a4840b12142040400070f41201480c6046024001d9403220a00070024010081425252070301d1030280d0010941004224120101450f28003851212040141d1a00c2c100320412140311001c0280c030000f46503100a00c503204514042c900325029002c0d040203061070034986070050b000114104a4603106590100000d05071040950548116602c0510140b10724246580180496401583c00089660170050080303003031900001da6819082e4803980f03c000316807406c03943c05c0d50740e000942034021458407094800300040060f409411034540701490306143e0343c000d0742d040c1c410071980394100d4680780c014010400008100e040748200960141d854180011040c90114010700880040c3d42c0c0c0031640c2d20840c05111000315199125603800c030341c6141240241005c00150090034440ca4000680420441020396071a4201034041c82c82150a0700c41003045a80e10301084201340042050800354600400c46088007145421400030041441681541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 564236133 1250 564234883 564234893
    0xd231005010e0f031f02041806030305030a1a030d0203031005010207180b0303041a040e0705030f01030212030405060d0b040c0504080d0327060c0f0f021905120c0601150903 76
    0x250b40d860140306003c01403049200d42c41c1404841800c0300c4a181410440c0b00d4148000c1c000c1d001409035110710004045000d094504620802c2c003074075016154a4116a150030400c009440c14501035840741003403018400090b101002400800031030780d0060f580300e02d00b6a2110058048e15070200d411540b10003010044400c44c0f50707204014407101070020800310300100200340355101e181d0000c03810f14052902c03c911074800901620036605080b000c03103036030b4640200840350360100391009040c1c1c4260800400052402208801400210406890400c0d986800089541c0c00841004410980352080d4218501d00b0f88500b24150b481401c2007403c19081c43d0b41941c0c4c603800c440902d0305050b9102111100b040441c24904507985400c401c1c1640400c0c05c0ca025001f80c0351050310980440c15000311082501d000c3d0a030a154212150b0040503030884a869000d1540b0003520240e540707010742d83e03200356654000002804098085402859a945042c0d0700350040280f4448a804103c40d031801440014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 564237383 1250 564236133 564236147
    0x807111c0b06040c02010e07060f080615030f0a110a020c090726090304030c0603020703080612030a05090d050d020703050705040203150402093c041808030a020d23100501 75
    0x88090754001307010009984142d0060600c4103021600d40705500001a032168004020142c11103569610314654441c80144241d0498620070f1502030002480011050a0300003001e9a2010107140f001c01c40031000d80000300f00303600c1a020320700142c1282821040c1410f202200039000324031882d055014200f03400d511103c00e03500c52a00540051940086484d02204006940c051600480d461000035074500014000b580803138822404154120001180c41c0b600d85900e00354501807001540c900680b980782141c2a07801b2460030b03039005001d5106203010034010049100c04484035001401d509040d070811718500111544024800c500401c200100442441d000300888801640c02586441c9034100144001d5828410490a003507590f00a20340c1c81407888140400100c4c1d240c1004003002d407101840181d0300e15460000d041c80780140608001a0144001c56100031032040060805044110b90002d44020011100700484461303820b440d0002800041c03a000010240900d42d4507160000207000c01d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 564238633 1250 564237383 564237391
    0x18080a0308070f03201c0e030417070b07050105011d07091413092d0c15050f0301060504090e030c07060f030204030512070302151b07020d0807111c0b 66
    0x2c8240301540d542c3d180030303400103617030300d1000d2a02152034100f6400041203a00100b82c01c0301030401d2414184441c0749288103080203494040083d40c6403d01303000c07000c45107589020407852240710b01c00300015000d00c0c020240c8000c41c8518008034041d498103001c8c0140c01106082c2a10038000d03941441748007030304807864004a42000386042c0307050400c500044e8605043c2d0700c2e840d81481c02c200011080128240039201c0030708140200b003102c3d0014a0b11662045c40007140200404442d000c00d00c00007921044071101d00b00f4500c2d08a01c0c0c044c004901d0203240e04203038400c402141000c03509100b50602c034001c22059440d0b440c019801c211800680a80d0307031102c1d20481040c0240710345694840c0d0b03c0b0b6011213000d107401c2800c803072000e080369510001990010109400502540440700300c2e1003201000c035030003002614410724201a0304c0032900095440f51008a82c407680107040304000529500183c4940381c05124102c0c0f10355141000c0c46031a07002c3d501d01c81d4503484d01c20011000189010032503508 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 564239883 1250 564238633 564238637
    0x31218130207020439030f054b0a091b0e010506070b0a05060f10020c180408180d021206071202132d0e040501061a04030201121b18080a030807 63
    0x480701d4101d4081e00101002d420020407142888d041050131150031403000c6000c0c800f281241c1e20511340c9903d4041a0100e008101d401943c40442144440524140d031500007841c0c942c00100080f03a680d49000c0410b04190351007006070108002c0100240141805004141c02c0e5000c5e80b400384030b40d031800000200104030390700b4941d0f0382c008100b00e6141d040d030b030090200e4003501b5500d002e908104003941d24501c0f0340c5c0c91441a0822502031a10b0308092000c54091580200001d0400125200616440c2d14140d4030b641c11014a424440160703560b52150604c0070301441c041c2c0501d08040f03c00521100040311181042c50040140600b8000f26100c50000c03901a10321402d02e075403901d601c1061807555200429212413109e403011030001c440d184428042e03840b980003040501c0e501ca01e5110501007000813404000130071301040000d540a1700b00c07070200c243c0016000558241a11250303500b05101910b260009000f0680e00301d00100801c000800ba00c200402040c00b007015940061a072240102400c003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 564241133 1250 564239883 564239981
    0x261528021c0e010f1a1c03091205100204090509010e07030b010911040905040b09060a180f080d050c090109081606051b030403150f0b0312181302070204 67
    0x102000290700003a021130391580140301c0300088014610f104a800c1858903c00c0b0716101e0740c00002000d0f00348080b07000340c0c55103076104070340c1ca00410b22146440810060307401e40180b00b841d85400f04c081c8001d20241c441d00074009640d09000c028103003100c410355102c507a182d00c140d000303001040e6003100181c1114002000801e100c0d41c03414400e802406503511000820b03044c84203100c1000016400780740704100c0c440c00c650a80da1550400c5d01540c111540b286d1000003020140008125000403030b1810341c0c01410b5545c43c00071080e180f401101d070221504150301c0700c00310301c072019036038405510001048000004c003095864648000082c444620030b0000340b000000d101d000310441e22030840f06508041081d46e4480d5502e0074101c0c594540c08101020306440c050f1601041d00462003004401c01f4007a009040d00091003c14481c00d921104c2d00d502840700c0d074184030041c0d5031000184101407121400250b182d841c1132040c04181c80d01480110310248610810707040345180300d032455403650300d04c0720450 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 564242383 1250 564241133 564241151
    0x8130f0809010311040923010f030201030b01030209100e03120f1803010b060c06010e0115020a02130612030c05070f0b03160306030b0a051b04261528021c 68
    0x81e004202d641d0306428824008140026101c07803070707032018011220301d92061000b00040211008541f000340260300c6580b4102c182400903500c654445141482d040c180145040c15500002d95004218a42e03030001070445a14074005080030322072806000c004041c1242401024043c4c2c4800e4000c0170000500c1d0000b40b80891078a69007508140c1c0d201001a20145e99580d0605040d03072501024081c0c058003c844000014a20700724420aa60072046035001c2c2c42c121701c0076820040341303a45221481d4500c607100c4c6000b0644103402c01c98803441d03034400e03190b120031000c403450301d10700f0000f00c1d501101d00c0c5034003528200900c168400440c6d1b0311a03140076001400310780e40c0100350007c01407138001a10400340c1c40204030b52a42164011406007014440780200641034003032111040c816030007018148290b00c0c4020740704810a001128241c5005410b445524900190780510b004040310502200d02d0000490382c0c12500030332485414101c0c0c007405520f0014900254a01d6260181202201c20360b203000b11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 564243633 1250 564242383 564242387
    0x40608040c0b0f040806010503071a0702151818010501020705150705010f0504110301050118200703020105160318140f0706021e01090233030f01030308130f080901 72
    0x7000c003819402105a480d10b00011501d603254000740140c0050744501c3d0008501460b002416070b0481d0762002c040c40400c03c50a036255001d4020220403600007034070188000d0540d000001a00d6000720541045000c01b05400c01c0000d41d003007200400c06914110700050000b82d0307012034100103803141030b1580c000303922050b02941501d10034107034082c02952030a50107049240b02030708818069030040ca4441840c242001c1010708880b02031040882000406201005640041d0001c2c07981036510860740500321352440080000740d01c04042100140d42d45d10401c81380240980110350f051020f4a01004011075504c1709140e400d03c0d810005e44070304229102d540e0504410031414041182071410b461070b85030382d00006503440c0c0c1901845468800c020030070071501c000521690b8110781d00140704a1554a030400c1c1c0c000c501c9000405007103c503006c003600511040029004500419407096500c26940c95400c0c0100781d00006880c5a220005520780d005c0404c0d03800e105031011603040050b160303030b030a001001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 564244883 1250 564243633 564243653
    0x90603020c120304081215092d0601050c03030a050403080c0f04090b0a09140703290409020d05061f060c02030a1211070b070606050a0b1c021201120201030b040b010504060804 77
    0x100000c0d4805a100b008000c10710907a09014101098031021402e0b100c00d181400c4071010304010780c0890990802704000c4070382d01c0b45082c3e04018181005e515010318544502d0071540212084040942c0b501d00b84820180e11407012030388013480c3c035a09400c0410800400135035201e40c0c803038025410340300c3c0c00f00e03c6c866880d104490001c049494040105103140d841c4c1e401e1076a0215058004a4589011090907030011681c0006500444100d110b8450302c02c410000105130034207050ba00500f050041100003201000f019003c2d06c440301c030900c0d0030b0325950411040c0c2030171600000200900446048010b8400140841000740d115500044400d0b440d202254580181c1780081d00d148244900040d58a201800900b00180030b51814022144c44005000c030000191013080da0604041140400d1081c4900200d140b0801d081030241c50076000c0341c241140010b00381c210003030044002c018042107603010b10480100310010340701444011402c000107800f501881c8150030600010000040401c164980c07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 564246133 1250 564244883 564244897
    0x50d050604060905040b04030e01050415080c0c072322050402030c0301050a020c010f0e0a080c010b091008191110090e07021c3002130603050601090603020c12030408 73
    0x401c0000c0c5ca094100b1224007074003910103901003940200d05a0080d40f01e2800c4a0948005440302080042032100072148034000500c1162118000d1260000780036050040e003004081140c882c040c0f004d024444494400030b4080f900e407188000c185100000d82400544108034280103030001802c0d1740380d0011070309110030307088540d40c10b510303280c1008100780d039590240454101450082142403020740070801287c0c095441105903501004040c00000e81d0310307000701a4001c40c0c90012404169000100b010914161111505501e030f0400521180608001a40c0400e91840c0310707040c06c292580b900e00c4d8060800003410302441280c1e440054190050740c0c004000c0082d0548883c8610301035500945610b83c0b80440c4e01080f00200b84041d003144612040031003952501d02450044100c40c0b982c132400d03403460b80d626000c44d03024010702d06050401115180103002d00d0300d010500346810b1000409019064114100741481071007404a900742c005404042c0e00d080c0340400d40e4986030340c180007403503004041c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 564247383 1250 564246133 564246149
    0x30c071e12020a03110d171902010c09150e030a0605040204060b1c0902040908031e01210b0603010915020403030201050f13110111011a12010c050d05060406 69
    0x2000014620140e451082564000101030034045440354900c2580c1240400040e50103250400c0510200366480c070004c1c1910002090310710100c1c5142c1d40c01240000c01c500d0482107580c082001c038042c5d03549292100d024001032008110a8009000140140c20315001d03400410405a060741c025074091050500d902100070115000380c0c0a519020b0040d1000f00c8080780564140382000440501400983d0300c040c40e15074152243c8101104400010140c03050160780c00741c0c89407840b01c04030708200011400303007901103640501100161081103607520180e0040b07204a40c0c0018900741601402d41500740550b1294418403252510340001e13026144154001c2c1150064181c00a0006100d50081048a210740c0084c03040e1f64880345240741c0d54908490340300c45801c001070303e10300044120b10125516041418104d44003003542200908442038078a8042180000380c2c200c05151402c5075071850008400340080c0078454040200034803d000b03081035942c0481d11100400c01a54498110034080c00c100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 564248633 1250 564247383 564247393
    0x219031211070507050a080d050d0b0a0803030f070f0e01390b010b030708150103090b090706020111090109061803291308040b090303090423070215130203030c 70
    0x161460a240e03a100b03031011502407050101c000349509005020004484004003d8880c3c4803003204d06941c00c0c1c0c04000c1c0303901d44c1c0e9900c00e0340c1440d07a135548102c90040c1880740c0040d030301c0b450310f16034803001d102010307100005104054002c0074945a1007004840c1c58002841c080d007846c031806c00808411a801488a0b4403d41140ca0000c05820a4210000a6801051481c0c0c480c0d91300d003e10b040ea48000c0c2d40c010300144240000a41c2c02c04260005180148185400101211075803203202c1c6034a81540ca03030106da000b2090400140c1c0d424051099044010b10985107802d0541c2c001034801c45043c032403c002d1040c0d6110740e25103040030a00d1040115007003071015080105a140b900c0424500502154101d280c8201084046c6142c00f048186e007540030b51900c6c98141000050325040e0810002130780c0c184010025003529480782c0c0603007448515401e40540c05401e242000e103090301c0008000404650020300c80e0031100c440c03211895041641655000d14082082c00840c0c114443c01e04201d84500c5030f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 564249883 1250 564248633 564248651
    0x90f0105011d100f170709090e100507031d0118260a0201020423010c0b090a170405090c0a0203030a05060a170705011101020a08010b091207060503040201080f0702190312 75
    0x200b402050350151542e01d420301708054039440840c00600340c40c0e00307000038002c03101400009215406042c0c9011440100c44203240b050000d2819140f0803244180040c0d258001900340105031100c000700d49003801c009008041042c8400f046014407108003030710b04080411358509004204040c01070542001c400f265a8180c140c1c0c029010b58064816403803c2c040c001c01c100e8503007901d44161074401105942e802400c150f5601d60003040280a00810314a010b680384c3c2d040001c0c50031164101440d4501d081079151407500e410094100402000350705d050604000007500c2560120869900960b614400030721525040302040c000c41071a00188140d108410049550403400100d1500715403007643da8070515040603050600381e0180d0398050000ca031004006003c10411030002d0003031810003901400781c402d0480300091805220390f0005011400000034001076582c005003003548085075080c0e1044034100414020358440d40c0e540b00d1010340d91020f1040d010148200c1044503400c0f0284400e124600f2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 564251133 1250 564249883 564249887
    0x803061c15150501080609040f05010b030d0905120303040804150c200306090c010c080c28171204030507030e040203010f050f0d080415030207050d1706090f0105011d10 74
    0x3141c104668901c2c455400001101d6200300d500c1d0340308150103801c00c10a51243c0d50340c41d03c0c2c50020035084034155200d064170b44060304d0802140203224001c2d03456883c01490301d801c0c42040d580551001d602c5810820410000c15004411201190492541d200610b464204112486125984010800c595680840201796140051a40c200c0000c0702540c2480d10f4604c00c035aa00c582d0305600701d010800000b29100450030044c00b40444c0c1264800382c9001c40c89000c0100841c1822840c0040040550101030042c00014409103401c00e0000410b2131070715030b82c2101510011001080142000800142d080c10144621f0303410b011001d02a00642d00c1e9616506d07034410101082c000c42e8065400103111002e1490001845106690001282490f10742440700a00000b00b82d00842d8040c03503020480080050000c020305070401000d640d403108130a1100220b0102c18401030b004912030035049007884581d502d40000103044620900341240582928140800304000140c0724903030001168050600175a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 564252383 1250 564251133 564251141
    0x60d0f020f07110f0f040906090b04030207060f0201051009020d02130f090b03011b031d0f0c0103050a020a08010501030b0a030510020304050d020a0317060a0b0c0a03030b010c0803061c15 82
    0xa00c65404000000359401c18410942405401c4035403181c02d80d081d1004070300b01b40d805525020300500c40800c901c03005850341002c0c890159030803801a40908001c00240394000c0089c070700004184028401d130300307007200203100340308081c0500707078629031700140786142809164112428201c0c00b5500c100100d030764081400c1194554855019924145000d2003000e14061048042ea804811382e40d15100501002c02c90003800128800d901c90800c000300b40000703010070482036014801c501c0051a502c100100010255840a495400614010b0000d10f0000c0c0c6c0145895064800a00e40012207206420006d62120b200c1d503c09480d50003121450300100119400442c8600e006104032240300c44142e40c101d964202040010340095401c2c4080c81101c08a4190260048001000c4040380340c2c480c40100030550088940740c002d98401c038002e5081603054090011401000d080c4880b220207140c907218181c2c40020030aa21990440c18500b40c0034254108800065070052039017110709106d03900c074000070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 564253633 1250 564252383 564252397
    0x20a2a06060b0f1909050d051b06030103050d030e1e0319050903100b040f0e01050f090609100506040f1401031e030c030c050703060507090914011202060d0f020f 71
    0x45081100124482d400c2c0c0c4102c990301c0741d07840c03107a910b0000b0f514030341d841000c010000c41041046040000030745503103500030000f503a4001c2015002c0f0ba90200700026100486180c00c0f1300944c424801040800c0303004c20f4180e090000b038100807030001140b03800c49060540e2121030380719040c0e0a10803401c40240c004003811811007040700c00e007225041c06400365214050f4440140d07060340716804a0030b011004d0b030056041c0c03940290020503844007032400076083c2d031410b21040300c19a42d00d8082040c1c49580401c07540e00300c0800c0740642503905154141c9910f0300c65404041a045448030007090050b100c551280241c0010003138108960510f0000c0b4403a1040d0038401511801c9003031180da008026000050194650306480d0914510915581914180c1e500308040e5400c0c01000d000101040b900d000d818419102603031191141400c00c2c5491040b40e04241a0384c0d441c09804006110b411503a4045c8188150101e44440d103480340381d55144042c00c400c4490504107030000c0b92034808036071028050481c4c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 564254883 1250 564253633 564253643
    0xc1b0b0c0a0c0503190305070804030803190506040c1b020d08070b19020c031206010c060c0918020c0a080309030c07080106090b0f0109090513050322080718020a2a 72
    0x30b120350b20820581e64078281301c4134603048820000e90b040000e024000504440344a000c2c0315052540c0c80d101c5031820b4004a504813610380f844202c2c50004032013403154660100c0c08540c00c2103d0f8a20541c01040c3d00c0c035511b0701400000c0c0100c00304c02595a14030800181a6000301c4403695a44da910b4145c0742108192400401c0620100303040c0717201409030003a80c2c202490390000b9400c040c19080300c0c814140e0f01815503814020310740d65100105149000d4014581d08540b500500c8a16012510000030740c105005030180c0c0c81842942c40401c0040fa03100b0507182c0020007076840b070720740002c030f10f08511850b1010180d510030044002144041134101c4411035100342010050002c60109000507000603030314160018034941000d000d96144d1f580240d0b0001d80007140003400202d1903076590319650290f030008e10074220b00b0320440c0000810500c114058501c0c1c0f80604000762a00700001008030414132038004c641c0e00460044c071018400c960913601e221002940c414410141e0b10700350422600d841060354 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 564256133 1250 564254883 564254903
    0x6090c0e0418052b1e0f0c05010f090209150f1026060a0905070f080408040b070803060a0f03030203030a0203041a010312030501090e0d030902033414010c1b0b0c0a 72
    0x104440c09204503082180c00e0303040d40d01703040c0c201c2141150701034a245807076420b10041c3c040c00c0c800b045003441083c0d210f030500b400c0040d00754036030b004100d100b4400401c050030710756140c000c14100303460301c20b4038002d5085e0964070300f000810280019288180302c0744c10303004030041700c4a44091080041c03100c00c2c0038520540e203500c441070f00d0341070b00803e4480440f9208041034404060040380352040384481d0340035000d10341d01820b01b42c48100381c07280740c0e001d03e40a54200c2008001d0040364a44020100020420100c2c04402e07075281d5034020b5280d000007031014403515400b03c0040c050011804031b0140d4203084e0b003000407166031207240c1031002c0e1401d0109440043c2c0b410001246480c1c49100e208500050706000300034103920090110064280820101e815028900030190044d008060303140358081c00b540500c0e140341b114100c0091740c1c2035a5002d0686070050348882411a40c202600d4589030340c200c0158000c0e2201c619146901081c1030380400358220000400300c01d440000324404480a1245032026 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 564257383 1250 564256133 564256213
    0x203060d081c0b090c030105010806131104050103050c0c062e150807020f0c060c01090602040b0a0f03020a05250f061d0c0603010501030905070807030f0606090c0e041805 75
    0x1413085045501e401209800c00041c42550301480f40c0c5d82d030198009008031f6850040b0b0800c401503030101e0040001c4104007040034411903805000740c5604c90b004600440c10401c0d0034204c9a55641c0180159a603062400b810083e600c0f58100641441e400c1704104200461b40d030000ca000440141d0003c2000901d0b00003c180c00500c08200312180b01d041e440100340041030201004005c0d480303100d01103d03545d0380d900c01c0d100184060010748001c1c0182d044980d1200c815503009030201841c400240100751041003a9003403a40c00809640c10400d00c0b0381548264035007042d0024900c5480f0001420710f1440b501d500040000c25040484401c0d1b4103004150031146490703541e651004030f810300a030700950a200601c11075100754040102c260144080f0740c0d440355160101800c041151300107986440d1020445020b1043d49d001d100014210340008108128840c18018001c500d500c80d040e1207245c580034035600144040220066031500b141c00d454a070741c06080210340706c048407200c1c4200e505050080e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 564258633 1250 564257383 564257389
    0x7120f0306121a0a0b12010b100206011a0702120f010b19120b060109172a0607060e030903100608011103060120070e07050c0f1903030203060d081c0b 66
    0x240950280c5003c54112842090812210005200b128001c1d900d207001a880e07901d1003440024000b0f02c0c400045c005130004248401e00c000c4001c008259800000104419002202100211031603140026100c2c1154400500d155004902480491143c00211200a0f00640c010340703000314101c840281c104110391144007910114400c01c0c1038240070721114030200b107400340b010340d1000c0145401041a500c80003000320420b80c400c1041c11641c0302c1545c3c40300d860032003c042450103200880080d014810703d40061810301c541d8400400540d01c503107504014072000c10a440f48181c00809441440000320170340c400400c1584502101c541c24612030001088000c0b089034015203040c0d6400171848026000003400c10341018444201d8170840c0030004101c500401003e014008617900c090341c0d4201d950003186031240d00d070550051a000350700a006556814ac0c1490300240c2e00d410701603200d5480c540001c04d54000b800024142280c0000c00d02d810441c0d01003900f524003480030081204036101018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 564259883 1250 564258633 564258659
    0x60a060315060e0d06050c0c01051e04030509011e022d030412140d030c030b030d020d11010e160f0b09060f0d1d101113031707120f0306 60
    0x1094490114080038000548900c140f40722001c0c0190803024001c400b50b58540880380c0403280043c45103008204401040e40c28090290025100074000c00b0607130315000e00714220180903000030305129001a2907607003640525100c0000c458510312155584c0c48004004c0d49450401e0202460309121900c80c6152004c030384107000c4640e07446002541014141240101c4c84001e00405454480306507810491000c820000f031a14179400c1e039008142c141c0d41d4800074065441e800031092003a001280c075907507001d50004103514a00c0e4540703046034658400c000c504c1d0040012070030008a6029014060100315900c00541007111484114107080036135845103095240150740703015502039010031032403e2020b40c480180085c2280b1042c000341e80f0548480d4190041c0c16032114043c56080202d00c0e55610f85035109000d41401201b20b882d2810410400d06209014140001000b1141c4008181241840d12050f21581d99002601402861002001400191030900c850001030b04204010542c0c142c2044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 564261133 1250 564259883 564259901
    0x1020d08040b0114010513090f0b06090d0b0613090c060f080903030106030b060d051e060409020102030912150a090b011215050a020d14220b040311030409050f060a0603 74
    0x60b03515442c1d080c1800300c048900d0302d040f118100078061002d11903042c226080f61008004c9000001606030307060100c42c1c10750b02005c132251f02c681e40074048540c2d5038540c07030425503080d648103204d80c0e40c41c0c0e1858000760720230780d6041c01079503078614040e00241040b0f242c29201059501740c1d02c42d2004e5050b808012174040c0c000b16181a40341e0000c0c00100b2107180250003e01c2c0034000206a0342c14072450003803240458134100c5407040c0c2c0709001d9502c40002c1c951440c0341900f0031400e0b00e090104e501c0700c1d00041d54034440c980d2054019a0340104030425400b06222401d40629104003009582c104030b4020405171021102c2510000021000011030342c0d04441c8841c3c1480c3e00041c1c40c000030022581d2a001408020201c108040c3c08115000c052403407031041c03001c8501c2e200500e00c10307401d103804a00c4641207054950352104030445464000b00301c10281942d0300561510301640c510000184550850086501405010f0300300014024000041c4075454442d030001d0b180300102c1c560b0b82000f1410344040e80 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 564262383 1250 564261133 564261143
    0x30105090a08090d060f0f061a040501120912080415090c12150c0504030506010510051b010219082a0f0c010b031504300c02031005010f0501020d0804 66
    0x1603030800010074602c042c0401c0c031401044a641e400050316024181c1d40b4804030703400c0781991000300100b540c50305c1c802c800142000d141003003c1c041904119550b284160300645040c400111420202050b45801003180117903c0044400c8400b01d55902608030582a9000c0300e2042c00018403809510462281080e0035420002d00500e03a494903031040403180c20030701c0030342d5110840d00081a041c4101e010743c0a925526035203907540c66103903050103800c103081a0880343c450411804044507140d4410281d461510f10807801041034902c0d40a00d500a1189480300900240382c11900d213402c80e0042d03100c83c8903c40b500540800c81c0c1d1001c1c074011070401148070f0210302c03110911105a404030060080e003103054104000103a12900c400000703142441d0700c0c2200307103403c550310100800c005020200c1125054000340d800184c569458410769030306112018802001103802c1c01d0811341d58104001c55070306108000c10003507942c40b450856003102e8140035090151080c40349040e0100d2003103044c030b485039401c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 564263633 1250 564262383 564262393
    0x27050307200d0201030c031d0c100905101103130b1c020c060f090f07090914030310120804051804031b0c0504110702120304050406060e0904020411040b070f1103010509 74
    0x182d80117500400760b0340b07144010540e0300c1006180b103041100c51000c00c86109001044000035a2003001505824641034808001015a0400490701c4039440300c045d0714600d00b0541c60020000740307510302e14082c40018100d000680880002c0d000c900800070a8510810941c4804a035208841c0f041a40f013000c81824159101d2000140e040f03400e140c580b50401c0d503060076500260020398805281200c0d6400520200365179030800b10400071070009041000d014440074500b1441c18400c690742d070201034842e0300c42074600c1d2100502000010422640680300041400c03150940b903041c150820041160300b05d000c1041102d4600042d02c0240314900c805a002800c0c0074001d00700310034400a400c000d900c003030b0711a500344007800060303072080160803002d50803100860301c40c0d00e000b003000b0944907103601040a00070752000c40e01e19034a0742000d05a01c9501620045072282921088110300c0c8581d40c032601082e5404103681d02000550710148042a01a210821024810340105401c8840030349000d03c1d10f03402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 564264883 1250 564263633 564263659
    0x109080a020d052118010906020d03020a12060311012327031c08130327090f0207062004210204020d05070818030405042705030720 58
    0x20882000c10b1591040007034816400350701040c2e81114403c507020a8100c2000314a44c0c9483c0034a2500d0030007080246007854010b881c0c03a10183d214210304142c401096000200340303003414041c110000820400d00000c21641d82d5900f0101d84001c0075550460006001807508550702c508040c0b12910301ea5900d84040c6060700328442d8002503c11104030140b0b40084007140107041e6010b0140005c003500343c40d8841c1c0404000780c002003100400401c19070074066400c1082003c02e40c0716042e04034900c0c040c000b811b022080b036000030310342e01c4003540401d030324904200400c260203069801800c2c10520070034050008103982034440c90319050850341c080e03015200b4003040161000030b00c407905600301040c881460800b004d40204090340d00001307515445075207560900c00b0b081d0303001282950000186001542c680c241803501c5403240700780d00c40d081c030654880c1c01040201450346002503540307094400c103420b00005440e02980780d410260040d44c85030307004000402d00d2131040601101c8a680181950070340700c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 564266133 1250 564264883 564264889
    0x60a0c12080f0a0b0127180516020303010e040206161401060914010803090118090e07050a080f061f09020d0f05060a06020a08131511060601020f1e032703010b0109080a02 75
    0x40d08006c2407600d001201300000d20400014400080150500000ca032501d08600350f032410f40310201318a0115407040004010140030300f0382182d0480c1c1d0446041d56154404444158100c00c0544080d013200b400c80d600f0300c11080154042c0084848c20a001d010310b210344404618035003000d1158541640040010103a550301c0380c0d602c80b0030300d031a510f1840000c40d02c2c0d010b4002111207811805c1501d0340404020301c00e6140017243c1d4401080c54a00401ca02a1842203c44d210100a00b004a00e45607001d8118104050b80010303601908034441d0454441400344411005020700810f0040c0341303450200031a5032030500b00c0c403004c1030307a005400422603100c1c503560f980d640340e110340d10f0540004515440132450041e43c0c2c04d0313102c2c0d08a80765203444203801501401406d00c100a40045c2c103540c8041801d40840310b002c1207940400e07801143c9482240c040304100e5007584600c4142c42c120817055040b84810020f083e084090002c0305030000c00214500030015101428a405184190f03803159031000b00600d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 564267383 1250 564266133 564266177
    0x1602030c010e0a2603040b04060e0f1e0301020f180906010908060106050f2a060708060a3b040c060c080306270903091305010311060a0c12080f0a0b01 66
    0xa0384401a24590803407095205e00395001074100e038002510000301004401e0f0321400305c011080c02200c140180820400c005603001c4a5000b410f200c80075001c224048565081d8165160240558611640d42202d01e40d10311213404500f00d03c5110385907180c0803600039403003034441506803050b12005018590814030180c415402034940c10701c0420381048104414520352083c440703004030050140c50440e010008640c18920300038030303d504104100341000441e0760f941a4410860b98404c855409504500c2003404000c2c1c06c504034607406c11040403d02e003c480320b104039244100d0291001041c041e444036412200075683e00405005c469052000c10b01d186020f0700250341d10440105425040c02010b00c0c0c02c802c0620484034090305420120710302c04103040000c0e04046d1040059401c0009604541d20740502c100141c0841f401100003240c032401c42c90144000d070180b00e80089290540c002c500701c009110180071100d9410074000c01d008508465214000c03000041c00c141c4941400c031203804a0a0140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 564268633 1250 564267383 564267419
    0xa02071e0c0b0403030302030403021c050418060b03010f03121d010e24030105030118080412020a09020f0301031e390b07060c05040b071b0b1602030c010e0a 69
    0x40300e4030794070006001c010300c0020001184a601c0268580ca09402d0113401c107142215000000012540c0300032440713a10104541c141d500b8012280c00e07013900001042e004100c41d0300002a0701400200100c0c10a000789907000880c0e00c2944411108180010116049583c0045082d01da05d03110340c135403015601074500359034024030190070075030f81080c4080000030184d1030700f540d094800300c000014401c5003028024000c00c1d040d40d00106070380d0510355840242134800d5120f4000000c50001c2800d00310354680c0c00580040c40c44400554940003694030307803111036000707120444444001400c0320004200202200200c20703004142c01402d8690b059200700b801e14416202d017000d01c3c1c40180f9036807405001b0a81405031250f00000c903103401b00c9117060301c100c1d400c1c0d00144e401d0000a2104005260380f40c0300701c031a040e0748240c51485240d800c618510390840b940d0010143c0550100f0081d448458262414103414003c804544010041a0045d90000b42d900e5101c0c7c1c00c80c40c40c1e0030910400310204056890 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 564269883 1250 564268633 564268643
    0x5102f030a020c060f0403030c090308071403040302031606030c09150c02010e060a030501080c0a0b030712020d090305030604060e22140f030a0908030910030c020a020901090e060a02071e 82
    0x10f800296501d40741002011986018000664000c0c4400e26500d0300c92011662003034200780c41c03800d0554903028210b004e220f20040030600d00c10b2155000c03101c140300b5100219405030448450b286030407580300c03080805014000009180810500c5054811a2030a04039400000302d00c6180c036021801302d650501910040e4180803264681d620030741c50b00340041c04006400e0b03400280c2d80d414014864205004003560700e11680d003201044c04280f00102c01c407904440309007440034020f1403003822600a4000d400504078000c0c545000700c030074580c010009600c1440300703d9080100765115119040345140580e0340742450244003804001140e521a40d07a03d02074090440007007145100d1862a2404150070344191071500b01007a1140511341214150003d469800c0c00f86003044246c4011512644d1b00c02e07420404c02d600c94642801450083c0000f2a4054000e8100d43c0e80e580c507442d0104c0942111041e90076280303d042c000550b051072501c280e03900107500c010b0074200040c0070800b0b01e40c0808028400e4079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 564271133 1250 564269883 564269887
    0x31b0f020616061b090e09120406032f0313110307060309120c1707031214100f080a11120703050c040e0a0203070902180303040305102f030a02 63
    0x35035540c0d00503020054000307070306900e90899441c084003660b01c8210f5004003003031010032044000c0c1e0400114800e4400440c0900041d550350348a85140143e001842c02020300b0004020a8450b0300d81c100d00b40c0e441c030600242e1b2000c4e4104080907200722114140290310700c4107002140e08140c6111403040c08500500c010049161050700080c18580658031850200369035040701420800750310140654056681401c400480007030302c90301c0b542017140e070034505525400104681018002c0014504d12044020b0070040c000900c09074107a00c03101a51400034001550000103221841d000d4043c0c00d584036403000c0c1c01e0200701580e5420802e04030240b12507100d821505005841d4204111810007580a00d0040204980c4a018001114541100700c0300c079401c0b00000402503100068910121482d031040107944407000803910980c500ba01e1b1005505000000c0c1c004144100040c41c1b040e0465420410010b0a804e00a9044414180560126000f11784030b13401181140c0301002c0c40d03008004820140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 564272383 1250 564271133 564271163
    0x200c210a080c18031504060606080c040302040b01030e01050703050108070b130e2a03040b100302010e12010b0a0303050d11030105150c030708040902030f01050306071b050f0a08070302010b0a03031b 87
    0xd0504070554800344410401700104000d108190041301c4c01880d070790814202909200c6030321143c0c0d1041d0f00020380144d4840c003c102d5564842e5024404030b2014030020000c0c1d041c040c0004001e42820301c1340d40503a00ca40342001c1101c0c1c445a04aa50303042000b41c6901d11203281040101c02c1707100050800600c400d000310008914040881090402200c0c1d40c962039903031919140c00c82c4500400340c1006009c200840044c40141d80102210808030421602c0456403542c0c08199030243c032503400d40301c0e0400c515230781c000b0070503401201070041c00b1100d443c18000380c0740c201a41d00e0540000d104265105240c285103507501c00310f400c020189241002c00b40c916200300d17515880700740d40c071642c001016603600008000400c9004c0c02c40c64003404040300034003050300b45002c009060490700c0c404032030101c1ca03400340241040003c1058810581c03142c01541c02c11940c904207248103401c00c4a0a82c00343d400d10a0020940c0b0b4444d0713901d0242d95040d268059043d4459921250b00581210112034146c60103001c1c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 564273633 1250 564272383 564272389
    0x11040902042601060608070813050118050c04020304050c01050a030e030f0304150c02070513061518140a060c05030903120c1002030f0109200c210a080c18 68
    0x42002d04800004001680b8414101e1840c41d2148068010795074545042400001d601072103541d0482560b14101c21f0380e4561120b1101e00700340580008185c1d6280120703043d0401c610004202005002c2c01c15101c003020a1000e0005074481282d0082c91500008207107444c070b60042c0c02500301350f4064640001c0103100d00c00c202e8075603031041c080d041d000300c40403007080304000580418400c40401d84200f8448039407910302c0a5030b684114054140b00f00c19101620300030128943c0f02500900650040107900c204a49000c1c0444401ca100350104511560021480401d203008041c41e8020203011602c12518156048402c5081031208480a000800c419405a0b800700841c0e0558108840560394842e15105130500e410300d89401d44401e40e0040c0100b00c0808850036074241180c0b41d0304400b0601071008042240f084488800d9502140404070b0100781d80c4c240000c2d55001031809020f059002d0b020200001200d005030b9100301c0004800b0700004044a180b04050500e00104451901480b0b03011000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 564274883 1250 564273633 564273637
    0x7050d08041e0b01050f0121020c120d02090f120a2927010e2a09010905010503010b0103090818011808011b09030302030a0804110603011223030d11040902 68
    0x803e4448070310781401401103140c0706400840d0002c09007400c000500c150074102800740510803403001855404110400346600c01d000d40070700c01d00d40303003c40355461b43c2000300e0000039000174003550301980708401d448402d41010845035144044581c001d001d00350007580d1f0010f280d24004400103c821081d5032100089424114040c003800d41072856101040184800c1d21880c2080c4404211983c10048402000640030422120421131030b200059540c900074042c5e005200304034519a0003c0e0003d000003211226540094140c07401180240842518075004509a58060030003900c01e4104000d10000b2440941c9100d500c40c10604082d01c105240e1840c032084d10f00307070380d000500c0c0d651a80d5840c2c03181c170740c1201009440c0e130701410a880b240b030554800a40e0380c0108034401e024081481e004c10180304801000c089510310003443c0580e41e607100d04144c07008045109007101c810750807155410b4a030001c040e0658821122000640c18044603001803405008102c09860ba1002d0070440400c81d40c03c1800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 564276133 1250 564274883 564274943
    0xd0f0507110f160618081903091409070806033903070b090d050c04020703031a0108011a0f0f0d0c02070e040b150f0a081606030207050d0804 62
    0xa55000100c0792080300d5003008084099a103140d0421448545403000081c0a10103035241458150003007003141c3c0d0741d045040c02c4d6821600c40c9118105c02500b200d000c0041907a9228465030380c0220407580d5200e01c0b608100502c020a5000468100083c125480781000715030180e0018212000d4040c1d180300c6182c2c04004036413003119914400c1e81c49008012210702400d01d024290000d00001d49015030304120350080c01c50440c4a02c400c038030352030f0030b004041100484000004104665a590526011300201500c2e0001c840242304500c0340086c5602501c0c00d64101c0e00c1008611800c1100c0340d9104441d944400c05825480d1014003030013400861400c050645001030b004001034403050000040c4c03605600754030526032031209100300400218a54604e41e08484030213072413000d403c0081d00140d080f0300c000d14007940048000000203215400080c20903011030b1403030142c1d089a522004124247e105083d0094031640c80140003286051007a0003059005016070050000b50001c2c0d0081201030704070708 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 564277383 1250 564276133 564276137
    0x3140712060e060a140a03050d0c140318280e0105040b0607030c0602031e040c0e0106030b1e060702091303020c0418020f060913020409060801020c10020d0f0507 71
    0x803428800000003403051a015001c203280000441c40c0101c0000c240c00040d008180d8109044a020409030300c4106d03156001c1d43d806820f80761380065102c0b004080c940c40d03040990f504450000f004180d90000700071900d800101000700840e40c9108024846592244110744111102f45140703000d2030412250f607100940012040384446500d040100404e582e251500684100d408014210000c2c2e005a0220145640b0202c007503100c0d070f00c60403a446d0700a1820300080d40360221000301f1040100144a000544544802c00886640c8540c411011613001941060f04003030800641700d07008107c14024100c0020081c04c85141c205180d0105a00c1e22003901c035000345003401c840d04030806406102c072041e50314050340d04100e40b14400030f0300b50010000080281c001c01c090442500345031294401c41d0304400002e44007880c5071071242c1c241402035025103d4010200d103040c00210300e00ba41070086940b46003da0740109480070040c69014001d44c4190b488064a9660b80e10f450f028042500410748145000c4d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 564278633 1250 564277383 564277397
    0x80d081608090312040813060201020309010c0906020d180906060207230a09020d1103090f0f1203010b0c19060f0b0a0f0b09060f0403060b03070f0b09060901031407 72
    0x8101180101900d0184000034030998408101c505407000054504440a0341c1580d0300c60780315418540c005100307807605251810061040491003d03015001907001c1e41d401c0c8002c001c10240040100c510841c5402080c005030450100040464805d40f21032038a01040d8103a13000b4603541d524088100c5e019644200301503004140c1c20080101502004030309141000301c0402c840280c0000101250030500650070215808201e403201070040382d01149840c00c004000701d80e24241800070550b18803039a081c02401c1e2280d81500f4840c01004207481c0480c01c0030b1420b180c01e69080180306d1100d0b800141d0804103902c42c0052000404e510148200c0d140c1e07004030400100313120b01050031780c152101c1c407114501a103c4000108840100c0041180c101c444550f06152500e8450300010b00d5031180c40c0c4e041c003903c0030114001c81440301c21740c02590f0b051411022074040699450720901a08120302c5042d00c845010f1248021034100580100204401454002031450714031441201c070300d4007030313600b2400a044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 564279883 1250 564278633 564278641
    0xe1302091014011d09180c0411120912070c150c0213020c0a02090a02090f090709151205040506060a0609180911030d0c1a01030f110109080d08 63
    0x30800180e5088244008407021007801d000b8244142101d010419041000d010704a0710120014043e83e44000c50040811010b820032515441d40900428041a900e01a0110040b068949481042e240d01c800b013600234144040d5100b0b5400c611801442e0320940e0040e40d1203081c034615103100500e42c01d84240740400280e41004040e11405034041400024030043e02e84e90000360760b4481040d80c54595441c4091394445016642c44e0030702040141c02900042d580040c82140352058010f0024048180c600e8130403088840304210307010070103a68000100e0007100e420701035003003400700b0136800807902c0c03c01c0b10301c0010304840304081312002c40e0107403400c1e0844420b000c0310f40307014484036000b0051407421800d09070400342400d40442009044010081d80ca00003001009030301420102c40742c800505640c2c14109841340034041005460085602d00b600c54203503913003222010b122505803a001601c02d0380000301541c4066070305d1010315056042c40300d03d00b000107030a0010481c00300500851340c0d452700ca90030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 564281133 1250 564279883 564279889
    0x807051006171c02210d05090601030b01140a12030f030605060a140c070801110a021002191110060f03230309060d060503150117011406040903090e1302 67
    0x1990700001d4994140382c04511000000054005140242c5820b1402041500e0300603850910640300e000442003c18090985240c1454054506c089501c0000d004c960b642c080448e0b210502400010b0460540c5001404440c174802c4002c0c0365000041c0c01c2c00480c03a222040e440291583c148120b000444150010700802d9160160030024601647c6071401d1500100015000000703034060034203145000700c1c01c074900310341c20441e4000a1100d0002000041c0d00050000220b0788400e49010161003000307201c02a140e040d1013241c09901103004010f100e12510300c0200c5030440d2030b04175040148150907100741b107000188218001455250010740b812851494081800c80011400001c0c000b0405482c40c600d090100c1166014441121040d070f0b80c643c0d031106440100410740102c0d4061080c03501380c0c0a05000030020764142e0b201c0401040030b400a03015140d00340c03044c94400640ca4402040411744500740f580291000b0741c885c0c2007031182680c80d61a0b400700b8607401c8407d90401c00c0300d0031032401541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 564282383 1250 564281133 564281141
    0x30509060310050f041b0c020301090c0b130b070807140307061a1005090a0e130812010905090c01090605160602030901050403110609070b0706271110080402061608070510 75
    0x128107660a100180b00400c045070220400c1b42c600003404404c01003007003196020b602c032656082e40201030700034407a19003420441517004071090401121640001141c550403040c00d54076100d9010310a54600383c0301d551070140c550300c0800d40340c42602c0705001c0000080c19901038400340c0040ca054048003500380000f0072025124000038841884020400194a622088140000e40e03400e9000184a0f848814142400701d00000c1c020f1b120348004600014100c0c0a014194104c030f04600381803016880b202c292079214039000103d02c1c041140d120040041c1801640034151032503d10481e20903e501640f1282e080c0da00840d5460740b0f0381d40d105d042008241e0014100f50040301c00070001c0c182403420108103030b41c841d210300822030130301000b040c800100034107074101c206449101059a00c10390b1b81c02c1a185290b164500007215100d002d103000f00380d181071074824141d4040c0603548400050b140ca40034888c6a911890075078440d9804440c030280170480701401080014401e50090844010001c5003174121 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 564283633 1250 564282383 564282409
    0x100915020f07020f010c0503030c030609061503150a05030a05010204030516180b0f10200d0e01030e210403030801090203010f03060c090e0705090a0e160c03050906031005 75
    0x10344140036212000601c8400d8940050781500c40b5000711a0f01e40041c0e61030380207070000604600c000400c2288085584000e14001e00c1c1c10740346a14191980001c103c84200d43c40c18200d8032503c1070000a48461404104c0c2c04800d0002e402100b0003901c4d1000b1908060b03404205403040da40004080040240400400c050400f2004184003000d090824101c0100010440304104684800741d003045a0b07165410010b01010052804002c0b08501b200544002666000c031242405180e60003024414041400340030722900d40d45001d03604a4050066004061440302c6d95400d2003100840e221600e0340f40203000c0e5130600045820384543c40c41c98010040070058110301841401031004021021801000009903a840030001c1581e409082080748c00c500c080d400407104001c104144080b40d50801d00070001030400b5200c03501c03c039031601b052120010342034408004c17049140000300380c0644220119202c4034840e18080e440c018000001a080381c005640c107481592075200100854908203040e5900c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 564284883 1250 564283633 564283673
    0x1605071d010f05180615040b0c250302061c0504060b010305070c0210110705040504060e0f070302030a022701060537050a1107141e030c01110f0a0b060406080f060c1b1009 75
    0x410102c0312b901511801480c80000d0040e1004540186808c141940044402e000483c0802c5189040d0501c0006002c00e001850301207868071010942c030510480d29070f4440c503006001d0140444444604403030680900c005503001d17000320b200c081403550b558020680998055003010480e4800d0342050343c28010580c81c00141c5d980184010001610082102840e0075011200c000c11103954131800d80c019486070070404021902da20012a200d50498045c128030100c1945400e4101c003402c00d040e180c64028681d00019500700400006024032079002408050f03882d2401089100000000f10b160503100d4004401000c464076110f0624144111200105000002c10718090b1451502094a50040001060410207a2000c02c0308840c402c2054043e556030b804115400040c8e28100030b50103003c10345055224a0410400140b040c2001a0110003002828003424035070315071001c402d0240d40445041080307519007100e450b01825092101400031422114046426040c40c60111802000c41501d251 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 564286133 1250 564284883 564284923
    0x60c070509060a150e060702060c070303080a020715050406090f061b0f12110c0d030b120d08393c1605071d010f05180615040b0c 57
    0x4100c6202e07013402c80c076540b11420000d242d0f200c0c0102140381c1c1d02c41c004010350800000500046013800000b01242101e0181d502e03048030741c881401e03000aa01c61020050700e039000c4405220500d1b000e65002a42040c40b030349001a503071003280e440f4015014a881d064820030744e1090904280310207210040c0c203406046c17504071140b0401900c060030a03e81180102c0010342e861301039007050035203c0c08036100c6d1034903201180d46c50078841390024080d16065800e64040c420300001c08041c3c21001903c80780c002401c0e203071040700d40d03620986603180c9540b28141c2c0300c042c0c0c055105c09604101d0b0340c0749a400e075000c005089a5510219050100b61002c4887d2580052900c08504000c521000d60f04030000d20f080d02c8480d13450b507514142c004a048403a03006080c600a4880002d605101c0c80800b54404403811950041680e99403e0710b0381a544a10403c1e070440c060340d2118891300080d100d0b441d8420001401d185005655605a05450f000ba41144044880000b003070307003c0d130004101200c00c0b012003c00320b030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 564287383 1250 564286133 564286139
    0x1409070e0109050c0304032007081f0b030303070f0c1502040e060906091602030712360b030405031908150301110706020f040902030a0f0b01020316020f0f060c070509060a 75
    0x18405e100c02032000d010049104203e40c4d20a608400e0303911b5504441b030494500580318000e458580300b0b0210034000c041c50400415624445d00d000d0080074074070080c003840c1540d4030709005031134a4000e1888101040701c0d82c429038000a0301c180700401019189c0d04010b0316a030801c1040d1240d20303009131619108480302e008020155131510045640a82c02010106080c11000c0d4140d155000d0071500804000040140340300329984400450b00301001d400840ba8100640d1005092a21040c8808a0000c1c0c0e04c5c0c405101d10000c0030000c640040c03041c400c82e85040c0d0105071803086014036400d40030005625809004042a02221800c14007000300c00821514a000102050354450700788001d19490300864a008109110020782c1c2c01000710305015036a2346044842c00009100c40b42204144038940195140305520000c00c0d2200c52080a901c1d90124140d41c0812000c2c059214645520404c2e20801d4021170b00c40380040c0c00443d40c1d403402040383c035081c0810403000000084c8498040c0e05026020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 564288633 1250 564287383 564287401
    0x30e0c0d0b07090909030c11120a1112010e010e150709090c140a03290102030301210209090a0201091409060d020a0909060e12070221071703030a0c050f0904020d1409070e010905 78
    0xf540740070b0b61042150152f0301c214004240300b0114814101015480e011042d41120810741005400746004425101283e0810350480d0702d14800b0350b43e60b0001045524144190300496124010200301070030400c2043d040b0100b40201a070290120500003902d07182142144202100005100241800401c00076010715000070b5a0780014032072070300d01a41c0742100c000e4018000205107080740d0054a42c1c3c03030314070781043c80d269500d501040490020702c6030a0000340d0220142858617104400038254a920780314501040985c10f0004810703a8015178030700703002075001d03118411407603164441d40b000316a000b07140c16194140340d034105050030710000400c01c00006954240200381c4140140c8580d030320720141358450701d241c4209034000c2d0500340d0381d0480d00791864000001651003103541400c1800a0b80c00308400700c0d400c0c05107816083c0001024001d01071140381035000b90200410000e000a500d02c5d21402480008806844104898000050078040d41450340b84603405410b000c041031040303040054030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 564289883 1250 564288633 564288643
    0x27031f0e0d020c060708030a0e07080312060607030c02062107120e0d080c03090705210c0a0e0109020f1e070515060604140607140d030e0c0d0b07090909030c1112 71
    0x3c0c141b000000000d000744c80f141e48500c3c40303600c40404680e41076888141480e6240c4c03180000e402c40564010001d451880e01e0750450305039a80c180d45080319100107600b401140c1d001145035024941041002116108081200900c20a00365540040c00d10401c45c6e8441160300034001d82d092034008031b0140798115081000c450b0007541c41c046103652940c41120700e5080c8401c13500312035801601d160401081e10180250082104000d00c00d66102e01c000c1410006140c0b194030800380090001401001203c4155000c6c2070550b50540c03a05140c501a08002c800c102d034840e04000e134540000c2280020310000300100d003082d00c05030111201c01d080c0100061018080d500c106150090315145a904075110301042e10b5a1540c001180400d1000000e6000d8440e1600744442000900e0080740c0c240c0d08000107a0025034403400b400e866104680c42d22a41840e6000904100a00c032815100040e002018454041c11500980d20003a045415240802c2c0024000e0803841c842e140c207420042a966011072 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 564291133 1250 564289883 564289897
    0x219260403321e0f041203030605040e06160905090f01090c110a021e060307090e07030b0d020d02010306030c0314061b18030c06070f1727031f0e0d020c06 68
    0xc0044a140344030000448070340300301800150413880102d800614031203042552580b441c030a4074144512903e0300c080c0005c841036100c582c0d2060740320303a0104900c0d50910340d102c80408818540242c3c255291404603004800540d41c1a00640d4000c004000b4002a4410156141100e15001000d58440d50106543e40b03c1c001020f407240100d90442e44501c000844148014880549110740700c0c5480030000c0c0c0600381e0340c030841a45659030300009100314441d01c15518035400050804080004540030b0003421070784440100d05055448002001203900c00d401e000040d88994210800d0105045525003804800360000c0031180b003050241030002e074044d059401200d800c07000c0841c00e09600c80081d01e01a0107104040d0400f4001800d0014840220300320003103a40070310700000c909414800d59001d14414071880c000c01040800318403107000d11400321902c42c4000182140c80c0e640d0784003050320b4913030100401071002580c0e0b880c001010340c3d03050044031000003113800034010300c0307020001107644c92050305 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 564292383 1250 564291133 564291157
    0x607050a12031d0109020f0411072306010e16030908031801061e06090b09010e09040c090c03050402030114060114160f0302070315021926040332 64
    0x702011152034401d0384100780100c840c000d881040007002003698001e000110007a0b02134440d24800640c80d0419009411480f85c02c4a40740c1e02d032030b44640343c0c0e243c803080c010f0301d10308100c0700f40d6003044c50620204940340c041c1c110f403030f00c0304424181103039035190032000c8080351070a15080ca0020004149a14140d0f98800d1250091102d0110303812003582c018105034010b007e00300058031501c50181480710503581600c004c0d40f00d080400741c491038807650314040c1860305800280c00038507081030b0341880d202c041e405c40c0c8520385c182c00c0d0a0300c0c0e5041009840040400780c0020345d44208000c1941742c2400782002000034200e001c4000d003064800200100603072501c1074600350700004c4201c0003803a5041d55102441c1c000e07038154550784861500a40311101da2200356106541c0d100409000d11032442100c60900d120380c0810040c001a09003943c1e6042c461045130064415010184010510181068880d51180e40d409000d0710703000e403040b0b180d0824400c145640000c51081c007078840308040c00315200902c80d4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 564293633 1250 564292383 564292403
    0x106033c020a0302010f03020d05040b0604200427021c0c0f0e120a0c0305241003020d030521270601050409020a1512110f031b090406030f110607050a 66
    0x6c4c01042d0084d00c205c00310811044d15100c2000f06001e2420809401580211014000005802e4005031511005481c3c04020001003004110307035a0313981c4e2501110100600f410f441e1106e000355903c01c9810141c00640100001c51712560012006d10071422107480b0b500780001101098032000f002c00c100c0001daa4040c0b1042e00715508545410444003001640c850b03113110100340c4a10b03040c0d4a501589103400d01ea80440e01c0000012640300189511400b01000911030003440c0d0b07002c12500c241072044c25014040e08201c03e000c81080224000d06810b2401481a05410300140e40001040c40f2007011100084903540d20321200c20108000741103030b401300c07804558100507000051500905600610201c1d81601e814114075811008440840401c83e02c100101801e203042020141716a0504e59144002080001d114010110404002d04d9031700381b0203400c010f10400880d086603178680080e80c0d100381c082000d608220403440600340350324040d90220b04050581c1d8a1582d54086020000c1015101c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 564294883 1250 564293633 564293657
    0x90f060e09102f070c050406030206030c030a140c070b16050d021c0e0706030e0d210608030d021c2307030b0603070c020f0301110a0e030106033c020a030201 69
    0x1400545112400180c01001e21116402c00104502d40c0580803c40f080c40c03030445c0014041c40e00740f00311002c50350081c011030f14554400c01480f100e50300050818030016650700c000d24003000d000d2101840381400e000950fa4840341f034144501d00d030702d00401c0c100c5541000c0c58100c00b03207540101500c044c000b1106015840d20203641284109034078450780480505d1a0010041080d10009050421035081c0d4404009000300303d65059103078443c84100300040b5050307041c0c03880100140c54000c81000301150001030b00703d07100c0000506540c000168800792540208142c4503140c50281d500103c3c40400c48100941e041c5030311074400d51090203160140e9006c601000a441c00c1c013035004060000b400500195503480d16000250062002200503400707040b0711000500300342014850300d02401c82d0301106504000382180116804003405501c15019504d65800100040046c1c91000c90300d1039050041070b9040b00c002d9800340c0c000801e200300350480d04500caa44090b0710348512450581e5028a081c4003901d50b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 564296133 1250 564294883 564294911
    0x7090b06040905040303090b0114090f27010c0f0c02032e05040516050603070804021011010e2b0509060702150d09050c0a080c0f0415090f060e0910 65
    0x2582d0000c00d030703941080c04200c1010b84c5640710356040d034820002c01c07206989509108540c80d550308080380d00303c20244003040c444490030303080540c0503c03c4640f480303000c000c079194482e0081c0f141040d15030f960b444047c010103c507000030103105070a80c1481c1c0700e140ca6140e600000e59425030300c50b600101c14910b9070480c007080380302880380e02002c420602c1800315041c203240450751030a01c0d211905402d99050000720301807411780120382c000c04180c1d8455655858a07000c105403e001d0b082802c0a0080d841c440404c420002e01540c281e0241000107055a5a01103460321050702e0f2841602142d4201100d0444541da0010165500440b003600c401d42c80e052148085113140000c903807614101798003c01c900c1b410b01650b8002914151248090ba5282e0566000b40044503181d4058112103130082d10001c00981011011044403000082c00880c0d45c24410700405401070158101c80d10b81601c4100b117116094041c040c520007400070681a07605813404540050300c2d2506003603003100140c1c59294441e01c0e03503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 564297383 1250 564296133 564296137
    0x150c130510110111160204050a061e08160b0706050705090a0b0a020d0801140909030d140405070b041d04151802090f1501050703090807030b04060f0506010207090b06 73
    0x310028081d80601441000050b20101968080c04199800c180940c9841148070301a6203200c0524001d6024506050b800c101c090b110040c859a03410b0b80d00c1070005641c800c100c0d00c14a03410b51550031100c0d0681003c1d0035601b040303030700a0280d00040040d5020441181d05a0031104042c2d0001c400090640f02d00704111340341d110f240310302039101040100228001010700c0003803e410400c2e40880e01600100c040588400700d00344610001704024009891060621080c42035100802c442940d1402c2052104103044443d100051b006000d510b0781040204402005544044c016400381d080c01c161400c0743d1070168000a40d0355134403084501022404004d4150000940b00518601c2404035500d950342c10a044442c40304182e11850521011800340e88409031018007402c4400380410040f00410b0041d01d540d40116021001c01c00302680005e400d60050252901851082034010214205410440e050301e4441c0300341100c0070710b00014080d0360ba8000504104507030386a0000305104099400090a41c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 564298633 1250 564297383 564297389
    0x105012c070905100f0f320d060807170f030306011b02090f100b0f0906091f0201050106030c021515041113150503090316060f1a01020c0102150c13 65
    0x680f078400d21550390f0000020032a0b21400d903940a106400604120386030b50b05080300141644a04005034080700c690854141e0b06180247d1b05850111043e580328102d40d802d0303011200c5900003c401f804403100940d840d43c40c00f001180140032950610720300781e80383d2201401e1503041c0302c3c603003e8101c40411110800314407150000c0034807103c2d1810141000e0848000c036804001001080b8010440b8610b805c01d6440f818800d003820350405e1450401c1c040300303034804003d40d0b034042c008011442000044205030700c4002c0c4150f0020605514102d4082d09846c640c00700c450a6410002c0c696503146022031f2210362200811400d40b0a44103000080f4005000b4415603080304040024482040d220351192802100c590541007410b041006004071039078001540e0720840e6030410850129140c481e144100044c0703005200014a0514081c0c8107821204203c070261800401860744c102c0355178040c0003a4142c94002c4c005400c8085100400e44400c920080034800a80d0b804681b4100d0707008116459000303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 564299883 1250 564298633 564298639
    0x1e0a09030f0f05010b01051218011806020901020c010504050f0907030e030406110c01090b030718090504050c04060902030907030201110f0106270b2b0b13050105012c070905 76
    0x19001e1a414100c18611494100707441030741c00c00c8007030000c030351181d42103480300c240d8242116001d850f6194a12220040302042d13412540d00d0708445005501c0401c03402c1801807213608010380d0307041400006418880c0300e800c0141880740c140030030082a1142e41d200012504102c40850f05544d40003019001800300760030b0940148008600813031b03006e400c5241800601580c104950998810f0001115841028081d1503004003040c000324800500949420b9414800298204001515a604041140d0044606a0b003503840000b01ca82107082620440d005000000025031440c9020803c880e511240c910000741007020500e0301c0410380c00284a00c0c0b445100310b000174041c2954900501b080f2105264000e41c001e0309522400d00425024030543d1000350001e8002c04004030107814030751990f069401000d480c000081240d0000901019495100718101c56603c840c00170b0506200c0d003142e50580040c100f021444071461202020314485240340c4c8156208a456607495460465856031294080c5130 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 564301133 1250 564299883 564299903
    0xd0210260c13090c020304030f03091212030c0c0c061b1e2001020d050703022b020106120c03020d02060d020d09030314060d230a0501090303111e0a0903 67
    0x1c40344030018010710500c5041440d080003182c40342024412a14501d2050f00036a008100030030008042400d0700031594000c0c00c00c00400e55480c1c08141030318482c0300c012610703480000613451006815205110020341d0510b40710700510300f140d9030a2444070f4140503d1041c000780e1659200071480349100700c41055072042c500d2550800150070040c04d88241d81d4100d94018041e1a05d41010000307007106002104141e000b001451041d500c150740d01d50203100d05808602170112a0744400d0f107501001813000050070002800e88005d000300070f08540c0310b9041800201d24101c0d400001c20b480c000180180c0386c0440e40540d01d4101e0348000750180c41425400b055050003c14407203a226010b51180d41000d0080c2c42c00e00c888403000c6164a82407400f127900940c400c640c00d41c40400310341c42c0d9456021440c0c0a11505080c3c1005c03c1440345003901048084440380c0d11040014101640f41c0641580c400d03045017130034105030b8607070603410801e01c45040f03000f1a1200414510180c2c0d00c030b108440002c1d03421040b129 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 564302383 1250 564301133 564301141
    0x305071b12121d0102190c0c031709030f070f0f030320030403052a0d020603281104092007030c060204030206040e040606060206010b07060b0d050303090d0801050d021026 75
    0x1e01035000306c200781d01180c1242125a00c8140074168040700158440b072a2004582190380344400d1540b52128001d9608050042d00120b44040002410f80400c0000170104249003442c5a142200e003600320591403000d030403041001030b8001908800c4210104a658108401144031901e940170300d500180c1603101d0071024042103400c042d915003101114041c050b60014542c8140896980580300094001604000003151604d05051101214002c0c1540741042c00401c0c0c0c404064451940d4005409000018104089500e034032484102d000d10740030f016440858099610071500030100091300b0310410404950800c28258100d42c0956801000c8036203841c0c950740c1c4d40305000d20480c2c045513101d2419201280300c0e8000100c083c103c400f68107600c2c1c940041070f80c880e005000810889070300030074524041e0380003078801d0010f1803003514894018a600501c159000f0050441a80b106e8000d4410b500c4000140e11954068243d1251909090184104001c00e41c003040200445500300d40d15000240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 564303633 1250 564302383 564302441
    0x80d0e15191701120f02060304020f0a0b04051f1b0807080a03020c0d0207081b030f01090b0402100905030606040518100204051005030c07060b03100c0305071b1212 72
    0x1120071014282e141c140b0326a2070b40d4401000078010480603220300380c00300c0070b507005141000c021075009201034910070364108048046032045d40d040d0401400c1c018041000d01541c02e240c02420500040d040e0684040031400c400a02146108911035100c2100c003410401406a050111207002d948000341c2136030f900c5280c10007402508035009012140c0030b548941d03240507200050500c00e450011000e4241500081015014003440c0c481d1a9014003800038100c800030004e10403000f81c5800b07850302103410301c0c00c0c6c810080c1d007464800000b005d000900d2410700440e240055100c1d8006002d4030000340c2510340c881007010f4032031020000900791240040000c0c0786902074002e80200d03030040d102c041507040c60701d03070664190008130b4004032518814841900426071035000b2100c0c104000d030655042e40c0c211051102070398456032031140400d4941c0b0500c04c4165200910940c00a0940051603482c00c1655a111490840c04a41c8080200b0f400380302150942c5584108085e4080f429107240c04910143d034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 564304883 1250 564303633 564303647
    0x3020606090906091b01031e0609050c0f07030c08041203020703030305090d020c101b0809130c0203070f060b060d05010e09030301060f0c051f0504020406080d0e1519 73
    0x41074024140c000125010803000200c40c0d002d9543c50015201c2e400200b055502c41004080007030381095243c61314100548083c04010ba4064111140841d040d03040200510a89001401c0c44190b0201008411107078a850015100460752515203003159031074074102811103000b142c0085002c401215450420503400140042c11640710b84c8040c00103a540100310782d1a0340001028802682050900000d10300e0400f90412061145082000003001e1080400d0400c64400e4021034141400069501035403070194040758031960404000e205103056280000d480303006480c0000c01c01c04c48241d510040142c01d4220717511040c0d011f071285840320300001228000d4202842260b8005512102040607281d0120469060303540c00d0300c80c0d03644201d5605049401d051f0300c210944007406841000c5501108044800041a84008001c101c0b400c090041004450403603000344010fa00c044070a0300b1013074000c0d4054040100440d034065103100140c503601682c1c4075011101c031448112407141074146801580e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 564306133 1250 564304883 564304891
    0x4060f090b10050a320c2401030804030816060507020d030e070302061b07080a120210061404020703030e0a0c031a0105010207090b0111070e1605070b0f0405030f07030206 75
    0x265034207070340902d80043d00e0070b114184900002602060480d050f81e585040c4425010010403489044070001c000d49071110781044001850301e4005a48211a143c000c40c40901c05429002d1103102d6540b45030395510561060b441300414001c0c010540c030310031000d03031503d040255030020401c1c0a50700d8010f00080d19240030740301030004285403541d0182480d40000b001c40c250703640a01501c0c034024842e41c1c2e4100340060301d0042c42091089000100b0401000c0c040145268818041030310650381d4020042e080800d00001000e2091a0040400c220203044094803a4481c060781c005a0f1440b250804030040c2000b000403038034901c10804001c04200d00310740000101c84c05050444d03032a050720124842094028880d29005a02102e0b0601004265901c03602150205061a4401420b0000c0071814400c1540c000a441c030502004c1005414030003104640d0340040d0b2400f44c1c584001983c4a082d8108060244043c0103286c00c001000c101b410002c56603442c0a080c0c1d02a241c00c810700d8020b6403004121 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 564307383 1250 564306133 564306139
    0x40611030304020604170f0d020312091501060e0f09040b01140a03111c020d0f03080109020903070b09040908130f0e070806010c0206040b0c010f112704060f090b 71
    0x220040644040100999024941c01010b461610349003a111130303916074004c1445030352130280001e020703070b1982c00704036a04c44031320107030003440c1c488000c070b001245420740007054000c0300d030040e100c0d031800e0074001070116041d039200d410002d5199803c040400c4032900d141e0155a04402c0060510051000e506040703070493b501d8000074400400e5480600c4940381041c071008090624484612030f051402495103000c1c0790a205041050540c50340000300315050031a01590448a1801c0c0d1009150f8440385c4580504040082949818060750100395260322903c02c40c40c40010200c0e02d0081c9980715040800704a4105c42055102d1070601c0c0a84003c7c03200d841522184e0040c14400103900000c01c3e20746104030301c107880d14100d90341e030302c0015504100d40640482e4051300800000c42c0c240e803883c0c00741008040003800050411891402e070001c480d0315070850030441e10123002090182080010b0250034010f018580d5904e0109000450081c01d65900524072101d14618049424003490303001421143e412 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 564308633 1250 564307383 564307397
    0x9080d090321080109052214060f0105030d0513050303040b0c010606080f0a02070609021e03010e120307051605010614011b080912100c020f060f0f0601120906110406 73
    0x828030440110301584020205a030a00101700641c040d50005501c541d0301e80e01d030020420248851082d40c0c04080d4211401c07043c602400c0140d0382c04004090380140c80c2e8010381025410318001942c0c3d10020300107d02008030004254548107503e01c109001041301a049a442d035803510080c521641107840c07001c0d0725610b002c070b000860314841c00c800c81c0a02081101040f180c0c40741c0d10b401c0c019503c40350040c2ca40039125000a001601c4412100038180200d80c00d080d010300d45842054252200c08000400329130203800070a42c500d400c41d0441c1d812544a00f803a41d6500022815139070401e0b07100101520951800600181ca03140d0241e0101da10002680c1d110340c1400c10b5020304008203200740015081130307010b0202c1420f904002080c8205240300d0300c00c44500c5640268101c0a03284604640c40040c0c129092408125004108640e0005c3d03072219401c1c024a8850843d60070080001e2003e410006021000c5007002e03125440030300d6154001c4000e05c010b05466080340e02d1075110340715060015001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 564309883 1250 564308633 564308663
    0x7090603030e1e060414011b0b0a1d060f1003052a100c020f0a12051b10080f1308030403020d0905011715061b15060d0203061609080d0903 61
    0x75070031036600e1100340180706505084c2442004c05c9030300802401941230029207003000e40d560301304180c80d46482d4400c000500d603c2c504429000241c0b0000c812210400d003041c61403130024080031502643c0440440341011195950071103079050b80c0b40550015025018284100c80295520054560600703400070902c80703840242428030064203c0d80f595040010b811307160560061400c01007440b56100020448540c09440740f07070f40c0c4420713801000d003103a03160700081040c40e0848026240c6024400e0480d04802034250555014100300320080c022580300342000001200000c0c00031002c800d581e00310301d81da51203207014074000c1d5541c82d10b17040d120302094210324006450b601c10854032041e51352020b0140c0580c1c54910707100c14516400c12a1551205060101d0300c184107603000c10689400c074080040a083d03103501c0005540038405000c15000e081f120402e0b8000d620002070b00c40d002680c1001c2e106145280400488256070507400034861401110040c10403182d00000f00d030145d0f400358100b0900e50704 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 564311133 1250 564309883 564309919
    0x9090712180201170403140c0705040e0106061b0303090f082101120615031b06030b090f0606180613060801120c0506030a0f0203010605041403070f1707090603030e 72
    0x29807181d000f8001041640d20b00035a000d074a00701d40e001842402c003d00641000441300d20700360440c1102e00c40d0356020320310401041c981805008000003115000700200da04000c0c1c024181200003040c503805440d10300036034003018403e40c0300000c8582c102d000e000a1418514000c2c1c0c1c554080c000550321a007a40c8591149501c0e01e09025048650100302200040d0065545202400241880d81129910408004042103920011440c42e4000d03d1003052458180340002d070407501950201d0b40900504000c002c407864130003420350b8104404032112612a139414010241c454048107400340c02990120712042e040800d41140c03002e940603506c0b109140e1382c8602c805540c031615040301609420350694108090b040440085411282036240810f01c500061343c00c500760390003030f40040c0001e030b40064100000461a0543c003613021085000d452a145400440b06a1505034010302c1804c070a0f828020a19010812540b0003c042001c3c0c14025603540382000342c00202c0c409810b0303004e40e030b052450030b004030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 564312383 1250 564311133 564311171
    0x30c030a0f0608031603030b2701080109050a030e0409020d050d031107020f040903021006031214090a0b090a12050606090c16080a03020c010213060e0409020d140309090712 76
    0x240142c0300a5040a6005c1c01d0780130080c1c103103030055040c559205250245502c828107000d403014400c001c43c1c605540000e080301c154a40591060b0700d540d1400e400700b0009000410700312500c41d014a08180311100020000b0010322009000075440003d0450010401c2000f040c421007192250310304000e102d92900080020384900c7d40002c1d403001e82030888108038907043d44a040e840d8000c1c412a03141114108900c0c0494045400030f6603118080303000c84c0075055104110340182d89190714018100b05034400030411200d000e00400b24000c0b40440c104a0b69103440c0c042c030004103210094203405040c43c4c10010388858060325800d00502c100c2e00061016440b240444005c40c900c0000080c1a10003911090171642100c1401030070150200b202070031840090000e80550840c12075408080d074035150700503185003080c0c200d06e40601d0510300c036140965100359241c540107030400724018140d60040d05850540c411642c40981c03002004c000c0c00308890f8000c030850b03050341032803070100300c80020f20604124035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 564313633 1250 564312383 564312389
    0x5010905070807030317101505040305010c0504060203030403030b030f120408010c05090a0e0405011811030715020c0906040b030d18080303040209160e1e241605030d02030c030a0f06 80
    0x82803900c0b250a4001000c0086c059101c0d090810040010362074404d0b4203580c000e86170305140040c0003c130b0144280318081c811203101c4081800c00924042c0b9040c1c01079140e00000f0302c0603003072583d207484590310b5072000d201354040c02200c07e044d03424419a103420a03103130307401c03600900500398a030180030030419008504903811800000c03c102c0d5003c1c0b61082c00d500c1c20304001d0003141d09540702c00543c14031188205e45c200316940709884070088400e102d0140f503d0820658801034504850800c041d00c200c3d00420a01000c00c801e9034410780701e5076a000400c01500c140501c2a030903101d406420103065a00205100e403545400500d40c0720703140d944807010f03668002568080e612610751804105411035088600d4031181c0c032400c08038180c020300c100140f0003c1c1c0d00c0320b400c0028004441c030184175240480c0250302e9a000318100d144056050707940884035028800501c1380800709e60800b40c3c280503040090b02d00c0004140c2d1305654a21348078513281030716001950030341d802d6810071120040009160040e1015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 564314883 1250 564313633 564313637
    0x30509010510030b0a02040e0c030402030c09190c02160e010602061032100201020d0b030f0c061c060b04140f0d0605100509090114060a0b030c0d1404050109050708070303 75
    0xb200b820b6072039014482c03401600609410784d08020001c0c0020300b0b684818400c5400e154859140c1c901801814140024401014415551003041208440b10508400401510b13a1800103903a004458241d19006600300c8404c40c000d00c0c454009400c4000060550580e03031a5801e5940f0354950074906054880f09000d1448035a845180800a030050040d84030b00f40c58814040e001440c4004000c941aa0705001c05600103075000130318440034074007602030000030681c141c0040015008581c03203961a00d0b000788001c1d10640f40010700c869140700040f503e0300b07120411603081006959600908195510610655001500003110312215183c041612007031006c025058001c00c00507070b502c1b00014031000b001020709903c04007004c42c00340c6a481105100d89400070000a60110850303280700907400c000c110911807500d41038184205991b0005803a000400c0103649070300e0f0f0a09200341d0300684889140747c00f0171030112082009011054104210b114011010b4a0350551169003a41c1c95904074040600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 564316133 1250 564314883 564314911
    0xc180913260d050601090b070c03290109090f150510060c110909101806060902070206070308062b17091005090d05031606050105030604230a020613060305090105 71
    0xb5807001c80c0d04440d50040c8145804070314940c680c041603040341c01241c0e0940b101203900314180100300464044019004450115100300c1e00d21202c0401241c0c014003070650625103541d1850204050300508800c40c6a01440c41c07080d00303c80750400f000404089460300317205030124500042003400360b01ca52801c0360300041c0c004c81c80d500704014800c91181c05400016540312744824040710300040e00c1a1304402c04540101c1c513904010307040c60ba05980c0c4a400180300248104070040041e501c4004540103150b150034808010341e42d0000061803010b00246000b481801020720404200202c64040010b030b2154087d85210a4130b401a070050b4083c0e01001500442c401428a01e6030340103601070f08244030001c0400d04042810b0b40c401d81150450396540c0c403039040103203102d4204070741402400d003d81015002007016142c207444501d41d000050b258030010900d9400112502130701406203e0340b1640203401c6603600c0c070480c50920400001481000002480d10780402c0c849030b0306015250107044101e400407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 564317383 1250 564316133 564316147
    0x20a0e01031e050c04080c0a061e1103040f03050d090e010506070204150b030601020d050c150a090209070513091e05070512010612060e0402090c18091326 68
    0x5001001c85626503507681c460782c6800304a000650180a21a0341005401c0380c40303500c0c04100a213000041c040c11486002e511b1014091140e002944504e180c031070700780d21800c04100182c16913410703c0d08081c04806010014011403030800b00c0c0740c090b00702c900c54001c50310030030b4603604101c070036442d14040c0764140c017642e400401003807a00d04080c0c000d0b00c0c001440001c13183e500001d18117484000d580702e900e0210b004800c10041d581c0502948590180c142046480d11844000068464141f90300040c070142000c404520304491561140780030b150301500110f114102104050000d4000c203000c40d0000062a40200740100980601031180400c0722100081c1c009030440c10014090050507401001814460318034160005400380f4002c1056031503c10403491078940b0002541d210390440c05460020344240030042e100d41c0101d03540945a0011982c0313890707103220201401c46403041c81c560b025036460240504c001c441c101c2c0d1214244250103198420040d042d040344850401e00c500a400c890a000d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 564318633 1250 564317383 564317387
    0x1d0906010e060c01052e0b0d020a0e060703090f17070e1f0e0406050a0536030a03060e09060103030f05031005090406090b070e030714040207020406180f020a0e01 71
    0x34800d00500034a410f0504001c210010708580040f42c00030000c000c00c4d004041c00642c1007041e40000c00950b00c00000311414180302107070320310452955214465000a4134800b01c0e11810790501800e000800803503a502030f5080081c0f00783d0060040301c1980b04c00e07400000f40918040341c01c07003415100c24081d1085e1071500c003030010908002030513004402100c4a03401c18001112032100007034410381c11001c40c1810310b414041c0881d44c000700042c10040c80d01c010b00c0f6039150014808106461055038031b021450440d01a102d140004035804941d9100100e171600515070160001c1041c1c41011440c0062a6183c80029648620a00c40540454030030f10707000440c01e10800046921040a030000402c060361440030441050b400c48007582c3c1c0a0303541d210b400c02c21032200c10300d83e0001750514044011641040019844039040e105048280003100701c40340241c1c41b5038040c1c0e088960000c004004496136245030040c0308a20380902c0003014584800603210f045c8500c295100d45500e82d903160304a101b07075001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 564319883 1250 564318633 564318647
    0x12d2d0807050411091c0b060607170c0f0601080c040e1501050d050c0303041d1302060327060403021612150908071403130e0613050c041211011d090601 67
    0x8003854420200020021900c600c1b050f004010340044040088034410300f0944e034202400303806580310380030812a010104141e02d0760b880070a041015502e41d1400007122051500b890b049001c180c41c01020000600c4942c00709510112400c02d840600c0418030f0601c100c2c0c1c403050611440030840d90400010701060a0800802a050344944121602100000300188c9036420a5229402c800c01910010141990316050950040000340c02049051139560000306a800020503803401e007440d04008600b8406c10141e84500341c4070070001ea6500703041c03c3c24000d46441800ca41850125040e140002d8401e610040000c00705170011454880c014180040c0030180a0101095544035420310541c004560303c00d10b0400180e5070070000b5035444008192510740c0d41016030021a8055140d020007416848240701d25107110888900080c0f10303641c11a0f0581740c3d00580d04019824146102082c041042d01900c0441c0c44000b40c03290341c0a11001d0111504044a50720055004000f0720049407880d402209 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 564321133 1250 564319883 564319901
    0x5190311040b07050610090b01080105040c03090f23070f03020609010c0209101e030f081e0705031c272409021005030c03012d2d08070504 61
    0x1503128502581e900844035280c02c80441510250802402d1002c3c03d580c42c0c000100408501005012207407211001800641051003603900894444806140340c0c0e02c03a601007040680d000d0740e025094001c0d0300709145900c2d00c1610303100b202070361000c0c1180b503108001000c80440d5001c02c21082031605550a000c003e41003152502c0c1409240300b81000103a45128000c1d1181e50120301400c401c80c6045103501c03e0740610300c1070075510421030200748041180c0a185107840b035040900c040d954096105041d0b41c00c0b4280040003041d0001180043c1000404030042c544042c180c1045464640d0300d40402041390400740e0b9480f0300a9005440140045229085007070942c00741110707815807501c128501119500310406103081680da20490805c510f40011021407083c1503251003410761801d04040c00c040e10041c0911a0010b01000300c0e2030300c1010801c2c180351948903542c24078190954890f80e0f503126000b400c1c074000003100590101c448140c40c900b000390450300700800400c20546003900b4007004004001e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 564322383 1250 564321133 564321161
    0x31207051501090b0301060b2d090603010308210705040302040e010e0304080c180112140102160803090c091b1b030c0627030703051605060a061401051903 68
    0x10000c8000581c07240c4041d00038074a1180100c0c104801030b081500715450b0b07410012910500b031050000b6071881c1040500c06002810000c41c40300c881e01d00c0c40000380964400305038400d000100100410074807401400303204810781c06600454044070344108070404102c0702d0000060060004001602d0540c001d41079900c82203000040c0c610581c428203041d0351040c2c01880f6564490070b00955241000d41800240a08003401020326504010b500d003400341100801508044854044030b4010000f94100c41c00e04034280c4024900d00b0f1140b800c200c0d0b940040707500b843e00f4081c6e0a0b10540604000000501c610341608a44881c18a101c2180380c07550422490341c0c1d0315800c038034003611044200300004d0039600c1e41d507030043c022131420780c52020002408080c008103c426500c03006460b18000030607110030039814201203403211401d100d54441c5002d0140b0280c0244510f0b400d1000036000340d400710050f225203d01007003015000c100103550341d02c1a2141d026403015010200700c0050310983c40802e0808c111 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 564323633 1250 564322383 564322393
    0x114010908120d18061406030d080f131a07090e0106030b0d080c0a05070f030c05310902180a0b060703090e041a040b09010b040e030a140408122703120705 68
    0x29440c4d18081b50743c4810416500341040e400d100b09885c0402031400140614a40a050342ca0041d40c25007460700043d00f000d001e0749030402c55808200140341c004114242c2960780300403900e82a50010034011030b51207201400c4581c10000f10f14540700340104c60881b18042c00b031010561b031554070380016a001c906c914005d0301501d10004002181401034600802e1107062030b421650443c1082c240c500c880d540910b2040c141005586903071002c024104401ea41741c140c0c40b5100f600980c460901400e580c42c0001e50000499480000c0d5480d5405894001e9400c003c0402c001c0208409000480c03040e024054046007400e00100040c0281d0b0220341d034458810031a06010b24107582900032400000d8400b2543c02a400c410050400001d1140340701341c0c182128144a440e00c03209000d6224407960755100c0800c80d0b03203101030145000c414111801014110112213104e00c440380340114580020380480705505180c040c420900d100c1145845505400401500400044d11152000780d07014841c00c44180c014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 564324883 1250 564323633 564323681
    0xb0a1d03030c0a03080f0a090201021510090504060e0d02030418020f0c01020a08151903080d1d0708010f021206010f180603060503100e07140310050114010908120d 72
    0x140030f0f1800f22440ba4803035020760b040c042604288041e00401c0580342030720780082140940c3c1e00080f0b450180b18a0140031159880d958103418020070980c04c80c0713200324180b1043c0010400c80754040d004400b0101c066608126100c48120b86030321451281c4110100ca4411200e05244290b000b02280745102007207a01c1d000300f001f50707d42641c114000a50104074900200306002a485690182850301242c21181c101395841941e00c03c003610703001c040c02c0c12074080388110290042c0d0740500e07529181b44080c2503464030300c881d01c59510582400f54051070b5003004042600d28170a8000d60f8581407104d1101086543c0d55001150560440b03840c610400080384041d180c08105100b000d0b01400d240c1e0b902050440c00c22082c5468903886000c40424589480c1c00b001c0c0242021554005548601c24104c0d00600202c0002c2c2ca05004401d1a584c01460003000240080c212a000780520a081c0c85007d040e60340c80100c15103600404114034510345041003104050345003540241a0691042040b44003403007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 564326133 1250 564324883 564324907
    0x3010f200a030e0123151509010c050a06061409100501030209060706051311060703200f1204050301060609080d05030430030b06041d0c07050f0a0303060b0a1d0303 72
    0x3405e0360096885080c14450180300807442c2d4605035004000b10450014082d00c600891030604170340080700648000414810f0b1b050388200384880036290040215102e0340090305081c03004082030711900306817010700b10b141c0b401400c1c1000d0051188114410f8051900e20707150040d4013950003030040310340c0400c0170403401002582c2485034034000e00314801001000791892030070020300030740c6038083d0307100709800e0000c140002c4e48043d08104249201560510840c00c90200f03900e0702c1040c480380304c054040e4140005158044201610440704110000e000140d81d620040da0050020300840940c2e030410007c071510203000d0f000841e00548124441c645490700805882a84140868591140d529008a00501c1545409500720110301265001c1c9050b14081004940c4010411a909104445000603010340386200940c4d6443e90803a055804451004014a807192210442140400c0c90120041000800c0c203050303030001e10060325940b02541c8070304142080384194640d241c2d4580300410201079526 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 564327383 1250 564326133 564326141
    0x1903110a030c2c0d021c0f020f010807080106030e10090503071209120f060b0d121b11060c0c060a0f11010e030a14072003010f200a030e01 61
    0x12035554005000300007241c00a2504006214081220608070040d00e0a005070192580701c000f000c0710290015015032000c42c0c5a1101d100c1c406155601c1e050b0341c1c2040c0002072801000c030300d108841d0820000c02000064400000c01d90f200c1000070b4122006007c8a8081e034005e2000c1c0304100304807030302e1070142190700007580d28110007207485400110740b1070200900202080040c012a042041045040c0f130b80c11a0449803194010340280720310384a00f0203000041d4014640804090040400040503003440c0c030b0002000c120300d10029041c0c100a06034003018003079a151003a40b00002c0048000e01c403080007916000210882114020480140d90750741d506801441c1b40f140c0c0e5154549070700c015a0000d00003090700560307031b07a040e4101a03031101d900710040200e40c0c03528050300300800821160440c2c07404501030840000c041c2e03c1b9918246500e4441e40c02c00204102c0210000e02080440d000701a0640b072540e0748406608001e02c04944003c02e10101a100c0e0445600d0005051040c1a03002400d40b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 564328633 1250 564327383 564327397
    0x50114091f0b2a1b1908010b0310050613090203030d050108010614010512040204110409050906180d09170f030f0d060f030b0a1d01330506190311 64
    0x102d2800180b00300701c03d40a414000c1042c0340c0d4920100f0010800c114070b41c840804140c45000381101200074041d643d42d2000d1514808091070107a404143c548002d03900a00d80304401c00d100c0d00c02c1254440703680d802405600d10501002d081c3c00d00a41810341080003500502c44202d9150105004200036542507201c0c045c0200507240008c10000e15102d4030760740b203081c0e200c0d840d4100001000442c081c40c0e03d03c480c05030420b6054500040007410440c14a0b154012604803078036850400e4148030400d10000344490241c1c5040c1c003103244c20000c0c0e40c00c0907520007049808030b02142103000304010300b0b0301d04407500260325a540283e8010302084000ca60075640045030541042c440411a0110f0340030310b1040c04d018096041c601c4e2185800c6071564000c01070010f180c22043c0341c807a11030b084102e0700889054645081c140091040340c03e00c1c40c41164140841d0036813404c7d401281407044d103000f5032911407000c50b80043c0100b8500035650034040060b0040b4003203a014180c4071001c851484008030018409 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 564329883 1250 564328633 564328649
    0x9070309060507090305120a030204080a060e0105150907030507050c030409061d07091502190b07140415050c07081608060c0301050a090c022a0301050109050114091f 73
    0x40350503103051011039002410040c104a0444c20600c001100060350010043c0700d401415105c41c00800c0480280c802c541040c0b0060040104013404c2182541181c00750010300c00091041c0d42d00c13940c9041c01c0c5000e12380d04c02c0c2d001403450081403580d03000e43d200e56000300d07803231808078a084044143c091555015034402c05005a441008014514010400e840c02032404285aa03079810700240c0108000e42d2402032054991201ea23030a0b070301ea070080066034442c0010504100107101ca50920b0024a1812200e600c0400c802011746200b501d585803c59042e18409541400461a01c0707004a80e0358104040b480384511a8a0020801c450100b003400702894200240b00740d02da003410070040c1000d0010741031241c03e000c140018049a0380d80b018500136220703000000200341810306012031510741c803600810307609040200c03c100070607050000220301205c2a4001d011a0742e9074150b150448c0e200b486840c3d030140340c1e10304944292070700003282030300704803142d4404490901007941c40b0003404041e031150007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 564331133 1250 564329883 564329891
    0xd0218090c04081009050a12020a020916080a0b0112020a090503150105011808071203200f0d020601030b040b1306140f0a150323060112050106051903060b0609090703 73
    0x1003c00c030100603c101c0c0d00188041800101840c0d80c8165a440e00100c000f8901d140b80252035070342c00c0c402c2080070342c5076400625600a509140550850408051300704000050f149000540e020019002d008550740301070395062203d0712100c045000075044608a0302c00c11502c40400641c1d40d4081003010707000c1c100b404484649514090016101000c6c2031242000f501c02c5000030000c454003c22803c04480c990122126814003601c0c08480b204060007101e090302200307002640d21034900041407038419211204943c03401c180300000785c1c1d0781d50091000400c100c4d5550005000680850211a084510312010382c1e01e400701540c500c0107592840c40c1d000e00241081c400c015501c4003501e203207600003018a0b01000301540103a440c424200c142d00004c3d05540b003114903a41c031904402c400b2a004000401a41d0040d616042d1141d80c810302035400341c450b90309061002c20240b0b0705280d00d48a82c002075460b42402807441c0e440780043c00c1581c0310030b94016001d00880f20943ca0798540f8520403080760364002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 564332383 1250 564331133 564331139
    0xf11070314070e040b01140f030a030309140f06130c030b01030f0b0f01080a0201080c2203050d02011e0b04020d1a030706021902040b1c080301140f060d0218090c04 72
    0x10314003412988962801201c10f0144004102c8010565041d1203490811820520010012548808403400c0464040c81031010f0340f424181e0543c42105450311822445061503016000b103903558490031458402900203002050010203110f0008032854819500c0c0d0698503900d0300c5052006409910030f49121801c51114000c00109105141d4421103400880a00e54104a100d668038000440000d05004072400420146615282501c441c152030808103002900e25919003490101c0d2440119800d01c0b0b055030707030501240103018a00e409450318103c0c0f82800384600b0054042d10343c030070380c058100b6800c10020844810707a0141021840b090300d1b45400301e000328400d00d0702d03007403a0380d100308115003044154005000350040c011064640490700450344181d2240001c0d80d031704680e0004242040041852020081c40d0301c0914126104181e980301810581400d210900001c1201c15030f103e0010444401742c00066405000d0032081080148010800100490510030b4113888000012030045020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 564333633 1250 564332383 564332423
    0xe09030a090602030403030f0f030b03010e0a0302010e06090a0f06060e280506010206010603090204020f0406020d02071a0405150c07180f02090f060c030c030307050d18120f110703 79
    0x81c00082640e48015807a151454500828103003d98a84400b040042c103254a1514030a0700524560200100200420700300c0700e040a03074030b4114201c12000355080165140c404100800c0442c03140c08148003404060f44039036a03005210100c80c100b15022a51500045010140e0141840c85128000101c04803541811110000894014090300289043c00c042011a036804240c1e68111040b0f410046680000b03031001a0290055440800e019000810001074140d800501e028400465400340d030003c035103a5060340100c1c0503c0201038075104c4100802c00187c100842230900040d0f403d0301841c2004440c01c0f1031800d0031402d60086820504035011002d5595081c40384200c42504110218a800300f0440460003420800405034840c440114403910305a609000311621640701c0c00c2a260b517840c0c83c02000e40309801142611641c5481e04e088400c56090181c6007a01071034006480302c0d0100040d880441c1c0c4038071108440c030100040702d884048078a200308507080245103c0c111164400741d03a0821 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 564334883 1250 564333633 564333647
    0x4080a0b0f0403020d03021b060405060f0c041a180405151e01020c040f090206030103080706140c16060b0a060504081c1d01050421030e0603090c010c020a0e09030a 72
    0x160380d4900c070001e000c0c40300103030700016905030f200c2040c14096100d1904841e0b640c090003502d240d500742801050100410080081000b9200d43d42800c030410b51610740c04c0c0d00009a00440c05024010f03403007003104620640c4002c0c050001020030711144920745501c080800d05889041c0c80a6a40800d240b80d201c0d1a49000318400300d111079400c20315525003040b00c00007580c400603c40c0450003182c1e9008220035200a680040c50925009014690389503520702c1c280711079a2088400361491b51820580720031041c802c0e15a10b001d0b0800018860509002005021062001d023104847c840d60b9134400c10181c1c0c40b01c001e600010981a1642da807590320f04100796003032001000c0c0e44c4c17a104680341d4035854100c0e00800c1c03460f141070704010342c0d0352411386600060700d0a100d42e070018140301020f40c205174411300110940410351882541c03402c812141c08000d005403800151552421a0007003a41c030302c0d45501c40ca0034550005d00046c03008407019926a5845202d12055a0508507604000341000c0080e8128117 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 564336133 1250 564334883 564334891
    0x200a0807032a05030a0212070807091d010b090f1c110a150804080408011a2d060d020409050405010506030d090605070311010213090b010e04050c070609080c010204080a0b 75
    0x1100e0681d00c00e504116082c5007102982c0c041c008003001140d03000070554150b4811030b65800c00c85070f8a00703200d00080c20240c411100c82c0005a004a80402c12201001c1940e1101752548604140e503401c1c01a8440346030014840d498000044c01042c1d0700d550f0b80d4109401e0b172072000e00a080a0381282c0d04100d42e494003d503210f18058032102c02c0c10403408c4d03c40c41a04213900503600e4041d04c10f03160b0b441d1002d0103102d940c0c0b0400b01582000803001c1c109001401c0c21740903003021251040c6062841c0809a07001e10207415288201c21202601111801c003500203101036141504010f1510351140440c104072501510245c490742e54a0081100a04080100720344081e05814101c2d0028580301000b000c51255230f60040c01c116540950211a2070250151080c0748c0c2c00200c901612626014100010030042c003001c2d0018102c0f2041c21081e0a01c4e215050160a880a00c54038140f203c3c1c07108800303404403480864400c43c0c00c21102c1403d0300c0a01c0640050070224014001254150402c104a080064 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 564337383 1250 564336133 564336161
    0x7030e0105010f122a1d060108011401050c12030105090705040b07060c03110a030c0e0103020424090302060304110a0902091f140a03150b090a0306200a080703 70
    0x240050200054480a0030100d42074410700e00200c0c511482d00d40880c080250400e0140d030001004100c00000d402269000d50310040c05034006d101203114181c180310000c0d078809001c690020010721130300f10003200b210003002c1c042c1000c601d0044034a9015151035945251403158038030100041c04145042262550000042e1408500385418109441d0f0244900340006241a40e03502c40c0441860003030b08641d000f0340301428055101c04044c00060054040d100b450000191482a000d01940c000e03c25201039a51442c07010808200d0b800f41081c03100351111041081c02040d42c2c000005983d100700440c0f00ba442a034610200809103024007403072140540100b03000c01e006106580b00c6446604a460818408000895520226440540302000107855540400c0e900281d500c101540541018007220301c40d4031801065980d43c0d01d6100b0600078110310f1036101c4000102000480c0c0240c0003c0341b6a8180b00745100608085034403040369074400d400704004034906508002840d81c1500c10329641d040c0351 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 564338633 1250 564337383 564337391
    0x102060108031204020a0f08150a0507350903190c080306100c0b0705280507260a030915090803010501030e0c0603011d1b09040e01090507030b07030e01 67
    0x440301c150b849001c0e4956911044901c040007800303554030002c541005020b410a44059141c0b100ca03440d803221000c2c403a200090900c0c40c0810b140c500c46216491080034244d48103195520016100794101190b845c00c4508040316001f40c011140801d10001d000b40d200c3d1008558889481c2c00507019421a207043c0c50a00c0380100202001c90075041c02c80b68000c07000c48030003064494004042d94101e00701500513240c66512810040c1c01c64105004040040404095241c02d8580c0040e12901c01040340c048400a601404400300052188026200d00d042d0340c5109448214004a4044540c0041c011040000d03140c1c44e541052082004c1b1012040174400024440388150b52602840c2f0b120601c150350400d5910700211161003024030090395010300040103a5542e582d01d0303d1a8400b011511035040030341207010003103280101900300f030001d242c3c08030450f542002504000c000007082d11024051955484850910004000740321907006944140c080c0c02c090b06280750300800f00c1301c0402c0c000307030f013a854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 564339883 1250 564338633 564338639
    0x1002031b090103021e0301140d02100302090117040501090b010504092f040212040b0c0307020c011b0b2a09061608120a09151a010f0311161101020601 66
    0x580046848a0040d940500d641c6412040040700248182400c0008908000c07421046099010004604a0380c0d000304180500c002d40040200503025074400940c041d00d01e8400b0300d541402500076068200050420000491800050802e45c610441e4202c2d8140d550721101e07002c02036031603e1580540303000c2e5070410078640345035541c5001c0c6021490020070b18003068200d99090894610f010512800a0f0095403610142140b0b40300c045002c0d13134100c407014089000070b14141d0003207003070700c1c8501800e0303006081002d0100d0040d40d1900f80c002118070210164140039021541c0c2806c02c5003e45032203a860010b040c51303c0c440034001c0c1c2d500110301030300c1c0004104580f46540d40f04180d691034608440c102c600b81215161111492007040d0b01c140428541c1e10800c002d1014943c0701c050428040c0410945241000340c0002c06c9444402e80000c031107140001c10740042d4460844059454000d060020700001c0354902448203130801e8040317004003441180d468007040f180711013601810a00b07000400076541 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 564341133 1250 564339883 564339901
    0x3010927122a02042705070510020c0a140f060c0d030c0206190b0303041a0c0d0320160b0112290c070309180522020f04150f0f08100203 60
    0x100b00403000e885141c8400c00c0b00d4071020700d1066582646002da404841205c0701e450081d07294005441080c0c419840c2d95200d00380c0302d00201d07885c0408200103007240762aa044c840c2c2d0202881140075050b03044104251103d0407600d90720300400b090481c4200600130080c80d44801020345510700540411034005c0c40c184021b62280fa998115070b5008520080703800030489000c20b00d14010340c1e000b00c9a04a05031029445040d0940007004541d00780002d07600070744411181035040d50043c0c00c501d20308560381c03409582610403d002410a2400640e84154140201e40322501440c4080e0416800964000b82880c02c01500000241c98440c40440151040c121a00c0c1549025070040c240040d1400005a0700e04051041c01d40c0c00180ca00c03200300449980404128000610048456404540b003c174521000b00c000540018070036540242611003240c1203e050201800e0f80301a141c070801e044401c041090590510b5810103030940d080c2207094545044421031801c2040c64078892098810000c3c084840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 564342383 1250 564341133 564341207
    0x601020109080d0c140d051806090304171009150614061812150711012901090302060412031412040b1003050102030711070801020a050301092712 64
    0xe043c500c00280c82800030000f503483e040340381070300110100300040c011110350a80d40054020110040c81c503103110020034606990749020f0b107550f591507005200802102040c01c90a000426130141590b81c5448040c0b140804d40304903031400c840514a886500b00017200d58407500c0d00074190412035000030081c01010405500c2050624801440d102c5000041600c40550301c04400c00b481c021507040320001400c542c0c0701041900c1c0c0c030700000d80560302981d00c0101402503210203a078401041c18030701507401101c0e800e08103a003102418404240c0c00000541e6039038005c0c0006058040f0503c030710303e0803894010140c0d89410002c82c00030f003040c0914020004d000c00e003168400c0c1d204010514986420407011800303c9680d05c02031166000000308a2516880b04000345650100d038121383e81c050310751405038240d000b84001c500002d20305000411141020b904008404075509000d400b01450fa041500082d2000401c15650f650107250081400f90f4003942545c3c101e800403142058011500300c00d60521 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 564343633 1250 564342383 564342397
    0x20d080c0f09130219080103080a180f0e0907050904230102161b081c1202160f15060e04030f020c19080f0309030303060114040306020a0c0b060102010908 68
    0x54202041c0750100c0e008900803a441000010b040c000410750000c8a100a0b50101c1442c41800306003160100106006540d80c038180c961001226081200c01d842c200c407045642c0f0840014071031410300005a44056170300c054064005034920000390b281a8003403a150405039031100d4003a5129030f0402004c40d076101c14003003400035500801411903541030300c41030281c050b00c41c6c0003103010074407950507041213004050b00007914060450441555650300f0407a44800300c075690f4406401c201c40d54030401610480540c240c2e045811001418010f200c1d1101140c003e40d1442102c1d40c0800c24005030034000c001800500c03990881d0b2041c030500703003850f90440c1e003043c02034001030501070003609095400c3d00030b200346803658002500c0c44000c44100c102070501107003e44100d04041c0a00041084884008005c4414007d0003078000c51954031540c00465480a40c00081c102000b001d100100c006400340c00203013090801a07813070180041300c500303100d07110300c43c0034201605585c50000d100d0001a1510305440c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 564344883 1250 564343633 564343651
    0x40b030a111206010206070201050f070f0c06150501110316060209010e042c0303091e031b01051008012003130204050c0a090e2203050c0307120e01020d08 68
    0x1240c0340c1a0200000d890030035401c1da500e180c08074240300b00308444201c2a10900c0c09900315a12a00c0f11541a801c80e081550321007400d0a02e1000600c00902a410908041040b031030b10720740517080c9450710000c41d80030540d1010551494002044190781c89094482c41c0309a141c0650300c0c2c00c104596140131608102c40080c4442d4000c81c00e20340f503a000301f408400003103014005000c080204510204071214040422800040c0c00d40c1e00702040e6800801c3d03c1c4505004801811061821410580c00c1e0341c9540c01803280c0c2c0310400000d02e95860361980c440309984101d001162900b00300200c502440340581042030350740c4c54800c0d4040803803021540b07031300c021301000c0c04660349841e60942c0c5040719a850002940041c242400d2251080d0f50b60001e080e15507a50791108422a22825842c101c61800c2e1200801c4225680e41020074903403c1000c8890144a41031480c60482040441d5085400c640400d131010424005001001ca400c140c0149165000748060f0201414035032001d850f20201074800d41e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 564346133 1250 564344883 564344887
    0x1203090d120f02070c05130603050c060313150509061e07081b270a060f052115150a1d040b031e0706031e0b01140c101a06040b 56
    0x4119803260b2107818907040115042d03658000600703145501400c14410240103403510010280b0244440c455001035a0340721b0054081000003004001a9420190041221001c404060030002e4002060301c58030a030100e40110741841c1a01c1c2080c00c3c042c0007000c0c401c0401d0300251469148010340c6400e6440910341c2054a49519402c2000302c088802c4040b10003c44000100b50442d4103200c0c11080800c11580c1d11010003041ca0300c04e01c100d0510503c5498003041241c080b48a515001d01c0103081c00c98910342c050103900401c074140c10250324040e034a5207124540c080143e10b035410440c99034131880f009100400c1c90800241c8001b8031040c1c0312621160288420800203610f80d41d945c1126011aa00400b203802051880300b40c6100e00c01015000980340c80344c10303400a14a4000c1c001c03040d941000c02040c1c98540c07040c1c3d4002e4082c20281600324100f080d1429070480c1c0b1031034980078011810201000317000c10f980c103807151812510000d0180c17a106010010b44121560755404071030a8641018802c2e03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 564347383 1250 564346133 564346157
    0x1009030b04140615030c06070305090d080702030307060218010801050a050f220c110c0d0b0406090c060e0f09010302131509020a02010906061d1503030915040303021203090d 76
    0xc006020030484020b0038040c54083c0314018011103e401c0c0c0c00342c0c0c01c40581d05004000c07410010b0a1003803c04c01030120300300b40404082c42ca401301301100c0740d50240d041586420150b500280c1503038031a4104607000d0b40d001c0703500804001031040d03205000c40c003070070020789950501c0c0016061087e0b81c03003040d115032882d4565a03515251070348520480164141003003100080030b00400060710480111400040c1d00e00c1c10300720096800651598a4030700a005c0c0082e45a040d2240000810018000e0300d900c3d44034a56a0005255264600c00904240c3d0b100f0b41c1e80d50b80c0070100080c10406c070305042d2185d0504801400540d550701a40011608200c4001407000f00c4101c524032004480e40c0200c5400744003181810400d5010740010260341d1040308100310242c1c5903621f84080c410b030010100c3d10001c4000015650804007500c803503038040c008081b64203080d101d80004d0038000214440014224020408004046e0100090154122011403050440c603000b510265240c0005281c1c60800010351904 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 564348633 1250 564347383 564347393
    0x12030b0103150b0901140706060311060f120c040815060f0f030c040207060612050a020a0b250c0504111306110d0c0c1d04050706031a06072d050601051009030b04 71
    0x200104d00306d10380321591144428103000009000301e200070388040c0000c1c00310b40301c0e600d080401c440303000c0d2500b25a1030526010405601c00703580c000b40807452140e0301304000725042808108002c24954160032101d010700d01403040c80082d501400707400d802580c5440c8901d02e01d5074080f82c031b52000b081c1a10300507120659420801301402c10307a030001085000c071078200e80a000c2d02240084000b4000e4541c41501580c2e403c1580f01ea21425941407500d0640c904003000341100c0c402c420907068007500c3c10031a4661204001021503524070700681c0c09040006400040340c1140c0312002c010980703801e10383c189a040744d881a48400c80c3c03e0000041140d6a0045000c121001141c0405070101d17000504421a100c640ca207131000c002d444c01d07a0b0078847d481001070428468025240a8a1004a001305460702d035810300108e90000b420480e0380410b130105000400081c002d038074440320b200801c0400f0603245030a00604102040e0072842c0121040101c14004640200044003240e43c820b454a842d980c80b8241 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 564349883 1250 564348633 564348647
    0xc050c03090f061614150f011e0e0109020a030b0d0201050a052203030302030601270603090309172a0d080c0f1506040c020606150a0c08040312030b0103150b0901 71
    0x2825400e503095428200620403105d8400c500c03c04e240c0300304c5600d2003200e102c00b90b02400407101c80070815074030070050041c220707880c100603058520803203020044c0d80c44010107640c02c1c2c4260801c6544960218143c4034640d4940604402898251442c1040b030500ba00001c2007403080b50b0741c14003440300008072131076a0882c004410070708240810341e2000d0b8944034a0010041d43c02940c255001994081e84410070381402c600210301107114007034000015142c04001d5000e085001019002d00c542c3c3e880000c3d50405d0500c80006204040c4043c0519141d400400500002d0005515091400c0c4a5002410f500c3c2d00b6071142e07115401041c115110060342265900d031280000030042c183c0210003030f0040700c1210030b40300c902441e4201d50620058082080c01c917640e0408a17800c0b03a01c460300058a002c10700d03003880104076444251406001044050f200d01e03460368455031048500607d4505c00c101420384c94403c002d1004400d20301841140303402c03035204410091030700504101c0600000c1a41090b8003802c5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 564351133 1250 564349883 564349897
    0x301060309081b0c0405160903031d0d05301c09051f1d030d02030411030d0903060c0809100f02090d060504020405010e070c0b04110a08010509010c050c03090f06 71
    0x60700108008055185541312071101c4051801079041a0124503c0300c07585402400d1320142e82d0301c04031080d203541c5040b5903064960846640140d0404201c81040e00c410b041c0701481c5011314000e0441d4036003101c1500280400140a40148404031401d1442c40d03010b20845400c00d01e1b0035a0300d10346064520039000182862080181140701d0f0b480441c11890021001d1403250403225000c0000c2644090450b0b00a0341540080f4810382040160942041c0640d025680090261014400d4040307450f010910b00400c0b051014041681c081040007005082e010302d01b0342181502d0b1440396411700c0c4c03001c1996000032070340d94001c590300c0302c4810288c1d40761030303040e201c00c40001008040041d100741022401000c003550240e00031428a80082503801d5128081401000d03c0e0b641d0341c6099009455024961034041c2084405c40c1e15004954110303507600703c203400580408000004c3d18100b054140d421601c8107500f81c2d091040511100d544440084155070b00840b0581d04591307944810030005d034241c0300b000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 564352383 1250 564351133 564351157
    0x190203100c031e0506150f0d0207051c0e06040501030f0b04150801060905070822171206010f0503160c1502120c090609040c1704050616080408030106030908 69
    0x1c50030510503a0706402c08103003640f26442c90031412690030034a1055807800c03510309412114010200c0c401400d00d900910704071041c2c07285642000a0381c1d2000c0c0603a8804807056038254800a070712401400440d03440649100f0a0030b105401e04031510104849001d184501d50506541d4040e20080228542004440300802030040044014101084840c120036004903c0d00b0340c40c000012402d07030a603204503409201d25444d51001e540e5900c2d24401114240a0070070f1180b165803d07030b90001804050646040824044455218160890520702006006010904012a01c414a50156009821a500062000d000e02d66070001d01c4410303521004005401450701581c13803504084c08030300b03901a214540b00110081e44c19103a41030954968011402217562002c8108404446031078180c1c440c00b804511740c140312000c4041d00104400d003120450701a182900f00344100040c0f940c00840d810414421401c21040c241415216038150b4001405506c0525a4620f1850148900341041c4c8403c00056 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 564353633 1250 564352383 564352391
    0x3020d0c050301060906050c0709020a02101401172a0307030b04060c0f091a030703091b050109380f0714070605040302090a09030318140f0f19020310 66
    0x6400050450b03009214010015000a4001c2100c0b1711171400c4660b10502080104149410b11f120040258050540001944541140039011600310f00811603111860441d1600d02c1d8580350440780320f80d028011840c07403034002100e41d090034441075112016146121842558100f1050702181c5010560b41000e01004035510402003081800d400c040d1001880d5542c80c0540788c031100041d075800405000f8540f4080c040707a10380c08a00c0e00310780519030029071482c000c24908040d4031090945080c2c07904190b821a143c40b018452540c02c40300b040e00805003215840c401d070010510483c15000405000c1c41c0078100d845c0c5210b0785404401c26114410b0160100310355854075031500d00800d07441c103e610441800b0ba210005216809917080e00c003100c0d0080c20b1810701e541d465200d24000e081c840c4c02141071507654242c1c12242c0c10440c1111810070701c14284680c801c0308030121a481d2071185611081668482000c500c4901300102d22161903140b55079000c07015010601c0002d08101040072902001864 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 564354883 1250 564353633 564353651
    0x906070b0c0d0f0f0b09010f030f0501060b040603020c011a060706050408040e1003030806090402090a0b15040b0a0210180210050f0a0e0f01112a040f0603141504020d0303020d 77
    0x80781d41300740c003401c81c801401c1060207141014400001024804c501030440301800c1000401d0100c1c00e030456003171084000195850301c2da814199a0f4003d5000240041d6000c5000401510b0921401a42811801800c510355030360030002015481fa14800500d6142c45002080400074210140c0d0f0190501224041062900c854100d8051009100030703400a05400c0104189082507801030b4019500681000900d0340ca150741e402c080c00320142801d4003c000300300c0c000040c2c03c4500c0900094501c004080381c0e6003541140007458090301501d0303282031600d45614030100b40e809808070b80d02c040e07059030300d04005d501c000b60943d8513020f080c22000825800294043e04581d10a940c0400d249085500e21520b4000c0c070011114500741c41e084802d158031a00c07800e444030b008004154005804216007503003113516600800c0c1501c80c04080c03082c400e13807a0381d004e00412030202c40b20503000741c0c2c040c000d262086e420141d1214500c00500064080c280030400141458860f40490b580340905d10414071007100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 564356133 1250 564354883 564354911
    0x3150b03010e090709020906090f0f030a03020d030e161a040e0a020912010e0601051e030f0c1c03080a0914030c1506010905030a1b08060c18060906070b0c0d 69
    0xb0125080380e15030103600340c04511414240f007600c5002d10058800d0742806940030602107090b4200080503400340044820b44140d5904112400c0f54911130342c05007651b01c256103030140980d60040310100303560704010340045c0040340710804082183c41801c041d694070300b9400c558040754800d07038001c031150303507010350030401e482590390000d045035a01a617207141105000403c20b4200c1c0d4071b132603040c0000e40141c40100031624014800b2400004180010400c0c03501d1200040d2410350804204040754200d81400301c01d500c3d04a4140b100b080c42d0305180062149150380c000c0c0280c40090484905903507488119080c040f04948070707071361400d00c441100d0391380d85214401c581e18400ba6090440980e00350000442c82c0d44510012000c5907006070042405402981d58107585030124940c85950301510307400011584010015180164480305180e41d460400110440a11410440c1e0a0080c0d80401051080d500d035201241c5641c0e81185400c00d80e51108504150745104070084001c0e5076040c040e0540f8000c1d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 564357383 1250 564356133 564356159
    0x10020109030207210210020f01020c010e0d08091e160b0306040b1e040f020904022805040f0608060312040b040519080a03050f0915040e1e010603150b0301 68
    0x6001e9002c551809aa407450041020340c80b003003288540300b81840540060411010300284407403540143e90703010b18044031300390890b082001c03c50207a039161031452414800038001000f10801c40d00c1e0110b05868042002e6039222240d4249a00d11036006000030024402030010750b111040ca88806d000482c0d45e9020120190010f03180503100d40c0c80c3c10000c9c400343c6410402d4800d074100200c43c030241c540c520410840180718107240841c0060b02001042c1d00d90b40d452008148016620001d900d0018070601d000015160480120f418054100001e21004200403038070002c60740d041c47c0c0f00030141c0d200004039040ca2400c00001088070b90108002c81c1621118024000b994000d81d4040380514554501c3c00c0f008201b44921145178103c11062070200b80301c0d90042c40b40c0800e80103c285045404400708206440c00071355800081c1000c5030511440700c4112503180c1194017200021940b140e110040d001d03000061051106060740c1b54008940c082c10b840950380103146d500c090076260340c2d413460134602007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 564358633 1250 564357383 564357401
    0x1e0504050d02010b0307150309141f05060d11031c02030a02160b070f02011103030709090507050337021602040e1b040b060d0c0210060f03030c0b15100201 68
    0x940100c1c01e00c1000c00344144288400c0b80002401004d400f07141812400d6034055146000781003584039440e840100340d0042282d201e40a0f6030b40140039280c4003245010403050855052a0300c54100300501c402561040d092100712600f00502c40061142c14000030720b4421281c07400711800101c40c45000800d078010000c0d10b601d843c2a001e440210031024000403040c3c80038001c102d81c4410a000c401c010880f0301071000c1d075291060400385441090b818840d45950021500940060400304051107210302c41e01850b500b285680c00e01c6400c50522684240007401480301c004200c03840c2c4c901d403c00c8900019a0300500f415520300c119a5640e5143c007800507000c41c40416030140d0704118903980f8070703840090458959040108011400102c181c200030280564500d00c2d64404402c2c402d11000040600c10a102e05142e0340062a600c000b0051a406443c2c03244d00251000c1d0f0030310020008650081d81402c0c515501840c00c0010740c0c0e4211108560303c40c2581c02e260050208030384455140c1d015841b941c28 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 564359883 1250 564358633 564358643
    0x10120519051305150702010921020706032a030f09030e030f03040f0b280c140f03040e0405011b02101401060f0c0f051f050f091e011e0504 61
    0xc95a804512000800b003060006080754048084070301003010051341a504031101b1b2002180e01099900c456000f24200c0f4049059000040004e1640740c0d0100900c00081c00c00381018000404c444080c8841c007030070285126804040c6000c1024218401d61024a04880c0107108001d01c01c030609008007450f0204081e1030082c420034034007001103c400800d030f070b0480b00445800c1d10090b007080e040c20840e81100c0007100183c2e500c0100b20302c07146001e1000f0b10b0300c0c504540c0c4200e80d0b04e002d4180003248040310201c408041e0051903409100b01c074040100c80540b01c1941014001745c580b4540075004140c1e48640780e81040303c130f210349056258081211034182804505c01c5c03051070541d400005080c2000e103e0400032844402c540d04107907018401c200c44507030290a072204019010b803500da0401261040b401d40c08403010034805103101c07981c440d19402c07001e0201c80380032903e040508946c0d21401020380002105088146c160400e609400c004620580000c11510b03d440451002c40501010313241291 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 564361133 1250 564359883 564359891
    0x1030b0618040b06070c2615151503131b09050108100203220819030c022e05040c031208040201110d0c080d060803030c070201020601080d080610120519 67
    0x843e45402c07001e4900701c50f00708543e034031a9480c09418882c081c0003c00c44030194890b401c3c026070141d005003c0388051941c100c604199620341038520300c502c20b036a000b1451140301004080700b01c001000044c1ca90100040c2e00070900030880c0d051002000781024442e50700c4903c0302c100071074070304610b4200c181202c0c0510200c80301c032640d48107041c00307034041140c114009141482c224242c5031030f0459500304040c0180c00e540e142002c49000950311514005001c80813070344036405415003a07030420030442403102d030001040000d140b0080700f50b0040888003044044a489201180910a01484030350003140d120904042e104007074130000d065544210303010780c00300c1c2583d070410b140c0d8400841c4202206005036202c81003c0001e035201c007501d070005001000b4080d512603000ca00c001c0204000c50007242031955090b10f0302c0e10392000920700701058120401982280c145000700c18cc00105c82a04a20308440130000c28502906c125240c0c0e50210032000c01e103046c0801e011400c0001c8810741e50650600b98184 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 564362383 1250 564361133 564361151
    0xf0f060c110d030309080a0f020706090b03011203051b01060e010906031203050a15060c23030406050d140f100b0a17060f0a0b03093901030b061804 65
    0x3440304091808050046000c00303002518600d8008141c1c4800740c030900340003402aa054562a07042e030414403204020511100e04120040c0d010010000100054940300002505020941807240018030a402e04804c46843c40c50802d03010b182034410458910028540c0110f051840901901403442001c1a01031001c0020034010340c00d02664081d42e41146c565408003040440c114024400246050b1010355a100c15038241d1301c1c503600c24402031005030341c8d1038030400d403e040c2110302203061000c41404603030310301001360b0002001c8143c9003260310504003107480350344584114000e44041e00791080c0344d10040003040000a08118598055481000704d08001500c0f0428003d59201d038a45240110b10980380c01f400e41c000c12489250301c800060441494200042c0101e0280c450750742140800d103c0110402881440401c501091070001c400d82800500071540c28960301d20490502c10030400482c0d0004031035134000c3c0c222420285000d00200d945590090381e1141503030419203024420343c2130078161 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 564363633 1250 564362383 564362387
    0x910360201080f0619080c13020901170405010207050724080408030c0d06080a030302190305010b040509042301150b0708040e040f050f1005011d040308060d0c0f0f06 73
    0x10004040e4103855003016911008000c065081e80102800c3d4444041e0b2082e1151900c480803550003490080002c2801503500020000741e00600700c42c0d9103d40c2d1061041040030780c0e00c031481c4001c00d12544001c400d2130721a0300f00180a481413403400743c17003441402c0001458405004121103084a0b15011801041c0d007000c0444458106540140030307010107001140d01d04e07045c100103200040600e440010b004e90b5900d802c82c1440032640007070b00485c2e0b022994501803104420184c802c0d0600d80b800700525810406200014000c5006a502501c40c050000d410091046c0800b81c120b20300d2003042a0b44a03028036440d02a284403100043c1000d1341a5001801e407840d1030558450725482140700d8206418016a0210214001d20990381c440100c2c140b100410380a00041010380248005080844c4e1465210410b981060f480b500343c0c48001c454408032903c0c101f000e96041580b6203051019a164600000c600b524401c070040c00c20304101381c0014001922803d00c0c0c1c21103049100281d003c4d603031401c0c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 564364883 1250 564363633 564363731
    0xa0c0201121a06090303040504111e0a092606040b01050a0803090d1e0f030504031a010602030a030c020f0f060406050601081303080a0f06090b0901081209090910 71
    0x110415030038031203a5072840e4900700003e040a1304000c0c0032642030039940c4000409076a2100029140354a0008820301d40148400c00440101e079014080c502e0134801d00d40003004500c80c0c1c8109418100928501c4078071001c4071809003580000c11041314014181410710011110080c4a56440348000101c002201c003400b00540b291041c00522172114807041e61254040800c0300300700056000308034541000028010b0b040248405c2c003903582c81c1c0d104d030b0952400720b03442142c0624004466001000400c00141e000045a99143c0181b90105045e5041301c02030303150048000d00780083c0d01410a070000780700c50004151340b08500500e0305010381d0315408010b540c110300a482030554940b2078025400801c9c0908102d980000a01030b0000340700c0b4140751410704403401c41e0444c0c007005442c1c0c07104910f1850130039013003409131419001501e03801e00700c510a070780c0e01d10032001e903680210800000542464400e1103000b00c0340704500402e0010710b800d18251542090000740302d07546840c0352240322030b41c1a81121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 564366133 1250 564364883 564364901
    0x603140606120c09191410080a020604090b03070803210a0612020d052b020c01210b0a0503250f05030a08180d060f0f0504050303010b0f0c01020a0c020112 68
    0x3400903c40c00a0600c4000d5500401009901c91451a00b541e901c007503124150b04030400700c03451030640c100202410000400d070703841041140d00c40340c00c43c005a41d58000710380072a107103100e001810558060104e8101541c660107964a400003040d00f0084580c5402142d80e007034120440a002c41d0340d8010294103c45c09402082410040ea840c200010b0601d1107603011001e005e03404940861110340d860910010180c40c5209a11385040c054419450301040341d6540b2070b03403d007082c1c4081700d14001c8403074440c045000040001a02d401052959894800090000e40801780948a880141c80074210401c3c50703411000044103129140090a82c241c20003600a4420080c0a44041041c0740c9503100550044010182480b8441c0d02e1204281d44104402440e103204030301c08104030740c500343e19108441c400f88010003080d0400c01000000b90003c400c6a054540f482009500c1d0401e980b00b40504c0e000e8140982801d6100254982050350010610b4074954400d0f81d074044020b80c80d051078030a85001038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 564367383 1250 564366133 564366169
    0x718030c06050918270606010804020613030b010909120903031b03031103250e0f101803050a05010506040b1e0f0301021b0c030c0105190c060603140606 67
    0x60014032045100d82c000b44264a80200040300d5040450340107414140103449800302c1c1e1001d400e4152400501c00210032194840b00060b1200e403605400280c08448014002841079500140407041080a00800c0d00515000b4400d4022980c4550780500141010300099800c200708803005c0044501c03907071300c14003660b034580d880c0b594481a0800420030300280c444c0031410b058450030301881e44201c05014601c910b034100303440c1c19014030344452020001c4a1889003405c100045100d107000c1c0e1110015000741450a03180d109440300180c1e070489000b171200c0200b941c40d0008400001c10f1000000c0d280c0c81040c0a0002041143c8840c4208012505d924560940104082e0358090042000e144950007446e0040c1041f00b0b2132240c0b00019089038440180c0d281100c590f100342e22004801007002400c0303640103a0092404015180001c2c00d28068110499841d4107886d507401c0c0243e2003000b17110b12017070b07124070144031594580c0380456101c0b548041603003a92180d180011901d1506d41c051000d4803081c2c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 564368633 1250 564367383 564367403
    0x3011116080906040b030a0b0a05030106060f0c050c03030c0706030e0604151a030d0c050606030303040305031609030516060210090c060f0e0319030206090d0207171006060503071803 80
    0x190780d88101c581110882c0395003c10305020001e02584480010741c0b1808060000161400c456401c2084d5415690401c1d4003ea140090130b2007546d0300b0500841c0064610305009046603014078100b4584142c070a8000c1d0036010100f03144544c0300e00042d02d481a12940c0d2014008091003910a56132000125000307404e82102c0c954a014460060340511003250107a40d52055020301500400c1c034024030441c0540c00a040035081a05012040c002c1540000d421805180b03981081e440c002c1c458080030f04040c0040e4090034100e5442030050348020011b65120381942d00105c2c1c100540e04151040c0c0c032803030b0054091060b403001c0313605403445102d00082e442140b00001c5410034500315500b615008803c428040340101e4200540d03410400b212000d285c0c6001d1811444036858000c0c03e084020b010b4034455030044440040076500030074000c3c19107d8410300100000d034948100742c900f42021a1000d28940742c118003003025a400001140700d0019512001e184030300740580140030761098400a8a80010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 564369883 1250 564368633 564368677
    0x509120c030d030e100915110306060307081017280c14010201021c061a030f0105011d0612010501140403080304020f0105251106092101060f090605030111 68
    0x4c2c0c0c02800e01100390002c4074118038001c1014021a04403040642d0b1810740403102001051081c003503c0c02910034011582e0135414400085000741c00b000d84480e00340b01054000030500c01090203520020003e00c43d0040a407402089650307118485845005040c814619420144400d050015600f00e9800586800d032240360038001e4140c5c00303040c89010b0455400b08601510041142c0c400c2a140d140a4000030b0258a003050710502c00102c0d0198488405080c82085210003021007510f044420030300700186003a1604000c03043c00c03a0f130321044591180c00461401c45000130b6030b0300103058030000e8a0301450030a8081b11030009000710f210040034003e0803c0001d0041c2030400c0822140d05041c1400c6080441c044015820300c0c0c10054050401403c00d41035105000703241a9400c440041918142c3c54080f00030085130014040c150020440c142001900c241d00c0f1007540400010000d5603c8142c0f82030b10f8030305010242145100d114801c0d804e02070440724034000c82c0c084540c8200b0b2811560b440d030384 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 564371133 1250 564369883 564369887
    0x3070813120809010609020703090e0901060303080f061807050304020907080c0d1a0a06180e010f032406062d1709100615080a09170d15060509120c030d 67
    0x4001490743e005552584000522420140003a000e00d030320a880c1c41e80c4460401c4610904040010700403032860313050081c2080441e4005074269005955400d90b0b048070369400c804100e0240d01c3c81507446030426540c0c10081c0c1c45500601860103980300303c03902c901903180c008040705c950a042d90b4403c0f40810030840d02000382c805a024000e030300050069400132010070400240740550551002021074031406c1103034040c80307401040d440039014507182d0f65540e504180c50000b50790110b010017083c03503110100300101540d00d800c0f1a61001c0030010709011031901d594005040d0b811003822510071804100c4803040030500e15040c48080a19607440040015002e003031080e01c0c0001400700165406a000345042c550382ea4003c0c50050310300080d08030084a4680c80051000000420f170101203803800c05007030300156099000d4041c1c0e40d0190010740e25040419441e00c01081c0103028000b4070440b0560002d02550040c002d0000d08104079103044994040039000b607240e01401c0d5405505401000d070300060301d4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 564372383 1250 564371133 564371147
    0xa291c050f150405120307090303050c250602010b01020109080d0b120a0c050108070509090103030f2105010302030105100f05010c0f12020a050705190e130b0c0307081312 75
    0x25009804035010900050380441c10001a850a030441d01010700411003030000800001c1c0380c09161020341c501e103180041000f4400d05090000600704040012074024100c03040020715210b12a10701a105219104074040c921400c091040e0400b550030000000078a6006201d8240006e41002c0b90703c1c5404841c007002030003401090107481e0710510545800003150401c2065a40c494814160240c002d03052000250240c03c009010004001041100705060745540401030b0443ea03250a040c1800d090091741074820171084900c9052070700c485035418001c1031084d003103141201d0080c0c0003007000d81c40c1c519030f011601049004d00380c5442299001080103501c00c901c4900e0135070051842da0709003001c90751070784036072440340c2c5500f00140d011800c59024080244a0080142012541a4007102d04030301c00d112022070074428400039811040c0003403c181e507004c401c8480d09038820810122407a0088008095400503610355000030300340710020b8041014a0500b20006421102c0f071403d84208407021a212 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 564373633 1250 564372383 564372439
    0x3010b070c03080a1d0904050d080c0910020604061a210109060218011806090b070c031a040b010e0f01051c173103021e03060a29 57
    0x6510070070000100311818090702c81c200041c1c2d01c0b079041d25154440200d10000035002c1521845981041c440001c01c0081c0c01c0401c245035041c200d0040d51101603044407400342c02c205c15007200380ba000c4e01650540c0850803503c61803148500304081d449402d4482c1ca00311043e0045030b000055011210079000b900d4010321100169500045180b41460365110145d810050b01062aa01d10702108100346d0b8122070546286100c60781802c1c0900d05e0201d009185201c6482079210300340c1e00145d00c0c01400041c800e120051a0081c0010440350302180040c42002e40403601612140c8128001060050103041014041c2005d081c1fa120346908080c100309512103c0c0c42000c401c140714001c1440064105100c0620840d04e05400a407603040f01075a00054580d84056554600c94401e80510740844800c40c89055070740540303403d140003000d40040240c440070721030f070285d15228000402c56243d400e0f402690107860480d041c81d4440000fa9041d8060320380c0c070110702d54030981c4240ca8100a201c5084141c101c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 564374883 1250 564373633 564373643
    0x1b0c050a0f06061d060a0909050c06070c1a1602010806060712020d0210060e0f041a0c1e13060509060405120c09010f0f15030e060a140a02090603010b07 67
    0x2188803a5510045905480c00c4116000c036103565040144440e00c02d441c81c014021148003070554940900044e000a1a0b4010b07502c600c0d550700a01d030140041003000050450f009050a81c5c0c0d8145414040012110340c4560381407551400d00e030606602650040d03c132441e07804648000c042e00303039030700540d000900284601e81101341880604049540e860340007401d80001d40160405603d458002030500b240361081c0031625081203030400c040000000d0306030b4002c0810803110010344440c42c0043c800521144080d00640d0300c6010b0000300c042c440010800000c41d1040750a0141c84200d00f00d6050040d1400100103180109082085c02e018000410141d00001c0046140ca610383c00003030404201e01006c40c00961010b040c1d894181040c070a007c1c05401c80c1007060301864640b000c0344080d290b260088880742c010602250b01254082e404c03080101d00d030001500e50340d10304400404001c00014103600d001042c0100440ca41c1c11480c402c50351081005041180303507a082c07811180f40c90780b1840007116 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 564376133 1250 564374883 564374893
    0xf1e12050a03020904021605010b0f0904060f0207050a0b0f1612050c09061602151c0b0105040e010e0403033e0f0403260f090f0a030507180f1b0c05 65
    0x181e079101d100030007440b0000c05100ca2907c0035070400c1401c48001c011154040c00d013000c50b10020365549140203034444e5003c0c00218890800841140280c01688002821803294100c1d2900f0030502c0c8560714420a0b00d0200c006d61a611610b01007008103150041c000403488848815a001416070005540170200c0c0c2c1800b45001182c82c04225958001002c000440007411030301811880c240c544030341500c4a0019050802d371490300842038200203d00070b8a41c51703076101414541a4080c3d03040c0c8006001284a000c0c80e51781d00d024968140344200d60880001e440d00240800720000c0285000c01c5c0b090000c001e243c07034180c5108000d0040c9208510180c840401c1c00f628480c404850000c0000c0c41c822050070007140302541c01c94402e000c0301883c890142200744049600424808280d800c00803048661040366488078003c2788400f01544c0024025010741400401d10251119803886031080041d4101b000c83e10007203c00d0215401e04e1002c00c04c1039245030318195050b11554500d007006000d4401d9076 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 564377383 1250 564376133 564376147
    0x70903020303041401120c02070e10030206070b01091b201c090602070603020a0c060f021b010b1215041403041e0614030f041202070b03040f1e12050a0302 68
    0x70b440c2d50050341c04a204400941441166540d03c64402104607080c0c1c1801e00c401a0400783c040e40381c82190080502601d644d0340000e003d0000010301c00001e40d005030626079030750400e0030803e43e812003d01071402006d040c84d00510301980300041040d507080103984e0714003100c00180200800c95a1244480e1a80d10583c03982d01005411840354401404d280c0e00e4200290f032030100c0c043e00741038040e07000c2028580b0500000c00a10741000e65602c070b483c2d0242c0001101205000d850009000e401e401c2039913942030500c962005c00341584042210340c3e08440c40301503c41c01c007103043e964003107030351144d0303440c001c80030100d030001d0b101c3c2032114540340f444d8096030b0401c1e468280c1854038414584000c0e2440c90000c404014942c2c0000194031940004201c061540ca0405004075000300041e000801071703505602c0c0e46503c50b10a200007070260002882203503880c241800d060ba140390010000380c424188000f42e00203090070302040000c601c0d620012918058414100a642a80103540402c090540130002c0e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 564378633 1250 564377383 564377389
    0x80f0c07090902030c0607110f060706050a05070e040606020309060304020a150801030209071b110102031903020c0606030c13020307030b0a0909050d030e0a0b06210f010e06160807090302 82
    0x2030041c1c0190480000c501415004040c940031603048004d0240d0350030031000021803489105000c1502003521100c85560ba04404100148144000a4841880c0405106510f00039400c1140184440e80d40c500700040d4030000c1100f00d60040c030524000da40b04000c140c0b0395007061000755510500050801107903035a01c0300110881d01c043d01c0040001030703c82005004500d00317111100d81002043c5051800c02d405e00c0e00011050f0203000000c0c101c060b020090710926882001160b503859024400002d000540c40c0d40580a5007110703085c102c01c0d02507007000070f03240d041c0051245107918005000e40110222424108002c0d80080d1242d0304058035000c59101c0c6480716076421006005030307040044c00aa240c2030880c101050220b01c0b00405042c03480c03030b2040b030200003011055248c0003023106505854810005018009010260424001d030b040340f0464001c0c0821800f0307a600c0500024421110641500c5898a02c1298110820504079012200c8136103c0e840d035685c0b048080c207109641548035000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 564379883 1250 564378633 564378643
    0x62c0f10050307030f0612030e0d0c320a06080a02070b13050c1012151203090608010807060516060b040504060209030c0d150c050d02220b070f080f0c 66
    0x644003081e40041800a4160301d4803500d400c17501000410003495042030200315180c00108030240402c050050070b9980c59841d50040121150320111401c0320b2070303681e40ca1030a107041c0d100600e05121401c002c03000902c8400d01201c00624401080e07408550b080c0300c82a00c43c0c020240444048a03400d1200c0c1c0002040c1403452070241500c0c044100d50542d107494818640100740152501980540995100d1150400407030031411054003008142ca58403403c41c0810130205a00074075400300301c08030035824180c01001070f03415250716640f02c00c916a201c1c10001d40d01c1145100b0500010810011102595a6560b40c2c40e6214400c16000c510110884002000e441d4103490607125036900182406851504100f0740104e00c4e415240000c0300c0381d01e51101071805926902c03891069484246040c0c88a205804807038201d030440d0002c54844007814654040303603090701c1303221243c101d00740c2020822101c404203581085501c800303640d103000c0700d5940b0945107030018400303100142ca040c0710980c0070341e0303081c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 564381133 1250 564379883 564379909
    0xa120801091109150c190f0201020f03120a11040b1209010c030614040507090806010b070515010302031b0310020d020715020f032d071206062c0f 64
    0x550041a5410192514100c1d030815150360340c403040401403007416481e405050904000710750400340c1c44206449009041100400302c003081c10a000310f12400300302c1182c1074002464001e0742200c4080a0f04c103500da5581c8504405104e441e2192400604080c10980150341820340e0341500324141036503580c112607145c010b0810000c0a480b25010041101c000748100d04c6002428502401400d28164403980f81042e1213406900403500c810010300e0b2540122403003001466210102c400f0717580d4440c0c40b45003980080c4011149400780101005216002060050580790020041c0c1042d500c3e5042008404509a200d076805010f48540e00c54224140c0c8042c0050f1008c000d0301503aa89002c3c0740100c22418410594500f40340305004040040d6020010780f907000c0220040781000242000c002c1e0f030150300140151041000c44000c21a004e40e0001340384817405070756001844540c0c2c8841c01610b00e000c0c440c0d440090110301041e040214002c03014503074081903001c1d150f4031088241c0c50100d0800b0300320701 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 564382383 1250 564381133 564381137
    0xc080409020c010e1b011d06070b040c080a0b0601111c030603060e07122004090f050c010e090703110c0a05030a1709070e090c0301050403081005011106060d050a12 72
    0x115803285041d100303000d100200040b2101030f0407102c1040480c41d42170110640c8075810092140010491007141c051b80c0d10145c01c00400b481e80b0745210f0b03d804c48400700b048501301c90440c1a03590003e941d14000840c00c418a900c0303411406aa55580c0044802d08104010b940341403044404503103090315006940710780030307106541c0418070b2070070741c205903040d94080303001801030780c0c400c0341d00704154481000691151580548031400310302c1f11100e80c285021040d041a0740c0a0703c0e001c01c0400b00100c100480c80290320410a460211590400540c0e040808001d800d401118140000e081c0f1882940b1910003007101c0030740d55003070282510b0b942d03141000300c0710202ca46074800282c0c8450b1a03040081e12205c5c1052804081035464802202c80d02d440561155000740354000300031841d83c070020301c000d0340c000714098020485071825040c0140004000c0c0c9501e800c3c1c2c0c0d2079203004035035944600e4402002e1610130300103018944660b01401041040c006054555029030f00030107000403649c2c600f00034640816 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 564383633 1250 564382383 564382387
    0x52101080f0c1e06120703090b060405131b0b04090204170d170408092701080c060304120c08030106090509010b07020f040c0509120615010c020a0e04030c08040902 72
    0x4060a5494007290000a000507441568000d11940e22800c843d101003141268241001c0c54103000b15216000c0c1d209a4901c5211060400059170352507400021001d020b070314030b6031150b103541051108454081e01e4021800079007454280100e84002a0402488003030410150b1560351100442603c0d04544c12150981c2e4000604110710b01d144000700704148007020250941411041000d064007504540e50f44e070040c6c4120000b800c1c0200c0c2429222000b601605d9080100c1c20707001e0103035000c030045514001d581038074030000c251701c0300000344d20010392000303040300c3e00e141c0302e94581c40c10300c601802607101000408140240010000c00145008012503141c2d8200721b401d00303042088046058202200064041c05aa000340c0d0b504000342c1c001c4442900e0000e00c0d022040c008441c18411860101c0c4c201201058001098900098051203a6034040c03902801c14401001100e805918241c06584040500014020a519100040c1d0454820304014001d41c8040d6110b508540260f8068580c039580 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 564384883 1250 564383633 564383639
    0xa020309040b01090b1b0c0402071b0902040f14030c03121308030901080a05130c1503060e0103050c1203220305371703040b191a01030c052101 63
    0x10030b0054822046007400e18191842c100801213025000b540003e401440d1080c80e5400c10314001e020405104801510075551000c042c10500302c9a80e00007405400724490f000002400b4905e8401c0d1410b6520049180c0012460312890809080101d1407059241c0940110001640d4040000109541a040b0000d84542c5510040034100380242d02c900401e4008002c0e4402d40d81e885081c00e0361001d080e070030000fa03948440c1c904007442e403c88040140407050021020a06110740c0d079010061111075502401170903120208550522403e1100512f15841480050303014038001200d803003082c8550040300c0c1008540141e400d03aa040265850111810451080c810301c01c0c00d000c12050511418015000b000310402019038403280007141441895284008208105840c0000328444200451040e1241403500380114828000d0b43c5080c0c3e080303c0d405100240b1405400f68220280310606001c1c00c203000d01d00150042e100d03044490781080000c10141c00c0d40b09040b0900d114880d10130554802c2581 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 564386133 1250 564384883 564384889
    0x1b030b011214100e0106020a0803070c020918191a061903211704060c09030f0804090b03070e0712020906070b1914010512070b030c030618090312040c08030a020309 72
    0x22044c0c0040c0072106150740180442a00040c4024065601404296a070390385e030390089480020f4003d00a5100b11010180a0001c0569184868a403801d000b9128040240301d001e0464071002c180050540c400301050070402c0c81d0400740540d0124002c2c00c1c00c0d5040d600f0085902401e50160800c980700c0604000b0512144203401c285009001181070640e1880c1c04201c000702c0d00c0134020002425961941101c0f550b061040103400b00841c2d1242082c5004081c5241004260b0010b006c0c030380704185070611008440c03800140c0b45c01100e0580480409580310b03d1011a1012030100d0340300345481e002c1005072640e80b9803e0003004a940521500003c0741003808d5645038002c0600903071983c0b10b0520b9007061980b50180e194a04640f012a05028130003e80802c0d50300700900c981c481044104040104009004140d0085105190442d00d07030304c942c07440c03120f0035552400980b40c148455100384030103003008200095658025015040243c8400e6950140d80c1c0f4581c00518450010703000455001b0880c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 564387383 1250 564386133 564386161
    0x2030709051c1e02010c020f0109080118050d0f1d040603080f0702010807110327030330010f0b031302090a140604090b0c0d021201150f02011b030b011214 68
    0x108450501454103d078000810300f040f82040a8800c40344400038240c50fa0040c08078000510000c4000d100320f00c40b200f038000c2100000142030b6814020b44a801401c24480c161220001501380c9500064050b08108141d01640352514a40c006549090100102e80d181000c0c10003400d58404d1356503621085d03c00184080c4014184209200359103035100b00404020040e94522a810505c1c1c101c2d40b8480e00304050348140907500380b500741c040041d8008051a01001d1440440c0c040b000702000000011076846a08009120f001c6000e988072905125084e5110021a0489000802d40396400055000501c2c403c2d02640d0111a076a41c4045402c04c03034548240c5950f014100300e5041184208580310340c003807004028959001d40c800041e8015a5102c550f05035008580c40c600c03d50305540c2c6450300b062320241e400800ca00405e84648144000e103105020b010607801c010fa14010104520030019030140c200d109409040c0f124480b40607d40091f50f108170511107280309041040c50074030146c908145 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 564388489 1106 564387383 564387413
    0x30b0915010510030e0106031a010e150a060f051c05010801110403200a09090510050f060a05090c0d020f0307090b19120902040516030c170a02030709051c 68
    0x202c0d278441051030503030f4501c0c905008242c495480883c1c145450b13000c841c0e8040648041888001d20400060090802d107092041c1011420500469401c0d6078088002e40180d90358010010480240182100325407100f0006103032a007142c455035115a68009035204c4d010600645111945400c40c0d601c0041044941c1000301e16003629000e52100000c07510842c00d54182404a0a07030304401d00c003c2e015860043c101450340d0b1805090140c61400200000e000c01418040d40c140049907000034000c211403100803d07664036044501510342d52940d00400c1034001e080c01041010030807001c0c80040003c0508261103440d00000011018082c8844000e400900b420144002d460840408808003c055182808400340360102203d10486d0003a548801c144c0c082d01051006035036a0045820580504d803800d00281c44402007080b25411076040455041c07860011018051220703c0c5201c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 564208633 564388489 := by
  have h0 := BRFrame.cov_init 564208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 564208633 ≤ n) (h2 : n < 564388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
