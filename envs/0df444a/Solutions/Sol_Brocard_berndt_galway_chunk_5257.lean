-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5257
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:16:04.707691+00:00
-- url     : https://prove2.me/submissions/1c771950-fbd5-4f19-bfa1-b93d942328f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 945323741 ≤ n < 945503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 945324991 1250 945323741 945323789
    0xb180d0203010b06070b04201e190602010f0b0105030c1905040b12092a040504050304080a12030510030b011202120304060507150204030c030b09070b0a050c0c010801 73
    0x204829100500126900c2d110700d01003183c2e0b80211504548000004041c04104501c41c00210030b030368462081c954507002200000783c2c0c818000944440080f040d203140f00a540c40380a84415026801140d9000550703444000900810310f014640321281e1800c0448440c80d071095003160302a000e0341c0e068504108c00c110043d5082d21601c01c1c55414003008000c006140f908290203000001c905c02c0440d06940b8101c22807508001c9811500442100d00481410041d005500d41c1140c0390380c2030718001219611440d025245200d07a40001d6078500c48c5440074000c21840c0041103c00540760350742403003192205220755000403050f000040c25100c281c07005116100061641944c0f4500081901412031300312300602c3d0455100350443c000255000032a0703428400b9031491000714404501007113207424070390380f1210340000c000e002c000c0507a40c6400c082049540c0402902000e021810b000c1542d4031707071581015110340d1081207560b0284c041d01460103036540c0100076440c101c8201548445860300c40454130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 945326241 1250 945324991 945325009
    0x1202010807030e1f05101a1303060f06170a1505090a061416090509070f12020d0b1827010e06010807090b0910030f020d050a0302160b18 60
    0x90020550f403220300d882040010001500c2440c3c0001040c0c3d100400e0355224015aa4010000c10b5801c0e0039000800c0340d1410342c0c00e41ca006101d610701c00b13034071039202c0400c00f02040d107290300c090510350800c00c00c000502c090340e00401c100c0d1045c1441c076040500c00c0c00003a454403171340540070b07000031101d00c440501400203400a50f07109540c1c5040d03410307207655a45c400c42100c04a01c48210706440142c10002c0c00b559549582d0700c100002d0800e081800c2c0380c00e000400b0000000c0c10803081200c0701c2d1420b208180034111300c10301c20807400e4080d5165440748900c507004200060059104a82c40c503881254000e40600c042c0c0940d0a07640c0ca9100d00121a0180e0710354500d03c81510075640d80c4140b07d050100c003d1003070380d000c0d00c500e1026041c00c91500c4101d1058440ea00c1c0514803030071501c401e00a02420585203142160707403040c00241420b42078000900000602900940240100075551302007550104005142210b0309001c0c40140d900c0b0100e511b52805030110303000b40d181915043c0c164500e0481c0740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 945327491 1250 945326241 945326251
    0x6082b030f061e0603060f030c0b0a050906070f1104230705090a0e1501030213031205040f150f05160803101d0907050603060f04020306030c2106060a12020108 70
    0x46a0180d41d800303195021078520358490300300642c244091015607403601074100108403000034011014255240ca0344209d60510a490107103800043c1c2901d501e000b141910075132900140021b4030355586040150401900311000c44281e80ba05070405a030385050710132000301d882c9440d01c00711ba03412181041000d08001a04030790601600f0302640d003181e610040c000d0051f0550f20100207540c2490300c4a607648550241c00300e4181801130100842095900c0715007000c0302e4102c2200d40405400d92001e84140c41140c100010030350381c200c030124001040400603654040039603114207000442400032a0140500b072410307030280f01c0c1c1280041c007040c00c00c0c0186807c0040b8030340c2004240e07552112103510900d850f9500109204101c100b00c1042c50a000c4500207110641d030341880c515180b4002400420341d00012807003154084040340710358a003000b4508201001500008412882c5822095100d9000230306094920844001074203a08004801d03c3c01c07a050006c803607900350000d81c010340e900940100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 945328741 1250 945327491 945327521
    0x305090d1a090c0a0b070305251a090d03060e060f0f03070603240e06010f0215010b1b011a0603071106011514120601051b1006082b03 59
    0x40c014542008404240102d4008008100220004082c402c09403229407024800134000c0c04004046070b00402110b642004002c410910503111844440c1100c54103800030b014203e155802d50180c00703019074130741d01900350b80048950001104904609540b8103000d80115000910042480c034103005044008031340303004001100804010b0042450301c0803903841400040d88071018007074079a58001204440880e105050440f10703050165408105034094400c5040140c031074201140e05200703001074801d050700b45c00c0c0c40f02d403543d40f09020a040e80169003000c00381115003a103401801c005204041e013403100d02d2078809074100104200000c5401c001c003e0400c0c059481502608070505000060180031640e81c8a0081110500018640d00c000d028101400004114081c6402c3c40300103041d03807100d404d10f230483c0d85640081d503005100340320000140b45032203405085107220340d0070380003502a541e81c0e01c1100c5407507004240c102d0003960400303203080800d030352907070300e822414400c0d0001000051010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 945329991 1250 945328741 945328763
    0x9050d020f31060617040b04020f060d3603020712031701030503120f151909021b1b010909050615220f06090618080304121205070305090d 61
    0x4080d0203155403001d0382855650341d81d03c0a000341c540018100c41c00189441c02c4003583c3c46d1564445002c0100500041e1148018002c80300c49982e40d50304660b2140d29202082c088401340b40c7c4060341c13014188901250311544521458070b07180204c0d50440c07404d0341580c003c000349490201070700009a2082e10075000c00806042d41075203105400a058003c5101d0b000079a61400a00c0420318445000b42019a07140c180b00c007071220082c44601d9030054400102d504450340b20b40c070380f50350f4000c800551207005064000700e040c9000114220707648804600d00010742d44a0703841d00401660440301c1c81545400308103501424000b00000d42d205039404a4054000411280c0300b030424041500400f440342144000768044111440309a004c503001041804e4002100742d0408902030b20364005409030904001c0c0cc280d003c5101150b61114600402e442000e032951a9180e50344240c0320802154160355036440850b01c1070700710780309030116072225804d950350030b050403410420401582900b0310309072102d90f00c803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 945331241 1250 945329991 945330049
    0x905030d02030708131e030b0a1506121d070515070b2a1c0b1206010b160f120f1107030f060f1a030c041a01050912030406050a09050d020f 61
    0x104000c2c6d02203501800d207412540e0724500c5c24401350b07a40200104807440c2820300b12200440341401c14015201c2506252005407468031200700140202088a80206802e6130510181e0b039000c030740c200c151401a6503908181e4601c0d011400302c3e00c2543e0008041203138100c005140d8580c008822502e400c4422303060005190001d00c40c0400d50032a02c2c100c24050001c02104003946618400c203450004203480840620110280264a41b0014890451a12000030341c2d1556103112035215643c0552080e944082800d9070b00b4a0240031400c48591030219103602405a840c60150318401c1d1982d003810001c009940c11581c915014508083c1c00702e070495100c20440d800c119890086000141404181480002058081614149110b40c08034044c5180c0010094000c0400420342070201c801e0030201da4920201c00800c1401e06030312202d03d100d010200c0c0103d041a0b022000302620310b80341d40c03207208040d10345082110500d8084070003544081000c1c211740050414145580b4428172030500e821000120f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 945332491 1250 945331241 945331259
    0xb1309050312071d1801030b152e081005010e0d1a0a0b0402040602060402041d060f060103060f3203030f070b15311b0905030d0203070813 61
    0x95034120081941c00800c0c10354004e000d44018002074088070601400d07540003603400642d22043c000074101d0600480050030f000c0c41c40e6070f2504d40c03020182c0103076000603000a5580c421014010400c01c10503c031b80e0ba003e6881d01c910401401072803001143c0c50090316110041d44d0041c000100300c0d811940760b00c101008210342c000c4106c8815011494001d00c0c5c5003000444c01261030700c031001c51244d44180000d00049900003800d0b03900075416a40021841c1030517a03c04a141d41c6143c1040442c8254400c1003141d0141100042c022982a2401d2181ca51540380c0c4400001aa0007158240306030000032403603414055044455011015100d82860322940d000329007907600c90100b0b11071207040000d02204200112003403a500004514400f6401c4041e0400928607000803503172040c0c01c07202e003061aa064a0f94411300c21400c4400749080110400c040ca00d5140c600108546001040d0a100c0004a90030041169504142180d026518103c00d99640401540000040c0f04903802c0241d004200d00030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 945333741 1250 945332491 945332527
    0x270209010e090406090201140c1b030f060403090e0906040206030a0b0109080d0c02150a1b083708010503060c0d1d032205060904021c0518100b13090503 67
    0xc00342102103100170321400003501c911512103202049030420000020b043c00c010803070466001110001b080d4401c090b43c0040e01d01084600072224a01906080c40101a04296010112841c0708030717203611641c80c001034a848020845029400110800014411810b646e0124805e204141480f1008036150652546404207103504200030449400c0040d0651130143c190320035030082111a02d281c49c0f0b0604004200c900c48241c0421300d1603129000404212449007915010003a4000c40116020300c841040740400e000b0080c220081070074404030086a200b001e015060380c0c0080c004002540b1000310300003542d030090030603e1403140c1e1116002003854001c080950b103c806000115154080c0095010310358466041c00480214480c0f010400d9445400944440c0c50046278010b0300d03080b5070710114545068602000e20010b2034001008030b01520710f2152618000d9540848080d4511800b1840487d000f02d0400b44e030029001248042c0d40d0240d0708814180c03403043c01964201186405050f50400c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 945334991 1250 945333741 945333743
    0x302160c030b0a0e0f0c0d0201020f0f0703120f08061203072f01080f070c0606170a05010c0f051e160f1707030818031303060605030106270209010e0904 67
    0x10a410061051042c1180a160079404480703005c0c2c81c000d0344402c40310b41d90755407100c01540100135404ca2441560b000740091b4008110b00c40c140c407044c0b10b0802545da00c0c0c401d180401c40b00e50091501c01c1e038446100fa0700c62400083c664a40044984413242004103007140c8801400c0d1038841040000c001540c00c1c910405012035910484140380882542c40005600e0260103604002c00c210401c8459421201159000740c0103040a038001c10040c00d0050191699400522288081d0580808119400101034108c42d02a070000c004204004904403070b440c2220441b1710003c3c40034450715440f12180d420306c070055080e140420b03241000e80c92150750b516000303c4003600c007000394281d141c043c031100380310b10080c0c0303402901d40b030f89000c2c0c2c1540c01070181240a070500041051210340c0b2084404100210b0ba9003950415007036100b0f80d500c0ca00b0a000c2d02c424000d1501075405c0a1300062603840072140030000c2504908082a940007140720580250045100d46040007038803101d01840d40c440c146041c1c040c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 945336241 1250 945334991 945335003
    0xb06160501091415010911070605070c020a06030605060901120b2206060201020313030e010215090307050f0105061518060d0608010c0c05032a010606020610090e0d0302160c03 77
    0x407100ba003480e005982c0310341d0410005800144952062090912406041d102c3c0100c0016a600045e030100d242030150440007011203261406100c0040c0e00402c1c500d1019200310b512100e00c9450780030440548066124454218006100344002e44d17000310202c0054502492000030501c80450009020807808049041c030f10f00a180c501640002e1401240082c1085000035491030408100290090a90442c09000c2207200020480160b200307000398190000104c0c0b1050349410428406510713680445c008a40c0d0f8800c844003c00081c4d81030148603c10f04000b0006140c010900c04801404d0307000c0041102a40d401d60080300301d99039401c0240082c0c814002e0005032190510060b2402c64180544050030f02c440007007a1800284000200c90928024080145260181e0003041c40702c4801f64480701c610307509010002c20441e03800140c007846100c00041201038195582003180031030b00011000f0607c2d40003a000220b510b80250001c08103050314511142e4505001e456440713059045402c2103403a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 945337491 1250 945336241 945336251
    0xa020f030d0c09080a05030d020f0c0715202e051e0c181203071e030905061905340314090d021e19050a1203120b06160501 54
    0x2000c2c0e01491010243c0b00c0c400017021011620b80321140c3d2070041c58280703100c06800180c0c1340314002c8a2421341da8940103001c2100c1803e6228002182c16050130319021000800c40c000702400c207400c8040f0400c1302c80d0398401501d2080541c0031060507420144900021141400170003101d51096407048074418050105241c01b8460b02103040800e0368405401c070947c0c0e00301802000035100403104d1400b0b01c0c0c0e0003220003644038600098041d0031805601d001500c02e14503500800c240486d04040b100d9218843d954104d82d0030348030000c00c0340c80d006079142d4078010030030000000007103409440100b4006034044000c44003042e404034600c01219480d141889640d04c62800e101c1019042820000c0c03007501100030b2800c121900022584030814281c000c0d00c140000104035860303000c07090051340049005004034500c40e40004211a500c0300341e200341409010940c200044111540d43c2c1214443e13450750b203101000180c5036030103010784040004290b12120400c6401e10041444d407016103254454000818 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 945338741 1250 945337491 945337511
    0x30a05060103030315240912061e2c07050913030e0f060d0b13050c030108100b061902071e08060108010204050a060f0c080a03060302041805120a020f030d 68
    0x61710b00300d070850840a039a0800c03d00000149606e0485041c050055a40c01d28149240480300141c5650000c0c0d610004110320b40d007805200c1e001891020400c0502406900900d07032800300f2621080d0300e0300710046c4904074120341240342a0f0f1f1b44a500c0c2c540011a04070948590010f4030800081d59411040c9581000140130183c1201c035022440000715143e9050040c1034000c56918419100f44075845595003e031964640ea5011080aa0000017102000f84d4500032003164030661080c029180b16214884900c401d840b554010011100e10181156041140840c2e10001c150307124032140c02940030700f180c0401d0303000842c04104111034400d415456564603003600d4605016068010424a900400041c4036030f455001c1120100e41d007902d0f103088002a030640440e00c00c059000700405203400010142130203549a013011301079034021502042000084800280381002c5180300070441d400841c0f5600720191100080c0c07aa508180c010340c0c6c584101c8140c10b50450740803000c50181d040e910005c0c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 945339991 1250 945338741 945338747
    0x3061d1f0f1b1b05071a0f03070e1c15020903031e03160c050a0b0601020a06020711010f1803230708011b050408030f09060f0c0601050f0301060e010b070809030a0506010303 76
    0x80354403458540d00c0c07040d070f0005807201030325000740e0b001d0854106580100c211059003401d046500c903545901e54140c032800c101c4001803001c402044540d10640300c8107202c60700c1d012603003100725015a01c804c211612440c901491400b9410658800d54907000070321440a4500d000d010b0388100280d0140a10707500e04d030000c0c048441c4403100c0300d214200540e00706a01c000940025080c0041c035000007c4504981e111b000423481d01800d200300a00c0315001240c424100290080005041070090301c0f080030311030420030101c44103080d54259980f03291741081c080010521404461800c07034040244840b000b80d11552103803901600e54070030f40d0300ba9514201c40740c200c80644e08002c170700815494102d1a081c54500465a42d005098400004500020710b105056070781d0f008a03450802024226521421106407691311907600b4030806014002c0300c0f518011510341841010140d81941034008140e90801e503050004d60813803c4111071054040210103400c2d6020020080c042c0d01c01c100620344c0390b046107402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 945341241 1250 945339991 945340007
    0xc0519180f1e05062b0f020f150301081c0e041a06040807151106180a0f0501140a0c1d2e0f020106140d02130c020703061d1f0f1b 57
    0x1480400880582c601074101510b1845d041c480d800c10301902e004603042c00052103001038605480c0d0720030280074039038160001440285040b92660001d81d0008d88210710840705030402c22204d00b00140380954240100d1510f40c0c440044000404d1080810160040120341d0690041d00080920350041e60b00300542a00842c03214409803032440c02c4003903d100d43c0c010f2540ea003009060003100d052207202c04850300f201040081c00c45604203462400505160400600924200700e05075084024200054092981c5001d05a00b009142d51139a000704104c0800c8904120340c66586507110074054025102c012484c426140d54100030319046072031011005000e080000ca0503185400d6906140d0200208100342c1008018980103444034055400544000b419581c009034882216925103c0c11a500c554005007280c16240700e9841044541a0f445403c1d500d01025200300201c0d42c066036205501010840e44104220007a040100d4002c0000c0c2e900f6080d03c2020702501a04081400b407851850f07840a00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 945342491 1250 945341241 945341269
    0x20f040605180411061204030305070e011d151206011d091602100e06220c090e030403080a030203060901090216080307020312040c0519180f1e0506 65
    0x104120103860600410050390700d100e0901c8074402d0190008080c41420034034000320410052a00f59518030401e605010804141c50980000e440c20001650440c025094001041416102c68540141aa40358050340f440782e1103590b0001005006860406520006400d40601c14110f24500380b4028000420801c08810510103032000c1c442039014030386651600a400140068242018588405040c1d00e40844412088000c40c40c201c45ea009032003000c620280581144501c04441070003031040510f0002c900070b0040d204101c821020803111189034001c80d523110b50070050300d040c982d581e00e554015401c02000440070980010410060b441e003081a41c1c0074003584c503c1141803a410001c1a0440600304400911008000010801142c001c03c00ea0301122003142e401242d0346403510f44a6100e41e094890f00c0c0c01462440030550712500c0044c90141502c0700843e44440c01c1e0824101640940507100700c82414954400d420a4a001610b041d4a41d0060742e00c00410b090901905004c0240c4403100303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 945343741 1250 945342491 945342499
    0x2802071e17120405242704112d0301060801050109050d030c0312110a020309030c061908100b0301150212130b090307081e0c0904020d02190905070c020f 67
    0x200c001c100d0650b1106860603110700b030355000850591800406403c42c205060450000c00102c3d407880500c0b2150b0f0f0041000358440d4600ca5182d2800061200340c851065141420314800e200d00f94200c519201c40c0b41e180c0101c40d2481b00381035921840d82c00d4987c000c2c4c200c0c02c00210f6880042c459540c01c00d41036801010b003a41c801c940300001e07440003000d40c006030b80002c041024091300c98811040baa00900007641105640340c0d0f031803d1151010b903403588141d003810300038018060845079034a460400c0d0703001e68141d981944500103441a00702c6050f00d000b09407204050001c940403038494520342c040e5000e454482882c4404224170000a80307401d8000649c0010300d503080050740c003010b0440b0195000c860b910110301e44c99a900000280c28583e0701c0d001080c0520402511426100300550001000320300c03002554104003198080c0082080b040b5006034200d40080e14950050070210400144000e10a282032180c40c1c0303550101040d9001031f1502c40c0003406492152041d0b107452041c00d001483e04803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 945344991 1250 945343741 945343753
    0x207061d071d240a14011202121602030d0f0506091f050f0406050402130509010e31050109080903011a0904061806020f0415052802071e17 61
    0x85500d980c03003000600b400f03a45085018603403201c4150381e0109100403002004152000c0d11003550240d118031480c0390a0000f9518801a0701c00340292003110800b610030b150b4405150341da0215030b100c41c25040c00000846c40108100d1810550b244560320701c0711031a41c80468241466800c00841c20800b4001c41000040101040704c00c18190080c80b0854900b0380d52050580c2883c400a8020440c4d03600c015005030001503045003580412140340c080d19001c403007989490762200c4c080a445842114000a01908980c4418825a04e42020a281508034250540f401d4450356000c0c2941c041e424115401040450402c0c000d207028058444544160f0b800701d00c5c008940c0b0001801d000015101400e02c941c1ca4814a2500c03203240030707003401c03542c00901c00e41d034904080b808105903501c9031145440e04900071034802c0056101e0000c88240d1020321546070b070360019a5a590900542c0c10080d2401c2d4031070700800151803a02c1040740d132414416810000042464002d0b005912188403401040c903401c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 945346241 1250 945344991 945345029
    0xa09020a051002070312120603230d05090d06060302030a030e041802030a0809030a080f040612020316030e1e010504050c041104170c04020705010c0e04051e0a0207061d07 75
    0xc1c03413108072500421142c08001d202c3d1025940304803007181d0b401c0305900f0000c0c0402845070089030814200d80311901c000f00d04440102240d1070305404804400061000c0140c09010320300b0a2160038024010b000000b44a030b0b683e4006881c01e882500d00b00c0204001044600c0c140c030b4541f240e008031500448015000346010750010b501c5e1003004000600302c21002c0f1300d0b6561703610100f00c0c2c10060b0740e0000f80541d490412451080a0f0780103445518001620b02401021080650082e60f00440c0400d0441e0901b01e00040c00340c000c1c03c0504031080c10b03407042c03030a0160342e000d13189460107030801c0c541c00006007804d15003000c506000503000b03a240071380c0c280041021281d94103000c9504486003601c01c0d0314040d0302c4116845c02d180d01d00c1e80d01a4800d0011a00c401401010362100c1da480388030381c9401f000512200244400e44100300c548803810404001c101d4411000c42e50f9081c0d02c8100d5080c014640000350b030f034a0048801d027408100001112410b143c051944c1003200e031020b420800040da58078480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 945347491 1250 945346241 945346243
    0x1d06010801170316050c0a030b0103210f0507170a030f0e160509090f060403090e0709060f05070809030a08040806010b03011410170a020c30071a0a09020a051002 71
    0x5013041150407684000058014003d00740320402c0300f003c005201e80703a419924100240b503114280010341d0b9800030940110108460141c82d001c0c45099500d9507401c2481750103042e605038024140a407090084048078591441004000b0041c0c0700e8540c800195601c0d80303d50f10f40c01c5411b00d00d082c6803541d2000004c02d69800c1d01c61442c1e0210341080f102414650344500c41a0704002c4c050100c4807141c40303210107101c20190404801d00c10307208170455030280d43e52450803c40380725080381f040d5408a0050480940c02c0c1b4420741c010881c541c01b803d0503e18001c60203003c2450522002e0060f18031110219082c02803204c28854540104080020141554140b40548a901229001840c414960510100e0a41e80905201c031100e00c0c02ca00d903400c5910b01360200c480658400062030140740182440e0344107005680080c2002d00110203001c0720388490111081c09640c0c40403a0036120105200f032a03000c0d2000c4011400d100f070401f417201007044841407050088605c0141c01c41d92151042100400160394 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 945348741 1250 945347491 945347497
    0x605070c05090c07051902010305060405100e0a06080f0715050a080a05060f0301090614010f0303021f18050a0b01050901140904081905030f150d14071d060108011703 73
    0xc011920010700742c9a203822007980f41324084005101d07005102043d05801a5034081c0401d5600031b0300c0900c015991402004102d03001200c0400700074440c0c5c907090102d95810b4244d60b81c0424071507030002c1c007661a0005a0700d007044038204c0c480c1a501c003180900409444803031240280324141461402d01e0f8204c000541034013130017440005010b0780c56001643c5070759086d000f40351014000d00200408012030802d440a001007125444000764200300001c0d80300740749901c90b012281c02d64040d240450b004490240c0d64070303500e0105460303d611a0f0f48a8035000c0c80141c607502c924402c100508480110f482d00c0883d0010590ac80e41c401c2c00c80c4001049082011116030802c0d540855521286a0343da2624042600030f020305032a01040d1220035074402c54002c0000c42c0180e02c1c0c044941183e41d0382d003140624032044d224440c0d030090b0f68000860000345400390b001071107a8003002a03425990300e4540c41441c4500c3c403042d4540001d850030600400c0c1d41c005800e41e02409040a10921880042000c41d54a00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 945349991 1250 945348741 945348749
    0x516171011041e09060305100e0c0315040c050a240305060a06050a0c1e020a050d0f0821040812072c01142101060f020a02010c05030904051f0605070c 66
    0x48072403c2c0c41000441103580b072101506043d101000752548074103151b960b50101c072280150f034501d81982c0405a41002594a1481d1030050041c45080030300031103040c0b441c0c0003410403150041c031144003055690703a10507140094481814188000a4124100380d0f1600d0103031400000c2c54900310610040b92981032100060740c0450800c00c0d0307201c08040044a9410407908080c00e5030361694011400110450340a0041c18001c0b24104a01600d807004c10a0280480c10700610790300c00c050405002904c100c0113000a880a0003030340c10703d21140b52400c241c440007224129400c030030000780d8a40c6000312029480d004140786c6042e8004801c2100322040302d540040e116030042244092f50704030340e8881c00d1210303420002c00c9140750310b603140c00e00e030900000900c85014051401c83c0c0300214809216442c01c01803020b0303990041100e44155001518581b840b204107841d18003042100289649950188034018500030b0740c0720700c0b010040340014800c40880d4001d4801c1100c00c200040102d0300c582d13240c900303803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 945351241 1250 945349991 945350009
    0x402180108101a160611040504060812120c12090c01080a0c121a0a0b0a0201110f0304081308030304050a020f0a06020615010e130506040c1b0f051617101104 69
    0xd404c40020b004400c0c140d680004041d90700346403030b5100b081e007440060400c480c0c0645003841426298443c050701ca46405002e01c4d0320320400d200c032810002c24040c59a030007246907030a0b24a003a81c0c140b003912603480c1c110345240099020f400300300c5d010350b030040240d03a018484030000c20003403811000c014040c00700003841035640c2d503d8000c0d07241118240030f40044501030040241c09202c1d5904100380d01500702c58218005075191034110000c403c00710b4112580100c4032140c16141d42c0d195685c941f010740140d40103144000e80f41101094002007040114005d45c0290014032007502c683c41088401c28130035040c40d000300440e039410082e06070001551a00f269840c005060703022114001210800003442040e039000c0140310001043c1c4980b580a140030342c0065400f8801c0c15002403040d15100103201360145610040400b20b0f000c0f6070354a810002e0035100f602954040070124151030003403246900908440c5c42d120540303070380c2c21004020b4200c40f001105400d02c042e205986581a4a000b944920010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 945352491 1250 945351241 945351247
    0x106050702010c060e010e2119050c010213060e04050901020c100902192c070c060e07050a09060501030e010e0d0c05070e0c04170c03100c0e0402180108101a 69
    0x400c20985c00c05110b64000c02d00070450381c58864100317a5103007400c14100c450040d040c800c001503580f035081100d1200458410540702031a00040444490340010540c298a550a004091040004200c120000d0605030344039224030758103004010440d40090084e0446078410030034003144400c0824100440e0700c1e01c03038001989a40e1400071541b0468841110500214008008900c0c0c54486d540c140b4545d0130016407030140c0024100759080c02006581c01030100f005c1d810b00b2000103c01d500a80414115601078550041e502c0380030070f03000ea5a0340c01c10b9202e0340d02c0700c10901c0075507450320911141910f280003e00401e82c501c5c0c007090325071030303d07c0401040251510054003440307820408200249403c00c205070903480c1100c1c500a5079002801044c490100c44a07210158640002e42034692900003809008205041d18034540140010402e15091044910003542e0a40e11440645040704411400074000403104000520482004020700301c0681d03400c0d01440b4002e82007031800b40b290101002c1542d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 945353741 1250 945352491 945352493
    0x121c0c081503010e060a0c020d09030f0b07020f0d0f0219080d0c2303011703030f0708070c05010e0604171813140406090b010b0c061b0702030616090e0106050702010c 73
    0x2c090184d0031101101c510800e024000380b0150360707002d900d6000d460381c2a50100520071508844c814928480584090300e4a8000400b0600110040d5001000c50045a980c440306070401801c1c02e5161410501081d0094006881260144071803804032000b008890032101c0107650f074015500840da01d0050783da0343c0d070020818090040324400901203c0007035520340d01d584116041502e038401d0007159406050070504201c0003000109503400740306a4802e06d6095980c1a0049540b090020240700401205441c1e0401044080c0719241140300c0d401b020380308501e01418031001102c038000c1481180001049a2840c0c2c41c5070745004a9104821540500515200c58983e0041c011070200b03005105005014001000801c5e0311418031144142c0118405a990750340d00b91544c050070b00c004c10030340c0040002a00709011080801c1c3e1120307a841d9030070305006d86600400e10745202128040c4c1c0c103100a01c2000360154201818100602551100150b69818484028801c0c0515100241844000d8681d04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 945354991 1250 945353741 945353743
    0xf0f220801050c1c0c05070b2a070b0a090c0f030804030c0b04030c030f05031201180c030e0717071508012102061911031812060103030e1011121c0c081503 68
    0x147c082a04029020344070700388940c00c2003401126a22113609516100031100b6660f100c41c080e115141d403c640720904964520318020040c14040303004403040441540c020035100703120950040038500a40000f83c54a0440c03900aa40300103a422100345554144020000940f0700443c010903240c2c41444080310525910b04a0301e9802100008035540d051000042241d95080703910482d8a90032500522003000c0c1348100381d084421614220446800c82c0000f40400701c40407140d5400e0540180482c0c2c0007075620385a01400b00c0c452082c82c030000f0b0b65070f001040703c1703e25032030380a142c071680788454012484a54000b481e181b0441d40940740425a110062024034040c0e042025610406820340e562862030350404e01004102000d554461740b00f014909806030400510241038a0341b41d181d01d030030414020100300c0f6035060344284900f046490644001c01d000e0501c8020890400c7c508000e80b603107158040048207003001030780140304500c0d006282122f80d6220031300b682c21591041103000800c080401103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 945356241 1250 945354991 945354997
    0xa08010f0b0f0f0d020d1a220e031b150c040510030c11070602010f0f050c04032a12031b0b0601030506040b0904080307090b0f0f0f220801050c1c0c05 66
    0x50000070310108010265508a40000180c41f040c8181c4107078540c07050040025601c030064a2180785010145c1c11100078006512101a40c0407003000c403410402d242070403001c03d96444000c00300c9078024000d25958030b01460850b54105046040b10743c106400c000104840c040d2842002c0c0401d501e0b000c110036402d000b07645403045003a03480140d503e000c1e152000a4082c194a04090310014913200c20003581c036050b8030030075000d9400300c1103c1c0d01c1d1500d55103c01d02d004d24100d55481b8003520100b070410581480381da01c10000d0001c079a41482c988081c1c18042d18100f50101c401c0700d81d0795078070b010100145d41d140d4200d0f40110f00b400c00080070f45440001c10001d12000050603007104180c030501c800c1c0011000074620581050380e0b4802d40320740352140c91a0074090603504000c030070418030100c500c89050201078098030550300090b60070a00303681e0140c2c44014401b900301c00c1c034051048052100c460b080c060b0584c09501c0c1e03402e84d807908a940035142d041d03406074108480901c0e42c0c2d00d0b0640200d8070440403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 945357491 1250 945356241 945356257
    0x6191802090406140a02090f0d020301060f0801050109050705090d1b051302090901090b0a090209060f0d0203061009080c0910151e030b01080402010804050a0501020409020a08010f0b0f0f 82
    0x20410764502481c082c0010b2801510b10300440201d00005030040644e4000c403002d615014107441e0001030004c01348012041540d90480c0d25540300c00340402d40b05036049007130004101050002c034455142c0002ca100f142c070003a007039004205041003441c1e1140c54112a40301e82c80e920250b05088400301c9524600c2c10380040c2c02040d0b00401d83e075035003c10140e0369006030103c0c0604445484035a680c40c20180211038450045a41000307201c04200590381355a8060441031201808061901c0c10346000e410b0242c1c018016100b402c0c0e404010322540d4108555900380b1503015060003041542800180713175941414135290341c81641c400000a0300860900a100d005140c603527200a0000d4940341c014144200100c22100700303020444480e05058424012400c03000b0301038581c581284c607280c0045401d5140100103841c148252007102c0c00268007480140000d0000e00da0050b25010302200003081000180d212034545004007105001c40749540c400c407201c9903004125941c0c0c403a003c480c20b24080c040d00c0c030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 945358741 1250 945357491 945357499
    0x10c140901020c060a05040602011a01140309010209060427050123011e08010602060709150806010c0b070518040203010506030f060a0f080607030c0f0806060f0403230c0306191802 79
    0x2001417113190001c010b001036a000f42c0081c809a01d500c5600d4049610186c00359000600d83d55440441c1809000150340207500c19001610744400c03c0c0200c0e420358000c0d0300050038940001003004181c1d048003600400c40b90f41007014032031545014000e000c010480b0550160300f80803164480b0040c0e001c1d83c1c01c0c450303001c030080014101400030000a003c9220034401d00c0c3c09405a48002540c1c03510400a450582b8518115080c55440500045a080b10010582814068242500c10220780ca05911500c1920715a441565504140183d150554025140c0314000d600600c0140b0072aa14202a240e1000c0b01c07207074107c2076079507a100044202c0e00035803041d2150300f468000811140001f06003a0302ca41d549840510803c6801c4500710781d0642011507501c001140c4c500410054a80031004100c10716201c50003504281d01c0c0d840d20015524a500381540301703403114114642c2048140300f0b0003603e400890142c07520b45070011480158100e2920b100c00c95030b5540c080d410f0011030180787c0b00c41c0c40d50050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 945359991 1250 945358741 945358747
    0x108090c0a090203100b07030f0c080705160602070803120a0c05040b03072a02030606010c06060f0f14012c03150a0524030a06272003010c140901020c06 67
    0x42e40d00203600681c0d241d0001004d14001090b11214075040791202c985c96070300c64140c00010401100c240c1d20400c401c80d40c0704410071845001c59400c00040d000c04c4c0c800c0c40d41c0c1e89400e260506c007034030b0031070340b548496065007003808a4510020b044200c154000c88a003000310703600c0c1c00320008075000d21543c0c10615080740080309100f0000c1c1e00c4119000641818505c004401401039004c1d0151400001d00035490b902400004109500c00d03030560b115144504004140c00f0384942c12030030045c005d500075180801922804200442c500a040800300c1001e00b0507100081c2c41045882c03044001000390320489040404d035a103c3d480030801d001d808020b1070080e9040d4108005100098001615012120681e00e101051038010641a00c0039902000b0300a060041480e900c010160172030040c61031055001c00c07160840d069078054402c03101442101c0000551520140c4d611b103070b48640c3c0b0014080d0389004680f5840c00d0300300c040004100c0f00d05c1c001c03e454201410040b0310302001c582441e60171403008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 945361241 1250 945359991 945359999
    0x50c0120071e0b0a1e1704060c0e04020412150204150c0f05120406034a01110a080703060b0304080f0705010f060f061e1b050d02070303090e150108090c0a 68
    0x401c82c4000803c204901d400398000c201e0b01c0403214071b10581e13040d11140800c1c00c042000194254003540000c2e480c3c2c20200c441e800344000040403038000d6030188440495411005003004800f0070000c60030084400110300340350900070a90540c00000c004a024800301291481c240043e801414403076545c400111081c03002402c1c0030484036086840382a02103410302c144175001e0018010072810750403030790007903124440000706820b00c1c540400194034020110b4081120a0413401c2c0610403424207801c1441d6a2007045180c0200103c00003031a5200700340c540b40d07042c46a8400842140e800076080640c580c1c880c040c1c0c030083c10039446031010042c4603601c1e103141203006c2425508250100c54150b43d64640260380c0701400d03501c802d070201080314000c1a80e4040310102e80160039508a400c48000e6510f01c0d648180d407407038074146403428030f00c016a100001c10800c040e03105c241c0c0b4001d000c8039080303003140e07003440c404844001c104c401d4920705016034000007605180b001c200181c01e403240101148209035071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 945362491 1250 945361241 945361247
    0x14030304030909060b0c0a02040b1c0507081c0906050a031103090f0c060702010903060e0102090a2403090f0308070e0d1a06030706080408090f0409050c0120071e0b0a 73
    0x70b0b900c02d1920840c1000c900203960700c001c00542c0c0840c0c484c0005049801d9856081000801414800d82c1e07100e5000c40724044445425207081c401c161140c03004103282d90030b0842d26880c00d1580c0f02c0c48028503200b0b00d40c90a1559102d1290022208507007000e5071038000c43c92003640903000da0003a070603440300040300b08070442400144078600002c0b15019204002001400c0c413006100741d02003e40850000c2d803081001509585c020110246004001030810100f030001451074001e0380c0c010344e141c4003607107680036040420454884041d022070608101c1501c0f00d90b01c4000c80041d4820107001e00c0300c940c0c0020090350040e8900740c000080105494401d180c075281c8a90741d103102c203802c0345180c005400080c070b1506000038424255101030b203c4400a68642e6035a09055206007a410340001401d0150400f64896020312042c9a01c210003400f02044040001049807211404000b076071200395480e080e1641e00440c01e041038818200000c80941500580540c124540c2d5110503002c110000703c0c40c0002e03034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 945363741 1250 945362491 945362507
    0xf07050c18150103200c0708012c1513062a1808031b010212180c15180d080a1106070f17090a0c17070509090a0b041403030403 56
    0x920b4084202000005100440446081c50074451460703442c44003c4800034140e20103080b5040010b01220181a25405030780d003515041c03003904240c1e80b49111031901c0e4251a04421032040c040c2401000401c0400c03090078610603001c5c02e90340b0810780169020040c009a900f10f001e041ca010380b251032a40504440b460440018803a407000004e032440c14030381010385110020340032070300d1a800035410a940c02c0704100312800417003c00344096600f00000200f1880c400300c43d40c817a8101250f1044001003444507a4281514182280c1c82514503040c910103100c2d5041c16910a007080502c140e0841e1210700104401c526210000b030040384000c034074241943e03806101c620300c550120f400c0ea0721039240c41d6000e4500d190541c503030314040703415001d1011030b441122110980c002c1d1030104840d00300d0780740d4440c0e08000d105600700100e0051811104101c0b00010007142e0300604050394119500e16154144a07102c04942d00010217040c8404003050034000582000d6030b5540d604001d4994070308140c907000d090741d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 945364991 1250 945363741 945363751
    0xc060a27081c03180305090111070915080d1709010e0f0102090f1806010819050a06050a06050a050301050f120d0507060b06070203102d05011a040503030f07050c18 72
    0x14444192a50b00c1522a0082ca454a0003000c0600c02001441e98142c409410064041e0b0410001a50124a000b41000111300403c220280042c10940703610144000c1041508000380c41c0c0d205500f22012181d000d800004581a0480c52490b40d0302d82450050242c40544110100707489500480c0e080c0760010750040568000450f4aa40c0c02d685803000c0c01454140801e00006100000001030f40d41d502500000f68011400d5201c0460303102c0f002e8500301100c2c82902c50743c2000313903182028880c0d41040301c6c40d90040c110ba17051041c20805181001001444140555800b54914482031a03240d110316040ea5801000941620f0003041d541d4801059a00320700415101c003420115040b015050041c00c40d84240d8010300a083d11150341d6010401802e01401d070b1040082c140e0b03205d000c805034001040c0a50111405010038654036004800a056820707882c800c00c481d0041000f003105a82c00000c90740c035090759500080c1c46403d01e062941c14a031140120300d40259403015542c0c2c40300841c0216900c94 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 945366241 1250 945364991 945365023
    0x8010e06090402100e0a09180506090105060a23060f0c07061b02010507020f1c20100f09050402070b040b0f0c040501030921020304080d020c060a2708 66
    0x540d403508108075059006840c042d401c410240100d00405102e486542c0d0040006800741c00c20316604d00551046880d10807000300a4940301c0381860422170103200040c2c00c41141402440542000d9002601c0c0030350320b22841140700c00058031500d40e00070788881d5040742a00100740640341d0b4402a55005140c0c01403214409a00411102185040c001d00000140d080c0842c401290960940d006485a90042e8000d90384801a403c102d4056910550130b5038140301140902d0070070f480c131850711004100c41c0c41c0c1c1241c1040312854180c0581d4540044465203005245010b0391072810f4164150340c015181c3c2c1245402c02d0002801100380031841c0c80c0d042c001d9100d210304841c0d03540c44c18031198080e8400d8030015100402040704000c40c0d84680c001a00c4980200300e403401d200340c030b2207e648500461040004c0943c1011504100300d0406001103450094180090302807050101c00107011032049218070380502c180e24980c501c1801c2c81d03040c00084060b0001800c0c80c000d48441503269902d184076450b1203a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 945367491 1250 945366241 945366269
    0x1e22062a0801080606040e16060519031a1018091a0d02130e030d140106030b0604080a03180b070506040507050a030c05060a0e030703141606021005100b0a0801 70
    0x84901c641c800c1d60403181d001000d400036440314020003001d050b128602c044207108581300401d01125540601c4020070342c0d600c50a6607040c80c140300c0c043c0d031a0b1090076103043c94604204a4546440704041005c1604122008410300c01c0213035082e03440040364500c3e03810742a00040c0c00b181103942940f0524038960140d5020084000361410040c3e58410140000e4100100c3d910440c0b4440c5150001801d0801d9102030364105000780d4a0751045407603045c000008070280d1401088851f82600c10750582c11000c0e9602482d2905055005940710303242c510040400290040d03000f0b4041518110314098407401d890b580e50740301c99003001170355050240c505489502804c0b030700007018501100c194084a0303000101c144c64910700410440f1503040540080d0074082800a0541c0a5400340907400141d0310524248041000c2c10031464603281c0120036810550700449018080c01c0d8000501008407500c00401041a9454802c440c020304c0c10b13540000045100412440364076074002c0e072030078140c41c0c8933110350103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 945368741 1250 945367491 945367571
    0xe070320030111091018050d031808030a051804060e010306020a02370f022101140709030b070e04050a0606030513080405100c050d030f051e2206 64
    0xf80380300e10200381d98403070210314442c40d00c203009045c3c50200f02c54020021080710f80e10004508800800d800446c0010340c1510100c1c0003088030041140a07101d40c1d0015414002c1c0b00700d014065124034a4208604d104005083c0b0300c0350703a0340d002540604260148580256528030f040c9000e0f4102e2011100540544402e030140d0070150840c1815080004a02c40d16819001a103800080107400c01034034036540c41c60403040907031911a00841c0b9085250b89040c911008203c0307203400c503844070440d00c034050403d40600c140e103613001c9601c800b500d801c502054941e4440041c20340d0252a049001038005090508000300c40c503441c0c1c02074003200c4050310306001d40e594071079211200780e039081401032003620240310a0004d4101030b405801e07400040c3c1000c4100301f2a41d02d980e03140070709402c0c030f03980020380381c1000101e42d48d0f080c05220b4000400216240c40140c00d17508800700440001c1980d1010400c1d0011000d521802e01074003008941c1002e0104030305410400428042502c1031b003042017071641c040c2a02 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 945369991 1250 945368741 945368771
    0x80c011406091801020c1b010207080105070c0602092722080a0807050d1a15161202011d070608010e0f0c0706020c1005070801080d020a060e0703200301 67
    0x248280d600034180016a540d442c0d0f03030709559501e680840d86665080c450303482e40020401c10303e041291502816900c00313050f200020724280c055000b14000d42d0601043c450880d400c180e1100760103502440c00b50302ea207803da002c85c510f4886c5051110b00c1c244840039807801181c80c0142d41d0b008581c2c0c10900c49004a0302040c4d42140c40b10380c0c1d8001c1904404009031504e243c8140c80b5290008550314040b450040c803201c070030083d19003c0400c48031200c2503460400c0c10746803801200745003001040407d4141f80c040c1241c1101804200400742140b14040c0706848114404c4d031054080f0400b0a04544040010007240341c0e4910060003890003084144d00041f4440c840c020110b88688080e481c1901e8a0303448000c14402c41d00321110440c0ca541d000d0180071311020062003072681c45400b0982c001054601a003000742154010780c41021382d508414556541c0940c003103007560300c00e40c0005011441c0c1c8047ca00031460100303550b0010340515501c0c0d00031038a43c41c90100f140321418048000f8000060703450703050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 945371241 1250 945369991 945370031
    0x73b1011010507110309212b080403020d080903040b0c060405060a02270f04020309160b0a050a1404170a3f030e0102031008010f110f1312080c01 64
    0x1013044e6401440003000e5842c0034030b00c0320020301746502c034540d0812203058290329080c0d000c080010702c0000d91035080340d00303985200815014a220318065150b07043c50740f0041e445054203803400003080078540010350008030800440c1c0040c80f6503084d03141e5807036080c241681ca41c981560211014056000490003160190096034012540f854aa1a411005883c00c00038007a915100e540c00070700603402c8440540c0d07a44083d51041980101030803025004d104d1031101003040780c0201105031800d00000e940c640e40401078542c1d1075a6803c10540040c000f500300c03440c1c1d0040b0307400390041118000f5014420f20740420740000807032080c140b40b00f00c44000352513400703c031140d1a040b165210401e44158005101c100322414500b045040001c3d006143c07140903401e9a10403128441050f190b0b160030401c90a0900c512191202c8042007040740d009196400d180500c10301e00b5020002c400850061030404c2502403060080c01e4507280000700814034505194542c2110104200c0c55280c038108404022102c200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 945372491 1250 945371241 945371267
    0x30b1c050114010e0f13020907080906060d03050406140d06090905060a020f0901030c0318061b020703050d030c090e0f01030b13020a090c0224010e073b1011010507 72
    0x8139040341d0343d4007000741d038500801003d01d405204c4c00c1a1000c056126041c680d0300480c8c0ca5070700c020040c40e01c0c0c4950741ca4040b000e007080303000c0ca600d620340501182e4000240c45c01d841c61442c045802049008600e440703802407910004459140840000314050182c1c0508007441c03140050701c0096a80c44862000c0f4090f002102d09403034801c0250124a40c030a610009860701103040c0010109003a28a1000d40713409a05c0c11a20907580c0c0c80700780e501c080c3e043e2031170301001014402032020b182144c0e0b0f0603859505060f441070a143d1101c100c01055070080742540301600c03c11200341007501e8000c807030404000c001c0c4070581d403400044000c10504061011210580c903005025016900d2030055550010090406003c046000340944040001017903041c40f400390042c510071414a50402c00e0660380340720040c04e04000c1c410352203215010200880e40b81c071030318041d03013154001032041c24408482405000b01001d078400300705403040540e144c02c0354190040d090514000c210f035035213440c02560340d0741059507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 945373741 1250 945372491 945372509
    0x10060603050718140409060219110c0a120503120f0f01151d0109050a0902030412020102090102190c0f0611011505150f07060518100b0109060f030b1c05011401 70
    0xf8040c40a0382080c0740345201c04501400c009a00c20741038485008036042440c90209a110810994901580c88041100b0821130103028040c0c00ea094400204030007100d104940f10205c0c2c02c030010080c40024026643c4040c0c0c40c914a00c15032071f0100c222a1001d404030b03921085070043c0d030004100240c0da411810060109a118920810191340340d40882420351003055040100c1c02802180c2500e501186000030a030120000d42c403402c007480c0c40d0a400c20101d8481045a106101410b2281c3c1e000032948600f46990340841e02e00009030506407140c284d540c000300061480315000041056020b52250208010310008000d90b011000104e40202142e100d4185c5c01a000c040c644188000345e0024400c80c04801e148910b00b50b119540c92094030003ca6000030300481505071030b100100f0600c107418800e03202081c00c1140c018417800207032840d81c090040d0b00c100502c504d103441c0c08070f000341d001c8600c4907001401400f80405412800012030b458840c06c40f859403c0450140aa0181103101030603031721610 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 945374991 1250 945373741 945373787
    0x206090f0a12120b04021b060619033c11180105040c050c060403050403020109080d140a021011030109290105070804030605011d010e041a1305100606030507 69
    0x7000300ca00440d00b00c0395043d80c070740d0380014000340d40d05d078402005848103249880c04d1300380c1c00d40366050400308020003090049141e007891012006882014809603980160b6140802140014400784003400c3c010214441070541803510150310240d81c04809188600b140000340d1800c6014055000100c401c081114003201c0d005005620745500a840807001c28034101e42452010340c0d00e5441c20340140c50070360104000007400c0c001c1d0350307010741d00c14050f00514009101541905c031f0024400c1c034503400202031401c1c010601009451091000ca0f50340c07001c41c00d045c8800200303107040d10440d900a1094152151800c584000750041c0100c9003070320410b00700d041d40f40841d4250015030705e5900c00c0741c017102e40b854100408030000d042c0d84520f0740030340491006100c1640480b07840d28441001a0401d042d010051000c0100080360f0810032012a0540c05401c122515100f404407000c841c0390200802a0140343e03512001200b41d9400a4200d0b1b0b42954240401d8441c2d5005075044110354a024120038245 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 945376241 1250 945374991 945375023
    0xc0e2703280c06270606090b0a0f03110d0b0708061905030a0f1a0115090b0c06060f210a0b1003020d03111c0302180603070e1504090c0206090f0a 64
    0xc1d446640d010f407800d13280e9134401c1d002542140e00c1d4680b0703001c12a075150350707680140041a01e07441882e0304c1503800e6800140c0c65041585495148026200080c0507c0d800022405540c88014621180c0743d80a402d030038541c00d0210003e00181d000301e54180c0a0b41c8102034040380b0607a084c1c4038030202c1b900500039003804480383c0c841d04490a0a80000e58503101c0c3d46010002440081130100d00a24a11491401018a1060040040d00941d02c80055a80d042c094030440d680040303042c075040502142e0341c104845409000c640a00202d00c2d09001409142c03a0407200180003040b80d080107481226051030740c1c0d03902c9102c1e207907010b100d000182d00300c032039050001e0000b40243e2120026920200898081c02c05840003610000310394050440029008140c41405800c0b8107000008003c3c00c80d1894114540f82c08000d050320790440030b69104080c00300e010645520300100325009030415107003e02c0141404103000e591aa02600e00d0600c0f80b041c5003c80c51078078004900d180c04242d1140400b1f85000135 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 945377491 1250 945376241 945376253
    0xc1a0c070618050f061f0e0106050d06050a080102040f081207030c0f021009051806060a1b17091005071509031e0305160c0c0e2703280c 60
    0x2980c5028001c2c200c182c0303480049a0204501210000120001c003543d24110381c2a1007050307000c02078002001120780041c0217010419201a041d00c4e844d1130400d440c3d8421012290260045900183e08144c03880310101c0e07070340819001070059450f40d402450301c1d40d50f240c101a645130403418840d003105c8000c1c440000024418010486118014051031201d0745950300010150007a01e2000004141e1701e0404010b40d0400001c2071020704066141c18640b4503001010034814452044c0b594104080e44507540b545001350a048492550440322001d60100d0643c69003116901c101803591141000900c3c50381c1d1903102d8021540c81c0c40d4000c50b110480c40700c6401c0040034045044084060100060f84600b10015000c4000c1c0d4002543d94041118142409400310400d030141e004000c101b00c2220000204180c400d03803204850303650902c40301540e0b03013000c0c4000080b0300a080317014074104c603400c401d100c4600101610a100c402030594210000c6445541d4290010200100200704080b900c8008154 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 945378741 1250 945377491 945377501
    0x1170118080703082a12070e1008130506010b09190605041211121f0606080c070501020c0313091103010315090201050f070b18060105090a0e010209040c0c1a0c0706 72
    0x28903035208120264501103100c02020554061400c0182c000c1040b000e02c6c8454494075401c69124200201801420804601040c054408110621030950045607480110314045180303190807605403142942c480e42c800301c0581c003500282d486a1100d407030200007a13100c1000901156140d459207440d0528003100e0454030304524106070b07940c01b420106c8859645411240c1d56a0b0f06180e40502807903400341e02c00c3d044c0800346020303514200b0b10384401400001c2c0c2181c44d842c2c10260201d0301c1a1101114a0024003a125020780b00d0396a010105880300405d6082100b001a688802d409210b036a0409131180c034580001d00c03002d02510719218000ea588055503106600b2280185000c0d403628040c42c401d0005c81d84495800c0b1500407110040000e005190440012040c81d200d005d0328080d45000001480d080d0050909032415030b40340c914000c44002541240c01080c400f90003400143c8000a010b0421180c2030001e90700010b2128021034800c224100304c0e442058410456402d00b02c9030b849800c0144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 945379991 1250 945378741 945378751
    0x10090c05070f060902041103070f140c1e010f020310050f01110105010f1403010b060306011b15060312030615140d14092109090606120117011808070308 67
    0xc103080090001007103039a407800342d18a0042c039020450205600c103020440b800b05032440041c280a20034070041e2a84540c83c1612000b1510303004c41420060410f0908621500b070b843c007918495225440c40c1000e041c0070800c0c00f82c0d10075008002c25604d0b19144020b0f84021603c2078032020074034505022030b1521047c0388022203010b24000b00e03103100381004282165000c0c1c10280a18000700020040c90149a44141c003e10083d4001e0144048100119000380809001141800680d111401c810340d0312031702d40b0080a41206e841c540400406000c9001024140001c2d00c00c1c3c1c0300c001100302014001e01400040301c40d0203070f494000d0812048100c50081c6803a90040ea450000c011901c0c407519140101e45030085041c3c3c0d5404182002d5800301e141181400d00408911044402032150800110980d9101c42003a01c840c007240d580c403000030315288a43c016403200301401200104400c2d84220080d18501c1a25008000d681070f01501185584c04468004100100801658000030b00c1075001580203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 945381241 1250 945379991 945379997
    0x10204080a0312380117041e080307050909070c05100519060f140a0605040909081605060402030105060f45060f0105040302181f080114090610090c 65
    0x16498042e446801c2201880e480025185104d072140c449148960050a11442400c140720b2155491098404007400144040d10a40413040780c41100c005050301c3c2c2c01e1050740800581d640f843d105202500503004208400d004009510025541c03a000e01034082085401400402c02203000080e030001622005100301e10b01071041c03500030711810090181601405800082240c80750030030402d5424480c4108040d44607852412040140c260081d0407101075942603500400e0311103507800d08205c140703e8080e0080c00b00c0c10f1960a5800d0040c04200d040c000c6100300d000f40f0960b100c02c4100114480e070142001d034007010032002e4040030307900607840b2201030701c0b9181042404900801c107140a0a16115080301c140ea4240421400d4502540540400403007424010f017070a00b142c0100c1c0180410340c4148401e61803607000310345452200303034400c80b1502c04c01402903031090f15615418080c140c1034400c044d441790302c1c2012640c45a00420090310519034a03130b61f60000751030007045001810000e41c0c030b5028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 945382491 1250 945381241 945381251
    0x61203030f0a0b0d032c060f090d081c0606081b070203120c0a0309050a21061e0b0307090c0f0c0c0b030114010206073e0726010204080a0312 62
    0x11a0312000b51003013065000e61140d03980b40e8401500083c2c4003112118407940440251948801c95544000b61808035001081e10741d02d4804010100d0744100d049100640025070124400c920400d5101e180c01c0d1007410041e060000a5807404103591001c81a0f030a0401d59502e000d2840b00e1071a000c000c0c10f07485000908a07201003886450000c8568840c200d19011604000d030740109040c0c101030f1800091030f003a2100c40010f07140c1007011070040245180015007044071450102480180e0f0040c1c000c01c8010581103c1c0600c244a81c3c0004085004025000e03025007100010788580741d1054120004003030721920501c2d001c502c2c08581601b00d48008440c4144a000081190148080550b018040524824808190890002e49041d00003062a410024110243c90404166050880100300f60110705080804804071140100041c04d100c0161849280710014050036410b2104000030308100e4200588103404040350701b44e204500440325a5481051340b040020710031209900380030401040014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 945383741 1250 945382491 945382511
    0x302070c0f0602060609150d080307021e010c11060f16140a0804060624050a021e01051e0c04141804030207061e0e0405090a0b040f0b061203030f0a 65
    0x7034072a03002e03046440140e00c0038082129a04000d06e649400401000e0100c1d83e21545100140c1420485400101500c0d004400b06038011700801800c148806d008100d10200c403803000e8518001c0003500440c00014916905590340800c0203d126801070104054164560365059604903010102c40c0d08841005040390400c51229007a0014100e1178003e6954034590b414281810007e4522070f80000280c0b2070741c0516046e000200c0e450070100d01c050307828541d44603003003568180c0c04d1051541b03c03030004408606034806540340641c020b034801d20100890210408501c0003002d401e007022a00059001d40402080c41801007119801d540d0b1240100500e84140060400c0c4200c0030041d10b0450140c0e20070981400240d8201d98070001d0091445401c1c400e9070280000140001c080302000750080360780d0303404990b403070b4428401c0580d11a044540c4048505240c5000450072461120980b5030384407003408181c01d4504060a010402c42c80b4004600f961500c001110040380082c00c200707040c50759190054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 945384991 1250 945383741 945383759
    0x1f05031f0806040b33211509070603061d090309270114060904090809042d11040308031f081f0203041e03021002030a0501150806030d0302070c 63
    0x14421880b44c01c01c0c44007402c203a00c060310518105100d0040003089280004102d2414158940001204649994810680c180c50071141c003075010f5040c4160003804805240714903d5503045000b0000c01003182c001c84c3d52a00103d04644040c00ad60502a95070541500014820240035402c0700c18401078a00d001ba40c071001500c0e410f0540c10740030140d821040c3c0301c0c1c1640030700840c070750040c154031004c60120401e02c2d0006980744140314449128958070110403080c03017200c10035908006c40241040050100303984c10203c041c003002450040586c5980d44442844199000b886190030081d0000783c10903045981e0880d01ba0001000c0f00000ca501b203008440b42119111600010582031028000030b014080c0c0100c030805015895004443c010000d010000b03aa011341070789410b0b840717092407042681e103280880c103041000c001401544e001100384903100d1081d0748a68100d4441502124059840010688190310200d03801e5030315400c080c0c84c40410328041d030000d20b000d9203d034a08400ca940c645405d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 945386241 1250 945384991 945385003
    0x1101060e07030b030c01080f220b0405071e0f0b0c1c0503061008010807170a080a03140601020a0c1a09030a0807020109120b0601050706180b061f05031f08 68
    0x41c00002e500c50152004030f00b020301168159138401c0c6031156040ca010041180c641710b01621112901403030285407071845002045140020340e020361143c5090915080c503a503980c0d400c0c020701c0c0001c400406a42e5164410b120100c0c1100d000e401091071702c43c54900440300701d821180320f03a1018056030781d50800c03824142c201e1902c0303100da40e100e80e03840e130070031000780007031410881408410310118000510954100180010482d40701c2459910308a11680340c8031b00b40a4040802000c8510108144000a03095004070707900100c00c0b0003150b925504d88004a030343e0401c200c0c1c003510080120005101c16440340e5000341c0780c5500700091030300c1c210203a404a0300d071208800090301d103113402080e02400c640c0c1c04038070f0200030b000c101e108000381603540e16080f4441034007030a16818800c0004e040d208200098200094040f1240307018a010403680c1030000c40004200c03034442c400c00d5071075401c160300414407808007548003440d680c40703081d80e48001d14000c01120304103035090300310020030300080c0d100300030028 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 945387491 1250 945386241 945386251
    0x4121e0c0302010e0c060f09180108030a0f0c0f1202120a09140f01090b0307090b0412060b041802061c05012c0f0403180b031501020c0f0a061101060e 66
    0x2080030103111400c0090071900c0099001c2403d030000b580c0d80009a07240c5c0e054641443d00c1034070f900c1e50707003007000001108210403410314010191034000000b0207106c003001804501c078154075426140c940c1f140003214a031a06010042030450341845000100340c68100000f5210507500441d642458401403070070054028200c5038000924401d01404088039400507a40c0a82040d2410b1001c0803020001a014001d83c0c003454102c140003100152000b8801c1078600c009009208003540d0390343d1140251700300c09000f014103480302d80c2000c2034460542402d100b107101040c3c003c0005121480245c1c2003090030b43c00324041c074503400d400f804080d000c405c00d40b056034001c01a01d1044207003014140b064041010036004d484d6003c442207001c1091a500c40300d20294029070524040568626010f540320980d41070360000903c602c1c010040210b014125880240364032003d03000c035440040c01d64200002602c150000d41d8000c0d0640f08100a200c0c040c040841130b2260910011a102d03807154070403144c200044503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 945388741 1250 945387491 945387497
    0x309051507030e060703020d05030703060513090219030b0109020714010e01060f09020301030b0609041e08090a0509010b04030f0510052706071e050708030414150f04121e 75
    0x9452010542c00a0050740001c2c404e0300c8950410f2500d03103003c0e440e04d01c000f4900003030101c00000070780858403a07480000500401800b01002d0000d00703d5440080806000881c05480844150b4500b01001c40148044940c02521020389a0070040082c000c4e40009204661001601412140182080c01007a0a00038988000901145050715200c9206080d51140c80224410401800884c100300c0c8400e0303024405644482d42601c4525080d289802c60404485485000c0e107003140070800c505004001c0480c00301d885000c01070712107040180b0040c00384101c44c10b8032000c000800004a0105a0240303041c0610141c2e485105a11090001e54000b1600c0750881e075455501611007000c0301c60ba07882852155001064140f44c1181701801d02d04d9504060701d980604c5021000718035104404841810354000d039016101d0030107107840380c034220594030b02035560300440504403141c0c52020812031058112000c45c06a07501c50b0744030300a20340c400c0a8910100705c01d80707040e180040e00049401440344940c1d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 945389991 1250 945388741 945388747
    0x2070b0402013005060d060e061005040606020703060b0d02090709050405100305061f090e0309040e010207032001060b0f0a08180c150c01050c1902030a170403090515 73
    0x1200040007030000c1a501d07280d01c0762041d000c0208080d0180310040c0843c103030381c000501e51204070014010000c00f40d00100028141028403415100c0416200d004101009075428155150f10800041d14500d000f9000182c0c0b0800c400c0010844d00c3c4c01540c10800c01602000c00c04407160080381004004650000c0402c4d0014010055030905100791588000380c0a00f0081c910300f9591515294040a0105115000c1d48991925081c04040c50720000b40a00c6804110301507510480c25140c0c1c010013041c511491030500e00144841040c0220380d41e95605030785404d020001e01c8841900d040282980365034940da01c490100301c040c41c600003006070280c21000c094841021410040405800a220320303595841c6400d0b07080504070004180844034008c45a4030b007140c041c05481d10550050507207072400d96080c4010f005041041000a00200d011100f051003c0038a82c101070703a6034410000d0000001d5540b014401c2c01e00f40302000c40d03400500c85d00c0c2007070f9076076a01c1d000980c603002c81220580b0201400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 945391241 1250 945389991 945389993
    0x607080c0706080703110301120302013c20030c09040207320c060d02130b0a260402011202071b05030c010207150f09080a0c09110304050c0f06040902070b04 69
    0x38900f1907000b000e40c034080c0084100d00e0800c035118001031040740e0104ca40d04140c8402c140c001c0d00f140b5072031607149155003415030303065800700c0340742d20a4040c02001040410b95480700c0070480c0285610901a091a11080d00d00c164144205a0004000303801611003480202d203a0b81c2d03280010301005014911040e901c81c40144921180f62485907025000c3c000e0002500e819500821009800f0408603a55130303c5000401e00a0040e1055804604440040c03a1001c01d58607460f9015241c1c00b020390785c035074003220181c2c80a80101d42e40c00c101250355840003030004005601c6400e110445a079214809810400076590341d01c48800342002800300c0c41c1000300c0620160604100e9041e80e40e200f48010186a85440440301800c4c801e24001d10030048030111112035280034440d200001c0c2004021604d05482c039040c000c2501c42680550100ca44c18400141c035410f4120082e00d00954000006d40504611482006259a041741c912504881c0500000031104403900c05000140d025642d490000c0c502 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 945392491 1250 945391241 945391247
    0x331c0c0306201c18050a080a02152809081303140a0b0103060e030c07120308180303060d050f0a030201090605071403160306030210110106060e1e0607080c0706 70
    0x1601c0c4070740390142d03414002500c41c444503c0d541401c0c2c3c0b900c0a070000358113204004d030031541d214954010701148100704a1320200030401d0002e24400020b503017940e04800c8261301c20020464181c60b050240c00341c0c03030200554516240f120300c18850350b560340081c00c2005070303a401c40c60f070308001c49200181d04915400c00c00d10901c01d45420600c5581d10151015940c80e40d034100d078455042c0000390a4640d00d007034803c0708202c10801c4076451140a021258074598507414078448a540c4c074411000038045001203003800210404110781e03200080301031820740d501c0d02c0610180f40041e14060b1000c0c85554030021003079005001c1380d0b55550082d400440c1c0c020705414510705440024045408002d80450255034125200c5c0540ea000700c01076641580b065410401100901003640000e5401840c085102c40016003050b201c0c1405e250901c003d00825540d1380003070300c2d50410001d102d6004800780d400080151422038000302c0b020740050070a800c14400346c5070320050780c01503001513000d40d2264605015007070b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 945393741 1250 945392491 945392531
    0x10b090721020706111303031107050603040308250c3c050f060a06150f080a0c0c0b040c1706010602030403020907020a0f060203331c0c0306 62
    0x40305042041d140d9000c0c26044800030a11148016515800308142080181c45c0c2c2200b10340c60821a501611105c110303800c02c4e0b80b040390f0b100440124503000702c858545003011415100700d8100070120360031551191070590308600d006001c2082000c1101815030110820602003640762210788c1d46540040d06860300714103a4411411142000300c000c10703240240c83c000c0705500c00b00404085013040c8000e613032504610304000e01d61030344030342c1c0245d00400100d500c640d80400200c1c1d99104003002d642d45082401e84070068408a07080c00900d4000024609030032540080070080e01030320f006503a00005444080d80004281c4080324088030243c020405c040a84214011440c41d420187c449035142110180d600c0c840c07444024025040c010009448900a1004042e0590010741424028540c2e281a1000354001c8070b40009140d42c0c0e942200102880c1540b50406078184000c2444400b44141000003a1032110302c0200c1080740c2c981c00360002412141c021005601c1b4031800b180c4440481d0000000e55 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 945394991 1250 945393741 945393751
    0x10c05030108070b090a1508150103020c0c04020306314a1b1932031204031e02180a0216030c06061a0304110316030302010b09 56
    0x480144014090010041001011070320201425075549140d900415040070780e50b030010403000c00d00780c3d90400380d0760800c0344c26129904500c400450380d50b404005404a000e607500c1d42e1002e600c14043c914080c107165000b1900098010900d0a90003c25142c0c3c001c0c00020003203548005082c02c0382504407044a01072500d40b030321845800300e031580f003043c2c803852003c1d4400300410410624507401404c01c800c0c401a408904000f0040d036483c21440340c0c04e2540b292008034214042c03490443c0d040110b2144070b80110580c0c84800d500b0000f146554800c1c010042e092242000039581c50314080309541d0704014100e0050f0440d1800c13620b8900d10708040042e50b01c441944203020b00141050001a9201e10404c890303c014003c0006150712130402c01f100a000300300b001601005508456003d05030442d0340d0b01020781c480d034418407001d51548120440314801c0da07162911554203001245c00110764503550a1200405400c0310601c10411a1031828030f59580d1040e400340c0d640b030459030701600300003428079405 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 945396241 1250 945394991 945394997
    0x90c0702010203070623040503070c0f05060a12150f1e0e06011b05030408010207061107050706120b04020f030406140f07030e120f122d270f010c 64
    0x1080494001075240c2c802c0280c002c0805a0307500d00081405040118025801451003404103546498540540c0c0c0e5030080d03209490070300c401c40780055a000c8004010059901c06001242460038a020036100c801c000b0650825980e1159103411034100710566003c0240f0311050700074412813820442c40a011403038165424280450030080c42403a50710160710350089028a02120080c00c0c05034914100c0018050080983c000000c0015041c0d1054010f03004160061004011220402101403424852442c00800c0c3d078000507010059980101d580000d0340c02400004203822000c4400a001c9070b0010882c08446a000300030720041c8a0746205516400c0399190540c2c02c20f00305140d840f038002c0c000034120400c054452400311394083c41070203455030f4211b1044031203442d0311945402d048590411981e0032841020b0800207040d0051043d101c0c0496140e0a4002c203049402841c202d9855000400390312481c0c802c41d200101f40304204034440044902070029042c03085181c4481401e4610143c604010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 945397491 1250 945396241 945396247
    0x9030201110106030c03030e1908030c010b0d020907111002032809020f2110020304122105060f06070c0e060f0612041109010e100e01030b1305010e011802090c 70
    0x80b104d00f0040d081e647c160401c080c48940820000d684203d40d1a44103000209114001426103000809005010503402c02809141c44030420b00c08006101240a07510001107004101100c2c000c01c0260340c0e202c402405d80702e050400350b0984050380e03c20343e50070b4000305100054541c81b008110a01e644a9120842803204060700d03000070f403c28000c101e41500c925150a24040040c00b0a28150320ba2a80343c0c065408a02130300801e50000e400854040c1d0b8180c840c1a101c04445119100b5059092001c0115070740c020111124200100340c020403da40258030b0f404900e080e42d43d40c070003500e02d6601c07485091300c0d00c9040045045017544c01804140c0190b000c1759040c500d42e40c41c501501c24083d22480b80004954590805020b41510b40b00381c01d4204031110000302d1426955560248621703403072000701d03070050f955031003230015050300748409044a030030b24000c914442103030390310400034500500011a100745100c682e00e08407820703400c902d03040001001c075040442c00c0601620354002540d00740682 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 945398741 1250 945397491 945397493
    0x1e0d140d170c0901030b01090f2606010b07080304020d0807060e0d0f1704020406032108060f0a061115090c1e0f090403050d0204090b09160906120e0d0903020111010603 74
    0x10750148803c000e040c5500c0d0300c400803c59101d6041c0b48000c1c41b0001903921201d6603054014841407a05451881d101100703400001c0c1c1301c10001d4810b04079070300a05403074030707040300e40c0c442804507000504102c2e44120014581c0b40420900c0000d44803141c042c100c00039580c510191400e1909610328500d10512a11200c2644d089801c01002c041d8150200c00130f80300d0356036500c00140203010f640c200174201b05a00c82903c8980e06e040da4414118240b940340e910305602e40700e0070401401091600f1590041c0030500c140503840c8148040303044070542100321242040203104514030013400312000c1e0482e40c40010714a0042c9081e800c402456000e42d0707e001c03a000c0960700441c41c601b500601c05809528440701040c10940300c0c00844006900841085441d5a22032a17900080d040704140c1e68480c80f100e41c04191100101801224546a940c4844001601e0414280c0b8401c90810229032081c0d66900d241c41506002d1024840f151036583e04c2c180d00381d04604c0050082611070300610500e07032504400340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 945399991 1250 945398741 945398761
    0x1c1107050108010510033b010b060301030204020a051b01020306040612020901090c050408120d270201030c03110c070f2405280c150b1e0d140d17 64
    0x1034191481900d5107000010b084101b60003401c00c2c0da8000c01c0c0480c28900d86003c1d4144004098120318a40c14650f4540603044040d500f030b900020040c80d0300000401c010401440c20b68000e101004803410810700340140d11202c0205460800344580b0181d4000081050503e40352003a440a000801100c1360b094940741c001c54040d14050245078140c035614848404039a008005481c02070000c2401c1700e440220219444c0000d400951010034254103240d0300c40301d0300d0f0340c001c188055614031203600ba2030007030190011800f80042c64a070304189a60350504e90b1100e0340010091011220b4440240075140c5880b903c401e95824592043d50500d2200320031203e606025404440c6101107494150344a0031090000d5404a09000d01e000020250b80f0001c1e24030707a001210034002d03a00071940000740d01d04100241703040d5003c00342c01542c8071000c03100c2d85207844051a00c4c00400d00c000741c4003c5912880740d90b8400000c19400780349140e98081105001240d520000c6031b48200c840740c40028281c20556021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 945401241 1250 945399991 945400007
    0x1080f1203060d11060a3207020d1e05062413240e0916051018081212130c030f0311030d060f090e06010b0310081c11070501 55
    0xc1ea1003140f039500001c080c00812a480031200d40010205669000b0007000076040300c3c0d441030240e6071803124000048014902c9515215000f070200764080c44c2021541c01c02039412a0303080116440c0034000c4025909410003a03141c40300d240305400404c0103003000c039030300c051000115074402517600f090100400e05444820703444110034818000410003a80401d80310208903030310800c40c203003c4043c40d000202030886011103400754420701d0545040c2018118810341100b00b034050281c0010b68401c000754100e205941c0740ca1000b80c0b601190015903103c00c3e11608004038680320303141004001c1141200f0401441c07169400c2803210780c01c482216a40d40c6d41c1b09030403049100250080c02c0410900c024580a80c9228070780b54004000d4960381d2040001c14001085140102803078901304d56004a20703407a403803164038522403c000051025a180c40c080c1c0c0b0982d0b1004000c100f42c9521240c0005424100700001d4440402c154400b03400e0038000ca01c01080c2804c218030040840e4424282000f050340c00400c0c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 945402491 1250 945401241 945401251
    0x1806030b090304052d030303040822270b04090501020712050c0712050f0a20040212010b13030602070303061d1506030705040503150103050106062102091503070801080f1203 76
    0x31415503110021141c03000c0c1c1c00700c1c85c207141c06000010400040082d401300910240044968920141c0340c0e4580d169440c032200d02584424003500f007122a502e01071001e1110074421800c0021030102c4400c0049400e40d907212104031400e17900810020100600384241d03084545a6240141c02d02c40c05040c0e00340c0c0c2c0c0703800e807080585900784440c203c42030050601c00d12042060ba5012a22140c10518240300181c5200c8018200c0303940101828980780f9040c000c40790040042c0420091076400c10f080c44803558001c41103112034668942001000840600280c002c25020703813000200783d4600111100440308105804440000010030807101030940c000000141c20b09417002500c030b540c0e100d02130b80e40d481583c21450341032194110710405c140503816031a041c0d03480b5034001c1c80b81c00e540313100c1650010500c0400c84c0b404a030035490b42c104058658040c040c0e51000078002000c95445400940c550360050b03400d44001081c0c00b00600c070121040001140c0980b40c0c2000700503841101c10000041d000c0a00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 945403741 1250 945402491 945402529
    0x513080405100c02190906060512060f030c03150a060518040b060f0604030c0314060403021509100614150c0309130f0203011508060405070804020d03091806030b09030405 75
    0x1450541082c425070541c4003c1d030b40a414041450403000021034070740c209200b819811802d24101003040c1b485101680e8020409005003410342e1294000c2005140742e40c1c400942521461860888555040007400f00480d005801038440c0c3c20200003410648815800c250302602401c58642104d07910900001d42c0250440b00000d00e60304c50700f00042200446803a201d5000a02040c04010f200903c0090022039100e400c0985c058030700c4204003500d0f11030844010b005a08001e0b5001894a251691194821614400e8403000c101e40502401152a40e070410990070cc12203401d08890b080011030452220b141101d914180420304132060717900d2040c13003d518000d0548514407260151036420030a5860740218096440350785808000f070000d004000709600040040010410506081c801c29028041c02d5031038a00c1a0f50b81c2c0c0900450b003a030a07008400b000b945d00c1001034002030088a80c000e8039041d2402040603403a505000405000280403c000390704108000c000300ea50f6240300c8c16044440301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 945404991 1250 945403741 945403759
    0xe090c03060d08180a1e120f0c1211150f07030e0a0e061309020a030314090a2909030703031b0b010b090907082403120c0a060513080405 60
    0x30022078440034681d10002d01a8030041940c410460907500c2844c0c401c1001d4070003100c91503039507445c460302040f00c3c00311149444010750288110403c1c0a010140c0d00d0242c03100c95500740003030361203880d03d030f1065200014182444c0002c00400c1103880c464040e5400c101c5170100c281111914040381d600c181315031088078000005a2204150040d0314007601c01da401480d007031500c0d5588140c1000031908a440f00e10403408400141144140c1c0c0c405c0c12820b0380c02401c0c0152443c1103940980d8001005880c1c500b40203400d001d180601d0341d0703c40e0740501800d60015844080000030540e009100e44030a1100391591083c000c02056403000548c11080302e4051a0411417030490b00107419800010080142c4076000504c0003180360043d41d802020100d030169032010103503135a01e400300e41d890340643c0e1a00e504034190410001c5440c000316014107281008060701c480d0050040c4030682c1d5400702d5010641c9800071144501800424802c0541c0038a1480014400c003096a4a90f08107206074080c0600c186556 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 945406241 1250 945404991 945405001
    0x10e0102151f090509070806010b0c0322091a010e0f330a02070510080118050411030a0f021309260d020d020c060108070b041403030904020a050703020601060e090c03 73
    0x80c41d444070040031802c038200301d1405c0010910341c40c0c003003c0c040d00340c0070700c1460000900c0344200070032039241010b00300245052505000115240d801c0c15006072381401034400d004543c010032840781c41d815220940003403203032425617000985030242c02d4174454400ca800e0764202c29a900c030004080d0040b4140b01d4000c0e1405042e01042181c00800050002541310100d500f40b012500000c20b031080e501d0845072001200310030b400407260841c003400b61888041c5100d0900c1860400b90b00b00c3c030f82003403103041043e1989407214042840d1118440055076090141c40d802c40540c245184401501d18150006000d1078110740c60302004800548003000d12401e01c003460301c401c04a4002030700c2014220080c103550b00c1000e150100041e400c0707030043e1601c50045000004003220700040304021940035101c6141414501008406c01100c40c1108a806000400030900c046d60741d031008049541c07881d25130b1500c650060074024a486c2e0140c201200b8041c40c1d660506041d559100d40310303031108883d41c50656035560 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 945407491 1250 945406241 945406291
    0x10050d020409060e1b0d030e040507030f050703020d0501080a0f02120c09180105090f1f06050301060f032112050a1b080114010503060f0f0a0b0d0605010e010215 71
    0x18407000a42040c4c540314103001003540104403a040401592404002c580e481c004002c0001a100070050205403005107190180c1815000315520031058100000e0f42110041e8001c25103108490f03207000a40d0005035143c05030014800c00b405030050302d00520100206540e0b0040740d446c88040039108803036240200c0813014003041081d4082e44058102040c03414105890f400003111803c181000e9401c000001319030f13000c00038400907200b4031301c40140b0500030482480190103500c1c4015000c1d482e1124408130751910240141c0d0000d21246901103822450342c00d01e140580142640d042c03921036440501c01c110340d40700c007107181e01c03548035400016180c1762109128012702c1e0240d4245000707020301c0c0e03d041d603142d044034200341200c0c0702c0c0c6003006884816400450341c610040b0b801da81e0001e0044540b480504056080414080010300380d40b0400b605c407200c0c0c1a0360340201c10219025511868184880e5903c0100d184a40c0800e00044c00c641e11940207e0700030800050a580d018511038a072041c03c400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 945408741 1250 945407491 945407501
    0xb1306080402060409140f130b070509040207060608030d140c07062c0c0f01030908070f050c130c02010c0c0809220f060e130f030302031b1209100510050d0204 70
    0xa800c0b81c1009003080a00641b900818105c403e003803580c1901000401d1418034018a9019507070008510360f165462150644d0540c1100e01c5250300702d0340c04d104e4080041d0017403181c00d0140a041c0010f545400002e0100400d03126141e801c2c03200c140c031a400f44041548104103039035025500007004603034941581e0521003182c240c01d00007001e400060310030b0010303180046500c00c5030030310a48200000145041c0103600344c030450100201035900812039000440e500349043d521240c030490aa40c0151000e10018224203420b00b10004503550301d624140c10990244104907001d211414a0500e000703143c0c42e81c90180c042e1041290291050451542a01c144201580b9204241c1c078410010380c01c3c580080c80080200340a00107100b40d801c80840d00b581000e00c01e01d80c07400c2d407042c2041c01d04003003541c048010b5000941181030010003210328400541c40200a03280c1040d10100c00b43c618503002500c1480c0910300c60711001c10a10305410f008601074030400d00000d4400c1520f07407030f105490904c04240101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 945409991 1250 945408741 945408749
    0xc0c03070c0e070e1c1b050a080f1c0c020d0203070e070c110604080607050a140d091110022a09040c0302091b03040f140a1202070b13060804020604 65
    0x2041e103503030200d940607500c0710050140303030b0035600c0007008040c0c0300c1400340e50f0350707004141c200240404400c01c00090340180400c05140c210b02d9003000c05551940800c10740c082603000180140c000000c1e40c86100420080120b00602c60004074201c40040080544460b200b003001034041e5885074410000d549041010728028081d1480700d64892501d01001410210400000c940044604486c07450701d1400c4810b40d81510140c0015145507122620309442a03070006808609101145910080540c80c0801500c80d1710402140407507001c01d00e152007201c4480343d441d50b902c034024118029480507030000d01c80c4842140441405c81e101d5250111280e000c041410096000082400700401c204a489032202240e100303a4508596071030300741c010001c1d050300078048415120b003440024041420325184281c1140100c58030081284010180e601300380b054681980d103050130b10912072115a0400804c40282000c1100600b0b240240b4000500005075108880c00c2204d8503003c03c0540d0381c0c09049174010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 945411241 1250 945409991 945410003
    0x160e01200a170a0219080301170703060f0902090601030c090527011706070c0812340905031204090c0e030d0f0315051305180a0b041104020a05030c0c0307 68
    0x5070100c2c4424805079400490000c0040c0240d0440b9404402000080c1c0d101301c3d84004040d045a0074013404584520309481d800e2003900c1442000008504684079800e01060541400300c1c1081c0c946c0140082040e0181840d410185043c01034032440c0d0303024216205070b0390121540f0500101264840c0344850807012101e004107000b030000903a005a082c00700907500da500c0c00752185136840b05000d0319080002c94001e440c540702000811030f242150251294000510347d0100f4640c46e00c00308810f0408440c60312070aa0b5528020513148180e00f02c04600010b00c8220010904410f005a25400398000da2003807100d5140ca480703480306803500802c40b00d5588100501121000f50741c0d940010f0042141c94141e0380881d1074500030317500600d103805000081c0c0f11302401482101c420358510a0060000400306450b03c140c028000c03604101c180000301d512030181c00585005d040a0806004030104165940d216600c10001139842907001003c0d6617000c6581e01c002c903220060318040500758403c1e0f00c2d005001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 945412491 1250 945411241 945411263
    0x1051902071d0a06060906120c05130e090609190f0f080c0a03031812110a0c0f05040e0a050606010f1803080a020c040608030d09080405100503160e01200a 68
    0xa18602c4074851048986050a010240d5103680545079002c06000c0c0000090014002c200f40c03036400d07004a031a000103031406500d046050200f1070703129032542d041085064103020501403c41810407070b49401c04040d0000d4407014407a40b1740307803880014020b070090410800445010a203d003490452000d2034100324416501c00400150945860000000f00c0109290880401d11035213528007180086c0d600c0019801e02e150201c0094480c4106d034441c1c00800d21031080c45600144a11509400400e00210008055070800013040141c40c082c0700d0200281d4030521074600825000160690421020700300302c12030110214085a96006c0f5281211041c00403060010802c4401c0c0c2c01843d5900c0b10703500b991003605030601088161000d51043d0b0006074001c0c840c024800f8883e17031002c02c2c02d0b840740180614169a0348045094100546401804a02c002c41000041406041c01e69003a110768a01301c201c507500c080003c0c0640e402956140e24030440302c0c20a400036282000040610b41c2c2249603048 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 945413741 1250 945412491 945412529
    0x702030703030203090319030807080a15091b020a0f08070f08130e090d08450c0913030e0103020c1917120115090302090405060708060f0105190207 65
    0x513503640040100ba020384102e20804a01003c0041202c00e110b60540d40d444298584400480301010040c0c240741c0e582c1c2e034500c00d1041e003c003800d07141401040d06500100e08401544c0f0850340600c40e10350581c0070354010b80e580e08005410380c17402c003070001c2d840030388a40c45203c5401c1400e1003a0004000501d0400e0000301c8e864441c150007100c50403980390054205850f44e90901881d1504900030712940426a14000300d1f00d6003030341c4580800b00301000300b070282c0042016100340310745150003a840b0f2041c0d0444000302960785014807018244020544600c8210b00300800c201c0e40100303c00001a04114001c801c269240c2c3c031070740449000030342104c1194010700080520080e013038840340080300e81001c2c42041c0d00c1c2c0c4143c100700340d81c023980c400f00710011107030f01c1c10f0012000c1c1070700c038a075440400c8441c403000320042e0742c0d02c0b84050181d8011030040000d480d01100203000d0120140146120f1180043c1e514101d130b9204084900300102c0303002c882d243c06081c0106a01e400c0b000d8100009401403035600300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 945414991 1250 945413741 945413743
    0x3609010306140c07020d034e0506151806040b280909110c0d02061605040b07030c03111b030c0d020109120c030b010e01060f08010f1a07020307030302 66
    0x1040749401c0d22042c00e810348400c0052003240c460b0b00d80c0250806580700490b80464001c103554460390142c0b106034200300b8018500030340807200c21540e1942600d04654400c400c92000010711481d01c2680c0403c2041d13051040c001582d401200140c1003d103a80010440c1d4485008402507018207005000c0c252203688900c2410340c0d580041f8040402501d000e0740b043d44030070186a14140001b031a440b40071060b428011280068020601c0419a008013000510290b102c1001000010704282d8060415420498851054100398032013584c2000300620040c02035110000c00c9642c501d515003400c3c0742d4041d103494103440906a00070450014001c0944521640c01551a0228098030440030364841524503000c01c80004956480039002540a40041c0010000115034903407440c011034404080e1541c0750b88515100500360030200c062100000100034180e0850748207404059281003848242d810420643e9603100325114441c80c9900802d007e1420200e07440846803202c0e0003509480016890307040203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 945416241 1250 945414991 945415001
    0x80303150111011a04090602041503020a02060106020307050d0e03010e1204060f0908070b0a051b070302012c060a0e0a09060e130807033f113609010306 67
    0xe2030100b0074000909800c1141072140603018400c000402020010aa041c000105256001190016820000481ca420317815404072030001280d80c001d66200310688000f4108034060f4001c50555200303020000001d540800c2501144200d49070000b84c415030900060f001d0401c1c0203140409000d030f00a2405502e80f220010010303200b143e118550750605807982201c90209601c075040994015117001c1c0103505410340240142021440e120381000c140c2500700480c40340a54000c49035500c8a9000c008658110400501e1282c0303400d03034182806603d807012001f0405996205101c0d00002a80c0c444542c0109a0190011000340c5050000d0380c4a0f400e0100401c000e0083c418030b001140e00262100410343c01c61045150700801135800d254640e60296800c0d0306403000503644540c2c0404a21003400390782e08106e86106100d038442e000e103000c0c0c002001291080341340e82c01c501d541049810407203411070b0001d00700304c41c2d080e030070140716031907004440e1905601b010b905500544240c000014840c0d42e4000e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 945417491 1250 945416241 945416281
    0x1a0328050a0e03040803161109011701060b1216050c0109050718020901120b0f100f1727030705030c0303070923010305060a18021309111b0304080303 66
    0x2084882d102c4000b99960380554442e14040e41c0c8200322020705130386000180140341e0b100325001004e2010543c001440d2042c02d81292086052020429402c00c109019403401002002d410743e01d0402d009102c2410514024070703603408200000710018115200c2c2c003c0340e8a8059007002080000c02514000351109041d01c15061002d08040c00810443c0b8144216075411a05850344034150b0007600b02440908684014103500c500d01244140c001d13161480c6c1943e00d0710060390740d0380601c0c81d01000508100749424055040c6425041041540284446801c1c0f0241181d910525080300c20902341d45540f04054006141d400049440c3e83c01010000107903010790075684642e40032507190500350300740c40c0c01440d0034803107880b1030025081d080d4001d80c4429080039003c1d03c000400b41e206c0d807800b039040c40148007110503107070300140121910000074811006485a40010700034210000340c00540340c01038000c08040c1000f422980d40c0c01c0c0b6000c008550007401c00b402074903140c0c5803081c10b94030200ca82c418 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 945418741 1250 945417491 945417511
    0x210905031b1806010c031b061d1608030301140415030b0403021509031b0a0210081b04050a0e0c0408070308040e010806091e010605040f0b03010b06041a032805 70
    0x2d84468080708144580b0490060755041880350058400f1200c1003020203400d04207407041c0c0300880c04142ca9000e907000c038019950b1503070020342482c1070312890103130b062203a4803071300c05000010300a408021045074110364105058529580a24001900620427002801401c041c40600003040003542c045052140340640c003515420501c604180704000021504140e05070010000c0014040f080c0c0d0740140c04018240444030000c07980d90200d442c189046c8440300100b00302e0410401b2610300074455a000041c61940703103090501e4070010991074807031343c001d210301100f0082c001103801c10349105850082801c0021039603095030713a0600c985580e00c6405407109241002d400454100d0000583d14002c54010006204003100c40d403072403040c03114420b2840599521600005400c0c3e880d07001303194410700f0024000401500380341c105403c490b031620302d4501030a014803040122080d00c0c10b00f940d0b125034411289540b07690394503092044449600d8004800c100842c0200c0d0f440070b05510181c4581803c3c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 945419991 1250 945418741 945418759
    0xf09150108010605030c0d05071e020606090a0908270901090f0c091409071101020a020106050301181a04020303120406050a061e03170408030c0a051504210905031b 72
    0x30f80115002d100488403a0f440d482e0400076043d0391640c0740c3c03105a01c4101803800300d03108010014041c0b0010007010401c00103030f101400f44032291800c185416041140024100078608150f910740b0910700940c03010740c00f81c2c00304403402e0b212482305041c0481c10b648014165001581c40d44030700801801809075a99040340b40103c00c130f100364001d43c5040159503291700c01c110940d4140342000007006005107204100090700b14000c0d4814000d0000d00107251107600045491800c00d42811b00710307043d141e00c00c0054466200072070702003905542d50015021a00462440c16511400801d2544c801c1030400c03c008820f980c1000140483c59011900940f02088144046550b0b1781c510594072905021000100e40c200e5010800140d004030b912406d81041303030595091650b2204144e0443d0400d41c02c6060b1600f00c0303003a400802400344a001c000311107444040c290340c1003984034044152484528421045141d41c0c251000c1c6000b018035400608000301280c41040b1041030034825070010b481d1140c0648018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 945421241 1250 945419991 945419999
    0x10914120304020616140601171c05040501231824091e0316030b010602120d0c031b0315120213090f080a0201050106090602010b1e0f0915010801 64
    0xc5900031a002048141005d0164000011000101c0011120098600e85d030804802041c028035000703040d905040f80c0c05200c0d81101d00d0074202c000000e5080f03240d104488050300c035000415030781520021320b8403250420040000d0007610740e0070741c1c51a00140c00861024034205a43d0410006d00074103070750036070074a851170041500c9031241d003842440c0b00400380404400c1b803c116072941d084545140e0491204451b00d00420300b031003000c00c520109081441c1091040c080c030b40c0c4600380140a03a200400c1603003800001c01d903060140c0680c4280e00703038442c8052800f66100b50007007490350711025820001c2c05002d12002d030080002c504c0b4041106491040050200c0f0305e41d1981c101c0070f0b000b13070071401303800c0030710340410000c04180c9030407205482c0701d0300d0800101702c0b01d0020740001600d9800020702941080800b810080d0103034084802c680c105130384070180d51100f001d0503614030340410301007a1101c008070004a8901c02e589200d50460301c080204091001260b2009980707150a0f01d91851503600c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 945422491 1250 945421241 945421273
    0x8010c0f11070302040b0a120c03050c0303030702281505061309170f040b0a0f1704030c0b0901020c1222260309060a050d0501080705030d20010914 65
    0x4100c03168260b900a21410005400e00b41c0021581880090241c840e094641c18800320b150036401c0b05840c1d0000d88101442008010092045c0d0294114021030440c40c003101c00965400302518902c0c01c40e60411a0310f40015400040c00c03034039a80c4040b0700304805803a0a540e400030305003212024414102c0013021508607103544104507200c1c0c0c02038004080b049c006031403100c0580c0004241e15070004104400a1800d101c034010340b100340120303a1108200a510207008041001481880a07491221018000020340003400c09821a60020581c0e00d01e540795450280240180114103050780240c0340b01c2180c4403d008002c00e0342441c80014041e01100c107682480012015001e00101007454a270700c00e440030714840e80c282c0041c0c072610482c0d2a02a041d000303d80c407030b041051180c0100d923012400305c4400c41140034a50240011100400041d8940400a42e4800c00000030302e080c4200140d0025400d03040a880c1140441020024441d10304d2a190100300350158071748502c03250194180079400120 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 945423741 1250 945422491 945422507
    0x90601030615051b0601080312010f0f0905040c030c0f23010509060706021c0203041202060702030a11011b08010305120c0a03050901030b09100602013e1308010c0f 72
    0x40c00760702e42400081040d41c01c2e540e50380190440981502942c03180314500d070040283c14041c144640c017071500d03000585e40c1c844018106810464215000b030400f07022a481c06080c28040b41d101c048041034035213460500030210303825600702a198010440340810700665404542e001c845020307503248891241c21202c240007011408403140012010005031072946005006000030350700075400185440007611304101c0842c13820002c2401160084100b0043c001a1120b44090611600180107030b0324040308001d403244290158034003800382c60304035401064800d60001c000e101d01c01c002c880d8030903019207010345007003400d210846051044481101d0b43c0a03444c0c1c10f030f13849465200d00610b03181c1d002c5d0741d0540e40d541000100034101691910201003030b41d58401c82c10302400d0119107100c82142043d000038207681c05010310404050380580d84a9895981d0240b80d031040c20a1041034035140494414100c40340f2403400520043c12002c080843d00c42d02c1980600345208660b22a00b5092941c440d0590702c0304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 945424991 1250 945423741 945423749
    0x601110109050a1211070603151d0109020f040b030c0706061205102a0e030c010903020105090904030c02090c03150d020603180f030d021306030603120c0501020d0c02010b0906010306 80
    0x3c0c02000310f4200140d080d5000000911443c2000303070b210001c00300e100d0302d00101d80e400000001c2c0c90b42c5585034041074000c0341d400035040046c0340c0800301404042200d4100418401c00000d1070340001c0400101c4646400c0c0c4000d0b0101140c4965607080940036441290800c800039a00c00c2d1401c034000a511025520165055034003a0140c440346426511000040608060f0084205401d8030740c2a60003204d2140505056526150f0400c1c41a0300d5050514081c9507400013814081e4103881480541e07040300179200c1d040c00032180202c0940d02c6280403600000003600013504813241c0400d0080c0240c0c07107809944a0748101c8050000500d45408008030b0019120019400100070000324200c900b180b40c8514402c00c0b180122010300010341041e51456214140b00200543e000c10b29000b042c1080390075100038146441c0c28820242142c50300100e0221120f01381c010b012041055404008080d0142e51007180044001c0000082c905000f9018140100e446842205623400080c0e1030341c000e1052105a03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 945426241 1250 945424991 945424993
    0x4030c0f080102131403071d041b121403071b090b0102010501064104090b24210408040315050f01060c110a0306140a0b01020c1e0301090308060111010905 68
    0x340b5004c04017841900b200c032003d070035005025001c2101e42c251401c40c031300e0007060f01c900e49280c82c1505000052a5032041d0007017036480030b4101040800c900b15800c00074203420100340400d444450410324a1445070350002450401e4800c0b04008100807202c1010440d0b00b5030b4020b11800300c40c24012400c8034424050b00e0007040708a414100142c64052499500d04002a0f805081c005275621300d05075040c4041020140e641e001800b8840f0b54100c0c01041c0085106031050b40f03e2000c80d481c0e6000c0004e0361041e0800c0807a01044880072400d20701140c01c48101c201d0901081800c0a003031044680d400b90100340d4145019140081d40089240f15542c4140960040c10311185d0918100301d41d0026407034415070781030002000440c071540d942c003025401103100b00d00c0045d081c1010320350b20b25102001400e606000385010008181642c01007a01c0c141490110780e0103080e846000068880c02c802050216015881c00710071004050300540d03100c5c06600309880f2041141c40300d44080f4243c1303a46034002081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 945427491 1250 945426241 945426277
    0x7051203013506190b01090b0a080c040f030c0f061b110105040314070e010b0a0c06020d111c241701140a09120507050c100203090604030c0f080102 65
    0x4010040c4004101d071240718500011a60710710102d900d40380f01604c550b036200c16103000d00e40440245200c0c00d800740000b820202126072401d04c1d202240c0c0640300e055003d1000420029480b104c80104a9016052010310040004e07140e08000d00c00c440240169000221120f4001c216503024400fa400b0004180c405030030888516914000070f18a0070240e6810b205081c0000300c00140302c808510900b40d520001400c1c824903000d6907070520030042c0c0c464100c030301d010080b280b2030562103004403400d16005000546c1c0c90b400c0d00c000c81c0007032015000120035080c000c0f501282074100b100c514040c138420240c05120804070960b000c030218141c00864010b14255010400080c0c14494844c80d40c42c40301000051181d00c0f00e0b09264a0050441303000c00070303540c0c0c2c00300c7c20f00f0050300707030a018203200d05441c0a5003004416565241d0300c41003000300364821900d001e05003c1e99803003081150340001000c0d003040d483d1941c0385080001c1042c02e000b8a0350030704600d500230448460501c20360760040c90469070303445 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 945428741 1250 945427491 945427529
    0x9011d0403030e0120121b0a270e16260c1605300a0c050f0102130503010e0d0807140c0a120f0e03070614040f08030705120301 56
    0xc000c0100700310380c0f4001d54031a00c003008110760390300f00c1801140171400d810340d030f036612024a480ba4900c000c09410300c0004c81c61f10b42d9584200001940e4084013903080105403e0415401000240801d407070b90500c0713060420010138805c018a42e524001c8003400c410444401451500383c800700d4808041c03c0d5404c036080d1160861385602c080007500882c400b000c1518101041362a10504031448a0640325540700141e0b0210801c07030b240e9030280f003070041d0448039102c81e1685003802d03d0744074004c0000e080144101d4210103000060103c40c1207540107400840d070b45c611082560501120a2140a102c2e52910140805030700c00820955249607940d9143d108982e40c01301c00f954034056032984206514010700442c104107904100d000d143c940901e401c411501b40d07496008100080c44a403000401a08480314402510f0024040c81038603d9420942d08101403691a104103004a600c01c40c0c0080e00c0d00700001c1d2081c03000c002003481c94054000e03204048400300b2a042c50703110a224030403011700e585031004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 945429991 1250 945428741 945428747
    0xc0905100f050c010204030503121b03061201020c0d0909060608040506040b0925091a090408160609110f030d05090f0a0e090105330603060d0c0f0509011d0403 70
    0x304181d801c80c00d0803810490401101c908980003034000303c800381e00c0040c68000780e03080c3c1500c1c10b5004000041c0c4010003c01255291100d00014100f9801004011221800e203002901510b14513041802103d4000c80ca00e000146104018440c00408078a0310384045841c902c0f640102e886190000024590f6403280d94943c111004c00800703c88060150300b150643c1d0070781c0a040c1c51002821241d1044050b420283c0c00f104984002d45a41411807440e00b00e04840e4940b0f032003ca034080d41001c8959200d10320340c0b85c404010009188024515843d00e00c110007000882201c031201c00005544c3c10040710484003d1540e9031200800e40d502055060041c0300e2245020507401005520160109165035a0b9880c8841340b40b00c25950b1248503515081001000308007404042c0c00c0541c801500d04000da5224039100002c0300b011605400f415001000800b16100c29640440030b0303038049010a0b4980d80e0320700c1c01d51602c1d040d01903180f0600c41003000084090b80e500ca03414190101c0d00d02190b154580e0344d001d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 945431241 1250 945429991 945430007
    0x90f0e2802060c070614043f060e0c1203121510030c18050a0905040807080a020607140702010e060715050a06030c0f080703030815030303040f03030c090510 69
    0x20380d94000c0000014001a1220400381038040303040c5008048490401102509110140c00b6429900f80107110400608116202581000c2140c52201c40c05030520305803400e0015828480c01d01350040c044484040080c1a403001070138031a10015219400728040c1000b09100da0040044400d5006002c0c2c983c4240d01e042e18a0303040010a86542108220300e00071880098500482c0300c0800d17035034000c6800c107907001302213505400d541d060500070701030815000442c0340c1c009000e00d4040aa61388002030400800c2ca084510280d08040c1090710f465801800039564842203c244e0005040d604a451800c41880d013600e40d8103134143c5400080b084518140200e54010141c1528516042010007160040c00d214103070182c0304109021a403141903040101d40d40c0e4503580b00c1210b80c44201c10801500e41d001c142801503a0b071628014509484400c40f40e4800c41100b116290b050200000384002c006a480c055074003288207850501011503812410b84030078038240b181c40c0d0458890307112445001d111f6040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 945432491 1250 945431241 945431293
    0x206090705010824130b03160608011401030b030f0c031b06030408030a0f0f1b08010b09040b0105070812041a100902161b05012c0409020f1801090f0e 66
    0x11100312141c0ea0400584280c40c0803400c2140703650f888541d606c1600302880758038070407131070244554015850100c008108140500c07402c0ca444882003c00b1803568400d030011900e541000b021502503001d1a0442902c40c0c400c1709a8030b1080c4940604102c91820740000041c40d82e1000b0b1045003035a455482d441d400d54402810450391030341d20816517040030074620901d09007614007030b80001c0e0042044a10f82e0301c81005d40395176043c04545e00040015001d01c4017203485001d010740f4040754024200f00180ca990043c04001410003501089400c103060591402034441c0c1d028041f42150400c110702002c61110040ea5010316940c2442000e02105a06400924145034007035840c20000416884050b0f000500c0910b1051408a20038100121342c1d00210300d03410200300704851034860b01100040c1e802559548803184c0500e0303d03404010300395547e01780440300d080c5002d032102807003205036480103194001c240510070460b40b9080c043c059100241c0709170070720307181107000500c41e01510040c40084070380c20301c036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 945433741 1250 945432491 945432541
    0x4020d0b042301080a02031e03090303030403050c10090210080403140a020105060301110301081b01090f14010f021207080313020612250801090507020f030301080d02060907050108 79
    0x400e1030040d125071107a9607401c2d11504084200380c000c03915036004010b060303011112a5020003020000740c1e0340422012001e86402a17403500c03c1260411007819401210122030b898000402001309041c0c0010040064400c43c5007660200c0c0c1a00e0b841008968584201940140e0481c1540f820503000d4107202d40c10070701070304106c00301d52210190700310680d020b002c901e40140d4441c0c09101e09402c090140c44400250b181c0e0103802c56040804039603849030310030113a900010702d00c815080d03942d0007030303101401501080d140064a16101c50300c1c00301c0200740c01d003ca4005031100c8c1400b00030f2031000c610003801c04121050075160031003d440e002c1041d04042c10365051600c0d507000a000603600c0030000c20210358129500e10942c07401c12200140c80389200c19100d03011109602c1650307200ea01440c40c2d810355601c0500050140c50700780301245000012080d002607440000008030703083c003001035000c9540c10564200c42555031030901d40c64640c0f4181c03180d107005c070340c541011844048441e41140719041d4a50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 945434991 1250 945433741 945433751
    0x30f12090801020d020d0f05011202060d09020a09051914150a0902031f12020a0501031a0a06090f060519030902030a080a03060f1409190e060f1015020c04020d 70
    0x500e0b801ca030700c4403080018181e4009905948011503000742502000b466108102c80d40c904511000001c0b88800000d1042c10001061020100190b001c941c0c40c41e0058030050b625034980055500814040e2407058082c0043c01c035101481e40b55004082d503c80031350044415944030b00351418194488040343e6135010303a081c0c8002c40c01400520141d0b1007034900d114010141c02030101d085131320384001c0d0025140c507001a0304a0300980c1342c2c00c000600702c0b14203190014250101040d8070036080110280c040d4406c02803a400601150700017001011b0b00d18020441d10b20341e658880a8455110384c0203007030841d01307412007410b8005020307501c54001280080e06440c2c030140141d41d00c0495038002500722000c2035403020180a82c12052034100003034580809a0380300404030000140c00c10100800802e0302e90308080c1002c9000f019a040b40c840441050100d0703030f082c102040030003680c81045411144442e00102d00051400c0400d07180c1d0303843c103001d8024018040314003017404069484444000803550325a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 945436241 1250 945434991 945434999
    0x1b11030d090606051906022e0e0c0f0103020a02060f0612070806011e0303020a0212161202030d08010e040b0709260f07140d05070b030f0405010e07030f1209 69
    0x64001c0e030005038822031000441034102000c100441004888102800c0d15024050103000d400192000076040451003008201482069038807881044c0c3c1404036402e0700700011441e2220b00001c0d40030401408441c0d08910390107001c0111b00324001d403541000180c1c8030901103a1220101c54031180c001e20090b0895003c101e0b00861725140c66056032024004d83c0c07200c401002003a40002840140b41400800e452202e440d5032002544c40da80544080c0c815402806060708200c2d04000b4013003410080040d0020099452602e05c410030700d450003d038080e000da031080c900e20720300c2540918165000d00e0341807480b94841d62100004c000c8010030280501000c000c0105041154590381c100c0310841d5403802c4050071101b003202d41481e2a05500040c250f004c0103052004510789084003160300d60540d45074a601c401d5040c22880c045c10385e030006050840010600001e92840060148203d018100a002205180e01081d83c1d40e280e910019184d90010403d040c0041d0030a100e1110000d03642c0307420300a080c1c039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 945437491 1250 945436241 945436267
    0x5180c010507020f031504050c09010303121d060a060f0b0403020109031401020c0601150201200906090109031a04051603030503180c030f281a061c1a0a1b1103 70
    0x40086c0d43c0700242c00c54801c01c020401d040000e41400401030b1481c003819450365801900e0200f480c1c507108005504c5d4800e03829400c044c0345100f07007018034003001c030b4005080c00c0e01c1400042c03996014070b00e4405005000820a112454211821a039040e9213440c000703441c54132411055002c40d440b440307055408208a4071000c00810a85010b801c99a401d2003e000d024080a801c445654605003905100c480852103090100d009854038047c0c00d484103560b80800200407a200c4505420040c051034108400302440d03600540c605200720f1081c0708075210366051507070350a61850288001000a9001c0002400d45c1c0e10654011140104150444041d0800800003030b0610490420203403007540803a800e2011b500d00c40104200c0120070703086103503441225464032001c1c450071464111840f01c011020429031340324101c0410701c6100e9003081401280031450030040d2841e0f0b2040403a00801c3c03510224403003507030741c0c0300e00c0c241540340da0403107100c1080514060b14503e003141b28034070080c00700380220011401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 945438741 1250 945437491 945437503
    0x32703020d030507030507020d1b06020f0703030b15090d060603120c03030b18060d17070c0e071b241113060503072001150303021005180c010507020f03 67
    0x2109802401d80144400c030000c044420090540c07003014104030900070000e402260450140c5ca4920b0b0559003840303500039051a620301c85000504251000804c0c00b94840e5040c00341520038404e680502519400c0c00070042407128140d00d200d90b20703408100b441440c0c685104000105449040007295031960f07526090446074a050f441e40108002e00c18601c101607051241c00140a01181d05001590a0341300036091480001e24450044000280540034014908004080c02e0b00c0b0400c102c1c1c1c0c3d8001440c09603030205107031169503a110400700110724200c4c05240c100422000100a95942d40da032511841c2011881ca4045492071408040b017051814180c05525601c030802c0d044160f891b4440600d448440102d03500040402c0741c20f100740000b01c1d910107003000f205019505e060b101400349003a00d0f801131082c2c04140c100300b4075505001040540201e07010b03512a007504000c02095031050007090070400c0b01b0081a80c00c1e040700500803d998045d1025281207030020740407609900c643d0000c20719000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 945439991 1250 945438741 945438743
    0x70305060a150c0314040807050f030a1b0608011d06132c100e03070f1b090f4508030906090709093306030b06031207120327 55
    0x100101d0f407010074150003040b800c503107103030803612070380ba107440c03d42e026860b03407260b02682c4d21070442c1c20721203038580da01045000311103074128004405010717613400301c0e007003980380352080c0e4001c180318800008003085c0450310403400c40285000000c0c86e1b6692000c104018074100f401403402c541c2d50300c1d0f1080612a282d1200c940c500c000700e1752a8000c80703010210b45000d0f62280700c02042801c3c045d58002c682c0e00481550aa03c0c0c1c02468081c0180c024a4096091400c43c00c184054080116001407100f01941104000d400950703030811009009410700803248180211502da070b401e02d5001c40035884481a914001b03d01080480300c1e1170b9596544a0300254420303142e10145034005410f0110703454050184200500b443d00d002c0003141c606a50300031020301408440482c142c4020f100002c00d81d820850100910740d194001c11460b138903481d02c0c0b002c4c8001900d07103d010b8420011044844804a07045640031074001d1542d1078184034040045000e000441030070002403202000813100070420040c1c0040ca5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 945441241 1250 945439991 945439997
    0xb0f07141b0d050304050d02120307030e090703150b0a0e03070b070b01120b010308070f150f0e030703090e0703180506040605060402070f2a0303082508070305060a15 73
    0x11844501c1460904180318481841009100c1c0c4480c0010800004c48040b41d00135545c90700300f01c0b000c2c0001019480803a02141d0a400001428010152301c00306000c40d03040d0403511200b4640b02c5102c03c81c2210059490a9968914400240130400160780645000d044c146401d0280c0d4100b500440e09110440c0d111054140c1c0228218080142c602152409800784800c611a4514561199042c0080610028046040c0000c070f505c14422001e0104c0311050b0132400250082041c40d0034074004040356a451142c0a28203a40b00c1c0003031101004031514990541c0c0d0301c4047c1c07410300c0d83d91550803401034401420b140c0d48101b070500700c480c92450440c2103805180680414900b509002007039480c000c04440c451032040000400040d003646401040301c0d00310b841a1155425000440790041e4018054821008000800820942d1000303071588142c101440c20840c0d0394204038440c40700c1c0c1c6182c11000c046152100000c040e5840fa138462548040001d1140300400c1d40c0744840000c18608030313062000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 945442491 1250 945441241 945441253
    0xf060f1401090c0509030d0f020106050d081b031603080a090f081e07030f0309020a1a0403030306050301050907270c080702061807090902061e1b030307090b0f0714 72
    0x2214640e100f403002200039814828030344524880001d48a505000c801c50912a82c904449200c2d40b0035403089016000141c0405901d082a007081041d03038000760040040050150b40303214040302b000c01a104880c2c06605034951106c000e0f5001d48083c00e004000000316659240060f020410078040c2d4803100340950005a9900c1f030a44070007920240e0350702035002e030303103000c00c49280040c4c2c0c4500d4000e04c0701414600000e00c00048e1000031280c000c2540083c4000c0208020714500c4040f0000a104980c0b2a031810403c0c5a5501c0c1414261a03049038985066000780c48108000e070301c201710707421031500c584689442d08040c0640c610107d03061606d4260010310040700300b01d5041d40401220f43c011407250308445c0c03c1020160a150340308a140628091503495100040854481c0c206564041d00f21603803202c8850800346040e01d00e44c10801114140c02c03501d14200e01c0f03501010040300d0007180c1d40e50320805905c1c10b00d41c00045550001b905400c2e034840411a0382c01240c40c5200b4079030211655005044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 945443741 1250 945442491 945442499
    0x90e0a060c0e100c0302030d110909010b0c0d0c02090609070c080c06010e060906030a0312021c0212010e040803010b090105070b10170d0e0f010908370f0f060f1401 72
    0xf030701c0002e050001803000314060400841d800005403000103c2d00e010100d084400a8112403107405801c182c207070482080300000c1000c81b0400701425400780c4140c1261403036551000105c2e01a030388410043e402904000103d112401e19034180380d4480300d40d0a100b0045002540e44ca06194031024103529542c2281c801440008150100d142d00007500f22489050f03810700d04002030312001d480000a092018054496030409019019104036209041480c403c45d06510f00c0310b00690f00003898803018149440000c1401032044440b03901450304200308500356030a0440c20000350b0b201e52000c0c0d0501400b80000c000164a007130301e491003640c11850800f0401d1a00c0120130a540440040030429006614085a41c5078000030074a0302070f008840c1d1301e0403003100c40d0040e507204140360014400ca0080701103d043d016114000e19441c1c0d00351079843c20600e4898018600b4444900000a00354076044c1d0707924002c030350f8001d80c03004070742d010305d10000e0040d40d0510340b8400c5a0071b110784080301808a000409c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 945444991 1250 945443741 945443749
    0x503100e01061a0d090c080a0b1819110a050a030807050d020c13091509030f0216030201080106051c06080708121306050f04092c0d09090e0a060c0e 65
    0xc0010700c20f000003400c000c0000150050207024007240001c00c2aa2481709906104d040c52003c0d00130401c0c44281c400b10409424011102c010032142003442c2004d042881c8400c0c01d00181c684807203005583c401845244664030804032514031b40c6402e60019005c8400700307407641c6950b00e41c401180300707106081e942c0d020391802d20300340603454002005541103880e0601e010b881d2024480b0828200400001d90062075107811350034846525200c03002140351545210815400c89249078260545400310340341414000c192060f00d000902000740003c210500400c1124003400142480000d1081014014100b2101d4001120b110740d1000340c207580300010800081509010445240a804401c513103080c0e044554911588424881c0004010f00080c50750400c121810689025103148001841150480b8280392020003200b0103156852600e01c4030000425400034040040d440d4640361504164500540d00307004101c00f07003803140940224840b05000035114400c400d6810f109441e00e01607004035100b84 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 945446241 1250 945444991 945445001
    0x6030b040e013b030f1e0703091701020c0d08070f0912320d0801080a03022508101d031c090309080109030917150109150503100e01 58
    0x18081c07991511400d80d51400c24204402a485001421200f100440308052100d00d82c95806001d0140070100d04a580540726000420f038411034a007050340350b85e001c403000404030304c03c0000040c00300d111f083c02080803030046100300340c82c4018240010305146c4444e5000d814000c2411000000800304001c1000e4541c200107800a05030040c40c00c1d00b01c0c541843c0c0e0f00902c201064101800105a41c00904428500c00140c41c00550342c0700b190400b903220344034407981c0d40c8003200070280c08208904008a080c810014203034102a415500030400c1c5c0301c003200505031448240d0300000700074014000101e915a4104450b01080079075100c006a1406c001c0080010451110759038180e9810030404401c00c01e4018400440034025040d002030190703114601a16039031420b5001414550070800041c040c15000300307680044501d1b2450592219201e4202c1e5a25100344002e190400d120040040c0a100342c6a400340250071701c1e8a120400a90711100040e2400001c1c801c2000300319202c00750f410f2015001c1c001c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 945447491 1250 945446241 945446261
    0x3190905191515140f0a1404050f070c02040e030405040c0203040512010c08041104061a091008070903080d020d18120314060d1110050d1a0a030311010e0706030b04 72
    0x1c1090540f80052520710004500c00c071110b000c202034400225585184c1410729001000b01030010700780d9585218045000b802c0207082c4900d1400000400011052003158410b29150b03442d800340c0886a800c01c00100003000000c20144001d01c00854152260701c12402c190303001d40c0085451758600b00402c0130801c4540c5000713102c0c0e414002d00009254000c20850341003603201c1e40e110f41c001c54540124004180d00d6024103418044190340c1400161200020201c3e5802074542c032145019002c07050300d0384082541c11a0001c2c9240c1b000308085141c02c405864061001074000d03180100a0180308142d81c15941421080a01002030b0b01c00c01c005224506100c00d018281845030b081c045130071702c94441c40200350758095103120008100708040000344041c03101e0000d000d6101d6025400005003181c0101600e4800315241c0040500045014660040785d200010006541a403c40d0350440f00c20000c005451034075902c60000d0440c50030107200e0800a0301c5582c0c1d00003400d015000401060f9007900705 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 945448741 1250 945447491 945447533
    0x919021c051305030f031906170c01090509010909112106010e04030f0e010201020903060c090f1f0c05030c071203140a080103021e1507060506150319090519 69
    0x40340302c00241003c070aa481080222542070348a9a99450300007104040d4010344c80007a21704240811800e4094040c20300348850902208c2503007008100554000280c2d00685500c8143c0c0e4004008001c501d8102c0c0c21440d00c10101c400c4455501070214829059141c89880b07905040c1e0b16090b003a01c8100305030703030040c008039100482030f0800c1c0d03d01070481a81040c03c5001c10030842280904d0303900035011180101d0000c0c0c02c5811078038105100341c1e0b00d5004101e140740709401c00007040344146030134a91030960200c6001a01007c00c0403000903035096a0000e412201c3d80424803030900a01424801750005080c003003400446182079203402040c034462984092074409080c49021a01503005400905582c1e050b6850341180d03817503003104482d24004041d0954002d402c003000061000481d005002040e104101c144084d4881004002111005581c14005050103000103004001c00b02d0075540c501487c050300103858502c035211030b4104004111105605001d004c003902c200500d00303104000080c2900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 945449991 1250 945448741 945448771
    0x732031501080c070b130f0503221a120402120d020106091515080c04081204030614060607290103050c0f0f03030f0705010b120d030e010506010e0919021c05 69
    0x15440d0945c0c850301600b800f01202180c3c40c008108004481c02140003038010080300d8035910f480c1da007141e880c8000314098041e040940320004801e40794000d0b5083c915044941a81000c0e008a80281310b40c00042084c1e1f84059020120b4656940510640b0900000384e40003180c014180b0001c00161110845801050010074100300400c039010590200c03024100c1c58440e0003503c91010b0100c0385c0c016178000707001c1c902801241c8414140100014422644507d00501100001c1c4c1c085002c251400c4440a4008400300030213400124100030081c5406070703803000030407000c151528100c0d01d410300341c0040314254003072030100c101840c061203140b4403103500701da8074203450319114007003031303d070300441c0048600700601041d1201086800e400c0b4a07001304014002002c140b05608100d03a40301d080e101c12802091030f10a9150345000c06015552051380103841e05020283c801e800d104194000030100740d000000821a081f2550807030004140d5402d40564a036211640c01350071b0b9080b544003610726201c880c034030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 945451241 1250 945449991 945449993
    0x7050f0f010f0c1b0509010b0f0901050304140604030309140604080a1103091008010314120a0e010309050706050414120c010f11070f090f02030732031501080c07 71
    0xa4824012400b8600104a080124000c0d15080d44048006003410015006802182004102d280488400f183c95a01d0350b40d036200041702600c80c80c0c940e0b1220b001c04000c5a48035500a02c015608180304950754507103400f503030210500b1310b10180c808500203500d0300f42c0c0206010510200c40c2c45429540f000d451942015607640345c19205d51140d807428040c048002840d103400c14000c0d42c1c680c0c00068029078006d1913600d001000103000340000c9410051010800c5003184001584211607040c00910900e051100f000545000344440708850415484902d903e00081c020700c01040103202c142c0302c0503100c6050141602c4061080e854041c081e0040409070701d580d2a00150480d0020320a091861108144d150f080765980e8a0203e110342e1403150000024071041c0d00000300040361000201000b84640c48420041603100642e48071000403583c0450f1669210034484420725014030500c21210100165600b01d855003080b9251030042210103080f014550b0014402036200e002560285d24040c41c1e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 945452491 1250 945451241 945451249
    0x1080d08060f06160f060c05070c05010e060d020c0703110f090112050307020d031e030c02030a120f0603061401050f0d061a060304080a03150807060305060301021b07030507050f 78
    0x10003011648654010b204282542d200c1000716040214002c0700c1e00b104003d281402c035020510302100310703801450b1524101c5140d114106492906a00c1884000e40a240c030004458001100905503442401002144007000407032009000001e20355026103400b902d0340c1003844030043c0a5a001c0c1c0178202e00300e8421110f0350b0b848105415207403113241c0020000000e080043c614001c10394000d41083c4140101d200f80341d0000110704400c040c54400c00042440c000085054814000380c400140c1d005019000c1058040c02076600195250000018000f050303071510025180e495209480c100e07640c0182281c0c0c1500300904901404041c0e480c0d040250044010900c060f60192001d006180d5940d140042c17241a080034503089203004107101c0d264103043c28405240c1d485903011030042441d1030305420300c40422048403403c8443c04c0002c0e01405140510a4000e410300526055055508108040c03400d8102c002441d030b0004030800130580207085191040c9446000d0300502e10a401e5070111280e540d075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 945453741 1250 945452491 945452507
    0x10030b1323060621041401140a0510050117040204091e0203120301081c1205010b03190903120c0207050d0305030118020306030a0807020f04050c0306040c0804020307060e010c05010f0f0501080d 85
    0x2c08895042c0d40760f84a041c1b200003001e0180201c0700340d5080c500d0b0f208030070700d005103100e0244100b0941003150b82c8400c60350802001c0c45106071030115441c03420019041c1b98040b40c0d00d0340180040c0003c5030b006030a580e40c21107000d843d041852000380188031107082d4103041050300b5104d074004007e9031555043c00e14540d511900d000010200d0004000c91001c2544550383d81411000138110502c070558650745165101d41080b2400c49065144020100052555004402c90b290300358a5505201111200302006080b0020101040d4410454000703200e4468459000c001400303a91415181d504040841d00c4114103c500a09000e00510a1000c02e03a00800d1550050754002c0104d41d60300024804a000e0b07110b5024404d07403040c43c1404000c44010850300a40c850442180d0400036841100c0c03003912100810303035020790160704c01c07041804401d003c0c108010466005040001d000e403407940c4d0755030139294101c541e07148c01070300e551440f5404c2c20b50303008003805041030070040e12400d05142c03030060840c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 945454991 1250 945453741 945453787
    0xd05160e240a11030a080a0b03210904090213051807140910050d06060819170306041b030902040c09081b1507050105060a050f10030b13230606 63
    0x2040042e400020500550302da00030f400d800803e40c0d03103444014901a01c4c5003011640c645a80e42030807200e28181c80c020840c52031410801400c00201420400194540d4108c400150b40103552085600c015076034038a20144054a0008040f0742d0f4a00003400f010034244241410740c841d444600213201841c0303801c0120410303d8060311180c4059460891403a15136078141c0c0a2504102c51203030000903c0500d0b000b135401d446000088030030702510013071462603650100b10702a01c007003204004070342d0400f0310200840c2c200f00004c102050000740c00f00744161181d6910786110110340c2d41d42c6100c5c118113203402001110035982c140070030060320300b0005a45500048140c84204c1d20341441103403060342c441e0100c081c1d001c440070049454525030300d07103a03000745810798065104141e8000c1c00030782450050103940e104903019000c002111400081907010341a0115069401500f1107074650004445100c0c821f4560700000020302e10100010030003050400240004d4001d90b010003210380403595082d0902d00031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 945456241 1250 945454991 945455059
    0x90b07050c0a060e0604140610270c091e0302090601030e01140109020417030301150c03140313060b09240a09020a030506010909200904020d05160e 65
    0x2800151104906002c152076004180728603000a0291020002500c90b04c00e40c4134540c200080d1030300109540d602c1c03804070754085444031041000e20161141c184d5030b0b001c10800454030b85910003070082c80b03015100c2010340b00c2c001510400003000080c0342c1d070100c0c0c0d031680c10030110f40c170003581540c011800d01c020003840c050626407280d64415141209502c1015000f490380c2400421756140c005000195010b4864501d400d90303606d4507501000000300c22281240c801051201120780910303010b481034000e00b1010f4042c4441c0072180c085014100c00118030850350850701001480462501004441d001c0402d1409440c4101c00c0019000c29405010450506030380034800c49080c0d02c0c00650350303091541080a803c1d002003240b20340541c150f000b007405410240c03070301c0000341d4030382061030112800150540b49141d00301010b90490500703030000b800070200c06000585042458281d50099460681d01114400c071060410387c5099409444c0042005003220480b03030f8000070706900c034207064a5041000754 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 945457491 1250 945456241 945456247
    0x14060904020d0209010314070518182506090806042a09021c0e06040302030d110405031e0709020702060f0c010b0d0f030e010c050318040609060803130801090b0705 72
    0xa40d5182c075000e41545500401d241c000e580c4902d45101003070006560312800d8420481302040c0c40c50101000c000d0300080416018003503036103605105065a200d022a1006e0184064034814a0700e072030081c19a11400d039409680143c03801c079004005d186660310661194214801b4800001c0840543c0d0380045820541c4c3c00c021315110f858402d6118080c2d20044041d88001040707545003a1120403c0c501d40c070f0f071040c10041c1d640c0c40409c45448903c204d80040068000300585e06c001002540000c1c18410704003800d904047c2c64a01003403a201280c0a84400b03d6056103031011004420010f00014005c0f02000f9420100b080e400304040c0d0061031755092407041c0c0880e010000360025846103c01c007238005c00d5803402d18454242150283d0940300154001501054444400d5004107940c03205250702c500218a025190009030310140c2c40c442910354443c1d102c003400620750405008801c054000309001d5a5202000184025038081550280030300d0303414900b03901c011500301c801c0d030759000f4500d0904a036 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 945458741 1250 945457491 945457493
    0x503030a03200403060f0b0607020328080a0804060506030304050a09020309030d0213080c010f050403031d031c0305060a0324091e020405060f0f060a0903080a0305091014060904 78
    0x140782c414191011981d603202140c000140012500280c00c0324001c204104401205001840154803529002039050307230102c006403140c0d001c2e41a500020b800c0d03d0041d2442e03003000e5920030707031540e014484041c0001d41d02c1051100340409442400d0b04184118011441d103483c04002c2080800b140c0700f080e40055000c00001d85c04003003130049500c1500160000c5507a4942c0d40d0f099903882c116401a80301e01d10842489030059405581c4c1c08184542c140c4440d03061500d15681100c003060400d01f0301061030501c0000502e2503d007007081401d40120809600d40303181c0c03200d00080495070001c102a01c10b403080d030410404100418100d02094000800c0d81504416090410000e04004c1d1b0004100c00002407100c14003031520407124603068802c943c2413045889500801c103800482c144083d5000c0200c0403103c0051400200030804910700d400d000040580e00e0b00d80c0d0140c5d4104848441c0401e44450812041083c00e00000d442e8480c4071004200031019400c90060034900142100d0041c0d0200001c14 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 945459991 1250 945458741 945458771
    0x8100e03040b0706060e090a02090411130e0d1805060a111e030306040b04020c1c0e040219090806010608071b080d0603020913082a0d0e1302040503030a03 68
    0x401419840c8402983c600c190310704040208044c1c401e801076401108041040f50f0000b1800c401001e030020000b0025440d00c1c0c585c041c4108404890591013800900011680c956a008214101e80054060240001e0900006c1c000008070305e5045000c0048040a012668031041918444030769850580050320304071000754900903415062000c9651014280700c03504100000840c8500c409960902008000c101404140d010302107d580290700031007990214405480154210b9440350302d080400c032225540800c00300c0e807105042c0e0b008030f8030030070300d4241880d001041c40c401003031510300420282d803500b03500504003100680b01a0400009954102c444081c2daa013003103800ba0406a000c0c0d0702d1450310900fa00030045880200e006d2141c8800241c080c2c1c1d4061078101c211500404580e02d4500680c6d00c100848a01c82024113440205d4040701105c0c4e0010031046c1528103040c8c45220300d00740c0c000104640c40c1b001a170040c201c0c078010003003030010f40c07801701c2502d500d00502e080c00708460703005102c44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 945461241 1250 945459991 945459997
    0x40b0a1b141b030c01150504050402030a0318051e040605011713020a090203150102210f1605060103050d021603022206090c02030d2f030c0d050f150a08100e03 70
    0x80041d0f4803011075408a10301040d4007a00814200101002141355154207010035607a044a010b54140c10840410340032034000d644014003605280c01c4100019150000241e210014019400c8440c0c00040781c203005041c03a20071100a0030302428805e00c01e803003609001c0030310035009002800107000c0c4100401191a00700b00580a051000c1d015520f80c07820031030b00700a04c000d560105005115100c4500181028000b1019042c00701400b00c92400a01440480d4558046202000120202c40c000000f044040c80b100780603501c540064032076a068014006d15001a501c40d100601070202420001130740c86180c0208014605004541d42040d4a03042900a040550000c00c0481c2071152403601d15034040002c08000383c80007000c0000b102c400d450204802420381440da04034445480754015882400041c2d944500d0b82d41ca00c1c4d03c3d002183e100101a10300a0320035014158420042c006001b08403402c00d9048042070340c0800f003042c41c00049954400e200c0d080303400300d42c1ea142d1707540745046414411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 945462491 1250 945461241 945461287
    0x70302060a03050a050601110304270612020a0e06030a060506010c0b090d12061404050603100c080708010527060a0f0e2d04080918040b0a1b14 63
    0x51291200a00d54024003d050101c0d02104828684070000700550b001c0d00f10b521000d41c10704001d42c141030410306402050542e5150342c000040c490a040c007a40d01071400782e4805400c14a09007207c0c0107542c070600900310030079049100c42025880800c82e10b504d0001300c0022030703a048040440c0c1ca8841d1001038950f031103003e00190031041801c1c20001c054000080305900d5103620750301e03001e5017508000d03040200d8076580600744080484e80c0650364dc0c2c2ca0540c104a0304200b0090544110360b00b00040d001c01c80c1e003210348072000300d480482080b8240d50001100d500401041d200a010005400301c00c80108841801d04031f1030702040c501203070082c2c0303802c0030441c060007191008101441d11030100c282c01e150121100c0034541800d42810118540ca0070850b5200c0311000d84c500407a0700d07a0740d10845070350003441c3e040c0d070000d00c10a40030032201e000b00380312409503000e61111035035401d0a4600c841540c600c040d0315404244810a030340c24032075102c10a000340c07250680303600c1d8507241e03a8980304900c0342e21054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 945463741 1250 945462491 945462499
    0xe071704030e2d0105091818070f150c0b160306170616090503061b0f030a0b0103060501031802060c0109050321151f20010926040314070302 62
    0xd8003420800b882c040c0e404041079009403840168483c0c00044800e482000d020079000322501c403500c0c000721542e0242c0ca41100840c4c0560f19078182c0080700318940201c66000100040100c0b001b04180089400401554002403404400403881c98855201d0702d8409021824a03418003030150300100e02c240d20800c0900000f050040100344000103295980c032060310b83c8406008010709180e0405d0081c03808500b01d6201a000c2d0040e65500b1200c9012814080ca1010540100300504194000d031000214412040310f203001407011582d400040403540560800e506061804042c8032414080f084140c0c00c203541150707016a5201c185c800c1c039024003400306004045100c045030101202c0d05680e5030203444d4a4050300440c050f030b58040b0040075041d80b0ba01861704805004500125050034600700007846c00941054105840c80e50701404401b4400d180031422655503c18010403c0320111400310f05d80391609607084002e0803245070100a10540c44003c05d4200302d4554020324140910a1000641d0010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 945464991 1250 945463741 945463759
    0x16030308060315041511390d05160f03030c110d05040504020a02070306020705010917040609060c0305071406190213060e0109031e0b07030207050c090a0b060d0906060e071704030e 79
    0x8101000c81c07201d910b451072801503400b0a20407032506040e400b00c18400b18004002c8230402d588240c6980c0e010311884080d1401950b002d00c003062104030282c1d8124441d0340d00080760201d50f1320040005000c1e064280180c4c106040d042c403555406001d80e400da40c0110b80c01039603440501000d0f407411401c3d5000501090003c107011040c0310040d4407020005000f022003205c500b80c0d00101d0541481140146404a4240d000a020b2a0722401c041a84103229040c801c0c0741540035202c041182070042d42041e150381c810001c114124103e08512400582500020342c10000210210ba404251501400003080319408947d20302c1c0c0e02c0782031054010754002c0060100000c4102011926201000b4192180c2c00502c0200b20030074070910844d042150400054075410000b50100100310030301404166031a030f1242074214032540c41500a119900040a000a040c19280791660036200c20b603005120303a200c982c08001c0345a80224900011200d52032600480e9600c3e840c050300d0304664800c000c0c0d0824010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 945466241 1250 945464991 945465007
    0x103050708010605010f020703120c0f0b01091107030903020f030114010b2a0604062d0f051f09110d06090209010e090c04030807050f16030308060315041511 69
    0x10500e1026509100c0c028002e96498100564200146c030b0055001a03000740030401c04244604040258140c0701e26002c0c003940c05944410b0442d80c010303c81a1503d6145a00401203240b0070f10640340170300c048890290409041d81c801604000452001a001750620751215140b40e17403c2d80321035060400000155801c2d611940400029003140d11400d0724407141c2d50781d0002e522522180207288441c00c40c01802c9990301c076501d00004e040c0030141140601a0508503140c01e040c030b1102802d40340640e607400103803280b105102c10242c850190500c44841540e0710740303039201540c0319200001e480d00690046501043c0c175100156070700c69020403c18052500c0e00101c3d075482d258004081c188001d0b0ba83c3c0039110040810803400c02001c0d5981c021103039040108200254441005d1301e81c0500603010f070381052104540d06801c0a0b00288420b0501015110500405800503090b9402510541c014115108194a140344000e80988040c052100c4a00c650840055540201080c280b0703c0c81d00d02d0311101302e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 945467491 1250 945466241 945466243
    0x140303040c080d021c050c2a010306090603030c1b0f0f030b16050a0f0c02060409140112050c040f1821020309030709051e090a0b010501021903080717010305 69
    0x29409034180714003c03003101110a031310002d95617001c0140740070454401c2c0d26000c02aa010340c40080421814045c21104081d91701da64040c20600854900ba101500340301c01e00014125049504030340768403460803000340702180c2e114294000e0b555004018421880f05091582c03000021030340b0001c0f16418040c00030544503070079500281200d205030141c0301c09803594161600d013034031a40c1010b00003803002d100c800400d910510011030b4880f41e0f0b080095804071140c010410992141c1c1000b80038988070800c0100003404420054010006040d0103441e260b00c43d5079054464041c080381e6441981c80d00e2603400c040c0d50f1548407105014200090301415406c62411103d0b007a1080441c0c0b040300e121000074074110380040100c1c0c106035001005404254204002c8034010070010b010306880d48a01d59100d40420f0030134070b6450180705024000c10311500d0b10705d41001c2c542016048141150002440510348520300c0642558140d45401c105030307031390340d1420116042c5640641c0c19030300700c240800000601070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 945468741 1250 945467491 945467513
    0x3020418051b011d010804080d0f1103060a15050906032706180106030206040312020c090103140c150d2d020408060f01060207380a181a030414030304 66
    0x25080c0c031100c1000b5001c00380c4a40280d10031002e240411109030001f0009801c02c0020500004175040004900c9003800a207402ca07108110450320311079001080c03251070710309031003c4802026441c40703076044001481c0000744a030150011580c00b44034040003007403411081000c042c5888202c84641c0315810300e00f00310f042d270710541500d01103040a11f407900405e503103806005072001c1e03a4000c0c010341e01e090729641c0c0ba006058440071a46003140070342001c0403125030311550043c3c000e50003100051031350105007914a040001512080744500301d117200d401040c1200a09490488140f000700161080b1208802c0c1000341070400b0000c4c61454104040b0303035203881580a07209803282081200c45585d0391540358110003c00f0301a400150303118113400c01003801503412940480140d0405441202d000c48501e81201064294101003145d02096008082d94031001c5481c2e40c0d00b143d1400b4604500e441d5070001407803128061070180f036000200003414001c209031390724040d010308400c50740e49140c5810a801c02503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 945469991 1250 945468741 945468793
    0x150807090b190806100c0b040204150303200d080a0b011e1805040921030b06030109051e010f1217070b040b090102030708160e030706020115090908040302041805 71
    0x32038440120740c05080645134850a0317242038031080d440011940710081002c6005000b241d002d51500e00484c8510704140718031000711310a4565800d9241904142d820904c3c03909016091540321003004101e6560254105030011940701001554101c008012245841c21000c00c81c4290709a45408000e075a006056015030300600305180142c9449000704415200c01560203080c1105800e0004141d1018000d958016031007403c1c0044d00d51803034004200c20f40c20036031141c1d421580e21810040c070f842c540c0c0707180e401c0c55120041980b803560420b04140c0305041540130b02200f88191420b145c00704100c200107807280c80241280651503000526146000d01000c4404503900000c0001190358070301c0500959000700303031644030100c9039950303d0000c205003000455030104100c103138076500255403414401540a420789500201d41524824640b0f055074580ba8003c020030b620704851340c4c000c99030820a50b810307a541103401103000312120703251091110000e480a0400d018160180003444050480b02c9046 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 945471241 1250 945469991 945469997
    0x2707030f050609040204050c2b0c020a2105090904050a060b031b040f020909090606040b03161802280206070806100305180313170601150807090b19 65
    0x1240400c5484107845040d80c0c80b0390440c41c0080490010b2a154220380d602414040c1c009051a0901d00c40d0010b020030341c0250b40c1c035840007198040040d5000d008601c0080c00500052107000300e45c0e6110701c501284c42001009840c00740804105d00c2e0300c03c600300c1c4c89940e8001c040c2c0c2841c0c141800c0050f20ba480113201100e200d032400b807040340c00b802e01142880b03100d03208011600d908c0c40490140005881500903200d0703500c2e8204000c81c19076031804c19090181c280c010080c100d500e40b18091004139200192440e11a030710000700f0707180c8840000a07203c2562003a44d5234103040c144041280c8081c2c021171070418a000d000008280021a039621107a05408007642120303d0303610f030800300355203450059034444d0704120145030b0b500da030070f009410441d0491000c00700c80140c15542e80505080d908400701481c0409000d65081182045c840a0a10720154020117400c0320352501d4111884a200d440840b018008254009500c140c00b40c0d003c01c00130f20108805a5498001003e9101ca42071080c0104000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 945472491 1250 945471241 945471251
    0x51902071a0c211b16090e0c0102010219050c19030804031407020a140a0b16030801090b31051018110915070f1410180f02270703 57
    0x24030a48407004807002c03c441e41c181c9402141c503015180c401081c0c1c0044c80512501c40a014504000c2000d800102418840010445a05070816041c010362104450441e801031055683c1c804071014214104052401d00b2659040c80001e06414010340a15046484404202d22028190040c00003031250f880f80e511340c0208101e890300318110f80a01040a500030103100c0052141641c4144044442100104000e403810368903403010a00b5481208090090041088a0300405400c52030041c00b4000064040c0000d0806c0030101c2d1204041060141407580100c0d10741d030240401030422150481c005ca01402145400d200032030b2400494890050b2036a9003d64103240c0c5a410b1140052420702d0800a40c50040e440007049180400c56001c0c4142d00c0041203483c00180301c1c02103001002d0310641801104184e5007003001d0a0112080076910200e040c2098103652895682d500010164007441c4490b10404d603001141e14500d103908081c608100c0301071407003141000382003c1c603c1090780340d8040c09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 945473741 1250 945472491 945472513
    0xa12030f02100e030f07060e0106080c04061409040803100e10170c090109020901020c190509010e15010c06021603030911060c10050c130308041a0406051902071a0c 72
    0x125003041a500205400600c030001c030745e40e40e440080104501645010450350303104004542182e00c0c80d407107407c4075840311031000d10b903003000c0c003801004060900d902216200500c01240d44010300900040003001c000000609100c0b50514050252040030b03001e044515095480e0101300485c0d0242c988800c41302010010b030f881c4000b590300c11041c2c000d0680702042e40f9040340349020703400400150341917000e800541040d40d107603001c1030003041d907000e034003002c1841c40c20003031242203141a00400c50b4070603108104082c038240030019014141080c03800d401c0024907420910003c2c014051040c0480611007003500a066040e00089460340c080c07003109494807111020000148100030415074a81c01190314040107100f03540c46203600082c0440c660785400e11047c0540082842e030340040310700100104040c02100009413040c1c0c004011200755600d09801d01d44068141e020310311107a061440302d120b140034101d1003030000400030b11100c0c652517040700c0f070701c01c251946411282e0503c3c180c0c8141c4111407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 945474991 1250 945473741 945473773
    0xf04030311070b0a05180102011116061404031d0105070803010e1510090501110f030a050307020d0c0206160201030b040f1a040b0904080703021507030e15040b13020a12030f02 77
    0x481203130444c0c0b5002d20f04800b88003a595054001c183c1c0e1419550307122030000d4600101c0c4020045c50000b140c140d503580440b450110111106038694200480390601040002030b00040e40c1070f0402c420694440707651040800480701d520606034000d144d41000b1000042c1d103c02e451095008000441c07407507604040030390502c458421044e030f08c0c000140440ca020095940600c21802002c0c66500c103070380300c6c00610350f1550301e958003810b0920b0000720000100b004182e030600081041b10758902d05984000150340000307003a401040750f40e2107100050345100d02168040c0c0e004032101d1314003500500940c2e4029141c503009200003d40820308010070010800b075450b0900c201d0b4242003008000c2052500d4039100c0850b1b0fa04480030842c25403082044031610356101140503841040e540d9004205180054a03250800600070142c098480803034040c0000291144603490b40a200c0c03075448030b61318506000150001d882e0341e002000c0380525800f80d8040c103521201600400c00207400700c54080100422030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 945476241 1250 945474991 945474997
    0x1060b1c110405120f0109080309150103050d051c0f020405010e0f030601210804090605011202070312020c03070816020a08070f0312030e1e0d0f020a080a050f04030311070b 76
    0x400781129040205004034600400d00d4016202040221021034a48038400b03400c41c0c0c44107070140c824020110410101480c1002142074000c0398030148410b55155a0b0b64a03035420051000c4400d1080101d0003105d0100c5102c5040d40198040c00140302d07800d807103000c0400a40c014040d1500045544049002c507090103417900203980c0000e0020685a8030348001c070032819420048401d02100b501f0364440206000c2c00240015142c0301400244a61403c0009404072a41e4080c00250700d00500840000c031742c20180200c0d10002c8414017585c0c2e80000e2201e5810f41c40345c103070020458600031414054142c8080c2c07840b18443c1c825144214038a450340c015940d43c1185100340064100d00c0c027001c0c4006915400718900c0704070380b030401040001d0708142c6607080120540d151200c0c41c80c00794444034611000c01c00c10818a1003800c1030b020308111524000c5d182e07500c02102130120800014410210740c4181c003200c00c1c100d850003a99807240e40b2444c0c010201c0181c030306030040364892804040703500b000320021 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 945477491 1250 945476241 945476261
    0x3210e1305010e10060e0d02010201090206070602030f01092304050c03030f0d05100e13081204060506010e06090f0d08070b131703100509040c0509130b1e062101060b1c 74
    0x1000846d0700c010b4200710411183c100124119529070600c440180c840d000903162451040302d015803207140c10100c0c0004d49805034000158942030101c0c0203035910710400c2411185203d194041031680c2e072818030741e10b0a0b00c00c0d02c29503014880060450034003083c08011745626403a00b50140055141d02200303400a180350300407100340039001c1703000c1803058100403012112507103d080036030b042110b94200c00a402d2400c41d03040d00e105403988c01300911927134443c0908413071000843d00c02d414855280e0104108a1910380214040c10091600c0000d0001000a544000780e20106012452034039651040e840882c3c01c000301d44032200b60b29031842e01401d64081d00d110702110122840c2152900d810414004000b900a866910440c40c022549840310500240301d00d81102021500c043c2615000ba50b0040050251200798403c1c45202d41140140e03a0703154010b0003c50b079440074034201c000501001400060700e15110342c644540000d18214076800340090107201b8140440307012402a603181a1040015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 945478741 1250 945477491 945477497
    0x40302060a0f02070302031b0301290607030c08030108010c1e02060f070e09010f0f0801050c0d020703110d26060906060f040f0e010510050403210e1305010e1006 71
    0xc40e0340814400c0c1502d11004280e40304903411103a03250046030820028282a00032010000044006030030309026a0228202192141000c90600b80051003007862072950503215081c006000c1040c58030a26804440d1070304040381669a580d61b000450080412030b140c00041100c1c44a203014100414001c60a225040c1d00a810a0f41e00c4001c038041350000106018107110303401d00c0b10307815074841f803c00d640030705800720b074007052141052003564503140c995002115582c144001c2224540500c410307a00c1c65448100c0158640402d40340580d1003004065a00000b40301d0f201c428900e050b40080b441400141030010640ca9002a40e05c00760081c00448a0700d8104174100007244850030102d00504d0660000c42c00c0d103007410703200e2110f000c1680c0740d036000705400c41e0380350300502c5103150580714100d240c455420901d10b004e143d6502c1c08000d842c200d002c071002610403c03c04500a005030002111000024a003681c8541c2098900d00140020700481d90010360034000552680017501003103007a41c1580d2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 945479991 1250 945478741 945478747
    0x5090c19080403090e1b0c01140105060f120703020702150d0b0105040303020a1b0810053c060a030204020a020d0206090c01020a02092a0a11390613031704030206 71
    0x40380c9415280d05c00f4112002502c036001e60441c500c803c080141c041e40d9965000810031030314007a51514508410b8020718403500c0c08000d0714040b044264111600514010b0b0344070340c01da0b2105025070003402481d80103500300001092004103e240d080060012980303d00c0200100401800110303494065400b00401691001e00810003041e156030301420800103040041002589880d001ea04140030250510b081c00d40354820700600021201010402e0115501c0f0f4040d00d5500000080d00d1020704844049401c0905011907225195100c80c0400b41d070b00507000b5903503400440c0000b550340d10a41164401400b03001c0c003080c0c441c0303000b050020203610142d000340319024a50b020468220070187c08410808100481340c5a128004600507806546186203d919121403220140c02e291002c808554aa00400c1c2d50100055501e030050317100c0381010b669070365100d04078604060918035460700c030341c4e014601280113401c009040c25031030140d91246500c001040403000b0369200e42c0c0140d010080d0b2206041c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 945481241 1250 945479991 945479999
    0x8031b19030b0f06041502070e0405060118140408040303080f04050c010509120d0207150201020f1c021c150603020c030a112b171512010605090c1908040309 69
    0x81c1c0c11905070307064000e2042400940c403c000840d2507000f9401030030030812000040c50400d8040c071120004003144d000d407000e54038141c0e80d81c985510050290090040b480c1d81c40c100e0301011544030784005c0200903454681420075090107886500b0a02c804c40014803c04002a241341605d00c0203802568032800810b40fa8103040015290380c3c100340d207265000001100c805054120800106540010710b4000c0d000d105c2c04d1490401c0300011201d440404d6a00400c903690038401850100d07250140343d0402030400300000000315019100745e0a807503c22f10034074440c03250580481da00c03003111009041e01034011307556181d50a034140d0082c0700100300d01b40c00c00d018a840d42801800104551200d00c030a4031880040a0140115440036044403e1925980c11042c62099003082902488003620f000c2c0c954289802c18cc0030546400390075545004548141015807040825004007026110090080900c3c0c50445528056900140c1d0a4000f04640c582001d844030b024854050055400d42e45140c3c40d1410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 945482491 1250 945481241 945481247
    0x1b0f0306011401030b0306010b041e2313021902071d060607020a12060b13060e1605040801111305010c0201120e1207080a0305010b030108100e0309040908031b19 71
    0x10035960794185a01d41c8170400081c0da05022081c0079014228030740d901d4030300f0302c0049498240002401010072010740b40610408113080c8140d145501d40c280362400d95101c0d2030229101403050040004e4460000c50402011841c0c07140011540006034221041540e468052030444001d504442d0000300024002c9445401c01d1300c000c000d034034001341c518541c0b260389401c0101d00302504e203c207480c000d035200c0741500c581c03412030200d210301450614140030310350410600300041c1c14050510a12510031001ca2440c4030700440a4800420200c070080203801038001d04420540e018084801b24401d40c080081525801015940340c19078040c1d54010140d031125103094003d041d200205010f03840752110049240d0002001009410710404040351034010800000d0103490341030708400d1045000707000600c6901c40003e0649880c00b54075a021070b034501e40381c10071030a610940c940c0c00d03049400c0c558101c0a00c4161401540500f650074a035000d24000b5074066104c0307020b10840b1451000780c095811206030302c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 945483741 1250 945482491 945482519
    0xb0108072f0f06070503040c0f0609050402210106090518010e1308040506131d0f0a020a2a030f0503150d02180a0509010c05090d0308090703141b0f030601 68
    0x71003000c40d10301582401096140030012528080003803000410007080049804880d0000c19050401901044c104440a07020200c1750145d035018940c04140000725004d4000b8038001c860501d03001c2802c551315000d00604081890094600a1105d03000050401002d046542e0403500c2c00306010080392078290586803941410041560440001d20021035680e4034039004105044290070a400745c0b91034400e000c1c003260003205440301ea50f41031108102c0c0c5180b0185c0e495a02c5001da41c401681c484650381d058400e48d00c0490410802c02085d43d9560303c10117407041c40c050150180c0c44071461004603080451700c2d880b044401e00e48484400c52186c15030b0400209019071a44020100101242101c84822990b0412281d42d88540d4984040c811401800e100b0a45490309524016152001100110700359129aa1001701044030480000e010080c0038000c600c091980138400070101d007480039420350355020704d0b065a81041103001c1e440c00e00c1c2ca0400707440c0c00c9050000d005401c50360300c0c0c00b0a4a00c40c034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 945484991 1250 945483741 945483827
    0x6031c02030f03010e061203131e03061806200702010815040912111b0d030207030b07180b09130c030213080105090709290402090904060b010807 64
    0x312050148442282d11280a14080c0c0f07807a040020a5241c07003401c0241150101c0c14405c281d80003003203d1030a4914105410055513010f2003010504890645060040c041640c8007620403407074003095110b034028100618520b50701803041481210f801c4041d01048030035000d031010a21008024a40055001c0c501e07065000f0013400c0309001c80d40080c0d000c2800da40340d80400700e803001851070703100030317030303e802c56000040020908004c1c1160f56840c0030840341c9500860380705205880b00c0710b11208251080140d940034591106101449003400c3d0307005403213840c1503054200e10728500300380411071a203441c064489403180203203c4080084ca10916200070407252b040e0b103007055001c00c2080e1000c0b07402c4084e10020b004010000032145002e660590500c181c40c1c012101c5c2606280c6903c0d03040c40500c030925501c070800942400390501d00d00c0000c00a10840d000660400c04010402c030600155600841c0015420303201e040c3c56541e446001c49544100403134051004844040d40b900002540c1644d500c0e02c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 945486241 1250 945484991 945484993
    0x1a03041401090b040b160806060906070f060c08010e010e1e060103091b0e0a051015031811100201090507210605012711030f0c070c06020708010e030306031c02 70
    0x1030042c584aa2400200c00c58007a0340004904042c060300007070329008181c0e1101c083c508950030b402c01000140711481075a03003041c41500f012500702c0a0220070889040f0841d80000104a007140b6850060510803091250b8441c000694000181314038a01000f28410240385400d0b5003007042c0819071400440c0d025080320304041d074508800e0000b40c0740d81e000080c51252500b20070102481c086542c00c4904004240d15021420702c4c0c14004443c42e030b052100c0a880802802d0040002e044000314000c00304003041107526501c0c11050414000f401e286a1316042090780d0702e01901d401010168241d0b0b540c90703801002640901010401d403881d0000b600c0c1c01c08200601040191440e0701c1d1142601c40a03002b402c01211b0317114294607130b40c0c038840f00d035600c007800c8d80c90601c22180420001c03d9203000081c80100300300040c400041010b2040d03c1240c148981c49814a1216074650f98020350303d40c9140221030703540d1b113003945000c0c8603080041a41e00c41c0800070001c1c0514464a100040000c072103036105429 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 945487491 1250 945486241 945486251
    0x806060a06031a0103091a0103080c0c0a0f061110110706230c030a0f02030420030723120109060504050d03090f120c0506070f0806040203010e070309021f090f1a03041401 75
    0x7071f0761000541500a60080f0052911362070a94082801c248560741c60740e205040c240f070f04002c500110303284801103038818200a2002e6110702d129508000074a0500110381e407601c6100c4d18603e49410241038540d00070b000070002004d01d07403441e2049034140f0005070034080f0f03043e0000380044141c10041d94007400c14070340820490f8501344a03400380d8109483c1151401004800300000c032004e11001128000120000c05105103060078000c0a129801d803190b26600e0508014503158541c1c0810b03510090400c4002c00280255060400041905403800c407503c2c0610000030a04034402d004e05000a500310a1341d10000081e40d030b41d06050b0002e00241d8062100400d041c0c400300c2c8040c00450300c5107510b03865403a10238102d024024044040140300c184154410f0006121841e00d203020303903a10244034200050b1801c0f81c2d00002c2d595400c4002000c41e003007640ca0340c4040c100d500501c031f181101c51210b03a02014607201c0700702104c1c0a01907400d07071412000a20004002c6180111645103100d10b030000065 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 945488741 1250 945487491 945487523
    0x10606050325030213060909180812060d1401020a0e0118210c080f19110f0d080c010c02102f040e04060e0c04050f2d010806060a06031a010309 63
    0x22a12035401540407c200d1081000407c01d02c0c01642e1600c0c1941103031007842800b41c3d590750803502500200103199184000025502c0e200c1200102d0242d80100901c20251419034a060207075214004050021300e54007581070070303540101d1031801c02c8031141c0b40c4010091300340161002680011440041d20300b034554054000308400c10304907000b81c42040f010744100b050480540d13280420041081c5520555081c040001c0707241d654008111007070817541c06250740b000e44005000c130702c103682d0003070100c2100044180084d44154060a00350351150241ca1115025422000460340d0300c10700941c680f0740b003810081d08940a40300c6040700c03441c151007040c105a2544c2c03809000d4042110111b072002c0e0703a41c60104020004200e0f45540d540308031818800c910700086a0141114054500e0243c8501c4655084014482c100d0082003a4070a800910b480d40e52120915540c0b44140da060b401102456400700d4814403074040c0821640d038086501c132000a41350011130052072401801d5810b014100702e801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 945489991 1250 945488741 945488767
    0x11a041a0d08040608100609090209041d0303150a03020a0b0f071a060a050906130506040e10050709060c0308070e0d15050402011b020a031b15090303020106060503250302 75
    0x800301c98014281e0070b0b00c2c1c81c00d00c0406882c00c40082c010004084e81d00008001c1705921000780410b03608516030241c1c445900344c0c0450302070701010068454840c3c0e005000403e190300000074600c201c205000003244035034607006004c0b80d41000d020194200030014418440540e00390001c2207030100034044d0030f140ca246034403141d40691a202160b40154000b90601c88140307004c04054025041c12215003142e42480000690901c0140c600303804916102c10010300e81e55160781c400140e48482905894220001d0b8000c1c1d002480101c1d40f00d00401c22407000441c0c4603100702640f12110740c0c9030700c9003161500d03804000e8900e210403200c00350b0f0200c12408182e00080d45025094841c2c01214800724007401d0234800980b401a40b12500c40440b10050303206400340c0c0c0d48640b0300c402c99412241d50b0181c00c00c02040d0458802060b08107025107014040301c1f014060384402030b00201c0340251700030050701d0745444048a00344801d4465120100380036030703180e00c5101b900a02006481c5542001031070945144010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 945491241 1250 945489991 945490009
    0xd14070b0d090309090b0d06051b0d02030417131a130306140c340b0103050a06050c03010509153106050307030b01030b040804180209040e011a041a 65
    0xd441030340c1c5680e00241010742003000d913800b91900c0441032002c000100b000c95040a00048003811881e1940007050700340c24445c5001491024000005550784030107100e610203584142c4044406042e0f041400300003044010603510056002002d41460501d000909040c5161941405440010401a46c51480c810202c4200114800c2038081540011b4149180303e90030700a00300c0708643c40c00c0010541400c40e0450fa000c0368800340750000214240310a2007000030140c807c0051141c00d01200200a00a000a03a0f901d551b2040e50184400c0d601d0758180d0010340000c2c441c50344c00032070342d10128038803030036802402c44041e10140c00e0400e03065036040441d5402581d14101d41840c01041e002541c510768a0040740050071095000300402881d607511451140e0301484040d090201d1540130030104160401190001d00f00c00214154198030811104000c1d800688201d200b02c2c6001048089124180180001c6181c06120104036400d40001d11000c3e10030b980c18185001c0000102081590310500b103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 945492491 1250 945491241 945491257
    0x3020c1903051e1c1a030706081603020421120c0803160e0d06050601090909080a03021b0105090106090e0d020c0f0102241017030301091104231e0d14070b 68
    0x40380701c170660001d592200c031810001c14000c1d000440b00344a503c3d0806a0340c0e4200300d002e25015000000904101c00a008076000401920380303000803882070300900446044202d0043c0d079a0600e000c00f045041c0d90b40c0011450042c42504c01b07000003130304540e01910342041c0c141142010010001d5520000380012440201112025a22801e11440d5680f02c0c0e000303c0588100c050800441d4482d480b000698002c0f6024141015000121682e0084426481c0b42c10300040d08024005410002c2034640070f4299800ba0030511860821044505100090140c502515603000341241c2041b91040c061a414111140c42c158401c0e0004995400e100c94201584256400f182106038100b080701c110b541d45440c2c1c00358001004c507001c0b0b80c04124000c0102d0307045940c1e04400003000e102c3c418199038240146da1040581c00c6202060321118103035646030f040c001004a4189030494000c0c019015080100b150490308444501e00000000704c142080c402000c1c03c942c03c4459281c2e660066403456444454 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 945493741 1250 945492491 945492547
    0x418060912080703020705070302040506190905010501020c100f080a18140c010306050315090a080c0105040611040609050607080409110c010612080f071401050703020c1903051e 78
    0x1200714503456002c084941c0000b85071605504d424a203403189650362207a0301000c0c2c46941e480000c01e500b035540600340c0301c031910a003520081c0310303945000040c0100310911503640580200d8030b1046032403510350303070340606141182c440c041180074a0004948504c001411300d94801c2d80c40303074001c50f0108400401d02445100c1d8070420f04004000505032b00b040004a6010305160818600b40010340d0089150801e8610800d07a108403581c44040b0507160588421000e014a9030004020b80c00540c1034005a00c95030007100280400c0b0b40c0320b200350300310748210b01c604c00000741d200306c0610003450308600038640f080c00703056440d080c10f0321640d4400c100e030003a00030f011800000045001b4164402c2c0101801014842d100c50029030f9180c1306e41505205072031103003001d160002400380c02c004190000d84185a1844020001e40ca420034000d8025070202800324024071405885600a01041c082080e1031545662154200000d280310b00c0036500202c0501500007009000c0c080030b000301c03039800316510140700b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 945494991 1250 945493741 945493763
    0x30a14030c010b09160c05010209184c1806030b090105060a03060507021c09080f06011202010302070201021207060515030102031302120f0a05030a080c03130204180609 74
    0x1c030320796003160028001a8040d00c0700404000110450500c0000c0c00c10640c241513540351044d2411500a214050b1900c3c0c1c420b60724202490951071070750055208800c0fa00794401607080ba1205040303003007040c00440d0110329044041311020346c0313580344c03080d2010400110081180c0c1c035001c48407820710740d1202d01c407107156071410100107020b0002d0500b174110200d00b00810a500745040490b824026900010302015102c1010444141c0300300700c582c00b15940210300e0b005003000c04400602d06000ea01c10300b0054410620032000b180300c0415a1812603c03002d1240051040e16401500a90031181080e41940144105045039007600e10082c0100352107008001200d02d00451365040c581e40c18941c90b4001d030320500401c100e5a08040154402ca5011614044003181010496182219031000e00c20300b405031035180c0c8200b00f000000760400c01c40644031004c1c035581e40c600800351408122022a00304102030079074009410503030b0003040421030040d000040910307a606d5070010707284000d4046903894460 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 945496241 1250 945494991 945495007
    0xf190305010e0132060609060403020316030516050a05190e010f03020406060f080a090501020f1c060501020c01020a141501081605090c0418020705061311011b060b030a1403 76
    0x14000300c5146601e15420040b0044060340c1c241c0c4c21207402448680103c0c4c00240310701999441c8419180156401400c59440d40c91000c5403050120322480121003508c1031403811507213049840c2240054030400341c401c84000d49042c1c1001000d11400f035640f0004500e081d8046070b4001021109400b03414a50298541c240c034501c140002c548481d0721940402410504961034558000502500080807003030126100103203007842402482070304034064040c600000c406003c1c041020419211031005031007040300c2c0d0340d9a001682c41c3c46038044a03d0050704181000340002d140b1007488845502d400c4201c51507071002e005002c00c1034001703800000107a030017408e800c07a404441400000c0949810303036000220b030520704200d48080c0a540a030740d02003e10500406400b8010380e05448583c0c0e0000e00700c0314681400d1494070f105424030b0200ba0303003401e108404545103500078003020344000044a03800b440c60a031030320b82c0801480c900c100580c0c1401111510808591501d060070078420207480074594036248 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 945497491 1250 945496241 945496271
    0xf061b0106260109030801141f0905090f0c0403030809190b09012910020102120a3204060c0e0306040501020301091a06040302040b03070e010906060813020f190305010e01 75
    0x10180d58056207070b04001c45140040c2e4801b14241c119070301402145407070784802001900702540c0141511449810651940030795901c41400c01c00c881e4181c2d00100700c1e480d01c508c3c88044d54400c403040ac240070b800f0030003040003a03c11121079600c4010304040d40d40851000c10800502c1030342d488151560221001808803a82e028445c1d10940c0307420301214400022051101814a050288458466100302410386807440c000c0d011200d10254404103441c05180024402d03000b44004903100d070403290441000c40d00a5842000034000d0020720034401840d42d01c44d600d48025054071035200d410008031051502c0c0740c1e18100002c50142e407080c000542c60b5070410034403104031040400c0080380301c0560360203604140c5404084a0940b03806031800b1590044003004a45841c19a512001c1c8048d0034400000c1d046490740d00c1001a201159114200740d00c495824881110b104040607500c64406600405685003540d05071070704050b800342407800e8565a441d040c1c21203c1c418500200d84e51140380040704444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 945498741 1250 945497491 945497549
    0xc0d0c381303021002030c01022d0406020316081c0c031b050f03100e0106030c03060b1c090303060504020a02030d05010e010e0114010c0f030c05010f05060f061b0106 73
    0x28004034030900300504114070200203801844040d000b521400050b80c02c551090085803d4030390040300070740d80ca2044600d10707103002c00ca0801140080401c8420500208840302c1250b08a4500b907000f5800c100c2c01c410302c0c040040100d40300320b8600c00200413561440680c000040c5189140d01070002d804914008091306840340e4401100c980049078506008160b000020b94441c220300c1141280c907661400c070321984990044c3c01086040d05420000a1500c1c0d00d500218004022540c060005582c0c480380d01d00140100c4800b000105000001d5444a04c0c469002464040c0a482c0201c2c03800d17540c1d80030600320b078001000d010050704005000800c1c3d0301c2c1402540d0050483e40d215249540c544047e414400c0b0b0103008901000f00f503010a1181c0760303c00c0c40740c4010150403000001903240b00345030282a03018551011981d5500308042c451640e1083e2096610a41000c3c2c040303107032483d80c1820480690b01c1010803406944883c0c1c1d000308155003d110f200c0103401c290b040180000c0030a8800c9607181 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 945499991 1250 945498741 945498839
    0x14130305010c2a030e040b030a0524010605031302130204090911090103030e060304030e03031308100902061c0f0f060320010507060b01020a060f020d0c09080c0d0c 72
    0x80f0b110000d00c0350b0010810350001d4642c051030f00003101e504080024000d454503120307a40d814440c44450005002000c10360042d5800c00c0c1c2034428885401045140702d00342c1c24450800400c1040c400a03000c104501c004842e9107100a160000c040c0302c0c0c40b801800c80c0c0160300562405950342c102c00c010440c0400c100780759030070215040c1115601d556401400c030252080c0d16805000040086400c0601400d101c01c800348005040d65110b07055540c0b85060308020780304c1c5111510844d0150014900d051180c0d24074590040c02081c58004000b04030800b01e48a08514820f1603a00c404190b01d064152161450340c94025030085000c2c2d02e94103254400031004000c1d40c80300c4a04030080000b0b40c0c0c0080440c4c40059004c1004602c115502005038101010024007504990401d80740100e03004203a4010420071050400030040305071914000c4401d1410b90003140d05660001343c031025940742503050141403c0c8185c606441158580c11803240c00c0c50300c14058103403d9150b040c00c000e1882d18000300c060b10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 945501241 1250 945499991 945500027
    0x10c050c150412030905070305010f090c05092502030d1a040b060f041a0d0e0a1b06080a0216050307120f03140601030c020321060a0506030106050a14130305010c 71
    0x103082648803805148003c40840b41070564903042a801c10a05015030360007590484020401a1000d11042019204110044407a0f0340d8500f0301007003618004441902610604485182c005a0b01c1203c00400d0581c1801e241036100038080074114100c6400750721895018120400988044d00e0b0900094401e10058140b0810f414030507440802025003d42c0c007110306050302da010070a48810f504100f0312490340700f100b5840c00d200840e0300118000a100c0d181300c0c03081283e035a01c40c0c0c01c401d40f42540c2500e401150002910900440c0d281c2e07a00b03030068034001d440402a51448041d0b9a9a5840c41e80700702000c039074101d8520500038170b280e0412040010082c803400e0500000c25141d101401c4000028a964140f50781c0364071142119201b041540d051040059407a80400011245540304020465403d44145c10001000c285401c150084c0c030f04070f450a44805041242d080015a0200c5841c009182c0c1c100c820712290890680b108565401103004600000c2c0508110b031004040182c2ca0603c01d0203 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 945502491 1250 945501241 945501283
    0x20313061128170409090f0506010609080d050c01110a020d03110a0903080a0311130e010909050a0f0302160f0510230f1b030c1b01020c011b05010c050c 67
    0x30b9002a140c1d91110303990040412141402400340003656000e1500000921407401c0201d1040040454181603000d000d00100c0c0c03426a81c07160112407043c3c0030b0048050a810005a20007414010405000c07180264000498500c20440c100d6002da000900e4400059201c90400000c49800d8400e08000e52418500c1c28030300000c402c0c018025202d1484014400c1a0020b0b0611703686109a1000c035a130030391109066918075840f6065098034070a8082c50300c10140503400001e4440080c420203a502c1d40c07060140c03507072003803c0e200c84400881e60030040c0c047d401071000c072201044082e24034201400195500e40340719407c00060000542541294109020f10f042158000e620102500000f5104400d1000c3d6590310915040581e802004141d00b420503a00d401761410040200140c600040c02c0c004460f0010080001e00240030104207030540982c1240311001c601e1751040c0d0012511180da400c083c05681c1041d41c0345421101c0c66105040012401f10741002c002d003081c4643c0c1040740e890502040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 945503597 1106 945502491 945502543
    0x3090d0c0f06030203012619080327070e070c0611251a150d032007300209010803030f01050d0807030e010203130611 52
    0x90440700d2040082041d921030700c280d84c100c541182c4030342d40b41c030602c510318503580d00e5080340d010a0b40240c807025808a40d40c406000da51a00c41c821403640e9241465580b003840010b00c400e203070450301d5005c0170909058005130b440c080d81e00e5000741e403080744c031024802e440c4050f00b19401041a030030034004485807103104000e004c441c0320041094504011060340c038145d200984900070318400d00b210b02968005060b90400b40e004240500c0a045c202a180000e10f109110742412030015580345181c0c0c4000d0041054080c0e1070710100c0050016038146100d1040c03900340403100782c00c18400140200d90a6076038142c0002850340140c030310b43c0b0a5071240314042c0c0325401228400030f1800044000070300fa007400c0a050101c2c0e031f0486e1142c2d04142041c1d80c203d5440f008a00d03050b04600c0140040c2c3c0714045041500b00081c65140c4410041307000e0300210904040b89a0900549410300d604981 = true := by decide +kernel

theorem cover : BRFrame.Cov 945323741 945503597 := by
  have h0 := BRFrame.cov_init 945323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 945323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 945323741 ≤ n) (h2 : n < 945503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
