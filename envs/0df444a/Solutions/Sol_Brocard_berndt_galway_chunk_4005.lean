-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:33.037574+00:00
-- url     : https://prove2.me/submissions/b67fb497-a502-48d8-8e71-840bf5b88477

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 720143884 ≤ n < 720323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 720145134 1250 720143884 720143899
    0x20f01150918031403151806040e0c06040909053408150a0b030c120f150412080619120606091e0c050c071e230d0c0e07090302090604090f02 62
    0x1b009002100000b040a043c0038100c640c041400500c102c00040c01120030720300407401d001c8030303013080800404c100f081004003c11a0703081600309550007005101e200300449080c455001d034004010300c501c45071414600f49402c0801c841e00d81d0101c901c4048900d50003d00c06034010380c03078003103204102110154000502000010b0001c0c600e4000703450480a40c02c041d80001840800c1c10f101d03100403e2850b001c010030011900918011542c1c40c4a40743c08071400307130411640380c602060052054401d240c100c00e0091243d509441500002e400780c0f40319610914022180c0c0c0f914070b04000d628040c900040000b01030070881c1000540c0700507028800005540c102c2e954429043c5400341c000c00940304008070403403c84841c51703110005030340f10400035280d40d42c0c0e49440d202c0c001019030220303515070100c03003400786034040b50560a000e11002c8015418106c0f120420300c0408250308010316050b512071314a80d59002c04e03007882c41c018480ca0200140020740200e040c1851180403c0031112f0014102e80d0598025 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 720146384 1250 720145134 720145141
    0xb04060629070c1d0a060506070201080f060a0503120316030203090d0c1e060902030114090307060b0f2e02120915040b030f0403080906061807020f01150918031403 72
    0x60214000d0b41c1212540390f020107920b01c0b0482c0c13640011031003503014030820401e031340d01e40e0104802400340d24002400140150005400184c050650507005400a000410010349500029082002c041d0b160702111901104208c86000c407080c0c00356560045003411072450400259003a21840202c0c1e80f0028003c1c0391450604108002061404520b070054481001c22081d10b004400780090760001d03407083d82003540c44603500760482c92403802080120015490440c076075a40340050a01849078941c040c20a540504140d2518030b400c0c2c0c9550142d0f0130350301440c2500004141184400550b40d021548020891002d4508510850308071020031920003aa45506496400481c03246070444d1706a41c80200c03e02402031640107016000354842c7e1212080e03990350b0140e081e6500400c0350b02a030b001c400c0f91060500c0001c09070200d40c100c4d42e00e10584640940706010305003546c0480400d0f2445089036182048210440e100b80940002d000010891034500ca450040000c4002800711400381c0300080030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 720147634 1250 720146384 720146393
    0x41b06050909040c0906090902041401051f14070b070315031220100c091d0a020d09020d050f0c01031515091d01050f0f01081f120b0406062907 63
    0x407440103083c0b25601b0b002e078588032aa00805090a41b01c220300590800f61b0f01c0120402c40200e040c1a244041d00401c10f013120320f5149072011489046070414803840222490040c1900001041820b019150180190425407001000c1302d81d40190301d4542c540d103510070302c0000c030708001100070390025281038800110700360700c6c002d2003181602c0040328600c6541c010b0403000029801102024a2075110309503107580e9402440c204200c0d20b8041d01e8a04160800594a07a09a6001e00719000803903000040300d59090b80800e00021120000392910303400040c450074090070402c107481c401e410a2900748024181511a08100f280c580143c240c19910342400d04052071145541100800d1343e940703880d00a040400c4041a07007103081c00b40b46d0050520004010490802003507522a180c01a55031100950b41c4d502078030004000000c0e05c01550800c02c0b070002d09000518403c00880703002da400d0f0320b25401d05140400844d12640c0c4440021840404403501c2003000c00c48405070f0001e8140c00d00d680d12450301e0b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 720148884 1250 720147634 720147653
    0x70f0602031e090601150206010f030305072f040f1104051c0807080a091203050a0c0813030812071b11030106030602030708090f070506180a030f030206041b0605090904 74
    0x1601c40d0b000e8100c40402c488a0000614941280c5081d0100711046071001003c90320790509020300c074a9803a855204000092140c40107001e481d00507a060741124500804118550040300e1442c1a400c103488001d000b103160500c10078128a0070510200308ec0c0f12110350200e89402507204041c4500c5009280d0308a5010b0010503c030301c60741c00b2492950324861441c0c448900d070005e081080014651040126005601d43c50340f9905a8145e15201d0038180458400c90301c1c0f0281c100300f01e80031101440030302800d040381554280a140304048458032107403109185502c549009040030200031306a144041c4207d425159200c0642d0000c0c4480c00d04142400401c0c0504030551004001a100004004041758040e809601448401090384c0c210352060484a03600e42d03030750182a601c2241005005900d1140204078014002c015143c1d0000b90394a40700ca56035107002c18000e602581101c1d0811040010a03036541240e8142c0035110003615040807402030443c00744c5110540203804d80030218040c40000030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 720150134 1250 720148884 720148921
    0x607050114041a0c0403260408030a031413201e0f2d0a0305010203070201021b01020a02030a0f03020c0703050c03010c02010b0f010c0c09111905070f060203 69
    0x2802408001030761030482080c2541254142c43d0307054454004140b10b82c110425a00a41c1884103040c1840c0c10f5844465071204200f010390709101415031141d14603840100030700700401c1c1c02c0c8041d6490320045100941079130f01c050034484007101840104520341605c00c4151b4a2640c000c1c54802c0b001c1c4039048600c8416410302e80b8154450f0485400790a952660b14000e181c040c01620340544100210050044180003602001c0c142540d88083c10364910f030030010031402001c003c2074401c04d0351b80da49030039003264010b480942c0140d4000501d0b0421032402c031010101c25541500840c81c04813600b00094407401202400380c20803d003248602043c510036010703604500042000d07104410f81d03e1418558981504003414000d500b4000b00003041030043c8106030302141d011b00030582890b0002c00442d280a0014012180d00c020410007050f10300e050310030310b4810070103056000e6807034012841d0b80c8544807110980302c080203000c200d604000303500c02d40c01b54021a848400583c49482d94084c0b4401c10780c42c203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 720151384 1250 720150134 720150143
    0x9150f0611100e1f0504020d060b0307031a160f0c0201030f0902030d200c03070510031e0e010f0603200604090e031c0b010206160e04020a0509011107051507020607 72
    0x4800c448031914080b52000c041c942c03140380b6840d90700c011145130003030760011a4065404241c80f102500407820350b401c410500300e0f004081d610300329200d603181001c9400304481c0c0060300350350800b0000440440181c1c40f100c00c06034104280d21001c02031000f000c411007108002c0c1016110308201c4040200e175000345488603030080c203440b5242201c44c001170a0f0b680c1c1c502d8a8400c446205005003c250340070400303440c030b000d005c4d010704134050900c02400b90340d1314080044c8040560710107600540031644940203008030000900821884950301c05a825216000c00c0d012802386480e2080000851400748071280c10842041c1002010105001a9043c02180c0c0300c00065420141c0800d2040008001085014024400752004000c61160a0101c0e2040310b6442d0150b4425000b254005c1c2e1103210301c901991442c9041d640c0010f01c41e0202e01170f60810742504012039004140c01c9070542c0c0060400e80800440c4001744215440c080020703c40801d031000400449400256090079034071340304120780c48950003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 720152634 1250 720151384 720151391
    0xc03041505130501080105060702011d091f0e070e100c050609030702120105010b160809030d0f080711030313030c0204060f03050d0311030705160b0408030109150f061110 75
    0x480041c0c03240c1d0040d5610400340480140124140d0f019201c20390685102900d160304020080d801510750b8000c0300b000140e800d101c0d80303c800d065911110440e12400e10302c1d4a4401007a541640640d030414030740c200c2c5101c0d060a00030010510741c402420800075000311020405056066800c0c1c40d22044500c000c1e050b40510410000e540744e00000910010340700b6581100000c2c929130b07109080310000c0c0200400d5007030800050781c15400d10010310401a01514940d0b16104c00a4006464003100e20340250210b50310310310402c14560095049503001070302d800e101720751289064041d5140d00c0001e01e11200d0f010031751544401d05125803441640980d010300b0401c403594540050b82c0208110b1312040b24103200340c2c403440d00514800e0003070404000580d40024115249c541c1c05550710f8108074840c081440c454900309002c9090161828000c9000c0c2141666035418150b44806030380407070300c840da080d43c004441082a034244081c10409c40d80340d886c0418900000000030b5080462a174840d003034085c00d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 720153884 1250 720152634 720152669
    0x3030f071b0507181a060f0f0301080105180a0506041203060e0a05371a09150103060501090f090c03140406020d050114060d0b0102011b080108070b0903060c0c0304 72
    0x80001e084050b00c1c900140b0b584c040030721240383e805488558800f24542c207041c003035070030950030041c0207005105800380120341468400d03664440a90802d910138000303603441c1e2050064201c0134140c1c600c48414480c0252190519948072269200380140004050030f00418407007848030703c280d204001802c0a85001541d9003004410b100142c4001d0b25044c2c05e205061514281a01c64118945a41020400b010b030711304880790103050091080e1171411291a1a105024a250b694900100c0c4944103010b2031016501154000404036403058221030b050244041c0140059003d0b000b004045800480001c2345408040c407044014101c0316100e00e80c103848c42001e110401582360042c100d8002d40103002c02003680e94054010103c41c4050489400c10700401c034940c50a001c0b0741200300d40603418000401c281c00990508901d0b103900c07985100000381402d00520030220b080c0481c60003404c034a95007038145021540081e46854000d020704450340c0b400940c0b0b204041c0e00340300382c80050071408007040a146 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 720155134 1250 720153884 720153893
    0x70c1509050f0f0f1c03020f0705160906080a020f03010b0904050604050607030c0e12160b04051306030519140304061d0109180f020d02030112140c010203030f071b 72
    0x1489000d203008940a00301e50b071210800d00041c0c0c2c0603420f000c0c000818521051030407018482c010745e08840201502003005070003a800e040010400503105a006204212000b220001305051542003459071a0610f032080010820009500c0c1180b5011113000c01d59000c0c41300040d00400007641d00307940081d549010401403100126103d03218902400039a1019a90901e04a04030740e5000c64002c00309520341c051169504082d010b440c80c0c101d940c000c0714104d141c0a9012815070169034000c850400001030180281c1c200a070241701030400c042802e1000e1030455030b80c1c540350881219101c02600c040c5041b1400e02020040340301c410040383c01620759803030300c80d40003d1910810194174201900c1203e607401465118031444003c80e01e032078960004405162003248003a000381d03091910100d40034000c202c086a1103100450082a0110520301140c00a01d014054070070078540302201504845a010a0350740c0100c11251311000e213026451156989840603100c50340d5103c405100c4540ca80b11600400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 720156384 1250 720155134 720155143
    0x90c0e10021e010905070611011e050901060506071205031b03070c0b060f090708070e0402030115020c101413180e0705121e03210a11030f070c150905 66
    0xb107070001181080d100541ca401030a03510349031001000c542c0316107401c01005100c0d4111001c840100310002c41c41130200000180c1080c0b09500d5161340790f0b511070611051700f80074451100100300540e150f03400c0218985841d01b041080c0c0c0b42b00c0092000001c001052503079012000c0002d150010b000ba0b449007000a0010f0201c080910103c50300c2400001042c821310340400307900102000203151440c29664110100d51802c8042c08020034403607940da20485a03510390001e1400381004005050039030f001c480009180c9040e10241078040c080e00380000810603800010050182c0c5001c03801965954541e20306046081c455015500300f8000c41104403848080e6003140d1107141000c8101c515480d02d075010014004101c00605406500641692084444d001c9403142d000f550700341940d08000c4170701c143c00c02804580c10008082d20303c040821080c91070314401c401c40100100c107001c1c154944009007482103003029081d141031103402d403040c4080002038a1540c09450b0010f0301402060364515102d41e0700e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 720157634 1250 720156384 720156403
    0x60c03040504140f0a0f0b330901140c100204092a02030d0f090209070c1e021c11120309030705060304110d14061501030e011104090c0e1002 62
    0x300c0c103005142d2950a00f81844500810340854405881d07110f48030381c0001000d0300c03d1015820b644681840450b950384140f001d01d9000e01c3c035600e10440702982c0740440c10754039001c000b0307018800038080d040885e43e208481c0403511001241103642c810700080a1880d00c0102e1403400c1707406000003000319083c3c2c000d03003000311400c44069404204048214030015080d1615940304010f038800e00800360340c05a6608006444d1080c0080090000a030303401041050804485d0500424544d440c1c000402c0600302e01e942c2a000d4480703e1120000143d40040e008407c1c0581110a803410b000152052113000461700d144103d006002c0c0701c21500110300a5103d4102803030762403180c0a0070000041d10306100048074480c50380040301304035650f0060100241d003140003805a6032041c6140390140d10326405c201181c00707100303406910130000e5005000142030f1100c0c0480810316034142180400c1000d01003091782e094a010841c04240030030381c424210b031080308190003141d12180302c5145120454010405860 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 720158884 1250 720157634 720157639
    0x110d05031e07290a0f140708060108180a0204022107180801060e0c0a09080f010f0606051207030b0609030304030c050307120c060c0221010b0102060901111c0b060c030405 75
    0x4026510707500704400711032850802c2001d40002000948144d0b929030100c0d00c40c3d594070400140403d08481c0301e1031a040211440c0c0007203003101003440107030340e048400741d940518a00e5045002c2000050b00644506003101d00030f000b6a000f003205204e015543c500510008003100222009180a10b00104401441d1180e103160303018031300e00400ca04c1d5041c000c031001d07a81007440100d41c40c0c8482803403160359031041d024141002420b0380042081902441982c00117001d21002182e80030b034804845044a000381d00000510008100da41d811200200000d98810304500700018841c0000d00803d02500c100c88180d5410f007c0081e021041040e210002e805407030044c1d0071905282d4035000001008156140c001d030550a1041e170070003002d4803501d8411447c0348013900940701c2100e1a40a40c0d032404a014030b05500c1d03511101035061550b810801e05a002da00c0c4c100030300ca220014000d007803c0d032040c0586002000c7c0029006c6030840341c2074001114240020340340c0da9440d2143d03403c00c1d4072600316010302c0e031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 720160134 1250 720158884 720158903
    0x90c08061905090304080613030203131403010513050c0409031b08120906010f0b0c030405060403061406030d1d06160302101a15090d05120c1504110d05031e07 70
    0xc034800f4000058406542d0010000d04550b10b0307400c0c09243c04114101c0c2182144070800c90201c0d668000d408403801810002ca4146003000100c1c1010b00f0344100a00040031b02003c010711001181000585201010007a2400100c90304903050031035200d0700148010600340451f030071000400003114020001148002c0441d6043c0d03c13241c5c40300f610307254288144500c01c48104018080b000c001e100808160b80a803080301d00c0c240d0f5071008940190003652090b603241d0303666500200c2c500d46591080d944808101c1c060904490a144043c05440c10034200501048100e9521105500c986085075880035040700841381d14207144c90025607409010b80e02c003044d2030800902e18081c241e500e200740000136000707004e1403650a00f42c00100b00c60b0007400c20305030310a02204200c00070800a01c2001040b00c40581a0b0340d032007a184421a1a02c5c10002015040814400c2008042009000c0d20740109604695040e03988509050041ca103008070010f4500c698030b800032400d10040c8550003406014030400b0483c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 720161384 1250 720160134 720160141
    0x30306061611120d020708010e071a16060204060e0a0302210709110318210f070c080c01091205070b1c02030703060609080307150b0111030f030f091609090c08061905 73
    0xc0d4265274030440f0b0b032011580059024410400701c80307540805070490210281c100041c101c400820702424040c19501d550380042e0501c0071550110380f071080440c080d0341e02c801c500c0c95036005c02c0104111100401c1501e0382148802540d10080c40f060000b013041d00800c0c0440b4494040c1c1d80030765482035859020a072103400c0200100003000c02d4240340d0b80103624111250413110920110541c2c0b00c030300c40e0080e220081292000140134070305d0b550080c4c0100740050849038000c0d00090310a08582d00144a41c130302d988c04640000e280041e4400a41c0c401c640c0940e1140340c4180703250070450b10501b16580050001c01003120703203035055200c00c0845030711340d452420303c1d66100280c0b81c40340703c1c100024000c261140404000b0300010b8100a50014041c9840400c8040452155083d5007003a0b00814504034000305101d43c4669456141d500034507903030050016040b82c0920401a0f940381d2044900c000c4c0c0741c2c011b00c0c0501541003008070040c0084000d6811925100000040440c034464055600c1860300020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 720162634 1250 720161384 720161399
    0x3110f011e060e0f13020d0f0c06030e03040f030f1b230d0b040204151508060915060a031503060f020c16140607081920030306061611120d0207 63
    0x50500903181880131400546401c0d144204100c0701890690f0402c0001c200c4800191280002c112154019050b2800e10340c24250007c0988010f01d0b4031035691703030081c0028000c2c0d444000e200b008803031380002c070b0b075041c1642803600c10342507100b504032055685d6004200141412070394100110911010f6030010804c0034030000c10507514000c2c0c2d006009200c04000103030040c20036078410800c400030b0354044500d076565400c48035043c84e28110b80c00000b4013804180045410b111200301d412200700c100f01c4420b40c6034200402d034503000c3d060000041540b54505000d4074040d101113032020359000b400038030003000030341816030180d4003550b0b0000044c4101e0f50304101d00c01c0141c01c11030a0f622a003261644100b01d1004008950f00314079015103901c2e10811500d50302d241011800541441c894460504000398440d15034107060700c2c41c8880c0d103035030800c004012081d551039084803001ca160550320940114542454115601359a05180d00000d0800c0c841201600000310002d074028903608030f50225840310354 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 720163884 1250 720162634 720162659
    0x2070503150c0304032d202515080f0708040c181104060f0f0c11010c24051807031e1b06261303110f011e06 48
    0x220800c1045001c0420864a525001960001d01070700c1d01d6000a503100300282030300710030100c181c012005000c41c140c0d007450b0015019130004203080440030845495082d160786401c3c803c0a031044c4214080d42c171301d4041c0b55820006028040e80e00140314003928002011304621426200800791188580c00180b0f514480d59805118030340c428080401039140c4518044500c004100d146076050f201c0540000f003422101c0a00014683e03030b40e0b2820150343c90036000c0c01280031050b602e0304128240c44440d02013402c01c4035041d02600f0a1078100007110407814400803000f07482030f6828402060102c5a41c80d246541c00c014021500c0c44c00f02c04a200c4109101030741c410192000a082e00c1100b01444000644510060341c194069868940c80b04051220010010b04030340028000c220140d525650741c50341c00301141e403a400070001d01d14407410051106400c511503034000904000420313001c103082d4038062010700b2100a0a0700203001c01c0038451210180e036044607101025240c505800015454450311 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 720165134 1250 720163884 720163903
    0x7110c0a050609030a150f050f10050d0c081b0109090204031a0a110304141c0e10110f07050f0f13090c0302181501030501260c041b02070503 62
    0x3402480301910300820b000094008521080e454000c1102d014041005241d0301c50160000c050000b8051003280c0c004011150060000c1c1000c0b401c04c020002d138611840307503c1040c1c900c100d65490003403803d40b4001e001d44299802a241c0c60140c002c54125280c44000ca5490b2a60309072a5620710f1500c2e6220b5508900445c84098000c401d1000000400d00c980c1c2c01d081d070011018080420745020a002400d030a070310660302201d0f060001403034680601000e0068126a0b400c40302c0745000600b849a00418a03070b1102c1c0304c4d42c42469112914041c0c20b0088083c00c455920000982c2d00c0c0d80c0c440c900160b00c07000b05100703050080912030b515044618100c40203000846006008400038104000004024414940200d800104030130700840980d54440301c0b10748159140441400e146880d481a40c10300401140c098141410140184504410164880c83d45c541d001c02c0141c1c1003012030322075480c0c204100c6883c1d4103d454a1080c01c1c0004207951903002c4800075400b1517490310ba0310f4061640c3e8592a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 720166384 1250 720165134 720165139
    0x41a070512130807050d1202040f050103020307020a020301181403070c0608040807060501030f060f0b130e0106330215070c1103011a04060608011505250b07110c 71
    0x42108005074203401d04881d410034590140ca10341e4181c0c80d950101c041c0d20401c41543d00d644507658013107055521071501e40c2c142070351072010342c145841c0002c4040d00c04400d0003024180340e0080700203180300e4401c112010103607400800a0000c0d000303801c55a4548140c0352401d403000e0b0304801e100d40d0504000030889500c1c503807107100c1081551520300101da41e214050000c44a003402000520701269017400b5480c045c0d8081e040d1303e513402c4264600801100d4150211103861400d010181031142d540101651803a50b04540105603001c00000190040580e50002802500405400810340d0004180c0411480407081301c0552410248010f0f65680c40032600003051610100010704058840c03d0440605072182c0050b50800c90345500003807d54219020340c02c03600300c8040c3c0040c01460140254401824507091a41440d410f18510003006942c803e525810302c80c0c0020f0a5000180395481e000d014041891401e109050910301450410003d5510200140161000408200380410590500c0c44c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 720167634 1250 720166384 720166387
    0x40612090c0e0c1908160c021f031128171303030207080a020a110f010507020418020307030f0201021b0f01030e0f030a03060914010323190b041a0705 66
    0x406800d00d10010006201000c000ca083c82400458140145100c180d20041d1705c4180741440c000f000307403001512580341102001481d030b42d1100580ca407046402c1100700c0c3c0c0b840381d09024400c00c00039405400f0403480c0c1c200e0403900080841060b4045043c60902e03c1c138629100d52818031358041102c03d0030204c04107100e0342c8200c0d408140061200100d070a402842030801504106072903c4842c03441e0003121075000960070580301901004a10304900001c0701d0101c601d050140300c3c14000038250700840c00001d005036500d9403901000c4950307102c4010101d50040441d07108649034982648580850002240036101d03807034415091a110710109401c0c02005400c28141710002d07001100038200c040d02e0f100c0e103402560b0170b07a800c410040c0000c02802c0b0044c1ca01080c05440c009021089545101c002c00d00f2500d440300600018500b1000e0810302841c69605200f00b00c1492341c034506000105200c00c841860300a0ba00041100540042d8400c902940c040304840104450513542020110b9036000060303030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 720168884 1250 720167634 720167639
    0x20901090504080406210c020d08070513181803170a020a05092814150306090c0d0b0a030c03020306090616030c03140a020310060c080a0f020c04050c040612090c 71
    0x5ca0a03c010030f582c40c81a48140000f80194081b003224011800200140c004d40e526941440d040a00396801c945149001442c12400e8191150016014003c0107072600004448851403038268014581407128a80230014135101458040c14810700464403144190a04001900318803103032003550b08a0307040b52140c91a00c83c45508008112404054030599450540d00c81540c0f08a2100d12201070f00d85903460110034a09201000300e00455500d0300c0b039020600701f040150729107031300403501d400c400d031103d03940d48034170910100c00064000f041480350010350401d000401e01140c2202c0078122402941a0b0b0140c1c1c507003114040d01d651044030308414074155045411602c1d8443c1d40000c24240d0b02d46000602011410000d420040054641e000e0150300401400503160004070707010001d04c058101b4140310050369444103401d010303a03100c0303034280240c12141400003402031004c80e051a0005004109034030b404800110260007500480000550016408079070303030342ea1302c40e00030300c42d0704003d04490292 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 720170134 1250 720168884 720168887
    0x30f010e06062701270c050319090f080c07180605040608060f04022101092d0c030803250306080609010612060e0f060a0204031b061d0307080a03020604020901090504080406 76
    0x1d10700d025405c03002000c0040360b1400940e4800c040c80340340943e0301c4580e0ba08011501603c51605000b00c0d00c0310500c5d10046800044a030840c0140075607101d210300e03440b00030002c586030038200796502024050410041c0614454069840070007603030300486041210580381c0d40c10340c1d91840c00329001144215500081030140c504101e9010180700750300000e0069141480d00b1034255400d800080360450426000f900d19181301c0700b61100e05461140ba40c410100a03500e856516003138511014000c84000800305848002c0401681c10485000d080411922203100000b40106885d12810119015040104400c0101801180c4c1118a1003881003220707041034564100400300c419141e400380c45140c10302039003070006104641c4110144180140c81d44d00d182442007580c441e590190308620f03140c99080c080d0035001020500a6000801e904004840c1032000c20701d080340a40084036140300d249010002c15900043c0288541c1c401c1e265551583d80c2e400c062801c5e40c00075030300141a400140070602c0300e00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 720171384 1250 720170134 720170159
    0x702061612050408101a03010c09090e0a03020601150504030204050405061602070f060e060412031d180c030603010605031906140903070201120908040f060305070809100b030f010e06062701 83
    0x1040000d035010319409000c000623085440340030314140031a01d10a81001240b41c10712440344070b220118090403900c0c10f9a940251180b6050052000c0d1100c41d401208100d8800c00c10745000c0c0d82d0282c030406c09070419007000c0740d8812080761081c680f0103103880b00b00b12552000c207500c01110403c0b4013611840d0305148050340c0b80543c8880c000d070054014440092030201111300f02400310b00a4907085000780204c200445d0240c20495414052a500110803201d98800702070254001d00c4c41c25120b40300e0b200c2e10006400740c501c40c1e0040394144100000040ca402d10f03030400ca49000c1c0b0a6400704410b400c1c03442c0498290504a030040c400303400900004002d0b50150f403800e080c0c40340a43c00042d5070394050751403241a8116400c103488807a040e41050001582601c04e980e00540b0070704001d000c0d40350607054169200da24003400301c070310760729400300c04982c3e00c080007500311760086e08009100408509140035603079031007240e41e41d04c5042040c000358100d811240c092641a680c80c01da440702131382400b6641514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 720172634 1250 720171384 720171401
    0xc0210030c02212203150c0905090402061902060717100521030304031e0503040c03080a12021b0c010f02120a0c0f11090604020c030717070206161205040810 69
    0x1402c0100a030f68142d111001414400d540000d0500c81038078117504000800c20b02c001e200b03506c910314124203200403581100d440c00443d1800c4900030403550312440411500c1c014a015103558081450b25000e5594020521a2140c4095620180640c030031100200400b403054030107482200d4440d00034009424265240d03030392011346201c045030140781d0003011b40c6141c2c0b080b03501f03400080724800c60038200b904007411600800100e02d4000d0540c10f1648614030440300b2440000c01d0214001030200c0c415015030921416150500c900315114220b00c0315154140000c071154265900030201554280e60040c4030b04140307414203500a0240480340c015031902a030041c4210820b001c402a0b46000080341403e1a0810343c2c801d0800900d90f5848800340401e00034080e1840e44202e00504c14108801e000205680c2c1e1a0781103900309080304a0341b50406058400c00e100690441320014140c40d400c03805506d00c0c00401d00c41c0c110b04000703200205080350f0318021030041c00616000b5030307011121100c4c0c80c0c110999 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 720173884 1250 720172634 720172693
    0x50d090918020a171504050d1409131a0d24200a0903020d050f0d02010516140d050f0106120b0a0611100501320f090c1204030c0210030c02 61
    0x3000d1960b5180101c2c0094200c0702264142c3c1f0000b0090b4048e0b60011b05912901c03031440300c0c2c50801c5980b400003407241d4444405c00b581c041c0d41e18400c00403401d041564140100c4007900001940419040240500d0100007001425801d01c005403161401c0a100f920712110031000c20b40d40d9588540031000855202c0c0095908100c1040d0011015a445002c1c0d488960312641c0100000c50325000c50a007002030004450b400e591401d000c01c21540001400ea200d451450b03d440484001d90714503214013405036010f840102840e040400840303c8412070483d041c0d526580321040712203c02d0103034409980b505000c4c1508000500020408030b802603580d1640310380000d06803100b020442d41204201c1e1000d80c81038030a03507001c1417805610440030750769034080010400d998201c01904800308080c1c400300c141042c05002d02c4400105008504401d032042c058a4401d4031721181440c4c10010f00c00c1e03080300021f030301c10307590720b040d00f00c281d4024403841c00074261940242651a840c04d070121801c030342c1840c41301c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 720175134 1250 720173884 720173893
    0xc09120a05010204230a0b03071112030108070305072c0717160917071403030c120d0b0108060a03110d15140f040302070905060d050d090918020a17 65
    0x303002a60070300180c005414401050864184036001070302101c682c1c402c0150140020050034481c0103c0d49044a40c050424144000c111086414080c5000900c0c0f04142e03490901100124040b0320201d02030040701d005008441d441ba40b41d4003949425007001e03260101e07400903004403090030420712a8840d40080d403410811070b5030070b182c41010b5032903404031780c0089a0b105020300d036003406401c03e0000c03000d0010702d00380902c07013883d0302c03452070781c520481c01020030140d001032040c5465074040081701e40505075241a11a0320741545031001ca40c1d08207403803070340240341468407081c0e2551107613040340d2141000030800030455146884040e4128504401207400034495a000c0c004108000080120090826800244036940c01d510403803044001d044001038a00380010b110121340c0c00582031342038030918600020b540d12034034001000310501c00b030000d05070b0140c100407403452034020721680211503139460300388000e146140340e07958101c0c61000001c0d444103002600340403ca414146400c42c955407082240c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 720176384 1250 720175134 720175153
    0x7060503062101090c03150605030c04090f05030a0305041e12080903090402040e01170105070203071b050411120703020a021209120a0f1b1401050319050702100b06030c0912 76
    0xf801d441c0c610790140c4800c080e00004200700000b10700c400202110051007000700906201c0001d40b195455640d5a21540d200c51101e003c5c0585807403003408031a40302c4100c0c0e5880510324009006804202c0303003607a0042403009203294402201250510856208406111400308034500343c500c140003912032003452005206181c019108ca2004001500003005081c0c0598500185450046881e81e074182090741811b0520082d03a40000658604c2c40c1c0c04400c04c044108425820380300303034104c0da0110742c5c41810005c80710085500d40d002400409079140441e4903c0d6a41c4900350242e12900501500507840b00030036142c880501c1c0050071240710b0080100144441060020703140c00044501034800b0b401010200007013000c00500d0300e07001c0104600501142c0e151807000380840584100c607a06205002001410304100420f54007020015190108a03034100180000c2d0342d20803203000268064030b0701030191030915000003600d01c0b500782802c03e01e00c0c3c00008414030090403140b0711400014440c1a400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 720177634 1250 720176384 720176449
    0x182301150b04090b0618151e0301031a07080a020d0e1005060a090915020c0c0406080f160b1e04030501090b1905060a06111509030a110706050306 64
    0x301004210506203140c40e1410105024102d4008000c03040c4a607a0800a450038004540011032002400f00c405888001e03102666055903c114140c0700081d40790b118882d09060000e0f00a0f6043c0c0b0b00800d0511542111403000760005a01951200c011800c03403000650680740580080241356401d18005c11b80310106078a0518181541485900190f00c3c3ca040120a044c00301c10800205400d003014086200c2e25140c031400074819420300300d4259000900084103800411070240100e1700170300100000c6907a03da103162105500b13a5049860f0103024103005100460a07490015501108030851400b84100e001d404044a20407072840004818440000030031802c2c403441d01101d01a04240d50140b03003019101110702281511404120314080c180a103a07207402540000f40c507102e04003042104106040309262512300401038040800c104100141e00c0000320240100c0345041d1200d000d0545848200b544829481c020359002407814800560a840c11404e9109000703014138003c205000d60654 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 720178884 1250 720177634 720177671
    0xd061215200c030a0e031f180807060c080601050708160525060305061503060d030e0301091505060405011d04030309081902070906060909020c0c1f03182301 69
    0x20100254002080b03403207480f90400170309105044100c0140617544901d5107548138410741004179240b515620040d2501c45800d903110440d4958000ca2415119941880c02c08041c080070b10100e000110203101169295000c1c1d03003920911980400c0d10fa00b4620b1590210000084012090b101d601c00c00c10115a0f00200d4594550300c16000c0c009a5056410310a01400b5101c026040b07502440345c0c002e4410b82d1080c010150b9801c202c048640d2041d401090500316940d4000c040c00c1d40e03141d40f0b0825840d040016004210f619101c095000380440e0f5201801c01007221402d200d0143c040030610b040c1d0030020748680c4001e90081c0300741000648030b5030365110204180c10a0141200c1c80400300355001c007080d0108007050080150100501006080c420014000c00951040005c0c564003c0f8150702031050900a21007226805000c0500030b0b0144c4001c5155058a400c00901080c540118182e400382041c07084520785820884060a54201281e1410519544102900c4c2c95603100f10f8010b05000b40d41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 720180134 1250 720178884 720178897
    0x30b04061a13270c0203070f0618080a0201020901200a02100201091b0503061014010c17031e150d080307020c030f0d020f01050f13020a0b0f0d06121520 67
    0x4540c003441d0b0851100d00d030496003030711300308410740d80300f0300040000991045148010710703071012000c0342c0381c1200700b282c04602e15483e500900c04080800c60007403003a4154040e10490000343d84949604c88140400040741003a000c0c182826004a054070025080506205580e400c19100025904843d0385505907071111403000b00000880c5580204418a820002950884c40210980c18440d15209403484100a000100d906000308800c2441c1400101c02031801124918044a0356901e805241d80c9043c0e8482d2460150182507000410840801d1003803561481502400f6595000095269941070341c000801c3d010442c460016079000a441c240b01c05a01c8042610083c030203080740403000380c07c0c42c80340204502240e02d4030081040c41803075404100d802541c0d00800342603040607800440c00c6117040d5001200380840001e02c03d0b1840d01040020710103009400300400646131a0072184009070200d060103400d043d4560501040209542e128000814075800d1042039103088105400b010381021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 720181384 1250 720180134 720180179
    0x3020a091d0a05090c130b01090e0c030907061412040c05030123060d1707061d03040501020c100509150d0606021e070303120903051e0703030b04061a13 67
    0x5a06100800a080c020380342c11003004d201400c0c1c082013240104840808261700c40001c030b600c860400110380d000384800c6002c0c2c011a00705031454904a910718000350b1094556000714401c07031100041140c80740101d0701c6140c1b075140c1e032645800901d810070702800b680a0001d4601e5407212200184a950921031482440800c440c0c2c9a60004045050001814000c04890040d550104800001010a02e83c441c558800d10303035144d107442403810b022000706001d000c803a6681d6201c102510b0440c10000140c0101d450907030031183c240c4414018841c000d100c942d185408a402030004200ea840c000c01520f4034000d949500c1070030b02442c484036100361307000d41d8001400358225014900502d046403115100340031004000b40000c0d483c56600070308404a1001182881c5c1d03541000314105841681115003084841003103040204034001000d4030380d80301400441c0441e18185032203060b41010300a400498088885100340d070405004186080d44c00100b81c050b01000111010400185020b02d803020000d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 720182634 1250 720181384 720181439
    0x914040612120207090501050f010c0614010f0e09010204061205060d080f09012604080a09080105160809060c0d11090306040320010203040803040201030c031d0d0e01030203061003020a09 82
    0x803500082d051075813a41201100f24109401400f07282c07284000126035200c28070702240c01ca03a141c1031080c01882200d24000c00305244200003c1c1c011202c550703c00944059039030039025911044001303400c0340f180d445102c010540c0301504201d0401c003940000e612881c05081c0103400d070782d10341e44d0410951241040882c0880302150b00442941d0180e0000f0f0b0100201600b01201c05440c0b48a81070000000e0001b49044000180c983c652442004c081004001603002801306040c542901245440b040008000141d44000045d102070b100244003401a001103c0f000d00e4881d403800c00c00d014048000e862040050100411451a2002c01c01e0134410b602030354039900d60080b041e8500b0b1841d407094000c1c1620340c0c014014000400c07454811203422940c2400e0000340340040450036409008251029290381001c11482045503902042c900850031032075450421224003180103404a01007611a590418007010b5001c0c02d51780260700070241e0340c1250401105c426030f03c41980301241d41d46070100c07162608 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 720183884 1250 720182634 720182663
    0x120e060c12041503180b0c041206020418020711090c0403050312040515091209130903082d040f03030605060406110607141821031305030c010914040612 67
    0x41866900b001240c2e034641804540c2c5c54560409400c001e04002811443c40000810707403880010741102c0040080444a03410003085080c428003e4100d0310035480c0307582c22004440082c40452080310141a8804680400b10340f01e01d041c0000e41c00b00074840c4420000400010020600810250450389110f4450040926080c036041d4180300610079144094200e5030103201c13003032a0110b02240d83e28001c6040a489490031000144076061072003000e0641071503d01c02e403051550001c80b56114210a21607594090311140c130000c0c254448a801d400c402c00d5084c00b00b00014090b0405c24504ca00900d0003180c13050b101e4001460952040e4400030229005401ca0f4080a400b840001d40c884000d0610100b082c030608075030003e6206070400400e40d002c007040866200c2e035416001483c001d220003007081940ca604040c56560354466101c80380441001580000c1354540090303201d001071410395810a0903450028048540c0701c00101403503101e0b480b03130380100e0400e502c02d410b83d50250140c045003142d000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 720185134 1250 720183884 720183899
    0x615040e010f1517100902030a0b01030b0f0c03100e09070503060705190906200106080706051809070f0813051c0305060a06140c0316060603020a060309120e060c1204 73
    0x5142c0c1e072010b900c1e204900d040e84d440382d8004c151800008034071100450710024a02c0042c1c281030301c2040050080310410004424045003050716032040d071103000f400d0744c02e40358031078440c980c0d010440c1d182c0c41032000c000082c046402e400388002c0c0c20842c0602119106a03e4a00203800c2c03241c112408400a04040b40740420300c0ca0303090042e25005141d0411207015820000001c1a82c144200c001c20f00e0802d0580c4117031088001d5000300010220b0700142c1c0c60941e11046c0040c036a40c17110940481ea55000105141c0700e1030328902250242c251030720380550984584d20103a035044c40060258210854100455010072402c0c00303030301024404040400624100c00384082c080b520080c0003540500c03800706c802d00c07803984c01c00c84c04400550007842c030340e80794411566028514490807a43d0351515003c07207000020486190045802d80b4401c8503030303030000d64483e02d01303c04999a204001d0044201040b000c861140200e00000c80b0010240c2603500d0251215500382c500440d0706201551138000150410030b02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 720186384 1250 720185134 720185171
    0x1060c0c0f1202011805010212070f05010c0801082b0804080705060c0d061202010c030315050a14010905030313031205040b0c100b01170118021903090c0f080615040e010f 75
    0x1010080b8500c945c2038108130000750b4403018076001030040da000154003014040c0d29a02c0421030b650140090001e558070450041c25490207129050051003a890300740c0150707101041058040f08403c0384000d400c42e035044100c805803000381c01952540410001c5101044085c0301551040d00c0c041302c010b036142100e40c111421900c16510411010164246400c0141e0f841000da10710950185408180d0b0b11060f220710414101d19400305900036514000040e010462030401207900c80240c9960030740340da0302d00c1491345905c50319103601d190311101d51040c400211000e40c101042c24103450001d05050f01c60b445514158400390010b1500e90100018071501000e500070032006550170318003440c1f40c00c3d601da40f800701d4034418054400f2400109224081051540d070686580104001030303940d00310400f19000d0002c02c401030040d582141a02d00104482c00006000021696410024829591080710b408200340e91506082c0c0d100e034544d039000039415404d01600400104403c40000d5070014521420b411 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 720187634 1250 720186384 720186407
    0x7030b2719020f0f040e181507090909030e281a0f030a0905060a0c020a0209090f0712031d060409021806040902270307050d0302101a011b050601060c0c0f120201 71
    0x440141740040300d01143c0411000d6040781c2380f0b01d480140c1c0e11941400c2d1000b2481781c01101c100da180c10b44031000d250384802900071002e070a8449010104807980049840c150021051a440910004c100412024105d0103840001a1060241011001c07200d4555942c0b050b111003d01c152900070300400d2000610030103400880c151410070100c050300c08041e4445140841c0039106100745c1c400030f161410244010703801c0d020f5620a8899182d04c501c095240c0c11603011040d0005990303885401640c0074076541080c4071840061041381840c3c80c00100340d010350f01005042d240b0204020314000e0381d880b0417000c0c0c030140100950150300c80399044200e603a445014201080f4061100400c3c0d0050744011a060054071400c0e201501e5003411802c05901d0200e52860012140d8034013440c40501c18807034061090f5080c17090380d50f4404280401c1c0c542201107a100d0b406040d43c0c0003100100681c0e40600003000c0090b00c01ca600003201c66596400510009969012030041641020400115030303024116415 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 720188884 1250 720187634 720187651
    0x307020123071103070819080708060603131a0907080d0309020d0b0405030c030304121b170c0c060d0906050c07050606040b011707030b2719020f0f040e 67
    0x181e501407501403100400000e82841c040c4203407100364030354540c01031003210921500190519030343e440e642003035103407080d92131380748000100c4190108080512175056035000e040000d11450540c1c4520340301c8403a4004036076007282c200c80504049030311503203d01043e82c45403649401410b64240342203140c1d820603e407402075030205403a0601e1140184d840c007103a4050b4a402603417058560f5a10720300760746144a00b006004803840023000f00410440d282c0c00ca062912983e984d10307003d1a01810346013448207983d0074003d0221320215013050107008548054003c4404040842c1c803103803002e0011820540c810350941e0100c0392200c21810601100c0d014154008040d10307402c034681145034407895202c0340c0107407580d80f05980318089800542c3c803c0c015600d00c1d10a060902681d0f0800200140003800d80c0340b5040d0003507202d80c15403040d1007441403209210020081c0107a009981d03080d0342108082c3c0342c500c0820125070910500300328a4031240502040c103c103e010562380e5040055000010740c0c001d15016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 720190134 1250 720188884 720188921
    0x7030f0e0f28110102010908030411041109060d05040c1203030608010b0303190c050c041d0c0301180f020a0b0304050312010b04032409050105130b060f013f0203070201 74
    0x10a081040b080703180c10980c0145840300e100d4507042c0100c1c098401800d016001a201005000620561000400858104640400001018500701d400798040d1403426507200070203129503403105425402060348144944024001c29807142c401e2030103185044810760029584200900c801c610134442c510840d50110b0085041c00601d1034034108078002e0180c1c3c1000c0149000050040040800079050744039401802840410013000d46841021311151034500c0ca4407698143e600c5904061103040c0e94138100320780410044020313840d200c0a18448081c203e82204601c4000a5140205800303035010f24070400c040c550301ca0004072015803101701a082190552000c00c0304200242e0700380d10512404c0b03042c1c00c402c0302240c0d00d04200030040079000da0107441035003440c04004200d601d040154850303501c1490fa4000350b4841505012405518281880c085510001d840174000804012880e400304008207000d800311248200840041000680180340e6802005100f006034080c0241c20ed1004c4045841 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 720191384 1250 720190134 720190183
    0x3090f0613061802061c020405040f091214040b1602040c08041a010b0d180210030b010201060f0b0d0b13020a030603020a05190b161b140d03050d0507030f0e0f 70
    0x15107170707110f4142044000e10000f107280d094540650107403001048020310400208515441e1000902002310084500402024040031024090300a62184500c0540450704007828040780120301d41c060303d914961120710fa000310006a880e401100c0b60100030b5683c90642d41031a2a1184850428044103852100100018007880c2d1a01c41510161910200086245441c1d02e2074050803d4003042c01035041800d0950490905401d9048515080401e90080056640d140c0106000c100c980c00345d0709000c8070410583c0c42c42d4007140c01071020704000400113074821080a0b002c0301240e100f1611200442c1d206c000030400e5203450a80640206426280e6201018131920403902e0348106000b901d20110000c5807489091007000503495806503c01c05072094182c19200000b5094128460703036140d541c984100821504081240381129641502c9a90502c00000e1070b910180200611f030780201a500e1810482d071241d907001d80700222202034081e003c1c207079624003c6da080024140c2c4069005000003900d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 720192634 1250 720191384 720191389
    0x405010b0429071e020918070f0503100b041401150806010f0206070f050c0a0308221a070e04020a030506040b03010b010e060702061e0d06051f0503090f0613061802 72
    0xf121815544441c013120001c2c400d2140031220a40ca0b00041c0d00141a2020080d189006003210210b03280e51100312100d09503103004100d003c0500d4001e054240c0c01071821114200100d40104240e440010400301c1c0d1412441b03012002582c0c04d03071160b1000030307241e030382010b490340c1080381a50007080078a002d0112820380e02c1c01070359a03000a85541c0401c0031031640030740d81c280701d00309a68441c0071580a480b4004080d00740103101c4034090305d46a035a070030702c0000c00000345900c4091003140d641c0f214410701542c0081c0c2d10b62070714903c010414002e10000544000d45991390340b005000910250b1000a942e043c600c0a100c2102d40b07007400c0502903850292782d900c2d540e0700911081d1100400b291119503901461002c6180c070f000303000c0a600000c9081d02d01061a1842130f0142110903100c000410006949504004d40400c00000380700003441c1100140d4902407088004640c048590011210742451007000d00b864404100c400840030308075090f40c4000c00695019501c558068910345100b0030b62280c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 720193884 1250 720192634 720192637
    0xd1a060a050d14101508150f0c0d23040b1b04051c06050f061302120c0c0312090d121e050402210d030c0503150f040207020405010b0429 60
    0x4015000c1000e071468030355256000c00000000c000980070a12448110782601e03050340d1214006c1807100c0c0600220070076402aa0721040d80714440622550310140c480e00203103030440c1d00000744a14103544039034000c0311103c00c044c0c4107442001c69280c40c46c0c2620317107801c041e2030040000d41040d00008901c040c0c1103031000c043c4259010b80d40b0440c2c90b03590040c0c44030105a44030750001d60081466003403100704481100440e514a201e04410349580c40b8041c0c0166020b400c1b03124200c0100789525958010403c5005008041c06640d40510201ca03e085204010041d07a4903048520036081da004442944820b81d001c49004d8020b2103030340301130001011a1402c985a14020b41c10b1141c4035644800142c1555286038840b503a020345110b400801034680e001581d190101c90101d02c0203382080e1100b110580f096080724805c1c2c2c0c1315102c1c050342c40d02102c200711700101d1441d822036010341c00388505400369407548250340c020080380900381c0c1d03900d14004107016000411381101c00c0021141ca140b5000089600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 720195134 1250 720193884 720193909
    0x1e030907062723090109090501110a05070b1503030714010c020f150402180702010b150406170c13080304050310060605030408030a150b0a021c0c021207050d1a060a05 73
    0x2051122110315042d09986035100184100c3d88042200f00001b900311455125a58150184000b44580362120300c80700c18511492039424006901000950045509140301c1038000030074910f0344502400c3c05002904d13641100ca03098552080361143d08072003441c00d105030004001c003800034201c40d039100b080b0140c64131240d159a42a0b0801c2c0780c0018215500d054002044c0c2c210342e0001d0585080c6800f00900034442c0d0030400b405038034014441442c02820405031421506036036648100c4418034498094507460107010084008428421b188a100c2080300242c09000910001c1d41ca80340b804003090700c0d092040b5507280506160610a0040740e90100c1102e0740290059106981d81c5c0320300394400000d106d030340301340e0010584041c3d01281c4012190010700b028001035007200c0440c2000328400c01c582c0c0e15102c0082c0825040125500181818040750920b40209020b5540f565030301d00c0854003000309504122558065507101c200100c007040b0029400400a0b50342d00705660424010428505144 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 720196384 1250 720195134 720195149
    0x1a250f090303120b04021309050604180213092f04051506180306160305090606130b010203041d04030908030307080103080f090d08130e04171e0309070627 68
    0x2a041d400c6001044d0400e08690700c1c0900308540e900e50710b050881070020103000c1d110309a03017404082061031415000702c0e0590200c06c6900030f00c1562950030001c1d05008070501e07803600e5031110341c43c0340440c18010307501d82003003110040400241c0080141c12420014200002d2140d89054140709007104205002e168040041ea51195030716048250000c40c5802150b0059041c42200d01b001580292155224034a80c1c098400f44403039180d040e061600d90504550941d044082e51888019544242d085000c1001060040d2841d103501c2e1000b80c08644980007100c02001079070800c0c00201907002c1d90030001814618059400c50401030401801c1700810302c0054500351003c01e6280c2444500340454806c4880100030f00b000c448540f034a6007aa4120b09501200b201d81280001410049640402c0c81958881c694504d100c020302c441221541226007103441c5a001c400c0c1e1341100f407148a006500400d140c1d03005080c418604503000382500402135004070314800d2945111400c0030910010400d84081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 720197634 1250 720196384 720196397
    0x3092e140f0d0f0605040b0d060216020301020d0b100903050a0b070918091101021209060f0712120614010816020f032206020106050d0f1a250f090303 66
    0x12100c201418014a0a82207008a00103054808880e042c0d014400300388407508184802c6548034204011a00c41605046c2c104001d2040500042d20641c002c24141c41c0c1c0e000c141c802003400d500800c2c01c9801426000703144950702c601052003440c040f5080038003204103142010b20316086940c1c480d10b914290000a22203da180042100103001d10080c50162180810005081c031403650450003a01400b030064800031000e42d000710543d40b000c01e4101a21850804403403500d242001482026803000e041840d001005000c51000070344000a0450350207541d80c0c480381d0024080360000111002d40d44108580e22020005010301d0360008000741c0e000c900400500642214890143d050001800c415582404005554080414401d00c608140d2501ea042d020f40607407140401d034201d980d280282944001954503000015801c0c48200d403815124105d46250078545100302c3c0010101130f9a280001001e035800140043c0701200708924124461a042c1404506000060503100440c00041c040065 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 720198884 1250 720197634 720197657
    0x907030605070203091f090e09150402040b060c150c1e0903100e0708010f06061b030207030f03050316081b130302090a0905160614031e0903092e 64
    0x1c0c4299501108054542018400c5464002d00b032061407591384400300700500e1000c01c01620048c500341c4980d00e11401001e0b01400340080a404000080040341c1c46512408418482e480394005041807100031001040001007400c500741e051103000b414070f4900740381400311403005481e01d03030400c066095501c040303a6550318410101b411f0411900c0342252150820000c84084800007480804556034640200603ca10380303120304090b1a03c5d4414480081d1040d40c0b81004c80f8910051406801d200740102d6800a0b940d9813121807aa10158082d0042800882008a80c80c02c41c81c941d03100c0311355071821000ca031030000010256010090154925034a01084003400d10a851590501035900144105114075001d10a40702800354031608440c0c81c090410f00c50109080c59104809881241d160701c00c0c82a13054000c030859400041c012400c440109d404000200c000850b403074003030000708001e9580c541c81903080c00601686103880440c86403401000305088108018600f03080314a5103064418070b107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 720200134 1250 720198884 720198887
    0xb0d03030515030615100c0b16121103010f0914070e04111204060e0a21090b0c010e010522060f0b060a02060105030105070e011205071103040b041d090703060507 71
    0x2e500007220340d014440c0c501032221540021880260042d02120122400400d924041362507064960000304020711400c0810040c6011000700c003038440c0d0130701d42100d45c02400d440701c00540d0300c9982c03070a82e58a0000014082220403030300b258050841400b0130301c181c2040d07490003414000024040801c001c1c3e481081c1080755581c1e008440f801148220700c0b5101c40903421100000c200c195406c50343c8038034000004044810226450400d681c001400f029103034a0700780560501c803c0e0107141020010100340100e4001600c501408542d0440f000000d031a0310318000d118211007015011801c1200d40220800e61400c2020031a0081caa0256000c20341c0c00c1c0f001c0709440a800040701c2d8651003e408280609082c0d8000ac00c54101c50044001b44a40e8484035001d49504c4400003041c3c0c00901d81c040e850354100701d160403e64214203549444042e1805241c8124255002a00160b00c03e00d130000d01041090101c44100d190710f0000500c09810f4200300d20780b41d036a206a17100041c4860f03200c0b4002030405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 720201384 1250 720200134 720200161
    0x50621060a080106061817070614090405010b070501060f140f032e060f0e0403050307090302060c031c06061b110405010b041508071211070501060b09090a0b0d030305 73
    0x400c0b60200034444183c982c20058491400c202848120745c50390b2a001954210003203803100440c0910001e07080030740c2401e1040f121741c000340b0106141001e0404c0604110b403207510550780200035911802d600d1300c04a191150a4078144e030b0155070b89a0094405202048104080101d5440222083c56001a980c0046400d0044c0030101344a10a0311501302086440039041c13840b80401d244508101107505c40c502c118600b00300740160720801d1401000600000d0041d8001d5030014924203201e152240e4030783c00200582d0150808130b40c140c0000c0356068424100000030141c10051440c10700210741481401040366400c0c0315800038240302880704405000741b50805031b444e00d90142c0300740659030b141e1880c10a96800b5105000d4203404154004400510862000303004030150b0ba155a80e40c44c0e504036142c0a0729000c0181c21140f48200308000c0003a009202c0d030710040c420080d0554407241c240d4200817941c800104070100c41d40c01e040e01c00030716a48034800e0200c0c00e40e05003000100340c0c40d1001c4600d0340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 720202634 1250 720201384 720201389
    0x190e010b010212160b070905100306081b0310050103030203090f0f0f04020a140706021803010203070c140102042102010206072102250605041502090901050f04020928050621060a 78
    0x40032045d081c814800d85c000700c5481030320750503188020091584030045045400318852407040b42c02c04105103405607064190341100110043c200e940c0e000d500030541d0b0842c2d8003a44100c001da400001c05400504000c5460300d00564100c3e0803446030894480401d00174245c807019103105a9000401c0f0460038021401310100c41c10b84c0d80840c0d260001860038100a60141e2805003012080e0a00713400e00346014004c0324401d03c11541c07001444200359848000e041e510000b0a075480d5020700c07001c6220340c00708601c1709800107981582222862580000b80c2001d0300078042c4003c0103140c454203103492001c021110701c000b40080e0010380d151a2120b107010195811082003242c0c005040800c000c0c09440d411450055000e00b420200d00d00111098100700c0c81882d001c41d0300305005030010009490302440c0303010040300c058405403070804010005041c40c04d8045c0407d4444500c072805200d030b4000541703454054002900c6540c41c000b68000e40e242a032010803410300c109224040010955111030448100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 720203884 1250 720202634 720202643
    0x41206090c0806010e011a0d09032102031005030d140a020715020a05060105040c0c02040e030f161208040f0605041103011104080c15040b0a0512190e010b01021216 72
    0x601c070780302c1c1d06003501d402082c46101a04075036000045100c0d120f0f40380d00c1c40078008943c00c0610700407400468001a050601013a030900410780f00344e41b40d20b0320160505081048803c1c005a40386445001040100314a8200724080d41c485001c0808180c1c00802c081010b00c044201c464941d144160120328204d09078005440d0040446004504660001000c04c0027034070640a86001e030b0707214424003044403489511100062141002d840140c20241d01c05c00050b420710050301d2915444034814807040c1e02004191594840b8203001c03400b400104140968040d04030301c0c241182c0d040c2915401c241101010025200340d5480001c41c0400591a902c0303940360501600034440c80c3c0315078100840c660002e210b6407005010f91050b060240c5080c04480c071900155104141c24030342001e0b100361142d00081501d0381441801c000e44071083d0b94140300240f16503208200c000141d03090240140a5844031410001140e04084016142c3d03a0049840d080c0b100703041c12007a4403050319000c110829032503100040c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 720205134 1250 720203884 720203903
    0x1605031b0708090f010e0901060f03060e09030a120603030504090b0d050d020303090c060f03010b0c1006030809011b02030601050907170406050411120709020f0f12070311040b04120609 81
    0x41c00c00c00090080d09045104954a1105080800040d1201d0341c50142e082d9100f11081c0c01071005500980b1107074a00000d03460002502c0b13171190004414180156590702080d80081091041241e101c1c20500c00c03d01440c0c070074000c480c0786960240440c06280501d4100503152069400d242d107035036803008411a01302045800c0c004018078042e441c1e80c0281c030103003464021070980c030139541884030444040080240a00d03245130b1811850041d5a00501045000780c0500c288030202c0c02041e000e15005140100c1265954006101c00074240e50341940c08016601c00481d00b010260740c0c007145203411644c040c1c030509032a0b50303035040445407a100c10329828016600309007804180f01040c1c1c4070710b00c614421100410071004400401000301c400895004455020702404d0009400e07940260100c07000c1150000d00341500e4421040081c0c001c51000d4620100003000c1124295140c0070303000c58044000f807410f180c02d0a140b103054941c4510301522160046e084100000c11030300d03a100c04d034210340100c00d96 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 720206384 1250 720205134 720205147
    0x10180b06300903070203100c0201060b0a030509010621030f031e0b030d02030903100b0d0204051602010b1509060f0f0c060f0619031b0e010f031a1605031b 68
    0x140c48410000034104442a060000d2840c2e1000421140c200d5001401400441d100e210722101500500030500110b54843c0000a1013442e102d024000c1d2110780c0c1c0f0b0100d000e28101c03905608544c0c06501c8003080302485203005010a07103030141080b0203905460041d0440c804c25105401800031000d0189801c28400718200b190700341503021094541007142540c0800302020030482c0c0c0d034050b12007500d5040d040340100311043c50b9203a01c5006100c001404260700e0410640001e803c40e0000c071040400104800c0ca1103030072030b03030a109044141c64103d65186c07130202030f015900f2490041005075400b4440c00a1501c04000c006415500c3c0d05ca9208025942c0302c03c14403415480d400140d036031001e04168600441c01924001282d0b240d4040840c5101100303600e55111022104070100340905800359003040454003054040c0d405020340140c0030146d100d28a9841e128410304034046401001c608191309200e0062034010000c800000549400b5840c0e0311102c420103110350310084249011480003458 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 720207634 1250 720206384 720206437
    0xf130f08010905011104030309260615040b0a060f1d030118030f110615011e020106060e1509040c020f2a061204021009030b0907080610180b06 63
    0xd800380c50b1103180248070307550005e04404101d02482c0002804940303400f03800c1c040c0d81c81c804240c030a030020b181d41c01c481041c00c0c0910603081803410348190800340c408460502890910340500e006120090317800791101440c0c003d00400c804418805101000b00e241441425110341c290025030a80000f0002c020415100180740080f5000170402c501169104041003a0940524142407000a074100602504d030303200c02001411403c11000241841401c07190480110008030048900e003c0303035000000c80d14100300303014011034000d09070b5911683d8005c0640c11410039070001e499020509030b0380803450f244810000c0e41042d510040110f40d134402c035030300284281840d005a009002d0603e50002c0284040c00a001c41440b4a50500310640c1c0408041401410002c40305494024a032400c0809652a079803010b5400030190b440c030036180d018606c14402d6107018071070f40d604440725000031201c8a20f010595003450380d913200b2080a15580340e00f500030780d890706001c0360101da42d008000c10140001048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 720208884 1250 720207634 720207641
    0x90a0e010b2d180406030605040f150207080d050c041701150909030509090a0e0304032103090215130b04090c031a0604052202210702120f130f0801 65
    0x1100b502c85034440700101a04005401480d080700c000901d800c1c5481c1c80e10518084119003000380316000303640c901c000000b00c0c4062007032900483c4074180d0360344a8445414080d40c0383d101500c080a11502c10020200041c107484202c1d0705c265600741e00425180d4480703c20101d50b0041d58411020508004104044010194414084642000c85018016440e8410700c82290303c2c500000700451002c00514155140400c00c3e0380c0d20219414000c01c10143c030850031411038001d0f41c000c0f0340d0885040b40c02c1c0c00e415042c1c103203440d1140305803a08124480150300000d182189c410505590b9081c0050080d4a6083d40300003040981103414407a40d555036513040f41c4e0b004046640d10000000d1811310400c40302d811198200481e243c004003120f003010300701420401303080c0041c800d1101810721003000c24440030341e6002405004042074501050b00003100d0702c100070704900405420854000744000165059079034280d9081c0c62500c580c007500d4160800484100c007075983c12090014200c41c8002640580540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 720210134 1250 720208884 720208897
    0x30c061c0b0a27150e070e1f09081e030403030f0203090a060e030f0a050c1002010605030f0a0b01080f060103030c030e031b12060c0301171614100f1202090a0e010b 72
    0x40c41001381032003509000110103018054512041200e00106207a14030484410a90010081c001450074038074244248071889200c25100214041000c1000880304c2840040d60541700c0e40c0903209140c0210804940300d208134040101440000980303070342000e100700103942202402030305110040c0c7d1207100c0540090b2002c0342d00e0303100f446003480c01c0b0a002d40c08030781038403044c0d0311400410310007180c0c0e420003e40c041e1104154013199a0f4000000e040c2d90304018a049d40f0b412800a00500c3c402805c007204001d034140c011078480e0b40310340941c040714000021040c1c1121342620b05000c49401741d06d012540075052070181759041c071526602d600d03590306d07813034911105c50011038060b5601a081083c0e01c0c3c80e020101d4050352016001d2004000a07280c02c2da1120b1a1620401540d0482a9041c3d00a03d01d9407160805428608a55080e602c9800e01c200300081100f07103400c0288541109000040440012030044214a0b401161704a01511001c1c06440544030304000a082c2c4d603100d0b0642d42140d045078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 720211384 1250 720210134 720210209
    0x1150f0b0403021935011e0b01050c010510061b0c0612141008010b0d0f120917010b04060b040b07110a09020c030309060105120d030905030423030c061c0b0a 69
    0x60405042c0c0105210301c40c9402c61000e200b040080c040c1101f070008003240825141804004c0004042c40c00c030a00c104c0c2c0c4115100d44c0412109810000000d00d0001d0900f2007076000650f9052900100d044404228201c03400b6207807400045000d400c50030090000341c45003160450410f400d20011241c5c0e68624815140360030001c0004002c0402000105201180040c00c0074090130000c2c4080703140180d600c21500c0071800c0291503107540e12100030b04242c02d8042c119880c0d6646080412500c0c290044800910355034130801c1c01d1a00700603000d8450300c248d100c02040c0480c1115400b00c1030700c81000c0d410040006403001c44d100c003200c1c1710550302c1e50b000300e442040d1805064000300e610b1522040c030440d1004003900400c03441c640d0500a078001c0c09422426a2a88814800040c0c15403d410340d0306603910109075000524a002424103180440403c8901c2c42100d0500900c0000710520340c5000e19041400d034081030302c69405001c00d80700c004a8000c00010002003458106e4001d0a2070840e01700c1010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 720212634 1250 720211384 720211469
    0x3f03092117011203141312120314010608060312031504050123062203320303221e02030d09120212150901150f0b04030219 54
    0x100c080254106409010f006001680044501c020034031414226403043e0001600c9071600b5070071120308403183c1055000d624600d599a11b06070410401c19019810a6035604007400889040d203020307410801c05000d01300411005000282060b0780030002300a84c03800803180b1580d2030412034099007a148105280c28025814180005194410b0313903030b0003000300014401c3c21000c501850030480968007e2100201700411040d0040c0c0000d20b80300d9020013944900c40c0d10b500021003e59a2640c0707400800c3c1e0000710b4000804085594074040308503a480810f2051803042010818800340207910242c60180141d003020501e040800d0070807001c0b40e64540224201c8401e40f084110807141010a401502e00d5003042c0e2140c0401810301034014075458210005a039068481c01c200300607144805c95401500d691104900d4404400350380040e07001d031015a81c8000b41c14103100303a55000307100d06d1100a004002488000b07001219448851019017207030b2003403840b070f18890009000c0c103203a072480607c101c081 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 720213884 1250 720212634 720212657
    0xf06050f03150c070f060c02031b010e0717010e160603140405030405130207060504060c03060807080c21030310061e081501050c0f03073f030921 64
    0x103001480d1141c009a00030100150b9641d101c3c0f80c0c503039402803e4112810312409200c900040c046004261000c481940110784846044010100d0740b003102c415210a64503046254910341d101003420030036903590940d45500301c4824000d40d40108214180104a070041c0003048048440243c001c07811200709590074807000600048050720140251002070280d4001c010810290401850400c40c1c1c004040b40142080040d407203040548504440480c0c1d503c1d99507403e0b2400035098401c0001800041008102d00c40c01d081e151a40d80308441b410b240302e0260314003031506480150f2081288a44188152601d0f41840600340310094464001e0070b000c2800036041103810043e005034111030404a80e01c1c103030307640c940c8040344000c40354054185040000800101c04400300800840c42c0940e140c00065940d420356041c4034503245a44c13445e000c40300c0c85040c490007444a80100140450711f00d0700b005030030f1072114441500140281000245440c03e801c8807485200c0c0c0c0f42c0004e2b00c030801682c64240386640e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 720215134 1250 720213884 720213889
    0xc16080d08010b120a1e150b0408190f1b0603200405010c0302070801020315091305060403053106030506030a020a0b070f0c0801050907060f0207120807060f06050f 72
    0x381c24025954201e5041c001c03110b9031501c1c4c0e81003a801c00e802e0f00700051500d008420b064140404450b09412064445681c00b071211000f124102c0140303401040c40c0d003020b05204510362900900d850b20b811003800080034a0910040b000800c0580d91b1003c0006403e040000a110440c0441d2103007901007441c142e1180181c140d03100c440480400c070401c5803468181000e0054441f01c0d41c10200750300b1807085100124119400344003c5005000940d155100002d24500700414907000401003004c45114494500019000003090b6401541c94117150307450f000c020701c8000c0c0e9140381c00c1010902a0f0030488200810751190a40819140103030790900c02e680d03c0314103141d9922890a0000d41010800300200040d980d0400600150752054500701052000d50f01c65aa21000b20380100c24142d560720103029a607a400c22180e0014925414580703942c411028020b510342d01580319016454070301c406620208804042110394642d841a000c2004641051894004002a01a290162243c98840c10091 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 720216384 1250 720215134 720215147
    0x31140115052707110f1614030106120b09031c0b01030f0515090907230102012306040203060a0e0403020d080106020708060103080a09081203040501060b070807030e060c16080d 77
    0x40451018800940b00c91104a5813090411100c4006005004805d000c1203024499140743c072041490481e0610b041c01206441c0e1000403d400d4070036850441e08000011075040d285521980100045c01c2d240d4680d007160b8194031980d09120031622030000b45010050305540514411002a070303007000003500441d407520031107034166000c004c90342d02d80350f075045c061520b4042268450345040907248482d5450144405209000d01c83e15456a9031003e500d00559091043c00300310215483c1010020780d1101d064000508043d003554000d030b0300000010380da911550b41c54402000f101c1008001403605050003074448a0a00c004170010341503400000d074407803001a459050702d5505020380307070592a55880f20030a80c40b8082c00d07014009241000070b5410000e2002503801c6041e41c043c540c2d00c1c90a49040e508442c4030341c00c03d264200080c01098080394900b01650101c66050400d00000c0045400040309401610b40d0110303d4440c40c4000ca0b040d04668440070b04481d0304500311101c40040e41000e41c1c80c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 720217634 1250 720216384 720216439
    0x30f0714090c1b0c1c06110322020118120204060e01050112180212060702120708040612090605011202030708030a17041e06060503063114011505 64
    0x1001c000c0c40f003c50020000c04040202c2198841254a0700c0e1210005c00e8003030714014111100900d007000c5810500a01d40540c4441c40c010740d2200703184d89810390034032248101804d0b00c0c03480b4a1103140b6910840e405000c00000d04911460750765580d40ea202450510501e410000701c1c0200d0070820b0010300000c0c0c00781100d060340e80c161501c1547c00c1540c41190b0040c40c94080440244001d1600d100c05615210000781400240b00c01034045c514080402901d840340284210304904020010040070405000540d010f07910145170541d54440200c4c901d402800403000054030052820000041c1d15401c940f22002451087d01614125940d0f0310485d503c17406140040c101007580082a40105840c84124580c01480340d80740d004e030b50003180001c10303484007401002c55032903640c0c034420b00843c038040020940c04901d20b072a035462030502c00d20540101900c130b4145c4054201030002d0004205044003040003c0500100802020010040040301740685203e500e00545000e9800c401016003964038220 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 720218884 1250 720217634 720217651
    0xd0c0302060112020d021002061806060105121e0a020d060f0302060306040209120604080414091902030c0708070b01050405060105180108040312051509070f0801090c020a02030f071409 81
    0x30360f103003600c8002c404900740c0003240d100304641450001640da030554182c4201c01031340141847e1500003034200b83c4150803070204100d03601003001c000d03513680d0040440d80018200b05003500f664071803511441d074042041c0c000b94071856030f040c20017121007d2036001d0700402100300780034807807245d0f9004030b012841120300000e5081002040001c00c2c0d81081d8004254440c000703042c50789400f0604400394144901903074104d030003d100240c20800364405501490f0115822a402c49540c1454150090a07444042030011a40c1e004800200326140540989503d0b640180081da640c250030300d0486c00303c58007401143c1c0f103a0714150105889500c1a0144c80801d00130190a19540d0341c82001520100f038001c00c11020400e100451041404407801043c0c05440b0942c0c4a085050124041000700b4500821040c20000740201401603540e00c2204641181c038051400074800384940d000320b04001c2420360107900342c410307655403051701e00340011458121400c14240e24514a42c410400003840d005845006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 720220134 1250 720218884 720218893
    0x90606041a012003090a0306090507050f0607021201110a0c0c0603050106020d0809190803190213030b0405031201080601090b01050403080403060c030e0d0306140306220302070803040b0c0d0c0302 86
    0x240300001c0c0c2100d03522240301a81180c5c1041c0d40c802c00200025065041110388540340c0980350108a41002000007504d03040b140e002d030b0842c08001150706809807034000f070300c548829280300181020a5100c1c8009030044900e841e03403880003101c0a4400b1001400803955242d05030710001d80a40b2900c1141d06a40941d40078045289a981c0119036081015109400728010754400401c1121400201c091140c0b08051454903071a101e403140092056154130400c290740100040f040c40500c040507001500d9000c10403104a8440e0b003000c0d8650f006c0d84185482100304100040390714140014058100c500c00c48042c024812a400110b42c91302032031200901d403160030700051000601e29040442042078034903000809403d0b034161545441041c031a03820219035150424801c45070070070192042d03031200350000c20b910300b40b000c0094a40d280da041206203800324880050101842446a2002410380c2400c41c0d807515220b00c01010940c1c480e0810b00003a02c245080e251026028800d900ba5441d0183c0250 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 720221384 1250 720220134 720220157
    0x3092b02060f0c071805070828021e03010302090c13060503090a0210030209031002090604060503071407110a0623130b030a020d3c0f05090606041a01 66
    0x4141c0e0041501c00500c10b6040c0648114283c0402c9200d0082c81030443ca900070f00c903d000322004442018003184100a031020800aa050030300d44e00300031251900030000b6100110058100080c00346c500c40602000c07110007100105805040554143c0303008a41090031a03c0f0b002c0819070714401c010001e400010103600c100406400744000d940e12944800503901a00e81036400215180450791072100800d6012036080c44600f020890300025900d0013204510f40719003000040c55900442c07003084100300c00080001e52852088840c810340301d9603404140c0c1c40304800e15125800002c03600300c0d14000c01400e032002a440d8881d40c0d4902220301c2078243d400010f1300e44190187d4552080c0440001c1c48070340c490029880500e0f000451281d1040500181c0b1100d895030ba8105450750b0000342a8440c6222103440c01028280000030941510380038006c0248182c0c41c55203000d0042c0c41100707140a4508020441007101c08034030540700c3c0c0c0049904102e891142070103062240c4650345500e00007481c8070000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 720222634 1250 720221384 720221389
    0x3060b071103070510080708060d0b0703091704060e0f180f0a1b0804020906150f09090105040e1519090b0402030f0115120f081c0f091e0c0e0903092b02 67
    0x2158000e03801518203004d20b03c4ae038403600c094080c15034444000980d981c95100600c280d440300c0b10500f460414a4500d8a8541034009206000c01c28050b4480c04000b510340b041980c545400320710303040440d16401050b00d403242c0804881d40741129030344250340c1030170b00c4840320035131401e00140c003207086444a407415102c88c0c00f032003480742c0010102c58001200808d9640340c200c0040c082c19504607140c0c0f203107960320041e00c24010300b0601a801540202c0c100040340c20364460109001c404100c1002d008002956405000c170414400005500142c6142040590601c030014802900c514025812240a01c007c05481030803942061503086c1620f100c200244044510280860310042c0185944000c1d403489031075014080c0c1c000804840860800422031600c0b010b41d0298560011400804001d141c0f01501c4410411103100101e2648000d000d801500b0130a560004802800100040d0f151030714080c04040c0e82c941c40030050714800c00c0e407190030314118501c3e01044410351604401c0c012295500340d0a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 720223884 1250 720222634 720222647
    0x60501090b0f09010207051c020301180f081c0c0804020103140f011802070804140307090203012301180906090b03070b090103270c090614010c08090103060b0711030705100807 77
    0x400c0384c11070040403800200c1c2e50790080071411000e140c01c91036000d8105403040508407444103080300c0b0320b100c0220030400898080c0c601c2140301900a441076035a1341c0c03241c402d640c01c0103100d004091302c2440c4c00c601031156a441140075204e180300f070b01c04102a6414004c2404080c40071182ca046c0c00111000600003424000d43d0302c0c1e004d0601200250604003103503900c0a240c0c20503080410300c203040410001c041d2030300b0000540100b848001c1140385504040c0802600d4020201c140f01912580102130410391050321105040a035142200c42caa07a220310314280a802c0340d03c130340100c06082c0800820140b1300132035040200e9024500d00c1d85003061785801940a802c0d480b4010f5a26075484c1113a00b00d1120f26032032a0140c910502030301c0350302410320308500101c801940005408030590245d0480e6a41c206178107d105c140c00102c0305407650b240500480203400c0d103400403202d42c00041040801c00561100202c0c00d0070045060710f40341900e6506000d80c2e0340c100581c01c40000c4403c008a00c10034000c52 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 720225134 1250 720223884 720223897
    0x1503050f2d2d090c01140d06093305010e010e030d031a040209090402090c0903030d09021314150a0f061206050f030316050109080a120606020f0a2316030303060501090b0f 75
    0x10748803800c080449107411f08444556004003803081c3c5640b20010f2174075148059903080d5054004000321800c034810382d901c110000d401b4080c10f007e13040b054456940e0080110303a081000c01821941c0101003410010042c00200c6d00f41c1e1080398203042c0a64483c07030503009075503130200c0c042e001300301c29515074007008411000506800ba043e10104041c1001d500d0034402420000e48640380460140c00d14410f01504504044800705410b240c0003958905601c014003594110000c54611160a141c08001440090244d840801e03107003c0d0220008409801952440f2a021900c2c1d00f00100c80d81e4606105802a042d0076240d4580c10130800c034100301c0140701c04461501c2c060800007941110541d100036443e07100c07a1540002c28842194a075078201c880c000e41001d44014030140105002031492607580e00255030b4020005802c40030101c103007030360b0411003003490701e0701108450541c20040c0600d4801c045078002a00004c1c2000004140b95004012240481d2507059665190071095045034500da080003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 720226384 1250 720225134 720225167
    0x411150415120e0f0a1101171501020f0106090e190302060c070606090f05010509180715110114190203071b020f030d0503011503050f2d2d090c01 64
    0x28402c03401c030b1181c20854100320848120041c81c00c5c1d5020304164803d540360310900c07030400038094001c003603030b440405144d6000602003d603000f001d01e0381c40040c0d081c90584110503605620305000010b03400c003140c2241d010b0354000360956000380d0700350000c0c036a14141e100340540903034481004900701c0031809006040142c01071800141c1070742c0b10341032001500d600c172105421860302c0314010300040c43c00c07058050708880c01041d1003100c4648170003403d44500440c0300c0d0621522051142d85004c0340141141ca0341c50072023100801203180d20007205242d607042510951103028480710340402c510707007030301c2100d001b0b0702540c0b10810b503507081e2602e0814040c0f89034412604960400b41040c1c55131010000e4400d0002a82c891640384d41c10302010f1401c02440c2a0352108050a100c1440725003400d00c48400d4101100083c1c0401c4c0c043c01e02d090000d91005150351081001c00c180c1044040107400000030201d40701c10081c040c52102048802628103001e44103080302c2c0c1c1203000000059030085003000f403203070102d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 720227634 1250 720226384 720226391
    0x14041106040b190f030c020d0e1503040807051c020a0803061f0806031606050904020c010608031b011812031a031b10032304061103041115041512 64
    0x2a1002c01d0010381100b040e01c4940024401c2082c107242d0400710f549402c1502d40b40c10482280b243c1d0000307644903442d01043c0d080c004084144846a140e40000c021540350122510f556400c0034600950160310005082e641d50050f11250038102ca0084001103044000b0b9000307040464143e140d00c1c1c0c0d87e50010300500e6000356000680030a80c214891200700a5400d51035880d600d01d814001e150038200d44042e051050b0380076020504c40c140d049401c2d038092060070350700140c0703072841000c0382801020550001c429500c00440c1210a5100e148050650040e0b403a0082c082c903601c5084400c4008401d810041a199550003400d105500c2035100042c1c40d4064801c4e0803021180401180c18424850035142c1041c0c0742800483d041d003000003000700c0301030032071030108010031200060941e9074141c0d00903602c40780481d0000c6803e2001c84d400647c1140e4209a065541e07060a00c0d003807220003000c085940c01009201d000c404003440910503a421110049035a041100032241c080302c040c02d0600c2e503020070968 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 720228884 1250 720227634 720227639
    0x5150f0c010f1a0109080601062c0409080319090b04020f0a0905131403181002030f0f0304060f1109190f03050708070902040b040e040f0b091b041404110604 69
    0xd00034400303100650302010303d6101c1640001881c6003040c0e00180495441080100038003070b4001512008000410b01401100340842c3c00840b03106030701c0760201c3e409803e20401005110040d00114050403d0b2808a040c6a1030401c805d0240d075030414001d08089480360002d0054201640d06d080056001041103400f1500c0740c5050342100c60590710760b03000d0704002107404200540c1d6000e01c0b0072221840e008505103880c90104000c1c4000030700c503441c0500840c585100720b45008000342c89581c941e25510303580ba80d080c4502c4141c05d41045401359a003e0130304803941c01c20112881001480c92070091001d1a0805070000c0c00318620011840d1600381c0642040000ea200070b849058029510a50250255074900502545030041540081c02c685104000803c4451101c80c1160308984800702d0300007460340d03070781094002e500c000b2901400300c05412082094041010503000c94112082c006007000c4040d10040c4800c49a084c80820180c0d030b00d46000c00d010442c0b62551006510b0008c090600c0c01c0d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 720230134 1250 720228884 720228911
    0x5190c0b042a140f010203070b04170706050c0304110103090b010905060f030303130b100b0703030c050d0e07170c0f0f120f0105060a060c030519090503150103050705150f0c01 77
    0x601c2c1da010880a003903c07242d107080c52400c081ca10081007000d00c0254105462070f21201d20169001d0402082c0084e21070b0f810200c4041c6400b9504550f81201007001546002c2402c94402d81c422201115554007084a0100c550700070300c5101c280030b8101265000f1030382007400305001004040c1030305a00c101c0700b00010240c0c0d90100011849680f0b441030a9603510464038000c01c91400c00784c07000d85140c100701006c1c842c3c640b00c0c0c2305031102642c02d880c000c101d200441030152400d2140c0340081071050b00305403001100c0c200004244048510040c01e00d95448040c2c589243c07641284202c50741e00c80140305070b0403010700d006002030200100c028462000a00402034040c41c110f5410005810750351104104000d505d01101504010510341c01d143d49a102d291f0780007070651041040c007000c0c400c183c00035148141d20800e0032a001c0d11020342142e4070010000725036104103409100484041c460742c4004281410000c500040c0303284144c0c4041e003421000000c02c603460f004040e82200c10340d078a07103220080f070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 720231384 1250 720230134 720230213
    0xa0c1a030f060303130909351809011202010807020c0a03030e06040509041a010602060f06010507030311030c0d0f18080c100207060c030b2b08130605190c0b04 70
    0x520503240d0004082c2414585802c42d000b00304a00b1500c5d054004000c0342444503140c2c0050381e24400c0441e250b84480490030701d045460000309d000c0c3c200640d8400850030103058091040c00a000742c07101d0909985a0f807080b643d68144501c03c1d900610700b9401080001e005407114100c90704010002070801b5151004074031580d500300d07410b40e810301800c2110001010070030b80150142c1142c0c4060700c1d042c40d01c00100c2c10395810240541c0c1c104072001500c0d1090504c203274819100716104507011960303400c00e0302d4000520f4103c149024202880c0c41141c02540340300d40b16010050000056503401007600e61640240c981181403014150b0048016140144010b440200b20091207400f00160240501500038111000c8580d0140100b450385038403040410541e461000f82c8100c11500401d0ba83d482ca804030701401045078400b1041418000401c5107a040030141040782602d9844020804021408079004100003d014100c02042001714020559084155120040110385500da2881c1d800c0001c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 720232634 1250 720231384 720231389
    0x603070f1422091202010203040830011401030f0b0f09041b03050a0303050f040201120c030605030f060f0c07240204080319020d210203090109080403050a0c1a030f06030313 76
    0xb1169603050201c108100024000181000b6100860451030b10742c0c2c8081151150448c00c086480c400703600100e400c2d04502d000202681c141c10300b42000c1d607580721308800030840b00348918082400c11104d420340040134802d06503101c000505211081143c0c0381480222400035009840c504002c0300c0c030a400f00028542e11004600c94001040621220300b0014102c41c0040d03c0d00006400c1c030824040941e178072100c540550084442c00040701d449160081e8000c0100354003240d0140600c0c40b42c0c1d00c41a0001c03c109100e440f1a13030351102566100032001a02e8400e900c8010441301d0b00c0804106882d000c3c070b400d00d945900c0260010305d81521070000e185107410040319a022500180c03c3e0140300c9605100841c8410854101102c60101021405403c00c011418001e070f4180d01100151031325400b50044400543c0010145130b4980d207034203000f134860f0504403084d101140340b11070021740c61f409131030100400b150006c3e103d4110b40f1007181462843c08003904a9601d0b201c18452960038040440e0b41400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 720233884 1250 720232634 720232699
    0xf03111912030c020d2106030b040b01081207030e180a02031e060d060b040609140f24040e07030c1503050903070c0e041b0e0f0603070f14 61
    0x482400ca4942403400c414014035110800d810540071100c0d450b0001104034500c109030500105400d4000c1c4144500c1d54134410180031942841400414030104010140c002c4d070240018a20036038840c07840703c1d030700c40701c4601100b42020304000500100b0f202d4510078111010041102d040d4008002c0489188002038403c00c20156001040c00740d5904231400c0748134403011041220302d0f10324200c80000d0803a00322102c080c02d110745a0010784c0060f640c9030310000103418001410041c210301c029042d101450304491540111521342c002c107890203216031498108a40707540c10013500c800e01c5010701c0f0150000c88000d5000e4826194040002032003101104041c20070000790300640060840020152035000d40f00da08150020086240071500802c41003050360328004040c20340d0f032514902086039075404415040c21082100d07011844032445920580200095800001140c5030748040540f112124459414100e45c501003c0280c000c0c100e4034081c1401c00108403200004403080c0748855036010304030880 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 720235134 1250 720233884 720233923
    0x180405010311030c0301200d06050307080d020706020318120309030a060b01090501081003060e071805060108010501110601061112070f020109120816111002060609010b070308040f0311 81
    0xc42c64101080501d84401c0201c000b848000d580d10b04241000102c0f0000d14001c0f00000b0b400e0b11032070110340081000304400741c00c0700e284541d56a26151900b12150305c140042c0200b450000c1c00510005c141c62503018402204006c01e03c0b40401c003c0540c9004c85a81c40c40e00090210540d0342d0703001d00c0620b80301070050801054034031620b0001060a41180c00c441c1c14802c264040c02036001d00400b175101500d903c1080040c40a000500c5180b900140e680000594051000c0503006450300743c0086014420a80365828140d07216001500c04880d00300300d060180e0b1044004200d2248102c000304040700859065690499100301180415840b040060700d0103404400390300c1c02c55074016441c2000b0304001d003140c1c0818003d83c2e0b400184d0703c10800d00a81e02c6070084084000d12609000380d00c020341005000e0452440034040203500c42c9003c03030340c01d40701d841b4280002654001090440d925654141d584013481e903203075520030542d1482100c05404110844400f1140c880d01005a041452442d00743d04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 720236384 1250 720235134 720235163
    0x160b070c0b1803060604020f03040f030c050303090a060c0905060d051f030803090d03090f0b0709050a08010b130c02030f0d0207021009090507050a090312110d11011409121804050103 80
    0x261030b049000e46051b02403441001040c0b080807141d81642d80040d405208941030118904040714480398406000c1c1541c0030000512030f00702c40010303071251000d00c50102030101954640c015034441d0290301c03907250800780c100200030700c0c050a5440154444d1080912220805140c1c00e0b40001d0300341c3e0341080341c06160000c2407203500d81041003241c003580d919250501c8408401e6582c0100e002d07070020000c0024527460081500c06000d50141800744c4405050400303007030b503901c0806000e00520300b11240203030080c0e515001c40102500903402c06903115001146040c8801103441d00950100e0824200c49074207014120041e03035543d0043c1c104800b503681e8018014101106c8200b122030180985c41813100c20084c41c40050303041450641169000f01074940d4140b000c003c01d0365010003015050030a07000309003c0117a07080c1c100c0b48000b15080204001c205442c01e000c1c1c04100c4480a40307030307a84a6030007808003001ba4075002009140c0c100c82c170502c04109420320350215054400a81045030084260584c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 720237634 1250 720236384 720236389
    0x131b060c060605030724170a02070210020a02031f02070c0b2a0d260124020703150e070f080a150903080106050a170408090a08160b070c0b18 62
    0x50401400c01180038091241c0740280e02500310100c9211000002040080c2e018802c0c040c80c44c20031b101d00310307d41ea0302c4039113002c40e5071030700030742c0104c901b244118458007115501610002d0402c48241d400360042c120503c031144030414540b860800c04000a030204244d000042290502600030501c0361056a150205000850320707191025501c4400100b450340d071021a9840020072081c190001c1c200a0383c240c1003202d09441c5030002950040041c40c00000009031035001c81c00708001d020062505040c01c40701060105d0b100e0a89100c0036098980f0941030102d0282e882e8030140300032841000304e13411640e9801900f0044009035100030b90136084000d90105101c0c076128203020001003507100b00150001c1d0fa5018000f90010f01694040002c080b83d91440113014036442c03030100703a596060406c41d21306440c105116920505156000d6940e00b031000440c2440002c120340a2401e504a0001a5003080441111908565030550340c6041504000511380750100050545c00c68002202c200d1910309800e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 720238884 1250 720237634 720237641
    0x8030114030604050d0e18151003021611030c0d03170c0a050a030f020c01090819030207052e0e030307020d0207120f05030717030429131b060c06 64
    0x100c05009401410401c00020804694410388104c1414031000011440c008140403482c43c03c0709200f44642242070280d40b100d00c4a9003c40184211030a5003610b00d000303401c0382070717010300c0b800c201c514222032101000242521004011041c0083c04880e0740d59200c5000400640d4109020341c00300e00b400624921708141c88641a070b11604081005207080f5900100500754403807008007501f019a00c01e01c256904900d9011074084543c054020300c60401d41c0c2c100f24440341d2020042c40103603d22002c0c420b880c82e000f03000783e5412541186c00b60030046d00b00219182c03116041c0e40c101c26980c4107409010301c58001403184182c40150480290b0b202e2401c01406071070314140b80844801e40d8051802004004210100c2d101343c00c2d80005030a800b2141450450700d180a408001001140c603071445491118a407030283d44198061300a110351092504540e5082c1c0d400034030515800704190f80003583c12041e4030501414217104100d00f00c0391004108074074403440269042030001401d1000d403001485407902 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 720240134 1250 720238884 720238919
    0x1806050906070b090109080f090306060414010302060a0c0507150e0306040b060103110d0903050a090f0303050909040f06060f1806051003110d0c080a0f051509060f0607080301 77
    0x105146000046000294a40101030b0000c00010f801000110002030a4020381121a4029a0942c58400e40c131040b50040c0c11080e0410300034406d4000084840c82d040c01400049a25130701000a543d0841c0c00340849544920f01e52010700603042a02c400041003009440010060400b101010207a0481e0060142c03040c0800785200368455014440802e2000c2c5e1041d420410034240041c0403050200081098000c1328000c012176481c101500040c550000010001207409680b03c500b19a1a50321103100403106020250005400344100d9100d4105450103a41040c05403414980c001c21303d50780d0740240c8105030001d43c54802a01400c210b2030001004400c20403000c8441404940d0074500498180540c0311440c802701526008a0804000101c0488400c207135042070a00034130511034400b0303200708401d03214640c0d40c3e0710305000aa241c0e146407158600071075010380302c0071f030184040b400c1105220001d040c2d2540081c401c07050054a43e145030081a81e54810348210741c0b81d62500c82e0380340c0c541840c0c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 720241384 1250 720240134 720240137
    0xd0515100f0b07150b0d0212010c1404060f0c030509030f25140d06021b0c0310021204110a0902040305010b09010e010302010203070f0501021b030715020f16061b1806 73
    0x5010020004281203c01510309000500000c0e0243c980b0001603120380d070500300030b07410044090124148c0034040d002241d201e00d1a4542403940e0503902004442403066100d0500000c0c074400d401e411285c42a802c00030024024038241d4180020a000642007104481c0404030b513034025003454031040c605450200d12004010740407214246440740704481019a1540c040c85501c02072103a9080040540c155500c00c4442c82124100006010080c3d6550515a101603c40c0c402c45800d6030744a010b41c002c85484d0141090803585c50f440340d84e500d05072090404103240c0e1000c000440402c00e4451403010b040194061030010544000c0b0805000c180e0406810000e4149054001440583d8001084658103540000b01060700c9070b150a15a00a0081c80f6001a03110b0000200f001081e40001c050609503016604105084100100b01380c1244200c5012510412081c0f11381218440c0c40301114031180e00414002c507101c48005503a45890500d40f44500110f0280d9a103040c03c3c4140c000c5100141020f03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 720242634 1250 720241384 720241387
    0x40204080a050c1c30090f0e2509090c050a0908030307080c0d150e0a1b1209020102030405030111040305062a0c1510080f19020d0515100f0b 62
    0x20f401c84c01025026214000d0400001c50300201d80080720b500b0841c280c0c1c8401100f5108200220703070001d00c504494410300b04400c9002d0800b0440c05007421405000c1d03101c5c4c0001c0801c0c82009842d041e480002800341c4003d105151000254080a50040c4441d502030390360f0b6565240c82d1400040d1586140d41c001180399070040c41004151a0012003d82d003024080710880d803500308281c860409400400b03101000740e109140c0010300c42c80c811120307601500e286d400a016002c1d400c900340700400411098500080c44004d170802d1038465039803146941c2030040c41030380d10345511180882c0c00d484903171041c07031405d03500020300b0410b010f41840321640241056800070400d07100101003046050ba03610f00d843d050350000070301c18900754003048466020314940310450075518000c00c08104240c854420141d590261355126481c1000101d0020040d40b030403950080d13841690340070301c110721504c148201c1e0395214400f5010f6180344e10540c1103200d050b20403101e20045050011025480311194440c00352200c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 720243884 1250 720242634 720242659
    0x39080118110d02060c01020c03030a0e0f0c100201060b040b090406050303070b06130b0d050c0406090e03040e090c3102030c1801030b04150e01060207080307060e010209040204080a050c 81
    0x7100ca0705225186044840d01d046821500015000d4820405042000c1d840002c445045990100280d48220b800803c200140440ca1040036128240342c0d400c445540c0090041c58000d04d0700c483d29034103d074414800080c0b101d88901c2800c500f50310a4200c800100710200740c021207031600b401740340d01030075054025505080d62a41e0b0804081c40c05040740e03201f081e03010440c0c0d0300c0e44801d41c4100b5030b017000107261007003801041c103005854505a4031140d008504008010500c0c2501c1e000d2038601601801c019407030301d03150825104165a014001f00d2aa00a800c00d01040d87d03a00c06904401030301815201c0c0080510041c01140c41c0c00102010b406e03a801802000aa0514581516014051050349800d400310080c0100d009007101401582d10600c2c1c845034210791922254044140c071100d4000002e180d0302c079101aa502c02445c03003454890781c0100290740002d007141c0c0000005010700340001d400c0004401c0054282e80150b004110240d002c6a1158217029040104108a09054502c11039560 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 720245134 1250 720243884 720243893
    0x21602031207150207020d150209130605131805070312110601151d1c020909030403241b03020d2904230406021902160339080118 57
    0x1900b4004078440c0f55000c0b5071036040d501d0342109001d4856000d111010001851424140290040081240a0910fa1500c0c0660041e18490170007580d40007054600c4240103540080040d1040e00c02d200d20020304c1440703004c0050b000b0040b000c00307540714803222403611040e290b0081140207602000300083d44124010003803502e801e2041e4a0741c1940d86040b0607420345104c0000e01c0040c0354640c90b900102c001c6026401ca102504401c443c81c0c0c804c07600c0d1016a01ca04258a540c0d01581c0005032000380281c111a1110b8400d003080715090b407100f2008245a40c2c0b40001c01100c1c0c00741c200351400300e5000034049640d80060701c81c1c0d02a0000f00041214220600707180781c0c4610402680c0701c0d014603501d400c0d449036003100083e01c0081c100180315101c1503180c545000d40181d04045204104101203c003520401400441c4034001200826100c80703c003840c544035600c0000e1408082c03906986214094254503614a0014150006100c0d0521050385402c500b282101e070401881506012507021100018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 720246384 1250 720245134 720245153
    0x304051e090115030e0607080123061b070305101b0315060f030b0402030c0a09060f05070618080d05041e0803010b0c010e070303121d0a0f1104021602031207 69
    0x41c3c0051840000c101034118041d03000b00420000c05049100d81c03400c214240e075104010314140c0d00008a0440920707282041f017080201a04140c2d544820141300f10020b00d8107150340800b07a00c04820490b00f482d6a0f0361991030030040303240c1c441ca24080d181c403000ca0b030410801c03000094004103882e0401c092800c054448603446014024081040b400d40300316401070b4400e420140080030024401c5540703051000035144103034000340c5154082a480000003a096001e03418000030f08000ea140c0e00d181203000c0d5079030801440002d0811000d4800c0d20042004030350141701038130382c140082c03800040c0c4e8103150070408008040c80c90041008a00584000009984403058034110740e80e403d842512110b010b121580904001c007000311003445440800000e05030f015250b001240c0781c0007030401020031240d60306070704a41110030038080e035408090210f00003121100203400c100d0003488400225a040740006050ba070041420070b07080d02500c3c03141320035454140010f1030408010440203150030b030965505030f402c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 720247634 1250 720246384 720246389
    0x31a07050a0305090c0406060509190608131b0618090b151602032e110708030402010c080d0606021c0206060108070e0405190c020106210c12050304051e0901 69
    0x42580300c001265100e04c08000ca41d2004030003d0041c8580ca86815000305940c0207210705510403aa1b0b20010300490103500c0303100d025961540d9542c0103542d03d80b02480c00e4038002c050100c45464808600d189490003003a0888080c0000390795180c00b11030790300e40c140c00c41c1c4223542200f042035180280340d459658031182501c030000d081401d0b03e91954410702445401000b0920301035010301415281c0310101080340d0300702c01518681d04a203e0720500105410080b54180402c1c5810201c0400c8400003258200f0065030340a0704c149405d120040c21655101d01c2c0347c0040c1c00750500c00d502d5003810f105a540502c282c200311818170124441440041c0703030003940c448024080c00d040c4142e21001c640f02d540326640386000e00d00040d00610031400c1040a0102c848030900b0114412480e2030368444145106004980c00c8680400340d11807140c0310b9915400c09594520300448001d019103200050058000240610583c0141e01640c0c882c0d00e0a0203000c0000c0c280b00c10490003140f01c1104031901d9940c080c94905 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 720248884 1250 720247634 720247637
    0x4060f020c210f10020c16030f080c0c04090c230604030204022a0a03090509070903170d0e0106030b1305030f03041a090106170106080709020a140f04031a07050a 71
    0x41440a00c1c2d282410482402a41001400341c9030701100c03d03c102d41c0040a50714840310850710607040181d560b100c094440e0000828142841150701c2c0890541390103411a0041c040644d07603001c1000c0f0005045402140048039503190603e401c00c0300980607550700d600080c00c40c500b51148111000051003c3c07103103000c024810703503001c0344101c01480300302c101c8441030402c90a2211410050991141c0e1544c840d1401c0300056440300740030890303050030441540561029115010181d055030b41d441d01200d9004041d901c0e1120034000860b01c6000d03402550112503845000185642c00d60602c0070344d00c800100010780306420041200005000042243d000c6031034418415129144c0b8079203075044045140500f04c424198409000c3c0058040d0301c40d20481e801c49965061402c421006d10f402d89880b072046041507045681c0c10449480c16400803c0c21a51504d4180f030482100e040b0070310030390090481800e01b141c000c20300f401048615004c036040000c01440e41102c80c41d20500081861060100ca00f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 720250134 1250 720248884 720248929
    0xd030302090604030c0510090e0a1d0d0909060e01120b15040906140a0509031605210a03050619151103041205060a021204030f090306050c04060f020c 66
    0x145842541507404940c030042c881c9550742e0340c03030420000c040003030b010340d61244480003182c50307800340107042020407178041c8201958284d503000c286400401d0071340801d04000b206c03a0070324032010809111182591000e5290701b111a4104200070701100c00315048171803808030b45001440100b1066412903281944001807005c190349200401c010b034036000d0402c5400ca800c001050701000000d400091022001c000d1581c030b10303a22a0b601009940d001c0d10200500e4004004004081030b0649050300440e004d00100c4500b20a191800c03400d61011502401e082070010402c1c06095501d1b0207416001401160440c4600302200d0000114007064401c580074061030b5a41916024050402e420100c000e00c0162034407259281c1c0e40b03441142e9200c804940074018440001c040941d039100b6510031613500504281280e4031560242c45602014204509000301500000001240c40c0100d5200744100c07800b49031690b00e01280030b030660400001f1441550000408040c00d44c58030000c141d01d0309420321010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 720251384 1250 720250134 720250159
    0x9110406060c0b1008240610090504111629072109050d1806090e0105091806010303020a14150f0a09021302130506031005060f04120b010314031602 65
    0x302c0030001d0651004170540180300504841c2c070380c604a264101b03840f888540c1090341c1c9040c100b28100100304070b032038042030800500f4802400e244e809407503003030812034a181c603064260138892003140440c03804541601440c040840d0b07076000106910143e1403c062203025900380320720068101f40d42e40002e000e032215403050702d5010004681044040f10703006030645111904901c1c0084c5015403050042d0910828950002030030b5120b50034050807078111000e1580f259090004104c180c94020b0318080e454590f80d103022010450074403205001b10712a800a048410b42841c2070199401090303606442608103034a6400b45243d2061000e034050f034803d451140694440c0c01c0200107002c6900041c0d00b1034146020034110364200d074014150f0801069101c2c4540d40d86030200031841c803007205e06605e03004280004120505154000e05800903500003164205a00c603a8450300c280445442514078001040040040c00035130324540302514000302c042d41c5801410781d20180e4071f420490340280a0055000030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 720252634 1250 720251384 720251401
    0xf03040f1a04030801151d040f1d0c09070c03020c0405071209030302030f0c0702060d020d180305092b03110f0712060b030a020f0d02030a08040909110406060c0b 71
    0x10740c0c007140c400300c6541c5031500b401d0a004140140900855030610340030580c0c07207205800341d00d4036014403440b25014207424001d03806000c0034026000c0780008603500c84010301c2807030760080e003011925500c8800510528104004001801030003a11280034031507440707140d00100b0f50202c0c4a45000034262000b0a8070f031140c610442c0c07070713214210034240c04500c1c0040070b00030076505800840c02207864107280e84558840209840b0584540c9000950101041041d078890b070002d03402914a01030400740000b40ba840e600c5403081181038103642100060800911007a079480d00e5011052540034120500d0b03080fa4589401c0d01202503232910140c14010f2000c1c02c000120020070451044076090380581e660b0582e540351007502070a109030200c5200e800c100442040f07040000300180c0e5160010b100b090048044418000031190840042c0c1e05030240325000340111b0780c420b005200034601c42d40009080000350401b100c4c01d502e004400d40c4941c2c100038003040082d44c003040e54440301760800d041e02020b1b00c56890 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 720253884 1250 720252634 720252653
    0x60e120a0203120406030518032205030a06140a1103011a0d021605070e24010507050a08031e041515170a20090106050904090506011e08030f03040f 65
    0x1802075043c440c6526090844180f04044c1003200c15980f0184034035100e00c0720780400118658a600000d0f4414007051608081801107082449811944500500d890f08040b074100002c8030740a0320000c1d1900c070000c002400b581c1260340d00024035203040103c01d50952010314648010300ca40488002902d180b9860001400103c900d100d403889011503481c601040016643d402402055031580034040c0300003000600306030b465101d103039680c26400442c0002082410a003000b071555604010080c4084c1d00020400c2024158440c0071b50200c90322807421441d4215582001e43d280e9110341444c1040c4000038040c00100c040c514601080442c01d82084403c03030307260b46442d500120441ca030307124443d140c1c0030020942c803070000c0c001c1280701901e41c80010304901e40c624031041160070040060040008912400c050410f601e801000072402410a8603004d1500340e0a8104411210302384035446e4042c0c81260408000b001c00380061740c00c060010040d00741d140030007840035110901d4000341c0010008483c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 720255134 1250 720253884 720253903
    0x310090906050103050d111c110604051e0a02010203190315090e150609190609020c0c03011b050304140723040b0a0f0b0d0b03010c0210060f060e12 65
    0x16420410080c0506000018100070700c4103503958001e80d070030091504d124100742d96441d110031009004109000d90a80960071a02c1d031010200181850508540c140501089000f540641c006100045007180c1e00410020291007001059108042d41030041c0d80202c150340864240307e5402c084215003840940142940d408082541054100d012034200f61661001b1b030b186284e98200d0b14940b4041c032450020240503203d065101086000089211a140c101d4045000c50300c600450300075901c48040017a0b80006002d001580c10025959103541000d2044c540c10071201030a0100344008c0c0480030380f040c40060030140c00038100c05008695400e00300000802464101036042243c032114940d40c0800329010680b070300c40c0f82000f00e0b10042e0701e41021068150350b4810102154680f500500c010541d1002002c101c0a503101d008100c800c0e41c0071700c0760084040c0b254014040c0f480403030b0140d170200ca603950042044980ba4080905c80d243d48922000c0300740d0400e803900c2c48400c4510320240c2c41d155180 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 720256384 1250 720255134 720255149
    0xe06071e030210050f04061e020a0c031710060f02010e0303010e0f2a1605060f040203150f07110319030209030d080915070932030307170310 62
    0x381191040000c108009111180c080d07800e40b104905610703550010342d4410755404003815480008a4041916584161004040e104c80e071081c81d851000d405050360000003000c0f01003404d0400ca0b41c00d0503000000b03c140c1740349041d600b0340c03030b0b10308031008d402c0a0245018100c1040803041901c5040b50017544840046840c0c00c0403661250785d118400c007101344003252040c50707800c0a030000c190b000c0720580c128a09004c0c0b12b1020b5101e40b111000d003191b290001d550080303044000522420110b402440b1302401001c2c1142d14140610306401070520b000541090300d01c0480f0013030704000c00c8402c403e10190f0051420302d040c07003d1084190140d03181d4000c400003c440581c0f9803c19901054050380240243d0b4010f030241d469840d050300b001c2e511018103e4000350290003803400c2a10b079420003100c0b11b0384101e460420b50b82507502d03041e4030342421380d0542151002001e0708080030072012091070600d141c14011002549460055511006c1c0e00c2544444503103540b4000c00481d90003548000700b540601000d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 720257634 1250 720256384 720256403
    0x30509060a09081b0304060905061c270b01030203010b1f122a1b02030c040e01060b030c0711041e2a170901050145020a020c010206160e0607 62
    0xd94504c2d5125440340c0301d00c130301156032004001081d0400409444130007401c0e02e61582c2c01010150980041c14400d91038890180c0410092030000269281c0700f0042802114824107541c11441450b007124002000303544181100002c1ca00c5d8400018262030702c0780102d103841c0d5404210004010701400d131241241000c8402d20758003403c03401030b9064a03040204150343d401401e05e03100b640e0369000e910f0b030000a900f5410002596945041c20b070000001080081e000203000399440c50002c034640c01c01d5a051640c008009100c0c0284004105041021481168108840009001c0740750030000c0d4150901010398403001d80d00300210b0900c02807075007050400c100d500c01880031072004109440c0b160846120710321070008a40340a00520403036058030340001c0302e1903100390005401d01100d031090300d07446024840035681410000810040307051300c1420080168485550401c042c9c00e00d03400d00040c50465021804000152080c00704881c60842c007070400c18416440c09021524500c101d82000d410b40c0c85 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 720258884 1250 720257634 720257677
    0xa420201090b18030f090d060e100609140105040507020f0105070c1b060503010513020d02071110030e0c04180c06050318030304050a02060319050406050a060501030509060a0908 78
    0x101900322803001885142c40c03040641c0c910210380754188840241c2c40059000f0301040941a910f14000c00c81d100004068a0003401c00e55a90010344d800c441c0307403000300d812103914000c41e490305000c0c0e4009400341d8070040c01704201803800881000b0051080503c21500d03100401c0c1454003e1000d0b010200b41e40c0c1c002d0217a4a09204050305100c010202100c05455441d100031a0f01e60902500c0292605540d4461541e40307030004006030301140c19542a00283e00b0003d0358030701c409920040841a11070510244082404803c0051301c0010041c1d24083c1414901c08100d10440400d118800380821070740021001c0746120f4400b012540124001c0082d81c442c44040b0b59581c0000c082c5108001a10700496040003071480030b45c580c003042e500184560b010541c4000103181039400396910110106080d42c070f4118594140c0e05440040d1810340d060340d501e40070b119511885000d64409044282800d0141e42014040541c1e1524003c00400701d00750746030700580401240700200d030721440c44021042104c55 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 720260134 1250 720258884 720258887
    0x607050d09150201020909180f03181203210a0608060f0a0501061b020103020307050d180b011d01030f0204090b0702250612050a0b060703020c030c0a42 67
    0x1c03000d000c2c041d6001c80382d80004403403d02c1402100ca4040000e85500201d0702c4440d50445038079103a00000440b402150111510801d0800240c0141700806101148a58a84007800240110340c0d54229441d0010040b0242c4035070004038503c0d40f526170315110748c00e07645d80c1a025030081c01d194200b40268000d07131081c00b45102c42144c0d600c0c043c4a200b081002147d0741e0769000d440f40303481542480342007140d03003940700003641c02036008d560300540c0b40c01e00a18240384445103404840340b002003800c0c0616200e410ba0280b00c100035070709002d4450450183d81d1250302c80403101e0321078030500c0000d1040000100031401c640b542d0f040b03000850751005085c51203080280010791a0464251810300d42030079000c1e05e0541e0220340c03a070401190050707216400c8901070b4644030800303050010700001802da2103070302c880d1643c1c540400800416000340d010300002003041c010941001d0f00318000031710403e54220180105c21900340842c007201c1c40440c0180d001083c807026148500801368199071980e072241740000c0103e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 720261384 1250 720260134 720260147
    0x905031305060322032f10020c0c190801090b040506161b240f06090605010e01230f0c0c0d08030a0b0a031704050907090311010e0607050d 61
    0x40c5640800c0d400e800e40c9940034085140021a41e124a60f00404010391414154000440034a800f9140c240891600d4001c50082102600c1003da40b44018000c2420580c1c001c0c0b080c04600038400704254a41050b44589039561704804480510540c50002155080e80141030a40001e1640600a00850718182080303e82c00e04101e9054565008500006501c0501002c03440c4082c01c2c42d489030510706d02030003017006140b612034108480d10010182c090b21041d030380c900040100440c41c1c0000c10030461130141d40d07040d68020340c0144a8103041c440c041c8940c1c0c0c2c12542000034a00c1c00c1c41c100b0015030b03920540d051072845000002040550016400302a440004001c28810054004440544425006000b1009442c0c100900500824400310704401d44540080750310000040142e030045850303440d031900d038002144550440c0b28000600700103d04050a960354031100a04007000f5440c959110301200d42551441e0034100210212200a030341d58100541e00c500750010110f82403c8007980740034102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 720262634 1250 720261384 720261397
    0x901050c010c0507170a080703022a030c1506030604080c1207051501060507030c060209030f1212160c081c0f06030c050409051203090c030a0b06130203012303010e01090503 76
    0x441d4040e041c0003413905c038907204980340030001c2e0f52404c04964911200314001c0d040048880c0011012034080c081410100c0740030820038601d24055035450b401110381a25196100728100c54091030681005035503a0046941d95005030130541e0507a50b41c140488035403c20050540c20814008007140c100144000005c1c0ca01a0a9520044100d184d8031170205031414020700400400040c8500e051600059041e0060719400030080d040b102516007a00ca03c03410445912101444140d0201d0302550100d09050125040361442e0b6240030742c41c0400d40000c049102d0070f81c0c0981010800076440c412515400445100c06940d030200300041c00c004000d16010709420b04c0207850702518032502003241e161910809000c185c1c0706c0300500f4444c102c050200125040100810a14002d10300c0d05221500c0504c00a01c82d10702c24118242207241103400c00403050180176000c100144107000600007101050b2071215610800186c0303400303e420100000c0d0141040080005003542001c0200e400c00c00000301a00380d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 720263884 1250 720262634 720262643
    0x4141b03070f0e0a1e0204170c01030606080703050601090b0301030605151f0c1505010e01031406040c0509060a050a09381c0f0b090c03070303140901050c010c0507 72
    0x4032564907800c0703000d050150f010302c41406482d40c020a07841140d60703104215164451340e02c0000d124105116900b00d80082d40403111407401e40e0f445076801d8a052112031020402420204001030074140c0c020010030300181644245690b03400855816030007846508002c20440e900a80d5940c0c480c5803c0010304420b4460111640350030340352000e5803a0443c01040d07000741c52080280c0300007050800720340b500111001030b03507288005400d41c0659030441c01818064080d182030300059516510380703004140b01d0b8900e5004241c100c3d105000010328000140c41c00c41e01c04076070f14122500c540001401c144815484154005030b69100010701d2500c80d086a03090300c030031503064800483c0614182c4030b00b048400c2101c088070101885c2c0e888034945003130340c440f04060000040150070000e542d03c0040c4144550207132105525001001741c1c143c4c2c200b16140b00c07910154040c2440300e144d0781d80030300950040ca4401145074004a24a80a0b9114000b60750540c1038910081c0f180202e01f22000e482540948000d48 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 720265134 1250 720263884 720263893
    0xa0b040c030504020f2b05010b0114130b0703050d050403020f0c3f01061409070c0210050c0a0f1a090304030519030e131a03160e04141b03 61
    0x600c80340c0a0b210711807040f40c014200040c0c2c504128200b12001e0000c111000881a801891246410503010701c0341c103942c8248000214489201d00143ca00c00c03403103a1005464404110a040c064810917135801182c0060510356280d800920b0252054010303000e00c807080c40e24241c01c20050503800500c0309800c40c00d600984141401d1031040c040d8003040c00480079110301c1103c90072204944544681580900310f941050380802c4c10000040c292849503100b011141c102d0840d204541c07800f03095041d04280c080c01e01c41c108200603070105180012614681003400000f040e4503d6812080c888400007960225690100100701d141110300c042500184865850a000004030084000401c560640b9080401803c4a00449005a0141d9001c020440800156a10010643d1924404110200c9039000080380c1250f50652507402e0403008220f1741e200c1d80c8128443c04100250a061a040e40c1c0403d142c8501e690b12403d10110451542d040080184500d0061003040107460f0a0444510800c41c180c0f03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 720266384 1250 720265134 720265151
    0x906051311150304021201060317030103030305070302070f02040905100f020408010b1c0f0c050a0e191503170f04060512060901260f030a1d090408030f0a02040308030a0b04 76
    0x4090b102d050b50300c0e000c9030020008a800f500d040394800500d0798100002140303c58499903000783e02070720403d2151103001b010006004054141c080d55a000c419443c045082c00429261442ca550504034041d029503540da4600e03060220a01c2000c6034000d4000c0700b07104048201d4180380083d800740c8290350035540ba001c1100300c80c0c940f111100700c2000680848606807a1662204100c078200c0344012603181e0a0100b0000e0f80391151202c2c00700074070740300508002515081d03000e114421805507500310300a01d01400842d6121130100c00314241c94118100390584036203210025410301c245003400207444c0c0702140028002c0e030322500070301099a60031a060304a85640c01400700c00b01d020700030b01800b8114020100344203001e0244507200b01c40c4a0003114030343e0b00d1000301c83d1309650000c1c05900004402c000031103514a900c0740d1070040018141c800443d2880c0c56200e1008034000680007030344c401450001700c2c01c0404140c060390042c50300090441d170f40e8140070200c140100204e400c4d042c050340c188101c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 720267634 1250 720266384 720266389
    0x4030308010e0105060702100c02040504060b0906330906072603010f090e0312040506150105071106031f1217071713231807021b040906051311 63
    0x60b541250005420241441c000c1c0d030800801030191000141013045002c1380038090399031405854025030240310300040c42068142400a000b5008000030700030318441100f0200890f40c05440b135995058140000c0c0c02d03c0000404003010322034044120742c002004203080c014044101070100045840492000d1010454104003035207000034440d452852905040030407030596a40c11440300340d014541540d1900854441414410300c081d682603d15a0244d000c04c0611100c000701c3c040c005509003429410000d180d55481e0700c00703201c508001d00034039010021824000d00d070030802ca0020442040c1c1e0541c0d54881d40f41041c03a400d0754005441680b0045069861041c00bc0200d40b09240c1200e201e84405110001c107107099070000c542800590700e600d5000608600d0704035803c1c0c070680d120100500342102036040111a0103100d650100d08410041440016900000c0380325140030000e29940c100c0c0c0c0c0800000e0010401240094489410101048045030101004000440c41010301c00b400000d074405 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 720268884 1250 720267634 720267659
    0xe09010528020904061710050a1a0f0f030f03030907050103060815180703080903010c111903020a0c06051c022a0a1406040311011a01030c120c050403030801 69
    0x74941045020100240c0720894640003060710b4040503201180c41580d0b40141202100c0c5011382c62180d8000758880380140c80d0724050b01d90814800d91050000003200d02c0702d4071201c900860324510501d4030741c1e0b6005068a07684990180400000c040d1450314540f084019141d9204645034070a901030300c1c030041810341c000d10440c2c05031060b100080100da180d8081202d01c1c0e400150035040294800c440a8545c4d00c4100041f4018621504440d51101c0900090509440312401c405051041000707a80d208840000761620424840542151003d403160809030305000c070181001c2d1942e0095200450401e8000c401004840c410600c045030795003415100300102c0c0030301d507042198810190580c000106080324400b9030074030392406a4107243c050f03644e846003003001041d401c422a04190100814103030814140e1528505000092101080e58125400500d442e000704e0b9060540c2c0c2c01066000b584180031841002110040c10401c1140b0154041c11940042c401100003c00441c000b00b083c109040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 720270134 1250 720268884 720268921
    0x507080103061b0c121404090f142505070f060c020d0306180902012705010809060103030909020f19050903071a19211407030e0604140c06040e090105 66
    0x5550701340c0b44000b0303641d80540c80c2c2d810085108002c8051140d4141c2e0410000420041111400008060010030500c405560b40c0801d1902c80160903403c00c0081a544069040a1003515240840500c1840c201303503100c0c01800d101400150000c00315104001280d4012002052190216207124030607020440a44513280107580302c00e812012400f240e4242c075040324444d644141041244000d0300405820700009294410701e0003580b079041040b040d600260095044550540500384660443c0c42c00703803e01e0900d116010400b0350014484800b01c8517902039500751844c0c0d2154090180f080b50004086812451040e0b03c2405081b00015100074540300c0c030107001d1040c80c40349040c00c0101c11041042000601024148580035807981c040180842c03064603001e5440708000703603400c01c0c140000320071000200101e0130b241c9032025030000035600240d01503005520104942d0145501c0881c83d0410424500c0702e90413220100b00440c3d003810f02020103114580c40c01c020030695555841c2d400000f5401d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 720271384 1250 720270134 720270137
    0x29040504120f0504080139020307020f01030608010e0609010e2805120301080d2627070e04060b01030b01080103061505060711040c05091309150507080103061b 70
    0x1c07400e036900c5010788841c07090180141020380c18907039540000c600303450300312904164803025619080b40c05252804a04240c2c181c0c052200a003001081c0003954a1103001c0d0003074821010000b4440d1107a100750071000c00f40034500300900001a105081d69551602a02c0700e2509508110044003013040c00203803d59070501240c1f0079680044118217803040045c4c0c6090a0b54180940680302140c4800c0790020750003000184018440c01c945d080b402070000c000140b0050340c00000980365103901142100051b0404d4051845284041080040d00d508100380c42001c0140d0003050f030002040044100041d01c502c0c0500c1003803150100c0340307004400710390f0440783c80ca02055107040148003007500b40e840305c1504c0f410042440c503c80d40b01c20008006422000301119295a8050295030342e0810b401580051121402c3c030030305000109000984208105520421540c1d03035000300303000d00c94488802e44a08061b601e007080f00d8100351000500300002400309441c0241080c1c40381d21445190410906580030a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 720272634 1250 720271384 720271403
    0x60609040203130c060914010f050a080a06030c180f050103030206281b2304151803060209030d0509060a0305130c060207170601080a080703090929040504 68
    0x401000b504040c100000101d03c0303607800c00000719020310f0440908401e8550000040c61300302d0a650300a0900314a604001c107214400020340e4020703094881c142c03203e0401d202035540d0703021140c3c0100065400030380409100400003c01a841d40d1442d094454551020b00c43c000c0c10503545816580c0a02c03005005a12880000e40c0b41750060b14500c0e0b8021001603007112400c1c60f5503890003521521050f0b04104081130b6000d068040e00641154480025540199100d2551100e80c40300b9001c1c911072900400c0c001450062603511451030300c13408225020b21008019100c0c201800250802c0740d816029209442d60503055600a1003641e01b0080010540351400c11400d000b200508406400745800000101c400d80009030602d01000251110740d008280c2c00345030190f9200c0161480c00c038010a81c0110005000286001c500c030a80250403200312661707400d091030111805c001070360162081600c1c0c8140100709666254211b001a06411212481006000b04000444505540c0240000c04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 720273884 1250 720272634 720272647
    0x50f010c021021180f08160b27070e0601111209011106010e060103020702130e0109050601060309050309091e10031205180d0c050d06200703140d0f0609090c0e0606 72
    0xc031114400d0030501c52044542030a0120a64620f09010800110b800786c0c4884100b01d80279400564068a80c440316190480c1c0281c901401501d615042c0103291880c1501c000103115030340900c0c0041400003071300c402c0303819010020118100c590440c103580c9000690301104101d40c00300001d100d40c16030f40e010788414459200c0b04d006500130340c0603140c200d07001840f0900c0020354040d00c0c0320350090300081e940049085161481c1560811030160003a0041c035140892840100e000003082d60115001569042c006444440340c2c520251415803202e2040c0001da8200403807881d1946003442100d02c24006e8000310100c2c002c040d2614060590301441b003501d20940c0356018900307070345c0340703041e090054800c01001619180401c01c00102d044060755015101e486000c1d02e168281000156032a84195260502c9242d079001000c101c181c0c1d044009080703010451b0328402c90380f980405001080c0190802c1480d0b60b171803603100603183c5a401581d44041c205800a07a90342c03800907007807103420004c0540b4500072 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 720275134 1250 720273884 720273893
    0x3030c02120a200a030b090109030305090714011206151808060f130311060a020405031624090b031018050c040614040f030c0e0109020f04050f010c02102118 69
    0x3031020300f078140c1c0544020300000126490382c1440340a021040c2c00803032500f500781406810b13039001405e030782202d60042000300005031040300042c1100009281120700d40012074202c0024000c01e8010132002908e680303aa81400743c20080d2075260b5035651406c014101c1d5100b100b56100e840072900c0403420715107440050025041c04108030080e038400e0a040300320045800540d46010011110101c0381c50f4001014847c1d41349c1041040b04580161120000715410850f00000e40c5520041103081c070000050484d003103d00411400003c2d282d00300c01261030386405052402c00301d0b01442200f07911804140500300680aa026445c030596852040c54039152511408480d0420081c110600c8000c040c000811400d041001d0200114003a94034402c4041c00d040d52603038103030010703402400c0b51441001454401a044400e44044610846805000410407070040e12a49050500254402031022130403a4607500030894001041030615410904840074904400b15000800c050341d0071400800700e8000034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 720276384 1250 720275134 720275183
    0x70201060e0f252007080a0f02120a08090a12261204060c08070216030f140f0a030e1c0b101802030603010c090e07080903090a03030c02120a 62
    0xc0014040c1c9400441000382d07806140c04955041000a42c051030180070914840400385102074100b40031700801490074407807a80d149003410009107100000d0724590b0641d80c841c0c03444c8400b204a0003c0d1241c180451501c0fa800303510414050b841079003001c4002c03504a5803001184111944140b215500700d8060202c0101c0b40d00749038031400e4402007080824103590340d260320b0a000f03c1c4035280c08074460b54040005441c150000741203008552207648401c6288407562040c00842c0d400c035002d42c55405c401c0c2840c01d900d401700c01c192449486081020124603000150b4900c0090003507071689060080c1004016055580700e00425070036600c0c03e44c10011444014000780c0000714440c03406002540c80c040e0300c02e10b102040011401640c0070040080b00c0c00d081c0220032112401c1d18100715864203182e2241081d2401604200401c501d000c0099882d10080046034500c49000b00b0b500812a40d03840c0050000b2003010080b40191a1111103540320321001428802c1c86d0380c000070b248180d848079a51640e91 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 720277634 1250 720276384 720276391
    0x19090e06010c110f1e0315061309020103020f0f0c011103091f0902030f0601180207021c0201091a07050f0a111c0c060806011803081c060527070201060e0f 68
    0x40320304d2802d400d205070f032082511141c8008045c4c482d02e82c154000105400c01d144c0c92a4043c021410001b008581d0f920110b8000c2208040c09000504d807465000480003401030581441c50013800154070940b2104010142000c5641c6400920001c0d514150a04c2240820f58a020072a0f102e6241042c0d1004140e03540c3c882008400d10000d0b00703a516030000fa00c0c140d04c0c06000b0300660054001409003610100e40b02070300240e50380040d440c08034136a0124503501d02003010518100c40c903141c0c0b0320840e81700c0c000c030400070b29044800d941307040b503041d5001102d17610041d002c40310741c4a9000100300f04140428023aa0040d0044240200c0e075110509100e403d03d03a0080c0350266403030a41081c0b00080d004000031002d010f00360f41f0b4004031f103403010000d402150150050404000c1746002000000d40b880100c07102c0504c1000001101c10000305d5540c003401040d000140d01808a10a60071001400701b9403040e49168080442c1140c0c03034250301a0301320303a028040d88041080c0b00001883c580900142c0580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 720278884 1250 720277634 720277639
    0x9060418061d0d0806010c061a040e100b010228050a050f01091106070c1403030d021606110f030402090c0d1a091815130819090e06010c11 61
    0x4481803540c07000d04861802d1000011218804500e1840c1d1804000e040c440c0c0c105420b01614500b440800030b000070701814002040c40b520346e400000700c00520040840c04100203001881001c910141207510f0710326880d0385807500d610302810602c0640c0b0016000844030700d02c00c0296940300d014200e403180341107039041c00e0302d1070301c2148266030004e80104258543c9113641800002c1038105441e048100c10b1090249500c05c81d02401048085010b5009041c110b400c00f107240d402c1c02e500240800c2c1035000d0203895540072880403c0440000448225500f5420b1140c0402c21403132240140f02d820078098600201d074200f90502c00200103080140c4200c2d0440500d0549600b44034000300d8400035200c04500e03010304020b00004490072410803030300e1140c003d851062243c082610107552250b5400c1a44500f00c1048091004251000481c0800d0602c480c2c1204046641e400d410b2045044820780d42e504000151409900180e07a08041e174110b07006650595803801c3c424101d0321040711060441e9001c5a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 720280134 1250 720278884 720278921
    0x2004090e012315010c0308180708101506030e07060f0306050406091a011e030b0d170408190803010b0703090e01180e0303011217130905060f010905090604 68
    0x48a14841c1810007088084101d410181494994030003078050703e4800307109041c0520481110001703030700b011800760b1001144d10800b4031140902c4045180801d0f0740d001c102c1600400340d015030504c0300c1c0c1d0072103d500441ca2003114000707555a03908900703e1f468110140d000d0f4100e03c02c24013065101e45000060244140781c08101a9100c1c80000c040380d8856100b00e8015560307403038040d01e02803403103018000311000742070101f082c1d2401005942c88101d41d0152500305131f40c0380318540c40c1d81da43e50304c6004103540144c003081192241c8418004e80e0b03072081c083c442080c42407240a60a0015041080c8030b03442d40500081d00710792a203a400c0c0c402e0740242804600b40071b408400803411002c18040e19000303184102005040065034002141160762404002c07003a03400c01c00040c0403000c0060040441ea42c1d01c55003195081d40c080b030102d54603001e109000c10810219201c00a619000e07a000b65002e04400c8520f507581e80341c1d0380015550a02c541c171a080c2c011007000c00007449071519500049280000400350f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 720281384 1250 720280134 720280151
    0x6070c15020c06101d04171e0a080402010206150a0b030a020c10200c0c01050a0521040b0903120610030e0703051b0d05030403022710030302012004090e01 68
    0x1509026040714004510041e518040182102d911740013001c4203009802000f0170f0400761154140c0c3c00580d91140d601c2075000803071090391910a40301642003540d9625880e100c94140000404001d003c2e2016401403181c500468040f4000f4000310400640080032500074618020501031b00d40c10081032076080640c2444002c00c0c06006009003040c0515408000a000b80b402080c0d41c401c503650b20061204510900201a00c44030000b001142c128003400d040e901ca41c1142c0045809228419444060640c0444178084d0380200ce90307485d01440c0304620f8071406a80708020036960780208880b03409050048408103403141460b02111541a2442c54041000c8400b540050b10340f0141c5c0c0d0048407136511401c500c142084940843e40e04031801280c182e50345262603118550749000d03500010f885000101c8a03c07172002061341107404c2c0c2c101d08600c004902d261500c0200306482c82031005801550801580701c0c42d04400070111002e228021807a01d08060800350002d00901210300b07000d00a65852840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 720282634 1250 720281384 720281407
    0xd030e0d0b04060c020c01050d02030a1d07080d03050606090907050c011e15050102120d0213090f050a150e04080d0216150902060a0503130c06030c0e0306070c1502 72
    0x10a40141d0141e4052021402e2a02d4407100700d500c50412641150010145401c1c1a0390000032103204800400000d44c8a403541c01040c001801810011004041c02168070a6a0900810550116902802035942c143ea01000907810360b0781c02c855682c0c2c441810000e02440e89403440020350007500302d01d0800e080c40341819141e401c541c8100c0303030b042641c00303046450202440719000301c000d08000c0090658480d0329200011b0741d03a180040341c0452040d0046901a0201d001e50f0688220300111420161030070340d64160080280503189600d46818103150005105846900454584813000310303a040d00d481c60714500c11000b11001d4021038401d48100040060008640003500040010001c0250318070b0310740c64411581004e16007491800c0e07003003540c00800750b51030000f5a9018800c50a10036944d684040c5d414000718403103c0000c103200300311a40801c7c0550300d40d0010500d00341544690000d1064541016951401260030100282c10241c4520000ba00b98140d40c0159107182409812b01070b0100300c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 720283884 1250 720282634 720282649
    0x4080f0a0e0306090102120903040e01032a1401030b0a05090a0e0a23151506070f0b040b060a0b040506070219030c24030b0907050a020a0602030c190504140d030e 71
    0x2504c0b1a643e40102c0c900d52403425420701c01b030700030012034010340c64285044039010380010141300c0035142051441084134861007030ba811300d01110342c0500c181c54054540c0040c0c60081c1007500c1c1d4500092030603041c0205401c10080b22400c0e07401c0240710400503078030b1010b2000582001e80e64012103000780f401407400145096003a4448690443c42c031802e04130fa05110915000808441030f404910714024494180e41224240038041001d4641d07540d03070289400c00340100c200000c2c0007402000410100310601c080081503174014a4101e9444180c2907940c000c000060046000d0b03281d00c65000c20200005290001c10196201c6c2100c102c0552140d036511040b02a21243c0d000d0306601000c0045a05a4049030003954042d00303d50070104441148003002c079405d600c00a10381e10510100142402246000704001e4820325031044081d5035030301e401142c601c500d8005890000d0807203103070483c4100392401032084d00c1c191502c208000f840e07202e513202007004070a2000025011701000d01406207564aa404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 720285134 1250 720283884 720283891
    0xa051309020a030c051521070c050313050a05030c01080a150513090b0a052a130f21021302090f101110050705040e04060b030a030f120504080f0a0e0306 67
    0xd04c41494842841009030108076016043d400801c40201c5440c40c0b4940301088000216440c04030743c3e40c02600b500c2ca0611500c01030400d20010030a00003003c0c803000b803201135410658659076000c0e900d1003032641d0b0701c0460980602203604000000d91520460340140782002181c2e542c2010785036143e000c00d040e50401c0d1300d40b001d0292104085e00511003860ba40c241c2240321804100600e1901d58603150829102159981e0001145c100000c002194071056801c154040241916099a985000000500c85100310b80c0b01e100300068201c4800c1c07640065941d116000740c442001454081c0c3c1050007580401640ca600a030606030840443d15420000c450b400d480c0d84171500110030165000f4508080421480080c5050000708504580d006054400300c83c0301a01d621100c1c2c551345801e80c094401d000846415120b003000d060181503100f628150348980f00d0704c88001c065543d0240106480044a01928800c0100540c9207141d00c02c000602d048440c0d8608a0002d00345280002c0c148a401d6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 720286384 1250 720285134 720285143
    0x390d0605100c1a0c07150f0c020c030c06030f0f0703020c01021801030e010905100b030a020301110a170606040b090612010906080f010204030506310507090b010c020a051309020a03 79
    0x90041e241044500c00c08203920b4103c20201c0d003258589056880c03c42c0c420540001c081c00096280e02d00350701d900782c0007141c0314800380606218150541c0c00007507481507000d20b0103100388101004c1c00658101241142e01940a11110203010b9031505ca41c0c07202c140c005401c070020154200714081d00140c0c00e10240c03148000c0e005010303017034404078000182529080204800d881e490072900300c00042c000941d04849105001c0302082000400d0300203410001c0150002e501942403c1c81031084504010017055004c1d01c2d0b4950f8602c1762658412415000702c11035149400120801040c000031b261a005010520f40003440c45e0700c0c0c0b00742080e905a00290a80c002020251641c20901942e034040c0404810071813202c000318141490750301c419684d81c4000d8028100d038090410701400040c82064040c0340b900900d021152030361514034000d079980720317940704514040d40b5001c07100e030103507100e66030311001c09070010104000607051808021030701602010440000d640c6005400052f1103220032400190b014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 720287634 1250 720286384 720286397
    0x801020a0504060807020d02060703050c07021201050a051e0403081023030c0d0507090209120303040b0717040b1605160312050709061e0e04020c06390d060510 70
    0x1446000340c0211009417004055402640108620f40c0c0e000404d80e500900c40d19000c140ca48034140d5000f81c511a05030007030741040c00400d0440014405400803800303948420020042a60b40440070451400f009103102010b6030a480803401080c8500c66068100812032120b41e6603907030740c481450f81916031200b00882c00f40c0c2444c205141d0302d000c0c0070040e2110410749603012542d6140d0340e825200c06c0c1c3c0b0b00070700c0c01c419400304025500781c032040b010a440b150204126a541c0c01c1c241400903c4000444904001419085508000751004100319001e103911920601c0d803601d8501e00907040c41001d48001d01001070030b201101500a00c07401c400280c40c026120308a12a60040c0035000b1799100808500520180000801566a01019a009100360319400070045100c400c02121a8044080100d0340070f40080395207800c0090224045000b0300052929040c020031a103916501c0480d0101c0803a590070700041480c40c90001c1100419200c220050300084882c0c0312400151403090301640b40700080c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 720288884 1250 720287634 720287639
    0x1c0506010e150405040f06050904050a1103120301060c020102010b1c05100507020a030507080d0f0209030c030705010e040e15040303060608090601081c0e09010b0309151e0606040801020a0504 84
    0xc0000074100781d15001d841c0c0101008100c00ca00c1c515200c2d600c9100c1c002e030740d00d40110f1a4a4200d60001d03014180041c1502d40362305203420301c640d0302d1405a038141c421103100c43d180540e074600080c4024040d444048280d00b180c0c6005812b417191170151609905654880e001e29506680d01c0655004c03600c620f4000480070b13100c508200c0d02e4102e020070703c40da0851402c8203001025070001096031440d64140340456482002c0c0c40c15901c40c1c090704e07484910060a144030040200e5840e006020700702030030303422500424628130800d80e403907030300d80b10380c6001c1422055040b2031410260412881d250a510403a10103090441d10408000c00c111010b50000360f6924092007490b600400c17864000368101c0081c8141c0d410454903d0311a01d480b2804000320031000b00d00030304d032401030440e100b10f2880241041c10b250394400052407154011102c0285d10300032030050294490000001c60300801650703a0b403604802c540541a40d400202400855204400f8030001402c04024002440c0036861640e9007600d80e031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 720290134 1250 720288884 720288887
    0xc380103080c0d180e06010c080d0203071202130b0306060c1e160308030705031503010203040c080106050a180b0a081f050f040b19151706010f0503190501021c050601 73
    0xb41c014200108100606070b00d1300c2103d5400c1001c0e400e680030310141c00e0031740d182d0200581b0560303d4440014124480401c1107a5038a28640c003952040302e041c0c40d095040c10149000074120311684404000081c1c5000c01444003101c2c6002540c0e00440140046d8644551600d04501d024914502001844820b02c03c04a41ca036050189540c01400e500b00ea9800c5421a501e0134140d000080255042200100000d081d040354901d00003401140074000f10741e80e0800b0b080c080b00f595030501400e03c0303940c2070001c0000c05040829002013251500301c0300658603880908028050090041420703404003000c0000f2034100c100380701514600e117064020001c280101c002103c240c82c001040c0b5040c0030000303010040841c8828400503400000075400d40740b480c511044440007802d04040043c0540e40100c1d002c580c5402001710143c80180010894440d0b03aa210343d45440c7c0b81e824000c2541640060076000207840c04000c0e4182c00303500c42c5001604061280a0354a00074082c000da08040d15142c1c8144141075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 720291384 1250 720290134 720290143
    0x3530070606031502031e070302070212030306030106081b06160203070e0f0f061305060d230715050405122109101403070c03020f01020a031401060c380103080c 70
    0x44660780642c2107180c4490311803802d45042d06c8821031004583c00180e074046c820380c1100c0146038000d0074078081961602c14260b80e9041203442c00d01075840c0000110306100d0000c0c04100c05000b06280200c0000400300b07228042d0480000150003425458184005980c14000640500701d1501586000c2c6004139410180e5600502221741c4e4440d08070038804135481d0310101000c6920100f1b070100d201c0e104d540204104600f84c1d14042c01e000c02c0540701c01c110100e25002448108000421280119155550300c5402d0712101e0021010950400003085903040c0b100401ca99801d45409883c040714646030f002000c0c0b9090050214a81d0000400d0181031824408503020800c0518080e204001d00c1c002850a0f0b100c050402d200f480011aa2802010f1080040d01020000d440080d510307101900409400b42541114901c219844400003094061182070540c4035143c0000c1d4681101070400c000b1200000ca0804540340d8044256240c40440b29006509008500c2020520f40c0c1d004e1844009060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 720292634 1250 720291384 720291413
    0x50f0303070215010f230301050a1a011106010501180b03010f0f150c15020c1609050c030405070e07141803060c0906090f03031201353007060603 64
    0x8038442000180050161004007001b0b0340d05101c40764884041030070705a407914503003281544d40b41d800c103010048240390300d4000c000c41c140ca000c10018403200105c015510541c80c2d0505410f15809070b001000b07150700c0340044408000c8203626907148192070720050b001c1d50f4809d800071001e00710051010001015040030600c002d050003580c2044824042200520f0315440c400098921103880301000190111581124590a83c0c1030440f583c019220302ca02080d0800343c4540b04c081d43ca8040050207042791001100c0c45144d028020742051800c0c410039034000d20b00a0311140810840c94406825041d83c0e000606680c8101d036508005d24108100f01850b10b600184403060303446041c00b500e010341e114a8242c9102d80307802c8030004004031099010a03d940107042d807000c91800c00343c3c000a16034490000c1124401c2003130b00707440c00e54180c0000c47c1e204418602c0000c01036920041d042c00d070303800c86500d0840380801110341400c290604141d1245590304182c80035102c585e6182001c200300f10404480008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 720293884 1250 720292634 720292663
    0x1d040627032102091e0a0b04061e030c0804030f020a08070b041b0501050904020904180f051002090108130c0506030c0a082406071704121b032607050f03030702 70
    0x603150054010510309580145c00304c0d20f0b503071644400603059407101c50031070180450341651501c83e55941c10041480044a8104001002d034003888401c00344a03020f0089085215140e05601e0345882c1c0e400c0b1099882c82480c1e50850003040f8420340040d44510003405e240d4007074404026107007880d08100082e2503010803034280a07000714a08001e01e98204041d00d9038800f00b20750043c0c07211410300124001c1c1441060302882e280c5950181000c00c400b618203140c5003800742088900700b541c40300d0780c4403c03031148000305070210702c2d1040000e000e021452900c1c0c02c2180b040c00143c64141c4c0c1ca201040a1341c00a940c7c1100d4001c02003800142e41d941f11244650003122420120111040b001000080010882c01203001c0c41001030602d0900000803c0c403034002d080b4100351503803a07540e0b071000e0b01c410035602000c40d82014285000f1840c10b010a1502003078a03003100e03003c00c0d10751a090b07909491040d01610000024014090840440d20a0103008060200140915038900c1c01e000001e080c0a40703888440d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 720295134 1250 720293884 720293887
    0x4150e07081e0c0a060f110105040b280c020d03320705071a0a230f1308070f1106040b0904050c04030b040c0f1d040627032102 56
    0x8104100001d42c094814444111680d21903140c81d529428080d94101e00760b00000701040c0014166802084524100300e076607144140000450545da080e01c01c2a2000f9241c94120004155841c925030000398000c0d43c110514428000030542203000d03100000342070400341c4c00c4070041403d1103825014002c85004000e240082c1080da04035403410b1141e143d0405030250410a00245040b8007510444481d0b50300610464041d0111148103520904d0482d02c100b02c442c01c20300c50030200c1e10714440c01001d201e15070055003c00d55818000304101d01d40244017407480c60705202103070301150110700141031700c5010384040141035048d81807011012902d100040d0142d641080100300c1010044e01b80d60400c00212800f107190744801c079041c1042d010300e410103441081180e00b4403042110000092046461400d1001c0d50300d546c5d4455400700318191882410581070810000d0005200d5910101c5024103d40a0840a00e611030064866400c0304004502160f0065130948400342c1e0840040b040041840007503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 720296384 1250 720295134 720295139
    0x3020a3609140d022806110d09080301140f030d031119030212010807120b0a060b1306020f2a0406150f0905031b0607060f0504150e07 59
    0x440311010a8000160039004640480c44203404035000314001c650000340da04001410421000d460704482c1a0520240c4605034203441c0c2d81c0107a1400c4c07018010200e2403691800707802e4840a02800041f0b0110035201c400300451914105284603100c5243c1c0110326443d00c0798100085079a03941441b014091007400b0580590005590014054140740003a2a0100300c440c41c08034003203001c5c01a02103440707601c0c3c0c100c00110700480d8551702a0031a02401200b19980b07980e039448094079024540104e410105500c40c0303403800310b01c008404a420a203031000010b98a90340d01920441c0e9040780346881c04985455908001655040080e00d800a9155000e41103502500c0c0b0182e0708441d90b04031007405400c1080301802d0030354817680300b00c1c0106079410300c03000f141120000081241c40c004140801207040700d4008035040c113001a0705440200455501581040c4190070401584c0103810300f283c405840e682c846103500e540c1e0040d03900691081c0707040f006d44141003030345406031546044a11101c0d400320104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 720297634 1250 720296384 720296429
    0x301090e15130f1509111804080a0e01120204080619020c03040e061306060e010f0c050c04090f0f050102030105040f0c08011a09150304050706020303311b03020a 71
    0x50b07041c4103a20460056401003d45048580c40c1a20740110f00b06501e41410072060017103074443d1141c0d515080380da005200c0e401c1081a070405405807409411888140b09025142d80034411078454900141030107803000e000401060180d900942045040740c00c000d042c03240d003100320461144c0d1500b06d04020750400300c50450890f664007440c800c00541001d108040382c416107510301c1d80d1700c8044040109100050303d9600c0603024002071140c0e40d0005003160b41d0700301e415100f00100b403402680f00b13025040b0740e5840c604010150401e0b0b5025248400552356283c00191981e441044a034451800981c072985000c00300300440c2d1a207a00c0c01031440c01d080c003003032119a120090505594000c0e0302d0600f00f00c50380413041103501884081c01c2e000100701d0301c02c00c1a4003410010b10311940c4180700b120000c80d29a48120b8481c0000e0740e14210050045001c50089880c2c840542801700604a60540042290b00c856508080341300880c6903486104a061007075080940355040540520301500031084402d10070b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 720298884 1250 720297634 720297661
    0x60c1d01050c01061e140d1a0601360519050d03140406090f09110306040f0b03030c03040306050a090f030c0206070c06120c031107170d0219110715050c010608030301090e15 76
    0x15840c26403401040010707800e2f8050406501004c5101c10189038101c1c2c00e4400221005030403000c01c04006145030b00044524040004041d174010700717507039a0308441c43e001c03e2101c6500c0c4c4074411010302c4080ca4034001e40100307030070140000b40a6952240d000c14a0000c0c240300c041040c0e04842203080c18511102e8030b00c143c504c01c580d0005020b0b180040c18000e801d641790010003400f41110707814003001a066801c1072000002c2c006903030241c0d80410450320396082400c22a403030700394010308a102110115012038091b4403041d40745400a8805498403802e5580c0c04844006a049200420300d00201d08600140714440d0f80e1243c51942010042080d189100601c54090001c0050804a0400c1e12003000d4103510150f50300703821024401c2d9218545207420600080010300903600081034030801420039000010200102d40307600b4040c0308070182080c011030704da40c400d000d0203000e03649030f600c0040c880d00d0800045000307200580b40050817013001e041e407606150740c08120300e00c03000018043c44089a030012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 720300134 1250 720298884 720298913
    0x509100e010201090206040810050612120a020312100e070c2a05031005180109080d05040204020922060e09060c070201020a0f0b04060c1d01050c01061e140d 69
    0x202032404404640040b809803403c0301c0025003295020900040c04c10002a803000c0d00c051342ca50501040d0354540912013161f6078041c42c1a801c0d4050300c5400c032804100e4009108119042c03040e170745000642a050000300394180c5080d0303004001c1080400a0705800d2240c5500104540b0f1f040d043c000c1140c4403c502c020b030700b0000641940381030800903000d20044103958002c100c00750a45800004d8621381d0401040d04441c00e400303034400c002d04491404810310038200002d510072612030a02c03010150000c01084018400c03a0815400c00c94141140d544c4c40b00c0288202400c0d140241041c60441004103954060380070581c000180018450040700c08982c1d6603000c8107141c00d8a4030795006000403454036449020180c8100d03403589400c0240309050540a1146000303600238864a484808129201e86000580a0454509406108440d8413540c000e2561002110022901580b246581c243c903e50f20102418241c0c01176108019400070f200780c45040071412503204441c3e41c403075194000f84000c640b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 720301384 1250 720300134 720300137
    0x109030818100e070e2805100305031204050115050a0308030c040e090102191d0d060f061409010503340f230301050106050f03091002161101050910 65
    0x71490410106040040326a8000942002c0c030148101c001c00310b4449529002d07804102ca982c0b40003840d40507130090032090000601d8100480a0240e03ea024000c0901030415a00c20b0071904000000c60010800392020340c2c44150141e0309420140b51040c215413048030042d11129940508000965691102a044a0704a0300d240d40c2d81c0c0d83c1c2041e504a80c0720359006088030100c07040c05e00440120550242149031000f034800d85000010300e03010380e041141040018440b03858011038007a2400c0c882e152100c1c26201d002c001c12904044880361041d990684c1011594003100d442c20401072034074015150041005034013078141c40561000d010031582d5820001c0c4001d080d0005107420517000031000900404414078800d403d0b58540901e4803103a102c2542c04d0301005851503c065280c503042c803c3c14100e9016840c1c007494031540640c22100f9420041480034140250b1801c464050740340e0004205500042c014400142400d1800042200c02c40403c0d0381000018002640d0a854030b141580741039426 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 720302634 1250 720301384 720301411
    0x1030207080d05040c0807061d0f18130b150904020114120f01030b09070e0a0b010210060b120a0e100218131e05130b0405031312031101090308 63
    0xc40c182814144545010024918500400c100c00d010020030030900791101c510541d249166a10021110743d103120072003400010800024035198030f01001800c81c082c1c006003460320b00d105049068030301340c4000c03903401103c0014480c2c80c80800211a1716264848041400903c030b0400c01000700d0507030000103100905003d1444490380401000d102a59485159018501c4681c5070400e44110410001c1c0310480e280b20802010400c0400c000c2244000c1e02e003140c2ca511150b0f9544072075200584002e50036a415130142c0c0348203071103120440c0110009047c0c0b5140181c0d0300c280da082c10b0000c0f090020142ca160b02e10b043d6114502050101d05106010b00c0700b00c0260722404104507411000143c1c480e0258070410000303e0001d0310055800c5202c840380a1860076003030004005041e001c0c0c4604883e01109940700841c0100041c0026101d540c1040c000d900301c9043ca610b20103181d02e40c07905078008120700ba2004e00310001301940001510a0020304800034054411305542c081d002e448043c08401704140c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 720303884 1250 720302634 720302647
    0xf060e0601183e0301030c090c020318090a060812090f01080705070201031a060a0201052d0f0901060515071e020d0204050603190f050c0604150807020a02060d0e210405010302 77
    0x140c2c0d1000c2c0304030340e80c203c45680e40c0c0d617592a00c0c01e0004020b2084580050412040c152500e0001c0b0980300944046405141c05603c4002003114040008003510b0b001c43c0e84810100310b4101c10800f958480a24240342c0d955280108100300782c05043c884854100401c04040185443c0d010703007903170121503080c01d003c03400050203e1810044007101c07203421342082d00401c42d4240f40e0b80c1508918056203c0c0010404072040f0590070068942000111090045000011940c0b4402c00206103a000080300c000140c21900c80c00041c0c2d508110103c42d84802d100411440c041c80b000050362005a030000929040748190b0341e000c40c04d41d9a00c148080d114aa403074000421548050100350202d10451012407a008007030700c0e0819101000c0801650ba40c81911100b080c0760402e181158190303810340880110343d2411203411070b09000001d18420450007100b2070710f001a00d9610180c8080000c0000c003080b001d0b64455903507d03000b002ca01510381c080a8503415032641414408a9095860038030700580c0d201e8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 720305134 1250 720303884 720303971
    0x100606020a171930140c0405030c0105161703010807062f28170a0e060a02010e1006080616141602090411151309090f060e060118 57
    0x4900c110340e00d102000c2e00c06041d2202da1540e20511380b105c038034480c1510b9a298a10085541c1c002c074003a83d501903001001d201c00e15030050010745444448480c0d000303103240c21640d450111840040f640c03441094003000502c0000380c00d10014000e042c450ac0e2005016000d007c10721802c10541c0c12000b5030380480b401406031aa0103110342924400480d6540214504034041c00d0b00c4029041003d60f240d1480000b00c0c40211080c0040311802011903851800101340c8c801042160741c0f03c0154041990368a183c50218220244580103900014410000300c1c107262203046410480001c00850a210074001158111500a5500351040d9985501c00c3c0e1914844401845032010200010358003c11042c02c000411444a22008080d042511240c101c404164034940b0503000720740c21080c80d1800c9142c00c0c042e40009901801c0c2d0907004001c03c0044150a031140030407504070214862081e008000140807490341807100000c1c0903071010041011a207005050101d4080f160349401c60852300528032000d20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 720306384 1250 720305134 720305177
    0x30115053307062307090b0c030717131203030c02011e0e07050d0606080115060c020f152a0d05030c1318020a080604090b060f0102100606020a1719 65
    0x20355585048482904d04814003440f010310440344940015420040865020034150684540004001c02181402d41a41d2070007101c40010144420141c4180080701e000d20003201c6030401000c4114518000c0e007454140103041c3d40e0080545019603040044e01c0c4510009040300030b2446000314000070710305102145031400d054040e030140b9484500b20302c0113424824280d20260480364120000c000b500c000358041401d40c050ba1103060085901c1115800c090b0508603560780703484200030410302012296a413018400d41100281158880030300c00300d01b9140048904012a03184141c00415081c0300c201001411484014a02582064082545650b10301ca003c2d8280c06080f10b00c0310100d40c08642c00c1110006d401000101c0005008000802c0d9142450701c240d055003600000c4000150340d03813006000d11080c2e8294050b045125081032101c80004ad480b80c90041d01c0540d000d0f040c01c00d000e041040210410100c54440007800f046118152032030a42c80340d01c004290304000000d80c807251051100c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 720307634 1250 720306384 720306401
    0x40302090f0414010c0207050a090b012a0606030f1103012c01270c0501030b0130020313172a0304180e06180303071b0203011505330706 60
    0x180d030070100405c100e079401154200c1507540a44040703035095a6400288152000086440d01040501d00e04952401c0e482660460040d20b082806000e24500d6035403400700e0301d0a900a55070741c20340307011117010805107140010000300218024011440780420010071514241e00401e610070642e408100014000c1d0014400c2c006903592240024200001c0681140201003080352801030801e000303d074660091084211014041e503540c80e01c1010700c0090000d1070419181080c02c0c00840d10104148a014001540b24036001c0e14214071281c50f46c40c1c4003500800c07800119840c000c052000e10311000d10a207107007103402e802c1101c1401a04900301c01d6400c1d403145800542c4500e00000c201c10b104141604401c5100e40503038121a681d07680c031441290704502d03500c200c4140b07400410108051621450300c00d26a07000c5020064455880d035030010b401c40395030503405020020617600400040c500384011307a0200540078403124024601c0c01c2080840350f501c0786015001070002c587c132018410542e202901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 720308884 1250 720307634 720307673
    0xd031401050f0d06110703110a110d1a04081e041212050d090605040b06010804020a06050306040b04020c10061a0706050a020c030a02011401150203040e09150c070c0902040302090f04 80
    0x2502a40d005481c05e030380c0005ca042d80814040040750040c0307a00003c215000c25003110080c1c1041203000c0411015000244081c0c40105080a1051120441440d160f00440c4503100302561002c0d0130816088500300300780300683d020010720042054402000c040b1340b809602000b144074580b110401543c0b2070140703410009070340b0b02e0000c560040103207030341c4041d01460107940180050750380c0b0070045900c0c98003142d0094002d11100360801c400f038001c1001d940c0240000740040f440648520100302282c00c500080d0800e0b90248491280e5410140b05600140401c145d100300c03480c41400f0400010b00c034094008103600e50f00e40018250042c0f07541520141ca03000c0c0242c941d81c0c0001c100c000c0c0a4484102c540b40c0c810b0303000c0c00001380c50321000c1880c0454501600518105460107044503541ca02c0101105580e0040324680b94681086000343c0707215480502d400c5403260f5240c10a007044c1815608400d0306140704100501c0980d50340c1400c0355224419682c488031a03074540c0b401e1501540711420090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 720310134 1250 720308884 720308891
    0xd060b030a1e170906070b0601030641150a02030424090b030601021b03070b0712140a1202071505100801050903090d0803040606030816050d031401050f0d06 69
    0xc518402d500c441c0100c0034015a02541c480d40c1c1c4010200301c034410040b645600480c204812000540404407130b9a102005040004945035500c1006190461250400b494a9020701c904142d0885034540c204000303e030111044100384820010a0181c103002d070b561040e07500040f03034002041e442003040b0f8001c0d00051110013400d0f18441207006184d9240d07c020808103281d0240800c2c801070b0b0006491061105034028040c0e102d90054500808000755404d0742c050240a001089421821006244c81441545541026090110014180d0124a000300501c9a00704031000060b58846413086078502c1059005985050518100703050040301c4101d268101e007040d0411042e035081403030749000c40324440001d20042e92071a29054980c420207501c40d034030084080300a0b000c070720303e40080c66100388180070001d0001e4581e1604035140e00054100820718001c17a030201c040000038000340c4200d680508040c031008403800140204280140a0340c0c0c000c546095002d003142c0d44040807203005d950494401c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 720311384 1250 720310134 720310163
    0xc11060a050a030507081005130e010203090601050a080c0a0902030a0e070e01050112021908090a150c140a14090402040308300f0a0b0117070906020d0e0d060b030a 72
    0xa031803500500070300000300313107494000f624007405104e1080c451030803a44800c0034207041c4000c0008064410100710b14050340d40e120640d80002c24401980121800002803240b036140030108641e03076046070851140f5420280f04070003a5100e000200003540c040038030242e2070303944030014000100219160418580300360000015105a4007000c141611001e030b03251941d0b40400f15040090f4802d03019120070b1a020302000c440303514816003042c3d81210501040d80c130344508984626038080c1903504242c4410f9520004d181c01e00d80c004104190402d0a80307105410280781c03039030107000303021001000c1c0c48440001580c20301582c2c690303046901841d072000b201501c0d0f402c01480c030f0071000700c0515061009200046007a43e0382103003074035030380c03003415440d4034501d0a54030003148030040d1076042d000906004513001c0e0030342680d080e12440c07842038081d982d505000c41d191610082c504120b1003000000d01454525003689621006a144c11054020310040703002000d0341c01091801000d5040a8a400c425010340c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 720312634 1250 720311384 720311387
    0x503030703080c1b2a0103020403380c03010501202e020414090702030c0703031211030403050711010e0f09270304030c090212130521090a14030c010c11060a 69
    0x184010f00171642d456200c005484005500701c0c4a0790001030000414502020101d825444140c2018142c10359501d9100081400a4108040a598000340b2a402100502a41d46c3c031107030010798410072440105071054800c0c0391381c0d1500709244090410303405046210310403280d5a007054200d050483c8046507a680d84040d1580c8a0490108030b510940502002c81c1103a4800000c1d41e081d20040c801901015143d540d080e41e00704402d0b14103001b0640c81d503210390343c2c500c8180051445180a9100c0503030b00c4e144d901c1e10700091048804440d06004a0600d4200b96490352410110781c09429140c860007a204c030780358000d0b1201c4028811500c1c0343c0242804a044801001030702c110f85c8103106903403007a0346806801059006100c54028005840340000d4040b0100d503281020f1580100c090744c0c00d00204c0302d000d9002e5040081c12108503180000c2013003072401e254030080010700d03403c0410407180c0d5089000035110b01c1040c1d070031410090070094240c280301481d1320040d100c0b03000504080d0b031891100300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 720313884 1250 720312634 720312673
    0xe061306020f0c0306180f07090606030507111b0d020a060e030f030f1e1309150e0c070305281205010b160303180614100503030703080c1b 61
    0x15940180211028035400200000301d82e4000e030401009064555100041b0410558814598054500c200090105501414040d140c0540000b900100b41e0905000c405419583d0140c0f082d01008103820081208083c0812034841e1038404402c00000e805d503100000b00c0441c4040d00195000c82c008000058164011850380c204000a03016910307115a0002d403251680554a642c0d40304000800507103d143c017692200e003c1192220752003600749461003058003070541d05500a103030310664440103101400c503d08801d0004100f0b03421540c01d9403800320091000c9004540004090103004902c081043d19090180c405214208404943c8020b10741001082c03942102d00125201d480c0000108084402000722040860f03a5101103001c8502e55400310002c0030120480c14034000e0001e200000640c2500492030fa0040956007184107050102c1c282c4a1070089078441c1d0302c00c1e0700401030000080d41250034198005401241c040d1107644c0c08070040307080c0188160b601150700640070002000302c40c921 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 720315134 1250 720313884 720313889
    0xf0f090405070f050919090e25030809040207030519021c0924020f010612020a0e0105030d0c060b040203041b0f05150f040b040b0c010b030604020901150e0613 70
    0x16014041c6899084003507540c2d01e480b112a000003181044802550304000c10f00d8201980c075005407030007595603041d40d038048459050154505810005046460807214404003840c4141da00c1465051440c69440304032920800070003900407074000c101041418002d805480070f000c00015001030320140300800170b45815880c60082c030740030854200310300214030624500d41900d00c12060080500c14031103410200e201001141411842100c1b20078020711002e0003000b00610a40070300d4405d4003900d01c10400801c2854000c8410005000c1c0104001d40c0c1c00a05000c148038907081c08002c1d400b881c10200081d002d0303480c84940140c000420b220402440c88404203c440ca0006803030065921a4221004050a4801c8a034810801c0d8801c0c076441441d68001e06100d07051340f030b0180c54181d0701d046c0700c1d101d078100b6800300c4503034400420742a94126083c0543c6408000803070203440c2c6031505074000340c156181802281e0300e5050705144000000c0c05484035a548003002082d1548078643e03152055010075030360 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 720316384 1250 720315134 720315139
    0x4020705060f0a11030a0504050a1e0b01080115150c0b040b010e25030e0c120304050102060a110406140d06090b030f010b060306060a020a0803191d070303080703020f0f09 75
    0x8800042c1c06074071078030074010544905104c032403031600c811144078098880908191868042c001c0ba1400260204598200d68000740c24000a00403460900010b0084140d0000c2016414041e80c070110011080c001070943e4204a03150308411540304084807928160382c0b0051014281800740820700000d00310440c101c400f400f592241c0d540e6080003451208040508900d80c0c510404140c0e0b40290103501b01007181c15240c01110400c500744000a01c40041c05044c4010a42000805010715641800042d034000c000250601c40c3d0158820314460074420741c4207500812002205a4ac40032001d4000c40760340703c0d02c0581c04c0c00785640318000c1c80e000304080e0500501c82e100c0c1c00c40300140c041c0180110094420010005400c42d6141000d2044a038080201d100440c019250898001201280998041c0c07901c0019090000d11404002c3d007143c01520314000000b10f0308000c00c100c010006124016264140780210850301c80f60b200340c010340184c2c0040c010b00b00c80803ca849409400c1c201a00350113008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 720317634 1250 720316384 720316411
    0x1303150b010206090d4d16060806010c0b0a050f180c01180e0a0c1d03060a1a1804020406060c02061b070503370c0e0709050409030c061103161d0402070506 68
    0x41c40d041b01d42c0d400c042c4100c0d445401200707004210b070f180121f148603400101818814080c040603900e60768032550840347c8150040c2c0d01d90920031100c003408103040c0c0c403080c2c08641102d1404049612690b403080008424100582a2181100014008020002012100250035490401c0e03c20304024140400480c0002418501450980a5542c0f440115440041d01622042d151048280c0151980307030001c3c91410301552104d005910754800350014040305000729003160805d40304200c02c1e14030f1a84607004121650f4041c5c0096a0b400c0d003204c603040548004000c520386a00d24190400203145e1207103505004000f03071000c058800068003141c5000c0c2075900364008081201c0300c4406d2400090160040f2000078042c010031340c03500c1065800419a00700410080c0c3c0d9980080c0584921320b500310001007565049004011007805030b050301c0c4540140c1c49081d4039010704180036202e8041c2e081002c006d00f41900d050b600c142c1c40e01c10056003501500c1550744400301e060240c0d55040a98224070003110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 720318884 1250 720317634 720317777
    0x36060703061a030405070e040b011d0601050306100201271502030c1914070f02040b0d03020c060a11070803271e061303150b010206090d 60
    0xc40d00c150000d0300c040c20025810510b2001070251190401441110240300301e41000c0352400c604122280302368400c50180e425981400c0c1441000751045103090002c2c8275030f1061008aa0301308050342d81c0b1917815a200082c4415094049014182910f012071009400b0b40c0c20b40041c521004052032610b0103800c280700b00b0091007001004903c404c94195070640000d01c508440c4003854890700f0646a4107282048800c001909119096840704000b04c0304c1c0c01c44100c03071104500b032034080c5050455080318800801e1100b510f01070345800c0d1540308184608400520451454050043d08215880c00d104450181c0d84405947d0360300d07807001010012854405030340c02c0802460304802102d40d0406480b00140008060300c00704070036080904998068400e10070310041700040810035004500844400354210a0780052804070781340c041c0c00c2411900800d0402c00459800125501402214a40b00d510031103030000d0024044000d081010603914620f00082c0344000032f8004848140c08005e00310580038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 720320134 1250 720318884 720318887
    0x102a09080f0c0a030b090f43050112150e040203070e130201081005040e010c110111070219030f051b0a0e040b0711010e010e070f0308070b360607 64
    0x8484240e030990051443c1c1090000508840c4801d07040000401151140382800b070030030381060b0181800394540340c0e1180882d02c0c0840d09031080100301c1503035a82c07600d45040405010740f08a50f41e000b85814059a07004c0000300c40c500e03030f01031015112181410112180c40762810503803a803040d201a4442d01c5030fa407002c18034000310401c99000d0300144e1140b1848a503190300540c1e100c04c00928001444c2804440060a910742d4050780c00031711011000001c00260030b12000d402c5d480348038203c005aa142c00400081c80d4003400c205c501c000c0c1c040341d0310306d800300d400170100180e02c0580e0002088507120400601c1002000184040e070840050102130899039008103010b00954039125603c4a00d05c1c0f00c0108000c502031181e01c0d80c0000007031901030306141c1c901e11102d09540304003601011581d503030002c2101403071084c05014081c142c1d108080c0030481c9192100e6105000710314029051001d00c10110f41d10b0160b089222914612103206a0b040c0350f200d10031005240c80e010865038880c06110002410036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 720321384 1250 720320134 720320143
    0x1112040e06060c0601030311030d0606050c07090e030901140403081204060608030702100c061416080a0c14030709030b01030605090d030c050a0e06040b07080903071205102a09080f 79
    0x403024180140040d031b00e0368500f226030b5052504203103114041040340000c840064026031014000300d8850075513880400c1d088600d4101c0c964828425245480c00310458070402204072800040c091070400c40a44005011210510070380d80014001840000e2005101c11309154180c403542c0150b0080140396900d800c1a80c5034825420004c0d4024592402001c42d50b020b02d4040720024050b100000e08450529420503250f0010345444020020030986006410791090b000c59109100b02c40a1048280c000d60181407aa2242c001c880600c0700400081d245a20510356400159008901d446095949003003038401080c055a03d041175010780606028890300900610300840c5c1c569131994503001c414a41203d142c141031079415840142004002244401a00644103450295801e16642c0905600305031030a003090b8090110001183c0080f00070520104030914800413811021032099522615000c00c0da42d00c2e02c2c0c03141e9030441d101950a200e64007039172040694002ca003c40c3c0b041003107000103036a507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 720322634 1250 720321384 720321397
    0x120c0203060c07060e1002031005040605130c12050c040f23130906020c0303180d081504020d1e0605330c0703030e01020d2c011112040e0606 62
    0x507038000d6010924001800c8014100c00e07004a01c00560310600380300f05414180031003500240d0700d8010051000020145480800800e811501004040e1a000108808801d101524000e0554401300c10002c14051100f05015004400c0f0401880c0350003080000142c0140c040d1f0000c2030751032940400c8000c1007495400351000b40c4000c0c2c143c001b085004020310700b684140003085842e140c1c490341001482900181ca5807410071000307561a85060f0055520510f005078203041590305c001ea85a4034290004000b60300314141c6032810340c042d00804040703400b0340300b42c100f4688814500031444140c3c035a0251903841c1c041d01c80781d0600c502580ca0303040154840b40c40201600300020503642c0f614285003441c4120015032074000080c03c00018807821414500715a00c140c0104a0300c01c181c4500c1d40c6d040c803881c1d042c03107928141220080602e21400000021001c0f4043d9104005400c43c8180d82c080d042c3d48074403103080c2c4125490750301c001604441e075801c14880c0543c03200d01c40000ca5410310b00201a6070380d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 720323741 1107 720322634 720322639
    0x6070f060e0304180f110307120b030c0f010c0606170a030305250e03070503010c0908060c1e0d06052e0c02031c020f0601080a120c02 59
    0x401d80d21441c0030300c59960400c10050103102540e140440b4900c03042030740003840c1600c0003c030100030041c040040a4414001c410004500d90100400301d6420901c1820301c040c500c1d000503d5694000c4155950348820034809500844d40300b0500140e80d280100c1010581c140c0d0b0b003c0c442c00b040300415080034580c03c181d9614042c1a0036014441d0001c40b8849412118540c0c046055400f004040000040107907200c4030b4209035a04100741c602800c8020300801520001c104054801545449011440d01407180001c4140b200c542c140c40c0c2c0039190003646909820509000d00159200146e2074404660701e41c00480d007038603491200043d0461880c020692007021000841c01240c480c03042d01e0801c140444000010388001c00c03007031008e0074848000300700141142405c0c0c0c20840f120000300f02d02d1042900004807c4e40c00914484101e0003841d4115041404100840740c04421810294 = true := by decide +kernel

theorem cover : BRFrame.Cov 720143884 720323741 := by
  have h0 := BRFrame.cov_init 720143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 720143884 ≤ n) (h2 : n < 720323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
