-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4529
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:54:45.740547+00:00
-- url     : https://prove2.me/submissions/f4442287-5864-451b-a436-f43d5168a474

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 814388489 ≤ n < 814568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 814389739 1250 814388489 814388503
    0x10617070e041d010b03031c2f091c120f050f040608010302030d080106050f09010c0c081e070503120d090618030816050a0509040e060a06030c0801090503070b09 71
    0x40100180104074000c54800c400325540d880781043d079403d1a280e04000c0c10000116a48582c1290703840c0191003407003d04038000c01c0c0c4a1030301c0f42c1c9070b6851001d00850007120402d14100da4003003c081d42d903c2c05020b08001c0c21131802041d0601401d1010308240218140c42261190401c10f41003011146420510480d8503100700101e098038908085008100d0a83c0030300003c0c16240309400f1200641240301040e540040244107140c0014001c020440c29011002d0190039151010b0402e1a145466540d583c100140140c110b49010350003d03c2a44c0c901c96900110415554cd00c1c0207040c080c1c0c18040403035211039003500401e115010004003000340c40e54690040000d9900038800304210310804800040345410030009400296880c808a030100348001c0a85140140589800d45080304000c8142d4194200034000da9000d81d5580303400301c00342c905101040c0700744041c0e40c00140f81415441e10b1142000a42c204014507072501c0b04142c0000c03c0001140c01d51074021480381242e903200007203103103840c00d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 814390989 1250 814389739 814389767
    0x20d020904050709051e01140906120307050102120a0b041104061b080d06081005130f03030f051602071d1b0708121501020a030804030320031302030f0601061707 71
    0x2c940000c00291094170032000d4400b191819040c03046d0f9a980507541031000d9240f0100d548158540045182898000c002e51030044d200d8060702d003003d206032510360880c0c10500320800c820b000c580401034080007520074400480000c440402002d609620401c2003801240503131801d1103820034204040740c80340910402819030044003559900002d00c03810b806000c0c940300e03054881c8190311018079001258040d0a114900c000c40341c1900041946a214017120807101c1541495640e6800d00781e04c20240c05154444c21103030b480b00300581e03991032000303261203950345c015840c4c0c0c40710321701469030703c400e00302403030380200309407005c000200e010ba0841c5095108420000740211030000303900e581c8030714030300c5028850503050485480790003200c401a42c950300ea50b84010005000b900c00200000d01940c04208088071350740c0304030514440021002140d0f842039a02da84002d80c0705450804514080081079600100300c00540020b500d80507000d00a4000d414141040b0307000c030170001f11083e120b41070000c2c00c02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 814392239 1250 814390989 814390991
    0x30a03080721020d0207030f09080a02090a0902030312060901051207171516200c12070906030302160b040602340b07051b03032a060f15010c020d020904050709 70
    0xf071030041c1340002980b050700c0417000f01380d00348404041c4a000d04600c1003200c4108011b03100441c1c040e0700700300400c1e03401412120300036550040580562410805000d100d81e6032548000c250420b0010052100c0c0705900040c1309841e28008650002c1c40461200c003200c824034001042c1c4d889415001d41002d40c00b03c1e0002c001d541d00c2081001d4001c0f00e11803500d1302c203050784820780300b006901a27001c40705580c1d08400c09075600c1074952034840c1c140500c0b000c1c2d100c040c07841a40d0070981ca0346030030800d680743c1d9842603006911807070603613548951801242000b090f14003500f40c5007614020b0044e4844202c1c0a0401c841b256034403400300803160265000103203801035039082d80201d4554404129540010304160b0381842002e82c4400003038182c030300e10031564000a00441c1041c000d09024410442c030000400c4041c0c0502c00480e2059404210444c0030350712021118003280b4042c1d003800d0342401c8007607220381005054512440581c90b1500c0721080c042d01030b2500c4099643e5824880e01c2c00c0a590f100400d92 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 814393489 1250 814392239 814392247
    0xa050412051212150619080601090503070f0303020f0a0308011205030705070906030620040504020d090210020a03081308040e180a0804051201060302181308070c06030b030a0308072102 81
    0x307066206100b441390102e03620040320011120107100c041d0269000d8051b49025540d0311a4810340034462a03503000740145098a500c0b41c07543c010a0602c4059030050f9041c1c41c03140018010503406210005058500000500401d0700c0754400030b0120b0010310841100918240300071052020a104903071a403078010301103800042d52481c6070350003811503110590700c141c90701000d51008116003005400c41e02781402e140d81401c1c2032104100095012401001245a841500000689900c0c03180080c8181c40c3e0003030300c400c0400d800c02404070407005090710010b889811054000400d810b003518107884030150750103c0f0350b40703a01d00382015030964441a17125224000f030703e10402c2445e0f00100207480d0151a08484c6682101c404c0e402c1e209540002980a0201451241c0004140c00110760003e0704096131110640b160312000d020303901c814030545002d56160350074030038160940502c003541541a4010070306d001aa03107004001c003201405403020030042160f0500441d05c500300b4200700041001085540e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 814394739 1250 814393489 814393507
    0xa09052e0c30051c0c02070503060408180d0804060e181801061d010909260c010c050712030c1e0c1704060f08040c030b0a0509010b060a0504120512 65
    0x10000c42c11150204407000701c0200b01480b43c01511060024030200d0040b010001000c80c0c040c1c108154031604603c1650303000102e50703504000240c02140502d5503590303241d0440c45264000351011010b00e00402034800c0f03140c000b030490002c41c5e04840044c07802c1c561900b800720004207008090803440f407008804405020340f80030407405851305a00e140c0000c1203a070f40e5130859248400c0d50f403101c0f40100034010307004000010030394014041c2a44200b81505034203400744140107840718501002000c28002192000c407019003485280c11000f45070800c02c0c14031051b980c605144902c506030344020142c40702d00c2c020705180079800350b009862081c00003180c4502c006c04020055401c0480070b503a49050031101c00000e01c030720f9044905a648a0344d038904804607030300c003e0f10f040300003034800c0320004c51000001003c900810307041e601500540750b01050508110441c1421350346000300c020b01c038010800c200004950017004980071101080107804480d001800d001c1e0810780f1061055001364000645021 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 814395989 1250 814394739 814394783
    0x8040614010815150a05120102040b040e160c0206070204020c1005090f07050d11060f16031e0e01091e050303070b1f060206010315150b0a09052e0c 65
    0x90f070080904050b109984600769040d02c3c804022030103800011510041c8401e040241c084071000350030b10000340c07070240d0398000c50841d58480d9004101500c02c880a0103516011303029050454115458408010401d540002da100d21503104000d1289500140c2d103108980b06011600001da4100c0c0304201603c0c0030100951191141ca144540c540a0399001213910f00e05500494010340c2c100c03000c015681000d03014040c01c0e41c8514600342c0c1c0d00000740300300419600c207605202c010f00d05c0313503a4080d0081003803c828102ca00c4809102401e01180751041e007160303680503c001007240c2c4551207c401007101070000440c1d0000ba60001030305404002001c9061154018409000d00103144100445070b1290b02c3c01203401c5c4150283c1801a0004001000402c0c0d450341d8041c1e40307400341100011440c2c642034407011000c00c80e0340300400755800415643c0110f500420600300070103003592601c01107446404d40380100c0e104a0852000316103828900c8a145100b0744003c00d00651189441c0b02002030703091141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 814397239 1250 814395989 814396003
    0x15040b030d180801051501030203040302031216030c03020c120d0e0a110906030d0f030b1c0606140d0215031b070507030c17060402090405031c0f050c0406020607080406140108 77
    0x41e441d40b602e40700000d036242052148611031800c8020921416403050011400b0f540003030002d90841c48244442003081031407050040c0181d040000c1070907044402c4401038203481e01582c0110516205000c0310310019004182036281407078030441c0720340d507540070315110005003800381054419109040c00c00d0200045140c200c060300d41c2c1206c400352107965020425540b0b0115940b200700260340002401c45242c0aa00300d500d881c40010018000f0320074017218613803040402c110540f07500b61510002c01240d00304942c10b0396080c034103450380d10245e40a0b03004510304180c00d104040b1600f0f000000600f4036088425030f288000ea580140c140d0300c01950800940d5519980400e481c1c003200070900141c5200c007004180420303400c010260880d80d0b615020400d150500400c26202800100042d20b03407420411000f0003810010800018401d2500d041841118002401c0080e8244100010300c981500018407580c44100c40c43e005665644900e441c02c040c1098488042c80b1880c885c00100c3e81c2c48012500b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 814398489 1250 814397239 814397267
    0x90b0c0106050406090c090909170c060601110706020307231c03112502010e040c03020a0801050a051f05040312030605032407050703031503060b09010b0a0815040b030d 74
    0x80c0320654840724510b04070391b15407a1000114110503010010050950000017660f07010300c0049045125030000300400c0d601c0100036100c01d8100c1400c1040c00d682194110041201032802822042e082001c060740c0c0344101003003d00844100314200f4100c101d022958440c00c1036074000d80d10364141881e1401c01119411980d2404a030400200d140441420002d41d9202514800300413006684d0112a1749649480c0034240c0c100710300c03030540344081c0c0c5982c0180c5c203e0039120755005070768420f110b2004004d00030603040941305038002c40080145949025035151010301c0035101030041c01326400f040d0b0755841564802854204032600300030865801d42e00c410100c1e07006806072051241110b28402d64260f0781e03804011040800004201d9040c07056005c1c00741144281000680745401d01c0c9482010b5200f64000c442103a25032000b456581800e0102d60300404c0c0409805040030390109005c1c0840400405130004ea411503401d0b9005075880c4d403c1091801d0018054075003074544508000c00b411444581 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 814399739 1250 814398489 814398491
    0x90a08010c0203030402120d2019080415030207050a020609031c200606030a030311091903061404120c0c0e0a0623010918060305030c0c01030f0e1c090b0c01060504 72
    0x500411070f1f0301141d002d40000141d83ca04000c1c196660740380d62843d0185800100d070388a5100f8407001c00160100103110ba03406051496103540c50802d6030600c040801600b8000c260040c0001d200040001070350240c12941102c5440e255110800404e203002614488403861400b512020b81d00c0d00e403c901881494007010f243c00c400680c40c40041943c1c0d20050302c070071744c25501581810000c1392080d03004840e00c40d54008160301e44480308001a480c04001d802c0840c010100700401c000300078291061032443d002071480d460b014035003520355070a58106c41e000c135014032070003481b900204101000350001620b000c4c0239082d96030418508640c014202801081d0030060403c034015030400a043e00004102016510400c0ca10300f08a04043c0342414960800c102d19115400031000907018800b503c0101d8005008002071032310380000405075407500c0444440c4a00d444085400080042445400d01c01d00c1c149a41403280c001e102200d032001039502c01d0820081c0803906802054040d0409400c6131404ca034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 814400989 1250 814399739 814399759
    0x311060c06130b06010e010f08090118031206091e0c1e110f03090a03110f0604080a06050106050304020901120312020a03060315060609060c050f1002091c05070605090a08010c0203030402 82
    0x40155006c0c0000910213012407003455040d040710388620809944055000c00128200c0c00e01c400050220640d02000c4011482956110420240781d03c110380051859000500101200703150045040a0750b0b610061256125030109190f640152860040b109610003030140300c11407840e00a0661043c80c51180706402003030070021018100100782c40f603980e00201880c01c1c403851681e0b5031902881c12103006801c50810302c00076607940d6816000c1d100520400c2c01804503000d00e4a407000841d20160480803e01405000307000160b00c03803022880c1503c1c0030100c0d101001403282803e40b40d40403000c7e0b16034169800021010b03050f540c0354100e201200c0c4110408800b00640404c040c082c1c4003603024041c002600a10100300041c0300b110342840a40c011000d4030610000700100030f007403d2060310074500c1e940d0009416010380c10480d2010402c0c0c0012401d45400700b002d580c43d680c5940d501d219450800201088100003030307803245200c0c0010141032000700030040c20100301940302e400482e0b041e80b02d040e00c09 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 814402239 1250 814400989 814401001
    0x14040305070b060d031d0d020a0314190c0b0d0207022d030f062802031f05030118020f0f1206010e071106221202010e010c050f040311060c06130b 64
    0x10350b01d026002d502d13460306c040c5c84464184001e0826008a002030b80600c0111004d80545c84002295004d54044d1a0480031030119017201850400c00d01038004003040070303421110105155a40700c00550314181891540d0300003260071807000e40910f81020354048a03500026030034201d00341e81c021030400807201c4005502c54080070180c8402c01d00718607991039080f4800240407026803e82d0f83c4e0850300c0342844000120300312a00001240c10444581901c60180d030005440562002195001000114024040c001450003182c02c80402480f001740290b095690400d0035569404030406501f6001c1d00300504034204a43d11540c5003420b10a0030250040d01021445442c0700f6604840c0da281d001c00140a1600c41e05510079200c0301c0b1644500070407851450f00b40c0012004422100f07000b080380e0000c9584280c0e5084a030071140385104060034420f00704101d40303050065200352012a030300518400703294881400410402d2242e0110b80443d80202c50400c22004048004011104d005102070388403542e42c0e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 814403489 1250 814402239 814402249
    0x90106020d0c0f030203040305060f01053f10020a0e10030603020a0311010212280f0f030b0d020406030c031106030705180406080f150a06120f030314040305070b06 72
    0x5504000016400c140c900010521440c1844040f911a1045916040d0b480e203c1c14101070701a80d00000c807001081c0104481e2404040343c042148440301d010358042c0b00321106072a9445101c1000c252140c10781a0841000c00501c0075030f141844001c800d554a03d175010b4000c009980c180d1805200780540700e050001240303c0d1081b582540da0143c61079440c1811611140b070283c49141e03a4504510907210040c10000c55003001d44082c07a41515481d0141c01d2035200311100080c80a072170301c02c111280001034a008e41c800007a0032070b102541000510308800308040345c8054800a03000e0b400509001c5c2c00420000c410403c00212380c080d144840c101610b1000b0003d552105641d00c0002a2003030002c5c1590b5004036a081c0c28484000380002452a607170b111280c01e020302d0912500442c0c000e099201112142c1e15070140c1d00005a002c20000181015a1000b00d03d2070010054208250b0758905001c05000751b018900d1041c3c1c44103403002c0b500d091328000b440340d848008221204e000710f4020410718140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 814404739 1250 814403489 814403503
    0x90c050907020a15231009020d0b010e040c120e0c030d0f0906020a051024090501050f270903040e01090c090e06030709051509090f060f011410030b041a09010602 71
    0x7480c5e8a007281440058503c501144000c0c060002c280745415000a0341c260170701c002d2160310341010010a540300d0020014045032040c068007400382d401c0a003030b05401d69000e500310485c507100507000540200c103001c201d440c28445005c1e8a4240c41001140d1280c0703070300070450355440b01c19a9a803c074416201c4000300d84030f42e000308000302694060031007410704110300e400881ca595903e05032801c0c0038124604103404020300741c0c0581642d694480052180b4107014007140740144060329012131110907040c21850500c5003c2041e00000140781c00f08002182c1882124004c00024000c08900d50310380500100a11002c0301d400041600310000040d031581c82d83c5e485104500080c040d0107010b04e01200391024000060041c294064000d01c001915982d49400700e00900d95030b0700030403034007540380941840c00034041d0030309000c800114010444605400c03061040440e0640d80c802c40fa180303e032400e5000d0a80c940b0a26030003801c00041802c03083e50351201801d80701d421103460046903a00e1000360b8a50704 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 814405989 1250 814404739 814404761
    0x7050408070b0d09050a0605060102190206030a051b1b102706020405040204060909110906252004060b0a0504050d05150c031501050406080a090c050907020a15 70
    0x401d038420030461004101502e1203416004000c41d00b9141c40e0b6842d410402000000c4908581c2c42060002550f4100714480754030801c01c00d5029a00b800d40c0018441d400f00a080e030a000f0703110000100201418240d040c3c0e1140b415951030744072281ca440b01c441180c07103080361610f08d2140319015200300b223182c001c41c00c049040c0f120f0b8152950864862111403040f100040d207a441d003c100000d4142c0b15407004100500c1c1d1956442030040c2002c90503000d40d150401860f104030030500c0f0790340e00f640e5200c046440c103403840c0c042da404040c0702d400001600301c00ca0101034054080d20900415120003403210342c41e03011080310100007044d112401d414090080000e80302c000b40050205001d681498aa08540741d0f016000f15200d0071601c001200802104841c044698040801480101c0340c59410030f06030380100342001801c181c208000140a050014010700c01152500d200d2002d000b0240714600c05828047c042030300900e0b2102c80a59201212901211015100403e4420f1204140b1903200600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 814407239 1250 814405989 814405993
    0x9030c0d200d030c060c020a20121b010c110301050f07020d110705010e0d080307030c120b0d110d0b0f091e0705010f02120c0a06050109090c0b13120b0f07050408 71
    0x7071740ca42c4c0f401058090840e00c29480b80d4403185010a40e011120701840700780b4401e41200076807171002d004220180c07101341a100c2d8003410607001c400341c81c8400c180402e03a0030b03c0c0000d44d40180341000c1c0a42e00b5009444c130f03050751900050180351202211181c0c480c4a25400316250303a05244005c80d5503d510302e04803161900141c0781403207950712440700035540803001080060103040e951100c0419074400d0300c0540c0401e54418000d0a90381c1c100d01d40203001020740908000201c40707400898444041d000c002403115400c000f00501c507617a40d1170300d18655a000101e0300614505004806200c0e041915029420310a40200264501700003026110030001c00c03000d403810516050065905103018070807c0c0039400348105242003040b448018000001d0518000c000000d001e00304441100e4041c2c00520001d414000c0d00004035248204141c2202c6541d0041c41e900d8009540101520306940c22851032404040321440c00e1108a6040502400440d02103460940b14250300362250300c6548a400e00b03136 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 814408489 1250 814407239 814407257
    0x100c020a030801120f260d1d03030103050606010c170d090c050a0f300b0615030c070f11030111030108071212080402031504080a08061009030809030c0d200d03 70
    0x10310840e0890342c001130140d81305000200c140410046c250417130801e8a003034a5171211300d881c540381c030a1113031520410311314007940c03540d4155142c5580300c00000b0501810b203d01040c10208000300340c000b88100e100e04410300703501c80b02c00310745140241030301900c02c0d29014038102c00400d051410b566943c04407883c0d02000118170703180855180700740715001e011800f403068011581000c0c81154030703060f13100f0b0710541c0180000d20741031041207040741e04020304021304a418006c21440700e422030100e4000c2a00440c1401583d041c51418208030346056403090341650901032046d04441144002c0c5060b1400f10058030301c0300362200c0100a0082c002c000c05411014080a83ca08c4a0b005610007508180050251140da2951604603018094144c07000c0b5048030002507941c000342c0d8840b0b1903d0700a0001c0b035185c044103580010007800c070406400060b0100c40006004856030b901009120051b50000e8900226003005007010039042c0c14441c3c40c08941f88001c000c1404600e04820703180503141d807645404d489 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 814409739 1250 814408489 814408493
    0x30b0f15181803040b030a0513020f010c050f0706031d1b06071104050c0702100201051902130e0103111e01050f0901021009060c0f1e0e0102100c020a030801120f 71
    0x20503803002d0000035000c922120101001c10061009201034502038039801e95034117207400010200c51000300007110500400c50a9001030380c840d4880d0120003424a031041c0f07038222078101329051030440b800e1507036144901d940020f001c6070140c1203116101c03002031014650341000d23030209880c0d0456400c8a43d82c60722008094030103152120240041b0b50149450040600801c8040b60031a00151640d40000308003140340380452409440b403422403005480240014241100a609881c01d01003891811580200358185640c0d600e4821704001c10617402a0b9103156981c2c104a05d50b10300e50326049004c3d510f0f2280346407030440c1d1a201e6040c11a01a5a070070b241155503180c00c030f0b0340e0f0000d00900707045026205041c5400079003030040c0d90705a80112800501d0000202c4098009400600d03010b050183c02c0300703a049420240d40c88411081018104860601c0001004038104201204149400341c80d040c04a404581e000038040502442516001902d981310703440000d40800660b00104046005018000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 814410989 1250 814409739 814409779
    0xf0705030403140304030206010e2d06040905011109010306060206010e01140d0f0b060301150518091204180506010905061b1e160e06030607030507050403060204030b0f15 75
    0x5840740c020b262260128120061511241e481510103400503030099006101c8148501c100300c0e00a00f451884420756611010600c0247e9100a840702010070752500141183e1283d4225203031143d8440020001e0840510520850b90050603446000928141e4082802030001581505986105070406c000d03a2070003444c181c10451f0314104030380004414200c0000070b28119001400d2a00c1051004854a01a014142115011000e8201d41c00454001b08016250740e1006031013044080d050403015030380d050803079180c900d10300b9010011040008000580383d82c03102500980d00003403e000d0000352547c800446000c0b0241c010309504c81420401d0015420406081c040000d140c0401c1da10802c43e1000059402d00c84010b401c881d58020030181c0c0802c41c0382c07158100251140e40014102d908240c00401d81e86c0c0f40050032041813540e5240030410040c040c6d02998002c540c0040c055540e140c40e890320184481080c0c8003035000341024004a0200240b03200080c204400280c0202140c6d42d0b401c0b0000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 814412239 1250 814410989 814410991
    0x7150807020a0f081306020d030b0913031b020d080307170105090a05090c060301080309042313050102043203060420040b0301110403231002030711010608061506030f070503 76
    0x21380b142001c100100c91001d04948400003014a034015099480c0380303c17005410741c0c0414900c6807017440c4180400002005110b0f104180c240c061030b0580740c10a449034880001000c1c50070195100000211500800070f20100542c400c907129906c6101c950560902402815028010254401600d10002c0c800f041e0540c80240d00032801021640210410400300c3d100e98400e0300010400c1d0000540c420701070400d4001c0302490080c95030850070161801e0009510010f000e058501c8000590f0b42d1307042845000d40564000d44181c84207070b100e40e510b104280113282061100c10008201e038807090342d018680483d100703100d90341140c1032041000d01e0703104040c20041c41801840e841030362280c1c454101c0e2024880c02c1d0502c805080300706c1d545d6080d070803c243c1c04129204134165059100d482c03144503050116044a02e0f44402c10096202d80358201d084c2c481c0a400c800a40c001c3d880d140b000100c61b0300000750300c2e000da00400c4c10440c55446040503c0034500c81291450741c1260080041450721341300394011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 814413489 1250 814412239 814412243
    0x3070f031205101a030c040515040308030a06450e07030b04060b15040515070b0f18030f0301210c030b01180216030c02040e07030507150807020a0f 65
    0x2103140105221001152403e90f00e42070f01400a02050280c5a100030b245818662040351003070861408888030380c080d110b01e0007514011070880c0e071010b2115000000ba0f60241d58445110f030b44a10b04a00c20a0082a0074410285c6015109440c0d0040c0d6008000d50040700304043d140300c0c200628820354204016800c81c019a142d6a02d280000d109031084c0b140901861082c201c100b40303030900c2c0c1400307800c0d94800c43c4c00e140314058403d1100118070701c2c0070460f01111019070712030300ca11504550880040c040e0210103800300c0e0400d01041a01c2175100001403294101950303e0420507000041940e036030140180010031200100014460300da0700f1800e541424840140c0c0c07140c6c0c0d1503a690303401c000440782d5101721a141c85000042c081c8003120280040b8060807010b0450825503441c1361032001802c40c3c0d00103800c3c82900310415065407144d400c01405005c299080760786843c1c1c0da241056607021030f441b0310743c00302202074440000640b050031121301500407540104079a680b0350310780c0c0742840d6443c0d0301 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 814414739 1250 814413489 814413497
    0x51602190503070b090f03060f0f1b03070e010329060f07140a05240c0a020a05070f080c120601181401030f030206070c051c0210060b03010f090b010203070f03 70
    0x1450341d800b0440d002c05001130340013654880311000140091006030b41c2c01c1c40d00c030fa005032007000046121640a103030300001c2d0081c0d03403d01391240c08180b54424110400f08624220001c2041030b11504811304a06213203081c1d07010419051032207090b103240409102d4060345603070000c00402c080c1c40c024010b00454805a650240751045076030302c1c0800d48190b00d0294540da0884080d8005202050100c1101035003207120807214100c00d1030302c2a45480703006181e455610b201050050400b0301c00c00c03a2804159212085424080e21411499420074041c0724106ca1441610a800e01e182000960101c44091035001401e160742400d01c0341d0810851090703d0740314a170f52540071294111840c4044c40c020750280a10035406180ca0a0003823300100400b00014840c0d1100180b001880004500c8030b0244401074500310460388001c100e00300b1407905003030340a841c204080451550101e000031412290380c012020900c580c2d50071031102342d41181e80700c5400350300140300f018080752030380400c001d0bd02e1007450 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 814415989 1250 814414739 814414789
    0xa06140607110d061506020c060910030e10020c010606031118010c08130504060e131205160606050307080f0703080d060b0304030905131401031202120316020c01051602 74
    0x40440c540c0001c40703c054a00ea6242c00200c1c00d42107050010340003500f028406004171410310b0000c20964820310000c1ca005660719800494a1442517100d040340d0b130030240c02d40c4c0381d800b6a072034140c0c06504000301489165281c12400900301e4000d1046901c091601504107040919181e416070510a4a49085060107998511100000d032881c00030500300b91081100320495040900340000c8031142c7e000b41c5036042941c801d00c50820070248040c5142d51b0b0103901140500075a1000305c41d0360040c0110f4080745003009001c10100320042d0000c40035100282e0868942c55a201003260b42c54a58100011541c0c000c2c04082c00860881d40c000c00e00c90a04200200e2401d541c0c07441c000141c2e0003110160002400503205200300e203086e40501d018900010014041c056000554806180047c40000d007107518006949901500900849001002580195890380781c011120644030841030032449c018000d4a140300441d41c000c1096031110400e8461419110b2042e0b401e100100d07030312522410403480074003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 814417239 1250 814415989 814416023
    0xc05010506011706101701090e1b0f0f01051c050901110405100806061e0c012a1238090c04140d0210020705040b03061608040807170703080a06140607 66
    0x1203c407d00030b251520b07001880c041018800c50400820080c8680010700c07040ea400040c0d40c5001c044113040c0422a2503850345144030380143d5180c411900391180000c0300a200058040390f07a07100074841c50071f8074024403010b007120300c1032a032601c01c1d8043c0c5903009815003c030b900168443c0e0a0298031020181000d4540000c015035040c4050750706440c031510320303000640183c4015082c050448500020010000c60520340d0700703021500b0201c40741407001c101c0031008410b8542e500d50020302c041c0c0715649802048144408402c8003249070b0220740c1c50041000c0b10388141a0600c644100d115151000d42c99041038103110b160802004a4800264070040341034416015940347c00e83c000080540b50010000603180105100550b80c0078645a4443c2d044101000300c4400f0b07480c500000b80b4441d180484541ea17840c43d205009014083c00501102c40308410305180710004030040001d18007a071948401c0d41d43c0e811200c000c0d181039000300c03445500f00046142843c14454083d00c80706201310241c0c08241030907 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 814418489 1250 814417239 814417277
    0xf050705060d020a12110a0c06061a0909090c0a0e070c0515010503120913180804060804060506060a022107140d0e0303040b030601050906090607030c0501050601170610 74
    0xb21260100319070010b918011540c10000c100c3c404040104203000c01000030745081040e000e01c5102d00c05002d287c1540404007d8a68080d4014021a80c814084aa0012404550f9401030748040b4001c10014001c81d485410014a034594480005e140841d01c90a10401c0401c155011f011113051101180000001500a110750103081c01c0c0c0341c0001c003656240c50201460b2000124a40c5032540c0e0800c4002450384483c1c1480c0805030900c0b201050f050b442c02802142c48400900c0940b11000110b808a100c590000f280741c021406001c0c03c1c00652540b00c2080340b01d10a005003140907a12500c40e10701404800725070480380007400414039080035460380b6003641c1c2442c254042d5100384c020f801e017095000e030880e14900d6049016801107080c0740c1069251070441c4030190906060200110320704107a80d075640102c4d0f02140019081c036480380b1143ca4058941c862120301160994208030009840c0c0d480340343c0d4004114164184101c254440c41c0500c001c201c4460070f91820001ca54010080302501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 814419739 1250 814418489 814418497
    0x17060d0305040e0f0a0b1c201201020a1416240e060405100603050318030c10032306060901030513060612051b010801361e05060d0f05070506 62
    0x1100000001ca07250100c40c617070846411400c401e1141c480b007007030583d6400250203080e1240b54048080b0083c5409803042d07030b86000d11400c01543c0490815100090880c0c1074029002010b5140c880d9019910109000704080c010210312400b40040505000045108004080894240c0b184000e107036000580903030083d00c84030086042e40b07501a00501040003002c00c001d200d1403142007001c00096046a880540340c0c419200300003500c0f18042a2224141e8040c40118101c40300240314500f00201203002901404a081940c00107036182c01c04445605500c40c1c43d10310960b402014140303400c00702c1c0c0c0103400609000d000390702c1c0403e455203d000000c5041c070521024001040303034900090403501d4640d20b880072441d00c450302c41443c0152810b1590b00b2800240c1912441c41840c240501902d50310b00e0301c09040040241740341c101c450340203090300c0c0551100e4200c0780d9104104200219004844043e10301c1030322000e81201c032101207500428408030901c07091300e10650580c0d00f4107540380001039071500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 814420989 1250 814419739 814419751
    0x3090204110c010e0c06091f0912030305060f0d080306010507030c05060a09121e0e040906060609060314011409060310050c120105030f120a0e0a030f021017060d0305040e 75
    0x2d13540a00d404460810012007003480401c540c0d07a4540000d0b080400e2002000c1d40d1a042803202c0401c1040e4040d0245008001a1410300c42c80908403100d402d0040c003800d0140c518a0040005805095017070800c04070002c0c04541011540786907840342e0004540d80e602000040d010421018540b00005209101d00781c0654400350010807040701900700f03181c05103105000300046c8080700725018401c8104000c24044100d4030f04056401d03200350303804078002d081d200200402c042d00d811808100290040382c010b0079181181e6080003011b02c451901880440d080c09420307900c24242d13003213880b44d1614a002c02da220307002500ba034550316031b9000c40105681c4140c0b06441e8003500422020084c81d071441c02d160060a04600a25503410303220403035502e80000d81c182e20a071440c0010300e07040c00da0061000c0d450b000c8002d401e01c40c1a694034200119100c001401c02c9110324110103030b98060390300c906013240114036000d0148440c2e807220010400d8005103c0c000302c007400720612002075580d0ba03003055144602 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 814422239 1250 814420989 814420991
    0xc070f0312020d18030605040611070b01080712050c1905060d0c08060d020d0f0534080303010605031303090b070b0f060603090c040209120604120210020f070303090204110c01 77
    0x40e07400001c2d080840c510304080801040181c0c5030962254603100b041185d410040000c1c040d00e807070401750050300b000411903040001c0000d6202c1080b08199260703048032a1281070b501d0f0952240310b4030f04802440780000e041030b808130701036031007d10700508140705540542401d800c9244e0741e44003007005500074034074035002180e4842d0b8451030107402c40c07141030744500f003100d04000844890340010000c000e0100d0142060700405c20b84010803800300f10900d0746943c49004151444504801d02c0310800d80c92030383c51080120641c00140100000094038140d0b80c01c1c1d1501c034119680c0000600500340710f0003040d82009100c2900041c010304080c0146003850007103000160610b400320780758508100240040e40030f03540800c1000050320001c0f40c03030340443c401221301680d0358441d0000540c03d180b80030410841070050388140002c00050100001058400c0d80a0b02d5154440e05441d008134016800628655082000418000781c420781c840f0758800c0c4020000070b8400007008500311243c0100100c03460507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 814423489 1250 814422239 814422263
    0xb1809100b010203040e0112030e0a1205010f060302150d0906050a0c030e0c0105031506070204020309160617161b0623060f0402031b03070c0303060b19050c070f03 72
    0x350303050700540c0d00c20341c0d0a00007035240c01d113070222a6001800502c6041003502142c1c001e6000c2610440e0051030300140100700c451a592102105603804180801c200c449600c2d00820300d0b0400c105001d0b00d0112038008220340410340102281d221654010143c403071800d655200080e001668500c540c40c0030701d01c40340c400504100c20340b0020b403c036500708540c0d800c2c0394850720f941c0e55141c1e4403e04581e4000c0e10b0b11600d1a117070318440d01160140c06200c100961190000c42001f40300c2c03c0000718110411004c401d4103107007a035180300a440074444115002e41e0b80c910140043c525083d40034840b6044109860594600c41c02d03280c052100d0540c1c044111281612400e404055100f04803003201d11292204c01282c040c10040c3c0040d007820a107015060185801000082c0f0741c01c011000c00c02806415500f01d135491400d44001460b106c10301c803023200440d140c490003060800710750054070036040c01040d031001c402c8080c25050f01c10390021a01c03000e05100d5000003041c1c841c16003200200840c4100220810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 814424739 1250 814423489 814423513
    0x1b150c02071e05060f1c09141c0e030102040b030f0402090c040e04020f060706090309060908010e0604061a0a060e0a0b0c10050a0e0d170903031303081009061202120f100b1809 77
    0x802402e1100019566201109142c0400f12610240c081d40c000c032b0401644032001c00010901a00850348046088500402044207042d01000540d104510840d030744443c45d595120050124041d0340208500010403034001801401c02c0003008914802c0200014200300c05a0b403400305486840030b049002403048541042550303000144c0c00007030225240280903c02824031850f03998a402040542800d849030070015401a0040111890310000b51041c0c003415151a4013a01140300401118000d51a000340010640c4441003910000c85004015000c41990010b041015000240541c04d01d607540310351b914100c007820012070108000c551503c41003680302c041c000f000960014401400c0350020000c02c8a0118125140020b041c0d160411035a07584071000d044042d00340540003081c00368540b140108041d449074102c54182ca10881d000444000844106034546200381c20406860f4440d102c0c10302180c0070750300f12003400080605030044503c0000d920500c8c502c02911060040e0f0400c1d103640766 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 814425989 1250 814424739 814424753
    0xc031a09030a17060a15180909030c11120d120e0106030201020a081c0203041a1515160204020d05011d04121b150c02071e05060f1c09 59
    0x250000e0190301850801890b1480602011420349100c400503075a0700004049541d1148000c010b44400d403510f94581c03d0541d00a4120024000c5002000c4030310000003400b50070034040c8100182e450b555103002581d0550350100740011707145402d0752003450641c0c42d41c2403040400a40c5000e40707095a448000b00a07069005d000c41d1010400c680e01c3c1c0c1d0403c401400580d80015000488603801140c1503503440e0001040c42e280000312881c400210300000501090000c80b40e11820303810f1410700701c2c00450b00d440700c00d10301c2c1c42c02e0711000c00c0e0402c0b03180c03c4d0b408559003c0700c094812078580d0740304a07000d001c0a80c002800c0f0307030102c40801c02d800e0b50341005100c4d524414040c034948a03500c0ea045842414240c581c400b038811044003010400005420310a00d010240074807209203548032401c200c100300d0440c961001751040c48044001031241d80b500049010110300101e22540c1d210013401007450800061082d02e40c860b8400e0a600d00082000742403004103007240103842003001d04001880b070840c0c54146 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 814427239 1250 814425989 814425991
    0x4060902040b0414011e09030210020606100302130306020f040305060708071b030917100e0118080d200c06010e04151509020c0309030f010e0703080a0c0c031a 70
    0x6420144140800e211030200c1500310b4044d1980c044480e14001d0036100101c1e0041d04659105141413180040320310550f03000810300041c1c920850300041d540ba0a08030490b56844100d8220307034080c504581d2158118025170003004440001c000c80a00d06440b0b0711460142d0b401a000b8100c4c07010009420800e01800384501070300050346140501480c200104000c00c41d4040f10040040c020161180300101401109100010b000400104003650102c0890346c2d120101d40540c05201410441f0400c00030006105030b100c60601c18a02204450300c40e1501005c5030400a001f00741d96544090940040d82c0b44a5108448100b0402c65595a20b42c0041e0600b402d2060340b081c01e42000c02d5007400300107564040554051480c20100040f4486090041c030780588550340304d600058070004e44d140704c1b01008001455404000d82c111340000240036111402c036140301180e07040980021405200050a040c02060074000c83e02e440d582e03042e1325403514030000f5503d84c0220703a031210684149000f040c6600e10b407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 814428489 1250 814427239 814427249
    0x7120c05040905030403080f16051f06050607061e05130c1508011503270b100e01060807020f070e011401031b05072111100507050f03041406090c0406 66
    0x52204407540d40c0e031942d1300c2c0200e0000410444000c0b801d4450312128400b52a491400149050303062262424640e46881840300045488000c200d404650303041c160107014200c2e9005006540b4008484e25070900908a9103a00403110070401e51041426009001d200c1c06500c0074150100313456110b16014555801070f600c0f242542a60031102060305811020301411a910b0a41640c0d03000910072040340185910341469414000603109401c81e0118803005024a0348100c400e149a5101c0b11120350309401144900144c1c001c4850051048078400d1032091307000080b90045a100e45003170305100d4180442c540099610801c85001008122a0340c0c0100500c9030084c2410804044003643c8012071098030080e24041c4800024000200150050304111002041c21000d4550070f030160b00600341d61610381d10b049640b150300102c1301355280c030344607903405019180c5a40341b50020028480c01e03690001007040e500e0009184049445010a009851280c0d1049010300f05a0001101308012200d1035004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 814429739 1250 814428489 814428491
    0x706020705131107020301111b06090d03150806040f030905060333040f1d12040e07051c0605012015060f100509030129010c080c07120c0504 62
    0x20021500e850441e411401c2441c140411042c0c109086800743d4400c08500940540c030b444030749003c029165000c1d0200c00c0d0500141640c0403180181c859850340261801fa089400c1003410100c12402648038107013225580300c450054540d030304202e500b40711040740c09030303a1b00c1c2e010840e92080560200c10031002d0700003220003074203600f0101ca200c14082655000e01503442c041814011003010740c58140c1c0701f40c11005000b03100341840a0034481c00341c400c074060054902c1441c45000c40d80369011070280814040f080c9140d05140c9400f00e011003604001d840c10301400310801650408034004071400201c03080038a00802c60a10700b2000500002e01040d5084904012a10712080c03401f003c11100c031b20313220359000d0741616103c1d80e0003d10340c0110908a0380d4011003000c82c0c4108141c2020240c422030800710020028040a810700000101c00c080d116441490304d0400002158080e000380d62303296004901c40b0381003c0c1e42000e00c915210140d081100d1052542d00d5040c10050812140e9005c3d06c2300b514 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 814430989 1250 814429739 814429753
    0x8010c02060f131407170a050f0718021305040e0a21170912160b0601080f07030e010e010510051c0c0b0d02070213060e060a03030e010309020301020c010c0809070602 73
    0x103044241c0145050060139003644004020b41101d041020780c01030300d51260340003900030406450307555605007004125524000c19681550400340442c42404803034130f01c502c09694031448901c55000303600070f4a18443d8a540c0c03240200c0c0766102c520070502605c040c0f100502e00120141450990b0300c414500d01c007000080002c41842695104070b5120207112031541c0c040d4603446031003c0302d04040c590809000560300202d406815500349056000c0d14a00406110102da110071004403034060003225031991054810002c140490300c40c2c0e0082c62100d10b444000070340842c01c02c40c103e007511400d40304901034030032004c8140050310305056058805090070466240c40151340d50b0742420b1480b580f20341d461340380c800b01d0b0301402d840450701110030065004280c42d46209030b00303000000510140c09242001d07001030000503100c1c2046864601a00d815846041074002c000c401100a00078544003260155028440903038403080902034207a00017625260300c002454001249890005254000c00c21540b20003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 814432239 1250 814430989 814431001
    0x6060d091e051c0516140a030807140304050a0b1519060f030b0a060e0d1401021801030c0c080310030602030108010204050906030a0327170f01060b0403021e03070e0108010c02060f 79
    0x4e41155030500d0085035603411001d0700d00b0008070801285d00d44902600a21648070105030380007050b18407503081520360226058080c1d04541c590700045a0081144d0311808070000412920a203542e440246c40b00311a0210b400710b00451b1201c0d01e603a040c01c0e03111aa5a01c180f04083d04410310848054051500304034086146d000504068560b101d03c9040c0304040d8200001a1103081c017406004d904a0f80070410316080000080c001d600c40fa0f900810036100e0150242c0943c8240502d480c41e00032a921584507400e00e827a480302560025050f221140049140000065207500240d402041100c000503102c520f07001c10721585480051406100307801540ca940d00082d0003410002480000e8000c2c0c0c410008130580015a81c82c464001540c00e5801d480c81000400303000580c11000700c3c0b2480244406961000c61040301d0059004c002e500420448011018401040700348480c500c1c0141100c511139600c40c045461074900307030054070081c1d460f84401503603c2d40400645403c1079600b80700d080286400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 814433489 1250 814432239 814432247
    0x23031309061a070f050708060903031005011716181206050709080304030314090603040b0612010c120e010204032108010b0405061204110a060c03140c0606060d091e051c 74
    0x2c00f01c000c0c190720b424219001809810412100a045400304032440c034240824981e549800448040180b400c40060101e42c03544030b00810042c590b07403c0522a0b05458108a58001c00380201c8540d04002d000d040d4603140500803503450300108203030540c100e16103135141086c8083c0c4200810710000d200703036041c1c00c204c45017000003164222a010b181440400c030b0400030f44840d610804120580c2f00074084107100501810519041c010503080f034446881203e203880049c00d90f0342140101010a60b01e03c20b4205003603054000f965000600c000040c03800e5200d54503070000e0450300a00d201400c00ea4801e81c3c6260307422042e55405031000034031141c1000d10340380020781d4030302c18141c038032000c0ea21f110041410440040c1c01040e0409004141034000e030b40b82d001c02021070fa400d000c20790000f0040342c04800805082001c440c000d00440003d0030030b503580d000c04e0000036842b000c0d44c0d10020ba40c55018602082066508200911001c000484d440740345080113890269100400001a04603031661102d0382d1f04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 814434739 1250 814433489 814433497
    0x90f0c092a162d020909070b07060501080d020105070e101b0516091518020d060803030702010b0405041a0405030408010606230c0a030e060903070e0601110a080723031309061a 77
    0x2040b9000e50840e91b855040e142002c080d6400783e11542c1000c1404e1003042002d421842c1650713808801c403200105140340480c01d030790080d1281c00c0422040f0f130710060342c2d04055121400714071040c00c192a803000601501815845018015074a5801510754a0ad208203821707072582c010701500030103000500307a8071214460030005100d40355241145029403038100c45140c06a4680900c076460030050295207151154996104490800065180c10f4110010b4a40b601c14940120341003103064070700781d030345038551028400064001d071094070041c080040c400000340900e1018180540e00c4c90030302005020505440c80c0000050101c0c40810701400c50706010010b06080c000340c0510b801c0c3d41c0b0705c40300f401161192103145d018540500070208040358074580500340601404081ea0340c2540e010710044400d8448c2c5800200802c40c2e001013003000f01040b0030b00503240c0c00b480c41401d4000c2c00002141d03a40e185034011081094500c200c020308210f60344a03482072000401d01641e500000c0180c1c002a100c032842 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 814435989 1250 814434739 814434743
    0x1809010f0e0d09290a020c040f060b030112080c030d06030302150c120403050d1107150e0a1b05040606020f0f0706051e04090204030b090f0c092a162d 66
    0x41810f2500c288600c01381104865002030111007a640e0110041c025200c4c06041011400b50b82003040c001c041d01c0c03980c41108210b4a1510074a8156428426500300e8000100c40c00d0318403d45c144201c0300440000d2009001003450031000040301803451402078100701c940303c80003142d40504000c002400a00104903400d100c01d041082c0440e03a11850103550174080e0140e080490351030500c3c044001c3c0c1d4198020110345000702c9074075641c41d40d030070030000c10b48023205a84101c50b0040d00c0346100103841901c0402a00a4008405213620349400100341142c2450b801680161303c500c40c508811081480086007a91111002d08155810320601500905c15103c89541c5d40e4902c00c00348000265803000d131400707001180f409541d030356500e0500890020003a00c01641500840503c116101400103040d880c200000c5d08144c0c090350703152081500e1501c14005108201c2c00c14040f4000e07422400000d0081029111840441c800c032410000c1c4a8030000030a03070920300d45040841a8620100c00105e0066 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 814437239 1250 814435989 814436009
    0x603120304030c17190207150e09040f02040908030f0907030506160314070e030d05031006030504060b2d0405040b010b071e06020702040b031b09061809010f0e0d09 72
    0x803c2902c3c20040d41d4100140c0c2d04190f04d004030b840c5418a2800c250000018042d0b42200c03042130720713940200c0d8409900702c001c00200c0c07003100b121021410401e0314150b0140c06401c210120201c02c0c0c01040980700e01c0403040303a040c030002003004840038045a0150300300700044020500c540c00c0d81ea50a548001c0641254210706042210a110510a4203c0c589140c14643c0916160605c203101801245c002c0d44950b21030f0040300c0780500441d100d80150f0340f0074002c600c00c000c5514034000081c1d000f45030260080d1038150b01c594205010751078000905007101c0707441c4220116004000000b0140c1c0d20214156403040f4105002e000218514424141c15100410000c40ea1a945481d2030f80b0903c014141c101120104000d2860900225602070b21304140265801d03c48a040001010345411400d107243d0160040440c03900079034108603100585c803a0300500003918800054100368603504046a9008840e9146e581d8034007400018011102d69684c924010b00401d801044054610400350164000315 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 814438489 1250 814437239 814437257
    0x10f05061e091810140f060d0804060f09080f0d110a050c0f010306080f0d0210020c100f0e1911060408062406031807050a050f0f031501080304030605060312030403 72
    0xb0540134807a000450070390f840200001c8004500b14060ba1508075600d1440c60b5041d0001482c07401c0205111180c540d0022442e1f1404e0304081c404c1c3c0700038000002d000c0800030078200116540408000311172002e2569401040b04034628200102200300005107520717a60010031380300380080c3c1e0009400340301d16000c88884404182d82c800403001080594003492051046102c40d400c3c000000c5810160a2880c0d400d4900141442d0003280c20307440741244c403c0c442d5000e00410003130888954408220340e504d60704003190740288002864606412041c0300d040107101d1808900401c010004140482c2005403085810b141c500400d8640710080200401c1c4106200214020380c15030910200000b244c008003032175100e040000c182c0c65198211030f645000f83c45003903004901782c80c140c84601c040340c00c01051608981c000e14203018450800001081c1c15100b0f034401075110b00e14041c41c582c0038107900ca000310345940c5181006029100060007641c001d81050240050b11240042200e03405078042c03c1c19240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 814439739 1250 814438489 814438531
    0x10302091216140d0f080307170c1308010501060503011a04091a030c1f2d030902030607030606050304021203160c06030c050408030d050c040305010f05061e09 70
    0x10307040808462200d640286840c04042d207001d500305400f07485800030b551508140240c1031041880f0382c80c0018207121002c264800000300054021640041e26242000b00e04e146460540443c00003038400196862000c0f03048002820040b4490000b040b00798002d01555241441c050000d20041c06105541804081a401e00d11800d10490340100071036901040003091025124030945d81d0590b00b07030700c01e014001c620000351a12807142a0208112024280c003540044026a0750340c00b81c10010150300285041030080e60501c1d10030f412105a940c80214174010301c0d104060070302c2001081031f03003418030703011003440069800000d80e41e1003503041d01c5945918602e54005840d5015403c0d100710304a06141401007007201b11568141101d8181e2014040c400b1184005e451a0080d07016131039403a40b00f444000070100f011b230040360b0882a43c3c90414a80740e1a13450b501e00356605090101c0109846800f030100030701b064004010f0010781100b68000761000c080014400500141c250308510000b030000d005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 814440989 1250 814439739 814439749
    0x11031203240105040e0c0a09080c03060109021b011d01060b04060504120c0306020a0e090c09060f180306090d0f030209061b0c0604090b100e030d030c050f210702010e07030201030209 80
    0x406454400c45c00c40180c58516110b200c02c0d48146800000a508008001812a00040c0969001070010080c01030f0b42e0800340e805000f0342010400355a4006c007880000300c020350030710801030030a990407510036124814140c800d007034500a1f030101d19120410002040002d6200e002e4405440b501c403030003000c0d1401c0e8103001c02d41c0001e84e00050826440001c03140d18940c4c00150115070f520043c3c0d40300d031241e618000110b07040d00501c4ca445402210812255240c011950014685d0110704080b5540030352418000ca494842c08980040140d4010018001171381d820942c141d07403030541032909500e84030071000881c0d02405030a02ca819000011a41d84807141b000f4410414140005407032103032104d0381c807080880500780b540481800750690300340701c50301c051049600840404014008002803a80b5000450052801d00301020070444203008407800291444010003030a41602c5860000422101b001000d0400c0980748200b0b580c901010706020031707404104c103402c590302400d0040e00c880d800b2000c22 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 814442239 1250 814440989 814440997
    0x70503100314030309070603110405282c0411041a15040603050a05070503040b1302040504061a0f091f0b0d2705100906090501060311031203240105 65
    0x42c600024103402106048000001d9480380940001300c0f401d0540d514070075000c603480d10945500000703082109220743c1c00c042801101c008400441035403030004040b030070022090b10ba0020380c080b516445e0100b4140004a00122071441e0360500710300c02d41002e98a4036551101149424040c0786c48004c0001c0444019000030050b1501802d803401540c0046001c80059000e07000300c401080c07412000c035140504ca8030039a0312a01c01d549446107551920344a20402c07010090086018401c030401810040c3c0342c9002d05402507105283c045011a2a00c1e100ca5001c0e054400c41da005410282103e80c195445045031504242045400d1100e20840214072030f040090f0b0308005100c4d0000204074000291079401003050103201c13008081e5580c2c0c04804c2844201d01040043d0455210400340300c00039030180d0220024a00ca030b840001c072901070340c0c3d640e425140c0e598810740d0004210f80d810301c91428140000f09041c0c1c03c19a40d02d1071440d00b149000320407441c030026031441108010340038205034010811a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 814443489 1250 814442239 814442243
    0xf0f04050313030c06090f0b3a02180607020112020a030902031f140705070b15280b070b0a09050a0c09020a020c37150908061e0705031003 61
    0x18242c21030700c9082c1101c00c10b00c1ca100f4003000943c1740764009070b4000d280c442c3ca404d42d00e0240c0000e00c0c0602c00c084592040c3c2032240c038a0b02100b81c80e040c800f441c00c0c442c403000540c1c401d0804003507143c0da954012004c41408022805005100801403e00181c0c0d00526414a1340ca03034000050302d4034102c020440041401c080000e4240c4283c6201d50124a0507100302c0c1110100c2c00001e01204071001c00c02c101410058614001054060140074005030000d075406500c88440c0c881079042103220000030300f2003d8034118130079031003040600c000c08801c03441c0c140324040c0404100aa140922640d90b030041c030300f40200400140342c4daa5114008200f400e002d81d900b03890300141d904400303640301d8442c40025030110030202c0c05031146d041c802c4030170b04102c2c0074040091102c40001d90442040302184014025205050015114a0a01007600070355070202040d000c2c01683c411100a042a403481d250010103840d0020316880602504c080b494680340c10780d445250751401a85945544800c0004124a5040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 814444739 1250 814443489 814443517
    0x31a190606080a050703090305190201020f031611280807061e1406010f03050a0b19051c02030c0d06090206190e01141e0f16020909060f0f040503 64
    0x800a55141d0010020f4040c02e40c10030100682c1d1102c0744164111251004010081171013884401600840c050b1907115030407086c00003600d061180103024086034001c03a00304484016151060410a40c8509c00c40c40c840100402450080c06449001d012080c40e0079103c4440c0481c50851820400c94034240c500180d4090f2042c003400c0d500220000107000c480510103c200d251200d5148410000240d060080c90183c407144d07640c0c109020110003905005100c1c1d84261b4441da966000c41e1181d003201002c104070160499462414001000400d541610b8000711040d40d901c41000980da0101c1d034070207180300c12180e4507403202c5070b403414802403c1e500c400070b544100080345480007a24003000c050b02c09004c40c0e2f5103c1c10b03181500c0041d10b84c183e00302d80041d40d0b020280020001004070406481141000c04602410b004480c0314507440359000f595201800501005c0f5001182020000c0b641c1013803012000c0d00007841c004403d09101c80d401440c040e01030a100b40854113100052084a0b45142d43c660 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 814445989 1250 814444739 814444751
    0x20402040308040510050414042403032a0c360204030b0f0f0103031409030a080408010c021b0d110301090506041514011203090b040f0f0906031a19 65
    0x400c2c1900e5085841480c0c0100c5181117101182c1d032040c03084400342c654404410080b21000b4040c080248848900281d100001e200703961103160301c455011700150305c00c0d50b54008207210f55540c101010703050162030022001d00c80c001e000095480c03440c5801e942150796043e8032039180c0101c040d0030f960420b40071010030900030340c6102091403d0b001041070300d010b5041d60005498440c0b14082164080b5040c29070442c1030f100500000703200d542000c100207070310080c1030f0808030550006410314090350b004552003007000038104448107081c000e021100d88503001405a4030120000521040c00e040303481c502c642c4500810700304020501518540b0310070042d000700030102052802c00d07075580307040e902547d081880c0b1260607140c1100740120404200e50324039084c00d991901282040320303001c844c0300b00c0a01c00050340104603024031001070001090900c3c5003100c4103181c00240400159946c200f108007e041c00014400315101c0e61582010402506c4105c80941d941c0605003810305c01c420b6803500d8142050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 814447239 1250 814445989 814445993
    0xf07020106050d0c0e010501140d0e030d0f1b0e01020d0e03030f04030f110a05151806032415030c030a0e0d020102070204050604060f060503090703050613050115080c1c0204020403 79
    0xc544400751410402907040990301c41005427109101c0340541c010040c800c001075600381120f40c20a481183c0c28100312410181c103a20000c0075149800e20011040b80d454081d032181d00b0501c0014144103c15044c4aa046540307240002e450f43e0610800800384110020b15150390b480400441e85040300c50b181c06600c641d00d03441c00348170070a40340134191402d400d007108449080ca0080a600300b100e1000309045403c00110300c035042e0607000038840710b000315418081400ca0351031b010003d5108035144612594440e40c080c0b4011410485460f0841c01600c0021140300d53301054000c6a4129001c003d84986070f64078145038401070161150003211601918030303d400390f0394054014042c41842220306100c203650b860300f8001250801d1151401075000404104074071030054000f150030000701425100e0194880d01d8440c40d182059074900c10f91100c0e1841c0205020081c0304907903254a40c14603d103411482c0c80c003000d5845503c1740c840b512590a0580e05079024240709088100e0302e5001d0f0042d03458a64034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 814448489 1250 814447239 814447253
    0x80301030c080f0f300412020a08060c0909040f0507080102030601110c0913031e05070b070513061b051b010e0d050d0c081c090203240f07020106050d 66
    0xa102d0b80305144100d040140050070041980d004070b080003001050862a2060a918044103680010655680c400704a0010603544030040018080754200d9104200d50b0b44144000c000031548120b819404c0300080c0702c3c845131017000716102c1590448000e00075840c1d90038078180701d4244c0c540c000c045201311800000da901040d00a1480b541c1c00340c9450280300b040b102c0311600e64100700755007540054500005001e418009640920302030080c6441c0c14286080c4030000c41e4401d103002c010010036404a00d000c20441190085580111300e881c000d03082030030280c80020000304900a4109019824080710b003062862581c81c098142c101080715070424020b0180e0360914040051203001030003007514803080c0c2c108000a00b14040e4424010050b00148400c11185044008003c0350000400c224404d6111101e890041c1007040c0c100002901a503203204045c81c0003003683c0e8040000141120707104981a401c02d280358422015400d8080315911810100d00420b495040950701400318100d11003400301c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 814449739 1250 814448489 814448513
    0x6011e03050105040b240f16060e071d07030b130906050610260c070c0b13090c09060518030f030415020c0901060c021306090b09060d0807021c08030103 67
    0x130b480c10008459180140f00e10202d0580b14100a1828041a0704800381a04000e100000c001c0c90514142010f08515140400c01c0503015918103071215150b40030360405110480040200d103004008180304920a80341c0c0311070042c210303800e05544071400d02c2c0d2501e503070130010032141d41d18ac42040040007078a442401400140c07142d500540780151131001c1940102800142c0e4540e001100341700ca5410b8083c41c105002c014001c0780b4a80062104100141e1035607103800143c2101800562258902440b1841e20390195104030485810303d0420780440d6005210303001900d0a51902584c4c642c0c09400d04044660150402c40c2c1512910b0340c0c01c8410703440400603000751104003008801490120b4400c99a45000d139115507401050340004100176801440d480000c58806003548929880c001c4099048510660040344500c4d20746242078543e00d41028501d50003070046a4401c21000c1329100d1081034020350300004e00a28060231840c0c0c22140800412401e15404004141d580da1a0b107440f11255031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 814450989 1250 814449739 814449749
    0x40c0c0209010906090b0306060321090d150b01020c0f060a05070b040602190f1b030215070509010e0d0b040602090319051006151e050405030708030415020a110906011e030501 77
    0x41b03070a94480907868046601800340308014014400409070b0b42c0e0ba600018161516109609020050500151950714442d080140900a895003401200e905441034940e844161811500000440c075034540d141100441041000d803a0b06031078207107130502a80c0070f105841d80031307050301e120704100401c10815400500c41d148a504500354160f03c2e41030140c440720400d2140c0310100310b1554403010000601c80c40a0b41c1702c4d0003131046881c10000031500f840c00360025500c10001800000d40c0c18201d582118010355080c0003a5820820300103240c4500e942442c0180c001040c8039000101e00005a400700b1800c507180380072040440202c141d5203070940d07484c442d8000e1010480c2c2082000207031400c111002c10301c420410f8650f07c0900d0032003403515820b07001c0c102c80c0e0004e0007001c0c031000c50140c400304500000781403031400441da44d48c00d146031001910707002c8000104640c080d02100b0001000c0501c440c00f1664141c4880989407990401070354904502403140252a19466640d920350b9451381102e41226 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 814452239 1250 814450989 814450991
    0x607180506040b07030f14190e19060e0a08060a02031b0f21090c0f010203130b0301091b020d0f02010609020307030906114b04090c0e0d02040c0c020901090609 70
    0x406d52080c15150341d0030008207241100c0341070081000340354240c140b40b01700401d240703040b003010450344000030070b2403004003107000302004522400d04c4600c0d008060620326583c1201e6032088246081c011179600d14000b0b00302d102043e000f0001c50201e000b01c0d03503440d4580c00003a40c81307500e03041d071032110300216000201000c06509400c09144240c0124441d0b040c021880d007006001c1501103a0184141d03041c80911060461008014607010b000ea4150b1100150450512450396545010700d024140c500c0a8060208182c428190001c081d400003081e588140040c00d06500b01102490f00fa8010440b03907000305081400003040001d0264154403d854540c41f80104001e084801200d10f2400d002e0541159051200c01c103060400c00300511900d5a89407480d401178403803d41d1442c80c51740052204071121047c0034040b5042c06540220300401d8160900c07484c014001407000b5000a04d001a0120007900456586ca036001960348a8034500303000c0341e0042c0155031256940c02641e00200a54401d07854a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 814453489 1250 814452239 814452257
    0x14120d080a060b070b01060e12060c0901140307020d2d0903030324050103020d060305100504140a170304050118150c090b0301030210091205070e070e030607180506040b0703 76
    0xf4200c10141e542c5143c20075500d06803a801c050301618050204040c60354002102c0440041410341049101d03c03a4001380d41190310707028104005883c400d01c03e008100c07400024002c00c41004d50000d1419482c0595160072070002d4211a01e100030800000748480042446d40b0f021b40c2c8050b040446a01107a2003640e04109a40c00300c50840d0750071f44a0140d455400c85548030410856200c1d4010307003428004900c0000e031241d500d540e824501050b00c501800e045460302c00b0401400710340041580d10742810070103402c806000e56079001629880001079140480048080b03418000d003507003d82c0c2c4500c0200c50b01c802814680c00d1044d06548840d40004e41607091441c40c0390340c103200d034040004460f000440e060a6900359400c000c88856800854804c00482100005103c158607045000c5140250080c052850400310540303070800004010740244071030900292180c2e01c0c00039100d580488146443d0780b14070303421918000d001010f5800181c0c0500d0100e80400c612003a40020b205580c0309480d00558 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 814454739 1250 814453489 814453499
    0x221060306090c0603150303030103050a03090b0307050415031b21020c060a320108010501051e04091e0507141c03080a0b0a0b07030e0301021314120d080a06 69
    0x92010200e035007641c03c0c0c0140451682a0506030301030b5411464204500c402402c4103408070340795030000d80c41940c495100403c41410300d5000780000380034000131001e9a1541c41d244201420b9480355210b000c00c01c542102c00c81d003405102e64482c0c2c400300d060000080400340b0b420001404c0e40180b000b111030303808000c2c0450ba5880414800c41320f07108511170140c059a40d444040b40300500001d1542001c54844414030702c00744d10828a9a81e001c44201d03401c15555052040c01e60031500d0580149029905200e9a0840d100c08050304080c1048122400318031035040789018901c00070b00d0104154803010560b0b02504000340441d16000342c0f0101560241d000080100f0000e11004d8111026410243d500d03400c800f00c0d1107108466440703105018081420103c0c1e80100b81c01e00650341c89034002d01404503005040582c0700d0f04001c0c81c04401c400a41c01e040d4400c030050075050b61031090182400c00031000c4038203500c415071000f021861400560b118200580c5014022100889545080300d2620f1070102d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 814455989 1250 814454739 814454743
    0xa030c02070815101a031504050402090c0d0902030304090902031b1c03050f0403030905010f0206040b1f030203010e0106030210021c0f023a0302120601140d02210603 73
    0x403944030900521045180041200c483c00f400f601c0c250701a031400c0d40c0420600c01c1001c144030420000010749540385000c100f45c2140c2a50444d049102314244020301c40580d544007546a008140c500b01c1c2907450035404071080003001100360094050001080004a116456103c240c00a0082d03082d1010314000c0000300081c071311001c52580e0f001ca0340d1540c03542a100001d01c158001c1e482810034034508012000400c021307400a6101320005480e1403418045541c1c4010100c8075110b0b1030004000d2420140e548481c071481c003d00311142c0003200800b80300d4503001c9603610802141c000d00204088030044040b81d0281c605030205900503a804c510f0140f102e480061802d000542190802901c002c1e120021241844416440021407040c00c1ea80201e040344144040c0c03014003800c0442c1075450402a800c10050945100c4506040c814404204507603502040154400e50902c4c18520002c2160b0a40500c0c7c0a11718a2450b1070b8070106014052070641140c00b2140d051040d05e1b01060760742d034004c140d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 814457239 1250 814455989 814456003
    0x907210803131e08070c080d0c03110307020901180c050703050306090a2a0801050f0121061802030907050d20280e010f03120f05120901020a030c02 65
    0x2400c1410030400580c088811044824400c0d2141081160150306880c0c220000d42074603030290388a08000a65404024007612048010b041e43d00c00f80c050780000d9840900220f135243c4016040c00704441301030311150300510844603134a034001e0140505503182c0a40410647c9100610b0b00941d1070103104c21002d0b8082e4003a00c0780380e94541e0380ca070302e560748070340510826483c0a00601b46094030f54106609180c0094086404c2080402c105c4412984c40c020062082006911090094001307030300126480c0d80c88240c0b450048003480341100401c00b0341d1003440041203643c1c8000c2c01488031252004241090343c0055010f404034108546005445208010b650850100e0044c9210707002041503000f518003c0c7c0304601c505004242c1840740e100c541c0400e144018110401801c81003c3c0c00034170006059580203800b40c0000306500c61080e04607074407510342c1141e401070a0180010b1246400c41307644914101da0540c1361076001100d00d41801c640e09400b07900305007000ca01107428208014003d901c009030711 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 814458489 1250 814457239 814457243
    0xc0705012c0a05040905010e070911090d0c0f0308070b0105010e090103120c05100f1107050a0b09070803130303121b05070203030c0d021e030a02070512030c0105090721 74
    0x1140020300c240c0c004035000d0804051a0b6003284000c040000c00d603503584a111903043c040c5001041124000004a080101e03d811640e206864152040f0058070b21a09032062040c0549004440700803600784198259100c0e4441041116450f1001c0108a01c0b071011300f041901c030b40d03400d00e420b9807220019500c104034070000c160880346038801000070901c491800e5041c5c800900f0b01951100c065255541011440040039403d01d4075405500c0702d10b203051154514031124200c0c03031400c12041c1e69400342ca825030300c40090122402000414511041401904024041d04084075039405c0a841026051306651209030082040711a058000301c1c100d004103107807840000c10000071061403a80070340d0a43c104840a9805100a0040d6140901c1c10000c3c402801c905400400101d9840076194000038400a4104020341007403003c266066000100c000558400721090483c0c540c007604643c3c40c60003050545545076007000c0604c01c00c000049408001c0d1410149070003460384010110400144201c480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 814459739 1250 814458489 814458527
    0x51e07030b0f090a03030f15092906071407270605030109030c0b070314040b01080c12030a0f0507020306040b01050405060102010209010c02091e040c09050609040f2a09020c070501 79
    0x100c1c0000740701f070380303c9962a1050180041c6642c550408000069800c0d000072000942d40e003101c0302e107115503000d0951141681c0c02c000d41c05848040108070740b030054810003440124018902c080fa29801d118181c05040e0502e076018280c02c000c40310f50752940540d00c0c100030441c5090001f003414201030013810000c60f01600c030820b10154541d40c5203000880148004109546c603e1607104016042c3c1c2400c0c05603000381c125030019410306120720308181700101400d204016070b6901e030841139008010b07280010203030300f064034020492110588061282c0c00b0700a51500455040008000180041c903040c1c400a44040145036200401a402c0f8801c9441160206158072030400040c0f1b850680194007d150030004c0300c50950003a250102050701341d90442e508141d10b4018040580d003480b44a5201c0f02c200d071a0101400d2584034910a031158510141c105000e079840705020081c1702600b105c07002c1c40c0c0200e60008556400100e00207400c0030510040314011210001015842003181092010784401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 814460989 1250 814459739 814459753
    0x8010f0509070c150906020714010603150b01030612080706050108032d071703010e07030504150207022e020601091a01111005072f0c010c051e07030b0f09 68
    0x20050720000d003141811685004c0000e80054046224003440c10454810400580c45000070714100c155901c0e0f85a000078180c6c036069040021403040700c2412040d0324510701c00502d60843d140100d004d0304498001001c1c0790302c613418140801410100900c44a4000e61042101e641c807a00da064807403296040d20080345a4004d50120b055045a80820654010a070014030b0076a10365158074210280684861070000701000412010448104440d80309045103000c1002d480c1c15076803150188a05204400340c1d80c3c0c04600c101c219251000b9014211b8075118a48226082044807046d0702c5003004441001400b80000004a80341c0300d01815003000d10f060383e003609000c29030004403500040f05488034040d00c2201c084000075100751040c14061543d50380c0c0d26584066852081001d52140d040000d4868112445481706c10404a09210f603503409280100b01d100300e42c24420310300103610316981d001070302066031041203250002d055000c4074860300c44101c095440074100b0302180d104441020880d00807034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 814462239 1250 814460989 814461001
    0x2a02032a1002030f09010c2a1203120f021605010c0f020c090406050903040e0c040609080d02150c071b05030f03160f060f1a03011d030909060604050d110108010f0509 73
    0x29010a0f101807400001c19815a151300034502580c111078614042040c01c0302303142c000c604028402401e14400b41d07548005140c2d80060800000345503000c52103584801d84034249540741c048616034106038244a20341c000d5401c00f68002d1540905c80d00101c0c030003155403148540040317065004a0b07001400366103190b0762912860082d00c0000c010b440c1034001000042202041828204e0040b1054030301c0c03540301c9090034070241030101c00c0e0b0070407001544800610b07291310b0b500249107411041c200101c0415511492140c3d1114021300000a0000c1d01143c0b000c0d50300c00b0090044400c80364200c0440c0d0b0144801c0100b982c40348100c500031078059002c09446800324044031034202d6101d115200000d049070020b0304034002c40741241003229074201541c1c40644546400d01a803854010540002c41841149803180c90303a9101d00501c1c203000309070500001e204c0355261410740d401040c0162080c0a800150b00c0c3c6010450180b240560105840b1400801c04817081c603001c50682c2c0010b0001000b685501c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 814463489 1250 814462239 814462267
    0x608061317030a0603080a050712300608030f030a050f0c040b0919061707050f09090619030b01090e030a0806061c0e0d021c2a02032a100203 62
    0x9001c100c000c4d4490400000203900310b4000d0400380d0050381e5258136400e040c070b082009200405002800c0081e08070f2400c042d4003046840740408990040300c2582c070001c911615014024540c4030f500d090101080031010440400700540c85100e1215040180355a0404c2c030480c02c11080d20050f0581005110500406060000421140308002e06400500c0300e2a40b000c0e00000290b000f01d0001042c080609154400f40e26003d07030814000d0800324144142c012007119203006408140b4451903a000200c0c05a45a12181071610b00d2000480c030005912420604a1810284079440c1f02030f250031000d070003982000c8190b43c0254207658844020751030364001c104940e044803d04602002440212040d044018407502c046c1c09008009041c100c1e076003801c0641041c00b4403102c2104507401c080d444144681c00409541c0900301d41200d0586004041c00d22100b140725880029014031903031441003d2032440c05c1c03407101101e441d011207401c002c2c4000140913060310480d0314140980d0040c4896059a403003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 814464739 1250 814463489 814463491
    0x131d01060807050d03120513020117070806150f1b060901020f0306090402041803110f06090607110a060501062a0302060604053103023a090e0703060806131703 70
    0x28580302e0a84600d8070040386c21038100342c0b03060240080300d030400710455800081c041f0148003250364070055071400d00e03c00340c02072000420b078038490071400300060315184180c1c1c1aa6079112a018200f1f440c1c0181c1001c101000380d0811660039148280c000150030164140200c0b02121443c507203007429500c0701c0091022440b0098001c0364441d4598000b12180320101d034034402c48900980c0d03107440104103013240a0400c900c051108005802082c100a0324000000711950040480e1800f0481035000c04480d0782041e5007560014150707801d0000004d22503030702c450100d220034201c850900050010001c84c00b660003402c503008000d07030015030006406180039801540d0002580710020a001910303a00c24902c03000e5508aa006489005410000d05904100d81c14010192415002c100c1280066110a1030481018503042045c80080790001e00d20442000e8001c1804500380040341c242643c01402405080c05100c403284204d0000030100f0000c00e0300402060f4000c04000031000b00d1840c800070030740c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 814465989 1250 814464739 814464743
    0x180303140c07080a0527040b0d050a170c060109051506040e070e060c010c09090b22090303270303110901050d1107020d0b0405070b0901050a0807090302131d01060807050d 75
    0x141400b59035050021b4564032503035003880f00607681b40c14082c2c1e03080004603065018628052591421140d001032400903030840250740000e0b59000d180650450f00445102d0628009024041c40c8000101d282c95604110b00076401c0c010303581410907151091080342c0c015442804880100107000c02c3c04a401f0712100a1380400103000a886c0241806c16142520700e0004c02c0d1001407811503080054030400c1c4500f0083c080704490383c2e64540c140b2050900034081d002e6102a00f13960b10f25885003014000c0d8001c4605081d0b01c0c108904483c4828014030480d0302c2404185c0c042421f003040340c54503920300c0084424a01050310740604141513112202e00500300c803041108c2e9124100406d002503501c513820140c0c1c10b4402c08188420345003610b01181046d28035448540c52034414844038400741e800c9001d440c2d010286140c40170306075507090011030b4034404941c0040d40010116030360950380c66454201e900020109810310060402c052142e03801c81d04280300306940c54101010600503850303e04401c038204c0d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 814467239 1250 814465989 814465997
    0x1120c050f030f0d052205030a03050a050c1b180105010917070803040f08070b0a0206061210050403081005090f270d09090605040506150a050c01180303140c07080a 72
    0x66440c900d440c603107803200613498080b4102044000d03c0c040b102d0410000014500400d008040c5480c020a40d1042c011300c1c02402d2110200701a00341c40c1c450400e884509a00324212102c24080a8155a40d104c0548040d401801c42c00b4203000b481200d8a12103040f03c80694a602c080c0345090300c040182c1a0980c5036010034051402d000464100402c0a0b01c041e1403404800301400b480c14080c2803904403154050a01600c042c01003440340c0380c02148007030307001c20301713940841c0c9040c1000c42c01410090140c1c1210a090710f42010301c0103140d80000440d1145680c15440c105503038542041000381c6208880d514046900c6400181000c40c8504000e44d444010b0f080e807461aa505c001c0444c10001c2280c051800181c0c1c02c0410030854105002c1c80c4000c00040d6030402c81c2d81025008a0070715541c070780f82c94441c1c0c0c200148045445115204407128100c041c8000c001c08010040c40260004c10240141c00107410522510700d00060402e0a0b4081d9107507920441c680595584d9198040e080906060244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 814468489 1250 814467239 814467253
    0xc0a0203070b1e070801060e0d24140612071401020109140606130b060a1112070f02030601080304080a060b0117090a03110c1c08040308070507080601120c050f03 71
    0x8502c1102280210740c460104600400d659807054040440109910100a10b0f000100300040d00603c00c00780b00d000071758036030300c0445030b506024104026501580c1e0800d09120074011704c0c90741e5580f1807224a20283e00400c400d880e144200640584100d000c810513170001042040809c05949666101030010300001c07402c40455107410b000403081011541c041c0c1c001d10100540c40c03501c0d050003000c40090400420a0a0301030000c2740840c01035240d1035080c00f034442d0040c0c10454082040803000e500c0c9a00456075400c244c500001045d01140b81240030340b06a50010600c0c541c0402914241d5481c0c5000300000809274480300081c0840d0340c1114180a0410741c0020310501c1019014400d2072a0002440300551030700c1c0003040a0103060102260340c102285003107042ea41c2115107060f0b4880581620b14101c0c681c2050901e910641e0f0006000303080c00510399040042c00f1030301108070380d0f40f882683d2044ea43c1340600c0780280c4140c00010080311aa07038080c4601d01d061120400b98180c0a0111015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 814469739 1250 814468489 814468493
    0x1c06060302040203010e0103060506010201020415080613061203090509010305190c0b0d0504110d0302060718050301090614010f03080d09060b12030915120106030b0d120e0f010509090c0a020307 85
    0x49910a07002074060b021b10b040180140b040b24002c00b504180284001c51905240000c8003030f41a40040c00c520400040d2000301d560384c0c0d034007082440000fa0141041100c41c0d81da0030b240095501c07251040b00450a100d100280038a0202e900074100d907000000b9145581d000005410001400356045802c5e9580c0e20002c0303016507100003d8900106105400030b514141401c0891641100108140c40b030141035040000107a8081610f9030880500d040c141200c3c94900320844948406820081c1c1540c41e041000003400000c0c0c00c009003281c001151009540d0302e8242c0d29240d00201e000c05401403c1c10814841e0030030f030350350050b40c030f10f0b0041000090004031080024980040d03100031503243e6101003070001030380c603000c5003036030004c040200898a0800804100b003580101480743c0e070185513407041c1c3c0c045151140801122156400440b450011041040140c44040c00642e918054411594542441c0d40640b0031140002d500a146021594070708001021035803041034581c085000500c00040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 814470989 1250 814469739 814469741
    0xf07050f0a030b040c14060702130e010e010e030703080f010b04050105090a030b0a0f060f0501021c0c150f05070f0234120605070201020703091a130611011104051c0606030204 77
    0x1000b00d2103111812907851900200000031600c041c11b09200e264200541401030341c3c0c814511000d030840301808600082074a6140e40100882c810f103988950030f2810000b20040301000800003148280c40c2c0c0e00480c2c85603548080800da090081c8a145541004240100d43c0507001410303007000001c2060214540b81e40d5091003600040d0303440c0d280e840e120803603040301499901912014041400a50007020721f4200001e58900c1c0c0b00c80c020b0403a01c0100c250b01c000c03a101d005000940c50b08071101c01e00300c16002400c6001428400d0b0108038051078040030902a034450f0720380086501150303006044480c21402c04451030740005a5126001c0c1b808c21105030039421070000c1c04001d0211405803610006142429814ad1f1002420f420440e4030401040000035006140607065495010b42c0e490040c0c110040c2c0c4615228140c02c00304698200d03100029200d41c0800d00c980d8411120009201440740c0c007080c201a40558080d06078003540403086040000c403240100031a25015400c08155145e0341d0f00868 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 814472239 1250 814470989 814470991
    0x3070f0e191205010e0606030d080c09041b080601020a320610080f06040c030f03170f01170a030f0f0e0d03020610060c0f02090603100515120f07050f0a030b 69
    0x4090b84007040c0e41c2005004003803050560408590001e4403180c03518800291b1a4034421041c1014418950049003014040c00165140719038040c1007042409814404801e82c0001468036400155004c00015101d506c04201c1c480065070101d02c04031102c0c080c443d5204e0304c0e00310f44075111141800340010400340004201c414010708141d05121000780c104103206003805000c0d01645444e034407000910000035041114202140d81004464961064624040f02d041c40c0341481c0045071580d1400340900c50b4544004941200e4040480a00590314940059244c400442029000c20310b0405030440c079134004c0383c00c81143c007d5850202c00711000b200015161135000c00d01500140e000c44100940741000182e0f402c007601c000c0c204050120840c1c0c0d00c0d61a000ca04c81c1307009000311603da01041c01b42d10200900c182d1110351a00a005c0d030f2a04a004402c40700c0d2001c0c001e0300c10343d0030a13a1001c00d6407001c02c41030503800b2010040c080d41c07800e2030300380003900502c4100e2a401005181c0c000020894500f516 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 814473489 1250 814472239 814472249
    0xc061107051f14100504090c0e0f06040e0a030807120b1203030406140c040501051c02030f041211030412050c030f010b0306070518010c0312060906080607030203070f0e19 75
    0x5151042c2c16a11141c1c1103e5144845090981103c4140a01c104030500c0400031140211000319103400c80c0c3c50700001511071548907000141d40c1400b0310090b00740360445148150305c1a1010000c0b001c548042e60b0b5103420103900500070406240105550034800d01810140c407401380400300d004030001020601070710099a81719500d030400710a201c104001030095204403551f103c0207840600784200c1aa4040c070892281d40c0c103110000546802c800883c1e02e0426150781d07100803c6459282400d141286001d045404641c042e440804400307509000e0b002100071030ba0440000d50401c0d0604642c510100b100001c01c1e1034074412141c3c101507070380d82001042c0c01d10b41107800209107180070a040c545030510280030002030040a02256104844c400309540140009180180b00e0b900c03d410145c420010828420780c103541041d0000c500d09495401c070034126200380d011034002d075440c0c2104800f28002500c0c139100184103401425140d51140300807013008030380103000d4811014100510044841c890b406 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 814474739 1250 814473489 814473523
    0xc03070e0a05070207061403040c090507050903071a071103010e01240e0f070e0103060306020a2f15090102132c090619060506031509090a030c06110705 67
    0x81020070021400340c1c0c0d800c1051800100700312130030804050680c0c00110315207621504003000140c148003070b1601d4039001b080c0461003044681800ca030001c00035448a1f00d076900038490300740c00081c07018030b042d0b41080165001ea405030400b9510b9840c0d10058003c00407441d0b0540d01e41a0742640583e0031310030340503201d8203018195940506d00e010000c11800b10303400001c00c00140d0b001c000a02809044440d0b01981c90302e004070289040d640182d004110540012f840300b440490a9008680c10030010008121208040d04100c0c04561002c9415458940304c1c250030307005800d402040342c818420440d04200320b2400541002400a41c030305685070b996010002d00c1c0b00f4070521000060b072105034124004d518086181c070f00d02e0030b25180d998a2001515480460035824841c4d42e25905c103501c10b50103014010032075984c0782030075560002e098042860303c600c1740c1f800710081100400002000560240d1545540050305001c1d1980c100600e00038219010089041003c171002585c288103940220b028414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 814475989 1250 814474739 814474741
    0x111c02071401050112030323070815030610060503060109090f0507080f07020a0b09120f030a1118090a09060216050f2406040222050f04022a0c03070e 66
    0x40200d071015030901c008106074507000060000d400700d001c00c183d2198040c1408140412100581843c03054000204041c000741c42c018011419405070130540200490820b02c216010481c08064613210b081c2d9003540d1180204408121850080c1c1c003075548880c05040a4070b400b0394880010050f25002e074401603d4a548000b08081d6540103c50150040f0400409081c0b500c0c15403001f0396200000b20004e8038461520000400d2883c0402030101548004a085601e5001003c4005100d41054460080680c208412086000d4118054070007403a02e0100c03449581e445d0030288410f603000680300f451916141c4071002c001c50018001007d01d80c00c500c1c4556401201400c141d810140803000b2a807440e00040c0702c11010b011411070002600c00e10302c98000312a120340001a00904c070b08003003042d07004a118030788480300302d07214075890464805894071800c00d0049001c010491052540c20400b0001d02100313240c0d111000b42680e1001481e900881329085040f40010340b41c01095400303e030050182078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 814477239 1250 814475989 814475993
    0xb030f0c011e0c0b2505030105041d06280218030c010915110a0f050a0b0a020a0914010909020313030e15070f080403020d0807030809070810111c0207 66
    0x5410201c2e501c1c0320700d1012003034100d0010000c03800c818029140010f9540440d2114907809001d50304a41c0200281c6164030f00741c2d602502c550403d214007403040b40b4011000b840900704440c02080750025102410b8030ba907560302c80e0398043c00401d210445480e050104030340340140520081841d40800e072181c440c00c0482900305440c214000c4d04050410112a9003006205028110048a0720550408003c5040525081490503850f040c0160003480910380d22024004080345074050b190144100e0401607840f07901c92800d9208a11442c0001649020200071852403125550a4500145410020381e40d6440b031034000d0b030f0000d448004484100e6904001010303081441c0700e0254a044d524075050004041003802a8003402e88050140d181d0100c032201000303100c4040b5405940e00401818142c0300398180301445400c0719408030042a00000420780404000402000b1100a43d0061444101407103001001e40340030180b21001180c14080e00c0b030758590074030f2040300a500510340161261903074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 814478489 1250 814477239 814477247
    0x70c1110120b0301060f140f13060602060c0f0a08130b1f121106030606070507080c091806010b1615150b040812090f090403030c02011b080105130b030f0c01 69
    0x41c10188207070700d8031170201b10724600a0b49a0003118254550101c40000b000045140031807440c12041c0d00003030000040025220380ea001e00d007a100e036503080718420790310318484404a10072440003126200c814840f2200d0184076102103035000407041c0300c0c004000c04540c1c1c1c4d08440501540c105002010b403c0c8001c82c94445000c0d800000c0403001c14405042c442e584a41181070100102c081c0903c0b030000009400c0d461b000c0458407404e030700408030340700c840e5900ca031681c9924224440314440c016010118040051380c85200043c4481500548081c0c1d180000681c030541c0301084080e2100c80da001c1d06030100c1c0e40040e00240c1c0e01650180818041a07558091101910503000b2440c00c000174041032000c038500188440c4c40c0c82c0c4240c00103a881044900046d49075400e501c0c00d07940312001500f00000c0551640060384031a5660700240407407184400c1407844610105200c2000840c0007004016031310340300c5540c0801c0c0e2212800007a400700c056002c60308002c00000780000c10761003a1480e4540703580c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 814479739 1250 814478489 814478501
    0xb031503061b071b0512031909150e0411130e06030102031e0903070609060f060801020901020a03032703090614040e0c0c0f07090603050705030a0b070c111012 70
    0x1c103180901c140110200c60404502541c84041c0c202c160420f60300c110300784000c0e89034000d0b145c0205004007a46009007034540d070307034800942c0d00381024a134a5101c40040c0251040c2040d00e180b0b4a100315003440d2042c3c06c40c3c0708418684020740c490389600c800741c549040d03240107100c09a46441e00e003540b03c0c200300303c070441c0d120b015000500a0b1710400802c4017100d0701002c104090014040e4072040f44e21400d5445186005104020345080d2420700341c00200b1186602802404201c2203040c0030f13055694ce00300b4202d009616249025070040600807000078800e0f480183c006900c0781200c0a920303201001039001442c020401c4012510b0441c0c00d12019400103441095080040d01140ca0b29051243d00301c0811000340c60300c9800000030130505a8102c042c0600d1103a202c0c02d400300d03281c0c0d65446c020180901010703c800d46240c000c04002260743e0501084c40f2201c690801400019900c809208841e44004210300b034526a580030908034460b80c03019082035089040355100d48a00046500b54130841d0f42c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 814480989 1250 814479739 814479751
    0x51603170c0d27020d050c0301050c0a030506190b1c06032604030c0b0a0210110a09080601080303070e0d0b160305011508040221031306030615080a05040c0b03150306 73
    0x10700c2003088211100c0f14400780c00407507040c0d51040100030107180c6149000e85021640c0da0550806003001610102c0002500d4142140da80c148100e032208014402c04071002c03003040700c18148482080c007584100000178200e07011040c0c2996602d6140d40b0702201201d44641048543c510b1907150b0b95083c1c241b0400e072064051088603128a03040c55550340d4051503003039200746450140d0101d01e20080c1402808003d0450005140c2841880c0c0c07180f02e190a0756001400200100e2400303800480c51200c0052800d0503909240002c6240d61100141079a41c41d4440e4200e07039209130001c40c1c0400080021016a016203076070300b0f90f0045501e02c15806001d0b038005801a00d82e24a21000c84282c0e80d03031080403107801540581d1517500c0e0400001c917000344ca0a0284142c030b4140300002d02000c115450005040c01c54035181c1e02006807648454914088040c040c204500040c2550046042c045040c0d020076089032081814072811503441120000e26042104d8501006024420200041c1010701421364886 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 814482239 1250 814480989 814481021
    0x40f0b180f011203030e0a03020d0801060207081015050315071209050c0f0402040914012303101104151805100c0602180315010f0504050403051603170c0d 68
    0x200c1c24082802107803005210350311202070303402c2c0280b040c10701950003240300703403c0c030b1050350019645420041d50300e00409143c000010741070000090310364400700d00320050314454005440340180a400f0740c1c0103040200b1001c540c0708d0f0640400156030303a0800001031520001000030300c01d441c01340d0f00681036906201d145540039040c0011617001500200320207040603000c5a80c01100b99040c00828024041c0d42c11900d0310600c2c052000d2440c4403540c641c58100c82e04c541034180d500c0c92038442030880c2e00009001a425134844032441300c050185800c44000701842c550510305003a90f8000000c1518042038204010410f0b0707079000803001d00e600c015040508426610b55034414046c2500409125200fa409440c03141d000c203154030282c0f403100b4040203440000b0111981184140c1960a4000080c4600492041302c50350028180c180350080d5442240c01d52942d13411300400040403008141c08410031400c001c41000507491007410700c3c1e070950007180139003509601d0799403038150711080b41d8000802d442c00e4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 814483489 1250 814482239 814482241
    0x60720220b010906050313230109051207050606060307180906090c02010e1011070212300405060c150a020a02070b130b370e091b09010e040f0b18 64
    0x399170010201c90b081880004083c000409a0510310300780c14820020088103000254052403064054001c2d1000c02d000b8415034040301c40400703400f40644942c6500500c66044000041d40038689400070f154002040c0c1400702032000e41c400b050100d10703e80d030000c00e00c29603a444180300c192000c4c4500309440c003090008012710b0040c4003103196110b00030801d10380d401d516143c0b0100703103041a100359075450780d010700002e0620700052030361500c41c909884030750790940c00300844c0c071064030b80b240b0726041c0c0d408201511703883d01d8140028410b4913800a620301105201b001580e0094101842c0904d00c00c0562840050f11943c98100003801e10215038455110080e040c480f10416030003582141080b40c1010310f5483e603500c584115116041120012036044041211703003032221203a0802030f1038049a8035904d0ba2040c0b28000200403190741c06940d00c0110003004504500150b005400034003504405060041d01861501c0001d025101400304121100c1d84610240485e82000011460f801203040c03129451 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 814484739 1250 814483489 814483499
    0x30a0504120c0510050a0b040f020a110d0503070f0c0f11150405011b020d240b18190e0a0f060501090b0310090305040f09020a0e0906060720220b0109 66
    0x50340c15001300000e92103564101141440e03038240e00807585854080c005020b840c0006400d20001c2d00f1074103d40010441e040031841d035000010902c40e401381800d889182c07c544503840101d40c403444080c240418080002e05590126403011191491648a0701e581e90b15001c40c80180030b1080f240c10720140048a0611003805507a8000388004480c00c0001c1260150a9641c000038880300e4014002502c10815079a51820321150800421104061600d060200100c600107012088892041500c1d04000750004550440c4080c2d00400442202d21004560741210803101800d08580000494411512400031b004004aa0181900502c00039508004d0b101070100401e44603402e904a40c0002c556407003a080c101030085050324080c01016200005541d04c0c2d091020080d400505814003140c1d0020400e081807505501041c8601f6002d05080e04041d259a00e01800340c0943c280b484119005a0884140d42c441c0184121014041600601611303914030106048601d04000b09040007c00034080c40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 814485989 1250 814484739 814484743
    0x1103250504062109170307021501031205070501060b040b070201030e01090804030f0c090603030302040303120b06090d05120a020606100203070c0b030a0e3310030303180503030a0504120c05 83
    0x12a19020f14500018140d60f60310303e038001c2040c604c00900c0d0f402d4100e00c034200c8841d00d0700034600c104003e8080700c0b00080307245420761320004244030040249081c6845048218030a4004d00840d6200714000700780b00c1d17200c06290903560820342010150b4400459050195070340b500842e040301407160f0081260240e01d440b100254480d80c0009400030301d040101c90104420003420200408008008100701600c81c90020060740c090f00c020340000f0100341c41c2090103540b6105a035400d00700140201c1c5820f5104080c096200090b1100381e556004030b5040c0d16401b0030030070081c8021130480c0e02910551400608002c245080c0810100465006108010000704a0400001915000341403180c5903920114508043c19243d03a034009030f801144d0b6007501c215040e13803480d10002c112000d10705480140b5403060030501d504417805020008070110400c0420f010b617200d5111408180c8080201c03240700d46415103968804c1c3d85040f0f080380d6031400c200500a07a150b1200c0344001030700d42402044d21079180d003a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 814487239 1250 814485989 814486007
    0x140c040512030c01061d090105160e010c0f06050619080615040b0613030606060f051902010b090f01060207050f301024030f1104110325050406 63
    0xe40107840c14080c1c0380107080e08000340ea8107031031044024850242c8501c00890046280707107a448071a10759002040080c0b2060042c1031140034400800424428503503802c0307032070400e00001203040c800b58458401c08a0301c0c0c0ca01032641c82e8041d1001142038140b079024001081c5030491042502c00500c40113000c40000869540d0b0091180f44083c0841114500000c0040158884042d0301c0080024a01300c440c21820041080342d0140b0401c120740c03640c1d003200b038418440301c000041c0005c4080001c1c04a46502c4407002e03001070010b100001c0d0b01c485030350114003e803a06460802c0c10a010304010481ca5a040210740d01030641681c1602c0e07040b0514001c14605800350598002c411014130f80030403219240b650451b260302c070800844a0440c10040c08038000c1c4541250031400104c02650301d00f1a50410503000105c035844a0120391645454460581c1143c14825050f8001d440360f07500101f40000b00c001c2d40c002c1d0b8440d1190720385d03604031107072017250318007274400303103000d2003012b0104021450f0408401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 814488489 1250 814487239 814487249
    0x90603050606040f090e071707090207051c12050106020c010815040902100302071b05060f031003050a0c15080402090105040f020f0414011101060305060a0b181504140c04 75
    0xc60903032509000901a030040c2c1e0815510b80065910000390344d2100d400c5510248090400d4541864803402e40300303004140780040420a9010800400c1420820340c0142074079800b070410340329144404110040450703850480880041c844040812a094a501c01d09004281d1030000342803400540340060440b071030041850240d1807a02d07096001c1c13515280c01800c100ca13070081ca1030104560100c1c015009411460058549900d8044040c12140503064080c06445000f40242e0a11030322106240490340001c2c4003658030340d061500000081d20401c5800d8480d4809c400c0443c84504000902104a11400c910f02c00c010b90b0f0710620003da02d8041c0391a0641c0c0b4162004110080708420460282c03060b010200c0c054200001d00040c5000012181544208241d03504228413050b80049400e8038440d00028005401000100d656000c1903403009890441c00b4200c001550310724084030311908021101824420090380300c102c010724261242600c490001c24486d1500d0a04442d240540c2c06a030140e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 814489739 1250 814488489 814488491
    0x1020406020c150903060403050c0706020606031b01110709090303112802030f040b0a2705011805040c02010c020d170f060d0b15033901110d1110050601090603 70
    0x902c00310350511404c40c1d100800c00340458600e400d1078034008281e640318000301c0380715009020000c500644040349083c0664001001803101e5001030707000700e02e2008110052030500092004c882c042c140c0034840703e8001d026441c80002c10110b85d08014054030721440b00c0e10b0510390b081014000140090842000150403004442c44403801c1c2d40d0142d241d07119008400c0c4400e43c02190010380c842d03120000b0303e01c18041d40c0d41c504008100c0500b1441d500f10421005140840c44d003024012940300c0c40980b503008800da14008609a50766001c9400c40341401c1e0344200603510750050380c9001303030100440b1901a48600e003043c904840358030301d00759654000d4413104156404034085401aa00c030000680495040040280a410601d581240d0314005c0c106007402030080042e44d10848407418048001a0502003241e0030300000c035407850030b0303030600214014103000540140d254080d00401104ca103089441d120003003450100b10310149070800c40844c074840103080c80100107050740e20401d00b8040f1025814 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 814490989 1250 814489739 814489759
    0x112050a14120d090224040909050717060a05090706020a0b0606091002070f0902031012151a1f090e0421090501110a1e03020f01060e011701020406020c 67
    0x1080e98100702041c0e00c0910341002c0400e1422602c80c00d41e03c84881c851003243d25540c000c00c84401c8094070f41e0b42c0b0b210040740c6072080c4410070a0800c6074116682c503e1050b070503580d0264035a00c40070000c0011225528084e40001c0070440954064402c95800134022802007040518000c002540c5540c14400204103031818004645252140c4051f204104c5000700f00b803a41d50f4079054002e55914240c400c08014100d10b400015004900b031085a000d00081c50590b254076042101c2100082d220780000c40b0241e031241c3c012440349605200c1c0d00e907076900340904080d03440050810007081403908083d020351207403034980c0c0b902d1190300040103100b00e40030314910b110306980ea0b041140c03248030781e10754409400f129112404282644100a001519000d89a80341d5440e104400b03103548600f2a01d009103101c6c0d070103080c080300b21a103111180800c0d200b84105d031003901201c0029401c0d1541d036070005011052000051000107114010b42d81012021402142040c0c03401e0002075590740d2944540b40a248000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 814492239 1250 814490989 814491023
    0x60803091c0506010b0a080a0c050703030b03030d090c18050c0313050a08030f060a170a03120b151206010c031b020a150806010306060f141623060112050a 68
    0x2503071203150360080156660340d07039910310084c5c095110504140c00a030320480007d0400c0650302c0344c1d000040d115691503050440e01c2da0241c00800351340c0056941407206006600d8841c0e1140120618103100e851840ca90515225a0729000c150f818811a00303d41040e0802007051100c0e41620ba03c492202c4524043c070b040c50420504050a503076014141420020030800e0310110700c0000c0c1d0003410700307407044401542e0f203042440c00070f81c3c04d5581c00d440c2d0304150140004030b4411408051070150702c6000141d18902c0400141c04035007164280240d0090109140d000305000344a0540e00c102c00b82030040b501e51407681c00805240c0d60342ca2801040d103c1d40e00781d6080d9240d401c41400507009884c40030040340e0103044e007c4c0242104803a403c0c0000d050400100d00c0c2c42c401c100f614503284460300c03044280d002c3c001c46100e1a400a104040428424000c0c0e00d020030340080381303840c0140440041d503080305242806141080c4058014030565410303060480c0000c0c80000d130f0340001d550440c01820480e9400c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 814493489 1250 814492239 814492279
    0x80f04020a030b0a0203011e061e110d1d0906090106050a050d051812041a0c030d02041d1b04060503040f02150c2815020409020301090207120306080309 67
    0x142e000641481d035035000f04a00d00c1d40075030056044c0d0b41805205030b01a00300c41c441c1600400c60b4003901000481040e5400450b2003a2000e00b507001600d8100220044d00d040d60191809040c584454000384030707807440a107440f0511004441e800c07816902414141780140104501150620a035000c12070f001480391404c40c442c20980d50603901118050186080880c1c401030780c4a4154040705c0b040c061000301200c00f201d944200d8007100d110000410340e1000803a4042003d4000048825260008200303e03416140244010405011080c2031700000da50101c501a55054008246029003581c9101120102c01c46a09980442c3c001d031410903660f40d12072400c4100481a000300a411150703400a1040700045100908058003424084a081490b450342c0ba07401014580190015205440b03000b40119446080c42c032149040c8480c0503140580d6407019038101da20036440b14009513800b007030800412003020040402644d1600d800c1c41820f041840d080c0d02c034864108014400e000030026031980300c0381 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 814494739 1250 814493489 814493509
    0x1207050d060f03051903080a0c090533120c1b150901271707051b130504171c1b1106090d080a1107060b0a09020a080f0402 54
    0x20340050000654a40022600d01d08500003214075014400440042c0c000c100800c144264055681c2c035903030707111005098000d15681c030003241084805000400d4035101c81b40e009000000481d24900d52550340d52107800d00030f41d1054074680c0c0a1040003110240400d007103070907400611030b403140c95680d18002410540b52a05400b8111b41d8060441c90001e0200c506010f00c0c480c000040081c810b050312815021000d41040c0000c10040381190391003404901102d05600894070500b9540b0714085168403010300e03044256850600f45140390914141500303140060400f00e1001e84014003150a00c0e0b07448990b00000e001d922619180049040300d458402c2c0207103120f842d001c00404020f055510030603800407240062100c1c01240303130300001020080c40010110320880400d00a00a9082d0755002160006005014000540d483d0520f05000f0451140200a264031600c000604846840d041c031201c1880383d445010700c64410700c01c0403441500020041c1e4415001c0c00303408a43da840388005140485 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 814495989 1250 814494739 814494757
    0x7030b040f0f050604050a02040e160311031006121406041505100210060e06030303070509040902180702011116020d06060906060503310b10180903180b120705 70
    0x41800660342040805900060113071605540070310a0369a404807080a902c540d01c281005003480c01d0000b000e044107142c0d480b807103c40c3ea150100d41c00a0f26005002103400a032a8910800000c103400c1103a2a00007450740c05900d19400d0030f02c071200480d03004010340350005040e07900890301c40c5a0142a0080c00400c5000390100802d81e022041400000a5583e00041c680c0c0c0c01161500c0000316030480d081500510a500040046213541e035103030001c0b40c46030444c0102e6038115855640303100040e40c43c0c10700b110720040440002e074030702e1900034002400d44524075016000c014040080003100f4140868040341171341c0545802e60102d0380d600d01403004001c603038401d1140c24030700640411035650110085021300700c181120042041c541e04540c003010945401721000350b00d10441da80c0004c0c0711000c12a4415042c0811004080d176642c1e480c1d00e01290086144400795030b43d1104401c054102008401209001c207450003100d00b065610b00c16441008502d01d89454054002181c0c0c070f02c030703a0460f61622 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 814497239 1250 814495989 814495991
    0x70806101202031c0f0801120803010b0f070501020a08092a19090e010603030f2c031903030b120105060d06021b10020909060402130504020313200301051e07030b040f 73
    0x1210f403500040c011003c4981708000108110b00000e40301480e44803440203035800400300b6145900e820a031800e41d078058026003403005000d10010307020600a201504184540b51103181a51521407840782c1460705c188500180703050358400b0034504108000c210303808000180c0d13407030140905998a041100505901508a9a0521440407882e42c01074000310100c91090f00c1e1035210144241e0207907007440e0707424002c40000e0000c01c0340704c56204e00a060414507600180946c1c0380d40e00100d0710001174901c00c18065001c00e803558a04d00c0e050a1110603134103040b5901d0000c000c54142080080e8124040100c040c1040341c0104d44c034100014011501e8500326030510460b541c5080510107000a508100b141d903200303050010008089003440d000302c4514450200c1030314115400c0808001c004d400c064005141220300007084d400203200741e526100349181c02c03031080c140000c0707990400d400e4030002000c1800c00c0c07540308180ba81c406106400c154004820341000711300c1300c1d1031b2800705000b010358a40d000c0ca12 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 814498489 1250 814497239 814497283
    0x200402040807051f05090103050a23100b04030305090f19030507240e1210020d0608070f081911090406020a08090601180203100906080f07080610120203 67
    0x81c410004007481101c4040e03e40c44075020709540c02d42040a11440b841c80414410020034045620940c495580003000080c00110340407011412940c075641510100d9110310071318144810901100c2c44000208062050286881d040d41d4004100c0d01800b02d10034007605c0360200da60b00544c0c0e1440c5040115418105e14a5407641e00c0c207005603103040c14421210180c48140800806000c1c2400080c0525503548940e01e14040c44400e000c6240b043c00c001c0301940c022405480c040340d0142c00140103905181c02c011a160f82040541c6082c0f031000e034004941244600c200b08800301000c0350160440c050a075200e40603400301d003422145450601e040c07a03448042030003040100310460340546454210b07562805a08e031b640401c040c2d80e07100c0c00c0c0034980040350050740c0100d08403100e4005590003a202041c010b51b25680303142200035541940c229280a0f042000812000e41c1c040001a00418140c00200b04c9410300b030003a50b4010446001d0a4042400c148540045d51030401c000042d0310743e542e82841c07071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 814499739 1250 814498489 814498499
    0xd050d18050624060301050a1e090f02070c050307380a0807110105150d06060b030403030204081c0e090604020c1516080912090a15021c050c06010320040204 69
    0x40c0c40048140000f01c000c2c045040c0c4142000000d581c165030011b801c0061144c248014544025201145002030f0300520074041034141c1180991003022140800140c2c460a080c58250581030b900d03008117000f54000c0d0410010344940c118448406030941400d0010039500b0241d26103c540f1a40c15a28040d8000075000020b07644840000d1040707403243d4403441c5da86c0320400c4190aa820503500c07c0b2801d5010305030a41d02e407034850000c0c40720030710901d0b0002d0880d03a5041e5585160f00b0444003a8007190740130900300424001031005200e04801c030201d08900c80c51120000e0b214854401110340107a200900040c4039807200d80c12507100c2c0440d40101c0703c440d801000f03080c0c0c17842403c0315440802c50741c040d100c0c44214003401440d80600c022401408803040300f518103201d550841e02c1d0060780700301c801c074001030043d40d801810254002180d0182c0500f00413201e00c80106c450178003460080140070001b203000d82001041440c19a0b9000c4480c105408444003801e00746020070404940c868030000d40025 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 814500989 1250 814499739 814499761
    0xe151f0b07061a0d030302030c12190e0f0304120f06050a091104061d0a1b09030c171f1508010b1212040303080619140906030d050d180506 61
    0x601c9610800050106683c144890b00380d5001c20b081c2190072503800164000024000e40195900610050790030b801d0004c040d401400c145000c0e607054a081001c40c05455900b1094003450301d03d412443c0040054240511486030380303208500c01c1c0100c2442c0310850800308107185a00004c0b84d078120409000909021903907000600c50b00c4022940a810162518564200360240c001201c14110391040c641e452000780a2540340014101e0302ca050b0350300710103100f079100355103189955210340d40c802c0d101c00e003180384c03030051002d10750171156800c94100b1f0b600120400010f020642140c190310310181c0c2c40ba04000030000303810202045001d09a03061030128111405500134a1130b0302d0100e584042e84140030106d40e1f1900c94642d40215543d07010001480440e019649054000c00090b02d95140c000c1c01d8845ea0002c0c10294100000348544401800d13114607005189540184048018045410f645079000d8054410200800003894545a100246e000801e41542d1100d0f0000d00fa18002d10b462441d0003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 814502239 1250 814500989 814500997
    0x20309010b0a0509060105040b0d0212010e150904020a050d0606081f06141809030c0a0b0708070206071d010905060c0303071805090711010b03010e0c010e03010e151f0b 74
    0x142c081e01110800054030b150168550b0b018041c180c440d64a45814208105030681c000daa03002901c54013006103c180019030022a170003400c24070302803074403401e18030b40c440b00740f150000e1202e1040e4413250500c00582d41d02ca0700101126011200940342145d607191020282c20036030300024160254103541c0c03507006030602135070b0f00701e81400c030003088895201c4800c901400003200046401c4201200d242c4103218104c05907582200040c401c072410f0540c800c030030314541044540101d401164090601005503007000041c0c1c1c0084060015095038074010380d0042c494000d007541da141402e8001030102d6940d0244111801502000d8240c0c2d64440030440341a55079402070328085c0008045002604051110f000c8110980d0002400010240c88013070044400a201c40c81d549055540c40040c14100c0d9824401c04c1c0381e1002800190079080c0744072002600d84400100c006010340d052802070707090050b02055130300140040e548800025203409102c40d04130b504400042c480ba400f820000b142c56030005002d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 814503489 1250 814502239 814502261
    0x30a0504030c0c06270806130c030f0c140603150603150607140601060207031502030a140f01030203060711060412020a0503030a020d0c17070c020f0312030105031204060212090d0602030901 83
    0x11505d90300030843c240c615020f8a1144100a820a1010075055034940c03d0a0310800c0c01010045419500c030340314541043c0e0100c030212910000d00301c0c00c000e80031986000c1079a51804440003419480c0800c5190400d4a90510084c41a14000001510fa49e103000d40c00005450240015856450038a08980c0c8481007000c500480e214010002035403030720006038802a80d9002c141ca40000c8400320140e00a5000507143d00645501c8800d41c403103035152451440d10400410f074480e042c40d45580145801c2c180c0203448203040080b0b0309403400600c4c4000a045402c84c0c0e018100303a41c0000da0080072418800d0500d4010552300000040c00705075605500a001c9260110308204141240c0d030009548048401c0500f4050b000084002618280a1448502c0b47d0707001910004e00c10780d500c40000d041c80a40480501e5021000c8010b0100c0c4c01e00700321132a0120f40641e441c501c2c090605a003c1d5540c2e2102901901aa00000e106010364656803900051550300a000355100e04022600314040d101020031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 814504739 1250 814503489 814503527
    0x90602060a0e014205130c0504170a020a060e1c0203030c030a0804031413180f0c0906081b040e070311070b01051906091203020f060c040612090206030a0504030c0c06 73
    0x10b03c16541c860002c40011100010006c2075042c10102e8040042d04081017020280801484000356045080880e49112140400500b82d81d50b220701c1045061003040c1c0164007040409000850143c4640120032050b068030007a0a81c1c00040c1e1001915610a002a80d031260101140b048201500007100034004c130310035213480344000c5c1c0b002c170b20304518050703031581c041c01d4000801d0400005c00060340080c0c01c5106004081245101c01c40e2410594846010b810009031580c041003041c10383c0020020b800154584202e075010040c0713100840035000718003e08030030f03c2184020403580b5001e039001d540d000c012130b0303200354490003607080c1145040000d2007a10300521b4080140540e100c40502040180c0b140b40d101c400083d400c00b4241c041032500448120194800c03e1030605606404001a612a0314445203181d526424844002d0112700b60b0781ca0f08010030700b00940880140d6880041d00d510045e1480001140d546900302111a0030349d001703000e0043d110f081d902141d21a848022041c8680405c1d031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 814505989 1250 814504739 814504841
    0x2703090f0801200901020c03070e07110102030907090513060501030804050f010c0b011707050604030b070e030d1b0303020d0905010b0111030a0813061508060403030c090602060a0e01 80
    0x10324a42603c07880843c01841e104204989040c2c1e0f20355034080c107440724040c0f0441d180080701402007480d04901e03411900700c0c0040c14041010a0f07038046050b00f00909800000e60450818001c1d40b41c0d204040d000e000d2a103a03c07400010002000322060000709500b0090501040d6507e007004020703503026024450286039858140300c002e5014420000c0c0b4541c0c81302441d40c2d168a0000c0d0019201c081c41c01542030b130f0144002c0060166103040140c00030310f003d40400341c150b080c0f801c00a410100400034142c0690090401c04114540004540c40c0c0803120031329545010003640b504070004c4c455400d030381201c42d10701003003a8140641503004100d41c2070282c941c3d0b828101d881d0102c55590040403080c9001035500400905010ba480340c0c4090703c94861200810140c4a134074018050754040d80004905520013400c200c02d043d0b05004c1c050f558000350408148090400100039203c0701d00806021a03075440d01000803103c242540191600201110a0117460a0049170640240d8081621450741148a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 814507239 1250 814505989 814505999
    0x7051207200904030c0b040804050301020c060a0c021212060d060903020d020c04110703030e03070b0f0411420307020109021306050609090a0b04090f0b101401032703090f 75
    0x40703021030169803d074131460f01015046d0f944c001c84040041045640e0107060200113403644003400a42000390101028040703d140640f040c0d000c480c4140031280842d88a20300010016444108403400b45103c0300b9100b03665616407001c03d1540342280002000b840ca800d01a105056000c07444c04040001542582c0212500030100015500e24080b000300c0202c04000a030f0000340258040084441010305490400c491903c0d684184142203038442440901603003040104a2182303089031005400312484505205070300e9050803d2031403031021000b0794003c00b04404c03280300544064607a54032074910281d603a02d442c1000070b01a160a9100f00d0192280d0070071500c5110071401803030141c0c0c8001d40740e542000000c5040140a00c0060700d84955a40e480d0340300320440e1958010704c14403a0084090582485207450481b60700b51000f001045800c11640003840600582c0700701c107800240918020a80c402a10140030000205010724482c1145859036a4100364101400c1c00440d21286902c1c14019030395 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 814508489 1250 814507239 814507249
    0x1206190f0927020604091e090f020102060f04081206030a020a090f0c05250201170411010e01020109030806240d051609210c0b0c0a022704080705120720 67
    0xb07000082d444002400148140c03071140d40000503040315409003c00c50500d03a84400f04603901007600b82c030f040e4401e910240a65804000040d040b441c0f26840b13a0485c0b41031f4444094034040c0b02003619003080b5000c0401c446a0301000b000000c00c0c0c0080c0707000341c11641e44040c4001000440c40c0908081e0800e5681a003c0d8003034400d075070341210070305018101c488090314401908486d02408906028042071907191103880070b458284254800c2c1031680480d40e01038000340c40d180c0801c400d641107a041128400c0069400300c001074003c44150ba03845c0d400e543c9000c1c04810402c0f0340c00e40e200031301400308003101c5904c0d035030b04614020303c0b402d240c40101c00080801240c4c034034218040c01c8100313440b12204050760035008007028402401109140c1006031501c4c0b0f1a00c1560240c40c00b004d43d0390107031444606529200300c4a0340f000452650050518040020380d0012010040010708041c00c007068803800d01c0b4090002000d522400b503040c5599050700c2c50300002030740c450200c000156501c0d0214521074101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 814509739 1250 814508489 814508561
    0x4020a11010227010509030a12050403241a030a030c0302120d050f0906100b0702010e090c0702121c1206050405100e0702030a050f09030a0c0b07171206190f09 70
    0x1038058408c510103a1070310b90141c10803010407000c11034104000404581480343c882d40c91443e40035424450003c40c0c0564058803410f040d0240640382004c90710140c1c0d6000203012507001d038181021080411241010b03414051850b14802480354000742080c030361080c0754445440703039079444080030294560302e9101d9541c0d10202e90b503c14001c82d825091006c6000e80d4040c4c80070920515202614060190101d85c0749141a5050510081c0c049482021031400e8103e5000b181c040e070008000c5807101011b41d031100c00380040c50001784195030761039841403c580e0300320802505000d8424082030400440d40340028015100d50b0b190308810b080440e824a20110481c0c8a09040d0360703903a4140303d2886100c501c560303c240e150a61500c1000300c2000000e0000e10307090020040c1c0a40302c0d846150a00340b009010840b0968030004560030058161082c11907180160031102c1600c065042e400e198803081c19006040d04502c2400342880303c00100c9407500e8208180a618a0b1102c28520365030804d0100c072600c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 814510989 1250 814509739 814509757
    0x19080705031c23071a0f0a1e020d0207050f031e0403050c01050c0f01050a231e27030307120b0d03030c03020d020304050717060705040504020a110102270105 69
    0x3948a8048110000070000c0e00c01501c0c62440c00c3d40b6140007551080317034003c0d0440b0240c11000d50141048442c0041048055002140782000c0c0034081e0041580000f000b10440308030b2410303501160080300604141d0546454643c80000c42c0c1d01c03552410350386652500035005609034a01448440b40001d14030100751412242c0c400b0040c0300781c89860b030042d5225004016040503c0c4940024a613038480f0034082c0a000781e900d041d000030364045c441d06036008640c055041c090180c51481c1441403c01c0300150701074203150a03a000d5013240d00c0e400f401d11344c4940003400460402c9084c0760041c0d152900070004500520498075103445081c8d0070304042c0150751052010580c4128001002c0012038040e401103890f40078140380051812401140681c100d802c1502c041d03850b5445690180107202c4140e91628886464030014541d501e007070040185103102d98056540115004500d220034240a60240207281c442c0c0d800954442280400c064405940e56050070079100c2240c907910920b5000300100c4000003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 814512239 1250 814510989 814510997
    0x60f0c04080d03020715050a1406100503220503032409011401032403080702041d06010902160206040e040c090c0507021207030812311119080705031c 66
    0x4800300243c00a40142d01c061743d10944103994811015194410184110702e4803200180781e41b8103485100640030010b00b0180583d01c0d0200003009a50404250fa500c40b08900c901350300b907144480b08902c00090501e0080c03a500c0701000b40300c0e0702d00f40c01295242d019482c11440b280710b4424410055660820f1045800100003194516902d51203504042e140c6c84001a0b5003542c1c040c140100300c1c440c0c095500c2a900380c0b0000c120304c401c5260034000d5104200e100c545404400d1031035640591940818410b01e14610790000f05490341c0040141d03900035458004200d01d4440356a42c20611102104442c200c1c3c10407540400451101245e11807844050300d107a5626043c450150b00b84510041180826a40780c8105800000003400c03640c0148909208803440c03410b00e06101508080c844180c5200d0b60480000091416440d05074107021070200750003881c81c0f9201802580480c085152a0716070307007000c9605032404100c0c0e0b807001070004116401541211410a4081d42c41d2507000e079041c180200107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 814513489 1250 814512239 814512253
    0x7080a09060f02070e240a120203060f060102071503060f15030e010c08150a1701020c1902010804020d111905012303011e120b0a06054608060f0c0408 66
    0x842c6d580603064511541449005001034184000030300e0000f0281d00404030464a03842a1086003000e020f03942e00400c1a03081d20466040c600c002035240e0740140544408425100340c03444005200750403c030005c00e14141d036820040e845241003400d94911815040100e030801d80c0d0040035040501c2207000700c2520713a03124046500c4161840b003024140a070382c9540444d06080102d4102c2804e1312042d200705d44000010380c2d850f4505691400c26690390080c11040c0d0310300c42941e000d44d030405c0c2c01a07409541201d1103840403000c0d281c0036298441031100303146c0100102d04030806607034440409805942d401d80f100814440291200c000b00e440d64041503642c99000d000411089a202c6540484041000e0903051120b4980100004228440344262840d0f010381c414802807510601c9403c1c082e10301607030200c12520000d60303200719178000b503072501580d002c4005069510404440c0b010050740c0c591600d041000340da610f0601e68071070007650841208200b80300412008120b0608403411030740c41d0b41c042c20340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 814514739 1250 814513489 814513501
    0x807120b0102010e070e181906090311060f071805010c06090303060b0a030506090a020309030316110f0a060b0a1a030606040b0408010c0f03150e060607080a09060f02070e 75
    0x94104691003906540d241c00c481c0c59079240510400002d0151811030950900d0409180c5000c011600008002d6820800340d1500e281843c642c040441074001d500031031556030078a0b045805140d0041005080d010305801d008208580801c1c081c00b80015a072032400c10301c403480d60b5074000030340340c496140416030320495040010f09507000401e4081c080c0c00c00041c0f695441c0d03003448603607011031a0040000e607074208202c442c9c43c00059403a004245184114250f10300300218956a10010304076802191481c801507d1244c8211066180c40060304243e4a52a0b0100d1540c0d40e5003005042c00c5803a20300749090b1030454104000c41c8012141c0b40751400c03050420b104040241ca0740040c0c80da5400940c200004107034848584014401000d03850000216a826604010300000750000014205800e220f09030448030b1260800340c0c2075800c01c001307282070340c1c90311000203071340d0320072003070020310142020551092541d00300705948204d42961316080d000b0a44450100c0c0c5881483c011401414000004611 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 814515989 1250 814514739 814514741
    0x319030c0c140f01060e01030c080610090218030d0c0605370e1f0b1e100e090705070b090601150509030a051614010302130303031808040306060302010f080712 70
    0x600100c401c2d141c3d000080740c00703a400d4600c943c10000da03460000004100300482607602400400a000c0a0940c50805035106142e0203000c0c812419000d40200c0c404442c480707450580307022010014200e0388040306080300038051514801040d91118070f0000010071254829444004c0900c4a40b80650512001c06041000703001020025291a5980d4800042c0801c04c00070480c04074840b582010703075070701207450000039030310300c14105400786130362034000c0340038100c86a80240c03890021164031414900d00401100d0701c0328201c40c0258800040002c2c0b105041c9c214004117800c81c05680c05a20315030343d094905603208404e102d00714560310a0380e81042c64500c6000a04101d04c0d006060751036464264861034a000310a0106282500d0740082c2080840e00107280600341c1030b021708042d400c260b1800c8110881603102e10028082c1904d0b10354215030070b0041441c840320f0310b030f000540d580c8440e103a0805100905c1c3c107002c201e010400f4215004495401034040511400150b07540d1304110340c420b229a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 814517239 1250 814515989 814516013
    0x52805060a020f0708071517010536040b010e0712050a06120b010609080109110d02010c021f020c010509091315020f0315040b0105040e0c0f03090319030c0c 69
    0x7200714010500b5002150905200034070042c440c1380d008080741d034201480ca42c14104401240418041c0d081d44800100c540c400c0c1a40c11100103d031000e508400300c103000026900c014030318549800d881800c90031102c010f00203c5001d40d00800d000211682c13500d200b0303134412905481e6000407032280001d802c8001d0a607042107503c0f286003800480c1541e51603445001c50345507110102d03403c15040300140601948508120018182c00e0001c2c48411015140c44000614840d5100c1c080c1d0030002d050020759001d013145400061f800f80000d413001c00306100704001c03070801040d5240140034000c0403860a6108500f40c1701354071401050500c0c5510b4104a018032000c0f095001c0718004008001c0e004585014409001c0500d16400050f1783c0745000754100403888880c40b001d91040785400700609840e6409000d99007520b1000345080c0c8140c80d10b6191803040d005411021000301000401c20442c2d050100142595000c0c1b80c004d0038459080d40300607800c1c1d500303040c81c80c00024234950301800456003810000f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 814518489 1250 814517239 814517257
    0x9060a0314010207080721020c1011121902010c0f09050603090a0b100501091a120903070606090605030c0d0b07030b0105091e090a09050d0e031c020705280506 70
    0x14030b0b00c0138175514440d141c4c01900c42983c941040d46c803411032012000a403103072551600d1001d030030700003030501c0050301c90f41c6100190400c004010121410081d41005011010072107600899181c414050582d01d003060324404c5000194240111089940d016500d4600c1c44052601d840e000eaa06060902c030042c0c1001300400132620554804001180541e0426805140001010380380d45051800240a030708943e403041030350400702010a003080003010283c1d0307502c4000c515440702685680721001c2c81d5008074a000b0b0605860710000040c00f55440c0e0060741115005e034103444603002c11004100c1000b00c140c1c409001e000466002413441c0f80700303a00516081d9014100340d42080442000300700c0701c5c2d0200a4800e41d00d1000f00c2c0080d0310740340c580e0b40395500902858003440a02c13483c1e9109a02c400304001b64506000c950980c070b01a41c0d0b000c2c8030144415000303401744581c09244100095070b580d882c2c410103004900d03d2170185290020b086401e241c505807a10499016450704040c0807195101840c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 814519739 1250 814518489 814518491
    0x4141c0b040b06043204050a0b090d0e010e03100e1f02030411030d09060f050904020d0506090105030c06090f01140310180c1704020604151d09060a031401 68
    0x12180016045090340c0e004500581400040e85071540c01d01040301c4403078000342008401d0181c00d9880c52281e03205804411001922056140c5441c40c1561424044240090201e07602c8400c100d1034400000c0e60305005656556842540c040c0c00c4019a10301072a0083d4603010b03006820314507000802504024407096201040f02d04105a450319882d0301d2000307042c0741c20324640010500c01401a0480c0140e00403030118080c0042c00903400c005411241d162090701c042c0452166900e502c0d6002e50203071048400090004c1d945c60103c6d55a040052000b21030442c450201c440000c1024180019100440b40028201c1860454214108611160510b0f119810007072900211018980c02c0c40c05507001d014440682032186060490080300107041c6400c014074646044281c002440d0320201c2c201c1440105084a0b134191170307900204a4622031900425850060019101002540f05d010902085a604081c01003c40c041d0708000e4500c0d0b090f00c0b05a4007145000060021444442002264440300c80c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 814520989 1250 814519739 814519789
    0x90303040f110d050c0907030605090a0509030409050a0c0f020c06042d0b030406060902030f0a091a01080c1c03090501080901090b07030902040e010506011d01120504050d0909020414 80
    0x1800095140f07404960541000e14800b0304c40c1040c403910b40c0c000c00c4904041c800d00c2d0902d0049160728000030040c0e040c1648072808100d0140c0103004441c050008140140014a000c4021401801d80c1c0070071100050340f21780410f50a140701040b880703200b440081c0458541031a19980a14075200d1001c019000d10000400da6541180e01071440d00412822412540702d1605061480840b8003a52140c0260707401002082540020480300c554004030000d8009848040d80c241030422450240d646209548424000304c0c24000010305603c0d100ba00316903072030000701514207004450500071001408034610050030300031903000d00f54070b03a071003400c070000020b21a0494580e4200140c060ba0343c6800b0907911102c00c1d055080600a54154402d500c0080c011410a00d00017041c40110310702042113084202000460350380700c1c031107000e80f41b11401c0c010300079424103080c816100c0300d14051b88808182001c20025000d1128000d503000c88480b94410343d01c800d4980306020220250884540e80003071100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 814522239 1250 814520989 814521023
    0x190605221205060702060a0510030314120103150f180b0441160b031f0b0c010b092406210a0e07080604060b03030405130207050c0405090303040f 64
    0x124040300302e0055008022a040c6000040d04101c400341400398814100070401070214080781c00e0398200d030ba041c5890406505110800c18460040c054528003003960440004180b000b4043c02101146010070308000074008034141c4070441c1c600a000218980601c1a042c01041007009015032080c01000c43e64a82000d8106644c2b4000d940c050401e1185c040f8020541700f102c0c505035500302d131a55800107090b1510b884203141c1c2140000e22400c600c1e442c4c008000346070000b000c22145010000d091304400030359280e840500c900d80140008000540c81c02e8112003480c0f508180b09409035084611000782c00440036841c0820544d9500c62641005041208049028450800715160004c481079800c0d5030500080c0707203082d02e407070a14003560350b805000180701e10003010135115045a4031050000d0401003038404281107010796400749074411142591803084030f0144d0000d145940c03280c020360300d50180c82020402101d0f015a28100260b1090002600047c0700c0d01601c00150301030025010300300e802d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 814523489 1250 814522239 814522259
    0xc140a050907022503031e0324180203040819051b0604120207080c1306170d03050901020304110d140607090905010e16120f0f0b19060522 61
    0x94495000581c06280d110013054100005002c090010102559826180d900c0003070002c5031800340281a8083c0307580c5595943e0003503201d00081c0010b2480d20b43e5088c09004da08034401c106100d2244c4d80c41480352080d448400034803c491241d42e004840c18203100d080512544200b101e403884c081805420404081d8a400801100c08041c40712030050a50746450302e0842202e0140855000c02c0d54040741b030600030640b01051040c1c1025041e0ba6074a001100c40381034001616642d407103108080585103180c4203201000c80e5110380000642c8040c0710549030918018200e20007100c020348005110b4500300c00074900000c090107d940201d4071000000c00203140340341811410b480180218201c500304201c8000341d40205801009890021201c61510350341e81c0340c10451400c0310b5000c0242c00080490101c5590340311038146161440104000f122007142403004044c0560b0140c41423030000028191501402c42d80001e680e4135030344885c01c05100204018040000080e140036855925001156000c60 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 814524739 1250 814523489 814523491
    0x917070c09090c080f16120c030b0c1b160b0306121005060f1f0e06071e150b030a02132a1b0812180f0d03050703090c140a0509 56
    0x151403103c0c00700d840e180c800c0d0f107800c40c50081e185060700000b8854a004840400301812140030541e0310004c0744207480e1044941c81581c0004040c1901d14081c00468040c02c0f010f05039003440759540c0c0d01c05181c0e0742e608076541c5050000c14a80360b0701c0e8800c02c0c00002c40e448003850300080c0c040c000c080b0078001c010160b4184403440002450040d41c031010441309240028442c42040030076602111080e03000c58410b120780244081203024020000722603940c0e82c45450462b80c9080d00507681c0342007441c8080600d50110182182500c009076030040800304004a0701c59449690b034002c00428200d002a42484000e441541084900641d50340070208034045500c84840300c07004002010102007900e46000d0700c02d0750036013041d403042045405101c00250180c01114a5002c0b40c4d082054103a880b51201a1407441d0440c40d00d840b401250b4641304840c6000541980ba020f0079103080c015981e501c081141200c0700304102030151080018200701c039003511440354000345005010828407030f2310f03071001c9514240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 814525989 1250 814524739 814524743
    0x60c0d051c02070f02130204081b0f0a0e07020d170a0c030e0118060608060402010f0305090c0a03030c0b0123060c01140717060405040f081b070f03060e010917070c0909 74
    0x8110f0301300000c40c58880032440b25003107201004c5080900300b484490340c030a481e8100c60910b02815040040c1e42d500c0c4925801c0381c00b8000d101c00c000340d85031007101c1c00c003040940711070004d8440c1c4000c5d000d000d4012408000c5521540a1302d0080b0381c1e4980e0400080d0244180c40c1d003c0c1a0745120003109850203001758069038442400168000c0c85500e080000c4400540c8222031710f0304007109000042c0e038400c8001e4405040c52801040c9500c5000e40ca50038111052081c0780d200c545140c0000c205034100d01c5611103e400b45845980d1a0390755024240b40c084808000300c80c02140c03c0621f8131502e007060182c04100a40000002d036030b203010f14819081c00c3d042d039171000403070a19111444403160100c88070b640000300313640a004500b0a07545d0508403003561103004000190115894031000c007018411000e480c400c2e002c40e03802d03642e906040c00c40c22035140030540c2d25608002d005d2041c0801401512000c0754002c8110268082c03145150356660000441144c0d001c00c2c280000030b2004c2140a800d9003a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 814527239 1250 814525989 814526003
    0xc02010209012604170d020703030603050f0c010e1009090c0c021e01020a02060f0904060b0315150a030c051216112a010c0b09030c0c060c0d051c0207 66
    0x759030800140c1442402d92607404810004443d00e40303214001c05540b0f8102d036100c2030402e030054007251401d25901036818084031051000c40c000d0305140c2e05400040071240141c06440c4411180ca01c0380b40c03903004051843c0e02003030070040d103149981052103c0f402c080c0d40740d145c080301c481d80b07a43c485415618101d20160000d130034503c1e101d0951406030000d031207400e860900c84414009a600107510344442c01e001901c04c100210b41c4100d5158900e00725008048014800c024440d150b00305a00d0300c2e002035405072080440000329095604024104000803003c80410505200d8048000c502400c505014002000b4040c00144c0c981c0e1001290702e03004215154049002c00d60000c1d00819189261420b011540d00042071090905122852004c01c040d0388600300803a8640b02e0010390b0300d441c1c0300720028000030110003040100a404005000382c3d54840066a15460710f103010010039005d000082c9410740c1003800d0000c20703240140e0092000358200d9030100b09419410200804a811140c81940d0b40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 814528489 1250 814527239 814527247
    0x806040c06090e0c090a09050a060e1b030f040204061203020a0303053312120301050f0109030206030a05071e0302031509010b070204020711042c0a210903060c020102 73
    0x1001500c98440601402d1920b40001843d20109290621001e0645600c2d1003001034103078001d0700c4011040c006000104030512080c28080342e5900200706501c1007071818603007403020aa591000126000024080040050071034885007400701e958030000e4000c03640310365109070004280d10060420a03089019402801107100103040150030b40e07400408041d4101500c102221850f0110034060b038501d5200d0701c6041342d80300c8043c042080401d00d40c103110715030b10415187c00c002121000055059070416144034088120100055030400ba5a0100070360041d02071001076040c544d55484140c0c85004c0e4070b0108207012892810040810a29000380c000035000010000d03400040c601c2001e140301c007901c0e0701c00300e5031404502c1c105500074884000c1c42240c0020f00c08040c844440040c3c03001004c004d00400490701c180c2280c6500c00c2601e0441c1c02c0600034038070100310320170020071040c607220781141d44103d4035580c1048102c0662043e83e2030030188840e1110100200b00d103440360821501254000580d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 814529739 1250 814528489 814528493
    0x2060a05070302120c0a030e0102181e010c081602100804030e0f060901030207030201020405061b070603020313020405190f050603070b070f14190507033f1206080604 73
    0x40d500020001c078141401040f0300e03489820301204881e4000506001c1944602c2490401c9019280c5403c002a945d030020a80850b00c03a40310920314511300040710941c40c6912007802980182c6464081c040c04280401c1220011801c0300d0000c1c07004c2051361200811134501035000940b02c0c1e400d80000000504100c1c01c01c020145c22407020300e5109400c0b188202c40c1c0000707000003125031103201700e101c2c1015008158582094001d4041d04c000d00801403c20b030305c4500c604140107800c4520b5011484034480e01c0000501c1c04d02a1013100d014510301340e0041f034400810b80a0102400c0041c0070b074201011140d00c48094441076221780480702c0000000030849080070b008251600050f60400a07100f50308202c41000541807018000c505a8072070318041113121800f180504094107050b001c3c100e00010080041000300128604094a12850068070003628100d43d4050581c00c04010500c02e440d4460003480d81404000c01d584004050320306102e0b4200781c0c50700034081d120103901c0b0780c0d00c40d4065424030003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 814530989 1250 814529739 814529741
    0x5030706150b03090a0206091206090a170c0601150c081308120c100504050106151e0e13051b0c06061f20120c060708010f05060d11071202060a 63
    0x2001c8a042443c11410050903c81d00e9075200e030b2009115000000d120007a41d01c880042d0070000b00d140b010740d81c00d403603c823540c10703240d01c00e9a2040381ca201c4403d5510207480510030941b005205202c0080c0365907800c0800780507480c204424042c00f441294104080003511400c000c000034051040144c002918000d10980303803602c0111178054002d420f024940411341c0015a4844090031002c0c08074440d162402c3c5a030041c00315410107203060950031400700724550800c1084c8041c1e0b00c0b4a40d1101c0c2000d4000c421035900146a1301c607540110360511401080500d03400042d000701e100d0b413215601642d10135400110b54070140080c0281c0c1c204904006c200d10303211003c043c1440c4059009240503848a07802001c48030310358103000f1180d0b0300c58199002c00808201034030030301c10310200380d41c0d9480d40c403a106a070383e5008460b0440040c1e01000003041d40c2c941d4041e980122600580303860700b00b040074075004010300b001100001e1a10003d000e1003000c41c4044402074054082c2d6005070400e820808480700c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 814532239 1250 814530989 814531031
    0x16230c1e060c0a1d100c0302150403050a0c031e0f1101090c050603090304050904083007050a02010e100203090d1704110f281208030105100c05030706 66
    0x8011500312104001c050060b031000c8407030565440c503140380305607401e0300c540c5510a1459140d54003c001006005140c83d00102020020ba000703800b15550a00c46004506410004070f60040c00200d00703025100205004400200c0c1c81c3e413081c01e00040940481c6a40012410072054120008030403402da0440300342c005002030350790140c250084c42a0030043c1c0300c101d50500e0381c2c41218065040040000e0104600b0f10668001d84802005d01c80e240c1010f041091442d04040d0313031042d207440c07484481c80959002000441c9070401070100780c04640e440100a9440c2d4100d400c0c00010355483e00742008100e50203001d445a1820203c100503240e0030880405443d18100c04541d805010700030074100c51194190070420f901981c00105186002400340105251450119420781c000b602c0d0b082800c6d1904480080c0c202e80948010094019a541c2616025aa0400b900078154030000c000521150400c0c010302c07041c001650400c0548902e803a5a9645140e0188200f40d41aa5441024025000c0c00b54007034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 814533489 1250 814532239 814532293
    0x1020f01320f01120305040b030a0603020f120a0623010902040620120304020a120501060306110f03040f0807080304060e0106050a05031b041b03020309120316230c 72
    0xc00103803801e010002c00e1940c0600a02c41d01400c4000c0d180200b5125808413030203810360811060301c03810280002000340085010803032185840c48108540390409400c03864030308008030014940d48016444510040004030021500c220b8940010842d9084462038507009003009107005940b01c0c03504d007006181010810910498003030b44c10358203445030710000e0030041b680d0609295940c1c0c3d807118800120028000e90094030001d1a04501c4820b000048d800384080360b00800c42030154101e940445d091a125004100d10300030720610104d408108000f00000c045441071126504e8540306459001c103d41041707030115541c0ba03d40840d529484400c1c000d00005107000d03104092003604181c0001e444c0c0305502d0071078690007010703490100e0503625500041884d03841c2407034120161803c0800180654001c40e00c80506d0302c9002082250203e0348412688111400c03001c200806116241c116140c00e02c2e01d800d009440342c10707200030000c0e11030a00204007181c9400010b016043c0c48107940e8400c01004008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 814534739 1250 814533489 814533581
    0x4050601030e06010611150a020c060705031012050c09130c0b0a0503041209090c03020d18050c3f0d020d05090409030c0804090506120601050d030e01020f01 69
    0x11004115000840314191039041c1006c3c1c5072400d01d5260146020701140b0300420f0030401a042c8010400d159004100b90301501c01910500d6507850419a00340c4002e544041d40800c0650040288203010305100424900c6803060364101001c5100103881e600050319007400c065045001c1d0b60400400c0e0400800904030040ea80d828601d4100c00a807080c0001000038100510f900b00440c103591040c2e584c0703405080304031020000070a003090010004e4100c4818290b000307107880e00700e14018500f92006105d1a61000c024607041c204501804440c104201c21a200150000300c02c2020070240c031003001d001c00004840d0540c00034012401441d1019401640c0e09641080b00f18040d195800021070385044000c0d5000f041c04100c0c3d02d411242c4501401d00540400b50100c0c0100303062050b03401030b50255508813000d80052911900580e1103c42c00c3c801c2550040e4881c1c03402002a0181c000d190001d00c050064864100750250700c2825140712042d000000b13500c250802d0365502e40c1c1c0c00648100d0000080c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 814535989 1250 814534739 814534751
    0x60e06010f0312110f0a150f050402240f04031a0c0c0d03150801050c0a081b0313020d0b0406050103030f020318060c01091208010f05011b060f020d020a0e0405060103 73
    0x140d080503d00c030519000300b000070340c81c1c20307443d040801c221400840c0c0200e411200c01c90202d0804071800c0e2000396009609604203003038614489044d0040a0041d84c0040c20071207481000f07600c02c04c82c16401c4442010342e6005102031180108020040d01c02140203030740415040164512040b0240c0c80101120401e11041c042400d1320030380014803ca50100c0d0b030a00150786403081c42d01c00c00c40b02160b4800421982820704000720b640007600540500242502c0c1c0c4462515006500c000070b00803d4001405140d007440040c45102c044215a28424000f8042c0e200e68001e948585551071400c4074192181e0341c88500400c10140c0c00f4075060407609040c8065420001d900c1d0240c03c0e142c5020008a100313003c0810703030811000080d440466a81d074000003808644031540c501a091800900c120400c40041d528009560350040680d40403c0185241d40c101c802002c0d5107400083c0380150b201400d06500344061408120b00d440102000d1445483d189140c60350041040140c035001000c450415060031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 814537239 1250 814535989 814535993
    0x7030215040b0712050409110c07050603060d06050705070602070b2a04060503040809040e0f0f07180e0109050f0a0c1a1e09090708011707050f060c01020d09060e06010f03 75
    0x75203103090782c4081420116a18070401710303094015900105501440c00c0405030328400110000d00e2284104401d50741ca0641e24420008640021560f2a402003400b0005500180d007a9001d5a4003203001e0511905114481d04c80e01e023280c01120080360900360b9141030050000404050040840c0c0d450408032610031034018030525401184034050a02201001250800502d5805c4d10321902c07000d001005101e40015201d40d0300c01c88080089820b028901640b10020f0340411000b054644849655000c0034034400b01ca030042c00b40100a0203995605c000250000d94184200388501001034000c1038144902d052a1040c03807119400306890010703440010034030440c03000a0740c240b1200f000c000c030420301d2000101c0210344104612103500c6001e09080103601908600c81e1810b0b18400456500101078032948141e4800840c050941d0081c0098030702c0000d8580300005003001d000c01000941040032280b007804c00c1d214600003c0710740c03d0311081c4629088800300801c900400c41c1003c44044a0f2460b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 814538489 1250 814537239 814537259
    0x3070e090105010e01120f0515100305070923040f0c0f05121515030702060a0c020102070b0c0d021b010c142d0f0714010510030b0c070c0b0c0703021504 67
    0x1c0c2c01300d040c0110b10040007408000c0da4000c10161030030072400d00540c80c040d9000700b0708941258440780304019250384245020f20910400d88a407002c3d8444040d20780c105041200103c2000d9258101489031540c0d205c5641c80398002e1500c903c240c10340c04500303500340040140034000415040410010184000d2240b40c00c0030035500d0300a045003505190401498011446128100c2d000041d062400020705c2141a8001a00d51003400d80e00d408001041c44d148040b8283d1147e00d01c064140f100000c04181404200002840e140c14052001450881c2d111100792400c6840c898074550b5035036490800400980040303141114500341034041703203416142c014121900e480d02c50960089556a00101c40f9000b885048034210072000001540b120143d01e0550756845c3d07440b00000c100d50a01e070105038000d42c41e003d40c03070540390302c441c9050321546c41d11402c0440d5003040c41c054800d104024400030304010302800400d803200c0c105c8040c100d02c1c0c1c154010b001284421000b0030b003841d40100030421580ca00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 814539739 1250 814538489 814538507
    0x9060e0303120a0615050304060c170a05060622050f04062102010e131508060702070302012106060809060f062215091e0e0d1218030503070e09010501 66
    0x80701106207200d0f200e07055000001c0200713030052880c1907542181c0e40c0e200c0b6001310255124910030001880710310b5440c1300031580c2004000170441e02c18010404514124425004a94480c401401c01d030304000c0d0050429410101d86443c44101c4000c80c0028009030170a0031003007080c9032003640c01744022850f001001071896080201c0703040c2143d0001d031110440e823241e04040c4072003c004021806480308880004010074680c00c0040001003640c81c00a02c0800201d507003403003510590080d002d11407a540042d14881860040900e02411903041116003071001e10400c40a0003080d0b8071480245004e829040c941032001d810070b00ca80c0d50352010815681e86e48003403400c0718203008401748400403d412000c001b5018582c0d000c140395180302000704400032244d001582405445c201040326401140c41c3c03108441140000c1c0d002a00000c0440070391a001c1c00e13203000e074400c8272074001500e42044551a0300c0302440034001c0303001403000030600c498140e00c000000c07100c800c101e0b00c0d0780c402c0d450100041c1000031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 814540989 1250 814539739 814539757
    0x806090303041707020402030a1b0c1e03030e120703080705040f050d0302100e030d1808160515010605181f030509071701061d130b060f031c09060e0303 67
    0x28000e05541150700d850f0035910b40990140c02551241010000342d0081c0c008440d1040790180400c1d28013900d144102240f144064120407520481001441c4d444d01100348601e094007415120f00d200080400108400016218000140b0343c5458107071800038140d0101419010802c08280814005e940c4501143c40840e48111446880c0d21464035041c3c0c20052104c401e000d0f003030701e44941d4040500c0044028000c24121000030014440031151001c000202d00c4406009481c05000340441400369902e540b05290040044901c43d9910070142d4400100980bc6000060004286d0340019510b060145100610456044100c4001501d030502c11042c84a003240c101512000031405910b414400c3c0d00191141c8489140c0b007000f004101c60207400203202d1441450980c544901059580341880c501400110105480c000300300d4503102d000c000040d00c03495001081542080080e5010000000d020106200410030700416101c007800e84070195000300d090102c1c00181441d140d030003104a0b800c5130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 814542239 1250 814540989 814541003
    0x1406011e0f0905191a3102030714040b071a0609060f0418030203040e011409070e0114070f060c14072306010b1345061e080609030304 59
    0x243d40e44109041c0c5110b132030a5440802e141c440700c024840032070603288240342400d4410581c2408103800002e441201050002c2c0032013082082002c0084880d00155009055481c15a8400ca034601003034405a10683c080000600d000800200b04059020180303481e00c4c00c40300c01ca400d40b4000c40410390070710004100303500c02d5181401c041c00c40c5d0795592000c880401a0700d01041941c8941c0b0340039680740d000d4060311411090840000581c10614610401036440c080e18107840c5032210441501c80450300d10b100ba0520011034400394854440340040c0010038080c0201640c0100700e070402c40704070743e201d081890410070314003084400740000b601140e002170f5010b047da90442c0140c200700e040725214804603480758018040005400d40840010340580c1800c3e017002c15140d03550301540c8800303a10742080e14182c10021b1038101540c4007014902e2205042d04000002040b034105031003822292180c0000e00c08000c20035259540c400c8458420000e0081d5000404075820714424580d52408000c0c0000c0c164 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 814543489 1250 814542239 814542241
    0xb06070213060905070908060604180308040305210a151412030c01090302060906010e01060c0b070e131d1906090c170a03030c0e010917010204031406011e0f0905 71
    0x41c9980c4118010b22800030108054104808003c02d40c11280c07040c0c034100d12039800480c00c40d1805100d402c1c3d0444400703221206642c001d607400d407102c107001401a4140002807000d001804500003120404500381071003003801d450308495803001c48070140340c240030380042c0d00c82c1844242240d6050400151044032803004800e20240348078a0752007803e20410103542031848080c100742e00042c0c4180501c10b51001d4600c10780c4c036601603140f80b040074490100021001c0070380030082490403090a420020500d0718503841801000801c80822008200030390342d686e240007000c1c070074040690f149040115903000d03100f203442010110960203511100076004503541c11142c010884015000001021008020720000c00100703560307a110045400c040d400f2a00307208861607070741d20618901038010700503110300c18181d04000051980c0070b4442d2001c83d15660030000030003c034281302c4e1401070085552000b4052503042c09084a10440100741e1038200c20201241485060b0200d4602001d640a4540c00181 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 814544739 1250 814543489 814543519
    0x607051305030a20120c0906120f100f0c091a090a060c0b0105090601080f0907170a050c03030c07120510061d091606142a010e010b060702 61
    0x14819039074001a49845088040f00030011441c90604c40302d040d03d0304014920440f1000d01040003150000f09550ba00b00c0c620310b640503d001e84500f41c0194014003203070313003515249803058034010001c01c648110341d1020980e0000d00b14a0301410840303002621040c000820f00d0301015106500342e02171b03400e03510008002c07061900303800744c103454500000504030441296501c6c2e024080a80482c400e403501c5400b94000300c0d0500340b20451a0140f20180d44000030b95580400322012a100130300007010390b008125002540002c1c0124030a03008e59541d0103002200c001c1d2406529040c01c2e441800e0007600248024400d43c1d0000c81c91208403a03c1510316a003411141c60400d007001d10350014050350515002001c03c103006802070004030352003600405407071600c90030b070030542c2d5407800f112080c0100c10b00c500a1024a10984d56a106140c201ca542428148102100085514500e00329120760f10010301d01c100f801000d003d1600c0c6a0350442c003c01c070040b0b504003c500749120300704000e802884002c0300003503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 814545989 1250 814544739 814544767
    0x270a0308090a170301080d0e0901090f060b0a030e0c040e0601050d0303020d02040906030506060a051f0e040905030c060c040501050316021f1e0e0307020d03110d020115120302060705 80
    0x80c2007580403e28444100103000034040541084c011840581300380310a10303201500071000840c12060050084c80c9503031920740d0500140030024543d594150b10b4040c001501eaa151300034295002c1c0d1178601003880e0f5442d03040940340281070041c1c1885541020ba504440d41004a00c10303040d1081600d1514002015042c00c1d0080e01c24440d42100292000500241400340d80d405142030b24820307804c0e80d06a0704e60b6420404100d20354003034181d01504d40c01c002d4140d1001444118900506820501c80b400c0e5410000ba0848071541029601a0000510404521800e200d0701d45d10014182c0824209424100020000d00004181c015002024011f50f44070074002c000c501900b10138464000e078082c2c8a03041c4000a0070000c3c154540b8200045107001455566020b0070042821140081d03003000310381d07001c0114ac20244d52050303003408641d0030601c18001003400b1003164083d20703800105500c00c04e4100c09404040950246030482000c1d10b011000039800700e044c80d0803010500c1d290b500d4080c0544100307 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 814547239 1250 814545989 814546003
    0x260a05100e010f030c0b0c0d0509010e04110c01050106020a03020a060b0f10030c0e06270f0a08010207030206150108060103110d090309080705010f080103030c110d0b270a030809 78
    0x100048541c0c0000044103000412404252441500038901d485e0faa42041c0c085406600510001c03900700c1001c088129100340003070000442c0c14500000048000d40201707046500e69440e5011000e0b001410440c0a0303424050140104040d10007003500388900c3c1c03002901c500e000c94006041c00c1d10317550201c005a03518140484034000050580c11f0005000f07001a0052010014000202e901c064603900d1a1501000345c403001d0920409000396000f0080d004481d0380c400c4826168003440c0504000c41c7c503252209004042c3c80c0a500041e51a42c0c9420040e2403c03000800314081e440c281d171321400346ea991040446411000030b00740071440d0f8540c070707014060500130307240306105452034000c0503801e050f80080044100e54114080d14815503c6000458091011912010203e0100401000028821071201480e2802504881c0c504000e6000007150050b60729400d1310400c1002d07040c040b0410107001d030389051076074003001003035001c11000031580c40c0c440204c40076040c40f11420005900d0700d02480fa0f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 814548489 1250 814547239 814547249
    0x1120c03150207021201110406050309210703140301030215070203010b0301050c090f0d0c061b02060f0301030b0a0614120c0d03020d0210091e08120a0606260a0510 72
    0x440d40724410088038009400824050b40700320b982c44140c9140e111306110f06442074000e07220007444c1c1424001d00390b51950019000302c0c614811528000250f000321940044050100e803580c964030f0000b801c00034001804086042c0c41c00100700700410050350342502e05000780d504100400c1d25802203000090052000c01c1d0ba06805500340b204105542050340c0082c14114002c0381c0e1511900a034105018083c203582c1c03c002c00040544806020440c01444900d5240e88144400b0360071440581c0440d2181e0007203c1d80b5000500c0100040c410003202a0171f4660103500c4101c1000b130740d0315146080350b2803010b21043c103000e6404001e01010400090140d01c0d032035000a00307000020560740c54025a615030721203641c001405100085803151006002d00070b40075800030f0b144943c0c11007022650034504242c000880f00c0b0042000f25002a10000c00c2080c030480603040d002980c0c901d0800c004d44415504143d07106a0b6a086500080940d1012052500810000b400085941c0e84c0c034041c806080c0c00340c00c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 814549739 1250 814548489 814548503
    0xf0201050702040c030b040c0518010e0d1704090501090c021b0105071a0103020109050306090307110109150e0307051210110c0a080d110313020d052e1a0901120c03 72
    0x90070805a090341100c01101d0061f00c0070020001c0220701101d840c0182c41941400101c0100120b0309588a60a03503001c0070f1005010540c141c441d5a60800c107040249a40c0000c01408103040210008034801c0d0381c01071494075801e02030048017900003503d540c0300841718524980241c99284035a41b04200b501c9026500a004200940e81c40b0f01c405588042440124002400091b0100b000c1c140419000d01484900703009505103e82075642210f40c604580c4e60b036041104413070380003441e262480750141c20007a82d80c4440200100600506060078142d81140b0b0240700d18807000c80c0b1000c80092039551300700401c040041c802001301c00340091845004403040d0309200c0c00740d401051204000c0106040c0305096002c002130f050740f94407264580803c4607034800711200d00c0d1160300541072003550006168030031000c0d00c000480e914039420441080200d0700700449107900c803407040103203d0f119011081c000c00482d00100307001c420006003043c82c14003d1074610300141c2c00300704c02c100030742e05030001031503000700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 814550989 1250 814549739 814549751
    0x604060806061011030406021f021e030c0f071202011109010c06020d09391a0307021002180a05031c0c06111606051e070c0c0f030803060108010e130f020105070204 72
    0x15009545042c00300c1c07040a00d49c881d00020900030203504c216480c0300c1c9162200c07904c0303909800036400c5a41008141d03010315081000500301c0030640070001e1503000e2087c00410241a01030400908403403100740e00c0503001f5420445401c00741e1308002c1c40001585c2c416001344e03030703407100900d000c01a050b60f40c80204220410800c980010040c11802d600309401000c484031281c5801c80041c0d0106401d103d00d200034442036541042d08080ca1000315801841e500441c0d03c0b2118036588071080740c0c080d62028804072000d9400c1403c5103024004000180401c4000302060041c0c100c481b04850207032980a028070518420039403c200f44c40c0c001c0e45a01010800301a03e402040340d0040041b180704500720341c0180f91000050b500c150b5000e03000e8250003041141c401958030b1000503100c070507820400741c03160907503c600014100c1200004802441c41810400c0d201c4c203001002400b03100c41038104110703482c1c0900402085e22084034170109041d400222801d2203e00d01d0006132014072a41e07201a4000341045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 814552239 1250 814550989 814550999
    0x906060c01150801140a060b0702040f090b090c010e0f060307030c0c05030c06160c03211d0c100c120f17091b040c12050903190305070806040608060610110304 70
    0x250050903024017660100c01107541c3c1404040840d05140545881d80704107100b000050701742903000070100303c500740c0c000070a820700380c5950800711002c03100800d0543c0f01d00c00460039941e0120450703400c0f600a94918607101c03a000005100c5000041c1018201940c03110900e4010f80f1504a48102e15000b40c1504e54800031800700548480c0c00310342c1c283e548150f40751801c401900c1440c010300c0664050b61500b4941101060000da542050007200d10003a40310000403201d10b01910340e1040340c505600040446080900510030a00e080c810b03400c041c068030200440104a0142901640203014545401c507090110710a549041100e0310f1550001c01c100c007000484680081e102c170140281b45420304041d1084010002541c0510780b4060000f5080d02c4044442d600c40d80000d0f81169002e003c0c2d80c1407c890400c0101c66902c0741e0070f85c1d0002901c500901541c1500400c80a41002055505100b041d0400c0f1519950300d8002d065030f8018503012800314000c900ca10018604c454980c802d1300c0c1d40b290f0361 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 814553489 1250 814552239 814552241
    0x101203050a0305010617070e0307080730050d050d11070b07111212180a030503011809020f010c0606170c0a0f05030c060c1005071115060906060c01150801 68
    0x700ca01c0460310742070021a005000e04c51142060409280a49169441800880d00e084905040c0e60b0180f01c2d050303000c94090802d00407000a84a0417901c03c01d500050700c0d069410000d000502464501c80c040043c0c0400c0002c83c105441100c203082296a40d200c460601004040c07403203218904070008240704080000a5480d00e0040c61140c1d0381d034140c01c1c1710215154030b903000807800609402c020003440d580b5080081016902803410307050b142840b60700300b0340181040320840044000850000c018404144034520007907441040300002c0012002c0c56004c1303610540c040b410305051000b410f00c503504220700c58006d240500141c0c6806440800310340380142e9117104401c100c0b4400c0b45416004a0000411081c010440354020b0091000018003002d210185e440210001242e000f05543c03400080154080c01d40500d900781e030380854220320910254100740c058200300d0030309540c00c401d0000716a41ca03a0b0a43d0031900842c0d0803996201900c5280d8010107004d4a080c0507810800d0000030340d00c2c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 814554739 1250 814553489 814553497
    0xc070e1e0c071a0903070f201206070c0206040e040309060f0f05030c09060c07030b06040e03030f0c16080a0c1106091e0301020409110c010c021504080315040e16050409020108010302040510120305 86
    0x6923440a0038400008040001150340b04504454581c4128009028ac503c1400008031490015000d41d15047d20340c0048841d00008507419404504280d40800c483c40d0300201c010700340c1850303140610445074419001091071101421032846110081159201603a402080711310100003482242e000035504d1511003501907049401a02c0759207405200b840d43e1001004992003184103200c1311805503255400d0150341d0f0050384501020094150100d8006500c5200503c90070002c1d8a80c200209040e1070115a40c0d072000c80390034040c160a20490407551154070044c103407221030340d2050b081c004c0e058010034024001d681c01129124200720758490455455401480c5c0301d003101c40288140c10075a0402d036600c0080300004441c0c88151000100400c0344140a19044004e10200701c3c0c07400388140003c0c0c01d4401084152040350030130749040046400c010050703001407600360f41c140088030f002e40001c0c000402c1448082d000d00c1d12080000d08000300e403580c990103007103003040458101005050041035900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 814555989 1250 814554739 814554773
    0x3101a2b0c0507081b0a02100c0b07050406020c100e030a1b05060f1b070f06210b13151d0117070e06060c070e1e0c071a0903070f 57
    0x1c41d0a40d41c60065210742c0c103e86080f90407500c030034079101d0103914503d071038040c0c0d40100441e801070603407440040c1da403c280e0001858242e666180c0d0001d042c10b060b201c0c443d0180c040e400384041000308102a0fa00401d00310411a800ca401c80b5425001355403d036024902d5040c40b9a15014190800c81003102c1741c0007903a10400290101064a900e900500245200310880180700b02020b01a9500080b20034619a0b040400003050740d10b99a5192030f0580e03823400720b420030000718483e000392007034a00b461981c907000d04074206410310902ca42000850080b8502c100081003550310ba280118400b25040c0c5904010505002005814040e4121000045500380203403054130f0f0090321001480d0304001101c1c07007582d824503920101625402c0c00c00001e40c0c0a00c0d1024001d0040c03003800500c12183c07050844c412044c032034110840740c20135802e460401200909006c0c90400c24410f1a000c00c00c1000c3c00c2060020110503500030392122080c2c00d20f18052044000c1c584450550888100462429a488512 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 814557239 1250 814555989 814555991
    0x6050c0d06120201081626091903090614040f141905010e090a0f1113050a08070512030408060a1401080105241302030a06080c010503101a2b 62
    0xe910703800740307541d1480b40c00d078040d0029001001141c424011005400c0c004d594506003441d0124041d03580d005024400032180d00b8180700c040c03c01200c0d06050000610744210480100790650742c07550081c00c8039440e0b004000c10880030b45000d1000c9111310040f14007400c4000c4a01501c541d580380304c0741081d40d541103090702403c6000305041b40f05040f0081803040d100161640d100d0110324400740306092500a004003281e5807606441010b0850328800d21403152600e40d10b04d60788841e001d50542c00d04505602050041d00c0d401802c2100080126581085e01c000f1225007075001c51401c640c44c034500681e00403200b6805240148180000704d540f000c803452600004018583c1c0c1d132001001d080361800c075128280040248007140750060030703210085040100030604c0c40c1d04c0300c103060f0b00001c90b04211590140c02da0340380400e010140c0204000d2284880910b84989945001d02d0300c20340b00074962245490074240b55403014208942d500542e040c41c11700e08540a40c60400ba08009000c03018110261819 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 814558489 1250 814557239 814557251
    0x1d0a0b0a17131b081009030e0409050604110a0503070314151006030c050405091303091e080f19112707030c030501060c0f260a020c06030601171306050c0d 68
    0x340b803400e81101c0404000d80740030301c55400008086c1108200c01c42c104518840b000705240c0d106e10075110003074040c02c001e14591806107071207030780959110310b001d11a01c41c1d03c0e0200030b5580d00007541000d50340d0002100e00b6101100315010702d04905046038407407803080c005c10045010907101400c03084544980c0c06200204035044207541c0707481117000345600020741d00c0001c0d0b200711000600806481c0329242520032103546140810100709400c0c03d41044104030101002010b1040100d15035449002001e01120610410b10462001c0c095400520340300101a810f247e50b40d925009400e4425008503810a003c441c03220180c4542040700ea40c40400d142ca030303464403010b1180c07103410f050351a035071158410005580c850100e03845918030100c4400d034102e41e0444214807001c0e0101c4044481614050b100c0000340c101a090080341400580240001d000b00a250781e440204a210324a108440900c0c90b282c80305108503d5822020140a442c1080300b80800ca0003240c0040014854445041006c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 814559739 1250 814558489 814558523
    0x1d0409020612190510051005070c030b0a061706010b220b0f0c1c050319020f2a06071e02100e1e06010b0d020307110106080604031d0a0b0a1713 63
    0x940e505c240034280d0050703401e0300784140c158060f00042000c24045e0585002e2072b5601e40d41d00500000c04c80d00d65500c20788510041241d0300c01aa070701902e81c54142c01038201c542c102131403c41e135030040340249203c02c42c113410821607460b101d141b10000703400c5000096a4444500fa42d882072540b044503142e1161107140c20f0100001d40440151001c030803d55a03042c03a6172034003003544108941c0000ca80b4481c0703508010381da0a2111000061100c0350324400d6280f00c0e0380c0048105091481d0300081e03030f007494001c5000c1005180d0f20008000281c0441c070185140409019401c80c0707050903241801c0c103c1860220a90103900b030004070051030f078100c0e10300014034243e00020592941002e10940200290070701480e044a080c640103560f1040191809280001c10740b80103d003520052303440701005800000600040c55441500007400c036800440041c0d1100000300400c4a0541500c90b100001c440444c10300c4c24540729800f1904d0340f40800c11b40c002c040c20b00d03540200019092210403980c2c04c003d800345c1d0721 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 814560989 1250 814559739 814559761
    0x8030402120f0c040507050909090c040e06010f0603020f07150504060f0204030b27060c071a060f12010b1806030c030c09042402030106110601061d04090206121905 72
    0x40000004018103e811001c6041c00301402d405800917050040a0011201c292540342d035252113405c12100402d000850030b801c1c80211400c0c0954500c003130304000f006001c01c19007000100111001450010398521400da8500c115003d08000100b4404652601001c0011150041c500030307806030208105100810341404102c0c030880c40000c000300c150900043c540c0c0c42d2601030141354404011114140c204c0035283c0750420700200e5142714202070118a07032080c001484460400b800e0744041118413400c1050024265001e2030b803c4900c1858a00c1808060150a420815401c0000740a05100b81c22403407154a018a040700d0a50191083c0d80516142d458000307403503a0076100140200c07226403215140c85440808082400c400c5440b50555105400c10360300c01907000304190355405092111060001e030804006038405410002c01c016100b03510260b140d070101d06502c003154000303601900c1e4070100d201c1d80202840c0c0060410841c0401429541c034501c00a4146000c0b10208071a03070300c03021015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 814562239 1250 814560989 814561003
    0x30b010302090f0d06060e1f0603150509090708030a0509030c031207081303150e06090607081812041401080a090803010e061216061202032202010513030803040212 72
    0x340e8010b0b8240038101e4982000107554250a00079000424540c0c1c0b140c047c1910b01d041600d10012201003004844411408030301c58201608040c030b028000c44010300807103a95098940101f92040303c020000c1014404100310681c02464001e0549480780c0304007101a040e500807049240c0640180d181c14900d038a008158503819000070040c0d42d051041980310403046400a94810703080040b50352001c004144000d000341c1c44480b50010108a05545000042c01c080028100e292076070300007400d200b1030300e07080031625900003c0108074008003403240c90060310300300400e103d03005800c0e1300060102d1040380014100c140d04030300380c807503e50b44d07100d050f281404c8858004014090000c21310062084e900d42c51000e9400020084c0440282c50b01018018148040c0b0403503144000110041084a9034001c088d0218155010a0442c214900686080f81c2000c014031131a020780e0300c6001c2d4408580c020340594100140303041c403100ea025120315090450394401d0340c00b0380c41020b11031032a50309480b00107000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 814563489 1250 814562239 814562257
    0x1c05160c18060b0f07140114041e02090c0307090302060c1005010e0c0403031206170f0c0102011a090c0c03120a1503051c140a1205090303060d1401020d02160201030b010302 76
    0x107600c1c104d0140c003c0d41ca0703030300200ca089030481c8aa00c07200e44200c03002d0242030a0444402d0001d0307103604042c58212402c1a81c0090100240c3e10380c0d105801607617400e0506540b040d1003e010716500d50740c08504490703001881d04000d611000200710031039031010000740c02c8003030030846504004503600c0d04440c5286034021550142040790404c400d0001a108a1620b030269000070000708501d42c581ea000312004c600800c801c0010b40c40011494402c40081007000c1d0b0b01070080c0020801c82290a0071003a52007074040e0b401e4000c48041001c5521440c401082f2902145507009598880808203200d65a0b0300050b11509071450602003010010030009410b18105d82c1d120004044004014801016003840301c007000d014815010612032000f14940b00510f00300e1483d03507072500714003100c40e8840116a000392280d00c680d4000e05c100011500c1301102c441c040c40d0005201d000780c44505202038003a20565072440e80050020443c0ca200d54004100c540c0b14038800d803000e0000c1c80c040d000440c100d004076140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 814564739 1250 814563489 814563509
    0x90803041b21081209011b090f0e0c0d09030c050115060c030806040902030d11070b0705060c030c160f020f010c080d2003070c0b0c07051c05160c1806 66
    0xd0003a2070710a5000c0614041d11504150341130031010020400b00b28411640210565150b8420303a1096807003580c0301d0001a02d038200703103a0ba03d0070512218a0400b00d80181c01d0301030f03503a501240e071720590350058a4040c1d00c508014012900140703801002e070090440300319800d40c00c0c07800d0401c6190b0824000d00c140c420030b6441b0340ca41030b40b580f02112030180160800b5003040e0303103107180005628140714400c0f1020303070740d1101004850b8903030b58580b41c0880303907100c010544408d0002c0b5000460108106400c240703419501901c0713071209900000c044c80340780d0414103443c4010420004100c60700c8048540e29008a402c04c003001084401510a103c43c420000e0010400f00094408428558081a04445c0e88450402c030203000102c3e403480b6500c00d46943d404a035094030204100041c00f40d002d80d1140d04070103030703600305002696065600d02280645071076000e20351500880151003441942d001148145010404041905184200480c0f5020b07495120440a0820203204403602544040703404140c0b07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 814565989 1250 814564739 814564769
    0x20904030509031c12090212121305010e0d020d053f0903062814010503071a0706021b06041109060612130201090b0a0201050915040b0a090c09090803041b 68
    0x705c030000d06004204a83c09180c044030031080c0301c0100000e00c89144400034007a5134110b0a51201d452400310307404075041100341440881242c99042956075040e90507156140b039113555142040c1400d81e4040014241640f00c0b00c0381c411a82d100003010000d0b04680e0280318854180000c1140d64400d2043c0d15806078000030201e49141089030b19051002040d81d503076030305040e400c800790313098503a5202c0007040428000e0046c0801d15003841190000e200140c01c01d02c074041a0f2901c0d0b4912300884a000c0c0079158086200010701c520084081c401c4002c001c142d42441c45c01d86000100042e2200c00140600403210000300c1ea0f040100c11168520003da814001a5841d0301d8407038091211602c04030b0402c5003100000804100b03020207003924120940001c00c3c545004c0c502245400180d0f2025586041c0700d105010108400e540399075004903484002050b100da41d41032029540001d40c0c04011030903e4100c6840501100601440c011441560316081181d403075100500c3e034262a000384640c420f0100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 814567239 1250 814565989 814566017
    0x1905340f0506030f0703021e030f0709120b0903040306060303050c161208090d02031c1b0309050603060a08030a17090610271404260f0d09020904030509031c 69
    0x150325a0f42c00078483c46c001d0b1401d203400e61368401c48200307240584520500031050044246d010031102c0d5014081d450b1200c3c0c403515110340c0341f502000996010b04070000700004110400e40a00894007e15040074080c00025541d1a0050547e409280030010310b000700038507044800c12581061003101e480040342c80320b50b80240c542d03480551112010542c044008100c41005840a0006e0f02900210326445d0030744001c172400c083d21a0000c120072040c103500d20134031080000d4010b0301e401c00381d40d030640b00d0b142c41e6519240411a82610398014402601c00450b03094103e03a0310141c0d52110424454802142ea01d40381081c0d0f035621816280344007901d004901c1841000c3c4064031088468400c0b9490101903503030740080780c0c11207800e1817496100300c104078104424482d82082092412001c0800120310980e0030701402d000740192882c08240220003e80e0107030020081d0041080300b40c00034030380f6682d4241441d0143c2107510032180c40e1b000e0b0140d003042601c005900410390382c2c40035417a1079800841100d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 814568345 1106 814567239 814567261
    0x7060f0918020a17192c01060501090b040302030c0d080d020705012a08040b0c0c1f060806221e06090209060d02031905340f050603 58
    0x102d0b0034081c00ca205c035451840200704080700015042c0d0210080355404482a001691206840c8002014080c065004804070b410076200c6002c0c5035622051401c41b40581e2102a5264100c00604942410400400403086100e60601850704d45a40c460208981100c201528245c0d034a00caa05400100d171150000501c82d100e080302e0100c1c0c0343d00c4000f0200f01000780f0007801150f155020030298042d01c4141c50320040c800007a103006010015401c03c400c80d0b2420a41c3c512820580001413440000c42e02a010700d0800100250b03802d820f016044200b80949011a00c88944068550552013402c068496070f41c45100003040c83d45140c01003040c000809094a8800d80500e8900001a91300107170300c03a0f450702d0350032080100c1103050514905019100740f8401200e0404050130345010040c0328400e40541c07844a060000c2525406c05440b04203140c040c0c0e607000002000401c40ca000d01c = true := by decide +kernel

theorem cover : BRFrame.Cov 814388489 814568345 := by
  have h0 := BRFrame.cov_init 814388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 814388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 814388489 ≤ n) (h2 : n < 814568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
