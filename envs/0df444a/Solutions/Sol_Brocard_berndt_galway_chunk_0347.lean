-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0347
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:20:45.676486+00:00
-- url     : https://prove2.me/submissions/5d8560b4-0b88-4b3d-8c19-422647efa4d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 62230218 ≤ n < 62410074 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 62231468 1250 62230218 62230229
    0x207060e0a0506090c090621070801020414040515060c07090c080106030b0d030c061509020d020403030212120403030c120203040f23030d02180a1202010824010810 72
    0x10911400040e400200c0c1030014280a942a141c09903142a0900d4407196604121a0b01c034000001241c45030030304c02a5901801c1c5604e04281000040d0b11582d0320f4020180d100107110b80d000582408013041030510004445c3c0159010f0245090a0100d030450410011089000d200081a010b401c4a030030445c400085c0403004040041503030b41640200804800d0156a002c42d040100d0f41d5801c0c20b0258a6210345174040d42c0700d4004d0300f9103036102c00192405200b90302d02c008018030301140218030b51004041c914207184005a4607403031843c02030304004100201c200400b0f42482800b010760300e0b180403154410390510703000070380c2c12103002c05075032240c48450380003000752020042004015004001d01c001e00d0081a100c507265104103523a01c007154100001c21059003041c0309031280081d494001e40341c9440e80d1684240b41c807a5030350114490302415442095414480d6a0005c01c4d96004205075402094451700381c501468440010780d280485100c20b10b040128200004072007035403184001e4090f00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 62232718 1250 62231468 62231471
    0x7080706020304020a05010c03020303070809070f09090b0a05010b0f0d020708041206140610030908040504050702030307090b07030509060d06030203060a0e10020301060903020d061413050d0801050109090906020706 94
    0x2045051000003904200d404034041c02842d5408141980a2011824090b60540c010f51543c0e84a0070202d43e403031409000c0c0e08042c8100342d40031845102501002015041041c00055401d8250401b5001c628020308030002d458600001405541803000440d042d0600c0c10010607a106a0002d10304000c1c4034071031001c2c05180000c07070302203030700f07540310034401005401800107103e010055410b000b8180750680389181e001a0030039043d19102d000e9082100307000d000310381e1613050590311070108041e11811101640103030400000c102c8200e800071142c9019101355100681412044c3e030f4041c0452040c00e40032481b81402003004201c03030000790003000165034064169005408c0c2901800c01800c901c4116550074015031004401c101c1d168426a8104e9040d955245580c41c9540c007401451b0a6030141603444a0312142c041c0098071324200d2846c0159540d243c8051044100e0420500f8144003030f00c00c000704850a80104141c0c3c2e800384003d410748800c6c2c200000e00c4d01d0240340180013131080c180700400e0113 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 62233968 1250 62232718 62232727
    0x10b130807090e060a05061c050304051512070c050312060f120106090c08060a030f050a0501090c050111150a050a23040201110f06070f0507050609070312090602031b01020708 77
    0x40d20b802210880c1d80042c200ca81540300d170300340001075401c21660035400c4801e910b003404103000b40c1c05034100301c5406502928509501c88000c909201000d0b0424421749034000f82510003142400940d41d4000110b2800100701d0b0a00e65400707403644940c41c0b01070806080c4401141696480203003140c061880103107000380958581c4000c40c01392100e445a4000340c0d00e8420f500c00c1841c001c0c10703090303c038a00050a6072a9182035581c1e9961003040048140c900b441400c0140001030424400c131400c0c10f0140c032090520321b00d020f000401c0032500e4081c00c1d255800c20703031402058003401084d8a40000b031244c40400c0951b030700c09020000300040e40b8982240941141200b21003100c0100721400755001fa40c54080001c40c20205541d583c0e100c420b040c10035484000001c01c00c9210b803115401841c007130b240091400001d900c5580c80d141341611078484d030b9001000d04008011a6241e90903401c1a1410109151464071a001c0e44a008900710790880e9071072010a180300400079811a81e00c03d60140241c2c0c7c64 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 62235218 1250 62233968 62233979
    0xf07080702011e09230f1e1c0203120901020a03030504141506040e03090d030e04020d1b0f0f210608150414030301050a0b0c0727060f0b03010b130807 66
    0x8000462182c107285181c800711420411196174150908070300c020703003206c20b190301a50a00601108040c1d07800580074207001510180e5641605102042c800404d54080301881401058148141005042e004800812080f9616600401c403655555050700b40040c0036621810410185414001001c0700b80c00cc0046107010711240309a214041d10082c0c42c02c0000032480018142d40c1c2c0300d11026158010700410017200001d200762102091000040d0015040100100944050700c130003405140c61072924a01e15807407150700c1000314030642c2c0d141c1341925040d8640000540112820114ac42c08818000409440030445800240c02000c0c1c1c60129818840040c07000c0c00d00480c15502112903600005107001c0c0800d000080e43d0580300010070502c110b40c5008a03000b4544c1c8411007460b800c0c0603008000805c840036509100402038005120b140d04500740b01440c0841d1600d0b00021a052000f440038800e01100700e095a043d5040801100d0766454404594490615540d104081c40c0c03240d0400850b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 62236468 1250 62235218 62235227
    0xa0905100309060518120c0c0d060501030201020d0c11011b08040603060e100303050a0c0201030e0703050303060a17032b1b1e022d0303010b07170f07080702011e 71
    0x44060040c0340410542e117030480c1c0c00c6a180340c500b4003a50503500403258000f6100d03a8000901034201c0800031200091060b0740424030106c41424180d4181b0b60726030040013556018011664440343c00d1800820043d4655a40d1001210101e00c040c10003e4803503e400c00d4091138803152140d2504500c03842d40f03403643e4820040203409580500c0000d0710701c3d88049a080c490541c00701058940c991102d0341004c40140c000c07a440801000242e04240d150106000001024492100030310300903c05103640340f8005003413040441d030f41d502a0043c5400f00710001d14100002c0700b62101d0004084456031026100100d070701c1280b00510b0f20b03000c041e01e8001101f030010300c581200c90003010785480b001100c4048849903590212140c140700e001d070300002c03008840d94180c0d41c1e042c5142c0710000d03110821403103410301480c40d642090300190f14913100090101c3c140003100e04140f240341d91060982d850405882910f02c014020b0100003032680300e0120720f10007161300a032a01c44002d4403400c43d4910140418000a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 62237718 1250 62236468 62236481
    0xd02030103120e09070210090c05221805100507030207080307030609050703061410050c030f03040203010e0604051e100f0c0801080c1c06060f030f0302070806100b0a09051003 77
    0x860303d2030341c00288900b0880807036482001550040c003018043d0300640d8024111140f000c0752030108800001c82c6540c1c0d103c4841c810041c00500340303116400c0032030181040b2201140c0070700c407020f20340d444140042c500142c811500940e8010104090b142c00406030301900801c00028002e08001c0200283e40754140c0c401d100b110b51514040c0800e4840301c10030707411201c00e03001e01d01004060107410340450400c0451000166010320384075203081c0c010051242144c1040301442c00d40b01000080c070042d45000d01a050034038442c0009009507051a594150340c0300240c5800c01040c0c2c00341905c44a403014207100d11803400e02c0704a0244840c00708603403030800034003580745d00382c0102e601c0500101d4110ba0010302001404005808940b910100034824071050000c042d08440090b201c40c400300e202c3d4101c01e006001148034001c8403401010b54a40a810249144c101c142c02da84a0401c104034210300814110492700e4110060782d176103107120400c40300c128507500001d400c5409650200680c40d407540c41803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 62238968 1250 62237718 62237753
    0x702060f2e0b042301030216080304021201020d0b0a050306013209010e0403080a0b010509010c0602040f1202090702010b030c01030f0f1508100b03030a200a060903030608010203060d03050901050d02030103 90
    0x2d190130342461005500f00c3c01144440f900d903070402c840102c0022025002144c000740010400800808101001350aa07405540c200c02c0060300c0c1e00c1c01c0c0c109802c180700388030301400045015144541c1400180c030b5600301c002c108e0070b0005d0003032084001d1520648a101b060b164010300701841301d43e100c0106100b10041503070304070000344604000480e020b015121302c5581c260169a07440c6042070340c40045500b605030b02025100241d00b00030015800e03c5040351480103044801c0e0781501c44045004000b509180104420150b9060200b6080d4565020a18400741182400d0024001d016181d00000418095010800041c9014020700036905014086400c4500d5030013150754000c14143d001041d101d80c4502c4a0b01a4400d03c0320000070ad008020bd000a5500c848440c000c8040e00c1078040e1614055075400d42e039187d9140e0402081c50782c140620760240074030000030b6246061603408281d05280d0010003a041040110b40a02160321410441e0504544c0f07070000e544035612800d10200c80e000d1203484 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 62240218 1250 62238968 62239019
    0x506060f01020a0c030219050d050601080c0105071a190e010b0a050103020408100b1c0305030906070801050913030207080a0c050a0501090302150c0307060f02030702060f2e0b04 78
    0x21441d6100080b030880080d402002c07450058030315400c2c402c90a61110544220101c03948000c20344da107868882d400454090030051440e54940740043c0c2c10300b2606081141000700801030880030880010400c403040010f100d030b00ca2a07a941041c0402d10104c120101c0cac0c400b9003170074501c00480b0815003021464540450319034007003554480041d0124800e6102d038180c1ca407c40410030282c110580d020001101c0003401780d600c00b40d030701e10200d0080e410070601100410340c00310a01c208420208070865006201f030403d1102035040c00001048054000c02e220518400604070b9000c0510903c16003005000000c2258a0300919113800314010450303005840c0a2007c94000148540c4100a603100706c9402910f0311040c40c1d42e051b010704044d40100f003515040d220400100d4000f81080c032070a440541005001a02c82c02c000c60028100800034003424a000d03000414041744a8480c00c1344000c011404030381138210071104124509020b00b5601c03461903007601090008002000040007a10405601c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 62241468 1250 62240218 62240239
    0x10807050c0705010e03030d06150905040203280b120a0512120121120306080d080103020102120c1e01020301030c17150c1624291309050606 62
    0x200c400d0701401070302000325440200200407a5010b0740780d014040e40040c3c142c0e0315250050700314900791881540304507550074610901015490307220500d2405400201c07015031560811001c004030705000482c00c02404902c10010100e0080c550707004480144028002402e1081c146e280692609000c0c4006d132014080c148480b100510050304071040e15441081000440e400c0060050003801010082c108904100301190040ba0640c07010700c07003020301c69801203245070506189604001d5082501c509206001d8018070050307801041c1d01000c05140700d8950348170522100c1451401d080b070003500c42401e600c2283c0c40303a1504190020340c103a90280503800f001a5554000c501c000840213034030031294118030b0386030040d012001c2c49640c00c9001d8010860424460b0342c0c1d2040000c2c540304045801126000828405500c0010005d48010400404220704101d940c00302c81c05002501c1400864603215244428650310701034503442405211408004141061510b95a9100b041c0c516a00c189003006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 62242718 1250 62241468 62241481
    0x3060411040e040807020a0f09020304060605010e22060909080a02010e07060203030601050d0b120a03030507020a031b08071a0a0506060304030507060f060801150e060405101404090816020108 84
    0x7100e0031a11524200c4003180d50b01d8460a5540c0c120071422640701400300800104001130302c5941002d010705030001a582d081c240f03415002c5030504e40c4058180651041c0c2c2420580e12011000041d2a400b03600c200100d007403902480040c21507401201d105403078000d00c0c900380000c0b0000391a485001c4e400070400009610040c0341d80e0f18003031080c10016801000041c07240d5208074064001102c026802290500c0340d0070000711140606040c3da0840d42c05183d801013071607494040d0035003200c00c1d030024081c1003042d41c800402d103144454520244203c03a0301c181c0304100c0368404880c41581c100d900c05482e5881a4600c050f068001c0e81c10307109a07070a02d404101030703191480850b4040c2c2da05499051a00c00365940b10009030401a00c2c034085507548180c0041c160f08280144c42d402401c0276801101181495007004815801401c0c1c14011881e1038100180c0d00c07400071040342950702e00007110009240c123400040c054125440c000307002d9074000c203100e40564421041c2a451601c00d8841110380ea4508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 62243968 1250 62242718 62242751
    0x307110a030213020a031b0804020a061e0e0f2706040b06030403180b040807170a05280c0e0105010e040504030912080405090c0309160b0a030506210102030604 70
    0x20700002e54440c10303400a01d04032100b43d41c020441c0203c0c50501048a6020000c1011032040001c070040104400394100400c524042c3c2d25400a403455040032403031202c880183d2240d6149220001041c45000e203080803140d50b030398010500401d00108030b081c00740344080480d03202611200013103c001451901088241c501400352a020f500090503041c00d503038032038a084440702200d40c0c0740c00f10200710a00c04201000003c0040004d04000801090032514101c1c000d500c01a20062541164000e407400100003440410302000f50320a2240350740c07088500c040b415000d44603078a07004224002980e4002954107510300c00904030344090301d034101205000000c1c0800d5800444000b03000a1151205100c0b415000081c100342c3d900a010050030503454001103145d0b000260380da28441140402004420701c410000d80003c0e9503030240c2d00c030b1042c0c6800d1140070b46003d40c540c52424036440d000000e89545407080f020b0062081134240c1c5550300c284100c814000e40c810b492050003103060110602010003030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 62245218 1250 62243968 62243989
    0x16120207050907141224040515010305180d0c060b040c0c0b090309060c010b0418080414060706020a080a0b04092f03030409050603060f0403080a1a04090302030711 72
    0x240c000c245640e58204221468524408044c2c1440340030700000e2410313054100d8851045009000180c810819100c0e071101554522044510460419042120b481030750710444030020740a00700070a8940ba049405c2c1e00d00d02c80203d2101e120300c10a48061070641d0721048100341603004400400946101100384016144620503200100300c1e40d5154200007040517403a41c1d4070882c900141da0070000083c00245441d8000f08010a4582d100c001c051f005140c2413003503c0030200d508030750b02c5041d14203958210710f44c01248070340075803400d508000d5000303a02c40c0c80c00c50f1940d9038400380071951000d51220182c040103007035619032001440d22040b80304608161040200b029000b6511141401c0103109080488510b00c8005807400e1100c01200000d4404101400c00703040d81e40d2003c0741501d840d03010f041c074019001746116988040002444042900030000a4001c1c2402c1c60200d1010581036491840030189071000da0080e10b0018044149980030000d860001d200301038401049100d1301c20045084a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 62246468 1250 62245218 62245229
    0x618031e080603060403140d09080306120601030b07050a030b0d050102030403030b0f0102070b0d0609060b0315030109020f0108090f0706020d090503010c14030415020403061407020601082d010216120207 89
    0x4c000400d0101c0d00681012540c0c110350000700349400d505200000c15248a22070403220b804021091120b02d1801c2900c1040f40c4d88040d005102c0342d032554503000e0915101a19080c140a07001450a441d00e109821034201c10700040c1038071003061828a0240c0c000d500485050300000d280000b0015280740034100301c0a0140140d000b8400319040070b40109080d0b00090700c6101d442d580344000581d1011030300801d4024000740e2a40c60303c80c54070240107a00600080315107446a45403140040050340e1f005c8000d900c5c20001e20300590703250b482d4501ba41ca0314064044940003440f072010009005640042e25200341001a44d8040c3e000795203005240c01d0310035030a034280103d070070200710081510b81352010755030050140c105424030a07030801c0c08008070780c803641094540684034002c5621024000d40301c2d58001256100400c84c941c5403405150310354070031a80e10000210b01c8090300704000482c0407096121040d80000b15036075103081810b45050020301e81c04503491441810309032456800400c0c6003007201d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 62247718 1250 62246468 62246473
    0x10b01020606010e01050a030e011a0a0f030309180e0f0c10020a05072112020705090f10171f1b260c0708070b01140d08040b070618031e080603 63
    0x21540d00540341600700c8820401015607849d005400032600340540c031452501c1000440c42000036406020740322a0642000f82c82c503441200820000380e001c080c02c81281d91340c00b8406200c43c1c642007494054014482911014803c41d0b1144031034602c003183c4001c030204111400b13070310000009002d90700d03880301c010003602c5604850410443c1d92030130481480326a000c0f50130111003980555420010303c01c1e032041000141d00c8004240028104034640a41144d8081c2e00e048075490f14204041c120700c400c1c000e4140c000d03d0070b00702001c0000100490410840399021050101804110b0b9900410046903505510b1000c0d9040c6a016030060703000c410905c6642c3c0e00000c900104040320b1a0111001e0400005c00c5010405040800c04900203003040610401c0070680d2545400012204042e41300c13592032040c00e42001d100c00191800c0300705d8044a1008509640310307442400c0400007800c9000080d00ca80c0c01820721102015484080c6d40108464034120405070f845441c8105d80400c0121021501369 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 62248968 1250 62247718 62247737
    0x350306060a020a020303030907081006031101030905010b1302071502030c0a2a0501140c0f0406080a060806010609030b16090b03040c080115080c1903020d0c0504110c010b0102060601 80
    0x141040e10080c8403214450040714440911a400701386035510444680001e5000482d0a10201700d003800b000603803d290080c14800f560650300e80708110500101e620b411306958180c4001007010a41001c916180700421204200002e89000000f070761080d2001c0356400100003200c18040528401e8034000d00b1410651030400110607400d5aa10134071104112207200201d42c205601034280890f0500140300704004507010700100780b81c010301d10340940410480c01c000d115000c00145030700c085d501210414503003400c0b00c0c3c9409012900401710b0350860051030144034000720358107800c50f070120300312442240b040c174641da1042c0001d02141c002002203000100e031140104802c01d190300165401a01071139103034a0303443c1e03641d003035038211030003500b03024003941d0018010800420300b485a9420380c041524003440e1031030329807070404009086003c0280314041031000d810a0009900c7ca050160101400410150641c01064030f400d400840f280d007050741c200356600c070352544040b8025004080607110300300c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 62250218 1250 62248968 62248981
    0x3070e07050702060f0c01020f0702030118030f0e0105040302270a02030408030103030c050c040504030f020705011103030a020f041e170f0d1103130b0901030c05120a0f09020303073503 81
    0x50303034803914005c1d03054603051110054100080c8010b003810402001003035034458051040c10300791400101d00308055042a001800840e03042412008142d525240500410f074458005a07424007440d000a500088100d4032034004024210940c20340100105020003181d0702c5c0d4a0980c00c1c0e11007250014155041440108006805080181400c070700c200d0503225010781240210381210000c1720160002040700075030b0409640c0601081d400b0748820700c0c24020417103c10306101d94a200217010410615400680040419440320507074000e0310600d010325590001d00c69007a1280f4405000b41181801040c100206400d40040c0c04140d40740020301514000307691010a4401e4125210035140c940020402c01c4d0f64003d0b8019000050080044250784500f060000101110403045580040c00420840d04280e0140716000c076511000c1101c02141c901e11a200d04000340109540081d010300c000320307404041140c200103102e00c54001d055032480d107800e240c6031500880d8881001c140c2100341080842d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 62251468 1250 62250218 62250229
    0x315020307200a0b01050303122e08010209042a03090204150b0c01050f07090308131a070201170105060405040209150403050a03020d020a03080a0507090803130503070e07050702 78
    0x500a045041500070500d040c0d1254900800c0390300c010110f03400080259003040840c00150740500070641c01036080410081146a00a4010f42011850a0144c8034640d414000c2c03500c480e8468140898103840030f59810405002c0d410480d402440f8a007404071001c22499000715020005002d041c182001c2d10310304074180c0081920210590f04140c03682c0c110403000e14034000000c020182074004642d54507081a42a007103401c090100209800f00405222515078881c10b40700c2502e420810280c1d54200385040c0e80310011999000407100040b560884140d0401440580380b00c80c001c5e240c030801c00c0c2c40c0c20a070700c919031000d006943e070080c010f02c424407403420f096000d006028400b91520a0402001d102e205542e0407036801120703558026181c410406505101d400350070350443c0020020501195409403102400800540f070190791500003a190900c2444507000428121003625074036115180c20745509100f6010302d500070710415200180150401481c07038840c01069441d141050042d608014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 62252718 1250 62251468 62251471
    0x20d080c07050604080a0201260c0a0521162d020312040605041401090b06060f120403020f0d09050a060c02060403051b0a05010f0c080903150a02070b1003150203 71
    0xa15440703110030108068449070000d1016004540c0100070740c1e036075403000511013000c49141030b10b4060550480c040e201c5403c0b0034250041882209540c0301c1c1c0381190200d4207401800c000881404603500c1203220b81039410790a50203803009d00820003024110b43e1013a40d0401c0300314900c8980280c840e5a040c0e40100d802e109206902d080e1043e00c2c0f40c441108c41c49100c468054506941b541c0c1e6031410320041000c01c11240a1101140c0c009020300d0301365441d1a04098001007480f03010305030008001c00320407ea00c080700c481800383c10307a41c401400e00341002940c850341071030100858403070602c01c00b5402d402500c1240071030340d0007000440c080e8108041256014280001284c0001c420720020001490a100320306c03900fa44900c0c81441f00d0100c0c0c08200c035940f0183c0c4039605002c0c800c108210100e80c0484082500ca8015580c540d440c501440400e01c0e020298002011411f02102070220215050300200001801059200000d4503a52280b10b5880c0d43c510004121202c1c800c01c2070001d16498001d107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 62253968 1250 62252718 62252737
    0x309170a0b09151311090c09040f0b09130203070329090c0118060f08041b0602010902130b0105040e040303021b0c03010609150e09030408031215030a020d08 69
    0x291280003469554041a52054840010b2904808109100d24100760b10b0554407101460307246080d0907007916900c02640c40c0300300b40c03802000904009818182000200ca0b130f4214060402c000780ca07116850704004015041c0e00d0f034840d41c1d2842c0890600708002d10304011064005010781441032856403240c00041171352205282c65840031821038140800e8031501d89c07041c1981c0000d030400220148c0014425500d80c1046114000c09990030302004d07500580100c4801440d003020302c550703102c5092250203096440280701024041c1c0390003080980e41034115000c0305100f07540d1204a0f40624075000161803c0c040b0141c0010300500c420042c9080e24480c0d070b500300c0d0207410300514080076005000000c2c541182c540086502c0a03145000b20300b000d07c5079800402030b01104111030110074540c085001060b100380c3d00d0000c0d4030000304aa00d603082c4225401801400c0c222035491030904d0b9911400081141e50401481440e00c0440c480d0a01091814100390300400150030034020340d48003a2503030000e0208 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 62255218 1250 62253968 62253973
    0x16030209032a1009210c0509041a0c04030308130b270105040809030f010507050307030207080903150906070503040503090409240e120903030a030203090307080d0204170a030917 78
    0x42c20380752120800195440c0c040c2da164440740b4280109901d08104544800c1e03045140300c440b10f00496440308414044c1e40040f1032a48483e1201c0c10480801907003290749003116120700042c4004042944014012030b4420b0300c5d8500d00d592000260348100100220140000074202c0005440000720000040c14030b1061303c84c034001c1c4d024030040c1d40c01c592084030215070350b42c0c0008082c4403034030701041000e000c103c122000b48458500608018050700000d000b03002031603004034801003041200001da0309040005800c6842c44038901e0300784880e0800507500c1108a000b4000450b260303d02c282c08892246411400070341c6008080740a000082c00b690030291b0785c00442158204400c0700c1d003c001c2c1280006202e020032401038030883d403400c2a403003501a400c000c10030003c01905072004000c0d50068411804c00586a55907200c11904510131044010150381c400284426414000d50180c42511780003d807090415680328081036076855910300c00343c08a505000c0420040d00411034031904c03440e001c8203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 62256468 1250 62255218 62255293
    0x30f03070f0507060e0a140f0c1c05100507031104030b1b090301180b180705040e0309090a06030c050114090f030f010c0518010813080901180305061603020903 70
    0xc40c202210800031002c0364507080070004506006007c080307280c940b210100078200c402488002183c1d0f4071801c221840c0540f140c6852204403d62282c8821007698101003a182c0d2904808603640c000d0a04540c0e68001c2460308110020301111103082d141540d42c0702104403a5512402c0107010380070900810a449080104040d40c1252028010b015110346405072601150b07002c1d00e445201e401c0010055410180001605d101d81c500004240d0308440b01928005503d01c1c80015003400c0d4846e0031a80790304502c01c6400d002c0302c10034940c0144100c1c0d00403c4054100b9884da00115007600020703c2002e046042440f00c0080c40c41c2101c00c3d10b54000c0e0080403660500d104c2e022a600f918401034028001c21000320340c80c05811508900d00070202d100b4a001040303031038a680c600c00c03100c1242001070b014601c0400d15100d6640a100020401d0714400c503200176080d520701d0184d5961300f084503041400342001c0f407840902070003402500c0c04004014040c22003405007076052100355080410b0001d441c0160030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 62257718 1250 62256468 62256473
    0xf12091110030c0801090e0a11040204031202151509010311030a17040306051b0a080a060b0301030606090c0e0609010c06110c060717060303030402041109040608100e030f03070f0507 80
    0x3503070801480c455403004115082d007204050000403050340584030341820481c607080481c2c000300d28891090741c0049094801c000080115001380070b5a000280317010002d000c4004034640000720714803e030000f41d01c80b403115034480e0840c41100500b418116000985200103100180c03c507000c141d140040078040302d11414031a200c00821000780302c2c0c840200c40d03000034240b050000c0d174028903078032420840e820b07054401e08582805039031040c20401420030100b0340205181a10b190052401040c070000d00170703142d585906019005100d0707446103001e6145000f01d901d4036103000b038080711080c50340140003e040c80c00032801940d60f903c4c1000100e03050750741c0e00b0200400b6900407000e00481002c52008000506d005400501910501d0901602441ca071008100c030681e0000100c1e503104c0d42c103840104155041c03107003070307610742c042c124095034418100913000c0385e508400a1f0402140c01071071703801c0c040a0990021561280b1072140f10040b000c0c020000038a000b030045110b03411608003450241d20307141498 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 62258968 1250 62257718 62257729
    0xc040501090308070201030222060201060501050c0604060e0f030301140f030a03020d050d0204051c0c081501150c050105040f0318060504090209010207030c08011406060f0d05040203030c010c1106070f120911 91
    0x107001c7d01140040127042c050b4560910072032024100c02c1c00e00078a048031010302155907074401030000b0b0940782c60301060303401034206001240f100031802040380c0d02c03941c494034a41415880f50146038051104004000b01a00c1c002440c14075040d00b68000d00b00840890390300721820b81c400142281c916408200014980c0c4505030800101258444400c0c1260107a06c3c0c460641d4400781e1001c650f80d400b03071401c56010a2003005082c111440c00c8040c0d400c1410480c000e540a41a102014000d540b0f80b104002c00d20014041010340280320f507451038100c1804403540704000065000d0100021800d0100740000f0301071f907000342440501401281c0d41c5940e02c1e5101036400072181c000d4403541c1d4441c10454600d00713002c031a454028000b150f04c1c508100c00d000380510303203009410050412544440c086001c1d51014411500d0200d07001000384007085200308054a025120459603041c3e00c109800a01d040e803040001d103080e40010754401d01124581c6090380064041c078541a1a00041858100209d81c1c56 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 62260218 1250 62258968 62259007
    0x1022101061d010e0a030b1603020c0304090c14120f070815010806040e0a0f031805011209020112150f05040b0603010302091b031008100608120d0e030403050f060c0405010903080702010302 83
    0x9110a1f4003514011926140181c15401c000051500504c4444030080d004010703902540c0052400090954070801e04403019036481a01012807100003400404100703001d00e15a20403480300e00ca0b450261204001115068802c4482a48109144200c0a215072003184a80d42001e001003020550003404456641415014041168841ca94880281c1016004220303010301c40b22401d601e5031580e187c080003a0404900c038503a10201da40c2c2d82049401c5a0040490003090404048200306140c00140d0710300c005002ea000e054172501d15444002020b02d07060290031420400580b10314156441c4d0f43c244601c191000c4c0508402115140c04056000c110740091849402c0300c081c18060360b464034034113034104038101000f0401d840c00c08500740151880040c0540340c898000074032558880e801c50004004001c01e903141d011602000900006000300080d03003c2500b2001e03c142d401589908180c9040f500c1988601e601041c0c0350b030420000305204002418400740117040c003600e481c200c00d098880c00f01e0f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 62261468 1250 62260218 62260223
    0xf0609041107050f070303020c01080a021b010b0a09021305040c0c0b16090602150106080a150e060301062103030902010e0402070501060f17031815070501022101061d010e0a03 77
    0x8110801800f1040088110078842407001c0d14503581582c50094455030fa100300241403020f4400030402c40300c910340c1150034020b0385518901c0101541c00000380a03004509031140726803e0004040f035028401d200f00c9101e80c4071161304442c080c0c40d0405200180052080c0a000e0042c112601c2d030105140800c0e1030322030800902c54448401c0f0740240501881d150f07401c14030455121320410050900d00d900100d040d100d607401c2c282d03481d503a103506110141920300e007400041da5264000198203d1398503004c90041100710000c1c0851500c03560a04001c942c95844d403803107200011004000b0034060b900c0441d100d030061602400d8038034080089020382c0c0c024401100e290f90b41d0b001c1001520280314500d00540800741c00403024501d9005480e60b01c1c00740840251041d445402030b040943d64180c581d12000801c4501d00791a00c1142c18218000c0d00110454003483c0314440c3c816082d680c00c8805941a10780907242c038954130304000c2a0048040d255601300381484502c2c0404400d039034411088100962 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 62262718 1250 62261468 62261501
    0xd060204081006080d03090c081f0b120a060903120501120204050c0c0a031d0d0503040e0c07120507060b1309030e030c0f011103073c110f060904 64
    0x140340211041c07804000040210390b01e8030b0800240044203020420300d140d005146004180c03070031107050244003044141c0c8813400d0b62040f44001018201c1c1000100b40044505500b00440c04144040c8108030a15a80c15856a003080c0e6039480082c1940e0322012000303005c2d00c1c0c050040d80103842007504468080c0c00442954a1300c075000021480c2c85e0040a51107504e0201d0303181040000e100f0180e81e16100c0000405001800d489414405d400c1b031440c646c2014020603011080005042c41510780d8400e00482c51403081c02c6d0000340c005040201224009a8016101f1403020103183e02154141c00c43c0808071a4261a820108040c0da61240350103d203010b0407c00203040405464054a500822500fa038041d800202c02020107030394402440007218020700f450700542c50b0060400e0700b10b100303581c0700514003916202003122030f800e40c4044202d600291030340305203015502c400710f081c00c804dc1c1c80c00600240c003d200c01c881e01e00300481048184400070f00440d080c8050303040000e0035031318840c10703410451 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 62263968 1250 62262718 62262727
    0xe040c080111071b14061606020d0603020307060f02030f0309010f0905060105040b0414040204020c1203040b04031106091e01231e010f060f051210030201080a180609020f0d0602 78
    0x81662903100518000030700480d130f280c03403421299604844034600c1841c46013002150a800d03020510481c0149a903204030119910760b000c005100040040c1c0c04140c0c080d22441c0808102d01d4040d4201c8141408540c000b10b09002e480c028403803141d0310003802e008580d500d8001400042c0c4540c01010320315803054010380025030501007804201d034113484a0034807490500e1030415100c81d08200854101c2d805072030150740c640c400381c0028076104410004c110110400400c01040c0418407102d9030050b44030707640e60b41030b4500c018045a5516800e451004072034001c599242e005500c3e003900441c0443c0250300220300c051444520310400414400a1541d28082900308404241e400c101086c1c0020b245c00203442ca5410414460010241406010b00740f00c200350011211a000b04146c509507001094206080e01d480001080c0105035448102d002c40c2800c0c1c0854140300b12402840001080b203118001d50407421b0721048060240301c1703420307a08a003000300c00c501542c03607201015072513074024800503a0b43c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 62265218 1250 62263968 62263973
    0x5270601060f0f050405060703020312040602030702010f020702030309010e1906110613080703080c04090f0218032107060243030509061b07270908040e040c08011107 73
    0x440e102c0c0304120b01080400c0303070703035090f89500f0500b036406603101950000d0301c84049140030b034954810803201c3c2c290014030900700020021b89400961042c5130030780c024070298514100c15000c0c0c2c014803100952607082805980b100d03500c1103121003040040245501d10f6074803c01d10501900459801c4040012981e0908850100c0108141b40d00b0040700130350019a01c040303840340081c80c002c40100908001c0a140403038044c404500a81d0b0140100110420404400010300002580321480901240311303404c2504042d4900800c80c0c000e200c2440b0000031200c0e1005401c014598002003007203400c0c5e03601740100e194030300b08000d2604844150407010317044d0100040c00340d004641400c6d03004075000f490100860020754090241d40601c907042c0e0380c140c1c5645070b9540e0703040e40900200322214184a11940011103818400014816590010b400040703a5003809221040d266030200280584e81c00304404c00580070b5102085600c02d0003620801401c0740c0342c0006034207550700740702d07454030180012601605 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 62266468 1250 62265218 62265227
    0x5041508010e0a0b011e03020a06050d0518030301060e010c0c080606010909090809040218040504061d0c0a150203120f0103020907020309090402040b060702040513061116060527060106 81
    0x22142d0054008145000041c0c0d64454001414042c006984d10a04441180c24050b00c000c00040c42e8028980c048064440d00000c0294100b12428aa50ba05120100742601e00005d5408111051407000d50702e160300f0034409840d1010203c84007810400140441c2020503d020f407148003428510003e801281400030004160b05201e401101960749000a0000001c03028801c03925011030643d40581c0360084955028121415030451542241c10305003040104400c1f544451990920024207812003000b20139180e507203165840070544c2100c0c11220038015180f100805500c80070003841105d00c1c21042002900140c902643c1c0940914011001802146444c4d41c2ca00c0c0e1110013440198100240c1000158171004080d102a02a80d510010b4141da030f101c01d01100c3c241d98001d8828000d034140108070190f43c1c45842c1d01034a000f03182880070b00503402c07160202e07003c801d4014000300e4885400d44601d0010a000340604070b61082511000c1149200310200703076504c06210020b03203c650700d0103074080e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 62267718 1250 62266468 62266481
    0xc020103230901020c0f06090303070e0a030b04030e01030c090e0a05040f05070305060603100209010e0909010e030c03130602010902100302090316030803160908030412050304080304080d11030f070213060504150801 94
    0x2c0306d0f034021a00704a03000000105480d84881e891030450074081040f00898442c008070b42001e0429007c2c41e003044203041d088081d00040a40aa03810804010300038001c88405019002d071000000700c0b2000309160724080d4000039003040c050404030511614503911540f400c0307195481207809030010020048985030600041001c56440c40c019407070031201b500020010402400360910814042020680c00c0713400354421300d0180100001c41e81e40306101d281c043d41e642c12212400303803500221032010519505c180078290781d032a405888a1613006020b80158040e4218044054152040000e65400c1c0343c6054841d00040d806441e410780c6e2801d01c03850b624481c441d200211401d01000160802101d0700010442d01120034028121854901503d80079040d8450b56200c0c036400d00c0081000305250f100890300b00042001c540314045103c0004644030b4032805920950002101d041c0004000340c2403068400c20380c0c410a00000400d40c2e00e801c002001c80d54010792800c10311010300300c01c0c40034001c24032586 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 62268968 1250 62267718 62267743
    0x2090d05100b0906090402040207050f2515020d050c0c040f020904380a03020d0b160e0f1c05070f1401030911100207030b07020a0c0b09010c020103230901020c 70
    0x201c481c1c0ca13001011070b0240c0c00103880240180e0307001030360000b402414000100b6070101d40041c5c40007909a40302ca0b0b07200c038003035400e0005030801e6540000303900714002d02660f01c0300c14150007070182c18004003c283c400d9086509010340f140148818034840759030701d204000922820702c0c3d00613103604c40102804100e414a401d01c6042c1c40c80905442003000400070010110f03584200049003190000001c101000ca81e980029009034014038041c08008402c0b072501e01c41e05103607116410522130080122111000000032982005c41580303d0040c5052a404071071060303004000ba2525021b00b941c90616002007940708000704419030078180440c0c44c03200c003c004460000d20b000c1c0302458958590b012010a40d0038810302c04d2142c9188800094000c0c0300740b000a5400107443c107101d1a1848020352201100801265040480100410300743c43c0c50061b14503800e010f07035030341703000086e26401076004114000d000e03202c1c050740410b40702001d50310f04d0150344220040d50015840d40c880417000c038682041b5201a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 62270218 1250 62268968 62268979
    0x2030a0f09030903021003020408010e030405010e06180d03090305101b02030901081f0f0305010b0a0504050f0612030409090c03120203030606180f0d080a18060c03110102090d05100b 80
    0x1d00020940c0001c440d0b0070780750122218013810455a105078002e100d07540c0700050a5080800c403c4c210080400a00100c61003a22800c000700300040400c0420b12034400c8500c12140c80c07090500b0309040422300005824030030305120700d045469490b0b00785810005516440c0083e203401004144910b040e80040702101b907400154240010603002802d880303002401e0070100d0002d0303001132458040780f0300750b0380041030303840c401e035542c076407a82040d90283c00980101ea0103100c10410004450410344200b51003015106044003080d19030b00208800c1100a0b506400c1c80e200601c03001c219100383d80300d180e200e940314650030501c4518500d459000c444c034001a100940d0428400c008540d2604400c4800b095103040074601860560750000310044803150340c075600300044420183c00c01c80d001000f0254001c182e03c8840e0003c42c0d011a184480820303016060000350f00d10560700010340168450700c0c071808031200150400c0b032010046142003028140c1950603900c071400e210010f0040d0300c96105526020790b407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 62271468 1250 62270218 62270231
    0x105150a0b0f0c0102070611040617010e040809130e0d0201060905091c050f07030c02040b031c230a0206070908030403081603020c120721020a2105030d02030a0f 71
    0x192407210300a0400d00e901c00800000c1d514895002941101c202e80c0e8001000c200384043c1c524401501e800a01440012624440203141c6000054240c00c2c1241d0402c2d50400260f03440d80e8038258560040c3c1c124a82046c1d101c17a04203a0920540906c0c0c540010041c01028408a035180007401d607203481c2d00811400c1d1170b0009001d410750740440e03005001403840000205c03c1016040840c2d90b8403420392209650340e00880c00404056001c0c3d51009102d0080354144100e5291004042d00c6a849101c0030320b540c02e401c0340320342190340075515001c0000c03202e400c200700040410280002580c402081c034001030300844100810071790004101d0300541542e100139803e160440c1e417418010f100d91061003074440b40c60070110080520070072a005028001034141c40e46e034007541da0099950b6507a8050f11200040e94030788c005c005c1c2c102d24031928036650000d1404400900e0448200d946d0009105400c003070101815a280129008100905000940030001650f80c0340c0003401c03800b00c0e8600d41100880b2401c004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 62272718 1250 62271468 62271479
    0xc08040b0402060c100c030b04060506031614070204140405010606020703030c0602030c25020405090a020a050405130807050a06050610020a1211010608010506030c0f0a06030b1309050105150a 84
    0x80103141e000368181c1e03000d0354814810560500d0070401480390321801d810704042c180ca80f607041c0c01412503070206480c1400026150401c00c0218001207400c0340704d0484140400c08001d20800c400b00601c1c0f0200c2003149402c400317401140507100c903410403401410a01c0140810030400f4450380d4020480752000e8014181141c1c2d00800c4a2240c2001901098020011441f03012110f000c8401003007003441e011010108410b081000c0c0050404280d1081d4078020018418442c00b2840030f0b003440e8018141f240355800c2804000007000060448100e000c110b0185c54009050103008090032401b1f10018109100949400001d945000b003549005540c11011540140c1c1c00183d54020242d00480407281c0d41b85041003150883c2000030900c0031036090500000b407112065203e14003542054090f221030126840502060741150048281c10038032400040021501c251310040700584000d0400854000b10b580c804151a056841565603955030410305c4200c9095484000702d4000c2030b1b540c900b40d1071610 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 62273968 1250 62272718 62272733
    0x3150b041802040b034c0801020f090d0f050109080403170f0306040f090c0f030b0c04050d0b040302010213030b070809010903320307030506010206130c0b07150606050d0c0804 77
    0x140404a8101802e000364800405500203698854056006c00c0c0d884410b01606941044884441000d82030019102140201040c0202c8240c0b165440c0317198600b5407400240841125001c600f0344410900c40c0c8141c000900a015001c0860f020304901c1d80caaa065080500181404802c0703e0940081000300002d959044000d40341d0021013240e000800109075271020029214000c0c0041c001c0b45042804202c60181a40c043d080d86e0044981006654941c0561010340c0f19a01800364042c01d40e519440000b41b841801590141c400d2002605101003103044044541031500120740d25444d07182003010956200c0025684000120024010a80c447e240034000d54075602040040c46045041d66045070200d68200c003480842d840017540d0703131510501c0240101404d50f00d0340d006000300c40228005050003494032041c9074000f4032840c0340500e81002421a984060801c0b9460f042c00c040c070000380745070361090800811594490039a40c2c408a0710401c1160300005d60300050100f14824070000c5041c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 62275218 1250 62273968 62273971
    0x712050705060c0f0a030305150409020d022403010b120a090314031305060903120f07090927060b130e0c040c03021201060207030203060106050301080c040b0103150b041802040b03 79
    0xb40c031599920b010b440704403400c09802104210407442086902e80030564140d200c20300c00c04030000e5801c1c2202e03d81040105817101c4801c041c1d44000700c1014840580b4100c01e0700190742d0360502c8045a0451031000d481c1464100341e101ca455003e0210700750340001c150400c1d9940c01403c85030100100c280079a8054240c005048503a041410044001144143c4410400801c0e503001011581c551400c030140d0303956a40315910303107091200e507400854845040418140d018034034540b5014240e6052222440003055842802c0a14204100d0039006c00004c0e05a1861403e00811011400380071007401c2c4080d581480c000901268902206000043c60101d2401664072044401044c82c40303065034120080d0007071481a0b0000321644c400044c00d960001200f400301c0c0e100b41e0544a0b1a81d0702c020a0300d440c0001d1242d40240d800c2200d056071545000d0303004150742e40d0305060000f2202a01c610814402c4219041041014800a01030007541c0d02c0703510101400d420000d055140a06021086545000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 62276468 1250 62275218 62275229
    0xd0c0305010f02030721060b0409020306030d020f0a0602160206120403230a030203102d12030504030204091a0a0b03011a030d180509040b04060c1805011112040608010807120507 78
    0x6c07242000f40d420f40590450380051003400c0303409407582c0d12041d8030345c000e5000351a858070901c14010348a035454008200c00544141d041c0280030b02001c1c5468000c0030354066011a10010950046940140da8213806004209181440314207246018031f40541810282660403588094502c80300e1000140d5908a4800c4404ea03c2e02585070b481b203003012000340304c1542003040b11500d1071400780f5a5156030104a10b4109480c1414032869903140090000d440b2015409000228208070620147c2000e03044511458806d010852844400007400c050341481500d40900e140e49804455080345401d00508500c015000200c0380b400d01c164002a13a100d0030780c141c100600c00000504180120728001240c000c00340a0010240ca00e0a0f00d00300006105c00c4508441039440c11441c01d8030a4072611302ca0442c03907400031032400f1281c10302c401518100c0710000c17100824414041c01d0501c2440d4030340a00000c00b0103449206443d41840086810040144c009085c2e4400303240090000c00c10001d4500d0840c3d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 62277718 1250 62276468 62276507
    0x108060f01032705010c08010e070518030f01110a02070509090318130f0c030f0e060103061814071403060c120403090302190609080a080912010b0d0c0305010f020307 73
    0x10030800d100b800c1000220f02c41500401011001c0041c01019040481c4450b0203581e00403060780c03581d4541000400564422000400c1444503010a00602501c1d05420100a0807a50313410303d50556103094600d680c00b5491040c2001c01c0c00f1028a0b0104840c4024060840c0e60090703915110000301e0f520300480c45000c070700074117412440140307444048050340404181e03681440120108044007002c0c1c000b85c28040c00091515040c4030504030244500c1808441100c080d201c0790b40380d511800040c0808e8940d056605544000c0c1c035000a0205518118280c12640540071140c070780762403502c14480802506019400890401c440300e21035200b04c4210f1824040940e485d5155400d0444110025401c02504042822120a41c00c0d42254200b8210741c043d80d10420078a4940f04c12031f031540503010004003d1b10051048021a1621026041483c0c40e114000580065030000140c0e08034034901d002d582c4c100d0341e80c40134400e100703003030041c08901c1401c3d090642c9181885007004000004100d80c4600e440f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 62278968 1250 62277718 62277731
    0xf0a03060e131505100b07080304110f01020a03180b070b010509011202010c1202070e04030203030a060602010c020d050304060f0c050703031503020a05130e0106080d030605040905030a080a0e01110309010b0108060f0103 96
    0x8030340810405018001024103952985010320323140100e60f006890994800b032002040da80c1c3c926044800406004040e80a8205640255016203001801040c10034102100d83d4010032468403c0014000c0503028103800e2165500d804140000c4030030607001a03000750080e240b20380240c0d800082d00c0c2c911662203c603200300820100812410041a030704505a940008014003007410f038000003840c0904110301c410400380d0b99540e0f0603400c032060160304c0d10268121203402d21034a80a14003441c3d0040c082c150104610845203c20412504400162004610301081200a040c0c1c0352182400c55070383d504843e1042d5003150001b0701c50150398454948a800c464076122840c1e1085c1c0c201d150080c010a0082c0000c1f82c540040c1e039100d4007004842800a403030309074005560701e02400b420748140e8120340074620300380b01600210392414000340031080d1103844038a4804002c000b4070030581c0c2000100c00d40c23516810154803007800e4991b0003244904005484c4140801d90b80c070240000f50654003404e000410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 62280218 1250 62278968 62278981
    0x1b231315030b03010f0606020f0c030d05090103061d1608040515071101052802040e060d05120a030506010909090b060103050601180e010e070f02030f0d020f0a03060e131505 76
    0x540365030200b50360954200a640c2c165046030b600144180c600a80070b90340308400c0e100301503a580801c000060b038235a01200460392000d0080000301001403041c9808586036403900907989001e4100090882070310020010013a0040661045000d42e02191030015801d003001d480b195945d1062103a01d0400c0c1c40031703401041209001c0c52030712a6000e0044020b1103203282c200021440d041040c4100140c4802c4c40310741004ca07d070780d0310854007034500108400310b003030b00d40c00c050100b0b05031480c1c8111000d02c92055494000140100500203e1546660201d00b9240500004288101e16841001c61a0909280100049803401169805142882d00080c5541c45100480d0302a05613482214a0300c480e880114040a03c048034505130703005004500c0064445180490302000c10610410040c0c20034880c441004030f2800003072078401c40d034400241c1041360425403801194406030309070010070f503150820070191104a2515030b0008114a0b0030180024a489d40d208500e00c3c580c8070401e41d655040012003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 62281468 1250 62280218 62280221
    0x60516020405090f0706030902030303130314030c091f050304020114090a080303040506070c0218040302010204090c0309020f030c06090f06071e1a1312031b23131503 73
    0x20900d400400601c000c0c10002041c41d11038081c0d00403451039000f402c4000ca040d901074024901c403140d000d00103500d1540c1c2c680801074a03101d980030880c2000318070340003048810110f4000d54000e486030080b00d03641d00c0464080026061045411511074400303a6042800c0c5a0000142c9920030f4080c02e050036500490404007400f0303c2002491640100340755800708000c20004081c500c664860800c503400c640300e090060703034a143c0b11a0000d5000c605884065140301542c40c001e0f4025101e400051306168542d20448180c52000740c01e440020355880c0703000107516080b03407603001c1200b003074001e010b0b419070000c0407401a2240710312081c01000700b4542601603842d140210340402d5007003148000320504c0c8045100200030390140c00d40c0c030001c1c02d60340400480d002011a9009100720b403c14084440701d990b91403401007080941500740340d52900e80c0700408440003041c0700c942516650f03036402d0510201c03103803800002c9182e07c452251401d0212045480c2c0d510700407000e580340c0500403100003840000460 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 62282718 1250 62281468 62281507
    0x206061f110a0204021603080604060503030910051306170a0e070909030903060c0c0b1501020a1103030903120301080d03020414190807120b0106050313020603150603010305060403020c06040b040605 87
    0x4d40003031000601c465550000309000c0c02c404c0c0b195460700800e0f201c4100300800d4423440c0c0541d40d8141c10801c4038071307050f1400a09d030242e6405c01d410082d040c0b8602107440340070f000d402d9000e40042018000103540d9207081c02d0380940d2103074050300200302002100700a0781d51915240a80395149607500541d905160140d412140203680c0300006001d00c4900ca20010401c0e81040001c480080900000c2441c0a001860b070424104069004111802298844180102400c0c100b43c1e0140400c00945c040d6440138000341d08048003c10b41666294941142c552800501864000406205100034000c00c102c42d034407009128000c03142d803155900a980d51041074400ba5000444511a02c0c1002070020700c40c0119400380c601441c20313201c0f0380c0e81e02c040c107840d2880b00700d03002c205030b106c132960510051400402458110702d100101c2184110020003181041c1d20a07001611150300540c100300c2050b604024041205c117080d01c0c000d040900d4a011540c50340614050f800520101190201121500039840c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 62283968 1250 62282718 62282723
    0x30506011803050d08160c06050c040302090a0b13020a021207021215010501021203070f2003120a0e12031803090a031103010f05010617091005040804060206061f110a 73
    0x1c4140b40c1d6450850740e10102c0601c1c0c1804518200d001580c3c40f8428001c610300541c19444400800280f59a08402040000c2c415408101c00344404405070300c84a48852280c89854400900f6400520030030040108130744030480420700400034441c04550104084c00c0da0403841c03c0f83c1d9141e03036082c030000c0d208038052000e0800c0b91113030681006540040070041812220280c003500e00001c2290344024152108a50741008101d40d129078007419449080c0b4032010042c200e1200b90b0302c1200000b040e0031640401c0d80000320588800034041681c3d82c0703200d0307054120384100c014043c6800e01d12000c1c5d164000100300801507c03107050841c40340e81c4144106c41c3c800c40c0041c2914559901e0b8034000c20110955185103000c2d41c03801d004105040220b204a0781641c0135a120404a10124101040d224000400312001c07800b41c0280394030342e80317103074014240030f00d00c00c2128548613824203c00a140805c000c01140c415081244441c404028820030440b9aa81620300480e1160304030010301d16010360040700 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 62285218 1250 62283968 62284007
    0x803121b070c030c05010305070e06070302010615020c010806182e0e07030e07060203090d03021c03020403050f061302090601030e0d03051501080915061c061b0512010603050601 78
    0x50401c0090142c1910b098900c5002281402d0b900d40300110704886049404001186a0303032845c40c0d0b1880c1040151600b03521a10011988075125032048801c24541e40448002d0b074002042c80442d50707000703000d00340d100100703480c1c4242d200c01c2851400345103d000380880108540d030354001a900b9800b1341d100e1001c8062245a42c00440d990740d0241c0030f46008580100019140c1003980051030004100401104c003181d00075400c005040c001c02595118040c021070035445090040c0c89c2e00c01d04c0204e00345080800d41c50040c1c55500e14180030b400c00c0708a880314240382d0407610402002c01d03405040316075445d8040d07841d0510741d0340b100d005074000c101c06641d8a855100c0d6109114480b9803580195108030400c0703035034038620f200010054995900981da0303604190460700102c64400d031340c0001c0d2030b4003210041150841944500d000c04914050090a031075464580205982107036001480a10402c1c2c1c80c501140782030780d0300000c47c070411010700540040503141c2c2c002c61020381c803d042c4d28642c8800c410f803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 62286468 1250 62285218 62285227
    0xa050c0601080304150f27030c08031b0a0507060e04060b07060b010e0f1f0207052d010f120504081b010e0f03040b0307050c210d11040803121b 63
    0x80d901d80043c411040d4000065041c07a444038032500070329808400c96104c548009010712400356101119968180c1c03c2c0354004c7e03000010410315400b100c000e080401c0510364858000a00c2400c40b107401540c807403207511912942c40061000a00c1c40216440f81c9050086104024005405004540e01038144a0b402184c070106010480e8058428400300b601c1c2d11100040301024400340c2c0c0c180c0292264054100c80107000f044d0b1111540410688081c03040d18601c6464000064a801c3c03801d81681040c81441d282c500e80d00c3c03600100700c1c0c6000003402c02240e0241c2404000b0a094042030130406015150004a0f081000e20002d4520b020f0004641d200c0c18a002c60b00140205084442070145204000c250210b251011044900303489039010001d24540d40d08006480680c41004104441d03c5400c3d940e030300c51303035000d1075030361811070780001080d5200480301c2d00406460050a00c1045030004010400050720000111808079868100da210280d81e2a64880d2000304242982c1d09000c00004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 62287718 1250 62286468 62286479
    0x204050109022802030409050603071203080a0c0810030210020a0503030106050909010b0304050307260703120c0e010e120313030b040302100203040c03061a0a0f05010207081506060a050c0601 84
    0x100a0103a9003a8000154010030341207071515007811043c070074407000d03070802c02052102041541240e41d2000d03001d02180d075011350740c213500010414443c0342a0002044602449075410b014000d13072a41c548945803c0d2801d04102c4116404d01c3e070340c1d200085c0b143d06da021403400418028001d020001c1d0304141a25100d41c1c1d40e0301b024000c5c0e8030000d100c034402c40c12400041044d5810b00c3c1a607004903089070003141045c02031399800f0781044810200580041c2030900b01c14440120100030000c40c3e00c2903980048501a04500d5401d5a203a500ca407424449000700800c0301d40d84c4860b030030800601c1210300c0d14905400412582c214070442010b84604541c01d88040180210304084a0080d842542190f141c11a50764920040740019200100004400038081001c00c0305a001080c10702c0b80450401c500d000c048000030300074586036010740321b110013104c1e0411031585c0511040005140c003001400070203007044001030f44a5001000e140c860000882c0030494a48182d080d9046c04d42035904454013941c40c0c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 62288968 1250 62287718 62287721
    0x702011407081801061a03271f0509061b04090203090a020f06120c0322060603020a050114040314070302062106040204030b04020d03050c0a0b040b010605040807060c020301090204050109 82
    0x1160480c3c8001032000c0349809032501403040b0001c9484c03802e080840c0f0110302d11181619407000d040581c002c00603003e001c0d11600340701074492002c80742d50028603100180ba010070f01c078100c0c03240e40c221030310b49400b041110260300818800e6000244140c1440c1c500c034a92104c40f10b600443e00003100d00c43c4017008000c0d03648000504d80c0d01e001e0003290014607075000e41040101901c86e940c0102e24003198000802c008080c0c0d20041c581004104401010340c1c00e811450179103501d010b000a40707013181c8409040081d8103044001d40040d18003868229001000100809041d12a501c07005205084240d1030748044441071180601555004003130700c0c0d443c81c07001802c461001c41030640e202d00d2155070b404900e01d85428800c40d000c495102a4444540d5103940030000c48040078a8250240b00c0100b2203c0f442900500c007003400d2034410001040c032030905040244c181d460503044041031040801091150003400102002107840c1460101c105440902c04a805080c074070b10000c4d00135003058000304000130305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 62290218 1250 62288968 62288971
    0x6060504081608070605070218040f0b09071409130c060c0507080a02010f08190203091e0a0201050304201302270109050409060212101701050708070503070201140708 73
    0x180e60884100104580040702c07500c0407803194051552100310200491800342e0701038003116000800d204d010414248002c92140350403502114403000c40e210750303800c006a1243c5150010070302c10080c0606401c000c411b40062a451400902c95600d0400003880c0300c000d44050035a41c0e90092120304003030790b40c450203420359146460455040c0290352000c02d42d0440002c405510756016034038200008900103007559401e0003d807851603800104009040150214002517000358009001003011030354001c03e802c544000210010490b811207081040540c0e444000d49400a1300054071045992909941e11110b00e20300d0411a004101c040000c122003038264040c000710301b0444e050300d6958003894598400d21407961300c4039011409600c014801c41c00d09501940003d0710800300145446a1a030345a000c51000b112245050380e48800d0070b001c03505e5a036000a200b0a848002400a4100b2580140101c1001441d07403081000200010b0074061003504134203100c00030400c10710621b042044004000a00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 62291468 1250 62290218 62290229
    0x708130c0815060a140603010306050703020c0609070501110123091905010c0305130210050a0c020301020d0204030c0b03040c0303140d0c03060807120b0a020c01020c1902090606070f03080601050d06060504 90
    0x101420005500801c0007917a00058401000302e4616030a41e07951500400d009001e101c00c169003841030b500540d1007048881d00a4a11000402c00d15203444c000508100d4440e4a111069040020480c1310b00496a0032085e401610b500c00070a03580d07103040140c5854042c007240e22008200829407001d00c4010340c01000d180d0215a814000744c0c3c0c6400210705400d003428802500100004541458648120702414845d03100d0310301451045c485400090a81e00000c55038036403036600103010000c000207000c840300100078882d42c280c1945400d072541d011920103880040c0a000c1d035484010b0301c840c0964115100118514400c002c1b01c40713003800c000c000707003480e018030301d068440d03008042880003001c0900c801c1c0661000383d203c1a0340d03c4c5106c0c0d00294124041380401343d03400303000e60390381d054007480202c02d14081186610441d909900410042600c05000c60380900400c20040340803440c0c0d000c4031402c09805042040e1107448a00040742e0f0b40c8100400d2180381c515010340402c05ca41d12030004c008844 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 62292718 1250 62291468 62291479
    0x9080f091003050103030219021f08090c0405010303021f15170c06030907090e03070c0303020d0f030204050f010503100503070f06080903090a0510020102070b070302031801050708130c081506 84
    0x480500701501220420301000d005130303208401a41e6110a11412811554070203800780d91503801d40402040460101d42400300811044810002c5050041040040301c1d070080700c0a00495141d51406034486c50308410048016105604c0c0d4414020326401011a201510003040b00f1a541d41110070700e04104481a0441d5006a5400e18114038201701900e0103a030000b805014007a14100054008050442e400503a50200b801083d000c59819006800218080e4020702110401c4287c010b1000400402403401c1c14030500c014000b9403100722944030301c500c00f803c21640da5104e00c8522500d01c041030b40b15641c1485031840218180603e1200f501c115001603c41030b00c22303200c04000d070351240200c48a59401120114040103239241ca54815008d4905c180001032800d109901d9000c00c81d041206c00c44042900001400070703c000342041e65980c550090b00070041070818610040c0111405400101c09040340c641d800280161440d0250003008070000b210222a007020602c205801c1c00c6845506c00e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 62293968 1250 62292718 62292739
    0x90405090c01050409020901120c020c030d0f0507031b0c0f050f0906060304030309081605150603031306120f05161b030801050108070e030607110d0e030c06090409080f09 75
    0x30000241c0580c0003030058482c0c509150a000320000250400440d21b070402c6005031140c2e9100e8110301c510142039515601400e4420010018549040f05a00f40a000c01c000135046941c0e0030b600405580e84a0350500c0c001858084250905103051417018000d0074070030b554100040c2a40c610410001251010350781c0d8940044440200b0028460071289550011000c00014000a00c243d01c0028464402d14917942461200300100d0403c00041d1b034125240ea2108804000d18810030010740d920820440041d0320b416420f000c003191900d81445007009003c06c03204071041c2414250010300b40c2d803016083c20000b904d0250f9100e1a0724840c030308441c0100b80089481100400898095101c254050700c50894691a1000444099100500030300800043e9084e070700c3c282e9018030003030f40940b22030355400708009102148076040942d980d10325014000c0508894460740c84c0400d2b094007c6d041115560340341e52503500840c000c0c2210040060881c1c000190141084801502400002c1001c1c0d850f207004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 62295218 1250 62293968 62293981
    0x10302070309050f01140c030a09050d110108040c0b0706021201090c170402150c0d120e0d0c0230070b03130219050604141c021c03030e060c090405 65
    0x224422103101034009040da4100340480e0911211284090301c041c548170b80401454101c00c500c541020100c88103070342000500001d032580c40008140542001c891900840b42c2950740c24030401000d640307080c14001c0e4000054203000140206100604020901c00e60b6403100e85170a000940c000000035940402800012a02c60141c2c8204d020b10303031a64441ca00c2c2c071018000c0038100030308024000c0741d1000c5c4d16070000581a4409010b0440d01c07880000902071141d8202000d00116840050050078501c1c2c0041c4a580e80400174103845200d0081c100280c0411050000c180c074001d6207035200d0609012078114004061355285909020f43d040001e480c00c0c00e840e0620344410340300a032808440103481d00d04120143c544918034482540d80540c0d580303920b6035524041206a042a80031121000303081421041078140901c910007004108101c2d00c020b1896940007031403007000121001044504007151108046c06907108040440307410b070490301c3c00d1030700c80c24280c043ea0100d00001d00443c10301c000300e0300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 62296468 1250 62295218 62295221
    0x90f1502090a0e041205220b0c010c0e030c01110c09010623030405031903020c2a030303010e01060804080d09050d030e01021207030e1216021801080d23030f04050601050103 76
    0x6280d0010317580c1380014191201701c441e0740020030030010f550313241d850301c81c0e6000207241c1680080c0410902c036615a41c02c0b041076806c4458030251001441900c0d40d140d046941e01050b0482c80c420309080c04446081440303200c9103030100150711180c00031401c80003c100c641e003040c40043e10000c5160031101c000500000380400d4041910000c12a60050040340081c04140c59080d24000c000d1400504103000c40b5429440c10100c1031f4003007008046000040d0f0101d0049000540460381034009510f507524000403140d401005216503130410440c3c1011404004001e81290700c1000071301c0040c0300741c112506000d40c80c0c10122061001292038003401c00b0303038400c060007511000c0100c83d02602c40f55942030f0081d400fa18900f00d040302240504100a201411190042e08519a10b1441030040222920521060400e12030a01c0400b40b40100100005600002c028028065900d05a100c0040d031080b00e29900107440b0710040300e004084204040f40000c04100c52061b40504111002c2e40d0f0703103000660 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 62297718 1250 62296468 62296471
    0x5090c100f120902120618061005150304020a0816051906020604020d031806080a0f060302061c0908070305180111070605032509150206011206090f1502090a0e 70
    0x100410764022a104441941d0b41c0120050f41c00540440709050007a206107041c200200e542e00c41444040421070044c51040000715808a2148104d94032641460009610281840071581e814580000001c046482c1c09040400425030001219148160b010941e40c551a20703000e00c90013502c0e01130241c4825120040d81d2021510039401030031298035280c0a0243c1c15441c1c0300c098041c850400c0020640c401c1210b62980204056540c00700c0ba42031815580301582c40078003c1000113401c050f418000b41e51440700316200c441148020708402d41e464400003000e0002c54101500358040400e55409264115004102440c000d08104000f81601c10040d9813010400301011020381c030000b003d01c0440c0c0108011500400d400c041004e1300104000030921308030030350300c00300b00141c045a03003001218916040c0350003481c02c60000d03000f107604208a01d06503520840700540503a40b5803141c3c8083c00400e1030003284503030f000009000a07041c20610ad40183d4400c075000ca0141021100005526500140d0103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 62298968 1250 62297718 62297747
    0x1020705061608060f01030b01030902060d06080c040507200a0501021c1d1c020c0301060b0703140306060304080a11070314070608060f0609030f060109051605070218090c0405090c10 80
    0x305c041601030380114000c00085840324181030b1346032500c80140e6074071000b401c2c42980164010401506145120342012001c002c0280120308080c00e010585400c61310030040758014005001051003a41c400c1450005490400f510552000900c0e0f45011100c2c44001141340b01c0b004c06001c01202d103d051a40d501d0081d1820540303800c030141c0c44209168900c2811451207051040f0f61001003014002800c4429990245019440000d00c0004150704004141c0f011450000040d0442c6003040104900c0c5c48000c0004246850009010202600031160200d06844c0d030012103107080d440389401c100c119489040003800d44922000041c2961140c10072600c9400007400c081c96a600d40b00a1181c81d4110311000740d4103018044c5e100c0e03144035042090714007d1407082c02c00305580c10000c0d460001503034170b80e0b4070700d04101c81049510050380351100c4012915449562070001540d490b42014146162254180d901500f814140888004005218866503104072038600000308414415214480c841030304 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 62300218 1250 62298968 62298979
    0xf06170a050a0605100305070f080c01090602060105010807090b031006140408070b09031f0207110901050303071209050d1b0902040302010818010603060203041209141503180102070506160806 84
    0x150382c000350a6070071094004040540140fa80c4e0b840c0d9481c9800c19240342c1201000c6e0000c2c0004002e01001000050f0001e1420b00700720410f281800d03002502d400050003070341d0501c50340ca00818aa14801c7c1c0200c0000d00510300c055869003841c4025400200342d912440d000512441e20480b424030004d81107a003126044001042d100d454168a00e216410032101700381d060045110a200801451800f121300940480d0300598500c81480c0200001c503d007814540540507580040c8842c1d18000115904990840c0d60510315180343c2c0c800300c5e881e4020707810403030b002130a140c0104e0400404c90044032101130496101294241c40d00601070490089201c00307800600610082590b0300d04d80c105810b4900c101c20004614961241c072034606a0380107480442d210220505010061039104600d000540300300010400c0001a55000644c44090704605600d0740f080040414401000000118002d0314000001e54035070300141441030312110300301c42c0c16840c042b400342d0f02c2c0840d501c103030a0341380b040100a00c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 62301468 1250 62300218 62300233
    0x11120d02071205010b0406030c061e09051e1009050103050109020906030612010b06071104050a05090d050901090302090a0207031209050a0303050411090103060b13020f0703210f06170a05 82
    0x10b030031040b5100140250b40b15562200304421949850040d8406540148a2040754618049000300300144d10040c4e964540c09011250443c15804001401120400c0382d411110001003141d41115442030011340c0d620400d01a0b80c001d00036000824181251400d88080043c0e80c0c2e00c511000070391182440741e95019004000040952900ea101380d1450341c1c100000140c01110540401d055503c2030714140d609202c00481005140352038082c0950101c03a141c000e004905109150666400d65540300001380440841d2920060744100081c00085030000c000708128185108080025888004142c00156070501954000e64003406050387c420781c400700501340b0440d42e8804400402c0058021145c2c0001a09000c1c02c60f511000325602a5014410001e0000d001e44100440f0081504400040c9401407285510340464076094480503134050501480c5804034034103c400a008030300960a00c2d0b0f1a045613440350700510383c02401a54100080d55000c01c007551070440c1c6e5241900320041c81c0c0c1d80000c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 62302718 1250 62301468 62301479
    0x9030b07050705100609020405040b030309031b030f01020f0c0f060f0a050703060e04030f090906030213050a0204120804050a050a0b03070e1207090506040c0503100909110d11120d0207 81
    0x10002c21a00703001d00d00391240740b10010700c1041075074500c2d403000d2070854022800380300d2490f00388115461032000b203004615102c0c0c180b000c81c1d100c43e0340c282e0100c000d01d000079260f00d0319141808003103103d0700740100031581c1d068039152400702ca402014101d03202d8411020703208512980040c515001d180100744012007582e0310341406010b4100101500e0805407030301d000140251742c501d00c082c0114402d0b12a0350010746e01800c000d000100c1548440300860600f10700300096159010114141c860008003c0b403036a0b98031a8a0f4064842c5600082103400700300038600920a28102901c2501c00c100d545040080c0e4803420000c10002600a845141e0b1080010803c02ca005548401d4032800191480501c01c58607a411030501e001a400850782540b1101005001d20f014450510814050300303101d030550420300c0711151500024050420300564a692140c144031700440c04c1c081d120340042c00800300c0c805034508000510310030290039005010303060801e0f409080c0414010180700c580d034002d003941ca2900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 62303968 1250 62302718 62302727
    0x9060b0d05031b0106031e051c0c030e030106051903060f020405090c030402040617030c1005040807080c010f02160209160503130f060606081b040303080f04081204030e03010c09030b07 81
    0x70343c0342420f941d83c0303120000003d6010440c0d14580501503d01503841203050810900b045003030302160301e180c42c08000d4540541c1d04410003402c85038052400c00252942400460b00602e456045070b41c1c441000d201c20240705c80c40040404c1070341e110300c0c0b060201c401c07843c0c180801e90107280102d9600c145044001b6144801260103107a20a00040010070025074511446162a03100748002c0400d8000042c60151489c0c100200c0000386184503042100b4540780c0c8468003103010314a0b00400030f00c00008c80042c84c4800f5005000226021842190b550084181c1c002d031284510700c0481c0110034030300000d2404034411030494988c98468481e0792565036403008650620421880845606401070300c000082001807144601518080e00c0c0c006032400c0c40416140d03001503100c000035049500b00000c3c000280c0c09054940c001000707048001c043d8860349050300d624055000c900a1140745030040106040d0311094104028009170020030140010f208100c510114034080030f040b41d41810085007060784103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 62305218 1250 62303968 62304007
    0x10501080a09020405010e0610020609070302280b0909060303090d02040203061216080610120b0a060b120a05010b0f03060616050d0306030506070306032004020405060a0309060b0d0503 81
    0x141c00a41c807000c580c00503040341c20070382101c685499224108002c5003050011003e03c42040d0000304050700e0400f001c5ca60351307121400300a0203030b07280114450b10240d41d5545c01d8903452402c602d0510b40c40e102e0741c2048154200381c41c00c42c0702e500c0c2d4402144c1c160402008489440700042c08481c1050010740074000a540301403e101e4000005103054408500f003400b600f5800b84c03041d01d00c92601c40c54800018a0809d010700019482a06c800d001c0280080482654076050b500c1140c07505182c1e80c4008400c0106565445900d0360301c000540c000031410b40800042c854444410100301c180d0f01c4071500c10160260b43d8442c1a034103010008904189410405411681c90864250612211a0382c0e5142400088424180403c0c3c5801d414410400d090000701c5c0e00000b585000c0110a2440c1c8030f041c0d86140c11403089801c7c144c441110a0651900c0d0100c40241c00d000e070251f9956582200018010007036280250b0304245440000300740d500c0c020020380e80b5240c0040085007403e08004100e9441c100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 62306468 1250 62305218 62305231
    0x30c05041a0d06081212070c080408011506020303100605090f150a03050a02090105040e04050a050d0e010e040902090408030703090b150f090f13052506120e030301050108 75
    0x1040c4800610324016880103601e42000511103030b1a180d0b41040d14068402e0b42d000740103603402c002c11340340441000d1010b0301c00754071142150041903103030864203860543c14410b014000000000300400c0310a01500640c415202266500f482c03030b81c2d42c030812612400155215600b9400045c000c02042d0300c01d2014002601006102142024505000433011051244a4092200c011504240560301072040070f6120392010001e600c2c1c00c02210000340700380b155010300d524048441c8082010b0210030000382080c81d41c004200c5000d190b640c20007070000c0700030143c00360000341d103074510303441500b428015803101c180c1c050661443ca41b101d5441d0003403604001c0c40d1200f0590384813000ba02040034580c1c0c260042c010b02a5030070880d102c0c01c042c421101c13640b000d00c5000e05081000e000c803034150350084030780c05043c568160001c0071080c074040e800c0100d07400b981c0c0d241c2c0f003014148804901c0825041021210a03880782c14100010240300001d4540c100c1010b2070b190030a000406c0103502070001190b00c800d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 62307718 1250 62306468 62306477
    0x2030901050f0f0c010b2803080a020f0d0806030706110601060f020a0c0b070b0a09050c04050c090406090606090609080601050d020d0f030806090a02160813050a030305070c0e06030c01030c 83
    0x1801d80c040e080740f0740c01c1105040416034642002d120141803610205402e20390304110a12050226403008046503000c0c070000740307038000004410f21208d1007806442c954482c4442a00c000c0c078051080204900420b60303000307110740200c10000038403902841944070b078561940c010f440568a041d5080c2e4048001c600882d0541c020080d2001c001200c0000c0b4101600c000c9604e251900514280b16100c134030014029501e040c0340c84808000710710000350034070700700508440c0800c960f928030107440028042c402d40660000d061030300100704507045030001400ea840641c0c50943d11135030b880303003160603000c41d200e4861607810600040c44a800d12480e110205c500142c0500e104000981d1006034030403501c0800d4000464950900645d4a001c0a80c13a030404070030700c0709605104110260182c5883c01e4040100000b4001410b00091042c3c02151402020000c1c50507c10ba07549040140c91980481030480799140c10307002c01b0901c551403000090082c0405002040c3d807082803030041d4000d29081d255a0b0a20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 62308968 1250 62307718 62307727
    0x90f0711030301030b0405102a02010b1305090c102012040303020f06070207060212090d020405130605060303160813090213030302010b03010203040b0718180c17040302030901050f 79
    0x2003007000194000c5101d00500040d0346024100f0600b03100d14102c1c01210340f030030405d905407554200e8540301942d485c030340b51010320500b2814081c1d005001c00002c00c2d41140700b1389141e00c4611907661001d44541c0041090f961f04c8088682001411000b41003008080350390125482c1c0c10459219035010102804c1046034039070702c11842260480d400c00d510444c0143c1c03144000f00c3e00004140310700cd40054460005100703980c10500080d440f485030700d8002c46410b40115618141e65030702c500c005002a0080c00411013400c0c2600c651884203000c6c941900c40c1c0b800c140204109003400030440300240c868105441e620310450351250010740c4850701c1500c04801844011a404500f4401010480382c0c8440b5030008a165180190030741c0d0310107509511070b900c140704100200345406281544001ca620b04100c2e80d440c00d044400c40400369030403410041030580d0405511501076840801800000d407100700c071280900c0120803c151003160002c0060b0400c3c418000a54020f10290801543c1d54003d241030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 62310218 1250 62308968 62308997
    0x30c0904050a06080f0d02100e120c03030403090b0712030b03010e070816080102040312030207080c060a1e02030601090302040b0a05031902040509060c160201030e1920090f07 77
    0x940d002a501c0c0d80b00159900030070071200c042044a820200303412401b41156024046002e502d07948040c401c3c03100d4540b00d014820074050144a01c04e0b005070300003106ca4940310540401950380d04115000c03000710f02c2003040850003020100030f079080340d0341c0034400804d45122008101c002d004220005a015034942140503007100c07090007050050a050401081002d44807030148038109400e0f40444541e910411062000c00ca420007011008c00c402d042c0540d171011185090002446418240e0603280100c83c00d0200b90101a04104141d10b0271100c1c0d0361854105020fa00304030712041e200c1502191200c4000c00041c00c064111500e11a8010082a40295240040380c2840548100b904401c54404012811494284035150b000021000145020b1400c00540f00141c465522030f1005100c401c90f02004580c400d0300401d00c1c42c150402038641c641c802d00151410000754840072070311080d13251100c940c0405080d0852000c044e0045c40340c0c0d400c0e01c6d458132090240038040d06120030090b848005291 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 62311468 1250 62310218 62310221
    0x150a0c0c0e090109060b01030902060306090618070807021209010c12050c01020a030b120109050601060804021302160c170312060a051503090114040b070f030605031009030207050607080f030c0904 86
    0x40b607102c1c4000403c40c1c071035131319040c0201d50000700c1c05030505281c04241005610b1b0003040d40c2e40f1100903210111642c030742c0e000040c00b0900380305c0304103080d0b040c0804020364546d001350124046c0e03100c3c1d02203900704104050580841e0044032919030001d45032000c0702021030000d20448020b40700303d0070400c0ca800d400800440c01e81c0d0101d1a6100480c0d110003661800d81814401d108020303d00d0b10080060400c559100e544410381849000200b10014010400f035581c0c82403944421001050f0840d47c0c0d0b6007043c4002805207441d4829290013a002c030740007030305105101c02092883d40c07910285192000c2c0441d079554007000945195080000d83c8000306803501c1310107081c4021082c3c805d503282c492800b0044a82904c08540d00042810350440501000803009880503400c40058144010f2403081224218010291a40501e6040c8280080c480142c2110340c080010b050290b42680d46141d142d41c14000703280320b45840101042410007a94500303900e00000365400000c8000c0c02443c01512200003070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 62312718 1250 62311468 62311471
    0x20604121a0606030c0f090a09060312030c0801050d08040801020a090512010c0c150f090b010501020d020c030703080c0f0d030203150d0f14070503070b0d0605150a0c0c0e 75
    0xc00034502080040140070201072180c8041c0c00003900d0001520380140402d1681c00058128592503002260300c2003c460b01c501038031035000c006845080d4440d62207071244050f100c07500c0b041d0340d901c1c843c1c440d86401034880e00034585134110030b440d000c0181c0d1a0100307000e0400e100c0c65090701c5c0c812042c080840c05101c00c1c002003081040690301c01d4002ea08100400224481c0c40c40d40410507031400d44070072007068101060080194101400d03104a58480d4518005881ea07400740d042540d01d13011201041240c0305c155241a40d10030b0342220b03500005540180d944003150601540d056003d04010400a1403200080101910b20310944000500484002d441c0a8031004250b02098001c410040c000040c0d44042d001071200b02c580812102c0282c4903000f907001c44000241215140824128070aa0304025510003840080c048801c44cc0e5141220307096500900c0424403040c5c2071643c0021070785002d15090f40301d05c1220300410701d4101030f44e170b040c0c460082460381190340008805000440b260580c4800c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 62313968 1250 62312718 62312729
    0xe01153504080c07050105040303080a050406020702040c02010e010c0e010e0909010207050601060207050102240f060402130b0715050903041203030b060a02100c14160c080303040503190915030b0409020604 90
    0x43d8440d6059440316062041540085041180030b00c42000800d0703000451a40203c42041d00166a880318101100688100d51010350044d003441c0f85034900c0d0758154080c40e001c1107410006c1012149081c4211991038560212034002452a03590400c54600000080c0d00203840d54001031400d0307a50f80e109410311009a0200001d83c101c10001c000c43c3d6010300241c508842e2a400600c000c210010420181050150032250510004400681741c0d40f9603604032400310a24030078050f80c940c1ea401c0340040780c2d0310004d003c48621005140016080400e400307042c0c06600620003035410242030030b005880198004000707070101a16035118440e180c503250000d0a0b1115154081c107c02ca000a20a80544405e54014400c11600301e010b11180d0110074240c0b00d66034810065843d50403c076051208041070744d0703000040540800402d1000b0450300000400c5003000202044460031702180d410307580812507100383d05e24bc0c032660f039054101e51312036803019280f458001c0c4006120b807040d4010400fa0382140c0c010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 62315218 1250 62313968 62313983
    0x80a18050d091512022a071e080604140c0a0612150602030f0c1f0902030708010c020a03030903180803130e09070603050606041706010e01153504 64
    0x154600194440c0c2c075031010f0110289980401c80a0f40c0b4020010000090a543c074150701288078100d01344601040400800d80c1c0d003004268622a00295898802e1442294069504900c021b0451450b26030084102c580c00000f51085681300d03184c1040c840c00780003610000707000b0004c0840c0159100c3c090703a030182103681c0c1c480c000542482503a07404c5034108031500071034440c00340e000c0103640e42c00000ca4184500c600c4031192180b16107400c1c185007002d0001d10841a102074140464000c40c203510035140580207c0c21140f80d41c1d0740d20000d80c00c0752207880300c100050308100e01600220340a5003010202d244240741c1040815100d0700070985003440c41d04000d5850f0400200000202410345440300a003d41149140080c1440b43c103103662025075104003000d16417903000040086d0f03030f50b0b4182c41c01020031100c00b07560400d80040582c0c0b984000d002d00c0c01d0354280d41e0004200b010001c0172490300b1807501d0f29458490b141d44000300e640251901401c0c0b001c2c041812000f4448681c40d104540141d108096 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 62316468 1250 62315218 62315233
    0x20105060f04020315100203040f0b070c0f080a062a03090201020d030b090a0e0304080703060204081506180604020f120105040b03060601021b030c18070206010e010b0901080a1805 79
    0x4101c60022a2071950344a41d0041c0705001010606850700388420800700d459820012201d6020713070540c06994005108400010b0002490b031544800801d100c0d441005035085940d00d4128200d04035405000f41ca500c1c4d440058640d00091555000c10501c2c02c613244005c03041d500c0b000d40d40140e500500c64007000079403685003280855804010360311211981e41400d001c5160a18040381e00c3d00700013001820280d845d607a00100c444001e00480700502254415199090348a0500c10301941c814819181584114501030040000d941070b8240140ba0081000c14450f543d0f0307a0750041014041c100541c059804c1104d5a0f49021244c0204114000700c01e02c082075602d4901007000716001601444d000342c1181003002042e0fa0702085200c0007500e11f412015291041c44003203407419869010407900a8041c0107204c14180c0c8841c00f1030f00c104c0081c1e00700c0c2e90310780e02c1c4d84411190980078410515403c40521580015600458401e5400400c40000051602450301990310243e04403105907500c1e0040c14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 62317718 1250 62316468 62316481
    0x8010b010908030405010c0809210303040302120405011b061103010609050406080127030201180c1401020a1509050c061602210c04090f0c06020609070911030a05070909020307020105 80
    0x2010308002c1c80310388051810a4176000001c3e2100d441154010070351400020794a2099a9070a002e600c03401550041503d0803500c1c0380b0341c1d5a030764820389043c4c016200e8443ca8030721102d5000c04440c1070b200d041e910700e903d943e4040b0f0314040c8403c1340c041c02c807065501c0d10302045889004002460081c040c542d00c0d07a00f0b030f92412050004440c1e00c1d420504499040416403452003940b0420045802010030014401c3d107590f007022401410a01c100c40300031070048645005100c1d4a05002c0301b80c46800c450b803104030340341c4070040e0b0b41c541c280ca0004044048100912405d01d50f0341d0b0144207454019820f540d224240c85c4005415a800044981b144072011255102941012041c20319015003e0803112250f4140d0b0b0640345e83e549460038071901c01c42c1c03a103a801c01000b0924849100840d0301c0900340e50400d44509000c0d448000488030000540b04000c0700084202181c090038840001c100102c40c80c40e100c0141240c0504002008081070101403076000a0b00f001910003540700300303401c7c0c2c0001451f083c00d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 62318968 1250 62317718 62317727
    0x71a07020a060e030a1202040f1205030f040306141f0b1b0703150506090709050607020a150806010305070509010903060b04110a0f0f2a14070e060306011a120405070f08010b01 77
    0x4940e0380112503c14002402074424180c0850103403401c2c102b500445100600d8441c1c554450107511004801000c100041003110350b411000310714009844171081590303140b415600301d1044580142a035815841e00700410610703140203000c51056021400103d1801c1014140380116603482114907140303003400b000c0c207040f0034803d5940000d01220484118142600000d10020a600520341304010006c3c9400071542c0d0285418020507216109242141d04950094401c4808862190100c0e0800d0009404144154102d845100b4140c5500c2c01307040c110b4075582d0090070001940d0707070441d69411000c0c10040b1920302802001400c1d90311015200d22102009025440030b21400e410301c08010403000301c00310f980650140c8802001c0b000300b2030007840e050541417070411a007118030501801c0303404034041141c0e0310784610841064003154001d90740c40d000d500d10240c07480080c0c1c283d4802800907410840c208200b280d0400d0080040f940d200e501ca00088060030a1b590007046541c0d501c070010f04142d41c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 62320218 1250 62318968 62318987
    0xf01050109021c0c031e0f05070816030203040203190f050705060301060507150908040807051e060301030f03120212060102010b010309050705040903050c0a0f0201080c071a07020a060e030a 83
    0x80120039424150102d02d40b02c03030b0f07050142c031a18140e07807220489441c80e4441d078010000c0d410800065420143d400b210f9500402e4641440c0c0c00d041d0522001401880c028013000303009400000c1034005051500c54224025003025200301d0b031600645042c220300415079075a8001160082a402100d0f08044c0b502510b40a0941d2000f80605000d00040004070b401200341c5107483d800c00d6a90310401202c0b484000202004900100119030100b00070031091030005000d030580743c060311004103402d50503400c1c0710a400f03200405a40080c0810040c000200c0201028810510905148207140c1170b50980c0010b0343c100b074161480440c100400c10899681c24020900079910070308003041202d043c1c1d1105a141d4185003c1d1501681e1620042d034205031283c0203d034190804801a5130452900d49007001252050040a9001030f29010204443e48058011030342c1041d80841d601308224800d901110341814000d00c0d00040d805802c0c03885000c1501070154180406078100030b5595803c5881000e0075502e80c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 62321468 1250 62320218 62320229
    0x209030d0305040f0201050c010b0a0303050903010c0206040b01140d0510050609010b0a0909200d020304050c013b0319020a0f06050f030604021c050f01050607031d120f0f010501 78
    0x2c100602002c074081c29440a2484d03020b20303101d82c0e28a004503030107001d4034100030020780008a0b05400010301d9030000c05052003940032402172200314000c01080ba5942d00540f006072040d1a0074004200007070780d078a521001c5940117010418213110503100c00d81048084d00d4102d02458881c4204070180c6441040a8007401d001c292250030109080e03401000c1c802180181c0c4c03030540d81d07440d14040707040b04214444400640c0707800c1c00d40d81702c00b40300c1d807400039400c1510100c2c2d02d4841c21646602070740c0545801d4142c1e4000114151440f00707501056004001c03140c41c0341e103000c1000c12001040d5241030001040c90380d20103640342c58040c21803042c4450b10311140e2054040c906060b00174400550302000b240c45241d07000710383c1601c0740c035080002402485601c640302c1103a09075840c0c000300c070801908224811445144e4020304c0f6aa5a814040544190340e401000910440c135842e008040c2030620b0040b90300d02800c0700d80c03581c1030044114903107821041c240c1041c0d48000c2c00c4804a4800b4000c83d4054003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 62322718 1250 62321468 62321471
    0x60804150506121029010518060904020705030309060703050709030f150509070602160303080606130e0109140a0209010206010522110702010e0f0a120f02060408010209030d03 77
    0x1505885022403080c01108103091140c070703400030480b55a62240c5050750f010b004801d44006a25140500000701100000c940c595000b08059600e42070407605680d00c100703410b0b114249069804007034261040440c1d0911940300c0805d10294459455501c00f40034020b100d5801555039042c0f82c003855140450042413001011300b4441003000701a0300947e010200c9501c030002205400140c42c1008014034040e400d0b201a516050801080550000e45081105c3d22a000c1d20030880c030000b89810610401d00001c0c022420713150205400b030078036200805940b5140c100c9071100e80e444400c00c13042900280d0044c5222500d50507950b008100d1400e04941140882800310310385550040042d4417000140f2600d4858403941c1d140e03440000c072101c5881207441007072400f0040c290b100b00f02116140c100b00016030001d01c103001e43d281281000030500f01041c03001040705030901d02e464206888040207002c2181d41a03000b409003001600d9480280001d00b160f0400035854465040915141c8440902c0c000e0800d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 62323968 1250 62322718 62322721
    0x301060b040504090204060b0d021b0c01170604020903010c020106140901080c0f030a0b040c060e060310090c050403050a0b0406050603030a1409120d08060405180c1212030c0d05010608 81
    0x2a4840c1040350300b1907100b6140480c0d98001070002500810460b4488104d801000819100c403016507401802441c01c83d42a8141d804044107800759070b4000b0350300c603a01055411310035064400000200703c2e80124001c2000d40341c5820714011a003074486130b43c450390140c3e46030b035000c1c170111140c540642004d0005a562512661501582c0d03662900b0460081d4050708116400075900d4409010700303503030107401c04c91000c0b8a007850310385010f002d21035110b0342001452150b500d5a2510f00a0101c80c003a082d1104032805403400e0420304130080035082d406005100040100000050041c8880d000660052410740340c10f240c903040038015690028400c503c0303604204080b103070a60300041075003000310300c155440c0d0320340e03008070040340e03010600c86d400da1241d104512150005d650311170b80c0c041c03241070240c400f44016102c2c0e007004140c82800c0c1c0240301c000e411401c0d1814160401b000044500440c240803184404001c0075402c1059105848001041c000040c4514a104203400f616006101074a0321b040203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 62325218 1250 62323968 62323979
    0x30c0e010e0303160501020f03040b040c06110c01080c0910050d0c09051e0a2301030b010e01020c06070c0308040b04032a062d05090405090c030d110f03070c0302010806030106 77
    0x8910543c803400d42c0013215440325109025095068907241e0714140c1605942e410181010f40c0000001c48007103079411400040892154803e40c040c0690100750030050110b01c40202c010349080f1801003844c000304c9024012680745076241d80b0418100740950f29601d560303c41000350b0304192424041428188489104100201d442c2c05801c1a0340b0f8803c2c0020b1043c18421000241d440e44080d070004090850982480700d100d0705050203005e540a007603d04019410b641c0c4015291038118048481c05a00300005100e00c45c01c0c1000140403841c8514940012543c83e90b440c90780642140e00409072407100400c043c0304200340507003c43c10303003400c894000900340464540201e0b5803400d80101d10412504810707140c1f04002e000100da11210401501548442103090700410f190040c0144910940c100404107283c0300010400d4800800090042d24000282007800d031001c0380720f0401340001d03110701c9846c2c401c0c402d4280301500b0300d14400d0701100060f520714000100781c20000b825a0384280d1500408221 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 62326468 1250 62325218 62325223
    0x30106020d050d02040906032f09070c06020708070b061507080a030b0607020d050606130e0304121a070e0907031503110d0c0b03090f03040e0c28030c0e010e03 70
    0xe000641e454400e42d9840140c120300043e01940e8401d0808034203005000c000c0040c9540d44000124480c41071b03c154080c604002c480e4019070480d400d4101d620301c00071502c0c007486140c01e04c0c101c601825001d482d000090fa190070741075120175800c0e40d084500801740500380c41e040d003049030394032030008404c2d04069a5403205040361060441050074140e80e10940182512144155140c07280c004004c07400300c24150a006446c2d00d8100c44462140491200c2048405914814441d101008200540c2001d0501c0b002d9044881120815540c00f11003420049071040c000b4040b40c0b14904030b558003500340b41820280444242c015005500f0b040c149100c4a80d0707208292034040480350071200e248488021040450f1070520081000750002d0101c110110b41c0d444c854000b98000c1d600b00c2c00b100d049515903c0c1b400e0712400317940a03900c1032010140c082200900414007070880c502d4002031503108455a80210301e00b80c41405c495034042a1100d41711162282c1210300d06803404000e0802141c6201c0c9203000a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 62327718 1250 62326468 62326483
    0xa0803070e1201090c0911040b030c0a0e0909010c0806010531091508100522051606030f0c0306080d050c0c19030b06010509060403121106180f0303010602 68
    0x1410401460035001e200d03681c034001c51880c5420100204032190b103030f0500003424283c5001c4d464605082c601040e41d2603030f1640448085514501910b41985c0300d09070a28110390040f0700103020010001800d030401d81c1c814a50502a1100800005052050b1540a0000c1c0c3c402000203052000034032494520010213480c00c848940644564003800305103408281100805421001c0c0c1c036840d02224140320040c640723080c1c0c1a20015001c41d07800a194030b1040003900d4007156075100d0580cac070055101a6100701466880007a01c5441541e907621080d03010340d030b405407071a0300010000303455121001c1100c001d881200d15040d01443c0034020181450403055440c802010000100013000070001c801c1d00e024026054802001800d03901d070004aaa1a034440fa10035000556140c0d50b807102180c0d2660041040751a1343c80090725403030402c2e16580345c104040c015031071002d05021006440c64014141408603d204d6141002d07210500c100c01440a494101c54441d040c10a034400c0005210f40342d000203280 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 62328968 1250 62327718 62327731
    0x2190e04110a0f020a05030d0603051006032402070602030a0203150a0501140a02010b04050103030f11010606020604030e01030b0409031809020403021513171e010504030e190e010308040807080a0803 87
    0x1885032520f42d0407490a480484060039600000c291101224078582021040321f01a20803110000c6801c0365000481d00c1a2200030140313042d80d0612480105880009403205c2103243e00141089419241c88050781c3c011500c580307410b46d00000b044001c89241d04450b0240d401511008002802c21001902c0700c600398003240800400400d02240d041e03c00d40000c036003c00050814810f80d43d40b850050b10001501c150040812040e41021119020502c900001c44800750f00404054490380c806443c0d80c0c0d0641c01d000c1c1010b4540441111070b880d02d00902c2c881c0b521a95030004081140c0c80c51000e00d5001d904002151801080100050b030b54101c0017041d00c0100d2101e45d541c0c0c03413112915014000150b408840e6000503106030910b03946012401041845550015010f00310400004c00d0880d0f07001c0701c000b4003043c510101c51000b400c000c100c609070880100014004640c54007003265994500b40d00071500160001424010080c041c0203400041c075000000349800748c090340d90240e040c0070040c5403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 62330218 1250 62328968 62328977
    0xf050a0905090a060f030c0303031d12030402040212130c06020a030206060402030a0b03060f06010305100506030a090c0f080f0709020f18060702090901020a020c01050a02070e0c070602190e04110a 86
    0x11602d210342603441075000f0401007641c200f003680e8031f01c1d1018a1030028030080d40802e1130040d00182c40c0706035005002034900d02c400034040951260341041495080034000b640c1180d0b00b81310b00884c0b001440c486500480c1c0c071107280100c2603030614081d900f2102a4200c1c104540040c0c5598001070780000d103407604038400301c0700561a66104e906801c000e10000c06000c0e850f10404091000c01c40444019900803402a80e0902181d0f40e001003500300003c1510405d80c00010402c0011a030b0b501c3c55101440d100c2c4610380d45d00c0c0490303864100c101c0f40503240e00412401e401000c0403070000c0104006090080c0000307442542131014040071011035000361000c0100c0d958500e50100040e59502e4200c6454950040c80d1501504000308924000d40003403e05101500c03034014903450643c0190181c6285003203e500030081d16040c0342e04d4141c000e1002e004014205c80500800c1c000405500160282c405054620700d03001c3c0c00d11034010500401c030420140102c0c0340c0310301030140c80350090031120080d203203082 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 62331468 1250 62330218 62330221
    0xc070504021b030a2303010b070201050309010e1f1505010507080c0c060423030f0c01030b120607050c060121060207031209061d01021c090201090e04060c0f050a090509 74
    0x210a000c08211964200c0030f0000041e40c0300c031240c2003480e030130120b440a00c3c0130169040040341850244828091500f0301c081c01d022170001503100b00001c40e403101240b0700204028005100080c50510080740a040002c0b20300420f02031440c052240b41e444800c000d2090340c0d014900310001c0c1013031140c1c40f000317001c1d2000002c15040960041180000450707010340560350315030fa0740c00429000002136518480c124195a0080043d141c00107985130041e0790040a01000e80f4100010740041c080002c80640240030003415a030107540c140502441100d042d01c0ea07994070400d50000703500307106050300294203041d040c00740c3c806c441c95070140603002c150317000c10016514000b9040c15501d20311601d20500c071140c10141c1003420030281760411003814a608c45840040d109a84a180c240c3c007607184900d10b5a4050b640c00001e201c03042d0462445c4900605120b04e20944682e0303241200078013100c0959500d5100c0c00b40c000d64a030712801d07a6912005524085041c07919100c00108201d03018424944035440500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 62332718 1250 62331468 62331487
    0x230310050616200a05040c080a0b150301031209120309061d0316140a0b0f0306010306170105010812030402010203071401180f0b0c0310030f0305070804080a12050c07050402 76
    0xc54a2690580041080e0514451042000e0340080c40c1d040d41c500400010300c0001c2c9071b0415005e840d0700e1a0007a100e42c0510703691840074100601044000d180d010307200d92211028845014005c45c00307140540025500044403400141c00d51506900000122920101da140840e074441d6180080e200c162800080b804000000c8040c1d519000403001c0d81402010319a4960304006030b0001d00b02d0b8105010860071a03100000c002d1505074a100301c01c05240b040065511001e41f0700c0c02036612010504000481948540407601c0703081b082a40001540e65480c010310201208210310984079031025500391071071919500003512070003034200080c03d2041c2460701d0340c0b1034030703080d042000650344150b00d8040d480e4560034000070241e81100c0a490310302c101d07000704100f010310074212171055140f000028041d0349560b6800c0d00e1520003400c2a810408140030440006180d00001e100502e800c400801c0c0c035030a85d0420b01c13202c14440c0500700c14060b00300407034248071001013100c1088a0b000c035001600c654440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 62333968 1250 62332718 62332747
    0xc050304050913210504090902030a0501060303081b04150c02040605030d0c031106070e1507020402070804081504030905011103130b040f06090f2105060103032303100506 75
    0xa4011551140d404403c114840e494042d50000882c01001014022110004c2110800c04114007010014038204001d2000b414142c1007403030313410702c0601260042045038841e00c5c210348045c1c1080f40001c041030240030841800140320100800908010751400385021b4000505641500e80a01844512500a070030f550340d66008100410b00030b800d40740d0003801d8910040c018001e610048010411000e504413188a001072007074450103060701d600c0c491020380c004110300301c1c4401038800c00500c001c2091200689403070002c0c00d80e403032246004544803800c1021140c14030681d44040a200340c410340801010030760010703240f070458500b801c0a00003c0c40010a03142180b040071800852102c041c0000104405180010012a40c80503880355020381c030303032004072040071031403054408401c1100028400010b11601c82c6c40c1d00d088034002c0b560301450640e109400c11100b64400c4d00810224900d550a207400c042c3e440e251000703100c40c05491751070000800541458940105030145901180c1006200080e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 62335218 1250 62333968 62333977
    0x70911070b0114040c09030b0606030405030c011e0501060305150609010c0503270303030c03160915210b06030115031107060501060e0103290406120c03060509060c0a0c0503 76
    0x405965903442da120081003100d809040e418a0003985064500d60015205517000b0301070740d0b13000551052503221b80d02004100d40000e00117803039900040002d1440c1c91003d1160a044048149001c807071401c6000c01c0508a4005034041024941031000b000a003820782d4501c0c0c1c500550803203919484000b140700407038443c40d0820005006210002c0ea0000c41c0520124522095811024000324001c40105054503400143d501e0060008144003040b10045200c81c410403c0b21503180c0b00032002c0ea18041500002d24451012000c078071452024007011145600c030b0501a0384000040c07001c1102d50021800e41d200c1440748484d0084c10032003410300c0500c60381203207840c11101c1e100d242d00c0e5078076420850001c107000c0c860a404654210b0620009500030f0207608070541c0070441601c01d02492141595869080c1d0112580c40341d9100e20100d43c105901c100064010b00071000004041d040d894010300305c40c005460190749501c44010000d03580249130444a42c00418500180c02004924199245014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 62336468 1250 62335218 62335223
    0x901030e030d060605071103030c03070b041a011701051005030a031202040b041d06010206130b04050c06040801020c070506090907050714070b0307030c0f08070e0307090c0305061806010207091107 86
    0x803d8800a52241e100d40a03054070b44c090807540c040e000b9000101544e13441582d0300c10400d138000340005000703c2d00d4000582d51281c082d2041e088402070002c06406480b00980041c01072140070b05c01d1031807401c403d110f6682d1042001c1c005022445c1400c00080e40e0300201b500083c204150120f4000c07400341190162f400420b160b0f42c40c00c2e10b031b83d101d145440f00c03150380c40510800d0b07168400000340c080d1320005103a4050311107a28810821b403e02e4641c20b002e0a0001c10a552130b110310300d806a05501c03150000d00040c01f101c400140c9490104444d42d05020700340e4012840fa40c403d00c1180129640e085520380c20608604090307a80f58032030320f40b114160000503142a00742c0142c031710014428008400442c401c1110386c5e01000700804108050304d0040340c0c0c803c0b0b200004d15130000141400c3c002c2a1120760428002e040b1030342203549600c02401e0710764030026140082d884506002c45801d00301420000482d4dd946000300c64908000001d591f00030900c00d2036180d2743c841c0001c0680e034a030a0f085442454 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 62337718 1250 62336468 62336471
    0xe1203061005040e0103030201020a080a0b0901090e011409011a0306040206030106031d030d0c0f031803030b0301020d050901140601020708100203131b030b0901140a0203060105042106051b0901030e030d 89
    0x44e50307400c02034003e4008203c0080405c1c2c201c000900059900cec4104508107800915078140d40e4282007131032005058150026040d0343d40d541040d01c4034074440e0120b0b481001d2010000c10448900519005240605000203010f6440b071800e200c01652440c06583c151222458006420540c0f4800c111411803c0c003040320003400000340c0d4988005503904201d40780402511540c40302c03a00800700724129580840c566007048108099800003c0c8603070401c419a43d0010000741c1403c0c040001001140c000b640c6401042e0340d209081e000712015842000c0d8001401d0020704207841ca0050300640315102d1016220780d03e5030000c0081c500c54001440f8400d42d41d00090b452030074103000c082c00507030700e00d031030005849040d00c69001814040050083c074069034880c00040d51203171038003904a406900040c25141c1031080034403010505280384c4c0107000d131040c01e014002c4c5089405040440840e100a029041a65408800a0100f00008017280c003411020720b00060601d4130903c425003113010700680d541d000ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 62338968 1250 62337718 62337721
    0xb090109140f0606010e0f040507032408010c08060603070305070c060e060a050c0c03180a05060309210a0806010f11030a0c0606090608060f040503040803120403030e1203061005040e 80
    0x34001400c4090101c41c2d108807070454070f40000554540303000501c59544015000b40040c01810705400c000d40081942c103011412004494510a1044003d09044905100314008000c0160700340a506e403064900d040019036400c1c0800440c071588030041c001420306031518041075a82c2e05c64040074152384e402070030810400c030310580c0c001d0f100c95054494511940c14200480d4140d1200d004540780598a200114903082190300e000c038a20f400b00b4042e90b446a0b10280000301c90b29040011072007140ca00c4040e041d40c5260052581c100030540c0b180c2000120244420584590001001c3e0b400c080e090a000c003007041122412a003810410070301c075030140400320350414400e03045a8402000d512401e0140215034842e0441c1303089407003d11800003154010b0000c6822180c1c055880c503007141c02041600e14080d01d41c13040b1803559000d00380c0c0442000b046010001031552500c503284940081601600d030b07402c040c22425403140000341c001c0e0301c104c9109405400c8680140d04417001000b007950303490b869 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 62340218 1250 62338968 62339003
    0x1707050312040b1f0611100905071509030507050405190f06060e01170c030603190503070c0519030602030604141503210a0302070303020c0114010503010f0204080a0b090109 76
    0x25906807011500401a540841ca01c505900080803041480b90040c500780e600e081790171a8002041501c00c0058050341450741d00c0b65680d8010617200902a00c020b180e0145400c000046100c051540c1d0001c014550005000140010900000720b41d811034002c10f281d110304070308131050300380907900c1e05c41540f403e590343c1d0150301a80c000004a42064845441010010005690615941e0803403201c1b007c502e400a005000da4801540d000b90015040b1801803030201c8409800c03034140d1406845d19407000c41c06404001c00d5040408c007408065450341140100740c0c5405203a50490f000c01415a078011002840d59220b540c015060865019011155800c214454403605004200002c0c0a07000d21816080d80044000082c0c82c1d00c0b06004046103800c154100450094100d00401c4040640801c07981442d00000d000303010004180034401d01440d45810205803c58800c04401c41466005000400064101060450000f60462198039490b03490104032401400179020040091041d0b0403c40c0c04d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 62341468 1250 62340218 62340247
    0x170405010c020c0612040219030b07021b0a06080406050c1306091403010504050a0308092a010306090e0a080706060512030d0506011d1e090702010b01090902030c0717070503 76
    0x84400540980f403c08022800307001c1d0380d206010b06201e02c0080d450110300182000d030301a4211503480c0700350390b041e1501e907920f401c03200300265103140050340039900d41520145030092407003541400721084194980380c16006000ba03032000b400508040e42d1000000e5881c01d040c02102c001c12105444c075940c4a0704d0f0940900144823034000d010710b540c2401c480c40441d00701407042500498002c8010644d20740c0c55602241e6001e0000c1a0301050700440003c2445a40303034100340c1c1c41a4442c804e0070002d003200e0000050840b405584908861810304000004010740403800809441c5c01c4042c3e20740c0c4455500b4581c4c0640000d5000c1c542005801000007007010002c00502805500444140080d40720f400c011920300b03034500d1290b031818900c00c581c01000d1400c6000d0303801042e01c0c1e1081402c2e21800d2000581058021138061015035155524100150b9001c1d00a00c050140d92004505606050200d41c0035405450402403040c1100d4403c4801141058203540c03880b41c0c4030b0308980d0748040407189140c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 62342718 1250 62341468 62341481
    0x20a0c0c06030606090b0c070b160807030309050c0405010b0904090305040506030a02031014030d050a0c0c06020d030e1b0409020307030501050406060e010602011406060a09030b0c0a0f05190f17040501 88
    0x170029200410409090012500f009809600400324141800d00340c0301d90368413100c1038450140c00b00c2c40030b47c00250400c0c050192103002ea2030000c1d550f071741d82c104035040803102d140707252103580745c600180001039005d8151074503114140e500082d940c0396441c040c0c1c1c0318480d90f003020341e000c2400f104208014242d070f00194400d14040341085227842c1e98002000400741c50099565040d0807000031100c1c030314421000f8201c5018280740c003a615080c01d0300e560010b0007907a0840300040e000704100c1550311f6054002e5800e03a542120044c82c0c40c0582c4450b03030340c0950f581d000452240d0344581150003590703020003e032005160040005c0225081519004c0300401070380c4120f0782c003080d6403400001d4045c01071141010b560701a401201150f0307600001c1107810b0340094800c1c410f21001d0078000c000700d2511428503203e0a1709000142d510b01951401404038010f01c6040400c02c8010896408010841c1c009861280030605103907050000c00702055618008040c810548034807640c04010920005400c0341 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 62343968 1250 62342718 62342729
    0x3110d02040e070221030114010e0d03020607020f030705061f170609010c050a08041b09020f090906040e0706030c030f09030c030e0108010b090d080904090c08120403030909020a0c0c060306 83
    0x282d80c956032800c1c4040145510340110f0200385c0b4140010001c03032019100310040c0540500d8040c81c883c41000c00906010314031402640141c1c4102c042040d0ba81d0100091b0300c200c0c1e4507000460908244d50759207555124000d0030b00f0f04044101c0311846070010250360200180c040443e00028210f14540340c03a42c2d40740100c0d83e0508940c03c16003540c803d18015800c0314511140c69607020450354a50b169442c400040850150141240050004803845280b004e4006514101d440980d54100300e02000144100509450700c51403820707a6400307840c04002041011507005044c040b5000950b954250300505e551745587c489a820300141d00201580a05407507025440b0380c17580b10980e4070300340044416034424003415904981c00c02c24002c0f2b5240000c1e0092055100301e5007180303000759590204080d0f9080807400c5070400d04401091141c440c041c455a49a0081c0301d540c03d05152464030010403040040c17003800c1c0240c3e0f00080300c2c05032502c107000301e42e012504450402c651656440c4c000b0001c085a1084 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 62345218 1250 62343968 62343973
    0x7050106060c0c0b030c03010608090a02090c04030c0905010f030b09010209030a12030e01051009020f09060d060302091302010c030509010c0f150b0a0b1210090e0714010e01020d03110d02040e0702 86
    0x1080b1800c1c04e8082d82d010301250b9194500b1a03007030100a890104c40540030f89440c0c03117400700400041e1344004100380300304005000d003a100c0d441c40c500b454459000e50018104c0908010044c044404660620310840350810401c0c80151203070804e190080c4582805641c06000c2d5240d0103042c00440c1c0e2a8444800d910ba50801821041c0c0700703c1c07802c851054500112413105c0a904000314500c0790090022440c0403854145005100d40c0028a00d40c0410300e040c0200d500d0344030410640c50050981030788002c0010311040500c0c8254002001d0303201c0001c00806000c401304903440c05074420903c9a01c80c90f40228848403205060400c26240f11a030510100a00c3c101400403850b4101095060b0841c0c1c60482c40504000441461400c0914020180c0e801000b0900000503440000e00a542e05100c502d005452014105044001860401c0000c141803129100e250715032a40d00040d4191024a28a000240c0c40b44c0003540e2081446141050000c09001140206240d051145803501914041d003c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 62346468 1250 62345218 62345243
    0xa0b01050f09100302060a052a07080a050a1b080102030f190b06120403140403060e070b0406080f0403030605100509030d140d0b010504030204020706021306110a030e040207050106060c 81
    0x3084030b8054100d0341c0385440c541d01c0c4030400040c1070440240c81950300506110b0700b000301c401c1880040d581b050400c901c0c800085e041c2440c81d08000d0003840c01814220000c1c026a4080e46c44039983e0b03148008000b000440694151512042403a070601d000d00341101c000e561b01c0c100380c0303c809544842900c052481c4502c1a4544210512a21460401010280003607041403001c12003080c40d280300520030341c1400300c0c50000ca10ba12041d907004002070340c1f0841d000a03500480c404441d241250315080060802070810080c0003164000742981c2e484000c24010250942e214070b42200a00066440389400c042400c00c2c0d085e010340c02001800711210290211441842400421030306440360003850743c0816420803c0d500c03911a5900046804c5806041c51450a82d0f00d50101e4100d074013403081690b01070303404100381415400c541668001000685003c07480000f080c078215894100d5000000c05001c24840a00010346454041d01d2050ba0044000c204507a5150300141c90358000a070111000200b084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 62347718 1250 62346468 62346499
    0x6050a09020d140601020706050c0c1005040f0b040f210204020a05040509060d0b04022b03050a02010e0c01090512010617061b16060b060c010501030804060e0a0e07080709080a0b0105 80
    0x541984604c0d0141d000b030091901c0d000041e00e50f80d1040381c0e110054054048070b04031b203854810884540c01816510b0031742d211300e800b00c40764801c04660440004904100000c111071000d64505000b0369100c1e1201d44111302c8800108d80c5840c2036000029040f90002c039000a1058111026000b181c40a6420080f103071780780b1041007281809044010000c00740387d80800c0141c206224503000c2c003250b0101a1900411031141d454035100050702c110000390b0006034013442c0c40d60a00405002d00c2041c8000c0c504081c1e004000307884810740b0300566006003007101c0400140a030941110b002000e2701c0848000d0720f04d143c0110340d15010201d40035501c010f1211500d58401080c9070880d110401409024012917050b607440c10b000c1e0054000459200300305102e02c01c4200402e00c1464000c621485400703680d0b5141000283c110582e91405034400c42095504000d90044020b81aa2040c01c0d460704405580c5c0d03904058031001d805401000403071060f080c1c0b0400b002808045203059a80460b24990850b0a02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 62348968 1250 62347718 62347751
    0xe120f01060b031b0f0d090c030803010b0703030b1f032c0c0f0a031e1109070e030105100b0708160510090c0b0337180b09010e120a020106050a09020d 66
    0x401702010841c20400900e030750a0520361010841902c2420b0303c00c002c42d82c0b0703180c040b51a082a04243c0c44000001041c1d0201038140c03080201011050303907081e025001411141d030300c0ca25801d1904052507154403000000c0061100c0030b502c2d01203600100010040801d5865948503c100181402402c410f20490440e182c140300e0201207950001c0c600248204040789040200d05000c4100c035551800c2070a5022541e070040d910b4860001076803484101c0c103004e4101402c0d0342c0c1c041d058042e0250858024405e4944120880b00815009116282e8450503410b204103c10501c50000c0c2240c020504003ea498040b03800c170440481c061040003908540300c10000c0342510082c0c0c1c0c66244e04a500070380640c0e0015501f41c80ca02540d00302c1d404207040021022400644000c80005c103241c1920200c440304200e49549010b0f00850514020001c0c100382414041e51035900110240401901154144045100b5000030014105c050000b04503e90b8500c20384004e900480c40810031542846c07079602d04020030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 62350218 1250 62348968 62348977
    0x10e1b1201180807020411030a0e01050a0605030a030c02030a080403050312010603060b0a0f0215010b0d06091127030a060506011b030509010302071a180607030c0e120f01060b031b 79
    0x442d90120049002036591000c0e640c443c0c0012a08582c40c0c52103d640c100418029510a0701d2076003011450160b0083d1103400c494000380900b42e41807034584140520f403030010b003041c0171540c10304059405982e01d0000903d030404000000340703100030019000c801c010011000d00108501b01150014907600d601c81601995130764001c1000407041406449003181c072a0042810701030190060311070105d11941c1c03422000d882600300402e541c8c00081d8a4809080341d11401000308038585041007010140f6401c1d01d03c83c8120003462045040051340f400040011407000300307260700000d08551560390a8035142024040403030305140070401c003046002008011411a070031441d416130302c00d803400800e000150700035007112406440590000d6041c00864020310001405008442500340c02c83c400754650710b281540007400e10f0109414003820070199504030341d003000e18103030855511400704103a03601c2d00d14246d49450300d10031640c00c0c080e0020300c45001c1801035000701d000c0750a000e0384005468080456100c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 62351468 1250 62350218 62350241
    0x12050709060b070828030218010e0d06020306030f01020c07030303050108030703080109022d09040c0c0b0c07020d050a062004030b0f0405150f06010801140607030e03010e1b1201 78
    0x2030421109001825100c010b0401c85400b0380c0c41140704601e03141010f15050000d400b1740202e68002458180b0b0340102c014901d00c91401d1030044032072460380004c240c40021150b002042190080040745c02070b0b40c144030040c1098050303c021500d9040688416544c0c814a11007640400d00d050000b19088030044101c40a40d6019110000103034030b0008408000c0d4045a5440c0c010540003d80c410a42040743c2d14800145400710b015450f0900f0104000480720000da4580030b00c411004a100050301d4000c42c80c4d4402c1446c0c88031510b0380e0b018000314800c400510402403c50246071f200500b000042d6014050070701040c080403c5408104460a4082c030981c0006400c0301d50000014003080c2601d030401754401c0c424420384210980400c403c41503181e00307444001c2000d86041c1041820b5901c111080c1c0144615604044801c55400c040381d60391045a4020702000b0b4050f0307103044662003d4002c061003040032400c4070b0324289a40804140741080100107841000f0f403c03000b0020b024140140e07000303480f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 62352718 1250 62351468 62351489
    0xf070c0504020702092403030d090b06040921090308040801020c07090e0316020a0806180105060a050a0e0a0b031b01080a020306100c05010e1e0c030f070504110705071205070906 78
    0x48440095402110041140d186c1480c44503c2c0884540c90a00c09882c43d0803540901146002c200d25110241a50040c00140141e141c0600c0030080380000c100703a000b0001c850700032031841c0c26800084540c04880d070806041003900203000101c002056000b41540851041507440841c0c40e0031541080d1080b46407600f240d80c0c01032205920150505440b0440c0782e1005000c44207841e0340c0d4025030300b4500212801c4107076014080c001e400d0010207000c0c50742d101c03004640c00304551f401c0c80001001d0881600404940f8594940000c0b0003685c158400e414502c00201114600c1e004001001140c4681c03004490008405c1004074111003024000d03a40945002455010414220030041b46c015142d01c1080d5015902c0b6071035203c004d1001d0196414441481c00c4098119408055940c80d0540c1c100c1c455000703a1280700740050b074400102e0300c2001d9030b20441c2c003c660f00942c103840c803c050140300b80c060b100340914030000443c200b084035000d004910600075034500941c0c58064070121741c1144201440d09 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 62353968 1250 62352718 62352721
    0x305030105040c02070e0405030403030f020a03020d0e0409172101120f02130c080f010e07080601050d06050301050a020d140f0609311b08031911030f070c050402070209 74
    0x902d040e030822100e880d035510440301040d40e0740581d03054800007500c064030b0390b8000140910905500c0040c0500c198017500041c00d05030080c1d90000d41c5c5010107441442048403c01e05030806541b43d4010134a002d4122012039100301c8800b0083e40e1031b0b84240514009a242c00d041881d4511480d1101c40c1210140442003889264548561a000c01d10803412a800140d070340460041c0e5619101d114101c03511541c90f05140e180c00950b80c000384006802100046040b04d00700701401ea4443d4529504c60000e00e400340d10f07005596021030192081e03802865141d400d000400520350425409809072610406080c00f407114010781c44d0054000503a440c8851600710800214103080520b0303544e81020042071100d40d000c034034000041c4074031030392482a90b600c00881501d03030500c192010040044000c00e801604414a040600c981c1c03480b0316a400182c0f40e400d000982082070280140905c126507810540b82d40e14403040c80c040c020341c04140300f101c40080045022070b05042c10b100750340c0d943e680903103e500f45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 62355218 1250 62353968 62353979
    0x908070b060d08070807020307050d020d060b190602060f100501020703120507060204060c051203160804020a080304060801080f011b03020702030c0a150809010c020304050105030a021e04180903050301 88
    0x1000d40107080c203400200403040040000d580d4002844414040e0100c0e139210b001620405090120399400184540c00390307804040981e403941302500070182d002c00001480002c150100c1e03d00410b031514020b88840003c1c0c0090019008504030344680d142540d04200e95680d000420510105405803500580c0241424000120114241c00f840350040c14030900b4040710b40d076840140c3c0e019170000d1002600c001e0141c0c0400108002d81110500c4500700c40e8298900a14940511010081440e00704400c09011406649440c0740b40400f40032a1400d0700e64441e04d4000c050100306013032207844807500c5119910013111a041c4a55038101000700400b0307041c0c180d00c0b48104c0107500100d0041c0c0e818040e030301405080d0f640b0802800c005082e0901c42d1005803400e14405000518024103c4815174140070340643c020717501204841c26281e090905680f00d454054100000340110403c098a112a04840c8441b04003040003030422581419401540f10b0144503007403050310300c000d5000740400c0342840184070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 62356468 1250 62355218 62355233
    0x20040807080a0b0c1e07080405030c04060e0705070f08070b160207030c06050c1015090e0307050307020d0302070e09030301171507050d0b030109061b0f02100c11030a030606020d03090807 82
    0x180ba0034003403005c5000307848500c0340095210107030449191000044c00c1010b030609014040014200b1941003007194904028155920401800b0a040100010740041005030400f58460b07002e030044007054072070100749441221a80c0c141c641c20207112601d11001e02e102e20008900c42a260700098407982140790010131703100e64003c1d0440481c00c0c000c824502c100c021051240380350741e0761a10081584d031460b0065690850794520001040c9800c1000b80d84d000c103e0000403540010360566000c083c402c06400c040f400d080880d00130020400c2c4190074410300c0fa40004c091410788101400d50030212590280e41907139141991000d4181c1207000c80000e10640c0170f800a049075401d80e2401051050000000900b118600b400803600c0955a400c512503040410300901c807000c80070b0802ca00084000350002c0e41d140c4003542d07076480040c0c80b6007000348158810a0b8240e00613501500b100d846610464003d8040c020301d010b4100148a2200201c250501c80e003d0551420b070020705d414a0540540c43d00740d0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 62357718 1250 62356468 62356477
    0x6140a0207060309020609121011070b0c0901140a0504030b060f010806011101020c010e07090f020a08180c041109090901180206031806070203070303060b0423010320040807080a0b0c 80
    0x99102c40c0a011034190b0343c50300640010b8120607507000e88a4184140052700c02ca0301d100c12000e000240502c10301001821052000b40c100c0a40c4042607110403100c1c00403034a0400402101c6070403a4085240c1c21050b070070a010f0420f0701c2c8106000c2402d0368907c42403001410946004500152442001c10201c0d40141003101f00407410100152400805480d003600b5540050301200a50380103c404002050543c480d081850440342c0c0d056252503c2c1c2c26009060243c050440e0000c0202c444868050810401c0118500e600151090040145001e04d110960700f014500360b015801035000290030200602c03030046440021042c40c205200281c080c0320f00c0f60402404031400c0d11241c2e140c1e1007282d0f410840c00340b0403e1150700466480720fa92400a050700d400380d2210181d0001408180076600e11100d0b2401040350103042e8814203100c00300120301802200c241c001d03511030700081c00355168a0600043c41074a0840d4102c0c1d190381d40d01c0d1401a0f55603521540070303051041c41c3d40032400300d8000034010b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 62358968 1250 62357718 62357723
    0x10501270e0a12020f070806040c05010810030501060b0418050105010504060c151a0a210204090206210a060b03060603061917030a080901050411100207030f08030106140a0207060309 80
    0x12030440342180c1d14421045030002c3e0070005a84030481c40c0d04580400c21151000e0903000018207400e04095980a06c0d02c010350040b58140101440054412a00c42001e003004681100080c0101c5541d00c0b840c80c2542d0060040c0f404541c0e0055900b11141e400e03014040c121030060350780a1030545040401c8070280c0145d10b00315550741d10030a501d54007404074040c84c10003050031001d0741d040061349400c000100400358421200030015403620054070004203840a4aa5016070340807601440510000326503104040024210580d40212904810000344225104440c03c400070000c00352a40c0c940d06580c007040720110342c0030f0070400c000b07015424060782c0700881040c2181d9007652591a2070a6810704c2c0741c0840d08000c2c95102040c52199240d012040c25003040c2c4082c0204540e0400381c0320300d4040c69480075a14064030384100c0c0fa155952081102c4801140c01001d0b603c50301d0100e207000b406992003032068000081d407424021090847d40c0d000c0751811081074006184103171030b2450070b034040d25840006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 62360218 1250 62358968 62358973
    0x7230d060302150405030f06070212030705040e070206070e010309200d0206030115030b01080103110d03020309062205011701030b0a0902060a050a080f19050603070f0303020a05010501270e 83
    0x5860f0828041001101d101030325032501d082c8001d00d1300c0e000d40103507004080d602c0181403200540d00828401000e1075510341665803650b130500251101c0c4159841280c002035801704120342d40c6d030f0116410340203c14035518040c01c08080c0004400344c3c0c0b03100030080c6c03000710440c2483c070b1214a1200c0c01c3c81103d0000d400c03020b26155a03000a51150400d91140c001c1038a030030301341a2003507418030070f4044200c1c0900b016492541192103170541a00304140780e500032444000d540d003e06000304280c614a040062400355510503611031060195444d01c050501e03c5a052000314166024a0118460000c49100450342d42e1940c1c55050b400301d40900303a0108203584030400d4001d83c42d000c0060071140f0143d154680d41d1416410024a04000186550301c4070070103106200c1880341c411840f51000540d4a0045025283c2c2000241095034990101d0085135100070008101034022441001c01401200208003681c0e80790324a03c9001042808002016030000b80403070301044550001441c7e4120008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 62361468 1250 62360218 62360231
    0x203040507030c0b030411090708010e1003020406171605060715020c0a0c15110303061027081002041508040503071506051e0f01080417030a0507030507230d 69
    0x83e10b078140c80d8a5085188400c00010801082c469a41403103e00c00d041035a00e180580f40c40c2800a0101c40103002d5801b03412280b03804900d550f121481150055a0020401c015032980ea080300440b2400800d4602864001c00b170a190001d0f03100c214510866402400c7e035491300309d44da84e0f00c903000322001c0c039101c40c6160b0922881006040410501081c1d501c29190452024140062030356005420000d400c104900329180c490f2820300801500d81100342a80c4031205141c50a8042d02c041222140d501c03000300fa00e00481000d22007048030a81240c00324420344108030030140c0042c085e8442e40c0140b003101140e0042070306045101d102d2881d8054010411390b400c3c5400c3e903481c01b10060181108904c0c141e1108030a10031443e04003011074080c60520a8190061001c2c00800c2e2807500e0340080707a042c011a0300005080c0a0008500180c0c5071400d503101d44c8e00d143c441c00c0d00c4001c0405032201d1300000d1600300000c1a2500035100c07403141c01d17500c010348291081d003601031a000c1c0c1d0241095415083d111366 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 62362718 1250 62361468 62361473
    0x9120901050715020d0e0303090706030b0d02060d050403030b0306040804050d0309081606080123090c040509070206040b0f0f0a050702030d0204080106031e0c0608151e0907091404020304050703 85
    0x807910343c580c00884402580d9002c00000550581d1350020205441e500104103207c0c0c2c0c2140002c0080480d94bc07420007180c0c4400f08000900713400000032002c0e400200010b102c500c040200e92000344103a2007070300d00b04001c0c000e003428140d4621007241e00400100080000303008520301104001103461091502d0710a490300c0310704c0e040c204411607403100000d0441c8142440441d0b00f00d03140c280900b40f9042c0d100c1501c0503c0c0c1484c812600380100603070040c4101400308084818400407076010340401340c0f481c00da500700f071480213540c0c040171102170f2002c41080b0041420464090002130091484070808140303a2115451000240006040c40080d80f000700441144200d41d4006400200844800028005d10314108042d04ca08498244d051003f070800030a40016200c80649060350728529000e40039640780f03d0000d41c041e0041307440a078052042c500c0c0621540c01e035005000c1d40f800640f40340621780c840c0b0700306503050b0101d0300483d4400001e07108640b5650030194003455001d80280126500a40c0e01e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 62363968 1250 62362718 62362733
    0x708090a051206090f0c0d020f06120c0c120304030e04020a090302090c1810050a0c030320040501030b09090607210c02030406020607090605030406050411130605010215091209010507 80
    0x7140b03404516002102005100304003842403024400481c406404003c1180001858145100344024841c100b2000d4116082d03d503601525500b07003600300c00c44850306010400c4000780d0410415218248244002ca51420780e00d0740070342c0d0145e681a2100f2600300e416100300800781d00441802820040340d050008056500c2c0c2040c24010b942c11001c4503950300154001e801e10342400f50403030340102003001009900e1544403084034445490f910741842d01e140240f408601404000c89a1070001e00745014400f407030321086009108036023098030200117400c60b10040c0044032404079001c10f101c0e001400042c48040c010101c27041003908440310a64040000c203d0f0100300c1da0b400d101ba40c0142e002103014003015404201481c0c1000e243c0c2000160546800d0000f41280310040000301102d07103c20105007040010782c40d461021074000d000c418068010341007000205014800d040c014880d240a2019000b4801103280c000c0c24580b01402a5001450345000103034011820241041070800001c0b000c44c050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 62365218 1250 62363968 62363989
    0x70512091005090f031c030c0306030503120415051504050f0402010c1502120405030909101206021b03180a060c0f0f0302160303031407171503030c01020409050105150901050708090a05 81
    0x20b138151080454001c84009082322059414041414a006414004503000100365003061001040c6a10030b580c03140381006441e00301c1c004041c0c1c0d80c1d00b03201c18050440804881c40c0303860700081e503003080701d03a0340c02450b030701210016107000c0d000c28030030a5034001213800100301002c0c0c980c440b0400341c9070072506900c803490883c0445041d0f036503810100f46110780d440d01205054120041040b901155801d00e0780f1480407052042009048640c00030341c000c0d0010700016440b0202244005980c4c4541034410420310002161210f244600704400300817814a000d6400320f10b03625084861100802425507a85030014506030055056129000d00507400403900340841001d5403183d540810419a005080c10310088050250424446104000c0191545d403280040d8031014410415481c6507040303000ca810341c851034060403901e5000040c049403080d42900864104c520030303141138080c007101c01d03c0305100e80520ba005900099007000a4404200c0c0780004c0c0c40f1410000300903164840d41c43d400105001c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 62366468 1250 62365218 62365243
    0x25120902060c160f050619030e0c090a022802070b070609081b0f01110a030b010c0506160206010b09180709091409060f040b010611120a05070512091005090f03 70
    0x70108400e04c0040c1c441030030100100b8055600701d0812858540c140030f40099400c0780c508265a81c110102103920400c80c942c0d000340d002d1b207003140700d0814000301000395222052103420040355440080c41d0f0751290359140e124152550181440a042c44000d00b4650300c07101085d507149403500c0c10b81011681900c000d1103602c2c2c50300101460310890790b14940c00c1204254002c4d032142d1401e0b5500c042201c0013030803651208400d00e00002c08a685800581d0a41e03102c00c000303015840b50750700700714010701d080d1050301d80440147c003110310070b03a640c20351503525110b40071420b500010203101d9400000d0403803001c42c1d001074290600415003620dc80c2c20788126014291b84441c08032501051013848201406016002410360300391402601d02610360075a0b804043c0306402c03c01ca042006d20003084001c0c042408417010507034645079220f008034030013003ca03003066070b042d952401004c224620341103e80302110300804000d4081503c0d980e0340d80c8150b600d07800252130160400502244010b856900f401481c80200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 62367718 1250 62366468 62366503
    0x60c0c1e0d09230d061b02030a0306143d08150906090105130f050f15030304081504060908070b0a1506090306020f12070825120902060c 60
    0x40c05080080c21074100d98803c4005009615035402c1114007003000c6240780000362a40715410503c1c0c64020001c0c00101c041a100b00010280022929800710040c4040c1c85203030342c10b101c003a44441e0010507080f01c2c0d0f0310300c1e0340c41600c0e004072003c56480281251681900454040104c6403801c3d01004403030000d42011002507500d10404c0625920069100c0c0d42c0d030010386000e400c4e46068030120740d043c0d2040c0141d510810401d28000000092504440402c0901e000240b156040414074040e45282c152503003038040b034100080090905000044d03070101c3c0d2241000301070b541e000c080340c6001142d000c1c0003501c203a03403665141e40111380790800510aa5101d86001d408614011803690b00f06c403c0d50910007003805950104000c5154403007885403d90b07030404070040e034503400c1075411700e490b00c55888043d8560300320721304006010341c00c0b600c0680700e50041c81d02d201c03210b40c10b0390a00710101c048a1242c4040b4800d1181c5910380e0880b6407008581d588041e100d1342c5000000c0142c00e00e80b01135001c81c514081d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 62368968 1250 62367718 62367733
    0x302030708100b0d0e0717010f0b010c080301030611071406090d1b062c06010303030b0a060914030a06020309010b030c04050103020d0201050f0f070f061a03060c0c1e 73
    0x154803000259002e060141c2d107141280c1000c140001d184030b01c0e0b44102005803550f00004030308500f8001980100015400040340070b801703e01c90383c081c009035100040d00310701d8090710840d03a500400c8543c13171031a813003641245140c1c00e6070740d0000144407330040300b40510402d0011400203102e0700520241103003200001d015924002008901e0b02c500020094100615076a04000016481b171781c070f1007850360145001c00d8034000d09240010003640c49070780307001c14003008204c0e030b035a4a0042500303810389001c0da400f88030b101d07000000d000604219100d07500c0021061031003004081c03124012a090a0402000c3d6181c0c070742c1940307680e81a40c100f0780384440103035928039000801e40740c104030520303030b10f8010359041c0b105601d1500001d611134140e00001e414824000349003444808103104880c03224007240039241d1100021b0800d060700d08c02c000c0044a001e850010300701e0241030138100460940c480200180510740c0e03202010703000360b003040d01440c0062084c3c806900880040c41084103007281c0c0b060042c1030302e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 62370218 1250 62368968 62368981
    0xd030e0316140d020a060f0c020d08070203060f0103050709051509040507050f0103150b0903070806012702070c0b0f0903240709061209020a0519080d0203040509040f02010c0b0403030203 82
    0x140d0080c0d042c9480342406102880058517004400ca0840707070903040540441450881c107942040c5103090085d07201480c041541c00b08011030707014019650098007190f840d0303074446043c84050b001c00e00003c2c0196000b55400c12200e0035079000950b0240165802d40c600b1081c03a00403401460060f00c0403210b641000b21705110340e04000c200c96400910918060010f40d0103244c40034460565800f806903440800950f040241d202003002c10002e00001d41182c0c07280d0795982035901d0000c10517128003c50a80c0c82c0054402030100e0081d641c0142c0c00003a82c08240c0d18166a90041c0e40c0444440003c000b07043c0300d242042d41e014072603402104401145180d0032002c07072000405101e402080030007480340c7c141046c0000d644c0302c900d07981d403444096070001d09040607000140315030001d6030107103911198100340c021422000001d44000c684800e400c42c0c1d0101001481603803280a03d000300360b0000070341e200040124080c10740c81d01c00c560041c1000e040507601601c0d0b2070038400707003200e0540100303030000144041c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 62371468 1250 62370218 62370239
    0x1003050c040c0c0204231501180b0a120f02040b030a0e07030309290408160602030a0f080c121f080604030f1d130b010e030a03080103020d030e0316 65
    0x1150303103044408110304000e07000b001d80310124115003e0f01440c1d44502180c01030750702c10115a01400e203000c0403241490501e01510410300701032401800a414a2080c01c0c1050342020000103480d80071b9806410400504021201c0b040320054080a454840e030b81d20707121443c140300820140c602da038040d0f030b5240b8141c2e94003026200c4000480c005688803110410101e50f11040740c400361407a03c242c202402c04240c821116205204c0381002d888400014002100080000c0109400c01035441c02c5052139915041aa00c81c001c1d100e444012608241d034009816109070700c07013a8050000440d041c10200b02c00e0544440030011143e400c1152040e24482c00d07111440e00300310004010700001400d00c2d1520b55402003aaa501848041c10700100f0002c4c0002c400e02c0310020015410082c00c1c1e019883c480700c1e01c1030094004130200d0f030301088002151224500380442d260b05a07681648500d0300070391941e8240a85c0c804540b905600300913002c401c00f4207c0e035003401100c90b08201d5060311100b0500340103d229 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 62372718 1250 62371468 62371483
    0x506040909021c0b01050907020c0306070e0f0d0b070513030c0305030a08010e070f050a0507060c211503110312070606090b010e150d0603080301080304060206100602030915040905100305 82
    0x10010300a680705600000d60040c04e8505486013502d0f0013031184c885a00503840c028000405551600801c0104032406601c01d144c02d02030081120340d0209110716a0031303c1005443d00b9809040d14440388001517107180241c008140712031121f0100c0d05600c0e902d4032072210407a29500221140e03000094200801903201080501404400f040740300141041030000c0c0c4bc2030760400100c800d02c01c001c0707140910240201c1c1540c0c0310a8000d4400d104041c021080201282e8141c82000322100f644070381c0440052451042c0b03911110100c401c9100c1a0440e00d440d00ca80012a200355418800c440d1100c00c6000210041c01130a031080f040468140d0400c85881c1c15105054840c43c10000944c220724150b60744d0100c488628001e0010b10766841c8890080c81c0e001e04002c0c2c00c0900380b580d000000003002d010020040080700c100d07a0a4540d50b840d80c07141c482181c1503078410000103a000740005c20040c80c00c5480d440c1c50340b1001015a1800e03550711515000c0ea1402c580d6028028608601001800810b100d2072 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 62373968 1250 62372718 62372749
    0x90b16021204030f06021c0e0f032506021c0b0a06030506090a0504020f101707170a0e071503090507080303062110050c0703170c0703080a06050604090902 68
    0x1058a8081045141d00c00c1c042e0748005818100341501030403d01400b681200c8120380c40c4c800400340014081082406044058440ea02620550110041450000c0191507540304681a070002480c1d041540358540b60000d4820758100d070f802c005014900210528044800c0001c140100710707201403000b00b1a080e42a40c5c049000d260500c810042941d039814250b59005e0580c0c50001041d44403130000c107501d1501300c0007254004504404824003280c00a020080c3c84805203050103165940d0901200c110b441a205204480f001002040c0344040a41011000300c00241c11103003800d9846003000030100d11401c035500400c3d42d4000541c207001082c0240300260400034010351a609001012603a0082c00400d1640c0b03241d802e8150f929114420b1100700c48000c8203400901040c00c1491708030102c0c1e07111182c114089804a0310301d003a104003002c0081d12074078081501034200141c54a081d602c9140013005803d80d90790301c140108841d5103420140c009040c4d80d4500045045151040c08010418001c09 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 62375218 1250 62373968 62373973
    0x60106020c09010b0a0f12050106020309090105060f040e04060b031c03050f070801141305041b060e0112020a1b03020706110c03031902070e1f0501030506030c0411070501090b1602 79
    0x5008144c00e040898003407404500c3c00369a864a52041100c040b0049040041da00b0f050900004010758000090003000008680c0301d08103990310420049139100d00200035640080501041045404100440340c1c054000c500105528003c040003c0c1040480704d64200702c40c110049410440d541071003542c0e88003500510100c400c0c2071114001e00107400511404d011020ad010824400c2e8803106610381184154a0045c00541003a10b44141c00c030315440c11092034040207600c0000c88910500f2041c3c03103a80181c540f4402c0b96501c4241c0b0340030754400c10207141408081c01520156600e0110030001d00d83c002d40c0034100c03c50501400401c1c4260050000d40203a204a62080350707541e0200454807000030084403040c00c100303100f20681c1440001e0f48a50f21451040c010090104521080c50070160300150005108680341d900540840318255602500740d40300c4403041c1d249040c0780d8001003196159000c01030500005646680c25102100c00c229007540d41142403004030714002c281403440007082d001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 62376468 1250 62375218 62375221
    0x409020304061a01202401090b06030f01031e0203060901270804180b0d0f26090906061b01230903070b06060904020708071b050a0302040e011d060106020c09 69
    0x2000850210a4140d0fa01000503010b001520304100703000707080d0000c1c0781d25210402c1b60a40d1921110b42403148031812800c01520307105519107482124820000c030342c501c81c2c1507400c588403204880848101191003120b440010b03030240c0d40420600f03108003044400400c0c075144101035402c510840070310b52a014914035104100081400c0151402c1d9024100d0302c5c01050000c10390340b400703026140d0b02650800401c04c44403003401441100c401c5041d0140824150500720030f80a010185543c1030f000352116010b00c100c0025140100700c01381c010714010409400c0c46045c81070104552078000c0784008580d968140e03900b03020650131078804074240062101c451881c0c02c48160792a441140c6009011684c40f10024119956103400d840842001500854648016140c00d00065006d81800d8803070b907a00301ea03042c080c0000c00d4080025110080c241c004602e180d5400d020140a0f00d601c544200c0d5240c450341e80d80d261904111422444040c80205119458260080d040402802c0307070f18041c141040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 62377718 1250 62376468 62376521
    0x402090303090906030a0605040f0b0c04060c110409020303030106090e0112050a0f0c0b0a0906030e0c0609040e0a02060c0d120510030b18060f0601030612020a030305130902040902030406 82
    0x82d036800101c191a43c501d543c0d034040c00642010b024001c010402171030310080c04280140c1e001e41100171032040c4015100c80e1240190042a4050343c405e032000141a4003081c00002c81d400525482108060710124200e0120b900090030f5410907008140098507041041020b8110505c0b018014030522017000784581e000e440304c135100ea10080c0050180c084d015002000c12010550600060451f110340540343c03400e2040c0105400c075035111f0710000906103c641e400413003001c2800813100d94018120341c540b803056414070025024211010889001e109007090158460310300611001001c0d6001e08030f0750119400142011a4003c0c06200191030701042200c07004070450254143d9800c40302ea44e1241d07071083d101c45401519044501c00700c0c051441030001d5107040001003402000241c030306015142c2c50302800e400c2441103000c00b940c4002c59100800c00b00e40900c005040054460240004881c0c88986c0c12040e0f90050f840b8265443d8000108003c0c41401e08c2200e03c200c190848009080d00380c0d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 62378968 1250 62377718 62377723
    0x110a06050c09030d05130b28020c0a080c01020d0315050a09020d050106090b040306050408040306020d051b0915130f0303050304031202030603030304020f010e0d0302010618020307230f040305061504020903 90
    0xd000c1d2080701100003903060316048e004c82c0300d10030303034080d03175a081060040400d0006d450b002c80f0100c9038081d00144e4008500d40c800442c80705001d42c0c06034010049000b42c1c0b02e046003c0c125002c50491070400c0b1100c08140c90315441c3d80759002d003041c10800b6039030700300c0e1120365021034005a10050070400c100e642030000d800e600c030403101225084a004111600c6a082c100741c07034411988000e00403840001c604507c998150042441100190b020702c89000c2210029080c5100d0000b4040e031000500a1030040503a40001502d23151028162588000341c5501c00796003200450342094001c280040100010558440503100894240c11020760031403c018011960328000034000910804200d8401c41e4503900c265440040d400f4000d144003500045410302900078803d500840d14060f80e0030f20300440d105840c3c000c5070b02840b02c4e581c030280c104103c070036020300036406921a50070080d801c0020510b04c2c40203001402c05140904050804d80c00c10b40da03052800708603550030500440c0107210340b00007590003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 62380218 1250 62378968 62379007
    0x7050306090f0604080c030d0c0305090601061e051305030d020f060c040f060c15020d090605060306060604050108070203040503030a050912010e06010b07020a0905070e01020607030e0d110a06050c09030d05 90
    0x1da0300b64030b40c01b000c80141d0171409000204180b4a280c4000140031343c0c0e241d003005008140d03500c2500e90030790702d4000444184220b0342d4100041c039001c10310a03002c2c51040c0c0050401c140010440803810751928002810700d00d0036030303440c40141c0c00b2000100c3c040c001881101d400858184031207283c00e1400d41b10400f05a03040c401c160520101c9240d00c0305010b240401070b00c541c0982e550455541d52011029002007048800540e5400d19180004045007000245580909001000f6038145440d11004585807940140508114042800001385644081010300b40103c142d0310748030f80710035251080c0102c21595180b00c041c203078185480075007949400314a40381514507015940c0e50320f03419400401d0a035407155005c002011302c0c010030042100e0707001c0210380c20348400340d0030b0703030040c0c2c0310307003004a0548500781c3c030440d00740c0c011440711800d0600a0440505125518041d03411403140e948501c5e044400840d18066821700000d40c660ba20714043c02001c07280449400c10500307110307810b4010340b20b0215 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 62381468 1250 62380218 62380223
    0x10b01120c0e0405011e0501050f070b041e0609030e0d0c032003030d06060906090803032d07020105070905060c06160302120702010c080a060608040f03090f03030207050306090f0604 80
    0x54034805185141e02c6000346901c5190042c100307001d2569181101c3e1201c02030390711007060f202d07648a80410903611910495880c000c03035581250910100780c0b607002c0715a1001c0d208035000c3c15140c4041480b10f0403046580201c5006ea003000031300b11180d09003d016200c1140e4114881d000c50b000e1540000d60710f491001c16250005040c0003d280655007980e40342c448200003992500c40444d03860032160303003504280f064540315582c80b600682c0d521019200c80100b8002d00342160000e100081c2119010034000110b404800c40c4120008001010002080400e4a8510050f5110002c0088a980003400c140040009468040c50440d07021681070701c0708005080c8002c2d09d9001d0510b0310000b07101e0340541d0500590716800014a040c01c07100680201240ba038140040b42589002810551040c03040500325a03072900e0b81c06907680c2d03550b90150341050f00d60044041c00790188000c81c021420100c1c40b006140300e82c000703001c4642400b0800d807800e1300081c00c1c0303042c540c03040c1820b00d881840865400e402c1903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 62382718 1250 62381468 62381471
    0x90d030603031d1c06090516050d0b070203070618050f0f100e12040f0f12020f0d1a010906080114070c153909030c120f060501031112010b0112 63
    0x16843c005004070003114545900400040464000e01030143d00404001d0700c41c000322032183e0f02c0701e4030049000e00a842030581c0800d80c0038020021449404100380e0007101481a80d190070b14683d9010200c0c1c86c1d0981c8514240d4a1410b6030003000010407503112842000001031000d10380543c40280e81d0380701c0c00038131682940c8410f03c4030071090081014036000b1904100003601c958403100f03903507800394141c460150201d92460001030300c5140d0000c54220b0356000780074045041c05080c18000c0d020003412003100d00b179848411540205400300c240c0c0f40a41a1242c0124030280f40541480c00c2d0740190314980e01d009071030300520091030f420184082500b5448604201000d619000450052040c0d0742c18400c6d075145401951481e40c80c8604248400d0035220054924a60090b8215031003400c034000200030892065040c0044266030885040c42c078403035901c6030322020070350342c2c1c2006494080e442141c4007003507800c114001d807411064202c00e000842000300480c9680c80d000a0001103c07202742400075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 62383968 1250 62382718 62382767
    0x4030e040c08011802160203060f1e04030f0302030601020c040c09060306060810060825030c1e0f120e0109050102040f0e0408090904030306031a040212030f090f0307050a030803090d03060303 84
    0x11403940d10082c00c003500142030b226a89031400424840d6071080b0b400e00d43c0a0500c2ca03007800b801001c40400c338001c5800d0382c0c41c110f8101000000b0740003940043c0500741544100060303e0f400f9950360203084d000645070396a000b20946000d5000d400d4503400d4114030280524034042200c1c1019501091701107948601e044411074a808003c655004a0084545407880710f00b51103840e6183c054016040102c0d05594080004421101280c28422440b81400008503000e101d01c03545841038442120380c010f00745000035855543c00c101400c40300c1c00c1c54100d0f02c994010a04018191240b6800d000400d050b00d410b5901f440d01da0349600360f40c4101a0b88510070202c103400704061610035400b480c06590721000820191018003203561012400312002c0344500c00650056030240e0002c03090f142c11000c4500d002d400d020202040015a03c0501d100c01e415102e4040c1c0018a175803800c0e4048002c6006080b010fa581c1032811120b820701050000c51024181403e00400020360701a007040743c0704031894800e0084 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 62385218 1250 62383968 62383987
    0x70807060603170c101b0804031b0b010504050604060b0a1209080412140c1c080706110304200f120c04020a0201150503010911060a11030304030e040c08011802 70
    0x1c186a41028018500190b6010021614031004150035004003080702c54504214129906841d491819a05e0100c403c2e800080d0300c40c042c40c1042d80140c0700b400c00741012450144180180c15254405a440181c400010061800d16216007600705906440c2404094205180c4802074800d8001200400211514080f0b4541d59070380070016895101304016603540d52580302c03016400c0c10101c00d0302c0403035240401c4414904001f0710242c2180f00900310084903103545046040001c1080001d13101c0c94020010300c0e00140b064442c9002948490040507101d007800c0c1823034101c801e80e40b800d200c0c5104001980a03e40e45d2541d000e02d120840032103040c0e0780c1e001940e0056080c46640f42d001c0d9001800440c2d5203a0480e019002070342030608200a00d02503030f40e01c100305426946d5100001d404e5010141c5a1241030034890000c04030a800c5041c180501c80102c01e146142da4421101500080d10b401c403030b02900d2619000390903d0142510b4041c6c0d0950400b2104000e00900e94140854240d00040c03e280 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 62386468 1250 62385218 62385221
    0xf030304030c06110a0f08030906100f0611011409070e0c0a0203030105040519050403020d120908070204091b0b120114090619080a0b1e040b0606070309030803040f0506060103020f07080706 83
    0x1075011110307200e0000c6c0e03803800b062560000c0e40c80300c07814041c0c400080c072201000c00381d1004882d07002050304c03142c0346804000d8404100d02e200b100740d19500e0b003044050300060be1407082e0007410744000400441b85054203000140d64040d0056401c04410084140c1c825030010075a419110200d5000802c2d44820f000c07410010300503003900c0b1100382014208414185c02080b4030a8115103600c40d0f0301903007c0d000d8090304507001010020f202d104148005405428242e000b0038000f48651310000505503440c240032a241c801e0340c8005180b0200003100c41d01d402c02180c0940c01049203c14440e115a60240069605032000341414010054248402510b881401d40d1a00070b15103001134850310501420140d0054000b00c5010b1081020a400880034942143c121407140c0c6d080340048040380c84d0303481006003d40c483c0905408200000c0004804585000001c50040e841021002c00314511031511504144008103010b0516206002c1104d0360500c110481e01003070b60142c4016520800e62a00381c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 62387718 1250 62386468 62386483
    0x6070e061207021c051608071406040c05100807020d0806041b0e030705090903160501020f0c0d030b0901120204020d0e0f0304061209020a0b032809020f030304030c0611 74
    0x40180781c14814040080c0e0041001d008440344c42e410240b0344580103030191014480d5002c0d40719400c0003040c3e0500800d40070406042c5e161b10808240c081603490003602850300301c090300c0c1901e0001042404018500c0c080303a460a03103070458202440241340c10400039482c0c0710b0400c1d8042c1480001800114143d0b65940940350041841aa03892402c051201c010116103003030080c0d9003e44075440d070225503803030300c108043e2043c002c0d54000e516019049044948100564030200c50541d002e01c01c0c039290100d4500504000009600203120714440014000d058652201000f405800d03404018807061302020140782146805840159a814481c1080740003040c5451040b9090f00440d42070700c0386403a01100174012034809903150186040b032030880d1801c0b1010040e00950007103c0000400550055602071540315180405c20401d4110030707100007480d404141800e1100075680c0c4114411803420412041b4500b4041c1d0065007404e0456450030311103803582c0100410300880c0d00400d08031030130400010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 62388968 1250 62387718 62387737
    0x912020108070c1e140625110d05030403030f060302030303010b0a0207030203011104050102160b091314010b030a11030f040f05280c06020307030c020111010221071b0506070e06 78
    0x140e9542044c40240c2c03110b40807030000f114008009001601c8030800000c8203070040711414800301d4840040404041881c2e4003c01200c1070011413200b80d801081c00740901041800c072034607029942e10b81860010100c4250300280320741c06241c11014005030310f00109403810760f541c40303012554070300790600240d180c040342e07500007035056080c4000c414004005201402c110b4900b03030200c403041a0b09045a02051019000d2a4402e50091040d049580b600c8142c210405400003000a95400004501e0820b80d00980244107500400014025a241540314005908040c0240c3c641981000e1200552402010f0000b0b40740d00490400c1a06010050107103190084040030691a2000800c5140d41d0509404c0c0b000d54800c030443c1000561140080308072340305164184da5a681200c2c0550054071402c4145503010b221390b5083c4401e41807010a19040d003020310204031401c0369450005402000c0429860000d810410303460040000200c2c0022840e41049150800b0103001c680000420712070300079503004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 62390218 1250 62388968 62388983
    0xd02040b040305070e090d0c0803101502060403140903070909020402090d05060702010b1203120a02130306020702030f0703020105070b0a09120e0a0b0324040204090c1e0912020108070c 81
    0x208400003130000101c880c0b05650540c03540da071026803612000401ca00c43c01241d5102002d00c0060300d00001158070540c400352400d4016101c0141c6460241124240c10259000c1c6040c042415048040b030b401e140c2c81001c00e81d01c0c1c8100320021a4a590700c610031b80d11456120081a403c650b5585c040e200c88010207054009030384264208142d44030810303a403550141d46400180072450420008100703900017260700440c50003000380b2280c0f0986600800c01c5200c0d41e800c1c01284c1030700f01c4410001005502980e409a1a814140105401c0408907002071240e684112010030041c2d0700617095440030794003c0345c0160b0703541d42e03910b02070003400100320010100ba111344154801190001002035441c1001d5a03410103403910344021460612042d9440840c415150130f14085910311244480003504010301b000d030815669007581400d1f64008107600011a0042140e50011000c00600050711816440c2554103a071500942411042010310041d04110301080003455580c01a091018a04ea11180c2e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 62391468 1250 62390218 62390227
    0x1d09010e1501091103011d0a0b040c0c06050a05071e09080303011d13020310090303090507240f0905060d1410050109080f100903110105070512061f050d02040b 70
    0x7640c24029400d000d80c400d410718040b80035488000303050983e0305071201080401c4054808520111065000130700c0c5812143c0c907011400300075140d9020314044010079444103182081d03e071410f201078800c000d087c3e001c260b107040104000b09070300170108443c2510700640c1c1d260000b8100801c441d16902908001042d100010001428449450315009519019508600b5648401c0c0f2042d03031104d050b000181d819400484684808080b40d4898007486219040014580715070b075807018204419503103c15103980b100844121f00307803c1ca181d480d00c000d606292040c05c0c9106040003a00d0310310640181400354070081405da484100a6210b20206800071008000b01d26003806e50410f0b41e4179501071103000901d9040c00103030203407000a005001d0162480034210780d08086036558020142500194200b040c0315424414070f0f103080c400d460281003a9134443d41c1c1c0c2e54001e20840d03148800a0300387c6001e640d404c441499040c00480c000101c83c4850715250742c0e9400b842046001034007a58016011082e00000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 62392718 1250 62391468 62391493
    0x5041406090c13084806092b0302070512030f030406060506030405010e101a060a0207030f050a02030c0f01022a030f0109120302070f060902063609011d09010e 70
    0xf41004c00c2594050817440c0056078020004188620318200030348941250035030034100d1300e054409000031580181c0000968062a504240500500201880c460680540600038140d05008090242c1002d0700c42c1c03000003c5032185140c2e00c1c410b000d140c0b4000200480454204042c0d60003440c001e03c40184059100d0900341426802010a031036440c20310321a41d0164202d4450743d0040501c041c0d80314007158000705404c414801c60394030094540c0704600071402c001c0001a03080d04051075481c0184001c01507880140305141c81c1030b81c6c0550040c1f00e6004244050450783e800910b058140100440440507184000099968a034001c007420350701d4081c80310500c1403030b04154010b0500301e00400010003000c5102ca015000ca10822402034128a0704104680100380315800800481d440605158074200d0f0085c1e9050008058507902e1a003d01c24081d101342000030307001380c007803103080482d17480740b99514021010544605072500441e50252410008100e0042907101c40c01c010703d0f55059400aa4102 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 62393968 1250 62392718 62392753
    0x12051c060b120a060b09010c0f080708180307180c090314031804050705041e050a15080a0b030d030e030d0501090b0102071a030112060e0d0201050105041406090c1308 73
    0x340200003000070b09800102145160b009034011251107400840c90079810b24011180c610000000341d030915007aa502c0da001542260042100c2400341030b185844032885010008510000c0000078440c0c0d000b5001070104401c000041012070050703010014090015171029540c008242c1d10240250203207101c40740c032a8034044000c204168507481803c00c88801d1a003000211901960903074000340003800144400c0707241d5070700c0301008040c07070700024003131030703a0303600154030310b1020380140440000104052800c140c102d01c2c41c5401a010703003403e210010714040800e0344d400850742060304150f1a170a40c0d611440302031085550300c010801040c03000d5030312a118040600900000c10340144101a80080c848640521440300000d041c106140355902c0e03c10040c0c9809042c0800307440887c6c2e58005c502c6003000800c180c07010254183c00100d440d41c505010001100c6041c440c41c40310000e60420010b003507503400e01140c0d000406085083d2500081604040f0300d80d400d80203110340c0c3c822941000c1013841c10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 62395218 1250 62393968 62393977
    0x150c02011a040515010311040e04080a0f0e0d0b0c0c100209010f050301080604080904110d09150905030d05090a0b070e09160203161401020d0213080a12051c060b 71
    0x20300180701c8a0800c590a000c203d842c2100d070344504040e10030658400f98800e4021505d10042c02c940d00b402c19403200c0032040c040d60150b070211142d00000a00501140e007202e141e07510542c40d82031441e001c400daa804150740351009080141403210707260015240d141c2100c250b501c545c0b130180840d020300c190269440000c0d441031205902083d81e000c0921315035031141040741d05aa5220340a4045520b45a03507408440c0c00602010390f000d0b0703e030040400c0d034503840c6015082d0700341c03901000316100629050604610309030780d45803c005401c1298240c042280041110004018110001080d5032808081418240d208030000c05264104040c0f0a50307990016030040d17181400c5900000f0ba490341101d0f051141041c086031409600700744084c0540e55000b1410f81001400341e407002804c4e020395840182281d0220304402003056002c206000d03140300d0100d1050290074680001c1142c6041e0361100103a510740e400b07125041200000d000d4403c44200d00090b20f110b034445905101098454003c100d050b0070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 62396468 1250 62395218 62395241
    0x803040f090f050c0d0b1c03120e0d0f05030405010609180605060103091a06010c0203030a030c02010f020408060606160f0f030305060a030308070c0203010905060f041205090a050409150c0201 84
    0x1401c049040380d6009210f058003520302c1c0902940303401401000040906201c0c0f1070b2903407024510349440b11b140e04440c4c140071241e00c642c0d103155410050710307519800c07034012000390000c0d5403000100d03c000c140c1210032581721a0311428240d440781d5640c1780c0a809044c450304100081414641034000d107001030105248031501c00e900501141ea20840118115408110007a1101d40300c0345914407000807001075290060410315104031000d040c0c0c1c001c81e00d07517441101380c20002591942044440c0e6420712450801e220207071015803401d0314040c011550f4140c0902498403558001403007105541c0d01d5021498050b0b40080d00301000421414440b8005d41012025404241803100003003041c5841d00e094002e87e0744c103490303c0e20b40c0e84a0480c1142d40c00d1a00c3d208036099980e594640340414030030000d451080d01c55140405291806140070072440103810b00110a0100c1840400a41c0c0e0f56620180f06556059034009110381c064180400301c02c1404044405003807400c882548503603030640140c00d042c1c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 62397718 1250 62396468 62396471
    0x20030f040608011d010e0601120c110c1f1b0c06050304020f0d050d030b0607020a15022406040b0f060c070608060a080a020402032e0303080109060b030a11040803040f09 74
    0x2a80d0b0580303000c0c0104ca00100401c14642a00144200500c02e9082c581001b810b14110f03000c809400110341c00c940380613400ba00800c0b9103101c0488a1003081005500e03c3c0c800b6280c5a0520076842e0108050300c0310035000c83e09201d90145540c5001c00603011008066401c25000200c0c01d98500016140b03038000d8406034095606864824102e051002c440c665080d8008014100d04210701c50440c0103262444007140c0c0804d0030400000075994003103140d4090405460070103000405820041e15016003000c500400100b001079088450150400c0c085d4025400d8501168400125001504e61401134529070b92080003c00c03010002c980008461080d83c200b5190407415480f28000c010b00380581e807081c808241d200040c50703401410103801660308607015501445062180100311081d0005117071006569245028040041c103602030b200354010f282c2044104902c9040c00350303108040c07200600c0c07000000d40712600841d03007600ea030046400070800c010569403111b440f881811fa00c6851031050702080b6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 62398968 1250 62397718 62397721
    0x110f0301090b060307020316060605040f0501090501051002060f0405100f0f05010b0c0703080f0f03010305100b2b14030301120606051005030105150408030f030402030d030b1020030f040608 83
    0x6082c0b0f81e0469001d090245c004505110822045c40d03c8a040da02e41181c0482d141c480008098596000740c1c0c221f00c182d10401324240d810035250380c04030f41c4141c0c07000e8031034a40c019081100940205101d50020b030311100c4c1e0740090340c61b814100c0c581011180e1002000d880c00011070700a42882d0300c05100c101c0014401e01407641d88160b0003805000b070b141ba010f02a0082001000001c15403401011884508035805042c01030001c200e46250f00242e00503212034012001d4441000f1680c401d00341700030740c1126000c21602500c0b1148500000050410110030807800d08072062205901c500c1d140c000760a82101c1d52036854802c48840c1000d415004c0320180e007040004201440d010800c0240e041165441e82c1c20740e86410b0811010025450086844000401c00410f400c441400240b801207020f0030b00903524102131042c0b6140840345041c0c0d070105031502c02c0c028800d9440d01442803410b071580c507080486105052069010b15500500c2030b00c10300c4006001d0760b851014001030400c813102600d0b5584207 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 62400218 1250 62398968 62398991
    0x306031202070b180d08040e010503060c040b09010305180604032616081905010e040c05030a0309050415090e06010306060b030c03070c1505040c0819030e04020706110f030109 77
    0x1550b1040c01001210031043c801c101d00740b458414000c3c0f0b012402480e40c20312910a4440305266801030308021243c0002c8001806107040c10007400b5003000074880c2803807810f4a401c2081a0500500d440141015100c1e4042075500001c06c01404542d401a4244c56071420b05103000b500c07032043c40344044a46980b02045a400e6070700c11407480e1181004020401d1059402d03d4101d4860310014200d9601c0190710782c02060070030143c0710320ba020380005008601c00b4249030400340128001a03001c07a100303034809140c0c10000fa81c44070310041240d0342510041a0000d1407070704103014542540045000d5894002c255400c1d8400180c0c0134126805030704100004d54582c0e00030a22440100d444504400d01000800d032a14405d06401c81c25030b024030590005080c0c001c1194064074416101610030300c1354400141b10315001400b603030100541c0d503440c007150070003070b50b50151100c0c0035494141d2107607901003030403800e003d003036049621408000008255180100300e0320340140e4100707005103c1a246000701d080d22 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 62401468 1250 62400218 62400223
    0x90218070813020a050928020406180302010e0906060903030c0a0204051003020d0b04020402281403010807090203090f0d020d0e0411030612070e010803090103150605120907030b070306031202 84
    0x980f40c01801e0b21300e2841c03c100901030030701005007041d20700c1d102541601c0d202d408880c0740003000300303080f040c0541e9440ca0560000d00380010300380307900d04100d420041040143c0e08801000388445050740c5101090382c4140028031140108000e00e5014000010400703c02080422020306003442140c0070031441e200c0075030544484000d07000094200c100d40308082d01044903d2002544688005e10140c40c05004c5e503640e002e22021503101e040e41c079810181c2ea50701d0395085580d84d00100040302942d81103616115015130388900c0340c41115070056000003c074100c22000d2018940d513184110483e16401d1205000a5031402c03d402d0140005480c82c04a00321460940103804618102c80305103815502d6080800119035100c02e9906180d01c200c25000519015042d842402051944003441d01e801c032820014040e00d840e24003400203940510018012a604001642c603024116002107a441e034900c05031a1500c409a00047c100d41c240c2001c01c919240d00d500300901f0750f4400d001c1c0705103c90b81d00f003040c3e0303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 62402718 1250 62401468 62401501
    0xa020111030f06090a020903010906050601080a1b0c020a03050304080307170a0e1201020c060c030604060b0f030403050724020409060602150c09010306050a0815010501020a110108040201030902180708 88
    0x603800c210b11000300324646056424190070002c801001854a505900001d003111180d10703044900d80d8890781005515a0042401d6a002002030014041c4003181c18200e14149450002d610034404c850a03007005544626030030b20085c50b80700041705d0340e603038071076074020b907070707802607102200c0780e100e0b10b8070b048901c07004001030f0b40301c4003a5902e45840d4001c0e071508120869106070046200c0359800c2c400c400e44000c04024440c021180f847d5a1903880c01e102d02400280c800ba40c0002c0d40480c002c024802910038000c00316039000b45c061506a0320b415091610504d400d003061681c800d90710305881c040c8103132201c0f0f6004008031a42e18008000d004d60b9108140d840702c00660040e26807840c0c0c1d4000a82c1000c0d51002000c1c008014900001e001d61944000b0b40307250078075000258540c0c42402880d20100050380c070a805820300740024442c090190391000c00c004a0f05c9072007030402c160000420110390003500721215107540200260b0603603800700300900b40100200c89510006920704007140719a02c0050304d11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 62403968 1250 62402718 62402731
    0x80912120703080c0d020a17100e0613020f0a11010c09050906040504061e0518010501080a0f0302010b0405090a02030607230915070c0311010212030f090f0d050a02011103 75
    0x300c0c106070a5071400e65009100511401c0c1d500340c02c002c06000900a40700600c420003050315504848030508d0010241c1107401014400e44084d0200240004000000c16991140003168500c0742c4c400340141c0140a8011121090107405020480400180c2c000400c0401da49042000300503803c4201d10881b6020594480c458000c520303040891603038281500401d9002d401101301203061502e4000480100c00c1e20340c100d030007184d40c030b0003409004001c02250505005454000303010303079410400160344034a81150000c20300810a140c6d101094000c3d005204066001030080006203410032030a6214101c042c0203d100c0e004020002e070780e0a00640300702d4400c40c0e400d000801150361118007a03080d43d100c100141c1e07000c43c84100e400f80c4072010b00014981e01d840384900104842c51440d101b51092114501503040d9000181d0341450683c051090765401444103030805c045480714200c440c2000d144103e400600d00400b61207480203030f044030060200c3c03003881c0e000700203c54501048006600040c3c44a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 62405218 1250 62403968 62404003
    0x3160612090c05060d060e07050406030b0d02061204051c1e020d08010b07030e060301030804082b0c140d110705041a09100e090d080702030c060f15060403080912 71
    0x140591300f4030a018048180d503081c00082c0c13090f100d504d50b644501c0c0484600e00041d000080501c40c00c0e9040c00342e0b004042050b40c83c0c100083c81540012014055680c403000405441c0c000101800010048101d11110201f013200c00a01e03020001860019401c10210408210394140141b00c0c0c0300191080302034446544039455642400e06007102a4061072041e0b08001e0b400f03440c00080c1d035170f02c0025402144110f29169a0307504e0030755402d05003840440402032072600145016000b150704882d00d508201d25181c08071042985203414803a410744010500d1481c441c00107003407009500301c0700000130a5588412900001c6c0d44d4000c000c2134994503804480012800c009020040c02c004041079003080b003816000c1c0d0300ca51908007504114104403054a140e500c48581c90881c16044500e65400041520103586031800c00042c442c1e5880c0d01401e600c0c141030011000a020100d468800e044004008240e20f0340c60b40d882c2020000d07500001d0704280303c1e425003e5500d1000303d0000d5070f000c02c550058907 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 62406468 1250 62405218 62405243
    0x1020c0109061115010b09040605060301030f021302040b0315010806040b0102030702041d100c0306090207020904020f0616060f0b0307081c03020d0e01020a14031b0304020409020316061209 83
    0x8102c50343c40c3d4102100e042445084440c60710000300700700315030285c40d0a1909640b101250700421086e21621351003580955001c20043c400f1410100d010503e00342c06603080741080031a14540f5009125544c4064010007000c0244450100c4490150200ca2800d03a0b60a41070f88800082008a80b0400c07110b6001d40c1c01000300d08014141600495003c1d105580c1c125a1a0304141e000e505101021801c080307915503800c0c0440c031454052003464043c240d11300c421803c000696010031340118015002034400c1010714001845645c07090102c034480d4410f1036102d4014503240c82c081c00600802c2440b01001c9007840041c03000da05002610340c0c01c5480c0c1c64020660744841c0350032080310401101d110400c1507000c0145001000c1c103800f40c07120b01c0049800040c0d462040800041016903508094414070008109001d080c4080324203118030740c2c0c0740d01605650303030315944002002007404001c000d4060188480c03d500c0080710140d588101c4640340c0301c5143c10020800c4070800c036078001c14000c244807030300407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 62407718 1250 62406468 62406479
    0x121814010c0503251b050105040303030b0a0f0b071104200c0a0b0f33150d0603120f080903120403020a0203010f0b0307080f1209150706020301050f01020c0109 70
    0x401100641c2c0c0100b043e20700e02946038034000840002d0052031101c0060031603000d4200320080d0050841c16240440d8061881d05000000b842d5214a110141c109512601110f80c1d640c1c400b800312004101070242041c030681d50750200b104a801008043d0303000b4030f00c0500421a070a060083c048804030b062203400c0c0121446400000c00d400c01c0d80281c240744030f1081c6070800104101070141c0a81400b601d400241c2c50220030000e0100d2544081220801c8004c9007845103208448170345601042c2103e00c10342c06521501142c01a00070000031003410342c00d0480c0082403100c0301252010b00803a540d01d0510810081c0c4094607a0907040d64140d542da88100b00482c05100301171401d0742c00902c01d00c1a03d840036504c0d000242074611001c20303039100303da940d008108249000c002c1c9070020080e810240c952140010130036a15283d4904450308640c10000c0c003280f540d690901c45941905100c201246c17035a42500340703c40290024041c00380501e002e05104121503000098407112031505950701d40f400b50170030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 62408968 1250 62407718 62407727
    0x3070b04141504020f18010b030702032502030105010519030609030e060a03050105030c0102071a0a020307140706230a0c050c13050411101d06070f12181401 69
    0x2001540c01c10321003405820024010701041e03140b40c1d96100d02d6111800c1c6801000402c020b418400c6125151802e80c082d5031080000a090444004000c86612941d032010164118800c207041c0904d68a00b02818400c2d41c00010201d6100b41c1c02a4000c102ca80e0301e580038801103408600c2a01050500e0640400000d00c0603082840243d1103441c02e02ea4500c22940484c0e0030b90000a201404661900014000340c00c08114900a8200901c0100300307079440c10b2006084146c01000301d1422141c009030001e4514000c104856410ba4448402503145840ca440c254030703210301d4000d0900280700c0501030540c8540e04901c3c800c031100803544592515050610a440501c0390101c100d400b40150321450019540750003542d20102545c90300410186410301e0302e05540c1081f810b00501c0307006580305900030a42e0255510422200343c0b0a03a24004034540c00280081c0220000240702c2480302035200304012181e100c0c40711800b01c5881c1c4000e9002c3d94850003c108185019550040c11403061202466206 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 62410074 1106 62408968 62408971
    0xd0207020312032e030203030703170f010501050d05060d08030a0b090105100e0d03020f0709020c06090c10030c03060509040503030106120b030c0607081b011a0306060303070b 77
    0x40c070f2403214180648640d88070311381c900c207102203d81c0190f1080003d5a002000c0320740351401442e00a160111030312586904141c0200410201950f9202da01d060b140140c582078200410080342d5801004010701c0386e58403040c403100e0b0402081c00c410066019006107000410812060814005082c0c01a4461405869214908032881d58480c4410360304441c204c0d00b00a554035107040c2245003c41100340035180b4050700d00001001d0711103030700030011003400d00d0603106156035841c200790310740b54448d428a41000e06c00250145a9100340c2c00740340e07c000c0508002500541750004a550720b14115001c0720076074000401442415040a80005021480241885928001c40110382c07103404042d513050190350042181030800c007100f801d881043d480503503801c5030104060f0543e80a40310444006201003c0484100030604021a449100d0440a4000d61502110380d0b10b008c201c0d0350 = true := by decide +kernel

theorem cover : BRFrame.Cov 62230218 62410074 := by
  have h0 := BRFrame.cov_init 62230218
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62230218 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 62230218 ≤ n) (h2 : n < 62410074) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
