-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0158
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:10:00.170391+00:00
-- url     : https://prove2.me/submissions/5659b72f-0c48-46cb-bb7a-6b851d0de622

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 28237415 ≤ n < 28417271 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 28238665 1250 28237415 28237421
    0x20c030d060302090f09030706050601030b030d050424091203230a020105010504050910091b0b030106180605090603100b0f0c0c0604030b06060a090f090207020f0d0203032b05070c1401 81
    0x1482c0894000d40c90408e06039241c0c1c000c3c110041606040c075a0710700c009a602c7d101800318a2401304150b440c5980d49050403403258402e00000100e100c55041a032411600c680c21000306025110f03d1030640c0709040703452a044840b0b80598000c4508001041e222141c0c4c6001c0d08080c2502c602640c0080c0f1aa031b88034005e1000311a030403141e60400768012110141010080d901c4054410701481e5981154000c00b5080094450141d008420403200000100086903110300c50048001c0d050700400781c02031a011005025020383c3c0c1c80c0a100d240d0000c00706601c4102c0400c580d006018099600d901d0308409019003100ea000390709800c04a000f1482c03000a07501e031103000c68080c1c0b0703401410068192524400c5c0000f03600018126010f03c2880080410108840054980203000c202000760759000d862051001c10030362810302d58040d600d80308110300140c1e008020346940042c0101c09083e42c2050200415082c40c8004842031040d14040921001c00d078480007411a65000340115031100b24805401b42c01c0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 28239915 1250 28238665 28238671
    0xc0801240b090411070305041a070206040315230717010b0a08040305070b090a0210050a080619090608010b04180804030209060a0e13021009080304030213020c030d060302090f 77
    0x2160a1061060018071110005014201006000083d0781d07003124000700001c1e40010800e4011a00c04503081012842d800c5105030145094190360b818070200f0380c0410068001c50200410300d4608060102281c8d00d194044070003c00042c0340000f01400d07030365100c08000e20503603400e80000c111040c618100c001c01d036000d9041303030318070494185000e0004004844a65000c1c01c200c0411004220b01008a07080d031502500071505400504116604c03441040310130741e5000445401d000013408020301050b04a91141d41c01403041d52058005d44114442e80000ca01a810a2500a01e41540825160340550004004420a40c2e0801042012000c82d03100f08402c2540200702180c1008240018180a0303102074110202420406e02075445540c0e91b01d0301c00c8215511403000c8002e100314425407400c0d1620107068085410310410460924049948a1146000c041e01884d99151400380307010503603040720211460318087c1ca4507401d0741010500039004c507210603440381b41940301095050789900c110740c1c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 28241165 1250 28239915 28239971
    0x702060409090203031218010f0e060609062404090501061806050702040906060803070501050a060501020712020a08030c0f01110a0c02040e0a06020d0903020f120f0708040b070c0801 80
    0x42081d1400c400340c0080e00540300b080b0381501052203010840c1c01e074051102c0c0110104215250400144074102d0f00311030688070003020303036030614010400405003c170741e6541041055441c400d040c5c1d6600c000c40c0340c07020102149040d4090641c07403c07440c0014003001d0301c269080c01b10240120b0f640d40008981e010415801a00b40c524114010040c00c1d008a0080400703501c040d001240342907054540004035403941d0300c040141c0d0070018440b41000420f1081c0b0764040900b134402c02c80c40b410300700001e54501e558054176206210600b9400300759540c4050132401008007400302c0382c0d00e0008520481d1030305205a010310b601d6003480d10017001c00c1c03500d03404e075040b03031a8a41d11410180229000c00000d042c032a820070409010322000030f8007080860008045107040e20b040410100540d00c2c0083c80c4c034400700f035420040e401c081989011400d0384401c8840c0d15030400c0440d5160842e5003401130701442203a11510074003000150301800c114010031400100c5500000812040f011290300d1491661040c1c6208 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 28242415 1250 28241165 28241167
    0x30715050a020109020303070605010302030d0801080c28060e030706140315010c06060801021305040203040503090904021305090616020f0d03020c010b0a0e0105030105090a03050702011b050303130b0705070206 92
    0x8000144554007a1030521510720021684a1881e0003290442e881440c00740d41d40b80d190001882582001c004046100d81c048c640542503605d403100d00d903103071000020868032860841400c2c40c008940c01d551f00703d90580079000c082005070b440c00e029149030300240d1071178080d005080d000a41c1d940287e90701081004401e01d030034036666408050a08070340d0340c0003009061000368802c1401061203440f030356000c0c04058000594400101c4400c42c54803da991010f48903a00404c1000000352003c02903c400780000c1d82d1440c1c5a032524400039000140801680e1562480d007400c00c52400d01c0001d075980140e20f52000c1c401c50505881d022a211a0400034100b1590312807844942014403960041001040710000056100180000903c0502d200d5005040d1080100c0c014041d9141c00c1c0300350340d000401c0318010030f00840315a50140803400351030310107810310414001c5c904284da058500524000d43c0401500e0f564500944900c44400d0300ca681680d4101e111000582018095001c403610705400500e86 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 28243665 1250 28242415 28242449
    0xd050c1b030f04030204091401020703170c0a02100504081e07020f0d0b0f09100e01090c0603020a08010e060307180203041a06220609090c030b09010207020108060405180d05090a050307 81
    0x101c070247c41e8a440895508034514640004400d0078400740209610907940d0410f1940107444546240b078010703040400090081100d0302c000c0d070700080e03980c0d0030020300b00c80800d5503078843c10b058400c0d0056110590207405d50f01c0b0080152880c0000034004ca034421219640e090a0700303018418000d0080c140140582c0300c003804521082c0f00d00d81659404080c103c00c44401c40c0007003400d4170a031080c511a80c4030b145e444031001003c1000041c5800080e069501c0c0450510b41c01c4003000307104e100c041c4640070300c0e24110340c0801d901d510140502d0010b0000503e0f0401c5030601d5194940095004a07410b8442c6181d100c0b2200101800c866014061704c00180b2900081c080030413040e251494405865801c3c40d9500c20002c0c00301040c1c041c9070011030007455200b20081c9035040c24030b5040801410782c0d9a9034810003400005030b801000b8a600004103580016403a0350703070001441c8082202075800c10710311800d0540c6919640c00b50091203148400e07a8402c0310f1669810902d40d403a49180200a16070080180d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 28244915 1250 28243665 28243669
    0x316051608070f060f0605150a020c010c06060e010f060e03060c0d0b03030c0a0506100806010806010b070303021309020d0c0302040503030315030a081606050c030601020c010509060d050c1b030f040302 88
    0x340c07507068010ba401d021010300c159030701c10468503480401d0606607102d9a003049146442360491f10400300740500f507403510a1980d8000c0d11180541c42690500141a000c2c40038000c4a0b804400542081900f1627020350312042e9414200a01c0c3c421040000d00c80c90031200e60341000305940380140801640c59040c20201da8211019000ca00c42c060303010b04c414001703800b080d4000c104202e401070003103029180034284080940d0b52101d10744c0088030150300c05001008542c10024000b4111602e8410494a6044a03d01200a40b081407541441d821700400c0108840c441580107064007088668100040c0f003c0c004160f043e4000c0b403041c10340c1034206000251038803545800074450424010f05071006000b0541d5096a9600450a15400d0030802010714041001f540b00d940e0f007011a00c6000c60962a100000070b590340e426800e21070401c00d000c1110b011507250007060742e840d20840b910502ca070b8a090903449041d900b203140c00d48640750203224160740c2e08401000311400d10b40740c1c40322641ba007030031902 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 28246165 1250 28244915 28244917
    0x90a050f0112020d0506030f0f0a0b1b0307081504060b041a0c03070302030d060906080a1506050d060f0b0105120a0207030903020d050105070e0a0503032706040303050316051608 78
    0x10040d050108407811002d00c49050300c014014000a99800500d07410311109044c58105402c4040503c1c4e400300c2c10440c8019000228005080c0e4000006400381d52924010022182e8242d44a0703120700b404001c0c003d0207038001c502184206103201070040c25071407003c1084142d9189100d050344040c003c001c1070020942071049590401189801e542c44e0024030341400d465980155410b400503007000c10007402440c0702d0b00440006000700002800824100103450f521001000d02c028014091869450603030b46c0503410000081800908005800307042c0d0400c8005012901000c9003c00e02c5d103104054558095010b65000902c0c070303682840030303a4985031403400a502c102c600741c080c0031490500000607907541025254062081c0000314860614286c041e0030703031b190540f140e8803c00388038034240810703100082545c51011200c054500d60064101800368100c501c411896040740c00082c012040c1a001401140180166017404104440410088803070780103401007640001c03030220018022801c0c0380c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 28247415 1250 28246165 28246189
    0x5101a0114210403030b270703290405090304121202030d05070302070b0f06011202070c0803130303180605040e04020310050a050a0b03160603090c1e1505090a05 71
    0xd04242d15084a850b1060448aa44020848104400d4040008142e4180202c2d0640f92003130751714180c81f400a43c032040406500c100104400c1041c180064040c61103038124061042490849111441104485c800c5224260440b680500e01340000b042024000004803801c54440d1028510300c1e811559a00d143c600d1241403540c2140320a0001400d014003c1c41014001d81c1030707450040c0e5039201840c180003000002001080703071040c1c1d1020448030ba6000518030000f08440040142d0310016407600c8445405130381c100d0507040c4804584407881002089041061313034000e40710310360150880e021114940c0814003035440020302c03d0004101140d40780118980140c4004c0541e90390383e005981020440f0021903c0038a840c3e02c40003841261200c9120310039200740306a0140c0204055440c855040000c0c03881a442010355418002081c071690300400005882081004600d46250403051a6035940902a01010752600c10300c60b5000781c0035400b16401c1007805845081d4940c070744810444580004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 28248665 1250 28247415 28247447
    0x41208041401020a08040309050616021306030c090209090108070303020d03020a0302041e0f081203010314070513060303021207020918010b04020a0302040e07050c060a110906070303050405101a01 86
    0x11400780084120078000741044106984d03a640017884e16040090070404c290740800c0c0551010041004150481c030304c000301480e01a00c0792103d80d03408001900c014542544081c06032940242c001c546542d2540003065031020440d48800b890b40c0f5000041c0c3c0b105240d21004015901814110040a0094010b48904600c1c0c0c100181443d64412499090100792a4248841c60052a050203401010038504005c0c000c0d03c8010001003203810302c07158480c8010300024160141003c1240c12072182004420b0143c0740180101c2c81e090380460024000c0c05407030000318054014400d0807030110307541c0020380e441283c00401101c0310f0f80710300340745007542c1e84a0a00141c0315502d07040d0455160f00c0324001000102c4640d54016503c0b49009011600c40201800703d108010301080348800400c0002403098102803c1040010164015100e1031801e02c03504426581000001c5178080a01d40c240c2e1040e4071903401003090700c0c80703034000e01c0342e42040b0b400c4055040c900410f941c02c425030315403043c000e42018a0071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 28249915 1250 28248665 28248683
    0x303180a0e040311060c0a020304030809030102070611070b06010815040c0e031e160812130509040c150c0804060e010c06060902190e03030d020a030902150301081504120804 76
    0x41d10403001c040c0108a40036400700701c2c40211000c001004200d40d070350048660010600b0040a9a0000c0d1a8455448080e2a4000204044500755029411a00b29a6006000300403110b0700180c440c43d260020034060310740c900d803a800968154000c5000b030f40300f00f206420a80d11104100b041000030b01286d200d14003000b140c2d84455400c2d88023004401c0312103203196003080180900803040c600d00803052601c002480c82060040100b040300042d00c0041c04082680c4584808280c6000810f140c1c0ca0f902c580d90044242050209210100c001401a05c401d051b280341180401d4405460306003298038001e210800070041000b01522403c80a5080c1605242c492043c0a10b62682c07410307a5003a400412104e035001514291020691410319803210260805128100341400000d4032406a0540308400c107400141081c4030503c66840581d485500a2911111010520100e0800c3d0001d02440c40140309500360800e0700413591001511403a40064900000401110b003110703500c101074021212611 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 28251165 1250 28249915 28249919
    0x70302030405150411040b010c02060d02070305160f0209010602010c0c020f03150a02090f01021c030506040b0d0b07030b0a050906100c050a0f03090b070b06010305091c08060906030c0303180a 84
    0x320414250307001314055504c0074401e8501d03d080204481280d20194188003031045c0314801600c400c825601184180703000144c41c0c0804e801c05640e148102d1210704410280d00006204103c0d55010811005009941c0c03003c281c0c1c1c84142c1031b400c8075403102c0c112000c6a10220504010319040300d40398042e00d03001c0e0680c3c020600d10500710b01d15020540d0050000c43d00814030401c3c504056400281c0180300748000c0c500d0b8550203094880f200404000c1000309a110400200039444941003c0300146000c0c05110708135600d406e000039890f1081d95801e000a00b04000c1001900e080d540703180a0b41d1005092415035100c2104204107200d901c03000806009402c0500400308506010b04450703540035540e0300c2c508c12041d1500070190b15881c1c1044c40c0c0580280000742c0031800c000709d080c0d4094020700740051a501d0750680c103454414107541d000850200554410380c40b6a00c028018000c0b03030152240c15058942d034080640f10340901c0f40a0b60154030030301038502003500180d8103030907900c0058081c2c41c00d10307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 28252415 1250 28251165 28251193
    0x60105090d020402190801050333090c06040608040501111e0304050a021804170f0304030c030e0306180c060a0215070c02040207080a0f02280201020106080f011e0c0206070302030405 80
    0x14201d0045e4002144002c2c0c01040741d42814843d80d03000029500403070714000752a07680c0c0c00d82404031100780aa134240f410300042800740c0400c030349168120028041500e507039544c03a00504c81c00d42103e0440e010750030810f108000704001070175240144050403440c0c12010302e5085101c06034000400c01e840c5071040540701005a03c403001e0080c60105220f580031900d02d4907003440e4001d10803800c240041d01c4400c1003c0078101d003034542601c0d0444e40c0343c507000a0131714007401c00f1075451140d60342c00340d458002c0750107003d0510101c80450090121010a5500781052a0304210082c001d0b031031404007580001e48481e0b0030141000e00c550b4030400300d040c814020700080d0041004c030381040300101c487c9140014400d0344550042503441c42010944014005280d00b04514500038982c080b8031224652640800c0045a000b134100001501c2004c0454044050031401d00c0d0180001c00d800071600c24145601844c00f800c10f001c0c12131690202e4008005c282c03030300034003180290310040058850f4001c49004e02005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 28253665 1250 28252415 28252447
    0x501110c121e03030403090e0a0902040507020106080f0307121b060e0d08010509090c120f060f10150503010e040201030f021908010b0702010c0f020418050f060a0203060105090d020402 81
    0x9030254001000040e040c403050000715010b10704003500d0b0360b00520070000000d0b408114030080e50710f4410600310070345490340c03020f001c1c01c16140001c1d801803c100800003600d605620140450340003504039139072540304084aa88030300ca06040a003006000307070850503109015903402c81e00014800e00c01141c00901303803110740480d128011f10340c04c0c4d9000301c3e0750400307040d070b000040c40e000d1300e4221200011030504003603156458000c40d0f8268005d83c55070650018185044c44500300b02c0c4a510309580c0c00d0724141404200d140300848000360b0411150b8030210394110038220a102d003601039154940b9690a00c1400d010300000140204d04040c2c40d143d80c4640e4251500280000c452002030070036460404140113482c00d50160000007106005200860140c0c3e80200100810b642100300da80e4200306a001240c040c00340c030454000041e4003990f0a4080000001d51850a032140506495264030382d809480280e10041d00d4460010340305104c1c42c8061f1a05401c10a20644000d00052031f00c0f501c1450124a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 28254915 1250 28253665 28253689
    0x50601020c06030c071703131403040b04030609020a0905040206030406050912190917120f040506031305060709030c030201051b070602030a1205070c0f15020f0d0c0906090501110c 79
    0x1003d000072401e5003c0108070b60f0350803030469514901c07601f1803900d18203040b5500720024000d4000c00002d9240d44d0b001031300307004490207851440c40050b80c680d140e00740003000d040c0c4904100e014681c00340b130008035840c5511032a030186034018036540c503503295511070001400d030103011010790c4e0041001100b401700ca940c00500b14862262010242c40c0281c0783c0241c448603841c0e10410030002d01c005809440c0304c0208445044002e1600d000b5154540720350014003034040c940180740c100c400002400680040700d194081200d20800c01c5400d240e0720400200d84521041c40001e140c60420441480198007a10140100d410085400181300c0d084680c3c0d54030b40140d0f5070007140542c00019500e12600d40c085010030390105e006205010505101000070300c0750034900d002404490b0b6000b04202045111064540340a035450819074946000da020000c456200c0860601014508041d0303001c028080d0000350112089034407a0b03100189458015644001d04255010366400f40b045048810b1707480d0201195 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 28256165 1250 28254915 28254931
    0x4060f050f0a050609011a0f0d060b0309070b0903101119080106020c0409120c0c0f0807060306090504020d03050d06050301180501060b0f0a0e0105070b070804170418050601020c0603 80
    0x7010700703021265804540703020b01a180552407010040c0440340b146402c81000c002c0214003145c1c3c4498244003107020740102c02841c21494201140094607441c080003541c09a8444819070b1940e0781e035104034030395500c50a4100d580581050164a240000540c00017120074016860586080d511950411101090360b0240c0085010f030b000502c14203504111030464100181c1741007000c40103030388511070095074141d120003c0005031551300c010041c0c2ca1078940d000b08400211050190b403a071080b04e80390a07460060390000f9280020014a081642c014a80103039005801c00c0038070000c680b42100c81d42d000201c05140c0300e441e100f000589403424400c481e0100c003503039250201c210643c5440d500f503414661011409c0801803150070b04002c641001c075440300c0c0607802c0c102c1d89060001e0040c3c03014000c00700b025004150b00f01c20000d819401060541c4510b104d40c0041c07580b030701c08404803140350050b03015004a1014050440210ba034841c1d0156400150500442c0d0f440100140080d10311b510450303d040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 28257415 1250 28256165 28256191
    0xb0a050d0f0b060103020a020c040c05090a06030c0e060a081b0f0c0309040f06061409010306031502070302100e0d050702030f1e0715050d1d070902120c0304030c020904060f05 77
    0x107400d02caa20100c881d00300400340381c20341c50140d100d500250307035518a00c0102e1141e41d55411a1710380314080c0d4101c803207100c03000d801102503d079520005001840c6200180c0045044013101d81d520345082011105c84038116100c501542c3c071000c40d032440c48101e072580d10001038030410106c2b149032104070141c01ea4030f01000c0195501c094810071b2000350b490394240ba0150301c1c04c0c04c2c0c0900c01e45410134500c1f006442446800d40e16800300c41c1c0101e024000c10b40c40030f041000c0e01c0c0c04807110052150001e024042c0640c08540010703442ca031448084442d03071050700c00e1503005041541540c5104900400c8194001000c0310b90907015184038509041c950400c540e40041c00c0c40070600c03444801d000c1840101101070481d4229a02190041d05921030028400c19640d91501c01c1d6179249150b20007010b000794408112808a9128001c02c0c2c001c0d80f013070311102c10010710400007508040300e00b01228856a4141e9030404002041d80c00c0c81189140274008031200d5403111540c800d10602442454403c2c1c42681c002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 28258665 1250 28257415 28257443
    0x30c030f010b010201110c070314010f02070c051002070b0a0302130305070608040b0c0c030702010e24030603101a060f1e030609010806040f0b0718180e0a030f030b0a050d 75
    0x2e0708443c1b40f01004070703001d030081c410818100e001107008411a6000004c0300c280c07070b0280840710700500c60301540e0080e051000c2018028420080e403e00242c0c0c40a44550040e01c1c5090300030ba98501c41c5104010302880d00304108804e040c400d401034041d9010041001c01c200783c80b6a2207a0130004645c1003000059964000c010612200075003068020340885004c40c6080f803c10351080d107034405d00e40060305100080080602c50f84a01d0743c1d210054801b401a400400c001300001c540d030303620550b009442417145c0b08002090007a01d00c01c844084035000951a1118030107000e00400e03401142d4a0714982d442441040030300d0b4281500d010550080503146035691034000300700010090b040e0800b24030342d804001003100083e0204850706480740c101d41500c3d411307030381d82e00119020000600c6042000c21b041000050300c5000406504a00c1c0c0340b02001c0c092030000c0089a41d880540c26009400a0348001440018a0195001c0000e000000d02030f00344190b202c0b03011503240c0c80794202c21a00715540a0344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 28259915 1250 28258665 28258667
    0x3030c18080c0411070c120c050301091113022503050417060405010c09060203030a1d070803070506060d030203030a0c0504170c0405010603020405010e040b0d060c020a050708060402090411030c030f010b01 90
    0x116412040d00482d001d0500d05982c1b82c005440241d405680300c0072180d000400c0500c0b00390003011004001c0100280042140c502d0009100190b542d0214040c40340c01203010340d00020741c0280e60a007084e04040f10070081540401508200a80105900340101000302044203c2408a21841c0305c1c1f6000040680b41410b2901c80d0031190f6030040d000030010b11070410b106959003c400c0b2508800e0b540c03008201660107040e02d1000c0c020846800c3c040b0710444030002a258004005801c030316005030280c2d0195a00c84052000441d4072500040060b0401c10000d4640342d1550f000d200c548070f081c500a4203154807004008141c801ea4072600806501401c401349061600740900c40c05044a0318003581094034000018280110500b911886140c5032010030b051510f600700340d44902d5801a03014040f441119001079100c0420b44c00541d014002c641e00418094000103034a4083c40d40505840100c0d919a04d8040c1400b601506081e4035000d4445c04c84010f6400b04082c0842e64444000007903152800703c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 28261165 1250 28259915 28259921
    0x30f0f010e04170703030b060c1b180105010c1104050c0316140301050d0203160308030105030d051204151506020303100501031506051c06091a0d020d03030c18080c04 73
    0x1c44166100750601c100800601c0b40d403085154843c02da1140d07a101d406524068020f011038444040e000039011841440b20440083c0c1409482c144480d004401407506041c01813507030f444805150101000801000554441c5008860709802507180c4440701580c01c0c00102503035001c0c1d550b21207240010061180080c1d408881d02034030003450a115060411080c1c080340d09000c148100d5106200e5140f01e1001d64906200f80c0a0001d0030000034a4107d4a03440c040c44c50f84c10a000c2d8502074440c9030540b5808038040c2c012100007024040c521646507031780340d0b82d1342958551501165904c1d501d030020070009240b801004005004584c000d15141d28111a0b200401d041d607074080c0d410541080c4100302c1c01e1040c40041e0051310754502e06180e0b10b0a125035012030060300844c80b4480302e8540343d0006020f144a62164846280a03814030341055100000c0210070020700710040e6118810850700340029000b41e100d80769034601ca0400090131048003015071512103680d80522215000015008901e00d00b41c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 28262415 1250 28261165 28261169
    0x100c05030a030c12050f04150e1006060905010c0c050f060903030a020c040f0c080a020703021e0c03010b090708060d0203120a050c010506060f0f09010311070303090302012a030506060708030f0f01 86
    0x4c00100000d05d0301c000740b4031001001030300142c503070981e000030701e104004d031030300f24001d0385c5854001c8680403000841071100030059481544001104500081140d40c4110711040c8003c0d0413060035240c1d103050030f04100b11030b03a02c1c4040c245e1041003040300c502d490b1014806401d41d0025600078000b0003406c00c040c88103581000c109900c0440c54848400c2059411042d03442d044010300c2001070321410f0f6840c090b0f24048200c1210b1902904040740c0384004800010140306081c400da009001c0064640140f14000d5800e5540201044002d000550182050300421000b9400101150003d056441d49150103074000c0b45101d0003e0800584000510307401d005d0140c0020003902d8681c604550151000c0c843e02604030000342d00d040c0001d544140783c1c4650003c1c410030703684501c0c8659502c25498054010200003000324003650800c0203800d5108198515202c440003c8501f20816a4082c1003c43c02018020a416403244e0248450804650001e01640c0b08055040445e102c6003468001c03101220416 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 28263665 1250 28262415 28262447
    0x3020606090c090d030806060c0106031506090212070c02010905130905010501080a0206030c0706061d0a0b030606010e1219080408100b10030506030a05060405010c090501090311100c05030a030c 85
    0x1041403071084e84a2004e915031094140c5498120382e11000000740c5244200e9130894441d6003031100102c18000c0001c645e126a10108004012499503620910260b014448494451124200010f00d01c0d6010320311000d0480d1051402e142c2a68580000540c20f0001c40d0039031006036900c41c0c0710f01c1000703024801c080c0542540d00062141c02220740c0050610700c4001c086002520001c500d1a017006140d4028001070b001c14a0b10318055000d44245440c1258101d0f0700700d81060030301d05607180508010070114003511041c0d403040c00041100c000c3c0003401d1820485031646104444000b2907148506801490b200c1c4a5404942e0351480c0250700352030700f980c0c002c1c002c110030700e00301c0d101d00350342d4030000030705c14003800d604000ca81a075880c00028101071440e103000d05a4001d0f20100701c100101035003c008114101d85610000e19110b8004694086540c00020b04030000171240200602d4507108820740e0340503a10303240c4182d451660b205c90464000d0410840420f40390b02c012140e054000014164174244 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 28264915 1250 28263665 28263667
    0x10b0307030b0f0d03030b030a060203041101031b09030201031509020c1b06030c030f040c0305010c03061502030705120f070f0803010305060703020903060a05072619060f0b0a020c0d03020606090c 86
    0x140c0e83c0062035200c8180c81c0142455541c003014101900c0c01d200c030000c1580c110808644030b10389414003890b104680c408003070000b46172903041c101110b110304401d10ba00a07540d5412145501f15401903005108900a00d000080c0900000a05c81c2890005003103c01c2040007a05202c07110390321090040f00040d050521440d0280b040142803c1c070039054985c0505041c06415140e2220b007090039012641e500090019420a80c400c540f40d03406401a40488801c441c2902c4013115207201261680546140109903812071102180705e17615000141c000b10340a07008580c03620f00300344e554280d01c1802007030843d29000003100400a003c014010107501c48050b040c1903240413030307410009072104001400c80c5402030799900402c15584c45241040381d83d25100d0b00c2c1030715144da80c03551403019007000c41d1038401354109600c0c0302c50b0200706801100112010381280c0512a030400701540a00d1b0040c044490441c814442040d1696480c4040102598001c3e0050043ca042020038044808801004841102d038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 28266165 1250 28264915 28264939
    0x415081204090c031b050a170126060601020d0c0c1203020609060c0f04030201080406140109020408010e010c020d14070b0411031009020a090b0105040e162a121106010b0307030b 78
    0x10074002c103505d82c0002d900c0c00035642c4002000941d21000c07040d10340052007500754008101c2200f01450781004d040002c0540a080058041083c2c1d01c0c00200c5031540181c0000480340c52003402006440d50481c402c64110414a80760501d422040c259a102640181c0c8002c05000c0f0900d0180816a08540355050b401d2411081002c2c00d0482e121714480241001144400681445500d5016281000b100140107005c1d5944402e2040690010f0189601c1c0d54a02241e87e80c0b00075051041c0d6903003e540e42c015068030119484113840240c02e007102529804001c020140000f800841240e04c03e40c82840c4403081ca03071200c0b0601d4508414201c0c0f4003000d520b440000360250b952294940129041c0407000710b942d18015004071254022030b40714011181004007404207031145990800d01d40c035010f90b034018005107154409921403140e01070308030a07454210f450901080e003400c200c01d000c1c0014201881850360340c215092800009030b00c90008010044144966541d06000349031050a04a400040f802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 28267415 1250 28266165 28266191
    0x2010903080a090209060111030d0e0f010b0406050f060a05040806040302030a14030403080f06030c0307030503030402010e06040317070602070506160912080301050d03030b030a030509090a05090307020415081204090c03 96
    0x104045c6c042414003025221542044004000320741185005403014014107032001d460303c0d518282031030110707225420f1044141650400380308107421200002c0210b0081c62a030030034002254040c8081d071040050800001c1040c2c1020000b80c0d000d02e1003a8001d40e941c056a2100418000c81100841e400e00420410701011a611800b8070341c003c03110f0842c0e10b41e030b03458000029103481c002000311505402007260000c14848048091071042e0300030380712100070039454000c20101c0d110320b00005102e41d0300300000071307c510000c0700544506407241c6001032414074140c40707046c40c10204554091511058284c030f40c5059510035a00303801080783c1540c668850a0759a2400100e0105014042c001c0614110b59414140300e03401500e8100405000c0e600c0c2c020b0203050040c0181c0c0310b40c902c14001c003209804030f440900b061203031034894800350014500f484003035070802c0007034450541004800c51503144042980801403011200750210b60110ba99910b14002014055070f41c400600024181b400034842303d05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 28268665 1250 28267415 28267429
    0x402061b0715020a060606020a03120504060f020403060e0708030a0f0305040c051504060207050114070f020a090f020a140309060711010221070e10090501030b0d08070302010903080a0902 82
    0x4500110440300c0d5a18507850108268401240445100c1503101d406030041207007a0140c1c09100113100c41a12003000341d90f02e824009000f40010741000c2c0e4840f10700280c0d0300680d0001d108100100c3c0c0400c10306ca03941e00740e03041070300107803000e56440341441c020003410004440184034450143d403e01c03542a002610a1001004450601d6101c40c001020008038020700d80c080c0000911800c41d07002c00180c9110160000d0003007101604c80c07010013194643c0100c040010780ca0800380d54500d440c01d15516100380040c0c460040b0380141c0881d8000c90030011038000d480d048000403074010380728555507400600440b400b0420390385018041003405032600d2301044590b03104140f42000c140880d145024140284034540b00d140800d1580003044030031580e81541c460040219a41d407504845400d01004001d490f060740c5000413844c0410108140e5001ea04032a1051800515403207804002d0f071070341c3d410340e4000e0b50101c0050355140004001c040d04042d16075040114400100010259075020a043c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 28269915 1250 28268665 28268677
    0x10c0201050d0f0f050903070b091207030e0105070c0e0a0b0111070302042d0b211c0302040305030304080703080108030301060807050310080f060402010201110903071205070308070f0203060a05040206 88
    0x3040782c6a18242480ba05584c000c101c0e40d2060b000100403514003201815181e80068008480c2c0000f10804240300c0c0c4000554655610b1900b0150f07880c014a40d5416618503002000180c1404000c1c40400d0101e98000004c0000b048040c20342045c1e031500d0130765441202c100c040c04c01e0601070380700c04e4124a0680054180300340d90341502e002621143c01c100919800c181020310720507104c04400000914846038001d010303d03440c01e6501d288480c500e0200036241b112002c031a04281e038088400c0c2c07a000204183c0a04000c0b045080041c646030f00c1c0d407202c1d42554001c480654407800001601c07000c0542c400005030040c4000c1c0b01071800c5504061008003000805042c8808101012001c2902403580f02106001094404200c5040d5000258055107a050071102680594602003840e907039000184110f80e10004018003900c1911308103100e150b0300462040c8240c5107449181c0c40032000034803502c000e105181c000c2c03400703000b401c6803841014130b0098003d040c0c225041c2000103010050b00c500d010380300c3d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 28271165 1250 28269915 28269937
    0x10e07051528020c180703050403090810060e0703110403030c1a09010b1203030907121a070c060f0c170406151202030c0a03020f120708060709080c010c020105 70
    0x481c5500c4190300400c2c050303410808070a118045159079a00039001540c900c1c8100d94080c0e0b030126500310300704610300242e082d003501034480510016000ca4400d5200560081c82420201101e80d21003040c42d1400d0351207141c000c0c01c80ea5485050040c180040c42c4184d21000501c0d0502940c01000d20300d40c05030049200080030702c21f5014011007000600b510200f000c1e180660201980e19006100b14080d000d070b0b16031580982d00328507948803903501c04400c0300d12035500c181c000e00c201e030b180c000000f861019803e801d43c1d4038125060034600611800c2c1541c0c0c0518007543d11105c04004c10304011007264110b1a00c030600600c0c01c16150703007458220740800700e40130000a01c208659140d0900354090003520603041000c4480c1c60740404c05084180204071601d000b6021a112100c01d0811300c0300420080c00069802420f400b1480f10324605011020100c0341c094081d110110b03a01c604261030a80300b0707503040c0085200f4900600820004103c1e07244030724024079100b00100051b0f000640140700700900b1070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 28272415 1250 28271165 28271179
    0x50904020d1502070f03050909070e1c0512040303110f0d0219020d0f0303020409061a0304060b0102030c01060f030201081e150f13020403060c09031104050402180a05010e01050102010e0705 83
    0x100b00d0001981941c442d039402001c044c1ca0401d0070328000340a58030800d40c181c400c05a0b0004240d41600c6002c00d400c0390400640050740004040100e41c00c0c03140d4140040b02c0d5403160a64032003082d140a070243c8000c3d8400d4403004070355012580c10600b05031402c2c01612517a0302000c15100059800a11840a65003610a10049820300e0001c1504448158070181030031400002c04401c15a25038010421107040079002c112060301c0356241c070984d800408881000d001c0901c00709010900e190700c81c11b000c240c140101e0b071400d8a00b069850940302c0b90b038054103406544140070415560003080850307100c1d07010740c2c281441102e0072130714140c46c0030013800108900c480318007404900e4544694003031403032500901c052907800f80070307800d800a54841d00003251640d04107003c02c510079010b00c0d07440707064a9100341020b050001100912008100090090ba0301101e00c5803100c00c124181c038591030248504607000b0480e90306240101070201c206070722850440e89000c0300c0b0840710b40b001c1448025240116620 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 28273665 1250 28272415 28272443
    0x150801050d14010c120e010603030507060b040213120605060a050d030e01030f020d02031b030103020a0e0402030a06020d020901091406040909050c091603050a060506030103061d0d0c0c050904020d 86
    0x30990111003140d0342e90320f4580d043d41c100d5080414550030b800f01c80b8040c095960a040d80b1403d803102840000c01003003091111000050043d007006460f1800038000504bc180342c50f140001074540359025101420400210b5010f2202601880d6803000d03040e5642602e192034840407880304151000040c040001c100315100c41ca0f0321030f4100d5a1482c40f21081507485030070075022030009520580b05043e008540d43c401008003429031040d070341201e400804a141840c03130240b0b000c00b81000240b003280e0600074030300980d001400e64405031035500584600161140c138000300140026011307800c4800607400310b003d030210561320101103030107036003207180042038540c403d2409074684502c44c14880e600454520030401400d181c818280c2914009903818841525408107450840e8610b0084942086d410401440410310031340080050941c9481990882e081081c44941030840e03d40810300024452505601804640044a0050101214110100d080a600003603c5200740c1c0c2c0d004040c0000710b030f11 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 28274915 1250 28273665 28273673
    0x180603011127040e03031801060e01030303140a0506091503030705070303020303190203060102030405270106030608150f13031e020604030f08070c060f060924150801050d 75
    0x9009280c080c00020740b1284480d5030b50ba000d898105404080348200560354010745050b0150125059401014524640b189800e00400c0320001059491a640b1608001803100f540224a40218000e550000e100d800686040c000900050308880b4020309001c28803841c1d99500d0780a03a0403441d203940d504010500303034000c24294018120050024014500c0020a154020000310303c0348056018540f130300c0c0f08900c04030007240400d03195180141d00511091049091119158581842d0488425403000050b40c013801001401d03007101d40000e0300d8907410040140100000c004035215402c900c410b52030200540b030312144008081c0040201250300183c2810b000b01c424031884020b02c4510440da036161b1001075a1040e0540d41200050720341c0e51582c498910819950b4041c00c10b40d52203030045110b0b900c07140094000f81c1203292409644007c0014800c80c18403a5071400440ba2000340e00114030300108505054085c0d0000040e1850760645420340c5602c81102c2d419a002207945100100c91414 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 28276165 1250 28274915 28274921
    0x7060f0302190503150a090f05070804050a0305030606070605150111070302030307110406050603010b0a020c010e030a02010804080d06060306030203010f020304021302070f082206021606050c0a020d03080901050a060518060301 99
    0xf191030b080b0410000c081a0b201942c0c11500703000003120412701045c2c441400459150600b268003400307035080800002d002078403480003590811402003140707007880341545807141180d0b01503441e0036603008105100d54003541c0211401d010303950b00002a103031251554021a40324031034440e00410000868414801c203940da0361040c000741030058001526507848142ca00e141d40d10030b080d40409441601200c0c070803503102d442c568040c00f4018001d400385045a40c0192076486000d0800ca402d0340b0240045039010b20300744104c20041a551b600480c00e00c0c035500600d803c481200c0000c0405a0040003040b0143c0c0303400b0301a0341c10307a4444100590b25450ba040000402c0c0c5680300060507500b0005030034904003006002c0c003a503c099a01e01d000c4c40c9540e07102c1640d640c0325405081c25030034203455007000024020b001030400c003050b10f015661f02d54920360000d18400d40a1b84101c01207510303075040c050f4612091280d554482a50b4a0030000719082800003207a031000340e00c45d0984d0071016400240603071000c0d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 28277415 1250 28276165 28276201
    0x31009020f04120308070e030705010e04020304060b0405090a03031a030a031412010306050117010509060703020915120106020d0504050a03020f1305090c0315060a15020313030507060f0302190503 86
    0x440c1c43d226142c3d035140042c9111340594401000810b0444003004528000c42c0c080c00301c0701c050f114615210b902c4020710020f500b000740259640d80c2d0b03501c858401500c0c0c60044a103d410400040e210461407450013500329082050703030180b5400718050501068900090360350505130141003140c000810440c081c10a441109110302003422200000010404181c020606a0703032036201d01002031458510a9013200c05c1115080c1041c0c0c070150210303c15902960042443d110040c1c81c6500c0da10076100d1b561002d50142410170072880c0700200400c041503061116a82e00d90451602510705031802c0e00080181c246030001920a011229007040340d603a03071a4605201841710b0358103212a26041106944902c0c041c1d80240c000d000b002c54a5480c0a10144103921580700245254445820954283c4028100b0400301c403d41c802040f440880c07800c1c1e0007245005502c1040107102c800d007000030080100c003034845554145401400100024809400146682500c0e4604541c4a503100c000e1100031844078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 28278665 1250 28277415 28277429
    0xd080c011b0f0206060d02010e03030d02040e06040e070605030f180d0e09150603040b090c030609010504020f01080106020a030e040605060a11120f04060c051f09050f03031009020f04 80
    0x1031070541c44540c000d804445070540e469201400c005440d05a0b100c14045a80c154004440760f84100150f01907100740700c0d0100098106c0c0d084c08411400c500807a4060340080344c600041200704101c0d0314150040300c82000052020b0030003a07107415000340041c0030103001c8090483c8200005801480000110360702c90707400608072504180344650190000201c04019401102d80c0710000e41100448d1001240c4440c0103021503180d90740340d44881c0ca000201401030b8140b4011200301000540e820001140101407a01c00041c0e5403d1074410049001d82005400d818014030400420100d80c021031400b02842d010b091842040709040c0009009024507042598003100c0401e80420465100070b0f21140d00c1440000c8480e1410bc902600c0d43c2c500880564610f5070b4003c100038081380d4400e59905d6100d91144049609100100c02d1000c89880480381818100e682c4074400e41c14071504202c00408176070340360082e41c40c42c20811120105254140210822941c000035150411b00d0070000300c4000b0120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 28279915 1250 28278665 28278671
    0xb1905160609150501170706050d020f131401020c010c020f0f0a0f06020105150607080c0c04050f07031b080a110c06070e0901210303050a0905012d050103050604020d080c01 76
    0x414544462855009a0110320113490000041600048030241c000101d00c0007008020403032800300212415840300c1c100c0c3e44115000c1c400034411540902c050107172038014a03800d0741c000303003402024960403c080402e541150311005c559940f0741d03040705182c0650354040d2040708120301e008000c5804181203a4042c2c0e0428054030700041c8614001410a083e6191a4000d21603a00d0354802c0b40c00d0380e4040a0240e600c0740080024400044512009002d003501d0901a0b07014a01e01c1c80003d012038008441e80300c5120304000800a08236414031404007400c2040640d050a5000d40b07000030a44030f00100601c1d001a074030110103031000140000d81b02c10300c1d040c100b00c4240d4a0184002416050904007841c0102c1117840082180c2c20399101200451081104030790200d40c40391400c0300900409484180308655649044e00840c50a008802008040081e110240303c491482c80f84030798446a800c0304c4062800c4014070002c1ea001c1041d07600140c04940c0d0320100d1480d030400c00316610070800c5120381503107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 28281165 1250 28279915 28279931
    0xe100614270408031e150402130803040602010209040e0d080a0e0a0209040f0201080709180b0d052407030603080327030a08070e010804030e1012090305130b19051606 73
    0x10034402581704080500c45005880c0d02050440c0d0001e0b4240c800c02c48104102ca180415414a035001d050701c03031101d45003d405039655890003411580716802680040c0d40026410203a410103000b6140d60141c2c02e0014034401580c0180105540c001610100c001515003050f2582403804000141900d90000d044003160309051404c001b44a05a8000302e020450300c00000c1e40d0306000e851001c0c200d88a03003012522800d10b01801000130101d503071800c0d80c8881c0b03207120040031482c1005a0100c004101114405112072083c1c02840318400421b224101070a048081c00000d4030b0009803600180c400781c0f407440e038503039150070b03d00707482081d002e142094071000c100301e10b120354001032943c09011980c03648070490500070011100c288084401030302040f80315101c01480e0501605140c08243c0d2441e22581c3c2da002e01c0e18190035079031351007420350001e100410f41144404501c03a6078002071030300500140c6807001c0c0341009070f486840030408009020012075560f2444002c207003a40c0c82da0343d01410810000e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 28282415 1250 28281165 28281173
    0x20325030209090102070f030804050703121d040204080a0215070b0f0a200307081b040906050109050414010519030b01090e150702120903030403050601090e1006142704 74
    0x2281840264880c49031400401c10010062080359400342d00445a007101c201c4a44081d103104034058012590303489200303800400b10340001c10003c079003016666680d03014150203500303141c403091107401103205610400040001483c00150100140c1d4140c807400c0c3c0e0410312044081c0d49000f0b001c005015007100d90f041108094022100078030548a0030707400c21075030210907088110001c800003510441e00c020808684040d0040508560108001041e5402481d149071002c0840e0805c0e400502c180d516240140025a004010000904000d035000c0020320507100b28480010360600c5580c1c0034592180311200340543e88540da02c041c540028403ca50b9507900c0c9211001230220300c001042c14043c04044400a134100c82c0001e000e00e44550050000c96902c00003418158065600250705102c03c101c0000040d000303101740f900900d0030910000b130040908081504281e41c5003024001c0600c3c0c11820705c04d41e40710000000d4659429180c00903c90743e4041448038460030130120034802051202088200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 28283665 1250 28282415 28282483
    0x501020403030212090604030f020f0d03020717030c070306050720100b0612010603020901020f150f01050a061407020616060603032601170c1c030201050c0a0c0f0203 73
    0x16840790f400c880c00c404406000b2451400307004a103603408481004204082103e0000c848080390000304103601c034549000001d00362000b08101140540c108003c05c002c46101c0605d002c000c41d415002942ca41054001e000c1d8030392040d4000244002d0b41c481c0803d44080c0300d8a0000056401c80c113421101c8003c0100080e6200901101e00c091a818103403440c01c9401c0c1482038545c80f142100c0c252074264246042034010350402c070001030461050003200490341d0401c11940b01d010070009076848050a0020520413113050507000240109024130081001550080628880241d4800f005465880d6440040d00030300c41c146000c000100054111010701c4543d034072181c21607100351078102400c400d984010a04820b03850403444030040000040011448000c4500e660300c40c0031003927590301c03907c440009401c1d2502034042032040b041c02200b50700301502442010740101001c0ca0783c0f42030800321440100503800d001801001d200a03c4030344021074038204988160366a640d0036002e1281040c071012408 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 28284915 1250 28283665 28283669
    0x3090f06040b0a0c050a0203070b07030b06070605040210050309031204081b06060a05030c150d0605120706020d020303040b1801090c09020d1103010312111005010b0d0b040c020309040905010b040905010204 90
    0x3c80303140c00e14070200e15004108950141010344c024504011903610380b020310300d600410144c00e041e01c4880b00400380d80e95000403c0c040303125100018403401c16005000103200503186103c24860200180140b401780002039130702554035125003082d265150316090b07001c0e0040da40a0070300c0700910020a440e0307403030120f1401d1044100f654085494ad41c4c9030105580d403100c1045030741e08080361404100c01e10701c80600400341a41007190216400b50b0f5003001c1071801d803413100c4011658100c1c1109020340740d418070040b511100781e840154103504041e00c910362551000340401c0020609080300d0700c09803800b034000c2850a9040b52000c0344640d951100d940c0651301130354601500310f14050028003400e107083c082e20305981e0402040240d070300d0922810b8490450f169661440d910030100282c0c03861102e406014080c1910143c00e40d201c0c103c6250413401c0e5590004c2080c480c034140300115065542c0041503800d1008103d50100302e117001810001d0040070340354a01c03038002e402d0111160a0190540080003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 28286165 1250 28284915 28284931
    0x30607050403060e070513020c0703080a17010603051b03060310050108010e15040c06051c0207060f0e010b030a02041116050601150215040609031202031f0b09130203090f06040b 78
    0x1103e84e044103101a103c401c60700406d54441e401c0041003500030055400741483d010741204a50019403a5100c03030071240c1000306545c00203074500040300c00407807214540360b00500302414184001c1c10320100d4580d08803e00320820b45031050100001e03160766403c0021161010140030200030a50311521200e003e0f01c0242070300d80c041d100b43c0300603d83c03211012154521032501304200d40501e82c180b080c02c0b00c0c3c640c40f0345002200780043d000c0d0210b503a0f55a1008007503041c41800c0006110146280c008160b88900b040c0000c16403501744940181c1c1c90205134413640d03550403a000a0011901807600f1024026100103503580d126404005041060001d203090503141e901e0150256060002e5080383e58501e44103054502844100200d400140c8503040303145d540703100c0e06191078062042c2c0d4101049030070440d18400604004a602000c4070901c0c244000602070b090015490a8481c3d4081100703486090a4240d1240e400000601151424089201401d05d1041034600c9410035090400b0106c1007941c0d010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 28287415 1250 28286165 28286171
    0x90b090d020714010801091a18010510050403020f0d14010603140f06070903031b0b0a051501030c09050114040e04080c0706020a0c0501031e050705070c05060315061803060705040306 80
    0x3c1004250065162a041d805964074070660b802c01c40345030054100040a500c120410188030300095076032480003c042c0704240d10301c100940c0350004100050010324501e005208003040140090384a00100782004282510b0040c203450844c5402c1a401101d805c4011041d46460008401c0020021900301440c95100460741e0074005a84420b484010540e014001f080700d201c170420009005e0481d040d03450b6404180301c400b0801c00d495054070a20111807040c8041e030740340c0812144c1d001d10f02000010040a1a0070040c04012030805040d0401c64000d80c0e0502c503001c211041d801e6000c00485000e4a0b001480e102e9a0409181034859a08458845540307070180b25408290280f0001c0c1c0034840e01d41041c001c400c00740c40d1800540041242d100441c014004903c03005000024600a650040f1140c0c0c1d51540e844500781044211410507401240c8200410414403070406050354250210541c12182c080d0303501c0ca649000c07074035841c0000299405000f400d041100701c94200000c1c0080340c3c0a04c400f8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 28288665 1250 28287415 28287419
    0x605010b090901060c0302010f0203010f1e030b011710020d050f01080613080702060d110a0f092d030512070c1203140a0e031f0b030d020304030609020103090b090d0207 74
    0xd45050050300c1c0e800d908100341e000100004e030f108080000b03041c0d0013400009900c02910900005980c400d0700810328000c0104010007542c15040042d455020151070503005282c115503410000d0141071040d948480c04044a600c800001848840d100e1030003500119510204070702a8400341008039030180005800f10f000080307010780130481301e11401c01c9502000152010b0b6403003e00d1034010600603038209806000420b0b54064502c40c0c0110f00c28180c41c0b0702d84809024500510820100f0103d5080220401003007100c0c5032a400781a0700c030408040503540d4145100714049896800d64806090f600c05c544c1000c4920701c41000801d42d403030007141c004070095200c6000320702d285103102c030050009007110104510484a503014040d0442e01b46013072400100e0310000285000c0382c42034a280c41410840e9903040b6690280302d100152142900a42603914607024085d40341e014030b100140055803150541011a0b20a600040185a00c82d50210180c103040c14803c0d540c0d070010b0704140c09881500740c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 28289915 1250 28288665 28288679
    0xc010f0605010c030804080d02070609030c021c03090b0a03090c0905060406060305010311150c07030311011401080303010603200304080a0906020c0604090209130908030405070e010f031b090216060501 88
    0x69030f0320315019140e0306030980344c90b99007210b5580000c1443d80803d500780640800144036000c1c0010380740c080c0d070311a00f03492414010020721402c1602c0b0342400e01d140046440003e600003890b01c0c1210a4500e00e21349400440c0c4094000d030107604402400c1c003400c00c002282c502c40a0303102500504090b241080020f0700c807a0140d044510a0101078120340e0568281401407070102244003005440c075007003a04002500b10755524040040d00200c000c1150391840c0b1803004400d10518120381000b501e290100e524062045490b03220600640d4101925407507001008140314000303034043c0c01d501d012140e40c0d10306410480450b41200c5401c50000785610b90014002e480050390a403c560010500c078506490700249500a500101c4860f070843c554501c0c40c070300010944500c04015000313140305607032071601c0d107045414504235800500d003440c2e14000601c800781441c1400e00a1300c1d40544810401808420360031080000750744a425214000514850308201020071884254032403141444240d8071158 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 28291165 1250 28289915 28289927
    0x106030b01120309030203190b0c0304020609010c05010204080a030f0f030506030304050111010603020316030506070201020406020618160906060306050306060612040f0804030c05090a020c15070509060c010f060501 94
    0x1101800d84005000180112019826a00c0c0103521a04140f00c103d42c0d294046070030826100c000b829140c1118880b1003d000c0c10030001640500900c10540c614a8942d0008a0354020301503c28108030014060008001c0258102c80140000c02c0480b82552480d1070700a14210074a000308001032605090019018040d000f2240500c2c80103000d1400d107800c0600465811002152038200340d901d82100001585061290310708442404080c0311420303040d420203c0c5808000303080740d0216841007004101d01c5a02260158006800d092803d03d02040b103090300f850402c000720046186040740c1c01c009490805540329030100c520b00d0300d080c821139903103108054880208549050708420100400c03000800d034140c4440e0710a101e0501e00a40e001181ca0350316090b000303508111010301d03a10a0601061400c500500c4c0c1c002d08151096142480041440c0e4885180c0d03910740c2d40131820100030074100c1e401354060f25003060340030308019220201491424082c011500b40102c44c503182000202c0d403540300305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 28292415 1250 28291165 28291169
    0x11214011406060c0102040306020f13050a0609030f0f050102030f0919020d260c0f010501050405010b09040c09080312010f050105030601020d080c09040c0e1813200a030c060f020106 80
    0xc03104411982e2008240040e5501c46071030032486550030440480041c48502c06803011641900401ea215a1001202081c100a85c6c003c00d21030310384880304000b52503028203032a00741c90b0300c42d03401d240c003903a2881c00d413004520302c000003440c0c0c1d4004000c020107860041e034010710030100e09088071180c0c00307024283c01c0c01441c038003030203904009410071181c00704103040c000039500c0e0148003070f200d400100c501c0901401e801a080884e0150451401030b401048240140340c007500c2c049a0030807185d450140344101d03a00c11011900c0c001c170740f6640e6112040d4042d800d0200104183c1c001d4954607200440d00100100c000d02600c0c030f501a50510200e1346503c10003daa1080006800824003511800d00c144c45541c2c0090002402c000308110b00700750360701e41c0e000721006031010b0384652a01c1d01d008410410300c02c90790705c2c80b0194419501c0030822600002038190340382da50003050501c6034030070070181000007010924034240c112184640c00410444110700b072a044070390f40c0c1d441580004d03000130124240c413264 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 28293665 1250 28292415 28292441
    0xc030403110a0801090302030301030615050a0302101e0306080609010902010c03080928060507021b010509030304031403040510080f07110c040903030203010501030c03020f0301090209060c030301121401 89
    0x5100500000d0048408404240300007000e5009550f960300c2c1042c00c0d104c42d40012001a0404001042045401c0c014040c80b00804404204114282404039900320f995110181c810594040b00d80c443c90300600d28055203940d51200e28292117a21003002d03004c0c080500c02c61000303200d032a00240c0303502c00621a51088603030507554840d00c82d54a80f01160081340c0605004440d00035060304000364030403203c403140001e85100110184140c14103240040b0380d0010605015504010200c0030242264481c0e0031040100b404c0480c0c807402000040307071550146400042103661400c0c2000c2e07400714004047e004544040310100080740e40820201d40b41c02d019a503080c2108403d001047c0c03094018400050300c0c0c103c003012901e20780940e2000800f60340700e5460940101c5c1d40000140429613160141c0c00d084110390406510300402d20440f20281c0c801480350940307042d40400c244000b03549060441e0480c6805908981c0c90303584401710912403c0000700300311154070080405100000060084604216607 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 28294915 1250 28293665 28293667
    0xd050f0a0315080708010c0906020c0f060f04050418140a08030a050c070210030902040b010504030f06020a0509060d020c0d091203030c0324080c042a02150703020703080109020c03 79
    0x301002a40030304800c00c0891491240801d02080101c820842607004265500010404034100c45c8040c010442c960400c0086402c034408103032030340d12800b4424520f10b4050360b01507030300c0040a445d4007603400340ea04071a9109040964601c17851000c045a0a61940100c040b44254200c0c0c0441c1a070740c81110b100142504010300003d035401d405540039551084500c06454506001540000d001c1d400040e25103010030707540c204803000e606082c8940b10705c112082c2029031425085d6200d00c6050000404028412900001c04a01443c41030f41500c031030f80d0020b49034075120b6030300c280c2e018069045042c1811715441040042e00849110700203200c00c540050b109a4820717a09a10f0403005001115410800d042e11a982e500c60f10442c03280b1180e14030781e4803110085585c01c10216504100b103450720309102d02c0c14581ca5a20100700f401c0c0c0881c1d032003018220001c0c6003801d0380050342409800540b00201c0c0c0b01c4c020801c862250141c009002040c8680c2d034001040e138840007003400728003800754582c1e2240e03c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 28296165 1250 28294915 28294927
    0x5070315060f020703060f0510050f0612060f03070617100b0a030903030b090c0c07080a08270901090518070b0301090b01030f0f02190903110105030414010509030c0d050f 75
    0x4001e00229100c42c01c584141d0b1801910307a1100c1003920607030b4155040e100e80d5001081980d03014600b041010700b904942d0220314901c038200007006030003540f00c103043d031022075404984103070703a24044110300da0f1014040d11121555040050507040040742c0f403400001050001441d100c0b841548501a85c1d2805a0300d4280130b0b50450031002000740c55011005c1c103548a40170081c50380d4400c0d240e4420040445c2090360359181c0c1c0011400c001803948071900c2036201400d140300142c0f000050300d0403078001000c07509608100d00018000040d0300394001c1d40010040c0004102c01680d80c100d01e200b40c809024442d50b20444010803969004c4501c1784501038241031005100b03150440c2c11070b0403800414034002c11084c0903503980104a03a403031440001065400075044200340e450002c008009012070400704c4859280d82c64070100468034942c0076040210010024041210006820043c0e0020320001c0100b4a1f01400c60350350303507028028102c80340c800c00d0890914644590111154903080303800301c80c1428 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 28297415 1250 28296165 28296167
    0xb01300f0308090309030703060605030c0904080909100b070c03030f05090a030b07020c120105060a1a070204021b010e0105010e010f060516020111060408030a0b0603060315040206160302100507031506 88
    0xc42c014104281d180410000026180d90030090000518094880020700d94549410149800e0060066600480401d82000b001c2009001500c00711403059a07441065524102d400340c005200c1e07000402410b0340843e400d0140004074007641e0507039109846c2c1c0380c2901d000802c2603a80c0c0c0241086a640101c050034140300003030381d031000c00d600103905d0f0044484c82074800c400150517940e0312070541c039140c0d510020082c00345041c8030008001d000e140d10600300d00b150660710b01c2d51b512903441c01130b000b150001000740350711801310448041c030305600c0000c000d00c6504006440c0606028895413403012085c1c0c0021071140003401c001c404503600341e01c42e1403500e141c001c010001002c8a400c1a4180070900102c0c80f54800e043c054a44550302c240310841e56458000c0a160855103001c0c4c0d594084e030014400c000040d100000c404401140921200310150340d5840040c883d8881c4920340c60300c00d006545401c0805400007960408036500316400c0c02140e0300c980e4210200c8440048000007039070110320801501d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 28298665 1250 28297415 28297427
    0x203010503190c080304030807050105150105190509060c0a02090f060102070918020306070807020115030f0201080402041d03070b06030609062a0f0406020d0206010b1b07030b01300f03 81
    0x903c691418040107030340c0c0940d00d0441e0401e60094568000001c2c40f6820070000b8400d26038042c9070312856084404004c00000d000b40501d080b414101481c075031900e440d560240094620240005002507560600b6084040e2030b0040b00c80f04034010042000400d07108124100110b12600f0180c0c0104003851408480740080d200ba28008011442d01c1d08180000da2402d1000900c0b0b00381e10349030a00e5a00704488028211107400030074411000100e1420f00014001c0480704090075024a0005580e44032400000d00038603400c050341c40c03844a104c080c080076640201c050102a13000e480d0400080d500c000030b25842700f804403013554803504488001406001c0c3c1155a500d0840840d00142030421141d409451951005240c00440000494100252030341040511030070301c5240302802455140c81420f0b2440c1c09445a001000d812024480080d2281006100001d40d006480480c0650750350510451107002c81061012002c403010000c0000c907850040c000710194404460320034402c1c1a10f080b188 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 28299915 1250 28298665 28298713
    0x102010b1c0c0506030a05010e01080c06040306020f0c0d02161e030602030414030304051507030c0f1b0c03060507091a1213120e1f0504050f0409050a0602030411040203010503 77
    0x104090901c0b01003040d855000c0914070808808400180c99414041c071103403120344c160702050282d800220486015198a4141d030f084035488180561201c4410489403218001d4012640d0b692103041c0b55010701d44c1d400a0045003084d004a08094501d403500340100d240b0654040070b0b00100c1ca030b410100001107840d8002d580c014003414007484501c0c5200e01e5079007150300954007618141c1c050780300d02c1c41241e00d10120b942c005c00c0a0404021403180440c02030b00d1044010621400d000c2c4040b10810740000d10800300861941c010f60700300d41c00d074892410300300903d4103451140001d5100360003c05c0510640d000e9518061a06400c903003498014048500801001400c400000d00c042070054001414100d00a00360761a0781c41d03060300c902c140c2c03080c0302503a8104080d0000b924000d5814a0800d5041811181a1f070400e9a0341a03222800c2c001040242003404d100601c01d11410220005000a5070702941c003c0703200b100c66031000da007030004004c140e01081c02802d81c1500aa8100012100d0115510300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 28301165 1250 28299915 28299923
    0x1012120e06031305010b010f0f030b0604080307060539070c05060703020606100e1809010e0f03040602010e070302090105090402030a080c01020a0806031b060304050f190302010b0102010b1c 83
    0x1104030030000129071107400a9038000b00d50b112040e5541d042041c28091904024004c1c40c150b291000c04800c002d00d50341542e1200c50900d80e8a028000c044d0311003800320307030180c404442122b45d10750750b41c9040801001d04031594825180c22207100010344094101121402c6803504410b0409008945000d440e980b0001c4100c95411002900041e1905c070580946102c0740a034016011324a8040c05000c6400d000801403810088580e8820540c1e42d5281d099420910b40001d444e041683d401000e00d0040005082c0030440c1d20561f030172890003100c0003004000717071030300ca43c000d10110150f02c6070307640d9425060000175031120b90400107101605010b000340d5440b9000030125141c1403140d171201207013075021b1030501c1f800c3c1c1d400144001c10940c000c9803558001e0003d800400c1d014590100e03421840c0304150519220309000000f08007030107410410002c4000343c0500f9101c4a0340440d003007544100b18200101d0240d402c200c0c2549030f660062082560256010b0304200d10304041a40d0080340c000e58040450b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 28302415 1250 28301165 28301177
    0x408040e070e03070b1c090c0603020c010209060310030210050708090f010c0212011d12070602070206040905070c0303050901020c070612060902030a0609060509010308120601090302190e101212 85
    0x1000340c3d401c1001800a0480041c8155606100c101560700c49980711022580181801d40070000184207454000c22100340d4900113858040b8110100d02a01c03506409951000340801800030780210032042c1001c8a00c216159013845000341c0058030203004103800900109000c1c412100c65003881c5e4480844940140740a00076100c40780d000490410f41d0300c1c01400a030b0354821842d0910b8600c1c031005484103e946006110012112001c0e1482e445a4030000344103540201c0c4010454507008240e4002d048100300a00c9280b405070001040700465820540019040030081451140c0604c01c60346580c182002400c0604d0425034191080d10b62800111901556882c1c000380005040c03006d107005054540f40170078241c0c03800d2050003d03200c042c2c10040c1f01e4803420f001000002d40c10001c540381c0050601000c000b82d601d020068407807240aa20294001580c10802c1c04a80044094007003980c01d50384000030305855041c445075014000d40100d507949503c0d40b05060124011401921012407646016 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 28303665 1250 28302415 28302437
    0x604170910080601020d0c020307030f0f0b0106020d0f030207030c02090912040909021906050409050c120103050a060f0b0a1802090406030804060f02010b010507020904170f09030c090408040e07 85
    0x110301041d12109007040040c0c038140a200140d0b80c10301c0b030880d95081c10b240c4144030103803540000391035110078400100181098070001080040040306002c0e5a6085030f82c00c034456a4550029488003400010741c000291030b1645000f844e4081c1c400d903155a40c02d030b640c251100c01d0650901001d4880640b000300513100d40c1560307200c15140f030001000a04820440896000000e02c148031400d07560b250803c0148000340c40034404554807505480071201001c1001c02c00c0d0b03c504c1c592200c54807540b940040f10008400000c030034402d000400042c2c00c0d1003041d00304005008005084101d410039035000ba40220504402c0040c142401555048c2211070200140380840c8080050100ea0302c7d179104548454010808001c82a00180c41442e07800305070000780151300042c0c00007040d62052100c000e01c90703010b05c40031805200203111030795520640d480c0d003180d58039005420f0329203d0300455940340c8241301d00c1d034020348582025040d0074011a0301c06111814a410807030130351700c1c54200422a00803c402c02103c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 28304915 1250 28303665 28303669
    0xd0501020a0e0f030303010b03160c0506070e09240105090102031306090303090b041a0a03021603050d060605120f0405120a0903060b06070f14030904140f0f070206041709 75
    0x1e05020a0340c0d12207166002550b018008501d000e81111842604240700412041883c401203d901101064101558038811403007a1002941c12001400b184034820801c00c0306500240b09280304841262246510b940b0041d08421005503900000030841032001c2584043d400792000e0404000d0500580381407180d4200003030b995148507400f910005800d150100180b52b0400c60381c0d009080e0413412140fa2030b0414000c070350030a8a02401000e08040010a210700034400d505403184441d0070030603903881030601d081c0140103401000c0403400c1240340c8903000603554019401c5801d051141d42c0c030107540c0e550f003504009551000800070f89050082d4020001d100e248140200040c80082d21001c441e41d0844c02d201d001c60b1305240d03189020b4141001070b42d0203c3c03810205885561381c0a400c0c0100034007418501c1e401e5011700c4c521b064000d403e0100031560455080d104038441c0380200c3c446141c40ea41e6500e0000028400c0e19040f0140e04a00081004148480100740000c420000014940000440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 28306165 1250 28304915 28304917
    0xc0d0f03110304050c09241c060c0908190b0609040501090803010303020a1514060d0501020912031801030504030903080d060302122b050a0e0409050d02030d05100e01030b060d050102 80
    0x5003c4134a500040798030740e81c40c0303010b0485039080008140d1040208440000c4e2030111400340344c1c402e01c100240c180a080b54444204400d2000f54804010700036841c0380c000140020341d071030040b800039005002d2906070110104404006054000f188803009458100a026814801600a5480317540f42c10385c06010812030f5000f9802148668018203500322a0b080095001c1d00303501d80c4c420400d090010742a0801182e403030007500810308441c000e22090040c40c2150082c0719240c0042e4000402103040c10890a01101500900c0c090101603c4520131081c0110100e60007220020085030b144003090001c00e01d000c02070704080e41a6080010f4044d100d4000442c0900b000d0700c40d032241d5100c000080300b05402d5041c0303618014520500400b56612068000c1e080307010b4090800100540407103128416a03035074101c0468240c202c01a116031a6030035000a4480d8004454402802c0c10b00d4042403001d04610194001ca80309081400403d9003103985000140e100038003644c0d4403030304039600c0d4000b083c001e00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 28307415 1250 28306165 28306171
    0xd05040f02041e140420010903061506020f07050603070c0602070b01030b0603101406010e01031104031202060906010807050603090c130f0b04021602210d0f1101020c0d0f031103 78
    0x1e01050080c44120032050031340e49501d03000744001d010001071000103145043c81c22088038500812030040042c071401218a2034190307001402c0a414500a80500000c40d61035909441c0c2c3d503429900c5080d20340c002103030350316554411650840003c00009450b58402c03a6103081c0244211005440c014280c5c4900080301002c0c0c0003505d03484403240600207035140420540a00c2c06007005c050007180c55030340f13610015020080416040c0101183c1e84d8420381c0c4290b0000310940504001c1030b807500e44908007840901810246a0050721407007010801001c00041c031103048401c5070340100840ba0078182400304541000d0f0071b05005200c0c0080d250015982d89d10b034601551103411b400140041032807040000e0b106545811801184100b000b20980103454103071588140d010380310b00301112103003440f050340c417294040e00b81c9250240c1c8000c43c81030742c1c5c0301464491b01c0450350348421030a8a0054494200d12615010019030fa01507841049654018500c80000c1900345c100080c024030000d5089005900031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 28308665 1250 28307415 28307441
    0x30a17090a050d0b040201030b0402070507030503070c06021603060f061502010e1209090c090d020619030c1103070308090304150302090a0f12060b13020403060515150d05040f0204 79
    0x81460034090522507401001000308481c07480690001e078480424510014001034100b68445010100a89070382d0100c90416038440105c44070300303580e810810744980141c40e00301c03a140300740480096058800210020352009198503060002d1840c0d440400902110070902e40c0c00c0e440701400941c0102c0d07841c00c68030800740ca400100d200030304205a64100000550f1480160b1414002c1102d107440d1441c1c8180e00c1001010b059584d9060b200c0061851414440000c2d84070400041c464a541d91400040c03a03020f005481c141316100c0c945905841242c4c41e000702070802d034401c0c0602000302e8410780740240c000080390180c0345003641710b6042032400d82238010b800c0c000c41c1c3c0001e000107581c140406040c0040c01c500c9090480c032410846401d841040b4500d000d04443c0d1203480d54441ca81e01c003180083c0011842d0411941c0d95031301c1c036007023028041c221240200300224a001000d1410040903150100c01480c007454034101003035140d900100006041a0b44010003440c409006885a128080f200800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 28309915 1250 28308665 28308667
    0x19060e10030509030714120f0c010501050604030f0b100e0703020408070503011505090c0409060f0602010e0c01270504020301030b011e030203030306040c05070203010c03020406030f0e07060e030a17 87
    0x418032614004a54240d0105842d20007000301080c00801a204d503554040c0050014192202441e0f203800c14003009501800000582c200300510040020320780f1000038070003404141e983c0c50403c2418040c510000d0900e4080f89403450010308840041584101c80b079490141442e100c8d001550420821900140881ea00280c01d005c603001c02c214140c01000c0490007884424078003640040320f4400740c840c481c00340d41d120020070260310404090390041d00c03050718100050395680c0c6580030b4102491040c44055403826880c0c1c41c400304c1c08603491030f4800040e12000c2c80fa118444088041d0210f4201211310080c8102001c03945945030300055000314010201005954103069020341c41c0340039034000030340381c4d138015001b0401038034088152035100c802207500107070801e2000c1058031540320385a4000e41c15481c100c418032480790103038054810b07074045035000c100c5c0b45001d4586a00b05ca03281e215108403640000030401100b0f10078803411280034005416030340c20741056510840408054207022440100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 28311165 1250 28309915 28309937
    0x5150a14090105100f031e14010e0a020a050306040b0c0a2309030607050a0909110415020114070905030a0204050601051201030f110d080319020c0703060207060b060906030a05061906 80
    0x1c4c2c4040000d00704400100480c580fa5940760b2040000e9210704041e50440d0b2510281408401d070942513010354680d001b1b100114140040644035000c1c114200c0c821117090303101160a08001034120300c55036000903030074400d4170380c4d02c000b400980098140d4410841c44030400320704400c541318250100d9003002c4c0003079228020003003094246403005016004118040c0484080746501ca00e1170011110038400008031201407145103d0703d407146402000d1205c0342c1400410400794154003d09240b1596242100d460b2290801101c00401c05c1c403445030305130300603071005c1e002d40f40c60381c400c903000541418441d180c0881c58082c00c202070300c03d0f4000c3e030340c1c0400100641c00b40072201071a0700c40041e0440d07141241f00202d83d20f41c0c40b91300029040319100d800104011490340c3c0305504581c4031221140458030f605e03a807031600e440a5444482c08942081c00d01d541d41006003806810340e142120004e042070304541e583d071030103001014002c101c0384d4092406a40442c8801e11403503a40c01070a002d50321031200c61 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 28312415 1250 28311165 28311181
    0x1f0b041d01060509090f0402150c060a0c05090a03020105130e0103080406020f010c1707020a0b09010c030609020a05090d17030703050f0702060402011b08040e01060203030603150405150a14090105 86
    0xd4816400b55040c0030013086050450394412510f10390100c00020341d810162100c1c0041200f03041010b005410701c41d0001421103100c600003500e54401c0c5c14069003800400c403e508115500d0250740756441e00024150800e20056001d100030f080344034100400390980550b203d4601c8a071020030381c02a1102a0001400d0011990500990107e0040c1600a0000030f4000d403008046450301200d4415901e04039010030f00c081d100b03000840300c86401091105050421400c0c1d58000c00224483e040800e00e000d000056451030360090320010090307916607034200030b85507040c0881c9041e00c83c021680018985c00d64003076000c10601440c0604031235500080c0a29001c10b141c40215000740070070007998044030070000140c0c4e20100c0b0006407071403104401c40d807501900d07040c041030040303820294115621300e00100340c959001000c0d5100c0c0030200c041702c1f070541c00d04003d03244000c0103aa005c0c0160704a50801c005006620200640050702040c0011300c0b0340049912612044007511580217694482c3c007806022 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 28313665 1250 28312415 28312469
    0x20d0903171006050f0c0a05010e1e07080d08060109090f091104020c0606040b01030b0406090917040605030c071505130c050a05130c030b030615090705040605031f0b04 74
    0x442280c42180501070f080c020f002e4524003c00c4241d07502c048000480c00c201200911003901c00540c82030090140c0c0c002c2d01000380c0c581c10316031150510301903581401e01680d800000e801084600c41741c0034158280a0350320882d20f0384802440e0505103c1c420780c00140700a454810941c0d40f02001100142601c0185002c84c1d04910003400c1a100303074010300038200010004260141c01c008102c800050f009100001038000c0c141d0705c0281c9500c145401e000041018044d00440c0744588614904015640811000351089c09036000c1d8100161040c00005d40d42c4540d88010040c2d80e00605045c1d00428140d0441800c2d20403c580c0c1e0500c40700800245001c108031100b543c40031300001c0b01d0072886681444080b8446140030820a000309458260b41201c080c0654054100c0c000c015080c1c80300c80c542246100000882c05810500580c8100000b8031958414001c0d80c0c00c0d519180c0d1414030b980c941408804102101000070104e4088107480050140ba40030001c2c002032815000c48040d02e403000c003400f090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 28314915 1250 28313665 28313671
    0xf0a03030507090e06100e01020c0a120209061c1704030204020f09040b03030a0512060d020a060203030411030105040210081b03100303030605030f0d08090304030b010905090c03071503020d020d090317 88
    0x101044100c01d05c155075480304d016814100709850401401c0ca0303d403004074a0200c40100c0c6a4111059101c0441d005c00c042148401e000e0007994018059240e6205102c161030f4036072207804902c0700d00c4043e50001010008120b4014550b2252203081581300e400090403a480036826040900700000d0400b0380b410300c2e005181540703504070051070401d54100d5024042d031107540d607940c0100e102040000ca0319550740c400712803141e4026041c2c1059a8a517074019503294025107090342c44602100007041c0d10300d01409140d201d26405000b2140400011000307a411010150081c1e4100250b0302c40c10040480c0324025510a0300351340030f40d0340c110745103090140480c0c000707421560007508103d580a00c0400001844001c0d421149462011a940c44180351f06601950b04001c103406020000080c04505c0340e04030318043c20031a03007600e407035800103401c060b903642e818481c0041e04144030000e18003640c0203074003402c580c0054060251400003c1e000610450752400011030204070314000f0142c0210800c02c0480d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 28316165 1250 28314915 28314929
    0x101e09050906190c02010204080d030507090b0c0a03110a12090609050a0b03011202031e030405130213091805150405010c05131503020408010207060509060c040506090d03020f0a0303050709 83
    0x10b82d04260000b1882d00d020790040510140d220891000213910035411030700142a04819901c091803081c100801078441075030184002500000b01040d081c0242c0121355005800f400242400c01041e5806d98044010024104890282ca0b5000020a05550032400840c4031542d0b280c1c0d0407400d02401402907401b41d085540540d082400038088580b03c1030849047d240300407150b9807007000034030001b03161030300d00100f0304484000441e020115000010181c0140d4000305c54808403d01c0c0550070900300d0142d01010811141e000d0401c00160f40c0c0d5038003145c010340752041c0d180800815507d07160715001c0344421886800080700c040000b03001c003c0c490413901446a00e403940c904034142008145150542c06030086403030080d440d202d5803e000340d0484000385600030003507484462606215000340002c80b5503811a0040500041d100086070080f601070b100010005418002d020040c403200c2c04010710100d0a5102d03070003a09007003000411800111300d100355400b00f018a058100103100002a9008603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 28317415 1250 28316165 28316173
    0x309152702030a02120313060210050a0207020609090c0433020309010801060e030106031a160e22060512030309010b0103090b0f09010f0c02030406170f040b101e090509 74
    0x240142e80100300c8014040d0121400e039980302c40ea0321900c0c110300c01c0e205503200c40b03403129a0005240d6008524004000d444c890200100d42c0d03001c92400980c03040f520300070b500102c10440c0030358918111808542261034100d00d603040c26240c1c19201000d4042c0f4107405007030b0f5181d540c1120411210000c1d2140347e0381503c007035030611a4480010384100f0301070140105020300b41c0050f1030f82d5102503000400440c0c20480e21030107864114115501d4001c2540c01c86420071a854444076458011466a46000809400c0200d00500404000032025207203540c0543d03d0384a400010345941e402201e0260315075000041d40e40e90402c1021a8216030b24940303814149401c200300310000c100d01544c841c0d4043c041c10145001c0c1e90340c90411f540142885000c200046162420442209500001400075a9240d484020300901c034051014980201240e82e00c075a1401140010002098080c0490700020401aa0b40f2020340343c01d41d0b641020091142d10001e13410706501000080d120f4054107400c000c402000d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 28318665 1250 28317415 28317491
    0x306060d02060f0c030d020412030e1801050112020d0501030b010608130803010603090305070f03050c0d0203030c0306060a050c0d050d1d0a020108060a0b03010305010207060c05190f030915 83
    0x2184050240f43d5507083c41c0c460200d01810150001d004442220014000071561035440318030380004e44170b1859007980000d150650801c2c09040140c016068404803036072905641e07180000440300500c804172180101c0c3d40a000d001c2100070a40030700c0c0e028504c22018440598100100101b501c1d000501c030f80781003100040d10001154000382102d054611a1a01141d9000b070f40c00c0903a0b071383c42541380090401c00040c00700720526034480050017a00402c07800b6600500d0140000b2a680d000a45203d851800c040000ca211403400704020810001207041490070a004020503500340a60022140301140c000100080d2100c0c452007025610407004895004d442618103000d6a41e00001c40000d042c4003045011800035035070b020b80100142030003001280e9130343c0c603450403a01070341041d0740c12940345080c000c2054206000301e064071011000c000107440e203e210504200c0c3d18405a2a020040c141c0d141c104001040c0c1002c1c4002c008004020003181b00001d120720000f40480b11100c4061020301502e403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 28319915 1250 28318665 28318669
    0xc030a0b0d15090317040c050f0d0209130606080708010608070504110706090c05130207050708010902030303070507061404050a02010f0203041a03040c0e041202060609040b180703020301020a0e0306060d02 90
    0x2c185204410400034604103c0d1030191481031141c0705d1801800718840402080000e1304401e4015150103440009820450a0500c140c2c0303040a440258032040820020b80410301702c0301502051070080c540072600380c1c1d0b0b03441e0190a2100e5a00001c444e40d446840900601200704004001400281e40401c01c00b0b8030290820114010240000c00d8561502c8122090080301800305000d0000100f6900c0d4605045810300003e600000d01202c807070091403030000e00c2d08418820700b492140c000d409145190780ea0b000031036003613000d60000c0300d40d15074541ca950f0020104169043c4079503c104014000141140005401007100340180011544104018041d4501c0524441a8207c04ac176009480340c5551401002d00d20b800d8000c0c7e4103004a8008100a200386500c60303401000c5a41c00369041c603103e19040c406290400c40d030181040c0c00710f4000c20801da001e0b4820002d021440c80075107440c01c2d20703030340000d080e640004100c03800500c640d003000e0320f1403a0910855070040812a00000b402c422540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 28321165 1250 28319915 28319933
    0x181209030b060f03070305070801290d1b03050106030b0105041a0a0603090c03060507030213060c03140903160b0307020f0c030a02040216080408010c03240e19050c030a0b0d 76
    0xc02e4000c1c1a010100c8866840800c0160082d6500c603055404650300da2260900170310303141044244004411039509403598003c400181e046e04090101d042c40d44240c0c94412070302c404240c1c0c441c04c18800d83c0380000440e86c00c1c812000610b02c110342406c40c652410b410041680c80302c0d03041c03c611102418030a00c4650707402c1c040d00308664180c180412220198141114031011541c0042c00310b03414841000074445d490b42c0148141c510034810348041d035440784801c0b110038181500c0200130900e500d003a8443c56060501074200004001d044545a40b440d01083c004011181e0020700750300307008418081034680600207070b0140d074100c4008003404201040083d98a406641c0d01170701490380000c01c462006109074041c2851600403a40958a41d03580300018020311031515213000091a11200181d034804512414070300018242044c1d0704c190401c00b9038201c0d290058641c1109541901446e0403482c0ba5000301441840108170250300c0c3e2170f00d48010016075803a2a4520300c07840c0040603040c000b9011b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 28322415 1250 28321165 28321171
    0x10806030714030a080f03071407030507020405280905061e06040903050f0301080d080f06090a0b030309040906060e060604060f0e0105070c03050604021503090703030e040f181209030b 81
    0x259070300c03007000601d40120f401c2070303240f900c06890804e0004900820b00f078224001e50040409540381c2c03c9c4c004110160705003a00501c01d000300015000c110030009498540c2140d60080c1c0325202035002c4005c1640040341403044042c42c011826140c4104c003051150a1007541e41c404d468040c15255541c08100040c0101d400501c0c1601c5a0394800c5150145403040c0d00b501c011216000c0d07401e580c1d585410007a617031070025800440010b11800c0011f4124490070400d075015010181c0941c1054990140f1000074041d02c840094146c07000340044406617495024105070b090207440001a5982407007103014096000070003480c06501d0800c0100200c03680a0080441c00001d0328141c0b902d250304400491b40c4d80314607075000d458240ba1000205c140600424268010341c0300300c86d00a40e8940800140c0711500040320782c0005500940c800b003012a01031010b0205a6070004c100048481e02001500121307040005005100d0002c8940f0b02c040001036002618020f1940c109000d4013455136581202100d801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 28323665 1250 28322415 28322429
    0x30f0213090e03041a0d06140607030e010e060d090b0c0301030822031703010602010b030706050a120f0e060f07080c0306040903020a0605090c030c0111060106030504020d0c0807060e0108060307 85
    0x207025182c103014050003a10080d103540f03e001d038011311602151001c150006140308590324a841c1d030018104a0b0041d0308024454050100c03400c1210540301a02e4461180ba00c82d8103100d14807450b0380c0650b40d41e4004100280d40404000341a21f5581420448040024621580f4000400042c00450810b00554441800c420f140004601c41701c503c00f110030055a00c01080340600c5107070541224201000345044c4c41444d40200000700c00b101c100356461340301780300d010040344007000384507002031043d141c80c500480c40c1007020034581c0207821040300300c481b46842004683c0001062001c800014240c8640004903403410216904010460070141d10000d0942445240d442c402041054002c0c0890041541c002d8407c011a1400369030068480c1403020034180f00707010392112200b40e0360241c180c0a600055400044c900c686c00d085040c0d008000280069a00c20308052040d00019401c24001002d07000c0e080207803030204d01d051009403a00800000303903814001840100b00390354600007015001c691b44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 28324915 1250 28323665 28323671
    0x9040203090a080301061d01020d0c0206031e04050c09010f030305030c300906100303081807030f03030609050703050103050a02101803110909070602100b060d050103030f030f021309 80
    0x12200500c1c82d101c1c0801d00104803800100c00020295007000340e480511901c016464000c0300e00303000480e11850072501182c049003001524401506001020b540d02c00c40d01107622501090940c0c420030000b200326402c842c05d40c0320004030903041c00e021641c6801000c4503100c10b103216045650143c81e80c040200041380e91003003c10441d81a10300e410003200482040020840c0c3c16108514001c0e00c0441120760011031f104000c0810400c070102440346c41180c1c1c042e9a03942868584100f1144580b603d8007200c5400c1c890107a011002c24103d04101e2002ca200b6100068060701e896500000d8035001000c0300281480d040c010030104001085143c07140c1d41c100c0d80c42c01481800442035540170059401c1e611002210b00d400300400c010300c850940c00d220104c8001a240ea1805050799441030203014100050b08442112b0840c145550042008880014001814610401000d07001c8540c01d900c20342c0003610b608441c2030565003600c15540d0141030301d0801e603d400985000c1515000082c0b00c1d4038112a5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 28326165 1250 28324915 28324921
    0x1060c03091d04050607210f0902030616090e2401090b030c0408060906090703030c080702100e040b0d0809010e0d06060f031401020c07030f02061207020d030c08090309040203 77
    0x12158803141c000d08040300e8010040140724110900c01001102d00302c40521600340410001345c040d42c40f807010352800e4a001e90000310440c0d503101c054440d59100c00d51460f00c907045c880059409000342d0348110302c0d030071004142c2000035038000c1000610b940b110740c41c03c09000601103444090a201c45000c80300d484804001120030004840c261019403211440c000003209208503000c4400040081354401000c40700d080c0c4501401e075071030300c005540d0504aa4040320701080040e0140c07100d2400e4a00541072282402156000318856000a1035800300090340c00885006920b820f108200d04030209a0f044030038000e0070799540183d0710070f015031541440245241c0801903650080300b101244e0f84030f2406c0c0306003540c8648a511800b00c1d40400c403800038010111002c429414400c5c2c80415109400410843c0c0c5540c45040b04243d0440007a80c100e00c0070042000502070b00c08100e800780b01e080d4010084000350030300080441c3e004021000c1040744030301c113005c0c001e4030000a5a00c010022240180e4940b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 28327415 1250 28326165 28326167
    0x804081b010f0b010f0207050a1502030f160201030c02150a020c0106050301060b0901030b0105030f040213020702100c0b1602150a02090319020a0506160303050703150f0f0801020a0801060c03 84
    0x219464400308080c1d824520b10864020142e000500821400c1c0c0310250b11075001c800c240c0e100d0341d85004040c1c0206005030104041c04100304951030070707621801968603044041108035603907400120b1101105400e03469903811135038148a592058040f81c17002e01100c4205090440000300050310344580680c01003002d0030824003c1d84940e009100041c0204400b036568100329a8541280303c110303001c41c4ca08070b00c1c0c0c290b40d4003910440f44100c44200308501d441e0740795801c0112400415013408800c603800c3c0228801030b1550829204424480d803108071903113802d07103000e8a02d44401018440700c0d0380c801290035001900092005002d2880c01d220031165030300c504101c0024043c140e00300b54144541508040c0c041c00d0740c07011007001802034411960b01a12502817100c103204004d07454a041c0c400c54221000f180c0700341d0029812000c181340102e0106d941c0e40000d40314907500d4100a0010b1114041007100341003148104004124040c000d41c20130b0580d10340a0030075801482250300340140c5101400801d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 28328665 1250 28327415 28327447
    0x50f0402121305190302101404080d0e030412080304060614030c04050c07050a03050309190312092a050306060405060a0608040807050304060f1b080f0c15090303040308070f080408 79
    0x4c000006800940b0401410300a60701c0c00180240b901c81c9140c03046284005105001c00ca118603080100d26192012400001006100c0b10398403800b10700080c80041040d141c0300c400c019445000300a90f5031a03040c1810144100ea03801e5109600300c061110120f1503645020680242070041100c0021b5640da504420303a006100e2000014110b000d451182d03010190407001541c0148040811039250f104200080d003038401c004034025001c101c2e81c0b14000c01041c85900700c001580e124081007428218102d2076451001604030021694841d407080c18041030804001071a030146088500f402103040c41c80224210680364080c1900b01321607034000600380700c900000c81324540d42c01002c881d0b440d030f51088020305000401b40c0c45000a0030b10715a02c1e9040c81c49035210810306400c416014a0308080a00a148907882042441d043c3e0298209540080000724100c600c91014000134550b64605460010007850000749103105112108914055003039110184550003903003d004036589a80c2c901e104810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 28329915 1250 28328665 28328683
    0x9010e04020c1e120f220906052e05031b030a14010b1305120708010e0c180708070518090403090923040809010504080703060501050f0402121305 64
    0x360002070524a0741800007100302440d400c012410820b0a510788240d03458030038112a1524014042c4000030000a14400030f0402e501040240d03c448140c0e40310001407040c803a4850b240c05580c0d210204124108059100c1241c60356031607199019040c0c81c104003824802188460410001000207000000c88281040c10001e07001003c070b860385030201c01c5201812551641705008407142000040c40079070a8140c5156103102ea40e00141d59040500348412103441c078144226030700c903091002401c07410a100e5001c10070b850344050520b00708204140031041d07a6908018050000b02c01c204247c89512561240e0130110a10307210f13a48800d441c0c04041c0300701e881887e942e03100d00544288410142c03c204003500304c5114640901803141060300c40889402e140e941039441c4145040010001001c0200808020005061081c1096100e8107040e10707045a98108540381079a4800501c8a80b40c400341000c000d403001c91341503240c1040d1150b070004104000c0e00070078050000b85094410000c00f407080c0e400f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 28331165 1250 28329915 28329919
    0x90f06030c1421010e0c011103090d030504050406030506100503070b0301120305040e0115080601091406030405120301290301050a060e0f03060c12090106030b0414031606090b06030601051509010e 86
    0xf0501c000741500902d21010303d80c88038460145481d8455000359480c1141c6006400070310f05148844044c01130f0401101001c404000707040202068940c2c4600c10100a5800740d030042c141c52402c115006401c0290b500214800da011020130030a00c050003048130705685401d540803941a8040c5004e43c0c0c58000c641103604007144180011444400b20884c020b1100420b03650000b65840e4a001074a0082c550700481d810340e5070041000c080f0741003000096410902c1081100e4015100c402c00c000590001c1c2c12110306019115030510b600c40c490644542c0e200101d200c05840c43d49003c0003c1c0301c1803510720400302880b540d841c0ea80d9040d0381d80c4130040720182016042d20360074079010442048a5002a0f25203640300d282e0008100d510405110300c0c402c0d65445035400101c1e0701c0c2c944402c22070340305a1000844c00c0c0b200300030102d82c2c2c1040340c000c1c0c501240319800c046890241442c0903910880c00030107881c000da1006004029994404200300700400340006000d540d441001c1c0103c5002400000f001e0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 28332415 1250 28331165 28331209
    0x1020c0307030e100306140609010e100809101b03051e07080a0617060103031107080a0804061706030601180204050303030c040312050307050307050a03090b04030801090f06030c14 79
    0x10715030008143c44261000b10340426410a500d50140c0071200300d8000c011070006103608080e05420424010302100714141051a102804040000c011605015401b00010b0094042c0024000c040141c8644015002801c0c4038070074210301099801603144611004154654000c030f403039246110b61000c5030f11841c42c036448291500c4407002c1c041039400d0341c0c150b910900d4041c1c00a003070600d0000498004202d00d020b4480c0340d00c0c513201140c0c40034000304040720601801a0006490b00304000340d80c2e0f02442115829200e034600701000e00842500711517943e03400e070180100704555402048140c1503c8804008491010420301c3c85002800340342c0149826100000c20b100e101040c3c038000c0c00c02c4034421719404008a0380000102d6031341c001a1582c00c0401c1c000d00208890900410103801d0030703141880d0010390030300140c40d08400450145d90a80109180c40b005100100b01e90003908004481403030144211842c42d0307901c4540c5079040c415003503182c501908554080c0d652000f120b94954071503c900c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 28333665 1250 28332415 28332427
    0x70c0f0506010501090f0b03040f170301170c01030b011e02010608030c0703050f01020906030109020702030c0a06030903080108060c04030305030c090630150f01020109060c030b15040302091801020c03 88
    0x5559501d6081c040c42e070104030f1803072002980500040e00d134400c0d03819110307405080da102d9030f0307900c2c0103100510341c201d46070003007040801080714150010b1360003803030905102100c80f0391030364110b810441d030604414105414401041130726604102c00800d1a00100f500806c01c03d000c00c0104d004094581040445020004102a9846000400f00141da015100b507070011b03c0c1a840b87d0f4201d10409040702e070080c40c1400100840203590740a0600c941c0050241d980c2a2124000910031000e07681021021a54400211080c0f41d881403229000d1b0103000020000380c200816800c1c0103014501c8010f04004000000076400b522401c140e0fa0702800107020346440d286130f84882840c18404607503c40001040740001020101c016004502894100c82038861000d0080d00340b248600c01040418155900d50352400d001401c80e00c2020041c1020f540c0004180d00e1880400040c80c070a00c100d1803031400140820302c0569520141c2d030380c1100d8660a6485015019002907019000d1b0340c0890615020114403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 28334915 1250 28333665 28333673
    0x1090209090114100f0b03040501060306061d100302010509041805010501171606050a030e0102070b0f060a090207020603060909120c03040303030c03020304120e010210050108010e0d1b0209070c0f 86
    0x50b0050703c520105040142d981c0001030100300744144100010703415905402c2090316080c800948e00700c0c1c02000003281440d141c1d101d200c15688070b90701c120f0f110440c80c000811051012410150403114a086115902d480e58000804038092512030758461681e0b03005222550080402d41c49010794891b000f44110760f914001e03d10840802c0176000040d005100c60301d044038440070078401c107803041740d11068109518000201d009000640300c40e1400e42d400c00151000c1103106240b54419019490f41031a6460f00c8414040102d07410b5000144503030040c040c0e000140da41f00f0550b42e000000781c90103842a519a105180f27003640c940c0746100b2a40d0f0008582100752000f200410a403802505d090210040c0084110202d01c02100d000c0c0c010449041190703401e602c54030655400300d40520480340c20b81400f003ca8800c443d000e038480c0c2c0d0140c1d59490321940301c84051042d2090a100c80c2840e00f110760303210f4010500c050001070003c0c816650702001403400d03030084441401058100c140200c2e901d4403450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 28336165 1250 28334915 28334921
    0x209120109080406030506090f040b06060c03180102101509180c080604020f0d0b060d05010b0a0f031401020a140310030b0a0c110705010212030a11160b060d0c060e0102010902090901 80
    0x74800000f0b0400001030700707a0038010050b40c001c0009c641e40248035038464403020031100740500300700c1c3d000008000c0540d42c40360400140c82c164000300000305002200360006403401c5060540000020308091a0904020b0b44500e40021100302c0742001c141117400703090217421041c40220003030500b13660100c042045500002c295100e140f0903241c42000f140001b04003d144408540000c100709210f900103213850038041640e0f8500c600c2180080bc280019000103a0b6402203600300e40000000020b00300144602081d01103040e110315002140790100d039410042006001e40c2c8403804400e00000458894005540084021500300d00d01c00214280515040040c1c00e1965030b00300092070440b80740e101294042104811100705800804c12504154595900364200030810f09905a80380d603141c52500c011001880c103122a20743c1c00e039982c1401c1c5010510090007400c140c4c0250f45602034803002034060038110080d02c0030350504203600265040104d0240003d0311009411031840800c2c019070f800150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 28337415 1250 28336165 28336169
    0x221010906120c140102010f1b140903030901051809100905070905010f0f020703020603130311011e05191b030606030203060a03060c09080102031009051501021002091201090804 78
    0x40050050702d654408151403900d407410080d19240810108022840c1004002c1550b84018000400c5000300041c1600c111900081201c16000000c110310392040d6005100c9200c00019861300f03800c2210601c046071b60303400740400d4039051110004600308049845040203287c4c0300014441d010500c0c000e00000d8800c80d607032250500042c01c00000c9515140140040000e8540c1030b0745030400703e1271140d41121886580c441920039030003485004005078803250015846420b17994802e07000020b05103401010102c6030340d450341069141150410843c441c1da002e4003c1c0c3c06860780d0105040d2125085d04425100c1c410003203c45a01d080d403400e400e40f54407180048100071545080000b107036200b4086e020380c401283c48a40c04005001c0610025603a83d0214403800c0c4d00d40740c01c0841e0341d00d03141c0c070f1400c81e8000c0d5803404600607000d000f0800800d180c010983e024501d00a100042c1d0340b038500107961500c500360640d86050300402c4c1d021198840303a02d2020521103500080c808101d0a081012480e80300e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 28338665 1250 28337415 28337429
    0x70906030c09020c0a020402030c0705060a0e0d0c03020601050915040905010f06051504030f03050c0d02010204030221060708070201020906040b0408010506010c0b07030902131a0a05030d090513022101 88
    0x75800000d804641c42c829a40c200d0400000307016850700603801c2000030360008208191070b02040c844040411030410401d0b03c524201e41c40040c40030583c4510528006144940504000070100da060000c0e5020410504486003600e10541980b02e40c241d901c00c002000300e0640d0014609204039043c4041500705110103011054104031694590003800407280220600300900c0004120800009090400c000301c141c4c040e00c0d0a6090501b4a00d440341440220b2000c82e0050790045000e005620b040801c040703c2d030401c000500220320300400f43e03d85a883c002c025400780200040012900350013074040307600e0404002e020603900ca407101900d50060308540100b036000c0d13180c440021001c2d40203807100c05045410510181040d0b4032041e084014003107a40d170490b005441070030b0300c28480c0300c107001d031400c40b0746a81018000202000f0901c04000c00d50f0740554440e510007001d40300c00300e4100c4000002e98070705880109809040c2c00d02c1002a01c9050000002e00a025540010002a40504a05072980 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 28339915 1250 28338665 28338683
    0x4050d0b071d0d1410050408030108060c04060c020409060608030417071203020c100e0a0e040201111f0b0d08040801060e070f020d031d0d0305060f010207030b06061b07090603 77
    0xa080d00102440c060304001d07410280f2445580c0105002ca143d00986a10403400c4801c44486107101a00341c032400d035404c0394008400301c0140558001444030540c0840c00952780d074145890841d0003001c0e540c034484080d0145070350760b40311030604c02d80350440005020305408980e80c1c0e944d1440d0343c001070b04545112207241d0060003408074462030000c0d9062005a00b6500074052441c10700e0070062030001c1341600009008200400100e1900c035046584010032003000310305602e207014000900141c03c0f0700301002c115048112004684594100c03150259410604009140790070380c0003086d010300810340050034a00c0080740004400105410403c281c0d030588600784095103491005640100c1c50b02c003080d0140e000b52080703110261003a030196500b00c0f54004a01d0750104400350071030510a52464810010380c481702000407604258210380035280003032004013802859511046110180a0800c522841002038149151401d642c150b6003140c541c00183c0d080f007543c0e000500c0013801c2c0c5100407100750403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 28341165 1250 28339915 28339937
    0x3312020c07033c0201030c170718050f09190b0405040803090c220209040902040c0f03060b0408060c1605030406021b27060307080304090b090a0b03070e07030204050d0b07 75
    0x655280c0503c110420b02c41d2420f20040d60300540140583c050a0010840c6a0b150040409026040c8074024038143e1074400b0b80c5c401c01c0c0307a54078101441ea00041e01804140e4680105600c034811003541c812201c0f40c03240f031000e229000740b0018091914200e03502908042c01c0c00144021000254007400c5000210f480c4c0d4134095040c020220701c400c1c804d200c06c910200700401000611340040048040082000400907255800901213640c3c0e903100e40d001803500b803c20008250148546006044500300d0f80f410585000c5400e0303a01e400060010a040f040842c204050890b81d130060b030115640001501e84072503c0300c1c0020f6581c02d400d86800184140c28050040c00c0c280700c1e5802441c142c0c664041c80c012046010400114a005000c01da01449448400680c0b07100600140003c0c002403080807440f401d8079010840e0102c00606688041d610700710507040241d4000407030724111242082c0711100341d91001016402405076034422074100200e4201c1004001d5055407840c8102101d4a0300a4168 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 28342415 1250 28341165 28341233
    0x111206010903050a0b040f080304060f06090b0d030c050a020607080309060c1602091008031803011b0c0b07090e131209030b0105010c0501060306060f3312020c0703 72
    0x1146500c03000d0101d400c2a501200800e0407201c055601500849180401c0642548c410507144d0048506403015036440764440c8644486004440c0100640001880312070b01440004480d2515084001c0a00c01d5840148003003100510600c080c2540041c4525101c040e14200a0440d80c0100d400266900039000010541e000220071785590740c0b548841c0c8444039039240e09004000c4000f400c059804030681c500007070b030900100001d1519100152701c1403601340c207440a05003940e0b01c3c191054841400600381d1340000360b11800e45880c9680001d6440c12a4480102c00d491200080d003080c0c0740d041c0d0320020000d0796000e10140d949980e2160800d942103c0540744120303045071880c0402401d0401d07203001003040d58420031083c1c0d4924001c8000040040d070b6035071080c0c21228550f006171540b20031003604000b01d060b035150082c80c0101850460310194881d00d0125003221002488000748104c0c400a241d5001180c2d05880540f00c41c0d038116600d158072402d11200c1c21804a211108a8000001d41040c0c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 28343665 1250 28342415 28342427
    0x90b130501110d050711030c0d030f090e04020916180806010f09020304020a030602030c0c030c01060303080601050c060115050c0f010f0f06030803010302040b190b0406020d09060e0103150911120601 87
    0x4030040d940c131400c00c185651414680c0300104400e5915100780b1241d0310180d5110001d5045091098681244040144201429a44ca07541c003495400c140d100c00c110150f22125a40b603406042c0c110209214080c4c80c03400d48003a9504c21802120002a50021038015000a40e0354141ca0403401e85001d00c0d99928200b00c245e100459000f034000c40c1006c41080094141d80107180c01907450035603a070901c02803007615440d6422a01c2e2408440c0c0d11703040f0820a058201c000c07180c0205080c1791062400000641441c0e0710181840303401104220340e048600002e106078107032210814520b0170707200180c001d0401d80740a030041c040380050503440c00c2d0414890051900ca03402c101c9034811400c80c1940c0c03a5408000082c18480d500d40d40241030354602c0d1072540009809140540040d4400e152241d040403c0285040120100a414030a000c0c1d0103204464001da0150760701e042c00d01c1e000c02ca19505070340322066014030b03602034400a810010048103d13502c4801404185d194070b1750b004229a80c0a00441d0b034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 28344915 1250 28343665 28343683
    0x90e060a06051207120e0703060b040b0a141f210209010c0b180105040c080c01020a02090105100c06020f0c0f0105010e040305030a0605062109010905100c090b13050111 74
    0x200744100b2286030003d0010142c142c0c0201903080c00062960261000070541c2c5204003006000d400807001401044854481d803841020141c0b420415000c0300c0001c1010f01469000b40307002811001f4100d959907442c88148000c1c54a0350300050512252018003507d040c003030f003c0703850000001c50300c17041c90b2141d0ba2099500c102c1b0165561094929180c0764080d00c0c40c005409403508e512041150107d1010034045c2d03034080c0384100710442c0a10320703008926041500140c0058115081030022202695681e2803031819100200c6414080e503144000a84003818444802489203002103280c1c03840201c0f000c0980503150942054842c50180c0018141c201c030400d0281020b00129500482d010903c0f9178042c6034000565100000c403c8c0d04c9400140d166080300308c00c211807130000c0980b00d4801c0c041d00f10068105100c80000e00240f039042c0d0300c403030711000d04001c071640702a0703507540b1100d126103c1d20a80300140726031603440ba038520501a08203454821405980e0100340340324912680d0150000f05201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 28346165 1250 28344915 28344917
    0x6090603120307110712030906080a110403080f12100810090b07030e070b030903030601030f051512010b040905030c0609030408032b02030f15011d040f140403090e060a06 75
    0x110b95a60980240ca607040d001416002c0da2041d0362010810f0303003081d60320360001da00940350344181510300a801041130b80c1c02000f4412083c100301c03042d00d51401030320507642565440f054040d125004c0303820035000e0380694011403504500d82000e10810802000c500802d86003100291081443d900d903860050720b034004001000e0a0f6058005900b040c07203540400003000901055502e1203a903081c5603e01c0760002c0d00c003c44581c0001041c4429980c041c860300400d510500c1d01800a4500751810300d0303c4040c2043c0c83d5005030004450300c1c101c440c003035000d2800103c00038003c00c0300142500700941d4980018803051028815240841c185d00c50020551b404c0300d03048070045103000202d4007001c2d51600c0d200d41088503026401440420000e050005e10700c40c10218400e002d0515104486900f1020800394180c1809011030441d00c440e44c441d2102844100b054078007007040c05005d50450001e1080032240e08203006002d050004140d07003c0303002c808271485c100c1086000d032038200c2080300038856441420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 28347415 1250 28346165 28346167
    0x30504051c05030d020c0106060c02100c1103010612120207030b1605190509030c15071103070902160b1b030106181707050102150403080402120a060c080609060312 72
    0x1501d040a101d028516445002140d03001059454900c2c2d90807446404462903000f184100b11034100348180c400802c1c0d1032500441d034000f80d40100304000400940f000030040d484600b0400d102c8404180404c01034042e00810000d1360f0f030b260b04800d002d40d02a003205e1910348604881d00440c0f00203140310991380c101e110b1001a489038441103030f030400004000d2080c05414072255440032034210401d009811203407500b6581d10310b40400c00d81400d1803103d0b418864181c690110781d00d1148542614800c9a101c0d400d00841c0b903407240080d150114070380c003503601c0174000141800c08404190080039218414804003a01d41c882990711070391a8000030b60102828024170040029910a0707203050890440c0b07240705170045855072075448211003070b44016081030340122010805540d0404c0b500c44150342c400c151010343e04095500034020300002d00301030302c552180205c940c0500b006000694075254485420000b1800600c80035010130700454443d446070255100081050401089076003000101031465 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 28348665 1250 28347415 28347419
    0x3010e01050904030e031516080106140a0309080f04050108100501050f0904020702030d080711010203010f060e0a0b12040c1205060f10030803040602041a04080307061a090f010303080601020a030504 87
    0x2001c04402d0080c800e6003000b055185038003150714144a1384501008140d40e814084c5451050341c55680c9081d140d0b4010094013000400600c0d9020400007040f807020100e07544e6805e40d0300c00c200c000e00400c0501a100c04000910800369050800041c8120303082070b00c41420700d40c0c0720001c00e1a01c9001c2d2081c035001c034800700503e004031800d900c010225404010001820411103802080c506494070020101040d51041484070594001c1010b0b040d03060f10030001d519660500064683d00505480703a281400350300d00d50907066039250100300014000b600100d13030f10361014076a409500d21040d00c2c141c0308410f5889020564500145a0020040d00640240496103030302d00480840c4d0001001205a07140050001c400078a40348010340c004d81c010f0300b0150b00d9030300b4885041034407401c001480d0324030b10041004204549010083e118126009180010014810360407403180b68207091b04d040d40702c00c0d4101001015400310a100d07050300c3c045d03a01ea80080d95840010390340d458503000c0140c0858818002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 28349915 1250 28348665 28348669
    0x11d04020d0615020a1b080a080d091a070e0406230415030308040203010b0103060f06030f0204050a030302100e03040f050d02030c0409080a02010b030c06070605070c02060c07140603010e0105 84
    0x41c484180d420800155040d5103050019400c0e011644040040c2c020301540014049550315001c8003034103440c48071020f2031034000040d54911150b000100481c9000c5110400c02005500070040036801003a1000d070004450b40200780c040007103c0200100e204200c00a41a0510b80b09800690700c600700c081c241c5206026010b00031040305c4070b45907801500c42c0c035000c0000c40340c00e40340d100a51007502c0b551b00d141007501c10142929440e1b4819810149841c40c1082041d4642128ac012907c6070f00300041c0801200c9900070107031041e500328607000503100070b0010030154001107a001c41e404a001c2044100d030004a0240ca80c4114465101025204101406540b81900c681740689100604403100d444980000c18244c0d0351203032081e1408000420421000c40d02030007540c0c0b070500201e000c1d044030820b4500249480c084e030b000140c241035603440001c10042c0190011491560020101a01d9807a480042e42e82c41e80c403030143c5400d07009901848072003401c1600680c0e061751358103200700301c0301c2e0300f0001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 28351165 1250 28349915 28349917
    0x61707050702191412030a0504050d050a0506010b03040204050a051603020c010212010b13060516152c010e060c040603050c0f04080703060e03070f0611090a15020c011d0402 76
    0x6050303038000e0700d95428904900c8050100f0001304142404503611450810030403082404181948a42c0d0300100007994819a11404480aa840c00c441210f8040120304180f4079000c003020004141d4412540081552003841c2e0140d440f451003190140080e0ba140fa51480695906035030f85220302c07541070b400103403490082d000f0b000700d82405e1000500b0403c4003419209204030a900840e0080030006501d040300d241080c220f4050081420440d10b40040207001c80100c021181d4081c1952051801b048120300540d08280342008242c000c968901c142241655009040121030403450b41c60401a150718aa001c00e060f480780741c01004042c1000c0c0f8100c01940500740090608140e801c0c1007002c20f1081880034040c10103000c01100401000d0305501c1c150048800b0403d140d011944103004c0c0c500018034040401c41d5940c0d00003400310b2105031070540741179a80244030314640d2101304000c2c086044002400381003051419603007200d00c204426001504c04203055a00c050545072100304154047c10650 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 28352415 1250 28351165 28351177
    0x30c0b060d0813030c1703091c05010e0c030d030b0f1201020f0708090a0605121803040b0a020303041e050303041709060a03050402101409090411030a120906170705 72
    0x1078080081c0369a199a4040c15900071400c0307000d046040c05081c000d0002642e049409080000382c250201008020740e0340d034030b01501c400c0c28800ca0f020084840030000158a001217075500030000d00c102d000c02c50000d80c0740c01e1070f80702c114040c0c4035039844042c020b8401d02031405c110308042c220304694034003001400b11400d2512440a1290f400f04080003005c400c1000905002d03009080301d90301c07086200200001d0862640c4900200f007410b00c640e10320b5005503000242c200c0c91060f0b152100311441d1740d44600394004d40d800001d95410104501c01402d030040000d510a9109000c20304010b44400f0504122102055001d400c40e401400060001020305902140340b0301d81502050174107070020001003643d4050b51110340065100c0041c00114141000c010100d01d406080c00f50a102000f202c40b489400340d08202449020034a001c20140040b0620310311100703001130140c522044a50500082900a07400004000780c0c05800000381e540c07050003a100401203e0050007402e890300e102c1191250002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 28353665 1250 28352415 28352419
    0x9021521011503020f090907110d0305010608070c260c190f0210020a21020625050a0302040506040b071e02010203030f0402130509060a060801060b090105160b0702031213030c0b06 79
    0x10014550159181101f00780305004aa82d084801e100d0540c2641c10129110355030380a00d4103100051000c550401200d5034002e68902e0034584490442c100800301c404405d0f42514410f00804d10700001081810040982800b514119921803800120f01d1222562249001c0d04822141047d02e00616149040640480c403920460b628803d0a4032800c0c11644840801d00780c0e80c0c0c515000b910480d0701480391540c001400c007103510030102d0354500021500c43e62100401006000512000441d000e64195000b0b8000030340740907200c5445176803c1c801a03020400c162292800d2056004607061810000200c803907042c0e000d103003507490f0903209451070794004e072080b40d0103248241e400d1030809881c4265072050400d207006108074184040144101c0b005034020343e507030b82d040500a0011408800880316070420a1901540e940e200046a00c040141090002c00b110340c11414010410750002c05804261400200f0b0341c917070303224200b0341c0d000711000900050105800c50407c0020601c40c0e1801c542c00880 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 28354915 1250 28353665 28353667
    0x30203060a090501090c1215060503090f060a0603030809060705040504020306060415030603030e0307081c050c030d0203040b06060c1005070509181005040504080d0f09021521011503020f 82
    0xc0b14038400580b4804d07003042c22142d0744d62204010141d40305000301c881500701801040b1040022420050009070360060740280900007000c46d016a404010f1000d014000300181c506074200302d03038000017600c004d00c010740000c1c0030031011452020010644500440e44d50b00c42c030b8541480c0006220294100030301907a4043c006000000b440c1250380020301d4400d03a00d1f80d000489d01d055103000740c110403490340f900d4002c1e48050307403d10405400040c13005034002a0305000c01c5c1c1042c00d040c2200d29100d406403d4619000c081500540d003000c42c5c003e1809548105084041c42da100002e0140e10f00070007101c106107621140c0000511455680940d410441034501203280228900204240c07070074401842c0e0031103565004101410001120741c0002d40030485090215050a4a600743d65004e401c1d051485181c7c1d031741d001c00514186501c070101042d405030058210074a2071403551240e0300000d00e10b040001c3d4181000748400c0d018908681a214604007103200f10f50f440c403084000350044200f50b112000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 28356165 1250 28354915 28354919
    0x23010c06060306020904050106030204080c130e1c02010b03030708160c241b0201020606010f0210090614090c030706030f060f0801050403020d0503041a090a1403030a0605030c0f01030203060a 84
    0x80c040c001c45000e54022040035988014800a100c02c44105074845020144144824005500c0110b1018400003046807090f080d800e103111100010710202150500d83e2003000307185000c0024081181c014901941c00820581001c00145a100c0c450b82d940142038007400c2100641c1c2c80320340068522107901512480300c441d03407500e8180010741030300c802ea5040c441500c14103102682c2d04c0115294111400c400e07801920425500107540d0b02030241c5a141846251502c01d40200d10812540e501c55400320001e00c0710309618100903000340101c20443c13030701448190009055580024034110a28000340003042c0492030800120020008035111860240c3c844800146020801d04110301402030380000103071605081c13030060b1500d12003040190900c10148204004220380180c8407000d00d0071528140704c10354070340c100d0508101440034010a181f61102c001e08038110000050740c8240500c54040090b85e884404050b83c0703500b0200c825900142e44844e42c400395100703030091608000702422000f0304035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 28357415 1250 28356165 28356173
    0x10020f010606030204051203040f0b0c0a050105040b0a05070c0f08130b0f12011a0703030f020c01020304110307230d110d06020909060405160806010909060605041701050123010c 78
    0x28407180e02c030b040004d8011400703106602d03058074a1501c05401e003006501c1e103490007056203080b4030103100e40c2c0301500340070400c150007403814003100624550000c000c1005161525204001f20300594810143c5440d08001a010754080ca00c004241034001b080c8807028540e03079403a00250303400040d20706903052002500003244c602600203420f00034641d280c490386940005c4007a48800700305074440b041d22103240c40c000011101c400e003100e662642614000c245910b401c0b22110103071140c024074101540c80002080284000c1c0144580c240d88110152f400190b070701d071104d14a41846c800e00e0941241040c510b24114940084002c5501d0310030992107800300e169600081481128040a0701d1290700007518101354600200072944c032a8040301c1c00c10060400c4110116800c00780107250060160b01000300d4a160700840b00c050081103058024459181c444400401039009071080114076130306c8250540c0d40d60018012241a02c106600100c002e083e0750304c0007614000407940060500c0202031861000c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 28358665 1250 28357415 28357421
    0x105121503030d0207050c0105092b0209040501090209010501030209010f03050402030f03210601030c0503010302010c11031207031b110d08040801021602030f07030314070501020910031e1a10020f01 87
    0x50f007800c01030b2148034504001d800c080c51074503541c1c10007030200100c1c1030b80c3d5030b86000250b07c41c000800700140074405036400041a60980400313540582a90104020040c05401c9885158401e541c20131540c3d90b00c40040d0241c0c021160b050f40440c685024208413240729600c007aa0040c001400c88040560800c00c07507045610525405000c0d031903120036607a5000b9611400c640128081c6000c20040c101064010010300047c007009041003400d01d515810301003032041e45000e040d030060644c0e0010070400c01010003580300076012404108051142100000d51001d40c110b960303080b03070140c071041402c001041200034443d402122110000d00c000301381c0d08406d1002e0b217208001000422811155801018a01b040d00e41001c54150301c02202400000c1c0c0c41200303e184805401c01c0c8071f03100d403803c0c50700da406405031000c460380000001052204480d81070b007206814215004800b10b0500c00c545262080e9008002400c0f0303034070b50410b181c6100382007401038a815103c0510648100c044802540c0c0d0079 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 28359915 1250 28358665 28358677
    0x100e1f0302120a02090111150c031807090b0103140105062b09050703152a09030503030c07030305010803120f0c090301050906040605010b13090209010216090515010905010512150303 80
    0x1240d9030216000d802d86d60403071540e41c1c04410003401022820441d03188941301c828010501d040d424070201c0800c454180c1c240c09400d08440c15002e072643c11351521383d000c004200e803030031590009080c420810ba001c0c851545081c103030344c00980036515014004044a00d103c20310700f012207000c0f19490216010002911070440c1c514420005410343c0740c41c5007000d080e03c0c800d0754035a4400c8c5103042910240d5802244114194903403240300854411040c004c150303180d0000d5480a07256000000070024580303011002441070354440c0e1803c000d0b698803640301d56528041c1d80c000030085040f6002003401c1d07201c51514554400030142076a46098454000710f42034030380030340b840e01c0f1350b5100500f40b00800c141c034092a8090520307903024509000078907014024034012482407640075a400a216a0140d100703201c0d8a899049902d0313141d030401c0da14000c820081c030045401e80302035020800042c00a40c4606558130480702c3c140d5581d82010b460102107540b8001c0900340c074602080c11100c0c0c002c507490a10160007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 28361165 1250 28359915 28359931
    0x7080309010507032a080714040314010e0f030a0305130210050702010f050c1504150e06010305101503110406090507020a0b0928050c130b100e1f030212 67
    0x4150602040c05820745e00c0d0801e070703c034160800c0d000d502c820881d000e01d924410107140c9400412611000c10668140d080700301801000040090f02005005510a0001d46284c0081c020032440c040014510b884028a0006401c00c0c1c004204454045100b6007100341c1020035001201c100d802d065000420501c082e15200e4003058010445500303668104005c503001006904103d0b103172400012020740c41d140703225070340d00d030503034036180814140a8190303042c800205035520700f0440c5290450b0171668904091108864070710802905000035900c070f0260001d018104e04d035540140341143d60740c02c84842080344580d000340e52240d00144a40c2140a4035020b860150098096000d05052680d40c0550041c111159580121020284842602c03d500007004036246e1070141d40c1c6040ca061410f0426010b65113a00560041195180000b81d42c48820440803c503480c2d050020480425103503000346906c0300b540181d10213141c0c601714009150307045c80c808252500504c1e01030441001502c0c08000e6803800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 28362415 1250 28361165 28361171
    0xf1d03070f0602150f070c08091002010506100914060c0f0604230102030903120903040807330c0212010b150c07061b0f210809070609080c040e030708030901 69
    0x890f0103101580e131107401034920b0750741407070411038040b09448060718543c2000b900c0703a1940700b440442e5099400d20200200b2902c040c0c2200000240a40b0050f03803180d00c01c4041807191502180242400001c4031103413010082c0b1030b6202030812581e500720300c60004887c041e00310005003414040c003001c0d00ca28030410350302c0d9920555099150070a44200030048540c0e10410501104000000c01c0d18a0200011118405c1d075407440b25480c00e500880c1d209031440d201d00440816210340e0320403003800c03030040031079000200c1a07421520041800545401c0c4045000305a0480c00346c140f080c1c8a030118102480007051403080ca0002c02c2250711484595840e044010450418034070090000e84e00400c5580341c00e65180c2010b640481d0740710f0095600801c112704401000040140e075440c41c0016601414256800e000320b140054160b1000700c8400c032403030145103804120940520341c0039003a51007603001000040e00784c0040c000108452441c00c0708600c818050035001403440c1b80110b00c220740c10700000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 28363665 1250 28362415 28362419
    0xa020609060109020c0a080a0905100e01080c07020108130606080d1206173408010506030106090606050406050c010e0a050a0302010e0a0201080f040309080f07030209010e0105010f1d03070f 83
    0xc14100101038000f0543c4900410110035050700014107a1119500090b500740e030b41550503401e0f0b8008006074051504075815201c0d01440343c4c0c1101210090400a890b5580b4a0713480c0f5034100924404d5607030090205d60244042440c0303001160010b81054800c42c0c0024451307840d070a4151074204a5401d290014004010281c070350710241c02802c000340392940640790310041011885840702895052a500c28040318040116140c60501c4100110320340c070007200d903494407001c80078060300301151814000d40c20300341c0000e81c226480c8100021030f407242e541c4504040c20000304961f60f901c0b09a03c0d0025640320f501c0a26680c00c2445005c90b074601c1000242451a00341c40d0182c2541c115001605064008c0305880300582d0b0400e200c00d600c00045107040c8010760b258601500e481c2c1080d040035405209846051420000025000c001d40c1e0084840c4001030707a0310050004400001d0041900107640501500a00d50042030100c00c0d15401c4502001010140700c082460b2015070341c800c0140da0010341c13007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 28364915 1250 28363665 28363681
    0x9021816140403030e151207080403030b090c09040906230601080109050f040f030c050706200111070807050a14070e1602070605220306020306030c0d0302190311030a0206 75
    0x894010004624112801c01c1c2c95070b100a81200c01c03a60903d4000c03607604202c000d8640c0700c0e06c11542d04000c0c0d1a1096120700b82142d00401c603650072101200424588400c9504e140b41880d80300303209058421600346007483d100140006004001000c4807155258984600f0916042030b00040202d11481c8100007480c06034001030140c241a8000400c4030b2400061148440121b03d850758040d820941c0c04440f0901e070300d0103c600e0115106c01405600070300e1000726200e5842000344031a8200001e08080130303200c40c00704d036080f01c0f1a401091b600c5c1d01304000e403000007060b54014002050080055580d0104140c03a003180f1f000d110320a1410700d0304a48c00c04d00c040b081041c0c8440e005072110070116200e0151a1303000e969110309005160902602207012040c8001e01784180d445d401005044490207a56403601d07401a41098581c54401c0c0145031034800c2d14240304400580d02c0d50140e000f4944812322100c00510301280d0703d8250300704000d040e01c041c82380d0700c10001004c0c051f009600800c8030b4501032034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 28366165 1250 28364915 28364927
    0x6010305070807020c0d03090305160f050303040503030909060a0e13150506060307120b040c020c040605030102161203090218040c0506030601020a031101060306090b01060305060901030c0909021816 87
    0x1140180a040024010031550010310091804010b440407006c011032418241c8030501203034402001482445410f00b0040181c071076030003c95052800c00d420b025250303010103032240220f005064041d80b05005029040c035001d41c2035600b0001c0900107040306a01d03000d00341d92000c003c0b40c1c031052030140446054100402c8000700c2051f015600030400c418103103040010f0701c501c001b8102804108001d1842001401c00d41c0c031601d071540004100704480c4900400194440b20291452407013a4544140020507090600840745080400600c0c0c912081499642e8900d50841d03009072401c05544006010050700c3d1201c3c40081c503401c10780c0350b80752032400703280641d048006034200390f004417000d005100f4a41d80024141c04519410300b8240d00c450b407020000e038010202c903800a4640c43c1441865024400090059410307110b156806000030764070401800780d090001c1c4002040c1d4001e049042042000d60f074820608288000d06480c3e1a0440010044032107405607140c10030586043c044a1072076401c40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 28367415 1250 28366165 28366171
    0x18150f04030c0e150a03060f060504051503070f0602031909031a0604150501020d0e010c1a0403080906041502090103090b010816081c0315030b15011101090f030e0f03030c010506010305 81
    0x144c02080c00d0418004202184d040303200c0100300300e86a1202220080c01030b0001005000060010400c605d0841d504200700c45101c000d01c0c2c0607000f00c3d5000709111a103c11710b01d041c0c0d40e2580003035181911209600f00c0c0c08010040100420036130301c00100003c1e9082d000b044491008603c5c070035071400d0803410003084643e100a07049440196200410459030045244072010b5528140018002142d0f070050f03800c0c00780018020096a0000004c9004c8a502c0c0603c43c020750282e554013502d507440400d21951a0b4003030b100030b44a601510030346d500300246034004003480041894085007681c8150713200e031003850080c0c01070406904603401010305d070443d4560400003000c42e18000c015401d0180c980302d6000e0007260040c404c05455840200c0c000d1045050440155400140740340649403500c0c084807420440c03040325001481441e01c0f214a10414060625103540024540401301c940c1c2d40c00351410040060a146c06c180d4000343d4214aa6080c00600352480d640e500116081c41c200c000101210801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 28368665 1250 28367415 28367431
    0x30c1c060501031d070e1509040b070801051008012601021306020f010b06030105040c020703051b011404180b030708010603150b0604030b0f040206070602030106030e070b18150f04030c0e 82
    0x5004c8001d42004006050b0045880c0001d0111858481551502503001140107064202d200041400700f0840040d003103500c00c100701e9a40c40a16600c0744200702440b00c08005c48400a1202e17001406242c1d00804600c017000c3e0550058456104a100c5031804da800482c0c07034001c140c100b03074010403c0c1c07501170001c1d03000401e186008122800d481d13400940070740010b02605000350380d562000d40b072103802041180080d54024040340d01c00c0203040c080310b18009200785d10600098802d03016130740d207444010568003501c43d50001800c019140c03043c2e490092945c0382000344c2c0f43c8a49000081c0000c000e1046602031030081c5c6920461403200e000c1c20342030761561106140201d03020401040807410103002c443d0461003903114443d4130340b03c500000d8014004d800028144910020000810302c0d0954050744501c2101d400381c0f4031055a802030003080780155440702c0d42ca18040a040c1c441450400300d94011840054090703801c02007481c1c44420b064201d50400c4074016100e6500b4030000c80228042c640c003920b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 28369915 1250 28368665 28368701
    0x20f0105010e0108030d09020307080304120c0e01050d02061e040602010204031103120703110703150605120109080405121006060f120605010203040603090f0b0a061401020f060705030c1c06050103 86
    0xd0003804d45e0b9a803240c0e001034190940d484074450115a000e210f0b00004185950031652a01c3e114002c164015814040031903641c40d00000c00165041c560040721f04981008080034036551090b000d002c19640549c280340b81d00e22092550411105070000608041e1282c1d500060b126810f515000e4240c011254a2034840c0d403110a00511003010a422141ca0681c145402c5004001318802e05240142c0c580008080d0a2040240c0c00110442d500090445400f150400709034102d9920b00750803500002405000d203c2c081100f40700904101c5000b02c503910035001243d00c001d420040b40c0d004c0b0352060b040840000d008484a0803050f83c428000d142c210340d120800c024051070b00001030343c1c0340301d01d100d4101895110161101030104280c01c800d02c031a0016200c04580ca0041410350040109015040e66008900c507003080d1540f000400ca140240390100404c0581c580c40c10a8409400003012803168244c2041035003a08002d4017860b4515040d01c20010920794103000015060710000c01d40c104070404 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 28371165 1250 28369915 28369919
    0x30b06010f090f09110c0109081801030b010e15040503011119050406050d05130203010f20070506010509250e030d051c0c03110705030403021203030106020303010b1810020f0105010e01 81
    0x3c1e000c51032404035489400006062121511105000c5c0a0f88401d1862546000180c4050044002c01080384494244014485c8034400005504171148242524000b8503200b004514605004030050101000103803d5030900f9034910020b400c0d10203030910b4801506004c902d620b000050f82d02d156001c120715083c1070341418101040109240215407110610701e03140c4020a5418080c200101c0307409801500920402480558000240000302c0031079440405014410315154140c3c2d0964546036807001c0940016442c010400511203006040c5510a5402c15900703444503070180395040200515072a0401c1c1490b500c01007505000310b2004400c05d101c400c200d80781d0041100c414441882100440008510714900703c210010302c561100501200c0e4001200400c1c00000805841101c0c8222800c1c14496101841e243d142d0000307100c5c04c0050781c4203000600c580882c1401900031810640600c800188410000030b00c0140c1022444000d03800c03042081001200c20f01442d03000d0701850300b008103654 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 28372415 1250 28371165 28371179
    0x6150905040c0c080a0521040b0405060601021902090a110c070905060f0901030303180b010906080601051801150e060403030f200606010c14100204051305040506010303050904020d06030b06010f09 86
    0x4841c06442d41d003041b000055080c00000945103100210300710101c441d01c40d00d13092801c0301036803400356410742d8244903403070007d1055031000881c500c203603c4000d41c04081c150a036013070006881e0080c0c00b400c06561198009840c0901c42009024905044070081c4101c40c5044a500e04aa0700900020301445802504503161340303c1c004c2036030441c0da00d464006440d00701240003c10701b141040005141c0c1600600010354150b1580041080e02c40f9941a22200c0c1d0b40d0300100158020b4100c05840060810310040000860080c00507107448c1039030600700380c001400000221264015041203011921460b480300d106540599552080207000107281c0c00d00900070303041c81d581c2500503d4541040030003031421040080a0010100e0705659404440c0907032418030410b0041d41160240c0b50044458004202040046008060040c2e4100c1301030310269003151000c0ba038542c41142d090b43c000744c007000400c60a107428440c460041d4050b084409041c201000014407203080b0503902010406000c10902c286 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 28373665 1250 28372415 28372417
    0x608010302060f030a021b06071701030b040b0606040b040b03040b01050609030a020f0102011d010515090408041202010908100f180c0e040302070e07020708070603050c030a0b0406150905040c0c08 86
    0x5012040303d0941c8a54402907084080e1280c02070300ba001503000c0840180d51140000c95500500e03140e00d0300c0440340306150701001510310034031010b461521000049804580c80e0710003036400501c01342031030345080e850361080011a0711a52060203d03100010400c4140502c0c01d01d071f00e024060803108145064410000680d40342c80001010f071080042e000c000c141613000352b00084405821640ca1091442d004100c0c1d4000c082c00c4640703108600007a054032940707290416459116580c8403031998280f90400400100900164100300d0500c071500002040f00f0030100700c10320a0003c844008201e01051051400075101d20341064100c0c802d1010f40140007503186c7c9100c00079a446211800c9680c3d413241000c0b4948205079102c101c100c45041c050020f203a40c0400c140043d91051000c441c1c1e80303030b40e42c64214200c440c2104c1c104040c44080c03000c43c000440e2034014203503010000700082013194403a0521044074014080781404110600d0301000942400c0c0140c420007200c07402c0c0103040000b691507a02903 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 28374915 1250 28373665 28373677
    0x30603020f190504110d0e010b01050414011b05030310050f0d030309060b04050702030c010b0109060c020108040303110a030b010318080f030405190f050c09010807150e06030a02070c060801030206 86
    0x202d4000307090100c1070002c4412441c0000c1c48001c109114050742e02c8010038466200c1c0b14840078850809024640d618414040c4143c8e0b60010380d00c092606207000c1c10f08180c0305420b8141e6040216860030180400c0805040c1c01d84540924080d590724100440381003082c00d42d5601c000d004030400e41d20482c44da51000c1e00d0080090b018100071405541a24040001700402c80b06158401e15050600626941c004041c2503600c00c1c410013041850030b80e0006541c404520300c40d0900042c1501d503008019403148107a0364005102e4200800d911440002c4105150050201c5c840000d07a2103008a51541e494000d03500002c44a0450180d1030340541c41314245441058400030320400000007080c200882000b5165009103694101001c400043ca00310148945044058071248103070489100c480c42d254454074103c2d81c004c0c0090041c50300d4001488201c49104a8aa052060721040f000d0503072038110040d84181441030006a85060501d0709988282403034001c0d030200f02d10304005000507120141101d107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 28376165 1250 28374915 28374919
    0x607090609140f120f1b03060601030b0609040603060c0f0504030503180111010204030302102901030e160e09010e16031709270901020c0a060203090a0b10080607030603020f 76
    0x22101c42d1903010602d800010180181c01803190840510344602c00318080b078991007a6810f40d0b0030705402d02e01c0c0d5181001680d0791030394103421020114000390300a6020a43c007210142600e410b0180b8000003c0840e001039109582c01c5c4d0b250b07200801250362021541490340801e04002d414241180c5070740e950380c062079200703412900f500320040400d030b801b03030803000310041e2090300a40da26900e91400a44031541d50f4165582241001c00044000018010381c0036003036034816403034a03400c11460044000c0e00360000b1000141c0504851a0608103288621002130581c0d480040014205903000701e00f100d0405012000ca80c022002405004140f24a28170403a508100351074108144040e0591103032040e2414141d1000c40030f03400e040d000000e020031102c1c603074400b00c610203650b6850b520741707003070384144154030702141c208010703034000101d15030302843e0850f4401d822074110700d1a03642c88000380f100685040a070038652000401064508000b070580c004100d00d02442031602e150b001c03548181c51081e40c24 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 28377415 1250 28376165 28376189
    0x120207110d0c0503070f05040c050a0e010807031b020f06070f08040b0a060e0a0c1d0d15060905010602030c0c0a060519030b1504050901050409020d02190e0c0c0607090609 75
    0x10b000503034001074081c001c01030a451200d55115110446003c0c58030a0758000c5050140c140d0001c0c1c0600c4c161010070b40180c440030742a0900c80c0046134070000080c0ba01c414541c3c0c990a00f008040407803010f003039000854000b0409500800000362410310010b190b40c042000c00c0170b290300110742c4192303480c0e046a4030035001401c1e07803100e0740500d001e4034980d042a08120448070811a054072143c10904030b25032a074840300c4801100d0003007140c41e00072035070311590030010114031200021580c0d80006803444145400103485506c2d40c40314000d441081c2e102c1d80040e407000c0340d600001c07181800744043d0749204072480d0003903628104015081d400f0b050110382501114441c3c200c0114001e4100d1070345010001e0204413002035064510317035190028052240a01101c0e00041407a08107441014142c9400501060b0204000d6007004421402000d0380c101c54510103500117040c46000c034100c0d008041c64582e00c2d4844102c01d40484c0340c01c600501c1c0e079040002c1c0400802c9202d40140b00a42540e00110440c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 28378665 1250 28377415 28377439
    0xa0f0308031503010c0e011209082b05091f090b0103020907180303020610060305060603010302061b0a060504060f1e02090f03030f0d0e06070212181309020112020711 73
    0x142d40504200100b41e406500301196243d640e80e0180c11001019000d0b02c9160404400007210011110340d04401410300b8810441d035800400795540c0c24450519044c0301c1d004004203040c240e000d42d4010745440c000b603804864599030204080b00300c07864031440c20008000e40d440c6074076090341112040c480607002e6008100440d10b01d51144403214201203094880342d0300310b9982e1600075034680e42190b211200b0080c2c540007203143c5d0701c00c0c0203071805001c00600c070504617400c54003040040ea00500c0d241164030440c8059000b072003030038082e4020300ca025940c0003a851400d4209603068652008035810007510f4541445442d03988140a000c041c0301c141801a1114490b201003014925070a501a034544404075400030303280340ca03030024862080301010521400100c242d02d550340d50300075981c060250f006041c400c5d03c181104400b0b010b8403002d400503100402903100c04140c080313076180d080e030242c1d42d1103a0b0f906083d942c20004c40031000c02c6203002180b808805403103001d0605450b110140c42032840c0f0f521 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 28379915 1250 28378665 28378681
    0xd1106090409060207030c050c01050405030a14150109052202030303040f06020408010204030b0402040f0902011205070512090309011724030307050102030c0a03060f03020112180606060f0306050a0f030803 90
    0xb4124641d02900455880c0080c1c00c01400b2070000d00d10449440c0b145030044542540700b002070705c003181c03400b4000305060035055480060385190b205010841d881414904011001d0041c8181d0003401e440100065a041440391240d5000c0801d1000c0e0303540003501176240050b10004101c07948250070105c103101da10000e1420030b029100720b07070001c0c0c1190300104010003844050304010340264400c840c10056101c880ba010419601803801c041c0c003003400100030029070701e225040030f5407140d00c6140203850254590009080a4001e4403110356640c4042640d00c0d4950700b001122401141000f00e85140340f030071341100c5025136203a031400940c2d40c07201c000c2c03880c140e1010020748003100d034080c0080d51a49440e81004d48c06070040d2060b40001b904041000400c100c0b081503450503290107035142c4030304103201c403e00300240100c00140c140d0783c851403104101007002803281c013003d80742540e41e0a4841e0070400c2d005060310303030035041640b0904480104100d206259507010046a501104c12901c070b40c1c0b4000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 28381165 1250 28379915 28379921
    0xa0806010c080301060e0108060307050306060d06060302041107121e03090606030807031107090509030d020307020f161802030c09010c02010228060c0206040f060b0d0f200d11060904 80
    0x1802009542c01100204419403c17000690101d102a6101c001035078039442019901d00b1144941505908108045903040c20400304020300300d0b00031100490b64039a030342d02150440c0c03152008010404004240c0300c040160382c3d0b071054100811441c14440c1003204080000704c0c000300724058410b140c3e98514034400c0007020703000030008581102d1030325120031540c2405408002ea0300f41e913075030b02d000392100840d04c01642d03c40c1c140251000d90007181005d0440c00c40c0c01c02503002802d8481548282003043c084110104440b901240705800c001801500d051941030b0500c4040801080d0180103208000360300c4108400d84044800900e0104940505800180d04020401184082c0e100c25560014503188900f6a61381c1d000340304500821000700f801104a80b02c00c1c081d100107210001c12003040d030200d002d5030400c0c11a90320007010070b105014280d031140c440f03800304c6004507550f45104401482d145c4006120108201c0e06071407110401030155600e0901a08800e4010b200b0040860074904d0740e140c07a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 28382415 1250 28381165 28381187
    0x90603100e0309150313170c06070e090603120702040203040816110a060c080d0506041b0305040209090a0302060a051009020d0b041d070b03041a010e010e0106080103080a080601 78
    0x100c00c0285152031546103840e5884100803501554200f844908194808002c5a11810361002c040791042c0403640c1d11208280110020344a00c3c806000c02004210f0512080f406000141c071f50b080c1c80401c0d002484035039130000b01034511175040003d446800d111054110342020f6411107005980c0c0d41c4614108205000b000c05502040511124110400250b481c2c02d800a00c000c03604900300d541c0e2000700b210b0104100c100200024010721680241c545550030298012030002c20104003101044550103000111003060030005c1d840b0301c240001e5082c0502420307005603e69001d8001495141c801a56641015003c114038550741d40000700360721030030010000034100f0a030b01550b59070140380c1114064055030101c54419464201540f10101d028904a20f150303031b003d0044c198151a00549464607080200309441074032205113400d1100c65680c1589001c0c01126140316003950411143e0f110800c01600001705201440c2c0061000c212a4400d44105045601e048407055442000403542c0604613 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 28383665 1250 28382415 28382443
    0x60e0307120203120f10030f030e030d09050901092d0603150f0f0e0c04020f04120f120c080d0b01050c0609031b070f030b0c070b010305030301030b061e090603 70
    0x15480602150398040014141c00c1210b5140341d8164071403c2c0b9055070300c10180e44280d4a1b24030030f0300c04c000003040000d048802c0307406030400c03500d0b00700000046030410b010086c15400240391204140064a0803c00090150186d40d00400c40c000b4010446020f054403000609810843c1c4046422030407290b0300701d400079550104802d40101c00da0503444016100340034204001a04011807030040c805640304010001a0140c01407400d000c3c140305003c000c0d0300c240080f20981e00200000b24541411a2480f402c0300d1203510740234503040050800c0000321000688250070050300741d2440011076141405c1d18008015144001111018200161410320650889690b40d015400030882480c0c400b001501d00c0704038150740104505410241c080e100c404500a04500c0301e04a1030a001080369900003507803203c0049950381c40e03c1110f484049007004260b00c00c940d030768070010040c0100400380103c240c0088003900c000c0181200f88501000050712242514000c003a01000107450b56400c00c56001201e9403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 28384915 1250 28383665 28383683
    0x402090d060c02010212240111100501080a0311120d0b0a030f0b01150905010203042603041401090e01080c09092505100f021b060403020405071706120a060e0307 71
    0x2800c4003a010350484200d40741c41b034050100090800040b0161300d0000809003418042483c0030b8001036600c250054280309480c85103c9000d096020307107101d0f403806400848000c2c00300021a241c01042c00d95100b2030b081107170300315464007140f90b40e80606071241c040c40d514011404644507800710307415072400d92019001c00664424441845441880341d4182e80b03041000300d42e400c02c081c41c180e6000c84984107079030050707104020800aa4a08101d55826141d0960100b4680c1c80c00d61398061840c1c00a0b01720070083d000c40b1030000c3c011f68001a44d03900807c103022044241c3c1d03141068030340d11006031406079402009a540001d00c03505091010f1003d0310f14140c0e0a000503005001644044002801294007a4203020a030b2000030340143c0354aa654030355a4000c0482440d0054000328803000040d0007070700000180004030041c1d03114003540c2d01c280c03910754465250302c5440c2d84032851400c014000a0007405110340108041501064a10340c140d08800003203101103c03814940c1c9144101c50010b0041c00d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 28386165 1250 28384915 28384931
    0xd0e031c0e0109080d090605060406060f081f0803030f010e1302010c050a0c080102070303050a0902060a180312030509010b01090b0a0f050708121608010503070510210f1802030604020402090d06 85
    0x40175078008200e29006103410031a550340c000c14481143d01d20300400700801d1100c06004011032243e44081c2d03022545000304600b212208040c0b03213010000b5004142c8641012041082400b040802ca0303004040b911003132801800e0161032a85141b64030000239041001c90195007080c010200034443c6150b610020103030019503900b07000c6000b5000a181100040e04110102d05040d0715030207401e43d025001070100b0302d0003030740301c1e02544c80407840c1500000902c004030002011500d00e208030221000305460200301e41c54280ba4007403c50300c000010070b051200c0000b0501951260b4000d4030a00038003820045840d8402c824183c4860182d580c0040c5a03540006901607903050409115001e01c101c01f00d8903da80c1410130302650a05401d0280035090f0b40b080e01e041186180418680d181c2d03c03442d09000840016000310060413400203c50b20200f55242d0103e8900d00d9410304c18200382e01800a5002007010144d80000c2d01c0390b40c09400a881103070003144582c6207648910003880140c0c0e1105040005030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 28387415 1250 28386165 28386187
    0x20a1709070801060b0909060d020d050f07031a040b0703020307020109021c0506060105040b0a050901030e1005060f0613090b010207050d0c05010801050a030809090406020c01110d0e031c0e010908 86
    0x150310760081103429401c1c207030002920401d10b070a0302d0181200400d4000a550340105003c071808180c0004d0380e1204142c607064011590034054418851b20b6000a080203604508040c0c46d04168036035a000a0b00e080d2081002056204001c1e5422400e60715015990f0380303440104902520900305d001e58000300e0401178290000702c0204541110f8460340aa03585559000015981130045102d00c1c1c060718410000c1b000150300c0f420007891071550504000800c640701c032a8081c602646c400c40f141307a141e5600180901e40c905160403003500700c0304941051030408020000096180f461050100d4651030300c0010b081c681c024000000605400740a00440ca140d60801201149952007402c5c007040000c000480e2504145601d04140da8020030180e00c4d010301301e4180041880020015a0b029070700380480c003160f4400380640c103280b42ca040b00c3d2a480b4220a800081105da0315005d01000d50320810520410b0494001c145c0c4410500400000d82d01c0c000911183c003425444d0301c010300714640018003452034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 28388665 1250 28387415 28387423
    0x3190e10060f0501030b100e030a140c01080a051e04051c08150102010b15030a060801021305030c06030f07080901060e250806090a0e0304080a081b01050f040303020a1709 75
    0x9501e21412280b1043d0740303400541c2214104600990425040400040342c540500d40f820070101026048800c00c0105480b40d24440d20903941035101071f0000b50b0f9000f402d6074041c40958100d54051410801400d00c0228400e45074030056808a2121141f000501400014002c10180c2c1000d8a031075010f07501d00c42001060304500316072400c105401c06170b05000952051240d0b41c1c2c03c2c00060304460720742d07150a0801d41c03907410040030241240d89814010038464001e0000c2d01c95014112070f03521040342020304060a1100c5594a540141e0050080100203a00d50007182d0300310341c0c141007680b01178503080200c2d805400260404840c0009860901580b948165040c40458030f001e07601c8248c03a9040041111401c805607034165120790703200e0118003480f0391a4813198500e100101100c1c41c00d41d850341c0031403d05c0414a02600c0d183c0c004180640003c0149017180c00c4140e224000700242e1a00c0d41070400c1c405c40c09480034040550100e0341011880c040c02603c3d190320310125056031289058660a0707a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 28389915 1250 28388665 28388669
    0xb03030a0801031202030c1e011506030204092304030822030815011d010806030a02040e0714030303040302071802091c1203020f09100302130e040c0f0501020303190e1006 75
    0x4c0071103807200121441d10101c240c4415110f15000781c0281da50480812104400c5c400c5030005555039036100c82460681080c01c40300420303c50b00d001d601c1c1da10b0100c03507000b2208008001f445c1d00108546454402030b5200384503a219a15007030105040c0c9604108a0034005102414002500020f42c00e20515810480d514410981c0000c4c120300d803a040401100e0300408000d040e9070f0f00184c1e112a4040b50701400d00c8551060001e811248610595000101903d000c44c45140c0d00d0740110f242884a42d0740b05001115000c0c0980085103182071903540250394035076610a4261982c08885580f00c100043d40441e07004040060070000c10304490310750102101c0c0701303950490300b03040707101c00c080d210500078000d5400b0f60000e03442a5081004040500550342658145102055420080004998020b45680c0302070625036641c1d8032203103410702c0c180c26103001d960000803140075075000410640c3e074000300f200d501030514481da1b2444a04400351002600001d02c41200c0d03805064640c0c00050110350240d42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 28391165 1250 28389915 28389923
    0x100b0f040513090206030a0c1412011403010204050915130c050910031808030907030501020301170c010e0603040809040915090201080a09080403030c05030f030c070201030c032c010b03030a080103 86
    0x100300c005160700c02e400c496112070003d4000034144001104003d090703019007140c80752030611400e00c40d0048818003ea40c0400380c8140f982c10418018482c0c094104004426010242d00842c03410303090500041007040e0040000100001e0a0006d0003d0346440220358010842001d042c0003150700c1d004040c00e90f400024859004103000c0b056088814072074002d400309161002c1c040300e04105a0307140c0485580c80200403a8003403180550000028009200450081c91200c2e0012415a01c0c020b4440c01c103095440550304000c480282c04842d507451a0840e50029484040386d43d940140703d01042c00703010115000780401e01140404428100580c101c0d0380114801d0344ca03c4210307a14a030b500720031a201c5404c0904958003d0205100103801003032032482050091040301c1c2051115441550a0343c03045072909858500440e40300215600340c0905e0b40c005e40141018400318000c2042041c4030400218401d8640f2200c0d810100d989100390702a484041016060380d0b950004588064805d02d0284401c40d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 28392415 1250 28391165 28391179
    0x406020c010c0b0105060a05070b01030c051801060206060607050c04141905090c0d030c06060308090907020d12020a050708071407080d080c07031b030801060206070c0201020a0803100b0f0405 84
    0xd40c5612a8809400c01c42c2d014500d103080d40d084c501804416000416480248a0204100b801250440c02058001c1d07219140e0307c0d0006082005018111513060080d003603a100040041c032803682c000c1642076021100340c0c1c070140c40752414100329240050860001da003041c5824250505c030011041e003188910b80815403403001481080c40c40d811208100e46440300d54004070048265840c01e020304410140c044d00d09000c00c0281612003000700d990396442100c1c00c81000030304096904044114940c8041e031400030b0005021a0b42c0080c0680d00b61040e000140c503800500084c0c054000c90135910f2054020b941c071034031004280380100710700c07603028844006c500ca14000051180c00000380a0441001540c440e510b584a00282c04200d0308881011000c1c020348800e11a03c1c0308011204103001400b07079a801c01503526140020b810440007501c500108800540d032600942d070001010805994403001042da242e13030701c1300440281d018507040341d144900300103580d2420054000141c81980d004888071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 28393665 1250 28392415 28392433
    0x180506030d02070810020304020103020f0c060f0c030f060906030319050d0605090103080a0302131805070807030e030a1d0901030f05010e06070801090509010f0e0304090b031501031b0306020a05040602 88
    0x20399444421380f1070780d6a140e00550f40007003041e5080d00503540262041c1409424691440803058443e0046440e449096010b1000c1007a00d8004119440d041102004a5855810404c1d00040c0c0440b000307040d036000c0c0c21103401081454601300103d0f200c0b01500040401d80c1c03091444020075991040c4c0c1c400184070700340382020549242040d01c03d41200d0f0702000c0c07203140046241082e03003e9008040180d222014aa90008006e00f180000c242c240a101ca00015580f50101014009203406402e0408152074041c1c00c0040110000c1200d46001e1241814800d421300f05031025041500043d4443e04040a00000030401000321500c2903071500c240000e0100b000ca40810f075941d280229091400144c103100108010b5100340c3c00107400010010020800402a0180340142c9041240503c0ca44d44002020804260288950081e02c80200c0150940140041aa0034270040c180805013103030300802e0790521500f412200355030066500c075105640710047c80f50082c1454005101d41d801500a030424 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 28394915 1250 28393665 28393667
    0xb06060a02030909100f0b031e010302010807050f07020a08030a0807030b010801030201030e010209090411040606050f1b0a0c0801061401050c0a03110a0b011202030d1106010e060a180506030d 84
    0x503105640c00ca9802141007000010811a943c04040c10720440c0c0403c00e000460b91825080d0003102805124280d55038905000d50161610b9441d180d80b0041b110701440180300503039000d0705094001070180f41c025290317850401c25000710310aa060007580f00503d480c0000d074030580800980916002520360080c2951400c6098083c1c1c0d07111801d150005440d8030041c40198045d500c0703220845405d800050618581d9004a103074040160303416500065007605001c490300c2e15004450142c984d0740342c803a0401c200c030306404909000d64611010000345e045002c407107181082005260554000969000036503846649a00a0000303014054031004040c1030118154080ca0485201d41c0e010401000c4c81d200d2510111692903403040055968080c0c0b04010011076a924001800382440140800c4522110701c101031070095214095000e0054800a00285000c003080c42d0341119010102c2a0460346d03a4000140340070ba0540000354070540030324a01d8020421548044e20415054049810305240c1e260 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 28396165 1250 28394915 28394917
    0x170606060703090513020417070f06030b0108010306231503010b090103050a120e0a031104050f06150903120304140d180306020d0b03030a0c060609020403120302070f0c0807030b0606 80
    0x207002e8003145046a04000a007031185950b103072440c081800506140d1504690304039444824011001e59000d100240700d0140c0c07128050740244213509040210403040340021342945014400604999912000b0001021284607038081d568405c030b4219245140c0075200c1c04002620b40340341030007517180802006840c18400c40c0c15041e00d400a00526001c0c1031980c3d80850088000f0100b010024492480d00940d02e80403892000795110b407142041108040d03080c07104444d8020000e001c490264000e2041c00d840c0c1c1c103030f003c0201c0c0c61005a16540d40b442008a40781070301d00b281d02c28914000004100c00d01c82004004e43c0c0c82c01910040d101480c5e900e0340100c600000e0903d0015007030801110070030010380e00d03900800e140d0710842401b1804510780d0001a0464200d10840408924004101d204201c0e60b0b1107990050b0100c84001c605090940d02d5000c0030188000101d0149a40020703043c050210000580100f2507000540804d2907496010803034413001c035132008852414000300400e00d41d20f40300c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 28397415 1250 28396165 28396177
    0xa1d0d0305030103080703090806011d0c0a050714070b0a0309050d090806070507020315010e010305060c03010b0a0c02041503060c02070812180d0f06061404020903060106050904060b0417060606 85
    0xd901e4504590950300c565540e0383c04400210140200c2d403d00003011f40092000034000c104000b903003110221608011382c0a148004e00700c5250764030070080c551403039030400e041d9000c043e0009000000400e40080c41807030107440da0410305c0307175002c0030444010480d4981c010390701440c400d07001d40b1f03004424500c0c265281001c81c0582d0312250880f10006203c0740c8900007030540180014102c59268503401c6070780c031005200382c021150b010102d400600501c0b104000154109040c0031a607841c540c50054040154003031042e0701400c202e554550170f420356a4036048107050b07140c94210410402e43d64586040109a0450510054001c110000070281c2001c1040c00d107000071040740528100320b4400c00a29011409815903001d02a005102d01183e080011020380611940d0005003050400c00030700d051249554070103200d580100181c07003c586000c40c200c0c1c11a541d03030416648514110b0001806042e07a034110b4801501c02290020304250365407241030104040405403a1103445e000c0c180f104c68840d41d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 28398665 1250 28397415 28397417
    0xe01091b0f0806040e12030c03090f0d0c0807080408010f0603110a05060405120a080d09030e06070819090b07050705090a20091f030c02060108010c0f0c08040b0a1d0d03 74
    0x2d8001001c900700303500b004910310440005e4484001706201640c603140c00a94032905005004010010008400c102c4502842d06450042003c0004c1144c010305803802844002c0c045070003c5008000c00607500140c4002c0c01e04040240401d40c22801c0c104000c0200c1c2c40181ca8511102140c00c1d00c0382004e80d41c0800b0340340042c0c00c0c07500c1c050a20302849001c0e4072001d12004a480b803c0f010401090100300542503e070903908000c148200700f81001080580300486c0c09109080421403140003810880441b10019502d0140c402200240750b010742e0964443c1c2c3c00f051003a0ba00161004c20007030081450b00545100702c6d00e0404c03070385030002418200c0740003c841d42d194554800802100e0105403015029940c8020a00706d034100d211b80d080420407074607c1103140429122012010b41c243c040c031a56001d841e8010080061840458005103c812445402000d10030704019040501641c9011240a0104209219030b503094041e001010b42e01700401c07142c0c184a440704410210b103000ca8184005a0705 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 28399915 1250 28398665 28398677
    0x308030a15080d030e07050a060503010806010b0406120c0c1502040f09050403020d05070503160609150506030c0d0212061503100603050a120c020a0806070e0301060515070206040e01091b0f 83
    0x70f500e5069005100720107200f07032940311321140000d06907118030b0000064004c0380d4030b603500c1c0e52400711490b140c14810303001050306000900c810700c0307010360150b5542d0310b0180d0603c0100d1a01641e45003a41c00003074010010f842c12981440000d01c14006030008c004490b40b0f01ca0403d00e440daa080c262040301c0050b500203005802805010720101d10400c0038015541c0134000ba00c0c501850304807081a84001050112140307519106603c00340042c0400d08a04040b03142c500744407500c3d24070002501c0d02e01590207a4401c95400c0e44500039515800186803035101e51900b120341c00d04209803813081e4010002d610a21034816003610000401c51070140204495000008100b01d03d03081d5a4178034102c00c0d0320200400c224241440b0300140e5914221800140300140180101c0e0a100200030b0140400200e50740c02031307060110411498507156114040000c40011494503041c41d03100264480c46079034041041a0940350012070700142da544541890715502c0c4140710f018551490907503074580e0040440d000700f60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 28401165 1250 28399915 28399933
    0xf0102011b110708030711040c0215040210050c060a090c0f06050403030f1b140111090d02040903020f0604030e1f0e0108100b070b011e030c0b070c09060308030a1508 73
    0xb009400d0b28401d00d140c9400c2c0c0342415254110380e80f45030800c010613601d4039503002c540c0d144c3e42403501c0755001c0c40f9180d1026180b00400080100c801c03210103031000340551010454140b80c14032410550b8006880d881c107075181400c25480c0d02029081040047c0c1c1c030490003600000c0c1c034000c0300d084203089504030340701c5c142054070f10344050300c0b142e100100c1e031000d020000243e4000c1d20001d001402101d849501c0f140602460f0041e03460851b16030040b03030714802800b084404804c0d514001c4404403183e0448010425408502c1c00300c1c00d00050800402a6218030418001016088002c40b00c3e62078055880380c4060004142144c0c0b80300c1e2204104010131416200c00e08913500c03408070194410849118441d01c10b94485c4500c507076510904c015212244c12400512407240341c3d820302500c0820003003e002801381140c80382d411494540c880e203100c0c90340000d42c0404008480940c40c0c01406500000c000080c4d0741d04281e03003207600441e03140c05001e181518640d02450610001010380d20014001d2076880 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 28402415 1250 28401165 28401167
    0x6090a0b0a0603080a0309030906140405150d050103050a030f02010b1023030a1e0204081c0c020303030106090311010807080610050f03070f020f0102030114130e070605090f0102011b 80
    0x1800a0000100c082d126000070001c2400b62009048030b00043c1d03400500f9812071f04004001040d980c1000e410002c0d031420700603429052400795015100111001030001200c025070100d03a12507801080c4500e4141400082400300100e140c00e0018000d4079940701200429202300d080300c13401c0b6a0036510001d42c0000e8001d5503c1983c102c07110040000080c03011000d40e029000544d0412600342811545841c00c41c00d060180c4100030003201020300040d0300301410062000d403501030701a42c042110904600790962035101d280a0714040340c002c3c0a40780c0d00e51f12844000d0025419000940e545100010790031855449034440601c00c4850355640070254503a01c0412041d002c440741c0c09001c00405010492180c00210b004501654071515000c203601020300c0080e00741445d205884109910500c010000340d40350105060700000d08441c80006540640300290003403580c2046072111b0311481001041441d0007400406008808807080f125229a8000480c00e0313803003882c000d00d14070042c521441c6a031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 28403665 1250 28402415 28402433
    0x6080109050c0702031f15080703110a12030309020a060e030a02040c0c0803090106030c06020f03040b070204110304050604201e030102070b2805010509130201030605060a05030609070206090a 84
    0xb615400998600f41c200d0b0000303441c040091000320784a1401c0d4a0304001c0c03110a100d00884580d00d03035102d12003a85072043c49030300c85006120142c101b000c1000c0300015a40c4401095000e090f614042120201880c240100140010f400072402010a808040740c2d950050a84404241c070040003405044140e900b070002911188503083c2c20300222440c00000654038201440c0310f0700c0c3c800000284940b642c104a01c20168991013a419074111050001c1201804000c8074265000203036030713941e0341c0410301c08500288003103030301e0b140c001c071010051004200000c19814022030060390049520a803000840700303850303032000d9440e9004462400e191403030b10160311903d0800c01d00800060501c00c0c00e880c5c040900070100c0d0708010400b1a40034600100f03a5540341c0b4040f0844001d0208603e41c10307d80464014500580030a45520003082d607481168400d80100010b0b1a010b8003140e21035008000140c043e400c281e032254411400344000410722480002c20794440d08104000300000d11064551030382d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 28404915 1250 28403665 28403671
    0x15071202030123130e160b090306010306050402010207030221011a010906030b0406050603160f08040c05060702040609020412060b0d0c0513020c0109030e0f0f2107080d0c1401060608010905 83
    0x5425403500a458a2143c07060045c04410304028160743c2a200b10420220311541d0000b40c1d00200074042105d40d45c0f000610107040d250301c403030009000d40311400140d03e00308190703000030340c80038100e2812820440410701e141c81185500f0000d00c0103864100071029080002d69041b0b0000d2055407040010300e11907000340c40d0a40d03015000140d401d8448001c901a41c0c0220f40344160318a200c0d10000040b5880800e0100485d058944080241000da070740c3d205090441c46030b00d200300004143c46c3c080d913840e640f01e01d0051002820456840ea5100407610144007004010340d125490141121410300746004911000c0d94030202c4030480a08101c02c00c01084916840070001650078000302031510401d108850380305009440d0603040d00400c3c03041110f40600e0042c1c0d82d006408034105940c0a803110100343c00607590305481015070103c501c044e549040300c280e01c000804c1c82103c500c101e10030707002010721b041d00b8010080a400149401042400e03217005104035000503802c0001001543d85943c8110b030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 28406165 1250 28404915 28404919
    0x9091505030d200703030201020a09140603240d050c0a0e010e01091503050d0903110409030804060203060d0605040c06030e07150f110d080108070501020d170601030b0315071202030123 81
    0x2580f4092030050790b2500056801c2107000d0b0b0350008110312860703003180402c1c00801500716801c10a9580001289684c00040c1c02001c5030410b54000300e4500d440380312101f010302400b412031016190941806903aa01191800c1409060700b480702044008800040505984101901000b143d1038141c50704024000c0e00d540010405402c3c5001c00018403d0009100c0072140f42d03607108401d4207500301a4201c140000003184500c0c034080125000a401c0014154026044040181c40b541c0d441c0200e20b01d1602060020105440c00080008114100210b401600d10581e0100905400030302410f40e540d0710382c0208005180003e620320021482084246290b030a540fa14405480803801c02900d403a2895000030040f8a1810041c4400382080011310002e28091000303020810700d10f607019011420040c0410030b96034440c40028030f0340e4026000501c00b41c8002c4d084443c41c03042c07107072100d6010070142c2d2507d0020301e2201001030004241c0c0252416602c003c80c4081c500408003012881d41060201c43d99 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 28407415 1250 28406165 28406207
    0xf0501050f0d23070b0d060518061005090307080106150e010207030b0402042901021614010305090102070b010b0703091a0306090703060b031003051908030f0405070b0a09091505030d 80
    0x414090f005200d5500140841d000c11612405604880c3c000c0d40c209400881c000c0940354105140d40b00408d044e076400901c151240c202250600804070341e544600840660944114040024078040560249040302e80d000c000304d04584810304111905210301201741d006a10420041c404644480100b603005403008000050702c401d04070384544a019030784c0c007645841c105503460110558042c00180fa4014500b00a003c1d00e604200d1850041c1d26200402810150b580000408801095040750031a0b50403c20354079840d070f501d45e60004150300c0741504800050320980300040d150005600d000d115142c41e01c41e0750850340d81000b48400c200005120070100350322a04009541e480e8000110302801c1810300c01e024160542c1002d44c908201880500c485110503001c5c0000300d110362054a42007c0c0b41d840d4070049460340d05080b45040006d4100750302030080012140d101a400c40000c0c0212882102d0a0081614018036a004103a6910500c0d0b05500002c803100451791042c0c44600301244d07800304035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 28408665 1250 28407415 28407473
    0x2413090b0f0610031b050c010e0307060b01090f0807090209030a0b04030207060314090a060e030c010c030b0901090209010e010e010926150106020a030302030403050904020c010f0501050f0d 83
    0x21038030400d01611409464249503040c08018282a2007482c00c0c60030504043c0441d0350403a420f01c14000c1c1d0010080d00700000480d2180c1104001e4218001d910394902c11030743c032601c007030400c0002400d04030707141c6001c41d020f690000303000c218071824034084a80e200c000e00456841c1c101110041d5211044d06545801440b000d04000b03184064054000c40c001e90051140606094014080342d0001c0c10115000c0030b000d0400c0808a80003840b4504903910003070100307920701c2c00c841302465402045840d00195003030005007581d555155120305c03000721f011100310445036641e80c9841e00302d2145103c0030b8001141c800d0300b641554010064030248003818504200309075501c4611404600c00d54041c43c030111a071580300d0303e040078200140c011900d03a019415141d0b524241c400b95640704801b1008091540100c0000d0034980504180c6000030009002035540315000318540340207000308000341c01000d141400100e038a080c40c801c0d0086052025040d0228902181c650f0301500c806070303011489056803580c00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 28409915 1250 28408665 28408673
    0x40b030405060702010e07030c03080706060e01060e0a0e0408091e060d02090a0603140f0417030c07050105070207060c0b1003022d0d02010507060c0c0203030a17241309 74
    0x11881907001d000903100303604004000a003903581c0c510f04001640c1c0300700801e1010801c402210801c0700c3d8002c0003d0341d184568500b00c001351107258026600812030800000d9002d800441c3c0424252003101d1b8599400e880e85600f01e4142c7c800d135000340410303c0c140810790160610529412a400103c030800c0040b0120b07400085c0d0b554032a00180b002d086e00032034a5410390500065010140185007014040c0300140c140d69078441500030680388843c80c107500810140b20017024040d8400c01c58600710740d078914180b40c2c943c526611500f000c03240b41d8600701c00900380354404a805000c0d50583d5894091000d8940c441c1d845200c005000706040a400030310010043c2c0d250011140032118880c040100c1d00c5590300c0502c0e4031140c11000b1030040343d03024202001170781c3c8034040701c8101760b02845c00200800d040070126046408018001d4251000040301719000360025940604c8410001d0082c000b56036101c6803861449500303070000c0d6055400e40c0d41910314541b414040b410032800c00c01c0069112801c1c1c036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 28411165 1250 28409915 28409917
    0x3061905070c02040f0b130212130c1a0c0f1501091a04090f1a0c03040201030e0c10030e100207110f0310020f040302090106110a0212030d020c03220807030215040b 72
    0x8441412641c0c0c42d4041b440340c0c100168086250603c5600071400d02895000e040d00440006121500343c03031050074000c01b0000191a944050007104005403401c204805440c0700c607620205004941d0f110701030540b0851800083d041e000c40c420103640c2c46e016441c003c60040a098a9089035a49688100c1c900b04035441d144a034031740c3c59014420360380d00f41030181081000303280c00c50a0303074003506440300402a1900c10442140c0e000307a07080c03030700041520720021040d0400072000d5541303a01c058906405008a941074011a03041c41049045e102510303000c1d07210b6400c074410030000900c00c00f01d007510907001e13141c032404400c00220003074281c51061140155100c100d9000c01c2210708540b0707010409000b58100060749602601d000d0520f0003850004007119541c4201d480c1c802449400c2d0314a03012600f060070f00070b81320421050401991a005129041c1c1d4680e002143c44170002d503401c0d070710003041003280b041325400c9408210103085050b0940c1c0078005c4001d042d4210452500c000c200c0042c4e20142c101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 28412415 1250 28411165 28411181
    0x30509040e030f0a090e070219020406210c08070302090c030a0b030f01020d0b060301061709030f0d0501081b090106080702160306020904060b041503020c0c181503061905070c0204 79
    0x2030743c050f41e0b801003500003411040f51074021440e580710308020010b445070002920014040c0030183e0b420000c40900c001406444244c110903900c0e082d80040400442940030305100d81881a01d00040140d1220002c907501c5000d40f101941c400d1014010400e443c1000c00103507040080110040703505190540031070f14110442c164800355a5001804094400032440f0b600d00010f401c941042c07640d450a03000510480f90070700c00040483d03400b0003280380c0d4641007089407007201c62f0486250b161003403030b07500030010b1101b44a50422402100503d0048960841e8100030120b00140b00407100d03400e18204030f402c1c003001000c500c11740c405c03480c503070168503001406039008512411016135100c1488041c04280e440f10b42c808010b4130001d2100307010f41140c082c140422000c8501d401616541202c03486450082210300440c0c01c1101180b0701c00c1540101201c1d540b103078280c8242e20b40d05a2a0702c0c01e1580e41c5074221514002e00041c10350b68204510315400c01e036044452440c00e4500c4001c1500000c003210344107 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 28413665 1250 28412415 28412437
    0x6011d060d02130e07020f0106090501060c03030e0705040f060503010e0a2102010b0a030b0405010c0201052401050904090b011a03041a0712110408070b04050303031605040f09060302010e060a020a030509040e03 92
    0x5074011f842c00d003d0045401614900b8001e001d80e5152010150180d141c80c84014140f507192541840316000c201710b0348008007801401401401028003c41004104d14080d26000e94201010000c2c031105c00241d421000741c0c09190200c24002003030b144031050303180c9081c08046540314810002c095603500d4074600550f002c0c42e960226400e00c1d20303050342180e43c000403403070540e4100001c01080341c42c02845042140c01c11072030718040c80341810040341c261040904a941c424900004031051004003180d490680340360700007a1300c0114071102c0751012404100c800500920764240721030351402c502000349800c8000c50170040b104103220500f11050f00d07034800b0b05800a400219040103500020402c0c04010808422400e207004d0800011036141d20000b0020f444140e01c0d8480108842e20803003c0310010440c1e03000750581251507071a58409440b6603c82640041d403519220000b6161031421682100126001054140c0c40c40d0750544054104481e003541c03040d40c0d60b41010094000f400100312492407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 28414915 1250 28413665 28413673
    0x4090e030d05160818061b0c060c07020f0d0809060d020408010e010902011b0302100506030a02030a08090f060903030706110d060806061906020d080a060f0e06011d060d02130e0702 79
    0x610f00c018007001006021461016100000b001d00307540106880da088040316010a00c0144040744a80046c840d81010882c540b0516041102c42410b4a000e4558030f48210b41d44810714414104000e1910340702e6001070f20f807000401038400075240c040d0003030410100c0b42e4000341c140780d40ea08003c4d084a00002c250b1007941d4403a03141c90b00715a4840c040d2004081d00301000070000c090381d24000d40c2c500c9115034003604280c0d6180130900c0c80e03030308010400031150b000b03085418442c441d01c4c1c501e95503041081c06a00a6030102504443d1b071030041c0560b40c540038060011030030610245c03105000b501c0396512044804000300040010480c007030043c8406002c88030003c01d020f040080078880e06210742040c90360710064840050014503804602d0241071a41850a800a6103e80e580c00006044550050b5029941c01030001100903500310388601c54103003602c0380d00748100c00340da10f00a02031429035001c0d44a00200240445148954050015030615113644088039031240c40f904000c020903196840981c1c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 28416165 1250 28414915 28414951
    0x11070f02090601020624030703050d02030a031a100c0323070215030412142703011505060316030e070906030b0903130303050a03090b070f1704020604090e030d05 71
    0x400284503600b19000784002d1001e0300d03020b082841c4500110607050284a001410307450580c3c1c0c02c10041e8003440e0007500303642075181c0400019690758005503040f0b0110341480c2182170354490324850f000b00e401c0060244000395015200407149003600c040d040307061002444002c110b82d151541c02814401c842d202c2c16541d20f0950042000b0000800ca0401000c0f408208000001e000080524503010044c1007420030507840e14103800c91402000d1a8070790000c16201c0400f2340100c2c600c01c00400c00020360003000f80c01c00042002000382500e028103a0428400c00c08a1141c1d5a08080103c0031041840d000405d26480c40b2100d0401015520004926443d20001d105011103602207982009500d802145000c6104075440501c0c1100e00c00941886008201218441d00a410128209038000480c580502d800711014010500c0c402001001900b84210318010051003500140115001817445003428075288000c00904401002c0c000b8030300017440980c81c584101d02030306004d1015203609185120b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 28417271 1106 28416165 28416169
    0x9123b0a0306020a030203060f0d1709010302090d0606061418010c060b13090c0b04060e06030a1b022b05090d111503090111040b0a030207030311070f02 67
    0x10f000003100468076078968021031203a2000c4a00f43c041c110301074140484410400001406480591082c0b0080b49094028105048051401500d0b1102c81c40114941d003046d00009c030f40007034684805100298010074294060fa410311005400c10140080090004e800d914060341840304990008041c4003041d005402c41c141c01825009041c40310f010800300801e0442000e03205140b16002c0421105503800454044030001e5549402d0101c6200401c41e25500141200403407969981185006042d81c2c00706107203800c1290090001e01000302042020010200560108007001066999101d07400c28266100d010054851595801107031402054258100e510580e000d5000c801c8a46c101045000a5101d150700500a200c3c51a0402c0200007034044c1e4000d1503211002032080020040c800d40c060250240a8035010541c110030b108022101ea00000003070b507845900e00c0259040d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 28237415 28417271 := by
  have h0 := BRFrame.cov_init 28237415
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28237415 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 28237415 ≤ n) (h2 : n < 28417271) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
