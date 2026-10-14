-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0889
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:28:36.293877+00:00
-- url     : https://prove2.me/submissions/63b8a2b0-7177-4b25-9f42-53eceb720d59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 159712230 ≤ n < 159892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 159713480 1250 159712230 159712291
    0x110a0c0501110a030606080906010b0d090204200a27140613031505150901090c020a150e070b07080f030402040902030d030510080c18040204020922060501080906 71
    0x100c082d40800100c00e803d042d8140e010700150b0700c0c80e540c0d020079030311015030450b52400207028180500d041001f001d4003c1c0804c2d482181d5191010300085000075902d5801c505880701c2ca0506615040700060080d90369038044422440c40540c803d0700c00101901d0f03010090034003003c0c01203c1100c451552503c0d0540d5810080c1c404c00c40300d4442031005191a45040030b03040d6800c041d6490010304006c041410080d802100b4101100d010702240740c3e80e882c0c0404100074100c200e410b04250f010300080a40801c90708410307410a581360b001c0206450303000024803441c24440303a00c4139a41d01010300c5080006000d400465a103140f20b050400d46a88903800007800078802100020b60601c2034482d24003906070940c1001d0322502141e40501c001070390b100c5107075440d031109103900d541c40b03000d094401c540415410b4115400c01d0000e0001030800b024400868403145206005640c4005549490f030b5000c032480c000c4001a02c82840c001c8a00d003050000e540e40c42c98040c0c80c0350195000700d1b4420b241c10400c600358 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 159714730 1250 159713480 159713501
    0x40f06080d0905030606010503040201022d01020d06260703141504110108070e0a23151b0a0809040e0f06160305060d020120010b0310020d050a110a0c0501 68
    0x81e550450380307040c0c0c0607042e040c00b44500da0080c003400c800629258014801e07030707100e00e4040e00603180d01110301d248170a01c0e84030600380030325440031900c901c2410300003403000d40741146815000080e00c506040814805d452146e07602244d01420126007500d580c000309000048903817001c5c0b40c00f00303502e01e8580b43d0708241c1c041441c140220085010001400f418814a090810003a2119505901c03004d60880c3c03405120034007103400c21070015003088250241d441e203250107582111010080b410050010320032848c009504c501100c4003061800c0a00180c2001c034200c0b0f0b81c940300610980e101c9e942c03030030058001c805809105940d100024502d81d5000d201a0b01c0810034141561058600100692450807003103822030002458203000486a09080100c240140d8058450f540b240f0f040903090300d0f44d62010700c201610f95480b000f5040d5140c0f8108489078681e403c1d0480541c642c40c0401c4070804032880140b00303600490a00c4032900e103551080c0c00f180c60b8210240343c10545425a4102280505002c1d144d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 159715980 1250 159714730 159714733
    0x80901200a03200a0c0b09040e070303020a0506010806010e01060c030e18010915081207021c0506010e070e010c1e0f0503030115050c1b0d080c010501050f040c0905040f0608 76
    0x301c19003019032000c01c0303841ca0541000401045100b2001042c1e4480107010000c00e1454800024000310302180058840c4d100001c0000c103668890f40303800c034201041c5500840260b4440e540c04001c000c010701072130307014144600003480c0540c545030203201010b0041c41a04188404000d07014203041c802c4030803c100c810003404160801c82c421703a0203191004240f01d20606180740c05103104c030015241c442c00d0100c5079600003d0100c01d48a02c0d200d00c40c1d41c420707c81280c1c060100388410700749459923441251842e004001034521580361840800b1860f100400280801c0a81d2461201b07030380c0c118407449183d540264400b14014612060000038001419010303201015004c031102c1041000030086060700e400010b820b81f40003540100781d0315400b070302d80e80c074815030485000a032100000406100382850010190603400501d0349070740c2e403294401c000c00c94207070351260010701c1a07060401d00f12078000c00c1640d00f0410800c080500604050646c0140f0f403003241c99100302c0c1744088041e0400e40c00340c0141c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 159717230 1250 159715980 159715993
    0x12040f021216090b01050c0601050411120a050a06050a0605030f09011e06031e0f120504091a0301050906160e0d0206041502070603090b072105070917010908090120 72
    0x320729000e01181d83c410009460300346040c031100365218509541e00c185018000704120790038542000080c004941c400d0710f084600b40044a071802062640c5809104095800a07a5050064881064410a401045c0904003c42e400c110325640001160340c03003544c240220441d034590401183c00341500460000c02e0180c50200f050304406283d100b07808813446031000001e0a810070302030046809070076401030014803035050b6800110300e131540c00c0f418118903440e24600d4207460f960300324119822241d0304030543c4107183c0c002407d400c0074894550040c04030300040030280341c81c448040c252480300800c082081030902241c00304c0c1d1180e101280b40075030f0041c400b50700c60b520343c105d0522180401d01c070b24005120f04280001c0c001e01030f20030003051540001c4598002e0ba18082c042d221130611940103011030381080740e6605c54005031310565000e80e000c0e566080c052407411000e03031003943d004002c4c0b1406902d441c0e50b000004985408803030b8618400e007040314034404040044083c500300034003940224000e44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 159718480 1250 159717230 159717253
    0xa0b0a1b140c030715021c02010608061003020f010c05030a0e0d020d06020a08070f020c09070e150c010b030c0f090718080c150703080c0d0605060414030c0612040f0212 74
    0x1003180280c203201030f012181c0c000c0d80c501d9110102c5542c0300944016030000072800070300030202c3c85003c90029840c000401e0281e61115900d1505004840391a030241403490706100714506446080b004280034a840d450b1002140c84441c0c40c1e200380c45644050020072000c0c03001684414112040054000780b0305610b040c0c403400d2010284d07000d60714141c001101900007410807030081664059820156004141c625008003d2000e8a54094562014414401341010403951502000301002405a41c01c40d15986414000e509444d801d0f1100340c402d812444402810340c50341808015420b0044400c1d0041d80c552400940301007000d4000034190404921004c245503070002050184000d040d110030b901103148a821000c24040c440c2c0080000e0074071030108505141307007000340103e2a540b0000203480383d43c4000040131588581c0c42140840c050341043d070301519051000402c42d0342c095401525200b03054208000c0c0c600014401088071800850000940d101c40c140707114040350280c00c458040800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 159719730 1250 159718480 159718483
    0x90506041a010e22110d06061a09010c0f060b03060412170606180102010e190c0608010305030d02030c131403060903040f1202150403120305060a0b0a1b14 68
    0x4440c190201e120300900001140d452500c111489284401091219085a0008060400f2009101382d8200d00a03405202d2079544002c065044288100400615207180242c44408004145248280c0188c1400400b4983c6d8000407014141d5500008203580c801d0a07242500c003d10105400507090311a200410040009542c6921a9800240c481040060070ba07050840d40480403518150486014452002ca909103100c2c0a081d0748030500001c5000d003003a89400c0e107040c0301d140041000781d40010300305082c0808006250b0140400d03180000c607039070440c0c450303995a2290745026040b02c1e90000001c0c5d42c0b03000c0402662040034002d0300e1182145d68800c41d00200e010f003051242e102e40601d07801700380d00500020484086905101096074500d180c00d08420852885030f41c26a041028003412500c68030412006002541c0b040d40c006000d14818000142140e20040c03459025080720801800144a180142e0785024014030703004901010f0302e01500011003d444000b014000c4012507418481c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 159720980 1250 159719730 159719753
    0x10213031104090201050919051203040e060301020304020d02190308040b0c010b040b1c02240c07060903110609040e010903091505090a0e1003080c0d17040b07080a09050604 76
    0x1481e07410850030300800070042141c061500c02408181c1c10815803115052524200700d0040c03440c450015401e542d1004540c0403c048a80c0044079080000c05000100304280000d030000300030f03802141103103040d03030100700200544240607200340d18910588075541c110030344600207594485030940e00c403030340c0701c0c5e0130b0301039411044280d0b03020350030000d501c1070b9402c00e44108410204000c00350303042c00380d03061072680d405503440b1800d0744c200c80080b1081c0000303482003030690300000402545940c0c48240d0140e8505090560b00a5030030070000e50820404101200c410409031101103440701c2c0e0f40e905070000200201046101c4150365420240d0b42424160040c070b04030112161107815292110729400c0445c0c0303e1144212260b40040c2e241401c0c4484d442101c0400da015410b98804040e2944030340f40d001442d0400350b03000c2c0d0a6031002404103055a032107405070313031401a40030078a0168201a5a040400e1700e00424680811403040300040f040031180c1c10031208aa000b10030b40c3c086061030b0800c81034024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 159722230 1250 159720980 159720983
    0x306091e0c030b0106030b0d060506120a0c030516120b0a020c0a0b0105040609020c03180102030c0a050f0d080106051c0623091003020303160c030209090d0f030507210e01021303 78
    0x203d203100028025009004100035100d0041810307190140a5440c0002803401500494020042c5a540b00c6980d0b409c101c8895424000c29803070311601d20354a40103181a02c201010011101d500900b00401d6601d0001030300066808480030b1032981c0c413a00b056009008410111301d052240e1217245c003e01480003020b5050341c000b91424404551244804810307842102120b082c0c55008103c02104240d80146541b03600380c051041e640b92a0601405e5441c000c100e00d000e5625400c82d60200010b49030400400c02041032609011005600d07100002e0800e0050034080c842d80b00348a0584641c2d004503078413010250144010108184041b40c0708604841d1041e4402409886a000414141d10b40c032242c20741100ea00400543c502203030b00d000d018900001c080c0845503440388890110042c1e42c1c19424901c40c0001c02c3c0280030b01c5000e00402444400581d526205143c80c20040c0700e22680d200b00640303d22910f000d403d0040100b1401d4a000924010b112840070754404035540b1121a4038107030050032203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 159723480 1250 159722230 159722243
    0x110403120e090903040e09071d0108010c18030f0203151614070b01050d0609080f09030118020a0b0f0403150902131407030902060c01050405010f0f0603020a0306091e0c03 75
    0x7805000180229200c0030369191116900c00d04c801c201d940a640c54056100d103c440664051565504801c009641d903110414605100b100c014002d44000b481001d9100419103000080c000b41d2160039407901b00503000103000074810000312001d44d24100b0000c2c1c455022000b01d80d16902d481030a6400042c45003840000003125805114019801081a00d030090b42007010050035928180030480304c41006041280c6507911003980c81c01081034503014080104145058079601e41c54402010308498202000e12003862031840b000e07001d42c0750100704c0010f4842801c3d46036075825040c0003200d00c90086a000030f0080b1f5019100a18031412900100009482950050f075180c44010081007507540092441e600700500100240b0114480c2d0040f5000703500181c80180341038510b07456642034502c21102070718035039110303243e60551000074407070040b04001c00e540402003c2c4c21076000691280c03103031002510032621000d41c4030034021120100781c41c10006201a82074141e0510b018032608101c0e10003034901 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 159724730 1250 159723480 159723497
    0x303010f06080405030307111c0c062904050601021e0a020109051002030306011b0b1e0a020a0c0b0907050904030c0201080a0e060403120b060a200d05180411040312 72
    0xc0902802c6064080d55000300914119074440c4401c4411540e01c5004001c244540405900329003d04e0000070708641450b6504000e03010f4509103c0141c843e20603036281c5d10310803000c000589025940340004505001c542c0400d60b81c607643c2c0101e24004021040b04106e4181c0008a00c01d1100001c0c1050140e200380c0f6040b076040d42e91410000c00c20064030145c0b02603001000003e074590311650f4502c150204001c520301d004e000c0d648404696502c21640400171f40c0c10301540300c0c000201c3d400403581c05600460250300c0c00050000080c50030070304440060881822901044070500c0074400c120180c400a03045c01c00501d0141002042c3d0600c50744141d01064030807012406c100d286000710300c00a00f6400040803d503d80d035801b1100e00c01c0420503a54015900c107100b0180790b441d000202203d8103581ea0b5198440c107440d84100507038800d1850421700e0307880514400c0e021a080000e580602c14034461046407004648042400381800360780030310f00b035040050040204a40340d0480310040008c0d5945410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 159725980 1250 159724730 159724739
    0xe010905070e0d110303040906030b07030f020901120b040603061103040b06030115030305030601030e0303011205070902070201020706120605040204090e21190e0604060201230708040209040f050607020303010f 92
    0x1800003640b040980c110503058000d001090030b2001c07684d100c1401408903880c0c6603450429508460498000712030030f840300c9081c0600f03c1c0d40350080544030b4250715811403400060b81c1c00a000900c41c0380c0605207482d200c1c41070500e09c0d075071030380120021500080280110348a01250301250350040f1000c030341c903104039030200d030141c00c05208030b442c00044100344032006801c2d40c4041e1030540008101038105500c0c2c2000310301c0e00030240301540c000c0c881120707618158100ea01e0f000f13052540e01d401805c02d0303034410f200d6000980e07400946801200c40504207050320b1103241d1091009401940c200340d400600000c3c00140c1e4965075488405600c2c1c0b103805403803814154040d0130b50b8600c25902c40006400c0c0c00d0125500310500c1110f0b0b1200720b44582880c682a19800e00480d5840d009a400080940d560745c00780341100c2d603124080d00d00c818100703c00007040d10300300030b001e0031000c0040d0019000d4032520b00010f04000e5010141c0c01d015802c501103c28600c2e01440c02981c0764424003c4e0955030005040001c2c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 159727230 1250 159725980 159725987
    0x501060501180b04030b091e06010f0801020705100903050408030a05040f050316060e01020c09010b030403020f0712081b3403200f06040e010602060705070f06150f0e01090507 77
    0x540f10030701d184601d098034513100c0391880e0002030b148000c640684c20b03141d40070300c50344800c241080b0324100140c50903609d0b1070030403c002d05240d0700c00c0240340d00400905000034004902a59100480300e80090190b10b6030404070f42a001c1e039049080030703110016500c0c0c102c0b60094042e00464084664000a0603101c10915440b4540746222041802e00c0f20000e0001600643c0c202e81c52000c1881250600c10b541000900550801c1c0d01c00422228008240400e05038140301c003004400c034060042c10303c24030f040b070090100110070340e02401120000c074262054014511402d605840c00d601100d0004840048010010902e11a1a2030b0203104c1e40300034882c201141e0305a81120380143d10101081101c13201c9152031901140419480384120011008175038442c406000030f00842c2c900190258109000603150507006041241880028007903c0b000030039000ca1511402d074454070100786400074881100303e0a190750015207442c1035140010030b00c08a4924031904071601008140702e252039110065 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 159728480 1250 159727230 159727277
    0x109051f03020d020a030203010528060f0c06060e09010f060b0906030603010609021c050604060e070c05161205061311240d020306010e01020705090a0b0102010b030a0501060501 78
    0x180d40152101403040001104949618164500380c18098a48044080030500301c0e03001e0a40c0b1404258040018045809c02c200c40307505001322a09401c0c00d80042844104403a4030611a50342041140340701c03030042c10322554150b080705500020510100b5262108004c0082048406000940ca05826043c100c6881d0240a013285c0c41a00f40d1882e00c980c99040c000554001080c05800d503480c3c2c240007070109414030080c03403e6503c408929040c4610000d9030001e80d00062310003071240e030416200b07100780c00f500a4001c2d0003130441d00300481c0140051600307504001c600400c00da12514040000190110102402000d8911581c142c40d425502c2c0321304036504451004d40900b0380d0350b610003a54224186440240c1019404204c5502d0218000018a405070700011084230308036004000c0c01001d50300052920507030319090019003035650408010441382c4100908070003800f6202d41303040041d40d00030f43c0900d1a110001e0309890840c1558100b240c0070b8852480b54500040c400e0a401a043c4040c8404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 159729730 1250 159728480 159728489
    0x114150903150702240114060712020102030708090c01050405040b0310052511070911040806040609020a060c0b0415150308030f0112050a060903030b091006080106020309060405300312060109 84
    0x710f1034942d007010041103031f20360350013480d5401400810460340814500b2031041481c4d0f0407a800540c0c2ea1500c11001000c0d4500600000d03c55400220010f040d60b030084141c0b001c4e070f28185c500248580303001c0c002900d8201d8480203509814540014040c200d2403000d0700c4030b001c0c07a0840c0c10b4414038200c0641110a407840540542d21034010820a0011044642011034540c0001d2035071418151551542410001c0581c1c04032201c5980300840011404d0a0701c10038000c104504041c03c00c1c0308503858411850900510003090b101c100d8607401881030090780300108a47d42e00f4440406070b0b88a00d42009140c0c81a00c0e440300c40004c4e08000503107014140000c401440e417010140181c00156030304c030000f509a0b14000c80c01e0580718114245aa260707900441e104107280c404c0405540c4c9440740c040d09088041c0c21803421034204101110703654440208a4040f50702c2915900800d01051401c080781c10b40c42c2079105a40b449100002545000000142c04608820a882801034030341000564902940340725 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 159730980 1250 159729730 159729793
    0xe07080f01052d161e0917030c060f0702070314070602150108060a0b04150603050603060a090507090218040c0f0305390904020304050a050601050609090705181f0311030114150903150702 82
    0x4bd4401c0e014070b00781600f00308175004480c080c13500c070780c2c07403031404004078a13070701640e0303101c0c0c1020450141d04008518a00010b4490b901c0c507035040c68580c07900c81c0801230003408400d07102c119222540c2c0351139010080c180540c0c41080607081c1c84200c02000780405a8842e0322034441d020100d440008544034250200e85c1c0000140340d01458500c1c0b00e0040c0d001134004080b9520005210035041d25140940740700c02009546111040c071010340054210b40000c0d2001d02601412002210009011a00d00c04900b06000000942000380d41d06088584a68070a0701d13041400441404108500001c02c3e00c82035100e841910300c90381c2c1301c07402d100301d5000701c045450340701070198080340825000b2002001c800b02c0e44200980d001950741e0115408010003070b03401c103203030b2400384500c40360700c0e40352045841e040c0440c00ba2902c2d551400501c007003030000d0841e925102d040c100402d051021102d0b0100ca440d42030150959003507407028851311030709282c201c44100141c0105403d101e030380c111130613040ea403844130141c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 159732230 1250 159730980 159730993
    0x204090e030a02030301170c041a10020d020c1306330201020c15041109010b04080706020343050307061d060a0e07080f01052d161e0917030c 62
    0xa0b00c603074400000b81811680d008d4580100740075150707070041d41b00c40000103040a000e1a00c0c0c10a12480f0291034280c8400c64102401296545130b0200e0511100102142d0117070118030160a9400140502c0d80f08200f00d1090b100c480700e10302e0004a036201c4109416507541c0c0014203620040c1d0a030b00c40c0708aa000c580d081180484003401c800800a60080c6c060260310303d2140740180841d0a0800a80000342001000b2030104220041040408082c050310b102941c14894401040241c440032042900520b0168880d10003080400341020950700400802d0440201858200561a644803c005030740f19070410344c041c042280d02401d0321484000788801400d0503a90701d5211002880d611100140a0180e003d00140c418420010303042c2030040d00300000341c03d080041104940742a4400420942e00f83c6c0c0000600540d5001040399104424008001a5103014607084484466624019a056007203590140000c0c0d03005a0001c00e5940d0f01495201044100454030b9030f90103200d07540b00466100d00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 159733480 1250 159732230 159732239
    0x605030703090c05030d03140106020f0601171603080703081302060d11091203090406080d081605160b09061012080c03070816050601060c2307050a090204090e030a02030301 76
    0x75444014014020458402c54549920021b801c1a40000c031040000c1d8440e507800d0a4103001f10b0300203005000f60300042100c40c5080880c42c0c0c992405201e111203107815500900d01e1000244055142e000da0310100b084580d8507464080105d8022040c150001103a140c0000c40071010b0743c1d0100c943c0c80e002004941021941041e01c0d01903c1c010740e8088011100f80144990798072885580600500554013440d01e0302c05140078001240c56075400b00410b50300102c1e5140116401c200700035080341c501059040d207502e024105039003606c1029051803251300945424010f014803003140c0742c0901c50b07c0c02500c0c1c05498040b80031003e0341c1c607401600084044c407903962000414190040c007a080003242541c0c00c204071a00c0c5d03401150040002c225000c1451741c0e8060401c1428001c06005d0401401e0a8442044d55242c9483c4601c41c417000d0008210219860301075260100007c00c01080000c028031241c907190040035002e03400500c518600a428543c44114030b00c40072041d01d04c2880650700441c02c40c0e181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 159734730 1250 159733480 159733487
    0x606010905130605030d031e09210905060304150b030609030f0a09050628031a10110d031b050f0d020f040803031005010f0507030f3b04140106050307 66
    0x5800b0916441582c1c0c410020b0305440c14080c50820200c907841c0003078008203580c400f00c012424242d05480c0345240041010002c0c6641c2004101c4a0703110280e0074450945c4401654028255000750b40d0207480841040104410208018001d5103c850f041c00f42c4440302d010326640e0303031040d40d54080b150801d01c02c40b403100c90760305c000e0040049140303450b803074280e51003001c141c0701d0f030004e0a00d856400c4010440c070224240e001120b40c90520b2890100111824102000e2545100d41d08403481880940c054030f0800f4818240fa038000704408003610494856000301800408080010300d10b0304030040084010b040c040c8003a64500c1001c1c003040d504e42040c00018030300075440512030a504e5282448082603c0f40f0401c051403041d0084181052418200360025214143d42c4510f10300308a0100680e00c00a83c1c0800c1c50b10050905091070356020f00300400c50644c0c0702d815072150802d40001d9903c2c2d01030194a492821a6010664080100c041020307822007150a09020303500102da82000444c1d1014407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 159735980 1250 159734730 159734749
    0x16050307030f0203161103120c070606050301020c010e0601080c0102061b040b0d15090501080c010c03110102160b0f0103050d0f0302130305060415051003021309021008010f080606010905 82
    0x40d189000507000180c0e40007003040382c0042d1541c004200e030544031002402c3d0000d51a16091559000640c14a105001080301c01000244030b98104d88001c82d0020030048160008409040010300139034407101d168040c94002d0240034903502e01485841e00000d00c001002c103210300c07080c1069024152560306d01e40b0725911300c1038108248095100030400041c42085c5000034003402207002d600411482e54095281d03200c5160398110918030313860000100580302c0300180032921800c0c01c0c2000d00074084503040a5400d48141905d4443c0ba5000040b20884100e402046211840c42803026918903201c921000d00303641800d002c0241507501c030341e10080d02c240c010501c800b0480468a805407030026980c10010000010ba40129802d43c0300c401840304103d503d01c010f0f050048000010489440c00c007480d40b40b503905030712019000300000b044c5521000c10581048100580252038612860500100248604000d104520034051801000701c0c2d400390100c0c42a0181c44147c0d07501c0c1c0b050f4100400c003c1d003102c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 159737230 1250 159735980 159735991
    0xc010c020f21072304050702010b120d090b030c0a1803050a0317130c0501030f060b0c060603060a09050a0b091005090c03160e150d06091b0905160503 66
    0x107422150608680d4864068500c00c1030b00c030341d200042019048000f80703041990b8002c0c80e66803040540c08000100341902c15240c0840c00c40d40801c1c6c54660303d10aa004082140340d264014140010720703580c441000420758a0212941d07104c2d1f50fa180ea038509601e03a8042038402000b468020801c88011074800d800c80c10000c2d11011b681800c0d90780d6699228640714001400b140030130101e030a150707150442c4280280e03100d110100c24000c40740c940d60350100e422107140540d03414140d5800700260105401d5104001500c03201c0c200e070365904c8074440c0d0341c0c2c0d13038070412a86107100e0300c40c500002d80304d00105e019010807980d101009180001080c3d403481d280410040c80768160b0b1103000700074143c2c59200e0044038010645c1e000640f805586540038141010b00d001b112030308a10701000300f005414190822203074089000c0c0500d40742e00c10301300b0001c0d2040000003c0034100d01c0c20310b03030040103000018803940320020700c850303e044001d640c982c184c205a41c0202c5802c0802c0010001d003104040c0031700002c55024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 159738480 1250 159737230 159737239
    0x1503030415020d0305010b090d0314090d050102030109050601170601050f0f03040303060e0907182c06010609120b060f2d0909070b040303030908090d06050f060a06020c010c02 77
    0xa8441805140707910140404500507804881d642454603058402c86000d04060b414152a04807460b0100300c10080180c0014100a0300040c056000e8140c4425660344030b900800d228141013103401c089000c0e400a0081844988c82c00000c40e00c01d6009104060b1401e651958031192550750307000640741a00441341d07641c0d019104010710110500400001e5224500c2a10700203092801e00c139642c0311010004001c003100e98840c0000740603600603000042c200503211a00842d005c05010a50800e18a515281100a0150102e56045220b0100b0803078141e6860303640e54589a6510b8040700900304400d00040c1030800500d01003031950401c0651104050000740103080800003000c0c0900316020303100e900c04408400d40e40400c41d180b42828003203421440500c014141642488032800c01342c0f150784030040601d661007814604108002d810384502c6100200880700c05206400c2000281c1000c40c2c81900f8422004001052840c041840000703071009603006007885480d24006480d25810050241d902 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 159739730 1250 159738480 159738487
    0x150c03070804030602121b040504050c0903070807090e12120604140901140a0501080601050d0314040b03010305150415090807050109030512090a0f021003200a0906030b09150303 78
    0x100310441e00070401107210b02801681c955038801c81c2110386001802092200c1540810440100c2c812820358007903070411500001d072a04c0e030301460040c034802c0ca090325405008011001a8074800404c03150101c61812405125803074803800140c1d1500160700c02c4a000c01001d024003002c0c03150580603e0752140c00900005840404d064905008600403103c0e02803603074550b20783c1c800144011005541000c0228024403055050444c81ea841d90f41c14080d09008002814030402498403c041c101406aa09040103540c1c7c1d41b601c2c0b00e900700390310034027050311f051088040c486d11720692050814459074220b001c0d00c0c01c50040e9903d52000d492007034001d881d140c1060112a02141003882510495842030712004e94441542220354041403000340484c94035008000d262000c1500500200803056044030180e0601648000a500030021089143c521040c03816242d650504030800070300c907008440c0c42c0c2d001d45582c0c80004600707842100300c119401a4800e0046200c0c01c115402d24100168002d0030b072401c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 159740980 1250 159739730 159739733
    0xe010503070e07180f050a050d0210030504030c0c09050f1e0705030603010207050f030301030204150602060402010305040c030b070905011404140d06180602030f220312060b13080c0a0302150c0307 86
    0x1184c5902d4100160501e00301c2002c2055103014100711000b0141035929101c841216000244405410000003041c903031618002800c051148001c01d50507540000714202d015201e07600b1600806007116140905070b2902d010132281d0b120265400700c1c3c225507800161141d59000d10032540c2d500701a02c00d98240d902408a1800100144a00d01449409200540d1298514010481a00d80400d000003a002d0015410b10240e41c2c04106660300c16020708010030030782c44514000d10340714080e50001d0002e061100900c568660301a5100c0708881090382c1e040541003014401d1121481a481100e11480d1950708030b402c03508015040c5103203a4068140040d40440039504440b400300446800c48106a00104200300015481503030340c2c000145000d507c000340040f80c034146941d03211040103003c0c0245244000e115a42541007603001d06544401d4a441c1c2c42260704106e1405c41d1800b64541c03500401c2944401ba0a0240f465012250001d0415181c500d241480001c0d03a40b06211400355800108020b20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 159742230 1250 159740980 159741017
    0x603060f0f03010906050a061203050a0309020d0b0f04060f021303170705060c0409060b090616020d02030f010903170c1207050c070f0501020c18150a0e0703150e010503070e07 77
    0x411350144201040624000c98070408841680c4c10102c0b80030000c1040f0f002007580107040d0350b1843c0e21400c1c0050044141d00025030481c0508400511014040e03080003d954100703044180124894103040c032580c005091800103a0181a25484103c01c0400042020414000004002d800080c481c0ca01e020b085840c5e15003840c104503080c0416000005040188200c00e114140040c01c194007914280801000000c5d00c40c070645961044020100409400750350b0f407010364039583c60b4000c3c200c4101007010b00c4c3d401c0c0a00b0000f00c0c00d4000c070b06681c80801094420440303861043c030310b00c85141d1800d000c0421030500e02c2c4000d801c44040150500150720000f10403c0030401804442d502d00d069035103440002440c000c020412903001750416120020045601c00c0d0707017504509440e10540c403501400c4046000c0d501140d2011406e604040281300d01c480d015801440008080c000401400e5292001c1c002921001c2c8502034042c0d02120f8104103000e15a00c47c60b404c4441072624119a001911014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 159743480 1250 159742230 159742241
    0xc2202040909020a060305010f090903030b04090b0109110309030409050415060303050415050a0206040809030a08041806060c030e0613050907030501150212040b180a080304050a12020603060f0f0301 87
    0x18a1001d42d80c50351402580792004114006104500c0c0500443d030400607004ca000c003081c441c5c3d00360316880351114010103009800841ea100d102a108000c03150081c01c1413130b0320314000c0c4268000a450040700c508110844400c480c8503040c0d0030019450700746400700340801071000800070f441c98102c175905880c0120640c0284401103003c0d0765a240c8131b42c2044d02c41c0a14109400c02030b414042d041045408540e004641642c1c499001002c0c20f07203a0044002107800c2184000005044c000005004210100e9941040c404890741000400c0080d4451000f9600c200000c24040c0205048456400061402e04018140c01b6010440c61803090f6a50000c00c2c5529015540c0c480401d8440c40180030800760045540d504880f20720007006102c0241000700c18500c160300a04007a05000544061030182c0c50390211544800a00440340c1e456440740c10a86a40144c02594030880d001140040d010140d84000184150010b01451841d00d412003002000801c04c101240c212000b1450800644c1d403c3c4600c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 159744730 1250 159743480 159743489
    0x603070c020f01030b100c14010e010501140a0317090f041404031e0f1103090607050709050c0f040509101511060c03040b071103090402040b0a0813050c220204 70
    0x1400c0c09032010307104000e0742210341d0454038105403920344a038800760b80d80c03c01c0d0000781c1e0041c1805010a0414100070300c1450042100c814550f0808500e682400d4055202d503048510f031203000c1750b440320480d00700100d44003107110181c05601c0380c7c002c0f0103407102d00000900c1e0f844402003a49407102412000308050f22180200c0b030380d030b10140c2001c0206058000ba4109a42314403801c04030403c0c00c1502010306001446400c0724100044020001c500d07000400c2102d04034940141859180d40182c0b808075520000c42c000d80c1641070a03e0017141d4040d540070143d03498011403640fa60b0615003003505000d0001c00c014801d00b4208560280091103054654200c500e4901c6079488008007980c0000c030900d011000341506c800500d04204002c085180189042e4001180d85840c5201655011445143d4000c81f20104d41c00343c0300041c006003004610006000000003a1500c4001d55074100e0984814500c440000e000e9400c046c02c514080d280500c06841300914080900d21101002200c410898005401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 159745980 1250 159744730 159744737
    0x1203060622030825150b1c0503031f080706030c020c0a0603020d06140d0308131401090b0105061806030c0d050c13050306071b020d08030f070f02010e0a0b040c0302060307 75
    0x115031295601d038a8000325101202d8128059404096484100751010071007440301e01e60b0340d150111b03029580d8200480445212130141581600d40d801e0850f1a0750041c0c0d0001d04002c02641d25103584403910304524222110000a4038000349010001c0e00a006070f540c9900c2140129441d41206549500800000d406035550040e104d51095005104442540d0010b610310380e070b00d1000001076507030b444461149961615100c403d588030300c44d280480d038107082c0005240c00b085000c0000003e00c150b10440400e4040c00100c120380e680c89050080d40d00c602c5582a901040400c541602030411030f0065401c00b48440700d140c0f4206503400d000080303501c2a10906428000000c0c480302000d00c2c00c00c03040280c80100c01820701e90811900180000413030003c002c0d440b0101544910542d0381d160b001100c8560003000c041e9807490240d1031480f03011001c5400e440400d407c0e03941c0c415000d10503c00d42d074001e0240001000103803083c3d11203000781c0000500c101da81301ea114101200689404001c0d6014038510349 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 159747230 1250 159745980 159745987
    0x7060617010e0d030905060109020d020f0a0f0f03050402090f04050309120c09060a06091509090f0b030f0c06040314070807030312060e060a030227090f0f12030606220308 75
    0x84425090800382c03a00388040500f0545d50002046010509504684542ea00103a4403008004103102a000d40c0301c84414000300072840480d45600001302040e01192581d0f448080407601070150116501a10080d401c00c4400300050405000da000050b005030082003200d0500c541c42c3d0010750203500440c43c8030714a03044007109d41598107011500c0360f00070034101c8042c0c0700c4a00304000101150302e280b14554060100291503454a8001c18245014120f212401c0c450000b40010040280031a600400c0c000c4c454006145c403410b00111f450f5007444002031180d0b140a01d59214030455110380618500b1034015400c1c0050343c4401044010000d40c8070391101c0f94100d440c01d80c481c044860030b82c065505505d4400030006142e840406002c1501c1d8111101c00b030303001890f0300610191000f01000390642d29a80240140c0407000110200210302d5142203d010101048266840382480098410041c1045c070200310945807402c09450341b031010918007000c10260702c1c0c031800510b8030342d07200742d4040b400007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 159748480 1250 159747230 159747251
    0x304140712060f0b0d02060d140c030609060306011401270f030b0f0105031e0a0b180f1501050f010c06021c110a0206011a070605191b0906050706061701 67
    0xd000383c60400d5039116003002403040d03001c0891140c0c20f4014009104181c009020509294564401c0600700034071001b00089140c00d2403800d0b640d51095408610904084001415038078001034094103030b904240000155804400041d82d0101c0740701500c0c0340108170f00303000c1e8040c5114504400020001984100111b515504202c032a0340e001800310f04c01c0304003207401440652000503ca000001c40d0100591803030b0301d54840281026080040205811a4038003480a080f2038540e49100c04446c400985600d07000c5d02d101d1b01d0b41e403c10341d0300d1442d5036800000108800c0c5004541e50300f90039410304141040d0b013030726a20303d02282e02550042412640030480700300420300510443c16040079001402d440d049108001030340d900300c1445080c10716124a000031229a1803c000c3da090654460390a10242c203048000d81203c03100da80f441c0350050700d03001e00c441d0b04410000c80295414010b480712400c0500b4030108a500380d10900d41507900c01c0e21240005402104440301c0d51450b04804000079283c6001c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 159749730 1250 159748480 159748493
    0x12180816060915061a03010b0a031803020a0215160204020c07050312030708060f031b1207080a050105100b070b1b03090c0a080f0c06030907030210090612060f06050304140712 77
    0x242d00600140862041c0c5050300c079040004487c1914054500503840d00000350003103000c0c180380e024900241e60380b040c0142c100358000606401c8203108444080c41300744100a983c01e14094440034641d04003109401901604003940141300391200b007000e4401190311a80440d1174403013002c0d041880400000300300501540e002c86140c4d001401100d104582e0000350002980c2d5140541d000702a006c2c00441c1e044c8039903507500b0018120a07006007a140ca07250f079a20a40d40316114048240c13115401c010014200103855038640e0180c1d001c2c6070025013480d0a64881280c5080020f100210304200700020229102800d409584241b00400c000c00c42511001c050010314001a440800958026114003070200743c081182c4c00b103041c082d07400940f0b0750f9444011514049482d40702a40286e0f64600d81071075a80d02c40c000e0790075100c540d100c084501c05041c40300c40454246200301030440b40f03204404d0007640d201d00c0003035170014091140c5001070004580e4a600301078143d444200f21441c114144001c0004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 159750980 1250 159749730 159749741
    0x6080f090105010e1f03020a0f0f0b091810090906060311010201050705030a0e030712050c06130302100b0112060b0333010f0c061103040312180816060915 68
    0x80480c02030006516184486440c01c03c007602c000c40d8091407101c028018516102540000d40c0c009108840041c1e072944841641002d500645916155046c00442c0301c0c60761104840e010702c00601952a049203151034803082c941d01a10742c00e0b29000e15240000d045e034003401a00a503030b005540c001451855880d200484040e03014245055905010801c020b054002d01581e0380700b0320b50310001c210608440c85080c19807180810007444030b40c113840c04111140d842070150000307450210032a0145e49420b030140311a40340d541d000500580c42610088001c0712507802091200006060603860b00340703003451040070707140e46070013000515401104103c0c0d0010aa03840f0300319030010b01030f060071480380c515841d900355401101c0507060084030090380070203d10402c0b81e0680345401407070400002c0e03070070800c0c4000c07580295810303000900148112110440140300315003464600500460510856503140c164540066100e107140d1110383c2030038070104015004d9003807501e115803140d024104aa606000880701e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 159752230 1250 159750980 159750991
    0xb0309100c03050f040b060102070e040c29070303020f07060903080402040b0a080309060702123012071d0301060b040317090112020903070302040e0d0206070f0903030507020a0f06080f 81
    0x10b0910b002d00000071013a40a850300036401605494150743e4000040c0e14019560740442d100c00c81c0001080288842038150100b901d85102c5c40c0c00080090300c40840202e040b1015041200004100003000030780254002c3c003400d12104075850400010b516050b04035022000140d000c99415010001185080c0c4130301d407079448003164a005294109143d0f0ba959010b0f111260740206000038100041d1f58613503448029241c04c0c0401c4401d1040400d14940c6809480311003840014009450844008419400d603111885141000c005d165607030103044410004012841410042e1034403038402c41e403002c0c0102c06c05031400641c843ea54074039501d0183c0e001c0001c60918645064140f0030148143c0c0e0000e0004021001d40c800036803500740701da002030300b400180e5100952061800c000c440c820240415060035907040d03034080e6502540d80610607141840815900000904013902c00d000017806030020340364a0380050590080d203600c54018084100d0305400800100d141c400410650300101e004860341312 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 159753480 1250 159752230 159752237
    0x6030105070e15040b03012709110108180714090606090f10050f1602040c020d0816030207080301081c0504031a0414062401020a0b0a020703090b0309100c 68
    0xa2525000041c0b050b00010388a600c90920028142210350032070003520050b2035a11003484d56969103031050f103d40342c0540f0540c800c074012128840101c3c00b180c070130030150f103801c500f001050311801801120100c40007015226410301032045204514010000c50000c0e001041c1101ea008000c8810001469070051030603200e00c20070012907215440c0c1c904000108203050300c002515540c4030030151041d010340c082c5c811000d000420010301d2055928500b0050a000b543c00300300301c0c40c1701042261100240246800800c4c82c1501040340d11400501d201040542460010704118080e83c601000747d1080c3e00091003a030000303410b6074820301e00503140c900c40b18041c00d02c246044c2c616074544bc0d5074018052004030f03c08004d0005807c0c084100d824400d000d405100362103da28000401d01c00d14107a241480c441100340340550b206550000582d200f0068004001a15944d11b41407908082d5010001c202c0401c4020305000072000b585a01443c000d1400c00081c3c030500c055a003d03082210322084e950000c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 159754730 1250 159753480 159753491
    0x50d0801060225090509030c12070201030b0609211005040506011e030b07050f0c030c0d081602030409020726040504050c0f0d091403131503230709030c09050a05060301 74
    0x40740648040c1004c03120b60030808191591210480790440c051508042c10314040c0c0000301110b20601401030500f94400d0300c0410600c0340034402c2c001e1600860414a420000c021000c0c40c0024040e0200910800c40070121205403c2c0742880c201600c0041c0c174220751700d034401c00043c026114400381c40c401c0d640d00b07a59400348a42c82c46e1150075038400301814075400e10800084810ba010105d60454441d003842d10200d0f5918605c2100d07a03661205058254000a03550f00085003103002035692108500d0116401581401d00b071011510003540906001c0300d1501940c0c61410348486a199024030100841c00015111454a400d1000f86e61008040301424041044000c071031480d91000c0d603000011a41700068050824139104145d00810000c43c0d4070f0340b10200b03183d031003081c2012410040d528440f095102c5000726880a605a81008000c00850f074044e80d0728207200c0d02a6a03001b42d00c0045032511182650340c030340396003034019010b4101402c5030380c450003000104000c03401459000a8280c1c0200f12 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 159755980 1250 159754730 159754783
    0x1180902122a0d0e070306020304111e010f0503060406080a050604120c0308040b0603010608010f0b0f030f0a03120f0504030302070302010c08060a050d080f21010914010b16050d08010602 82
    0x55407040110310103901355103201c2407a84040c100500009035500060855607030400342454a40d0303581c480d88562240350140800d01640d11440050401c1a2041e1100211203c0b0040180d4031a040203044603002a0380b5000011041c404210707600e1500d0145006d080ca500b42414803070102c1174248000c43c02d1005030042a0002030703014403079940c0650440da00d61100e490f400c4c00680906500e41c4115529820b0050314992004560300c050403032601111031101c10178161003450303191501d000c03006200ea00801c002c0004240100c1d51049921852580014551000b240c144107d410907a401c1d4002035000c80c00350702700364091081d08003641d540d0402400e14500305d40001d40c040301c0c500803603002d12504198141080006001c4d900112039140b80152a8440340f840d41501c0071420f940664030031504400003070a8481c0b403185800000c0441440c03501d0707030301700040030026500c4030701150f000305d040c0321061010840601101d140004181d6640ea440c1d403400400a14081482040d401c1080d0191800c28 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 159757230 1250 159755980 159756061
    0x2030c030406030606120506220e0105010305010c09060201050f0f061f0203040515070c050103150e0c0c060c0414010f0903020405130b0601020c030606240307020a0b010609060e0118090212 83
    0x10b07150380580420700a24590350300c0042c0040e0f401c040b04ae50b0801002000300101034100080207900350755030800003544ca90040f801c0c0d407003ea0718108900f04200c08254003481c40040d550740010081e0030120111039103c0d01400c4111824000e20050b00701207402d00c03072441d044514580c81002d80c0400c5080c90710329158403102030720300c2c071650f0b05041d074a100d4400c1c001c80c0070181800030007185190361400d00d40309c141a10190320050b4080c2c841d0007940f00140f0140540d0b4240c0c1c3c2603075000070307021241c00003034001034a00780741e2541c59a06105c404071000006aa45000d1184540d00c000300107541d520503807a21984030368002e0020341c155040311010701303850b40380004c9031079011070100c60b044103120052544002c1e1040720300028030032000020402c61090380004040141c503106010b6070209a90f03c00d821150311a190040f60001411203015014079823007a084081ca804114100010039541d42114400b240c2c088410618010591001c2180071124168840f616200343d440c44044803020284a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 159758480 1250 159757230 159757249
    0x3071208060a2d0909030c14070608130515011202040c02030a050a180905070816090506040b03071814010905031b06070c05031002030604051302060d0c02030c030406030606120506 79
    0x103000703c00700f66510601120081980308000e100380740c000c0040c0742c240c3c14020700e10f00f440c030301c10f896900191000318030101c0b00144100454042c3c1c0d42c1c03803040fa01c41c8402c0c0040a64400c0d400e88151040780100b200340f10324840140d008150001131140d00b600d50348140416114400654000d540080c0004500c2c2500981142c5c8450340c586850f44540400c40706605408a56070001c0c1142c9117407004000090340c102c00760301c0c0107051002c02d41d0102c1e482d08108440e02082400340f00d421500501007000130707001c5200515003001c010704120180000c08424213403043c40039441030b00821030019000d101540c01c100510041c2a059002e408550601200204c260840038811030180400061140601c4114003110b030207800c0040a8441d01514401464082d41041c1c40c0e59120b9490500031994140e8402d800b5180e1950181c030090414145010010017000c802200704254042048800d03100b241c18801000505010349002a92501f4405c0040c40c800880000c80c2d24586010b060107500d65580811 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 159759730 1250 159758480 159758519
    0x10305060a09030903211701050f0d020127062a081615060306060504090506060405131e050609030f040509060109050d0c080d020307020906040c0e0303071208060a 72
    0x4540004946011669040254000382ca074100c040001c0118402055030000e104031326580d1403480f004912890303c7c0c40c4600b032060b164480044208000c0368141405028079040c0141040c003510303115009024201100541c81e060400c00f43d03041407160503001070303003034800d500e445a0301c142002a01c2c600d42441c803c49500a0000c010104010001071405403c188603590710001d4503a0b11181c021b03c1c0009080107000840e406400d107540440c00e420b00c3e1082c2c40c44c0c190044010902900c03076809200060801801d41c0c601030213590680000302d0050050090744802c2400003c02c810000e062050034900b0140c4143d07401c0d0004c002d0740c3c0140200400b03036800d0720801c62304400162940e000680d0100c00320341c040c03a00107130303000d24041c1880101d41c0a141210400400d44d80700c0c0c02180c1c0100d84a22074280700a50001d500d401154150500d640950404030280c100040e52240031000240355402410048642c0400c040c00c1d00c0d031295100250b250440710a0b144d04091506111405400d01e914049 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 159760980 1250 159759730 159759751
    0x60e180c150f0c07150c020102060612010b0d11030f06010b04090f140a09031206050121021209100b09070503041401110d02091e030a120c080a1e0801030506 69
    0x1800041c00301c0d204645940407481d401940c0d48036190300141d162581c1e4402ca101103a9283c20440c092801104940045941640070b0051a6103800810a050608508803043c940d62a414201d0136181c40444e005003900a12821009032440c0c02018500000180789009603040080100120080c000941e01070390981000400c0181d030b520b071040000c00300c03180c00981c0e911010080c0004100c16502600e990b60096944049181c14000c1407800d644d141d1054074001140504000c1010b10911f04080c1507503802540580380000d8020048000c81081c0c880398042c0c4c010320009030006459205070403041c0f0058468112510b4185c8020301726020040c0b0191003105000000f0f404040c003076000440d680700503880c05132070b40190341c8001b0081d04185403190151040000b000109020480c4c941c03400c6a004000b4a01030401da41c071112042501a040001e00840c040540700044858000e064403000700e9482203015a000c5444c480b58100c007d00c14004d11171030900501c081607022404543c08042074071f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 159762230 1250 159760980 159760999
    0x1d0d120f02010212132906010507030c050a060b10110d0521040b0a0e0f0322090e010207020a0b0a0903020405130b10080f1501050d140d0201060e180c 66
    0x44040c0e019110f201d04c0f030421807213240100000000b100d03100031440c0e40640d4808107102c20f082c10ba0052040481d22001700a140c840014895620079402406850710074502800303014003907684c0ba4541101c5680454a560b118400c1c1420341c10141c443c5070202034035160800800404021141e160244000c03400d080140010324000c0b0054142c070310000e04058034202e481585060304003c2d60780b9200b91001d030101030030031000c1c4803172640c0004e400244034102d901a600e454000d2591040700305c1d001080d090034a03a6028002142081ca00c601c1c5400300540c00056034a12136481085144034864001100500040c001c011300540c1c0f240d198800d40e03a06072000501620380e040e590700d18400314174000301841d441e58100f091024440074203c1c1120342c0c5404076108403824501ca45d441d0001d40700707449625100b020041000740f0340a0b0920f1841c038020200c1441070300c0400842424800c11450450251b03444002c10050700207005484c980c4149440030398a0f958080000103911801c0300d1242500c280c1000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 159763480 1250 159762230 159762257
    0x20307030e03120c090609090703050a061d01090f0605060703020d090501080f1512010213140f030a060b012115210602030a0e0319020c060703050f0c0f01020301061d0d12 75
    0x711f40c0400001800f1580070b2501000042c080e103401c5800c06070090030301e44005240300005480c44000c0800c148800d54981c2021503100083c0a0540003c10f0703140c40c0d260008003900c4000040c8039403070003036001c2d207405024610042c0c6960041da102d81d0403c104601041a4102c0217084980c0004441d141d0740c030f20380c4118000a041c110080c501050355440000c01150451547c0d044a044400c06218074076406440c0c0200071070742004181203071b01504105460301c00100150b00c444c0388a40c0c14101104014040300c10b115003041400151074040e5a139003001541c55008039050341c020000d6039141d109802c0102d288640710422407500821803600880420817180c3d5903003002210ba804ca0f401c41c2d8490000071080940e441c1007046100140c042c00b050310441703040c102c3c200d414072a0140c8a6900c0c0500b41e00100100d50b01c140c002075518010212648280c0000380000d6000302001d58031041c3c03040c107000384c02600b500c2060720785226128101400d00040d1148843d01d008404908180f446035009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 159764730 1250 159763480 159763489
    0x1609050a090c0e060a050c06060603060306040f050f03030c0a18061d0307090e060612030a17060609040608030910020a1101050a05070b0405061603050f0c0d02040b0d020307030e03120c09 82
    0xd508403150321107008071782980c029501001429815043c5021203c142d102c007000e21005200c280e4201717405421007000640442d0b402030300c0d400360a02c03400031242d44648030382c885400c1d500241e8050120f442c000a820900719442001450088170300702200420510340700c00900319002540300814a1010105209565513007841002c00420412005000f080980a00e032600c96004031181c6100d0064100c00502d491000000d40380407032100d4548039540d54485044c10200138000b0161035004808100c112010b40302c03030180d0f000501c591001141c641d45840100710307030750251103800d07800c550210718a0000b05003805030385100d18000b0b082c619a20700d0a0001211244504e01010b011001d451041c0410400c0028805201c0c8142003d01503581c280319000703d060783c00669801a00e4821000030400b00c4844400504002c8026040140340585d2a40202c4c05a0420100c3c0203025601108012601e07405000e002d4242e800c1c0005940303000040d100c0c6211410002c1c10114075a0808100035601c0e444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 159765980 1250 159764730 159764747
    0x70504110c030f1308032106040905010f060f050d08041403010b0d050a03030506040204181d0d09030b06040212010b0906090405040f030e0303040506070b060402070b0c031609050a090c 81
    0x1c511007600d640b80c90400c414101c50b031140703000110400c078210b000201c000c0040700391600d464000b101d0010181110b44c04054404003d0681907110b82e96460800c0000d82c00d12a0810460143c080810018900308080040b0302446d84124050500d03480150000b540e1202100c0c140d07051205407030010003406020a005120702006503410100e41c03480841803000c0060500e400a01ca5a81400550b4440d828402640183d1282e0441d121038003100700411500780e0400ba080314145e1003044407200c070b18041c00d450245c0ca05081c02c0407450341441407050080320b40714294805002e4030190b02d001291a02160040c07414401c842d00e5a401003010320199884004031084200004e0090007a8202400c0449024043c213204801040d2500311151a509000c4262401c440d0000c051030b091501c107488422078860010107040d402982002070b0303c00284e01d145214043c1d141d4140a5440c2e280600c00d0020b8201450ac8040c18400391000410855403030103010300076580d440802180103202c410094840c0030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 159767230 1250 159765980 159765997
    0x3030c06040b010f030c0306180606180b040509060414120a1e11070504090f060c0302120a2a1e0e01030b0906030604080715050406021305040e07050411 67
    0x1682605490006103403800746020703041d01180c99985451002c800210f0f484014440340070041c00f080410030342d03403010001e00c5000002101c855040ea03102801c07103c1d00e40024410047d00100100405118850003c1c801c0b030640c0c007008242014180c1e00d0380e03480300402c0203240b1843c0728900c4419070300034460401c07288284480a2340716186a0b10151038824a503a4034800c0c240206001c80d03004c0d11410a054424440300003a241650402e018800030380701c10001a6070b40038000e0040340000f5954420800c46202517580140c0364420345841d2141540e000e480243d000e81000000780303000904242d20282d025018080c5254007610705010344610345051200002c0d0300660008041d1303241c124030160040b000c241d07070800000303031004104030182505442054260744030030009400034074550b00a2503960300a40c0c800c540803615482d12401c5d2002250200e5442d500803c03c0c028521186000c00e0107000c00b00c0e0306004915500300495035601d840d104261240e903d0710034084000d40c0c04022a007005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 159768480 1250 159767230 159767233
    0x20f030d0606110a0f11030c0a0e09190b01060807211409070803120a151404050a02030903090f010504050307120521040909030327050c0306090c01030e07030203 71
    0x312030015034000101001c1c41008042140058503810f95034010404e070030620f92210046010500075240c0031800d5411110790350301403083c1036003485540d03a00724031403004118001c04100c8070700c1c004a03518200b86280043d103d05884480804002455981600f811745056240500c00355071900c0c030441e4841d40a00840032403c49180c0346042d001c00075045601c06c0740d18820303003200c9a110315802d6603849d1168410511241c0044c00403c851004080e23855403c905c42c0b03040802c0c440c0c01000e07044226000750340241e04180070340214002d281414081c072944110b11010440c21440c1c07000c0c945d600e910402e03801c6442503c48244502c4681e01034820b480250002800300c2c3c0801e80c4420a80c0e12443c0c01140507201c40c85906080030301100000059a041c80c120300c11075040628001c20300c40680a4840200d0915440d4800368106132051588001003e08030303003080001c1c078500e00302a410054011030050080d0029030400004030400903045400c12130038a00080e400c49100312041c1001030581009605 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 159769730 1250 159768480 159768487
    0x6030602070308061207051905040606020d02012d0b0d2108061009030f08040b37020c0d1109010303020319081605030c1201180e010b0f06030601020f03 67
    0x2400410350140805510076240c50b22503403101c200300041058a4800594550f0140d4000c1c400ca04181d003880400300146020f2882c25925400014141c954036000440103a11045004002c10780c24040d206200c94a10100700740103501391040803140c0c52154016106035224056a1415140e01c4104190706400080e1140102c0c50f942c54141c0401290350418005011140800d15500e889113041c04919040d80700d03000c48524581c2c941420800c0740c030080e100e861007404002101d001180041c0380744040505101140c041f044a000c801c100b0f40490070842042d1850110352280d0000ba11000c1c190b412254500701c0c420310710781066a07a1300008400d03000410030780004101900000940030485144505c4070f19429600006c07150b048040702c40e0322001544807401d58406001c0e4004540161400c01e81905e0003103805a4803103141400c1e4030404400102e8500c403400181c07103216040008214400a10584540c003000400c20108108102c2c81030b00c000011a9181c0e0003007024008895424040d29103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 159770980 1250 159769730 159769733
    0x50a02030c1b01140306061207021015050a060804031d0607060f02041403061e0402010c02030a0c17070b07121701090b03060703110d0906060b0403050a06061202030a080304080702040603 82
    0x2d514401540c558041110b58201842101c004c000f80c1748a144007a1002d801c1030050404102d0350507001d4186030642c011741769240706502c0c65003d000300040c0d8003440c40010724904820302c059a445d03540000100020032043c4000030b80d20100b50803000c008220761404c5410b0705400200d00d0b20810100034500c0b031406648130200221070f00940200d48c90b850100707160b9006031040c0b41d02d4160032141038260352a407081c1c0b800700070b0b0f51900054000e0b0040c90a61b490411942c003080c504130b40200143c403a5070183d401009104485a041c07070301c0780303001c401a00c9941e1078101401214016504000c2494014180411401f40303e80c460394119003c0c140354041551391180c0d560000d08200321a940070b0b02555002421050181c06042245481402d01c1881e0502d00e0305490018110081c007141e01640f503c3d000258800400003030005940a2000f400c401241440d21504035425588420740c41d962254107000560303404140c0c01d2429400601d00c9990756224502000b09101c3e00030000e50084c80c0000100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 159772230 1250 159770980 159771013
    0x30918090105060103090819140f090f030c0f0f0d1a04171201032006030a020c01060f050a170f0703032001050c04090c030f0c0e0a0b0403050d050a02030c 68
    0x180a2440d000003042075844900046044c0d41d454280504005010807420551554611400c52400080d2501c091401c5107041010700c968041042101c1420010030507028518041d021005c1c4c881c8220001c10300d0707150b00c1e0003140101218002281c841d103001c05150a40391140302602c400154040080c0d20042165860081230314029202070f20350b1101044503c050b0002c0c80c04844240b01412007ca10f05c3e031075136840040f4411003a0b8100b4100ca030643c400340c01611044040c50058090700e002503110b40400e8416400c584ca42e42c424003ca01c4009030400040d155442c0080035981e03105469240e49441081c0c0d02d18280c800c1c000705102c0e21640340004140360340b06250f004503e000d0b28440c510f40c0350883c0c01e1420b132081640c1011512008101c100312402c0154052240d6010b5800d001c203001c94141b01d0304085030104003990020412aa0f2400c2d0a4078003400d802d0054403041a10b1401c09003541c40b21982d440d04101d10409200300000c3c10606030b402001070725090743d109000c0300c0f009440e016100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 159773480 1250 159772230 159772279
    0xb040506041214030c0319090b011d0c07020409080c0d0c03032301060318050307081b071503020a0e1c060f18080a0c0b01080708190f0605090309 64
    0x1e4500c1201d5003002d90380d581c8280b0041601c0c000381c46402e429500c508420704802d40c80035000d03100607401c40d65200e20024a500030341414034011607150445600d400114001d258244141484650184040050034000301c020354a0954059070700090724800d520781281c0c50b01c80c203001c480b040d101e01c0861340038441d03000c090301525510941e024865440d4102c54070302d44200c040c1034840e070003007000300500c0b011b40719030b020f000001c0b1100030300000c0145513240c003411036003d1441035900010004980700141c202c104085003418100d07006040305890920000e20908408800100705600050004241841068028500c030381c01032000980d2102980301d42c0300c0c43c40800b412915141812000c0071140d840e803181030310701c00b403014031515a680c041e56046041da2101c00380c20140001d55801c480402c0c245c09004d406000010001c0165500300b00304a4500420035800c052006121006600020b044034040c0790b941d0343c080d2010441303458440001d41980652101c45ea00400a8403040201c1e0721800d040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 159774730 1250 159773480 159773483
    0x2030d0f111306031104050f1201061e17030a02060f04081b0606011d010f18090e0703030305151309060f0e03070201110609120d06031e050d0908100b0301090b04050604 74
    0x700103810403580c170040340740940c0c8030f640d40c400501c40e004001820807240c14580110301100005a09444801480140f090b5402d51407043e50103a0080c8164000c0d000b44103e0100000025401d0004180c1e000307507100002003d94000180000104080203e140b054a11085080d007601d80000b00301c64126941e01001c03a20b481c00245841900c0036101e40310900120541d4042e5200c081c445040442a01c0c0d40160305186524444107010009001c2541d1040d0f0019414031000780c400b0600d1810010305503100a0b185240c1d08132100d01003001a6913100b8800c6805556040c080f80c42e0015040c40c4000f0820b61841980d4241441495060030340080000c014442c801d8965843c0d0060f900d24072652414100c4807650300b68090030b200381801e102480235100704000108003188031600c0b82e0340d100c880700704500700c8200040d242500c4005c000c01485901040101c61612070321403440c2c9603110360380340c00800c000c2c042281d035400c54400300e40f020b401c508891500881058210b040c2450070300e64807042200e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 159775980 1250 159774730 159774737
    0x903022214010305030a0327030206040320060a2304060204170a0b04080c0a050a06090c090203070c021c0204090b01050103050c0304030503160c050a030f0311090102030d0f111306 79
    0x20410200e1854a60740d41682d42007802141080b0000300203400070101c0070f4001c030540c0c03c00c00c00304003040c2405046003040c508c40da0152020341094500a8503024940807200b0394840c240000e0341c0008030008955034015003134800403078411040303d002c1114034081e0040940d65050301c030400c0144040c80d0010700132501c0e291140b80e9041042c600b02d58071040c100000511a04007240850007040004000d0441841000d05a803100910b0703650309440d00c06110421101c1c151a1411803082c0107000d06204c0c010011b00c0300941c5503141030303600141500c001d80740c000e214000080344174403511089448030903030540c041c1c41003003034030098100030f1030783c03002489400c3c0004e0038240014051210281528003039075142d140e40f030854035600c2c0c41c5020401c80010100800446103a0840840e0042201d00c207a507000c4c0d190029900d03000c2c44000c080d01c410705407150320702c0c2c01004075445a0760300004444501e0440400050b4a06c2c8140d00300c0050150a201c01d406860b0100d01d4106290410b0001c1c0c00b291403645 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 159777230 1250 159775980 159775991
    0x9010c11010b011704080c0304080a0c051012091506060302090a0501021f0c03021218010b03060105030d0305150a0b031e011202040b010c0219080c09042109030222 72
    0x302800c0c0c45070400315500082c5421090000e20010302c0c0e40301e030010312402c1c1180c00c000305d404040f461070b0072580c04116280d01170020a01440350410000c07001e800b090303c800c1000c40e141c481c080c052100d401c240701191542c40401900b80b084241c11036071003810b092418400550340d500000c000c1e401c515122449054484c50003d050760000940d007001c100400c000030340c02c0803800ca1400051540c01c4250040c540c0030026000c02c007201440991084501c1c007c60014131818083d02821582c00f0300b901c44c0a5408540180b00503a400100800c0c0808a13207401300707441e42c40d07114001601041c00c1107150441000580815100d0919018512540c2c007141c19102c40d071001e0b54048480d40082c4038203102404100d070350a0160030f02c1d070000d00c0951018100700348010030690104405009550781c000307000e07422000c11300017420140400300103803104a5105070b0b582441d884c0c0010314030310702d283e41038804030030b06400b50f005000320300d03090003103030014003014240c04400e40545259200140c0c1e0200d8031b10b0301303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 159778480 1250 159777230 159777257
    0x51509090102130b0f04030501050103150b120c190506030f07110c0d020108042901051c020f010c050a060f0c09050d05070608100905130302011104030b070c021809010c 74
    0x14400d4668884504181c1180e59140c10844c0c1c8180d400741c80000d8a4280c100700100100300300340030351341c020f6101d4051620200303030344040d0740105c89070182081d202d9812403561100031003001560b6103516104a40d10b188802840d0000c10000c0b5095010700d40006000c41000b40c0b840240f050349120b02c400b610741c100c400c00704403003003a101d000410752154800105d090a8026522034611258054401c00da82c0e00e030703440180d142011502945915040a032803590043c00b0504108031229040300e118124064649901d6001032110085002914104084001d080050100400c15003401c150800380c1000300100b0704845070080c1c02204610004101d000310000342d0350074440c070a0000c02d41c122001d801e403a1f080070412203a06901401d11441e601c945040803ca4030102d01c682e5003c2c03803ca19620300c502c1a18a030113400d661000c1da040146107024003080003c02c25403500ea65101e0f03014680303103000308200e03c0041c198128081e0307402c2181c0d0f001c00030040e50010542c80b000a405003a241c0c0020036200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 159779730 1250 159778480 159778483
    0x102061b070f11030109060c031a01050319090f050705040617030a0807030608011a03060a090816020316080a0209010f062307051212220201050d0f05150909 69
    0xc500919010680c200301074004219807180301c4812610035150010b1201080d000607080d56540c0c1015035a103940c81c2c1200d42419014070030100f0030318140042e400b8110051002a14030300004010b01401c80d050040c182e4880a180d000c0c045642c0d00c0038408030062070b54188a5520412402030301c2c0074524003040410b007510003011402c046080240254601100700c00219801040a000202030607220b0724007003010f150038051604d065000c134500f40c1140c3c450400b0903140c01405041c4c2d51a082c580510080811330b0807084030300e02e505d6407600352110212440404c0c540110105509036041100b2804240d210000c10210580e40c002c0356042200d03601d40307000d4071000810348101000300300003400324070700c9560584c030309161f00d545071241a0801e04582c41d000d04040e01515015403004000559402032a00c07082e0b9241c003d0090450072101194100032041140503400f00a4140880481d4860030401d0b660051904100c02c003106000e54242032161015180300c0203c51441030a201c6d0000348048070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 159780980 1250 159779730 159779761
    0x1101020106050607030e15040b070c0f051c08090a0909031706060412080906030a060501080901060303170a0b0415090e0f06040b0712020406050d06080102071709040204080f0c010206 80
    0x40c120f92606034580e078142c0e42080380034038003a003080d001c0141c0b8040003a4200640f00502c0c0c0c07601c0c499030715002480c00d03040d45801030304038404ac0444401c0c14400e540b00d8044916103c40109a200b058901c14141071401d4010501403070390184076684049500121504181d025600c00e894540f1004040c14034500f00450481c1c0072a001002400308000e05002e400300701040a0140705103070300d0039805001040059208841918420351601c20401c45960300a59071603100c3d44000c02002201e041d907400030000d01034a001d0300c0b03074490311002107907005d1603c0d8030480d2540002002081408504141e28601480300e12030b443d0414608481801803e90100711458102910005441165100da4131400c00d03410103461041009024201c044490800d803000303102801140c0c4419880d0300d0780f03480100956025400116113640180110800a000400c005000301e401080760394a8180540c0418003d001c0c0d0391040f0302c588100345000400200100e60840307001404c0e42640e2140e502e00040084481 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 159782230 1250 159780980 159780989
    0xc0b130518060f270a021e03040b0a15080d180f050303120c07021804020f060a020c040905011808070c080303040f080903010209040606051309060b0d0b030102160804031101020106 79
    0x100300030140341c440e01d44481000701003183d5031803042c0c61130345510301d00490810498983e0340791680003405000c01810700c1d101a41c003503042c42c1001c1c61450103a50300c1e04140e00250210100c1c0761198140d106100300a051000500800c504440c0703448003460004201e9140d284039840584044240403c1c0d0f0851a4002025244064000c614003160b21240c2181018020540154644180842e8005985084501c400703001d08004c0307512581814010000e503c082c41c62402e00c603800801207545400c0d004030300a005d40c201100c00180c4c2c070003a81400c80c050440c2005080318104020452b004004203000980b41c0503002e06030001c0c041e43c488072500d07580d1102f640d000d050048a510b00d140000c0990000f018204000380015003003c03c00c070040ba0989150b40c0065010910100e2070703852100c0040c880100a204041041c803c061a150507a4800d2140da81c1484030349468505a10458409404603003c060104194003021070315070508014a8119010032901203540b0b24a40c0f060f5881405880c040c0c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 159783480 1250 159782230 159782239
    0x3030608160308070501110408030c0d0302180d020f1009060206150303040e1b1204020301150614090d171c05091b04090c0603240b04030303090c0b13051806 69
    0x2076080d030322012201d0300400c90449066403241141c005840320000500000c06040c4011034842400c80550b81c00c290941188508042c8140a441d800e24041086030ba68100c080d41ca50500b00d40600229030460780c0d100d03409030000300fa680c0066040d54044502021510140d02380c0302c4a4880e0f20300100300300c1d2000c020a034103038010302c418880005160354a90b0400c2c9000300407829080071003080441c030340085102c01c0c580841e150400c02981021701500501005271202a84298242440a400e0b0b2030210f0204e884214082421079050712600426110103400118001401c5225261003246522042d0742d040320321980c41d141e148008140c0038282c0115403541c0901135900c0c081c84049440c0d003481074002d5100d915040600049800055400080e00c0c40303a07000300c2c4c01154540703916000750310040290100c3c1c8078000104001070b0000151f4007501c1e42362a0101d42c3d10741d0350030243e40c9100f20341c10030f400001c0c0012301500302c1180c100e80d91045803402e071840c1010000e80310a0030304c40c0d02304540c0c07903412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 159784730 1250 159783480 159783523
    0x7080304060c0c200406120203150910050907060e0108071d0609130b0f1813020a0312080604110307020d0f020118060609050907051305090c1c03030608 67
    0x14040b9005094482d04600d401c0902d600c0740c1d29150b00c08003250340070810100c41e01c0941341950a00e40035601c09458000c0044103480c01c682c0c0070a564400340801403161920040c04903641c0c81e030600040002030886581400310b410689c54691716000c051240801107001013100d51003550040c0c045901c07640d0a6119441090f86d6480351069959102041a030b01c5078080040382d5440e50b40511b00c07205000c100d4400141c100c118001c0c819403900e1114210b1041000d695420103c00d103508029070300c00e500d02040100401a44041a0707034000a03000141003408070300e150b500c00c41d8440300442c0b10300e1301220300748800d0400071503c84552005440e01030050f0044003001101d140070306003058180d00203100004100301e00c11b01c0c3c0b024038561980c4c201d035090b8551500304480c00450244c260441500d40140000c41d03c0d082c00074102c0c07141890001c4c1c08a490b8800146020f0041c4410700002c03c02800c2c805800581d2104a0400700b149442100428500100400c09442c0000c09901e042241c2800348007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 159785980 1250 159784730 159784733
    0x3030106080402010e06040b0c07081207031d0406030503030f1614030403170114190f0614040806130506070c0b0703020d0e0703120807050a0e040f0209190f06020307080304 76
    0x203200c1c0300104140d051011800d21a40c80381c03243c500420041c101411084d464804187d981c0741030914582c0881360075403200910312254a08481100c005651604014145981c81c1e05001c0d82d05803011001740d40186412000414080003200461042d612070031203c034203176103440350f2000f0303441d0345007091000130008048500c4a80240008580113800b0703003000f000300080c909400401190982058243d90045090b0b0625410007000b00b5a02920742c201482d03000c0d0502c032400e070307410328148135100401421021000e02958002e0803a00070f404110300742d40c26407618101c40c083c06100c84808980c140300c1e00b400a20094422041804499807003480f001e41c54852030b10480c0a0b410421a4680a60703a41d881058115410000840294821440100d1001d000d10000e0990003004200303800340030301000602c9030030703900100d007221002040342c0001d490303212510341c0c0e1300a0150309040c80e040304100000b0100301070303004a44012500380f24403205105854a000305d88034040d4140080901c5020300102d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 159787230 1250 159785980 159785987
    0x3060504020301090204051f0504060b0a030b0d080a050301050109081f023006190602070317070204020304030e0906062106011809050103210f1103130b191103030106 73
    0x360840e00050012070715044940018003159000d49010084002c02500c0c80b8603220b02c1091000141070803902008070034a44400c0b007070b89219046101d0201070765041040c009944400c00f0154580d003050446407a290062005041980f00303004140c0441d03810307003000952010005c0c5080040054181c0c0da0b00411102c000000650842844010441c6040c0b260602c1c1010414030380e1005c00070405482c01c1c1d42080e4041c0613203400c000f06c10103001e5440450034001c0d190000385400c11207034441c548003003054100400f804140204000207510034000002c0c44145039104054541d240740846110107643c481c201008098800d650300550781e44142304d19180d010a1300d0344001da0204c030605103520403c403108000110648a504031010003076450005209101f400c1c18407003610000c82801c900c040348040e001500004089880030100310030b40000104403001401900c0000044032404c0b25050303112200b290168101c00c10810340301c00480080310301c40744074181d00c082d0400014040c61543c0d00b0584103c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 159788480 1250 159787230 159787241
    0x1605030405010806041116170a02030403060b0a03030c0f0f080a0305040309050102010513030503090f0601060507050c0f0604150e03030d06170114010b0a03020f030705070515100b0a1202310f0306 86
    0x5560f208801024581c180c652407000b82080106a0b02440d3343d241503252031811510340c00c40c11030007801190b03070038400a030301b0003007504440e030300032406410241d00d5250030032409107907030002010307501f021030300011581c0c058100a0060b44079842e10700301551601d0049080381d1088540010401c0c0c100000e50219000c0c00041d03405c032140c1c1d0140d0300400e048002503458007200380e01c8040040d40c002a24428001c00f48415044130340100d0721003107446100400903c29025900030104200c043c22400d80840c0d014007180c0b0003c100140542e40c40702c80743c9822200030171161048224940703000400e604800010303ca0130000100c105541d00003a4244070240019420403006d20703080c180e0030420202d507150010040e500c982c48503660740740d03201000d241544c10302e0312589940d0001d140000500a00480745840301003030303070354048419491f6a40d50100f1103800c030001d81d404200724400506042014050078110303041c4c044030340700500103002c0f8107000121111a4454114820001401400001e5264021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 159789730 1250 159788480 159788483
    0xb07050d0902180103020901270b0103020910080a0e0309060708130f12020a090504200f0603010906030c080a032111120103120f020a06111605030405010806041116 72
    0x400c0c440c903901145242152003000e83c100b0120000410852400040716409458200003410070182d4086103010f50081d000103401c055030311f076803c81003641d111707074180e07624070400410510b1207890164000d01210b509555003000d0500f00b812041c1e0f81c12002040b90340142018007024941080b5440d422410b420003286503410780e24403000000d00d101ca14914101910940449404442040c03041004201c016840003055609000c00c11021035810a19060034403401034030305c0c0d05c0b0010385000a0450103c1400c0d01d500440100c00460401142ea0062040d28450004141516101c0520f103aa5914403440240001e0440c59032805890440042541072440c110000c18010482c0801c1032440d005054100c0800e400003004000b480302000e100c0c40800302d03d04002e14082c0e140c660094441d00d09050191100361644010903840b60b058041304c41d80e4480c0320940e000c1d0700592600c82c0d02c131303801840382da07002030f15003004140303d0b1920b031084c00c2c0035015850145152809031480401841d5105a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 159790980 1250 159789730 159789757
    0xb030402010302120106080717060f0d0213020403030203030a05060409020a060c0305040f1e0b030118020c0c120601081c05180307360b09040b0a0207080a030501080d03090b0705 78
    0xc44c0c54280c0c81440c094040d00c615101d0340914940010000c051817049000c141c8040c00d0901400103070303256898045007510054800c08540709070340c000300f030a10003c1484540f85038400038001003072542c080301035401541803110030f104075241c440400090301c00c1c102001c0c4d0b104000700c4040241e103004071605010301d4801d007449800e00703941d003114440e002503980c0120039050104402820104c520200340010b003110030b201c54119410710034151001146020301002c1181d0015090004940800c0901140f00340206450f140c0c041d0141c03041c0d100c41013031180070094802c18051590354280a411480c106206030f0f550ba007407a07001080184810f0302e460b4038a426000b1a080800c405c0d1311030218500d812440020305241c10700c445404541107003030304108901a443c2c0b64207403c4039950b0207800e5801030703002141005180c0394014054000e1080c034100400ca8680001d250203901e8041c2c109a0407a40c101040e01c600904100c016001c1e10f56408006000701c10780d2000a243c41e005078068001500d4810 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 159792230 1250 159790980 159790987
    0x2062404090f060c030507080c070501110a110607080103050d030b01110f0d020f160302010e0a09050901090b01051906030c0203210a0b1203091003141005090606130b030402010302 79
    0x20041011129110025224288a1562201400101d01440b201120030b440c0c100f240e450211002002c403a40034200c1d071766004e8001081e0f02807140035008240340030703482a1019995407210700c0c058036009407042d01c4a00c80c0a800c0024085901030803965040f82d403c200580058082004114020601d503400d04d414001030000c00348251000b0008500d80490344001803004410a903400f03072500700381c01800c526941c0a165420858040b1440c0c1104680c4d080c20481c03d031086140014000003c0c030303000500440d01c1c00041061702601500103410341801408074044e10f98841003030040440d810301300c80501c0000801c0030000c5502c65803224104020510550703050080b4490079074180d80661000c2e1050030718135424405050b0052260040d40881204c102c0401e2201040d07241e100e004a06a1600ca5030240c0074208080f0300940000038501ca08807405003180c07070203541c25440314400b4011070380134001c1800080c586d410300801301c0302410000c0039001446032a1203850a070a60008000b02c0c101502403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 159793480 1250 159792230 159792301
    0x30b030307031d120105090c0a05040b010e10021e16120308040b09030405040c02030d051003030f0e011202070b1006090506040e040807051c0f08041104020a020111031006031401060206 81
    0xa1145600810147c0054022480c14104018004174035400075441303649442e03041c01ca41d03a04203203014004281074603c1d5081203000503082c1c0c28030390b11201c02100400c0c600e000c00316290022a40140030324541d480c1e13040c0503807140004482034802500c01004500101c002c14003080f058403015034444607030002c40c0c1c03500780c1701e60205041d20403402c84180564030101d201241496035000305503001c401030407030004d9a451510000c08102ea841c10300000d00104070304540d09039100764104043c00307010900966a0f25034918005400c10021918104986842c0401043c842c1c0f1a801410031944003e01d0181480e0402d00102d18075040907004542e00003040001c43e001950038041d8038148188407400b0704081c014000003400c6000c5400c007030400c1240c104104000102d10a41003080988261001030302c0d8009076030300764010800040d800c824050f010040104103c0403030740d04802d81c2c550b590280418581c501171503080c0882070181c4400b603000800001c03800c3c026041946600e91030701c401800400d00340f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 159794730 1250 159793480 159793483
    0x90307090609061701020a1b0311070308070b0f10060f0c1a0615070308010303031d10020405030709090804060302030c040306092f1e03011515030b030307031d12 71
    0x303950092620b103454030300411107002c001c2c1c0b900e0004032441d80254604041500001c0c407030800103030000d41c400704903848603003818071451200d590120000d04445940c0c0d124181070013a504690b004488014020000601510484907114003a280480340100401d0070001e0035a988180c01d000f602c104202c1c00c00c80c001242079503038000003140c12210303042c1f04c90500c00240804907007200c1c10001840020420100002d600c4030f2154112505454001000340ca5004094135180c00e00306c0542039841351003200c58021205500501c00c40d03800b141100c0c862559450b02509984d245440548040400d01040040034080d4008541c003075040c2440c03a00d400d45075a070b004202e8500e81e10940c1c8800038800c01030100400062040205680000c07115440c900c0403000480b0802450788408054040859407480d9442c250090b01d10314021402e03100403141c4405c1c032416040040300800001a0130110b03a42030904021040b43c168981550f6a041c0c1000746a90709001001441250b42e001040031840c9548000d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 159795980 1250 159794730 159794741
    0xe0111101109030622081804050a0b0f032b0e1005070501060506040305060711010209060c0606030c040203100e040314030403030902010e1c1103070e010f081002030609010b09030709 80
    0x10341c0c0007a00d842c0c80b6004241441e00030010080c02c10006003014409a061200d11601075896210903070075520301040011601160030610529000b600b400c080c00b80000c0240c100d01d020f44416a007040da01c039000b10825503140da04e022404905441c0b982c40c400000000a8091164600d17401c0000d0008506004118030040c0b1000c450000b481c0458200100f00c003c0c024213004120840b8a18207003811030700d4003034484c6030107002802032102c0720400300d420300c400b9010b40d084804018000c54849444c4404541c440400b1102c00e4841e000d20f0b182030740f062520384280c90088070855500c11845003826030041c18007102a0041d02401400000c0d07a40624103100214402c030310a03038020800e03801c90710014002d00741301d4901c10712804080400d540d0105413281c903101030031b0f0410380b1807054911820100f800c1aa540c0c01003a8004854400410a078084958007000c546140080f5801d83c070100c120602240000e031125948100c4100040005000c2d00000d0007082d20010241c558055450348040110380 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 159797230 1250 159795980 159796001
    0x7110409080703021606050702060d020310090e0d17090d0c110303070614100605030a020f1606020c0f0705031b010210050718060801050f150d0e060411030d0e011110 73
    0x20703c074646440c1c002100a0441001b041384d814000d0403e0019800545180a03844298488ae9408000921025a902510001014004010041c860300d821500d41c480d0132918a00c0041001410740c0b01505440e001081c0c85205400702904401d43c12601c1221012119070040c0c8201c1114420140c455409200401c03059108110000743c1b40e90220312064031540043c002408a400b6540800880da040b4040f25448401d420300140c1e60104e034880c101c0340d0b02548081840003010004000308121095005060b040450811100d5101c40d4010b1550307120483d02505803d604040b40d0f98151000b8140201180c031014016a18000d20030707080d41c0221a0201e035540e001541d0144020704e0480190349540281c0158a01038043d58100300109442c0d040103010719000b00c410400c3c0490040c402001c0c0d80f08981c482c901400440102c49a4596524003605c0035206000d0b844400720300352400042d40002e107552502c0300c1c1c4103030b00208015140411403d809003000d010340100880107040500c201103507007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 159798480 1250 159797230 159797233
    0xf060102071d0f07020303060a030602130906030c050f1219021203070f03080c0705060c16020a060c032c0d110301060308070605010b040b0412030c06050a021801020606060711040908070302 83
    0x240343c01804030040100252440066410400500290b51100750441b800e40b074205c0350240e0fa81021a020003a4060035a0104844620b05200401000101c98002044a100b1955201c0740041d15040142c2070303642004074100da03804200c40c0061805000d00b10548280000c081c511031403403450140e401c44c2c0c403040341198182802c0850340e04240e004042e00350040c0504050324182489941c81551300c2c1d8000d030104903408004109400c0302420002e80c20011a4040c1402c8001c50b0340c0d10000e45518a100c400310f000c1000364100c012070040890f00703140020040403034515110301010030b001e000c6284182c2510b0100d0b0340811503015480074081c240046104040a558952650901004136801a04000c0710301c1403c00080100c0f041920685040d9684003040303003980d800341c2c0303010384100380311b5400288401d090004002500e101507024040f0f4142c0c000b4124504e0716498012600c071101194025484002030062901013a054054120340605c0584001000d18be039031100a100d8001071f000300c005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 159799730 1250 159798480 159798539
    0x5010902030d03050907050409050a12090e0115140a0e03071203030b060c0601053703061a01020d0c020307090504050d0210050c12070302091f0905180f06010207 71
    0x441c1800c1140c09007140342031604204500b00800400d0321000b240c85a42e20898880c951402884414400d841d8402c1d80461105011050300c000130b0540080b5108410704034121400008480101c0e42d0041c10075800f65a40000040034480e0112140d04446003505c01c000442c80d4103e01624100701c01c0f03002d00f01950758984042d52600d0020195580e2990490040c0380a0041c0a4000c10000700f041c19160b0446006102950602c0c0140b0580685140075a081e800c80101e89403424880040c80103070380c0a19010b02184142004481e16220840400341c01070380310700011008180304034004180d40b80700070300303480c0120354620705401554015681540c0b00d40100c520403a0554040200c2c00150450007428001d615041119001900401244401c200d100000244115120b0f40c111407650000405003004013212034a0560408600f80300080810026080480e607841c0c208070200000e025142030014aa03203c1c4503203025840090b01240c158401c3c1c02c00400c0d10342a0840700c2030080d1540200c00340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 159800980 1250 159799730 159799733
    0x9100c030608010b040e0304050909240114010f02101808070602090f0a150302030402040e06070c02040f06210809090403080f070f0e010e01020c060403050a0b0c0f07060b04021303050109 82
    0x1c45016601c0d1170f104038500b04021070812004025a02190411110b640d40c03552602040f5040048003445800d10095051042030b124006040082c181d8001408000e03901380800015911300403009181ca015a0055000e04203000e5183c010005015010b04c4052680210f60303140d000c80d4103e0142154a0740d0042a20501c40c1882c10351a0703141c2008641e44d113001480d10500602e859099410f038401c01d41c0000c0040c09544441c0c0080c800303036132100101c880030710300304000a282190405049204600300403801c1020107140c010070040e03ca40c040d8610041080d104081d4070000a910308a500ca181407003800f529540c1c049459201e14000d84849015240111a847d0070302d070010603560034010381d8010180c2440c1e00c4509455008400e0070245200390110006030f251918a260840c2d01c8a4009004003c1001c04034280416901c03032a10b81c2190b4641503c484054096000c810429207028058803012810315080b60f4000303000508018074005800c048085401c0880d0401c0c0c903207070b440c3d40d103800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 159802230 1250 159800980 159800983
    0x32e03030215090304150e300c060c07050d21050a0f020303100608090111030c070506130506070c110a0306020a020606090103030e0d02030309030102070303090203250e09100c030608 80
    0xe50094100e40034501c2c081c100a07292081900314900c0404000040b00318502c0da4566040300e13014023484129210341200701c2c180450404a81c440703c522107003d03c41c1414400c3c18401c050321065110600a800d00d2070a1209218401c24440420f560003076001c818018244034070306180300c8585003035448541c0c94054200250110700f2003043e020031540100100a6002c10b00300c014411348080b4a000015911005840e6014000d0600d40c0f0580e2080001030000d488440801400001c0c410800e65520755074111604810180411014049402070000076000920ae80500c540542c400c030a0102e80001e510080341000601d508215041907000a503451001d40410807240d1068040345e0000c5690304540d002409a654802114081c1c5140c0c541c010465070107000351558018090001c5484120310f06000700a00440740050380280164420380c444540d40060300701291003c80710503d151443e003042d1084d000c4004001041d24000c0040000f41c02a05d809116896801c0d0782e00481c2c11030800c1daa03079 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 159803480 1250 159802230 159802273
    0x20d0c09060801180f0209090c04060905030303010b0306010305180a05070e16020d050a0908151506031b0703030b121f0204050307030b06040603080d02030a0f050606032e030302 78
    0x5818031a60300010000c8904d803504a6901100030b90021032829640050400640910700a07264092504410802201f075903002510880d40c0c00e03910804100d54400615132603210070300480d40034520400c00203c65500076045103400c04852200c04c041c1c1800f84c0701160a105000100300c035507070030411042084199a00409401a4450242c1074010030f80820281d0b80d1089150010203019010440071540c5004809900042c52198143c40703001c0c3c0010740301e400441d0300302c4070800701d0464801441c0701e50030a0340c1500e10a40074064858000c0000580103106e03504001c07400c40416450301c0101c0f00948951703840d410216041c00080c69aa1440121090003001004103c600944103010800a03035400003403240c1140c0d0080e46001c07043d11034001040c00340186e5003004e01604000a904450183d65070300031446902990400c20919071a0900f80b826194156042c1d60710800c02d2021515404075242000b1025049035640003403080c1049480b04102d21952058002d130700807103224800c0c0000c0c42c601 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 159804730 1250 159803480 159803489
    0x5030708040302100f08040201082706160309020a06030e030d0c08040b0106030b0d08030907150c0b070c0f1509020306100906050a03020a06051606060e0a0f050c0a0e0f04020d0c09 79
    0x4170340a600c0d108401800724000030701c00b90411600c100810410456015240c014070f40b07204a40c428220703150015a56442c0c00d4030b03001c07841081034070325171a018400d03c58040081e500031329640f112450b00c44210054404020344481e01d01042082001030b04040c4641c5040441c140c4900d9214076050a248600c0c2105030310000c2414100b05a41411744e48024509070602c0e0301c0250356807a0380350f17580100e150440940065482c8200108400390940c2c0018031800d01d03900c10103600305150f44100085800815210005003410100007440c40080d0054001c041c2c03841c07414000142c1c000083d00001e184ca0000e540b0b610254642e4041800041c00d44d009810180006031441c2d851070b0b01c0c681c00710b0204201c0c1d10031007042101c08660008801109400c5403400c1c2d4220006225868883c115040414003c1d680802010b2402c000c0003110300c55402260f10400002030101c0c1445100c000903aa00c40c41030850030b40c400e8014813040060b6031244068803500280310000106d00b041c00c1009810a040340c1c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 159805980 1250 159804730 159804737
    0x2010314040506060d030504030501240f060906050901030b0a030b06030c0f0603070507020307320103150902030702071701050f09060f070c020f0d030e01020c0f011e05070503070804030210 83
    0x8010102c2c0300000c6480d00304400f610300f11400320303030b42c10704aa140c0a181c0005016500b07224440000000780700251114848034400d9151903652243c041e12094024414600400da011008002450080c4082c001c0f507081814081003c0d0308020000d00361090780d40080b1440d5a4440a214040c2010010340040380020783c0c55200d010034103030015816001c018120000c0040000e81c020441d03d0a200320f0f401407802c40c2069003828003100710211410350250101c107500c4840c04041100b507119000355121900c0c642c0c8120101e9040002c800c01a41c401000742007580b048410010341c40c510345203e9107448410500024103410300c0081c021405e0f101a0005a071a4842d109002c421141081140d8105600b418200145051407010910001e10f0784001a807040c00c001480081c550001e01c0300c44000400d034260b500c50f05141081145031410844602c1c00104640d0144004010f407001c0da0900c030280e1f0900500301807042d640c180c0345070f021250440b100c0201142c2002181842c00076919142e90905 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 159807230 1250 159805980 159806021
    0x2809060c0807050118060506030d0914040f0e0f0a05010b0103020708120a09080705030307090f080a030503061212040e060a051302090f1002070303080a020309071505090418020103 79
    0x1006000282103400501052400900041041001d520440311600040d81740b501c90f62190818030000e000496444c2c0c0a40070700030701009080c0c4107002060681d864644070342507118000047c0001003441e00c6022141e00da80f55201820a8420085015800551401002c0d2660503280c280d09450900700c0060526004ac082d56000652900c20750705e10300750303410300400559240c550300e8000e0308030150301410603400002c01806000001c40158030805040e02c40f1030005684001c0b00c02101103130710902940e0781020040e03200081c407400c001d54125900605101c43ca1124000890030f007032a04a4075808248001410020080d0794561690312410840c1c584005901d0240802d104600d02c4954080309a400192241d0740c0d43c0303661603142c0405c8042c04004031081d1409000e540c2c0e0003a0701094000c14000070015022500720f000300c1e8407501031040904925803404403803120f0740300004904000d20401348003650b601d48851240b0303440c420142103078110f4910280000b40440e002d84020910b5058540c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 159808480 1250 159807230 159807239
    0x30309200414010b0a140904020a120506010906020c01050702031e0601081e120d150311030118020a0302150c15070f020a0201021203070903020d05010207050c010804030e0607080403082809 83
    0xd80941e05e68101d103043c098100c5203130640c0340311284542c3c080103034000e201007003244109030b001c00c80c01071f404c210700c4007004103444960056a81d50301034490200140d0205400e00e019500c144c0261826920107003c4940c00c4040d592000000010310441c8202540700c03000401a017002009044540c559020701b081400403441045504c0f6401c200e900300448600282585100d07406038803090041110180038490640c50745020b16002041c0c2d0302c01c42c401c0d82820f40b11410a40c100c14121141039000b0314030b60415240d43d007803203028198440b0b80306228406006a0125070018842052142601c9101e510246852400984030210800c0e5000456002d10303644030060b41c00151141c280d001303081c0031984903645c40c08215100c070220741009400c041007581d250100719054000d08140c600c40e20542c1d02c5192000c00454861500701c601400181d10000030203641e051060007041c5844c0140300c4103181c1500e94031166002e90140d042880b03106407503e140c000c01c004d0922005944c0606180071408503140c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 159809730 1250 159808480 159808499
    0x6010e07050702010f0905130906231503010207050a0302010e0115120308090118141b0d1106090a1202090f0108071403010b1225030c1203030920041401 67
    0x4a0400074144005c0f100d1404889020345401c800a0000800141441c85200b03900d5010b480e0140040311002e0503c0704280131003c94a4419a100c40050780c00d01e03007a5103c1e200c070102c0000505049030155820001c100110b03200f40301c40b9480f10b001e5000071840481d0b0013070300e6007101c1d8402c04013656183c0641040c400c65448403003042d20f003030300b6150007040e5460780f070505401818100301069141c40020005010003116240c0c4407809000c2000b980d22041031080b050500b5186940c41c83d910141401c080310004440707096141070084040d09060030314400002040407d9280d0b0080000d80c171441451104625005035000e60146001c00c0218140d450038444a54404060140c02c1c210f49600140c4126501c0950210394007117402440c3c070306101e0018002946984c040030020000314090b610a02d1529006000c0e4022a640708040703d40091800d092400312007980c0300210f0815403100e0502010500d41d8200c0c42c00e130320f07903020640d180e144401d0410041fa8603c2030f5104010144c000104280c090 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 159810980 1250 159809730 159809737
    0xb010509012601081608160e070903020d060e010e0a0c050d11030109030801050307090b01050a081801090305090310050f06120f010f0501050117090a1113020301090e06010e0705 78
    0x40c01e0074050900414a9101c1c0070000b00c002d60300c014007040d50000541020000b4011030400c07000c4a131000e40350303200c1c80016110001c284402c0304000e6954010001e00c01c1000304103a01584d14074007454240c0c1c80381e0008080d0781e4180d10039180b8607180c0b408101855000c1c461100c0503450100204408030050351040049282403251610500c010b01d180001d003e0f0310311440180d07820003002005807506034030b00070b000d1000a000f01406803140359408660324615114841c05840161a440c1c100380144008503816640103000c2c0740081880401180b6856090040d0402248a5260940c40d101058107162601042c008000b10b61402d200c14842055885000c49421050507140104130744000d090f80d81c85d0440f03c618400703840d8606412500802c0e1300d0760105050b034800341c1e40c2000c800e24000403072003e104d040d6890740750342d04400e204400203400020107140f4004044c0c1241240c0441c084210203d810076030200020540b112054000b0001c10300c0841d02505910402a600f4203001900802502 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 159812230 1250 159810980 159810997
    0x70b03130c121104050703110c0106060e0303031b09060903030d050a111303060c050c0f06070f050f0d0509010612051608030a021b04021e090a080d0c031b060c0507050705040b0105 79
    0x41d85d0300701262000748207400038034405084424a07941c0d0308484c00618002c104c00e108100016910450366400c43c540882100e01034405508481101020801c1d40c0805510030400503601070406c12020005480c180040c004044400c5000191443c040c8610300655211420000700440200442e40e021001400320500382da03085040000c02000d801c90130740301881251105081807260050701c80c151800041c3e10317071041d0300d1590f0300c2001d140346e035900340d038140500504250410030500c030385000d11405602240c1d0103804940041181940c8101c000710324490300710255800d801c40d4100305203183c4c8034260080189940e80086140c005043d80c02900e541c1c52509041c0741c1088440c00080710b40c2c580c0c041da08030b94500c10415403814418050100f45d036000c4080c190040d1019900021000c1c00401d58a814146a84a50150000d20303a000c44140d4032140149580701c01000d00300c80404d401d4414207610030b201d07448a40c0d0f01c07087e50034403524059080d8092803155003040c00c000e100313903844401d0f01c5441 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 159813480 1250 159812230 159812239
    0xf100602030c07093b0c0102010c0e040507141b1219051b100f05070201050105100e011707030605180601050702210604060209040f05091e070b03130c1211 68
    0x10310264040c092488030350900d801a403900c40349110203a4045d02c1145508060854120803912001a0b098800d084890300200758100f20102150415410540d40841c02c3c1c54081e04404440c5800d40168100c065480409002c800c00f245502400b0015035111550407600141018110900d405207800308040a00401c0f03408220f041017441c0b01c01c101c15242c8681000d960b4080c50703040ea018010410b444400d20501c0c20705010070701c3d850041c0f00c0c81d4140d84014141c3c8525503034104040d41c107680f081c614541045100080110154072340301c000fa01503915a9800314010385404100050041131800c005442240481400101e1313070000c0407110300f180d051b1601120703040b4507a41152102d18159040c400b5018031010801000815402001556411507040000845104002003120300c200c9031403103294008501c41d410082440982d8600e0708002040320341c41500d0741b0b0740118a8200b918040c11080f202e00c862410000003181900141510720400681003009860314007407940c3c94414580035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 159814730 1250 159813480 159813491
    0x8060c030406110f0711210a08090315010314060f1608060a0308031e0c0403021c06150f031712130c0902310501050d0203100e0f100602030c0709 64
    0x10380c6525090381d2185203c08a04c40e2a1902c80c01d00265150210300b4292160100704940382902c4202901d480306243d8500c024105500d4595442d00d041c0c0c00080f100380c1c14030130001d01c0c4001c46c1c181103815020b035101307440c200d003101700d2450f060f0710f0a40c0c081c140c0f14084d8520020000840f5540c0c001c20500069481c08444a0301c40701c002c218115407641020304545000000c0043d00342c503921007000c01e01d4040802120981d503d19210900d0f008600009512502c00c1200c24403c2601d0006000c049020300400a611740c111011483e03800c1e0300d941300c10345000910000b0010320080000305665101203a0340b1901d0041c00680c44a01d015004195038003401103800744005004d003c40c0c10350082c0090a4013150740da040c40030380092401c0340f502e20910316010300312204507411b03903040020129601a1141c0381047c42d449986006504020b1600c14650074554000503080e82841c12180114001400e191aa003020343c1200b0400340a50807003c19503100f0000401002030006070301c411205440750000301e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 159815980 1250 159814730 159814751
    0xb040c0f0f0f320a09020a0e151602040209040f0507080403030e0303130f2301060f0803040305030708030408070c0b032703030105130b120102121003200d06141008060c030406 77
    0x8004d1619080080c1c614404a12800d48680100b41a000d1810403215902d10040f02446c01d40c080c07160000103540d82100d0300e0008018140758014140d1064001c10100d10b00c3d11145c50141107030400c40700900040c0c400e03010b00052682611403015200c410b8805545140b41503400c0810101c0700e80401014180c800800c90180240070103500d485000340300002001402c401c64260107004c49008942d21111071240004201d0b40003c00c9031308882e4000c0142d400c0c07500c5034580c40380756040288182c880c40000c0001c20000345c038001d580310240101120f10b580368101071407003081e10b210000d12280c1700190b513082d0030100040001074a0442d20100c4e00310040280d4488450040c0c06501e440c0c079004600d184000b0075189041d0040d110b49401c0340c924180070b6641021008109800c3c0c031001e0015031903a03141c0d911141041c05500c94002014016600d11a805e41da401c2c102c03601040c03000045030601080c003d084010103a80710003016144002c01e03150901d88003200c3d4501c009000200581d0f0b4414080c035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 159817230 1250 159815980 159815989
    0xb0f010503091603121404082d07081b040c08011701020c19060c0512010515040b13030215040b18010c02060c0a03030501060305040f0b040c0f0f0f32 66
    0x72403580f0412034960659924030300841c08090050190340031645078120596584070210175202219140c02c018481003103440301014800c43d01904071803003600924081e040b0f041040120744e00400d4800020008500186407406030041c3e0b0450407407145050000351909154030001c0d81e8151100c0d40c5050500c000c11000f010700a00c1061800800ba0107074001680c4c101164980091845006035070034131103240d080e2012510341c410008080d038910f040200611103403c00101c0c111081d0303405030205151948810300c0d40300b2508500c440f0790150340018070034411030800b00b0400401c0ca0b003206030390b030400d4106101000b0900601a1000040d58459141724030341e8425904138140300c0d006400c444c0e82c0d48940c0601da0315142c4445054020a08160002444034442d106141c0700701c1d006012010074034081d40c0d503494126009041030b114900c03c100042904c0c000c07444400d0003010243c440014043c0f901e038840c2d0789000316501c80c4200001b00038110f24002e0141400d0040c0c5c80c000100304480342413400005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 159818480 1250 159817230 159817243
    0x130b060c07030803061e100827030306040b0402130501030f060f03080a0906020c090606071104060b0706050c04060512040309180203010303030e0a151503050a080310090b0f01050309 80
    0x3511489801c03030000910020f480214010346040e60342040c0d0010400110429841e45480c864200c00480e41082e2403910aa038520b8100e500d90500044260140a01c107000500c43c00d032801e03440e000001841030f54030b0036100b003000c20391007941c06504100856190b51000c18803841201e0615864800001048c1c40307540c040303070103844030400682c1065160308002c0c555401680741074006c52500c540c04540c0c1800040d1001c80042c0c001c3c590f084580d038642c1485070940005e0011a520b0085185804460740d5501440019008520070350b500ca1100d030030004103948020b42404d201034004c00080c060380380d01400b00c445030120701c41c280c1160b85903440d08651012507075101072100d02c464040500784030080c0d00114104c03406036505118280d00d10510300e80f1115481c0005102190340c98018200c08515000300182032030320507007200e48907541e40f03d041c103001d00080b0840e000300c0004100410035032040100400b0707104c02c2c001000f00069501c0030500c0c0150503034445051010220010f1040754003003004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 159819730 1250 159818480 159818497
    0x105070203030706060611060402131109030604210801050f0f1804030c210804060b010c0203100f0c05040f14131811010c0305160c051f0e0a05130b06 66
    0x80b02e540740030350705015004212600584c00007034941041d104044800168690090780c0051102019109802c1141c1c020305181f464280c02010910140b80e441d0380c1481203074803c0d400b42a02e0080c2c0c050700703950300101c0f28958805a003400141c3e801441141c0302c04d00443c140010a40b00340388500c00031000554010b400095600210b100c000400c4100755115401001c000e219008041204110b1481d64000011031039520000401000001d008542950400c4840c0007040c14070440090a680209003066003060b040382c101c503141c0c04001452001842080754020b050b180007802c0c0b5050580700c1002c070150348111581d10f01021014805552604261403031011801c10401200c900c090316141400172144d003c0d520309100b000b8101c2c1c594050103d05064075499581d0314942146403140d100e45006d04401075482c8039420002046039121078000f0000c910001c4480201030b50049002407401c500c508106e40a1003040c00100000e0300c518030b40e100032050903c2d000c540400c12704040340c10360250400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 159820980 1250 159819730 159819733
    0x11030c0402130b1614030c010b0103050405060402090c0f0c01051008150406020706060f08010c021506180a0b1507060e0a020d0303050703110a090503070f0b0a0f110601060809060a0c09050f0105070203 88
    0x4a2165601c4c00002407020301c012030000d109c0c4c284841300641c1101d40842c3c0142c460342210001400610380240c240703512a550013265818448516910891031300b001c240300d80d55a40d590288640340b61181405d1004001b10001460014000302c040c03203d1100241c4000e00300d82d00840e0396000c118541d084003002e02103450419004568a0070114080c18081c0d01c0b003000360190968200b81f081c1102403007442000040c150540036504800c0100349000e00800341094940e03138000e000e00ca03944200c006540c2110700781c9116103800c0a4100841110320b5000c0006075507003d41e0710b00d80161a0301c0d0750544c050b6018240050140d54500003940501440c854103030011b000054a142d07a21340090300d40042e51800d0b01110281c03501c808011403c01d13858060350407580000c8c08022000e61081810400300b00551606440101401030740f41d107014403c0e080b000201d80d429042250241c0c00b004402c1d4405944801400100303401c45d8080d04c000614090103000d0224241c012001c0e90184c4100c82c0c40310703405070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 159822230 1250 159820980 159821003
    0x81c05040803070305100e060f03120301090905060109091101050d0912020f1009020303090603070c0602040902040e090c01200f10020c1c050d150e0411030c0402130b16 74
    0x1c0c00021a5004840300c801080c50300c804204100300d40020a8280d9889406070810b0b500c841003008110007204540540c5803090072143c00c0d420103118083c50082001d00004540c2040c6031a11b2814104142c022001e21880d242000011030b040b042c04840c07510742030824940c0c8880e414035090140c9907000000d400d45912608090802d6030014000f03168184c1c0e001900c9406240054580075142c4401010354180c1c02406072241e98034090b4000c581091840c1025042c07001a0b030b4401040c3e0300613a015100d030580c0402c0401c203021035040e01039070200b140000381180e0903001002914043c440c55405110b009a00040180f40380c081101900300d0700020300303e0b2118042d486028001c2d5200c25501d891a026002100c1c0303500b400000c840710340d0840d9454144c140440e0750305000042211655800049510041c0011186428103809000300c0c01040c41c0b02d91107001e44240745c6012600b54102e4001d07407040124620300014400404180e039800031000359540c0903ca400000e243c44924094640702e0072030f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 159823480 1250 159822230 159822233
    0x50306090d0e030a0302120a021504080721050d090215130503120306011d041116020414150d02211501090606141303050118021503010303020307081c0504 68
    0x1c904000c4200c1c0d555903807581c2c09840900d03480300c843e4600240940d100010501800006101070308100e4900d00c100c030780c5d41644800595000206a0b001e07151500d0004010007801400544080076817140403500c29440f0491000810500c03480c010a00b440b0380c2c4100190440d607a04000b82c0246d40c0000740c250311404864010303506000d20b071080d00c5c428401c80300402c001e01c0000007070343d200d00d4058403650100803c0440e51807500300c090001c10b60040c0e503200700c42d0388858030703d018028101407030f444494101c9003481071004070303a15000b822082c00c141004110000b0391819885501d80c2081d01c40c1c5401181034408140c001e80100c00e848040380c00700e00e00101d09100041ca4619159140582004603603032601c071142124158060000020340c085c00c00031412104a000b050341c9440d1405810440e6034030b8840a003110019040c050390302c1840c20081c000d510700b14843c40f20710b0341b2100202d0301d1945140c0e03001c2e69034458070300020010301001c5204117480004850f043c8010f20405414415442e06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 159824730 1250 159823480 159823483
    0xd0c11070b130e06060322080703110607030b030c010e0105040905010902070312110304030c150e070f06050c150c0412030203030a1d0a0b060301110d1a010206072705030609 76
    0xc200001e06042c4520000f4448000844030b81c054a80035007040d2075503d5003503141c24500d5071341c64850151072542c1c400c81d001540d0100180b0116000b55640040d9040401c141c42c00e00d00c000c1d10700340406040860101082c1d5022401d08091402420000c000201001c01038400d0300955215005a03403500d0000544c02c4866001440c0396071080d5515680320329841d00c00c5046408046580740360365070500010300040e01071076401142c1070280c40d034011107001c043c0e001c2040d075441f002c03a5a840d401c030440c200140802010014090700d0103081c281d0a00100050a0f540c5c2c2440c1d07443c3e00300308000d000104800340e00c00422100680950000200c10390414100a981c80c0c0c02520040c01c0545400844010942031207140785094442001620000c1841c0e1614501c0040140480c0e606540c1c48a03a5402c20400034001c150b9050000008560500e501e501c1c1600703c10620104c2e41550804410000f03055400109803407000f054a20031f10307200c1403040095052180300c5d0040743d0184900c0062010241c030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 159825980 1250 159824730 159824737
    0xe01020c010b01020a0818041418011d03030a0c05070c0e0105010f0e09060f1207030b06030c010801061707020c060a031e11121306050c0a0801060e060d0c11070b 71
    0x340030000d0000031070b020300480e5261001e00001e0200b820620002201d17082103452240282c00003440800e04004890b07c414400c40140c5030a1902100100c0c1d000d4546428020090107182d0740c2003894844c0000992603443e44002800c50701295a64000740000034010703403d48500f650003100c211550f07500e07100c1014030680700b80100390225003001541f1240300c0c031032071110540b8003010f00300202c0c90302c0784030074030149555400149074010208503040a050008102c10001580070700c034074811905041c400e00d420081c40e04940c60401011600500250b40c010140640305070304043c15408640d0743c0042203040c42c403500743ca03980c810000249a40d0241d81600250742e071403c0700c0003d41c00ca9001880c03560481c0e0300c00081d480c2c01c04c4180820f1060951102c41e080c0d000321408032009074103000e50713200021158112280500c2c210041140616190f004400300d01405140c0be10b00d60000a40000a8160040c001000d0006891b250119491440b4008c030a04040002d011100e48940300c480340741c290f80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 159827230 1250 159825980 159825997
    0x3030c040f09060b0706091a09010b04060b03040206030106080403090801021801020f0703020102100903050408010e0f0d0203030f0415021908090c030102030412031104170604020913050705010f020f010e0102 91
    0x9070708101156010740e62007440e00311a02e02d000c03070b0700d02503a5030345800151400342016a1030401200d0700848106011250380c1c821610000002920741201c03040001712801034100130010601070080000684501c0d04480c15144541041c40d4140d58a1800b19000340c40c0383c1008100e1350000c100402001402a001034034900241c0a42d6118515000b05940d030b0016448080c2c01a0300421400749101465842510305500920b0030030300d459126101c0380c2c01d58403000f40280841e4404104181d40500510151400b01700d103101851460418940c00701d0b0614014001600c81241081910700c007600039070407249501003141d042000440c15080c06051003008840c03501440c09a0803c0c800d0520341031084910450307020103c0d042d9210049004c030010003003125001580c1c0c40c01c0002040316100111034142e00050300707004081600d0140706014003213201601c881c81041103900c50800107071000c90214103441c400c0c0b0b81111808040801246042105c01b1428140d510308440c494841c401034004160302d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 159828480 1250 159827230 159827249
    0x2505010c080c090904060b04150b030601020c0909061612050f01030b1b030c0a030608062d010308070213021909091b0f0309050c0405070c050d051e070204090503030c04 74
    0x66842c202c550610348a210010f80d40109550000f50008a49901c04c982d1200b020380005130b40d140300030346c3c60300900703094011040481010080003515030341001442c0c0d0b002070a4540b20401c2c00c0c5141c00c640d4600001c2c00b9400d00c0001011441541d134800c42c000f030b004004502c000c0c01241088000400c0c5a00d080c0010755058644e0000a88140d1780c1d9107100300301c6424400700d40d16554407607109101c0c580050f56a10201502c802001400c084100012130140315109005140ca80d00710101030415444080d10b2030403074030204010004502042d090f030b884550180d44036211300f0b03107010385e040c000c0c07241440c522543d941d00c190003512903a00960050645140c45410000066020100000c80481198180020387d06404031410203129801c200b0103684210202d501d603445d080c001405032070045030002c00080404031a8024000d0401c0048039151213400e210f0301d0100b0303034002109410441548542d1400e400540041151039543c001401180c02c0b009483e182d081c1460162520340c05840b40c0d4180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 159829730 1250 159828480 159828497
    0x10605030903042d0f090c140a08152205091501171c08060310050708011202061204050109120f0c02040903180603020406090801060506030c2505010c 66
    0x50081040301d0003910408001d60030185000300c800c0051101500000300045410861030035482c0c00340d80b00000d411180510001d49092107103103421030f0607031414101084030400750701e00050382440444611440c2d9141c40c00c030700d90303c0f035152445072104048a940c005050314140b6180c0042c000c40e0003c1212007c20501060311070412035551461480300022090082e40010001c0b100003144180b296400c90094421002d40cec000f4a281b030380c42600212010031030359820084c0c980b0701401408021120140d081241d800c00034801400603c1c14007500c40040c5070b50001c4000d650300c038400d54008c007420441014985c90300d40b6140d0b01900180702d0450702c41d003c2c00080800b01d8000d8040d00021046540d801210009a80070800906401c0c5426000e0090015101320841a07904014004e0643e40d1000350307582d4030b02403000380400c132568000841645003100030304c4966240400c0707070342104641d0b10480d00c038a0500c001d000d0800840d0030041c2c2d81e007030b881c4041003000b030103402c01c806000054403030707111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 159830980 1250 159829730 159829739
    0xe0a03050306211504051501030c03020a09021e36040b180c090a03350f0706090305040b0403030809010b09150d030315030503030906150607060f020d02070605040b01 73
    0x10950b54850f10710081c1e0304003188103540b00c40d0031500b080d809030085049806240401503411082c20f02070700b00362280da1070101d0510a50420121030001008820811407601030307402c5018040603844034104032501b00004a007203080700b0744403c0c03800300304c45540b8400c0c02c1844040013005100446d501c0b43c0c00b6908160001d205840d1010075600c0c0c5002075403000704203603a5002150050b50016000640c0035a04000100105265055114000c44c50383c24164141031020b8000000ca4030808400300503450030482d03800601400f00940d000130b0740c010004100942e036403030141e5007800780c2d4210820b182002b1500100303041c2d000031a940500701c440b00802c86c0b442c8403428000000c20844000d80c82a403040d0b1202e44070b04000c04006074540c02440d001500401400c07090303450203001c0e802607605d68400700500846100612407030360000440c14044a2903040b210200310140503c00010b0005580d0780441d03803144844d60112a1101c1e19600b003199110035500e44800200002d075019603422052800115 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 159832230 1250 159830980 159831019
    0x20f09031b150a14070501020a0e03071d0402150a080a0c080705040e0907090234030c0b190213090506030d12020a03090b0f0403180617060102010e0a03050306 70
    0x32640700000e0240c54010b004010920303596400740030070400308030304c5052800000c2c641001602d003092103200096910403074200010560b401140e003281c401c5e0000c0c8010403405a02001c48600d2200d214a1204255a240000b662a01100300c03210a18480040c00121050b0b000346501e03c039400d00c0d4000c1103200100c0034111000902140c203040458800c10081c05103030a8a172425500861510890350000e07203403182031b0142d800c4800b64480601140c2c091005139003001034680c1104a5981154a051000791001004034401010180c020032001002c120070029001c402c034031525001344199074858418955080898280c03295501640c44d10b40414141e2501054645400c0c505030340d0788040d00c01c00c41d07041000b035104200840074503559415043c009001e41100700e10443c25207000c3c1d5414506400d0150102d0b500b0881c0e41e040e8411240144455500f00c26102c1d400c03039168410802c156120b500503801031002d480c4c29403061084020660801d54003c1c0190301c03548084e00d0440305182414082c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 159833480 1250 159832230 159832273
    0x603050f0d0503060103090602070501090605060109050d0c14030f0105010311100f0c021504030605040c050a0819120314090a12030603020d0f08090909030c010b15070b09070504020f0903 82
    0x1c0001503003080892007a600c00c1c2c011880a5000700e00040c600141d40d9141800c6a00b25402151010f0300c8204100f8a982c000041400401c01660100201d5803d507541414803221030003070103801c1d60142c1c94050f440e10108607017009002190020401540c590a0002da00f1800869a5120305000a07521407294400c002803051004191034490404540c2c1c4c0c2042007042d2410061403200ca0705103c0040480d140c1d00809000d05d024446110081d407d000c140401c00e045508214030940c808200140d2041c03a0444891003235070420f402d04045080394601700d0140541260410407032101a05000d001c8201203036090701c0c540301d90104076400320003074801da09442403840065405a0300301c09950105111540c08070f0114883c0038481e16051060303000840e06441035034004600d92021a181c507030342c2424404c45148a00403a4681c4240000003241034452080e90f000403d585001c40100f4107207581001001c0207810300030b109645130341c00c04115100d0b54000c286400d21a01c0703002000b007104032800001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 159834730 1250 159833480 159833503
    0xf030f01240c0b0414030f031b040f0303031e05180c010f051e090a17010f1104030206090a0e070e090f0601021c0e0303040b070b0f090607141308010603050f 69
    0x1d070b140084160b115415954001071054400e007484001c80d0213840320610040c1020201040714540324280044003817003030008082d112002c3e11041000303001c44d8080c4080507080765858500810180900c285200360b950051582d40714840c100070902c44650707070030910500750303480400844030079500f030f00c00449030b0034410400780e8081041001880800790304403039201c1152100d6020180f1703100015011840e050343d01d074061102070444084060241c4c000b80130b103403482c1042c840300344180070800d40e540704039105600c4003d205620010b040d11464071107401540080040310200c2c0350790b282060001c1c149412148096100303442c01400a80b41c030b22080c003d036000380c1042c0c1c000e144550311880d02e40d07000c610a80152050050b4080400b100c0c0e83c0420050024000701d4030321644a100e00c1c42d081503500c00103081e00c4918901c000402c9200c940000d20b85902c81d20701d141804c40c0480720060100d5604c501021500d2040590030086541141508000c082701d11850841c3d0008261420301615021001c11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 159835980 1250 159834730 159834737
    0x40b0a0303090b07020402070c080f0609060c2502040606110c0306040506040206130b0a02010c030605010816081003020a030b0106020d02030a08150f03011401091b0203070204020f0f030f0124 84
    0x78020f04035400050031189102a100515121039600c41b005490341c640d03c222003540c004120811125001c0c001036402c025000020420b42c20510205083d42c09843c100c5442000012200345030303106410580d9a0964011304104400c1d80c03104001440944901041c41840c4640055007216007000501a4400c13500800900403503111341d801c1001c82d600c0001c00544650080c4070205020160200400d0285807507000040e030309401c800080e0907640c1560000e414040040204040ca810740c0202c0c131411a0545880c8041ea6a000d450103000301c00d9420280d0850704101c40401040000c0c038001e8142d4503560203c810b01040303e04101e03682d00c00c803211040040c0c05580403548080c0c2e0a4030501408074014000c0b01e1085600d00442e086a48024115007000c420741c00400010f4094810042003601c43d003500d2a010003240000b950301d01c100d0000a00a075030014281072450181410fa4039807250780300340d1503507074146202401d0820b0420302178500040607220600c1e01d04038030000c402003000d034542c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 159837230 1250 159835980 159835997
    0xe06070f18031e0203030a020309010206010f0312030f0e07030804030b01080102031311030a02090f04030f05090a060503090a02100507030306060302070c0603020915030924011406030a02040902040f0302040b0a0303 94
    0x6583d01c4040786140440b1500b003007440070103801031380c082c8003400400d406035005640300c02c02200020710300031060740011595000d038607080c404a030b540040806010344034100410803203030b107100b18070040c561f500b40c2c90b6050003080380100402c000c402c02441140e00400350203030582d81768005a400c0344016601e804020707102540002c0040c08040c0b49003036800000701641c03546006500814203840703044400450300070103201003000b01504600400390303a461514100e81009540307004102d0280140c010181130042c04000034415600401540c80700e182c9c064000300c518180c108015002da0000e40c01100070074181100498401d03c41d109440b22650441007081640c0e142c034005030000d601214005820010609110030b03408101802540200000c00c000d017902021301d10b0f6240e8071381408240d15152100070004000e41012a850400c990340c00715440d9a0b65100d1810b100000d10855005110050001c40d000642e006001040c2088078020b84d007d01c480d050741400c0007004211400010041004203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 159838480 1250 159837230 159837233
    0x1050a05010f020102070204050709031b0303321209100908040303030e011d07080c09130303051e0a06090f230709031709010f230304150e06070f1803 66
    0x2071441c02c258000c0b50000520340000c0c0d8021401340c69017102c42c5070119200050803c01c11500070f40c4c2890607450240c010f1005030031564003e041c031b42100c080c40314191a580c2e00c40001d03004c039986040c1c500c41c0c4440003680c5440304101c0c81c2d90601d0440d9030000601984030071140e4901c444c00742908040d0f01500380b42c0380a0864bc0c0540081a0006010100d5903079003425000c0820901d1415180e46403001c01020302e5450a45c00d00e16141c1d0002195000301d8049042c000030000c1c0c0b01e402c040c070ba035040c20003140595400300c412403c815103002000021120409101c4680c030194080b805a40075008144030080407126640c083c1d0704034800079100e21191901d007240303581401600c15000a803a00e4010f4101d0340d41d44503464890a01945a40d0204001451001568222403003401050301814031640d01442c0841500b00c1a030000016103407580000009010040301582e4412004944a020403401040c1000700d035650301c044a002c804507068040d016241401507158540e403a170101248018103095 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 159839730 1250 159838480 159838487
    0x7030201050f16050c09060103020406080103020f0103090203150f010b090303030708090c041d10051003060b0d080a031505041a2101090b040c1d04080702030a021509010801080601050a0501 83
    0x20018803444502c060040401c02401088006280c5014500071300b4405400010480983d4002c2c0c0610705061041204100729a00a403034541101d0b01104c0306240301d030010005070080d22001c02c6c029414014009640303100d405032500c007406540c482c3d1341c0300f482d40e80311403140a0a200e2090341c254580d009000043e1030074801d100f640e5011040d441a10401c01604020905031882407800a446003c0c07000703a011044010052540d042c1500310b8103101905040e049803442d02900e0001030b083d1134071070520080d50b448039111641c0e4594040b8000303548445500005005005c04446100344004801c0c0018091515000300c0742c2c03400c01d0b403120b40c405001d44000c01810b03000004004045594400304201602028481c480a0f1401b03400000668901850205002d00c1d85421682c12041140300860356420f580c0001940070758080340c519541c03665030000078505042808002d60165940765001ca40d80707082400380017401c0d001c0c0c0383c846a0766290055240c50348000d0251941100c41000100301c550711 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 159840980 1250 159839730 159839737
    0x191b1211060c070806161701060f11031303060204030308090109230f0d030b1c0506010b07020607060509010615020604050c09061f0504050a090e1b040e0601120b180703020105 77
    0x100b5204403803000303030744c1c205a03030402c1c0c02155860b854500814510343c01a030007600020468003005120500c030340c10510041c00c20300c075460b01c80e81040b42c80c0c42e0003014040f0030800c8469903000c80605803951942c03071601d80080d600030302085000138000804918661014015010300c60340c0b100f406050000700c0f0b40c12001c03003c101656045a40306070380c800499610140911204141d00c3d170b0700814200c140c0c40030b2080c000c0403000007194982c01000180e000c103402264a606480031900c00940d651904c0c000280c02e4000c621024196a140030248040042e056001c4021990340781040c100045036040e050380c541c1000c4501030b103207406c034032406d015624160310021362190000f441d0501e000c2026807030840301c008000800010400004040c8494038024549000600310240c0c14800300c114184c1d031540358110f80845912a464030b000861a6a40796004113205018440484142d90b941b2806600e100304071640a9030740484d82c00104a0ba50a01c922114002d103905004107240b600e9980116002da1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 159842230 1250 159840980 159840997
    0x7020904060e070e19150317090a0504020c061005010507080d27050c0306010e1501030c030b0d0c030c0f0807060e01020304030b01080f152205191b121106 68
    0x12024041400044090300c1c40c060178942c01180c982801c0c000c0c1ca2000c031054655035003202484441c04000042c4844083c01540c403001c040f141c0c482d090000807a19400c00c07908450b5001e400450303551410000058600d101e52812910042081e035208010f542600c150f200161500b601000136915500c156003294501c19988104c051002210021075040d1029141c41101d80343c005110000e040e03d410001c00b07001d400c504c0350450190500365540e291828103004440d0505440c0d6200d66040b50095010214100001d4030311089108540b070701c403100f4403541c00203c0d0705814075280400c280e4105070100040d100c0c9540140811401c1442c15211002c0035a001c904501c400c0101000144000320b0761030080035008010490400440704043c18a42c0341b200c1c41485060300000c010034141a1a0075101e0303000086800c2c0d040d0301c440d00303081c0c1c207008501d51240004a25072020b1806c0001c140c0885404180d40000c8111a5032240c2c0680060b00c0501000b81410541b000c1050182c60141d004101c0356 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 159843480 1250 159842230 159842233
    0xd030b030705040e1e0604030206090c0d0308060a031203024f0503120301060318020f0d02031204080a120e0f0609040f0c0203090307050103140a020a02030408010615031107020904060e 81
    0x4500616240b841784221040c4070302134215009100c00c0540400506800c000040c018041d2007003900c006c681d880f4020600034040160300404154280c030303850710317540c055504000c201055108101000c0d0281d03102d00342806c40804e494a40a1180103824801005180b40744803ca80c41ca881e000c200004c41c080c0c01220ba5801d4092000086503607040220b541c05400c40404d03a0707120340c0740c040c0180454030050081303445404034444100050b6100d01001d01a50821590500c1c151207034004030303250050341440802c0400c40080c1c041101800019601c103050b06c42c417004c0c1c50700003601c041206c0d18074000d003100703401042e01c0301c001200b8a030140160404080c0034000040c0c8607078485664007907903584c010140161f0030019a03050141418041c080c06083e0a08090006100400c0010000b40e802004104849c0e4003041d04d158940c82801147d0041101e0700c002e004c0e5545070307510060030450032850f29000c02e140c4001060450307407c1094810f841d03001880b03106d01e81d9031500c4060281c441c42680c6010b9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 159844730 1250 159843480 159843493
    0x15030402030d27030b011406033d03060e060606040e0c030c0708120a0605030c010e04020a030612030203130e0121081608040503010c051c02130e0906090d030b030705040e 75
    0x15a010105035034011343c0141210f0265526100d0505800b608840c1c88601900040040128041c4565121b0001d030060804903d00c00c1519011010614403140c041061401190800020300102e0b8019400120108080d036181e504d4900070040c0c640b080c0c2c07190050001155000580f03001300e96025650000175005610b192040561f10441d0a50005003c45480302d90001400742c955440e10030f6070301411068008041c0840b0740c600182003140c0603540107203d55000203101a8051103a0000301c0140290f556191154050303180c06500c03a04080f00a00032040610400144818040802c40c1200c0240b411480d00887e480303008a801d146c8840140c03001c400800100c041e600745c8140b90440c55008100b007689030b07400e041c00c150944940040c0e10341000000e21a401d021444265690384000d4400c00041e40c40041a611070800c084030743c401854080044100025080003291076485903043c10144c03001200c40d2402a41200c1d00c42c49016010750081200380700030300b8290b00401101c1a80000c81d00c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 159845980 1250 159844730 159844787
    0x20306010206161704052b02100f020705070807090c08010510050d0e0708010c11010903081f050d06140f0415020a020106050d0302070510030b01050d02070f02031b15030402030d 78
    0xe011058030304603007544c00404a440040c10844078402060788015400000034800c1200964a0527500300d803110f4175903102c821040b5001c007541181d80450f4094150340186a48404003034441c4414480e81c046503041108504285104054150683d0b8008000001c11074103c882111550080710220321081d5130f40b040c4c000007c10070001c000003000b03454000303d00106a564020000900864179030840e0f0706107580305d00029084001594042c54001007241e09110700b140050680c03c003a4007481d00082080003e00c24403485800c41c0f00018031074405a4180c0e118030300308864014045a016080d010f030103c0400461030150028100c107400d520000c1020ba1b1544000b840c21195031000300c0243e03200443c1007002c2c3c20310218203021150706044c20001001d00c6000605148600d8001c054240c0c1e00003556010000b061010f124440d4014003225007000e00b4515151500d050710402c41d100e07404801103d1041c000d0482142d01c0b55030301401034201c02c5071402c019038080412007210301088400800003031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 159847230 1250 159845980 159846017
    0x210603051203060a03030c02031e0d021e0601290d020a1e0c12020723040507050406020601330e0319030c02130605130f060501080705120415021303021302030601020616 74
    0x48ac424668070261207401655400a4a48440034074810a12030300000e442e80d00c0c00012070407a044940480c0560010004001d84045850109800084d10900401d0000d8140b019502510042c4ec82e41c580c109410b400c04848500080c0c1220382d03400207040c00e61040005415800d10510500b0b070381c01100e40050300c1d50b0340c80c4000070801d2070108222141040305c1c0d685103003a00078a9040040781c140189007905001c1c000f03403503140500400007036030715070108030291009540b42d40c4007204111205044c50046110002e10300c8150105c0c0314464170a200341c081030118003005100c006039154640c0c0701d104845600b840029118400000314050b951400010692641d990400c84160707c2c620000b0441c4a01462404540075604080d04200c00b0508100b0902d42000880304d28002d4031032942030507611417401100c68101001c240c0229070000c00c00b21040f07191000800140d074802c454010641c1000c50001e41240000c481d210b006034083c802082070440c00084100d030501d540e03c0d06c14007a0f240d107070084 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 159848480 1250 159847230 159847273
    0xc0503070314100b03120703020304030b01060e0102010b0114090f041107030c0b01080a11012f03090906030105040314031305160303021c1e210603051203060a03030c0203 75
    0x5540b602c0c920700715406842018400e000d03491500c1c0008000c8552800046551040446601c40c5c0e00030000030813500303040c001c1055800841c0c0c011820304d555a150400246410749840c031090240d0300b040d10010b0305600803e4001102c1810780002414025807000f00843d190f030100f456074000c6c0d40c510054041c441401c0c01842c2490103a201c0c0c03030300c2640301d10300314040a4050748030040c5a04014100000600700122403010310809180420040f024201d590018034141403404038135804100d0745000c82480403007d0301c0c8680701254043e8241d6100700515080c1c5e441150010006040b55210342c101c0c05101000e950042175640520000c02d950303036142d0303241c407071000040e1182d4040350508100b01a410030405104c80c244d810204215029850081c0c000c000c25040c490000c405031407011500c0d0300c036942181016603644220041c03820380d03c461400034005404165402c0c01250340007040c4d200c5400444e030203041c01401e0210100d00d50b0b1812110301d00840812641401000042e001d100441c4294 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 159849730 1250 159848480 159848483
    0x30c07020123070c0b03010501051603030f0617120c0c01030c09030b0f04060605030a020922150504031701030f030305060f040f0605040f090c090e0c0613050f0f090406090c05030703 80
    0x941c0d0343d0050304000001d40441c0e80514110102003005100036640801a40e142620001000c00b401c082490190041e0100044c0d40c6070b04c0d4a40840010030311081d501c03094100c0340000503603c204102019241007440b401f054041c080d80961060040342d4825030083c0110312181c5080090103449648070881e0304420794080110200e141e0a00061082c0d40c4942401000c0440c002c1007261001d038082542440c000f000c0c2d2020f07144503951841c02404806200110715804494511801560200b034001072030113940540016200c1c40c0c02c0c076050704181b1402030589811400412102e2a15603080700035050050441c0d400100d2955400c9481c1c6950180c004c12500a101c040b4005003040c043c44116015006001c2c24941014078100c0410f0121106205480d8400c5001c0b03250402961010301e00700003610400d070031030070000d02c1d04480100065a10300740c580407a2151424413400303042040100000350346a612007248401301d40042d256134801c52202c1d10880413800b01c07a40c0d0744002410204203600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 159850980 1250 159849730 159849797
    0xe09010507030b090103032003130e040b01050102120301090e011b050a0f0305060d0f02040b09130b060d1505090a050717011103092e320903030c070201 67
    0x9110115405001e507006440044e100c0302c80c9503141d5200100309400190034039100032440c3c1c0e500d454044050044035616406040c04080850b914500c0009d405000c030303020b5030740c0d1450500226039503101140150341115034504032419a401d03d1008001004d800c2240384040d9030b5140c9030105684600b020003180e480c00e480d115201d0000e01d00107030412482a40d00800c0514003c1004841d903603804080c01c0c03507a0442c80343c1882c001d0754070106d80100203425000d03502404100400c640404a0301c0b440203030b02d2080040107800d071541c2d0f00344030701031070101002081310740f0100402e816900300e984115032091603d1f04544420aa948900781003010036082101c000804410000c455202402800c40b0304030303c000701c0340c51480c02e00aa030f9101c1c0c001260345500142c0300494402000d0400500741c2d02200c0d2030200b0041d415207440c1c155440703a907080041d811240c803444c0c80d006004080c00020300c9415400d025601e15135960000401d0b6512408049050210220751f0f654000d81c0a0f1804841100005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 159852230 1250 159850980 159850991
    0x50a03200d1101150b0f16020901031103070b07030c02010f0c0b0703050a0e1b19090203010806040215090a09050705130f080f210a05070812070e0301061a090a0e0901 73
    0x14490300790742c40e80c04180c05134101c1600401905070000121550340d1400018561078800d442c400e00c0c80d0040460000c2d5204c6051030010040c0145424500c5404004500300c4505a9883c2d0040c0c02c940100300000e03003c074009001980165000d035048582881c240e14000c8403422683d03641e0889050166011350000707580b202001400091445540700300d0500100410010f1200e44a040904c508a583e50380030701d550001c0c2c403806180f1040000043c0186410540d220f40c2c40d9102d1b00e036140001c950992041c90701c84041402100701d241160907144000d05002c01d484d05004421010305805001803040103020000b02c0d1640006840400c054585c101c84400b685180682491a015800d00181c445070000e51451107000f00b03c003482c580c800e400c070715290346803011048160341c1c60190320009001c044000406812010003000e01512036601e0391030350504520340c90207050813514240107180200380240350045260048030050865400300406c030040140e210802c1c41d81c94041543c41214503911407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 159853480 1250 159852230 159852257
    0x90204020c01051009090803010b18150a091d0a050c0d020a0509090105062703011503050a02010807110a0201110115290f03161e09090b030703050a03200d 68
    0x488800000b002d13810400c1c040e094031501c1f0400c0b6031106116500407104009070b40c0b42403c503002265407074460002c01c0d590a00320003904400080c1d100c005403a0015800e41d02c04603441c804071071040d40c40301c20030300190b20315901c80385088010080030708211310b402070602800d106a4040d0000b0802d42285950f0309032112107410912070b0500b01070300068840c034011f1101000e0b00010388400e0714034022409008a00030320210120b0b0040c449409060402c00046001200340000017900c078811038403c0e40d524074036541c0d10000719602d03110034610a4090f00304041c14000356200c0c100d01011f82210200000d51480341409896440943d0780c4040d00d06820500b0b0405151140942004001041e4100614084095054007024400205030240e445c5120305160442c1c1c0c8210f41020401c2c0c00885030380b0010440450242950210307204503248a410203c400c20a403c0c01b00d01b1034200c95203d001850218215031701565084842c41e095640c1070004600c1880c080d0742000700c10307107147c420380743c0200c1e14185 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 159854730 1250 159853480 159853501
    0x6120a080f0d0b04020f03041209050a0906060215060a140f0a14030d0507020d0618050a03020105220819120906020d050a0504050d050d0f11040501020f0d0819090204020c0105 77
    0x110b03a4152003a40f042c4030000322240c2886c100c03035009501c140e00e82a83d00c14600c0c00d80342c400d803c0e0800c0346c00402c494004219484a07611685c240c481540840d2002110402c1c0c200140000726030700d82c2c1001314002d04004e9001d01a00f01c140400c002001e0f406c100b417054010650000d03203903004004820441d507004106040500c94001011101d14009150880360b030003281d081088214010300a40c2d40d040c6240450701243d00c0140c2955115055034034041c62801c000b07002c2d01c010303550f02c0c0c0314202c00c1d07140000a64000c4101c01129902a0103581085d5a003c580a81c3d1b1600c0c00e041c4092048485100030f00034064400d121100784a80801070f05c521808203000304440008011511443c034203810b20020070000101041049480d1a0180c1e880c5002034041c800b0740064070503400e1160900404c0d9002040307980240055860070303403c49142d15207601100d41d4401008c9404400310349080e0105034800035043c442140048032100c04540c42c080380e03010074100e07482440034000e0303030b555a014010b40620 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 159855980 1250 159854730 159854741
    0x150903270414010e0402090a0905010504140601060905030a060c050903030a12050601050702061b010b0406061e080103031b0201020309120a031805030705040203090c09040c06230306120a080f0d 85
    0xc034070300362000b59814000302c0458184003a0006c2c0c407602d029400614120750a402004025a02600900140c00c0a00c0c0c12013106c10700000f400747c035014600c00440c0300f500c24604c240c1128001401401c0c480d025448440003026681c61100801c80100300440b61500d0400c001c050542e0255549200304081e10b4008040390009840e007810070804205daa009641c0e03004c25640c1070006011076408420850103114010700e0500c02e1241c00a080c0b803800103c6c0c5810183d80703503803e020b0032202c0c0400e291302c0740c0445000801740070080120f80b10b43c1c1100b00e086010038800d814030b441801120307e440c0569001030000d9103075900150055001508040805500000424807620f0b0301d202034406900340b80000c2d840304101d00600d809164040001459407004000741c00c0351381c80c050000001418a81404c03440b0f101c15014a00c041907101400d0b14141c1c007136510490059010003042800c1d82c88140800020300700410460f41c552281508601c040340e9494001d042e4090070150490b170781c9001055010a480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 159857230 1250 159855980 159856001
    0x90b0408130801090c0501080a1e15080c0901030b1e01030c051c08030a110d090803010303080f0708130503070507081b0303040305030904180605130303050105121509032704 76
    0x74113040c11040050400071a000c00e035002401e002255941d08070780507000780310050203070055441414184680c17644039403045441104002020481e6911062404e541d0003420401507081841d6000402c00328580400d15034008055814421000c405031041c10945e11003a0800d03900603088440400041c50000208100a1b804d580000c85801d41c6407600d101c1408000c246001032900c0c4d030001000c5588400032100c40301c0c60904100200300644c1803a6200d60000d000840106080b0300106051100d0400e000740300c2c6d4a2980c0b1600c0542d00d400c2007407560302e0107000445aa1106100300000107005002c541c0142c100800200100c01c0e81e52100c44030b44095150b0349010340c1040005002040022080b1350702804192404a034040e90104424451030340a080079003a545031209000081044800f1214154041d0340d090000743d8882d000c1041e00d11091002c0807a0390300c108036030046501c026400d16408104a01a03d00f03000c0701e26801180102c3c00b807804140940221040c1c0380364035051180d040ca12 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 159858480 1250 159857230 159857233
    0x609010e04120f14041202040c090f12032c09060415090207020a0e0a09030e1002030703080705251407060206040f02030703020a1403010f110913090b04081308 70
    0xa00701602d4a0b18030b03264405007502049188911550150b02448140303a0560710706807420f5032155500e01d0403d010b10440c104a01c590b0524030414223061081c50580b054508104c2c7c030003046807401d0b45a003045d50805504070241f2544100c030200300d00441400852501104556242d00b60f03000e0f040000e0f600000704500c0c800c030719180800c10201600c04000058896403000103981e4205400040c680c50314660140050006a5003080650741c415000034100d54800d0702c0d02c5003504196010000104481000900180d0081c4a43d1021a01c1801d249030021010308200b403404248201c0c030142c4070082580121b907011090000000c1007041c00005c0c0c00080e20b60050074249060080083d1983e4001d4030203043c546401040000359501405000010356004007100500d44d6585c008050103020500c1c024420752038000d40610300152809640c000e030030f2020400346000c180d4810032490391100002420600d548500700b43c002069002d10601981c01105d000307481b01e07103001a00104003296080310140e17 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 159859730 1250 159858480 159858509
    0xe0406050601030e1e070b0327010902060a030209011419021204050d1511040603050402040f1407030911150c060a1a091807031103010b01091809031412060901 70
    0x4e84a000c11420f00c02e503140030051104100401c0740d02d02d0038072141c2040b85038800000600c50381c6402e060a9490450b07110500b28401c50400340394608a619601d0041d400c25810440c0e07050031031107540244159001410032024000c84000d0120300c0f5007107001c11521074040e01c0c0c01c4039146501040003040c45c5c0c042c0008203182604101c0440c54020013200028040090f08802d09034140d959000200c01d1030764960301d241c8542c0c0e1080020040c10050780d05a004526020011620044a014031503d9040d0310700701d1034031515509000c400600d900d502c103407010041e00b0420449541c0e08514071030071641100311552200c1410b4603403818080050b20185000d4a80066a0140040280940902141168104019520008070000051070000507402c28040c2140c080100000010712030300c00d6070190700030028400d020005503040140c50144a441d00259580280404103030b4020081c2e40e0f20a03e0309030003411150300c2100312904005448005513501404016542c2011003c2c24014645009824079 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 159860980 1250 159859730 159859751
    0x6011409040503121b070507060908030315010e0415030b06090c03010e0c0d090f030809070b18060a02070e07080a0c09030f0b0a110409061d160c15060e040605060103 73
    0xf501d210341c981520000400b01e00040d41102a01d00c00746240f901030300da5507038a211500d450354941017140600d41c00314101e60b07808a20002c00206603442401c0d40c220000d0410344140c01540c04107406c0300c0aaa0098542031640d03c400c0c445d05100000f58840c02044116050840400c00e800d50024020454200c09000401c01405501041c0d50044079000d40541c0d40c5804801c50f4018000d00030b00a41000103407401441015440140b542c41900808180c0d01c030541c40b140034640354806c0384d00c0d02c59000c0903840d50310f01c0e900e854002014294220300490b00c40e42d07503410198070000411664180820103100c200710300c0103028058030745510000c0c5803004a82d030560ba80c00310400003150010304040c4807a00042c0c42c13146903034008040c3c29104541d150b22150307180d00d1800075280900800e20b8400448017008210300314184954001c00700c00c0003510b9015415403080b039120f40c07a440140c481c01101c03480d281e824041480313400c0c042d040c0d4000d020f404e864241000010f444c4040c22440c10903281154010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 159862230 1250 159860980 159860983
    0xa110606100207060f050f031302010e03011514030f0717010608060c040306050612010509010c020f120a050d020d02040906150c11060c1c0201051f050a2106060602060114090405 78
    0x14207135001410b00d078466000200003100c1c64090008003450603030002041c03203400800c60007415140341c407d83c2c1c2c04807210a10000d0500340d404940d0450441c0907100f8052050002c1c40c203c540c030408000d42110280384d10411254600007080d4083c039030f060300300c151030300443c9002e02800b80035005c041e0040410f1700340301e880c07200c0c2889540f0011f448559100c0106d043c5030303a250280e03e000f5407502c00070711560410406445c000c1a501c0200f40161080840c409440140800d060382200c1192020a05142856a0a94452b03010b02c0345d0142d04c0c1c3d401c1042003950f859600c040d0004d0250b0400c0003071881c1c1051884a00588001030440c24084e26040340c00004030701c0030000340ca00070203035100d0351181c03810000c95181c02658030780489600382c1555541c8020391705611140c070403030b079045901d45062240007201201c08040d000c2c454000715a990240b02406083c4607144403510400c01e40120030b40940c0700d4500b1103056802500060308428010010b003141c950902c104007108130392046e101d0130556544d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 159863480 1250 159862230 159862243
    0x103120f02030711040209030f010f020409060503150105040c0507060c020703020109090506151303060513230604030305040f0f0f03021b01021b0a1a0309010c0f020c09100b0a1106061002 82
    0x11341c810f030b800142e20741068a00303010042c460013000e002400301402200b44100079422034012201028986035000410389400a000003070800301d0301480c052a400c040a2001400c1d040756203605001c401c1104100142107841644402c1c20550302a00401e4194800108074003030701d50120101e81d0416050011954032104c90030704445d1032a1600e81d0707801651540f01d00c0601280e202a10f038900d02405c121180394144001c2d12814411032584404041041c4004082d14500400300c0003036008000190004e402940040e81140c00344042000514003961083c0c100008120122010080c08250808040e01003007845050810318030104414408800002d503036200300e502d0b4801d03085040c038405040381c82c0d14801102800c4848034031000d5042808a220040d0320690326071806601e4621700d07400d854441e003d5020766690580c0540362520240e400c0100f0304001514800750f86001c0c840c000780c1001c41c1002850503540c50707120030514602040d011070a008005005a0103038000200a215455010030071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 159864730 1250 159863480 159863513
    0x108061002010e0304061e030923031209010c02010608070506070b04060b03030a020f1908090906040b040f0b03070b0a14030a06050301060f0306151a0c0c090103120f020307 76
    0x8025800101800480c05030580105100f01400000340100780d80b58030040182c4c180c0c0b0100c0044114405016044040300c410300c90240140c2501d5030158501543c141604062204800031641001c140ea200000980025501d0804580d5940742c0e02c002103030203006110042c070149000c0d29201307181070080303880c91164550007080d070100c403070003c0d007088404d82c0900c0001030050200c0e07445640143c3e003c2d50303409034500c50300317000e20902d24038461841240409080503a803041c291800c18115505105020310054166640140c60303c0c0250802d03241d078428044a4680d0060105450030400245401c0004cac6401008000208120403203040e50030600c031044e1000304e074441e5544c0c3c5c0e564100700c0b0300800075074000a40c0340d42000d82c002030009600308a881580c2c0a0b0f0740c20002040c0d0f240e203011001180f84101f060006001e100003055142490203000075500183c1990030400d840400555140c00980044034039a918081d40303085207600000b0020710310320071f00046151517040d849444503000d00140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 159865980 1250 159864730 159864739
    0xd030212131e02030312070206010501140a0207030f02061e091305010e040b130c0b0403061d0d0f02030d11070303050705211b071101020c01020705130b0d0803010605042102010806 79
    0x100d102c1152801c100f1030b0450b13a40b2410f021207505003010002d4a840302031083c0c90000326550740000400500307604441e0030700c9207600140403440c5580d46400c6009000c2e84281e81c410424840110116600707000f1380c0d030402c1d02e000c000d940d8241e0401041400c415041c6030100051030100140104405520301030341198000e010a60550396400001d01e41075080403000340084c404a40008103104144080e0054910411062110700001e0788607296131594001c15000f9035101c4410402d9084c042d004103280418684166031412041420344403e8560000c41620100c20020ba90307410f1603854854160410024500b2515021500c0c20784009175000c403410101c1904840003040d40c210f071a0f0200c030315000300f0300e40c0d0544031034103814550148407035804524054000c507035034440a50701c041420000e6a50040002102101d50780030880281003c51000b600038004030090400b141084003d1070007400aa6201075840f42041c0300100358407203401d040d45410406030003500050b80c2140c17074030794401000d44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 159867230 1250 159865980 159866033
    0x604090c030503040b030709090e03030a0905010605100519050f07140304090c020303040507050102160308030a060b0f0406030b010503100b07031e0906020616090e180d03021213 78
    0x140034a031a012948010281c3c4800580015204c40e100003541c8120182d44038486401d41d52180740c0180c1300c80340e450001d141c00c10400250700344003550040780454081c1d00005180d5031200041030780c01085501c00f41c0030450200300c00d484514641c00410b0861614540319040c2982c0c078501151500600100409141549031402c03c0d4000800c00d5500600c4d140c48144186048890003075100e52040d1403c0d0b85030301520102103003039400004c20060040c01d8001001903103141d612002e0320b6400250095015507180c5000180b0340245801a01c5041844003030259614034283c070150403103074aa407103d0f06004062007080040d0b030324100008111782d49022081c0d500c2c0010314086900950480b0440c0c983c075074402c03654560a41c0125403501740c900b00d03000c5410903250304020308200040c1411040000314045c03c140300307250000c4007603078202c090302e04d07103020016040700000c1c03c0203440c0008000099001c9090f00b800c0b200303000d8290b00046002004114921252141c0e12500035810400601c1080c41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 159868480 1250 159867230 159867233
    0xb0603010611011e020405030c040623010e1801080709061d1e01030804091d030a0c030c05071d06040e1515060d0504020414250c0b07080103030f020c0603060409 71
    0xa400250820b0740d0045032655480c980c082a138029045401031a0003071040229240044c1020b22642040c0d44000c5052810119400256007840300c41003193390400042c034000440e40d80f0362503425007045442c045050308035030521981500e010502d500c040040d5050103000c0180a140a0640030074000701c410002c1180da601d40103c0450140c1c01c2d084d24150780200000044c040000040c1013a030700c04ae00709105081801c207400711524172084022889070000c0010814040c003d006450300d1134440c0c01c006441c20318903141c03c0d040052540c02100d4100c01d00c400302ca102100f02c1c0105511103421603041081815455070107540c2c038803505140810305000c00218111220200c4140c6440b00004c0006503240181c903031604c060003041d2001c80c040c078104910000d503242e41c880700910a186100f0f4011840381c0c0140300c604000555a1060f00b403020300309418011844124446100710440d4a480905501d140790044c03c1440b400150000c5411980541400742e0b0740038100c0e074114034215130110305100315 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 159869730 1250 159868480 159868483
    0x30a0c03020f0a120501080102040605090f030c03030f0a02070b07050d0f050c100e060f010308030420120c090a050c0906031005040606020d080c16021c0b0c13090b0603010611 77
    0x44001d0314103140400f09007515520b922081102d403411030303040180141e0f40d80308481c509034012130207070b0008240d041c00700e6001403c09110a0200580090441e00c0d44200100880c1c110b9000305005160b6803000143c0015164041008000905021403c5440c003c465141ca540350001e59404004100d610101241d00c5c501c00c3c410769000c3c0c00c1c041b054450b2218030001101c02000300c0440b0010f9401074100103034101800c0e28445040302c0d0030038406455903480796107410328042640340b900076407103660703604041c55121000c002d03038203031040d80080070366680070410030486041c001c0110803024102800c10901344940360607120b111401b0b031055503c9440f8455100d400d21138540040790071510b4030f071001455039400900d100d82c100c0d150b00c4031100c0d82c8800311031030864400d084100303030301c070200c2c0d0001401400d00301590029044a10155100c00e503407540c843c1d031042d000395001e040c800030100d0f05001c07060404840c6002031031b484404102ca18644400b04885000500c82c00080c0613610460101c0d0110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 159870980 1250 159869730 159869737
    0x14010f02010b03160e0c030103080f030c13030b01090b040908190e032b020307030813060b0301050a020405040c03140114060c25150c06020d06050a03050a050f12030a0c0302 76
    0x8064800c02c20010310130101d030100e01d02c910341c400c844000104203151514000c5906a0781c0240c203880c5000410160314104c4d9002034442410401c041110701d0024a04021300406188500c2d0325035025450000d142d02551251407031940304034501803025001179140d400b150b45000900100400c200350807482910f4100d14408460b415002d201c41d81c0f80c0d1194244503d82c0500c1d401c8010024042040390100e949001d000c10003408507a607500461389007841a643c40140c148075440100381031603407402090945030203880c00e200107500403c007484140313000e000c0e0440b4886140750801c0049000910350b054558107104a0f0040c290351070780b11515403100c20446003c80b444004503a61a64094801e085850816580e0f451019040602250820051303d0550b100c2c031182d038074203c003404a030311454029803101d040c03401d0300f0743d9410000804c0e856005030344005502880203084911210f0511504102d03483c2052410364019030900039100740401c042d00c0d04200081e0000400c42c4007404203800a20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 159872230 1250 159870980 159871001
    0x90f0a02041703090a080f030706050c040914040b070c0803012607030b090c0907120b060c010906140903190e01030b041404060c0e0f06070822030c0f14010f0201 71
    0x10050354002e004070000080141041c107407160700500d640c0d201c1e05626101010042d65050308100305140c049081d0740c01c40b5804c40030103500c1d1032900d507460001d0011603683d841070011138130100042001f40180410010340c005128108070350b43e001c43d42e5804a580c0b0050040741d40b01b480b031048542e0045040101420b540c20150b040320400d54913414000c02e0200c04643c4003206125440c0c10300c8490404210320740c040d08031a114511150805160760001d4011413144542203030080c010242a08424019180b46074002c00e000591003d8182000c03c2c044401040307040306a104000e502c5411800d451000b219181519101440e8260000100d000d44600d5000c280e009086c8442c071180c0e10a0180d5190046104840400107882600d01c207844080311a4440e5602880401c0304580794106800200030040c440c40401d0301d00812051548420384103600a9598040300300c50078420040841c1031300020349008440324107944c0c40e0980c0c1800020003982554100451b148256401038001d400212043c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 159873480 1250 159872230 159872249
    0x6110a06090f1b030c0801020901080114180a1a030307030512150301060609150e010905060d0e01060602031c1505040b0301090c080c04060e0408160c08070321030506090f0a0204 78
    0x4005120710012043d02e5400140c404110710900020341020510860745001c9060316010200c0c2e281c0f0180212120340280c000340c001c00c800c0e2a40d00c1000d14a41030350710501240c0c000081d01c401640950f80d900840c010024002e5204001940c08aa0002d094039406805401c5825040d070f200ba074450307040040114595090b6003440c4000c6a018bc04c0b60318401610740841007030a102280c0c410456401808244050103e081100140110b0500d1801010801100000464912032a8007510f01b120380682c400340050f0800700303100313440c1d4111076180114001115402c2c080350740b231350038410758500075807181500c07442d6280a01e48050314203400c8100c0070340d04480142c420541e240c00e40c82e1128007502105200c0c070700d0503201250500e10501c103e40190380210259092480d000d07000101491156400d40e170b007160103000012101000c00052001e540305001610040c2001d8407007036803450f0b400d4400010325050404004181d256424420f43c06000044000102d8403001030f488000c0c800c503000305181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 159874730 1250 159873480 159873503
    0xb0d0f060c0c122c0a05120f16060e09091005130f0b06040b060a0c080f070c0807091a0105030402011d10030227030a060b01031503030c030906110a06090f 68
    0x103c0d030021044281c000502180154950849010304101d00c2d83c484516800902150300f44900e08000c81c80e980e8060f0040304440080d1f009040080c1740045140849042070905241804007075400350404161300310a5814072103604103025500d840b44000340c000038081d60386100045140c0d0400c6003d90713016420079404440030045050044c00200200e411038019418840034003143e040070001c403625400550380b00310381c00501e07580d03038211a4800c61020645070014408103001c2400c0c080144000d10301c140040c4611860300c242c0501740c84030b1321180c100c50740c840d45802c4001c7e40c0020450307a0095091070180c0d0350f0b00030144480c2e280c00341d10000e2a0800c4190400c403e207190075038010304d0482801b1109600404100800e5000c0d5039080c52416016006008a100080d507550001050110305044c00b040480b241d980303a480c840300c0c030761044e0002041041c1e61804c1c580c010040c00054410b81c80c00c2d00344034015404a665450b0440b500400241d039a8260805000441c0040c102d8158040e010300403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 159875980 1250 159874730 159874763
    0x1505040c051305090f120f0f0d0203010609170304050a06051b0d03060611010501052202070b2409060102030319021b070501090608130b070c0506070203030a0b0d0f060c0c 75
    0x4202c1264034900ca0300c541da0005c4251400040c03030380752001ca0344c2e070141d00e00084140c280c0301c1500182014100340d8030034000031841038241d0010758040c1505a48001c0e0b61494a0b145070501c40f601541845590010842032015845803400e410239103440303041c05595010304080001c019a103030340c04841140144a00d0518503503058010300c08541c010b0381c070f0342100f134038815101d07007210400e02c0303100da1000030385040e2061841c2c80c003c18400c500c0550001414020180c0340c480f140003040741e0801c1006202d040480030490400000a0040800c0c3d820b40d4841c6001d00002c0d60382c0c84040c1c405107a05c0310a81900d0014200c0780c04440d0441c42c5074001ca4000e00c9807401c850b42c0c0b20820300400d4082807440d42d01007065031040f03921502c0b45a1840d28110307100440c1d1109855040c000d403030541003281c510314bc0b40c0410707010070602e07000e00000d40c0110356034a010800002210040e001e1075105440200c0d10401266825200c44899070300700a00080da24122002075482010007400203204803c016102c1c132 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 159877230 1250 159875980 159876019
    0x903050c0a140c01092102030f101d0d0206010b03090c0d080c1c0504030f02013b0d03021005090a020a03030c05060a090f030e0103021c0b13091505040c05 68
    0xb41c1c1e4190908440304244103000540707080b03981d0f0041220030801c0d1224912a0200020700315041d40c0040c05488404107500700c140d041001c0300794145002d5440f0444a8034655142c0c1c10242403031810380c0944000d48001d40000e49884042c400d800601c0400300101c4c58040b070500a248070000c0051010794001c0640ca460030807600a5001c0203680d00902407084520307081490f0441140032103540d014501403d56071800366005540005a0403c9a040321440e5107607145402c43c00c03800601128210b943c080c807142421080e00c00640390713001c4c41610813000002030300003d42c010310a10450010815a6500c01c1d0180307051302e2420041d601c0150000d0000501d41c0040c890300d5200d000b582034031025943c2420410546005e5900108414408021080071a22500456260500500d03000d45440c0800130b400441d0706072640010080b6580b0901e2001c00e00c0e025920fa03032541040c0c1401d010841341502d403952101e001c1110000d40585400000f41005890046040544401080b45040b40216181c1e80c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 159878480 1250 159877230 159877253
    0x21030403051507030507080115090b270402040605270a0b032a0d0e010e03030903040e0112020d02060a0905061306080708010b0307030e0309120f1e030d0903050c0a 72
    0x141030700746002c1c0440c1c1518443c5c080d55100d040b950710f80007a26460007074131380c0310468640c0c4083e081200c021008259480180d0007000440f446004405094010b0743d10303c52850705089100c0d1185204200c200300307240e04041030b03030911041c42c0c880040c2c00340302e0440800c01d442030f0f42d54545d024100a80c0400c000b1564405180103c102c5c507111840788076036900170249110010341220700c400052103281156107403600510440450307800042544c3c856449080c1c03440e0021b4444c595160030100303007800f203014050341080c018a41000402d071003d40c3c6401045808426410190050b0b4000480300a00c0e405500c080d4014070000d000c4a0fa5601724004000d0214003074003484000405160200c2c03544c501c50000c15050782c140d050068a5a15440000d40041044c0400240305000038042c00c141681c0301800d4002c42070402000d05159071a0f60ba169050183c850702c2c0184007144144a50303c0302c0000015110801c600c0302000030110000d08040d00c0500880385c0d00c00541c812101140e003000041e0081 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 159879730 1250 159878480 159878503
    0x804050a0807170a03020c0906030a0c27050c040b071a010902120903181011120c250603180b041a070e1c03050708040e0f010b182103040305 62
    0x101c1111403080c1c3c0300c103803248000e600290041e4061001c424561500140140e0000d030020101e40c4104d1040e0b4503051100c0300c581c000040c40400f0070420303010170500a92040c5503441703804108101d180ca040f02d41403501860261440e9403102040180c200201682d410f00c2c04412001250a5581e4480d5000041d510040d84070311910115004218000000000d45801c180007054420103105400240302400701d00c0d80c164020005004248030111409110b1059070b581074206c61a940c0c3e01c00400f403842c04c012000000400c88070003101c501c206014400c5503043d54040c5c07801042c09030840488518040307402601910804e1003105000422014004081c200c44000c032041001d6a00c0d03201c2514030300c0300d08032242c0c0c010300228041810b40350001c1c0d200110602c2800c0950620000ea1135071030450b00701d904046098400502400301045460380d48034010301d14000c420740341a444201e42c8104450b0b02904a0050341142c50711019104050f11000c50460302c40226a10342d0b1707072402c6c015a9407904208 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 159880980 1250 159879730 159879749
    0x51f0b0a0608010e130c050406080c0307050f0d0f061e091403031009270c0e06030703020607080318010c0201060906170c060703030b1804020306090d14070804050a0807 74
    0x20009801c90050350700ca41203801c0e1042c10506a6603003680004402c031000300869a540c8520004501c9a84511a00c005040c9400c000c00b1071845040034585480c840380c01c81403049644020400e8180e0b615080340b07803501e41c0001c2c2450000594684000a0700c82c00c1018101c07100009044410711441e984424200303401740300410307690b000300c0340507945901c400e846003c140b1a0034101400f100507990042d00c1c140c91790b0110700a206500140d60458031200c09800c88400c1c60142c6c007003010b09100b25405030400300c2140070304003c1d4551b40c0000c0840c42481c000a06048000c000140a000c014000c1383d00b03880110020310484641d43d1009009025038040c0c907262501d000e201180506a01400f001c520b200e041c0105041003822080000e150403a0350110201a1142c4119446442d0b01102c1051034407005c07210701c0b00703043c5032040505141009200054a03440307100c15200c0e0710350003a06045403a0070300c02d40b80d986071400c9c1024102c80c40789410507130f008907501c640004c010200044002c211812481c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 159882230 1250 159880980 159880999
    0x109061d15010501021b010c1a0405060a06082d0601080f0d050f0405011b1a0402040e0303041203180203011a09070203040b2709090a11041413051f0b 66
    0x85882201a0083c00384500503408081104004003070440301c0a40d00c0014103060300385065a6481c00784001c07108584001c040d04040600003009000c0008a03045500e010b000d2220508101c091a82c40f2440c14148200c8102c1c00001c680c5000700d150210316400000e410344002d5038407000d201c0d0b601e07103840a010007188034040300101c02500c5182601d40307242c0641c203d18503140c502401102c4111501140301460031078021800000340741003801c0740f614207241040b5031051030503004000448840e4812454290030400c02c101c0043e40000741d42280c1c0302c95090006040050820712124000c5003200250158a005500c0e10110940da95221a480c000c41d01c484540c0c0c0c8940c0b0490700c0f805a4811002c0b2103005009009804041c0e03080d0702200001c91002c0011042107100041058109940700511504004191414003100416940398000d080c5c0f424130200c0b1001c10085401c10004040c0c0e944100101010350400c242880001c0240a60882d4020001c4250305480d0043c442078400d00e116a0500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 159883480 1250 159882230 159882253
    0x3020f0f07050904150e03040315060f14040510081207060b0609010801060302180411120604061404110f03010f1d04080d0b030f01020a170c030103020d0f050109061d 73
    0x341c0009407030014051401d140c50707994a040002e842c22102011031900c070240c140303145a0401c080d1000b1409034038880e04808105069170100c401503040f204c000c0798822030510200745915101080030b8801d45001440c1d9a070303084151419503564124001500540300c0380c002811082e4060100320380104000c020b0300010f8410040ba81c41805112070101d0f0980c0c0c01000350901903409090300d107155003e4168003003150000101210306010501102070004681e4801029004541396800001642c3c100074107400d003100004520714848200d03114649840c40c10060440c41016541070b007880c1e04445499585a00c0e061005460600500c0009081c2409030b123950684084214004c5410034501d5140c0320020a5004c080d2a000350004c1d018071a07802d043c15000f500348014420101195200c0031811010104900507001c041c0038104a0031040c401800541d480c20190365a40e82d000b5003186d024009850a6030152038140307405480545806890403075510030481d01701c400e15198044e0303003402c00d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 159884730 1250 159883480 159883483
    0xf030f2d2d0b07020a021003021207080105030304090c02010b090103080a0f0215040b040f0507080105060109081219091e05120303040c0308030a0213080102040914041104020d0b040903020f0f 84
    0x4941c01801c8540301c4405030800b240c030303100709a03810000c83e02c1035840b69200358010804115040d20101c0c0000d6000940b405604008004160084807178a025a078035490100029035074050b0f4004c07080255500c01410021500035888512070a401416082c0d0540c5d603400c041c40503811525410011448944e081d8440d1480850350803403441001d03581401a4482d611502100940140300311400680a02d204010a0040280c400100011000850345181074000185032840c50782c0580299804000107415640d00324003a03500c640102009078035500480c01044401c00103540c003001c5020101280c1440d45000c1d041c41c1c00a441055408658000000d008030395a44011200504a58160a428000608144021500030050880c003505198000001106003001030b4000d000c1a0340c00101001620410f000300102c005424000d0030031443c1c0f030b80701d106c400301804942d40d219940c0005d0300070036860729600c56811460050b20800810295180180d0307907803100800a84580310300346c00345060450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 159885980 1250 159884730 159884783
    0x70c051c08180406300c29070c05040c1818060b0408010207020108010e0f040204050a020c070f03020f0103090503040e0705070b010b0706050a052406090909030a0f03060f030f2d 78
    0x18417010303c0c0c44240c13070045021129220b000365510819010000c65095141200140c000c05004249d0024114076020420040314000c035503c20920412083d21410002c1c030314003a10407a5582c055003810703134095110100c010451038002b1101d4880104010504640c158080c1500b40c0c801e0304c40078020b03602c1d110414004c80003214443da100308001d0005005051903000f2070b03085906800f0142c10100c06004c203508060058100040003071034040c0420951410390344400a51800703090400071800c164454a40720720450207000c9007a814900400c009074820f034110388082d5003207078108800356101c3d01c080030b10f0381c00a4420b85d100d030300341030115200580300d2160386e0103203207a540d6144141d10742c1c09800180060340030b00181c0c858028010400d00303441d004c030843c0c851006000a0b6036200b000400103007030b4202c08004d42040516001d810f11500510021001c00d50b600800b41c4581c551180c609581d0713107c01107001500c4502c41046c500280c0c507004692010851003402494400008100114500309 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 159887230 1250 159885980 159885983
    0x60e04080406111903270b07020a0515030f09120a05031f08030901210515030609070501142b1d0a0203060402150f0a05070c051c0818040630 62
    0x900c44c05280000c3c0c0181446862100210080020901314071124050010140e0001d040140b00050000031407074032015810180c502165000c2e070f01045500000a00e0000410032178004010234049420300e070080022800b2200540485079546129200052203034100380d540c1c0301d20320000c5040d4080806c0841e102d000740d6036041c0044d41442d482030300441e071401d012030f03000042110075810071450075403a005252245408036800c2c126840b000091602e081001000b0b51615080410140200c0e80c0c0300c0b103550700c1400450f40281c0c40b951702081452020a400c1c18071913948024040111860915411520a040402400d01942c1c201c0d0150961908419030000b0b500d80c000c00001401441d0807078151010184201d5074905004c02183c81c4840c030751013151000d01007440031440504200410704210050712068401c03541c1c55178149409862000807401c010030340c0c1c002003483d0802d802602d03c03080811000400a01c0313803ea540401c0440f1486c5141c14603005520485044c035a0072175030400a002c103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 159888480 1250 159887230 159887263
    0x11010509100f0504050a0803030714040308030411040e030d06050f0a081011040b0418050c040617070e1903060c020d021c0c0803010314010b0306060f0112060e0408040611 75
    0x1000009000c03145000c0300ba0041041c0241480302080326150042c0603805820300e5001150b032801c010702d000c1d10b0015200341000480d1800c02052000072544030a4a400550010b0f0034483c291019002901515202c01c00028500c0b012450740413034083d580022088410607190b12404100700002d02c0580919405030003025804490740d00b144003810703440500610b81414000e424551250b007121825440355014040f031000e055000840c01269128032a046000864414502480c1ca880030f4018401e0700301d00080c0c1208440065042806101a400d0703403074005000708040301601d0000c441e028018041036074000e150032120051507000140345240545980c0042200e84084c5215801d20500000710748104000b0700190070001d62003a000c6c40c00b039846450210311203840b411043e030071203110402c0140300b94091020312a160305d41d040c584000040038130707018565400410100003d05103d03400104003589131401c100500280074003410640e102135803040b035404029007900d542c0708103055045050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 159889730 1250 159888480 159888499
    0x9070807090626011707060504030308060f0f0301020f04180e0705220f0203041406010e0c13030506090a15150608090f12091c080304020906060d150311010509 70
    0x4540586040c5010f811440225002046941082a04802c003a444144c081c84022140d9541c05403d20017500544158500300c1d051514544006000c1c0c40050141805450744000742100d0361207018440702e07442e0000d4001d6607920a9061031110950191082010005880c009000707160018040d94800c04c00650007040742c9410a400c004e40201c008011200c81444401242105859070007902c00028000300016264602810400111030301480400d00540000006100c0030074450045038011340038425850f16001540d8250150411540000d0418482c0380308000505c0310001b8180743c00340c4106500c24040b001d014001040d120810321407202c821f5000e00c18011103110721081c0d40d10410030011540009044050715040280b8a00d01d00e048550010749081a410a0301030840c00321074aa03a404000300694680c40603c1c00302500080c454880c14011902c2d507503038542619846080da150420041c0d9440b0500d0300100d5451100b03c83d5a2502240d8030019805002680d81410014285464 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 159890980 1250 159889730 159889739
    0x5030705010806030f010509060402100512011802071b0f080a03170627010801111812030c1b04110702060307081b070501050f010f030804030303020a02070914060907080709 76
    0x80b40310b03009007895054070403941203802c0c8040c240039145c0039445100141625041900500074400c160341c906006001041002a40320503241d80c9030b5045406056103038896480403005400a8410403074081d200342c0010404085069110032404100e96a9006078441e2940d580060742c4c0307a506e1944003401042d80d02400105080541034980d83c00b0302e00501d0385001d0681d0400040030b9070f00c0040103c1214a90800510081c0401d105040c020203c071040a03041c526884d203147c4070b506032001164010b202039080e02d6a86181041600c94509030303281580c48420802c41d480541c0d80046200c0e078402c030305007040d1f0300f4044400d400f00c910080c8c001c0c100c00c5c82c6544d40ca5080d00e058901034002c8410b0160380f282c031300d40c000621001d003030050301c514008503d500f440300500a8400301a003240c001e410311254200700060528007101d04595041c03c0258594824a5007070703040c80038951200030043c0c180181c84210b1700e03048484c00d10508084030104480d80321030004682c242c000f1100b00022a40c4d0720070902 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 159892086 1106 159890980 159890987
    0x6060b0316030b09090c12010213080d020705090c070b04170d0b1905030703170d06060e0310050609011a04080d230304020607030f0c0210110c0a0503070501 69
    0x1010f42044824240c86e004078100e000d01c1002d40e0302d021600308400390140c5482c41c02c0143c0034140140e03102415a00d407484409440014007400c0d03000702c3d0914240c0f45060044000b0101d10307080c01c4440c1d03142419040083e00503601d490380f01021110030380100005202481050300040fa151010006206840400070100d11601c454903006102035200001d80c2c0088039049400c2d000c0715084035180007024440e8440c001240c1d42014004501182c0080c0c4d0320188882c00d80071100080a0341040030200d4200340c3d04680d12406100041200d01045031004000c038034481402031500707907074a0701c080ca080c103410711701030103d04a821030400034402802104c10442150382801c1c0780d450b00e40e0010f2103d1190030402414024075400144d0f007288030f0a4400345141e40a44184030400c01a0000b41400c0750741c180032905440b501d003690342071703092510007141100d0700900200a29401c040066 = true := by decide +kernel

theorem cover : BRFrame.Cov 159712230 159892086 := by
  have h0 := BRFrame.cov_init 159712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 159712230 ≤ n) (h2 : n < 159892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
