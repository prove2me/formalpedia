-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5343
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:33:31.765063+00:00
-- url     : https://prove2.me/submissions/fc9bc8cc-1421-4556-a21d-ca8f9896f143

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 960791366 ≤ n < 960971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 960792616 1250 960791366 960791369
    0xb0d0b06032d0d050f0714120a030605031e0a06023007030c0206060a0512070918050c0603011409280e07140306011710021303020f090601120c05070f0c03030801 71
    0x6013003940c20080307441801c4c8014040c0f000050580000403205881010043c424141c4803a580c04655503070b00300ea29000b078050a12071061030300034420942d044900881280607415510b051038094500e4002540300c00300070350010344140030f06024400f02c9802213400540a26845c41c2c190390101c0b1189402c0a014048582104180080d504160100710099a07400180400c0e2001120102503102c40041c01515101a07504407020b198070f0001b111881403000450368185a2160301101d407030005240c01c0c09580c1c002071085240804000310b030303810107182110200303038019040307110f80801c0300025205043d41154007400b040034a6480c81f5401450006115110181044443e40101001c50a02090381c8110500c22428a4804203c050305802414080d415120001c1c6a0542d00c941800200c42c0c0341811902c0200e00c0354822551640903420440016403181505848000b81c0e88150306292010705941139001003000001c000140014568500005203540620a045607290541c5000f51100206 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 960793866 1250 960792616 960792643
    0x50d1808011409010f1506121b0c0b070504030305030105150c0a030306050a080c0a050411070b04080301050406080f0607050a020102070503130311061206060714150405060a0b0d0b06032d 82
    0x100203806c0d03a0000000342c00c200b194058038084c4060b030002d001140042541c0c804100480440c980c1448005510035801c1e2422030082c0890308440e00c0c2ca000648480c42213101c003c001c0741c4280010010380c0342003900c25001015000a4910713021001e019241080124032045010943d61481804503080c459480d0000d03106150040048a200b880007424088240c85094403032341d11106004074807200d0805880c0007950040280c1c10a08043c034042016400c05d0143c01c2c0242d1820340d00051072440050075200741403201d00070384a80c0c0c4401e00e04407110303407140c880d5109640d000c10050700080e404100905084549942da5402d840c1540383c513611001c030100c2035501c00c00d000d00c8121001d80342c5440403038001e0b13003c86d041035588483d0b1030104071030103040c500440240185000c1e540e80108082000348150301c15404d0318a40d0b44e0f80060342c000c90702c580d011307190010095040e0a00040c00840140d80220000f070842e0610700f0920b601078050285e05101d281c0c80040100400d03a102020003012048400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 960795116 1250 960793866 960793871
    0x60815010902090a030f150b01050403030f0c21021f0506060301140f0919050612030f0d0212041a091f0213050436050d1808011409010f 60
    0x200884484488040c062400500da00191151441eaa02d4910100540e406444141c4101c058100f201480040c071441c040b006052101c121519845038003100c0580c2e0380368982031a14160307902d003261100c400680c100c5103602014039800d96402001c12951b000e2040340c0c010b0141c11149003060142c5589084800c0815041c8024012076030b8801094a056645882c92443d115109000158000b07204e40d88094000404000b407200b40c00e500421030511001403c414003250716442d040c03098554248040d69829001070018864511001c3e00426462008000144c20625500c1c08a5403110f0103a0303086411081c2200d071a002d1000304a2050745c00354140010382080852002000e0200e81c80b1501d04010907400a0050180803003010260090b08020b44204440b110303580741800000f100e10104040c2041c541c0c00300314070000e80ca103201d04a41e401030241201d8a920407080e2242c0c0200c00901e0021000d200c80414a220248a050b0303d0416100b00480f090405854660860304080b01081c1440e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 960796366 1250 960795116 960795133
    0x801060f090603080922050a0603110d021f020a17040806100f06140c0a150b0603091002160b040b04030f0509030a03050906040f0f0801050601051303060c050d0e01050108010608 78
    0x80c4c1c01e034183c8150000c192654854008030005070818203040d0b140f4601c015141006104c2e04070303015030004060741d00c50b061540795624024104400141c03c800300030340c007400384840c803211040b40c554003039554000341c011a200000c1c25950460041c801c91190300340c401b40401c0402101c80c0411504e0303002240f5101a81190f4100001a00211142e018140c103000d80010140c1481a40c042210100d9070001c0540c0c0041400f440c000c4000c480c40c0d0388143c2d680e42001c00100b554030b0480c0840e80902d02003401809400b211040ca070000c1c1d0000300c05440e0484c0c0714100d034008540a40400751003544100c1e113a107103034500b034036001c0c1101034000c050b20308109042c021440b041d1000a1007184032a0035040a54462204200107070b050311031908610800903140703c00149111240003035000341d4a10078000c0c482035848000445103030140304410b01600d0301410342080443d8040c3d00070744800501e0f00d081031908001107580000e5031103501100842e40e56031001000032100a20404000d422850051712000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 960797616 1250 960796366 960796373
    0x20d20040f0501080c040801020c010b030f0304050a030b040f05070608070305070c0f1b080d091701020304171606020a0503040605060901052d12100501212003070801060f090603 78
    0x440d030380141c2d81400001d8000c00c40b0100750710251001800010000e40d07031681c001010b603010300900340959000c0c0c40703811031043c260040801030302c0c1580c0001e415651034503c1e41e00c0d0b8043c9800c0c0508103450303440c00d020150700481c9051054101800b05511100c0c01c909100c08000c0c129040201010100040800044002141080c114022640080c85114040d807583c00c807120900103a40f20304890300c15030000002080c2c00c44c0880045400c1c91441c10000c0e100d50b0441401d03484111002050396041a131589442c640802c091710030310700f00d07c401d800034000c942d9980c2e049a20004010003c5000401080100092401116400001580c0c03508a552502020032812000e0700c400c071055103500038121100160302c1880c071a903c000140004040340b0b07866600380d00d56408000760b400c0541000004141948080b1041c0900d80040015030341c20030391901c4584070007411903040c05010391007607a04102c965041240b030001d0708803040005881441c01011f40150345440e4090a40b00b82418000c0022 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 960798866 1250 960797616 960797639
    0x1d090106140705100509071d0c030402151e030610110c0105070f021c15050103050a021c061104050325090509070e15090106020a0b07030b040f020d2004 67
    0x2101d1010919196005454014107001c490681c1e031443e1803030482001383c2218005920b17070445901d00d000d16605c1d6004c1c1191041603400303d4201e003202c0c504102040050401c1d450701a1024250039207941003120000002104003141081c03540c0001c0d0100500c10507182989440c2c0180c0850b0626420307989011020315118000012003605015020680e002808401c61030522516801010201c641c4202d42c1e001d031045681e9201981c1483c0300310780c801c414001a00c126070591380c100e0700601c2d81201035401c01c9096203e40c08518010800d031000140015041c0c05981035a43c441c085160f220b41c2008107251070714980b008546404141803802140030760300014202d09a0307940c80700104141d900c000b030f01450000283d01007800c4a0041040180d21385042419000c0400115003800d402d981c0c91008070b81c0c1d01081c280252602d14580301051409000742c0c003203807031443c01803c045403c1800d03002d4202243c10026240c0651900c85126120000b6141220103c0781e003909240c40c00e0600f080d0b0201c18 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 960800116 1250 960798866 960798887
    0x150804020a14030a14010903020c10080105041505030a06061e0b030a02030402030a05061503070501050a02032d0403030801050f0909030d0b0402090a2607080d05090a080601061d090106 81
    0x801000b4003061031450b46050152540140e08014500c4080c01c00302d8400b0b000341083c0ca4140c006001f100200c103542c1c41c00f00c071028614195580c0e5003032980d092400300700c020103001c0140098900750f0b020011f0340d52414003070f04007a24001c2d000010060315001c0c1010901c00e00a500408441455005002d100220801d0b81c2e0130407810300d00180c4035641c82c80400c1c034003401341c40091302a105400411000c08260640318402c540300340d050f114200d684000560300c0d80a42d200c075002681052042c400403401d03012207051905540c401c0c25015500311880c0f0b42c81030344160400d500040c00c060043c800e0f41040c0e40b03803440302070341503a04040345d01d0090810ba0b1240503507c2c89015050322008803981658543c2c042c2c5101d00e03c010300c0794988995421110503000504039203220408410a00d00c0c08403100400c02d20708a800d800003030403202110401c04c44046d80301d070750451390065240030045443c000c1000918064800f50720303640d02c4104d0070003488c030842d2468031025114280c00001400200c0c0d04c009000c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 960801366 1250 960800116 960800129
    0x10908070510110102130f03120503040809010f020a020636030304030213090c0b071101020d0206061909021902250e07030e0f1e01050610200303010807150804020a 72
    0x508180f5050343c00e50180c4a01d0301e07450000445407002141a0110081080813240701d50302e60340003108c2110041c3c8007408215030180c0340c258140f01c3c0c001d065000c5d944025000b036880c41992183c1902d94001101350b00265450768510f0000c00581403009183d04c14034400c1d080d10505414481c1050303000035500d204500000b4003c188800051510300700b15004841c44642c42034210340f01540741c034140010b54100d044180c0341070600e102c000e5025400460b007500781590311343c0904180e0b0f80300400d00140d42c80030041a90445080700d00000c2c400c0062010b0301c14100300e00d41401c4400103c080c000c0c604a903100202038064110303204004c15001d1100c0d140300700e840503964290aa0b44201c410703001008150713103000241c0110903480320700c42070200e00740100e00c90740860504a040030042403402c9500450b003032504000600c40c0014128003419a03c002c00460700034485201c1740344102241150401e038840070503540b0884052000c2400c030032101c50a16443d16000525250940000b003040ea40d620503030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 960802616 1250 960801366 960801377
    0x601030816031206080307020f0d11150f030a0b0108010b0f040e0a1d0705010f1403271902010e0915010c231e0a020a18062102010908070510 62
    0x21002c0601600d996402043d514a081012603500c8083c2074690b032040d00201e02c1980147d09158080c9002484401e0343e64000b841042c8028182050206203070582d07001e54408841806005082491580210b01c596084c1d040482d54601500025001082c180c1014403002c40c240000020949900b0641d42241e0f845004905951102d55240d401030004108840c00d00d480300702116000d4070002011000c940080c1d07118460141482e500b00c1d0004006034444d0000c100400100301c10010748000c0c10120b00e500044450114510040645040d800303082c0d503150321080442d100103543e08181c2110105e002518220340070f140a0440e004070028000015061207120820b120611070190903400511440c480f01302d40d8042d0141d40035030f655036500303089000f000380c00d0912003016001003402d407002503014080b2007140d420072284000c020708054440104583d1071000041e000c84112504031b612002460414210459000042200c0b12941005c003043d808030108000a0311164a4000d10888030310b0306 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 960803866 1250 960802616 960802657
    0xb0c1e07110a03081b07050627180406050f06010c02101103031503010506032e090204022b0509070b0904020f0a03051608090a0f080d0606110c0306010308 68
    0x8a0300580004010782d04a1040035001c8100503011000384044500c4c2e0103414a41d40b503c24019950303a000d030140c541c1003801440140110f1400c0c030344c07400c902e40318054204210701c5890702196000c0040111902441c0d100c1c1d06000622042d0710840f40c004c02d420142180610f42600081c0002c000e0b088024003038440c50307015440c40d034400e036004408a840702007a00da9900306100e0203c122105503480c00d02c04d5103081c002c2400352030000341c0d03110501c401c0f00d65143c1030910030300804154001c80d440b48021585030090070300140e03614401400c068000c202c5100b409480b50743d0341c0030581203880042e800d051409081c03007000f610010300a81110422810340c0d6840d4605004500640140780c1d803109038031408a840f00100e13030940c020768420b04c0841010110b12030260421903402e4000d0310300341c500e40c02c020b40300710204800415407203c0c5402400003a00d0442459299004c0311200d82c0000c3c00120004d00400301d40c90705224030404120218010051541192560303451481006608070840116054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 960805116 1250 960803866 960803873
    0x2120c12191404080c0c012c0d150510050108060d020f0d0614010e07020615190506070f06060b0a051207030b10021c0503070816020f070308070b0c1e07 67
    0xd080c01a4002d40b03021260600d4030381440d0b55004005409107a000300401218194450078100211124501c0d5030b00c00da81080c06a150480750030114550040c40c401c6554010641500145a102c50304200008080c136113503104200038030043c0c00080c1004481801d08c0708903079591a00c0f141d140d404441d94800604800001a002014044010019418080911310032041415200d04882c8101c00f8009039942e4807408a03100c0104039040c504903940014114000c0c241b1a50008440c0c000c0782c03907400d810ba11000041e8a913000301c4012114200c401001c0c104100301070044c48014801200b84a04081c09034030054024028200d056141c04002c1c00000e0066220390081c0048c054060012250702e074401d40d009440c2c8501405480c000d505150400c0010b610030742c1180d105807001d56035204140c82d00501072a194480d010510f0451060000070a000300051200a0041d81300c0c000160382c49071941f604201490004187c010f07210030a1214200700e0307400302e4240d200c84001942207581d480f001d24 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 960806366 1250 960805116 960805121
    0x61a130507052b0e0c060d050c0d05040501020c070609182a0c1713171c031a0d030e0909160b0d0b09060a05041a0d0602120c1219 57
    0x14103414030380007030038150340181c0c04050241d565603c07164410b0008010100358180d89030360303800031079410074400c200860308410540c0c4000c2e004540b210300c0c00e00e05141462540140c80d000e41d4181c803580d40c0005c5c141e1120100304500d10051036181000002d042c80c150107841000354038503088000c40e0301e0b20b0255080d007200b08960411090411108101003910b40350051560303510700d104403004142c280300304a40b034612a044d80d41010f110000c01c0451402e00140301140c80581c0c28242c100d1260b1091030075800e69509015505070001c0e50000b42c00c44030558101104402c4012a500074040c220407003011070b502c8460103907010019501200c1c02c0e100d4410711490701407441500b8419070080040403405c00352041c01000c1c14450035400b84907011201041100201040c5c034680d5010b5281541008142026009107480c520420300c07100c0b00715011000710b45900c1e07003600c0445034150300055003442445242640e82c1c011802c0c42c602c900304080f201c00c0301c91070741003d0b104181c00d2040e8405c103411000140c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 960807616 1250 960806366 960806377
    0x15010503072304090c030b0c040302030606060c15040b07090e0c2a010e060a060b0a020604030807030e150402090709080d0c0c080a0317010b0906032e060c061a13050705 74
    0x241013000940502d040c01004034543d400116074a00b4000045440303502050291802e0f207400401a003065102c1d0000c0010035030040c140c4d11020b000300141030fa40b6100510200380300b98000c0c00c1203402490144401450156250028805d24500405105a03160148280d4142e00104a88045c1400d50481000382007182800d50b5030709507085c40d2000400d4071000c58207a0050000c001c05000040e2039040c4040a40514009880160300075070004010910a00f01141c02c105c9600f07000860201c03004515080c880206100082d0700aa0424002107052603c80d0580c000114a05801405d041400703998032400996882001c0005001c0f990050211151600006100000858840805516001e07090b0160309100510305000076000103034001c00d90003120820500101254510b0742c80001d6400840c400700340807920300200085054185a0381050782e0040d0101c1c6e11644180442c2c1d1a00000740c07004a001c07500b02240400180b041500c68010071a0301c00000e800c00700745542c484004507003e0050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 960808866 1250 960807616 960807619
    0x3060e15040224270d0209061035070801080712240b0a0509060d03030f0609091520040b0d111b1522030c0b04060608150105030723 58
    0x840c0034a001d83c00d22601450707803130f0742840d410f001400402c2000349254080d020b900f14240310006040d6141c0a03114901c00e1016003440c0301a02c0700a007285080103040e00107081d00840c101da4852920940f1380da02d9034084003070320301550300358107050541391240c006100b07003c1c0098414510a00708080c402444102e01c49c460400c2c5440304451603180050716881c418280a1505030101142c41e0801c00962449140040d105120032440c0b507604400809854160002c2c2580d20000030450100074001e0301503041c000c07680e412148140c03004080445610460969134800700c3d41c1400c5089203900d00b035074219200c81d40601d0700c54000084842c05070007412402d04c2d0042002541c40b011410503020303c5c0288101208032600c21810682d201e801d59401c0c2c2e10b103905094a62240507510740e00070708071401c06100340b030110343c21071503652510270541050360b080302c1c03031500c0f40c02c01d01c504034080195182c80c010142c1000310b02d5240c0030110340c4801d20742c052034010110700d2802c030413100160301400c0c00b80f900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 960810116 1250 960808866 960808939
    0xa0216030f0e1e01080703151502030c01091a010b07020a180e010903020d09081b0d170406030204031e0b07030e0c06070605010f0605041815031b03060e150402 70
    0x1400c102600d03c5a15400482c00705480001146600b403181c030601814032051240549007d041c00c610031210420b0b8078424003144010030050802da107081c0908100240310301072945101d8031000c02c500c640b00d0f05811881026030144100e030003690319101202d04803412100c03000e500041c0d143c21a00a02103209001c211036081913444400c0650005240808600564480710b8240d01c074011103440d481c1000d42d4598400f11552400d1041c68100c2003201840c1c4500040c0484810100203280d03250065070012011960101d805c00902002e072032400d4a4040741c42801c5100495a030b603050100c0400740801040603650030030144001000c0045070035100c0001c000d9505c3d0810b0346043c50240c1800d0091054408401c2c00c00607450b401340050701c068503c8281d1a01d4520824041e880c010014411480c468031010000000480e10840b00d055414607211400c6940a056040c0342c01034484514044105920000021008200104420345c00c107034100e841c0703555580e400c10b48800c1c0d4940303021078240814 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 960811366 1250 960810116 960810139
    0xb0d0204090504051029091015050a0e04020a0c060902040f0612150e0607032004120c05060a1b020303040e0c0c0f12030f0601030e030f040503060a0216030f0e 70
    0x2000170000b4040d03117483d4080c802004c0100148000104d40701000c0001030030004540340034544840c2d900c0c0d028203400d4070300310802c3d60340c1d01c194150400111014042400040d85c440e500d0340c840641582c07050309680035881c00844200040000b04941d0b00944071a54810000c0110358880d00440d9400b048001e0a001240e20780040b01010b40e41c441084607000008014040075507414024100d010300951301a040b40ea440c0b00d01500a40039032080076500c001c50120f02c00c0d00ca191100039101030034007041c1541140100c0c0c0b900321401003c64003c035201d00d009114510040c1c0d403100b0802c04040c407010301c44280344035070300c0840e2a6000c3d50700b09880b030101200400c5007107c80034014040f0b030340d05441114a40903100c25050740b03a00040144090100040000840702008a441c030364000006150008006401c548064295003101c800b000121030000350410980c50200b200755040500080d0842c030f49a2a00610041016200d00007400d111031541079107070150264075211120507000d0034030300004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 960812616 1250 960811366 960811373
    0x7090312030f2405060708041a0903060a0b0a0603020904090b15090f0405030f09030c09011e06110a0f02060f0d1b020c010806210f0609190c0b0d0204090504 69
    0x2009880403034034100d49000c42d007030010f40c01001d10120240e541c0390300b00086800c003002c1c803104d80d20490043d0341d0030b901000000f4610454003010429014490440d80c0c07606941c504043c204400a08554143c604000903454182e90b03800880d01210003d040040e607400320000824041c1c9600d003000f0746982031034020800450602380116101d100c0480389110a81e031002d5960f941c0e01c4d000c0e1405451076100740291041521180c0091000c41401070446455a04410000f18140006d0b0081a100e80aa042c5841c2404141c01684041d0405003048840e00d560400b580742c0e12070050780c000e0a0031000d00c1150382036403104070031100258051030409688034000016403000c1e00c807491003110300c40803480080309005d102003200510b03e03030140c0d982c02031a12100c081040205115144018000f0000100200c041007000340d88141080c01d4068061031400456041c00e10007401c0ca80b20300003003420752540008524a8084080e21800c1200e1a00d0748101038000c40203004c1c54001c11a00341c43c010910050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 960813866 1250 960812616 960812621
    0x2010e0106140102010c080c040b032206140a1e05180615011205010b160201050f0c0a0c060c0f08160c1409011415031b12070207091a090709031203 65
    0x3924401e13002170140074012101200c0200048508441100b8140028003000e444000103680159481401d81340038090510041c1d51520f22182c121019543c80c1044406c09441c290580e40c01005000100495840901888001007240344500c0c4001d968100140c2d02d03035030011070507004c001d40c5e40407605a40750043c018804038250035002c0d40442e17804900504001498003825050780d141242d29814529100c1500b500c10844034800c80c10b000040c000b00c07015030b81100150a003007903914001e000b1000c042c10309240d00d180f02c0d0861420016422041d00104280c003100b0440c00358440c604035600c440749000036002c070a003c40d009001d08103085001443c0c803004048e4500c40b010444403030341e41d40d99807011214950b84107903080d50010181a0311085012420001e07640c03222208890700e1900c28800748085807030b071100c070101c0c8108444405000c102a8100a030341c016040080041126415920f42c16880103d090522403185008000284245100d101410010b40d4451000403c44114003c040c02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 960815116 1250 960813866 960813899
    0x714010615090902040f0b09011427090105181003050a030801091d1002090a050603100612020c1c05070203010c020f01180206090d0c08030f0901111b0f0102010e0106 73
    0x3400b54400426081c0840c82150125a41d0321a090210742c81c000701c041043c0c00c40c10100741445200a03e00343c001444400500542c01d60320304074090421101494001101d805070800e0042801c1ea006011341e03107410030034070701107006502100480c4c2d6458050a4034101071b600001c1081c000d1485800405400140c003a058580343d010030303c51000e000c552203078a00c00c10600800c0951107042c1900400b04598010295184044c000c90107058540000c11455401500c2c1001c0c8160400f41c01c00c1000e9000c540302480300280341c3c081d0b20340005a0001680d4501c01c401c0090480202c3d4180356041c2c2c01036040b244e106602030001d01c070748002400081c1d2102d41114080780c030355003040d48003145102e22066048070a5030080c03130b86040070082030602640360130400049030071048100010a09140400180900100301390035250f41d234003800d0004040c1028500c1d841c002d5800032200012404060386503c15040040d01c4c50010341060300c00403170141c4505141c618a552900b100403503100d206900000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 960816366 1250 960815116 960815159
    0x6080105060a050d0c230415030204291e040906061505070803040602031b281119030e0d0506060f010c030f03181208190c1407140106 59
    0x407010f079455042c41010700c00c0e0303030004155155106046c08802003503181200c0c0c0314820184000c3d00004500810100c0b00b11011890364800400e80c10030440c0b80c503010300c04044500070102e500c40f44140b8428075100b0f0078520218410301201d240d07510080f4003018455190b030b00040051000c02070a090500040803680a21076088007038200a1003006d00600443d00b41c103500000d15491580d503a1a244006e40010304030712005d03400b08418003504412403000e0103543c1d144011030702c00100601501028000c410540070144006150325503004a00828500700500800d0340003603103602207150440b60088003081199010803030030722100a100b00060254451401502d000c01d910304060700558407010044030040009050300085031600340319800c401480b01994800155411403030f5610000040320443c802c0004581c01d00b0006a106011120400ea001103030703041148801e003d40040c01041c00d11880b1038070000c005250303010851040c009811008042c0300030003140381c840407801c11000c412328881 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 960817616 1250 960816366 960816379
    0x1c140604020c0a060b15030c0406020708010c1d031e0d1403090705010f050f0703111006030819050c0706020705030d1b02090408190201050703111603140705010608010506 75
    0x180141401c0c421034008150641c01000050b03a80d913508006485580001ca03044100030340301060200c0000c000d1401444001c0d001074030350f81807403802460040b9680c81800c40760704040d015080b142d040034441c1201c082d0101071000c240b100c1004249080d606160041d1031a0320294001b210007804101902444255500d010b21b048000c1000300040c041503411694a8108203810040340d8000c840400c0840c045050150404000b000f07500c0d00d44e080400240c1c00305400d1a850109068240510071484005003420040141191a0300744107005091034142d900c070500f130020f50468050f1003a2800b01c550003040341d4610f6150380700203441e041c0d14400c140c0288a0680f4155140b4000c0f40c1c1c2d070a0801d0f030041e40080c114495001c10051180c0904152a00642008007800060031110918050f4800e03400200f0142405000113044a141d450195110720040c400e030000c04080c6441c1a80840d01890011b2208a03206e030780d00014450100014242d6181c0b900c0004c50840640041d8451074085500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 960818866 1250 960817616 960817621
    0x5191103010e06060a0b070f060203130b092b0e1302040311120319030b060c0607020706020718020703020f030c06070e1206180102041d0a050709210201051c14 70
    0x35540780310a85034545c0c0720541010502c100d0240e80040c046c0c01d40a0201480c140e0b100d92a080100d80c01541d2070482005100081414072102e5007050b038000c140000104201940030b000b02036501070b0003812003420100b141034400d0051049204c05407901d00204540e190f121611400e030001e50051004450491480d49070401c00e18004064070150390f007400c081d45c40d00e14244000c045413602d030380204c2e062582e00c800c0d4500c542c817078501800341054590003c1800e420221006880d02c48154004000c55000c000d007480381d444145010540460a00c0015845803002c0c03600341e00341092400003100e18480490401040000004c44501851541c1c0301c40c1c00c89110242480310400884048ec542544860301082e003c04260012454200c01040014249900c66111000300a0500c03030303e4030300100030360600c51190941e00ca0550001054184403243c945060880440c20080e1580e800c603182003542203000b5640654122502801002d00c1d00c809890b8149544008040c0d9448058451050303500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 960820116 1250 960818866 960818891
    0x4112a010b15030a0f020408162c040f02040905071802091c0f06021804051302010f08090307051507020c010914040207170d0506030d090f060503040519110301 70
    0x54440c080c0000761202c0c24480424070032126075800507001c0e20305150380c0c16100703c0c40d81d404e1000d40090100c40d8040d10aa5450702c954103198022a00a89260f440b050480381c3c4885028a000c50b801c3c034540041c511580d55400c03c4403003920f0040b8003940060818032150104400460442e06440c24607039186400006224200200c0c0039812200b0303000b43d075094502005540c0b80400d02c05440c0f050a05040d49031080d528a000c2c1c0c0c0245026a20b600061151070605103454000c031a4803122a070301c0040390170480d400007400309800e040c091041c043c103900802e400032020701c116400c09400c0300c101c4840c1c04be4407100c0b40d1200002c6030407500600690711040017035031103004d540045850362f0a850381400390701c0081200a41c0200ca00310780e800c40d0b003074010080d1401900030b0711003105480e000044505d400c00c00d0500f0441181d80c103008100d0744074014450030326540c244000782ca00d640b90882c1c69136280d00c1e00038030305108452030a10385007102c01081c0c108501402c84c100710302820740c002d1201c1c20141a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 960821366 1250 960820116 960820121
    0xc09091c0519030b0f040e03040501030606030b0d02010c0f0c060906080a021c0203060301150807060306240f05070605040f0203120f1b0304050a23061804050604112a01 74
    0x20b8002400310032400c0b022016031003070f006109003071001001c20000b00b00c842c0c001002c071020142100040e0f003011800f0061076805219440003015181414080420200001000c43c0784110b0001d0602812641c00e805100001550f040416071107107604500c6030b02ca10000d0a03102042c400c101c00501da11000403841321050007500e4164040c0caa50b0301c2503c030f49a15100182d0030050481c0c1c0c25643e140d0a80b000c8400108502004100307203405880170500b0084014182c403996001928050400700303004c3c0e00c0701400c2c2190600940580340c2000701c20170000c0d04030b880f8807502001401c007a08182c00c1c8002d0002108003000011f00c00c070102c0e66120b04040f003521840c0a039413041a443c0c44140f04c1802010743c405070941c190110002603a1800c6d4076500014144105a00304101c00d24a40e08400106030484007040c3e01a0b20071114281000400c5001511029035080403600032a1a40301089c0344d44c45540140d541c0840c011740c00d5072a41614602c169101070080d49044020380c1e002d02c19401d441c410b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 960822616 1250 960821366 960821377
    0x120103151b0c020d0201050d02040f0f1a070305030a1107061e06050d02190902040e090c03160506181224040f030503040c09020708071a01060e120c09091c05 69
    0x80d142c507090340006070204a030742c107981d80b400c0e4180303c0100301807400c032a42d910040c405407911207500c0c0025070414207035001d03005040d0040b03c101595092141c0c141c1c0b0b411000e42d0121a0f0516000e0b543e50303980b9800758050841c22498900300e0001040000810813075030046408041d20404901030515405407100540e0110310070243c000940d1001100503090aa0b2403c04009400324501c61580d6102c4803101282d0007544074804224071342051150360a0b0038030418000640071001000d43c0b4264544c05180c2c2c04051054500c90310000a04803140468101818000c941c02422a00005440f040382a122100448004420004e40c0f11078420b08003144417080c000c1c1e40081444020f403405607801c0d00c0303561002d0001c4d41d40340350340c401c0047c803d01103000074000c00348101c080f5a1941503524041403041c1d20101c11110104040c00107000c17480d030001c40b010178a10100e40c1e042e0103000c0a00514100104010081c3e00056881c0801c4554180000c0e585075207003400f62142c90135198001c0032544d9004a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 960823866 1250 960822616 960822671
    0x60f0a030c0e0a0b0a0e0315061807050a0c02030f0a0803100906030c0504180609240c21060b1201080f3f03180705040c0507080f12010315 61
    0x80301810702000403128080e0031800324604102c000d006d104000640340000090344c0b1400c05005404000050900b400221001c05841e40488010708180c0d0700688280620107103141001034074603484065503800c0003c030042c883c40c20140c2e448072140e400c002c2d10f03691080328034a904801c1c010700010b50b01d4040c0318040c00c0b41d4101c143c8403800740c1081308100c003030007010107000300350003060580c1400b1030347c0da1140300b40b824170030f80040c85500790040c0e178000e840001120900030300d442d049039981410b4003c1e1281002e440740b41d030305000e00641d505500340148626040000010804180b615451019580580c140d0314100c0450780d4010030054141c2d41c8208400d10310b440f0142d502048922002142c40e20458040c940b0740108034200307004248000b0350821a080790340000c804205130114402840400003400f005e8400744400d10344090007828a100e0b641d0700401d01a0001591061076040c0400d4500000014001056550396070400d0b042c0344030660304c06d4020034680384005040b5244d820890780103116 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 960825116 1250 960823866 960823879
    0x1050a0503040210090e01060507030219260c031303021305010506180307360606051204060b0d03020a05070509100519030b1e060307030206040e15060f0a030c0e 71
    0xb81c81e800d200750031150301418014031032958404a0103c18200c1514040c040c543c2e55076403204106e040007890322050000081c0003e07011000c40d40851655244402c2241c0307400400c49104404443c00800d9225221741c00c0303918003001c80c0d007041c4100c00300840030171a070084030030b4404044801002c00c1124003e100d0705500500c200311504010b01041201c02c4c00d414010f05440d0b50607582c1a042140200c0f01d26400440d464092210700028284068110703414501042080841d0809001600c644220050403c40c265014005010800c60703412148080030b018180d41110011450b0280d900c8020b00030442c4c4038050140c0118030f9052526140e40300d6942e232800241c40d940360505024842e80d421402c004219200200440492407a0701d00d180110b04450701c940c4600801d5084448082010744000c0c86138005000400150307541200b5102a039480d501110764548440e1010004032040c1c9414035007049001ca640a00a0355810150074016a207484c00d001c0d151ba814000c980c00c1c40040c90440d40002c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 960826366 1250 960825116 960825121
    0xc022a120f06070f0903060903080415090309140604081b10030c020606010f021519060b070b04080a091509030c06032f04090e0f0708030708121302121b01050a0503 72
    0x20701c44c40040da61410f00e070602a81c49600ca8840c0300c252040c038401900450100c800340000c01c4212008103080c04d1080c10b04000c4199255001000480c442c07180c44400b0a0140c041d80c0c0c0c954a900440c3c00900c40300c011503c071003c0e19100c640c41e0410215005204030040c501c8004070714000c1c01011699196603010300785681d910070056403403590340400c4034114440c190925201c010300c403d4060150220340c035a01d05c44d80d14a44d158058420302d4200304492882442a840000d001901d070a1300140e021102c40d480303059030310b8212402e40059120107103103940d0b06040f80030203400c80e03c41420740e806805003c0c5d6589d1120307002d905442c0c05020229501c0f81608000c3c05941c0038415026000c243e007080c6c1494950703941184400d5402d0850a41c11307581006100069405040040c140106051070196003000019221001d560050290f18210f080c00d000009600950080e2405003130b80c1d00502c1c4100060030711421a54030100d255007207154420f0281d846527558003803405c0d1381c180482c0343c4d521851035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 960827616 1250 960826366 960826381
    0x1101020316230322120b130503120f0a05060a0509060d030e03010606050d0605010c0308040b090309040f050f060108060d26040e09010f1407030c022a120f06 69
    0x100b01e80000303444044000400644081040c8002c0503054100302980400d84202040b138041d03100b2640c09800802c226140348400a406449207503489180701d0f090081c26442414600d096200c0c07440c20540b102a00303000c0000e04103200403010300850f01c100c000c10041c0c3d540c4082c0240c00c500c0e8080d49a0280c1d0f4040020801c2c0360142c1c841140724400c0c80c00700c0804003c440800d0030b480c11504403c001c6580428510004000b511444e0010102441c08000c454902e882c042d007070042c06000988813056202c005a4010020011903c7c941c8001d48204000c0d1116014078000709802d4407881c1c1031408040100d805036208080e024007a00c002170004200060568480c1d501550b200b6400318003600d03070700c008100161104080c1c402480b0401c81000d451501164003800c440340e8882655100703250070b003007595040c1c0d03003080f081d400421410000340042c0d203234000740e19013610702d0b40480d100e132640c11111220030203004000650a4060f1101c403200da8002c121507846c2c00649121542d19401400040e404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 960828866 1250 960827616 960827633
    0x120506180c090f041a12070b1b010207080d1b02010c200118080c07090510050907170115030b010206090307030c03090b0c2d06011806051c1101020316 66
    0x1490700042c07074a40303a4450840401d091780d43e9000d00074031104018a003450310341880940c0c0012061440043c202d0142048022100c901078092440480b038912038560358007000943c100c43c1025081403c04d500d40205900b91405410241d04c2c8541e229525458050311500501034407058502e16210f446440c268504600c2e0000080c40c140b8004c1e40d00d88031140b204030070361f84401d1101d90181080c02e50701c0c00741050391407400405612104000d8a03020820903c5d001c143d00203c1a10011100c60880e0345409008680700b45030a2004203003104604000511084280c0c80542c00311520f440c24010003811900580c0ca9010440b10b076841c540041080f203000a1096400c0c00845100742402c1d604c05441c0ca1040043d500074801c4030540303903c400c02a08420000801d400d03840d14000c841c61604003014003403036465007410301c0341806003d030800481001ea000c6820a6000e820090302042c00242cbd0f8507100d4842c5050181d054a10307810b80d40d01d4403000d5101000b196406000e90f00030b0011001162b949244 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 960830116 1250 960828866 960828877
    0xb03070b033c01050a08100c090504051302040c05090904020423040305130b210615160218010302091501030f06090c14032a09060a120506180c 63
    0x19000c8051070101c0307026001d45000c150029418041d440d600280c9600b85800602c1038200911510313a8040801821b88009203104152644d86408034000c420b01c07200390f400e00e080303030001ca6010781498100050320800da83c051300c105d8000c407414484604006000e80b0107101e51080150080030388800980941000c0e00510b0980f000b13006040e05201c402c0d07402300d20508041c1c5049001410010780190100c1c1500c0c140c401800f0240c407441c2c500049012140101207071610144060095600012015a03400e0410450315000020f040c0c3d89103004543e07001804c05455080f8840c0d0419940030070040c252000440c180c0341c0c0502060403503121780014140c100b40806466040580340d8210013007815443c083c3e03e009245007030001c04e410010007005405918000f1244404080500810a2505d0008200e03400c4c940e1490081585080485c50103101e44a0108a90f4201a00280e41c1c000b49600c685503580c203102c080c20410071b41d1035580420021065681c10f00910710905c2001c50b01400302e0704010305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 960831366 1250 960830116 960830131
    0x6060513050f0a0b0f0c0d02030324030c1f0809060121050a0c0f030506061005190c0c080f1c090302150c0d030e0f150708040c1706010501120b03070b03 67
    0x24590b6950710b045585540910140b464002010481d0800b03091b041040d0f403081719280c000f55055103890554030600f64200c42070007841c503801c401040d1250700c05100d91b05946201801c4064054055160486407000e0910844005115940007558985003c100b05042e5030001c581609454855900311003401c904032002d40765401003240381d0b40080d4200510500400c515810041d51603d03500300f20f41003000081000b0300510344200d04400c0641c0c0103040701d40c000314807460b0703a51400c0514412034008032403100041042481501c0403980b410300042400490404004884490261000070109500f41c50685c2000c03407891401800149003440d0100c2114100c1c00c070b0300c1d08083d1100c110520b07000004a9001c04681d45040d01090b0800c24080d0782440040c44004183c846c2c07030301907100400d05000301000d00300300850004c501004004070707154005011464190008081e80c0c101702c1c2e00ca03d0288a2a408182d001000c5200709440713004030303481c0100040107072904038071706202c84146601c000e00c1c41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 960832616 1250 960831366 960831379
    0x317130803040807060516022b0f02070e01060f0801090c081f03020915041d1b040b0310050406050705090f1309021801060e091510050906070309180e030706020a1b030e01020106060513050f 83
    0x8911402c03864006802041290e44200300d0110000d4046c00030541031300900c03286420300042010060300704022540008480c90b0b4104801d81140309900601402c0d040294800080c20a02c920030506485095009004030750410000c0c07c2080941c1c81d10030346171444041d5402c12280350310300d401000e0410714500b4010340701040740003030040024240140304090080c15640c031030901081c02828410280d0014407410900d00e402c40030b100203009004644800c600c81c2d40300509070311076041c140d000400c2c450342c05052558004003c1819985955003401070000003805241004c00034502920003038001e109142468424a442c2003d011070742001c104a9402e0000410210f59503440d000c2c01400d0b01c90003903848401b02401d0003c0c107068a00e110300d45a8100f418444c05a0b07000c60301008a4580c107501940040c4e844190075000c0d01e01c180d4078819061803081c1c03907000009140c2c11940d12035a11f20264000c00065072a0b40054402c0c1c01000703021440103031303403420a00140c10a050b41940000c00240103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 960833866 1250 960832616 960832619
    0xd0918020306042c07061d1201020706060f031a07080411181509130b010e0a0b090106032403030807390317130803040807060516022b0f0207 62
    0x5440c410f68180b044114080d1310030000b9003d091042002900d8640341c00c607078500140c10180541c84941c024a031081082420303001540d01e00354125414240d000d1010f10080e0359a004c030342c2640c02c8500c8244c44035550728621486102d100d1203460f10540d00350320740c20f03526265912200340741c0c805503040d42c1c0c10402d414088603140c51070071f445900c03405900700d50040048848060004510002c2e1070402c941107118407050029801c090a00d043d40d190f888180115561840110060203191205540151041e000858140d038507820126404c1c0742e000482c00541d4a42964440140a40c80040c00040084020410b000e00c100e400c415006000b441d1600c8000c0c050502c07a040d0040541040c00011100200300c0070590008100402e60941031003058541c80c0c00342c0520461028900010a40c404c004000b4082115607004d0b03d10140d08100c040101d403911940700c44510842d510349001500c504a855040110301194585a18030103014240b8501c1c8030034002e4a0020051301a18158001e40c40c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 960835116 1250 960833866 960833891
    0xd020a0201180b0117030702031b06070606090606090b0702030a0b0702030d0501121110080105010c1e0b040204180c03021e0d08040e010b0c060403210603080301080d091802030604 79
    0xc55031894014010400039500d003c181c10702281d05c540404035940c10134441000903941c00301d8040c8a52401e00c9981d0302c07044c43c1d40f002070590700c2482002002503150a01c0860901095804007058907203a840e01c3e000075440b60101c560900444500035030541c00a50090001502440256040740c0390740100ca09250075402d030b035000d90300c0980100c5030301e0181c82416402d02009111202e5081c37070903a8615040d00b0703907440040c000841402000d040c841c409041c5000c0040d45580d020202e241940c08441310b48a51400425800099509920440c189040500d640c04050030040040350b000c00521f841d94515400c3c81140c91500c41c01c02e41126074440510200c0d200e002e1514510761088404603555410101a10030055040c1c0004000d50400e01282c58940c500080e1f982d0030a0b05810700c445d1600c4907040c4803002980600f51184010b00f045000001c0000c0c0303d019506881c1080c080e1000c1c0042c1003000c0314130139010b200b0207100d4003040caa14901550b16500554000070090004503c0c0c01c01441e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 960836366 1250 960835116 960835151
    0x11409010531020d1712060414191109061207030509010209010e090a0209030f0a0314120c0912010222090509060622050c03070f08280e071e06020c060d020a0201 71
    0xa0303911b445c80c081c040092928244c41407510b050280d008400b0300d828540604218000c0c0002c04440c003940e10706022400c880500192840140020003880da6480d01e00a00f0100c4d0000752034050101c0d08250110f69090030600135102486010383d075400b102c0d14424104000700d00d028101c2d40b10030390708003d00f07e2162008c1c00307015200403441000f040440c000307103001070a8010404040260b07000a101c0d54100c0c00c15100950f4000d2900403160382c84041c010b00040c0c9044510244070410341c4001a0440440f841d008a804007080c1400841071880d600c0c4030010035200112141900344c2c0044000408a1901d51903c1403405400c107121070445c0c5042d1465411690f00f86c030784030f1103218080700300503a066000c071a4041640441c0b801010b0b901f05020300d528032103200c1111090290100c00082481d01465010000c0001944100c1e1051543c0d500f04580040c1510a811241e8201c10b034046541ca0002034884483c2070701401c05490500100e80c00300084d04460008400c55407640d40c440c00080f03009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 960837616 1250 960836366 960836377
    0x6040503010f050402010f090803090609030c041d0d2609030c060a020310090b0312211e010e090c010c111008160318020909011409010531020d17 64
    0x42d070001d0541094000035007150112049030b010800d903440d0a000880e0044182e4075082003d860454482c000100002d050003041003000d6000780c501202c521103441e00810002026080c6000d0fa0002104031100f2500d16410b08018a160034100c0e0501090000e203803500d136405922002035a04200c0d442c080a0b0a115055a40c0c3e41070302d40100900c0f80340805070310144014000c04008100c1c440d050030119890b4600b80200086a20740415040307c0d600e41d095608026619840140c201c81c0b4016074440013503440051500c0191060b940040b5140700d102c208640070750360120060444103206401145d0303100c1e0341d10084568407c0d4204003030301c54032946410003203141c3c00c3d2681d40f0245450400080f03502040030703914007018281111407480d2040d890b00000d8083e01511201001c0c1d8400951a015281002c030300d25019110f5001c01005800c1948203074020220244c4c1c4c4140c000d600c02c41008031501d903e0603641c500820740164001468886c40c4006040d118030024000c3d1500748000021700d4002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 960838866 1250 960837616 960837641
    0x90509010f052724180a0e010b0307120c0e07030f0b0922060615080f01080c150717040b04030b0112170c030c0d120506010206010b03070e0604050301 66
    0x610180520b00d46000c0c3c0512111012200c610030000d5070545140b6008003424900800022203a102c00318a1682803801c1d810748040e2441c01d8081240b82c00c40410f8800f00c50030110107280115208190300180035104401c0b40060050840a0074800511440541103104440c910300c080c0f000030703100c0f1194a0440c81078101d51000600385c090b18007480f040d204030b256920f1041c07071030724200801000044502e14044201c51050b4600390700700c2c0380000040041d50810680c4203880c80110510580c007400030343c0314441d0452444040d0740d882c030b103c681e10807441c000d0561116002c0898001d60341050050a010b42c059414916815107c1c40c45415039409508a091040d42c001002c0c03040c0120484080d00604a009100320350050703d07203034078000609020100d820854000750810312610304005482a5014030b0701580c901e03200d0450043e108165016008208030305100008446600101d4041d0484603034040f22461aa03a0050484000e16003141542e4030040074000483c003924240700f4040791000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 960840116 1250 960838866 960838889
    0x40501200d0c05150c2b1107170c03030a09061d0303060a060819020a1101020f090f0607050a140f070b0a03110a0e1509040f0519090507140109050901 66
    0x505082207810030207450303000c1111220040c01e00108005c0d48046170500840c98103000b6103d02c0c01c0d102e102c45100d8126a07400903d007481c41d400c030074401d4007004020440c4100c1c15406008408200400705000d401e00441c03054005000140c4144119000301d05024070915000803d1282e261480c4024199006000c81c0c0b5070003c0100a80c1d403c0c0b0a2000000c2c00540c01c00000c689001a43da070503040760301201c086143e402080c5119542c1c0222944030343c5005040c02503441704100c0c03028141c01c0d0040c00b00b440c824a80003080e07080c0350030140201c99030190003401030a440c421503102c0081c00c42308044060424415201c50503c90349045c0701c0e0402034071032001e034942d41e00038040c0d0080030b60740c019030500c02469017000000307170487e0804024805040151051b07010040b8940c2c05508601400078865045410845208080c110b190312480c441c10000d0035840d440d0401e40c1d0120122810341e4801052544415414004d010302030840311607101051400380c510310340341c2d8041101000207030321010b1a40b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 960841366 1250 960840116 960840137
    0xf03040807061508100212160c0b01090c0f0f0f1d06040e090d0e0907030e01020d0c050705060a060b0d110708070b04051203040b070f0216081f060506040501200d 71
    0x24070601000e115172000d00d0080d41080d081c5808014030b054094040105c10890307030300f1084818000c2c03480808040d08107151481b00d42e9a8101d04001d030411030852000030300030208100e03213580a023011441181c40c5955500b0b012032414816504081c01400414960301c20f01c1c1280d5403030b6074240051002d08140b04020290741041d20300c0d94940322913612500c09005840e284400c45480d04405168800780c10720700410542d45200715030b030091161314000e4000f54101284000c82c0b641103c010100c242c481ca08455035513461105040440e09580a15900f8080c1004440000e0580f40c0280d1806800d82745000e250603204d542c1c00c00c0543c061039084070307115289001c10046c4001030120301080040301010302d02e1483d00ea661001101001070030482400380d440031700d40600b0710030090700042241700340c0303040c2c2c450f0b45981025907540d80380c0300517064600f07130000700710b00080f114091882141c01c0a02218103282c02d000c015983d00704603441103103020004e0251401151420000802c01308520349a400303000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 960842616 1250 960841366 960841379
    0x403021305010506070221060403050a2303240913020916120e0a050a08130501050705070b0903161d07020c0901060f021204380f030408070615 63
    0x400c051480009062038600108010b03203a110840d0b0380340380e044901034405804544d448101300c2008440e41c280388991300400080540ac1703c020b10480c042030b101e00d1b401e841603080d042400b805080e201810b00c041803020407410f60b60000b4910410444008600d05011120003244150000b1140035141926644521081d820020350346a0006020071154005116501d800f500710410001030444140c0d5543c0d000c0c1210100303200c45085d055001d000d4500118007420421995044640390902507c900600014150f024008407040c2c5a840005096441d240ac000040150451541681c25021b05c13040f460070702046200030005490012000060084500710341920540014000000c1d076025880c104800d0b44c444070b216044484070b24159400c0c1072168070803403d004815994200c40c8002140c04101c00004416003050350030070014078854801041841090311415110b0050250030030403580c03051140d16002103034482e000d41105403034800f035a074441c0111141c509460091006014050200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 960843866 1250 960842616 960842629
    0x405060d2a090e031e0a05030103021c080307020a02031b090105060d0b030604051c0503061315080a0308090c010203040303050f090307121a011e26011401080d03022109071505040302 80
    0x3066200c00e680c14032400d140050501e01c23060102030300c1510081f542945c02d400d20700400d6400b0341d005502c29203a0601c1c600281d07540e24803140c101c0c4203014400400d4000900780c01103e9448100420545150740703000148580c030b40c04540311a1020762507403a1600c0580301000218061441140100031611013902042924640c0c010300008110042081c40700540e00c4400c2200c00750f001147c00240d0100207680565904929407100d48540100b042d0ac00038107405c640103900c41d00510041d00c40b410004001240c4900c20b0b400002d000c078405015060140d11301d0400f41040310400390440320419104d500d0500c42030030a540c210742c6030400d99802c81c1007881e00e85281c0d0040c42d00c6000035030190280b0418078800e011038000c44080541400702500780407400c40308900c191003614020485050310100d40c0000c48424062080c181c4910382100d125248030f072080f14441d840200101c0340e941d09605884a150320013800c40d84003841101000b003107424036200e048504200c82c0c0c6a1666030740c40c51060109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 960845116 1250 960843866 960843907
    0x70f06080c0906030406020a09080d0507060b09310b0a02030712050108032b020d15230f12011a030f0f07030b1f060903020405060d2a090e03 62
    0x3800000b809035040e40c1d125401920780265002c0702c01b50f1039250a9000315040d4409a102010500c80d00c0e401c400e41580001c0284081070082e07805000285540c018469040416103c41d91410b44040c10070b801000c40b00203610203016070300d40108218419486500d841d03503081d514101060313800001e018081d900a000d0b45141c070302c0c102d0709000c598904082591240124441c0d498442140e207041e201c41300100c00c82d481d03c10f9100c002151540102c500d520010328818089212140c2c1111000c0351040131080c81040003000c0e80d00c4803100001c2c6800b4402d22403040e1181a07001040040c200350018000c0c058070b5003403620741c080301d1300400040b41051300d4a00d240482c000543c101d94810701c002e032000b0820405072a080040040e270307500d840c1c401e0310310320082d10084111442034480205680b81d0147c150f0003102d008071401c3c40292031b01d00800216074604040140105d140d440c035403118008501000b11503800700b40713144807110380e03c1500394296142c01e40c0010f05900009809086040350078200c15 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 960846366 1250 960845116 960845131
    0x1e0d0801080a0b0a0c050d090812070921061e0b01030b100212032710050c2701020c10032406050a0815120c0103060b03130b09030705070f0608 63
    0xc2c050050f480305481c146000d0704509402d610384400069050084040f1840e00600407810066640c41c0d04041e01903400250360b9580203200c01012880036845140b08000b0b0b51849140d80c0f00d10251400600040751200000302c2e100c0761940b8602601164242d400d50040740106400f08010a40000040480398002c80c003500c11004840d6402c01a075000075607841c40c0c05004a07891385c98441c003405110b6021020002d04000b05407410414184001269040121046500c10700c0680ca40119500e002d004200c80c881d02c0c00c2031044000e0040ea10300c881884600e80600656070030010300d8010a013440024500040400d490701d1030000c551003d04e2b40008070306641d0510411007410807000424074414501c0d0701007004001e1000c50699160128981a95a40201114500040d0406154072441c10080d801c4c0406c3c6010000030301c4401c00c0c0122845040014088000980c4075603880e0b4100c440075003803140c41d20080c016200026403c1040e440941682582e02001500e00040142501c50007414078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 960847616 1250 960846366 960846373
    0x90f0f080c100c050d0f06030803090d03060e01050d12140412140307050a0f0c12140c03070e0105040c0c020307030b221e051f0b120304050604060e031e0d080108 71
    0xb2905550704c0402d4502d00341102002142900740044804040c2880f904040c12541000041c0245070200088151881c644da032030038400c555542d806400c01801c24400c8075002082004501d0001e0b00c640310700940f80c0b440c0d04048004907802c0c0d840821a401ca5048060100d910494003800d01c1410440305d0700c1040103e00071460a039081e80c070207861b01c3d0749100041c4401144882c0d003042000c8c15451038080c258401100a501600d414100507861700d00100304d00f2070140801364056401c01003154410354864503071042080e40f0b0300e010f102c000d00d2900510020001030210020069509210200083d800748001d03003c40d0610f010101003000800740811000314811340c1900004640907070141c0605040703030200d0f4900d580d6042c041e08040380d5a030352076100e105680b41d0309804949544203040c0c4000c160f44107030a100f40c000d0780c1a80d80c80f580c020760790700401c00c1c80200090b40c400c40b0000c052640140544a8210801d45520141003491500c211a50409201e07110b1080d0b02107251070043c96010000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 960848866 1250 960847616 960847631
    0x103110414091902031302040614090c160c030503090f01080f040201200a03081512070e060301021306030f0f090b0411010504080d0203040e011d010603090f0f080c10 73
    0x500c07071486500403198061241900000c41c921030030269520103003001403082d076903031912144e071601e0500640300892207107144c00341c0400c400b80420a00107605a01501002d1076031074051800600d41c001e04e8881c0d80c440c441018585c0025094480540150310800003580c0300c03d0301d041000910031402c164141004044010400900c3c03090718816001902820308204101201c1190400360140d841c51500300e10500e0007800030560300c850280d124111080380c20003410580010018050840540c444181e40041c100b8400c0704c00c0e403c24140c202d40014001454454444403d03200c0c40050f80c13203100400d0b03649105211075000c0f80a02181e001d64240c0420070344405503283e9025003000303400a8006401d00d030003a045a4025000c0300e01424680d402c440007840d12500c002d661f40d00901a40300b08500305000080e010004905130070200107400f0205000c1d80c01d10fa41140285640c180507900b2990410034100440c03120b0a03081c10460141c0201c560b02d40300031212600e0800742c20b2120b0b640b80d00c0d01c4503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 960850116 1250 960848866 960848879
    0x120615120406180807030c0503120c0c0708030a091412010c110d03090b0a23010f080f0f060c030408070c060903050d02060606041403103e1c150602030901031104 71
    0x4455001b94182800800d1007914182030b0b107180102d0100b50f0f18501c0b500140103410050b1400b4116520410048402c295210f0035490740303d02030400e603240031803024003007406214500741018048110203019900c0e407180109a280c2900ea0b1200d8441c0070400381440680c6100c020320168026203101c0c00d0030f0041408560340c803600c903071000341580e20b000d0b500c000c60146500391342c030705449022070340c2e103d403ca558480810b502589250700c180c003204d10070506003c01090f808100410340b500ba0307002400095440951042c02030744020400c88a04000700310060004d04c2c1c001c0b080300549165690fa180d20350071450000d1610100345864401d5600403810041a0303071b5881c040b00c003514801c43c8100d403110030b260046850f111541844120050600340c5603c81c900c12211a03421041c8008054961403811110842d00801000013034441030804000104a180c040f01401203268410080007501011070300ca080c0806c88540c100300010b80000454000560f4140100002c044070b13001000d192078a4880d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 960851366 1250 960850116 960850133
    0x801140603011401020a060c021c0305011a031305010609050f090120090112291002060c0f0c0a050717030c06131406010e0a06170312061512040618 65
    0x115411040c048140f161240b80d2003405403d45051f8132100c1440790074000f0310041e441c0c55080300c642e40d24011100c16003404510902854ac103c43c2558680e91902000720904421644010058003801540c42003c0380065001d225600c0107001c0042c00042e6070421170103070310803040054250070103a810450030381c1a82520040b00745038400f0b444a126922920480181c0f40352000c051480009480c0404030303084d031010040d56018462010001c0300c6c503c45072004120420104081c4500144d0010f4002506004504002e1442d00c00c2100300380c0c100741e124210b83e441c0c84442e200440c0c0075041180d0800c185076a03140ea0780010140d0f9400b46042440c4a6410b60391500000c0420318112090048002031112010b43d81607104542ea040d60349031b43c1c59084407142c144090340c841000a280000010300e04040d41031540e9003c01080c0030390314040c003035080107840c0301001c1c209540c000c64005101800d2010100145060bc0703509500c090249010304010b011903c03949500c1441401c200c01100000301e10b407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 960852616 1250 960851366 960851369
    0x21f020c0603150108012715050a0603020309070503070e0408070213090501020c0c0418021c05030a08071803110103360515010b0a0c08090a0f03020f010905090105120111030a020703080114060301 86
    0x4080c00034550004041c0785030340308481d27417100c0d0300203004420116801c1d0341a00154400c040c004101e40b2003035540d00c02d040c0d4482452092010f041d00040c08070700000c61580081146074002010301d215409601010000c4801008080f1000d039400a40c0c1141d02c10288a41c03000240304880c200088000c0c0d41c100c1200c0b1440c0c20001f0300c200c414550560241d0700c1c109900b210a03803c0310850307407100e40c3d80d2805054403806030396040c0800c0c0d81c100203041e1000291080801c0e41d0340302800e0410700c5011001900070f000031104174120b00030a10000c942c0c01480140c020040d40c4140850b400c0c5400740c2c00c21b2420038050001200300d00c0c840741c0050203045038400844c3d803007640528003100341140c1414501c02d14050300141603440003030310748005603441a211000003524001c03102d100295803204015202540c4900c200798103c10b8580c01008207140407454a000c1c1030030327000042020041e80c3c003000c8061340101c1d007029000d03a000c150402459400300d01c1502404030124000c809040710b50000c1d0190205 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 960853866 1250 960852616 960852689
    0x9100302031b06071a100b1806070809030114010f12020f0108091516080a140403030b010201110f04030c0b040605031306140a0912020307021f020c060315010801 71
    0xb042d10b014016141d0808584d0440d40140741c0561107146072021900241c03040d50300e40c00052a140c03011803401e05540858020780c1c5800d8501007045004000e01551f600140c0c0f0950b440701c800e1044020b1500c0a0049500070258841d18040c150704003400700b00b0003081070300100c0c4040b04041c0700c03e00503161100c10628182c000d0a0524840d80c0d1010030603d8a2425046000031202c05428040c00300d0850744003101250150b01d031480543e0760200d8902c112040741e00c5440008100b0004240480d0082d030160507400010301c008114103125441203001b40e4032525984054140001d010401d000a40c420140581108108503103424640f0400410034000501282c03450f40b0800300b64801c01066600401000849001d10080b43c03030035801c090000d208142094030041700d4114140710051005c0b08aa80066000708528011198040704000c07080d01d1003031503801d51203140301c0702d00c083e07807070f00b0241d4403030000030701040100046030000504c08041a401f942002c0c20200040031018624481c03207010b0301c103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 960855116 1250 960853866 960853903
    0x30c06010e0a110408030414270702070f0608100621050907030f0503031e060102191b03080c120708091309140304050414040506071101021e03060910030203 69
    0xa0b80300710800100b525030000d0100d610b0024001544500100191040342c0b10710024250310383c1100103010564030081d0702d1041900d02a00446014420304003080e40003a40c4e481100d010780e44070402d10f007141e503a80c1c0195000c504848100516410ba0555803406002140b4005910304010000d120348004600d281c03000140d1240c0000346010000c1081038000d58000d4244291508181000c0c0e071039500503540392301042c0d8140d180300c0007005203500c1d07580079007410b900800e6582070b028078204441110b080c0484610005822003c0c41404075840300c000303140181c0310350741e9800c030040c011b515001903d0790142c1d110009200140c042018203040c3d84800006a494106080781b100240008061a101c01401404011400307140c0342400070240c410f440060300d04008401c0041d0740340301441811100103000e80d02080004000c18400e0544a1800510100141c140713024134050505008542403e80b030140b80100c05c002443c50401380054018001c60060894941180c02007030700c60076100c076030490390709 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 960856366 1250 960855116 960855121
    0x1406120c01051c060914091c030e150f1e0106090311010e030a200d120309032a0c06050c0703110f04090c030201140c03090411121008070602030c06010e 67
    0x20080d40c03c2c0d1070300041c0100401ca483d1a00400100a91281c080340e01c031505c4002800c181c0c0019000300c40c00d00d11840445000403040c011409003002030190303242070280d031062905c00401c05411a02500c4400700100351803405520400d00d5a404c807802ca26015010300c010072009412812003020340390041c001c0c1da0034003690001070301c0d074400103846a038061240d152006d0600021020103a172611380b086444030004c5403a820080076100072200980050092400450242c0c001d07404200340d00d1080c14020b0407040c10403012030009115400204182ca00143d0785010001c2000648021b443c65003080350421040d40c810300c0d03960711203000c02031052024042801c5036075141c0d4040592a40024801c4c00b01003441d250014001c0304510040340801c880d01b00300001c46c08000191844140d51000841c20240d5220401014215403d940c031260341e020030030b01750856820303141035200b80e020f11045100b9604d07110751282340c903411394000030864006216070054800c01141880c11119808001540c54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 960857616 1250 960856366 960856387
    0x6060a0c050d09080d140d020706060503100207150501033504060c0b06040c0512041110030c0212040f0b09510706090303110a02011406120c0105 64
    0x484031800040c00e98810781141d000030b9a800070790101038031400e40c20b40d00d80002500d41602d8100c1c1c426842180722000380224181c94040741d000d084018050040401c8080c0e541c00440c2c282080d440b91901000d03000164903044c0007007a1000010082480d80400c120b42c9151502c2c80f40010403002c0c0031248041203260318208016041006111450740c0005941d81d07076410b400b07804800d81c14000c075411380380c0800203070381803505100d10342000502d41c94840c07070311050848100212038000c1c4200c03164404406080401e403038100c140c0b007842c0e0342902c0c006840648140003a01e0481100d046483c2010208400e00c0083c1c0c4510070803044503140d942c403544400780030740003071600c042d10003500b149150501250b1403049440d01008411400c00710480340f1207282d0503980a280d000f1080c24541d61142003000d000000c080c0d501c9131a490f070080c82d000030b18410b001c030460403583c0151903080050307444240c0004000c0c0d021038410341064080b55801510324085030712544603003001c60032605215000c41c500001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 960858866 1250 960857616 960857627
    0x90118090c0906120302160b030711070b04090626030d09030201060816150e0607020f0112060308040510050306030c0108040507121a130c09150302090c18090f06060a 73
    0x380c1000c940601c040c640301c000e410104841504c00b9401072068100d40d110200102d0400b406035a01141100d145030b64056056980000c640c00007541c0f48100710000a2480d0032101900140110880c00304142d4540704000303e02c000e0145906136440c0c04148104050b010000407204401034807030002c59540b18034103050f401414030341d015010700d01500e0105c40e0030000c040c2c0c000c070682c1d00401d14903100342d400040c11102c040e5030096a94124100b00000c0740035243c24000ca80203031005142c000c400890403212441903d07001e03841100ea041700403406010a240040050a00c2038130791074042c1c114a072040000741d0716000c03c4038840c14031000d0b60100d030600c40c080c4200c1317000d40070f210310388071505d546450081e40c102900c10754009400c4452002c6421401030340484011a0b80000381d142c112030504000c80f00410317600c2d800e01c0901844840c001b0041c0c8410403114461025490043d03203035620284862500003a55448034412843c9034108102c100007031a480344c00490503a811a242e03109a0000e0301d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 960860116 1250 960858866 960858869
    0x170a050601080109121e0804140a0c030b01120206040e06041107081e0406020d0f020f010c09091104051003050a0207140a03020c0306010f090504050717070e06090118090c 75
    0x14502610300003003004001500a45000740c4900349805c201c507403c1d03208540034907a110881c40304112643d0050003c6115081c05030b00b00b40a0549814420707a00e003000c610340744a201d0200e1309003c2c034103810000d1040c05000c1600609150f04940340e80781c00c0c2d60007d80b0f076104078054005203640341000301e0f81e9034844d0b0380a04102c1104100350f542d030b04418101071102d40c021481c3d581d202c016403a1550320b0642c0c0c5900380d0742102c2894008016480c0817080c1924440d4000551314114450f150604281d03100074050002103200300d486121505080641d458140c4950343e45501390703420104001c0041c1d80b20b50031242000480c507e400121511103d5214010f0300c80e0341000f612145210343c0180c280c0a012400c800000d101e9001c8909401f4004103150b180d00c024800c4000e00b0324120403c0080c8112500010303402032042094480854503440364000f224000700c0304000960145000303000745134505220607005101101c29030360b6585032090010344614611070f030700344442c5c03151103103001c00c240c5008007030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 960861366 1250 960860116 960860123
    0x1050603070b0f2b1b0e0909013b0705010e010507050115030c06030e011104090c05041e1502070803030402040b1c2405153016140a170a 60
    0x20081010a84480204000c20101004981c85c007150580e003982480310382d5803011401c1d00d684565000764010009020b5000f410340c80d00707549521030f09010a41c64501c20b008411045e07046440422202c0c40e5042c00c1c481c10080d03299030791004a05002c680e802c100c041790042e80929000d0340d6600c40c2d1a005000d03003a49656980240500c00e008002c00003c8202e02003504c00c5c9680c200b00c00314800000c9820b0b19070100100c0b800460800c802c2c02042c5541e0040310710f100050801703500c2c09598201218036680c000005448010b81d0f01d200744443c10004503159141c0b030031440246a1a82000030b0306480b4800500004e01c6581c0d603001140c01d54035088600d45e200301012404c4501d0f030100303040c000c00e40904603600e460b9003460210211484891032003082e018010803080c0103200148a4180b04086004015400803071310088440141d510701038035481c94100803070000d84110525044044a00d03100c0340c0012041c116650100051501e0b10031441c400c64054201d641010242407007142d041001500015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 960862616 1250 960861366 960861397
    0xc03090f010c12241e0b03090a020111030f03073b0118081506010e030307050a0209060a14040c05090406060302131505301e070201050603070b0f 64
    0x14070143e040b01c4a0310341001100800e1002054001800c2001c0443c0082c5031064200b5183c144601d0f9050301c507021100d41d20001d02c240d001d03100d622004044e017049800a00a0f40100548400c550707022030b040ca05140850011810319600001d0f8804a02005140e0002c0095198402d5000184804c3d050901c00d031031004c502030803c0d0121400c1d100d43d0140145404911090400303140301c446208250100c420110291840a00c4034001d0f2500b0030f000341445041000301128141c203640c09000038840d85208000510300c1410b244140704030f01c0c070000c0072540700e803a20000810840c1c00b10120f001000350211400103100004e15000c0e503d5000300d02e0900c0c0c201d4031308000421010b406a00500c2d1106951148068680d0303109440a4010515180e030300000d001030204950191081300880200940c4080303064204d02c0942010074103d600b210f000400d803802201c2c129242200311034042e00440d15200034041c40c540030001c240e40e0030482c40fa05e21a1140020030b294241500b5050760760000c281c00c0c20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 960863866 1250 960862616 960862631
    0x3051207030c170a0e09070207032613060306050306070c14071e140f01020d20030a0804020405130b1513020d06050a1e030215310503010501030b0c03090f01 69
    0x10f510305034000c500010f01141c500000c0c10b12038607010300c0c3c007841907180394014880b81e4250341c0ca081b0701c494080003800c520390340c0000d426038892084001d072244d41c21a00c61003907550315004004040c0c41d0f040d403115009030030140920501c2c40c1d021201110700e60b000300090002081c0390404a15010050384a176046001c104880d01c405054986130b441199544000400c48904d40c07001c020303440c5400400340380982d2040a588450318002c01400d103600341040d00b041360340711031800348900310b601c102c0482c3c0018102204200c21440c1610415810030b807403803100440f90341c0546c0c540404050161401401c21081c100281c0c0c1341e40c1d401515802e080d0008030541d290115202d4000c00b500075070154500c15045610082503070030a56a20300701c522045200502c5c074501d16020300405070b0501448040c0c07001c040101c03a4482c46281c102e85d02c0494281e03030f2043d00641d200e080300c40710021078012905c00d9041000400104400d104016040742290311255a40d8507403000701860000a400c502e4400c2d400c0050703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 960865116 1250 960863866 960863903
    0x705031501081306110f04090507030606080910020d0e0f160608220609020414040201090b12010512010b190f06140d0b0a0b0d05150402030103051207030c 68
    0x1550241221031240c0200201000054410410072035407006286510403420000ca801500100070070f0f9a142c0d01e03585004000301030300000d076102ea0000704506031100c083c403900c942d05204071001019113107010403182c10244100e070340ba240308109010601f500450450440c10341c5074406007840e006e5030700722441103000401c025203404079000c0034494940520000100b10b80103446881c443d0544902100300a01c00344032000c80141015402d407803081c1e13a4200d10b001a215403160600621a21400c0c00c0f0314a043e10004144803000d411065480800b80400c0350300e455090300d5241528022a42041c3ca2402a45500e0050103500007890384949405072070042014030b45c8640c1e041e507040c602d500c005580c8441d000e40f036080048109203840d5034101f10700310f83c618041c1e01581421034002c000c0700d422681c4065403603254001d40080522140d0351400c2c4440725045003802125a04195000d5085601d580c86a5444007803000520400b658000741c02010144540d8185100550111042c2d1a41810b0b41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 960866366 1250 960865116 960865127
    0x5010209180f06041103132f12031809150d0803010e10052b050d2c060307121b110c0909030a1812030e1c230a050607 52
    0x2e441840c41000310000c105941030038040d80c83d2007406924501d207140c40c0d01c00c000500030102d240642302200c2071026521087c100d0042c460360304000700d08224482d001001000005060804485002c0e4420440400140b687c40c0c1d000442188c111265440382e504d191301448079224a6103120360005084041d8010082e42402540c141c65140402d80061764400050503a42400e80c012207501220654001c104d240d203400800f0b0603e03500c8011040c05041c01d5440d40e103040c050801c460046405078200d9210708a8418142600712a840529003500c5002c3d004990644130140041041141e4940c070a40c0380c04003a00f240949201c10400301034802240034006000728a000c0501c0c2d61402001d02440345881d1000b2558007448280d00038601d020b1140205540d0800a4503d0010720b01d20f0344030005101034036030075150340d00d03010f40c46148020300740001f049045c00a000b5003408d140c6020301d062020503002e04a0035040e01e0103c903000c82904141081c00e00d4002416802005071050f90104004250b008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 960867616 1250 960866366 960866371
    0x230d0b07020d08091207061d0705030d090e0c1e0c0c0418020f04240b0901020105013c120f110105070b0c031b0c03070c0909021c0501020918 62
    0x15400d9034252144540103c4071440181d6255000354802c904030416490b0400062013850b11542c000134150280007403c18200030884000c003595008140e041080c3d080070b2201c0b02c1607070328510300380d1740040c1031003907440e00c10602801401500b000840c2221203501c0384140e08954004040c0016111112495000c0d2740348180c2d0030581c09941003a0110101108c049000c00c25260300914203540865000f00340001040503d10b14030803540d4000e0300f903d00941080124005d0468072041c203948a1455002a01b13450040c0c0c0441c180f20590001d42a122407941c3c8582c2c3d40da074038408481e01941245a0a0459180c160000501030003c0d40007201080101000e40d40500d210b856442146008000195034a005d0036002610318510040003c1451041c035006580c000e030003000c0008649003a101d04241500000248500c5600025001041c086001c08140c000c0805210510075651a1307400309000c95102080100f069003640554401c002c400e4040d501007620181c5040801e200700f501030001c08609 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 960868866 1250 960867616 960867631
    0x30c140d03061d070c060605060c011a010905010212071b08010f1515080c04080708060907120206190905090a0f050c0f030105061c0c0c03020c19230d0b 67
    0xc0020004207400c0075900c50740c01640c09003e4100d56911118260b50140c884c2c0c104552a40da1044042165643d0310060314491203140c0c00000c0d441103400b04812488903182d019414805060010030042c0ea00045d0b50300c40290003641c0c2500d0340c5081c17822101d003c4841840d1460042c405d580490341010550040030148414101880380e44009a14200d01d50614014a0111142903641c00b204038003810025801c195210742c42403410399550f20460605110760003903451a0070400c14400146002c0050342c02a1289460700307130015a443c0d00041851288100704848460549003960b5294041c01c944401404041d05848203807400010b010028056000c07082c0001d840c00e00480e80a940e21001e540b03c0211840f5210302d0b5908100c2000880d40111411007044c100100f420400c000d40360041c0c1e4030340040e0340c035080080c0340d0030720b00a820040c03100c0185010392400d4564a2442c800940c3e55000c440e120070341c034a0619414100d051010007100d10345c070b405c8490005000704002c1782c012094440d029 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 960870116 1250 960868866 960868871
    0x2701030b041b1a0c120f070b100b09121c20120304020f06360102010b0904030503060a0b070f0308010f0605040303080c1204050105150607021309030c140d03 69
    0x1800e030752000c80b0141800754100c84120f8001000c0000020801440d20940b000300325501050303a55080c03c5254480410005202800310707080382001000c10300c564024600b000720002c1141400d4421505001d00c031711041c850115200e40c00300041c02441045404610035206646079000e05a0140400500c05508180070f5581c019180030050003260b4143c4441802e42410b1850701c40d5020030904804141c00594000302c20400040154401710030782d529000700341c28800c810115501c2c50700c1e140480da001c260569040040442da1a0394203400345620a906051079922500c500740420303940070b0142c0056404803c0001c0e00130500210740740007014a80700342c0c0c42004a07030300ca40400d0610400d40c8942800701e0002d0000b840000d00030201e0701c7c0e200482131410742c01d0640607007802d00000010364050300e159560703000384210105090341d0310303901c5501541c0640c94128180e000c680c407080140c48190640e6555550741c01018440e50b00d6000141d00415030849001c440060aa100d40d01e81c00d101b8040791 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 960871366 1250 960870116 960870143
    0x91e0317090d020f041b020601030507050108060d0605100b07051e15040f0501110403060b13021303082d1201084c0c030b0d0209062701030b04 63
    0x400d198200e5505010240c55525000d0303a65091145503003e049815520a032180e00c03c0b84403041c0740c5001c0215680c164020002541f56080031030521406401c0f99041210344e1007082626169594030315071181d40f0240008596a49000351142611140c02c10b0008510005240f400c0c0b100c00a014071340c490282841003003411880150642e6142048038000944d4601400500802d560301004400c2074021000880c60150340b045004c610307407103078004445d165660701c2e002c41c86040541204191001c011411880d291000440000030700c1603100040c4100f100041040c2c41402070380c450b98111070304d04140d510355182c01810081e1500021560001e0000130000024403082c0080d074401e442c40e86148a644d403407415075148c0e03c40030b01601c13641e07030110401c0200324400545c800d010100350300031440002c0c90000c403180203083e10403d0349003d114030b0f600e20b000300c0980e441c611455003205c0100c3d841e0010060310907101d030944084030300200c4111400000007040c4800903001c24030a900c82d81c101040070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 960872616 1250 960871366 960871403
    0x7030b041416050c0a02150c0607020f03090d02010c0204090b09121606020a110601060f0f0509060d05100b0304080403060606021f1a13020a03270204090201091e03 72
    0x1d2011510350b08281e01052010802c0d902500c01402802442c500b03403405a05070340c001c01c9400305400250030021000152203821035805100c070a80012191015101020003007100d10395034001c404125104001c40b6410b903085a000c4e14078407a00943c0603000f0f2025041078104150301c45003c441c0000b95000740202001c800040b40e040307540b520f440c001d00c2102c9000d1034945500079040070800c0f5041c00801490b0060368a01002241d008005c9a926800c0c808040580248010403200c044c0703007030103818001110796279110419500494940f0f0300008050341e420148441d55200c0758407808003100c00000744000e0000d080000d00c1500d00500081c04410340c0d510b070407030355048815980e0140c000d44911a0010b1031141e0070103a45200d219904100305424000024200140904c903200c18682c0081c01e4002e184d003501034030030b0b0f40040b41502d00240c4443c095844803c05034000c020712640d502c01c6a00d00310b82c000c81e101c0300a8103c0c5a8020103050b845502c00904507880c0c002983d0860f216100c40d50003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 960873866 1250 960872616 960872651
    0x7020f12031b0717030c0c0616020f011401052812031e08060409050f120403021005090d0605060d06090807110f13020c010e0303070c0b0108060f19090b07030b04 71
    0x1042d6010240b1410340303080c81d00013042c640000d01040883e401c1040104400d01c0d0030403000d40a40c030702c5030300c1c1001004007140103450020911034642c89179040000f201120754026010313a0440701d054441c44141580e490980031648442440040707901c0580c100070400c41110008241c0c1c0710301c41e40380c0d801c040c0d017480394458403a030109484c80000380d00d003000295281001d410507004c5038401d8085503204064601c54609066402403c0c50080c40701080c10015071425001c0403032259402e003802e5103480c54210128088440c1600007030030044d240d0b00811210f4482c00c11001d10b442c0c104408002c2c0040d945000b42040e4004803055611404141381d51603139140850883d01d400e40005c101d14080c60141c41034201a4100480b9203d1555135402002d002000606c0250700c1000300d0754400003107040c0391400c4401880d06801450007503002d40700b000f004004803941c41d41c0010701e14a400c4907c0030902c098401500c40c01400401e240114404d100c40b035501074106500481007180d0901445200b804038010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 960875116 1250 960873866 960873877
    0x1050f01020d180f08030d14270f030f0c010f05090d0f0207080d0903050607110316110616151806091e050f2103060103090804090908030f07031503020907020f12031b 73
    0x200340c8020503010354127001441030241704881d050300c0742070480010150a54005521a014607500002c0241c4504d00a1081e00b0b100490314004001c103041603280c2c82c4e60740070b015044d0001e0280074901e181c1620300810503040108500002c030348031400b800c0d0005081c5400d034803088400d84152008191514010340301041c1d2048000300450034001100b1709079a400c0700829040e90084811a00001a034440f60000c1000b41c07c80b441129940000f4070f4084041c422020491051502e0201a094200441c01c034213020143c00020120341401107040401c1000c046154500c2c2e0812200c035582e0411001080e8001840061000e441c112580344406407850304111558850f4034404000148a960180d0b2215490074014600142400e0f1541101811105560b6042d60340003004030400c84501c0d0000d41a5500074060b1034140504550240640120714650000900c6102c440c00000c1d81184200444401003981904031508029a09088000c0d1303070040d20001d0030340070302d01407a84411550204468 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 960876366 1250 960875116 960875131
    0xb100f0c020621040503040e0c031b0307030609021306020607020a0c0e15060f07050712110904021201240e1e04060f2301050f01020d180f08030d14 65
    0x309004410750030840c2981c0700c8a800c0d40c4071040c07007031007400c0f241043c00810300c614410390045654074100210740d0b8000c2402814465003030010403c011840c006443c85a6480e00030a0041e5104d84450790150041d00040d0440802c1600c042004002c080c0c500740800d04858098096510703645a6680490300c80d050104094918085494100000c92111450a030b2084442028900b00102c69000950580c0080103a0040c1b050104012060090a0041c900109403c0e800c000000440da51988034440000d064140b02d205040000f900355215561074005172070207140200b04900c501e00212404021841d0032549413181038078081514285513850b036015200c81020b02102122100702d0880b0800005c10484e000d545488031001c0700c0c86c490080180407401009600e509028504141c000303000140e110728032640c44500080f065980110b0808009030b520f10780b444200340032031801c2402d14400d511401581901d03c100050103840480602601c1c41d1840303003071000f600d203441061420481582e010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 960877616 1250 960876366 960876377
    0x60c02030915030414120a020c0d0c0501030b2103040617060604030b15062a0d090b0f090d0b010303020d03021e28020105070e0a1203110a0c0303030b100f 68
    0xe82c01c40c5040018651061042c040c0c03295141e50140000d0a180701d41c400b4500c4078801140054000d501070052219940c000d84002e408011181c407919403440080c03040701e040c160b8542c01c00c1403a03120b80c7c0c8040b841105a04c40d0b18a91210054400c0e03480e805072080200181d11a50800042000720702c815010707103001002242002d0440e1103140440d0400307880003c08082100b503800503130f10b6004c0500048200c401c2001310558400004000b09405000c0c0c240541e000f124400400300e8100c002801038a032891005038994061983c000c000b81315441410b58451988182c2c04100008400148d060380d10035403d03a1046d40030031740e050b01a40600d04002094072105903503001c4582480024084039150b03154149903d00d00c0e00a4100f14285030740c500c10040c0d45480c01c1202c1280c10010a54008909995250f90145000103c8903607600082d001002c002d09015010071055042142042d49038000c4500f1400d186d0701e02d4003400034803000c007095004441c156010a0b03028000c0c00041e080900b02c0c2c560 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 960878866 1250 960877616 960877639
    0x2040e06040b060403050615100c052508010204080105070201060518010303030c120c09050a23040b010e0a06050a180503210c16030c3501180f060c020309 68
    0x700800381400d00e0036140c0280091100002168041003103034003c040420044510002500c140300241840c1c0302c295080c0561480198001803000a203103c01e4440290302560328100c0a001c01c003074201c1580000e030251300100300882d054906502c01d5004400c0c0350020400e0a648a06018100555050903004400f1030030041010030300a800c01031603262245071001c5103400c0c000e40e001c21900000c01410028494000c14030a03420500140c002400130442c458410b80e6241d1829480121104d40030f6008940300c4185820f107134000c500764064180300802d000040b9841c0c0c60700411070742064440400203464000301b00c003900d20104c140b00079118048d02510030304040074000c0700503104410001c840c1250402602c625400140203280900703030f2442041e08028914201846508134503002004103002c1c03405c01c0070200303d40c0e40070a035145940c101c1c45036a120700c0700b0102e401007039000d110031a50240007044808100071800d200580a00c40e0a0030001194070010481e5640140510681c111703402119 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 960880116 1250 960878866 960878869
    0xc0607020a0c1505072f041b110f01090305030a180206040905061302030901200414010c0f0519031d1507140a0308060a120203060c0a02010213081f02040e06 69
    0xe02402401e050411301c2ca448266680d2101d80d080200c0f540444000e03040602c0c80303040303200600c0e0081d8002240c3c248140740c50051551202c00c40d9180c1c02d401e100c5102c04002400714248a0002200c006c01300820a484050402414691088034444201d0745800e100140b01030042d9070301c13200704d9000750810f8102420103503c98020b04020b002c640d4440a80d41c0b14000111160008510864941b40040b500603210802c2c0034180c0c182c503681181101e0300b80804d0102d04c040c910036840100e024a0719060b005101d0070b2551844c4030300034016001b801030f108881c4169501e000480c070207a1083d510405101040c0e124044d0120306594190740c0102c03a04020600b205900d0003524070300b80500904045400c40e95006442e140a0203002ca01244a030390810002d454500b00150003040180b040b0400306803076034002911148001d10f5406800000310781c001c4958405d42c1641c841301e902d1420104000d4881d0341c4503503100201296840030405511074001211000e000303540884414110020f002c0c1c56880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 960881366 1250 960880116 960880139
    0xb0103060b06090a060908070e04052119080615070302060118020f070c05010e030a080f161b0e07090e0a1a150306040b09091509190501020c0607020a0c 67
    0x1007429501000a1120f940640d541141e0308005020584650000070328203076103a0308010442e032102c0000da5101c401c10021500c08074440850070540350b45910325001e0b6000c140814040d100e8480358050212511011107908641a00c3c000c0b54211a011990446854015140d1003040c200600581200780100035a02c8100d07410800e6081780d071030240c1005207802c0d4009485e040f20300309490f00802800100800c1d6006010441808070540c0500700030340290301c41a081d0301c1460101006454002000030603850002d0100c44925402201c45448030380d5200020091559030007400740c80304940340428241409010500116802c1c0701d0350100c0e07a40c1d0307181c2440003000c01d141d504100da51501c03948048ea0396522480c00000200304030942e01c0341040c2003404122114140814040c0c11400f0038000f83c0ca80015165061481c00540000c403941d401c6559400d041203c0b04e9505506810380c0320108020b01034024007403c629000844d401c81d5103e0717200f203070340b5004100081c00001802000780900c604c0310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 960882616 1250 960881366 960881381
    0x60f0d09051c0e120a05030f071e0b0a0f02031b090a09020c160b03010b03040f02130203180c0427140604080c0c0906130f230709080303040b010306 65
    0x70402c0d6024518035000741d900d03090040d0080070016189074242c01c10b529040310343ca8410b0640e00c0040108404665441d5943e109500901061000c08a01c61080101c4042d400603141402d92200200728105c1c50300341001d02050340c0c02ca0b52182400354036104040c1d1031080d03034820207441d80403225040070320f58082d195510071401c0c107810945c215408500005c060008000242d9007400a1100540740701002078000d00320b800401c000041040100300300306854bc181d0740c00c17a40105030086440c0651002500350b0200030000d07241c003400072007006035018200e2009942c0410000a440a40780d0712410441252000c4510381c804507081240954441500c40c16a0b9030944550b403200f80c8503010301c0d8030900d0403108031012183c0080000704542e00003001d020340002c0c501c1c103541c181d01130f00304140000c031000d1030345542e05139040c1d076041510009003840e000300501e155144410380b00d80f25200302108548104951490110300f9607600001c0c0007200104480c400d54004e104003110703074216035411002e840c54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 960883866 1250 960882616 960882623
    0xf0c0301061d060c0a0c0f060f0e0d06050108060105120c030303150a0e041b14010e060f0d32130b1008030a0807020607050a1d0a0b0f07050705060f0d09 67
    0xc100c09290ba181e41c80108a04c0c000303800207204040c5c151034101e0941c2099000a90003105060041140f41d401000c4500d901660341030a410074161040403644926030340d4000f80140307003400000203010001155a80c180c9000366a0700950508101110b9520200d140300550158030402c000f46c0244586040c07c500c454009200e544041d50341c0c112042d52410a80e4146c480c40c0003104008508031410000e04018490542144441d0f101f41e0006481d00f0f4428600038019107001035450a007178a844110360024610381c41c2008044a41610300311403001002c1602c030384600b204840714100020303e03101c5200380b0345107030700c45c1540759565510103104402070603a081343ea001c5100400c9500e02440989103070410ba0303031503031708070b107030200c0001e26040001d000d40061080408c0900c807079035804a0728401031101100c0120440032001c0202c1c42810290b400780c070310640003090321080c3d03103902002002c40e50300400485119503100e0381045190310503051111180d03c01001440b4907410740da0854601c4500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 960885116 1250 960883866 960883907
    0x5011d0d02090108102a140c032a01052e15080402090f090d030207110402041e0509240d080f07061b0225120c0e0f0c030106 55
    0x80355400b10b26031460a810a40c241e0f00a5142804607000600c0391548205002c0b21302c04042601034842e03400104d1028440b02001103861004040301c203010104c5028403c0802103d0b61080712201001000030907480300b00c14030901034011801303040e050285500a903105056a00440f4030100950b0310851410342d1104e0001d03c44800198010341042c1409803401151901c001902d0a48101300030036100074200000401240c00384245200c1c00600000814414140140d40b0aa00e09004010106881c8415449400024040340c5280d03c00744200b01c1030001c4444881141c1c1f00d802300b110014003100c0d200820071504110101c40c48240c1540b0304050000790204603c0d031038030744805240360700400c0b580310101c83c00107800040201a00c50f5844103685100c1540c070445d01410001c6d140c1c50303100c1c100107002420400f100480000700329181c00821500c000d0f100d4031100c2d0702e01310150702e0301031142030708501b940400262240a980f0455200718141491103240d45e082110945d100b40c0c411490001c40c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 960886366 1250 960885116 960885139
    0x41a0d060506040b09130903080109020a03020904060305070503060f070e0105090d020a09240302031009051f05070e03031c050a02070609080726070b1302030109110a080705011d 78
    0x120b0b8039000304050220403441d40d544610007001d0020100d14146c45c8a90315207482c2c040b40c0420b038040780407030654032001805a903640c1843c07801c03000b0b4081d00c5005030f8030500c0e00c0c00000c204000025820200c60066013600c2e52035032102d50340c0380c90000440c0e43c14045201c4c060420107d40c803440051952840060803c44101307071603004182c5041060700312800159859030500c4034010041d082c00301d003000d0f00c190041083d04640c04241c5901884100761140c0703440d03c110720200001400580565885444469040c9460a1103100900700c1a40d081000c180c200f0501e000604011085402691101c12285455900108010018800104954241c503401c1c00440b001804901031516114050040191901564240541d2034200c40301c0b0100c01e8140b124002400b10081e80551b42210b03003001c603440580c1d40e0346030154a03c0100400083d41946042c821004000c0c84100003d0240410742c0c03a1203000fa01c07040110f5a510345801010b000c80c44284101c0c000d0110003000f40003c1c02c01502403e0b281 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 960887616 1250 960886366 960886369
    0x31e070c0516050103110412061802060a03150501030e06061011010c0e10020a0f06021c0f05100509011a18150301060f0804020603181f140a02041a0d0605 68
    0x2c5811011401002165000c2100d0341c0c2c54000c1c54060b800d40e0522a2801d803521454914540102078024012615007820303a0700d00e0090601e0003040d58024005c1ca95440007244002c00415003812072080300060f000001c203041d403003480381081c0c0f00c150f040207144a84410701000b0070f50b4010a200030400c00c0c410700246101c0e00038012240510b035961500c3c02c0e104000c004100c0004a81000300b81154800054840407501404515180541000e001a0b07a00e105c1e000301891a04494110000c243c01e00d034040c0403100300d0354002e520030000303030f09101c0e4074a45440800c00031002c01c6c400d210000003101e42c44120061104024164500f40084d00805507a03450049541c0740020000e403115000041300402026810050980500d03c5500c0e211545140650004440703000c082c1c140040c1c20b258590b40c005428080113245000104503a40d020150201e11140010345080c0000306079102c10800841e0002060707000b541d099480b00c1040e2201c0c0002070050400503000314481c1d0103400d8071003a0010700c4d0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 960888866 1250 960887616 960887623
    0xa120c030c060e09150d140111031003020405090a051c090509040c0315020c0a33020c0c010503240315040c0e060616021005071e17031e070c05 63
    0x14081501c944001c0340c014410014400790062081248000f8840c0c500526a2403042d028103055018441f81c000062a80001c1e004089032400c40d0880940002808040c40f480c11101088078401c480a11903a5030f480c0c15a0344810280704010040d5005181c0b440c182c40d510749400d10007581a2400300410f03030340c0e01c5c0007411044c0183d809031140001a0401d00c10300c5103040c40021501004042035140031140c801d02a552100190b000c3d000b0310048a0650601458450301000c80280e02e141444030801c40011400a500105010440e8400c807450581d145d4054000c1c0c074420840524005a003c00320005480001c0460a46a030326002e42c016624001c203602c0709550056000d41c0d0101c45880c03c180c1c581d807800001510f050310480043c841ca0404404000b14024440c1d810707210701c0740b240d500c03001c02c1c0c0380d030b002e0f40d10000c2900712811010b4500c544075031003030600c05004070322403002c034080c0b40280d4040b884203944040316044a0410590030030000315205800003840d141c100f03002051919a2401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 960890116 1250 960888866 960888869
    0xc060d0f050f040b0708010308071709060d0b1c0b13031704030503040615030b070e030304080f0303060f04150b0f070c080d0807050c07050d0204180807030305090a020a120c030c 78
    0x30010203281c00d21007401800f1404d0344e40450641090509541151520122800b400900510b066180326010604d03810000503140d1400b405040545c41341340450b10440a0710071012031034080da41c0c407070002841080c0c200541110710381145070410192a505166102c600880f4019010f00165003100e0440d407000d00c1c0c40511950103a0b84064590810746000c2040e103040e403c441c0881c03914140300348003240740410240c2c1c000700242042c6030303500429000b00b411401658490041c0b405410341803c04000044015880313120129200702e11000140c0801c0704941c1d86807250072003000381c00014401407403804000c095405450b102c0030304200407031b61202841d42103070b007280c3c00c00d401c5022030141294101d2110394010700c0c1402c110342400c241c05070160f902d8100e44242e42c4504030143c1e100d0155281c3d503000c0d1020080d000300f45402c3c206d4a003040e41e4603503c1242e00301d00003490070f40001e0544502252030328015500a02903107186107004107201c00d0040c04001031b1110122180004001109004150f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 960891366 1250 960890116 960890131
    0xc07061a0d1103190b0f0127021b0f10050f010f03020d0f02060706020901030b030a26040e04030908101104061409040e0601181401030311120c030306130207050c060d0f05 75
    0x40c81b8035021502c02c94049043e8002d5480c072014805240c203004400c8101e03c0c11503030412006840d01d50f550078407503a1b040c0c116215202c5005001480481c0c2c500840e0607401000945802c3c0901c0d190340c4144407054a09105100648014000034801454600c038a0075601e4041c40c881c865541290700010300507440003100311202e590004d10030080f96098041c050000c4000c401170f00b10294251545145001510340c0c0e4040a500150129401d107070310000c0e13070701803e82c103000411940340625029015003990301406c0ea640c40751449422114040f801a00c581ea2034070310516041038036200c8190341e00a20702d01c0f0f185002a040c400d409550311a4401c0030b9080101600501407549014812035070001c43d13442c010209400c08040e11400c894001d400c1c0e0460f40d062030304101e19620001518101581c10054021415000034050103403072001010754040e0f802102c032070340100c1115400204030321851000502d5504013007204c4549140c5035014054103141302d2400704514401c42251070803908206e8540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 960892616 1250 960891366 960891383
    0x21008091c021f05060915210a061d0d05030a0204050303130302040501060c0503071707020a0909021521091002041d0f01061d01050706050c07061a0d110319 69
    0x3100d4580f02400f00d001508981c1c0420006420004089107021030300408400c010740000c203c2c0307a407035101d00504041e503100202820903403800100707481c0d440340d010607010740b1814281101031018400400350440c80d0080038005000c0c3d0b020816083e12542c0000340481c04056080c400041e20351400e00042c0240b086001c1c00844030750541c4108000c440040e0806000c10203441c141c103000410010481c1c0c0c0d541e0300401502070302414142c000c0d00910030114002e400c40d00e40400040c442d0300a4000c06200c82c4210f50410017060300340c0c2081c00030302407682243e040b0b03030071074403820290b0b0100d8801c5908a01c881e41a02c01920014081d20180d910542c08440010000000e001d540c10200101d56003000c860000b0a2203075240c00d070000c04445840c070340c080980d100a0345242c01e5a01036002c03100c20a0b0b00c10805c0c0b06916000d1109411070300b01c030700142c6070f860608010130f0740c0036410710041480450082240d00b4a0390755482c4d030407442c1041c440060300f605c02e00d803070681c40c40107d0107800240c0344030b8900c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 960893866 1250 960892616 960892633
    0xc03050124050612060d0f080c010f050601050d15051203090a0f03030509130212040807060b0406060206071101020c2d0d020d050c031306020102030919021008091c02 73
    0x340745030a100c2502003400707640980091049684410444044c3c0a440345145040d440300c4e00020041c603c2c1d200010480c100c41c0c608241080950405040c010100b00000c01244040442000590710112080f0340026410000841d800215502c44001400541c03d262034403503d0f40080b6280081031044040103501c0411a06000e1a24240c1c1e1005841c04180b2000043d00d03665026045001d01c0c02c0e804d10908242d803039042c01c03a41c0b40e41a12000c1510303130078030303000360500741050706496018400540b501030070090540ba441c1414045d001c2210440d6004094690710040115a03003412650407080c155020080646840d200b00500c001344041e2a01c8424202040c1d44454034a4445508200c120b810640b082243c00b60080b5080c100581d49080199480140201e500c1c150301c42e0039110740040b40300c40004a0499415805076220303065940c02c442c102e83e40000140f060680201c0300079440400070b9001008644107240c9550010094800c031503809000c41e034805031a18008480d440140c2c0071080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 960895116 1250 960893866 960893891
    0xb010e040822050a0f030b0f071b0305190c050c040c120609050115090303021b06120403080615070807080a02071a0a08010e07020c0d021315030b01060306051810030c030501 76
    0x4005009000d45224817084615503515110700311802007011014181c010000b032200c41c001c000c1640402e80d20080343c4401e51903850b015102d904140354030190700c0e001500000110340540100170905400400820051458030200405040c0c00c840d032004015180d030304031405114a00600020308048280881c0540c1000609110390020300f000070200b001544081010a4002c034104444c00314002c032203400e20008201240003849070391038000425066508100a165008081c103000320b8003201c2049142e0650007850317505000d83c0901a140d0782c010040300c030014540710024400609180191401d075a0740e1a000340b030b141803101c0205420030b0009000080658001981405004000b0303010881d4109030200a5503102c000840301c0c02048181d031107030250350f40c2072459242d10211100500200414412000140c2140e220444400080c1c0c0c00100d500790082c01880156480a0041d4907000446131100c010881d0150100382100c00b0720a001c0046040045010090743c040e000100b0402640e45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 960896366 1250 960895116 960895129
    0xe04020f040e06060708121015081006030e0705010302030a0e0d0215060a2106091401060303031a0315040c12030c051b150703121b0801120b010e04082205 68
    0x2001c4a2203003908005c020006035588066510426824070000c10035a2000e000d1108d15031a030304000d03201c2610101d143d1040303500981c564070500754020030184003951a8001d4080c4c681901c0056296048003d0038451944203501440e0301030010403003c01c203440302441c468144202e0220450068004e82d58411032429000c606980009090fa2069440c4e440c0551840e030a041107006603280462400516082c092a070b04403846440d04040307913030901c2503103110b4140280401e200480119050861180104442c117410800050011700030301a864110741110169040080044a0010a046c0046080d03050307a1103810866119032100c501c07120540c00c1144ca8514800c0f405d05c892202030008071081c1e2903007840c1c081007001c0c220711240c5a130250715080d6034294840c46052280c1e0314107a58040c0a91511542a4614020b5111400341c0d980341d0290156090102d400035207516072280040003982c507014101c07948240109001801c01803813013404003240c052242c100068500001041c001c615003035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 960897616 1250 960896366 960896371
    0x70210030902091b18030a061505103905071512230606070203060c0703170702060105010c0309030b0f040c05060702150702010c051002120f04021f0e04020f040e 71
    0x4000c4032802c51346420b42800714400d10b100c0d16446591148035000ea61410841480043d9001c24140905490000c41000c1c0602520506224031022242c0007442800342c483d91500400f04441504591564803c24002251000044030307480c41d24080700303001c94014480308029080d00410030005813186803000f00000800204898414585030150300b5814101c0388a20041605038080e03406940c031000015068011800d001c0d4150256408101041c514070000780130307151094403440c41107a101d5102002947d41100d0281c0035a102c00014001c56000c0d44402d040300c0d20034545412400d0b242da440083d030820030395104418030440020701c820040f05810740c1c000f6010645030705040c0960b81d0001203070040745008030800a00002804410b42e4810441c60000d143c20104540e011003403004140000d6200340c4224400b101c81002154082c4510400940500d400a0601c50000e02d2040d00c044a0f5030031402210610807404200880307901c0e01e0002e0640c6650840806440d48e150040710b08803940d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 960898866 1250 960897616 960897631
    0x90a060807021b0906011d0a0b04030203190c03030c05100c0203130b0c03160507090c0c03021b0607031818060501180b070b070c0b10140a0f091107021003090209 71
    0x1210103c86503840d2000100d6210200340303800000e0b52009410002d00115205995412250312a070110340b00348140e001300216407082e000c461030340c21840e11756250540702e132034000c0008601c100704001191003a07400960150007007060b20007005508480c807045403540e48240c805a000402c4070019102c030100d0385401000d202c100c0525018103043c4490b12403041c0c41c40800c8284c416a00c0106200d01046020081c10008000300444003469002500140481200704d00510641c1000d10348100006940600c040f40a0a101d06000460b642078600b91011403280c01520365090001600c10b90307050310b03145500c0180000240417030070300d03000500660108000c0981408904000c02285400c1c00880e1101e60b086050f4812513210707540c044614207a01007014107401c3d600018002c0d0105c8002034503040f22040d4000342c4150a200e4240907007606140314400007851403c1c400c0007500b42d035810880c00300c0c517810400c0e441e0174103650025120101c65014680040d5441c81580d0450030265143d5400507403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 960900116 1250 960898866 960898903
    0x2091303050406030e07030b09060f090c01021005070e090f090f19060e03070f030e040f050601120513080c0109050106230105090d061404030e15120606090a06080702 73
    0x16151000340081c0710b640b00d40c40800d81e5407a1180c20412003804032401442c0d03c400c001c1100d06005070513507070b150790541d00441544074130804607040180000700c440300d0300c4041e00904840400c07074024400420000701842c06000c1c0410400745a60b0780c106407107100704014155081d40f0305012201c0c0d8508020301c500030000e940241d29042c0c400440d9800071901c42d40c009400708500c1e1100007824214040c80d14000d1180200800d2001019002442c000c00c0040c1902d040011a48103407400c41510b500307139111408125000159400300d02a174001e01c4d88540d00703102c185000d800c1c40d40d039049503a0081034240c580365076a004000801400f0300036403000305160f43c0b20009203185501ea1400190340040c4041c14000005086c0c074444c1c40720a03583e1b2180d90407500c10041500303507603150000400201c07011000111907506918940c0740c641c992b0f00100284100113814001c0d141e606641a050240c403c030740c4014107203c1820035a40f84c0c0c1c0d2002c043d2942d075880030580e040110b80a46072001d013030b113403411030304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 960901366 1250 960900116 960900151
    0x115030902030a29070507051507050a030902032103061002060412080a060f090c1106010f05040203041103030a051917070810090c0906080604061214030c07030f0209 73
    0xd600062034160990003071400724058180b444200c0c1e1503da02c54135030009610000802c0b80940e00700740903220050141e010f40d441c10076071440000980d0011035500010907018064107401e10311a81c80045075034800703021102c61100c90040180e4103650000913910403c0e000003009000c0c00c004055410300103060008140600b0281c0c1d0f10519001910001000c01c4031150020f0028403179604900001c004191a0090203915141e0340070250604001e503101044840e90141404000081d20904a8600d0b110060841d800d02d410003002e544090019030f1210202000d04003d541d061004000b0380c04240c49607035840d500c0803800f1010044581080d81807010072090016400d5084440d2680034004d403800c480175964040e4031844059007500800380c110301d41100e03c1e25954001c00100142d071055250f690fa1031342e50b41c0c10841660158010411119650a01400010001d190b00f00310042910190703810040280c45051030000c90758020b40d241210402c80305c0641c101801041d82090100e09100c180e903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 960902616 1250 960901366 960901369
    0x90503030a021905030d0c080103030815090105131506090f090207030815120d0306061205041203090804120803040204050a14010509090a0b010816080312070509010c06140115030902 80
    0x4031400c184810003d664260100704004080c000c0714140c10451004000e08070007100005c14011007400110701141c00d640101350b484011508402c0c000c0c600504007071450307003401e0601492090348030304c1c41c0c14141c6035980e400c03062080c800c080300074151036500c40f4003a502e01040c01859603c41c2d4800004144100502c8010076404541075520180018440b0301d020080c00c08034005c06041c01c00c0004034005c0458111000c0e6150708000100c4450365110450510000d1100303044410640d401000c400d506084444000d0282d084804458040d00740242042da85609a1800014100040703c00000000820046181500c100e0f50800c03001001000640041071209454203010f0003001d1203080020000346604d0010001140080d910100703040c0d081d65144690f40c0c0e16402124465101041800041480c1d00e00005442c045441c040300c4d405192a00c0c8400d5645a201c2c002d9141007040100c8084040340150091040c4c3e9001390500b0700f11580f401c154141139248200c1804205410440743c0c9015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 960903866 1250 960902616 960902623
    0x24060a050d110d1b0f021209100512010b0a09090b2d2706010c0f0305090427050706141806090d050f0607170c09040f060b0406090503030a02 62
    0x248a900360000303610380d05069a082d05004001c0004001c1d81000d144001c0303044003c80350b0800307107420b0312016542081c07100c01b641c4904150b03c404240078018010120146886d65010f00c140c10241402ca00d0140704403526102038000360403002440100107403003c41d0a50018600000703001d030f201c0401c828009640020280c154407825072022606c241c1041b0007080b0500e0469240f124020b003c0100580c03481da1982032001041c40100c069010100003031300c2940240010002e40e503101c0124203458100d42e5007529282c0000c4041904555610801071041615208061011400080409071240103140a034582811a00800100840001c0c103441c50368180c0152200c20960360f04032240804513038046107182c06168011075121410a404e1401d000700455800e181081d00d03426580e25940e400e0342a030388403401803034103020030030114001000e00c51150090060060001c3c00882c03d0050748a0880a9a0701500100c0e0000d60004040052980201c4c0c214000c103020f50203541404032810000c3d44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 960905116 1250 960903866 960903877
    0xf0c120317010f05062b050a14010503060402090c03090c090106110c04110a030b032a1c0b040b040201120911040e0a080712090308071113090c05121524060a05 70
    0x6001c4641c65226108210200055411200080782001f861038030389444400342110b2040700440b002110004160381c14046580c501c1140c01505001c42c0e0303218940703401566071008008046034050403001507495076a00000900a210703e07a9030341d5010881e520300c40e04228291105070700c42c03440c0c403524060b000c0581081c1d0b010124541400a644a08a00801c1c00c0c0700c240d100e0420a020404100802100302140001c03500d4030030348400c01d41c4138582c1402c031007040c040c18001e05a0449440082c0010b80c20740e4106500c41d106140c41041c4006103020603050310740c044421641c2c0c1140e980c2d074580d207040038450995100c0b0400d00410807001c1c5038540604034854201e01070100541d54984922107801241038000a590080d0301c0f40c0c0d0b640d140d041c4008000405500948030304958404468402554040c10840ca6081490850960300e02010040e0200c044051492240103003107001100d213501624651040d107076014142c85298241411004101c50002001e22403402030210144a951000a540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 960906366 1250 960905116 960905137
    0x1e05030d38270a090b0610050403080901111b01030c0e010c06053117090916031b020c030d03050115030209010c0f050d0e04060b070f0c120317010f0506 67
    0x2002c00060b8041a00c0e000034044041014820502440b4284000380d10010300302d400741d001522151210810403c440518004a0002450601c0140b0204031a10000c0034102c0050410160001d001c0300c00904241c180c00c00042180704c4550585c00346d58041c050f541c902141482c0820070341d411040082c05003814008090a140d61301c600140c20002c540b003001000125002154000030a840c10a1450a0307001c0e80440c0c0a010392130003c010682e80c071007a507003c900300620b101b80c156280207605000c034014940150805441d040d019280c050f61050109400f010f603405000494000d400349490520901c034888105464034004010002c0000400000f40c02286000341e52500c810004232100a8100360203442a00411107000400200150000d17aa2411743c0320400705c4003812080200300c80144c400e00c8500242040002c0015500c2521071401910034000da8000c40e40b10842c0045c040264102100881d6108480c442d103540e80b041c010f8010b003001628040e42d02d05100109885010340507990 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 960907616 1250 960906366 960906379
    0x60b0d1502071b180f0b090f1006020102030105130b0301060b0f25050c1c05030a120c030905030315120d03050108120403051203040203100f20030c0301031e05030d38 73
    0x75002040c680044031300030380081094015007000c60084401d23690a8030b1102c00384058032030008030355006000f624100c80d401407a0701070010b5840b04280c0a41000001c090703255503103020104079140188090482d1a504070489925103200d00c91008003000c80001010f0007401d0240c640f030000303100203160303240301400b603070300320300b5030130400a0010058421680140f060201043d05822154071004c0f88142805950701030040c0540f8801c141c0c212021040c000e09150070400c0021881c403d06010a40c54000c0a052119a000180d1001e41403401045075800040e4031400104a00001088205180440e2147d0f15162900e103940b40c80c0d0703d2070b440e4950038983d40c002c8001022365400303225103110365100c00005e1020f6518040c0d410010101088114030341004000d50191003030032031054901c510890118545142d00b9501c803680c0074241c0c5418411041148a1a10b00203101407024111061044101094204034200303a8180b2035042c1b070a00c1c22000340c135100308400081030340c403405035081c00b40d0b540d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 960908866 1250 960907616 960907631
    0xa0309150e090c0f1b060f1302090117070b211e0412030b100201050108060115021b03030f1305130b010c020f012609100507020307060b0d1502071b18 66
    0x4074030078018160885c48104284078514200354000c10894030440c0c018591248580c0c68400c2c1002e4001401e20180d0000320700307c0103104100018005004203100e04044480c810768030700c0301040703590144010f240300c0c2010011815800311404602c5420401c12481030036070f0b01c03040c2c030040c41041000b00040e1403015042020a1490b009a005040040e0050503510090f5000d5101038040e00d400c0c859810140300302c100000300c1082100c06803021501980c083c1a004a0601008809200d117441c0c03940e16010801140c00d0301c0741007a0040c28000c1e02442e07092403e9180008001c0300500311000641000e08040021050741c1c1d0150070701445a5040380e1540d01c02c821400101c0700309901c81740b00444015407201403181d41c40170181052086180f01c08030703000c0007117246c02c410039500c2c159841805039006121080016410b6001010508405401001000095100c60b031111542d844c0c900c0502c1c2e40014054140401180d10588a00068000d113181c180380c2803001c0e200207040344060786510307511504d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 960910116 1250 960908866 960908887
    0x50103180b0408070b01080a02130509071211210d020a0c12141b0f0307030c031707080d090213110405010e030c0d03030c0807020a0b010e180a0309150e090c 69
    0x30361301c40d0358000812034a65a101c0c0c0c50603a443c2603013102a80b050030011180c404003071040c00780f28860400c10001c2e000d03c5241008031110840755038801c81da49414895040140d403640080c0b00c014001d15600c00303002d680c5426038641800e030980a5502150404e482d45d001240d60300c0025021504058406501c03c4100e0816025070002d80c201692180101007040035480540c801445040b882210002c0051034640c08040e6240c1c02d0388402040c00d5442201040868105032400e03150740074050140b858811250760700d6945e030b480b004003e900c141c3e8a0001d2001d41c06c00201d810b40d80d40080e402040428840c1c141c07a5814052803065a04200c80913140740342c55201840886144003004c0c2c2030940e01d03080352401401421817a4040c0d0001200303400000c50507840007541510f895040910401d169090035071303540540e1401040d120305450411a400900482004000c018601aa4a4030030043c18140e4461242c0c0c80c5610303000403c0320003a0428801c0e6112480e2640180100301159a50740b4600f8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 960911366 1250 960910116 960910133
    0x20910020c060f1c0c02060601030b060c0c0d150c021c03090b1602010f020f12060d0c050607020f28170304140f030d0c020301060e130303090302120406030e0106050103180b04 77
    0x2190540340c00d0400030045c040c01c0d00018500d008170826241840440e03200c03800e1104500541d6668003540d84058841407442c1800d0100c03104484c000c800c0716400c0d1211900d01001d85041004d40c00041c0e00c1040440090b0584407d605201030151400380040300040d141d211903414060525a482c1030641c041e1074440f4001d51000899040080081d9191142c107041149a5044000302410100c50200064074520300341ea01c4c02d0740c4951110080076898100814484c0e1a0003503002240c0098070002c0c400c001d542c90304105048017180c0200c0b1740e08a401d992100306c0c2d081150b0702200c803000d1080000314483c04c0200c10356056608850660700b00400c1440001d14a106030540d00b034060084140c555182c07070344400d1101d4564000e90090280720b40c1c5840307411240310115050040700d5596034901e0b0000784242c0140032010b0080c4100d800502d02501aa50305074002c2c0e00060100e680e981446004180c03c0c014900103210909040050350311202142d141d03100520b100805115600002808200094 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 960912616 1250 960911366 960911407
    0x515090c1309020d05250302030606131401020c0a141203132c100506030a09050105090109150506030a14010f05071121250510020910020c060f 63
    0x240d01c008066981c6800381c400075031243c1e0303d4250840c00d2200041710044110031505182c00640c2c1156514106202e081300250409052982d200c8000c00040c105031220b407003000058040410030106222000001900d000956540f41d0300403d240034080041002c29202400541d0701982c101c11410b82407a41141188941c05a40c010004c02c101c000c02c4940e10b4900d640442c030303044010480e080d8a42154290303091000c0310141d4030108070344428005403e01802564000c520f110010a4403205503a0301400d681080b224040b99130364030884a81482800c80150000c6252428100840d08210b030100c0d4841d81c1000000d010603c1e41361900c4c01548007540904420323128040104a2810000801010802640c00280c802c3c440c041c4100b031104d52610f619605da5111620081c500501490034400102400d8013801c40c41e200da03a41c1802040040c46408441d40e010440107a90b6201c031420405136624900380075045502c82541c0c26269101c0d80102c0e0074400c0001c0c0100c0d00c5811f032481041100848 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 960913866 1250 960912616 960912637
    0x4020903030d060602060a11030109090219320607020114040801060f0302120309030a110f0604121b031101080a0b030a0606090516090308030408160f11040515090c 72
    0x91080094202c0707901100649503540d081d58510b0300e84424150907145006810040d813003003000100003c900d15030010b1031aa10280000a48202040d280d80e800700e20b642c00003810030030707245116117161858000c19560907620740050b10280c1d2014041419400b030050001d0500c901c2075001030501001a05445c01424200c009014a54851140011283d443e00c412409400c100c0103000d4035003004070603505400c2024004003645105034035001503c19011a0340d9401881d004110358013038035000000c1c40581040444010700d8402490031100250134030102c0113420300001c000344000345100d240440400424a0010440e8030b403024850010140c80400681c0b500c1a944d8a0041100303d820820442d4100c000c1003001d507070b500c02e01c5180544111801000110000003d00c002a5918061034026014468250805413520203402c0382d9000f506054903c600001050300810140d80420700c1070030700640f030038001750400c1101035610340814905a84194034180029410050010030740390482030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 960915116 1250 960913866 960913873
    0xf061d1c0f0f06050a0e06040210030f2d09030f1107091a0306070e1305270703060b04020a0507061e02031611030313030f110d09080615060d0b04020903 67
    0x75901d0952555224201c045951908103000903d9010030b51082c42a00c00c400c502405d015035465007044004403c402c203400034143e480c0001903030714203144a41c07440405954181e200c6440c0f061502e00c111080d0964415142c0d04092170f410002ccc1c0e01280010b00a009410100c484810715402981403c40b59080680060325180741c032202161503e5144910003020340c1a82c035241c0f625802110000d41c05d1107000e40140c1d0000103202e600211364481a4404110100c080c0101a40007e1609410030140c00000d594048481031050245502ca54a95100115030451811800f0341001e030160255120203022556501360745014400f05503038030910f07203842d08400c55480c90300701d2213449481495481f0500042c840d01c0841c80e4602e00104aa010315072031004400e2242055078200d0f192603500079002c00700000084804031a040400c0202a100541d440310b0307a1950804011390f20b4501d0050022400750358043d01c0c01c45540324901240d41400010740c0105e08141000e002c10702900c548000d1540511 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 960916366 1250 960915116 960915143
    0x617040c03080d0507080f070503130c030b2802180103020c03090414090c0103060b0d151e0608060108040c030201080c0421111008060919020a08010f061d1c 69
    0x40c204e40c03103940b1460a90310340300a40d44440742642d07050a0200c6003d00451b0040011035812011440c0c0704000a100c1c6103804075094403542c8a280101003a40c8840c41c46c035810480700d480c440030101040900c41941000c600300340710310b04091401d80b40015458141075000890541e0500305000300e0b24000c5000d042070000c04210040c510034048112841003140c020008555120340c440d015000484001845484c102049401944c1c024003002148a103030141034200021185814a0500c603403081d00c00c2c0c20007600d80780080181c0562002010a0704102069007008000344598040f0001e8a40a1074844469520b448044800384101d40021030b05010b071910405100682c0c2d02103030302d99841542d803040800c3c0544148207034014201d007403101081c03151001440074104002d91980c080c2d4015822a034851180300d07264100d0b88600038001c0001e0060006101d5607429555410061a10b8900580401204c40d48100402d04059900d44603210200c146001441c0c400540510706810040601c40d04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 960917616 1250 960916366 960916387
    0x705250c0e07081807030b0a1d070311031c05120405031308100e010b09012102180601110706020a0b0a110f07030206060a0f050d03021219180617040c0308 68
    0x20b0000b00d40154074400d028080c4902601d01103500070441c1c1e4030a074560740c03540307802c0002006441427100c0c5070340c0c407030882c14440035003501013021600445c045d13542071034003e003500d081c1818038103100d0b201881c00b03100366450011a0b5001040320b85a1b0b10080b1200a03507180c6251060561040c41900420810306642c0459800760100364a20f01c0100d4400801031408192802800d0360012001e250380003142000400c0f200780c0000311100e0550a440c126203030b20803140d000405e00e025551000340c0d450740e008108a81e55820480356040c1e2601040201176035440e01100079035801c00600d0003044e041444000c01c0c20304100e0740003c0d40c54000030448503101e203401e214a003042c0e003090800754018443c0d1000f003401030414281d41c1d42564454820701e07101d9410041482035068020b40118118420300c03030f0950000d1074034005800d104030640c21503040070710555001020300700005611140c410b4006001c001c10f903045003584200780380366400042e190344d030b50505514107410340e0f002030b140c450005101101d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 960918866 1250 960917616 960917627
    0x7020109050111040807152c040212040203011815180209011203090b070c050d1b0e160509090a230a0c0908030717090a0513020d050705250c0e07 64
    0x7030b1000b6404846d100740d5142090800c20030848888008500c50f2076641c0c0b81d5051140120482e030100304852081502c05402181c1203a01a001c030242c3c100c0c080043c401185005c1c0124021101c56000404c8190744a85406103c403e242101ca1403099492010041030030119040003001e42c0c000f40111806d43c0d481001c000d240580c400100e0001e80f40d1900801da4260b403500703450030544c20060126043d4205010f1007611050b840d0203844010105844110191b0803070210740c054010442001180d09040d84803400920501c2400402e001d03081c085a10903803190004198000f502540c0030407001075030350400d10401410707210031064008a100300003180c18290001d100d1124a99201d59100365030f04440c580ba4003e070380004044030601e216121541120300007602c2c802100070109003049580b8000034603d44080403a110701560049040101c28003103115240d4040130b1400d000389480c00c001e100e00b960800d1010028500e000c10300ca02000d11504240d840090000c041c80c140f031382c4c1440b1801400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 960920116 1250 960918866 960918869
    0x2c0604081e06010b07120504050d030f080601050a1d061b210702030604060e010b040207150f020f030a020c190605040507150e0103021b0a0f0b0f040f0b0702010905011104 75
    0x3032900500c00714030039000054418126a02c1512080c2410a980e46451020017820540740801500f8400400c481d643d91010351300b00c52007920b65406038045602c1c040c10000e8010046418064180407601079582c10420210346914080d4001d2210000c0e07200207051402483d2000001c4800304225214030300d000100c1d452580e10003804e400d0103109000341d1a09034031601e040250150440004a400070ba0309801c035030301d903002c50800030400603079050109049810191080c0c810320f04203051b8802c13510790b03845004c2c0d40011101c01545020030b00641121036100284c042010b00f41d0016192100c1c51042c13103100720000650001a4500c00f0b54208180500030940d0151214041d0039000500000880314411502d403894451902c096440310041d0002d41211160307840503007e01c1d8440d900100c00740605840e15100d0034280e1034086203400e04c08010705005221001c12107036130062001052420000d40407103548a00c90f0b054980e140d000803405041d1850f0000d02d03540c00c14120a01d4600744001620 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 960921366 1250 960920116 960920143
    0x110301031b14091003141f0207050703170904061413050f180708160f120203100c030f060906060f08011508101503150608072c060408 59
    0x1125030540c640c0002140c00303640300c1e245100346000c511407400c1c03d24001d0241d010300e504005a414950b00d40b43d21076403400c545004051504900040c0703a801003800d1455200e1543d0340d80460401007a65503272682c40c0300314000500041d407410707001d02995020408640d4105005402071158a80d241c10003010f0800c1d186101e80715030b01c0c1030f505c0c0b8404c82480c81154444c1c3d0990500c51940d855078031001580c4030003000c100006020308880441d0500041010001d040307150244260002e04d0304801c1482820160041c245d101035400c0e5080240e070300061804d4040591410014607a10101c0059004106280700355200383d060080004100d00c0a41c0038030b048680980b110308010340392a0089814110034001e202003030b045070701ca8143e481d01c10614154400764401c4550b4000b40ca56540c200010b40d1050041c001039202c0965401840a5061881c0200007034180340103d8101030b6001741070311840341380040c0e6201c094410f12695040c041e07655401a200500003035515520f0729000d98a5400400c00c60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 960922616 1250 960921366 960921383
    0x61e04060e0406270213080319110a03024b0105011a040306111210150f0e0d03020304050d050703020406171b0402040f14120606060717070611030103 66
    0x911304490803600c407003051030103000c80749a011064004000350800c0b02c03e0b9041801241000c90b07020000c00080804c1c1ca40d54003149000400850020900b031080d004003d4039800c100030580c0000d80015641038040b06001a984081050301c0401d019440c40b202034610049605103d150070494000300e4401c01e000000c001d011a0b81c03620030b000d40680c0d80100303046880200700b2040010030080c0d4031013420024a018a280b40202d403d16600038690161211020340840e0701d001c20105180341c0c000d440031002400d100d402400380400c0902501c441011907401030716002c01c55010584284211009010010114075030900c2c10f0170020350701ea546000481c0158908080440c0018200205d0482d20281e80c00802030b074603400314201c0c1181120302c036040d0040d03000d000102f1081410022030707015121102e080034000b1814803c10200c4030380030030614041d82140041c040c840d101c000842c1e01d075030b0300460043c80545022811580c1c52190b404013901461601480d00140451b40000318105c034004e0342d19 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 960923866 1250 960922616 960922619
    0x31b0f141809060303160b1e0f010302010e01141305040b04060e0c1c0f05070e09092e060b091f050306040e100c0203130f08060105061e04060e0406 65
    0x4094941c81a02241c8551a000c003010720038501e0705900e8194812006020349040849000d40807400e003044079812120080a00704100d03414841c5140300b068807140c80403c40fa1802c2c4224843d41880060101904210308510a1410750b40100d4119a40c2d5039000d007042d544640001c2800303000304084c040c031403003141000050703600c515090041034166603444001040c103840f40c1c00c811030b080d800300c2c4040400c4d80101ca1041294421489003058051008070042880e1800400040c2404548406540701300308035410f0140860001424492510b1000c05005180001c0d42c44040382c00c410b004902048da06160000c102d080c040c402400c0c0c5401d059402031140710141c4031f0b20070000f403620440d10000310244006808d034503068101c00d400c960300905135070150762291140c505076020384284501690000500305000d550804e0074000a018a4003102502070418a00903207c4506125081c480c0101240c0e07070b019440c296030041302100e28980d900795243c1d80c40e20003900c000b101421071031140307250010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 960925116 1250 960923866 960923897
    0xa030e03040506190c080a020303010f0b070b070818100b0307241202120a060e090c030303040809180106020d02101404020d03120609020c160501020a030e01031b0f 72
    0x161002e45000400e014240400d0111070f9548440741c04081081001d04c1c41402c0125111900400e42840a940034564941c141220a41d81c0b90603640210150030381009440d000c02c52a403107480c1c000d4807a2500491949440303041c0d00072074103100b00c0d07681180a0724118158070f00240d4005050250182c050b100b405039540c0010036002c00f0303407007070b286100c0660200001c01489004059001c05400d80010300745904203000c2603414501700c920043e42a606c0e00f090294007001c1e554036901c003218000408010782076001183d128000900700401104000c108180c0e1a0b454030b2143c902c8040c2140740070f2256070b640d0070003035a44800900b040050b0055481c0b2282100403802590000c88150a0116a60321160300b0f0191800c00080c09908100d00e41110039440303003031350240c47c0091820040140c1c81c2c0111103100d50501c80c030000303140c1492040c188100300690300403030f08603165038043c28081074403140c0340016000f13403448100e40c1c45050160400654955000b441800a180707040d9110010f00c00c0005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 960926366 1250 960925116 960925123
    0x30708010b0618190b18061314060c03070305030f15090f07030e070801021b07050102070e101a07060c020106052101020d0c0c0212010b0d0809030a170a030e 69
    0x10725070460420030291400d2288207007010b4280ca00503212a420040320f540c800608450381d0400310780040c00240c0c1c0801204032488031112480220307500c0e441d1a51041400007404011301c80d42e4000f940200c02c1e00c644e9501c1c0030654070a90403400541e41d69041510b8001c103254800c0320941c40701c3c40c041010446850040c8521300000e00042d10038100703a12800c0d0742c5c0c440c090703004001c141003607280e001542000d202070202e5030040109000140c3c8568014001005128034400007810507484000200226030340001c84104845a40c08140a151690000e04002c000d51b074201007181d40441c406500400105402081d410b0302581c401c201a07024400c080f42a92a50f12803650710489100d40c1a4a0202d079200c0144560a11800180380400c0c0414100c1030301d50f031140714000b18040c03030f80f12020750400c42c0420306a0541003008024001e03a16000a0300e1a44109014002640201d0050307080d03141040320500381f5030008a01c012091b10000042c480d40d01c00007a03400001d05114102ca400703000007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 960927616 1250 960926366 960926381
    0x210c0b121803040504091b03030e0f180112031e090608010e041211010e24070809060a020a0504332604050a0b0a0f15150e06040b0408070503070801 65
    0x1809140f40525203020000580121a010381e40c20540716280000550069009030083d403180e10b408104140d01c0703013048440d410501260703024080b0038034602c091a200b000704505440700b40380d42807e08460380c2011070b100b13030840da8220554030102203100c100700d405c1900c0c8401c440c0300350b84140d22030b0b80341c83c1c1c203040401080d00d000340340c030054200c00c142940c0115007000d40040c1d01000024481c103040030b428075081602184a007151082140c014400c0009203429501c0403080c100003000d82051902903075580e00040901100e90340c0800e0450f0002e02c200100c400030003400c6005120018a080b00d210b4005000903070160000d032944a0b440303414020303a40c08045074248000a03031075007031403003007043d410348000d00807145400b5544c40600050b151031403080c018514000006126401580100e007160200c07801c1ca202d42031803910412442036800e0405100740d00074a00707010150340c508042040c40c001c0f030f04204010035002c14085101500011740104a0b4811000c8078000f03580c9954403422a00403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 960928866 1250 960927616 960927661
    0x140a030810120b0a27060f0b0901080703080f1201090e010606141602061605060f0106090e01050121050a020d141e1302030d08070806010f09210c0b12 66
    0x2030001202c2c002ca80d40104e40f1072980f012100c60400f65120480500250a0801c5401b03681e1088085c0b1905800d202c0c0e070a0410040d20501718035418002903550b140454440246400d80001e1500d108030490000d4402c00e211074110164556144c5070081e003d031442180240e003661902d40c0000b001d520810441da42c010800000528114010094506951303546078260f0704013000700105d0107500741e0840744510040c001e001411903810540d0180642d074a045c2d011004110300900280000c2000d41c0200313046900900f0840d0728185514240c003014248544c1d80203602c0d15260801405100c42c1d0010150620400c00822084940000c038161545095070400544d034204039402c00340e43c04021101e41c01400601c050a0102d130581c0c0000e15002c0d541852b08009120b00382804042070300855900c0d0010001d08103164803a1000c0130080c4040b03401e1081e5081f1051204070724028111030782045188a8200c000501c1d426114500c0704441d500041200345120381000000b13051842804008801044 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 960930116 1250 960928866 960928883
    0x30504060f0c0b070806120c090a0209012303060301110c0c12070305071811030708040803061909200403050c0409060f05280b0319140a03081012 64
    0x40480449444900005003070501c4942541c2e480825030462116204200070790360796030b807494668241301c4403800f00d69042465520000144140e984e440c001c003907005992500050701d8240000049490b031550072010811021044055a5244a8000290b220703210690090001001c45140080707540700b4080c0da241107030404807034107410f4502207a90350074100d115812650300507141d481c0d840c202117056220308845000000c00980c500710794090140d11012400c0d005045203410503018000c240b00a10080c410300000000900594440c0d40c02c201c00b80350006c008504948550214006040790311120481c900c141d903292030402d140000302e4003683d40c400c4c00f902c401540501844050907202a04407130090300c0340c01c00d042d031a2a52140da445101903102e0003460500e21400c1a000000116024200b21306000e503070600c644000544100d00c0246940200b8070b2811800e06d412039080c070300c4180d0624020240c201c810b2551082c44e80d4082c102850410a403140d0b00c4080300c040c8003080304014031141 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 960931366 1250 960930116 960930119
    0x303020d051e0703090305150109060f05060717131221021c020c04020c100e072102030f0d12050c1207030218040c031a04150302061c1802011b030504 66
    0xc00c002403c40240f00303040840d5202d40300d070b032003500b0b00c0720103401482c0103114240104044a0f190048a00410101c0c050011040c14100469124413642001030704c8040c01840000524280c0004c0768a035914101d828400c0640b11140c050034a503850405840203506440c45c1d0702000d1404168000030781c0f654004100141105083c5180d41c4034865000b0158083c06d0010309440d1987d00041c065010a0400303004010300c01d0a03080201c1c0c0d8141441d160a40c8980002d10120403d41840320301c403107100d20300c41d1200c2d04c40c5c400a40341c0600401000d016001e00300f4400b0640d50005d65400403401250002d1010b6620380400c071040b40990620007403440340302c1001c03918081c002c0d03000300010b014020b4001d00105040740450255107140c4c006a001943e04e850341da845280e8010494800007044401307103c5c52008c100d41c601204d01d180406071052400240d21581c0408409591007000030200081c02006507004907958144510300c003c2c0c5c040754041080088800700b80b0b504050b102d50540314542441d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 960932616 1250 960931366 960931417
    0x5060a090920120a0e06010b1207030506150d06030c030807020a06050a1b0f1209080c0901031505060604091e240e060f1216050619030504060b18010303020d05 70
    0xd040c0039140e001c449030345e80c0a101c07583c4002d01c002d60182400441c07003995002807801401408500502d03102c201460302d024409582c2e50301d0749030495500001001910717060107465410040400360710040c526101850000104140080078002c0fa41c001c985a01c1880d40d140da00351014410448200e00044140200201050840c0100410a8040d8030248842595a640c51030b40d40c0d00710040b000030032604541008103040411040d040114251a070302c055501d0343e601c900c50520a202180800c1e920313000015090348070801554014007000c2c0f014800103d41020b60001c030115500078100403800d0511807106014090600317071109200360300000c2d2142c905041a80070700001340c20f1940c0145404040c2c4c10308d079078081ca64815584400003801c4d04152a08510b0141c0000d40c6c4228010314091010450f1082c0c0170300e08280b001914200812039544600e4518010122001080c0c2d020300c0c00940c031801d0465074140c0a041c0c0c0c1c4607030202c2d0301005045205540c00d00480c3c900c82e81c50113039040566007a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 960933866 1250 960932616 960932647
    0xa090b0f210a0c170a1808031906050406142b03050a02070e0402060904050601030b03150f01060e01090314030d090303020a030515030a030e030c04051f09050f1f05060a090920 77
    0x805109110441b01c1c18880e5913080c2c0158030a442c510401e800ca0754445990513000c1c400c1d04000d18040310104905031a1102d104110502004c03018410260720301d490700d083c201c00d00f00c015401d12600750303000d02c1150741c41c0c00307001d43e04500d0502c00184a0490f010600300901c20f0700c41e02458000f003015040255582c01c10000c0d14005080300e04050300d603c2c490700140c408010b811a0b074480c1d25801c1003d4580005c21101c110380580c0240104180044107030700b2640c00015100542c0d4100c80074152500d07682e01c0503403441c0700e0104002d03d02c901e17000e40a81803603450740c064044500c49907018021174030b98640da24012400700040c56810b420046140b00001c2c05021103051201d00941600d9040790302d280060111442224110702c601200c0021941e000035000c041c00280080d007070108268180307c00d401c4c080c43e2005108019024241c10501c5000c41b18684410041c10001c1049940e01d5603c200249600d80c02e05c5503810389828081d60a03801000c1c001d6102c03c46075008405804d0061180c4040d96 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 960935116 1250 960933866 960933881
    0x6050f071103070305031606050a02090612090f07030308190b3303100303140a090e04020118080309010201150531020c010902150a090b0f210a0c170a 66
    0x901d8420343c4800000603c0610141c402c6c554444070f6401c00c0205c4e03050071010b943c0003d00c8918184d1040080e40b2040c1c2c0c40d00c00b55840c0882801c091682641d370002d4052070700142581c3c0300014810450004101980412075610a60042480c00b0707880000003100d405440807003203090b034031410070056840b0520310022600c01c4014401c00b1106050302e400141400d42d402518105d4803032416000c18420716800c0898616980301d98000b051820030a031000815510f11342c0190b0300c00345d010501140648e80314054004081140c401c054480c2c55035514656a0b03a807200706014003550a2420070a082e90500410508a4030060090244800d14240c03c4c0889421801105103100c401c03c01c54403049401d06c060518888040d0000400340313900e00400c20341c03012080401d90314103810003c0d2002a940184440c00b1035840343d0f84640c41e020002101c04c15400340d0042e40e6440041d041002c0583c2401c86921800b9140200c800c1200140c0701c0d0044500b611610002c4000550100c0415188103840d0b100e482c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 960936366 1250 960935116 960935119
    0x2030a0b0a06090504080409150605030c1b2a2403072a170711040c021f061d0c16061806090c080f0a03050304140d0903030906050f0711 60
    0x10b00c1a22162424200d0f0030a0310203030380c800e00105090151007171520601001502c010003c0b0405841c040c001002e030322004208a0180401248103002c59404240c0181490024819594510030300060070f06101c5426482d0703001d003206402d02604c2c6003000c0ca403445150780b20005035421035868001004d0705074805461801004140c0500b160004510071403032040d682c558a007900d000b0002e0a0460700c9000d6607070019100f5904112010000391030a00700501e000040c0d4001c111804c0c0c0b0070013a030400c12404c050160008100c02d101d038040c5510741c07090302960910b100d08c4010036414003510407078503001c8801d0383e803140e010049444585020126040c0c0188101d4011803005600440d44054212540d4200c81168030740e0031030402c0251f002020806084000010110748600700103895413181c1071080a0b040c46000000708050140104225410451540c21901c10040141004025490500c8140c00156070b4620228200c2e2003074048030100d100b500302c250f0600030162140b0a505001843c800d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 960937616 1250 960936366 960936371
    0x902031f320a0608071d0105071515140307080c06030103390e13030516020f030d0203040e0c180603070507051c020d080408040303080618010b0901030c020a02030a0b0a 74
    0x40c2800d42e9020949800303416155100c6895040144003d42034800e42000c00350000ca5900b10b0816607640a8203490303d05400c041d41440000c90091248001d0280c884403100c0f00c0900b04001c11940c0e100040c907113040380709070200c0d4100313a9240c14054540000350b8403140e000c0f00c2000104041170108080d0032002c000084a0304202d840220007001180d10300a00d000b6051810b2020424520006040c2d940301040040b120a008100c1d98020210310a84ea100265a103070704084500703640700d0007480031a0380000350481e40501d121241c0a03569030014401d040f0603040810001320703447c1307280b030035100c2540c240011394010007009001c001164000422203010450f0902450022032810400d13100e0078035400b516400030a110510080c06c00800781c0302c2c4024000d0400c00c0c44001071441049030112a0107242c1400213844240c009000040d400c060601b044542c03c0c00442c0c02d600250003400410402d0703c04000c082004a016600c90010342e4001e5817503085490607001040b02040199400281140d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 960938866 1250 960937616 960937709
    0x503120301120219120c0f06020c130f090807060501050f01050c2a060a030542030304050307031a0112020f040c05090301060e1008061308090114040902031f 69
    0x2203140c491a41701c0280c030203c1c03422800304451103000c500403014042a1026140b2649950701046404a004803040d030190307510045001f80441e151b1041d018240c2c4081203070781c0e5480c1d500300348000d000b080c019644a5100d1410401056015030111040c01c02c200c400f500340040d07004520045008240544008450590003101c044e5032000d0060106031801e40b400581403d01e989003009020000a2179103035a464640022840f00c2007100005840440d003920319144c900e000040303400e40c0035540c42160103100d0184007104010040103081030021580c45039038407a0b03a85104420143d0900394020390400d20000c010419410103402c114a80f03030315800c046c0d1405c0905004682191b4243d81308052800f43c1d40309002c1c140003085407010003010180010200d504100010b24014a8034010040c04d11000007200e40711a401100105c0038441d43c42000d68681d42e503080000d000c1d5004a0720a900c2c051040e94403424499420a8041910350388a00c40d90100c00001c5540034a680910070810501c1d444d119 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 960940116 1250 960938866 960938879
    0xf0e090304081203090a0b25020d0c170708030108061603020435032d040501020d05160507090506010f02060702030d09210c120905030d08040620040503120301120219 73
    0x1440c42c02400e60342d01030f22510001c18040823070f0f9102d40031840d01f10b40002260b440c020354003082184816402c45044082c40080815a8000c0d20404c0802400070700c002c800061141e101241131031044031620455817030500040001c404074030450081010020718042c03441550100c007a00c9500c0c00c1d40400f1040301c0c84504042d41485d6421148000300d440104001c0000351035501c0008000705c200350703c40c59042604040020b0340740c040700314209007048401b01c0d0a1651442c02c1c80121a2150400d0959410544584109000e044100e41d0640464044403120000d9407002403403d01c07902242c0c1c091814041465140009030540050903590b101614a5102c50142c00c2c104680c0320382d4458513107800c620320b180b502c02c1115422940300b0041c41900070301040b098078003281c00c210b1400c051510200503902c0c1c1c034061005082064920313401e00c08102c04482c04d45c50040c01070060f903000310f00b203d80750b4500803000d032002d201c24015220f50031090603403100182060480c290900402a641105860303c031308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 960941366 1250 960940116 960940133
    0x130608070e030a05010c020d030e070302010e03031b010c080c0712081306020f070303060807030b06190e1e01090608030d15081f0605150901110c06040f0e090304081203090a 76
    0x148184e5180e5502c02a01622a4040120302d41c90016402c0901c01c048000300e525446055512000c1d06006141a0343c030a140d6040c005c803965407021140c402050f07482402d2040c02486e144403072a0102e140358001c2a100c01c1c03854141c4800d607900908191000c2c010100c01c42d108400540110a000395001c19840003600e9070000d090b444409002040e2248120b08005085c4d800580c009103060700101800d2001c5207003895120740c8210240c82d0281d036800000190401c05001e45d11003100700c40c1e103001788000700f20201c250005040b4203a48442c2c0e541d0300d403500c8a0460794140300e00c50460380108044102c0c004c1d55049004400344048500440d2030303580200c1801c2100d1880c013001d02850b0060600300c461814899840509001d80301e0200c91f07400d14400807024410040401c2c184800d14280410568040090304402c840203042c03940c42d5641d41104e609a0551030140c1d61011501c9400100c54407000800d440458001c00e0051071804a02d45180a160380b000e4181030490040c0300c9079401203810708 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 960942616 1250 960941366 960941383
    0x30c0124050402120c03040314040305030705060603030a0c11040e03040618090209010503040213060819031121070501020d02070c0302040b0a06230702040c1106010b130608070e03 79
    0xca00c185020090080c0500300c503000c9410661103144140400706106201c005040d03440030600c25401d540b503c0390b00701a6805121000d00e9030300a24001004810000b010019214483c440c2c41210144d80301c3c4401c0546901440c511640050074040000d4003107803031803403241c12044001d48001429468070100d28115030141d0400e001046401c80c0481000c003c130380100005213a0b03088118288103007480024124400a0400382c4036800300c03998074003007a4055000700001e0082030210341401a2007030026449440b8103000754049181c0c1050004010700102d103000c11008425032800884801c81840c144c1ca40110070301b07503002c3d942807140350200d007814401003010310f0040d42e0803e483c51840c4104819290b528801034050074100070204002500400c90b041d207480602205201c111101c5100c110500500c0c070060340c040d003002003404800b90803020700981c86616005903800d40c0e8903000304262900c80d040d11a1010f81e081c0104001e158841d103041604281d651409880ea440305000083c035101d01c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 960943866 1250 960942616 960942641
    0x904020c070323030a020d0c03110f101a0a090203041505010806041403090112021b010203040f0b1b030703050402012d0f0e0d0602070f1403040807060e09041103030c01 74
    0x58080180d048091003c01072618407100029803800c0383c0c8140094944801800c01b109012400e9610410980602044026200c07840100e1b00c0b66081c0d981480c2c0d6032004c00d1001201e051a041141100289180c0d554040701c1015014441d05403401529200941c00200180c801e41c2c00003075000c40c07101050183e2402000d02078010070540c106420540545407000704008450752080000044a03601712104070070304014100010780380d000460805400003110f0701001e60340c0d4030010820040102241c2c0710a04513000f81c4610320b495a8294101d0143d041440170390152286c2407001a48a901c00c0c2c0001e68404d10606d0304400d800c41c48a600c15200c0c3c542da00c0c4a80131200c5103040d020643e4442541160765500c0d00c0c0203103485401c10049280e02c030f0107180140803150005414400c1c00003031592a20301d923070300030581c1c00d0082c0d41014a980744d400038003a1240e0307801140c4002802c0340c8160345241c401e090003400c0030031076120340c4c0c0c91a84094540b0242e5406000c00c0c482c03d02c20003403e01c104c0c50220700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 960945116 1250 960943866 960943883
    0x8100f1a0f1611090609040b0727030c050312070b0c130602010b031506060a180f06020a050105060f0f041e050a02131a0316022a03010c03050115050904020c0703 71
    0x1101c1c9043c01144450f014514081c08044040003c0c0c0d9540c00313000754005401407180750650725481c0c1d00b05c1d00308040c0802c48010541d00214801075a68041c03880044038000e40104510300c0e1548209a2284d4443c01380c400810818000b0b10046400c0c030702c025400c1024490788903d410314000290251090035808480035035076802c440c44a0303040a00c0311350000000c007489a42d01c1d26003180001d200307001d80140c4200f0044605000203403070a0094400b409000740101d0800003a90f1000300a58403012560111a15400c000100e02607080029403627000c1d0394020044894182c142060100600691082e59600c506800184c101501c01d4420700340680c81c0c010015a440c0154200225195200d5100c159000c41c02038803005582c514000b900e801c00070744c0703800408500c2070a800301d1a0081507090030545401c0307041414080b60b11518803805d140d1040d4001c1c411034000b1042901152000d2003090404e40d000c5140070102c7e40700380010156000000e000606000c440e240b95444c0c403420350800c45400b035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 960946366 1250 960945116 960945157
    0x20a0c30020112090203070905040b010513181e24150b0f031f080109060f0902011403060d0614060a2106110f0c0c0108100f1a0f 57
    0x5540000d84200440c0c4403800d560a0055580024540110042a040b0003a955032074001159403d201d49070003010025400d002904041c05e1000420100313118803403240754030240c480e01c82101c0d805201c501d4040d000c81c402c04940349446001159548450064a01c0721590f104400521a29031402d90740701388000c41034820020548080c1219601c21851066209918080041500340d00840e00300c2d0034107a003060788980302c1c20384201c4002c047c2120031010301d203100c5000c10000c005510a04040740103440500150740c2441a09007115038806000c0c0c0001d40c001580c490742d014440056420130809044418455415141c02e400c581d0007400002c0190249000d0000743d24100340401d018040030b908012a0b6100003080e24652816280c00410550f1550014481da042502c25900000742043e1071a603200e26480d07406469031403402005002c00c031100003280c10203034031518510540d500c00e42007009480c1841d038170f07081a1010b45066085010304114000c0c005040d407015060541e107901950146c1c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 960947616 1250 960946366 960946409
    0x20706050a0614060c03031305010b06040b210903030708040312110d0b0f0603040f0807080c0a050d050301082e091203180f0b04031404140a1d070f020a0c 68
    0x296001007503d807040c0307401d01215400c41d0011040b65041004100d407104189001d20b0642c1c05885000401c81d40444d0118000941504003001420364001c02c085005107003202400800c3c1d6040c0075900c0c044641c3c820710001b2a140d0242184030307009400303400e05c01d01c0ba81c00e154001c415a1001d02048200100105040b40b10040030f009041807520300f100c800500c5100400440c9441c00010805800c1c0d03071400c48400b0901c0300900882d0100e40d0040861035882c04850f814664480031450100d500703104100014001c02e02c2102605d041ea6102c1000d80700d81c03403441c1c0c10b1041480714158100130000041e00c0c41001e05480c0d1140380d010500c5005102c01d0582c288030080d080781e00d92658121103d1a004000d00013030210904c510116501862600050702e0302e06044850380d8110401d407202c00c01c001404112038480d603020020419088a0782d091194484e607144900e65801403206000202040100d40c1c82405601c1428240440d44102d81014515446e42e090004d0701c0d50240041188001c1c0e0421076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 960948866 1250 960947616 960947639
    0x309022b021813080a0c02190302090a0504080307030b0a210b180a12020c090127090506060f180a06240e01080a090803010e0105030f0f1f020706050a06 67
    0x10a10000311141c01807401c2c1002501440f04071034004d11303075500001c28101e024099040c00e1581074018044d40200da181048114010f4140d01090303100d81108000601b0103403003406060301c20b039403100710fa9081d9201e110090380076105160b6050f5014281e4800404c3c07007080001c68144042006408601d40c0c40c49050180c0c0c0ea01004d0103003800c50099901d6140368400004440300880e40c00602c4505000306258201d09003503100d1501d95101080c07000001d510480710042c840c140000d046005004a0421076940c02c0321613400c070052280d001440040c501e8600404401041d4074003030090800c0215078004403c020000300c514030030340c9035103440c2800102d02c03809400c1c10103490544150030070000004040c02442e0900303001c0341045031039400140302c2032242d003207075800e1640001825101c0d61103003071404842c8424041c00703001744655140c42519020014031030802d5103041c400b404d11040c0303a60034024000708070303104081441e03000c000100020380140700d003a1040c1401d103000a1103a040c50810440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 960950116 1250 960948866 960948889
    0x51c0209070c0b011e1502010606031503020f100e031204140f060d27030201090620031303020c1215090d14221d09010204060f0309022b02 61
    0x104942e02054200080180035070b541556100071070003072458140c01c0003100c091040c0e0040207003040e805101280094054020209941060b1001d00c1100c0c140c0c407011400001501c4042e41c02101301d08610a00d0070030300020b090212030381c0340000c0c000401001082c41e00170542c1c1c0340c0401000000b1b0400c400318600b4041020b9035002c40700079420018040008500d0700404041c0b4010b15a1001d0002d21003a1340da003c800103080d0307a91034130700504807828068001d082602c0c0075100541010100ca0541c4661001c0d010012840b000c450f00f9526658290401020b09140032800c0d445201140d80c0c4c00d40c2c0d0141d41c03101a060201c01002012041e10384e8140c0200c2c080c0a03c0050f034080203052595503004003d182ca43ca00c031841903038413070300e5200001c00c443c01d01d8046801c040d40981804518007545560301c01c00c0fa0341e10741010441c1c0d180d121502c0d08034480d80c8121700004030b4614644031010310941128007032074001440c2501d240201150580d84130103000e607480c07030307515416440c2c001c5003000c42c458074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 960951366 1250 960950116 960950131
    0x7090807080d0c060209011e02030c070e0105011707090f0b0d0c0c051b0f0604141c0f0b0c0c01060603020a0f050403020901170f06070e0f1e010e0a051c0209 69
    0xe40004202e000d040241c0700840288101d40202c1d0302c1500c0d91042c680d05620351080b101e0040841c40640c00a52241c0c460011840325010700100400d61240706840603040325410b03034030308051403500e551031100c0d0361002c1c0800c020803480f1000040c00d540000001d030054010302c20140ea03901d2104d81070504442c0c0c0d9040c54400c0c0320240700780b0742c04282c0c04151103038a2091000d00c140740c41074050000705002c0610707186942c0442c0201d40494440c880d4551025018410358900803914420030b800354501840030401008205294a4040000e8001d2841070700a10350580d8903003420003d58105083d66420303000000043d5010401e100460752144080d0a410114205076180500310380100f24122414042c10481c04441c9040d00750154042044894540340c00040c2e40960030450740050940960303104a600c581c0b01c1d034515804601d007110400b034000000c640c82d1204102c020006603007044201c40c900e5413040310b10350002030b11707220389000d180e01914000174048090203d10400408040182190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 960952616 1250 960951366 960951373
    0x905120f040e0105030610090506120f0a03030c020a15020f09120f280206030c07080d050f0604110901080c0c0703050a0b181015031202160b0c1b03070306050709080708 74
    0x800017151840b01c07022381e1001c04c00070490fa95444003045404041a124110ba480340001950719400c0205402501920a507402d000c3c011180000704d075031301c1c16504045c2480401045900d80114240d0003496405045042242083c1c59000085c50a203900140c200d0182c00240c01710303a031000c0c00c3c000844041c1e0035403062849561038421244e00d03d03486960083c010700000000c500e18810550540fa0340540c0003900c55541c0882400c00b00140c60300380c443d00b0600d0000004281c031407a0901400019035290504a800e011015004443c40b400181051100100403c0f244010350710501507a4091400b4500811605000746481200c5040c000c0c1000c90018260f804c3d030b0b482600c0481d100c5003158101002150308660640c002d4410080d80e813000f400701d81e40e5003016031015008518004140c0750078880380c030050b503540c0800e4610f00c01c0d158401c100e500101d85071000d0b0004200da44080c1840501100c00050306c998942003244c03800e41b0040f0100782c1410b000c0100c035900300841d402030140c10010303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 960953866 1250 960952616 960952621
    0x30b10020d0908030309030a0c0c0306020c1018080a180906081b10090302011d06030703090b31060e030c010204080d030b1e0f0306041101031404150905120f040e01050306 75
    0x1810341f20b0142918060802c0f8141030300a05209802106001840d08450119603c0013081851a0b42e07540d000147c103402c40c200131514149140d1060700128640d008546185498440d0300d0850300007886003401d004146400386e01003203040061060703001900c4807200400c01c030051012303150240c402e40041d4601c50481d00403130200d240d600c84000d004481e420b00b4194400402c0389441024070a0049041e82c00039800310170000010b40c55005101b03014001d290080640c0ca600700b01005d0540340403400c20903c3d0956401200000c2000c152140c0b01c0c0c081c80f03000802010986c0d41a0545d1701103114142a41c0d0046000e02004205102c204421402c9080420400c00458040380104004080c03580c8010303802102c0c823850391611014005c1c4004000c0c10313600107192038a03108480050240742c05000901d080c1405480c012500d145901581d00611040c003420301100f0400c01034200420111414022113210061085041c4040d100c0d01d034074042c226449030b060001a214048050307124030300c030f984284103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 960955116 1250 960953866 960953881
    0x3100b04032102031b07061d0904150f1505191a09040605030a030315120507030809010c020a0308030f28090303180804030c0501020a0b16030b10020d09080303 70
    0x3a20382100c428594140075036071804043c2e0541c013601640300030380c0f210000401300c1054081000f40940f801620ba8900e01880018401880c521485003943c000710030300701050102d14620341044a071407a4140c04204403456450070000c0d2869440746a01d100d0712030030244001d140c05c030604480f05a0801016516614008452480e00154140d000b0a4000007501240c5600e66030080401b400e4040c0454200140901d402401800c0b600c860715646d0030a25070114003071aa040c0f00b002c001d03030004003c100d480c1c1991a4020b141d881115064107101841c441c550050f01d07003c0181c0000c5d4081c1030025101d00d08104c0a407042c10b40141854408468084941609000c0c0c4018038450507020100058481c030b00d240c141c00820800c61000b000141c18134074801040171520050095034461103841c0ea1850f0381d0b00040e030303864150440091182a0000009519806d41c0c40b034103022421600e008500d40305c1e404041807000054008820050304600788251500380c00c00c00c044018401c21000b9459483d0104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 960956366 1250 960955116 960955133
    0xb0106021203160210020f03092b1d030f030403060e0d0c080c011509061701050c0703050309010603020d08030906090a0506180709050106031b170a02032502010203100b0403 76
    0x1041411029221556403d00a10070802d2000e0721804445c00c43d0b032612840d0040718540c20856015085102e40b00e03052040849440c107185143c1d14107048800308038940c0314161008a050007141a01869914001015590030400c005400d4040c0380556036031b074207508000c07065a45060b2282e04950000116044040e4071009800c3c207250040c2086449001c80b61489000d004140441c0e40d4440081c80007207003030303078a0344e2214084403180390b42d045c404885800d115082e40d40803214481c520301e00b8802980070034080d00041d90701c8142000006401c0d0784070f030b00051040030711002c280c03141007000c0104400c0c00b20400001e50000e91403070092000038429501c056441500605590070084030b8070100140b08010024180680f000d58000d005642c1c48080040042910481010100313201d084403009180c081d401c0c00114082120007007002c1d1344d5841c0e184010b5400940121108244007c1d80903210040c518219450020740c3c0c0050303030784d0400c01a140f4200d682d030340100b00c0c10441000b08000255117a03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 960957616 1250 960956366 960956371
    0x3060c0210110d02180907180f140f0a030f081806070b1b0c060910060e010f060e011115040c0504020f0306101103030a0603120504050d0b0a0209130501030b0106021203 74
    0x3c44001d60f80303450040c0540070b020605428075404c0a40e11007400041ca1708071030b500c08030704102e07009080c000382d80e201000d141c40424843c4070300310240b031503605c0c403582810710344039207101409072101e80420342d03a6071003269200c1002c0059502e071401040d452101c40c118400d401104d04112032040c1040b01a8803590100303080509034040c540350240b42e0380c4540030640155420350680c00203a42c2c0c140f8107034249075111308800301140e82c0c0b1131500001081d10014440313402c0c10307581a0440c1000072800e04009403603c080142c0800c0c14001d1102c01e00707100c45030401c09030040b604a003104280c11700302813628442018280c1c000901c290f0060060440321a001c500b40d07684428202d405159030b200c3c0308420f035401a098044d03005580400010400b402e8482d0300100200e030b00c100c20b4404284031801c4200d9003401203000d246e9200d0414001c100110b10080041c64100141550042c07800c140580002c08130380c5000d0860f015035449100410900c00849010b80c010001c0c3e002a24620f94210005903c40c03100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 960958866 1250 960957616 960957637
    0xf070c0203030306190b0403150b060c0a08090a09020a031a0906150f0405120303040b01050a0e060409052a01110303062b050105070305060907141801031503060c021011 74
    0x141e22142c5c00d840d20320b070b440c020800c0510590b0b40e6500c80c14000003030340318000c84010f000e090003546042c500303000c01100c00c403143e41d00140ca00c140c41a40c030001c07140c0c0420034141d405581004041001c00070b40c8014120724106403000610350400707001d8450750450703000400344920740040800001e030702e075007928008002e070100040da6640758100350300e807585c0610307045940c00c10402d401030940045c0000003940541c0c0140400390650b0303a500301f0045c80c40c000340108d142d40380d42c00700410968101a00b164110741d21070f42c1500d080d050f07002c1d0301100082c2036100c40fa050707040b54002481c5558000a298051104040180d4a10b14010700481d400303d1000300303a182c05400c00c0c3c541a0640700070030040303104142c0c410000d0205040c5600c00401902084c0e400038402c04050002c03034141406110030b008552810f1070385500f13166035043c050741c0c2d00d80e0300209076046c542c403001a8800c0d0118600b000000c0d61040c080042c0c1204a64002850000243c0040006520313000713100b610220f102040d079224909 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 960960116 1250 960958866 960958879
    0xb1513051012020604150806130203070512070507060921140901050703122406020a0f060b030109080403060203040302011514090a0f0f0f1b0c0b07020a1a0f070c0203030306 76
    0x1128400304c0c40c2c52090341d200c2120700a448070740f000140d52003a0024007911007180c0000c89105a032070002d0403403200751000c4001c54810080c4286071240030314aa68428043e007852401c01d40c1c503844800681c3c400e540110b8501c02c03094544500d042c8826208410000d19183c0108941907140d01030000d445100140c1341440004540182014400e00201c0c4000003003030780078051241d6442060440c040f451281c221510031041020405034400070f0140000c0341c228070810010402c40c0c071540300520905e0440b0340c1554a61000d000400c051000604c002c0d845044016034a2920703080090031a908040c080820000f9050200000c906a41c02d1018942d02100c0380c6c1003c0c0c84020440c1c005203d40c0c100c0c84070503030602c944210445410343c0186083d44020005204002c0044002035403014080455030104003080900b0b0040b49034691450341c04078442c01203c41a04203900c03410030840da4000c03410369044020041111001607028402d4126615003003a8a034000e40350b0019889000087c9964020303a03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 960961366 1250 960960116 960960149
    0x50105180706090b031f08030a0912030f03092609030105060405062202270a08010605060d02160b0907030519020a030308361506030a0213090b15130510 67
    0x80594503801c50740c03818100c6e064010f030354a0109131030750003102c0c14401003140f0210014411901c0030342543c50660540d10400180c0701500181c00420101c081601e040c00009248440d0703028503140355141091100005071940b07000c030101400d43c0c00c0100002c0c0101e0500040c01035903150511000c07242d0078168500320a000703a8249c1c107002030080da400040d2202d04c450100314050861000c080c0912010344840000c00c1d01c6444e40390982d8124400c10b03412400411111905210550182004640041500710b020101c0d44072031007802c00075900701440d90460882002080f500300032030f050800c2d0055034030403101201c1d000100115524400982030040c0940081c103241116061b003a2489901880542d908551280c04042d10703a00c00c1d105802031250140020003884000b9115104003001070081179445d8140d400e00c0b01c1d0600007160071441d0364444410500082200d00558800c1d504081902040c0b0003c10800c0101c8481c0b1480c0c07050107103800c0512140c03030303160000724096034100c881c046080c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 960962616 1250 960961366 960961381
    0x9050a0f1707060816270302030f010b062506090812010f080a121e020706170405120703050d0204030609120509010e040506010c0203060108030307081f060c0c030b04050105180706090b03 82
    0x10030007507250643d10b201b070189400800b01001b140c00e0030707203009030b0448240c1441c4040035400c0b200181c5090786c0c428400d1182079091442000c1ca48400c140300300d8207441d04409966184160303115400201e40c00e40010a0302445000b009a03079070300402d00a00c0c0c110701c81d0f290020f0039840340744014001e4103200b100200041920b001d04041c4441c0b4202044012120318066030081d04d5000ca40207600000b81098807801303081062519007801150480301810144083d004400d8103640716020840034084244012460344c8901e20280004501941d80854411202c1c50320b0442c200404021005110046c0300251459a02c001381d040320403c290b50004041e25a200140c2d055482d07220000c0d454442d8000118403800048091402a140350b21400310a40750300340a040d0f101d0010025540b100813096040001c14802c040c24030307a4034084c1c48104452600c0792242007002da412101503501c2e070f4445043c0700e80c82c41036021241d10100d110000e040414245000100000340a1140000409000c40440d440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 960963866 1250 960962616 960962627
    0x15151c15031502030c091e010f02120d0c020106051306060306060c150c0908120c1204180203151305041b0f03060209060c07080a0507051e040c09050a0f1707060816 72
    0x1000c800819080c47c56120114050140b80008042c0303001840ca8000c0743e04103800014440710035600752004a04100000314040020009401404215901c40400080c0c82e103c0c84a0040480d6901401154150400d00c004d025640150300440412090304900c4010031424102c003004003008540201b44003141d20000c680c40409600200da4034001e4a40f25052402c56000800b040d0010405550b01d004d091010055140a5480f50070810710358402c0c2a62840c0d40d5074011603226122a210040180d49071001c2420b0b404000f001c0c4034038980d40c805000c2070048903c1c40c00c4000d090b00c0c410f1110581003a401c000300c8040385c80020000e54010920091075a1408181c901c20700105044406183d035a035406a542d07440481d0940c1d4a006481300401e180c1418032130080c0c220402421504500d9080062100070101d02e1110001c0000e84180422a5920007900340d008000110103240c4440c10045400250200c07404201c4640c0d120300010804241c020001980c4041e1544100d407102c0ba04907002d586 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 960965116 1250 960963866 960963877
    0x20c0d02310b041506020606100c0813090f0b0f040c1b050705010f020f19050a02031501050109080a1e170a03020301061b050615151c15031502030c 65
    0x9680c0302881030707585650303011408510342100d050222083d80300c00c64020030054010790005070018000034480b0b080c2840c01c000300044628090030b030b101850b101d00420742c026101ca65185e41c0e002008100b4403030039014903152420688070800c6818418000180c01681c041c040c94003071a2206040c5090070700407920300f4100d001c1116100c8011001e4a17045850b450503002d61030100d002ca51104258a100250095051710140010000c002501142d18400851481c080300d8900c00c040c1d5000060b101400101210080080c840030356506010000d095540c2d0341c0c205240f10ba019404a0021824a1514801006140302c45020402c0541000d010309103070341414014031000001c17860b410b5941039000714102c4810350b4034920354010825109100401120011313000d980102c010441c0e00020400c005604035000744140c0c407044402c40001546d8209080e03900c5007c041001d00c03101c004079401010416865002c01c1d810050541d0b0f105403242d200040d121120b03580c04000213544405040031100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 960966366 1250 960965116 960965179
    0x30621120504170d0207082a0f0d05010f0b030c1509190305030a08070e030c044205030109120813060515040b10050f0d0b0a0b04060f020c0d02 63
    0x43c00c00d249101c2c1030781d031a1074040362001031250000001d44404041440105030740b1010b0100d85044041078156440003202c055a0307481401034110454954480340080d40e9a0b01c510008030b084620310324003d0403580700300507150094101840301ca140350341d641140f80f40341c4520b2004a4440340030710003250361244010100e1590003110f4102000780080000134016128007a6101d840554504e40101c0d07000c00c80c0c1c18100c1c1c056200043c00e078802d03c2c0c0b0350441109149a01144010500402d00102c00e00000202c0e10713000701d000314042c9100c5600900c1890103001d0940c000d0054803426a0b950007a98900481e60b000c21100c400400c9410034040070b80d001e101d810210900036401d10804107440c00c0034105c066072196103082e014140034241804414842201525940d00300090110400d80b5a4030007501240c40e1a030300c40505500c0d564044031903018001c1d0743c1e000c41d1550304014002d08070040c607482000039580155070404242d600c822010348600da0550707090641901d40c6100008500c4c4103500e42 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 960967616 1250 960966366 960966389
    0x7080a020420120a11041203051e030a09060609180f14060a0b03010513030815060c0610080d0302030105031c121103060a17060c162001030621120504 66
    0xc040b0301040282103000308400001041001484d903107068441c1b040c0d04c9072881b141d42d40031300000483c2c083d00c003414008201d04802181802540f0305110a81c0c0300316034201c08a81d40e4507a13001880498801c0c0006850840810040542345517800403113119026402400002601009010003141c10030804031108030fa8219100c41c10200755100150940f400c00030b000b907203000e0000d401004903400e0301d4030b8180c041c0c98141107500e8805652500800c4002c0554000408000454202d030b000c00180e445281e44807051400740d0708040179107040c5060001d40b20100f60040c001400780366004581680c8003000246c050140594804098034079071924018201194078004003d032084842c80c00851007040c0c12a5540480354482c03d51070910f100d81002c85059901c003400049800c1d002200601000310040001401d50100d40c2da09860444003a2040189814001000d20302e560180a05005070000b07040050b59009855040206500c0c142005024a1202e11203d200240a0390032a000740c0042e0803503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 960968866 1250 960967616 960967627
    0xd06090512030c04170c090103121b05030717040f0b0306270711010608100203041b030c06031404030e1e0301180b10262d0f07080a020420 61
    0xea4451340003031003080700280142c5030030341c1d611340041100007000900500c4642d459003552a2030103041c0c03440c400b03d0300b8040d00c4036161221100e60070840803800d1060b00290340d101d41901d44802d014520100302140744c141804203000070800c400035001500c1768041081d4507591443c2c00102900c40c40b0800384140720101c24010400c00c00b041041c1c1c4540996103891f0b0321307409540c4032170b030032a5450320803d03810350444c03c402942e6964580056810034000c41800428114011030b0050603020303940200c607140f034840000c000f507a130507004078441c0c852124518500c902c3c068501030a103011010300503110740c4140c20041c0c0d0100d60045050700c144c00c05002000940600b41415101140800f0140c4000d040c5da000034086e410340d1842001558038503e4201040301690302c10624840340c04168600f540116007641c1803002100c0450b00b02d072405009150085101d45440038102401210701c6030300e540000a050210b01400070706101a0f60f416200000e8003e480442c5003180b8029801900c40311400180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 960970116 1250 960968866 960968881
    0x20d0302180409120201050c191b0204060e072a0305071a0c0c010e010603020102330c0307120c140c030409020f0c0601061706040522031218020d0609051203 69
    0x10240425004c640081115440c0e20400c841c05000b01c0b0005500203030180c0d18491210301c00d40c055510190248207903600781c0780503400034050700c0e0503401481204507143e0070402400c3e4001001e520101c01c61742407800a502d000c10a110340307075800c1d0020301800750001d03c8030200840c4418816101c45070881444076803c0056100381d03a6440059148074035802e0001e0844d40c81010700c90b04e4220303503050300288111446134001c0841c60f0070840c0c118920202d8844404e00d10150308101c80d100d6003000003d15541e280054005e450301180314841c40c03059250084070103055030040201040130422210007034a40304d0940a031442d610441d04102c0b4101e002159801c10b1055101c048e01209200c641610602d0307890f05012a0066400e040903020140280c000c01d030b083c01c0c641e00c400c0d00201300a0340c1d4409400109105510000c00321411800141c849480245004051007417400c4940c19100c0700100d1072207900090802c044104000d440316640d644107800b040703402c00070500d60100c0160350039141d1030f0200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 960971223 1107 960970116 960970133
    0x8060604050906120d0c030f0503100b0309010f09201203040e070c1a0f0901020a0905040209030712080d06121505071b15110a020d0302180409 63
    0xf00100c4074200034017154540b480540c545c0f01603d01a40303002841c480f0842048810040e00b4000d1240300f8a201c207044044132400505c151301e0b81c0303c298240b0300400200411142062070804614200500503080c200342400c0f01c94404001e400d40024416440d079035258003c403e410421041c08034400c025541500818985411314145556641ea04001c14896165a1511402d1420000e43e4000300c940e07075030b115404000035400c00e124203002414441d51030117220711a540100341c0e4905914104950030044c401c0000805070031540b41081e550a50141813521541400d00902240c0302607074406604c5210786c48600000c125042c042038600804010303080d4000c010201550b80c4100c031b000c8080c00e007420301a0603d20a40301100480404880c1c0950f500c450701c82007408a0b0b40ca4503004610030780c50855505000d42c1c2d800d4003050075002400745900382c0d0fa000d031800c5280c406001c03002 = true := by decide +kernel

theorem cover : BRFrame.Cov 960791366 960971223 := by
  have h0 := BRFrame.cov_init 960791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 960791366 ≤ n) (h2 : n < 960971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
