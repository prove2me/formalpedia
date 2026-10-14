-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0937
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:12:35.509696+00:00
-- url     : https://prove2.me/submissions/21d63a08-0a94-4cf6-b275-53de4dda8e34

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 168345323 ≤ n < 168525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 168346573 1250 168345323 168345337
    0x160506070c030203030c0f0d0905060405190b04090e12030f19060b0f180109030b070e0d050a1101141602010e010c0b070315060306140405040302070b120a050603010e06010506030a02 80
    0x1017130766220310b02c45050035110101f000790000039010b10f00752030804500c40e003440001e40310000c204609041c2044144900840c000b90304203501c212000011410481074000741000f04400c100c041000c0b844100ca071070134980e03600a5640c03070f40700a1061003030071942e520100341d000c001009982881d8160401d4000a460300360700031010200c00142e002003100c26103000f4000a49080c0500741f02642140046840c0986888003810908003031012845103032045200950800000b42103280c80405a21000d090860041c01214030f9440b0300202001940c01658111140b1082c030082414080b45442d108481c0c5c1d910b220081c1044946102c85e142d50780100c01d03084045811490603240352500b1400500200380d801d40c0343d100c0814000d00025510303c2170082109860b0400210400440c505003072001400015000b10158028a140070901c00503000103011090119038414040341070155003001200c002074801b900990400c00c00100001c0f0010300381c1d0440c7d03000d40d0700760b5980e80c5801c000c00013409020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 168347823 1250 168346573 168346579
    0x160e03160e0103020a0b16020105221d09030c0318062107030f0903020c19031703010612090b07141b010b030c0108060d08070305040b0f0309010e160506070c0302 71
    0xc4085528520a00e410707050702d200351403004026480c2e600321455030240c200618003075031041d00740c43c0040d40308201030204d602c264101c07040c0a1a00e0f20f45800e8034160b0741c0260b440c541c0300009440d818407500f48515080205440550720340b105d00007060f034580c810b565142e842043c140d05500840d464050807140d075452140c01411920f01c0400f40c0c6200d01100ba64410002418140011000d69840c803c0d40f11440e8550000c2400385041c82c20b2244072803041540d06901650442e0000c08030f0b049480e9000383c10520804c541e43d0317604158000d00342d4040301240400755850103c1840008407854403490b0080b2950401c0c0e84105c01c0c42c48081c42d54854004581c5002420043c403238048941500902d11511044084e02c80d400401001112120001c941440c3e205401c294401c1c040303900340008008e000c0c040d161a625003600c2d28562000381d80002c14406c0505800420030041640a00c6140514010b080141c000c0381c6a00382c601c40c28400783d000d501c0c8628030024251007002805c0c100c05006580c09 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 168349073 1250 168347823 168347863
    0x908090d080903070506040506070f020d050610030c080606011409121b09130206090114090604060c0b0a050403090b130905040c050a08030a020601090f02162306160e03 74
    0x107403401d0841500800800d43c02441800b0021425290010a132400d441001c1c1206051029507203030a1406070042c80c0c10b0340c100200c40140d00c0456000d0003042e104800c80302c51071451920707610f01307880300d0714081e0301264940e0401801d0100c1a80d00151500512013450f074003d84421864000451200d80c07410101c00074131820110381c032035910b411b0102c6400c0200f1205003510f607480000e9400c00c0c02140d60700030341c00f8034100222035496009813450081840c01d90003083c1800c44580106010758490b400c64000700300701c0c0003900d04021000004590000302d11005002030305081c0d501034941c0c2c9082c01819400d51000c55403420062660869500402e100741c1c4c148494100b80c01c0401c40746806002d914041e00070314030041031740c9a00100311154811994000c0942da031030040e40400034180e0b0058888615000c004010b4040c401a0700f0811407801a0300403416400d83c03884c140f44c81600001801116040181081440c441050010816114508022501c003211000183c00d044085090100d040d443c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 168350323 1250 168349073 168349099
    0xb010512091501091d010203060d082208030d1805060a0b061201030b0601180f090507031b0206090c0f034206130b030303060f04061d0f010501030519090809 69
    0x191780041003a00044010380c0704154001c04410700785e00c0100d49154110341d504000d00005001d86005000780d00e411007200019050040021288a4091b400100954004200b6031405409481080c03920303800c0511080c15190b20383c0d5030781e444460044c0070701001651408205003580ba42411901c0c0c207061031801513051b40e1a4070700850400703030a50780c03a800594414201180c0380915402d210035a880c60900c8a01203142a0400703029200040c8a42c04240d2905c4180d041c081c049000311006c0d04094001e0308503850b2801049240400461449104a540b181580a40c1c0c0b004182880c0044844480c0c240022032880f0b01981d0a8801101380d1200b5401002600d4255408200c503010380021200c08504080700804d000c26510341c100215072640040010400c18900724601c0411030f074000e040400e1075550f500304080d52174847d202035030360800403004110b041c481e0006030502500090800304800c0c00e040d110315008014ac00d006160441d0b0b00d5a00c0c0c0117206415050300c02200c0018002845000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 168351573 1250 168350323 168350339
    0xd020f04090812090d1d191401080604200711030601060807110601030c06030b0d020424120809120a0b010f15030c02190602070503040b04050307090b010512091501 72
    0x441a21000c0c000109000480c12808012601d4a5040c0499607403100f881c00c4400030294031b031001040b0036401945d00780c4030700c03902408501c280000c1c4051001280000d285100241c02030800912540c0b02d02d1038540d200c0794200d006031014a1518880d8a00e94507005a4034000031004145090a030b41132140200020300603502000040c41400160f844050480e004659999185801e0000812481e00844103208441c801c1d40111401200100b440e1485150754003c03404540216a142c8140508001802c1201100040d603000400013030403085003054036034480750418040c2e00e11080c46403000001e1071401c103104100c007141c0c00c2d40000c0001e4895a48000580910303c0390b105104c4040ba80c221581d0343e0a0180c810f030b660820150700070385440301c450b04220305508814082140c0e032580c03e10104001c5502000a0000740c8109100203603150305080c1018a400c1031640b0501c200c504003c0540703483d0b41d20105803441f4403800c1d078154a250b11468140c0c1d045c0041410300d001e000c1c011b0800020058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 168352823 1250 168351573 168351577
    0x130501030302070b030c0405010c02060909090105060f18040b04031416021203090a0b0307030e071e15020d050d0609050a05040309050103060b19030b06070f021e0d020d020f040908 79
    0xa100e82c00b202c000d00e95440b41c0e150140811520310000c10002d010030071095020b403094541308c2d80b00034069443c1180781400900004015600b80145039944e100f08109820008075500c048101218030f0807903021084c240380d00000d0b0040c80140b40e40308000204017018050010001018a4003141c075031901605143c1c55044003418005034495200c024107040a10800700807142d0311080a00303c160114180000c0320340d903a00250982081540e140309500e01a6814061800600105170031816001026880201c552a85400030b0407960f041002152f1a180c000964640080d4941801074440b10440320081c0202055400141024201000c010300708006078080c51065111303460304004035450b100110103d910a01488901c0f480820045545810f4010007011500c0140341c04901b509180d00810a0b03500421400c845118486204804510300500c8210728040c403c4001d00300f51842d440003480d01c140c484400b034003071060710365190150346480c034080595510140c010f009044162519544035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 168354073 1250 168352823 168352829
    0xd0209190801150b03010b030a110d06090e070602060f01170a150b01080a0509070302040b0604090606090609060201020f160c0b0a0e04050c0408060420190617040816030e130501 78
    0x803042c0703d408203030f41507440c040d00e05031101a00201d0456540080700d6000300014540c170065000140080d03143d800da6070003050058000c01401140031404954024641000394020f042036401007010000090902c041d01411103081c005140207440280900d2801c090020300c0282c01030000b90480c0e06c20002e560060030b400036080c1c6c3c84498541d14010f0003411030308c06440c01d03246c681222301c0030000f600c0c298000c00286040103201d2490260340e280404115001c903800070004c42d601c1d40c000c05c030035500000694014182400294600340e00129194440d101e040c4101c008000c5801d10a001c0c400d48241040140a24100c41079507000c41410142400d007564249071310039800c210010398405060800da4045901d020010149500c0c2c5960300c100b00d002120150520241c0c2818000300c0342c0d141c010061420b18680681d050503410004000c04c107103070020001072040118403e0100082412023182c01040300781c0b443c030111440d13900e0111030103980120690351240c0100d2004440c02d550303500290407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 168355323 1250 168354073 168354101
    0x301a04030314060a050a062708070303080a020712050304050a051005010504060f0e0403080c1309020306040e0609060c031b0c07050f0d0f020906041d0c011803080d0209190801 77
    0x4141d880383c0030480070889034041c1c1170304003c080004100d03143c0512440c40b00b00d449186502c45441c000c07480905288a00d03440b6000581c0b000c04104145a0072500c5e10b9040b000403031055150148a1b2151203402ca2120741d03a50400600000103400d0001c14401c100129600006642d02503103444601400380c40c0a01603103100390b150180019410544080410443d00040110021603880351410340f40340b200200707080c804900400210200340c8003c00c04502074060400016224100785c0188402c4501c2440c0740c480341d40c00340090014040c40041d0707256012401c8403146135203a6451781d00d981040c154802c04119001c000c030b8440c9040c50085200d90680301c040d03070400070601f5290200100c1c412200d402800240c0000000d03005801c00481c072a50041c030240020a204099190018400845220303040c6960413200c40f60600e903900c151415142890003081314090f030708540380c11100d403040f4000490915400104050251104145070064140d00c491421761280e90f040e04a02812072a016002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 168356573 1250 168355323 168355361
    0x1d0612040c080f0c04020f0f0309070f09050408090d0519080304120e0a090c170705070b01050a060f050304050f0d020a1101021911030115090e0601301a040303 70
    0x42d01c80000141d8000c8040e040c401040021104018000250700542c000c40c180c030b0040008541842103140290301a600c000010120b0914050300104165440d410418010b4107100a22010423201410380307004d604100c1d0b894003400c005261040c5404e04000740a6894000960000c003402000350181d81301d01d00581140781d0940c5400b804079994509410311603400600910b0500c50a0075940c8250048083d13410103080c90027401108000c3e80d1012200b41001070b10000300ca004005c0305500041c0100415210094414100170018010710301501c802000c12030040005402d01004210303640c00e001c0c00d602910304043c01d03100001e44aa5440300280c881c0166403044c8c031030035480064450b50720b201c41507400c141d0710b9481c0e07a0b0310401c002c6003815542c199202d031440103414440c2d8280e20000c00c121500005c900015009681c03c000d01644000c09020028540390700750709130a02c4406510340f844000d5910001980f4208a900c0e5000d4070040e40400c0074010841059016804130070021001c4140328 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 168357823 1250 168356573 168356579
    0x606020a200114030712050a0b1c0209010902130e0718060228031206080c01030f091a060111010f0b1c0203120a05040302060708040501031d0606011d0612040c 70
    0x200c0303518520905a0300141d08003083c040e1440ea0100030315013041d07086c0342c02401d190702c50b0001e005aa40540e40d02100c690b8880e600d450310702e052a41c10f0403000302c5c441c41d848440850340029140140511408a8660300000d940040590055401002d8000e200c014030847c10b100900404c00e1000303003119600c0c420303903900101c4c186c0e00000791400090718160104031180000c05601a441d824410300b00c0911128103088081c80700203001d402e001c0d2122000030302d8802c6c0424001800c1d18001505440c6e820714003580180810500645903865242c050802e10342c90321a240122011010303444204459481c0c2400c5000c240910782200840c0750303084442e0701c10070100c40b070201b6100c030304000025813503800383e00c4040c201700403076014003000041c43c01c0c920f08081d580c4d00410055848218120b50b0840002800c0c00b256802d48500c203d0601c2203010a00c03003841d1b80702c1541c0d849801412142c18420144003108143c42080141141d03600c1c0500700946a0140b22641950144143c1701241e000c2210203000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 168359073 1250 168357823 168357863
    0xa0f03050d0e0f10020604050d090e040809010c02090a09170301140f03011506030f0e01092a090609050421050409051009141506130506030a0f0606020a 67
    0x1055a8104001e0321081c464404240e5210b403205022680100980c8403082043ea110341d032000207900d1903005003000346040e240083c1410f140401c200f00f484401081840100c408144d401d510036070280e21a41da6014a00040c0c409000c2c0d808000d6219244201b0400201c00d00e800022040d4400d461010312011080200702d04c5002c03d00624540001740300d88000c032880c00e081103a031403e001070000609181041641c10780610941c0240e80880c1e00e0342180c681e500f60611170400c0031042e0b0300c0200700758041955640c0a00203000c0b01c542e500031021000d0004101d074851020010710020b201004481e48e2030314600081d0900310350075100c482c0000d4000c0c40c582d020800311a0040025507030b40d4500b40c2001e00c1403000b020050500032185101c003030007141c130100d04d103e103e110020248a901c3d540c9080141201112200100140644401d0000300c0300940e0080d1428251803085134034903282e03615103100d60003c1c1802d01500a501e414403900051868010a00380b0169010f20b40c4141d0f58956494a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 168360323 1250 168359073 168359099
    0x709080f070e040f1a0a02120a0c05030c070602040503010c120507090b0d1a0301020a0c0519020306180c0a0603021c0b0307060c03110f0106170d020706050c07050a0e01050a 76
    0x1030840048440c000040000c4d007103212511800d841039090034210468400c9034046020200c03031032080c076580003861804410801800c1c5a009644030800d01000700803100040542c04050801c100c10080855028100400c07501034a0140c1000f5001304020340c201c8400401c0100d02d440d5010105140c44003154006101c0d181c442d0a4400b035860161400000c4650340300240034100b04502c0c00d90001d9400540ca5400f80010802c11407036940701c1d400402d09003043c80c10180d4081541134540e00a42e0b03404016180482d4142c0c1c0301d030106445440c80e484081c0c1c8a414401c0c0d05000d541c0c850040c00000c2405c64040d405803008040102914408042d0000c1440880d20702400c05503055000200400240c1d106001c1d450146202e03103440481010401241803501000c15540d241c5079440b0042445011828070005c00b02c55225402402c1c80c0c56120800707911101c09001c5c80701000000140d11640703210800c0a50700400018011001c465950464408079000a00402d031083c01400c0c0001485041204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 168361573 1250 168360323 168360329
    0x51303051c0504050307061119050a09080102070b0f010806070e1306120303060f09020703092c0c030613020f03070804021f080a1802031207241a062b0e060709080f07 73
    0x59074180309c50f0940800e60b101d803c050390714001c20001001c003249080d82070014002c958400ca24460090074560605081e0b07500580002007164456400c00405540c01040f142c401070040c1e58101c99068525100b00241c2001d803c50b174030200d880300a000806d58194082000c0382c071440d4403403240079298003035002a4420481b000c3c0000356540303414400380789015500c0410400c048820700d01c00c01680016143c0c414200c0c0c40c030702c4d4004040108250750401d1040d040c5d405c0c074242c02c2141340c2103a204000303030310f4007014100ca410010040c0010302192141468201030701c00310f00c11703a0703c465600e0700000d12350001215581c220505100b404894030422080c034080380c5a008004e00040304a04d2400c0d0030981100d2170603500c01c021b440c0660700000d030381801000300304c1c511300c00800d210000800100f200900180040e0144204201d2980144010448006c1151000d0500065104c41000c0d16000d45005c0b140c00031140200814402c41d650001c455500303c03180b00054030140303d0305d052003513220030483c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 168362823 1250 168361573 168361597
    0x603090c2e031e06030305070b0105030307031d03071a070203010b03030a140c030f0712030506190909150e0a03021504030e01050f0d060305060106030b04051303051c05040503070611 80
    0x1110039108a80207810003c4030a4541c0c0e4289140740041c42d0500075a05998019070200e80700081440034802c00144080c00750030150011031510146503002071a002196503011402d03caa6619260580c0c0c0c24041030000b0560840ca0300c0020081d40100c100c039034401c1034100e209604e4034005040c90704020060b100070303080a0321354500600d19009134020300e40c0079450780750a60200300300e4504510980e901418100b0f0003944d00440312103003041d000d0112440030f485a44244040101d103c40004006001c0042c0c80043d507010850324143d2500003400c1007812100903855080c400c0000c100000042e050301203c0c001c0c0d08071900c0400e400d940c800d02c0b00050300c0203800030300c0241c0742c02650b50140c801401c070021840b0b100380c42c0c5030b8030001a41c2124002c2c1c05c1181c0135040000100103055043c0140700c0c42f050308440c00c0145080c088090a07241c0c05682c0c000f0300f4404003086410b8012911003a500c640b18004905000b24900b41ca00355849601184084849a15255a0001d0060080f0695030303000162 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 168364073 1250 168362823 168362899
    0x40b2202130801360b01030308070306050301052e03020901091b0804030206011a0c01050a1a01050a170406021e040e07030204140d14070803040306061706010b030a09020603090c 78
    0x38501000c3c1c0c0018503500e003038503c00051300001a5114800d90700860080d600c8521070300740080001c0c2070b603456500c030274402e070b06040a001141d43c00910750000641304050030919900c900c0350b54201c0d014580c1c00654032000120001400c041641c000205107440010161a48804000c054606d200c0955010340168811001031041500700c111804c8503c0c000101035080061201c0f000d400d41d0000c880d20b001e56601c540e64807040120740c221070a1003181c00d003041c90500f21504001890781e0104141525801c602001140502507180d04071021807002d100300700040d080c0807075508619070280c810074030403e03454000540101d200c2d2003600d05960200d84100403e00d100c00401c80d00d841c2c411030a50340c01090030b90800404d88204040801000201c0203075480714594145282110000d6001040c18141d865400c507049a0110307660b41910b041e0510940c5940300c0c0500302c001000c10b5040250020000002e0054011000613440703208030003261030607800d5269240d640003421110b621507407010743c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 168365323 1250 168364073 168364121
    0x71403040e0a1802060a030f06050a05030d030b13090b01030507060318121701060908160b0405060f0d050a02032a1c0b030a0b040507060206060303030402040b2202130801 75
    0x42c0c11034200d100f2240440e0103200c8140c0c0014a030b680c04404802e01299032494040c0c468025405000024101141e0b04000180743c01c1c0403039114902c140110040655400390b401c17403a950605201c54030481003108002c122400d00e4034065028081c041500ca9114034000051030900c0b901540400300001c000b0440091030030381e03810040c040010410414010380c0d1080c0942c100b2411481b5000b01016920003940c00c0c0b5184c20715082c403100c0729031161010343e030319014003001401e001140c0c02c0707035016240740340e50718405014000d035030203080b1669600701d050006000c1d100c526070b000b0718018140c21640c405030103000c0c600915448074207203402290b0f030410b0140d0300c01b03594028008a40c81150f80000300300c03500c810703000a0500f000443c044400400b45424031042c01002c104010247c0340781c1c0010720340ca0a09000090342c07800b008000078421500d030740303c0041d684c5515043c3c08610085071426180104078083d81c0c0c01035002005c100faa01e00d041d58001940c140b0500482e41c4250100c1320003100d00c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 168366573 1250 168365323 168365341
    0x6151e030f02010e220c0e0307050f060d1a0909010e12031807090e01110a0207291902010b15250f050f010b040501080c040c091703071403040e 63
    0x501c0070082e81400782c1d400c3d408201c2d4450104035000d420800c0c20602c0c90039030f107003010402c852500b00c03c0410017084481070f003041e0310300046040a45a040351001c6400c0f003614001540d43c03241e14502c1c20308505049071500c05030754021401d40c014800b110291203690ba4041407908a503920621200d05900a0902c130b40100c845600440e005940018500c4c1f242c40410f12451a00505901c8080c0079582d030800d0030104082841004c4010202004940c5885000e28000f96224014001c24841080b44400c00001450741581400c901010b54020380c3c407812511000b00182100010170000b650a045c0741c10450715200d811240f40c48040c0f070a40742420304d0b050201e460b00607202c002110040012540c0c40100700d007003141e055140e120b14014110401b0500301a82500e100c4001c0b98020303804c1c440103000401021803800700130003060b28001a40e000c2c481c0112400c0f615070344180c8031140032694cc2100008007000804140c1d0040d4200840c1c40c000c800740e41c0d1742e80b18070b110b035030440400c4d0b07001b05607400c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 168367823 1250 168366573 168366593
    0x2032202130f02040b0703090f0b0705100f0f0903020f100c1205060301090c030c0303090e070507020418020a0b0a0207140916050f030708061002010e1c02070b0706151e03 75
    0xa82c2c50b005050036101c50150b1560341c4404010740c08500e15175010420344d140403104c44082c1500003400360408105075181640c038285980310100c015110400c4182c1030815911017044070049020502032441c00e410069142ca402c01c10804e0280250502c41d40301d90014016000d410420369130360144a054624460010078004c4e00083e890b540f03035802a00411000000711014600079242101d40c0d40c603503d0090700f4200d080d03000c00c00c900741c40010041240d800c03c0551b81159010345000c0b030240e41e462400d032150003003101c0c025405000742c80040f42480284c400b4011001e9503400b29030100f616030128003103241540c44503c0d071000440c4002084044010500c0c2607031001420070506081e6020210300e0b0340c3e0022914100014070000401030546005045609121300900003000b240c5d040440042e281c65148032481601c10941041904151003001020010305400702d446403201c076030f0714000c009020180c50401558a12040100b01254040c14111180308030110b4a01014510360700c0104074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 168369073 1250 168367823 168367841
    0xc0302071e12111903080a0c1a04060e010b040614061c060608070e1002060103080f0706050405060f010608010602060105041a03010e070905071701120c080a05010203220213 76
    0x1045004a00103560111240c0740802c0e03602c6a034804090b141c401c3c080c4810031403020f1248000d001d5030311041001c030b0034000413603088011a192144100a46003042c009500c000f1105021507400700080200307000103907001003c07840d032290003406418860010002622030b180561001200461804419450010000c048041d400100e81360f0041e0181d029504030f50443d0300c48000704800208202c002903002203c28600e00d02114a606031407000138000b0b595a8050100610400c00018803012010095056842583c0d0089060189241500d00151201c000b0750360081070810200000c076181e402842030a0503281c00394010030140c0c0c60042088058080e00301000d04c1241e100720032050b00e031001e0046000300c40c902e80c0104403241c50a46d154085405c02000c8401300310769260210006049018039030b046803001c0300811415645420841c2142d485540702651031f03c154406181041019009588030307814403000c003101580703142d5507140e40403142c40c00213602c0000d041c1480c80054055010060b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 168370323 1250 168369073 168369119
    0x605130b0307140309010b2e0305070516150b06030c0703030507050d05040b060109090506010207180608031201030605010f05100c030c0b091f0606051615110a0e010c030207 76
    0xb100c00c3c000105a2a0320a43d00c000c0a651660105072150030300c0c0c9100048200e10215548041030464018200103082110324030406803940003203004076206005603444a4042c420750001404149040429030303030100703280340504e81004610440e40c034045040e82d10840715000158500b40e0103a07030840c001d010040541060007402e02840341401c900e071045c41e108612610400c095030070458005020303844e0b294000c00071103007031a007081090b99001c01e0b80d104550000101d0008803100243c22006040740b600320b00b080d1702c00401c5c600c1d224180700c0c140d94101c034021501005681d88860303400d44500324a0240c40c0c4c01280303800b05614618031901603425414042e14250003050302c030350b03600112a0004d50b500c00650b0b0140c0929100e03690150114100000281c0003000a14903180028025010b0314500c09000c9410b945010280310300c0712281300a000b0020420000b44404c2654042e6a0f00312010500005404501099895004007482112190160000c1c05018540040300e03904a0b21840001d01c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 168371573 1250 168370323 168370337
    0x209090f0a0f02030c0c101514060d020a030b10050c06060105180d08190e090a050c0f030a1506030b010c02150409050f0109050c03040c15050403020d0b0406060605130b0307 76
    0xc4090f8030145024400300e44c0416522152403c3c1c40d80f0742481c480704410a5898844141c0c50b41c0486034018040f41e00468003039510a03011000a25a4003440010441c19400040e00428171503040d805101041c10464502008422500c002c84481c01440e104008640c03164000c10075035030041018040c481036101a02c4104081d80e400b080300014450011201c1c0c0300b021455215117054403954100c4400503107804500c000c0f4100c0051050040500745401e11503446c40401d112140c0340c01140c0c02c014041e0905030b0750b0700302036030588002d200342c504141c00000718030340100f00c0510038054803444c50016551124503c00e15001c0104c0b141e082a401030300401c04210000e144055409014810382281e404880950b2600035128259503000780218144042041040f0004100141c0070054480300c5c1d0000161a2003402d0a503124429a00065488540448a8010030076105c603024820740c8183c2007070144a6403842c1c1507034280249800562130054000c0284001c01500d03001c0d552020141c40d01c50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 168372823 1250 168371573 168371591
    0x15030203161a1b0d02010c08090a03021207140a030504081b01021f2c070b07120315030c240e0a14030a0c030f0b070c0209060108070c0b0a06180209090f0a 68
    0x9407610013400c0d0100c1c0542d45401c2c601e8400e0390068010f5600c5000b100c0609102c0082d50780080d110300c4d00d02c08407080d1443c041a1041807003a8000546501c0c502e44080b03810491003400c011b0000c0d0400e2103001d40610854903425100c0c1c1e4000000d07008100d068000300003481c0b42084040f075142202120301080343e0382e141e00c0340300c000d4040c40d00c80c400084681c5102c855403850440b6030034240184c2081200110401c03002c0c0006414001060010f00305240020301c0030800c0e0890603030b0310410340c4043d1441110300340c0030905144078503012100e4886682d0000600003d15015102e4076600703506107501c0b194600e8100151000d20040c1404404010300342e4643e0041c503600c0d1500e40342280c1043d00c5044054030306a08001030541116040360720303030804d11030b8100b13a030340000c4011800800c039504018000340802c0c4954005d000b841d4005a0000c801c1c13400b1b1812801c00310080406200342241c0c42c0e00001c007414101480d1017250080c000c0035156942da03a0740e100441101c5900680030645107a550701000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 168374073 1250 168372823 168372877
    0x6060602060f06010f2a06110706060e0103081b010b04020f0901020c03011e0f0e03031509070c0206030402120a050111091503041505180f0d091d0601030b060c0115030203161a 77
    0x80c03e4001a021123440d141d00f02801c0c0403086801c1500310380ca20800100c01403021400748001c2c0e403c5002030748041c100407281d4035900303400341030342e41c10700d40e00f0a0012609102d060714940181c0f491038000e070708560310303c810f090401d0300707907200d4103401f204400c0c01c403034500d12000540d0000d002d105111800030919132582d082c0c59140d54400c0b43c1e2160200300c510110810b07460045401e5410001901c0d0031550050140c000407030903c0054070003032051040c0f0413110700346002070041c00b0031260880002c108903003e140d600905039101c0c48016210724604a640c0040700f00a000707176409580c101c040f200c4000740c1c03141010000c0401810040c0d4110001c7c1180c04004030800103642080e03034004c080d020070380d00c03030401038482c51198100381e0342c500310405d150000b8000003511940c003c2c802d19010074210008008131b0218894026030740c44550900a0324030b407000c982944101124829012641102c000142850280c9210700610010511442007205801811009041d0552100d8420f030310490100c401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 168375323 1250 168374073 168374081
    0x20f0d260c06151206152103070b040b010909050604020613030203070611010b12030904050c04090608030408100207030206070c050304050a030501051f0501141606060602060f06010f2a06 82
    0x3150f4070308800b019407281c01d03007441c24024000700c0b81e41c00280090309002d541400c02d902d00c400070500a00c981d800280306846030015803482c0000c00d000b520341d2541c0741e080914800004440c01e503042543d8030000544c1c1710451003415400c64010001d0540c0c0e03103a07513007040314980c88110729100b945090440840540d40911507040107140070307210400d81039a020000760a50b901c2425151161000c80762400c5102d0b4040200c4007641009c0b18001825075580300e410303059008981106a250340f0f08800071512401c000000d00c01d4890800c110303595285402841e2060b40310b0900000c0068210802003514207020304016009680719000b0790707040680f50700109003400e44036441503071160344901c2030080441041d1071040075641691000f408040c14040043e00c2603a041c4d052810710400001d0f201035800300d851103044000e0b40711a041c00f02542ea034100035a40c00d8165075844a10101748041940e66002e001401c004043c82e4440e00948081c4825600a0044820045020100700060f41b0002a12441 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 168376573 1250 168375323 168375331
    0x80c0a081603080c010b1c050118020f01050d0f060803090406150c080c070305011404020910051e190e04151404060c170403030c12110d09020310020a020703020f0d260c06 75
    0x311f40c0410746480c01c0c12801d40308100c591035046030080c08201c0158540004802540c0820f00784160b0b1040004c2600008041d4a00381413420361800c00d000c18542c00120090002c4402110180400c9489005d011480707000c1c0b20015002c80c0000354108009107a01010300540c071501004e0300e625a81c1c0303880303c1c2d003581d220882841e00c0c007058404100c218508040043c3d00b0800c0f24605840c1c1ca402d0502044441e003100003030464a000d580c4100c2e0301c0d580c90400350101200203040301d09807559507003e10300c51050243c6d4111081120707803000c0560707900d15101d51420b214072a005075081c2d88454440c00000c1c2610350010040014085203840d90041c0b01c0304040c020b5100e5600001c10010905004120b00040321040b2241414003484515288807001902c090041745040020b40c00308134400a490f040103404020a03150001c2001c2c07801070340219210301100c4c02541e4401000e0780702c2c0308105005201c58030080100203103d104544000e24180c0d070400d81911010b0151502a11126040c94104111 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 168377823 1250 168376573 168376609
    0x9020303040e0c04090e06070e0f0d150212130f061104230405070e0306011a071b210b1303090b1305040b01020102160308040201050d020301080c0a081603080c010b 72
    0x1303030400000d142031180aa8401c035441c0500424105400300404101054034141c1c8a0b00884580c0c6406564044034030305420303401641c010f0024803c500081c00b94020030421100301007100300251620b103403e120720340c0f0342c0d03440802c140100d1f03480d540d514000e0000c551740440720b00c0709200c0844c0103040301c8913284020072080038501c6000b03d94030810058803c024142e4080141c1843da0007082d80b000516541503815503600c1c0000019682c034901c181e03000d0500d02401c2c00d030140c082c2d0030700c3c00c84100d071b4001940c10300360103240c2a101d04542804140c1d07200d8002003003c440711b000650f007102d226681e80307081d51092900c50075135a500d031800c60207500b100b14000003148040e0003c002d6840d003840383c940486000c0c00250f00b0a043c42210403600c0b91104009414409014005811a84a05c0880c0c3c07406400040454030f0b035071035401042d07480380074441e07941c0154031131000400c1c030350000120000036a010f003018400c07503400c555a000094010100c00c890640d00c0d1809020240c1d00c841344805040030007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 168379073 1250 168377823 168377827
    0x150912060f0c03021303080c030c030f03011d0402090705030601022b020106050a030f08160b01030c03120c0c090e0307080a020a02181b0702120a0c170601080d0309020303040e0c 78
    0x400701c111004001e4980c28940304103d4519a515111040b50407250045070041e100c9071030303007511421449444070107c400d00000901204849500e0040c41c1a54560308a201c0b20403002c801643c0d0040c42904c010303620814050009208038410401142e004406105880c40c01c091014410040318400c44541000e01c08490001c810690910503d80149000c45941400c0c81c95501d41e0080c007a1440006003980d100000c0101d140c500050000341500d9001552400b03e60f03403410403441c207081c01e000490300d0903d206050400c5c244038074801c0461b181c01c09a000c00003807030049080f00a0888011910a82c0418020f000214038110042c1411110980140015078100c0c0b04114650790050921170707214071220140301c41240b036a107a240941c40c0120700960b4505250000510100c444103601c0305038401e141c100404c111541c0c00d000d00719200b46003449508405035039032580703402c024090500e183d071020200a0245129800207c40e080c00a42070b0303460700c6c4d1140c3c1e14404890044840301000100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 168380323 1250 168379073 168379091
    0x3090c040b18160212090a0302010f02030f031003030806030309100305060d02030a0809030628150e0a0b010e030304120b0a02121305070b0f09010819060806040218040c15091206 78
    0x140010805a940b068003a446c0185110000d4485080c17808040d0400c8450119000082d00070001c5a65181c2a81521916403030704030a100e0001403a80000c5001620380d1012640c542000000d8800351b44008040f060401d110441c101d000b08401007034280c1c40801c132400e2070050b0310240001c00b6181d014411f0903580701e1400c0145881d20302c000e801041c0e501d010990141d102010160b5034149080b400d170000c503a4141c41e0794611842c02980c2c101c25080da41003024405910019808808401001e0305c0c0e04c091160000201910780c0184d2217203102000e40b01849200240e440d0b480d8a5000700b203030342d006007000d202d0950342c403c11608075003201400707032210800c4051040c200f0074100107140c3c10000529024220320100707071502841c003400d41401100e4006c60b00a50388210f01c0426264460030801c0490b90761200140d071b4400503a41640a403003548001c41003500880303629803085802c25040942c00e0300d803451881540659444270030801c082c0a0010684180c465000034126001300c0e004503540c58 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 168381573 1250 168380323 168380327
    0xf0a0509010b060d14070f20240708010504050105030a06050912070c0f090203100b031003050d05070c050609060301120f050a0b0f090f190804150801080d02010203090c040b1816 78
    0x74081d0120741840f02c3c1040e4109010390003004688a480503503026940700701020708080c0b270900da507040c114030001e4400358a08a03041c0c0002480c4549039035030707070300d043c59a0710f00034403085030745c01e0080c82c1d0190031841000000c1001500481d400c03540c41d004840c03035503200e250603a880380c001460854036415020020002600340b02c16040190584903021451800e00c3c8400230056030300352060f0b2081c841e0100000301c074007003680240d400664002c0e0075200d041502c00001000c0e03500c010f01c01c48000c0702401d40030456080142c180c03445800c0c050b005501d90303404c0c01180c080012980320200d8904c66035202990005500b0b00c80410030754810505c0040d00c0c05c021080e030000c020010321074203040d400203410032060100011070b4420700100b0f10300f000406e5074504240707540e48945d4200003141a0600c0d00c1c40401c55000071114105d8403088161034000340842c3e030403070a038407095800210941c0141c100c141d80745010740c000c5101da02c0041104400e41e83c1d0302c0d903000c00d0341c1044070071343e038020000480e2041140d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 168382823 1250 168381573 168381611
    0x90f020903060106110c010305150409060b0a090e030421060212060913050c010f140309060405010c0507030503011a070b040f11010e150c010e0703050703030905090f0a0509010b060d 80
    0x16060110b003005c94040c1c020740c1c07225406071310350406071582c010408180c5001081806040c0150007400440b4642c1000e2001d041456200780c020014030300300050b0340c21180704219100460f04080c2d85420b1400f080ca036107075590300c280e81040b8010491550f001640c107100828034035007400100c42d49450404100000e91038010a5800f030b47e10321000b00070000350040f401d04103400c1e09083c8901c000000d440c04560100c00135280c480e103140c000042c8140c4030000112688074a120740028010031888001c2151a4060440c0040210780244018065106c0052007074502002c540c140c1e41c00d20001e6111590384002c2a1421340b03c10280303015542c00d000011041d40c038125001e0030718491390801400855011040c140702035030700400128900002e0a02034005424850380321084555481c2c81e4103240351607400d2807208602054021200103641d042228129200d40c410110700c1c0d805a0340c15034000c0c05850700500d030350925540c400b4071401311b5032608090040218946000945418006e103444600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 168384073 1250 168382823 168382829
    0x1902040b040615030c030b0d061a100914060702060a03050403090b0f0708090d020a0602030417010c050702120f010c05180406030503030c070c0b0307030c030b010c17090109090f0209030601 83
    0x118141036040c4990401c8500d00000040c40e80b50010300c0c0c1790100c00c11001030070781445480d40481c1080703500e0b0500105400c90402060401d18040c2070b10140010441c4000b440d0300400c0100d26070700010092088104201c100010000d0402e91820300c42c1e41c005840d95100c80d01a4004c6a5180c01307210a040d0300610b80c0000d055503040507031411352030114000042c028100024054600001c00004e6a151250711220340707940504401f00e00c03600d0303400c003075144e4001d0b000c3d20b01d0903411020030700307040c52050203402000c41d940c1e198545810202d0b006d20102c0116043e00c15024400c402d440c0200c0356091042d5a1004032980d40c450f110f02c034100d4604c40490b80c502c200c9120720f09000b03082c0049040070044a400480d41111546c0c3c030300342840c10881484542e07025640c0c00001000f045503068042e004030017610078640d001c0050005803030054032202c014680c007801e040c000f110182c03d201a09001407092705014141070307e449585500b110700ba10405c0d4100030529401281c4214541020007102d0b000d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 168385323 1250 168384073 168384079
    0xb070c0603180206090f010e03030d020a0f050315062209060906120209070305042613080a0b01090e01060509040503120c0f070803040c03081204031e0503271902040b 73
    0xc0842c0d02c3d000202207000c0c02d000e20344208044040c00307401c2e80c05420446000040034043ea602c50f0428615140250801c0c1c02e680301051141c85084d4804c1d00c43c1048a1180502140071204998030f4001e00c01c0b02d401503040b01c2c000e421085010a00b14401c5000c2c1001448645804910300382041001c406541d070f40d5100d290b08520740c18550b40160740d280103040d8086003514000070242e6950600440c0956001090240900c90079047c00040a1500051503e5145002d000b500555aa40c03219500c041078500a0501c02100380188101003041c3c000c404590402c0e000440e070251a80c002800c0c0e65800e6a00f04c4d0709520002d402c2d4400810303264415403103235401c00400c1c10129845004c030703400e1180100003010080e00100140410042c039412401458014500d540c481c00071040e01500b94034113031801d4022803036141c4528030070080d0541c0c4034a4000a42d8502c9e0442d12059581c074a40d4000482000b21808202102c114842c4100503040c851810343c2110701c848030702c500600c011202c54440c0303580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 168386573 1250 168385323 168385361
    0x15060e0402120f0907120f02091308090906030c0a330f121806050901110405100503040507080d020d0e061810211e0b0a1a040b070c0603 60
    0x42c114603050860f8401c0c031181540c11035507100c0000d0f900782910b58000300081c07104050480b060040f811901d03400300d0b201340c40c1d5030090349a0070106140381040c83c4004240074010011785010741481603010f03800c035402504035800c210600c0c2c00030310600f01301d400440b03000b051024041c0c0c600e088007510364407080ca07121524030000b540d1300c1c1c010241c3c112210310409000c155459504c09840c282d001d410b40e40040420f110882850b8a0142c0c050310003034a21500c19802d00465030f014070246002c68080315402089802c509146520030f0f2440d4000400650300d5020f20007000400410038022441d0040865000e450074407450a030203062144840710450081000388040421000754070003c00d00c29100300d50100151400883c100c0ea100c100500c80d02d049182c100d107810303402d41e15401224403020050390549205c00c014028038121031190000300d901c00c0003103500300003020000c90650081400380e0030003407809444041624995029900c1101c1c4a200c03100308100701d56143c41604038854011440704 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 168387823 1250 168386573 168386587
    0x90c17151b030408040308191d060901030915020d0c0f09050306060405040501021303080d180804051507051501050901050d0b0106180518010e1305190206090415060e0402 75
    0x68601076044914211a400c00800306003401810030aa038011039203d40050b95990302043d008141203003803401c0c1c1d40071401c800c4071100750901d04141010262000360000303042600c10310044001e0108154203031980046045c20086074050760005101c0a100d038000410b541c180380d4002403e2260562a2000708117800c8820300c9242c3c1c0104071213800c44401c0310007090540780c5082c00d0340248241a03002d00ea020761a0000010480c00e4000f03410030369041e410811505040c2200c2c41c940722041c000003481e8850400c070512181c44d08520801d00000e107101c03a14140310403030340c80a00d0240c0000c01d8160b10f0b101f15004000c0d5103424054180580415905141c000e0515940c200c0d00d0030040c09100c0030300c040307441070040c00b003a4400310320020a07000f4555804c040e102443d4401504083c0103d20180001c400000c0309003030101c40b69036442f50301c840207019184030960842c500b106500c40803039010100300100754083d5518014101c81c0100d200308502454500b05000d400720020101d40e5020b5030041c4000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 168389073 1250 168387823 168387841
    0xb030403090e040602090d240b2b0b01090213090b030618010e031c05061c11010306180c11120403171204140105010506090604120303090c1715 63
    0x1e08111015400720020030b88452034141c1c0a40a2200900d4004584504080601c02074016031240c04c0844504010300e03494500f81c000580f5a11411306030040d540c50340c4c41900c221104180c0848d404c0c4c049042a10307032000d603610000700200703a0154001c242c020402041c0b01e9000d80c0d64100810340900e0412680001a008c2911054000c2041c0e0001c203c0000900d0b4502d029000341001c0101d01c07007505d580b10046607800c0366441d0340308c1081d07072100d140500003a05800c28090a00c5141c06484442030300b591035503903e441607144001c24a04064850324006800c1e1003051078010708115011011868240c110402403009103c00d44550266000303010400000341d050003203906581d082203000c81e809611800d1610380d0b1182c03602c9242d65101c518108024065010205016818101700902050340da800400429001d0403081951016041004114010400880017881442420086444002600c90b03080420356580400001c141c20b034030b60503c060043c031a08560b0741da5203042141c10b0805402c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 168390323 1250 168389073 168389087
    0x60302010e0906030c120d03051f15110604060c18030c0510170c0306031b03070608130f030206070f140f07051203040318050627010309061b090b030403 67
    0x1415010b4008400865650746050081910034500548081000c03850011881d44c0c0318994242000024600000b040e804a0702126030105441c42c030303500c481d00900388400691244d642e00d4500080c05545403110308005001d101c19403255000340c100042d210780103a0058511604035100c03039032119100b042440064005907054040c0c42c02583c42c1400d4030b50900098564407602c2c41460700156044082184d0f0f180000300940c4950002d034143c1d40e117107e9003c4550030080c4000d5440d945508008005d004842c400c0354030b40c0c0e010000d0b0307000001300b200b03d440e51880d64501610990040c1c001d2800c00c25042d8200c2002182004607143c071001c8070440003601c841ca4024034901004240000400c4002c3c0001084035816014000e5041581d030b040c07914024204842d46400c4034100d5103038100014803441e0a10075100300c00d10301c1c80d200c4d02d01d5004c4006004940026090141070503a254152070202e1524442c2d0391440c01149004050703421101b0f0050480c1043c1d920400045e8010800c1100099202803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 168391573 1250 168390323 168390347
    0xf0305070801210b041b0b0c0a03030c141c0b0d0201091a090a08030a0813020306041115040e091c1b060618020d050702160506090d05010e030d0b0406030201 69
    0xc8152999440599240050303000030000b070101144d100c1444107203c0c61641c2e085d0100e11070711004811a0380e80c1141e007140d015001c2d240485402800400d0f0109000fa0020340d81001d071458100032198844074030744026004002c12005005d20b20800000c41c02c0c06120394507024504444220990000b0750001303040402c1c5001d02c0d071100d00c00911032141603d02e1025075055613402010082400c0d101c8400316601d03044070203100d0000b89030300c01080003a840e0302008000c45401901414460742c03151101c80c50210103000040d00400b0341000c90b60341a100e02d01038005070170203248078801030400078070461404a00c001c41070350030041440305200c510b410003160080710a6460f01e6a060011a003481c41c0103001503400307668200318422207214210700c0c40d8010900c501002800f0807058403010b00803655103039041100030402e9980c680c24051841d02e0009884100350050030829020031594071182521064503654500b980045410b40c11b48850b030085c20b40000701540d041111515680000740180b088403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 168392823 1250 168391573 168391589
    0x509060c16110d030c1a01031104090c0503010e070807050f0303071502040f15180b090f06071406010e07020d051b2410050a05060703080702031b030403030f0305070801 74
    0x30702070800300034070000e607000e8040c4001c011155060303860601030a20b5281880072105004204003000200401c1541141030720b8014000360410240c14003840002d020581c81954184510040020560380901400135a0380111000e00411850004170f20300c0d064203600035902c151401c20a40380c00d901c0000c16100d202ea00070f003266404c1d071400440c51009100342d070440c1135004a100300c003081d6003110f050011071f5030807a1355600c000c01c0c21400760b01d03c3c1c660f95030041d80080b40c420803c11000340b602c400741110210004011038980b4140e130341c40520b03900d4900302c0c2e1090798005200410000920180d12544400280041c1004240c43e41006200384160b000240300c00c82c5203821044210010482a261030b4080360644041e54440191081d040c00d013110b241401c0c489d14400440d00c0d0130a007515a04844024100a041000c540d400b81e4003c5002460801180700a0002120b440c5c21140412030a0154502071982c071401c50400409812611403d0b5007498103240a02445550260240f8110355800d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 168394073 1250 168392823 168392857
    0x30d02010e06040f0c080601080109120206074d0c060a020d0810080a03020606130902060301030b0619030c030b0c03011409040203030f0f04150206040c0611070506030f0702010509060c 81
    0x92814951482c5281c01406c0903216500010582d403405500040844d4051001d010400141450499903841c0440d02d2000040b5a02c01e2810a4401e0b00342001c0040358689442e502c1c0005d100c484c0e00000703264200750703003a00341030000c081000d03806024650103c201942c8031031074101004400381d07403500b0011082081190480008010034141800d031005802a20241c1c2c4002100c0e050080d520042950340310b1141d0940d9140d4003e0340d006101c0d412466501402c80da0443c0e1854071241034103940100f003143c1003142c000b403c81340d8402c448003202c091807003184840511429800c1c04030104000502c0d951841c1003c2006100c50018038040301c0e00b010084461110550355440800c0c00d41c002d44400d8601c001000c00c1c00c0300e05004980c00b0b04140d541400c003540c400c1602d080226590b03e000d80340504115040307030b0280300662085001c0c4003282c82c0d110031603001aa44901043e010f034411240b2507071106000d0140000c10f603083c0a41904035418400030140c50401e019100075501c1072000c0f243c60113500f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 168395323 1250 168394073 168394103
    0xa0501020c0916140304060912022e061e090f0b13020a030b0405070c0201080f0103031b0618030309020910030506011502010e0703050303040510020a050910110109060b030d02010e0604 81
    0x4201c480130742803490722202ca910390601e454084040d11401808071109603040500f62050348c800522010a00c0b0422101c9000100107185072a03112000d04214110503142d20003c0351071020f03544202070780c12004141c0c491103031404902d54201c81d8941070900c00ea5091255645403a80c0380c05101d008400d00410051742c03201002001e90080845807601c40d00b0505000030880043c0e04010040d1302d141c000c1e240d28113540d46403203420003000070900008020400c03031900c521021301c1807440003090314800d61340000c40c5a601c000e80307447c044281d0b2045002903218401d150450400c244a10742000e02d1160120195003903940e8030b9202c1c0014081e400302d42c0355040d44041840c1c402d4114407007084e1590705403210f8036101c2c1460750300d0350310455065425104500742120390748005d100b1100d01d20341c1c959800e030030000300004209044455900306001c005554041003034803482841000041841110000b030404003680074903082000031542c01e015039141240b61a80204045070351544503601c4100d510304220 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 168396573 1250 168395323 168395327
    0x1080304060c11130e030307030c0201022503050f0c0c0a090902030705060f040e1302040b030a030813030c0b0a0504110a0e0c070c0b0307020303100f03050a030311040506070807020a0501020c0916 86
    0x641c85064600504081720340418080110041d0b0040040d96014170958940300d00613821703442003020140c004080380b562180b00301c204cc90035120481c80b84c54501d143c516a028141d50542018078800080d8015480a000c2d500c3d00c402d043c40205505501444a071000b07400007603c61100707100b003038080e0700d00042d0b40300c1e440c04600407100500340355901801c00341044498003148400c81d0400702e0281d4030b0700c00080f4003440c0019001c00c180750f041d904c0d41300c50383e01c900b42201c811200d10310071828050309103206e40020301c0303c030308441c4a44800d2000017468501703410910a403640c903c440c0c0d40a01c44000092021801c0c00807440d80c1301400140450f601c2c8418503040710781c1c1080fa444004440c1c000302c01c0c429581d0b0b001c001140669000304894080c1900c940d0040312020b001d200041480d44850080c80009000c0d401c900d09400f00710107518102952100440c2ca203900101c0c0442e000c24001403508114608078103080041d080a1002700142840d44001c284080c05c0a0314401d0845060080408554 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 168397823 1250 168396573 168396589
    0x7110a050402070b01030c0b190309021314040302060703061a0705070f0608070801050f0a0e09100c021f05070e0d050f19020315070f1b05030c0303010e01080304060c11 74
    0xc90301510841d41d91400341000407820000303002c11510340e807402000040c0c40307a9000685105030f051203040b141000e440c1c1c001350000c114201040303030401190383c0014039001c52842494503034814902205c0362403400f450700904142d0010400700c14903140072410722194001c0c164284801c1412148a40c0da500303d810081d2605142d54000c0c5c89000b0340000c0422030a40c072403402030041c140e0f6182c5c440c150340c03621f04014603804101c0c0a650040841a0100318051222080b0f6401642c1d40302560050100807207018140e0340c20042c100056070018060070700707050026024400c4001c03074160401c101c1c01d2000e402010b010303074606001d00c00e5810f51007400c1403144c10303c4bc0c8002c1c0407a40007100d129624186500c260381112a00036842801640440900020049109403049200d076884041808150b02c00b80c81c50000d260000044038811540d00c000542c00300000c12230b2290060043da229803400044494184058206940c507800c10702081140076001110014100e80c05500d00300e4003005c03200410030703030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 168399073 1250 168397823 168397829
    0x3080601021b1005040b180a060507050616110d020d180e0f060a0e0f100902031003080d0e07030f050f0a0c030b07030b0310090201030b030a03080c0f0c030c030307020601050a050607110a 82
    0x6c45400110343c206c4a00e0705000b0700807034505a600c142155559107080c0c605005510010b880c42d00030300001a05040d10581450b1500f0325070a2107016020b46205580c68940e04014403c0582d028040026406400c141d013040314122a40361406260704013481c140c07500c00094a8664114400d00214080da550800020003074807214120400514040346001c20341c0d4001d03250f94407000701c5050003080c1590540210f030311900d86108900e0106286a41d0380a0951015090240560b50b598038000098810301c966402076008024084001e4003e061003402c281d081d800c4050b06511031301d4100300050075011040c2c1240c4d000321481102d139032100c40990140160000881d0300d0f014401c00306580440e00e46c01000f50314001e80c1c0030409106007906040c0c1c3e6007003441c03001d00852428000504a14406402411111b070000100780c00d08042100040ca16041b25103032403d90341010040060b05541004041d0041c0700c12500020392528050101d0414890070401615800409001e003410342c07901d03c40300c401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 168400323 1250 168399073 168399089
    0x405040f0515010e0f041133090a08010606081b1204050f010f0203010b340305180913060f0603020604080a15060303050423091303080601021b100504 66
    0x800001980c1201d18000301340200c034101c000d11070204451705103030041a40300d540c1c00346e604015201684204a0b10103101d42c5072401d07021a9098044079001e0640000a01a582e40f00c540e8844e4401810881c01c0c0714076130032001c1c040c4e1501004110142e8001205500401142c041c584040020040885035114130000b010b5031002c020180301c100000000c0c480c0d5038400e243c008100455003080e0010503484284030b0b40616840c182b080c501c0e00e001d164007011400000c0402c28a0750a0481d0b0040d03003903403e141003600898400b1625011404842240e104030340b200b00c607440c40e940b03440140080d058141250103490595620300b0119001002d40c85000a95002880c80781c8441d40c905a03c3d948540f000380460303561040c0c8d0310500450750f0074000d010669078981c903900e003010700781320148000040510004031031094140d500c0710b56448503038000303008061500b07001c00d0200180c00d0281c6002c40c040c1010f41150311400b1492660126071300e40a100e00021906a07904425020007102e09007d81c0d005860 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 168401573 1250 168400323 168400333
    0xe0301090804091a09071101020d0e060921040317090a14130605090f09070902031501090b0a080135030a1e0807051b1603061d0a020405040f05 63
    0x600c001c0201810450344419801d010000c071144030f440240d8a0004215009105000424100f40c003c40043c0100300d071040005041c6102c145158058031003039408407100d41c0000c03051101c0c0c41000e0000099171190582403159041640728200f00502c1244809007107407620350064402d4403d10000c81d044048003c2c80c1d0a9402c0c1c9644810113410b02c903840d0144524445500e000385180c150190404603480140001c4241e41c4070f680f00f03590114014290200e901613000e0226845401c1e10146004021021607070450030340b103c00240040b5050b03001406084400d01451a90315400281f1a041d942c090b02e1102c00503000c4003001d0302c0c48072070580e000b02001e540c0e07904c0e04255400002a01d820100c50380c07884042c1610000c0748454203507031030a440c002981c880019148a000342c004042c2d030001420075100e1000d42c496036504100302502d040e411174141500400601203203005810074580702c080f1562064401702c0358180e8510254600034007407921000082c0c01e00004803100c42d031058001003964 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 168402823 1250 168401573 168401591
    0x803130c05030d030510120f0f0501020405120a0302120c06060d020111120c010c030c0f0e010e120109060b09060f040b18010e01031e020a062f07050102010e0d0206010b0a0e0301 78
    0x500500300850f110480ea00100c030340000d100c2c500c600007d04030794200440301c240843c0c0d0785035075000b2414460140c913203640030000007075180c44045080418030340f0754014180c9071304203190090074100c0d018200c8540c1c2005010344807078020045005600030108030303503040c44401141b005994640503042084954003841c0107045400c6c0000000700400e496490080140742c212800540c100c03900c80c04140c000400702c200040c1e00394000c181c04c03404500f05042071002d89080d90000744140b80d86000d00390060351126411400c00056000350500e0920488500340145401400f00b40d180c07090010703042c810394031444040300545a2410290711104105e15145403903868502d903804100081c8012101d44080008030b00d00042a081001031603a80149094000391038205c08481d031030140302c0310300c1106891002241c07100784d0710241d44200c0d81056000d440c415281400180c2142c2c01104c10140c1904510003402c41c881e40803620f50705484e0b0f1012442d869240c0d0002c119022041c0b102420f80541c40c0c69514 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 168404073 1250 168402823 168402827
    0x190f0509031c1b140706050a0c0807020a1e110409080903060703051302040b04020c060702010b01110a080d050c19050409060605070b0a0f0b032a030a0803130c05030d 73
    0x50254151125212080036881e070030a004680e0140309512040c40703030f6000c801e540c80c4a1800600b416040b80780040c208482c0d921603d040701c07810390308084c4c01d559a903841588650052080c940c02034641c00940248022a204c81c2c060007452141d0581d40780c00600702108100760f0030100004218082d2042001d13942c54545140540e000030307000c0e4031030711a0b82c00280c0b403503100780512072040382414001d0205150703a07400c3c000940801804140d0194090184111814040000c1841801a5800842c0440d21400050300c1052004c000d0315a0750000348039130010580050441e0304045214000142c19511510355610358010203580141c141e0003940c241201c43c1c1d0003000f030300a071040c02104111b203540e1503200380c41038410580003c00010140b40003c025080030b61201208001c1c060300071901c810080300080c140641502d00e50340f08000c07110510300400b44500a00c20b180c000394000e00c030151440d107c6070000d000040098010b0314800d00c03040100905281080300816024040324004550b038240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 168405323 1250 168404073 168404077
    0x30f050105100905060c010e07030b0f09071a0d1b0320091c060b181006030203010303120b0102030919091b02340b0c0d02031305040203060d0803010e0f0907030308190f050903 77
    0xcc0d80c9a450140c20100346214004035981c800c5501400d240111407400c0d00003010345800c10140d00400f16594500001c00c100100c174400310f0402159070000341800d03070000c1c1c800031305070b00f04074580c0400c014480d0004603140d0302c045100e900d5400340c0c3c03001550b520340b0f070002c0600060351a40e90020011001d40c000c1100c0302e003840340102070f84000303060040d4950504400700c0c003003480090000785035803d500907408030035030000d020303200c06205030b07443e00c200907010450071180d01e42d0385049108a104204691800352242094441c5d10445000c0750407140b0b8030003980d54a00c801201004a00d403403c4224007984400240541d42944004200c074a544900c0c0726005d030040c01d03a0040500076006428409031012044070520100e0f1365244402e40d0034041407200035040100303625081019032517000085050031000d18000c10901d0850700c100d2808004c5140050700280c0b081880790f00c0b0f44002e00010b508003e600394490300c1d040707200312120f040301c20740300c0a0862110440600b51400051085201004c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 168406573 1250 168405323 168405331
    0x10f030906181506151b03090509010609030c0f0321120903080103030815210106050a09020703020d21020a0e131a0102060c0f070c03080307030f050105100905060c010e07030b 77
    0x9010040d0558580d14607032a10301c0d9503c1180002c40c8900c0c030749081d46000106c604494080c0c40c282c1d0300d058650010402e0310a00f80c210740c010500c452010000c002180c0208030160800c003072555041c07455659010310092000254000307036100301c0c0442c88810320035140000c451300c0c000c038248130242c10303801c0c05040d9000a00054002444150000b0041192030318400e0410300d002d04599445019681403200d140710040c4c44171305554031501c000405503500c601140140602410040e51803c80380340c043d01c0d1212840d841c40c24800800800340f40e501c06140140c1030710011840140c0c0d2003524074411900380241c03030312181e80414201d808684503c0e00f81e01110302d072240907241341384445a034001a6074520b0115000c0b101c003c01040411b150002910241c50071501c50607016005c0c0340c807036075040c04940048131001c0010703a45500362100400c0601541d80107000c03c0d2010036810486d400003c1072680140240c90003403000051800c0051400d6000d060a01043d4042da10007a45a1405d4180c0c0314040d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 168407823 1250 168406573 168406613
    0x501030317071704021201090803042d05070303140d021305040e0a02030a0f03020c270105061804090c120309091505030613061103090307050d020c010f03090618 71
    0x90001007401c0e016001c03040d0002c06840d14200f07103540360707800c00044604104d00d15643d9502c2d04000030000301031501135800303a8803e0074000c00b07101c0145d407940c500852200307200c08c0d0b00f800624400c010030000f142450035240c051802000d140b81c00403c05059200300458408454800a0141d0700040080000815620304460a07c450599880070554401d00d00030080d516800c1352803d4000100795041d1484018400c2c019a088404580c000401c0000224020290102c07500c0744401c102e40315861050140400700c0c2e842c1d081c814501d0414203000b190004050007241c1d03420b004000d0090301046030000f8401004890313150308c076500e0010203d2642c5c1c80b404003001d0a10011042c44580ca03102182134034400b50040005548814804006404192056a46603170750000f0351702009a00e002148602d0f5148001c0d5a150386a243c4146000d604190703100454001c6040000c5607a03202051100000051030007054440042c108075001348085030304600e07441c4031851002c082106c2c0c1d0b03d0160140e1100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 168409073 1250 168407823 168407867
    0xb1e0d0f0e030414090a060b0a0801030605060105041503020a020f0d021b0d020f0d0303112107020f0304060c1406070306051513050d0609061d07240f110105010303 72
    0x30704101641c90149000d0590707009180c00c0200d045040c1010303e5584030401c0d82c800300c0c240b9a144000c003a1640520381900020700204014001e202c03641c02441d030080c000b80b0700b176485c0515200c8554200400903016804260300080c0520482d44200991140c0055101c1580c019803200342019644e03101d2051085100d45607080e82c00c605240c1701c1c0d410030200d07401411000f03139000f1250070001400c2d0f481c8021000d0660740c003e01694160303082d02520700b000141081c0520034400664614503010000c240c0710455215045140301f160001c01521b003101c1c0f1070709100306c0001641c0340900511601c1c0c6280c88581c0315040803c460b19915401c0401220825148a241c9140016444c05207101e903008445500b89581e0b003c10150030105801c0000c3c0c2d000740301c005095030b41a40c4620a940f071500140501500a80302461000c6050245c500101196418104900c00c00d20032183e1300301001c2d40003400d00076640780c088240350040c92031035044280c0744001c00542d03840f460060900751000c81c5240030f20440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 168410323 1250 168409073 168409091
    0x90a020307181d0d0810090f09060e0102030402011d0d0515070f050a050405090703140f04120201060509150a0e0c040603060b0f0d0905121b010b09040c0b1e0d0f 71
    0x215040c4420300c0314543c00504003c50700982c00740c81e089070107403003140c000d80b84100000c0c00c0a0244103400315540c070310f5000310303010710f090a04a0556880200c1086281d10410512006030f030490f240d00c01c0b50a0034400029000e05190000303580c001a118041c14038002c1344402c2600c0700744c0000701c9200d8580341e100c00c00a044140710488060196280030f10108008010900451415540d000c0c0d006130607240100d20300784017802680395142c0549030b141103100310505000402180000100c2c805105100030414585030100098100724040c0c0030010292207411400750300c0d2288900070300a02522050440c442c00c2c00600801039034060b02c140d00000c1c0c600003021032050b8040701250050000c42d100f950510403424241c60050034101400c031503d00c14250698002c0d4100710180052001c100d00305c580240b05107002500792030700404e949100e200385c401003200046410450006135100210300507120400c1407a070585166112050700c988200100d1750b02241d01080c1c1094100f082e09039010b01c42101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 168411573 1250 168410323 168410351
    0x31e03040e010b130b0c030409091a010501031118040e0607092115020d060806011401030501080c03150a150b0903010f0b03060a091a100f0f030506060108090a02030718 74
    0x1d10031604c5142030140c1420010308400030090036607281d1380c034103581c585507540c00300f00200c0c1c404031402c4581d5401c0c01840540030200703140703442c0100000e007018000a180805040140c0c030904044c01d4914a0f1296241d07031544840e4170080c42c401e1780b4030072076145040c060005804100d092144583c1112600406140809a9036140310b80f07640c041c0038145103c03200201040a9003064003501516030703860f40000354120082210354000c2c202804118540002000010306458058000590b1640011041c00084e100010305603a81503403d0807039140e40c1c071000d0042002d4007210722168041c1040e000e0205111200074018414031800701c0003004001b00c00c240c10029a580030718202d61680107040003071190a0b1a41040042900c65451402031019825100f035580100ba03440c1d2010845102080c85000e07400d01d02d0f0784c054500645400c84042c91591420354520000b4200342c10442c2500200d5403e0a0030040070031314643c028240c605070380d180d00207404140030000b015640d0900b0705c02e40d00a009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 168412823 1250 168411573 168411577
    0x914030705030a2001050106030b1c050304052101020f0306010f080411090a0f05011415030c0703031107020303071109180304150e0310020705010506010311030f06031e03040e010b 79
    0x3030707100e03014608104070700c80c080c0c9000d000014034100400c0d216210001078402881898042e2070701d81c40c000341108640f4144286000b20405803d010042e20762201c0220303c001055804903001115460072002d40703a020f8052091803400d49646a60002c0f89920040402e0740266108200a99070141c00c90b80d00c01d01290603040c2554050940e0100150480103804d02c0500154403c0b40c032003000c140215080342d8502115802d80c4840e000901580c1d0340c1d040b510f4000c21420415049590087c00c1d414003400b040380c43e200e06c200041c01d2698403540f451030000c20106865500b40c00405032070b00c6400c903040c01c007040018005c0c054880c0340744100103401500340710f4045a042c0300e844002d504181c01d001d9a00d8801414000c2d180c1404401110b400c1241d4040118030313500c41d00b695001d6200c00d86841d1150a54030041c00007410b05043c02100d40c000c213a40c00aa9910154204201015440c3e41011905101000410407004e0203214090103039880300100510403601f04480c0d0040301d81c1d80d403845c102c00e8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 168414073 1250 168412823 168412837
    0x9010302061c020c070806011505040303050315041119030e12090105090a030516080d09060804030f090e181002090f06031f240801061b0303060302090109091403 71
    0x840428444090402d64100c9890000880403800500e0f200790500500d20b0095164001c030816032100c801400074012144a080c1d40450a007000c40c28131b0b043d55800b400c5804010501036014144602191495849812520700944084d0440d540d41d10029002540c07010400700400119050400c00681031000180744500070354021012828640e03070b600111780d0b40d8010514030b03074064032111020000c03032814440c04019003c151011000c0526018005040800c0d0481850600c03002003000c0103925000380d642540702e0381c1031410700d8001e03c602100361101c0d500c0340c1103003000031005010003900103400f941c603a8034805904210b51440c151510210168840c030040c1c10382120b0102c0300d10040e030a2000246802c014403890a1a1596090141c0c066902160b4800040c050a05c0304200c0c00d00000c101ca4041743d002032401c5d408030760502c10050042c40c4824180d01807124074000c46802d01d4401d80c0031201440c0d00511001c401e580d241400c401030300c80c132031042c1e40c0380f80d11801d0101d03501c0f0008200c07105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 168415323 1250 168414073 168414079
    0x4090809090702150a0b19080606190501090501140733050108030403110312030702011515080c0a0201020f0d060501090f3501090b18030703140f07020a030605070e09010302 76
    0x1d42da49214172038026065840d141c07604003400c1c160601e6440380381101c002c060885080102043c2c40e001d010441480d40c134110808100c04051810b003c1ca9911404900541d0400c2c20b042403504c09000c01096a4844d181015003120311400030186d181d0642d02421088100ca0b13108500c030480b5200560088038005c7c42014500da10401040001030948020108520401002e40d101c10544114445060307204441e4200107035590a00544000381c02c0443c60050103000c030b0400728401040301e02a011200c0540303442c1c2b04410104a80e00014801d4044555409520101d05d0701d8088615402c00034000360702440307020544031038020511080040901c0201e88a5110441e002500703070552901600310070004410152903200d85c00704070a0700340550b0342c0702e81c4a01d07250150b9241004003112800c08072180c02c00300b6003003041084040382d03005031100c20800c440714800d555030041c0301d100d400030311a9a03030088d0002c01a8400000b80090782d80b042d48220302c980c4486000401940401035108002d01000754 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 168416573 1250 168415323 168415363
    0xf080603030a1d01021207060915051612060801150e150109060c0302010f091103060709260f12030a0f0506010903080a030b060c0106080c060705031b0c04090809090702 74
    0x201e03058110316021643c0e806005072502110b0568000100364400c650640e8580c0d16507260350100081444602c05c1c50403104400c0001e81007400100001618a032181420050f0820525440300c0c22903101d030000784200740081202c102000d605281c0a9254031421104003408030009201c0264074040c400b196005a5030704101d40d0900a00f92241d044824060301150741c2c0f03821030584103959102d800d00c031901444221006518050405141c444000d00c07140412040748403c0090180010706101030501807450000e1020032001c000c0d00d0408525402c800c40d10925000d0800c140c3e1180c010342c0102022481884140800c02c038100c01d8031410307200980064800802040400d1140016162141d0145004220604040b00040482d0070190ba102610395441c0000c104030101000021050801561140d0810b8400c1c2c840507244c2c040c5089026010100703c00703c0d8010a0f051106021002c0000e2007005001910708103050550002104036004000c0f90000c640d0b16400000e00602d141c50745c0300f00c06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 168417823 1250 168416573 168416597
    0x1030201021507050c030f030a0c0905010f0c050a0204090f15060308030609090f0604110117190209010903081c0b09040b0412030e0109080901020d0801030c140607120f080603030a 79
    0x100419038001d20420800000380078111720034100303000034880311406000458076420544600001c440701100000e00303001150b2010400c50b60480c8510040c104541400d5021402500380f450511210800c000e60040c41e0000c0368040101c0030010b00c18041c0208440d04106050302c030074004656042c00040d101e00010320008056142064500c1d620092a905541110302c00903000f51801605803400c1324640c00613804074015582c040e2290500c4042450344401c14100f81504180b000f15403420101d5164001400607001e9010b004a80019544003103400d0f030b07418444690860b0004885200c4400d0350401d4801282c5203491040d250186401c001c0500300c81e12070b030b52150b11034031265a9090038140c4840d08500079000a01c81d255100e805040c61503a40c2908800080c1010503180c14401404140c00060000c03804072030b000003e4905600107884c2201070080001c480f4010600c0050030360015200c105459580010142c80f266003030f8a40024a0b115001055100e0017100c042c1400901158201 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 168419073 1250 168417823 168417853
    0x30703050604081b0d0e0103051b041809020603100306061a030f100f03060e0d0315030f05030708040801022d0a20010c0816030c090b03041406160201050f0103020102 73
    0x4144ca104c040d8490445403220341c0c1024108000d100951000c01c0016004111658050155a6001510841140e0114195008103000c0d014a000b0140006e03050021002c004101d0f9101d180c4598004009603124944254841d003c00f105020407170340036080000000c0c0c440c00000d621031540810740340c90307030842d984c0b00c21442030444010095060710368201d00c0011510142c10b1060040e41c0146404510412040b01c424507003003403807608004062a10480c03941c0c582040310301c03e050302d42c0310300d454141190604280f80f85008500303000d842c40400160018140d42d05600078401c001e40c0d288450000c10380071650799100408050041e040c04000c010302480a80300c0c201030455011214a1031054503007402641d801c481c801c8407603c0120f84503901b0b01c80748968101c00c0d001200c0c211702d018001155011401840310b00385201d2506410404400f150030891a544d907240074294090441d03417146422303256034a0403a81080d00d08050351030403001c0784d00700c07005e100300ca07050344d4043c7c00070010344100c1209 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 168420323 1250 168419073 168419077
    0x806100306050a110a020a02042417010b0316181505040207020103021207050c1b01170a0f0c081b0301050906010c050316060c0806041509240b1803070305060408 71
    0x40c018400da9580761610060b1813071018000c440610b5006084a100b41d03c1400300711036401c0411880045440c072600702011584c000c180a99940c42480510308110b910128094229554142d90500844001829450029503070b1421640800d200c02001807040c0b03003110458002c00400001030b007403248248164282038006001d46441031400606e0502c03105855141050159200000110006512903901c0303010000141345082c00350500c614655000c0010740008070358401c80c4141c0090300b0010340c4444681e404104042c540d280c080c0000c402800e0002e1104004880c0c0700340b80c1c4080200c5c12611490107081e603040c4d80c0040c00c000350070b4590400549080d05080403c0f1001e04c42000041d5405003250b107240a81da120f0100890344815040d00a40003410080c640c6009a10308008520318410325144101180c2c07228100007400d04540c281855140c803803100901d40d250381d110b00081c6801d08140200203940407031b01d203008450417a104058a6000c207200240480d84500c001c03a002c900b8040c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 168421573 1250 168420323 168420331
    0x9140904030e1507060b10360e07020604051b032a12060114010f0807030b010e03011a0f120703030e0607060501080f100b100c050106080609030a09080610030605 71
    0x88541442007144644403d0741c0d101040031600142c80741170254080c105484040c0c0030039814204405040714070070b402030f07011440c41941d0741061a03043d50008404414644880a04124a0500c032585441100a0342c1d8603001c0da800c541c81d21845070b8040540070109121011410b00501400c0c8100c83c20b840300d6a5008001c990b0020214407034403960541d0755001e410480d01d42d0302c4019105541c07400144425440301c0100b42ca040c090900048aa240d91154186500120f14200007804004200048501e05180d206c0035800d50310380190024003c090005260323024104940c100d050425400c144038800071103c41e00203680d8403603002030000901402c02c41e540c00c0d07806400d9030b0074420103407601c40c140c07442a8003590b40d9030040c80e00507449440501604054207200c0740705000803000c00000c02d505013420b40004081000421011003001400e4000c480100900c0e4110707070344c908202070410b859038402d140200102d1030402c00090303400b0000c40c800d407103413121501c84400b8500d1030b01d0759000303400010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 168422823 1250 168421573 168421579
    0x40603050a0b060a09060201060602070e040b130b07020109050f0706050724060902030412110705101707030506011b080a03020c0f060906101a030402040c0504090509030a09140904030e 81
    0x12854481c3c1e1181c02c09048450241c0d83c88916442c03130500f02131700319003158000d00c0454004840c00e20407405046829a042540081c003d44203a50301d00b1194680c010440740107018406500c14001c24581c15003007070520900880c01d03112180100e004190740d424040c852000458010311900340411185e440c030b081c030380001e4050b02e0038064a00302d41500f1581290410220580d001c41440306102c040440380a1400c0d850500f6917070012100f0345544da80056108842c070646080192050f210301c81c0504454681d100100d03a5247d003400721018010300380491380540000c0c2c04c142807502000701024418855604031400780c0c50980842000c40180d40503500d00b4656124056103c0c0c1e242104001c403074424040340300540351030300f0000f40c00390303400324140e121ba40044000680018000b0070001100e400c90750490f0001004c0f1408101664030b4003482d4031001384d03075141808203e90344c4004001000c407a0ba42d80d4031040207a4440b08020319110801107800e80001444001600013801035043c03003c408001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 168424073 1250 168422823 168422831
    0x30a14070803070602040311030a0c0902130e010305010902090601170708060d080a03140c0705120306120d050c06180a030c05030d0c09051504031214211515040603050a 74
    0x840d181491076000d8541154002d40c001b07020418001c0380c88110401c082c00314050320b5040c1141d1140240542c5030301494500b80d500050403001e0a05840c61540106203c00a9481c290381d41d08005000b024407400a80c011902f0b40002041e41d84078810741a075150a00b5440201901c2d10501110401d10042050f508410000346540105001030045e000e01610f40d50082407000913801a1042e00c5009060005510414800c91001441c003083c000381e1004000140c64036542c445000803460b140030b2410400301d02030f02e041c03200a560f001005001403030014044482d1921551401418128042040c0c425504621420ba0000e485620780d14000c80c041c0f0100c9083c402c2020040d0100c404208406000c1000c0f440d040285045c0380035603240d440203101c1e09038242072442e155412900403007400c2104008503001d00000d14600078003602c502c4209003031441403041e5401c980926041060b903040f4240c80c5900c000d0034003860030308001c00300c07082076101c80c03030909180107419009010f003c0c1803d0100b68407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 168425323 1250 168424073 168424079
    0x10b030c0304030c060203151018030b090c061903060501090f181e09030e2e02030f030c090f0901032a120b01061101050606040b0912101d030405030a1407 68
    0x10600240d40160411034201c42008040000c0010085002784048140400041030180801032100110212500007604400d1a5910707501e00b8184174100e81056407140d00820526904400040740b141c84490354ac4007004443d440780015106009603102d144010030070340d0303000d1103185023155880c0742d407404050000c60540c5910500301c10324620280030808044e03a9400850905911460010849200361a00384646d416402401200f0301d04000000e1001c1070f0040c4e082c1b03000d1081088450039982c0203c0e903610ba013003540d9001015440703410000e02c50340002c0080c3c8800e1411140007030490354081901c44803c5000180255050050f60b9015544500c01d640015081404000e0344079807449041c003ca01c41d03040c9075000e0071942480712407003001d07850b01e010000141c4a20084900350f441c030f21585500d405c0340000080815201503003c225602400700310003040b02c5140c101070688125031075001032940e0410900703656409244911541503028880903804216101c05048154274902c0a0b200c074162 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 168426573 1250 168425323 168425333
    0xf060b06090409240510031b0305030c070906051c0b060609030604050601151b03080a020f0c010e0c0607150e0102120106020c030d030506030a021210091a0708010b030c0304030c 78
    0x72040c441a1580c0c80c0c2201c0d00021500f60f00030403080b1130b81c3c0a40411840c10310702c0000000c0c0515000041400c5100c100c1206801c148404035801151301c501241d680d449811211a03c524107841402e9000e803c11001052601d0219080b1200d000c4040524502038001c0d190141780c0d85000c0c020303d420260410086020740c80505c41188168000c6d4018000340d458400c2c228000c0c0c080c0f8a0143c208680c600030440b201c00540c1908000340d4240c5409401500c85164110003413048401141291400007000e581d07910040d0003000854031081e0607662501a10000c0c0015032091190040c0317000030300c2c0005c020b26089030f4021820380310301500050400c11102e0800c6200f01007a0043c1025074899070200f500342c42c00704450508200c5501e4280100d0a01c2004242c1d034014054009115603104000c5101003a4100803103005944110814016500705040419030705d01806207044c106040c007000100d00d14041c0721514100c501e2940342a1455980007021061600301134002c0b8100001918280c010030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 168427823 1250 168426573 168426581
    0xc0a03140c2d0f0610050103060f180209130903020609010203090d0c060e0109050714100f27060e090a05070804020d0f0c0e01090e0105090c04020a0e06040b0a0801120f060b060904 79
    0x200382c04010180c1d820300c40b00c0580340c1701046e03102a0415003400020f211021520820303d040b0b41060252407182c19042d0f14070400b0380a1046070f250001442d03a440c05000e20141c1017120994000d4090340c40307946031010500d0903403108846c104001d600444e509805070b4400c40841d0462801180002508594a08154251040c03110240c42540c8683d100740543d08040000b00c1503c5800c450201000c08a103030f014188402c814078080602c840d01420142c10700e5031451083c0000d1408207a003030020b0310b9170409088180f01085080c0500600400a0580c40482c4030f0980100c065440e0803031035179180c0d400c20482e00c41e9040300f100e841c082d410140001070032005080c07000e0301083c1251980b641c1002690300032901075940401a580c1488144230941e030020800a524460940380035a40c3d00140c05e00307031204a00409480e421160005000070010700e003c020b00b2070340784030366503029259a032078418282c0c2e450300f82406408481c081c5040c00010b0704650008a212001414050400e000780c00050215 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 168429073 1250 168427823 168427843
    0x5090402070503191d040b0d060606050406020f0123060102100501090504110d03121a03060c07030f080903030a050712020309160906030b0a0507020309060c0a03140c2d 74
    0x26500102e01d03180030480803e24000d003030003030f8170700b400d095451194111200403000c0103683c015a1348151300411522881c4c031030307080f880c5c10840c1441455920349006240c0c0d4418420328005025441102a00031010301503c41038201400d004e41a511945043c085002c001822a505520030a03654401d61000c2c0d0082c0e40c001c1000c9040001c4070b02c0c0c2070401d80700403820300201e2407103010070030030200009401007140d0380c020a00001c00180b04080c00d541c0b00070050640c00c0194580304500802c01000a07010013410358500c299641c14105900342c00565410005480c0002e030342d0418000610094459804254445003c0c0f401d00b1907860088500c604a034020390720f0342c803075400003a401d115107400446650010241510308102080c915145d0742603107034007c2c01d000b81041c0c590380800c070803c1c400c0043d42c0700c680009118956400701203441e42ea64504242d01180410152903084404604542c10748011110346006003260880035620008410321a910700c142680020201850400d0100a84808 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 168430323 1250 168429073 168429083
    0x121611042426150a0209042c0105040f1101020703021008100e070e060711151c020301050f09090a170c0118050309010f2a031d031c0509040207 63
    0x60241400c000449411002d5500390007129519000d9031030102c0011a6691030075020026205503d81d80c2c41200607208040c081c81d40b10741001140d03a0b08440e10076801c201e001245510135002d8103851169403d0b214116809021400900f041d1400705110380c0f281000004144181d07100261664005100c102c090340000e00065111010001c0250040030160043c0060260050702c40ca030180d0014540f450030310940c1d00409020030072608001c032034446080c0040000b8400603420f400c2c0305015506420029078401410400308034454503106d1442203070f040e118050860701c19000e1080038405580741c090900d03442441121082000b10b10782e007003080300040c030082500c1c2d40c0340280a01d5900303583c0d25000c4542c06501103460354001400020031100424400e00300f40c821030310389002c01d951401d010300400d000704012041e11510308203006602c0348464803980721650708500203089850030690102c1c107290180e000a004540c1120340c0303980340b1501d07101480e14601d0304a84801040990704040401c0b56 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 168431573 1250 168430323 168430391
    0x605010e010e0a1b05070c03080d0e120310061409030a0302010b0111010b0904030807090e040c090f0506130209280501031b140d02190c030212161104 66
    0x88107585005125400121449050041810046024140b00c14a040110901c00c0001b084010032144160281c010354100c03c1c007641391031b1009000400340008201145150182c000000501950201981d018000424403480c1c1d0508108040c0e4400c40b02e0034a0b40807418062110800d503a0b01045804d0040784680d0011805a0f02c0c039002501300030000721014626418840d6540d4542c44041e01d082e0302541500c1c00401e00e4440d250305035809405a04604201c040540800080c4100c01505200700d501540040203603601c0c5c1c0c5450400c90300d0686819034046081101c9080c554440d4010700074264004000d59407142c0001c40700d60f040ba243e410b48a0346060248010040740d80c0510440b011540440c016014403e05000002c00100d40d11076240005100800c103020041c140f5811b64a080800c0240c4000d80528048040c010410b502030440051160b14410001000c400c01074598400d500d2030018603681050b0303542d4503481088114103070450742e41d035400b400019400c0b0041100c5550052500c2c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 168432823 1250 168431573 168431579
    0x70503030a0b090a110708070807021504030209010e0601081b0409020a0e120102031303050a0e09010b0c070b0f070b15150307030608030f0405040e070504050114010305060d030e010f0504030605010e01 88
    0xf4481d5008107003128841c07a00c40701c51100003036201259040f0343c1c4031255655400051034001401e0185407c040d41120214002e143c654410030002c2082c0c81c0201d4513440d41c2d030f985805100b00d07600100c5480b8002082c00d408908020b14120010b45884002032a1504143c3ca03036041c0c500301c0c0c000220410000700d40500e030031940e0805560186444000200a5103140307491414203200007000c41c001001c004d40000d540c001540300b400c800d00d01c0c01005008681303035607407400c120305e103a08140300c24002e601441400140c018003010881c0c0986082e4005c1505280107a2034244403198010708101c07094447e000c4000060340d6050300380c044002c603801666100c1c140124010100c44a54000d891190b008018900f01d292101c010340742103c0080f10b010407208058034200381440596409150458240000401c0e2131001244010450101381d90421031540d0305070401022103584140500460205809140d0329403284803126281061410072500d4035540b90355450071104240e110018100c1400014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 168434073 1250 168432823 168432829
    0x3130302011209051906110d09050607020f0c01050c030c030a092408010e0421030b0f1c11010507050a0809040b0111060c0904150905010f0b071101080a02070503030a0b 74
    0x100382c101115100400240c00982d0b01c1c15a41c0c00c03806030711581304150842c508208406504500807808800000ba6115070803945602d0160031102001c5807540104400145503502c00210406007140680050080e044101c0c010b650941c055038121031680810007019244200c100b004140a01d030559840a84502e040000c1003038006800f005801924100803411000d40c0c00034a06054515400d0440b80c02d4403945003500b2240322043e20f01c603040b0080c03403040300c0481c1c03d940f00d41c0802d1000d940d2590801130080c1088203000c2c04804c4000147c004a00c41c1010034000ca008141c0034030103040641c074081a0340c13110391900c8125a4110345002000511050a043c14011420703501402c0c20060026504500066180c280c001c0c00c440e029540410010491740e0703550450843c01912150401005032900c01201c040d10003402848a2200c20b50000540e0b11500c0049500c070b0381c0c000b07081a0751305000c000110707074864010b0300c1c06151a80902c2030303c0c041003003480254010500c51a00041007c64a024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 168435323 1250 168434073 168434087
    0x8030702090f0108062206090b0103060c03060501122d0606030f050603030706050601230c01140405030304030e010203120a0b0307052704170304140c040911130e0313030201 76
    0x601c410207402d40c1c004115266002440680003141030940c403142120900c00c0b0584612081c10180400c7d05114415041c40a00130102d13050b07900403041171041c1d00903000180e059031307094814240042c0000e842c40900c00d415a000c5803001e150a00c56000d9440700702d04e00d200100070843d203118890390329036080010541501c968000968140380034409860410700103a102d01440801500d80e94841c00090050303071050307100c10004007401008100944040c4e4400f210350b0405414000036600e0050040e10401d0310122003441640c0c050f0040d85140e58695003243c500c914020041c0c1988810712190f00d6051a0303404180c40b0b907501d4080080d9004d2104101468010140c2c030460140440103124520302090a0104a13401c2e10038011194030307222860a40c5035440200025140030328040207020800c40c61400c0440c1d1285090121802414214204030480300c4010000f02410500b5990640b40d0800300740e45680711807224000141c1840d482411801d50307104034000d104400048006104568128038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 168436573 1250 168435323 168435331
    0x1203050a0b06030601050c01150f0311030a0c15051e030405011a1011070f03080a0f090f050d05010b130b031203011805270604030e0906011215030c0803070209 70
    0x3001e0003692a20400b154040c070001d40464108140028a040820807d4000e4800040c0000760f2000301c030340d0b4492490b5440070341e00080740c01250b80082c40340780b07240000d03040340c6582d00101040c6201e0302c1d104140002c140248400c0c13080c00300501c90303444494a6a03241c000c0c40c0650441ca80c2e982c0c07030946001c908480c0050f26420382d9a1000ca603484280d03c40305900d02d004095400c1080c81d5000580d440c1d840c01100f5070102d00b413030489150100401ca050301c080c182250180c0c40e4448010a4207400b919806428090042007140c01e080c1005146050310306040b0490040c00001201400103001caa000c0c1c1202003070b000590385408001c41d080c14100f04d0b01c0c00c00306064446609550401ca160700d03c04030505100c6501b103441e0700c042120316400d00502c10802c66440c0c0044c920f807490241d002c0d26080e080360f098022591091400005081ca450b010744902016914075100504288402009080c50003003554280300000d804070010395009020000b4103168001581c503840144104152110020 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 168437823 1250 168436573 168436591
    0x409090b0c03090a11040603020d06020417070b091017100302010e010c05060402090702031603080a0510061b03030204090f020309100c1d01021006060e130b01121e0207120305 77
    0x410803008a4011940001181c1d01c40000d24486070007a0001b406014180c0010f54021074050f20f040421031258000d000b203130380a02c0c04056000030000c030381c5d4803890140705021260000300300c201d1346854010700c0745010003c42c0c10514852170402c901c05112200865a2010380400003030b0034030075036030000d041c103003404000d2810450030f9805540d5241c4031200908000d0044031505c0101c0c000700c1c001d005480310000348140480d00c51409040c01800d0b20130030344c1c420042524100100c0c0e6800745942c842c400740c540075110002c0700c071a02d00702c005510640c080154100b40c0e081c0804603580800d805824024242d142c00036850f4145941da250a0001043e800000c0c80c0c03a1214407a0b44682121000502800f007411400f5038101220042c0c0c1000c41410302c902e1494074192010035611341021000310000c070b0640d4003803070b416804000f890444154000d103501051400d1901c2c4220780c150381003c0107240c0350814180c40e81c00051110b030280c0e005030b0801c03560104c0322140304090070b03131500c20a64011429 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 168439073 1250 168437823 168437827
    0xb0412120c1805040506060d0f090f0521090d03110a02130902090f01050907050a03090204020a0f021009051b0111060403050912070b0a1202070f0c0503010c0206090303010603020a090b0409090b0c 86
    0x410005803023440794070551701c050b54481011082840c01c6900ca101d00c5500403260045120507480c1640c0c4640309810100300007281c1480320f40c40c844084094408610000e043c2d20802d1001e92070640c0c070800e410001c1e00c51845413540f1600140c4440d44c8a50100141e4040402e0040603481004658040144036566904000004022907556201081d4204c0d10314103003190740d4641c00d0401c401804400b1740c046c1d002400014219011548030070324000e207122680c2611420226000204144e030107480d0040c005500c5603294110b54404008103e00d0003c0c141880300c1c40700814031704070b420321104540540c04900007180415850820760301003062200070704041c214035800c1c0740b04080c1c40d00802003c4010002003140b054070082a5034102e8130b220340c000904059018840c0b81040c7c89100030f0241038069420010004c884074000682c00f0b00503a268005181113a003002c50460081d000b5101036420031103000800100d50703040340300602c003400717a403071000c14a043c2a044c180403100d0b0103803002d1200720007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 168440323 1250 168439073 168439081
    0x10203070f02010327050a1502180f0a181505010c08041203030605030109060905190c0b0903120f03010f0e0610080907080304060c020a05010305040b0412120c18050405 74
    0x3803110307000c016a09003000582e84044014455101141206202d424008151004280400001c00345c16a51040c1500b020180444080c40240d004110300206420a0351100742d01030b1078000c01c0f078540c400028080804c91603980308400a001001d030100403007190b85008040309941c03052807030b0002d010282052195140745030394201c214411403043c40503807101200621708240c400e4000600a10b4018000e0240e1035160030180028849144112000c0c443c8240e0320843e0300100100d0549560042e00c1d8440161620143e85120f6101c0c0d4405545030040a0748400e105888002030018006103010a82e2650f040425102d51240700d50070140355019030004100003542e8060700317846890003034a070035602030f00d603a008146413010503000542607000c0030501240595218520400c124000c90704d00200300d60700d20041d021a00c0039a405055440034000040100b84a050000324030b036400d103003490100c0c603100461000ca0342d58104080c0000ca0f0815004c02c0e20b20121340e114090001244c0030409418 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 168441573 1250 168440323 168440333
    0x24050f03030f0c010b1e09060f0f0103021606050709030b01051509061c02210c0a090b0309190b0403030e01062303030702190f08060103050606011116090203070e01020307 75
    0x50b102000441c00c0c0000b5201044042904a1948104003408078200281da02002c418028480f0400ea8014802200020318610344407507103d1180308081e100c0c1d020210766900441c06540101401242507071007071040c0c00001c58a101d0188203460381d560314515541107142100040c54181d10951060000303035402c00442941d801140c0080e28121149641c034005001886480d050712160100302c103201003031001049030800d0408040d14030215000241e81d807181c1c080c500031700510740300b1000124240402e0005802c0d80c1c0065800007030a01c2180c055a1111541d6480e003858a10101c82082011040c0000c140c0c0500402c403281103018000d205190a040c881901001c15109100c40d80100850040340e03505c0500403201129009010060000d64100c4080c6180e5a1072040f0800820909800901a00003242c0c840c181c95205014020f642c541c0c0c0c0c011030b048000c210500c0c03c240100c00000c03014103080d804640040039a1100540c40c0d01d0880c0000d48114030034200c6a041d5081080540c000403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 168442823 1250 168441573 168441577
    0x9030601050d0212060702010509010605031219090e0c1209010e0a1101090f080102091008070207030809060903030d1b0e0a091505031002040305070609051c02060d24050f0303 77
    0x100c0a940249412001e07000081c2030f43c903031051619090281e80280301b58254190410f078444c03001d402c024071030765036200280342e929218201d0081560105001d0303840580410f24180c01400d06514041d03003196160009145a4001619078198060000540c0200c6c9607400051a51010549008220613501141020b480748440300000381901c40340d60307031440c0c0c0380c0c01340401074050b0900201d144035190721445020300030b600010300a07219010039040c7c51106481400da8501c03810a036405030120500d140c1d1001c841e42c01040c103043d407240d028001116a924108081c020a1000750004030b501008801203041000b1007602d545c0804c030101d048030400e034640c240c2c02011103803080c4000600c0002c00b42810552481b6401c125810b020391b075803000d0034540c41e030090401d89000d00b081c0d942c000d59900081da01d012080c40b66542007910b00040300c0c0e02c04c000e5200c041401e400030b81854500b5441881e41400c0719500f81c1905240101c0030000510326070740058001c00fa22003543c2125120a203240007035981c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 168444073 1250 168442823 168442829
    0xf0e1b04060e130b180106081b04020c190804030209270c0a0314030d060f030308010f05090121050d0c061506020303060907030902030303041a0a0501141912111509030601 75
    0x3228002d808980c0e03410103c0c05d000215600100208402600c846607192252111f6660f00c644a0803d00c01100c246024401c44201000c81c0000b0180304650a03017401c21602d030b858060750f0810f0240000405038a61803201403140ea920741e80440b070821300750010511000107801102803984203112569064484086460580350000e036019500340a0443c13031032a5106d6091091050ba0400d6000119a05010001c100f07583c07003512080710a81c1c9402042d2440304a500c202e0741c0c00140000100181608800329900b10700003050207088616241e1500e030319140701080800e00007080c0c0c001e10340601c503043c413407807415944020b1004156460040c0080d6607001c081c001502c50318001010509850003984440c6016a02505880e02c80c541810210008040c2c034001c1c4818076080030006119448908c9443d05a41c1c01c1d1a040c0d4003003c150b02400300c54a0550300c1c2421051440c4408035141c484c0e1005810014810b04228030305040c0b840c144102c11728030882e522a0160706100748a461342e408102c0300c0c19 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 168445323 1250 168444073 168444083
    0x41a130512160c47030603030c0f0c0a060503130615030c0b0a120e0706030c09090204030f1b060c060207170c010621080d0f0e1b04060e13 61
    0x101d03900c08140c40c086a0000c0001445525200c8000a1455440360b070046210420f81e000c020040340c200c040056980840180451804c288030302070f402a10940185030864400b43c01c0740e0900c005004807030300c0c040280110031025845403403807802c503180c9410988050481d80c0742c0941141420199000b04043d01c1400400043d01d030030f5803000c100c0205030204000c54002c0c0004000e00d503a406038818650003400d148001a00c829074484101e949400b030503d00b44003542c010440740d49440c004900078240c0e40b52030341c02c12120500014410304940054005580100546502c900c001c0c17400c1540981c5101070000a0b95040200700324260700308409500150308a5000369490616241845401e581491100980c0d80c01159103502014158031203c142d5488030141950514142d4049806883c04c910082004004000c0c9a1208003190000351100380e007101c01040b0000c16220582c00e05020400c84003880700c030082c289003030749828001c2d90020003200d602c118650400017030126203420600c0010700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 168446573 1250 168445323 168445327
    0x6140909070212030408120a090f0b04020f04060b0c1506010504170709061202040e060c09130603050a0b04120e0109030303090f020402190314090703020d03020c0405041a130512 78
    0x7440318024408012481c03d400d036980e40d01d1401d40340143c0160803450101400707060180006030320f0300e0346100300001c180d04440d8005000112366900f2800840003001282c22401c000449006038030f172030065202074031243d000c0545a0b4521400d2914180204403110402c83d440420310a250343c1043c203c50503160b6000c0018201c0c01c400c2d040031307d45030103540540c90003444e02e1800155103104004200503c0d10071281404184140c01c0c4007662818156491281c8075400c200795020b901c1d0411541c9034130084500041401ca6407900c8107818801c4402080d0b4504844100300420421400201350680078242418200100004002840701842d070000a081c540d403441300c070084c4084141c0041d195540140190364844050440b440f080c5030714000351012a0802900c0c1d4146003000910910802c07a18006080c090b00d550200156001504001d90075401012614201520f43d4001d441c451409501009041300c8489549926890010081d61201c0444407410000480c08641c558000400b10706503a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 168447823 1250 168446573 168446581
    0x1091503021c0b01030e01050403050a181206020703080a05010305060103140c151e040315110f0a03091101020a02091929150c03090105030a020706140108060106140909 74
    0x3900a100d03541c107500c2008a080c040d408a820b0b2908802e140d82c2007a039060100ba401e11403554243c41e800e0f0f90050110f80180880d280c0c551007140303001c4c40e00c29990070f010341c5c00c0e41d246107842c1d0011844000b55011900007580c00300b0b154001c4600d680050904104201c59859600d62948814060000809442140e06c14041e11082040303040064100202070a0301e1029030003840080d984602048400c4001c0c012621503584800d00a8504a9812150340c0300c952074102d0f800402032913400020034a03000b0610040b4007084051002d410f40345032685001801a10500704240d10098407121241103600107d60900142c9030340101b00c2d00b080a0708121106041300245a1010700810b060900c02150903c110400e24054101c224095031010f440d50288401c4880130000227204240342c3c6690b6500400c180e07800e9503c540b00441d0b01c03218101e001810720109680c0c80041e070350143c101140d10140c840041c0103028003404501c0c010506810030b100b100b00c540100744041e0003900441c0c0e04c0b80c0a000001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 168449073 1250 168447823 168447827
    0x9060103031211040801240906080a02060d060b030a0207020405010b0406020a030e01090b0c060f0c250816080703030501050301050717060609060c0304230d060504140f07061d010915 80
    0x140d03000c1d017074240003401015515030300203088490000007554100454400060070704c09a200e0102542c034400e010300b041c0d030095001e201c060340c0725581c84141d0950300c020020b4002003170780103035010b540e00c0c110142c2c1ea220a40108415250183c004010383c45042008000e45500000e403142c543d60701d400e000d4818140346c1d00684020011307070f11041c1c529000103100100c0c903001042c0d0500c5442160444030441d150080c0309aa1401100301d4a80100076098046075101c903020360003d004c9104400581c9002008540b03091614032030881260703c00c9021441c3c204058041c000c441c054481500204900d03d0460740003041c80034040314807004865a203012551a4540404540c82e0b13060242016680c2c4115942e0aa82d070b900c14403400309511170760100701000312442404407540c3c0d80b00800341002120141c5580c001054003410480c0c00e41c801d491312926001c0c0038002d020040c0340c0080a01185482d005020303010100b031241514000804000c004820381c4c210040c0c0050341c00400e0710f881800819941 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 168450323 1250 168449073 168449077
    0x109121b05090702011d0d022509180308060f0603010b070206090d0b100b0c0607050c0307060606020304060f1e03020a020f03030406150b0a020c100201021308060f09060103031211 79
    0x105401c82c2c000310811603100c1d0150000c0c2100b00000c50390355038130700719491410f80fa0b1050004500050b0450325140943d03841103494215103103103400d407540c02182c0d20440340003143c0c3d07a0503e0640c2e5910001010040c180c016600b0750340407009a071390382c45c0010802c001802c28030050086400450010400300250741780c200994000890141070071006032103609042010000848040d0203454001401103001c0d2400f80076100707203264103402010380d034031104410794082e00a9110ba000506c000d0181d480801d0081c000c060092051750044d42d503e60411000a01044a2210200c2070100c51114201901e441010031110441545001626145408001ca0a12408122482e00351101009000a106595004000490000c040440b203a595a1441026030180741c1c6000003681001c1071003c820300304800b410894081d035100041c0f42ca030b00b011040c60031040c142c200103015071110f0b04008801c0003010b0300e40e402500410003040d0b99891a03500a041c80e050404006075180c0340d104880d810707200c40003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 168451573 1250 168450323 168450329
    0x3020a0c020315090708070b071104090503130611070f050f010216180b0f030309010804081306031407030603150209010918050f0f090d18030605240109121b 69
    0x241e90081d50010752030001d29a09641c41384440c0a0a040095218130000320712046071941d4014508002c96038440c00794100c405880990025159003a010004e10144002c0c44c40521210a40b208141404401419021600c00030320007648003040520907a0300b98010f140845001310b407501070006035a00100d08142030b00140c1845014207800c0420900d0780c448001c503072110050030820411000504000010210404498068004102003c0340754400d0180582c403a0054905074507051014460700c40304107075a40b24600003596008000402c02401c078404e82c01006a142c00d101c030300d0458440e46006002e81884112260740000d04490382e0f4000d000390001002150304600002031481100005090100d41c07001d10f41180c20300165640305030442ca80d000b8262203005003402c01390b00400b80d8030400180d18100103512145400000500180501c5104801e400f40b450030a951041030800c00c2c0c00c45410355414000519018482d40714007100506c5c002c0d4102c2040c90307400c5014400c20032110741c160 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 168452823 1250 168451573 168451579
    0x7030b01210e03120c0408060a0b0603040f0311030c010204080610050a0b0a110a0c0302090703051014061902070e01060f050a0c2f190302060a0507022d1002060609040303020a0c02 79
    0x50410002500c000046c1003101c01c1d44040c8c03a40365848400050441b60a407642590040307040c8040340c003252200160780b800030300c40d052400c207008180050f18590b0f04000e402d1021a034001500340804902444600d41102e003065282034020300301000500900304038004c000311503502082900140d80300740180b1482e03000e140291849251142003120070801540400d80c02a54250081a0f1881c0309100b0184589001305181c400141454503010b121080044890360000083c0071100101e80744503203903062a48907400501410f13280021120440718140c3c0410b09114000c40d204900300e4100d411240e2204152500c965010f07190b00d0305911050b80c26030400406200000001e40c0d000600030001c00500084810707181200e01a0b40c800d20003030b40f600000f0340002d0207009070b111141c01a000307000c00e14070040082d61f800c00c601481c102024481041d1000900582d1851103543c2010900f01c0744904140c80601480c0c41c204001c82c500310300240c0000c1c04c0590005136180c402d8415060141215401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 168454073 1250 168452823 168452857
    0x14030f15061c0c140f0315090705120d0206070f0c02010c02130c110f03040f030204050709080a05030316030903230f0a02160f05010c080306030a150507030b01210e03 73
    0xe0038420003030724090044c400e5040e000c0858040d5440c01c1d41003058804001030003000c00303410400c240140014060002662442000008145695849009007507210000010102075003c1c081c02858120060003030000d01502c1020030304e00c5603000b40d02c24000c64082c2481418015603102255084a924035141c84c1036142c020340b00d210700d40c00ba500505025100080300c141c000950309850f101d00ca10301c101003803444580d400b040141032980000340d01c40c3b400d00742082619981d0380c04900744100010304417110b80000040119512602c40c80a6803520301386010814040320707a40180810035800140b0b13000c11440048d01c00c5503802e51046900d00c0c584bd00307442d61a40003180001e0755410b010200c40402e03046070300340410400d804c411001d0880302d0580d1414183c0791140c549600d6580040e20b000d4050040e003010f800402d9198110b6584411454000945071504580003822140c115611030704011100e640d042594006001d07542211003112400900080040380951440c070940d03401035004810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 168455323 1250 168454073 168454129
    0x180605091e0f06060603070221070204021c0f02090a05040216120903020a0503012a09150e1305010308090114070209040807030f1803080c0102160602030114030f1506 73
    0x414440e40c04501c900c101c9501380c540344200b05a50000b1980240141d003c0e0030000d490001e511010781c14010000e080034501006a000b04044e07034010ba0b1142000f003641d44021806440724800c81c48801c0e80700a0450400964600080d03070303000180320b840d1003103801050400182646548117140560b05c04920280009808000f520040d490322007688545c58803a030010b102d06040c00b61000680e00301144003a021404000f101000600d804148104500c01d500890303072901200341648245801e0b21602c105561480800044146142d902c00d43c8034208401003000030004e4040d01c480d0042402e00c42e00075880070080481500401c00040c3d409602c4d1014001400801002055424041d9031590503000a40d402510303030002050700891502080c000400200d100400038104200600002524008c0010781500000c0030000040c0c0f1080d40c00001000800102c0d03901c1055807406401401003080541241610303030400c11800b0040d8481000040d4080c0d6495060441c01d400c5082e1aa1090348 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 168456573 1250 168455323 168455383
    0xb210601051b16050d080306010c14010e070906061d01030f0e06040c03031103310b0d060501110c150d180b06030105010603050f042307060507020a060318060509 71
    0x1650000c3c0741c40603c07850743c0214140c1800c0c240c4140042e00301c01c0c9585103031104801101c02005c241000d0f203000c2003020f11442c00802c2800b48035070318401480142036076410407484408450a44d401b0906201c18250b85001e031001001c100c9024400c00d0030000fa65000a41601009c0d048019407200180268030402040000054071801528040e980b507195025000f03811980c0d074400e103400480d0701d240d0703132103500c14041c2c03001c001d56811004008080340407907580c040c148142e0000b41c0d49078800784e100d09040c03265580c0101d510400c0f03280a00104003a449a0b000720701c1400300c44e603400700d880303600042d003c0e02140f00f07400a0354120030091140481ca201e5040c6810713004010b0792694429401c03c070002070342600c00c0c0541c0340940b808071451032113070310340340d98050b050490b5a43c04010030f1850088200310f00401e11640c4000e040980f50140c1e070f48054170401c800484190070803c24149040b292020035404c0c034030f028455030390200c0001080e40315080503921300f454425881d0a8018007071030001d4400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 168457823 1250 168456573 168456583
    0x4080105012309040b060d080307080402030c01140a1805030f100f02070b01060c0213050705120f010e01030f080705101e0504120c06090b040804030302070b210601051b 74
    0x1541e854002d54002042600502e0207886620708107901803c007901090110307040030129900034400506501c00101c0f20fa42c1e404090304116980c0740451504401c010550400388030303110015070240b13055086050b80041d6201d1341d000b5220054104944004000108c01104420b440079010007400c9480519030180f00965815030440d549212030308003810040c0160603802640d058543c0302c02c074000240e0070900110b51101c1c0411081e43d10030380d8914954000c071441c0c4101d84c007803181540d455a590010200104c070102c0081c0607c520310710213400401185030424003450540b03500484c01d618442d4281000a198001c004c0090080d00600104a0740030700c1c81c3d40b1403100b102001844500728907001d4800340c201d80c000c5034041d01103a003e40c2400b00807482a4800e15900380f01c1c00c00007848543e140c8445014100444048980300790000d030600616404101210040a440b69110f2030b140c000d01002807011010300748415062901d8000c1407140e030042065402c440388a00c101d50f03071880940d103419910 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 168459073 1250 168457823 168457829
    0xb03150c04061805060a050a180308180a080a02220e031b0c011205130c030602070b0f1b0304081603020a02130204050120030702130b1009080604060f0f020408010501 73
    0x70410040c80301e982c28180d00700f030034101c070030041400d0305018032103000340d400340c0c40301500508100c0c0300108c0e0b420f41c10781210901d01460040030382c2910b0f640802c0307000f00740c01407090090344150402c3c0820030480e040000c030805d00744d9040e42c840c01030f1468502610603910001e10710800c46802d00d599407554420010117800b40c1c2950f5595240030107410036265403034500d07640c000760000d04107200c0512140c01c141c00030707604884030101f003204101c0c080d10340449900c61904102d52007900040e0440030b01003044c500a800210034442c04c201401d00000254001d460540c28800c1c108003c40041c05103d407440503510342c0b114240b122100c000d09860020b440301c3e40c01c0c004034440c01c210a0a040141074a10a540a80e80180c407409503800c80402c600040d40907500000d0807600c02003001d00700681f100c100021003071495540200e12448147d082103241455400e020741082001c000c20400c040b40050404c2e006038000c3c80002c1d0440344864081d0142c1322a03408020340c20300001d800208006c0542c03140d812 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 168460323 1250 168459073 168459077
    0x3050c09010e070e01031d010f1d010b03100b01121404050f031c110702030a03052122020307050603130308060405010501142104060603110114030a0b03150c0406 71
    0x907a2540c001030b9505070705481c410002036200300c088110754002e6000c4441c0b01c4a034003040c896000320078890303829250214109113005441d5060018800544a0b5440700403080400a000841c1d640011a03990700640d122800e8058031908401d41c16406024680202e1010b038a00b40032a891003181e45000c008159002c499900c12844080880c25002c01518050240680e03154680c02003040118040c1030400300c07416800204102c1d89006941c100030040e529840380c0c503034607122015155030070724108450a1084000100700100b00190f000401d12000c0c1e0028024003c460400300d00209151580d2a080160040c10000c02d01159022032000a080c0c1d51017540c8940c0e2694840302808180d65081c40f81502058505034481c240c1d00d064005058001480400707881c259034844458010b0348006d4400740d85241d586c0c0414070910602c99a00340040c1020700b014101c5a2010612003168880103064481c2699100300d0110341e5a01884641d9070480e92601801143c1000e052581c5150300500c26500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 168461573 1250 168460323 168460339
    0x20306010e040b010e121203090703030f031413050a170c0705010903110d080c0109030302040e010608150f0f030a0605071b03090b0306010e102106050306060d050f060103050c 77
    0x405894107002d15000224113940e45c40d050380000d401c0c0204401c411110b40302902038624210b1025000b035006c0c0d8800c1b20301c14002c026043c40c40c00c005d40703c40003c420540416041a299039031075500c41c080550498061004226004030a050090801040a000811000200d111040500942c07400b804c5c41c21081c0050300e0b10560764500669600040e8840101328012078840035545161401d070700c0e40341d40d00465482e4900042111485d086888001e401c40100364046014400443c030070440c3d5001d05000d0425140c20f040409200002c40450850584158020741c00d10015890303090044030090b4000d403c55910118914080e00a0002260074030000b504160b06007644d140e800351100310392500343d02c54548441c1442c884c07203075a510041880e414000722140f108642d031100c403200400c409103075403003510038160108542400b01c0c808402c003480fa82080000c1c0700e9580c1c041841e98010354110fa401e800e6001501d80706081240c500305068050140300000018085c02040c010300c040c008540314a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 168462823 1250 168461573 168461597
    0x6020702130609050903070203100504050106080d05040e010f21060609110d0b010206071b05150a090506060306010b040509060409020a0e0702010c0309080306010c030207030c081e1207030516120302030601 90
    0x998901418501a62540c025045c80124ac0c80603408290000e01420020480703c0d11440035070705c0c10f210f82035000c1c00071344000390030006803004090041c00341c40348051400103180f414a4180001124000c032401c407400b03000701d81c000c00c10141d010717100500318518180464000c1c003c18104a0b0400181c0303402280c100407005c0415840800c85074852903585e140c0b114201044007100e20380d0786800303c0440f41407007001c1d031018244452004281c499034003880085030706c00b103601d801400c000d00036160f64000d51003030006120390400507094400752101541d11624a5840b00c3c0028050b20460350047d402078920320022034040c8800095a00c1005550020300403540181000c03011a450400e0240c43da40c008d0021072840d41c46114031a03070090103841290245502c1c1d0315200e16a882c1c1d6880060568450740c4032f00440400d440d249010203129001518140081d1000c0344124402c40d00d00404110002800710941503882c1c0c1014034454010b400c2c01c920b50300c1444091700030740c8191181404a01e42c0701c0d801d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 168464073 1250 168462823 168462841
    0x2040608030915030a09050106030f030e1e01030e0102040e1e0106021b04091103010e0304150804020901290a051c02070c061409030f07260d0c0602070213060905 71
    0x2d0301004006800070440048804074000c40742c00107400d0808442d2a9813060300825424007540b005140111860381d404400780c9000303400c0c50031307500180d4007900308641c54007150000c00400100000b42802d01080480a81069900a11030750300300902c0f28034040705008041c1b2600400640f882d103042800b804690700c922041c0c6e65241c0d1003000c66249006800c11504074105038004000d0944108500c104560351500043d0030756400c0c100c1500f456001082c1000710b81c00300b4621429074038441c244812542003035004200c2030b01050052261120001c0b503108807240c1c118414055070044c0324051900d40d8001d5030001c2c0558421107620803104889130740b013202002140300b140c0d005540030050141e0b6a10b01442070f030b081444a814022100002d100c80022501c0900401d451881048081e00c0c0319401e0000c1504000510300c500c4243e81e40b20044d4800e80762000564480d110010f080100c8003804926061000e807090f260002e4014180030b407030b002003070300580100701503400300c01090240d55991451 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 168465323 1250 168464073 168464077
    0x40b0a050c1921090f060b0103111b16030507081501061e0201020f040905060a060c021305130c080f06150102030f1804140406052208030a0e0d020a0204060803 70
    0x500509915082c881111a40240480ca40407040004a07420024000c0d000c6000c84841d1031003507503d194540d481400704a0180700c0c0104100c000d00302000550000f03101104140102c1c0c2400d40290b08207241d807000e000e0200450f50451803911001c03c1515164030b8005d880342e04e140300b038400c0c074424500e02100342c600721400541030361000d9031402d24161100c0b0342c100d0204003c446000555500300038022034208103500070b10141010030004182820b100b41030011846007035000d2810840745500701c0d40165603103503103140305120160003c00c0035150a00100c40000351850002d10070b00800100042d648404281c002c18000380310252410b543d03460801440c0c0141e000c002a005030030411019281c030441c00041c10030031003c903a0b503030345000e1000041402c84112010120301c114508007080104070040c040c3e00e5006480e200d00c0c00e103600341050450041c90a03804010004100480098180d007035590107959002038080c1140d01d001c4d0100006911250300e464145d0141d0309081c0b000c1950440007003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 168466573 1250 168465323 168465337
    0x40603121107090519020a140408010b090a0908030103021e04020a030615090503210f041d0705090f10020a020d120905030604120813050d0806040b1002100507090e040b0a050c 77
    0x42170f09060003d081e00480250f102c01c030404180310700107216141100044004e48042e010f400000280004035404201703040600402110780703030781000d009400107210704c400d40341101ea05071014804541e52120b10417000c1d025004158215202244155a082d0305810481c1202c0c2d03028910b20b10220480c8040303e480300140a01d40d0141c1c800b9865031503025100c505250030300c031038180040c100000e00c0c0300300c0915449584a44000c000c03d451183d400b114114030305800074128145907107460b0f00310f004100610304001e0018420f40c40b400030f00310f01900070b201540e100c0c3c0d8001e00705c06401c561032500c40903c40c80c034248200040c850310300c042a2400c001400c01c2c061134100d1440c46a0010704841152888802400481c20810703c80c41c03440094002c2001e0a001501500d07079a42d036103003d01c28031044952042000d13126030308062240c1e180c96004240c51580b0a000c81c40400d0300c1c2c0d5070380400c2d00c8113a0385501044c0e0aa9240d010401030010440403180140307a008400d100640300e0300c40320019802060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 168467823 1250 168466573 168466591
    0x60b0426031204060608150619030f060203090706091a0d020f070c080c100e040504020d050a080d15061e140c060124021c0917010506120601080309010302090406031211070905 77
    0xa000c20345902d062724008050700707611201556581e841e565100b25136000c00904803005a0040248480f202c800d012800186c401d9144c0f809100349002e0310018095848007441200ca00005407950b500e400d140c048503d003e400c0c250490340d580b40e520700000542c0300c0384507155030f5000b03034562100da914020503148801c64007a580d015030007a0360750130040280340140c412a40300e6503440d1720740700040040c85440300041c001e160060326900140c050b0030503144a80c40c008190700150340280201a00400c08001c001c2c0190a4602c0c0303a041c40700140c800c04050042080c0004002c03494040b24030001a45a05a80e40e03000420b8030000f003480c8000340e0b0070322440c4890160b00412072413480795039074120b103052150461500802c0310740e407080041c4090040e0700480a459458000b007040d641811a10680c0408001004004943c5071450050716409020038480c1015000900140e1550312900034030007454002e020600138100f040009884c42160804080890203103110004424102d4494684100b80c45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 168469073 1250 168467823 168467863
    0x3030c0501200708280503090c190303030b0a03060f061802040503030304030f050f03070e030c12030415030e01050f060a140901140d0c06050301060909060b0426031204060608 77
    0x40d80c4069454025545104541c411400d858500040700e1203681750a40175a1151035407420000c1d01c03641010408100d80d8009c00e1021460081d00c1c5185500f0011281c0600d0005100141980011f290328090f9001030021410502442c00c20b011a5101c5801c544110000880e8000848100010390065201c0c032039158100b8800500400d0041415800d529290310345540b410000040005a9800a480781e000142c000e507041011130804000300c0001c44002c54400c07108600078038005030740f4880d034000c5541c4a2075000c10094298082d0b0040b20034003401d607000f0700044c900030b148003035500c0c1d048992a03c2a030800900085403200024911400e00000c0e12030400d0b0fa0038081120720b180d1180c0d04a44d000b2289100c0400810801517500001e8041c0381c1d211507595140ca04010160005508501c1549160400404c0008020011102103400c0440200715001500d24004c902c0b060380b6108410900000a01d210000b0403101002e100c1c03445813100b04106512510025651040b80503019400141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 168470323 1250 168469073 168469087
    0x1005010f0308070f0807051b04021c2003092b020606010c03050702100309060c050a211e020304020a14010c060b0312070302031c0c0f050a0203040f03030c050120 71
    0x8010007000d510380115181a25004c29170f0316001264003010040e90039800024001c440d59a0224890701d01003000c83e020750910350704425810710503074200880b110856940b0f102001d100401c11440c1308240114003100d489240c4003002a80f03c0c03801d561981e0781a000542510319000c5083c0d4040c0c055020f45d401000c0c0340d6a05801951103c10022013a401e200702400300000507030b03aa805035400e007000750ba0046041992450300c2c009880e0240105010302406020350f05070303581c1c82541c0a401c900c82982d15900506005103a50050000003408c00044050f44089061a081034006601443c4299680c5040a85ea20751107068600c00075410b90008904480700c0005c40c03900d400842d444d010041c240e5442481c4228032020940c07286900b100540c10105120003d251020342e4112030381d18000050000a0b003c0b54010807550340014000c045c4800860b161003c81d100f0000e9401929800f031620f01000c0c1c4030f09010300b6a180944085035070b503080010a40040f52145040c0650300101d203941406c02603 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 168471573 1250 168470323 168470333
    0x601060f08150301090c060216050418080d0e03030403020708070803040e060909160f05120c0d1403070203060c040509070212040b070501090803010f030c0611030304021021020c1005010f03 83
    0x500b0381045a056484506400c042488140e0b10301c004c180075001421628043c800d032400d0500b150780201d209518084000c182ca000c0c000f5180c50b8141e200c0610390341e42c018002082d000345400100e07120300d44030110402081580014022040d030b00c4020440b42110754582819640b80f140d800769965690424010440031b0074002d01c01c0c2d400628240a036003265565a54a0710f0508060784640641606544100030b6420f0042046080c04008805081035680040c042008a0b0b1103840c02003011580c001c150107049802d00654415690003400c0d2006401c0454080200b500113020b400c3c4962801e8010805840c000140200481e01041c440d50419160001c80c04075608030720015103865496000f284009080040154040c000d5010044040d80c01c40c00c0045c00c0c10f686420084c01d1018620240d01d81c00b0000082e030340e120341c1c101c441c3d080480b003442003203c10f0030140c1c030f050514420011041e8a803078410340251006501210072070b04408562200e40cc02d8600c01e00c01c1400c1c01c9001142480825 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 168472823 1250 168471573 168471601
    0x121312080c0d0305150a0308070f0c08070801090204050603010b03060613021309020a141e0d09050a110310091106220b040510030c08061e030109050f0601060f08 71
    0x1502540d0328904210000c100780c0d040c2500c07066032100180d036400c02c00c0b064800a01502d01100d0381905c085980f1410750f80c3c0c5581622801d00013030010141d007000d0804000046499078054098402942c68103681c0b01e1590303000c0d010007907049210344d040000144039410305105001c00440c0041c010b0101d6207415040c00481c0041d4070000c00b4041d00ac0041c03211504649a600e0000d08903c000169a40400c030001032100d0500a10792a150008100034401002403540c0240000b005140c1242c5d92018550031a0041c11810741c02031041c060418404140949032035007640d0b202040e005c1ea01d11500b4245c4820071175a4000c002480c0b06032003d400c2c7c1f0107080c264080d04503e22000f883c0342040d101808040701c0360019512600462800003018401c50416815484940100d41001c0c40620b182c880c02911030600104480d001e10901024400c08a001105040940402038001c01c0a95500e04066448808007194503c0c58440e04000242c414854840340003c0406583d41c425103454086003d128a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 168474073 1250 168472823 168472859
    0x140d05070302091002060402090903040e0f0c070b01120308150d030503040203070509090a0309091401140d02040f06030b160203160528120206071d01050d020c0d021213 74
    0x3550901c402180f40e20342e106103214800d8180c00402d09032034144100590b0b040010145111a0020b200070042c0f0700b0003200310ba400c6000e4000e03004003561004485261401886400380000f2118400041c0034210b14030322030a9640241c1d118605640c50302207115541c0d044804180d0000e90342c98000000c28410406150030510007011354031000e0751407000a580c6d9500f90f40d02070300f540280c1c46101c205904055038a00818445009104c4043c00c0e880e4103140120503c241c0d49001c4882410160543e5402040445160f0091003082136481c0c900d6650000d1000b400121801540e500101e403401e04001c2d2208a0b00d00542d005529080300740c2c0001500030300c0d143e8229943e2041d00b075003500c039030114581d030000c1c900e84801c111812202070800b96002d4021030b80003c10340d0810307028000d41c194003000440202c8441c046545400101400480b010300c030300c4220603a0310744041206214114041a40015441281d013102c500d21072a0700e00e25003a104500000c4041c15055008001100c203020340c038288 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 168475323 1250 168474073 168474077
    0x30c141014070f212c1510050108040609060f021e07080409090f141006050d0507060818030309030711090106080a0b060f16030305070f051c02090a091a01140d0507 72
    0x140d4a00c00d5180c0f84044204c1c6210592445018000c5c500008000500080004140007040c60070030780c00d0414040114011181004206000034003804911740064444540c403800c200300129a600650002350061110310980c0340140025140c1070076039030142d8086980202c1c00c0d038942407400b0744030001000b01e14401c41e02402d2409144000c40d02200c54400c03ca40c40f000031f02a0780e02140030040c22101550890380c4a106081e07410300101d840041d5210554600c0c1c18801c80030344406111007110884e90509811920001040001c2208048081e080c20740c071844448081070002e40411413038507800d014a200064441d0005641e144840d00403103021400500594502000105004403a40c0301000c04501000c2141900f0101545841110303030100151815280d81ca0701d29000402d64443d0764004410120408401d407420350441d41120203610004000e8509241e540041101602c15124041c0707288a1060402d0b98a5019031120a0309035038108a580ca044c000e8510703e070082801410383c0302 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 168476573 1250 168475323 168475331
    0xf18020714030309070504060b03010b09010c020120030403021201050912070c0509070e090c04060203090405100e0405070e010909110405091f1d010b0d030c141014070f21 75
    0x2581d081400250301030004c9101800030107080c00c0a00042d10840d42c040c0c0110f9004000400a48c00f1440594075221800d1078400000d000900048480c07015454035080406000d000d808003402c0d00200501c01c880c8280e4951110032500d013100d508a650450702d01c2180c5d0030800c19151090300840040021611542d00280700e00c2d00d440205200000071072340035010480a00c4803121500c2d08400306a071000c0350341c3c00c4034603080c10054000c2d2a40035280c1950b0169880704045029080d80310b444601074100f540c09070015161905015548085a01c20002a160720ba00082a0b10186014180303440e034005a4040d07141c01c480d0284002400b00900005c3e0303600405007400804005803040a50100d0100004a06000c0c4014106070040000d000108560f00d0505c0d845601d4540002e100c4000341c00d07040504050311203040500c90302014180400c4540500114013405000c07030340c070280d5800300703180c001031855660303420640380c5a541e41c05000c00b01300c4680c6000071200c0184100704660f080028040b07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 168477823 1250 168476573 168476603
    0x20114070c0b0307020c0f01050a180905040503191115070210090303020a033803191209050306190507050d020d060510090f03020609010509090f01050a0f180207 71
    0x44200c0c01c0d00c1e0000440000e0000070710114960403c050181c80000701c0d2111050b03814840007914511904c0a05010f108040c1500d0000000d01190355005103c044c8083c0401d1070706180480d16076010865020400c201d0040c0190741911440401e9001c0240100074480104c115050310030200c1d008184000310300c107145d203500c02c144860041040b054400d480143c2c4410001001906403128000b040d80c2c81b084415451070b80403030b031150701d0fa1034582c040425030710451002e000c241001c0e14000c0001e4a0703c2042c0145040168515038a0b2034404c1c503a403003401041c0c032601090b4823008140d9442a11940c1c08010703410900d010707481182c0240460a16070300e88043e80140d00240e0704000d4030100010b6903410708000c1c07814601c43d22005583c0031324091103660308140c82114043e00c540030203401a8000700d41c0d070150b64007030421580a00c400625a01d494540130350052132140007401072034007070a108280007402c00d9407100c100003a210008451400d00d05a6904e490082d0800c24041d100d642c0ea00d45a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 168479073 1250 168477823 168477833
    0x112170c0109111f0905060703110d1e0c08070b091e15060108060102100b060412050102030603010b03060709050904110a08100614100f20011406030a0f02011407 71
    0x1505103100c3c2504000001c0d06404000c1c055441980242c2800410b540b8014595070182440e42900c0040310055100c0d8090b0030121401150b4504ca03420b10300c607a0b10f0090400384c1100a00400700006a03100a060b0003407601119862100c80d40142001e005004080c0004c1007001781940c0b142c0e41c00304680401d00b01c580d040c00e080c5030300d0351218485d810100151320700c403200e043c2d0300354007260a0900c2006030500700c0000b0354a4128558902e8459074400980780d0035550f04007100c000b42240c0c40c9502000426040040c000d5000780c500a2081d031a1100c0804039040110380603114115588075208858544018800142001042200d07940c55a00355192196a20400300003c0c100d420000d01c0b0160f003014101003100c0792508407800310b10300b004072a461541c410b045417003022110302c0d0801011082c00030a50300852161604c502a035103640000504031015401802c0001e010046100c098599030241500c4142071030300035050241400114000d54000c04031042511044051107240800f40d03120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 168480323 1250 168479073 168479081
    0x903081e0406110c030604020a0501050d0b060414011106040b061c142d070902360f0d020a090b1909140604020a1d030703080d061d0112170c01 63
    0xa40041003502e481401d550b03e0402100030f00300819070081031203050540001d100742c20b06d48141c2d070400000207a983c03040703021a04411900705010702420b07103440c2c882d0f040828030340520746244d0014095005030a500500001d0b081c2c09950030840000c2144c0359541030068581020218141b01c405a0100c3c400203035442e200103103550401d10150140c80304031030410401003001c1010150f22002c180d401c024030003000c900b8104440040100580e1114001150030040400e800880d40160030b4840240494100014050b0034031021503e0107240c3c0400010400c10309115407010750000c3c0c1c014003d00c80c400701c941c861030000300c00420709001d040c01e03d100300400c1481500040201504c035174a000401405506540d04030400703e80c1035040c8130b0848002041c1d00130000824000e104886000b03402901d09125000203107800001017a43d071083e00075298003506040c482e80d07002a5000c114484402c400d000301a06841c502c1c6241074108615480d070b10500344400c00c1d41800f1800c02c12001e02200c0c0d003446 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 168481573 1250 168480323 168480329
    0x10e0a0609020f060406050306060a0e12100507090305100c09030b040c030209010515030406110f04170f010c17102102030d020102030919050a08040e041103030a0903081e04 76
    0x24012440c14202e205005080d41040741e200d00401003800244540358110742902e41c8050300340d83c0c2c1c9445e809160300c221041d10415030540c1d0403880d02e030200c42d4a000c01103410405454251070034840c0362903d8404480b0b151a03880050403039000f466501000e83d550f5003004540d0409442c040307420b25107944610307000b0717142514103d0f440c0000700b40400031420310002c0306004150840e0958091040000402403512000b8801040c0564419110303210454103020350b085032b202e0001403038980d6100c1c160110303402461101c001c25485071509800c40f2010500941c8030f040c0e599903400e407881d00d10706c001a000100c01346c685200b06400d588007141d41200d001c030310b03c6844c50003040e03113103001043c1c010315052030740030380c2d0050459004104016602d100082e1000703da1034500340746d6241c03401c4d90a2003401c1c58070a10000342468800100000e40441001300603000364003c1601411010000d02003654a10a480e407503008a42103000400200d600781024101704409800ca820014054440b1040d10354000e030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 168482823 1250 168481573 168481583
    0x70813080616020d02010b090406090303061707030203010b0f18090a060c030507080f093012090f0a11040b010302120103060f0e031c0c09080d08010e070816050a02010e0a 75
    0xb91102030220b5042140c1944010a400208071080ca0307030000c240b20005c001c10103001d02d07480305400b004142c030076403103940284900c514103141d048400c440151900414481a8400d60030950800041d25103000320440a1800901f5000c0740178403005041c3e000400148103400901a602c2c0780c1c0c011803214040e00c145007486039000070b41e9140410003e4140300010b8805013110490408001c280f440016407001010800000162040110764160148040d040d1440c1c40032200402d8007030100181204040c007a1983d070040c0c0e0044450300b0b0506940e07198880b4083c0001c4102c222840356420706610507041ca00e0107140141c6000009c013603e84800e0000c1e0300c111495955290200c00d19035951080c21580049803003d0741c48c14200c00c3d51404881c0034000c0c02003400365204021054036019940c034000415000085d14a0140c0b24207014014600901c186090a201480000c3c030040c030030f05c911803240460510101d20a040c40340220350030b070485c041c118150f65840b10456407091041110711020391040b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 168484073 1250 168482823 168482851
    0x11107030303020a110d0c06050c090402040b0d06060f17041104090311010506030703030c08030606040f0602030a140c0a1b081e0c03010606170c0f030108010914120708130806 77
    0xa404005e0044e10a17210010141e003107151140c86243d840300e09041c2e00da4000300080303116120762070203c040d80300d000c0da2941c2c410b20024002500c16071640240c000344401c1c3d413040207005d6a4060039100140840003c40c00546941301101c0302440340308503280c0040c080e40d0f001441584401c08181100d1a403401070b40465000d10781c1d02d4102070240143c6a002006501401d901c1e031940d5006441250b00c441c1c014201c41d4003100041c000d860350300555004080c000c0c0302c03580103580c40002035202d9000c1c0c65050001010703071000003101c00e000d90440c0c0e5580d407103000420240305c042d121f0202d014146c04131003600005040c0d0004050004100c0114600d103440c0c495203480381c3c4d1003149d81c6405d402c0138001d40241d0401c0800c119460300449040300880803413400d44a95502c800608101e4410342c1d01c010703090440400045080c4805520000700c03244901c40300c0c446401841b2806542d08400b4011004824003000144001000c81c4007070070103402010507200307a071a194400a81800d070100c420340300c840b02d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 168485323 1250 168484073 168484087
    0x60203090f011b120518010204030c031518080a11011508060a06290c03031e091c030902030304080708030705100c050d09210305060406170c010e01110703030302 71
    0x400e110f024000321401c005108040003014024008000640038a40056a500c1c0020031000a01c00c401188015000003190344a440b440c0c00400e600441c001640ea14111904031012100b0a100c1d484020207007180340d9803580b0f0543d4403c59654007032140035040084402400e00b0700c5009010b4075560100004d585407601c0c1c1068800d62030300b04020010103107d8101401000070f03500054142c400c0040700d9446013202154072215a1325031251031000141d620001080007220400c038125030301038032510300b04800c103a11224034003070783c4010518542c00f8080f58589c1d105143c034081c0d4000c46100748040c040da410300d95610032260034642c1e50381c8401c142d40c00c000740c454100401804051211420f0140401c54032403241401080c40c002c80702107686040d90b400a45060081e409601905944126122058a605584020094801515114029801d28601040b0340b03a1542940321a00d44041c0200b43e249101001102c9080c4441b903914103000e0a40420101310805000e0080594029100507941d015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 168486573 1250 168485323 168485353
    0xf0e0915180f010908090909070e04060c080601110606130f020c01050f07050406141b03030a0c0f0207080a02060d090203060403082a0306091f0306061d010b030c070f06020309 77
    0xa030100700b034006900d06a507900c0051040c100b44d5015103015039000700540d86104181e03203840d442e500960007800070b030410041041529006840c3e00440c40d0b5403c00203072200401910040860b5402c9002a0020720000e20b55007041d101d01e0101c1c110740d420205041e1611004c0c44c3c101e0303200f05189072240e511101082030409581c00c190382c0120403450714a19192514100420951075941da0403001c907800a03800041400c44000d00340c20b17103429003d8a5590816079007160080c12122040d0f40460005102030300d682d80049040000ca8007000c0240c044402e07280d0030001554402c99a02c01c0703207696200f101c005a2410084e15104501c2030300c4140c9281403078441014000080070718000440008840c8031010010034054030340044d01030b1003035041d07916a01c85010702c81c0c0c69800002403400c041040042880001e40005046030801c00c20600c00c40c0d200c01032011a842c003400b61200420b0104042141250028020000580150000204500707141d40b10300036070f8400e580400ca00c1e4880400300c10070078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 168487823 1250 168486573 168486583
    0xa210506010605070203121c0c0f09050105130605070c080a0803010e090c0a060c020409060e03070c0b04150f020a1203020417010614040207140f07031a010f0e091518 73
    0x410b1506016040855a9000940d29165081000010031021035145020000061100d0901580c640705020305100b1540080c10490344407482c00c0061082080014594015000c442c41040501c800c3c9020a0034004140c5865000c0b08084400c0318680c0800103500c903051115455142c4109000e550700d505d810308204124101411441641d041086a0320030381c1e036080540021541a41080702c00e1b1001c5000160040040303d0000d030000d810240380e102405070220080001a10411000840e181c48030240641402203000300101610300d864100380320b900804980c0c1c413030001481260358602007076484070000040c0d840b0b4840460340202e02441260703a51803403100c186035000d008110107464942e40180c4c008066074410f0089178009005030034001c80d02816030801d0902412a06108040e00c070540d41c03a015440242c8a9114800000509440c81d003506e504884240304410130050400da11402c1406000d403030703820a44540040d40c0b901e0b4140b003400f5403141e80c600020703100207107840340c0450a207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 168489073 1250 168487823 168487829
    0x41e1e0804150306060909091e05030306010f020304080c06030606041d04060e010203060306150d061b020601051e100306081c0207060509060409090204180f05160e0f060a21050601 79
    0x1141c1020000d010190340704040100310381f030001000c10310390000c1c00d09000442004000c02075070b10082d5018018020008010b5019502c01c1c2d9940d0b041900c410300c200d8583c0114080d07120141c1000640622078a4410041e41d0061801800c5900e41581e903840402c0b502005000040801961010041400340a21170007074141546070095285160040019032a840010b00301c01501030b01c00040c10a81d12101401d4403010385c442d030208100ca902080b61101d42c074095040c0c80052241e1000420380b4204030a5100c00000419050100c2c0794641040000c00310520b00c0560030182e07108000194030108200580a83d00c0c03d8500984040808000034205441d98000d1001d0100401c0420004c0d182e6000311030440d050094001550ba40f02d10002d8040c1131050741440c2000c4040b1002c400f071000749500c58840c14401c50454203001400d15482c0c2803080c052050406610118002980b0742081c4580c00d640030717800510b0540c089855455039214200050b11904122050040c2c03001042810810503001d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 168490323 1250 168489073 168489077
    0x2508070f0f022104050a06020a14010c020709020d02071a062b0204090602130314060601080f06060c01060302220608030301050d020d05190602070b06010305041e1e080415 75
    0xc8110071500699036500c1040c00300849a602c04250805501c0003041d24007622000307214101c039655802009584400000c0190341c04550202852030b460340500c14023500d0020382d00541120740c5010086030083d08003c514141082d020000d01001a2044511380c1001081c2d82d1441740d030b410403005110480f000e6041000503840110400a03c0c1c001c900140e200301d640c1118080307981015403074154040e0260410602075070141d110040b0801a49138240c1800d00d00680c101d94071944c80100440c0d0f0940d0543c5c49100340020b4101061083c02e14078002d05001680034000315805540798049401a02c0310030311300220040d190f45240b4040b04601440d030041442e04010741c155410480081d10075403c5140092140c1e040d02c0c0c1c41001c000301804515050300c41000c16042e02c10090130010042d50140f032088072900d12943c000b8403190700a125240c0155080b0f10681b103c2074a148947d01c205400600540c1c0c11962030030414a255101091082000c2c8500c0c48241c036285480001d1584044850b48201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 168491573 1250 168490323 168490337
    0x705010507270f0b0c0307050601080a051b0603010e250f0f020601241206031506120c0b0307030b0607082512080a0b030f060106081e0c032508070f 65
    0x14410340111031000da5a8a95001c3d517a21004000f42e031640c803501d03100070114010f00c0300000703440001041c1003040038080c2003910f07801c002103031403140440c10107450254040000d10041c00031041c8a00704a07481040c07800c2d1108a071101d44101048000c0710742c030034000120000d9000000680c40200548044694001402d8550604041c14a42003440d1100300d03260b19130000c0c4065151103036040d0340795440b00b003108110140e207900300908040d8070012440b2010381014000511220503a40024031140c0081c4500d19881c00e00b0b003101c40507070001d4450300070903444410880080d41d98500030210750380b145142554403489840c1c0f030400c000e8103c10001485507030003c41c10105141c1300da0483e450503203140c036103004d90b200c9200300010510a0000764151298441503131101c1800224541030b1902c1d600c940080395207405061407000501280c10084204000c041003d207000d000c09541c2088800c1c800e001040090b544030700320252074176540340c000b81d462030601c0345c0180c02240c9480114203a1070110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 168492823 1250 168491573 168491579
    0xe27010c140909010b07020616030c05160b0a140405060a0e090c030f2a0412060f0c09030201140405040e03130812030f1306050a0b0301060803070b1b070501050727 72
    0x101c14202c148911040c5c404001240001c55443d0303401c45240b0030508035014010343c02d5040003401500300c3c4a04841500c00d02d00002041205001d07140102e13200e14404510301051944e0440300f60448218040d511071081c0404038035a0b58210180c0003000c0650b683c019481c84800400103000c001a00b1840f000c0c01c108240074241801c0780c034540d442a00721503195148150040c201880d031030034414885034000041801b080d44400500001c5075503000f4801440400502036220301150110414a004075440013020001940104c4541c200301c03111030030b03280c101941e50001c03405960711003402188036000007a0700190750940d83c0700c5c10090103120b401403604c88101c0f4449074080c8070213440c5120020141c0300003502d042e0500e041e042640e520400c280314034280404c00b04050445111114440d5007007080208040d403002090720626504004422001e848000c4211040c0021030b0155030184410005040810805d004a40c040d000a41d80c240c40e40c2c910440000f114620f0300b2454030a500820420 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 168494073 1250 168492823 168492829
    0x312050a090b0c0a11040501062007030614060405150303030123060403030c140703030e040203090a150203070f1103030f070c080a1d0d0210030b03100e060601020f06040c0e27010c1409 81
    0x6411801030300c41d10030010300c412b0100c03901d04003240d48010074a03414800c1c004544c0800302e0700f250161b070007a82d0511080d10307500030b90100d5000c0d00d1a10394040d44207100400c101b002c20704003041f6a511212040c92050000c0e00880c9003940260825808074401c140c0711010050386003404414400c10101600d030407811035074024000031100440310703c60358001c0041440c11006005125030f8a50114852900b10048001540650400c032540d0000c14202868481c0e80c50188000740c4004501001851640d0b43d2044031745074049000c0c20b00742c100074503059802c00041c0000e001b051a00c0c0c8a4403105090019105281c0c200f24241c11894011100014418010f840303030f414404285d26036003000703d0801d0f1f600780801e01d48400447c001c007400e4144503800c1c414a0011030024082c0344281d0955841c80185014136035100340548008148461104041190400c04e0f13401d1500440d0100c2000c1848144444c05886100340ea24021100d9540b2144400e54035040b500078818405000210341c2065481000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 168495323 1250 168494073 168494087
    0x1510050c0318060f030414060106050405090a1a06041d01170a02090919080d0606180603090203030d020c0303060f010e1518090f07020111040312050a090b0c0a1104050106 75
    0x140d0702c0c641e0400551a207590311030655500240b00f09049859142606100c040a11000100c0700306010341310010881d03504c110201d800380d4801078001c3c411a02c5001b000d0000704044c8200713149044194403006603603610700c0000c20041104800303858001030111142210303c081030384070a014a080c2502e000310b204000c51f0a5000c1501221018601c0d540e05074102c1c10042511210345040400f4401c40080084280213400b0054030340400304502910358000b03896550005180c8103c2d400740c03000070403140d403094001001c02d40c80034055900f4400c440b403401041e0780011983d1402c80c0c202000704071303650038111316004190b0800d103066000c00c0101000300d5403507041440305581140b0000f440141e401007401300782541907006001c01c045407410b040d084502000540c1c05000550800c007885403580700220036a400c0c0c81d0407401015050821034001e8900da440954280240030440100240780c001c1e4801505084003030802812808c101c2c1c1c5014100c0829180079944190b107040300500c101507101031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 168496573 1250 168495323 168495337
    0x908060105100c26070506090303130f06020c01020712021504150c03060b0f0309060a020403150b04180c180e060a0c090f06020307031103090f090703020c061510050c03 74
    0x929030a2141e503820b006802c0c100e01300c000c0340b8800383c0b01018142100e00000501e034282c001c8064440e10b88424418a0701d9200c20f43d0101d1140003c46040e00110f0311400031f8410080c4140c074018908047d43c02c8160070b98200c800240c03403001d808003104429a405110352442c0314800860307a50107182c6503490b0b0146480302011040d5640d07039440a00d800e1800385d070228014110580038a511a803100d10344042561040f1041e02c2240203000108002207110300a44050f07035885108884190005060b50001b451200141c41e8810744802c0b00c002c00b01294140c000d10b2a0191800e040395074144800ca0300700200090303c2440c40352404400c00480c00300440c0040e08183d144034080f0760484c0b00c1b03404035005200398200350241d0318054000144c040d000030081a880e4071a44861066034210a860b41c0c41c0c1c01507024058120900d5104a01545807e440440d4007001d01e007001810202c2d8201068a0200216030844901064040842591030040c480c01c0e150300c220b1600a1030420089403403038032400b80304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 168497823 1250 168496573 168496577
    0x609070810030f140708060403050d050c0412111002030c0a06200a050c0606040903050a0e040617030301030203150103021c05070315050a0f06050f06030405010f021207090806010510 80
    0x1400305520740d41480940c0011a00464000d8501c025800c004651454660600c800c510038070000080034400419818420b40e0503844035410080c591403080080c100c01480d0005160040201069548017407040ea41e0913401800207540d0b42c60303604103200210b42c00804810a55205020320701180f40005500007150b54020f0001c10040742c405417640000312454012034042501240319049aa130120180c4402c200c00d0f4111446619500144406c8134800f80c00a40064020403c2c0030f025401003c079858081e20180000400d6a9520900407039020010302442d06500000010000d524003004003d40e05005241c0c800d150703514550002c1c48082584011803040c4034404801828080203100240065410500301c071840c43c41c4200d2040202030031542201e00d14940880040054020710030b000c240d07070b00640300201e641b10003010482280c000034000c45640d03480d08140e19145481d4001382c42407056805229485040072540548007c4803508544440e41c40710004100d00e9503a9696900d0460b414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 168499073 1250 168497823 168497837
    0x60207050a09110c030c1b09041703101e0306050f0c12130c0f060813050c0d0507180902090109020313030f030e0105072c210f070f031406060907 64
    0x1d4482d80f00030301820004000d03900000c1503a071544100403032024000f80101444003202041c1c103041040d0300384c040c2c03805410210101442411200820000e47d013100c4540211a50aa0303500e200c411aa142201d6000c00c40c1b008850403c00c1040314098190054000d02132003002d4902070046007481d01941105600704600c20020541da0035410118401030303900201c10030b8100b038640901c000b401d0036600c61440080c86441c001a04815401d040d4140c25034040080c1202e6014501048041007190005641c24001c0242c0000c0c80c09100380c01e850118140c280c0400d030300045004014103150164001c41b00c0364010020400d800d080d4000349030006600d82400c0b1012400013104034002c11115000c007040790718000600c10072682141d890111094802000880b100508210a0700441004541c0e600705c1c8140014800100001ca46410340c10135410445a0300700c0c080c1d0080340350003010f90040ca1441070211040c000c2c0040c4001e84584840c904008103003500b000004144e0004c07009103a2404c014078 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 168500323 1250 168499073 168499091
    0xd050a0f080409050907171c08100503011b02010e120f030415150302130e190303091a1b0f03040605150d06021b0a05060a09050c06190306060207050a09 67
    0x8035040d0b40c05041a14800c0080c2e01d040304449644101c42c0c002c0d01c031420f4907103841c2c0c040e401000404a4002e40c0e07105a004407800d0b030b0042a01c1c200b034007030034000104402a80105c0c050310244034404c11403207466070086019070800d4000c1d00319103402110b0121900001a191002c0014108480d01108882c0e013950340c0c0e5465080c0441101d1340031100281290420344000e03601c0c1d92070811041070724000c4580700d055241c8024210200c6400d48581c0c503451304250016502e80340301000445030305000f03040216141c4020340c0c52030050481305500c40b6105840340c080c02810400448441c00c400480941c143c50846000d02110181c040104014882d54035100040c800b20880524500b45540280c5150620002e500d402c0340030390892400140c40d01c003054508060100d0004a804100b90041e010300407030307202c01c0136050180603007920030394880c428241403150584440000309280c119050080803001e881c60801000c0d80c2c01680b0100465000d904203100a81c1c5140c118401c9400c44000001c1d1200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 168501573 1250 168500323 168500333
    0xe01120b0c0904020d091703153d170c0301050415030b0c071a0402010503010314010b0a0f1503060e071b0516080715050f03090c0a0609140d050a0f 65
    0x70521500b59080350021800c080c502c00d20f900055070b024402c0c40340d0f40c0440e254020a48035070208481034000e4030102c03501e1f42400d0401c1a1644c0c1181880014804841c20701190b00300079080d113220101c0c10780251100640000d510841841412002054066241c00c01c5071014000d40418000d252095550750120006690111900402140e110102e440945040c0080415a412860060300c0c0030000032440c403880400d0515151240364140c41b110f043d48d08646800442901c0310f10000062f6584c0c04410095665203a580001001c40b6403400000c203003800c54610301d2906a000107810305003003520601042c5110843c0540c400d240d071074a00d056000300c0000a1640602d0340c806044e90041084030940c150700406a841510705080841e400e180d5211010103001ca840310788440003902c01d20500d80c146503c5001150001040d104880031a1140030014903a94400d60140c00450004d00e01000f034071070714070014102410200c5d0f03210004103258880e5a140c440c120340c020000a030081031142005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 168502823 1250 168501573 168501577
    0x70b0403110307120801090c09082503050f0703031d1e010302121311060a080c03040206040302030d020a0b0a0e03040515040b030a0f0b06070206180103060b0706020d05010e01120b0c 80
    0x158100c0c110001d9020f585034041c2c6150407e006906500d42880000c8003218029602c110890315484010441400d0950884078030556850039071007207956013140080450800c0210500d0025585e01810340c10349903150140c0710084002c0c410341101012a80c00355940d41e2f402900c0d403a40c1c85980d94405402c1103400480003031040d04215145401c50340140a2001028010910000d116004000113110302c4410003543d07001300f446450001d1b420100080b11000300c0000346800c030748060305145c10f280d160f50019040007003552800c40181d0141c102403080c0080d0501080d00406942c1d410031600400401c15600c0744140d0091500034a0300d0742501c0048441c0004641c000d0045c203824580b68200a21510098a500ca9201e202d040c20040f28281914200c401c58124560080c500d6282540c00d0b541201084418494a81455514000042c95a400000810419120780d4005070303503106005014080301c0041c2c114110001c006401848002e0580069003e41508a0125a070581d00c00e05c4007100340c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 168504073 1250 168502823 168502837
    0x61817061308090d050106030221030406051e030c030f0a0b0109170a0605011814010501052a010501060e12030307020c0108150d0309030302010c030b01020d030911060c060105010f0203070b04031103 87
    0x200130041030340c1041c0441035004c2d83c01d42e031084590458040401800c041a0364043c054110706810400041098501510082082000f0954440d11b401c01c1c0f011f015420380c004a56409260b0800000c01890805940500d9030010240e0010482800d038000000c16090140c001c204036404840041c82d048801081200701c60b0764405401d00656850b8080d00e040007070b0448460ba0820304085074000f061101c401070301c1c166003060b5201d90616850f80c3c01101d81103a00b1204441c942031844000c0c0c80004c0c02e001e101d01908031070700c030340380e000121740240145007100c2940c00441d038101744107020000341c3c04699503014200901c3d21503030039101c495428907007250b500c3d01d00d90b1089518003150704140d0066011021680650020000d84800a60590030340b001200c0860058104034a18815280280d00800c6660700a00141d9410712261010580c03035030000e280c80c8416404280100000c2d03034080c007980d84d445890300c051070a040403981e40d81e10b9010081c00c02414030404903014039080b01d0070410740e004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 168505323 1250 168504073 168504079
    0x50a0e0f040903110d08010614070303020c0609071719061508070303020132010308030702030409060b0706110f161a04110405010510080c0f1306181706130809 70
    0xe88109803401800704c0103040300c160040d008641d6050040d90098044504944031901c6654103d10107080503545980b040104905041d401d000c00c7e10340c0c103400c03c0107500c500c851070000c00110742400146003a661054100c41d00a6100c000d501c2d0a01d40301400101c011640400003154082040c1c05404008034180c000003e1889036090000515a054000810032410100341c0d004e007141d820410101e0b4202c2030710f29003142a0800c01040000d800d440107550001030f52040d030782025103860355117059445550001030040701c003290001c00c0c448a48035001031051305003241ca00e07062500803c2c003520b0198030080800322088041d414240a18890094130402c00808030200707510b0300389404500c040d10040060b0140b49043c00209150500c0d40000c03070b0341c50040e00c41400b155030320740800b485640004600040a04184086030086050058100242c012500d50010b203820f121810109540136030f02881c6980e02080824502010114940381c021240c00300e098440c0b5003030b0501c290248136031034000790 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 168506573 1250 168505323 168505331
    0x906031305030d0b18150d030e18040c090e1f020405040f02070c08060c0d02030603010b0607031205090303060d030c0201020718091e020105042304020703080603100c050a0e0f04 78
    0x2500383d0803075112549aa030111040c076001002004000da850508540c1403080e0168100440301d207240034010840701d1446441c1c205d50007125200031412403c0342025031845039105000744000c1006521082c2c001e07240d010740400003190780c0c2140c240d03101018140c00701da14016942d1003810740c1150301250040e000103001072000c8070300f1180050003540503003001d80b04c401e01e50700003054a05d004141c0d58012040020450b00340400c030040b400c001d41c40504295490740d41c071240ca1600ea1220000360034628041e480355842c04002142e40c80039101c00401074401e5410800800c20b0310340e540c2074a18801034040c03900d0202013540e440141d15202d602e4103c072200d5000403c1c006240e19041e044180014840c166100798002140e22440c0d00000403070740280401d505000038080c240095213542100102000c41c01c0701c0e9503039800030801301d80c042c1c401500003440c00000c00a450800304500c11501130701010401c21010018002030480c004d85040d1810820000456140d0355981c507420503d00b000100200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 168507823 1250 168506573 168506587
    0x705070b0316090302031e071206230c07120e040509010b13090803040b0402130207060f14060d111207080304090b090103080306061b0a110a050d08090603130503 71
    0x30441d810440c0c0300c04010b803200d000c8203121442400e91000f2240e010b0b00500d014100600b00b80d4582c8007800c0200018414200f000540c3e000040031a100540110000502c2107801b4641c107540b000310070b4840f0400f80210b018017900b00c40312000c40f0105030304000b14114102201c2d50444040c040c20280700e52044c104414068052410b600040d25040121201043d0320381002c41c10042d200b11000150600d40240b0004010592015030994058801856009503613040c82c9100c04030b0f00308407025518142d80e59080c48a9081c14410003e0b41c207800000440185400b0f0005140d0750700340078004001c1020072a440039980c545803060051844032109841140340c031545c416030b490300300744289a625810034081c60f260b070529852050581e40c00c045a10319564580b000e00070309500c49091449950390034012a0071700c180c2844181c407000d105444801444841008000c07203108250400c1d44181c400003c1c40340000e441408540c3d01c0c03202a59140e840380e40d0b20707040389161905800c0290171400005016 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 168509073 1250 168507823 168507839
    0x8030103081b1605040c110304050d06060515040509010e0103021c11060403030c17090604060302130b040311030f010c02071e050907020d030f150302090a060b04181a0a06080c070507 80
    0x43c1003607031403e0b14108074440b4192412a01140301d01c030050200c0d00100000e20403800c2100c4c804080d2401107601080c600d9490703001c1282170600e220010f07210322011805108034030f02268014010100200c50100300d504540001c0d150002404001c2c90b4901c1e012801c0040100c0d1400e20b4000010090150740c9070f507a203040c080d003100d810034403c56400802d641306001007a00d400544298401c060031141c2041e0801d030f81a4001d62116860700e6542e4050000010382a89200c01080514461002c80d04803e178240d0506107003e038604550301c500d074108070b03603400210746c0010030b44c00b107608010302803002c1d105241100581581d19089650400a603170100403007541c00081e94980e21400b84d4081000e00740f1203030726000301d50505801c0142c0c1002080100b0142ca441c514a60f0815a00400001c000c1c2d034569291034039a00c035a2000028840c0c500910425005910400c10440742859942010700308190000b14014240e0084a01b44407a0170080b41022070110b00356480750340d200044400e041e46516070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 168510323 1250 168509073 168509113
    0x504030e13090623060301060e0714220504050a06240507080a0f1404080a060b041b0807020d08011a0703050705101d030a02070603020a03240f050d08030103081b 71
    0x290003004200c130030101c3c1481c00d051080d03804840b034941070030040341c0700c000d0f040f500340c0d12120b41140100c00900010301912002544440710007601c04001a0807450300040c8002d03140020f12695006190060400a0080728218146c141c1e24519005118559108043c1c64900452402600c40400441ca130103900b604404880c031118500d4480140389100c48500c2082032145004100301504003a42001c00070b06030780c01920078800000c002040d400005107886c815689882910800035480100b4030602640510040b210b2480c42d2030300c26150340c10b01030915007074051030b521340e01c21a80001c0d40c40c0c1890321800a803a8171952010949101610a481708005040821590411402ca0f0840520341080010403102c0070b1010707402402c403081c9007000540080d0440400d10302815150300c000c0c4410000c0745000810095200880d03000241044210003039030304550040307401382c8400039146001c10071903001d5030f045075440b075032165a82541c0e2171100358455010a120300a84208802e480e0643c17500c2d18 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 168511573 1250 168510323 168510371
    0x1814131107050606220213081014010501180e0604020720040b0f0d0b07021c030f0606090602030415030b0d0305070203100612151103010b0406020706030504030e130906 74
    0x401c0f68036680351102000702490320030105250740d2100503441c4d40c825030160060150480c48044546a695480c40d241d03090029040d9503085d4256112480882e1030103500c0d0b00c0340505000e107016000c103100740f001d9141002c858060400c5080346500001c074039680f590100d4100316071242650001084256900c6d4446805000642c400c0f400c0c44078860050402d44902c41100e8402007815540e00001d4803000c942900c080d11007011801445005002c01e035240d020180030645c542e6000581c5c1c140c0200f801c08481c0c03141c0001040220414042008540c000140d038213030b5022014007900c17110010300640003040601003154114040c80d100006064120340684001d6000307800341d551100240001030304480c7c86005805078014aa20f8030070104201e42c0345412a61f43e80500055140741c40c1d09282084d4200340e1040c1600e000004041c0a40b5a042c4501c200405060800780060f04103503402400501c41d0b031b8030181c02480c600201110070740c2d442d000105000c0d0004800c02100d55410404814150200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 168512823 1250 168511573 168511583
    0x403050f0106080a03090e07090902030c040e160207060807020f0109060f05060a23010302090315040c0b12151309110a1d04030e06040e13020108071814131107 70
    0x140b0000307103610045507040b0196411b9031512105810100d0518070240003501400411031074400100d804c0a9502c000d501460f112501c65403a00d1400c1c204410511000b056054011550041c80f4482d13600014010103880c61410020701c55035a944080f450304094400303c1101358200b0203204c0078401258480c00002007030003020302c0683c0d142c0040c0416030b00c0511034202490913049040e0441c86035041c22000580e41403601510380200b50340002d1400d4030214403c00c96028400511080000c86e041c1c110003000460001c3e82400380789040349501c0440207121007441104807401e9180e5607940494290600060300080008142e07900f080d41c640350b41c1032086806459031250204031032000f01071640c0068805e900d59101e5690f0780d5412034181d8000c80d045608618280804119104060a814410818641031104164041c00010030308203003e4100d0040c460040c01e558440c10600c10100c3c1901c5800301c604080310407681c04140101110344141d942649081401200340d2210b20041c51968015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 168514073 1250 168512823 168512831
    0x803061c0c03080315030606180c090909060105180702060a0902010905060309150709180b060403021002060403020c091e090708033f0a150b0406021e0106051302070501110403050f01 80
    0x30400341503132944161546a446800d200442ea854000740d90004e41c4075000c12b070700328249100c03840440c1c80342100b07039220389298100b580113100e030b8201042c400c01c05151050240c441803e0a580c0651201d40c0500184000c0303403200f501c1c07403e59000305240f0005200140c60156030380b0741300640741c2d11524030181429155490341e0104004505c04c24900c0c060314088003802010002c2c507140d41005280d0704e00499000035040c0400030250b9030b51519180c212078180c01400651a0902e0000d041000000c491307031280da2504c0903c042c2110f504045079007151060007000d81511079001051808603540e1141070a0311001862058103044aa810002d00194140d1180c03404a5013200320f04200740c3e030500b400e42d50003a40000d2004066070300f0800403116040e51122460780c441c0c0551800340d0040d00400c01603804401c0d000d400000b02d943c0d01c074110701040000c01c03100d402c040000c1d041000d051400d80031103802048000070305c03000b0741c05094a880c004c42c0303450380c45549140450311058220100300c159440c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 168515323 1250 168514073 168514111
    0x3050f0f04030b0405150f06011d04090210020d0909110d05180d2d0f0804110303030a02031e24010e0301060609050a081902010f0c060504030806030c010302070803061c0c030803 78
    0x7407422040c008d1105844012114481c680b24002c1c000f401e60145038041d07210b00014000d0303100c2c0032503e0300d10781e1107901500354080d20410183c070001c220303030015121515009449a481c00c0890a603020300804140105103910b038480c5089010303200c0250000d03240104021140b00c1a00b04415400707100c4007000705407040014040c0418080c400c090b141000ca2111055022840c2c8100078156100f441041c66140e081d50000c00700f407640e002150704108551703001051100c03070500d41200b03c3c11128940320040c1d00c0d180680103140c3c5100094200100b040802982c40701d0360b0b01900f1038103900c083c00b070002c012142d03032800c006001c1043d42c400c6500541d800302006c10035a0000c034508900401c00000c00400021650045075920381c410440c4003000040030106000440a0103160b0156002e5038800e0f00030b003000ca04150a0140311090b89040c1031041010030009804442900e80c407000071154090002c2d4150b10103146180c020000400180104a0220400c19450090340c000c00c400d004031424448 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 168516573 1250 168515323 168515341
    0x20114010f1d0f011502031b010c0815010f050f0c0114010e1321050d0213030201020d020703050c090a090c080d0e0a1809060f0f0b040e01020703050f0f04030b040515 73
    0xc0b003615010811020381005003c5100d0303016034101520010b10440b85044048024803400c45445100103100343d444100100c0e04641c0308a1310740d0403000741e084044100600741c1c00a401c0c520800c0b901030610501003510800008554151145220784000a00c0000541a030841c1d01385c109000348111200305101048025000a440d192090717884000f007134040100100075170540304c0600d600020000100031000c9100514006021800c140716200c4600c0b07402c44c400a070401d2220801c0404540c46000c04102140c00043c0c0c408600d50141c410268903151454140c011384a04d403800b40107005030b11070018005000023501050901c082d955900d00e00405000c210745c4070704034452009084c664031121416106643d12a0400c248200c0340002c03600c00d546070000549540081c0140c68990320382220905003058010614039141131b1008502d007044079540a00351b400768001d024038041d0085121044c00c0c0c440003c4501464110703090701318a1816150080d621a10241c2d040306100c1440c0100d94040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 168517823 1250 168516573 168516629
    0x31b0c120509090a050615040806100b03100902071e150b090f0c0a03090b0c07060f0510031403040906260604021e01020109120807080f06030c040c020114010f 70
    0xb401010f20301c107611503001540c05000081c1800d5404800300b002d60032105c007520020f000500012018007a44d1a041a03d80d1803440b0a078407041e0595410001c12141404007600c00307041ea116a54010780356410b6081001641034680d08012050f24040d18007810f12030102c0c01541c2e009240d03041840044258030510800e00010f8456411018100020408240c00c84000d007241d4840b928001a42101c0303503c03001403c50059400109841d80010f241d8280300d22070040488240d13405506000720b0030047c040c00401c004620001d4407104200119810005052080718000c102249090140c10744801c000f68158181040100145810580c191884040400d00f940b140d41c000340000f01002c10800401951078401a056045544e1840101c000032890b030121507141400c2e43c0c0d03644040c0340544000c3c01941d80940666a4555440108440f41e1b40008041c050102c00760350120f0b800d10118010b80c050060f501c900d03c00200154008141060301115000486200c0310706a5070303641c42010804441 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 168519073 1250 168517823 168517837
    0x70303020705040513060603150e0106080a020d1a0f06010e1c02011103040e090c2103030406020d020f0a03200403080306090705070b07020304090606050a020d0e01031b0c1205 77
    0xd41c12810040000b454503070310880c3c1c80804111914450005981e80b10103d81858104850500391460b00d26020320317091207001c0c1c03c5112100200005820800c500d584d5400350000240300f0071344060040100006c1c04842858140d1a40f90181e180c00d00c02d2442c01d10f00021980c09000075008811100c440c80c01c806408600090480c69003062030f000e8004507050010020112420322040100065218042000364401d41a00700a00445e0300030f80300304165241e00c041060880701500072507051510307002c02241e421590050700181da810019881e03001074080d030300c3c002c07011610101d08010250b40680168400d80c128802ea44010090782b002810315019900015004c0d003c2400010007500b801925183c00c202d990521a0400c05070360b0f540c80280c0c07401c690303010040e000441c003000307020054010b1001402d11030622508040711054000c2d07551640301000c1c820850151005249a40070f5809800e8484003105003d80c080c150600240c00a4424038040b241c1030904007105002900c079009a4840d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 168520323 1250 168519073 168519077
    0x6150c06011811160302030405130f0501050402030c03070810050d030e01080708070c021207090504140c031b0d0c05030f0a031715010f03141e13122109081209070303 73
    0x2020030130410031140341420403044095200070000030034030b0ba03581d49442c40d950501150202c0ea450046104005941041e4001c0f400740b801882030101c0c0c09040700c1680d07403208940c980030541d59100840644011500d80c00381d0707000400a0052000e06601003092400114280c90309266500c802104580803441240c150340000c92400321800146010440c0844440c40001110480c94540400d482100d900350780c00c5a01d00300802096250070818800c85504c05400c90241c80740800040100201303500107a85a445400d0000f404010015051a080041c0102904580b80c4440e41010b0641c1d48250f1030059011842d40d08810140504d80025140705d003035004840c0341042202401074035100c040000c1c5c075041c1a00c0314448500c0c00c6007000c0c0f0b584950494404000b01c901089018980c0c0c820203007482045400c4089400080740851100300319107801450181c40000b121600d841c038550304105440d54480c11301b01c0100900140350064007071084424405001c60f01e0311981203a40352514440100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 168521573 1250 168520323 168520327
    0xd0f0207120204090c090e0d0e0a260d03051509010305120c070803070f0c1d0f060d0f060203060a0501080403020a03030f0e011d010c0314040b06150c06011811 70
    0x104525540c405581d1161014101281c41104c9075520070740410f840c2c03c404004d696a42c0314440b000d03030030020148000d9250070841c00c2c0c400307100040b48140340e45001f100b14811480488801c0070040f0f0f10b0b1141101445815a681030754501c0c80203010b00420354040c419814038203402c0c1d60300e18100c08140c1c12654804000c00c0c80b1a04080c840c1895080340c02108114020440002101c4c5000e00040c660544130309400c4078078110f41d10300f04c2100201c542044600c20361040c034000c1c081000d00c003415000080c101c80000682e556100068001904510050a8940181c0f0600401034035070099805488101e0b000b042c0c1075298001101d103254204c030094010b0707200b0010600800e000754032082e180c0240d0500840c10100c400ca02c242980c40341c80e0a140f203080b01d8002c1074400b9100788a1002d600e0000d1a09200700c01180080000e8030001402c0a04a0951200850302c142e88030000c07582c07006446141682c44003c500ca105440d900c003441008240c41035128840944400d9100c0d80100504140c09a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 168522823 1250 168521573 168521579
    0x20d030e03040f0e04050102090d050a0201230304170405040f02090906031c050c150103150c02120a080c1e07140a0f110312030907050301150501020c1009030803040b090d0f0207 78
    0x20541d03c00140c42071b2940d5500f0011211203445d50080125002c1c0104020585101d091000420000c95038042464076604520b032001d2800401041301e4015400034201c1241c1c1c00c03011448480b85c4202d51089620501c1c212115041c44419000f600703c0301d104880c844407540d00c01c024582c80d030303525880007103078080f20041c1003452501a0000e0311410030082c007200c1070420a80c1141c401080280c0090b0f500e08081d5030440781103801c0e4081c0300c1c480912403004e460000c8118400800301d0040d480b0b030b1814800309100094070070b0703910000c0d12014031a8061121150000500121565002c1c00058a010f00383c2c142c84031606000152400d503850348400104001c20607900d03490384850750386160b19454018042a0001e9810bc80b000d14051000c1f00094880f451610040500f141c0950700c0d40344885211110401c80d582c0c0108407045540f6040e92040e1005007110000c0340c40701d8250300001c01512010061106120180620350b104041d85021070740b50740300030b990603941424440740480040c0d014200c28 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 168524073 1250 168522823 168522839
    0x4090305030708190c0302090319020604050103021e040f030b100501050301090c030e0f06062806030c020307060f0504020112290f0603010914010b0304030e0f010c06050403020d030e03040f 83
    0x50703100c018240144130300d40105080303c0580701d0340343c0d01e0400079401240c07500040ca4240414005c4d03a4601a0b000c507400d0070ba9000c41d07201e0013035209480c1815401b01d41904110a814170300c115040f2014034450b5610b45490b000c1c0c0360240381d40019100d4104410004603090200700540d400d56405840f1507003160300c1c06038943c3c0900103101c500000c040d10b4412411102c401004055100721541014090b14075140047c40585130203c11801e05030001010300380300c5403400100301425141c8a103000315400d55105d4090346144074a0303000600991428017404040d40c001d902c46409140300342e0325407900880c140c000406941e820b441b00c0042a019440301d400410040c8043c401c01e50001d450600c000382c0f005d0016202e90000d80c402a2956100c078400d032a00040802900d0160144100d00c0c6e003141081d85000781044003040701c8a00540304600c641c000340c0c0c00b400d04903208070351021080c0407510f0686802515462801941c00101e820a8108139002d00007000751429a0074007200d00c800c052400c815 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 168525179 1106 168524073 168524087
    0x50a0b03120403110d0c080f0a050709020403030e091b04030b15060c07060f14031e01050103060b0a0318020301060f060e090402010c020105090301140a0c020c040903050307 76
    0x400e200107400c0b848210613151050321417801c4940c3e80e02c0d00030881c0c25560070100030b038480d0b413000300380680e000114207500d1841082980d0740b159841901806070b0040b4000100450328820400d0071509203002c0e083c0d840700a003610314966941800c03107510701e540241c10569480c05c4e11320030044080c4c1d1003610302007280310607144c95282c00c5041d0007168a40c8813500030902005800c011044c1b419100d40c060150b800c10300100c4564904000c0d81c0658070514480445882c0e0b900d1400008a66000348110802c80c0d118905003071501c50011030480042c038000e4900300800f101d00c8018800b58030f0910801d000340002d800c1e080c8509052180c05085a030101c48018499140c4604000050341d01c00c091000503642800c0c01034842040c207001034094005100420760420403941004881311058000c105908941c0c7c003075400e001081c605010035110b48010203008240100301154040d031003030f90 = true := by decide +kernel

theorem cover : BRFrame.Cov 168345323 168525179 := by
  have h0 := BRFrame.cov_init 168345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 168345323 ≤ n) (h2 : n < 168525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
