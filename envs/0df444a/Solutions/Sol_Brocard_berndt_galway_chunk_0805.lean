-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0805
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:53:56.627249+00:00
-- url     : https://prove2.me/submissions/fc88fa2c-3ae9-4f8b-be8c-b4c9dda12009

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 144604316 ≤ n < 144784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 144605566 1250 144604316 144604319
    0x801060f0206150109050a030501020406031b050913061512050c090d060b03070803180907051c3b0c040213030303050705090901170105090d0c060914030f040807 71
    0x14011208088880038640041215640e6501269010407010700f00303504205040500140e81d8035840c00c100050b42c4120300260300c490a00307100038112039190400020074800544406c2d50301e50000202c6011003000d5038215404602100f0032000350141c5d40c0140c80e441d001c41503d400352035200c4190062581000d205024585030030350740a5040c01401c1166902080032846080040d07003d51040d06072500203002d5901881c0da4040711821500320341c4400001c09034480900c1c007949001f0348259808046800d01509103441403002040207001141360510056443c1110005098808807604c1c40107540d50f90b079000ba0f500d0300040083c0c06103203406100d8a10500100b00c0303803481e2a000b034441e0500301c0360444400500d180c80031000781c5005084103040c03080c1004810507035190569400c0c06803c1e00344486012001031781341c00e4212100140651000c0e08407500d0241c010f5400900005015000f42c400300f401d5045050248007030301c3c03101501d04a44030000703400c0c10b1078800300007402c00c54244105440609 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 144606816 1250 144605566 144605579
    0xe03010b030c06031b0a0c03020d03090f02040f0e03040b07050c0a050303030606030703020409050109021b01060b0f1309020a080405060f010302130c18030506060f010507020612180604120801 84
    0xd403000d00300c099040c2c0120102c009181000070245601c1031000c03209241800009040750540e5112090080004903400d2001c414582c040121201d050350902d0101300b10243d030f45500200c50f145031b0300244115182c0c030f03060640d00c803280c104508428180e03050380c0e95640d07103140039810b603848110b08a48038002c3c109940700505e04104000100c0d18054061172455980504200c110741c0000c0070b407420f256080c000400e20302e0052041c01e000c0e05006400580da9035070103005500f103031503071440c2050680c10280c0a00881200e10241e40340211081c1040e500c0c3e0101d409031210300d581941007403100501c00300b141c015082c0d00c110001d000341c2c00341c002e031051a01e81185100601c0310034000a50030aa000c02180c80f064003540c00308550703965a142020b061810105422910041030340142c8040c0c0c414000e2042e54a403c280040201c1d1090034500d03d05405a0701090070b9000310032540a48441300ea00068194640b541b008401200e104162155450f041c9400410b04902d070a090000500c04000403820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 144608066 1250 144606816 144606821
    0x50f06030f0402060f041d04031103090310020d0609090c030209100e070c0f02100309030905030316082b0504031205070507201002010b1c020105071e210e0301 70
    0x100d900440c011002daa8940038804280e00014600c1054142004000341c40620400032200e0500050103584040c185400c0c01011041c816004440581040102145d19903001a80000020b04000056141c0045007810002002d8691080007480c0c1440000010061051003020540f4802c0758000c0c0703181c6940e41e0f50040e030b80541c01400000303007040d4003003210640203218200645d8070502010b84d140010b45c2c00f2a60280ea58801000420780b00d003001c0d02015003121120000d031000b503000314141321160008030018035450384098410000020b00e8040070301c0903401891035030145083c12054581c0c510780c900060204882c00c0d4009030361980c2d01400c41d00c0c98001c2d20b010b001582c2c1c6503820b089007a10740b1801040141480d040c001c0d211b000c2c00040362a92601e0b016a0211500002a02da0a45092003c82043c0f020b4052071010300f0300b103800050384c121081d00c0c0c0c003d8000c8a40b0701c1c6000d0402c01141009044040a000302e0b0304a00510341d08148014070411500f84c41d039500c03009081c040249403e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 144609316 1250 144608066 144608071
    0x9040e06010602030a12060306020c0c03010b150a030f11130f0509060a15021e030a030506100807081003050a060e0c0d1718040203040c03050f030309060c090303130f050f0603 77
    0x103810810485d00204e214403922041190715031000503040f692581c1c0c480407644031481168058100c900014020315013032040e1010014190f954240d020301c540e480014600c12100c0801c01d260b5155a124800030a030392265440301c02400c042c2d41c2c0c90280c2070f06001c4100e6070740b04800805880100c04203050a005400b0ba00401000e0481c035402410a84030310760400050f428a000c51141007411807101814510582d003601c07014000d15a181c80d8010b0003001d0350300081c81c0e20701624245250074181c6a02c14001caa025507186015600341c1c40382c0300c0140c0082801d500c00f0303240c1c1c42203100c0e030403c0c80a1036100700d0b06029034004071105c41c000c1b403060059482001001400d207000014245480307142c0720004000d0742c02c0ca0303403544031030006243c0001c080707800c150340548200210348000d00070082c04104682c4030b0483c4200860461074040c1c1c5e9141e0b5164000d003d80b0503120041214205030310200140d03280c000707200e002c822480c5d881f050344003006200ba03c00c2c42d11551a8030034407170242c103001040b01e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 144610566 1250 144609316 144609329
    0x60901020c1b13050a050603010c03060e061c0b040b070e030a0c060e03010609050903210c0717040b18011404050f0907180602010504060510060206060f0406081209040e0601 76
    0x400d07010020034403250781c5402c41000750041082030740d03075a52250030711580d44504800400007a0a040c0300c0e003031500f1546101120414145000c0701407007400c842c200400c0d0701c41c10488844100d07098500310400700313010445004100f001d040d028001041045c00d0454401c4130203036030300003902441e903040580d01c0d1030070840900034407089401884024814104103c80000250011840039941d410100440310100c400f0440c1da04040f03042c3c14800d0b540d04108400c124900200401d506044c110009288103281c0020400c1d441d0340480030410040400351401080b03403914103500c0e40d0b400c11110510600c0c410090f03000039001188400421203010588040c0c2d07801804170071110b1100024006000c5001c0e04003014001740170388214214910402480240c601e0342d00200c0e071424145403020a4840c040c080b480c80614081080c00925800900150701c8802200c400f503400400d0808200240401e4000054500480810350116200d86004000f0798001ba20100183da01014509499000c00c0c007501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 144611816 1250 144610566 144610573
    0x3060506031b0903030409090204050105010e01080f04030903020904060c020c010206190b03010209032a0603042f090106171003030e011110150306051006140f0c070303020a0203060901020c 83
    0x7039024610b800e400c80d603070a10040d4403882e103140600000e103103810991003003c3c020f890761500320840c2000e009040c0180340070300308420300c0020800041c2030120700521511401d40c0160002e0181441740410a00540c0c001d0032100b100d0600d42000000f41400c0c23032850001d81b0800c0f514600d65440003500703d202e090015011500145030409003805046522000ba6141d074003440303005007643d0140003a041d9864018111510410381c000e040e12401c845501da01c1c8543c3d002d10810010803002c0c000a12164981c0d088183c0e03142100e000d000c0c0d0500c0701100d01e9000032408001241480d000030210500c01e0074064034a0f20340d80d80000308041310380365001c010009444a00c10034520b5008810604901d03641c2002c0d01d408042c0c0c03082002c220340719001d981c0d4002070303914030030018005a8800c0340d40007400800b4502085080181c0600b580004043d4800c003201c002030701840010801e419a403541070220245c1d40d500d0b5403801c00a42d81c0308d00d0032099100f0b000310008151556414802c6940510203e4040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 144613066 1250 144611816 144611821
    0x40809041a031009020a15020d1704020105041242020313020f06070b16080106020c030a1b030206040f0e0c0304050d0e04020f13031202010b0d06020f07050a0302011b0306050603 78
    0x150350103000f04000480e0030400c0001b0201b600d51014410b540c200070141e0040c0134503840c0b0300c401014416413940000001c11103038180400760364020229415140c44030402d501590661400c800d0b01c00b04030004001990505a4034036803400946030100000e0729140101800b070403114510002c901c0155040b4422501c04440e034001400c001d00c03e180031100042202c1c1c107045c910780740c0f546044012a013134480d61301201c1084000e15001003420b409402d00d032009082c40d4003284c2c003007a600c4030104009004c8007001c10700c5090301c4814441410103150701a007681e4480c0c3d550040f2140c040e405000e000c060401c01400100000228415284201c0d0402d00034001001560700a84a40416041c00c030b40040d020081c503501c280381440200414194040903650710340c50b508200b0f900300b1451083c0d4045904020421609a03920b02d140b4641c0e64016400596485010341a48011300c11000004c1007400b80740160001d043cbc065011403040c0100035207101410341303402c204a044650502031507501c01d806002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 144614316 1250 144613066 144613093
    0x50d0e070501110129010e0d151803021f060b0a11010606030e150c0f03090c010809060705090f0310180b25120f060f0501031103010f0b160803040809041a03 69
    0x11030020407032060401d01031011f1080e002c0f8142240c01481500c455140801140310740d000e0380310741c51110800813110740007400141d80007511859000740f82d11010404520702c110700ca9050340410b0081030190051756440c04092030140050100010200d0310354a010b400281070380c064000c00b8918000200600003c0d010703030084142c01c0001400540c40c0b541d0600c8042c201c094128021030040c0104002001c80d00d090343c00040801e44002d040d98065048401400840f680100541e800c0c40d000b1542481600964804a0300d0826005403500310203050071015406600900b0203204158001c003113066480d0307503a00d401054075005110b10803070a0102c20410306490322441e582c2c805c1e0f9071500300c04035040280c144c1800c16a0302680100c841c01c807074210204010360b014410422040031141c060342c1150f1400c0c2a00790f21410500c0360852142001441038016216500c40c01122640011580d8583c00d080c04c262109030030103551180954601801810261606484110307200e100034014800e020f8100c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 144615566 1250 144614316 144614381
    0x120203030f0a03060e0a0902032119050f12250c02010302030c1c060602010c02070302030a1101021e010603121704032f06091908040510050d0e0705011101 68
    0x303200d0420181c0d600313004641e00c020021030b9400b81007482d001041c41c484038010107081c140d02c40c3c0703401340700c081d80c1210a02e000d01d040150351004841814510719102800425070380f9102e04069044000b100003007418138811010174050150303158a5000208120100114000c1807428070b000f004940344102c00d100540c460740003135030320500c407540075810300707907211107460203078943d20302010680c1d48540e0180039042e030900c100101d100440c0700900c00070303246401103078880500c071002500c903600741e0301d1156060340204200707a4000503000035042c0314035105040d5402030215000c1141c0300007441002903412b070f114200d00c00000e05881403038551601c860390155042c030800f40b29080c0034405428440503822002c2e0448420700e4054028084030320748880c1c41d504211a0b030b16030140c2d41c5500c00581001c40c0d1742c0800c3e42e041d01d10030349856020480030300b419155030190384600031400d82406030039454071b28045401c00498400782c903012003c814500391380e402d0b030301d0303681c1c5002c00d000900c80440014000740 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 144616816 1250 144615566 144615577
    0xa08010b0d0f09060f0b0409020f040903030b06032e03051903020708160509090a0305030c0a020c1203070201090e07020d230a050712090501120504030306260601120203030f 76
    0x400000890021401007107090310844681070314529174880c1420805000303801520001c403002c84007046024902c0e03001504649120480a015a07a1100390104060007580080c1175108020411512440e21007840c0802c032940c010303018030100c200c0751380084138110050440c0640750f01001500d00080c0340050b50407402000036065045101e03801001800440a202d8120a02e041380c03c3d032910141840140316044601404e1044130342d0051510001181e403200c25644c0107007000c0b01482c1c0d1100c1c5a4001c038036217542280c0c5030b544503100744280040340324004010014980300b80c803011581d03680c400100c182804220340c68400342c0c202100c50b07001644190b0034070130503c0084100100e1400302030320101c400e400c10700d40c19011900014056040c0001a0102e83d015100740c980340c00014140030009000460b078650340c10102d510340740440c080600079080100a8504032564400c409020703c207140f0200700c3c4401c8880c81e030203118000303c1e030b041801c00c01c605500c0c2c0180055203030602442ca1100341c1d40c0722 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 144618066 1250 144616816 144616837
    0x9090317040f02132a0c0215040503010606030b040c020a030e010507050322080f0c0a0620060903210906011205120304050709180201090911070b04080a0809030a08010b 74
    0x1916142d07001a590300700b00d0102c1c004081c0001070041c0000c0c1a664042c1070548140494056807034811a940d540031030007800076641030340e440c91b5061780029005c281d8016034000a03819400c2c8000441e03140e5040d80700c1c80c100c05089406111082002000340e858420b86540900000c8a8035013405880d4000d0300101702851150084074603011181000d084003120344000550542c04500c8100b240c03a0b000c00c003d11030108504040c01901402000194405220b44290014401c00030010040c1c5a03082c103165003500d13074090907a0620315101e24090b480b944002c42c0ea030161410010001e64085911907141e118a202c08014100742e420301c3d1a0709081d400302c0c0c3c42110244070780300c3c288001c010030304041c501503841980108180c2d41052951001c0d10a0060b1015840c0c410081d8000540c6c1e02140350b40880b181800000341d01185004603000c03611032020060410070450040c0010080c000e402803829003a0b590703403020141c5a5030020380d1284200c800c600002840000140002004c074401442840d98 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 144619316 1250 144618066 144618083
    0x105090a05120f0129030f060a090c080604051e0304320d03080f0a111e210a0501060305010503032205100c061a1503040204110403050607090909031704 67
    0x10700c09002c3d802e607840303100421800e551904982c1c544a1340d031002d0301d4030580d080740980140f00140340e26550b42d0398000e140142c2c45403249902014000c650201c00007900c603000a07680b00f8941400c2c5580d0ba42e040426940c0c1418122290290040c400302c2504e043d0f654078039210340b13038a100c1442c42a840c0b00184600450b06110480e00755181d03258414010a0392094907400c506180000c401700840b41e00030301b110603d03801d00620102a000f42c90071107585910030300c1030340002d214210844038035014100300b80c2ea007001900c0d103421040041c0490140300e00c1002400340566a2210320880580300c0130305c212a050343c001c0c807400c248040441d107039003401070002007810512980c400005008191000078800443c030340255a0050007224000c40381140c042c100580b44071104040400e2040c045c0055400d44c03800e001c00401c04668481d081100d580420f55030789515607859044c59520380c0000c2d1211004600c0c604e10000300c04a160003801011a09274440105980070143c0d110b424400c0100120364a00c17 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 144620566 1250 144619316 144619333
    0x50d0303020d11070b0f0a02040509010323030a03020c010e030c060c18090f061f050412061409070602070905040305030f0402030a0204290303070b01260d0302180105090a0512 77
    0x3e0544003e0b25600d03004001c21489030800b44030703c4030601409040c42d5901801000140010b4541510b03031811030303600075040103600c1c00b0783706402c61440b00c41040c03d6007800b0000380141c1c40c40d4140c0141c11442c4c1d1110080220504c2c100015070340348a162244902900920006408610b2400c003034000450314035403000550500600240f548c007411624481b02a485c8000d1000300d04040c142d62002c125900411001600c5550000c0e280d800ba0b88220710b10048441d00400c104903142e0044204210004802a10781c14a9240f0a45a00c05030044100512803c400040d4202c82c46c0520340c05240c1545506155485540d5440d4810000800a81c1c1601c1003050880041e2140d11481c81c200821520414001c0081000e04114020f80b4503400c4c4658803d12a5401003820401401d045651030070b4010118401101a03071480b01d090002c0c10050b0103204400c40704150507400510503e0420754403c0c01103180800196100c0c0a110710864101c204180148103609064580c070210005c8901100d400c003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 144621816 1250 144620566 144620591
    0xc0509180106080105070e040902090121060905070306110a050a030c0c0203101a030d021504050a020603090102040305070b0406021c02031303050a120206090a11190b03060316050d0303020d 83
    0x50b001680140c00c580e66600c10091704960103914048a840125001e0044c03020710740000305550010700032602ea496261404100c2c544600581940085d4030540503c150150342c141603840b6803071403009035441c44c2008c407901d42d44280075003243c480d855146c40c0c582c02d0014030b40080300144014120b04041c0840c2d0b10502025079030070030001803e509284004201846014100c0c91000e0910b400c0f640a40d1200c03c2c0f10810940104c0d043d041402c3c1c803150300d049685c4030b04005242c20b00200300a9080300000092012400d010340040068a018400300c4140a13901c48141170320384614030800c070041c1c10400d4000403840c0040e000c04d40303030259071044a0402018500442c1588041e82c412210f503403000154908003c2d01e849078206044540c0040c00b0f15242091071507450b403200090003032403480c110f01035080d540d131001c0000141c4a48101c00120180d25000b000c81c041d80706a441d40c0c80380c03055034501888003c14003044010350340c01424484900c0c4c8a0341d07081d4069040704011982c4d1985034200d0100d070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 144623066 1250 144621816 144621821
    0x60203011511010501050609090603030702100810060c0b06010f110f031b030906070f080c030d1a03120d0b06070206160312020c0304060503061908280c05091801 71
    0x103010005601c1121840001c4080e00c001030000b803015181e410500100002e0795804169840800140c4014009580320070000e070035441149002540000402104180107602c883c20610606518a00d85040b6407102c0c3c007500c80c0e0110040050103440c0040005400d54460440e245800c12981440304138061020441c80c00c15914040b202070315803000c039602407038901c08640c0729a001a03280145290050020115140c0d02c110075000c4c140c55150040d51702008840400c5901714558541a692552003070a400b00240c2030340510791000055903854196680780224812000414034150507103007100fa0540c520251440b01c2d50761fa0301c08400d1081c040982c0740d2000805000c200b41101c05000b807000e00e401b902d1640003200a180b83d42c410300a151100000004440c01c0e141c0301d003002502da9032008000780008210302d52401e404484508005000e480018200c90740d0240349003020b80c682d40640a4000c1c5112407880074060340d0805000704036030700340583c3c21a001b6030750303800041c642e0241b4501c8500703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 144624316 1250 144623066 144623069
    0x18080703030c111e031005010e0109150b040306050a0c0201050702250e1611060408040b03150d050607110a0309052e02030c070b04060c030f050d15030210080702120706020706020301 80
    0x240a00783c040700c04c43c51500344007440c0280d050b14410081d0f03506007000180008014016440c0181d61000750b2048070703030464140401441c14600d03c5589603100e191120207060281c8803c5042c0d42881c085080160060003a203229802982c010000043d400b480b05410f0b102035483d95485405031000480c20941410429118030b04d50740020b8111184d5042c000c2281440005622031078018009100004040d8400c9030100ca205042490720303071701d40744d01054a400d11601002d43c00460035030420104000413920034820300c01c03925483c1c48040c6941030a511031100316001070000c0e00310310080c0820b1800f07008511594080e6100110890190315003031403c1c03903d054041001d40c0c804149840c403c0700402044001e440007500c03003400c042c50540007820040803140d0060620004500024000f072103803007501c0081030b02180c03d002140a07000c1c041000b09450009034049c0c40c240c54480c035694000e403841c0d4007404151f4000c000c0c180c0c04074024101034100040403030f2540c2c0c08000305000b1950a001450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 144625566 1250 144624316 144624349
    0x60303080906010602060f1303140c0c030106080705010c02060304050f12030109060f0308030c03130c06090e15180c2205120d080610020a0804030c030318080703030c11 74
    0x10024103141c8501840c20310140c1c483c40856106804004012484030fa5094000c0f01c07034869454071101600e000d03950780103400b0f001d02444034007054500c045100015581c280e203909400070480f07a85c50b03420664a404590260901181802c2c00490050400c48020741d032090044003900c83c0c07a018410018142151a0f82840e003030000840103205000c034911404009011380401101410716582c0d9414031400020f200c003540c00070210008a01410344c3c0c50b0480d1503031340700d0403e000c039a40765035003c2c14003101d81c054052000182c0d000500340b02000b14020f070941000404100310520004001111800010800f50441c0c0c014011b42d0389283c81c002c501030b55413500f6030030807111500701006d00c25003030308503244240b00350310000c000080d10340c00c041c401750494019038090213444003405003a031030709010f108002c1980c503002500001340b00c5482122412390f4441d075503c41440030754031082c40b44199507000345100c54101002c1040040d0103070501d00c038400c0c0300f03000003180308401400185030103480c0803421 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 144626816 1250 144625566 144625577
    0x10f02071202060f04020105070609021003020a0306050a030503040e060a1703040e0901051501030e03040e0a0e070503030c0d0f0903080c010905010f020c0703020f0a18060302030c06190309060609060303 89
    0x18020031200c0101c80038402040d20081100f89800c0c220400c04050203007001e8140180007030144280142c0340c00101029402520b5001c62030302807200103000b0342c042c101010000c0d140c01000f090741d2402401032000c0740d42100c01035041a0921040842e00c48000d08070650003048194009540340107141c1604142e80280c0c0999100e515100800010b0f0700c00406c4102207915040412034100b42c40d1902d4404044203180006040b4019080c681ca1803040b5080040185030301e104111007100b880e0400009104040c0c140c840c050b60718070900d0380e80d00520790b03c440d840d048003c1c80035419216915404501c3d8040c42e1a06c50a030b529181d0325140d9006200d0550a41d450781024424060240a144803060301036204601e80401e11043d107881e0340b03180c00024894a01e66030f00c0c2003556900c1c0103030f074043c0106030920380f25064030b13009480003000c561000304e000c2d015502c4122107520340041500d0805c03190520803201c0c081d8005003200182941401120440d035600350200d041290b0b4803960b80a03501c01e4a40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 144628066 1250 144626816 144626827
    0x30703150e07030303021c090b0f06010e130509160614090301060b0f0a021605060901050919121115160f0501061401090b0306030705060d0b030a11090a0c20010e010f02 74
    0x20b04000c0c00a003402c4840150608c007010000030101d0340300c164092160300700d800c0ca9454581c012a00300804001851307000351600c4002c000d62506612042c0121003000464501200780c0e6000c9009050622456011420ac07011103801400564010b2180d8440103000065141d2103910300452074005109140150101144c802c6606804105400d070603e01c4101d0015100d107044006400c4e0303c00c1c011800e0401c000803450300c0c40c5840b2030b00c080c042d8000102d112460b19441d120381e80265000040251020138005038035510f6410000c0c00c071071820600d221503902c1d20f500460118010380d845841207031001c403145040700c0410320a00c2008040c040790f281c8000c000a6850005003500e00c07540041c22441010000d00c040356400045c460f08481007074400e140c680902011900041181c4038074160903003e0784206400f004007030007211102080c1114240c038281c96500011048840d1203401030003040f6007110070307043c50f89650741c414490700d60500007241c030010191038642034030702c02d400004155801250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 144629316 1250 144628066 144628087
    0x2190b071710050d03021e01020a0206250e0d0f0b07030b060f12040c09020408060a0f0903091a0705150412021225020603092a030703150e0703030302 66
    0x50740d04080c4440c203141405060103680110401043d1140c68812605824840308050080c032040404250707110a140e0300c414440c02c040d010b540545107450040c0a420001100d02c090365000f0140e2000d013035151058080d840740280d514144220701c19500c94400004080015074500101c19450710400805e0309606001c44040c042d0707840940094403802c000c1c0480030b4001c810302c00743c5032414025070f8107000780c0d00c5038141528855610303003101e03810034000100400c0080700081c00c140900d0703900d51304000350400c8001d44021503101500040015070300c17040801408000403090744050182a2801789850a03c1c1e542c1450810440956502c4078120303001c00080c406210a141c4a500490000e440280c10792542d101d0b55224110180d080c0d21140b8047d00c3c6101d0400c8040703101d03c0d6019000c01d0b1750341008407640b17035510019007960081c1b0304581c002c05c20b1082c403190700d0700c8455030103001070041c01c0c1142d0712000d50405142c403440c00e4550740d034080308142d441042000000c0d0b00a450059a4178107a01c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 144630566 1250 144629316 144629327
    0x5090d15110c0a06020d0902060d020304020901050906030c040b03160f181517030d09030203090a08070503030904050a0b040501030f0b090606010f050d090804090e01050108190803040302190b07 85
    0x55200d2240482806904a0302c074000c607a40d903500f6849240180ea940c120071075180240303807144000e5040500070600d2041104142d0096018034005c40b40700307003242e9841003000010101125415050340041908059904144c5c1007512000304c02810340e20184c2419032403208000e02035000d211113200c15101001000154441c1d22241c54865006001c05c0c2aa4491a001c45000380f2800e00e030f0382e207410407201528034284240c800d0606600c0f4184101e60141c24020341d41e4110b40d4000c0e124011a18001031f05003000240034040351409405103082800f11810000180b000416088500351110b103095100d641d5407288601a600c101c5411000c60104d0403c0c07600004002c01400c6542d11450601901d6038000140345c001c640c451809036540d03070310702d00c1a034041c144000c002460002d0124011402a541e50400e00761100d807500208807a0380e0300c0308425a5240b0101a9004841849020310045907006c0300541d0b1160203801105c4840204200080c956503488005451105100003403080c51681700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 144631816 1250 144630566 144630581
    0x2040f020a11010b060702090c070b0f06090a0603030f12021902010509060c07020d0b0603160603020901120b061602120a0f0209060f010801090f0e0a3905040c05090d15 74
    0x10b0002c01c444280c020101d00c252040c0d01019115a80c80000030740c102d050202159030b80e9034000c0400b42903050200e412441400f041e50618484c200380c40000d0301060052194904407a0190b45401440c1142c04094038401d1041020000c1c0b40c0d02003040300c000158800081107180001e07070002603d071604400940c1440c07800f0b48400c3c01100100116000b5980b000c400c250b013560001c07240c01903074850400291800c2071a204429449680c25000510240c140d4003501c00440280c80d55004560840c040744101c8001c0360141364480d100348121a0504403d100681c00da074809440c00c04802e04038242d071454a800c0c41c030100c41d210f6030068002d0440c05c2000441e42c0081095949000006036440080c0504505000c0c0110490740d400302c1c002c0740c0380b0680003803482d0f5800c0c1040c1d95403a0342606002801609046500d041c1e81c0f51007014401c0f03a1613074045050b55a1800783d4030000c0d507003044200005462a2201d000400a05110905040d6105400c0c0701a46206140c030100b522141d25031142500c031034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 144633066 1250 144631816 144631847
    0xd0905190b0c0c0a08090103180308040309090213090203270c011b02030607080403030b0d15061508010902090105041a07020f03030f0d091e03020d110c06160f02040f020a 75
    0xa110f41e9403421000a40101010f038068512a00d50300c8050048005107000150182c82449402041d4241600311700f0090043d4026501c1004194441c0d08403826807185c110854075000344a20704014103602a400f4640142d15034540d03440c07001d58050b4000c1d60440011003529503400070003c4641d10f41e00041010000300c100c18003038500090342d0700080e466943c001c209106100052000508151083c1d120f001481d800034440c0401d540242094071000c582d020040e18418905100401e001686a00d91100b0308082ea9406803182e0a084a0030f0180d040601c4460600c03130140b1000c0798515070301011840945540980c152228003900400090490081d240b0b400780d0002c00104845400c0042140d55040400d1404120705503286021025000a40d44000410201c40c074564101a4040392821030f10516a40300640004102c03030158540300360090040e8010010400e0a852404a00d29490440d0294115141560140d000316050303404030701d0520310031a40020303510921b540010203082800c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 144634316 1250 144633066 144633091
    0x115180509070507030e040204060e01021204150c0501020d1109100c0c050618060301080109120f02101109030d030204090c02030f0f03060604080d360b0d0905190b 72
    0x40c110204001040103070500d400c2150010f154001e140c000e40c501014003001600442d0760310f6640744020b2040070320710b00450050084600754003072190000d0669003a00e142c11000218003035515000c2c3c0d80381e02008411a2655024011040c180d506842108a003090742500e0396956452502004030b8900c0203000b40050000b00040800403031030303400000c0281d41050303450300e07595108ca03520055050042d410555100c1c00000011800f80010340144c1e1007144070b44410390400220305015211640014229001a4030000e03502c6007203182904001014440003004914001c01040401d0808180103400d00100350000350800c081c00d118490130780c61100714406035084c00e1046004980701d11036a1012400c2d00c0c004000725a4a648410071580104017603c1100e400001409025240b10103041a80780950b5100c0160440d104e041081c0b0a599640c182420150500b00095030320300350842880c0d405440d0707560b4880c00c00540e041100861f615910610b4480214051030f019410b4080100a400c01a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 144635566 1250 144634316 144634319
    0xa05070e13030e01080603070e090d14070b070302092704030206010801060f03110604230306010608040201050a08070e10030609061202030a0f030314150102100216020910080105011518 81
    0x26401403d44020440910f0103040c1512032000207458426580c00003803440340c0e0b01040c401242030000f000e00150781c80340c90342d5032042d000e0f4401002c070780101200a03105603000e100095583e0301c2540200b2080d28010003001c01b16080451071010407103600740f614910320341e2206000605404104080c01004400000e0000d207040035010f40c4e08940e42d120003485242d5951400c1c3c403e9482d801590302134400c3d108070501404441d140424807600030400d060080c000e10002240f90f0380301d501b2141c42a40c06856844c60301034940c4085481000061005040002e040e0b5008001c1d0f9170103030000101e2950f0394001c100d481c01c000c120300072108654440c6000030f90320321510006071000b04076032451a030040c00502078240346080950107000107030500840640300d41c041111461080a042d03030041005c2c0c0c00c640b03205ca00408018207e210b00710901c481109466115001450100803ea038807a40160052840caa641d2980d81d003529001c1e0003007441d0b80b0303404c1e61411005034020010002e0302a640441c03040d0300d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 144636816 1250 144635566 144635573
    0xc0618051b1809010204080f0601061704020a030803060a0306180302010f0e0a030c110a0b04030605100e01090207080c0105040f05060c19140c070e060411030405030322050a05070e13 80
    0xb11000007542034040d003100001201410300b036054800400348181a070b03407460440e607a99600d41c102401001c000c00c4820003a206284001560684215406000605180c1c299107400440d50030040401d42d02843c40344001c40001d10902684a044103882d0b05c44505c09502c0c6030280c25242c01c52002c0d17003054038241c000d08101d0400a58000c0054160401404e409064100900241240c0d0025500600a04400a02c0304140e0b00200100e90044804001c1505c41e84406c6900e152103124400c5203004100051014040a50041c1029031007251403602c2c0152031156035007902c00c00c0320141da501241601184c1031040502c911548950300e8090345251008a0a40500b11104d201404d41045442c5510782a07003d00c020458601d90207010884180554511300e1141020080320542d00071801c0c01e0b40c0008034082074040d60302442e0b1110103181035940e1114100c00f9044103810703601008021190784404a002800f900ac5000c0c05031002e006070609284481e0008903011344404420120802e1a0012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 144638066 1250 144636816 144636829
    0x10b0a0821030f1609150513080313090f020405180105090c07030815010924110c01050403060216151a06090303120702240105100903080301030807030c0618051b 71
    0x8aa621118844c8900316600308a900d5910350f0031001311041d01c640313036085041c2c06c40d02520540c00c004054030046904d0300c1600d602c81c041e0320010216040040405d0014034003982090044900a0b00c0c0182080d40d5540000c40343c044d003910189640103000014062810500081603101402c524010310303181311940d005082c0040200b14107807032000100300a2280c0e10945800000f48045540310810980302e01c42242185101d0b0111000b2036040642a401078401262088842e4016101c0f00c1c145490341d00c80c1c41c0032750f0026100c1200c1c10021400c2000080480700144100c1c0e040107400140c0404001c543d071030f21042d5240d040d02c105814829020b0a130f5000080712070800100581c88129220303080140d1400701c1e08072510b44c0c1000902c108200f0020300f9075400d030403144100c407818515a424881690903500c45d00024001c88002c10040c002b00d90110010001c0900c2031405542c600a20b172200421508a000790b410781001159000d02800750810169542e5208807100c1200070001400080c0c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 144639316 1250 144638066 144638071
    0x411060f0f0315041a030d030e0304090218040608030a12140109180503161a040201050a270e01080615060301050f030312151801080c010c05010b0a0821030f 69
    0x141c1c18400800200902030014051055202c090800d100700703100c1e1820b00d1a140b1100e12454004e1048841a07125940700380102521106040040c52500e42403d082001a60204100c43c1c5030906051030203070329848510401009080420196442d01103c403001425111020700c800030071424002008103a2240e825614116003004400290007084040c4110a5490030358015205010114a402000c0c0410704030019441c030495901c02c82d0035503000c00b120410001d4902074001141030194000e107a010f400080861221025000712840181c0c00c1946112569000071080060b044010020511704110700e50f0400c015070596a407802d941000f240d00e501051148a1080812034041c0520b910280212810409091180d03010352829000140c0040400300c5064002d9840075a02ea64600910078154140c0312030a01905242d9050b50044a88002195060710309542e1107034414919500d4803191802400920090301c4001c80100070b103284030021925024070103008204028550150704000c95 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 144640566 1250 144639316 144639337
    0x30f0105061e0d0b010b04050307090e030a0309170c2107020d030e13140601090b130302041a03010203160212040e0121020d08030108010f14180f0706080411060f 71
    0x91181102e14002240c030b1841000c05800d01144200103d8000c0c088001041500c2059003203855190b642c00320001201c024208a003442d41060024151a80c400d8000c21046801512039519008039200280035a6100c0070440180d0b60000841c00301103801068821200714019400324140f480503004030b070045104140080070032000c002100d00542d03d0700140c0710a002000010856041d000601c2901d490f0103440c0380d408241d541c031b0300084650300e405c03c54007808421a042031405207140d01703000190440074144c4d0084048400751002c25202480554841c008100c0900c400c0040f12002a0910381d00c11299031400c80200000e115880301400c0d00c034110b807405500d45100ba480301c420200d41c1911018020751083c00c03180713038405000546002c1e6058440240081002c000c1d5111640221024140882e00c00c074580400070780729042100b01d03500e440b02c003082610b0a0402c00c0b00304078145021a00980d000c2a155070070311040c490a80303400c201c0e060007507400e10720340103031b2131080c03074085c0507144411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 144641816 1250 144640566 144640609
    0x608070f11100c02010b120105011208070c031a100501081006050c0307060c0807032304060234110d03080621120301060e03010b01090510111209030f010506 69
    0x3011003100800c07490315440140003040200f0079103084001e01070000410854800c00c01c15001605c02c8a040c8525812203943d619002054440303551202c40d1a0813801013036844c0351540c00000b002c01c04076090b415403080068000d2840d8a007112400c80c0440203a081941003003100000c002c0024409801e07901514510308060303882e03083c03074000c041c07840c4121785c170081504d4100307103213040c10076000317401c6500440040d01e09000003200d4020105902d06c1c1000c9115003102c041c001304010501a42c0200030043c0b5003040c558100c15a0390101e0882031814403105003138030f144002c10041c46800d04102c04885021100c4c00d0702ca040d1504c0040280102412240c0308400b0390509058150b501580319a220051006459070402c030b000441c0c4081e0030034850480419404044070074145810f04c146280014141c40d5184c8841c03c00d4140919050b4980391303d01480300c213400184034200c04018060418003d0902e03250f0700c10825060504041c0311006859042e8108428080310341e0340d0700b10100d01a02c015441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 144643066 1250 144641816 144641837
    0x110915150d0608071706250c05031611010e0f2b0f03090f09150303050a0c080f180a03050a03081e0a05040512040e0609040f020918070608070f 63
    0x1c0020103440e8062402849651000200c20ba0307851040c44042e030448060314200ea03900401c3c40070844c460b2940300780040c012001070a08500580954a03914051703400c80b0704211010614402d0810a0101542c5a0064180200d81c1e5030340141501001002660030030300455007200410b844642c1e800030703c102d8074001004030074420f142e160a41c0d9016000708000c0b4001c40faa060103013103003909000d10318580c10320101c00f04101c81580141503810014106000d00c2c0c0d85551070858158100010314010001c011400e600410018006090b01c1c9030801c45881d81e0715000c41000c010701840204241c0200040041000854404943c00c041c4ca03030142490542070780c402c0c0d5501c003000c0700c0b49a5241c4100741d0742d0034404441c00c0d03607002a104d40c4c03013181180e4410700c1080144040d4000c2c0e102c0c844560401000194241c2400700a40350031a02c60070103642e04807031950014040401c110b0b07800c0682002481f1a071400203080010300020a4241404215402c0c9107600505000c2040c0040d818403003203005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 144644316 1250 144643066 144643087
    0x819051603230f06100306060e0609041202070f080705090718120f08070b09151b070c03020405041b05040c120e0708070b12150108011205160311091515 67
    0x240c1d0b0fa100328460309483d96403622200b640b00020b80760009544540c0740620204140d00b4903594240650801030401c265691903170b90300400344240030321071400c40c000c000300007400c20260151000500082c001404103181080140308200c0001003c01c42000400105c04101404a00181e8143c3c0c11002c0c81504410603070030454040490410b000780074110003d02041485503262010f8024585401907500e0b03603401c800f8010400505860f000150148078001c1c0d42000d152000604820b03104010a600e8203907a60001130440e0400c56080d03618007100004604d2010940e920000a00350031201045101c03080c81c0e0041c13007060352070700c0b5052041d91540c40c00020101042a640104000422a260340b40c072500481c01e607400003200c004034000d00c01c02007a000d000702c1a081a4010341a950144180c0c83c02224501d03c441041303040e02c0500581150720017011000a043c1e01550182e03503160f9000d562002484118a0014424044004500a04c00d076583d030710700031284621104040c0310380320220b981 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 144645566 1250 144644316 144644323
    0x70c02091e010b040905090604020f010c02130608030c160e0a0b0d05010c02030903120711011404080303011e08010c0c080d0f060e06010801050306280204081905160323 74
    0x80c0701c2401d58990000015800c481c050040c030540749180c1c028011501c03260724480c2e484130f05640080d4407600400c54240306510841d140c405050001705036940300080c40580130200c40041d0440e06a540001581c010901070800002000001c2030500c43c8185150440452096002500f100510303500c82000381c40594400c001008030032b8001d8001c10542841c0340001c0d58aa1010300418042c3c0103c00320b000d00c1d1940300d000d03602900c0e00240c0c484a10901c1c0401198251408001a241e1b410300b44404600b1a108101540c00707800b04c6400c8141004802064403141d43c40385d0b00c0010f641e810018800382d210340c0610b0350780340507501822050301c50088094010142400c4c5c43c03900ea0052400200249250444080900a41c02a00d4651085c0d0300da00074180c982004549401c0b010001d00000458980d03601006001145805030060403c3e8803141103900388048001004921000391034000103101d018003508911030304040f401100c0b2441c566a02c4e0008440c000003c612101c083c15100b440107007031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 144646816 1250 144645566 144645601
    0xc0a031a06120d030903080109151203031d01050702072301030b0604210b0a06060203070b040204061502030703020d05130b0d0908040f0e01080703030e04050a060f08012003070c0209 80
    0x900c2592101c101d0503c008005004400042d400600c031100000b4800b1050b04c1100d0442c20403006844240d410500030441252441c101102010b5562496041c1c4940d0f178802c2c03d201e86064000442c450500c80c0c030091900c51503030008400812002c0b4000d010f02c11002c2500540202800d022440011b468006560750245a01115150b01640010031548280e010302e0032034940300d000c4107000ca407075288a00c804c4840314083c00015a008110340d201140c10700007590f078414402000860311582381d8404404000b5141286000350740041901c0f0b042540500103058584000d10b85035051219201008991607040d00c190740006400051400b054091504a958001e40020071203681b641c1c2c40c803002d000c100d06842485050b01c03c0100124110780d0111b00319045075015940c000c101d03043c0320100001480043e11346681150350311000680d100111400748010100a40001449992880404a44c00e24004061903440c2c040082092994205d0003465907503405031407070040387d0340f00c600094990011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 144648066 1250 144646816 144646849
    0xf11010203100602190f230111070308090604020901050d05010f020318071502060c0c0f0708060703060503150f070908011b0905061e0f0904050a060303020c0a031a06 73
    0x401c01c1080c030b102c2015141210026822245180103011100c001441e10f4040200003650005116010400440d000301d40c00b0309000d0b0700819900010f511a0855080d0341800754810400718041c024103400080a80e4011100409003080745030541c00650b030708105004d103510660110025805204c001d502604501581d26400c40d520f042001403001d28070030041d502d0a2034454402d01182c05c01809440b40c03011011600103107036a44070301c0c030300103855000021949098420791303500440c1e1035801c10040c00288280e101625060800c240000e098a403241c00103802a031110a294101038440c8441951010121003201aa5100c00c002101c2401046d402140c03558200120800817080f52108101903030116120121a59038440502c1840e009015400381c201d03014107401244550f101005145004401912516050485000508036202510310283c0a9510383c02403042640400c501e54038010111a410ba1051030f541c2c42c6c00000c440d10a6290550544602003241919103842e800142100c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 144649316 1250 144648066 144648071
    0x705160204020d060f051005030c090d0b070f09230904020a1d06010201050f0c07020d0303060503120306030c0405010305061603060e01061701050402041505030921070c0503010506100f1101 83
    0x1142e0442c030150042c0e010304000d01e105c440300021a442c2131003c9620310130311501c07414116541c8550151164221390f8a881c0c0002103c0c1c410000542aa284039225600c1a1514241c0300d0400704001c00c031148039005031950300c0724001512001c18a01845000c4854201d401c800f0aa81d64404904003100341d50000307005001d80503092404460f8803280720301c2002c003a802041103a480010364802402c1c26120040a100104001805810005000c1600030f000c1c2c00c01061503603561011901c0c1c0540e4180504141e003010051103042d1070240031440300f41504942c140543d50540e155a0740380d140140030407400c02c1d010b045c20100b0602a400420003080c05020601c2f883d030b0b484901400f002058020190a03140303e1002180c2c52601b40b081e24140c5000c226641c0e001d1088030000e40e219440508105040e102c0c281c22004007500703091110040325034191b8010b8580c01d640c1343c005007110340c45c7c0156200f641000108000e64a41d10008070820085140c00da07500f80b00301505036141080314504507980e50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 144650566 1250 144649316 144649327
    0x90a12081603020609010c020c0904030804050a1b061b0206030c0c070b07061b03050903030615090301180506090106060507020f04140412110f0d080c0f04030b04111206070516020402 80
    0x40e00130a005210b1400c00000b40040c1108280c100d84440c02e007a240c1d0303440400100400d001ca0300c15907855500900c5002210701e01451074482c00c041c0031380050b1000003200c4010082c0050f60f0301080310000c0f600d0400000384958090350000e80d050100a000d844408004100c25191070310400201d40140191811260355041504014019000a0040209584a43c08480a442e01c20710400d440f404800740918207680703841007004201e80030011416a006020701170081156800e00c9080e0300c0740c05060454035a01500c0c0381c038a041c010002d08014040e450900b003000819041411681040d604030f03900001401b1000c0050f00a0041d043c1840c5009011400c0008100707095004040c045c3e2507032244800c481d0440300390380d6105e8030003ea28000d504244003650416001e400d007590008403070102c0134240042e260860041d90410b501c03c1d640341901d98244818001076141c10070b408001a100b01c0040c0036003100d81ca5440c400503001c50104100041c864280c17200c03519160325020b5008005560701e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 144651816 1250 144650566 144650573
    0x30f03030f19021815030708010510090e01180608030c1c0c060c030e06010801060b16020d050a050a0c050604050102150a0618140a0c08160c020405040b150402090a120816 75
    0x101610080a024048241d170a0580341c03210002c0d288106410307512006180c2c240400d01c42101c010442110910807035410109100d0b01300c900e40b03800307402402003085489414040090945180d80e1110b003103a001008044400d01000c69118100781c15100f920820101e092012184c0a841d41d401514003841c1214200391503034540c10440503541840116200c0d40d0f01c03074603100d00702d030000d208a40076031108020044941e0284000808601c2c0020320a4000365003540fa164103001c095401100c00390407a40900040040702e4045030f018100076240603003010b050000103565198008101407007128600e0003d00c61030640d41080000d071084541c210a085c07410240d0001800710b01990504842c0e20200251200d20035104451904800e035456900342d48039006552040c0803000642e0040001c0004064003503280c40c0a0180103038481c10f000c801514003444000110401c48203141d201d1801041140c2c030917a0350006081c240c8600d030b10400090a21403800070418401c0000303d940c110200015031052 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 144653066 1250 144651816 144651847
    0xa0809180702010504050d0f0509150f040e31020402070c170102120f04030e0d03120504030c020f09010b180f130e0709050c0406050703200601060905030f03030f1902 73
    0x3d80d10400890701f414000780015a890150100000300080e024030080380c0d1403403c00407200c181d01000185614000107a01c1420881d8000d0b00300402076107107002400122002034401241129005802d00340d00c0f0780e459810b00308014110800380c0705a401151100c203202c44000c02e00000c00b41007500a0445200c40c9449003c2e400908000840040d101c0c0019541445002214426541580c550040840c81400c00a80005c59402602003000111115102920031b00c01d250249020b41c43d20620842d86104015140d00c421500a0059130b038a4010001c0061203c255000c07407542c030f00c84880728407030480803a040c0c1d1103540707442e98465038840e003215160701e1070b6100f000400000c400f9035422903282c00920341568400c0d1001004010b040104005e0180315030040d00e000c520038030345002071124020301010504004902c0b03005580000004011040d0081d0010300106403d9015080c1c070085030541c5622808024100640454404009185030502c2c0c052090904442c080c21511240202e414100703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 144654316 1250 144653066 144653071
    0x609060201150b09040c140a030f0e0d0806060901022806060e132004091a160e091005100306060e0a03051b0a0504020d050412110a08091807020105 65
    0x155207400703070040800080700b20503020784103265541450301c900141400300131710015a030b1004000e690252042c8045408000346401c50482c0c0e4041060800002a5811a802c031034402c0d515a0014000c020f2981d00008003d50000041302c2c0d8030b45504850340141d0401012601c0340d90384485d140e0a140c50f504004103288940740c0076960420809466101e01d0040c0030043e40c0d60042c00c1c4101129000080840c00c1d0f10305484150f04650003495501c402140641c0d030418030403680810340e1550410003031a00903216510074424400406016a280d49c00351041441003a01e5004d089168005400440b08c0c5d03030a08010b1901900405000d40f10810040c02804180039102c0000e200e00701c031000604d06501c0044c142c9801001903c2c0d440101d100808458a038600c03610703000842107070001011742d1075102820b0301f83c0030400040388910345403501c812308810120540d01440520314600303a0000c40001d019043c2507000109981d0b0b95145c20018046100e01d0f00520280944101044202c9a040d0001030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 144655566 1250 144654316 144654329
    0x204080312090c03010e1903090509040f02190605070f2303041703040605030a0b040902100f0e0603040804050904030201020d021306080a1422020307060201091e0c050607050c09010609 81
    0x1c03801410f4008050a80d407401c141c22400c0c0c0d0043c00b412100381c1c0701890f4031003118400d04180003015a2100800c001003070446040e80c0c400c403041090001e50400c520b80e0007020910640c08103030103082242c09807040c001c0d101d0261000300080d00c000d080044ca064550300008c0070b40c044c80388a954000752240c3d2a403040c0151500241c2d0f20700c0780c8015005c0082910309880c5540c4840d819a901d83c01d20000800400d0101a805a229100880541c44d4400c9481d89298181d9500d0304e401c14280c0d02034140018903034101d0040508100700b00200305250103a60607034804540400c02074032242822400b901581c12400c2e91a807000480c1d4007100b420880c1d01003295590340720001d10341d0b902c0c0b0800040307584443c042c2010441c400c001458400341e480200e42008a6111011140303e070907008245481c0d1a60803100261390344107e43c1081c00031940c000418400b401b644107801d610242c2d95101307a083c40f4450503004e44008222901000000d008580500394060300702d90866a4401d40282000035910840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 144656816 1250 144655566 144655573
    0x80423100302040b0304141e0d090602070f0504020307050409051e01050103051e0c1605030904050903190507030e030a240213051003060b0d0b030106060e0306060d06020408031209 79
    0x148240d500a0090710212603a0078409411a03540e03450f10100c1456610042d4058014401400413500500380421003000d00040104440d03625880d0152000c1c0d00707908140150b603c500310402120410940140c25160f098030090703225168960700391168001ca030441ca484509103402c020791400400200f260044540301035000ea40d030b81b05e00642c110b400c00e44560b4a400c41103900403500580c0581b0a5811401e1001e8071881c040358049a03001819603203400f20f8440c1c10001c0d6101c51403030a40100341d00100b0010155240030840342080240b41c0e500e51100e01805004108841854000c242d20069600040c0c1518100c807110701c0c2c0010460005c02100740310560341009040380c2c5c1e00c1351003a40c0e0b41e182c400035600b129504000401100105040c034640415440710004206051a000a051030064508012651110b084201825203040b500000100003181c811050140d40000d0544e803c02410703030b048403501c1280d0803c2c42c06486071390441034244c88001111b4000f503030300c82e40307640c810140c1d801603 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 144658066 1250 144656816 144656839
    0xf0309050117061909180b06031c0305090c12010e060f06031b0f0303040312080c0307051602030f0d0504060e0a060503010308130302030a0f05150c0301060c080423 72
    0x1035a12910014101185560b40c50000b101c60078110001040d034842075041000c0c5660321811030b410341d83d0010a4a00c0034401070344c010100404181259004113085000c0d102c22a00319400604d580070314101e080406440b40c004ca00a600140200c083c00000944200540c0414040441c060b00c0b12051b25007581c41090006001c0050458225000b420010301030148129800003007100451600c402c9984a00e2545c084000b5075800c0009000552140c00d011032450b1188034080c101d048020046003c00704200b0810800d030740c0c00000c0b50728480300c14800c2c1c0d8000200f40003007898540b0300e03401403082e44074079480801041e40140c0540b048402e9507803101107100c004014403030804814814180030480c24001440011814070280c0003452150b040380c000c03e9030340e800203450a0484081681d021018142050031301200380418003000e14080c100c01e803542460602503ea61005101e030b0320402c440c0552003c200080761b000c4400904140403021082c01c210045220007008190800380302c0d003110301c003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 144659316 1250 144658066 144658069
    0xa0608060c2203080d1e020c0604020306070e03150c0c0115050a090908030105010c02010507060612060c02060601080736060f08010e0109020304020a0803270f060304060f180f030905 80
    0x1c000542e54884190f5042218417030154015080000c08074880d200600045144440c080c4080d0074000850b40051000c1d007454018142084005441c0c07604004081480721403c0d20002905c409003a21040300c5002c1e5694170080715104c1c014900c080610b9400c1ca964104903108052560342501c0301118001080d681c5c40000c42c04980c040200140b8840060004000035805940104082801070420510b4210703996038160481d04c2c43d41040c241c12200034038100910a80b4400d000300d107100e50000f031107942400700020342002c40044c0384104002500d80084101040082da0050b18400c905c0d140c030901c5040e00017503400301c600f801440b000692503e030101481c0e2168050904960b111080904580d0804100b2800395000a0050360404844d0340e0006e0030312030400c005c12010425805800c0c042107542d4101d420141198456803040020400c0c0b005180d40c3c040490b030f00141c3c050710004034800d0819480c1c018007006615070308001c81224181090200b100022941e046c4660368141c0d100d41c8400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 144660566 1250 144659316 144659377
    0x2d150a030203060a110f0706050103050c04020f0d050c1605010608061303200705060a051206040209010f1d03010603050607080109110a0f030605060d0218040e0309090a0608060c 78
    0x4006540340c2d10a1001c5108885190f000046500248003061b20f0400582c02d0f100340d81d44403160440710349a89800400c2400300038010704110308402c48047d46424440517210348107004010540000e590366001185122503000d045602111500c8032018400042e410018020032841c424010700d40540000511031008080c03c03d04040d0f81a00e6041d4821409814400584001c0c01a9101c620840ca4003040c10b6a0720005050314600c140e0f11241d5582002c1d100d100c403a04054121030041d801806202c01c2a0b81002d0002282182441e14010480c0c8000d04000c04080703c03001e0503019403902501100f48280070038030b644100d00741d4550070b42c90390761000058200c601c4c11040d500301c5031060084003011445a49100d601c6e284d1441c0100d451303134454000035019401403581e400b01a600203691300310740c1d41034000c1c600400300448040242c0c443c500406031300d9218907070142d80304401000020382c105120f41e12140143c4418800c4890302d00e4100c91151085c0e00c10240c8814540c1c2d5261812401004107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 144661816 1250 144660566 144660569
    0x140a0918050c1203070314040302091005100f021b06040302040501030602070317070c020d140708030a0f0801081203060d060c0201020901031413060e0f0a15060503070f0e2d150a 78
    0x190b00445c81c00859807800c403a040c1d10301c44031714902001000b0000240e9070700106140540d040392901c0e03072103d03d0a420002c0d1020650780280910204a1083c181d654021030074400103102e0050f445041c03008003001410500c100d1b080250320610b001c001000344209580580490791098a4400140c00740da20071100b809030072140c1d80b000400801c018401803d10303501c0006003501c58944044450743c071000700b604281054101c100a42d0021602c04080d41e848802081c5a00e06810f01c1c50030795050074a801d0716203000f0100c034103000c4000800319880e030301d0303400d82d110b4010340040c410060300b187e40c800240030f035100a00540c006814815880c0348174007150341d1140140056481c9500c4d010301a901d0710003034000c0c48800c11850013001036403a5601400c1c23202801080c030400085220502c400c113200304803005500b042e03009038000f540a1110f00c0b0410301100948842010aa00310360b40d070740d100b480741440403410613012a0000550101d4400107408a400b41920204000d25400ea032004d000342404035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 144663066 1250 144661816 144661849
    0x812060d05030427020304110a050d080d0c05120702030304030905060a0e01080903041706010e0a02041a090609060a0309141b01110a0803071d010c0c140a0918050c 72
    0xc010800242c50128004c2e80046081100c4480a050303814001c0201c0c2c00440e1b0603595690003c41054940c905024403802404003250022400400380c0c5a1032182c0c081c40c20740907902a44c514115210502407000e590074210351220b510040e107000b1000039260f41098030100d01140541c400400c282c60018141ca008040d0755441400c111007060045800c5403001e0300340c1500e800108008108207003480b005500750300000e401004039516001a603004030304011704414103a0300c1408203000c1f00811410b0041c2d0300c1d00e004600c41c0c594081c500000c40c10300c03c000125503c50070000f14421042d8040c0c2000004074094406628050880d00c800f5031600c22079070a4040c4002000902881903000d200114554254103003141c001c1c61203562a900181d0088c1c902101091101c0703e464907030f56880c1c81c084d840c01c000b861300030060102c56555894540c60742c000c16a0001c0542620441c9884400401d00149011740c001c0c031071121015031f41528801020025905406070b20102109401c101d4403000a2102 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 144664316 1250 144663066 144663073
    0x603030412030305060d05010608030a020f06070f050c010213060c060e0a17131527030c0b1c1a040b150405040e0708010f020306011d0904031b0c030812060d05 70
    0x41ca50b800310014400103144aa10041d20000d02c808210248a5980500100d6005682d2078190341c03c0a85030510b01414100d20f50301280403c80800c0d4000501d011440c01c40c2001912501c82441f841c0c0640613090740d020001d0001d000004516910051105034940640410054514403803c074a0711190119405060405507880c80640580d8000c0103150203005002907060103034032403148072241d03529128201e001070002a8140100b010070a22201c0003a84059940b84142c6140e0340c81d07002000c90710501410400114090003101c601180583e071070600c0d0b0404202c41142000c40c041994204070f480c500552800200740c08a05081200003071903000f561800d070415291408000103080d40f030102090342d00902c2c40014214200740106c4401d451446005030308e81c43e01c4000103100c050000f4000d0380610320341e2020030190b154024141d4210b0b1301440c1a252240502c443c008002c1424000140303004031400e00001400100c00c0640101c3d003079192000301c903480d0f0701c003080142162446c003c0e04940 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 144665566 1250 144664316 144664349
    0xf011a01180e090106030503040b0a0e03030a020604080702010306030506130302010606020f07050d0501090f06020711010e0f19120803100b1e03071206030b06121f0e0a020301090c0602010506030304 87
    0x4010000143c2d01c02d44460011400c2600c17580d0b6141950002da01025804201050070014190456a440344010f0140e006605002034414001d40d20300c2e01034409400d00c1400900c850941e41311b03412500c05140c00034112526401d2181110b103882d01072803019001540313091408541a0300c0820000e84194441004180040c00d100c1007111909010700120384541d40c2d60000e600140682080420b401d000f00130040e02da58150034204151181d20013142e0400940c0844c0880a560700394070400e0083c4165850540e4102805c803001e69031035640c00c1100b80f0746011300440104444080254440c660340d1008440b1aa03071080741112901035003880740280200001d903103245020030030156a000903035260005003031005c0c84201007102c8964205036030200301e200030040305040144103048442c0e5014005d155114604000051090560070604413040d102c08611420010800c43c169105030024000c1140c84058034040c44000843d01c01c1c0700140d424000020854a000b04c10703030741186c080c0e8200301b0300340c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 144666816 1250 144665566 144665579
    0x5040e1c020f0a0233071109010b03042a120201020c032409010f050c04030b060f01080a0207080423010917060403050a031517070509041505180f011a0118 68
    0x182c401180d070681e281e00c09007400c504d40c801e00170840309040000207840e6030740c6030030b051560180d0845449140514903c0c401081541041403c17282c2c003035006030500e180000000c90700b0108007401d2028030b01644412401085c7c07501e1031a80c00808074802d800b224590402c440901d503c030400c840a100e800f036484030000003a040004030865124640000004d0f40000d01204102101d1090b90100344c00701c4045014403c0002d503031481c50f0802c0044134502c440c03091103030008110a8000301000c07182600070a2010800c1800410344003d4039404840c00b106c8101c84001c2c520680b0b108140d0b6000882c90800055000d40011460840d0131082015104955030340d01c080d07600358820200035040681d0307840701d06041a1014400305c05008601008552400b0700f542c1246401a1600031502c2125000c0500c4001804000100e0010b405a14045450b5440c000da000130b0742c2901c1408102801107250f60310344941c041d0712404103e00b080000b0521400c07008011280264103503141103400084507814020b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 144668066 1250 144666816 144666829
    0x4030204020c03190206040b01170d0e010e0312030604050c0403050d05031b07060507140a1706010c1e0201090e07050703030902030705030102070507051507030507060203060a05040e1c020f0a02 85
    0x140c502460882c0d10303014005044d038155401d41c198900c01a0000c8042c4410002a940043d0040c0740680c0e61400440b800804961030b0500000000c0520500c54504646a400b524880c1c20261005040e9040c05c0d810401c0d6a03001e510403504a84a00c1c0740000294441c0050310955060b250028014238803000c4000307043e1419800070340500c00510600c2400301080d0110310091203401c1c82050041800d06102d05c0140c8903039504c90780e0400251081c00a04541d0b94442102007107980300a020010036129000181c5100d0352004025001034007426100c0c000e8030305410b02c0946a40300380d90b0780c2c20ba0313550340a0070720060300300303485202c0011000c022240110740b003074001d1414030340000c0503501003680c0d4100117401c980c0001402c9a807a000500700f00158070f440140039900360200381071a80740203e195002400c07882502d00003840f05030301001040d440d0b00c40805141c05084064402c0121110b583d1049907504011441100c0b0091074601481c0e415201140c083e034824025001440e003a083c03035081001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 144669316 1250 144668066 144668077
    0x8070812070b0604020403021002010b0a0f1a071103061f05060f0d0903020f1b04061a0415030605030a03170601030b0a05060c031207082d1303020309030d0801090e0c060403020402 79
    0xd019409100100243c0c9e600c1e0a006460981b03038000280d18000e480500480e07480c036900030001100f0002040042d14052405041c00a0285803010354445441c07410300142c41c48408019003510442003004009620f00f9218180280c00f800581811a034410410805110702a1030305c40740207042c02030424000071030f00641c2112f480f0b070056030713181c0048410700c1d4039100d402040d501c0e413051030086024807424144a0700c0060151800041603a0700c11b42080a210310885c852241260420f175840207110740f00c2d41c02000941402000e54402c0342035800c00628030740740c45400f1021480d40c0c1000c82e00c1907010f032203100545034015101000b6685004204800c94000b81c41c03442c40ca0004200c11095031a51a40003889401c442d20744110b641040c0c070403e0a000c6080300004201e880c0b90342c00244800c0b11180c01a4400001c0d19010000c400c1494120704501401e0489a0144144501030040e15040603101b81078602c00001002540ba00310744440d940c030354213240c10390400c40410091015080c65002043c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 144670566 1250 144669316 144669319
    0x3090a15120f0e10150806060d14120a050d0b01230d0204050402040e100b03070203030f04080f0a080105040e010603080708090103020f1c14010e1602011d060108070812070b06 77
    0x4500265409140c2044c1d010aa11034044e6920055018903c4940c2c4600001c2c00c21007005015915145020610214240fa0098030f056054030b034185550b0303420840c42603030800190360039440b10015000640340d908101e420300e01440c2029200074240d40701c0c1040905d100b821081c4034040f05003a507041c00069000700c1d0a82c4c080c0c2e17020080030031035403218002400100f05010803040c80340352607100300e0752448864100065500c2d0810511805079400401e0700c2d00401c03040c0b406801307030f02c840c80d12404603c1561101ca4490790b010800140850700004424100c52090300e00b4007040402950749400c8030200d0000406500060128001140f000f001410070018103050061030040003040380340c1690820440300b908215410008482e40049000c0c5010710070111003643d609506100c1c800319103001c0100035003e0042c4c41c0d4001030340035100350800c61074510801507807030383c0600c1110303129240c04090058000f10710511000040f41c10340000d900035000484100320b800e015495540501404003e028113 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 144671816 1250 144670566 144670571
    0x6022b0c02091f170601080c150307200309030607140a0e2106090c010c020d1e021f020c0a0f1820071b060912021c030203090a15120f 59
    0x74503a03003404203942d80150401e685105070760107019001d03170319202058010311060341043d100100c0d507480d2610f1084003419a0350040c0d4490b070300e0440c11180f18440d000a580c1c900c00e03a0030b16500a60000c40180b050715416000e4500035070351610107889144203000e9480e41c0c00c40030444840402c3c81601240b5030164010b01c0600d600e030b00c1d003020701925031910b240140b05400c0141400043d5200b000044020314003801c1944c1c7c0d00c40540c00185400c0e02e040340c0508101c07200809684180003040481044680c014403500d00f4103035016881091000103490b02004d131141a142c0e20705443c01c1c100040c1180c05aa4a421700f09040c040403800034085480045502500da0004144004c800c50000c0c20040140c2041c54480d100c900b41802c1c65003901840038005400500140041c40d0f004d03170b6010903500301c0040540005c90384d102141105401c2c1c030346400c200c00080c08034400c055003c4020403e140b8201c3e03841e1740d00da840e0070342e07500007012003200c2802103001d00e00307100500e00b200c3e0000304008903900c800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 144673066 1250 144671816 144671851
    0x130902041b03060f060804120323041110030e0304141c03030c080c0a090905060a080307060603050d050a0c03230d050604110703090302131506022b0c0209 68
    0x181416048503100002c030f51600010302c01da0000c0d503c050010056072402922504164886c50341d590000070149003055100c04001820f03800d030009081e0b0040f1205000c0c52546094104484000c3c20161024400c1c42444c0078180c0303043c880d006051a4483d0764010310320342443d0100a120b079200ca2426150860b048030400454206c0480c05062020b0082d00c1c04144404000320040401c00003d14408200754280b10704030340140d02810100c107507130380c2d448005041d85441000483c64031890784203120622002844408200c0141c000c44e0840c1d2181d002c0702d4000340d0198040d85c86003c0e1203d0540081c90319035040300886d11031040c0c0035030142c680c142200c0506144401000c84e90011084603440380d00d0700140121420544030308001e0a6046e01d006041103841e9400400004140c4000391061985d00043c910f03190642d8845080c0c041e50400700f01080380d5402d0083d40b81c256500540320340c4100005074805c3e686004d00310401280f00d983d0f5100d03420441c0d41c2080004003015011440c44030020b10b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 144674316 1250 144673066 144673091
    0xc090a0605060f0d0924140103030512071b060f0507050403200d02040501060c1b080c09190212041a04230f06010807030c1a070f031818150513090204 66
    0x800120b0740c6c80361022220151030380c00114003654050b4080303040d07090f100c10040001c039502c40b0070f69110047d90070f0354540e90b4907124001c503030480b021600b001e6220151000482084056440907454901c07000c02844240d4607198280c940303000741c2c400a451075103880d20302210461403242d050506100200408084d02a0340c0214040710340980144012914070f0310300030117109444500b401e008000c501110f103a0350400303003541c1e1100e50740b0603518003d9400fa4085a40c407108441c2c00309085c02a884110344425075a200041610002e41e410755285140440d50f80040c20400947c9200f56000384901d180900d421004449428000f01040250f014202d0400902e450900ca25030007000b0401c0100381450440c1000400b4408035449400d40559044400032800b00300000e0b100f00070380101071740e0403903401801c060340c1520084070101d0344614403480100d0603c255a0b1070087c003030313400d090810a544a1142c0d01c01e02a005008643c0d0042c2a5601c03a81719006075000540d02910107030001c21702b0418aa03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 144675566 1250 144674316 144674333
    0x702070905040809011b150c120f02031008011401060f03020c0f1b0102210903070321030b09040201120b060d0e0a060c0212120c16050c090a0605060f0d09 68
    0x320101d0798003a000500350340d107680c480710824030004200c12400e9948210354a0320701814031f1500c241140c40c0c40d0b18040380e00c940601d54a10f0a0116000203002c1c1d03206c5d4110081c002d61080b500c4404c140704d800000303c0d842d801403044041600000072124480c0e420404152800014030410303108050b000c001d80348010740184031107000508100b0050071501d5007401400403101d00c20412504541c000c9d0f00803100b0300056074040d0801404030700c60a03a124210b002180c20208507400142150440210b000403081c080d0300307905200b40441e43c1c1008010414001c1000d48642a100071b4005081034a1403034034401139502031400e00768002d1603c1d103054407103550601941d80407002c0c054030b40c102000701018002c2601440b080c0305014406480d10915118000c00036000c1d100c407020451140c6070001c0d801c0051502100e058541d0582c04801042040c9084e550300c403140c8001034020400c4201040152031140508425600014001030a10004518002294102d0140c0c02c3c01c0a4a4600c0f0350701045051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 144676816 1250 144675566 144675571
    0xf06080f0a0f0212010f06050f030a020f1306090e01060504030b06130b040f0b040e16030b09030d09080c120c1e070518010807080604030c020103050402010c120306090609050402030705090702070905 87
    0x5000c40400ca61409906c10b400e540164000c009000040041190140f00c02088a502122503000103840c5c4085c040454454014116138251200d034000c0040b45598006000504507000400110034603a00c40500306c904e4081c602c001400c50090402203420380c076260a000442c0881c00d00000340020703042d400103081d01c0200304800003d03a65007803d10180d05081c010626030804007401805c010131011200881007009101c00307400c1c40001c1e00801c1480350203200f1610700c50108a024441c2079a00d0420440355406466150014400c0c2a20602148010402d8030329074035028000d0039a940c004d040c0a2082907141c00c401d1001d0240c4840404d951f5200c030b9903841c440d5141c0600c40101d42c1005401c510700f202541085d0419441501000002988000101c0c601c035420710b40490140c40346e01c0181c0311940c00020003803016680910945416a140d80900d0840d0148803042c0890fa944030030700030440e002500c010750590003114042c86141003181200d0b4101100d807044640b11961000d450f001c5580a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 144678066 1250 144676816 144676837
    0x1e0e010c08030c280e06030703020708040e0f0a05060f01050904020403062a02010203090c0f031005040302060a060e010b0909071814010908011a040c0e060f040e010f06080f0a0f02 79
    0x8902049408201e80e003c0060420b81c19203040d03040c40c60100a0901c000603050340f4401d0030004000b888e424842d4054a42a5912200194496460700d4500c1c030940000c9400f01e0290b000000020340805990003143e010b000c002c0c1c1040400e00d10500110303402da1005903140d42060b02000000700140c1940f242c440404e541d85c0900c0c0341484240290814103d03050001403c41e030060003403029544c00820f071050307a000c04030f41d03003042e903414900401d051502c08802e1540c018544020403041c160045205486040e8a400412466403030f40030320543c4460a0149051108003482403603418107104208070b0b089175460410141c030941d581e480d22070300d0032250041c42465401c40c40840307055800c0b41c072440183c82c41000030f00c200f07040420381c0040c26070030040151142d9101d230060351800d4011820301c1e40f610800b40c40203a5841c0c4c0848032401a40c4140300d11180704041000004080007541440070903503c99541e102090384540e15198101c15019101100700c50b07540b400000e100481d427009240c401507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 144679316 1250 144678066 144678091
    0x10f1805010807020f06010311030c01050f0a0f030b030303070309030e0a120212010b031903180608040213020904020a260103080f0a091205011407050c0d03020706060e13050d1e0e010c0803 83
    0x1000d0504bc40c44150015042c404107004c21a1078048030f03001d03510001c82030320340220482000501100504540c422041d0140000401c0c040c0303850b81034000c0700c0b509002352a00042c0d0070340801440352210441c401d000f4800420008000103181c220801e4018141c560000f00c2c003562580e00180c2484003070804100c41c1d1111480000803d50000440d41600c903860209407251441d08001a140d2107005000a105400000041d803a40888d81c2c143d500520004d001151104201c140141003190071600261f07044419500c1c07030700d0101181000701d050b241d10401150501504042c0c0907043e40145a9143c20b10518000100340c1c018503a202c04900c42c06400082890f085045842000e180301500b064100305080002e00e000250015461406202600e80141d03641028100400204441c2c1c000e950b000341c12405004080002842200d1054042e90a84800c119815405c0d2030800c03e00d04130109480c0b030040d0100c01d0078024204500d0811041c103008101c503105a40311044c5910848400c011200d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 144680566 1250 144679316 144679343
    0x309061e07021504090f021207050c1005100906050906010203160c050301050c07060e070b1605070b0d0e070803031302091503011e0614150a2606010f1805010807020f060103 76
    0x18410b005460000134107500842c0303001040c20340b50708c8140004025100b07200d40081c103000800c0080090740e0b0075000a4800f003006040640008504105900c1641034050400e2004111458944c10703030741c0503104c160005c3d4500030039105400c209400e035002c20f59900030180b0000807035840030f0207000c0c07040c00c5c25481c00d80e60721402d291000c1100c5001d5000f100320340c88401c05100c3c064034001210901141002c0c03c0c4006407103071800504e4000b49400ca14a190004a070114150342c09412401c00306448005480000d6251403a81c0d41d40c1c0021120150b40c0241200c6100141c18201c2905820207002010f0b0380038030108030046805d5807005980c1200e842c000081103d4901800d115180c0a401205942d6003210103000015094043c40700f00d450700d01031b002030386c14440c0c0e0183c02c50b502c01d4044205054040d004100b0394000d060000c54030f260105148003d0020000c0c890749480c000050040c40c4000412305010045426440007000b20041d442403031003001c2c046000300b020a00942c468420940c100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 144681816 1250 144680566 144680579
    0x30203070b0a090302150603010603050f0d0f1806030b06041509030b131a10030b0117010f0e030a1206050d06051006080c03040611040f14030f0309061e07021504 71
    0x1ca001082400000e00d440705240000354041034a100c510580240c07442641c9a00340020f00401040d0320041c024031442c000c0d1515540046081d50400c50591980c2c1340403100b864060307130890b001c03508001805400075400c1c01424001c0e0301c20344c0480406002d150416403900788800e00c0003040f81800000c210528400c100704402030b24042d901c15804131010080c4038283d92400c2c1714a9200f511020410b6140303002600e444041a00c00000316044000d100341c5594074100e141c24410442d960038825400c040c58613585046078011406141d180e03200544c900240c0000441d90448014a03142c02691101d02c0007989603500046448040c3c05540b00003442d041c02c610500000382c2550128090107244810820b90180110540c0c0c1d109400c40008100703c40d10844a210500c0303281c1120801030407a9401281f80f103035a942100c0c420205404a40944c0c408a40d0700d42e883c01032046240d031100c130400c00f482c403900e9100e51420101c40c41c4030006040030f94a034006280c01c800301d6000720307050001207803c201c0e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 144683066 1250 144681816 144681833
    0x80d02041809170f040501031d01060b18030712060507020c030106060504050405060f0109051311030414160e01090e01020408070806061003050f0403050304030513090c0f1106060108130f03020307 86
    0x4000402101442c103034684d50320440c18040d5204081c1815078562884c9202e002242c450141c520510340208051a140e504200307242e00708450000c04280895901c0b400d5040001d00130742030700c000e107004c0000d50719130b940c030742c800b400c00100b220086004813200382a460700c00340120000b600d043e4803491f849a00748804e0104135500140154482c0300800c180c02402c0c2d070010300c6030003034440c181c4510800c0005010214050645501069100c000010810090020482080e480142d081060300c413201500c0000c8a080482e41c00345071148000d51004000c034000c603a100c06842e031070082c0054102a0760f03071a0303d8149485513010101c0c40d000b04c801c202c418541802d0302c2d2641103050804210078104848074135001c141c010310003002d1050010108052501032400c0e170b0050215088082d0742d007622408040d001d40b03591000c200c0400c2242da02c030100940203a03195003d0049034001801242d0b151401107851500181260300c4401d10700031000045246041c2d01c200f030f18001d400a66469401d450005107 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 144684316 1250 144683066 144683093
    0xf090b011d1b07031b0803010f0905090c040b01090807030f060501051c0618020402031602070b09090a0b010e0d1a010f08100f063809010c080d02041809 67
    0x25000c0090400c01001e10300004264509001c0b900543c960034646805e039248201c1e00440025030148a0904003000102e900850582d1030310780c030a0f60115601d0014209580003035501c00786c41d4026030441c0c449410168800404010140f4109140940e02c1c486103090107425001559480d070500200d00030302c0003c0c00380d6801000203880b004190100014480c4089101b040010701ca203413100c1080f84074000901200c00c442d40c0040085599003040e8050a0043c0c841100e0076000d070080500000380200ea80c03060b0ac0000f4006041150702d50b480c8040d48008108885465042c0b00002c200060541c030b41d0301007020b50f41e10411500700100c00805017041c08800503070180030080d000300401e104614001c10858800201c101011480d44003204406014003001e4200421030b882c190101121240c0c0719400b0040102c00399500d2048c0f50b05000c44624a1061095440c0070031542da950f240014503c4006010036554008010300300782d03c440b524848030740c984001c8600240c69810020038411120440e0741c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 144685566 1250 144684316 144684359
    0x60237200a0806011206110d09030e03030f04090e0f01020307020601141f080a0b13020d0b09010503060103151107030e01110109030e060c12070302032104050c130f090b01 75
    0x1100da281c0841c0c640d41c3c100500402c040300d4000c00d5034100704116508485c503440c4010700e00640310700481c0046d0700242079003c4150005402c01d40303c09001e06022003140e440032100b581d1645014280f0107800d0103002c01c0d40b000ca03501e00ca0711400f00e600d02c40a1000d1030184805034080c0400354944841005000b000106092040c1103450080b5102d0a42040a21800866041213842d83c1c3d02c50a00e080100302c0d01d6a0a904900b084e10815824602a8010056944418420408003516405000d40940240290354043c1c2c0000010700104e042d817480c18085a000040c00b0901003451030003104a07030042c09045010a01e03030040c80c8807542e0440d06003a041e0040314020007203026a40c40041880350f0802541d0300501c4001010b01208005100a840ca4001160360550701c5000d0f1500030343d2548240003034950380700306d8a2018401d000f0343c42044d0243d5005801072102000401c10005611444100d0011542d40c640421107080821f01600d005980030f01100c9a680d8500b1819080315a040907400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 144686816 1250 144685566 144685579
    0xe0702010b0607120c150f0c0503190e1609060f08011a0f03070e270f0a240509070501080c070308013b04021906023720 53
    0x41d40c1e9480b840291031469800c5010038400700340708141a02c841916038800b5020f03142450400400d15103c1e009400301c2c0400300700400a104c0004c000710b43c90300040c3c901074000303100854808034800b5260000c08000c1c0841080e10503c107420b00c4000988491a8841106940ca1710400c01441585100e99001080303200000d20000e80a0807030503101e003028076010b40c440c0c080b9054415807914100b0016002e40404905985103040c089c02c0c5100546080c00c514100383c038000b1242e001001d01040040c00200000000e2400d01800c0d0707a480369281a2000b001c0d102000590183d011f02d042d400f4170f80c0288448006019120300f440001001705000070140c084031071040142c0c0c800640d00141c054111110a684110302c0710f4051104001c1c04144a0100000608038031000100c200c2c0c02c4460f8092482195040f0119440346104c0c160800503104040158002550f401c040100d200042601e0443d44216028800c40108031030880c0c500b0041b0980c0c0c011030480b074180d482c1017030b03050898030940112541c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 144688066 1250 144686816 144686831
    0x8100c090b121b09030307060204050f010c020a0b1815090102010c140706020315040501081b040c0f0521190b030109020d2015030601120b060a03110904050406060e070201 75
    0x7402c8124201510646401c03501204540d02d6031003080649140c2c190013000c0c1c03070303689916061490107500b250054501c02e41c80000208402d60099206000090380904800c130349070300c0d04910000681240d070300d840300c0c1c2e105a2101c080300d50f2503d00e1002d4592000d00e03111b803a03040d15000282103400036034203002840030740c400c019150f0340080f054400d55030744802e0260b683d980b0602043c00e0b0290503080700d500b0508010000c201c0c0d10000c0b40002244c0039460301281240810003c01040d1040002c061000c10420020404c0c020302c110300400c42a42c6485001241540c00410841561401ca0f200c000e01e118802550200180b83d001d082c40e1000120000d011a81e4107400141380038100c19030060822480709640441c50310152000c900f0785400610050300b014000b00c0c9081e00781e00c216021400659042c09480f9604154487d900c950a03015181a0529000b01004d4000345128010070324410b4040c07042643e00c0d42ca030f004180c802c0b4420480410994075107241c80540510140080b015641070214 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 144689316 1250 144688066 144688087
    0x12071b03050d0b0a03020a0e0105120102160332130f05060306091b0a0206160f080609060a030606090204090b01090602060a05060f030d21090c12050708100c090b 71
    0x540302e01c000a503200180d001c2c258400500c20100310341c4005d4018021840c001240841d40c11028121038043e81c02001c403c142010440c01c030302c100300c00000909505003101011a206d0302119034000245c400d411a0515420320747e209542008031100c211840c00101c2440c10803400300c40720700410b196130405075061f0901e0300152050100915860007081e8040c0003520641c0354015002d00034848040341580c45c140003500039110202200c0881c0110159202c40031100d2003040c4140c0c0042e0700e82e07240b40480d115141009036225010708402c1c0c0c845005280407020079900e02c101d030000d10f20020f0040c0e407a0310741000c1320b09039144e4600e042d05110303030000f0410040ea00031406640c007180e20840000d0664440001940700301e0326103110380e0144105843c0c240c01b030381c000c04410f281d0254061284140d0203411861801e50f510f456000304610013802c010000e500501c60074100c6684141e054a90301601ca10b6505e1070583d4032081071100c6501c4807a0541035942081c1c0e031030054174260580c1c03031610342041c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 144690566 1250 144689316 144689327
    0x12060103060b13170a021203070203060c042106150602060411040507080703020c0a0602030a023402090604060e0c0301030b070509010e0f030c04060f030506090d0807080a0e0312071b03 81
    0x110304c01c04000402c103034001d072040a2010701d044a50081400106450f011540b039501d402c0203c080b8028410381c004110320f06804800d94048503003524002e02845c941c0712000f03030340c2406010101c420988906140c2030250280e000e0002a01da2a0300902451405d0700301505800030100d08140928503000521020035844080294040382504015941c1c9002c08070442c03a10903200d2001d00482d1011017802a0200c586c1c0040544410300030a05007016101809122201c4803c5801301c204045801d5400040c02d00d0300002d40d00c494000c0000407100d0742c2c1c1420300c83d0038034102c8041d89041c2c0000010700030407483e00c030419040f114600c0c0007802e01075440c00113002803c60090140c4945498404809103540401c840c1819600240013401070341d40e100c0040000d12002d0104030380d5800b82e840002c01040001400856100d6155074440c96900e17642829034000c80042e00302c00010362035040115408004200620740d61038800c015441920f080c0710300030035a21140034642070f0402c0101c2c00c0004a43d200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 144691816 1250 144690566 144690569
    0x18090b09010909030e190e0a0c3c05040f2607030c0b0304051608030d0c03051b09030304030f0b04030905030105090d050c030d060b040815010609090b04020d0212060103060b13 77
    0x1520b4a9411400340040c0c41c0d080c0c00140e224402941c510300410154946940181d481803806444028485118010ac2c14401c204044440c0410140c0100d41424011860b13240b20035884506102c1c1c42e0540fa25441c4100c80d105401580080b0400362407241d400315000d542c840d803801c80700003034559542542c0c0c40d900c4400c424030606080030404400325007840401d1010038015100e0a0710100a103a982902e00d440303800c444410710607103140c00c613012861400fa01030780d0b01c1104c44000901509060307014041840d000700740c14035003500c01404040009040b084420301568000e010700503c5203402d180003440524290406c45c0170744d06143c1803244041e4000313a50000c207000c40c24945c0c1c80e500d00c0088180f0310b00030030414030b6099041100004816003080000c00680d0a41c03803e44012142e0300c1c1e2000742c1401d0a00c103c500060400b0380400c480a146d50103000c81550003000540740c0700410501d0402c0c1d8201110030382d00428100e060003001e40e054414000245080512541000000d01d112140040c25 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 144693066 1250 144691816 144691819
    0xe0c09060a110a0507080601050a0b1605071502060118020c030702040f0b0d080909010602010b03100b010909060e1015120b1507050f060f0115030b0118090b09010909030e 75
    0xc2009012140540c0c44004110001e42c01c8076040c030760509002e03648440724420311076240070340000032940342889001041590005040241b40000d80c440c001c81109015800752010f00480c1004180001c4802144510700c0056000b45000d504040c2285202c822170b1620a4015104200742c3c00d03038071000300640c1c0d0050740483d0002503820070109030b1009090641500b59002003000302e048100000c03017000c1e141e000c00c01c0e100b09030f141e0b032214026400c0703485114820f981030384049203008401c40d080e00301111600040c54005883c56032000e203042510016080310088181c3c00d030030402c50000c40c8a840300241b82d1424541c80c00706400744003400d0303455103856101d0844d0700e5504d0001c0d141c4801d8021240f090300c11800d20303510f203614140141c80c2d9081494100142c060000455a03581c20404038606032041084e0390301c0b05650500d0140c0080c00c540351428103010b050141d95504090000201e0001d02a60402181a842540c02c0014121058000c81115440c1480e00d0002c258040001c1991680 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 144694316 1250 144693066 144693079
    0x203130e040303090b090f0606040603020f120a0605070e0102010f0c0f0507020607021e090a0e030f031e01090c020c0901120605091002071b0e1b0307051c05040302070e0c09 76
    0x9a0341002c034050a030b4582c002c3c0c605c042c610107016004000140d60442d0039003000c00c1e00c40c44d85a2601308015520a07110295200d91540840c034813510f4101a02401d0403103000c2144c01070062550780405880c002c0310740c0c001003810708200c0d00c04c958080c0206032070b000b0101d0b01003000c030081c5140501401ea0746030001040040206880e8219122641100d00d410b4006024001c2ca44003010540081c0e0740d001c00c9640a1026138001c0344070381c695401980410000301d8081c600341403983c202084180c00c000e1429440ea9002c03200d01024592811105019007991070700400c5001e501d18002e481d200d110700301d5038001c07902100100080a14007803454600c913800b0740301164a840380d030002c07858040104a044280c40c400101c29080203500c10a0103515103c1039000171540d50345000b007154541c4211007a88400c0f8003040907480a100c44401194041c0880c10031905012840b000170031012100d030030079160076a50b1401c0c4010f0640402079100140a00d401d21601480c10b42510f4540f4051110414000e5a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 144695566 1250 144694316 144694321
    0x9030906030513080d051812090609010903020d11040606050405011e0e03030a0e0f0d0b0a0f1b020708010b0603010b0a030b0d0b0a090b09030c19050304081e0106060203130e 76
    0x38803242503840f5a004004591a40100f6840c00000c0030280c454003812a44058000a180c1c1c0100c0d036250490000b0880d50f0601407400e003031101030b60101c0e14150420000d868040f00690742d802811440300d002c0c030740101c0100c5401080c0800c844242d0003d10034807030284010040341e07a211030b00003200c04081c0c4400712070100410049c3c4044190088a0340d00d80030209043c0c0b85c20354840c0c0c030781208140c1150103110080040007802130b08030701c100025000c460080300049120025400c009a41c0000c40000584a40c0c0520090003507500318801c0c0700160001e00e0304110642090245604031481103440503d10351400b0344241c3d031031245d0018442419100d00300c100c856030352940c139010340c66000611608280341c034502d0f03c401804082d100300c511400d54008526821000810b1303800030a800002082418140c40000c0b00761801248100c0c0c451108010104000c80107000700c0760a00d85600301e04422201c01150582501c00da90020340444d4000e0001c0c0d07085009044403181125032080d800c4940c0d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 144696816 1250 144695566 144695581
    0xc02060f032404090b042003030a12050906091c0210050403090315090c0b0903120a0801080f0c0105030403050a02030c010e030306030d030b03060708180106030c0f09090309060305 79
    0x600515940040e806004000c0100d41400b007000058034072640040880504020410441140c182080150044c034441000a0004154800784010150b00580409030004200002403442c0e20010990002651030036858a480800f0b0007865000880180035107418904231020b2661031295011520110f00c1000b04801054001e11a034410b029210310b007440b1a1403d030901078070756110b511003210b02281d046140009400544110011541c2c8240080e0320f144c9850150001d1390003401420b03906016008894550904d80d900400140d2030a03119554150f14124136941048881d0740400070135041300c4003041c000d070b07805802c407a44241e1506080d034441607080022881c50003040d050f81d895620784241e001d5030201c004080c1d403041508804030360f444201e01100300c003912341118445030507034080c002244101740501212680314200c2c0301e03205001e184100c203084c00e50300c107a80103851500c1c101c50b040c803408a02c42540702c05807460788010300003a9003030b03980148a85400d22841007003503580c20108904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 144698066 1250 144696816 144696829
    0x3060906030f03050f07330c0e12100f0b04050105060c0309061b0303041401150807090b0303070c030c0e151c02060c0706050d0b01110a060b2e0e010e100c02 69
    0x11b00c4d040007000b50a0103180b905050031010800c007826010107094185010200c090044e610661455610885c801c0404030038081c9008007101d90555500848125280c0f588080c40344044041c048400801c2c0341d102c4900313000c102c074410b0b00b103240220810070114158140001c1210801c45050f9501039903144c01c4403c0800d2084203c80b11030a5000001c144070a01c081c0000501050340c2035002000055001ca0712882841250b1240c0309442e00702d03603020010083c8030f5224200b08034014056a01c0c2c800681d0301c2c00700000058004940c02c1d0008541440300d0050304c0011680548003070803100108940f54001440009000c80000890001022003000c6440328002d598100c05d240084a5503d9183d204c044c0540d042000043c4010f481c000c0050240d42c41a1400203121502c00040c100c14040d60b1180030207401c143c240990404a054408014482b0000d40d80b5204010650301800c010382c0840028042e10640c2c1c030b0399040000d141b00c01c01540c1d684000303e4031100041d061060040c0400d00c0442c14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 144699316 1250 144698066 144698077
    0xb041a09040c020609010f0c0906030504050c090106020d080901050c040e190218010e030a02220902060a031e09080a030f0e0303070c0b070306031e0503090405010b090103060906030f03050f 83
    0x104030b4109140d01a116800088450003801614000e01400090900e0701041f1881010f100000480c003503410419075009500c100d80090040e4240d9207a60400f5010404d00e250a0384000010f81c002d0903c01ca58a5000a0305034000320000f00901041c204040d64040b1fa0040740100b4002c582010049051510b1001002602045d201810340d20707081c000c01b90700900741310300300b109002c14204900c90403a458041400c200143d8010004081c2c0c081c103150070040484440c58925069554a100b100560380300d4000c1c00d44610301d40c1d40400d1607000c14803103203003411032007144011141c101401040013800180503202604002c0c60001490103042136880007404403580307404114080002800700300d0354808000300303045000c0c07803421031207854103a01102291141d110160011083e040019141c40105080f020310302d004004903802e001a080c002011281c00ba07012044c0c80c0c00c0080d50080e01c0d601030064000802959071b04010061450f106d540100440a000400b0888001a014580da402c141560b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 144700566 1250 144699316 144699319
    0x60207150513030602033c1806010905041109070f0f02030d0204120c0506030f0115120e0609060711070e100b03040506071209051b010207080313140102070b041a09 72
    0x1c05035980c20329200035441a184111004400c06200d003d443c040c61106449118038480100d0444800c2480d441f2000c0c054404028180d4040d440426200c041103094060034079128006a142000d24080c20803491062010380103040a1b4100022540c1050f0481e04400c1182004a50b80c48200d5040341140708404280824903c0480c0c0841e00e82c0d80340648070300e40c5200d2150819861b40700c60800c041c0e40011600d0f0740841c415070005200c0c1e0100c01c010102d80d0002414208850102016200103a4098803a0320800b58040401c1000c009810081030350400028182070400d0706010740000d40ba4a114000c90703040141040c040f904103556018008001d1182c03400c115101d06003440c1907525410103890300d0000403041d0a040f0710414003032040041c6213a004004100c01300031003000040d485420b85c0c800b8150b005981d000150700000313100400d00840c005c1036040c00380c1d041080311044506030f05883c50440d4800c4c6401d01c1904440c0c0125030079225030a00f4112600d101e002001c200780305250805 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 144701816 1250 144700566 144700597
    0x1180b07050c0907050304150c0201020f030a0903020c0a0506070311030d0e07060f05090a06031a0616050f060906010b030a0603020d0f02240d020c0a0f030807090602070602071505 79
    0x61081c007101280307000e001c0a00f150011103035143c0b0300c4225440c1c0015100030b000b01440250005410310a0340c01070f808454140005400e1541c1400c02612a0308204d444803560341d1910042800c05a0500050011f144103d40b1150f2141c02c2c1008200f050080c03010090510209006881c441502001603031443c3e0181401400307440d81c40803000d5124403c2e0f104410205241c5181107034118052400c2d030b41021806001d04100da860141e046000c1c0c10610f1100f10b0647e1072001d1050161900d100412680d0800e0744207541c080070616200345031a42e050003015240c2c015000b0300071112000b003440c50464510008160b160303118049007800408413540000e40c4804041134080410640c0325001111a0007212503c1450014040e1020864400f015030180051b04000000340f030401580030b8003807030095004803602c081d81c1d0b98035007020108144050300454100f100300403810750301000300d60240c4118405400d0040c509000a5501c2045000e04d0489070054411103400c11702c210103580300740c01d048490307 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 144703066 1250 144701816 144701827
    0xa050604080a02060708071b23071802090a060c050f0f0601060807020d0801030209071103070503030a0c050c0c0d0201170a05012306030a022a0303090c0a03030503040201180b 77
    0x70115a034810945a000b41c090038001545031805542c00d0340c411040d513183c0c00d03601e0001e4000c06102e038072a40e0b0101c1e2040b0b0120107041d0203980d8440c501d090321402c01c006040c40c03030610b0050044802c110911440c100e0040154540c142c8030803201c60304441150401558201140c54860304181400e45c400d60f00f17100c3e01021001c1c2d41000528075040310015150440c45446d0604120b88036000d00382c0c3e86001c9440907004200608085441c03d034056460716040c0c0c4c024803154802d505540c0640000c0c0e07600e52000c014000d03900c905201e030105041c428106176107049171100c0c50340d48801a4401551148043e00000c2081da4000c051007900c2990101c102e403180c2c602110030400400f028060b02800040341e08001c0d61400c401d000f00d50b1503000c0284071a06641e210070701070010358450f4841c040360400800300400c040844041c1400d5140c44034010790740b00d1526002d0036207045411208140700741520801040865000000c9a42290302031074416404000001c1798100c07628a58056035040000081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 144704316 1250 144703066 144703073
    0x80a02090d02040f02040b210105010f0507030806130f0b0406050a03020a090c02010213030302060f010905070504210507030c18020a050d180b0c0403030206090c060406050c01090b040b040204230a0209030a050604 93
    0xa0b000b028a00302d911048892b40c07108011a402099106c0e0800402c004204030f4011031f0040003802da02c00e90061050a01d010701180d050b05271030194054406d45515018203c8451070180614000f81509a501040b01803031500000c1036424035200d09400783d9624204181d181d4402e404407205100001c98035680c02d42e9a1400039aa03050844009607001906c1c00086001c001340d0280500444951b035440d4146401c208814440590103810305000019030b40341c1000281c001d01400d0001c6004101d0120014681849040c1406d90002d0f0911242e204018400c02140c00c4410340d9000480c080c400150900f2010300c0715003481c8007500103000b40c000301d41003195010122004005a038030136400d403030850320b41007141651402c01040c556440f41c000d110501002d4410000340035614003a4002103441c00d02900c802411400584060700c030603060740d080100754142030103070504034034502d1700d411400d10340c00401c1100301c4400381140c0541c03500040e0000032640d007007100071010354100c001e03202079003060314 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 144705566 1250 144704316 144704347
    0x503040e0a0b06030f06031b0f1c050105042a0302010f0516140717032a1e060601090608040b01030201030f0917070203010c082818060b01080a02090d02040f02040b 72
    0xc407564400e200b0140c0703001501040c013070414001c0001503c01c0c401883c0400411070762b50741c00c030f031180741c1c205003000607502049007406180d010b00e0140303101d03880c0d03030024046001e1900616030856038054008802000140d9000110b4480070095142035615120505c1003003251505c45e803006044c3d1a840c0e07104892545020804c1404c031000040c07082c5002d41480240380d203e0241350400980c10101d8855089410911132024814000c440c003903602200c200c551058142401080f07040700b5501010030050075580107901c05014210300c2c10300701801d01e0319a03501080c20364140002410551980b42010b910000750300555413090748084511001322803000c0d243c105170400b175010b074400c0d804c013400e1401081c05100c06a000f111207030116500e0031840340f9600d001365956500100c825aa500841c81640a203895400070148140d0010410207440390006108140181500301014410004200a07031385d2903070b21a0380c2c00e5040e07034007240704c0028910500007406280e00c800d000b80301c0024005040400c94 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 144706816 1250 144705566 144705571
    0xa090813080706091d06060c0601081c09030b1303110d05210603060a090302100507050c010f0c1b020d0f0b0a0c0201050c2703030a1107080a0503040e0a0b06030f 71
    0x78125140ca9603283c8040740e03494480e1055000d40740420a801480340c240908855000b070000d00180e260480c0c1020031807074524260300208440d04550000b40c00000c406d5050180d518040ca0001e03007003410350b01c50381c0c007041c0e016022255400201a6620400d8080e41d60362008084103000d0381c0e40703a9051034010b000d9074449070003018080455040b00891070303100c0c044075004850140c018205541c5210f120782c024501003800798158400c0005100b4040305070b000381d0344074050a54030300d5101c8121003401420742d1140c1d00780358034540c2041c035075800c0d890b4800c600c61507501c41e05104100442c000e00208242d00205d50003e0305003807515040c0320601c402805254007a880008040080914541080f0300326101070750101c0c41c1034010403012403682e056940ba01d07030254105a4500301c2d008a400000d00e15070020154402054603e90140381c4e140303003070218100420a03503001e0404085c0d569078884d2640320758080c46c0c0580740070b000400e80d007511507803001c1040c6402a10b9507940b41001c006810581004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 144708066 1250 144706816 144706829
    0x60703060f090c08041203020c0715020d030903021c11010608070609060203070b010b0c010213140415030c06181a19050715020c0309130903110a0c0e0a090813 70
    0x4400d00001c8020b098400c0d001000d4240c0c3d90700816484582e901550511003081905c00c141d001e0180740c14018050044100a0010800d01450803108100281c10600c0416001c41403600d05101440400d8020401c5000d14000c6500745600d028101d00544282015220100041d8070b049008220020001340b41c00688540d61241014942c0e1141c04030395a02c6504001400c041c4864010030002401c400030303020300c005031400503082c400020394400030781c08540e10880151200699040c00c2c0d0400748900141000e4403060404942d086840f06001e8444500c100320410509a95811000b24916107401c040d140f001c201042c1010604c500c840075410560050841608200c50f20309040e000d20700716100f40743d000032070800000a05403204003c3d0444a0224401e0000304100c09103540c600550005040c6040000140c40d0502d04000b00080c404441d4402d5650109584101190401403003034200e03020750100c08095610f240d0302c070f000380c03044040052103606c0100d840000c4c200e845c1d0f0b40d101500c80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 144709316 1250 144708066 144708089
    0xc0105010614030c0906030c0409020309100f020906090904020d050f060601080f06010807030b01050d0c09090b0405071e0201060302060c0f060f01050a1e050d0804030c09020307080f061206070306 86
    0x80c203100720940c03000741e40080d2200e13070800c8407801900303125020b5540141402566801e245e80c4e8075480050740d00441d01205550801510820810303514441d03091074803000c0d101103080000c002c011801510801c0c072410f101c1c0100c41d000908642d184030001151a030b00c401a07a1502ea8039182e159501c407400e1b69400d0114000000060241c107216413500d102c1d0b50b05a64031005a280e4200540060582e450011304001003000203007007021781ca016400f404600d0356244114103103018240f000b00e034980c0c000a03104d1030a02e800d005110394013690b1b001d0b031094185440610f80412100c141e005107110703071000b504006c0102d0124040b2801042c0c1801480c0940309642d81540d840000d10158030090007240e500c000c41c074000b03100000700041400c04903c0d002d000464815190400503c10110102013145e44100010f0103204000c0602081c900804410390150305506000e10301034542100148010703803015400c00040c5480d665031200500040501054611340d0a0140300107020f0300703050049080c0c021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 144710566 1250 144709316 144709337
    0x1914070320041503031107030b13060b03030403080f0f0408010c0f080601020c06031801140c0702031002210703140a0b12061312020a08120f13020d08031b0c01050106 73
    0x182401a45104030344101c0030f104090035a5025038104045031283c1540d44540c02c404030000e4800c2110b41d00800882202c1031980c00076251240645101281c51030003a0420b100820000d03100f03001740c808418440e442e6944604140820790310600496000d000c683d820500a031090725048a444241580280d8401030656103120059039203401400e69a0742102c4200006141d201c7c01213801b81140003e4000443c2c0b03a885904885a6142d06035540000804009080e10440c81c0c20810f000c80b4480300c95056051521080b01c12083c00c0e410004075110100003030020700303494882e50110b04001c44042c84520a4102506114000c0800314640c0d40100c01d41c1d171002c2c2d030b47d00703000800303c0c0304c2c41002c461203c05108a81e42c8038000c00c03480503180150320500c401000010b40d0003001e0020612000000000d5161290689401c1c00001c2d0171f815452894145020240c2c680000050000e6000041c2035641c0c0c9480181078020b070744d411111000f0340404240c1010f040750640146040700c145985841048 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 144711816 1250 144710566 144710569
    0xd0905091503060a0209010c0f0c0807330509130e0c15161a0106180f120b0606090d08031b0f0d110405040903030b0102010e0f1914070320 61
    0x140314807a00030740e0552102c800100c0104a03034008140302981890a0400642d0030ba0300d04c1842201c28908881c40c1e10340e1001400181001c0050400405400400e110101d1101d42c1600a6038507070b0306000399160320201124003c1e03010310b04075000820080c01d1590340202800d1f402c03005100c0c1c104554814041ea28045089141000c4da0104048004541a1406290782c1c8500c003c2c81504104503136400100100502e100e80d03030060700d030081c10030f1b80b6803040c1c03c844002d460000b07141a0f0032052981070812414007003400908c200040a95000c0c0010806880d40b44c00160b0b14000ca003030039640302d10010398060400040c28003440c001d02c810000381c0c00300c043c070b4201070016004103440d18220080601140040440b550000308d5040c2702e00340e661b4607040d00c400106040e11700440050f0042030b00c900d98001556824031807000f02d000440d0190129044020916441d0031103410b0090941000c11096030610100811210007000940c007251a5284d5924285c0d2107800b8800c0810510201d1110b5020756 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 144713066 1250 144711816 144711841
    0x206060f040b1819180c05010804030909020a090b0c030c0115030305030402091812090f240c030f0406090614030405150903120a1d0f07060509120d090509 68
    0x1038002c05000403c0102d4100440d4880d000b000300d203d409405400811404242c030414a107503000c41541200e080c46424400e12183c081d0b80520f04200700780003007001195020031b024084ea0690700000d40d842d400902c00722070001242d00800a000c800295038160500b0010040c28030002d214002e0200e104509402e0310300e04038510020380420f508100280043c40c10340c002c41c1d802444280c172070103080301382d00e0300c580b0302001d80ea410300402c100003402d0002ca1510300142c941c0c5020444801392520802c555002038140c0c3d500d29080c03491000b003001704000905009603010807240820740764883d640c402c07000b05508030601c100004104050100361507504900b08503840f8079040002084200d6002400706086800180b8001050000f40b101102c00401c025016014100c40800859002c1e945405003040c0d04800156039400d070320184075803180000214107907003102c0060a2030740d100c6c405038001c5006400701211840c00340c0507821008150541103100401581c03c00e803051000b40c4e41d000210001d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 144714316 1250 144713066 144713081
    0x30c080304050a120206010807080303160f05070b0f01031a0613050a0b06030f0709081614010302041d06031009031e051c052a03040209100504060b0c060907050d0f02010216060206060f04 82
    0xdc0102d11851a407950500820002076081080e10f8504d02d0021281c440d0540d0b404151201d580302d0419500401c00d001c400242000814400d80403d5018106030300041c1c0f50220b030105440c1ca0316210b100080c2d854400d548800080e2002501c441e81d21b140000703104513441001c442c92000f0410042003c10000000030700c1d441c0301e850021307405200350f00300544210143c3d0036030b08603410907400b0030001c0b805242d075000413014165148485400b50503c0b00c1014141141290b0514201e40f401c5021030200c3e6011140ca040d0130403c5600c04440d0f06182800c4404e88915000c80c50154440100d0300300c048850f6001030711489000c01681c1c0b00380d241d11291041ca600c5e403031514502d40414000320340549098101e641d007090280d400140c1c070310350f54030214050711600c1e400210642808500b60700048000c1c0100c580c003a0b65180a02040360400000603039500c1e03907170f902034100700485c4e07030103403c5900030054101600d041242c41d00055584520095584208845160050721002d40c0041c0c07a0506004808 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 144715566 1250 144714316 144714331
    0xd03030e071208070f08302802070602040510120b01020c0604090c0207081209010212090a03030c050c06040f060e01021f0b0103090c0608010501090b07030c080304050a120206010807080303 83
    0x42c0750030003e0725a4180c40d42a203101b964411010010400301c94143c0c1484840300c401e003400c40c0c0e650114a90142c03500417008060540940c150a83d9450300c045040325581408140b1a0040e264801400c00384002e000340d0704a10b0b00b00500304d0b2841da890350051100c1d40200c24420050007a41d038440d004903105c03911180c500d0781140701400184071800650700040080345061048590450b07036184250b181800c44040300070340560005045a00796810b1025814401ca9108524900942c0101041e0942074521000c0c0400c19400f50301c000300542440984110b0380d000b402c481c1c175152640346050302032000344510404070b00f041000c060554004901261080e490b03468442c40302c804040f03124003800f02a444c86041541c0c629024001800d0326409402074610380e42c03000d05641c1000c0024010f03c105400c013a8200f04203002c9000060f038030259413450107074007071010303a220703111841c00a18004034800000c180c40100700060f88440e0f80043e84a0481c3c104100301c2d013101c0c0e17540516035101d100688010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 144716816 1250 144715566 144715583
    0x7030903122a030e0d030c051203090115030507120201091205030d1a01022a09040b010602160e160c060e010902090c0405031209031f05070f0f020307020d0804050d03030e0712 77
    0x8020500d444110517018501031304001c541e00c0301544d1680d040c5200f886803a00310304c0e03010040c0045850244a00901d0007241c0200b03501240c1143c407420b031303610060702c12650304a1280481d8403c59100d41082d400921074105c01020810842c900183c498000c04400714540e442c02e02603d200807400001c020031f988040c0c01a24460030420288407a41102c4000c840b00c6c0101c15103516800d403524480d071071003240200711402803941000c500a05100c1883e5007180000e5070703840b041c494641c20184250b0040000d0514810034864a8403c0c1c55030030041e0b002901c0d403481c00c44101d564940c10342140b414180b013152466516542c0740e8008106000d00c2c003609401d54400b010703c00500342000002e103c4084020112030f010002c111a00d64400d0010407046803c0362a4420f01204030b03003101d030414003505a4180a5144849071a000b03540e4019014080d2080e0b401503140d600b0711004008542c003911005d020f0525140b410300b070240290070040a034000034481c030207000843d69a0b405981d40710951050341d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 144718066 1250 144716816 144716837
    0xf04050705070605060a0b0a03060302031212010b090f0a030b0a15080d050d0b0d0c0303180303050921070f0f050f1c0303020d06061e08060306070507030903122a03 72
    0x2003c1c001d11009051641000301d584012440380711040150040e04101c1d940450110b0440c41030506002178180e03101c076011004d0000c04012000e100c5024151607910302d0854680116100040c00e005400c00001d030499020780001c0b0500c02d10703501441c45078002820030321815901c0000306d80103c2c013901c69035140707400c1041b030b6941c01880342c401840701f00000d40e404101d800d0340400140c0c440096407002c0f100075066000c20802c01d0b401c210b8076518103060b440e040000c1403450310060031a2090ba40420311840300c0d203021600040c00c15105041d000c03c60000c4444a588900b607103548010b03140a01b03a00c00e10f644200140a10305070b9944a440040a401a44034813003d6624000e11800c01c003003202410b400f40500300c00d1007107504c10400205080e58401228100b0104c0b030140c81c140b904030131030421580500700318680c0c0b4002001070700b10441b8540240e84450605084038aa83c054100804c510240c80303894000c658060007000c43c20303140800380d00c811040b10895460716018808001d0100f84100030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 144719316 1250 144718066 144718073
    0x150206090706021c0905040e0d0f080f2e030c0f0b090a06051b030304030c1502120105010e1504090203010311010804030c02010518060304060e191e14100b0f0405070507 74
    0x4d0b01e0841c1c8007281000390b00e591321240001d090350260741d110a0582e001091081166510000d900c4261000341050010703400c4c0b408400516802c0101000905003040b444a03104010000304203a0301082e51280c0d040550702d81c500507411410601c21101d82d46842c01000c56146050001c0300d01c0d01d00d005007101d661078a001c0090f64550055100307111002c1d0709100e88d000e032610900007944282c0c402d41c0d81110784001450601d4042c0c2c020380f0b20811607441400034400c0049001e0000b0305541003400c0c0059500035003000a00441c4040810207079020011400192890303454000d14140c030311500d8140c1d154500300c80116031480b002c6034042d000035041000d48000d1b502800c010301c1c40a020030503110050f0480c5000c140d559206490450f140780c0d54102c100254403051040c5a01400c0012429010007075640701d1024200c0d191900842603000380c44450100560b0720070000c441c0c0e2104081c0c4045d444031031610340c010321007007c5071805162806a001920725181c81a54071039101c6484403400e00e41e1070385 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 144720566 1250 144719316 144719353
    0x50d05040506030136150b03091b1314100512060a0902010e040606021b04021305011101020903060f01030302060a0b060d020702010e04050a02130e040803180c090115020609070602 79
    0x4a182611484040801c529601280c440028070414050301140100101c0c0c1180e02c21006d036406002e060009105020b20f061000c580c455864078021110225041d801c0005164014501160030985151001021814404880300d0340301e40c110f030300c000d020181c0c0e0702c050081031403511000f02c05903001300c000a15117408541c40f00e40c0c80350042c0360a62100e02094081401c540342904080050b80c0024100d0f40b1095454008211420b0140c60035800d020601c81090080f40c060300845061020010103d582140c1c25410740c2c0440c00020210342c46400e12510032641004c0a020035401401080001402c030402e90150a080e14409860b10b403616600076240b4000703403c414403ca0400040c941503031440d41e00c5000d1540204054000140e80301040c0703010080c1c0c0f9146a10070140d04180004000121780d000054a1744030340c6c80c0d0004083c03100b07a81c0c44542021040300e401c5600c84d0002001040c00b080074461500143c0d56074003122000d4480005040c0d40d031100c1e00c181d0740103910405a1038948200350 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 144721816 1250 144720566 144720599
    0xe0303070e010c0f0b0703060504050a0c230906041512060e040305071a0c0a0e0904021315030605090c0a06031a0103020a0201110309030702010230090d12020703050d050405060301 79
    0x2101070303138498407030b5079140c0001102c192560340000e07844c0c4000303014502d01817040c16004894454100103110f50700401400d8100e581154100c801e095005032034034946a030044801031100101f00c40ea4968880004041c0c00102640301d500103242445280c030360001c02e01c252020f8980c880951052a512580e080328a03034090141140c0e44201280303481d03001c90f051205980102d140c0b82a042c0c58040182c40104525485504184185410401e11015803031b944104402007640301e101182600c1014505c400844165200a000c60700e00401c0041c44500071500c040c8848084502050040e5141012400d4524200a02070340318800c0c580b003100356000b82c1c0282007840a900010611007241138800410b50003c0f030325503d09030400647d4104569050105c4121000d030343c0902c44140303101c8400401d001d0b03203030040300a242d80002105c003003640e10b04440000c10795000135240260495000d00948035203040c40210392030311071a906141c000380103005840039640003034035150850380307040a461615840d6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 144723066 1250 144721816 144721823
    0x112030507060c0906020f01060f05040b04090215071718090612011a1003021e0f2512020606031b04110406090602060702010b0d060c0311041502010e0303070e010c 72
    0x1003001c440010900d00503800744441d60784625074107a240500c0039051000c0505140000d0741f500d01d0600c02d501124801205580090b100095001e240d04085002850a600b010303501044002003080d118621600404c50f6510413904002c0e0300c0510b100203651401402100402028850000207a5040011007943d10010041148800da504503200c80d0071540b440c03243d040102501c000010180c2010100c09200701450b2030114545001070800c41d00302600f0314415891400001000c117507001c00030080e9405040c00400d00750100c5e00002240702e60704411a0304548030350040d600301c0c81341070011450901c0350340f014018080e851000d0101c03520360754001c042c13244c0c055a2012544c10b10007000020348040c15403515418110360030020007030b140200c010840c8046a042c4801500240c90f10000204403d910401c0030665a035044000d40280c0300040806600e49008100003944695520042c42a090260020801c0e04418101151684800c6881c20b01180a19a280c855548220001c00d40d40e0302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 144724316 1250 144723066 144723077
    0xf040c05191a0307080103032001050a0605040e0c01141e030c09030f1603231606030c03061a030c0c030c0604020a08150c090a3f0b011203 61
    0x4568000038102508072410034061180610140301c8540c0c184982c1503140c1c4000300540c03c51030081c50040030804140001810000c4910b12000c1c0c01081c2a0b070700704410740e094003e00c11440d00d00030340e100420080c03080c940b00f0350030000101031245000c02c1440da00c200c180d45090095003111041ea040c0d0b40714006074159058200076105980039220003450090149440c41036540707440004161038118203841001540d0804500a0780104003049000200c07a4414242e050250803050080058a2800000d0f241405400307951003407a4140080a001d581d11a2410040304441960807402c0309c180c2d020709071b4031100b1071103480820752200c0007031540142100505490080d400c00c600b411900880f0410542e80d212030240320031490809a400301030801711008001904000c02c0d41240004042c040d692034880001e44517405454095242018240c410040d200301c40c1445295404e4041c3c1400c05d0b074400006c502100b03007a40740325000400054100d100c1048907400c0808031616680c9084040b024040b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 144725566 1250 144724316 144724319
    0x9172703030f120106030b060c0a1e0f0302070603050c09060301030f0f0206040b130b0a0503070e0307080d0203040e070305010b0a030b13140901050603010c09140613030c08070f030b0f040c 83
    0x208041c005118882c40034000c1c500c3c83d41740050140039504e45004480c4145000d010401400301c5c000752031000c00d07402c201180b5030f900303820000421003290780d04040c0c00d01c10300a502c2802c2c980c00040080c100d40e8076640c204440d980f07007000b94203a03018075525658028030400040021a800510704010301d40581403541000750300350f0020390a0381c401d500503a1800c0e030119541d4148504200c4540052007504020340c581030700d09400821611004111101b030203520f9036401c900d07440030040c040140c0803403011580340011601c0c01079900d0b0002d00c12045003002c8840082e030b00610034003c640c12940080ba41d40d040440d88441074010b071144649007500002000e0760341b02c44640300c0c05000740520650581d00e031a810503489641c00e640001f41468003c1e0b051803e50400a58045003050488501c0a1030450b0b002c8108009074071407050481068100b064648088140070203c203000040355001d030110350015560324650b01d4140c00520010340740004a5000510005060107401d9100744545450381405 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 144726816 1250 144725566 144725587
    0xe01020d0e18090a1506061b051609020706060503070305030301030b0c120c041502070302090a0b2101020901110c0607030f02161710090b01050d050a0f060917270303 73
    0x155803c40f00042554050340440b0280702c0030102085906003031090078452181458009000b103100d4400b10012102d81100745010b000e800d02004960701c003001d460000301c6d60f0b82c44100d00a5041404140d945919240002440d4980065070710100d903030003c05513040d6840e648604000300c0c401041643c40080c100441882c20701c1e484136007407141000010840e25141803070461000e26220f2100f141c04c0d58020b140500261343d0b0909181e40c825600d0300040390340300038139010850303100002c02100121402c0900480c0b0914064026007c080820b070f0b1040392070b02008004c2640d0705808071000380c00617410000100400e1003080004d081c00100c1c01160b144107200410030458284a90007851415200c403c035201854090104c440501d5034220240305030155511510044001840360070310407011801c0004c00c2020520810124030380100e0144486546400c0410140001c10030481d00e01208014100e4030080050235100007aa6a80c001d003992096448850300000c0c2c8c900003d0b52620003440040c01c02c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 144728066 1250 144726816 144726859
    0x307090e040b010e1513020c0106081e01290409030917100e0304140603100512010b030c01030c0206131b081c030917070312090b04120e01020d0e 64
    0x4600c201a1100d096240002c2d100c85000b014001c0c3c0041d8005105c94150383e81c68500480e42525803050060380c984000f1140344c0140b485511000060080801400d4580d140700098a162031803070303000384603081c2000c140c43d0240212038118a10b4400d44611500d840c20698441c800091090804411151f02c45045079144180e440101555034410240f94000301404e01810350403c050800440c01c250420314a64807485941d080340c2d0040c02c0c00300004080c01c0c084542d0900a090103002c402e042d6044d6580c4601a00c0391400b000c4c0031f44500340c01d81005521920403a841e41d0141c0c0d02602d00d82d100c00310300c4c0e840d0200c0981e040e2000555001440c040f40b000c40380c0f032030040a03a00e0081074505242c06040c640d4581caa803840c4241460000048040b64800d03a0010400f401c14029650303600700c5250035125041c1481e183d004c803074900311580d01000315082a460046010314000740c082006190304545d100c1400c081c46005801103030000c440c050262070044203140e030041c400322510032240120b030351 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 144729316 1250 144728066 144728071
    0x6060714030708041701060608010b0d02031902040602030a1107060c0204020a020c10230702090c0f21060906040908041502030c010f0506010813030e090a09060501030602040f1d010603020307090e 86
    0x64414130105e08441c0184244522001808070b401c0a114640c03500e01d000d14079002c0c01000341a0035800000040d00c1c951840d85035161001050000c5446035142d144c02540c0e9001000d5030008a030303502e02c0e000403204000a01e041103680d5940d582031050744650070302000c0d4010444807415442080300101e010303940c1001280000c1c1890380c58480301039414143c90300016001074405142c030420008039000d03807542c10b034440d4044c076000c0402e076881c0c04194000c401071107404401c681c903860702410681d01c01403040c2001c0c060170040303400d0b8880c2d07180c90081004030340b03004100500a2100300002c004204480b031842c98424154010350b82480346039800e83d400c1d14880e41c0d00c0d9007071981e160108442c41d0b030003100140d084003d42c4940c2d501ca032415607001d0412207034104c410340304001d4076001481300c4046070041e04280307074400341c04d000c5543e4030316000010303401501440601440616000ca03880110080d41d40c3c0c5500f0803000780c4070710f902c0d24206600030b500240c6000104071001c80c004ca01000d240c00103d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 144730566 1250 144729316 144729329
    0x20c0409080d0c0c051c02070812130918200604090204170d020a03031e0c030614011106040b07031404050c0f0906030a030807110706030b0f03060606071403070804 72
    0x107541c2d0b00319a61802c119500d4206100910001c4501c0300041030300000c0441c40081048003210500010303083c16454003600d0760100000d8400c4400242030084003d01500c1c5085001c108120b1b900d480f058418299180007452620807104410f807900030070b1800e02031440d01c210080040003051060808a200c40e4481e070046029680c00207010000800d0402c0d403081007601d1603015103046840002e000b1344070b201a4002404040d00c414a007a00d43c0311840405255100004041001221800010340982458419840c6881d80a11162095402070004203404001d81000d005903070707907070390700c800790a070024002c002015920340805800520842030349000364011801840c00005403800c100220008403151030040c111901402a15100020310307a00c8203616040c44030890390b480001b114485504006511144101c2e400040c00540680c40744141c0803041c3e80035850302c0c244c00d003855036035442542c046070000420021240800d145113640381c02c04004500303503460950179032210841500030747c0191 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 144731816 1250 144730566 144730583
    0x130f06060f032609011706060d05090105180c0604090203090a0c0b1207030605060307030905010e0d0e030f06010f12031101060e1906030b0a09020a09050c04030515010b030115020c0409 81
    0x1440748015500808807034000150085103404c1407840020310f41c0d260140316503641ea0000700403072541e03624034055950210b55020200a0381c03130038000c1c09028003000d032100d03202c075120000f401800c41e40c0414200c03102c820240644c1c0c5414984961007000b54002444a04140070344028040010510401c0c2c40041c2078110b440d03501d41035010f000450039807015292006041c644141004603850340010799600080038100010081582d003011405031489804140070f60046806a500190300114070045c5000207404aa110781103075004141e4500c8280036186503151503640801c49540f00c41c0030007010b42c1c401c0c40c0c02d90090b4013000c955403e40b61aa000b40c950908800b040000540c8949100c101c2e02c001810700348401840d40e103651b401e10304040d20b0b0070281c40c0c0b9020381200f0364440c003c90900500c40d03084108041e160259001c0d41d650000c0c001282c41e401580b00d120481035a8079a400e050f0f4110f407072042d00c2c40e4a000b00e2002d00b10611801d45003503000d00c5240c2209652a481001c24240c02035810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 144733066 1250 144731816 144731843
    0x2010504030f03150902030a2a0912021806011209200118030b0c13080102030916030b061908030a0903021306061b0c03020a080102090f09130f06060f03 67
    0xb400350600c1c408001c081524290000320004040505481110300c5807500507500e483c0c08040740c02420080c1c030502808440e0001b820703248081401e010040d14440e40d41c8130b440a4489002e80d652884058001e035000c000d502811101c03843c22807503180c00010505004800c012059902001d450240009580d4441e4460312140200004140f10859120901e05200c0d11900d2030388001100e0f440e40805409403c20b074000803404400c05c81140c1207250050006000300740e542d00c400e4044c0d801105e0980d158024114000b03540860b20000800796540031301050360310b5480c00240300401d040500400c10548054000190004040c00100040407255854011540c00c50040c489804251010711001d04e240010800c200b5501c0400103100d0300c42045a55032204071800c0490061209800107948030720130301c000140c41c0318154000c0c03440000548a031403880010764100554603408840d007480c003420090f08080068001d0700c1c6840c201c7c0c401d110010b034440e01d92400510160b4a60400c40712800701d03000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 144734316 1250 144733066 144733073
    0x90b070207030203240a0c0905120604022b030e030c06030103050105160815010c0204020c1227060703180e070f140f0a1b1b0e0601020c03030a2303010602010504 71
    0xa407003201e1400681e0100c6058140071001c1182a00401a01d0420780c0c6031f00385140c0340d120b588038100a00f0028064805140d641c45200c1d20b03a1006c2d00c00701d01c502240c90900351710f071030344012145400010352441b034800341c1284c40030740b031440d00c0882007517050080e440f00d141c2e03030394450002d0340c0030714058000044e4a14007a060540100c030000e25180900c84110200800800070446000400c0006c2ca003100442c2114070106000e4028030610b000c40d03000760900401040300140c0034155840308101b032010b11005074550400000708045656802030000c01800000c28001c2c440d0380400c1245100001a1940d83d00380d0f141c0c00041941e0f40c80c00550183c0c11000041c0c0d104400c10045040709120070300c0c2c0040c072400703902c1e5441890148420300000304620f41c9400200c2d4020104682c00c40d96841c0c0a8030b8100080c4d0040c4214090081c1290741d0601061865100265180c64000003400a41c58051269070640301d881c6103400308060260b412401c1e4943d0041c0c0e002540c0244411340000c2401d081038a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 144735566 1250 144734316 144734323
    0x3201081f030f03080a0b0307050d020d021302031009060b040b16060509010c02100b0f010804020a0306060608061003020c06060f03030c010608010b01081305030316120219030b0102010606080402040f090b070207030203 95
    0x60102c865681480403003100d591f00440c10908a800403203d5880030440d61001ca8407000180702e01a42c08040700e00c01c40c0710312000360011486035203002c4d080d601041d203541d230030011119a40100c50004a00303000501c2174220050081018800b80032500c0500b40d0955912000c0c1e4008070307800341c0b1503511200381c00d1415404000c0d121240303003126024820410600081020004019046410018400c02280c20340d215980703590051500b0150a0002d0b41e10f034840a010f0070005d56080d1f0046006410304d03007031144130744207403a503088220016118075240d000130405840b80d40f154155241c08200400211404240f0401000709114400031411034800e1002400c00e0400801d024025020f0040c07020000d400807040701c1c1e1001e0700500c040900b500304d4804581452b20401031100b424800154955285440950224a43c24030350781880804011f0004a080e61924070a82000c10a103501140052906402a031011450248000b42d4005982c8601406c45c50a0b2104030140c0c008900500c00c1d8141030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 144736816 1250 144735566 144735571
    0xe03030a230c1018080301030f05060106050a05030f04140a0605060411040f0603020d140f0402040e1614030c030607090e01080705010c02120f0d093201081f030f0308 73
    0x807014100351884000700d03110b000d44000022803a5441c3c0148905500c0010020b4410303410064040e180c2d0f840786040459141d1600041d2404c0c032030f800000402074400c0c4100e8a0352100c640e51241161228001c0c142401c00203130048680070322040c414040410b00300006044640030b144040f51a08210040c0001ca40c08003080c210b1800041005002000030030a588045a01d036250040c0d030f45c45131001e09401401c5940314640c80070320500501610f40c0e03c0107040c6005a0007100c0070820100c3d04143e4503960380103040e01c04171031b0451003010088030362102414003041e60007034299582408403100190400380d0450300100801c14180c402d00509020048881c09040010004c00000341054006010452003c20080c17040e01c00c074990141d00502403091400c680c5040003100e48401e1074001c0600880c0d124003592844080c0402c40d0b01c0448580c0c1e0007850070440c101ca0401c1c03c8000300f40119014100207110034000070340f003d110180c011601360340f58000d50089040c540a040d80d031400a0881d40003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 144738066 1250 144736816 144736877
    0x20901081b090907120f05010504140106020712080433020d050f09030c03011a0118034b0605010509040b010e060d0503030c03060a05030f0d0f0e03030a 67
    0x800e1000120301401c0d00032220250000c40360068195202042243c030511a040b070004802d0400544a821403000d0300200d0690300704460901009508030145d1107900d10034841c2d01c005030b000d10010016041030800d07158207c2e0055000c50b00d89500c8000e811001940c1c580e10282c501d400350b009036042d0300144900c3d9a40a560f2000d07102c0000443e200400f103020b81c0ca81e1100c454400100441103a0b0100055040a08041c0c000d04c4558a840b41c019902c0301c00d0095a4041521801031805c2144401d0000b81a00d03480300e4130400e0b04c102911210610039607a0305100040d402c03403042920394110340b41d035200a00680c2e00044c003031101600e001c10135104107078030490080101d10b080c44006607a41400d42e056134800c8000301c000340d4580000450749418107001030030600001061060105c1401c000b07500c1070360181d41d03007040d2640d103906055540a4441140420780c103c1072411012520070390b00c2020034086460900710401100e000a42113a02103005440822100c800b50380c900d070403201003032412000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 144739316 1250 144738066 144738091
    0x15010c0b01210605040f02040f09020108040f020307030f050a02130e1b040615031d060601021b01030b0907031a010305190e01090803090718020708072010020102090108 74
    0x2400e554060020304180200c14101d0340d1102030b800401a002124096950890b00078030040c2401c0c18036101e8050a907a060380141d0030901c4d141c816003a00e01802244541c180e460851981e11a00c54801554142c281280c1c180506c082c00004031305040485203841d030089002d05404041740c030400182c84103801c0f6403082032781895111400b40c400841e84140c50000415403d10700000c43e00000c0050640750072404550000050a4140541c036a020b0210090b0190000e8001c2d04030381300300ca580780e00c125804c0c1c0c0140d00551442c1140460020050502d040605012a0155072400040e00640049506100281e51104a400460610b5000324903880302800d040080d405c0c214407402c040255040624042070b145e4051400c1244258002c411041e0003030b0300305441e0304006102c42e840c0c1465201b0304d044100701d44d0822740b91706100d200319511175074003c85240c50400b00d95500c50b54507018040c1c0343d0304c2c0030042881c84010384803c05660801002540016905c0040c2c5d0005400b00401400c0000390b240c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 144740566 1250 144739316 144739337
    0x15090309090b1e1003090501020a020f100b0a0b160819020d08090d030e0c0301021602011d06160201110f030a0306080c0d080f0f0a0309030305010b130504020a020a0204141501 77
    0x481500000340f66034050700c0020020040d0746042c0c01500c0c58460042c02907100245a5552030790204540001303040d142c05644061162071349040640e06894401c1c0d5120b010f47e102007000c4c0c01410001c0c4041c0324445445218907901c0d4442c40802d0304a1030100000f00e08140301c681e0041e50500000105424a04200e00c0900784501d0071a500c510442450090694030a64002d540fa800c200040881000800035940c4810703051031204203240740001203000c07641c00e2002c0c18400190628215001d84040c220508004000c501c0d0102d00a200300c00303a060008546102c1e24001c41800b40c0402c7d52150002140c0d07420210a0003170464007613030f1100c5d24540240542a01e0b69803005030720b80310150004051078642c0d10703030a0703040e65901c1030300c0204210800016104504c01d030140c210340180c900a89041046a82e0756141c0e560038491403002044591030031006111a18143d40540758800c5284119001120103a012a0031111034032041e40c0b640420300104010001313151081100350780c00303180000200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 144741816 1250 144740566 144740599
    0x8010203090a1b09050429071d0a03150504140f06060d030e030d080f0f04030c030309060b0d05030315060f1902121c050105010516020d15090309090b 66
    0x4442a19000309550603144a004001c0300d943c180401501091908001d581060300d0319843c0b2102401015010480d443c0000da4a4000480198440c560310b459044503011810666011014001000c0354814403900000c0b0104210300816102c03010211000209800d040c10580501c4583e544118074591100c401e007400d0180c0444c101d904503a054907640340d0003d2600c2c040c1c80f42c014a240c51601407280341d40d100c412940c031200c0c8a0003090820814440e64a4400c1c1c01d220b40c031b008850144c042042401098002403080d4000f000c0180100b80c005029641d03640002c09440c50000290786035880401480412190502c0c080d03e800d0044030007a15210380650380005070300800700312210b8244200407030030a1a0003401b00420780c031010340c000d90b43e500c6442c0111030b00d0482d190107240e10038904000404d107540204225101003548802c106204502642002548d02e042e60080300c03018800390006042011600417a0300d001e00c40d441c1c0b21582402c04001d40b00b15a14000500d104003823403c0c400010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 144743066 1250 144741816 144741823
    0xa05011419050604060305010c020610080105010303080c03041a011202030f0a030801032907030204140f0307090c11030a09050102061320030c100305010f0f080c1221090a0801020309 80
    0x1c541c12860040b40326983c6800140050100380d2028101e5401c090070a441b0b00d5000c5403d030303c941409500204180c0e1203a80440c00c0b00c5003404024040f07039502c408645001c1d41d800195500034072648841e50344440390074591210010a900c122082010300c50503070304507e8240044180d82c45418000c10030a00d00b034030001d19001061202810121002345c601044070380c101c2d500700b00c4000c258034000c09820000c0c0010020361061042680030380b1291410707440741c9000e420741c402d810001070041c040341d4201103552009081c041400d0341800a214a030414240051000d0700700c059450311400403040c90701d00064203050004000031600703070700f010116000501d42c81e9640e0484192070a01c030102011600402e10b0308070901d10722a07106a0f01e400040c50a03a0540100d81a26029150303100c0640c1d4450710014000682d0040c0d110503040500f5051702420000000e00050046800f1248070011032044c1e9820b406d100c803851010700c0c0000480d2040d81c20030700301000041402c14001c40c0395140002d580c1e502e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 144744316 1250 144743066 144743101
    0x11030907090902130213030c0e06093601061a0301081209041107050606030705010c03051602010504050a0e10060c0201120b0111012c0309031b0102011407020a050114 73
    0x45542c0c04144096450342491002d0001c1c402c0021075540801048507034000c0d885110407a20b5410f1400089070701c5c0d69079a00c0301d00880740941200095160207503204000c070980c84848007002c0300c1400195829158102a0b6003107050f10380000f405a007070015441540030030140b0220000340400041080c0100003c4081941d6a19101c1c075480b0385038000043c01801c403a014404a084001c40c0b80030602c080410100d003c1c86040f021a4113007039035003005444030303000e4003009000f08034184016103030460003218250582c5d10515196240644842c0002c0d4203035899081001c80415000c100b002d150105030a440c050103850405c81c00103420741c0d00003082100054058562a5103540c0450f240742d0064414100c60a8441e00a0140c0d0800190300c0c21003017a500b8501203251800c1340000c407050f00100488200aa01901604603107800b40c000075000c114900349241190b58400800002c0c044030b114441c0501f91544c05820340350082e040c110b0946081c40140800c030f002c01707c103010098062804004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 144745566 1250 144744316 144744329
    0x30906050a020304090504050f0114070504030f0c0b0304120905010804020d201e0102011505060a0f0c06051305060609250c0f1a0109020711061b0d050d11030907 71
    0x26a241d4041c0310403802d60049a0181d4512410402031100b00030340802c500525000c1704008001403500403100f40c2e1140016640a400b08500f004180040399a191040300d006020754101d0481540e903801120355607008490903580f100b60b00002d1040070f81e21402d900000c01091804003104c0c20700d900024034106450000510103050040c02e41c0c94804682912150035600411403c5050075041e42d032405051081c1089006520303003900f00d029440444100c3c010b456000d4181410080d0318203043e42c100c14402c505030140000081001d0002d406070040754400d51000625608004240c40d0851802001808840c440c48602c000c102054030000d02d810540303250301001305019403005c2130985407500807080c0034244040391030006e4103103c001184406544609454080c4e40da81c1d070000d0360102d01840800810000c215a020461440c4c98000f51800942c0c440c2c450b146181c216030b05910b452010894000402c1e4041102c1284039240e2140c4a0109217140700903140d403420b07100c0540c0fa84041d00a15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 144746816 1250 144745566 144745577
    0x30f07020f280b01171005010f05092e03060501060f0e10050403051c3b06120a05040203060a0c080f0705070b07020a1203090b0f09010b1c02030705010c030906 70
    0x111011221500d2810b1110b4001580f4581541c48201c40c0c81040ca0700ba401102c0c80c0b00d182481214200c0d940708050413541042950300d044c9042000300110f0402c09441601005091800c0744450700b42d100318084002c41c008001c500c11480c61420341c040d103a05a00080034041201c0e403074540244c00c00c0e103e020f51841140d2104404043c0a41640d140c00740e9000030301a4070030031103112100492440320040b07144079511101c4e60380030503000c81200244044125290405a43e0000c041010841d150000380c0c2d40003401182002000d0b001000619400c407100c52240780c5810a000541c2404e0081c5500540c00304030a00483d056524007130400407028000c00d80801c2460000745085201d030085d18002c1e0f502041d0030010b400c091000a60b58442101c0548102101200b50550b2501030303c00c00d49a158444101403141e500c01c07664640c942c000600000482d52a241448007569034007050007540347d10f080403000b841d00280141490002c06030005410710000c00001c0380800d401c01440422070701c452501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 144748066 1250 144746816 144746863
    0x14130c0815130213090b031c1101060b2d0c0a02010503040813030c0612021201090c0e060d0606141813020415050309011a061605070b03010b030f07020f 67
    0x4a030610360581107040b940d5102040c900740f0184559200411103829000611200c860f8204041d22003d081545000f0020880540c07828035000e4070209604040400000511070340d0743c2c15900e810f902549000c07580c405142d0350440e044095840581c40f1104a81806080a0340050b1881d9500f060746c0029050083c0440010704106900c030444c2d14000c84039192818580c0d0702e15203502030208a01984020400d030000e0418140d00d18429a0f01720741c1c590b42105102c1e407900c40d0b1b00004080c00e908603010082c90010920b06600e984009213031240c01c008000842d6464100300412010445a815900b480308110402091140c049051601203044840345100035003030209900038030899004c241071000e04131464501c2d5421001031803149459000034040e07a8000c14040b11584480a880c3e50b0104042c4114142103440c0002400d0b0544a00202c8800079242c1b03a403401c44d600240d01204d141ca4001082280c0c00c19402e0a40350440390900080c504401d0401c000c984030f01881004c0241c58103107900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 144749316 1250 144748066 144748069
    0x4050402090d08130e010b0a05031503030c1c0201110f0a2118061a010c0b18010509030706061205030d05040c0b0a080619120b0a060803030114130c0815 67
    0xc912002c1e50b0001c4525a1031080e01311109507031540b40326050b900b508079000003498685010844000440c00d82d501c501d59030341d554203541c40942240c903c6070148801d05c140d4024030780811082580d42050380c800c000b016070781d2a0080c00e4544100181002c0c0c03130280000305602c1812030540b240c2c40114206810480013803a04005907906040710713440082d00340f900040d512045000e820074840d0003150b09001c203450b200e12000c1451042244180080d14200c85100410101d410305600641080c0d00d0308440d141c01d2203940d081d91700c02d4442c03006541000458004000f84c03480340400401c0c50801c1e151504c200b60706c486482e8092044100c050783c0d214000030701048000220341740a400c042c0081c41d210004071030002c1100208440345800b40c04400f00380488400701c0d403055030840300e07110a0052006400ea64906030300c040503108041682d16040042840c04040c00550302034070700d007007518000c070035540100b0801e06884020618414030b0300350301001e82035002c40c6040c0d04c1000d80c201c120b2038242960 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 144750566 1250 144749316 144749329
    0xa0b0c30040603050406060b03091917070308010503100510060809010b0a090b01082802130f03050a060f02030c0403111f090504050a06121202011e06030506070908030405040209 78
    0x3008040303040c001801060080d09070344018007031401184200710268a5282103070140c0300c03d480780071207640140c2c1000503900060304001700c0d491007080020351304210619004c40b82e8215640840108500c100140810309081100d60500b01c0c4184050006003003002d100703001e62080340103410407c2810400520100c000750440085150064021120345580310040f2000340341070000346001070b0744c4102040d110203414078044510026801031310325031180440c0b010020352018002e21414158410002807541c03e0030800c0c6e00450251010340207800c0d80307141044c2140e00d85d11618244510501c01e000600070941e007541c054a5000c44120b100c0d0f045880024904100340e0040c240c2000380701e100350200c55020742458101c0b030084e1341c103103c1c9483d030980c0e41c410354080e4090f81ca0300c41d003000342000116400750750b00e104a00441c0000200c1000c40010402d02c080c1e00c1c039403500300c0758803110300b00100031041007403607402304892608074801d5040c11300c400d440744a0b501c83c0520860300400c0f00c224030b59816 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 144751816 1250 144750566 144750643
    0x31b0c14030c0a0c170a0206160309090c0309050f0607081315051501020c0303071e0c150c0b07170c0d0b03060109090c0815010b13090c030603020a0b0c 67
    0x10103c60082e40300e468000c5a0240500401c1d00000d03002e1191544c02000243c1703410040c1e801032601d400d00d0300344900454295604881542001045000014840050312a24007810740f1660b01050040040c189580381220b4010200304a84c400010010103c1c1d11100841d000f140d00740c00142034101e181045014034040c00141c0220358036040920441d00069040d44c009a83c081e029181d40144d410f041640701d0081c141c01800c660600c450000010342c0c0420032080d094401c1202ca1886ca1b2140d00325009030416032404000310364060081c1c010f222012480c0c80d4882407603d805c0c08031032065a0a1150010054002013500902080c62403250059802064a29202404499056a403005c1800c00b030240843c0030742d00c10030798a20129508002051108024000c1031890030543d00c0c008001a081e840109030140c961141c0901003903030101400365002030215070303902113100c900b035004100200010380d00182c103503501003000d00102032000c524820002c164003481c64003104403080d00108646103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 144753066 1250 144751816 144751837
    0x40809060f0a03060305070501090b090f12120301030b0a0e030702040b0307090903210e0a110f1005120a0216110418230106061202130e130201031b0c1403 68
    0x102c2c1c0903198551507403100045901900840704419038a80055484681601656003a1201001103404604048190410a01d0302401041c0e00040b20380d20b035810070f901000304246803c000001001482070056102e600640c0c040d904010300031100144640d00c0c030810100a02031512036041c0070701a5401d1140d00e00400610340107100d0b542807454000c06100218004d50000c4000350300048414140d8880d014001881100800b086181916100300b000c4440d5902644940880ca03202d1090721945095503602c603007505c42c2600d80c00c0d003041c0300c440107100808036680c0d14410300c0030355001004072640010407500842c8408022016001081c0603001c0c2d410002401c40d9250402c0c000c0050420681d000c500740e40c0c2e40c048402c81071504403400e0740c090388248030020b4a51140321220001a900400a0f070003000d01807902c0d80c3e910769100c1030025040303a0316400b01000d08401400d6503014098501008000405030014903245400a0100002c09201601e804410071149007000410001c48092880 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 144754316 1250 144753066 144753097
    0x504210203061905220212210403061d0c010e04090b040302060f010e04170307021e0f1002040f0312170a09020f01051c0b0301020906041502190b04080906 68
    0x50001142024603461a820340d0b006107842c0c0050751104000710744400001c80d400c2c8145603031100b6020089805004000d487c000d00a6041080e24031650021740c3c028800d4260740c20341c071149103003821070072104d410491203000324100c0f1140c40c18810210790486100c4d82420003400561903d000701d0001d00f00094000e02003043c4e5418803007810b40000d0064440d10b03102411074581c0c0e894400050100c00d00303039002004008401030a8230540b1040300515840140c501c1200c01c100311700c0c8079040345429881e02d080d04540040c00503000e00c120a00c48900c0404004405514040c82c1c0000c0201c41a030b03d01c400350407141803648007401c49208000c1120314512116200413681400c030000720003001000d02c120720900030424104190b50140702a14103040031001a42003000d4204d000381c020380301100009526541c00c000c2c0781000c0d03427060003520140a021014013011415468080d10b840c3c910905121480c00443c0180002a54415926841303070b03100c1d183c503490f440302d5000b2407030500400e204514502d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 144755566 1250 144754316 144754321
    0x7090305120d0615020c09060f090f011a040807090f0e100e011a060706050a110f040311030703080a2604060b0103050105011103070605041b03030f11010c050421020306 74
    0x145500d02801402c818207104100080d41ea442c00243d0407000406480580c1001004168070b151090b00c1d00d40c80310010b0500340444041000080d800e040898045510590f200c00502840c184040700d1011154121001854075040040240d6110024415141c07481d460f0380042d40300a1042e000fa01254540c64220b4803034070411006040a8400346d02c5c1c40565610300084c90340c9103507104060720000140501034600d019000e442d841d001e0706005000d4820284c9900400415a204400410300d003001400015212411440c01c0c045102d84604102d12a80c807800c41400410840c0e000c48040114a080c9030080401c01c640c00200c8942c0e84007c9503c400d6a07008000a0040766000000d1a1078241d904020741c1c0c1e2120015694080c030045103a03040d42c024400e8400040e810340c4115049401061004c0d00c41202c01142c1a01c0d1800b9041100040c01e03040040c41c01c640c114443c0c8403003000c050001e02000c000003034001c0482c00f40c1e100c0c20081101070114401a501d1950344966055005026a40c0070b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 144756816 1250 144755566 144755593
    0xd110c06090d09050d0212010e0f030a02150903031303120207061a010f0e2103030c091207051008190c05130909050604020d0213090b0402120a03020601060807090305 73
    0x301000c440d6092240664054000580d208070014016102c000745000244801502800031440344008160081d42d40c40440441c00c0408114842d040c00b00700c8001c41e40c507038808000a003080c0d02c0001d0180d06e00303600c1c1e00b404059a4007109507580443d0442e181302d5000c4031f0341022101c2d00d4020a894450920000b241018410250042c038005000710100b082e5807210440111540480c40707500c0b04c005024081001e025180070110007030034240103060000c00301d030314403965415070b402942c601c260254001603a032038505140c8546003030012072201030b100c118680700128401c400d241c04024200070b000380009030500401c05003541f1640ca040000c20001c1c03110340c0050101d51044c4800240e0305981500080c031800903002c0d0260060707003c1c01500c1a81c03203d900b07000000c3c28142040340d00000c24641d40c3c246555a01c6007802c0f80303010f50034010070341c240341c0140451600007012610303e0b81c0054601e030b00840d80008109045422074540f00241c4c0c1e542c1302084230400c0160b04028068016440600b01e070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 144758066 1250 144756816 144756823
    0x90e07020607170f060402090301020f03010e0f0c0423150a0201150b0c0a0210170f0103170306010f0c050f0d02030d0c090303142505030a0f05130b0d110c 68
    0x11100e5455501c0c040120400c9404880004c507080c1113803c214000207a1182842e1b0081c21540c100540050b0030881c40360401100303a00244c10030085c1c82c0c85403007000040c205c03244000350803107032542c03a9514007030030511510285541c5032030170f00d010020682b010b280f58076440390520000191486541d102c0c15a0400203010703003001e182e00010b00c4043c1d0030200300c08041c9011920001e0554005001c44a003507404d1000310262403d41b0010311050b84045e05180d00040c1c0c4461051000e4603907200b131981149081c040c44031084140ea1140841401003100e41d98219261080711503081c00c010302d1302c1200345020380c0307010080d6607440c01c01c0c007520380803000880d0000042c0004c802600d00a000c4c69030704001c1101c41c00040e2201a00003070f0162103c900c07210b00030303004140209044110502030a1451403c401ca0f2641710821900b03a4400210541400d03440300303580905030214540146440b86003194000404400e00480c0c640c1400051125441c144960141e40b200103a440000c2e15423a142009684 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 144759316 1250 144758066 144758071
    0x504021c060b01021e03160c050307060513060509130e0a060f0b09060607080f0d0608030f0403060f05010f0522050405010902091b0a031d0a061e0b0904030c03090e070206 75
    0x9841141c07500c070085c0c00d10b8003c6000c1c03d0b5840c2c004608103042203240c844500e842020984558070b50f880003288684050252a019014035251156902c0c07410340315241c0034207282c2c40103007009814809820030307980c0d8070201246400700b20b03030124142048010440c00c00c80400f50040520f49468084d02c14141941c025003d03001c4102c80c2d989590365105c0c14048980f240b03003401407c80c0810031081580c2480c05024118401c00c2400c00521240c4408086103181e0140800101d9614086070820400c1400c2c000d03095610300341c41080c00594075045642c170155060740513441c0310b00da03034005088141ca0740c42c01d8200c0710441c10209021900700b505107035000348a0741d8001c0e8001d440ca40300003a0311030701400c10080180c60b404500c1d880c145c5c24420440003414030030b0550f07482d04141b40102c081c140c020049804100c1c000c100c00190541d0130304000424041500404000c6070909280d074182e5581e03000d2581c1e105805060400f070150f524641200c0d2110706d131300084582c6001e40140112a50f00103541031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 144760566 1250 144759316 144759319
    0x3601051302030415052e0e060607030c0201030519020f0310050d03050304030f09050303032404060819030315060201020c15280e01110c12090901090504021c060b 71
    0x85940030000302050581c80111409020b040d191500708080418030b600490744080340d0010320301d1080d000303c14540c0380d0010311310b4082c02e9460f02c1818001d850099844580003c000c03030307035240380070107541c1c02410f110110003000e03060540d2400011001787d1407031603003c505c0001351070071940c4001440300e4462030340041c0c1d0861880010030b400800d47d4200140b07401000c540540300c0c20b081d6682c65400300c8600000744141820400003001c00900c07500c2c100060b600990b00100c4c0d921162042e040003480544041c4000780c0f043d414110108509400487c1c20720a40400c400c940c1c2d29030f40141801c0e400392241d0070040070b4a022940000030b0703990707040d8040e260118110060300e0b1035640c103015044088009548220b5070b0b44090002410000d8841030050035070340c5a01d40403c0030240c04404500310b8100e8030062640b0f64001803902d85d0803109110000c0302041c0413826904100121022444d80c0c041401465241a9a10f010600350348c0d88441d00581c5008001c1601502d0303e4516005000d48040c00085 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 144761816 1250 144760566 144760579
    0x1090b010801290a0e070e03010e061009020c12040f0311060301150503062101060806010807030302070b0a02190f140c0907050a030b03010c020d0206010608070e360105 74
    0x21840d020103014105248080540d4200c95003518040b1031103e646507503440d6408050103d001625064400040d449200152240e00008201d070084c5400e444814a0100040d0050810044d20b884030750390401c02e4a016900c0181c64951040e05903243c1408108100c0102c40d02007400180010002140001e0740e12540f020821014070f0fa003801f505000030300549444a81c001c0e2a001030030701c40c0000c0c41e0302000040c0f229030038400703644402103d10b0591644c00710603510740f130007840180d0040011031b00500449009050052035914025210895402540302403d800105c04800780d1007003004018030041e40100301c040300e90500c1e090398134140d80320702102c6048802e861a80d0f52030b00440c440c07041010192807618030b552034603c204da080d484243d03118141541d40c610b070802601c00b4840c00a807080c050300145401c0b405150041e1820205034403034010030502c0e008001c0c0307060703000800741c0045c00d040d610501a61a0900462130300c80d9415050020690100c000000303400f04032414504a41c0e043d0b03040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 144763066 1250 144761816 144761819
    0xf03030415110d0c03152303121b0a050303010b0d05010501030c02150a140f060f030a030c03050708041d16170105090a0b0603070c0308070905030a0b04051204030501090b01 76
    0x4105507060b0310502c203007140d41030010204442c02508122104205880c0000d880251010380300d4041c0820b0300801401100b40b501e141d9000340007440c3c0c046d1100110020100d07003a15007c805443c0c031814181094400c40c840000606030b000300990619140c6c4101540d4407580c403a8200c0c503040d0000841d400d01d184c1800700008565001e8070031005c04850319805072514500300d001034410098041c1035058407940d00c0740749017480340311110b0207401203010b5a0481040c0c10400100b041c5c0d044c1404013248640c0000200100003a00065030000080d49070a000f07480b4006410075100c0c9000319406490304074000c112400c0c030000070008130351007201141114800d0000b0b81001310ac03481940d0301c010486515141c014030403450b148114a6200020a0011810700600008581603400555040000c03508a588080c20103401c100b0055026495141c004601171420001a540314039202d40601000c03483c81c0401c1c14001d040c41150780501c0040d007001d036220b03500d251242c001d20709400255400d4490200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 144764316 1250 144763066 144763103
    0x304030f151d0d14041503022d0d09050a08040602060609160f03020d06120f030908010b0604031101031b020a1b06080705160204140a3b0f0f030304 65
    0x1061441e01080c10014800980f400c1020303111045050702c004910729007840002020301c5009400d1092401d569405a00c445a001c118182e443c40d0001013904902c825402440d03072410701013600c0740000900c0d0301144612560400a0400c5500e140141c900d00300020086030054000403014020201560500d072255074509528107503201030707501d07540003403001010b4201d85407081c0c000d02000a018070000641703660301c414110f000b00f4000c000311a0442515203030310a050b0020301040041c00610000c1c401541240009029031155010041c03605030201c15461007a413280d4000189201c64011086d942c1901c1400a0f658500c1c20f80105c0d004c8202c180444caa05040c0715001040b58504d0320341c2d0210f910ba001702a902c07500204040c40f006040c0507245409a40c4602403d00000070b010303a104403d09050100d00240c0e00b61038100e5500c118092441811144589044a908104910038101e803002c90901213003021000350304c0616034404d280140e0506040840103500491241c1c600c042520800d81 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 144765566 1250 144764316 144764351
    0x20f09090601110723090106021e010c050313060b090a0e0c06070f030c030210020d02040303030605040e0a0209100b0c010c1709100518060907051e0a090903020304030f15 75
    0x110030b0b06420442c0104040c2601c0d81c10407a9503000201703050076824240b4082600c200e0700b60301400069000d004015210300c500c2c3e04d150078200c0d40c40001e000250390030801414911018000400704c0c5e02e54803150062140b07a900040d00280d004205603203a0924040441c09444140c0d6050784d1401698049034403031400000311015698444031800c24042145c5017130381c45500e00ca100740c0c290f0041c01040c0c0c00d01c15451009107200d1280010050312503003175041c0201180d8617034010303070f0049241c4064025000b20003d5060049030b8102c40501b22941d440400b1000302400307030300062045502140d004000a019040307001b28040c0c42c3d5400340501f8480f100507800c2882a541720506d9040580410600a45600060b900c0000540b89041e04805000990706c1c0c6442210901266040307031500303010304d280c20091040d140c3c01d0b410405202d1406103000444040d41c5114810f05179950344c0a00080600a005940080d5086981d0240c02500c40c10104145e84154080d80c2d085c48ca03004884a00b4003042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 144766816 1250 144765566 144765587
    0x50a2d030e1902030a0f0219061106010f1d0402060d0204060203042c0a05090c0907080a0f0204080c0d023105060307120807020103060512010903020721170409020f09090601 76
    0x600500001c034641c0c84400740d00d0910381c1c0c01c0ea04040d5080c3c032401c98800340f281c1180140031982cac071441d01c4454518554204007042e0011030b000201090100802112031025071401c1c0c2d94255200b41ca40c40d00d00c0001c030b181c49100c604100860010130002a0303940c011003d0701c200c81030552071015944a01d00a0103500388001d14143c0c43d00901d1011404040c0c4a44c0b1203a03000d40010100d415403086c200005424803800c54442c000030701c000040010f0502c0a0188150f5240d15000a41c285400c2c07454458a44040c100b81c070380940d071100f001c2815075540030301215900c03415002d091103103041000325150155a8406000e40541440c001c203666080c0024104100c3d50603803039502080800359250681030340080401e904040e110000440c82e0303a11140c9034a100e0001c1000011403056034500681030050662064209002801c040081e030103511081082a561000d588034072036810700980003040c011034105001d6188080b071085e01c01d68805001300000781003116503034502d545010044901b000d59 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 144768066 1250 144766816 144766819
    0x108010212010e1302041107150501030b070f18082404030e040906090c06030f0c110a020103020309030c06090102090a090c09090f0b04050c070b07090303050a2d030e1902 75
    0x1100402c00030210101c4160011411a502070a0320035940000341031f00c664050700e005081000403020f08100913041384450010084000780159032440d25000c100c194024604001d0148500c14503041600c03da0a0810002c44500ca04400c070b44c6503a1303c140d44020148100d4582c001c0781015108608400300310a103e20b038180c6d81c800441d549002400040c0c1125602113411070b0300e84100c500014103141d030070409084c4549d00081d106020340504030540720f03800c8041043c00300650880a209202041c0072200e1fa070207080241c1e0700c2c1c0302c400d0f01030702d140700e003401192250040031305011101c401034005003c0748104072050b5a0b440e4441c4c45038400c40e4031141c0044041408202e0030440c0c9200e9801460100c2800c60000900755030281c0814107071031040f59458803448001410401300321040134007580020301c903d0001d540c40c1c00e5940140007441038010b900244003000c070b00c05240ca8403400316400c8400c40344d90b2900c408404080b002c0c015181004482c1c40901445924070320a01320403801e0020242c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 144769316 1250 144768066 144768097
    0xe010816140c01090605070801210b061212040302040606050306100309060608160801060605120f0912070b090606190515090604080d0206070206060a030320061006020601080102 78
    0xc0400141c6802a840c9405000e0803010701600b103440b1001c2c0f1503884c8190040a0100d45403078010780c020030001c0141c20100000761820078141003c020000740f0201c00781d200d04507505589440c3d0000c0d215040855485116206180c3c2d68048c1e01c0c0d425011b001141d1080d01e0520203d0f4503403030140d4036800102e132082c2d041001003400522803403003500280c00950144030000341040c2c076150302c3c9040003400c01022148002c0100d003088210002d01c141c20013448949085424040706103004921b040002c0c0c03850001104400c0852000d140a1142c107040840c120501e0b40e44000514180c201d1480171120301c9540e0041100192460902501c00b110038040c1800e0344164034103010400481a003031450304d6031000c0c414441c81010340c8542c801440034100c02001480d253300d40c22030081c07402000904020031508104103000e115241d030040c400580b9032506207406401c0707243c18015040c500c0340c14a907001b445000240120030052101e00d1040e90196030070354500c0da0700c3d99100b031301343d10646c40c8030a080030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 144770566 1250 144769316 144769351
    0x105010c030c060f060602071806050a030f0501060b07061e0e06060618060301240306030803191418071205030703050a0c06151805130305160519030e0108 68
    0x2d00c280c001009862054100080076654141084102c4100d60450005644030381c90a11a030401543d4080040000400c01d0200d2030418000c00c084040c030340300080c10004c00364000f601308031084d048180544040d0992680320101411710030050105c0030701d0301046140b116004c0131000d2050146074204e103400070040580740c45a0302030118960024026995610880c0c542440554841c401540200401003000500b80c10b010f9034103605048400516081c5407400808000003100c0741c00382c9a010308400e101c2d034603207110180002c01400c01a903041005a00c0340d000c0182c0303c002104501441e0b48004101c0e1007450701c031150b0007651442c010001d00150700510200f400207110760014489440d1500e8203082c0c0310440d03900d0304103440120703400d441c1175142c51206110f0101c00303400ca20042010b001e0248518104031743c0e4103580c1c0c1c000300c4000e405c0150001d011440605202201b0032055801001c844034540481d00310544040400340490000302414501d00c0d03950312a078401030190118071a01030707128 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 144771816 1250 144770566 144770573
    0x303090307171e06060103060b1206100903050d18060f0c0b090a02090103061b030b06090f06040f0e06091e16020709050109021317070b030c0f160b0705030105010c 72
    0x66404500801d402d103c1d04668070b0100a0a00b803126500400303500410b442c1c1050b00016056030281e801c0f2000e10340d010b1103543ca80d94280d0348007035048401074030002507044021104071085540c0303410240031840340c0d034070b41050f140c0d00000f805d055240038000e01404589504046800305402c640b40d20000c2d1605035064040f500105440e9040054101202c100c000c80754041010301409074010f60b40d00790343d11440303071100f55080d90960081c2c105181c200300400303489000904034000c070030055000b41502d001408183d01c0b440111005070020710107034060f03da5684821102c0c0742040300c030503020368081000710703ca0039410300043e203000d0800114040c080d5074001d41c207071104408548080441c4034a01c80019890200e00c2054040c2c5824103000d65120b003446050b2500881d242e0256815800b20b4241c14003032100425400251180340403956980d4603980400700c0746000300c6091a403100000100c2400c200420421000258443c000d1b401b003640d20360030260b0b402d0009200d0741d40401d11103084034000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 144773066 1250 144771816 144771839
    0x3060213050418120305070f03050711011b0201140c0403080a020a0b04080406020c0a081002090a05180108150405060105130e010515130e03040605032802030402010e0303090307 78
    0x11a80445418440c690389000250541c2d0b03180018080100544040c1402d0010b5426660f1222013a0304050000c4e080910005001070b013050005801c066880002c504601d101d070700e882102c10f03c1c1e41d000b40051400301c8503010142060b2204c007000740d0329001144000c1074000720b00354443e00228801c075041601c1d54131a0034155101100c1b440c1140a203c0781d542c001034000f2500c0340500e0085502d40e44490502070003034a48020340450511443e2024001c00030300100082036002c083e0700740b0740540c80b0011031010429003901a00729a0307002c266140031040c80301005c0d41c018106d66851048603400440c1600402e00003e086e1405441038014100501ca581004580a03020501000c00003510000d401000c41c00c698054035207600312040802d08030014604200348030035105100408002a04140c0b00044d130f280b01c0c610402041c0240800080d40c031291078142c0401c0701503c18201e00e13501250322080c1c0d0095104444c200c0c00704042c1401a09075050010a903122500c01400400d8182d0038050402007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 144774316 1250 144773066 144773077
    0x111008060a090e1203041514061e0d020a0b0c0607080106020c0d0c0b07050606010905060c06040b04110a03050105060a0f03120810050604081506010c020102150406021b0a060e03040f030602 83
    0x820b40f1441448081c0109904021482240500910003030007821f900740f07409440b001b041008061001c8414091280d64803001c00c214000407080041c001c007500b0000c503640e03a80e1000e002e54410368018002a0400301c1100925000000e40113940c400d98070514159800b010a01800b0010703401003000b0a100c0c14549682c42d0901c3c01341a80009850766005402e5281d4001035040350140c100701d05200455821501c18409414111149807e260303502108039130341c80c0014409012400c030742e400319040c000346070900d0310500005440f9007a0203480381081e80c041c1006640c241e0148240c1d0500240009200b00040140c17940410005c0c00048800400c6401035030241c1510140030b030b9a10002500c0d594000104010304208002c0e0101201c420140300350400014074843c18807450340711000050703a000c03c40e80781402b9588a106082c0d216818602c000703000308208580b100084c402072444685000440c000601d10524050018080c04900162a80a00d10a40281140c0380a0510000d083ca802411b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 144775566 1250 144774316 144774341
    0x10612120503040c0f03140105071d0d0602071b0f080705090106110f010e0109020102160308070209041401050f180a0309090e030d0207080a080109020a050301050f0d0f111008060a09 80
    0x200c4040c1c0741c0440e05c44441e91a442102c2042c46c00400e030906c00c40c2030188036404001030500c0015140042480e008418041d1070340c0f4801d03c400e2400d02d003040300946c141d81c0419048074001e060103c1112843c5080c0507280510311944a0078134000a0050300059100e00313032000503000e9407403a460b00000783c84c94041302070841d46a0048074280c2c2080740c1d00344245079001e0301e804000300d1040c8480c000a81084551401d111104007103070001c0c0302045044007103500440d819120503289903150f0405030f64400718126010847d500308405d01100600604207917020340101882034201c0c199882c54695a090300ea130000b404504582010888602c960f030001247c401e06c402500d1a101c040c0780e019080b44c1c0071030000c44410760080303400c0c0b0340c443d40144030602500c00090214903200303680d400030302a400144a0300d4458048400e821034a81c4a03600b200c5000f59001c034082e20898142d01e80411541c40c104265406104824480020b5070301c0b40a505010f0341003d8203000607c2e042c088800050300c3c2c81c20844 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 144776816 1250 144775566 144775583
    0xe040e011e0606120b030304052404080303070f0c0b01140d0812070305060a08060609060402070813030b0a020a080f04050a05030406111905060712110a030e01061212050304 76
    0x8100301181948002034a10201c0d80058003600342003024050034400740c5000185460100e0249254030004100e8040c1c580c00c40745121118083c00850314441030340c0401ca4041d000100e40022450f0000002e1030040e440380d04c444102e400b100104035001072044e400540b504080c1c0f00100b010414110420405a0001d4a000341c408038030380350012144d21840501200391106400c000c0101c1e03041c420550444022540c2e100f60320310300100f4035a0384e040584440d100e4540c000204495550b0750f0b0407285005c2d4440303d02605d690030254031b403000060a00c01604c0801c0032400182c0750400c54400c40d0f200400b0782e203c441c03081d1103540080d141d98200510413135461051590350f901040041000d0401001c569944403d2031364a400400d04203e1140503e0410440c9855904000344011501650042d0135203403071419542c03a016040c004e85031001000a0b246030014810443e290b054000c421440038040c0240581c540c4c0d25003101e05614505400b4188a0070b0034503030502248507a00854029000741c0c101c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 144778066 1250 144776816 144776831
    0x2120402151905041d01030503030a0c02010603020406170d0503012303030c0a2105040f060528021b090601080619090c050307021c02190312060b030103150605010e040e01 75
    0x40c1200c00c141410b1030011920200e4108440002c10b60004c6440c2c0c10449500b4040d495076032056076070b000c040c0524000a40792441030200038801d5000d0801940c00620038072545503911005101d01c1440c0b021001e0302c0c018024440320f56400760046a048a644110814181c80142ea44403000648821381943c140810415000d80356010403080480600400d0103240d89906030002c51088a000b84141051000502040081d91080002c0718111141e40c285150f80d400400b4128a510f08440420550000e17010028180b403030b0300080c08507203404010b100c03694000100007000300c005000c84100340001e56800c00904c0c141400d1510062801e50b034100c950986031118940019516140c0c881000030b007001c02007024242c1c1c100320103e07949512080100000c204410000d41b00c80d9200303c2108070204801c010410140308100000e0240403510381000032703503140d41d020303401c0d60320038881503506003454000d030782410606c2d2042c03200300d404c140c41d02a602503d540078000600022503407a0b00d0380d50303905203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 144779316 1250 144778066 144778087
    0x7030201021303120206010801110a0e0f09070305071103190309021207030602090f0d020915060409020c010f060e0c030403030b0d051005160f12050903090d060b040f0212040215 78
    0xc01c2e0003961240320044103604241400078500b460583c003030885603040152449076280110100d5140000301e01d000d006c8525044046100c0c0340c008903c3c1d07900080d2160030044125810340c44180282155a19070003011290081d0540c2d038055211410220041e00d454503211500035030049401c42c0c070251035004200d03070051899040580c00e900580d407403070300000c010002e46130400c260205800100c80140740d60155801056071541c0041c5170001f90411070060100a546180982c1d009040e80d402c10765660300f2411246002e080c84070103000300306042440c0800e0050b004001f003442451000a00740c01d543d40d9071801c4000c0c144101016800c140c01148a0001c10000e11409803440e104030000f142d0703170800c007a41d00101c18024000204120540304104041035000058000000b40e00c00c000c1000d4617040710032411441200a01c40e4410141e400190800500350440000c03500e00321800c202e4110781d203680078180d00c038400811400c0307071300c0000080052601c0b013200701f8107900001505080105015 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 144780566 1250 144779316 144779347
    0x2a310812031603020309060402100203090d0c0510170a0903050706020d05040308060406050307060e121e160e040f11040f0b0306010b0a0804120c02030303070f031407050409020703020102 82
    0x59403031040e10000010022016424100c0c8000450103107000c619600d41031141648905c030240000340b1404000b081401d400b07200b0406d4400381400200402500f180301c0ca8403102200052295a01500c14010302025042c007410410003120451140d1070465550301407030300010300104c90304905024040c0400c0011541c588050500c44440000016050510342005045200014086da22031803c10f2024000f0f41c9010074084110340842c1080180c182242c800282407120608108407184148080700d55078204202c11207000200100680d00b40c083c14030300120800d40140115966003480e0004a0001038a10201c48003d6004040081001043c4030000303003170300c5124015100c015210012b0782054903082c403100b03005040410b200751400c100354102408410000b04003620500c8012a146079481c0588800c0d90740c05c1c2d0040550350f40e03151051014103855040c9018000191501b500e05520921060019010707441940b0740c981001e1400240300041c0d07104900c21001c40d5028001074200507481e9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 144781816 1250 144780566 144780583
    0x206160c0f15031803320a1e030c0207030b090307060609050a1805070e061c03020d09080d02061f08030d0f0b0613051c08032a3108 58
    0x5142d103a03401c0620040202038410b4103a44010415090f1054030009030000501b40e0708441c18001c280100791201446800201e883d03a0a0341440000503068001c0303940620113406138000d4490904440300504012800c0700c44401d840000b607808440b06001042d0880b00d0749030b000304180202c83c03518096a50b08800c1d00c641345d00564000d5120740c103004404580f401000328800400c44982122100e07926019617600c06445800c2850408001007042034131030340080d95004d5641c038001000d1100c2854001d617120591640c800000308916000b00d0010030104142a882d25035500130680c81c0c4502d0008100440c1000e04a802041030b042c00140c4400140045c08900c010328100141c1202e0b0100d40c44243c4d05132507804d030b101707803810884003805100d245029010b441041c2d0b4070b0000244d2005200300646400d000261865a0200400c04004811440480480c03801c1c440100781650000e40102c1e14016000007056601c910140c20344584900c4249856000c140140200340c01d40e44c4070708070b080c072808 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 144783066 1250 144781816 144781829
    0x60c0f0d0f0e1b0901092705030910080403120603050a140106080d020a05060906060907030f090f2306060f060705010b1002030705010b031b09060112060f03060b0d0206160c0f 77
    0x203903c84440300d85018074640d8014150214140300d114035440d42030b4166002100d51148100d03c1c0200001401002c00c00c0c1d42c4000805080d5070180d004102014001d0301044030200c002403000d80a00100c03c1c6107000314400c89134040024104101c4d60341e035658111480c0b011030f51941d980c1d1400080c100100300303e841600c0c4503a4000d0019140303142807a0b410050000c08401042e4441c0092262a40340c44080c907602100c0b0f840c0c002607840130000c1c50f401410352400003030142154820040d0600c40001c0d280d01400003109080152090035070071440c1c8440c400c40b8200e910001d41480c101d500d0a240c0001c10010707101d030000003030042105000030602000c44003d01d00581c40400c04104010007403080c0b0580c0d1404400500c036854152040003c0c20341807800c024007a001400110b101c0383d0180032080101c1c0c0d240542848615110400d04102104900c0262203c905103c58903030f0508241d01071004181d00602440d10308000341c1c88080010311164412504503031035400014880301d01d80c0c1d500002d0000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 144784172 1106 144783066 144783103
    0x1401180510080c190509030d02010509030a11070302040f050f1e01050103020c010b040c0f1d0616030c0b0702010207030f0e0904061a0d0c08060c0f0d0f0e 68
    0x1c81d1142d9610703681030340101c820150414050440301506030200c23114001c23103000c22402d0b02d5040e6050b90942d0010440001c0131072203129101c40d01c01102c1c0031685640e540380d000c141101c86820262710382645e83c9061140f141c0d002c01c90300350090790301e2818040c05464045604540a418132416046c960700143c1c02c4802402904071540c0100001c00c00c00c261221098050a610010400140080c0e005640740000c0c014076091242c4001c4041c014605068001a1840081300d0ba54016024460028030706000944100e240c284680c0e4a640056201c0e002c900c3c010b002000410010003e20a0b000f030328603803079200e0401c1c09502a40080c07010810340342c0c0b884c5c0c208030750380c0750411913401c1040d68405209024072040e6001c1110b0014046503410f0b51114200d030303d14007420400c105021000c01820160400d0b9801c581400c0c880354600180410300440300602d01850080c8030942c00c403 = true := by decide +kernel

theorem cover : BRFrame.Cov 144604316 144784172 := by
  have h0 := BRFrame.cov_init 144604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 144604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 144604316 ≤ n) (h2 : n < 144784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
