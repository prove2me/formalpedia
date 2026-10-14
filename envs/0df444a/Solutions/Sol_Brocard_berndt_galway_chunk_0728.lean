-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0728
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:26:54.513936+00:00
-- url     : https://prove2.me/submissions/cc8310f0-ee2a-4e3b-8651-1b5bc6e16d8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 130755395 ≤ n < 130935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 130756645 1250 130755395 130755439
    0xe030703080c0f0703030c03021e0c09060616210504031203020d02040902160c0e13080d090210090e011d0c070201090b1803010e010c051204030c150501060e 69
    0x80200311890115001c030b1414020090b411007140d10400b15144240c60b400c0140050008100c01c0300107100c0e85039000788021181d05100200b0720400020310403900c2c0304040203c6200c000b400b00e50407103414018075088000b0f1081d807468142c044c2000756a8071415005030600e8000404003030381800070800003040024943c109049148a444c500140c68406403d9284043e120319070142c00300c01e00114903102d001880c1c1c1c04680b8818400c28082c0f0728141d89140d0381a02e104121801441c1800c15078020010810400061845c40d40c1e6034000518440c0783e0b40000c6851014400c07800004034030075000d12a00c19102c0d500b13400b611140300700f020103244203440c0c8150040020300f4005944c0002c03400c0300459004001d410080c1c20401102900c4150940002c2d100072800c0e40207034801c2d800c14000c0780100360103100b8400e41640d95a1224600058110310807107440c4084d0044040000403028503010548842c07400ca481490396901151a500d0120001c25150b00b44248070300c1104043e44140d20001099 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 130757895 1250 130756645 130756649
    0x1203140c06040b040804181d1501060309030c21110615120a0c1404061e03140307080a0507060506030f060601030f060b030408130803120105060702130c03140105010e0307 75
    0x4104110540d5039403502c44586d00440d408900114038200301a515811150444000c05180d6190950350b2404000401d680d00082d800c40b18030740c4120030040c0b000c0c1d8400d0700240700d11406810040c08600c81c40e6112000d10120200c107058070992180f011542c0c5502c2015a510a46940014040ca0509048038011050340a0b40c40c2c0c89045040c4600b000d150045c1700315809250482d108500c40c0c0d94440e10031100e900c2c0e0140c014451490302c5c0e408607449a1520405800f000c90321380b4407080c0ca0550351404083d400d000c0681003036120602030b100c00110101c00412203600f06540e001e40b50300131440d0000035614007500301d61080e00b060029605071640000c079251300400c24a404954108001c131043c1c0145865000124401c40020410051003020001000105104040f60501954441d08941c403809090440030031180d6110041006140540241100301d000a00501d148200881500110341424405001103500c0f080c0c101d02c06001d21038641e00404082c207150003c6444c1e07000203a00d428080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 130759145 1250 130757895 130757903
    0x10e060c0d031805100b150a140705011d0304030303110906092101060e04150c05030a0c020312040605040b1501020d1206030c030515090309010e0919061203140c0604 73
    0x545410b142480100d41c0d60101d290800c0988901c038034040740c1200a0301c0b01020f41da008030f00e1f0034003842c02c0c50200c00490f04200314036650044480c04607400381c406a4409003069500e50340ba56500b42c5d40e00507410a60018141c00c0004549c2c4a10b1440c0c0503090318021003040100c51002e218900c550b84440080364801902180e00c1308108990740020116540030540e9480e06620f4108042900c240960b030060107036004540941c3c03403003210b060010680e8010f107140d1000801c180b000c5a02e020701c6030020400c0342040d0040e2424211290200054160b0840341503601540311401d06c0203024004050030380210441c000b05001000160000c1e58980e10090700004101038030752900104003159100b00065039000c10050b490070f680703040256841507031880c0140710003000b2022400625001044541000040c3c40b9106440540000c10030f00407030080014803c0c500070449000d8070762192041302c0c090503070f1703500b0028406071a08008140c0c0d80e60b0401046c66070410001c07140d4154001a400f1b520940c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 130760395 1250 130759145 130759151
    0xc020a12030209120d0306060216080a0803182b02010e032a06040602070203280b040312050103052404020d0f0f1202060609130b010b09040e030f09010e060c0d03 71
    0x810f004126900551800120741c0d0044080903028a45d15421040458080d60708507002c0800803144039800403440d00c00d9030880c1c0d00c00f1001c000043c000001841d440280138141d4203045824010780da0615091660030402c0c0114180c0c080a80110201583d90944e072510003004055500c8409560b81c1c030842c000b50308034410842082007400414180d52900c0343c403000030b588040c1000d10304071000e5004003008074424003941c4441c40c0c4010301514564947d0090768824104400c003512400c0c40003101070000d40800065800c001520b80d030a010b00c5000718071640c020072400340e04038028224407101d1000d00c20411380c2841072001503940c0001c400808c50f0040c0001c0407149840c80c0058042d0800c59005041101807041c500940341c02060880c40703444140c8420300c255032404d5004103002298903000b40302e2003101005200c000345080c094503c0f13001c09000043c0700799000c8129465504141c00110306a180081c00074800d5900022146403c202a1125801c1160b02507005032510080101c241c10199 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 130761645 1250 130760395 130760407
    0x160603061d0f240402040e0f1f0902160b0f0601090f180e010204050915030601270f0b060d0f0b0d03020a080d060302120307110102060c040905150405190c020a120302 73
    0x15000266441543c401881150b59581e00d01c40681e00901c00ca8990100c40c0da800d000800b40380500703100150b03049a00c40050749250601c8048002034003e00450125002e00141c1e0b8030019a40c241481c0c0908010019504c0c5890410001441d04a040e0000f042c084042d50040205203410280c0701062982c20401140074441c403904d41e402400385da841103034030003440018000410300b0f03421a000504401d80c02d036a82680c83e5031820320386034038001d01d001650030900c1151542e241e00340c0c041e0f16100a18000032903021603880c00031741190004414160100e980792407804803002244200b60802c4001d54200f0a032010310b4502a4440300c9641c0b001d03110040c0001c00410604156115401a42e801441e0010026040c01b0341603481d000380d04110b86202210f10004006d40c000244070b88190502502d09241505140610b0b016000141c907440640c10b540035032100507601c500a143c8694012088401841c411040c0300d82600c412907540415500440748680229080205613400664035003805680d0320307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 130762895 1250 130761645 130761691
    0x4061407050f19120c11011b0b1e0f040b0415061a0d0506040902090c09010918090b0708040218090a020406030c1404050f0f040203160603061d0f 64
    0x840c198000b604a030091000c0001c5001d070082c610b548407405002880d000b03070f0710070205171007803150100040e001642141c400e950661190300091000d00540c0c1d450f2118052594521450030020303070301ca1241c2940c0c0b1b41c03040301100381460600d6102022001c0c0106604068440c089030110140c0080c1c90800e013005415809646a00f1980c01403002610750180300381c0752845103001e03420815070301e80b6250422000c50301910b01401000c4000c0e4000f04003c44a844080c260041c1d41c2c0009455814866079107000107040d482c0c4125240b107505505000300d01c5840d02d183c500e0184078002c02030b1061080d100140005030701c030204c01200341d5a1440e200050b036240c0c00300c003500d010320b4420020761040c10060040b04200520002d03000700c5002c8030100040b80b03020000c03c402d484040f00c190b480752001c800000e0036020300003101500140098290b0f50014400f02082c44005040d0b040007004c41c0e00c9800400801590a0300d06040c0d06490b11010700c00d0401c0300c1e02101c0d000700a08005078642c0d02080b030b50100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 130764145 1250 130762895 130762903
    0x5090307050a0c03020a090b13180b0a0f1401080a060209011b050d030506040e0c0904020402090a0e24100c020303130e150a05030703170702130504170406140705 71
    0x2a504001142c501c0c400b5481c200414880e50300080f4041c1e500b9150000b00580c190040650240008110328810030381d02800030002c1508052010704030b1310503040103020407070240440e401000700d24000704000401c503030a00c040c0d440306042020024004d070010081c80601003a603149090b8042c5000d03035526030b100012101b0480c81178584440c01074002c80d160404c200015500d807d0162034801b0303c003560366030080004503182c00520007215000000945000d181a07103c040e44240300400060038591580003045408145070440c41260351568107000410000e0540c2881c2545089541c0007d0142400400d52120302000c040c01480b00d03134030502c411540c050041e04d860265041841501503074503115950180c42c1030b03941c1d2916548214282d145810300c8070304542518405001041450329540c0c0f030b040420491801444250003c1c800750f80141d4503e4401101a01d4002020820341401d06003c5c030182c80c0e0311204110400100001c120032500910030707130080440718200310385408043c2022810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 130765395 1250 130764145 130764157
    0x60408030720060a03020c013c061511010608060c370f090f030503190306030606030b04110f0f06090d0609120f0f0816020f0708030a031503080d050903 67
    0x3c0a0004100861032a915038041c0421980210003440381c4104503030b091504c0c0c1909070241401c02000781c1a413440c0c03034503910070380101d000315080010241c0d51780c00ca840d0359140c004030f4480000d1080700c141005203001d00482010700600005811030781000180d0040c2d5104d03080ca801d40b558040c0310791800803280181603041d50201e120031000d24035114040200340d000c1c4400d83d400403500d42c0c0c602240da0021196072005595111b0021854a20001c00c45492113101040c4c850800d900c45102000003000c41c0240c000441c425001e058080c20b01345046801c0c5c0310303070011084c01005c0c0401c5810090782c0384000700300c0c0e059041da55640d0711451070300852030341c070b006060103080503081080a0040214414501e0719100312581c80c0c06035030a00c00c00888100070001c52060010307008101149201d0001540300a0210082c0111490220b5100c40c0d5410101c05901c082883d4201181940d441501030080300b00c011100d009030412181180c0e118446402500840140b450b0f030b40c4009849a03004000302e441d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 130766645 1250 130765395 130765399
    0x105011b050a0b0105040e0615191a070303060801020a020c0108060303130b0d050601080c1e07060905061501050a1202030c070b090c01120507021903022415060408030720 75
    0x414145042c0008043e0302131046a00462502d40401300414000c1015030003002040d42125110009004100074490039420f0100c6000500400041c0c000300074400c00b001c1600960069211085814003070100c1d000c9510040d0740da401041482c1c0220b40c041100c080810003400d088015440703c202080c80e5005410010035079902000001c5140c840b544041d1a44806801c1300f800280c1d107a0004444c00310080e20000021941030080b041007200c40d200d20000011010115030130403c1350380715182500c4401d0420760356600294144036500f030400b086540080c0003030a00a20742030310840c00414180328120741e20f0704d065002c4041914200038401721205140c00045001d2181002e180c820f0300c80d5451400d4502244460315407181e091200e01805224070155005003007541c01a010082c4101500c0d0401c80841c01085c043c901d03c13068503915005c5007010803504510b0b6151a05147c881c1c8403800541a1081000b80002c0201c0c190010480d500701d60301c010342030300b140b003042001241c1c0310fa1440701613 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 130767895 1250 130766645 130766653
    0x30e010605101d062502151902060601051c02090d02030f15101a0903010e031801020609160b0a050c0a03050315091603090507080105010f0501020d0f080105011b05 72
    0x4103903a1094803c0302a00d10104100d01c0b40c260041001045d1041010040241c0899000307a60548118540d142840e8000b82000d038028000d0070184140b076101034070070700080b0300102c1610206c960401115600560a00304580303042543c4010003408080c2d9009020481d80004811680d9101d5003104107000c1d074050112844106400005512403e258240a810102c141c00203110a10903101c000c04590075880180c018018510000100358000c0596a8166485508a0040c50010401003d8001c120f000003200c0580c9000020304115002e440c4060590150bd5803580d2030480125038411284603545c2240d0703e2081010980e0345010308540440c507400781c5806178081c150450021032103120381003d9289201c040000304001044152b80f400140280c12074000e036854060351000c800e280c082c80880300e00c00ea0310b600301400d40d2402d030401219805402820415960100300d200000c10107800c0000c0a84410070009201010502c6664100002112010010040003000345547c6800030191 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 130769145 1250 130767895 130767919
    0x60b0a030e060a1a0108040303090c09020301050a0b0c0d0c02010c0807150507020d0c02040506010e0901120210080403020c06030a060806090610060c02060f0306030106080601030501050703060e010b0901030e010605 94
    0x6001001c0440da080101d01030b010000d156038019100b454035403600d46200351503454440c401143c01e6100200704400f40366481c200e0b440450510001d8030010301008101503940d40c10242403284018040e4843d001d403030404d0000200451002c1540d0800000a1030300034483c14890004a403c00c0d41140b0141804400103440c0381407220311040c0c1c40d042c2c0351b0580c0a002a44400d00b00f241c0e1001c5683d0803500023038109480100529080d0065904080e051410b65409000030f00000c88100c402c0c1d006c0d1aa500c25000644210709003e01c40f004840c4060811400624081d02e000c0e490b01440d421141c8119800000554046025071046020303200c010111421898036407045030b910316068907402d0a0302c0b038218002070940c0c454200f001c051a40580b4072800c1410600b1403079655000584080e916540301c860104100c1010001303180214051000070a0320b051001d006002c0300c0164105560000002c0014014010f03104101e0f0184103080c607000030f2481d29020a03d0050005800440d8030000d01859 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 130770395 1250 130769145 130769147
    0x2070e0f01140a03032f07090e011503020a090209060706020a081005060c03040605070809121b030109020a03030804020f2206150c02101e051b210d060b0a 68
    0x80d0301c1c1a9801482054031540c103440c200000303205544001000210403140b0701a0120386003603821901762000c4000701051040d1104141000640d8110240c1d9a0b82d0b50380805c200c042c01d0044054192218940700d00349030a50300440d071000c485000e0488019000500140c00380c503900101d4031861b400202c115203840c0c81c40e00040240c0404c0d50078203400c414402c400311700c51514804443e02130b007601009601d03007440d10b03000382c4854008800541d940841800f860015484000210003000f8007140a0038100310522003884441003042070b07141c02685004c4004005855180e402010340341c02d070609c821941d03a68130004200c1c0c54050099a00110040c0782c0101c3c0f0600300c4070440403403d1030700091180c66200d604107035032041038131011000200311050a001509040c1c0040c02250007600c0c100c0808603080e0901f004422038a124200041d000061101d24007054408108240540001078203084c54071a02007451451500b181034449080010015507840c103a90001004014283c1865140c4005000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 130771645 1250 130770395 130770421
    0x3081206010807030c02030301090903120f1d0708102a0f030e0a020306040b0403020a08040b0417060f01030303111c050a14070804030c060e06041101020111091f02070e 74
    0x48540c08030390b1020125030054000c1c040c00703118191990003035056a00c0c00342800d0103400036090a0f82031004056001000c03c0b0a80038070020706401c484041451400f02521155000c4c50440f02d5600e50080c941c140524170300885c1088600d0803501e00484c1d1200803a113122001802c220801403c000082c1309401e055402903042c13080000030b0384003005490b401e40c454a80703601003454000c0d456040313900040d0015403d0f02c00d0a400c540284102d4103980000d5032044a0b0341e000c1d401c01c15110401141c200602001b01c3c54000e008800800503000904000f41035003040001800000c0916840d04007440e00e164043c1c007607544050f045024a803610041d0404140200300580b181044c05080c040f1445a4254035030a9600ae03420654131820725035104c0e10b0844562411400c120b994a84a0000f00e900200400c5060f0149005011004207001c40500180c2120642070032154070540c14024204031f40e8444a41c2510030703081d400e58070003003082480300701e01341200c030342005c14031080314020b010280000741 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 130772895 1250 130771645 130771651
    0x1b0306050307060c080f030c09090403020a170a0e043206090903040b03070804031704050d0f020601060e0d02120703030801030c050402090f011d10050d05060a030503070305030c04030812 82
    0x641901e04281e194801142d401030f5404d03001d000240304000080c038a06042c402550300c20300d0443c000c0e00300300300c1000150007180300740c0d01500182e000d100c001040c0b106d511503960600302a40146071501c84240c002800c0c2c4000c9000c00c601c20713555404540244914101001e04c00ca94056081410411040700507240c09003e031a81c40c002d0801200007031140000104503003d8420403854541103640e00801114480e00c010021070400020300441400020710702200750145d845400900401c280c2c654005081e540c00410f0681158803034401000056002403e0141c8840705507111140700c0b200d0f00100380c242018800701d82c810301c5492400020f0580c8858640d058911540d0840b400799507520411086e4064040703100d41c050156104000d0540c0140001800341c44d40b0042c00006802840010391903038018001180072a00001c1c15200910aa11850798040d00c11990060f02600755140c45540e40a8088010280000040403602118142065030029580b05e120207940c2c0d510041e558000220076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 130774145 1250 130772895 130772899
    0x30c0809030702010507121205010e040b10051e0d17071e0b0105010e03010e0f0303060406060201060b070f080c07080304210f1b030615050306090a0305030f0a1b030605 74
    0x190208034482408002c480b800c0d41c050b5615814410243c1700c3e404d2500c0700701c146800380190100000d03013000d41c502400d07000748941501000a03150078241402c85500041600344400c803556020302c0240d0382c00c017045400138a07411041443c2038441c40070548011182c200902108042001010620805401814042d01c94203002d20807002c108118101c0a40843d402804840034a0050040e548540d28440710550010004100303014042041401c0000300707125610150800400c0221030704060144800034a000e01c001c0100524010088065010b942d00040490a03880780c03010500c04001c0a9510365003624040e41c12840c1d556042955980c4140f0a80c1d900c0032103a1200c0700c0d20543e101c008014070360441d42c10920300c0069030f1806000006007001a00c020b40e441c4c008008101c0e148900c1001100d25008250420700b82410146031a41c020003070070055005205d0900043c2d030100941e50000791071041c0134500d4540503c0e44002d007042d00c5031046402c503940c140c00761030f56140e08420202c80c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 130775395 1250 130774145 130774157
    0xe1614010f0207180203061c230304030c09020f0408060c030901060e090a14031e040306060905090a030e04060302220f0203010501020a0b13022101060b13151806030c 73
    0x4207490682c1c80311924854a026040e040043c01c60542040c2c0045500c40002448580ba44440d040c84400d40160f41006882e44503c103100411103019034180e1074403100042c2d0045040620303680d40c081281e85107006034a40369402041c9080b11907400411f4130040e02c0311505807100b5140201c198900b03604201c0b148280c56082c0030001030704440c4040c0050286c46240c0203400150003988440d070b60f21208000d913450501c0200420b00c41c1c0026114803411180302881056a074920318288601560140c0e00100503403450002845100b0b0800204140305c02d92500b800c04e1780103103e800003401403040e680080d420000e20591821888442c00c0300084c442d0b00c1050411040020b6084042280402d01038507015034424166071001ca4400030400d64461440c040100d0610060b0b4041020f801040c14449450900a442d0301d004e24020b0250401512a07040c02c1414a84061003040400c82580300c0c0c111a1200610080000340c03141c4140910701c0140c01c0080405540d4890080c020501c0d0400ba130300080f1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 130776645 1250 130775395 130775417
    0xf0d03080a0b0103020403030e09060307230f100219080d060b0d150308030c130803040603020910050307080f13060504030e040b010806060706020906040f03050303190e0601090e161401 81
    0x30180c1700343d405403901613443c80c800c801e0310814800003000280c240341d4184030b02e500000d2501c000150705080c4640c052407014012541c1c60074890f4101068003000e104001c2c407110740c0c0d12a80c0c001030503c0c140d00a034412031942d182c14140100039129011740500c09504021021581004602c010101c0002d6820200000080c2040b02c40d004903031404002d080f01ca003000480c280042ca03002500d504400e21200c0c03030b09207958824607031841e402a070043d00482c4c2c01041700700031817505c1d54080d1103070315a5003025451460301d00001803032a54020b00a03003030044050003044001d00065800510030340d1112040240d070a15080203046103035016129072107641804120700786035100b111164003030a8050090303420f0210f5950340300082d4008100f9642c2010f4244000100e60248481d001c0095001c0c2c0007450b41d9052032620001012258645e070843ca6061141c1c02070416400901c3c24110f07828460300003000d07090083c0090401100e06510080b041d07480340041400d80003815421540c83c4241c17603284200c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 130777895 1250 130776645 130776647
    0xb040b0d05061206150a050402071709030c030a0c080607050f040501231c0b0609010e0904030e18090601090626010b0a0b030108060702060903030f07020307020a0306050901050601030e07060e0f0d03080a0b01 91
    0x4442c15100600e42c0034041c20200552065038090f203007000c030080c24ed07603407000c01070046032508c06d0300031081d240468120b20030030503000180003050f0484050300c1c000d450096030b1000c40340140308500c6803504110904400ca050010080d1031003c90384d0392040111764882ca9042403d9001c1d8800c8824038400b0b10b0038145035840c2c50000b088841c00081a10344140784d011b050104070407100004d000f642403100c00001e411141c0c0c5c8000142c4900000d00b01101c80d1400c0107424203141070b60580086810a20f000c5090052540001c06000480c00f8109440414003110a18a01509050900359000801240301281030312000313020f18180c50181d42240c805613107124040b655080223440c074050f80d80041001c21109203011050702c1e80326040740116850b00040340c0c0842c0400400740d0041d00c00c956a0382c288414071000b070281c0c2e5004107092800b80500540c5040307407900e60480d480b0394400c1c402c0500c1d018806481c1c6000038120007000034800100c40d84582030250912000302d40710348201c1c1c0740101b100459 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 130779145 1250 130777895 130777897
    0x203011503020309150403050309010614060306061e03090703060b0603041110090b0a27030206040918060e0a0201091a030714090d110102070b040b0d05061206150a050402 75
    0x21181425410305a8010200c1038000b980050816140c60050f102018040f1445490880c01288130307a46013940ca15000703000c0c5084840036003241c0e40c019000c03182c0f03404698035034094131f0f001b240884019580d40b0b0011b112260400c1501038010311180040104001804003084010031240540800d000340c4912104101c11403000f224001c00707000c1401e2000070039081c49158040c845100b800c0c0300307907000d4444640c1680d43e04143c1010b000108a014607001115540403004075520344c03110501211819680022024050741c003480c91815070300c0c00032080c2815040134000c0c03601e8101e442003100701d181c0c1f450746460359120101070b4041400094002441c0c92540080b225484030b9482c058255190300c4002c4403052504030f42081c42c10300610520752256581560021414401e110880070050807000181c200300c05a4080401d982c4180000c0004c50060021114091082000082e04d562040300003955400b120701285814403c0a0401009481c8071040b015821822070340e01c1030840d520400c10060f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 130780395 1250 130779145 130779149
    0x2d031a0603010311060409050c03010906060c020112150b0417070503070b090d110402120907060c0201050702090405070b070803090105010906061b2102150f040308130c090c030e010b0301020301 85
    0x4000c0030801000402ca0b000101c1201c2880103259034034180c0e07561031402c180e6106403a10030300703020000010007400c0c01e6482481c00600b450f04081104041540001c0d09541e0040f003511383c601e48400c0311429024444201402a00140100948075078481c40020150010141840d590307125419000c1101e20b000500d5200b199141a00c45286c20b051b40d040c800814448035080340c094910045441700750b079450000c0c104660503002500c0244c509814550701e003200562000d401d010400d00d015000d40d0380030003114807664040da0709100c20748580c0303081c4c0e1504c44c0c16031142c2215800402c0f65401c002a8000441c0122040d00080c40700744d8a64858804403900c7d0320a01c004914868044c1056418006645032003900502c1d5404900c108902c1e00c4448000d007402c0134006030031170142c09104000d40c41100c0c0c2c0001d001140c3d0714007803038a940c0160031804054601c0741e00d94460304080c1c0411004c1882c0701c02400c0c1040c42880080b85511000e400f519510303141040550070545003036450f0905200341c2e81 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 130781645 1250 130780395 130780399
    0x111306050a060c0302120406030c0306063b03150103052127040c0f020114090a020105070f0c030f031b2301020409320108030d0b012d031a 61
    0x5400d0702c2e0440c155402c404408084080d8010581c103202c410704010040c100502c0da503240802c1c0480e440f0380080403904660032900621060700e2000b00c1a8a109140c031100100c1d80b0941607001c01042481c0ca0100740320b28265515115841c03403141907007010181c060480c0d1241c0122192941981d01c1141c500070f17580706405400c902882100c0707402d0072595810b40c5030300000c140140c0942403680420242d03a00ca14580020a0040608140d4258248075146e200c03103030301600b49002d04021030070f103880e40c8030104080d04102000c103203101400345d042d00c210501c582c04044140c003d545d030b10b0803c003100420101580403c01d28081269038100559001d599194005c1a10381c10f048090024080b4035000440b640c1c0320341d400e02010501443c0e51103140701c00e907a040d581c811001c0000c0c0f2000425040d080b01029a410080010440d10b60000152030114243e0000840c01001890048500c1114141c12168528000c400ba0000d182020010a44404c0580d4140001c4603c0c04c82c842d42541c00009540e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 130782895 1250 130781645 130781659
    0xa030b03100c2c0a0801020a0908010902100f0909060e0a060803032502030409050a05060a0602070803034003020f010212040f0807050d05190c050316050c03010911130605 75
    0x102074402d16058030f404424400405052150100807900c040300c1c90f000000346070b50000b00c4491890b0041c540900500d4080000c0c00804213941c0800d07a440840440b240038420090704c400b60f482c0c000c001e014007a240a0404106507540c0d8480504c2550003590080441e610b13251011801540120440748100c2c4880465000500d50100c4203044c075450500c0b01007140824000800e01d040ca41c015940150104c010100300e50410804001c50201580d03c01c04c15544802010400d2803800b0060302e03071240d00e050030301d0701c41840300d07402404240d64051044010684001e182c4074400c151024030321041d000342d01b140c480d07a50040c82c5500301c0c810241c0808262014000040c009503a00c401441f04c2c0f40b00300c120604215039941d0366072030107000310905030100d0000304010b41d8480424400e0707240f117442407800344c0368111103880344e988034891041710352800364034841100300340901008580b01400001d4000c1020b80d1440c1044140c801c02d4100c298801c020242001c55a80c14a00401c0c003600d030010601 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 130784145 1250 130782895 130782917
    0x61e060e01090e1302011b0303021b0708070902090a0b0d020319021e0c0a05060420010f0e060307020a02060a03150902120112050c04050f0613060f0b1804020a030b03100c 75
    0x10f03100351003584d2022810086640280b0b110b078103d50848599007072190b140540ca8043e100c5c28540e2200c3d8090b0203400580c0401d20400101c00000b400324102d51181070f00683d01d2440c04040380509615402406080000250329442484654011840388450b8401040250042c10f5501c00f6446503e01c0c165400625003038184025078088000d110300d41a034411602c06220507a07466080210448007524007121070030680b250f00c002d03e005084609424a07040403038040d504800382c0640122400c190003030740084004de42550003040076841d5141c0041c02d40f9200e480c50072005000c2c01c0c94403101c1e4803041d00501c00042d108114000e03654000d02807001614168241941080300403580300055230399108080075032026864a1081900402885a4003407003858060107020b6500c060200c24042546003010800841c030480000d001aa094560203d640301c55050180300d0240345080010b520510000d004c0c806a9015440f4494000c0e003541510f503041801d40304801214186c11921380410660646 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 130785395 1250 130784145 130784161
    0x6010305060a181503050703120302090307090504030c140607020c030c030a0f020d06061805070c03020c0f010201060b030a060302032a04180602030406090209100f1701061e060e01090e 81
    0x40043c500803280f00050708000c0d0b41c0d20075000100c258015245038002400034005c3c000124000c508035510350505605e440003860106e55901f01178483c0800c0030365103d020500b003601c100e101442142c0c22804141d2400500380d90191540010307507a50015201f07075110040e0b582004102c0800c180340c014003406260701e8940710790300c000c4a91701c82240d20125041880c0005080c80c4552009011490100e00f07801500b01e0051084400180854087c04100401c2a000950000b40541000c50a48030710404085500042c0d000d00300e942c0042806807004410401071281950203641280d0003182180c0220881004504003510665161540c21204102c00040d504040d0400c0c03c1c07900c200c2010210032000d5403079250403a0001e0310100d55403510340180c1029854415a100d0300942c4445001290500d8000e01c020400202d10402c0c08401c0c0f05c82d420f1200d40d0081d440f98005000c1c3c060902800b503046604164000314038010080420105038006025510481001d01030b144490685040c903114048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 130786645 1250 130785395 130785419
    0x9051501080f071b0305070302010507030e0a17090607050a050c0111030a05130f030506060123090103150509010308070b070f05090d06090813090609020702060901080702122106010305060a 83
    0xb103c081440044500c0c074003400030300b1307510042040c004d0b690340340c8400c000d2070002e00b90340d4050314560401d81005400b0810318004100130a0903070340b000c141240401182203c2040f801022000d940c8443c0c0402d1074024003d0220326413885a00c076406a413086d000c03010046d00c9400e441134000b00260b100f40301e041845409080104480343c2c810b044604000c4e42d138a0041002d403c1600115400d821402c00d0003844d5070810740005507580c402c1100c2440401d140c100d03c906005039401d003410540c841e418210307460446048030010b0030010341041c84070340c0c482c1489030a50f8440002207e03880c0200d0005642ea91144850120b0940d41e0b598140c0b401244000704483c2900c0d11000340e442a40e640e00302e0b4001501c10703005069188500100080884c0b0702000c2034119035180d80036112160040008038010b81e02e09040b201848003d0030070304002d0704c81d04400c80c40c01c21404c030a81d42d00d00c00060a148403580710302035224003004445407a034640c2c3d0b034000110240c2d40b040d1041900902d295006120005a80c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 130787895 1250 130786645 130786651
    0x309020f060f2107050a3c021903140702011704081c060f0302060c011d07050f190501080c040306020a03022a060109020a020f0304030f05010b0a0e0103060c03060b03090709051501080f 81
    0x10890030090914800c42035414407040b0000401400042031f4042419018001e01e10480c000a81810011486490180c034240840c000580c441400103101e0003160f0144a4080c0c241003c03111a1825190034980304240707501c03000043d201108090f015141c038080a008060540306100160036041b8610380c00e00000d03802005000d4195500ca4060720803141c80c041c071103210005035030014403450303280030309021544202c80349590080c800340040100c05060111482e00b180c8003842e0001040d81c44501c6210a1302503034000409040c00014030301800c17503054014044080c1c0c4200d440038800c0d5040c00341c881066003460000c0041d0004001009140d415070701a0803240c10700e00545140d00d4003e840c090031980302c3d40044602040c1c0065a40c24031409200701c2c0704040c003e0300c83c41065405c145541c1400c00b814407006005c00d44485450390344c0c601c80d4001000904e440021140c89040000040d5100c07030040c000c1500f02880c00c0001103120054000140c06c030785043e15112050b859914200700600002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 130789145 1250 130787895 130787927
    0x31a1005040c05190c020f1509090c070b0a020a0311041d0c0405210105070305060a031202030403060c0c050d02030301180f110c070e0f10060309020f060f2107050a 72
    0x6020351040311201c00c00c04c400c1c0c03035140c2d81c80c40383c051aa807041010760000c50b965203004446060351211b809021104490001c00d048039500c40c00d5484182d030030700a02c82c1784070040c450b03002c500031700140c07005c160040c1034240b20984091050510034200610380d40180e10030640c0041c0d081503141802c25100c2840d0b074100240d010038601c0c03c0d86540201e07098001d00035130403a000482d01102c4034031500c02c1c41b5094011245103001d00041c2084c0001900c140754a02001c0c008602181a8001090080044030b00035039004805010703122842d080582039402aa01c1a5140e001c0e03040340144407480801100d040e10170440d8010605580001000018110140c07000e120039034a0320340244030050301d00600b0241c8191801130000754103005841100c02d00c00f801460103034035440244070a003c02c80d2540310503165903240c000381c45115800014030703000c041c20380581c0155001690f0480303a50b1607401080000d4241070801203000d480d412160748001d080b02e441002170014090390402a106d174129000501c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 130790395 1250 130789145 130789147
    0x150e09130c030b0907054e07090209040e07031e08070f0506100801060e0a0f0212150102210306040915180b0108030309060c0d021c0501031a1005040c05 67
    0x3079a540341d100080c1910343c03d003142e101d24420400d5241c218070240707403103c001c910451003000c1d0207c100c80d20039a105603441440500d151b03c95000440801402000050008a40381c032179032040004001d510500a07980078608011895801b00800102402240e1b40011403005495002c18102d0f811840c25400b211142e00801002c00480c001c031518406440c080c0000e80301c01d0a007101c14050050f22580114160390510000304890100d0104842e07100311104800704030b0101802400000344603000715400f003030780c000f02402100d04101c0e00150045200380c00301e03208000c03000455400c00400c02082c020750740041000418a0502d03820030302c400741c4242d488646ca1000c00001c0415505000d031010118815041c015040c000b0007103680307004000c1070000e985182803204200313841e018010001d0416600006c2c055154260503411941c20100c0b002c11503c10141c80d0035041c016000c207100a0300d03985000401d1404004449145070301a071510103092140503d842c003400301400c00481e4034018044 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 130791645 1250 130790395 130790399
    0x2307090b031203040b0a15060e1003020d09050c131509020a0c050703030302030405120c0303150a0506040602030301090608011107030e15030f040b0115050702041d03040f150e09130c 80
    0xb6120740910b00075480380049440902c0d25400392021a280ca4801e941003c440e00800c01203181c000801d42420001a1003c02c0c6058002000344d0191080b00d51014101d85000d1303900e002d020740450404860343c03007181e43c46115000c00e4840e1080c0d4600705050703d0303c48078400d81002a600e0030350041480400c6c1d07003000d003a12402c688419040c2580c981c021380c0030a400100b0071017004002d03c03d9040c3e0300595545036041000300c0181c10303900e010050603240c2c101d068204c541602d54402d25041d0003024002c284c40c0c0d0321602c90400030f480b500f086c0314500c01d503424200e01044802c018080c0000b140c2140d4941408d090741c1d07407030440c0c000852a6496410274140419080e28141050080d40308003080d2222200e5030806181007080c2d004e0591169185814200348180001d030701c20122201a030701214080f6556021110400030001c800d03800060a21000800260207100d040100741141c1c501201008c000c42c20503026541e180c030348074032294081e584100042e103410982240d1a900c0d800b0311075103e4156 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 130792895 1250 130791645 130791673
    0x405070306360c020a031403070e091801021c0501080708120a0509030307030e010807170a0c030b120f060705030f01060f0c05010c0302130906050d02090402011215032307090b03 78
    0x140e0f004880e40040e005050300c0b10626400804102c20406010007441c44e501e001607005040700e0225010511800c00240418070101e0803151089070190200002c56503042c0080c00350402a0a4424540d05141000000101224040355940c2103810103005041840b01540c900c030001d03402054a80d041c80018046a05903403420406000304603c03c1c1c40301b041c102841e4002405000d4005e01c404d04202c0303222021040700700d541040c5600100d040d0408503a040c5400c030168082c001081020382c000c4c01380005500500400543e094903440441e00b6202a40c0300c400b4102c909100440c1c0c004145144100104120792051a41d1407003d4242c0c60545c21815003580e540c1e080d95110038030000000d4003c80c0b4411041190340b0b444006103101074003041842e2818002c100740c41408640648994214000071f070030742e4050440a41c0c0510204400c1050603c015040c140f414100e010544002c10b020300c00c00224118017092002e0140140c00401d2010300d00b44011003c1c0500c902803540600540c08075029203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 130794145 1250 130792895 130792901
    0x80c0409030908011802040f02190e040608012408241003023102040f03151d03030a110702132007050f0d020c090c070602090a0b0702040507030636 65
    0x700307002a617a190450341e00403c4281c07030580c1c0002c4a100e2041024420f203034010660f04004480c1030405103008580c15000600400d03269000c0d413241e50038401410340400c03e034009500d01c24040200c00c4c04490f1038403401d03543d450610001d40c10a11010071048099075060f5403859000340a01e01c81404c141d02d0354041110402c4551000c1c41c4d0341c07030486481449507010b034010180d0010440301141018644284080c0b400894800601800c04024101d2514061a0000e840c5a0304541c0b08c49400a068440c0c1943c9030310450748000e02c9403810f07811004101300c00040714007260300149001c050300d00c40d55021000f408034010b0fa1160301500030b69043c41403001806040f0050160b00501100d1201180c2c1da400c1264a10300c0c0c100315000b042c0e081e60290388095005800001100000392034690743c0c54440000d1040c50280380e804404200c0000e01d00b4a0300c002017002c035200b5102400036407107100c000d40030340d41c0500400ea84a4802102210342a40c1d268030501d4444020341001c02d0250381100390011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 130795395 1250 130794145 130794161
    0xf0905010b010801050f1c06020d060b18060a0507110a05040c03020a020609161502030409060905040201030c0e090601140d0c0e091305030306060c03070b0a060f050406080c040903090801 82
    0x41a51910303507003103481d81c00040d51401010143d070079402044580c400039400d8040780401d2118401a00c7c071100600403142e0541e40a0900d05900704103840d01c1d20552441500f0a8040307145001e5460030342c03a25801d000c41520a075003800c0d140d040c10441c09503a41480010664803071a00031209038070020304c1e41d56a01405024082c55200140e4034681c102009040900c002c00c3d0454640c003007110701c00090116290351048075580d849400301a41800310490442c455a88500846420080080b070b40e0500e903405580030314401d880070099128024401d440070b802d00c55080f6442a18940054201d50040c0c00609071600328042241c9008581c000c031008440310752480000082518001110a040c14043d481d080f401088016441c0c015503520199648002410b450145102194081c01c80000f002507a11455112040030050320700038103c003009264600c50120240012540010142070501c03c503010b50b4698809010320701031080500003d008a04401c4041000401001804a400784104a5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 130796645 1250 130795395 130795403
    0x60711062409101508092508070e0708070305070905040f0204170d030605060f07030c0305040305030309010f0b040b0102060109091e050604120806100e061318060b09031f0f09 77
    0x1003c2d00304648404900710b8514000f061141603018400307917441c006001281b100020344081842041c0744e01e600c004900c940d101d84034902c50b41d00041400b0040e290031902c940050381d5400317403540d00c1c0700e000c4050314010354031480030441c480c1c0c05201d01d0526400c48261002e500401500d42680c584038079581e281450400c8056803c080c00140c00c50f40c0c140038a0004003000c1301c00c039060118003020603809210704180141032025202c034039000c06000d5401c1d28001e58000f000c2e07903243d1030021030941c007810f058001c04004504c0d084e40300c025803a003449a140d4210b41a8001c15590b8200380e0050000c0c40007240a44000140581c041c00c40c00d542c00f6600d51240c4108090506400c0c14a840740300b50592185440500002804211203030300c4101c0c1100e85440340340380442d840038800011a544e0b02c1000f6960f4222081000c0215090700c0c0803074074a5410034080b00070005079076200003441c12401500c248560542002e04207182d48500707071007a10250f1468480000ba1b140c000d1490070700f00c68031240125 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 130797895 1250 130796645 130796671
    0xb0a0e160314060c030f0a0f0e030705122b0905030a1e0e0d0b07030b0306090a02090c03100b0307090b04091a100f14040504050106080108060711062409 67
    0x1c01000703626010030400000d80c0000b004103003020828541603000c024a408010038031100042c0607d1056000740b5650182e40c0c50420800d0b000f203018070317120f0b030020301e0507111886001c60301c00707040300c1031406c560f6500d007211140d400584031540c400810b024121520240d02d511082443c0105200340001d1490011640390600d801088526007050008114100d009100c08100e050b0210b8032640d0313460201680c86a42c40300385a40743c04c03040e0000c00305100c40ca5010710849041003c014800100110603a008032547d42c1c99603101c07424030020344004c44180415241112003004103100000c05035400c5121030800725001900c0f8560001075820a50001e4032050321642144901d2020140c0c1072101c1c00203945100070459156000b402000c40220754500b0088820017290035190b55009031405404020024042565071b18002010a0300a0041c82e2a5014500200b914280103c2c5000d0600442002a22aa90b100d4108030b21030203400c484401c81b03468480030102907136151075039148500c4024201c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 130799145 1250 130797895 130797899
    0x908030a060e01080d020a0b060612040c060318050a060e1903050a080a020a4401031704141507051c030b010c08030109050903040f06031a011b0b0a0e16 67
    0xe0001c0d030710180e100c04d00340d070403540c40c040d1120741c00b003600700c074a5030400000c0407983c40b5200400c1a030703c54080e101c14602020700a00040003107481e9032100706c5400f503600f84621941e604518507420502e03d402845ca40c0b1490481c800604103810440c82c0010110030380f0950010161645941035002008400040000400e85469a000750f8840d41000d0b02420441c1400c2ca0344074003815803034103021207520b01d049203481d00c140c80c400035414020403200c0d0601044010200c181c0c48411100a003c00c950600800e508010505141c10698080b1152150002440204401400a030b441ca00300c0303200785280c041220f000070560400c80c45050b841122801d124142c810a8010110381d5000407060400600c1091b15021a9010702600c1c15940e604000203640e484444c599483c40c411a44a0301d040da11103c0c00003907164060b0b100340a00344a05000412008401004440400c1107014a100302c44060310180c0100e0341c40c040b5540d101200c9031000510442542c02c0615042d040c5080340e8903c4d2500c442 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 130800395 1250 130799145 130799159
    0xb130914060105070b10050a030b2e15030b040501120507050102010c0e0f030f0d0f030f0603020d0f0510060b0a021002030c040b0706090206040303121802010e0f03010908030a06 78
    0x2440d0064840a0868802424050002800343c82480400790124001034089845420a40403d0703004000007000d6061860360703890002960003081314040420000324200341c00040c140c0c00c1030039054282030911800381d414420a4480d042c015200c1e40100359894031100b81545640c441c030342c044c00d13990072501d20015052070800c8c54150180c201c181164180740ca5450340a810505207014401c0455400080d08192004030340b42180031356140301548100c0a240d140290082c45210b5418020741c0c080c010000441640c100382c80d01351000030742000100214001050b141c041d44001e80344180281d840317081007803005074240c40c40c5820069417803900048010322070380c04100e1aa50303a030f02ca00b0300f541146052040c0bc0c401d8022489049100c41000800c903003002590b03030203408042c0d801000940c4458903410010082689070486000a0b440c101026500c030f05c41440507144141d0595641782d00070b0001062000c0303024007990140d0035640312006e040001d420072000e18820b00c0568000503100b450418 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 130801645 1250 130800395 130800401
    0x30a0b0418080a21050a02031603060803030f280203161e0c030203040801060605030712140c1e030c09010224060d0c05061c0608070501051b070b1309 66
    0x604101241e441141980014807a1810b680400a66042102141e50346000c034505611421155041107031401d01040400c240690156010300f10082a5054044052400b40c0441d00d80d070140c100740b0b9106000186441603050103e980c420f0f001c680580b0b1150300c0d0b0002d400d0a00c4801c9159040c40d40100421407407400c1c1c400285034000c0c140c0b03040f441c0742d08005d030300040400521440000b08414440180141802041101d008001e818001c100c0540c0c2d54800911a030010754910002884d008452040c19000b400b404004ca060040c0c41c0381a5194001c0c0c511081d800341e1500705203450b81014012004034104081c42c81992100ca0b65541d4541d000002428100d407041c242d031241c0143c82f40705172005542100280d11000544681d08440b506060101c45c845450b48a5580301d1400900041f00e50306e01030300780e481d00d1104081485550703107503002140c9954142c011607001800c1030000a000000e07691074014010103080585040c1510f404082007030368098014104944485d00302040748025a00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 130802895 1250 130801645 130801661
    0x504080f0c031b0f04090204020f0d060303021e03090108060a090c1808030310090207061d0d091a0d0b0d0c030b1b030f13051e0d12020f070f1106030a0b04 68
    0x741c843d2588015103002030a00d03860030b0112409145d0394880740c1d0464880307504891a0340e07a840070b12500d8880c415899009443c0c40e000440050152081c80d07100e4814803070079640d05d5901c40e4061810301069000444206100030b151540c000709103070001034401e216206c0c03d0f1500ca65a03aa0340c0040d41c044003441e00a04d100c1d8010021940108108100c1c8034466105070103071504c0107005aa901ca907400d11502400f401c069102c90b051545016a40c0c0600003da05002500151109640580c1d144001280640100146214440c0821902c00c25000980c40440d9440000b00322025034034144d103449a0703032920f5410031105000140c0500c40705a1003900d9070015140441306440c40c41c50113948a4076030460180000442030b00ba15200c908110080c40301c002511008151204001c0c022040b65686a40c40407245d00800c41d84003140c400d01c0000d000f1178443c1d0b00c40305030140c605541030b40d50000140c0c040c1c200361096017076000c041c400340d80c8010085000b58846c540124800400c0d0017000304450800c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 130804145 1250 130802895 130802923
    0xf02041a0708030c070303060302150a170108120901031409061009060501090303110a0501110d0c090305033c09040b1806060d02070f0804030b0612030d0b010504080f0c03 75
    0xd2184100080801003101c1d40190303540c01d0b03961985c08515081d0041c00c05500001d521500c03480c001c002e010384144c06421081c8007569206400000c2443c0c03214406401c0c09858156041100720781c245103070000040284020624001034104040461030140354002d0b102e034522a0041c405010004481d04080405000003080401041e072400c0e001900700f240b41d2100800f40416100c40701913038001802100d2100b50080024842a48a0601c920b0603910008204030321a1400b202d040c51075204071010303000d0305e61000046181415038407207a581d014001840000005403131001032154400d00c0140300310501340002142e110529a410001a112000b007118054040c0c4041c85402c0e0780d060701655001f040c241c800e107603a5200254540043d1061100c060b02a4002c00e01010401c106040100110b90141c0182181d5890303060411400008100052015902c24020f2117109515a80800c1640b00c0506080d032902d0b986020343c0342019144c0c903c218980d007103035000360114201030001105032054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 130805395 1250 130804145 130804147
    0x9100302120f070612060e0403020a06050c0408060a02030a0905070e090715020d0f050f04030f0c050901060c030f0309171209060106020a0b0a110423030a020603011e090f02041a 78
    0x640a402e40d200f0380c82c401c1c41e04101340b114203407a000442c1d034080c00c00783c1280001500203203014240a961081c0c01a01220b05502d01000030382520003030310544081d25543d001820700f6440d2405102e0203500050f0007803200d5035480d4034400025504215040082000261049080c60441041d604180d103943c0845009410110030707400740c3d64003160b08184000d40f4184490715200d83d1404503003500410420001d804070006010060021100c01c8407419032181a64841c050740301c2080c010829001c1c41280049142450594006405052024030100062400262808040d180c041d8404440c1403005096440020304007040e48810609692081001c00105525403402e030b0000e541d0724100c00040c0c20012407001041c4818101e13080307500ca08004a10035030b1540c0d201d0b041c0401c58100c0c00303c804d455044008140e11541070125009038580d400501640c01c0d41c1c40c00f00800700060007281c0c01030039030207003541c00b140211035486913441484609030010380729030400d0144441c14805008010540030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 130806645 1250 130805395 130805413
    0x11161a07021603080a140a18080c0901061d060318061018020a021507030c2604060209030312040305090f0603040b0103140703060c0c02010f05070c230910030212 71
    0x10416614000c0360f510000c40d175a9811400070484585c00c01c0c02c00107461080010780d4480c13250b4840303490740000701c0059001031160f0f547c40a40b41d0720041c407140749401c81c2e81200100011406502c11000d8481084400084448a00c0015849500880c0c0b172030611041c000c60300340c094004009507640a0140c100d8409000d00b089000303000d40900c1c4880c41004e6800090745080603100344180c1012a0760240e41a5550420301809000703846034040706c00014400c0e12078150310582009090030500d018002d4080d907500e841e219003020b0341c0194a01c607090300c4200310709000014040700f5140314501954550b0785801402d81000090381510718002e1080b84103005000100b0003244946044075840b14940e0001c583c00210a4100340300e0394130241c0003501e45002041810781040841c2e404c0391007681c4181d01001c5030032080d203080c001e441e405402d4205000040c81562000401d00ba11142d1580601100b51094030001f08556002c450300080384079810b1003007046040000e007000107101c0510242c500c0740 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 130807895 1250 130806645 130806673
    0x402120d080a06080f060c18030a21051321080a0c060b04090b0a05071b08030114060721031518050a0c0804110f04020c0309090a06050307030611161a0702 68
    0x403006441f01c10f4100e4001015081066924552952617602409982021146040c6501d60400040c2600204007100c002c03021103d1013602155820040c40c01c031203500d03030f08005046103544080721042001c00d820f44160780200b80c0503805017103c0080d5540d0b9001d00d5159103418010b54079001c030300c14091b600b0800d07114009414401c0481c0d0110440700c0006050380c1d210b02c00c480c40003003025481d6103c1401a901014008004000c5058841865400700102c0a00040c01002c2c480c6120180c040f000b01c000b0601055008080003500c0101c929010030940103507594401008a42da00801560113800c020802c42d00840c01201da0107400740808010101080300054400c0170000c03c000c11000d100c03468088503a560991614200300050400c54079554000d60003603499224802461140b0f03100741c00201c3c844800d00800040d0b520140140c4a51031039a60b429014040c880c00c00c1407029414802d0940c4441c203059094141c900404000007007c143d050721542c1040082e000a046402450b4110000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 130809145 1250 130807895 130807903
    0xa080a030503040c170f0105060a03030f03020715050a0903020c270a06090f020903160803180d0f0302061909020604030b0403020c0a030302160605030405070605030402120d080a06080f 81
    0x10390542001039803075a6501e0022403000f215003101c001c0c0f10a41100b41d0b01040001448024203001d00000c00258489074104004c24603980700c002c00140008042c2075403a44250068051070744500c02c800c284075101032101082c0d0b14200c0d0b10ba0b203865030ba64cc0e01010f142c2d040040c20f8a801044d1200060101c150640300005c40401310030445a60044005c0350607081e10794040c40c002e02008404210602105001001071b40c4004c060502c240f2480c0b1040304480c1300740040f50215113042000310704d000c8040ca000d0740700624812b240c590001407a203015004c16071400c102103103c1d109070f0140410b0f00e0f0152640140e4107000203060b004d50b1030506a0001031311500d08a0b420349070440c000d1441940c5602d4124904810824500d03046400340c0c0c070000805400041c81803c9050205540005644600d4100c4050108450103446540008001c01c044ca009070015a00a4005000364003e200d140c3c80281c900148107580c48006a488070030401502014400e900150035224042c011030b0400303c41072940c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 130810395 1250 130809145 130809163
    0x90406170604060917040f03020f102c121c02030f07111c06060602060123090c091f020d05040303120b12070807050f0a0e011a04210606050a08 63
    0x4003d1340d40322031000b800190b0851441c4809050942503a41c1c3e00d401d03840c1031040c1c242c4000c900440a0304580a0149818101543c6080046da1016405015882d041c800300d281440418101601040c28079441d444e000491021099020300500c0552071141d00712003248150f902503011500103200001d5024156400c9680d00e41d04556600e8500c40d06100144030a40701441080010100d0b200040421030701c2e82016080340c07040c0c4c00342c030003580c1e84030000e500c003103207400032000c0d60742d1710400181c0546010b14000d40c00516415805040141d2800821028490610124030f5582c400c02070010895041043781c0c60a01186481c900742440c507030780900094400b60001d0080c81d02c0b035030019499210f51500d0001056000304603188980d903100c48644851980c020a4003d01000841114508180318040b04690040300c603400c99a29000710352501c01200c1f404561500030070000000c29601d115a035204907e407941401003110306900d04601103036001d40c000c0e0f00412080c41d082240340000304a0030b00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 130811645 1250 130810395 130810403
    0xb0a0807031b0c0b010503030901050702240a1211070b160c0804060e030105010504020403080a0507050a0c0e071205040507090b030102040e0906010e01090b0f0d02040207020904030203090406170604 87
    0x1264440000580c050118034074411204090921522121507100503c0c14500d0700403140c0300d070130b40d0f294402c0c0341d01c82c81054042030100e041005540018104605a84c100108240c0080c0704101d00c0e12002c104c03030340200350a00010300c06c18021401c40400e4450328200c06e5110040a140071980e42d00d0508100340140001144500424814407440c01003891081441d0300c034180c030f96100c0d100c802c0600303a41040c421040c0250318020000c41d044c03d046c400c480030780b500300c03181505018030904215560307031007901c0458617402a00c000200049100a543c13000d80500d40b480782c91407911040042c880345500c078584502500300001d01c4086030b00410250140d42100a0100c0d651207004040780c06449542d0011200c2c400000400c030a403540440d0f4207040c7c0d02c209210844c1070f6a6440703800291100f5400c0315030700107140c40d6004c0f5545421b207142c00809101500c05400d114460b00082c465802c12982980581c000080c498020f25140c401c40e005450340d49004031002d202c12300c4031070b964400280028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 130812895 1250 130811645 130811657
    0xf18050714011e021903080108010e030c03040308070213060306090209060616031805180106020c0d050318010306080307030903031e0819020408060a1e0203090c04091115120a060b0a 80
    0x81440c0c2c030074403140e0010303132003031801709460a15840c00520260702441040d4040d441e001d95014440400b1044a0361650000000c500707050450300c419106500c69081264402d10031000503001d0b6001d401903800031801141c00041d02242d60041c45441d81c0010a010300c504010041105012011300405660070303018a800241401290118071030100e003504096400311424000400840b4100c4829042e41c0d0b842d400d88070804021024010554074004d40140079070030034400e415544000709112a24080140340202e5030965890019046600c0040260005400204140181070708400d0003480c10300c0c4418401d2650740d003010010172401000c0c24000340c400106011468100d825010781c0c0240c0205c60a4445508010b40302e14010210962484880c4032808048103036500d46109413481460100050718400c071035401080014a0040c4d000c5506c403100909150181d120100d8901050b81400748040e51009070b242744040311840280444246e40c1407940074052100724a0944199000c1c40c1008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 130814145 1250 130812895 130812947
    0x6010504051f1b0b09010e060105150c01060b0d09120e0d030507020409121e03111c1407030f0e010902030a0b0408040e0c0316020c0a05010e040f1805071401 69
    0x1107550040100003e103038030b80b03c25508400e2000f40c000f014083c3d89460700070485243c4840c03032540c8a1030248927444d401440140d601c020201c621008261841100000103006900c0d2034500724035401c1100844a403ea644110b801085003102e6806800129030500c1900c00c095039002a12510005030300070204500855200e00715201c940000d441c965214074442c2c10001821002800c2d9007030f000102d41a8454610700e03400040c0a4800c8101c000e082000c0d4616000700c000d01c44207440034aa803c0e4442e01d030baa036106601480721322449030042e14036540100301d080a0788408402e0715170f43e2060b805103074980040400181c0d80010040c070355903484452014295510300702840c65020f00d41c07048450b001190f00300705508207200019889604d12410031041d14004a00c00c0fa0390f848000c032106d4100c41c844105200c07030f41c01448020300381c07000184080b9071000912049004d407010014008c10805180080408002041c41101d0182500804419001039620b0000740000f100b01c00801c0825101420 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 130815395 1250 130814145 130814147
    0x1d010302130f180821130b062205060f3a060e010207060e030705070b2a060402010e0d030807030b0d022701080c0102070306020a0908070b0a020606010504051f 70
    0x80b48071150840a100c0f90b04036942d0038001c0e503e42c498446440415075801c0000303403004080c140e1600a00300e03075200070880d00290303440300c81c4000e02401d50381c1e0002c203084109480000c0d00314003c601c1c040186000ca21402e00b44284415071000c014008c1c4076401e40c6180003102c100070480c07a4402c041c5443c0072100f200c4900b8810941d0b004040c0054115400c0810720740c070582054000b4100c4d00d1068400300602d241c2d2a070071540340d01413800c00500703a4206110070001840514050f00c103110148074000010f60100105002ca6011107580c0c15040e0072030010030080d981c201d20230014400c402d456079014203849030307801400c4000040c00c4100381340d0340b0941c43d1200e85401452400f0b1650140c4800000078481c0c500003104150310b65a00d2000c5038540003c500900c000c0780755990035006800524965040d0b54800c00a9000543c007a010089920000a40c100d401c20064001780743c1d400c1c01d26501c1c035020b60000c3c02c1c102c0042c0890305000080004000c20744504150f08103861020742240303010805618 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 130816645 1250 130815395 130815401
    0x3050105030f06040803060d08040303020c15090d060e010b0d0317060a030b0a020304030909090503030f1f0506250803070f030c09051306090c11211b0111131d010302130f 75
    0x190140279490301003008000c042c0c0028424085010444a40c080505030b078204a056225030f07262290809080c055010000318140c206d2040000d0203030011a500c07104c00b0209481013464130003580040c801d800515900c04140c00b6040e00318a0640d1a00b042d02e0841d102c0c00c5901c02d0160901480c00e50000005051512400c200300150210041c10b1110f1200c909001341c1d0782e0800d8850696488942011841e03426070080040350a40d04000807030540d034074100c10400c03140c00c4000328581d0760052000012504080d40c0d85180242d108008040d00c0341820003000b0460540200703080d00f0f0520b09200901019000030105040f6503007120101c0e2300e11140c00059016240c59400600000d0500d6100c1281d90b4000c0c000ca103c014011040350300c0b00c040004c02c889004107802c900c01455004000c240ca06000000001c00c81c2c103908800802e0302c608000c3c51090b680d105442c040310000008200b4413001c0108401031080c03d003a421261401d50550300040c1907114068170400740203590740300094600035960 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 130817895 1250 130816645 130816669
    0x10207022d0303030f22050c04090c03020303070303020406021e0a0f03020a06050c09010e0303090a170f0609100c0c05060109330e0106022e0609050702070603050105030f0604080306 80
    0x50290b980341d0910449646000300700755800e46c0c6c800c404000000554144004c07814900303400000404403c0810400c0c84001d0907820350545102c4840003001c8007585081009065080c46a500141c1d91850540c00a007000c40c10390494440b0f4034a0b0310401c52600c000510001242c1c4c100d107903803c0710700940c601607140c4504000d000308118201010490008070420103010440800e8844454010010042586a1080043c0d40d6880500306600703101e494520303943d04036080b01010840c0c80c400e4104075411314004080318400c540b58000d11041e40f0b800f0b164018001d050040b070410416081c1c031565070a031a08014080c90304416565442c0170b2460f49040c41d20b4041d11803010b041c082246140c8010300d0080ca0034011400c0c000942c0c1e00008000e440001c110b20003924001c0302101d111044802500c02c0310802c0e000c2c0c000c40d07440303050100300840345118040c05056150002c01820389000c6001d030584405901003842a009400c1e0580c10500c0820007035030242c1d1012141d60340e5501ca10004040342510 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 130819145 1250 130817895 130817899
    0x30a08071d10050c0d080f0109020408030f0705150f0709090603080712200a0203011109010203030a0b01030204150c21020c010503100806090303010f05031f020705150a14010503010207022d 83
    0x25060065580ba0030249141c003805010841280681e00c800420050b445a4400e00c00c0f03cdd401000f0502d0890b031614007521540340f0a9040d21190343c8540c1c01e08004440a035202c100c10f400b0001070000302c1c1d801c482c0c40b400814031110284515891522090020300840d900603140300001042c818400344502401d50041c1c0e5099a40d01d1072000d8100304642e42c07221084124003d600c1c140ea4600d48030380400a0b02c2055405a006501c0c650b01d0b5500000a0700d40c0f011400d051580901010500d03400115000c01034504540d2021041c1a06040004240b4110b0400d81c174501c07a040441c1c0240d503800305608030b82030401c0c2030840d40d82e2580c22565010084aa024440c0c50003400b003442000640440114103c52000307102e403042e140c541c820141c031850503502c44403d40603000c2c004a01c01e103e6802a103500c60041058407003c40c400c4c1e4003400c0215007181c42124440c1e54002e1403011003130031400c0d14050700d8150021820000c280d808507074041c0d41804140999941c1e603005a900c1700300100e18510060700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 130820395 1250 130819145 130819153
    0x60414070e01020c03071a0a031b031a0a05010815030c030d030c1112040302101209080a12050402090105060c07030609030c03090602032b1d030a08071d10050c 70
    0x929002020105691801c074014050f0b20b130610329900d00001e00ba030130764214265554070b2801c001001d40c403d601110b054000d00d921000003c0c82c0c030300101600006035159460111320a00b8207074a50440c44001c0100601c18205c1c5034080c0490f90f80101c0c2280e10200010035490810400d40009281c42540070b4039640c0351040090160381298903070001100c100903a242c0c05066003d1780c010035140c40740c00c000619038000500040026151080040e10f480c0d016040a070140c42d1107034440030548520304070170b4a4a6800203650107505501102d5000c03858036654080000c2e0516038001802c401d01032059a10425008c51115103001c01404094020b56010004010030049403030050301440310001c041d008150f580d5000100140048200c0d150940b503418220300d40e0090800c160002a810107020910940d100b075210780a01c1816410f507410f59580c4e0065445910381c56004104200c020043d000300001a04904605d416070250110a0b0b10104c80c0480d460f56222411a111300a1540c000402d00c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 130821645 1250 130820395 130820401
    0x2030a06030b0606030f04030309020103020c16030b07030c0507060929040510020304050c010c05011b11010506042a030207020916030c0503070e1509041104080115050a090203060414 80
    0x2819880842203038400c0c52007900680da0039040090134081111602000040c0000150020340301c3e5011080303540c4141001420310000403840c0d0b01d09035403414041c1c60244466800e03c144608200e56540c048120300c2e05001c0c00a4800b8024464011900010552a141d55850040009800381502415032004060401d1040e0061004201e50290740c29181c1c1e00901e861100c2140c41070080b68403654200d8000c21070707806440011225089004810b031459540d402d454a80c0f1150b0f111070440da25010342e1160075403100ca440150171180042d012074071035882c21016030380f8144566401c1e001c81403510085800500102c00035000b078403ea40d0000d40c0030319008104814041c000c110380c0c200c10807a44c2d082007260300503135060782d1030710090380c196000c160a6a00d4103d01d1820703100e010003c420543c6424280481d0300041015941000320300c3c42001c0d0b005c2000c1c007001ea024458040d840381544900e504003440e000104141144601607902140d070000002003054031580c1000101d40c0c59000c0c034541ca86 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 130822895 1250 130821645 130821661
    0x150313061104060e030a1707060b09190501150801060807050906070303020a020609010903140a0e120609060c0a080a0506060910030c03060e04020a05042408060403090603020c0c13090203010203 85
    0x42d001e406100081400c4100d04909401e0002e500d0300c135a5803000005a248010300c0854082e500400d004449054035403900924503100c82000f02d002d642500403081486c490070b0401010307160142c020405010789040c8503900c841e8004207542c111816814800708684032a0001c869521442804907080b050005e252410180d140e801000c0c000c3d52542a240c2c2a2a046841c0b400e840312800c1c050009440b002c014010f1001000083c21105404c2c180342182101801c00300e00e0144d8401000100d6410035004c100c1c1c081028025558003190422841d442c09407036200107421640f000d0500e41006560318000fa19035201c01045401481001f000c8400c28a4000d0700200034100d04a00180041d081400010f40b0500d01e4940902a95000b02640f000c0c80c14007089c840246503030307402e54500780c04100900d43c008198103022806007404078040c000514107400d010f408060a54000004c1601c10021405d40b0103011511032041041180c0d07007809401001c141c24007a00f84014003035810b5200209000c003074 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 130824145 1250 130822895 130822897
    0x40f0608010905070809100e01150b07020a051002060a05150607060e2107141e1b0108190c0207050a06020c0f190603050a06090f1a030c1503130611 65
    0xb103040190901003595104012191703084c00781d0b10151075500071442c030f41c048015500144040c0c0b825200002d50110030058880204d001903100300c40c5480001647e2080d0b05081b01088003810091b20400000d140700c9100a40d5500004c1a04500641e190301141c102032514020b000301c90401803080d626046a824a0001465200c00380e409901c22000b41007150450010b0410440d420050914104182502c8817091120031807940c1103140114a1201040b001c0301400e0107010351000c1c01020000212843c80582c105001980c506000b20b107000c01444800c1004511010889810041110494501c0680c0b4200319604115405042130313501141032540007070781e12803a5000316240c516500d12502403010311148640c10041ca0f0300720725820f00045000344c1007140c02101034a00040e2155450010030201d94801d00c01030541502d900c03510210811a060019481034201c0190842c0c0ba40e441c0080c6c007a8001000110008101000040c1d00400078000404900d402c183c0034001609145401002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 130825395 1250 130824145 130824149
    0x23030114041506022a06070516060201180204020a020f0613061b0c0b0c1e030603010c03060b09010e010c05010f06150906090603020f09030a20040e0309010c02010203040f060801 78
    0x480c500b40c0d14900c0482108103007000c0300c481e500580120b403000c02c01040407020f0728250750000203802c902202c0035145c0000030400750340250701a0545c0702910001c0c50307090020354420300440e8100b60500c0360343c001c4a941400080e504580041c8e44035100101a414084840848041401207604000d005103c000c0a007045030f1080d0740400103210b2074074900381104803401e1001c0000d4401c1e0304d07890006245140352900980200411070900003c1000f403560311802c0c00c1d00e050300e1000481800440c3c01e09003e1201d0120075401d007480210b08160441c01e05c0d0042c050501d04218503804003802c264000e070408204d4540bc140240300d03e840044984001d402ca6203d020880450340b009004107501c9202800300741d44466840340d000c5c0349844802c0303019400101c010040702200b00004011a9010403001103414030401031115440d520345160541340801d981402c1c000da003010a100b0800c40d010003226041c0400b400c1080d602c4240303000403072a50049030800c41c03e80c0c070b0030100842c8080d000850f07141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 130826645 1250 130825395 130825399
    0x5010306021803030c0d0509120303041a01210206090a1701051b120604090c0e070206070f02010204030f020d0f080705011a01051615020d021602040606080108030a23030114 76
    0x60102d6030390060560368401c204e242a4140c03c10001920500e11803402400e11240c000c09807440000d003030b2051421175100b84d400701c40c054100b0501181d00c00b09001400e0040c91401040d21214900340345a14071220b40d114024843e000c0050039290715900d40120001512400c08030703031407a41c4200c2c459402042c0642e0b07400c500340705c141c8440810351841e0007251012170044d424440184c4230300051101901d2410412280c030b494064020400355180000503114400681c02414503003004400a414101d03065400011a40100003e001180da0304410404180e415211041c101e902c074140510020b05c80800204000c400103208800c1c081c0c15040001110360240710100300340900d41c01903c140c0301c2c8200b4100e244020118050124500c1d06151140d01b0f03d58030050716001e1603a24000c100c1e0702151084400140040e41c000c1581058454030028090340d0070138045da541068803486e07681c09180e00c102c0030841d840300501c03005641e1803164090703118542c2c81f240e141d58540001e41082164003602c54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 130827895 1250 130826645 130826677
    0xf06150309060b151c060b0d020d0c08070215090111040b0d0506010c0f06090f150e0f011515050705070f061106012301020a0c03050703051002040509280501030602 72
    0x980f40340b030310451900e800491080e2043c80e0022229a01380d14840e6280807880140d61500c000402914560040c03140c5c4080003001641c5a80000101d0200e401848080c03003040740240800c10102e80014511340030844400b040c0d0303110307903440851902600800071807203002a801328001030701440c1c0b070340074250264622006202e42e64800b4011a080c58400700d001d480c1c904d400034008007140c0c01e42c0c0200c80050150414000056680c0c40f032214a1005030710980680351703601100d0381301c400284500c5030020fa83c03000078003110800c41e02444a0352240d0294081c0e03803080551106d000c50181003100c681592100c00d071210b07946d4074101d15400c010306202e42000300c0d034149013a810b50a00030807021306031201d9a1044001542803108800790f900030b40481810742c441d00da0008040750a007110034004502c04e4004222480c2145072641c24540100c0c442150140180024060b6a072042801c55001d107404400c0d15030002580e48175502c2d427034004149012546808004814480f40750003e00809100c51008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 130829145 1250 130827895 130827911
    0xc0308040f0f061d090c0702090108030d060501020a0506072114060f030a050a110109030203030f19021c0807090e0f090f03040b0906130b1c05060f0d03030f0615030906 74
    0x44d1010412203d402050f10300500d4140ba5614100b0038a0ba003024031501050b0038035030701b07601043c1c6010007a040b5a11a50000c10207110b80d4205004040142c6001c0c40601140c032a00d40e101680d0341005003070282480450420300c0a102e01200f090042540e41c98024041c0e00b281681d200507801044d01d03402d020b010690143d85580c140011410b030740f194030000518007018982c41e055411951140a5410080d4441c00000076a0f0100084d121301c0340100c2180d07a4070940c8100f04e076400000011400d0070b6401c0b07a5151004a0400c100f900c2c003103c0c03503051070036440e614007500325010302c0d103034000c3c80702e040410040c05441c2c81c02240007442403003500101c50710030320b032403500590ba80a50b02c00c02000886c108840103090500e10060000d995a650841e1b040680301c2c00c1419454022802c015415000600540f90407400d40c000d031a0020000d540f02440344005c40c0204544508001b4003500f8580c81d8000e0071a42911036001c20018480840701080076000e0440083c007820f500001660802d05190741 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 130830395 1250 130829145 130829147
    0x4060f0806010c0b060402090d050312070309021302030603150f0f0709140d020f090708041e0803180f071503050f0114011209050318090a0b090a02070c0308040f0f06 73
    0x4000d00807441611982030200c5543d03501c40d280800200348940058003888100c2c044c0d214441045015407082010b1a01c0e2944484401341001000700044205400c28840c07401503150031f00035500c5c0c003508000260740ea0342d038080842e160104007600c1d5031039244a1010000b50460b40705144d40100300040f00b0003940d881c1c40c4011902c89030703140580b03041282810305a40700d500e00821140d0315184050b144550007042c0383c00041802c401107400c0c1c400301d4400010442000213000880101c4001c56080303120450f01ca8541800b9804000c00c4010205072130b03810101038034001c1040060301d1098008484006454103110740b200141c42440c3c030003103401c000100383d070010300d035034aa4140d5804614041c003002c0004011117010b1801540c00404607a94841480407030420320013443c00341e54070082c2628070032428040c401a00001440c0c43c0c004d9107007402c030307040030340e1008403090308180c51200160b21040ea03410700485001050340300a00c5001e000400182c2c0d40c480301e0b504070494980e0f0040c070031101d5135260 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 130831645 1250 130830395 130830407
    0x605030c0f0603011203020f03040321021506090403050c0717010b03030c0a030503040c0b0a05071101080402031b060d0603120801150f0c1707110f100504050409240204060f 76
    0x8500c2e4000300a0006011418120825428aa0292046492401a103805541140d02a80065814032503586180c441540c04684915030806240f0041801d000407035440c60044074050000740c130a00012020400f4540306806903413291900c0416602015950140c40142d106888031005040d401d00510700c1c0e0030303d00442550302265005020300101c02244ea01101e00303500003401110807110b1a00041010034800f0043c1c9140c80c540d864059440c201c50a08800f01c1081c14a107604204500c1c08100040e103001c9010540700d50510040ca590f44c1510340000d1441c028010070a603007070b01d070800010a00c248205602d01c1c1d620b054641c40b5003641c0359038944441c02e840d0121400442c80000d52040b8072031090a50701c0c40ca80c050b500340102008140840d624561100358256807409011500305181d02d0413087d12848600219041004c0d181400c8014100d4000d501c540c44c401c1c0d41e00d40c0302c0c4041c4000030540100074025100340141300c48098000c400250040c0c055500041d42022464564070701600c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 130832895 1250 130831645 130831669
    0x1a04060f030807080a03090803040b040c05060301060f0c03030e0f15090102030403021b0f090f160f0e010c05010b06041e0503030301120b0a1d0f010f060f0501050304060b130605030c 80
    0x540841c0c6400780130b4a5200380340d40b200940204059a4034040c3c00400d200d04042c44c000c13071040304907000508041c206450540c2841d04450b1240d1000c0004001654000c1007440e103400d07041c01c146c514408503040a400801041c200281c5501901d00146280c05000c034143d030502e00008048003070b585800c04942d080340401c480050150780f089600e0502d80841d00d41c4900c9144005040403803410480001c41c0c09603806035240c02c410700070a000d100350041d019181244c8001c0c0e510700380142c450b085a0091000c4a2505000e040c0a074004202d410300c0707400c3d0007000c441040030b01941c0c2d445503030b00049400040000317401910111030350b802013914a008400c07a412985010b0400003a211541c940d051084005402026980c0c0e690303424002d020402d0040409891401c805800164014640d013400e41da011026007004030300c0c0c560144040034204640e4000d60b0303020310b0001d4407544c40e07152240043c004440b540368001031071100c4c1f00b200d6880d0341010040c1e640c207400741c40e00e04140e0002c0c00300c412041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 130834145 1250 130832895 130832903
    0x90908030f0414010c0509090703090b071b1407030311030a05030109050603030c010603050c10020601030c15051219060e0403140a020109080318120408072105011a04060f03 76
    0xc00201d50100860110160400e0103a41d03080e00c80a1000005400c64032101c85d00c0b8049180032800c0f00c0c06103410610725078009800d080c14803005d00e0a641d25055090000c00007014001403001c1d07191451440360201a00d0f0360310154029208140208099440c6080d2008a00003503201c0c0e22040f07810804400e8402d90f1041d5100d01b411030342494a04000f51a0080940c0d405110a03c000b4040c0902400703540010360003800500100416181071002044021420303d095601c5540100300241803034804804492021011a9240c854040122190302c11107180074201030170304007480000b207228091442d61009182c42080034035030341c8406000c030f40300231280940800d420aa52010144241c8000d0010a203a0b00c00020342c01c030342ea0745c0c25407147c0059448540c206058103d084000c1010006c500c960100c816100d404c052502c0315160f9100c0c06401100005441081800c003580e030810010710f0b00d5a800750081c4440240c2c50283c20114050b842d0a030b1089003080030000318a4070a0200c0800e41c4d0300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 130835395 1250 130834145 130834147
    0x70e010501300216200301020c070306020c0a0203070f090f0516030e0309060d14010504180609021c060507020723040504020d06090b190203150f0312040801020a0207090908 76
    0x411109550a6031a8104442d1064080011505000d0503d2248000302c0c4902e0400c05019034040c00c0343d01060283c102c082c041d80c410008080d650000240d400b0880b984504090780e602c050b550460b040c0801d00d40c00942503c10440042200c13054034107841c06445e030708082000000e45000e80d980545da010740e08103240c0fa07100070905485610a0f008042c2c40d90465046a18180d02071001c26484c3c0e000d410040820b680e903122030290340c502151014010541210248460103403d05041212034144d030005192907a03905c407083c1191100c102810800140b0301310030004442c00d04106010300000c0f00c04000500445001103000000000e4001140128494000c03a543c0320300140001060090300680e484000d2402103030001e00180501c1040703620a2090302c4141c1410100002007031007000310100300500600410070309040381c1c60009000c0c40d0490ba4100d603916004086800c3c000c211411041041000402180b02c1c841500180309250682e400c551034181e55020311000c03551031450060202034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 130836645 1250 130835395 130835447
    0x60807020a0f0f02040905030f13051002070b18030706030f140115140d020f0c0f0606061207051209072c04061509140a0506040b101b0b09070e010501 66
    0x51900c1c00700c1d12a0384050030004060b9210340b20340f0302d140c00000070450048270001d4042d00e0241b980c05000d00801c001c3e584c003044403a1950300a0744540e114001d5100d032203404101b005403c0702111029000e49800f4041d208c0f00d07601c811004001d40010441c03804940d0402c0d986d4000301c85202041740c1203580c08400380b00c1244440308112524006d440c0601e5040100780007034480c030319071403005000458400140c3d0391340d040804802820304d10381c9003200800d50084c0c42040055103030002121191038801074207049650b030303840c01900c09001e200c1c0b10b01c100b0000502000500306000a0400546540c024250700402001d040c011039068000006980c200d6030740c010400141036a041450034a151640541881b5114801e1400b00c6c0c40800b440421800c0c0741082c010b60040304d10a8503044a4190b03800d215a50985011450141d60181e000341005a00145c4084c800400c1c03583d92142035000d001864542440e44540d03079100c0c900d0080385845aa83c000024556014a502c141d500c5403808906883e0306d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 130837895 1250 130836645 130836653
    0x9020a0e1009020d060302031606020708070b04120c0312120e0111090f1c0506150607050307033002030906090a050a141501090509060105040614040b0d02040213060807020a0f 77
    0x14004c00c0b0521103007a201c802c08030043c1e83c1402038a075003400d01180c41281600d0014000d15291550303104507034980085109005240c03101d022507050740e1001c211120200c032039140c10140c41400d548040c210320440c0300c0c800340503607021600c00b280013000e80301804010b4004030801d080380d10a0000d605960420001420035080001003801146c3c0004c020f11080d10342c42d22000c0c1c0c0352000080486858008d0420070a48600c100e4050098a00c107031f443c035042007a10342e0791594910841001405000d0740054002d182010a140b1078540e00d080450b1030b00200709403160801a40055074030803080d00a05000688a00d000140420100d4100c002480c0c1a1a10340722601c964111090004403070143c039802c41d410f07500c00b1103194020015443e00080d1480d00310305a904026068118a100700d041000811203d94140c200f27000744081146e0010310001800d00090110801c034600a410500100729060401f40c3c8255920032251240ca500100f41d442c014103e85401c08240d00034901e2a40d40601c43c08a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 130839145 1250 130837895 130837897
    0x4080a0605040c03022101050709181a060a03150e360607090e0601020a1709040204030210030209031b0607120e090108011d030c060f060607060e0109020a0e100902 72
    0x443d0050301e0080c950360702d03034011403c240045400f00c0c0300040045105c81c0c40036070174458141c5c0a84940b80c149501030400c0c95010840a0340d95a88082644580c01d0440031902541541c041d502c0007003090365a503040d500b02a0251103003400c142c01c84000118001480b804075220306214681079401006611503171000e590503004001c030041c80360b1200c070401d242c0c5118100700450003020952286d944032490188500003040000300210f04540200300110006030074402c3c2d0104481c99112a945c071100f4003004240207018075400650f116149111403603060744c047c3c2c000e06142c5015070668441040c06820340f5504141300514a801010030050200030440b014141d00ea09e18081c5032900071102c0c01400600c59840c00c2c1c0080c1d00f2650f46140205811260040740300c600e410380d102450801c02144002500c80d140108900840c07045c0600080160f41c800b400c8442d55a07101008009003500d003020280205040c0200300e001d2050f040c0c0204400f02c0c1c001d011441030031003010140d005804c6c001c6000107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 130840395 1250 130839145 130839151
    0x5060f0c240a0c050a0c020111160b0a080f090705041509090c080c030c060d05040507050d0506010e07031404020f0a1d061801030b01290c010c020f010204080a0605 72
    0x52030280c14481141c1940c00050001c00010808141260381400c0300000203c820081800c800d0210400c2082c0507113400c0010101032580900b06900c0c4076100455240c2091200000e20020000d02080440d60b41c160402604003a83d5940d101b050075540c1a0702054404000d81701e0f5041580171540c108614600b5800004003000d4070000700443d50381d1002200107032503000c6c4085400b440f02d443c003448045001c11000c980c80038118010401203d400020a400d845074074080c0c017100d03458000040600c01c081000e10014100a0880098000d00c0c0c1446510744030280252200301204402048000f8030a00030070010441040c040c5c05140c030b5940c01c200c2d0030006030002c2c0e9005002481c001400040304265840b41c184920000c00b0a850300c1000c21882000ba96448000400c41900500204504c0e4140c075042d500d0b08008113040340303007049090907001207d0381402410400086d818a0000381900102d004e0403e5808850b1201c40580700c1601340e009601a20a00e90303c07103540600402c10603008160 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 130841645 1250 130840395 130840417
    0x20a090911090403020a050c0907050418090f080a030608070e1f08120d140903030601080a1506030e0d140a030f02160605040311010606080103020609030309180603120405060f 77
    0x1504101d10021821261007110190f026030000026a03080c407200f0f1002407940202141c105403549421040a04103002d14090603440c0a0141c02208403c074081d4480c103240ca40001642e050a101842d04550a0740050f08140009041c5600043c4d9580e00003400001d542c41c4520044080e0789811103201e10b000165080c0030142c0446500240c000c03414000c00c2001004c09902d256140c1545001000380d480c1c900001c642608403108000344103c011068982001c0c091a1040c1c66488446180000c1d10203a040020b25046a22001444540651010700f040004809842e1f5081c0021700c1a81d00164007040700030341080402070301035a01d11940c0084c6800500b0740006045c03010f107004070200c0b401303c070501701c82c015070311010b0000341034100114614507140306c0000d0040e1418104004d00a480621000380549008101030030165003d100b95a1043d80c05000d20641001860320b100703419070103443c901d01070f00404500c0d2030188041001c4900381d90000d000e4034a4403012140d102e025600442400c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 130842895 1250 130841645 130841663
    0xf060305090615210708010b03030f09010309170c06040b09010e06040b07051b010605090c040602030a12020c03030f0105041109090c090409120c02040b0108070f0c05030c0d03020c061003020a0909 86
    0x30144c000d125211807600e1a8420003400054280000b15003115180c0031901e10070361052103004240d01e000811910405400c0c030300414403840314a0405444608200c002083c2280800d1042e008540040c0301840b45014071902c000d01d8489000880c00c0710000440000a504500002004105042040c98100c041da01d0281d2500a4480300406a18001c12b0744203080d0351202030800c018035000342c42d41e4001c0100035070709161618000019689108000d820703000c0c00b4181c0c015030b04010080e81075491042440c2d00366503070ba29110340c0c8415082002d000c0c00d0311407480c040ca240301a10481003617880e0b1b080003070141300700c544504038060307201c0d00415005036100d0749804410b00001d820101c4080e03803501588540587c00101c0c81040203035071b4809151410400040100010642d110083d24000310190401e004901c04506019065101c2d40502004074420003003c1c3c4000d40d0306600030481003581c081910603d0319840e20900a0318040c1c40081e41c001481c00b014048444290b0150201074481c440c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 130844145 1250 130842895 130842919
    0xf09100b0a02010509060105060c0304030b22140124061b060e160506070c0504020702041506091a0403020303091c02031219080906130f06020301030b010f060305090615 74
    0x25401070340c0003554140040c0d44840500c40d00b0503007000b0140c0505411500e090522811102c004d50340d0066102c060051405030700450b00d08500c0c8141d00410031684216254405d12034100320402c2c0d180f4a044000961a003075503040020110800e14003112a081ca481c0d0199282c15030490354030000c142c0741c0081401044244000500f03d00c10004420041c50141c4040c80148500102c00c0e00c1692066014a00812030140044c40c6603c1a401342c500444006032a04140c1c000324009141281c840c100d4802c030102c011412300d42018049040710304656090010220610000c20540510302c0001d4041d80f09200341a103510307000369620824241c0700c45191f03451200307400080c6040c0c10780441c00c5100e0030029244a1807140003030103070310100090620284606281c00c1141c0d49a1004201c04007840404041c0d000b000010441265100c0e0001019902e03940c690601d400000d400b0312400d41d2420284400003041402400b4241c0304242d40c01c0030b001c6995404001350810900803410f03d901145c11400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 130845395 1250 130844145 130844159
    0x50702030901210f060302090705031006110309030d030204090e0a0f03080402060c0d03090b0a05160e0a030605010b041712030103030e060f0a0c1103010b0f150c030a02150a06050f0910 81
    0x113149514400d804c00440c54a1560041c0100c07050007816410070098108104091550440c8280c002c41c1d909280c01900c0049100925085014586609034540181a9500050307641a005031050342c0c4d90a400b04214020f120a2956038070107800e006116402c08a0030f10003190144c60203c0e84076002502c1e45240c205083d280500b000e991210b03c01c0130907640d0100c881803110011000707620418481c8100f084d4100310005480040032444204200110803c1c008869200c001c0d8a00003507600c01c03401d0003d941c480f00b05001582003030180802d507076080008514075050000701045420300c05980b03545180d0031920110f0390b03040380320b04c41c42d0010010403219a80ca1101e20040c100b80365607541c1c080c541001ca180100b43c4150300d48049100340e052846240441d515901e076451118011203034000240c1000c404141d45000d103a83c00310050002240c89141c0700e40104081c0c00609204268000c582e49441952080310400d000b183d0708001680710580040c2003805881d034214070541408d10100d0740c4e0351b40d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 130846645 1250 130845395 130845401
    0x50c030c010204030308011a07020d030302090a091b08010b03150103060308070b040c0f1d061c030c05070828020301061e08070905150105031302031903020606030105070203090121 79
    0x80c10005a50005041060562094400e03001d40496070710500302d10000407880310140620780c03001e0711482d580481c0804142c020383c11140320750b9019000d8081c9035a1000001c004003d840358100b4000d0383c0c0c0551240f214881c48189060b100b407052254116120401e0001d030549003006000c0c18150356200100120740c84001a000985c41a014000145000d1070501a1018194801c2000340b404010a0101d40011290010b10017140d981411042e030320300e8002110040c42ca045e501e942d910515258080c140d01030124060180900100c4145a90700c42c0c500fa40e50540110f1a600700340328078a103500c04c42c0c80c190604c156500050001c1069501c8082000d181c0145002c011004420801c080140d06402c0c01003038020241a2001c01031881c016841402c8103522102c21410400c0005c0000c240942e080001d620103500038044074102140c0c030f0100c0e5620380e0410016005449000c0000300c43d46014006c0e24400c01c3c1c140e010310b0402c1c80600042d240100d200d044054801403054011844284500c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 130847895 1250 130846645 130846657
    0xf091206020301170708060c16080711031902031207060213060206090d0206010b030c2802010506040b0f030a060f0618060501140304031e27050f10140a050c03 70
    0x128016543d52401d41611050040d10700c01c3c0101d03400440003000000c801241c115030000607084826524a0310581070201c1c10b280b201b0013050780b600800e42c0001d20601d03081c1040c41c000d054040396003580310300034a10244020420300135410360100300c2c6200300b40b04040151a800d071003050050306018220004102032203068100c980103a1002c000c000c00c0c3d0008000456640510340040d04d07107941032000407201d601c0010030a01c01c021000482d2003111060207008a4506145803140ba9411498040207000e000c090710300501c02c60400c4500051450040b50b101e02510f0014000d0602181565400005d00021521500c2d0f83c0d0344d0750700003e001403610320710300d0390090b01c071500041e1203003002c001500d11500c1960a4000140603c100400079401018485911206a9800b031140390004011925034822102c00c00a00e04060380904080300208404d4081e03030411143e00158949102c103101c6900001480c4900040010600c1d0020038124801480d15101038030f403103807514039000199803a540c400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 130849145 1250 130847895 130847903
    0x60109090609050d1d1905040c020c0a0b22051c0303021303050705090f0c16062310230402130e09060405010c0306050f060d0f0e0a050105010506090a060f0912 70
    0x345500c941001c1d8045d907880c0005134225040060105a4480c18440d1401401401d026558030900301d18002e008200b40d141d8402c0080406101c2900d0743e1708103d068124504441d600f00b001040c04140c01128111942907410180450080340b0291070520894040a0f03030039424194200103803046034040c280d80001560281008040003450300703061111a40c1e000b4046031030350b4025024403c00783d2452045a036184502c0c445804415a40d05148004003d00001900c3c2c1041440a0214038030000003070500c10b00301e19070b011241c190794003088031903240c80c802c2e078a408001000c0300e8032903403405501504d0b01803190a202d40c0c2c990346074030380c02c10340038001c1d110755680b9400300d4100b1041001c00d00815000910358030b0140041c07843c00c1d011500b152202d24442e0b116400116400c950318000c0c1d0300c01040301c4000c030002d100d1911880d141c070b501c2e21400a419540341d4200b0001091074104001201d401e500c0c0541441c01403403405000700c0710320141c031401808211200354002000211b0900c8401e0144c02 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 130850395 1250 130849145 130849157
    0x140303070918051608282702210a17071b0b09310c1b1509080708030a0b040501080f070905090a0f110a0506030405060109090609050d 59
    0x74019841044564424108603007403c020410007a41d101c0644440c02091078100948240c4032051b4250704800703101c00f01200c00704408281c0c030365840507070080c034030000c0160031b458511650301560503152825004040c0d0040102e41c124040b5210f00f013003030240109040240c402c04040303541d80c60a00d8a07401085901e030310380400c01c681403040645c0503102a00200c0c1584ea51680b401092501d02d0041520041c130603101c14540581e40201c03004840c0c0144d2140d0035224000011002000040038400315406c0059460b900d8103048170b0b4164500c802039a04107001454441008858201a014035902220a18424000000010b05c0c0c18043c502030710804102141d000040300501c0110b410580c000e072120b41c4840d9a54100d58408500b5100f62420305001103616610504014034281001e800181201614540300302070008045803400c02c0102212299280350b0745408001c4135010982d40a44540c015200403c00c41d1025403000800510500000c00c0c0b4201c0780c1c4400303080200140030540800c107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 130851645 1250 130850395 130850399
    0xc0807181e0905010f06020a15021207020d0206010f050f0d0302010204051503061503040b070e0f0a06030212150102030a1107050904060c17070207140a0e04140f0109020603060103091403030709 85
    0x4583d026507400752025019460401d460540000c0d030b41c0103c42d0001c0c00032140d440c400e0a03001d4051701144c81e1442c18000d0344142d0304103903000955035090300e00d0340d40050140c1ca00100343c0f4001004100c040720307802030411081044440800801d4407401404405541d0300300400141c0b41c881c00401d8400030f007030045494580c0340460600101e841148800e4800e404100304000c00104c0c1e010100d0703040445454024009000c1e1f001040111114500195100d8a640303000141c03d68150000c1401011403214038499440c0d20000107450000028498056041842205104d0b44600b040d80c8074022804100c950b0150fa9070049000300c4419074003030b01c4240e00c400c003c50080341c0010710307007124069041c041200c510701880000d440d0142d40c0100306a241840c05801c90b1551a032220a0142c007001400621504080c03900d100100e48892481015000da038000c0102e2030310600c1640d41e01500502881d1859842c80700443c01019100021603040c2041c007001040070390200003075885948941c1301c5000d0340d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 130852895 1250 130851645 130851659
    0xb3d0f09061b0b0603011e0207051e0a0f03140f04050405060306040c150507080d0621030f08070309050d020303150607080904090305072f03010c0807181e 68
    0xc0400d4002406101c0a90b49410085807091010040d040d00007145621580300c420001c2e024110722030503200401c1245611086034045a03005240305403191040342c010101030401104a00840031800c07005820000926002c5083e4020880d0668401c0c580b071ba0f200250715080c41e0b45500000010091450040390030f1120703061510429030401c0b03080700103208628040c2d8502150f640035008400c154000c048071654a01d00450655410903801690310380c440c00c01000c0d907070080600e0702c21603688079040340710171100f010386d600b42c6040030b0780560303503540c241e010000103459444000d0803034020550b881850502040c010b0083c8009128541e010f5942e0b41000b01c172000e5500c0855100500c6240d0400c0f9100004945104841c40c41e50252404134150b64503050540d418052100c018255400220045000e1503100000c0c000701c80c080c0b208000001c0e6101c051500b00c074402c44080d4003154440700403881d0180100004a80c00c01451a55001c90751a001c0806101c485442881e0240c810f200042c0144 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 130854145 1250 130852895 130852907
    0x8010614040c020c0306060411040305070311030106050d11040213081516050903030904090501060506031602061e0703050603101a0f01051606020a0e1002030d0b01030b3d0f 76
    0x2d2580c3d00c000c0000742c150100003034031400c01808945c0f18076a0b8488039040140303c5400c2d02e000350303000026580c410340e5a00340840310040c20b60030340d80f00707529007900030034039183c0b290451a459400c204207003982c89140003803100a5124001c06020b01048501c006881c160800c1140c21507410000101e02c3c6003401d148a02034958104161414004140f0520540f610b0000a5401c0004100c0e408644451141007050041903a40c11680e003080c0c00204000740e9089c40071081108400941c07c44009940d64203901203c40d45554543c40240d0108003c2105241721f40c01040e0010b8004041c0c1d503610310000083c4c0d00301c55040741210f8120031800000c3d030701464291800d0320300aa0a0a00f1842e01d0203c1c040325194440081004040c2f45e4007241c0d1110880c80380d0b0038010000406030030804144111075010b07640f90801c034529803e013030401c54110b2895201c0d0080c54034946000d0320041040c0e1881c08030001c00a00702400c4518204481c9503c40308141c80780c0c1c5031100707a5030f0351510701c0c6a601c1400000c008c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 130855395 1250 130854145 130854161
    0xc0924090906040b151e13140301020405010c0602030603070b0d0603032a14070302030102070807110a14060d020c0a060b01080108060708070813050a031206080105090303011e0801061404 82
    0x2c5145810704400f0551500805c1140c0c0c286041c941e150b50710b0311407030540b03c00c90950690080082c0c2c0030666aa5160740380d07010b03c050781c00040050301c40c044018105400c1c1d00c55405140d002520410b200800184d654001e55003208009091b0390404c2d450761080082c039000030420995903920b5180804c00d15400a415505141c000d0301980c003001c1103c407031100491302507880203280c0080d00311030108028050181c0c2c0055a0300400965403980b0f00d0401030025000000107840403c90070080a24034540380380c40d00100c031038003c14400c610201104006130398103c1410b00c42002d070200482080d240f800d0055581181c41403030300045001c64040010300e0308105801455440c0d0000040c020816042502644e101c0c1c400d150001d881c1c2d03100358003085491400384008001c2d1044405510030142c2020002c0010041400e0030001155100d46035400d80380259080200f64004000501203265007030f2581040904941002e2805070b07640d02c04500710b6142c1d0f8010b0302e100c00640e41203403ca00d0a4002c0d040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 130856645 1250 130855395 130855399
    0xd05040c0510090b07030503061203030109050a0606080412050904020702060d0501030614040804030215090303070b01140607020d080307050f07030c06110901080f10080d0801140405010303080c0924090906 90
    0x140c003411305504400b00d03c94000d024003400804400108180c4e90008201b00806240b800d90b81c89580d00d21203040a00b8064840c080c0c01c030309242c4046105440350b881c40c2d1095800c400310406860310140f090326a980310815a64216800b0468000543c41d07200060112040d10200011150f1650502604a80d03d0030521113144455005110204035400140c9098940440b5642c4282c044211440b0301e610550302a66054000414004240604100068103e5035409040c0231031050000c1081b07624414071400a40c06000c145040c03000c2080c0d040a03603802a80c82c14594644040640400348a4024520171030028840c0346001040041038010840180207100000341000604c20010f004400c006000210300500c0c0000614014110300c0000010312000c41940d01e03200440c0001420810240510310000400c8401c80440781020710031681247e8040c0c1c0c540c1c01d80e40303880c0482c80c40b5900020120341c5c03000c0c03488500f0b101b1300003002101c0000c400e55441e465a0740b601c00140300c42d04d43d000f07021034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 130857895 1250 130856645 130856657
    0x30d0b04090c150c02120109020111030a020d05030c0d0204030c080d080f0604050901140915060a0303140d0905070608010314070e010909020a150503060102060a0e0a060b0103020d05040c0510 84
    0x1c0300260390444804295042029000b103d80607100003250b69120010b4040e500103190702c0a460041410343c8070100307040c002c0c0e030764454034408041d01c00d5582c030401e814040180d0107029a01401849034001d990003111250246107070a4071192090b091b84c0042d0825124020251400c2007680c0c0d0030480c0a0091610f4100002c1c0e40c54104180c0b03915120040c00c1c02d02032511000054130005080d03200a610054494204c03a50b8184807850a56414601c80f80325003028644d0701195072b9103418800707417084a0707040d0b981c209021030070341024006821a29202c48038507280e0703110b440041e4081c00303000058050340c1c0c4d83c00d46035071550a044a101044840c02e20300e6404c0302200b031000404180640e81901e030700c045c0110301000d0358070200d003000c9507070750001c000c2c2e008070b040700784403954040300660280500760b00704c038590b0b1100184e0508859640c4800c0301c081d440011084009160b5030050170b00b4800505005080200f4804d564068403021201106c0d80c00310100140460324000d9124415071103549400c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 130859145 1250 130857895 130857911
    0x1061710050d0503070b04061d0307020a0603110d060902030f01120209011e18050603060610081504021902070312090308030a0b03240a1d0d11010f060602030d0b04 72
    0x5031454003180145802030140698510034014204200c1d02025030042120449217000d0a0050050650340382c108218240201c04004031000013040d588a2034000b844e01007624034100c0c0a4009000fa0104c2c80c500500034809252884d689100c0c000040071035a1026a4900e003038540361159960581041c0c608840e0641d909002d625085082c5041d04e61092059504914900070105100344c0d80e4018002a800800074214038401c40e00040d0180c1800e9003104d0642d20746204100340c4035152400040010305000000d18040c0d1010080c0e001000041e00051a2150b40081600c100750714008a4000d40e22840d001c0003005016810041601c1c070900d41825a2030655039042c282c6d12000d4180d5000c2d0303446d01281c2c0b44e16982071154090745494041c042521000303042140900c003e0031174410740d10607d08800c8000010100c01c0c000c1e4061791783c3c0e000d0000d0000c0094141c0703141c2d45600c100582ca41d0707107020000c8555024442c40015003481d03001591502400a944c800380c40606076020b026604144036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 130860395 1250 130859145 130859161
    0x9050706050712030e01060b0c010902030606040209220902060a0f020f03031009020304020f031606230708071401112a06010b0c010e0318040e01060506030a02070302010e0a030305010617 82
    0xc41c000c00d080300c0c40d000c05c007001940002409080f450700070000d156400504075140c800150312580c81180f0990540304a65550000c200481c02004000b0307030050600802900010192440088001243c0c0c0f40007403165000c1c1c01042c0d60f41c21004400f00440c0c0f00095943c0d10503010400d49488a2054005501e10324042169003203120079445080c18154000c004117007190741d036503095120f200000d002c4441c5201c403072644070083c800c40d201d0400452141c035452408040a070040e004403240c28414503142205079500c1d030b500e962100c08c050b01c140191a145841da02420b01a030140c8014803440507441e4141c00540c0780340d40349807002a11005480c1c0008120198000ca0303041d0440d201e10000030388450b1403181040c09032591101c10f00c1d0f24000090744001240c0400545100b8680c103072401c00c182d2030310a0701e4a0881e02180035256010b84c0900000d03000d50200d07001030050350303c00d10022421a02640c4464508540c081c02100400d441b50014000c0b51780c844003140303400003e003119181030308000f40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 130861645 1250 130860395 130860413
    0x100902010207050f0a0e040317070e010e1c0606091b02070807170307140604060c051c0e030409060b0a11060c0a0c08120a06030606050a0311120a0203060901090507060507 75
    0x85101e014140600c1c00c003130741da075910111100810f084015681070b480c0c07a00c2c1c010110310820b0f05944407201401c01160485108801d0600c0c40340d01030f101c1079031b9124510100040003500b405c1c583c3c5410400c4600100240880c020503000b402000000708404108070035000f001c05032202d001c41154040e00081100000028514003103c0a0840c882031300071854003828210b104c0c0c1040904160035100403c1000b60b0f0000340580701c0d40c09404100328804030120704607560310405005090405c40d07014003003030044055100100500444046920b0300d9038624642c4c05070b5084d6801100440402315040e0200341d005012168444600d1000d000c1070b1810580504060103103c4074042000104101e01c1c08100c1010308844c8072079100012000b03c2d1030000f1929028040600040f0741142c20400c0000c1c540c100540a00150381e400072640c00050381701d04c144400024040da1410003446500284005070300c1c203200e203138020200c0f040041040a03050900c20710f0003081c1e03408581000001c12088010811140d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 130862895 1250 130861645 130861649
    0x603040b220311210910020f010606020a06050603060402090705090607020901030506040210050415030f090f0f051902130c0908122203020114030705040b0706050108100902010207 79
    0x14844249529144032540505809007074107040d0110418040060680255a89650460441c2140c074a052072030f00c550031031591a0341c40b0402400900040000340781c10f0010880e0b20344588121061540d200100c1408c2d1030f4a0b500c0300c40942c000480200c00e012090051991010058000344071a080545c0441c035040c0c0c000709034108004001c280596103aa4450480d6942e640080210000b035841e818035584401055508a1040a02e03520f415485c50281007070b1822241c2c10f4174100701003043d500056000d42050340ca243d0796581c0c0c0d032032a980010511000072244c18041d001540c8007400914045240c00c481450301032201107003e400000503034a900142d1410901c07080d001c58491600c5505592030042600201158050708105d52010340d07521000d000d20054010b005000e041c401e091001c4062040c2c0170203170001e1029003540c40701c1d00e034400003160040e18914000c1d180607903482d6044c24a030040e0100b00e584035201c400401111808100701c018031a82401c1c2000003480617070000c0e503221428 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 130864145 1250 130862895 130862903
    0x804030c0804091d01050f090c06090a0306022b02040521010912030e070501030b13020307090e10062a060c0905180105031501060f050315040c0906021902060304 71
    0xc0e21480c42041a14000c1d580100b03103c00040c00300b4040801881510803140c407469216611b00f000007a00400a29120b50184100c003010b8010308d803850301800500da0200d02400d4000b1010300000001a02e01d1000701005410341d1034583c29055039072901d985150b00c110616051740d006201c00d00540e80c403120300000741c000440900042d107201d1301c070560161003924000351000710100d0180050640580012010228031000d4840494441005608a8404200f910b40100c05a900c401e004d41e4664001c5030071881c01e080404800c0d60341c040901c440d01041f100c1c071072860480b840c104492a04610680d034a16440340101d107100b10f00c034101c5600020348000c0648040e864090501e03880e07009217042000f52402401000d15a0303820402d1300150700003881014001e02c00c407139146076550494082e0a059031165038402103110f040c440115181d80010b0109650254030003030b140802d0b95148034444026010303440d2008242d140070360103070030400c5040310103440c1c03d003a0f4000703801a510b5004907030348a40c1c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 130865395 1250 130864145 130864157
    0xe18090a02331207081b031509010b07030c0210170403051905121b040b0d090c0603060602030a080901060f060c03021002041a0304110402040b120c27150d0e0f030a080403 75
    0x140c107006c0e054020160840d40ca06200000138403c03c40761071104100000800c3d0340e800010b03603079600180b05a12a4550140010700c4e03003041000180742003003964810000034036090a86c41142d02d00d80240e0b241c01d513411800b00300c000492031042042d9010002a4109a0030024140114140e01081017200109040b02c1c0400d190021074450107000107441c050000166150b44a00440c02035100402c4d10340c9081c2c0c0c0c039002d071402c005a01031080c056001520388680c09503043c00a1410191030064000d00b0300700b529500c500011601031411078010004100c07aa44070031024800d424080e051419864001d010f80f40100f00c140230f101410b0604510402d10020344641d41e5503035050082783c256200142e654028000a000201c40b80040060640e82142e090396145544502002107042d1141c0f16100e41d4003d02040003a01e241410700003d07002002c060030414032440304034400d0b02541c1c440c41c02101e40c0e44d5506c0d80c5602001003040040c17401c4035a41c0085150150302003000d400000c0040c001820004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 130866645 1250 130865395 130865401
    0xa030e03041a0c010e030f0403050c030c010f140c030d0c08090114010501050703050c0106030c030219030c090209040f1b1b0206070602030903040b0c0303010e070e18090a0233120708 80
    0xb0003584540d10301040201070b0b030b8440c1f030b91031408415503000788021f481c5840f030200c5103a00b5240c0400c0c0c10413107800503102d2102d03118107080155600e009850740030503103640a12007101a56400e0004000d690300000303002400405000004d08100c1020302013100980c035081302c0544c899002a11207055540900300385807514402d24044500784542c0d803c0d00d03800e5081c400000108880b0051403000c0d64403c503003a00d03664021580c0ca00d0810164807001e482c00c0d104900c100046140c82c0d0040003580c0003c3e20120b0110058030448043c1d4100d00e925100301a940c910241d03019502c401140800d01580d049004407a4a03a00002c174980600007000c2c1c40642d0001c00300d00146010030841e0010010b85032416141c081c04206a80c803a0000d10a0080e1840c44400092600307100b1031101060341d400501c0b84180140540705811030000050504041e40308076401040580d5071480b103000301c41c50400c82c0540d022681c029402c1040189480702024810501c003801c15080800705069019604e441c1a004551b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 130867895 1250 130866645 130866667
    0x10e040f0b0301110301030627030315050607030e03060c0f091315030f1b0503210f1c0b01021f050601050403150209100f05070f0c05030706050a030e03041a 69
    0x300801c500300d607142d031034868400910507400d40514126801058100070102c0e0340c0103545448000750303c030841555003a66040b00040e00a42c030140e4a800f40c4021106225102c1020402e6170740800c9050780401c41444019903036180420101d039010920b00c0d0914106103c2d040110a01d001d4140c09a100d0b08003c01049400a46540800b4642d44400e90340c01d40d90741d507410720701400d859881c410303910164030818203002140700004003021a0001b5009080c200c02d4039008110b128203001003481411810090f52381c185008902400503844c84000c0a800d41206019080c100c400c500c0701141550001c008415801411040112000c802c19402151540c0c1c0c105c0100c4075440340c1c2e00014010003103c06a9402c081155002e4200c219041e20302103891607030540c0c29100e8008601000700001c40402c104000916180c0c42091301c20301c100315031402a43c480000030300b0b020640d04101c00041c4041880483c1c69414000c400e41e03404004051445c103400c0034005d20700c0c1910003000c1c1c2038098002800804407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 130869145 1250 130867895 130867901
    0x709021608030708100618030303020c1510290f07030e04021204020111070b0f0f0f0c0f070614190203120103050619050c0a081e04060c030e0309010e040f 68
    0x141d80c007240050362450301c0d000c0a0061901680d2540300a01034400200781c41d0300403543c0590301845111350740c02e0380e85141d8048010390b0101c051542503004075100702800448041400340210500001c84440c6800d044842d004030310030400d00c405071416503108510700389410b003c480b83c0e00402801943e85080b641415500c1c070860f0200c3c6da80040c400200d0a10701d503552132050380158400da9030171500c4007940200d20f03034400c1c0034041c3c0c040c1c40c3d03010491101c003140344030010028407040200d440d050804c42e0002070303c55040b11003400d9464211506101c2480014840304000d8906410880f002d0707841742560080d42d0060354211600250704078080c294940c003c2080e51561864840340142c550b841c0d290450302c6a805844940140034900070382e00c0050514054244185464103081e0b00f001c80151049800090180400d281e20380b10032141550000850310840c8254000d01d80072500c8010306500404403611192503c1d05900107110440160303a214a400c0c8e40c01600b1100490140300d016150001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 130870395 1250 130869145 130869187
    0xd202a03040603020706051501020d11010e03070b3c04080d180204050702030a1205040219030812060a05010c03080c0d060303120c0203040e0103120c060509060423070902 75
    0x12521020500080035503154005200c480d03c540c1e824001d649807103c107100c609040342c000c180540c01041c03041040c9446580c1c00c40031800c20707000216111815544160450340050f0050f100d0703030b1000081052001140d414071500c44068000e441e07125284010424001402d0145503000c10450404034041c031000901303a0b0f42c03240c2080010450401500e020365800c1620400c00c9000300d003840d00154805001100b902d800c1071107510b07803032880706d421910200117100090040764000305600c04110300304015112640030303500c202500341da201600d01d01b604400c0802041e66105050ba203000b8082d50b603004506061303295040c10014582c0e2140310083c180c4e8090243e030010f51600c0d00300e0000074143c2c0910201038907034000c07004105140701c050080340c1383e104901400d441d086140004000180d1b030381c000f218120792a8034000c819268070350398101c1038039015151803055a2000090000f80714500d012101d83c5440e090320a100c45142400d402e07110142481000d207600da02042850007604541d46641e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 130871645 1250 130870395 130870477
    0x806060304060e120c01090b070302030712020c010f05070c05061609140109051203090a0e3c010f180621111003061d0603030904020a050c010903050d20 67
    0x1c2c8900130380070705c14002c00c0480e80988904880174081020300d8042d03c00c40e402124650754141201603034490240296000c0c8500300010b65031002c010800001e18803503140140c690703980d02c03000b10b070182c10890303e441e0000c0d14201e445440150002c4000d9002101202180c107414a101e500c01c42020051303400c4452503010b20f810200416119450503008030092210341802c07520040050744581d200070105c9011100030f407032001482c41c0c0341410507072003040c451003034800902d009200300910090040604207030300080071701840580500034070501ca907902c038550041c1d0804020403450050411f0391603400c50f0a020310a18170041480601074420308080c00400d020301503001000c20a030004000303154030721031400b502890003040742e038a60501048034000c850050041d81072400b04401c000003503000c441c128041c84030800103600c1c0300b1809c1c0594010036006e07480301e544910001d041c1e54282c40e81140c8107640010050b00e005024101102a5000584800113461114800520152601d480340007916 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 130872895 1250 130871645 130871647
    0x90e03071e0c06020d0f03090f030305130c03060504020f010809071a0c1e0f030a1d040b041d0d0509010903150e0303010b0301090b0a0b0901080a06120b04120806060304060e12 77
    0x116a0307540004040b80e5548041e075400c0b01b200e2440c8011821a5466200100320070344c100c0149005c41e00c2070700030b2604002d045403031103540c41c06a500e1000025031030340b00b101c036661a501003000f0351802e600aa0164402800d10000c5072808120840c0c035100e150140e40741d1000285110420680381c501070f10b103844289012194080c0c1c0d04101c1000c1e007091070721019180d1154034001f9034000804020b688010580380c6468120764803e8659007907002903480400e0301700d551000401055600e80c09140e0700443c3c0c2010102e5550146000c032402e100c51080d420051000c104007044050740d02c00060742c02c80e5007060403551a000114144c5d009009000a40b014506c0048008903160b1107410095040b1480c443c820002c43d1a004140900703841240304001d1742c0c65040c0180382240d4002c0307a1031035003d0f41c2020006500750300d80c0712000810b03608010071b603040380d07178681048108012401b0b110203150003401c04481b2490301d04001100fa21004100900a03904c40740310910507681009201d0040e541202c0309 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 130874145 1250 130872895 130872899
    0xf070203160f050c060c030d0c12060303030e01050c0324060f040e0702160f120c090e03120108030f191218020907030e0d110c0a140307090e03071e0c 66
    0x429040308440b41c195020300401a02050398908801102e00580f5640090350414260f241e041000307000381410b800600c103640f00c0820304049603100303400146110340c6000480b1501c2c80c00035400c60b0401460b802a200003003090040b5400780f03041c2002d100d405030501c10184d00080010900d1030060024106444d81c0c0440c0c003043d40c0c2c0b0291034048c07159a555007194405071840d00350300104c80705881201002a1040c809000050081a0010480d80503180520115582d503000808880803000c1851143d003010802d1b14986501d00801030040c0302c2000114140011480c0311304044c46400c8204020100520079106402d00542d10119018a110810003405440200d500d000a0381004101d1080e03003000000748441d0301a02c2404c5a0101c0c200c0280403420079444240c400044104101c1c2c0d0718401c0c190342232500c2d40d03060600c00c050702c0c03e40100c41c02d00c8444800e040ca010020317004000024105034080300c240c40c000040c0c8140c9500409001c40d00114030b241680314107080c2601a1840311ba8003c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 130875395 1250 130874145 130874153
    0x2031003020108090307150902010c020a15030b030c0901060e0a03050105070519020a0b01270e0a060b0306010311060d02041814150a0e100f090902040c14030f07020316 74
    0x8000c8034001e8880080e140d58240c803140e02e03482551802008040350741403d400c41d0b0741c1a07228103102c91041c10148040d0146400083d10302c1d0f0079a01c04201e428424040b2803400da85030180703096589041d4010003810907090001600b820050007504100544003d00202640d58000a1001150403100800c9541400b9030018400e40c403074072400c442c40c1c01e0038400d003c40620005114091031b41000382040c15900f1300d60b14007103041c0f15000c14404c0d80708120008000001070f20a501c514242c035001001030098624011342501e1039102d0f014426040540100007044101c8880141100201ca02950721100d0103c1c0e07000a0050350884048031260341d000d40d8040b4040c2d449030209480445003001c45c4d54600e44d100d00410745910702180c21041200341003140216419003240c0241c0c0550b11541e00980b1560742c0381104106a0114203669144c907800410350416100301c18000805142c070303000071840f0034400c1041c0d00c4041c0400131031079908000a40703024401e0051b226a284203105400c009945428 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 130876645 1250 130875395 130875421
    0x80406050d15031121010c0206010e060d0309090507120e060f0a0c050409050603240703110a050703120b090109090203120301060c0b130516030614040201020705060703050403060203 80
    0x4203505286400800000a0201c0b201801120b9006680c2c1000d2103070f80c030501048a42c4203d100095011181131020194420b010385403480c0d080c0d0f40107000300d40c50502000b0640d40003501c041d0288141c048080c0101c0e0340b009030700065800c3c606011481d5220307501e040b911801480d803002c022614040d0300410041c0c0204486006070040f01e114900b649031125124100d481c3c0503d200e0100388100802c00c4403120540059910001c001c0584075047c0020361000c410b07450303a4808107010380e10b01040042042c0c15101d900310144480010038100404004041c200313105100001c1c0038480c025070141c04401480c0c00c850a075100282c640e47e01541e48009100c0940a20001288280a0000e615001c6260001501d04071402c503a00d004800403103807142c500d803010203056401c0100180200b0800300b1020020220300300308501d4000d0b4401d10b1070914904541c21780060b4800342a0507410301015070707800184002590070807103190b55145000d01d001d43d090700c070f03950006000a0010080111003000c0382 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 130877895 1250 130876645 130876657
    0x50a02030a240b0906130605130b01020f010207030f0804081c060f050108061c021305070c031b0b06040510051f0305090307080f03100504051302120a03020303180a08040605 76
    0x10390040014400d0080b007401c0c2c2d00e0900009800c280154001045803401c002e512044160880d400500b00f510ba0011581d0300f44401100c0058035102c41004005513410400c003400701030450021800c1c01071390740d4010700c9010f10301604401c10003c10040b4041c045004103caa8a0500e142c45801c103140042c400805040c641c801e030308903420448e8001815500684445e80300300703030007000d22004000140800081081902c026600f041d8444038956005515120f000c0c010026516804508551880e0003414400f68550711440080f800340b118001421070a811a007001c01280d0100d103a50f103480c2c2d0b90301c42078296840341d5032103800d05803580c03842d03151b55452a500582c01d503020720003540c880d5072641e82c910500c0c17001400d4100412540081040c58005107802030303a6003d1a00141c1d6441000406440d070599100000da01c0d600512803c40c6840d40011400d4207202010f860480d4880d01d000e912400001d0811f10440103540e0304e80e5800c00188000f1320300d564031034441ca84072600d030032000b00300d40c10213 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 130879145 1250 130877895 130877933
    0x9030d110706020a0b011203090803040f180e0303070c020303130b070c1a040909020a0b04170c0306220c03020d0f05070b0304020a050607111c0501061502030a0c050a02030a 76
    0x1001052407407001c103040c40d04c03a03003100c0d40499603464014111700c01e18403d00158200100d821001c12411410300040c030040040c00f2200042c0b07420084501c41080072445150300c0646040326903a074080012040d00c1e400745842c10013003920403480c00440d003184100000c0c507901c0d5030030160124074108220b01400c01540107000000c4ca2607110001804070480000e1101580c0f14144005c1181c03c0403600581c02191015100c0c0f0072142e0340d2000c21025402c0fa420103101d83d542c00000041051041005140085040300105040d0400d400ca80c0300c0b0040d5a01d07040400020304110344103000010811030025035011307141102c1d5203140c0c280800080042c00d402c98440c014030710700040c10803589043e2405940c00030b18012803245050b040003156840740404881240c000249048160380e0001c01c000391076005416403000582d6440c00c142110200d8100000c10180d00103152000d6134008103403049080c0a003000002402c6504143c0c2c600a80d03e0002541842500105403c021240b913200260f01c0c94 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 130880395 1250 130879145 130879153
    0x7030605060a0f0b030a02070b010e0403030b01020d08010611150106050c0609060408040909110a090e01060605031b0310031202030901200604120c08040806040506070513090207030509030d11 84
    0x510801c00c003150746240714483c0c41500000d400d000c0045200021504007089240c01407401001d90b0780c80d04a000264007020b103940c11001084241905409241104d4609101500802010307540241c03281c50180108010042c2d031020a62a01104000c02c00c0c5a0021a8600303240f0340e55058010300741d500180c891030307d6002d054086907000e071300018000d010329840643e031030800342820000402449200700640f903a4548403403200742629902d54041c09402c030000d010074146240041c403400d6680d03036030003001000800c00c20009030842d03c210340094003d490241a41d40c1e161f000c065411049075400242241e102546810046034000004204540c1c080c0c803070102da081000ca0b06442010815084500c603001600007a00040c00309a0540c150307510360506030306a003080d4507015900e8000382c01c8050103910010500060000c104605640100189016841c040302000000c603142c42600c114030820382c000c9440000c250080c000c1e41d1446001504807490340425401c0140071102e08048401a401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 130881645 1250 130880395 130880401
    0x90c0a030c03032d05070206070f122003031801020c06010b03010504060e010302100f0918090c0f12170904050a0903031a0616020a0506040303020706080c07110108040f050d0207030605 81
    0x910640c4201310340381240e40421503000055050312668070081c4205e031312078820080000000e10708000407102074011540b0144091071541c01070480481c00f41501800c0c0c10629064500c2c003000012250b10581100f4169804000e050f00140680030780d130b0100b105801a04008030320290154007550481d1421501400101e0b650541d04031002800e000103074018002c900c0910703201d8010446107240d002c01386031030079403250340381540a0081c0310180614810340d11043c0c5102800a115103203c0030742943e50100c2005850700e040e04a54842415004210002c1c8544c1110502c10460136510000e2001d0424480f41c6407001d02800201502c031002c501013031601110003d608540180e1280720400034000781d11b003040000030741001e4110343c3d8040307a00c104030341d4001c951070716000040c2c8000c511a8004000ca20b08150340a80090780090001c5001c000600c4000085592615500c140e00b10a003010405030f03e840c108030849200324034024100e48a860010000c05900046807412030703004000030041c43d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 130882895 1250 130881645 130881677
    0x901061406030112020a0513021803121c0e01050403090914041709210604140307230c04060e071407050715050c0105070c0b010e040b0708090c0a030c0303 68
    0x56540c03070300418140018008142001c1c90194814001003440030b81565030800524080b5030500d1103020342e9008210411403004503151581e0303415044003d03200300020170b01c8048079401100d000000d0540411000d084200459100d401c44282c0e800083c0070b91f18040c100500051301074440c1c0010f50b413404081d1003105581c1040700340200c0d40403500040c162b03103648440a26030800303481035501054054004208400792a902c45030202003401038005403401d401c0502c1d8001001200000304d8004200800008035000c0d08458003544c00c03039255010100312400207103041d805600b4140c00519001c0301044101003948035a01c141c02c00e42d1603101a9441ca0040440d5016002c0c00400c1c89d031100c10107100f80c07412a04403003a00d00c2c082c50003505015199a5050070b540c0c09540360808a458410074805009002a819014105400040580b0704166640340007600000b024a07080222107808034100200920200e0b1321480010048070900b6281d0502d142c031074002c0e12085001c9445034618120300c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 130884145 1250 130882895 130882919
    0x91f08040b22081b070906030515010605070b13020607030309051002040602030f0a2c0112090201050901081807060503100f12060203040309030609210203031b1b03030c03090106 78
    0x2001c030030705000c641035641c0d50f00b002078100c182c2100800813921a400048003003000a0b500a0014002c049641c030715601782141011034008090f1040580400140b000da84c00078100c1d0000e560111010703142da610740014201562008000039845940060740c0014107130b25400054646018074245d400b51200d58007907408a00c600d00c1404050380085c001d220380c451489028201c0002c2d5424407001d010314001c89248100c20b0f21151002c41d8084c0fa416503ca564003140750541252001c40400041e84540c0010b005030040c500744504000d03c920001c1e00004001c643c078940764400504486129071204006401908112a900240c032942e05000070000e40002c2140200c1d40c0c5088142c011038403684903c800303940300900c1070b410b0050a010000005055118101d001c0f4050146201120f242180b80c40c03400c080000c120381194414000d01610340ca2a8202100d051034000600303503200d040302d001800584035082c10403003034000442040a0f85a140009521820300080200310007a202d181c0e50a00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 130885395 1250 130884145 130884181
    0x9110108090d0809010b03060c040e0105090628080f010603020f031203010b0f071a060306070305150f0f06070515130b06060a020102070b07050919050d0206091f08040b 74
    0x1140e84102e01000c403990240714210b8020a43e40e0001c251100b005000c2482d001062350700110220f000030b03041040400100c1c8840c090001103030004004d04203980043c041d0010070343c0c90302c0d07515090001902000c01004029000744000826108522404425240200014801a40503042000c3e40041500e0b02140821400c088014000d041d41d09050101009030020a41640341520402541c008100ca07419404c80100d1443d812603030b10310700681403504049014021009150500042c08400d170340380011003d050500b540e15404020314500002d030919081070816812050026110040c0080450424980745403100c0746000b40d01c03848a1600c4410034000050159850240421030300d1810038010180692280f00141c2082101d454020701124241c8820340480c0b000a814603490901380c14646001a4800e8805501c51030320300450480111140c009100303a800050400265030303a02d244480720030154551460740c00520501500404080d41c0c04e0f1804540040000c07030141c016070700400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 130886645 1250 130885395 130885411
    0xe0108060412091823100b09180a020304060c050c060a0507051b150109020405010503150a030c03060507030b040204030f020d031115190606080f06030307060504030309110108 77
    0x503140e66252102c080042c0740580b40b10412581042c0044c441040000e40000260f4280000030200da0700583c1c1000034800300300d0180c064880c0400c101c009a0501e0000c0222103820303000c00d80d5854058001742d030100d003100344644407a04007418442c40b4185a8055071080384101010040c0301203031541542d6034024801e460300554041c070005504507c6a401c0a0b40004043c01d015007032941c0342c01d44000311610071900000c02e900045101860413001c0071098018035030b0003400c5141c1401c1c4000200b10307100c0103000c3d0300304160354580c869990b2180c00401d4029074003c80440f01c020345034541840905001e9804400081c1041411400e40c50039100b1201240d0380b040c1d80324103c11aa600b400315010304042e041e410b000084810310910442031003805400f40c0b401100014038a044180702040300307021502031003284d140039800e1000d41e0700403145036080100e1501800b129a181d0001034514450020010035183c10036040c0010550140c0104003002c0c81030300358485d03c007903003401150844402ca0b1519 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 130887895 1250 130886645 130886653
    0x303040f06020c19060902100503070f0302180d030c03030b04050f0a09021f0e01080c0a020c1c060207060c11010902011b0807020306100e1b0301030818040c03050108070e0108 77
    0x80090110342c018400e02c071003c41500d04220ba400841110800e0b0f0302400d5511a4031602584214031b4103044030000aa481e040c041d0950a1100c0e008201c1c0c100649420145075000480b0020030803c2002c18200100003084540f5088a52078014091010f2120490109080440a41181c42e0074003032030303100f4080107900c08526540e61004401801c0c5091060340c10030034200d03e0b11486c07030048944401d242816220040880c21920005103000001455102d42d50710601c58640b04d0340d07000c00c0d5000001c40845100900f503501003105400051440c40050030288000780a0701006041e8108159a62480d11a4041004030f42c001602303884617236000a0008150001c03101d18840a0150861101e01403068541010305590100f4500007082c3c80c0c1c0b180b40d40484004200c202d088491080e40001c00e58061032504030b50846002c3d460106000007840701601040180d20401e40b01010402400e0050061051304504940a002442c0a0040010b00e0062120202d00c44400f00320030f5048031a680024 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 130889145 1250 130887895 130887923
    0x314010501060c0312140c040609090b0f0906010207150e040501080d080412090f0801060e06010c0b0c0307030f021303060b011d060c010e0304080c09070801031e080903032208030304 80
    0x40310310910740d07001001e42c1035541000d0074a0746d0140d003c0300d11682520f24004e80d901d041840c0070306244003540c0000b00c50f60400d60080050f0700d03000b0707015880d8001540c04414070740b5040f00507420180150003411a40d0148000313070b410316500108090700840c056408000590b25901d1054070790342a41c07907180120748e4140c0845d000482103100400782501d00c0c42c04000d416112802d124031b806c0c0e680e10082300d5a440310700901c408500000c10360341000003420541c0a00b801c83e41e0300c80d014500100318124001011000a130719034041e4102c4c950700119004115584d026440c08022442814081600c410749402c1c1c031003c407540599103812039000110b03040341101d88040d0411105521124190f1210b549907102c81c0d070000406c2018002900d20130014141143c580010b02014040040c00e0340c0c2001100d000410100d402c0380030a403030a68600284660310b1041d418080114410440d03010b40502c0009800e0b159814000364003203c480503c0c0c80704040c2c5949130313242941d0f4042914054440c1141b2500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 130890395 1250 130889145 130889147
    0x5061207140c010c0801150504050a0308070303180f0c08030c21070507030b0a0e0705060a08091606050c0f280f0f0804030b0a09150c020f0f070314010501060c03 71
    0x1619070300071040c1c14080c079001d00d40600c94251500800c40c0350100300700317800512a5074108014000c1034696440d020382041c0c5450001401d07412284400303450b001000840209240c841d421001500c1042c62040220a00ca4681840000521103081d40c2c0c41c0700211000c031341400701004440500080c000201100c400d80c0d950000d140d00c1c4d1000c003988482041281d90000380b0140913100095000b640268558944450b00e18203644298078140c5081c0c2115030b0a000f907230741700390a583c1042010320381a14240c0e83c4806143c5814600d541001c00000c00100c0024142d502a00528400c04248281e6074400d580c402c0c1d1a03500d504003540904601c48501c034840340c80782c50081c0101e8150058007100c0280c2c40300d0321101e12243d011501552900c070002014401d201040c20310b2170300941d041c80200300d1008180c03552000140c428001000d816201c000d54001548208030a0b085242e048041e5100586000c0c1c5155072900644411582800b00802d103c03500f00043c41140d04031906034403600105449560 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 130891645 1250 130890395 130890407
    0xe0d020d0f11010c02060601080a090c0b0702130608030901020c0301060305070e0603070f320a061101060b12060f03070b0327031803060a1109040905030c0d0503010f05061207 77
    0x20034202080041c0b804940150400d00841c81306a00c81e801070041030400e17a00050440c080100100321140c2003418050002d139407200e10808440c21201c3d5640c5558907032000605000030b501701e40f0000b508221001c02e10072404070041181c00400d8084421404d0350009050998041e4400941103402c40300342000726102d01c0503440e500c110000c041c0d50800340c854843c01a0302000d6001000840b6180c0b800c0031000700c045100c1c1c80110040390103500503100f40d2000807070000850050300304101900000c0b0010702d609401c5000942100c880541d125541403030100100901110000d11030542e80341c840c03005080206294060b0340340000e003a441c6980d10040c1c9503c80350b074801c511050030701c0c0c01400740100c4000d001500c070118600e840d0f00c500039101c40415140c9a8080c1070540303814a032405906140700d00300110766510f28150790100700300c1d10600303102c0d0840c0154904440302f40039086103184800d80c0a0001c5058508041094601ca512001804400d0107a5013040301640c0070880030420482c0610 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 130892895 1250 130891645 130891667
    0x3030708090102031902060709060311090d030201110f030609010e010b162111060106020d050d11040302090117010e0a030c02010507050c061c0b031b060d150f03060e0d020d 76
    0x3c011a0325060040c4400c0700b03224035506030000140c0191051040c40381d4480792940003800b05140c14082207454040e5403119100300c000c4a0700c60707520102900201030003900f002c2188842c5402d940c0d00c4d00c0c01500030a81c00e0307004584192041c03d985001140d1a603400039100e059920101d000c500340001115000e10800503490203842800d2408801080108860280703e000c5056944500c10000e00d01509403900703006820040564006d0445407078a560f01400765156007224401c041410b88902c004050180705580010707422424020000c80e03680302d00c841f10903003001d42c7d00c000c000c10703d44031640c0ea0725044007070f0340200020003100070b0f480551700c0b51001c0d080759030240c800d03255000c06500c00903946901119a00301140d07031141001102f0546403180c040c00f42e81c1039001e003119205206c20750380305d142d80d445014440c0c4400303e5603107089031095200c51040344807600702055a42d11100304146500403440100c40342428003205400006010075400241c0d20350760001c0c10701071401e20f07068405850345 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 130894145 1250 130892895 130892897
    0x90d0305070f110f120d210c0503060a080102040b04050108150909010510080f030d0213080303010303021b0f0a05130f090c03140303090d030c09030212010507080a060302030307080901 81
    0x24008507020528140014420034429001420300541890070b0290704929246024880c040300c0b8103090300040042032030303d641e01d0b6500d0513524044140d2010607115000415959a2a182c004004444c503001401140140170807900c9403103250350b66003200c3c00e0780b08034050a805c0482c103020400055006010306600249020306003111144207001042520600b1608403140381c0d1030340301380107190f004840c18201800d80d45001d0031460f0800f01550b035403489a00036440d010341e4001009000c00e00c180b1040800b4042c12401c5c0d0740da0f560340381002981e8050341007240c484140c49a03198805450814450f4400010107001140402d103003a081110f180f001d1021020041d44039000503e001031a840f07081c03800c9100d5441003c60360b04500309842c40032070402c40c20582c0e50041041c060307030400016a0f5400c0c441581303000700d20740400d04001c441410715540300940004140041c00c54003001908420312481c15580d41d68000e5a1362060f050035240e2a01c40a13406800820081000c41c0b0030500405d012201 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 130895395 1250 130894145 130894147
    0x140402030612060f040c120f0206090103022205010311030f040312022a0f0a030228020d0b0714090a050105090a050d0507090b0114122802041e030503090d0305 70
    0x550300074542042e804413002c0c0c0d81d08141c1d40821040006d14180304001d13040045814406800715600c1c00486500500040d12038131001c6510055a0300c05c3d0102d5961103210051903d038410144c0c04265048920700803240400c2c00d02005094030322110060741d00c40d07000c1245200711030700d4988040d110354502044284c01030313401f000040b0007141200b02032500001101c2040107160084403105080c00701c01440c081c03107030b0403207405200031950000c0c41250b42c0c0189580d4880703003a46911000310103040603000940007401e8448603824094188000c5200741516220107500b9001c9559049041c0b1a0508440e0320500703a00781403190754401d80242c400403201a0010704c1c0300c0d4440b0001030104055060403642a48000c0d07081c04482c8281c003452400c01e9007800c0900382c128841c070400d0481d02549071005410b400b40310004040d60034000c0041340d100e8034101105c8072170810044e400c0c0a0361080c091610311000f410080400003d00740e50040443c0c0d0400041c506080c91030003004840d5590a1b400d80130410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 130896645 1250 130895395 130895419
    0xe1507171501092304110307090303110f01050708041b030c090f0e0316050f0109020d02040b0402070b09030c070e0c07120207080f0a2d0b0a2403020102161404020306 73
    0x140c0c213046aa100c00b243d00304c0403005005100b04010f40718480403071601040b090082c1320141ea013204520040d250f0604100031844801540c0d80d14210000642d410690308000502541a03044440907000d24025124600201040a09603524422072711009100c609501410060310446a20a400d140c407441d401040c2290401100b925507041140412003003002c00c0d412104200c0c04101d02142d40a030607000340030307001c42500042c503030081000003c1d001e640c503101c59041c07a1742c640d030440d42515070021442645041c018042075480d082010380100500c14075101203000c012213601c03076101e000d000768101d2070f1000781c0ea0382d44080308100503048198440c4150100d2059400d101194080100728000d05080640742401328240209541a83c00100d08001d4400140e50311000e114980d50000800300094507a0202400102205000700d80d1201d00703040b904083c0402c10100380c084078000d03401c0320b090052014400081c1c0c1c08a00c100350846d0b201590800c1ea030b0034503401841d4408002040b0840b081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 130897895 1250 130896645 130896659
    0x10306151d06280216060804020402070303060305010c17100305030f0d060302060d0f050f060d020f150c1005060102060c032208040303050a021204080c0616060e150717150109 77
    0x880410101103140c00f00307002c40380701c03541c100f00100425030b84190b40301416190040142c620304014201074021070b00000c41800f4035000e03030080002140e000000b00309001c103051005140c00001d000c001140d1a40c400400d210140402c0008203884c0c00001452802c030303c150b82c104143d03106a0104c001203403210400009030340c842000e00307540700d04254041000f001c0c03108103400f1200000c0545c9148130306e02c0144089500e03201aa089050341c1580e100380300580b6100021602c0d40409000f05a0042c0007541004600001c169281c0580b1032100a102c6038940d04010380c0c03115400c9522a01251040c8000f4009019031407012441d988101c072003034804404d0391682006984641c009038003060000980629403075041001038911141000568201400d00b9030b059150140350088a1041c8808650069440110815031424651150040002d28551004070703807111000e443c80240b20900703500092840f1300410100c4001120036880103010b546842044400c00c00b0314403010304115030302402142c07034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 130899145 1250 130897895 130897927
    0x61b010615170a05040f030f120c03090614061c030509030a030c0b060d0b0a020a030b0d03030b03070611100203070c0b0103030e131506030504080715050105010306151d06 75
    0x80003072903550104501c4201e1842000e0403000d00612100ba00e42800c10001c00c0729402d00d0b08145074507140c181c4e0041246041155080661314038088864503290710418100d07010303802501c0791403040400780981c0c0c0b140e0b070003854030150485015410404c003803400d1003403028804406001c24400e003401c9041080220101385001c907142c508401041d52240400144071304604c1d600c0e0312900480c0c0c1203112100036580c88008e0f240142c4400b405075004505818080e00035002001134101c003508859040d489800c0080c050103003c6074540c040e0044000206286203c0c2440950542c54000106407461649180c84001c3d0b000404410400519003008000aa00d074106e04c0c0c020360185e582c1042d0300440740d08115007a255811924013080c5001e01585020280c00000c900711151400c0c00079951f900e5017448a424030468000074032003400400003110361310582c0d010030305882e82039030200901525500300b910720000280da05404240b40040309080c0b29050121800c01040280c80f107802d2000300c2c2484480c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 130900395 1250 130899145 130899179
    0x70e0708060405090a030c0b1506030405010f1d0304061805041515020f06060f01050903030a0809160e0a0504031b0302010f0f020306150c0106170c120c061b0106 71
    0x500c540041c00380a1410340145904104e01c2005000c0300000c540d80030340f11220040d0014024421140002c3e610819a451542e4818010301403176524581840c006000b041c40d2802d10b03404600c0c1c50088d0403070a01504030058402c0224008500d05070030203600f51410300c49960180c080800382d100c007013901c0e1140d00030002c005034480c17401e0a090781040b8043c01c50000318034542086500034904070f468014000f0302c1907008017069a1000301840c070880100e90354440e84c08403603094800010007907031443d0b10051a501c10b1080400fa02c100c1c9550312132010483c03003640300726203154407001c0c08910182070a6000b1500284642040100c11121a1550030070038501282507001d0b0350b40c2c2d484480c00c2003440c01005825403581100310f10358544000094102441c1c1c0c060804581800320b0f000302010350940c81040540b1090b88480080f00b6402d1495642c0e4151880c158018080c1e031040e88110310700050661070f040c400a000034102618200c07400c1c990455204110281d648440300000d08950308000200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 130901645 1250 130900395 130900397
    0x507051201021c11040504020306120610080d090323011509060317030f0408030702010e072c040803010501120902040f14010f03050c09040305090910051008012402070e07 75
    0xa10350600d00f04088079070210300d1880c820320b81010b01160f6500d900e50200d4044e183c0840c0d00503120b03101d83d004240c250003000107400c1244101d1040c0700c08070340c581ca401c10461700030800312442c241c2000d000322002c0d01d6510004001c0719683d00d02d81c00c08100ca40d0314007101022040001101d02203c00c802b883e440c0564049240c0c03036900c060601c00d1010300004000b055107008112845c1d03081c0307501521a13061005001500280c40031020400c00f034800e4021500120010046460250703c41c800e01d43e201d10313400d0505400c50300e000c40100c1c982c08500411446542c224040c0c80c15030b072070000195445014540060f0086913204a4a401640e6a01ca04458040c40941c0000d006452120544881c44180c22451580c42d0801c020400182e001414100c40c2400707a40c4403a0549440c90107864500a04016951203c10b560810a501d08100359410071950126424100722f51501d0b03099800070303800c0c0a0f40ca0780042c0b40302c0c24611807030740c0012004185035034812140c0040c0e891480600401c01590400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 130902895 1250 130901645 130901647
    0x10030e0d1103041e030c090b0a0503010b0a0501180b071101030b0105162303030403030509100b010c02100c150b030709110a080606190302090316050d0f050705120102 73
    0x21054008106885040c102400c0900300d041050711503079070780c0c0540d100b100940d18181d101508180100c00407440110b6001805508040c0c540505001400f0010f10305d501402c80840e000172146014059500d2405001d8940050305007000d00440d82e0600000e01c0d400c1001700d0100010700500403078014611140103617030b81e102098080e4001026100750300455810050280000229200d00c04503030381242d54081c5981001c048200002807906e10000c03048440b5000110400042c1505900704910a94410782a075603545001c0202c8811504803140e082d0000303004c0d514200040c103124419195092060500c400114142d540d68600450480d290200f0303907481d401d11130b0b0a401c0070001d420181110180501c00340c214080c180c1414000d100e403003070030002d013040030800c141c42e0380d001c858101c850803420840240581002901a503c02c1e01c11741d01a1103504184044000e6203005001038500c024400e180e529400d031281c0c121121201310668980c01403031800078260380c4d0403040c000f411031004009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 130904145 1250 130902895 130902911
    0x509100e011707110a14011a060409020c0724020c06041401030e030c0f0d120203360f01090308060a0609060804032d030e010b030705150c0304090b09070329030c1003 73
    0x607d003580c0c480c04e031282420868030860b02082c0e40b22400d131802d40340f102c440161070700307191442c03146130088613404503002e03c2c0341c0d0494041d5080c00d910581d00c00400f60302182c8040040d042404050f01c114440d00b00d11a49800c00c2c1100c940c4250019248148500c0850b800c2284241c1c0c007505040c0d1040040500d82c1c894504060000d40000544548000c0c0e590110305615094815a00c41c0310307060342c8201400d0b980000d001c40c800b410740d82410710348801002c030f800d15010017141e00d00038010114207034003141e6040001440e41c5400c07250141500c84a5071103028491500bd400d03500c140c000b500880a00035001d40510b88070910b01c100001c40c075451062442501d80300e110140c116089612900382d980d060001500690300c0000f041c1e41250070542d2481c40d107115550b0b80191a000d008801d42c002e0200040000f03070840c254200104602e01210ba1403001c1c2c4030070310142d04481c2101c2d680d405200e0040960011440042d405484c940750140603682d024901400048100c14044541d00c082a80c401c49 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 130905395 1250 130904145 130904183
    0x31b0304030218060d0605060613030309170c2404030803071d0d02090606031308030907260c010309060f0e010f051008030912120a0509100e011707110a 67
    0xc160000801c0389a03440c0a4200800070071905c800e81c810244c086c1762120040348690701c0d0b0404944000f414440e0a100030350f02c914000309640030314411140d030b8040c044c070242940d490100d50f1200100c8000d001c40109080b02d055040796190942e003031116a0400d01c0000040740c120801148105240d40d90303c40d4200380c42c000702000d00e0003a031642e0300416040d4043d500684401562542082d0704030381c0b45440b50384000300c2d034240404560b0003c1c610200030090182c00c10000400c2c030142e81100c481072010a4138250034481c1002d100320b8081041c0d02046040505500903809884107a00840c1d0110b00d10242e66016800c0e902c6214410040da035664010f170019170014415150080000d65030b0840d06494502c0c810703924003d02e032000d032207054400807505035010704100ea06d170b103004071000349526a1007031900030f003041c0c0040302d4160040000020090b0418441c0580c81d50b07010050b120440d05d4280c000e014144d5900060601c0140f100070b03442d1004040c03041105c1028035102d0b1fa12a40310110a0310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 130906645 1250 130905395 130905409
    0xa210c08010603231009080c030406180b030c0307030513082a030406050d1e0608060907080312010603020d1401180e0105010506030c07050115060504062007060302070203031b03040302 81
    0x10600d003a4040c62690301030030404c0810007407041d0038203100100ea411710174182407146c0d02c00da0500e09918480003400003101034004c1c840c1c8050122096045900d1940e4812525203840200c1e800820f0281c2040003802c100c0c000d89c016904078070f0b0f090341070524060325034402c0840e5006e1402420712403113480c0380704842d003d43c090300100720031010051401c282c50400045c0c094000c00310020001a1200f4404902e0124002c01e420703e40100002400269034131802c1a46441040e5a00c01040c041d010b00807c00040020448003034036030001c04000f40341c1c03034240c08030000d4100305400c5030003a84400041030b40e200c484007124007030312001ca0121494421280391108990310030704a8411641030100400941d9508829039510150b45603555581d80510314110b0300400009140d03d410b10007208001c55640d90101c0504250343c0103486035a00030210f11540312a15940199400c8168407900041c401d40f4802d4014040451005d02100d0408080074000360003c01c00c40142a82540701040810651410345 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 130907895 1250 130906645 130906673
    0xc0314060601020c24090303070c0501021006060807050703170c0d0c03090b0c1b070b03040204060e04022202091201020a0e06120a0b13020a0e0108060109050a210c08010603 76
    0x400180402d00b103204c0802d81030f182080c0410b401c40c2075410f020014902c1c80b82201c8540c40e0003016243d540f4100e19145643d02014060035006101d000241d1807501103900c0b440c0240d941d1926000240d030b40d060b0049490342d001d640100c003040303500205900d00084496059000e0045022031688581002c42284100c1d2040d5521008040c149010f400104019514268202003500300090340e51910710100207480031a940c03040a58410581c00007170301d203070079009540500d10854040c894582d94403c0032503000c1055030702070b512640d03409150b5544219580080e681983c0c40402504228460300050004001c8640c1400300740d4000800075002a0f100c20aa0358000703040b2201424080940010070000000500b001135056546031100d010369100004e04130110800481550340e0012050018032038207052000f18080358078a00420081d40c010f0317052900303441024240d01002454500c180c1003000c0084880001880c4000640020446601000c0003400d0300000108a40e451031800301c81d400c0e801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 130909145 1250 130907895 130907897
    0xc01090b060a1d180d0e04050c030c0d24060903050601080d0c110112060b1206011b032607110d0504050a0302060903100e07090e01020a0e1c0c0314060601 68
    0x4030018000b041241c00201407007011049880b1490380e41c1c05004e2115100501a403200384500714100361900c0d809254641071000540e001d00c07290f01e0b46e403001c0e070040c0401e544207116400240b0940041508a0f8088a185000000d000d80503c442c142c40e4030041071142c01003400a842034000b07205011381040098010013070040108074843c03189000900801c20014003c1400b4a040564103a50784a0010b004c01e10800701c2c010001c542c1e81d8000b22003d98400101800203440760b90002c0c1d50703580241c2c46400c800c1c0c41140420040051558125a075a5105049100c481180b070100302840f412240c2640c070070415915860304103a20764003a82c0c40d1038264442c580403c00300304400d00c4291038945c81d01e011280d0540303c2607110901000007a042441804480320f4291400b0700200301c1c071b800000c2d110304480051004000141101911500344e206030031400300032801201e21500541084601e5010448030464907042800721ba60300d07841801ca041e401501c4020725201c51003030400341440015004082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 130910395 1250 130909145 130909159
    0x60e090307050a0b04080409020406050a020d0f120902040e03040905061e03030a080a1404030f1812080903100c020102090907020c01120b04110409060f1e03020d170c01090b06 77
    0x70b641c8890341c0b07002810f0010424001d00c00403a0402000f141920702902c180001036440b01d455680007412900400c80d00d00040c8103005070805070701d0044125224104282d40c2d81c1c83c442c1030030745002000d4050031500f26005503854201d000103010520240011b084c1c0c0702c0380400d8a081c4401080100003d40a1848030081401c0d044000c50b90000300303c030000411400c00220640c0c4901310741008000420301c40c1a0f200482c07042004142d408844402240c441d82c8a85041400b62484001003d417540a0664200c503000c1540700454042e40142000f0382c001011600c11000c0d11202d030041e00d84102074180942e401281410003032501e803069a520203500e100520090184000090065601c0c00c011a082580c2c1c400145c06622584c102e14021001e600b182907441d43e441400740e0086c4041e01c9800e0010114010115214002040d50f0b480e000750440ca440ba140d04540800c4001c00c0e041c0c00c12503407a440f100415810303030017041c0a4218560304800000300085513040040180030f0013002e032486405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 130911645 1250 130910395 130910407
    0xc0b10050420180a05120619060b03150a0807030b1005090601020c09090c18011a070f030302030a06050d060902120f03070f02030f03030c0c0c0301060b040303120b04020d060e0903 79
    0x22031603041c3d0f003040c0c11030f94407848000500d4010800f9501c09800c02134102001a0f00c0940300f201c0003a00500403e4200c2d5000040e0403001c0e00c0504454a901811071905000c00102304941c3c0c0d40e48600c41c5200c002032030798240c2d6661b869428582001c1d0780c021651100d05804003d422414500c3c2071300180380598004950303141c5080003e448104030b4201034451100000414603401082141119040c0042c004410942604041c84003001007441020020794038aa00d40d60440d518400f603694050380070030409a005a0b6903001e078065000104070400c030947d200c000090079030f2500581c1003200c0c09007000107499030036801880110108000400349991068800340710711100001116211a003140d0007a85002d0070344002403d0121818101d410352001005100c16102c2210045c001188000304440c60150602d040c1030984010384901d0400c000e042c80f081001c40e02803450380c22415079a0f9400606103003203800003001c070380001c1c090b0b601856540b4810300c0400d03480d0300142c2c0c104110340000e40c1081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 130912895 1250 130911645 130911701
    0x50c460b04021c06020d0207020406051c030c0305090406090e0f0601030305030c09060d0c05190f020d0509010c060c0f020d23070813031b0e0f0106030b010c0b100504 73
    0x5038003500003405100f01081041d8610705040d00314111039400f640c15580e410081c1a00381c040c3d08202001d91299180080000d40c80c40c1000010345031030185081c8a00842d207580f0251002040c3c0e01044d01071060402c5010040d585500c644400703401108000105070078031021a916200e054440d02807960702000040c400b29411a0035079034000213501c1c0080d0b603030000c0c5011035800e010b0003030000031083c141032180000f560020050080f11500e1620109208800001150b4103805c4100900141c2c0044002085191003000104600300701030602103420002c9076502000c5580d581020b2000a0141100840381c41c5d043c01303030280c3d19117645420a102601c8014664189112100e07217642c0c50000144402040070791000c0d10140d0075400303038806825a80c1e0411800c45a0001c40c1c035865511400c00100e0525030b00701d40c5c140074403017035903002011380c1c00c025068004181030010b10b4180f011121000000070f580d9841c05120b5601d59007100e0400e45800c09000986811060004040391003050302440a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 130914145 1250 130912895 130912913
    0x605090c031b04090602030c09040e07031109040303090f06330b03060a03080403050106030201020706030218090408040503010c0306080c0f0d030e060d06030807140616050c46 77
    0x1000220711060314142403400041c3c01000c03040c1009068a00100400005401e65005030009030800c0e0390034005a5030f183c40041c2c59041c20f00006001d140c00800400c40c45c1405c07027080c1d40c024443c0c01d0000d01030100791600e601c05d0841c0d41d002c0340d0b0131703440f00b00c821801c21031005c0c10081440188104040e0002e045904680340045018440702d0182c003000103441999090301a500443e08000b04554594a90420602030040d5000581c05440703826800201c5030b10034400c130340a120000f0001d200c01c41882c400c0020303010001d00300740d03400d09045c4400f04040e40c0a200d02d0f1400d5a01d600c0005030589084482d50174022041045803181c1190758a40d61542c03640585090030310f41c18902000910f94200001d101c5000300000812250b241120100c1013081440050640e94018a01412650100c0040b2550340100700c1d46076482c1c10b213552021320414043c0001e000030300881c0c810b58215a4080030081d4211011540c03208030340141810800c51180c1e800b035952145855078500600d41499502c3c0c003000c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 130915395 1250 130914145 130914163
    0xe01060f0809120318010615090e070e03010c021e030304030918020d060b040302011d130e0a0203030703020a021c0b4c0e090607052206020601030605090c03 69
    0x74040c8030300014419000a22030701040320700040c50b4030b450b41400c10703000d030051550030390000d030540c603000c000301c0c107a110480441d2800d441c40e6106680541880786043e03030b01e900500105e0511101c0c005404407a41c0a000d101c0c1e076a07855034018020001580401030f03015680f6580d45140c0c0e00104280000310350b11500722000d440d501c15500941c0018945241d0087c4030380d1141c3c006051034164082032800c02c070300013401200d0007661480d4101c1940a0f58040c4a0b12142c1c07802e901c18048032080b1400302040e004280d00f140d45070181c0300d0600f0103401190860b0320200f021001a0803148800c1d0862a111004110843d840a0b1121a04903580d58542656101408125901080c16800c0e550a210300b50103520003083d441c405910b000d00179260000101000801d00c14000481b04040b800d02424080c445c400d000c1d003001400075441d204000d84855109040821140c000c41510103400c40c9000c1845000b484a035000b880700b0340c5942000c6040f21400342c40c03014540c010100400c690390780003994040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 130916645 1250 130915395 130915397
    0x10031a1215090a0c08010501030312021602010f0507020a0321050708071b1e060f0302090603010905040f0c0b2203020d1209080708030301030c05030c0d0602090d0b0415060e01060f 79
    0x1e41d0b0384440d5125071500441000040c12100d6480012400801c10340040c0d0403648240c40b209550642c1f08040001d90144400c00da50940c0c81c0317025100950b00c540700f040404c42c16070607d17a19005054021039200455908140e40800459140f00401200a4072005125100c0d02e00107052103035503540c0e440f9500c14900d01508545000404e21814800f04000800030080c9040d098110150750103140300b651417911980b030100c1c04a44e0b1212905d0f0290080b40c180320340c01031040745145c0c24840708000a00000d08151a010003406010000401d14070308031010300505200d49e521004088a0300541e80220201c0c4022654646010001612031400e0075401c0d40e03000d003072001000789482e411201d054403988415418840c4240000e140030307011006605030b038040c4d038100141c2c1d40c640081c50303501c0302c46095894100c041c00715a0404140f290f4094160014010104102000c4a0b142c00c20307800c4040d80c0c240e03100c080d03c140c03e00c040401d500c00c1c00d009002c110b6070500da640c94800007400007815100340344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 130917895 1250 130916645 130916683
    0x304050a0504061a13051305090d020601050109030b090304030204090f1707080304060f0b040203130302060609070206180a0804090b0f03060903030109110903060403230405150702060910031a12 85
    0x214460a45c514418090725000d0214850b031203101da22a005888195804079282c02070305143c6500328404100c850582c1e106031150006645140c0d01d100b40301400070030440050106010220042c1e484d8000c00c4c0609005650640c03158809040c0040390880311481c2996180c13040003007600140a40c400d50390700c90780007480042c0c03076214641d451010301008940607901038400020012141d40c0134501d085024001e6003102c0942ea69003061111814040d10000d0160303102d4000a85424903d41003880b60448120a80305001c28a0382c3c1e15030a60016005945180e0319514036146a00b411420b086152500b200104520b042c480040c82e268441801500742d00b0b5200c0100a550b004031000300d1fa01d041e1701804660503450907040051121105400145403140002c100d2102e040e0500c00f80c400b03850f0000d04648211240d101114041d5022080880c1c0184041c4866000b03661194110303110144507850201e145152900b22840e02c0840000c10751003107842d15461000c2010015a441c009425010f0311 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 130919145 1250 130917895 130917907
    0x403020a08030718080106090b091003020d0212010903080a050903070c030305030601110303090303041109240411030a0b03010606020a0803241c02041b0c020d11120304050a0504061a 80
    0x80762820b40c4003c07044c04184081e1400502194154840700c204d42c01403204100031400001080041803041d034502c1c1c40083d1415050000d480e10001c000c2c1100d10041000d20381c01100703d1342c142034400c002c0c5c043d0041195a130030407140f645a4002c03103900507c454081d501d84186035462840041850101600700034021000544903401b0f508004403c3c075034602282d44038502400206da0301d42c000c66084402442003a021001400c11110702801002d0600c0314400c0c410070304055100c0c0c103c505160030742c46a1a850303034111500e040d000460041004400c04a8458031180a06007983c99aa210500715448080c964020071083c0f016a5040b400c1e5158070490301d11a05601c08004084c0c2c04908d620426480349083e500302c0e042c1082c40c1072032003683e0906c203c5c01240f44101100300811a0903000c2074070302c3c1c1c03118010300d13080100904051081d040302ca40e00c400d0302c02107000d803105103400c0d0007103a01c00581840360303190021401005010031102400003500346a6441c00f454001e0007000880c1d4008108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 130920395 1250 130919145 130919147
    0x60e0c0108160f140705070311090405120a0203070c090e1203010f0e13080406020a17040614090102070e01080a0303110906040513060504050c0d180203060712090c0e01080f060403020a080307 84
    0x9101d424120055131648401440c14400c0c4c49800c14401103456101c0000c5910752400d059041520480c0c000000d130100013002c00900145920440300b40c8114042000300700002008194007002900c1100340019601000c4030915140030110458100354040c1400100184200f2544442c10355045000b8146641c40d4048441c08070184868005c244000c003140108109600080f40c0070007a00920701000c1c0d80b010b4014402003445103000d6000000c82d02d100104020740d0b408003d195103c8184120760826503985249801c200003a00080a5504190243c01c00c0c1641030265006500004000c1c524240c80d04001a4031449a841224020340384400b120742c503040c1c0c90340188014400036005001526100000d006154000509141c0c02894074500c0e03044040d1141c0080d440719030240c0104096101c40b5800d1310390118a14421105036106e803440700001c0e801d088104000c00c00302e54803041e294103000ba0181815044204002284c2c015410000400c1d80020344020f61600455a103940c0d8480c108 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 130921645 1250 130920395 130920407
    0x8220f0c03050312010b040b0f1c0507031d0105091507050c010c080709060203070f06020d1503050a02030705012105040825051b010e06090f0904060e0c0108160f 71
    0x80050440c0d030100c04004148034000c4000c00700010380f03208601840c0e80342c21084040f8040c43c06602c0000d80c1c280117841d07021003490024804d240d44c1c00a0800c4140c0c004600074142d4004954441c00291035408004401f5020700c50a0584200c0200901103880c1c889186940d80d11140f0064602464034808a52001e00420803512490048002072000c0c1c4400640540302000c1514140c0005481180000b02d16102009a17644280e004200740302490481e212000079400981c040b074900385d070380c031540002c1d40722017032517100210310800181204c020140101801e00310b0b142d01050500024800140c4d4107411564180200055440b00054079182c504013039040780a50600e00020110b2601144500c804020800b11751a209008031168503000750046002d036070003910000c2c0400d2480c180c00b079842c0342c002e002c2c2510510160900019040240014401c41c80c00d031001da4910343da1300900701c2e00741000e020641c4424401e003400c1c880c07410002110070b04050a10a03034130412580314251416103100d48 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 130922895 1250 130921645 130921673
    0xf06040e030a030b1003270507051009051f0807110312010b0306040e0309060403020d0f06020318060702010b010c080304060e0627070302030706080c040509040809010f0822 76
    0x81101d403580402100a0014400280b0592240b541d0b05d44c021220751080c0603081e05480362401000b066410000d0501e100b959141e0201e80b540194032010986844426501401880303940d2a2403842e4902402d0084c00200c0c250345070948103400c440070400c03581001c0c4050b00408a4034000b480390080001c15810360090541406051010000008544c5080700c007540c0a542c0445080051045041c1d03070550341d100d501c1145c0e4112206000400240c0348c8a0603481c4002d0147c403114020030641d6561f00200c1e03208880c0211000b0550405600641080040c1540007175280020043e80440b200040d00c640503014008050001c0040010104922034103c017202020307160440b0204c0c144800300039000d401c0e03000c0400c901040e503072100e602c10798001254000c413a000703409410350b1410b10300d00712425640203041210401040000054941741c0080c064442c81c0101d8649866019840005020f0440b81c40340d0001c21101c03405016140c84038502d4120106001c4440c42000105850040c400348120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 130924145 1250 130922895 130922921
    0x140c130c020703021311041202040509010504031d0406090516020d08090c040b040b030d020c040f050c040909030212190801050103140105060903100e030901030b0105070807060515040e0d260f0604 86
    0x7080020381112450308484230680708176424001655560741c65403c8030011140034002414401d556000b4900580c05090805c0c0003510210340d2a03145c00303130441130382c0080da00c1500c0c00c1c6540900300c2c51250b05210f8282c10303100e83c3c60201c100c1c0c10320001c01c50740c5401b450302441c400d90703862040310880c0d51151700c55503030700301c001d01541c0e50420700c04070207501e4030900e0f110140100d007002c031400038100c0d062040320701c0b03007405240143c201400c0c00f80100003041c400001702c0070f500c142d65031650301a90039400b911035400c68080101d038540c40e0070001000440180e21907414141011038810900b4009e6940905440040e94050b4131014403200003480d0001400310480200c0c40d01e00c0344c0078140d40100c01004814000e80f0180407040c0c0ba10011501c070710034070401801101050218000203001034110039001141c5203080320101186000040454034074091061455000d825070030003054025501c04c0003503480c0d100101d0a0449411440d0704041d00070002e020383c100f0800022115904c940c8640303128000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 130925395 1250 130924145 130924147
    0x1021b01120e0a030e12010b1305040302010b090903040518060d030f031b05070b0108030412030309030c02090702060f01080118060b04020d05042628020a140c130c020703021311 78
    0x113800c02510224000c110940920f940050600c1c110005014a01070031a0103005d00f54803a410850101c002c11002e0000c404554031540f0810345d540e207003507000f03000380744080c09990795515040800815141c40b030501c074000d5240c0c2003042442d9a411481c42d010582505054140031a074910460003005102001030740140e034860225a00d5911101825840c1d10541c50b241150b40c8840c581a541d0007680305a0002e050301c034565400203803003a00070300070721840b07401c0c000821681c603400245c00507800c5070342c03000580c0100d08000c4660220300075240148030420080014084202079000002030841000d04220703251910000c06460301ea0490358218100c120820960503e8a0200500300c410b1414405581882200c00104a000800c580168001c030001c01134841040c18003136008000e00300406c0c00e50040e8110200401c007481940300c40c800d441e030040c04841c407581040200300c030120355100c4105440d100343d8580c21500000d10704150b80e0125024400d8808c9100030802800340502c1480070110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 130926645 1250 130925395 130925413
    0x70e0a150504061101020405030a08131802030f0a09031b240e0601060f12180f2d171312150c1803060507121d0c01021b01120e 56
    0x19001d005041036414582c0c8000902e09440c0c641c909074082c2c1e0044a900d41c0258441400181140b4000d20b16064040125081c1540c1c40030380103141d445002d030161080f90008200304240c1003072010f4591080286000f04241c852540700144404031018072242b80768a03000b40380c4240310034030301c1e16803102c40300c490200b00005c03034400c01c00c024007004410b481c203612814001261007400341550100055082e1b649141d001e400c0300a8401902c0a40011105c9440b91003a0101242c1c00303400d992a910b0281802c440703502810701d4940540510120f021101e0801048400c0003c0c08034480760400d010411702a60701ca0220014041107181d4a40c42103e800b80c44044003010012a209202034000f000b40c0c1c1001112803a41c03090b2480c034100f00807001d01040c0000140001803d03640900d42240041c54510b05010b00300080354126460b00700844108101c0c003102200000e000c108450040da42840505007001c0c42e40709403a45951060821418001c2419652110341c00030360002c800740c01200300322801c41b5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 130927895 1250 130926645 130926647
    0xc0c03050c01330806091c110607030603021504061b060605030d020a05010506010f0e04111605030301080105090a02060301090902190b09040506030304080a02091504110c060601080f070e0a15 84
    0x1403825004040030041804000030300850219080d80f00d410040c010700302c030342d60182e00007100803000500d20b418001c88c14503080340180300700552440b5580c9a20005001c42c15801004841820a403003409003003020041480219407040c420458104040300e4081e000c0030510300800035050a4001c81d404d07205241e4070b61030143e8001014a00140200c4c000c0006407115001140c1c079044039480b42c0c000c241c2c01d09501025003055400115020024981242081030290b42220b007000a184295a503134000b100512561600384621900300241c03100400c1e00318220380c0400e109000c144590303c0b182d075980c8050003e40d1580f40740c1000c40200f0840350705206417914844a00b40e0440712a0701d005514240000351982000012503054648402c020005900c5a40c200802110024081c6000030703001074049510f03803120301403103405410400b00c20b0b4840004030440380c94820300424a034104101c9009016130030103003a0809400c41d045141038042913680344082443c44030303254070024640710200d202130501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 130929145 1250 130927895 130927961
    0x207030c030f080c030105060a110607020d09080a020d08070503040305031621140a09050a06050715140612010e0a03030605130e12030702120705010c120c0c03050c01 73
    0x80d40301e600c0705264840010b400300c60701e801c125540120510100700511107440c1c004080c1c0103e02c03482c078201ca44c1c090b0f40001241461016900040980d0002c00c2c0461301d01d821920034009400240000c3c20700a08640009840c1e0301881c80140120000042800c00d0080500890b4051908801102da65104695080414403500c10081d038040010491584c07804001960200d41509650b8039030408103100c0d000c500b416801a403c1505002041c0c0000075a9258010b449005003516112184c581d0050300345216103040980f2203424062030841d5074000c1200751150725800c820161660740884c481d25195900400300c4400b80076243c405c0c900030b1000c044e030641040003507500507642004041116495081940d03882c0d980d60009802407071401139030305541005198004410300c11611600d05003005040346034404a000d44540c2d4603008562403080e00200d100d03464031012941040011100303d0300405030001054018104600090040c00d141c0c070035000244110f4030090300062035404617080c01c5070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 130930395 1250 130929145 130929167
    0xd11090414091c093209091b04140a020408010608030403051b040f050a0510050f01050d0903020304050d200d030f031104181b050903060414070902160516080718020d020703 76
    0x40012a1981e000071420001081801186420010280885241552005850841d800b0381d0095a90810365000120440c0b0ada40201e0004d000162380324280f1b160740d0300f0350710b140d0003c40d047d030b004020810002c0c10000b80c0c0031040300010a07400e51803c1c0c0800140c0900380e0042500520760500d01840800c0220364001c90054402041700d1050550714030920480d00c0c0a03c44560204c0c07030034401100a038080c0c0d04217006803442441500e280c2500e07080003403404590500b003650422803100310380742e002407501a2510790b8001101c40c0b102807205c0c0da500504482322281200304054440f040403403503000050a90300684450303204904129102d03090080148080a24089800b41510941e16400d005104403190b40c0e20140c0a010541da403034075041c0712594400c003400341502c2580340018400c8850f1000c1c040404003c000c0b4035443e519414000d00e400709888140c00c082c030402d501004003010000304034080704e8600d554400c000c0001f9818100a004150200010a0001581da410940d000c0304100b9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 130931645 1250 130930395 130930469
    0xe0106020c1002063603071b0b030c04030602090a03170705071208040323030703110f1b0d030509130903080901060b04030f02060d11090414091c09 65
    0x2844a0690600f2a41c030007041d1141800796034040f01480f100c1e8120840594086540004184010800f181052859200050980e403001e100340c40081080d10102103200140031003a08142103081c13440c1d05007030318800d81c0320003800b1700d90010f0016107070344036203451800454004015040842c0015031000165120345803c0741c0a010f038880100b01503400f606813207607564000245600b41401c6980e40720300820f6440704171002c2c80801001d406041020401482c81d01d00ca07031382c2c0055046d840d1100c586002c4c0044003040c0190040018540210303d00320f04401d92003801c890105400000d420180d03010311480b80c10640100d100b02045c88229030642002c10f0b1544290355900c1503940c0c0c00c5030030b400c80c0ca5502848500e03050030030040021605401d030042e500d5000404203403805904003454401c80d031403000b009104800c0894090102e1800784100900c0100c100310881c1c0502c3c00d14201c0f926454647c500c00c502c4d10300d03201d1405005110b0320000c00501440700c50590000c440f05013003504030340d007998122 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 130932895 1250 130931645 130931659
    0x703031401060807020d0302040f03081e22050909101503020603040503030f011a0f030606040504021303061b0e1203210916060f030504051002070f20180703060e0106020c 75
    0x86c5514443e1007164116000c601c03501403050b08655542616912050b00740c1c40c0161510f82e0302642036060401000282012590350074040f54030781c50204101155804144100b06480400c00304410215210005050345200014000800202a0480001c68101a410510101c204020420300000a41c004c1701c403103407040000c1e0390320300e601040c40c60041056440c1c00c80a100010402031880007554004c1c10062680c1c0c1400c0d11400403e013247c01408900e0482410384c01b040040c000144640c0404d9104d4461007900d0036001c1c0d0000d010500c030a002079000d081d420748008140e10b41030082c3c86c0108014101300c5c0043e92034004000c040f950581c0d4440c8140202600c01c94241c50a4030510100c581c3c90702c2c2e00c50f00200400040e0010b000080080d506070241e41c0307010303806c41d0444c030090003443c0c0324903840c1c1803000e45420050701480c0d000c4107041c211058150201160781d180c1041c2d107241145407441990a58079508100c0261200d588801d0300d81d40a000082141500400e4000d00c079207090310700c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 130934145 1250 130932895 130932913
    0x80a05150f040507060806031e0d0f1416020d0f1212020a0909020d15060f08181509010e010533010806040c0c0203070f0509070203040e0606070303140106080702 71
    0x2201c1c04041640c0081555002140c01c000060103010855070110300141a11800301501000c103860b04000c2e80a2045500032005c01803aa0390864940c14441180340740c03c0d6211401c190042c6428481c40c1e5440d071544d20720000e100d04640e51034004040542d030100502c08041c00c1440c00445404e00c400c003540110310f900c00540101500340c800d840303074194141c4e9040100751920304848020f5011807018554162685000001410004080d0300208402c0d5a4021100070408000340031100140100c07042005007062036208a0000032203815a29503054500c02c0c0b80c4614907124010002507683c40825400d182c200320361440300d1140d2210790f00c61526a90500c2100d050041c0003010910016408240003130042040c07402d007584400641000b5080004490206800281c80c2002075800000d403000300d840c090210f800c001c103204d6041503150000710706213402e00c0d80c100c01e010300050015009141c041892014507200750400f02d00103d5442103048156111200105110002c841c0000988100c42038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 130935251 1106 130934145 130934161
    0xb0304080a1b050d1e0302090307031209030f030e150c150606040e0109050106030b0102030c07060302071e03080a051303090b0f12010801060914190f0204080a0515 72
    0x42064442080c06005c1c07090006000550415006001008041d14001401c2003642d521002c0c2014020100b00220340c074608030b40c4040d03c41c2c20710300c512006054010507a01d00c1c207481561140d1030068807450401480c0300d0b805000140d80d009007400b80310320f02c0c581c3d282900071500802e841d00d41641e404c01c01c0e00c00c800030313006a000ca0303076205c0040112a0b0148520b40003488280042e504000c030746c000342c1c0c0e281c45441c4542014990001903600c1007140720446010b80d20002d001b010044501d42c00e0050001500300c642500706880c00303022440b01700010700702840040c1d040d52103400701802c01c01880d0058012030084001100203100683d100b41908000358040c140110001890924120307800090350556503094604a03060014007400014000c15510030141b480710200d0700c100c0d4200309400034490ba5100d10703540e0291200b0107041000100d84070105c25140c52065041d5298215 = true := by decide +kernel

theorem cover : BRFrame.Cov 130755395 130935251 := by
  have h0 := BRFrame.cov_init 130755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 130755395 ≤ n) (h2 : n < 130935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
