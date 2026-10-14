-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0565
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:28:35.312127+00:00
-- url     : https://prove2.me/submissions/d6b37c36-f449-417b-8db2-c69dc0995739

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 101438848 ≤ n < 101618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 101440098 1250 101438848 101438861
    0x209120105040203060703060e040f051501090c180b1b0304031208090f1b0103020304030207150c050c0405100302130209030d0509010e0a03020a231005071a010506040303030f020c0f01 81
    0x86080d205c0949440409408480d0709114049840307a54100250105200c1c40c0701041d21070146041c2c40d100014400e80030340d480c409070001c3c00403654400c000c5c040150300c5211800c0032014481310806e041d00700550481c0c40c2c05183c2801440c0564104140c021080501c141c400031640009a2420008180c10191401000300c030aa11948104055265242800208120340c0c4602907040c421100410740114060f40c0010415170540c03180001c0091030003c00b01d240c643c0980305a50354113000966107401d0341095064060541301c4e9080105200b05550502a0601204d5044403116050201419580080c3c040c4100540c1c4c14080c00800d4500302d50400c0041080d020260780302200c04d014482000000d814a0002079001150f00f84103100401d030740d042c40e5031075201c0c0d19001c150f4900c40e400050480000440b80500003000441d41c001049110829010b0900051308584c01640c18a00841e0b014000c6100107010140c0f01c03070750701a0b50342803a4100c80c40750340d0740010b0700c08489900c1310a502070002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 101441348 1250 101440098 101440103
    0x227011404180905011b1b020a06083402010609020f0301050424060513090c140c0c0901030c0305010b090118020906070b091b101b020a0806070807020111071a0a020912010504 77
    0x146d9000d55000f016540030750062a1780100301081c43c5003032540882d80142c0c000c1c1a0149100e0b980580200001c41c00c01034164540c40b82c940101c0c4010320f600090a480e120341c401e26150d030041c0301d1380903500d01a070180c03419214262800212901d4500300c13000342d0289002d0156200000d4030020500c2d33603002005101020000e9034502100350f60303204001c12203207904403404c0041c05d911003c00344540040000c01590148900300e40a5140440c0006d60401081c2c2c01151070041a85003001004020300a26001c071400325901003280d0701d881c42c06500e40c0c0510754400203040d400500002e1580e1400705440034607400c103241e005c162402c204605d070742d0b06c1c0c401d4200054800380352069080d132030314280000300c454241e6035140185181601c01e500100040720201c2e842500003101113002c102c208084c0348291200d548941880c00e045001030300315514000b001c0c110110800142e40440c10ba4400340460005944603a2011b0342c48806007000ad005000c80f403644409040e2201031a0541508554090750 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 101442598 1250 101441348 101441357
    0x170903090301230a0b041b050304020405060a030816030203130b1c060f0308090402040b0703080a0b010e060a08060109170706080f01030b010b0a050d0227011404180905011b 76
    0x70118a21a248009043c0500c0c07500d0342c00000070308203461a0802e8504583c05040403494884c03050303000d81038007d00700d68180044c9011003080b05600c5d00303008007604098141c0f0940740c82821500c03002498810404411356000e0465100400c040c82002200c4100c1c400100d02c0d141140c4940f5130440b10760100300101c000381c243d440e5200f0090110302c02c0000329212410890819441c5948164058210082003680150f00348800160700200307500070095644240c0d00c520403481e00c00c2c1c13501c4c22554040b42590400c00d20b4140f1440e19110001200d221000b90b0520306101e5844100480390068960806121140322004424030306c900080c8042c00c2e80c084c0c0d00c642100e50780e1542600001d400901c005003e4540300001003291400d00d60003058054154905103141648000100c0180d0b4080200c0700c5101c0700421404a00c16010021003010307100034a4002036401d8491059a1703d40610300907207645a2041c861480881702c25404884040d43c084028005a11288081c00060114100101c00319 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 101443848 1250 101442598 101442611
    0x1050112060c02120a030b01050705010c0e090a0203060918011d030406020c0306090706080c04030b090709050a050423030c0111030612030c0703060f110310140303070203070506070201170903090301 87
    0xa40013086031102c0c00780d0200401d0800510190071000307003195405c80c86c1448410481d80012030307000e00580c2e00c5191039440c0c007500da0306048184444a800180b68901061050080c49440ea41e43c15030207030040003078005081075000c0e07455490700400801c80c800d1501c0d004101d40c84c2e5003103000f001030030071104180c0039a01c000d284001415180d43c02211801c1c2c0681001e6000d1145600982110b5001041200410300385071b10b0340c0e6041a10141601c0c107200551103440c003084000043e000d295030141860700c0a00c00c505181c0c0c2d94103681c2e54044114201e1281d00c40500341000800c0068a00c22180403000780021207400e070141c1c400b41d10039222a401080c852071840c24044002080301d403580d42240044c800b2600d985c032010001c299a08002d0358064030791010b110756000800145014445072078044444504d00b9003c5900041c50a5655000e0303002889076034003598000c0b0700300d01121420356085958108610040750003080d05007001f03104990800c1480144000000640410740081c2d0080000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 101445098 1250 101443848 101443871
    0x9050702062d0103020603040311031b070605071a071211070c0602030307082404140907050915120c040203010303020609150f0a02160506011202130506010509060f04080105011206 79
    0x80b924102124201000385038010001401d1410007954428000e180035034051034051882c0341503900410ba11a102440702c42103d41002c42030003014024610350410740e01d02034072551907410109103038546c1200070206c0c2001411f09805000480d4403031345035030b00400c100000b903081d203000361f0818101a60b0740706142401081c000d000008880c0214220380755900160786a80f13031303602614402d4545001c00c0034180251000b82d04e860069102090140744500340c01d2808030040f40c644103542e40b20610450811040c032a50803104035003002301c50341c182d513501440007520f07000070700d41642c0001d4203410031310020002041c1343e400300e00b060240800e0803d03152034008030343c02503001103004e840300c2030810b000c200070902910440d4028090780703a855070303025010103650f12683c2c18013009a001e03040c14182c15041c24210f1074500102c44030661021030400c45800e02600081c1540a4518980e005080000e914803208050f402070381d00404958000b84140e68444208410404541004441c0d9605124a0501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 101446348 1250 101445098 101445151
    0x11061b010e0a050c0d11060703050d0e06070f0f02070f0e060108180304050f180406050a0b120c010513090e030403110f150d0e06090f0715020a0206030c040905070206 73
    0x101e00790018002e041884c81031003000b00242c0e081600301d8546208142403011500da000241070854020b80b03c4c0c58840b00106403100684103544001016504090b041014403034110301d140040c9031003803600703540401050310160310740b03a02504004040b8800074030018100040280252069100380d170b034100c0503102c1400d400303050050007603071003000e030801e10050010b1708003150410002d0230001d14040c2e07000c0514400400c804000d98064410680710001c10060002c14040c40b48201805e40e0740b40b00a0a031021816283c95070202421304018000641079031011070520400054800c64004102c04100700901c030703a5aa22510049910380010300d824000c0b03182080c190152204042c055401c4040e0f68460b0341259400200040400307541c5008002a2035070401120b80304141602c01004003001d0110329074544101a8032000c1885182a0660300306a4049001003005074182c07003080d103c2d01d500ca810700040c05190404048185884200860b840d400a0386600442602000038400801032254a1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 101447598 1250 101446348 101446363
    0x1306050f1603090315050f07020a02180a110d020a031503110904050f0f01060e100b040b0a0207030803040b060405150607020d06141303020f010614010c11061b010e 72
    0xc40400d824010341d030300d01103001188400c1c98403d00d02000d84644a076148406100002c400188195840c1c0410508001c0303942404c0e0005990300003060131540941c00a43c4031810804c0c211070420180c00490b42801041d0440144521003001c210707201d11480036040c2c001e4104e00c503c0d000007414140c0c8814070203c6039040074107481e0000c03410f000692a90003070204444000d4400c881a110b02040ca55045a050240c003198140c0301c0c1c00800c03110724080044018644c082d1480c200050007010410800b410801194215648181a81c3c3c441003108811303030502c032159001420003100041000200711281c40b0a070300c00d0804942c00c00980e02c40c141d5020141101c8400580c200e14200844c41c00351401c140e594461503c50000170480558510782c0100820050301c1141024a03880c80078810140c05024405043c01050000c01c885880d1804580f43c08580c0c440d698140140680a5014070400c6449440c1224014010a1b9948405040c80e40c03900140c41c62200e5551031b00c0f5091182d5580880d490703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 101448848 1250 101447598 101447617
    0x1d0703090213050405070306050c0c060105060903070e0408190f030e070515070222050708070206040209010b0306060c011109030d0309050304061103040905011409070c02150c031b0102130605 84
    0x42d490070745240700b40144000741c0260b805205400000000414901415205008072628561103010414015103090010380040e07218030300c00e20141e89180c9000076034104170380a050035180c035134a0300d05215446128200980301082484103070109040c0e009110140740200d1603800304244944102550344aa40600417240d0100c3c1d00c200c10048540100d01820f681c3c6e000510051208240ca10a0f001006ca90703428a6234a81d1030f41c082106e1503811000c40340d03200d5490b00250001c2c0c0703860740c00100402c4050103070000281002c4041400d0341c5480099902c45401c000c0200140c01100085200176080006824032034828407505001c04d0303100740104c0812541c08001182400d0510b14107440f03800c030051305030740c0030302c000c1c40001141e8a8500a050082c5521241c11032080d410405008001c3c400800140910120071000c0c401a1074040d9045551003200c081c82e5101d6008178203c90031842008c10807030150000b410703c07000310141980100044d041000c01d4003515a51100b05841600807003021 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 101450098 1250 101448848 101448859
    0x21008060109031202031309140f010806011a0705030a0201060f0b0a1704061e050103020a0b0408060f06120a1505072109080f210a0209060d0b03161d07030902 70
    0x80000900c0d203504c0c1400000c0074016039080c0200f011a020356034449503c1000e0658880d1105074405564080c4250011480c9031003800c0c660404c244240e580e40180304d1035035211450344000011a68850684140c03640c8901526500c03160954001e021300041c1c01a440e011009100000300300b491541140c401d207100f47c82d40f1001c50003075031926094180040066079074035226210200500d8204402d09207000d01c601002034607505600601c8003180780c42d000244000401c10040c0504900060159070000707440505d100a83e84007008940c2120a003144400743e881011004c01c10009241c6a6020902c1e41403001c006039681d000007220039410f41c020701110620140c0e08410042c4c03983c1c00c581c04d00f41c042d800c480d20b40408011070420039030041c44184c2e03a0300010300d00c45030b115103a0f03c00590498181441075040076105d2001558174440d004c07126190740e42e01d109102c0c1644061002c80d074003c2c1600a402070305ea5460074001d6850f0030010308030190405000001702e026010b407042c2007405401825 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 101451348 1250 101450098 101450117
    0x9070501030506100c1502030405100501060c0f02040b010c020406120b06040624140f0403030e09010833070e010207080706050706051e150a0605121f03050303040f0210080601 77
    0x1743d90441000400b5225000001c8049440403058002140035921600040c50140a00c40700c040032030704180c11080030881c141c14900c01040309440c0c90042a501150300207401440c5c1001a00ca2a240c05002904a0300380b070310001e02c03030343c0c040b01c13140780c40c1e0080a85805542c1c0b007008000442d002c40c014060010404a0307500414020701c0da60400c0c001281c01d10510070490065490229000380e15042c110640000d020300c105940400f00c0700300c01034180d131880060350400070102d883e18155041c40c280340901100001c800014100345400381030f468280580c01c0d00304898020106000a2141e070301510030518009001100043c5c44030448265540d034508121003662047c0c043c1c500a007898222180c890720710801d070444010302500690240c84400c0b81140e80d84140f104a1560354020010f105041c800303c030b16083c100e85038580c043c0d55500104035002802016800c0092a0740015015200100420007001400d1540030142c900880d5040d1000591a008540c890811900303240061010714 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 101452598 1250 101451348 101451379
    0xf0b0907050f0d050f010512010c021b060405090103050303040c0515030417040e2e0b0403230304090e0105180c040c0306120803040c0801020a0f0c0519080309070501030506 76
    0xc0c1400700c20000b41c1518112256001c50709544c401c0d540000d4610b0b00343c1c0108410300e0700001016070301000800030b0012540e00c003c040d48070041000c00443d0031411160211899540804a030b0180130010109001075840342841030343c94000321411510030704100e402043d03502d862460b18040741d903803100c25131a5a88a85d03410001010404401c00f440f10705000200b8040101450300e449484402501d04031454080701902440c80c4d00c52400640048204050200c0c4150408460580c0d41003007120285030035034518440d5400c42c82800400c070380004540400c0300c400540045610b400d50760000d014903151b0f0b440306440d00100c080d2600c603a500a454428031030629800219a511403400c00052007681c840707083c1608511101700301c0c3d548900108210420503040c9004020b0710070704000b1030420855171000380220000700d68a00c24880c4040460b03080000c00c000e989800c01d2880c4900f81e402d442c80c40c04040507003090b0f800e00e0035400740070404541d6511a2185034070480c401494040b0020059 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 101453848 1250 101452598 101452607
    0x1b07031d120a150f14150916051e03010806070f050301050d020d0203010f11091f05031816030c03030e09150f0d061416020c03071406070f03050a030f0b0907 69
    0x165101d000c03e0b91900140310901c5614480c502080301c0803c1108000e00d014004c0f12039100c6108684c910031260351050051200105440c11125002e03070810581e96a1035901486011002c81c89000317008000000105007600041741080c0905035948404908000c008030030399590109000d0150017450404030000076240c0414500303000e0380042c00004240805410314820354810101066a800002685e1074a5080041c54000c0c4110350000c102010429030900034100d20000d80111030010050b00d6104051205004c901001141403002c89503155a034902101c0c0200c2d0744c4425004181d070ac203000c5071981441a501c505c12510b1035200000c86031407400700081f117650000400d402c1000b02c12a140054030a04c200c0800200022114441d4603120f007480c0464a461010341c1c2c02c640100d001410161000202d01060395000043d19a13103200100114200c2c3c0a064009010390004201d59402d2507080b1000b000c20304010b1368180300f030040d484940c00540d080b00080907040030501d0005400107108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 101455098 1250 101453848 101453873
    0xf121505070509030106060e010e03060112030804030219050705010807110607180b030c07050708070321030902130f0501080a05120c010605090a060504321b07031d120a 74
    0x240c01d245083c2180d0740c0100b4219009508000701180460007001215071700310507003181501c1d048009104560408401d040a1602064010b090020b0400460100f500034040200190041c0e95035490354041801c2a40d504e0b0348510803d0702007031580c80428103032407003481d402c42c0c0082d24030000e10058039462821140b40e40d440317065085040710b5102c049036028405000794040d80090b0b9901d500c2d19032608046003002081e621080241d801020108005a100030f41100715411035001c2e442800e6030360100384c01a0080d854000d44c4400640980d8601107038540c80683c0000a100b030030405680c8621080703035642001c54010340f696104c3c048507958010000002c14498103004000310708140d075440072640345202a110a05416112142030006003002e02c03d1003000280d0302e5010002201401c0d00c500b000717100c1d0058200074201000024040c07141b00c80b400e400140c001144594451040c03c0080c00c00040340c41d40e6002c0c0318a0b4041c2d84a42c9086d1500002d45200100030702110340e1140e80d03000071f9251 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 101456348 1250 101455098 101455111
    0x603030f11100e03030105040608031201090f1404060203040b01060e1804140f030d0f060f0b03090c1023090108010b0313050a06090213050408030118020c01020c01060f121505 77
    0x928642410751041c500030241083d034404021901c0e54142010842619041e401800031980140b100c0260900046065411942d40702c100180344400c0526150151071506012001e01e000c80e000c2c40304000e425401188924060020100d49076241d400c01c031001e034a92985550301c0110b8a11103210481d19007503080d0054460a0781c034984643e00c503030140c02c080403500e1181082e0404503034070400b4900c1d0b01a14040724003e00041003000d04000c582c0d007068586021390310b4110b401000007502c2d80820000300b52503500090400e10a0300c4036080c0245840c861242050b016001c44102c94150010202541d940e410141c4480b05a60300348820f040540d000202807502e211440c030307520404200e013800351141113809250049840007a500600000203401545091100d103040204000710301005c3c1903905641c5080e41c4e0b483e00000c0c1460390710180c012400b003000c0d25440018000b88451056104c6402c58131041e94070444540d83e41860901c55238030030006802c0540020000141900c0c542c0441d51004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 101457598 1250 101456348 101456353
    0x110304030c1205120a090605070f1a0907050603011206021e04080a0309150212090301020d0f0b01030524010e1c0c050109050604081504020105040302100302030411040603030f11 78
    0x5590352101503441201e5402440c1e40850407001c0d400340801070052460001151241340c1c5407000f04140103144030f8861142d0002c1241c041384001c10020307008655489250880c0c4100c0340004040c6055404010070380e4445082d110701c0d200080c036410b10801b40c9040341c11280500140d40144e4884001950248540ca00000340c0c2429442d0000f00190190028000407001001d03112414a000392196003507810000703941c0c12585001840590014500c0305001014422a48480b1100042070290050080342900d0794240321074044c0c01c03042540203408001c001da070203200c5600c60050210342584c060103202e440001034001a00d107540500e0729148510405425040080c00200803442c0543c3c1d1b002e012150420f16001c204400d603848000b881c00741078101c48161419150141483d900e0350356501004441c0c80c1c1c000040c00356805007064038002c680141c0408401810040c00030000d42c4111412140440101c0c50b1034814200f520418082d84d9240d00c1344041d50101040580d140d007401340000110340f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 101458848 1250 101457598 101457607
    0x20405041b06020c0301060914070f030209031e0d030504030c0605060f060d0209010f020d02030a0e040912020703060c05070c030b1305010f0e06060405040b01060f0c021903060b0315071103 83
    0xe40003401801c000c0c4042e5014000c803500c0d5400b010b003511900e41c00080501d0500e07098840c7c0b45d42c1d00e603045812500600b0300d445031201c0e911013980a4020b810f00d0607814018140300444c1c5003c090804001c40600e030040d030b07005214124043e4219041500c0290005100c55101c1c03000407030503480309412034401480b04605441d2540090101d62000c0024805681c003c202c0c0a41540c20641c8015540c9140c0050066003213100b00080d500c1c0680810001008101b46030b04a95440301da02c808030085c0c000b80034524003600400040d40d502201c3c4001c031240343c0f404900801c01e0344a0003d071552164441903001181d40303180c403000003440c0003038207030840c03010020301202c0011400d1255149503091000d000c22162000e114990800780000c00a40c000c5040004000006800064a80c155003240c104441c0201940d0000c44180031003180084d000310095128400714a2020403890403644680018082040d4410516441e12081e0a251481800c82e01c00b103100e0742c3c001e0003030508400c00300c800c0700d052 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 101460098 1250 101458848 101458883
    0x70f0e100905120c1c020d0c08060f090a0c150219110a0e100528030303140106110703020103180803040812070504030b010e060114191107030c0302040504 68
    0x104110036020020480c1c40908000c2c5003030080d00300340c0d07451800b4080d0100700c41e2a004901d54200342c00c008030081d0b611559000c11581c0e00035286100e150410a071a91103a128092142c0d2914280c80c03110013001003400140e011a00000c90544190303000c80c12140161510500c500305654503003030b11042d401556201d00b03403111604100699180662101505030f104001401f00032101354110f142134bc03020004000d01b40c2c030700403241012548103a4a0000b9000f0b0450702448440c0c2c4034440c03181d80c04002500006259041d00407291203c45c84c40b420b090341c0d82e100003e60f91022103468001c0d10313822a983c1080590b020f13510201010207110501034224031590b440c48aa0b42c000c90301251590350110302c1c03180e66010146055030010b91820704a10701411615540c0c1024130500c034440300290401c000903d9a48102c2d081c100d140c45070440b83e500c0b02d40e48074603504c080c00e41d1b8007624000303001c0c0e085142d4199000200078086a40081843e108a420b540910018260040c0300390b4403c1a01c0710780404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 101461348 1250 101460098 101460109
    0x180c04030f03091502070501080703060f0b0f070503190801050913060f1e0f060501080103020310050705120115020c0306070f05030402060903070803040f12030e01050a030e0f0717030c0303070f0e 86
    0x4c60007266406001d4080c10304d80003400c45400506803400b0107281410902040210810300340c240e03486d4510840e16090040d244c09003501c100f201c020103d0001146134003095903411118200302c2865103500215a0700c44080c840904822545d66507400011043d020210340b290b072224500441c81036020484181918810301d4079405d4040010b16030b80d45103840041090300d8441c000c01f5050900e00110654511380000341c0c1d1380340b414149014650b50750081070102d400303041162840322440c5282880da43e5240380190313600e5003240302c5d40c2c00340c0510000d0402c01d14000c103002d4400d032625220721042e200c0c0312008031900d07080104100d800040401c1801195a000c004d110300814544000b9036660b0f041101c400d10301190b590140c45001c80d5007100d100000d4110501e0507080600380f821645803040644104c1c05000129070703c05041c01349043c10300041e41c000c90180300b600d940351106202c906109002503902e100c0e010508445810038000b140c001072060700c00320440c45151030030100811202c0009007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 101462598 1250 101461348 101461379
    0xd021002072103080a0506060f030a0b13020a0323070c0507120506011e05030d0f03021303060c0f0801051c0201020a0501050c1b161406040306021602180c04030f0309 73
    0x42002d011007080004041d4403442d07040d4003040d000000d1040c0e007403010201d0014018084106000d49000c40003d031500c43c03691103100c04140042900c09400780002001000b98071960182e40000d0401d2400c0d22050200404121617600b140d0720f17103200340d988140803140c07034403221002c66042c020180005084070301d14005010041c0980007030625545801c948984801c000c0030000c5844841243c200310701c0c0c0e00400c41c00c0b0300841d58104a102c031007210350200c00a20a0400e1030031070b400058004010b00840d40e0040302c41c00c440343c8a60b103140e00c410318103035146642441202e03031146031109c1c4d00340950405880350209501c10f00449881d02102c1e6100b80c20341d101280d0301c489020011450410308418089500032a11004001e052940142190305040d0000c500070a601030703654001140c01a190342e0121402141c101c2c40c01c54480700520195820f0b420450002e922984e61820210244000d06802d140600807075001c19103400e2443d90b625040041e5104140e0a10004540c0014103880310719818 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 101463848 1250 101462598 101462639
    0x10207060204050a24050f07060f0e06071d041a0a03030e10030207030e0910090204080a0b010812030103110d0f08030f0f090a02060d0e03040605030a0c020c0d02100207 74
    0x1d40c9480c2444240650040b20b07904c0300300d00c28400c400050f0114890703820642a4101403a080307981d001102d04c400154481d102000703007410f00d0900c2c01010420554407580403c208881614403544590b1021508003c3d4601600310413812259840950310340f6500115985240d040744c07181c409071090004419402c590310941c040ba103a00e1025415207050340c00b00030280005d0608509001d01a140180400840c5001a0042d5050800708a80c0002c0b00485001068021415581d90303403210400c1d81ca444440d001280d41140ea1400801c1c48000462110451100c0200140c04d5a103903442d0a0604da40b031758002da800143d5054004040b03021002e1040400307000700c000561300d003040700545e1050007000b09411410004231041c044404000304901404903011074105803105820311500c070040c10991641c25461200080000b51940c11a01940c469882103004006070040d40505a07145d0700c411504035030000703030203a00d1801407404140d900d40302000b03807048525040e01e071a5000d003807940c1f02805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 101465098 1250 101463848 101463851
    0xe040b0907050301050c040e04020d05010f060501260403080c0c1b030c010f020d050702060c0607090807231e090f0a180b040201031d061003020a080c0f060c030c01020706 75
    0x1003241184042001c1002020243c0080102d80760a040b842240d0146000e481d001d9600340000c98155074910200c48201074200c0000c00140c2148803800004010700e00c10b85000c03503003202800100103d14500c041004102449030f0540b5176495400726000080200380000d0000c01f488186414801040000c1038008444114a1500c2040c0109460054001690360421100c8020f10180541c08615201d40c0790340f5040143d2680ca030391000820501402c085600e26214080c20024000da000c000c06046031140000c3d6100e5585881c070001b414a4540c1500c0c0a11280102840407030420355800581c80504050200443c511500018a180c10a50310310074441040303400d0110400642c4121b00d0400e0001c81400700320512a40c40f00c8280500602c007a0506544100d0048210b03d2103000444064240c010380d01c540c6000300c403c42d003030f40c080c1c00145d02440344802c0108100b54002514500b00100410403052001010108415a44000480d990f13602041c030014105220034006055080d114600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 101466348 1250 101465098 101465101
    0xb01140d0225030f140304230c060c0c0907050a090b03060f120a0219030203100c0306171515030307021e030a06052a0d020903070308030c12011403031b070e040b 71
    0x10300a103170300c03003405015003448820024840001d004014034041a030110304141610480e00001c03c2c00c0c42c0042118070b070000000105001c0300d98002c21041080c4000700c035001c01da600c1d0400c1c225654011080d40c00007081920006020710740d41c45016541c003032402003040c0b4440031200082982c0c43d02c0c19903140348950003c264a011481c14030381403a01d44084c0d0403802e8155141d600001c2d9540d03104c0e0304a9040e5960b074180c0141c254401d402c000080c15485610750151210400d030340f0341d16626940c21000320300b441000b0030000003000700c9145401900400460900c43c05800b0000c500bc21802d0f040894032050074201e409490910014020a001c0c180c009940c0c80e000b0301c419005610031890620303405040b8080c000415640096a4092405180068445060501081c58103400d0f400140c4106400f000304059071b91004010454550005002c644503603a42c03002c0c80c0359042d00312010303605400501c40030445851078440c101450392030300e0031a5007982c0d0307411101a050300d080e070b410307a02c1c5d111110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 101467598 1250 101466348 101466377
    0x10b03010f0218010e04020f04060207080c012303092d1002040609061b0b1314070f062d03020a02210d05040303020d0509010e010b01140d022503 64
    0x8154607002224440961500809003a801990842c14020034180004500346035460345030366040e1140c1e45468002c442d951512804080d41c0c4030218400d246640c800c200c0300c03030400e502c11400c00d00980e41c0c541c0c604004102d551025003c41c0c00c001c140124901c00c003d40600300d000380700400ca055004d41d0507101007c1c05507844050a1030525a610410140100001c10003164000240402c541140c500710700c0c0c40100c070302c0704003024100480290410364104180131800c040c803140011820310400e107550002d000102c00c9034680325144624403480344106001c00000340502c0d03020617001d04540310000c0d5096800c407052000f0182110b5000007940c041000004c06404100c140b800c035160300305056110700700c40b0050900d48901d41125207001e803200c011a0401d4040d4043e520416000b64042c031991801d11002ca00808003018081c0301c40d8249102c00e07007954014158841c81c0c001c0d20180c40c0c07508410035404800395114207003009140614250710707a10780d00c91340414502148641c1d102001e244259 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 101468848 1250 101467598 101467601
    0x70203070e01060e040203040c051908010c0503012102090a020315030708070509010b0c07060e0f10080a05010b180603130c0e0a060b04060e0103090203010609060906030203070b0703080a09020d0c08010b0301 91
    0x2038090720702481c1b040080c007012a803a2203103107003203400441c1c881444002c0928006000359203584058490b42c03c1043c18000d854120300918140c440c1c180002c0a51104290400c03c0000621f801a4009090401068049415400460b403140c02c6100891450340440042031070928290700c141565004484144a2031074003d442500600e86181c0b001e0801120b0002c40303481c2c5110b8414001031002c0c68808514503100c0e0f035030510015034000e040715104000b0701c40c050b16800d41168608580792030a000800c07107106802c1581c03440d0002414200b0601105400d010041c0d00152040041300001d80c500720010303880180c0c02010b0081c0d8146600c0034141011100240c07086074001440389101404280309081d8080b50303144c1c14000034078021900300341d24004039005001d1a08030f040a14105440400e071b4458940000d41140d109400310b582c400d50326502203a8134060170100074001080103020030705211264000c00003540c00242100440240c9940344244105241c0c09000750b40d441e000c881159103000e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 101470098 1250 101468848 101468867
    0x3031b03050603120a0c0b27030f040302010c060e01090f03020f0607080a1d0d091d0c1b01060504051e100302090a0e01020f04030503031909020303030a0b0105070203070e0106 77
    0x45060078425400c0010000744c80b204850481c1041160128003030b2040c034850b21b80ca810b80c2d50820007405041c1405900000c43c201d150544440561070720003028008a030020489444d904807906250903d8116070044802c40c01d022019034040e502d54844d800b6812081c892282031612640103540302c08003500e0b010b82082241004028160410010010101d8000d0895070b40403020311070000d8444401c080501c8170440004812010f44160b0007658091070304191100199610b006003074818581c240e0000e40b0ba2082112900017442050100c00171210000e00850440c800b00000401c000351200c000c18201c0304100d921000941c00c030f80d0f01c40401400b5003e51038102c1c0c1000d010014131801c50b004600350341f0001d000d0300d90559036400c100a0640c000c0d0305644400380c418480c1c5135519502d060a5940741c00580310b044446815902417003d10009100e2a044160f000e00a03504503680c2e0028040200a0f00041a0501c5010400503005070741c103110b40c0001d01418014201c0d59410003034000c120040c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 101471348 1250 101470098 101470151
    0x40b041a09030d03020304080d06030c080f030405060d111e09040b03060717130c03050d0305070503010f0603053d060c0503070b090a081201060f030c0c030815030a0303 74
    0x20204001401c5880104001080340198103015a032510769280406161081148178200c82e07141c01c4020080094031440303402110b1380c4100301e513660201812003d85a100307510899501400411120010000c01e4228000e1000c2c816001400e0403d240c3c05402c0c1040c070403c0c2602c4008000507170700c105203010312400e0a00d003010340c01001c8500d0411000382220426480380006040e00c480043c1501043d003082a40c49680029000c46e03d83c0d413803400c036a0300e4106001400109041c4030000d80031a2092080ea030403107180313501d0311803500d180100642c024003000e041c002414610703940302d510101203004680d450390f607401104a1041000042d50149419582045c03042201d500c00840104500009075005030350420b02c0d1101903290000303114601080c0310802403a1140100e8510283c0c0450054035040740e485445205128135824012022110021155000710340c4043c40140840e01c41c0010503401407104840c0012a81c58000003480c105085008800198682c210079602000c07000c02c9809840 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 101472598 1250 101471348 101471399
    0x60503040302060a0b1212030405012316030204090c0c020922080306041d0304090501061403040615080f0705040b060c0d05070f0c03060506091006050a11070902040b04 74
    0x1003580e4001c0d1510b002510301c448181d11240900c10903651142c406900f506808129250100c018030100841e407c12102610f065280c42c3c00e080072800780303008a51040c0503040c0d01046035030381e802c15000c0c50600800780b10101582808082502c003880d2003401542e0f401600c4118a90040b4410041c107a00002c0c642034030380320f4a80c1464481900031000404081c1d02c5121b8030303104d50f42c1d0800304006080c1c960341201c400c00c000325042c54100006c001030098440922090100daa01c81d4802da80c601d5844049140c82c000801c002004181030ba40a4200d0070341e2012a601d40301c0c0d0300c0380c160f4a070619560710700805410041d420402440c0c1885840380c41d0909440c0c49003404665110662200e04d48030300d8000780200003800c17074208581030701480c25644d448a603007031040c1d460781070801c01004201e07103c41c01030b0149c0c404030f8801c0c100595461308603600c079070782c191811420850031140c1d00c013491541c103490b2080381004122904280040c001a208588a60313442d13510700000d40c100030100c15503006480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 101473848 1250 101472598 101472601
    0xe041407080706050901020109170c060c0a05030402040923060a060602160302010e13020c010b0a06030e060a0b1201110c0d0906050409020f071202070801050a0b181b0f0310060503 79
    0x5410100b0000201c0d041c40c00d02c2910380300070078010307405030108640003054001900c4102d2103185082010b0305030307020f22608445159031074040e40090f030300c20000001c0109030140005001031905400c00386138a0b00c20480e0a8000901c1003c003448403009103100340058020f2000c110486040d132043d10001e21440c40103010080b03884a000602003103500021b8100400d019205640b82c40e642d2042030340c4400c0f01c80440d83c41640c0d50009000345007491300184151041c03580018071905c40d010303600c0310030f08003005000e9540b50130019400402c0140701d01030b08845461440c01c00107000788a1404800c3c44605099907a100658403e4104100b03c030504050040c9040d09020040d400000d41d01501c11f9260b00513034a040100303a4500714060303144028646030000905000441c0e000c915001218a41c100030f201d2034807100c030324400340e41c020541c094100d40300c1d0b107544034400300c44d182a40e00080942d108644002040c08108219801100130440c0b401c80001841048850005e0040007052149082402d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 101475098 1250 101473848 101473859
    0x3030c02210706030903090e06090a1a100203030108160f030b0901151d010e160305040218090604030e040908040611010b060a1205060307050d120314010e041407 71
    0x240069040a4020600c81c40054281e08101e000340000c032a66104a6411954946006020b48035028085001961107a40010041d01c8e4601d174501441c00103114051b00d0b91103080c4000285820004000c0c90a1508100c1c0707903e440d1824800410401c541c09582d0b0385d818940003501e417141940b840900d08000e440c080191842c070309100b41c1079a9210b800080c44c1d450b10040c1501401c440d401124070343c0920303180040d0f02d8107054925100050840000165680c0c0c0e41020039004600b21201d203409400c030703162585494802e90001d51712920007415442604c0051841400d801d40840d881d60656201030144001e1540140b5091034221040320305116442d12507036003103128092442040d003440000d2920200d229401e41210801c100080c2c102501e500100000070900c2c144040c1070550f584c0740070041681d906000c61020709460300a05025901000ba50301e2414202d090020002095506c00320404140004800f0034000c0040c003241d405a41414104503545140d8520700428035444014104031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 101476348 1250 101475098 101475107
    0x10b0c03070807110303030f16110c06070320010c120c0c02010c030509090405070618142205010b0d0b0f0904140f070f06020f062809020d03270303 65
    0x307100e940014141c0c1c481841d850128004901611000d030305000200400c0625404ea85900f4825510345861b04498402c115060350130040c40b446000064111007501c2c0440d003881e200811019200f8900607040300303500e074280529070f20400c403540d00f40d075114052184c00316400000c440c0c2200044404009080e00600060100c8403d144001e0500c0f487e02a800c00f03041c080c03002d440ca05580039001100d02e2030140b40c2151240068015880800c003a8840c1c0d011600c0b05070019400e60b14890003261503445048204a04070704042501c80b0107540c0032414608800c07260203250f001307000000005450340080301000d010f481c05404894060307008607a44081c150741c0c0c0c6102c03132f4200703401074102120045011030041c10300c0d5405110b0341e45403040e0140003071051400d1a0703603c1200e4040c3e00303803099403a0b180750094440e0300940d40c941050b58a803800f0f00d00d104200900110403883c50b40c00080e0741040d035020803a2014401e005a0101c1e18150408900441d041070720000c81d0b880b1203104007002d0542e6000351 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 101477598 1250 101476348 101476357
    0x60a0608010302042007031107170a110a03050a030e0907030b06090405040204021603020c031c090b03090c100e090906191d01090803011d0f132612010b0c03 69
    0xf131049803030f00344c0c000c1141600401340c0c0f05104022400c6503518000d08015180800c820f940301031074450340000040c85050102c400985100d448043c0c0b240104640f1141c0581902e03441d115441640c802000000407401c01403244014401e4070b8a14042c10424100a241100142504141420000034403100d035100b00c11210080b1080b94006000c4d1502d00200300240a840d07040010402c04041007003d05400080b1104040d4040f4110350425030307200d40344d2403003114400c082c00110745d43e00e8003400b04500c160069940540d5900032183d022112100180341512051101170200b00050fa42403ca41803080700298440403803001003a1504124a2038803030061071030000d41e03500d544c40c0c000483c250010a40241171104410081c03003161030505110440750f00078400c800d042d10301100107516041d0007144861082c481400c40803100e0741e44141c0000d240c00b105000300c402c00300e80249001e400b01c0707a40045070340d10b4a00ca011519212a0315002020b1036042c1c0040100c01360900200b10b20240001c00c56 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 101478848 1250 101477598 101477603
    0x1060e03120406051e1b0c0402130303080717070f02010c110c040207080904090302010c080f01300c090f0b03010516030e0a060507030c030b010804020307050613170d08060a06080103 80
    0x1d645d5407201c0c004041e4602c4001c24180b5048500150b80502c1c0d0f078000c00100f020030030010035039041c00d5030607040000724891000600400d0700112401c0011900032250b0552041c01800e002e0041c446000d8030850205d001c540c50320100e100c4080d062803131a424400d59400c028681070000750410040240c030307950101088150303c06e940000f056010045c5400c161202048060f00c00d012020a500c0d001e03028010100320000043e5100000074801c1d80075008032412100d0103130f010035200d140ca04140e881c2502c007840c001c054412404045001440301d42c0c0c0ca0009040322030001407000243c140400589203120039052081e0f06000070f00c030078000480701d4402c200c28242000507440d80304071b41450504914820180038980381404000d4401d405801c24480d0781c0305a581007000b4a9550019500c800c0700341c03000b94069201007418802810101d00070000800300c40c10445880342d4404243c15486900c0c40040901e030040c9031490b0079142c00840054021100321203480c00345e8140f1000902013a07051002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 101480098 1250 101478848 101478857
    0xa0e03070b0f1b0f0a030c0c0f030309111201050412020d02030d0903020a0b090a0b01090c05030601030b12010903020a0c0801050f1302040605090106030b100806100e040e1501060e03120406 83
    0x8541843c071101d1400440f6860922034544070341241c140001d103604640b44117000310703007000e01c1003074224800d0081c002000e40c071002c40740411500b03480840082c005044100c0b94102420700700d40c0b895a5141761002540380740350001c00c60b0300e01843e21002c0181c01d51b440b8010365021040181551f9008800d641c10411540000102002e503070404a02e4803000a6010b89054242c50600010250226500b6440c034040c80c04503103140d07030300c4d00315000300e4003140d509500091061012031425032103a04200f8030580d004107801c104408250055003143c0e06920110090780c0099000c0f4100142d15003400010080271f0300800070b81c03804008590b81c00f0402041001181c00450341d034000c55031154898000f42c40050f143c502990303160480a0010310480340c80c0c0340711344c5291b0342d120001c5100e02c0303401c0c1c03203002c019203c01c20140c4102002e0340c2980360b15a805500544400c01ea4201c104104401130410790b8035920702c01c09500d00320026107042400e605050007038104003010b902c400101401c65080303d946151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 101481348 1250 101480098 101480101
    0x1804020906041e0306020703050a140405060f03060d06050705090f0d05061303030f0c08060f0a050f040b0402070213050609010807050901060f0e0a0b090a080703020901090207080d0c0302030a0e03070b0f 89
    0x14203c1c0c010384030341c00081c480c07840452214107042d031180280c211040c00da10b5000024101c1e4007255007034040c61141e968031000030001400c40e082c41d1400b07103410100c05070000400c0103840d52158155070045400c20000340300401c0480f00b038900400108825002030324240da5030310007034a4513a19603100408842d07450040707000b81f10406200e94042038202410003410020a844444010f11a19040d101980b281c0c501940e03c00307084c40c00070701c0e5004032080205141d110742421400d2101a0002d00040d03588a90b0a002c60000f6071900b44111114132034211340041c1614066082107081e69068002100e241e0040d41c0502243d03c44061844c191a9a414100380304442c0b003c085515290640c581a0060301a84000942d0510710740504046401111507200c181c0e121915140d54100500c00658070031242d0700104071503042503000b0b101940c0038030b5080385425514010b00c000d8410741210180002d0b4000700304140c0c1e2445114800d0200728810181d850b0045a8035160508180076040b00a810303013110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 101482598 1250 101481348 101481389
    0x601020a050d0207140117060108060402121e010b070c0e0a0b19090c020f0a2607030c02040f0606081f15021606180603020703090306050903180402090604 68
    0xca40e09155020040715600d0200b460000d45031402803081c0c0f24009000d802d0b2035959801202040d0420101c00400e9540d55a05401144d030040060328084c1c120b58200a1801c110070240707500d0b4850b00c684d0003e41120900446580e050480c140c1c0310150034a0700344501c400103821000e2400840c0c80d020240c10b407d40380c4100c4040144440202c0503884000c980c11041c0000002041c83d00712008010f00f0018081c3d2458180e8407070001144800c000d401440300003000805041c8282d4020030000c0042985589042d2a2603440c1e0010f40b0a030003040040086008603c1d0502488201000d114024032410740f9292000c0e01103000680104640512030001c12801070b00d43d202c20000340002d0100c04e030101c1044102031745030102580c5550642e0303414100400c4517806001845001c020701c04081c126185080310480c0250814a0128104a442480000402c889000b028020090716010b55951200d000c01000c9010b007245400c1d001d1801804060217a90f03030f00056408491512503003c0e40407a205 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 101483848 1250 101482598 101482603
    0x250512040303140108060414240903040e010605070606050102030a0f030203060d0228050a06090b0f0c010c0f020105150108060f010507020301020309010b010f0e0607080a0309020307081c032003060102 88
    0x410380c007080001d100c000141c175080000d02c0343c0c0554000c04081c1403940c90011440d803901c0070703d00716030048018040704501c0030042a4901e41d000c0061020703130741856209c9001c180022400e0307200000240000c5105001c6c0f002500c124402450240025490001d0016000d4001009030400500303060703020002078040c1c0c03160200f040d80c5950052032002c12030000b144440c00d09248a0b001503031a039203c40042194141999100d09a03106d548a8241d11850035500700040c1d40440d24080e5400024003200c50301d40001d004110360900d580e20303042201075441e00c009085500c020300d4400d00032280207250000c3d0740c000c030b0081e40122003a501803100f5a410001684c0b0b6100703850009400d584008100403204a041d805040300140c240d031480b501c405041001c844061900e200c0300c1d80402c0802c82e01340024104401810b00e083c0311304000c504582c0c00d0300081c0c2000e0183d40000141c1e0020130115640d24500c490400103500c41e03040c01c01407002d80001c00c40101042140000ca20403001000c1280340c0e008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 101485098 1250 101483848 101483861
    0x60509120105070801061710120203160602070501120209090105060a03110d0207110a031e020a03050a140c04022803020f0c030901020105010e0f04021009090e06250512040303 77
    0x40240b202d81004480282103410906c01c100c0042c0c030700254039002d42a0350205c01d0040c082030701c01010807424080706200c0b801e02010b0032607040c4620720303c8200e100b04001a100080003160050a0349902e8540050440c2c000c030100303c0d400c9441008240c42e25500c440d503285c15500142d44c0315886080c02d02e4264001c1c2109029104010808201e44981c041ca07a001800c07028400d00703251001041a105008028020b4000100005526007000a10030a1820b0101410340020456010543d99848141c1400b204450130340b12400300251594000340d0400208219000548045107091460500001c01084140900312191442c200e409661442601650035201c007404059503968201d403941c40c0d50387d005213051805035081600000ea4502207282c801c1c4140706282c1c4202d40c0c0d40da507900708000013003500360b10402d021002070045522002071045120b081e4262004044505149200c14099070b01d043c038824410740c40346500138a29522000380c810320025044068a035445900c1c00760041c198 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 101486348 1250 101485098 101485129
    0x1240210061403010b0402030702060c0d11040e090d080702030a08090c0306100905100b040308090102120a0f0219020102070308160215040302180c030c07110d0b040209010902070c060509 82
    0x703040e8081120800b8142e41400020210000c0088070102c4c0f06010a0307000448048000da00701c0c0d400950034001000040c64504981c1c140010702030750284200405170090340010407601c0c0c8080401080c400c080094950968803800d10411624144000950702c0c403d48441200300207020003c1044d2030410064000c0d400c42c01416100300c0e10305071807100c02c200c030070744181d448050074180070600030380f06400d2101c152008141a10300d0181591a03045c0103038840407a0300c2c1180f03d61080018400400c3d07024146444855179110707440c8450b520f000f45000303030103079030410f200c00c0c4000440010b030380015000d012694004601903ea10b54a0ba004540108258011390041803030749040c00105d07031900040060320720840d902ca0080d00840c2d451140001c0450b01c620094604002040150b030b080e4000e0503805101e0081e1603c2c3c24014004107503030703403511441241c1038440711050004510301010240e002d08641801142451340310b84919416a0803882024203010300041c4000c400e446480c0031641885 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 101487598 1250 101486348 101486351
    0x14030109020a0e040308011401080406021c0603080408100204350a0f060f050402030c1302070212150105060a050d18021908060702151b1902010e01050f01240210 71
    0x5030f031070444518100048808800241c4840c00104e5051000c407131032081b10506a55181160f41d4559480000358420481c404a440c051005440e038081c080c026880a14803e2510743e0b15949070460041c41c120040c1c4140703403454010701c4103210310301c0c0c90320403500b01c400850303120041c0c41099680142002e400044040140c0102c81a00050043d0084a5030945214060400600e175403841e90b0400c0305c03001d4a000b5895040b0200d03030341803444c001941c89031610304007100601e00703146503000809140182c1610303000e035001081021050140071021034014901501e405150401d03000f002060351050012504040780c0e00c0f004030a0001c8040c12443c1403d0340a0005246520880100c0c05889540e108032043d03446404001120a440410f01c500950400d01d819182d58803216000c50809030f4924070310138184428009500b20000e5005c5450260721150000110303400c5506d540360030341e01d0041201d0461540300380104241820383c414010030141409400c00b071000804400ca081c425000c44923107405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 101488848 1250 101487598 101487619
    0x714030a020309030d0801030506040b071809060509090a02090c07081204030c0209010803041503020904110a05070309050f0f0d0314040f05090109200d0f09081c060503071403010902 80
    0x40c0c002000f050110030031000c44110304201c40045501d0542404000c007540c000202290015420040044d0405d0441c2440e000c10950b11426420307a400d95484140d1058403403004006a081c2510b10913040f800300c001900d025070003a00490503841014081ca148182c00042600610a035079060304e000780001c1d4161803450800c0d04000300124a581810391040400c5400000da50a0020032a821038040510312138581800400a400130340100c05020341264032420058045440c21000300103030a95901c80c10744035001ba00300140401c5164100d2402042840104940c680d40d403060700f8054001240e80715818a00c500d02161090410707943c500d000000401c02084003d5250341040c1650015588085985c0c0e0700c581420559188946001d44d4261840c070072003003085104024101000d8410022480441003c5641d00f142c1c0084000c0d501200081040070b891050002e4087c404a40300005004880c108800030392200c28900c80c6040441c40e081440c00187c03401e420415543e40c00808a2101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 101490098 1250 101488848 101488867
    0x1b0f0d0804050f07140f030f0607020d08070e0303040b220306050a0c020a0c090e0a1703060f040c092603070b0901051806040b0402152a070303050708071403 69
    0x11500299402c0301e8901504030044405880050341804850b00078100501e400444800c0c80558078a16a40320b0f007500072800c1031089902c1c20001c4031300a1200c0e600400f40c03014400703c001c1070310741f014058208000100311507244980d4000150380691308035010b20f0b5900c1d81106058131600c3d0181802c0d40e882d40850800109000c0107500a6204820091007482000e10300c1404a0701c800142400071310f0749503c0d070b00500ca0070400d544400c034100c51800485400100d940c4607140c0c0c8080301c20003030b201c1c0c2c0400000c108250400c03d600d900703c00010b840c1171101648018014041d04e615018202c111030503109020f602d001c44940c91415143d0b034900b0741e90398000906202c00c42c203404481c840f45942c20840807455008940340c0d0014800181005049951150355034241d0340c82c8040c0080c0c0c1d000c0d4443e99503c00d25011a801000c60554201d0841e12034903120102d1423110045410b2401030703400c16001040826005400c581c1d40b1a8042020743d80c900b00340c50000d039001d4901c02c00c0340180c0f0001c1a00d007003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 101491348 1250 101490098 101490107
    0x615020705100302122205060c0a031503020105180f040204030501060f06050306030303070302030a09081204022d13020c01050907030b01050906100e0a03060c091d010b1b0f0d 77
    0x9640c410340ba02401c0b124214826010ba00c61180c11701200407040c2d00094011101d03031300c0c0c01804001407142005034001503c84500e000015106c000c00d084002a00b05c9901d43c042c4a51110440002c4150b4050751440d00080e00d14040c5005c000b01c01d03a0507000174075140e6185081c05c2d032540310040c011500d440d100d0521b18020300b46806124060114141c0104810b4001c0d0282c91282c00018015131031a070700c205045001c5d400181114024a40760060400043c100d58090000c1c1d11010000c0b0b1104d1419004000807480c143e4849848018420b400005a170000e81c072405c06070724252040401c22a006014800034441c2c401030100c00e5191a0500c050741d480451402e0859020f2400581c0b1360340c0750030810031540380076107020354400c00c802c003205805400750310403100c01140200700e248001c0d520340700d62007a14568400040090b01c100c1c0d060003410385400d00a407020b194001d01105540c144075a85056109584045010084048400d1410341041001c00032403402c0c032782640e041c030000010181 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 101492598 1250 101491348 101491363
    0x2060f040206090415090c1205010506040b0f070812071b0c09090201020709060617091603030e0d0c0e1609080601060e030328120b010221120414060105010c0c0302040f061502 77
    0x4001903421280940780d00712324040c80e81690720090203646040c0c03a00201e0b000c107030301c0303209400c17100603041c0400350101e60100003030a101c3c000290969824a40802c0082c02c0c003d407101c68011920140c6680008100d011104800b5280d00d000000361024540c00141c1c1b400303a495110018541c10108042081548100200a615058a2450b10588076116035940f5001801d144281d13612040300300b000030078810803004e0940c12015050a424440a0b114005010242d0b0404e8554288110034031458018240f12440408482c1c904030100c113080813a40c54540d201071140c1410403500c0e03075820b006a5400c0c0100c405100400c0f00c203550340300102225540319001c0821240115542007200200080307680240c424a2034164060990000e010701c107040803400d00c0115092404050140e41901d0111408031402103000b1041c2160310f2096401003483e05005030004c4c0e0404c004608400000781c1608035650075640d044401203080c1d2400c1c0e51050080c0f00b140d00c01d80d003400e01c110445081540209811 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 101493848 1250 101492598 101492621
    0x2091903030806060c0307061d030d0507020d171501020309030607090312030c0807030c03180b01090b04021c1e06060f0206071d130605042a02060f04020609041509 72
    0x14683d90b5280c200206401202c01c52041c41d001000010002a071550040404032800188401c80e0890345241515542110014081942c1d0b24003c8c040143c0e010004e9600955036840c2624201c032207100c2c00140c1c00ca01402e091942d030701c00c41c01c1040300c0e0f00a005031404400064210b80c4c20b450b10ba0b1300100074000c10b22099900381141c0c00c520342c62520070b0103040c038480030b151107071055034030340c484224020b0038100760b090205a0303951450061285d024003c0ca0380c070b80c018a51015903504284140080b105840c0403580f203244108880d0004078031030414040c00c0800b40000080b0702d0782441080202d0b00d0004180c62105280c09004103072507400108a180c803100340e6003200c405a80725001605c20880100610f641320804001404c01860013076102003c40900542c04241a40c3d1180820142e95a25031140c035625500307060303100d013a00c2d03545000101050707904c02400c4500f0145101c0c00001b4015001a0003681c0005e108280d0352078640205007403100c08085a100140e0315000710000300b0003030bc000c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 101495098 1250 101493848 101493857
    0x120204120c0311040c0f0804050f0f010b040501080106050d030c03030905060f04150e0c19090203070206071209030e0103020705031e0c0c01080f0601390c05030610140102010209190303 81
    0x31064105441800d1702042c464480c1c0894000058003910050b400400441d01e910454010543c1c0080500809583c0c1c840360b0004a140c4408400b040281c541c144c11040d00f80c1e02d015020044d0360340e510b603041c410390741500300b0740500034160500f1070141104903000307802031203810140610107842041d4248a103004140020192981e03244403008e8a05240e800340b400d03480408400c11a14001030060b000080d5480b003000c005660f80b45000070380e0400c881032405038000381c08104111382c1084504c010000039000c00c001a0103559405002c050b0450380d114105640030901504002d402c108440c1c0322405000d200840317142060440700a540000c40e41d00c07843c00342c02c0b01140c0360b500070800d0710b0060384003042c0c49802c0c1da00c00004580b800c06d5101d00b080e6070b46886503440104044001c280300741100b401b0900600c0711351401c0c0f0400c00101c80d03110754040c2d0312020410a41e16203621400003590a1100b40c100703035102000040340a8065a0b45c9264886e01d540d0005040e40e00d000401401c81c0e10a454 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 101496348 1250 101495098 101495123
    0x206070311070c06030c030216050708061e0a020d09021309020109080703030206010e0702030423042a030b13060603020705010c020102120a0c031503080c1b01090303120204120c03 79
    0x580e6101c0d030040c65401801000300401c00d01c041c9000c0c0c1c00c4441c84074180d1800500380350060b203002410030a55082552190400c0d0400c0c811180d0601c484c03075026648094224620311541c0c0d2100710404020045503a4950209003081c0c810002e07004a200150010001c00c1c5108902103280001c0100d110100d0120b4181c0500068105010030404112a0113801801d15a8031b060704460018200405510031804100000304d803505000810b03a001d91241c0e0044010881000306000840e240b401c07084100f500f0910384c943d0b80d40145241d040319140b8602e03002c680d90030301303c1c04601d410503440f1803280e025040000c046504c03503050f8040e0080c1805034000380b19002c02e8020aa00300d1282c0721409501d11840000551181e00d19008107000302d13241e16000408445010401d2000d5a244c0c00c1203480707110001d404d45003040100541c0303c0118031031040c3c009900c0710b4400600a8105c03444010f00303200848101d0001d20a042c0e05a038001c1805811612041c000f51510360301c501c000d40412034481c03807200b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 101497598 1250 101496348 101496371
    0x204080d031a0a061b021203190503060f0f010c05010507030e070506030606040323010204061706010306050a091104050d121d0108010e040204091a0115020a050a0b0903160302060703 80
    0x4102480d0403401608941c02035041410132a000b1000c400300e1580c0411744014900140c5a941c600c20600b00d1190207591506003895103044103059440171030b13080000500034400265039010100f000f16000b1a0303007405540c05000165003010801002614035480e006c100140560503820101e100b0801c0015500441d40f14401c115140c00160741c076070340084042c003040c400200211080e0b002095440c1d034a0880d89480302039542a0b03407190f001000010180e200c804041102c6964a5800403800d003014030070716042c0780c0400d1800059128002042c1d440e001220400300b16102140c019050142171034141c0d0400b0b060203120070881169a5000503000d5041c5e1038980035841d0701c03c41c280e01c141c1d1003401c0e07a440c058940701d541c00041e10070b80e8016a1f0b20160400580300000f18407044820400d90483c541c5400e40d140f0000d031880c2c5503503080d500700009040000300c0118070010b0090340030b0005040d9031144500c091441c014044d101031111051298071041c15000581d09201c1e98150b038044c00081d40c0c6a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 101498848 1250 101497598 101497631
    0x10617060f0120010b1206041707031704050102042c0604020a030b0406080c090f090a02061e0304151503030507020d030905090a02030907050a14011112120411010302030601020a12120204080d03 85
    0x2150041d2090104003008800409c1220040040d0382c001d142c1140c50340c08403001d8080000054600f110310340e600040403c96084540c0415500070465010010501010710741e090828000810380346c800ca03400100700c0041e90081c2c1c010140c5010141003000394589a540c0e00703681c0c1c446500c080d0b1042c9959800516451024001e485c0b2911180300074281c1c1e80c020341e080c8a900e0300310b020401c504d550701d2404030100180301c001540c404d0f400707400074010340d40125290004442d403c2c4441c0d0304103074160700f003031000c00d4020040312015581698aa9040c1d1418101140c020300d01d40c0240b940180d0341401e000060b4059000365000d28000400e071900b41d9964010045249003034480d509079003030401005207496026042e00051071400c04162929030807402c01202440d4800c2c5150360f840d8020b54144020310a071703040c4100e0a2a42070070110302d1800d0000011756a2003d0b134600602c2a14020f402213105482a00c003640b400151030019501d941e282c89041e80c07594030b01d4a503d00020f00e40020382a928111 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 101500098 1250 101498848 101498851
    0xc080a0b030610060e04020f0c0c0411090a0308070204090f05031810080c0a020f01061d01150c12020304050301050a1d0601030b22020607030e0108010617060f0120010b1206 76
    0x414524510b604d1900307500382c0f50b0785040340c0c070345920503400e010704101018402c1c02455440e0f0304001410034140d80e00200012039405500355103c0840c20b010814494440b010780300c0c2602d4001c030b021034854445100142c0580009400101446a245032160070080000080c2c00989580c3e0700c2c000c0281c40e42014041403480e90401316000400e01d50220368001c86080040c910300300c003403068901614000101609442407640b040d20415200440031084403241c03200e46000d00031050464904401001e0020415491580c000d8441c010009114240500030001c44004210182c001d004502e07091160900030a8640b07200400e040c081d00080b0543c2d9408034001d41030ba0781c01064008203898500c1c0103495010403500c0400420700d140096000350303075030802408005120f9528001c2d1f1010b0403000408a03c7d042c1d10041c1400010340d00c4007401d0308190401a84004180e4158289410900040740d01b2311284040445040e148110100f0b03101042d00700c0c88042d0402d6414846e10413000a856036184030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 101501348 1250 101500098 101500111
    0xc080c0f0d03031808041e0f030204020f0408070f09050106080402010206160e0303190f08091203060406090207060f110901081b070c060f0207090209131e0c080a0b0306 74
    0x1158060400c00e103015070540340035a00900c0e00051492010501c0c3c092010150001d40d800207010900b00001d4030002c13101010950340781084400355182410200301030045010003480f03a90085100340010413090300b600c00500d1400c040751841541d81002d400040d11a000e000c83c00e80c2000004210b041c010110180035942c107034000c044941d01c180d90b10510300b40d03140d911002c00a401c1c1384103109a500304042c0950100000089440074a0400081c00d52040b1141d44005d110b80d803000c001c0c10100100741a1070500c980002a0390f00e9031440001001459650000e400d06407001c0344071400d20429610404015010880c1000030751007100a4030b0a80c01512400c45c00140c0082c00200302c00000900014246440c00d0801d0400400d41da6042080d0300682041000821402e003100510313070704001c01c5004150005003107280c02c80d004003284c03000340e00302180c101554903020310010480b200324aa48111600060421011041001c0100840400e44200c12294203003100b2002524002c56550701610 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 101502598 1250 101501348 101501359
    0x609060305060f09030f040608160c02090403030e0c0406080a02040b0a0f05131b02340b0a090302041d0606060301120215130905180a0c050d050a050313030c080c 71
    0x5556411542e030350f03803000706000000c2c0014014540c1d031854003001f44c40a8406511000003620700041007003000040388066504002c45402400c01503101c1e8150b4541060305481c0208281003c0c00600346086000841a9000f5240520005141002282c0040418400c80741400700540761420404401c181c1e001e0740302c01c2084160b0801c030614112080c503094400c01140418051280422210009046041040941c00419603202c10842c1d200f114030010140401c0603007072038001004905044124044c102e40c1440005003e1021400760301120b001b1680203105200340450508102c05c42c01d0350b54003004441c8170b43e0b0f0205401c0e20304602624142c554240c40003000284075020080844441d034801c2d1000042002a10030b030341138114400c009007000d00c2e80031605092620b4401101c0032115001d041a4000b80840000141180e13000001c8901c21101140207500504110f424036402c0a0002d0040c80001130101d2210441d10004040728010000d00e641640d44240440c0c0714040c2240c92a40f08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 101503848 1250 101502598 101502601
    0x901061e030e0d030209040b031002041e15052503231602060307171003020f180a05090c031c0f0f09060c0305070b0a050a0e010b010e06031b030a050406060906030506 73
    0x214805d6018001c1000010008911140c080c00802d08010340140c104801c50340000c2d081c840b00d00c03400c0071102882e0301c404107001e415190510208070071032008183e1040000001d54603105144069204800305070004400c1c488244903d009400d003180700000000080e141e07061b41143c5464101600c610140900c24079850001c95401c1000d0f9600007001c4900b4000905210f8100526800000f4031030010543d42003070b05030450040040241c00701c10128403900c001420165203001b168019030f04021440d00200307107900c901d807265003840c1401c09801e405201c1d10f0100103030018812440003611840d501ea2040b000c540d480112600c800c1c445582d00442c2400e00c080090034851a100020540a480c00ca810039039296520703c1d0340641500c41e848a00e0700c900a000703000003244200030b00c245150008011420140c0e001821078001c10f00058032511010002980d1804041084c642a520484c505680ea2801d0041903008103015030701a69070301d00e010004500b480141c03050000b80c0b500100100000d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 101505098 1250 101503848 101503873
    0x50f090105120106170c0a09050601120906180515011401021b060906040608041b080a0f020d0203061e0c04030b1f090204081b030607050a05030709050901061e030e 72
    0x10002600b95030700b141d0f5a031000010800f020050a0700ca032800e40f00603240303802d001c00030008120700355040311624901e00744c14800c80744e80200750703402e00304880701012815030954200500180401c10404803101e0303450716074800b045004520441c1d4440075800860680c0d884a00203c0f8403182c61100e10b0147c2e120458130709540d054480a8500060f00900c3c3c2c2c1d00d40594000800c0e00f9400c103034004030100701c0450901042103d0540a46541c000500a501d44180f4020700903694080032140036244c09010380302e510035919898118040960094205c2e405800d048020b0008400010703544107014442e580420342601ca0a4121012030b6000102d504458641080e107205800100094000c5142000c0c8001041002c50024100900030b0300003030301748488455482443c0e0030b01041440c1c42a0004002c024040d130300315082d034084100500d8480c2c1c0f203585000040d81c0e138000c1e60304115841034a02e000002c1d07095100101c49401005051035801c8a040314030103074103540011a50800c02d40080c42d42a03403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 101506348 1250 101505098 101505109
    0x10e030307121e0c030b19050f010210020c06040b070804080712020f010c0306080c01051c021e040803031b0a0c0210020a06060e0703060510050412150e0a020a050f090105 75
    0x1800e03542e40c07100240c1c4050010110700002e49070041c0d240d61a48480c0c14502c01c940500c40c056514806031228960080e0302c04c5402c00000c031502689110716205031174413010380d2080014242c4045504011550303940120000e540e1440101c400716840c070103140000711082d1043c100b160003140e000c0c0ea96400c01d112641d17400d070b89c003451041d6042148074408041c1c0c1c5038002401803610226003510b00103404e07810062840d00349084104084c1c1800000c100b416529035894079414050800040b005854100b08002c0425520b00d070081014210f0001c10301142c880c101000441c000e003190000015001030f0114040d030039001d0b092030100810070488880d005410a854000e40312280351040d191030840075030b1100e04442a9800c8072400000c01c40030810740640511651000c0c141c01c0b01c41003804800b0407001030861045024001010f11110016400c021402c40f00010101001c0c20a2000c250603c0d059951450340110030781c41024001c00000b030381d040801080e22428000b502d0305007182e00302028040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 101507598 1250 101506348 101506367
    0x7050312030c03040f150b0a08030a120b0102030c0304030c0608060f10140c0d0e03060601080115030902011704031d0a061704050a02150a02070602120313051c03020405030f010e030307 81
    0x3110b030b0205c5440000041d00355021880b80c242448000201a00c26030207000060520b030b04003c0941e8001c001000903283c1264181940340204500482c2d240407140040b0b0035400b03040c0d041c002c50f01c40814003204005101c85035a0039281999154649a52200300300984940f041c5001d60300815402d124015040c49090382c02d08030400d88400c00d180c40c800d0b0b10f00a1410752800c0e1101d000a0f21002d14044519080c00703601e400c52424a040110b43d418882180c41c0500c00341e40000a05030b07101c50030000c40e4020142c81e442c1d20100141480c4034078080c2000f800c082c070500c0320200c0c0d0707481800000d003031032503d01501360640d0001d644140324229102d101d600b0750800503009649034401c0212440040e0f40310350021080c0d003030740100140c44502c081c002900c1e10416400190a5400996030300216044003030a03281d05c00501a8400c07480721050070080d090078440c181c5a05a118060414a0344c248c254000b0012a401501250341d0050020140c9003218000651450305800410100d24800e103e40e1150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 101508848 1250 101507598 101507603
    0x30e06070c0909020a17100609380402040e0601020d022b11030f04061103090d0206070303020d050f07022104030f0206040b070605040308070e030601091a0d0804030507050312030c0304 81
    0x490a0301d13644400401619001c06228036400540404007c5615000390001015550003e0021b24007540d4110500d882000b4140701c00581c060500e04080000003c0451180000d44115a43c2d82c0742d810301000c2c0707001100c1c0b0328094403a030010b0310059440007640c3c4071074000716024440403d141400300c9862030810400132003007004204084c0c0043d5401d1008003161500706804507030751845d0a4001d0b003000070410070401075402c10b0011040a8a0328074270030350401d50403100c4540c1d9042c03d150a500030702480d80c101da00302d49000100700c3c49240c5280918000c00e5141c0840341010804e00c0e59a111070906101d00100420a102c2040007600700f13501100310310310083c20281040e0700c501c49165241c11420090315559210030512060582000b8445e80240480c078242d030308070100d031011a036510018490a0002680c81c00002a0a04510300c003011049008150198190440c20111001d802901058850380241310f000503144c5000241d00020728041e03c000b5045a45041e5194038035007005000303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 101510098 1250 101508848 101508859
    0x601020703060e0a02101e11100608010906050c16170706091101020c060414090612061006080609070c24060609260a110103060315020c010c0e0303070f06140702030304030e06070c090902 82
    0x1211032410b16005103000b072f22102c80000307040080380c2009010f9803c003501011840001300040d1a81500c1c070441c80400a030013250004040d1846116100a0320a9040140c1480d180030384000410003900c2d40040703440000d0b82240c141c4e500c0d84041040c5480341d4451503060001407000510b030f606014030f815a11000040440000c0c680c1400d07401d0070084211103004810281c5801400100c0e08140b081d90000da082c0d81007070451625110181420996280c040c2c92180540112105482c11000603117500001e10800d01130555105005826400203015030740b9500d400c9a901c50b4649a040c50200d150311a24005245c0414586c44200c0040481800c40e410503403509400300120312a40207410138a00301c268016900c1081152031400c54510082c14020010360380801e4210b07a03000000d0310f14081e0003194404d0020350034900640206000090440f95070b05c0d030400c0010803600031000d18032a034001c0e190006040b580c01c0810440e44102080100b16075070144051080466540c8080d80d641c1c0301030310 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 101511348 1250 101510098 101510113
    0x204200307090f0b0f04090504020a05060d090302060f09060403260f010303030c1409150c0703030503090d0c02031207032318180606030601020703060e0a02101e11 72
    0x119169203600c21100307440810001141006600500c01d440030003000914001030801d807098010745014400c0e4816074024545503004035095681c1d0310104001084000c148990f1031110108040242107107450541c00350042600190407002e04020544c428042c04010703100d5945c441c0c3d020340f42100148510452800c1107031200020502c64111f940c0102b8240080030455851840c0050a8070fa0303d0440104000c1c030b00d2030b2105400c02140969a8002040b0f0b54242c002130007030012400c3d4010b10405642c2445001000028150042c0c0218040c2e28070300305544e42580e0070502a030308252060300007905a408200011606030110001d0f10f07005200e03262204584150201c2c0d40c200d10000b50320042c0c0c0c5000090040d084241900d40c21540c4102a00d0381c0c2421160340c0c04044003403d005040c5402900004002181a0b1081c881038000e940d01440030010916a10b0740c2c1580c0d81031001e012400798231003000c50b007442c03401040e0100e24026070b040d01c00c00000e0700c40c0e000c0f500f1694107400c980f4140f00e042d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 101512598 1250 101511348 101511401
    0x412110a05061302090106020f07090209180a0c09050604060e010f0306050d030905090106030e061504020c1204030c090e061503011508010509070611250e040506100b0f04030204 78
    0x1100a000706850700c5160050f055500400070060743c181e2110080d94001c110007203450502290100494554a40068a540c52000800d054900090403104140141c03400c04c140a20154040030f00c00906640c1d081c0059142c0d02480301512460180b02c0220f100c851100090798844e04c94800e24103218a03010901d140d9850110305525843c40c02240071502d030034014002420a038410038010078052500384090803200d000e642c0c9520010700014015161200e03501040c0e1215012078003010700200403542c07411003400f26961160898081256141c401e0340d000900d100550103040c2030000b452000d401d060700c03171502c10402c02c5510003005426549500f2422000b07003c041c0000f0052128000104051814000c0582002d040f50000d002384102c04550042003040010038032419055491340e45503145051030500003101607680714410300050031081008116001c54000d020302c3e0a98461706a90341c0328048070005005e25500300030300f02d00c00d01081001d41780c10f41001e000c140c95040c4100c00d00c1d5119 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 101513848 1250 101512598 101512603
    0x106050a140609131d0610030f05031e030106030b060f03010e04050114010b07060f060602030f0a02071a0a080604090b0a0b0a0803030903091c02060723100507090605030412110a05 79
    0x440050007695510340d40c400000e02c0c03241ca0590084c03c00703805006c0920b00140c41012414182c000a864001c0403d801c404004080044407403142d0a2203e010f04040d041d24515860f42c030034065080000d052240484160074010309031901c02c20703500403450550313083c0110021080d50060042e80c00350340322480180c1203001021410301800700b00c42c0e41650341c09641480380584025140c1e60f68691f01d000c0080005980c00700644800c4030721845019501c1038041c1c4100d2516240f90480c039040d1840500c02200405258028006881c0584461140f42d54500811044440c400c00151070100311800207551200107170300441d13600c2d000801051f030094445042a01e913400444410006500002e10401646044070065440d412a0031074800d9440d819408035299008002000744211f40240d9511050703610200c1c1c044020040804030b500090a031900c41000d04019200903002c504885800b00f1124801d1084a20681e000104480380e02d280f40390858a0b24030521a000e100d008420030390300041c20a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 101515098 1250 101513848 101513869
    0x207060911040e06090304170313081005010b16030f0c1a040b01210204020307030b030313060915020c090408040f0305010203040b250c030212070309090e0106050a140609 75
    0x240e61100365008610107020880390610074903c200c0e84440104911170f413002003142c0aa810840c070048613042501215841e5028140710001d00c018005c101041c81e15000884569008202100b4401c590342d80f13160031210701c5080a41c2682e15041c0c0c4008022a0017403000d6000c0c2aa2447c1180852125071100c0700004440034420700302d440c0d04410702c0f007400f140943c0c01d4090314070700c2d06c10400840e0900300720407a401e011a00a02a94000c4001107d550017503000d074402c1080541501e90b5604000054505001540601c10200d588000b011524030b01c0156481071807030b00c03070300203041c1600c02e0420480c01090082c011540d0400811000c50500d0b113281e1568002c41c45031001607103030b00302807820300012500101b0400c06c0441c003d0545281c50010040d000381c5202074242300a04602d981412414011160100802c2c3e0000040342e40070140c0c0209200c04646070100200003034050407040318240c5213a8414580e0141c0342c8101800720b0810511103c43d000c0006010070719112201001c075084d1500c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 101516348 1250 101515098 101515103
    0x4060c170417030d0f06211104050a02030702060702010c090e0c160507030512090120010b04050c04030b0c0717030a020c010912030f06030c150512012601051e0a02070609 75
    0x8039441e0a00c244c01d0068800d0100c803120f00f0300506007444042c283e0b601704140b11040003200a0384c0b9809210003a605a008684c001e84240035600d05000054080e51043c1c4000d00144a000005034070584188112401c6e2452a500c00b12100d207400c00703000c508100505411050781c0b082041c00c0e0743d44640e01070852100c0c8503e01404103146103042c00c90904848800301d1040d11370820440300260303400340880780341501469406003c066155400e5004218044d0101c4e0041e26200c140668042c0302c0024000b12440b81108400b00d546030508000c60307000e100e00c002c2228108003400001894104050750b40602c0b100401070034a84c40b013200c5400e56040f440283c461986051055190340d07032601030000c1a9207842c13418003d90340345681d10b240c201124443d04e007101382d00303e0b60103400303a00c01d02c1250f003051008400003090396110300707001484582e070320140700451412002d200103480040c09401c1c45415000d04101661010702501c5800d01d0380204403080e20365007041000001a007902c102e04a060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 101517598 1250 101516348 101516353
    0x1303030804030801150806010c06020919050f04021603050a110a06021c090f030302030c1209032a030711150c0610090b03070909060908040b07021504060c170417 71
    0x106801c0c05002e54a06800c6a0340407002068401051790300511410f8102c442841d190781505800c1c14039000a01604159030340c003504071a400c40519200901c400c0984030100c450f80c0c100c0c60580c003004200e2090500b40d41c5c0b080484480c100200b4020005440003c01c00c0c10140c000d0304144080340c0c00e2443c0b8201c11a203107a400300300700c02003030070810014007080900c1e01c0801a1a02c9900c4001e84024000801801c040e00000003032440d1a0300403d444a80880c540c460200e420b1104a082d00c903008018100c2a030303100d558460307070281d80b15420701d050850701e000030307600d80b0b881341d1a0f2407400c1070401c01c10344c1c05c6019402da1510000940e80101400c40307550340a09041e050900d0040b140c1c056551281001a08283c2480b0b00e684e8041780d40c104441c60910000b60740501841d00d8400b0702000c5c080035059000c082400181e00c1c05040c020320140740308480c2aa00c03405800d8020005005901581c80000c031020070140008081000041c000b1800300019424a903492054188401c480c1085c01034a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 101518848 1250 101517598 101517601
    0xf06020702060c030d0b0405040503030604050702010b1215070219060216080f09030105090c1503060f1903111c020906030f0618060c07030e01050a050408151f0302030615030313030308 81
    0x658520950703a51b480c0c1203d041c0814142234948603601d02015051178400d550b580041100c45000f540800d0351410043d2158140e10070188101e82c40c3c03404008604140340d01e8500248030a80b01280452850100100c0d4110300c08290300d861000750403500d201c11140100080d071002040d40c0d20003515852008044240da200911303c289802d41300e004d4032001e00c9603c4110a807003150345000c0140702855140c16072030b4903590313400001035480c1c1c0c90601345600600f00e1560b401c10045003810000c1501d00569014090000d94000d10414421941100003115203450720701005203400741010ba04060010201c0f5050880c00b2841418a40c09a0701e01e07259a038010302440c80c9040138406141d01001200f4203a0600500342c4000d0b00111030365464038100000041d00b04020b60184045d42c2c0a040541d04030f445010b5448065940180d0a5038649031685585030701c40030840c2c17440c00440a0b07c4d0302902415043d107512250001d44104e8082e11503041c0020300145619007404c055207001903000380d5412416 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 101520098 1250 101518848 101518867
    0xc01021204020f1e2e11070e010602031b2415031513021f0305060f0402280c05030f03060108070207060e09042f100f09030f06020702060c03 62
    0x500c2d48040d00030010a2402081c070807008440c0141c2d0081580d040448190002c3c02820403145e00036102c18150140e01004810f40c0d10580081c0d5000c1c901c807c035030714140c60b58010030b00c80d070003441458010380c8104180c680c0e07003c440b07041c0144144040c08540c041190084040341647d44030a40305901c0c50003004125038000b50043c130496680341a0040c00f954900c2603141e81280c0c0f0001c209554000703101124000f19150f4640d41c1e84620380050b071074501c07504521070003800303130006a50703141c421580c458854181d0301d85442102c0258140c506413030014034100c0000810001c145230b100013442942d2041101086040c4020040d000e201004541d8a181610026081c0d4002038564011540088028000c0030b411030a00e00560008950b1000f8603580c926192a9107024071625600d410039182c80d0040e0021a5034440812680884001c55400303a01601152000105002d00c0f00264900d0401c01c0840d01003074000d41a5400b51300003616000980d0003062556008082d00c0740c0591000481045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 101521348 1250 101520098 101520109
    0x40605010509010c0f140a06020a0212030705180102010e07060c02031203010e36010b010e0118050904050a1a011a0403170a020f1e070819030c080c0102120402 70
    0x504801d003030481c101030b0700e000000d00c80d00400c50300924400303c0358100b500303000303903444546040c0c80c006089690360003c9190140107500301000742c4025110b00c03492400281521020703a4400d101954070039080c4012440d210411100a55814dc107655980f079030010b00440600c40d40c0060021502c90b00c90101c8148141854950300b5101c0d007001c25001d000500940c40c5130108a5040913011501900030f2038401c4004c03484058501c2415038100c0400c0b400d104002041d041144505000d8035501c0240b000d00005540846500f00050303690707a0000c0d400d0140c0d2904584450f04540281c00302c0e0204480c03a55a40d03000844560122980021580104840900e0300c11074034045d503031103250324101351460b500d00d1100c550001c2c51107401000400c3c04070025100700492001c0c40151800c5910017402601d1500b403c00c00e007510060b507802000700105400000040000b0803400030b420b508502005510100c803040301d010710072a24180100b042011f05402400a0311486200544031056410540304110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 101522598 1250 101521348 101521361
    0x13060f0503030f04060c050102122706190c050f0c0f0f010603050703080306060702041e0e01020c0703110d050f28030206010905060a0306020d090b0906161d030105040302010b04 78
    0x501c240d0007003044030100c02071801990101e03081c078248100302e12a9407420a000e8000e100d01c1d038192103606000c016840c401031101e030f240000d20780c0b0b0114050301089580c43d241c0c1750071181c68400380b24123642da44014000ea4401c42c04c0714103e24100e824034051603100c414035072011501203029444150115510542803020084003000e00008000b6185141c0c1c40503203960a911025050b00c0000c40043c000e52070300402c9480b45a8010410070016424034000c400c241e1880500e8035185240ca0408900020305100326400c010b000002800c0c150b04d9540d880500400707034120560004800c8441c1c500003a0104840c03001c280111014015031281510300030f144d900c0c609090802c503e115480c1c50040303600440e0a9064545c041c07004a80b0342d4500010464070312941d400141600e1000455280402d0f00b98000b40301d0910a4540301c2c0300351110b040c107941d504d4064614800c5806801201090301d4051510505200b4246d0201200d60400100082c00c564048800b50003507512124a04c81f030b440c1c94403c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 101523848 1250 101522598 101522609
    0x3021c0b041103060f0f041205070516150302130510020109021e010206070512070804020a08030f0304020a0f0605031504060e01060e040c0f091a090d261206040c0e13060f 75
    0x80c3e0340d21b00003101c0c0812601c081c1c0081c01040d009410807080c41e12030412940519040412200660038046140500c2841441000c0f25143c0039865840560b1190084403c088540080c8107422400c0400308001080a0b64500c001d40d036860740d036403005840da00b034503624120301e0404c4c01c0101d0318043c0019041200c02002d180030018104040701d100011015440e410010500d000301c0030384d5031880460340f201d02c1e541000d44513110100d211204c81701c0c080010740c461031003690070f140c209565010300d24a03e0594014100818014000104030580240c882502040c3c0100042001070b66800320903507076482a00f0000c002214440c08001e0303400d15000c1c809500c10035141003003001d08030b49002400341c44640950380001c41300840e145030741005c00d400d40b2207040006143c002010020315110408546104a40c94024102e01610009803c0c00c001e950004031200746a4a1130364a03013007088006c1000c03103007250a00c04031404060890f21142c00d400d0024210400000d5420304003440001c81c0c00266020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 101525098 1250 101523848 101523871
    0x12091b0311010318241505030f0a02090c1e0a030605010813020109060e030703080a050a09090501030b0103140a06110c1009120c1a0c0706050702031303021c0b04110306 74
    0x401c00b036101c1c1e80c902c1c59459008451003803145444a14445c205d028010808001350910039009100001208204212201207045904c55030380485415101c10422001943c4817030508001802d00e04104028184852807000109118001a8608a283d00301c0e250f05030000c0d42e0365101b030001d035810000704c0d9001200d1480c031001d0151103900003041301020340507980c1080a40c0c07441d00380944040000c64043e542c000c10050722514030003401412078200180c000300040c2910b4000a50314894460075041e00e41090300c58600ea82940c481440a200301c0c50185100c3c410b6183c44008180300d4400c03410442d0410400315034502d1544001c9183c03844a204000106151400741e0000030094500d21500120328145041b0049290074002e100c01e001064807a14411403070b08100022141c3c1c0028a410340c4102000c1001d0303107030200120707502c3c050040c0804455a0903001030000d031900148010894030345c554220001503665803034801110781614222920880c003a02d0390542d1600b032003401d9201350071450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 101526348 1250 101525098 101525111
    0x3090603141603090206070506041101080108070b07030905090a061a04121103030c0d0c17090d020f0312040603020c010b0f060f0705010603021c050706030e030a12091b03110103 78
    0x70181d001d0034041e0002a42da0300b036074407240c1610b000b504042c0340503800400d40b544480290903c991a10802c0710b040315543e5045401d05581e601500451f8103a491001c0102001410004406c4056104800135024040d620305c00140c0740d9078000100b8841c0604800114805113050144440b003d02155801c0390600d0900060181d200c00041c811009a0404010701050302d04d40b000c24103500c146080d01109003c0c3e41c030241c0304541c0002c0c01000d414840c00c40401c20025402c000200e034001c1d15106030748100000d0b40f600141c940742c400341d910108010241c420020010324a039103158456407084c00400d401107400359400d4000c2c40350010309801962545800e401d200c000407298801c168401403070103800305080c0180042588203d02542c1d011f4038800c24514010407000c4d81002091003255244a546030200308144030380a201d031b800b80344200031030404880450555000803001c402400417a42c400076480801c26900101d5813821402c5100a8070390709604102c03c410000000d0380781410f05100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 101527598 1250 101526348 101526371
    0x403061508010b130f06080d050c06090c010f0807020f0105090a2d0305070501020415120507090305031c0b04020403030c0b07170a111912060602060603030406110313060c03090603 79
    0x400344400b20004c40001140405500d889000385440c1d00300004d144500381c5420440317a0840001c150312200f0030f0031180541e48109500d42d942010622250004403100c071001d00580c050301c02180c2108050040d039200d580070500e41801c44c3c0c4200c0711901d00e584401c99103c284003541801c80c8104000c000340302059035048008188a0402450050400c90001200740502ca001c0d070603103000e06040070030b0100b080c441c01c400501d444040345560710458075210106061a0042000204403540310700914100034215807198054007800e5140f00f461600e914419459685903c01000611311030717140e4000c3c40200f414500c00d01c1100400d0903081c4482c95603009448503d80c80503c0d8031613041403010070b05020440000103c0c0c002c82d444c0b88002c0ca041b0220b55038440d04900c84011450072600100540e65070340c40c00300e0b52440e099541c2e80d09a0410041402403a1040582031201c40700b8001300c0b850900c0c209406680400c8603844800012505c0004504059100c1d050900400307240c5400d21078402841c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 101528848 1250 101527598 101527609
    0x1020303150906030f0102040f06090b070201140c100504261314010e180a05060d0305090402070212031309050a050405030901180f0803030f1e13080403080403061508010b 75
    0xe90002d124644000000b0f10540d820080d6280c2901030760b000390340b101c3d075403000500050004e01648011410b1003c01042c01040c0c0d400703841c182d40e0140d440c14180341e03100c29220050b07070049a000a060141c040244039800080c007446000c0e034801c460082005501c0e40c150424000d640101039a0103000700b001c01c8500c10440c1e490401d58171000c0340d41c21903403010401603a1510341020781580010b2a01c800c0c1ca09022a075007101c1c40340c2400901441103547d10003c021041c901c02d10002c021880c14007000581d802c1940c00303020580d10280c6807200c401540d005a23860341d0454030502200c01681c9400b403180589034007500b604000c40080a104500345507807070310344a000d20244203041103c800f800406d49081030180c40024410b01e03941e50344050300e502c5602e442c1e9008482001c0004984408620031000303100d80c03030113420000349184010b5100e07001207840f8180e4100341a01d41190a200200100d1455001403008510844000500c001000c00d014440a0345511900341c60b40b41801100302504c98 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 101530098 1250 101528848 101528881
    0x30c1703043801141e15030a14010e07110a030801031b0902040602010e07050316030b0a02040504051006020d08091e1c0507050601090203011a0702041803180501020303 74
    0x100542c45400c02c1a8040108072021500038610799400c2c00703070000610900e040a0810484400e4481084191003060701d0710840403181c0e000741d0000401038040301c900860101035034010400c1040400d05020745444000942c0c03007078005101c1c20b007502d01800b020380d811081c0c03080d0105107035010346031000035900d014114a00511002c2d180003080c2416003400b00289840102410300f040046480e961605c000900034840780100b11071030301c84c48034080f60b60300c1c0010f0011005104003078003ca0b460704507a0341014820018210812140c1c0074031001c180d0356101e0240d07610441c0440c0300c0c0d01c00c952900c0c1780240b40c1a44105410248414842481954003000c69105d10310000541072550481024621602d06402006806074409110000100042d40840100f4550340114211821a601c070045030080303204c01e00c210503c030356141c0d060544541d0800b001d44480c500081c000903248031811081040541d2903201140005d0850340301d154410140c0c55504042c20003803001f581149054410b07491000c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 101531348 1250 101530098 101530133
    0x1050103090204180c17070503100b12010c0c02090105040515301b01050307210204120b0a05010801020c07030209040c0510020313052b020f040603030c170304 70
    0x71101c2080040d500d568010100030082e504940075010b096042c5200990214003401201d804244880c40e0120ba00049490039071390000d000e080c1c69840070700600c00510107400703410f4120640c803403002c007284000e05c51090410304a03224115500094070400c015100c050b04140c0c401e51902c1c1c24008103a0011441c40300e5603200f035540e8103c0d4018150041031084250001842103400103030156200c601c08250751052481e00412140048507650040d42c0501080724600c000903420844100e101c15800940000002c50800c010b2900380c0b0b0305440c00203402a0b41c026038030384c0f04440602c65240100d2043e6030040014200071414543c4c42e4000c6511440a1f00c0041d200307541000100302403101e2020f4020040600614101c01c00040c0c0002130f4503a00001045820402201d000060a052590810b8026011003202505a4810407440e903001e9240b000300ba0780088910254524580f65031003400d004d1802911094190722003403820144503038900f02000042c440c140284400680d202500d40900314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 101532598 1250 101531348 101531351
    0xf0a0504061506031d010c020a080307051c020703080a060b04030204020c24070809192a080a0516050d02010c1401060e091c02030405010c030203040302030a0302061e010e01050103 79
    0x49803418407030040c0c0540180c1d0150b036980d49400050058040d440307081e4207141d07001d04844950390100c400c2d08031051000303142c000d6085624410f0014403140000c66010002d8103006e4104040301541e000303904401c1000c42d114940c0080e5020925400c40380407030b4051500e07041400400c0c01d01e485804103008502c8000e0040d40c003c90300024000c0244068000c80107041000b403030303908070031b114400d81603020381d1781e0004900804080350144001085014420501c41c091411000541c3e03242e034090003018a10740e9030f030f250160000c03440c0750041403000d0050420100810200345c02e428580d040c09042d040c80c0d640d03d11414010040d82d11110703040c026032602402e00f021009405c3c20074903030348809102d0034502035281200228005680466030380c012842c510440b8004448101c00102039a0081003040c0941c0c400d02003009150710808a10407424402c3c41501d0070a592907021a01c1d0100400084004d40c0055003000f00842040740d100c4c0340d00541022038101075142c01e908583c0a074060041d40d0406 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 101533848 1250 101532598 101532601
    0x4050f060603072108131e0302011b0f1a010807121104020306030307080d020301090b01050c071e030b100e1b09090402011b05060f0603070e01050907021204170111030f0a05 76
    0x70f08004c210f10b064001130b01c6540c0e2003911104c2e80310502c071402441030703110b99440c01c40164200000e0800640e40c1c1a103c03c504050340340311400d403840401d1401c690603c5100c05001c00241010303040450104800501031095045c1440c95040080a402004000d207240f0249070109004c40095202103030281c2d00140d50381c03200c4001c02d00310711030980007820752400081e1000f100f910350741c0218100c0350740356030400040030f00000441e44c5100d55600700b84039500c22401840b201e20001c001400d84c10072000341c103503803554030795544e0b108010072100c12268500e8514100154900790422a0b400030201c141664403440c0505516418019a4001409005e2010003c0c00316401884850342e0311690303031040c089040d0340c0d18001c0d5440d00122007a02909801c80080744d000d0400003843d0b0250340880e20070601d075030b0905080c01040e19000300701c84114410560034000660303600000300082c000d5082148041c05847c0001425070342440182c0030284820070801c07195584580d802600031005d0000030846 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 101535098 1250 101533848 101533889
    0x150c080f0408071401030b0409020d060f18050c040b03070e010e10030c090506240406120f05241f050a030b121006090903090308071b0e04050f06060307 67
    0x10390041e6000440103208910f4081001e10000418950b0b04209a909120310810303442444162414460700175003041c0b0703009246001821942288070164021500001e154101c10b071460301103054554207456503000603031105458100740c0105241e9041c00d90041c80700c140b400c80704035030f480c505100720310741c0307000c00c6000c504031840d004081c8004540208003503510701c1c1c5981c01c080042c601548c07107520800185242400d0140700c3d032169440680200d001d541014980300d01554003180448540c41820364844420710b84041e5441f41c94099804410080666500f6414040d4200c1522340c041348030f0100b10303180380b500c1d00610245100c2c405d151701d032407501d4011040054029042490b4219031000020b240d240d20114006030707020360345140e80014000c0f1641d80080e00202c848440c009000a1415407050001c0781c900801443c44a10070f5101100a00e9865400d021094542e0019001a000300b0103010a11408210200d0001451350103005242441d00019689003094410350311994040000e4040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 101536348 1250 101535098 101535127
    0x1060b031e150607150b030106050618010212130302030f010902060a0309030c1719030b03030406030c050d0603050303071e0905092a0d060b0307050a140f0c0105040b01150c08 77
    0x154940b02910060b01d4650901d80301e141c0381c40110030410039a00d0884200780302d1505015071021180082d010519001405407043c81c148441100f00741948200409800c860020304020084401d1200300320301e0141c25441014140003400c0c3c0703002c01907030404d424040582c0e02c080840c0c940f0071441c2400a5850722500c0c0a80348410240c402503d0364810840c2d04000f03c038114020640d1175a0b8104000102c034041e1029001c0310079038840c598142d403091105002c000d005e036000700710000301d90030329a00b001c0344203010900f0f0780c401e50801c07103076900040203003c4075035040003204002c0e02d240704603040c51006046004004514611645100d0b42c03000002c5211022550001c0c40840c01e5040740342d006003034411301c0d07100543c081901c44000c00e00c0d00b0400504003060b08142c1380664207644d00c591800d07001480480e00c200c0940d0111f0100030f42000031203440c20385c000041c02c0b0303410355000210f214a010704001005d00c0050388411000300c0c0e01421801d03440d44c80814445015840001a601c2d0381d1344424814 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 101537598 1250 101536348 101536381
    0x90a060302030102030403170711060a0c090b0705010f0f0b03030306010815030a0b06150301031208090709061d0c090d02120307020406060915050a0e010f0e030303130501060b031e 79
    0x9400d94400000e00c02803542c02908600562302203511000e6039219034030704481c045a20100101690000b1001c03596180721508a0000d8071f8080c41e0120501c2c0d1907082c0c0120710b0344800c0085903d80c4d07581019100751440750042a80300340c4110703410003103d03e0071400b003a140c1c407000703100c50f0410411200040c0341500956400c0c000d11000b908135038001401d0700e4050170710001070360b075076124140011f030508091421030101e1b07058a0380030a0881941a038400c5c29641030b80051b050b10b0a5000e00030b0082040c101d28440d2030014010070381e0000035941401d400082040c00039065621000b406c11400301c440d100c1c103500004050f4150340b80b4422662800c1268114040e508000790301030300301080084e655a00440380003d6416403044100c3c211040704040d40e0b24800c000303001012070300c022600000d81d8014004d400541e4650b08160001c88041000241103600c11100e000e01a52a40b12443c00e004091140034080c1ca59100850701d1800c00e8611080b280c0380c00385081074169802c80008204034954040760 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 101538848 1250 101537598 101537603
    0x120204050d031b20040e030703090e040f02030d03050609060a05060a050d020909090601030203100b030a1103031306030e070603060b1e0c0703063801050309160f1e0b0405090a0603 79
    0x100c51031303030b2060f600690120b2450000340c425400c1c501484c00340388012040b54001c1e0b900d0b40364018541d10b41650f214485000500a030f03004058850780300d015031030902ca40c0841e44da05690000d002c0c80c3c10300802149407405004680a42c1a0034001d0200e0f4503074104440c40031409007412a140c460205a02c80070384120741c44c90b81c010183e0f00a10104a00c0090410b06036403088042d5481c44521031041000c03218000e040c03643c16846040c41d0000300e00c01c06081e004059000d000c0c0c9251200040380006070040366880079000a60752a210312101c1810f0125101506040c40d040c0501454100300d8295406006082c1440380b1441c0007421188025004507001e6100141c04c0d507a25642c0c9050903801006140002555004602440c5141c0c0540900054904054a0341c1040080150b1300444298100034042c3c590f91080f041340c51201c20212001c07100901e40409504891410300c09100002825000c1c103403d1030150340c4e0309200c0c0705948010f940c25030f2401c0c3c1e86500c55903500d1890201501055001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 101540098 1250 101538848 101538863
    0x30703120e0705030a050a0309061701060302090d021207030b18060c0c0a0b040b0f0112021e01112b0503101217030a0506030706020d0c08090415080d120204050d031b 73
    0x2031410006c005c54180c0c41c0702c2c0a62184d6000070798442d019200341aa604600c02d460100400501406000c0e601400a00001529004096600364041450030601c11000c0c002c0c0ea1250604004200d0b0100d0710944c4109103111800d40901152101551220003401d80c2c0080f40b404112805180001c009100d41e95811600d600c07887d080604024400740750950365001d081d05a0400450f44165490a813000c155014104d41c00a44034003098106501085110b541000580800700092510800511113021120348880402c40302140041003081c13420b4000700d0500400b0310030002040007010390030045410007000800b40c5042e500c0e02c0512400d68121040440c0c501005101b010801503008910452055085075041074031540143d90f6280c10844230720018007014041c400040d0320300c01804480f0310180010603070080803101c08812200da40c0150b012030b0f0115215050315580700707240480902c4000c0d000c44ca02030a002c0031501203151458054188500d1070f0303040302140038031b090a4070040d030401c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 101541348 1250 101540098 101540113
    0x80c0c030a08010f0902120415060306020a050901080a0902010806090a0e06150102010b011d060c03090301060b091306060c0f050f06010b09040b0406050a030f050a05030a051209030703120e070503 86
    0x10042c112040a0141d200004401000440c1500541c802c503814410500150101544c990382d8140411902540c0001c00c04c1d101d030000400a420781c00602600000e584030180c80f00c0030a000180700500044c0000029810400d0b01000b60740c0240b5034580001003500d2100c00750741e4146150015108001a03030240e40318480c104071600e1078079100c100d502034099009000c000d211100445541e840078031b6484c100000341040071418900300000344074a8440605503808c10150b003000031f007140c80552080e1941000064030010500c2d0491341001d8005d0212420841d15007021130040051028280c002e00d00420700300500140a810400c10002c1a0548216180c560310b9202c0308145030054a2124040c5041100e4902c8502c0c00380200400d80c1c0d0080c0086014600e141c42d003c0394940b03203e4058406026039a840070108200380010040483c1c3c07134869030780d200100762104180c114000c00c818159002400000b00107039200b078061410810707484011584900841c0e405043c441294041039040c0318640 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 101542598 1250 101541348 101541367
    0xc030c03030907050a0506030f0c130504020415030605031203150a090903020d110f0c0609060f0406050c060109020901020c09101706090f01060303120c0c0204050a0227030706080c0c03 81
    0x240f04400e44034240c815003105aa64014408039000644d040c04004000c0ca00140180b000d89005c0c0c10b0078503040700079109065484011a0881e44250400d00d801c0d442c40110102e4181c05000e031000802094004203440c00c40c0c880342e50481d00004c1c0175068501d07808080342c101595010844000b07400c41030700c104183d078070526002e540c03005007030000404645414940d0f0743c501008280b2030704610803400903001a403501020052903522021006034803190601041014502c2c0340e019001800054603a20780e6034060300b00241c50140140d1101c41103a0042003800c0650b64045240c40c1e2404041e5508003c5488046002c50f40359020f810818440240200c0300000000004803503004050020595403289499885075080c0c802d0340c0070244c007003248280101c801f0b0316107a10024a07030700d191a06440d4400d040c0c1c001801da44d0300742c0d1030040842d00401c2c4500400041300110395905281c03003600001c81c00281c007003030321004548182014044c103400007501010a42c02103c201080300d509036a55001c401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 101543848 1250 101542598 101542603
    0xc01050403080a020301120b04050709051f091b1b050d02030a03050f07080705070501141e0f04020a120203070909030302040e090a020a091d010e010204060e0108011a0c030c030309 79
    0x8032001d90009800d032000c149603207102e100f00d0b4140c551600c005030301d008540c3c54059080d440500120740a04c1400380004265469110321341c010700605540c0020901100314010780c3d0b2034103402000040d40703071034030014850f618040503592942172802c24420181307051984500d5550402ca001d0454020300da00c4000039076010000f480e404c1e54907142048030392100d4500d130715240003c5030f580000c80e80c0c10303020917400750042003c1c3c01468030441c004510040b594042e00c0c41c582c2d050f030302c40821402c01001c00100f600900102d590041d50549403107078030320301500040d034034010070710030700000326031445440c0150740b001c2c802ca40152905946c01d2250b07640529008000358824410100d14402060100d4005a03011441d605101d0b00109200f94643c142110741000700241d0400c5003925442a0080200800a00880d9004155a400180c40303928046010b055003081400079410804030b6070050001c0c0310000c5048000d03c2d1040983c548542301d803007545107035105403001202c0740c0c0300200402400c881d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 101545098 1250 101543848 101543851
    0x1170a0519060b0304030302250305030a060b18060c07030507180b06160209060f1819060503030f03070c0206131406030405060a0b0a0b0409061412030a0309080405060c0105 76
    0x11a40701004507069528402201d68500900701103020400110300402e201c0c1c0c000e01008046000107400d040e0f0300107078071003e241c00b62500310007007000401049641c2c544c80c41400028034200071410f240444a0240105440b80c101c03803140304d80d00100f4008400d0b001000450055584002200d2601e6161640c640001072120002c5d11410b09080c1084103c1c24002d09958001203ca001c0003010044c80d401c0080402d80144002d070052502c0107078980681d10820b1440d41e03240c5034800306890b418003415210100b190b0012888045041107000c024039203000084600304008080d850382c49444a002c2265940390b85280603602090104a0b400174420301010b50b0116880450000030300f8420300c040c40420300040f10090201c0c0c2000c40003e08250854001c1052000000c1030700d21810707200c410b04920b6403c21340180030f07642c0d601c100500c0101180340810001480c00c0354500b1036a035906030f84c03e03175074030135800701c081007544800c0031400300b0070301505540c06080020600d940790481903001c03c1c0207120 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 101546348 1250 101545098 101545111
    0x11130e0706020304150215130501020d050103060504020a230114130305031206040c050409021303060e0c12030f2205100c05010c0c0b010b0903030708040e0105010f02070b09010e01170a05 82
    0x405002e80305d00d9000240d12803401480701441007442da070706c40c100003070302400000030359541d5002c00411481da901803040c3d80c0a14450b200004041c109801404541d28041d04000d0061181000d4810540c03c0100c992440803801d2800941c2400c0039a081629030083ca003120800e8604c4040c00b2041000c088040c00c0c8045144510b04c40556409040200b035444111002000c42e800308000d02c13402126400030007400c42c1e1031040c01d650035960740c5d94100301c07164003d040c2c03465002502c01180031f02d0316001400009201e940211708190740811448014454400b81400d405032030030b8040102a43e8080c0c8000601d4010880e03410325000000180040074007220491380c6500e000040c1c54480d000701a100407003604a840003007260300300a0300c252954480401d940d4144800d102c0c100000d000b800003400a4041c1c510f5282c219403525001400c0810110701450a64100342828400307403d60740140c411220091801410030000710006903405030b908007541c22070041c16420440a080b01e03812140c007619 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 101547598 1250 101546348 101546369
    0x30803040201121103070c0303150b0c070509010e070c1707060c09050108090c0103150e0103060c08070503090d140702090907141005030f0703020c070e040605060d11130e0706020304 80
    0x8101e081e0030701301c401e2660018a803050600110340c0c40da110b418401e1000f4864240002e030700b1030340c1d40307102c541001c83d42c0310940d80003001440c542641400d0010400400045d5507400c1554100302e10103c00150040c451810415801051414132036402003807031400b0064840140c0d91480c0c0d040c000c001c2c00d8041e001c0c00210304036190009580d485070b26054030031001103015008000a0030011800740591000c0801694510715021901a1285c0070040c004c500c07419000600701c021000180655000401c10004d11a042c820000d40c6a03008c266549100c00d640740000c0402d51850058000d0b010700007000c0d4008a10030f0400c03001c0d100c0014a80e060300d5641c0d012801d8840300c441044040322102c02950000b42042c80803a80e800e03207007a1240d40100107410054240701810340c105140c1100340d07000c4d003a48c102100c14401441a07505c140b94000005031441e00818109864061003405d00c101901d018654104841e041e0034004e510141c01510990701ba248040d40d5020003d54035040341c0994800718 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 101548848 1250 101547598 101547617
    0x80c03190c0b0619051009090c0c150203060d080703031d0606030d0503060f030a030206040c090506091306150602160e1015030204030204023004030e040c02070906030803040201 78
    0x85018450005140c0d0740622100d100f5507801051020380c41000b800040e0b00c07410403d01280650307034140c00000e0b102c2241c0d221249a807030f10100c44e040d40c1800070301e0014050300621481c0802c0d003100841ca441c4c0100b120143c2c0c0c9403602c83c04200c0b1201030140203801e061000c20700408156142d0000754034020243da0341c80307441c00c03410085604c555056800790307415409031600094441c020000f45a10a00040000180d003107440082410701002840840058100100304401c004000c100b19001d042c900d01d0402c120702e842008070305002c1024001940d04500c080051080141c0c9412001410764220b00840388035981d0b1001941d07642c1c040b07410140f0f140c0030103c041003454114905510030360000f410352020350300d880b07055030a103010b40852808142e02000003001685890004004c0481007900c0d03046980c01400304294880754203c1d11400b03515410b002c0c0700202e584040150482c44040340c001406226001c2c00741c1c549441944002c5405082c044000248041e01c0061440b4034005e03290580301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 101550098 1250 101548848 101548897
    0x30f030a060311101b02040e030c03220312110c18010602010e0a1101030902030a080c150601021606030b2202071103030a140304020406091d010f0207020303030a020d09080c03 77
    0x44444442c4144d001805148041035140d8040e100210300b00d001500003d45001080202c50a40c0e1104018894503440000c0012403002484000c405080070070200c0c07202c40c3d080d1755a0300f1404481c4100030040002011400004070410f1000300d8481800602251800c0c0b0303090806440c21070248610400340d440d00b8118219403402280400c1c0181d880311106043c5c80000c0019401089440c806030b8043c4505401400040e003200020305003043c0403001040c1414401a0300d180c0f46070001c0c032440c1150080580310308210004103209055440c14100401c04c41601c601080303010000c10703c0d21802c1e0187c01c00d540d190442c55030080071a41c0c019501c5422048580051680d00d00c03d1060200010303450222030507001102802a40d00184000d00110340143e83c0c03403502c41a91094981c5410030b59134180d81e4220000300344a02c00400080d80415401d01d101500029240c3c0001884110501c0d00010748800061071075101c480d000f94400c091581340c40c0700c0c0e2911641c98200111046941000c01d41c2042d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 101551348 1250 101550098 101550109
    0xf05071805010302210709030b04080304020a050a0b030a0e01110a0c0c090504050607030e0307150b0f0411270901060f080108010501050a03080901111c081501080402060705030f030a060311 83
    0x24491702c170441030040701c0c4050544194100004003002c0402c980980b0100004580b01d040350b000328045c0c49080d07141c2c00d06004100c1210030039400b4a200d441146020010900c40100340d0b0707405184094002201c030380040c0340d1400b4000c44110b2001c2d00400240f00710215402c045686441801560304201958450500384200c0c1c50548001e043c0f940a14009401b0510039088814440310a5054034240513080c2e542a18145466101c68440750701d0700c90059080c1000350b00d602c42020111420700901c41441c081c440320f84611003070141070565000004214912400000941c4d0f01c0140c40e101d030541e5031300380040c0000210b050003c00104000c00016003a60305005660580310010080c0c03d8491540e914503445910440d2024140440da51030004030032020300c02100c0f5100c031150501404010a00000cdc00303198004c20200d0344616070411840c299a020032882e5000707905440746d50781c0c3d50040c2002807450140c1c01c04009002c01c000f08102c42c02d08290403040c03c90f88551010401c0d851900c0c10005d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 101552598 1250 101551348 101551357
    0x40602190309030b0c1201151d01081302030307020909010e0601090905070603021809090c010311030907210c062019021c05120307021e0706050d0f05071805010302 72
    0x500103119500140081a20400165003052052080600e40881b600c1c5190722400f0036848111030352024031802680d1500320659a00d54140c55003951b9140071410006400b48501170b041030000c009180b140411505c0c20003c54001a400070504400c078544000600c1c060100d581e9034116034018640000b482d201507008880407036034020050400c550601100318000c0d00112500011002d01d0a0344040c40d403034044845019483d00000303861180849400501566080c21059030100010401c005030183d01281c12420356000d024980803200781d245d410030740a0710800001c0c0c4500c08104001901503004030f18081d0b003803500c034010b02030404940e038410741b18510030540d400f46c0d10310b01803e07400600d8205440020900d008a06c0c450102c1603484491520744881040d00761100c000043c0326090f5010003102d131400e45045000ca45d51b100c4482130b941c50300500d108480a0003408901d100006006420000e0780c0f07031441e45d00b0040c038549418002d1102c1103d40b21103041e4860700e4400328140d4440d00032603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 101553848 1250 101552598 101552603
    0x60906070c080c100c0b07050f070b0103030f0c02060904020901050909090703030f0f08070c14010c02010506040b03160306050a0b040903020303060108010b25020a150801030b060406030f080c0a020a090204060219 93
    0x4050081458460000079103005004504000d81048592741c0c4c100c1c2c060281582d2805501d10419075070440c6800703001000301c6840001440f40d10001e890060b41d44d50115016903030142d8015856520010050700e450240e02d00303041d4005601020840105000614441124000d50300d00d01d0540080c0410340b03017000e4080c0d400001850a03400149070714020101c5000d0030f84108248404840b00d81243c0d421603841d040c0d46401030b51540107010081c40c0501480070044000c802074040040c2c40c902d1581645828031004000b2a02d82c1c0c000b50102c0501e0348218020701001e0310903c0120554a8000d450354400c4940b54046004407002061080c80d400540740e18040a0b004210030003141380d6005030b401e41c00030701240e2050901c10f001c40c1105100070702449035402622038120a5046250142d0845001130260740107a140c00000c0000c910a402c00140007504645900e07556220000414240078064a010f900700340c200340b0006880003258001e2085604c150b003603d64030b0031107680e60201d800e42003501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 101555098 1250 101553848 101553857
    0x7120309091a0604080c01030b04020a0215070c1a0106080f0402030c0d06060f08061b0304050601051c05010e0d020f010e0c061c11040510050a08010311060906070c080c10 75
    0x41c030548109900203591942614407191020100d940028000d50180e0810750b8150402601e501ca5540c2601441c2c0c0e55090450301581031850b5684000d54440e8030306c81a89081280502060f4954046c80e101c54581360051012881c0011607034210000e801c080c0710304000108100300242c070030012070788190301440e03004001e0000800d03002d080010701c0e490000d054501c1c03a9201e03000140180b0300c1d20034200400e0324070040c18951a1035120050409008007000c0704040040081100254001c245141510000c80d1620700035903103801c1082900d100707010300501139031a1503650314544000241003400b034885c5a086403c10b0000100c814280c44e00f03c0b04010703e5a100e443d001d00303240b802c2006011440401c08070000114064840c01080e40d0306100d00c00405000020140041e081c10005500558858280310b864030340d514000900d05041448040d2040b075400e140140a540c500040f00c4040c2c500600c442e07160401c6041048401000b4404c1382c840707201f082c810300054100700c0384042e00d0a01d1500c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 101556348 1250 101555098 101555117
    0x9180b0a1a0418182904060e0f070f06050d0e01090c05120c0a120204150b040306150501021903030e0a0b0609070f0822140a060f05012909061b071203 66
    0x54500780c0c140241c071200c1480c0280c1c0014121700141042c0b0328030540c050f11010560528800c42e4174100310501c443e08003150801e0000740141015507005900300c03512460500d641d00c455408420081c8044115208d00d5400e01d04902c06205600c110242541ca08403001c6000000040c845a5155458034549400c2481e00908001020202e4444080705001800111710341e035940c140c0c0078400c801900070104003c4085014000d00c02c4500c0340300080300d808000060000d0420f0700103942c1d03c0c0c0c515061080d070452403c03000100751003a0419000c0c08507000486004110625040e540303104100d5100d40180300080000310b06a21a5040e241500c40030b48404078651078006050840c103400d5200344030324100003518040003d6800c1710501c1c0966500c00580020841d0380392000c01c2c1e85240200f40c3c07a8501705001813205124803004910000044403d6442e1060421001c1501e40034510314184c1c003850110300c0074244102080408564214081501c40d142e0303c4030341e8800350008243d00500018030649 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 101557598 1250 101556348 101556353
    0x7032f1c08030c160b0103051513020d050a06050c0403050c06040f0509040c0506030a05060f0901063002030414070b040e040803070201020c0a050304060f09180b0a1a041818 76
    0x10015500404100f815618000c1d101c040c280c0c0e005502c0d6401c6400310400001001030001c103010000c038650480c8003071081810002c0702002c8102036004082e00c11617003c00041e0800170100034150640340d01c58000d1100c0d16010b981c20f091034100d48405d88139809416420201031802d682150f0985110140c200202400d0006111030344000420031250322520241c081615501c06026500c148900c200c0410180391130340500805295628030903014030304860040c0310f41e03a001070100f41d5040f510b42d104a090004580140d4031107640360b4841440500c000107000600008800c030306d0001d4003c0081304c840d50395490b00101140f040384a2a0007040e003040101340001c21100040d604010070740300140c20070b121a1862410031044c04800ca0b403e600028042000c40d4120108166104280c20102e8046180032054002401c0041c4101c450550b580070602d0b00c2d03510204c20320081c00800c8030044555000d1201d66402c1d9020340142440300c9001000c803d50807806004148a42070b01110a1004035a1039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 101558848 1250 101557598 101557613
    0x905160902042907050609010207060b06090f100c0b01080c010f02030301150c020105070515040b0601090302011224060302040806060a0b07030c02030705041103060406050402070812060307032f1c 86
    0x410f0b060501000700580c1004c1841004001d010b110b00c9400141d8410503490803204807845030381010b02880e4144000c2000f5521180c4040590364159498070b000000094101c1d0b29410844c00100300c0040c92001044c2d512000516000350354bc20b88401101800c0706906990746c2c0400d200301c0c200c48480e41e05c5030248511400e8a05400c83c410305010b4100002130341c4590804401003030301d2140c01285d80400c0240041b030558560002c80070309100000e9421500004e00e08a00b03140d84440b003a48849408016013883d000a402089a05d03190026150311440014086d40c460711490b01e5511441011402078980140c010003111500c0b0b1409150102d1560192640003280a00b030341e240c01103502c000341a8803070780101c00b40c00c48001c0e400ca5880c41e10300300700012203481d60400ca00552051082d03d000400000031102202000c8548640a6980500013481c2a005401c0107100b4801c1140380d203540e1000c040c260404000400020400d5407142d800c0c01030b001c50100c07141e40b503e11070f18103100119868 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 101560098 1250 101558848 101558909
    0x603030310120305211b130501050304020a05060301030b0708010801140708070201110301090c110703080912030d0c0503090d1814030106050303130510300e01090516090204 76
    0x6070503e40c0c14180072040c0d0340820101c111030b070002c02ea04001009442036584001020b1b0400540b80c050605a8030703018104203104034000c1a050042c000045010340d03940d001550024500100020fa50707607101d2404050900d01583c128022540e02c0002013090107041c000c2c64541d01050405001c40d40c0d03000d0044402c202c000d0074050a5540e560141d030f0100d80e42d000210f0107440c1c043c00110314640740c1000140055120104c180e6640c00050040c00024007050803164100c1044450074a00c1502c851050b0840c07213896005e001e03040c90640da100c0000e401401640c80340b5913500582d01e02d00a03802042e12400b85440c2d250502001d85041404164210110715841c2c1002500000b52991104042881c0d584507a40d41c690f03001080c24204450314040140380d0b8980400e191445c1e90702e024529103161403907012407600e0241986140e4110788150f0b54003005816003044001d0010008504109844210360a52001c1611031a80701007003000303640c0211400c403803079169440d41e2605c043c046110090705 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 101561348 1250 101560098 101560103
    0xf1704150b1306080c01090e09060a02090102150a050103110f030a060518061f06050c07050607030e060d0e0c01020c010903060b19031212060b030a09080d06030c0806060303031012 79
    0xc400310b40b895100704920441d40900303000300c024200541614000b41c080e8409038017201030442d8480401110040100e551340d040140000d0142e10f07080c0040060f0b0500305001c281c0082c204040c010000142025080541240c0c050b03491194200300d01402d2060254441400c3da4241e44104480d0001070381c00d40c41076502c1500700c101442403041000d041401c0900039a10304802d03115000c9892000d0428040b1480101311509280307142644a0101a440340325500c40d043c4500030208103201894020b000c400c84d04440141001e0f969a1065941d400a0005400600451241c120410100d500019102c200300d40e050312800001859a5a01c00c05041501c41040d00155000c0404032458140b40140700507510030729510b5611102084020091001c080c010600141003c03c100840464801101e8000c802d0413400b2451001e00e0030801010311030b806c824029289000000800d0250140d043d00548410106441803070301d0303c100300355890009480f4901260039104081000300ca1004d45581110b2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 101562598 1250 101561348 101561359
    0x30e0127030303090b01060809120307051201080a03020f0714061c140109050c030112150b030f070e0a050115121b080403120608030d0b041b0f1704150b 67
    0x1a000c15100c00c11000503403007100460b849503005402c1000f14102507014016625010741140781820446075903d00902c4041c0c3d110f040000800c1a013403107076088600d007003006640e004255a441c0c0c0825070714024654164018064013003d50280c12010803400129401000d0307149101220b201000041d41c4800c05940284c0c0a01294480c142035a01440ea00015113543c9843c0e1507141c6480c4406444c001040801030f458100f00601405034000440340b002900311000c4419440d21007020740040600008181d414403411040000401c00020b4980c20b980b2000004207a5444540e848030a4071000e000b8410440501c0050105c124459200050800c0d02c07070a01003104100c0307048404044041e441d0301000203030340000b084185030b0480940a0403a0017880200140e031b140240c0103440303001e100701503400d4039281c00e010b407140d81e99034001c04000760045505140f081400740c0d001c0d004090300b42415000c070741b00e403e610100d5104440f03954032607a000f80200120f40b40c90151071004140e403101d881e9000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 101563848 1250 101562598 101562647
    0x9010b09010912030305010f12030219030c020a0f09181101050c07030605040602090a05012111041a120601020d020303010303031d100b0f06091f0c050d020106060f0c030e01 76
    0x15118200103c1d480c50207920b000605504001d201c154500140e0042d8641d040076400180010f680010b4031280303030050315401d140b0400186002c840f080080c1c0d0010354409101d94010a40100410402d0110b07013055000b00040e0410400310145001401e501402000030b01d031400704c082d4000e00040602d8003042d4282c6034415200d580d040112407050350190f402a501240921030360038070491030300142600b42041d00f00707403450358928150413141407607484180b5147d0301020210b01d81035003558090070058801803920f034040300301d88031140c0203021406912442c1d2004203140354004500c00f10b0100300d0b07074040c618581c00c544040d809000000c80c07600000c1c06291032800b92000c1400180c0c2072040d000740100d80c0344034120800c8000720110700e0961141400300b0210410f90f48858041c40340140322a9050007040c140071090f524a149540050441e000300481e2800155042d0700c504182c03400e40d201c0d88401d4a021108a5007400541001070105119441a032a00e6010f0108209480001000003882c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 101565098 1250 101563848 101563859
    0x40e04050f100603061503150c021c020307050c060a05030c030c130305010c020607030b0a060311090d0f03020d020a031407020a0503190204050c0a0804140f0109080c061509010b090109 81
    0x3007030030322400031401c1560f035007051041003114010350b0641031101c19001146415a00c03407581449031080c1580c03010f07a603403118940c11070003030002001c007040c00403903041d0f03000b81054040d4036a4800c8208890b140100060513406141002c262031000d4000d41c2d4441c11940e07603046805080d88040d107142a00c0109010158003684401c0d01200658400d400104030a40d04c600003a26041d4094080001e26042c080100c22940314114181c0c1201c840c1d140100b54040c40b00c161072240d114070f00308941c0000312401344401f44000301607507504a030312a900700c8404e5442040308a0715569400c00060010f0b51910329803045104030805131107001d000600440c1244c1d42c40c4006807605400d025500c0071a41130a18039015840c0511949500c0f4201d4203a252920900c4100240500b034020030040103003034254010040448204040041160740d40001c102214050030410410b8010700e16002092040c000000c05100e00880044c0da040c0000e01911007e90030b00e80300c0b1540c2c0d08180d503003504103c00361724000340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 101566348 1250 101565098 101565103
    0xc060c0d0503090a050d090e1005031b04090609050604030f022b0e0414011a070809090c040f060833120a0c15030b03070f03020103201c0e0d05040e04050f 68
    0x28106c0c46500c030503140900c0c058402054140007081809481d088010411154601041100d100c000306103c1e6280c2016507400074000340902c9030050929803800e881482080000034095020b0381c003a2b1503600144460910803680c5540d2141a9030392105850308444005814001001100303101d0704108000d4450740c80454116480140c0621100102000401040b140c825802041811002c41d1034034050150b1275155807803003446541401420300034005055215080103036405000303c030401180380c65403010000d0104409640c0702c001428015400e03207a040d5024001c1649000708102c0521540e44c41c010042c6030310000120030601e00886d011070000504400840c00079200c42c0e1807145200e406464010200d40c1000c400318042d42c484507040c8200500c07100c3c060200ea03824030f00416100129074208408103000c03110741040c2c00b400b05002d403854040000b01c1c01d0300b042c0e40708200050403900c2901ca0f90b0300d207480d044501160041106201c061031100900f42c0c41070040302100e9807100f6064a061 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 101567598 1250 101566348 101566363
    0xc060305011e051323071115150a080a050c03010501090513030f02030d0c0207030b06040606021b0a030819030f110a080a020705060405030a26060103021303080d020403050c060c0d0503090a05 84
    0x31a40500041048042504007c0c0550004903200040254106148103015004805084c030250f0101c1540da10929640381c940301c01c06000040c068504114843c602140d9904a0f00c100034400d50a00c000450b4001480c0310b03a0744200d0340280090200042601d0a4940600c0700c121801140400c001c201c00d40c40180c0100c503600d000d10b50081240600d1810300c1d0349900c101822251180d4100314042101560000b8403501c000c0700555030360340e41d40c0c8130400608241095440100307110404140d12042801c20101080c0c0d404280d14207202209400c0c65100c2181d044050041807407038140304d2140003601c02ca0095901c003954034070042c54030380d00e51995441d1000488045030980e2000808456240c2d02503822f40b00380004460420382e4030001201c4000c0075000910303290405034003090302c200d640003500c0c0c600021600b1640c05a50b640c00490000040d501c940001e5036144150002c0c01f08c41c2c10f04d0700480e101c05541c400545641020f203079080b2560761010703100c09114400c040c0a0310105509000d0072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 101568848 1250 101567598 101567651
    0x3030c03091407080106080609210705010c0504210b010b0703091a07151515020a140601091802030a020f030f010f090b090a02010e060d020c0a0c060305011e0513 71
    0x814400d45800c00007821364006e5001142c1d16000b1034240a824003001074120f9942101090091110034407200d43d42090089040c0540190b0a00c010000440c4d004030041041c0c85010100c1000440e1028000441c1c5040b070070700820350991800108210f40110000d0020b41744a881c2803849181d440001d00303e600072031a007540c054140021500104569084004c0108e1150341041c0070136600c142002c000020244603c01103000350154070740c0c400d8424031440c44101d610010740d0314036000d44a010b40d9628004d01404c180c00d80341c41c440c1d100041c505840a2119039008004003448100d642c01e11108089680121380c1621680c0302045031701c2002c0c001c0c03070b140030329402000501603a141801511030307a001d400c4070f49503003204e011480540d0344081c5d41c421099003516800c1d5207052810700e400c02489070306030400c024014060004100011000361008a903995541403089980384c140c19007509144607516441e50000e14020001410f080c200191007400084000882400801b41c165058484002c42d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 101570098 1250 101568848 101568853
    0x131b0b040b0409140c0301140f040e0c12010603050318030f03121902160f110d030c060c2a08040302040203040b06040606080105030c0d050a020d120f1b03030c030914 73
    0x2440f2182541c1328402503071100b580300e4041800d000410300c038980b00600510103008502c0c459800c858540c0070a0081802c4050320411102064082c8075403149450046a4440e00100454125416050050070140c2c0c2d08003000d9885c04807425425074150400000290f010302515050380705840c814006024020300000d0506858505041130705280c84000592400b01c0340b060018403840717803441940090b450b5120b071414207000f516003040c001c280c40e0402c0c0e007948052040c504001305030b404035503090340500c03d10051040c00342c02038040d02d81d80c041c3c134103500c0210400c02041d04070290320510807509034000e41a0524140c0c50340c020030103990040b03409031035140ca03a2082c002d07281414810b0300010301c10f030300d011101c2e5414000041d49a8614030591072041c080000d24005001043c003a458450b507004140746001e0301a40f400422921280c0080700100e00080790003c1d4aa01070864000300b04010341e00003400300960f075001c0c0c0041c00e00190400c01c16a503510302c01c001580003403040701c402586400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 101571348 1250 101570098 101570107
    0x22080a08030a150e1311060c0a02090a09110d2607021002070303050306041e0e150f060105030c03280204170307150c0c060f0501050108060306131b0b040b 68
    0x244032040d100314049415000b00f4510b410041c1c9510403400c0e03a000f10a0043e002c0501c0e105081406c41d00700015a140c0d0300406c001385002c0d4162000a0b00141c04d842500e1400003590703074a208030200c1d9100300d40a041c0a0f080c2c49113a0251030941405036405105e40462324507141d2404080c028040003600750f85814800095070701c10b610303200c00310002901d0548001c0c201c0a0031a0780c011700e0340c04091301241c000c81e21454024482d908111445802640d0b50030300b009050010501181da51841541d02c3c0c4101440c40c02241c0418501845035101e118103840315803454440030b007030301143e6000500741660076208a6145d0100700800420308140b0603080300250315103045c80d1341c0401003406400c0201c4954800c000b1000045c4401140c16468a4a900005000f01412005841060240380c00428840c41d10000c114880015400103040e2002a642c0d840f807699500d040c0b5540c0c02091380c84000d007104100380100000c843c42c03810074080781e0480c07035941030f5691207030321001c1c6400c07540100a1a15000c107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 101572598 1250 101571348 101571361
    0xf050d140a140a140f04061403010f120807060510030c0b04230402090a090e0d030c1d0a050a030b040506090105060d120311040b07030207090c0522080a0803 69
    0x140c201400d00310440406203030541861000c1c214620309886002c41280c04039004400710b004640340c10420f40c0150440781c3d03480d40b03504000745541c000e00945001c038401c0310f9164040c003a220145d9041e1070754418015000f13800c00100300101010504c0c11203240e401008150001411409014060500e000c85001e400c0c1c1146005460950142c01018288409210030040000c0240c0414032081407007409104140e440341c040390203446003120298114480d01e400207401d04c4180c1c4044c00c1c01810200352000c040102108070156002c04064000007020303001c00b42e01581d001c900303540c030055004059055981d514400714170441c165620590f2402680d2040000b805010b0180550003910600200a50300d880c00008070080050000a00072450304042c00034428025840607805108803a0303026141d81d41d90303000b109181e000e84000c900600901d1030004504055018050450100c0c1e02d03014141003200901d4910051070b4002c254070308490070700c0007485000600640c0f81c0c60b4000d10b8459502e28208 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 101573848 1250 101572598 101572607
    0x160605151918022b0b0d030e19051315080a020307170f10020705010b042a0c0b0702030406020d1707050c030705070806011509081e0a0f050d 62
    0x180c0d00d501804801403491103010881031a141919150810101c0249420048400901810241111440161001e00030405481c3c1441c2c0800c0040311080c0050301c41401440483d0114000040c0803a5070032078a100c1a1400d25459030440c0070200584031955a14000540c010001c111444840c603503940c901c0118207660841c10018000c1000200440006940031a69031003891059004c011740070a003456180ca030a0015104410b50402102d00906403030304144025071000c0c408645541c40c0c00321030301e41402c090043c602400945c840111031490541103144511100359540400c102403030581e1070002d600404524003410107a070086813228184a0064a0862101111800c1c040008034100d4500313022006103a018003a4501942c80b03a21b4100001d1442c020f001005100c2d01138610081040140080d0f51412a81200b052200c070711b40c4010241c95041e20f50003880d85a410192025828441c42800200610707907590413a9281d0003151600c402c2111100012034040d00000c40340300c203007a8071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 101575098 1250 101573848 101573881
    0x5090f0303040b070204090c090606050405100f02060105010e01020c030604110a1a07060c0309080712030b0a080307080315090c09100311070b060a0f030317010824060402160605 78
    0x180c00462030107080c02d054810034018640000d102d6600e514010f810400c3c1e0703140042c0104080081808640e07101e03000030f030883d0420701955000741d0158161903001c1c0d00c14285611451440c0e0040d241c0b44e401e0800464600800014050642c0308103c3c2e111415201080950b00c04e6001e02034a1504100100402200d83c00507032004400c80c0e04100940c0380c161210301140d000c0c550040001034601510403054019010802018010140100703040040c070031603420002d840d645981c0c0030040541c0c00801c00c0302e03161190152881c91340c41486240009200c103c02107821000320810180d20269501c000780c44030404882001038010013046083c1542013080c481c003204000782c00c0c04d101c2c41010286602d4540540036001d44440411408036280f9181c0c000341c003010348205c0d0488000d503a120306014200341007903d070907000e85640400000b503621010404c202030200480c402c820300c1c0c400c3c10001003140d5014140951060307081080c620b00c040301004030710044c0e215440209003840c2c04111300481244 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 101576348 1250 101575098 101575129
    0x2091605190801050a12030f110c12010b0a090e0705060d2d141509040c09020a0c1a010b0403031103090d1202010c140a050a02160806040510020f030f1807060509 71
    0x1c005c403c40000b90300705103440c1c1c185d2614a84427410045001581e468401c2c45030b81c4a03084010141055444401908069031288003564203280465540d0100342c226402200e2440d507580040c8000c0c0490300d03004006007802c26035182d0100744c90990700c44000e5415402c00c441f242d0507002e00c003403a20788d51080c02140b0280b540b90440c818603283c4101c0040d50f144c1c10001c180c2c4214815400201000b40b400700440203040b0021003107403513102c3e440d409031541405c40e8081c1c03202d034001d01d03030702c04000b4820700303080e069030140c10b1601d0030726145940c191010708001c000307001c0501060000d81d09644501520800090141030710055010b00b0340b00103030031103d0a112040410404103c40035868400720115a441da01c0e81c82e056658043c080c50482c00c05c00e51100d01080c000e02084d0020340030750700055144c02a400303482654025000821264120b104400171018401d4050000039243c0044085c00e82d1302c43e441300d0702c1a10300d0141000c49810402540c01000210b100824805500d05000c0b440d87d00115 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 101577598 1250 101576348 101576369
    0x8090f07120201030e0a050106090222080309040c02150906011802030912030603010603021201061d090c0906011707020d14070302100b01030603020d0803060f090402091605190801050a 81
    0x50070045440c000e04a400006410305440710303031500c00b88408000c00c80c0300355044002044a6a1100c4402d00070354000b81c5c50040420416100d41e400711510386074a801c07030784550021894a002c013810711000d081c5c2114070106500402d00c8a610115415590b075205001030409030040d90304110501c140b0100d4403807400400c0b4410300401412560009005017000101a20103440b641c50900181c007402c1640c02c005d40100007110364406910b4150001d1003900e8405010b52041500010254601c0400310b03000042075115401d102d42030f00b05400800c1e008401854107004650408020300e010310001c2d107030b04005a00070040144000c0e03003c0c000580d4080c40c001400e15003060f544009559410079030041600c81d580d1880c2c0c81ca039030f0180c2d108500846d4050030b00940b10f0901d0810201917007044680700e0141e94003190284041c03410307025161107158011b24501d85615540b2507084204118422407092100810401942a20b43c00201d00f00907002da441218940c1800c1c140080c82660307a00c84220038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 101578848 1250 101577598 101577613
    0x1f030c02070e130201030e010b06040f0e0105010507020d08030702150f070207080c0315090c150a080a0605060d05060409021e0312040e070807180b09120a031211091008090f 76
    0x5143c0c083c0c1c003a124680920b804100700940880c0c1c1401410700c00d1455a018600017000124030403044040d10858000e110382085071303030b0b83d0030066503140300d1024029881101910740b41d0000b0b0409000e1900000c107803049503003062030b904902c50219010703079000c009050b2000801c29040d40c1041b01c4005004044003030240c46480f140802c0d40d071307a4850b40940c0400726a000040112404216a59030004000e1201c001d072004084000c25070782c8491503180025070f40b10000340a0320000d000e40022142c02419841ca0008801c9a070b00c0103010140070f15620580340e84046001d80d030350401d4400c203e00c208000200c0e41e07044004243c03402e06d071044035488044003803000300f102e111800f0b05503a000880c1d00307040340290303650342c0100c0740c2036260010410815140e04010450980c56805002100c205880742d1852000401545542d41009a40100040d500341810301071030307046410400f500b407050b0200d14103040320300000076440d52070100310304000340341c03602045030f0b0b50010024114009140005007910 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 101580098 1250 101578848 101578861
    0x10b0a050f0409031103040b040e07020a11040915050f0109060801090503040512150c0a080c0c0d030b0103020d0908070209220308070903080a020a03020c01050c03040909021f030c02070e 82
    0x11040300302101e612540da501c021005041c01180b01240715210341c2d00ba29565500e48502c15040d41103070099140110750301000a49440c0001604081145c119400d416114010802c0001034168143d0032075010b01c9408008034154018042d55024114101d1080301c3d40d17050050b55811550309034422407150b818822010046503000c0229400d8075003d031001c42018011090b124034040a00390360240c4c120480d03003000307504041c420203020714240302d0303507200920344031480b42d0040c3d03010710b060f1002c1c660804244072689a010344c0c04803d40504c10704000d414400b600254a08035240d00405981c0000d001682004501d4103001050f44440c0c224840b281e500c0030399201c000d00040302e1600505201d224008031300d216002d4810354008540c0114007d584080c0880000d4603a081880c00301d026219105202c14a5130052060301e401428110044d400c240c0b03801040780c05003078602001c3c0c0e008910060749500d0006560348440c40c000e155113001c2040400c1c01e100a250170181c0c0c0c13050704d0703050690b000d0040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 101581348 1250 101580098 101580109
    0x70203040f0e0c04030b2505091e1f030207020901121a1e011205060705032809080a0203041703040608060609041b11060a020c0712030e03010f020c010b0a05 69
    0x26956100d02d20030259890000000032071241d6080030f4207002500c400c10444100c03883d110f0407105048001d0b80164581c0400c16a564040d10500660200600c00c1e094a1102030100e03400031600e00804000c0d203820b4240e421000c0280401c08200007a400050f00b0003581080030b455801001510840d072414030098440b983d518451040702a03040d9902c60220b103210903802d480070b52051009030080ca031540e5842502c0b141300440001200c00f8010500080c6080f800381042c0c92207074200300503403008215a2290241e461100030f0645290b00d0b51803102c400405c40300c0c8060905034020b07400442c0d4072801c22003000030071203080208442c5503204100511625500034000e0760003100030b0355169103401000340040c0c0500302c40b058000c840000e1410b621000340c1e100f40311201041d0040140d51442d219011514180c0c80380030340d0075034903500c441d00800c0324a000b203501d5038001c0c1c00b0386808003450200200090a5a88010005002a0b00494000304081e002c0c8900e0951500454940d05113034900030100b030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 101582598 1250 101581348 101581379
    0x4051e0709050c16031206050613050301180503041511030f0a1206060e0105030402010e0909010b1002150f0c0c070f030c080c0a0b160614161704061104050301180b07020304 76
    0x24200038580d800750841b8403450f044036000c0e02c4000c00c180c2d158458445c01c00840c031981e1181c5d5100307609104960580100f4021180b112540020280d45000c0c00c0c50900c54074011040e26140c10401070f80c00c0c03100011010b02c0948000d036191074601c2e981d000511760042880c80041141241782d46007403000c000d0b01e600003400c100748030400c3c00d1494032541d445c001070345d081c049050340c170341c0051f854400c1048030003040d0720100143c64100c1d40c90388505030341801240c2d01d51a1528505451295034081880211100d1540c0d1740301d54004040c525142c403c200690511045a0080b50001e542c90320520421010500c8000134200c0c000003480c20f140c0d010b0010b46d0640e03c07803041c0244441c00241c10401c129554000401e60303034210000303006181c2e1000308071052010403a5a40940303451043e02c149501d20410080d800940c02135030b5680c4c983c959444020003000c00c1000502468810440083c80d52420f0082c5410134040c04015161400345080c10300d03038810001c20b40800c6400070803051040300c02e0019180c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 101583848 1250 101582598 101582603
    0xf060c19030905010f0509010c090b0f0304050f0313141e010e041503050c09060a030312020a12060b0c070e0601020a060b060d05130512040b1204051e0709050c16 71
    0x112402149140c16401031454078006007155007845c07031103180841d0300c0d08000d0094511070020000c024000208440072500360048000507101002082ea80980f072001444d0014041c100b50754402d103904031514510741c40703880291014950301400f004490901c2c04140b6142c1c109035105481310b901300880403110003a54503400d05000b00c9007440000341d1100d40c00700d030100e95070340d4030b0b0300340d154480c1072840c1d41d204982c0449114030413200018100d414404e0465048a03810b4071860742c42441800f2810282d00130280c1c0d1410052104041955543c0500600000b44031200102d0341d0f41d10710346002820142590041c4810003c1c1d88140159642d0001c0d054072000d8210340e001540c400c800b8006a524412031205076569420b02c0144403a80c20b000c0c00055400788110100c403584050704802500902980c80394410ba081c5c02d1200307141c4102003200c0545d00ca44180c2c152602c4140c0e5800b6850580d445144140313050740070070820f01581101d1310500da00709025801f61070815a1000d89450340100c0c1c139100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 101585098 1250 101583848 101583877
    0x52215060e010f0503180a12030e01050c0901090324110c0105060d210309060e0705100c020918010f11090f040603020603011e08011a010816140a11011d0f060c 70
    0x46c0003144c0001c1c08404006540481040050102d01c00010041c00e00c40e40c0484180d403900c07000c2031601840304100ca68005041e1034448000d444d548400c2d050b00d009010324010900c81e18407041c686107052041040c0c070505141955201d807010000306003141c1000302050b00522481d00039202281901785c2c00c40180d1480728015605c40c0c516082100680304d0b0000c02400c2e14103148854540345000704038442a100192003038039000b541c07140104c4140d508600c019401103071000115200409030002aa001a56500003143c40c072100c0404c2d208903429110510b20007038012803601418982803030302c0c2c880c1c01403c98080c0a050f0558000403550300c010300c80e203082040c010480070740c68003400c1141c00007007400000130041010000f190081000c60060080e0008030702c940043c1400c03107202c0c10905850050b80c0c5415000e1405a0300c0300b215440320b008041405440d040711040d070301d03090007039103250380d0f10310740454600850140083c41e03d000345014000c2904441d04000c2c0500d0140300b070b2190800050341 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 101586348 1250 101585098 101585131
    0x32202031005190501091b1430040c06090801021201051e0307060e0907050a0509100e04020a0909140601020d0c0f0c15110610052215060e010f0503 65
    0x32400341800301801243d0403a00340800004c01c102140c2c4000c026440c014512191034409000858108000001d0990303030710001d009800700340e001c00c251525456a114400c4d5686111006c031416032140455044604c660f24117014842194014201c1c001800014021b6003054064051894680414010640130301280744581c260081900305c010820720004d001c1e10300540d11404010310203004c10f02103034001c10007030001c9801180701c2c40031210300312150b9a03045d040440f41c0040206010192010200f000080c1d440c4004681c0e42e480100200c4c4250f031a0109400d240c03010003429116600e00c081a0040d140d0100607030369170003103021160b02005103416000d203085481c015048518420b80903003031440306840491351411502e000c42e911181d40d201c0603508c81480e29055580d071011101d00b030306000d070301100b0400d84c10801c21190505010b808280f80d61030541c4488011507690401e9108050420401001856040509607103400320a2804400f2910041800b405911025050440011020700c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 101587598 1250 101586348 101586361
    0x303080411041d06060a0e0c0a030e07060513090603020108060904051002030c03060909060105010e041a0925020604020a12060219050301060e090112140f03070503032202031005 78
    0xe412030381c1c20600510030002c80b0359025031540394580404801081d071040c030000c2685881c1031480b00c2c04568520408412a582d240d42400c0682c2003801030340103258854100a41d43e640c1800310038054002503131407a0301c49a030040285200401f9a00c0141c54514202040c00903036401804540e220205413a0581d00391114170303009103440f060f6513420b0210381c070200070f20a40d00140d030011802000700303e403941d2058650120300750f00c9000a10078240440d540d1041100503003010703080074084000061b05c915090004101080e0461011124940d10086060b040c2160718a804403810b5580c00a20042100c2d00e404e5010070940c1b0824040c0d0885041d11007141c02c10404190104c80c0d4000070123007009803407820728001030031940081c0a2103010400b0110b090006040c8000403d040702c40c00008040340d03154580310384c2014503a0041e011800d0003980815541c2078020401400c1d854814401941c0e6450031403040c2d51006500342c40e50038120388036400a03016a0700003500c1509000249d000240e00d40f5101d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 101588848 1250 101587598 101587613
    0xc06032401090f0602070612140a05060a091e0e0f060a020d02090d060b0901050f060f03060117040c030510050402030a03120b1806040c05070803070c020f04020327030408030403030804 81
    0x5911540c00c0d1000c000000c20746580c0400c2c100c6c00c540701501c42510000e50055040305603010f004c503006c88800c1103000505014915040560402c401a0107540215280d003901c0066802950358854046405500b40c40c0144080c0b1030781000b440c0550203400160305000c44c854030303800f010780803108164020400c1c4500304080c5d0704490001ea00148204200c14a0b898098040c0004021031442010454000079650038091070b05803a240008003402d190840c02000003d0369000941210304010948003804e0620040012860041e03000e810000041499860424a42000c0b04000c1c0300302414030307050000503100003410580665042c10402c00d08000403125030020058901170300d80c0001d09450040444502c4942c0310b005120903034040c841401c511100303591500c5400e00c02030550008000142842c0e00c10300d62903500503c02004614503400400016050b44c1080d00c400c11000c460010406c03050f40781c7d880c03007a003200100002e1130515203004542c035200d00503880050148103001700058100840d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 101590098 1250 101588848 101588867
    0x80a0b0a021918051f12060b0406110601090b01050703030203070216090b0102010b150715061d090c010f020304090b0301020904020a0f02070e010f03020f0d150b030c06032401 77
    0x1c054002c8244619400e00520a09449000803040b100050300440c082c00c00c100c179941600200110729540c5040140100d450005014441d03986681c2c40741d020400e9000c0380700400081070113030b079010051480d0810180c28104183d02590140d4030301210f0114698100b01500c0e950750301407c005031a5940c603801a1b00b03040d581d500540302c0448203035011404045581c0408603070207083e8001c1000701a00307000d01914040520404040030b005000c2140001c1d1031041d50b011079a0390900104846948200c4a107464641c0c03248502d03018004020030464400c104949000359509280c00d00381c5000940c4040d40b02c0c1306600400d00349580310b43c00104a03840035011500a0b80014100719501e10201e1002809803a00c2808000140250303500040d1003504180c4ca43d058643c04400c110b60325240da8200810564005103d6420074548800000401c8100c03142403100501e814000c11801400c0c001c040c240307541c40c903405118101c00e00902441200c0b50080b89a80220160b50790011400100180c55420300c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 101591348 1250 101590098 101590117
    0xb1e0408060f091e0616030b090c0a020f010623030109031418031608010b0907300207120f0c0b0f0c040e1609050a0302061603091a04080f0601080a0b0a02 68
    0x2c048440f20340038200005c0310f030302c2020544545003800f000454124180d410021702a680310b0082c3c404604601a1304c0014600b002d02401250404550507005509650040c0d00c0a2031002da00354411034118a100d41c0c03000c0c001e000b20000c00c00300b409940e021304400015803a520501c032020034012440d0040e5000024001c00060480b2081c1120242c41e001c2c1009500810541c0c1d401c1c503000306428200500c403280500c0454076800d08009088820185511160717164403240959072070341001c0301450f40300405009010b0724101d286200359500180c800301d5440703010760030804980e000780d01041850425541191481d0310014260720340d180074254500940e0049e4100c10710980600007451064940d00c6076075417440d244c0c0c002860345d92080140300c80c014400a50003010821010546030b1f404030400f01c609110b818003810850b1106608140d184003c01d0112001c13100150a0000a00401c60314000e042c0c1d28008084960501503850744500303c0050040c0803c1c42c840108109880d2038068540c03010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 101592598 1250 101591348 101591383
    0x50901110403080c0c03070609030602070302010f0f0209090106021908070206210a0b03060105090c0903120d091e0c180207050102030406060302091305120903030706060b1e0408060f09 81
    0x903128101003030294401350310000284104925210305007000304081c0d0807542252201103070345140d80c55001c0a036000f14000c4045559036403400c0094600c1e0b2140705480d400d80000162a00022010703c00187c0e41038000d42d0941d400501651481200e5501c00540c2c107500100c12078840c000d61011030703042d0103003200010b1110341180140641c0304045064074803550280c00c061081050041c141030703d4083c00c0c01020b401c4000307840010b6090103164003d203030b005400b07012124046c3d40c104200100fa0801004404510b03141c80b040e0f02032245000e0345508400d07201c15101842d07010790b61141541d41c058480d0443c201e94070071842c0780800542d0b041e907203002d401c54001d5540c1c1c44c092030600c0c01000c1d9030100328482c0d06a080460042100c42c0100c0142c1c580c40001082101391400c51007a840d004071200542c5440100700b400b00040c054025000140344880026032a13081c01c000ea070000c0455004441010b06051108010b0130000141d8030382c001d880403500708030b0f940781d442c1040c4c20079000c10310510201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 101593848 1250 101592598 101592607
    0x5060a0305090706030b060702100e0306042006090604050409020a090e480a0b04090b01141809060a080a2a050a05101106012c01120605090111 63
    0x85416401182c40b84100b1400e6a200d59242c0e0415411201520040364204e48140035110044c10040d201e00044603190800220500c03280c0e000a01d860422241201d004c0407560404201c207501c041d0503140035100b226440c6c184010140801e41c03e001c1d51003402e109a23120048a02591076803c1904003030610340000780505150301010f40e9032002e204440044003002a0a4000f19808400b01c209080269840e0f6101103c0050035145400d07001c280c5142c1d00c5090318100148100c11440140002d02c40030070301007284d0080f41c0001d046258039141d180c2c0701000400c09000501011020220500700460700c5031526218080480c4150055811581681c4201a011010f00c0010a8416050000d1030711550700d4408141074000064502d01c00d540e04107085900602c02881c1220405058030b4240c0340c00f60104c6204070010385889003c0e80554545410500c1c003035404074420911050300d02c021000401c0c00d515000b1400b46441031803002602451f61000461510342080d080380c0c01c5019031211040e1903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 101595098 1250 101593848 101593867
    0x3020903060a02070b0a020a0c020f0f0415080106080601030b160c1a04020406050a1d13050303041b0504060e0115023c06010b0f0d0902040501141003060b0901050c01060506 76
    0x2903008000540341004200d00107062006d00740200c1c2e4003420996101c0840160960911036004103007031800303500010003072808026071250301c1640790341d011001180007030b14a031005c800c2c212000384e0441c2046402c070100604c041a824103407160021101105400300000d1a0412107140e00030403c01050000400c041540b51106000400d014034000c460070860550354038104494194180700f030f80c03603083c680e42034810400f4020151503031240c50342d101c2c4654a01c0690f0307010305507842160201c134045d40c070041045001c16034802410142c08103076010840b883c10030b9110078641805104107500c00f00b43c1a100c41c560307842404954130b03c1a04424001c0034180511803110442d924400d482004001102041ea240d20005410360407681502e40302464061081318400389070b40829489000e00761107418840051b107441c0324150082000d2010b110700140094100700340001000e00303034010141004030500c0094544001c6400209003420859511403803c88910b01400c40c592089074040c0d400320f5184013 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 101596348 1250 101595098 101595101
    0x809070b07120f020c0112090213150f09141b09030d0201020a02010b010c110d031b03020616110d05090d0c0e0a06060504080309060d1d0109030e0117060d0303020903060a 75
    0x2c0064594984092001c0161400c81e51080906070301400602603014842100d60a0780c85010254006001d0450000c181c040800640388402d001e00c40b604604401000b041214810741c1001d000000340500041c4c01084004040c00c10160002e2090807402c0d00e81901e00c01000103c801c03204002c0c003a101c059400c0e0303001034002e4001e140a0f5004d542840e0300b050040d84a44000c010280c0e2000040000c1d030004028088420780c6650110300703000b20807200032041d00c800e020100c40c2900c40d6000744038525003500d031001461142d82e40301c01440800e003079034908008080b4611417000d115141c050384681c20301c40010303906030030701d28080e11400441c1c1d0b000c284415288000c9124640c09035041c001c10f42c1d00e145c1180c03148079a12544240b40c0092000b1182440c0183c020031786010ad540700845d00031549401a19881850180791581d81c2d5540756a008260b041041581050424213040c200721050307020300c06d002c070401030500b40f050440d0700890040500a07415205c0303081d4040e044441901d0140c0c100b10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 101597598 1250 101596348 101596373
    0x50402040c021f0c021204080607020115050603060d0302100c020106080708150117010b04110702010306210807020402071208040c270b0a051905090603010b0d02010809070b07 77
    0xe01450402030100714007400016120040b10503901140c02c0030400154660040604444030411405950580700c1c001da0040701810141010a025110030308000700041d08480d44c2d1089402c0e01c0fa0407030001c0046581e8441680d5024078140d4404030304c442586022424000b4809030060028600001c0c910f10340d9055002800740c0d007280c012980100d445014003a920820320b00619043e9441c58018003280940c1c1d6010a542204240045840105200020140c414400200c240d2101c00f142d15029507a050180a0007000140c90b02594007010102c040101c0c0c2a010010380310080000e074100c119200c60703046590054100030300382062101c2030401040c000c003e881c155a03600c2400d60200d241d13235a120005e0503a00100b403181d91318024500042c009003c11510043c0d0040e00700d0000100f0f170711203000c10181917903a00101c0f00c4081c10324003048103402025041601076071410107207000f40c0d241e0074840c400c541d40900b401ca030b0035178400740d0b40c624200003600110000305001c0740b00820407102d801ea24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 101598848 1250 101597598 101597603
    0x160804080102121b090d11030a061a0d02012c103501030f03020f070603020d1401030f08090d060903050a0f0201050907230603040f020a050d030e060a03060e0a0504 72
    0x35046901ea1340c03800c0700310001c0b00301043c908031420005840b4a14207401c4040459101c1d81c02e0b403c1e10304540c4002410040721004c1501c00340c0d150003c00d01c06844001c1160366a400403240102d2104035500001c10b0303603e200c0750000e015100b088182802140d229804030a5204c014002c80054404450080800e060318140d006031915240089502e07403414070782528a403030f010901552581c61078840103c0c40c00440010741c203600500e18598138032001400b116002e04a0340c3c8025030b880f81200c48100c100c81c1080202c0b4040c3c0c50780801032001030494104c6403400794100c40001d4032165800300040540d0341c135510050a848c54155003c081540040240500003107030b4880401e08881c81c0c109030700342e0b541250110102d400a1405015150013010035801c0c602040610b8203010f11240040b1703089500580d0161141c6110715103d41c1185051003040c005000300707498403120340c601545c000e00318011450f182c9101c0c200104100040501ca80e04c10070091504c9004d00f002403e08042650003403405031400d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 101600098 1250 101598848 101598877
    0x90c03030e0a1401050d0209060309070501022e020f0f04120201030f140708220809041506021e1603060203060f09010501120207020d0206120f0709140402160804080102 74
    0x801d60910304000400100c1e0404010b41002d00c00b40401194107512401c1550105507090015040d1929135001031803203203416000426010341000700180c43c040c01040f82d04e030110800c0c003d00d0704132402504504036070047c2a4015840c0c2060001000d00ca0141001c1c65104400110300002c0045c008401c5400060003a24104046141a4004000c0c0c4100c0029050440c0110f008100c01790310500449502105164005d101d81841c010038041d140010300d41624002e002003000805442c00303104105072941c0611100d00250f00c2e1030307006034403499803051601c030041a641169a02010070b00000e8440f5a012000809840e102e2038448002d40090701c1487c040c8581300403240140c201002c1e110b0580700141c4035000c004540e65034040203980551400c81e006180c0900e11801a11a000600b000d4964000760030f41d146001d003140c0001d000010041030811604500802000744441619000c0910a0703801507580c0f001c43c02201c542d042c82c00c0008041308400100000d04285c107602900300700610301c55 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 101601348 1250 101600098 101600117
    0xe03040b1207080c090f0105210a02180f030703021306081e100603030207050f0a1208093a0501020c101b05030f0c160b04150606050309121c090c0303 66
    0x5144d0b54600403000e01c560001080001040c440d80900054000105400380c840101e5900e0701501941ca0002c0d140a40915008564021400118075241008903429603003000c3d0015500c00003030b940c20141c44081c0c000c0171104034090001040c1e8011001030b1192008407200303810101d1554540c0741c1100e14070050760089034169000c05000780101c0c0200c0e50903500400e095800c020070005070203c402440d980c48034a0010000300c80e00321451020599015400302c42d140c0f59074030207002c1000300c61540c10060812002402e24404046990300306640c2c17441c8401f000404103413402e03e0080c0316000c03030303441f00344a130440ca0310b02148030b03400009071b2082c0454107c0c10340452050a4071240019103011104d40e0034000041c1441c101e02003c4d2150381ba4040d4a21246102629407241711407066406590082001c07852802900d030501a000050907103103811886c0d0f2070715a80c45503c0701d500251005a441d40000d8110a00c40d200c002c0351820f0402c1f20301003003114920b00d020501c2512034030086002c1200c851 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 101602598 1250 101601348 101601361
    0x907051003020a0806010f0207080604060203010302010810120303020306120609060a0f0e030f07061e0509070b03010b03070c06060b0408030d06060206010501090b030a060f081e060c0405040e03040b120708 90
    0x942d104050391380c0341c3c00c86030344070034005403030911503c50408114403501d40f00050801e41004001c0c000c0307020f94001642c030b50450000425106000b001e460368185414810000c4c0b03212058990440c03505841c0050b146e0300c0396000208002107408120526220340000e0116070500400c195014007600f1b401001038440183c0000300f51142001040c24030b400a10103a400707051010700070113074135205280012301d144ca4801d08541000c1000581c1c104030361f592080180780e0000304810f03000740445084150441d031501d81c1c200402d101c01410070080020b001040b41c2000701f6038000790041c0050001150700d513503c803545107640e43c0202451503001c501701000090841d0001c41c0050582d80c040c0e441030314190806c545c0d000d841d80003420a41e07036150f4070f00c03000602c64042c46000024100701c50150502c190000d18104001e02520b01d01d90498000106112002c007a5004a41c00c560302940c3c00300f9006001d030103d6045000d1079000015130240091000448104034103a2032141e9102d072102c0029440741c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 101603848 1250 101602598 101602601
    0x11031603050703052a040305011803030e01090f020d02040e030f090f1002120a050d060306020a030b030c0603060f0d060207080a180608040816020a030602041503020c0a0303050613050907051003 85
    0x103589809070402d0b421800304840089450f00041208072141d42d071b107026660750346d0901b190019408418156050b20325032081550500503030f10300040e20b0009010741d452544448502c0740740740702b000b4032502041d450701045450f5a0022100745007450141e07501c80b070100728025810b9010404c4244201140c080798915440c0c1484084102e4040e64010301ea004201e110140e0380303900030b0b00300701d0a000050090200c105658026103002e03501c24040580c42d140c02c0741020f010703a03259416883c03003038003e8544626113481d00000c0d02d62010045441070025188200880c542406240020382a03500001c0c0503c00e002d01200204803c000540d201290307907503104039196510106019200014140e0b00c086000300300400060034120f442c000c2c4d030641045856001501e082d0b169032045501c1d40e000f00b0100841c18121004510b03210b21400c0640c600000174281e26181d442da23400080506603500c0104405840e02c0740c82c98001450309008100c42e062604075103035940744621071544202c0290301c25203101c9109 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 101605098 1250 101603848 101603851
    0x180a051f180e07030506040c06030f021206041e02071a060604121506270501050d0c0e07020a02130b090a1e0902030f0709060f050301020f0a121103160305070305 71
    0x3200c0d581c10000d0301c465041c4040d0500c00d406090502ca03050020002ca0003c1c00ba45009900c03820440400300d10b48100542a60030314200354100c4da00c14050310381d0350a030f00d00546a00101c00c8400103480c030070402d502c00c0c0c00802d100c4c0b074800381032000ca10070301000000c003404210350030311828100095442c8030801c03d951046002c1c41d000c4546072000c0364005080e04980103413440703003000d0100c0c4060710341805112040383d12102c00d0415801c00c9803407840e030340c09100342c1d40501410b45030310600e11800c0d00d800300070ba005803046c150304a090100140300544240220107000c1d9008001440001444001da40584034a082103031280101c0c4020841300c500034031440e0104104d860010103a16150b0000300000d100812017a03825000d41d0340c542190040038826000502140c8a00091441c108001c4845540d0039402c1540283e1041054004800720700f1300380d4440190506d80300b07403940c806600c410043e02da01900075502031004001e10645d82e000600d8290b006080780c0c0d04121594030714170201c064490 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 101606348 1250 101605098 101605109
    0x80c04060b070303020f0f1206010e03010b03030703181e0608070305100506070c1a070c0e010303020a1b03080a030c030f090209060f01031d0114010b04030309090902180a051f 77
    0x4022402c0064020b4000c0c040c2d410b907180b03020b828080400e99a41c000e611899a0260008400c001c0140075a04100c07000c003182000e500800440440c2c00203c0da8070b20030490041c06228034900c1421450b5120425030000e0861407071607000446140000b90f00300c80490040d0404100d84c0000030b01807178132910404d4480c800880088411f20f28102c1400f0050380001029200b2054050020805c0a6440340c0b501030720000c20310150380c8802d075051285103003920360001d401841480004102090b4001100c1c901c1c00c2c0c01400500748030300c1c00400d940000d6603c0e400100403080108011031050741507886000200200c2e14144900c4035071044000454100030b100035480700c006400315104d801c0c84554240c0c0c5d0b8a041c180000c60341d2055412908038000c0b40c01c2200c1c41da440b0401061400301c0f581a19005010580c0c0c0e00742801d05585d0098030013446402204c0303070995501113640540d52075101680900648180e448080d061000c0f41c4006420b040312414003070350000d40340943c01c411100407202286c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 101607598 1250 101606348 101606369
    0x70e09060112020d1a060a06021506010806180118050603010902010903060e030904110703020c03150105040b1810090e0307020604030f060b03030c0c0f0a12030f110f0106080c0406 79
    0x81c01c00c1002102d089424005a800c2020000c2c2c400006400540d1441507291403011500180352070350811840700b42c0381e003241c0115049110b01a1075040c20000c0240c0192003401c000c42c1541e185004100070088084625040c1400600000b440550482c0803082501c0e04a006100c42d68401c028182a9458110000c0c00106007190400200300294060440da400c010262440c10381c1c550005026103148800e541503941c00040c0c1401010703010403407081c0502083c2c01801240c41c05502d50f0400a90510941e0300840d21440c49000c25a0340c09180c408540030402540c9060030021103c20b20410700d8000d0710b090380d28081da03480e0490000010713602030680c028040c1d4501801c680e00c400c0c051042c18001c032030140e110107130030403140d400780047c007241c100c40c034014241042c01c0c0c0100076401200d4000f15026072000d840a000c450201c001c0d41052300c0c2c2500300b881030440d0030001200e244072802e0307404009001e001c04000c803e6106400800c201d82e404011101d51504407001c1004907641071080c0450303003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 101608848 1250 101607598 101607601
    0xa050103050a0b04030302040b18030f0d050d051009091110050c0a031101150e0a060b0f070320030408070f09020c2e050a05011d0405030f1b0a0311070e0906 69
    0x30f049202510b610a10905e0301500701982e803900e035452038002000a04e6800941c1440d14001c1c10204400701d007104411004040c60360711110003404e248201440c10030441e0301c80c400601c110002c03075400303801000c0c034070030801402000b410a0701900c07036460881c41c0b2400707209a00c40b03401c0344501d003038030550010400940340504240e9010340310050fa0141c222042d54031080107100040880940388010240000d9203507942c07070a83e281c1c4088170500d40001c40003000c24450212680070010555103041d500d03003400010a000360002e020100701d20b101c86419440b00040110700e1080c0803075500100c8040800340512540c880c0ba034101a4021441d0031180c0750f0003500c107550740c00c12141801d8442e55405001c14480449100a8410f84000b100c02440b1075865800401100d61a1700214075100107688041c1c0ca941010390b10580c50b48140c1011440090000c50490000390103a0b040641c1140b41804481c891546071a000e4000240403004030398a0068403000500421349600451040c80e410025208a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 101610098 1250 101608848 101608853
    0xc0e010504050f0106200a170a110102070302031804020706050907080723010819020c0d1d090105060310050604080708060606040602070315090828050c03030c0d0b0d03170a050103050a 81
    0x12282c1415084803944150810b1f4401702d080071619125407403c0301420ba5903286280800340100c00040d01040060b0320400c01ca10210b0760220581310754405000314501482c10000001d4060300419101801061070201030110581c0000b42c0c0000712007580c0213036402030307541e80308030b03140700f800c00c81c40034044121214070b10150340c82401c05582c4028201d807001c1000c3c0e0220707010703000c0f80c00c841800ca190740e110741c1c009000d642d006a1070780804400e00079801c0c0c0442242002c1a5202410f100351409010040041900c0ca0010403059020f0000506616100c66550212594460032445100c2040c010400032500d0ba0600a00325400d4502a40003810b07031511f550342c0d40781c141c140c10381c2d14842030360744031059000a02c000008140c8400100041c4030b0101114828203010404001e01206003c010801e00c8507911002c800e0340d9206c030300c0c4500315458409510784080034000850b0040e81c44480c1c05216420550010400c02d5031124034000c1c0001565415138000803a00e0030700001e4043d50116010000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 101611348 1250 101610098 101610137
    0x7080309180c070b0712050f061f050c0f0a0c14030d0e03030706020a0e0f010306060e0904140d0207030c05030c0a030609050f0d0c0311010203010b04050105070c030c0e010504050f0106 81
    0x420003030301c1c071645150501a880d080c90b8440e00f17490400000303001000406035410117024954100d07503a1403101685041850004108210b1030850b420f00002c00300c030a40c3e94a0159050790b04585000c410340d000d80c2c00144d000754840d9102c0038220381c400d82031200030071007010b1500142c2c8400c2c1c02400404c1c1407100c01006407102880640c100d0341c1071104100c88400107016002510003805c0070303201c0c40c0020440000704103980070400036083c1010f1400398100110b95110b0000d010350b00c020b0f42c44d106551070301d04055440785103100a44640b88185018124440c2d4006a04002c5902502107002d09540b00e0b01019180d101b2803200c1940301240480038004100d19a10404060703104038101c0d603400d0703101680c4905100004101030080760000c00c444062503005102d01c03119042c440000c61031581011081c0344540514010305d410043d01084600c208000d00810380051904000e1189440e40c0e40c2c0c43e03500c203c107000d00850340114202804610030540207040f290695080380c455459224000d6a800c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 101612598 1250 101611348 101611351
    0x5090615060c120d0507020c19091d030301031101200d0f0e120f10050103350d090c0603180206130302060f030a060f031a10080610080708030918 64
    0x690007904039120f8141c80420091249a03c649000702c0d40d031510200190078100c140004a010381d5407590604182c4e503c04940c030042d910444c2c0001034030019004410408030410000840350b2000100110a0052070304092201340800d0742e880c0c0440d11108590036203d6000c0010003081d50000c086525110700400070300ca04203540d80f50200d40d0f921050001404903c04140300c2c00c180c0c01c1103513200c45056050000ed1a440b01e40a41881607514590f500704031000399541c07045100074102145205410910001c040c600d0204189a031203041c2a51003900a107440300049a1a0705c9103100001c0c02406805210407070444860b0401c6400000e03003c0c01000d50003444030880b000385c000008130050f038400d00a00110030b140107440781c50b4588a01e4050845490340c01c001003151442c0801c0001031007519081e1a41d50b20308107201c105032070317480700505040e16640204081e8060307002000441c190311b51040c1d040f1b41c1964111200d85558003101501d03407003001200364000202e01e00c0e41040748078584219 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 101613848 1250 101612598 101612617
    0x507030f12020d0e0709090c031202031b06010501080601090e0a05060619031d0c0603010b090105040312050304020a090b01020a02041808070309030501060f050d03030c0908070f06030509061506 85
    0x7425148040511200300e82c4528001d800481d61070900445005080020700040c00580340104142920754a840643c01c28622005103865501c00e020083d03184244103403004c084c41c8400c403c104c078989440203030304c1d4082400307120300040c0201c001030b0700e9601c107448200880b607a89000802e41d4030b8204e614405040d0050610350082000c000d20302d85603101e07040b0000030142d0350760001001d600e5154003429150340300f005848139512444e50080c681c1d03140000c580c1111800c861460380c8054150041e1158080e0f5400904416001c1d8601905580c000d030003184554400c8446440c3c154440c9541011291840c1207540181c0c4214010340050616612a080701800042c00380300704200c0d581d030102154001301045001860f00b010030030400c007007401250040d142001d0240c0141e4240004101905540c0f82c025080548500da45c09041e40225441c001400c82c81040e00d10180e00c80424a10101084c454440000c2c501400607102441c08520113018500c0b42d031943c644441c00d40200310007a080040c25 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 101615098 1250 101613848 101613857
    0x10050a2304020a0503030310060216080607080a0608060403030b010806031501411005070b0f0c1603050a0906030b0307030204020705030408010606021605010f08041e02060c0303091c0507030f 84
    0x45000c5c3d43c100080c5100d509420300b052051814000002c2c141002c4580565183c50b8450307040c04200000b08004e40c1c0700c04141b803c081c982d900c51600e0701c040c281c594080320b5140504d0040c4018150b164100300b83e000340c2a203803100030382c8401080c5a0340300650014090044030a40051103c245000300038071f1240d5000c0900301d19808854501c90008000964403810810b68084070001401e02d0ba0034045080d0042c102241170107400c1d113031b03141102c1c0c0041803110507500350000200701c05107401c152000d010200001042405680c40c000d00240d00c10a40b60002c07890550700090024030034042c001b1489006009800c0240ca1076003840301941141d0b60484260000380000f28031031100340f1601000f401d0686c000c11044500e200b045001e214580c11042c1003141d15502586d081d6007081c400364110343d004100a00c06000d1844c00090342c40d0f8000000d500c690005084034080c03c0000c003550141840009a40c0d004201c06205080f40c000306043c2c0012400074007080c07002c01c0c002c2d00c2c51030419110f03003030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 101616348 1250 101615098 101615119
    0x110f060720040f06090b090702030301150c02010c06020c01050a0e031e0d0b100c150b030606130605060703050706140415090c0b160606060306050102030d110d050910050a230402 78
    0x14200352884c0d9045600250340d0780a2525047ca04486002e401401c45d0014501d594145900f41d0509880385d482031090000034880001164030544c020804640c100c0d8045456100d5054440d018103001c0d140c81c40c40504020007440803400100440304c2256503610fa4500003a45103000000c503400c2750700100042651176856140c10380760b102d80081c01c01030f150340d0741103507200c0c4e03203814500204601e4481100034500301010490385c8002078014bc000c0d0b81261515030110002c164400902059000540c006401244d030104164005c0081c254a40c881d41050142e900075982000003078900301c402508040700c441c81031034a0a116849044010b0003095101440340c0c503030030b10700420b0f880041078010400d1620b800d1403d1050512500c00504030900d0288000c52400f00002c0d82c03405600402c0403500d942e0300303044403070410180441e444020b80b203200744000e1401c040700544442545440c019207a05140001e01041c0045c400c80c1c40040180321840314101605600188a40005104907048a60002e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 101617598 1250 101616348 101616371
    0x1021f0902030f0607030f020301060e01270603020705070e0c03040206070c030606141008190e010b1e010f030c1d01050d0509030306010f17010e09030f07110f06072004 74
    0x450000f50500c50000d040703e040680d0010708858000d45e000031010710610040c45080d0744640c1c07141e0026024a00f000103882d84184d00d0407111a82a01000121740303031880001e07119059009450201e01800035500312550340d00c101300124400300c400c0d0361026800c000040040c9400c0c0c014202c0745020b803c0052200340c0301c3d0f96110458203143c201c1600001070308900007003890322010503820032044e0302d006903403410030b9004071014850058410505035102c0c800203500700401d611500d07401b0b00082c0310b49840c0c4100c000d400c040402d2034902c140007450094074001094041e004441112310140c0d01d120030f000d0066081a100544110064100300042021441a80d62800b071203000381c40c074002130340c3da07424124005440c02405040100620000e10801e809003000c0718074031811291591084400f50340e52044603411440791251522a142c40446c15400f804000036071800c1c404003e03038840707803050715000401145000b104402055089520408030310107005507180d200030400079202142855505 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 101618705 1107 101617598 101617603
    0x10b0d0201030e0102091801050a06020303090a03031d1605040605040608190615060801080d110d122705010b06070804060825080604110901021f090203 67
    0x1401100c900d0b200b00b90112a0301400040210680200c00c0c1f035001001c203400c4c00340398080d03020410301160084c00001200d000380a200024140a091568128050f1121071158424543c1040c000c2942a01c10030014110700d003c40c3c08241e440d414201407004540d00d0341e015520a6041440400047c01c1c0400c0e0041da070504241e66220500190400002800201c00e200c046801518000900c46030710003201411799004c0f8094400c100980b05084443d0543c0000c4a45107401000015001070b014079080e40b600020440041035004010345141c200004800642e046107607094602000c00c40d080c4606110010301301e500030308141c03142c0ca603840c05000b94044c034400d021a000104803002812031031025010089800703500071075102c18004002030401d840d110b002e02d00f4034004071a0700d000c0206441c0c0494046c0e0044c84102002092a4840b00c035411485848a03501d10054002d618107 = true := by decide +kernel

theorem cover : BRFrame.Cov 101438848 101618705 := by
  have h0 := BRFrame.cov_init 101438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 101438848 ≤ n) (h2 : n < 101618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
