-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:32:17.225925+00:00
-- url     : https://prove2.me/submissions/33ebe2a1-182d-4bcf-b317-e53b55b4ff5f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 7913676 ≤ n < 8093532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 7914926 1250 7913676 7913681
    0x4030203090a0e07021e07050406030c031106070804050105030604090602180108010f0e060603040507050301110714010603020109090b040f0504120212090f040e030c0604081b010b06070305030402180901 89
    0x11000d8002c02d406140030420181000509004e031405900034550a452030401403003002c5a48030200280c0a0020b0004844d503c5000e440041c50040c40e03850f03400c1c3d00e145840040b810808441500602042c0300d5800812510010f0300c040faa006e013482a526500c0700001001820302000042400c0e01c04030383c20361228035840320645103000030b80300d181060f620b6441403203291920344902c505403541407000451070708111000d160802c0c403030303001c9810483d210400282034581c180c0710703034032607a030089061001e008000748001480f1009400070807107141150002081c4075054000c858110341c07a840203442d2521a07a110901070980ca040c00c0195040038500000c50300290303c0c50b80010301c20f103e2080041d031505400c483e030b9503030010b00c4614450725102c28070001c0c0a003070740703400c1c003a0205100c1c0090080b0107102d079512591003041c0481c4e9600002403444018548003a1001c0b0aa241680748409502c4413003c984410b42c050500d03a4903a50b0741d20000c2c0c1c0c0300f0310308483e000c16201e002d820301403801d8054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 7916176 1250 7914926 7914937
    0x31605190819020303060607060b01020f03030c09210d03020a170a0209040b180f04060609020c0606040c02030a051b07030210020102030a051302031e0c040c05070c050303040509011a1204030203 85
    0x9500d1003400780c01001d0072070342d1707000a40d03200341e00202c100000c0b000110f540d03101d000c4d0000c060050b6018446443c10150442d00221510703000a400014103c5484c54003807600340013003120481555024900e41c001d00c0c0c0d500d12480c5610281940000c0500406006010010300b01070554092003441c0b4010903010069040b07000300b58001c504140140c2d0640c901181c00300c2d0810000c8540300d5060f5030b0b4804100560001030419142140d0314a00403e241210380010403100d56040010700300b40c240030307051108940c1508104001c640043c030000d0070352070f071000031140c404c40030a0200c100e082c100800c1d1030810000e540020361064042001541644d019000b4612503490950100300f291303108540603880e0002c160b0001e61640181d040d65034540b40010f4540544108481101c030505030b00400300e01124800292040030550100320702d000c1006601c1860702400080e030165040034507000100d45020410300847e5002c0700e0f0311002200300c00d01107098076503000702e281c03024509040c90f0038080c0d00e1741d001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 7917426 1250 7916176 7916197
    0x70309030b0105010306150302030a11030405060609010504020301150c02060d02030712180201050702090703060905090c13110405060f09060a050c010b0901081e0106120302071508090316051908 85
    0x703500000307100c0d80a44102821940a050388201383d0804a0b4100c00a40c0000c0446400d5903a854a902050405601030351080e0f00c54001800345040c05800c104007504143d00c610700c1140100014010300b40f810240d413030000308509141c034520230340307100181990280041c103a01d01403020080140c00c560024400c501c0c41c412007030811010080450b030075025600740364080c0c0400c0c0c040111000505042c600709038094954580055103a841d80708020640380284d41280d07440d0b01180044900e850000305450250f82266410020580044000e841034016071058510808011400a680d003004100301d90201a006101d1543d41440340800352198000b41c0d903041c402d42c60603107012018141002494141c401090080007110811201d4030148942241e826299540320300c4005522980900030361a40ca20076006450102d08211107130410f604089004401c0000207070a124044401004582c1101d00214a0201c00c41427420014900495588182c0b48030225024803000e1107030207005007031080304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 7918676 1250 7917426 7917443
    0x909092103020a12020703050723010507030606020d0e0904030503040201180e220b010b0903070503070305062a0f070c15020109050d0302040e060d061d07061403010602030a080703020f07030903 85
    0x680c3d804e00b1049000350030005000c2541045100e01150050900304c03c8000403c0844908609114416003074a1045e0341540c080317529000d00303200300c0e501408480f0500c2c81d28580400c10440f03640c0020a80381001e0009420f0120004c08202964440d02103041001038044410191030380d07078030601c0c180e060125018524800701d8107048801c0402c402c04c0d110a81c0e000480400d542e4244150000640d003d140e1080d410301c01c40d600003406480c18008e5100130350089000c0c151300d2514a0055440700f00e00c241481038400708518070718100b10800c0076542941880b4107140d464000a02d060f116802050b004424074a182c003913201d0540d54150801c1040340d00c140c064400002038524141c003a40101c2c0589100311820b0740000700c16080100c404c0510b54003e201c0400c00a0501706855002d10100000318429001200c0500255401980b815a5503c502003020314540c5847ca00070b44078000c1d44042e108000c1c05c10302081006119405030799040d201300d400790744d9a18107490301501c41c1815203c00c03280c3c580f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 7919926 1250 7918676 7918697
    0x403020c0d0b10090e1005191e050a0504020109060507050102040f030503070515060a05120c040903080f0606030f060402090d0203160311030601060203070f0804090513020f0409030909092103020a 86
    0xc2c0225640172900c1c00c02040000400c07514107000d04001407000c0409003508455000c110301c03d024400da0100941031506841d903c5002c1e08099510082c02d2465841c241414040142d901101e102c00f11865850f00585409403072030107501a1149611000d0f01100c4010701100f404804001029002d01c210202c1d409180200344a041c100402c55103154005821001044a810101a104411188041a50840285c8034000340860b0030480094001a09010402a81040398521a50080c504541c5181149044045802c9052004000a01a40d00400c6030f8120740c851612022049500400b0b8034a010b42c115030a103c0c1c2107081c442521f6000c8400c0d0445e07041d0801040d620705a80382503005c0e5191001310b445846018001210803107045104120010f84030a80c8d00c00e00d80202030304590741039504007500400c6211800450b5107846103251103041000250031843c280300b19641c00b05c0c0410846010f01b4000c10030703096507a50400c3c0c289815102500c1740c0d8160f00406150501e9115181c041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 7921176 1250 7919926 7919939
    0x4090b0901080606150d0212040516051c05190602030a0c03110702010f120608011505040b18070203040305010f06090507020703050d0e0409020607050a050705180a02030403020c0d0b10 81
    0x46000b0301c01c444041e00b20602185950505903003048000f0048803a00b40b5045040c0305030000c0b41c2c861a5090400341311b180170b00c81085000d00c0207894601a01400c07113405410513000070742404a606140d01450115800c0ca070030001c0a10130040103102c8981112203424480c11f000000c0e602c12079950041c180b40c40d002103034440c01f034407600a244880c80c0b9510704140280e801555602c2c10000c8440c02d11004968558441165010385000350902c0400070559a4484072682440000342e0490380c45681803e8212619440d11040220940c1c0c3c000320300421070b2075105059003584180c0e007000c6c15650801090141e9950140c01100841d5904002008590741c0c030301040f0b0b00d6145a00000702142c100e082d10760031040c4102c0101520510081c80041d42d04020b90000c0c0d4564040707281190140c10880d1000d00780701040c0300d030740c0c000d21058504469580c07402d62008000d00000b440c070360340b02d6400b00204080c5031003000036440300342024125580310740c00e5040400e4590411280c0446042c8103801c0407640303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 7922426 1250 7921176 7921189
    0x901120c0201050414010e06010e0a02120103050c040f0204050102030a030b04060801091112010b060313060605090108060f06010f050901110a06020418050705090901050f0d02100302120a090b130309080601060504090b 95
    0xe0381f0134800a81166420000185150880540b8102c0159001d01c180701c03403603560b4110f45009601ca04000c1114140303075001d0100340c40e000c0b4000722105105001c00c002c42e036000300c12a1550402444c0c000746000c00c0400080081400790070401e040d62800204104000c00351580c007a010398112140f45041100785640307400c3e01c0f01400c0c030541000c024404a8035101040900710f019038403070750700800c0854455000c5481d03000709912000507940100c043c0260040c0c100e0049410070800c1c41d000d090700000701405091482184809070420841241016104205101451080c2e51181e001d559542c3d99910640c45051107040307903101c0d5854100810500ca0103001101c41c103640c00740c51110380c1ea00c5c02d4104000e001e030001c00640c00038a40c400c1907005981394170704080b481c0000e480043c1c90b112070105511800c1002401040c2182c909000701c408124a25034540e40496043c60310410580c1600d003c50303000c01d0f0355010010b10310820001040c12038120010f0819600c4500081215108000402c0309 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 7923676 1250 7922426 7922441
    0x907060201060e06060a0c0501021612030b01030b09010b0f0904110c06010902030106090e060301020d0f1a06040503150711030408060406140f0402040b0616060902120d12020901120c020105041401 86
    0x500c045c0030006819070500854000c1d590764095400107050060b81d2095900d2040c0340c800c11a103031000e141c920700405804d0710a40f008100280b03004c001048248001c29600c00c0180119103190502040d8038100c1c841759005c40c0c4e005403015000748034014101088000640020700d00c00d0650007542c0021594400d2842030b47d04072147c0d9510003180e94034010401c80a00400383c210b54255408101070050701c0410b002e0072407090015000065044e20b828210b0f80d036181903a1105100312401c100400c010f64002a00d071a60340011006a034294032103d20030340d031040492100c500540800f0030f00291848001c1460b604c1580a2541486825001c040030080200e04076030310301f02e800b060000b250160500740d1021210800c0504001d2400a030a0000c001204a201c4115501c5071181509003c50900c0200c201543c01440000e1a80da22800005807650148449140e811903000c200e20103a680b103101c0000300340102c002c08100030000c035640280a004201c07400d581d01c1056400c081203c000502c90901c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 7924926 1250 7923676 7923679
    0x71704060902011e090807050a030b0f13021005041805160f0e040207050a200109090e0304090501060201021209070f030201030504020a0302090c04031205130303050a020a08030907060201060e06 85
    0x409a559a5840c4018245000c00360704000030b81256516841c412001c2020039021610380b40c0e11a4a018842c40c40c04aa0350000c0317001e55658001000020918440301d1717080249a001004d4940c0c410285400703048403250b0295006010a0301c2100481d002130081042c0e6112100202d0142c1104c044001a1141030315582c002d0b4450b1110420418400e2041000b05200303443d142e07400340c1100000a041e6040138005480540103c03c1907010050b0705000009074a48803048003140c11740701c2c400a0708207500740c41201da009441d443c00d1917010406104650240c00440c0c810042941c480a00074000d4024603c09042c1e9541070b004a108444000303459411903000016860005066a0044001c0d00700644100d0700300e080c86401200503500c50024070702c90030390030364001d80362859802c11030417020076444a08244007080114110680301f6017041001c0d65010b082c200d9131903140420482c0ba04001c902c0207010302201006104c1c2d110000705188084450a41c004c3c01219100c41045040c0107054a81d01d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 7926176 1250 7924926 7924967
    0x806150301050915090a020a031a060405150d0903050301030318030b010902090406030609060b0108011a03040605040203100920060c0304050103150305030a050912190b09010e120d0507 81
    0x400840c0380240f40507510031490071602d5202450040800d401d52030a860b403500b400d402040d08501c056040c45140b0b800c1580440300c4c0c2c158048000883c1d070318407079800341e90300034240c0c5d9002d900c01c82807000c02c0794681c1c0b4003801c00b005407a44504004206030000c3c0070880008042e100240caa881d80e141841040da0703000804000140d00e0404800000d5000303541440d000703501c40304000041039003880b600b21401d0240d02c000c5540016180014005041604a00b0700706180d82e5680c05040110805d4a80c002e520a100148988aa00000f4541410142d814114500f001c0d00791041000c184804000b49410300640b5109105402c100800c44c080c000c0200b9055000f803100f0011507109400080550514401c1e40d002c0070307100d8440500f1544504050008a03c000466a80509001429001c0c2c0e48091000d806048d00c80c840b005144030410038064986a449c4e8049420f43e6029403149421b0041301e001c0751100d10542c0e240858a81040151851140c5070400145000f40901c2c0e48001a031003d4011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 7927426 1250 7926176 7926179
    0xb010206060906040c021207080a030b01090f03030302030c0403021905040b060702010507120507050a06020a020705060c0a0213020f040303030e01050601020c010804030c170406020309030709060f03140a06090803070806150301 99
    0x3440001c01c170a1102804520036107012032010040c8034002c0040c1d5008006955480310010800f5003a0b40c5c9180400d810000350003800c2180c0720b500c000c0841034a0345840c01590b030346c540c0840710910380613903000a50301c21050320301d00f00e003220213451800888006803018010011410308025190144540290104a0811428001034110600a0700104042c105181000036a403115403802c1e2011208403501a40043e0f250009901040080020710045400038a0580403002c1a526501e106400a00802415400140c0f00c481d54060f107406421291440c0e031100d40d48d0030010302070005a4440d4091354a005c01145155101041075961f0030340684808002d502c807503a00700d5561176010310036155498070103046140c2d801400300400c02800a40d00968407a6400010103003041740507404010818030b009002c010010000d00701404498000054400070300d0882c0c8681e0601e05c0c8510010051464160820100442d00300510300030141a42c51035159501c1d64140420022090582e0041c90f500303200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 7928676 1250 7927426 7927429
    0x212160e090a0e030f0304050708030a05120a0906021303060b0604031101051c0501030b0403080709080c120109020a1203090e10050409061b0203041508060a051009080a0b0a0b010206060906 83
    0x301c07140c114956040025080c81d28550b800d065421443c000e112410b000401e00c0b06000d404c10007500038060b1000030f107103055400e5002818a2081c8964100c064003540c001804100c81c80d4400c0401c55040750040d9612002d400b1070800501c0c446c0812104139282c034850406904000c0700380c2d001d80ba07111015a1006118600564590304007910311811301c90510a8240c19445c82e0140c00e000b140300d078494038001d00702450301a00c4240f00421410070440700101c10000b51100180340d00480500380e58818080080c0055540501a100d101a401500d40b03600040c024000d098038032a018081d43d10010f03082e84400d4442a0620195100c103019403040005112520b810f9100401862080d81d00040c490041c150948000d011401d40c20003507000418100000003890740f04400d22402d07490a086246040400248000400d00a550060840c0308040030300030f000b025040060007a0784203e4105454524100007070060842c1c0c5200018149015820385500004505008036802099961030707544610 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 7929926 1250 7928676 7928689
    0x7020d02060f040f030f02010e010c050703020f030a14030901020c0607080a1209020d0609060f020901021203070903051209010f0c02031009021f0203130e01030201020604030809030409050a0212160e 87
    0x44640000d080400c000240c2c41844c21200d401580f1034a03a08480d070762140000341501c0303805d00740d850610004030000c00000c0e0f0701241c000709599040359000013841c00c24001c0b80c40c0104002004186018200c14491891000005880d40034403d030700302c5a01a0803107003481594066820020041c107410711141325041e005645003000c030a041400050f514407590002488031440800030b17600e8a640c0d505600602403680100304501507814400d6203007441c030300c000175954000700070320300542a000b101188140e03203d10b680400554002003100c601c480170406404255100100d07150200350041220784160b80502100681140c004009d0561020146564406040e50300000c036404214054184550701307520032a060020031650045071241d058080c3d801d1031102c141c00440f501d203079450040005070b07400200241d0080d858902055a43c664600071490f600464010400031070410080210400b00b070b5001c1c018640350015030075403585840c1042d140114081260074006400340c042140d01e401c101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 7931176 1250 7929926 7929937
    0xd0e01020c04020a081e0c071e050d0215010504060b04140118080a0605011a03060d08041d040312050105010203180307080303010306020c0723040905010e120a030e0307020d0206 78
    0x60040d80c0c40740c9120000201264004010348020507030000602c00c52155125a07031800d01d62404113445d9070f042910f0356000320300030004d00510407241500b0008d0050394180d50420015484011100c6120500d0000b0f52601d401010200741800f013500002030b240b5050003007100301d68440100c5803805080c010700c0c41d44000d125004c1414080d0500601c14240255505040100000030141c0807000951403c041a07581c1a40060343c03003001c43c048000032010003800c4980000044803402d10007505860440300d54006c5920240c90440200b035002443c2c0f0b060642d81e40b00300c0c420355032000f580320103001d0402200c9080c05000d0059100380810107244070000540c003001c0d6001000c440240c5d984810140c40e591013600200d0700c40da00403903020f0440e82d00704440006070601d0008404418242c11540c0042c180070f040c0248501d840f40014402d200c802c1d440384220b54084026220490141c6032041d403d50f02075201000002d1400b5000940041d0200075900001e500420001c1400382d00d40070864103800c030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 7932426 1250 7931176 7931179
    0x605090f0d030c0f050906030105060310030507090203180a0f08030a110c0f010e060702030d090c05030114060307140d0605072007030201030c05030103020607060e070801021b0c010207080d0e 84
    0x50099a180c0400200411074042407255804204011500300081c4048644221441408030501090f90300340d03940802d980c15030b402030707881544980d00c141d01002840d20960016005004402d0089441c5d141c9070003c5100c0c41e0807020306080c01c50001d00c440e0f82c508d115040a0b000103884840c0c0000141c10500840e040107911202041a81030b18032001c410307500c0a41d202046501205141030712000c2030060002108041000e00070354688824042c0d200d220300341414061581d034078171f44c00410802036603540203810050000c0104401c40c02c150055840240c3d0261b104c0d1113034807800036810f4a5883c00c010304410280980041201c03590b500000780c0300203070400040c8414010000e0090f60401e200403543c1300c4078002003014078694000501106e494054810070400100014805a00c1e100c080320741d929400680011200d00030f80c0d140b420860340390400a09540009006614141998030703040c01418107605807004a0006801603030b8500c43c41c42988515040f02ca2007100c085d000d00402c00c4107410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 7933676 1250 7932426 7932433
    0x1203011d09100e07050901080d080a0c03090602180109080115030b04050f060f0a050703060f050d02040b09180105060d0201020a020108070201060b0301060302032703090d03050405060304060203090d030207020a03060509 96
    0x80203881c1109440c1c030f06411070402c4d0b0010f5410031280c94013490560041004901a2140c508010402000e882d4000d18000317072a07031240c00e184080c601c243d114643c01500000215140d40d624070b4514006007004c0d0b00c8900103108a00003040400041c45040b8111100d41e48005c401c0c3e00d103a46076410f40e0300082c004d441070b005001d40c0c25001d503002d001c85441403d40140c0d4400d01d02d01030850340110740c00a0a4502090b1031706900f1701840300ea008110082d6142210003440b507102e184001409030806001e51a0045910000c0c40154481e0328200c00c810001e1800a002903a960740a100e03c4d00b0601d030f4003a0040c0d00440400001d540a450520340004081c400400c4041d21005441126402079001c81c000980c00410072002554000b402040010440d05021001c5928956580d881c0944083e583c40303036407a9180c140c1094001c50407503004007806883c00d0f0300c84c40c1500709040290400ca90f5034055018103c0333100a80d0303100384200d44009a0040414107010f0a5484920007030000410001340c622 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 7934926 1250 7933676 7933693
    0x1506030b010e03010219120507020c0f040222050102010c11060c0f0403060504030509040c020c01020703140f060405070509090a0305040902030402060403020d1101091a0f0903030f0d020403051203011d09 89
    0x21030a00061043c240e0b14441082c50310011800180100090200302e01f5652421080c00344950780410075542d10b5400300d4001e4000f0700c080b00001c000380704c0c503d614a400e103410424440c0744810003072840e0494400b41c00030081e00100da08141c9005c0300303440c03081a032600020009182100c07c20060030520130f24030100c40c246501c0b40c2e00e010071a94140c4081c0c02017540803545103110314150040c1d0744412400e20180984c0112000084e546580c00e0000400000c1c0b6800740d681c03101020052403c1480060048400e1403d06040490315480e45000e03850061540c2000035511303a200007010303401e4a903d40e0702c551500f864240c0c40d100941014200300d82c0910200000005aa41e508600918074013038952034210400b0040090700b581c2031680003400c50b05400084a03100048441640c3d05060111602907503030001900090542c401c060240d1503040020030840d0420301180d0182054900c60022141e41090010f000740c1103000911420840b16243c034807c0a038400c642d89210341200401d401c94034142d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 7936176 1250 7934926 7934929
    0x70f0e04080c03070506010f0f05030604110f040603030810061103040311040f110903010b09130209100305070e07030c020703020f0402070c23030601050f0d03140705030403150507031506030b010e 86
    0x142d10240b01585e160b44040014440c254000410720018031022a8a40d0100d2070300c4003094890100400c0078040e52508001c3c43c4c1541c0f42d01100451014000703108220b155103902d005000c40c0d0055440e02d00005d03480801054050007981d0381a81c2d43c4030900110705040c41c50356100714075400d1a0810390029103500103142404070500944c2c03896100107281a0b19000d5441c00d05003181e0103142c0e800d00c600700540501c6980d200724074411424075016210002c559807400500c2e030038010141d00c020142c2c45060300002c0c0703031000b00320300c640101d880e65000d1280000c00c1c40c08030303510303c154003004e58044190300303411000307250a5000340301c5e030351180b452140401d95440e070610040380c1940031010544529400e030340f030529082c04158003401048480d0f072041c001900105440010051004051221030344001c8110070b03050b001d4809055102e0122990b45442c2e2502c10340703500344211010340c4142010049511607000e40207200e542c00c0352801d1044240c1c07a100046000e00303070b0030301e01300d051004001c1140842d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 7937426 1250 7936176 7936183
    0x60b0a090c030b03060108150405030c010510050f01090e0601030905010915050402011209080306010c031e050405010207120b06060a09030b100303030c021903120908070602120105151206041b09080f070f0e04080c 93
    0x880d02c15914841e3f062a00051090400942c09124104a81244180400703a5840246900210207280000384040382c0e1800034010010b40201801c08003c400441d40c04201d0303034210341c0c4103602c00c0c0c1c6e54a035050400b0085405139003101000401c541d20500010700107501c1001d0000c041070080c130f00103100529040302c0b05181c1c2a0305c2e0ba01d10005400042c240b01c103503010040c550060411038900f440c404410b465203100b0b000c015000070711541000500880e100c0c4600094005503400c1090018903003091200054400907622040340400d041c46001c3c55428000b00c0d0001c0040e00d01003403091401c09a6804407207201c40040e0544805030345040784000300d40400c020388140c0b440345c0c5005941d42c1500c129885159016401544039030b400c114012080da001b00f007503da218213841c92603d641c0d01c0340170010300905030b8001038903600300e0200c8664009541c0700c0904402c9603080e409540140801101e00c0e44ca4549601803ca030941020600b0841c404228040d182c1c807030b0284a0b0700d4103041c5c116015509 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 7938676 1250 7937426 7937431
    0x8070303112704110c0703060b0105070b0c0712051810031e0203040b09070305070b03060a0504050406091202011503030c020a0b0a090e070309020906010804060b0a090c030b03060108150405030c0105 87
    0x8030305400c07848540b114201032113240c180c0345100d45841d00b480450300e00c0640d568040c1c04018007998071030802c100a81d01030b400340d07010180c2c031449002d03103454102040c0c90560004002038580007507007a2000d21031402002110304540c00c4002c8810041c034980140503e44900d850703032070105035507410390030084c19510003814040d0780100b60250341ca0031300e42040740c0e074003502401c403808a03000030b0010400100d00141d958119548072400700e860760b680c040000e2040b03d540e40001e803c44d0402c01008100045039200c203a00078869820b5039045d0384081c20072801c0310150b213285007011142c0071092011070701640c16002054401401368000b81d440d241c00c01041d4114070840c030080b50082109020301c862805005500194a00e400c1141100580000c0e01601002c0e19460500002c0300108050100541203844280c0f405042c140b1b04650b0b0700200001403042c00341103400646851031440480c5000720b90305048915601c010303ca5513040902c2c421813203001070000c81f064801005850784035042809010b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 7939926 1250 7938676 7938727
    0x108010b180601050301060f020106080a0309030510090308010b07050f0a0c1a120103080a030b0a03050c03070501050403050c06030705160605040c050105030f071805060708090103060e040807030311 87
    0x1945010394040c041540341041e160070910700301c0c0e401c002869a003c019070341168818603003030560a40e0104103900600d4260000780090043c00307290024103811650712021248107030102d61820b444284c4200c1124101c000c020009501040100b2a0004490103810441c0c022002c0e101e00209080c4041c0c60548045c904960503d601e640402c400035400b8840c4598000f8801c0403458101018200f1150103014080200341402c08a094046c040c8079901c0f40d0252131010744070000040d1241406c60f551803100120500c2441a403102040303551280707040d141140e074170100800b011020b03030040000750307040140640704010083c402449419010740543c0385050168000241a0801d07050907644010260009070502008106011080307500350540356020231715240441c90b03d00c0340c42a950341c0a880380d21456211901107046018415204014418400240c13002c0102d6540c55404050b4000c0448000d842ca1906001c4000030074081c4e00014411440ac240c01494203101a044142c1110b5560489 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 7941176 1250 7939926 7939931
    0x20a05090913060b09010803070b15060d050412111203090a0c030605070e06160b0601120c09050907020a05030a050901090302040c0206040201110c0a03020f0613061e050403080d0203100806010801 86
    0x8080c0b1030f00307201d04007108a05503001c2101b58180b0800681e02e10410303500600b40c0d100704000030400700d044071403404c041900502455807000300c0c1c6078410181001366400d48400842440e1003604034000d04001c0604d000c1d0b0005080396600b911b40c2c80c506a080140000704c0c0c1e01410000c807000034401030b0f812014612404000449050940700182015807102d211801010708000e09640c4000001c02080c1455110401000550361000100c031400c4845540481560901d1005d0018581048000c2d06841058032240301e0380e0368148040780d64011005c5c02500130b03041002427241c0144141c2c01060a5001810941581d0780d41358045011a4040c000c0e03100180c109009000c21582c0c0585288050841c1c0c0300103110511045000640310082c42c1320080c49210180080d00094403100c0689150b0340310f080300441400c7e52070b10050800035000950701b1600201d0f408054400307009400740c0341500d8010003501c0c01d20500c0080d130f5000394009410317410320307034a13140000800d94001c001c070602070720a80c1f001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 7942426 1250 7941176 7941211
    0x4090203010b0a080c0403020607060903020c060c0a02041107170a030e100e060708010b0a111009030c0b010603050f01050103020d0209040908040911040b070308040206130e04020109080c0a0603020a050909 90
    0x2020729a01070305c010303041c000030001000503a070b8010a0320f4041e50000c20008284800c0c0ca800d03441c04082c0124180c2080001c2041c3c00500000700e10f040d00703207009440c1400b0006180840e554103100301c510080845c4810381c0307420a042d03021b03805400d400c00903040c00620080d60402c0c0ca80b41c50403150707050f2031454803405482510502886002c5e0030201c03138204100a0f504011200c0c0450207070f111301400700000d090400c139104404000c0c0341894100098200081116814014221311448030180c4c2e00c50301e000c0001902c0e0303101c3d100d09849007000043c242107036401c020044019520200030440000e40a101c40301c91940c0e03520802c48194410056203594602e003400a409907008a2041c2c0d0b50020244070410500c141a0100c0b4066545481d08000560340ca1000600c5c60140d00c103443c48070842200041000d681c0e68000318000d6000b600e071440c80c2e6507105201036032901030000c016049212040100712813406a005400448001c0c14038500b04000c02c00070400350f0108070380c4404c2c6400020f60 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 7943676 1250 7942426 7942447
    0x507030803092a0f01030b0303070609080408070503060c0412030c06020a020106080705040209010e04020901050c0307030302091e010c031808120310050a0f0b0702130507021b040b0a0b07060204090203010b 90
    0x26000d189a82e00e030f21441c040342c0c43d40e0001da0200140c2004505150310b420213245640e80a004480d00c5580c032003410420424141008043c0e6007160194120f03502c0b9000010802d450000350140c0703c0c4607000e0400d4500b41c141031162181c40c490700700440911044070070b0000011641d0002d8503e4181f15800001d00300e10301240c00d8500350481d400540940d1041044203100c4e68000c03204100c0107020360740946c1c0c0c0c01c030380d4004039128481d0792040c002c64000410100d00701a4944c005081c2003030100c2e401c90914980040681e10480c01c05038660110f401c1e21f40b4000000c0c00340c0f40c1e61484e00c1c56840c56208061381c60300028109071008041c00d0702401c0c000301f0041001c01c1c8200c0400581426210440100d00308160541505000e000b041040702e4049064003c43d910b44000d12240d684e84c21080c02941003004019580303003856000749951450040c150103450600f8401c050310a100242080c5940d0b1500b003400c005644180e0013900c044e07408220114070000310f4001103008011402c1070940d505403261 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 7944926 1250 7943676 7943713
    0xf040506010510050d0515040204150201050714070b15040203090a051203041101200a060c080a0b0907030c02010b030703050a05070b0301060e0111100c0302030a0f0509030a030207050703080309 85
    0x801852180a280f19220310350340e804825101c036028240c000003078035141d840c240e4074001204014107510500000f0302058060052100c070b1546d4000d50020b01080d01d41e07410544040e09071054155140c0010b000c508081000c0108890f001121324107254460f16802003c101aa0710465100f0001c2e4845003800c0100a401c000355030252030f20000c01d6003541896521007d0048203416001d040003800c2c034041044420381c8030324564024000c021951501c002d4a040e501806103030050754049922000040c1802050340139a100000000304181400d03640c400e400e800414190090904540d681c04103500207440401c4084041c0d1702a0300103104550321440d04d640781050541060540e40c50520040218503048009c084200741c003420b0000369203010036549031400184903400d844050a204000020a030541e00441c00b03000070700010301130800700100354001e8076000d8030b08120070303402003010704081c0b8407903806400e14510403400c5e24407090796500c410039180c0080e98034080796042420402160860345 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 7946176 1250 7944926 7944929
    0x3100923160605070c050d0c08010501081501050102030a0e061803100506100c0308010501050d0e061807060302090f040f0b0312030a1401030209060108090102040503070303030603060605030c060301030809010201140f04050601 99
    0xf481d01a1601c040f640e00c8000c00c0c6050710925006030b144400c041c0c02c100b150070141c4040e00c4c4280080202e580c2d1810440d46e0f50b2003208070080c040d9101c0d800070549500c00300c11114460025182d07240c112501e001440b80c0e580c44506082031120344d4212251031641d0500c10110349842a641c08521030810600300710941ea5030101c0755061090b09101c3c0300000f41c1000000d811900c003400c105468015280300900a01025491017460f40500800c0140c2c0b19100c00d0000c0740a04010119520035444150030f404034811502d415070f01c00c003010311010903841c043c0c10001e4414080980030170040c2d40300020078584084202182e200030070120070084181082d100d404108c25050b801d810995140d0f4001c158000c00161101c0d04101c410f400142502d0360940465005002c094102c070103056403420010020000b900044511900b4908001a680b13000109803c006200804084c0f40da4655960258160700086000f4195504c0381da46400d0841c18000591148404840d010550f01e054030300203003060b405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 7947426 1250 7946176 7946189
    0x309040f020918060303070f030206070e01030c0e0603091203040b01031401150b030601090317070203060a05070f050a03060801050403080105030114070509010c030306030203100c0f09050310092316 87
    0x5200c80c0b034042e41d80140b8607112101007030072440281c45650101e4158031030540007602800001c00a9001c041e80000c2c543e100c0c6485640340d00c40044440c004500791103440d20154001840456042c81c145845001103410615510403210b055640c00c0c2c04042642085409442541c0c0d200c0041051141041640035042c0070070008106450340300000192281c0d280c040e8010340d1401000007602a4000c40c005405513801c0301244056101c003903c2c03803d107648401d004038001d01420000c503c0c600300340e0240600440180e110350b00b000345504000c407055041000240308145d01c030701340014203581c00e00c600c40c0298000e5540c80c503507605003002e250948500141404195014170200441c080d401000c3e102d5100003446c12000d04009410120040d14540d00003940c1030281d0000711810280d80da0004000e440301d03845900c82000480e000b5103540352588075460300740d044481c07145a00b958a03803041c03502900c92902c0c1c8c500d540c4404101a40000304d43c0500350544c0c4200b1942240d0a41c500c0d10300d00501e0b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 7948676 1250 7947426 7947431
    0xc18030311100c0804030e06070b040501060503010c050c0a02120a0b150f0603070c080904020c0102160501060503070602071203030f020307090f0906120210030b1002060402010806090906071107090e0309040f 91
    0x83c55100503e010030040c0060300b0860348801060f4240d40c1d40084508580d0041910309103802d243c2001c50080041e4400e19103c0c1d8078100214001034001c400340c42131800f00304042c00c18540c46809001642d1070000c05008640242c82c080c40000700d5520300c41d40141d4035007940c451100d801005010705003001c3c20a15106100900c108030043d9404560104c941c0d51090010341c881d1400404640a401104124000d80d4000315120b000c00001080b00e41d4180d001d000203100181c0d444080c561111040c2c0148001604000003d10000000b14141c1e4a40d80c424600020b003a00e1418080080341c00544480000624540302080030126502c032510140915600c100002e52411105103549101c401c4001e02a80e5104402d2404600981c00840364004c0545a044401210a00203450308004c56080313021406000101c1e245040400d0302c1c61203039600718001c0a250300c60031810354810680340312035419440b50007400305608003e17004113040200c0c200c7c000d50b1215142c204120550b0340d100095034003c0d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 7949926 1250 7948676 7948691
    0x301053622110409060b030a050105100b030415020c030403140a050d090602031b1005010b04150203040303050702121f020c010b04050921040504050f0402040c0c020303030a0c1803031110 82
    0x28040741c507403141c2c0d0108540c00204a6100d01d09000a0420f65014581c907002d1401070400b03001044d000184502040350030308034001e46031004010130380001e9501800111596445850b03044866000301010710b00d40c0112404c140d40ca6940c100c00300c03010f40c44908650400710081040000c00c0014451070009820041002e070f0074050000e640340030705644540f10341e005014040c003141080c051103c44400304002070125684444200000c1e41c001d118003001c925608106001c0644080b0982e01541d80c5941d52600c0c240c225000c200407910740c86e9140c6a14054050454204100c03e138041201d40d0340c10f600580c0b5022000e40381d60840d1584141c0c0c0303000e10704000c100002510007040200e800424444901f1404503410720040e003c2c0299040113030001e1030300042c0844007121080440c03003a03100719006d200c10b000561085a02004042c03000703405078400e001042100e10281c10a84000300d2500e46507100a070100d03480149040d4139031040d00440ca0884d55446003500034000f18402c403034140c1d030901c44034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 7951176 1250 7949926 7949933
    0x10504050d0f0c0b0708010503120306090403050306030c04050403020d1206050a05010f140d090c05010c020904020906010e030102030a060302030607080106020d03020f0c010e0706091202060301053622 88
    0x504000030207104001a2031184085180102c1000c100d264100485000619182d5806000c404083c0141d51180c4100e048c0380000030b442d40700f2207204a0340034045ca40305031074540c2d00380c0e42c94201604260303050040800914940c0c42c5c901c20148158000c1d401042030f2580545c01a003c00400d05024400506042080c403850b121080c184048034002c0c41c01c43c480c0074207140101d48501c440207940c0010440011100c038040702a80180341d4503030281030b4071041d495035000156417400200000a40001c0e03e0343c0064090300d4950109540b1600604003a41c1c203902c80c00002c0c2c22680f04440d4120f00720b0307492106106600701080200e92048103400d04070220b505004000e07540d014114030440030190000303080420581c4800276245d000b520b01c0024405861101e00d069180c100d540030300d40000348180c0c0300040340c0c03441d0141c0d940103d03009052140b03580d003840180b102c10031040c4444214400342c1d040212000c00350302d120490311100140c2000d41030920b03c6404100309440d006d0800c003168005002c4011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 7952426 1250 7951176 7951183
    0x109050a0206090a030f0c1509081906150303090801060506030f1302010912060218010e061b010b0909030301060e0910060305131709031903050f030a020d0219020f01050405 76
    0x10a40480302c0a4480c0b040320000342002d009900001c100000b0218400c041000000100c8143c0d4200078541a9400500a084514448900c140d82d001e078000102c00510910b80c102210701c990040e60301041d00748054616481c010000c0c4e208500084000204020f10403003882504040e1000719400d41c5103007801410f0740741070540500307080c07890f4200106140444e03000e150b81c003000705114801c0c0488843d07941403000c029044052200050901e00d1081d80541d032059003000f00f5400014186410010800701840e8508902c600d01d500a6507521344641495450402080c410040032006564030341c1441c20080009c80d609000300c0c00b0302021070512554155035003e00c4c050341c490b4600029607a40c1c0d4400a0b060441a040241a0a0b091528030303800b006140001c0a500c0e009030b00306c403a0110080360403059004240800380015800380b00284501180e440295040401c035440503003031092900c00f00089074880703608098002c102c214140721098061020710b051082c040002c100070302d8a0380f00c0549 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 7953676 1250 7952426 7952443
    0x1e030708010501081504090f020306060109050102031e13080106061101050105090109020f1e0c0c01050301030203061b04030c080c0406060e0d060e030f031e0603030a0e010804020402071202100608010905 89
    0x610001300c001401201502810800b40c02c002442485080c0c42030030011107200400c50240d00030b001d0600001c0c0654040c004020481c0c406900841c50111051045030384401020800440200c0800800407586540c500f0074014003240070000079094034000c4054807003008003050741d0711641050b004109650b2410162030440301c12403800750740c441c03d110800c0058840c1e03419986404416800c0c56803402c1981c0081c018004004044401c44c2081000654040c0424400203503d0f03400040001c13a00b08911071001c000d02c204060711803c1c96100e950b5601903071800e400941c0c456204a440008030300d410701407800180303050b0902400c0c407110070011a000380c507568800307010140c56070360440e00c1400400468000607010b0061503183c1c10a13080d2070003030041801d039600000d0880c0c00490024a404411501100c48540f14418004400750064071a074000501c10b0364801d500788000004185100410b860b020a160301611000781081103032022a6504d80000b90300c0ea140403640701c00900d00003071904 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 7954926 1250 7953676 7953679
    0x8071503020a141803010501080102071523010e07120e0307170405120f07090c020703060b010c0b091f0c05090f0a0909051014040209010e040f06050702031e0307080105 74
    0x160ba8100140d025600350085400000e0703000303400100704043e803802010540e00080210000c0c0041c0c0d07a90341886081c1c1c0180728024203500903501030040ba031000350740280000c41810b81014108600c1c0403480c2c0d01140242d01400b10022402c04115005078800e080e01c85036043c61800300110980008201c1e40ca004001c0020b0980700c01104c044c010018a0080c0c40003010010118920315242003601920388010b0244095684100440491582e480703014000c9103c1c1c803a4000c00c04145580c0701c6801504130940102d040c4014200600c02003450308460768414007406005200000220300925690f210403540380500909d029075452030b86a1223822950012000c4030380754023a4068400107502d6030407903402141045d1030060b2110402002040718540f0090001d01003028000711381d525251100101d800075440001540103002c0d40e200419400e030064015402040500700a5a52804965060740c20b4070241c0d01c080f418501101d1001004002240c103003a60506508001d0000303001c074001030140c203 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 7956176 1250 7954926 7954931
    0x3020c181807051201060608090622110303030703020405031c0503010b0d0b06070318060c08030103020108040812010e061009030809040b01021603110f030604030915020a051203010e0108071503 85
    0xa1007010070411a0080c16000703000c041911105018103000745030511900d0085000003001481e151804200184200140500d03039042e03040780480d00c00100c01d45c03030044a0310411208000380540b020006140300d01e4580c1c40059856080104043c682401e64806442c0081075100d1403103070562241c1600d04655904400035150b90403c401c070130140c0b4001c451070750407160209241c0b003850703070000f03600102000185000c0c43c40d6442d40c20403200e1203042600070b88080c1d8200010801035104444155009005030650341c1029881070003a0a103110070380c030009800c281c004c2400b00600d82056901034000660408540061941d41ca1840d540249244940b06946e43c80392401c250340240441110061440001000e282c0c0700c0c50652810310540c0006400f405103680c0004403400c00141085c01142c1545400c5012440c0c0710f04401c80c2d0207903000d040110701030120400005113040140b01015009e0520441d140d40c1450b40c0b01d079284605a002c001294000c0d8802c00c009094900004401006890017 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 7957426 1250 7956176 7956211
    0x9040f0b07020f03030a050106090e0405070302060a030b060d0b0f040b0f0d0c0302060a110c0f01050d0903030b0409030509031002030f0f040201200109120f050901030b030c0a1203020c18 82
    0x183d05120151452542c40e010020400c9a910100d6005a0689880c1d4581407015a16480c030141e01e54001c4074003c040d580466024405450008003030025554a89400714940840002180e0160058500603109903100c4845218600d403002c0003101c80e113020b0790100002e070040030008040410309000309000300110a0f14809101ea0030500002640d00030f012242e4482a00768000c0141c00b4445510009002d0f64108400c0307440c0c00b011100111005940365030415042c01c22080040c600c44d2011010f06070ba6452148164586005000c3c0c040e0181c2c868517107581c492824181400402e080015016104008021038050030340a41c507000301c2040c51841c884da03921304c0103807034091101c40c0100c4210b200c102c40000008ac1500120380307041c880d03414401c4050020a040d6910a000380c40d400c04100c00f40140310081d4440c1d880040c05000050482e44615140e101040c10a00c1c10340283d8480702d0802c1c00c240270f0540400c00c0840344101950458801d40d219070031140713000310191045140d810341001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 7958676 1250 7957426 7957441
    0x2010c080906061c02180702030a02010e1203190608070b040e1b040e09030d090c0314160b07080403020405010902070b150f04020a05120708010f06030b09040318030501020a170609040f0b 82
    0x1c2100844615a04001c0c1d141414080627607a6004125820f0066083c604500508000400ca003000d0f400b60390398550442d1102c5031000213280c07010009500942c0c0d54071000070141401c000e10001000c0b0403811560b07031410141645000c1d0002810660010790a000c00014074003480219011202d851820090756142d00d9202400c40c0701d0758200c030044c07a04040c809000e000701c010044040b00c1c410a0062034800660451a0321441c4044d42c0309821000c00200708026088074004015a5200340312440c589512940003608441e02038221816681d404110402002000740b02290048501d191b18100d101c20800029400d2030317050340440c0a140c020500d11216401501a1402c0c1100b07000b901c1443d2401000081241d9000d21401b0342c602e145840004000303029200d42110080003400040b0150b0b1192001c0e1540502a00e1003103042556140c00404070700c0c02c0c40030b031580d5042030341e42da803048c40c0b000b80c0c0c0000b03a50040c0c610b078440e01c07000b014000001c00c5040d02501a951000f000c3c25144d032080c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 7959926 1250 7958676 7958689
    0x103020303070611040b0c060106030c02010b03101503050f0606190803190302070501091a0a0e12030402060c07090501060306050103020c061f08030f030402040c021c03020c0c040204030302010c080906061c02 91
    0x240000048500490302c4a0b081f180814424140c0b88550390801052130420710407403d90380d1010304240c00da04102c0158080400b15000501c22604000040301c00c16a01e555092516901c40000c07040d43c1c00074414480f4518162200b00504841c80814604050a08140750345a115840310021091615001403001034000d405482d01960000000c101c01d0b40c03142402503035420301601162003045281c002902d00040fa10407030403a201b03840014000b400300d0351083d61055001400030f9034001428130030060224010403125014058034070300402d82e54035188014081d9001d0342c001d281410300501c0407046444000452550008007583c0c080031121403075400311341444180c1c00006880c0400280403030803418a00042d40103610070b0b9410024140c0700d25049850386c04110106020f0658034a0b500b441d140b090b0054201c1b4408802a540400d1020000408a0b40301d980100c0c0542d46406880091b035811400c6036902904030400b0300010b02d4100001510040d40010706c001250003401c44a0a42d107179031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 7961176 1250 7959926 7959929
    0x203071109010612022802030306090709140409060b211908120402010c17090108010e040308010513020405030109150e010b06091201060803070f020909010207050303060603040201020109021801060e010206010302030307061104 99
    0x18110011b8030200c484000e4981d4801c8499500510b54074000c9410544126610710446041007880d0801d202484c4c1084040e10a8180980740ca0b910b401d40300da1195141d4400341e80038021040404070844600303031614103141c5030000d0154005148400303c0040b5100038200d8104036070b019100807241d601c8d880181c4400c52050310207000801c09141250319110305c18020080c070326003605c91180c5a0390300d04404001290840c0c00400082e0f03a50010482070074290012140080251805414540c552001c6030840b01c410106480c4508240b00c0d01824040a210304014100420000c1c8400308811003c12001d1103401052401040214001c15001c203013035103d0f0300548106010b0740d5481e0fa1a061202e8603084e8803109a120f007403940c000c04c0341058144216045154030401279821661041c2c208059500000c009906554a549103200144da9596403002e040c0041c00c107000c855410800001e107044900188203066511503801440582e80004c1a40e511903842000841c840700d104c1d052114a0249 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 7962426 1250 7961176 7961227
    0x70201030b01110601080102040609170a08030c070f050d030506061216030e07090b01020106051801140609030a140c0103090c090f021902010209030606060405010806040c02011803020307110901061202 88
    0x207044c00440c401106400400031506141d990054503134035071140c030f1040e2071640c003c6502035000340c0c00d5200040059000e50707400520400001e08055043d00c0b80044200709000407182d5420a120b00e0a076aa010302c01c082d001402603c2c154240000b11140304502c42c0060500d081303040075210404101031294121004c0c0e40103000070b482a0340c1ea201c5281c009000e1500901c0d0140d401c04070301060303d040000309400f01840304940e071050341c0d181030b0301062400c0c511030150740c2201040051401e41d88040000840017031142140445030340030111044d0070b20f0318102c3c83c207042600f0001484041810341c20030034140d03042d01c0c5002403140003000b5580d0007482109079041c1740e98400300d01c480f0070b141c041d40a041d201e41c040e015624150b8400c000c014640c070446c090140032a59403008140c00d82404d5105250000f51800001000741a601e40c46000010f8120b0480040c0e0000644c80100816121810101481a20400101d50504601501356040b08124001543d804241502c0c4006d0350030301004000318 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 7963676 1250 7962426 7962433
    0x50117090a03110f0f1c05030705030c0702010203040306060e040b090106050a030b0a020d0903050301060914090c090a03080409090203070e07020604030f0e06120106080609040c06030c12020f0705060a050705070201030b0111 98
    0x200700d80c4061b04c07940500000c2d0b00c10b00050310b810300842e00401c01c892040301290341fa145540d8030304400d60842c2d0448a8140d04500c0140008030010b8040d10482c1c000d010320500c82c040600c0c003458001e1244200400c403240c185d062200400854540d07101241c2a20391118000702281d44916010b40240140111000c0c01e600b403010107000c0c96001801107040c0c81c00790303980c00520364403400c1c0d0003501604440410340200e0034030b001401c0050f440e03014101101c0001c00b014803039a41d030303101c3c0341d0a604030f5003115004035983e22a55046207410400d102c0103007150071038444180b0b406103029460300c030300800c09014450301840405815120714042d42d0003043c002c00c9161100e000d25040006582c0c01d00440000c504c1e074101042c180d14049801912899006a540c480d40341405012800340001c1440716080c40711510280303420742e0f002e00182c5140085003411a807079100e5414010f1500e01c0c0075210860540c070381014040425403010413142030540a003404901d03414070780700491307101003284032103580c030700 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 7964926 1250 7963676 7963693
    0x3020d0609060608090f0a0308060d06060602010209031009050601031103072706080109050a0305130509130506070f140306010504080a0b0901060503150a0c09051207050117090a03110f 81
    0x3440741c0c1c410002e5511655901c542541d400c01c0440e075800700da82106095034415442d01c0002840f65a10320340c08503024140c5042c80d141c560710303c000e5801a401c0138008d41d40205903c44103042c20454046104440385050040c13107403944810761a000c040c0000343c81403662400b00030306510b0400c10304009000c0c210301100d11240b044c0c0c8a081daa203100203108002802c0160000f62250140a201980c50708078024100507505903409613041e9004881c41400d071200c5c3c28001806590358143c00b1321846c1c1c00c12a0036034080d9185030203401c0240040c1f05505110200c5420703a1481e80c018901c002140e9418070080e500d480d000c00584840c040c2d540082d49901c614800394041050400170107000f0b1001c04028481b03a601d80c4101070301d6148a159a00c014031342c8400081a01140390800c2286c5903250400701320440e2584081050700d03070322510020603548122030401c0039591015660030076100400803a074241c101101131948600d0084400f400700001c48400b0021820140022042c0180c1d1030106c40d00d54 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 7966176 1250 7964926 7964939
    0x30509060415080c07150f0605041a041112041e020603010902070b01150c0602070c0b0a050a0e010504030305120601020c0405101403010504050303061c0b0a02120603010b060f0a03020d06 82
    0x40040c2d960b60b000030700004081050005214241c0e500c0b1039101e503440069400c0130a0300b80062619030060b42119031903100010b4684c81d544a11100b010230b042c0c4a04600c0f01074824401640c0150072061840c15040045405000b22000030540065219010038071145e510038540300801d009000181d40304000000004800340f03942e004010039842081c0030016a80d8900612190585100940300483c3d03419108000286442d40101905885400c0c11a01a6120081030515800c02414040450000a081c3e0552034024802c034804000034a0001e241c2401c69400070103a0090504000151145c1400700e82e00b60b00034802d060100100cc0d0040140346450468100d00c10143d1041088041100f4503611183c20107004071403085030884015461a01c84c00c0520485414902807401c0d000c0224443c0c8000500f2441082d0250380d1001000d616000e000c5102ca40101014103418480da24004242205458036002d603600d8096084d03500340c4555000c401580680325031480d14040c1850400301040783c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 7967426 1250 7966176 7966199
    0xc12010f03030e03010c050906070f05010609020306210d050d0e01050a060f0f03020618030307050607050a030b060c0a060e0f030c0f01060519030f03030b0d03020105010806091b0603040305090604 86
    0x1101e009560303c05a200814052500b01c5840030750600004800304091680c41c10b00728001c28040d4860301c0c1c0051000d04580b0b40b10308441311a0400f0700d0f940d4000007400890300c0c0201c4240184000203032800c0c0001c1c1000301450b601c44045903800103100f0049944010020343e94440d003544032009000b80440c2ca4487c0d000c4005012601502900e0801040d0102d0058080d40b0300c0c1c42034943c00740c00c140c5002c8003404400c1c40d0280032110703907134548801c002803000100c00344103050040c031b0f1039195a600c40d4034102e17001d0141d60080310b445020300e20911410000b040d0000d0030420403a0428800a4400102318940f820020409001440e40c0f000103000c05101100248941c011146c49000f04101511007042290741c01145440c900c00d0300b030540051005c07964005180c5005446802e000030030410180100341c0300c03a110141a000b5035510801004295001c0c070a031544034002d080684002031404003181c5480c40461044c5025050200000b41010f005604036403450384001c028a8545a903003da9444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 7968676 1250 7967426 7967429
    0x3140601030203060a0c0c080d06080a080405030712020f0f01030b03030423060702100503090a061d06070503060d0b04050708070e0a0608030a0c020409060b040c0f02011505180c12010f 81
    0x380302d07420004100da0f0700c1e4421b10b20300003074555607041c0f01c0410b07480d0103e960300b150300a22061070741d0340710004a01c0410850344061038424109180c681c1d00e00f40030141000d40c0c4d40d10000740c0013500840f4000580d5a420009440c0c80102d8000000400000049004000d030003445501444001408540300c4111489500482e51408400c07041003484018000b42e40203001c0f000303401603020326030450303407030f010b5001740d6403024005048445040c4144c46101c00d880030942c400141011528100c0314000080c0181584071260342003040c954100400440c10723811014001030706044410300440c082000a008080041818104560100340c8038404000d0401c401d6075094011031070400c2c00201d802000c02500d55105598641e03101058886e02400080c0070440c00841d0040c1da104450841580c1d03920543c00110b006a03204420300c1031519020742141c9002d110800450310350034042000d40e4400410301d0b8554034036181c0036510340700c000307502d01107000d80342d017442c0e41d55801d40000c0b400386001030a100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 7969926 1250 7968676 7968679
    0xb0307060309150c0c020d05030c01050c040501021903050906090301020d05070f02070f03050714010309050106080105060f061206010c03021f091106030405071e090f090b060312030a0902040204031406010302 91
    0x42c4081c0005502102c41800500c4c01003140003c40c0000b5191a90003654614064015603103410424000306007100c2c02100d414501040c00315082c012541c0c10000f002003051201101422440252005000c600405591a100b0317100020844002c0c0c4081d0141d40c092007440c141409035041600e0007030311010b1641821070051041101c00110042152184000c0301d400a001e40401d90034800d5404441400280803414180c81e4481a03000880920501006014007000040c160410404001d6060340c0c403201303948134400503c18685034419407a05150040c00c00d08180503004580d1034103906140d100701251844424041d04000c2d802101d0700f060400c0703841903246000c4100c50b901003010720b01094401600c690310400d024444526484902080100040161005240e507811441c0a0f144058900c542054441c40c528080240c203050b4a82c1120084000d454010345000c0c4003e15400000d00b4000c2403501d40c0680e100b5512181e040b14055500465003071800d100c214002c5075568070a1100301e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 7971176 1250 7969926 7969943
    0x30606090204051504060e04051e070c0302100c050f03060a0b030a0906050f0f041101021c030609050105030c01050307032f0307020d080108070501050f040806090a05011109090703020705010b0307060309 89
    0x1141445130202100e083c0d40c0305481d503008003691117060000400004000755450f2a03000e4030300742d440f54007030300b6a07200d09240c0e81c607503600b2a0300d85802414408401c2076400001e040150641d80306422405407280c1c50007044180e5100c0e91054000b4240b543c0b01e904c000b84581c800024001111150b41210300518040c0100b8803254070f804180b02c20301d05040340c0808501d41d9502c00b140009207c41140d1801110501c11588007031030300b904501b0820081040c1c203010940d40d01080050b10320f0b80c01080e00509049024090203800c08001a00030f02c001802d401c02c066980c4140700000840e002e00c07044d0115608030104250030384004c4000c180c0d02c10740301c483c094072401c1e1030b06201e24030030b4209905031500356016041742d610b400015201c80d088103180020525042c031020444550801280e4032551100000308a00e00030790a016085420b441c00484080e04200001d00b0291101e17030400da0044003070b19006907030b241903041480c01480741f018410f5150158030380008211354190030079803456021340c080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 7972426 1250 7971176 7971199
    0x617010b06030c070803060f06030703090b060a03020312030a09080d050103050c12071403010f05090109170c03090108040201030902120d0311071e020310090f0606080d080406020d0603060609020405 87
    0x802001d4002140c03841c109060400400002856450296170803210140c28048580452030014055400880e1040700090380d90a140050040100000e600140e0503104401640d0464020035156460210140000c0c3c5000011500056940c2c4c01524611340151a02c5e840b07044010304400030706000e120030381ea80e10403008a00340c1841c001446102d0240d040e401040341a1400e54a01c1682d8448102ca0b6819542e80810081d412110700401703215420071400011b0001c2c070f6240041c18420000f00c2e07900780400c00e1043d6041c0340000411941c01102c00d080c00011070341c0d1840105c001c0d0902d094029004800b0404075444004005846a02403c558406020729101e19405002e24014008003515403a481d0001011088154140051b030b540050300f41da4201c08101c02010541d40300410440d640074220319160140b103403078482c0c2e1010786640b2001e450034038040c00000304140005400981099800a10400c0118169100d00d002b5a40480c052190958034490300f0000d42003403107100e02400c451281c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 7973676 1250 7972426 7972429
    0x90b0601030b030d12180c050a060206040506040204050c0705010c03060509060f0105040302090406060503030301030308061527010203190207050f0907120203040507031401020901020f060108070302010c150617010b 94
    0x74020402c8018004081d02e0046610403101c2c44901a0000036440d80c0780740d02504241103000100c0d0150040c0c1d408200c080c50304080c40305000e01948000c0c1150010300a010000c0c0000c43c10541080d01200c0100765500c4030140c100083c860014000e05d5586050701c04a079058254010404480c0100e40c1a9100d980e02424025503804040c1c0b502d0020720104001d10051408000309500a40030701c0000030b40507110320109286a2007a0010b402058642d0200615454100e01200000301c15040f41d82c00c5c0545008558528500510f092208010902c0714400b164820001c3e208140758030450f8440b0003403ca000030752680024040c45024120b150b0303520b00c041c1030403d0800d01034005542e400409500140300b020003504090000c981e280104040080400d048081003000c05900b1000180d0f554075600029280c0f0046452104c2540c0100740104078030308011492508998080c2023205c5400344600d04000e0704000c00c101088260315100c0003041002501002c5003006c000c42c1c0007040765500000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 7974926 1250 7973676 7973681
    0x80c04050109031e0204090c180209100c05010e01020301062609060f07090305010f051f030201090504090201090504060f03030f11060a0c170f06040b09160c0311030d090b060103 78
    0x90030740400c80c820800c2000490500c603e40307446409100030311100c0660b034005000d03600c80c00026034074800c4a55090015484500c0704c0c440d240400001146411003c0300451403114404482c1d80c00d0112102401c0d05024003900003a02c0010510021503032585c580802030552040c13062100c1d003101c040755003050005d18041d491405071007401300400d810340c2e030072000c501e50140041c040c004001c600c13100013001030750900a0940c903c403001004900351904080d000a698400c0808400302c4141100401c0540d810000203010388000352408151044103000503610310400c0d81c4680c1d00145001c10000c0c428248500d18000d03203110365115501c1c0c40e04e11208a51014000c0e00c410302c0d50f000310000c5200d40e8003941c40070031002c0650910f0340d1042c204407582c045141c01203ea907a404c1224004001d103500c0c20740f04da002c0307030740c02228400f0417410104450726034081c3c2d5540d107605125058000c10241802000017031076003000d134011299100341c412458006850f4074581103908007102008240a5800313030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 7976176 1250 7974926 7974929
    0x10b030a050601030609030c060903051905070c03030810030b09030a1412010b0d140702071509080606060c1204030503090f090403050306090a020d020408070509010b04030b01030f03020c0603040b07080c04 90
    0x2078002d020b81d9003513880c0e0b2030080c0807601c4228203000d2030701c100600080e8103000c0c00703543c54040d0710741940b61380c1d541d111a00d1010400b0104410010f0801c9110009044030980105807034052829010340c1d6a103d4081c42c001e0701e5500068031135544038040129115000000b4044460345a40c0d120f00414201d1400c104d5000e144402a2504000c0300140300b51003c1c103000e4511850b0003e40403d0700030f40c0e03c540d0154460242d4803040141c111102c24460785e154105160356141c55458804000c91402d948951103420290a040c0b01c1c00000901854041003000307402c82c0c44105030510ba42e02d07640e900c0c0c40d1743d40360f120703070080d41c003481c4038030040c08507072400140c0c20744103d401d52121403840d51150b003004030f1030f00028000b2807010303401d0040e86c030058030070b02c040d00150002c84020401d2070700384020065a004168842034003080100800e20003e1601c5000904499010500c0304e841103a5103416401d00c204150070f00d070012000b000304000d00c08201d4031540243d45030348407100c1684400e00ea803002c500c500d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 7977426 1250 7976176 7976183
    0xf0207170705281e0201080603060705040603020d02040302030723030c0d0308040c0806070c02040608010b0114071703040f060c080103050d1101090f03050310080601050a05010509010302070c090608010b030a 91
    0x86035655000c400441c1e000c06032404490422002040c1aa211144e0300c00d160707040700d08040c110412108658000320050780114003100180182d03e0440c0c03000f0580e100320b004103030030580c020445140b0400c090b01950b000d142d00034140c51088cd184c410749030001c04080d010740040c05a6203440142810080345420800e10050001c1d541e05c881524160b42080002e4000c5900b40c420000000d415941800494020009561024010107481c0108401e890082e0854509a490480600b5441ea0040103945502c044008040d80303a440300d04144600884050441d4600c078400403c010802806c1018486010310034003040040740d0669400311110402400000c00b030f68010701c4025220f0340503105a0701401c030244004110319501c1c0c0d84031441240a002c00720081200441130101c011841ca030b404003d8103c1c1c60040400f076160400186141000b40300300f80c180080003800f4511030344250121901c858024403c4003600d9074070a800c41c01060f251140081307951800a610b075240c9004034105000c42d80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 7978676 1250 7977426 7977433
    0x1006050a060509010e030d0f0e18040209060a030b01060c0201030606030b10050d02070204062312150c040905130c0602070303080c09010203041503020304030e010c02030d030b0303040503010f0207170705 89
    0x3070a00c25075a075030101c01e615040c003c156960f04201c0d50f040110242e0391904d582e07076424030b015441000e0110030040036401d00c56400c1d0700030207001d64247c171901603020350106c403501300350b489140101d0171140540e0000b5100100c55800483c1250300b150503680030600c00e0f64101320180d6211401c504a03504098107076031201c02d00012850b414800c1015180e484c5410500501e031aa4540c0000d080300c146520a42100c5001d80c44441101c0d44000405407a030001d417001d07004e030301810032221703140c440c0c03240000507990006002c10000794101c41079901400108000b00070b28108001c2511780c110303400b0421950041d2018021600510201d500e00c1220b51640392488a034880e12000c103e00d40020b0b80860440c4014803001030700e8040030855919004280c5c800607039034146400d0007003011058148036414010004038080c0140c80010b4036a4058803946000030301400800c00080c1184500da0003d54075600f4400714403900c02c826030081c401e0510690808110984402c030000b298040d104004d00541c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 7979926 1250 7978676 7978679
    0x1081606120509010e030c060103110301110a0c030c140c09070306081002090d0609210201200307030603150204081005010815040312060e01090c0c050706030b01050906070501020307021006050a 85
    0x40250040783e00710340e410002144014441c204140f55030403c0c100e0f40c034681d00c48001017090021001034440c0303014085d002402488070040310400ca0744560b900810400c2100301e546d40900d44a01103000b01141d001d081c00410707641030381886a84801c804d181c0c520450540020640160103807042c1401ca90810002e400041102c2c0c200c58001e4000d04903003504074010011140c005000c0e881116101d9100300903c0d0340040051207640b11030102000e9681c15a1315102c01060b200048d0440c0001103854a180c0726901d07074032034a0440240c4095480207150508280880300300542d1a0090000e8030a4402103070880c840030340806094910a2054000c2ca070000140c10100b06101d0005651150180c140140c000c242c4025020407251294080c542074121000140880c40003030091450b01ca000d850300c01c0c0d41c400143c54490b11f403441c82c400c0b00f0916036141125901c5d6409501035a590b44401031829803038042c4c03401c0860217503204880c082c005004811980034191090321035107060340c501030580c0141f00e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 7981176 1250 7979926 7979957
    0xb04031208041113020408120a090602060408070f0f060f0b13050c0d050c0f0403030216060804031d0a09090b0402040b030604050a060506040b0310060603150e040b0a11030106030501081606 83
    0xa1130000e4070b40c00da03000c010100c1c1108080100c080a2040d00620a40c0d032440500002e2100070300790466000c5411000c00d1201003003d2405030703400260031100501c0c1419061600d82c01101c00070b04000c10250038902e49001e500000c0d40301d98140042030305c002101c15481220b40c81164801c40b88400c2c1c0f90001d000b03040b00c10b84103038441c2c1e9100700b000344d000c0d00e81810031648424981055000701c005030711001c0c0c0b82800170030140d060401401e40d27081c280c8941c280303039070003074104500c804140501c3d050000602d58592382e060100001010900402c01280000c0e051406170210304840a90142c2d040800d02c121608001905030310a940200140008864640d910406400c0281000d0391003500c480050f04a1b503404c0c042000040320310800000c1040c50024090190b802c108050b80400080c40001c00c101c1200c0b6100c1648280d1062035158155203040e8000010009082030007400c0401100119650750940d0143c4d043e41c100d601242d481c14030113440c9103083c01c803d0240030006800841c810104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 7982426 1250 7981176 7981189
    0x309020f0d0506132f01020d0f050a0e030118060207060507020a02031002091906050a09060302040605090103020304052103190b061213080c030a03050903070803071d03010203010b040312080411 85
    0x1340c810791040000012412114540325400c1c05000f1196058541c03d00321980c040006408011003810a030f04400c0144d100503140d23014680b0900c007400680c404404180d40c0c20b50180300c0e10541c05508405402c101d09150000390085c21040303501510307280c040340e0618000500962000d50003401060b07480541501e01c4080d4100c41401604007039146808003000c0ca07040c0500300030700141d554454450b52001e4005110500961000e4185407042200f40161a400000c9840e0a2000e0a001d641c0340ca0310b00e0a9850800e04900c049a03022414107a1103040e9440001140034250000070b0001c0c03254601c920004070303010602501e40c0a00300700308461150740301409080c0d00c401c02c00340d460030501603500c03031b83c00319800032225500c15000014201e60403600f5214803504452280010340c14084107a588040c50310000d8950805d2180f100701c074250500250000b0799000801500943d160350750703100410103a40050104407440a8984c4070454070038810301161313100350f03040075141884d5410324084c8640b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 7983676 1250 7982426 7982461
    0x6070507051203070309020301050a0501050603130503040807120b0109060b03011401050903150106030e0601051e030313090203010302010305070e030706081b0301030506060a0f0305060a0b0a150309020f0d0506 92
    0x74075001c0d805101c629605440e010714413400391600c0100300d048082c03040500b110002082d0340e0301c407458403006000c261681c2048d65400495078060803270f407a0080c01c1251a41c0100e40c4028400d1144000c04250209040031b4074080c20f01c03482c1c0b100603690300c0b03082e0341e01a2020b50048418007403051004020490304c180c841000d48070181082444c000401c0c000c24240120080d92403401903654004010721917040c4501d294180d402000307800503504000020301400030785d011864803141300d002d000a032079030180115501844100721b40500d41d50b5030091358000c0c1d082448141c0c0803a1400000602c20b0f801580400700580d402005040c00c54102242655902405400072031800740070030038140c00c40721500c01035010b58000d40040270585003c07070401c543c00c0e00c1500314048120100f502000080c1c00001c2003500100c100c2404030302030b2450008110410307590341c0400380b5005031074044541e00d6019408a08281d0007a0f442d80001c60010702402100d00103142d005210f45c0c01760000511070040c0002000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 7984926 1250 7983676 7983683
    0x41a09040e0102031f1202010e12011103040b01030501050a09050a0308040525030203010605060f0406032301031a09010b0303070201032a050c010b0a0303090509040507090507090303020f0303060306070507 90
    0x500c20040c044070a0880e0802caa0304964850004100003c1d84010b202e1400245a682055004140c507540020400b01d0703020640c0740600d40804a90a07181d000707401c0395810b01e0184092541fa0320b8903090003c041c100030310040c0ea03d540790001281e071428150003001181030300078004207110780195030120303030a00000700165454001e80180120600003040c1d0700003107081c48040c1100041c2940109800c4803003a51056100d84002c0050701440d07540042910225000c500700000c15031005184c0002c14941075040c01ca40c404040c0c0040700308034998440b80340c1c284080d0490b696560321108194200d4a0818101d58960f009002c2c140040d8481d4002da00c411500315500185111322200d0f800480f084010000c2c04100007060401d5401001d01c50a5400d500880309014601c0c0b450300c024001040d94001e15000c1d075108400501030080801c5683c0062620740b01c20000ca00c0d01410041000840f80012801409104030f458040c00380001074a000d120002d0241a2689825500340e07010b602010084 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 7986176 1250 7984926 7984931
    0x4030908010e0a0b0604090309050603090c100f021504021e01030b0301020408010e0d05030c0708030a140901061a030103050c01031d060106020304060905060309100c03090b010308040e010803041a0904 88
    0x850200d20a00580414003500401000d642001e03241041185800509841c042c6103400b5000010a601050001c01c0350b0003580c2c0c80707507a42c454201c0300b4140711000e80d003250000d80c11506918425408140115154500e500b551245250082003081003c41138a000c4d500002488484591074040085804034003014140051030302800c0c008039080e42c12079407010742c50780d55030380302051600d10501000d25594214500586507103030426a1011500500750084e00c86c820220020b03100e180c0b6540804a17002c822810065036280003440b05020301001d00882460f9407050705007040c5448201c00368ac0c162503114026003080d100d94070044000b442c419112210950701c3d000d03002841941404164003030002940550384e00d030f003003604c007406050302a0300c1240180030030805c112403140045224881038100c120041038019050400318068145c02c200074220800c03400c000020440007d0042c42101c80b02c03002c0120aa85e514650fa440b801207100e1503401d210781503864480c0d0540d8100a040040004000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 7987426 1250 7986176 7986179
    0x90109080a05030705060c0403030912020103092a05030c0906090403050403020613060f050708180105090a06030501030204050a0207020901060509040204090c020c21030913060905040b0718050904020603040309 92
    0x105441e21111440035a00d07a040003640b581801001c0c04507551012044001d6464145540d0307004205111340e204e40c140f0204955008400c40e84217030001d101540e009204200c8400c11100000d4a8194445c5510345030741201d0f10016244c10007042c070008416004001c0c2c5103d070303152003c0c00100d400061045081040420010005070344080280c0300030140074542c001ea160a000e170117450310b074400c82a4400d112082c0807400005498004441281d00800300d01160400303404010b80e414050100c41c5640003890107400310b25070380d0550055048a008803410700c502d444415502d0120b2094040103900103509500600000c2c0c0140018000410050401450999101030f0401295240c9150383c005801941203403009181c44034031103140580800c0070b03100144821711016906c0c407590f20401c2c000c1400d0108081745034060f40c070400c01080303550000e100500d45480c00d00e10703005007103440d900400e1000e2289004449005442c01c1a80d80c00b4040300040c0d2266000c03c60180c10060013242080360030b110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 7988676 1250 7987426 7987439
    0x905010b0d0b01060e01050403080a050a020c03070801020c0c041104170a0803070801080d1701060c0204090f0c1a120a0207080c0a0507090c030b060702060903070b070308010e01090203160302090109 87
    0x2501c9102501401c2c1c120901d50403c04010940b01c072911480381000400d02050011400740811504e0340c5046007001075585080100c140d0500802c00d850036418017501c40d001400c010103400500c003550018094038614101e010401080720101400e1441e612010310060040d44295100c821840b040501112030084890ba203071000d03640119081000110742c0d1004102d2513108102070b00ca00c00241c2001500c2c0450034940704562481481303101c0400200242c1a0255111a40281071444c1c021540c2903035046541042c020003030440c810a8030b80050084100c040e44100020341b03460049241c110012a21400101d1019400041c41580c08070003c201194800f581003000e00300c079034864409410743d149040d60450032200c8650f00d080c01d240c21f14441c01000d940b40b004941000394100c0c0d05c903440302d0749d01011030300c0c050960b00100c80020b40051840141a00701407481d0480702c0711980b8110341e0f07072a08401c000340d00050320010325801c1121100a09607010342c000d40b0f07200302e040c0760040710503580d502c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 7989926 1250 7988676 7988689
    0x31c0e160b1306032901050412110f060a02060402090414030c010b0102010c0302040501200109240f0902010507020d1e06021c09050303180c150909010801060b0702040905010b 77
    0x1032044260150002e05070340503051840c000c0c0001c1001d81400c000d00c08080c080c20035103000c00c0d03c4889440341c06034114100340e0b0040d070658018220090781d10021407800c0c40c00c003000c03503180350f5410301c1a60222140f11003860302c001180c20101d240d070701a0081d5101ca0b401e07c0510358016000b1503202041144080301d0001c1000034003070010900002180300c03160f4400190841d900e10303200c0e0003090f00410040c0042c0e6000b0310038000d000c4030111044128038000203868010280d0783e500501c01051804d0740c08409181500d41100c1411f030110410001110841081c210f0743c003501c0c0240480e200f0b2048001511b801140b8400c09406009076481843d07407152288010759004500310741c2e540e40402c00d00240c1e00700c554964a6141105020450000c40341c5480c0c2c0d036030000400581101b140f48071400080c6506004582d210301c4050885044d00341506554401340c1c01160241c1e0003601003a00008003000d050040740100c4208940003443c194164080c0000340c0445401540c2540d00c1c1d84103580d0744c0e01c514 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 7991176 1250 7989926 7989929
    0x1703060301060510050a090506030105030c0105070809031507020705010503070f0c050c1314011202010903021504050a1413050f071803050706090e070207050603180a1a0901060602031c0e16 83
    0xa45d1800da0f2959004000742c00d2040d00d411490191209000600c03181d100082e4060250009082041d107841640c54030780c216100d100105909401020503850390044610201d80c05501079809442900307032190011141400210b03444000101441280019140a075201e104401d0180c2c0c15203402640c10404110703004012103c0040c010758030380c0b00c440000c044469590140480c40078a42c490130568000a01d01c0c5d46600019104110010881c0309100350310048800030940501074001007640ca8945e0054105500882ca01610000411018520682c03150b184103d240300d4034003540340c4900504580d01c0c290990011b0120b8000c84000c4082101085030300c00400d2660780750103840b0f0408051900200016002106560080c0703428051666a941a42d0344810b6804502000c070581d20b21962401d03000c1c20000c4c08442c1420b00c8a415084469810b42c41a81104024401c899940f00c040342d584c400c01440d02c20014204045094482664100304540a02042168888000e4400b11204e14526 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 7992426 1250 7991176 7991209
    0x4050f1501090e0c03030d1107060608011413030f0f020709050a0603060c0203030115030b0609120c0102070501020f06160207050310060302030d031806090303020f130e0105090417030603010605 85
    0x4040100076050b141d0041054901c91039010b0700c0030001420121780d4a00a540c8121045030315040700d00440351112083d100141c0d082401400059512000705008015140014542443d610000340c25050301102814440354160707102101c0e403007441000c50b59110700201349011400b072264002002e51860041d0b5001c6c440c46500026071519500d4602c080b540402c0121096410500041244a4450541c24410344080c10302060410003000011107a2242c0045250311038030000220019017400601d21130b241c0020b03002c59020548910043ea40d610300a0b808100f241c0c0200e0015010b9100d200c1d00705400301d0f041c011508140d488800003410003180341100380f0403070b44c0c4420400640c6000c0003c0284601903003410040624580f000d422465840c0340043d1070161a006441d00f0503110354101e07800c085155a84946a8152a0050226440c640310f03071202690180000305251a0100c4014040c550100b0f183da40352502140d000026007005000d1541550f07030380000181516000b0720510440d94 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 7993676 1250 7992426 7992463
    0x6010806250e03030403060603110a08011b030f02090a0303021501060302030106050301060f0c0203100212181911090106050d0f0507020c060d060f1401020f0303160804050f 76
    0x14400480e240c4440141404074a520103010000440a046541002826280341101e1200c403030002007407941c8501e510003402c1520707000001080c05140c1c1e2002d4148041101c141d00c605580d01d50143c02e03500100340140ca503d001021040d0014042e0b4046035070741a005d0009400c200a8400107648081d41c0d503c142c0c00360300203400e000d061000d503a811601410180c14218203650500d40300a05c40d00050040109100090106032010380c01340300707580c00341c0382d00504640300a040200c80d040650041040c1014200d01c1d0b001280282140c84040000950518010b0120189032140c05001c411000002c1c4c68417014840c4141003900c8030200c01c1d003c0e0466845481e40e804108510a084030300c0e603a004d420b42c034540020b100c0910384c04110f5000c0c811085813015242c0c202e040600340100360035402011901d80140f000620b02c00c2d4100d43d444c00c00026000c2c0c44040000484d003641328881102c2c1c10628050b281e507072074140b81c0110b540b95001401041190707142c2d04003050f00c030319060389011442007000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 7994926 1250 7993676 7993679
    0x3060b03010e070f080403140c15010f090609060302060f1e0f03040b010e0702120f0d02030a06050901080d0c080307030603080c0a050105060a0305030f0a020316030507060b04090b07030b060d020406020601 90
    0x70b1304003980c1d0303e41403058901640d0502d0b00d502c0040115030640e4568a480f00b0001340003442c0d14017040944030a092811801c40c072943c2d5120518030180d107600c610b440441c02c242c40055444d0042c071030001141e030080c0990b8900480c107161655183e00000724010b507141000c1c41901c1014020019024002152000d55070741c0c200b6040c084c2c2e10410581c011748440604104018486601040c1c0c40340c5141468030389a103690340071785c46031410b0048044c41c440c141d101004203c20f02e20700e50045012104144c070359030072a980300c00b45a0f88034000307008ed20011170140c4180d2800901550f00a640c0305107a482e001401c1c0e902c071398950003158010333941203000360300c031008100901c034080c0308040d007220f07080300c00e801c4080c5569145030301d03402694240c07010140c021550b070441500a104549141040615101d400101d52501034541c1c1c200c13400c16109607140140070900c44c28988100c04100b900b002b031140e00c556070ba820841c0504200c00c1043d421540c14803d80500d0300c0c160000c1c3c1302510103a000780c480f03503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 7996176 1250 7994926 7994941
    0x1009080613031b11010804060609141b03010605030c070c09020409090204060b16020d05070b0a05030403020c0a0f09090303090803090c040b090c04030f0f02060706020d0b01110d0c0303060b03010e 86
    0x110210b801c40f4144500d1070700c40000284038640d0416109601b0300b010b510f10b98950030035100502c680d038410010641040011002d0003200240c03980716441c00c4c100b4405480c44e186800100b804240101408204c0c101f010800f945d10a0010345541d074490f07102005519281c2e0702d5101030f0b806c03603480300214545411181003107291501601c005000c41000e40c5041c1903804610031004002c40c0d0340030303000d5550416400305001041c403004001d041046a07041e0384507486100102640d2003207406500500503405c1401982c5428004001100d490301c5070040c646080c09419401440ca02404505142c0d07140400320000d2882c3c405140b0540c01c0703101800c9a58144000d000c240e98540c2e54141c030030052007041240c4454a00c0581d016641c101400c050805054a09401520700000020794810004101d031001c20400350000c012201000c0f009110540c909001950510b000304c240000940004880c40710b81d5210303103006510580285400f043e0750342d5500100e00b031a40203030021006032100d10b00300841c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 7997426 1250 7996176 7996187
    0xc0f06030c1b0201050a0309050a170306010906020111040303030509030c0607030209100206040206031305070801020c0a11011704030807030209040609060603050106090b0909070c14150601020d020705100908061303 94
    0x90140c503001040d0b4015282e000070194032034040410149a80c444406040c0700c4200300501d0381c41e511807015030740c0060025011460750402c581d820300191003850081a441d1060003160f0884003146104c604046c04c40c1e4094001d000010650403031131205101808140d6800c00115001e51015200141e4074070310784003032200c0191600c240300e05551003581488010b0321050300b00e80c3d204402c003da140c250006841c22506162095000e01c17403d6002144002c1000c00201d80e118034540310781c8800b11841503800054031000c1c00300c2a5440c03142511000100802c0c0074065456210a00f89401803811141100040490310190401910541c2c2c0e800c040c00b03215018801c4030701501e400d003044a5140c1c5000407690080c403400c1f1040d0300802c04140411011030150160103141030384680502c5446070052040343d614283d002c1c10440e07032118240071445c59400450140050a11603001d001c03014208000d01c000003c1403240a42040010000000c03000420310400e40221070b10703a5020aa0866400e00408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 7998676 1250 7997426 7997447
    0x8010509030408030301120c0803040306050109050f040308060d020f060f070c171b010e0a09050702060105010e030c090606070f120e030115060e04060503010e0307140114010b03040c0f06030c 84
    0x39941e000700028400c07000b0000540741140d1020507240d981e0001c0e45080f420b20300890344508803d20002c43c0200c10090150000780c181c8242c4e403002c2043d66502146011a0101a02c018020034401c4c1c0c0401e403541403d2461030728041c000307494034928100010100b5a168004030503c000701201140c40010000c1c540741200043c000180140904801d0040303c42c0c072030f10b24104614a009003180c0350001c0d64010141d0f5041c80c800100008022581d804200300640001c503841c400501a403000030445601983c55407401040107401052040342c0300c01802492540a858154010410300045c03000a4110b0500071007244160040c0001541080c7c020306501b83e600100780c0b00e40d062a40d52008444545020821201e040c60b020710703800c4004c0085402004190081034240d4200280030300030620000007040c403039100d4603c40c50300c0d11f900c0c0e0005088850105400c034418900800420400341110007448e04980103800c0036030000c0c0c3e900d40c1c0c001e507001946c0c4400042038aa2020f40900c0f034200c0b07095078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 7999926 1250 7998676 7998691
    0x50304080f150103021f1101090303060501020d08010e06100c12020d02060c0307050706110705070e060a0b071104110f0d20030f24040207060225050304060c030c02030a0c080105 78
    0x24419411580092899200e1407880c03500004180c00841100d4480c40d1032500341d01170b410003006042701c2400d0040142c0924041c0a003d4840c40c102c00075054401c80740e03d4100c0b4014914070a6685a00041040c003a42040340c0504205d40101c080021641038460014a065160010f00c00302c090b07102c0c0a1b0514070010300c81c2696200500030010300540240443da5641c0d407102000807055a07489481c03180d0b001d0003034040c02507c1200004205038094503a914040e400480f4a40d0b1242e50b210034082075413003030b00d0000300000c008880c190100d05142c0c00c580c0e40140e28818407400c1c400c5800083d117050700085540d0310000d8a4010400fa0719001e41e1000d10080c200c003100e00d10314907000c401140c41100141c001940c41990300c904448000b1a00d4445080d0b41e40108155603e002e90304191002c0d40160060500c8440b2401c2000480c015a5000c0040d80f035004001c0c40c01c01d440e0040c15115801c00302e40079000c2c8803543c0d401c02c00507a418041d141d1014071500b020718042c1d0600400e242110401080c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 8001176 1250 7999926 7999963
    0x61009030503191e09140301020705030d0506030102040513060501030501090902010e0f03030d09030801050a09090507060e130203090102031501090807180f05010f08010f0b010801060804050109050304080f 90
    0xd0000c900c01004445608042c0c040d485185003100b54115407886400720040c01d091003524105030310680c440e507036074100c03204141800e0409240b40700305800c078820104c2c024015802088030317032507049a50700560740c440c030010001420282c0e10f80c0030403c0c10b0041454841b5182d501c40c0d05003c10742e0107100d001c0c090002c1040800c00300e503180d03001a143c14101ca0149104000a5055403483d6404204403643d0622100701401014250318000d0019007080c05400d1294030020000718020386980303e941c5000303070003000510001f840c021080c1c0740031010f88801c680011046810092100c4640011402800c503a40016070700c0c0303040b041545040c884280d64a0401c00c0100080013280381c000354460030785255000040600902d0348561000301201e0b039a1120365820603000040c80a0480b0144080301d10b180028003081e120548401c1c119400001d03103030b0100d40c424006101c03552007003030b0440c2d1061040000040d5002c40703480c0c151454125602c00001c035480b4091645004a003408071036030040c03a500c0078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 8002426 1250 8001176 8001179
    0x203071a0f0105091017030703030501080c090103080d11070f020108130203060a0b1306030b040201080108060c041401051e0301060e0604050906040504080d42061407020402040b03061009 82
    0x9018070010300c105441412a28003103801c00c80c5011a071402002116203d4058488103800745807203800101083d0003082c42c000002a25050104a11101800041101915a00710350f50740300d554200190030b915042d903e45081880c404001e00070505140101141c0c280c2c9006880010110741e001050705002d5400030803c00010b0b100003447c140c025128013000720b204841c0c0b44c0030800016100c054004085d0030060000144100701c00f2050040303000f07076a0915540c3c0c0350078900f6958402610103500491041104000b03003002e60440b0300c1d01ea85e05241c11450071708012041d4854452481e500f088283c000001001115002641c5c0207a051058442d42e04141c034042c00105010300041c8024007a60320380000908000744481251000c0c001ca0104214400d050201600c4401c9040c0c8200001040012081c48804201440d07000510302c81d9122898541030900031900c2c0302c0d208a10070101c007001e00026005030340d980060005080c0e88800300d6120b19081e802c000c569404a48250248201d0620 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 8003676 1250 8002426 8002441
    0xc0f090302010806130207060b010305060603040c0e04021324060c0503030a020d020f0c0c040b0108010509040201140d0f2a020304030f0507050402030a0c0306080705061b07080d0203071a 82
    0x14480803680c0900302101c4039665280820103650020030040c0704c00c0e00c0000c190301000240c2e0b1004c0311019080c0d80801c21603a0318030170302ca0180b1064502605544c1d8400c01000b1100d000c1c0000ba41c00351010707140d0890840e0100c111404e0303a15007818040045c3c105407402400c0c40b40a01000001d0039240f400c21641c0c030340e64444075241d00c4050412400f8030b030001052035103108281c048480410020813030b02d55410030401da05487d1408003405600ca07a00782650484950311690b10340b4103031480240f40201944841d401503c2035801a814565600b80070304c002e104030902c611560800148150001c1070b040400900340840681d01100c0e00e0301c1c685401d003802c04131540042503d007907d1b400b04940c1c405103283d08000345084030302c1c0e005d81c0c0d00900010400081c6030103500503c180b80a030752028400d441c1c8a2401b6034440c292070090341d07000b040a0211000c070000d80c04904400d4080541034956141e150001c10341000c50345401040581d100140407020400b481001818144220003455800d042840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 8004926 1250 8003676 8003687
    0xc0a020c030c100305060604080f030703081311060901020a020901080f0c06120c0c030403080403060923100209011101050906010806090601080303040204020a11010c031b0905030a02010302070c0312120c0f 90
    0xb80101015540c5c800a415a22a40e0444010303102400844001e25a68144103540e544071200440000d455400070540c1c641c24000640c90203648410388100079807514082c04103e4000c01c410030b0452243d89404800358445004841c064a002d4019100d07149460340c0d507901d403075000d00202d0700a200030084122407205000c6100e07084282000c600d90344862a400c030503d9402181c1000c1d2a2040c0010008204121540041c85c0d8910540d04200b0344040e070781c610366500c4080c2e51a15130b190042c40120300130320813039401410764240505120300c0b514071085100d800c40702d04079080e1206070f120b5401840290404c0080650140800c0c000300700d41c3d03040034040c0c1e41780d00000c0c1000b0f01072a00810b282d6a11401505110300c2480c00d5002009030301d40c9584001c02400c1e200304620740e080700203220448014801c45481e0140d44001d0300900320040250300440c02980401d00c02d442180000c107000c000140040081c0c0d50745056aa181303948a4540015101215460303152241403200c0104144009a00306 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 8006176 1250 8004926 8004949
    0x150806030c010e060f030901020a090b07170f070506090a0605060a150e04020c0607020703140f0705090402040603051b0306070306060c0201120f0e010f0c02070e010306020703170c0a020c030c 84
    0x80ca020240fa1410340049400c5009100c0c5510790544084204406808150b004c3c01c00341c909a03a446e40d0880d980c0c2d03074205031446421005040d03248076881e400001d0b5004401807441b44186401e45192141c5030701c9540c10054155518005030308041c003014240900f9004817504640c04440d00030030b02d40380280702600d82c0c91000041041c000c55100300c50056480350b0640d2900f00d0128190740342441c10240080d2640c1240c0011156001c2c480c0c2d031140342500001e60a901ea118420003020030300c0c1440b0810444120040003203034450b4a6650220008a0920500304480000020208019111004c01d0b04000c00106503100f05460220f0070800305500c0a42808425020b0910b1a108083c40b885031003c1c000b1280c1c03801c1d02d203060030503900500405500034118100c0310309e810071000b8500701e4120b8803596180709060b0890703c020010300106501e41c5c001c000392882802e150042c0b035800203241060480c12540d94450b000e01294410038190140260842c8001c02c038054036001c041c003000192400c092 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 8007426 1250 8006176 8006179
    0x103020c070909030201090c031103070806150906030a0f08030f010909030e04050618010f030203010e01020f03010b16021908100504020306070e030106120f0c06020102190c080702150301150806030c 87
    0x9820300d600515000794840b91495030048e02c108816503d03402d100c5601d190740c0c002d40b070003882120000240b4840c0840c0c0307903028100e914184514030707144104021000502412107a4140039521403500022044604044078610034290951a0b14090048400036001607200000c900e05151401e80003a910644401c0d60368811600002c3d01d4a655001c255200c1608005c691303040400000400c480c00300400360301c03c036482140203000ca8078a0220442c241d000e56100c294164134140018000c0c5010b0001400f81c21700112030304400180e0350b800092920b19200c2c000b42d040b401c540400e0010140c28850300410b5003c4800c10f001c1400c6c5940825981d0100820003020802002d40400c095682900b1000060480b51203280140401c1d04107030500402c0d10a040758492004040064a24010b0007514403d00310070350040c0c0c49903000c0c101501d08100156080360480003c001540042e0344207009035001b0100301c030b182e60703c1c1d40c105805119103d43d008603180070300c0213140030030103941c3c0c0c0000c0301c0e034081c0300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 8008676 1250 8007426 8007431
    0xf030309030c06060602030405030c0402040323160b0304020a060302070c0506090604090f0b010f02070305062409180607170105040b0406030b13050c09010503030a08070207090c020105150103020c0709 88
    0x1401c0840301c5220340751004003520305150300014015800000340065890880c1922840802c480400089100360b100042a55800c000d440300c00c4448401c0001d185841030b400d40d1519000001c0b08424545290440021218080107020550901c4040c8401410307250038110b03d459810307111424030101074800c080c8a800b001694694980380d4000b03880080c5a00f4600f400000c1144803141e001c0d2940940a6001880581220103000c0c400a100811260401c000d050715460359200c601200003102c49494010000c0408501c80d42c5554000d14814802045c400f1038440d410076015080600140810042095014810305105070541101e4119142207a000440220b100d002ca00500040c2e030010703000c10b03075000030000c0072a0800b001c404018450000c4e594a01019020400d0304d40d405e000c0c682c1c150b41706005007550079000e00415500244640100e0b000c8903502d00c20441039030414034240380141d44031014040342000c81c2e482904181400d00341503040a146803a990740d1a0340703030300c241c00300c254 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 8009926 1250 8008676 8008691
    0x60509040b01110f010906150b030106142701020601080106050604060c170301031b050a0b0d0905011b0201061406030601020a020d03030b0a030b0103120305090d0f05040905010905010509010f030f0303 88
    0x1e000748401035246002e801130b561144002460715000302413180003a0b41c3c480c1444401c405a1030030106074800d0701c8281c551b1900756400d0070412582400400c941410713802080140e403500d003190784c160703814401201c805500b044c1c08403800203040100681c484a0030760304011040c400342d82c032001564182c601c10314014a10089500303205040989010090206440002c0080180800006018000c4c00001c459120280d541c1c2c061001c851202c0c4a14210302d64180300480340305030f00740c0000ad1140c2c00381c0d00205408400016914152000712000c0300540c1d03445400300700b182d0095014820f008070441d055030540ca05800080e40f110714074100284a0150403801c482054000da01c55081050081c1001055580b24588001c0c544000c0c001544c400a98440c18090706100e4092648240304500c082c3c5083c011040007130b40d03001d00300340709a81072000501000c154003145105450003040040c0c2e000c6603551410043c840c1082043e048110b40001903072003030021500c3c0504002d032031545071600140e41c0c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 8011176 1250 8009926 8009929
    0x140a0203040f061e0e0904031103070c0e060102070806010b041e1203170906130210051608030a060608070203030f1305190606090902090406020304020103090227010906060509040b 79
    0x501c9607030010340042800c9100460328540c400e494103a6110301c010404061034400c2c0050302c60a85811100381e1101c1e0050000c2c0c0000d00c2251214a40c9030302400f207030305041042d07584082c402266008503002910f443d08120586d0790400c10302005124060140c9681e5041c00c440c40d149210300c2c016a145160460001084400c0764507208006000711107190050241c1480c000b080160944920585c030780d02180030501c80c8001080c201e0041d079802408216a8001d9424841c0300b141540a0324284071081c40031354120004000441600c6201d01a00790b035a00d000a0141c007110a036800c80c01c02c002d044400c200203250000b04880c1c001101c0078550100d0358450540c10740324140b080004029004186603501c0e00383d1400d40c00c00c1c2d12882a1000e03c4143e450b0311411080361315a1b00043e5200521601107000320700c4e243d0082d40c0150042c940031841c0c85454020400c1c100102d031494084260401d8403041c10709444512502400001c4400c0c0110b0b4605074000302103000314070384184640c0d03a840282966 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 8012426 1250 8011176 8011183
    0x206040e01080601030204050c090f1509030114090609030a050a0e0409020a0303030507080f1501030b0f04090804060f0215040b1003060510061202131505040803070c080f0105010303140a02 83
    0x10031850300c019006686410031252078040c2840128041c0f414400420011540c0d03800381c921a00300506020a5003125204106600e0b001946040c1448410003010456460031b01401c200325200600041d61820905000340c0390280081c6039580ca41c0040c4406210207910000321081807101d0b140180800300c425000030002c1040d0b1000030b5000381d880000008045c0c160308568881d1003070f0f4403803c42c0d80e0354045a00d0000741c2c0484142c94110a000c0a40782d080d03010f070744900c01d491400f405440c600100d0801041c1110024031094521b29004101049a030354001030b04505808648094005420030301e40d407900108d0040c0c1f008020701040c9000451050f040390481d4015a0043d0303044c006410050130015030b4044c1801844005000d180702c1c0340302601c0340d00031183d062405d10f0301400810b01d0b01c1c6507543c0900c00c03480c0304000c03c101080f000400802c100090140e4501a800562140f864081d41b1032400301c0c2c08040d03040342d0b4140301c0108082a0030140100701078080e00d0501c4e07512030321400200d08 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 8013676 1250 8012426 8012429
    0x80c010204050a1202090601031509110408030301080f060702011503120309020d26030f0106031d07080d0e01030506030d05030903090a0905012105030a030b0604090216060501090612020607020604 86
    0x410400c607980001c4c11300c110344c0400603803070700a40f1150203e880b100e0046041d83c099406008039901c419408114806540e4000c90030416007144070b0303062548038060b075415903100f0390150650394407003130024041c0b00d002e01c01c16070070210b14002008402040f0f801a04551040d01c4050441017130140380c04100c40c00b941011080329802040810390003442e280032120f4044600603d507003082d00001300c4c00070841100480c2e029a64140c8445100ea20b0910300320054000b6495022207001198180f1002a0702045150003415908001c2e020904502c60028403140c0800b4920b0304150418051000c10707100810340301e45071b003103070703c0c1240c2e0782d40d10703140c00074910720507007a03055040340c0896800110200d507070f4081d44c1a524240d0310340b80610701080100e1040070000c6000b6240340c0040028014480c041e52110704d582c20058646414603075160340f80b10490300444400280c071900341400000300000d5101c2e940c050f000c1c0b55001c114441c2000b6820321148140c100c028000e050003d221015035450700113880 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 8014926 1250 8013676 8013679
    0x807080606060d06030803070816031103040816050a08040810090f020d02040204050d06020c0d03090b0f04150f05070212040b1206060705070b0406021006060e100c0506010618050f0607080c01020405 87
    0x1f42ea0b41000ca10051a0500807511000542c1d00d1003552401e4910901400102c44ae00c09811400c5495603100c407150b66008164000c01c010080f40340400041d810b01c20725040c0750103600c1107038455151202160030004140e006c00101880e01e0500000036802900d9450300507015210040442418070104000788550303040240d2020368494a002045410b030024a403000800c029620741d4440c00e9400c0c0d055422a040080200c221480003c4141c040000348039801030084081d0b005c10b5a0314101d860440320f454444007141a2a1010000b00303d07010083d04184210b5140c00b5440c051401350050058005c120341c5881d44510080450016a507030303000c2c0e40e4115000801d5940d843d503201c2d2101829800b500c540005401411000c564540c0e07603200e044119170b071584607141041d6160742004817402c2e0000c0d03160140410b85d035406011403c2001150302800303c6890b82100030b542041040107030452540320502c512842554004030307482d10030554203901c0e803011030907032030b60034180071103000e4065504186d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 8016176 1250 8014926 8014943
    0x10f050d0f1505030c06040f0506030411040c080702011b0207060e0607060c02010207020a140d030305040204180606050109171b010207030b0c03040201030b120615060d060e0601090807080606060d0603 88
    0xc200082e048003010440d007048080b26024103060341840b0b414000d500c240b8041815081c400c200701d051070002190300c944120384048070403400c4800035044614098402c0005a0047d007044030039038091044510225100d00701c24461022010000e66800f01e40c050782c0108914006d00e0300080c3ca0b4181940c01c0e00c1c1c0d021205100c50344200300001d0013500610000c2c0c1c881e2407510360024086620036500e034030b400005802c00040456075241500607220143c012a000340d595400c0e0780b02c00324040e0316440428402d40c008a80341e07180070b0004109012980100320341c4150f4200190300c6400025004203003402290231080c2480c0e4000041c2d00b04249030384081c0010210740c04101d51881d4910003180308600c02d032010401c100800301440114201c0e44030300d42142d03004401082100c008d1103101c290060004019514200856a4405c00c4e0744456000c01d4401c4030142c00d00810b5030700000004080c040d06002001030520b41040c40c3d546540151000e8050040060842192101074001c000030356040100e8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 8017426 1250 8016176 8016191
    0x3010821030103080d09080d090b07080615030a0e030913051b0705031606061502060105030d020a050d0809030d06060c05010b010809030406110703050f0a0506090a02010f050d0f 78
    0x4951661080c25040010042121916661200d5003060700d0580c1e80020600b8105190650401d00a2003440350a41c0c00d41c00c1070012400020309400741e003003854480c0810104a0034500400707010140060103080c411010329a141822031000d50941e94064142c0380b010404641d000002421441740d010302d141c02000c01d0803941100d09036508954013a207807905a4940181c9105c0864050b0700903880020107a4004000450a060341241340d5007990380507000008989a8600c98842043c00c200a80809600a02e004000c11303c0c040c080821040c2083c0094041d0701c13050741c1d4507501c408007180810305000240d008281c01450810984450008004003000303015210070000d04071042c098404c039125801c2040f0140c240d441491564061440701c0f00460400b41010b40a50303242c42e101e007800c142841414bc00001240c010002000400b0611000d000600c507541001c0d4108a00104900415400f610b84c07e00140d0f407001250355028803a1421540b521082c08030300d405814514040825541000031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 8018676 1250 8017426 8017439
    0xc0818090f10050a050d0303021309020a0c02030c12070b07030c02040501031a07090303230909010b0405011101020405010806060c0c030a050c040e01060e01090c1206030c03020f0301090209180c03030301 89
    0x1086000d002c4103106010565520410000b952089000e1039401041d0360315000b0029000c2d03000303802e0041d1b401440a111945807480a02242c0180c014200010028414031043d03003028400080d01c1d0005540c0c3c036025455103034021b552000300d486000304080c0b001481e042414883c3c5070303048040d54022301c00d0140d565682800700000505e044a440300c8000400450b031414001c1d04040e0881c2e81c1920b0701200402e803244809104d00c11030840c2c0030a4441000040030f555521141c0034003a15001c03004a0b111402e04c400100f6810700b001e80440d550388104414806680c0081c1182d030700820840705255208101504c007401d0001000e922a018403450020760201b01000c0740d88800070304162010007030b00003d028940d003030710454803602410703100a00052010b0b40050300520380c448080e00b080c10701c0082c140a55811288a548142e500082d102c600703000318130380b0740c410b0300144170220001d00959150b50002030400001801000c4140c0200384c0c4448a40d10078462400c8100c00201a81e0b101d41e541d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 8019926 1250 8018676 8018701
    0x1030b0a110310060315030215030114060a020c040c030e060f010e10050d0816080f07020f04020703050d050613060e0603010e010905060a09080904050109020d05070f0c081809 77
    0x140c4084040d82041c03a0302149440001c1500e03c250365041c0b500b09400d180113026002080105261400340802d0310011003da11003001c081e45800070845416a60740c50300641b80204d01d02c0c001468030a182c20040000055400140d045400400310740000f011045080c00381d00412000200600c0c0d8001c14040260541e103006609048400340d14440e02955100c0c14803a0000003036000702075000741c0116104000c241000040c095501e04440c3c4801d81101540341c117440d94101c5d48020044450001c3c0200440c200100300d0b0310903100a44040d4103000040d600a0224014660f060b003010b40e5a030005415641d5420241d914070703400e80c404014081d1205042c002e0b200084032841e00940c2000060a010081403003102211f80e041400b4020369111060003102070005020243d48003401030100c0110ba03a103c0c4642e03402017140b040c0c010f030744a03a080d40002c1030313031001440c40050010401504080e16004960040c100358011005607803070414020800e0302810000401e50492040d1007003040c41000e09 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 8021176 1250 8019926 8019931
    0x904140a0606080108070b07050309060301030506090f010203040b0c2109010903031503020102030304020d06150605071209150c02030f03030a020702030f0f0a020103021b100f1a0a03080a020304030b01030b 90
    0x1004240111902c2e03440c00c1d915a40300303108400b800d0740640c2041001c001120094044503101d0f000b40c0e0700d01900c1d240014035541003a001654650001424002c003000b0412401d040d90314140025403d61401d0748034070f0007104000303192110491001812003440c50344017146a035100d1044026028600304a0051802419491422000b00b0b00e0318984100c0c0a075414070b028203c99050707000310318ad550785038284800c801500a080300d189032116030b0b11103400c000c80c02c0f81010380010342d0f445440c0c140381e08005405041c91744458050041464080c059140340d000d40b03014030425404c1a0b50b6844a62010901d421480c821074041030102005004c407840040e0001c2400c3c5000b2011074540c80040da118070345506030884030286940c00560342d0130065000e500030345040e182494126418001005459003403420443c04210083d65500e11000e00c01c496200320851a0301c050b00145e90040c0f09004130b50803c081d4040507043e6000802c0e52042c0398820400c1303801950f8401c040c216a56540c0c0741550241405 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 8022426 1250 8021176 8021191
    0x60c02030c01110a0e030f0304030f080d0c03020a1b02030604020108060303040306050a060609050a0e010e0c070203060901050a0501090603020105041802040b04060f0207060e221d0c03010b030304030302100b06090414 95
    0x7404005c8003a250001c1e26420614110001d1454503265035078460a01e20f200c002210405000d01070b0180202403442111480c048584016980d00700308440200b040c400c0303118000034800318001c20005600c0021715154440d40c2070074403030a02c1e03c54000186c9140115840180464142410000c00344181e070092400c0300d40d41e495100d8855115410055040c1c03150003000342c140940703001004600143d200064000b500058190300e40391040d00420304245086500c8405a034580302404240d140c50702ca0a8014044544208184d5040d680000c3c4140b0a0344074007100d01000c40c0c84401e1041003681140c004115440c55290f44030365410024001005811500c17015015a603000204d841c060a18004c0d0108010a1101302d40c650040c00c6c094114500351881c0c0c1155035044004001104254250410a40340000c02c0030300c0481c410942507074a00d65500b07000790000d1000700002900001c44035410300171a80040f80300da140f90040780c128000d00c0c503101d600500340881b04409007800c4c01242d00a050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 8023676 1250 8022426 8022437
    0xc0509060423010201050c0d0504020a030f0f0b0f060307030809032506020706020303070e1002010608100e0c03030403021809150c040e06030703030912020f0a03060213081603060c02030c01110a 85
    0x114000103901b211012030300d420500d00708009526194031240d1000d40e00500c000e014001050310b84d01c0b41c030f08401c506c40d42226005156a1014140f24001002d15800030394506141140d01d4a0000310761144440d00c001000584003040075661a0b03800d02c2012010060349940c0200c40d54542c1082c418909584101009405859000714045201000301c0c0d00c81d4169447c0c0c0c0340b100303500c1000e1082d101c100e050f0300c0c01155030310980071690540c1440311140070103544030003041d41000304e20100e041c21912030b800c0c1e200b81e10402041005846150301000700c810b40d103150800c40c2d80c03400600ba00300350314180010782c1100c40c01d04002807414140054825100c4104080c045a45c40405240c0e4034030542c000034010880c50081000110000c0c1140344c81d1601c09004404010460710200d45020100d4200300d41d401d03000b16003050030383c40321030450005011000007031680d50090302d0a44410442808060040d58440286140c198020800c403a44248440002c00c10307220340408c0031605400c0b00426100090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 8024926 1250 8023676 8023739
    0xe090702060f0103020607020103091202010509070905090c0603090a060603050a0308061c0803070504080604050a060e06010f05190b0310060e060703051803010605061c0606080c0306040c05090604 86
    0x61000429501ca10b900520218076a404c54003001803507001440101e04041e00c441c28100000c003003d90f4195400090b4001080d03505010441c0d80c20290306030003807000540b80c03800b0000241c40000e070b002214101660340680c0c03600c40e00440380c00c3c61f032071401c00303010076003131000001c10070400007600e680e154000e558940f04da8580500300604081d010130400321155521001d00042142500119000210742c1003891601c1e50b42c3d00e0103800d00314103c07030955032608510aa2018041c0c82d0103400200920880034282943c140040002c400c0b0360303030240ca405003405401c01c0d4920b036040701d0b000000d030071500b60940d101d04d4a5050124284094028440007607880115100f040c1482c0301505d13006941034503600e0910110b2016803079201e1120161035410364039030f40005108d0316002c00600301d80c69541e10074a00e1019841450b42a40c03c1d0390f020200704001d200400c003800da46a000d41e41c01c0b00084902080401c03803803030100c030507025180f43d46502c0175000400080e07049501d55040c6121416100c000b0911 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 8026176 1250 8024926 8024941
    0x403090e01060804020405060102031e071403190c05012705100b0607060203060406030f0503031006020a03050403060207020a0509100504050604050708040b090a0b0f060103150803040b18030d0e09 86
    0x500280b05090102d40d28101050044c503150300314650107001032045034240501240104191000004899140f010000d003000902005c024014040044c0b14010f62078040040010750040450380440410441c8a824010401800390400d90a0a86607840341e0b01030780c01d0041141c440e25013a0382c01c5a20380709030a040703011005c15014501d00054020542030034051070341c5803540a58030050649a00c50780e500d102000040040f141074045602941c01141c881c40c10031038909503444240c101405640c000740300c07400040ea200d0212800e60340e1245015032604601d102049010920f900110791041d014010850526071300540304045035004c440034411900c5880510080325420b541c0702c0c00041c1032800090101d40c40c44007043d00034802c481250442d184c2d03515a2190701c4000c0d184018125100c4007480007569040c01030017008003100c6c1d030304201180740040f40340e600e2040d4425510391810100b4010301c81041034122500480010b002e94520f040650f400030000919074001c54400c0901c0d8000c41c040c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 8027426 1250 8026176 8026199
    0x6111c0302032215150b04030f0b010609050916031811030c06030f01030204020a020703060c0e0901080c0109090507020c0d060b0301060b070b01090f020c030c010b090c0f0f0702010504120b040309 86
    0x2110341140c1014181045204e5401c050b0207414020707150303408103100024007216480003c000450050364140344d100c820313150072881c142043c0c1c0b003041006109482440281d036011000c0360424110030700c0b514425455081038025011070184125200200071700101408001d030451120b1000813070075203101c81c0c0e1440401c1800d01066803800004100000107000608241e801800005030b80d00441c1c8283c0d5807030755400c0a45050525010020303c2040e204162410301648407405014407030f010740420701210000a00d034500c01d104185156031140d010580b442e000340300c200841080980f4103c01c420315070500c40081e04002e42d4843c00303980b1700f030000141d10507890262400c0f654000c000120702d928080c000c030083c044907110016201e90822003000030740810001010700010000012402c00b450404100140e44003c00180b11820200112440018540121040c0001c0510010346807062070004032590f000300c0d00a4090820390b840001c5c00e0040001d1140d216921aa4401c1421502c90f40104403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 8028676 1250 8027426 8027491
    0x30106060219020f150a03020903010f06080a020d030e03030406021605060702060a11070e0f0402010f08090309190e01030b0a0b0307050105030103033606020c0301050105090106111c030203 83
    0x150101c540b05680040c9814201d13105403010040c241d4840e0740e41d214488082d0781c03245d5a6030f030100750700050420300d5050a025204c0800320501040142c0c6d844c01959a4461190803802485154010180e60805005004000c041880501140e403540c3e00c605019682c1c0c1c034500954042c0b02c58542d800205482c010044412459014240504004424a06030350b0a9a414101c2d086801071085c0440c3c074000b04000c2c6031152aa841b9045520f05040c00054083e0a07460200002c100c1d50b20100801404000200c0e500c5c41002d494108107018061903050200f04244c00c0242a030f0b543c2341c000420300a401c0d040c2405001198820001c2c1010541059a120105e12480d03021440500c010804039006426a191401d5030b000417907a603403650142980034a90411f48009594490107050240e00d5041040f1079946805800070056541000e00041010700c0520034001006042e8180991001c1c081c040c000c001c402c0102040856014008050040e400441cbc01460182d0889070501e0b0081c0d1781c0ca100da1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 8029926 1250 8028676 8028703
    0x90e0c0d11100504080a0303090b0a060b16050703050111030402011404060206040b190e010e010f0209090a0b03100c0f1e080604150506070506060901050a15030903090504050709050301060602 84
    0x5050480010910049011101100051003c28400090070003002e0006602182c0301c0c1d600040d5101182ca02034551b020302620b00600c10780381580c1400720303060100850b5902c18002110f040d02803024a01617290011a41000b09994200344102d2000e4009202a60003a40700740c8031182c4025800a40c00e01c41d001718410340b0016072148011401095940e590590840701c00c1d08440c2107a110f9103c10320a076902110900c1c0383d03039555032865150900a03c80c0e060300b0305820b40c3c2589080c4800001074070b080009803200031181c1c0c0d038030803041e041d94040048043c0c09a80d5201844a091110070140600208030b800c0004140e1440d80f40740d03c4502154101c5000c203807900c80308060f885c0da03000d005c01001c924902445c092170404003c0703020b030f0303c00d4040c080d030502c10300040c00d940c90035809004640d507045c0d004500034000e07100309101400400c400b041d021031641c0f41c0040e2078046404c0c05c540400da281d1001d07400c5442c080506c021580d03c01b1007031041d00c0b0258001d000081d690403089903191100700030034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 8031176 1250 8029926 8029943
    0xc0f080d140319060b07200105090a0311010513030c0f15020604060c1107031407050f01050d0908120a02070302010c08090c1311040602032502090403050702040e030301090e0c0d 78
    0x1450151500541150342d0b1a030034000032a031343c545c40070b100700f903002c0c1070140c9681101841c061486c04020301c0126440c07a00380f804500380864803020890000e41800000d0404c41000000c3c045640f19030141c9100c0d4004280300a402d0361b60381003408202c2d00b140a11804a000003402146200c1c40610300c048586281e0700030310580d6619110b80004101c4064007108000d885800e1500b011420003210340510b00940038060340700c548052103852314110340e2181d0701030301007115180050ba0308102540c1e0002c0f45403802007800b003403a00c0c000c10a80700d40102c0308031390800401030051050f000c0c0d019101c5284603400800c40302e000d80c3d50039284d00f101103600310500c0d8000141e4040346d0429070701c513030f0743c004202c2c0c004184400c81119a810301e400507040040181c0c008607612220000c00440b83c0c45000c41d0703c00c0740c030700f00100da004101244c400810160502000160714000c40d1102d522140407800700d24182c036100d58540c0a030317002030007200d02022110312480900c0c4583e4940303040000411030b40300303100303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 8032426 1250 8031176 8031181
    0x1b010b0405100e060111010c050c06090d09031e0f060912030501050a090b01050705030408011b0c08090105030403021006080d030e010b0d020103050403111902010807030506030c040b030102070c0f080d1403 90
    0x559504000134500b0b41000f08843d20307002001000d000c0d44560f0105074036030a445d8028031803840d107031400c018900c1609500188008001c143c00c0b0b414901565080007a8403030500c03d4444941846000c0130000303104c46000b42d42035003407084983c004040d0034402c011903400d081b1003c030124160b400c00c1c051035034000b00c80e480800560310301da441000c1060041c10035500b4920191101411500f1a0b4044e50059440326094804d0035862203400c072070101c00b810500e00414051303d500b010b600a03000345170b06000000000c142414001c0000d440c00c590840014003201d40c0300e00e10345482c1c040c1481410301007810164801d8a254040c0914422608050410307a24140c081e0011000f40c48082c2c41a4144005074007140d031450b205104510701e00700c100500441601d01403000412112005140c84109840e002c1840030300d5402041c050046102114049071400941c8002402842070810050100007a10000a00d00e20104030401c1103403031110554107090920082074404100c45896002070b01c404200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 8033676 1250 8032426 8032439
    0x709050f010e0906010e040e010207111503040204051005120c0a061106130f020d03020303011401170f090102040b0a0c02040e0703020a1a0d060e060f040b0d020108041104021b010b040510 82
    0x504d6100c14140f42144a60100c4004682140c002c0f41401c8442d940003d945000d001c201a01004015400d9801d180100e03d21581c641c507074003000c0c000038451070700c42001c42c0300c0745405c81c14000a400000c2110044005840e411035032802c1c0c0c0c07041d050284140b0b5000285c041e0051022040541d1540d014240c59607500d040702042110301e000c01c8900700c010400c0c90016894060301c901c0c07030600c6900159941c1d41090b80c40000010f481e4481810814050468041c0e03488445006030020035040c01c910450320b903100c0d01d5019010716008180001c502040d048041d0360b002d81c842100900036903003000a010480415034451400f4000030350020754042007002158020104034024180442d1000e0408003484640804e0b03035080c0e400080100c400c002405020325004442601030b440072202080b0780000000845d207107000080e4040d040c0f0606500203803e000b8031011016240b44006c2045503138103014070380e004c1403201c5030320310310b4949d0304e040c16125060519209550050303601c00d900101181c900031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 8034926 1250 8033676 8033689
    0x203030106021b0402040902040b0403060b06030c0414030a06150509060a03050316060b040507200d080a0c0507050610080607050a08040602070206090306041113060315090c0e040305030709050f010e 87
    0x610f8250815400c000c0010904620710180020b00100c404082d40c461850400c1d00c2a10070f61403c46120710b204109110198002e0310407142140c541844030300030305c05060002806c00042d503001034050b5007008842c4100c0780a040c002000c0e1081140e103c4416110034040c0041c04545000040c0720b6802082070707603441c220307000b550010940720701c90201e42c2c3c1203980046020740382c05550410200720f03010038a0480219000301c218920300d580005191101740413500620102c0040c101d0039916681e1045c11581c40e00c580b046a10f035907000b00445000b4189920001c0b81c2400e41c0c0b284010b5801400d001c070f03400521480c101c0d86071610039a1981602e8a458881c20025442244101c2c3e100400700083e04480e01e0601586101d18004c00e004481040300c40c0601154044074220b020505140c1401032000507444090b0300c50407250140001024022403400b03101844954000f0100c5618480804c010581d10000941c464052a6140b000183c0e4031000c1c84030310307031440c0143c50128007155900c60050a02c01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 8036176 1250 8034926 8034973
    0xa090b030c150708120a050a14040201030c030605060c070e090601030c03030e0d140d1d0105160c050603090307030f1d04050403120e07050406080303040818040b060c01050f07020303010602 83
    0x40c21901e18003003d560b2000090740c400c10307a071003c4007280b80400041c5141c910596512490301c1c903050007040b1b26260700341c40940005000034141548c506074007100920aa0101e0080d0802a00c10355403502940c0c000740d524509482058141c000c102d0018001041c0402c119048981c808240c0041c81e05694041d40c1e2024828140341e045111039260001040b032501c40d0090488040c40504080124440000c080c00d001c80c4d030151091400c011846e01990380701c030881c0c000410288980700350740e0703040c9041d01c0000c20135030000d40d1041d4040188402c61002000410310b0710f01c00e440d0f421500c2e242110039202c2001c050581c03902c030701490b0900e4115040940105901a119140000d6403a4603411010221907038805440b0140e80030b20070500079030401c1c0c486d1101800301390700150305610302590346520f1445005880b2070805003494a848003501c0329082491401c07402000c00341c4912010760214004c0c03100b200c02155445503038001c914264001b00071a4141c074201d502400340c00c030f800b03104494005040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 8037426 1250 8036176 8036209
    0x501050f220b0f0904030f0e01020313120213020307020607030f0c050403020d0c0302030d05040f0803040807060507080d0c080406050a1a040b0a05100302030106020f03040f06080a140a0203060a090b030c 89
    0x150f400e0f52500380d03640354046214521a403a070b07125800461100800100f90703a00c12506642c02040482000e02c280c014078011100004003c09509450744007040011030514030070001213001005005525402107041482813216a400700900310f000c070080b4040d1003802c546400481c00c02c000501c02742c20525151240c250081c2003c1203041c2d42d90340443d15100385010b80500203400400d0601042d1100c0c20b00800a08032080118107050034003d025456401c0c505c07407401440400200b00d400c1040170300583c1c200444410042040c0b04c0c0c1004054580001110200c6030700b490034000944201c02c5100e140c80301c403541c0140301c02c03580c00c00d01440000c203103400440f40c1c0001300103000600b903a10010183c00041c001d0350090b031254501800070703180c000513110080180c0c00034081408001013a1014108984003031070302c0720240d102d8140540040c43c61141114000007148100304081334160021030080e403054550080c0d03d40d0b1101c5800c01c44903000441940b64100d410444071610700a80c044407942c64 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 8038676 1250 8037426 8037439
    0x1140a110601090209040f050108060c0c07080105100f120c031104060308161a0c030712110c0f06090102090a18020912060f01050108040308040b07020118060501050f220b 75
    0x85030245549491802d078004610a40c00091044c0320741410b02680d1010400c0310f109001e15418148000d445010040028203444d4012925000928081245c072006202400080085043c00181501040b40a024103401100500000140390008505940000360411110000300b42160358000000311a489031b6540280c9903240070011802e2000140f00e000d0900b5141244e1681629012803a2880d211947c410954000c04000d807440e40030044036884075140c0381c0000a12500400d010043c40703203080441800030086100000701000140c41002d00d51840c0480d55695981d56505081c0e10903010495080711036940c08100020441c1d607040c03101d0741299800350801590328086540c0144804450590761302c00c1d414443c16203102000740d80544400e00e08003d1360700d0300340c03006030803c0c00150000f0048010180001d81c400e10030f501400c45480320003401c881600003070500402400d828050b451040740130403841070051501020801e01100c3e220000c000e144019030291000300650b403c490f0b0000c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 8039926 1250 8038676 8038697
    0x506040204080d090e01080d020303010306050604020d0e03030907140609040b031002120a05130807020d0c0b0f0c060108010603050a020d080d09061e0507120903050705030f030612070501140a 84
    0x100c007840341c0d0381c001d50309640b004c88651402d145803a031500181c0c00040e41e40c101001c2444150340c04800c590550385c0004002c503503910b4004c04540244a2080c400b50018a8600c02409911020000354060301e4124200c403011a2156903100615241c0384072940e20100c2085480450f00302904000300c0381c0c0300102036035622138110300c001c81030303034800624080603030807a008000089846200e06608104010841f542d40111039035420840e00c5282d50182c403814445640400b04040d148104028120030030109850f411000d00000054001e0070410368079002d00c0001041901052180000b01c0e600600103048080154080c4011250059010384641b80100a42040c0310500c0c0222085135119400c00251201c03101c602106086040344000302d50381c280001c0c4101d80d07903c900745895425403040009041e2582c0e10742a100ca102e0725500401500001ca801842e1012003400b03584250410340e00c2c000b4566503c1e900395190704650082501203807885041c0c204003410030025000703031040740c20000c6e5500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 8041176 1250 8039926 8039939
    0x60f13020d0207030f02030406050a050c1c0503060a050d05070501050c030c030f090103050109050403080408030601020c0d0807020301050702030403030804030806060d09061b050405061806120f01080c060406020d030506040204 99
    0x80c0e0003600da8a28060b0001940010075a0001c90000c1000280c4055406c00341841c00041c014402c08002c01c007049004500c0ba600321005000c0b0022010741d010000d01c08040c44100641142c0044400f24460f150700d990025990a02e640301000d070a9012010340b450600307040040d9295001809010b4507440203101154440030108004c0942c04501d03240e4a4581c1c50070301c00141540c8058200419203800e00051100103a089850382d5006540a584d02d40c603070343d400c7c004070310340341d01c000005034428105119981404030f0303d4020b00589000382d0003030003d940c4000c81a80c0da4896440014006018900020042440742003003a400c0480200f82e01d18118042d0400819200002025900d2035900c41d07100701070b03424075145001003c505042c0319081c10310b821b00080c0c1c20f0140d0300380c400040d0111036124806513034a100325482031400081c14609410310800101c6c3d0f00c40f0034000c1c5d01040c4a8260381400c5494000142d80c12141958020905880d0300b6400b1001b0300405051603801c55000e00010820 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 8042426 1250 8041176 8041181
    0x2010b030f030702090a0b0607120e0d060204030c061704060902030a080408010c1e0504050904080d050906070906020303040b06010c0c05060406030b01120608030304031b020a170f15060f13 83
    0x40c0081c9a0003541c82d0a15401040040b0708046e04480b8001d2401036001c01c540c4601068510440c1c00c52500500c400a400f02603810784401d0704810350001c1d07042c0c054800c10499602410540e805882410603054864009864138051f0300300c5002d2048a040009000a1081d004203d100b840642130b030700990031590720388481e50080e0b0001c21403651075141017038001d82d004a000c100640494080e002039641c40c8406049880b50b8010b00303000ba0f668500103010b01c00c1a44c2220080710358484100490b2070005407031511440203a41c0c1e000014004040020501d200200340c0e4001c60300541d4405140c2c4420b00107464400394548102c81c5020500400202980c6840151000303004035100880d452211400040800b403040034103802c260f1521505000b0500001b00f03803540035926091124040343c0714521400c2c0d02c452140000c2d070003004c545020404c00300520a000e0425900300448440404034075480385c584c0c0036182c540051030345040c00150640792054140b4210000a00035008220000d03100d02c1c103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 8043676 1250 8042426 8042443
    0x50a08070f02130b0108060123030901020408101103060405041a0405071406030906180708070906061409150a1101090f030e0105030c04090203040c050603040501050411030a0506061002010b03 84
    0x10120034800340c07401541880002c80702000c2c45000c08101130b001040010701481006000181004404141300c04101e403013034a0781c400c0b60090302d4000d0701c0340f44c100a840d004c0c8d8040d000300702c414098001c0c901c2d4800203600400301c003c141194028190f03035034201400010000284203483d0542c01c8164211000d074041c3d442c40c06540134202a150b03450610b0b071003a08082c000710b0300391b00814081081000f15100030500a411a8103666001e401134035030a10245010380907006131000d40105500001c100842c0c0d40844100d41141e12085071481044126081a000f20340700d40781c00045d051950f00c884400240105503002003400c203190540d02003400d0f00d0031201e02c20740c03c466080c480d407201d80030f00d030300009004c060000c246402d52440c54240c0c004503d07401141b0030202c0e46900400842c0400404024074070180101601c495124a010f0130581d01800080e00c055903404851000c401d6203060200d690a003058000008000a40b501014042e0300c06081001d442103541e80c010401c1503a43c103100d00107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 8044926 1250 8043676 8043683
    0x1207030515010507050a11010207030206160302010501061103070303150f0b0714030a020712050a06090503030a050105030d0c0209180304030c03030305060102030301030f02010e0a030c0b0409150e04020d050a0807 93
    0xe00d494104484681c1c0300c503031112503040c80400d0082000003000000c40e00341c0641c0c810322892106400ca0010b0b4600019500004d40c080d03000304130811036080605201c10140e02a60091000e640d0302c0c2c5098039054044400384200350000c1105401090180c0c0210441100f000000c10645d5961244141e4400c0b1640010b07200c0d840c0010000f003806030049082c003001411a0107140b030492801000f075070710001ca1040640d98a612800f07032041c42700a101090707510750041c000b031107800507038a403140d02c0703a0080741c00c8420145070500104450800003078a400d42411030322402c0e1000303003c4d001c0210551005065125024119800c02e811800a00180000314841c4555024540c00d610700038041d00c400a15150442d170041c0010004284c003901700717640c92602800c0c400a458000c42c00310307000088940018040700650200080c244061000a0040340e00c5441e00700f043e5403802042c0d02a0000300e10503c00c08281d000c000c1005403400040c1c101120384500100c0312031aa1954580d800358004007400d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 8046176 1250 8044926 8044931
    0x90213090c03020d14010501170901060305060f0108010c020a03050d020f04050409080703090e0f010302010e030109050601060f020705030703120e0d060e0705010311130e0702030702030a080901090b0309030f07030302120703 98
    0x985215082c029402084a02d0081c0e003290344c141000200110040d12079a172542d0b10927800b180c2c80d01002e41c0110b0245802c00152600c0c3c1c5131000b4900c5211500f8410020700b0340c40e000b03d90800f0ba00c0401e2110066500d0342c0c0d01c52a04500100c003002035040710b44c449030801c0e01040001100e6450740f203111000c5206a04a503220740c60307404c0c0640307410101d82c00380c689822400104211200c008142d07074150f03542424920003502042d00800d00420008500404501c00c04001280785500f0074a90f00340f44400d035088542c055150700a1648501c003910000384440042d03000140c050340124500c140600f800351821494101903150b20041e500b0080c0c00c00301c0c3d038218010038001c1d03503410700407440b0200c0c1d241e030017500d04807980b850078140741450701c03c190600c1e2802000c150001d10a108a43d40550001c085800e40d5149083c01c0202d5842694a01c0c00301310100800117a018a5405072071081450307801840c1441d80806803140b60354042042181050786c01c1294008282e03480740301d0b81c024595990300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 8047426 1250 8046176 8046187
    0x30f011a010813020103021c0203240f010801030210140a03020c06011205060a0b04060f0605030a0b04050403020a08030c07080309010209040e010e0d051b070b0d0c0810090213090c0302 81
    0x240140c444450006041150a104112105280281c1801c0c0d10b9420300c1c0050b603480094000c002c1c1c500c5142460880680000180030740c0c2320f40d40501d0504030b50301c0d0301d0110300c800300740d07003002400c22210762843c0c0460b00c01d100400261909102d20142074800d410058016052001f0301c001ea54000c410310f0300825404100005899810084240500306007941c2021440203034441aa850074014000c0b40056156003128550780c5968002e80c005001c03010400c6102600d500e4054182e4008880d030000080c646599901c0b54a014046e4500980d01500a0b0880301e06503125000030f91720042141c5030a55041100ea0001090310006500c100211000103032109900d200704410b41d4000a0030f80f0302e6030304020000d500c1c030a01007481c3c4100321142c03c250b82c4d1081c0d5400d42d0b070b0b9007004018001c00c160043c1c071000101604490300030b0203001c1179a84100550713418140f0a50700c441d4103442401d10355112880500c00000d459006040c102c8000d08580c2201d5650007042c0b094441407041c6100082c0c000c0348 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 8048676 1250 8047426 8047451
    0x4060806010207050117070e100c03020622020d0f0b0103030c021f050910030b030601080105010501141806090f030703050f070b030f1501050409020f0403151415030c030f01 76
    0x520680025003407024000740c91034500000c000803818102c2c08180514200411111790180b0070901d070500000d0700031600c41e900c402015082c000300702c40940142c0615000114480c0a060302c6000492026180341c003084c4442e000e1002030304802d4400c0313602e51468100030000c124280c2085000718420381c2d462100004910500180b40c1400d19440b0020080201118826400209698000c2310540303583e040042184800c4001e0700640707001d5500f5001c1e180c000b050244041d0011412f990007a200d44601e240d04050b0b990261050285250489203091024032652800b20001d00d07003e80002e2940e00000540c4000074104401c1d584119255840400064500d48080c0001d00081ca43c00b0401d034254904031920400c0b40c100100b46400c2c00100c5d001c402e8883c2e009a06603405008030100c1152200c1c46400c00300c80710740c01400240c460b81c2c00035900d5000d080e4035009000d152800d40003840c0c0283c45500030040042101072200fa407500500b010007c480d1401c2160741700000b10795001040400d440d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 8049926 1250 8048676 8048687
    0x70201110c01020601050405060d0c030b0a06082e02071e0512040302011b050109051c17040203030901031109100c060606080609040b0a060e090d080f010f03060b1203030702030406 79
    0x400089940c0200d10750712180da8011400c0c07070458034290b0700810301380d807a0000034035030449080c0d000b04400c2e8090004030030301c45c1d0700c91450b01c101003407102002520384410f011940d4590700b00410706102e08001080720084240e107024807541036008805402c006095030b031080c0c6203803241000c42c0220380078401f00081c4402000382c45402002003000310300d003030300f1a0002040da601041c0a01000e05000301540c003002400d51001817165000015141c41c0c1c4804901040491105101800019003880e6100f020240702880540525030080003140341c41e2004006401604c0f9146480300c0c000c4040c024901079844068465828450301d503105104461145001d4040301d2481c0c01403030811424a0801055840b01041e00e0f0b04944c00440c02041c995480c40c44601400003900a684881800400c0c030800c2c00c00080d2400c541441c940301c40c0030070b60310040340d1486041d00340318210208071212002c0000c44c40d680d01c00b680524000e00405402c02076004002d1a5038400c0d2071800041c1d000050403c0301aa000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 8051176 1250 8049926 8049947
    0x1204020310020c0a0b04080706090b0702060703020406090e0915010605220506030403050c0f150601110d09090c090e01060503010e0c0a08060402030a0e0d02030a03180519020d0602040b070201 84
    0xa081181007480e90742c0015613421540720000c1c01400300c200421300780034105050301c0102d60303c031500b84013a550070700d00008901d0060380c1030b001502c102c07004a0352090103070081c0c0e0143c0341c1668503a10260b103803a8034001455405048101a80078003030700742e40c4c10300c0d040f51700c01d020b03086503101c05544000100d1040d01c4400790340c45141d807403404002d00303000b01d1b03450800300c039085505850103544400c01d0440e031500307140d92402002e806100e01c884801c0c418100a041603c6184262100d0400b1092011600d4403552070079444400502c4001c02440700d240d05138011110361402d440e01010b0140c45440181c22120281c00010100b400400100104e104110705140e00110b0700014506000003030002810304100a0101d0303100d03e40220004419030302ea40c2c031610418024504450b1000200c0d0740182d140d40c020341240b0300207403c056204090300805806101c00700e50000c01091400c1d07545895030b03903030955210100d0f841145001030501107540f60004d440a4405800d02c266100c14500c009020244003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 8052426 1250 8051176 8051203
    0x417010908040b030402120106030c0302040506060309070303110f07080c030c010203130302060d0e060f0702010c020a1a070212040303030608071508041104180305120c03010f1e03060212040203 85
    0x10610361000085440c01035034111410100c3c0141c40761a42d1000903000d442480407800b003986894070001c2403101610700d1108480c001c2e60f0811541e10760500b480313014841221505850360042208000181c030540401d50011000380c1030b1004c0040e5a5017076810031400343d2101c0610f9105065a49a62400348841002e41e003090000710300c0c26400951942d064103407440003912031800841c40011030465a000040d10420b03000c00e0b1074251404109070940103009449080040d803038a03821811082c0006450190701c1c0c1c0010001e203000c42c401c541e4140202006020b034086009803a813100c10300d00c1c800042c101440c0301f501c001c19054200000c4600e4400c0b00e43c012040c03182003140e02e40c8011b4000c150950001d41004000082c14642c00124001e0240d0040031085520f40300c5505045c1039000018100300e6810301c003422160b0700e4150645c0c4080c0020b02440031a082c5005080028402c0c480030b000d01d904440c030380c07074800f1507513512030300c040382c100d52590368404940307000b00f008601d8188140049503c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 8053676 1250 8052426 8052431
    0x3031d0312010b0304030210020705010213050303040f050402090a0302030601060507051204050f010c03020f030406050403020406080105040b0601080406090206041203030c020609030f070510180c06030902090721050a02041701 99
    0x141e5074103101d070859062254100b8600004041002e00d403003480304428000c00c110080d540d038182d41c6420b40c006d50160121841d140741d207410200e0700340b4010049404843c800040e20b511035060904000c000d6000d540b4803540304180d4000040161000c4c04114020321945c3c0750103031100c415080c42e6042034820300b00111071520402007840305a07141e8000790301005084c07a2105c0c6400c0146404d0745045032000403d2118440030a000603250b50060080040e0b0740f080d034092041e580e88a07406800c5e6841540d00600c217011070000100654824202e4a82c024041c040c04500d0107031070340114101e41d0094028036400d0450720503a90905416010b0301240000390305c0142141d14002c070159440b8041c90b081001075803000200c1a062000800403540d00c5101ba290070058050604003d010b000724030002200c00740500400020428081d22030324030110f4010f4050604c0d42d98140040760090012100e65103b0001402210034584041c400e103817180140800045e669800d1100611818903041001c0300140e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 8054926 1250 8053676 8053687
    0x120304180605010c0b06121f0e010501080a0b060613060203030f090606010c03030e0111040803040e090d080a0b04140703050711070501091701110706060905100e070f050d0903031d03 80
    0x9900500344c90703840350091980c41640d00e900001486e13080c0c9440400c4c42c18865441e1800050b421004060913801940c0400c1142030384aa20482c00d8400c240700e1500c640e04130410366408100c1c1d442c0282e0340071900034200c81ca0005803040148a6800a400081c0107a2002c0104000c0c89003203400c664100042c0c200400f00c5150a0000801c2c2e42e94440d401400c00da140c2000c603405440942000100c20090031880c0d4030b858030744440d5544d84d00b09105070b40000300c02c40e0114400c540d000c181081c580c003203076440224564841d50080d002c3c007880442d0980059030384000c05001000281c0040c02078480c2d80e4041424280054000c001740b0b0b1010141e0b41d036811952040000340c2e001210b580840b80500320b924203c04840d6480d03030040800100c0c188240310b0000d109004c014980d8048000c0d1401c0c420200000d44488221861036117a41c0545240307882d1140c0070a05040c01100d42001007606032804600d40654504020141c404c00ca90840c08a501c480b202d500d030003c1000394403d4070b01742b41c00460611 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 8056176 1250 8054926 8054929
    0x506040501030807060c020c1008040203061509010b0a0c02090106031401080303012105010e06070807020d03051902030402030a0204180201020c040506060a0c15020a0f020c0109030b0105041a120304180605 90
    0x1d104008004183c11b40d5000c00702c640c03070300034407020301c003003600900c02c0c529861500b0303000c3c0c0b6000c01110120320078003802e00000c40d038101901c00c101c2c45810150511040e60700700507824101d5800560300409002c10000c10800507501c522000b8060140381d0740206201c101a00345c03103c0fa110607004203030f00b41c000740b0040c083c0d640001c140400030282c060404440303220600b0034a0040c80e4500b28801c0ba40503c0c0c0800503403a802030760700b03409515980d00b150000025100110704a540640c0d102210455004041909148540107190003500090031703901118015070001d011644442c0c0c03200c06c041d4240c581300c0290768050020085421040d01d092100f880c02c41c0000d412846100f04040c1404034410941e010b00042d05014681154040c80c115a51200300700003501410196907101c0052003103802c5000607511500010040341e51044a0445030390030001000060315000d8101030707810050384a25004c680d03c00010b420603007041c5001e140d5a074200f551444100c204070b00307644030207818041c00b00316a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 8057426 1250 8056176 8056193
    0x612051006050f0409110604080114070c0305030f040311010911010f0509060304061104031b03020a060203070b010b030c070611030103060606090803030c07080d02030406060f0503070806010b090102030702060301060302030109050604050103 105
    0xf10440f40041c0b03110340c0340f400040c2c1c0c00c028032a8507005800820042400c000560028148200030f40c400c6500d0343d070b400000c4a00008601c0000c00144061004c40c691018024041c1d4200f482070400c051030385504a11a400c54524880995212004500c12001540c01400920f0600400d1800a10f0301e01580040f070070758030002d400104280d540720420340418860302e003500d000c1c0d948010030140740b4244108850f240c0084e40001d0f841084a0100010060300010842e01201e51000c01300c00d45a04e4000005950b400060803004904000c0082400085440c031074058044611518140c8030b5066050003c00c4496640114090000403079050010820010907031798001d50955126a0300d40c02840e042285000ea20071350214a40084103010400030070390040e1050b42c185580800e4207503590410190b903884075201d407099a8100c1d0005116011032407000b06600700d41801280e2900c80c1c1a0f0114620364426031102002950200041c004000940600341e0009000c0b102800154195202e130001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 8058676 1250 8057426 8057449
    0x5120d0816020a020901030602040f0504050402011d01030b030a030207031104092109050406140310051005040b030c060c030a110a030807050912060711060906010303090501080403030906061205100605 88
    0x48500d01040070072881d6200300706038010503a01034010035403560b50707290110184d00a4000c042040aa00d10040b81c0d606280c82410700c1a03130141d48802280501c4031400742032400c07030b4956a04060300c0d581800128bc5080107000b1015109038010010a841c50804011100915036818070a40c28400c3c404085481600c1c403428444181c182a405421190000d4400c0309140e8007050700181030010002c0d40b14880041c1c0304c0150000d50985040514024050b021201e0499440c800f2151084050101c0c0c28a5031020941c0c500103011100c4032442d1900151043e0003072180344101d80d00009100580540c00b0340d100d403042ca0000001c150308812a0b401820003807004045d034040003004241080a0398500c444155141c888005694450070034890050400007000420456441703107802280d00741c88002202c604a03a05039480c0f0b800d45c0d042034011100c1d03140c0a032040d400c26440e00b1300a40880c00d00d00c943c400a00d8600c0c3c0b121101e0344103240c0380e81400c1c03001001e1010145440350811403912040f520a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 8059926 1250 8058676 8058691
    0x7090302011d0a090204140f0916020c040914071703030106030b1c030504050301060501110a0305030402060c0f07030b010602010e1209010201060830040609050103020d0209100905120d08 82
    0x31020a060449401c01940c1c01010360703c000c0b07110000594000c2e60b4000c00c01d603011a5038420079000004207115241c1c4030120415000318180c400111580652495001002040e1042e107030031500e100300007020ba8070f00040c280d41d405810800c44040341c9007040341e5801098080d03429007007030001b400c0c825102d02051050704107264071062511213170340d2206103800c0d4414007820407100d943c03074a04000344282c2190050500035841c05901040b01d6000d228062216503114004140264075503800300d0340c50300040c00483e0005018051400c4810050015640302c81d2000002e0070070300e00e58240322660030011b03880031055900d84840c980c1c0711003002c194100b115600b0b004c0aa0ba030221b01004031700400391a8001e074885d00800b61044000c03100c01d801724400800c0851458817441589298a040340300c2e42c460f800218004000c1046694025000303007002003100d500040c240000003001c42d0507880020300c030900042c01c080f000c0c0510f29002403d1940c000f0b401004100741c0910780c90103406500301a01c0301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 8061176 1250 8059926 8059937
    0x41121100504020d0b0702150a0209030316030203041805070201060b030405060628080105091605010206040b060a0b03010e09150702071206020f0a020303090705010302090d03180f080d170709030201 87
    0xd0b05540322000b5040301c841c0d128020801515040314001d48030122071b558035a42c1e1014401080c09030003d03000780e131840a001005540b0345121303510144040949500d044003540000d01001030035064895070304a005120034000300740c030f2405900007421220b4a82000550641c14402d21010031000202240d02c044180c4070603035041d99400810580540c2c1296050781d01c08030340c801207000d01c41034014a000322046021502210986c5205d440152214016580107a10680000340415140e0b460680c0003c8040c003402c01d119110800740078075a0090b0400740980c8103060034088000750030800b42c2440c0c03d0750210489142480c4000030348410140c0303c0c41d000f030030a412812080c00559070460350400041224240c1e242c0f4180b0380691a5081200c03e907120740110000060154064000c0b03a2040800400070410394203d40e40585442c03100012000001b4250340340459040c1c0c1070840240504903d2000b0000b00182c1c190043c001d0800340c0c2000c81d0100007005003e140b1b40c02c80403c00c2680d9090070030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 8062426 1250 8061176 8061181
    0x702040911040507030212090d020a0305030c0c01061d0a060302060a0c02010201022101030c09020f03011a070501090302010203150604030c050402071b0609030209071701030201030f06080102030411211005 90
    0xc0c0e80e094201c1680358080d28142c148422184c0503801050980c0c40e051100314143e558000c040e490341c60440c0d0410150f0000844680068403a0004590003035900c41d0030b034207102044080070b084407103540044000c40c848110208240b0030044a4940c4945800b006204183c111303400b0074040e010358418282801001000b00d01168001c1d010b50707960500c186d0f003020440e54070141c940c034480710038031064410356180e504c04500100b5078000c96054503402c0c40d29074511392800e02002d90010480c01141040201030101c000007074802c0c0a0507081a000c1d500160300c0341400c614450404a0000c14284580c0342000b0820004044880b198100c075021180140c88010034240b0700748030052450340100f08202d0100208041e40c014103c0820380e802552003004540d10070f6019500e0ba06040e5420b1402c07190303500108010740c0700760020803220f440002c1c0030500c56034404101d400e981080e1004c07140484070400c901c20300d0074042c1d03201d4040b14505859881c201d039400074054035079001d080204601340c0c44000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 8063676 1250 8062426 8062433
    0x40f0b0a11030411010e03030f09100903080a03050a05060a050307140d05030309030307020105070c020d021201110a02030405030f06060907030207050a0c03030f02010c03150e04140102040315060803030c07020409 93
    0x1000560507540c20180d03560346400e14008040c01015982c5501040e001c0c941802d2a080020603560030b0f91000381c0c500d1802c00709a00704101e5040ca42c040d0f00402c110620302100003200320001e42020900da03140481c140c2404c0c205c5409950009100303038040d159840b010042a500040d88200b160b0481c91081208103a41d400b141042500a00150007071000106000000d44000000c510030b03030203640200090380781c561040b40c004880d41d00c007a44c0001e5403020034015242003507107008012001400018088820711443c00c480d0051581d031009a0400300c0d040000d800d040c0014005c94440001500036850a000010004400604540304145d40854a4400c100041044103481900300300002002640c070300d001071142c2211103c0b40c0055081510209a183c041c1c0200000b0081191840507540d080c02000c0d40461001007066a01d412000205800120203100400c080c500995100c02e50841000104007078584171740c8010340740d0307000b0800c01c1001200941540d210542c1218086500305090a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 8064926 1250 8063676 8063681
    0x10f030e011107050a0b01060905060304060209010c06050901091a07081605090d06060914070503070e0307030b07110f0c06040b0a051c0e010b0103050402060a050310030b0f100e040f0b0a 82
    0xb400c1000b00000010b460041c03040000350744404070710541d40c88803a40e0b00c90400701c80a174490700c10782e60441c405001040c00070b071480d006004203801c1850031055440d003c0c1c80e6030050351429901d00400d650b40744211b50511110f06016804c19224010900043c20103010080c03000c0c0d4014008501414060402da40312403081c0d04907115110000c20001165150b803c104004052611a200031640f42c101c0503400b8010031107116209200a4540c0c0c0d040d9616000143c404001100204c1d13810f00031483c02200040c1d02c0b91505004481e07940c3c40092410f004900303d4600304c005020713526950b00c03045018030155144070071070381500e0080d100c0607200e00391150151707080e0080031b84030003118451600c1c51010886079400a841d07d00d181009101061400c001502110400c0c2d030013a4002000708141d082280c0142d00454024200340c0c0000b4030319035251242000b0007401d60725070206031b945d0303401d102c108030411640d00301401d140040c0c9039281c102aa2111309030481d10900402545a10001441c201c0f250b6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 8066176 1250 8064926 8064941
    0x1302070b0411011101050406060f06020c010906140f0d0b01030b0105070c050d0204020d0c02010509070f060504030f0203190303020903060601080108030904091b0f030212070e0f130204020c06040308090c010f030e01 94
    0x5138000c0c40941064500303200a041e4600600d10503043c1d02c80000780141c03000072032202c50708041e11000307041802d00c1812181d030160440320728030318281003060a0042c07030070000034481401d5015000030705c0c52151000400781c170a0b40c4030340760400000f032028501003141b01c1d22000451300200c0e018101d010180c8041000781c02864541550b803807800010702012a0103402580c4955100f00a5a0b2540c0d2070b6907012402e40c1d91801503400144082c801400011038490080030094001411980180740d4040302800010b14100304900180d0003203071000007404c0400000740c0081d030900f00000355604150685959000e01c0040d10711036600c1c5c411034400d0041d01a100782044c24031600c0030440580318859410411942d10040b801440303041c610b20305654020800d03001341d4440790440300340b9403101c00300c04000d0356010700340b0310361820308018940040e07881c1e100910180c1c0701032010300807501d0700d4200a002d0700c0b8002c01c008030355000b805081d11183c0e4019681340a40c211400c0010703040112030201401406003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 8067426 1250 8066176 8066207
    0x30c030f09030c0201120204080d030203040203070b04030c0e01050d0807020d030c170417070608011a0f0d050402100e03032a060a02040305100227040b0a090501051302070b041101 79
    0x1032000301000d243d440640b400d4828000c0e01d81c8120a8103a00c088412480f45101c1d03c01c80ba00b009082500040c03107a0019900240018115005262103507203001b00c3e0b502030752003111000013819042024a54403803017a401041c084844039640c0413143c460f80058451307020020f1055585504200406018040c1d0119080e040482103410b91501e040075030060340715004000000c0d00c0d20040c3c0d2003900c0b00040076000d595682e55480324592030075141c0f04000403480f881020300d40080c82038042402e07004018125200c410200811603050600510076a040207000910402001e0340000c03d141c1c07000811280807075103c0170750f0f1561509114444551050700c120790b0b0312902800f03080c400c9030314054004d0402d490040c01030301c00803528075120314128401c44041599480c2d0707041d56026103d240506101364504041d00114458000380001001841c03a90420070751165202c00501c41428006040607108103108000c500c2c080d500e444003451482c0c010710051207a9038250690580e40d1155901c034116040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 8068676 1250 8067426 8067431
    0x803011406070b181605031b0d060c020102030411010c03140c010207150905070e040c06180503160e1003020120010908030702010203041101050301060518060c07080709060603021207030c030f 84
    0x84c182208224100781592004152041d064042007201050307079060200c0f00d00078004e10825120300c0412501c0981c8012059001010216003070101c2d07014021786001d224a6400181d1741d107000e241c001d101c03c007c000c845040200a02940002175080f18159404606640d0500c1d00d54001501d8035019100e000b60040c002d900c00020040301c0803690300070840c0310317200e98180c0e0703605074841501c0900c140045401810941440b4420040700d401a0413041800c82c400c55000b804548503008249080b07211001003070100031458040201802c0321000c1c07500300e00c8012170042403c3c91500002d0083c000f02c0da0310320010046040d00c1e105440c007540244d03600b03980050f0b946d4880c906071001900035001110151001c0c88000c0041e8019845034040700d040c2c419545620b4203180c01e482714030102c080001299a00107408001580b1050307800c000e00c200400b4a4030080515505089096044c0d424652000090500501c142a01040c034010440da0000042c5000100f50302c903820210058a20424408007052 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 8069926 1250 8068676 8068681
    0x30c1005060a080120030402010c02100c0302060a1802060d0b0301140405070e06011202090301140a0c030f090c1203020c0604030602040303082401030e0f100203070206070c0803011406070b 83
    0x1500003612440044a0322510b039543d88080601780c13003034414450300007010450807060500c00103004d950000d0042c94564461529540031540c5410525410000301c0d040901810400d40d04010b026030102c00f81a040c031403024500c1c1d1741e0408400f1014024840c2c1000310302070000c0d1310917070b10198002030014000d05c41001b181666040b0110150303019182c038003640c180400c0d8420104529805164103039104a9094044078550009402104040e40d241d501c40591700000200329121074092061410002120007e140c0c000d000c65240201c03607901c0070f00300441c0030049410f802c08041214a1498035002c4028945001c0303081c400090501e580c01900880c010061280c598003038000d9030b10a455520705500c400d907000303c241520001c44004100346aa40b50150b5209030411802030307202c44221071052aa0401c19410600e141c0c5101d0580b0307502104201d0320940c10800943c20201034140081c1d010395079110550184814050491384502c082070901765030320b540c0c00300d4203282d80042c005800d90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 8071176 1250 8069926 8069953
    0xb0106050306030706080103031209050c0a0b1305010201050609040201030c0512100302010305060103090c03080a09051f02011107030203030103030e01050405041406090105180a050a0209060c0703170309030d0e030c 94
    0xd070400e40d0414000d100310840428100d00408081d41680d4058648005101c400d83c1e82d10060803ca15044540c0d010ba900c800501d901c0e500c0d41c0c0d0010741407000a00b0349900b08000b0103600312415500113411a8144010721909445086c4042e0b009034080c41d0118018210390303800e5071244202c2c444241c9480a040820060f001d0761031095085e207100342c1e014000b6407210401103007a140800009840545190403c10010b44214003c015000075410104400340d40c54000622800d021b4081075034210710103c104040642c21b126940088a041c10498200369040e14000e640303000500004081c030044c40c4140080340e002c0d40581c0c00909004106000710b00c203403007a402e030013001680c046000f491144008152880c02c080c401044221514030400c0903507408600c103018000241900c202950300f00100c07030054035010000d11000455200a203103692846c58001440340b54100c02c4650f41c075050052100c10309010040300c0c00301e120041c0114502420104050030741c41542c220f4000f82c4588001071140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 8072426 1250 8071176 8071187
    0x302070e04030903031e0e0d05010b061201050a08010204080307030302030717071716020d030213120804080d0f0914030f0105010801290105090d030e0402030c030402031606140906070b0106 83
    0x19a4480e83d5074600c00c80c4200c40710f191b40300c50b0300b0317241c1c02090600c00c500d5601d040c0007102602c254056000410783d50003020100d2103503485135490b9010101c81000600042c101501c3d542c0080441d800210315141c80d00c4d401c29103e0080000080816800201041c0d40c141b00b541c03004024080c400d48200541401600070f085036912603a240c00d282c103800002101c080300c50303000a100a18603005441d0400c0740000c22070003540a007603a00c01d407140c040303c0890810041d500448003144100790456860741005089847e040400070140100000c401c1a60400c59010f03080000704c902010300007160f81601000681414be6100b940e4429603c2c08000003500e9405400c608180ca040340600b000d0040414041c07003400d88088011030120f80d0030400824181000c0070782401e030f50300901d403a6060780310860004050b0381c02580c400501407804000d000c00d6240611140c011000818000310b9803600d40400504507031183d03e0400152031000c181d0704503a4031540200e48140d0703480084c0c80c49543c2c681c40003520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 8073676 1250 8072426 8072429
    0x60306060c073303110a050a09080a060903080a090c0902070204020702030d0513050d0203150603030c0a03020a061409060712090b1303080606030f06060a050702060a080103060b0301090b0f040302070e040309 91
    0x301103911a00f4149040d00034400e502c0d4045994000700d00d03050301a9005d1722154440d081680c2004982440041c0148003070003441c0c1018400c0c0b0700031600c076580d400c00510f0400082c0c130b244030481ca045400310005101c424000d085a400060144e190b9802c1c2c000100240118180a9090702801000c3c0c074183c5c1c0d0040060a04040601c0b1001c440d68540c82400044004000000d400d640031200d9240c0e40f400702500c007a44000700034126440c0c000d180340380c941080c00e030701403c0340964844c600c218200082c44c0100300c0507407215000c1301a20718013a1102d66481038003030000c030140a0030f014610b001c4942508030603c6180c002c10307801110f0906241766850325400c1c000642c00181c4600c04180b103494107004690089a070045c001889468290030014190301c4a07101d0130901038200220401603c03514080c10941099444020003580b540c10224103881d10311900c648039901d060580c00c00140000d01c015004480301c0c260780442d0307071030f440c0681c036051468004148600f080c81c104010180d2245d01e02c030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 8074926 1250 8073676 8073749
    0x30d11010e0d02060c030a0e030f04080c01050f0a180b04080304030b09010912030c090e01140406060e010f0302180604080303071416020f0a09050a09020109050609060306060c07 78
    0x34451080545034403a07080000b8100142c2150011031130b00c524020103540c00604501e070004000c5841007029140d82d20158620320303880300103d410400b032002030080b41040142800e14901d4680300c4800d0380011711030405071400784039a503141b040c2075401240000020b01100040a07540315100d446159498000d48021142c01881100007108254180900341000394413a0402003130f81c07540d1100741c000c1c20700c2004413010054903110000301902c000101c54000c1290300302050115140743c0500040d078003070760001c0d800d2103a1a0700014943e42d204880a030041c0389490016111548030880020724101c2c4040160b11680120300814000c00110003035000c2c945e107880d103040c03804c96413594071494001c003107610405160f100b60a0b000350410102030040c1c007000600ea0034030f180d04c1e1004081140c0054614081860741c4915001c2156048071840018000c221801814030b81b03080c1c0019082d20004049500a01000c242040080800c2040c2e00240c0848a0f45d290751980c0c80044078425401c01100340e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 8076176 1250 8074926 8074931
    0x30801052e0c020411131512050a06030210090608010b0c030403020604090606020d0e0d02011b050d0306080c010206010b030a0b0a2c0114030607030213080f0309010305010b0c19020a0302030d1101 86
    0x5440305c3c1008004c0740e084180d0015100c01d6140780001c1500f1144c01e0801d1082845040c444031940405248207940c4035030154040010b01d6421030042c8106621801da0402c107014210750140b00341c40d0080c1d402c504454421840c17582d24190716448604600403940000e40003480410007241403501038000e80700350307000c035402c41c1c00034429501c0844040c699a032120390000340b4110304c4000355205115402c4c4a02c0c440c101c51840c401c15564061401000240c0d03040045d079070b1142400407181c140061012610244010012035041c22010ba01a04c406428a9182075490791100364640742e0101c140c00400500300814880171002c61085030682d042c0c80700c1a102c1034840c0c00820b0107a0011f0302c5e00d501040240090000c2d41c0d60080035002580442694160740c216908002103040d002c0024409450519010f1a207841d592400942691070607040b20401210910000300c039198001101d19000c1c2604010382401070140c00400c2810f00300b500040c0d058042c071010341401d0340d001030803001e0202484008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 8077426 1250 8076176 8076191
    0x61d041205040308040b092206060f020309010206011202190f060f030903020604060f2c0105060105030103020d03050307031d0102070c0e070210020706110703110c0409030801052e0c0204 82
    0x4550074440c40c08000c0501c0b4050000784084510003014050641c40909a00708c0103d00100207051941116840003d480d100c42060049562000c0b0410350082c40340005c500f00164000007075100c940501608a20108650b801c0c403e65846c001c43c0050001c448420f50b5405899400e01400128203018460100d00301d031741c100801d203110b4400c80c0001501a4013a01446d161903640034060101e100e0620300310358444409540c1c4107059031044c80039180d80090102807550030003440f400c1d5400140101d060201c10302c0100050707145d800c800d0b807005503d0f01d0180d070390740e448000581c004d00a44007403980c0982031820384c0040200540c014104940698a18032001d0390702d40340c1c000c20802c00c40c0c0b03140058004140c0940341d03204907005072880c28818035021902e001c3d10ba0109445130407001c41600041e000c1003480c010140c0c24040040750400075a070a2007a40c1845e180509002d10602c0b07030070702820058000c03004002d2050188002405044588821420101c2c0020000c0c4a140c2050f40b04a141c035a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 8078676 1250 8077426 8077463
    0x17010b030103080a0810150201020c06010902040b0301151202031501120504030e0409031106090d0801080109020105070f02010e0a030503030a0c180510020f06010902070605010806070c15061d04 85
    0x2640c1c1200d900040140c03410800f80c3c803c581801001e04110005079809401240c0c2070407058081c4060398007a80016280c00c007c2c035a107803410750b06074040c60200784100001e1060707903200d0702120b0640c0c1d124485c24030920f4041d84210340014415108030240352001c0f06000240c0000038100c200100300340d0f242406c2e50350341c09400c0f04542040d070b801008500340d21203c04650902d90883c001103802400c1c035140c40d0201c00c2c08203003008400c4801c025241c001c0d510841c80d0541001c03007140981403020081048448684c0007901c0d5209800c405010108a80d0594085a21441031181c1046000d490782c000e880e03807444d0441e62038009030351111040313082000c00d810f402c1c030885c4842c0c8c001424141d190101445d0505209091038180070388000c60040462000c88000100020760080000c0240180e07904910b0820004a80041e00321744081e8201c1030911450642c8119040076983c2c0000411005201d680c680c42c00034500c81e40301c0fa120070204a050000000890103052066014402110300e0032013015 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 8079926 1250 8078676 8078699
    0x130303110d0e010f02030706090602040602011b020c06092209060b01030c0206040803090a08160501110405010804030806121e06010602010903020709110405040f0e010605010f12021e03071701 84
    0x101c0c1e440008014150b8440e16600c95031400720450b1490050f2490f0400d1130325400140d4460340c0066480380c0d00080d0422030654240f00b03007007200161242041c51000c0105000f511b844194202911400010611700c85030754500344006c10804440089502810b0b044c11154050940728800756025803410100c05425400790103100e070408081d6001d06203999990f0789810340e81d000501145181d205410300040000d02c400c00074003107030310b1545850340c490505260940c00d480d03401c18654801d6030300340004c01c2540d0300120f64a0f00147e040c10600d1095842102007400040c00020000903031182c51582800400c200a03803540c3c12120006948aa03078840c1c0040c0d00342c81d62100010010b9000c5142008040c0e119800820100c207a0788120f45815a2680003800380c403000961125015030381c802d81c0080c202c0034420000107103009c1c05c1c07036401d08140c0d00d805417007480034000c448041c80e000110440301a8207000110011200303110071b0354590800d02e0006000d140782900f00c148451021001007502d18861 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 8081176 1250 8079926 8079943
    0x20d080c160f050a05030703080f01050312030604020a020115060c0c05040204050d0311070e0f0703050f0c0f070501020904050a020310080a0f020d03020115030b1506041d06031213030311 82
    0x301d051046064a540d00d003252880c280702c0c1034880740912100703840000c40034801000c0c90340c0a80d132140398505155091124800041e0f02c49480385c2d2151428440301944130017900e0b407000b412200142c0f00c1c03105540c283d02600601080e8620b01001d900d010480340d800c480d80385501d5000f000401508c40d00da00c2400205d00c07960055941c02180c0380030500020b0321480349412141000030680c7c241315545d071070388101e01d00e040e1240c209042881042100896040c4115584803c04910500940c20804201a01481290b40e0340303511440c00181c0320b040c030500350110b402d9158050710800c0030b4a000e880c0e8000940050701d03148642403400704001140ca04c0007800a00b11900102e101064242c540c0c03c00c03082c0c080c018000c8055540f245039400030000c40000348002503000f0050302c043c6241000c0006604014041c40600c00d400501c014462081e02003e04541c1a074a0313021124039803684400030345082c0c0c0607441910b80540c0054440500021014000200c0e03202c0d4607552504030b0442403594958518 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 8082426 1250 8081176 8081197
    0x31e1401090207020a08030c0105070f030209090613111801140a02150411280501020a05070909030509030712020102060618040204090201050409020d1a0a080d030e0c060a020d080c 79
    0x800140011480da41c010064907100801031302d541951040180d040d42c01048444105942d2401001003107a00f20382070300040b1441d03240840c60801c24000050f4004805045680a1800d40710b1507054280d040d40440402080e00f07480c2601c1d4103808441c410b4080740c00c17140c140000c0d88520f010314400081d0381651030300d07a43d603005086001200c510302d40682c41c0081060307544058003031082130700b61200c00e42d80d80f20902e851401d580b200170700d650340040007030294842d504550005081c1404100085502d400f0740301084000b003450101d0742811070350343c0140c40c40651315015403070001401203041202d40b6580e5100380c0070f071a01c655402c0d0030040e80d02d84082d08000c038480c4980001c0d005242c01d07031015083e140b05041890610381c456000d07004076081020010010340e03407502c06005010b80c5a0055000c4482102c188003000e08005080d5100d0000301441414980c540d0010044a20148092402090068045500c800d20041c0c000d50f958480ba0843e13003ca0780c6d60001c00d00706d1a0040450f840c0072030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 8083676 1250 8082426 8082461
    0xf0305070e01030c090207020102030906040902030a200a03021308010c05120c03010f030f0521040503060a020705150a20030a0b040605010e0105090105070b011d130b01091802090403031e 82
    0x5e00440b88010b5844001c00300d04602007001144c4c0c5aa0b20003010340040c00307040c0401600ca140004180c0115000c07030184100bc2542030340e0403c14200201e0803076400114034540940c031540740740e07581d80c2d0090a5812909543d4241043d40040e1a40080540414006244404d0043d00e5010780101d50b84400e000b440054150b000b0107001142d0400b400390f8500d440f60782162510074401d10700c824500004034188c40089070000e030400c01441c08120207038001c800c0c3e510452410b180f541d1030750f84c0d90585140c207200c10045d50300001d8002d0702c0c0358440c4a00c00d012181812032181007881505080d032044a074038000500d480920760240c2130601c2040e040d0386040c0c4422545201180055910b130700300b0100382d4100681000342100160300f1481e880d000b00300e401d41d2500361184036450034294140007001f0a1003034401926400104034503549481c11078510a200080c00c506c580c0b811001800c0f403a1300650040c0181e4280030030035138076603c05043d82510520052040c040d41280b00296440829800410380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 8084926 1250 8083676 8083679
    0x2150909060616050d11010f02030c04030308100308030703020703080123040f020d02040801020403050609060705040e0a11030403090503071e21050d0906030c090b0a0806040f02040f0305070e01030c 87
    0x8005004240c1000d80e500c188840c80302c2551401d10f0301e20fa01521000003035040c0106c01074040d007401420380d0504c1481007582580f900201c2d07081700d405248800b40030084188042110040c01c009488042c542100c45103a0381e14002d48094041e600003c01140050f0200000240010103400460342e229400c0c0501e2864080c0300c2d0802000d454040c0790484c49030346c204108240030041d8030003000100b1640c0005a2120729604003d414510024002e441641104e010030070465813210407102540d5203002c40b6082c58403200c2d00b9000400d1034002e4103c03400000001d101c00d06420504000031070b44100d003158500360300d55490100c003100c05000403002c0d228081d4107000c0e243c2c5010068106a440304a20500c815184d00e41c0c41c50040ca0741107100c0822215032040c440b050f0b140c00380d4929842c85091103c02d203441c0c0102c1c5c00c2d8510070244a0b108000c03040011890702d03600c1790446038200441001c15900d840d15180454070079030307091201722458418000b00207001030964242c80e0407241c003d0b01071040c00c1d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 8086176 1250 8084926 8084929
    0xe0d05030a0315052107090c02190c05040911040f020a0203161a040807050c010207050d08090a030b100501021b100809030d0c0906020c01090302030309010e0103090501090506040215090906 83
    0x100b00c004610810500c5840012130b164481161120500c45010300d14074840000d180460700340b03201904030808041c1801c0f035400c60300e41c0004030b282c0030b010380d031a40350094100d50a000d2040010758002d503030b01900302a10403003403124403410511402c0d0110380401040200141d40300803803050081d0b502c003581041c041e10600400300309500c01211b0203145500c0c400074003202c61710560413046408403514200407840d01e0900030b041144d03000d514401e000911a541c201000035004c1454510700400c2c0b00030010f044d07825074a904000400540d0321152000c11420b168401e142060306d1406101e00600c5800340080744111b00000c48510448003404080d4030608404086500010040c03410400b4031080210360854081d074440c0b280203501c075139a03400c2100c0c100b0344020700300344601d84001d04000481409001581d170210484216881c2400e003140e0412001c0010f0b006000c51301d80281441d441e110110090290106015114900c02c4034502104211003055401a008940d0590703040003404000031100d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 8087426 1250 8086176 8086181
    0x905010e120c0306040501091a0601020c100219080414040204051507021c0303020a0305010503060702100507020709090f0302060606070807080304020f04050403020c0a05031203060411040e0f01060e0d05030a03 92
    0x441c4003403000e96509480c04804207240090580781102e180c1c2d910051713030090007410346040300e2107069030000e41a40d0810301c0000f5514484040903074400d884080340030239081d00030407984001c1e15000307001658910303482c01c002900fa08640b0a800140b0802c40145903a860719100f01c40035203034001d20404048010b444074501e103170880c030300498001c07180400f003880d07403160315190494103031199078003507941c014141c8004c041d00d4060f44603c0c040d42c000010700240e035401141c904188a0405400989a955202c0403442c042d8544d00072180c2c10300d4000101e05024210003080340c114001d4081700d00130340302d2009003c0c09109036203000e400d0303c00c140581c1c1c00003a000c1c0001c6400c01d000030310310302c400c02c1d071940041d04841d400d0b41c084001d64401c1c0004071090030900761610041000310003900035403e1109007409280300040c032461040d51703140b8034010342d034000740c01b65405021500b10000e40c5203032541c0100c035014400e0143e000801e00740c0240c081d4501d4407980341c0c0251036008002d1400d040c03121a09802 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 8088676 1250 8087426 8087449
    0x603150402090303030a0b0406060807020c010e010207150302040807050901030f11060d02030a0f0605010305060d020909030d05090708010f020f0403061503080c0a0b0c0702010905060703050d0f02190905010e 91
    0x6000740c0030090380040e0350b8100055402403003102800103004c2c4041c801c10003201c3c3d40341e000206001c00501008a42c07500070500340b1282000f8281039046402c6030b00100d0504042e50402c0d11421300d501290700d041c0c4e038164040c03c182c400d038070101e94105032500e08004906034244801040880c51400c201c0020340000850705100348007034803250030715030003104440c107980003111003c514654450001c111414180600b00080c0004c0c00c4c100598140840880c05205034480003a00480c2d486021440301d5030204121510310304103500400c081e0030211807807074403403130988116001582400203013070610f8003c1c030840b00307000d03101d036102480c040c9140e44001c06489110780c00030100390642c000001040040006001c4822000050948078100b850080103070328002c1d0600c4811b000a002d80401030f604520340f107003030300ea04075119501c50341d941c502140c031031044c0c074042e4107214101a0004a102c070301b50049c000b22201c030001540d601c141ca0000b00d8040c1124441c03c1e0002d068140b24041506140031400c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 8089926 1250 8088676 8088679
    0x10c08250f0306091a030c010903020a1511010504110a0b030f010306050a09050d031506030209090606030919030e10030c080105150c0703050c01030e0a03050418020403050a0b01090f0605060315 85
    0x60f005585400c40c81c00c41c0c01c1200e00c910060100700c50003815280a10062801c03060034200704039154155004a070401103a03000c2c2040828407201e00c500c030300e40256001000b00c0d000c0b0000340054a040d107480905100c1e04158140070b41c0707460b0780200300e01d070300c82080e00c3c81035480c440611200c1e0b10b192224000b601c03020305841a0a6920703010003020803414031410800c0c400383d0b1030110b401a03110800d40d01084a0f80e002108142c030510202103d03a8900c0e10b0a608501d0440e0115103030344542c9103150070104000400504100d48100c59020076402151072003031604220b07a0181d03540644101603041e1100102540c00143c4107500600031481e0003008e2610790541ca0b0b02040c00c100c065004c045ca004129001960180c0c0170422072002513030700d4011902c06411113006801c2030240c568010b08140120300036400c491404c4440d5030142c0c02c196044d1307001103400c1001c450f08140c10f41001c05036402c081c055600c6d45400c2c200d41e0481130020f07000305011124080c081c0703031540c0d807014032411140315800e079180d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 8091176 1250 8089926 8089931
    0x6120a180b040c06080709060c0803040219030b0703060e040f060c0e040c0305010503060a0204050d0b0411151b01020c0a030c051c0207060e03010902060d0f0902060408010c08250f03 80
    0x540441c5a09000c1841180318458406115003441d501611440d4001d01010070805086405d202c1c455110010744070301c5030b2002805880c0c1c4c45a00c001140d003040d01d070101c0700650540b8800006d004140b00c031a0300910b40e031785042201c00c0e29001d51020b140c0f17003190090000404004110002442c03503200301c100020619000750682d01580014064400090030140000d442c0d2005103d039240c14013050f0382000d41c01800310b18043ca000c5c040780051505000192401030520001020300c4144030441c110180c00030840e90100c0c0e0045c11821140d00098060041145901c013001c1602c4814401c484485400400030601888250790844104402d10741c00c62f658084d05d5003030810600c03011808101c000050b00078001040c07c050004000d040a4010688170343e040c80000c1000d40c640354100c03000503d401e040070500c4145240c056020b8085118000d4000380700042c0000c02c240107500003100c1d580c0d140c0c1c4000c1c0039110514445001841142000780b444940b00d8400d110501072000030303100318001e0070007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 8092426 1250 8091176 8091221
    0x606030210020c042307050c21120a050103110f030c030609070e0903030c031504090f0302060a0e0703021f1106010602030702040609050f0406020915032406120a 71
    0x4038003100c250726000e6000d40d02000000d0081d1a240c007940b0040b02042480d40ba9561170502c41d03421040019103d034080c01400100e01c0c1c3c640310140310142c40007442910815410742004101d01807648584030705404887c9400100d044840c040c01902c0c12207800a1021135074803001010402c00b030051230702459040c8541050320b015500c041c80b01d10700c6035038468060b00c50b0394a0401d103007450344002000c82c3c466801c100700300404950448140d0f9000300aa00544a0020b035400201d4024141c5640180c0741085003a02c11040560000c0c21a100355800071040c05070074a80366201e552443d45020003544442010b102d0b203032605c07078003082c41810155840e05080c1400080769150600d0001c0c1c1200005800011b543c5007981494020b14004214034002080140f030410142e2404e1311002c1d00040100390006012082075494041c65031501c4405112181e0305d007480c82d0030302c00b2a0000c00f501c40f80a1081a007070b11603454000c0503110002d640000100700d503030b940d281600040490b1020364540b054902103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 8093532 1106 8092426 8092429
    0x20d050304030e0d05161e03030503040f08070b010605070209180a020d051c0203030a0606020c06030103080d1407030515090108070513020c0313060e01031406060706060302 76
    0x205070315503e01d0400010314085010401030074078490302c039040c0080748440004000f21110103400d00c508540807c00c0402800d03c0e4031020700800c03070038400500403030b00c450704030a0845d00c14a4aa40380100954490744d118000303030800340c00944045040d00850500c070940795045988469400d094140c848805039807455220402030180040d225407100b0050100048480050b0910440c1d1010f1b40140009569030000c440c6100070b5402c050340028030760300128034945c3d0104041c2c10140385a09546803007030301d64420009500c119a07100828080d002d003900015005413016500032035503081000900a0b08a06145114443e0b103881c0c00412414000140c1c6500301d403825100c51b4002c851100d0400001d0040e1003841035180000180c80071100c000303004c000c05075441034450104c400904001102190190010300c00014420004076465281c0b01c0c001c0c0c0b201522400000c50069260b50 = true := by decide +kernel

theorem cover : BRFrame.Cov 7913676 8093532 := by
  have h0 := BRFrame.cov_init 7913676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7913676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 7913676 ≤ n) (h2 : n < 8093532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
