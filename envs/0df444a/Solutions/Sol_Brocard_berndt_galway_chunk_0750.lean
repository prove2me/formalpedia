-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0750
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:34:52.697471+00:00
-- url     : https://prove2.me/submissions/80364566-41bc-4dae-a304-3ee67aa703ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 134712230 ≤ n < 134892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 134713480 1250 134712230 134712239
    0x30501091404060506060f1219020702150703021203010602030c0c0604050d030302211f0503120304120e04060801060303080f0103030c1509061a10210f061212020d09 73
    0x3407003456045504004046160399450001c940039110700c041603020717a400002d94012070451401c20034007646200c070740084080765501c8100242d0103410400b81d40421000400c803040c0d1701c41780040401c688030b80156502821001c1280070203400076840140981c00c00904c041e01c01000303020741c0481c01c4088420380e0810f0f04100c003040300a0250440181850360010b24007140051000760030000d00880d2440402518240c81080559005030407616410049040040383e00d00c0c012903480300c54002d0100f440d00350f0b0380740d0300c030000318448041c410000d102c44010080050389850044001070100e80001282291452a0060114100034109480407c4000c0140000f950040149802982002803030104c50303414101c803402010305000080c5050f26144c501c1c98850122020140018011070b514801d010500c1e8099521a000e9072415269240080c40c00700e0481c450f501c541480e440c040d40004103203403501003501c58000e01c0700d001c1c0c8004081240300309102e54104490000030202e8980403400b00e01c0e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 134714730 1250 134713480 134713511
    0x61c0f030c0b070315210f0f03140307021f0f05070f020d0504050d1416060c020a05030607020a0308130b0901060e07051e0904021210080d1835060703050109 69
    0x1a0250941405c141e58601401c08140d1b806510340c1500f001140c0485090303071a0020203000006012004200c1d01160f0440a401342e8094902c1541917401500300062446e171000380010340350b040c0c011003980c5e500080d034032040688501403095041d9100c08002507103002001c2c0c03402c00f691501c201000002c1105201d5502d4249190200300c3c1e0100c510100d44005200c4103023042280031500c800c03c0c0c0680e80c00180654440c0104e41014002d407941d0000304d4842090507215001140e020004d68000c00186000a1103444100d600210860304c0800e10303d415a2a1541c0907400c1d01d810070103030f454007003c2c8080110108400d802243d80e0038050300d04688402c14a0a020050401120385240420700d19030b1900c85404130354420049042e42a103a03c1c18134a44528090079024140c0a480703507000d00c06206009100d510709401c0102101402e1604c1c02c1e1540f404001101000b04e03141c18011041d294485d0300031621100580e080b0050902d51601110040031a007050b4007110b9444c0c1414110620a6039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 134715980 1250 134714730 134714771
    0x1e0e060a02040807050f0301090b070210060f0605070312110c06060a060305040b0a0509070e011509062102030603010209030d020a0308070f1e0e060c010c02010b18061c0f030c0b0703 80
    0x2c02e81c4c4910301b5a405000190040ca65600c000c0c0c00d10030b1483c1004030495000c80d2480008060b50f42c10018651950f6146014501c0c80c040d8501054003005001c001c203000c1e03000b40359005030300c0d48041140200300c0010501504070b41099074083d0b1103c1d040c41158980401c200024003da45000c01c05440d003038941e161002006486903209a585402080ba640010300a1601038114840c020f0280d503503814650340452080c16400000500100b804a9100c0c0f0910261031a400220080300d51210305400000080d4030281c07072180d01d590708012100d403030346062200000500007038020740400201403c02402d400700061940040040e04105004401d03085140d40c1302a002d1000741c42107514807500182d601d240c220b003081d070340144080340c000304d092415088840102c4190b4020300001c1380f55418030600c02c1c5107503d40c809101b032403800a580e40c00c10750000105000c2c10320f11605118111b0316001005042e20b80160001121140c000c8144000601c4481c0c010000349003c00c10418032100d0400d552a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 134717230 1250 134715980 134715989
    0x3070b040b04030c0b010b0703021c21020d050103080306030d03020c0d030c0c02191706010b12101805010e06220c0507050601080d02010b01050a090302131e0e060a02040807 76
    0x60001c08901854032410150b00c21380d41c4008030020a586409980c50a81c121107000c500510a0b180301094015040406100c01200f5440d00c140a1162500c02c45c05044100101c0d03070426400d02110010081c68019a40218007130a0160380d80d05080040c541400740782074010090500401032407c0540340020381d900b25608602d4005051070780c02c001140d03401c0c241c050280d0700844005084080b074551940701021540845035110003404040681d03a2251402d20400f480b41105106641c044020640c0803580804407c40550141d6101d01141a07802040c00808500b16a90340c01481403400c1c2d240c0142d00204107c581c0303074000444860f80705429a4002c0c200c0f00c4682ca410207241102d008000f51202c09501c481942d18643e150800c40d644d03004019040070042d800c0001100365540034108480c556101691410101401c680900c01030000f8802070440e85607075076080000e912034082410104001c1101c000c40c0da40018080c0c5403800b0b04c094603906080d44104420805001c000a0010854 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 134718480 1250 134717230 134717243
    0xc030a0b0114120d030e0d17130812090106080127060e120c0f07050111071502070b070506070905040509070e040f05030406080910020301140609040605150a030e03070b04 75
    0x211258042120f2000c0014050054800c10b101e0118035505504070010042100040310190592540c0490b000c00714843c9515041d00c101c404104c40214800760100e04a00856102d490041040202d0300c591100b2a404040c0c1d0750b542c902809419000c0c000c2040c2000745454280040b580b90400c0c58030340c000c030314005111940d40c1004010096080c40111100d07105403020700e0310340b00454000750316001180c4a01665009070100480c140d8010021031703400d0710a51006043c3d1606107d80010300c1e21110387c0490030b52098803000107100316181d0007418681d11440140041c0c1c146000040e0000007503404c054031070f909000030014107450018a5204440b40e01a10cc000c507243d6044c4004100c402c00c802400f540000140441c5158000c404c45d4000c1d505d080494601d4841c0a146000701d00080c000d461401080050560086c80d00708043e14404900400024080d503442d00000c10417145130022100c107074004194400e0158151103040004182100078524000082c5c1d00c15044020040006040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 134719730 1250 134718480 134718509
    0x3030f05070f030b040b06030709050f04141306060506040306060602150603030f090a0b03010e0f160503040f051510051315030201200609030301090507320d050a0605030c030a0b01 79
    0xb591180c000640c1b4410150610390b0700d0a210f00014443d5209008040c002c0c5925244022542001d1044014200408101c4c08440e00e4401516140c80709001e82078952a840300f20101d4990b8070a401000110b100e00e0f40081c031140742c003201a04101c4030f03030504100c140300340042250b552404811503109103010b540c940d54038144e0400190120090b41c108445a1300040004644250a144014080c090750108a03041d039407500c8076006030a030310280040c00544244003140009490f100c2d0446d49500c100241c8016020511030300700022000c0710752101204000c4410040d0f410000b88107030f5442100304061282034520150300d1900c2c41c07184402410400c19054414161040350700b240c98480890041e40c1c0107003043e001c6079640c0c0c3c0080c007441820320300c0c10001c1040c9030300404034071511a0310350b4916058440840d11000010b054482d140c1c08440c420000440000036a00c281da10603003c12000080b450f003040c0c1030500c0c00b0308440c40070703000b503006503541d41c08114009511070445031000841d200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 134720980 1250 134719730 134719751
    0x4080c01020c01150603110307050f030402040b0301091b0f0806041104060b1303050d0504150c0303020c0a030c0b0105060a0503150a0302060d1d01060b090d020402220303030f05070f03 81
    0x900c641080c080c0a940383c45211030000d081324841004955040d5400e10001d1802101e4611610050f581c90300840c01c1001803440120a082c081d40c0d005000400010b1524480d8000c40d0035920b1040c0121104089041c01980560802d442d0b440500102510a401181481c04041d590314004d031000d03060040f4151201d8482c0e07100d070031650140c07004910701d6482e2030340b507a02c03072004007420f020465003801050050003030144181c0039030307044481e02c14982c0130020740c040342601c0d80c413144141502096000c00a24410600030000403080300e110756280d00203c00181482c0b1105030060b044184100c4040008a41b490750060640b5045800d00c100c1100115005c1d002881d4005298002900400041009903110b25a42c2c405940d00e007480403c0b0144450a0041500302c80c1d283c0035104039224180004591810039905c114002480036100514002c505410340a200d00141c03024144000c12102c10f00c1015854014003620394100c3c48140202d00f44000c0180a482e8812558010181d44048405 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 134722230 1250 134720980 134720983
    0x3050318030f04090b03031309020a020705120a02010206160c14030403050d05041809030210180c03080301180b01020c0108060103020d05010b03090c0108090d03021c0c050904050f040201020604080c 87
    0x184800382110850741c0d101106542c0b4440780e00300b84550342c20285000d080c40c50301e08011084401040755400d40182d00d0b400d0a604c00d00a4008a1074031007103100d820f4000c15103480e551410700000c01b441e0024000f41c4520310009180c000010039100c0c42100f01401000304641008070605002d92105040d41d103244421b5440740345000300c4e0300c007800d148034904402c0c42058115000b03000b40c0c1c00c07072181c0200d8070014013408804d5a6a840d40180160301492859422003095880080b0441f400140e44000006e0703612220130b040a0b0303070400d442032000003004211102c4020480d424446a0340030504c00300b006000041e440b1110844200d0500030380c0400590968030a1781100c01e580070920041100f56185d4002c56120f4000b1240803809200f80e5004107403940c01f0745002c51040c6010401490300d00e60200041303010750022241c80d44240c140c1007840c01c07440b074a401802c0600109544c1d80b034440b12804100401d40d07002610010401e03000f002400f002d40d82c081080c0b07034401d41003007207203984036664100136 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 134723480 1250 134722230 134722261
    0x501081b240c120f03150303070506040605090c031203060109210204020d0f02031312020f03040b0d06050607030201151205100507020313030c0503060a0209010504090b04110d020d0c0207060c030503 87
    0x12031100c60004502250031845006140103162000146590040da1407d165980c0320303050003d0000e130b0014000800082e42034204a0303021110000392503800801001007460000000c03404441410301004100c40307540d00400c00e800403c010a0307600318110b40b800502d100080b0140c80070b0301850300050b020000c0016a0018205800c1720070046541c0c0c41e1101502d40b00c0f421440b421a244042414020440307071001a10a0452140c231019529282c500040c181144c1e20074104142015140c9600040355558100603103105130090f00082030644070b204121041d9201074110b0324115500c040040701044001481c1038407000300002c00516a1903a0406a00e18015201424160340000d10088104080f1104605c04c840080d004c940c103640310840d00382700341d00801403a10700162084c04104065100c036000300c4080e04c030142c400a48569071074240e8100b43d114418414203107400103450210301c250b40c464902021424800340042c103040020090691558600180c1044000320104040b401e440410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 134724730 1250 134723480 134723503
    0x6070807021c050c0310020a1b0f051212090a080306010e040603060606030b150a082206050a06180b0105030106050f0f3601050702010c1103010501081b240c 69
    0x209000101503d02207654002d0001003d002e402540400a00c40007103000b43d0b420004541c40f860a038000b12030700400b049032a003c050380e10398662100c010104c1c60a010004842e5411600c03182e0720b4022404031100c03500042d0008500394041d2800c540401c0d0160183c0790412030074039046004240080008000d01050b4001608461414030002401e5800d54003403003012205440b54100400d0341d40f1451400d01079241d1100102e03000c10005280c6d107860400b100700a0406040120001d281d984480003110300032100c01441f00d58450003440311041034000300c1c108045040b81440711070341010000340180010311a00060243c082120078130710749140c007500d00715a6600207454a548400540504141d40c81075020381d4039020070000e000c210384640c4298078402060f110203103000381590046480061f944030550719100c103000700c9882540c082c002c03075000344100b2004040e114280480c0180000c03140c0e2201c0e220784003050540308a03100c00d2140c070074090000c103202a00d518540e4566810a00007204 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 134725980 1250 134724730 134724769
    0x102070b0f07033e12190804031b030e010801080d09050f0a0306020d15080304030c030f0f0501090c030210090e13050c060d02030118060e04110307080d020105010e06010309020607080702 82
    0x9004045090101c41c1341c0c10010a800c8032a113a09104a9034410300c03a44100c50701d602030000381d2182e0a03000b050855003043c82440c0c40c840303442c2c505018011440c8140001c400007a004242d0702865079200b540c5a0141c03100b00085c00130002803c8001e8030b1903115101c0c0310b0141c010088240703643e030342e0940034400444d0000020756445c0c4014035560b006294203440806801101d0714049200c600c000180e40540780e1003803071224a90f007552104030680280480840394104d0942480001800a00906500a114240e421101829131040080784031140d24140101700000004100200f070f548030890304016041b05030b81406035981061800d00200309a070319004007000070090940c80c41c3e0350041d412281c0105600d041c200c3d001c55041c0c1542c0343c5209103101c1c3d0b040c1601050200d120605030f00f4039414003c0c200c55a041d070307d11840c3c7c10560104101000350359900010002404011881984800240380802c940c200075400245207000350807015084490220b05101107485181c920300c00b0081c43c64 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 134727230 1250 134725980 134726057
    0x1020705031b09070c0302120d020403020a08150a02132606181006050d060506030c0406090902041d03070803040512032d0708150102030d0c0e0102070b0f0703 70
    0xc9101c0c2d044194110854016507010300090800392095110454640e8154054081004d00d0440803619803c50004800d0310365003084000011313512842000b00a080200c0600000c602e00500300c1d50404c00104000101401040060144e580e144441410744180023400214411091400c032001035403e0203051721803090000740027400c0301821002c0c142d10004001c44c1e04190b0303082c5015041d0703038562040c0e40d0000316440030440010360030f400c650b82c0420085d044030290760700b0f00002420b95107984d100c2d544a96a4206420070341c2003600814241d0300540e0300c0d01e070303100b05d088a6140c0e83c1e03c00d06801034003034140400450100301c000e00000960704409400e0310345a0038100c4200e65403003a00142d03c260012548803d0780b948240801440c82442c083c0c036454540c3d642c4600c18078660388150092130440c00104110041e80c0c0c003507c6505585249640c4410410312a8800a0f01c3c0c2040c7d43c011000d00041401030024040c0e0f85811200d100d03600d46070129010443e07120416041b242000402035413003900 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 134728480 1250 134727230 134727253
    0x1b010506030d09060905040504080705060403030b041a060d020a0203131509240e030c0303040b19020604240e030a030504030f0c0c0e070216030b0901051506180102070503 75
    0x150401406050228155030b01d9021000055510041030b11800002c10001c6404000901c1c00360300607603204d0b02451490380303000020f41c3c3da5420a0350446003103012070703515040b840d02410035202d181910880c14440c582d6a52062001980c0348c05034084500b8401d40005d0544070213442803043d6554540d2403c90446410f032a46003055a200d80c480002e00001c00d110000201c491490000d0500f2540401040404100d500c400b141d200c0e000307240850b0184581c100b104241d0310204002e0006152543c105510340a80140c0b460a003180c19105000710b5001c40240000310360101211406180003200d00e910004a51064070050031102d0f810000300c2c000072480d05403d03034154100a118510a035103c0d01a030460450035030b41040300703e2010303003d59046d0f18140032425440214503003080150048600004a05031050045401500100e80d0030b00d8038800d00c107180301d09000f2a0340001500314414403c800003004100203000d000d010b030710300b13414030381e04240b0a0b402030000c0c402405000e015960a000030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 134729730 1250 134728480 134728483
    0x11010903120906031505180901020417070f050105030412110c0409030c05010b0907230d061d100e06040902010e090a0605120d050406051c06090603030206070c05060610051b 76
    0x68072928011a00b4041c040320307803011700c0340403a00b81d035030041ca122121030f205100b088081c40010940f008641d0300300710120301e0310440e000c5a5070501802004001450915003080c1101884e0343c000ca041c48014014000040c0d000040c030442d118035403030010403071204c0e02407040c5003424001c2c000c1d8000f0303c0d014100742455404080845028010b00c000c0c04140c2c1000d013400f045442c12114580003813101a20701c070340c034061090b240442892210030241010f01c00b20040d0300f180d1b00d5034050320005404400300c50031044511845ca901c880d1818041c01c0341890a00d160141c0f241c003c00f60b070b10469542c0d550200716070260800c0548000d018002c181e2510304440c50a0041003140565881340e10403098290f0984c0b40000d2000041c07941da0340e21810145080301c15103075a000b1040c60034519581340c41d041c00c00c046500c100d60080c10080c1c0c0102c1d0452445c03c0182c20804090031400401100d000329a02080c00050311a40115065410500840c079480044941d03006420648480d405260f0520140040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 134730980 1250 134729730 134729747
    0x50901060c021206090309100201020d0e150f0105030c040c02010e07091e050405100b011403040c1d1014040b04050108011506081312110d02010501060212070804031101090312 77
    0x10981d80c2c10103108080382202d58603071303003211514556802080341c09240d0402c25000c0458a116000250410030320b403c1c0e4500761400b0060b490f909602202c01d021107107045000058006210300c0391007605504107404a500e610481c02540e0003a5114040381c9083c1d8404d51001d210156910290f505554071800e1260141102444540307030014800c103858440c14a9100b109d004503070020040a408200000080261050503407640c1400350305a0038a8182d50118001d43c412841000400743c554184048841c182140306900490039500750104004140c4007040101599940517820503107015200005020f03104228040d0f80042c01c1c031000041024054002e040c01054138440d1522560715100c2c2200c43c00401c03a841450701c41014058000710703620346450806641c85184c80c03d2030160314440645480e00c83d80100d001030b0742d0b0b400100a016418455550b60f149020ba610385031060039121401ca038012400054112544042e00d0806070b80202440c070001c41d40030b01c41130b2400d84440c0002e452540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 134732230 1250 134730980 134730983
    0xc03121112040501080612070f030b0f011d07120204120c030203010c0f120c0210090b070315080a080c190f06180b1315020c07081e0606130204050901060c 68
    0x20a41e6103a488031107485050300c1c25600103a6070961560340d40c1d01045002c81c0c0c10800d2045a01902d00c011584043d8100f000b000385000e280f0142c1039041601000101d008141d200c0c034565440c0042c190f01840211159581024072494031841180030b84501c01c00a100d1035001d2060010b900d00b03c5003c01420b1709046c411039001310000c00020144000c1510046e0190312020002643e201888007403000540c07010503c14010700c110f6002c1d080102c14002100d009420555102210804002195a150244050310018080c0c404807030340c0f44c40c03405550f0b48061540145801030205072840c848104011030380038001b0310851030342d580901d410800b0240454403426035107139040c0040c40c14000b41d00d050784494035a103c50400103d54030501e40c8540d0f00b403411400c640b5800d015070004868607150002d48401d0034800017070b100107440d001c1940d20b04500207169240b00c80d000204801c0f500000304030f445c0e0102047e251048050042c041c00c0b002440f4075041213900c070f030465001240709580b285035622400e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 134733480 1250 134732230 134732233
    0xf0306011e210e1906060b03010902030108010506040b01200c030a0c1d040f0204020702031501080105070221030a0b01140403060518031801210e0a03030b1f0c0c031211 74
    0x4040403000b001030f10004000c0b803815504c420180ca081014080709500c00500942c00041c0590b11610030000c954003c1e409140d281d5008001803044103000c1c8929500807800b16403c010300364890001070250401c00b01d2042c40070452650351801c00c4814484543c0b0303010000c0079034140b40880d02d000602013006000340009401c010004104164001ea03411740955040070341d0410700c18040c0d007040017039840444100d81502035074151070011400e031800d09028212100001c20186080700000345000a22010742400d8000c0041d42402c82c00514200e0707800500354900030908482120060f91090109a903001d0907050000d07000041c00501c0e4003043c0551019260381c0c0851480c0d452039030b6039001d90b413003041c40e0360840740691003298001c4566100c1d01030800d40c190307013407030786c10203030700e0440d090740c049034003542c00000c00c00c0201039051051524844084501d6407030441d01e9040202c01446030040b2200b48061741d0064000e002c1048042001103501c40d0744880b03002d900360002032109001d0348034030556 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 134734730 1250 134733480 134733527
    0x60f100306090f05010b0d151104091505010f0e090a020304050c03060405010606030b2e091806032d030806040b0d0f0b060108010803091516050d170105060f0306011e 73
    0x16140c01c000d24104190013034061400303202d119030b00340c00822010032740300e61540003040001141ca07038902030444041084001c0e20360310744ca03001c0094400c2c0c402c1c140d96030070070505a00c1105255038105003030390801d132001801a229981c40c031707209161424100b0704c1641485008100b10800905412600c162100da507014807001d0005070500c13010f106550f804090010205800f00681c11000004002410082c5440e81d0303940d5440300302c541116101c0c2240100141c40e154180240030200600c120100c40c0325080344080d07854045044906070b0310360402420004030a01081039076031030b03800100300c03c1401401c00c514580c052408542c182503010048891000400002d0354942c000d80b4150b04807103a14014620b8040588200542080c810131310545400c0c00703100043c1400c40412060b0010f85c452401090840d51340c0b200500700030303101f2400300064000400140803e032150810388009050f464440b0782c8075250741005a4662001c03400344a9076070184030300c00304203070383c40601c0e005100001d041640340d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 134735980 1250 134734730 134734751
    0x3020d0c1a03060d02010309050705100306080f0c030a140102280806030a02090a0e0a0b0108061f0b0405090703020705060a020901120b03060f06150a0302030406060801050405060f100306090f0501 86
    0x1141c0421500c1d258028040c1ca1307071202550103030304540901c0344950280c0300c51948400c0050100007941c0e020100003a0398580c00c1c0118a810441c0b0543d04180074001c142c41001440040d6840e86002c0d0018000218000e511186c00c03002d40554809032281c480b211900c1300b08100c08880004068060800280d1070000326069090100b040000a90041c0c80c0c048541e0b900c03c2081d002c3e0140440322051340c0300748505000800e051100031070186c00b00e01e01410340c03402c1400030100e0344580305d0b00000d410b45120104004601c00002140d08642058a00b02106e5030b074800c0c190002c1c00b444001412302d02550b4108488600c40e60b0050080320f0b42620380c40000116142c002c402c0f0703950300c401540c1591081000c03404e542200e07002142d00c001c0042020021407a401c0d0650f8141d004000e660020075001300600007001002c3c052074001e0500b180c007c001764a003544441b541ca100160403208440f1404011940c04d000c0d030b02d0f03090301954000c00f051044203007918100d40030f03c4031402e0a40e081e5182510030304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 134737230 1250 134735980 134736029
    0x911010305190b0604080313030203150c0324060a0c020103050a271b09140c032206020d1107140a0803012706170d0201051306090203030403020d0c 65
    0x900a50034140041c2d00682d00b0005100101000030302c4540c4404140000035135038a042004182002c40400c03482040342c03861040c549802e0b1101294660905540700b0800c0d00d0350b4000550758803006441880b028501c01c5499210500c2c9929189900900002a08084030f90009a0000c806100ba6802c00032907951380d0301d03c0220752244c10f00c2d0b66401200c1e10600d07101c0c2c4003010203000d040e010f00108264a40c1e082201e2650404a602c400b00c030319180d954a0220401a00c0c544c0c2e481002c9070415895032038040700d480b41047e800c4040130b401015241c0c0e46414450607505a5842c2c055914081004035140e040003c229049a041110a00e08041c56450b503600003180000302c0e17a0380240c5c81400d59003451800d00c002911a4924003000454005525a200290081000a118085c0007150650640380c1c90b5080a40714501001560304040a00081c210141c42100d0305a0304600005100d1629200007411071150740c4c4080d5001c901080030030b0900419800348000c80706d400310b001c40348882106422 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 134738480 1250 134737230 134737241
    0x6040302160f05040b13020c07061d0f040c09050301060f050a0803040608040305071106070b040b060a060f050a0201021909080f0a08070f050c0d0302010e0d0e0d03210204060309110103 81
    0x40d802c0b030003003001000f09090580056507102002072500041c400c1c0ea01c00141240c0200c080000ca40d403145008210180d00007821008104402c40c01c4001080207402003110425012105801165124000c40403248201e41c900e001d40702c020000e02002e82d45a0200398060b000e809614880d811080700000c3c4460000115170440700303180c03124405560b840d10192220f40102c3c4080d0f03030648402c0401d41ca00c0d69404014158113101f10708400c1c480c20903041911820100401c028018103211509010f8107402000700900c801062404d5551385e0703180b0070128007901075561981d070300020300e854440c1c64507040089242a00c002c0390490f4000e20365208003a40e03e101e107c0d400b0300040010400c03000407401d01c40c420311410340560300f264002140880815181404031806500503591050940c0031003105001e0410903040c18500032500c10280030004021030308281c0010140030380d220440e14003075000c41c209000119842e02c215100e0ba65000040c0c09480030440440300c03003407a000300185560280c03103030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 134739730 1250 134738480 134738489
    0x705011b030e070e01090e16180b040510090e0a0c0909110a140103020a050f0c060402131e0b0a031202060901060e0c03150109121103060a0501030203120307030b090106020604030216 80
    0x50101d40e440d00079682c00402c00d07010110094052106000700034811007002000814010f10610f0600d6010481a001c44207001c4c0210b102f0350412061100b0480020685825201c0c0328200181c107072145840c1c00e00c0c000400c48014202c500c403090009035801981d0140203030383d0088041340c440b04026000c2081c41c80c0d45002d0b1841001c80d4103900b030119446540035021408250504070b2800c95860a0041c09410200c0d40c030340190700000800007181440002512104d038030344018880c19900700d00440901c0300e007a07240180c1c4c40d5504090b43d42940c0715004c040007550804400b5081424818009450746401c5900482039804d0030b01c001260010310030f8151060325105a65801d50f11401c0c0b075010f0510034495418104040b20501180340701c1d090092440307240c4140c1c01c01403042030380c0301410f00b4904000c11f0b40b131510f80ba250040002d40c40100d0070301681e02030304604030ba495171840000e80080121030949074005405c0c00011a1043d00040c040340118041c2c0c00300c8800c0a07100c500705107500418000e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 134740980 1250 134739730 134739749
    0xb0705100e120316020706111b0d0812010801050903120106050901210902011b02010e01050c010204091109030c0f010f030e01021c06050901080a0201140309030705011b030e07 77
    0x3508a4200c5007984444455014202610310784416640c0321951604203540c40740281030f044001280c1c003a0100b0100e0002c1550303080094400b21500e480c9619180800003000f91f880c0c03d035650141558031840c0080c1010707841041039866149031003501780329004c00d0240020b40d40c070b0074000c03511044c00081070b50310740c4d402810b40b039410f40e081280880c0c060f040000802d06204d86680d40365001c0200d00c1c4108440510380c1c400156420f401d0000502c80580040e82000e039442c403009003000360368883c040c6042000c0c01c2c00e00d01d907225400b9140c58028800c690140400350f05d000c20590b070741c80d103160051140305002c80880303244110180400006510b42610700f8086900b02d41c2e0f04e00da040c02030b08285407011480b8001401e000e00040300b1844101c0030004000310310b90300d96092115140c80c2c1801c902511441e401802e9181442d800605001c100f0705400e0b00120001c4000f89600c0010400c50b04210b50042c000e04c8541d20510841400360b0ba4502c8241c0481e040c0248035401c42170008104c030032600b01e0704 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 134742230 1250 134740980 134740993
    0x30501060935100903021b010518060a1407060c090504050f07121404080a030509060f04060f0e0a061b0509010c020409030e030d0c110609010507030e030c1207030c0b0705 75
    0x811481c81459040c2c12102c58014060f040380409030a204a0864078081c2e0042d0000c6072a504524050040d02503600341030000074030004003980a80c0090555440b82900c510750f44010394603087d501c014148040c50911800020f08800f00301d003070740060030f200c0b0749501c95280540e05c481c00c0000f6148104d8400c41e14445840000302910f12602101036610000c4800080c96005c0024002d8a008200c0301511086000203140304003035414403135513920801d8030000c4c140c0ca08260b44c2044900c403020348042c00b850703150400101e90490a6211030100611030048905440107480d0413000390440361301007001c1c4c8064503412555207014804403181038405940705841e003a81c1e079007044002c0c0302c2d080c0c046e002c100000000751242d0310f04106070948644582c807080180b52691415204594080001c20b01507401032001200c03d980002c1642d540e80d9141c10103c0b40e0017181000b280c41c1c48440301019511201c0d80300e00074144003001c1116030036240288018914580ca0300c030340344814860007100501c00d51104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 134743480 1250 134742230 134742299
    0x703200a0c0f0602040506040b0705060702070e011502072111011407061a060a02160504140f07030e0d030b09011203090302090703060b07030815090606190306050d030305010609 78
    0x2a01c40910407841803c0040c100ba49030b40124200e0341264100d440034078000034480042c840c040003800e620030a184010046282003501c190007145062003000d00e000410031520106034024465540640420010040502c0164801c448000b071240c0d400c0d07440c1350200c0040d80013948034200880e0003811484000d80b402079076075605001000416503a41c2001c9c1006038400003a5914001004d1441c03855004004044076802460302c03075034140e4021403049250003030304201c00707144408451744240290645261983d80c09800c0e400350481c0001d161145c0140c1030f201200c00c4d003580c8400000803055410196503038881c2110502c010440034041c0202c0e110b01001c200620b0100c10059100041d81b40c0030a510f5900c85900131a5042120218046001c0000300031404000c52142d0910f00310032101d00e14241401004141240303e00b03680009450583c100b41c1c48050300135040100244805841050380c01010308005004140c280120700009146aa000a2120481038010040300a82d0000b6807082c044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 134744730 1250 134743480 134743493
    0x105270d050306010e01051605030a110f060703230108070f060e09150a0305151e0402010c081b0601120506090303150108040c091a040506010c11040e12030703200a0c 73
    0x1708a0858100401084261b41c140900d1181a040e030b031180c402035407600c01282c030190500a101c1e803000b115921128880e9824140000c0d801e410800c01e080c0025030700303403180030402c03c0f240c00c0751101e9110728150300014454400207540c40c100e44645d056640190b032070300c03411130783c00c080b050344150f10181043c0810f00314800c180d441c8650b00f00042812042e55a01e50300c080c20002c0450303c40a00719400d00420100c060354408005281020b403103060f00500d850790000c0c006a82446024122480c045500c3c0d030b860400d4042040c1c021010300484000307681d5a10601c22001c2402c070300700c03005c1c01080041442003600005403400f4082d5040783c0f2000d036441d00700441721010000c10070380300b84408510001d02075005106840000110750032030b00c401440d0b0b2050105540003c0c04841c10016040405004100341e0498609080c10450707021607480540c0c441d661600310b010404007031951001051240068046d40701081c0380640080700400000904811541d0380100c49108011507090071020001505 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 134745980 1250 134744730 134744747
    0x90a150e06180703050609070602070b03010501080f040510020f090406061107030602070c050409030f0201060f050a0b0304080f190f1e0e120316060b1e100e030105270d05030601 78
    0x120702e0120703a0480e549884140c0391070b03000d454a21158000d0318040c030400d60305101c034102601040e14001c2c03555240000080040000505c0e0b40381c44c504043c0807904002e81488110b240320b140c990155210111500501050340c000513050f440ba0b0b140c800c00041160107200b0284400031080042d06180d461516100c01941c4404000c8500e40440c2e20041516601c0703204041485009907219111100000c101034210303107103600318840f91200c1c40020483c0e03507102c01600c0e042e1001000e0795070701d90300d0358540825103000d03180301c4141070000400c0020900707040010a40c403550040e92264210100310340c0a86042c1c507003c01c007005440d0800a41920107020b062001c8440b10060101c2e944103000c24120b6042d0b8021103c035005d40200484940d0910006e030082e0340688030200c4281c5a1014022000c81c40000c0c0d440b40c9034000c507600068013101e14080da41d207d00ca00300c054020700032803070321307650030020031080c11519400010100d160a483d000002203560700500240c80c4c1d2880c6032030341c10040d1207214 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 134747230 1250 134745980 134746021
    0x501170a03050703050d05130203060f0c0a03151a091903170702010c05070b031b0412020423010e0106120e0709050c0408010e0304080c03120a0311070506090a150e06 73
    0x20803441c2c40030391061159a20a1504500ba1008e6810a00c100350070b185010300401d148004200500c8044c8031440d00f1160300303100d103060005d068070a8508412624506500910510840041d12100340d40420020440740c0d008403802410b003030f601546c505000e0402e000207801008941c14155401d19418014a209801410002013180c015070700c080c500100d07a00080e1a80101000380f0442900001c00f0051131008083d0321030030603090410703001548a139060302034880c540b00c0c14864102180c0d181884600313500c091401145685421103281c20300f03000c0c0324020014005035000d05001c001c61040c00b04804648001d440f01c2460600e110028280103014407160203410400028a4402440750001880300400919100c42c5007076005800c2140c4160001e009800100e4140c0492901c0030886051039400d003070009042d0707a041200c480038055540010404c0c400c40090294000340064020340c000c0c400c01e0500c1345154030740d003407100359808003142200f03030742c02038002c210340c004014808241407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 134748480 1250 134747230 134747237
    0x4031a010807030f023105090a02010516080417010213050a0b07020904030201021606140606030603060c0c0a02060714070902190813050106030b070807031509051b030108100501170a03050703 84
    0x1606c404507821041c1c1c0b4020b028001c101da080b80d290100070424015581c0c40a86600902082503698001030031520a8031480c2d100254152110003c00c4800740903a40504042d00d017425012540010090013540203202c1202010040100010180307406611001a01c0080d05060b042480e01c1d800e000d6146000380c0100c0c01e654084c8a024041ea10750044900b041d4000d000c085026546ea240090f160000030b0000d41c01030300200108219a04c000030b199030041d040800160b500c8034904c1a260800a43c008000d6026200241e14030500c440031004031062107100040e01c41c01c9a64000c19001c03441a040ca0744a4851100641e00300a8011036078070303074000c9400000d5904111035580b0642100c3d069002100e08078001c405001d0108d501c0461991302001500b802c102103001203880c00c40440d03a612035a00f0040e22800041c0004008445605400404030750f815180d507183d0780004d40791140a40606082ea213080c0c0000340700c15000540e44240540c0e0000f400c01085c1d42c0d00d089816900492054090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 134749730 1250 134748480 134748499
    0xc1b0212010513020405060a080a020d060e03040938010f0e1c120203030601050315060c010504030e012706141b0a021003020901081603060b0f04031a010807030f02 72
    0x2481402e00819203d10704064107402030f44814030422003141d902a202c9070003039841d040f0902219030005400641182c04441c1003100341c00b5480c255020b00542c412009480c017001c0341c0042c082ca07540d08110004a4003a6a031460b110310300003813030248600780c0c0c0118001040040181e0351540213082000d03003124145808001d0307030040303004903074451500340031680340f0495400820b007030041002d40d51074094600e101641c614105180028003900001e0044901c5410410121449690f92000c5801d20222940207104a141506016002c4500e0b0111076002ca450f04403840111840b40200c0002071030f41001d80c0e1160344c10490200c400c012062402241c02408000000740c00d1400c1d41c18480d06406030005000b510214810b00c9a0522089411014140140204103550380c00442a56001c2c0700340144035040c80c14480100c0140c440c9a1085c021160700041e0340506803a41d00040050384c0c002c401505810885803031001c00c1c0a02445000040d41040303509000084558254140d404e0005000162 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 134750980 1250 134749730 134749759
    0x904022b111e060f1b030403120801030b0c0306011b0302060a05060f0a090b0303070c080c032802090601051c0504050d09030302030a052a010207170a02100b0a080a0309030b01090c1b02 81
    0x204c1e0220100051719a02c08541002080200c00521242d62120300e8030300603551556980b030300322310406000301c1032501000c00081d04030f074400c0c9002c0714174000c540ca0605c268003880c20040e44890007524450031032410800041c039941000500e0003000c560290140072003500e8001880000c12101d80b80316814002041400b000ca00c03800038507406042c025018082c03030701c135120404d0b01c0c0400a14040e410241c95001c0301854043c03445031940c00036010b8408011541d07a240040f1014031400c0c04401c909401e081c04001c18010580c444c81c4241c0c410070403a0300c10711101d882503400154901c4002c0c01684108100c1c1640e41c4924050401040c0d0440707250f100200714544a5401404a07400c645103070750214100c02032082c3c5040b5114104512924185071402d40d000080d11141d21041502d8816154260a441911480c0090005000356401d83e05030301c54a00e0010510825407000b51045540c03100082286051480342c8441520b280c0c0360340c05101c0c00119903ca07a0f1804003004da0707014151118041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 134752230 1250 134750980 134751007
    0x310020306031e150105100c03030b0307030804171504020604061103070f0303020a02100e030301060309030e09070e01110303010e01060c030201021207081608060a050904022b111e060f 81
    0x5010842403001307800030220300c1d00c82c0e15142405038030461140b0300c0103000d0481e07183c014606070000b039010701d408a01c515460300402d203416080d500c010089a40080e0005540d08990030200ca460120b409803100d04001c1a09000b10f08801c0d280658810810802002628019082403003d05522029242051010f8031018040300f00d01909502003900018242001035061004140001180ca4100300d80c1d07100341364080e034900050007030f10145582c0e200c46500b49401900c0c00e0b184120020408400c510f03080c42d00802c0d03640070070000c90101c0c40422400c0000c000200941c0d05079007107000710081d40d130700e40482128044c1c03a410060b81555401c1004000303650400900c0341c400c41c61900c1e208040e08250b414005600032a0782294100030780007040c003584da902d400c041411240e04603a9400e10340c481b40001000e0004a000d4100720003801100e0100b6000e0102001c4c29a074020540e125810b40040d041c031040384580720040035801c030011840c144500d045005841d4140c60200c10f03500b045081ca2428 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 134753480 1250 134752230 134752273
    0xf03070c05100515190905090a020303041d0f090307080304080f12010609080d08012c010e0615160215040801060305030c1c02030a030903030902040612050c0f031002030603 76
    0x4020345840f001001070100580c00c5802d10040140c4400680d800c25106003541c660352805035001d015194001304e00e1400041051548a98005055a655076655044100917442000d807402c00030103004002a820412503a141b44174030300d1300c0040c42c608a030907a980302c00741d44010710480d400a4140070301c40700f5840000c040e016041c101c201e00e00507541080e001400f40b141d194890b0396180d21207000b40c1c22965111030b0003811561184607806030701245286002d8003281c00c5150070713020184000001400c1034449d121500842c000d030740d50303941000c1c040050241e51003050031030860581074075014801801c2c0240b0b448000d10140b1545403d0a440e00262070035241640c3c000c4d1940c3e1300104290708406c2c0103200c0c8401d0402003d19035104015046800780d100d0007083c49080605650740481018180240c11510705180d000f4010404607072130700741c0e407864115101d0041e1214418a0b444940a00301083c0f01100f0340c1009005100325402042410042d5100805454050041c0d100d408803403000030025 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 134754730 1250 134753480 134753503
    0xf0301090504060609050610110c09190e0c0a0b03070e100207080111120f09030c031209010c020105070503010506130315022115010825120b01090302060f03070c05 72
    0x86407508150070010f05840039070300b0030407040d80350100f4412255260742c0c0c003000404407402d0040c2c0700b1540c02c100a040000070303100302d0340080076981046050502545110204680008204081140c0500e003654490004034078582045400009100d80a8100b0207907a004869141046130540c298001c00d0082044401c81d030b0150b4001d203070600c01040e023806204200c80c200403d2508110401c500440c0d40a030181c111246501c503400402c043c50414000c651510320564116035564a0318040000100c1040300c1c5005103518046040c0100c03071040c003076103004201980c2d0b002c2c296400c141c01c1081660010400c00700d5240c00110000009004040d5060086807800b4010b845074001280c96070345031845084100b05a00c650b0401c02c0030841e505110340880002c0ca07045503e0764641d0030000c0681134040b0001c109900101c03040d081a03900c06140b0146111243c0140b041e8444a00107452116490000a40c4003e0602c6004000c0c0507034006154040300d24640a005044070392646810405014030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 134755980 1250 134754730 134754749
    0x51f0b04050109171203091005041208090307030e1309140a1b06020d1b0506100501030e121c090c14041407050a1d1809010e010c090b0d020f0301 64
    0x604005560f001810040144111000101e503020907203152600c13603030104182d40f1900f4000c404540d480b801040349000c283c10402d0f040040c0d04281c2819000407040e10b4414000612a200241151102100391003172180d00d619141002d00c41c2500f004516000c0380411101c42d41d88ac51040c0c0418201c800d40803a00401d071010780307420400742c20084403810216007290035880e200c41d010413400e540016500f404c0b8085140c518a09600e0300c100f16504840b0000c0038140e07108503c144140d00b1001c9130408121942600d00b000090301401c5456181c08241b040c141048105026240010748404004c4444000c048000a0190030591b6a0100d030a41d0b5082504d08904003000c0b4200b0b070505109580c200020380c08000028074052000500c14403403103e0078000c20803841030303003c1110131482e08a218404020b0282c2001840000d0b000c01c00711040ba4620910360800d4141c01c8405c4040c803400600c100c141d03072100040e03030810a0141c0142c1c44031004040c1550308200145031049104040c501034070b00740c034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 134757230 1250 134755980 134755987
    0x22109060a181703031b120a0b03060603010507020c060f0c06090a060c03110a0e0a0f0801020c07090c09120c050301060b121501120902041b05090a060206070909051f0b 74
    0x11180030403007610b400c4020343e41180300c2101c00c6000004103032980140404540030503062162420121400b40a460300000741241c010320002c080350747c0000d20302000541c2140e8507507990a08040c00e8130b405540c2000582c000180103031007800c0180c0205032000c3c1c410f0900f46003d601702106031800a0480300780f40c03590040081541044080d006100000040313107410700c25074112510321141c1d4498074004805200c4030f4503540c3c07029110455024020104d0100101c40959038a84040c041e5100b0748480415000360b110100e00340e6001d109100d01740042e83c0d6480711803401e058280d94021000c42c01980c205004643c00946a9402d00442c0b001d08000344a81e40ca41c030310b080007000700401c05019148200780030702241c055070768000d0075035041d04100d850104818500f40003040052040b6050480d001092940024216030000010280031405032500c001c2c030750b0380d50001c80e191041601c42000082c400c0c2410050804960032143d00075252b454440119440b68001c5c03244062140d2100c40c0d2414040b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 134758480 1250 134757230 134757257
    0x12010e0108060a09030806010305070c0c0e180304150c0218070e011d031f0b0303030a0212010b0715150b07030206090609030406020c0411210a05070e01022109060a 72
    0x10311545410683e200782c240704103c032581e000740500b1802003040d41010394680c0040c00061041c500050082e800448609052ba203440280940f10001c44101034031700040c003082d210044000045404940c004d040030300c1301c1250004102d8070004060400c0e6071101c07224001101104401c2d014034061a0591280c0d51030b2080040054807450520207074444004121a40b0401500c0201c0c0b00c0000340507250349100404040301004000302041c16142e41c0521003c0204000c0b100c480d40101301c2d5070000d04000700c1c3c80c1e036202c00c01c451521030600001e0801188507842401e0034038a0308056202360915000e01c0341c0b01d49540c070b10704503074000310400c1e40168421420b0181d28101403100300d400c120302201070740c034003824480c010f9034560001c9141342c0100e43c0d8144101e00100c42c00156945074580344030b03000d1410f00400f0800d5103207000355014100300d450040030031003543c0508880300003d001038014000b490700741e44030b51f54002c144440820349220100404c0b0815910800100f11850451302c1320120751507007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 134759730 1250 134758480 134758483
    0x901020a120b01020607120e010c02060a06050307030f030507060204052214010b0702010c05070504051008010b040504030e0f0102070905071d03070e1609030602070f0b06010915050c0312010e0108 86
    0x8284038001c52440c1c10703541e022590740032840c5030340a529805c0049594012000390401003808101e66041c2c1d52922041c00c4103642c1c0411228010454000140f154503114810141c9440c80342c440146100d41036810100040d004901a01d0818018400141401d50302c0b400700319801d0452201c0040f56600b041d000d440c0c05500c0c0f260300b011481030711000c000c070340c1419000b4031648a081c0001e814040302d2503400c81040420040704024010180041c0000e00340712010030071440c130702c0c0a00d00b415400e0250bc988541410302c5501c0c819034259444c810301c046040700381319504089031f5290b0b04500a1032004a0500031078020240501119500c0501c004403000e00f241c007106524100034440e40000d0001c1003002142070040c0e03000324040201b044240c503503030310a4544c0c400950001301860300206250741880715400d00d000c401805403000301c06540c6c48000440700c10031a0f000d401c01c00c5040d40a2840c8a40c4034a0150402c0541d4a0031a450403980300310483c0415000d0b4800c50151b521800140041c0341c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 134760980 1250 134759730 134759747
    0x60106081e010302010206011a04122301020a0f1b0b010e1009060e06010e03073201030b03100b0402090a0e0a0c02060403050301060e01090504090302160501020703080327060901020a 80
    0x560056495504584c0001d4075118103200ba4100200344c8415441c88020900480300103043c610204400c41041d8a4203425032042840300c15203890803a40c03500054007040c000c1710111150799843c0e10000c00e0500c004e860032140d290031584482400700b07035440001c5000d54078501800d0500d11114240c94500a444800100c03500050900c60074040e0400038403041ca180c4940140090815092079803071301010910780152680610700b07140096058441561540104004000c1124179850010400300c0040d81030300c0249480a401d03038024800e0102c50f4400e507001d00001c11006001616000000d400903c0105003034100343c40321103140e005d110b83c40603584540340c0c105101e400074005a25080e1005040c50005104840600071200001401030f0701c1030f18807001070b0000400420100126080c025524442c01c1c00041c803c0000c85030200c1c1c10741c000185901220351000f82d90307285070f94443c1e042c0780500001c0c50040d258103171101e401c2c00580050110702d00c80d004003000181c0740c10030350000038000314 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 134762230 1250 134760980 134761021
    0x507020106080f033c1c0c03050609160e040c1107060e01050f0306010311070506060f01020613080f0702040e03180a260c0301060f060210020a1b0503090306010608 72
    0x20700030002c150f842c80c2d80c0520602e1041c049a83e440c078600c442c0030030350120000c8254501c0c5c40c80c800203440300c0181400c2c0a6212810440c601004840148403040c1d0071103105480082d801005400000c0003005c06141c842641030392860008a4410540d01050541e84254441d5000c80c940d211440c0104c20204004c0000f8805403070850b010000d0b02002900310703c00c0c0010020031b18000400075240343d0082c1c110300c1c010f003040300da4160358aa550030002d8460406444e078a101d400258404141036100054081c002c1e0105a481c03120103c03150b81d0160568030481c410814040c00b4401c103c09651503229180201c1041d40c09155100c1d0103a415081e20400c0311219880b0b0b032080700c002d00c42c0b03040c80c205041400d071503100040d26808880f1a20380c84c02107139164443d411344c00c0c100080b40340040040b0030001c850309074007103d85000144003160284d02500c9010000a0701d5040107084030345040f00c545410310300801c10f491800f009180802c1c01e15909070800340100383e142c0148646082c03c050310001c031300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 134763480 1250 134762230 134762233
    0x1210050c031302211905010f05090c0103020d0608030c070312030e1018060615090e0c091c05030d0227010f030b01030b0d1109070c05060f07030f0507020106080f 71
    0x18030b4103207000902e071004940040e0140900c0c080e4108600f002020754007203105501d0849122600300c030440c15030250091000c5906500f09010a002514140a141d000300c001002812501c00108011070081d084020007040c400d4441d000010b8004091005062148a0302c02402c20b65095041102d10310080030103820030540b80040000071180f020820843d0b42610100c0400d002c1d07040e004c2c4a03103038521004098041480c14000092010700584024645e04c0180c0320000e07030716907852040b50300d03050485200403680d0b420084104549009443c840404c0000800c40c14084003a48a035417541c5c000e104030aa44660008218511542059070301f40980452030f00c442c1d2011070000002d21031500c00b00c034541819240c411604590b806604440c0c1e18400280c40030900c1c1140741003c1c0d09403c1643d540314000c8200c80081220f040c45180089070382038220000700000c3d11a60441b00106030018500c0d01019500c00c801100768510740500341c050b00303003640003007000e60600d101e40d41446561190040315 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 134764730 1250 134763480 134763487
    0x130305060403170411270709030311010b06030c210f01140d0201170901020415020a120305010e010b030a09020a0303020606090115020705010c020402090a0b0a090e010f050d050c1210050c 82
    0x14401c024401c505e003002c0c1c50302601c08800344070f0303e034400000c44c40b020f03594003002d41041130550784888020101ca001e076484d0501c00414040301800c0b582c0ca8825650000c004100142d01c2c204190300400101d406030a50310b0382160000308041c803120040d109203500d15541d800400011b800b00d09000500c0c1401c44003070080004640c006001361105507034080b52142c0368000600c0600003075055800401120f050303d40b1004d07100c48000d40714072a162049a8100680447c110600d10030302c1168107940140c101c01c40d1603401e151a0007459080101110280b64a40342640016140d07140d0310002144a50000d101030300300042008200b0030143c1041ca59004002c0001203016030004140d42151000c0c20030201d500494000304010f40704130801b594002084001c000340c10b10214008000e5248035540c8c410320203880b04100c0b4402c203030038403443d041c84015400602c03451401c01a0b058909120b2011144800799581c040f42001d08040d642e04c0b800d8001c11404407446001d8015291b0012550581b40d28 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 134765980 1250 134764730 134764733
    0x50a0b0c040f083f0a090602010609020a0504030807050a0f1208160206240409030f02121804020901170117010c1107030b091005090102030103020109080115090b0301021303050604031704 82
    0x140d81c01ca00c030000e1030240009039040124220001c1440c13001c5030780034282d40c1d902ca4480060051000d40c45030000542ca408400108880288240c88424607150344040c645469030b103803041160400c140a813428050800e003000040c0001c64040321291190180d1f03030044864120250070505c004042c04030f03844101e2500d0310916800710302e05500c0520101100302190000d40c145000101040c01035400a191150110901d81c1154060415110aa00f100c40b2640c0b012409000c03801260300c21480d42c5841c0c04894104e203884e8001e4100d402c0103140c06848a4040030b414010311400303a103c59009640c0603c0c00d00d2840c5e0078040c0000300015400d010115460509003a540c50155201c00f42482d505900801d021200903c40301e002e21003404030a0200c0e0408441286c000d605c2880100e01107001e010000500760810701514103403e81c103001c13011007a40742400c0740f00501240001940d00d55400c00c000103500358040c1d07000c800785015400801c490702d061f00d0302030042c0c1e41d01c665440c05620031404000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 134767230 1250 134765980 134766013
    0x70b04020603100e0f0a06060207030b1603090602070309030501060b0f0f0307030b2106061f1d0d05010617070b03010303120f0608150c040819050a0b0c040f08 70
    0x1900940d040d1465942d940d1081c1070b0021042042d003000705540500c105014121412020301401000554410400c03941e5072001a07944000d01d100c000c2446292800099031001c0c0c02001440c03001081c08d000c0f031501040c1c0e0340e42e81283c4c0403240440200b01c1074034050040c42800d1241c3c202800703820341c010b031900390b090308a000326004030208280c501100000051016200e42c00c04240200c02900c1100350013110300b41e4005c4003c130007249034414402d120000e606403409140010030b6121002124003501f5038024120781c4003410f156594030308d000844096016032607010001c4455401003000003016404d2014080782c00b01c080c401d2464990107940184008180c41080340c0c11039038582821041641901003100280c00c04044403c00e1901c1c0440000d04080080741030580c10200701c440150b40d070380380640d03c4428012806107468541c0415405001c0c01d8184000c40c0e0058050b1086460000c156601c01e13801c000111144410400e002c507040003c00181405d8901810000b00505110180c650803078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 134768480 1250 134767230 134767253
    0x30105060702300601210b06010804260c010e010b060301060c0c051f0e030d021f090503030109020702210d03050423012415082205010b090c07 63
    0xa0b124942a051101031045165841803c0c0700381e2010b10000d03403c140400d01d840e1039003485100310010307039001410040b400403400002615801000c03c112a1100c2c001101c0501d40107000b15040362140440c14001d00d40030700d188445a480302285a0b551034104c24003825211a42c20034074403a8101011504a5036441098905680e4a4500400300c020b99081103001c6540343c0d880b40b500f00c080101008950004081008607040040c1c4074600320001002c1819030341c5a01880c007a0060300314101010207060744c047c0c070120f00840b400b00440c038a0a1070700c4417819903200b03a2201d9115a400100311086085c591079102800c00c007100e002c0310b1140350410094407921591840801c0542d10070001e0100701e0300408500c02200030010004004c0f4101049900038803400c98442c61241e00c40c600d0255001140d10030f10183c440c454941000c07511242c2003035071001005050140081000c00d400844040501120b02c0001c4c0030300700104480105100f8041403080c05030400305610320821940340820340c41400c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 134769730 1250 134768480 134768483
    0x925050907030c02070b0c1605010e030c06090f0a081b01090602070603110f030a0c1b021f02030c062805010b09011d0a060302030103020a2c1b0301030602120a020301050607 76
    0x1160052a980b400c0742401102d400503003442c071b00410000c030780c5800041c1007107140c200d100300c1d4403c03d904c1d500156040010091150740c561f21145803c1c40c10b0a2481c080c0c103166002070b01c010a0030182000051907400031303030042110340c0d00c04000140c042410070700c014454907085c24a020440e0078150001d450f4070785401048141900c3d050381c0b41c81403842c030f003c6800c1041c0161010f5100d09042507a50040d000030411800040e01481880f03000303c0c00744100307951031940106506003401c2520071050411016031900c00640c0003e0003020700880050001e544114001401102210509401141c20b1840c54804040381c901d0080103002c0d20851310101d0799001c200b400c141c602d916121503175010000101221070342054060342c001800c03d400d50003031030583c1d2007198100c41d0349480302038031070007404018545400140181a99003e40c859884103c1c0c00481c1c1980810440000c80a104040c0d482a17004548480c0c1c0015051702081101000c103400c030b4500d04040d4039551612001a400d4061001d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 134770980 1250 134769730 134769737
    0x310050603030d0c050702150a111606080402040e010c120c08010f031e0c06030606030b040c080106050f04031205071a010605090625050c01090b12041113050925050907 74
    0x61341d1100f18060000d50344034540c0203000d2250b1071040580c41e29181c111000040c0031aa40800341c1c40c00c0c0c00049440d4161194030058981c0c407c3c0b0b0128219150200940181d811a58420f91240c4e25030702070242c191041541d88955040c04914100b00040310084c0305030800300100c1030014040500c0e00070204044a170442c0c024403480c48464207001c1d076900080c400504292061b44002101c64064001b00e08603072081c2c07001c000040c2c07050184003d4814102405d0006a100001030040c00e003d1400f91030010780d44010300d801d10f6201d1f51080800c17002640c5042c003103007020400c00c08000c0442082c1c0d401c0d41e8140e1a40b015949003c201620a00801110500c03c21020401c01e40b100381c0d031803411000300c2d141c41e112040e21000e81072058859084500c65800922810350200c2c2280020b0102c800e50144042d4202140d500c1d81c0f80c4035038524000320050741c4101c80b03c01c4511400400c1c081c80f0b0181e03900c0c074041e020603d5102290341c4000c10100820080340006034081010740d80380035905a01a11904 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 134772230 1250 134770980 134770991
    0x8071e050a180e070e032404080403060905060121050a0b2a0a02010c0f02030913020702060a090e0603070308071b0f060503090d030501030203100c180b090310050603030d 75
    0x70003626080030241d5240a0901c40840008240f804000414000d1900f034850514440b00c1c9002d154584460403d5407082044d480c642400c100702540003103070f00a01440303069050540320380c0e8141c04c3d070711280e07801e454591103100140a01100d1803081058030180c41c0c1c0b0b4010462040d643c490701c408850001609403481c100c00145813000c440716031050850800e044c001d06a003c000c101e4060f411407a644401503192441101c0814003c2c1a214070420b1140c00070740c2400a03450800c03841310030b0b10402100043c2c09101e84001621b49202400404500c2d80702d090285040451410080c00014141031007507004a00410100e4141d1040f514802d4111241480d5880c032011224030450301c40d40412082d01c50a540010309541c448042c2d03000d6458030040e80c1c11001d240004400343c510a003c082d6064005414442c8800b2069100c140f80e8081410100e106042c0038240c10382e046c0c0650320483c0c2b150780c0003550039030600d000d011404440c400c00c4003c01160621401099582c040c0e00000304200e95900c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 134773480 1250 134772230 134772247
    0xa09020609041119020106030506040f020a0315050603280303090c15020a030306080c01080106030c020f0d0f03050a090c050607030507020306100303020f0f030a0e040b03011a0108071e05 82
    0x90048035040d12028000380050f22903540f00251542c4001c407031340d03484405410803142c95403041c064102120b401000400721926103450380c1002c852402402c0764051688200003000602445c0001c135882200c0400040c0c51800700140350070112001c91a01040d803504040d1141e45243c01c0681c40b45d603415160000d503541141c038010002c84480d0300121020b540e401090b00016500113100c0315401e06c40e030b5041c00102d40d114a41e5944407010415140810300d400c00500c40d01e40f20b607002c440116242d1048840300540324a403c0d0605505d00106000185004290300d00d8503050301407980c0001d00032004110030412510f4010004e005400f80910500b4002a61030501d0b11400c141c517a2150018252041404c00b9508120700d110305101c1100940284859540c4880010407083c28a486000c00703146041510641208c5c2d060007013001e282e00950f00c0d108180700385c03024820040c0800c0300040e40c540d0600445e0000d0b00c5548003e140004000440083e100b02040d5090340e11300160b81c80c1002078480c90300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 134774730 1250 134773480 134773489
    0xf140406050c01090c0f180203090d050d02130807050114040806010302061605190b060303030405121e040e0103230d030c030b0d0b060a0518040f02060705060906060a05010c03080a0902 81
    0x2c44074090008511210003140c00f51761a24174008071001f80e00010540020000c0000030703400100e40e054441c0c1c01810200c498140a0310080c136a00304002801841c040b40c403407044840c04250341107449142c0c0064030521481d6084030a410780b04040010641c1030030720705049180d8940050000034016803001c03507070240400c8003082c110344855000c000d656891290502c0b040e003607804c445040d1003002e40c18000c544281404401c0741d0003203400002400361011355900080540c1d1006601c280203603980b03a80a130a8211a4002e04041c054610300c9508552650903e00c101d4003155802500003c00142104289030001991405450103130802040d0401303c200c06070000c5c035010840c1764224502d03401050812015450240c0300d00e50846005640c00d4403a400e025807a4184000003c00040010108001c2000824002c41c00c0d4402010540740c41c04541da81824002c080c0c40d440c0d90340e80150248846481c000030120054482860011020b41181e00d0040c030741c107406008060203941d0740c0c802100f59101c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 134775980 1250 134774730 134774741
    0x10302091e12030a020c030d080402032a04020f0c010501210b0a0209060406050d0606080709091814031e072d17040e01050409240f050a0603030f140406050c01 70
    0x106070196500c43e007130303030401179180d4001205451181c043c0c1d040e001c10460103080c2c0d8a00840d00a00103003003401a9400700a00380d0400102ca095211811480310f48583d198002450129254001d15441304214202242500c106810003058505d0030403010080c404500e4424907203a8005460f1102520b4400c0c1c003030000d1060503103142d006000040c0c0400c140390070030002c103c6100c2c01041004070300ea892108803110201a00d042e000100529400c04c081c07102034106842d101c08080c40f0300d81d001900d6480081c209402d0102c01000c2d0400300e07104908401c1e07402030814005000805a260110b9591607241c0d000d0444d031002030210301400540003920200c0343c980480340c0d100c1650100b51000e06052585504540b10780c0074424825000030905007040d01030111515440000140586040708019804600001240c2c881c2c035a200e0201c0140c42c80ca0085030b004a200340000141c3c1821401c008054198000c540d00600415042d500c07441060003040b6012192641341240c1c5840821040c5809440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 134777230 1250 134775980 134776009
    0x1217030a061a040608070906050f0f1201060801180204050616030318030201050a1a0303041202010c170901031a240903061e130302070e060109080d0e030c010302091e 73
    0x400314140b4600d00c4103488018010f0310119102d0000d50b0b41c41c0780c0211035451706801103800003002030004c2c54600ca190400f901c101d51109480031b00b0645d0008408568010990200000640100041061640b02c0d1082c4c032075400262420362030f190604020442c5880760205407041e002920b030051003858400d50043d0310401040300135814168040c02c000340604020b5800001c0b90b072901580c0b20740f03803c5540e0030707440f800e1003d00070758189441d002004001d01c1c0c403254240e06020a40c0e00240000300890149000862100742142d202c500d1030000404482d16954002504149076900000c0e59072805c180d111410035403000392890528146000c10345004940409030584102424007601c504101c815150102c0001020902a9130703030b4132484d180103100c0300040e0160308491807d020b041e034110b17941540840181419403070a81da07503000c00d00d054030030308a03071000441e0685035880625082c010480070080c240383c154241640b020000f03148a5019403034070000c03030303103146600e5103911413980158905 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 134778480 1250 134777230 134777249
    0xe0a090513030f030605030a020d031b06020403050c0f06070605090f0a03081b040e041203110705010203100501050c07050d0204150e160305010315181704050405011217030a06 77
    0x141014040900c41d10a144011404508411014400d01c1c1c4288592801c42c0c000400509042ca000e030248140c054031524180c0420000c19800c0c00811003400d0f04410f1588220303401640e0b00c1c07950820300e04103002c07136110b1031007691441d40542d107555960050f1029250032500002e0786444001e503240c41c115180a50441d907003d0703134600006040c1c118090521540840d4150000400c1c00041c5c56294804c0780a42d10900c10880d01280c0424494028941e21b40c0e40c0e13050004858001700c44012160300280d9044130141c0d000401c011900f024041c02784003c0c00c080c20f01e941405a000985134480d081030044038000c01c0c8010baa00199903858100031008132209006c1140d8984640d0100c2c0c4050040b42e1b4020f800d04000c17403035402c00344a44102d504036038122016210890100c2043c1019000c001400141040800151404600c1c200035030320b60710980d800c820355164905418032066a105a2041da4414803180034600400c0754082e840104000d5600400d690381d54081540000b01784640000900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 134779730 1250 134778480 134778491
    0x1501050c011517151608070201150320090411010507051914061e0109090f1a0703230406021c090b0703110307090b0c0703140a0212070f060e0a09 64
    0x1502010007a400181c10903c0a0fa8214802400c030003444020035105800f44000345d019003446140301c0d0079119003200345840041913401141a44002c03d1040ba0400c0e200b4103000c241c00400f8441c2c07090368118900d0103948078002e03842e00703813100000c9104032070b0050b0621a000601c0020010180058914101c040b17620300e0848071103042c0f062070b4422001801030745105413000300e603040a00c80e40c0c00c1040311400c2c1d070403040350b03007890300c000040c04281d8011100101c070000c081c4000341d519101140010121540404c8516000c500141070342d10204440c1c2519a184104100300c842c829a030070b0f80305401030009a96009035910310849802e01041158036180f61600030020002e02000c6030b0b001c1c1255517001e004940c81510075540340d02c800c0e100d0f403000c2011090b0400003171075080d014020303079501402a12070480d501d072140d40c0020a10320b440400c0c0c0d004000141c00f10b181500341e6000291030030700200b03409414614040c0004d070540c080d0b20144030b0b03c500f403d105941da8119900260250703140510a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 134780980 1250 134779730 134779739
    0x7030509070f0305150c030c0313030509060705010f06060c0308010b18030304080601030b01090203090604020d020f13060302090a020c030d0f09020d05010207170901050a0c020307050d05060108070e1501050c0115 93
    0x8440391000012058100c02c2d4010940c948403100587e4091401c54090343e22315121012480c041c01c0040c1c9007101071100a001604140d0381e100050100345005034000b10b0141202c0016001701e030031680243c0e05120318491500c0209501011444c1524003640320951303140802030f200d90300075a81001103039042c8000200410b0141001c40c950381224810075121000d640c0311000030090340412901081140e110500040140c034080c1e45104181d800a059081100048000310f4456a50f02c0020703e040c03505c500c0104210704094601d550300a8810304210304010b22844030a45034803d50b2580e13035126894480d0100607510b07c0c0d129003505a030091000755250780500d0a54040d41213500281d42c0e1644000a070421b05005104880c0354180594a441ca0800d05030b0003512007440c007031010307a01403046d100301140a480c0c040981c5c08040c0540001c1481d507142c203100e1032401c21690002920110300d507080c404490352185803402c070100d003420000d480f1000c2e42e2600e0b0040a0641403480d11284c420b20025 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 134782230 1250 134780980 134780983
    0x6030106020d02060105010221160c082406030a020123120f100e0604020708040e01060203031602010c021509010f0c0e0f0d0b0a0b0a1508181507030509070f0305 71
    0x202d500315000d0f00c0003030780c1c0d4000580c4c0f59080703010345540e0f41c035900a1f1034050046200050011100c01d000742c03140034880792100440b5140c140c0015003550300929a007882050f4020860b41d1115020280b03024038507000c80440c1d00c0d4000984000d05004121803079140c400002e002c2d460000c400c1c0a034ac0f588440507810540300c003039402d81d1012502a820000b0511810040c01050243c3d401581d80000d03540712102440002e40c0700301c4003690140800d01c001f144408400f60340600030031a80e401142c50341469902c03420382d1101c90340801d056a00d40312030322400c65008154110b00165201c2c600c201a0b5501058901400c0c4050000d02c80514043d80c01511642180707440320950015142c40c800c18520106000000102c078502404c0005000300190815446130002c00c08840060700c5000b41c1543c07804400c1c15140258119400306540d00c041080a8030504241c2c0300300d0507440e00620012203015241001020060003980401d51500001400f60b4010010031000704000708800040c0780d520b00307195 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 134783480 1250 134782230 134782243
    0x30f170a0c02100509031e0f0a0b0402040c05130302040c030f02030907060813200301090b07020705040b0a0b03180304120308040204061707060e13050117010b04021c1a0603010602 79
    0x100d214081c03d65040c03007260320030025101c6001d0098010240802c0400d21809201c11000d5064114410010220345000303091199107030041c800d28a040c0c984c01e25104120a80e078100c0e8400d0100901440811007603c0600002011650107540c00101210500c4046016100c0c003000780c42410b00000501c03803982400501d01c0c4c00c0740c415544000641d184c0303a04032a003590704081c0c0605680700c85842001744560310540100312460040001611541c0d035541c00c484903000315140000341e041700c5010826410300b80107120000b0350403100345605500341070100d18503010141c070410040c0810b0301d510701c490b08200111030141842d401c6031008941d284c50f001b040c00c8801c55080740954240303140000c0700a10707001003040000c1644040e0008508143e811620884100c501650112403040040c3c0c20b40d5040c03044901074140f905440c0c4503620034101040c203499411011178055481005805601044824a040c42034040e00f004100316000c50b0444035614940e0540c2580182c00000000754a500002c08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 134784730 1250 134783480 134783483
    0x9090f0403030c020c0112180606060801060207080c060703050a03060902031330052b0507020d021f0e0709110a0807030b090408030c1e090f0415030f170a0c 69
    0x140f180d4000004201c2c0c64018803031209000c0b0340004041c1d40f054203950880c8280c03201002c80290500042c1d207a44003550020790000020030118001408140e5051241c100036241000041c0343c106040303404a501d81c0f01e1a00090200a004198103841920030340103030000f010008001d5407a130810200034542c2d9282c4110441e50700c0b10560005602c2200c0700880e02c001811a44a0500d000e601c400076100e0781d1000d06403819442000100c1d004508402c10b00c910000d9204400045c0c030301d042d082c00f80c41d280300086004190b40c08000700052003540c0c1d0300c800341000c0d02d0b1903012a14181c000d82c2c032440d00300a900000592420800b02100b042c0780c0300003070042c2d0340f070f40e42ea294955102c0100c04d400704e030f01ea20442c3d90820410400940443c424800664106c2d020f855007e242c0300c424505181d4544100c0d2500d880c080f800907410060b45032452403010048001c41d4100170304956117040d010400c104e407100801c480d1b01260300405101141c8074203050210610600341d03550700c140f9002855080718540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 134785980 1250 134784730 134784737
    0xd060f05030c0111060609060d0b0a0b13200f070501050c0901170405071202010507021009081b090a1a030d0905041d0d110f030f0c2118010509090f0403 67
    0x19003403000d41c0300d44e00d0010315094031006022540c540c2070a00c42c1d4000d000b44070039045074000071280002490349140703074401c0c1000303d40000c003070000030100202020000b01c8428080d08080d24a91252140c10b070b0300381c080c801c0f007584d40d5855003c100c0b040810702619030041c0c4503510301700800c44c05007481c000038040b04009903600e00b00111804410108104140c0c0c028040c0c0d03218010900107140c600c40100c0805005041403403c09580e5400180042e508695040c009020608100300c40d1b0340070440c0310020300c1e80040d0840c0781303072040b0041a00b8a01c01004000b400d40c8441440b00039004024a1410091015054515003924480080c2c80a400e0744181d9000300d286c046030b1040d1a011007061002d12480c1d01c06007203a640d541d6000c8428068840d02c03100c0c00c2c041c1460540e80e0901c1000180450a0340712102070311888505441c900384106841009030340303c8140031010130303182640111288030b5a01c50040440c2c00d074420040710326018081c0d05581110750316041c0a101e070410702c0142d00c0303103200b41c1c0d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 134787230 1250 134785980 134785993
    0x3120411060408160f150f0c0b09010c02060601020d0e060f07061503030f030603030c03110f070801090b0f0601023706061e0e0a0b011e030504032303070806060d060f0503 75
    0x280c0d05d00650456100b080c0a1400200042d600c8504c2000300340d03001c4502d071030116007071003003a10b51500e0420b09541c0d40f0090ba5440c14442e072429010300c189517002100740060000801c1e8104003412641d2125100e81c030510002491221503802c460a5403030480d00a00d041041c04080d007210448140140019408070b080d080d49126001d00c40c1c0544d5003920b0745582d0b80300b0865081e5400352010a00124000341b14007034580450030340039003004814020503a00c400410a0394050a000f40d01100c09030a0b844100000c2003008030a0760000b908132080628081c40712030520500380601e61441800e031a0031080302c10502150240710b2542c00900c203440203c41030079212100d4000c0d070114041180701d25822402403800148808d55103a018540400c010304110035001001c004a41d01d8103031842c0301002203980c4206200500d079100210f40820030006507a054207441c1359030350307103820300000b04050108040d01c40019504c1e1910020303102d80c150054802d20695866203a000b0550910b4064039001e8030a40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 134788480 1250 134787230 134787239
    0x2120604050d1101060311040203150904060204050429120a050a150609051b0c03040503060f15090702030304020d02040e0319020606011809051506120601030b010e030312041106040816 81
    0x1840f17507030200d83d404000000d12001940505c0061b400043c846142021210f803541f21649454042d18841c0d0300c079000c01650359040c481000121004451216999100c49004000e40801450010f0b000d020450f425084040184191803801000442c010060b000c0c418034002007180090b0f8140320040300c2d01c3c1c1404015100c41d518800c544d03045400ca01c1d801241c4134100c6007500c0000082221003141c10507a4901a11000824074002081e1000c2d100c144c000e00410000300e00200d645a0071101c01c5400d02c100d82400c41d00255a0300016201070700c20307403480084200b10360b036550015103041620400c5ea6180e442020060460704841920440580280c078005581584a00d01410b01c072444200402034041c14002c80100410303000700059180702c40c2a2540c0f00554400f40600020360004000101a18150000406a4418001c00f50510511042c00311242e98040240c89a8080c001190b40c15981c0d2810401d5200225080e402c0c0c10800009001c0791101002c11701211800c9444415115507590303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 134789730 1250 134788480 134788483
    0xa0b060f07120f0c0b0601090911091003020c061f0f06050306030c030706140309030f041212032304020a090c02070e06153a0c0314041e02120604050d11 67
    0x3c40c24a08001401210130710001781c55909401e400c50018503003006103584410410084032000c04140c100d2407c0400d021520b440c03c00d0b230055281850b8501035050041201a00e59204809844800007140d1402e01172445011030440f40010906840c05014055a0705005051940107668450080c000d400b0901100c0c1000142407080f21442e9969260007092280242181d07000a4041e1007140030410907a2080d00a04e07007d400a0b040c2c0c000907c2c5000c1e81032030f10321a400d00060b50503017898100000d01142007040e860005a040c010516040c05645920018010812603007040700c03442c0c94a229000c1072680000c0038801d4410001511103292569030402900c030001c0904420004010015400310406e05104007940000d14401c8070340a03181156000c1d100d00510010704041c40c1d8450221503442d80c94029202c11418003070750009103003826290320ad4115102482c2500c0d00c410348800004645404641e41c100808420955a0f1800d007031408941303607520705010600140000c420399142c41da0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 134790980 1250 134789730 134789747
    0xa0506090f010b03061306030b10081e0a03050901020a050a03120c0c02030309060a0c08070b040b0c1602040c020c090a02070309051009031709040c030b01030609140f0a0b060f0712 79
    0x42c050f6000e030030350b6581c0b000c010011003062492920301d42c4502001002038001410380340604c006c540c41d4148641404000740c40c00e19940f500b070b03011000b001066103460401040410740320b901407801654a416036001030380382184015000b070030303845020a10303400d15a0101601624238400c2c6014013105410310011100540c0000700030350306800c20032202c9110b10301a001840705950906280341c08028a031036a5840c0c3c0c02c166010b40e84001c44070b0802c8100721040010300da000480703410142c1480468507800921a03182040207000360b6442240d158903900800c03a01110b6800200348109038a804007515001c1c2d00075072011000f1450500000c075041c6005038641c0d54089082e45d840030940c1c5152504110300e0602c03000c0c2c0c80084020001d492280c1c03140c0c0519280140e040e1000b280d1001120001000c66015078001141245071100404100001180840c0c20030b442c181045515160304401c43c0c004c1000209ea6039200300001808814400300c1c05c00741400718002c40051180d0601e818058030301c000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 134792230 1250 134790980 134790989
    0xa0e0c06090d060902130203040b0609070503040b1005060f04150504030224250b0702060105030318030f0106030f03090504050c0313060b0306011e082b030b0301050a0506090f01 78
    0xc105210048103810b0100039400000c0c01002e0104902d01c25802285501960002c540340c020b40000400c800c0c010380c001103540080003682d807440c0d0341c54035520050082c040508020300d000382c080040b800010b400345078030b006864010409a51400303070501151140d07001e07210b14400c440e600700c1a40c0c81c0900404c20b540c1180e4001e400e82000102c104a1055200110140d5406914041c44141d440a1041c0400010652103104560480a96040520040000400751821903201c43c0051003c6e840100c01c1c1d440080034104403070309101300140000c4c24894036510000c0b0725840c101c000824031802c0300c90040c0850098507409002030b01c1d0360912056034000c44000814100402c0465440c60b20031211000030b5015140000309134401070000307802d098080c1d0040c2903042c0c04040d400049d1001c181c0300e0004005040007094201300071041c510342c0c0000703c0e4240001e1010303c01c1c0301e01c205009070401c85181c54010000c200e14640560500300030601622443c1c090107040740040c201d4154626054140d0707 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 134793480 1250 134792230 134792239
    0x90903031b0f0706090b01051918090c03050d05040e07050a0906050f090d12030f09120e01050d0504061a1e0910080f03070506070f0c030f110f01050a0e0c 68
    0x200c0340c0c500031120ba011003800e041c820020005038010030010304c18817140511072040c030041949804200004c0001824244240101c03800c0108480b04075030f02045a000900040031404c40c1050500171000ba803182d1000d0703d50302601485164450340314004106a4051000c00421512505402c90710750003059920008500148024815503000b100070340011036145c408a450590328102046107680d0082e01202d00c200c00007042180c0319014011000d0005403d50104100310030358039140383c0500101c9040061040e003076400507a40e48118203c1e806c214145505020600b004e2130320500034032095600050b41c0e45521113001c20351a0000444d040440b02c0d1802c10f5140c0300c000c04100c1225400740480c108080c080c0310004040c0e006106020615158030055034803070403d030400e03d041c140010b001504200d84e60744507240090300401c060036220b4062400041c412444174042d104580128452403942c8501400d414809405401c1644104241801408200c03000c151032661008000241d6601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 134794730 1250 134793480 134793511
    0x703200307150609020c0a2f1005040302031902010e09070c060e0304050a030f0605060607020d0308060112020316020715050406080901060b03040b070311040609050603060315011409090303 83
    0x1060720070240020782d04419000040041c1d6940caa4022644601710444058000c3c0600d04140300303400c115070001c84900015008800085010503c0b0301c080415801c1c80f546c20f8481c03650701c45c0c4c455019500610340c040c00719184401c1049c0701c008688520441240040c0c03140c07150040a08010a000303025600a88030ae030042460303903403034101421403916441c1c1c56203c2803000083c41c1d0b6807403c0c07140045006000420208655003070280580e10000d142d07a01410741001004e006855410110f5411901450b054025132148401280c000340b07903415810a660000c001e0100700c0400f1802407018420039002c03101195950080b018008030f118120001080082c041002a00e0280d00c1c1142e00804403c00000c1302600d80d0345681d11a00b0a0310151a5034070b20030100400c903074045c400c42281c40c400115607410b06292550040c1081c0c10350042c0f50080300c002c4041813031510b04000b50144d40e00245445440e41d81c4a8070340440001ca0700302d0192040608801203140750750080101d9002d03400241c0780045 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 134795980 1250 134794730 134794733
    0x19020105070b06010c050607170907051c050a0f080d14040203060a0b0105070606080303370f140108030d0b011e0c150e01020307030606020f061906030c09020703200307 74
    0x14802da00030651811310441651030310010b08180102440f803011522442c2c05c81154102c0000781c42030003880e80010741e01c0000305110710b540d8501e00102400c044801d1184201c0649801410f040310314500800d00348000e0300328420031490030050a41050b03680c60030483d0f03003060088030406d142c080e1800794140c1c21032004100300c2c00316600b20015140060400c585032540650f588812581182d104000c142c1000c01803159811258024254809035803994907011841c035650b00c844021805580c0058913138610010b02c1541c03d94002c6c81400304002d402401e00c2d0780d1007a07204d88a034000c040405034686400400e84403580108010104030340a0401180d03551580441a54a03103070004060b1000c008513001840c80681c10700a5850283d010400035072642044a030240594107180c00c2841550002070805c0842480000d10540c405000303005101380c00300302100351004142c2c9410140000340180c9001c150104150010506140309c2e0365a055141401303803001100b030985030b01050242d00b00308072040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 134797230 1250 134795980 134795993
    0x8010b090423100803040609062a0303051b04030506012c01061d0103020a0806090a0209060408070e0a110304030809071706090f2814060c07051902010507 68
    0x14031014040e1000901010a03903101c40c890308184500b900c416010801c022a0702c0500c0303002402070030301c0001141814205003000c0c0070074049010350001c10403050341910804c01101d482d41020034100111088140d56400e0040152070202c0f075950200c014000d40340500f4a00742c0884080303a801c6405401541d09184441d00501c0307040441440150350703a440d130600440c44020f1103000f00303415103640d803864811081030b4074a00c0f07100c410b80d41854414010202840d07004200a54040d5045400300600d6844550090080c09280e40c0c10750001c4010902061103d00040c0c800d040c1e800b00f1600d01c0c0300d0340d40c942044c4107030b51052101c08600721040c400300703000a01400007243c0041190702690a0301c2d40307440d0710000c0c24100d03c0c03000340564088014400c00700e2062041005038001c2401800d14840f1070b0070078644c0e174103440c0c1044441d115140314140c1030041301d03100b25841541c40d00655000d410107120802c07142e0401c240c107039464052103655680039400a00e0520078a82d068440e2810101c1d02e48415 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 134798480 1250 134797230 134797237
    0x80d020a0602090d0b01121e02060409230c0c16031a0406020708183a021f211a04090510050103080c010e010b1807090b04140108150108010b 62
    0x40c0c04c0542011804002003081c11118040d2450f860407841941a40c200640fa11501d0030f0104c004003821a80c041c09038641404590550741480404070301d01540a07011115583d1041d502c034a99610402400141c00364030700144a008811800c80e0384038042084101a090514403000740304a1040b445480e122904084071640b00e40038420050078401c8545500c1f60b00e0b403010f000007002c00b0594001c0512850181422a03010f0503861020126440d00070440d81d08040c640484a2403403001d1200404555900c51246a41d008241310101090b0f0f00d504040c080c44066441c1000f84494200001100b48040c481d070000c050b9513a07414609000c2503014040281a4680e003584c00340281d0381003521500960149a008500c6a100c0301c3d9030b40f08021203d82140d868100d006021390610203608450b175150f00c8210030b440e66042888500307490b41402a036140b90940d100468411010034001a4058403d45050981c4020f8941456941d01d100203104e501c15507171030315401b18880030014000700c191080034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 134799730 1250 134798480 134798497
    0x2104060f090503031803030c07080705040f02070b0a0f0e010f060e0726041403030f040b060a0308030c0f09090c0a0f080c0a0c0813300b1911040b070c080d020a0602 72
    0xd89107070110600b441c2c1d007270405036000400560701c03d0f02c0c01c01c01c6041c44c0c85214001402c41d5011070038440b0607501c101c02ea10024004584140e01d0700c25401200b84d030355010418035000c900003000b110200d00c0016000d40000c3c45454008101c2100068415008010703504a03081941e8600c0d0030641d0501d030301c4020b00c0c0054800e5507015040c40582c403030258104020350003a4501a0038031118a010f01e41442c8101e4010030b00d500031003021000b04001801581541e80005500b440c4580742c0d0a440700c0740f940303030250b4004240c0c0244076000f4410404260380090100724150b640d81c0043d04840281682d2661042c0c1e400022510100702008506100741d805414451160701150700e480030401500214510307941081205034180800401c0d181900c40b0f08200c10820038001801680f8251140d40c42e505c030044c8203c1100c4080032901d407a00ca866032040005034150420b4540700e1307031921010030081d04a4001129400b01d45040854082400038291f0852a99940109a200125640e280c06500940300 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 134800980 1250 134799730 134799733
    0xe1510120908040b0705010b09090309150f0c0d0f020105060d02010906080711030f0405010210090807030c0507030b0f06030d0201090c06050c1c0e0a0906050d020f01022104060f090503031803 84
    0x1020845840ba24024142c1341d0254002244a004400c05c000b52740802902e40d4032158000c03c01e1071303050307106c405022844000386844541c460101d0040380001d8410802c014800340a8040c01c00079258105078441b5076004a94000c20a075501c120510101c104254006804200702d03000400c04c00e03100340203d83e48823500e440c2070900c46d18103a841070b00d1034016002c107202c4154003080500203940d04200c041141c0b440748509011024030368071070645900c00d1503c06420000c1c0c070342800702409800c020550043d03a00851419062800d40200340e120032054070407a200740075400050756885d00c14020744018a4000d0445c2203a0b51501200303403181c0d803022420110a0107250f94252087d0b036000b8002e941714100b41c98000d0f007818424100000c074000e54208440c207a2400c0e0f001e000340e8a17003001007010b80354103940c0c1103d50b58001c0010303842c210702141281c0f000100364054980d4281010090300807500e682c6c0b940c1c1014070129070151040e100034011076805a20a0154502c2a42e0018100201c000c0240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 134802230 1250 134800980 134800987
    0x2030a060518010e06150d080a0e0604030b01080a2f010806010207030615030203060c1c02090112020a0e03010b03010b03030f1e0d05071e021b1302040e1510120908 72
    0xc2c2d0142540c07414031328500701d03030071003010005c0d82c0c03000264000c82c00d00d003151440000322079aa0303240500e0082c0f100d2001000341500c03e4aa07662a80001c65000d1500030034500d0041d80d50303192440e41c890081030100e6074451510302d2480c036001d55002c10450412566142c0390411640ca004444040c00240350504501c10390100001041c0a441405035900c00301d00c5e4400c0c0c0d20b040d40141458030401030506071102404000903100202289515000d04440420269580c0203600049941180ba01083d00117070b4400207162405030f40203e48424410340680003030268904103c2014202c44a014085800d6081000100c2d100c404a00041421101986006200d000c040f05100b007280c1007070146580059642003402889508031001d22206c50440584010b1000c0d190f0009480740b082d400103000700290114104107643d183c43c00261500b44d042c40454484e039460512801038074040d101e5a00c2d12000840c80b4201e420702c035000d0009104191114a15070114403a00300092030610381c107030380900c41030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 134803480 1250 134802230 134802271
    0x1030c050f0c060f0619060c030201111b1005010f030f0c15180905070c030f14270405070e13090206030406020c0d020f120d11040e2202030a0605 64
    0x59024140b100c5150004018a152404440d0f8100d08094003580c072032060b03201005902c03440c0b00b070718000780d4885150101c0309a5031460140d0262590f00d40c003001030b1300c0100b80201c1400c142c4040340111050f400c111070011016941440440d14203000d00c2c0e800c500000d02c1840465802624642051f100b0742124010b10340d584140c1c000d0b070001e079103000b0000c1c0a21020314200129500604084d00100c03c1c20803690400c0e610242021000c0d00700103041c130a203400c41e545082e000e51941420000b05003181c0380e948004201c8208d480c881d0491001344c0819041c485c2030783d0704080c426540700310101d03141c504850500368100080c1845407189202d0542e01c3d103a0000060b110703c03004c0c5014900c521009621070401800c0523083c03a0b0134888442c1194826a100c00700307000e0000706041d070460891400e80d0303295691411540a400e08401854076400c3c0010009121003e4401c0c09105441e40325011300d4210199401601d2103002e410080d41c15444408290003082046d840b03550842c084804407101044035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 134804730 1250 134803480 134803507
    0x304090603030314010e07090e06041404080a0f090509060609060f0706060306060801020a0e06030601020a02031f150303090b18121b0607030c0b100e0405070503010c0e090601030c05 80
    0x81e002100000c0c0c4418002203000110380e042405803a050400004919210790700900004551281c8000d408002c008150503032a41e500038030a60070300b0000406140303068140700300140d0000b120407000440302d01074113070801c0c41000031074142c40c0002c154008603182e00007040266080354040d1588640200010038005000c400280340c21407007080c0101d0400e10307504100e0b0450306140e10000b8113034010000780443e940c0c0100800c0b040e0004030380c12610f9484c3c00004074504911510001d42600c140081c000b140800d01d2040da8000c0c0140905124040c2808c10607868224103200c000c010452410080c00107505200282c13108003455452030243e02d40c00300001d019000e21481c3d50856800040d002e4686003103004440b018040141c4090b840c00d51981d40090241440340406440703100c4084c00319440310303030700144840205900b003551060f47c00c00b41009a100c0c24540304c0c040c800e40c40d01e250024240d002e0343e0914070800c0018a40729095480c940150042c0000c0704e005410018100720000d5650107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 134805980 1250 134804730 134804741
    0x30608031306090e010803070303050a0e100504020f01171306021201151107230a05040c05031f030b0a0506040b0406090b0915101d10030c080a050c09010c0203030409 73
    0x90111601c1d1100d0700d4044054500c0c511074001d0840e4500240051001d1000081200d09280d81031070002070318cd540c03880ca03c004000d014041c0003e0701503202100504480754202a0040d4021900c040305003450000540d0114203083e0400e070320f1001500041d0100c0d1559881c41d401d1401403030003610302503e100401e44080b1098110300d140a6000000b0300703115030b00c0815410000f1400c80100845800c05604102c0030030400e40c030b80d03030007502102100170a07110704840e4801040058828003402c5020580545290001c85901c600c0c3c5090010114603105030142c2c150807a074201403128900e07160154010054100204100c0d045901c945059207180c99600c10040142a451400281d08500d001081980c180180044c5c8200050040c000401e5454641c000360030a80360510b40118000070301e48a600c4001081810b03442000300c03659001b82c0f6055001004803000c16a0344002546c6e03494560401c680e01038640e501d0b003440a2002c0035030303075024030a0f00960381e000508490404d5501c940c41420346d507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 134807230 1250 134805980 134805997
    0x10b0f120a02101220031501020106150e090a0b060a05031e04051c03050108030f1303140102040504050c18010e01020a061a01030b010c0b0c16050d0801140a050a05060a03060803 78
    0xa0741c0d940905030415a61268280900c1e00342c40702c5c40e2401014400070b05500015264400d1a00d2614061244da8000d51081c0000e00140c1e84400043d007140c8005400e4441002d403141c0500d001c040000d0704045c85104a070108540100a1401c1060302d200440300303600020320800315807001d80c10403503251598503c01441588603200404110101140d918050b10481200b1000d040c100801489000c0010095407000800d8501e41603c80060a12061884130181e201811041005140401c44001034000b8400d81d002170f54184201e44540060342c42c00e00c40c03100c0515940a44009120441d8414007030a1402441481107a90348039a41d140c000880e0140e00e07041507442440d0310817a5555070540a41440e40c60242071141c007080c1582c580b0071402400507e200d01941e00010811f8607007a8111100c40d5240d000400c80c0c5200b0311211018064140a001d564002050011800c009152a40e00003013596409025010b0786460901403050340d070000020714040c162251004a44024100054140070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 134808480 1250 134807230 134807237
    0x30c091c03030f0911190f090e010606050f090d05030c0d0201020c06010807030b01030b070203160b041505010f03060b06070f0302071a03270a0203160302040509010b0f120a0210 78
    0xe0034103180c0503040321441e4448801d101e08010560000c18502c08904041c00741c255018000013000d02626441101c40360001c299161400ca00410b00414030350003000d140ea858402000901c0d01c1c0e410588082c0201c0e04240c407486400c00c61580c103414030300f40c007580d064443d40403282081d10285040381003852003840702005039030215844213024030410134280140920f070b028000701404c0d9200c504805c0014000a8031b041d9208000c01e001d6882001100c00c1c0102c81605e072240341401d8904580d511030161005c0c0c608030034072092803241120351300c42c09040301c50f408034090360319141d65030310300140c0300301410503030700041c284204030105a2510455040314440c0e03014042c4a42800b0308030074070200788414011a00818410080c41040540d0701c0c102c4c4845c0e0168800d858442e4a501d241b610741900e90003074040c0103150b070101d10400e60302540070541c0d00c00c030341c18031195680035600c50032540c42030389990b84540718102c0c0035150700307040c4809103441440b81c00317a801c0c4441c80c3c1c011807450300c0c0031007066000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 134809730 1250 134808480 134808529
    0xf0e04020f041e020903010b1005030705130f06080a1a03190201210b010813020a0314100c0906090504180f030c06020a090512010905060610030f052a0309070308030c09 74
    0x1540b074203100348e0794001c0003100e50629925520313000400d240801000320b400d02200140400c00b20b0f114910703d00081161040340c44000e620740c4001800018255800d04603d400e02010040088030460701401000024004082801d08458aa811007040c8441681844201202c80202035201e00000140d81010724006c61140700d03000004210000040c41406004001c8824400580e12032000400b141d4000c0006911060b2560350b00742041d03440300300c081d40b45180c07541030029590404880c0084480c0c5486011050f42d440b01400196526080c1c2c007019800e080030490b00051002683d1890305010f85000500c81349640d4540e022079000c1a00003010031040310081000c1c7c6021074501940440681c020300c60300c500c1e23554540d40d0f514080c10143c03040d4942244500490701c80c2c3d002c0004055482814401c078103240d030082d03045003d103c5482546202c25074100c0c07210350f6013104880c0074440480017001c1c8a480c54a400d00f032500064541100007804119144260b917070400c49030f10000d1f5208640c0003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 134810980 1250 134809730 134809747
    0x191e0f02040c120e0705030f06010627050d0501060303020f0d0203040b0a03060f090e16030809040f0f02040303080103021804030206010b03070c020402030109051f050a05010509030109020312130f0e04020f041e02 93
    0x22348003c104201d820790340000300501006a004010513140c01606c030f1501c000c920b2142c0714100205aa401c03043c1c0124117007460000788441500075038100c074025003e50300b100d07942400c41c0c0d80340e84c0c0404101c00540d0082104210741d0146100400c40188246400942da40d1152401034040f030656000101154440d0228180603000b40810451500c1003203c2c124401e04d503503944c03050741c0a60b800903845aa070714507103001e9240140d0401c0a0034603005504641d13a5440b450007820300c0000703010580c0181d1404802c80755040401000ca80640e40680050885a107441056449940020600300070010654403103401130701da500146010707141e00040401c4030f1420041044484413407185ca20080030814000f048940c03592005081500c03000c0c600b15a840740c0e1507011a01503e14440001c1d0180703da030348040c42000c0b070340001d069452550b91550821550307c0c601c407810842c0718020000c15284500100b40103207802c0c0c1c140b804580001e000800c110340142d40881c100c02d0048810380c01141c00060001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 134812230 1250 134810980 134810983
    0x6040c08120a1b020315090a0302060a090b1b04080d0e030c010207060e01050906090307090603030807050c1b010315090501050f0d0b040605040f05191e0f02040c120e070503 76
    0x7201c02440c003418104106044000d084800d00407030035002031503d00b40070082d920709000344071280c41003205000d01824138103400c5603245248502131300140201d80214441107400c4c01224250b81d0040081c210329142e84811700300c5003828690060318a503007044002400d032424001c2c60070b980d01c50340b034400c90b59050f4030603d814100045003260454000703088c01d201d15900500306100b070790030a05c0c0654031801000c010420750b1155041c841d03814407840c900040d401e0065000f000035039210381e450301c482c0d8844040035500d600403070540d005290080342d03521540040030381a4050030032051401140064070000c02801c5210700c0d170007643c070080d141d800510050414148000400c1d0b41a200903100c5203690f01d4880041e84082d0000789003944450106003480050746805644540100c00c0d165480d10b81c1c0d1001d40036a55504080b1000d484075031344c40c1420503d41000c01a01070304003142d1003034000c480d800c010040c112858580140001d5002c100e4008180c0d2080300b0b020f083c0600244961403e040070075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 134813480 1250 134812230 134812243
    0x803060906060310090507030207140f0c010c0b0604090f0206030412140703021005150a09020d05010f05060a0c020402040801060803270121110a03050f0a0501080a030507021206040c08 81
    0xc50090b03000700700340b101400021a03e0310859a5140c0300040c0d6499078401180a03125584020b420b44075041510501880046603000040c0c80503011103652a044078010350b5102890f400c041c0c80d00c4030050016815007001d80181424501c01c013a8040000680e6000602640007510b0540303100000e6401610f603660410600b4900e0015084014281801917600941c0c40c003030714110354503c1d0344640200d10341d00120352104003401c50013440041e110707480e5400c980c02074010300492240c1d1410300c1c0c000a20780035451592401c0c2c60010744403901e00204000251442c200240c0d040703800030f50030000003815030020f1007003d020b0f10300344000d9580e8407255a940e40c890360040d032120403401c82d0600c11002c00c2e03030031401402c181100403034043c10500801082c030004000e04183c0d00b40c04480082c1021f80a42d05900c103611a40d10310410070b8158441c880d0f80b0040341c10034000e412031a44010750a0380400e028401424a00d440101500401e03250404031506103030050754100c610852050b001e12110030b050200e0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 134814730 1250 134813480 134813491
    0x60108070201020c0705150c0a15050a181b05060309010902030f03040608010e070314010e1f0b040909050304120b100608060906210109260f03010e13050a08030609 72
    0xc3d414a211644003503121501403141d94891581070784903012001c1804103a414101d008400d4030080b40c41418128801104603644900040c9042c0004601c040c2038440c0d5030070071000000b41200220150348654502400194580d80d0030324440c4001420340d00c080040d8030601c102030010038880a01e1051500d490044808480784d90000d00050000315405070103117045580c01003005401e5100c0e03060960007400124200301c00e841c1a1000030840b442c4c40009a07001e1400d0101180d0030320204241a070410240b8050711000742c03802c000800000c60075402c1222071500a6007603d1409544080c001c42c0e02c0b03610380046a22103203500400c06030161210500f80100350030b007015081498082d0001c0c000110061205209080040941ca030f0000c1c102c45905000c002200204040d4000707080c81d803e1804070240c1c900c13a0381c400c02014840c002240056400807040e000c18142036908107a294002c0750001080d507003003e1a07010381000030507010005101d145000e0103030b507a03490509400340b01080300c00500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 134815980 1250 134814730 134814733
    0x1d0a0b0d110406050114030402011b05010509070608060405070f030209040e0a2009190c0309020d1505010b0c0a23060a05040c0b0309060601030f0b10020f0f0c0d14070302040204030b0601080702 85
    0x38400b030b0581b0050440354802d90920301a007224070368680c20135501080a10240c01d42d8a807900b0001c29100008804040e9810f54440c407445e0b81c0c40100b080243e603001c075074003000a0702c0307810803910300d0740660003511035020001c0002c10070140c01d42c01036282580c804400e4441d00e503642c0b00d40282c4200460703070210301381068881314a10b15050858044070900c030500c10001c01c1d901c1403608c40c00b6119a200042940e03004103903030310103085800d040300e90a00c03040003400980d24000000400150b02c0080301e0b011100903024007840354140c0c0303620100444075100c0b02070a0145005141c8000c8041c801c480c899000d050000800c1e00f0281800c4200990541081080c0380c0104188000c1200000b00d03030368046024a07010400304100e180001c050440c444296801001d11101156001d801003680d484814840c411503049400381070702c1e0b6580322407030281c554211403405040000700700c01d54498041078030701c90304480c0b825507207078003007030072640143e0064640c682c0e8401031242c15a03001c10010741240d01c1c0d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 134817230 1250 134815980 134815997
    0x60602070501171509040b060f040501060c0b0426041a040e19150b1b1207080a030e060c0912010c1d040e0f06070f02071d0a0b0d1104060501 62
    0x82d20030300d010003055014100f0765001850501400c1608140040c0180406416081a2034003015600b0305459840c4507180b9031070610f5040c105449114100c03122540c4100307001d4000e0300e403081c211402900940d003007219003512089040e4203040a900a00b203000aa0399103920302910712040c50001610314907007200400c1b04001e01d00d0a84401c64004000901c0d81ca00f6075440d1b87c001009207400841e01091301603146000891041c0c1c2805800049498916088031122078898107071100d845811080d0183e400b40450008603550340054408441e06040c0043c0da0315488030003500e0140d08950820004200250381049414001c18000c41d4580681c0203200300c18110102404003030142c3c211641003034217180c840392641d82e182c102043c00c98103001594540031000c2411920380000b11441408502d10086229070a0310002d0a6802c4998001040c2c0d0a1100100c81c42c540d5000034100c40211a00c0701c11850040c1e44a1404182d19031040d10810041100c0005202c2516000c2c1d1149041c402e80d003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 134818480 1250 134817230 134817239
    0x703030207030b13031e0c061a01030f11070602160b0c0301150809070618030c0f050301110f030601081b0d06030308150d02040b01020307080f0418050712090302031c0f06060207 78
    0x381e2191408040003551000c142031010300b00c7c2c02d051900ca010b0b0405003440b1048080b9016034000c06c10400f000c0c0d82c01d00c480c00100171102e090b0307845094020300c0303e601013240070082000e81d4040c2c46e403010800341c6103101505a45802003c99401e5445040d20180000100304034405048115024040d44c14403003924a8038805140e00c8805038800d075401c3c007038400c2c048040b0340050070f04030000c1c640c4100d0500000340c940141e2049203100c0c3c010640039600e00344100c0009c20803241513540c40d501c20300da401e145a8031704004589180001c5e0201d281e2082e4000050644040341c0041c0204049181002035100e02d107003001807240002034403581014004201c0c0640507148c90509038403058040da00400c0100741540100c1c694440c940d07025005400214014246100110060084407450408500f010740042c1c008802c444054444e11b0100ea010b180f4109618841d0300701c140c5250090055a0810300c06040c00401d045070085040d52881e030390052419080303640d10490000e1b0500748010700c1c40f6400e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 134819730 1250 134818480 134818487
    0x200a02060f091f0204080d02030405040b040501080a0312110304050102090109090b060409020f040509090d1d060409090203010f0c0908011503080f0c0123040302010b0904120f110703030207030b1303 87
    0xf10494440303801034258110302d41001940481e001080560f0840e0032400d0f161000946a80150040c00c0c8030f070b030800740784960034501405128141c0d1300c1c0310007030154101d80740d50603141403615068860b441911400d21140601c05800690701c941d024200242c1d4440320640018101c3c41550040800340f464000301b18090303210001a5015590000d4005a4603895a8042580d03405203902180e807140b81102044000000490382000b03c44583d100c030780c10351982c4507071010082003004c81e19070080d60070301040200c2c181e1a0000644240041d000040d07400c20341c100c44080d0755a4102c182c0100f2504441002102c209106080c4036400f8000d091074083d0139540d901c0c1c064440d50462403840b0001080c1c900c01980c0a50011351069101c0450280400c007903440075400c21800c543c185c0240d440c001420800c2e0400069407845142d1003603c4201c1004483e5040c4c0d8002d11802442003003103008110a040b12604200c0c4102440c087d800400c00d8916526041794880c1d00200000c410720142045540000e40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 134820980 1250 134819730 134819743
    0xf05010806011401091203020d090e01051f11011103060a08060f2d010806040c0602160608070507020613080105160516080c151009110f0d200a02060f09 67
    0x1102c1c3d10880c1918880300100c544440c0c0745c2000e1641e00e80182c03001c08058000a4003101c88029840380c010640e90b501110500503024840d240e00400381041074500300c0c5000031051190161030074240c0c1011000c002c0036084419000003440301c0c941c00001d202052602e0701106000701210f0b40244030383c0ca0700386030111030301c034001d0280100a080c101e159092400424009030251083d9404a00c082d0b0391175180316130741c0b0019102074030303c84002400414400d01c04100600080e20482c8030200845c40e06004440443c2c1c005e0042040202c2889080010703524a00104030980000b0200d03000710b03007001d107100d00b160009007001341e244e408144103000568001d81643c0b10000c040c040d0543c880700f2828910901d01c607803003049a82c0c0c0994183c124106401c2a40140608079618101e00040e44031503c07401218104040b02e2800082440000040740d02d1070004c150140388604086001c9908940e28401030859000c1040060030101d01120003a80c10482d15a00c0090740345a580d00d0704086040d60307100d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 134822230 1250 134820980 134820989
    0x2160609120812040602131a160804090c03060302040b0405010e040803070c0f0609050105060609030307060b150a02150c040e01140d08180307150f11010f05010303120f0501080601 79
    0x240c024401505002110b02910210300010304030410a28091910500a501440f90b0041c54000a9804100100c03115012000d000040e096245400072912125195415542d81180e40100c2080f0100c0c40300018005c0c00c5154020752000700701141144104420340c0c60345403465001310b14140c0100855a2181d03110354201c0e40100d016a500c0d25040340803201504400c60107080902c200000b0802c005895001c040303018001c1c8001c200c0f0b40c48036070421000f03200301d4440640c90ba10a1142e500881c00b59841503802407001000c3e04d1021594003800315240d040080e2340f202581125001081e4008810b4405d58040c0c1d100b800c05140a00304800031060690602585180012003005400c890700e4030700140c00120380090200d074880d8551940001c0c640c074150340c40c40c000c0c0110301c40083c00f82c0400160071050007981e10703904501c4000a20840e4250346910b400c080d01d40d00c2d4002da520301002482aa4040e50096940d8609881410701c02002d550340f070307036025800710318110040000607808148281941c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 134823480 1250 134822230 134822249
    0x60f0402121203010b04170a11012a03020106060f02010213120f02041104140102011803032408060a0c050a02120f0403170414090103030c0b06130212040302160609 72
    0xc64101e41d40070700d01101030402c0b5040701000000440c2184000d406081142d580081d281c0740c000103804d0003520b880c014900200100c11010b424440380d809100c035120a10707403050142c0040607000141011450306198150f025035510074050003031035030102201c480340440d0300007546884000001d0305ca11140300d10800140582d504101002c200e0020520100740350001c0061003200c0070950500c0299029100d044085403500480381842e500600941c0c4050342075425410100640d03480c15005850350340d906000c140489800180c410785900064400f410f0020001e2050340303801742100c001c0760483c0700d0b07002c2400300030700503030003120360001d1060301c5040202010b90b15918403003071105444c0685d0300014401903400041c100d81300c100c2c4026104075003040b0f105105904400c0240b208411703007804040c00080400114a0101e01d4103e2125007002d03001e07003c25100941000740c0e00c1244c11404100001c1030400302800181a410001c000845d40c0c0c045135a60014a000809401082c1620804110 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 134824730 1250 134823480 134823499
    0x30804020105070c0509070237080901050f070c1e3203010204030615060c0c0b03060d02210706020607051b01060305010c09060801081f15050406081608060f0402 71
    0x2000700e4004c2e8800100030103844041e00d800c040304081d4031000f20508003075059502550381ba03101c00d40060f1110480840d600d0700c24801845807140030240c0d1158081505100040140020600444c002002000e0042508a03411402c140c2c4400000d21050341700015201c80300028086005213041e80385600e40302818403120300c1200d0b0840601000f501a5180d4994030228001040c00625000b00f41000c207030b01c100410242d1102c8050340d0300420468060030308100c054050091881c1100116000500107182c0710003d0210350024410f461700b01e00d0810a50340d40e025020b45000c04014040180426001611651a12000040c40c074014000c1803002c000c00d80c580502c41c031400707500ca9806190440000c3c0036851540b0b0001c4c0802d0110300c00c0b440000c41d042d00014030f520000c00c0d546c18004041d4114400e441464031110007604111781000001002a08001a103070b03500d20802d001046504007503c2449039060107444405025400901c0b5508424100304894176421085580143e044428140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 134825980 1250 134824730 134824733
    0x6090102010e0f0d140412030f14030406020a12111806070804080f210d050408192c0907080405070e010e10241407050303010b0a020f060403080402010507 68
    0x34204501000300b2a01882c445080150b002190303d030041d2215803240008040012a480c82601c01c51040d143c00359095a0130f100064400d502280e0401440d19010a4441c0034a402c60b106a00607101161065030000700c1030031403608440e03c10311410340d061080042045184c20955203109100d54040807101c1900c6d5103442c0d544407003da0320b200d9000703072000e038499840d4078409950b1400c00c040c0342210b00c2048c494481090007440102c00a4411507074540c00c000c4201400c03405003030050021a8915000d00c0b041401d181010000c12004006a640c060700d541059901c0210301521030b0140c81c011180d62010f20181c586c2c40001e50083d1052800000d1031361142881400d1600d6504020140c8008400024429001c004038070700915180c2480d00039199509418072201100007507509a00d1031b81c1402e80c2e01d2703501480a950402500c500600c0c44c04506541c4ca074190b600981054055401c0451a00c0f407181d8104060040225824000c08250030300d91000342c004a03004000a0421030300248000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 134827230 1250 134825980 134825983
    0xe040c140c0606040e06090a39030b0105040603021804050319020106030b0703020403110f0307050d060f050603030a0c060203130c120209090303150d05070308070311010506060405010e06090102 85
    0xd1030420034100440d01c4888802074a42c890a0070f50780d06200f20b042c1194100a80000f01d40c16010700120802400707082090781d03601d03400303103c00ca0000c01080f007454500c4002010f07100c010010b40090000b000d41650a5203496418114182c01c1203000f5442c208051005803a180c1000c0c036007110281c14454155180d00c0c00710b2641c0300d403010040c1d00304160055043c1c2d03980c05420201c140da1049800f20751a658040d8110b0803800307548000790101d80c4400503031800381807400b00e0729400709015041e00da100c0e0316000443c1c4281c6081c102201c4460382c03032030403a4514120303110705500040120051440d12540324801000303a00403000c0900386e07030b80c000081b40c12480b02140020416600c410210a04e44d50b4040b000c1e103010841006a000d1200500050320f104404411240f1842032042841e80710303c2c140c1c0900481c05549281203905200f000e0000c000b040624000e03020051007541e03000c0d1152040001c3c1400d40300003510260065200388012301440c1e810203c80c02d45804251051500c3e8079074280100d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 134828480 1250 134827230 134827247
    0x50c0a080906220e01090902010e010f02100203010b0c01060906050f10030b0d0803060913120c020a0914240105070b06061201080d02070f0e072d0504051002030304030e040c 76
    0xc0c06160303d1190760340c1d0111540e800784116026910807141c50781c0c0c0c071481d841c103035160007100030700099a0032030060481d0b020300d40701004c46090f441150007140c942a481c00881e0301c04e8210032440e40740414a00ba50322000d00641c00680302e001821700c25149042d0104070188070480f1400d1089800b0440d081120b071295216000f1804000d0421183c5c0642e0308049465500130380f01d41d40100391038070015200040e403002441e4295030014010903403404403a01210f50b1501b8a02c12640046040c500040901035030141c045100300621000c8507500b010107801c200003000c200b9401d200c00b100042200e880e83c1010646038060742080b000ca4581d501e8500292442c41001e071042150050a07001040788500081e13000201d190b541c08681d60356840c0c10041100600f84d02c264040780d40c0c031900003402070388116524901906403c021142040b440c01249481e60000300b424000194046000c0280d03290101d08803150191500145240d401d02e9200240005003007900f5034051034451040303012840c80780210 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 134829730 1250 134828480 134828497
    0xe1201020a1d1c02060f0d090c050306010e040b0a020912010219030e03070c0308070c030c0303080702060a18120e0a060309060e0f1b031504060912050c0a080906 71
    0x8654946003010090440c0e00a001d118a4040da62803656246040070402503041c01d03031500203038803080f02c15400c001d000e6004400300c0804110601628a04900b07038080c031048030b0720070381d040f200041c140402d141c43c241051384101c3c2641000f00a00c404690120240c61b0004404a40541c4c0c0b00703c1000482c3c550707004240c19803181e601c0080c0f500c0f01c2c03005000b5804841409651b01b40900d8050712200b69aa004068000e071018503400d0041002501140080203002c0c42600040780d070319607a89807070744041d920341e00c01d40108548608200f4000e5061224582c40400c22804102d241008000d1980e28540740e00c0040100800b403032541c1030580038901c141e4040d100206100c2c0c0e00c64803050024064204107000b04ea0b013a0501c001d040c0c85001c081800c2102030b4200004140c200d2100c07a5546202080c444d04c1c179014040e1402c01d00c480c1000f0b00703000348914020500420b52800c24030b0407010b00c21042100a0070010140540307201000003103443d01e041da8103c1030b80741d29640300400181c5c26100d42040d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 134830980 1250 134829730 134829733
    0x3281703010e09010c0f0f031a0d080406030b04140112030207080717100501050303121305010507110c01020f0303012310030e240a020d02070218010f05060c0d0e12 72
    0x244149950305043c46040044000c1c469100302d42c200307582c40c0181000010110300c1c810480c0f00d0b41c5129034489032214000e4080c0384007030403503480801c070b0300c495544055407805c000040511a060705802203414250302903c00b00210300c02d410400315000018051004040c84000d00303c011f1510070400000901900801d80f01c0c02d50341c65444090074150442406014003502c1003001c00a8028880c07941221005405146006542c136042140d000c001410a0408084032500341d0106409110741c17840b404403500c072085000c0e414200300b442e1000c0307882100c2c11540580400c261460002c0141c13411502c1494035201e5500d6001c140700c038513040f807001868000060000f043c5842d0b505800002005011100350b038040b4011314242d501c82005851985d0070340c45030602003201078500f54000c004400d402c001c018103003010341d40011307910f000000c001411414004010700c4a40810020350b0018282211000e141c40105144151100d801380090002d00c0340045d021203013030700d645c03000047c4140d9550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 134832230 1250 134830980 134830987
    0x30f0201080606071a010501020709110904020a1106040503030403080a0519020c0708010908030402180129040305010c0e09010f030201020a021e03030301090203040c06050403020616060b130506040b032817 90
    0x1151017500300824480c0500603c181c0c00c002a031040a440380851f8805501101132a115210003440003945c80620410104000712280d10000c00003413100a00aa01c01c8002e141d4900b080d00f002450000080c204459031458041840045640e01000007550341c040000075803107000c10002d05040100702d9010700c580b542084082000c02c00180c0003503218134401c441c4000150340320a041c2c0c5020030240a04c03440d034001440780a04850748040010481104021050720707260b1a079a600b800d40e0034074109000411508020750006181c041c00340d038090044060b640741d05514680000750b90b02001d00c5d01078003810380240002d41104e0300c1c038901c202400300902160760f2540d640d060203000b0341c011102a41c811210010106203070344200c00729400c0300d800030100b074149034407a21f010103200d0048004540499413075450804645501380c0c4414118509070380011070b45440014001a40c0c01600041c2c8a5046240e500000c01d240350041d00d403200c00e00d400004218401d01d08082212607412905076030320b4011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 134833480 1250 134832230 134832263
    0x6120507090c0807020604080705070f0e090f010e0a030509040f020f0a03050f04170a120e010b01080603010506090c0c01180807111008151306240504030f020108060607 74
    0x10035a04940400400b0007031014400411128124240c40c1800183c00000200e004540380e003011304803c50090090b92041a40d88401002440311a406016010071820401101c42d605000011a13200d04800900c202d080003000c0303c0e11641c5418006060010102d200000d0f51140c0d40310180d040300340c5070110740c1c7c4c07104481e01c56415040000303031000090510f400500e0a41da01101d0f20302a651181c0210b00c1080c0c46c0c00c4c00c00b500d400440c10001081944401844014510301501c9102c45081d0000034001581c0c100041c0188002804280242e0600c400e120307290b150305041540c40100101f1080d01c030750051100e01d0140000c016030b9803000c000c1c0040340060000c1c1d07800403c4014070400002030705d00004001c1c4040000c1c09040340b00455215000100f03400280c0e804903130f01e07070001040910843c0101705030700c0031611140c020b03518036040d0780303050f80700c100034016030086680031400c09a042c5855580c1c2c000c1390384c2842c80f00904200085c80814003130384444007603d110b01d91200d241d46401c05035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 134834730 1250 134833480 134833483
    0x1180803090d060207171e040608060d06092a080f0a1101110a210201091101031a18070e06070c0302040b1804110102120903030301030b060d05030307020c010f031b030b04061205 78
    0xc4039040043c00241f403510030a0300044801ca4048030041d4860300c20550b1030b003040152042c0c9100703040d00c120345c03162018000503100900321752600e100c2284081c40c0102d40400041ea81015801040080e40110b10303000703034104000f5594100541c001100c1002c1000500101d40030000049241e8030380c03080104180c100110031020005100e09400709074000582e0030b03c200d00344c5c1c00010b0041c1801c1500e480d40ca255512a40100c8042c214031001e0003100750403c000700381e9842c862562880c40e03201c45014458403541c060742201c02040704480650500b0084e8580501060701c52000070b1040e80c1d1500c80603920f49902004010702c0c0c11030000e201a900e0142040100341000c1c4100328014010f150b415600c042245068030071031a030240040d030440e8210b40d030b4110100000340100e41e00c5280748044c04002101003004510600b441c1d406841d10040850014001481e0306100d1003e1500701000c41501c1860345011008000d1940f4003c03440704c510f000418001c11140e00142d101019404282c010b1000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 134835980 1250 134834730 134834737
    0x705150a0b04060e040b0402040219021507031b03020c120c01020c1c091a12090304030b2503150f0b090306131a041502041401180803090d06020717 65
    0x10080c45001c110004200443d14103005100b110440304c80818045082200c00c541e02078130141005291507040140c010f803031900701c10030400591082800003401c200850324030b90081c0300d90505209807a0a440390300086a11845c0314410154042000b5020303400c00c00c00c40000601c2807266a684070707140c0101034081d5105506150082c421000c07000c1c000d800e81d254210341c42280e942c80400c00e170705240c42c00c0b80d00704001c111642e10000500006116041c00c1da04980504415401580d41e5840d5241c1401b030460000d10500314100e000140ca404459004030868940c446460005829440501d190880d442c181d08000070440e000341020500040800c01803c03910301c01c07011039a5943c0d489002604507031409000510419000c0d8510060202c2c00c000d4a0700070344540d00c0b47d1808081c107a200310483e04260f100a41e0018010b03204016541c004040809030103240700941401c03410107c0c0242c0d6440b80c002000d0007020714250311420b0041650585061950020280150725106c034074042281c0c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 134837230 1250 134835980 134835991
    0x18192715060810150e01020a05060a0b0a0e0f040618050a080a110c1309080412080403020405010b070b0403080705070b090708060c04060905060a0309060e01051b0403050c060a05070515 81
    0x2110740300420b030b015943d540114100e03890304d40003510b11000050111245402600c0c00350640c03091002d11000140148809403040403170b400001070b40c81c10301c2c0412401d00c405a10009020400c01c0502c0020402001025400303500084040317402d8083e25181c40c4e034a08c4500b005082401895000c0f010400d16a00401050081d540c5442c0d201d050150b1507600c0300e120801240d80700820340c184000900e015004080b01c9c03070041b00c00354100350b40c441100a1041621204960708400084e083c02181340c10f100d05230144c84090003c6082545a80e140260b428000e4006400d001002c800940c0e0130340304d0b104403100150300c150307801207500f429281c2d00c0e079805541c00340721f0550094500084c0116041015141142d409076031310b0115901d80350500503581e000780020381c201034541702070f040410440d005c0c1c0540405444000607140c07414614020032000c482c098010344100c200020008203400040301e84035840e0446e8036a54030f5000040584040c07084090041c05030041d0100008081c4440b001e240c841d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 134838480 1250 134837230 134837237
    0xa150309060b04110904110c06071e050304020f040905010216030512070206060607030e010c06020415030b0604080c0609040f0e070f06080408180103060e0c1819271506 74
    0x2e05080200000d440900462040454041c006020385203400c0e0001c04014510b140000c2c5428408092903060003422281d0b440410101e0380c41d43c1184443c150960540740c41417405500f1030070b0940c00113407141c102c0100e0354440ca40701ca0b021010f1000a41c100c0d00783d1452400301c1d400d0317030ba55850040c000e500100e04044000c080080010b101c1b03030022544601c100d8000b0450b6180030800e42d4252100141082454100302c00c00c002c0300005905480200050b201d00544880d440c50004001020b54000d24501801404244401c1283c5074000035569a001d0b42244c215440b4102400487c004019040076603100c5410300c4224815100c0c00b01d940c07001e0750740001300401c40071f494507026a0f44402c180c3c1d004040000c00c000c441075030b0248201441c4c02840501d0301092041d5200420411101c0903a4020b9140d080003a081c08000d000c000c503060109011785440310b0a40b400031700b105a90301c6900c05ca801c02480d08411441140c0303d12a111140d0300b0b507203020030040c1d520314548942c00c0018021100403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 134839730 1250 134838480 134838491
    0xb1306080f071a03090a02130219030603080a120b04020426010c0c0314130603020c0709090f170f030106030203011404090f02120304090501080609070b0c060c090a15030906 76
    0x12000210b2240c064a010354209201d80c116070180c99460f500003000000a03020f40c448110040e1317540341d5400107403401c03080c015844d48825001e041140f06090001b10502d46451030800c0020703102d6081d106001d00d0303030400f0120401d60030a81000b4086100700203501900c0020085000b5940c0b4036496070682102c03680d4910700020345e2080342200e00019000010910080300e850000307100e04070104815a240441900707003a1481d09040d061140e0350001c0f0082600401c81998695082009000030309100358140314421080e01d41c61b00010308960040c011009a0b80604005142d2900301c9180841150036503a5039a0740d0f00004009410078003c141803d406014400c002d0b1030a401018003098002c500032001c0000c5600300100c1c55090405140140400d200014200b80e031407203201d0082010102501030782c82c1408006080000503041410300c00c809208140038483c0000d4071302d03484480c1203001b6036110440000101d020f00c89612501030a103001490039041d03039040c1c2089080314070400043c0030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 134840980 1250 134839730 134839753
    0x504050a11270306100306050402010c0212010b03250902090f180a06050105190f030e010f060e01090606021b030c09040501020a030b03030a0e0d020d050f06041704060903060c030b130608 82
    0xb11141d06503060b041005d02c039031051010881769800b454001e48141812184403885a001c10340409441c5ca001503565902d019505007410140051541b50000c0c40500000c880b1a000d00220700165000b1800d40c1903005c50005031903107400302c81602d0f0241c010000001c022243c080100024070445214424a08114002505502483c141c880c001159581020300c15104581140c0c1c011140c4001c1d0200342e00d4101514820340207100700303046a0138007440890020b042500d40100c0c0b01040e4402c001c0360745090300400105a0200e400c00207100300000c840741070905c041c000303481c1c08a40540140d01c2240c01050004010707055000700b1160090b51400c0c07282940407810151a03004107589800800c0041801e0301d03041ca0003000304555507100615503456241140c07240ea20301a51f403500c1803030540c4000c2c240024054107100500080030740c0c206491502d0b00b862401040d412151000520481c2c84180d034400d1940a5008950003400150000c540010b9495911019007403503c07940805000700035107501e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 134842230 1250 134840980 134840983
    0x110a051207090e030307050a0e0d0213090303050c0a02061f0e07031b0f0e04180609050f2a090402040e060c0a09050901050d080f0d060605030a0e01090b010504050a112703 75
    0x6d01c200c0c81501c1d220704081941c0410384d00001243c2c00e003680104005501300042c1d40e0316061602d01040c04200017042841454040c04031040501142c124030001d101c0451410380c00500544c0c00744142003907184100300b2150b054544482900000c01c0300d80044100071f80700d82e1650000620011003004243d205212120550f000c09480c440b0700c0010340c4010344903130582000d070401500d0716070b43e0404600e04d002944510003240c071f0740a011107854012840c0300203035500402415400707060500c100800c1f01e401219410350140100003183c09451280009020b55499900c010350007403103503056440903d046d51404420b40d10546100003c01e05003400442c26050090f403940c1a240054102c0220310600c1d04c4606054100c01c0f0340a048103020080e240180f19540502d10081c030300c0e80c40e056200c0c14a41c4248080e114800c00c0130407140e140030138800c046041001c42504440080c0c0d4001a41d4a8103d500d01c06804140019508400006180c00000c80340c080700c00202e07100480000c6040c0d000f0313010035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 134843480 1250 134842230 134842237
    0x30c0c011e080714090a090207060b0a080304060c11090f06130e0601050d230c130c02060601210e03090a060f080c090303040e040305130609080307110a051207090e03 73
    0x141c00119401d000601483c040c031003401210001c0f1a21034101034019000400440207900112171154000c00e00900b04070301030090882400049404e8003c09040112103075580c0030f948203020812200c901f500381070060700c180782410600c0140003641d5030f24084400d401c2c0303d4015101c6c68040e016005100d0301c290038600c21854482e0288000e03141a900c0d1030308209008413004c80540d005031042c205900e0103047c40307585400d48400e00c00942148601036017045052040784c0c4550358600c0c180700081404a03400711754945e101e50b007401c0c18602c81000d810700c1c4488901c0880071108092602c080f003212030000102a044241007100c51001c000e48410088a010040000b410701142d151404a529160f002003d00358400307018017140e0600703503101100342c241c1c10165029000720300b00050707841140c4510750540d405480305080ca03210980c03628214603641e00c64544050445001805004800d40d90f080f07441e0300a003001002c0104103100c1c110340d16150340c1c46120741c82d61507140c0175201c96106800b0069 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 134844730 1250 134843480 134843537
    0x105060a0f0c02030f010c09091a0906061b060c0706050a060509040f030203070c0e01140f0102030406030905070302030a0b180604081e09030d0504050a050a030f14030c030c0c01 78
    0x9501c03038241403510645169842000883c1e060140c60148881c4203002d20501a0720482d60391480e80c1540391011f1101100d9084485894019180e00982c4594813900000c9070040340c103413441907542c00c1c0d0380c500ea00007504095200146025180500280f00540c401811003075009000421940c1c50e865104070445150744241a0004c0300c460004001c40c00b100b1060007141d0090058900c0d2001507541c1051109040c1c00040441400000600c214140303c46042c1c00c80c101900c3c820901400040041d540e0b0149100e82d004160b00d031040c94041082c1070040b02e00440e405822223021014614204c9c0c04200c00300c40c5408440c9030340e061140c0b0500006040c0c3e001c0c03908600785524068150300110a01403001480001203801002011001c8c2c5080000b81d00d1b0710344c25070710b40d41c5517070501c030070441443c0041e48480d1040e60910420710110310011303450141194041308140000020024072070650068000466590101081343c0b001002e01003841d0702d41101c266100601e80382041c21441207600c00700d06 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 134845980 1250 134844730 134844737
    0x9070b030f0408070807050312070906022118030f0105060415060801090504020103021b07090e0304080715032009040b0a1409040c0503070f030c080304050d08071b1d0105060a 77
    0x814045a0f080005081c0d040c02200d50500d002e9280d01ca85246500a01044a00c1c5840d00100009079a204c00094050103480c07020b82508042c84000e103008901e100d00088200c0700005000c208370802240d00e01d0150809016a0080715500c56440d000340003c5807400c1c021400e00742e010203c040e80111000942e052511040c00070390030b12541e03600501008004130b05050f401c01c058910300083c8440392128060303440c020f0aa460034002c1442c15603e000985030a036500c00c0c0004d00c8040c8020400c401a12444220501200b070a04001c038003403c101c60050b403001400c8a08883d00b41c1818000301006001a1028401014090305101c0e0010040c820691b0803030310090503030031070725060302c04c1c03900075002d441580d00a41d00c0b4000642402d130303194003000300e001c0c41c1c50041081043e00c1403003000801d130300030186040c640703040c0108503a40a07420008203907880014103001041180c0380c14820500b184c11401c816030340c07601c640804c00e445185591000d00031500000410346806004c64000340f915a6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 134847230 1250 134845980 134846011
    0x60905070c0210051e030f070212091503091606020a1a1b09030c090109020a080a09080912120d09021c02150a1e090e0f010302010c0b070509030d020609070b03 70
    0x30081300c3c0c40d044076202c510541d0590034070605441e0b00c10042c41c052140880b00c1303070040c1050803000e450b000602c1c00c1c040c2d06040c20f0004400d180c0d030300c444070b00f409101c0340c2c8034035520303556000300c1420070042076143c0705a001c0001010902c641c0c0007850b0303406144a0a00503810580300045102090350403100700ca690314901051641424070840604030500e170103000c450100305481c0000740fa90000b40c000e581e02d80d41c00306041e00c4641e404061030b80c010b24242c0041040c50710702c1d04d42900c80c0c030501d46518061400140c034070300b04000402c0013402014504040e01d86407151030f111031000c0e0606040a901c10907420745101045c849900c0f510040550040000c0d40304d0b4180e102e80002600a4840348080c040c030802c04a54062188100000e49d0001e42d490a1049041c49540032886070064030503202000408014030060f40c01c43c901c099587d41280300ca048035581d240b4200c0e228031440c41402e82501408a588040540005140740038026000542e480a52240e8103508d01c0d000031240034903940b4228 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 134848480 1250 134847230 134847259
    0x507140c03031501031d010c090902040b0306010e030307050a0503040510030219030e1006091b0203192f0a05120a0905040506040b06040f0e0c030402010c02010e060c07060201060905070c02 83
    0x4080c2505583c42c181008190f030900169507005100303003040c200210783d45600001c010a0703800081c4d507000d407141d10801c5003401e040003500d00503400010155414002420304154080d9410400e490402e9030000c1110005101843d010351682c20510a95008000700c1c014002028000e0003540c2e644441102900c101d0b01000c0d00c100e01803c150b40b00d010305401290306084504403113000e01c5010b0901c0400106003003000d010010842ca0903404440115001402a9000742500700d4885039080d15038030301480c10740d102d00781e02d281d002000d142120f200740f41d0301c03d83c183c503080114034001094050030940720402c245176400306242c81605241400030700040402e01c840c0ca0f00b90300498101802500c0003030141900700200da91785d80142c0200b54118442001003003603607080d004c141d9003c00400d80712411800c0a90001e89a4100c2849c000d0503c40d18007410021516002c00b0703500c41c2002c20048641c1d656a41d071020b402000700c1e003c0d40c0f8090342031134000380e0030714001c0342513044030b5a0240c806841c41115 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 134849730 1250 134848480 134848501
    0x1206060c3201021314030601060309020414071106090d0504180b030708031305040903080c090f0415031e030206010b1308011505090f090c010c060b03060a0507140c0303 74
    0x180006000300300181c8420112100c8594000840251074800050b80c440f036000d0121a001c0d150740c018086102c40310070000309502e02048660440f82c941c00c1c0810b03101c801d03100080241c40c500810403800100c05040102c0300f0350158001d06062400c4060310600e032940c1403440d8594044200040100e4030402041040001d0f028025400e04100440000e4120b404070002c6d041440d6648101440d81c00460503807041c01c03010b0008001407a0440781001000c0880d44d0103454198020580c403003605010030401d00039201c095a54083c040005c20400c0940036040310080c1e4080c03940010386a0001811100d04501c2c981c0fa90806900d405800900340c60303190507200c101e50381c050400913411400d04000040d03c4482400b51135014078030721640c00c164a042c4801d11066850003003104852944200600160010118a81542034420310740003440c0715840c00c3c09005440e4548070650148120001c00181d0388030366100300c2c060f07102e070359a54180b44480c2c01040502d0007802d00d89080b5400030000b0a806069 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 134850980 1250 134849730 134849753
    0xe121b040605040c020303040b010f12020409020402091008010f05090f040b04030908070b0301091103130b07021501031a0708150d0c0504090b0711030f07081b0a080702011206060c 79
    0x401000030800076280c00108040c1e41c80f8080c0a13002d40d01c0072043c8820801b208881d00d024010408812801603c0c00003d000c00c0c10100710080e0080f80d80e5800082551590b4044a1080b800940702121070007140c04000d000160074410382d44601100c02c008112803030b1400003031f401803c13418500609074882e81c0352101d104078050700450510101400c00111750700b06000c11401012a110714a44a40c54041e0780001d030b40c1500a00d1411160400400040050741110502c03c150011003c01c030503594030741c050b41f07801400f521030460300c10980d000004004400c860964040c205000c600240c0e111583c040d0344150054650000044036494941d056007880311242400c5402004100c00c0241e9600c081401c460f1504000d0782c1740380040b13080002664019400d0b0f08402d041900462802001d2082035156010b802e00091a5901c006442040a1021340e850121100c0c9041903c00c1c00b00c0301e161011580d44104c0e001c9001c2818800c15001c072310704038810b040440d45203450715a4420760300e5036195031540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 134852230 1250 134850980 134851033
    0x12020d050d0f02040e01030f0303060f0302030d0309050115090f0f0c08010e071b0f1b052809020a0c1109010e01060e0415150801051e060304030509030d0e010e12 71
    0x60f070070300c00011341c80308011201c0c1c02980101d0181b1031030b078a10304008003079070010b802c10649128485410001602c0000305030503030300b5003480c0009600c00a444e2150240031440982c0ca00040300d11804210100c1a500452408450000c20084242c5860a50042d1110a602500450482401041a07484070b528080d03214003c1e1411440c8482c08c07070781820044107038000517030740004061165801c120780d29003070b6282407805126002d40c1300c1ca401d001a59490320300300000211445150222810111062600d000d402021000d5483d0365090100404000c3d07510300580b115401d00c1c18460350360901d844014162107000c20040d4aa0703007007072000d0726210503507172050390030580d104100084079400d210120041c100142e0f004000d0742021800920301a41a00103620410350180c0d2203081032064120012441d4040e94000e450317548a0409682d10b002e007040d055050700584444100d01c42e80b28076004807242c42600c4000c107141040060051021492002c91030316486800800381242c290081c210601 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 134853480 1250 134852230 134852261
    0x11a090610091203170f1504020c0a0c06030219090302011403070c0c030c1823040201120c02030a1d0307051e040f02090f090f01051507051912020d050d 67
    0x15554480320100030740040d03c250001000d000c1550812200c03180c1c1190040d81c1c0401c49130050401011920581c442c070083d1510481d800600c00322100000e000208205070841010740740c4c01d5036100003401031b502829143c0c5c0305407a4000f0b4164800d0107080388400743c81d01a5200451b6843da00500140ca03030001c0d01000c188198800d480c40003d00e130102da00041c6200d40c0c00004090315003545a44035482d600b0010071a54202000c04114a0021801a00d540707105c601c3c004041e1901d00041e0390340f000521000a0302414401d00c80200c40d0008010301178580c030b41c0d032030005005604030001e802c1c000e001a4640e00d500a443d0421682c500030111304c0b104500480f159002680c404001403c5810304103901c040960082a03150759890503000400c00c0c81426034151800b0700d0a03034800d82100031305002d103c0c0b0a4070440d240d99844403a1400f0f07207050991000071515550400010300101040018048034041c01080b0242c68051020900050595190311224140324180001d50003910940c030705000d00c3c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 134854730 1250 134853480 134853497
    0x304030504051c060605030d05071101140a05120106050a020d0e040e0d030b1903080304031d0a06110606060f0d051e0c03040311032511190503011a090610 68
    0x190f640f000310702103000c2c0c0518440d034022100e03031900700706440780c5510061083c5c100b000840e40c010381090071900141d0780400107200b081014801621900142d41c0700321401e01d000310f012014145c0250080c00452405500c2042503a654041141d0700d22030584004016000a100760703a82c40d0090520520107200200086200300c2c41e602c03041e00e003002d60440180020303103031604508241014803200c910041144004c2c1030940c15a10f4650040c440980010208201d0344940500044542d0100c04924001132500d146d480d5100d100403c5491030600c102c1881c068a00422050301d0300c07804440800c00400d0005007441c00305c1c074003080208401002d9420118011100084039207240146511403105000850f0f16810107040003082d00881c81d814002c598001c0201e07810700c8001081495041650182c3c018021545181c00c800700f00451042c40d800a000101c4035501e1003201c0000c0094440950080024801055412020f180120021904146200045195801c03d03201c1c8418000050418115 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 134855980 1250 134854730 134854739
    0x1140705210a080a05130b07090e0f0105010807030b030d0c02030307060c180803120115051603201501050105070f0507080c0406171e0c030f0a0203070512030306060304030504 77
    0x8414a00035034444500005142d02c5081c0c0061485402c41e002980400c80b03454202d200c0c0d503003031100042c0544041280400034030040d1240b18424041c0c03242003554001030902014181500300f007801480e000c07588810014601c1d510030720821924000040c010022815408410b482000031079174141d80500081041c0d00105845001c0c0e045114015540d50350130914804018110303203000d0b006550b190304100726140d01c4501c0c0c804040d044d20000342d0311345613009400300113441622448030351601503d4842c00c100103040c0c1020703200d0a15100900110040c45c001c0c1d041c5038407142d112080d00511303210b1200601843d482940541650f52003015404001d14640c0c45091510015900c07240e110f03805501034110364107050296400528003502d12408019001003450f8413484221041d003486000301c10003400034a400c2016032510400901920740802403880c40540b1040060340c140c0c042d224620002400e0b0800d885101c80400c0d50344050350964841100304045644094000d50070000e00380000304c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 134857230 1250 134855980 134856013
    0x1b0d060518010e010f08060703020f19030b0108070c150b19030c14090903030a0c05040f030602031e061503040303060905070203090307060203090d020d020a09020304140f01020901140705 82
    0x407400d440c003000340034150314280b103420052405030403030b643d07000649604001d60760001401c1c03904072102e4140941c907130442048100391800303000880f8803200b104490030900d060309603203c0990442e080e40c80c0400e42d03450b801c0668420300481d000429180d8040c0d0359030b01c650100d610540c5610002011110001c0300c081d03200200d00180d801c01e84c2c0048040d032080100c0001c0c100804040402507031901818986403450a40300e0000410032040e6070b0701c507448507207128840c02c110303000380c00c1075200f40500907200c0c10404000e410450340004000c12900303d492101d0320021049102c1e000040070b81528044030704541d42d4540000c0d00442c14103032200c02c04221030349180a0b1920031042c2d640211b8030340504104061404207507038000001d41d001002080130301c0c2c8904500c0010a6010f6503058941d052510208090035031560121407158404030502c0304100f92103400203041100d000880e02c008159011803404c1307200f22101d680c08101d1282c40d1400550b02d51014116490082041d01c909654525092 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 134858480 1250 134857230 134857249
    0x70c03120212100801050106030c0f030c0905040c0905010206100b0406120605090c0307031404021e030a080d050106020708070f14040b030a060516090305031b07150c0b0c031b0d0605 80
    0x6003028850f103600b801009402d200b17582c010482440c00384103009010402078900503090001c0c104040d01c46001461660050700a00b00070b00002e441007100c040d40d10350080002e40b850140d280180600804100d1000d50000d030042651102102546864501b100070380e00c20001020b906000e5464103400102031380c0714501a40300f02410381566942c0d140c01003004003160500d1029142c1a1160024000076841b10f460141e40f0890403402401d0f2100c41c400040e14000441100401031503001503600115980358022a040381d4054084480325078840350000d80300d00c81401008181ca1281000304400e00e0003622013818140098000210301e400308020074140840480180c3d550343c0ca80c410300c4484101a0607068404070303580381190389141169a910749038441c645005605031440348201f00210814809000240300d120003201b10038521450140108a10040550b10280c0030f0000440d8460403004072817082c0941188a00d4050481c135500c00b00307802c285820b080c0ca681d600408183d544519046 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 134859730 1250 134858480 134858491
    0x901140c0102031b121801020d020c070512030a1b0201111b090c18062a10140f1f081b0901090608060403030e011401030602070b010509070c03120212 66
    0x150340c81c5400c1c070000c449007101010004c0000c101704000503000c0c920280e100d0700f00b46d182c0740d0001d07416074003407038640a400b0740d40c0740c1907000c1d00c00504031000f440c002a040045400c1590002c98913100c1c0900f240d1240241c01000c00413440c2950ba0461640c80e026240c800d8071310505121030f60100e0348055910b030200080c40209502c01c0c0d0f18075448280740c60144294044ca00c5c110403880e2007a00c0c5021035460381c41c2103800d40540c101080038402020444074115a04000e4110303400030703008000d1560355a0a08d1903401c6003003403070040124039250728042a2403003a040c110001d08240c0324000c0499a1848560101c03110b00d10814011070010400e011a01000c50300c46004c0c1a044d08180c10040e0300ea0701030f0700c896041850081c0401c0741c1e000208800354030540608001030010840009c0324090305ca42e0301001900e1270707840e002004004455019103582800744032050150f81e02d61062204048056807298041507000d00482c0001c1d1094004490080322640017508104095400f13000c030a6081c0d50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 134860980 1250 134859730 134859733
    0xa030b010b1215030709180f1a090307020f0f011205010f0609210f0602040905180615010504090914100e1903051902011404080a0f0203090a0b0901140c 67
    0x8410400c2c0480540c1d0a821032521403c1200070b08454001039520406440744421b25900d5180c80e1001c981220182c0401c05d07007240d00c030781700c80141d0b03c0c088401082e1200d0b80100000400d0100306580d40020a0390045c0742d02414407600600400c0400401c081b41c030000d0347c108000b0340c8004885050768010207000700036540415031042e00b0000701800d40032458008100c1136028003504e124856240318030700c00c01500422000c1c6913013154107069000c0d120f80c0e08000b00150420702813007040002c0074484081c9022135410303100d0759103660640c1e0140c105550005070000b00c00740014008424981e0104081901c200345000e000060410748a04001c9415110f4017544c3c0c0d41d003000041300070144016040d000c01200c0000799486995030150150040c0e41074a00c0c4945075110340c85416000b58002d901411210382200c510389410315000b00982c0c0104003a40000c0c101901d001d00d11400007040e00da003410001c01c08100b2a0425a1440c00b6401c00c40e9a18100214a0aa0340b000308840d8010000101c5030780 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 134862230 1250 134860980 134860987
    0x606060306060e040203220f0503070516050d0203100f02090901030f0201030c020601081b131503020a15020c0d02150c03040303020c061c0b151c0f050702060f060a030b010b 76
    0x24003a00103407607000e001c4d002e0750040042180c280300303141c0b01c000404180c02040c0b0410225040107058112a0b42008000b480000b031410144840007030040500c2070041905c5000c4c54640c001c0c0201e28023b094002d4040d4043c2041e0b203418265031b0460124140c1141d0300500b00420340b40010280c241c00c1e882940c1c045058948513040d0759150044449496140c0014280365141003403250b0b0791035a030641107241c940c03d01403110807640c540344284c403840c01e240018042c94655412107100b805d02884108c0c45400c003a8400210003540c1c0c101012640c071243c02602d80125480180b00c00302c405070700304030781c0450b214a2406064a422000c1c01101409000450300e850451030042d00c1c00e4180080130b44107500034002d89003440c15800c4441a0101029004112045500e0114400c0c21101710601c8400c03c001c07940009403c82c40d1911041c41001c2c031022300071942204c1d103c030101c1e503081e6180f4005800c101c001803900041d0182c0603400c10805820410345030303503e40b100c4103940001e8104410910000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 134863480 1250 134862230 134862239
    0xf020a030f0c0203160f1b060201050709060305060a09020f0c0d080403030606031107020d060f240e130212150705030708060910170304030807060b09010b0910030e01090606060306 79
    0x61103104040c4003180015032600c111700c2c1d410b81d490034070140c0091148400070b00705010000861745421482c50031003402460340792103c0019028007421111100009d64101002641c9031090282034014040900044078183c281141d0201a5202e20000c0105920421510030000c50402c00c2007508546a81d13558494102490020282c46490340201c04150518954900384c0c444102214003903541111480ca408200707280c80009441ca004244440900e001400030080708013060180000407089211a5503d44a400b10300c0141c03026120801200500c0c030a081c014100302c118000104150421204003800850000b60000e1088401800090020050142036034000d0f40319900100210360300c1405152a40801c0c80000c154402d1941009440040300c0106005100721405180c00c041125519484d41c20540c0191a000c1f100ca8040d40624000140f07625802055600464001717000318013405180004502401407010b020409540e1000380d071000840b00e02c110001003043d46ca000c1202c6240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 134864730 1250 134863480 134863511
    0xd05040303080a02040602070b070302160602030408012003060105160818040612050a080d0e0604080c0c0121020306011704060504050106092a020708150610030612150f020a03 77
    0x7505040c5284c0c0140401d120381a0046907090079a100901d903540c6940701800e00f01d141001210704d840401c03244001c04201e81e03038080700400a554040c0003e000941088004a41e40c035802101d200e05100c041c000b06905601c220020210f00411040ca5084a00320347c0710300c0c0607584a410040c1da1032150035480416420310f4014140104218100c20003801140d444160304c44642c503c00800103c40080c50076800c0c1030a41c4100d040455030000c85607146000e24004076240c0c003c881c04103040c407030b40c8041d204540c0f0407650300501e0045403403903100ca040401440800b80d0000b5080303e0500080710364507d56501035140d118880e600a040c0415113060a007001400c4600c02d8001d1001242881c8030101102c1c03a9501d485031280c2d00050901c008440103a040b403e103212900a8030003805049510703c1c4401200200a00502c0201c031320002c24000b224081c2c0c00c0751401d12403000450500e00151010480d5040f000046041a52000c0750030712204c0d0462040340e00c107290318030100e59240352b1144013030903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 134865980 1250 134864730 134864747
    0xe18060901060f06091409042102032101050d0b10050d031d060310121403030f010608070c0222060b0c0708060f15061615050609090d0816110d05040303 67
    0x20603040c20f62941d1b007080d05980024400542e118064002c140216080220030311030860604026180e00d0740658900c0f00081d140d501034000c0510409240481070803a0000303818090403248014074445281c03500d0f0341c41285058000344500f69409030b0000005045d25440150703040d0f20b10a6032182c20000501c003006520b072003031110441c003541d000e2003040f11603442030343c03083c0613949c568443c43d500328074038600b020f59014100b43c0c01030750f80070200600c0700e202c0c00000c0e0303c0d060310929102d0f43ca40e50364100c400c90741035070301c400e01070760100800384510103040c4119041910b600a00310040343c01901c81c4000340c0b15a11100c44040242d000f15010003100704140000350701710003100300448943c00c024444000001b21624803a00c80da80024080c800b000f80c43d40c80d024640d41c40341c0c050744218031307141c211700003000100c1d009805003080300c0c0040ca480350082441564415244c03601440ca13259084011070044010108806202c071119409080e25030070402c0180045055940c5940d80c1e00b1407900819921 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 134867230 1250 134865980 134865989
    0x80d0c02010c020d0c0f0807080306031e03190e0901081c0306051005032d04170a08040b060f0405010e060406080307030504140406030813030b070e01090e18060901060f 74
    0x240740080d002d030b48540c0480c2d40711101200d40740c03803000c5807618200901c9050001500400e8090001005000c0054a0b0091441008200c040c0d9400a00c002e913480070060b2035241e5464103810402c0049000250340b0411f05801460f80340452049282c5000b15117401c1080e040032045500107214040d0130fa8400e584030140504500d021700c045403801012440503074910184401b4054080001130880048414407035441c4500c40c6440c0e900b80121001d8000700e034054406803503c9010140c030700c03d0380070356204582c101c1307516540c0c64090395110340720500782d0368010340515480050300f0300b40780d0541d030346028450280400d420b18005a050210810003100d8113540400708941052020b00003107a0001c050701c01f15203100b4a5015040b500d00300003001052a504000e00d1400045804140c103411100d40d101524450200344840362146d81040d03500480e242c4440740010401e810a020b404003c89456030060300d0f00c014080750701d685501c0320307003050800c0381c0001e000da40d107003400c103c0b03400b00032a05002071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 134868480 1250 134867230 134867233
    0xd0f021206030f010c08060915030703080a02060a180b0c09040f0b030105060a0302150d02090d0605060a090b06071e050105090f0c01080408030705130b0a05130902030601050415020f0a080d0c02 85
    0x404094174007920f00e0f003004240900c100c41c1075001070b1000c52032500c401c0d040034005040d0f4031110b0b00ca1030001d070386410040c49040148100c80000308101c015215558030302c080e44080c400c4484082d0789401c10810010050300c500c0384184000840d507100c5010343d503115040d0850224248098400341030844800034002c0e407042448650800140c1c40d031040d001c400201c100f21040c1d036401230142c624042e21949900c0340d00070312100400c0b0180401540708500038103003119401d5280303030b4502c507400c2901c00608200350300c03801c00c0000e140051142c5242020070440070040c0d160a8425444003401c44900312828100d42e04082c0075584000d00c2400000d85d031070760900b4024840c1c10180c0f00d00c043c0d80001807044060020003d1420f0b030075080c040e5800d0003845c00303210b1140c0d281d140040050554200070041c1c442010258804203010317400303000f1f881c45102c040e034604d41800d182c807511046151121410009600402000b00c0c0e040f03d00b40044500c0c14000d0304a9903407005451100c5045511480503034045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 134869730 1250 134868480 134868491
    0x1205011401050d120e0607060e0115030809040915050108030405030601150206010e04030c0210020c040b04020c0d030506151207120203040210050a1202180307170a0204020d0f021206030f01 83
    0xa5a4140000000540040c04c54101d10311140050307604d1101004080d030b021301c0118481c02009202e4121200d4030701c0351002070202c0300c450092010044014000188506400d10100b80d0381d040940c4000503060181179100c5105072013241c0401161000c2e080902a0b4100050034040c90404101190040c040d068560105000d0346100039290001801034826540c41c500c0400c0602d84244043c2101e5600102003a103124994031001c2c1da24100e81009500840c2424019195407a007842034905540d0b034140503141c00300d442d03602100100b100a022550000410440c410041e201d00003812a07403400c6c2d140403109092000d006003080c103c41380c0010310140100308000058031000202c655034185424215110403c610050768034198070a0301031502840401c0c2c003107100400c16142d01c00880194151614140c4030319200c2000340c28821003081980c040e107c0305006081583c024800d080294600082c0d01201e80b076803809980c441c40e081e03d010307040303602884898030341030080c0c07400c41180d803008226 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 134870980 1250 134869730 134869739
    0x507051503011a07051f0510050d0809030106120b1509131101050c01090b0415020c0d0813060e1b0603061c05030c0f0607090b0f0403110a03020a1205011401 69
    0x69074441401481818200000b0106241c1c0e4071406540075264008107a600e091070382e90340c42544c041050b50b0b00d1009424140410350400c0c0c086001402d075000608003100c3c3c0051900c82d100c960348008000f0f6059907039038000181c01300c0c603440c162078058441d5400040e030b4200444d00780044407001022500c40c1003032000703221a900000d245181c01d25070005204004c3c0d4040401a11b1501030180480181d50805492901b0005092a0648102c0c8a00f815614122516202008038080d047c0c040d1800c1e4003900e4a10a46030040c20802c0d40b000600300411806403450340c0700010707507c2d8002c42e00c0e0035510a13000110350282e2012000e2240c4408d503000c03030540c03030144002050f055049280701d5001814900e01414801c0900c12a003100d00c1300320499030803580e030204c1990340c0e0100b10b510800040d040b11010810580c410200da0b102044918050b040904640f50b25a8001d00140c2095000350b503a1000001a103541c03003a14010014022201c4001d00681400d07401e68206d441c0e580c0740c000c1c00c00c00510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 134872230 1250 134870980 134871019
    0x1050105090607062a091e140904050a0602210c07110108040c0810020901020c03160605070c03020a03050a150212040b130b0907170a230a05010504061505040e100f020f04080a050705 80
    0x101c08d10044800da809500c1c1d07400c010707044c8404c8003806080346000041007003086404c414010340c000030702d82d0105c5240c4d031006140e5246003e0440c005000305203100d00c101c003543c49103220581040c00781d058103150380c1c0c0d02c40d240d41c50203e60714170007c02c050300401e10340c0b51503805004c5d20140e21402c0d00640a03035403180082c1d611104250240609011020a1040070702407082c0345030024690240803a48a036849090840c1e690400500842d08121107600305000d0325680d000740c2d011203160180c4c003401d9480310358500c5805400104541c4040a40c20025008200d905180314080d40350807000d09120380c02c202256691070840d18041d03e00e0361040c0c20100c009034007501d462140040303103412130980c8a1000755060900c8544c5401402e1503083c0401d1009001c6164000300d0030b60242600c02400c075640b1010712096541d00b900c0b604044d0001c2c21086251400e64102840500070207500503c0c000c0d0080c49100c445c0c2089e04040031680c000c1e103c0100304101000b403d0050302044412a103090001c95018 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 134873480 1250 134872230 134872259
    0x70b0a110702130c050409020c030c06010b041202150c011506081810020c010608060705130f0608150109081b04060905060310020702040212010608060901050105090607062a091e 78
    0x40f00f000741e66002c0102424424402e490107080324010655450904044e0f442e40c940185036100304c10700581000003110303103401c4100e42c01c07510b000c10340f00c40c42d000d41e03020400f117081408400c9840013820820542c05402c00e100c4d0490006910007815016400c00784010a001001440294002441003060305000760000d64243d180081c120096554070100c0744060150007141e00c0b21201d84664003d01030419004009000c50300707c2c24510030116a41d428083c0c030a0b024620076000070448107004108003c40b50429455199010b0400b0031100b9520b40304030745040103020f0406826000c5a01c202d82c5d42ca040e00442d0000c0038116018081e90034000300080d1034903c28035840d0781041d4006285000c43d1526010b480440c0950a60880e0325030f9100f801515200d0201c52003032150041c4800842e03558003840644104403009400d250500d00030743c1c2c41c0001130807075040e00340c07100c010f000b40081c041a0002d045010030301c96079162802249880c00c50109602300089000c0842072000d42440300c0e410240e4035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 134874730 1250 134873480 134873509
    0xc07020d02190f0e0606040e04030f09030804060314090319121517371703040302010207030f09360606050408070e010e06061e070b0a110702 62
    0x30328051201610000c0c24200c8641c00c621800810702c000010b0202c148034241007284c5121486100035901c000030003800e80304500401c1e000080e43d50204001c0380c8180e11a14280c0c0e12030400700c400d07036100d480e084070f241c2140d0b01000000b03841d250000d51140d6842c107900e410101c1c00d402113040422041c040314044a000314000100a55554803401054058104030101c49800c0111403500b030b216245480386424111031007a052007000307200015040c0801c521480c103156400150080404500340000c05144580142d0781000d40031440088803034a24000c500a520a0700010b80e60301c12450082d01d92902c401410041c03020f1946d0070084c4c0c0200f01c0780b84502c0040e82c050208a20030705200c01c51040b030180021106503141610120b19660450010002e981c0c0c40000c40e000c2ca9130300c4091445009090040d0030b10394a4100100388141814009002c0c00c0720520018030748000b071a101144150040d801c207440c1c0d80c00d010240304540a440c814803107a00b418020b480c0c130340203642d0080344130380d07185181 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 134875980 1250 134874730 134874739
    0x9010305040305120109090b061801060809010b1f0e0904080306220c02070f1a090d050a020d0303050a0c03020a05091e15030406050606040503070e06060409110a0206010501080c0702 80
    0x303001c15203d0307811120f50f42607010900d000e07541c48086450040001500490b0780244280105101d40703000100455809070641c01d00b0416800c0040c120f822502c05480045c0139034903440b080d141c07903603441031000c1403051b2540d604c0070b14100c441d0f004280015030751185000300207040c2400003003411801241c0d480002a1034200300400350b1183d945026540b091002c44562908800ca00c0c2281e001c01e500f01151000b00d00c80b5051a194403603c0d01246d03003203906560840c4104860b900600b08840301212150184003624035054454021440800a6441c1200000d0f40d5804200c00ea940c903108034101c2c00301c54641181040502d90018000c0d10900c4032162188464401801f05106800c1d024881d81e5409800e0a25206840b010040f250b00250707011101c03241001e000402900b400d00c1541d04494005000b40102407410a0b112103041010340b0290700010100300208801485014260842004c04600c2d5034030150100002d0034400f068001ca410481280d041c4800c240c80e0074150340d040c640444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 134877230 1250 134875980 134875991
    0x204140a062a02010e0a27050105010903030e030313060c05160b0406030504021f0c02011709070b0a030605060f0705010e0c06030c0f27090106020a0309090c02012406020c0a030503090103 82
    0x161505d103550910182e000c10b400d580403841c84107446041d00b00901c45828039020b11400f000740b00c00e84d402401501d00049000702d01308082403017040e04500b40b02019040d286010102107805c140c000c0c883d005403001c40e030a807091104110081190384614609007480445442c00e0003c110741d075206134805d410400d07407540c010609654030b000c2051120b5038a904505800301ca5100003901241142c20300341c0c00308149481d482c40d0f11764005151403084030104c0180500504100b48061a40c01044002041558a441c08a000d80340d05c0018010100403512581c4c079040c1d1480d00748c0c01c0d580550b1034504650882c0115200c42e0311804166a085081c1114041d00c505462010300b003203000702c0300078640c0e26030030988404204601d00c0107101014020340d44180d00f603803104070507603903101b0801004000814034002000021015030011202c20660310011480c1c0c04a1440c0d40031f81240c480280000740908034081000d80d8041190309406ca03415500781042034035540302d4540b24001c0c42102414140c540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 134878480 1250 134877230 134877233
    0x10e07052d12010806010518010b0702151b07030b0c1603031e0207060501080607020a03050906070f12030e0706090602030906070c171b2b0309090204140a062a 70
    0xe02030321115042c20780702c001d040d0703940c01407107944410070f101e1a805030000152190803105035243c0c103070503075986901252800815034240a0b240c1e00e90814081e0000041c4000a40c0408140701012250a100c00604090341142801d21807091b0103055000f02402c00c011708500c44070b148052452954250800040756042c1088c420109401040f5a040c82403002400d9020017080b40e2116050780e24080854101e036980480580c0c3d034628641014011030f6040c400b89000c2c0c0f41410003031424511030000018400f03c140e0340c070f0140007040c51781800400e071103c0a440b465002008940010105803a14002e507904d030600c080d4072849186446030150f000064210203008100318010700410944ca8400c4100b48945104e5840d0008041068070340d40d4000c85003001e603d020047c540b41c1c01c10903085c202540800c1001481c5200d40d074503040b01805121500006d410b011480078000401c0d00c0450340150900a100b0000110050780091060107211071900c80600d03c0048402801d480030419032210321010f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 134879730 1250 134878480 134878567
    0x5150f04020c011503051c020307060209031006030609020907020c0f040e0313060903061407050d0f0e1c1103030108060c0c0a0611091c02030c0d0821010e0705 70
    0x41d40e12540b0150300b48008419200111a08601164096400c0c0c0d8612014500c03c1030008500c802e0000040c0d00601060000c01e805a00901000c0c3e8010b04031500e540c0c0d40394010054942e07661059401e1076880101c8007d6041001413954090350b54800b40c00440b0f8120001030582c08060446c1d80a40d559441032178285034100b0458044003412080c0010155882d4170040035903a0754001201c0190800050910081c681c6c400113004030010744070340341000c04074002036004004100080080e11740b9191040340030282407249031180c14100343c80e20207034150010090b01004007203040e80e016610820040029440c080740b0190413601c40c41c0c001380d40e034034240c203502e1070070032038001c0a0005480d1521801c00b0103900402000720075800e9820342060b0003a90500b0701d40c03d0030a90065019004040c00440703034a805031907241e116106010f010305000440041800a08031086c2d170400b0780440e00014861010070751805680060a80340581c81c050310200d03d010306a110408090400039070030260384c00d103008d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 134880980 1250 134879730 134879737
    0x11040b09040b1b120c03040323070f0302151906140306060d02011403070302030a05060405040201020d080703060b0d02040f081218010e120c1306050a120602090307032405150f0402 79
    0x309141040f40b942400d505c070b804254419181280070849091410072002a5070102c00d804900c01c0400506000c41c035102e100044103140421001c601526141004c1c603180300d041c56000c0d4503150840c5960b100c14101030822200c2540003100140403040b2a000c9035070f0002405039109605640b0b11441c00242c1c40146d0340242c0b00000310f41c8104002c810411900d504d80c0c040c5d840b40450307403014001c50721080c00740070481c0c1c81030364003900507007242c4007803410280035080c81500030711035141c0050b00994403910b4140c140c1000c0d110310401500001d0411008640029880180c10064050040e0301701c0d000c0c507841c20340715980d6070b070000340c407210440e40d8142c0c0510090030301c411001e4128000c0c00d0389615216218103c01c8410762240d4000801e820b88444036204a80640d40003401108400c1d081c0605c004803502030500840e94031f5000c114071144c030380341030200c84021441078406004100c2c0d1900d244140380b00c0a0001c00102e8a04020401a0709400c045400e400c0000c0e1440c0108200701c1004c54040e10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 134882230 1250 134880980 134880997
    0x40b030c060703020d1b08120903040b071b050102190b150d050102030a2403080d0609020a02070e070305060d0209060111030406020c01080108010603050705091005030a11040b09040b1b 81
    0xa90200b51001455008242c90510782510b43d00c081c004c05064069401e40221100b018002d5001803101d8030084900070b0300035801080440c212420240d4884c16105203503c02082115a10131801c081c0040d400e04488103c00380030240080c0c841075050481c0c044074800e030b032030014212140a1010400c0d0329041d01000f0517000020f00304c140c80ba8810309110f03000c2e50065807805111450504420402040d0480118003403440c0360185040c00e18580f2503407099003191040355060b960f110800030b4a50308610040c90744007201d40241855514244c1c090001000007003640080c0345c10711082100540d1088030500620780e040307454940c2602c64100403601d10820015145207440001000b29904e0740000e5041d5840c00240ea512629a1300c51621134203954440c4402049a803783d10305000d6450721488096212030000b03056101c01c0d0b65280040c0c5400c0d20000103440f800082d01c2200c405051900420243c0c1005840c20398581c105680c0d00d9101443c014541d80344000030f940381c0000c400103482101c1500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 134883480 1250 134882230 134882239
    0x10b0307021908070c1403060601020d08060d050f0322060e1f1b050304080118150b030313060801090b040b090a020a05040b0705030a021903020604030c0213050906190209060702040b030c 82
    0x9444003824040e00c02d03202d0480303203c0d21542c2300003410f942c0b0001d01c101c00001242d89070340c81903c8140600510a014480c22615402020809175044400308041c06042480d0f034010940c001500c6085402ca0710070390003030310400c41c0072001e0a0050b100d128941c200720750328031115403584440f640116060f64030158607442500301c042001041c014004040c1042e140c0600080100002041664454a80c0d11308000c1c01c03c0c203070320b450441c0002c00350700c060721240002c0d0a40380b800319100c0702c401f0310307079842c0d001180454818070040c0078207181c500c58100c41c407106980401c075012900e0300103061410005c052031101600044c400384458440c605407070003040c0240072980c89049034038100d5101c0d00030b07180b03040051040d420f03108640108032403080307110b981640240006840f9510122907084a500c4181e8004c0e490310ba85001c035000710f10510f846003500402a20840c1043c060ba1800304891420603440c41d8010304c6402c071f5550700d0000721844203904840000310307036900e40d022a040c900c2c00706100d84e10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 134884730 1250 134883480 134883503
    0x130503060403020a03020f0307030806130b1f02060601050a1706060d0e10050a060e19020f030a090c0b2502040f230f0c0711010e030708070e010b030702190807 70
    0x2c060b000a02040014030036000d1314031140c52280c50305e42da802114400750000d2121400b080d224207203262050f5030310810b48000b02d00c088100300441e8058010046c200b4074080700b00a070100c0a80e0504c0701c5034100b582440d1451404481d04d2006003140c0d40500480700c0c641c403a00c040345c2d040c2d03140801c803280f804042d00140841c030004581140c564000c4e20468040300e040034000745150800b845032030107a9100005c086426182c6821032523070082c126005034411a82000840c0d00710040300c0142d845400300044c0450010504c0c1b8110200254030b90003401003100500401c001440d1180304520441d01c1d5990f04244501d036400020040e22006800c1038000345407100e41c9898004d8a094691035849111442140303850340c050401e00c0a208441035040301d2014001200080c0455101000040f014500303042d0140d10100007034100284d562014440d0391044200b004a200740d00c2801d070040100428441c210b18040304041e44461a40490a110b034000780d01078420807034000c040d100c00542181e010101c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 134885980 1250 134884730 134884733
    0x7030e07171011040506040b0705031303060902010f0f0f031812020601080610080d0c0303020d060602100b01030e060c030712020c10060e0402010e01120f050a0b04060509010e0c1305030604 83
    0x860b11080c1c0b035818145810000383d80340e00c56002e4129802c0f11000341419103031034941070071408103400c443c0c021a4a0301042240103220000e42c065203010718050500020702503814800905940d0803150541e080c41001c0c52440e55154020841c51048405401d011802044800c1c0c0b280c9001e001c1000207052101c582e4417080410390002c0c0305030507140d010040741d4154440c070501e075496050501c40d604c0141d011075041952240b040d0400351010303209040140c00d0000e5aa07808040e1141c0750400c00040c1c0c00a0013a050500341402103103d40034080c20304200700e08608000c41d494240c0240b103400e000f10004041030310365208500100d0b44410060045464444841c00c0c2610b03042c04030b080401e480e040c1540483d00c10001000e180c09654161034000020414000564180c01e80502400240d43d030303101c044462151a0280e107200d220700c5003000442d030309080100411034110b0f0304018050307030310303500184103071410000210381014044480e40c1d102c01a0804008601405030092505406540c09010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 134887230 1250 134885980 134885983
    0x110105100306060611120a090305030d0e0c040207020303040302060705030708040f0e072610050406060203040302190f030b060402070c080a05061605040302040f020906070f060e010501060807030e0717 88
    0x1541d215880c148410b0340d48113011a96030441d03075400c411680202000e6110103854a00400c0304511034104200304030b9890300c1d003d0550b00074000501c0c0454543e9100d1824000601001c001c0e910111021070420800382c012950700c0c00b40b400700031700070030303001400400313001c001c205860007980d0140b0120707aa682caa00b0515508646d612500501d0409403011611090113604440802e50341c0f81071f0104503991f02c02c00c13407140440c081d0941d446240d8542011600c2e84540c013514001d0701540c0c00440c2e0f66451441440302c40d01d501030352045561941d85003488407070b0b2690050703001c480d000201004192968030019009101d00e45006110380d80c010400100004040744140e9090b00607015203400b41e4440d0f045050900e4500591800914100400d00051909500c034900c541151803005080101030b9011900c03da00910058810384641b0451004100c940d0180314911342c0014024080c0e03500d003d00103092100003402600916031607400703641d41d4410030014180180040000003d0041d080d4201c2c0303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 134888480 1250 134887230 134887261
    0x603040503130603020313020418020301380108010501140409091101020d0207030b060d03171515070b01051210060b0a021005040b27030304060c0f0e0d02040c110105 73
    0xc4880d542d150400140680a80300380d0388540000f070801c0240000e07a900b008001c16401000f58040300920a0071800b5890911803441c01c50b5500945500180c54a02c00750f8a0601c00c114502c001034011030300c0450307660700491070f0381114001c0c00c10702d84a0250f02103401c0103010f41d8001450701e130303c0c1800070000d0141a02e40c8032155130302030702901d001240505040380c641e84280030250906010b240421141d042803044220201c0c000c0c03030b0079038001c40030940004940c002071b0b0300010b480d0204061001c07a403904038207031301c0410b0a0b12205850b1842d2a520400130203030500c200d030300c49c00c50030881707210240c0c00384003000b101803c0c030008003c42d944816140b000c982205a0b0756005101e00300550900d5407041c40b9140c01241c004115498035510200e8083c032400e1003120100c0410304a04006003c004200060360003980b1425020401100400c40244202c503002c10030001c0150b440c0c0d00d03d8060701d419440001c0c5d180c043d10045110728000b101581d80111300c141c9a4940d43c030345810010300c5c0c1d0002054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 134889730 1250 134888480 134888497
    0x5060a03050d050a0e300a14071a0322080d0c0807180317030601031508030423010e01031a030a0b0609070e06160c0b1207030501080105090307200603040503 69
    0x15202e0461001c018042100300c4050548080e20044100c102c000d01486100c9440e404010103c947c907040954568031600d00c8141480c60a0703002c8481840b100d60302140200f50f44c0781c1000914190719003261013444444651584122840a1040c2c0f50b007032140e070a0454000a010010500c6640441d20000b801e2b0f03241210322a0010b003800ca0900030a144003160007085941060b401035a240b0100701c85802684017030710702c90600d81c0d80c4c081030090180c1e449258000380005005503841c3d51400031840e000381016441c0340503100110500d81800c0ea04403004104180c1c081c640003481f100a0200b00c03040d00302d010510f40e8180b1035544400208441c400442d4407501090b00c500e08a51500d01040e108210001030b45603015005205450011100d001e0b00703040a070080180100c0e02d59110280441d43d84054002100c1040490400024503018045c3c10300400801008110b185415170038203449009012000304109034100d43c44690014039600c04100d144010301e100e689081c5480c119540740e02c5000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 134890980 1250 134889730 134889737
    0x9070f021e100b0a0b0706021803070611010e0601051c02010903080318070504020f0909040f081204260405060d0f050112050d0801030c090b04022b11160605060a03050d050a 76
    0x1403e001d003408580f8008030340d43d011615044c040c00e80e4400c001380d0000541e4201b8030415042200300d944e0b0402a140040403962940703501b07402080804c90039103d21000d00c231441e5208500400076a284c10b104420020605000340c030041c5954030040f604421075500240c0005808000d00180d0014080c10103003400c007190442d1101035580d02032205a000d070f003000401ca02000c1c0040140c1d820a408456846485112a005800749030754070304807190031103144400c0710b261140801042046a140c80000c22102c487c02060111003480080003503c118041e50b4007406003c1040345003102c1540291800700c46d0803006002d0740d81c40c3d55240e00c0d2071403451401d45079403007074003084c0031118016190135059079000b4200113903550405a10001418a160f01300381c1080c0d080000804412003529410a5101e043d10b0303c800301100c000c0c142d070540340f03050f40d45110900c04020040344a4250780305515940d0707000783e01040598035440010344c4100d89038000342c002e001304446c031070510b6480f00003080301790050340b03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 134892086 1106 134890980 134890991
    0x60405120714190606052d04180807062a0f090509071107090e0c0d06090206030907032f04090615090504110306040209070f021e10 58
    0x207804040314848031002e00d041000c4c6000c0c030001000115500881c40c1d0300f2000105003000171300c1c800759004120030404409501d0719040810000740c06d244003640300c2481d00309201503034400d0b1400ca42140c60800c01c80c00c4420031290600341031203102144144d12080f00720985111074841210018421095000501035417045401d47c401d40c1a5940e80d0079010500054500c1c0544c01c0d0004a161800c05c3c0304040e1780080001c1c00440204112131003030411149041a10040c0801840030350840b40001c20407126806c0000c03142c3c100d034415240114012290705000d0115940b481105101c0e0847e07855a61182c40c140e0072400701103014440008066400a031001640b81c00d682c4503888841d120400c1109120300c1036600c01041c00d0941c00340003036150582c0025244c5200410790303000e2001d10942903507014400c002400e14405511b00d1014000d5180c0706059440c404000003a20050415 = true := by decide +kernel

theorem cover : BRFrame.Cov 134712230 134892086 := by
  have h0 := BRFrame.cov_init 134712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 134712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 134712230 ≤ n) (h2 : n < 134892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
