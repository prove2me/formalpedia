-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:36:48.916771+00:00
-- url     : https://prove2.me/submissions/32f799db-220b-4fb4-b4f8-6d8f56bcbec3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 554496402 ≤ n < 554676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 554497652 1250 554496402 554496421
    0x150e03391606020109020f0d050a0615060201110a0e0607031e05030a05151f1e0e01020f010506090a02090f030708060a0c0c0c0303032d14090d0e04050c04090f05 71
    0x1c150310800071a403400c09050016610301a140d40d081d04203c560805003006814198108072204a0040076145010001405205091052400c8a82c607030020805424038000301c10304c9100d03080d0081d0008a2800c02030f161032420002800d003040c002d103847d00082c0b400c240403800040d84420000c1c0410001f0013007080010580c02016800000c945149981c6441500440c01400c00e03c8201845000b03141e5900f88032900c03980c3d521044a83e4094009126110140040d140b0000c9410380c0c1e00501a120444030120014000c5600400020307010394010340c1da102c0c0c0c4100a4101f06000da0f03104c0880c49803604595000c03c03814001c3c040340c10140c2090b00700300598100322414012280140301c45803c8950206805001c01030480c0d4160a002c06c21101c4600070610754403009a424400515070300701894803c007903601a050701040710010580903150050320a81e00c5490500840000f800090100e059003001c1d08440d4014920f4681d03c2d007003d03121281042a00c5000c0100841c1554403003c00c1030106 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 554498902 1250 554497652 554497693
    0xf0b03060f010c050705010f1b1b080703120e121b01120b0f040f020903060708041208090615031f09021314070e0f060d09150e0339 58
    0x10003d080c6000f002c5800d98800c0e03152182403041c5418031044c440303035950050003901d0f41d220f10520305558600ea03200501d07013000c007001c02c2c00c1c0160019070392030300100b881040001c4034020391307400c140d4080781c000e002d0104540719051002900d030840f4600c1c04a13600c604040021001c2d03540700c03040d1000210f542d000010480380d50f00703031a1169a8284068490182c4a410200f00307441015140801c40200c00c441c200c0280c03251081c40b6030148100410082e4075940010b4040c0034500c221280e181030031022104aa03160802d840204583d008100401c0303440408880031100088046d096072455400700e0201400c011f600c03042d0141c0151a41251070852a113149101c1d008010b00c5c404106031945084810316001009001c0c0f01488020805500c19a403116507141c0a401c0080c10190f4900c00c1e13032442c03c050400b001003190460380a000340042c40000d4095100010801c0c401541000e400c0f007464001c40e49200c80200800045003c41c07449d441042464590f00307075070b0380c00034000c0140e410b11820120 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 554500152 1250 554498902 554498929
    0x30f06020d1a0109031502040e040807030807090509010512010e0303010801230709051c050105011d06010c0b130c080604031e03061a0c010e1510052e090f0b0306 71
    0x210640300c022403032030303130031428a00540707030401641c0190154681604000b48610782041c103624170150104400c02c0a600700030410700344207075038040701500c50000c01d0351000c6640c01001da00520910041c480740c1031030030b2424644065000081002c40304202c0b0300303007103074002c0e00002500d944030280000f440d4048426400041d44290141070586840c1b980104001c0050140728031a541d00c07402c0120f204010b40d110825503030020020442541d6034401c18280c2d0380000450304808002e00c00144456001d41c40c01101203130803403500340e00303130340d4440d08149044602001110401c645010104544408001461041c1e1207525100e44804907440b02c1c031907220300c03184071004150802405001d0707003001803400c5c5030503481114110344031201d90900901411103807600034070a202e08005070900021002c0114040e040e000c1c07145000540f00e40c240400400010b416036410300d500070482c0d81d5100700040d085014201480c00341d507003d48419075400c12411543c001c0e00c0b141400b0081c4003443c58005040b1074070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 554501402 1250 554500152 554500181
    0x7020f040b0301180302010e2512030c0c0f1404020c0607080603031312030201110f04030f060216030c210c0b071107090f060902190f0210090614060d0c0909020a030f06020d 76
    0x40034460110920792000c0d000b50fa44ad00030360106031080601505a0780c858641c01051012440d40764582615103500c1c6105c0e4410003070703440011070460b003450700c2125510b010500c0904456071382d603030081d00c42c403401800382074144c44200018044080c1d580b4103003025081248620814104608000b400d542201d10500d40181c02001400d480e51004811213040781d601c0a080000c100c11400d080000b809408000c80785410401044000c0607800f0380181c0f01c0c1c52040390044600d030719100b4504000c07440c2040600205914040100c0414915403146078000414613010840c1ea203642070072818462241c0c0099541920b85516000748001c5004080140800d54821424074084850000c0101851708141c814450030b070344503150152003030280000217400c0f500180110101407804000401c0d200e2014045900c1c0342c00032030000e1a02022000300b098000702c1610703030305050142d11801420314050480c0d004107260310010000fa11951458081d5000303400040e25800c0011049090b0758401c40802d80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 554502652 1250 554501402 554501443
    0x2205040926210a0207060e010c0f080601090b0c010f091b080606180a141005193516031a010501023c0c01020d0507020f040b0301180302010e 62
    0x10400101e400310707002e541003150608a92600c20004000784510344001c1d201c5414283d2914a058054100100d200301c00e64440d500c0208010003251495025a016400101e10000810000101001800e510304c2d00310000100940f60354070b510100c80800c00105c81c044411040b80503022543c04180000b4142100035100e0350ad0030000041c0007008241a6003a01e044d9140030409481003035114403001d411240b20220181007131940c007103d69039a40300319803003a4401810018800300305822002110788184042504203003044c0b4200d6900244088012018180e4490b0300b080c180070002c1020300070068000100c0c00d821401d005c00b85144410200d1100d0f02240300400050742d0010702c81c000d007888091014040403c00c0052582c2240d999040d05221145200300c07000800042542e81c0c44010036000c840840754514400c0d01d1a0003034900103948002d80720961009800c05030050014150020000180b0170503a09a40d801c003d07102e101600140e55a40700c500e2040c1c410445041a080915950701c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 554503902 1250 554502652 554502667
    0x303010b0304060e1006080309030f120a110a08041d0901091109101205030a0f09031509080708120108010506010e0904110a0b0d0e01061203052205040926 68
    0x24581e100142c0020320542e40e402401180c40000d004e008003101c4852014003005985501c22603494000c1140d0034424010741081107128013000901c03056030202c03292607604102600d24240c584802c2c2d516021130500403100b12100040c032003801000035000160024140c40807070401c40380310500003131400546d81c0c9440310036804151b0680300300311034000480d1318900c2d0343c1d20303d04080340012181d44400d02c1800550000400c000b000b002400c202201039540213214400c0200403649442c0d00c0c40040c0041a040e030702440c14000c00c3d0404070500c2d0007100c4080c90100305903030b54540369005c2108002940042001405440800c2c0100c0e5000942481c0c04160701054500190181c1c1001d0002410100c8100c82404a52104121a0001c22160030002c2e06c4240c2c100344003010b07003024170b101900365280200101da1040d40500d030342c10050701542d400b401c0c4405800319900b00f003049441405120840700c40007849035500d00441110a200d01031380302c544030482da949000030203c01501d482e000c00611010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 554505152 1250 554503902 554503919
    0x609060305061b0c0d03020d0f0c0f180f090b01090e1902070c08061e0c0406050403480f4211100621020102010213061808030301 57
    0x3e80050412003940e10000038054281d44600c21107482024034020780b100c0024540e055400741964402070003040c4160014444200221000301070010b020070783c21180b03649820310440484803409841141c1100a585901c1d460048802c580d0002c184180c0351032107000f041d64002812001001e84003070400160a0100303180e42c1940d00c0002102015901140102c207006030440380c6d80040a02c14196000d604004462181d118014680500c00404050101e0101003500d01100c0440d1b42680d5068202825561079002d105100040d250030065510b0f0300c1c194519a440e400020f20005003140300c2c80e91803281d060400d00340c1551001c0721840043e041000b22580b03004441c50581c00404020402d04084250100c0342e01084a45420030310f801c0b40c100003131581002c45503a202e411940bc0300e120f0030000b00706d801914000d0061140652400103c40f5030300c1e8981e4680c4121504c1400050304040082d007800294000c194001400101c0d405940e101051070300e04094041d04044014524541c10a0f0b0307407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 554506402 1250 554505152 554505163
    0x20720011106061e0a050a030803040516050f0906010c050609010f061406121009021215041b0305090a080f18330c2b02030a0207031403071e03030609060305 69
    0x190302441c4c455080c0482c1c540e9220780c2400a000002c2c019080c40ea00ca0074140c0054000301c4080340d2a105124200c1100c401200040c0111107009142c043c540c40c081040c4401c4a90141c036140c1801040d80d0341c900028000d00074903110b00d910308000035607081c07184100f42c1610401c0c0c0c050603405550103040d2015884031400c903981d400714018007071095121201c60003002c070469840341c14060720105600301c1c2c4001404c45180038030080100d5401d032a25090420044072603d412802a50b041d0803034080e6858080c1c1c012540c0501000250b446007000c1d52503004d421703442440c40074a41c0500051032030700c103031810786010b41a007000e45048840c6881c034642140a080059061640384041d516500101980ca004a030b81140c00102a51920900303111541c4845208a2020b42951825228480400c0c400002d484e07901886a004103081442c41d143d102c08107060092215050008000b45400304035a410240c2c6e087e03000d4815074244080508004048401e160450b000f00340c00c0013000c00105000180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 554507652 1250 554506402 554506429
    0xe0c0f0f0904021002030913060303140f090904080c1615050f0304140c1806210a060f0f090f1b030308060f040603060507121802012102072001110606 66
    0x2680111500d807150160303d940185038905070700c400f2008002c0011000703600400e044038840d882c1c070032940cd0040120f0071030780141c00f00c40b4011b2005020f207810038a000640c03a50860301404902e49441c0389402c089041c00061400012458003008003048480310b18403c51001212502d00141807000300a1000c00c0d9110151001d4003000c64415003985603402406400c2e98860000c2c617426030081c0008031016425030440c0d80500c41c580d1200c99215070301d1130b40c0f0000c2c110703214040504007840c2103617500300c014540204003105c01d640d6540c11000c84116446084038480c041c048141880043c1d01d06640c08a242103082c58495807100000c100098000603d2038000904a402c00114044240414011b0217254000b40c1b0003800c102c1886206e41d000400c0f9008032204c05428460240c420038052000344810b08000c1c0040c4a03200d01d049409000d40c103c050f2100700c11005880c000d116150342e400b0320782e00140d101c10b460841c0c000c040d480d038102442c0f40c10105c6c3c3d05c2c00751816141400000b0b0581d804031a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 554508902 1250 554507652 554507659
    0x81905061801060e070909050a1b030f021b07030b010819030807170411120102070c0b0a1b1a0f2a040e0a0b01093006020903010e0c0f0f090402 63
    0x40400446a00a412a601421384019008150b00e06400c00500080035845030718070b070741d1901000c540e841c03000e80207414405d5a54100b0a42241c031020048006028000005c04425030a1083d5404842e82d100c81c108040d003118002e00f00e260444c20310303091810060b4000841a480300c1d00f03010720300d9001585c000c29143c16040c20840b50751181c1040e06d0402e6143d081d862983d81e0304041101300410f810060308021416107480c001940200c1c1350368200d11681c1d9001d065140303d400300300a4621454000c0035185081c0c94201d00c00611180c1c9000120041e01d0109c401c00480e9810a002179080d211056000f203482e00e440c00f02c4d00b8446041e0b80c010442c0f080135159030b02d83c52651307800c040c034120031903000f4140c1100e540c4c080d14164507203c0c010a6a91300c59400220752200000300d146506020341c3c50004445020748001c031a400c450881c950828400300c44181c0c0a01842105540038404c207054070f04680003070728400001108004100c404280340c1c911031407210000200310303210350309500c1c7c2c044da059 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 554510152 1250 554508902 554508931
    0x10060e040203100e04260906120601030603120507020906090c1e0c030705071703030403080a0905010b0a06050333040e0109020d080703080709051c030908011508190506 74
    0x1603c81469400740c00107580c40e10900f00784020010140e01074600303001c0b03014114200c0c0010390700160300b52140e81952540200c045c0729414000181c01c90b12a04400141000039005699540700b844400424081d60041140421000158180720890303d51106044134011042d00d400300944403d406030003442d0b41203001c01c2c1695080c0211400c201c0c0c040c0c2c0455000c9a850b80314070310700705603030b0700a6000d14600760860f000f02e103000e0710000042d24007996054032454003c2da58034103101c004100c4904190391540d22248454110344408c5038800280200d5900e0f0380c1e40340b6014100d84c0da00700c824140100c80003a0000c440241b60401c04590208040c01c840200e050301c1120703200c0e030240000304000795112103408034141c1049500001480080c1c0319840d50342007543c3c2c5040c01d44503460a4401c098001090384ca44c2800500d01d900051086803090505a42041e2180c8500b401c41c3e5030f101034080290411801804010b4040204010407038001410003444140f507a517280e1541c40245c920320481580 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 554511402 1250 554510152 554510161
    0xd0803130209151503041a040f06060e071e0f03020901051306090e090106060804080702040f1a0a05061602060322060c17160f0512010308040e10060e040203 69
    0x5401410803550000c10712800d506250044606218540b40d820b4450014281e49001519000055030b10030b40d045840400f4119440203404407500006004139640ca000d0030b0f000001130301c2c83c030a500141c50015030281c1d085c0340488001c1d1081100d081d015010000607844000442d03070228443d05c0701c10061030056180d114510042c4ca481c003410301d156442c03012110001c03403081e50050500c0100c500d0a9010403458440e0018076088030070901603d400104244c0000300852488001800214809080050081c2103000d403d4219003840e011540035110844110000b480d002e900c000192500b10381c5c46103045c1410341c030024841d034140e400a0007518044006100f210040300100d0225000c440ca04491344c0107417410038020044008440d0100e490071822042c200b0380001c0141c030441c2d00c10318810a2405505c815500c0d40b50303001e001d204110040007116140301e15002842d00951089080071b40b1503003441c0088400102c003c102c06800a50b645080010b141d2282407a10340b548240d50040c1c1c0c1e52136 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 554512652 1250 554511402 554511421
    0x9010309050f060a061a03010303033207020d180e09011b02150a050c12060a0f141e0d06020906070c0611010f0e0d32030717060d0803 59
    0x80a14040c20a00603508882c019010120f01d051081d807110300c1c00c00c49552070380036284a01507500a0402c00303171001e1006100082c041c0d4000340b501c240c00b80c02c100c6088140b85030800740f096195801000362448038284511160104101d11543d042400c14036000460000c00500e44a058030507050980c0451012407410342c0300b9071148a04106c1007101c10740081e08048040d6850405021603424010820300099607001e09214480c0100c10348118203140400b104c3c07484c0051785000c2d0a241d4401c00c0060b00003184960408020000c006010013054110205401c11041500300070140f41182e0604060300f0346682c583e003d40c400c1c00e40c00f030310041e101c0f80b4070004104980141c00e0020f09100c2d07000c8000c90140c0d0414555144000058001e2251000d010303405002e4985880700180301e42d120f40403005200c3d00828200c0b6005500d4003103444581c0300c41c000c14500d21082d80f80200c042c50000280070121f940407204134102c0ca0b400380c0303901040c2003590208415241501c0054440030021001c40c28100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 554513902 1250 554512652 554512661
    0xb060f0405071d0f01080103060507031b200f060103081318050610020f1b0d12110f0c03030d02030c0d0509031c0519020a02070e09010b01030b0f090c090103 69
    0x4060001c01441c5019440580400443d80c40f40c518458071100349107103460841650001c0410603510381415918541d41e440144c44060504e405254450403d01040c0481510511001d1040c0d038640031040403001c40c1d40310f80d40c40f0502c864016040618250f001540c00a0303820b046a60085a66944010f18815126400503540100c2c0540c1141c1c5019811110365030042c60040808503430032203500200039426079541440225110740790b0030404980c814a45035489548140401400c030703555270003061342e03a820b40300714448080d030104000d80c608044106040120070003030740951004041001280d03002a03079a001d10402c0c004920340010024a80041c0001070320030103803400c1000e1003542010020307280c6a81180342041000014800ca41590712700341d02030103020303100e40c3c40ca007000645400c0521000e54403c9000342e0075485261000141882e0a80c030951080d010440000b4004c90030f040010140c800c00f0314410b00c03d40080900b01c03080d50b10480c4a0f50080c03929543d00e0340e14203903e00142d011b407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 554515152 1250 554513902 554513929
    0x14030405030f1b0d09150c05061513060315051e0103080304020d0219030213020412060c05070b1023030c0d0203190f1b0b07030503130b041b0e060105070b06 69
    0x38000c42c0e07149003072613030004114019070325006d0032980062500744045800800c10140541103078440004564180c0c440d40c0d5509102e10081c00100015400190500c10340700d20347c0c0104c81448505198040e181190302c01d513500403407001901c600d5130300c4c9002d0460405c10b040c00060b021b000000040f40031540c540300c011650766800380c503030012820306032030440c2c031183c0501c000e90052540425454000259201b180c05503031a0424100031000d01d925400014030440013220f00703001c0204001804107005a0300144a0130100300c514400c1c44c1851951001102c5180303890302d51014644040c220f40c1e41c0820305020032002030301c2d0b4943c01e171010300000b40340401c901c5040100c008009042418000a42c002d0103c2d10300417103120201302c017440080340c00f00d40d180c40703a0750f1503043c14042c083c0001d100720001c5400001c0308001d400302e0036035a2544524040181d80494800e601c84000b84c02c1c61840001c900018440890441418540000080e003d032081c86030092010258100194560741c451001319641c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 554516402 1250 554515152 554515207
    0x30f0603020a1d0903040614090301021b030a09080304030b01140307090c02010c080f011202120c030601170105070e1f050f0309060f0108030304170a210c14030405030f 74
    0x30301e0341c3d441e0383c0041c0a0a140e02203400700b4070320000400c804400030403034003160080c1d84c40d50f0340c2a81110302110306801c00140180c0c555002c000c42c9011252140100c2602c440e600d01942d40c03105200320291070308903180c3c4080c0c090f800900041001c42c003e149d0700703411134041c01d600c050b860300b6010000f410004250080c1b50207524001f030b152002903056002c26030728541c07500d42c0b0a854944840806108009101d00c49550300c83d1658400141003965404908061803000c8411280d640310010342081c00c03d0b004a0013080382c210001088102c2402040d4004881d8140004000040000301d5a41854020580790704ca40c6103581c0c1160b107214100300d0b8440240124900e889040c0308c400240c9400040d9001000b0b00316031000840c0050f404021a8011644601d11074041070a540305000240c00c9258103409104900018041c0148120000c03500720001500000b400380c110b10307000c0c0440f41141c0d120302640e001802000000f87c00001115240c140d1024415150034059442c02c20740c2c1a80250880f6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 554517652 1250 554516402 554516419
    0x30711071401090801050c040302150403170d0507110606060c03070507090f0c0203030903180d0213090b0c04060912060b0d05070305120c2a060a020717010b010f030f060302 76
    0x110190100d104900d048000d90f0303103604070350781c3d04c0060f8240c4005483c920114801008100010f00c1d020300e01e541c0c4444c0c120412414952380c0e488140f911039149100c00300043c4005030f01560540d0718031030154006c081d41410000c1402c1e401601c2c0d52200018500c03030207000d001034902d0f500001041600c2550b0b90200807159843d407500d50500c090040a0000400745007004141c502260020080d28400e000c3c00c0001d500307050800801036003601c1e6541d8100d070404070411803038015894801c283c1110340d030207110104846d051464445c0e500007004100c046201818401400f0059224005034125450100c80c103071038240a040c0034005043c4006125404021104100d0410031b000c104001224003900c159101e440c007686801f20b083c8104446c1b00d0440d001108003801040d094102041014248032040b005884102c000c1511a4022a500d6025902c4043c08001e812615050b521140709000024000c400304200060070401c130005016051507107481e210040043c81e0f5100c44000c50b0000d00360710 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 554518902 1250 554517652 554517659
    0xa14040b060121090212030403050d0c02040605040204060203030f090f0c0103020c15040f0b0603030f1213150911030706020307030f2a0201020c09090c010e03011418190b01090203071107 82
    0x4010300138103804900034000c00580c0804103401005607001c694020f000390021000c100d00803030340d16903c0701080340d01550341d18000c80c0d50386540c406407002d0b02c542c0c0c00440c0e0b42d08100704000300c9440010104685a4003820138102c5621010842d645c2006080c02e0240e02c0320451140681071180280c178a11520740501e00300010700c9031a4400e0031009024000c211040d031101410315440744189180444e0401303041190035241120301c4e003a0307544045013500010002e0880e907201d400c14275148141e00c003082e0301e4804500a0254005200000e014102e00811100c0c0c604580603449000e0b810024042c081c905960900032400b5050145104d0044050070340844d401d418050001052100103030300512450302c180100d4108030300e0071030042040c00d00800796080290011180c620314a01183d8040d500d41d18940344810b01c0000407801800c1385807089000d82020320340d135454800c0303e410a46603406400c0018000c0b07000040300034103444a01303e0140c0e503641c0381401a54081083ca02056075031040300d0307000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 554520152 1250 554518902 554518967
    0x504021b1903121b0c0201020c0411031602010204080d0309020d05030c0d091215110d090b07030b150403030804080405100905033a1e080601080a14040b0601 69
    0x7080700d07602ca9212803483c407440701d54600c1110702c200e60304505000c1e4011501019402a070515000701d105204441c0761454800105e000c1c0c0d1105446030400f2040802400901000341110b91440d00c4248000c505203490b055155944101886104c0b0134190388940140a645a03c100c55200c01c3d0000100c90747c0e02d401c0758205585400841d40070700064100350b808100c161b130103100720f10000c1d00310b00c0600e280d0483c581d0a00041403100e103584840902001665080c400600035100c800e409006032400e070340b91104020703013598a10341080d0f11030200070703008040702c00780036003aa0305694251411031700c583d0b100e01d819007140c40b030b2303410060b4000f8a0310ac0311100303107a00c8216003051307810690a0300d5400004002ca021610108901c0d231034901880c6a6210f0080307418071860004404510b4625070394030303c0102c110b025206244062000990001c1000103a58102070000e401ca800d50b50100000e0030403000032020004007a00c01051a0030314400704445a11403a6280b0038a0340400e10400e0709808440704 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 554521402 1250 554520152 554520193
    0xb091c051201090b030c09190c05040f05030a200d140c18070c260a090e070c08030105220204090c08011a040e0a0e0a120e030c0303040504021b 63
    0x2039242081d0400000310300f10000b40580b2a5101c0050014034001c45150108143c00c4c100410a900002d55a02d070001c0c2c1806c1800389501103045034030307050341d51801e110098045104030707004107010b075000c4440ca0002508591a03070010900c09900141c000b20014001014021082c03c060040c03807041c20302034026038021401d00e6151404580514844440551880100e48112941c80c089504812410041140324081480703040030301060103503010445419414582040c40d2410000b4203031070061121a140064103904406c0a0510803007010310350350b03190481e110502850380600c581d41c0c003e9000810034001400380300407000c002d540b110707245e0025a004100305202280004c000000028140312080c07401d0b442084c0c0120a149000c1c184182c90904040252445507059901e00580341123180910a003100d00d80b198102c144400c1407940001d0140010012040c0300e5005441c8080a40d54000102c808551007520090b031503814600d40e031407100076014000d4941b4040c0ba0b100b003281c0fa541129 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 554522652 1250 554521402 554521417
    0x3140a0b0a1b0305091c03180b010e09060408090607050309220b01110a0f0203030d060801021c0b01080a0f0b06070602070b0f090706350702010b120a0b091c05 70
    0x3030702c54501d00c082c10114103131101a116074495420078400310300d0003144041800255007281c240811401010320070600a2400d00c1010344421000340e0040c0903018041c15040c1c3c208040000605090900d40c0791400d1520a50003440d104100c00101b0404002003402039462250300105050941e008002da0340c040940e080d01210040307460f00e50020b00560085010004c03c41c40c0700e0080500006607a915030001d48501c42c00d9900d448284565500ca90b00f41c007611018003c52400940c0301da0494001010000c050703c4142003540c103000d00c148a599000c80616800030701840040344012030032003a00020000c12001d01c0d0800b400050040a00505400400c81365101d1002490325a40d2840d2003980c1e04c40685091000d030308880e50030400c0728803407041c0480700050040081d107248a600d80340c0080381c0718080d2103da64101c0c0d000304401e454083c402c2080c4080259142c00341d0341c0c09010708a031034030b0480e500208180102400b0454600d020032040e202d14400a03201c058454a0001c00303401c0fa001a00b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 554523902 1250 554522652 554522681
    0x207110a060f0918020c25050a03080304200d05010605090106091a07060b06160c1a04090e03040b2205030a12050309010b2101140702060103140a0b0a 66
    0x290000749a0710652252400c4034650303890040d0503040a90b04078038404080c2c02c1016050702845203141300300003405200440d052408615000c040f2244894001d08075179402284105050541003021595050484c0d502a9201400000740d00d0f1600c2d0303280360711031380e0428250040100382400c0c040010541c05801901c0c0d0031100c0d400c1d03036070340c841084403080001d0155088800501510b031490940410203421038500c100300100701000f040300880c030745400001d017401e110403c1e105140c0902200f4940180a0008204411440240c201100c00948900e101e0940f21f2641e4000008901c00c1c1401036a0143c081000c00c0c954a000c1045c4e011302104030b40c01c030601d01000c0d06034001100c1c9000904500410340c4540d0480c0820441202036038180c1005140094a54845182503140c0d0b42d0440c0c844402c0d91000345501c1c039a2000c100460849004620403c090000c40b428040c0f01500020690b0440b0341c85441e03441680d0460b2000384c14400c940c0801071140311018184075503032980e038005260949002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 554525152 1250 554523902 554523919
    0x160906060e04020f27040f020a11301209060105010906170708060612010b0c190215070f051f0f020a1d210d0215100b0304031101020711 60
    0x307004010807480790413072000d5036034410002180e000444003072400e0302410390064180e10039081c5020500381c2c0c1400d0f540141c03640c2e000400703140c06504640d4843d0350030700031002890358491560810340f80c0b11141c403a00c0807008501c00d0008a40d00301c03004440303c5014030f00c83c050140c02c1540005585010030701034640400d030980804544103208001000c009400748014801c0342c0c41d80c40382034a41c500081d0549400220402c031045425682c440101d00801d003103894503035280340e1701303840d00c0c02d14182c4072001244a4040c500c05003d80d07220283c442452443c015055078561031032034a07000392869005c00600700d00580c03400d204404140e84807002c1800c003509040c4801c9402d00800c8089204580505000c1180350100300e6805441c2c00702c400000002a1030308502209903070100141980c8007550008913031041d81090b0129606205001c400c8801804400450030300c6000001940d40318042c4415644011000805052144818090300342c2010000c41d5604002c0c00c01750b5208600c402d5560241854 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 554526402 1250 554525152 554525177
    0x30f1507050a1d010c0f150506060f04090f02070b042105030702030a030504111903020411030106021b06071e031409150c010b061b1005041a070216090606 68
    0x200210351103008250359801456090029000a2090f00d801060400494000100000d203d001203500b0140c0688410f440c070604101000043d1030000303111078000c01060240300d0348403250314261002e840c48903001013032a60113410100000c3c040c2c4d0034040d02c40240007003844284202191011014805034258401000422205598502c019501071005901c100604000b080c820f43c0240d40041c480c0e690301d19003c58080005071101000504030406842e8008100118278151151610311140484110300310f61404d00060349510b082102d9215000c86a00021401c1d5201403c0300c0c00c650b401051901d1403e40000e0014002c484a40c0460100c0c40031180b400014a4001c01e58032017001c02000e080d540c400200051440e9040444488404d43d2548450219655080007a22040f40e000e50400b07070160a107003030b130703840c00c00d03100111070b60940741509220100d1007881001d0420415119180110345801104a2a002d56a134070a5800340c400312003c204440b603900000111019607039541004e140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 554527652 1250 554526402 554526407
    0x120311010207080405041a04060915050a05010212030a0e0303160e030f0c100309060e03031603060b0f0c0307060c0f2c010f1103071b08031c0209030a02030f1507 71
    0x2403420042e040f020144000c100a240039041852208407505c518440342044202007010f443e029040b1001e16500c0d14412020000101c440d98010401105d401821510b444000703500d8955403403007238030744d5140040001c541084a41001c0042c000030412295a03103400001c802d04001807c840200140c802d14135000c0030302e0000b45200e4240418000341000c071100c1c2003040031485541d0110400d254845010101080075441002e44012030300010710f03601d15228046d00b0001c00c05d540400241450f0160030300c0001c0c04d100a42e61741c3c800d6000c8407a551080040d50910703501030880005c08460900b60f100c0c00c996441740c2665800603058039001030032100501c0c82d0741714654490b50002101a40400690b036503100d400f91400100f860b0818121f88020a00011300b168081d041c1554407000c8900240d140103000d500882c014403581c400b4506104c0c96840203a41c01c105080d00300b0f42d484c1c0102e100e549954060100c0000d40d0703802000c03600410000c2d041c103522540005543c2211105400001e4405c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 554528902 1250 554527652 554527657
    0x3042316140901050936011404030f0f140f300a0614042c0c01120e0322080106060804110406060507120c140102120106050f1813061203110102 63
    0x1001c110b00e00300c41c0181e8075031600740c2c91446c4140c0c200140c0a030041510020342071090700d070b020f00c494000150501e001e003000341036005071380c81f18005c000c5880d88007800c540e40840106e50350140070782800e40d200c0780085000f059008441069108002e41e41c1c001ca1080b440703002d94a02404041805400c81da501440c08088458510810026201c015044084d526040c3c3c080032540e01200c80e540c01e074541b4203203000c450030905030b0500c41e680e101d10f07209001c81d81c00c0044c0f404031100102060000108845c41c0e26180d0081e4a040f0400382100c03c0c0e042409444414401c010b0441302d0002c003c910740e10440189181003d0b1402d48881d01c3c0e8150034085070900b07000d80c1d0282c400707030380304c4034584030f03850341c0302a000c0c5110842c40080001752405000003802521003030810901c032900241e12120f5140c0c5150404806038804c00038003504104070354107400000d003511404001d01d118240000c00d428041210440340c185c51010143c680040801c4900e040c40d01e41c0c1c001406075641441c0d0440d0141071600b02d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 554530152 1250 554528902 554528911
    0xc03091e030a0e0d0c0f091506090b0a02120d09020f09060117100b03010608040506160207170f030705010e1c090909030c1205040515030423161409010509 68
    0xa0700700304940b540c031078010700c00044416405048030b4040071140d100c050b620f1129800c01181d2500c0d4440400c01e02071107008045403900b1600d02407859a24294018003082098030a003080f1240100b420308803030b8004d0000352000e0280c07200f102e65805113441900020880480200c1c459403040c4480c0d00c00c1d007404205240701e80381c180c607030354075108000e850300c5142c4800411590346001d43c0030011403400b0414018500074a40c40e1100145420136103046c5d41000801801c8410049030310002e0442c0b0340d4000707201c404503640c000c144550313903803445806820404182d00c43c140c0740c41f0004109042080540c407100304514404180e501103003030050b880c02c8401c44010001c00013498a00c050080307005075489094200d1090400809501d41c2d030ba0b516910880305d40224002c202d02290410840c20036010b51512020181102403079480c0680d2807040144843c4540c00404039281011880481d0400c102030741c49186c4001d001543d50f40301c050303512040e01140814026400c040c00000c55007020486207024 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 554531402 1250 554530152 554530213
    0x231e0906010501111f0f0e01020c07030204051003140c2409041e180b0a14271501030c0b0304021f020709021c1b02030703030c02150c0309 61
    0x20360b441d100045036425070b103542e4604035020300a04010350740d400040c48590841500700204421261969130030403542ca540324002c45900400c15030708030742c10100e00b5400b6258100e1b0009090344400d085090401d04903003005000740c0e5408480d107040040012100c0308544102e501018020114690500c2409108025003d0503001c2c80903082c945801d400c070b01d00800000d01856290350400002030191058101c3e240380b28034089025500b8414040e4906a02022812080c418640b00034241c0410110017052142d202590b0720b021541c1e00c030421110300300d483c6800c003103403202c11510721404c2411400b0721085880341000b000001e29141f182e4156882160020004022030a130400c030320b07000c64010030004c011801100300c0410700130003c2c405000185244c00e0307001c001540100410342103e0790640d0709211019206010550743ea030020440310b18a074985008690320b110310704140d14001260b03010b9441010084c0400242000c580c011b1031103407002c001110072111406001c041c0c41418502d03c180d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 554532652 1250 554531402 554531413
    0x6020f25060804062307020706030e0705010e0d0506040b091b0a060507061e0209030c04022a010e101b0f0207140604031b0e0109140f0a231e09 63
    0x16010303900302640f01e40103180203d0f010200c000c21a001c21260302070610450b11901c1440041c0b681006400c02400040c00c0c108004207035140b030559a03030307820311540b4104400c000d402c1f200c0391540b034580d8060340d40c010201c903460b0505c0d01c0c054841550840d0007841c0d40c40b0341103140030402000705401e215030101806243d1003604004c01122154480c400c2640c00940700c0d044030315883d0940940901492140a0040c0c40c1c0400c581014100702d140c2c0c0c40035100703a0041c0700c90313401c0300c04030354a5203495100100aa100d80020300c07032040c0501724182020700d00340a0098400141180da0704490240320680450725104144480b095404485000740100168445d05080c41070f0039040f420420003601c002e04e010700b025981d070358018901c072003207040282c0041a4401089485454100ea074050000c194050011039201e429843c00088010b28040b40300740c1c660042185c5849640c050290000c40b1540c2c00c2c0c003135081003028156900250f0780d001e200707901d200081074804e604172001030150030208007415 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 554533902 1250 554532652 554532659
    0xc2505010e010e1c08030105010f0e0609040e10060b0d05090d0225031b06030c02031e0a0e1914120a0b090f030a0305010801111903110f0406020f25 65
    0x640d007030300a00742113402a5000d0f00c1e00004002c024100c2c04140c0c4aa540c895681d0b0402d40010300301c15901c205502880005240f100300790380c401041d1500b24000f60b5000a42500c502c0c0d00c2450130700e420304149040c078078203071020403195106801400c0d0040105014080c50701c41d42c840c40d588030140b078020030058201c09409421402c05540c1e2592111010014207101ca0f1203468801d615507201032503109a084145040102c10740500502108084ca800035500385200440358400d00ba03070f0b85440100035403002490b0041103001d072600424840d4040c02120380034040c7e01800803110f0050284041c903c0c4155a1007a840c40e0a2000b00303c0c0b51142c1010300342c18004c5d542c611b90501006031400c4482d0180001c04081c10b20100003410181c0d6885d175001c0f4065142c4440c003421580d044c40080840942003020450192201c0000403030308040e41f800040422203050494501c0c01070030342441a040c400240003e030a43d002626107543c0300444240d0f0f18855050495201d080110403034107421061914041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 554535152 1250 554533902 554533907
    0x2030a0f020a051002030309060708060306161e020307060615090506130b07030210061514030a09080c0c03062514130f171b1002030d020c2505010e01 66
    0x41481c40600b039a0b84041e211400100c3c081e010055400060348003204001140c8810400b854000c8a00e0400c0e20590901502098949c500180010304400c1008041240c191050f21028204298040c139281c1c0e04001c100c00940f41e520465081c0c40c510b06100c00401d6000c941c0403521031106444c4c0358006c410b0300c1c1106000e029044030380c1262405149100000e0341036014002080b18030320903070180580424044d82c00301110f9031504015000c0490b171000051403038201510b010581204035182e52690344002040c0090041c02a00034170160340400d0b01054000001041040c262040742520400d83d604080e03046444460b0170100e203503800003d4002d86141c000c1180340c051040c40740395103161400810034006020341c10b60284420f0843c501c0204034101c818012000c1107010034018005950782201c210b030440a0202c0c909100b10090001c401c0458020402c890342d600b50408150b484032000400180c50700c92504a410780310714410094242405020682d0f400d9032030507182c250f405030b11213004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 554536402 1250 554535152 554535173
    0x1404030323180a0f0803010e0a09030e01120914011a01030908070303051e010b0a0f03020310090b13091211070b03070e0117092803020705240c06040501060b0702030a 73
    0x1024014125070b1030104014a0428404c14090040c2964a51401d26007041d180001000122480e181030030310400030b0360251007082c8a03042440c24448040885503548001c0c14440002001d0001290b4142c40428040d0480184508030b401411a51069140150240e400e404030060440000304001e00c006402544605d400c5008c070200ca05080d0115112019207200030f81290f035074504017296030030035664444065600c00f810307480d0a500f11f0505030f8502c21809214081c4c07080345074076a10044419280c900d088030084c200ca00e0705119200d4281441818038400303030703e5000040d00c105544106620f0014042c000c07140312000e83d501d10b03034a4030402c5070440c001c0d03d1031364100500c0207450b03c02030948480d214020360106010344202d1400901400c108005500d040c011001d0043e1050301007034001c6407090032034000390703800382e40104200c401a0401c08110100465014081941c5414190024820b807040744039000802074240c84010b5000107005d1201c0095056100d680c0301000a40c04140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 554537652 1250 554536402 554536441
    0x30902010504051927060504020909060d26030a11031605091306091b0e06120402120706080103033b010905060a0c0c0506090303090603191404030323 66
    0x16134010754441454007082c050f05140007551403070601d03500d080503585114030801028200d80440c645104000411100c0000401442c450701c042c89140d0140031030442000044a054601002504100c1c1c1c201445c50b003041d5100700700356161000d8540c508180a046034001c2d200c03c5204400000400c030304480a52003010600d8011114003020b594a090034001d20307014040a10001c20060300c0b0908500c030b0031300460400c00801c084081c90311619100c070f404454901c40c0210390303540346559a00103c3c250202c0400d0440840c411003070700040241c4d0014045042c0c0e031081e941c44020118500c00328070300c42821400481b80070b0301c400d480441080c211850801204041c1400c0c07080030b5807a40040c205030001002a00400d07046021a001c002401c801d03080903105c00c0b117030380e03003810362440210b540e90103560318480c040e000000100d041841c000c5002100a940d40c0c20501100c0c2d86c41c03682d107000043c10f42e01180401d050001517040644100708841c009084440007600300c0d540c0780b1840450154105 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 554538902 1250 554537652 554537689
    0x60e041401180c090f0c09060e190e2203020309100c0b090f010f060e13170423060910120603050313150504080303070e0f04090605061003090201050405 67
    0x21811030b02140309400b40ca03015004081100c000307071a00d400c6000342c2e5950144808a44c1c9440d8030902043d030052468000d948040c906800641d2000c0081004034900401c0d480c4510130004000840b00e00d910103140c4500da03502c08540900c0c910414030014030080460040168105102c21402418030754038400d000703829450076611101075074a6021506e0300c10b444289058000d0200e00050440900444482e8103440004010f805c0c60715207104075000024120040c0e0014400202060003803906d00b240703102104416281d0350310381d99010301900c40091200480e200d401d034035008041c2d29100052b01c0140300050202c641d4203804030340480d0402943ca504440065650101001050040015140e01c03079074071009410f42803d0010000d80b80d02c0000416041100401050000c44004003e40e900b04131241403c542c0c1e00e1082001a03d03020500040d50740061801511b032050080a8020701d00564084d11804680312401d1411000d42e404c2030b00290204204010400113401e0581c8120754a9a041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 554540152 1250 554538902 554538911
    0xf010504140907092301081f09020c01020f0f0a0909110d0e01020c0706020106050306060303030108071202010c020d05100b0306060307060c051e06010801050a02280c08040f0e0a060e041401 83
    0x41c802171540d12521441000c440e4242c172812615541c00100c2c4642004030000708028168544840d200903034500d0040070030305d5030080f40e4800c041d135094058603141c50344802540d403680c25015007030059030052010303100040c05030f1134001200507161040c0080d490300c400c0b07083c0c50101c50454070005025986a40101590300300000e5250440a01480c1d0250020743d0000c1401490082014640f02000d0800e500c2600100010000601c00084070380840c3c54070005c0d0403480d12a800103a0b1440c00740740000e5003104c4e0350000b12081000200700c6020060341d44008101c0c03540d90383d09241e6240c000300d4089805174046001440414009c550006c02244104100ca2036080c2d180307010350003e02c400740d090b0040d03402840140040300e8203000300e5600a090200860514802540640c5079414512076007026884581c00064101e100d0340d020300301181c02094142e6142d40d10381e03011010781924400c81d0422a0725901040c042c0400d405100211a1900760325545915151148074500340008224080303507681c2d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 554541402 1250 554540152 554540159
    0x1b020112020409020901030605060c1903020f010c08010603050a090506220f03020123040b06010e2806030c03050c071e050f060a06060305060a090507020c19050f01050414090709 78
    0x940014000f0f807110800242c0c0728440c00700054161211a00000d100e0320051005c0c843c0c9c0c1d9000a48500c1040081ca1014480703049400c0a9050450541c400b000325402d00801c220000d070003018580c102c0b075803558204441d40d6400c88910882d03105400003010354028101046024500342c014000500ea1401d50201348001641ca003903903080d060104170090307511075030018610302c0000703840c0f01e8441801d14540c045180c41c3d90b0300701c203200c4010303c3c50f8140500d000f100340d46615020380489541483c03103a072501d2501ca80382d10300a01c80491041000290806040c0075038079110f07001e1240a080f040030000d08200460352444882a101852048242400e0300c42c04086442040421000c00090002e009542010705500c01500d641d50012404e1508010070b0040700c1d143c4084c650219080c990300061952a13941049041601d040a11940802182c0344600d8240320700d4038201c211102210b0310044050414010344d1903004034070544102414445070640b280c2001c140e803d601c4140e514004001548 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 554542652 1250 554541402 554541437
    0x31204110406180e061012060c0e09040507031b06052703060a02030a060f030206180f0a03210207060c0602072409050106050f21071205030307030506040c1b0201 71
    0x40e080f003140078068640111070503054081c800035400118101c24004900c6c100310b44007820140400c0024034441c0d0301c4c000c0a019034411602440000c0b00200040040d083c50b00f070280d980c1c00a80000d07141503590700a8928070381105a03c40e01110f43c2900d520381082c021030082c4840f401c82d100281c00c40300c0481900802641c090108038442c83c0e41070001030300e034204600b03204100e4855400981e10341005000078005690b8020540d818040b80100c00f800d100c0540d40850301c61a01803000c60381010803910088200614180a04951800740a0f0b50884544a0380103d03030b01c500718803c60b4041421101c0c620085113090300208101d0740201040482544007400c00c9000d162039000340c3c620584d0f0b42000200f000f070b00703008903401000200e43d540880d03440100003d60149500940c00200841c012060304107403010700201c40100080b640c085150030842c10826245c2c0d001f1546000080d1804000410514091142100741d41240e541c020140164104040e03105441c80d0040c1d040c0114084081c59409 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 554543902 1250 554542652 554542679
    0x61008180102042711070b060a09050a06032a1a0712080601171506070f12021c09120206180907030c030e010501050603040618061418031204110406 65
    0x407401c5000c10740d5113035203030544000310354048008440341e09000581c00e544060005640115410010030307241a103484000a6602000e41c0c011060705007064200074020490381d00000031240181826583d00030348041c0c0310603025950900080c2c03440807200c18801d0722000d034021080c000c1400c4c6024a0f00c51191503040c0354100c1048200000b882c008104902c40d644046000c0351010142e0070300e0014100004000c503120840c0380d045000d07003004a0b040050003940041200c0c0399401150540c3c804900c4a4001c0d03c500d00c00881c94050107000001d02d0289100f00d04d50070803640020030180c1106115070070040a54048088078132400200510200d250350b542141a0180484e605c0004140458140240540c0d0a9141149590b403410004100f41e032a4401200d50260b8021400111244501c2e40d01800d00c0c240007001e48038519100c000c0d0b9000c200180498005e0421203d0305a003c010540210f65030700c00c40b82415406030004020070005041d107800e5840a0b070004002081d00c50300c2c1c06640c00c120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 554545152 1250 554543902 554543909
    0x41518060612021f30060807090b090c0a030b0a0806090a060606020309030a0f0f15060f0e09100e07050d1b05010311040e0702151602010c020606100818010204 70
    0x550402c4200452500324410010004460038698800a2000d400391541e5040e040c4100003010400da591880038000300c0c032240c08403885104026441d103d07041e807070f40c0d84064060b00d074507a450084003200310304d44085c032580f244504e9500d2516185070500114054100728600380d8200321800f1001c100322100b4400c03507200f8030098006160b5880340342045415254507510110640d0001c000b11100c075140490078802190300011600006c003490b2400c0b00c1c14148201010300b0a4008128081006103184c1141007111524130018400c243c4880003903082400507a040c0265034404008051215041e03008990080c2c20b1070195148640c0d070304089110030b00a1316007100c241c0b15083c1191080110101004050b200c203203410800304000c0003212445101e107000c0c08800001d16800500020310801480c80e1540d170f440080c20f0341d8200b4080b4801f00344400c6180c54059420410b00381e12003407000031801d108160080c00100408074482c0182c82e8184041c1035400540031040406111810900062005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 554546402 1250 554545152 554545169
    0x91e020409050411040c0905010513090612050f12030414010b0301060b0c011a0f090910021b1b06031602010908210c0c060406111902011a06030415180606 68
    0x2503e041c4c54585210389810301c219115601d40184802c501d544204d040083e15401e087c034541e50540030b080b1100000c401d500c1207810300d04000d4045000311403104500c800c01d11071003c4842100e140c1a030319880c0c0c440780c0030544c5880c8007800010003043c091003140d85c417416404000146e1a811002087c00d682d2a03803c03900e402c400000e41d4280d800000d2007010721182c4515900e041544020002030a10010a580300740704003540700200350900350a02107243c1d031400e4540119070381c0402c20200344906843c0380010856025019a80c401a141c031088916200d0300108034515551310141103080510b12a9070032401c5641c0e910f618800200414010441200030b022014404000001a01810200200107048041d0705002213040040009040c0d600720364000d4000c503070403807000302c40d5445005000c1c0748101d500810010074040e50f01940300c000d600c4008140c81c1480604041030059510050718000c0041588461954450503290710406000c0075855100302080020b484000640d1b1990300840b44 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 554547652 1250 554546402 554546411
    0x150a02070b15011b0c030611120f0105150a2f03040b04030b010b04031e140316050601091a040e030f2701080f0601210e0106080d0e0604091e020409 65
    0x899a044142c1d110030310448500880000410740e00c0d001440c041d841b00070001764031002d40c0c02070380320880190341c1105088100040300d45454160000900028450b06020b85038104400d03880d10189411240902c80d20340700d920b044503458182e18114125181482403039800755070440310708401480144004c04001501c10345840c01c5051480407201d06174132004140108020400000302840703c101c0010303070952100c042c5010b80d818100c00550450740f201c01c0a000009076a0410003c210400564030301490444809030f0b201d070294030860700c0c0c0c40a100440c20107140d45444d00e140a8111742407c07115030307045d00e05089030340c0d03040700c810303003000c12883c8002400d085074904140c1c82584032044986d0918080820342400b010841c00c102c03020f0041810460610514145035440a2444010285081042109240d001c0c00c09000f000c43c1d0081d8030786401410f540c842540d01c83c69500c880d020b8024400744c5418a419401e0008018144003900e4031009031135070754068102c62002c2e00040005640205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 554548902 1250 554547652 554547691
    0xd1101210b040f0b0a1a0f070f030207080609030702090c0904020c031902010204060c0f05120c030408010b100f0807020f0d030c0e0103110a0e0d0609030f020d0f02150a02070b 77
    0x800e4900120aa00d121844c000c1c458a2503540e480c408002c599503e114100e007546202e078040c1151240343c8030300e6074010f0002001e0041040110320b03110118082da0aa0300700706d403601c03025a192a41038620b250580d00c14030a28001d490001040d68010345000c900901c0c000d0050003040a80e00190b207041a1900042000c00d8880c010100200d8460074a1000314501070600c08080c000c0c504100020307004a03489140c071800c0260811400585040814415817108100c121281e503940c400e020b24020707542000000380d401e04001d0780c9410041300c161110305941e030ba290300c02c682440c0020200c0d42103101d815880b80701d00000380917165401045907000715500f00b180402070040e40b0a061154109071070440c540740d41c0e84410b420398042301014070b4401a14141c090004880401104c00504183d150405c05810503812054a01019045800b580e4039107001242c180c034044100e02c00790300980c100020841070060b41c4800315030301c56150240182841015240c0e103405046c200e405240103001c46411a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 554550152 1250 554548902 554548909
    0x70b0405030717040b0d0b06120114030c03011a0613120602031023040c0203040e0f0a050f100e070504080d03050601030e160506070c230f0607020d1101210b 69
    0x100c203c1108100c0d4949440c00b20016102d1003200c0c1e04080c40f641d42e80d008240e6545c0d03c0d08039420303040200024020741d6103500c0f407000c400381303c82140d031712038450010030f54611304042c056806065952228884804140740034002c142d4002c0322500500909400d0120300241030313408601449015440042e00c1c0c1c544080703012940800b43d003040450080600c51080805010010801e00030010f49010070070105110080e032850080b5048200301400c01c104006554201e804182e00c900d00724039080c40700d0340b01c0710714107a1404002d88240d04d940700c030030301c09021144024184940000305031800f07502e80356031207a5690520606041602c0082d8984042c0400d42d81e05004601d032025084d409003400e40740c20824003060f01c01e03611545002c0c9001052840a002d8104204070042020b2105c404104142908111495440441841c132949012601c413803036040030701c15144050390180050b280000a5120f01d182c21058085090420030041076101b00c071703040e1900e0700404a241e0f047c0130644141c0c00c3c081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 554551402 1250 554550152 554550173
    0xb060d02030a050109062d20161104090209010311010509062107090501020a1b050a060c03080709380d0e06010b1908070203130e0708130b010b0f070b04050307 70
    0x40c0d607c03010711207072504400c0a002c45140d450b00165a40007483e114511041401081d01040d1100c8021010607500d208a4404030f8419180b40b0035420807140a40d504100b00484ac02000040e4002c0c104500500001d800703010700b00c40400c03050400f2030030711450100159590f40150000002402c07114202e1007031031400801c464102159091403e049818980000c0d51540c0410018080d0307080020080c580c1b8005803c02009070038081d20501486071a140c000c1e22a80190310101c0005d005c1400250306035124040700d034240c80c601030790b01c01280660710103047c3c4c0c3d40c11200609140f0070710002414a40b15038900421216591520100d03d01040c1107465040c03180503844650305100810452003480c5102e01001a24080d0307041038085074803180b0003286140240000c21000c1d11840a0101d004c02003500e007644950816503404200e0b94544410145120b0f00c1c61006108a41c041c0041c441d0f5061040600203102c030707210055050841039180c1d008800d000386c03401d44071900000303258030074459802c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 554552652 1250 554551402 554551421
    0x20712031d0306060105032202100801080d18150201240f0b250519060506040b19180b130203010303020d0512010e0402040618060801150807030b060d02030a05010906 73
    0x10340030f41c2c138000001034401d03c00240204943c42e100400401c01e540101803020382c894000d06840c00110b40038101521920080c050045144074404107a0003492003540000800c415056404405034581080701d40d0b420345120880080d0b5494401c5900d015600030b900082c0c3c0940000940c60305407820a94803200011f40e0483c14214204011041300700700307a4508030107185034030006113000c1d000c1c50603e1810181c8610704460452440c0c2c100a0911401c0e03080075010700c104603130070001c00345207008001136540c03038950080450f40340d940200300c04038540d0180c60703948040d00c801180844000c00050013102000d00c41d91052036001c00180f0625038100483e441a00c0a420141d00d801b84200082e003c034241442440d00c0401e0942c000340440d00c07180c020200811544d40d1a481003140a821040079000e18007503a0f103290302c0c055059132541c22114020040301e0a1a001c2d00006003142c44283c001480103000540040941c000b240050b10708100a0388180e00400000900c110340e850311405039a01e210 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 554553902 1250 554552652 554552659
    0x110402040e01050607031e021b0d02090a1509060303170703090f060c1b030e0108060915060306040917120a140c03070e091e09030301060816020712031d 67
    0x4244001e0031240c40990540d6011035200f0349440c1c0030302e0110740c0c62850507404203015400d80c0800c0c01181c1c0000d191101c0e410a8200c0b1460909a40d0038080701c1e40060002942c803045010215108184603808603c0716a00b40354440c45c40340d100d89902003a102c0942c030880c0000e1101107a003102e554208001600144203190a01056070640c482000030f2081120141405650303600040c2c109020b4002c09110382000030f07800c00c42c4480390501034442e14044020b10702091030400061f44602e840600300703104034140a512300300071b00b0702c3c403d000c00e0380c00040070a0b40159036240e0b0b982c08140c2100a460314910b040c1a40e41d55040c038403001c0031590901503c0d40c10001c0c103001c06000401030254020b603011000c00c03101512541c94003400c07111380c040d030000283c000a0395018482030a04108482e194251352440c80701701e40c4c807180c10a40d80c030300c424480c5200085544000c19000d1940040f6104954241e2040302c403500c0e16550790380d03041c005403403048010840c1e040e10155401407002d0304121703214084 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 554555152 1250 554553902 554553907
    0xc091e0f09030f13090516020c01020d080a09080f04170d0f08070c0303140a0605100c0203070e06061c0606110a050c0402160b0928030c0b250309110402 67
    0x41da658a0207084041503d200c004075040c8613051915003a90024a45d42030280b0090810004840000e001d40810741e005015207040f5064035400000d40045088080d13581c6501d503502ca180301e0307004040c4980f04a480010801032340b040259040d0280000c0d041c0841c40390440d190707010889241c004107008000a22900760707100d242d001c3e007014905500c034169040072a5071b5540392408400600b03d0b0391404619420310000d0000d49442c41e440042503c1003512410380310389c2d410f40140c034220b0b00b0180095066200030000c0c48100103081189400c500054142803c01464034a1030b4000748406030040401030781e9420030040c0d568800d101410b80f60040d170103040060190b8640c00e84400d801603825000360340000311803140c0d80c1c0284d038500300160092a07801041c10085a05512101516201b42421142d0794402c00030103206444600c0c603d5044c0c490306003241066070348112050000307080c0d8000141e107052590008803c0c03003079849264255500001c4c80340c081e00d4034010403075040403485d004a105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 554556402 1250 554555152 554555161
    0x403170d2004030339030f050f0904020d090b0103060e0c0405010605160804050a1202121203041b0905041b06080105010e010c1401060b0711030a0209180c091e0f 71
    0x14501102c0503030b42c151400f81058444004100000b891031000041203c0c904c1d15401ca410400294442c0058482d80d122481c000800400719080c2c0158031001c0500f8808010081030b524044d4014105d240049001007101143c42e25000080c400c01d03801502c80c03a45508840d0009401801840d1491000721410440342d410034800500c20700a1070092151038403200d02850034080c00605a900070100100415003264445650358640070384607604038010030f194446041a00c60110701f844c50075550f645401d0131907403117403202c40f0540b5615000d4651490f0b90980413814500c14010541700c0c03800750402c10389180550000f50b686074500d5100104029845005021580c1e22003118401250246802d081e801e1090421085140031f00622000c04e43c60404005400f04900d0080c1500c2400707050b51402070445481455103417040c945c4003e6001414000040003a10400300081d1201d00c00d108642400c403596000c01c0400d0020784a020b000f00960301101c80b10800c00c2e102543c88200c1e0300034200e00381003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 554557652 1250 554556402 554556461
    0x180901141501030b010c060c0e0906060a0c0803040309150818010c020d140d1a1306060906031e0f02090a050a030206040b1e030a02091f0c06020a050403170d 69
    0x200ca074036060400d9121280250241e10440ca42901c09070048410004203c044201610002d9410b5081c0c4c02006603000040c0546004d4050322440005a02c6008400e081640ca5900c20b6200400840901c5004100824075800d80e6000aa1000240d1100607450030107894005003201c0d0403a41190681c1001000c0e240c4650100d42c07890b103030b40542400180200c0904520204d80512031180a00618000301c094040340e0b0044444206941581c003081824500c00c6440266101d0340102c402280302e803101084428842c7e07105084c0e0490b01c07500c001d070118884140100782d540104401c140181c01207450802858100010740007404100e5170008a41e1450f4003044580c019803140800705540418010f4035514110300c403960200448920139074914041204100035000110600e0144442e04d4400c00b003000300c2229280000600d89400c071081c1d01a0751400042d5202e0400d80c1e007045003d01001000034030003840c44d001100e0b1a8a510340354020b07041420103c3c1c840300c074482c9204800304031510340c154 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 554558902 1250 554557652 554557681
    0x40602150a1a10020109080705060f100308040e070905030321090d0c060b2701030314090306041203020415050414030705180411060a0503070e030705030d08040f0218090114 76
    0x282542d0310f0310002c1d034030303030081c2d0042a200d00050004400020342e44104003000c1402031080904000320349a54840740303c100704054035030100030034002080200b4406c00302e48101d16a4031aa05240100c8126240c5000c80e085811281d0000c000210800b182041324078075586441d4455030650041c0840400d2441c001c1250300c0c07006024000540c0c03022102c200e0748510500d08a281c0b4207003c1584980d10150426000c40000d04c8190002254640004054000e580c101e440a043c010010501c40c1c60350740b034075000320b03221107503440034107900700000585000440e8040d01c811a00d910380039116031034000481d0941c035501003400c0c403d810101c01031246030784411242100c4d00000c2103a2040b0342d6503141c0790000110360210700d42d0004d00070402c00c02c0203621400842c07081d040d41e40c8412400c200e00c4103041d42c400c26030103541e43c950060181510114401c80485601034006d8180c0309d0070840b0760700491111115004111420360420003000720105090147d40c007440c0e00444600300500d001e600103400b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 554560152 1250 554558902 554558951
    0x2a0b10150203090d0c0305150f1003120509011107080a110303031018090609081b060105030606101211070b07090b030c0c0f10050114010206040507090209030a08040602150a 76
    0x60080500c800c0520805c010b421001d160b0060842d039a06401c0c00d0010360031142100c0114000c4c081900190498117000350500c201c03036000d1054603148802a20a40d07081d000300140504005c200c0c24034142004007040360320300408005014127212040c0382000c60100d81c6801c4910b01aa0003003050002584041c00300501300c5136940d09010444030352901d000090400541c02a001c035080074144400c2c072040300d00038051030003030784070b40d0340700d1200da10301c050b103c2e002403040903803540184c40020942e06040c055102040740c00d10f00750201c807015855200c101c0310045500400340c41c0200721079040001c8150101d070003503081e05003040340c42d01d0121506610f100080c4a9880c0c0080401d083c80385007410020407a03042c0d44401510b583c11615040c3e04000d01007446140340558454050900c1c550010854a00035a049009025108e084c2001240650b0100007440c2d05403013100c00000c08181c190001c3c2c809845594060041401c55400520308000064400c0014078500050f002c50210b503540b000c0b452 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 554561402 1250 554560152 554560159
    0x12050f090d0507051b060c0106060e010801050d1709010e0a261216031b060b03060a020921071203020303071e172e080708011b2a0b1015020309 63
    0x200111001083c0c05007d2089964001d40c2440c0f40802d0341500b00300705040980c0203a89980d03d0b41e98407810021071031151203020704554035080d07000e00f441c60881c005015109044c101040c03482081d02c041031841c0c44a5101a41046800031060036820040e000b054414500d9402408116008a4454118070400130325212034602c800402c0300701400382041443c0580c43c000000e0358102d0500f8504054081d425149220f4050f01e00010311aa00a20075103242960140140c9800f50b41605c00300e0400c0c0442e00d0313191181c818150000381c01d0824800c1281050300c40d501945d100e05003440040c3c0391101c00d0210380d07060803030708101818155010001042900c2a94420300712600e40311b0800250140e082101120000c45121048502881e407895108540301d4400301d408159a944001e030032601200c28101c42e10040580444101d44a03d8a22141052400c50700e0441d42030300070050982e00080300100c03040b50310700003000744030f0b01c0706003e510041c1200a8005a03201c1d0000d4003e44038491640303054031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 554562652 1250 554561402 554561443
    0x4170c01060b0d0203180303010602030a080c0f0a0f02010e01050c0703050304060b041d151030060603140f07210203160305060711030a08040312050f090d050705 71
    0x124220250840300c01040740015090b40e4000b1000042c01940c400c840e04e15810302c3d0103003a01d00b0a4000001c40e03040b61034a50180d8102499114100d40290740031f06000d2003904240408884007036010001c0081032100d480e8481d4645010b1070190135a014082200038691521013001540c00040c81100c42c81541407030003a54954461074100001d01101d80b803682c002d40f4205048109030b401089101020135034500f1102080300f0b00c0c0071400d0060045a0055200300003000810131250f49002c0b8040d203409001c034030000c40500c00411381810a10700b07410b460f400d841d1502041442010900d0300c440f000b0030806450b5124110003040e65990080c40b81080b404c662926601d03030b003200080c41c1840030768010300f0744503041c0c0d841070000c804500501040d51b9038096103001c510190300800d00d4441b0150320300061400c208145006a840040040040e824031881c0c40c6010040b000c1d0340704951240514a8003411a820b03c0340000b8030700b00c02862450103018081041a003c02d10016451441c0380c42d43c01c2c07258 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 554563902 1250 554562652 554562667
    0x2060703020a0b040c0f0e1005010c0f290109020c0a03111204080a0605010605040609120303141f050612011707050a080607020c0103140403030b040209061215030102030417 76
    0xb4900303001100c01400e0019403005020420a0440d030a1080385c003480300c5108610385548a4103600c080582d0701010244020200304030a50241460280f640e0280808410703281c1c807600c030b00c02c03490a545045802e42c0c0c0d10308003102c0303807417051131859024084032441141030980e41d00380395a0740d0644210240c00c0c0725506034071440b121000c0180382c4076024000815500d40d035407410001d40e16802c111040722403a00784400410343c0f5104e0320a55085802c5a80c400100c0d0789401002c10048620341c009504046d1210800e144904407108003c1c041c2d080c6401200c80d8078140b48100341e040fa25900403901c50041085050b11908a03125000d040d5502d82010b05942d0f0301e0042081e183c2801644121703001500c0e02030010b184800812043d20500c1e0580954a01d00444030044044850082c13600860862000104010a1023644424445e0398041d00041c81c14100c01c0c001a00c0c1d401030001607210085042c10042c0403490545910030b8207c0c290000c0d82142001d950b106101c02e503564101444140c00301c0c90340e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 554565152 1250 554563902 554563907
    0x908100e0106080321280525110f030a121a040c0f0f0f05030c0306010c06180215091804060b0d0f0b060d0b150d1205122202060703 58
    0x2200803c0034204403a65211402000150412442c40c030542d00a200400651418032001d10408151003205500752641e00400c400c0000b0302025001040d03000744500c01e0540c206036003d850344d0100107510391125000801081c20f02c1c3c0700c10300c10007041d260400d000201056821040b50702500c118002c0100d03c4449541c581001844021318441c2d206040c400b9081c0d03200c0c0c010010180c1825540c1d291800d1a1341240203588200c07201e506500003035401c000140601d10b041c1c0185411400515100380d0650070b03916001c09a80400081d4a003c00ca800c2a040c2149409141000c0d200e840500e400d0410000d60002a041c4003144584030060201e0b0300040c00304582d07680110403040005018481d0089682400c0851808011088034404040e42c0803540500e0a100e4144109a000c107584100d035039216007603e102074040c85003642015048a20900050b4020803445462000769649622008402c40810398010040c05182d0401ca040c0c020a1b41c420801d030380720b00d0954050b0f0f2400e41d280c8052408 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 554566402 1250 554565152 554565161
    0x1c02011401030b040b07080103030507080c1509031902070518062209033b0d050f0d0801050613030602030c0f0a020a0605240904020406080d0810060908100e01 70
    0xa511035151880001c0200f050810845018600030314031a0b00590740c3c4602a6001c4030280400347c007140c02402000006246007000341007044c50b10382903c3c47d42110308074282c4040c0c829501c200c1c0ca40c00200d9600682400200c1c60160084d05100901d4118585004582d40d28284a050b114040c0e02400058090700e888c03900032000c0200c248100100404050b8480090500d04e6046000850726000140071044920403c01c455140c2e180c410144070400c550440c00c1c0103917210240d044910405641c0204100340101c0c0c4a140c03074880580700301d00c5e51080040c44250140c10041c070032401481108c1a445540b00c031601540d40c0458016600d0326507800c130840d207010b0706400400c2140005030a848195001c82c105803640d00c0390100740856142c01c840103030038805000c4401c407056001c101400c06481c10300c1d1143d4100b80064400a10184c0ba08d284d11700b03101f01c07040b407140412840024080402d41c861045401001d151600211090034800203503103c118401001a8107074461314075217035000007940f1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 554567652 1250 554566402 554566421
    0x20a0308131a0c0f0c160504090b13051903050405091b03042d1203060e090a0b0a09050106060206330d020f0928111603050d050705070b16021c0201 65
    0x94880d00c851800042c96a181e114a100081b04001414001243c0c00c085c000e080085621440c00c114559409210828058040c601a1010703c54200c42d109031001082012820390701a42c0c07040d50b21800d110501011030409000c0313022032900011070030786610460003a65005503016030101506d0040b40518065a80030780320003421210a25004020414051109008080292000d11501da5110844d0a010b0811140040c4036004510305d0b40006403409581035009040000024400166841d01402c456007a0001005644840305112403c03040c80010720041c01d881070341c02008010010510f00740c030340c2445464050360030119424119511400340a000d0701014003034600d0303440c0030030030714018420180126040000b0300c4011192131015001e50000340080b244031600d8030a40742d015a5070b5103035030304094080203402d100c42e005201070350084500079280c03a0307501911440341e401c0201030100007074003d00c9100001613040100301d03008180c0c6440a901c0107140c90481041c3e810907805404200e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 554568902 1250 554567652 554567677
    0x2030f0304030c1205030f16020706030903180305030c1506010912020d02030a06061707030206071e1505012c0601080915090109050d1706041503080703020a0308131a0c 74
    0x15a90846504c1782c00740d40304000000e60078443e500c0d96080f50790314840b0701000f9001a0000c5809000350b0703002c0e400140000340f00e40741c0a50090380441d00c1065809264008031101c2d0000aa00c0c8100700c5e04102031120140302c403904210904002c4000b03011481140304e55440b4100300d00001d0190742d5450340c0c0701c800540150503619107504d140313170200050a190080744075400c040801880e241d00c0019800c401d0700d42c06050b01e840c0c900280c0b18140451510701c1d016a011051454120010701000b0700151545071082000c03c895040c450b000703172001e02c1202001c00f0400f901b8011600c100c00c0244641d0030400a00301000c5070340301c60340000e00301202142110701d0344044d103050260340501548000106030140003610b500c08056582260b502d410918194101800a0041003207490140c0c001c5205504404246030b0840d966566005c1c84c2e0011481070300542c02402000c001d154014207002d500c959061080c180f5002d082d61a5400200401e80320030684640000107540e0321244006c0791280c200c0c24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 554570152 1250 554568902 554568923
    0x70e090705091f0809070b030406020d0915020414122e0e0a0512070312380a05152514030d0f0615030e0a020a1e1502030f0304030c 58
    0x400800c0f01e4480140b07038100000342e501000031194640442c4010981d0910013549185131102d4031814069080341c0c65002c1029641d1b8407101c0016080b40e50340c0c41c5040c0e02000580c03124501812640320a04001c40c06000d540b541c0104a49407102090170170311030f4914403a010160740c00384600c00314400904900d9892078900401e03155001c10004000030803500c140100e9a904442100c646024002c0e690000c0100c3d1440400c45000b0446800c4144142d021802c040a04100d4418800b25000741c41d581d502842e5148201c009c050411045100c003901c416a101c82044d40088220445e071f100b00f80d40a440c1562070000d0030030400e8188007500d10540c021111601f880f061548042d146d0340030501100c80c441c81c0145e020403126403800b03618106c41060401c0041d0303030320a07641074003e1700016809021034059134484034010f9481000030b40180405040340301d030000d5940388481102001d50030580d420102c01c1403840e02c6642c008100c5058040c5006420b80b030b5140e9240c00d81c4d201c40784050041165090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 554571402 1250 554570152 554570179
    0xb060c0318060a09170a170405030d0c080f07030302071506080d030605090f0402030313060302040810140c1b03040b070209070c03020a120912060911010503070e09070509 75
    0x406008003800c0c00082695081d020002c0200610440a0150201d40024801c010720f0200520301501c090707414042d40d61450b09a0344059000041a000d94200b00c0045003d0085003010000404071905504026101c0c2c15151510070f000e016000c8640c2c0301c0b060006044042510030b4054a14142d0301152070b0304030204406146019011a01030324065106485200038514400c1c020700d0200d034000f405c0d003416038441d4030860480c500001c1c42680c26220801c26a015010200e0103940204080e91700180c40e142405945410240d09040c00d0002034104951342d80013001c500341080d046071082d065280c0d07400050114180486082d5030a00c00b82c00b000c60000b84040d0014010a1182c0c400c445500c070075600d2070703010b417440c48506002600503800f01301d80c40700003002c80301c40c07035041226401e08007000ca80e10140d018203807400b134004a4540791200c40000c01c0003401718190001400c00d082c040e0642c68161001040d00101424003441140c101c000f2500c510f00801c1210341403000544582403e03280c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 554572652 1250 554571402 554571427
    0x917010c020105071403040f1403071211070b1b0c0a03060c3b19080c030f01110f090402090409140d0302030112032601080d1704030e0909010b06 64
    0x16900340400954248000619014400d40400c20745a0030403001c0303421601c468036804503900b00701c2421030780101001080340d408101000600f0100b0300c550702040b410403075110003c1460000c58016001035200c1e190502a21085c54203641c07090801002806105000c02c20a030319092a000103150000c0180300c0c08414069070790401020250341d600d9411581e55103090740c9010f603850355600030180c56110a6000081e85040142900c40d2008102200921a01041800c02d0744268040030042e031004074010305a0809211410740082c2c00780c000c000460400150140621854034881c41c13003100000d4000c4181d8556041e070f0f0280c81702502c10441c81c074091801601c2d4807001c811a0140e803087c1501007001030312a000303c0b8140d450424213220740d42d0050303900384c81c50800c241140840d2104440444907140e100d0302c03014020090038000b4000c50401140207400800510300c60002d4411030020030010a4020000c990704010540d80001141d5a43d1220790040c041581002c1d8070000c0050240c21565 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 554573902 1250 554572652 554572661
    0xb040c0b070c08011109060d091406070c021504050f1203040306060b03010302130621170a051308060402030c0907211514180601020a050d0306090b12120a091701 71
    0xf00c0300c01c02046030b209142c140358000c0c01001c0078168403410801c2507982c01c100d160440d04000e40325103a03903804801072500440c18030008882403400202003025000541c0340c0013003070804080490700c09a142a0400c2c010034114031901d10582e01486081c0c5140c40b2110040007290021500001d0070019240c45a560f100290300a1006031320840c901010104e42d6516440341c9800c491b0510345040403030101c81003010202034408006d42d000c0701c203444010001403160004080c807031515540c0d69541d003040707122507800010740c2e0458242540050100401618001821b6801100c22a458219561000710489880300f0007860041040d010202031b4041c0351301900b0034410343c1b41994111081c42e850741c00308507944030f0f030400c034030f42c00f04604560b02e45842640c0c001e5904aa410700c1507c09a40b1603407078052506e6030b440d06290019640d4081009a07000c2c501c9503161a18044031076180110b03a4440265a86510030384045004400046e10070080c2d003e5140c51000f071140089101505061700320850003031 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 554575152 1250 554573902 554573909
    0x30f0a0203190f08091c120b040204090207032a030e04020409091a09010c020a0807020102070b1c0c08070c020f0f0d210c080412060605060301090c1d0604030b040c0b070c 75
    0xb42280f0205d008058041085c9101c003041072103410000f019031404031105001102d10704142a65100c02510030b89460000744050a80c02c5005070340c821031890002e12002030150b02039481c1040b07031109403540315002040000b0381d0701441c00c500c485100100190007480303a580000c214031718042002c010042004060b0078a012001582141543c48c00c0e40582614034103c44c50b00141c11486401c8000740314803014008180c0188111014107859100c000e034603078898018561078614800c01a150220039004001d02d84207280b41415203400e01450203400c00794880c400134401c08110711286002d840c0c805000301c203000d00810009141060303080c47c0e6010b0a02241c8003030a448160400d413200c5015891440219511540451500e480c0032098918041d401104548080d202c140014003540c0e48405076010b0034400701d000400820104015140d420b103028914010307035816800e1a55a69030000380d90131250084e101818a03551031900f00030302c20b03854000e0f00749010b010a107523040c0208507007004242d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 554576402 1250 554575152 554575157
    0x10e07090b1f021e01050709030b040507031a150f0913050f010f0f051605070803090f0a11030f06040b0a0b03151f0b040b0315030109050106080c011202030108030f0a0203190f 77
    0x81e02100002117099a204440c0300c404500c940008000113100070701020307401402042640d071000d8807965550210280400750610141c0f20704140080f01d5240c901d41d42e0429412070325041002c05550110300304140040401e40d4600d40459400c05201d018009010790f061900e00070055500c2071011500100030703464044ae2180d10b04000030743c42e01550f03a0b01c0110401c8035102c0c14109519582c510885a0004089404901810007000d13007d24040165861142c460360302e8207902d1007110f05052501c0842c42e6409240c0d80304a0038480410544049590001c80d040300108144104901003441c0000741208205101c109400700a41c007459410000310f10019580c8800341c49548404034032180c000c2e0700402c4400c11080000c50322078207003240c1242c1541005800030624207041d45550b801c46074140e00c0160190004244803c0c0344da4050380000300074030355640031410740d414210200c0e520700070800c4a0500d42000629800454000c000b40d44040c0650104400030890f03a0200030010800001d181c0d01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 554577652 1250 554576402 554576443
    0x10e010c0f18050a0506070c0e010e0712021309020c01020403050a1401050c120a0c0c151d070f03060c1809150b1602010f0e13020c0f010e07090b1f02 66
    0x80b8a0704a41250b03048800040040c0b44650401c0b081003c0c50780701d40c7c001c0341c0c000c80e03032540050001211140c00d4000c0c1074028500d021803502c1c580103010020082c099201040c0304100f005100c5281e10b8841e8203440c0d8145005845e2400c0800c42d50081c8074941010303090b0310800c0616000c0088156900601d8034a03800284040d84030320f080003140f07005000b020b0ba000c4008100084008913950b0100d0b48c2400d0302e00c2c000044d680151959554802c5155400d80400e84800c6d03041200c03810070340c090703024000d090000c0010074a8002c02d1034404000340001403140340c03210321004100c0d1103030019108581004114001041d52140340d00010900b1800c2c0c880c42984e00800065001c1602d416a00c102e60a601085403682880e401180e2180d84a4100d000344050102201a43d0b01c84400c00039054201401c016554a488c0204502e08802c1224040e55607060441c8600d01e00008220913084402c4500c001ca800c0442c04000741e117413041d00c80c80780c0d0500384000c400c940c0c10b54002021104072035002480700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 554578902 1250 554577652 554577677
    0x352080705040c140d0908090405010e0609101202011422150207030f0602210a0e060f400f060506010c0b13170a0915050c0618010e010c0f 61
    0x41c0c1c400c4c5011440c1140c40424403002c40000d21542004040501c18042c00d80b800e031a00c0000350486d8802c1c0c01800b0b1800401d401c0000a0402107003054000341e581554241407480c1c141d45c0310402c00305035070090402c1294000d0044406e0004203442d100c00c0d0105202600a5a0010141820081d44134040b540e04411100001040c000720320403043e42c2d008541c281032040981c031950041c0d4089044100c00306150080301440c004110000c902075500f0000201d01c0f0203a100207207141000140c21888907140c5d0300c0034000d002000c808400c9407240c41d00c0e0740c010846c000b140d110000a80c00440c0d8000c200072540c040040010850f60400980d1140b0b0302007109407103210044448020040c40144890170400114100c0e500c11056400c510313205038100c64010982c3c42c1120f00d6600180301c441d01284405601303028240f443d040b40c004040c0107103030041c00c0640f41c104c059a40d201c0600b81c1206c8220b40d82c41801d8240b029001403280b2942031009201010700020000d0080440300c24400004000c940e501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 554580152 1250 554578902 554578907
    0xa1a04050909061024210623090613090314030106020a230d030b060f13030302060906040f0f1109041104060b040305120a210b0352080705040c 63
    0x10103140b4642c240141d60344403200803d481c2c500d115020181281d1507503000c510148840d0207032001402a50401802c000d05200c10408c0300d00a4400c801c3c41910020b0030000152580d03400440782d200a55400310b14284241016140814006845280b4120010010912540000c1c10401141c03003010400000e070690503152044e20071940412045401581681c04164420340091107103100090500d4640685403043e00520f520a0b080e890a04161403010004c1c0764060100951002c080750203055280b0341652680b030350f2504210018400c01d0040000000e003c0c41045a0f00c5980c0060001801405e10f03003840d0071410b040d03410b918800c0e070500101050640313a110a0350100c03603006c40188086980a07106a80c140c00984c50601080310200c0c50308040002d0304000c07800703100703003c20004903146604141824401042c1002e1f620100d6040c4401034852074480020303c1c85041c401c40c441401c185040003542002c1140840d0400c500c043d40401c0c1d1042c042580402c5401c201c80c100b10104042c2d009 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 554581402 1250 554580152 554580179
    0x1b062601030201020309120118051614090103061a060a0503150a08101e090311071d040809031e0706110115051905040c0f1d0a1a040509090610 63
    0x3c1c0160014031200c241130804801086d1390316058000450341304010300448008040c21302c010b80303055010305914083c82d5040410074014181090294188a0a0201040b07034090107101c02003c09d81e8500400100302814125030b13072550030041045a499880f548001d000381c100781e0300700c0402248a42c04080c00c1c9418001d6a003102c04800180a0f8924980701060040080c40341604401750f0940007504009401c1c1b140001203403094442d41203144242040a1034100e845e00100f1456091001010540c4810003136298459849240a69904107680119080c0040c40400c51540500d9030620411490f000c40c0c1d04056440c182e540000c400f00101805083ea800c0501511000c00c60b244180154100340341e41c6090000051610101943c0e5000030130304230b4800312203850000d030a010480c1c0340e80390300036107043e8056406000a0324404072800010640b4486105044401e003001c0d00c0f54a21003107840c1603800400340141346200601d090840291200c10032104440c1032119400c0c00f103802005244c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 554582652 1250 554581402 554581409
    0x2090f040b060111070f030c17010507120b0616120e01030203060f0d1a0c030f070509010f030b04090605010b22210f0605070e030709020705191b062601 67
    0x14103407001d80b9a9001914a020401128501c070b00520902140340846100e020000318807408801c0002c51602c00314000d030480150080d0a541d041109010001341c0c031002c1d85c0607500b510040020b40c8001078002914a1103418100041d5004800410081c00400200c0c201512a1500c0c0c3ca001ea4125100442c00ca1100702c0751141c0c002d00a05005405041c19483e500350588a03807590018032802e03029050f528041122480d141c01000401c215402c0c86034062560890b0481c240103090103011300011f000040c0080312a010990345108440c0690b5554201030592500481c08210950b1a5042044180c2c485a444085ca80716124183c2e4003000114820f4110b0f0310744002443ca21400c0001015190351412003aa6000000000d15010400a01ca80c40c040d01d60790710303511850406201494106111984071030420381c810700c06840450404600c0200810711100c800c582c02d03c01d45070505121540b0141d4070381ca106503100200c3c2300c03500300c1c56400100c41c68580d400da1060000040b103080003401d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 554583902 1250 554582652 554582663
    0xa020403020a171905060114120d110309150414120616020109150c090501020102030c09041d120307030b040501180507020c031b0109083d0203010b03010302090f04 72
    0x400c108040340d0a00c2d24214944000f005039403000b051600140050012004103407259086440108598400200d508040c000281d0301000c1122142c0c1c031090710b80d03047c1000c44060041114109400080602c11140b0701e26008103a5006602d190fa01d10540740c0080c00303035560b10a0030f280d1412041c0303407000610b240b001c041c800500c1143d0350944030310814030340d2024480030741d13403180e01d608001b07036504100c0d4404828141e80000c22292002005000e00d040e5401141964810002c0c000042c021604540c0405000d40d404250a40b2200c14180c84041c514410502070049035a10100b8a65800045005d51802d42d8144806520719041004844003031040317210780400b0f06010003003503032250441c540c4901d01e030050312130300c4c0e0080000c03c0c1003040201c0b81d115445100d5001301f600d9a01700103280c02500c620300c000c0c000300c250481c08649496800c1507507103168032070b07c0e640d1003803850703c0c5010308911010351001d5489594554082c0801e03002808100e1150210300000b4800e1054410326134480d54004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 554585152 1250 554583902 554583919
    0x10f0b19031509021e0102061b18010c02090f0726060d080c16061202070c05091b0f070312050910020903030708040305030912120307050f042103080a02040302 70
    0x42e0b454000300203000c01c080412644403209840542e03a01c140c0c14002035001e041c407000b5080c24100080c1401401445280341c105e148009400089140d4242c9400302030250525000c2641c510051707503088038105000350310200010400c9056902480014096046625842e01460120440c0d0300100c040c41e0f4440618001880000d0451400102d00d450709400b4500e12440c1000c0100000d08042c2d01d003180c11040d003040b07407003000f44940c04151400400c103824400c60504149643c0c60403a01c0311845038610a030f002e1404165141c8001100d84208044004c0c030301e60360040820000880d402c080401d501281081040c40c0d205c2c3c9031405030a00c60803021000d0706540b0740844001009400c010556501807000380820000111000b00801c00703540110000c50300c40c042d0074200a041007444000000300d8000340032042c0e00e59090342c142c94100406003800c80d220a0304124004035405240d00006aa482200100401c00d0106000b48074850081d17460160680e030721a034480c00d80c421440700a4008850 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 554586402 1250 554585152 554585159
    0x10908190606080703120e0f061603180f0302040c03150303030c0807081501030504140a050a02040b0307050d060f1b0807080c0c07170f0114010e01061b080a02010914010f0b19 77
    0x9403000e49203440000340343c0803103404604027080c0181c1000400f05410408584c8030f2091507000b0a10303542401d00c00460f51045410302e00100d00b40c0c4001e10000307005640300c07005121403034001d4125a0b4809084150a16150f07543e04004000d04100c1680c10041a0004082205c0e5407185100d20302c2190713152622a206002003004400400c402002580c400700b041c41c00d00d81383d11080c40b00c006414002d1009140c00d208500400049413a01c482103172081e40301450812581d118002c3d06c0c0c0d4a5a08074070000341034075501920f01c024003001100344c090501c440030000c41040e00184440c0c01244a0340d0741c10f40070355550803816400d11603a144400309030f000010401402d00307039003100d06554503c2300036a41e8140a8807009425140c0e9155510a0044c4010050042e002581c2c07009004251600d0504203040740e807442100c03140b82c14079029000c0313403001802541c12070003504010b02107580403070381d00150a400c154141c0200000c4040e00d044070b013410103028040c80d00c84600341c0219003810b880d220941c603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 554587652 1250 554586402 554586407
    0x270402030f2a0a02010e010f0204080a0b0a0902030a12030b0910050d0c080d02010204031a0618060f03071e050301140606030415020d0204050a0b071a0601090819060608070312 77
    0x1280a80e82e00388641035415401e04071100c102038504543d141e0000300c1d162440030395150a48101d041500c00107031040c0310400c48400700045600220f5005040e400b095180c202c88080070348001c1e180a5098840c841c0c54000b0094961400081400d42d039404201e0f1408282c108218144203845051991014031300c00e003c10f00e03041074488001c0d48500c40703424080c0d5481d20001e041030030400d080c00250350b01080c10000d000341e80c990168040c0840c1404401407401f1800036009051902c840c1355610884000501240c41d255070508102900a01300e4021036030340c0c000490700c0c038003003401036000800403000060306080500449062207100fa40180c440d40c4c4501c180401900010010b4070490310000102c4601c0806100510501c5101900541c0c0c4d1402c2c40c00740000c012017070f4040c03058150304211410101d049074070a000c00c030000354030f07005242c0c541c01d004070707914001c94004050a004000c501e01900414001400306075100b079005201c400d60302c40040361200e07210710000d0680c002c0b007020301e902d403407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 554588902 1250 554587652 554587681
    0x10c0b0c0306010e03060901050603070e190207020f0409051f0b0904080706200901080c0a050d1518020910110d120603140307060608030a2c06270402030f 68
    0xb24107150201d0380b0484000000d14041d0107907045021a5565401d00445050500015015014070a245240c0303042c219902c5c02010b04107a481404994041380034821035894405041280500070410300640c60316042240e141c0f5081c030610318020f5031000000440040c01d0064603d000301c003c00d1043d00f03035290340b40c428040c1d0102070210b45440d80d41492122402c940e4080c8086050755190303883e01c469828002410f45400603010b000c030701c9000c0c0107100c1c0840e40035044602041406002003062564812114840b0000e904040803c100c11468801c1128107903010300104242241c40e151a4002400c080d04c00644001100c03c00c0d800456138002241c1c0508540c002502d01e48100040165803512030345450300780c0024512030381c0c2002620006110b414003501010f400c07404051483c15a0081e0090800d8140c0200c40303140c241000021610960305c4d510403240900e014040a90700c84031158003903038a2500700d003001a20003042e130144009040c9842a2881851074a641402c561100100343c00e040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 554590152 1250 554588902 554588911
    0x270601031107031d0d08031b12132d06060e070f0503040c0305030703030c080708070503180313060203070308160c0609061b0201051005030a020a1401090b0a050414010c0b0c03 77
    0x140c80d00c00c0d4111143c40750042c404456006101803607c1c0d052075090101c105880b0141100e40c150305204150300080a0f814150f00610300b00003d450711012071501329100741d12042082e00b0141e14004c2250390b0b80016000004591041100304011600d64807440c2c400f07401039030400002130540c000b010205004400030b40e0001c1c0240ca0000720150780f0380d102407071075104420440000340c84030740030310b42c1d41d8200c201c0741d03040a1242401c007070520f03040600500c50b002c01800207141c2c0507070318041c0188140078400c0341c840b81c03030803010b0040c29034071420701030f40d6a030008034210000b5004800003407400c840105910460401650781d4500211241c40c1c61000d844038078001ea99850b0781c0c040010718181030140d142d241290903000411186081e03065115400c4042e480035020340c108007081030050303442003400800da03900f43c010302e072807405802d004840010203500719508010b000a00179060541240240080301c4203181c0c01d11035140844011a444075408000407c03000c440c001282d5842160b502443c1e00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 554591402 1250 554590152 554590187
    0x60705030328020c0c1509090f16020609030d0902010324080706090302030c0d03020a080d0212100602030a0e0301240306050f071d0d0227060103110703 67
    0x51004a4481909550003540d41841d01910180c1500c1c068080365081007146400034000c41c20108804e28880d21410b0410401e4884d800d0710b40458519407280040c0c031400340c0043d08020052a1500040000b100c00761540c003082c00c4100391500d2014400a0140d00c61440304000d94200181107041c0000750003403180490505495180900c1000402d08920170a40c41d10200b6080252501110300e081002e2034101d0010040d10b003500744091b880000e1029120b50040e03a030b9804203034090804a08050b803041000700301440c00516515024034540160a004c00c1a4818082548401034044103032a85845500c0c00360b00240011584940142c805070090003019001180d055480f201c0340e007050340001d20301c0b01c504401c0c41050041c40124410342d680b040180c08140801d060204001d803002820301841c05641d00c01d2003a44003243c64292060300e510354098000345c40b40881e420030b0b48111408100d400b1094403840001401e541c03190013480b5440c4007070700415180011540741120742c88201413800b4103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 554592652 1250 554591402 554591407
    0x40e0d0e0301060e15130e19020d0f0305030405150103020d03050c010b090c0c0f010c052a01110d0e0a26040b12061008010b0306011b020d12110102041d0606 69
    0x1c4448840140e10705c160800d4214207884e080c40c5003040040001c1040d41d107185480c0600d4010004800500752580c0c440c5201d450a5100d80c5100141080e00035030001060b02d24001600da04040d0003034051800f0b944900706031000d000451020a00220007440040d5120100c0c0460b42c012a000740014606505800008983c041042d00803d82026050701c10101000000a03501080c502c20700040c00e06007040340092040d007400341d1008043c4c1c000c85595190001c44180e0305203a0001031301c1c41b074401c0c0080c00700a02260b04850b8040c3c20300c0d081000704814a5081101c5101c25a401146e1800d0b007a0748804044a212458503601c180c50144264074030041c4020040072400403c01c00c0076107400341480119690602d0a4000d0024412075040c2c180244902d80c0300500c155100308003034035403041c0c1c20302c1c155004006080c0d64580e50201103e001c2c1d00503005445003418015144000d494000c1a521060200e92002800c90700f00d22a43c40342c642545c0303450b03100100c01c0f0b140006894020200130003060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 554593902 1250 554592652 554592659
    0x6070801060e0d0c0e01051008090703020f13050c040f0b030610030509250f0803130302060310170106061407050a330f0507030204050102370b0603010b040e0d0e030106 74
    0x9502c604d15400031034881d02c095004225905e40744118001004070b42c5881413841c00c141030381903682c0b01c040c08000d101d101c0500700c45100e45c0300ca03180d811040c900708100348000e041040c041032566200780600c21008600d00030120300b031000c00007224081d8002520400101101000c124024030f80a8140d04584c00390082c2c1040002040250f030a9004000041c01030b00c610780607074010010031540c40006190002d2000890100030701c084070b0f088940655030075680e981c1c0d100300c40c840030305540c200160048616881c1c0d51281070551244047e51780b1074585404540b8450b091500030b001d050801811540140030800c001881c1600d02000300102911400180c01d130300180c1030504020031100b0503020307a01d044400014000d400b5503600884141008c6140c6810302000070340300d81c410454051154681d1480403070b515802801c901d64a1840e030b03004514a1424075001440d41401d45141e8800e6003009071074602403505103c2d400c4480d10200080c100c0304900303607050317884204548003254907559800000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 554595152 1250 554593902 554593913
    0x40602090a081506180a020705030423011205280204170609060c030f010e0601020703140a02040b04051302211009030f021203011703040b04030501060f0806070801060e0d 75
    0xd0700078207072410203842e44607401c80d000b6220680043c8161701c14204c04c0341514000188181300c541010b1201030150351002c95007401440c5200d02d50002040c04a0060300542089040341100750004090740d501c1e402c410304003600b10a0311010380700500d444080044507590030900b1010030445100c0c149015045c07a42c0c174020b401e903c04210010403581d0b00b11b00204017113283c0c01c0c4409940f00b03800042c4142035041207401204444414000c05105044410100701d050b8000c1001000645e4071a1841042c0d1880200c517035152445070b40202d00441c14551031076001d00e0305000720351040445000c040110100d0340c081061110004402803140803180c0141d0040d61424400c1c60405440c00901003000c1c3c5146c6801044a0a0541c1c0103085400010300412401c65607000c480c1103410b4100c12805040c0300b003c3d80c40c00c6120b1a804049a40f2000800108000040d00480116000007610713010040d650403c0741c0c0c440204691590016107010010310205000e0880e24200e80c0e0090324400c150403007523858 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 554596402 1250 554595152 554595169
    0x7110d030f061802070507081c1b0507090c0e0d1205070c030c12170304030f110c091807150c08130305030a17060d0b1512070b040302100309021804060209 68
    0x21a50400c3d00005c0300740c1400010880302005096020052008004400007031f80f901c0d22800c8000c00300b11041002c8a1210102e9958050703c90300001501c100c02d641e03068000c010464112414042413400070032400c0d07403034042915601d083c0c100e0008070180740c550400301e6140d8030014040310384884522022000c500703d0340c24040541100f00480042005a040011013207940c0c41c09007046580c10820080042c0c0d01c030304a44005461400c2006481281980c11818082d550420540100c2028100051141c0c101403a00805c0c0f0f00340c007600d540d507841d15820760348031307078000d100902084c0603c0700c0d040000d0710680200b11001c441c0c104007940b99103a582c0c0c40d0a51340f1028011001450b543c6030b050611280c0c0e051a030300080c080341d001a1401065550092001e0001c7c100004207500090201d1036849541135110f19100c500f003035400894850b90120700f541c20030b000503406002188024903d95020b481140708564000b00701c03c2c25904e412006000c0340600034030413508240c00b84010000d83d01c61214 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 554597652 1250 554596402 554596439
    0x203090f0a1202010605040207031b0305210a060501090609151803050f160f09180203011d0c0a0605030c031308040b0d05060d0b040201140c190b07110d030f06 70
    0x800161045000070090175941c1c2da0708840c0c8614410003050340000e03040f081e4650b118400030351001c00110541815a07450140c1c04990a0303003503543c410111114404070380b65200e90300c4504204180d54642c3c004546079410f85c01104042051901c0510800303d60352501038695002c3c0c50000c0700402000815454108a90300844032503100110b044400e82e820f20900901c42c0f03031804032489040c5029281c0c2c250411611403c0040b80c2d4031594001c101b42400140395030103401030001e10405e00c4d05140d0071244155020894214060304a4610007850301460f00c0701180c165940c2c46085817985004801c9980c00074024050399154900c0d808001500390014100404100340d144d6100c15540d0042d01c25110010002445060441205000180d080102076001502841c105520a2035049180103510030b1030112046c52240325045614503080300900b400e080d105070040640c13030b2a15482135428009440d1040f40c690004800414201c0c80381d842000d010003c01400f25003556161600400d04182c2c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 554598902 1250 554597652 554597663
    0xe0f28120c030f020d1e05040b121e0f0609061c0c051905030709020a0507140607030b04050403172a22031101230d0b032503060203090f0a 61
    0x30380e26014150014aa00f40103060b60001c2c107030f04820550014801c0040882044011802801d5030074094858401c1c0d03006845d90f00c1c2c840e07035a1114082c1ca0100c0b6031040790b0950f62850201c015852010424060030302484c2906100b10803520354000b08220841c0041030349410040098104000c6d554009113810413074040c50132400310a0a01c42130000d4480801219945013407107040c10403c0e5100010502c003201c90307001c00180c403404107076411901c1d4031401002624100380140081b0b1031020105000c0d011700038645041007900c2c00c05040c807040d5001128007030049040342011202c0054052003140c0e020040380d0743e0300314180e802064801842c01444c0d14090404011602005000c01c0c0c21100c500e20300ca25440c03402e2546165074099050180e500c0b05410003070f941c1804080c0105100c0b00588903280390118646482085250200074560308592601c00e104001004e41050100c50207440b1032400b100c11410f1075400d5841d004084e5101030200c08603072140603542c031020700040c00080e02039403045 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 554600152 1250 554598902 554598917
    0x315060319031205150a08011a04090809040e030d02160b0603070806010603020d020d06080a0c05041109280f0e010906151d130e010e0f2812 62
    0x12414145080003801880508120341d080000c00300382c114036800010801c24001040d19a149103503400e0840c1c03402000e50300b101003202e0105a19006410159003481405403011080041c402040141c800880d4041c1221004002a03c0c0a0900b50000c65030420108100d924213408a028542268048003c3c282c1d00d52184408404005e0011810358002d8005c40c010654141400501616120180b280f003052550020b1400f44245407178043d81d282c4141c8800c208011540e64201c6500c0d81c034005021507100d4100800481e59150900c02c54142403900d189090800c810070045c840307601038a100f00c0400054210808455401d090b0045c2c0c00303031840e0350350344401c0351400169400ea460185c001150242c02c041045c840c49450849940d4914140d14040031303012207609000c21898113034040f407a0020440444d40b0403075410f60700610002220440200b251144da0740e1141c0c2c0303c0b0a5215080100e40100d000d0750742a202c1601c2c1503040360010804010803411969840d4065206d0071922004505003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 554601402 1250 554600152 554600161
    0x717030414040b0306160c0f031106071e030903090306020d020c15070c1106360303040f0b0c100f09030905190302060d060504110903011b0e0f0f0315 66
    0x107840704560107490500081190300c000903204c050041150840462500b00c0c01c16891140448002082d04904002413807840740c20014a03101760b10541e581903209441c04901c1151144007015402e0f54035040c3d404110b282000214003a02d010081a420001000000310104000b4030003070140210910005030340f0550104075900f8000604207040311180d01c40c0c02c004c48280c1002c0413030306080c2e1010b01070000c181d0610006001d4041d451902c80140d0b8103040030700c140c1108030b04000c8143c0250459101400400b81010341d644228000c4013181c000d000300402020607104050114400b102c026140714100c802e0007032048070a59012209095150a0340e40141078010b47c074100581400d5441040d46003502002d55114002e80c031000740151030000b28000d004560360300003000784c0002001070010075082400c0c0011900301c008200c1c130075460409464641d00c0e5030030240c41d040c0c505032106580c1a0b00801003282009498610310b4101b21011590b00b0f6541d0140850b1814808a511804544c03c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 554602652 1250 554601402 554601419
    0x40b1b0417010b0603010f0b071a070305010f05151902070b0703020d030506180609040804080114010f14010c061104090203070819050903071e1e0302011103060f0603040507170304 79
    0x9003c22941c00391008000501400340458038020955150f14162a074559543c134200c141c0066185808012001100c14464030f598141c00903812241e00d107100700e408503119400c01504040c2c1100c14000301ea010000c050341c3d4801c03916030700c2e07018503a40107495400384d82e030441038000d03800407000301d0050700074002c200025a01442460f0b0480e000b5607024010105207903522031480800703008640311345005030004040084c5801103e010b40800380003400718030b8640360441c0c80040c081c02241541c409100c3d010a1041c0148900709006105940e16800400d5070b440d12402014840d1502000340010000407070008180d000540c064441e41e0b03201580c900d443e0340d4600005003586448907009003014240700003884000199042182c2084c420212022280c00210352640c0951004004041d070807043c40d0040c101d02811030b00c1d0342c000d40090181c4000d81044aa05100850b4940c0d480303a0b1040d00900e03581400405140d100c2c0c41407048446c1651510820b41400001440c4030000b640000f805000640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 554603902 1250 554602652 554602661
    0x1514030a1719030c0f0309151a12010e0703172205031606050414030115030305030708070e0d060c03021c02090a0501170a0b010c12021c17040b1b041701 67
    0x200b0b036107420405010400300040000703611403a00c804058071002c10708144400c6800c000c80d0001160010080442d0034000d04a02d0b840041d503941c40790700c09910b0004429030601403041400d070040068071401381181e8440e01502c1001c0200403195509120341c2c4288403001c50140d00e482c0e42165010011442c0c113041500c1e080001d41e00a04040214004001180d0030605883c2a9110104280d041c16810b201003401054902e400182d18007065200109040c0c02c03400a500440aa98603902181e4030900280c8010034000442600940701141c007001090041c4d0007c44042110701d0007500d80085203042901d0000c2c1e0110000d14035a00103004502c0e407402d0708100000300403c0c20054683e6415079100803011400911181400307840c4c103004071140e88903510051106038004151400700d200c0102c021340d61455002d54a0520f1025007030306007058090b81b50a941e98078420907007040c5a4071656414400340307000c0c1ca829480180c072000a0f0805c2410300140c0040c20070480d003d891f42034144031300c030b003540c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 554605152 1250 554603902 554603947
    0x71b0515070302130e0a1113030c05060408061b07050f0606010206150321041203120f05040807060c140a12180c030602030405100204030503030603060108011514030a17 74
    0x50710401c1070080f91909000e044c0100c0d1804001d206060342d0f03042a0f003001c1c0465240038a003180d80055030526090001c03204005913401255800c50250b15442401003511541c02007003565400b00c0002070134004103944403080910040d200070704091007076881c2c0d45420b126408290082e0000f078200031803541d0400c004c590081c2c0303240b010008048840086611003098620080380c0ca5507125103250420806004c840060905d901001c0e808402410010002c4180c100104201820300c0c0e54201d6028280c0212406503801290013442c1c00c01d55036440009003400f60105081c0846032110314620050180035212101c420340790724045086c642d419408950580240518807800c0004040104401e2032000e400d50343d121400582da42c440e401e00c14640f1902a071046007660000501004105012002e107000b03100540480d580c90340c035555441d00383c80d031549910160f1080700c0c200f08001e202c020714202c0b01442c05401e0707442d020304030f0700d820888114000c0a0208170000040002035010b510039003c00e078 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 554606402 1250 554605152 554605157
    0x5090f010e0327041128030501030c2c1f080604050303010b0a1205010b0702030f0705011b030903020d081905040302061e0c07080d030f060b070605071b051507 70
    0x141103c00411032902d001c0210540d150310035120300c401464580b0f0b0300000c000b440e50040c3c0e54641d50100741020342c24a00e4174104501070000401016880e0084c0a403a040c4e82c0e100361400d01042c186903204070030a21065012401599040a80b00340312000c166040c05030403c004100f401104007143c040e0600100e80c0f1811803640004204800308a0201c1924103461070b43c00e5030380d5a5082c880d012035000810a035010451442c0c8000042c03d171000d4402808250310035402c0d05c1da0074603400441c940f0743c0c1c0284140c1c0d02040303007403524001c264107881d502060544a8102810010b40f643c020a0803407031401e01c01c0b19000750008101c000c20403644c3ca90003820000b481c1552800d4155400325050740200910114402526029241c070710404c0001d542d0900c20340c508861041d5650754500c0d0380c841c00d4800c00b00c0800d10302484aa64104207014039000d0f1940c0329241440c0c440706a0f9420700070600148904d0810032034494202c0c030710346a11a4024094050401003086080d008098080750074090300c20801e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 554607652 1250 554606402 554606407
    0xc1b07050d1b15090609150e1011060f040b06100c083a1104080c13020f18010801060c1a060a0b1201090f0905120904060905090f010e03 60
    0x90364440c21014052680842450b00168809100c00c00c40980b0b034200800b4000e4615100721026403140b42a0b0444419a0740c24260f03e9a401d240e0707065640c075200d040005407014898550742d007810201a020340040345040407540440f0042d05040c000191440c141c0710b07a80c4014130052004014074590050011074a003038102a0360f040140840410041c000c02d101c1c40400d00003074000460083c11034045071f041142603203180c045401441275041c02100c5081c0c0b807508401d0050001c0d44000d0b81c1c00c1d0740742c80e4005e140c000030140400c009500c40a0507a00c10076003c000d20540d041001e4003400100702c1d21a80e0301101c0c6e02c42e100144c2080c005070484020060700085850200b00e41d0f004202030007004400d841401d403103060108400c0601900071a00d40240046c24000322a0fa2415250486008507010040440c0c1400d0190644444103005041030740510740380502e0703a210303c00800549900410020311244d8814101051700c00440c1c0112203500711a09408064070203010303d211640c4d01c1c902651 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 554608902 1250 554607652 554607659
    0xf0d09030614012d0308070302030a081b04050d0809060708070605151507060b0306090706031407140309190b0702010b01090b0d090302030909130c08070e0106030c0203120c1b07 78
    0x49400552400c05040308105010502c2c24030b8000481c0006950042c1b850b0b6559001070070041d581e6480705482c04006014640090070b40901e25001e01803461107010b90034503007842c0004018900017117140540d0101c0b010080c01426565500040c800e083c403505005031502943d0034000100c0300018414800c04416200d50781c13455072480d8500c85074101a5036084c0d06c41c511401c0c0712009080001903160580302e031406100d0003840000380c84088800a0781c7c180009000e2052017251188240c030000b0105410420a02c0d024400b103000c0c543c000c0d84103003200d041110602e00a0000103500005035035640074801800152507080c0520081a0340c2803c003201c0c0603180c0001003c1c644141c00702000f1141d61904a581094800d20499110072002400e003442c50034400e0000c440240c0f01001244c1d000041440002c900d0030104000080381c0b0046c0c0303850384980c80c0c9007064000c2d0400803100c40450008200c400b562100741d0781e0b464005d01420004a0303c0741054605880e0f81c045400501240703601c41c0c8004c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 554610152 1250 554608902 554608919
    0x3011406270118020702090103081e04051c021507060203040c090b13050a0603200a06080c04051009080a030f021204120f03030612080307080709060c020d050f0d0903061401 76
    0x207044500c500d50b0852489142001d0b00000e00408500962149042000006000411000c1c0014000c158a2f501100210342d402a11a12030340c801c094005a2500c546003040c00c850000740b01450000d804414100011001480c0d00d61020340c045401c41d42c00b200388070034000d1000f42440a0001c190302044400208000110350502110461622948034030006113440100c2d040440199404002c1e01401c110340c10004020700500d07140c0758000e06450030000303982072140441900500b00c0d103032981c6c0f030700e42080140034145924601c044140321548400040040c0c0402052680740e010799690030034020722200c000d0900c55919030792200981c0600048c040c8485500c1c0300b15100f44e00c242c01c00201c91032864141c1c041c0c015a8000000d060f029a28070080c1710b9010000d5200d08001d40e261100369846d0182560403c1481c020600002c050507203a000604040d04140701c1c0074050401c540c9076a910b001d10310b00c1c5c91b41d20011107002074040e0004004121850007048203110a0b0040c0c10042d604250b6807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 554611402 1250 554610152 554610229
    0x160f031805091611070602070e1e0f0c0f07060b1810090209030c041514010c330f0915090503030f070c0807060227030c01050a03020903011406 63
    0x42480303840320343c5101c55860740903222000d1904060310903204c65070740c1d07144082d4580206100d2104100061800120f0400071400030310000882c03005501050f4840c0140e08400c042c004003076007881c7c103040004090501d0700801030041c41e4424000030034082c65038418082346604119092030043d0500040c07101d100c1040d25224190b5244040041c0c40f143c04a0000340f9140e200195203801902e00020039030a4a11111854151902c004003004030101103001151903d2404002600700743d032039050152000b0960003d01c410030981d040d0410010483c0707026a04440342400300b4203c5a564942d64000c00c010305003600104202140104249029078403407646070300c0000c0ca20140050000c1c0025841401003000e41c0455420414a580f40e40d502d2501d14029446811000700503900c40c0405008101d045c00c0685603000050054205031201e8401503031a42c11028401d018107809210070381441d10244250682c441a80c49504001e0500405220648055021910100c460744c1000308099121380305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 554612652 1250 554611402 554611411
    0x1a010e0111120d0504120c030909050a0902041505180f0406050c28030b03010c090b030a0b0d060b120604030816030f140613020924160f03180509 64
    0x2460342040001604180c2080202e020b02c680c00e0390007285140a440301603002c036104500c0340468520b80b070f84882c4291194100000c00800003240001c0500500c00b01d50000380d0001c1d083c05003c1440003103503000030140d0f0642540d501c0c54010090f0100030743e241c03e24030300319240d0100700f02162604200300c400703200d20070007800502500d4a507004158402d00703e0089079410620f01001208000d081d81140d082890081c5100700082d040080c0030b42c0600d018840c00c2000ca0040d211015268074000b400c5080d0b0704010000c0b04040d036a400040c00316102c0345500c40c800d6208540004101c9c00fa03e00b004480c41c403102000f03071303103910510400000981040f542a04542848414004084480d108402810801d1506501107003482006000545e044030b90a01519040f600e9402c40e9075200b40010032801884034142e0701c503440a1040c0d108e004004034071420850001201840c0171010081e515922051010403221840c100494005040d8800d8042c60801111030300d00301942d107080001400e03d0005031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 554613902 1250 554612652 554612657
    0x2e0c35070f050f0c0705090406060503011b050304060e070b070c0f2c1306060335040b030406020702060f030a06080d0f050c07150c03031a01080c0703021603080301091a010e01 77
    0x707200e602401003000140d0080c40000e111f807203a840d080c90102e01415591180c140030350309000c04506a085080d60210079101a40e4840381565201d03100c0300d01030032003184048141d00800030040780c000d40c2c240c0100341c190f01070040c0002c40e0307107004800c01881c11160320260180c0407440b100180c03c90070000c010804110034105400641f00d00103014402c14204030010500380c82c0640000030019503c601d82024150111150110340001007035403201a003c15041128180402c0140701210b51100a550860b024000050602810350b01040142e03100e606000082d100100030001e10302c1c1280034840240800308050004d0001854000d40328001c0003070032405103c00070603408110942000114018020001030520402c00318a01401661031484168002400c00c4030110003d6a140c0c0004400301d4103945030721141e0b580105c0011a904008000c400710b019800c0300b84c2c4000d0120030450302031401050b50320b41d03a51425100001310380f052204401140040c8a0900d00e070f07038001c0b11025060b502070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 554615152 1250 554613902 554613907
    0x105010f05070804050a0f090c08040c061d04142a090103050406180b01080c01051215120d21050403020a0b091002070506092e0c35070f050f 62
    0xd151020f42d900a60700000d411103004400050303c0c0d0700613064007040f58940340303040044c02124001115410760480b0301401052000390200580c03031083c503651504010200d0540c480a0078880010160740d110050a000004c9a905002c0d540c0c3c2805045145020307004c010016050102c90707409414098200058140b40d560000101800040d40103014948603a6000805a504130700e002502c0c2e40c2c081c0070b01c40b054459441700f0341295001c3c0085418044a120641c00d09903a00c402000d506000c0e50500c0e80c0200c883d0030407000e95281004800b24000d046e45902100c84581f0341018014440c0e46100d149181c06c000038440400c1e004039000d00c400b0741092003c82d45d03a9805030010b14004201c0800400c06100286210600c05c1c08034040b8068103038141070358640086998125446101258181010b20702094001d001500075845894031000c0d40c18440403540503035001c1001d07041810b00080c0c01c001914500004079100303410856101d01039091541c503441c004074008189000c0e8580d00300312003600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 554616402 1250 554615152 554615167
    0x160f030f020c010906090c1208090616080d06141008063102030624041202011803050c01080c03071b0c0b0301061d01020607050a030b0103110a0504030c0504050105010f05 75
    0x454040701c2c0c030881d014009000f2800c081c50400c00a2100a509032414580a0804500c4030411501007a0483d040300c3e03214244001c010800c00303698000f01c07080103010160700c0300e800041e5481c00603020404106c400005c1e070302c0c901300e440c5801086e000039461103450402400074a081d080111103801c407200740c9007000c40c1c0148948000e2041803480c04456007059a00e008903089409800441c4112006d84145c6800e0a00c0b004000400c108010b880740b0300c420900c400d0114000c1c0d40420324030940145007102011611200e80d090881198005031003a410000c6a07441c03a5801100e060382280075005880c4c658504071000409559284151035002d4004841c6007090013001030381c1b60080c00b01c07240e0706030343c03540e4074080034010f50700721401c01050000c0c070184148298008070f08684290140e0300d805180c443c070303404110000d000719500c55061560700c400c641d00741c0e10a20302500300d1940381c0e2a03640c0c1d5141141002e05070b0692325806588121305000060105903444070403449020064100280c90303801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 554617652 1250 554616402 554616431
    0x906080711010e03180a060203040b1c090c080610030c1203031d0f1006030203071818110307080708070b0307051b030a030609150b0d2a08160f03 64
    0x3028103162142d0300f0111001c80000700031005100b0f40c0d10484440348a0a03031903052140c0ba404a106003005030700244010088256001c1c010076030064002086100c950908044000300c0ea8603d20036070b940e5074100c8043c00340031010013100744c02c000c0c81d100c0851080e19581e1410310789500c9008540e4404010503941082602a42240c0010503911858600c1c3d8141071041c40c2e600c054682401030306100707258103118000b480703201d41415250060081c012090600301c441c016148440e1203030598550307851403040084404202000158407071411008000c0e04081058038001c06504004001d0b00700400400c40c0401c0041c5801c11683c6407254580c582e9034440c02600d8a003d50080342c003074a1450026001880d0000c4000c10b100350642d141000001e8a42200b02c00b100d9051144000c0c031180d0034010301282d40002d001d00ba400c0c5403100085a403560140b08050441041000744441c410030b88a004800f42d044400941d2282041c0881c0c0c8014100380710040041001c114503206143d80c0c0c2045000261 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 554618902 1250 554617652 554617667
    0xf040209041a01020c010c1109071e090317041211011701080a0b100b090f0402130e01031403071a04020d1e031701080705090c040e040b0103060c0f09060807 69
    0x54010030400c10344000b2168a030b0300642c003040c0d06006000b800098103482d130180da00c031601103400075003a0000500300700912184003000b0740900184003d050740c1c144142c003441811031648121750b850303503003103440c40c50100c04299010b13a00c84180d141c10310050280c80e24182011f010b080e04030b01401046540c10740140c48524071800604c4903100000000305e1144800289260210302c94240020740340d032035240c0c032615900345000f0044140410484c0344001e1810010407140d2440c0140010b14086041080010072a56030744021481c4440c400104140b000b00d0100318035407000a4003075880c2c109156502c01c0b4045c0d245916110001c040d4012409540b901c01e6003800f255800381b00c5841180004944080c1c47d540c2c1803044000402001c4034604840422140a040310304900040810504290030404070745401031034135036400c00600000485241200d201805079000b45014039665040d801e00398240c80d5001c14907800e10032a014402e0329503030301c000d40341c085400a00e4442815100c0100460313545 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 554620152 1250 554618902 554618917
    0x1808010509030c06131101121d0a031806050306011209020310021c06030803060d060f02030c04230d0609020112050a1b090e04031808030a030506040b1801050f0402 72
    0x15840d0104201030018000300801d002c0c81540122910391795001d201112004a814004120a48040d10805654010481c0342e03600345441d1000f040f2055a040c240b04032910300600c0b004186d01c000070740d109054211502c2c0f07201e4010740c45050080c9041c02006020b0b48000b9100030304000365100e80102c03010a40d4003c40c03806a0060a4803080020380d01c0c101d01075048a030141c02c01c0c0811001c510680ca0303880c4128001c07294440da24170700b980c1c0e501c41040401400d4420545001d501c0e0507500f041d82c00d40c0d10042d4400d14624960544540c20146560030700d004100c0d521811210300705d20500c060b0354000320001030f5640b00101080305141880121340c003010700f038040d00c40303c5c0c200750502c004900d01d42c01501c0842001800c184446407418822103030745050f40b00fa502128605d03c041408280300340c20074058143d003004a07003402d56982d00424515030107080850b00003a0359605000043c500380c0031ba40c4202c0c50464200560843e08162108040d41c1803042510942c0c558071040d4454442c0e80581d04032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 554621402 1250 554620152 554620169
    0x608070e06270711150402090601200d080106080106090513020c0312040506060604032f190e0f061e03070f030b0613020a080a09020a03061b14180118 66
    0x40c0105444440d00b0341025501c14011030300480c10b01008800015031000d05030020400d034440c54503640c0a000e13222101074402da04010380d42f541c11240500410740366004d8070b6080000c003c800f606c00001002c041042e000762003003041e010010040d81d03510614a00544208031041482c040104e0000c400921800382604030a0001040c03456402070320b00001c0e80f09174010416242da41c1e4400301008000d2186000c000c040f59040c0c0c40496114540c0c18181c03600c60401910401d400ba00c110002e1540d81040168000b03900716090b06000b9080d42d40540e030780007401e0f10342d58445400d04800080421048564001c01140c402d86014800d581c2040002c7c0181060185200310b80d8483c1010705280340e040302c8140c042d60040d03843c600501d000d403003141c0700108903643d00002500c2c1e40b0b207600050120105e090340d00007500040071002c200306200d00c06111041030148400038190b40d10191184000e460603440c1200b05000c40c0742c4d42518110484080034007464107003503d1204c008100d0070154142c002602 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 554622652 1250 554621402 554621449
    0x5031c1e030b010306061b0311030c011103100602070f0302090702070f06020109200d0b1302060307081e04020a1a0c010603080c070b0f09210d0206190608070e06 71
    0xc03505580905803034502aa024000b0300c0d110581a80e41c0703810790030704822001c10208a00046031044070180364804d14181600e1070500c100846600307599100c032a07a2038000300001030020700040100f0020051440b40043c0c8240c901d400e4030504200140e200207030140b0203000010703458600c02e109250141c80c41e2050f8840e56030725074500138000e004134442164010900c40340c514902c0020400d0044030b02000b4440c005280b83c3d50b6401401510140100d0b5010400e07001d09001070395a480503500c0b600703582d9580840c0e460702c0b20440740c103441f805407400c02c800300b41024040941c41e0a24124203845203401c00c1e400d160401c5490034003600c40c5090b00095546030072008410022405c0007041000164012503540d152628003550361342c0b0640d1446407121004100b4a0620304148200e07008414412420440581c0e800305154185500d018040c00160072034000c02c203c83c0c0200304110101e503c103403001c00103541000b50140c0d503031a0310f0042040703110140c00001c556641760400303e5603400541742c4026 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 554623902 1250 554622652 554622707
    0x10305030307020f01050c040909140601141c02030a0303020c0c060409230115030b01121b1b0519140f011415100807030f021318050105031c 62
    0x291aa041030b038500006014240c0014100041400b03118058221108001e1500e450700716480300070015800c040b41d1001502080e50780511051010a00810440e5540d0344c40c8540c4000700804490342d9200c1e48114906140c1c24005170320000340150145a06060040c3e45281c64103100780352041558605600000005000c1401c04040e001050840c1d03201c00b2903500ea159503889801d13070017030900807540000c110b0b0f5041d264181c032941055a0540060600420a460f142503a8080da11419038507105030ba42400781a0802d40d000f88507042a01100741030601e100380c1a40d80940760154a801b481c01164600c5030202489000d58003400106004002c9490b08459640194080d05101e141c001081580200040005140c0c620312001c0c1040205400c000c000b0308001541c031120094120030405a07076448072400602d0b584014100d092400d4180204203207400c14003240e1502c00e442000c092801d110042060381c90000d64281c03a5480c1c823041401620300c01e270044460350304009034402400d2014203000e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 554625152 1250 554623902 554623913
    0x825050a0603021b071203121512030e0316030615080d0206071803020603010b0a0e1201020d0506041503030503071103030a05070f081006050c0c0a03320c0d11090103 73
    0x100b80e5105140c0e14640c00648807211185c5a075410f10418684544501010000a204840203c4c0c240c01514000981e5088044050f1100c6030342d13048110000c100c101108145900100501c2030000304400500146950a0450500340c4061200416454803203621103685049286488050301074007045800100036010001e5903620b09803004808581c201c500402c080d04002400c1d0b041d242c01030f1406107913919001030010b1503401a0700040820003500000030141d5924000c0c0d1741d45071800f600160302d407031301c034a1954110b444c0980851f22441c40d0000d081c0c1d0050380d652000c0d0443e50141060354a96590b58010707510318902d0002071929002c0001000700c42c040d0740d800540200203036903413910360102002c4180d40f15103081e075001c3e54030311074000200900d03840f920092003544542c0007614000c6040c000443c021500c50f070011a800e41c8420030401c4289002090951900c1d40200542082c07a06495070b41c3d1280150065680500b510310b41400a0040d04038049c40100030241102810790307920b00f4079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 554626402 1250 554625152 554625157
    0xe030102090306042a0b0a120912030e190203070302060310090207060609050c0c0c041d030c0102042d050f01110607030501050306060f01090513150803030702160825050a060302 78
    0x3170b0401414403414100403c0c1140c80c644c10b440c041c0e10a039260164a02c03050f200b5200b00305103203900c40d440c1c0900c034002400503100e80d096001181c501107403465088840d682010742d00c0c0107200f84601c140300301c600581e400060364002c598059584a0703807512550310401034800c0f50b0700b2001031f1500000740700307003041500e41c4001c041756915a41001140c0301c11440c041c031481090301e44a5070b94000045c4c4001454140c0c00101c1c5150ba001d41d004202420120341d0f4155000341085400595000c1410405102413104400c03070360280d1400c141064000c0011301c14102e002c0c2c001d150040c06081407210040c0d004150708070f640c3e600242100d100d441c100300000c0c05024240901c50280c001e06010491b9828444001c802c121016110f29180034180010312021030b124401c0e110000d40c5503c0600c01580c084003034640580840780c05160f40746013401c0040d280001d000039a840c3c000c0c1010080001e20b20101d14960b900d00c0e245040c400140c4000700e4100b00100542003a980840802000203403250140d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 554627652 1250 554626402 554626433
    0x60219120905091608162118030309050c0a030317072303041703060607140a020a0e07090803040308031f171b030c030a24090804090524010e03010209030604 69
    0x1a0151240c0d00c00781c0d24826118a40c2d100d0300403a1147c0c0201c2c08245048406108181d000a00040c15418030485400b40f001d0ba6902500805c0d580c0107040e060060038004100c0c40300b0141c6040f0103140c0740d990000c04c508412910500080d2099001c20781c104c3c03223040307044100c0041854100e080e194520380981c0a600075502228441e00c01c1d0304c035113003044500e810f82e407140030300500250030f140c03503601c1c0c00300340c0c418110804405000d070890510060f580c20800034007500303060282c0240703464201d001810f03403034641e000650b695200784070820010f02c081c0e089175440440005040541d0341251645002c06c3c4c003d40084030707408125600402d4400d0006411941ca01c10810303032410844210045c103441d220b0102034a50140c110015480205e02129011542012244092800c0e005030b64442e200311103014004889580001500304103141c0f4500405400c0b20032106010b801c03a04a500c81075680b200842c03418180800000300c080c00303540a606892010f84042e05580b05844c00d407400c41d410251195 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 554628902 1250 554627652 554627657
    0x1a0108010e1c0302070305091e0310382e320c0d030b10020105240105040b03010b04031211030405040908071211070602191209050916 59
    0xe00e8a100d1400069160b07a4070341d10a503142107030907084004030003030360003072170b0980c01c6c40310800c0048c000e61640d00c0101c04080c0340003a160402c202180415090650401806071043d003031251880d01c40d0502c2604c001c81003c03083c0d0b501c00741d00340303007851119002d006c46070070386e0241c00c1d440340e860a20074a840502c0d100f002c101b020203c40e00d040b2802d80745005580030141c03401c040c01541075561020308601a0b60701c0b110005250412400e89945131400c40300d0144880080c1d01c07100700380b04038140070802c07000a030b10500090086d4a080d0550f07000b4400c0f8100708488500d040d0251240a03400f81040b28007500030002c2d10b503660740c2c45100800c60795015101c115121400f60b01e02024481c072817611160300c403e1003005980703801e2400c4100005441800e0301502c100404000481c00034900ca03c001700c507564030317468540364103040c1c6001c13605003139030340e03102e14150340051459800740040319050784041036000c0d41c189500400314a044541c00c500d0707009070707420491100c00e101070240200005042002d040d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 554630152 1250 554628902 554628911
    0x1805031b0f03120103060b060c0703060c03050c0313061d0d020601031115031303021002180429040906060806040c0906061706120f1b030610031109131a010801 70
    0x8076101d5039a00c200702101c201d540042005100199440d000100385000050000c0d003400f1881407018107024813607004891660380c0f080a0201e44e80c040c02640e50207240c1e164018150300e004d000007041d980c25218000d102c1d544e100c4002d6007c0ca4848510000c40141e8030440b5141c004990001c0c2d50340e0030078001a100700c0700103401c010380b600d01003000d0054028038050840c156115060241710aa168000c12020350180540c05000f00c156071001d042a140c080c2d0b591f03401c283e103440c1408100c5802c030b00316664075081024180b4000c5c04000409811800c143c60003e03101e02d2500b81900100b01b16000300c1910f0050100380030034071808011b00c4040d00c920b6031040003000e6662409485044000141d070884c2070342000001c0789840d00d0056480700111600c00c0c1caa0001142d40b49600308500d41c0d8003034540e0780c10b041c010754503820104800c580c003120080142c0d42c410b0550b202d20ba400c03030304034603803d10810913680000d80c0001c010450101c919800044000c1003400510701c5115207400340205581903190 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 554631402 1250 554630152 554630173
    0x4050f07020d1d04020a030c120902030c10030917030103030f0302090307060807110d0f020c0906060304080f0f07230a0b01030201110c1210061e091805031b 69
    0x1450a40116001e070000c01e061090048290790101c0e4268200c910050403103006025910f6900041c0261107441e81e000a00860211000c4d000c041c02d803450940c60391410800a00589002540700b4030300f00102e4566601d00a5110b040b4090b0040c0200200f200c12205d0440e100c1301c0e01303000914142e0707110b80c0725071514500c5c0090440490141d00b152aa0543c0040700c2000400d000f03100342c83e0050024034000c3c41c203900740b00045107400c0001140704001503c045400d6030465050100030aa00d104480c101c2c8d00d401c1000001c0d040b40400350001d000c00c507001503000c454000303500849007182031006520f80c40d06501d0404421003200c2183c1156000318088051000c0000460165509940030010000a90842d0011074061021480103201031244060241f1030342d50b006180b0390140d20344c000500b0303400e80b02181c0c041642c859902c1106200400305613001c5c070b048800c40d48000d98401d2040020600300c003500c40c40c5180801c2e1800b8100f0700002640404441c280c000307040c0900410340403a0099040b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 554632652 1250 554631402 554631421
    0x61509270303020a0e0d140705040c05040b0306010c1e06150305060708060604170601031b0e15040207170304050706080105010e0103051015050304050d2604020321090405 75
    0x44184848034001210032085001074080d9003d0080c82000d881d141841c0600c040102d00305010070304040c0c545051469400c0e044800401550740a840f0a42d41071001c080c24510140844c05203000385c1031141004000140b4030b900c0780c01e130381e060607800422030020211000c3c0141004802640d0507100305e0b05180300d0404e2941804070400c200daa00500408295a4050f801c90b2944c0014000c40da0001c1d0400c000604000d90382e666404c011050005010254910300d08000759604190501d84560380001d401c008503400c50450f903034072590207015010380b03140c5400054028800c8a05c010140c0c2d110f502d0792800359003000091031103035200d44101d030451a252070041c2e8440d07101b440b5540c0044c080300b41d990b01d154485d1700007941000701c10450b030a0091b01d815241c41420f1255409100240004c800c01051110400004040a9a50402101e060410304405020030940b81d010800f900040e401308007151410800211602c61054102c4288804000c06031b40582c0200e40e03c41c4a81d0414001c075800c0007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 554633902 1250 554632652 554632691
    0x50f15040f2c04121202030a02041706090c01051b0102030a1a0103060b04062006310203120c03090307060e030c030106180b03030f030708010303081602060403050c0a061509 76
    0x504161152403070343c850f6220055007040054081c01c000c4103026031800b03040140040c2d4050034420401603121801c0021181254001c900d800c50300740d021030144680c6803c04500c0d41d146210038a001ca95518244449006408201c2da001031258400001c1041080c840d9000b0340b802a004045000c0204c0100d0044007540e41501a0f55141d400400007004201d00401070400c142004240003403403100130701d2807903003440001c8451000d14980042d00f050100c0340c000d0141d0940c40e11502c49912840d103600801d03a00d614403510310f803090710005070700300110504009880181d01d00404032802035840c4c041c001c0140380c2c0c000c081c9004c1e00c00d2900c2010b640c641030040c4003c0d45c0d000c0d000102e42030398905400020740044c610250309404200015090001d821006503c40d0201c1e03124244254510300d0020081e12008204403481c0046405d40d409196010601da03400c640c041c03030403949885000c070408d400c1607908070b8001c040c2460844401030303000c0c80355101400c84565040802039440c043c5411411003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 554635152 1250 554633902 554633969
    0xe0f04050405070501050a0314150405090a0f0f0317150102300f0910031b0924030e030406110705030303040302031210030f06140a0e0304050f15040f 66
    0xc3e04001d81c00c0c0034552041c40580341d03032209440e010030010b40d006a039144810090380d44060014940110324514181409041c1d000200700000b40050011900d42900100400100078140c2030501c1c22030b410705125044104003c82040c0b492012410492280040c8000400305a0b0250041e18282c181d041203420080f0125504c1d80d0048920100319012101d1a0740710348a03d240441c01403001803101e869071000144104041e440008218070007001d4803000400240b040303410031400b00c3d018041454100c070030b85100d007004624075129a004a0b4194007a04c40c100c07144030f0501c404203001490301c0c1d004804e004031702440030507a4041902ea00c1456100e2004035000f0700903034400c00c034105c04001006030a9038003003100708407400303110744980d030713200c4062450001034650303035140ca10503800304c9151040d01d070300002088401c1044241d10780c41c0715241d005034800c1c10711840800c403642c02c90707884e80c80d03603113900e44a03031075199076078540ba2180d415001603180540c0314038121140100941c904c1d80100303001c48 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 554636402 1250 554635152 554635163
    0x2f0c0111070b09061b030a090b04050a0e0415230105102705040c030f1802091306240614070c031104020c2a09060a0311030a0f030e0f040504 62
    0x407a0704001c16a80c982e40440c843c0c58201c0b03020003500500540d580740b00d103401400d82c005140ea85500e980002c04020f01070f0080b81c00a00100802c00081c1d88840c010011280320300b80c50003080da07941c18401c0248040c032440448590a084000486028074440d2014101300242c14071031590300e032400d00c1100300c41c00da04c13400415211880c03408540310708039034071500710015441a030a181c0c540c8081b8050780c40944403800440c0c0c0345c02c8112060580b030b009001c01503964004c649042c0413141c00282e00c01a02030640c0f031458044d020550240b21442c1c000d18041d9030000a17154401e43c15541d8003034025500d00c207000000d0390600b121140441844e040700d60103500004410881d904503211800c2c0300c1804030100340c1c410b030300f0050802440401d108480c85202c0c01e828031701608950500c20119840085001c84c4940c2c095800c00100782c0e14407a101060b0794101a100c081c55105002191400390103403009819204039524031000c040d400050383c03c000760280d520581384000703801484191038044d10300600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 554637652 1250 554636402 554636413
    0x616110c0d1103210301150e010e150c0105040b0a0c05040e1f05030a0c1509062106030803100501260f0405070506071407050d080403080a2f0c0111 65
    0x1040d0340b0414640d440c0c10003000e0301d4138000b05401140020300c0c1c155010204602c04001003000c50141d0b04680858425414065200c0b43c070040000e00100d49030f14240d105540002d0b01c07210030100c0009442403418038074020000d6040c0b5090000498404480803d00c0906141141c10520720a005a500300c803619075102a194440c1c04500c0501840046200d1001419810019060fa01000300b51041c0b400740703020002260600344444907203c1000945814410030130b00030444103070322080c07540e500103c14480321919100c260440010300115130000d8000200070045c000c1c9800050f400801303d80090300d41c610114601c0f1100306002c4048201080d00700071391000100310310740e1561030940c000d01c5174017580c413051f40fa500081d0403030f0040c600a494010340560144a0f24a003013000c04040c180031100c1d44042d28050795030f15075600c83c9010060030900c01013201e1180501a01081c115811015014410408440300742d44629140752070005513441520400741d11540640c550400e0350b41100060310 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 554638902 1250 554637652 554637679
    0xc050c1503190b06030f060f0f0d021306091508100c09210203010e030d18020a30120215160c17030106021c0908100509010e0616110c 59
    0x500040302c64190260068594465030619502c03000118410080c0d0316010403141002024414072000c0c41840a000321078250f17900040b603403400b180241850f411030b07020340c61191040f5040b01800705540440340141c1450482d90004d81c400380200192404d0008481600d1a40c2d411402610442010300012500c072100600401c03001031132984406001a13054404a0025804a405c4540c0c0f00204109608042041da480b0101800740c6222441c11b45182e0184841036000100d402c1030501c1507070a02560003a4000d0b5840d4801d200342c00444101c02a17039090980f41c10402410040c40ba101801030103007111100801c00c00c40c502c43e010318494020040300a00c01141590950801c4500360750401c800d07600700310201d203184000c501800fa9540980605500e08007d03084c0804049105410710070018428000003c0000f907111010b0041007011905458240310540100765420743d88205001e0a03003005603420010f094404102d009035100d64043e4520a0740c3c17629140040c401c40e03801139444040702d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 554640152 1250 554638902 554638921
    0x2030106120b04150b0405040c05091c03110604050d030f0203150105090307050a0f08071d0615280f050703170402190608010608100620120a0c050c1503 67
    0x2c6000002900003d0a0f28224003c26002e00b00c50b440f0380c00113500001c060005040c50f020300f614009850800905008911000070300d00d21403c4c0858103441d4030040e040041c14480c454603034187c0e82c80800d0b5001402d1504119440302120f100c240f000c02d060900007002d1401510849104100c0c0003d03012031545954011180c1d03901403030a10758103100d0718a0110f02961452146402003450050308175201e4600070403d41072102580c04107000b203104401c5881c25001008d1800e0f0300003012104118031407000304010030203000310070900510244030048003010b480d1044034000c2c1321305642c0b6103490902c0c030f080b01140c0c07602c05c0d600001c000522820600e00c2d404404138100e40c01030708c0140000d0b040c10b010742410100e4005c550001d00001d03000c4004111040e00b00130f00640240c070407044007e0141c14500c003e4041f0380c0c2d121102c0840e00752803070158540c039020711a204038523481110203a941d20140f030f001840d031600303803030107440c9030041c1d6491401c640b820345101c13000d8000380710180e4219078601e0140d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 554641402 1250 554640152 554640161
    0x901060e012603040b0c15010803071e02012f06100810050c160c090c090302060304140c03032a1c050705010b0307090f0b030a02030c04020a12060f15030203010612 72
    0x40b0301148428800400c500080d80090181e0341460320090421051034651810481e0040c1d205a01c10381040141401040e02021081255100e130b41c40201e811036248012600080104554001c2030041b00303034030700928450b50040036004052412a03280e0345880f4650382c1d429119101c0d0b2525644100d2442078403409541110b648228020300040c10420940c4400e400010744803011600032128000c14800403010b4407641d0015080c80c82c22801c0d01c0d0030740d80442c03114400548003802e44a0344c1000e00501d14820001d011400502034241e80c1c840d43c0365444100100060050799440100c0598507106803080043c4004201c2d910244004c80a581a803040d660782c0c1c01242c003030f1030a5481d00c20f031040c507803400c00005008207001040010b9104e140049581221060559140300341c1241c446000036981c0096000c401d8a411500180d0b1211078001c142c914600790f0078003c03156400c00000003041d6207000003042c01c07a561014108a81540b40004030304078842405106d0106141c4900070507101035640c803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 554642652 1250 554641402 554641469
    0xc020318030a0c060201021210080d0c02190902040807061d010e03030705070e0a0c050c06040b10050405090102070302010b180c0d02070602030901050a06080331031403030901060e01 80
    0x2550758081441c3c0b150310340414290840c102507034000810b160314401800b04150711100711000285242d00f0108960340759048451804100100c540703541043d03545003a4114188450b1803030001d60b10740d81e800614040e400902c107911050080e90380025040307005a0452241600d60324422640c00011001580c954502da28600e4151001b40010030000303504004d144090401403512034010310f0241e043c0d2060b101001c8410080000a000d2103556480004e4861b4100d030740440c030030f039140d42c078044905602c141d254083c650007810300f002d210761500194010003c81d406a070090004a280d03900b400780c260707806002000c00410410000b103c182c1040054a00715a0701030300986400941e446900c182c0e0015941c48080365503c40c20b02c19294074500c100301c001c10302e0340302840c240b0304036080c1420381103a070f00210f81b01c00c4c40c00c80b114080c0d100e4200100d009994007036103252100d032541004a42e05d0b00704840c0300c130a5620307158010030185e401403101c1e4101da24a101841080b40603400038043c02c0091036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 554643902 1250 554642652 554642659
    0x1021201151e0c021f0c0303050c091903120503090d0305360c030106060509130209030a05100f09111215011d0f151203070c060503040203010c030c020318 68
    0x1400100d1010001c1810070b00005150796900c403080e410700401c280c910072071420145c81d05c13400180f0542036812000d0503a9094140c1000508c955800b00100e0301c0380b155880003581b00307200f01129010010030700080f106030f0380204540300310b040d1884010384043c4010b4031000b003254044096000310030301c25041594489030006103400d50451000d00351001140c02441703001c2c84000d00d40d10302c0214204219504510b00124024040e8030b1402e000038059100e00f22034240210390040e20000c40c1030781d0303404072003c890016003100c0c4a18a40d0401d1a1148890072140e078546080180b501c0600c011070141d007031195042070740b500c0288030080400048000b00c0302100918010216056010a12012701e91b008018251b0064030704503010390701d0000594000d08040d05141100d0071b021907010101040110f038442910b40c0d614110007004852318602030b0380030041c03081600c0240898542d500c48007035801b07180300790000c4c401c2e800d01e070303106030240d0b1154100c2c88010b80c02408546000050809400340b00075019 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 554645152 1250 554643902 554643917
    0xe06030606090d05160b030a05070309030e0d0f0b0f0708150307142e141921020d020703110c151b070308070b09070b1c020c030309100506030102120115 67
    0x744041c0d000085d02d644801c42c1404040204144803070380d4022140e000d5080c1c5000c22000c03a80d954081d1010318080d060031700039072110f0000410080c1e041e0721011003e400c01d0540400d4603294040b1074800d4402c8614000185a4402084d842d00c1120201700d0079490040190214500b01442e599094003100a920350086115101106038400700340c1551809280c03600682d1181000e0300040c0212149400c16560007000300f14120710700e0010320b0200c0d01c00b9824135210b00750001c070385a54848050547e140840c01440012021700005c1503a000b40041c274440c0d203461040011301496551901d00c0607013926000b41c41aa030060700566000f00070040090000440000e503284c0d2101c061408510350422100c2010008041c014030003050b00ba260300001c4d1400500c40303d410f06030084070a001d0742803202038489001d04000c003003102a8060b0341c07220040c0b1086075200e18010300503590303405960802a07041440c20001c2002401c042c0210341d001200d13072880c14800d9180014503801003440403161020400c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 554646402 1250 554645152 554645173
    0x326090607060504170405061801051314030c1008060103090219030b0103170405061204021309050d09080706020304050d021206070c1a0403080f04020a0e010b0a0e06030606090d05 79
    0xd4001815150780244000a450304c1c1624000f44181030300c9614041504003407000b00704603034958085405100c888002e16100c1e00255005980074000c0d282055581c400e05000401d400000d101410044030048048400e043ca840062286880c0494800b01c0000c41a00c0005c0c0154060b4021000e02c81c8050040e0b03030040c5800320300015401d4650001c603a03d081c80401082480f240100384140c00d4404901c0c10301d003518020006841c1d1144800f41c083d0000c10800042c05c6d5564003568800c1d104840400303021400c994038015469100301e00050010130b40341c0348080b13003a4400103810429500c00c0d800540c41c1900301410444000b548403004c0b170344115840c01d00d02d01e941050043e00d008140c4d54885050994461a080485400d0b030018103012184107820000030070b9000d05c0703454010501120404d615119400400c0380e0034800c0d004080310140e01d00c0001503105808000303010f28891035564031a402c0050341008000c0c4000c1d6001c961021080c0555400d5250010069030794510032801c442c0340c03224 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 554647652 1250 554646402 554646409
    0x30507020703120207180c0903021903150603020112050402010f0c080d0e0303060120060a05090c1002031c060f09110d0e0d1b17090d150e16032609 65
    0x4070450101c01600014410002e00d0a86c3d034001d04c061034207503004d002c42c68500c0d0000384404036621010f44500d8102802ca40d920351002881d201035a04915030f1841c45524180b03c130040d000341d1204130300040d240781e040c903007094491040c2c5005550507540e05800d4511b828040301c00d5190801c007a5800f081c00c01000c1d84101c001d1040401710745420001c4c40d10707441c0c110005404420700028900080c4c451084400d92400d0120300c15903c11500c0d000040e03203454503048140b40c80c04190341e2603000560390080c4c8003210340000180281c240144214940d1000e1200c440f81514081c1c4074500d52201520400c0c4080c84c02d503000700c401001c1c1c1204283c18005002546401c0d69404c0b0141c6006811100e0201703400f55002c3c0552150b03483c0b0074800b00480076240c0e82e0100200900003240202d60001c5003041ca00d5641030404495a07402c559034081e0307030f8100110701c002460010240354091140c108554040c2d0b8542c6500c40840c0c0c1c000307024440c1e41107042d11070500d200489806840420042203a045140d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 554648902 1250 554647652 554647673
    0x80f01050907182405040e0c03040c0302271006021f0b0a0f0303080109050c181201062c01120b0601031119020f0705030709090f0c171002030606030106030507020703 73
    0x35810300c50581c3c9645103c1844134030000c07005a0030030008201300912117107250380420340e0441050034020b030b902c0e03031503050121400d14150402584480d00804e00240d0b540d6404c1501d02a4004952141c06030711028000280c51902d84240005030300030341d120031141c9006486541c002081c1c00008200d010007440040d00729507280d0044250a1409101481490380c40b100150262000840c208024200b20168504600450030140c0c00306004a180000c142c5800000808030441d1100034018180c4035104010405950560802d0034510580407040020402e06024104c450448072a04041c0494880000064004000c1814181c403200c100707200c0c000c4a002403000d0942041c480c890400c1e47d0340007e00301850010100d00543c8103600c144900d0750003142d404200c0300301503000200c0a019281c000301c414006440070b400c02179030901c001b4100c4081e030310380710300d60100b2400d480c594a90292180c01f00d000540d203080d0058418401400000e000741d02c0f494000306a401162501c0d5500e90b203040c20300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 554650152 1250 554648902 554648909
    0x607020a06021509030a09050d06090c23060708030f090102040e0a090311010608070b07050f0a0f1b0f03170c0a030504050109060504030203061501140403060b0f01080f0105090718 79
    0x683c805081c005428900003103075504415154003a514052000000034507041590203118031030a0740c00f42220070032005500047c2c189a105400c2505540c0da0507403029010400a0f4828040c00d9400c07248400d4900321080380c1d540c0380c4c4134240d94195100e4410207042108014520329480d98208001b1500c00c82038003000d403048a035450003007150401464010850b95803c0c5000409a060280a009120010403824140c2d47d012901686401e2035052080c501041001406418054405901c0170710101c0c80e01c030352030640108150707400f0780c3c000c1258600f003841c680304400421442c0c080500005010340440344503071740303007400e2581040701160720300742031010b4148210b0200c1d10000e401c100e02d5812200c13a900070071141c1000d0382001d10310380203c1e894000050805080c99903803190507026a00800d040d003440080c40e8511500c0b992245081c1e00102a4040d002c0d10803608180040465803250641c5841145544070700c0c03219910745800e2004100000d0000024442d4079014102e54074151402d04008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 554651402 1250 554650152 554650157
    0xe0f1008070f090b090f160c0b160305071404060c0f12080f131709030114071716120915020c06040b06040c08010e060616050105060a0504021e090607020a06 69
    0xb880c54416000b0840d84403c40450007001403500300700f101c241001e882176024855901c0b86140001c50002214083d800315001400b801203041444851712a140110220b0006500e0402640c0c5030b01c003081d9002c1103009490034461104000c2482024447c40303030841d0446c85242650044501603a034203500c1104005108005440802003010344541c8413406030308049130b0784882800c84650b03110421098015010148481c00000300b42029841c2548044601000e0a220403564289998028134100b0210700414050b00380c40c000c5510a80b42d07540c00115003c03aa140d0614003808401400042d06c0d1049055038000300382c62584800c4625400200012505107014206600d41460300d1031170204c010300760130b02907450070390320396801e5070800c494a056400000c0010f8241e5507400000d90144100503c0031b4054010300700c0c3c40300300a81500720078000d030000c03108025425100c41c184001c0380121341c1161540c20691141300b00d8000500d0052004001c0a400076103091000e401007889940035501c031400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 554652652 1250 554651402 554651429
    0x150a0503070201060510051813110a020d0e012709050c09040608030301260c1c060b010e0102030a030c0201020702032b0306240c0f0b010512070e0f100807 68
    0x1841d907081c030441d00980411956a8050905141b009005000d86400c207400e400811402e00c0b500d55441e060b440306200140000d100300c039480540b03082c5540100764900003603c2030f0403c002200b8040c4032103541412061f900d6148075100540d244ca00000c00c161108144d045580000c03c5588403402480c0c466002001d015503030f01708101c140021603403194011000c5030400c0c030041c0074100e03180d403c020b9504140d03000c03d0307170700f00344920303264200385001545903449011b890f00b801c0c5105240307091207441c034040c0c4030401004981e00c006590400c0b42950041c01078100b045001010350090707120b002003100900c001410003280d6404245006420842034609000d4020b00301031030b07440c0074800c0c00301d01c3d410700d02404624600522641c03000114141c0c01a100c010141c000b269070f00c109406075006400501e540401440c3d8200342e00314070420b00038035001d80c00501075410321002c00604201110f01040d81400c403030b642c0e088040b981c0d40e030146c008003014003800c034005a1030360304025036005022809030002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 554653902 1250 554652652 554652661
    0xd0f0506090f120d0207030504120f060b011b08210a05010305011107051209131a100309050604020418020607060614100815040209040207080c0f030702031b150a0503 73
    0xb0328000b10400182d039550300c440903050200c0440f00c140c80301c5aa02c0700c005a11220f5600e42562140265000000c00c007000c2c0b0154424007141840c614103040c040d03041004a050200b00448005040e80700400026080800d45030000e4002c500600d028500c1e4141c01140d000d18200342081c11905a8210741420f440388011700038881c00384150402c1200b03000d851442d02501e50f0b20142c441e0600c82a030b54120f13101290030102626a800240708a046981c4108401141c5c01c5040c1481d20204402c01c0c05800b00710a02c0280f0342c02480f41c6809944c01030020705c83d640e40c96007048050a2540c980c10200e0300c0c41d41e41540180c40f200702600380c0c2e503c910404282d4034145112003c24407040c07001e85101d0b8110043d42058550085010768014811203000d2a4422800c004940a445100f813282e030020302c0050460148800f6074040c0c10310401c04029140010044880540d603800b0340500650315130040000c02041c00c0601d481c219001c44040c00c103220140080c5066030603600502a00004214004100b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 554655152 1250 554653902 554653921
    0x100906050a06050901030b04060e0106050901081608071d04020315090d0327140109150207030215011508040303141e160914060c0706020d080f010e0c03060d0f0506 72
    0x900605001c0d5504c0500703601d90b4592265164000d400a04910390310b101102c00000c0c00c1d00403002600000e0031ba200e2a595170000c8a6441c40d8021000300303001d40b07513500030441140200d0510302300d42c8844000045000c000380c15415502c405407040340d2521070303106800c80c0d09a0610300700d40304044038000782c51100080540501561400c1f05039641c100d40062404031850300414041d0b02c80e64000d0410143c9a4842c6100ea004014031407004c2e08042058009034016040d0381c0041c0740c078901c244d080e90505012210032111500c0c00b80500c40b420210b40104010b441d00c24440298030038003924020965080741485650100001c0d00c4080100c102c90381590302c81c100302000c0b150081e440e999480024464044000d04c01325150054604e8a454904540c0b40c80d5101000e6808025454043c2c881544d0307a4503019645008620708080070441e00000134812840c080300b894100c900e4070412400c10707a6400740300c81070795100800c0c0c0ba0340700c3c00c035980580200b04084540456070348504010f040c94107098400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 554656402 1250 554655152 554655161
    0x115050d0c031407030e1203040f020d0b220503040e0c070b040501150b070c0e070504080609030909011a09040f180c030209090c01020c12030712050403150e060612100906050a 77
    0xd0320281070030a0302612280200203155032840e1f07602c40c1520344a03211881c01c2d64050080313400c060351025940400d88140488550300a008d4910f840990120a444071080c00c07400305109400790650300107000c20060051600010741c0e0200c95002800c1c030340041380c1d881c1010050203640a03507103607544520450001e5413030000e6101400200c448035084c034811707580e141d013051000c1c0110041c0c50b141c01d0108800c0e5009400391809002d052041e9803842c586a601182e40e034110b4404035214500d00000094485500074000e504005040d14191500c03010038180300103001b042c074070103007010303519128000314801810310010810310401104905918600422402ca40c02804415440c3c0050f554072145a0b00010101981d401c1640c000e14000a001007140c04e42c0118400a4000c01207a102c0e044501e901c440104180c9100b000e508100c5800c1d0800c41040716041d48141c0c119a11080200d2101d01d003005c2114031216a100c00c464640b0008410007059038029081211721380e4581090080e18403040c040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 554657652 1250 554656402 554656411
    0x180f06121107060902030c0402180a0605040810050603070f030308041502093109030207170a0b06130603060c2a051203070c33060501080115050d0c0314 67
    0x1030501010000c4055100036100b4800d00808a907901d024850454034244041018010000c0c02151191200340900d000c2c03a054090340380c410120344001044850044096a05960380c00700201041d88103060207070000c010141c8204e42c1840361a50002c1d0100c440301c0100c0140d842541c908200d130034903213007001920100030100a0300c24014040184151291000d845a003140d0a4604529074007000c05114030001c03441540682c1810081c07100103040c1c0000da09400c0701c40301c1c40e00a6150145068103511040009801050200c4e0a80403501d13500d019501084070494004001030203076602d42d181e008980082e4200b0001c01c50049040880360350401c01d1b084d0080d21030b5071001d940c1007540d4031300b9100c1022010348030903d900440480e2056204401d20f2074034507030000780310b83e211400240354900a074060800300e20301110b044010140702c07018045c00c811510181c5840255908000c0c80d0500006100b00c25000c01006021241c0c500089010300c80e0312171103c0d100050a0580d501c51881c11400050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 554658902 1250 554657652 554657687
    0x1060c110a0324060306180201090e0405061803090d210201020f03010b2808010e0702010b010215060621010512070303050a030207080424110c0a090507180f06 70
    0x40c01c00104900d00d090700c014010081c200f40312605002c0c1e0700401800b040d00081d00c424507050b5011490000600440140c50003603c564500070707510100341102c520211401003550708040080f41c0b144c80c40b1501000d2042c0344c0c4043c0c078140a03045020400e0000309010546491160039900d0103001040740401e0250f04040c8004d500c3e2580403000d00c240c03484103102e040b43c82640081c41d10600c854060071036007980365038244c08003010320802000313100c04002e005141503496607601082a80380148a403102d61201a00034003083d140320051840501030080c24103802003000c01004980041c01c41000d402040d001d4601c5040c0d5040030140040501c07031018102c010740c000d400910120740c2103010b45140c440075180259403442c0c3ea00c0d012640740101c0c0d00c60b24446030408001ea8a40800842120022815aa410b0040d00500884a568034008a14682c00c070710109000c0c8104449078200680c4402d90b0308005000c10440032000c08124a294000714110143d9030040c0a9154455545914100d495 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 554660152 1250 554658902 554658919
    0xf0606150a020307080a0203130e0901060f0e060f011e0309050706020102030c0d020913020403060914010c0516051509031201080309101d060d090b01090903020303041b03020901060c11 81
    0x1c0401075076910807204082d109240101c0e04401c628800c00850f01e202c40c050700e40f1002d5599a1403100741d4800151440c0b0015400d20002250711a81060217100b120100041d12401c7d4880c0014001036440d80d0226904108081e100048604c0507031000c03600b8143c046e84c000607190228200103080c19480d030021421640100103000e400e4202c44141e0b60f021610180059440c0b01500002c0c00d81c20070950803c100c07500208002041c00f28940c010b840050050035a01c00d0104114805801c94001d04a1840454000c0c0310004500d050f01d0361007040d19104400315401c514444d442030b04c5400b400c446072222940005000810019500801401000208001c6007041d002c0c00000d400b030000400303404200b000c107009000c01640d0403011810034000140ca800e40d00c0d84001e000002400d034000c2e00760742e0455618000100030f140723407182034801d981560255045403a5555140c02c50140c0f43c1c00007030164042580400560381d071034083c031300038240c80d10344040c031b11003a207001c10031a03e9a420b220302c102c5a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 554661402 1250 554660152 554660167
    0x3061309020a054603240603080c210414040906061413050f2e0b0d0b0d080f0313120f0305012102060a02100f021305150720030f060615 60
    0x283c2103940c145e0350b0041e9261a4588910841640400c528240c0b03441c0c07600f80070000052005060042c100031103000c1c150380d0b10501c0052814075404400200f14140c0b2803c0004101c244550307414568500340040000c518600141c50303a1003038841d940c00009001d41c8221b6060000d2600b82040307007003036a00302000d100034505030032600305420000385054075200620365001c06038030440302e00301e0b00901481c800c2129503459141204a9402c04900308542c28a0461070f0445450320b07a00120b100b0303034040c203e585094400d90040c01c1d1500b01500c148501040c07014128002000b801082d807030201d10b40d81c3c2d07800108108400506945040e800304487c0c0d08601001e8450002ca1802c881c40203806903030355565644c0d41c11f002c071320300f035180c01144a1403407418100c8159045180c00901c01e52222011044220391260104441c80c109040b00c9000132808210130000101617080709050201c0c01d60048070701d603002001081c00c04c281c5840b41440d90f00207008201c05442c0409005452440b50104642040070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 554662652 1250 554661402 554661529
    0x20f07020a090c09050a03080715111b060105060c0c0f0a1502060f060604080c01030c020304050d050f0d0f0909110f0d091a1501030e010b0307030b0403031103061309020a05 76
    0x14180780908403981c7c40030f9041100380503401c00d010321030bc00c000607941d40f410f9400301d401c0c40c1546a0b00002600980f0000102c1c3c2c94801c3c01e5039001e01c806d5000c0d0110013156410800030b01000c0d8140790b002580c020f400541e40001c101420810151900582107518082c20030240e002b500801c941d1089400b4041885030301800180300381c03034030000e0030005068102500280e240d4000e90b40025840150581550304121000c180d5000405101c0215400c251107030000b43ea400c40c41d20031140000d01703a1482080300c80b5440d08440c101603c4400c0562400100e403900308001d901c540d960f4402591036500100c10001031141c2450b8440c00304a62118604250410b03084614034405010704041d100c0c0020140740030294004c0e04210801030481e038a80f0b075240f51000211100f190260b020910301082504003546c6039003241d1040c18010800100d1200c120f421100078072103400280c4e04044416408075003500c1325004503401d031007110750803841e0308520107004040784030222000d0b80b20400220b03102d1030b580303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 554663902 1250 554662652 554662657
    0x110a020c0301061805101505120f06010c02150c0d0e010f020c0a05011808070618212415090c0203180d0f05030f0909010b090d0303020f07020a090c09050a0308 70
    0x21300c00c88011842c0e41340c880b02c082054565801c20610410300911055180b60440010319422040e03c0909100707a69101205411107802c90380540812002c00b00c8400500d42000c0488007103070300b01300032801d090600309a1480c3c041b81e20072801c0851110307045c0100b00e40c0c1003126400041a070f44001e1040004883c00f04186040510502d41070080c1041c5031103500d1500092000507010840441f43c059544840003010310f403074035440e807646c040091000710b920509a1000c00546140e4041c0c40c0107154542c0d02ca10075004101142c03158100c602c8000384c8800c1c507034002c0f5000c15040f0105041211b081400400032140c80c0f84143c02558802c0108441d031900c501c4500b0304c03203141161105403030505030030241c2558405a0008089020004140090b4900d00c4082c00c07040d8026160b20b45aaa21640c0e01d04461055010703a40d80300e12000d1038140042d110342c0040c15000c2c100c0c0b0040e42450140c0d404034003924500c2d000344101d1034968501c200c166612050403c018401103400c1032002d8510384a080091 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 554665152 1250 554663902 554663939
    0x3010f140919050c09030a050d03051e040807020f0d031701090204380f130504091e0309080703050604060b06030705070308060d08030c03040302100c200a06110a020c030106 76
    0xd58603200082c6070b04500109035030845c10040d003620f9076442a03107090f6882e04100a4260f01103817401002c103030004180d920318504100d2184c1501c1580c2c5894450710b400b60001c02c405c076445800542c40c0d03985a2511102c5400d40e42c469100c07805103018920b10454042c90507040301040710710600081200c802000301128000148000c00d101d5242190382804400e514840700100d0203100113803c0b1901c8058500500341c0c4030810300c80f000342c3c9450707200b0001500c441b0500600750310748070302c100040e4005c10381c20318041030b12074107214103419940d0481c9410301090380d005541136040300c41003000303028081c01820251036044643c00d2851400c030b0340140603070007034140c00ba081141500c00600c80da180d000b031240780550020320b440e80741d1400c4042080d095000700c17011130042c044c50712032a44240c01c0380240c0441040ba0746601242c185644410b180401040305403128034806c00420f0800304d80248140d140720f030311003404695120b07100c41d40a881c0c044145c034410300903031402004201c0010064144c4c1d046 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 554666402 1250 554665152 554665201
    0x2040b1212090d1a01210c060e03010e0d02010e061302010c0f05010204081207060b0904080316031d0c03070e090d1101091b05030c1206040212030f03010f1409 70
    0x4910304107011450003600c1180c010000344d14000054166048401101c0c122000401920000070742c01e41d00007441d051b0900010411240307980103000e6240907201913250703c5005000060804d924140540c6880c2030300d001080581d44d20050003900580a120640d48010b80039009070310504c446d8002001d03400d1b0144090b0400b49581c0224080020a404503030080400000b21260344140d0310801555500c1030344211a22898120003000341d0604c50182e0f80310b40e030094101810b41d0350f451b0035205102c1840030000101642c0f145603400ba0071058007148000082540201b0001002c00c040c0351800226070450b11802584004210031060000740b000d2940c0f81d14506070650100081c1c52502500c2e900d500180704180418040d16901205003000c0c088900c1103084540915118003130110320b41070b22850062681003030002401505203a904209280300c403008981c9030405600c0d4201158100380c01c40b03000f402e030000e400c001d10341e07107100c4406250004854183e02c0d030902206054600d071000d59503010703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 554667652 1250 554666402 554666407
    0x52e06080106140906031606090510020607120f090206030c0c06010605030f13030c050303041b15021903090506280509031c050d06141003110d0908090a0602030702040b1212 76
    0x2080e2020300c40c007c680703c5a00c6c08014103545950026149102d00e001c2c0d1402208035000c101c080c544005122800703682191503a500c4858601d018001800066451070712164403401070390f0042e00c41a00551282222070151138071080100800c0e402c1403810380c0b1007010800140203002d000ca012089403900204201c4d285441c0004902d0180c07005011200054401c3c04017204010074003104a404080c810f204442c1d02140c1522480a0051440035406072801648454800d880410100c00e41902c0350380603092403000c040e5500d0010300b0507848002403c0180c0306480c0310701d08070f550f000003901e104182414624104a8800042596502150702035691a00790352400c6c1569409801160703a81809100140b00346da850b00490284080c013804200c0c0250164031103146a1442407082040107280314071614500b02043e160100070704219003003038841038010041c03d401b590307a10048400418258001d192070b00d072980100011a2088140b080c02101c12500e4520340240200d0700018418400e070301d058 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 554668902 1250 554667652 554667661
    0x304120302030a1121060a290d0203010f030507050f330309160b030408030403120b0a09060312090315020f09030604050a021014030f04052e060801061409 68
    0x1014203012204d5100140001a04000705241e4600300c00003829210b1501c40281c54001c180210400300d481842180f07070642560100200b000000116002580c07800d81d401d0001210644040764400c1e4807040400400450400c02c00400f0b10150004081c11258040042c08a601042e85441c1c0c0b5250414240d05c6103a4580f234441401c00140c04804035103808546a2400c500c030303160741d508400c401440c0c000201c02c0025070303419141c003101c4c86141c0c4100c1450a40c0c40302e55007600c4e4140d960320740510300754440300ba01c02a40c654401d42801040c4805011a20625504108442c0c494800c00d0008011480000b400454100410f4020420103000c0060361100e0302c503a0300156000300b5030307034540c140a03e6040c0300c103004001803d41e014500854280500206444003605c200c1d043c83c0100000701d6051001030380d1a03ca4202040c2c0c05801203058a0380340d00790b00000c0c00074058840a0351001c4034015224828540d051141314042c1c21404000c02517541880520a107180140034180d1058031030782c0018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 554670152 1250 554668902 554668921
    0x604090e03070b2409090c060c07212a0302010e03030f0408010c0e0909060708040c0816090501090207050604020402070f05030c0703033b0105040b0c060a11030412030203 75
    0x15540300e50001d118a040f0b0a10542e0309204288030131000300e0035046a03440e0440c5103800f00b516405005118010085201640c05100c2d19030445004141c2ca40140d407000500040800a60304040040b2001000c2032805468501020f82c11030243e01a0035031a4001e003500c0c0d070440d08089040d240c0900300030102d00c0c46400080d00e1031080c1b400d100254800400c000400c401c05401c28200044c0036201c3c0d640031400c0505004845100b1548200d096101402050380e130350080d400e158026001e80e5070ba10b40306e510340101500d80400b0f12400344600c6040308080100030768a00c90b00d0702400441c030056141c003000d510317140d40d42c800180029200e158000343c0101002460340c0050b2886a1210a4985800840480d030f51155080d11050380480d0386800594081051250703d801d0440c0a00070341103908640030b2041803a02c502c40300c5941804020040402ca59044201400031141000000c014170b1401c100040705440c4a07020a4074194000d109100008145a02c03203a40c500403480d0041e225655003081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 554671402 1250 554670152 554670157
    0xf0d110c01030f060b0a0917030702060415050f070b16090506040b18030a03050d0c03021204121103030a0608100e1513062903071a220806011d01050604090e03 70
    0x240d81c1120000350f1842464008030040200c0b140c0000310b9400e2305075000c046840c2d1041c020002d50004042005000c0144164880e404001c1a46003141c100304010649518940c0801015140720029000700310808203903414418000c1c44a150442c0b24618110100c1e4440c020342c0114403200201140801124404500701401010700404460082c6046e0401a1050344401c6100314142d0400d1703039180459009000711841c0300040c0f14001c0082d9910703298903448404925920b01081400d12102d20f08d03200c01c101031805103c1b04000018610304d020815031610070502010580c107414200074054428011940524465401000014035551900018407801c001c1030000c01d09460f04800c0e40d40e1f41010b00003049030522600140c2070b48039000003016560344c100d103d2008900e280292064a001c00080501100303840a030050203120080d6030042c0004181c0d8021402c81c0d444040100200010b14103001440b09a0490b010f059504101c0842c090780b007039000d5050071a440344d4042c80600c204208 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 554672652 1250 554671402 554671409
    0xb090a02180a12150b060f390132040201180e0a1d06060130050a0b100912020d12020f010b010f0c0b060d020901080f0d110c01030f06 59
    0x912000350f455030044000c0d1008210261004041c010021000310a68802d104409900030040c0d402c3c402500d07480c4003941e0241e031104400861034080000b2182480440c400e40381745a518100c481d0b88524151401c403460045034005c08610200111321201215001104001001c42e022000f42c0e503030300050b10450007120388142d110900034000601c9040702d080c803d00921200713a0a01c10400c01c025026054020020099980d82002c40491155805107a9014642e103250320381c408060f0103d0016521943c40d0020340b02c0c010388460400c81d6030171301c921a0080144040701d11524116000200030455095400740c0003401c0d80c4101040c01f99980d8140c40e05541c2c0e80000140d407100c00c0884000c1d00c17402150301e00149582400d054104030b40c002c1e20035901055251b40c800e050a021611100c03444100070b80311681118150000e000075072180810140a0803c1d0001024280d8618032114a0282406002010081403000d400c0300c0d440d020030703480201da9092034081180d00c5150341210060a0710760 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 554673902 1250 554672652 554672659
    0x30405010204090c0e130507020f0703030801031104060b030403080402010e120c0a0510020c1c08121008010c080a0b0a090c0f020735120304030c12030b090a0218 71
    0x401040180540050007a603030500024409104191401da400d018042e00c1203502c89560710451501800c0c503070103258042840c1c0b04807100c81000880c0c0ca810300c0000d0308190005a083c0c070040c001c4c014503450416801710152000c2080d00c7c40d03c030100409001c0608001d0400040030042015a1720039040c4120741e4100500000d02000c3d8402c840c0d0b51a0380249001d8069294407100048070f25150b2086201040380c1d40107000b4041c81c61042010610340360b8042ea03001000003100c000420707480310117010100602452100b403820258030680480d5203d5000030002da05105601c25400c0d0700c13120480d040f01c940d2001080b001017040c0010460381c141d40044640514002c0c030101807039400104402c403540160280d81c591a00d6403d0008441d00c00d000c01003010f1494110b00344490405155601d50003900016201e0080020031240c0465200b81e4050380040d803c031040200703000d81548084100c4440c4e04003041015800b401040003440010800c07070710340c0c6c1d020899100100095008040140c2c009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 554675152 1250 554673902 554673907
    0x5100f150e150301050f010305040309091121090f0a080a030c0c06050c1801020f060c0307020703240c050a02151003050303090303100e0c27130b03011a0604141203 72
    0x1e200303042c1c541003480b03081c0c410400d202810045500034460700e401660195201408a42040e17660800340076407000810034500300700301d8400082c8451201d46410155444044064181610000c2c54040c4400031000c05400148035030780050780c1e41c4200c90f08010b1505000c2842000701d0015902034521210140c01c0500340020000030399982c1e0700400340158020909a80a803941c40126a69000400f0300e00c0298400c00100d10141d6100010f10340c03041c458812110174030303269518458a0280808200c0141d80e001d8016518592140160707031200d0003d1070310034100b0036230302c00095039456910f08075a111a44000070a51005240031250080d68000d0120707036990522118888d0b0343d40c021940443c0c103214040c0045420700d01801540d00030403902d000e05040107100640ca4150707281c512460181900c0d0194101d419440b81c000882c01601854000103080d03559000380350a4070208105224400810000d0b207426542d00700c02e48080d0b034411152924a106010007044440440300180c1c0b4151201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 554676258 1106 554675152 554675179
    0xa03080306060c0d02070312030504030206070f090503030f09040e16091e06031103070b03061c021c0803010f05030d14090301091506030605100f150e 66
    0x42c1000d2810900003152803600c0203480480c0b0250700003400410a0007489011822910901e050074401482c10340e6000791155002400d120600a00104030446d00c3d10409889024003406411241e81c0c010080d0011815041504038900c5281050708a00741da480c003040b5049669800c0c50a40340c1103082001ea007000e4139485031003a04031034000e0118140d00d03000c2e01503140154010602201c039280d083c0c2c00d160626803682c0160001200c20814024a501d658201d20003010000300c42c0d4000101c2c0c0d200151400104601c7c43d003484980c403100e030042c0102c4600550485544801416400303607207005141e22504004500d20114844000d03520074020030000074031280382300600002c3e800c0020b9407014064442d0808402c0116503550b018801c100b2580708903a0082400d6441c8a400c615051202400303140c28014100100101c0e0b04c5240c0b82d0b8080c0307000500700f01d0010405120020b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 554496402 554676258 := by
  have h0 := BRFrame.cov_init 554496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 554496402 ≤ n) (h2 : n < 554676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
