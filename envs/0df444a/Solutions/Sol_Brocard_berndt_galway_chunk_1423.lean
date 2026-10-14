-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1423
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:54:49.113603+00:00
-- url     : https://prove2.me/submissions/2e2d3b9c-29ee-4f75-ac69-6d0b400fc760

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 255755395 ≤ n < 255935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 255756645 1250 255755395 255755399
    0x5030309060f030907050619030c030c0206071103090603070807090f03021008072318060c0a0b0903190503100806041101030b0409150b1903030203040b070309080604030e090a06 78
    0x101c040c1102d100c0360203101c442c0d440341c5490040500307100321035124075404800807441961300e2640064501d0401502d480812110441c0c00040d02541c0c001134042016030025000281e5560017180705c07640c1d41704907205591429020b0f000141203600207880020004000008000341d19402c44000b4000d40001144400132502c0c550000d046500144801da082105440c04181954010301d45141303d1a100e45100c0c1030301070307120705070b0340d00f904140003041e820707491001d18a61500304282211f6403c00d4100107407403178005a843e081070096014055044034482081000d818421040c1c503550071461303c2e66060f41c4e9051009090420780480c0d00125500d0f00008240703c0000c101c4d41098820f0344083c00d001c1502008a40090000c00704104041c000d0592582c5210400794154828203101100701ca90112040044881690700c213000e000003809640100002d10030a0070542c080e26140340700b45409040d99407114451400d001c02511704030085108050210410701d4105491648440302440030041c0c0b40c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 255757895 1250 255756645 255756649
    0x111815030411010c051e123907060807020c0907020c0409140f0106090609060b0301060e0406051818011a0409020d02030109150e010b060d020a090302031c0905030309 73
    0x4030028100505080c0141c1d80940c40e0390103a1100c4044c5a000b100703444246c940410246800d60044900308064045e828241510105242c1611142c80100200f1081006103110300030050189000c95040300500400b6080c243c4010402d40018010640d41c05105003400e002c0646007421558480d84640441c0e4208050203034000b4905031101000c03180881c5500340d60030701950b075071219040840940105004a00c28a00c15040362003111101c0c1d0080004a40e14204c1000f00d40d81070165031b885840820040142c41e03c105c10b000e0008134002e01c001140c41c1e561001645482030101900c1c203000d96001008149110034040343d002541150003800300031050a04410844400384850388160380e210410300964582580d80c98856a02030300820803151141002101e0302c002085001e212801c080c4216180c1c441809495511f22001d000203007022540002c8030040d410600001040041c28000080036079030802c600d1111000b50081c40b00f00300f20318440142031044c190820341c0a540100901c03185a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 255759145 1250 255757895 255757897
    0x2030c0a0c020a0905071706030f0a0f0602120a0e0d091a0c01060b030c0c10110306040504021804152003040f14030408072c0105060319111815 63
    0xa401500c1c01c1105400d103803001900c0c8100d00d400c0026464a40010020001c1d04540c0011340d4443d02525020260b0300d107001c05513600c505c501c8526441e0006d085030800181c03040380c4281d0982c4200070250a102c540c602c0c0381c06500741250940d019544400418031400c0c0103102112402051f803800442e014103003941d51002201c010300540c12400b0000b58404855400c0d031100002c0c09030400480d9980c10550709510403074101c2440da00d0a40202c1c03101501d80d03600742c460000441000000e260841d0340d103c04000040c0340042043e80c0040410020502141060075406c0c401e0b4400c0d17441c0400c01c1507022203d8101d403079200359061100e81c400c0d0000900382e142410b603a80154000d480540c0d103100c074903010b5a400d25103a104865032002281c080340300130b00410f0380300603110f001c2200c503c0e0110007081504582d800700002c1110b8035031100103010b83c0c1040001594885031040d14015004815000300c41151081c0300000e20a88000c00c01d807540c1e05c1c0c0c02400c000e071418101d680d280c541102600c20303078103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 255760395 1250 255759145 255759157
    0x2d141605040e1b030102070f051b060a0210020307050f030709090609020c0c060d06050a0e04022e0e06091903020a050108070f0804020102011103090619050c041a2214030102030c 78
    0x80b01d1050f0310b010071503642501150a840d0340480e000701c51401c01c2ca403241d581c00518416074019066000c007944241004010740300200728a42c020301803120460011030080d80090010310405c20b00300700860081010748015409400f25688007508240760002d12070440d80c1503085061000d00400850302000d1000402000050040724002d0341e5000307944155005022940c8100e420010030800040d405100700c907107034481c1c0d00a94030180c00040040074600c580c545810010403680344483c01c03110041c414440030350307800700c05400c1e11329004015002680f80c280403500b6541454203000c052046040500c2c05000425082c00d000006080000300a050488806045410020b40e04001400e5a200b5000014085240b12441e0f5803804c0040d40c030ba894a100f11030a02e048074070102901c110025038130600e0701c80c0ea0384410b1242003d00700285e041388092a0100045404070a20001c250030a906e1680343c05a0704054211950501e4803160001d84255180400d00c40e0344140104000e03500c1c03810845036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 255761645 1250 255760395 255760423
    0x60b09010534061802090103081c061712031e04150204120308090c10050a20031902030703050711010c052d07032d141605040e 56
    0x5207400d030030841a9111007403284800c4280d9511400c141020350040c88819074a0f008142c18015201407048041c0184902d100c029080302c00c4000400105a0388005040412a160300081c3c9030440300521130300b03840702900112140d0440c20002402a83e0410803120089001c070f159500b07600d86020464804040384040d82c803003c0301c8000003010884021030f8a41075450410045484a890305030001d5050003243c001c9003c64070343c030003140011a0000e41c000b00b09a00034901d5019030b010130780455007601b140c040745083c0300d010312800300314002221030001c0d050401c5005580720072442c503c90411000d05110282550010007505002c1791384082240c1e00706070402c64240e42c5800400c0100c5900b0030361800584140940c0801c0084540c0208501c4a226000501103600f42c001c1c0b544c168075a1001c1c403006200503008034a0041c07120298000c045008203280b410032120b400341d02c406010141c0d02c030704120343d40c00c07403002054000804040036003c2c00c015902080103018151000381d4600ca02c7c3d544807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 255762895 1250 255761645 255761647
    0x191203090c030501020a0e040e0f0601091d0f0303070f08070806060708041203180501020c010c140703140102190c050c011101061d010f051909150905040302100f060b090105 76
    0x30051200c40c0c4080001958440021943d40300c441c24000e00751030b004c00000707100d02d0821b040c2c486175100000d04c800602802401038081a440c000ca203000500000d0315003071068090792107089160600740602107580b038046014503981e103401d24004000520301e015003024000c95a0510a003a0b44c40603c86610200c00d99283c0d50740c98039403c00e029540110780c0305050003d41c9490100406601200c40590190002c002984c280d481c1d0b0016602e4a03207948099002420800d02500400c2c48901c90074500c0d208039007560f0f45291a525408041d400b10301d03000c039a0780e4002500d07190045d00d22004910324107107450325003912a0325560b00703521607409809007810019039590038000344a00794070030740003026000600c071703044e0108082034503032080b09100d0301c0c0e1200040240010f071401c00d0900801228038240400e004203040111401c02000c100f005010803046084002c15103a035540f0034a40103a002e600105050031494003000242c0d07101c1d481000c0806d003071840c20069207503038100b03485a5010900304a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 255764145 1250 255762895 255762911
    0xc050703091712160501060e09030a03110708041211040c05030403032003091005010e040b010302060a03110d090212070609060e010203090a060e0108130c03060902040b10030e191203 80
    0x41d107882c11042005400707040c009a00c82108a0407941c24104a03c82c2c4001c1c0490703075032000d40303403d402300454002e502e40c1c108200c00c2100910030340c46600308100c03040505041202c2e5072110140c40d0016081440c409400d07140301c100b408140003e180217408100ca06001260a9150040060001800043c18980c0764005c50140402450021400b0b080013a00c081c2c1b07905d00440840d607125210300a502110780f40100210320b4010300081184100d40000d84199242d2850703092101c00c1d4452074203042011780c0c40900360b5160030120001c1100403d51840400c0b4003149004120b420100c1404d030100340c0e40f2184007080b885800121200481300c19041c8480341c050450300503821882516120750348841b440302c0c0403a4031504220015914003003a83d4074203240da40c460241d03a80d13909480707005c2c00401b030184003007000803040d03046520241d2025002007000045040403078105041841080c02180e210b42c4915071001c010400144215410b4440d60301c4a0150b03220044130108005040781003545030204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 255765395 1250 255764145 255764189
    0x203040b1320040b040510090f02030105280b1602040f0209010e090709030507090c02070608040c09021e0c070e150d02090402030316050102041509050906040b12010c0203030a0c05070309 82
    0x411044094402d1000d0b01c0c1107d40200c0001c158018202c94a107842c4090780242094404c0e47c1c169200030b080040200c0f91038010424001c9450180dc81102c0d0164011551052000c0500a2015000c2e06134004444910402080d00c240140c03410032a072050000c80200c0c1c1c1d00c2181c82d44844800d0f2030034101c0b501c400e081190b42240c0c6400262107441003050010726a096644100607000c2c840d07003900c0203a602c03103008a9800c001601c01070f014000f240b1052080710720342d6000303041000000f410042c0400380c80c2094450b50308503220641f41070304a0003040100722454061943d00c900c5214007401e90245d207500040000d0105440031340144418000101151402c000310780c2603d04040d910603600089207402d5010b580140140445035100001d900c40031070045500c4829914014065100c40e55020203000041c00320f0224a54091903006a10404500a12400080d18030325409103581e458800102c00984428040304810400704000c82408aa8008005004d0300c5020081424101c000b1007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 255766645 1250 255765395 255765401
    0x50f010c02041a120a0605061503182a0a0b030c040905040f0212030301061412180703020a0b07020a12020907050a020a06051311182a04090203040b132004 68
    0x40021303005501c5154203c0700600c0012051811841103400380842c0d51181c0a1240940110604e0440144144046030311800c0c0300c029001c0074504041140d1500e0081d4030383d0b078800e486181180218401c1590003075040e0801203c80f8016045010900c0d01d5800c1a0074000a940315921403410103542e944081001c000741c00c404480c81c5a00240714040c001c07910301070f05481c2d0b4400e01c58800807800000d1100c0481c40c40300c06445108801742d090032140e6a443c44280741c4003403002c4014815014080002c4016a601c10102000e4501800e0f40794907908184140150400b440d0030980c0e00a90b0030380b200380180d41e0b00030960390296503464010b4440e15680c0303082e4600100340030010a110300f81007c1200342c0c030b0000c820034a4036002e1502c09039114a044140800c0d00a605102000c9034811400079421b000841c6e4030480d4030380b82c0702d00031443c8102c000c0c1d20141500150445641260000240010b004181c94a01d401c0a5036250119040c015541e80c000c181141c84140d5024003d1402e0254090b92558 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 255767895 1250 255766645 255766691
    0x32307050a1107060302030906070207050603070804020f090412020d030204030f020f06120a0f050a0203060307260f0f0105071412150904061d0a050c0906060408030c0606030106050f010c0204 84
    0xb4048450a0361140000380203074000b00d50003081842188009543e40f480050000102c0b10058050380c075680f030308181210040d600400a1b82c01181d03a40d11141300d521400b00b5144614015003103401c01c0c4400b03200c02030421040c1c1038541d0030580140000d001182070207106000715075040380e02d0025100b101000c0b950b0b501500c00c255032404500e004000c08103806400c11218010f10300410481d039510541468102d0101303803150b5400d58420441880016081c0803440c19410500001500c6a4242d00e5024034100c0c5081d407082d010f81283c6d0440410001c00d00845410083d641054203a0800403141003850b0701860b5807404501c4118004034074550482908542c08040142400c03102e4902810214094882d40b1040148800146100c0d180c01501041103503041d03912001034043c0800711420070a81020107401c266001304100300020b190142000200f40c441c00e500c001e800715150401c03c00d8215049a40568000e2901d0b01003904660b070b101e0110b540c6107904940c0020080d81240340d0b241310031520 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 255769145 1250 255767895 255767927
    0x1f0f1e0803030103060b040506040c0518010504120303020d0501080304050d0305090d060c020610090204080c130e0303091e01020f040501081302060a120513050309060304061808070201032307050a 86
    0x48107105e0940c000d41d024140035907040c40329848410a1008850080340c00c074000680c18000c1444c11540308a2060550b10145030060525860f80c50400111001090803030120381e000417640014056801418010f144000c055401c1c03502c1d1002281031040000c1000702081f0000410417041d948540c1c41e070021030381207882049505403480c0040d50b00e075030030348400c1c07038a41410070001550703440f500031036007900c01140180074004c0781d1030280029111911310515034240c50b40722510301220104007540c49901c14030000c000e84490001117080c1c40500142c07040d030030b0f40100800b110030f010550454040f0742c001c7c41c1401c00d5954150104e8910701403000029881040002c2c06a4142c4d030040400303445840314182088107488a800024290510400c018982c0e0001e001c090414034005010b140e1181c015100130403401c0340700c0e0103000003207000c01046500b541d01280105c01d650703151003084040000103600c00c64501c003c55080c0d100302801070502e401c000300094504403440c071a90241c0c0e444948 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 255770395 1250 255769145 255769147
    0x151406070f031115041e020f040c14071a010b0304260705070b03100603150b031305010c09030303050901020a0c020f06130b09031912030b0a080a0b1f0f1e0803 70
    0xc0404c503112881500d040c0c64400d13805800b801c0010343c4481d01d424035503000340031060150002090002924941c00010240250100070300c6080f00f165000b40300c6030b44118000c800d000c0c4c1240101d0f801c040181c11051180105004000000d0129001204050412701c01400340200b8004651200d10807242c00400701d01a880001030780701c10f16000b0b1030050401d58a111601c03500c0380e20450803a110490128406403626004014803000c0714011604030340006100c4c60190b8280d1203070b90940c0d060b40f807850f0000e06500c108000b07256140c420260000ba00100a500c0c1181c0c0c4039000301203051604c4003901c101c0780081c1c900140e940380f408544041c3e516103101c1e940150f075604a00d0041d0402c3c450319000c0e000301c4c0c8862200003002a5404156030b8030036250140080044c0d000c4005204413030040e50040040b400114480b40300300409a05688a804812041e2810b0203100360b040c0a01c28150b140b102031070a0a02508112000c41c50541d0442d40500f1a940c6034030480e454180140e501c24281400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 255771645 1250 255770395 255770413
    0xc18040b131505030f12090a2601050604112a0a0b01080c1f03090501020403080301031b0e060a0b070f021c061103060105030a0b030c060a03151406070f0311 69
    0x12042d00300040307086015000d03020003a03a8030240f648410b180070301941c2c42d801007103026161040170005081082d401030503121603140c5070303000311051403692910b1088c3c8140701c4881d01c00070442409940ea0004099a050010103102d00d1011031900881d89040403203219a054008848080907180702d483d0001002c44422000a090403c000b0b1000c0c007a030710f210300403042c502e109418100301c1045c0400c0d05400d00c405d000c4404200300d000f81046102111995007c0000101041b1820003450207180580401200b0940d84a00c1101a251542c010248207200322b080011070740d2114054003c5810207025181d03500d20303e290404c038905000c0402540150000c0d80420342c4001d02004c0010b41d88115800c0000c5a200c400030320403400119090750000740c042002482454131a001038102e0000a003c450585080340006046a00030325130700e00000707503114140341c108086180254010610440d411950124a102040c114801e008016041250340c500c0c0508041c841c000c003100c0c3c40848425122501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 255772895 1250 255771645 255771679
    0x4050601090e01110a03053301120506060405090705070b0f01051c02060d150503070609060f0302091e01020a1401020901031404050601030f24091202010e06010501030f020c010e0705010201050f0c18040b 89
    0x4200115001824100ac40032003240340b8414280510340c002e1030310303084c1850f02d030400800c55401001201040003e01c142d10000e03181103480c2d400f5582490103d42c5560410061009891242d0f440710510381102c040c94015849003001ca5070603e54901c8040b80c030000c40c107011001c4c2d006540c000d030f4140c8104100010010b6000d001d0006840ca941d0364180c4040c4520801c90690040e002ca803540511080d2207440030b46010181c403040101c2c10b0050390b000240c0790300e6400c1800e48403c06645030b41d40002d0f0300011580e040c498600b0502c00c82e40d420800d070600b502c40c1c1d0760b07480050000401071008008003805104048031401c007441d941e1604030302d14030628000c00001d0909980d08035002034141031465441030041c0201d0389107801031802070045a00c2c1900440250203084100024203508002c00020302d0801e000c1c5000b1041440d0090413203a180000090840308011b0a4403145000c650511201400b828100e400d220884281d010b01d490005001400801c80044071035448031142075020245 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 255774145 1250 255772895 255772981
    0x5030403080a02060601090332100b120307050601090e0a02130603020f040902061e0d0908030402120d0801030f03051c0f0f061505030a09020904050601090e01110a0305 74
    0x2d003403180d080c2c403519100c440055980c40c103940402030008245140b0350103041c9000b106244901c81e030040d5a12005001103400e0300b40310102500500c000e4440d00c0d100d1705803e05484440f030103101c04008620b07040d26a180d0b6501c82c601030240d0a421a1140486482018200b0403a400c1640082c1095600610b4410301d400820316440100d024800440300c02001d4a40b500c07400020580291060b8a804902c0c280310713480c404100d119103881c4c0d5040c442258040d64038458025054450003807203913641454010000e45880707045100d0500e5010f481e06d902416805031526044a9003d4000000a084d03407600b51403a008020104440e0085010016104902c0782c00908462204520421514004009040c00e6907524010640c000e882030113000300e801e12039002154443d01c452000909000c050780080c3c20716005540a40e1264008030052202c205580b00708207084020400800800f817000054880c01d0191700f40c84018540c0d128001860303240c00441400140c07000100601c0c00030b118034032404007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 255775395 1250 255774145 255774157
    0x90d0809181504061508060a0305010e010902040b0a08120c030c0610060f020c010e010e06040b0304140f0f060103061d100c0e011704110607140d080906250c0503040308 74
    0x111100310750640c011403c1510850040d242805c8400c0c480d0f1841e6001a02c00940160409030803060380900007000c1102840352a668110040011800c036a890040100391001c07100c04074070490045800300140c0d40700080c0b03926075030401c540701c07a108e1041100311401e40c0958074250005009580800c400c0b000720442c20f01c00e80302c3d181c031441b950b40600b0800703d07654100010b03042d0104490201000709507005201c4401d5444c401040a440c040c1c0382c00115180d40c00545040710340750074515821941ca00c060004103800c08509008045003201010000e54500061001034001a5992080300b0500201000e4200300c25509003150000d44400c0a0301e00180015a9640001080139203903a41c9584906050801000890604400c90b215074440c441d07040c600c510380b079a206a0030030400700041c12200328140048140f4024011200e140207000d8565a4010541e50207508000100310002d03484a0090a5040354000d180700c48039268401511000c82141001c2c00030310011030000300b00a025001410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 255776645 1250 255775395 255775411
    0x108061f0905010906111002030603030f04091406030f030706410c041404111306050c1509030a0c030908070b0c01060e04170f0d0e030a030b01020d0203090d080918 72
    0x8415540c0705c408450440d148003c01c4081e07000203010080351031454002d1a0000c40080c02d880ca4010442040042c43d0301aa02c01003000e44c0b180d030b4031400b0f4900c1c500004d60001c41900908460003c4011143c0c69104080e4000c240b541c0e2440b980d51504000044e4a091b003694501010795854810451140000225054068001000001001024510195000ca805a03090171401401e00341c1000040c1000315004802034000b804210100e05144400380d0050242d6110039545880c7c100c4d009041c0f44110f40144803d41404060100d604000011516050018a007000c0c138500185812144010380d5800300c40d40d48541c0201140180211005002c2c00d47c840000b00411030740c48103180000b800c00c4601030006254040315140000c0311000526090070381c0744416143c40c01c4450400201c3d6980d0900f0501c0341e20124000e45134640601c110700180c0c0742400144001c0c250f40030025036a10445400314050f50320320099500b0010f011040d6002404000d050450301000c100e24100c2d035910851f0845 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 255777895 1250 255776645 255776657
    0x1140d060e0127020c070605031905010f080c03060c0d020d0e07090b040b030a02030a0201120e01090809040e0105040b0a0b010201020702060706140106051c0e03070507030b061003050606090108061f090501 90
    0x100a4003c51007210072140416010b068090310300a0195000d410081081c0307911603141d1810040c07010148100c90281600704071102185081c210355610380030804519074041d44c00304050002c04007555040d18890012028050b90354000180d030540a400c552078075001c1486003000201c1e5448460b00b0044003403400740e0b8200300d030040c01c03420141d82d000010800794058020018150243d4411522022010765034000419122440100582154080e103403c1e0360b0300c003010820349414901030041e12101d0040500a01050034903454180303c40707201420b1721001c940e0390309007107595900079010740d1001c507001454540c49802e1070a225020300001e10b410014a44c0150000c9a41c90041068440c030880413500c10350080c2c0804000c400034103540ca081c1d10f9234882030042c280003d104000320b4003d10b12500c1403226509021040c0070003545110184003d0504140c108211525030205643c0300500929200c4400c0d10f5410205115202d140120b07070700c528a90140303110142c0c0081d1404200c48007070b0390f82 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 255779145 1250 255777895 255777959
    0x1509042901050604050402030403111c031a101b0503030f0109060602060f0703091103100e0610081005040609080c030304050c04020c0a2004090515011401140d060e01 73
    0x128440140c240074096115000344824850b504140e0301a50380544a400d114010308080001d161a16403801c1c92151205891080c0540940d81070051390780f184004040401e40e054100c002440c10311003502e6902c1000148020b8500110440345280c0c0c03440c0e0840181c17681e03030412951105501809006041070b560800d400000e007544005490342c480d0041d240c80041c42d85402008901071b0021907002d40c0d003407848440c038a9070b0703581c144049150002101400609001da00d6001420301303100034080e0207860a185410054401e000c01c00500c4a8004000000c4c00d50759407074510001d100142002d49190300105a0a002100c00001140910b00600480311500026001c00013a031040400403c1c26400c031100980000d1501154602181131200b21010b041c942c81000c107080b01c641c05801e40c1c041d401124000800040c0c201c03458050040160b0f200122a110000a85100c0020441648a0400151414a60721154402d00c0a44401d421149031569140d46117860138040e0340b4682c0b000d01c800c203c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 255780395 1250 255779145 255779213
    0x31c050403060b01090e0703091a07020c010e010e0d0b1f0303020a0507120c03060f090b07092405031b090a03120f03050f01150c0606030f0515010f0e150904 69
    0x4003008581e541d400c0c0d61b060740d4411108901a0082e55811250141015001148160311151540c0314038402d81c010041d14014070b00041820b032102c01014140912596065025100c05075458800390300a901424592500c08030500e842c0d4040c420804001b440d00300100c1019404505050550f0160045841141d11072074014031942c500c020040c002c1c101902d08000165054000701c3c54030440c1c00700042e0440c0303940ca030a4101c49080700c6450004403104002e10030308808141661030708001415602000c10401c1018003140f0010704180c0500d0682244203840c4a840002c80d151544058254990700f13649242509a000f580c0c002c0034045150b140b441c0045034440d1050f18420180840c0c8255940d1070880e54108018841141e002008000f000c0000800c103a8087c480c011071149003599103a02407030078550700344403102e842980d4a031200350040240714091101c050646915524070700242d15491816450000074180342d40e0031603018420801441031540a48095011080300c9004900501c24 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 255781645 1250 255780395 255780407
    0xa082206020703030c03020f0d03061505031b2503030f11090a03060506040b190801051612050705070b07030e0f010b0d06020304020a0b04030b15010807020d0e031c050403060b01 78
    0x80303400580c0851020004648148002980240640180d80348040700c4c154003400c1c80c850400600200e9110719003004030540340d60010300d80348014a00241181001805158000007101140003009000320302c82c0e243c80c610b61691200300100082c10741d46d50890f884d015026060340c40804034190701d4407420100005801d401c0741c080e090020b0069012500b50b694010013401d01a0902d90003d644400388035154480c42134080d9003912104407030ba465485d1807080360942d100245450802e071450400e011005801949002108014402c08903c40e03407260350840b101c0c003901c0d00182603441c207182800038071600b40d03101c202c0f40f40110003a9541038042c0d40c0c1e0b0b682a07928032642e81d600400700c011486c02082d501c0e4069a0054801045190480c0c0d407121148038540280c0c0003a5201412241840001410104020a02103003801c1032811450905c00c0a92112041680c910602c81d070340504180c903030303007d2000d500e00003280343d0b12804515107000c0090041d001800210748262522010320322660080d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 255782895 1250 255781645 255781649
    0x60c0801060f080402220207030309050c030c011218020d1a15061206040e0a050d0e090f0408070302011d070f0f15120209031203040b06090910020901020f0a0822 71
    0x18a510360355413159030074010801c141c075095085030081901c0c14201d4a100340018000346009035070104404a681c181107040c46c3c82024003d00c40c1c0e0180403c0c05003030f6008166204c08a40c2d0710800103105000c41c3c2c4000c440305c41e01000943c0108000c0701c090400038004142d0480c0d4851604040c8035550703c401020a01140d501c0465101500344605241003a05038902175005070041c101140c0d0300c0d07000d0341341840e00c1d003008403c541c56000301407401394803507203c901170760300d01303411114104107081801c0b00c410360030009400981405400258a421b06000b508225000010301c0c2c054905103a03008592a15008070380594001c0c00c50300100002c0700d002c0d00d000b54064a60064450100040100040e070b030300e0740b40e580081c210507024881c801c2035a80900505004000c000c614660328540361528900305440204001d103c1d107220b6003400008100000d0341020340c5502240160394900c201c0061b0303c0c00d00e007001441c0440c42460010310030032a40c1d9014200d281c3c180c0410104600321281900c092200034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 255784145 1250 255782895 255782897
    0xd0c090e0604150815040b0c090616020409232a0913060c0f0e010c0f110d140102120709060c020910030b090f0d03020f03011205150103060c0801060f 66
    0x14002207141c0e032070640d1105a403121481d100d050300d540c4c1c40300c0c00782c00c00b004020914003407201d070400c01c000c1c0640076035a035600c00c80c00003107985001c500d040090440d000b40300301069502c089540302811502c8552014142039040201e20500038401038110100307080c0d502c00b81221f0701800c442901d180762a180c0c08100e030f82000f040ea442c40034026043c0120480001c02d40b0307544814028481c00070481c1e92041c55403000c60b80d03540e00c120703400c811005820804591132240c10005130351416004182c0d81000c11400b1a80420700003889090f120001b46050030303003480503250601c03160a003107210700c055000300454020002d40500c1c55545000c19500081c01d03200e0380d000308d4103015a420052030014030103030b4481100205840368684030f850386a00200115008049503118000c581c5020b44d041042008400f91842c06601d408103403040d6000a01042c4914600d5801c0041c0c2002008010f00143c0055039400c894030680350307905d00b09140613204803815007010800c8400045400c6204441080008e249 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 255785395 1250 255784145 255784169
    0x609020a140616062007030216081e0102041e0302030105011205120c01091208040b0f01060509060903010e060c04030c0e06010e010503150901080a050708010b0a170109020310020d0c09 81
    0x82580c0fa20018002e800341101da080d070710110441545000401011005007465060342c455810340342c007038a8111a2140c2070241c1d992034404002070200040c101152510b954202820400381c10201400790003280c1112684031404107000180039000c0255208680c02100244083d176a20b001150805034801c7e030140468004901e884120038155009008900025000047d900c0c2603481d0b15248055482440000500e00c1c1c0501003844089e00030590054282c90040510354500440500f09200d01120140520404248100a03940030f60103c50414050700a803940752400a018a03020341c03141c00122045d200468012815580300740e8911b1141c00c060f160306000600560054800381c200800c44102000c04010201207502c55003446402084642c00070900e80e8007511f04079041891b40d80111500d41e00d4021040744560300c2c101c0d0b08044440003d240f242040c01011001d0141104200c00b94040c03190000c00005006181d000b4000640b03c000c0412010f0044078040722903074100c0c401d090f101e8070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 255786645 1250 255785395 255785407
    0x1d0310230705121009050c0a0f030b0310180501020a111603030203030a050a0b10110d051905090310020f090a0b070b150a0f120c051c0f031202070609020a1406 70
    0x3802245030f58000c08524000b6043c0356442c015801a504100e990300b05251007c0b0b081031640740c02c0322241214481608050100f40100c0c4086642c1d04400704041303040a8031600105d05004a00c5824291150040c0096540b0060807001812401c840000d1000c10b01c00d080040080c0f80038400d040c425a5410740c051440c503201c0f280118081c200152449841d07903550600011070f5951013850452208003502d43c81420b10310496201e0510040904045c113000c010800034840c214083d02c2e06800540c9410305039120750400c40400d107400051040f01004900c0052009003c0b01d03888081c3c01c1c103c01c2120010709580c0c03105034000450080c42c00c014014403031203020910954840b14481111700c030140402004e59650040140d0101842c0d00001498080f08050010b005c1a803200c40040d01056983c40003d01c000b849042d049840060041e00604104e5004801c0603c103d584e280c4150000c03000f95141d0100e81800300080080c0d490417031181d050008002a40c1c1827035030001070643d40040610703013002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 255787895 1250 255786645 255786667
    0x60a0312030209061b011517030304080309150129040e0f0442090503040b130f0608090d0e01020709020c030d021216140a1d0310230705 60
    0x240100082a078410010301019901454040d410441e01c5e01d00c02c000704448030020468111096540c00c402c14010b207000b250481000000102e0742c0042c0e1090b810340d40e0360382e6604c642e030811078041444d41c2c4100761400000380c880d048030480310513128044040f080b40c1588804594043c070a51245c3e03110418002c0010b0500300c0004a00c1c0c0c0c0c82802070000c5152150260105402c00d00c030309030441100000d031640141501c107a44201408101c80140420030b5402c40d8071172942d40d0150b0b100d2441a03400c0003c0c0c08030225240e0030351900510300384854a40503625520054400d2404480d4804e0341e204400c40341c01c0091180c9072200d8030440607006008030504004800001c1d500000c4c1c2105944030401c209000448144000c05504508051700756140c2404010100e069483c032045504107c40790302465032400280085580100c86810100780100708040403c0c6a2040042c003590b042c0950b401100e00496a41c201070003005850310900d00a103241d0160018150b0180d810b600000ea0a1021003049 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 255789145 1250 255787895 255787897
    0xb010905010318150c1d0f0904080423040b0414160207080709090507080a03050301091a09190c08010f05210106090204091811100c14070509060a03120302 68
    0x701c44a00c00d030010142180d110404000c0100b5450b000c04c903901d5407400070f85940818031001070b400341948200740e9049500000c08034440c0c000000c1c0318525000216042208081c12640108811840c9042c01c0c00c82c8a000c0356035000c0d030341046000e1814070301948250300d468070034058a84180c1200315a60340301d002e61702c00745188901d514030039841656000304240100b0098240103107107407040400c91000c0d6180c1641417150726840350203035601504111000a800c4416a0b041d2522080001080a00004090002420485050b4011241406011b02195014030400c2524910b03841801140d0622004448a503024416040180e40700035051045282c505040a50301c012845400345101500c4641e5003141c1281d409018134517030015080002d0007d80c010981003005029001c241c2000b0b86c0c6400b01c00400340e0b24403620071007081c604149928041e01105600700d07001960342c0910244c40c200360750303201c0d00c900038a0311030807030000021641d02c0e04100c410141da5114490186404c200c8000b90b0113 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 255790395 1250 255789145 255789161
    0x6061303080a03110705160f030308060f0f040911040510030203102f040911030c0a031d010c08010e01080601030201020a080705070b0706020a0f1b030e040f1b0207090b0109050103 79
    0x3003640300e42d0382640c018009400703031188500031b402812140c406500c02e0300d01c0c0012031703000c2090030f00100b01c10000321381c100406c0c99100c201134030520844001c000000d2003140507a001d4075031040c500401c140c01c3c03000d10064040245000d581c00c200d1911411100240f500151000035410f44c01120001400f40e810b170001d4103020b540505140181115080700d1410f0401540c05486550b0045010802c081d09070050f4040203221022003451802e240601030300c203104c1e4152a07814103440d0201640300c40007101b528410701c0300792070080001c901c1201d40100111802c0c840c1c0500e1502080c0003164850011031224101ca605800910342d06401c0c1d5105101600000740c00c1e5543d000b914800110070001200802d1424410a00140e48407034948014240040005000041103995842d5092041c1c1c10004500c8160309401c1c0900000000b800040c00703031030603a240c90321003810002400510205100e42501c2c01c0c200d90242d84400c2e48031017501c3c1c200c40400f6001400141d03c5903041005500031340c08101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 255791645 1250 255790395 255790397
    0x207050121020f12070c030315260f0d030207051c0f2a06050601180e011205120708070311032d070b100f0501111506031e03090906061303080a 63
    0x10400d00c00d807203521a84d030011598400880d1340e030b07420340d410940c0c144076100300c18003039400d00d00000b401d00d10000b01d1105c00359002e01e01040160003081d1801c0c030400c00481c0308070003035049822000071442c5c001c4c00313504000400c075414071850200322502c00b003851000e03519100c0ea035102800c4a41440c4105d0b21025040e00d1009201014a0300b20b018070106c0501c000c06034015034001c02e0504209000400700180d40380401e00e04a4a210103000d598403545003981140e0004222059035041400c14a0500004080110742d401c400207140040000c02c0000d000390034003076212580300b4240b40c810700b1b413030303125080207002c4234a20945086012407400284040d01a06c0e00c050b14104000c5030345036145070400b40c600203d200d40c0342c1c3d010046a85174441c020b0140000386403801451b006040036590b2841c80301016004900c0480000781c2035102008040840805c6035603140784507511110860300c2e54000e1501900448122002a100c0e0800c4812948003c05000c0c0b07602140d40b8549a29142c0d0b001800b40c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 255792895 1250 255791645 255791647
    0xc070309080709051801140714090904050609121206010309080c0102031302090114012a020a031a060d050a060c1b142104030f020f130c0207050121020f 67
    0x401d03101010800030000d00034030800056503007011800503604e84078019404005030705000004040c10a21100f164028002e410600300e018008083d8008a000d165011a00a0742ca00200000d21100160f824010320a00c000d8800d54004569441c10a2083d8008250a850458007103021540309a101008045c01100c0c107a0411441e00030090036a07005a0300441c0d0310000801890540c0ba118101900401c0c0340807100f200c00d0406400605410b182c405000d4540c0da070000c684a05518128196088943c02002c11041c15120328050442c40c0d1044030303400303801003030303400081c0d45003031040e02c0050003900500242559075640e070324203002c1c1801001c1c01d400c0019640303503500000d00000c1203007909403280d0300680f8100080400c0030320f48402507240301d41d080d8040140d82c01000901c0101d4068a801803131450f0307207213560f0000c11800318000100a804c40548000103ca03803040742e1004111941c140c0c291851165178000440380034022007503852a41c01d540104111000d02c0d60300914184080681c42 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 255794145 1250 255792895 255792899
    0x1030b040606271a030c1c02041e050907061704031218020108060406060801050d11091302030c10141806040803040518010b07060905030c0105150109060207030b0c070309 75
    0x40e0b402102c060301c43c076098010540080348000824068842260050070305500507048040000e507490342c9084c40700b80510040010422400c980742a400203d6801920500500b40101d40c6088400304000407800c489203044041100080081041d40455101c0c0d9507a030740c10320060b1039900c0710030f20141040b030070300008108164000005001d00f55100001081c0c03038500c020380f400094200d40300100b1043c42035260440030b100a0741c100c0c01d841d040d20400c1d520012542d01e54500801d50040c04007140c1d038410100c00800000c002503c0c180f40c600e9100303030160f4070010b14580a0050103500b00e010b0320081395000046075001c2d4045009130003084a5011003000c01070841010a06961060704400010b0b080050107211600308030001c022401d00120b141362156241550780a03060242003401018262245c0e6180180b00041060352a00d6450390002c114500380503020342d0541100c2c00400e800315a00c03003000900b00d400072540004581d003052007600700781c0d40e190880c1c000e540199411420f008040c880 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 255795395 1250 255794145 255794159
    0x16111305010b0306030706080126030c100f14040f110103110c01020d05070801030f030507020f04140603010c02010c32180301060b04060509011223041a0103050601030b040606 77
    0x9914024082c2200b07059980c28030038141070409080340c100c44144034803e4010800342c85140c2010f45001418400d20b2514480d418100e0304500c25488000030900c610b08565900720416444107003255220748003004640c1500511301443d100031100586007407100308003c40411614046102503480500d800a200501000c0307803103942c1c01c280341c0b01016a5001c41d80c071746001014458507410007881c0c01c04100030362550380d1340000845280001020002d010072100c0c110b484210810018150003803050040403054a081c8841c01c4080b10303032074801d600780303210406600e0041c27007401d06905540c0e540360107624020703000c15900c18940440c0d400d00148101421000c20401010b002c0a543c869000303145035401100701400e660480d0050103640c1410801040942e4011084400c074410038285000d6030048103189200502e22803400c0104500714006084150f00e0600300c03142310f207109110032044a03103401c0108070f0382d040c2408028075903403240b001800486c10081691354428481c1c0740216440c1e807143c0c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 255796645 1250 255795395 255795401
    0x1416080406060b041202210703200406060f0e01050414040e1905070603060b0301050904120e03030c160b0306090f0c131203084008070c0614161113 65
    0xc091401d0005c082d0080045140440000786116110000380740c403c5002440d06454078070a120043c050070300c030b1b5440c1c001c0e2854110f54580301000244100101c60352500050700500d88250a000002d0031203003c01c00c10341c09a0150b400391006603181800703003200f000522009007050300d010031240c0311b020010310440c0151695019124404d501030f00700186800d00c0541a0b84080e08101d2807220700303000510091b1502440d079a0702c1a00804021804401007d040c6c440c4401000034075007500002440c50040d050000d849031035200d00020046846940c0c0c0884c0c90b2900050710020b5110721001c02103480004941da00503001088040c86038541941031754040900311081d40907030003401c4510380e00014541c10070103e81e444142203040401c9540042c80207440c1d41101e03100740b01a04c00409400010102e9100c842202c1684084551358071145801c00c80c0a08072248209000103118030220610f0385000702c19100c54850f004a0000d4458140c0d03640c07450075001c483c2850b04086500a09030103d10540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 255797895 1250 255796645 255796649
    0xe0c09150a05070209160516030c0c0801020c0c09060607021002030409060f170f1519020c010203090f0f0606060706090b13020f060405010212071b0611011416080406060b04 76
    0x81c80e42d55031400e9600c140115200e0040c152048400c5050300c2c4030300e5035004022160030800d108170081c4010303403e140980c0c0311589000007030b2419401d10700105607007030158014403107181448100c41803811900100b0020a40480da16a01b042040c05000c0046c103101402000e0480d803401981d0810740c41d503d1032403c60340264015020200500401c00c4030340d101184804100500b080a0300c1c40d02458103101d55507103c1105810b40d0000f40350000b6090414003d00795000c42d850220075035440c7c4500c0b4565011350010745080d400380c040e03440d01c0710002c4000207115440c0401030010700056034681d002c200007500070000c1583c500e07443e566041c00003110200032904c94205201d10040c602c03a103005020100503c0840d00b4010101048180160380e000a840b0000e40403407050345030b507083c07035160201c0c0908000042c160000781134080440c0c590f400c0380407408070040440007000184c0c20325000c0f000f14901030b20a44000242c620100d24298410100c542d0700c58001c150116903c0e81e100140c5009a11039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 255799145 1250 255797895 255797897
    0xe0c060d02040e0403120c09053001020705010603050601080c01170604091202010c0e090c0702042a02070e0a05190207030923120102040602070b0c160308041503060e0c09150a 77
    0x1b9000081001126102c0c0b50b00300d000354640880314900b46004102c1030b440760030403040780034160069050010317507a100c07001c0480d626500964032030046c1d04c1c20358040c1c021800200e070580100000441c0b0440c0000e40c101c0101c40582d12107000c1c030a000300058003403201802564000e0b031a000600d011840e2030945000003209580000307451080d070040100781c003180c110400c0c0700350600e0040c07002d00a81d5205868245404031400211500b460b892501300d01c0b01c115010402508103a81c01d440c158001c103440013101c40c0149840e00540d01c03552120122181204c04194220b1103941c0004001815405042814480e0906100d2903071108696071100d40400140418810381081040b01420b1441c00059859000b4000390709040c00e000c0003035298400390240103c20500420b036a0032107041040040300d000301c0143d41c10b203020f440342884121507001d40114141c0c0e0240c5680001c034a882449034000f240c84a12603a00540c80d40756442081c2d40c030601c0600d0b40400e06c100e40508182103600100034000c01c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 255800395 1250 255799145 255799157
    0x60c0403050d0c03020318030109062c0a03020d03110909090d020705030307020d031404181b1706010807090902030c040f0f06080106050304020406030b0a050a06090e0c060d02040e0403 81
    0x514900280341c00d5440103500100000d0000d90741c00a40c0000a442101010715047e0304006e1204002c2401000a8207000c0d160301d04198200520310130003065075280050150780798044d9400389038155a5010320031401001640103150928a1a1095200d545181d074445211445c00302e03160001600000b0940300d280300c035041107160380065901000444028101500a94103100ca9500091000c61943c4c03005000e00c4200c860a121281c521000c1f2009030955131031846491801034001d038003e150040c44102100401018641c416001d100000210884e9a004400c41d50740c00004440c0c07038034081c01181c140143c52101040c04070f0130f400034610541e014402240c8542c506042d0350b00e0049a0791242107031402a100502201d40d0245521b415601542044c6559480720320101e001482d0682c400f034503551080c010701c192a00c50b0b070030540c025464804188005500e03800c0c184100c070303014a403800b540d50203000541c9803402c1000241c5002283c085005003401e03a0b45488004e075220480f412000504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 255801645 1250 255800395 255800399
    0x1407060305010510050d0b27060f01080f0a0903140c010905100e030415090e010311190506040e040204062402060702030405090a090c0f0b1b06060105030f040f05060c04 74
    0x16040c440d850040400311001211344620910113415480303180100588151141c45c90300031a11401d641034869001070014011402c00c18000c4401c0003402e4410510440060b944101c1541c032600440e80100541003d0040c6ca1703c40c00341e541c1c02800c4c80e000480522000401100304501701e00041c000403007000c400801c42502615140d400c114140d01d60030602881d00400001140b4000180c505562800300c0e1442c48440300c0b1801d030780e2217416610140a10301c9042c000f1042044c400c0c071a0712401c006440c102c14141e0001c83d12910842603010313841e080341d0203200c10482e22040703a02c101e401070b0014000003801d03515505100c0c0001407036004d444080821906146565504105060740401070b031016508090915001400390440940460521742e200c4404005001c0d010a681000300412096004c0d01ca503a039040c04010307000500791001260f14001d403020b5812000c143c091240301c0c140e54003483c42c0e6813585410270f8144090300950f0b0419001c085400040c60030825940203070002890207803594 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 255802895 1250 255801645 255801647
    0xd18020604180518031e0f030109060510031e0b010905030307050c280b0a02030d0606080a0b0411070803040c1802190201150603020c161511060c0d1107140706 70
    0x98400781590500102180e45161000e4012099030f913032214000507406c01000040d250961806004031001071014004000103c1c8121580701c0002ca0340300380e69856017460280c00640445034041c0088030f11040800c04559034001541c080307103407050141880010f0301d031110046480c507002000110b036668048260300d01d60f843c22826402a514682103a00c2690b12211032410f0415542e2041d02c0b26010045a5401c0443c0203006544900d001c0180030070186031381d1400101086403d60300c0085052034051040400e0a02c0d028007400c40404000b01d82c90104d603a540c07030809602c028000d07250491000e502045080410040320b085812031980562924404000d0080d03003904181c028007560301d0810010741c0f51080d00c10b4502200ca030b6080c0140c80e101c82114003810f22844a00c540041c9025134404952180c8112103820130045980d103002201401420065585800340c640c00da02000500c110303c4404859004400523020844005007011081d0ba60208c1644ca03c01d00000a070700280d10a2180c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 255804145 1250 255802895 255802901
    0x305060402010e0915011d0d030c11120c0f0d0b0c0901030501051008150105132606220c091103060f010207050d02040506030109080408150f07050d1802060418 70
    0x180030102da0984031070130402e10b050000307188001c4146c14441d42203142c000302c04101e2041c0140e0603026003076540380807442c54018446442060110b6008103c52650191070400b5003480c64480d000301d0040c105a1140340c1046000c0b0340340030100703034800708a41c80040001c50341e02000c0d0050041216070750300d903004403001505549050300036074000c112105240750b9040d440702100780c01034070b00300c0c040c40c0ca08101d50048480d0300c141841142c0c015130b4800c00141810f221941d0040d8500406c11030b0350b04400031140d135500c1786008d40b941005001c05644c440040d40300e5004005180b48198400002a951240b0803810755800d4840c1000f0380c84048104692810540c2c8802101d560134805801c001e810f102c0056054080c01e40064000c40c0c2e40e0b800030303da54400358840040035030086111600c81741e658240b180c0d10380781d0002ca0102c0c0862030b80401c4d03881d88280000b40c0515459224035042c030350828020f6004001c2052191010901c009112002d6190040200041d107645014004000c0d4800c2c4c2d55015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 255805395 1250 255804145 255804167
    0xa0f090b060a0503071b02040c0c1b0303021509070807090524060f0c0309040513022803060c05090405091c0c0c050d020d06020a0c2003150a090c030506040201 70
    0xa00040201c2d05950780d0001c21240c0c0940f16080880c1d0480c2014030345145a11075100003904145403c00c200f100b00d4001c10300c0c2084900c6613201d00c0d4500b1407a10380b0350342400d140c030005015034003030b21000100e82c80519a0f50b600849010494514030351f200030061900101e680030303001c03050759501802603915076601c07814603c210311031806100c0d00030b070b2022440601c05c10303403c400880000b01e51055010360900c1181c1280500500074132050800900310a0305010b68182240311b04420400c3c1103000d0b0301042d10f40000304a14984071600f615507110000500300740c81c400c00801004004040460b038a5219650040c1c2c0c0340d02c020301c004000310064014084c0c0c0308020105010f410b01071080000c1c260301c03151040d04d40948689861500324400f15901c140e6590000f80560700118281503607070384c0b103140c0c024524040d007840321440f0001a55202c0003032400802c2e03505900401640882480c0f01c110039504600d1509000aa185e039540b9501d150410035041207503960444000c1c8030541d070307220b00c0300f4070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 255806645 1250 255805395 255805399
    0x106030911061c0209030a150b1c03020604031b210305070e13021e0a030b1e01080f060118060801091b170c0405040e0d02060c0a020a0f110a0f090b 65
    0x101d0b240b14902043c0d03446810004861100c1d4001868804e5a1410b200c0b0f100c1d0103501c02c01c010101d9014444d0000a48252418180500d21302000841d10b404102040d250094040d0085e00c00c5465684040b940e407602e0019544181d245041c10304000b960307004400e0380d55a078181854041d0918110300500b40c1d240907107803000b0415150740015190381e03099440c0320402c6079a100160f4407200b001550003410320942e1040c00e40080820010015a01034219191300744045440c500c21041c0681070035194402c590780540010b071090b0004041409036040b0b19085507050401402c2048809004402d80c1c1c0103400103000603200f1401000504180e006d4006851007152540060005261005220140c003032000c1c240c480013100854000614031003241c000d090098814042c0c40c01c07560810f5560241c00001900612071000003910081e60745054940300006540038120142c41ca840b40d054059943c003080d5201d650301c00b0102c04503a140800d0500809003101006d16440c074100c480022901c0100201e4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 255807895 1250 255806645 255806647
    0x2090c0307030b01030e1207020d0606150f02070b1c090b091f0c270b0d1b14040b09040b030102030a0e1605090f07020a060e030301081e030a051b06010603091106 71
    0x24030040030101c3c540087c0760142800c1600c9089a0000584c003d868440180000d80703824408244403d130040c2001c250140798550407090b11200c48200d03030314030b11742c424140441e07020300001e102060419000760244455440c0440c0580180e19121050380c0c003a5443e2017944c0c001c80a50f40480030800209030784a45441c0d08111401c000d410103855107081109006c1c0a20440304955480c004091443c5c000c0c10b8406078031070302c4070480d00b00440140003000300100428101402402484d1184220940c806049a0310394103040c81c2045465058020041c01179100b51241c038030ba07850351424030186102e8220740c4c20109844121200c1d1b242000719140907004500100841805a41c803030051071a04403119101100c039507510138400300e051000d200740003040e06007040d40780d03c1c1c0b40e00c001028505a0319081c0c01e032181c20308100203a01c201043c03142121601e03002407002070102030080000d0300b012100301c01e200c0f0350038904010550030054240c0002d000719580e21601070910000c0541d00c50030380740a458403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 255809145 1250 255807895 255807911
    0x14040305060f041a04050d080a021903020d02070b04231c0f0306082409010603020a05040b030a170d050112020607060504080f07150c0c03050301031e02090c0307030b0103 75
    0x9103803a000c1c01016420600035400c049400c0040d600c8484031103090b0b000311301c022800c05241c440c1d1110b10b4240320400103500c076804203c1c2031a040c400c03103d480b8289289111b80c80369102c015406508180154101264240007440103d031428030886e104601c200c0345038000c48808044010070b10569400b0651076031080c0107016851701844d100c201d0510407030030401654610000120080c05880d080b80e0801e025601d4600038140070030380c2e001450080c92816403500ea80b061101d0b802c840341031001a601c0500c3d41c0b4100014240741c3e20941d0100d03806000e9415202981e00d90740300d04c001d143c00f00700d04680001590103007411903200e12405413030a841c181035841f10703680001d07120f8000c495001e007400b80d0701c034042400c100ba202c1c1100c40c80700c4185282e0717486030304504201c01c141942d880d00321a030314100400b0000b030521410440703d007036034580c40709400c5900b99211401010340009042001c4a680502c8001580d0b070108503d1094180c00070b01a0303283f4040700000c00380c0750308615081c103260800540c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 255810395 1250 255809145 255809153
    0x20a15020702090c030603031303030c02010e0306060612090f0d121a010c120c050d0e010e09060a030b0c0904110a0e090405071401020c120a0b0906102d08030307140403 74
    0x5843d40284d084410151240c503610700007429842505503112603520000d000204140c0c0180040303da05000362a00300444c62803c1c1816100e503000c58006074002c80030040c00c040c4c011900845600310384102c049810100012601c241781090300c2000e4000b0600780040c8211002c0030380110036003c20020a010f50300703040040060010401154010b02c0280030b1210042090f00c03811210340b1864100e0121792440e603002101034000034150905900040074082034420a040401085010301005008441d68525544030000b5480000e80b640158050400003000f05030740c2d0340100300e10070155901217a661580e00a024096140802d825805038502a00300b1000c950040f61241c05c4449108400841001a00040341000208030710607a0004034100701c14001d50300041c0c18280e05100e86d10804494482001e001e40e100030488180801007081d01040c0200b001c81d03580d00c80620b0203001d240c00d4002d17800700a00c51085840c0c010790300300d61002c41041581640001901142140d074984c040c82c150643d11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 255811645 1250 255810395 255810409
    0x20d0c2f1b010e1302030613050903190c08030901020d0606021f020d1401080a02031203041e0c03020628090f0308070c03081209010b040c0e0f010201060b0a020a15020702 75
    0x716001030754a503148440a0350740950680002c500c00205181540c1d81400101c000942080d00c1d458001c01c000c0031880c402100c684209401000000700450800c1151a80321000c92443c0a1860801c034614000100003514500618003c01102c0005a120ba03d106c90b4442168003541c0200b0465005d900c46145400b0340c15a40d10b000d9805250240e0b41d05024002030000d004000c1c1e40c0151038501800000e203d80012886450300d80c4228141c42000d548180c5014141c003099501412108140707a0044483c40c7c500c44052466101e100c00c100e40c140da80e000a06650022442b42e01c0040c0c200000100c0c21065100110b07080603a0304003c0009400d140c0003607481505408010030340200041c0203c11b100060f0001c00003154884d443c60354400350313100e070301c00221001e954074110f0750700703041004020303160501032a500310466a41e0341e4030303060b441c00c10400000317824030860b410b656942ca80802c880404030014404a98203400504400d0b00c50718080c540d100180301116085c0b881440340200580e1115 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 255812895 1250 255811645 255811663
    0x50d080705104b2c060106020d05031609090f05060f030624040b040c09090b010309020f040c0c06020a0201090b06180708071e08011809020310020706020d0c2f 70
    0x1214107000304403208080320003011909a85006840100c4c451144402120b0556000c8a18002a24000c3c0d9071080305982da42c90340000c540202e841880000c21000300c1003840555211140780501039590741301361040407103c2607201d03460810340714410072040b4104180403900901068004001d03e14108080002c3c1081020505e0918000140b0000680d61590425082c03000d008004000c1710840300400391406009101d0140300900b028009015580a0b1146103403298001e000c2c454086a0041044010044051400184024045441c0103c1d1151002c2c0076200c48680001500d2819810040380c1e1042c014900c1c0e1013052a45140c04980b20046c400e290082d0306c5003411106622000c006503582d206102c07030304055150314a01503401541c00000c070b0f4126000f0650b0000c034040c2861222007030b140704034400b0307400da446041c04e440904100d0b401441082e0060b02d00604140d103100c0e8110554081b81891000148030b921070381202c820a10b5410305812824103c04c151444045d0900d40f40da600d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 255814145 1250 255812895 255813011
    0xd030509040f0912030c0906020601050f151204060f1a03030a0c1e0308010e0c090d02130b031902040c022107020a0b0c0609010c020a0309050d08070510 67
    0x1e500c0e8008924080e04048089948540d207036034030301c0c1d05132801070080c5420a50036001485d48100014840e00215585042c0d03403014004400c0161240f06005001680c0703504018070708420000c107000c842d014081540520f100305808201e40071400f03400000d840b11400c030068030400c1c502168925550000845500f04e00504001076a6401d90600b400d943c08041c10fa200d62040c035003025401c05a04c4014a0706840c0c0711155200e5588414003c054a40182c07400c6640001010900e003002d8600031007619074480440b113004c00c030b401041010a0911382c00c0c0d4541009140c1d410303c00e004500e000d010364581d0102503c000c00c0c642c0b8241d400042c5001c4000c44000b03140900041d01820354580d017684502030300f1070120741c0d541c905000b089982c3e180801c64040032a03518024401000d00d1000c2000b0743c2c11074050750f404608500740f004001c80c42d521903000312842c0c00308001c140c00140c81800a10b004100481d00016061540400c00d8001d01c0e00c070310600d44042d080185025400701000031030700f001c804 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 255815395 1250 255814145 255814151
    0xe1e01120303090f2108040210080907050a1d0a090803010e0a0b0a0806100e270f0f070f090b1c0c031b1a04050102072d061d0d03050904 60
    0x2490070260001e0403603070030250240000100a80500101024a4a0f103502d00402c01040d210042c2040b0b0f603580040e14000d47c09030f4200c2024030114458000705800000103020b4408c10703503640300000c8416403150311104070f00c4c0000705104e403030f1035500d010385512003040c0005100380080ca0744c840b44070b071205024003c8003c100c080811700b000510b500428a401c0d024000d0702e45a0303242d4141566680d800c8810554200d6000c3c0c01068130f010180300d0601079800e405000c1102600341848100d101c80711400410188158401d240e42d4600802800360402c8020001d00005418044442c60020385a00403004c1c0303901700401c081c810b07120ba04000c40300311001910803171004c00030b01c1c00345e10900480d440603041512141d0520241400c1d0a20901203030800c10080d01c503060107000c00c2c00a0701541c030805025801144003001072000407440702003084c1c640f480040c228000706520b1161209240c2021000940c111103c920000e190328844846900071200050610348554004081e8422075000f9400740791 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 255816645 1250 255815395 255815429
    0x9080a02100503090109082a0d050a0c0f0807030917030f070b040f020301050403050306040e0106030221030f040b030106140c0d03020f0c070b030403020616050708030c090405040303060e1e01 84
    0x10b8294821b04100b544106215079461410341e071441402e01c4103c3c508100c140400c54a0346c443c9001500f1249a04943c541c0c40c1081d600c14026507101c0315a803401e4555013401001c48001036050ec00a199103842600c862034501d041600c014031003060f02e0000122035004001c0b80d440c2c8010702c01074800c6d40c1d91092100f64103a40354682808801d0420000a42541c00c2400b031008140e049006944550800d4508000d1510051503890a03150644806504800f003130303a40c204541c007000765101001c1d15030b904a81c984143c41b4850211a40503911920803e140480144803280d808805c99000c0220000740c2400d0032101c10141c2d03140d0001c1c505403c20301d640000d1224820700a04261030744004103006513841203580740360100312039100b16412001070007080e000444000c151154016580380d540d4905d814594607581d51011030b400608000c1d4401000d22140107140d44500071188100d10076500070030080e103407007809101d000c00900a1701e464403c1101e5041c2c0d4400c00884203044400c00d55241d04144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 255817895 1250 255816645 255816661
    0x904030903081b010213030302011107020a171507030b0102070e010e1503010b1e040b060307090e040614071205010e070219020a09020721050711010305150307080d09080a02100503 79
    0x14010503c0c9004550011071070000980c40c9549031811240650000d202035114038181109920440034001d5014280c21001e000f05c68044140b0090800d01d58201d80c41084a54003481e40301c0e208a40c4180041e842c0c4040b0915544d0521001c0020051039401455039410302030341c405031000027402500c0c1c01c031800f075820b01256002d4000114036040500009070481018001402c2603c0b54145d00e40101d00b417110040c9a800d0507003c981c415281e0340d4031680e54a013404002650850003800a41c1c10f25110624480740c9020002c10390b015202946038040e11850007441c0340c0903a48164000b41201c8003400070041f81c15004a0341003040010014102546245e03403001074030301764003074109090081c404034102d0104400c0f0450510500c560540c20840c0c20702011044460744141d1000400080c5001040301c041e50080d0001508444205101c0e090a0080c1021a14000c450350015540354031138028102c043d07030070000c443c0107445000060007406500343c0111709030485510040040000020020f0528 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 255819145 1250 255817895 255817927
    0x100c0c1b0506040603060915030308060907030e010c050d18021c050a0503030a0b130c050706050402180901050a1409060105060f0d020403030203070209060f0108150109081f0506090403090308 84
    0x70300002082e030707621103498820003002441c2d103000300d083c4180b07000361615900d0541040001226459590700d02c01e641c4000034804c0d2540e000d0241024103480720fa40c0802c043c000c0c011150301d11100d82c0c450b0b480e8207080180b4400d8400c40c80840c3d4040007208190320168454107600941f41d550708800c01341003e41031500360701c1d22481c041c014010740804030501699924640001e01d015104940c55002e008190300841c2c22600502c81e1302c00421000c001160024515812003a8801d000800320051031003000c188500300c000480b024016030750b4840812608800500c180e140703a4454084549651400040c490f40d02c183c1800340f58441d500100780100b001000b0021154040310110065454075600c0c94040e58a40149100f00e104a1050000580c982031804804241080c16940d0a0580d10b0b103004084181c3c02d00703510b20341001070550700410b940310700304092500b10040512a14503044e020980004949001e44550700c10003081c0c00f030001103548854000160b0b03402041d810394900c013490480102e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 255820395 1250 255819145 255819149
    0xa0e06030c030105130c06111b04020d091515062a05150901060b0c0606010c0c1a09090601021f0b0d1406091c09030b06030102040b040314100c0c1b 65
    0x490741c04c0a0820208003416a0368401c1d1070301c213044142c1d61750746170001503034825018001960a948031a594041075100c001c1d05190103480a0700061524100c2120b50065901d04402170711710030400b0050120820ba40c1c40380415a0921492040c0c0751401d0120090030220807100c44c81e202c200c0b4440c10310100d071901c0324205c1007590141c210b448100741074039003016020302114444080c1d440d04100090071070380c0b00300720358a00304ca44020702041e598141c0103460951010034161502030102c180030501c0c84030701d400c3c0010f04040c400c4503601c5a1258040188000d0020a594115004030103608003000404c50b0010340c2540701d8002040c55517400012800444010501070100d0b1031200c4e80300168000451007600649185081d00c0c94107880d048055503404412040000040681038104003003009440c0c02508124020000351034203070350352030213000ca81160708265024009400c900801d468104240307030700144200003d01a000702c070080035001c0746485802910801c090505034400c0c0300804107400c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 255821645 1250 255820395 255820399
    0x12020c0303041d15120d1106010522110c07090b03010c050a120207060504110306090f060c070614100f080c0112020d0902130e0c0f090a020912070b0307080c03060a0e06030c 76
    0x104c1c5c00d10414125a840030080038540105207088102c6680b40070104409040c0c1d41c0140180050280600e28001954600c81c680c908480d81d501c0c01e00e420380f00c0c0c41c1c020101c80034000004d103072041c2051214401c444451841d20f2280e1314000314071113241e4006040e41e9a180907820156410b00700100307440f029108334480140003d282808100030000d001c0c40ca8040400d094046920350359a840b00290f58050500000507540c1c400b40c0041d904202c44801841010b03c95140440c10401000a0101d949400d55858000008a64042c020014a00344140003409607000410000d00f2003c0040c0101c0d46a221456513a9000141d030b0b1179280082d0006d01000c5d0b030140c0030442090503180d9400042c0030307244e03913031003107014003568040540780c0340e0094003840703c1c0102910750039141c041c0818000c0d03004203401038112000a03103054954005110780c000030325a44500d04d80e6460300b80d01c01040000300402106014006009005a6850345251107041e207107181e55042050300c2e008002072800080700b07a255 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 255822895 1250 255821645 255821659
    0x90712020301060c03110604031e0c021c0204110412020d0201030b09040b010f0b070215090109080a0b0a0507030207081c151e09020a020d08040809090412020c0303041d15 75
    0x520700f507002002880307590103591201c80188020746d01c10b413200001d46014001803085442022104100c0c480821008001d0500d206600e01950100709121844160781300803581401400007035040a0080340d49a240114450b4076090420560007415101200080c3c0036408880c207c40469000340d024041894009145222500d4240782900c480042401030381481e0383c40c41c0000a82402060a4403180ba0b4020325241e9058642e25862483c0c0e0844000c281c10031441d15000600e20006000d90081c2c1405400c500085203020034a180c284e032409061201054030400c2010081501e401c1039401030f941c0030f009010303a001544410b002800360f0b841d21038424008200006220700707030005030120380791088910210b16940c5000840c01ca0082e9140400580c00400d04542c0c8070744134000250340144210641414a228580410003485d002c035811203c0481c618822a800c40e01000802c0c02200304600461409040500c690111034090810b40c000104a001250b4a00c20b048a03410240c4005041d01d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 255824145 1250 255822895 255822899
    0x1f12021201090c0e041a0114040f030506070e09060a170f161d061c0609080d1d06091209010504090f06030209070c0f0206160b0703061502030403050606090712020301 73
    0x181d0003c01c802100d1a000c60341240005250f400d1074000c0742d418a080c60840d0740740038501801992004103640a4030300803030041001161010601030200c1c091800360000344014544100080c1c5118220a400d500c100908400c0020950b95004a41c0540342849041c8d0b5111883d098040d2829951602c596914080d4038880045042d409034003008070781c00c402110050f44c600c0700705401d00c0381d82561015044001a08555403895004006c83c0181d44a248000381046036902c0d0450395030007416500c1d00d0b49031100c2c44c40f040940340120351100c03801d076600a01854200002415a1411210091007107600c001ca40c0041c140c0c020fa042c1c40061101140501c404244610070500502c5240012442981400d0101d1642d40c42502d09541c01d6a11210102600440c0d0b0200304098101c0c10100c1118038920002c00c0015640300041801014540c401003080f500300391031140102d100c4044ac0e001c40d8002d0204001151001820a40105091316418101c3d02d50340002c41e1075140140c04942618000000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 255825395 1250 255824145 255824159
    0x10501180f0510050d0603080c0709050609130830010b1204021306051201020a14071101030b0f040e0a0506010501031401030605180d020c03060c04270e1f05061f12021201 75
    0x2880459811000e42b2845a1150181c5040766016102d4a8202c1c1c040d10000b003c08584001c80c081c00f602906520307040c101c0e103ca5140c0141c0060440503004031821019079000210005403174050002c02c1542d50a24610002201c80d00c040100044d10030001d803010355041402907804600a071101a007641208a03142d031019010b503204407040300000f0f10172042d030b40c8462556800c1c1c90000303610080410350601c1101c01100505400c03055958091040d40d0340c1101669107100305d0420900c0e1402404040f0050705125003003801c1640000d0605051405a1004400004200341940c6d441580001c10b9100c1c000c4440b610940b83c481408107128030046510001d40000d108064030f041101251429a9000e05441280c0198411102442c0c03070503402490b4070140481003007004428120001e41e107164130342c01078584001203208088164982c00c1c00f46400180740500c0d0740c4a41c0c292180d4040322583c405592001c0651000001080502e00e080021020307550119080e0700c40c6d104070991a941c40b600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 255826645 1250 255825395 255825397
    0x50a0b071101090803192109030909110405040203100905090610050f01080a02090d0210050d0f02070c030f1403070308090c040501030b011203050f040b03010501180f0510050d060308 80
    0x40c00740c9604150144044166109501400954030f40c64040d6003044580405010818400d242240501985480d548603032001c001c480c1420560b90100400c0c0b003600e60401820428850304040c0c040c1d8240361007030650505070000c80b000c0f9032013650300580d655148107058030ba171180d80d00040c01c001c0c10f110522840302c0d80000c405006000b14007085c0100f9036500100080d0b4034201c0d071300c3c0780898141030000e440d400440e8064141d400024050604110ba0f83e03002819840c11001150007290780442c03098403802c0288a01408000d400c0800c44c54910103403100030340c50225120003040000c031003a812081103c110504105105d00e041100c0c0c484506240180910030121030100007481000c04101040c5080d0017a0b034100c0b600071b40050000e9003000c444582e01003503818154140101080004103031940030307009100404100004a8131b07541040001130601c4102410250000f00004062100b4040c400b910000c49904980d050340750b442e14a016501d42c01806d0381e01070352620303114000050140c094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 255827895 1250 255826645 255826657
    0x906110a020a03060b030d26040302010b031203010f14030307060b15040f0504050c0a08061203070203060406050105121f1821030e010e1902011107060201020d0b060c0604020f040204050a0b 83
    0x2425a9400c01c9071f0741084030203484030521004030b8804540d40d0700120300031000c210340050003840080b41c40102100400e2030412007284442c1d00140010040041d41d0407214040080d2000074660000d00c1642c100096407030003070b01030181005a94100d00f41c40385d51500b144115101038800120b03140c0d0b66801c1100c3d803929044c410540954100400110a440c81808603400c88445403242c80c440d40b2480180801802c0020b60701800d80b10810210780541d8041252a01c2940304070808211581440240200881e06021514069001408640f41620648548254507e181c1c00c0000c0b5445540910301c0302401c03203403019046950440d2002407201e01030094080002840c1c03824498100320450707880c2207407444800c83d5026003164005100807510a00034503e4030740149804108035501c02d46050030f20314954000d00150b980043c140d801800d5a00860203501411102a800c00c4021400340e52a00d80040009100d1032441031905030f42d0703030b4580c190b501811010704280c55030354440b4041c16040e0701c49 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 255829145 1250 255827895 255827899
    0x3030507052116050c04021201140307030803070e040f0e0d14040b07080d0b061201030b0a0c0e010e0a150f0908070308120c19050a110c010906110a020a03060b 70
    0x1032004242600e500303401c0202da900100312030329085642115254030614500211071030302501458852590341c84c00600002000030300e100390b240d4540b07400c2c014000e810518060080d0403000c000c1010540c00015260f1120060405102481c510350000c0c004000e6a032030100c0152601d00c0e8800c90440005131140440f4007500e03030450000d4a442c01340f110380228480c20075221001c01c00303280003551100140c0f403480305222001c9042980b4a0000c2c805400903400003281d04206401041803181c815203060704201190403c02004180c124001c0100810345517040c107203c45851025981c0e190485a48000c0c0b603039588802705010805030080540440341c1001c40010403210300881d1490009c40c4900459601140c2c8500e00410240c2c80a04420b000b4a81e030440c0d8810301c0030700706c0b880160308400c2c0070020030b0317807255640d0120031005020703c1e11302c1c40000d100380d1010314044c0e42039070090003a8090300e40c28102840381c000105602c0b440c104810400039003000d4142c1d400010041550440358200c482 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 255830395 1250 255829145 255829153
    0x812070f02092e05060414041415150a0206041e12020705011d03061f18020319090b0c0f0c0f0303100b03090a0818030d020f0c03010902010503011806050a0303050705 73
    0x83c1c0d512014801c9441c0602940000c0c1007104222161282d42203528140d4082d10104007a800f900c482505c8032011640d41101c82c0300b010304007015141c07090741c141c0030341c40441c00d160a00240010080d81d501c0024402402600500640780c0f031014642003098606a002c0300b1524181d011140081d126565803048501042e40c41d124148034220202c1c140b0701180f400740050005680d03045045102c20030708045404050038080005c00c5508600329408010425402d001d0307640d0410191030000680090311042d030702490b110034940010031901300389800c0b0445921442d00d598000e00f0a01e0984a0071012050300d1152088140041d0f00210186100d00c030b11001c80046190703114803011581c8407c603a51412500440f80d0b00c00040d42042c00751840540c0b04482c40454071440010a1030401d41c8507a02000d85d02094a01548110420a1821725a81940284221b80036030f80081c200340418040c0c502440f012056080c4154996444500145401080000280e5513800d014265501c20401501c440c02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 255831645 1250 255830395 255830461
    0x5031b04150608040602030601030204050a14090105060708030628060306030b01060201020c030d02130f0602010f0b0a270f05070809011103010f0b0a030608070b040801060905010812070f0209 84
    0x80c0c0340d85004101c411a0315030f041590340b1540c2d810f0083d4002007400c0d0605d5803c4c070010403291140c180282c05000354052140301c000090041003642c0310143c1c445032007502c080102ca00026038502c16250015420395000407403a45031400040000007043c0032042303800070501e002801c1c40e80342d04181c04881c0109180fa00990300d9030341c12801d038815035024404e950300070050203801314129401400c140310048280001c0c5a10f03601c20681ea50041e522180060391500c40c00010408203129810241d4012982081c0091800862101c505406401e0404100f0441420f080745072058000300e80c030721a074030410040c500e088a03018040b0342d01278400502c84d40c41c208216280002800840303058554a03560740710440d10344449010243d201d00841c0c8101a20b540300002d1070001001100c0103032035122a526215810408084c1c212041c0b503106000042c00c0400411030360402058411010f0120740002c0c3e1340c1d41050500312030b140c0d0709180082d0400110340411001d14550b01f040f4903034154020301e26005038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 255832895 1250 255831645 255831671
    0x91504051305061609080105011403011a0a05060a09030b01121203050106020a150212240901030818060705030f03190c021e07170106030c1215020306010905031b04 72
    0x1d407014020103a038000000705040e420441c00112464502e4680304c0c1c105915601c0060a4600a902141c80003440d10202841c0c5d140a0191881c040c150103030596040c0e04000009070751040c42d1142900070a80020701c102c002e4415490b2101658100340800d0055966100000c1c61811400065030b00c4903500d00001100e40c8030b405141e048420613402008202c0083d12000600100c5212030070800f542000f0150f00701d50001c2e4118460611003400541c2c0b9400d100c00600c044a41c00c030214031880d10000140001040710060b5520f0100b141110004180301401041d0a442549800740503444003140c139480d00300044008521800301c4200d02500929025642c806464203007500e00003503048070056550300c048001e02c05201409070004c42c1d4a8607035030103038040341c0e00b492008010b090351030700000e00901540f1240c10004043c07207041c0524211540e01d803194200c15006202c000103400102003010b907807140f52584040d000c0101a11608141c070400d80b00130040c0c4409960259003002c0b6543c06d49 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 255834145 1250 255832895 255832921
    0x816230405030d180509060616050606030c03010c0215060303040b03010b0702010306050d020d03031113030506010509150a090905010b21010606080603100b12150711030a0507030c0204090209150405 87
    0x2c21350499254007500b03080030440e9a0000500c5c1c3c642103281881800440e19000e09108041d9014102501050601750300f0b25090000700303240a1b00981c1008191202143d0003d01c540e03142104081400307190302d405c1d001074250700c640d0b4000800c0907400320011030441111001400182e01c00d803401c00c480e81c8e48000780045d8581ca40c4002e0750080c1e8040c0c03002c011a000b600034901c8600340c0e8408901d091042c0c80524400f0324641c0041d942030b07000c2d40050145040c2011004e411610b103000d10303c030503420310b4005130b8401c4207401000c600c0d54a442c891001c004094000c12121000200074007000c0851400d1020700c0c520401c0315065960800784005001e0740070701c0f03540380181800b6000d00f1100008040f4100608846604540c21403062003280c09075030000e01c01d441480d01501c440322030500702481d0086c803c0e0700124003000c0030b400c00c012100015400c14200d030103141d03250420300900889400000c00030030340707403a0107900154424104500d60503c11083d003643c2104030707010416916040001100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 255835395 1250 255834145 255834167
    0x220501091401030b0604090209090a0203151017030408030d0f1406030c01030e070503190506010f14091f0303050a030c05031b090d0501020a08010501031b0816230405030d 75
    0x1d0408000014000304400104103980080b000d0000304a104450b804a0140d10f030859403019590170140800c02140340030b011400c08010200600c041e13174200403c40303103c00c40d00f42c0b0481031042e28107220240028001d1003030754001e04c4100700356034560310110080c8001e880f440079034448280c50980c090b041d2090840f40103000340c034040d00519030380b032100005500600c0d10040c9a48c480c070031048005902d0782c1c100014185d070b841e01c0304000d80491007403410a242c02e5068003d0b03030891100e5641032000c0629511030b0540031708203c0c2d25a540340c46000b041041a2074140c012014198107440110515800200920785031810f03907000c003c10024a04100d5543c041982c040c50351030b0a00115030705444100c006407107215002440038061060300e641e22400ca0340000903a074082001400100215a0503200d84107101040c490311416000c0d40440003400e120005016209020400c0c8015000700c0c810250340204600342080148060103008208896070403c0c892140f0034810605200c102c1c2c0d10815201c20 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 255836645 1250 255835395 255835421
    0x10b09070f090b0d090b0112020f150702090c120907050a0602010c080130030e09150117041b0803040e06010201020f18131d0f0f03120402060922050109 67
    0x70b86400e0030320340f522039448904403410b06504c40d41040013040c4100031090017071016003e2032a0340f80c07251043c0f000022400c0d400c030340f045001c071184404402c2a0340440e03038010b504480b10320f403a54562424501a0140920b8003a4070b000000803c042d0b0310001644401341c4600312442c0700c0305991908100c1c02c2e0b407600c000400000d2404801080b621421003800e22440b06d880d007088e0480010f4410502e8884480d0360160b001924164000707883e8101914810382218a0742000d944610000001030b01401e03280c5040c461a680c3c0400007014070040e00c20b4068640529000003001c5551000c1d041d50f039801c140034141c4070714450302c080741c500c0d801442180d00c0b811101800508082c1002e2040951040350b081c0c00750032101400b80040e010301c00d44680115121440c0482d4541e0340349001c0985401412101d208203a409510754410911000054a0b15502019040c60300c0740c2e04c41c0f0100d4280c0c05031042440c4c119415443c262003008500a8500b82404150300400c0f941c0c1e40c4100400554428a241c05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 255837895 1250 255836645 255836657
    0xc02160f0308030a09210f0f050a0e031005070e031603120c061e1a011809020a11010e010507230403080306030a050a050303060a060903120516050f010b09070f 70
    0x110954065540003641090002e020f0505403282e030003945034030503d11404455184040750064204010b10005d00b0380d49041075128108c0503000d0907920500d81c26405102001210244d80c0d40c082007030001c84400102d06000c2c42c244860041c0101d034410380e040b0f200f405030903590440c0d0f0103254219030031240c010f001c2a128121a00040d02d4881902c4010781380141c0b5003505510f02200351882802600211400050301d8001d2643d00340340e0746000c4001410062a09000442c0d030b61880250310a45074403900c0160349400c181016640843c000b0080000380d420051340c2c0542000650106101d00c0d04c0d07844510b103518920140e404448545046a10310a006000070b10110320200b014650009010f03045508001c6207844080c030708207000004990f258000400c00140e428000c103444001c05890402c2e60030705041daa9850120144218098200070002c540310304500c0d0180b13001501c00b900481900e06031801c80040a029000d144d034454050809840400c0b100c07481603c00000034040f42d0780d0b013 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 255839145 1250 255837895 255837899
    0x2031b030c040306150e10150201050925030506010f0f1d040602030414030316031a0d1b030816021503060303161b0b09030715080f060d080406030c02160f 68
    0x8002c141400441d82e850090005c003148400000395800c0c01220800d8034410b01a00e060444400340c421001c10a003164185401e100201030f000402c1041604c840300301180d40c03c5041ca40e44014010b81e8000b0f88184500000092500003413180c090985a450345031010740c40d118220b0251448840b43c2030941101c1500020b8003044056001d550445d01c02c9003022402c80200803900c0c6590001da9a11604690414501e40b0650f00f620440e041404229006588000e2a0002610b00c1407800000b07031081040320605680d448080d20000007540e44198169120640030481a1030101c000004900840c401c880d4041141c20000907244900310041c000d5280000800188803949690360040f80c841d000718400c07180d082070340140c20b0040d1440d400701c1d6840d5000c880415190940a44c0003100600c500302c14034194a600600550780300c00b05509003403003038a4a0002c0b03101002101402390030140f002c280880c00c00e0703054011000d002400d900711210440fa01240b160f12800d0b40c071402cee0580010b0082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 255840395 1250 255839145 255839153
    0x7030602030c0403081c0501060f05091e0319030f05042106090203060703020d180b0106230a0804030e090105031b132c0a0314091f020102031b030c0403 67
    0x860b4060a04000c05007071994075600d4107600d030000c1141d100302c00c03107441700200c400b0718a01c0394032300402c0340303151072020b00c007128801408501c01d46107002d0040400b03403048003076403840c80c03c407a82c144405001c44008107265249581000175205d41200010818618110300b24851b500380e0301075130740c0b80c6001035185050807200c100c2c9880c040300443d034040d00c540907200540d0701480b10510a165a80340580d9070b113840c81824040f955050000c5041210803001c0c5c6002c200d60511050640307003030341440d07826036500140100710b800b550020144522000100041e0b1f540c1d02ca003409001f41d103c1e0b1074000e040e4210781d0030805010000d004482e0076a1000120104500c000400481030604c05800c00c0344146101c4600360035103081c000c810a80d49005103c40302e03941e0441c000b006486e084a03007e4828100c05036002013103180303480740035245a00086200030740f82ea540304994034036240f12400d400384220001406030103900202e85440103041e81c00024076040000d0002c69200d13150690207685407506580d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 255841645 1250 255840395 255840397
    0x21c020726060411040f05011202010e030715020d030507210203070c1a0103030807110705190909110f0d05030d05071b080304050c101728090c05010c020307030602 72
    0x154640000c040c1c03500880040300038040640143c1c02001108400c0354520103100598600e4501d80c1c0240c1c0c94440100004c0001010700d6144079130903e0a001441d02d15000a03103860b0054006400008007281409400390300041c400c0d00511844c2c03401c0c0683d83d550802940c0308021426002c800f21010140d28401d9104c0358001c40d4001054205280040d40076150b9129181001c60f450900c890140300620074035400109840e400841c9107803142c0c0441001c1d0ba40c0b80c5514941c419070b400b40d000c0d601d0103421039110454140c041c1001584c1080000d09509105c0502c80c480c0b8000b60044007038a46490190428811503c2c0c05034101c00210316103001121804010300000740700c5001c000c1d42c008544454002c1a2120860a0290b00020303103d0519007810790030180703c07803078039032242c00250081c86800b41c11980703204410075100007520a944c1c40d02c101e43c8022064031801e481540f240e031407504482055505c2a9100e0b401040041440d0fa100c40c0190b42c080244030001c5e40c10b9200700b030100002000d0790 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 255842895 1250 255841645 255841679
    0x11b020d0c08031b0105060a0b1b03070f080d0c050310031b0312051806040e131703090d14070305040e0a020d0903050904050f10140102010212040c06021c0207 70
    0x4400c1d80042d40c0b500c0c16801c0d5040362004c02c1c0c080c444503401e4918610309000d0743d900590204c500310042450048410264404d1607003c0c0c24080600c00003441414090003aa07442c02e401c84c10540203101c5a03d0140d01541c0407000140301030303290054109226101d401641c1c070400c8178100d10f00d43c1500f1900c684443d1004421031580451000202200260408104205000d8640c0f5000d481c1d00d0b031045142843c2700b403507038540d001e200d05200070401c4102c94000c00781c00105c00346218215003c242844e12a001c0c42c4580c81680c1500082482103c2a0010340c41d0b0909056582e40c00700c02c004211343e45a144100e440c0500081c105000c244111001140d41d5601701150b003c00500d40042140c220068031040d01050300402c801103480c030aa803c16004d0390b68003410f80508442a0315100b4003050160308a0300506904900e0360b011806640d0003541150315850340880904042d01e0305203404900c4030714500070a0010300a00142144000c801c081902c12040c044e00601036403800d103441070704141c05034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 255844145 1250 255842895 255842903
    0xe15030c1e0d050304031e11040906090f0c05030d08091509070e0106080f091f180807050106051503010e0f1b160c05030705150309030c030313060b011b020d 69
    0x1548541e5503540e1500d0100300d03040e1044000e140c40c0c0b8550700b07210f0f94030211500c50048541c806000c0c200054050150400b4040c0206c4002402c6030f10350401c0c030002d03c0d80c00d000802d070103141c2c81038a00340407591300041c1c01c4410440132035114800c8010202c41d1440c044c3e1394a04a58060042d42c07160801c02d010f0680c1c00b50341c9104807114a5a603c401051703000003a8070240104d0f003140203105100c152107140c241e00c0030a00d030003080418402d40b48031004c14031403908040d1036035442c1c00c03003010031420580b8840c4403074101a40b0391f00e80c10b6601748140240245d110b40c9110b080425802080d8503186c8064034100d07071110300a000550b440030003200564000900c03007426a01e283c600076000203150300160824000000004440d0200c51400c2000c14469811841c46940300d084104456034a030000801d2101c480889580c4a484501440d89140503a000400d41ca000c0442004540d5036106000400a070084806000030b03d140f0006648840c8410720000300c036180c10b1403031009400c080d41600800c41c41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 255845395 1250 255844145 255844189
    0x120a051b0c0310050103030207060807080a0b0f120606130b0d14120403050604050709060803090f030a050a050312060411070201030e100c090e0a060b1b100203010902040e15030c 78
    0x30410019090520044000003c15640d800502c21300d83c0c1000040c2c040c19481c01c00506504000300d018051910003040500401d444001d102d080303485030349540345407000c050715812126401900441e1120b800310f4586004000c01c43c0e6090105103240a02000c40350301404c02001070740305c1e441d4101507a0003803940c0390305407190001c2004c98401480040000714005d5000c0e2400c1d08040c540142030010603444241d20a040000920a411010040329403d1004030f5115a101003134601003428501d12640250007801049081000d016001c0018809080403240740c40c01503640504000c1140c0c101c0b0904036035000c041c4903c03401540258000d109400324801122124400608510305031013012103c000020003e400402c02c24074100c99094100650b12000e11200e410010404818019140e502421442c01001020244401e0100d1043d4640b203030029136503584c407054500701a40c090302c40c090481c4004400070303040c074100ae503a6540304c2c05c0c000e001d4080c4000d44810007040c0821140128502d5403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 255846645 1250 255845395 255845413
    0x7080c03040506030406060512011406040902030a1208010609060504120308190c050406021504111c12021c03051b030a060506040e041a09070308181c0203120a051b 72
    0x2e0743d00701540c4201c0c070401e0045020750808040c040001c0402465400c02e82c1030a8260500103003802a0590054043e20000b66003900350000a242c1000150081c0405043e500380034046544503140f94180c0e035881d01ca6455a0ba541e0700102e030340c0c0c801c2c0c0c0300d8006010444c40e091000207200d4165260003c040c5c0300306401030007456500078119400c145521010450002c0d0401c0b801d6014009032840a803481e807070758054589501c49041041d01500390074481d4940591400d51030303014543c0344001a07000004d41050803500b02001e0f695994889141d030001c1c1c1c5100100c51114403a0041a2065002c40d40300580e0b507482d038100d00d5081c0c102400003000180c90300004181074941304080c00c020800405001154206030919052020f120085120000030b40307801c00c00007080004900702100e91180744680c2e147d40ca0754121203070032541c8074425030081f0041003400c4103151002008041d00d000710142c0310b141c0c02048100c2410721402c2d4a4802085050240340038900c0c01a25890001d06d190058518942e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 255847895 1250 255846645 255846649
    0xa080f1015030b1c020f0f06070804090509060a0e030a0804020301112109060417180d050c040f05070c1509050303070c050c06040e0c030702010603120f030b0303070807080c030405 79
    0x40c03040c0c0d000c40010359076405040e02c0d0f140a5428400b21013505030780003e00801ca801007400d90184c0215603001c1c1031840c81120f50b607110130b4200c60b0081c0d04982d1042e00c0300e0b140c035904000740030240e41e004140d10802c008241069040e06c1240f107400f0b040002507190008039601903030a1440100701380c1c5e02d03542e10441e0b600849100300080c64079491580c0c20018404585603141801e1340050301013981079002000300f100107901c900c407900070181081000d036218921031113081841c2e0303505000c03107070403120900c252401c020b000208004910000c40f01844891480b0b1200300854508682c1c00000071030720b02203c00440c1012401c2c0310007051003100411407080701d40f02c1074959481070300c2c0700c000140200b0040050241c00d11191000e5030341142c1103850903140603541103010380040c101605036040080480d10440c000d620210045a101841089030700c03050002900160340000c400c40841d0034a11000a1854040201c40503181e000600c542884141d032902001034010144260321352108210200d03240e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 255849145 1250 255847895 255847919
    0x310060807180609051309080405090a0b03192a05130e01061e080706050409020c010b0d0302010c021011071b0e0907170d170a0f150f05060a080f10 65
    0x10b4001134440110051900040c41806160801035602807032400c1714040000b682c29003141d04403402220310801d941c403140311036801403c10041c0c0d154540300d0036408240101198002c8118a4040c240221002e08082d10310603c070449000400c89400c1c4040080c051480c00003030940d4203036661400060a04008101c40d404c6a565420842c0095a29500314000a0f0081c4d000c5015112200181804a191a201822a01035801800e00c0d580d00424994030110095121b00c80c000c000030000710b00c4a4190034040d000f0306030010420014002d0710800040320300d05018107540c031004850305034035000040e01c1da49070304191451584149204590002429140311a403035008140d02c10103010102e29008803503000c1c0302c50240c282d0454100c41588110b040c0c100c2d005550454103500003035803542d01da200b03040040807284045d01807a40fa00b1241c15000e0311b803000f480c066801d6a41e5007041c903502c42d0b08100c3c8501a0500410020b80d10b00b000a070083c1c107031244d15030401120781003480240d0b1189180410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 255850395 1250 255849145 255849149
    0x1e030c0e090f060307060908031603031413020111030406050d020c1608060a0c030612140f01020703050d0e0105010b0703030b0d080a1101060504050601090b1806070506010609060203031006080718 86
    0x201905140c02d125480c50140241d178000c00481c01c1ca41c51540c500348055480e0b00071510425100308443e004041854026042243c1480d0740b00701c54001807030300922540a10001c1031003603002560000781d03e1025103002045a05403801d5440710303800c105d2440000b9000e076000c00d038098103030300031501118561000300752044098401d1101400c1245040c848a404481301e010050042604215042200303114104211104a40104003010b0030324504803003a260000840c17030703c2c3d40ca40c800940394083c5903000300034180414100c1402c1c050303104200310705400c1c3c580a003e5407120010070055030001030300030f034448022188060f00400041e1820b48510392250005030548004c40c0d50443c031603681032003c3c480c1c01e0292400725400c000c41d00342030300001c1c03c01c01c490250980440000404e450b040c4511031030a211181c0c014500c0381d0f200582c3c0350903900c5200030b204410104d80e00702c8020071001c0c00441624800e4442105124201c0e10b0000304407000207000e4103000511219010202419103603051400c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 255851645 1250 255850395 255850411
    0xd020a080312250e19090606020705040908030613090605011202040b040c0e12100204080d18030f0b15041407170108030d02090a1706161e030c0e09 65
    0x5120b0115a90319115250000d0030402e009111140d0b40c01166000e4100b0705280845107000f601e010b0840d004a40d40e04840074a80d480e819145e0400500e40071160403400c00d82e94541d080d240016660750901050b01c40400004203001c40a000150440c01c04082412203800c8100020800c444562101011a0800e801100302d40c40d039812a141542081d01502020704c20646080002d00383c41e8200928540303d206485204508c0c0700000c40e10420300300710071004585004001c554860396110500d0396811304000f10004600e101e03944500c043d15802c108004c407900000c5d141500f5826544110401c40d00501b8040002008030140809403605d11481c0440200d105161a403410710010113403501210f0b210111541107034030f0040c4071550001c030a40d04034207188030025813604a044001007442c0780031b40041481c6d0180f007807081e0b551000010498003490100543d03461140510340110350500c50030080c00c0040d607190294a000381d1081c1e1000c0341e04561407414581c003e00800000d0300d00d400544040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 255852895 1250 255851645 255851647
    0xb0a0603030801050303090906040507091a07060e0d090329040f050f030903120c0f0307050d03050606070201200c060c010504020f010f080403031817031803091503060d020a0803 78
    0x1204050b04619142d000d010114011410407945a001031403140d8000c00c003500658407440071402d45801201004003410342c01c4104d690049000e9142c541c20b4100c21741c241d03015420422a03a1908002044e409044a1990f40b203610131401d54130381810404409804008001400303c0001c0c05244c800d01142c000e501c2803c0104a4202504020780f81c0190220881182d41007001551416940040e110400203400401a6190304100300507034107250100200c6601070100094000c10007a002c50360040741c04650700d0400581d01d50105020135030117110341c000e0104004403000e418840c15070803080301c4001200304130790400c405840868883d0300070481c0110b0320713910b80040c442145010301441e00018802e103001d542d00309215038020301e4580040c1001d014107680c0c0ca62048015215000d081d5101e40280260920035a02c05080300a50b0088802110700030140c14400f84203c008800c40d11240001000180c403e410b0401d42407031640054140c1e60321034810700c1c001005803191028040102440c5001e9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 255854145 1250 255852895 255852899
    0xa2a06050d0e0111160816050f07090b09190b03160306140f010b07050304051504062d140d0f0b0102060705070b04030e040212091e070f090b0d0b0a06 66
    0x203042039074440888980c41d40d04050007144d50400c81400d071050700880780200d07078005010381040c1c01c8500c11389403514070081110112100344040024240c0f944034854080f0752030599914940421900844000c030b41c00031314600450500e003010b29028a80318000e2100280d03102d44e80340041c0c40c1505070300d10721140c60f10400c3d04006201e00340c40b03a44004000c3d550020031618181489140c4200705002d04401550081070340001c0c0034080060303c3c0640000f81100c08820f20040011101c0d030054810034000030800038500405010b510034030341108402800541340c0284841090f120a6401c504001102d0310521518104907803501407280c2040d0f14100c0003511000b00b40009043c080300a0162081c060100a6000040c4808203095805509841c10011110070400064043d2050710026000d12070300400303101084501040d500802e00903e1031503005501d00c80855504c0b04114419a0001000c1d082c0c00c0028003020b401440301c07401c00501551130100f0595803210341410690703606090942c1e5a4007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 255855395 1250 255854145 255854167
    0xe0a17010c050f09122505040e011e0e0f070905090c01020a0c1512020c10230a05040503090904080901090603021204120e1011010b04020702030a2a0605 67
    0x1814250071080c0741c524508040d40300705034002d00c15400e6050180503003181a20415034240155200c108030b4880d05603004210100100500029000b401d00c544e01d4101c07403255031a014814881105002c0d144042003c08100c0104020304e101c05005030113000f41c030140c42c1102402c0c4200c0029011100c000525418551203d900d0100c1c0c514031075040d540040001400314180400c0c0d042201c9030542610f0300100c7c0b07140101d038a0305c0031010882d03003e800418422818030740460a0024600440410004400c0c005d9400c0c0e8031200707212014002c0708881c00480c40c42c1000da00000e601500038400c59141090355408205082411241030b561400c0c007099818081d0382c041e006d00020821880d0941c20140090500345416001410003881940d004020702e000d18080c0c01c90040e0614014082c3c19900d0340600701411541e0000071030f2880d9468507587c0c40f001d00d0b03d4802d0f242515000741c000c007401d001a64030f0000300c480008403034900d90750440320207140603980960a400fa007030f40d41c1d030507403030f1034100103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 255856645 1250 255855395 255855401
    0x506130915320405010b060406030e0d03020307091205070503060c07030905010203030c0406080921091804050706080a1514120a150f02040b040803071505160f0e0a1701 74
    0xd201c0000e02034050312000d500340b01c00000c90480101c1d91091010351a0b51800f070740103101010070303590803160100740081c5440d0103074882d40180140c00140d035070885800380c0403412444100c5100b00450345124040c82000b620012680455200301d0403145040d4403480000c3c90150215140522005c001401c9000c05600000a000404080c001142142000e02c51048640205c0c010322080082010005601c030b00b080003840c0d40f2600c402c1c000c07a6034a000a10030800c5030312030b5004a003e9081d40205074001560800c80510440c1c001c8042c0c14444e0a001044070044005060300421035125101c2800c41402124804010091001103001032245603007805802e545884940450341c0000f0403541c04a21600155088040c41c103000007001c491900a00c0020f01494012441c041c1000c50003103401480000100220307170192000380c0d010700d080c0c5040410340d07004851807804824601564409540909500c203044911420310800240707617500400e80c203141d982d1012210100c1020100a866801c0c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 255857895 1250 255856645 255856661
    0x3060b0a0e0106020a0206031521070f0f09020a120203011202130506030607111608011d0a0c0303030f0603060203090d0305070e0d0237080c1806040506130915 70
    0x120354041d10342c035001d0b02039200c1070400800b9002e80e000000041450306c100b40c8030011500c008240c480c421519802250310048006a8809907204000b004102c54000c001c000c82240c401181002c070fa2814824007102940000ea0000c00b400211846100340035854000b55003c3c255444a041407600d541c0108414882d03080001c0c2c0b4000d103400e05100071a107000c124282d000f286401c1081440700b1041c2c4c9180f502040034442100b1900005d40031071420b0042d0030504110208400010384907070312061080d200d200e00c0301e00a0040400e07800c01c0001a0103500300100c2c2c1c05803614001211070352600d542c3c06984c411074a200c49500070104180c0c5654040c420f031178110149144c1410700c4002074011841e0f00302c1c201400307442181c80b2301218203900384c941081041e080e0889404440099468901100c1c1241800303100018002c2c164031a8407810840c0310658100a1007031411000c2c1c0360141400000d00d0051308a0780c02030080211010346030010700400011034421105c10345211010034000048841d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 255859145 1250 255857895 255857909
    0x1e013317070c0f02040c0203090d05010b100e060a1103040f030807200a0306020d1b08011514030c090103091b05090a0b010504030b190903110105070908030f0702010c050703060b0a 79
    0xa00b82c000c116551001c801c3c15905907000202205000b4041e40341d40200501940c2c04801c01510070104041900080d402c15429100b800e02248210b5003940c402c1140f07460603410003c18418151120b204e56000c00c120010310f0152464240ca074000344040c1744854000380c0e00c00c5000640701d82040580c400c205181240c0040440703022014400060310403c66110240240e9000315803440800c80540c0300501038090000c0c0305030000054040580005400d00c20011461010445400c609000710f810180c17103448032040351702d550391f42080300d495600050300c402e04066864440030005017804003201004200039468003120707031418041060010000301004080740c101401c002e00790760010140d0302981d62001407032820750b5031134044404556104051034442424045202c041c15000511042040d281500a000381d94030044280c0300c01c40d0ba4841c80381076605c100800d804040d0f00ca03000e81131881c81403500c140300c81d8440e12a14070b000710a800a0f5541641c4090121041c0342000c0e1150040c464 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 255860395 1250 255859145 255859157
    0x7080a0605030709020c010b0603010807080607031506030c0e030a0605010f120f030c1b030b0103060c0c020f010807090f090c0e0d053003070210051e01331707 70
    0x140760200f52103a0184c4a10200c040d00400e51600410f4203412048410802130141500c9603550203aa070350307030b45451241c0b6040c0d000700300105070174034800e00842220036a1440390300030305840c2c04030440080291480364000c01092a4600c1815030f01031252405050003030502103200e504000359400700ea240c41e8080d4030b454030b03030b140720720006056141d91382102501420001e08240d03032403c14180d45d4110440080800c4a101004410000408100c50603a030190900700715120144000343d401c8020540083e501a8000c4041e420795071007039000b1036001c84a031501820003551400240150300da43d0700443c0c0c025449034034905040303a02c00e4dd0400e414100700e60201d50b40b42c854a0751920b0ba00f0341310b00c0e81c18151003940122450031000c400300706045001246180d4074544168001e494048144c0c2c8010010b080c0000704a44481074a160200a00b10b01c1c210030b400c1e40b80000301900a0840f40c0d030030308080940701481d021100c0c0c11990b82c1c420582622441c8038101003020317104001400400c00024400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 255861645 1250 255860395 255860399
    0xc080906150315150a0305160f0b1806190305090d08071202160c0b07020909030901120902030c0a1d0702030a0807030b010315060c05010b10080609070e0d030807080a06 74
    0x14000450b100c0c40d500403045440c80f615920008000c8020012a058201d45c0041c030001c100000000d803207007a4070803044594000d58480c801d6040200c11407040d28400d190138440904540900081e20f0350100f801080c085c03822803142040e00342140e0024180000c0780e80c64082091b0101c080c40039007194029460101e10324640400040c044400c0d95100b0031001354080f459288840102c0c402c00700361900812078007045959081d846000da0f0103098124041c1d14a140400d0030b080000042e00d82c00d0f08141c60342050b43c200855002e0080c801054242e92610482d443c0700541c3e00c0d1411403a0207041d403000800300101103100b014007442c6026240d01d04540c0b0801c2080382e1280e05c1145d80f80c100c2c0c0d90b4a40850180390910040380941100c02e0703501800b220004001405d43d400850740e01030548100001d0060000400c100404c26101d81c005402242c1d0300302c0098100e01d401000b50343d020003c0c0c207151448100d89004540d01d08143d0504401050140d014050541d030070041d01d0390f0002605809000b094 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 255862895 1250 255861645 255861649
    0x3011d070e060907090e090f2b020d021009030909060603061a120403111c0305070207060318020105030c043b04020a0324022106090f0103120c02040c08090615 70
    0x1e545d6200f5605000b81040101c0c144180c24400552007a01c1181111242d9008003034075100807010705c00310314180424107407590595001003104181c498003a0082c010b02e511100034000a4002c481044007000802c820100e8004000c0c03040c00d0181001c1e5070000745440c1400c04100402c001050f0030b0f1071140c41889004404140036a00f9a84950716141000e851054100d01915100300c580f0342d4942045884840c01c0c0c000c2c0d00d80d0100b4440d51403542140c49981d0740c1c0000764101c0301c000c400285a80c00301c071030100255000b0401507400c1444901ca0314941035075403c1000305051f032680700f400440c1c0600141003480a4001d10304529001e140c142e5520b6080550011386018820f120007051090140001020340040560400a2103030042d020b40d075440c80781e002200d0b01d00b141c00b41107a0b54560000410080d0401c0e80c1c0d054842c0c00580b018841030303400d5440f011300c00e0148010150401c0202d00002005894901641c9204801030700c420143c0c1c100b5000d2039040c02c1000b400c503080341c07c8d01c2e06e07404916 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 255864145 1250 255862895 255862907
    0x170a0327030f0309120206040b0606040308031b090a09020403021e130905010605280801140703020915070819030c020c130e0d090828080903011d070e060907 69
    0x60350300d07007040030b1803054220050f4080e100482d000740c44201170361003650450b0f4020079514481d5104269803c5c203503860804000d014010ba00014042d2401030000078142c4da40b4802e40780800a181c3c5c0c41600f82000600040c0c0749000d5500449403580e008107041085041010b603550403010104031011003040c081c004169005190590310070703401c1c3ca82c1e0414040c40407e40c0000003805000c0c1c07072a00e00d41c42e0741000d0700181c03100d41c200f55508841d64030b0000d840c0cac2d41841a14203091504070400b146450301042203020f5049240d005501c02481c0c0000b0100d102501c2c000d108141c46034840760713210000709011001c590400340c442d4051509080c1c82c1c10b441c96021502182000040721400b54034003580b40004001d1403d04203441ea98072500c050304d080b0581013000c140485020b0302c202d60106c0d08160307021013102040740c1c040070441a88403081c0002008480135022031000503000140350050300810081b54660b001c0008030680003500c040c4140000050301c1036101100307549210541c02d102c1001000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 255865395 1250 255864145 255864221
    0x8010b0d1104021c0c030c02060c0a080105010f031e0c030c08010506030a021305031005160e01050412080d06140f0901180c0c0b040803070f02060403021018170a03 72
    0x21031907002038011340030041015052100956036208120015074000302034000c0407944400c1000d4450200010300c11183c4000319110301440740d036500d605910b428010340310500d501503013000f810344851200001f06000d40700385080002007840407a400007035040c081e04548843c1694800c020040006000f00c0c1c88903011650801d9800c2c20040c2d81d43c050070034211000d4401e41040e94540201800b07071f182030011782c20060080240090103841942c420101b030361500020000c034bd01103081440300700114400a40c2c0050414002c4103140d250004e1044130030101d60a5400c006026040301e070003085c4c0ca042c070112405401ca0180c66880f4554109201c241004c220011110300440e01d501c50000ca19115216405074035512410000030342c00e10b4039210605070400c4800b00d00040b52403001982c1f0a200080c010b0043c0d8164002c0c0c00d40d1141d600710b9002816000b1072152214001c030547c0c40c0001d5903560b101c55a551800c07405900c800a207580181aa040c801c410340320f07a2010113038490046041000714013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 255866645 1250 255865395 255865399
    0x140a050c0f010302090310020307140a080103030c060b041d10020a021c11160302030c041a040b0f060705150105030a12081009050408031006080915040503040905010f08010b0d11 78
    0x718070300c0e9440100e02038411603000f5a00b600542c107070348071b030202e06130043e501074213503a12001046005211078445074000c258824000400b0f600040001c40c1c01035441340c11080c01400041481c040e40720204043e00e40000300f010300c404281e05103400194092182e41984902074906514061000030002d64450440c40a10180c006800c00180b205005501064048404030284c4a411004100042048081e032005134000e000c4d10310700c214035142c00d1007804501a071110910b681e24096030140002000e040c1d9400c0e410540162400c070b120380d516005842900d10400042c1400b50340030451070b0034204183c0c410390007540b100a001e00007074940c110030984070380c0b189041c6034030313580300b180780c04030240160701442400b40b5003804d10080c000c2d01c000039482840a4000300c1c0095070340310411104408229150030054200b81c0c4e01520161200c12210f41103801103040342d060944405411048071800c0e848180b103908031a01c10000c4850a005030803c0040484060380c0d40000c9850308048120000b24640c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 255867895 1250 255866645 255866659
    0x90106150516050f06040c08010501030b150a0b0f1809060312030702070902070f021807090b0c1f061a192703060606020c04051b0309100504060603140a050c 69
    0x411248000081168420f411504980141003039090440c0c56103c103a9017907410907011200420b90b400d05014081c100c95002092039156500d06511101c24443c02207519030002010100040c81d0040e80302070082c00b50f051310081d6039110004082c105411204c401d40b402032591004004595801290041e0954860004159281d170380110803400c101590300301041c4580302055200500c5000000e02d01214402d444d21001550100b00d1050880c03000c5940000062154109002d0090a1009898041c84c01d9040b0b411074003981d0400b59141e0b50491920284a40c1c030502001020744000600350f03800b00103001e042c41e004684070710b20481c2130f25640c428144a0800d080510041841e01054040d1200c0d6540540d02900c0345004000b800591041e90010f100b5002101e002d4a014400c3c00d010740741c20f11203454603c00c3c0d95003040268200900c0d140050062001041c40b52509002d0a40300d2840341c08001001411454100c0320750500d81403e10042c1d00c950b20000c00510001040201c2542c111100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 255869145 1250 255867895 255867907
    0xe040b031908070501060308070605010608060907030f020d0f05250503132103090605060a12060504020d08070b040c0603020a1710051509030601080109030c03030f020f030903120901061505 83
    0x8008240304400f401401c079840e018000003400560720161062504c2040c050290340d071707180f0342111181c0c3d05954a175403188240000c12901030080d44041050b00741c6a8015040c451000036000446064640009800c1e40324403c2203200103000c6c00d510607440700010b82c0654103c0c46074008242e07003c02404440c051008903405c006011003000c0301d070380703200e9a130401c25003180e44960300a0203444101c6e4125070050500380840c109180c00c140c0300056840c422050400703030849072204e00142c90f001e4802c0e80c1001c2c44c86034803008292518004c20009004d040500003508282c600360f5403078004c941c0303c80d007014810311400c44c9190b8001492612900d01c031075092030340d844900c00078004e10720b50390082d42d0010049007002d05090b103280c05050b1b20f41d401c07010b42d141c503a81c0d032800b80d083c0c8100c1540100080d10403641038002074040c0c0c2c0101291070118000505140c05455982e0941c1c0c01910030b451280e0021031a10925000c14003119031041d03102c8001e0002a1814542c1c1c01301c4942100364800703002001c624 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 255870395 1250 255869145 255869153
    0xb070605060301060909050a0201020c0906010c062003010b070b1501080414010605060c011508031e030910090b09010c140a0c1704030303050403140711060901050d050106050a0e040b0319 82
    0x401406070a00b03600c10044c1b07400915086a072134140020407800350160780c08100884c900442e0140c0303c1c10041e140c10b02d04111a544910080002001c000007885020384c0c115002642000958003034004403401e1544c5800c54206040307052030081a01d40c0c20041500700725043d90340b10900c903410a41c004503200806050030309250141299401603a008040400d928059000540050880442d80921260b00c90b4503000460740768071072203181181c010708100303e000a5040700002036034401c41500640f80c2800c005000101030302c04094003960504118024409400c0d02031003145020401c904002865660344815461070f4002c10881c10203124024000005002180c1502c5035402c103d444125980c544900c1c0c094000c08099800f0307070000c4c911400720011030620508581079190880d903841c20800c40c9070300b005995072080300700d04c4c104901801094020502802014082e1140c0d46031140c0303a0440c03500092816030071411380d074030550a083c804030745a2800f1401c10700819406000740d803000f2107420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 255871645 1250 255870395 255870401
    0x809031606110903060a020904061a0304080c15010618090207030f0f0509150309010c1107030b061507030e0310061d040201170118050708150d02042c0c0a0b070605060301 75
    0x603513901801840f0403c118118603900400d40750308201c2d03003044030301d8440a000740310f4500d40c0e11032200c3c14810008503010460500c0a412480700e02e5003240e03101e64424800d628010020391010001c1080c044404004000281604000e419000340840c00e11040e510014102d9071131101850a011840b41040c1302d561041046851104015040c0c040003400c401c1402041e03882155078031925403a00c0300900b400340c82070f2000c0a0100340b40b07000b400030313600f143c03100c642d03110000d007001d03501c00000c031442c101c41e0944501600c182030294840a1440142005040c01c1c00d401030b809a40d120f2908a0a00c00031001e110f090399410000281d482460390f0700c3c40143c81d035441c00548060706182110000816001e000d220707da881c000b090040c03000f40c54002042d544140281e4038100d900c2c580f840088030b182010820f48505900050001c2011300a401c0095600c84244401c0412a02040703285420454200107c094211007650b08806141c6004281480341c01042002006540c490b8085002c82d81c00350 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 255872895 1250 255871645 255871657
    0x80a050705130f05090105040606080a0b01050913020903060c1908090c03010e070807060e0a050d02030a02040c0e0a12030e090408220513060305060c070618030f080903160611 77
    0x2002c002d821500c403a4540c3c4000840e1103401d220700e032941c001103200c4c2424014541121042d80720001161070780e01d084405448500d04890400a00b0700c842c52855658400000380300b40a0403006035100b8040e4141070800e0401020040105410003030f500c0501010001d950455007240380c030401030784403c0030b02400d0400404519500d503007425104081c0c100301003024402c6402c840b08584070030384d43d800141c50881d401d501c01540071080500c104401d00b40000090801e600c003c00786c40c840401d07540020301300c0e0b0045210100203a07040801d62200d0500d40014005040707080d20304d002080a070b43d00100800024a143e6004810440100342004000d009544134900c401e00c980c090348007079599840110015104640c414050524254100850351003a10183c0c0d8001c8040e200640d034401c0d945100d54040c07807045907490b5450030081c0d0451850f0b014440324502c256900381c40d18500d01e00041003000c01400d0201c071900200b0079444031702d40b000303810380301168404d034080b4091028241d0b104142c0584 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 255874145 1250 255872895 255872917
    0x20a17040b01060f030e0a02060d020912010b040606021b0d0510090308060f1906080c070c08150606311706061c0305030c0f070c03030c150c080a050705 67
    0x1040500c0304028514030305074103842882e0390340c50040d402c0e00b200f00c041e02c081543c0c0109a801203500d803005800c040380182449800564003519080c49100890002012080c240003265569050300d03400b032816000700002049144010105d030b5051424003100d05094a424078031540403100e0301410003d0500484c60501c1c05400704005132491400d01800f400740c1180c220344140c082c016560702c90f1a1000710209614203801c80d040c0100c0c144603042d074162201034600700640c2c000340480350018200040d0000580301c43c0d005058800300001840581c210007404051184105103c0c3c000569150901d4140d042c01341d28400c01c03c4000c0c42501d0001031000d822004042a02c50100180d50744006031150240c41d003a946008101580045010200004000200066401c10104444c480940e000c1c1c003140d06117840c0c0501c2c1262540d5641a51035107070b80110081880400302105000074140036074a907030f00c61402401181250000240b94840003440d02100940c2d92001c240741d03130f201e03005a071141102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 255875395 1250 255874145 255874187
    0x201090b0408040302091b19120603062004030f030320030106020f06090706020327030114180703080d2a09030215040b03190905030d06031a0402010210020a 69
    0x70b081203a0680d200b0301099006400d4003000c1010551680b402c55130031110081140d05002d00c008030f501003036600708040803c04c10383c0360060400504602c110001148500e0001600108060b00f080140f06500e2030b220742c0ca101844200301094030307003480d042810750501c0c2c000340000d150707520000c40e94a11030b040c2c107103c1000300020a6550b000142c12a00e0b500b201c080b0b49250b80c80d82e54480d992a15070141d840103800501071005520002c00c0411540001d094040c000025080b02180c01c40701c030640c101b00724403890400c0c081c02486540e52209a404424007a000f42811030f202d04d4481c1c8038003070211300d8140e9140e082c4c0019010b42c2d14144403c410042d50040501201c402c000e01d40807807400264840c0b02d04110794030136500c08408a5088900071181c4504550701d420000a600c40e10481d02707017085444e8945100003e200340010101101c49000004485040d82408880040742c15a8039520816080600000d42e03000900c40c3c1e40d906690320090790b24941800304a03031414202025984200e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 255876645 1250 255875395 255875401
    0x7120f0611030a0f0c12150305160e0a091e02060c060103050309131a0111030c010c0203030714030702120c160b0705010b1909020a03060e101701090b160201090b 71
    0x11070000303601400c100e039402e2000e19840100a0704807030f8404014008604084100224100036401a034240140402d11840e841e60b69100c9a080c000e00300d401103800ca500c0101406018001241180c1118085070108070840169a030402c541c168100360320b040140c0a0307852801c6503504000c80d8070300b6001d0401c0d60741c0c550303413490320303560725088103603000e120b03084100d60f18150100920811540e04060385580c40029004401900c140143d540c88080601041082e500c2041d0240100c00c030026055004543ea4500000d00030102040d40203030148035101082441240c2d60300140e001c8011042c0c020895a80c140104d507985030403403940490b160b0b0a0100d40008200c0704c0d15010300142402100240a0328110000304002c031125414001103500e0505c005200c460126805400d0072519400d001034100c4c0c80d05004941040122611281310500407070034040e1034042101c0c101410114402071004050070380d90700e88007580050600040e03242c40d42155903828401d40004403120b400101281e07a40c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 255877895 1250 255876645 255876671
    0x80d08070203041a0906191d0d06050405030c0615010806010903120f053603030c1002071a010b0a1d1003020f070c03030801090509060103080f03090a0b0901020703120e07120f06 78
    0x20440b804908045500d0b23054801c0140342d1500d221041440080c00c1d40a108025a0b0f850700506020b48103450500c400c0c80701d6202c17800204009405103245491080700c0000000c0018000d10008068604119007440100000b9102458035a5844040d04102924805c3e00c0300860321030140c1d6444900d1200b10812a03000c42c1402000c04940c5045820622a201040c0c03003855643e10a5801854182e4020100780420115681c003078418144200084040a841079071424003601c0280c1000c500500001241070009401090150b0400c1c0741c507a81103400d0030300710001181c0780c0d07001c0c1449050603000102c01e10729005210889807080c2d80402180000740d200d040041a01d1000d015a0001ea0728050100d46114800503100b8107c9038010101454614500400022508083d0010340144110114100050814074400b88503030644400180c640c0243c3c00c2c000c1160740458030102d0054a4080b6840e4030010102e42c2c0c00c1503d162885203405030020f8517140b03445c0380408102a000c0362820b801d2501d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 255879145 1250 255877895 255877927
    0x405010f08010b03210a03060306050f09010b1e0d06090c0b04170c03060a09050f0d050a0905180a05090709050406020901030b04021c0507050d020c07080d08070203041a0906 76
    0x3840c070010003080800881c0b82410f0f030f54200c200260300a401c80c0f4401c3d44d5080c52600c014401006149004510036a8a9032242e058802c08d0350500c81100106013000000c00d4248a034008000040b900a0355400303200c6e8501800c1c0c00718480041c0103004800307040e4240055504018a0300741d000007001c0110355181e207680341c942c00030302400195250b00f0304001040ca20000e0000b181d0b84000340604030544412070710a0051003a000d0889540c0034801462011440078401d0014172000380d1112592400f030007100420300b202e941c1090780700300303102c4411303140003107000c20601d52180f056a80040c3c0d40d00e070065981d180880c1603002c01809800c180402040020300e4001c0d00303101a081e01c042c42061300351002c100580c00784080c80c00400110340000c40030410f854100c99040341d46810400d2500f0541800c42c07059910190301000396038850001008102010425401e01ca80b03a49410144c0d418107a50003500c07440b8901c0b9000718502040c40940900c81c02504076000b401c00141001d5032480358540c0200c00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 255880395 1250 255879145 255879149
    0x506060114030115030203061c0507050111030703050702040506010c0507081f06150f0306050303041424070b040219170115080d080a09022701060215060f0f0405010f 73
    0x505207140c11040000c408142c80c181c0d00c0984004000c0300c00c0300b004400035000103000030303403200c00030b807c80d0090100c0300035015042e80214040c10320700b403d14002500300804200d45040c154800c100b49004268414145c907502541201c01081988440c0012196000000c201074003a005080c000904150005103e47c00d140303a07800c11284101d100e903906001c550541c40b502c0340e600000e608004029101c2d50f110000084103050001c0c0072034454002c2840c40d00300b900302103055100026080c07428900a140c0700e0b51600010400301c00310b0f0404081c1d003503d010b401c0e80140024002c0c00800c00b19580c14a00003818400f40c0d00c0b001c2d04560301c24507104c009481c074030b8091031075207406503548605000500318400e60714400001e003070314004036000303c0d1140d00c010824002140e032100d00301e0040c0e8030a014100010200860f40c80a40b00400c90704400583c1a0f02580565015032550500a66111002d941c00101160400880007418001c15000c946143c4240e91041c9480004145801d400d80a901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 255881645 1250 255880395 255880397
    0xf0a1e0e101409010f06050304020111162301051605030d091a0603010905030a2307030905030f1b060d020706050c0c011109060d050702031306020a020906090415020c15010305060601 80
    0x7415a580c006000f40c420003809491003001c2420010b00c515405500115005032040c50001d48401074214228202010480f01c0640c1d5007100c0c604000e10800345041500a154400420100d02145000a0700b60f00c20074107511080c07050054084203005080c400c0d1030895229800c03d21800413580340c0740c039a5661003000140c4110114003c40c5131400d0511980c4e402952200c02140b0700040380c1d50035140003004c001070b6660a140300108248624281001d000c01500c00e40721024103a00700010076040c10b00c41d4101003001e44c040e1039100352130825030540703803415007080d14100da513460000800b002a116040018000b9410b04040c041e0260154000f0041521600b0081003401d8550380c1070300c0c5610842c0c458503070151061101145111290303100a405c1492401141c0c1341c240d09481c039455000c401c0e8060409a0001d01c01c610941c14040da049078402c0e01105c1c1c10004e80742540d1a4034091440c030301159441035011500c0001044100056098822507580c2440e8943c1d403032901d20b03903410301194024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 255882895 1250 255881645 255881669
    0x20a0209090f4c141005041d06280605030303040b15091009110406020d0309051006181b17040c05121b0f0a1e0e10 51
    0x1aa20100120341206411401ca02801d540303030110700c003039003500022250b1110100030b801402d0814035500b034200000003105446031082c8086000c02c5003c80303242e4085160000c4c0c4c013808220f000000c0030464401c0e00c004440c0015200444660002c0000c450b040d02c0e11140b140200b48801c000101c200380d4103203440000a82d060032040c2030604103a030801c1c4aa26010307442400401e0000700c0001c921944405581d02e1102c0d00e80314800082c002200a66404164551151092014480070b0081820401000030103602c0c00340340c00c000035039402c44002013008040d650420102086000d010340c462100081070140b140c2920740041e64184101c1c4c0102406042c60800402d1014001d510003d1001c0c503d500c401c50640c4c9481040c00200000520071550070107014400700b4103a40303100345081291a480e00410029030707621080032440c2c101414281c460500c074101d142d401e0b5228070304401a1007620300309203d2410081c483c040342d0350b029005000503039132240030000d40c8401500302a0898407012140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 255884145 1250 255882895 255882901
    0x9090203010e0d021b0609150d1a0d030809151f050414160c0b15121c030b01020109081803060a060e01061b05070e06030d0212040510090b0a020a0209 66
    0xd07a1181e03c200da400140e04401c4500c1003c0341001100c2c208002d014044518110b042c100050b1031604030a140d502d03202d0045540241804036114080078a214420004254802040040d21201212078000d040118080018289000c1401038180b060104852800315042090707072003034960304034040c2e0000d00885140028040c41e0502a0084511100201240b1629013032059035412210303040c1c0b00d00303100345aa01c500015a4058a283c441c100030744501600582c15400c0120519480342d209095510041000603649042d0242400200c1c50b801d00140310b031041e400607405804504400792000c01c0c0032500f918081800039014080240c00c4050b181c4030380d1014101c0d000c40c2c905004040700161800014004c003402403c507040340300000056100290703483d598182c60200f281d003002110700b074a5810b01203503040030403011071139000600150003119645802460329001c0c0f840f829110310b00c400600d4107103500a80f0a00060304881d0800c03541d441d0301d9200650307240ca16503404c03401400360383c1c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 255885395 1250 255884145 255884171
    0x30c032d2715040305070218041a01050108090d0e010306031e030306060c03020d080402060909041109090a02030316080405120c010912020d030c210306050f06040302010804170708040909020301 85
    0x8020220000300d03000c50800e85440d00c080f031740d03a0088401203800c0240d0140d00c112034261841401c1c4240d1003a612030100350f5aa901c0c0880540d0181c1c003d030305214100080c042c50950119a503020940d60345090081c400350307100100c001d45002e44c000307029416501400401e5451402040030214081e40b024840a9a80c2e0b00480b02d9400111010300103030403003525174511610541400b90000c1c0000c100a080c6070303612001800001048d501240d030100002038514181c01d101c1b0f0050350080c01080a889284504c2e00869200d208407541503d070400044d12032810070014005031006020b014002011308010a80a56541c0b0303003e8203100d02065000c94006001c581c000d9407400003030f60141003c0066009950b0a031031581c0700320011200c00c2c04a464005042c1c030107440701241510595008500c10f0310300382c14000b4110103012082e00400c401c1000303001607600800c1040c3c005510264809502191501503402d0f805140402804e1075400031300014284043c0d00701040c0340b030089008100c8a200501 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 255886645 1250 255885395 255885403
    0x20306040f1e03110d170f04061401170706080c040902070c0e0c0c120306150a020109170405040f0203310510060e1008120706020d0c0309140102030c032d27 69
    0x3080d0700241c1c6d0f1310000503094030030700c0704c044d074001d84120404a0540c40c8c0440101102000340c1000000c1d9081c400060801401003151000502d61424031441c1810f2031124802c25103d0f034003406090300c1e00080c104d0100020124481c00030310303008540308064100a0807010150b8046280800144661108142842c140e041107034042c05c2c0c02090680802c11008480c00b064000c18400e40c1903540c0c440446010610b04015280c250350b00d210300c5a41c40d0304080800040f503410f4070220640c1071041c0100f007200402c010350224001441c0b403682080030004c1e40c0a0503007886804006104d0701030024120b079030304d4098101c07205941450030035148035501c1e04030b40320840429110b5440c40c0e500c402c1d0b12021103048400101111401845d0146c80d00c40714500700400d0307030340701b80c038400000350f442d05140b06001d0281c8045110b403207100002e41c0307541040020074000d070101524140141004048001200c00d841018080c007040307a4280c84401c0c9018400794032244207115414950887d05400e00c00f102d24082 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 255887895 1250 255886645 255886667
    0x803100b19030c020a050a0503030106090b1606020702030307063908180309040e060703061d0610112a0d200303120114041503020306040f1e03110d 65
    0xc0e614802915480320031070190078080038110944c040c0556040101b035040c008001348500443c001d50f40d80d4580100100b51145951003203406900511001040450008840c10116081032000d0389904c0e1030300020b8114407803110010100f920b401440007008181d5604625980d52800040501040070701288812107000700c1b00300700103010032000071070700c0c3c5402082200361200c2104903820151220003040840352103c480380403d6110604200f407007a454000c503006450141d410142d00010306015000414015150b1440744551996402030940300e40f0180403120582400c0341d04840b21000c14151400742514003440c000040582d05040781004011441002e5004203620208002c0301c0d4078800640c91712840540c10302040025408010039081a10b020b05138086034900c4812441c0c1c03c00c0101c0f01e14480700b84407800c20000410140e5408142141d202d80c0010710350000035154945000100c440718850594510021981c005141c0c0c80028041040380690450755a0308404070240c801038968 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 255889145 1250 255887895 255887917
    0xf031315020313062703020129030312070507020d0f0632061206280c050a0e04110a05121506040b1c05130b10080c010c020d0503070803100b 62
    0x1c2000c40c0c000713592640111025400c1d0720440c2c45203000310100005115003e20180c0060703448100003d504405a03e00e01e108a5514032503101403488003021070b0b200c0c016217418854202942e40011b548601440445149541c010100c05202c129454a070804800054095031518648160300825501286103d000640310711034541c1003040b181c2041b044000c0040545d500a2184418100800020002d0070f00440101c44840c050780420044400c4400141600e1600d09080c10280320070160000b0031103001c1d04c4140390280980e0000c0010a01074040401461036190000440003000e40e400f0016000304400e044038203049071100c0c002c40c0c043c1c920341c030407481d444101013200700b100c0e900c40c1c40104404000c50310448841c030880c41d584400ca03031040741c800600038100c0780c510b41040f805602650307200702241e05400100381040c554556515213120018144409000100299a503411001c9902c40d40101101d80c1c401107031606240a80094440481914006c3d002141049583c0d02b82d4407500b0320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 255890395 1250 255889145 255889171
    0xc06270108220303060512060615030c040e0718030503270310150f060905010e0618010f02071a07020103060b120a0b0d020303190e100503010302040c050f0313150203 73
    0x16000380400042c54010b022401d03d650799800140c1612a2400618503007074031005010f4926109007407001e403c49020403692841d40c1001000280342044069405440d44014210b1481d9100d04041c0c564031041c3d040300f828811812400010020004010b00301d01c0d0702d0307440b542101c40c180c0900c45a00840d2103901c540c1a004a82205220042540f0001c005410418000001a50342060740c907007402a030000c0000600504080c40b02e540c000c0c041d40407031401980c145103848201c00b221205e41401c4d4050301c0c10800c0003042444014800c21045000d00580790340c41c1c810160004003500e0580c040501240403c0c24840006403c45d812400d40300348000041441c00c0300c2d82c920140d0f4000f8021281c40b268008802102000583c40400c05000c0c0200040740100d051300b42c208019103e0004041202c2c41006c8500c54400c0841e40141175a0441c2d074190340204208807107030001d5406025078110319000b041d01004111030800701c0d9882c80c0b08140242d14200d288030a17142c08030240e20044402c912036401c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 255891645 1250 255890395 255890431
    0x602070f03080a05090a0e010303030614060d0504081903140603060103050304060503060105041805040b060307081002090604090504050618010605060f1e0d02041403060402011407050c06270108 85
    0x80d0b00c010411a0035a280061500c82a0310014640e206d00360009003440040c0d80c01032041580501c82c040c041e01c00986070305050220600020981d100c0c00031928981901c51021074100400c40c825161004000d9140b0000d140305140018000c10010f5a44002c284010b0041025810301058030b5050b00d8000c4080d5181c6400c0501c2503800d640080c085904005081000003070b0304800c89503592004030809004901400c081c2044c81111380003038a840e2181d0040301d400c01211500042c0884050a010405a119041c3c0d900061590040d45d02071941c01e400c00c801c01c420400c02140c103a2048108201d200c182480329080c0794221805d601400c1c0d005003080124414019115000d0045891451030100242d4043c0f00300e254160040c1d424115203c2e000301d001e01441f01c44806071010381c44164000c0c4018605500000c000501580c4138681d42040010f4a8081c0503041c48480c0c030485c406046aa5116080880c00ca43d1100005800c5156020102c3c0c020303e540c0700c1c0041e10300405050101948140e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 255892895 1250 255891645 255891653
    0x618131401120206160804081006080d090609060c02061c0c1202070b0c0c030c01060f0f061106040f020d08040617060d0b06040509010b0405010315051b040b070c08030304060609060602070f03 84
    0x17241c81c2000da40c0842d01780702c00184000c081188080c0d0715115078000c500180341c59a4207141070654540c0301d0030304c5000c02c8184010f55200d81d0b210102d400c0307854400340e400c01c20b002080302889006085030b00780d4030100100300440c1050308107080510156540042c000c003440c1c000801c80c000c20744010540d00e031400202e101242c1500203007101c15281000e591070031324a183c400742103580c142e10030341090900100c100000c2c50300150b00781c0181a070313003459401c20404401e02519050f00810042c00004400449015920b403052203036141a8010303e2280c2d902c0e10b035080545000d080210744448080c418000590a083c00d0b03000c540703010342c0f042c21405592660707410000074200040c6082a070750358032903a488195481d40905802103004500c43c0c0303160054a00b880d001d50305c0050220032090350701059205456804402c840c1103512546450f030f100c02d01c0d440c04882450700c1d81e1044590748004030511082c004258040030441b1060034080041d80d45d201016a100e00d401d10070708443c0080d48030200f002c0303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 255894145 1250 255892895 255892927
    0x8150f040f05040c0521122206030501090609060e040f14010c080402041d030f0a0e040903030e0f0d0f05130506040308040815060f0618131401120206 66
    0x184006001190744951440740c07504031141240c05441010000c0070402141c10165003110103840c0001c80f10b900701c4014a0115501c01103542402e00000d400180051442904c1182ca448803201d55148122140c4c2d80b1401000b904007030103092115881c240c00014801603034842c0320b04440d9480702d0300c8500d540f26103644503000303a050001c0d0b0300c039000d401e0f078040c54507405e20a103071030741c450354507542d0f00d500741030040c1f0089aa40c031041c9050a6114038182580c0c100002c242c1c1d500c41540840c3c40e6981040c003004490988000c0061504107041540321400c054046e007116922801c40c1080740e40d81c031017960120b42e48001d40b0310b01a01150704001e407080228402d8004092500d440300d907444007590341d000403400c01d41c030aa00070f80b0a0130f404207050001035428032000440013400000440e01d800c2100000300340c10045840c1c04c4c4100000601c00380c1d94244616452042d280c01051008070380140d5102788007030a0000d010311501c244010002c144003038402500000d0030b4010b0445403d00d1f040b0f200000341 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 255895395 1250 255894145 255894169
    0x5071d1c0f0c05040507050c01140108070b0a110106090f2d0b0a050604090509060a06030507060f1e091e1206020918040503090a1409041104390815 65
    0x2c1d0400825192210300406000348010782c0c40c3c65540b4070381230045003143d1140e003901e00d061004400400000c000020900700360780c0c150352402c0c1d8902c0098800e0340c1440020704c1016079075003003041c0010308a510358808004511040c03014440a051010b512596100d1120780c3c9114818981414100c0c161079444040000006001840ca1030b44403800143d080d0810751007905103079256810080a0001400110b410079a000070900c1980e05680d261034543e0158000c0c00304019001078a0307076030b036841099811042d45411120003140c544582d00107041c2c550034050703003020643c4552800402840e0082000c111744401c40103101036541541c418010b075001d41803190340840000101184818002480c41c051441400110f51301e082500600092070304940c483c1c0d8621441e5a005072891300c5050075180c1c840d61160b207884203205403000040080c09050b81c1c22105403c130740100e0040c545201c0030503040c2c040ba00300b00c0410542100c41124401c104859181c009070450781c920380d0b141803400031595 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 255896645 1250 255895395 255895403
    0x1c08090f1c212003010b04050d03050d1d0f1207021306050618090f090a03030e0f0307060617010c05070b070203040e04060c0f050f070f02060d05071d1c0f 68
    0x100c1c200050a031007450b803100d41c5041020b0ba984043d0810300400040d900b4640c5040740c000141558900f50500300039001f94803401d80103400d481e242108040c42030003181d0003001c40c09801c1210320040c1d20400340b18404c1160705c2060348582d080321007041c1d070300040e13070580354120702a26854520283d003400320b6042554440c041c0c2a403516004900c80e079403007010344004a0805c207115180f52080c02042440030010b40040c1651005405208241b035010882085a80d01401c0119809145804117407400321805514941e0740004191b00307041140070380001e005c88103903145c691205031814411508a60039422450041003017000801d002604510b0003591088860041e2800e0a075100741007060300300100c0e01201d50990b21001d032040039810600110940143c1e24000e41061925042c60440d40f0440c04050844040c01d91309804555a000481d600300701007020901c481d050072540504000f540c214000614860a406001141040c1d10410317070910003035900b50310700c5015072108101541d001c2d074195 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 255897895 1250 255896645 255896657
    0x1305120a170315010f0c0605060a03050102040b0c070e01080604170d0c12050f0709050f0a0504090303090b011401090b09040209030706050327031e07051c08090f1c 72
    0x45001500705400300710303190804641d24540b15401c5825502e100b00554140503000b5003500b0450340c4484150000c5503c990005100c0e160701c00042d90001450b800104958000100400d03420311000140012903a413004440440741c03500102c0c043c1402c240101b02c400d60090000401040d009030389a81810446000540317030220400c414404d49001d0007840021805110186c982c100c100c0c8111030b84040700904403e140e04048078014004034070342c492944103044d15030041e100c40c2d0b036188000c0c0007020020003c0102c1c541920700500070b08070b809001d0754030865000c0000790310502c0135a03a00034003105944903c01c80f03050450130882c0d0b42140d1f0090341c01c01c1d8240700a42c0c0c1a101001410040c0549865007a04c03403500c170010088080c6864014114802001d10010300080000290340c1800408401c142e49501c82240c10102802103820142580c46405100e001440030f09880510700d6109a46400c182d03500d100b40705544080d00d0181c508580d00c00d5101d09504883e0003d960004140b070701d050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 255899145 1250 255897895 255897913
    0x3040f030c0c0e01030210020f0a03030b030102090924010c0f06180813030506010b2a0c220b0414040b07020c03241503070618030605010303020a030e06130512 70
    0x640700070b0141d8114001c03d00c0000c0052040d444c2c103034140d0001ca01c0c244001c001312628142c2c0790361948001d030f40003400c0c55112200d800080c1d80a4065070304d13010001d4056155454008100e055040b031002484010000c140b1244246c0c1d441400c86002c00c2da0405108004810359980746001130038900da1810b50b0040c40d04188000440c5000244850000300380005002803c609185040100603403100d08684420444c1c2031442002181c000f002c501503000003500b152070401510708044515041030351000c415901c01607034610304800c6012414000c081048020207240920088545461850300340d04403800000d400140c482c000150b000c21f15106031080c0e054035202107440e041040c05034802c008604600c40800d054980f041a40c00b5a454080b1100803a80340003003615007030703940039941c10061041400c030421412021100d0082d41e0040c020800340d03940303090094580c0344000d4100d000441f14a2826440c0c50040180c85140421401c910361052815080002c031260401040c2258000c012130 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 255900395 1250 255899145 255899153
    0x203161803080c0d020601062a0501020408010603050d0801060c0b0a0b01020c040c030c03050c04050a0314030903030703090518010b0409020c010e0102030901060f0603061d071b290c03040f030c 85
    0x3d0301410800318010105009072000103070030700005030444410407010070700395243c2e4409849090070014112111000780440c0d0f040250292040e03411140f01036082a82c00810820001581e071115001d1780d4618645980307641d81103900a02010001c1e1a598154001c98620600d0345c3c48052842e2050048440043d0007d01050a86440c1207440300403a030f81e80c951480490309030140e65445190302801c24901814a00004d400c804030340000303040301c00011144000d5a004000321207602a008003260741f03c01251600600300b811364003e03680510707640020070419901403540107060b5410058004d08060600414000a4101c203030711543d90364a40c0070300866058280300960040480400108a017401d040c03038845552100e50000c0e0406141803000c01441c050145090141200300c000c0700c1c5280c81d119021205440e600c121845201003070242c82081000b40240c1c00664030007844080f0380d8480c1c0c410341c001001801c541e8501110020000600012643c0608007640c038824140400c500d156515 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 255901645 1250 255900395 255900397
    0x300d090b07030e0d0507020907050a02070810090317060a030204020f0d020d09020a0b0c030901210c0e0108090304080a0f03032307030b040920061b010b0a09020316180308 75
    0x500a03012075503071030005481c2c100034415810313141c0d02800c00516007000e650104041080041030a41004404580709007482d03c00e106410003004000211441444c504007003034002c08d60381604a001c80c40585481480982120340288909002402124034516503024400a0342c8803007104030111108010318000445d041c40540101c10300d2110020302d07100544107100b84030b081d41e04100000102801440c402440000071110302400c28a41088010a5810016021a10000401d000074207007100000c0840e484040400300c40340076a10061a61107a201c469100c2c4101d0040035613039004003501c0408038464440c51180c3c00e21038980003569801002d115000300050310300303030390041a044090100c210391500907a05014400c40d02005441e40c241e5a0340304a008288861444480295608006541c0c080c02d80e401034003c5408440048008040d181c000c0505050b09846507412080104e903681c00c501c02e90388901d00101c81508a00f4002c41d0980b1081c101d03500050171040c017000080b0010700204 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 255902895 1250 255901645 255901651
    0x30a14040b07060e0c030105040c1403070515070516081209031e0703032714010e060d150e0103080901080406020408030f25080f09060c070305030c300d090b 69
    0xc800010a8643ca41d00d45040c45c290007400b80c403d1b8148018040072600d03020312802111034405c0d0401d10300300703182c01182c14032100340e001c10380c407d41d02c405019549603c0401420105c0c41841a40c250380040010401401070382e014403d1140d021180201c20705800d000100240d1030010111404a0701480e000282d1028110005029411180040003056080310000d442d0340e2000c83d8080c0c00c2c41c400e0310180700e001c4da1032181d04241340c02d040008040381d000340c41c10b1210b50030127800c460f603400608003600050034a45c5496019204004000550880382d56400c5050701c0d8000302461509501d2801190f0605c8003a0041d50115400c00000440d0401000205000702848150540340d00e030a52100e40a03075011803406030300246031f14941000402120440e1294204d0220701c81e01d40c0d554102041c21802a0180c49085101c1c4a6010080c010000003400c0c0c651744003421141030301010304802c40d45079103d5088030f1140b80c041e01445c280042d0319028103030410030120001035450103612070408020301a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 255904145 1250 255902895 255902903
    0x80a1d0d020d09060e13091505010b03100503120909100b0408010614010e090103170c030309010e010b0319020f04091a010303020d0201020c120d09080c03090405010f08030a14040b07 80
    0x20342e0411a000d9000500302c001010300c0e0904045025075a00443c502c851000c0329650345d60354401c2c10f8020440000d07480603555101c0101000b0035a142c1c8443d01c0c1950040e0341c08040394a8441c4001801d00d00082c036040b401c08034a000c91b05004843c1c0a100110a001d442c0040340854a400402d19580c0400580b000740322140002c50384901e0b0280400c00982c0d500314041c100702e810055000e19460305424241180d41c0892540405880c01d1086110360154a6a117400d500002050040c40a015005807039080041d01c003c00c414000d0317004060f9079107003460035001c4161214001401620302407600c0c80100301c0151000c280b0152039503c0cc951120000c1c468aa40c980100045c420b00d5030402902d503c0c9440c90000b14540030310924281e56500c854410b403090000000746251643c140c64000c0001c440d4090110b58542c0d00c84450a5100d41050607501e003d20b00d045d00006401241e240320504644224024502d80290881e08803290780d02d100c2e0400071050308110004160070408010083d050113 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 255905395 1250 255904145 255904153
    0x9170309120604020114070201051803010b0a09020405090a020c1005060103090602030406090c08061902030901150308040306050c19120e0f0d080906160516050a080304150c080a1d0d02 81
    0xf61001402d0100c02441c1201511070601c81c04006036004001c0b6030000900c8110940350812401c000b90142034044901c5410001030800003e6482c0103402800c02d50340c048901c0c2905079102050340c8101d02038000640115842055a017030171948951085401141c10300d000b003480301d003a45171542664415902100c880782c1c0c82c1d40000502250088460103044440d01404c001d0070880e20160784902d0340c0314580601035000020480a540075840041d0280d03840790608100c65582c14008655001480144c1380c0e5400c1000140030800301a007241c15164200c1e09010f120301162900721502c5002441c03e0301481d513074400200141e0350811221055250043c01011894030880c00244a11409044070380554845000d00942e000980328806000c040e600e03002c3c1d01e40c58081c40482c0c401c00c01c004003600c580120044c0f01c06000801d4019481240036010408034980000112011581d200b20310b02c1c0020140000b0a2801c0080e400c40c48030304c04424040c88204160300c1202d0704103007110000300050b0b80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 255906645 1250 255905395 255905401
    0x9150c07061a0a06031505190501110d1202070f050a080d0f0b0a05060a12110a0e0105070209040816200f0a030c05010807030612060f1803091703091206 67
    0x107290700078105501103004004410202400100b16090031500540c030525883c2c00400c8002e1012106200092200500010210701c000c4648081441e2a00501e0300060307000d011008a0680007441c20741d01c0d04240c1da909146a14866a48029009140d0483d100605042410b0100d0410841040079900840c038044d603804040300b50034111030b0402004281c480c1030040341a002e42e103500c103902c2200e80c1614119940c01d800802204d40801300c0e40640740091410144030048401d21019100403c0300d86c0301c01000f10701c2030005650b0ba00880c3d0009621050b12400a030001e82a9005008e00c260703595441c0505106694800c0c281c10b002010b804914820550300350290b2a00d1010444811401c3e146000034509585800c0020300542c020b25060240c02404110030610950006c0000d040214840d20180d00c1841e018000e0801003008116170b9040060791840100b0450840c514190302d502da5440075840c2c2911100c2d00030444075116810301040c00109007036200d003048420580e4410300586890b00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 255907895 1250 255906645 255906653
    0xb220614010f0305030405040207080c030315150c10110d1109040b040c0203070b0c04120503090a0608090c27070804120801050112050a0e030a020d110f0309060309150c07 75
    0x40160b000e01044958020104046000801250b083d1b85050300d02694407081800c0c414424425140116000c1c800041000804c00c1d01e50005400c64100b220180706080b086003c10026015680c2c21000c81d80050740c91140141050f07019414660303060f0806820a140302c455282100c1041c1c180c031094032000103803004540f904d0b101700c0040c900d01300c070b080207040003500d0000d44d82c2c040c2c11002003103c810300d000310b0144410042503070000c0c0144124410741040502c0d103140c1b660003880226009036006075002c1102405450028411010f00008103c903680b42c2040020341c0b8101110114888032000341c094036406050301c2288200c0207600c541403141080d1030301c500f6000c0164042410440500c0044c801d07a07070300181c002c662019040020401c0d031903045515000b4800002d0b8001e851000191030b00b81a42c0210790083d4622881e2180070b4002039104005858074000100003e0340d4204021600305841e041e005180c01c50f200c80c04460740146007100c0f06030302840c140c61460340103038089030500c108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 255909145 1250 255907895 255907931
    0x2040602030d110f071e0f03030c0305070e24040e16020d091404020d1b0206070e090f01050907120504110f240c010f0504060b03010c0c030203070b2206 67
    0x2468070b0f0620145480302441008045002c0d885000301486076814504820400101854480940214440c25002e00314039026004203074161043c00401c3c24034000604242c040c03107911800c400c0240c0250074120614440034443c1480c003010041000c0d0030b000100784d030407d03109054460f1080084000400e0401c02c00030f460600091154010005403038070078003a0840cc0c002103c94900142d401517103810817040c0300f8024244000d06000d4000c0320400170041c7c076030b0000b03020380240907603107035504c500040d0410b0003008181120b424927a14007941c01000705050149101c6e40c07165141c500303200000850081401038410030b0702c2c00c2c2c600352520f1000c00c91030320380030400c0304000d0300495550031070a07008241c68030682c0c69503000007074010f00031038024024402900706601c0c1d000c21a008001626043c94180700400b0410b84503400b0b5840d04130703886101ca01a40481c0c8120390590011030808040c2d0b0b0b60002d5141004024280c001840c0150384456070400445202da5880382c440401c41021541b04901b003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 255910395 1250 255909145 255909161
    0x20a060806060d24050603010f06050a0e100c06150e01030b0630011d0604060902030708030a2001020a021905160303030903020f06010f0b0c160803040f0504020a05041e0902040602030d 81
    0xc01c1b94204010800d10b000c2c003510b402160030300d05049850b2020200d00307641160840700c1c500d030400c100c090301100c0d407680084090f4200340b10310410481c05840c0880c0c1e0b860a00b8900582c0b14405081005001041c0050403040d80440010029100400800f440e030035200710b44840b410f02125840401080342c0800e00074000302c403e40c4104521f0220030382203010f070750f0071002c4c1c000b03401c10707030789505070320541d2000d00500c00034103030b010100e9582d000c030380000800040c8100c441507c00301c030110301b0494207603060084404a8400b50700812682003280f03d690700850350f040c0201c909104500740e201c03040a035070011400650080e02c001501040509010b414040158212441ca41000c0c0041c0194060300700b410382502c030000b08260304c515005a130507160400c10520f81050640d102400244404000018426110b5954501c15850360320020b0105900510782c5c0c01c03000c074100740818001c140e100103800d070310041983d00004800d5580d4020404036405600880c0058200040402c62800a030090042d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 255911645 1250 255910395 255910399
    0x1503070314100e07020a0b0112050c0301060b090616020901030b09160608070c080904150f0801090f060506031009050c0414042a0b0a03060f05060304020a060806060d2405 75
    0x7465142c040c21401c2c00801074041c0c20b000040e5800400c48143c400c104020150368070242880213540c41b6501d45240d07815421040f1610b00c540e074011911401c041c0140d000f12003141c80114280403030001000110340101c03508010300040f401103a00503030356188186000354000d0350002c5c500c0c02c205c451641050541c2030a500c280140140400c8980e41c8040510743c00b00040c41c2c4a0203100182c5400b9926100f4444c4e000d900038100b50b404000889506022412140181141b284c03107940c40110509980403c800a4500000796020201280142d0407180d0710081c020250340c8074403801100300003280c00382202628203501ca00490469401c01e071081b218540c00c40d600d645164035182da61842a050250540c507040e4500c044035149007802d08030460040d26600360110380700c100341038009000b410309204011500070140707000079032420850101c90282e90007820b01d00405041400980d0b545074054440c1c1d0b00400304100790818540385101d2106a005500d02e2290158640640c0042001058200b24 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 255912895 1250 255911645 255911681
    0x80a0504030e1504030219050909150a150801230703140a020d060302090c03190e03091216093c050402011202070819050406050d0906060515030703 65
    0x4640c005034801607000b0708843c4240c9070000303590140140e00990348002d401601040089444029a100117010340d0802d880403032103590707080307906551200d1700000703c41c48407905004280c0e004000c0c0c02158000e0901d410b0316028540c2c030b001040c21141120f409486042080134681000d0102c000202c0d00010365190502420321846100100c04001610f80f10386142e0010780d541c0c001700340d41c100350000c580041a10410b4a00582003600590045032103000202020305030301602c1e81188510401508400000c60605d0103540c203020508010115040f501d201d403010709101200c5800c110f4014040140e00400d80c0e503014104804001220144d2204c0840c0280e0a40c1c41380c406903202510304003075000003040d15103560005803824000201c9800441c0c0c000540c007400e010f01d02000345420746803954010034100700080125010b02450203502e00087c1d080000490703c1c2d505401c200703420342c05601c0018000e1380e580b001400c0c480f403808414040c6c0d10b02004020f0525098443c903010011003504038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 255914145 1250 255912895 255912901
    0x70504060803250803090607020d36180f0e010209180c0c150405190206030c1e04090501180e070314010b03010903023a050a14041203080a05 62
    0x220b031a40030719200c1e2509000e50005a003080b04200403001c1d026a001551960f51b820404501c4da115070301140c3c00310243c4110303400490340a20031441c040120340000284801140c15005020019004000c42d001c00500201c010610390440b07810109078044501e40066040e000d2144002070760036080c001c2c811a44180900c03003454668002c4c92a200748840401d0703040355110421504940a060317100300e01403140a51111122601e80c10482c002c600503002c88a40b081002c441d104203115409000750402400c3c0013040501311042c0103010301040307822080c0c2041da03a68459405c0c82c2c1140d40030500c3c0316103a50040082030b901468a900c42c000041092280244107040c0039511915444014248044107180213800c2ca4207501c81112000300900a01903284241002035541080500000031099000012035149036a0080e90b102001981e90240c0d000c1c4e14244295190342101d40300d0b80034400d1a4256902c500540f5000348060803401d42600d491a00b1820010200b400c010301c0703240701610b85000c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 255915395 1250 255914145 255914159
    0xf160513020f0f04030c05040501090e0a080c0106050d050312010509070225180e0d020f0601050d0c0b0c070f0b07020603060d11040e01020304150b1c0512160507050406 74
    0x328100003800d810250740d80c01c6800480c1820300ca141c0380050101c5000c1008010020081103c1044030320480b800d110f02d9880e801c610040740c02c1581810070b00d82c800480040014aa103000d0020143d07201d0001580555802c0803900d884000d207000c407000c3d0070002c0c0c40031800c0d04c542c2039140507190584002690740307015140039603114401130400706184016035481005205c8190743ca406416038001d2041c205030114408405800200720480260041d21030300b0b02e05a2000608002c00440305000f0603960b480c1000f40300c0709a540c2c1000343d13490000c11f8800305501e0f80d514001c0114401d07501c028151945099001c02d442c4895800100c1f0141040100002607540d44043d01e40103039088410481044062808030b84815645000701d400a0618001042070760040d1302440c0300324000e041e43d09401080c1e180c081c5c22204510b0b09641c0c4840c11913404016078070401000349405201e0001c90f00d640c02c002003d9003043d005969000301000c41900402c080010500000004201c03e82d4280041820101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 255916645 1250 255915395 255915409
    0x307210606120201200102090d05010b0102070b090d08070c0515210106050d05090f070b07050c06070507060c060902060d2c030f25062306060a0e130507020f1605 71
    0x900c1240250000640d2003a1001f9411555450300080c0900518185441c2050103085540a0f041c09801040000205058010112043c0c094028941a41c2c2c810741d50b5805115001034900750f9001c849140f01141e070352114a469075200e80100041c980b5001e140c021007004c40c40c1c1c080c404440036029001000030319084070070b541c0301404580c004112507541050041c50070400c0c0e40c19065900c1081000111414240002c000c65401402958070348509a400d11800f071161100c014102d90090300100445c1c3d00c40e07400861064031a01002c1001c8225400141042d04480140c0b02c5640d41c81070013600f42e03440300003800b2040c40304948003803001002c800d42903120301400d0366169440c2400250000d00301d50b4040b6100341d078090460316204038030b0b0b24200f4000401c00d8010b41c8040b9843e088112000c80d103007400c2640b20310f500608042c0351006608040310660034041c0d103280c0045452000c00c0d0700b8011400790a03c1110698014500c201e80350341b115107003c600c5042840340140c8400300780515101c210b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 255917895 1250 255916645 255916667
    0x1e090207020d0f110a0b030a0606050415030c1b06050109050906041a180a080c0705030f0d0f0512090c090604090308130201051216020d05090607060b0307210606120201 74
    0x1043c4128003549050500c0c1d000c1101c00d1490740f20040701c0f004100c40912101a50040c07400301c50030010603031607407020342d414400c80c00703081070b82c41103c114800d01501c0390f040906c142030fa602d0001c0c0000391210060007135840c9038208640701a1100014031000280f4840c040c0d11248020082c0058203240c1c03181d0744200404888101c8154450001641c1001540c004a14800c604030407290ba04c5614100340450750041d40041e00c090281c40000103403494005600214103181001419080301c4600e401d0703900c1071002c00c0301d0084c0300d070a01c000001d4503030701c44885216110700b030090060200d0701c900b0040c002e00300400c043d10441ca0040b0302d1001c00e61046a60303601500d00300c0d103015061201d00050b5203501403600c06601c04076402081204c0c280c050000800782e00302a030202d543ca003048000669403030050100d8140c025030284100408a42a604260301060b401b4040c0c0d00001d846280d4550034088801407000304810f410102810084c403480b40000604c1c3c0c407040c24848881990002744080b00c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 255919145 1250 255917895 255917903
    0x308090904030905120102090a0e010513020d0b120c01120204080c01120e0601032a1a0307030b0301020301061805100e01110c220f0b090604020c0304030b011e090207020d 75
    0xc04143c0140518405450014013203100c0050a040342c5020354040800540241e001c587e0015010700c0012045050b2080149125104c40c202003200000f50010b038011802c0302c0d100d01c2c81c080b407615034408082248000b803024002c0c4000300d80000d89143c01391401503050078410030007040076003c0407a07800103204003460300400c00010700c004403000d042d4659452080340134070300c000006c20420451101c5d00302004100b0b07903083d10134211904598803841c0310341c1d203e04c0711146046101d48001c100030340c0e2190446c14001404048207001c00d0898000741c1248010890400740002141c40f030084540c0280421644403809a880000c010302d004c6400400714117002c40b1088800c81444180030302c0e804040064098001c2d03083d0201c5040003518100d0122011516101c1c41c050a207029020b29152140050030440d42503d40100388002036001514075251400b01b0301c004000591104140390091160700100756050b1096901c0f40c400c07001e25400b21003182d20400028005031a0700d2681c004003600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 255920395 1250 255919145 255919159
    0x70c020a03030c030315211b08030408070e0402030a03030902030f0607050901030e010603081e0c0a050a1202030a02340b0409140405060f040606030b07080f010602010605030c04020c03040f2c01030809 88
    0x8d140980d1428602d0305a00c190149001000c0b4000b10008041d008554040302160380881d44e54111103c10300082c1e4001e501a04041e4054020900a81103000c0b0244040d00701c486e03405201003514140102039a5000000e14009078001440d03034180101103d001c0722400800c01c0e18074559582c1d60a02c40c50b41102d1315918940d003080483c44400d01078503645070710b52050303512619103483c00d1610f4048072003040327450441c44003910900f41c2c4000203482c500035840d0010034458020040179003e2202901408170600155452900b40f0220000e48500410040c0606130321030381050007a5068501752484040c50721030b100100004203000203441c3da00440b81c00c40301041c540b1141408000713091140c102408000b54a02400542644100f1091040e10519241d03032069072900d134101c0c00c3e202c15200302c81d8164400690b079003051601d82c1c0103000510145088a2a09030381e0f003c003568110705035100300302e01456104c50030714a005409a0221010071070f00240300e01d40c1142d4a0303440a0217024a81806021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 255921645 1250 255920395 255920459
    0xa0206180a1506090f0902091314010e06010e01081c0c020f060327030f34030c1a06150a14041205011107021503070c020a03030c030315 60
    0x4007841419201c540100c1d8a201005115070316101611092044031001454a102103100c05054414104100d074002d2840704681c4964000c3d00715460030305010b079540d845103c8000d490785c000b40300c0c03d04040d01030030250803958900040010003000507804081150001e620804040c0c59000c0510000d03030080c101007060b0f8641d0300200f01841034800041c0c3e000000001448403c0807108036100c101301000859005001111003030300e4076805000322801c00300742e0a0220100e00d800c0d482c1c0398004044c02d040848001e01c01c10b56006260000c220307056000c500041081300c1403118400d60401240c0d01c85081a4050a04c0350200e00b080200c0c00b02e0041c80c00b03002c0740c0c601283c0e1103020300d4400c0b000c02c1c10403251190b8840882022207520100c2c102c0351503281c44400040b45402d08180e403542c0d50020840c6900908855505665901c014201400c115180010800582e0b039510400040c50095582c1e0110309040d00e006400c54102000f400c140000c0242c0403c408280d02c1e00d48022500004448100c5403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 255922895 1250 255921645 255921691
    0x6080a050d210911030f0d020d030b040b0d06051f06020a020f0301090b070207061d0603041e050105070e09070c15020a2c0f010804111005090409110f0102030a0206 72
    0x148980c0928031450b810801207605004c2820b0f460b102800c1c0c120191845030182c01a4103035202d850910000141c0c00008901c1c03c814020345c040048682c01400201d12004054001071074003603203400444a0560702c2e028401d6103124400d029041e204000c81294440d820020042c1d560310010728001c0c1b1034500740c81a03008545080d0072501000e580441002ca503410030a00107510f40d03032103000e2580050303540a40c0d1201159001207036454401c01500c0c2070720b551110380f10412031403403090f00c40b01000003101010b0300186092241610458060341e880c42c404040d10104548804041c0501c001c002902403101c0105003400d40c028103885040200503510a1010001e076000c242c0032a511034040c0b858800d0311000c04901200340c01684040301d0801c2619a140d0040d1010b00c2d040d0740103000320720841d0042c10b00307007804845940603904509001e420003410b2000035066a112000c1251071301d14605907a080d500300424081e00b0703c02d00740042c0d07092100c0359030002c2d5030300c074001c00d41e14020b4101718280701a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 255924145 1250 255922895 255922937
    0x40b040b33042102030c27010e01030312052505031803190c030306090f02070605010906060e0108060f1f020d0f090303050d060f0f03020406080a050d 66
    0x80c1001800300c005080c450350280a1101c1030409400301e880140c420410400180d50481d025500410681c080d1145800e500b11601c69096400300c2c1c2520403150002480c0e6180704502c0700b01b15652640d404013000304190300101c064182e10041440391140014000660042d20101c00c0e0820b28000080d1079507813842c040400500e0340c02005c528080032040b0603000d6030080081d8403926075000920a24203074165119521310520328200e07402e404044200711031501c103c88084a4901038034000c181e607a160a07901c0d0403980700600f1302c0e92055002807901d0402c46076000f100e005203c046070412256140103401f603c8a0022500c031410441c6c000e00240303099680c8200d240406002a0420f0b003510300004104207101901800c40340903108802d03882080c06d1050041003070398040c03170f40c40b140004d2a6039800e03600c50300074084090f1065180e060203c3c0c0d28207007a140f50f009081c00341012890501c0d50044c40100e48454000c0d84503500700c0f00071940401d40000340c103007641d011842c0c080000d40f600004c810360 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 255925395 1250 255924145 255924161
    0x40320041b0f170903041a070201020c01050d110301090b180f19060807060201090c08070f06080405100e0102040f05030313050f060c01090f06050f190209010216030c03050618060105040b04 83
    0x2031803c440140001d030280040604140d5841100d1006800c5100c0d11134000d60184550090059101129079426548100c003e00510700510201041c084c0400300034078516002600080055551480152a5443c042a0059119240101480907400c10600400003201b000f003a8208003110740011070310308a010340c4403038010200700c1c0a84411588814000b402390081031415588807908402c042110f20001c5110812180440c1498001900e005030a41e03001e040280150307654000d1402003410b0325954014940c10440310b8000690b268203080c94950608660b400c2a03000364414001c0b022210b148240034401d0313030400c03560520f84501ca03100045c0c03d41305007a40d0010301c5d420042e924080003115031506003e94480c0760180840e0740d801010040850080395807100c42c101450507a4084206980103051821061068841084203400480c100546940c02199011480d400400c00c3c45424400305400400c1e158841c81c0c06403240070201d42e18075060140502c966a24204041d25075a0b80d40a205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 255926645 1250 255925395 255925427
    0x15070807201204080d030b030313051005121f06030b0a030807020406150c020a050d05030703030e070f0f081510031202160b0a02011b02070e0c0f040320041b0f 70
    0x3643e240c0714460350b41c0300d0030005941d4000c6410f26914680520f40801030b00c100c58603001c3c400550526010030042d03551a801e0b003110070721008006008e50380d1411040d062250384002d403502113002050100310390b007180542c01034040615200301c112156850200480032650000115602c80070a4000140100340c40c5d4040c0c0101c1d0141003689502a40110820708034900850b07180c40f80f1070b82d62080c80100007100500402a820030031007040000e009501103c40c0501030720071102c031f00e0b40b621500c41c045061600305800301400c5010410101400300300c200300f110304551a0b041c15051103180d9000110039400010089140c036401c81800354400c0000f5160010900c520110841d0f440c4804002a841880c000c0015401c04c2c034040d0701443d40c503c1c1131a43d02466030061039842c1c5402e00f1290660030160090060103804c1000142400c6c224005d07001a600403040c401c2c0070700f43d0a1080010001038000140543c1c2889200c0004508051b01e50882e23130058100400200d43c2100c08a58101c0d011003022 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 255927895 1250 255926645 255926647
    0xb0406110a200105040201171305060a0b04180f080a03020c060703060501030e0a261b0c030708070b070308070318030504090b040603080702280305150708072012 71
    0xa036066501074898004140b61920416000c0c01c030309a110b090f40e104440280c04620070600000e901442400039550000da4403c2c85a071450050ba281802e204050300c040c3c500c503880c2e100001d038030b2070584520011a070a440141546e10010340d940c0c01c000c514914085d003003450101c0c58410090181c2c048030101422003050302d10754a80110003400a10385400b0781400640340174080c0910304400601c0810a0f038100c044107220101c10081520005c4200c101010002020300140260b030380508038001c0865003050261076030102d00d030285860889164086c410550024500300554090a001c0307079500c0e46c2500d0827401568a252064010b80011400000c42e4540413031040b090552100c0175009840c601501031241441c03100411003a241c0c140006424184100802801494121044411400c2001c1c030001d00716a403201d10607411080f43d0007a00c1d42c0d0400000034200002141e0300e9580700300181890140c80c2801b200050849000c0315442c00005020392481d410038000b00103400c0c04032901e007150307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 255929145 1250 255927895 255927907
    0x8010501030804031415011a091e1206010308070f0311101409030903030f0a0306050909010203040308070507030e0103050912070c14060c0d030506041b050703120e07030b040611 78
    0xb80a0a503c1884142d440300350f0010300382000c900100b08420042c40386c07001c0e80c8240e400c100610005c4180100100e2100ca020064460702d41c9a5040703030507000100c0101e108105000d401032205161a03154482d005030000e10050000a4040d0181c1c2d0520350886002803101141d86001c2c0e8007441c0d0160100c44511800d82208520105600200e424010364115110240c070b0b00c0d1402d0781d680c05100c1840d075240d001880b031400c080303c0250280501d07000360f00d40403d1450760750004c0b40b065041a21080250394001042006054210300c3c0310307410052a00d400c034a801543e4900903c010000303400c0324105034a0b1808074081c01c070100090461080c0c0318a51540d540958a04650380700c09520510080607828099000d2a20b010b205803800c0c400300002400e81c5100c8040100c1c0100f01c001c10440d40b06079510b942c10301001c5403070b107a25280c290f90346840d0755612040c140501030444680354000898104100350204400c04a4494112039219641c1030700c0e92903500d022000391841d8050031031044030101d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 255930395 1250 255929145 255929153
    0x3100614090409060e011b0903020105340303060501051315090803030c0406111203011703040b070803011e03050c061809040c1d070215040f0605280228090801050103 73
    0xc00b05c441c144000800c41501c21316038078145801c5075141d400110714808010409940554000c0007016460954000c15110400a22104180c0b81d001038600e100c80e1940241015014031424028200c02d090541c04c00c3c0c6162560009809540102c209060b03040c05511407040c000d40001015000100c15240c0b20300d0400241c0a494000b4468540040d100e56042090214085071182210305007441880c0b85a0811143c0d410004980200d00100d200c00c120004005541c800a007110174440d00c8030682d80e503d40709681c05040015408504214072402040001890001e1010b260310070668296445001c41e10841d070005210b01c0f8099000802041080304100b0409801c0c3c0c20381c1d80c076031030708914281030000111642400700ca00b4030159110007003100111000c1030081e40d002d4070610748a40d07486481d980b550103481082d070700703020051b080381c4041d50b5179480400007a00800c42c148085051461107203505121211071041403907400c44400300c49000703d00c100c00b0f21019013503860080c8102e507901c0c50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 255931645 1250 255930395 255930401
    0xa020114071110021905030402030f100c0327150207020405040c080d110c01080621011401063b060304140111030403080610031b030501090b060310061409040906 71
    0xb0401603540610203151401c0300d0303644281d45003441c0210300c840a4000b020402e441e5030b0301c00b03001640d1510070120b103000280c000b0040050b40c100c3c400d101050f82c00b413446015040d242c2e014105090002846590f16034280000072132116180c00070703082d01340000b101c1901b60081c8903400000c1d4110741804100802c0c40010741900e07044400316030460702220b898031800c03034150360703800307001c0c03a85400601d0b442590350b2040030507e80002000f4a246240f0844504681c5140d01080d01009141d4440d029595015007601041c1e0060100782804003058452494805110428652a4454654004070300000c0c0b003103a41001313000d0354080c00942c0e5909150038024070150031050440c55940c213001c045031488440c00e0a0340d0103180e0640391040325455450400038481080d003004010981e480d0664401b000c10341c02101c0780e08040d504e0000c0e041d4100014841603500340700d802030244000f0014030041e01807002e4030b1411500c60b4074105142200f4110100c3c1140304916085a001c1c0c00c00c030840040c000654 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 255932895 1250 255931645 255931667
    0x6170a0210121d160506030c030604021204051608070b0d050a09050a0f0c060c080a030207030c020402160308130305030c0d0f02031017010b0f100c0f0f0311030f03010306020a02011407 81
    0x401c48490f9130aa2a203d000401d05000b0b1642000d800d0000c9107000d00c8190146400910080000d03091114004003a40710600448003900c0d503038461900d84000b018800c060700701a1244c0d01c041c0601e2030a12200310803500c1194102c14440c0d40d10f60019246618690008034401da000013504c45126244c10000d80704001002c00b0b8456130303a024030014203c0d0140781c2c00c0031401d61000c41d00d030802d008044190001d40255000b9002d1100c0300082d54010307900e234401061400d40650b08040c58054900307001b0f022100051650907101c0e860010035011075007090640e0350155000c1907040d86e82c00c683c04100c0151032120781c107080c52800030050100040030307070170403806880c808a11541d010615980f080d081e2400080126006142c20070300880e01e040c03182e0011012092803c0c540b6a4040320f41ea81d0007108034115058880e804410002010107a0000c00d01e01c21002c00c500860505030800320034080351106100c000d00f07650380010003c1559000b90050750040000310000e1042d89489480901113260315 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 255934145 1250 255932895 255932951
    0x905060c070e0c07030c0303020708120103050714090f1803040906080601090e0d0c0605060a1e03110306010617040f12120605040903120f0e030a021006170a021012 72
    0x741c00055501c404400c25221003031740540c3c034004ca0564030345040e000ac0d880b0134015503080c0003c00c04607000c8485144c8690080d031244006068051610307a40110100e0f10400d954429810300041c0444403070455451904003480c00d91903003010210074a0185903108a0703100224403410004002041c40c1c01050707903412901d0048080c0940345107a40c2c480e0719446003481600229203000080c4011444641c89994046c40152040303015a850341d451580c68032590b680b080341100310f45424410004d02791180d00400e841034000f444235506202010b0f00107841c09104040d9003d64200203400e200083c00d041c04d4054200c00261000d60b070700c1c017004150031840c000c9881c5450500400084c281032034402d6085035509a6142c1c405082c1c1400c0c1d19010301400400c0422003611000001d40d4140e0030f200404104090f90010450301c003041015070700b90340c150382c40700749600a8650643e02c6028041407103900c60b94100e410301e81440041d2401d40b0f00c0c0c680d910010010b9441c0046112040d0030b400b024699000c6c0c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 255935251 1106 255934145 255934169
    0x8010b031603270501060b0c06010605090f090403020109120f05040e15180406110a0c02060714010606020a0308160905010f02010209040c0c0212061b09010905060c07 73
    0x340d0010680c000c141c503c1c105041004c00d10a4000034041003c50600b4400f400031215144c503014402c106c1030107400034001e48641d882d03489444c1098402801c2240720f00341802c000f8001d202001080303518407086207070050f120b4001e8007040642c44050791014582030a201408102d000050040041d10b10708010410039a500c40c1351030303451000c0c0c2c04904d644030326190034045c090398020f5130410038a804c10841d04101070340c4828106003139070301990350b155030310041e00e4400e0207003001310340340c1d0450b510703010000c10407075030200b140c000250207991207042c151940481700b02d03030941501c0000d0200e4400b06080042e54042e4100305510800b03400010704056102c030100d0709481820305d0b03000028455200040c00c40c5440030113005142d8010f03000b06898500601e0b90340800b10001891240000c001c40d01ca004c0380e02c02c01060004c0e080180c840e5407600e4400c41001d40e1404580a00521400 = true := by decide +kernel

theorem cover : BRFrame.Cov 255755395 255935251 := by
  have h0 := BRFrame.cov_init 255755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 255755395 ≤ n) (h2 : n < 255935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
