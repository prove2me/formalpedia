-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:43:41.579673+00:00
-- url     : https://prove2.me/submissions/de3e46d8-6c87-4a59-98ac-94db0990250a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 14208639 ≤ n < 14388496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 14209889 1250 14208639 14208661
    0x1509040204060e09010815010e04030309080301030302010c030e010b0d15020c12030901111201060e0d0b01090e010b030c030a140a02090f1f08030a050f16080403020a060c020a030204050c07020405 86
    0x3e80c3e81180940002000091201d03800141c403d002003800085040b2039091a200c000e24900c0100203500341070301e87d40190000303000c0500860007540240c0c00007034a1802001d0042c144d070300707607000700220383e0501e41c0d01c00c0c041c7d9a2003148186070b540400c020450300c1c03d601d440d20117400b6195080c0498003503120907148002c0075000a511501e083c1008009002403c40c05000502441000b052549050001401182c0c061a40f0b0810140300400d443d40202103a5113080c3c14820036040013008503145e6100d030ba44000c0c03d0241c0140c00901b1801b86c4081e60040c0c002c40d07550151184003801140c1c4070500c4603440d413014071042c8000703600980f0b0b0000764541f00060003d6044140c3c2c200d402c01e54086408240c01420180800541c0d1051010350701c0c2407815041201c03260003a86040540e014104620034098a1880094140d24130804c0c032181c486140d0b004010403403000354070410522106021440040c1d650114013401d51358100c400242c952900244070400b4041d5400094000c2d01d0042030010111403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 14211139 1250 14209889 14209907
    0x303040311010203010303090b07020105120a06090e12030a050402120a080a09060c02030c091506071101090803130b0d0b1201050f0601020a020a030b0a1b08010e01060914150904020406 81
    0x2075107600340304040304030600e803c13440244409030004010400c240242890000202a142c0c0140340c0316040483e80c12100740e0f0030405603041b204050355441c0410204204e4040c0f40d0401c6515800b400d0a4810000b440c40288001090910515a00c1c070006003107684960040805071001d5044600781c2d1414a0010f041b40d00c5507800d86d010a00c500d100240542c803c80c1d400980c0760340030700940101200c1031b05018110700050141d40e50700605290140140d190f105c080c00149020308900203501407424005031803160607030008401e03504100701d210421180300b09020b0403901d201441e980c1c0c2d50071a1034810f000b4107c11114591100b41140078184680c01504060b0150280310411000c5840308001a66501c14002000390040061103040011070400c6595035440705201c4c0011880c19035001411010001004109001c200a10018803100542031241d9025042505003980568181514540b405031005007081c407900120f088402004009815100070000c082d20a5485589440001e4440b0b24 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 14212389 1250 14211139 14211143
    0x5030408060709050913030f0504152705010c0f020a0911030a0c050a140c12070b0405060105091003020f0103090c08010605040f020a0e0d0f0506150f030d0f030c0903060e030304 78
    0x104050740420304c1c0c41c00c2c14140e40a450048118040007111b9603040d100180150410414803c0501001a10f003174400308025403114203603910160070080a07042d418103c455103203081e10440d8250140b0081e42c201440c4250140c0007030040706c0b540704504c0082c50031102070308151149400c00c100300440d10b170001c0103140070b40150311301030000e07100008088841c0d00480440c100011310500408247c40390b044018664101c07604195500d0202c01a81c2460703d50041c90100c1e0a6200c1c01c0411007444400d202c0203001d0002280c07040a00d0610044281e0000c010340000380c860071b984840304100342e000743c1c0900d4213160b11400c612407003035507190740d2030007031455100f0580a0f41c142170300380d5041f00c2d052088451001d242c0d1500054101d005c0144219088074402c1121010040324402c80030038820082d59210b50451401d0031303510456081808041010850000d019504c44010058019084180558920041c0c034000510212180c02290321580582c80507200510704610080614004801148124 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 14213639 1250 14212389 14212397
    0xa050702010f031517070f060206040209070207080606010f0e03060705040501030b0901180903020a0602130906051002070311010219050105041e0f020105180603070201050708070306030b0105060a0c050304080607 93
    0xc104070154151000042d200044e410303004418842c00e030080075090b403040071700c900725000c0c00e86802070030200707850540240700903900820401045207031401141da484084c03840603202c1545400f01040d03541c40045c0c54503051204000485150602c0740c0158040e1000c005c080755003604015001034002d0780079005050000303003003d1501046003003640300c50341201c04107515000740340340300c5000000078002c4c00400c904600400c101d220200340640007811884881526405d03001c0d14141c3c00714120340c0d0759409a80102c2c80c08480a000301d401181407001c41342c0003808414400380220040f0b0404e80c0004032401c4000481c1c00310b8003440070540c007541c803480c4601e0321480e0b07a00c00e0a551594040c0c020b84014840300c01fa4500303800552080c80030f0104c2e0078805445403010004800041c5503a0800c1392240c0040c1e540d2800c00c01644d41c0003101c180c025150341010012a03080d5100c0c2603030364105000e21405082c0c00120515403501c6080503c8030280c000007541c0d1256221a44552280e43c1551410001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 14214889 1250 14213639 14213657
    0xf0302010609110f0a0309080304060f0507080606090d0201022103040605090c0a1e030212010504022b0605060a030204020304030f020f0c131a0a170111030403091710020a05070201 79
    0x1003000d20803d654030300c1c41d494260502a40c0b00c41d084495000360200c404058980c40d03240000b0f41c1c440b000c1e41c000c511400000c40d045007540d04d41021243e00030001070401c100304081c45401d1b1200c100302c0380c04a905440c20000012240010303031074104028006860b1001780d000303603138000d1100c202950045114001c00d001c140c844111941c1c0c2c03130321044c0001e40c0c844102441042000c01e400ba200c42c442480464009120365203400081850841c01c51098481c2d44541c104021468a45040d0300050004080406901c200d080d10503010100c680000701841e68500201c1c9061307403100802001154020300940d0790746400c3c94001d11030b0800e1800741015208651030b422800320081154641503102410030006003d612010001134402000c5200c10724103000c0000c038a03030300e0388401c244c0a0690706070110700020001e072841e805c45404001c81445c000c5c040c001e020019074018910401c0303e040068210b03030440e000c9402d0b810680d40400101460340300103050940c86030080040d2401078001d807220322603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 14216139 1250 14214889 14214899
    0x7060506031501080109060f0e120d0f0c0507020108070311030a090204021603020f150108060a02030a0209030106090c0207061701052403070c0b010504020c061f030b100504060803070b06060a030b030a0f03020106 93
    0x52701d12a820619094028140d00070b99007014801429072185a0500030034400c0c0114891412601e46070580e800055000400409558100e000c03540c00c0b4041d450108081c640e8541c8006c0580005802d0707810702d40e101d401d0341e000d55940c0c0d0151121242c81f9418034040d1807961801960398010750610000754040c015500440c0001206024100d48442019150b25650034542030000e5100811942c10a5800c0c0403603241520700b44030b40006031060080006610304414806490003040741d10120030003070f9000c0d0003021407141039885070460341c080e910321082450810401140090300150080401b6010041184196228030740c50072850054aa040060f62600140002d0340f1480d4034a481f550300400100e0a0707082500e4040348800c0c4c500c00b540d440d15433a5681c900c000e61007130301c60500c2480280800d04ca00e00d403030702c9160010026071000350700d400c07515601c805020400a00d9548500e0000c6240200c0320b0190300082c001b09401400d4410307120f11032402269028080340d0607030043d840c020300462 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 14217389 1250 14216139 14216141
    0xe0f090a0f030c03170f0403021009030c060902010e060c0105010603050c0304050a0201080403050f04080c031207030909020d1104180e0609070509040f0507080307031b0807060506031501080109060f 87
    0x100300d411201c031048034007141c1c8082d41d40500d25031080b002c200141c4000844c1c2010007004900540610b82c004001d4246824001d18001d4840e80380510149030820f40b100203500041b03045007132980940003107030206d050b000583c0d00c00011244280c10250010700c407445280198003803816900140c90400541e25040702c00c09071404115402000b80e8004800d000140d8068444103602511038035080b0f20303180000b00d464003980c01980c0f203003902d40e1058103008400d2800b0b100c06e4641c11201044c00e07007042d84540300200700000c0c600c105000f0301da000600300d00403c1d554100509104543c1c4841340d071241d030361181100842c040010040a01c0c42e007c41c00c0402c40c0081500c2e40a0403101d0002c1000758101020481001c40c06801142e405d1340c40c1e814030001070800e100200c024020311019640340d03601820060101100241703442055000240014005180f180c161400180c0081f0009225514800828540110b502c0354031080c00352038000040c04001500801405407080c4418040d071034980d02620 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 14218639 1250 14217389 14217403
    0x605030a02030901060503031614030f2505010908030f0a060e010501050c030903010c17010f030c0905060f0909012702030312060d0c12030906020c0108070f0c0506010e0f09 76
    0x144200042601401a600610340002801c000042c155503240c002034070316400318446183c041490b0300d600e018402100701011200c5014030243d440e01c3c021a107480070520601611208410b00c00912200305441c03400a00c2d952540304c002080611050305140c2e400703800480d40d91070420456800600c0b680c04034060b000c2242c03c4403203100c07590303400d01d0300555650b042495400d0007888107000e106140d40c0c090041201c59030503910b81d12510350000380d4401c542081608400300b1007959240800c0021480315004048030b5070f403000003c20740c6650f4000781024120107516075000c4a0752090100c8040190f2000620541d090101029407070186201008541607140295040d081446a1a2216901c45a440d401640142402021411903565200140c0d00b60401c000d10601e081a9008054000301004003420560004107803d9041c04002842903800418032003c20801c200907031105406040c00c505841d03404002d0343c550b903031580d031100e10031401202c581c0f1030514a01c02103103244102003045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 14219889 1250 14218639 14218649
    0x30204030b06011b020111030d05011202010e0105070b15060c0307050c01020c030c09060f06040e04030302030108010b0a0302100c03020709020c010e16060c140c090702031206010806010909110c0115090e0106 91
    0x3c0e10381813100343c0064600a44001c13504100340820003252811428900c29a406030810580110144102d400014010456400c0d210305004003000b0700b5010864052103a94050303014581d8400c0d2a05101c089020350003111a10500b511012510808219001c02e80c0a58280280e08135240c80e201c1400300340d502c0008120941e0042540004540b941c200031418440c0004007518044c41c2590b00d0300c0120902c00c0403201500000d0380840180700d0503100f0f000d1709903007001c103d9814a0b52403d40c4c0000d454164401a4201030100303e8060000b094002c1c44004000e05170040d08544034805180d0170307030107009405107514190080d0392003e40c90051050340103042d40c02c1551030020500e02c0307958103046100e50207003a5010788200e034410f9116550741c00d800c502c1030060358007441d203808080010b072210349001380220341804200710400140d641e00c02211030031981c03000310200796415080e9012100b0f114540c90104154202000d400411041c00398090464413040b07401c00c40c404825015a01700c40150040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 14221139 1250 14219889 14219927
    0x20d140606070311010b181618050f0d0605070e090105030303010f0b0f1201091a0a032f0406080a05060c04050901030f03021606031d01020f070b0907030f03030204030b0601 76
    0xd4201003446070381e1300f11050114030000605c1d10074a90009407038011000c0341e60354146820040000d03890340342c042c0403018511403d00c0410440e00c40f034030041141c080c4c00b807203025600d12009030446a42d030303202c8036940c150420800c00c11400c04038401050322040d54003650280c403e004c00001c05003000000c480c12a40c28044d070419540c00d00540ca03800d6800040210308291040c018050303402d90a05aa90003040d502d071001130090340010031211007807917002095105941910082010a1000c445c00c4500340c032951800103548002c0c03c40344200c1034030410281d041450404041544840041c80f0b00301c06000d04115829036840c094030302400e110741d002c0c161f0403d44440c010800110703e503d12010035440380c01910750707500e440c60360401c8000c002d0748010700290b15442c0e8a002c00318036441803110030740040001e5243c88910300d01c0c05120700c26040010700b00c0510000080000c00e0500803a0085e55200d030b0381c0d44001200307040c002c0c00f94102e40007e660060b00d11010650760340c0180b140d4507912140c0c0c11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 14222389 1250 14221139 14221147
    0x3030915050601030c020c240408011a040e03120c0a030617060f13030c230f0706090503070e0118090203060702010207061805061303030605031f0e01021e03060604150201020d140606 80
    0x501c092000030410000008e90000c0c0004500500c0a019001c1a0312100308107030181700d4540c0400096a02050341d0b4100c1350010080703141c40c100745011480d80302c000c0070480759840d4201c0000310024540740c1d00c2401607032803440b4030108120000ca00c0303501600c1d100c804000d20b0f844059507400810400c10005001c18a40b40400c0d00103582d16090200c1000e259018460450003804124189903c0101144483c1c1114101780112034103d44280e0240c0710a0740141902c500741400109940d0040c003407855000e041e010103121540054114200317555010303043e01d0031810f00c2440603000c0e41280030f00300c030f100f410302605c80c28a540b103000381e0070190341000c0101a40d0300c801c00380c01e03003018081a080d4201070326104003280c0380e10100704141e5401f403c01008100300c207101105008544010f10300b10000d9004000d03134040202681c10200751b60036040200ca5584d1210800908a4826540403542d03085201d00144006901940a4050060440d100f031021046c00121052280e40440303081e5030204d0140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 14223639 1250 14222389 14222419
    0x3070506030c07140c0a1d090303070207060804020d020d03050403030e03030702010f0e030a1e02011e0503180304050a06050702090601030504050d120603050f01050702070602060103020a0605030403030915050601030c020c 97
    0x2c4c1800d071941c5a03200070390300040d4001d000728011a40c15080100c61002600e1074126440141c0c81540d4000080d201560843c204a84029101c030341a2150100300b18640000ca001d5540c0c4061485440e64010280304070104245405080c9070803d10083d0701040d0140a81440c41c1808800ca804599050356107a0228090b610207407010300c4a0000e4a415110320710b179900004004c0380010420848002e41a884840148001024412001486050310502c2e141d0300c2c401c030ba00041038035040392510070224108003141901a1a601540c0d009643c02000c041c00000c180d50020010003400c0d00a442d042220364604005400307403081901e00800310f43c04401640d018a00c01d128a210450a00001088042c0d9039101c3d1071400d10008580d413100e9550300e080c4040b454041010f83c009144500150030190b145800246c040c2e40c151107004c060040010003c1c0405d4440c0d0b0040c00765981c0f105000308402c0000c5807500c01802e003261450f0200e031800450302c1d10303d800010032481a0000a01c1c84180390051 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 14224889 1250 14223639 14223653
    0x60801060201020708040317090904051c05090a0608060d08040609060f0305070e06090a08120c07080f0703020105030a06050306090c0103111303080a140d020705070e06100f050f0703020304030203070506030c07 92
    0x202ca42c003848c540c050140100301c1c0c1d2075110041c0141e000300300070017043c120b1000d180d2000c1110003080c000e0000c100258526911682d2042d801c50b40142042400c640d00d05002c141c2c0c010202d8001411400f00117404150250400c0f00882038450a9890300c100041d0110240c084420a85404010800c00b000c810380d036142c1940208035009010300b141e0403266075502820b14008120741c2a07000c3c0328001c1489004600c08001d083d009003c000d009265030381c90702000c030307032656441d0102904001c4000300040c50440300d60080c80080c80040c040701d010b1b207030500c0c2c6c1c81c3d180c8100f06151800281050341e03141c2c0000c6088103450300039081c900045016455070b80c41c0d07c0d16a00030b191140a02103d24a040c0d500c001d120090281402c0000d0050f07604d6040d45420f9081c00392580011452410b842c043c4031850300e803960342a01c80d8080b401d1110004510041c00d4415014041c2c0d0300f03a4468001404108041d030100141046910070b800b1616403e40301c500b00b001e0350104403002110340c0c1c003c0c002c00021030f0035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 14226139 1250 14224889 14224913
    0x60a0e0a031b060c0b130302010b0a090203040b0f07050f030618010303050714060118180f030c0b06010302030c03060405090c03061303140316050a0c0218010806070309020f0409030e10090608010602010207080403 93
    0x110380000039039071f4030b0ac101060701d401580d03004a0f42b103940442013001b48042078806c95440301c00302140c40860319104602401a0003040390a095503200400081c9a6882d0380010944145020031301e002c0070740c1d403071500901c0c0d0307485090101d0340c0d0700c111814078250000008a040c10384c0e280d00d044c03218500410300703460003e020070702601d5404494030000070089004d0018030302d015400796840c0080b140c02801d001d8000c46020b01310701d040500c100208203080c600e501c281d07908140200c8010a040e05c0b440d600a2070080078030425541030040b001070180c41d1400301006820284a5200c1120005011281b08c90b070380000c031007500756070000c2150304028a100d00014102071140b401d0001040070310340c001c0b030004440f08100b40b250307892840040c4085281080030303540c44007072840c00b4030031611982d022407440e81c41d5041260140f43c48003010410180541d01c031110802018000e81e0420913a400014070341c00e200c1c403c0e40040345001340042003c91060080300c0807942c000079440c3c501880c1d55145008116 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 14227389 1250 14226139 14226143
    0x615030b180c0a150918020a17040503070303021b0d0305090f01060e01030f051006080705010806190b0d020708030c070b01060903080f130902070f060506010e030606060a0e0a031b060c0b13 83
    0x5e00c802c04100c94080406c505c0c6042d50342400181c071042d021303402034000710644c001c0700a1361020b803080100040001084500559244c900580c503490f01c1400401c00091440f4a0a0f0310b000300600c81030b065526a000718440d9420f80c1c211403003c1c0358403408500301d4a00d406403030b02e6850150018004118400f80001410707118004850380750074055a90f000702c0303d80d82c01a61042d000024104002c1d0f0317001000940000341212107255001203240c20322001003e502c600780c0d1542c0c0214840380c0c20b0807264195045240c1040307013555285811320006032150700c05030b0100c0d220b10f090400420464410000241525480100280b9000c1c4003102405160080046203195090381000802c5800c0f10780003600b4024030813a21640c41080310702d007136401d4a80040240e8100b18034000c01b00b0f0301d039400040c40e94008605840700d50740c400503010111204103503103d00c0390300405d040d0800400c01c40030343d4001d2031029a04513003031240d5480703c00407641e02081d42c8010300505a000c0c0400c054004241d080f070b46080c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 14228639 1250 14227389 14227397
    0xc03070b090a050f06041a0c07020f01110a081b1c030f06030218090708280203010f09080c060708070906030b0109080d05040602070b13030b040615030b180c0a15 71
    0x2c0003583c3c1d5285850010b40e00ea84c06030300081c041c40100700110b4603064946601c040c505483d4508148007440c24001e003c030107849801407800000d116400340003000f920300102c0050f202c0c12140390030302d14680c1c0c0c84140d8118000088003084030a8610100c4d854000411507540b03e0010030001004070050580002144102540e401d00040184d0742c10381f415141c40030680441c219423400c4499070f4100320b40c030b6001c210aa000082c05996910742d5110410410ba8112002152000d4070300210b401040150000800c1500d0700054405002e11b02029103144800201112219030704e03013404440072042540e592001c00c150b07100500c8114000d4001194440041c0741907130445d961807040c549402e442c071302c660000c143d0020301404074903810701c1840d01502c0003c0125107000c2585801900b130400f184005020600da242c0894104500b40c0c102c1070741d01d000507102c903a640380c5900b08480340b50001d0f201c0c101c1e01b00c10106035840611000c80c0c0814850802072896055074500481ca503405640070440c1001c02c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 14229889 1250 14228639 14228653
    0x503030708030c0c1c12050411101e030209090a09080306040504080702090c210412080903040305010e0c040c030b030d1d0a090605011b05030f07020109031401140a020c03070b09 78
    0x44007004400c40c1700341d0030307902808540190315000c3e0000d0a00394003074000c14108001c1001107a100d01d4a4030380d50800341c41840102d0000b0300115080c44094042c042400c110030180740009515402810080008441c00400c5d40c1329041d5400c200c46811030020200c3c1e1090001915070724090340401e900500601401c0d1821050f0350005a0789030301100c40700b1180e4400700742100c114840805000100c000e041415080c0d0a15448000904041101d24000c20032608002181800c040c4107940c02590b1080c02400012010381c035060721480e140340e0990041d1f00c1c02c070460300d40b64401c2c003441d5a80e040140c054050103034a203030211081d90388400019808001d0100c01e0791282c507904445401000b06d000001880d40c03c00c80014541503110900210b0742841902d054041a000b000b15038000300340c410403641e41c00080c401a0b13120340c62a407024103001468820444455010340000c80040c240d100814501d98400c1400e034206e0148810815440d8010310031540040c4c04201e946420581e030f02c0c01c45402c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 14231139 1250 14229889 14229907
    0x90d051b030d050417090607020402070203010e030403060603030e0121050709050a030f0b090105161809050906090106080106060909020318010e0a03020607030501061b030c05010203010603020715060503030708030c 94
    0x40c641c44042010502c0340d03548100700511903007140d001e024504a60400386003440340d80c000352042c042da03180a8465540001c40108542d825800362406880240c00e42c0d849070341c0d0b810800d00030300036444260b02140c003440301410203602c2060300d4904012840d6609034010800c500c000002c0c18000c085800740018400e000ca42540e0310f0080710000d610800c02910140514074002c480c0a002030042107031171781000d041c088100019a4020648403113880d222140c101c2c1000709a07425030480c1d102102c0c0d40c0c03800e401c2c0440720b01c02161281c0301d034401c0402400007556404002d0300300c030203a1040b180016503402c804c1c000d4503125001540c000004506d10903a50a8001541c0d003118200c4011040591182d100717a030400d501807003034a6120000d410100800d6250001c003400c0e00701d6251034040740c10301c0740d00850200760084a08030610394208000715100c1d03845520150003980701007400e44070458440014940380515005813030a580c000b4001d1400c2591503500c6034065000079001d08203c200602100e42 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 14232389 1250 14231139 14231143
    0x501060f0b0a11030a080412020102040b0307080711070b03070f09051c0b010b090303030a0f230108070801020c0c0402030405030d090b060405090318010e0303090918060708090d051b 80
    0x3028100d281145503565032040070260841401a00307a0319540c0083c0420b100940d0402c0c1440e070310a0b04007074024401c50000c04d00b01d0091065401c00043c9500200510032401c1d031104c5804d00c61011525190740070400014150741c1e51955114400ea808070820000d0440da1041d00c0002c50324801d428007085003501c03100051291011001725002100e41500040244245030801600410441001625040b69403000c40c0c0c603440b00501c0c0e251000d485611050340341c56150722500c20305803440140e0b1040000343d02c00c0a2801421b00c519280d0b4030544102213207495040c400c42d00f41900b41801007810440041c10701000c1c3d00020000c1d106408144004084002140100e0107102d104255015561034580200800c0354409000121203910a105100c1c40320b01c44c02e2402d04070182404c08800007081e80001a10f0340c03046601c940d8024002c0070074415590381420042c000d608110058520070b0703840303150498403102c04440412140d03122041e05440c1c1800b9100400801900b40603ca81c96620910b080e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 14233639 1250 14232389 14232419
    0x1101030b0f060706140609040c06050f04170c010206010b0c03160c03080307020102090103180807020919090302010b03010f1b11100203070c0606080303060d0312090605011203030515010503040f050106 88
    0x1880c00c41d1034505041c602c117442c04450350703c400200e940b101142040e454040c4005068010b040c02c2c41000941c000c0d00e51080e0080d600140181d00c040089804803511142d1140400202d060141c4500d8001180c40401031082c1e803401c4520200440c203103540d41220b50013070900c2d17040580d8090301e240c2011001c1241d07000107611c41d0885800240e520800c1e40001001ca400008400d60100c4121070000006020241200c2c1035540440c4e001c034154891031a0141204101da00003005c0d180b03070611040c20590107401144801d24203c008004e003000b80c00c201c105580c40203a002114800009000004900410383c0a07469002c0c42c044468040c010314402080303a00c151040c07030105000050b054100201800386802900d146000b440c21760600c000440d9002050b00002400d01440303e20300d801445081d0702c501c0410390881c0041c002035940d444c0c10000c5e0104070304e003500040e05000000304915900070007200300d03580c180d603842c0c51581c4680300c10464030b40aa030101c40a549840c030014003461007c40070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 14234889 1250 14233639 14233643
    0x30703020a050d02030304020d06050a0e030c010b09010f050f01080c0d09060902120d050306060a020a1e03080f0112020105030903090406030305040501180e0615070f081306020105041101030b0f0607 87
    0x40c00c00c2495810120f2030485522034100455104104210040c9c864a202030f00f180c3d4030000100303042e2109204107003d000c1007030940e03205100c045458051520b0540007415540030130360f1640c841e80d8894820b0000440f90303000d46604180000050340c1e06501c1082c82661251070814034505141e007150740c4000f5120500301c1910b10584514155066140c807130104001200307500010404c003030144801030210700006020b03921854001c240d40f4803070b42c0244200c62000307030b1054049030008000c0c0c0d940b242c010014a01580082d401c1400250b5480c0041d006a050710035001201421700c440b54011078990348000c0c501a01d0b03000a10400449031250b0041278050f511a4464a85460901d000100084012014148126548803082014800098100e50003000582e9040b40300d06680120710301a02c00d115004140f219003581d80c400740401c035030140c0303071548000e060003030b000d0780d5070b00124265001901d001d0001403089043d6161980640e11003a50300d11b0241004241842000000f50150018501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 14236139 1250 14234889 14234893
    0x3030a050901020709020f0a09230415031403040609051c02040f060b030403090602010b010201020403021e0303130801021905040518040203010b0a0e0f070201090309060503090304050a03080706050c04050607080d06050303070302 100
    0x10100d03000d42018490740500b404446034011444004462003481543d0581d860003140d40e81c189201584652070301402458000ced0700040c2e406404007409503298400e116000010b90403a0f00800d8074500b21003402c4020b0b072040d034000a40c150940822004080c0d003407600050903130f28800000e02c400c02c04003542c400d500944620f10703400d01d80700e0041e080d211080d51460459104100c2440182e03603a0f00c01d4003840504c0325840303601600d80741c0031074514800c441807045840142140010301082c15001042c008445100710355815410070300035140e070f01440c01a503074418080000c09130a118600f401c5540f01d40010000304107171010501140e9400225042590310103142020010645e40388070185802c54040d10080100b01200e8a00902c07111090146901300400000400c290400420071350b8007409000b006c21904503543d14000c085540710700c0c41241c0c1d82d42000001503580025034155011110040c090515100d01e0399910840341d442082542200c998070030f008286520b007000034040e0503100f500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 14237389 1250 14236139 14236147
    0x303030513140102090915030706081803030108061f0b03071101060902040605120903130509070e03120309010c030b01021b06040b030a05011a030106120c0c0f030504060e0f03030a050901020709020f 87
    0x140015444010811f24500c030006d0756604090300c0004005086588514004c443c5413600f0058850b150038a082c4450b540c403004c000030a03c0e001c04103200f8003603883c00340d180654002e41d0011610700c0300d040c890b03440b80c55010300020750000e01800800c0b104484003400043c00c961120b01800403600250452000110081502d40c000004052015000344100c4021424586091050088503c080c0205400381003100e0109100728014685c888507040001c1c15102d641000d05d5068040e500101d885003065804d281c011203d081c001c1c882c148510106034040d1649072a0743c07192a00060300710049607084081040000781c00d43e12a0082c5005802540b070220301c9525100740d491464415410980014404000400c88a40c01184441419203d0300e00132070340401c0c1c900165016140d80e1006890141c250107000100756100c00180b00f590b00780c0d00c80740340c40016041800174040e1081c2c1d440d500756204001d1800ca9900039030141440c20f1052048440c0c9903280c0e801d00c410703a00a604140180034001c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 14238639 1250 14237389 14237407
    0x4050c0c1207050a230601030807200307050f1311030405010b0901060903031812030c030809010c0e040203100f09090308060103021204021302090409030903021e03070303030513140102 81
    0x80581841c124101d03280074103240054840ca92a0300303d00900910134410007402d4240d03500c09102da01429100300701969090341c0e40341011502c59001c03180c1200c80c00d82038005041120000c1011810300500a4020802c050030881801002c001c001780643c0d00218210111a030419030303010f0518098024072316207440e41018a03045003960368900c0180e00c1440c0382001030229540c8111984101c0f6010324004d420603e203a4071b6506040d41c1c0303411018400000c640c4980c01d0640004071070000701d00c26914524542d98401d030803803c95042c804800000341d02c0075052402071030503030007071600a00074030020f2003050354800341504204a281d00c88052a230b25102c52000341a0800421035102c00282410740c81c24070b0b03507101c9036200c0e600208002d1040900c50003001440c1c4407503041d101030120180007009240c145040c06410343c1c0c500e01c0200d00c941642008030422100750078491440c00c0c409002400e00604582e41540601802454180ca01c1d0500003000045001ca0083c440d11483c0d1200040e80d4000103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 14239889 1250 14238639 14238643
    0x131a0909151c02030c010305070f0302030403090b0c030702191a1c060e010e100e060d05010905010f0b03160305030304030804030c05100606080a0b01091202030102040509040b090601140303030a05070c0204050c0c 93
    0x400405d4145403a00c07040100c0341360807041712400c84800d4a8016680d82e40e1346415116880c1c142c00100304440b000c2041202040000000d01c1e009008584810920624031040c408800b034501440100800540c503403002070b25a8000703000f5500003044400c0c0d03c000c0f40400d2004a03221948140c840800d900010802490030040e1684c00c0b9036500c48154050381000c480e00040c403406401d8074011400100038505120b002e50002c28140e9000d0001d10542044034601c401034031303044000394800e0148606240081e1001242823080720f5202000d1070031556952000e550110000303200f0380c240154921300e03200181e02401407540300300c195940003c1090400307100800705c40d4001d042c42c0f083c5143c018081d606a8102c41140122650034004c20388009040c0301107130290040c0e07030111b5004944c11080c0010416280300329441154a04121a1281c0c0c1c2c55515405240c03c0d5200640c16403c10000304403d142c040d0003960b0301c4059414000401d0b0541e07400308080720380c22144c001d00e4100225906c5688201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 14241139 1250 14239889 14239903
    0x603021002070303020604030509031e07060905030601031703060d05030301080a0b06010c0f060221010323030a05040b03280507030507051201140111070b131a0909151c0203 76
    0x105100030b181d5141140e0780a592071402800140034488041808102541d0400c416440c0e01d500c400f8400c0c0144662581c02d54a82e014055040400c3e68044080740714280000c58a048a4200d001145440c3e0800401c10443c3c0c00580850340207a0300d400500c1c00700c0c40410045000f000c0703650081a50701e41c030307003481085580040c08480c1001000280e980c00318045103480d141954110800582c0c03100c00d200d80c0c200300c42e05040740004004030348000006011021000703000e400d25071844000e007138140c0040c460f02d9205000004011a809206c14009100504003866100300c0d6407024068800a8048021505444ea850a1005038941003003102256060180395003008036800d200b170412a81210141180605001e941c0c048100059424040d03849030803400035120b182015142c4450711501c1c803d06a43c03044840040411190307100103815040c02001d0b9000c0040188401d0031b0074000801c20084100c080c114428807020354400000c070f95a0203801000151120faa0608090380310701c107040c28050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 14242389 1250 14241139 14241169
    0x2010306050f010f08060102100c0c14030a0504030303020c030d020d02180102030901020c01030f1103010605040602010605030303070e130f060b091203030f01050907170c0a0201291504050402030703060302 90
    0x80a4030752030b2156608090110f01c00c24007170600e080a0307520040100d02c0e156804d000c2d52035450504500080603900701c003184901c2801103114554040524040a03500c0c070802052000141c1c3c01c102c03c0020070301c44e6016100c80c0a001065920f031104008095050340c0088010210303803a80058850360a0400c0c00c4001e020520030b00285003812a80310012351100540106103051544420651070102c1603907200980c1c44060980d91600c83d43c40d02c40007001750708a406000c000d03610304440401c1524000040d68030640303d550f00e05032450b50352001d02820f00454a00411019240c42441c044402c3c54000ca6000c2c03d03002c500b1740c0d10f401c4010100502d40303840080c59941600100180080d1941401a03241910025940030100d61606034007259403007071820003000100c03162000c1c0000c4180300c000900d6080300380d50003440107a01d107003145d0300c2002059805842200c013036441241d103802d1045402c002c070045550300a007440e54440108041e680704450b0800040d0b503400c400d01c1107141628981c0d41001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 14243639 1250 14242389 14242399
    0x20601050312070c03050109050f06010611060402331c05040f0609050703060e0102040e0606030601021b0f04020d092306010303030f1b0c0c08010e060c07030302090a120201030605 79
    0x5450040400d4454002041d440c0410380b0008200d014000f0103c4013000456000008105600e55410b16549810313043c6200c012500484000154407071090b03101c2092040c07008058012034865600b00441c104248048810f40ca070884140703805880104640c95807000c0440303140384c0c0c4146400500917080748c00181c0c00204c0d8a02400d000111305615000203e0351ba104000099424080c205646840f0050380000d19a03802c0c016a440300103010b4014000b100c00346201c1003030075150b590401550340811541075005a10840300420300d400003c4401c402124080d002c81a1000780c07001040c2660f00060300d140303200d91160351107020000114954004080d480030130814039041d001000303440d40703010711002e000c240d101c00c00001440c0c8198440d0090055100c2d004440d03030204040909103c144485c16101c80c00e41d00c1c00090300c2031040c012400c410402802614080c0d82c1d07007601d1015500610b900b902016824403640160b03840b0128580040d19010b035240c00c01851500c001010f440440c0c01c240e00503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 14244889 1250 14243639 14243641
    0x6030e03040e13050c0d0c0905100303021507031b03090b0619060806060f0409090507050139020306041401060605041406071505150102010f020a0804080304140d080105040b010206 79
    0x2c90791406516400c9809070424109103002c5041191408000400d02d80c2c0c030944035502d8404001924035070700100d80400409000558030000c036841c41941c3d6120140141e04000c50b519281c00031464455801030142c140040c0c0318010550001c150301d80e803541c10700401d6556004000f8440e41080082d072024048448001d0401e106101e200c00f0501d92080d407062200c040b0200d980c40c3c0e690420385540c0d001c1d0001c4640c84503074505454010b071105040c141d40c00d018054011920354030840c2d02210851a440190a000300b004c500403030303001001d582e007030b0603400f0004100300165400d1103864000d81c001e0b009030124001c0e40701c0d65070031141c1c0c1d54018000e1080c100401c210307900030454040c5284c2001c6074209c0d00e6640324240120381c0c8411a1a05519905d0041008000304444000540104082c0c1c0200140e580601298049100d802c1005000c20300c1c05000400203003a10006540c010310441404103410f10a400c0c09203051004403001002c070742814010b000c141003900c20701e41510401d2000b0502 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 14246139 1250 14244889 14244899
    0x9050306010b12040503040e070c0b0604150b070804050607060b010207080a12030c110106150e090f04020603070512101d040b010905060d020a1518030302030a0503060d02090405060106030e0304 85
    0x150f20400d40100c414018800c006428018180182e600a21031040c840034140307000023005058000d446d42c01c45885451001103001400c0c248100c140120036150300c40700c007070308041720420941c00144003180c003210100b0000c207440d16030701c0c05040d00303510aa801240071a0401c0000e800e0a1040d080005140d00181d5020007042c0000690b5000d40302d64200000e000030618009c580e503115041003c000c1c0d600b010350005140391556204806005256240000c10240c1c5007086407800061ba052555001c145001c94050701e0440015900030409050581c40c04142c140159840401104c00840c9886101401c10042c0c03442e035410003140c3c2d4840b080bd5214a020b40c4c0d03901e80601d041c00360540031070391040007540540324202c1c2c4102c020f400401c01d404503503950078442010300c0203000c4580040c200d000001a010030070603069017940e5054000d5414000764a008440c2c1e074100904280c0d0208000e40d41c0c00150b19aa04c030980200d024601401c4550305154010b000d40d90b05021004056104000400c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 14247389 1250 14246139 14246159
    0x40606050309061f080a03110705030a050304170304034704030e030708010608010b0406050105070506011404090c06020604060c0503100608041401021306020f0c09011202040e0105070507030905030601 88
    0x6070085100c1c1d10307004c2a050070300d034001085a064001d20342d42d100c0c1001840615070031400c3d0701600003140003280d2040752610f0501d40c807107000c0040100294028002403000c403030700100220140f18060212030811f42d07603032100c4030340164100e02c6200b000b0086901410428040d040d0f984803050103080300404c0c02d8041425400c100e0700a20203410440e400c081a061541c0602a2500a20301c1030024001d039a100e80000b8000c0034510005841075103021b600240550189054515013030300300c006020141e103802c0c40c5520680f880400c590b0701a035178414850004900403600c0e030103481264002d140f14580340c40c1000c1101c02c3e87d6051414040c00348104480341161220765000d0b50114988803045485507e800724850b020200000042d500108280c00c00e0300f0a0740a28049665607400c40f0080c01d0b00c42907031600c0c0c01002c00401c0d0000c007000300601c001c400c03581161071041d01c0984001808111696103508403403080d5a880d001810006580c42410b40c0203080b000941022400341c0b04651511129031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 14248639 1250 14247389 14247391
    0x7030321091104021c15080c09010b0403080c01020906040306020d15080d03020a0311030406150905070e040506030f151b09090109050603030d06030309060f0203120114040f02041404060605030906 86
    0x20f10540d00000e1450411981c007000890710304030490280040415603001c46003191881c01010703140d10070207406038a985000c50805048441242155203410b0850301c03501da0304c0d48003403080c210301d64003000182c505446100041008500031580140c407581c0352941d04c03080c0c0b06039020002d41107900c80f0090154010200b010082100d02d42401640c0743c054140a8020302001501c05d030400740c02104100c240301064010141000c2800c5c0d02c51002e07511601c2c80401c0314401c2e917034140000c40c0c55180301e0150a065001981211005040303400e100c07015107141c0d281174038000402e551410582e05004104588031003401082d158807540354100281c0d0400f1031700d1164144681c8898a071181c4c0030841c1c545040c4205c0c1c0308510451001c0c0003140d12402c0113031440d002d034410400061604040d0503141c40c404000e803448011080b200102c7d41e440d0440500130180c2d01400e1a9102d0b585170140318402c15144000d02c0100170340748000c0c00010904d400c200480b046944024140442002000781000d0085112 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 14249889 1250 14248639 14248673
    0xc0a0902090a03020402030c0a0e03120703140f0c0d030606020111090d030c0b04030504030b070c02031b040f0609060305070608040b0c0c010b040203090c040509010c0f051b0703032109 81
    0x140c54507480c20010341290100d5001075002440041400f5a48059100504202801e078079014000c0c4070003070906079180c01c0c10315440d07021f000522003034002901c00e65000f04480009a14142044a00000650b50340d104021043c040c0d8001d440e074001c81501401030f040100200d000801801007035420940307480c481c071924944030f4204804001d0405000e022900115034200014206610b03282c503001d071465100e07010507201280744000044140d480b86a640c03400a50207406010911480c0400c0502085c80e401e256520549134800300c20201d006119160081102d100003042c080d2940c20304505140e00c2d0740100082202c10070400c40031403902120300307030081500500195a900b124140e02d00402d41c0d030203866402030000061001c441c0c80050303102e0b4005000ca0b401c00c02903d44011941c00c0f00d4030007404101040103900b01035016401280035101c02c444003c84100b02c028403800d40380c00c0c446203400407004220000b00071034002c51114140160261940020414404191160446074214040c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 14251139 1250 14249889 14249891
    0xf0c08030603100204030807050601090204030c0b07210e130507020303010e040c090204060e011107030201020d03020703030204050405010305030a120b011e020a12110d080c07020f0102071502031801020c0a09 91
    0x101d0069141040850410010254210b4940e500c030300e800f6003541c1c82641c00340c1b01441000000310f07500c0c0c01071003241c041301c0c0c0c030406902e001860081c034440c0d550450501903454030b41d02c0314010750640c0d900100301040d40d810360700d542e0426942420403101143c01c440d022490f900c0c0504002c0c9a580000c2200d06681004299501543d00e40c64504a0703030f04103801041036580045400920a500010314002040091303c400c1400c010701031403030341d941c4058031010380141c2c45441c6400c42c03640070b58003e00805000e4a400b5140980b20000705007a6002a4800c072026403001450078441c40e407203000403e01c5151a8002c0c4800729620000034855a84000d18a11001c966044024414000c07c08030301c0c001e601100344400c0c09c201d0803000e4a2804003201034500c5000b402c24000d10343e8030402c40c10340305801218520382050340903001e11040c80130600241d07041d445540408a1a0b05002c52910354050403940196a208141004c1200310f400141d8201d0555115080c05a02c0c0e603204541942a624a018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 14252389 1250 14251139 14251141
    0x702040f320a05090f0a05030d06080a110103050c0c06010b090f03030307020607050d060905070e03010b040902010909020d1d0d090504180b07021002070311011401050a120c05040203070e03010c0f0c0803 89
    0x44603d040001178150920340d031280e14004010000e012025108080c2c01030010003029039102d28080d241d444080d40107002001d045006060b40d80640c3c130158200300413103100d9080c25507080005e40350001c2038200789050340000c00c0107915442c0401c0e01090210069000d1812340c01c00810103940e0b0741001c3d140606202d80400c0c0c0c0020b0042c103521650044c45900c03030600c100d043c0400b000c5c0004c04183c131003500039402d12502100a081070f0048c0e800c025410b035100c501007450010118029003001c01c1c0c0a140c1c540300d070f0b106002c000140c048142251508130151100c0e902e007400c00b411120b00c1d0382c80603000c1c90030561145007810034000b02d070314400e13000101c2844540e21000e0407030071b10a2000c0c0d0300c0100c07440032907040c09150307000002c40b5100c801403008210100b0b504030340490b400400d104007540a881c2110038085c0c0f90003d0302500c1c00d14400c992561400340c40f43d00141c140c2e0421a0708a0000305e12681c4088a840c090040060b48402e0b41040955054042401000300e00310b0000981181d030004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 14253639 1250 14252389 14252401
    0x60c02040902040906090c080f030409050c090901031b08010b0a15022b02061b0a0c03030b10080402030d090303140912060717070206070c06110702040f320a05 70
    0x1410418801e80c0c003c0040200382054605100103220401c015a0048481880406c00000004035100481002c0c0011030030700c0c0c0f030b02340c582010348001811805503603410b003d40c61154613480c4010f03002c1d500c0340c603048802c01003013004541d81e032486900c1100142c0c10301c05110859100d4580342c00c00d0b00c4a40b80302500001200b503044e0f10b8401003102d80301400c0d03041d00ca008225581401440703c160000c1e0300b9901c041e107458914203c885040d859040c040c010800070140c40c2030180505400d054428100800c2b05158900080c554030005540f40011030740c40e0040000714075042c41400010602401c04505d00303130640c1c80c01404803841442c6148040c8001644240c0c87e640c440407090341070040421280301d07181c0500024000000b964017a004460300c003010480c19400418180d1080710b05135601c0700041042d841c1c400103001c0240088d20540800c00220f1701580b00c074081c0c118079096100e004030b054030b1241420110048650011400c0c000804941c0c901c00081a9050b90000b0b000240480c03144c07140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 14254889 1250 14253639 14253641
    0xb06070201120213060201050601030f02090307050108040c03060e0303040611070b0105150408030c010e010b030a0b1603020c0d0c02120c06070602073914090712020903030c0714041104060c0204 85
    0x140a000e1303c40d410075000080c005505401c0684074180a0ba02032002410340c0d01c800084e405030350b030f00740c0e49500807800a20155200b059102c2d8403c1c0140380f944800e0756203848500840c1c02d4040c1880e04c41d04000b00300014441c581c01211520840d0400d0f0529004080c0c880b80b22007481030140c180300e2080f000003a001c2c00c1140042d10080c0c4441001d9036a160401403006000f040200c83d60f0101d0f5081601c4071199140209481c4403040d00b0001d1046030303540300154107002591170781040c0c05240d424008a0420442000801c1c403a080c16102c8880682180c010031410340e101103500d40c995030110240603e56103800e0f065410700da50042c0c0160301e80075039242102c1c0003513641d550300789202d400c01c0e2410758101502091481a5100b002611942503e41e240e20482c6941c0031130094202c1d402c400800c42062085c49800350b1140101401070500301c62000107030542d4002c0100208940c4000c40500221142030032511424070202c601304403200c1016021100c80c012403080c10288542030f0503100c203648403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 14256139 1250 14254889 14254897
    0x7120b120d09170102030106050d0203040f0f0b0703140108030405040b061e030103060c0801060507080702150a0203040905060a060c02090a0f05011203020d0e0901120507030203071d0a0b060702011202 88
    0x1080c01d03205004100d070701c001c0194845105507107005480001e620160001131089a050b03030429a940c80ca010100700302c0e138020350300150041795403c614540c0c00c40030031502c401c281c40b0944030340d000152904241c0001002c0d602400200c02140080781e00402200310000110340403200281c45c0880c084092100051103401940340e0790359422054440540b403003000c3c800850503648512010070048041c1c02045036030400900500003c50300c10020708e804642200d0103801c08610040c032240300e205400c003001c01150803120681015900c040b8050160001502410b94452010f8a1901a00f40b60580c01003445155a130040d00400f01c40d0301140720541990400900500c07480701c28019565a16601030410341350302d1082d0014000e045003078030054420892060555002410003406900b8242c140b001d44c6901c0342e04880346d00c03440f000007006880c144080b5005002244070710034a00a01d181294030780d100102926109842d01c0d04021b501d036500400d46503155028644500c000c0010b001000082c81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 14257389 1250 14256139 14256169
    0x2060711012703021006030203070e060301020d0e01050618040510050915040f060507020118080307110a0506040203070501020d0f081308070c03021014070b04020105190c0c0b0307120b 81
    0x2040e0b0300082040c012030803065402c500c241e0881d981224180e0010707046940034000203505d80c000100170020500350888082e00084000c00052510300c01000950440d036402030b0300005039444108100c0903261400c00240b482169000070410b6184c1965265143c0705e00018000350b00f9036401c04164500c1040054100c482c03500d40400304181042e00780400030b00b5100604444c4607050900080c0801d106004d001c1c030302186111110275011996840c00c600c0c0d00300a0009040044010300d920004000700021950540554090485418030340140341c00c22a00b500002c0c199440b007203034081501d41c80301100d8180640ca207400e1240e83c031088034070f0445442d40c400103003080f00007042050a108030400240201c0e44202c804c040b00c82e0140d02d041c0d4543c001040d0f004440081800b524000c2400e090956500510500d04980383c00005a205461080e281d40803000140200c61400200f000c5501904c014041c510805030039413410b0880109205260960340d030b40652145490140b0391140307646810404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 14258639 1250 14257389 14257421
    0x1005070302090909070801050a0b0607020f0609030709020c0105010b040e180a021f0801060206011a090406030b01080a0c0914070309050c03120901080604020c03030609070e03030f030106030b030105070206071101 93
    0x1308288601d5651559540900c000c43c0d440d14010902c42941d6121360554010043c2201d4204603694081050f1840c107010b010b90402000c100c8040ca9030f03000d03c400d6001d029804da0060b00d4501501d80b07d401c488050300910044d03101003000b407003030002e40400c0075402812455503514418002c6502070030250060300c000c1d044110403600440549004a401548100c1682c0c0c03501660f80c0c86030120f03641d020a10601d42c000c5400020f0307101502c0664014500c002c07010300042071007966941c5540f070451003640540083c1e0445030207401000222102c10004008c004410312101840611400080b000034010300181a81e5030810760400078280000a02880000c080c2c0d800c0c1e007101c10400d6115030108440a00240c032541c00140e1502d468800c0c5c541011b1240e00441c03c681d520401c0c82040000600040e090150390840c410181d40d0800080205038004c500040c3c40707516116001d803d5401c11910702c1d02c241d0600b02040780340caa002440560110703081c9000b1038100c001030b03600e83c014042c0c811010300b04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 14259889 1250 14258639 14258641
    0xc0b09030a0212150a0207030e0d0201080117120c030a0810060509040b01020f0f010b010f050c0a030503130c060306060e09240d140705030f070305060a151503050613090510050703020909 82
    0x16145d9501030b1020340e00075240c45811240d20800c01030301d005412002408030384658010310030794180041200c00d0b071200400301c44440d03011000b640e4840d0014019102c81e0750000850095507507011480c1608040c403072107010051402c246003d40b56005d0203507854000d81d0388000150080c1e208104c0b04262039003a1781035840c0882036160003406840844070140c080795070700d41c00300041791046048580c1000241d002d0702c0d14002a44d02112141d1002e40004000d2340d42440f072001150000d0107002c010310042e100040c0c0586003041c050400682c1c012700c9449110000d040000c1c230404040201c2c41c081d8060341c1d120700441e5540002d40c1103081c0355400b41036002100d5500c0c6400303000166410695108908556a51002108282d42c40b105404010510b03000780c400b180341c0c003c140d08050391040c00701300030641054460b2580f8904c0780011100d03500080d203800030300c003603810b0031104190b209000035010312500c81030303880d544c0c1e031050030320b0380d400405549000060240d07100794165901c040c03006041c0302c11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 14261139 1250 14259889 14259901
    0xc15070206031504050601020a08090d020103060302090901020c070609120201080402030316080301090501050d0c06030e100207051b0411040b2101080d02010b09150105030a1401060c0c0b09030a021215 88
    0x803c644191a0b00552808021841c250700000e8a0803c543e4025075031458440c401040c010b0000901008074181902c0e6880030006a6824140904c242500c200060b15030b0311151706c1c2c41c0b0b404110751054091001d0700e4400e20040c0d001905d1181190b80a003400c08046e2510310100b4a0362166800d481740c07507171811101c10200980e00f00154104d5030b0301079041c01180d1f203403130070010320350a2514020901100d03604200f1a41d80240c00101401c11174109491f030000103800351200b43d9001d13040c111b401e500a2940001140004000341c003500e0000d68041202c0c2461081d0f25010307100710f0207900039004000c1400c5002d1b866085024400c542c030400c001c0141d59403145610754825001e5207481c055403d150203001a8100aa46244a01c02c03504130b034044000c08400540e151f90000d04144812130701c95500164180320429094028200c95035a10440405070901d41a00c0086810484040000b0480c1e0707036155030002081e54200d50111548a0301d00b05a042d030916010f424591031701940b0780e04040000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 14262389 1250 14261139 14261161
    0xf020f0105010f06110c010e1201090b04080306091e0c090307050a0e0105090a18080318010903020c011209051024090507030f0506010206010603020c0102070203060408030106021e0c1507020603 85
    0x456641751100f540c0d1032003800c0c45d5a194a000c0142a0029443d01d2a5034500e2401c0c40543c0e02450000303000042e941d03d5900c410780c4030f0008a03010784400c4400803d02542c0e04107002c50748c1c0e101d143d280e0341519500c40e1482c2030702c48000c00303041e0902c1c1400119010006507005c4c8080c10082c40000c0c50b28126998851140003988824850203215840c2540040c10b0030815009290810030030709403d0b00000f2240d07230b40c80115080904030520030080945000003018091084101c61400394005142c034007074100005101d10054074061a1450a110032074002501c0018611049a48075401183d00009500c45980524006924411590a0344c400003810303039240e03104900130880303a03034140003801103070b0710740d5054882c140c400038016800300c0c00410200d40300781e0182400d602010005850719a9503000a03251042c162025221158000010031184c0d0701005015500b4400014180e101d40e043c4010a403551154041c55000d8401030030141aa10580d03802c603486503070300034903098582c00e05200000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 14263639 1250 14262389 14262419
    0x6080610030c0503060103080d11040b0d15050607020901050d080708041401140702090403140c01060602010509062217040e0108060a1118010c210203130f030f02010f020f010501 78
    0x2039910310b004140441c01e401e000c0f0784581a00e8211044030701e84218810302c2d100170050b51800200f4a10103020204210480c07100500c0c0d03c000a10010484d0314001059802130505640554400c0c64200600001030f1500764105045030012580c427400000c03e0f040c018114403034040001e01d08000058045820750b006540d41081c1c00081c0d81d0700b40c54103180c0284110a10030f81e000a9481106e800001d40040c1c480c0c102401c270758500300c00305030800001c6500039082d10410780240e0701503510f40080001c042c10410400da07100c50703004458a614401d10910b062900d09203140503203011401c12010789401c0c450340032100100404210900c0d55a500c0c10f216440d02d80c1500c01982c91428001003d0001014200382c80411440007166072500c0f40a40042d1410b6100d03e000311018100d440c60085002ca1020510148010342e402071962040c516076082a911203e8005050030701100d2428000300d510361401c522000c1c0e080c204441014a01c442c10307460f00241c1c00303607c101c5600b0b003000454001c40103c0301d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 14264889 1250 14263639 14263643
    0x30803040309080105010f06050f0d060506040803040e0a090c05120a0b07170702011104060c030207030605100608010b03010e0403050702060d0c020c0a0905010810021b06040605150105090114030601030608061003 93
    0x70006640c03a200012420388451007230200042c4c0520100f1203401e501e000a1002230803d43d00090340741e0361413010950b03940141c1d100e80798540004c102041940394854065904c00c0d00c10b0790820a191181d03403485042e882c140221400740e000080e83c00c801c207004000c074045003500718680403143d2503c1c01e4020688122804680c0c027007250300c07000c10f02c11401400758411241a8101c403a06060070f020048034003802c016402d80c00c51099420000102c1d817188035541c0103442c000c405a107180d042c204090304501c01a448000c8014080004001c10300304840031541140d030520b1310641d100510700018105010310040d60966602c0d001a1500491f000520301540210940c1c01079a91039840c28400220350091041400e030341c108903114500308440303078000c00e0810916051801d550420141017071400204a8049038856036031000d100081c41914881080100b09203021403400140c3d41c0020410007034904000905440480030906a80c025000311000e4280101254500d14280910107110b04251000b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 14266139 1250 14264889 14264891
    0x207030905060a120b0a0b0d02030f06010c0c0b07020f03100605040f02040e0103020904020102030f0301060206010f0e07020a030809071205030702040b010306031a190507030e010e0c13090c0308030403090801 91
    0x1001030075003840400e54680b020541c8031301c0240808049014040d140034034007a6800104940085600c521072005130041240260006881e0301c0c002d1004a41003001810f00350502c6250f88035100000c1621050300306452074408402d41751803680c03000c5040c0840b041c66850f410b02800b0821030492901c1d90205040343c07003c03101400107010340a20380d0100d04c140c1c0690154a00c02200500c0581010201140c02c03034818030449107000c6803114002c1c4d40c0d40082c1c2014006801c814010400742241d143c4400260200078514050b034142418003a544000040c2d00405100d038000c00500b01c06810b1001000030441850280c0101510341742c83d540726400100120300c82c528100d120030440d44288a2a01640d85c002425440101c0c07101c006041c5100007490001d01200c40c0c0d00d43d4101441600849004860944021502d002400605801d440d0510019900c07a401940ca110302c81d5106140180400d12001002800c41220f0034900302d5885c4581020707000c45000000c1c40105544071808030210761001d80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 14267389 1250 14266139 14266157
    0x16060e1c080601090905060f0f03030c0a1a010b131e1502070509010e0103020a17160b0309010f110f0f040510080906010f08030702040b01021905030d0c1e18030f06020703 75
    0xd017142102c03c15a03a55802030816080d10010342003201c0c2d003030710b5010005c080342d0030410440358040c078140941c0000c98071140d050140d10f209405c86514640503100001c641400d1601505440080080a1164586050280f84a007140c0501b840300c42010304076900c0d10401403001d041001e503a4a486200b407074040c02a41d000000d0b210400500395042e240d00030003141c0c00600c2c0040010f8106000e540d80042800740c4014100c00d0454990007038020a1522400d035102c1c5482c0b4062401c4540c4581141074071800d0010076040703051600129200092003c141c0c81d240c03c0051a00d0603a8029a000b01c0e80000f25041140030700380d003058102e445584004122820340c3c0c3c1390812030401202920940f100342e40305008040040c035258216a502840c184119040c1203503403001c1002c8682e400c1416034451308005180207584080c1d005458a403101405e0400d018880081c000c03030f12107044040316082041c0c40900a031410b4110920000451300440101001401c5081583c02513010407422408620455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 14268639 1250 14267389 14267399
    0x608070915092004030308010303030c02010c020c0613090501080a0c05030d0503010902070f05030d0c021606021c09080607020106080105010504050c030406050a020f0f0909070516060e1c08060109 86
    0x100074007021200d25a0a40d040515104520010380303540d0b030070b01c40c181c034807201e00208942c0c011004e000190b00075990b854055146003005821900d08090800441e41407120316281c0d40c1c5c0003d0510050401924665a075012901043c1034900007900031110f10b5052500010340700c540040c0608005010304000800d503661101015924000e550040703010920502c01000304004c40d9010f04032583c014054003c511016030307142e900b140e00034401103200f1503503410680020759040001e00102c0b4288180301c00903508140010b903940c0000140c241c45a00076001c04181e0074441d01060700100403410031603106041c6900080e0281c101c50180d00301701c0d03280c00700000b042c1ca01070080901400c50281d01c2403175038885840d00b002a0000a05500e0401c0d0204aa400d980030404006c046602c00c2c0009543c44145460800c911081c02500b1107080080c10700a4425800744202d005450302e9024200241140100c40c016040002e084c113503841140d080b03030a00500036001482240302e44000d03610307410321640703034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 14269889 1250 14268639 14268641
    0x15050906060a1d030c04020a0507062009090c0d090f0b070206010e0103020d0303091217010b03041a04030e09010609080f01050405030f090f0a1202030f010903021506060909070306080709 82
    0x120307801c0b00040c0d1054200c0e122469503529011071004040d0039a00c800ba491400302e03050f81d11101c002000608005a540c0510409200d10b0040680340f03100290420550100201c4a0142d03802035031286030300340c0204070f00171080c5048a0740e0f8080341ca010321174101c1c10b0400e070000f06001042590f240f2002c41c00a240707144040360580c107036201000310703600e02e900390780900c0a01085032208400345680c41c95003001185036450542401d0940390344442440e0900f10700e00b00b18403010781c42a00790410500900001403116400c10780c1049002151050b20b55540c00e0840740203040c0250250001312a0002245590307014188206503400001140c0341c071443c0c1c5800a080380d10449015110fa042480440781e5100b0040040c5044070005040c0d031800e0006100050700c807450b50784138a841550140c98002141402d010881252034104000c0011880c0c58501944500080c0001d0742c0682c201000a100b5941c1e000540d0601000640040c095261144002c2c004080318000c80441d84203030000018a0a05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 14271139 1250 14269889 14269897
    0x60206100608010e04030215010806190e0307020f0a0b030f04020901050d03090302060f0903060a02040f060206040b0a0203061201090b040303060f052220090112180b0402060d1505090606 82
    0x1c15603802200340e190400d000d0111001810480440c0110042100e00e11801200079000e03102d00f1000d4500380c00e00605203441c0100e00c4401e41e1019050010b440b103240b034003200b81c0d8031580c0c0540300400d099541d040001c40207440b54100410707801c00030060059004006814912843c4203640e40100f50340c981c4104030161500c10f600400050b040c02c020320050610f01c010340b12940c544a0031904100e11600000d050400c122040f48070381e580400d04004e1a0301c0e12001200070a6180060034080c20251201c18010400401c4841255000000728007651281654110090f1000c40200048034141c03421a1103030b003064405900007030500c0408034401b8002040e030012158003d14081c1241c00341006c100e114404801210b061030340e9184c203050060101e19102d10410441843c060b641c10501002400018500390501c49103840c14004146002c19030f000c1c801030f0f58116000b01501c0c3ea4501c0058914803e03143c5d4a41050305000c026110105400110300070341d00b04940c41e5840d5034492041c040140a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 14272389 1250 14271139 14271149
    0x9020405060d2001030f3201050109090c1206030b04020a27050603010b030307050303010306060614090d15150303030605040c08180a1b140a0503100c12050c0406020610 74
    0x400f02112980d005403064603840016818100402d0121a80c00304600719550440c2c4800c541d00c140413003400b00b420b001c121a0000c206104000180e50400c00024841c0440b4001d0322841d07030352110843d052502403098060346030583e00d0240702540c1c0300c0c03030074107410784054804901030a254400424248416100004903c40175511b2100180003d24000040c14028007041e405550b1030300003010a440520042c901e06020300b00455030b81d455841e0003422a80c455110f542004420500b100e5038013942000c4800341c0600300d80780d6040704442e0034481000c80b540001d41c00c1c2c244c9000c424100b22851600040122800f0351020055103a454090100743d8880c2803103000003c0d8088002a130700c0c1c9440000c0c10500310342c6c030f044602c040c003e50303100c040d448200c000f41d41641c015007800304032031000ca442c6940082001d03520303101014030b4400441c0d0740d03030035054024210685a180c40c1c07821034800d66507108030fa042808140300d14184000203c0d141e52050094134010f000b036500049000940e6105403013155 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 14273639 1250 14272389 14272403
    0x10e0103090519020609030a03030c081501090603020304060b0d03090602070501020307080702100207030602030a0204050a06170a050601050904060e011d01030b0c0904090605040308100f140f0f0603010909020405060d 95
    0x1883c3c0c40c9440350740d03220858040380c0c405003c0c0404a000e40b800c0240b603400500c2a100010720203580c0f003010300781c0300340100900400d2005440f142e40590707203e064002281c3c1c0c64200582c8a032124548440039001c11990b864000c4600c100c10020f059000b10644101c8032107801b40d4030141d80365030049880344600b0360007600400040000c080182004491600109030038030583e000644c8a50f81d10041e42d10950342c1d5681c00741c01013400d20062400c001c0b010000e14007401e04c0c0120319000d06151404100c0140f100c5034255840d0005409a4080c10403071381d0304a1300420030010140c4a00a05085103000c0c040c41d10580010580901d040550b009a00e05072900301d1000c1d0700e29680c0a0030b030003003a0b000044558016480c0d440e080002450380c01000d0081c1c1c82600c130a592468504501000c401c607662110703c0d08402a0000c102041407807100340703420f800a561f048150101c0d80b000c01c5800c04a6055181c1116000000240e00350703842d88070341d960034402c40381482551200002c10a039000501d10162001b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 14274889 1250 14273639 14273653
    0x30306060703020c03070603060e06040b01080f041403070b0108060c0a051206030a0b01090e0c01030c0e04090503040f030503190504030c12020d0203030d09110d03091e03080d02040302010e01030905 87
    0x34601040940846482441200c1a0391180c1022030f0070140079070b000c040429119074007400a0080c110310140c0c080c2043c0c600304140c8a44900080c24040c000d00702c6062003500700e0201d828805c600e00c21000226640c4100e0760381d12202d15060181c074100f4070502e40140903100c0071401284030001100c68008940d56014207010010302e5030392040034007424582d8948240340300b0301c0002d141552400c1c002c09d0155400169441d290750ac040c288901d039880e01e41018034120240344001c1d0044500000340c04c050b0780014003209945401403445c891034028511500307040000200b0013600000a00c20100441003000038502545001c0c4c409002d50702000b003000c0c503d0407003440011040d016031005140000c0c94409100c1450300468215404403684481180e00c480507002446020316a20400074415200b06010840c02e860080c050000c2d4050402000302c0312481d000e5580b41460520b0146401c002c00523510444021158000d5001d480120b021440c1581004403660081c0700d00b24045402c00050052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 14276139 1250 14274889 14274901
    0x105010f050102150a1401090e0114010e01090b0a05090903070203070b0c0607110313080c0103060b09030a0206030405030f0c1e0105040b010603020f0d020f0a18060507060b1201050415050108010e0303 88
    0xb058600a0001c440c16503203440d101b40c140c041c0041140203014580d00040c0c00c1034052030f01c07825200340015404036006624010014140300681c0755044943c01c500005103c2107240005a06082d07a1b440668803038400d034248410918003200074400a4402c400320f03806566103131040086401003401000e0a0780195000600160050610014000b0302c442035070310b024186196081040310b943c00030f10b2141d00c0520100340c80c1d600341c42214060140000c00601b4407450000081d1b9449150310024080d1801102040c1080b030204251004049907410150700c81c10300400e056179500b81c105094a80b0035822421344080c1c00c045c400d5600031500702c0f05802803a0f08000041d07001e54811a01c421403407500300701125180c205807002d00345100a0101140e1703a207041c2000101034444807601c800c22248007050030084581c00a00311221203500480200f445400c82000443c1a0704003007100c0010350801d01001300f041314020002c095583c407a082000310341d80300c140a600325000801c040c02c06038806c01c04100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 14277389 1250 14276139 14276173
    0x9060e040803071803050d020d020105010609080307020402070503040f08010e0d030c02060711030d060b03090705010302040e071b08031518090a031b0c060c11010314070302070606090606110105010f050102 90
    0x250300c6400c549030042c403903560b9546c42d160141900001c2d0041c5c02121201c481158207024441c01090580b17095081141004040740d144c0c440d18074000c0c03003203038005030382810072105009075030060007a1a0060f01e4a81c0c1e824042e0b010f802c285003c0340207030090090450707405010f845840303d011160783c0101a2a5101c01081c2c40c0c006240b0100d001c94070007801191a01c0c00c02e8082c800c090450701c81016103d08011101510700b89094010b5814140148420301c640d100c0c10347c196034844201c1c984004401d5000b49248030400e80d180c000781c40003a0020030000074840d10103012400600a13184400d5400c24900130301031844c810b4441d40c006411042010000c42d120320811403850300c04081c24165000c983d0740b06400d0100f1907200c240070610404658050000c5040352400c070400a007020b000d130901058042084242c0180040285030740810b01d0b106020741548200c01800c00d078801009a540c03904030291075101c648140315020743c00c040011a07400e5040004900b20765046e0001c1042c0300030581240d07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 14278639 1250 14277389 14277407
    0x18010b0301020f03270615030708070302150307030207020301020d02041401030e030a0f0201021603020606030607031104090207060902041103010f080f070308030c0d150e0108031c0b150403060609060e04080307 92
    0x607402d0340c14850b81c0403410605000e4140500f07d2040c10810b001080b50505040078421303403080d880f94201c18020400740c0c43d014030740802a90540c074200c0d905c2d9194902507000b4003c51001a4156101042440e0034000c168010001e039103200540610b44180000114261200c0e40342c0c120300c40c0c20501028010300e0043c000c44e40101d0942c00054180031b00800780c801d1480c0401400c0c0d006034030540500205060034000b40b41c001e082842c05005890458080b0380c6d00d841548920388055030f0003c0c0010500410b9400111240d038024024400c0350080c1a08140e580c0080c0a03916100542d50800030f80e0107000034025081c4460200541019032550300c5250322500000c3c04415400d400f0402d0f03c0c0225890301c6100c0d00356220194150203142130011143c0a00310582200c24aa40104160340091280050081c004500c0c0000412014641404994a0b0200c0c0700e454108400114003c400c000c0907820910958101075400c204155031080301044918040c0e50103440750383c0820105950b00d100e05244 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 14279889 1250 14278639 14278681
    0x20c0111150f010e010e0f0103021c20010801060207030201091401110a0602030a110304051c0212120402030c0102010603020d030315030b19060e01060210020705010f020318010b0301020f03 83
    0xe900c50a400c501c0620a09400310350110101ca18000103102c0c0304c40a0842901415428150030706a2402c10800341a00d02c060101034400c0390005101d05c101d41e01d1881502800f070384054078104102080a0b900060781c00000c2c460301040c1c1640000c0740e0035200080a030102d0750140e640308842454550b130300080d10780417180030303040056455680421001c1044003075981c500c038400040c0e481c54241c080c030088610366058926616020800d100102c1d5001070503200804019180c0e406019a0722800c0e1f25240941442440210001c16a180e81d021030704d40c443d11840c000d4041e038030500403c1e07004a01302d558600000352b011480f142c800c80800e00c2940054040a4503030240078a054480d11a03002070001221323205a1a020080c1100c03042425008520080001d581000165410181c029480b40c1e4030081c0d0000c030660106091003130040c2500040c4140d40000411075580c01e000030b00013004c50344100128a1503080020f07282c040e0905108460048101903d41070442c0c0b40d25498502c0c4800190036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 14281139 1250 14279889 14279893
    0x61603050904090212033f09100e1b04050c0307050a020a020a0b0714010605030309040f06030b0403080f070e0a05010e0402120c0301080d0e03030a0302030601021905071d0601020c0111 81
    0x43e02d001170310b034000c0f840f8444418500440d00d0701d0714085911102130840c1701c110140c1c0d190028000003c01e1008480300e91074440015032185a0761800c0081c5061030f40300e011030840d400e15144035452180844c00c1c01c03403221850a68200184c4400500084d103009540d0400c80040810010f5103061103003015017100d078102e1040c1e494a6205e0380024070b1000d500d421061401c1c000060b1001082a04041201076202680c024450146028002500c038000c40071803500840e1680900e10b070a41250f40580b0282d5441407008130582030509008200b1102102d108000800500c040392515000d01039600e4a580020007600c0304c03130b08020045071395160034458150081d0b001d112256001c5e1401840d02d11035481022000d44030362404030b040c1d1400340e50700c4900c010712100400503121601c021048441d1240541005603072034a8080041307103000d543c5106440c19601e0410040200302010820b11300321072203240c1032a00c0b040700c00202142a0000d48145000d42d010483d10308003940903ea101d8860030182e02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 14282389 1250 14281139 14281151
    0x71a0a060b03040b01050f0a03060501080304060813020306070807050d090602090108060105180d030c0b090109031d010804060b0303040807150210050705070b070203090a0f030b010602010203010b0d0f061203020f010b061603050904 101
    0x24903002072f2007003030f00400407640010800f48140c561041e2540d5125203e4801003083c94190b8010a484600241140c02000400e50000d810680103100b11030089e4540b0300b04200300140c1c0d0501c00c00035000044c4103800183c4500c045202c03580316405407540b2002021317025141400810401401000c0844104c0c00d010100d030880c804034145c5425144128103c80002c00c01d01740d03d00d001007035041600035040c4448409111118566407100043c0d42c050340c405000551012000002440c50080e17500102262080742c3e4003051080441000c201d90312115001c40b04106081d4400900303460b401c0303411400041c41449450041864038042a420012500581c0d04c0d040640780440d071040c41c0d40c0c1088a00c000041c10400420500b020b00038010840e0348021402c550501144080c90b102d0340c0f6840220a8446000040d034112641c4100c004044010340c00c924540303140340180d190158490261003075481d09400180c5820007900f280d110b41c401c03039401050711611b07035025100341d08581c2c2c4150700303e42d40300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 14283639 1250 14282389 14282393
    0xe010f020a0c0203060619050d050709060303050a171605130302100507020a0f080a1b08030310080c04050402030303180111030c0705061b07020108040305071a0a060b03040b01050f0a03 81
    0x4401084208042d507500d00740145a030050602d80003011b8000d07401903035454486a40400152920f005032141250600a5040f8034140245040c0c05501700c40c44062410600000300f64208005245100c07454681000412120706c00ca003504004546000a840450582c840a544201c00030b0205295500f001c0f0400c0b52a0703008940c100c1c00d20000500861b00000d9248198541090a1340c002c1c00040e1000d1030a034180030300b854645245030402483d0344042e91800381085588100c0c3d902030150281100d45900e00180410399102c114401c0742c0490080210200c081d003001e008107446560007600540ca180c81320304a080e800c0c0401038007500c481d540c0d01d00084c15084460000c6025040c1002c41d5a220070060a00c0c60829401820104181d0000064038040c450840c0540341081c1d02400c080d582a40c950509035168801d42c0c030020070301c914a4541e40c00b0001c56200c4c05020f5030090307004002c100c0c0c60b41c205a1b6544015034028010507416001000320340341504030241c0d040f00282100030065501d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 14284889 1250 14283639 14283641
    0x10020703051905030702010b0603011202060a020f011103010f080303070f05090d05030c010903020c12060f07090905040303060e0c0703120203040c17030903012a0e03011b0207050907030608030307030e010f 90
    0x203008050004030000244800c5030b509000d0170702608c030101d4859196500d0f040142c142000d00040080c0645c00100c3c948420034000c3c07000b26040c5507804002d11004502c909074881e258400d00a42400100800d4003150301240001038a1181155490748040c220507501c042c2d489820000c2aa40d06c25007120308000015802e0014120a0b82007200100742245d041c038000e07040c071840008240c011010b18001d81d0f4103000004580e900100344401d003290341c0d04c4000c4101e461004680103000101d04103802e01042690583c850340407181c0c100621141600c0d200d5048400303100e01107010b000580e07622a040c25280c001c1d8020750f00a0710401a4035000e5079a40e08000b110410300551108680022462115a040a00661000c0340c0c0c80040344a0320141845605801c3c0d221036114000c01014403485202c4d0b4409510402c0d8048002814400c00407820780300956a070080e01449004001032400708910321b0190290700306460440340954110f94a4500071001000d00c5032060b2070540d03d0740710480c00c00411b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 14286139 1250 14284889 14284927
    0xa0909080306040506090f04080903031902160b0a2c0405070c0c050a15080603010905060115030605190611010b090109060815160c020112050114010f09081002070305 73
    0x440c015554480c685041080308942000300102d000e40440740412243d040c0b541607182d031040e80189107603261000c03600801e00d14010a224013412680600c812462140c00196080140903a03180740130016032035911500c854051700720b005010500d0700ca4010941c0004174002489418038440002404003c180000e0031b0f21000d903a43c0c00801c0912032810144212012650301500080e06d600c807500380b41003015044950705103588410404601c02141c00d40e502900155241c40d0407404403840b5584460208078602286200740c00031906e0010001941d040030300d00083c2d40ca0050f0808036005203415000d5802400203a640b4942d95610008190745a8500040a0282c02c080d280040c08c5800c2524603071810300460081c8420211400c100505c14551018449000c2d03103c0c0343c011003028240c401602da103030f0b207101348040040c00d08002062050307000f4503500034203100766600c030f041d54a2a03800f61100b0880f0300030b44400390040b4500d00740252254000381000d620900e8501d250511039100040303050a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 14287389 1250 14286139 14286143
    0x20708040f060f0c03020a020105030a15180c0903020a030303020a1103040603020a1202161b05090a0504210503040605060105070501021308070b090315041106040312020607140909060a0909 83
    0x811803001e011030341c3d00c40c101200200e50360a10b401015603e84000e982d580c42584024100080040056207080154012600c00c0c018000002e00c855262140410101040058004994540b8850314043c40c804c030801c0b03044a802078036400349a070454800710007a500c00440ca4084c090703a090300c080d207000100300500c0204807079500161075084807400104000e40c100003a8005d5801440a006400500c501c21210a42d00c20210805a034090005a1a40c0c0c5160300c0301c0c0d407000c20303242000b8000340b060300500c0c0f2840c42100400d40041c815070702c12080603000145500002c1c010f10000b00007030b51903846160408014104941081034543e181801d903480103e40801c00c4141e60310402400408018000181892021040c1030080d440b010a5035101801006407100860801140c14803030340404030210643c002d0300542e80c0329201e0500a600d503994100c0000140324245c00607000b81c0c4101076228020442c3d680003450101c60300304104242d00040c03d2942c1c03041c10001c00241504032403142c544124 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 14288639 1250 14287389 14287409
    0xd02010302070b07050415140910030b04020703031d1911040b060406020f06010e1308030c0403060e0303010f08011802010806030c030f010606120b01020c01080c04030606030b01030213060302090610020102070804 93
    0x61f0074440207101c0b07501110200007d1156034206000600344050655040d0181560200451422540d040300509444000310350443c1c030010f00703641856030581210030040d88032a528080b5481c603d8407140c1d6842507a605103042d03154480800000340ca8642c01c85006000100081841405000000c500d94041d92000001d070380b108240c2c941311503090042600401240c00900724501e0800c10f20b484030394104c0d400038105c1000000013100c0004480030340d0051a00080100005034166010990b01c0d4000e0042524451000e4800a42a181401000203000800344036885107a055401500c0c82c2102404259040c0141003100c1d0b11360300d00f00000781d405411400082003880c03502c5c5000c1c20701e105034101100300b9814000c280080b80d800003204601d80600b0310f0545403d0303a8500c8850700a02a5407c003c05007401c0010000038018001c84880c1a24021900500101000403d20701100c68604c8000e401030b00540c009006d62a011b613071007050b00f00c4c034000903103008002d1380d0701603407075005420031b030840 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 14289889 1250 14288639 14288647
    0x30403020d08011a0c010f06080307020910051c030c050d0302040f0b0309030a110304080312040209070804050604021203120108010617070803030f04020607020d03020703060e0d050403020d02010302070b0705 91
    0x1265040054401002041c02c00b04095410038103040c450010b80b03a191100340741c000444940c00c400c00d50210216035a038107000c0100360303240d1032281e88951120809a10800c8080c0108039017800715102d881c00c4541c0148081035041c0500054051090407100030340500098806031400f150341807000162400740e5540040e80c0e00d00b4014804424402030300007818284092081250010000045980ca54014217103240140c1c10428624034520903508408200d020110b85222000850100a4040d9108540005c0d41d607070744400841d60400b040740c018201e940814081409400d005000d18014800074096030f10f0802600d1108100d5007080c1c0c0594541e030364818040090300c101c081c03401096184200074001a61428101035a640000b50400e0320071400d02d000f080840d46d4050407601e0056019160103d8104241000380d2118000d00c410707541641040c0004148010114500700c0c2c1390060f88405c1d041c207085400b07111034820380071000c0381415800c104440200307501c4078840713100c1c81c00380d540d00d651 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 14291139 1250 14289889 14289893
    0xc02150405181006030b0105070803060d0503040803071a070210150909050303090607080c0a260a02090102010c02010209030a0f0c05041404030e0102010605180613050a0c03110a2705060307050304 86
    0x780c050b280c4c000c90405150071031408207680c1c0701007207980c00707a0080d8416869444050000c4c4a1041d0044001c045200004000580f04400b001800d0080d00130000d070300d0b0524000c0820b0001c0c0204070703181c20060700004120690706030300b80e028440c030a0101e039460300f149443d03443c2e540c21111160003d841b158400301c01c000000008025981c0d00038000d01c2c0c000014204400c0d10001400342e00901410b000205103041c040c2e80d089501e50041040c40c0c01c24120f00e00300b40d2010002036001803a0140154240904003a10307500500032503880b0301000d002450180074940b5084804507000108480441003604000381d03607981d50103105580c40803203c3c070307644a0905150142c1000380200d102410369040c4a0204100e9903081180842c01c034112010740321070b44e12100069a2002c11030000d04a00e80341500b4410b035400c103030b0302100746490b168a080000e804401c00b10380460090b9103001e0001280c015504600740d8134056250401c80d50751303c0c0614403035143d80c00500c0c1c540044030210000741d404820081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 14292389 1250 14291139 14291161
    0xf0602070305012910020a12030207030e01020607021b04060803040b031f050a0905090c04090b0105010e0402070c090b0a09020c060703230610020a0218160f0c0215040518 75
    0x2004007400090a110313001d480090700f00100d10380280e1343c41a402d088900030035030b00a02c022000745070302c280d5005520300792890140c025045454242d00062580300d0740c1d4069400042c0040c01441e65800a00c4a40444100c040d040313540b0f401d03041c0d0402d45079a00002c54110800c0070b407001d020b08040d0b15842c0c2c40c225807401103540341c410483e407030403444080810540c0c54402158050f02c00b1400c022030306a0b14100b001d450f10f0a01e11504d07401c1440d1903005400d01400b4036510341030390030036603c4408000c0d0020030807041e40107099011340201d02c8100c1c10070a0301c1803644034109485010705100ca05940e5019440220f80001c001616603400140c10800100c2d494410181401241c0011a1644000d40c00c000c508003001821140034503040b40600351098000c006c00d40c601a401801c0c502400710001c0041178842065620707881440018440350b02e0070740219080d003094549a901c1584d00101c0742c0030000d03448171603615103c12880030000410191281514440411041c440c6507129080c0126426 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 14293639 1250 14292389 14292401
    0x9010e010b011e08151804030305010503030a020c04090c03020306010306022a0606040b01090515040806060102060403020d08130b0a020a0210020c0304120203030c33100e100f060207030501 83
    0xc0e041142084101092103801aa0804054040e1404c2c404640d5400320640c400813420004982c080204006100d00600844040d40714620a6038140602e03640c0e0014503a5034003d000c0d4010240c0c0040c50503055504042d0700c03600035a4000e0203030869003603903900402c0c1803001c207810549840d900010b11554086040281c440d00690141e03c1c00100b200241d1135903147d08019100c80e114544a40302070140e1381c0300e400400040c0c45c0003000d0385000100d0079a000078a90040c8900390840c0200b60001c0e82642c0007103440c0e886aa0150003900f610702e0f511004440600009007061400b0200c50651400b28189480d040d101c0d1161600c010390b42c000105029140c0140d80b0154000d2500400204606500201c265070403100c42406400155116200180c110700404000c42006d2050b9034070003000b01040c1090700000704859000c00e00c040312150343c903005100202c80343c0c403070496080000c0040b01d1400c01803a6100748910ba03ca02d2003502da071003400b002102c6620034001603000c02010b00900c0f0f4288111 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 14294889 1250 14293639 14293661
    0x5040e190c02100e060402060d020903100f020418090528050105010e01030b09070315020d0e030c07051302090a05010c022706040e01051006050703090b03010303080f0109020901020a1b0b0309010e01 87
    0x5c10607450550300040785441080311810f44079402007884111501d003042494002121200207020040d609040e0000a40040c031803914034102d4801c450520100501c070700140c280e08040a080c0078010083e8104841d00004929640440b40211500110750280700e00e074041c00c1c0106d030100595145040108040001425101c10358100210400005001800b026980440000c0240e120b03004620100001c1410301d807402c043d40000540c1c0302110b200400c416040d02c2c003c54244070307100d4a01424100320b01030442440d0704202200703028020b960050001103600d520050003c487e0f0b100c0851a107650440007034610706400c1010080c0691450035002e00d00410b800e440003001146443c11002d06208280d01c80c03c000d01200040c2881418801c0340322101800441641a82e05d5940c1d20b40142200d03c201e40c10240d81030810300100d40c02d0814000c8aa451030142c0c0204840c40f02500d519005441174036440ca83e039045100d0001d03500070484060341c0b2606c2d0000002550007102400a400c1d20903000c40e03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 14296139 1250 14294889 14294893
    0x8011b02060906011a040506070606080706050a02030304030309020d02040f052401090323030a110c010e09061e03010c0e0301050a0501030b070309050325060b1005040e190c02100e 79
    0x2000b01a00700000d54604603207001d5901e05040803810421401d510941c0c02a0703400040c005040410b100c00c0da080b03481255030080407207814903690308003203807680151489240160006c102180100788650824802c00b40014140707076019000f6800102110340c40520b10b10250344840401010301200b010780c0c013458104015400690b514040024800e60550100034400d02c0d503107600d0000e60062091003814241542d0440340d880b0b01c0c60710060021711008035251050b01c035583d44200a9442179079030b01c00e140b00161030020386d03455041c01c00c038000090706809100c00b01420681040d6a4013409007404c0c0000341c0e1603180d4a4003052081c9400c0d9107006082c1c4084505200042000030304e0700d921140e00988919000032482000d01e002c0b802c1d441400d00018035a090481b20300b5544005008080c84140b08200c204405001d00082c0001c28440b8418840890010301080202c644400c03041030340400041d1a9000041d41e90501104444031400c4250051b40800305904000740701d807155414268030040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 14297389 1250 14296139 14296141
    0x609060613050402180613032a0e0703090503130306050a060303081803041e050111011a13060503030f03010f08060103081c0902030a030f140304080702090601050f0408011b0206 78
    0xd101c40041225124150103650b0001d030503034034400e610094145800c00140085d17a06d10080c03400c5880c2e092140400d480c807051030554402910350003001040280b00c2d00022980d00741c642021f41105c004001c20013000d0503118140440003807030130700080204a0300e000d50524041d04500b0910112a001000c2181039490308030140301007a00241015407201d001c0300c00001007003007a0105030450290f07500c9100740510311614000c0340c018070400a42611004c1c0c5e80c040f810146100500d081c1e502c4924a4a4000c00080d860036007420810004004420040d41c08552039503100b0100b8a140e0254241010304c14000c80188481303040304860303500400c01300e8010010740d410340c0c8031001c5074072546d07102504015401c494000c4038945c68107e1111150002e064600c480c866040c0a0900c5408010003c001003c0340082c898100c86d9000362030190340c004002c2820304109a09108100b04007034809030600038144000b11041003d00d008202411400001081580c3d05900c1c2c0e0038181e0340605142e0554100c3c00c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 14298639 1250 14297389 14297407
    0x1060501230306010512070906030c0c0210050904060f080105090c0d03080c13030506040609020108070207030809040911031b0a0501030207020609041a040908090306090303070507030e130606020606090606 90
    0x485009007441090344075aaa10740000686240c4203040360700000d2030080d4104080f9a8004980b03004480150314180508981030408541e55054480025400180719015001c0f40d80714a018049495020b030001400b580c8031940c0b01030002d0150310044040e91107074200840d4440078071403903803050007d403101e8400c0210303640d014204400041144108071404100641c100551a030302000468000c0d0541d916814903042c204041c10074031006078045031704c940c04524190b200203050000c407078221034200d04003118502000094a0000c0c4260b482103021102200c146e0380a000300c0600d85c41304c4000410107800e84082c80140e08859001906041c8141300e04e8002d61184800c491862030704880014146001240410282d25214019070300700d071a0070801c800700018500104440c1d9821812100c841c2d036603842485c0d4034401111000b0024005000303080000c1c3c051080400442030080040160324098a0fa0404607030140e480030005078442010301945003080784134103402000039124685040842 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 14299889 1250 14298639 14298677
    0x12030d0902030d0201290411070503070b1b0a08090106081516020d1b0c090606030e0105010504020c0c100306050d06020d05090d140708090d0602030108060108011e0b010219031101060501 82
    0xf5519036491510303042610001e541d80303601140190000e08c24280e102c43c82410070581c0d03900100c804840c540806400300b91081203212000403111000740d10740346000c1500c2012513131890050b1510501c3d44d02c1e500003013581903050124024941c44901c0c4140e0600d05105542003c130a40790b525419500300c52503111026038840d0b1800c1001075444012403900880346450601038800e50702102503640392440101d2000d5058001924003005e40000740070503600c03003003004100e115041d102400e41d80558560400b5007401c0c0080600802681000642c2c96a82d1000c02e01891051004803002580001c5130903400c85540f040541140c00d10000f40301a921088020b003040000c5d41c90b089209502180c02c004010341801200c1c0c1c0084081c1141520034010714000000e500f00f07006885007802a0400882e02240500c0b42d43c000101c02c2c0800b0300040b107100800401000751603503481c118010180007200c0031421000e50407203e0b2080d590003408003004401e141c2110b4081c0c014034100200a00034807051480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 14301139 1250 14299889 14299931
    0x2030910030603051b030f0d031a01080108100902060403060501031104060e0403080601200a0809040e0604170a0c020402070b070e010507020603190204080f0a03030606090503060a090212030d0902030d0201 90
    0x402e100c1710305607400300000203140000703030b1741060921b10030b94405c0c006080d8940c01442054044c3c182c108880c0d00c448005440840b82409102c50300d41c4503180d0f04c0310218444d0010318800c1c0c005062103107899160785501060715000d0b0000d64201810300c2ca942468242803180400401030505100034034209035800800501c4081c1501c1c0c100110225060b0a18240022070512607410302e0840c0c0760b80304d26180c04d0240750400c090041c80f40e85040b0000702d4131000461070780e104640c0208013800c038410422583c1c205421650f683c104125402c00d0440041e126880103100090107011402d81074036000e007005200c9071031401c010b410010300703102d24001070300c07210140ca402510307004c0c54030341001a0342a820028091544510355501c111385250300000000303d001c1905500036070303091001c2519001c1c20790b0b44500034170650343c26600c070b0000203030740180e103a115494280c0b0082881e001890040a2685103802c07208480000320b6a070303070703009045140421001c90241d01c507000900c0308031a81d011500190790 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 14302389 1250 14301139 14301163
    0x1e02030708040f0c0801060e040b0c0f040b0a17070c02040b041808030402190e0403020c0103020403030905010305060a0e011706090a03090512160905060f010c080901031a100203091003060305 84
    0x3d800308001005240364203d400740c06043c008000c82d65540c04000391101c070035102070b1081c2450ba800b0800441203441180d602c020844400d529140c58182c05108076400407000c1820071012040b10a00841c03042038590044015503100004010035004000440c0c60307001855216500e410040c4590b1405012007040c03494100070201e403641d50310300210b0031820404100b008141e01384c0038007007041140d540c1100e0099029900300ca00c1d0003003140c01034040b17100c0c502010f40800c40042e0100215032094000700c0c2c1c0910090b002d004260307610202144030203820303040000143c110707501d0245003183c10440b4a070b003e00a0340041c60b02c40201d440c040c203c0f12441c003d0038040e41d00c0400340c0782d5049007080591150612018440c121075503407003a102c0100000d4400503c108400d10200000b07620440c44141c9244e0408060b84c640000e007001540104100c07000c0c505460540d80030a50183d81d800c404010b10b1895401443d41c0b05d48000400294a2000c1c203020180352800707909101040b00041c15440c510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 14303639 1250 14302389 14302403
    0x603060718030506040b091501030b1902090d080406020d050310030b04080f0a080403090b030f01062709020901021e120703050d1a030705270a0b0a06031e0203070804 73
    0x6507021007901590058002400a10404040c8070400603c8142c0d03900c1090302c3c206640d844040c0d0346000341455000e00c4040e1440ca103030004214020700e50075250401da15203d10042c5000110400304000311503180050356a08004070701080b48940611485c1d10496486c9820780c42c40c84c0c103d0468405840e24007014150070742d4980024108040c50048502e402c24141100c0d0b1502103401c0000c0c40301404850880c0002e80d4858001481c2d605002078900070141171800031001e81c2400300031215215054542141030b001c00c40d102c0b48500035400500083c00801d003025a48542c54070000e49403201c00400e00200c501c111039028055080410a2051407a0500001b903454400d824100c505001d0280b83c1c1450b145002c031031120040d0440070a114000e029000da900035940c500411500f4440d03003402010201c003000d40f81c50b0300800e145059501508480c000989101228081085482c0a82010340400d50b160103120311080054018588221301100a520310320713203500d004181c080e018000030450 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 14304889 1250 14303639 14303657
    0x1060f060815010207030803010e01050312040608060f03190b0f2208030705070605011202040b03011b0305040503070803010623040501050a050306040603080309010603170405030c0607030311030a020a1706030607 93
    0x42c0c1c13003445010025078008018a4895071111418010203c0a20640703200f44100606288544c66500c1500d08a852507110b0070150741d41c0b0700502600540d85100c55034103000312034800303640c906030b60b03c80007030386019044400071403602407800b42c03425801038441d0301e9045107502e5603030300407004501c54001c081d13010094035100d0711161004e07503c1e03016401004021a0070321001091890f5115448904d06000f01d41c2030092195040c00d040c03c80c0c041141c4d20549802c44021101414007035000a0703003041c402d40440e032030f081441e00c406180e90802e802038000101c0c160030703040c11000851010010350700501e03912481c0500d006c00286c003a10803464060b00b40710011000641d65980d59000c2c500554020454603a2840c11040c5240241024081150250f0395188840c46841c001001c0c6d9080d18406001054030045040c00c10a5a070443c0da022000c154881c0da941d2110450b40c4099801252508030141e20b034042c615001d00b4a82010707141000300c0b00c11504110641d07600046c0c00d50081d806007012051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 14306139 1250 14304889 14304931
    0x106081e1e0c01050708120103060f1514060f091003020703090b03090a03110a0210110d0c0519150606080708090a0507170102042102010806030a0b0703110c16030501060f0608 77
    0x705014030040c650790a1f0802c0000003d020047d001544c060b00c424008003e40060b031510704c929004240200e0100e401061710005403030a165008005060308084d2150070100005c001803e440340c54100c07900025008a2010205a0060f4a1001134507203803031418103501c0c3c00001c03940c1d100c401d10000f4081100031010390b0b54586091005414207030300540288280c80785104083e100040b08041d54803a07110b8501141c1e841441203c0414510303178040040d282e03613240744c1c000f0f0000c0c0303088201c00d84405144003003802c0500950300c034200040c110b5840e14032aa150410000d0700744038000300a180103801007461500001e0000c1501e2003a59404240e04002d4107031080d030140240595003210b0030703480c400291000c00c1d6110390881500c1e58401d80e9501c1d441d40c7d805040c15103801407408020021605c0902065105001c5d8000c03141c02009403824078102054101d08034580b40c0204000c003100c4032001001d002380702080c0500c00c082d00010360010401403030072000803c404c100034064401c0b21020000300c82 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 14307389 1250 14306139 14306153
    0x5070b0a090f021801080c010e0a090504020f0d0c05010305060405131202031b010e010506040204060207150315120303050901020c070308090414010e1006030510090504050106081e1e0c010507 84
    0x250940142c61403036080b45404d82c80c80c8900007030045c00c45500c10505001c20540c85041c818404000107489020071514000d00e18024000180040313900c40c545c00170384405034951426113612103019480f4000c2083c50000090201c560160031540564103050130005a040594083e5885a5209010400142c40d02d08100e0940c010744072100001d0b040704e0704010540005402c8419000c0000d0000c105503110441004124400c82c850301e4096046040104044c1010b001c1d44a0348005606021440e50101c10002c0e85142482d0051440c42e0310000e44901810fa161051a9011400b50021480c007074203070402d941d407150380d8407004140150008940e12139881303682050004484440d418000355071180044400031808849141d886040c6540010b030b8a4440e0148034000da40e850407200e0328506180c0140045c0030010400c0c0e502c0e40d00d0b0702001800f100c0801071410b041d8400d002c1c0610100400c0401410b141d50f42c4441c1c5001d030310b06103030a010481d011501071660fa50900704aa690806490003103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 14308639 1250 14307389 14307413
    0x40204060b0d02070203060f06010c03050313050106032414060d0201030f060602150903041809080c0a05010204140a0509180a050a0305040501140c060c0a050d06030c030605060105070b0a09 83
    0xa041c41008180907a640c030b595000780c83c0c1c4c20701c220b05440d041e0750b40008141c0248401c43c0c020303001806402101000c640103030011a042900d40d400800c84440a0300c5090070f560460744100c0713103a04802e0000901a1a02055002d071040d00541481500400c5403010403e1001800782e0f031141d100140700b80c0c02c40e17010f40d00080113641003041c1400020380c2c1c0d1780069103413400c40c000003e60448400004a802e10040121350035a1841a074004480116102d054010000018229140d59003080007444103101041041030483c419800544d0303460800e1b80a104010111040c00d02414017030b0018011540c4070381c40990701650420016220091301080c1358074040d00090050f003113004546a00e4141940180140142c074020780f17940386000000c12100d000d0f88503420300820290800800b248501035a000200410045403800e181442c102c0c40c000f40071a04940d004036000d01801c4000c10411842c0d0240c00e5001d0000d081090030040151540e0b40011f100400e592605540c5541000c10009618041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 14309889 1250 14308639 14308649
    0x10204050d05060103020306010e0403020a0609020f040504050f010e01021201052803050705210604030f021c0201020309010b010201050108060109020306130c030f0f0b01020a030302030a0615020307030e0306040f0b04020406 98
    0x52041c4079190522549030403081c00306038040e008000002c00c04606d50400d85004981c95030091407542c0507078680400605403403a04a900035084408903d41ea9550300a00d8050b40c0030b1000340c6401e0030f6101c40c1c00e00f103400c0d100907491164014840040107030820316107181122800c3e210424002200c810100380d200c89445a00300200d80c0303440c04000d0000014820f802d42c2c406450840c0f20340c401b22011030300c07841c070304c000c00d9240c0d8404400500000d01c18024030981113094011075281c010118071503200300303841c5180040141e6010040140c01c000c00d02800794803a07002c2c00208660b5040c000401e46900c2c050140301b103071640000c00309840c1c3c3c80d07071003031496181365040c03040000100d9224028050445017090080c01418070140071582400c501c203009461505800910901c6c1d131340d640c00d8029400080400d881030303a807504002850604410b42905d40c0f1880e0b40555a28052454081c2103505014001d0b80a5401a0100400207507459044490a5000f4442420303903560380c40011302230f20ba1600301d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 14311139 1250 14309889 14309899
    0x30a0204110a1205060a030809130507020d18060806010c1a0f0402120616030903030e010903090e25050f090a24020a0203030a081e071d040507090501030e01020405 72
    0x1204021000d0742001d40b07900022079803041c48804440401c002602c4040e00c081e580100c0c1017108100040000b00100061940600340c030114040072b6a025044540803981140503030842c01c610202c95a200d0b080d000b2004803044584125410720714004c00c9010010415418040b9a6000c88244136440c125a26220800138060305145401140c0c0007405c2e4050724101d00884540c10700101c505400b05040b4410303980c2c10740181505c1078a40084002d404c8142040d01030540c0c0311945451f0400c2030041921b424025110905224901a40c0b03100301400107207518800c09042c0f0049458100d14202d14181140c1031401d1522050380b00921409172080d04a450f9001151901c00100c2026600500e0311714144400d40344051540503c00366164007500350000d616420070080039100d61300803c4090f80007904582d404c000800441448072660000b45e03141c80c0451403d2049d006060171040c20f003000503000b82c4050005080401c40070b00f0750900c9006180c180743d00c8001c640700d11a42541a10000c1100802e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 14312389 1250 14311139 14311151
    0x51003060c0332040204020a0302040504180b060603010303090b0904060e0f190b0303030606030a110c010f0606030c0203030f0a020c03160203010606030c12020d020d09050c09070801060c0809030a0204 88
    0x1102400504000d030001d403480d02c015039200702c0700f20800e481c0c0c18040b442203032410440e40c0e15170801000b940440034450a00d50301b03000100e920380707440c8170301d100d0701941c500c0352402d0300190309004e8490000140550711440041006100280e44100e00380100d6420888458440c0d900100140281c4416000800c100800d003040041d046600d04c00c0c0d07401540062034141c20000d0420000c070696400b0841e07d40c1651080000c517849040860003507500c00581000004c00000f14500ca08031644400c42029142c3c0d1205508144240c01d8468103000b030400e800c04101c2d00d01d06c240007035100c1c00001c050240c0c8400031030000b800c3c1002074040741c500d0903506040d0fa07030300c0314904040120008078020581c020341c0f8000002c43c10310300238400c0240031407207600c5596040701c4030002e10300650b0010345e051b014207800b4844a10615414021800118455005030981d400d440c0203100581400821400130400b595004000447c3c00405c000c4a040c0c00014066455407611b010030b1424640d4a002900585050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 14313639 1250 14312389 14312411
    0x90a0e130f031e1e0e0310050106090f050901030b0a0504030c051204030308090102030f010312030207021003020306040b0a030b070c0c0314071712120402030114150301180804050405100306 83
    0x4601920002d155005651110303000f180d085861010b0f208000362102d40e200000c4141c01c1c02146a140b040300002c048a0701c2d0044034001e403094480a80c0450003203201458180300002c824001c41c0c0142c4816030390f000700c030341c516203510550f964007a0010381c0d00c1d0360b5400031030241881000c12260700e50f0440101c1b0020314141c51652596401761006a0009001c41c9c085804141c0600840340241041c040420059081d620750703d03140b400c04e5440d01d00345603003044044010384810001290382038550301d00688916000381400103035001142d4861280c00005024000501d80040c6690031008525240104035030919060300e00545541020705811001c0d00c9078600c8000000d046000d03a2451450a40c0e8401c00016096860b56056807008030903009100355540c4208800090780d0040c0002c00201d4410804465401c40f4001907403441c02d060075007001d8803070f582402d000c4d200d25050705007020f0f2640c0c040343d02d07805c041d4001c0740a0503109a031a44c02080c01c8400d1b50002c00050345c0c100e00d0400c1034403005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 14314889 1250 14313639 14313647
    0x20a0303050301170114070e1206010f03021203090a06140903030d0207032715030212040c080106080c06040504090303020910020309090105010509060712090b0c06060a0506090a0e130f03 82
    0x134401c20308111459100c2504204d810301407a2019901480803118944a01400741c6c3e124604006450304044140400d01c4002c8040001e94000c003920b5402a0440d811030041c0f00c0740410300041c1300800c0d0700411803a1f406845401d2218210380032840c04481705822041500703100c4c428003a60b29894880130441c030707910110940c0100540d91090312420b5034140000d448885850141100f40c3c40b00d80d400d0410030030140c5440c005182003c0900e070040c03802c050034061076010001503909495039103501c8000e02c02e0400901c40c090140c80e00f000204451690000002c5c41403045002c1c090207641c5074000c1000301802501680e0006030001c0c41c285030002500c82c007d6581e04108007151007070104070000240d550203a803c480042e4400f070300705842c162103921741580d1040d250b440a030402440c202d001400c4000e040181240f040444044c080b81d080c44010031102003640c1d04010700c10034003000300407410f58400b11168101c0b00380441d66003180c2d44d000c07010300d01044805000340900c04c1040f403240405500c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 14316139 1250 14314889 14314891
    0x16060b1002100b150a0305090304030b01030b0403090e090c0d0203070302030303070507050106230603060102070305030c030a0206010e060319030c020d0602030a050a0507080a1d030403030905100509031005040807020a03030503 99
    0x2d603042c10040560b01804200d00b4905003a1105041902003051031284c610a8203d40c1d881410302044901e01a507a556040104509900998442440d4400d21003010f40c400d941c20000c01c0030039040e041170b040448119480d100300c040709501c10266400d00310219102400048002c6d41c00405a0346c0f00c1c504203402521690004604076255480d000c000314080b400c0e294000c0c5401c1c00075890351066120901071003840c1d071024091354150f00c5910710000004204100600c8480da00001440c7c89041010000e03240060680000292103805003c0114607100000c1c0c0740d0600c00120f0b0043e86584030f5040a4480b0b0515500c043d42000740c002081040c8805030300110300480c81400100020b0383c48a44520131120150b40e08000103800c64003182411007203411120702002010782082e40c00040f002e00d00c0c9154059032040f004191038203010869407908001554100c02c01c0d0400c14900303121000001c0c0c5903404c2900c00030b0800d94480c0800e083c031000e4401d40c1d00065000d410003c0c1a5201e003405412500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 14317389 1250 14316139 14316163
    0xa020a090203040302061305160303030b03010c0e030c0904080d050703060f15080f0702030d1404020f060403080406080a0b0303070c0801060f0b0405060c0f0604060504020f040e0316060b1002 84
    0x10211400040c0c4044600c2140d100d15016801b0b05103548960000d20b14840c00d0101c19501881380c000707003014104614001c032000354400d44002400c0c011709800d01d402e540050f43d001043c80400b084c600000e490209028084040480d0720a0440d911464686041e01441c04900300c021326001c01c1090079a05944010190b03507c00d8410ba589a550305080900c450050500c0c00005007100301040d00703c3c1c490694030b60445418016213040002c6490920200c0c0c5e103010100c2003001c2094140400c0d400c1a0780031030b60580c010b83e0a14a0a825034956004521552054204000c0c5c0d91001502002ca10750050054107401002d49544a00c10300785880d98440c980541381c4107529014002800e400d40d07d10042c00c07941800030650800707240c1070030007400c0c5c1c010f00031040c0c40303014407114070048100501072103101b584900000189410030b40140801510800980c82c000e0746013842c20030301410000309681800d03100c08413100000c851031810710043c026001d02c0766007201400c0c140740036258001c10a20a003007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 14318639 1250 14317389 14317399
    0xb0702062701300903030f09110a0603050103030203070b0402010903140d0906030c09120501060e0c03070908030f0301170703060c09080f01060509010b0304080c0d0c02030607020c03060114041407020a02 89
    0x100016039030010204000880070708200c90881c440326244043e0300000c0c2158060700f8009080e844422214007038815828007241e43c9c8140da1080101c501d0710b122002c0c094441807071300700100d42c15075801942c0e034401c25070007400030a0b100d4000360071681b0443d15500a10f5211019050303507a10301d40310300c2c0e490700704414034004955107c001103109807080c844c10300e64400300c2c1d03601c0424502e070140d121b000b90f032070301c10035a00755403150303808100600c00c114182c1c010504024000da41e4501100014035100c1280c1208515030020130450840c120450f060340d0548a0199507001613a484880040c500358003940020100c03410b18090000d1aa0440480402c42d41044141c40124400b010120308903003e80c02282d60000c281070043c44041e40c224051648144514069842d00704540c142ca40340c41690103503c00050b204d07a00143c00c50509201d0280c00824500013003481012560000b82c6030b0805004180081c2d800607910302060755550088203015040002c604e41c2800c00c200300940300c00120000768059 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 14319889 1250 14318639 14318657
    0x10f2106060e16020d0509120c0411120a09030c0b09011b08011409010f030809060705010e0c040c030902030606060a0507060609230108030f0318010c0309060e01090506010b0702062701 81
    0x41c3e800460481d80a4009075106450701840c4420480000300c0c21500003030074818040d0076240b80d100c43c0700707812034003003003040507503c45580340210104040d0082502c00550700f1f0040640009800401c0648440d6004007007802076902c1c00c40310303401418124151202c1d101180d02c2c0c8210b158206943c00c1c10303a200c0400d07a0301110541800d01005000038412405402101c600410104e180c110280000707820080c0402d191080648400d802d45040000d411002d0300058510075441c074091049929075040c030308090001c100c989e00002d46503c801090680591030001e04003003914030030011511100d40c0154104071807601c0380f0700c200040c001c500106610f40d0f07010071200c0c1004140207201d41207840e4031000714907180d043c0303c0700c115a401c058548000d035004921b001341074a000303010302e840daa882c0c1d40d0001070424190500303009443c0c1d000303103907002d50f494000607201140b800b10700241511315007200b50b55107048600c003140141c40b4144807800340414410340b40701c0e802c074180e40118121201740c2e205450 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 14321139 1250 14319889 14319931
    0xa09090c030221060d1407060905010f050a0f0311210a020f04030f080d02120604050c090a0302040221040506010e0a05060108010e0601030e010c020a0614010f2106060e 74
    0x203d11400b40c4181d0800708000e81c42181c11518030110342d0020010303109008106080e45e40c0c1c034101c1604030159103c1e420800091055660242102004001c00d00e4040e02070242c60402803d14841c0710064400c000307181511091180c000d800c010005400c14441c00c1e40c1c1c000101c00769010255a080c44190380180c5008984105501d00a40e8101c811100e070740d41c0751500d955150035000074085421a0203030400e001c82c2e0b11241161000e084105010301460141d0b00e00075041208854000301096004031080c0108a17140d181c0000c4e00050700d5051f5001603030382d6401d189075200d140d032304002c003000c4250f48000c100400a012400078102c0d01d071518410115210081c0013010351310200c1e501400100e4190041115400304200550082c03018100050300108040540b4250b407000003221000d039015036003000c100405403203000c0442c480403401d07820a506005038110005554825000c040341c2c5001c9440d9600343c824081c40105620000400078240e42c0c0d0b0701039010100494a69120b402c0c800301c0248 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 14322389 1250 14321139 14321141
    0x304060302071509020a0e041511030103050d020706090b161403090102060f0408070204090f0b0f10050102011e0207080c03040f0306050a050906061302070516090e150402130e030a09090c03 83
    0xd00c0e917500030010f17502603090003c103020020006006980381200750001c00d112422501c03501e280e1158125a03150382c0c0d030650416524206203c40c0000440d4000402004829031114100301520311041c0e40343e9a60a0183d483e00880001500c080c06603101c0c01d881080701c680c000010b01d82d1540030380075140c2c0c03603036601c10000c0140310484000d0002d11b070401c840f10061a0540c410313040c0e1481606050300b58002c0740c0300e12900240c101c0f8010140c61080003440380848400c0014001880244003d00010a20510101858030350f0f000d0f5080c22600420440100007428055402010faa00f00302d1b91941e036915220300010490348401c2e52158500b90100304c840000c0d0007200e214003003803002040c840c1c0b14a414050484100c10050758180d03802e00007400004d0041c8299095401080c000c1d205503810b09000c1c0d0b04507006003507000c045070300041c0240700400750010003641c03042d0102c81580d400c400141c00540501517a218805284c0000580c1c0381465030040c1c07418041d42e4194004115661032914107038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 14323639 1250 14322389 14322401
    0x5040b04030803040305220810020703051621030c08010501030209011d0406080109030504230108010b090102120d020c0c12030d020d0e03070b0901140403050a05030a0e03040603020715 81
    0x504a81420402800440c190400940d00070744a441c041e4500f00b0702c01c0100541881c0b001c0308005407014400200034018040020321441c0c0c1c1d0701d880071440d054880ea0003401da4441c0c103041501c6400580c81c018140506540c1840c0d4140030011084910808110010b00411a9001840204107224008100365220340300b40d030403035901030712400462640c50315405001c0e91011a02a03109854a00c0807030015428002e20301000e100b41c881a403213a051a4810302e48010900c8030366111814440b02e03040a86e80440003a044402503010035a4400045004074108440d484c614030981e007001a98884481c1c09038000c1150581441c15210354180c0c1000300812070411150608807688103011450786c00d440c80c0d008108059165000190054101c28034500b1900100d01c1590111400002c02c40064400c2c000d84191420741d00d0301101c203180c0fa54015000d405a101844104640400040d074862459802100040390b00002c80343c541d6950783c03004000e98000e103000c8662a070712110680400b480ba002d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 14324889 1250 14323639 14323649
    0x70e0f0402090415060b0f0c060f130803090c0910170a150209010c050d09030228030b071704080c070e06030c04090f080a18080309150903120c0303040c060504 70
    0x1140305500d880d11404d048104603201c0d428000e568040004440007004020440f034100c031808280c9400314030301c8280c10541d009000049d0314403008108400085124101c08140303510414894a035150042180e10b04080a5070458000300003409002c014000d06118600315211070348540e4032081030341000742d1a81c000d0314005026454500a413500041203402a14001c036040c500701500c1c40d49034592900e031035000301c03a5001241080b03c081c800d50601003100c0d80780501c04143c441611141140303660a5944901c03002e452a08400c01080071240301e1030f15000071403100d464031019410719040c01c96a5601c0104c01240c1c500c11514001401e24180c03040394440d6000a001e00741540ca48024440503042420084580800b42d80100001610a00c0904100b281d1540e03104c13490f61320b90110705614040364015014942c400d00c04e01e8500c3c0e80d281e025003101c0320965142a02c600041c0b011074a000d58101c847c010120012403084080c42000001d18402d60260b84400c0c0f50300d58803401503a0300d115038054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 14326139 1250 14324889 14324899
    0x6020d0905010e0d1a090601060207060822020907091e060206010e090114070e010207061706010e040b030718051005030703030c030504050a0b0a03150506040e0604020408010c02070e0f0402 83
    0x401840d03000d43ca00d65140e000c040c141e0304846256aa40404100b0300780b08121070b905002c0140403200c4d2040090a001d8202400200700031401d00c0c00140103a80000c0c5289001c0303004903506501030f070300440141c001d01c1d8094008212810104c40c060030314503680c00345100b00d14800d2180c1c005842c160302e00d00103c071010b4018007201d9080420300408680028a11071031903413114003140009072070302081403280300e59a84201b01403500c10b00090a100c029030104082000d41101c01c1c03480c1d8a0b84210750340221702401e021031b004058801150190a8240400394140908000000d054006007001c40c2c13030780c2c0c100404000540d981c0e0300325990f540300c9009107609980994030038000640139044230b0500d180281001420300d56070b980040e02078100d54021800e01c0102080c0360340070f25014012034407211496000c584a0f40d080002203001c40c040e034440c1c5011071500d140420000d440d2a4100ca0141c0783e05002808240030551300a0354955451266460030f2605000081c2040e05041c600c900865000380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 14327389 1250 14326139 14326157
    0xd081014040506150c06070906020102031b090307080d0e120303040807030c05070306090f020108090d050901180911090909010e03030604020702011b0b0a0c0302090604051005130b03060a06020d 85
    0x501009240080207940c011103803122900c2c11480301e5005c3d0800c200000000c111503d00560b00501e602000c0d4410380a580c01031091000b03400311240b2500c2c0702c2a100d0185c40e16901d409000070b01c1c0240d550b0200b8418003038511100a216031004091041000c15920100c9030f1100380fa40720368074403041302c0142c40260140911000a40b00301140c440442c00f034002c658406440703441e054216080303400d04803080100380e00400e04558001e129103070b0211405003d810943c90040000e00f00344180c022141c108140c0c40c040701442c603444960000a072402c3c1100304070300c00422500d500654400038580344500b06410028460020501405c8007040b40d1501850842e1580350901029400c918402c03814481602d00101004146444901101c0d0048509808a00380102c2c03600445480108180815004204207192516100d080360215802a40c4420f14090307600d4046480c0c0c01194a07070300800e02c004070005420a640c101441c01608101c803a180c02c503a80300c905a03035a800284511021a846c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 14328639 1250 14327389 14327429
    0x307090609030503071101090b030a0207020f030102030603070605030606070606080a02010215011a0d1107050a0c0611060103260403030e0103110301120b07110d0203030108010b01080103020102100b0102010f0c020d0810 96
    0x61080d1b81e40320041c10300c8903030a6120a00c1c41c0c6981c01c1100c0c9402c0041d404900d42d02985003c613484400d215040e402145141441c0c0007081d00c40d01d240c007a802c00e00c84000302190482e2070f03200468040300d811140421070340d519845038546138071340189c00303a0040c4103500885120440d020030310b5040351452900d280d40544007003882c814036081205042c5c12142e4900c03102c1c0c00d0b210404000d080441c4034401400305013190b40f4101d40c000403190403903820030841c422140e0302c050000401030b05403a0016400c04400301d54240040482c40c800d10500707589240898000304054000548014080b02600c050119001c10b0341c0e8180580403d1103410014421854500081002030b03c0d0150814a540340c200422016108404e2801034140308990060340000010080b091080c460130042d0202407800800c036500d1500000d641340c40150f40c403c1c87c59510348001006a0007503101c04030500842c80e00380038400131124065205c00f0b0302020031300896403001c00112004011075403d400d803030302c055090007000c1c210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 14329889 1250 14328639 14328653
    0x131509090f02060d021b030405010903020d060b030109030512090d0905041d0118150605060910090f030305030403030f110a0309020d02060c0705011706060a0c02060d0e03030709060903050307 84
    0xe202910201c00046500c0701580b2210020480480814400741c2d6440e0b98030302d184000fa80d8000320300220f80040c00b080c40903070381c05090a800c590301102c4850002d9100e0800600804070041c0542d0703d0341c1f9220b0580201a00440a080c1c0782c1031038541034910340c2e44c0d90415503d40281103624000201c031f40d01c0038000e40c6003c0d030100410000c000c1c5c50341c110065001c0c0c802e00b11003c8145100f8511006500482004070081c42c10107144245041031042902c1e00303010407207501800000c10b1144140c05603141c01244980000801050000c811009060352410042d1560f40140d4041c0c0009040524514080006c0c4c01464441c07416902120b142001e881401c40c010030340074000302d80c031610403881d440c056503401010340a034107280409414601d142000140284507120300d5007443c0a1944200851951140c0580c0c4104a003820a1501001c0b98400100d00344101030300c0d40091898800140c3d01044004003440c4075299a450b10048a5144c000549004603584030003826940100300c417000181d0305c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 14331139 1250 14329889 14329901
    0x8090304030c0608040f050706110c0301110304080906070501020406030b0a120309060f02030d150602010b01022e02090603070f02070803120c0a03110c0102071118070c05030c10050402131509 84
    0x141d0071250004019503210748c00c08000d644001c2c0040c04082490715000014005c09999403400c40080005120050003110355000050024040207404a880a1140c03960300454862a40c414021995a6200d440c050002c0c07003600b4030a4000e100590011500615501c5c0c000c114a030113440d810b18007850044221451421541d504c0110300041c091050411110b00901a05505070003011a0080c201b0800908603082d142d0b480d4115803004903504d500c07041d2000821600324854203018519080e2201c25406807080516640d0061400420801c529a108840c080714a000f0f41c2500c1516503144201c170f549010702d03290030070200161704c042a580c160850040c1100203150401144d002d1009481c64895004442d902e0380036500014000100a4522a5501c460000301c0d130340120742c003119801c038444410003001c110a000030541c050080c808104248d4800c5140c1004507107600b2a020010005410706507001c80c0600b100300b0700c201480b102e600400720000c82c40c2c202c030f8030b4541c6000444805029 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 14332389 1250 14331139 14331143
    0xe100b060903010e0715030209060403060c02010615031a0a0b090108040606050a0609030501200403030302160b0a0609180f02220c050406020d0e01050904090206040503070e0708090304030c060804 86
    0x304000c1107240c40038002c07407145060321005011700b02d103411025030403103039035000e80c40c201841000040d0559680b0000c0da0141c0760002000115035000c403505a0042c0b01c81c1d0000e014440d0b9001c110612164035411280c8042c41080541d4500c1046600303104a0350458082c0000b600c50074820030415522806002c1d5220f40503a00100b9004c0d0380c1c81c085510050300b81c0020b00002c40d082400d00611009019030084040c60841c058005884500705141502942c00010100f6400048158468502166044089401506101c51801d0454170314004006070300c0785110715801e084804100d014981c90407101700790840710300200c9003207a5003040030480403800842da0783c010b6401e4030b4002c07038014071800303410403196210390340e030f0b94184500645010b0f41c1840d070b8010480e80700203500b25a640942503c020f0081654003081c500c03528800644580566001a42c05110b024000140410300140d40d5008084036101c00c1403c0d11500c010a03124480c42c00090040540d0080030032105101c1c0d1265640b02d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 14333639 1250 14332389 14332399
    0x80303010b0f04030b040602130e0402060415050904150510020303040206121008030a0c06050c09030a060b06070212010209100c0b0c070f0218060316030302060606071703010b1206040e100b 83
    0x607481740c1c0d40031140342050307806503081c03640814054060480385003071801810b205a0700341e5803031510790300145035403060340540000030980c2d1190201503070203030060341e08914000307009201c1101200301d0f900b030100340c0b1b1288074890510a04101c540170f00100c1100e01560f00584080e28010b10582c0e00400580c001d4020484641414070000303007108203002401c10a01d00350740f44600d02015042c02010f440c0040c0a86010b20020400050300c1c1d94001503c6820591244001c40c641c0301620005850b0301a4400c0030b900500700e0950482e002e001940100102d501c1280d10802100036810103da100401c11001005991507030045013044108a020b03002051142c43c01c40891003640d40031640341e03100c8007c2441034000350001e1084d9481c0c10b2101e0805581d280050071481450341e10b00a540d400d010301701600030140040d04900340b0001304040e160007410f200045903603582d00c51484446920414402c0c4499080c000424254940f83c02410355a9000b0001448000c1c116907400004040515506901c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 14334889 1250 14333639 14333647
    0xb032a0a1206050114010f120e070602010207060528020d020f070b0a0c0201020307020c01110328020d03020702060d0b0d020901090b0102060604020405180709030501050f091006080303010b0f 84
    0x560355440d810005866000c60300040c2840c0e0380b030080156501a0000c0080100f50030a036200b80c0d034401312000030313203403903192022030260284218002001307013903480706241c0504200820401e40540080507403074414a010000ca50382c003032051301011410784890150203c40300c08600e46000c0c030b4000c3c0c40d280314280f50051424081c0c0a01e10070031350010741c08031240c0b00c51504100c0c0c00300c00340c41895040c51445c0003d42c030714680b940b070003901c4041aa07079840c103000c000203403035229080800a0f24a0b080c9a004c404203041d1800c1d45201484800c1c559140040c41404c100c5150548a802552512980031309024104040c6449181c05421041007540d04001e60380c1c160405039550680007030092500d601c000940300580e2000a003002c5000f8101400765004020400c0300352501820b00c101a0703e0814000c820703480b2404c0071189111282d0001d400d07503007040b003401035074081041a10300440d40030b801c540c00d04104841034800e0324202d200d4141c590300107000400500c2c48603001014510100300d51540b40c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 14336139 1250 14334889 14334973
    0x3110c0303070609110307030201050318010204030203030a020105041b0b1801030f09030908010f02040b03010b030c070803161709120a0203070516090b0303180103020d0e01050421030b03 82
    0x599040b4420035110203803980060000c0c8000340348400c0340420103401800515045400103482844003500703100142d04c2d0071000880c28802076042e10041c5500400760303030b5101c5031440001d001e0207080d40d042c1d0305c1080c0f00b051884410383c4001008122218085c0c110704180003411040204460410010f06168591160540b1002c5038400d00118138441d483d103422070350800078541d0840341000c003102d02148c4100030038484072860105890443d64010390441e0f607540c411078521518040e91000400840020003804084800d40c007003400f81011a84d201c0c0908030b01101c0e4086150820b480800d00754101020810b0001c1d003200007400b000f250340c01101e103414613035600e142c0b9041e51014070382d124003420b22081c45000309500071887c5500c4114000d5040c0a6170a000c9103418500301d8045060660010721002c80b034880703800c00c3c54440c0030343c4002c1003245420308090b18189101c3c0251201d01d601040c4028076140241301d0300c440740c640540100f404104040c003808096407110301c0d0384600d010000003981 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 14337389 1250 14336139 14336143
    0x312070e1216060908012f090901030b01030204050f0606070308041407060504150f050307081e0a020307030c0906020c06030a06030501060609170604080a080a06150c0201020f0c06030403110c03 85
    0x1440502c840360020b08618090008010156a80141d40180d0406940b0a00800d60100e44034070b00c01018030101a0341c0e8120319005662189a05050b00141204c0002040c811020a107a040742e000740c40500c000c0d03070746581c45003138580201d961030352010040c002117000c0383c0b15a119582c0305204d5000c003003194100c1442c0300d103010b48660040700060070000d41880a02d211b0180300d000000b003030400743c0c00c0940f281c802600354040144080c040040600004000086454100c0002c4c0c2c0c00180340150340c149a4180d01c00781d4001c0310790201081c1400c40c10140288907000c070108407881940609101510300d07003044410b07032016101d41000c64440b440840070030020b201d64401080b0585940801a180904108043c0100300303401155801420401c0041a00715003110602221031506040da560b461014038018a590380007140400c4614071000415500b08241082c402e000341c086070404842c00d188650b9039141d0f081ca10341c01100034004a400280210743c0d132010311a0141c1a201018030741030204c0c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 14338639 1250 14337389 14337403
    0x60504020d0b010318081207030b04020403080301090c1d0609030109060f0603021207030c050103020c10060e060a0801020711010305090304170619020a090315020f041206050105030312070e12 84
    0xa0a042c0d49002416107503815100780200f5403031781021220039800c507450301d042c0c03800f0303075105400f10803801c50019003a43c0c0b190384020031a100040c421900d03182c5a0408494030f0700f090140f070384d01078074224610000c14001d501c29200405080c800c0d2071205410310034000320b0381041038555015034a0f102c00c040041c455011f0920303480301c0d4000000c1c1003444c50041041c0045040c05405103a08800340c10f0010401a03d503640c203441082c00c0150313403111440340c11f9181c0004001d0504101d45014800b143c02c0307580100c003600582048600c6144a40c40d038042d10300b00e100d075030f100400c2200642901c65065009030801684007001506880c20995100781c0c01d611409985015840358002c2020080746a0100003a00001c02c542101181854810701d809171401030540000b40c69800780030b008012884064044400c013502e0318252035241c981c3c40c0b4603414607585040044036150305060021031141000002d60301d081c1480ca04860310346d00c8008058412054a5400d5504128801440c5148003402c1040c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 14339889 1250 14338639 14338657
    0x20703020402190207060807020c0d020d020d0b01090b120601090b0409050304081005070305060315091e0304080d030203060307060e03030f0403110901050306060a0603050c2b0e12160201020106050402 88
    0x3c180002001802420202d00360400c20521000c0418040036030750008202d03224040554607440c1c0d02026000140426280d06002580943c40440301002c00a154507024100d418441e13040c00341105101c02c00001030b0a4607000a4241c1c0283e00400010840d50082d444910000d04002101003180d118182903602507040941070707503c03080070410700e40000e104843e444507607450104160705080380060f403a0000c0c500e0681c0348a488401155449009012901169828111540f10001040e0615441ba00144607990450056401a0027054000c0c004c4a20a41004010b043c04505005083d608804910301c1181c00d80700a1090007000d080242c0204050350040710043d0f418042d443c20800d80c7c2c48160042400380d0407da05000480d11541030020603503076079040c0400c1540c1c8208124109014a852001c84042506180e0821591450407640030300d00c0d01c0350500c001552141c2c159500c0380c40c2c40441c011080c0802648603024080d83c83c04845910510021031851780d0b0314001016a0400421 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 14341139 1250 14339889 14339917
    0x20d12020f0c03180105070807060f0f0501060e19030803070f050708030408090f0d110609030a05120c0d020f07141305010e06040c080613020a110d03020d06080c130c020703020402 79
    0x8a8559005002c0c59110b07800402d21304246054108e6031a00c0042c003644500500803511440100503501d4140c00c008002c0101c54020441503a40f010010540c611503040746005003204854200c00f190701814840913240c010b510380c1d1a58031868001c551501d50821510204481841041d00181d218030045008038051005161216150010040c21070000c100240c41803400c5403c04001400310200d4400450b001c90f1699220948000420706208120800038141d00400c90300720500c905c004060a00011b40b00200c0e00048031908050780e6560030925500001e5002000402c11400c1c808c40d258160440a0401c00d41002906404800da6400fa0003103200c070140f503010404281024402d004e1901101d103080742c0d15040680104800343d052036070a40c54075400140c00e515090003008400a0b03444202c0c100c41c0e1040d00310500130025008070615140c45404e000c0001051540000d1001c1006402080e010070960b02e10241001030100008000a40c003c0100c0000581c0c1c852001d0850f40d101255 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 14342389 1250 14341139 14341147
    0x4060b100215070302030c0405030115030b0601020a03020705060702060d0c03050702010b0105070308060909031b0a0519021008041104021303110103090f06050415050403050702011106010501020d12020f0c03 91
    0x104224402414054000031503201c01104008451242d882d16004140790500698a84559490300202d00c05c0f500002c0d007641c2054a500746442d0807030701d42c40860340a0581c0c1841d503101c1a004986036a911100500140e2110700c0c140154075011f0700502c0843c2c401044149002c1140041078182d400c40428800401d07500c13000c00034010b03028001c80d0003c0c0c0003486c1c0b540c0381190658025181d200e002c0d00d2640a1103982c00002c441070300400868043d0410650320f4046e07845050301a81d0f41d48a5107104442c1c90244104611000d416030b00c00e6100107900815100c414402610121000e500040c01a219416100148200b903241d0341b00074030880032001005080355041d410000803d002da00401810103141c02454004920801c4250f500035901c0704010840e6100c0d41000e5100078520910700412a10302820300042640060082900600c00c2e00c5411388500c5100c051a11000c0910440b80560030a100f10155948200c000c40e00500c2020001402c20405943c020001d0b0042c5409042ea544002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 14343639 1250 14342389 14342411
    0x10e040e0d090501140a05030a020403050a120e03060105060304060f0f1b08090705010207031401020405090a0522080a030902150304030507150204030804050f03010f380a060e180406 80
    0x301144040d110031709107a200e1401481010348a8450500800100030002c40840c60280e4560122402140c0100c01c480304103640e414503408441c419102900896080b0200400905002c51380a040341c50041110341540d9036a140c40000d848003550000c51150340d05c03a2520a000d4030310641c6080c420207440442c0045a482010f00380c0c1c8009400e840c8668022803040000d40c2e4002101c100b503d511040c82a1003098040200380a0301454001d0f80c0e00c034003954200080d00b02c1c2c0d035001a22903400c038018445400c2100ca90180250400c003406806001c080012010041c00313904401031a40c406840b0700751103c0482107a1340030303400a81d01100001e500061090078030002c4203058250840c112000c40c94185103540c0d140c040d1003544a0a4014000c0300001c041301c0c0e030294001d0a50b107c40960a00200c8444c5107039499101c5603c00501000b2074001300c00040d41440f04c252101002d000d00b0702038156050040540307000b151507950350760000f0344002c0701681c032420000b414040c0380b00380303c081070540400b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 14344889 1250 14343639 14343647
    0x3070302071505160f0201090b060121020d020703030605010c0b0705090d05070801020c06060a0803070b07092c0705070c0302040209040207081c110c0322080102040b0309100209090411010e040e0d 86
    0x2217a4800c08580c107241c4102d0100b003c80c9885a00100b0908060701000392003040d07221898081401c25803403910100c0d503541c102c3c1194006208036440380c1e03400c00c80e19845d48015941c048030283c024151940c6035000a90a60040000300f841c080000c104000d0683c0a03940c8a28265580d00488030594011030004c0c9000e000b040f449410203412a2142085800c0002c0950f0b0b074003c240c0b0240202140c00c000c40d407518040c15120014165204040340c950724602e0140b0f443c440d0900746204d04401640001e0f0360244200d0544041590000c1041032440c074503000c000203504005509a4815820013840000030188401800d13007459858640c4404064904003c08480e44005009061001003012543d9a800441100c445070003200d610f481c081004145080d01c548160041401980300180101d464000315001d14802c443c450700f101d200c55547d0900d40160300840c0c1300d064002c0f800d030740403070000350705002520003102040c90010000001c200c000b03800d50f2440d81d000f41c042d4200d20510340500d540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 14346139 1250 14344889 14344907
    0xf0408010f23070507020a12050607140a2102090d0b01080d05030114010302031008070b04080601150f0c0501090206030408030105040506100801120f020303190210060b0307030207150516 82
    0x10b226944408001d20350b0034203440380203080100304000001d0078011555800011000703408800303481003e4441300d246c8550303190025990300c0d0200c0c100c89080c1801480e00070407510b40b5001d555404040c4426103c20345044034001b0b5000001c55000e2108101030740b0303504201000305010300c4031a43d06500d803164080c01c14400c040100c0403c0010001400800c12000120003140000c0c83c005940341d80700c500d2001061242d802c80b145900a5075800200550104050301c1a0751915098403100e0340d88014100c880140b5000035404142050008a50140500c5d10313001d95034001d4002040c026041d0f0b00103003c030761017181c007101c110070003200500c448d080c00d1041a40c4420b00343d0f822410303100302c0007015103c0c4005102c0c603400c4000c0c11201700200413078407a0500c1c4655016003145d44030100010a03c014a40c0300f41d01400500c5040045c201034102400b0340710464042c0d6941300e1858446500c1100694000c0c02c040d907403682d4040c0980460300c1180714840c4210003034a0340c1c2642c8042e8010081801913 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 14347389 1250 14346139 14346161
    0xc0c021002010b06042102030d02010b0f010306050f0103020c030f0708040e0f070c0b1003020d0b0a140403091e170106090501050103230a09021201090201021207150c03020f0408010f 80
    0x1c900039032042c0c90b841e4035003182e09803083d406d560384602000542d072800500201d9030007509405569191041550150440c9500c00411205020341d1420341c00118111044e03440303029444a2111003580e07481d4003c0e8000c281503802d0034181c0380340182122003400c403a448480200e0708100002810065260076036001500100540f949003000d081c1800300034030a1102c1840604000504400700f0618811094510002c1d540900501d504404605100451800403154103881d1410700d156601c04117504443c40c1e21460303050b140d1041040c00c0400c620003c200b460b0880c198800480e4010903c83c0d1444919616481c0390b03400490007034106601d0700280d07007060340301c3c5042c141850204150714104512000e078001c440c0e00c104041c3e03076070b141110010b0074420101070f40180220600c0303540d100064000c00700c03090007a004c032180c034200d5880148052040c064050300c41c0b21444a03500f682a9a80c114991020242c50058240382c02203440404e9680150302c1400269942d211720700e0094028003807551000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 14348639 1250 14347389 14347391
    0xf02010507080f150a15030b130504170c01060b03040609060f02040807050f06070f051605010e06030103030f02070e19060b040602030313030908010c08010801051003051b12010c0c02100201 83
    0x100340541c0203c009a4042e00e01c44108820b80b03840c09854440481d0040241001d880f100394480299101030001e00340c031b82e001c0f400740d0600500030000c0c40607030003800c0c0500d902c84803108041c99102100311264000ca040c0d80c009549074500041c0341d288590245000b580100c8000a08050b140340c40d400300c43c0030643c040102c1d80140001c201803000803416204071070b0140d503820359800594001130b01ca07228481d40105501719101d181c0060140004400000d800001c65880000c0d403179100654400d6a0024526800b000800040c00003a1041c1007611800c08179004490169403100043c0407102400c5444094a0a00c18081440c20b601d03400752000802c0060801403601d0b060602c004d48a02c0300401d400041495080d601041603c01d0801d00002c0c21000c000300700740300b51018010500c40c020311030008158240004140000f43d90a5000c2c00c403a401401481c0120183e08014001c1d550302079034661000d00030041c1c9070741c1d280a004d0b08410b9051a901c100101c402e6204011500420400260031a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 14349889 1250 14348639 14348641
    0x8070e04051b0f0c0601030c0807060207050603040602070203030c0a030f031802030a0b07050f07080a0801090b030d0809010b0603010905010602160e130609060e070906150c02040902030c100f0201050708 89
    0x319801e610394030040442c11440540c2e440307a515601e0158802c00d4900f030428032401d000001441051800d800950302d0f04415201c64548d0741301c0881e0f130751100d030003855030069080021400146030344c5d0003004407520140c10f9030b0804000c1c40c0e5130350034054641c1c01079002c569400701c44888164036204041c1c03041c0205820060b03e207580d4020981d00c44007000001e01076044a40851400b5000d002a0b503803150010050a9407545c046c60084c1a80c0c2002d500f02001c290070700004203c0032028010b05401900140c024020100c1c2c1c1901141c08205c040c0104001d550f0314002c000c656100c010086000e0a0401c0010a20b5450900e00a2600b1191000e46a281c10000342c01e01c0301404085007250804400c01000303d101400e814400002e00000301d00802140c038044480f001d42802080300411204454010030586039100c1e804003401c2c80c2400040001142c0c025450018505a840140e2003400502240c0e003501760240400c0200000c551041c011401030040718042c3d0360309000d815407241e1246054a51 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 14351139 1250 14349889 14349901
    0x3030506100215060f010207050901090e070902090105070b04030e04020403050307020a0503010b01051603120c020c03010b010201020a050d1e020f0304120504030b01050f0111010203010f03050106120c0e090a02040c08070e0405 99
    0x15034031000d01485d114031060300101c586a07100308140c0d406811300904610f01546c5d10f82c2000c0c0207000416606140340146140065030540f54425030301c1204e0182c48140c076040d41c582d01d181540000800460500ca56003d840710301d5100c42c806400518031031802907940b0f480c03600400a90345c6445e4401480b80e81402000d581c6640e100c016103d540d110105410300f001c060380740c2510181094824082e00360b19080c1c25800c1e480d40001c00d00d100740d90580007004940e01c030034012802d030b104215003480440c200300a1311450020550201c061910f280d510148a05102e10147d01641d01c00e204030740504401200340028071802c1541020b0511443c1003081ca07042c13450344c0c0c3ca006542c051050601c42e5205441c0011664020740002c540d4801d0b5100840d039968488030044d50040700c40c0415a801d61034403c0125054003102e01c41e982494004560013444c91803d100c06041e000e000704181e43c2e9020b00c01700000162114010740e2400701c4107480703001c7d031460442c000900140d001440039205500b440c3c1030200e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 14352389 1250 14351139 14351173
    0x10b0c0601080307020a0b1602061c0e0609060c1605070303020f060f040b0a05040f0204050702010c020d03060e010504020903120a0804031e0e0108060102070305070b0304050114190903030b03010207030305061002 93
    0x102c50247c03048503200c4298142c507503e14810440043c1d004080040c000460303446861070545400c00100d41040030186c0130160b82e5031000b044a010701a40c2c0140080351407400d40380d015041e20b00090018600144075640e640c2d00b808003561085015a21101142a070b80c4424450f10340d0003004480035100500e844d03190304285100140049104d81c0e940c2c0701050600c600602c6400c28280c01034800d002d20704100a0003030080402c0480c00e001030103050b2000d84410721a01480301258003120001000ea401d00080000a500c0301035102d6251050342c4880e10461146409041c020419440e020704902c0e240c20302030503c0c80ca0160445141000c04000710340b00c0d0f000303d040301100c6401e2034076001996413076005034a40800c03a0030107415445030030400500711511f2401076105a12030002072003d0a80d238404121250300c282e9100c48050000041d0a45a200962010a400b40a0726000c9618120f00d0003103400ca0b8400c8100350300290300da104210040c100f012010844171340340d200402c200c06406428103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 14353639 1250 14352389 14352409
    0x30a05030904091a040f06050601110604060b03030903070603020a1404050102150c040f090504060b010804020a0b03060406030803070c0201030605010906020307030302090f060c03030f06010c030806010503041a010b0c060108030702 101
    0x910460343c41036903c003800b0500807031103803020510507140c01c2da04150404105030803500d0300441e0600e05120002c0d01035440b40368aa1035405031040200055101c45c0d03141c10150001c03030442d80c0c040c44140140c041d0740c0e40802c4140e008004a45005a403072742c410900428079003007803600740f4500808000400440e41d0016802c4030400010428681984842003d030b611882250b03c851010070720349001080c10411548803a00841c41079508009002c041d000664a40da01118065070002e40c001c001c100a8111100a55100d14000e000095281e1295907940d0141c00076115100044d00d50b810b00000c65030035200d4038025200900340701d415a07160101c001e55070303c03601030001c0c10035402040f15109910390ba40d4030280b45c070004003402d460301004003407207550ba04122002d406800605011540550080a4010201e509542c0e054003946d541c0006481640c0054022900740c0000b03416009070900c400c000306d0203000c41c9483c680e510030b00410380c0d42c40d00744103070412400703600b0811560005a0f40e5031406 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 14354889 1250 14353639 14353657
    0xf05011403040809030a02030d090602010f0509030301060c030318110f041103060d060209030604060b0117070f080403020f06090303160504050319030c0506040b060406060f0c110a0302180103050705030a0503 91
    0x81984d4003010f00100741440d90030300c4029014468808010191a00007000f1010b903040751307000b04a60910700c40c40c0425071f0002d40d0b1a405036041000103001040c801d15401c0c0f800d90190070041041031341c20046000c00350440100713844022032807404407503501c1c0c20fa000f0103010740300315028080b01450414107600e0b40b01c050401c920501c98101d92008201441d0140c400401c40242943c8251426041100207001d45403511400100039000c09a548031945505034003c3c80c2998a061b4410701030700e810303500e00c40e020b002030701544100101411a0f80c1c0130820684210503603000741d9124240381604150302034400c940c40003809024002800b0584001034100c1190020210b1815143d5030f9040c00d90f900c441c0100090080e0040e07800b00010b00564110342c0f401040255400c10003d69221021150400704000020008014200444c0890140100041e045c2e0b0000c190700880d641d642d0001e00f0401c0400d034242e850f07a409000410034040e0a22006000744003c0c0c01800c4c140419568217600c0384104039030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 14356139 1250 14354889 14354903
    0x6011701090c0e04050a0e0105011212080a02190903050c04020a0c1b1802030103021302030103020603061909020a0c05010501051002030d0f06090921031a0603040501020d02030403090f0501140304 86
    0x46044850f00c50528080c0003400640104101d04250b409a405400d040b004002550b00f030100005182c1c0c00c0380c000d20b41661b002160481c0c071142c201011100b801c0c020b0142d01c0e130b5075000d0154490140100030b011120841c0e6442e1841507502c2d520301141041c0700240101c2c415481070068110007600070f1110f00c10b16034825030035070b40d030440c40700580b245003c83e801c414100800600c038406101455030085060f41e000321107061001c10503e1244050384800d0100070f400000c103001041060400d41d456960700119508290490b90301c1e00601c000b240c020340304850001e1900041c4205020003031181c1d9000d8030703095602040b40311a4410180d030704c0c4500d189002842c1c0c3c1c2e503018032504032480c5c2d0240025100000d400d000641042c1445d8080c01c02001c5015810806044003a40e21806440b94a203440001402c20307520801101c101300294100070400c2d90155000c12601c8482c0c2b200b44003c0d841507100f038403806403003818038601c0c0e8030825558000a050002c560404a04600325a003070340c0d807090740610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 14357389 1250 14356139 14356151
    0x3060f0b041202031002031303110a0c050405040309050909010606081003020303040b0a050c01060f051306060f030e03130e090706030507020a02060c0a05150a0b0a03080702060306060423090601170109 88
    0x3c007103031a082c4031107000ea032035500c003005021480d200607a2048070a4080e68901650034041a07200d40c451006070401044888096010040f50900b03070441030b4407078081c0c20102d025641c1c40740800c10b1880c049588204c680d55680f401c3c00002c2e00906201c0e0815032031000d00c4e07281800e56022a550344264015819415000300304132090300e205100301d0b800383d44520020b00c81195211500f030301e01c0040b0300449114a0704070203414000c2d25580701342000c4854940e503400140800314025802011481a544107900080083c3c400740360790104010b000f00030307600007001075182110046d030074409650041000c043c1840305100c2000d60000307800b8000790301160707034559410181b0307000d5143c01800d81d0010b003140101c1091214a0304100c04140c817440302c1d0081488506440801c00c180e981413400010309034035090003184054103051003d1503012401908481c076041e198118013055034145407040710080c6410b84001704a0800790000d40e0400401e00341151200d08446814003411414019903070250fa40d24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 14358639 1250 14357389 14357393
    0x1407030209120d0507060c0305070c03051e030c030601020111070c0308090f030f0a0203010c090506030a0903050909010b07030207061d090a0b040213050a0501020303010503060703020309030409110a03060f0b0412 93
    0x2c08085030a889810444180405411000d08150090076082e01d040c3d1400900410303090080c0921481412150355800f50700301166400d41d040c0e0080c000e884101140b05560014118524004601034903000104030f880785490800242540d407540302540c071103070040c4003000001c0c00b04070180003665400000951281503000225207101c0070b04901e2641442a08801c410a100101d608800700380284c0090066043c911001e031508011840340c0d5811031803c0002500c0407006500a4492521030f252140c64640001c00003945220281c01280c0382510000e444c0040540400414008010324100960350780c1c170101e00e05c40c01d18664001c0600904050000520400035030340f082e861485d00500031500d41d0360090000748040c1e0b140c09103900400c446a0b02103011360000080d28103c6000500514050740c803a1002c401075000a4035603041c0e4403017808042224208c90041c40728003403d842c1159190351181500500f81c400950082e14086c0da000030921001c21742034100c0d4243c0d005d042a500c9112414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 14359889 1250 14358639 14358649
    0x20a0825230909010905040314090a050f180906010603051608010303030e010e010204061211030c070f1b03060c200c0d08160c2606010303111005010801020306131407030209 76
    0x702d41c0b5264450446400490b916255030300142c080c900030340c0c41d085d54181801c0c020281740300e81e04040b6801800958200101d00d031441884415002c042d00d1640a13150300c21000d40c20010a0740e080c4034a4005400610245605229003a4403155250b03140d40214006507028202c0300043c000a801c240c0c442da010180c918003500b210700005501402155903039070b1001d004040300e00c40c0d0301ca003139201d082074a030101c0242c480c000c0d02d000e5a646100c5030324081f0030b0351f640d24880303a00040131201100b9841e40200201b04c006d260300d00540c080c60020882501c1c4c0c18004140e00c1121500c10b0b60024585121102c9110005011504100980d40c1c02c0201c3c2290800d51050300a407441100c2c1a10441c03840030070090003584000845180020310403901c04024010141049201d43c2c242040d48884010800302e44660401411070050340290380f05000305802410568509800c1302200d030790000103101d29403c1c4004054202c132401e05042003407220b800c000c00c91071000500307820205500410311940d03c1d038075 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 14361139 1250 14359889 14359897
    0x3040501080402131e0b0f03010203040c050d020a0e0906070306060804031e030204120507030501060501020304030f1b030506090a050c0316150504050303070302010e01050a0207021f1101020a082523 87
    0x600280507481d0751000c03020ba0007604081b84043d01a204c4009176220341d007014000c0d01e0041b0380c0203541c4071007541040103000320035a8402059900510a180010300d45855500705070050380010b02a05003880d10f004094103680c4d80d13a010b00e080002c0c810030400420b034060125a0405610510b4142c51041c100c030441c041d000b04d80082c500160140600c034201700e4006984c0741201d1080d8002c0c020165201c0041e0b07180c0c011440041d0411080c4a1501700180d14032500040740b02841c9003519140c0c3c0c49441d018904ac0c01150150300f1540155110401c0c00b10401584503d203100720300a089403140c0f090100000a15449410105695519121101e500803002d80d030243c1400f82c00c903900c9690a04009010309801c031126401b80d40f8000c042000c02c841c41c02150f40d243e4010301607681e0250b160300014000900148500100100c40580501400007170000b00340114503543c4100c0c2ea42000100d64600101c4441959020f9040c1d031800034a07582c00002c0e10665a10840401c420760501c0d50368920f261007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 14362389 1250 14361139 14361161
    0x81009060605030103051c08070e0a0e0a02070507090605060901050c010b0d051006090218011101140c07050606030109050a0b0408070606230a0605190c050706200304050108040213 79
    0x10804001007480e0303500030041c40c1244d009008030f4264800e00747c0d0307100318805000c0003040008c1400c0006000035000e2600c18090350307009400c2010903a901d007560030603882c041c0e544105246c4c00203981001d02804206030800b604400c0380400c0424a0400010410320914500b11305000c000304e034010307150a0039800711041800c081c000030140940e41c0380c402c0d1276008150007540d00070302d02900490307100e115100303503000c240e00d40008501c50a0191300554020054000561440d903d6401070607000e21040d40090191080d40e200f5034861081d468254140345d0014082030090303152071650004078600044140c01d55420401a003a42e403502d0610244a101d841e0340a0710050404000203051000b604155090019040f0f10703d101c030134510104070809690307109000018030180f2006081c1052500400e003000310500344941c2480d4540c0c0e420342420749541c00a0b0102e6001ca00480c00d0784d5038101071410b1225903402444c5068200000a40041000b4101902640f00010039250603069a406000720007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 14363639 1250 14362389 14362391
    0x709020a080402010207090605100c1b03120207060203131719080405010314060108040818030a080a090501050f03150105160c1811031f050607030210060b0901050901081009 76
    0x22003005009041c416054908a0040c0304001c000203c0554604c50f80c02514401480505554080c05044a01e100c11031000c0d0703400704038020301840103403845104200039481003035a0001c503070164801030701700f050b01d611520554001b000f13442ca50800e80c903c0e0700240e80c0c0e056014a004400e10000701c1c034110884082500d1002c0c80902941841107001c00b40007111f03801d9806012145844100380380c089001d94011340401d0300b04000c00c0c00a07541c04041c003d4841d20030981c070300890080000070329082100005540910700040c1148031960300514601c01303040282070862034505500001f1b01540700c02049a00314110201c1101c1540e0703c0350303084038101c14426091048144190402600f0480c0d40d125800005881c0301015002c0d500c54041c0c401200d10135181d09041d40c0c0c03a00b1003540780703001c02d5031109101402550040303207680e2a80c0152400c02e020303900819030321200c01c00382002c440c1e40e42c10140d011202440010030507a8003000312503a441c000c0c600740040d41c03a500c0000c1032894040d0807401c505 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 14364889 1250 14363639 14363647
    0x5040908190c020301150315090201141204060509010207120f03020906030a020c0c030c030703171603081f0f0306020904060503060108100b0909060403110a05060f09010f0c020c040e070902 83
    0x1050b40842c604224600842c0208910780c0e8040303126458080c184030080070701c03400c40d401e20000c81d410350200031140c2c0181001c01d19000e0010003500d2aa02480e0030480c0c004240c014001031040d540304071544450003400862030001d40d922001032409000400d1410019504403006c14282700390156140480040c01b0713a0b441e400c004882c44040c1d081405480981d11400300d018155190005030030858120180c0506a541d0031900d48902d44904007081d89002c5404105540c0300388204201844210f000c0e41c4c5042060034840a500040755407070780c44c10a4600a010140310901a4507035500480e40d00020050740d036003070f10002c0350103080103500103513240c000c00000050940c0d022501c0b402031807031040200a00800f810400c00703c00070503580e94621780c0c050030000f00040e0140000c440c2448503c000c5078170364661566210700c0c1c80011501d04842016101c00d0001c01c0809028410a90030320715028071501e07400f00002503554101246061045072180384000c1030741403d008213000351070108019035171 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 14366139 1250 14364889 14364937
    0x201020a080705010b06070c06030b0d0201140a0215040b06030d0f090b031f06030204140109080304030611070b04030f140304051c0e0303030103050303040c05090c03040b0403031d07090f0605030705040908 90
    0xc40c2300e2040801103401c0085507052440c02e680745c0b407681d5505031201c003003d100d0100110080e8020500b0001540704846601d900c040c07654400c0c2d842184940301c413100c50702e041414581400c070b07003101034414000400d00b01e07540a030f0072064600980d041e044a16071070340c0e9403140f4034041c0150080e9201c04041082004541103600d41c0003802504ea140c4005210106402c5c01100e80541d00e100e0f607400c94005100520000c0c006400c5207002007080b17911030342444140e480f400ca030340c2029102240440c40c210403141c42a508030a500145204070302d0b07110b041d0b10780707510340b079441e40c441c1030800d000c10300c449403109165030042c1c107801e80340900035080300e48035a100e00d046a500e500c2520181d41741c242408002441e894411901da00c07940407400ca86046807600d0f07a842c054100050421001d0503211211810800000d070000c0c07400e0701c0720790000c0001610b84000e400031a03d1800c030b90420982020307400d001a13240011520304444d8140c40004164403941011007090050600200c115092200354680c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 14367389 1250 14366139 14366153
    0x804020a03140d03180302030d020306030109150b1503061e010504120b0603010506060406020d0e0105090402030a0f050a062115020406020f0708010c080408090f0301060b070b10030201020a080705010b0607 90
    0x1d850400358a04101c0350508480c03240d1701e0044040c004005902c10440ea2080707020700d070080c0da04100041c7c004500e50702030340c2d160701030390703948500381c1c7d140e00e5613080d2110b001c0c5841810301080e800303641c0b03000d861800d208020403507402203064041001c0800c404502e556911603011178000302006183ea128800070382c03511002c40340055403494405e60a0001054840c5850340403101101d5094008211030840b498007038407070600300c00b03016050000034402c17254943c4480c00290310400603c1000149040c00d4041da004132180a029485018901502400401d0301c41038611040180c94003016821116880c04260752020050001ea01600100d000141a45c0000e5114881c044840550704e115448403249401c03034003183e0740680055003005c00318001c034480d03070000c20709a032014100c0480140c0b00f80221382583c00c0e980c0300550402e0300103030000038480c14000440e00f26400c0c0300c83c066141d1a40d00000d41d13440703130700310040c0000b140020300f4401c114007580304c0c05182e036015008a447c1e90f00c0703041c201 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 14368639 1250 14367389 14367403
    0x803070e0102010b06030c0a14190903150e0c01120e0f01091406100603020d0b040509030a0e120a02090907030f0809210615010903051e0717030a0804020a0314 70
    0x10740998202480071403a03150080959201d07104100317000e401c1001e5010700b03c0391050190307041400464200403841004412600d1006c90030b4107a01c0e02080c40349140b505406034141d10551090051509201c9401c1c00c07004980c8040402003460000728400584d100d1100130003420101c0314a9204941d0788208150301904102e480500071135403804001e1031280e6040c0c0b0303808119030402001c1c1240d1802e0081502075405030002d440c21510010f104d403c8280800d040302c400342c800941607400450007117080c9030b01020415603048180e5a03070702c800c1444010701c1e603a42c8100400034894808440064818181000550021074010f00c0c0034014014500705108154050401640607048200c43c0410500b80508542c00788050b0b0401012650740301000081c80582d02201d141c10803806010001c0440c000308811026003059102e49810740c3c07070001045290551590281004001c11401c810795400040b040c0d0381c40000d07034203024a9a54640c8000f074100e980319003004005641c030a070401e403202e000090388 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 14369889 1250 14368639 14368667
    0xc1e090906030b09060705070b07080c040306020a020705030d030b0a0e060d0503070309080d030c08070c14010f02030105040606090e0103030302070611070302010510170703020d05280c060306050d0809010c080307 93
    0x92012603c0e802e40c04c582d103108010018204000c1c1d0402b0450080c481c9000715400340345020242c0c00c090b1650398040580c1d004036120b40040e80900f1044c0210310f02807248808800e1103041c20461400c1120100303401d00030a1043e00d4001d90a8030000d91540c54484441401903070040c2940c3d0340c1d000c0c500d0080c00302c42d442c5c081c03002c10f031199540662040780640b00e001b0380781c03009456600c0c0a6075008008c0714100c2c034031070003251000e00f02889550040800d000714180c0c240304c0003000da10380d030404080c401110001e81c000010450000010040320250241036410349405140150f5100510306003200604604003610381c104100040540c149503041d0322960180544a5030032020f190f480f0800c43e01400d003aa04502a50807100c030820061625002040d029449030098500505180101c60500e030f010684d080024080c84040c00104000141080701505c5242000c0021909010214410030b821900041003420f0000342820168001d60030b40f020b20b54001c4240f035503454450802000310765100c9007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 14371139 1250 14369889 14369893
    0x306030120040e010b03060922080d0606080c070b0c0c03041a0306010318030504090f0f150302010906050309070506070602070203071710050408030a1805070f030b010501030c1e090906030b09 84
    0x1c1010203402e0300b06c030f0103590000d10410064954440c01040c0b1210f4036061850800c00c90b842d500000d5910026100f044182540080ca00385803440250030302400030724141d91100f0400001c40000c0701d561803c2c0d08941d20100b0300d601c89040c60300c500e00d144583d412404605440600328a501b004400c0114420b000c203030b800740081c550420802c41e101c3c80801006000c11b000344000d000c4c011803a402201c2d450740488001c9845000c400b646c01c11140b0750b40f80c200620301c000300700f4020b40d41c00147c1c540080840d0f16100d0b02d185490304600b41c603540c460183e58440c0000040f480c042c4200d81d010f40c2d2541d03800600b90346060750358a2500ea070210328030000c1c100038001c010070896603031060302c00d55228030b40180035503185640341041000104860031600f1101038800e112400031a0302001200090944444946110380c114240a403510005a210504160030100300c01c11880c2e01c840d8880244003141501101050b0120007902e030307030005402c440c1030107191617400014400c480a456004a00c0d90301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 14372389 1250 14371139 14371141
    0x8070b060406060e0a031101030906020d090302010e07031205030c0408031209010c02070e04020402070602040b0304050a1b08100c09171005061c110103140903030609070908070b0306030120040e 85
    0x1580c4c10b09400c540568840c1255404002044948039818480342c030514000030307020341b15074942040740c0161443d8007440e40c3e1081074400301602407042060a401d030308002d056403880e603606e08038803c03c0400305400b00a0f0100c086404c15500c102541c5c060300301a4140c9440d410040100001c50000b02d5500345035600345007007881454008140e50080c1e030307001142401255640d8003170001a500a6908071540b0b6402c000c00a442c2080001440c091403154003d0086000036061110f00e4007901801805801c1c043e80d8100a12000042c0300301900441b8100407a0469200328103aa541d58507521a803400c0e4883e9214141c10a40410304001e01c5e80001010482a10f844d020703c4241c0ca500700d60505c904942200d050041070140c03449141c5500305142c080b850300d4541e00314400d5000142c8004107164004428440c0703e21301081440d912100a1034982d003064502928555a02c03400c0c400c282c03c62000002007101900d0a4205807804030460326a10144041e903d24100742c0c1d4418401c84240781880c070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 14373639 1250 14372389 14372399
    0x9041b020a0203060109150909021824090610030b0f091003020103110906040b0c0307050706080f13080f18060c03070510050402180a090609050c012a0f03090308070b060406 76
    0x100c66206007e000140700c1015504140802c401440000d405036030050314441c8201000204402e158032884421000249400c00d800d8000b018039100307480c1074454008442000550348518a211401c1e00444c60042180c08002c8081110401141c1131141c220302e08504100303c0c44141169a4100c83c0700381e0301004603a907807801c0c2c400240502460107a005d1400c203c00c00c64101c51502605081c40c240c000d80b46031205680e507851514003540c1c854004610407004001d1720042002d030041d0b00c0040a03c140800f1344040d900c50200e442801c074401481e810120300342000224280301105240350140c103095441c00c0d203004030341e525040240c080b11188a040311142c4110114022030703004603030180c0b02072078410340383c0c0300c0c024200001010742c2074065441c0110000719020f0b010360580d160051018100251240000401645078220034035060300b26460395180c92504101c05034121078120404181420361031808a5000b441d560010380820008154841800900e551041c0500790895007000320660b61 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 14374889 1250 14373639 14373641
    0x211203090c04020702090c030405070b0a020a0c0510020a03030218030303090604061d070509041103060a0605010206070306031a0403030b0603240f010f110309030106030302060402030c060403080403060209041b020a0203060109 99
    0x1364030000d402080000205c0d6010045d803004d5078026208600b40c82c1059190184c03041c580d0000e0319a1001070344140d202c507081c8100b140e0044041d10f4191142c21400ca0700c132a02944d0350900c90802000c040e070001c1d0f000c1130009041e0300000395120007010303207a4908090b00c6680e03a405040e00e00380c80591414000340c844175200d2080421000070b800203404020b28060421800003030041003503031580710345428200340d540d082c00028411a000381000606900b402c00080c40c2240050628050615101c8103101003072410140c02089803405550151585d91071408030003a003050503400d60002400b00c10300040010001c402d40030200c4c0c40c100341c116a103010042003c2980452400c0d408500e61401000e8240d2080f00074000d40000c4008491421099030040383c2103805d540d02c20340040c0c00540502c81140341c1840740404c0f80d142180c20034105802c5071a070209520591100520b0241e0004811880c0c0c0c0b51508004880010b6015072540c40ca4072500103500d62403d014201d100b0b00440001040820305 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 14376139 1250 14374889 14374897
    0xe01060302030a120905040e0303070201060605040501020c0d110301020406081e01051c06060803191e0e010f0903061109010f11060a200d0c080901060305060402211203090c0402 78
    0x10001c000f40007180d2100c0b6466202100f8072420081440c40100380344e161030080002101364031005503644d290104000b403c54450342c109004100082100700143d03a0300061186805804640001e2181c40e41e00c0c011419200203064a41c00d5400824000303a0746802c6080c0380d01c10b0700c11054882035a407080083c00300303001e02401103036032240007002d00348480c0220000846e92a44690000a401030321584d04910f160020320349106509403650004001ca58841a8001000011500c0181c00240840d020b0b000174000311180d410412442004003141c0c4c0301d200380000441d0040b0003000000760850340040d0943c42251840e01003051603c200f4800c52192080d084403002c02c2000d04250748580603442c4c003178075140000c003054200e080c07104910a40f80710014480c01c4d9040d140080e10827a00f18000e89200c900502ca00341503403402e5401c102040021401c2c3d50300640c100d0340f00c860045a85440d002c02259810507820314820805a050f0790080a001075005c2c52005044501405040d000c02090b846 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 14377389 1250 14376139 14376143
    0xc070f050a06030b030a02030a0602030709121211150103030203070303050606070c05040509010902040e01020901020d0f08070e060f0d0903080a0e12030702030c030328050115080603030c030c07090e010603 90
    0x10880030104540b91281e40003641c1c0c6000141500c0354800c040d0000703450030071076540c1615000ea0000a2181e895000380b8224002d00145000c9000c406141d147d200a80c1c003207500354824405203aa08010440c02404491030391910850080d102c0e5869003002035480d0003650044005c640780c5000300300070f45400403e031944070b40d1044903811000d00300750a00001d0540608005a40d64072510120b00596403401030030700c0c65000c0c000068403000218002860306a04085140900491480c0d04d1031403640710b034549901c80b604d420103500710050403020440314444c06598510701980800e450540c5107c075040011518002c0e41d818041e926401001400c880c2a014900c802d580050341c9445400907180185a2081a60055a08103080d80f20f8090540e8012a588400c803070206203120036550685441c0403c0b5520114100a03542c100311150081e4200078400c141405017140c0010f000d07540400864550b026900245c03919a01d1280340c0994450b454000d00812500307140c00b04109079414400c8030122a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 14378639 1250 14377389 14377399
    0x9062309010c02030f03070305030901110702060307030c0c0f060e010f02030c0a030504020a1d040314090112050402030f010609020a030605060f0f0f0d0203010f0302190303020c0609041407050c070f05 88
    0x30212400554090118074000c980500410081c135000c0d0005201a01509010303491b480d94a01d4442c0c3e0050071240c802c542c0c50480030003440740102503101e0b5419641e00114034140059800c100e040c003501c02a40101000b490006520500400c007c1a074000030b11f40340d01c0c1c200034000e04121003405001d17030104681030411044144034a488140c80381d0003068000d40090443d009503615080d5103041042d001c103003c680071200704180400c06506c02c2c0d8004c00301546c8100c150401e5203850008081007019440070701001e84860204040d55403e01c14440c1d040c1c800002042459640e940c01030280d00030340640e40c04a841c02d900001c2c0e60520a08a55202c400f20356280d00e00f0b07442d001c140c02e00c1c0d0011403c4640c008003e002d414642e0801e40700030f5010b070041e5520f00c0450351448c410001d40c21030078200c48494600c030300f204200082d0002807110130174404845040d158414440410b008019142a401d101d0740c13a0001c1c465402d0b0800020701181856509580d503158031178a4241569030903100722501b01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 14379889 1250 14378639 14378647
    0xc110a2103110106030c0602070e22030e0405191103040206030a02031003060e06010302040c0c020310021606061d0c03010602060708040602070f06050106180305120f04080706090623 80
    0x101100840050314801e003000b41502454203070007400c41c1d0075078008664000e0040d009000c11034041003094014440300340f000c031841c80c01d0300c140d00e006540076440714282e0084041a41c2014046c10701340030b004201400801c01c3d85861b4010b20f00b030710a64050305100742c0c07411076520040c52230f04003224852500540040d1654542d1103190000303500c0240060011903c2650101c0081c040380038244041e5000c100520b625411401000100e620042030303503041c01042c03001d903030050300c0c0441c4086200d0300b00b0400603142e0b403050311541500c5036898402080305107843c02c003085170ba1039800c0d0740f501501c2c89400d110503a42c602d4400c3c002d510007802820b002d60722400011b4134003031084101551041c854a005810001565640940c6d0284940e080b43e0040e120740040c000258049500c4103e028003203041d040712851921416201e07c100c01a6602e60040001c012440c0041082194014a448011140096540c0c0001418014140660400120151040313409541e285000510aa000200013850 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 14381139 1250 14379889 14379929
    0x2071202060c010905031209060604020304020d030e030c0a09050411030631020d050c030c100f050f0405090106021b06090a170a05010509011e050c03010e10080d0c110a 74
    0x454000c00242c504540d01c50346a480010350510240c5040e10070160f120081c1e0801a16103410404020b01040c0100e206004020140e40e504050b881c5807030700350600540441410780402d040810080f141900480050780000f038501f041c0d44510700c00ca0240d044210751703040b0801090303150482a01c01c038055600308010f0040c014417100f901070310300c88580c0a6210608035517020881840c6480c0b0240c1d5240c0000706da006450138103000181c6003000c22600301031150740391040a03140c41c40c07034400c0fa004c015001c40c40150020f9031504503006014010b010102e00d6030340d100029070b00c11078402014a11840d01032012210308000703081d45c1ca851b000801c56031001d030601c202040b40c07039107250481c1c40c01c1c401c1180380c00106000781300e1031b40901e03181400801e0b8402100c0801000c0c80319043d100c0c49981c40c000401603040071314420389054035491080c402190301c0c2d4550090071202950840308d0030b0b018501c88032070010303080142c451207103100d2000c5545e19242c0c00c0030810781c50300c548502c032443c0c82a4400801c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 14382389 1250 14381139 14381149
    0x2010507021507120c051b010503010621020d05070210110306010c020402070b040302010b01110303010b16020102070b0309010618151703040812070203010e03030106020c130e0102030f011502071202 87
    0x11070080105160f00340145621041c22442c3d001d1000804140082d81c14801d100080c4030324822034180750782c00040c1c4004040001c0c01840144600c0c030400080c07145903c40481c1d44070700081c1880308204290b44400440c4c1c0d03004020801518000050f1280c480c2400d01e030480740c011070781607243c0806d23018115030722100159245000600c5c12a8010b5013001081c0025405550b514010b90103a400010b1120a08001400e28007001c180c540e5594400e00c0100b04640300581141c040c00c2c0d9818004990341c0080c070040c3c1c41d0000350307000740700071a40100400c00000c0741588007004440e04d20300001e000b0602080c2e60030803903000403c0904004180714040c40100701d030301c0f40007107446954001c80c0c0c80c00b5920840f00303050000c2c018459417000000138544041d403409016403a0004071882c060b500c0c55142c007401a545e542c40c035107080d0040003151414a034080450740240200c24443c4021341d528070f480b007050b0001d50001d0080c0b4188650008104042d588006121030030744002c03d1213417100b9030480c3c003006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 14383639 1250 14382389 14382409
    0x304060c0c0306050405070302040c0e060304120c0b07050306040507030b031504110301020d021b0c010914040204030c0b0a031406061b12040308030403110c011b0501060506040f050a09090201050702 87
    0x141d0020000580000010403511038a4450b43c02140500b24007400c1d44100b0050b200d904c2a401d0420026001c03d8045d603940320102c0c0c0d04180d100030701600841c8001c00544010940c00f1010300004d04881c100803c0700c1c2c116004600c40e400c00ca8040225035140e10040c3c080720341e08403540f901940480200251002e01141c019041350080074080b40130110000003d00360382c8148054020660041112091509094142e60040c0d242c00040c007215451800024036210309403043d03030021201c0890303c40340e81d115541128040d6030484a1001035980710b201c962416030009407444006460560108809180300007824081c010041400749080709200c1500c2c0d90000d01d04a984446c050b41610240e001c3d0008000c00c010340c4920350180d100e00c1c090901800c1c10803c648400a43e4114151541d82030380d2020001480540c100c040d00903e0449040c10350040030681c10890308180b0020f0041841c003440142c0c0411140c0454001c0080c0381c5895000c070680340e00820090208070248410b200519000e1451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 14384889 1250 14383639 14383643
    0x30f0305031915060305010509041109070e0901030b04020108060a061e0203090301020403050a14010204060e060c0a0506040309080f070506030105061e070303020310060e0f0f030109050709020301080c0a06020304060c 95
    0x4040910700c411502c8085034040c600c1c0142c0c451041c001044260740500030700b401080c0403110454286445e85407a59000c501c104814826540100014000c0c1d02850240c501c909c4050310b54200e6684a10b446201c8010554090307020a156a000230894502000710300705840e5584c0e503100d040c4555412081c0340d184440200d800713502090208001e152824400303440210300801c001d0200c0c2281d400d0072841e002c904000503c083e40100014020350703821118000f2100025034110b561021a1a903142c00d152403d00002c0c92400b409041c001419400304d041c00c140c881c80d900f07880c80304081d81c038074640d5582d1510800e6040300041c401000185080380207080c0101c0c800c1da800d810b5000d03481021007658040b00d4101c0100ea40482800b0009c5041c5c145d00c1c0140c8044c1c02d00c040412100300c00114900c421800291145100c01c10f80c050541b029000780400741c2d0701408a0b55410f842d003007100b0213034009016000c0d10340714110001042c0d05d01103140c04200c44403138000c0c503d0581020021a038940700a601 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 14386139 1250 14384889 14384911
    0xc01030b0d0f0503041e08030406050d0207021f0206090a0201080417040b0a050301150c020303030f060a05100201091101020d050301030f170406030c08060405060f09151009060306060207030f030503 87
    0x14000861015040e03180150f1180c005503a13201c3c03c1ca250303c8490f90350300c030544946c0c42c100e800900c1096400012141510a2402c000c1e4403100c4083d10800030b80f05425000b50043c0b044202c1003446841c003500f000c0d800c01c041c3c003030352450350710505426501e00c11800080d0000b66080c01103000704985500c0c2c0010494071000035460291200c0318040142c0c000d01c8038900141c5d00100412082a0401311841000e080d49481c88078200c19400003952404081d00303041810381c0c07880c0816080d07a03904a2603001050003600100040c489418042c2c02840701a8098401200094011a41c0c0d8400300d4204007183e0551a981c1c00c0d6400c540300c09a0501c41c20070102d030f0817a10b07482d404c8800c03140c40d0040c00003489160380103d00a50721400042500b40083d00060040d8148400e21103071790b0300c0c1002c80906c444280c1d03140805076150594800c032710790b41d01c2d06e80381c1103207819901c3c0c0c24840d4810820010740344242c5040c029940e84107002caa40380704c40d01c0080c0070203000605050001c0e105e88010b5400c41030741e2103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 14387389 1250 14386139 14386159
    0x30e040212040302060414070605030105130905240105040203040506130303060801050f06040c0212030112030c060501030305030402090108030304030e040f24060201200d18060504080d0501090b030c01030b 90
    0x41280c0150251402e4004d40d000d1410802085649410a001261618040c00b1007a19004003e0080e0206014491040c030404104640b1022194020118903400404490400c2881d40310040c000125078014582c00c8503e03000840d05091034001c90340142d52000040c81250748654110041c1e404c0104201c04060302c43c0d03000600c070780f024080c45004001018012000c0d0a10104001c200c40b9800b041c4000d54202c08410030b03451100c1020b882c11211440304214180c0242d140c21203491013010401003110349084008401c0c5584140550300c00d510035940c8400c1039880b00380440d0ba80c0011100200002c45910302c03480f0604041d048041d01c1480000b0200350301525040098050fa610708012184244681c002c002160f824098840a42100340d4160002e03090324010aa10340300e110f4807002007546a00e170303410941c0c400c505119615a00a0410400c2e402c10380340540a540c85840c00c0307440d65062400100b60381805214801a4900003402001d103000c0380c400644c0070f040400358580e88044488 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 14388496 1107 14387389 14387407
    0x7080901080604180b0603010f02040e16081308090f060c06090c0a0308030417310e070c021002030405100509030f06010f0e06031207080703020106061b030e0402 71
    0x20031700c04003698803400071a004d000440302c600030300c5100203000580441c080a640b8000c4010007107080c0106c2c0081d07401c07114800c0c292401c04c02c0700c1a104d0090002003946005007206039000d004440003505103000034005401c246a5a403060300b00c001004520b04007800300340c0da1800c0131540152a24215290003a080c04000c200a201c084d22940050f00603214506454600b05030b842c11404c0760545500c01078941010184080c43c2c640b1060700070440b06215800d1b40c2c801c82e019950010841c407590200404640380c4c2c01902d0a41c002040003140644801d28001403542854440b01d07680e164180c1030500c1c03e8025043c86a454201000501c0742c0500901c40c07404885040050b022a5280c10000a060003aa1801800020380c00648182084490f8000d0480e20340290020420703540d964505913840c14161001e00010345000d030303000c00001d020b00c0401c7ca03200000340c80117062403942 = true := by decide +kernel

theorem cover : BRFrame.Cov 14208639 14388496 := by
  have h0 := BRFrame.cov_init 14208639
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14208639 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 14208639 ≤ n) (h2 : n < 14388496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
