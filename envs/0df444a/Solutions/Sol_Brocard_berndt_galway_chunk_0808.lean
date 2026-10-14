-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0808
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:55:17.472464+00:00
-- url     : https://prove2.me/submissions/a36baa54-9439-4884-86c4-09701709d245

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 145143884 ≤ n < 145323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 145145134 1250 145143884 145143893
    0x9191b0306060e06030f0f0c0411040e010602210f160f020303030114030c0f18130b0f15010822061d06041407060207030f0303021b03091201060b12070903 68
    0x11060f03008041003000c2c11080016920b000c0104070030307010011000c0d040002c3c2c0071105d107030345100300c100070391140f0b88668540030180c0d1080d0a8400814050084d88041c0d41c1d203840183d10795081c0c99924402c1202d41c9040075107601002c1c100d8480328502c440303c1d46031105041500d401c40705140c00c11155108111170b8032000d66001c002442c060842c0c0c0d4010700c20602c0c5041010324084130841e281d80610055911420740d682c440c4096140f807103e01000d4100c6643d02c0d10604403030540030000800300300800c000e018266141008040c860601c620f00c03404c60030002001074510340d1040f2440d422008da1051001000ca0703101003101001d034810b02c40824000c0b440e50183d648804001035414996101c40c04220520140d5262520720340c1808025118880c107290009494904900002e0940d90706840f1100c00c02d0310070342c116081b00281e0700040501010b0443c101d0707180c5c1e100c0c6c14058880c0c84040009541440c4c10f00c201c1044a61070311020703241c842c09128803240004020205418800611000400318 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 145146384 1250 145145134 145145141
    0x512070f20041505040c090f050d1407030b0402011413090e0307060509010b011b030f3c02060711030405040905010902060703030b090106031a1e06070605010e09191b0306 75
    0x1003d0000c1c00341020b42080140000c554610881c0300070459580e104022007007542c2800d100b510f4050b64140807044550070f103020180e50050b1a03c0f8244206040001441103081d0341c980101d100340c2e00e503141280314100401c0640500410504480c13080c0d0703c2005102c00365030140e0b0340a01c198081d01c1c24501162182070494004460024590b511003852080d00c1d80d12041c0b801051a41d4100c1d40da00321426100184403007002c42e4020140080c5034a00b1170f02c0e0186010508031100700c82004c0d100a042c81003400c080801b030100c18400351043c1c00100d114180181c0e12208103110410095041610704010000a0310b40b80506030350315507070ba54212015031034640007404094041e0701c02103040081041071200c0c0a03016444007081514000328442880c01e03681d900c4408038411a042c900030500002d111061441e4100c0003136100c42d0028901c41000100c3e04554100c2c0c503903610151050380d03020000c40e1a4038210046081049900c0350150001e910303603e02c6c0f204081c0d0a018441c03100c0d26175036044201c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 145147634 1250 145146384 145146401
    0x40203062a1308010608010e06010b1303080a051206240706020f19020c0301090201120203060307080336010905190f03150b030a0201080613020c01020d06030512070f2004 75
    0x600c81044800e1000f08400d0190100a100007002080a40524a1b019481d01c0341802403100ba40c100041c140c4060840000b16005590090318441c1c0e100c2c5007680c042c0c033030b83c40003248000c5500c2901c0029481c1c5008041c039a5076a0302e590000410040c1100c50308003540c08100125001d5a003440701001445120016061401e40007000860b44080450041e25000e0300b110a20b01c04da040030394000044c0d901140c60f14034203148074405a20b9032114030000c0d00b0070105030403132206480701080ca031181c909170030482c40b03403012403480c203141034070000c3d090004610100e0007180c04540300290420030b60400d00940060100d0000c0c004010326250081c41c542100c80d64400e0342c403412210342e04140b441c0d80b0301c500d500342c4400f20001d010142940d40064035188004011911425071815144051107040d011a0f503801d2034034008540e1813001031403035002804180000c3e01c141c0305540c0400100b602c590100c4800756084180d5016155250350b890072580f400705509850061825481300702070b280e074094ec210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 145148884 1250 145147634 145147657
    0x151b0321010f0b0403030f08040213050708060f0603090714010c0c030308010302150c06010603110f030c07050c0a031106090a0302091303121107060c031409030409060608040203062a 80
    0x3015490604202000c1c0e58a411041c8400380400c420800a90011140030499809041510507a5194000940c181e4402c42c540385002d0f0804041150180d0722000e0701d03100b540101d5001c0091541c04043c481c41c0e0100311807840b207680c01250240003c180f42101101e004c901403400c543c500c4903a50383d01c03103128055072003100031941d01c40040c000c41c50300260b080c00b00c0da000000581080c40c100c17a019600c03e410301c95002415501d00440d030702460148211194800e0f0703040c03110359a00b400c000500c003c0d489000290740f94002e2486841891500300c030840c04980d044014110007030900e50410030075030701000001e82d109108900000c0180c071980c02d00341c03144c2108403011101c00c0c0682000f030095600e18010758101460502110f85200b0b0f40025503009507008040010151920b801c01c2d802004094090030301680e0725420442032a100100610a482e24124240030465a58405440f143c8080e54001d502d504600c00041c4202c00801d00d080c03035800c01c1d052620108241c5d90450855a114040f0401c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 145150134 1250 145148884 145148947
    0x70305060c0d0e071403120a08040b0402060c0d020a0c0f06080a020c1501060c0218010501050418110310090b190306020a020a080d0e0c0f06030708180706050306040b151b03 76
    0x703500d1b19051054448919aa13484146096203101001380802e0004000500400802e404142552200c40035110707410701c850215403800c2584a00a135448801420440d19060701080c04110041c00c421030320100c5100380c0320250b8a845041c0d650001c0d4100075421201440748400c00031034201d0190a590007400c160300c4803410344109006001c92501440b10780039540d00c01e0b1004000300d0342d00c030084604481120b2880c4032441c804040010241c0903c3e480203882e035001000340b0030309040c0d58079818101ca8041c102003002a005000f8400401420750070348140100c400c00c1080441c6082c2c005001000300c5205454601d03d450360b440c00d29422075a6041d00c080d0740c0d06061a80410100482d29103000100c642d0014611300e00001139962000414880400c2040c50205800006124090034000d94141c140c03003001d515080001d0558008588a512881c20890510918100440d01c52501040510302600d4801030498610b00d07080000103100191104110903200e004e20302d40010483c2c0701c840b0004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 145151384 1250 145150134 145150169
    0x603120906070f020604260d20070914010f1a070602070219090f0609021e09011403071e030b0f06030c0d061202122b090801020c100509070305060c0d0e07 68
    0x1587c8410211041030456104120801c2201e42113140f03c030300c1c82c100901040c0013061a11030f02d800c0007840e6224401e181c0c20f01c00c040d4001d04c1500c510034180c4222140003100140e17580c0d185c034102170148110b407101000c00c00460000c0740d0fa82e002801c01134000b8000c41803240e6901c0700e8a01132031544d4031103441c00350b942141e06000e114500aa8000b020800025030410f0300b801400910840003580032400b5800018041825901a81c03030020180d90060810f0303242c1c0380000303003d009164800c44201014a8000d10300c03108900a20810341040c038068502c41c80300d4003000601010b640094842006610103001302a0705600300c7c0100700c041c119481c212214a4581d00c1801aa01c0b0245ca00c461660030401000c4102a0384580a2400d01d01518403010710010201c800e81d485070329a00010441d500020f00741c4e044050025001c071300e6000141c0200000d981c0c03d01e04a890b90801c0c0802072484d0400300c04180b070303280d401d40640300310742c5100340004034001c48100241c9030520079400f5801c90803504004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 145152634 1250 145151384 145151429
    0x27020c060702070f0b04081e0c06030901140a060608060111070801092306010303210b040905030712080903040b0c0c03010212070e04060e0a091403130e0603120906070f020604 77
    0x4c0c0200301c10030b80305041c0b034100118aa03e824541c1c0d20703c1e12000000c44808003000c010820604001d1020300016540e0502404003400b822080000c01d0a0083c4680030411059191103583d0803191741e581d514a10351152801180c1020340c03c41c1001c203601c07031000040344a8a0138441d031000369124640e0b9010000c05409409400c4a00d411141c403980c004000420100780c100c110b00c0c3c440d9542824201072600c0100c81000200104006076802c1071401c0c1050b010000008010201140281d1801e0b400c0b1000e2001121418822981d00d00190424842003144030b140e400980002d0b00e544040c1c3c0c01c0081d0766000320f400c98014000030701c104440007084c04040c54111401c81c0308010f09450500c03025081404400c42050068140c80a16540d0382c03548003440300355160941c000f9021070589a81e044030189a008003040ea00511616a00020118002e07103000a06c076035001100e00340301c0c0c0c2440400401c0010640000c1d100ba9854004901c0440050f40e0b4400144054428445c2e404010114640c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 145153884 1250 145152634 145152659
    0x15020a1a0121060207050d050702030f011a0d110d03020d0f02010908040302010c051509010b180906040209040213020c03030f15030c0415030b010b03040b090727020c06070207 77
    0x40c04411031040d0801440140380c0c500c48803241094030711601d000c00e201c0e85801002445180d101a100b405026003403a04164018028500580210112082030b0802c80c605400c807032481280c00c41010b641c0040450340d042ca851400c611900866460440080d40300201d1038441e526a0200c0042c0c1101000703583c6103030020080130041500788001c00030201c00e0707a50300000c0e100750700020781441448403580301080741c1005072401101c42c80300d00f2102811b11031100d0340a0602040100e02c18019039803456408050820700521400054000b40400c0e1203580900c0f4000b400908180e80101202c40003038807079400750004001075140300c0300555a80ca414100181030700c002900c00e070440c52041040c2d200a5800003881907105c14104c400190744841c900c0d14400805603a0320050141c1c12650001951002c4803000c2d42c4254000c20030741c1c4440e611450383c90b03280d02d024060351150707072004252052159a05103401913541001c0d0030061600000402d86490650200c90050041e80001c10a100c165440038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 145155134 1250 145153884 145153913
    0x60603080d0501170706140408030c010e010f09020f040b060f03040b010509010e0f0f28090501060b090d03050a02011d010e0c01051305010e0f0d08070309081605010e040615020a 78
    0x4003104402444c8485880d15034440c0d204074010021000d407203142560342c0300704842c0240703000c900b01d82d0384da50b820a100d40600b00e90b18100c40796501c2d000b03101004d110a400f610400300d90050275030a807400b0040801c002001078214a035001a42406802c041001000065000324050b1101c05041c0d0b140074200101140140c01040720540d00c2028031103403003041500c2d25000311040440032246d40c1d5205203022202e00c9400c010020301e06080c81c0d08842006580800301c014040d40084c404142c485040b14294801c03a046640c1282d61107443c8800b003803048000c0c29609020384008541041c038254068150b400c82c1304000700c7d0741d40d40c0c10142c400c001c0030008a10b43c100207080860400e4104001c496000300244916414007080315120103455a43c2c900f0028402c0004043e08410a000d05142c3d50a40295a00b10081070b0b00d140d004c1103114002a0340d2034040041011491410b007000011544081031200180e00592600004500e9980e113142d400344924582c3e00819201d41c407030810301d14021031030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 145156384 1250 145155134 145155149
    0x3020d1b1d0a05010f050304020d0203031c060b0a050702060a03020f0310150f0503011e05031b01080106051303020d03050712020c040c0809070e19110405040b0102010506090f0603030403060603080d0501 89
    0x410b003080941d810500e020384003034103411b1075910313551903001050b00c0c030585000082d818080022507224400f40c0301d1060800e1110010304014550700c0d10a0500944524840c07400071a000388216001850040000c0124003810714000d81000e8445103ca0802d4200759101c0c0e000c4d0030b002d0f0048c81a0300c80c4a513507c0d105510b03441c104800c0c61a054001d0464801801540d121022060740103100b00340c0c0b080204010b040c082d049880c0198030380700c0160307c14000d0989900094001c400026001e21810640e422600d6102142e90f203145903038200484110a0305007201400001e004840c0820f1240c150b000f64a40d00d0b401410b0100400001c01c021142c04940003c20300006000344444500700285040a80303251180500603901d500d065541000400d5070b03a41d59a44c00c20440050b02c8610101134400c54505071020700241c900000168282d0304111501038001c4071143c00241b810000d1309440d81c0042015095a00d4144c498403860182c0c0c845410546520b2400140d103845a5000e100d81d42c0100301c034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 145157634 1250 145156384 145156399
    0x40302100c0c05330a030c0504062f0d09081002070b040605060105190e0f010f0807030902010e130204030b0604020403051b0f0a031b2403020d1b1d 65
    0x407640e0303440e11030b51203014290140d00c107000ca90307105210603000c8074a0b035014441210303440c0a090048162a40c014021180000d09240c4007410071030041080c1d60a64450b512141400c0e4100c2d040322804a4480c5120f80036110070400180000c541400a07290f03c0407035580d1003241c241046125850812081680c4035203070720402a10000c0b80402e240d1682242d4002e81c08160350712200012101401400c040c414440e42ca40200390a80790070004903501440c0543d0240e440c01c0d00c1c2001580c904080c94240d4000c14403a000045c2040d101c0c0d40301c0300125205060802c0c2c034000050102c1d01d00d9a40d0302c030b001d901c03581c0014184240010400702c190300120456080d480d290660b91810745580d0f90710004919080d4022107205c07142d8600185d0789851101074068101e469603030602100c00b40e521101e50149122000001c160300c02030300e1210304031220f000d100382c0d0381101d0000d00b100207612107485003210555034000011004040944000d50b0350041d940e80507003109040e0b917940260080d004c4c451240c0311 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 145158884 1250 145157634 145157657
    0x706020307031103040905090604061b05161b08010606030e07051c2a05100e0907051317010e1c080403030203090c0d03021e01051e090f01060b04030210 67
    0x600004841aa035858506902c81d1032045200ba483c501498200010040c100006c120b0f41e41c00c00260244260300034030042c000d6030900f0031410800d00c204440c0c2c1c030008034100900000c110080100410080c45039407106c92a5401054071311034001380b50440c1d41665101e282c10004198580104070b000000710001d022144d24060006140743c0c03030310540840e00702c17280071100140000da481030b240e0107203500304108c1030601c25040c0d031030803c0990003158801c800031500701e12a030f0300c66054003c2251001e80026010749030f43d1000ea4254006072901850307074010200c040740d011b102c1859141d00002d124000301e6100301e07400c0940e080c00024610100d02a500c60121104150300900443c2c01c5074050a0042c1d50703458202e1194100f00440005c0c3c0e400c4568800040101640003410b1145001c45149101ca8280000011400e94100791448407017100c000c0b010f2a0410700c1c0c00e1896422107004000c940030001a01825402d44000c1d078032006100c600410b080080d0305011034480310750744044c40c20624504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 145160134 1250 145158884 145158887
    0xf0f030a0809070b0a020a2f04020306150d06080c090906010909020103091a0105281404060807031110050a1e050d1a040b04050106053106020a0605090706 68
    0x640a0030904002041000c51001d040a116100c050603146802d45c2d695140170784040d5840303814400841d4503859880555188520204080b8801ca40390003d040f410f035070080410004e50409841c003507010350990340c402060300580e0020000b40c449190007040c8103117803c6070303281081c5032010603900034001300c4104403c00ea0301050030b45c196210410001421407030307070004070010319880000900d640440300408030413004040030a412140c04940c40d045403168404044508007601c0302e608848007544505210704420181c4181d0006409040014070643d110300c520702e0164940c1c819240065007000c20070031410410f8209483c0012400c241c0d24000303482600900002345200382d0640038001c041c080b50310314411400ca801106481c00c080c4035540000b1020b0802c0d03541c8280140c410f0389041e220801c0e50416000d04d5048a0007521a18240908039600328081d00f07002d1848040e140e141001c64400040b032981c8031002d04003950040904010070310f440c00840d20080c000c0c02060f808010100900d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 145161384 1250 145160134 145160137
    0x109020916020c060307030e120405030a06091103070f090c0804020904110d061a030c030d08011811041421030406030e03090d141b01090e091005040b07020f0f03 71
    0x1892140048001c0c50300000c0807810403d00301c070025400783c0f001080c030020744da041d0403444e645c04100042d111120082c08444001e40300f80d1003601d0300354019404400101c1e2180d4016513a05000f0b0302448420b211800001c1d00b40201500010307808501f40d14248a15911071086500507c00c03410300044905068000816514000740020408900e000074483c01c0c3c0c03a0342490203600d030b80c400d41c14048492402190380001e00d807904554001d00c1340c1e25030100f45d4540003900c3d000c419906c0e154056175900304100c14bc2201d4a10035118001c0341c4655141c0100c40d030980c001d2000340811410510040c0d00a01003080303061010003031604000c01e0080b0f414081d4000b00441701229102d04000445201500d0520f0541c000c4224a80e4442c1c40f6400740400d0100d01d80c2a015108845006c0d10000700032210911300101c50080c540d400101a600c0c24801c9d140d030520035541284c520b00031280e00c030048000c1c0c0401d8070b808450848a962040052050f020303010040c3c81c02040c00000035010102001800d0b9980c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 145162634 1250 145161384 145161391
    0xc05070614090d031101050708010612020f0f07140f01020307030501350a0203060c03070f0f05030a1104031b031704030209061903080705030c10020c1507021f05010504050901090209 80
    0x608101e52030307030b002c060003041903203111008500280b0841c0b9041b00e001d402c2740400d120312070205070803201d00c00120f01301d4402c90b0013101c4003d0320141042182022403415030000700782251300c02d0a0030790b102c10080081040380030324400100050b90382e01d07007072400500780d45060780000074503401026001c2c0d40034051a81c40d44100c5600c1801c0c104000201480c42ca4100f25050180d018000d0300300f03014400c2c610380003c520902c02922442c88044044a04640c0c00807200c011000188003807020560342d09080d001144000d40105041d0705046d02d07500c89904060307200f054071144003e00070040007004010f03054020503801102189040c240365401080c594030000304050310400e9210480301038005c0c40d01003c03000d1a042602180c460b000e500e0081e60b01e07401401640360134441c5201c01c0c680350f41d080c022910601c030101c02415008501000b201142540500328105500400c1d454050000020b540036505003840000031800f03514080031f0204451020305414101e9040070b00020240c3c1300c01b02950340 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 145163884 1250 145162634 145162639
    0x18020408100506150c060402031603240f181211030906030c1605030c0105100f090905011103150a2112020a020301090f0b09070503100b130c0c0507061409 68
    0x1001c0d030710480024110100c004ca441c4411202042e0300700c14800000303415104a10940403109045082070401e000d45034584002810b888ad00300c2c44c1d142c10303884050740d03d031300c00b08030b11000c01c224018a80358016994400c40d842341050324507020005100104590742d003010110309296a00c80001007803c2c0c0c691003140010390145200201003a4042070440440d121a15980100c61190304907142132a201d40c0308240d40e08041d03003880e000c039004070b41e1790043c60300722403030304065000345490700c181800680070500058540303550300ca0f9080a15482100103520800c240402041c401100c5020007503198900e4102c03810002c0000d8405074140545c4044d10740058200e0176030007590403500e80480c940b40a00c2ca0081d00365080903640b00800811941c10042a40700380124205a0342e00c440c005e980380014451a54146d00c540720440c00d040c0360b58400560058068075001d4180e518480c114142c603044c941e02800100c41c40141400d1210501607040078010914200c4a14a074031611424103000c0e4422992 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 145165134 1250 145163884 145163891
    0x60f1009020c0a080409060609080606031005061c03080603010608030313030c020619081b0307020d110f06010e1503061009020307090315051b0c070e041a0c041802040810 75
    0xb6011004200e16061990b20040165440d910f0b000908042c05042c070448010404100001c40c00f1400402c40034894103001e0010405820417500c924003034803002e8046a00441f152502880011035024500c54a600a40701c41c0301c00e0801d00149800c403401c42d84104040c0e0410b10074065007040341001183c6194151070130801c40b00c0b0034000250301b441904900300b80580780d000e043d0000e9400030340051103402464440c0310481703883c100c106c1682c80119010001a00414110807600b1700074902c04580da0b042c60110351071914241c0700d69160038405e810421030101d2203010007906801c4d0000e001d48003a0198064111414080000c1d02c1c6036a050068418840d0003100040d006803003001c0c0c0b1402581c10651020040f000b8502e1080200826500c022000341290600615400160100c5181640d044c1c02803024030719003104608d14142c06001160011901c2e00c8200484880c2d0407070b0340c081d000c201c010940d40e070700e00305c414001070100c5122100c07005c4c0144410030081d0700c0400e038984800d0701e801c001b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 145166384 1250 145165134 145165147
    0x2120d1403060411031807090605031e01020c070b090a060201060b0a030504151a010807030c091a07020907020f0606030d050d1805120a080c040311011103090a0314060f100902 77
    0x10b006440c4e54140c441031500040200b22000e4043c80d1002c0000b11000140e68a490315a81d140058951070f0140c5034150348040c86007451a080035a000c03500e0480100011304265072071700c0d6981000460792100c0c841c3d91011614070310310f00e4051403480003081c0500007007111500e0b003021f01400e8041c00718003070240350381c40c00050140007200841f10500c4c580d81d501003142d00309044c0403515910280d2805400241c1000c0083e0b10a07009100380d0f00400f20742c0d01c0c0c20024a10f041c002d440c2107291040ca1100d194024807110b0010f85640c0b1841c0d019a046801419000c044a01d51a24041000308641d00caa4004030811310942e42101c1210307280b9203030380e401160b00421175403c010940b1440720010100d11441010003802d100c00809056958a69542d01501d510351085904071030045001c0900318042c074091000e89503008030003108600c140142982c2c10078150700002440c111090703105490340c03005c0920024403404141300807a0710a00c4002c418045081804403004142660301440f255284d00051300c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 145167634 1250 145166384 145166389
    0x3090e150904050703170703030f060506030604020903071527060e101e05180a0f0605071a0a05060901090c02071a0d050a06060305090f030a051602030a03030902120d140306 76
    0xd51301079900201c0c0c0e010541c0c01c080501e452640000c01c02d90001c1d24000d8964582062400b40c101101d01c02403006055803512020807000b98858030b540d95061246070742c0010070004800941120005035120328511201c03500c0d14203008202c00040344000410520b050050381e4110321146240d1200741d0304071400810094058611400e80c000590560710340d90421080140c2c840020062010641c407502e403000029400d100d01c008140c00ba00e1484405100d09001d00352044c005400c425000307491480188118802d06036400e0400d036424041d0035190000c00c0028100032250303500501d1118810041418000e80c02034842285024008a100105440c5030702e01640d1000d4a419000c42107041120741081d2401500030a458030485010074144000200c04e800301281c00440c408052000e5032521280c0c8208880340d0340810003100a200328075282c800940c40030002105107a2190300c001440101d10b0040100ca8000a0742d4a002c5601214600c90095401107a040d400e40e4600302d81512902ca1200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 145168884 1250 145167634 145167643
    0x302130e0a0b03010b01020106061407080405090a060906050f1f020f16080f0c030a030f12090f051501081f0b030102031609080106060f050903010b150703090e15090405 74
    0x10303900d0103010030621450100540c0540103250302200200545c0c82c11400590070788549101e8100810845210a070100e000c000c018800d4510851955203010b03211030014036541c2c0141d4210004550710242400340015900c1140081d0500300d4460941c0407110000980c9029014102c000e5070580c0d0301007455040c000c10600101006e064284c903003005903060108404100c51080070043d00c600d05014614a90106090940c003c0150240c0351030b10294800b07a400f1640803200c003040003008181c3c0e90301c02c10f1910030700d40c1c510721810002c0700c100e209051462409000c1105c02248a900400400c402400043c0b26240a540b02c1c22005407002e824080e4070003041d40146480d01035000208010304410145005800c400154031750400312503c1d50440e60890304140a0f00c40420f89041070007048074002c0018200b0114010004a1a4580c02c2c000c25012421211403074419040031541c80e0800d80c00102e094003511904404405900d8003030301c103070300107080142170a025890500106062050510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 145170134 1250 145168884 145168889
    0x5100c1707051c050c1305060403020f0d0f120804031205150118050402070c0510050909070c05030d0e0601050a0909050a03031503080309030712030203101503200403020102010b0a0312030213 84
    0x10400c120a1820715451001c0c1d86c41010215600071800101066500c1d16400356410790380c002e0602c100c220000c801780300050180c0301003034072030030103a80d0714a00188500c01d81043d92106a03540726000c1c2454035014009150103040460714909140030440014401a002c4a40101c02d103409224011a01c25801c03010302c164010755000f500000c0c551051240b1010b0f039004031041a50301001c4801100740454a502580d001a43d10144400c08a00f90340c0c41150b01b0700c51140030f24180d92415102c90401e00c11950261844001900304000402c01f501c0c2c40d114002c0188050f030b2042c0001d01c0559589034450040c0d210040a01d41e40300c420080c0c4040c0301400c04040e51780564519a41d05103e410642d40350082c2c3c204885030307401c1c45004540c0030710900950380600540301200e0510b9041000c601d04c180340040603e01055071b1085c816148619980302e04900a1011004554960850000900f558900302026004e2441c020302000064080542049140140d01e4010b231104000004c0b00140101c0d507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 145171384 1250 145170134 145170187
    0x1080a0f0216051b0117010902091309060e1605060409050c070213020c07050d0503030417130f080601080105040b010612090b010602031c061505030603030d0905100c170705 76
    0x5030300c080240006014000c035042541342c60208008500456441011076600005010301c02c0c01000b42c404680c002d0055083c0081c03403611913010350726040341203070f108002c2640c070103407200f40a10880d4404e0194040040480c8489440c035418100802c0451099100b04400e10347e44400003030302c400701541503d02e15a40100441c0d400c6c142d200c030351000b0f5003041d4400d002c180250f180015003890002c40a04082e640800591f003940c0c0c2c0e40d2a0400111001001c02400c46820480285c6041c4a040c1c010090100e450310080ea05040081091900d0816000302c5132607850101400049454610814111507040ca003c4c91003083c00d40c00480070b4422040000c0c1040d44540010441e030b44c01001800d52411404040300080c24075102c1314050302c106100d25004503151540d0404100e00c1107004680c0014080e00722442d20300759110482c1160760504094440383c000e1089a107100300d983c0502480554546002682c2c1d03000700a402c2816000903081d0340a01c1000100142000b8148801d500c1b10b00c5138 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 145172634 1250 145171384 145171417
    0x70308040507120f1202061603181e03080f070206180a0203070e15010e0f041d0a0305030603120307020706051b0d1101180c0b0c030d061203081501080a0f02 69
    0x280c50605404900c20030110ba1a21314814144a03040c8001001c2d840b43d000425003400c5c1d01042071027500101040c20481c0c164028174524440865400d03008022002e0108076024080318040c10010301c0204054003500d900c140ca1010301c06075541c0022407a81004404240c00e450802c6809a14586081ea00b0002e41601440800003503c8084e04c1500740705030f4010456080080403840115602109121a240e21025040c3c0031720b00b41c2043e500840d240c011154032001e0002d000788045203000e199000480c00180008100490780c142407083c4070100d00a00b4107107042d41050714000e5110030703a502880c8100840031989014501d08040a51540c030300782019501c0c0d050760108020441c2c0d04c84200d40031298200100d445c0e0f6603030030f0072100180320b801110f030300d204904084a44001c1d0788400c00d0100c55200074007491031891064440c0308010200c050881c80400d5480c60090100d0350000c4c00101c44a80c00c1036003100c03e98102c00d5140d404402e00d00000b0751b003c1c5030031000000380904880c1400525a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 145173884 1250 145172634 145172669
    0x21090b191b06060e0f0402030601030308150d050c100908070e0a020910020a17070506010e130c0e070305060d0807060b12011802041b1b020109031e0c0b0c03070308040507 75
    0x4190f800007041c0c841c2103c000845588280385014001d1040d14001d400da4030040040012900c181c01e13050b00030161502c5504050007500004601e40e0340c0310810740309a0403d081c01079003450036003198480c1c00030505000886514001c201ca0729000c19212304030766803080d000000c041015035030480345030031401024800c0c0205100710003952420340b00c00c1115950324800200003030207410400d44491551000081220380e090181108070008083c0c000c0106c0050b202201000484511020020709050f103078100c0b45280805004081d0354000d00180c2c05070000054010100c1e20034402c4400340303600000003040b030f04942000304a00005800c02d90302c15528100718015540c40e014540a9018002c40702848680c0c007550f011200d05410480003c085424179009000a003c0c6554401100d40141051204550380e6100c414284552058a0b040b03000e04081c440c040100b5412284042c10100180c6414500f0300480307a50740b40300310304014080c40300e007400160030001c0c20421754001c0c1c80961503151341da15 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 145175134 1250 145173884 145173893
    0x4030609020a08061311030709060e0a0f02120403050919120201030b0301050f0f0408040b040e01061206030c090e07030f061b0c031715030a21090b191b 67
    0x10381000c040b4400c0145920014402d003000032401d005032070309120410b406400c4c0d510030821603400c4601c5505400344034400510451345209543c01050a03420b500c1051401c00409400c0714040000844600e01c14026540c4a4910070511503026078141801036480c0340440000d0501d180420902c200f41000610103d0b040002c5200052140c0c800c0c3c034107100400c02c00d800c050907900d048554141e980c03150000262003001810f15184c00c9802078044510380350300e0301d8189a00c3d82c45074200200310f9040c1801008101d6000e12040410340e410802045035a041d0f55540c161000f441c481c5c1001592101d20740d04d0000d00522a103c02158406a02d108600003440e01d5000340103003015100c482c400207041190414002e614990449526a80b0082c09205082400e1380c030b0100a0000002c1d45200c0040c03210a440c00c000c0601094001d05000c6984003504c00118160105407200008010b034640c001c001c40018082030743c8002c8a060000100d03803204c6a4112000d001c981e01e1001c50760204039018080c071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 145176384 1250 145175134 145175141
    0x80303070f110322090c0804050a03030b01050c060a150501020f07050103020f09031917130605070303062705070512040f031103040e0f01050406030503180102010b210607020a020a0e0705070602040306 88
    0x1109100740038846c1101040c425544a43c0440c0c01403c207030022510303200060b1182d40102174a8505040445c1483e02d01c2d411030f4604042100c010031b12568620342107001b035002189250041c00248003c100890f1700c0e103140d0f61107820511416041c140c021903200e0044c00608103460000c04042c0c2226440c181c2043c1100c2d03411034085003078591591040054407a40c020324201d0b802c42d942d0004211002d803412000320742e90f41c88101d00f0303010180c2e00d20340030400301480303a2810002045601101884004030460304100d490180c078050600204212aa407652442d850303030340e40540c1220f1170306440d00c0c16003001d0b03415591140c0d1a2030035010002d0003180818900402e0b40c003d00c0c000003250640da81b104140f10496025000c080e10315802884010009506078020a020726410700c004035441403400d000c04c40e012580d0030b08008169038003c0c0540c0403407040120650041c181c0c402040c010040343c000c900010303014083c0e207003800c4440e00015603d9004408950314070342d200f102156260b65030700f840e0005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 145177634 1250 145176384 145176389
    0x30906070501020d1a0901031203021207021c0302041202011101090803010e0a0b040915021e0301080f010e010902011e02011103010308180312220509041b080303070f110322 76
    0x4d86103089000d650140404c03d4130300000c00040e000e11000d07400e680700c0e548042a882d03c0780e000c01d5000c200c0420301800c0180c24030700420654005100409000790203402d40600500300e02c080601c1800104490041801da2103001c50302820044a0a5892008580036284210024000d140000700000344d641d5203450faa845191390100c1000100301d0001000166640b2410140944509c440c540407001c0166008002552121892241003402e441d0a01c1c469042640402d0f02e0b50042c003480fa903a48420f026100922143d070300200b0900c1a16400a802112120800c1d0600c103a41811101e0a5000b5402203105c5800c4206d03490300c0c2d681d01d2911170131550041500390080d144459550318581000194500105200107805080c032101c464417654100420700700082068800ca000520354483c840c0c0c0714010380c0940d50011a24988004210704100c1c903034449078280d4420000c2020042d489003c003400d005280c13810a103400d0b000a886da285001d00084914041c0c0303030180000c504080c03805030b2001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 145178884 1250 145177634 145177657
    0x7080d020301030302330a0b031f0f112508070c080a0c170d050a0c02090f2a090d110907120c051305040b0402040308070c030c1401050a0c020303090607050102 70
    0xb08607004a4004e415004904d0b5000c4146c9a1100441d4a004050f00007880b02d03031000d41100c1ca064402045011101d0fa140b010b0b6041c1656202e540e80c0d488a140100b00c41c1e01e030200819817906032485c50002d181180c07a85201c25400300c03900301340c003004030340070403254299000320881050503110420507880d221900c20803030301c03d0002c02e0009658410f400d107400d49060030300e02802001c0c4440805503040d41c008100c010402ca110720007400141c0e07a425180f0b000c2c81600002d03218a242841c4460328624a03100b0845070303032000c400240a15500c010841c4c00c80881541c5407019140d252070078195000592000395800304005040100d8294014601010001e00070801c0c01461070114064075944120007022500760300c0e1180070301460402c0c2d000f120072a2005400189450398a4864420782d4001c7d890494018031180c00400c24040220050f0016008081001902018003800070b4518441c2e00308a03010301c01b80c0b940c583c0665900b4000c1c0c511802c0c029051136940c04080c540315000b50f10000c440c0c40d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 145180134 1250 145178884 145178923
    0x9050a0b090708040311100e0313060905030601031b051008090c040501050a0b070c08240c091305280c090b0a02210403150915150b07080d020301030302 67
    0x18041c60500c001d98001c010b1612004003c0d103994130200c03881c4030a43c01220340392145840241409115201d040201c0074500c000e552901040c00c0105000440c17944400d040207540c14051100b950b02280107411642d004401c00e40c0f04001c880d80e25107580a0354070a580c80799081401005e1a50843c0189100e400d190055481d0310500034100003c80324203008941d000544000d050001c42c56100c01440100d02902c05641140e42d07400c8060300c1d00070302c0400c540008241a44044154214003c8550404030b00e0074060704004c900b0022580c10b1290840f00d440c699126004900718010b6001d4070028110005800c03000d50b100b0380c000f030000d000b0b410131260001e001e002000070001404030550302c11011702e038050034920240340c9011042003030018001c2c40d4003104100000015030f2070002241c40b69050500031a034084103082c1403070002100c1e074200c02c00c0d504003103100c0415019589201c041e2403401070a140c4a003c0c03420700440c903010303848005007180d10010000c41410340010f4000e042e0411046001c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 145181384 1250 145180134 145180151
    0xd0203070e10020d1b02030a030203070c060e100c020105070203070f18050f2d0106030c171b0a031806020c010606050703050406031d011a01030b010c03082406030109050a 75
    0x101400300c0082c4030042c0c1003040d4002c069885180d915010300c0d9000401c01140740d40780c0000e402c1c42c070940e40c22000b6030304c006005004c01512900c0b681c0100441e042807940c481a400c0400c1000c0700c01c11040301001035140903002160300031000e07555281d402501301c480c460b841d80304c840e04003041c9018001e07403007081139140e05821840e400b64511504120400800940399a400c020309000c144141c011007060341e2003c10442c1501a87c242e0080240f03a43c08122580000d0300501445100700c0c114641c088282d04112480a000203480c480408280c0c1007961920008411401445040030500d281c20310030307007107409101f466006000b084100c44000c0205a030b075040203886522a480004001c09c074144401c2006030b0280e8420504009a42015038031800908050303400c440c00200d542d10f800044410703412184d641403240d404482000e0030802051545a10302600c2d048009101441c8040c8100000180c640205540340c41c03c5006806c2c541c13256140e0240701e0240c00e0481d58600b0305072419030b00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 145182634 1250 145181384 145181389
    0xf040c120611031008280b181b01031505090403110102160501020705010609020901090b0309100c0f03050121080c0a120f0e0109030b040206090f0a090b09090a0308070f030906020d0203070e 83
    0x100b10020a0000340246d480038030f543c1302201c04400800b403d1079a82c080588202080c42407100d103000841d0010040c07400c1040030005411600042c0c1000805141e100d01800345440c0d84149503002509070038100c09601e141c88066019219421100400007400240c50b010007405402a01c5854810070003030000580300d4140c00200d02a510629000070000e06040041495580056030866020403d9a901228455407001030341e00e0302880c1400581204282c4446607810301c14240548001440314454400442a8181c4d000d000440541104000074107143d90907020410003030510360007603024180071600f000251000060001d1320000c61465984c250a640c0f00b410308600b90f981c00444c800e426142c503024041a070304100042c40c0c00035080400142140d699034035581c000c01941d00041013a64400e01805210750020f054106145d1040441900094000d14030952040352440c0110380710500100c220003030710391010701402c2140b0004007100891403540040d40705440f1074907003500000d0304005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 145183884 1250 145182634 145182673
    0xc0d02070f14240f160c1a0105100309030e010f021608071d010501021c0302160501050114060c0730060204060e0f03150c1b06070201050f040c120611031008 69
    0x82c0742d0102107800380012080103501c041469141c0591070007094220315582c41c601f000e00c0d12115042d014128000410140c0384c891010030224404e0706e814446a40541d4000c3d1030b403c5c4600c041414011008030f2001030603c2004101c48001c4081d1800c2181c0b0341d160301458030b40c441c078002c400d040311503808041c162003003200790241290b0040c2d0041c0480c4203101c0300725040d82d124500d004100b41e001c1000c5140a10000541c1c1d180b98002d0000260551500b014401100f81e0315562b18000c02040c8502c0243c51400b0800f64116115102c0810f4001c0e01d01916142c0d03e0351101014240c0814440901c081c051180c4c05081a54100d807035804210843d0001c1001d20200c071035403603615900c0740030130004be80780201940c0c1d00001c0c3e603110142005c00c01c0d500c0342c00c80d0b01440d180354060f82c880000c01030b00380ea0901600d500800a460100000c4c101a102d0014a500500607043d4008120071001e041100310703440504a07203040b010854a0341440c8998402c1900644502d0700140309001e14450714a51525 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 145185134 1250 145183884 145183891
    0x90f010c05070b0f0c06091f060b12060a0308030a0f15081c14040303121d0304060f0c0c060e1002030c10050c0408010c080a11030c0d02070f1424 64
    0x70010161140303010fa9880c49640f001e862030000d84000e121a49803a0703c10441180503082c0c00001c0e003843d554000004044075513209002c40000c1c00d01108000e2914588110760314441d1544002c1c540d9603920f0040746403c404d5600092103c01c00000f040300140e00359102c41c0c0e50ba0b4070b010041c00b1283c09400304080c3c40d030b602c3c010f10307010307403c044a2104a03507402c00345080c0c0e444481c14440849a0360007a1408240c1142c1e0054000c00d240540c00490082680315900c0d088c41c01030f2029112450403100e041d542e000714001c200c2032000032003910b58820701544480d02019440031604004548540c0001e1000e81442c4c4194040c44068220707030300d038a00100c20307200c8550007080103100031411080d030000540005842452042410000412000020301442d01d610750651681102820080514022208180d214480ca00402c1c414071001c0c107046002c44070340100865000d80c40b4a00d40c10306500d01a080030000700480c41c03071800d00e6a400c00c00b0401001107014102e003079039030945c1c82e030180e0000799044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 145186384 1250 145185134 145185143
    0x30a2307030f08100503031c180c0e07050405041b02060609061003091b06050901120b0108060603191a0f120a0f14120301030236090c0a0902090f010c 66
    0x10288403202c07900c54804030360310503140203480300010781d00e10100781190b0244020440501c082c142304c06901c0b01030301a06202c5645c00c40304a2420308941c44e10000c080d0b6500900d90360740313012800300b41c4a80c030a4040e200641001001005490300601200480f0100c68402a002d030094078002115458141c150701d110b440040c2c120007243c02181d10490090030f424804032440500c000e0303207811445c4a024010060401070315440c0c0d07504451000504125400c0414090041c1858042e250303990307001a1035500314005490460702c2c0e071648024007200c1d45072081c400c1c0c2c00030302e484982112040d1414031102d40320020365141400d07803003d13024010508400d0700c0485680d406404034000041140900004450045c400c00d490080d42c0741100f07042030064428408101404030040c015890101d140d18032120b070b4600c089840600b41507180700703021110b88001003418030000000d103605a0500c481704031000300810110540d42c5592001300207422050180340102c0ca0128584080e5029901410007103401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 145187634 1250 145186384 145186397
    0x90905280c0816090911070c080307050a080a0c0821060d05070512010905100e060606040e070f09081203011805010305120703090e190e0d050a0507060905030a230703 73
    0x1540421800d10744041480801c000f01c1d803100107a0342c1914462802e00101003040d1b50740c0d81155041440c1b800080e60080d900c00c1d001004081c00107580000d140002c2644042800d40710354100c101602c4074000c551001d446980d000400d4601d003101010105003901d54804030484548817101400462521041c0041281d48641001e128924040c0c14404049000d04004034503140c00c0d598540c145040c207035400c4121502c6408505140d40e00340020795000c5010b03282c0a0030f06190244c246441617000d0040014800040150040079110b501a4409042d11204a4001800b02ca850401951092040d402c2c821409110f65289441502425040302c2d000002041261059110000d842d4880c050031818040304120005481030100d0806216071031580040d4108068580310006407071400d203c5030386e10340000f44a0080a81c01c541655907101d160300d40591111140e28204000381034400014040d44004201c801036254040034040c8034036204500e01d24004444200401e26000700303180100484c0d034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 145188884 1250 145187634 145187641
    0x6010c0b04020a0b16030e041a09070c051e0f070b07170c010504060b0f01090501091403160e0717010f0e06031c05191b0b07090905280c08 61
    0x16000c94207600107000609241069a0320041c804284d8000c2415100a000c0d06070900c0c241904803012400028081e1424400b40710062010762070002d9406a2510551000700426041403080c3c0d0420180c0b41e20400702c4084032210840608003e010700d910907514440d250301e8101e209004205141280d215054030343c14007c050351007900c404000c0383d03100900402400b074904206024082c0c14025402070000141702c028050a00016004880031507040c8243c0810411050740d1002a5004460b21000c0488103091600d000a0819510321416120306021800101d02e81c11041e008500641ea581c0b90000500501503a00b400d000c401d208a0701c07403640f002020010f03e02148902a4000c0009082d112614041109a01205080d1036544009140841c1141c9480500e101c40da4106c045400c0070407220030107000040c2c00311040000106403141c0c00c3e01103213a1a020b104c0c000c0103003009400901c1b161038401030300203e130a144038210028007100021541d200880388102d404050460740e03401703100c1d40c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 145190134 1250 145188884 145188893
    0x1d070b0d020f070f03080402010306050f0907050a020111030a05061002070614070804090207120e060403020a090b030a02030a0f031d100f050427060e0c03040303230109020d050f06010c 81
    0x401204841212035410443d4000241141d081e08894a1290320307210f01e1804e180c000142203e040f80c100b28082c1380c40000d00c100c1a9103268107194008443c2ca030190b50750305086000ca0160143c5004580d0210b0080b0502400c180700d5003080d403041e0b0065401d03d0f800329401e802240c0d641e140d0b1003440003140903d4102c05849050038001c103540307402105502c2c506035075082824100d9000010607504000d90034845860681d2240306400701080850f400c908050440d00050b034040528428059600d58a4000039810f84052225282e00340d001004e030703141407045082000c11413401043c05c5000400f540090303c0d50b900b03030300c50031400c43d18007602e0002c031035289640c1602d115160f0040e54050010a01000a4242c2001d403051280140303507421002c0300b0450540001919460303003080c90f51061140c1000704030007111003502c0d80a50180f4020403181b5500b114801c42c954a007802c0c0204c0d1000c0400400e8209898000380058514680d00304002e030346006030441c2c1c620003581c9060000d8502ca00720070204 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 145191384 1250 145190134 145190137
    0x210140a0e0d050415140712030f02040602122110030b06010206011a030709030b090a020f0409050d120b0411070302101401090f06050603040c051201061202061b0609011d070b0d02 79
    0x305006c1c1004c4e03102581c1e160040c121a001250308544034040c03002841041a814042c407102084031041c00e600700303810710b80080c1d1215040a10090080c00100700350903440c0041c0740500b200c80002c2075507900313400c05a40b40f1007514100e010588103000b444011400315440001c00c54100c40c45c80b00d002a000030202840d5405900c00f51000c0100000c00b031001c03012486000455010f620f2250050100c0e064601c1072160390400701e85100d1055240c2124030004c564007182d0220b0708102d0f80341c103409500300700203048014810320704030313036007282c40d0000c03c80a481c01c030002400c06034080d400711608078200d90030000a03a080c0142c120294403c000042200b513001e504504070300301c04c034840890039070385800104046030800c85081e02c0c170184101c000c01c20313414003030012000448900000d02c102810710204c002000380440c4000d000c0c45002030095501030507402d01c404191001d0080d540340b410b1010891b406452a046103012100c0c1c1e05c4004424140001040c0c011038040050350381c1007a1000381100000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 145192634 1250 145191384 145191419
    0x607081302010c0f02040c09080d0201020c2e0c020a020108060616080a02010212131406010b031306020408060f010305010c1b020d02040b03030d021215010219030210140a0e0d0504 79
    0x4c5001030740c0302200603613503030147d00328108441c0e43d0410319600d8030081c0ca28200751042010250f910400810b500b0b9071004c03645919170f0b1560760580b001784900300e24091120031403614910200345030007180030310613501280d802d01903030003613a507491942c4031a0100f02680c496184225206e01c9400e0418002811400280021440c4c0d0300005080090800140700000300c122a03070315249560300d404000300442072440c3c55820b96880002c0c0301035030519800040300d100c041d103140704001c20032100c01c0400040e6011100030b400b0a000742c400c94186031011f024518000e01040b09d09500b001c03502c1a019110344a03455200c040842c012401d145c0b250280000121b110000341d030410b40b12005464581c50800c02800300d0301140c080181c2c1c84000780c80c4c12956540c06030243c034603541807e4803a00a80c0e070020b20ba29805030400d00b031980c102c15620b0709901e080000f5240915242c00d08102401240711299481d210746e0101a041c08284074202b035094485140d02e400380c02150381480240b0001c107254860585 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 145193884 1250 145192634 145192643
    0x60d050408090a0605040e0c03090a111f11010c02010e030a120f18060509011109010807020c0307060e03062a0304060f0f0c030b0d0b1f12080301080607081302010c 72
    0xc0d00c030301c082c049428114a601302c10003080340081c0130046030b01030700070850384441c14280350390850130326003200f90310303007040300005041e5a5071640340350103135034681904c543e282d01c1800600010040303050024108901c82038010406502c0c102e266900325006004110040711880091403030b210035a5002d44643d0420f5052066160f514501d401384060b46204101c078903090241c4600c5140d40501e0305c80203546004005502c03590410407500120704600c0183d941088090a00c51003a56a00c0303804c03480c0c0365803071242a43c0740c860450000791494201c05040030010040d802d0351560380d01c011a00b100010900d0380100502c0045080e00804007861014542080c0718400206441c11680520340c15104900c14500e041540c1b040d050840e590148140540040d094a00610b000155120041c0c0c030100180f02070090303070035140c00c1c103070740c6060040d244007070700b944544640305110030b0030013a002c4e40090091000710300c280400301704c03024058080144110701502e00b0302801e60040d8011190b04405600448 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 145195134 1250 145193884 145193887
    0x60a141602070b030c0318070803030411010507050109121d2412040b01090f0b030a03080709051309030908030408030d090303111908010512030412020a0e07030b0102010b0f060d050408 81
    0x3c45001d8000114040e80c2071491480e1a0f04050481402c00c48114180300420b6201e144208080e03100030082c0c9a202d90040031a2912038205001640e19220302e6034014401d506e0310050100304030110251074981c071445d1380d81c0f00c0d09140e0707205100301c020f400031100f0780d1050303450302100c00703510241c1d4948110a24521905051400a5994207041402550100c901c418100e006001c00489880344c1c40c542d0510120a100781c1c0d0700440440d4845205581c05810024030703000103140b05008003e4035000304000b500038808407100d4059080140400340c02140024112040040c6014000003520156040744000e1444d0104110034000142501e641c21824551a88500304070f007078980d4054260510204016245103070000401060130307005030081841400d0341d581c50070a6403c000243c6040e46c0140054000d603e00500000b414036940c4c0c0e00482604a40301c08018156a01da0040114100203800a10500403088100712202380002c0105410140500c000c00309a0311581065401901449925 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 145196384 1250 145195134 145195139
    0xd03051b130e09010e0304060c030f0906050904150807030302010515031f1e0501030f05100213050f0a080d110705270703060801060b18040e0c060f09030106090e060a14160207 77
    0x786c110b801c5503000c039020516883d455814180c00c51080e5400100619058607403d0070442c014102d4010f0402150245588810012049000c1c1c4402c0300641008030480e582255280f40c024064141190ba2004c40c41c4510550308060800160303200a08020501406002e90f0001800c0700170540500c40c40680c2e00450034041030100300d4032440c2c1c040d6010703c0c0d8150442c00c85040003403030704420036101d802c464410400c20401d0240442c100c02a918101c54550440800c00c001072175030011a00001e070a030003000a8281d91681100007120b00c40c00310000e82e40360981c0c0701c08102038000000d400401c0e1038480740304004c4124040b05650740c0550380c0d040c0056510340f646d8840c1d00319002500100c86818000490038000e0f000c100c20781c0e0140004640c02d10540d981489030588454811035100c0c055540401c0c01101020a8030550342e1088015008101c40c1303503545442c0c000381c410302d24480700d14001d00d0045204030360107008031204100c2c4e440449009489981700d569859000c81101c60440c003c01501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 145197634 1250 145196384 145196411
    0x30a2406080117030d050c0a0f090513090201020a051605100305070804060e0a050717100209060706020c1002120a0b030a020d022209050d020d021506010e0f030d03051b130e0901 78
    0x21b076805481c810441d40e4590307240c010050000c102d413180c22818095881d00800160f69161136040d68100e031204007107266030b400c4c4010303813401032144001041801140c40d80202c0c8161140c0c4402141c504480c114580000700200b5002c0341c1040c3e03110000201008001000714185401002100315031004840c081d03000b0b5121141400202d030801c031590031184402d908010300c100055480598509000c41c5021400000241d152080b07840041401da00450700304500c610911800c0f0030120307015000d6603100703401c03075520894080489450010f24038220340c00c607490900182c10407800303138003500c0d1381d140c0d0b0500e80800003070b80c44c0b20b603814418141a03000e58401c8036160041404042c4110000d00407001c4242000e420445160741010031940156101c9180c00810000e454000d4001c0c2410341400600c4008030b0483c1052400413038152040c11203030110a0380c1544241d100780d20f409100c800e60683d107644c108d4680314145082c20602c3d0682c0007440400094a5140c0d0440d11038000015200b845008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 145198884 1250 145197634 145197641
    0x2315030f04081204050d11070e060d0507120302010207170304030507020d020a05060c0601030c120305120a0b060c0a050d0905060d0e010e0708060708060315010b090a0506030a2406080117030d 84
    0x50442d86600800d04a1080760f4100c40500e090281c10400b42c00c103c0e0278401511802200207290b41c0c4600381c940c0782503091010038044000604480310403e0b000c0e90a505000c2d002c1c3d0300c40300044481203940c803126803582c4021016640a545c0c1b50f9240b6107032000a1302000508080c807101a40d01103590840081c096440d800281140c0032008040d052540c550304143c0d604d022103a10141080c07201900f0480000c3d4454110b03844114500e00401c3c0e40d495040e56440180384021403d90080400568190710041c0042c05940e028800e030201e89050300050000c81d500c81c168850300d81c1001d41880080f904c1c00164000c0c0c004030903040c00024200380191034052410203070750b000d44001c2c1c01c428203000101e940a0612503110000f50014101c81200d156450000340c014401c007801c82202044505032580c86054081c02002d0051042d901e030b0078201c01c040c0c000c10f00510700c1040002214211410205e071a16200100e071102e844100d40f40e031801d40390060a4603c140d400d041070100700f02601d2200494072 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 145200134 1250 145198884 145198891
    0x140a0e0a121709010819200d1b0e0d0510050a020705060703020f03061c0b15331b0a0303050105011209020904080a0908072315030f040812 61
    0x1000d04a00703445400d00842d02d401400c40c11040c444204500a9181d0300200c41c00e8121100080410b20345903642d03072060041448100c101c4034015514044ca0844500c403014241c030002036501044080c0d2960162030031795040a2118001c40c4a44843d601680303050482c105089002d281640c070020203502c880001c41d2012a20b041040c0d901094100074031504020180d844011424218641400159074064500004040a1250a001e82640003501143c03210041e00ca40c0001c250b209400c01d410083c15a50204508a0013070320500074160f080e41c1c54034038500c010400040c5d4410000d007908182c54181c0d001051018900846140414080c002045450450703070099030300003159410000010309000000520741c0f005c50074844a2005640c2c6c45100507085544101ea0a548484450054889807201e81c0500c1190140c2803001920b6290a140c0d2043ca0340b83d40c2480174145412420001c1c8038074160859140101e05000145203000c00294454001e4003030074807541801c1c03400064840c9440102e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 145201384 1250 145200134 145200149
    0xb040204080706030501122a120606050f030a02180c0f0a0c051014070f02010b0637020304180605040501120c0806091f02040906290307140a0e0a 64
    0x4580400a4542c5031103524054987c1001090044c096030300d502d55103441203003108481da4501840b46442180c03001008006000c10b007485050034006d8106003004001c076200301c500074980b088814003d4036010644da504540d0080c105460410b1940189038402002402e031012a4402c200c44040b901e54840030745299103181e0b980c00e08200071403038190306040c038508800b64050300307007001013008414010703c1d11b80c005d0251800300c0744841e490200324094443c0c2c0c818550000400904004100d0031400d01e04141074500e0304035082c2c0703800703c014141c09002059400c001600140401e1241b040d1a910802ca01010403c000c40c1450303d500014007110020f900c0070000144005803c010001c60481e8100102454806003082d4a4503001007070701c8040c40c01c1c1b2101e10a903040c0d004100e1000c00d034152000351699484c10802e4039160044441802662840c641207030b04451845560301d52201c040300d00c00c60069440c0504c0c1c1009151525644c0c000000d444184001c00d5070504450305c0764900d280060201c0f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 145202634 1250 145201384 145201393
    0x1203030c030415050c2b05100602070b03060922020303040b030601020d0f1209080712080403021c1b030201091205090f1c0813030507090c08070c0b0412030b04020408 73
    0xe0b14020030300c1c9428481d1200082d0403e410840b1012154050310540c180c0050f82082c0d82040e401e04102e200b00c2d031861141003030710740070a01c1503485030040381c1070a07986c0394ac08031480306456840c1c00b03030f8030301007111107a50151610000590078001c426051030b40140c101c0d020b1001840581c0000e0843d04560044114098040708000c004e42c3d040150b072804c00001d0520781c2503641c02500007050203519600c1810103544600b050401c01c07500d80111511030b40c00c0040c500080600e450024510354060f50140d00501c01c03000e02401e03e01108880c008480380300e8680d43c21289015080e907012112440c402d03001e5560f2541c50304082201003000301c0ca5000d0340e54880f40d403803803220304000c502e40d00303241014001d03071581c01c0f0415408600041b0030340c883c0c0c101d15010384130783c40700729000066035445c1c0000340702d40210400021380000c9604074204807081e40d283e03c0c500340e0703c20004a0300c110840002a01c40c4070713404007040204070080e01c032f44000b58892401042c80e030f8021000c5801e0380d1107680b042e00c01d81d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 145203884 1250 145202634 145202641
    0x806040506060109060e0d141009050a060b19210501141f0e0a050408040807030c1409190908091008040203060a0b0a0303030e0319030506030610051507021203030c03 73
    0xc0c013424600141485083c01c4003003c4040010412030300c28582c0c014140c420500480c1d87d051010054042c0801703a41005010111151420540b00c040b144411076080d800c00c1c19003103151405d2584194499a0540740f211081e1800f40405503016001c150401c50741d182c44481e038042182801114410b00f40020180d1040c10601d8160741000104c4800d1000142850b80a006401c20040c0198001081d0b40021801e62030b142466038661241c2c0d8804401c62144601c000300b04190401001c04680058441c408031101200034001388040841d24602c810580800040003890907511050000e0302031404581000204004107620100d9a071200e000325284c00c0c100400c61500300704455112443e01302c14045280c055002c00e40f0316905001c0201850744a00c40000d000904000342c43d044120703000e0b442e0310000c00030405802043c00f96100c0e8004e0041d03000151403e0f05441104013280c4010305124a007101c07420301c0885036085010120381c80307114071b505070201807003c101450141c280c04184a03601d04 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 145205134 1250 145203884 145203887
    0xf030b1009180f020f061209060115050304020d0c18091104090c030201050d020d0c030e010e010e030f0906040b040621050c160503130b19090b04150908060405060601 73
    0xa40e500c0340c01d42504010340485150920b005208846502c40800302040f00c4034030020340002048042aa041100881c400404902046034140201009410388200e0b90725041c03803c00741c03030550351444080b0b8010008200142400e4a003510a18021406002e10b903840f204144c03400030715005a1420552581100c600f03000054241c0e907501a401c540401400e54a980da24559181510000c0d0500c407011034468583c0c0300c60f03011100111040e0900b000f1451011346c020300145003030a03000540d51300c0e20340c18660f1502d051140c031886401d604c0055041c118400002d502d141c1c043d6a1542e00408140302c001380c007650384400f810282840e40c842c24518800f04110815905070b1441d0150311714204000d120f0b40044071b1048417074082100101002c804c1e41414101c0c51489130f481d200f01e0071084c0c09000252345031860f0151511a00c07001400c212031104820885403a2164040c1e1000890f040004000c2c0400902441001844900f0055109076555803000e060200c22142580c1e2a00719508101c0d066 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 145206384 1250 145205134 145205161
    0xd14030c0d11070509040312060306061a0a120b060d110d1103010b040509060d02091303020d0f1b020f03030301090209041415090702010e1911040501030302190305040f030b 76
    0x145150300e003a41c0b0100d000340c00d07580c1d20800d40c401e190183c0c442e01d010130141845622903d0400805401c184000d40e03691401c3d500a1242e417080c2015100109100741840c24010308840c21546980d035070381511540c00415100810b4050687d543c000001c1011750607500d124003c16002602d00d445060715500308a00751021703548985a1120441400c20041c0003050745002076a040c0c0380190b070306a010750303034410118a40701081e41001e503200351300104018a00e00e80c03802c041020741c401d0b07081d115520501201034440f450200100f401007480c414a100340000c501c0e410300400d41c0010240758000001d880400c0c04d40d0310a801000302c840d0002110195803c1c24000c02585842225055485180081030503000c584003181140c4500020380c0441c141034405d41000060100d00c01c25640030011600c5502d541c000f154800703d808011441c145407041c0350500c1142d0480f500b5070043c000b4000001685d001c003000c4407208a040c000c042c000412215040c0c1c031000b015501c504081250b5081080340c02000c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 145207634 1250 145206384 145206403
    0xe1c0b090c0a0b041503110c03030411062727100503031305040e0703060c030209030708070b03010605031f2c041104020c10090f031409090705090d14030c 68
    0x6882c40000c1041202c0b8008100c9045629190140000e40b071480301c1240038110211009212140c0416100c4011318040700a5000d00e100340709007103456200c1c1060000034001c010308410030b424018220f00f28080c105250b0445010300804c035200030203202c011102031101f510f04900381103401c1c00800a2840400601e01c0c00f0701002c80c011402c0c440a680f20490021283c020350340501d0715082e4200106a041128030013641d0b00c810140032402c14224000c000b074200c07c02880c400d104d03201001402c1c0d00041404025610626030691460b0300342081981c031640007800800400e80c4122407075401d43c020b12800c001400c0403041314000c101c01d5500025100c2c18002400d608000340784180800504503500c084c00402e81500d000d6165844061414188810075960005103400d10601504000301e0110700074869110f80c80b2040300d240b5a159944690144040c4117400a074000d01269605010b44054800c1d008010030a81005005075698401b0340001d0503c580c603035101242c2c1e0030f02c2e80000d2050102 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 145208884 1250 145207634 145207639
    0x4060206010608010e0c0a14070c29040f0311060c2515120b0a0503011406091803090105090a08030c0d0e01180e1e1003060606030203070e010e1c0b090c 67
    0x4582800d60b844c522601c100d03d106014442404123180c21005031034260348130a034005c154003003680e41d5449007002c80210b07802001c0400d103d283c2c08a0441d0f0950341a28250344c507400b181c004139411685c8030800590152503055000d002404a0700c0905c0c01003018480140c0007104a1002004085518052544ca500002003041c2503202100d03d041e030000d81d07541c2e01d0f805000c2c00700704d03c150100840c01c60b102da130b04580e030994202107110300c1034484126420301035101a40c03064065611840710381c14140452030764100d036401c100008409584900050300a2072001080c00c2219966181414134607446030300ca4414640012422000c580e4000782c0c842140d102c2030915a9403000461040d070003214041c012a003850100c000400c103401c3c44a08092054458032089410600306120410400e09441c48100d901030309007080860110f202e8003c0d05d000341959201d6600c0312a840005480c1c044c0d60034005900200a0641c0d10881c081000c140203400740504000f183c9820907129642c10b1010502c00c150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 145210134 1250 145208884 145208909
    0xc050d0620120f1017461703010905040203070501030516030504080c03041706010605121801140a2412150605060d02040501030b0d020609040903030e030406020601060801 75
    0x20842d9420311160354400c0d881e000020103580d490b4415180c1103c6604100000d0031200850000c00c54002040350300500c82586610540d144100f01c01011440803104100c2d824103420035451000c19100000c0c0a0b83c030a41d40000714107442d01804415130002da024040903030b2038405120942c28140504400f804c001e1905004601d800842910004151060b800c101940d400c001000d0143c8601038400031029501501e40d80d0b03079910000e512400c04181c2d10702450140000024181b80104101c0b0b280c09110a00701c0c81ca59681201e0001031901c10400c84030039500c40f090801c0100140142a00c10401600c8c0080c0405103c44c0000e11181c10214038042c1011312502400203095030040d100e10300e54020030b0308121640400c4018054055540465009a03003c501316005819640141c026200300784d03801c0004520180c104840190a1040603400210412070544503080a0b085042000c1c000d04006c111102502180c5103107030702c035910800060f000b650060013900d6211a8140c0101002c50120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 145211384 1250 145210134 145210147
    0x303080a090519020607060606080f09070f060302070204140106050d0e06041505130b042306130204020a091d060f010c1a190e0f010c02031303020603040c050d0620 72
    0x941d900d4440d901d0000c540f048a02400b0b08640e548002c58004a501c62000c0c004160740c1c241c050501901512400d03002400d901c0080d00000c400504c2104440c0500c1d021412036181036800d400941c480302c4180d8010307403140c6080c9284038400010b94000d0036242c0d2143da480142244070707000c642c0e650501d501140c001000340400f0550309000301c0c1c00c441e85e0300d80004844e190254003400da502d41060003044070350320a003084240550140d100414840043c2540403403270340c107000c180d1648000c4410640321b0a02203508800b600f0a070340a00103410440c00d01c2c0601c2c5840b907408068180d003103051040428015810030804c0d0a041c45038400c004800e0030060300240407940c1d41a81d101e00c0451010a05481c4800120740c081a5450002921111203003003101003e100b00007604d8540e0714524a0b219820903c01d042c0b1240700004036084246200c00580c0400e0842d8204581c660028000307a035503a100c400041184d61391596506103040c800c1078002065200000e0020200480a0310b0043c481e6050110 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 145212634 1250 145211384 145211393
    0x1806080c0618030f0a0b0a05010503031b010621110d02010813030909110d0c1b0b0a0902030d050406020d0810050d02030a1401090b06090106021f180308010303080a09 73
    0x81040d01100710707441d81d1580c8008090a03104110411901c0d414070820341c1c400024403010812101c60350052110400c141d40392a05039040e1103080c803903960158010440821458141aa01b402d1204148004590381760b45122401c020f981c00000e43d920900d00c0040c88040004c00e0302c00d403034034017010b65034042d582140760000380c00c01030014810343c404e004890000c410548100c90701c4000d000d01480c00c0204000d0709c0c8070b644440c0c000300d0f48540d05620341a69400b2003800385020000c140c036640604c51523240c00d5a11041d0140303001e841200481d8445101c4801a0780a2082c4c00b00303081c0320342d285900d40380303040d400901d024088041c544c01d20110340c0a0101c1e00400b0380610040d41d900340c130360200e440c1c0c46101003403409070380d05005800c00701020380e52090030b60190001700e01e40e070044440044985a007000c100d02210284101d0025a001e134404c1d2014030a101c81c6103103c440002400640030f0840c00007480640c0f000710048000420120045c002c064201c06220b41112441c3c5040040d0103e070740d40c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 145213884 1250 145212634 145212643
    0xb1f1502250e1b0d09060219030b0609040b0a210302160803120402010e0904061505092e0f060314090c0d030e0a050312072d15061509180608 62
    0x1c901026001140c0103d8000e0340312040f01c1003221000c904016003001410b200000790401c0c4d0007020b485183c1420040c456100340540340c08400000c04041c5041080c004010050604074041c42d045a54003500080411107280d500586180461500c1042e400c50302c1c0c02401e002c64804400c030040f03140b5405010f018400402d864600380c23080d001d800e1644a5000580da04400c1c0d1914a6100501c03000b00700822003241c204160a2009680942c0c0c4030b502c8408000e13038031000301e401411604408418100c40c00c0700300c280702c0840c034508141d524001d403165290800c0e0856a0440380210391542c5010100407c801d410944c4966028040c1ca50440c8000020708140c0b1b4140b0007504120380c085c2101c685a41e1545520000c001c010202d4805824241055a041c0c120078400c2d1500a440480d03d0680203080000c402107507003100f41c03070046032840d40d60200b06203014134030720030f10503a100c80124421000507000c0303021003595107401050034588804040e8000110355603504003070030620304010010340002d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 145215134 1250 145213884 145213891
    0x7020703030c0c2309130807060504030e0d030c0c0b0405010f0e040b040c020c10050705060106120b0612060a08030a05091c06060f060315030b1f1502250e 68
    0x1410781c050b0861402c0595910809800a54821600340d40c600c0c41c165076003031000303100076040c3ca2601ca142d540714040d05885040b4180602010010080000040d03256440554032a1190418211403040d41002c13800a5907022400c40115811000300c405009806030171000802210f5082c43c0f4050070203000030002c4901502c0300041c0401d5840100782942d858002c00c4640700054010051105044070080d559041c2140c024011000011809032181c4940125000141c00c10700801c03850f4a4408225103611038403070074a001c26691028001e080e500d00005141014002c0d14040103424041700300300c0d1080140d4407544441c0e000b08a502071842d0800f080d82d40344002120350b141000b07140001c47e14101030300c8100400c0301d4540070000c034501000e0349640081e101941d90030002429528000c40d030030003050001800000711a00085c8000c100c444408024180700010072614950740c8102d4200c0348042d0304101c015800c4100c84a011440c4401034000b0b10042ca402d0051881c58400c40364606000030307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 145216384 1250 145215134 145215137
    0x6060a0513020d0605061603030b030120030a06050d140f0d020c0d050307050105010807060906050a0e0d0212010c030c0f0302250201020319080103030306080105151903080f0d050f0702070303 84
    0x4544001002d01c2c5510884c001c00005d417500d82d4600080324251134840707544030200c001c01e14100c00481a030405100f400352210001054283d04869090b500c116908024145490742e40c60b8500401c258a440c1030f07004000b0322603108039500c0e004109d101d80c1021034081481c43c1c640d100c41e811200c1c4a5000942509019085c1e034030641104250400c0c031301b54800c125018000350300700305c000030700d102000030800c0444110b40ea0384100c25031100e4040740d140c85540c12840004e440040700e090b8525004041e0301d9000e100070000c1410001d041040c60035207142d41d00d460042960fa4040412851700401e422400400602e000c46c0340a041010310540c0d070582881c440812845c4603030120459008200b200c0380d8a0305940210402508240010151b4400340401c50000c2c0c213000000134030010500480b0301401901c140c050440d1203103401d000f155281800304030803916007601e0010120703038000000d0803e0b61040c4002607440c0a010125000d881c07001d803c410b8401e40708420401e134241c0c042052820340303501d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 145217634 1250 145216384 145216387
    0x105010503041a0c070f0804080f0d0804110f0d06090201140702060708160803010816061d0d020402091206060f09160305061306080d180f0303050d0609050106080906060a051302 78
    0x95044c02c40b1070703004001c8011b20409001c10348206220036030300a030046807030f00d0044500c08441d0040c01a1500001443c4102146c660400f10300091004a00d103500b0150180880e03210303001c0c100003c1e035880c10403041a41d0342c1d60303584200019035a00043d1041040f0b106006d8a181030855030218441c1d100304407018210300004a06020713050801c0c40078000e900e40048030962607503100c144080d104c0c10030801c440403241d8141c1c0d00107100c80c0280da200d031290111500391100c004021090182e0103900000c12a03216a08010040c00c039030700d42d035120003904c003090000e00c1d882c507201c800d0000c10344806d0581445a80c035a020080085220701d024812003c0c4c5140c04540c0741c4072000810b042080500040740f40904281300030800c4840095040d00001d0b203030350b804d5a04440103007005003155250041104803030300c50206001080c09400100400c0790b0311800091055544c00e08070045407000c0c2c010b00c2c0011045002c3c06000c1e80704000f510707040f0703100721080216903107000300080041c80400c400e1752034a0740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 145218884 1250 145217634 145217641
    0xa03050304020f090108030408010614010f030903090527060d050729040603020702030118020109060c03111605030f07140103091a010608070215041e050f0a050a0b0105010503041a 79
    0xf50003420243d82e500160500b0403070358440030807586a4126000e82c1c0300d19840c1c03090000f0500280c080007c600107042c1c40340380e002d45d50140114040c001000c0c05030b003800034100300000e40d61950080c03106011188030800810003001c0c08001c1c044400603100d9031180c45583c0e03112022503000b04210003115901101482d4450030112000b800c8950b801c0300030344180020078005000c0340c058004211680c030841c02080712046000c1c1c500e24140e06524042e0003d02e01070b034280b201a00030301d01c56040d68024108a079095850080c00c600d0926100365510a0481c101c00400160404110544000c41d003000548102414030060b4185180b4040309241015101e8400c04180030324221100c83c02608811a1000c640e140e0001410200c820744a110041c03140341c410302c5440700c540720700702c0c042c5510064000140e002c1080a00c0780e4024200c0c141c0f014040e04d0071070b017081007040080c0c61005124001404400c951820040030340d100503803115041c484104100400540440c056060000169010b082c0a48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 145220134 1250 145218884 145218889
    0x11401050916090b0a0f08011e1a07080301080a0c061d01030203070e0d032a02060706020c010e0f060103030306150203190e1003061503060612090609080d0905070b03090a0305030402 80
    0x1030f1503a214a00183d00014140c4020780d11076120b06800140c0d4480c03c40c6030760f8450414504042c100412a4180c10701c6401b8010306200c0ba2040200510701c40905080032038a40f0342061640c42a44560020350002d24a1001c001561990700010845400c3c2410040c41c041c64201c0c43c007990317146403810181d0000c0040e001030b0040307807480d0454030f010b4041080c841c510b00d0040d0010442188071840462000c2103032040c2103030101140d50141e4050021030620401c0d55556010b50411f01d2500b4855403941e0341034540e0300302040a8840741e40d10744010100c0794035606029003120755a410842115050603644c0d603420b500002158491712185c541204044c1988508680924101103242d910901c0c08094000300341c1e050b00404240d81440398001c01c00701001209a088640d039206020106d44500d220b034205101d260302000300c0e18011040800ca2400b143d4840d2003682c4100c038040c1c00035030b0b106042001d11004200b544060481680e080d0300d18149960f0090740c4402c6031100034100301d4004002421034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 145221384 1250 145220134 145220147
    0x60a0804171215030708190c0302090c0301060f020606090f0604060312050706060f15052b0e0c01030603080f0a030e01050408092b060c020a021e03011401050916 71
    0x741180040a4440000030030050080c035068400c1c00c61010302002100d4070740f402042e45400c607030080c4002c4c1080468070016840c080c88041c0c00b503c1c000403501c0000090303128070100500c910b12100e04142d8a46c10506c02904d07801c280d0442200b158030100400c0426250307a24220341142542d50801115582d500000d00501029040204005603502d0501006900300c0041c1c0100c9105680034002280c17100801c006446072407203080246075a0713203410502d00d0301a03c014000410540d40c0c829035107400b4103504141e40ba4144c440103c01c0ea45014241894100f070011041180d42445e052194610f035841e1124680180390000000034000034111402c63300035030110103180c103904008e01841c41d160820500b10340042e0f82c024002d10200818140d08030320f141c4151107200da80603428034109002d442c1c20004000c20002c410951140040003000743e911103071003080349550203403012142100e580501d400d640640540e201049603942c0180301654075000029800700082c00605907030050454210b519 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 145222634 1250 145221384 145221413
    0x6030312110417012a0905030312010501080423070e01080d081501020102120906070207060f021009030c02041d0d021f020a0e060f0307080105090105030c0d0213112106060a0804 78
    0x5241007155220891083c145001361014403034566440c10350b87c450130f241d240c0c85102c0196a50560050050102c1d40c05248115001405a070400b1203043d25001b81c0b80050081c5106540d440e030110400304002100010850301510722280034201c844001080944592000f904050f101410b0781d42440041e4403d40c1136502010b140010400c842c01c024424507180c020030b4641030010f025517180403c0260207108002d4441c0320613402010032a03030144015004002d0304404500304000c41e01540003680c1d95000b400c0c40d48003510081d040c815040c20a1034a4545818400000e540003600c2107032043c0c41400c4030a04000b811000503903509440c0d20103d03014000408225030050011409480081044001e107108001c543c071841c180d41d0701c0350700b004441c141c2403254070390581c0809024000c9043c012681d082b598400b0300030796428050401e4240a6426460901c0c51040000c5409e07460451020f008445081e41300d9118001c0d82030950115250740b1070039a1000901c040000410100324294480000c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 145223884 1250 145222634 145222661
    0x40506061303031e0306062114090c0a06080105031002030a0e06090d030b0a03150911061b0c0f0f1009050303030c03011707060801170f0106090603031211041701 71
    0x2400d84914014003940340c4045440c2d00e4130005001506001e010b13200d0081070383d180342c541e40c1c0d8500b9448540c5600350780d1800e00300d030032584800d05580c1210782c80c6080c074003610308030019156599000d03044c420130030865480441001044001008140c07404928407201c40341030b0030003598079562850310a001d811000078002080c8a8003042200040c00414041c0300300301d00391350074031813029080c0c2044908481804003030809003000c032201d0030000140d0b00c101c113040c3c03085083d84c0d4a4034200c00001e5003500304c443c1c020076002c01c00000a26440301413213030b00681542160303c020349440d60008a6a54040342c0c00d90350282201b58000c5400ca4044c400900c0248030003030882c0d0780c9143c110041c80690b002885040020315520003000d100c100003288203800e50f642c139074544410780e203022681d2250300280302500e0800e0195003100f2401c0d400a0061001402e03078002c000c58402d1440c41c0c000c0c1100350180010341c0841c030f40480740300000304210880381200c040c00440385405080a503210b0040038441241403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 145225134 1250 145223884 145223917
    0xf07050703060b0909031207200d050a0207081c0c0f060c0e100314061c08030405030301080c01020a080403020f04060b1305032515021e01290102060604050606 70
    0x40203000e401c03c4207150710559080c03810b03448411000369640604a0b07440b080c94090400185041d11800030b0010365100c240070803407410030301030b081801d00d40d0080b003500000310001416400d0340c0e01000b600f802003500300020402d956502c1420080c172210b80e10803808100c2d010001e641802004820302c1c01083d0001d500700082902000060000701c00020560b01641c0c1d81c100019029009203d1003484840c19a031180a41d41c6600800c1115107905040700d0f900b07412100c0020110340e070100594484c07403007180195569410015218680307044480414115131002031a000010f40c1c440507103040ba42d040e20010070340c180380300000d0701505154001040081010844840210000030513004031001542a211308204c000c40c054019a8403407001c0740c0c01c0c1c5000c00e00704807208180541c0710442c160382c0b066844044c01e0040d40410078224031042c480303580d12040c80500702d44488038400c082a20569840070b51501700c9001030340340e40008010510a55442001481075250107080390700900c214441076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 145226384 1250 145225134 145225139
    0x30206090a0e010b131d0609040204061d040203100b03030a11071203030207060b031204031b0519030b0601050a0807030218030d033303150e010f09021002150604020f070507 76
    0x620382500240c005d0a5002d8184000086c0204502c4c81400761030000b119003c03139955143d041c00700504001c1c3c4200d8110740e0306c00d40013a0b000e15450162402c1d0f041c1d00b403080c08501f0305004162a0120502c807031600c052070040c00c40b800f55400001c441c1b0780d8413207081894281032844015400c0002d95448030700151100740700c0c03404055044c0e004100492160702e0030810b07203059800b07042d0f903039119a20042c0842c400304000d00c0072820002c10410302d0141d0210b80342c0c2d603d465802180c0490011240620710521080c0280100804651001c0e80a0020300c2e000b030400020120040c241c520150106040c90741c001080c940c13040c604a01d041d50100e0213012200b9840040b000207008000c162510014242190816500e400420002480c0081d08540b4200c0d484e0558840c01ca12981c0c010710418000e6031480002504042802400da450050200009158096005002c1c544030114500d41c00c40d040700c1c15171031240200018281e003000c01964010385810580583d03842600c83c215001e41584600c0600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 145227634 1250 145226384 145226399
    0x301031b0e19050f06011b05010f020f043206030403020c0325091811010504030c0308030a0b0603040203060a0e0c030618010b1e01030f02040915140607020901030206090a0e01 77
    0x611030008855100b003050b41c0d200100009115003d41e03440307002907500c0c0003c01082014400340d4142c9402345000144800c118241000bc0346c0c04900d818400c9440801c0420007001e00c005980030905462401c0403800c180007040214100308401014820403010010509040c42000144010b20016085401001144110300201039542420148201035100301152103080390044002a04002440444050050703482d1200d0818403d2072504020080c0800404070302a4011080114000e4100c2540c038200f284c01402610060815140920420800d0100507280090082d0303000c04c001c3c1d0300180d101c0c0e001c010303541802e4059041d654140714085c1480400c4411508490040002c0c0c4003c100c51a801c0092100c0c041d00101c21103019000400040040d5000e50898100c42c1c1c1080b00051a1945800d0100103d80d000c1002a0f07882141007000c0c0940d140c185480750019108560103418a11140c0c00907020310300500009006500100340d80d00e0340d13240c5104640c05884007281502007507844446 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 145228884 1250 145227634 145227661
    0xa020a0c050f0306040b1b0406180b210703060b070303020c0f0609070905100302040603060f0c09050a030204020f0702040c020d02060115050306040209030f010203070e011d060301031b0e 82
    0x1054550410a031000101c61521000c0c00b01e0201010700500080e9603142c0b1004403030b4030001c00d00c00c121180e002684120003d1540104054000b6440d00032040000502080b44030303440c2d40242d5a009420010300c002003070201031040070b200e040d65004045581d034040440c050005a1300407090910007290070b400300364042d00600440d90112045403e2001d01c150307000c1d039a600942d0000c505070403448051103070308040e42115074401340015955400d540d90398045400c41e1203a43c0251030301036994045500109460091612011a524003c2c0314603003031900003521040c441c0b0000340b013654001075040c0005220015124101d800520405c40d41c400e600b000f07512007500880b4a0014040c240022880d8884200360b14000402a07903054210350340d40d81440003e50140380c0c2a94036124200c03107501300301800d0000714496410380c0c0d00c1c5025648414005040703900344400803505005044840c001946801080c1d0341101e40060200140241913a820004000e49400502c4404c41210802800140d60fa4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 145230134 1250 145228884 145228903
    0x90b0702060703090803040b0d0b040902060f0d0902030601091a0307050a0510030f0e01020a110f03040303080c090406060302040f05030c03030a14120a06050f0d030e01050a1103120106030b01020601080a150e030a02 94
    0x1c0d2709010b5400c20104100460303103140d0300254030020500902400d03d000308060300c20703801a02000501000d2030740019142013000d0b0301080030241c0303804203c01000340e001160904902c00b039008064182c20500001ca247c0c0182c0202030140f28081c030054040ba211b90051030700d0916179036041000c0d0050401a90117544905000c2d00450090302036007666820001e400d032a1590313008040c604260035a6012144000d02a20a4100c10070601807441035a07124445d020045c03030107441c01a5580d2808603805440055540702d00d00c00d4104585003809500c020084504801c1c6514044851000c2c616541d441c50098800b10b80e0200c500c842000341e41c900540c41081900c2c011150b0020380c02c0180100141c1d1080b94030014005400904401e5042d400b42000d400720454505200d4032240c0440c424034550f40122005a00641c0d5501c010072140ba0988559aa40c010a102070541d41d0305100b0340315617610b1410001462080030310001652031200707034010a018502c5800392035a038041c4501c02542e51019a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 145231384 1250 145230134 145230157
    0x501030c06090608010e010e040606090f0501050a060512010b09150703090f0e090d0f1b05060609060a08071404140406020d060806060310051302090103050307050607090b0702060703090803040b 85
    0x402c0494401c0c02040b145040320080741d28406541c0c00d12030100380e5108050000ca442c59115440452601d80500a9101140c1d4a400c0011190303d018104542002c03942d0022041c854200603651300300c0070584d21076040d104a03000c09035541c0c070b188011410346140040036a20181c404a403a0007010b60040c0f021048035050906191003d0712628070f9a02c1c01d03070988441403640e0055080d104903a008400040d00000a800d00315030030100621f842e420180b1102c400c07112900031404008445c5410240c2d2600b00c8415107071003c4181c1840c8003143d03100154001d40160807102c0384100c2180c2e0755500001d40208030902d82d511641014580382010f1b4018000000d2806d05010300400c1425001480d1031041000900620300c144405020500a245c0a000c018009480c0c0c41c000d0050388840c140d00b40207610a00083d82d403001d40d4240282031445c060074a05c20042d641804005d0620345030b003514a02c507011105941d54a6580ca400c1c3c9550ba0968401d11541c08040750000c3c00e02d451202506009005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 145232634 1250 145231384 145231397
    0x1a01030606080607050406231b06010b0a0e01140f0403030905090a1b120207050f07150903120f110607020102030a110c0307030305061c05010b0f010f02061609090501030c06 76
    0x1c0b50741e81610b8441c22106500055030510080181c6841141c1c0c26040742100600b283d202035602c0e0900c109680141d803810184008120282c0c000d410403c1624014210031451a00b00640508020100800301c1d183c941040040c40d2041c11090014003154488100c0080895075240d49280280180340c0f54403465110f4071030500011030282444c0070f00800e884d607040500440f071484001c241c0d04001c55025909102e9424411035002074401c101360030f13491101307000501e0b6483c5480340c421078049401051f10200403040d0b004000003100d4131000d044a0017181030055910f140c548085610f0396103861010298031601b02071182003078044d40294026600c52005128208031407100d51401d00c2807080c80c0b0140d03401001082d0201c5c1c401d80c0b01c55000240103189000c0d00d07507e0b800100340d90724452000c0c0c684e070f55660700e08411454489010841c495007030800d131021803100d8001a49610008009210300c4940c1ca0185000601c265042c1d809000040d204200701c0d40c59003818503280441e0f0051801080710b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 145233884 1250 145232634 145232639
    0x30c010519060602150a020a0507080403111009080604031422031b03031706030a02090a02180a0e040b0c1e212701090804060e090609150d020d1a01030606 68
    0x201044d603410100154012000070b841c3c03048803500a622800000c009c002d004d00a1100003100c0740d005000075401243c000341c40d41c400008012075142c8108101051100e000800c12480c41c0c04074802d80d0042d01420070130381c03081000400c42d11a204500d00101202c5003241d031001e26035040a102401e803802500441a003204e8440380d462640341a010140110701e4403020710031028015155264400e10280075108141d03007030f40c00701e0400d120a80700301040680106210340362480015115440c090100c0da01c800321480c0c00d400703905812010700041d01c413503581400551140c84000850303101c4512884110715012041d1502030682d000b1002d650755490300303440a00d01e0030120059060046c0501c282910040d064030840003190211018409019520350404402040d4041c019000812590300e07000c440028070401c000034444000d1034141311b044614144101c900d800d44505150070400e85a400c480c0d01140000341e804615008010806040d00c2c105407003400342110010b0489100d105c09004054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 145235134 1250 145233884 145233887
    0x1902070504020a0e04150801090b07020d0c08040303050901090506030109060302030c0a0f121b090b270705130302090c0703020607110a020405070329010e0609060318030c0105190606 80
    0x41406001c00001d002c012100070549020741c40300b612001b00ca024000d1703072551110b01c03030700303403410124140c403070079074240421003903d40620403030803800100e1600805400303082c0c1c4d5810081c003031808080c04018000c16419641e90089041801800005001da81c0301d6035038049a101410482c0400c900034010020512110b0a1054040307054400c8401090b41450810800c0b0011056440c41130720794090f940c0000341e0050032400d01c5005090500d8020a030b50310500309125004815000c1d000d6016114841400480c0e45c140c82507410900c145000e80d50f447c83c1882d84160440180c201952143c0400140a44100c0750802030040507c242c00355411035441c1e0009888108240f50720010710740190810500501d0142c1c41698850183c0c100000d800009019000355100080300702410030074414122b05045d0307081201e007114401c08807841454800c0c1d94001c103a80b408003521a0640000d40502c46815000c01c1c13094a805160141c020401031400c10301030614040018010386070540303001b00c040382d0203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 145236384 1250 145235134 145235137
    0x130816060507080708030705070c0f0311010203070c1710050a020a03111206010305041401140a1b050904020d0605190306110307020d0c051608150601050702130b03010b0402190207050402 82
    0x607034101415030308041c856290708101b80d100824200c20850108100800141c018800c1405051124100034402e401c3d450440c0518900d10f80803410356009019080015106c171103480c050322212418441ccc1000c4001c0c0403481c1c4001c002130486103030705003010083e0300206940035206502081e80c05014070101d440c010056845070302d8030390600e15007020000e0410b5002e50881508984079503003074a141001c480a80d07007140c000344180359140b0005010702c030b030949050080e016007090340410030003008001c013000b0f0014410150720300d020b1074000c42e513440142140d6000c10010038014001c03517012061140401c010080a00044031014035001340110140c0600d01034a10880c450380080c07080c810102010f44094204040c00c85091183c00c07443c5d00b400740b0000941009203c420010010325400448980d0801001800e80c0c0c1040f00600860340540d407103081240a032498500001904101800441c0c0540240154540c12500019035211490b105c0c0c00d845000b003590341d0a440c201c94440302084282d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 145237634 1250 145236384 145236397
    0x111e0f0c0f0d180e040c0302040c02030702030c0301061d04060e070b0a030e0102040501050f07060e030c16090b090103140c1c03020d020105010e06040b03010b1207030215030f0f0604021308160605 86
    0x38002003000c2c044d880840c0c1030190000d001e8050041841da076903000905070b81c810309801005070000319100c411810f04001d10030005204a00a204131030518000041080e10b080003502c51440c1cbc0000703d42840b280754407c2b807444202ca804d449615840c1c400410700313680840b114100107480d1480351010020180300b0f071000d840e81603540c41c5c0781420b4079080c43e40c142c2018209445040c1d603100301004200c0c1c108010041c0700d010401070844125a40d00c050041015640050200c50501c214010103503a0050001c1c1942e50200419460381404002d02d46090041c101c80d981101c2e4002e0f800380c800c1e81c1d205407210428404d50031901c50302c0461101301d0a903002031044c2602250205c0c00b080300da14094010300300000303014000003074401160f40041c2c2c051106480c40c2095070052081813081d41481e0440030390045200c446645581031144a2050810004202c0000440584003042c800d035625011a00c110401c050071b1090503885c2d83c0b80c907131540d00c40c8610141c924a54100001c125000ba415200c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 145238884 1250 145237634 145237667
    0x2030f0312071d1201050106091a0d0e030408120304020a290d090b040803060a0e01150302070c080313180b010e0618180613111e0f0c0f0d 61
    0x32603140c0341000d940115055200c14980241030f145450310341c60300b041c40d07101402d41000105180d403402002518070106904140d01c1c3c54240c5444011052002046560601e1a0f5000023003107505010307828118003e5401c00c0d11680034a100580303402a55101540c09a0f0007150036500951b543d8001c040380250700d04c0e2901d80c940307075044801b406c00f0b68480074010b1054070701008140c042031940c1d041c080020480d4100d850480100034090b0604011400d40058080350200b1841941000607000824005c12404c1081540000e64001048851540c1c0340043c215001165168210821039000052040c01014011a030055049035105c5950103010b58102c010307190403402c585c200051101540c030841c0c64000c202e20404840200740c442a8070070015222100c20400c00d41030070340c1004546000284403400a90030503501501a01182c0c0881d15403c140001d403414940e80d01c0440070407401424680496490301042c02c110300070000c281da03d0700001c0c040944004954000094178003400d2001d1800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 145240134 1250 145238884 145238917
    0x703050906130318060903050d05030408160c03080703050a02100b060703051b0607091e1a0304060f020a1d0a030b010b0307020f0d030b040506010306080d050f09090a050402030f03 79
    0x2d00000003580500d021600030300d884420448050b0403241188a00d07800704001a500d1241002848000c1c4940001e885076480d007503141d0308054407000760720b00590311500158a0704291203410095504100307001103034080d50054840700d043c00d0261258015003000390160160408040522159110390035400400a052505080903078a00b02c95a80140741c1c40c8562844410403403090100400036a0302c921403035503132410700c14203000c40010303290342d44800c1c80f0701e210032a84148102407000c42d14039140d1030020a03860b2a5074590400034050180144070322001c620000e08164030b02d0703000603000707081c42900303824994120114045c440d5281c80b40c403000d881c3d541c9880050010041c40301c001c50f0441d4441c812a0605001c032a29682407010403104040481d6480000c60028103050041ca40d000a090804003d503600d00350066071a0418000048104980040c14a49880d25a02039600302103014219405074501500c000e40100f42c1074406038424820818000403854000085440710000742ca440c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 145241384 1250 145240134 145240141
    0xf0304090c050903011a011e14070f0b0103031107050102070302030a14070f090203041a310605130309080a080a0806010507020907081f0b070b060f060c0a0201080703050906 76
    0x19001014140c070044200001002207514555090061300001c24500340048409880c0c00d001501c00c0c008089000c618040403181c030b0039800d403c0b0507115815002d400000c0d80c0c0702454502100c0c102c0d11150001c0914980c0300002c0300f410b92200c807244441c092601211070b5240c441c40160780d580514400250b269003c010803a0021308003550200300182404210b45549442d101c9991806d00b050b04022102d070b03401b0003000107004e03400e001a068442e07000b07521403050405440200141005081c600c0b08034052940d84560360b50003400700520706401c41005c102c80d003000d49030007411591000003503000071001140440e03804d1000c1402d0701010b60000d045860101017190564803c2e000400c110f0502000788443c1001d40c5507002a113100d0b54099845501c40d1806882400d02480e42003040400340109081c00c0c0260f9070b401c400c031500720750840316a00b650782d10000014909034944041d07a8020b0000f083c21001400c0000308200000d100344c807482250394a4800840c01c80c1c4c8111001403c680c40503010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 145242634 1250 145241384 145241399
    0x10b060408250512011407031806050c1c0f05010b043807121e02070e1005030a05060f0604020702060706050a0e0d021e0a030818010e010507120b030f0304 68
    0x40054a8a6040b800403040342e503540000e0046004e500c9121180c1d456400d90f0700e000021040040d0321400908080050401500814003001c5140c0c100408981e0f0301c3c2c0118102150907415240c609044005003072014081c11039090142c010795480100040c203043c00440c10070603100131750307090b01d44805011004007880031201204030002c6e404103508402e50000302c108142d003034004100c4c0c075010f07002614103100c51070070003808884098481e1840070300130b016960050754046504021038146034241900c90300c0c1c100c04010000a00c3e803009030705100c0d00036100e04002d4081801889201130120349c1441b641c455042c070003070b4884d00704020f5001a08100000014904c2e41c0300c00d4002c84403d00000d80d800c021181c02e485e181a8940d0b1a0150f40000540600078100840100c1100840400342240040540c0d015060400203008190141400405862809000d52007000c561000c40c00a03ca68206800054019401d0301c0303007444070710b052040004140c103001804041310b110000055140c50b2034802c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 145243884 1250 145242634 145242673
    0x3020919140c161401020301090b030f0d050a0c020103110309010c020706030c050a050f120c13091509050601180603020a090501020307020109090b010e030312010e060306070f180305010f0509010b060408 89
    0x4112565000207070344c0a9425401d2010b5800f81801400005001e0702d100b04241c5804600b076100300c050307404102e5101d101c40e400020343c0c0c0410034038101441c651a1510059010b007101e080f042da6803c10100412008400540050b480006282c090300c0b05aa12541c085040c0c6602d5005200814002c00880d0480b500c5500100681900c603808603040518128070f5040d0440143c90581026402103504500f614100340318400410a1032401c00040741a203c10000d4451139100d038149180d9517030002001640500d0141c000000100841c602d51038840b41c005e0000e4000c1e4503500001000d100c00850a94000404c45149a40503103c0c500383c0c603e410003280191200704c01d458100001c01c94044030544040019050300300d01c44192803a59030520000c48481c14004280c0e80c800c0d440801480400c03604104809001c030014a00079000321512114105407821903400148a07600c1d1160301c040070749556100c58011140d80c0000c0c45007200c007004000190103940645180d5070420300215100c141d1095 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 145245134 1250 145243884 145243927
    0x30e190308040c051c0203010b0414060d14030c0105010f0608040203060a0e10180b070519050307030b09040515060a0f1403070e070c0605101d06040603020919140c 72
    0x34520003c0d600c482c0416a65400c104404d00340007028102001103250a0048030000c40302510100408095460b00303240c40340b406000c10307006821240d104018400c98040d0050348040c45000c4030382d609400c803141402407009204c0c03401c012252580c0810b80e244a40c0703102e401a5002802002d050320b805004900234940c52482d0b004601c1541c0040303010382024007810011551140203659034510a0400050b038034401008401000000c1000503034044100368030354200307801c83c40d0998680c1d6a450b0160b0091480308c3d1003d034002c0d0000100020460001045080140a410110310301d03118001441042c00003400f40606400d1b2000c420701405018001d9250401070040440f08402d03640c240b05400000191241800a03174003866585c2806030170300426402c800500c0381020f8031440c0c150408030180d00c2031011032040c10b000d404100d0603a1036401800c0690b800603c2d052881c01c9c000702c03c4500d00100b9100000c0a0b0500c030307114507940c0e02d0000592140110a886501c2d010040707901c03019a16819 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 145246384 1250 145245134 145245143
    0x509040603021003140901020a090b07050a020a0314100903020c2803060518032b0f0501080705030c03010501080a030c0f0602030c090f1002070302121504050c01030e19030804 77
    0x10100080966103410a0400701503c03900c0005880c982035041ea220040002c08540341d0ba801001000c4503154030038000802c9819405c511503d50005190550a0035a508806503006260043c00320078008012400c92544907031000701e882c0d03402915000f400341c844400d400f801580044020441c18103180c0602e11404003440381c62141340130880a0310b00789a2241c0c00c1954015510360400000100849520f40d03402202c100560412100502e03445807410014180450707000301079110b182d0103a55030040d99105400942c280a29a114160107039103074800c0c8541c0d4400d120305010fa10707c2d41010300c0389030305850042e806441035801075201a40d1a4026400840d100324500429a01040707551000d0341c02501c9800c94665142c10350707070800c42000c8100c00f406d80305071005805501e5041d000140d03002100d42c1520102200d0030380300c1a0608046602d00d4480000c510142048100140031502d140d01c44000d0324200400b200c0091441d50701c12405856103c2c1c807042c0100100824040c01280d0b920034440d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 145247634 1250 145246384 145246391
    0x26010312030609090606050301050f010807060509130e0c0a050a050a1208070827010f0816091a04170a02102d0806011d010e0f042309010e010b010c03050904 69
    0x503003c00340125211200142e80c4596120340c1030246150a01800e03800c00c481e01e05d115980c1d4186202c441d2034040c01d00c01c0c1c02c1070140c00512146581c40300f4090f5129070805240800001d8007160200ea285d055031f080702441041135510101e8280382580d40d09081d0ba0000e4020305455040114a00c200760100000b40c91040007402800300007131105001380002045030703034182540200d51400600d54510000014140610800c400840540c0050701950140c184002200f80654a0800ba10741e024143c005050700300000e40300c4d180113a0034500500842d2801c8580241060744c250078240c451341e5090f4004d44c0304441e9901200c0c5144124036416445480e19220805048400d01b1001184980c1130183d0100d031140041106c550380107405400070b1181005256600b2000c00c00003446028500403403031245101c0790360f41240303440c0c0b68048585148211580d0390100300903080485c44082c04c8406032007545c04d1400151002d070060080e800740082c10b848005c00314000b41e44c150744d203410030034025800994 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 145248884 1250 145247634 145247639
    0xf030f0c03060203090f01060806130b06150a050c0601090e0a290a0f0b0d170a0c06020a020703140309060a03020c01020d110d0b120304120c090516260103120306 71
    0xb83c401940a41c500c0c900901007607800380d41300c90940d80c40750321950280e0000307020080c0200b10490b901d515643d00000308101c6030f03240c3d0005480c035040c80b0b000502032600803c401c0e0201d40c1010040c04511000c40484200b60f80c0e88551000b960103904030542c5542140d00c0450010381302c0c440200303c1c4d00d04450880c2e03161803101604801c209085030701c0301d10540ca5840120120703203240305170f0440d0b040c00e5032101103509040e16845d02820003d1120075562900140ba010954405d41c0220146580000d09555946551070001d6071240e0500095840c0c8016480288001100004845030080003501c501e040c420a0754094000303400500011120f55000c01c4140f6031881c032882143d052410308513815440300446810001141c6514120324003404c2c05030301055050400109a504650418903041c00540c807620b0100c0c1029881d9002088141c00c0006000c04940724004516105c800d941d5100c0701d600c550750412140900f040400200210070400600c04035204c40c0e803900d151021f0f07040100e44540d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 145250134 1250 145248884 145248893
    0x1005060111030c0604062307202506020a1505040c090c170610050f0904061211040c0311030a0c031e0b09070206041e03020118030809160f030f0c03 65
    0x24007092100c000fa800240c10041040440d100d90030310300d184c615400300c201070f0040c1800f00100000d006002881075103036000d0490801502542c81142004055542c820704284134145849100841035141c40750703104021038103910014030000c0300764000840000e0b500a5007403c3d0020311000e40b0030740d0840c486100201e90084180a2824030041f941c0d550406003413882a010300f05580604580d2007030041c000d07100f0f5810703440019190441800030340c142d5504030744d000145c014440743d8030100e21a518440180240043c100840a421030140d07402e00035024038140850849010380b45d0004144001c4c004504103044661290050500a040c0002e00308005149130071000c00000b20905c10076101c1610600b941407100240e504401c0c5d5000409131421700355510b5403151074800d035120740c1c40b424100c2201814800d4100031090078006a104107012400c0c00c00800c00303042103400c804240f0810041c0e6900c800022555412104100c404042d202e0440d600e8244050340e40c030043d107070001d042d038000c80400d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 145251384 1250 145250134 145250137
    0x1806120c1b0c06040302040b0a03050d050c0105130b070c03021f09060f0513030c0f0f0b0609090f070b130b040b0403050d0c15050403170a0c02070e0405100506011103 73
    0xd2040c200510348910114902064040c0c902400e2a1940c1107640401e500d600c0307000c02c0d039003034039411140400d1040600c404184c512015500140c0745100c4d01c07549181d41070708000246011080007000340100c0d9229031120043c0d582c40d0000402882c4005c2c00284200d00c580301d1950f255200c0d02c1551090300c00d00c841d1201100b00541a4100182d4507003600c820402e052003800003462401c541406180f0300f611280040418581e030250a2080111808040060514170343c50a0f0354070941e80300c00c0b039149060800321070a0456201c0c0c0244008404181800000100008680300b1000148210303030400d001e420352a081a0390045910074440700128000c585131011b00054070168004907112440c5007002868040010f007180180303c030507032201006c98004411150100c0c01d90300d000c601a2114a8200c503c4041c1010360030804001c1c000340b1200c6002da030441c0020501c1d5900300c0701c5d1251140e81e180380010003510700138420f90041035505103580c4150807160388024141000b0b5004016030f842142103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 145252634 1250 145251384 145251391
    0x6030506060a0504060b0a050705120a031d0f1e0712121808031801050c101b090605031609050603010806091c02030702192d09090305180612 62
    0x890300500204101402c08005500080c0300440e03060180c50300c6c3c00140c80c030922402403101c00f0000001100303800e0040400c0021582d201c020aa1941c408075204010002c010807900d03080c01d17112803c1c16820780c4600145030f49a0181c1c0304c000e06800c00711144101147e80c8004100f410a0250b01e40000d00c000350b90641210b1746000e05003210104180b0a070041c01c1d020151b024021500c0359280a102c201c6000042d500281004580140e000781c0038001641c15003d1207140714280d00c00c1d841e05018003c445d1700140d1120307440950244084c1d94881c415125541c0900544000810a0001a0303000b40c000c102984819100c1c208214071b141c03a000403a02680c0241c201415980c410401d22040b43c1c0d00f00018176a910707502c5010001c103c003060000b500d0344190748000e4402c0d81e00e0444941e83c08032a070300e03950040507041036a00507880440c06a4075440d0b841c26007912000701e070540014004425009002c0c0b40d50345551654a026000449241041c51200c0c000350850303c1804a400b40e086d680c08078601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 145253884 1250 145252634 145252643
    0xb040603020609300c030114010608071110020a030b03070503070510080a060306022a12040303080403020c03061311030601060503040b280204051002070305030a0f030207060f02040602060a1404030807120603 91
    0x4c441c005c000c10305081d141c04182c000c90b01c0c40183c00402011b50f205c00c42c50b410031940d2400300c268070b080500403450200180b02003240c0303510008417440c2c69509a40829400041501916500e650f01c004064440070f007442110b40002c1c40b103034801040c80c131410030964007601f0582c0c00110355803261034402c100d8111080b04130360030b030344010040d945444100358480070764401c00060240000c031000041041c06075210040510107490302240c101030080c40f5600d11a0b1005d001c5905929029400d042c0c0c440e1003400680e26020308600306a454100451701c6410303a8000c1d1161461074503959150121044000c1032100325041010751b00412001c441200310011200403070141e112070610040200c5036401002082c15580040403c1002980220a469680080e4207005142c00d4105009401a00c1017960003041185000000305031110070382d02400c140ca0060b0308884803030384c5044c900d0b4110390407105507c07031a03017040c4005000640300384481940159a0314010f030140c00c41c0300c0e002c0305a9405400454 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 145255134 1250 145253884 145253893
    0xf080c010212090703030e0d1103151006020723030307060c1205010b0711040b1207080102040f051c0b06060f03270d0c02090c090310020d0b04060302060930 69
    0x1000621428141c0f900710150340c0107460200d25650b0f01400e0041e02c844020b001e0f00d506408481031040280c1542048038000e801d5400e000000823203c6d00c0998100e820314210401d101020035a1480028410265103521404505180c1c0c11500350704080000741c04d89500d40300801c00e040c0028254091918640c0251700c5801c0310700c141c00002001e0300c3d01600001304800c010320543c804260300100b000c040300c40075540020550040d40c08500c40c0c0301503c2c0c407071403c0d10034190b0001f0b042c0f105500601c200c640300c0c540c02c56496243e808222002d60030b00d0100c07500c46100c0d0510070202d180950181e8001d80002c0544e0715104180c107528180c1c1c2c00c11a00a400990740b52502e4820303102c07080c01d0180001100006e04051090303904083c05041c2085006405040c060b000074215112070342c1100c030801001001c03200d204401381d01e030710040c1d401454424241803c201002d40c0f2810940103060079a83d00500441c213200c450b6003409800c0b1030040d004c3c03601030700f0350a41b410828011090410007000703400c01341 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 145256384 1250 145255134 145255147
    0xf040e040510050402010e1306080703030c150e0d0311040f0602160b160b0901060902070b18030a05031603110c07050102071a04052812020117090c06070f080c0102 72
    0x3a8200b015004030050a07a090204200040c0e0380442104540102100e8280c0341c03024560f4020000c08094100c0c106611501d2008000d00d504004d0800c07102d40f1031f005d200d0300400190030840aa80115031802001d501c03d05075204400e0184d00001c1c800c2101100003418582c1d21217500341d4911080c1e020300050380045100c0440041c2c0c1c144044060200f081880d0314140d401c0f1300c4c049200708040300c0135010190380c102280c65680c0a4100c08002d20b03010300c05540322805401d0041e1002c4007610480c02e10300d840740f241c4c3c0c241030002c001c0e1aa112559100d07107003195162040900410500c04114082580d140b02c6001c006a410b0b0143c02c450031480020110b1b03600303050001e4604141754205003a00e6990a0071920030301c034040c04a805481003078074400c04001c4074407443c2814480e803100a44594840103008030300548961f000e9840035000b43d8071030801201903000f0500040c02510700542c580c01c01c40c8000d080381000c0004103400b0f0701c0b4280001c500f010a8980c80501d80084e444180c1594002845 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 145257634 1250 145256384 145256393
    0x615030d110d0c06060f060314011715090a05060403030501170102070804090c0c1e0b0106033602090903191d0108060f0402120106030c09030b0c0903030f040e04 71
    0x120400016103040c810000c64004400039a00c0c1107941c20342c000c01207151809000c0007215048880142108001880e4054a41c0406130280c100031810f5001c2041d50790000581c503a81169209002440f1409480c0490800b58908403c540c0200700e500340f84900800c100014404002c3c40e8412802a41e0020f455410300e40f0841044044008030a8070782e0060110346c0114817142c04a80840c2c040240006100cac0099500746c0d1081d26440010f416071405841c41200380c0306d2014107003c06442001c1c89010750380c0310081a4121804901010490300c6544141001031044210b4001c3c007001e40900e40c0c407003100e1350780040c540754422070b03c040c001d420100300c0e500500f000751001a600034050400880450800e003c03095507401c0001c1c00f90401c110301c00407501c542c4a844000a8210015006542da050040c2074014031090a00c50400001d161443c01000c1a01ca5000d51042e240c0c050b00c00302d030761717103807002401d6154000075501581800100403242c21008004010b00003130419185411861815041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 145258884 1250 145257634 145257643
    0x12080603060703090302030f07051603060c23090d05011b020a050607020d020d08060a05040903050307021002030c0d0f0e190302070b0a080112031808010b04050a020f0403030807020f061503 83
    0x81000c1c18101306404d00001d402009995540300203130382c9241c661f00349040c800d190102d5021758203000402d401022040c80701d250050414030310b00b0b0301ca102401c181094030009049545016003198a0f00b4040d800c42d51801000e2140d5a6001d040049041080c0800040600203800320002c00740c1d00c070307800b2141000414820b1641c01030680c00500114070303d2800282d2200302e85034440d01049030507800940d40b035031000e080348080d000c06801040031441d10f18019116510a5072600d02500c03801034422822040c1d8003c807489100000c0e101414030b4034401000300a410900003607107403581c5030b0305c8916170000200100300c0c2036842241d1241400752141400707428445590020f1040b0301c3c04000c00714480e82c00800841c115a005048503111031202e00301105e101b08540058034000080540005100c00c05400c510007564085070204050346407060365404074480c41c0e044040c140704c244001c002080c06410f00031760150440c01510301b031458010010b400c0c14000c946a4a40003052201040903060800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 145260134 1250 145258884 145258891
    0x907030b0f0315040305030709120303090311120417030d051f150503040b06010e090403050c0106060e0f061c1418010c0206010e06010c141e0a0c0506030a0204031208060306 76
    0x140a42840e50f20060702440c40e850082020301401000004a0400c0d4402c50341070008080b19403800031294107034036004020b03052600080d000954003640080c601503002c00d0440c0b11042544442c0d103420f00e0010300b200009034044494106000520032a004003609005040c45490b0b13080c6024040b0052a584d4910340740960015003000c101c08441010540e0031901f120341240d08542c01d0507403552500012140e480741d05074101c1c0c000d00640700b80070806402030b01a008a0030504000c2c4103082d03c61004850b00c0b40c0c0000007039403090005c0340c244030300e0400000412501201840c40b42c11701b818401e000c41910740d10700130200040c81e05c1d0104141c3e00c5642108103490480e1400030301c03100c1d603c6000203640d2001030003240854419100854001c0e8010749240790240d5202d00c00000308000072184540718804e400401010040e0200c501202c66004600b007a1810ba02101803101941484c1c180549a00000c110440281c0e0030040070000c140c00700c56031461a0110365032a08140340c0102071506040024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 145261384 1250 145260134 145260139
    0x140613030c0209061c030305060103050603120d05070306150203040f0b190e0112060e04021207030b150103020423131104060503040816050f0d0e060706021303020907030b0f 76
    0x1512120010780c0c05484004955012140c070302c0f40e03480f00d500080b1003001e80c0c903080246803525080c510030150103401162140509880400490341c445041c55281c082c55185551806c4080001512022044d489580c00012034503000800a40740c0b03034400d0044410f0801000940d00200b0b0410040710403095420207030075280341c154140344500c006404d07c100c00720138050920815404000c0d003a40300303021100398480c03415000d000300d946d0f0f20701c10b0600c09815201607000d1002004103502c10701c00000d50200312544603a409141e030780c1d040c0d40c0039080000700c1501030400d82c00b003000054458180783c44d090b0041000d0031a041c9800030a01b046403030381440308031000303560030300d07602c010b0104100d030903581110741c24105140e07256a00e150600d40c034810403071103585000d100b0a486050100004500c03101350460320448401e1700c0c0803101952603803415030b1104d03400354041158200040d480e402501071421039101c00c4030080d890b81c0c00100065001c5840e003000a41d030b03041010341460105105041b28105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 145262634 1250 145261384 145261411
    0x4060b0604140d060b0a1e05040203060f01082d0708160e0d060905100204081603020901061101021c05091b0a05010c170711010908010527191406 64
    0x14180818901c14001a08a100e40343c054002010f100c226000a01c0201000308140301c119160801e800510081000081c4405101c07100818603003811305c200d0380a0080244450320050440004460702d1400030301c261040404407808051150110f2416400c40a0f418a040c8181c81d000e5002825424001d0032810300d201000c1c400001d25805c01c0842080202c1510800440e01081c18003001400c007a1500409600c9480e000c039540e00415809082500d903400c1c241c0713007a40900100c40c103111583c0d0001951100341c50004010483c09510740d002d4101e0b05600140c14081581e0f08100d0305035941c14280440d6403150304000c1c4060b8280304102e010064085402c002040100218955900dc1e015240c1400b942103004401d02810685010306031540c00f030b03090340e1400140750815042e6031130030940c0e0110313584030004585d0307400600800d8070a03003d102d9103803101203148d6440581d803c803840d452112030154080d424240d80c0c2401441c1c0d22140070f00d0703c589942c1540145a868807070300408001d0040c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 145263884 1250 145262634 145262639
    0x711030313031e1406090705150409021e070c2405040504090501060b03040309180203241f0503061003050601022e0501060309050d030608191a04030804060b0604 71
    0x80031414002620740002e6103602c000144807410400f91400200601200d6070301c90607511055000500920550752403083d500031076520418007007134110082e162020030005000c2882590001e82c003404015880506e220511103400c0c1140d0000e82c04282c0544460100e10001c2c0108005440441040107543e1400b10041d200580001d107280a9030044910980d203a20018003400006d4100801500d0b10314869583c83c02c1c00d00c0d000e071a440261080411080c01c5c0a1001d000502c94801c1e00d00c03442c020200042c204100302c1c2d000c010013032200480c50b403060414080408411050003c42c4501905841c2d003a41e82c2405070401240100032041d817020141041c0401129907408203015494404c00500c6610f0000300d1b2807424040303c0106400138009140c2000091041e42c03640010321b03618094001d803450640b0640d000c4090350754501824149510840c0f4240c0518251401d1031040c6004126410074070510000010b03c801c0240c0c0c0176800900304d041400700303122581c801c0d504060000c41d210b9103000d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 145265134 1250 145263884 145263907
    0x90a020d1d07120507080607172202040f1401090b040f061a0f041a090414010e01060c050c0303030703050609010806060a03021005131502010b0118031101020a050a060207110303 78
    0x12401d020f44200100c0780071040e01004410070030b0300080c0101400751001c1c1d1420326401080c2ea620710425900c0080c1e180f001c90012114050000c15903803000460005041070b9030280409440c01c00d8211100d00c0ea42c01007102e05c20300d059051400b03414507104c00300350816032604100a031031082582110940c901401080404003034903207d41c100b001c40c40300369290140031364030a030280120380c04480d4014108007912011523030f00005103504001103500300b000300c0200000d054080d8090003400505031f14000188021070040c00410f030424401c00c01c9540d1703103a60501090845d08199400d5012940729801c1c045a46081c001c100c0c0035002300c0c40107005134940307500005c000661511019010702e0712402d0060b01203100d40d040303648120403001c4218909640b030a403110a05c07811414440154070703061004100b50301c0341c1b8110002003840f10429050a0860b2240ca040c2c1400e41c0b4510705600c1072104040000e14240200003610307000310383c0141c0390032050070702d684200c4442810a2090b001002110740d40c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 145266384 1250 145265134 145265143
    0x1209030106090b0d0f0311070608040311061e1915031403190c030c02031f06060203040e01050f0f090c13170a06090c0b070c0807080304050319060b090a020d1d 70
    0x1d1703400010044440c100d0b0708050b100b00c0700c08810303031407240540080403810a4011101c070b070150f4403a0343c910f00070800e007a544a898200660b9400c1c070990075602c2249580c441e40b507125800c0180400c407108a5060301c40701508a4138081404442028808020001e01024481c004000701c0c4800140d450b0a0300603141c5180303400b0b8440d44005102c2020103650616215604103d0b5042e40038049680c070007500c4840e64100c8904800e0520001c0c2401c501165a62000c810b03941222501c0d08203000b00c3e400c080c00c11408000603494203800410010745041107959513008180901300720311100303030b82d04400f1400012010840d00000b905810031490303031500d0303400080d0142c80c0c1e5400034000251aa02450400b2003c41c1c6036209114224011440308180f02d13001304c100040380c1e48142100c1103243d40e061030076164040d92062940c1038021404078003444001e5505a13647d1440f9a400240b0700980b4000691840c5043c1c0b02121035503408654562140c80c14410395960242c1e500b960040c1140034450703540da6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 145267634 1250 145266384 145266409
    0x50406080f0607050703091a0d0507051801051c020f03160203070305040918120e1206040b0105061c05130b0a0624090e09030307090e01030f12020f1209030106090b 72
    0x4c01c08000780190a26110f03030100c1e800380a05020301c0d07407180000000b844264005a10f110750180c07401c008144107502038000c907500d440c1051011000007056100544031034101c050344000200d695100c44401d0f0356140f00600014080800c800d89038240440c0903808154501c80905c25503100304070060100c2e40010594048406100c0003048400c0c00000b24030400c0d1280500601c16408608036013031003070300318107000b28900d8142c5040100600e660841a500c940a58015003858446d100600680c107140000303243c40070110041d07003081c0c0300b035582e114200c1d04205d801d000200381050003007041202d01070005801000802043c081e16041c008203c50400c1242c0d40c4031144d400d45002c0c55000d5000c2e2052100a00c01402c0c078058a14140446a03140c3e40704031560340010740c0c0c1550200703540c45080c50380c50583ea00560952025882c544d03540740d4000115102030b0941c401c06a00581001d002c110035aa00d42c0c1c00c0345401c0e201d681d004145404e40e58140c002002c15400c0403403005194464100c0c0000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 145268884 1250 145267634 145267637
    0x9150103050c0607080705070f1d0105090403050c071d01150201020a021c140f0403050105090a170307090b0d090501051003050a0b04030309020910030506011a1204031206030c050406080f0607 84
    0x2904e41c0c0d1351401c41c0e01d5114111004140b8080d543c00054034010489014044502100d20b8400001c0c034141800c422070000d010b06a030224001c0b002c1408644590007600c81c040c001c5040701c13a200e0711004109a440204e0303002948544040d00144822072403d00c51405040700ca000a5042140004000e0340b506651108100042233402103414041c1c03182502c161041030459143d81e68942a1003040c3d510f9120b80000c0c5c806600344008100e05107000664504c0146d04001c146008100c645980781d401c1d40090b240c0403c00a08035808210003000714028007050f01c40000016017107a140c0340c4107080d514020031003401c0e103941d1030080000c03610126100382140c1e0700140441c02075603285026402049401d0010750011200420001c200d07d0004002060f00d0140c070403146140c0e6070741007075009484084001210702d0780c14004958511001500d103030f00702e032083c00c04514641c1d46011070b500f140c8081d44141c41c070a5410b4420009400c0c1849a000900782c084003070414a0b038215101e03652904082d15010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 145270134 1250 145268884 145268887
    0x103111f0804020d06060b1209010b0a0807140402040e070309020f040b1c140f070f0801020a050702041a03011109090108030301061e0201090501060605030411040b03070909051e0609150103050c06 86
    0x41040740c05e074046c40142c680d01c3d41941e117801034048042c01920080720134141544c41c2c8074004e0414503114101c2d1040b201c4640080c000241080309800030544000102c5070003035024040404c001800004c042e21881f41030f68000707030f0205980100202d02d5040071040b40120f02e0002100f0705911040708690102c00c4c03517804400110303000c3c58020746d0703d0381501021009000b4540403400070440440c0c042c2c201c41d106d501601035a038a800ca6130b4204e100c0c1101d050f010410411141e0010b0405401c0000360151039011034003c441d034100400d0a4642c468400c00c8145400151410309182200b20603001d499841c00941c10744d0705114018150b034804610300e0503d0140c0380c25004a40d4402d42022a0070b030ba002000b4002195900c4001d8050340041d102125602c0702c0400556550a19100c1c207a28611300400809a43c0e02d8a4141d400401007602c040e50360b4000c040c2c00c45034031013140000105541c01b00c0c0c010100b6262980e0f0550400469140d40d100c06440580108003049002520600c00b44003123803483e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 145271384 1250 145270134 145270159
    0xa06050f0f060409060e010608010b040e0a0e0a060c030e0d0507050d080402191d01050609100503060a0b04140a240e0f10030b090115050f1308060103111f080402 71
    0x50780b07601580d403254004030b0405101240070b254640c0e031181202c5c1d85803540744003039803520140a0540214050606000b01d0400050304018080c0c00a4400c0c3d000c403004d549007100035841c8c000c2524010610180441c2c5c07104000c501a5900704080f03031a58070305182141c20601c3c1c41d601e06451b85030320301a1604004e540404102959241c554003d4045014451a0409a55400070707169210f1440b05920031100b154000003481d081050480f00a8000109104040031514000b59a20740000d000790381c103e80d80e81c00c00704a40c245100100042d145040101c468440d82508024003141c043d04209003804410044944098520a14807074424650820456203400d100109090b6559200340300e620591071072a511070701e90190f1000c0141682610122031507038071107420034080c051104100000502c10071441b0803900414018240d80385440358240700865590220501c0c041d400e0304281c07a103680039078483d034403441c1c134808040d502512640c00e12440c81c041ca90241850400401c00b134080e48450211 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 145272634 1250 145271384 145271389
    0x2130b061209240c07020d03020316080403020307060905060d02030703020906030f0603060615040303030506130204030804141507020d02040e250b03010e0117150a140a06050f0f 78
    0x1511004000d03201e01080701e14104070103540e10802a048880682c00d0000003480c40321005000a21448912049510b044134aa09214054110480039411800284a800b221445c07402c40b900000d070141d002035888508500406040144a40c00181032203400350f4100620385a00080e102182250a00107171643d80d001001d5021b8865642caa69000c0400020000300c816011509405220250308a6100b40e80305000c1c09030049080d000034441c034900340310402c0024400c3c0c00c010303807020001d0072428424074410180000d90704a034000b21000c1c1ca020900384a030081a9240c00e0301890700710b400c1d01e5031810000d072808961084c00d501a001c2e84c1c8072542502551540d4100d10705103494001182d4210030360309401d515083c800746a1062000401000041d02e00e03203d0281e90603102c0d01d502c01500e61740707004500d0700710b8110b9041951b1140034988502e00d610301c2c0a541d080c4a2003030100e003c00c03e80d100403000b81c0c649500038a40300315245000b0341445142c644d03c800c00602c000c155000d14004c1b100200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 145273884 1250 145272634 145272637
    0x60f070b0103210801030215070606150309150b0d0228080d1704020307051c0507080c0a080f060406020307111902040e070e040219030506100f05030a02130b06 70
    0x10240ca90030140300004200480e101e0261030074810f40c0901128042202da08407446142840065481030340511b00040b00503140d002024110301c40c1c20006a020383d01d02d1031103031404890840201080e92a444072060040c00500b00c1581014484104040c02014000581980724548003034016400b8000fa4051211481007002036a00e4034484c00560942c2c40c202140e54200d40120440011404031109803c7c10314052900d000340e900401510352035082c5018840001e18070703810a0b0203400e000c8100c1e004034134184044406081c0c0e0300c002d440c45010005c140441c0d84203503404100c06070311030103041c540c444e0042281a0071a60140016a03207071224a8200e13245d0007482d403560300d180140654180307086581595400324504c250380610038049845c50300340d102ca50f5403042462056801c0c00240040c549824150091a00401c0031034803d40c1b652105480d00ba001c035112505054148000d01c03640c00941d00f14002000c0840040c910000e46501041b200703030214040f021402d4540b8280d81041c0d0b039020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 145275134 1250 145273884 145273897
    0xc0f020a0818060c011d0a0c050d030221040603150303050d0c05040503150906061f230304120905030d050d02090a030515180109030905010f0c050f031c1505060f 71
    0x34441034403161281ea00705d0080c21a40310049450b48203c3d9115150040855840c03002c0340c10040c0c4010107494a000d10010f24030700c8104600314041e25101ca1f61955070101000110852200015111820090081c049400a0056500034401c000c2c003000025030040c1114202050f914011070f00c40d4540409035014061138111356418051b005111004150b1814500e10500781c030740469906071101414080f8064210b42c047d00005486010155198050210060a480c401d100ca01451390354440c01c040c1c07500180c07412203282c082010044882d65001052001411040b4007501c800c40c41c40b1005413061042c150800d1442e90003159034483e599440300d084c402183c006094642c070346070b82c0440c414803280c01c6400458109041501012585052095280302941921a01d808038204001500c0d00304034130304640100000e40008900113107050000804d2541c85100440d00c0309080d40450080041e2001c1c40c40e5010f150031036a000402c283e034001002c4800640381e59956603a1045044c90030300c20302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 145276384 1250 145275134 145275139
    0x304030b06240301060c060b0901061e0507080d0e060f10060e010c06020406090608090f121b0d080a0f0e0a030806030a08031f0603150618170307060c0f020a0818 71
    0x48000965942c02c5100c10f09014440c48023004078540d00820000c0091084c080c080018003292007035554800003204480300700c011421f0203814108a0390781c12243e80d0000038040c44940d280c044000301c1d054208040360300483c1c0c003502012a4501407401d2050880c0c9882032008101a403098400b040e40245ca0801e0160b401520075540c940d01c0c2c2c1d07009001c903d42d611510000844440000340141004112424180181e0010300310500c45440883c0d0343c0e42090000316114032000221444102c0c0070410610440324075203442c116840e05501e003108440b410603420500d2070400954010407900410202090351b0b050034003130100d84445010a20b0f000b40c002c0010300c40300700001400f00c008160b240220b01551015084800e07507444260032001e07243c9200c01800003c50101007400124021004482c2c9624440900e0307400541c1e882c0e00ca030481c40705074102c03c8103420000705807060040c1d41c0240d0ba299407003030030406070351004400000e50350201820090140340b00480e1803060503207014000900b00340d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 145277634 1250 145276384 145276387
    0x9030c0615031407050306070801030807080f0d0e0c01030c0306030f15090b04201e280b07060e010e03030f040501140106051209190201180e100311030304030b0624 72
    0x1040103159580125005c0c0d0340c400c2c403e640c00074059500c03d1461505030707580250054200405039940d081aa04401040d1042c031000b070104030703081ca90f00e106240b91000c00100801c150303012000058100e44242c40070000301070801c00c042c40070072700d2641c400300d18543c002c0c0451100130b00c4615180091280700c10040079803000c04280010300c4500502030802d000e15003590401000c000c01040b1110204c205c09441d403000c3c1d44512003203803034510404d100c40340d12207901c01c07030705e00040b440e282c1c1686041c0c210020805010030454140104c078441e5000524064000300000c018241a41d0b0344c81c00300406014400700302c8800a000c0001c2904410a065903181c003560407561034103006005508404040c00c444000c8100103941d41030300080100c0c600e4a2000019045d10094004588841e00b20361200905000403100041c1c0080100046100b500d030310b188030050604510f40103940c512003d45e0244241d00074402800480d41d1030181c603030029403c54a128a000540c124490650416912041035510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 145278884 1250 145277634 145277663
    0xb0402030c030708090c3708030a03150303080105060d06180501030209160f0e1f021e030304150b220506030c0d051203100e07050a09060309030c061503 67
    0x1c500014502460050b107407801d8a5644c0c00099a8a0040e20a100d81c02030303d140c0340720002c440d54022070300003540080400c0c180140054240c100440759038015900d0340d100140442015606224441008800e8440c0300c41c0d827859514002e14448040c0503040c0300344030010350b100e101401ca82c8000020b10501c3c1001144229038098080204001d110990085c032403400004c441035420707020000302c001c46807100d4144600196040707807070505100d030305074103e00005103805c52480f000d0801401c1e02b529030b00400b80e4010301030958981c21850304c401c580a84c01841408006501c2c52211a0190301c010303000110000304100050250545806c803070386d420410100003405104607007080d40704407025400c48100c0c49594040c407908500c41d81010f801c6411115030307104903070030f1207004580041d14003103203400342511100500055a400d43d841c2000c650b00090010121b9005100c220091510f0f0804005480413600c001d0813078102c1100c000c04260303460003d1105854803000d00009542c11040380c489105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 145280134 1250 145278884 145278901
    0x51f0507050a20040203100303030c03110409050412020a150b060906030a0b011d1302030402030705120d020d0525030207120b040b090a0201020a110411070602031006020304061704060b040203 84
    0x40590b8404a143c00c0640d480707444604241c000c8034090711501c004210342610b561000c0b802004040d001c101016200c0031181e02d000b5580b0090300107001c080d100082d0b1400c0610308602080810901d13201075403c038040d020b004c200402e040c02e44400f01c0c40300c00f282d41f003a6200069807030310138901e10544c40b610100c144920ba50440c0e000704010882a04d44180f005682d0070710300e03081000c40700030a0348142c0c0d901d5851040d01054010750b42003440901100c1c065600ca00000e03002001e03405100302d0075031182d80c0322646283d0400c240c0c2110702d95030500901d44004410780102280c20703032034200c000800c08c8942404041c400c00440000b072030101c20596103203207589030400e10300768290340650310b4410200108014a00c080703600208107505800608038010b003580c0344525000341c10b032280c0c0d12594426100d994445103400500b21030b840f50600595a00e481c81c0041ca0301c580b01d80040e011580180400d00442e0f0704400003000b00d103c800d0b0710303092a980c2e901e1310320080c1002c5da0340385400c02d00101c107100310070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 145281384 1250 145280134 145280153
    0x31103010e190608010b0108070318020d080f0408060406050708010608040803040515090d180503030901200d03020a020114010315020d110a030603050f010207110d081e031501050301051f0507050a 86
    0x301b090780c0e071013800c1c2c03280d050440580352101c41c1d202001c03450407240001807500c1c0c1d0f0900780c900d00c110800b40c2031100b040e9620045130440d84c00105150810b008004c00c00c40705d445020b612940da42400c1d040c1d541805c2e0001d015030b0700180000e00450002001c134040c4003041003040c4c1102000c2022415a03e03040304400d403030303201d0303040200007280628280580744108100c06809a801c00344c01142050301e000300449104c4030326025240401142c84041c0b11081c3c0c00d225954558011703440c0540d40b41c4041500a0841c0c901030440d01f0890301801c01840052500541c1606a80e0700090140e10340c500000d04400a0080001503034010800184811180e80c06400c13090441e400b5005072000e034050500d0b12801d038852140300910b0392018840400162620300c0200350f00703502440380c944c10900d01c50b40140c042d54510b501001902800b004000b4410b0b84500d000640420a00c0d203030b0706551404001c83c40138149413011031207501a030311014150920900645d40c100d6003001c2180c104141038109110349 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 145282634 1250 145281384 145281401
    0xd050106151403041110050f030406020301030b150306010e150909060612030313030f0c0813150201060b090d050a0519030e040218010e031f060f06031103010e19060801 74
    0x1080d004400d840402c0590000d980c801c40c0c100f8035060302403030704108000580004034248400c2c031400b4400d00c2000c1c000e50024602c554465500142d59504500f46619102c3c40140031000055041e204410304e920080780c6941190480106164076449908428102400800d4259000042601004001c40740081c6140c004c07101a24024034501144000d039450b0b12007111120302e42c0c2c64070100c03440000d2054901c5075580c003091516420100480c2d880080760340c841d520080190525040a001c0c0c0c52880c2c44035488842e050008005280c505101940d46004400005205a40c0505501d05104051004103202641310f4140c1c0e00c8a0060f01500d40d101801040640010b400c0b00103d0f0f03210704107403003206e18885c2d01c105440e010080355401103520f01860510582c15004e540c003500b090508a03118504908030080c8040343c9503080c80d00d40360080c40140d001030105402c000d8a05a0000800f088a040d01d8000325012015515491400b0109440084840c070080c54600c000441d2581907100035003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 145283884 1250 145282634 145282637
    0x4060215101a03040615080d2102190e0118030311070306050f040302011a0916120e0f010f021e030c04050d120f090608190603050d09051809070e060d05010615 70
    0x107291081009213281e1500d03000304030003544481002c48c0498000ca0722100e154601c2e08441258903e900701060907030b080038004500d10941d2030b038010151500700d030846104440a18061549101c01107007810700915a2101406000c1e90101030300a882d401e010303401c0655000745085c0083c0c148110381c0c481d64202143c0642c0154a05603480d16017214054224030311000080091200c1d840c0c3d012000e01e000c00700c02ca07030400e000e508a10861007844901458910140580141c00c6c4040150a06807c3d190744a04410445204022500c41d1052410008000540c0201e010342c40303940c0c506107490320384665008240d000008481880400244501c3d24001c000640e41d00255428100c0042e1000e03941c81c0102000320b10b40c03100141207078442e04000181c0c8415400b011684070343d83d849d25801c0c0245201e403540041ca0003c1c00380204e0401814054040b011140b0800032807820218484e124034880c0075a1180c5002d800210f069556151101407010f504140200601a40c0e06012845c07120710106420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 145285134 1250 145283884 145283891
    0x18020409081c0e030f0c03120c09120c1003020703120f060f0e06010c060e0703140102030f0f0702030a05031b12040209090a030c062d0c031104060215101a030406 71
    0x594003045402210f6010441a000350308001c13095070b48852541005110342200d200501611b6100000c8008180c0202c1c00c888501d50b9900d1184103106116004030310301413540c0d102d4198042c058443c3d61104002c10520b28005898070128a0100ca080020300c80d02016a810010410010710b00c40c2e12032401ca580101a6900440c2d9400d1001d0500c80700300c603118003180001c006078002c03c07516040201003401000564010603200e43e1040e0035042141c0c0d1402c4560340c00310400c0408200010420b81000c01e03122403481c1d44c0350600c00213580c1d2080f000c0742c904100000c804580360006122580420800500e011900d0fa40141a009265001114141d114555103c0414940349001c202002000d406035110080684d00e51168000f4204100c22200b000718110404100b000032406d0550078107140050110702c11b03000b2031000303064a814000202107645c08001c10804a5000500e43e071001008001144082e5281155604c2d040540c1c1d11012601560a0030385040043d11002148694411300041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 145286384 1250 145285134 145285177
    0x1401230409030c03030b0609030d050c071a0a050f040504020403050c0307062105090c030a0f0501050f060d0320010204080304180e0604020d050c03070f0305061602030406031802040908 81
    0x1109a034222100070700032607903100000004c05d1080d04440907241010304142c1c40c280c0b050f03000c070303150003500c42020380001c20215985882c00c400384541c900038841032004440c0e28070740548503551489180b5401051100c00079030001ca82200d8070940d001048006c2046445543d00e0901c02e44914004043d02d101e800341400c0070400d1401141850310000d01c0202c10034030b40e5107502c001801414040c00c144690b100c0e076015900942e80400c102d410b058401c09444261021900d0220f017501c00c082c08040002400e4001c01555031101c1c0a100002074252814204030f10301000b215502544a800b400415400000d0101c2e01910010061040b030f108080c44401c50031600040034102c0c3c0300c503880b1142940040c0042000751901c0000061003034082c1d01985c1d280b04849000910300341c0e19a0100b294064907250810622105000301d652204295410b10105030320014003d48a10450243d0402e2555624458091030200d4640401c480c1d40a0010801c090b158184807101d07410000e500300070320600f01600c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 145287634 1250 145286384 145286389
    0x1407030c03050d0f081305010902030a0c0e01090b0102192a15020601081908130f09050c03191a0d06060f0605040e0106080c070b040606140a050d0f06140123 69
    0x443c04e9099135480c580d07035031250144400c0c070000c0c26500f500c3c5592605050009a64144650540c10f0310860902070902e1403d41d1083e0309200580c0285c190303a2030f06210b000543d07000305018000103890000c41920504501d000d0a01d151427450404400c0744403004001d000c1c8200e50300b0001d03a040e020300780c160010386801c00c0360341c0d4409000d0340c1740d250807406c04513010f44108138116038058828203019003082c80d80000b45c4107030f081950200c0c000b40240041000802c030240310b419003010014920501d145000b001c02c01d036000c015150481c0b019038030319400d41c1010f0f940301414010300008081c252080c1450800d000a0001406400707180ca09010000072110701070303000c0f14100c510310491a510f0b681780040c16141c201f4000c1000c0c11414080114000040a0100c02482107128120003d40c0c94107084425190b00000f440041c041d41a01d0f0090240d503032480c080940c000c0d4480080d441130070b01340c0b901d032001c0c1001c031078800d141c0c0d41d01c0c0002150107414103220813048041e1403000204080031004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 145288884 1250 145287634 145287647
    0x40306051015020105040b1308161a0c0d05010501171b0d0c08041101020d020a0305032502010e0c0a0b040b03091005270109030806090702010b13020d05090304030302060609041407030c03050d 84
    0x43c01080f805040107098050002c40cac400044040c0200d00d000d06002103110340c0350700260200c0721898100f0700000c3d540600842c034880c282c094103081c0b8214010102d41e2600803410803010305403165482e2174130460b2007071580c200100c0d58900c40091040c054001c03090006442d8500035502214503100a00c40b2000c00c0d440001c20f1600488140d0052501c008103440070f469560000e00000b4003013008003894209000d048010b00301c005025400021030804a03644035003056211a00b80384122008142001400c01100540c0d050b506030300006560781c0c681a0985241034440100803000a0405040200810502000030300c0303400700d80700c18481c000d080405103080f039000001c018045038460010270003d08103e01820791000300360000080c0008403c001034241d140d81109004881c0d00080ca103a00c0c0030b0381d400b445800045502c0118145425503401a44030217004142da4090399112000409010445444a1004281c041900c0e034082d12800d040301c4148040c003007540d162080000c0b502c55144500c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 145290134 1250 145288884 145288921
    0x41403010f0b0105031807120b04060c0c0c15091d1806061c0312090b1501020a0203070e0c0f030106020709050c032403030c10020304060e03040b040306051015020105040b 75
    0x1e44e0145141d4982005021500c4101c58541c0305104100c07011400031408030010006500813084001c0d945003e2420700d040d20038074200d40080015541480700095100701c50301060b1000d81012282c01445000704840d0030ba46035101c030001c800004060303c0c0070780c00340b0341e094090303903060381c07084030241240303040030b545000a560702608a840106030b8000c0e44005160703111850706c245400ca00c01092a0500000c0d10036a480c140da0703000405090141c2501c5071036a40810400a0010f00103203400c9800007915800680700740c1c0604a4400300154429040d00110341855002ca28051340301c0d40c480c0c1000b9035a2510f4054040e2491811008c10541d400307590669100d2003402d40300141c011a11002e502402080f66082a09444240030302d042085050101c5195682080c00058591071700d420200c043d142c6401c0124880e800810090000001c06004c031030543c0e81100020620361100440881c1980309603000e88c80080000400e648650390641040c0d02450240292020a445001c0038048161942 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 145291384 1250 145290134 145290137
    0x70c0f0f03060209010c05011425081b19080106030501050108010e040609060e2a0103140c0c03040e0a0f0b090705070f020a080a050f0f061303050915041403010f0b01 73
    0x26420070008400740c0080448400625061a41c9032940c2c1c0c809003501c0c11001c8001031210348408011070701001c280f80c502d8001c801440b03c0f01000a03000080d28400d00581107540c1140100ca802130348811070012140090381010040400072901c0b88000c0c0030342c0c1d0a02034100040e0a2400010740c544c80349032040c0c16100300c0380d451202030f1201e980c1c0a00034001e00600312801500c0d007000c40203800c001d00110b04e90981f14140c2140014403448440004801401541e05061178210701085021000440c0c0394440481b9241c0e40d40e1b41d6028010700c0c9580102e42c026184440e490042040401041d004445803801420041c010170225904010000a0407100380000940602c00200461150384441200700d00241200001300e0f141c0e0001420201003d0301541e041c0d211000051804408000d10307680c500c10200504200c4c105541e40000182074150042e040040100323031040d80e66074855030841e101c1d2001c48a1307a0744640d900388600c0700b140807200c010b110b940b90071803a0101c4400c2c4d005896420205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 145292634 1250 145291384 145291409
    0xb04031202010516080403021e03040e0a02030c03010608091204060306080606011e030c170a0501180504020d14031306030e011401050a0302010315080a080d1b080105120c04090602070c0f 82
    0x62139011500340e200100240d0851050211005040407028034103456440c400000d5035465062807004c5448800241030b4030308091040040103191161002600d0540d030280c5406e1001d500ca03100d16500c0c0000184580e107440d10b00280002d00b6035015401413080341c582900340d60507541c40380015240b9100000c048808010900344028203188207900680b010441801c02c0c02e0b22400071035141032841d00484041e0328081da20360050003518441c40b0041d00e145884032041c0581d140c10742c0892051102d041c0c000b40041d060810041901c00140292007100e00039501102c1515a03401004010b02060040e44825500c0d007061040c100b40400c0105058880141404040c51710750360046008200020368081300c1441030401207001d100038072101406a000718002c0f6254100da0614400310b41e000c200d085411a8107800743e04405401c0f80d8414112801100c400050707038400032000b03082000751481c40d68031034500005902040800e5001d441401d015510710401251980103080325684240030b040c0c001c2c00c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 145293884 1250 145292634 145292671
    0x30509030922090501060b07030806061903020a03020c0616090501021b06090a0b030a0204050a0b160609060b0a0602030717030603210f0703081504020316030e0f070b040312020105 79
    0x1420502c00d100754002400000c031400c1c1c40d1941c0e4211003854000d0710544400046041c24550b00001050f08884101d0301d19242c22003013007500380d544204018071401d1540104101c0d170700d14002c0c1d054030010781255094800c64031300074415203034003c01d02c22110040380f044040403829503c0083d40c0300404ca050f030b06d14400d00545108011254101071400755101e0039104010401031080c2e405580120344050000d40c641f4242410091500c41036003200d4003000781800903850140101a4100590b600560005050340c003a0600c1c4010b03014800714150013403501c1000098969000009014142c0541c0c031941804d00580358202c114070041d00c172aa416481103868a07a502025590030341e0303001c6980e842c0b61900040c103035004c859401072035081d0045402d0008002a12019010080c1b01c4c20b4110380441c5545040628210b0f0111600c1001003050740c0c070280e15041d44010002e40c2d018500c6041103411440e9a144244600e50160000300c814083d0002040241e41c0140a11401009202081c020300c02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 145295134 1250 145293884 145293919
    0x60b1c0e0316020f060a11060601050702090103110d050d210501030c1e0f0e071709100213120501051602010b03071802120702032203020a030b090a080c06070305090309 74
    0xb0840c1d001a68410901111206a80da80c54000e0042140c1500c9039103075500340203d502d0600d4002090036060241c104003d00041ea6081010f0b815682e00059003410300141c880850404000414000c200c2d205100d800b8414540001440505200200000e410303d031942912100742c80003032000034855104c51406105070344150581d200d1030208140640c00082c0d55035120b0341c001d01e00b984101c0303000c1404024000c1e030a40c4881700905015244001c0f507024100014400d95400c01c00321040ca1440c1d001c201c03100b03050a26058600104800110400300e25041d00b00319009040640e21810380300725054001301010b0040c0610510208010081d0083e1440d050f002d041030601e401e40743c10055401c126103d00701554801d418024030480d8025620340001c44031100381d01d04030103000e1000d0720004200300f0042c0d403a5a54042135940c821f031194102c0d1100b003291884d1680d0300c1c500412014004c0b03101d2442c0240040c080b0701c40d41c3d080d0ba080c8016115180c0d12038a038864142c1c0b180d04406a0706080b802032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 145296384 1250 145295134 145295167
    0x9080d0f110301290403060b0906030a0c151209051e0607051e07060903020607030501081617160303030e0706110a06051b070b0103061a030a0b0a02040306060b1c0e03 73
    0x1300005403044081c1e42c8240c0e034034480e501542040351550754411100003070742401310045900a0302500100f08904440e2621401c40a5520499074010410b09a406180d4802c42c904042104031b03280c00d2180034800e26210342c0b83d00d000c4400080c0c0091907110030710840030008205001c3c145a0b16054030b02102200c0f90034404200c450070100c0003004104200000302140300c0e1981c107034000c0d80a0031090508100040a4031010f0340012904e9100c104c00f4803080d40324a0b01c40c41124541201114141201c080007820101c4145410383d010f00c03200c1001083c0741d05074000700007200f5110f080d5500c0b240c66403030030b6a002d0200070030201154172070110130001843796030190342c000101c8018403501d00410411820107900078081101c030524503030010401c00549020386007001d0744102c9440d00904001e0046540c50580b5000079000c04038980200c0c411051581c129005150001d1080c0045500d4500b0707482c0300c1d840001ca990f4207056050100c44244510b200d110710f4a030a5401071840d140c4280c0345d07911003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 145297634 1250 145296384 145296419
    0x4030206031303090e040807021018060806180c0d0605060301060f0c020d0803070309060506090408030f04140304120201020606010c020f040b03150709050a061b060c0302090409080d0f110301 84
    0x24480104d2011035044103003003a284c403d500c6189025aa00c410340705000304500100310f890203100070400c2040c6000201001213081d00c000e85000700103591440b00082082140051000803100d40758180141d20310fa03000117210440134401c090140c00d640b001403000d184001d120f180009410708034000340061188031502149400109111130804681e29034580e40d504c10384d540c0021a954a00000800500c3e016299101d0000c40e40d080e4a8034003925801040e110081040c89011103580014007080000300795020300d451071004072502d949d100e00820020580c5102d003a40035116000025442d50722a81c00c401c1800e030702800c400b25005040c814800604031400a00364180110501e0580e203c9029500510880c4103a491a1105141405008528859401c0802040207600040382c21511000c448a00c46034031030b030f0006807280c030340300708a00900603003080540c0542006945800c0c081290041e100d04409001c08000c1031904028040c11500f00c0c00072400d160030700b40010041005140c0d1141031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 145298884 1250 145297634 145297637
    0x501030e0f011a0103060807030203030703201507090803090f131103100f05060f03060d0c0503061801060f18050406110304060204061d01120c02071805090c03010204030206031303 79
    0x2941400301c10310782c02d5031a01401110100c00050007100c00c3d40c0c0c9030241070001c000b04030107002100c0c1150042500c9100e00000030f0180801840b80907182403d120b8281803480200c000d440224070461222b50556900351b64410020790750b030780e0200794031902108541801e900144140003100c0c0f004180f10002d0300c4a420b1021040c0c1d1008071321003041c0030f500254030030800d010403024182d04040143c030603401c2c0c41e00907501600c2c0a00036129004885403c40f500800f048a040c081c01c4d40302e241914816a10703070001078060250105000101c046030710f161000d05032400003407103440e48920360f2510b03404191190f580315070039101c916071a01c1001d501550304035005440c00705400c200a052151907602c1520102d03085580090200040d640c07100d08005c1464000d0100700315070107035200080607030041110341420507650701482440c2500810580c0c008045102e00600c541807080b003540300508007103503220744078090030344420b140d031506100311401d90b54024252803c1d600d55400c02081400c40510450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 145300134 1250 145298884 145298893
    0x5040b06013e0d09090f051e1317072a0501050c070e0106020f01140601211b03020702010206060d051c02010e01060b070201020d09030507170a0210090806070503100501030e 76
    0x142030110910145404400310b484908006281001810441d4006c41c0b803031920f2031030720040c404d05001000d44038034180c2d20910f40c01015210800110f407080001c280003000c0188007190705210718141d001a00401d806451400b0841d509481022400030350b0440180d80d4604500050140c0d6002c1d070060009100d000c1c040324a12034032285400b02040080c2c010001503409440000d030300324400d01546040140e964203407096803d01c1e4001a00c07617064504804042020b4421038440f00340360390b101e540034a4007007411011040c01000050001d510801c070503401806200002074079400d001407140d000c1540107006120700c24540140c0541c4444020b840e40841d5202c080c4941d007000b0034081d81c4040c040c407070381c160303a00e800700e100184c0785c40390810360b0900717108004070200003096011950740122070101088460007a841c800c01130801c4001a0000d40c13001c0d4501452408580c4030300b0342c60a80e0307540d004031400358658507001d40f8207000031580742d007842020380b034140050b511942158100d004002d085a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 145301384 1250 145300134 145300247
    0x1200705210705100c020d030b030114040803060a080307080901030c1803080406120b130b0109031e0b0603150601030b0f0d0b0601030b0109060c0807031b0605040b0601 74
    0x10303414040940e05500c1c2004089003074410301100b8090b01d641038510403420804521140c80194440d90203a4045040c5642c404c16502c181c0c40030b400c40314116003013030318000b07641c5080c3ca05210150401d45005008400d110b030041440d034400012928000c0d0080d90140c1024000740044001d0300001c0b100f50200521240b56080c211814000600618450312419443d03a041017001803102c815105007004203401d01b41140c444d51170b8840410b2000c0b000c15004903540b030311100181c1d001681ca9200a008070038901044134103070910041e4000076403284004104980350101099500d071100c4000c804140d41600100318550f002c0d6128000450000d00322752082c80f803c50005220f8211404103481004101d420002d070781da454030440326507504c24240300604a00b0109c00801d0303003031440701c020100d01c000101001494001c402d02d24a20302c85120152a000070762a208002c2c00b8180c400702c0380c1d0b04075034000c81c0080d17000d000c4041c4d5400861810400c00c0800c0c0804501149012840120011112044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 145302634 1250 145301384 145301413
    0x515030a08071a0610030c0203160c0e0906040c0b0315041a01030c0203130323010e0f0d03020708091309021f090902040311010507060b04020409060e060301200705 72
    0x200010a0040728180c1d1250458140441c002054074480584000d403403040110503070301c002101c500003000c3c0c500000c22904070f10b02a4554480c4400c417001045121000004002d41e0400f48400d440200d40380502d40d441c0c404c5030380c0c0e0b1010150342c01030000761a030f4014488803420b031029650004e1002e4400c0c0d21102100041011184100c80e800700300340002451410700d580500078884980d82c6071000b54608207a410074000c44400f41c0c00f008082c118000380c00940300f00420005422401c850000700442c211013021566251040d0074900410700544070a80c42c124003e00c2a90b94085c0c200682ca4070308591842000440307811700144880361a99982d865025071141c000fa142d440e098915050a0f001f0801405004003415030300c20018240104004c2c000600c0c00b5800c0400c1040c2824196251040d42c07400d5800b405140c0e40c1380e6080792000c9000a4413480b1600312004a42c0942066000354079074001341404d807040c842c0685010540b402004910940000003401c100340500c0554014100b004d20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 145303884 1250 145302634 145302643
    0x6030705100203040f090911032107020d0c060201151a0f030403120e010f060b190c0309030b101403030c060c09061c0f0b0d0308010b0d0608010510140d02090a051503 73
    0x160031007035561340381c00f082040c0c1030304a23018042c0c100c00808000c0300a11072080007448102d14540c1415000c20a4011034543d0300030040190f501c4201caa8403580c84020090080c400749528108038170800c4d000150040d80d40303c1c0b040080c001c18440314505019440014100e6002a2040702080910460b0034030720541c2c2e01c5454034410040e00040356424508030450143c03280c907006680d0102040103074902400031107500801414440c00c1207805c09107603046c25182d10382030380d0000e8480401d040401207107504c2c2a1032102500c280f0041c3c1e400310407288007810340d40d0103040728005041d40540f020a1503552040043c1c07400c0300d0001c00e031302d10f1b118004041702030040400002c80580c0d6101d08149820311854000c0a0440a0582d199201c207086910001c0101e5811302c1480007183c3c0005841010701820780040004e0140d1500070302c01c504003e429031103001c0300362080c07007540401e030140440103185c03e0444802c1d150300100000039640300c0201401c001c10000e040401126080c11801300151001d10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 145305134 1250 145303884 145303889
    0x160e06091806100906360e030307030501031b08030706050901060504020c0705041a0612090c0618030c15040605130509090a060501080303060a030809042705011406030705100203040f 80
    0x3403850032003918140c3d40307401740e406a42203244c02c00310011a241c07420081201c400355661030050300545c1d548864110f40000c003100d003204481e41c04008100700f1096056080f40713049a12a20301084608000c0c42550b00401881c0141c0e28690020040354000c038415030420341e00100700302c0001517101c0d950750004049070f12903858042541c00031721041201d0702d8144200c1d8030603149100c1551702e4803504800500148513001495034207680f00c5000c54001001040180c001c0d05000d05256954941d81030010091040200038034806e10031601c2c0400c140c1049035401803006107944102c1e003403500b03100054410f5003004e80e88051644078074500065590359942c142d40142d149402401c0c851009080410950343c050300030300c8080d4804c0040c000a500c0e640c500c481100e8206240944401c510000540030b008450064403804582d007211188183c009183c840c02d1358890070080144030010a164411007000300d40440d4582c2196108100d5030a015030720448603403080c030581703203815200c0b61354401c030142c1c1c0d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 145306384 1250 145305134 145305151
    0x7110111070914060f03030703181a07060c030911150f07060506090115020d0c030c02040615171b0a050d15150309020a090e0304090e0a0302160e06091806 68
    0x1850000d4143d000103000541282041e909a0a80504400032036928840c1800080c10404003080181c01d107614254034a0260203126840d04c480040226000e006410494080d07848500c1c0038079942255000c0e2103041d0310907600ca4404c5803280140420013498030580c00138013000c1c075401c11400b4101e41201c801080761621079040080c990511000b8031111040507040b1410b00500c0e501d102045d190001080a09110145800325800419242c01c42c2e00d070500b240002e4100c0c0c00e084000c5041160b000c1100307803c41083d500d101c000c0c2a540c0190511101c00e4511164500c0c01e911003101c0c08080d03800038003c0154504019245c0702c24514010f003100c03c2c41c084440c0c410324000c028004d80205610000c0c40c81e80520301400021010b0300010ba240f2801d200b80c2c1d080c40d6507401101d4080c0d006001343d07002030a103101c0402923078503411101078460000741000c40050169030070847c00c1c14204040750041c0c0300305d241d0340c25243c0da0b076505202c14a1006400c1001c0106144e8a02040318030070800346100d40000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 145307634 1250 145306384 145306391
    0xa0f080406180b040b0a210b01080c040e0c0901020a3302040e060d0201020c03012409020406120203040c090504110102060f09101806050403080f1b071101110709 71
    0x38050000c000c2d55a40e064a103444001500c20001039880c40705035800e03505030044040da101c401d2402900c1100400d440c440da49401c0300308003480c4801ca54009000c0d40000e881d0103000d40e1380d05054003001d1147d0300501000689980128000264190140007040010300407a100024a41c407142040c9001191803203414000101929054036424034001110603841000d504203400c10241d03680c0c0034002012540505840101102507a201f01300941b452040a0000c0151114007000718254078400440504201841c08001aa03079036244211005c4a21944c0d8410120201041c184040e5001070001e940c03040100c42d0104040c0c0051040500551140c41000c600901500003e0304240c4000e000010090384041001003400b404074600800e940408800a4809400000184c07900c40300c07080130740345c20700c2c0004010415402c044218003880a1811100460396050000704840c2d101d1180110b1006040c01500d001501c464918000385030141440585441c3d80d07240545070440f51340c48012001d0b00e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 145308884 1250 145307634 145307639
    0x21303080309070501020a1e0f08030108030a080907030b07050a05040308030c190207080606100207030501020d0902150921011b02010b01030b04051608250f030b010509210a0f0804 79
    0x403c0101e440200710a0014013158000c54948042c244101c51010f81181001c03403c010400a000307400580d01030b448000680c495031119030304c980d41d0704140804808035066070003061030300c40d0000d1010100d0764041c1a51049035101c0c1001c03911504500154418403000b4000880060040c401951088031501800c5895010b01301c012403e40d030b030f03280074081590824881808807103030100345194012420b5030403030391801100f04100e152108903840a4007030b501c003040751b40c4000025001801d43ca030085440031002c515041c1204401e1155810315070303100004c28826200c0d842c1051040b000740f100a00000307908042ca1100752359404601c00b5070340050359030b003101640944c0c0501c641d01c00030400795001c12191402e003058100359a043e9a810003800f4011000425030004520b850301c441d240308104d401c1a18664002900c1480e5200c10f1102280c1401111800f0754496400e440071480c008010900095952010402030048040300100790301031408500c0102d0103110001c1100d0384140c40c0d840d9150b1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 145310134 1250 145308884 145308901
    0x509010f03090b060111031605010b090702160608040c050d1505011d0f130203070b040e07030c200708030a050d0b01110a110d0b041b0506040501170a0213030803 71
    0x840c084810801e0610b0074014801151202c0030030341e4444c2e42820300d44c2d10550003860461450050140400d400e100c28281ea83c200308040d003145081d9501515031240030340341d00d6016070315004864034242c05900005010050244540c1c4d0043d0014089c0144980c400d0300c0700c0c0410560103045070162a40b04048408000a400b04e229242c0101800688003400544000c1d808040c0c0602609c01d0501ca6466004200c60040320303416a01240d034000e00b103c401702ea480b09050320a410074407840c903504c0444400684250300a020b508044210380c0ea450110240005400400e084034098124040c4030300348021030b982e1010801403500308210340310161100008113420081c1c0e580550380b03504000d0100071071580f058001400e0b070030841d4882d24007011602c404001c0342c3c0001c3d0303000018040038102d00c18003003031040f9820513000408007011045040b60300c4000303000345840781b4841c207800955481c0c008202605001d50030341e0085080ca40141c50410302418905000200390000da421010000901001c1e2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 145311384 1250 145310134 145310147
    0x31812052b0c08070204270308090303100314072303070f0e0628030803070e03011e0c050910020312090109080301030f020120060a1409060703021e0a050901 69
    0x1011107548009150310540001881d4101036600106000f5010400c04210b54907034100c45803040d001c1c0d0603488460740811006001340c0500005401080262002c5200c4000100440c2d220380280015420704520315581d409201d0f000b0014604a0300034880e0125080241007015004501212080904030081c082094148025944039400d440c401c2d007010000348142d415203540c40708044420348141c079004141c1210304903040b00d10f00c403901e0080b60003008214400c400340d8040d51095a030b54100202c0b5006240c00c0b03030800b04240c8074240241c41c0140c41c54141d900b0141c903145c1c280c580b1506161140b0007299071009400840f9025801c04103440c06c203045c049ca801c075408034481009002d45070441d1100445444180000391000303130400049019039024507000d007100341028845c042e07802e01c1c9018950700c4603015900215020704200340101084103000d0394a0041c003104001d400d40380c8a4501c1580203503ca400c41c0010008a00c0c101c01483c2d501030007a2004c0c1220740c40f280d6031040d2403c0010150b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 145312634 1250 145311384 145311433
    0x1050a05090f0f100e030f0304080d06081912030213120209070504152d080a110a1704020a030b070203031005090903090111010204170f010f0c0c03181205 68
    0x142d07401014080d801c2000007541d00d80d80405040c00040c1007117044410340c1544140198200d40080020a102c01c1289031001020140d40403001081119120312040e919041c02c081040260051a604d50001c9030440e07200c004c81144a003001441d0200d410b110070002c007120703032203070488c80500f40d0030a0035403d00708100c03980034005140886c941800c5c804048220300000402c5d4040040c10300b01910b807841c011510410f00c08102d446a905052000340041c50490200d404240341030600d403041403918842402d81c0d01c0148140ca99880c42c0040c002c4441d40000e000b44182e074000c410b5840000400c1008840070301426150740616500d280448107400c4031415903004a00074400c20042140c01303c0c000c01070f03a0000409180c08103500c010904014060f002d0750300300700c0401050003085214001c0c0003541741c0b0100c800d01d00078001042c407d0402c5080703601108049001c81c030341a40d8140000d11078405601200d804068001006490705034a4070041b052a2003180d45920031064510b00d0702d100c041c42e070f02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 145313884 1250 145312634 145312663
    0x7060c0201060521070f0b0318010b01091a0706050f091b0603010620010203090705090604141803120f0106081f261005071d0303041401030b0301050a0509 68
    0x20ba92800000c40c803042c0b40c02c0701c80c40181c07160703420713a012101e024001500180074808600e2080360b1a0208040c555006441180b004549080071b0300c14464180039403044198141c446d003c140d8038002c07142410840f24240070000c04020007501e00020007610982e4020f4a0703404c5c0c44c04691a103c41d01d0303403034030030306005408100d00160300c4e5050b542da48004030b83c1990361030315042c0d00d100202e6030b00318180c003140c4281d0f502650000c0108840c5440025425007101c0f07085841c1c080b5521064203000484a900304110b10400480000507d60072203840501002c170136420449144c15403031400c0e8440d40714280d8407140304142400040107075a900c8426590080c8040408545810303500310f0802e060f600340d02c126208841d4007620701103404038400c290725201c031900b0182d6162007101d203030501c01840e04a40034004594800a41c03102d01d2000002014100c0c00640210f113400d081c00c405507090f26a4100c0c442c10140c0750131000646844c2800f1780d901400c00d400d400300389800d08040642c10004109040d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 145315134 1250 145313884 145313891
    0x31e07170102031b0f160b06010201060b0c1903050d0906020706111603030e0f07030b0109050c04120609060f150602190c03170702030d02100c050a020607080c1e07060c0201 76
    0x308200b91320760140f902004091040d40d2041508a5881c050084015016100406004920500664058403882444241c0c000c228854449000c0002c0d0f00807903d40440e03982c41240c02d50b00c640b0740603d0b0182090700074106a0f05000d1981e43d12030a84603050800c8030100e030049030785004c01c1018058262031215a2140608102ca400c404410319000d0301405010503448802c1108000c4007400b0007142c0d07032115410355a2441c3caa04000307810794000c1c8200c4480600c0c0c08001aa1404000150b03030542d1880c040c00b40407103110307444002c0500030141c0c080d00d031296208000c04800c48540302d03003145000c0d080c01a000b0107240540103420508001c543e031810914150032040058070760407030075054a601c817049010a40d200c40b0031201c1e81c020204029058440c0030f080c40e19043d0006030342e4400380c0c0400c0b014480341a03040300485142c0981400580913a00a03000728003003070700078403d40c0e5200710301d040b086040c05019401d20b44900d9098400d042c000000240120505c080d5005a111031090341c002031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 145316384 1250 145315134 145315141
    0x160216080307240f02071a0405030406030c0201020d1a010e09010b09090a06030b0c0415020c0a0303030216050729030903030601110c0405070f02060f0c0414031e0717010203 76
    0x3240c9074030402d1070080000e00103441d240c00001d00e0b1100701981c0ea404000c1007024850b9072400000079800804152031002042805503c8213003002075461196070312401860034645010400d4016011044009040d55024400f80502c00400c2c07080030f05014003030070340305040b5840000240c01d45600204980c00b88014000510081101c40c00311906807005655481c000d68901380240d000f03000c540c0000f0100e10701082440610551a005001580c1109124091103103210707500303aa803084610403071a0004201c50b002c0000c2800b9501800c0d031821000608114410203544031820000160003000442445807138010f004022140d09001c04d60f501703804540340d410001c448551341d00006012904120280f404c2412032501405500707400030003d001400381e4100107101400280d0f00780d0203030005118500c000391050f004142640e0040907590a01443c140c14408000002039640d0038a81e0580301d982e00e0b01c0040354001c0c810764000424040500b60701350528241c02c64155011024041c50381c018401d2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 145317634 1250 145316384 145316399
    0x618150606080c090f0405010314060f0708060f042019030603050c15070602070c0608070804030c0209070e060309010608010606050c0709050411060a030c0824060306011403160216 79
    0x98010f91644002d41d04e4410050014a0403586643d8180d0814108800041008040441c850001e1310007001d4450982d50120b0070654a030040311268000f85514001c6002d50400100c1010969806000800c22004c0c0560750381c480070300c49130080d0241c80c0014904c1c00380401c003280e50518800c1442c080c8009441c503140c0365a1480705c02d4107244503440580f00c0812032400d4104030b802680e4040030a6441c0d00c05414048001d6540c1c0c8110004907485030001180e00e0b200e800002e01c55949512040301c0c1c0117480e024410001c100800c2141400101031101d2200d0f40c1d00c001861094881500101710075003483c0c101e0f4259225a03001c442481341c18002c40754450004501d8409980074840c000805039503070301300a900c96003062043c0e038000d0400940120125415007100103010000c1d150129103850f100f88a10030b41710031005411120250003105007480ca090001160006014500034442c1646024204860b500507107042c501d66207140140e010320b5405100000445816000c0300000f603280094 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 145318884 1250 145317634 145317647
    0x60603010605012d020c031f051b071106090303070b0103020a1409041202030f04121a0603070b0d0f020a020f1203012301120e0c01030f0c050405011107030618150606 73
    0x4000b50341d8544c240041c83d00901c00c2140034144500207046a51010100001c92110000326985580850512000805000f9081526001c031030707041d40910328284661b105c1c2c3c640001c03040305040c2c0c050010080c2d05100d0740d081000d4a4558020040d0880c44d5146104120403014258481030814070303c11400c001d2507803554105076000341c02642c0c1108060410303108038114072a012009403111000700d00442c120301d540303048181e006c1c801d402c4404600382141c1c03000104441100d8050b032641c0851414024001c4d0000a00440c1800e04408a402106012000240c1e084481c40c400141e10036196200f40c0c0d40304000910249084811440c03455040038181d0500d548480742520000c001c0710203c2e1401c2e40705400c4070030700700d0191404000205000d18442e4031803451068050009060224000184a040c40303000d540c401c603611032902c1c1924000044d41c038240151118410f81c00b45103c0040455058001c154180144d80c1d902d850b2a605450b00c071030380b685000000d50220b480c000382444032580024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 145320134 1250 145318884 145318937
    0xf070c030809010b09070309140c0a12110d0f0314090612070c0b07051c060806040b0709030503070602042105060126070e0108010b060304030203070615030f0506060301060501 77
    0x6840c00d01035a070b4500040c0903040401c0b102da00001280b0400000b29031561200d03a016100345814003100021140f09541c48081d5141160f200681420401c01243e40d03c1c0c01d00c005a2044201074851904d060019126000c1c6510070b549124400c1c0500781010382c8851482941000d20100301d00380364220010650031300803400700004400c04000490f0350580101c1070462141d40c4825203002030324000034000c01980207200071140c0d162002c0d0595615a60500640c010358110800a10007982c0e15145c00c4641080901110188406848003102040e4144014a951401018003681d514503144480840c210011824100c405001c2c1c900000034001049040c110755840420742d0100c6081b20200001300c03140303440284144a0700c080090f1a00c0c00d00c08482c12203202c00000c00404840f5400e025040c40100d5004006030010040b8000007103055000010242c10030b040340c5a40354503541e50000304000050151061750140b0704100040c07900b40543c00180202386400c801d6802d20700141503513400600c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 145321384 1250 145320134 145320137
    0x3070c08071713091803050d0b0f0a0306050118060509061509100c110301060b0d050a110406051305040c05090616020d0c080106060f0518010e03060109140f070c03 72
    0x340c0d4200b8401d4042da01c40301020000e040d265901c6000f4015185901d80d4460324802d0360412003019010040c1c1c2210b04000380d0141c0350245480400c1918030000d00c010078070a07500c20240300e039001c82034942c4140503014500c90320000805505100c805030b6900c2c0741e031801c95551820700320f0070f0042380c6407814140c3d041941a20a8030090f5403205022a00e402628109a0000c0c18602c4002c14203502490403000a80160321000140b4088010725003601c409010b051003908040280350390404862740000d5112135400740c0083c40c6414500e81c5880341d4003d52000c40094000b05100300c0f103040c500103840041504450820242c0050780b005003950140c1000184035210103e0340181103e42070741070300013980d4001c1c41c0e000054007600e0211503502c014020410958030700300010582038042c000c201e03c10211522401d0a01040c841440ca0701040324880c0d50400018000b54287ca841c1044042d01030500c3c450040350300c40120400588842004020f1100100c6141c1400710694000e50002ca01c103030507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 145322634 1250 145321384 145321387
    0x91305060d02040e010b0a080a0206070320030a17070f2f0d1106070203070201020703021003090b010b030a0b030c1008060316030809040e06040b0105100201151502060c03070c08 78
    0x11880060340180700300340060f400c9403c1001201541c04194001c91142130200c4140c182191950070803607459111900003904601d040040c003021a02900544540c11200c1d0700c810b018174004040141075412141103000070a03a4042000759040e04400401d51141c0149002d080c6d80c084131800504840301040d0350ae0000c5122009a960a141031710107414405440c0d00701c0350801c1910f140103110740d100a08404003405103402141809102000702c422040e0142c2c0188044c40c19502007100c00041404107806140d030326003215001406600d01c0328000c0191034805500c9103840b00604003030314007090035103100e5007007114184182c2d070700d5409214040400d0300d00301500b07941c2d0340042403510442c001914000b00d07100c83c00104205041c00148a40d840540342403001d100708140090b5170f00401e6500403d6008180018030039410030a01182080081e440041901d0b0f010840e0140c0c2c1c1e100507042202800c4400452201c103503010000070380c12484811016285189c0300700001c101c0b041110004185900 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 145323741 1107 145322634 145322641
    0x9050f15070c0507060f0c060912021e060a0507090b070605070e06040308030a110d060303080405061503190c0b040b1e03090c01030f110a1d0402091305 67
    0x5845030040c07108a0a04c1029110461b5503103912080101c44407034080440c0181c00380350b05090103824101c0842030034403002801c20750201c10100f24a08003250904000d14005001940f081c0e40c0d00e00080c89444540085950300042e50040d0502000403130100e05100b096030110340113030070a84607076030b601c9043c030107214541c0502d00c0064410320301803000925801c51500800661018000e106181c207601605190842e02c09401c01d82c000b40c090341c104800c006c02040050f400400c4600905801d20082c0300080d1b03500a0280c1000102618440032030400800c0d074159006484074003190794845803a648009425001101281901d4090070009100c0b03201c1001202d024003070b18800740c071641035558019400341103c0c4218101a41e80c81008000600189010340400702165554405d110f10818800070300c41807890030548218410003104c1c00a668600d01051001101d400225903641d = true := by decide +kernel

theorem cover : BRFrame.Cov 145143884 145323741 := by
  have h0 := BRFrame.cov_init 145143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 145143884 ≤ n) (h2 : n < 145323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
