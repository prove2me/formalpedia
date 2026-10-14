-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1282
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:09:08.962874+00:00
-- url     : https://prove2.me/submissions/33e3ef34-d721-4ba4-acd7-cc65ae3e7c93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 230395683 ≤ n < 230575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 230396933 1250 230395683 230395703
    0x140a270807051b0a0801090f0803100e0906041101180905071803110301140408090607060603050114040512042303030c1902090606040803090d02120304060314160f0f020109 76
    0x4620074a41510110000c4d5207203841c1c40d95030094103080381e1551002400741542c82082e200000c0030a4001c5611458096201d4400b545901c4000d440c00c20441d01201c0c0d07648503000340030500a034a20903e10502003481d0689950b18103031182c1d403110079179100d40c0c00110f4039000405c0c011802941185c07401a4400c040d47c2c21203503039041c003810640d90200c1d0203001e5460008905142480d41c0c100d01d101c1c40d04000c3c66850000e40c10188041a80300700d4096800d01c1e6030780c030003100141d0207000b9904049a805c0441d0a581814241141891008000302801a000b00300800440408a10200c004003001c00e402940748074820100342148117070180d411190060b5800318043c183d40c05161700d0000d00075207409600381c0e6140b050201c24440c90040c00c0b9140d105018110052030500c103020003983c406041019800c06032403640f843c540144c0c00c1480826143d0368110500303800050940d5102030b2905041048403481e80c1c0c09040d060307590300040c08011500c1660304d0340c00c0c000d400c101c500a5200c61000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 230398183 1250 230396933 230396953
    0x80c100e030123010905010e071101091a0f0c0c192604170109022d041503140c060403260304060b030c03150705070606090f140a27080705 61
    0x41290400d00300000f41c440300400210b4607900d90321403603040e600060541455600d6a580c143c80307600060010860541d26204c80d10f00140700160f40241081e40c0c0104045103007801107102d14810b9005001c1090078005010749030004400080504003040d1800c504c9600058034200301c00d0504e00c907098612424aa00d0500540415101c000c000300c4074a4030500c4a9204251b203600d0030380d41003500180d40480021441d00c05400754000740f002e484000003946c60451660303000305003921400c00c0c160b01c10192000c0204240244004c0b0402d0240f10b81002d8400e0022100014525006074080503012001001510380d4450070281c1c4c00d161010298178490302d07860030385096405040c601d41514003c3c01a030781070000b1402d00060b83e4926030035824401c2e00390350f0707401c0e4129401d03007008105643d10394840780001030808070381c400e04030071103406000412140800302c0030302d40c1e040f0060440c0040c079141c6883c04072030b140040e0411203448240701c5821420203450400c00490700131210003801071301500c81d440b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 230399433 1250 230398183 230398211
    0x50c040501050c120a0503070f0201060e0601110c0909010606030b0a1d040203071e050406050907020709180c080601030605070c050c0103110c0d0903030206060a241e03090c0e01080c100e0301 84
    0x182d4408e20039070f40c41e104c07036048045040382a0780e00c500c210010122101c0214903250302400f03400c20311080c401d0881c0c1d442c4902c076000814410007134503404030301d0359a280d0034001c2c1036050040b0844900c050710401d01c0c3d2450481d900d045844010b141e41d5004c5003000108045540601c044801003114481c159106c101210b03005a4040c103a2003803520440c0781c03920020311814448001442040c144d00501402403a040464000c1d00c05000c980d00c5010f100c2d8444030005411a00e03030405070129a00805603503040d85400803c03204064a18400d0180b14030f00c62000410020701200640000e18000c211b4010000404105000324140c2e841d0600039181c0b4203501c80d80c070407204005c59000303a00311840707611002c062003038900c0c241c090210b0f02e500080c990040d0304c0200d1600f0203120f807585030140110b850071848006c7c045180901c0400680c80c4c90703081080c40203000d240c6000c0c040c801c080c088076514201a0707039030f184144040700c1c0c01a82d0340102400d000c0c0c02a45401c1c200c000150090000400c80c0c2c0503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 230400683 1250 230399433 230399437
    0x21e0111040b0c060a090b06040507030e07090f05010b07080f070201090302090103050f1e150c190915052b24050108090312130606080709020a030f050c040501050c120a05 75
    0x16841083c8904c00000340d00c2d406038064140080c0c4c21061040164603503070305102c060007005005009140e22402c0240c1802e600b0080d410050226410000e0900407542c03100c800d507603041e40490350f14a801c0c802180454001c10841e01d130f032610028a60b541d05d040c1e1005030b079004800d500c06540141c0041c000401d000d00416404449041c0c03400740c4480c041060407440503809600d2518005500c01e0490048a05080d000d9980201d142c0b00f40c0d6080045007200500c40055062403c40001c3c0002c81c00c0081000000000302d001d800e90801c142130000e0340d6005d035904108844a54480d0400154441d684040d0350703c00c6a0200c881c201d14000121113040c3c0380003000c203070712030a0300240d19403001400301030004c820740380440e0909000340c80c9900e41da4410f0102d030b03a0b54902510b406503940030000e00e00c1c1041101a0046c01c0d41d04000d61502000d55015040b10302c50400c0c09030050900040103d0050b00104032000e4803401d00f8401d840f43d800650951404050340b24001c402c1b440001c8160143d604000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 230401933 1250 230400683 230400697
    0x1030c090b0907081311060d141005100324090b030c061e031801090b15030d02060703150f031a010503031608030a020705010c0e09070906021e0111040b 67
    0x14441c00261005008180700c088071a000022400000302e0ba1528010500703014503401829068800d0340031038001040c550005810b150301d640c0d41d00d06c043c0800c2400f030310f0b40d912500013840c1599443ca030401045410f020401848101542d039003924201c030b840a0140000d2403111724409112a4440d0201d40040c4820440c148c42803080740000802d515001d011141205102402100d0160005444291030f40018186c100800549001301084503024402c3c000194028039141687d0308205100fa4400c1045201c81d50003a0400b1001209481d00010f0762070f084003851800191024940144681c1c101858015003003014940a00006100440681d0322501c01c0c840341d00700a0380d9850f81015640d12490030403220b00d946070605140400c0f610009181d018040050140c0751201e10350322039017110304a15400010a00420b0380e48217500700100d0b0254030001a04051a540d420300388065907981c011110001042e0301e0301340020140001307420030f1881010b41c5901c0ca4847c4e1701c07241442c40c0c58110756 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 230403183 1250 230401933 230401949
    0x70314040b010f080a0503180a05060c030d1d0c0f010908030a03141e040809150409020703020c0913110303210727050d020f06031303020c0406030314070302070b0301030c 75
    0x1096138400481c00d40b50080d40311000314549a460182c081b0401003004200d0b9005070302c3c640010352502c61a00408035001003038007440c0e490400b00c4000d030440d01d0742c48404a0b9004141504075110b2000108080350203804c41c0c1c0d0064002c0345400413903040406801c05a42400003007a0086002e4058002014007001141611007a60303c40c0848124030003030511000c1c0c40c3c101c60b070204000c1001e081c002c001b248005000f24520510080d05100542c4c030560100e1501580020690b0505505102d14a22000101c82070740c60f608040c4900792050780400030240044006404440d40382e601081203d2001d40b00c80b070008480e40315111450880300d01100e000d000f06040070303500d40c030803c040d40300e040c1408080c039000e990180c01c01d070a0128101c80c019049070072510800c14480d440d03803107901940c492600f29141400001051038000c1c2801c035520403050041d07003409070501c0001c0e0044401c09504c170074880070a80725070300342c01c0807071038002160700605448000000200a01209042c48800d0710041d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 230404433 1250 230403183 230403209
    0x170307110d02010c030f0c1707050606180106030e0307050604060e1c0801060806030f010905010b010e03030c06060d03050403120207051002160515090603130605010509010815070314040b01 83
    0x1000e1007240c400c020070090009184000760343c00240600e1816940c410301e4580484807403000c0d81c3c1e01803031300604505105441c602003050b00401c00100002c3d50300403803d541c215001d000071401000017410600444c0203150701c0d41d90130b007840c83d000c1050f2540305802004490440c24207061078002002030b001003500e1409440c2c0191000800090004c0310100280c1e00d80440e40e00e840411035500d0f9010707054a42c540140c580400e80e911007406100751882c0108000504070f0705480000d030024580001e07843c000c0e0000e0000d8043c80c94007046c1554441c0c415150902604170524048505d442a60001005144040404400035500180d0101610001d43c2c2212010642400a0381e88880f852403c4025804000b02130105041103020903545901d0101c0d42801c041420703000620642007120a002002d15a5800f0002e10080380103040c014101a103d0102c9541803200040c1c5611814074101c200002100c08101054170903440240e401e0140000306103581040d140c200c0c0b05403403c1c89914409240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 230405683 1250 230404433 230404463
    0x110708030106270e060f0612010503191509031107030f03022a0d03030f1e0b060c0a0308100306050702030c060a05010605120919050d02060a0c08010509060a170307 72
    0x22200d404940150390282c1c1d0b0307411450544e9006080e01300500c41604003141e010220301d90b440e580c0c0a030000c1004044500c0d05507041806140c58043d102c8030441c140b51a101403280400c40f0606d03044140c1c070f004440450350040390304050300c20a0882d2001c0825101d5002c0000a00c0610400209800d00ca6800e48090b14208026048500d101041e5121840243d41d4402c900f481c0204400c111301f4840d04001c00d491128a205e401212040d10752843c0c90700f031071035400360086180c2c803a000449104603003150911114440050b958405c2c10350050900102c0c00100b0a10380001200c48000c550069050201740390406009484c0d410446020b0715510411700861504d40d070034000c4905a40840d034401c2d04040403107030000c1c6030324001fa11410003401201a0705101d040b440400030801400f0704010320154190400007441c007100204220344440c03401c04100702c500c5d4071800042c11070340c0449900440c5d44a150014818015540c8800b0222482c1040401c0585012003d004503a00800c035011034450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 230406933 1250 230405683 230405717
    0x910080a0c0804020f0909150a060e0a050c0301060f0905030d0f030513030f0c020d050105070908100218040c02010b090a0b0a052e0212070c03062f09010201110708030106 75
    0x28081d58001d40c4014051185c540c241014010300b1352088640c01115542e291403481d03d51000d0096a0780c2150075107030003092000c5141800c07180d40020b0b0000c0300b000705150074070300c1d92400c4c041070285104100350440d200000c188240c0c0081d000d48402400d840c5840410741010b0540303101b03500c0520105e0304240008080ac1da01e14a03a120460b015103481c0054140301c2d00c100c481020071401240c2c010743c02c01c484000710b4024801c40c0d102c1c0100d034641c440c0e190b04095600d4500081c880205120742c1c01040003181c428103d0425140d9a5001d6801154440b44036006a0140c1071182c1c1031a0070050107010005e011146410241b03035001c0c11384008840350f03100c40c18003d00440d04080c0b031403040c184031080d00d00c0c40c07140c40380c44000c88518416501e04103040c1c030131400541e0002e0fa01740e9014849a03803d0090001a214030040c1c00708148110300004100303004a5126580007041c040c40410210710751606034000c0d0000c0d0011800e00c030f10350381d5030800c0349480c2c80300c0d800a005440000380d003d5401030b11030f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 230408183 1250 230406933 230406947
    0x90f030c0d060f0915020903060619060c0611030f0105040606030b0303072a030809031e0d120f1d07050904170f12040303410c0910080a0c 61
    0x5a01421401d20384010351202806460401a4850101d5650b046000031401c120481e41d402c0b41c640300e025980d00050300405281401c003800051043c0000b0101c0300307424030403c0420040311040d09104001207094108540144180c46141c01601400402c0100d100c480600141c142c0f40c00710703010084c00d40c64107003c82c200c4640c404107075055807040086402040b6014ae500c950311a001600f03a4400341c1101064104600356441142c4140307000c178800c1c00c1443d09000c4681d60721000f0200340245080007142c16501c1e030f00c002c61032060100d000f0380101d40c19202d41084c1c071b6a04080070107110017449501110000c10241052100c03600070701001003030030f1a005d01c0441c011500805d40c0c022a01c9450103d00a60348204416205a8020401d900060084191491155000e81c400260b260038001c281c1203c6900400079100b0300980d512890041d0810345c0c409007103100c44000d580940d41c0c80303500780c1f2494412040708a070300a402c40b0b08022000d51040c20148114101c0801344a180d03246601580d01c3c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 230409433 1250 230408183 230408203
    0x3030b0a0b0c07092f07060608010c0f030b120601060c030323011a070f030c200603220c090516020714090702030d0614010f1d0103150e010605090f03 66
    0xc1d0400f1504019048003a004000c2604042d9140c0e05c811900403c101144c41c2d450701084ca80110110b00c5c5800d100c1c07984103410082c90382100070301405549001c020903010b1211989030601d80d0b540084200c03a02e4040c2e0700a46d04000034203d0f045540c54010281806942240403070000c2c1c10100841104070407500200580e02c002d404011a59007002000009178095200800540300c05100d440003003011100306880701406919980e40c981250304000c0c2034600c200807540c50050040c50394504a495580c01c490b400a414050f03d02d8000d00e140c1c0c4104060344030703203010b0309410481c540410100b080f42c6c0f045015400009445540142691060743c5586980c441e26030041c441c44485106400c20140580e440101481560310301842c141c0400d080368803d8100d0103d04a01611600e100d503017060380007a078030015090010081045880c00c406046020b030085e810551039041409180707103010394500141200c0c141c1d41601d582c40b0340780242140c2040000c0d40c0b085201103001812400c02160b14902 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 230410683 1250 230409433 230409457
    0x507030f1a0906012d0507030e0904020f091e010803030703060f08060721020a09140a050a030f0302010207170c1603020303071202030d0f060f0603020405180406110703030b0a0b 78
    0xd0342d43c8100045d40c4d801103000a0310324269220b141c501d0036003040e032075242c800c0d01540ca07111740760510390a0090112803000e500d640107142040c24840544d903181c0381e4844180d02207400030312580d80d10351801000345100680500c0d02003040c5c008900080c020003d1489003901d50750070080e2a540700318441c00c2d043d042c800e814403a000340010ac3d0605214541c5502c004032641142544a00640e1400c03040f030780400d02c1403001518125040c020809034012403480e940d000c4600405ea541001c0c00a42c0c060003d110081220001c2c5138240105030007034040c1d441031908818840404071150040c0320481d880554507a4031405003442e01c144501114080c0420f41e41c02600a42c10030495648400d04a01754044100c258402406841c12401aa0003001c070a10400c000100c5c1c52407a240c2c821501c842c6980182041c14014042480140c40300c42100060002b500e810508544960038500c000f40500d2846115840002605031706154158000780400c16059403400c000650b18000c1c40072500420200402c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 230411933 1250 230410683 230410699
    0xa0224030a05090102091f0f030b030d051b07060915090b030c030406090203190501060e0c070f11061809180613020f030f16060207050d0b13060507030f1a 68
    0x3240a00d40d01195020f80e0303000005160004881c00140e080d80071104401502610302d004100c61a0300c035540780f40500050a040c0050188a40061b445600c0c65000804104021840c0c410320f2240b0640b41d24000304041c25039842c142c4800300281540a90b014001030301304102c40d200c1c51a032103010403208503003944280908507241d40706102d0882e03101030000d80e180f6031102101405a42c0074001c00720b0380c165003121081521190728240e407e4640c01e901060059406608002000d01c000c0300700c4002c40c1e4040d0110315007680c02e2a249420208a0000c0b980041020402600041d0703104100641000101e401d1190380e07403201e040405900342a0151442c940201c40440c054000c401d00d007040c030a10045c4a5034200d00e030140440c1c81e00e00007034808042940004040c40e400b01011684401a00451001c0d1044031306100c003282403502c0340d58000302040f05032400501300d00c07500d040301c0d00c000780c1c400710038404c0d07083c183c2d8010042c00d191103549441616200710391011a148501c603180392900504140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 230413183 1250 230411933 230411941
    0x231e030a0b032b050d150e0610140703030203040c09061806080d0c02040c090b0705030a140a140306010309050d030504020108010f050d0b04030203190801150309030e09040804170a022403 82
    0x5130035800001440c0842910745105110b0746004500490180903092051860b03442c00301c0400074107980c01a0850140000b260000b100c5074120703400c84100303070f80504025a41e5140e902d0031001c04201c603440180082c1c0b0701700d80414455540340c2007000006a80100b4022031791919a0759885000f4840c640c0c003c41c141c0c0d010400103007003a8110203032480081c189410903079070b255244009a40705030022211a08000b900740c0a460700200504110112140207604160b15000042c00e03081c420020800451000700015080740c1c0b094214409955208003510042840070700050701910091300c040b404106c1c040008106030320701545c440200e031402070410420098a440307174200c10700040d00070b40c1180010000e909036411601c860494500d5255078030040e82d81340440300000c1204d01030700c0c02c0030035007040401404a03500c00b900c2038500c0400c035854882c94070b5034582080740c0e1113142d00c95a0240386100740e40c440200041074031000745000341c4070046c85d035442001c500e800314408068444400340510220b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 230414433 1250 230413183 230413187
    0x4170a020a061e090b040213060518040c17060403030b011b080702240301031103030a0905040e0c030f070614040608010e0a021e0301060f231e030a0b032b 68
    0x110b040b03000108502d40070f10811890426102c2441040d603c0b45038000c140300c11820581c2089032100f681800c100032060600c800034401114140002d00c0000082001c039042c40301411002c4024a0401441c804001002d00141c0d204c402c00c032000d0340409e02d401004000355009801914000da0b46030410103846403e0382c0da01c10160080002640c10558907105a11702c40300940e4140a1091446082500e96240d454014480200b65100500039001030003488080c03134000401e44180c4000f210081120700b080011207140c8650404102d0380343c42050480d07031007031a011807404103942c1c1036a20800551840c03411400306e88614400c00c1c2c002002c5c0701c010000a0203c080e8140c102018880242c60180c8026803c0354480711006850301a20300040104091904814400145a1241000686401014045007480748001c00207101c4600020300c20303454800800034042c060740b01080c4980c40b41001c5640700e004103044507a42c0d0091248000001048801000c6280c013030500280c0140d07030411034802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 230415683 1250 230414433 230414441
    0x20a0308240d060605130213030618020907050c0c0d02030604080901050708190806011d10030b030106030609050c09091b0d05010903030f15030b04021009030b0103030804170a020a06 80
    0xe180c0a141180601d84071941c0c56101d01c012840c020140032422074241810071085080d1a01c107100c2880c410041220144661212501160380001d80005d41d0514030108948208031000001c1d1711010342ea0420000680000180440091043c201d03441441040d040c464009a00507000e5807541c046c100040005e9000002448031103018900b05040070b15a1780d8070200364000e127980038900d08006441c1e0045603440300c03041e50300c540c00b40307000c0c08a150704075030000600a100608500030400c20128034400ca0094005c2410b9840c00b034001c00101ea41c81c1031440060082c82c0c0100c41500803c980b855041c0341900105008540b43d8001d0188000c1d130350501c00c24011400e2419400802c40c0300e40001145080c030804032200d0198501150380c2010341e1a1108980803030b40c0105545400d6901170021030604c1d003002780c0c0154191490302c44d4a41410042d00c254806501c010080300220707001000f0990f1140f07000b8000c921803024041044c1550301159000c2c028004241d00607440140f406002c00c1c41500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 230416933 1250 230415683 230415721
    0x503070204051b03092b050706050a230a20121e010b030a0e16031502040b0f180904030e090402041b05071a070c0201231206040c020a0308 61
    0x1078031604040c2008440e03c40c0c00031600150242c00c41400e154440c4401c41d0b0800308100322804401803005140800752081c05003550140040c2e40d100000340c405c0090754041427440403401d1000700e86050101c02e0090200c4e0440c1c0e00010942410f00075150307400b0b406007460f400c1c007440c2d0449062418000b4240070525008224004101c0000303220020080308144441c0a0724840400503901d01e8500e00309002c2d5280881703502c0340f50780410340b042e030110002e40c100c5060b40c3c1e0146405010303030258003205010b4050394000440300c07400000c50100207440c440007007201c43d000d1072642259410b40b001300300c29544110341c042d010138200384690041e071412090040c0d02030b10003003001802002d4001941d25015002007844003285000800405005100d103103c9030b0307a07400100d00303c07480c9040080180403100f58980281802002c2800d42c0000c0c2c40f100590706a40701c3c0c24801a1504940d40b0341090b40103040e5030190081c3e14010124545078808100070041c5a01510389880d1a21268061800c1c20140c40d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 230418183 1250 230416933 230416951
    0x110913060302060706050901050f0103150b01230304020102070906030209060607210e010908010603200d050102190908030309060106050a02070e0c0d06080d0c0f080c0102160605010909050307020405 87
    0xc001000594807107024140182c012900056189030085515084944c0a418012141000401040051900800b140f1500c0702d031b901c0030030309514a60040c0c038802c9511216070b02c1d5070302780c00c0483c1440080c2c40c0513510982c001d03802c5034441139840e440d18045500ca80000f0b5084044c0c800040c0c1c45041080003080503500c2041d0040c0481d184821002d812076a225290b400140c0350341252101f0769000c407d49001d0004240204090ba01c0c517030b01c10729142c582000c110500c5c0100c050560296461984d115501e642090084d551084403e29102c280d50382988580f01150315503001048840002060701d1207126140c0052069900b410f500b0703140c07034000404100440c403488201050011092600a00840318240001d071107112117046901661005d40010800394407400c4604021640900c0880003190003801d2103142c40010b0070722624a11811800c400c03d9030000660110f41c81820f6120191580181c0c41003060340d0300c82418005594070032101802950041c0412005442c151b802160406525 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 230419433 1250 230418183 230418191
    0x1050405060c010e0705040c200304270510030803041502130609151e110a0c080a031d0105071b080706110106060c08030106200102030901020418110913 67
    0x5038002030800c0d4001c0107001c075565150200c040896400f001098040d10f411a0213110b503402204d0000c00c2da105001514048111009807040905401d0080310042e040007203107901440e050f041e030082495045803101c00c0d11480d000000301d01174200441041520b5200c0070941c5103483d103441c1c0b03014100c0d500250000e403035401c110035002000384030b061800400042c1c0364001c0c2949002a1354001100355401401480030318a00c05201410444102c0f568842c2410001486a05901c1740d6150080c032510040035030018410100b070300f003000140c0c0c05419100795590750074500217031010b088800700c400005010440606c801c000080c8920321001c030084409a658003a1503a480300da07498560641d00600209a0b0b046a607900c1404c2070081c5c0014020741e04011981880030350b111451071105104010402082840a03074485904050750b02001c0c20b0500255281e003020071040b0300030741c0300c1c1c811100284540041c0540008213405003440b00341c0e1500300720b810b20041c00c4c14001c042111508200c0c0312961 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 230420683 1250 230419433 230419439
    0x1003060e0f1905060105040209031207050a020d11090a1e0c0e0307030c030311010b0a0b090301150303050912070503070302150f04060903020f06030603060c16020d06090b0f150609010504 82
    0x10801c440540c4001c0c06444100012142c100f241c10180180c11181c000c900400c070a040a03240024640403102c01800c9240e03480e101400e0a0b800c0c07498001e8000d5012191a81060600211b07403200250030f070044986414684403008400d08a03520108403d6250003008012810007841d0392027100d408403681008100c02f820400040d00b0286141c108544400c5086011b00c24183d201e204176103103042d080c00030000a600d950010b03903445414482c4490680300080d482d4a161420740207546802a0007104484650720303454050a00d03007242200f1802400382100721503441c5c0000641000310b0342e01501400d0100c1c00d5800348032410100c104862400d500c2040081a8009050024002440329683c1d25204900f0751040140c00300e8121445442071009200748000340c0d0380400c8140d00100020041e50382c0300382002280050380740701d43c2c0195100100303420100134003049400041c4030701e10075000b0042075910b006600340c0340c0600b07032240c5408030201640c040d40c0d81170407402440381b03e005040c19810165 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 230421933 1250 230420683 230420713
    0x51801020301151b0503030f060f100806010f091212170c04030210080601201903110c030703080307030906140411040608010209010516021311040e0705031003060e 72
    0x7000b80d02020041020b40034a480c40c942c404d80b4a6200d82c1598500003902c0c1e59500c2d0642e40c0d0201070704031001400c0080228515998032007541303d075580c000c0c0001d000790b191180050b00c091011103119002c50598040f46244511650a00c1c040d910700303001107051000b158030b0342901740514014031810302008078001c0c1040d03000000300c5440b4160240c1441c1e03030b0300d0443c17040c014800040c03200142800f024030103000c0c0d01d03a00859410140350f20a569a1400c900c1d68030701914102e180c081d000c84901c1e0781f01640c400d25a11121540b03c40000700111036480b0035402c1415a1041d0f640301c0580365034810700100d0415031198000403035060003507602081044d800050070407490b030103030340c110342103c0ca0586512050505008010040429800860810841400290040c440c000e10751004c0c50203a028142190303152a8a242d44910049007003202001000e5200442d51050041d048040e40190003d07807004d22030000ca85c4610a4645c0b001d0030f86d031450343c0310800b4002291030030b8407070301a01280f40c3c1610 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 230423183 1250 230421933 230421937
    0xc0609060e0d14031509040f17041e0312050c030d0c0e030615010807030906110d0203040c14100e2202190305010815060102190503091c0c060305180102 67
    0x881507009000d601080300e00242900c80c10012903000f00c0e40604c10007001e841030003000c0d1030b0f15101b5207040104c0e6555203021003a108000c8001441c040003800701104000e601030190054800d1034a940d0300c1d010b4454690b10f0f040103140300007040d5904841c51f141c0d2a905c2000940b042c411280104d07403c100070240d030b030819108803004001c0090725460b001c41840c5010081c190304003a4041d90120700c0d1050700c0000300b004500606400074541c940c1c1c0d0410411030154040840100310031001919030424003a80d0010358000d81c2c0650300005015070102c3c02c020303507001c1c412003a14014070364030103005581810b035008140742a1540c0c0c0020390f4a00b4410742014071030494038000318602c00503039513048641e80300342c04016114541c08251804c801400840300c00100c0a84080006c00e59546076590400100c1c07801e102e45003914408103c08121004110000001d0060844e0890b0f041180c8080c0302d800750709203103103104081d20030160040c0c200300490107503004942100070255a404801410303515070f4217a03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 230424433 1250 230423183 230423201
    0xd0f110f010c0e010507020f010810091d0d0504080a0f080c101b020f030301030f1103100c030b01031a0d0c1a04090605030c033409091208090d0c060906 67
    0x265102e0300c2d41c2044030351003e42e40b2040c60302420308130f0619103240c0200718040008000681480400710200b512080c0814040340240b0f01d0507422f1054680111182c451918401c041e10750b00d02c80d25241010b6070b070044040e9002e41382e284000701054001602d941d0108107020605036481801001004404c690a201802c100f40c8456004560520401008100443d01040100c02c64201c48140350403040c011040b82c1c1140c0d0002110300341c880c82810508800d0003400e044640c035105170080480c801170f80303800006502c0b07481d4a0401c0010440e1005500781c2d003800350b0303901c5151140b6180c01d2051910521a41d04240901001c0b00e24640310500a4540812203000c20b01a84000c80e0400c000651402244094681500580b0140035a840469036415080302d5020091480c0c49010020002d0444a9050000400c21a00d5041da64028103c000e00c10b005040e41c04440d003001c0d04084902448180b8001c044403402800c0702800785808031103e0003284821036105480c2c80000000c110240140420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 230425683 1250 230424433 230424463
    0xf0f08030f0105061305010302220e0106110303010f0b0c0a021018050406050603040f170f03070f0804020a0501030f0204050414010e0a0b0d02010c020102101104050103060501050403050d0f11 84
    0x290303007402800c070902500d059204a100e034008102d400300c00c00d6545030070011201d082c04c0250320307070316041c07040020982c4c41c0c035a0315040c0b212040c0c0000c04200030441203040319900d446c0c80343c90401c1800215100e11003400303241a55100c2400c10080d01088c0801842c44002450990b14a84000c3e4009401041d00301c45140025074618000c2c04101c0400d00e00e000101f40454080215519080104181c3c1c080240701070440d200d0f031440c450030b01020340450f920001e020300e043d950360600110f90405507082600c0500001e80a020881c05160003244803600907600100031803411484c000045001c0c1ca4050041c1d00840c1c0c09200000f0582c80d14041c4500810300080124030643c1450070131401034000a00b80340510381044040341c07107030722401e404231120f0f602841c2100f020655800140d15009120500d052810b107040008459222108060401c0c0c480980e01030107100d603a4001107907030303014501001d4180d0f003000032402c003043e01950202c24001154105185401142c0072502e09210100300304444d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 230426933 1250 230425683 230425687
    0x4172818061101110c07030209091f05250e040c02030d02070f060e060114090c091306060f0e0102030d020d090215090f0111100b030f0d02150108010603030203030f040f0f08 76
    0x140400082c0034480300410030b00700c2c0b5410401e17071548442ea9281c1500c0080d008807111008660054414803180351907071800180c4c0d040c01d00300e901c0c43c1401810100da12510000000a188081409001600d007100000365030704a0b80f0112901000f0081c82d8951400c003c1d407008100003280c10820780040e0850074002c040140006040d030a210040d9800181e1808541e00000010300020700d1381d00110041c260181ca20040307555400802284602c581004150f02440380e28500b22030800603040714040e1002641d8018408800300004d03a0b8185c85000d843d8051303003088c082041c4c80315469002e454080c04404e40800d001c601600841c4503072051020024520200061455107420300307001100b02030342d0078a0301500c0781140c2c4d9680b079214040a8500707141d8540752490005c0f5968208449049036a4a1003580c51445100d2406543d0b55002148248403d86541c000111910188550800c40b40c06401a605d19680d03249001101c103c010411544114002c103400c01042c000e40c0c2da480030b5031103054419 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 230428183 1250 230426933 230426957
    0x2011d03160513060e0c07050109020a0909120203090d020f04180b07030e03040b04060c05011e0204030b06180106080c04230301050a09110d0c030b0f0417281806 71
    0x2004000c0c803550b00c05404c00c031342003050400b110388580c0d1000e104200b0b65140d00c070720701c0d04a0142c018914080d5109041090100d1086940d601c10203440f0702c01d44500e001f06a031442c050740c90780980d2503003540c0824075807000d001608001d902180030310b0b4020300020300c100070107582000c1081424015a41060701300708101c0c205826128082014000d08025418245412040802d40c42a40a55400c01001c03a42010821109400c0742001c80301500c84607104d082e010b81a01e009401030710040c0c900d03034000000309840d41803200194000d4030090f034885d00300340c2c00c0c010240c5140c0c40141000c0c0803600700b04000a800145688020301c28841d541c1c2d074524410300c420415003582c0e00a040c0d207070721a1070300e40010f00080040d807101f115518190361880000503107040400c800e40c0158406001a412034080201501c100d104191245211f101031002d182d107a40300c020b100d805641510071040002c4004024107004411150141c0001c80c5841c000007a1003440d154600c030207070f034409030118441c01408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 230429433 1250 230428183 230428189
    0x80402090907080a0311031b0c0310020304020a15021207080409110903070618090e01020309060c040e0109020d021b0c1c150905010912080601030f0606050702011d031605 75
    0x41074110500ca00284a41824002c16940341c500c003c50090902440b502040c240344024000d5030b0319003104443c1c240c80b00c2d01018845843d1123600d41200d01c40c3c0105685000b1424040c42070320b0103140c002d041c1400c000c2c03c20788007429045401c00341c281503100d4540c0000c0403140150080598511070720096458038501490001030301e81501c0c0c00c003661402406a6102e0361000511501144c20614003010000c81254240c8810029508440d50791401c040c51143e00c1c1905400031070007804071404880322aa00d181403020103000754040d082c040d9a0034401000f900729a50090040c520303018400600e0201d400e007468840b440e44420b40142034020302242c3e00b1515250a42c00541c0034200203410401c0b04c16a600c040270301e50380100c4140c0b40d43e02c105640074480b0035400700454503400b003210300505c180c111004d01000400c44042d0300080c1031000b0281d00c6c9000b4000d400484980791a0507050031680d600540e02c03084801041c0e0b464200007040c6605a0383e00300041189280030518880b0b4450404041c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 230430683 1250 230429433 230429449
    0x30614070309050a0b06012102070c1e06300b03120906120423061006030c0c1112120c0c04020903060f0a06090c0807020c010207350a03080402 63
    0x500345407401d034200c0b0100f070000c520780012a6000c1c0c0000015660040141d03058040311b0000c0311803403860345580ca02100705d41d000b00f8049019041807006140d0301e07030328004440f000e03025118441003a5202040785900854516004a90b4400105000703090143c01c845040c0300d00d070300810030030785440145080d42000d104151103400d01e11380311131801c86450082407642c820220102d10169041002505015042008001d000742c80301d0100e41031803070182e106070340325025a0010b41e4004441c4000030002c0c0a4403c0c419902555221401b20407101d4036080c1a1468102185801002c0841d45403e420001d21000d8070304a46140e2064680c400384218500d000205074038280114410003404c402d90394001a05540b18400780d02e03025980e5115660078002c0c003410f9100981c80e07400c00c5c10f9200c816420091140c4500019800c540c4440500801242e60344401e02c620880d0031610035081c04040d40c0805015880b41d41c44130b1000051102c00045031400c8440f07502030340040e00180034801107190080e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 230431933 1250 230430683 230430691
    0x1204032007060e0d030c0b09011d0c0904060f0207020a06020d0e010306030c0909080d0e0d08060d0b0705030c040e012c07020616030e0609070e09030c031c110301030614 74
    0x307159503400d060000d00842c0c5810382151041284e01030241c10540b00d65042050a544062900300e1070034800b040700e02070000405a0303884c1082044107290070781d200048040200f60300070800862510746072501c50041c42c00442d0fa980e000d408210303003005078551031400c2004000c1c583c000e12446441e120024828501210094100740c1400020004a440040c40c541520381c154000640340e4060f2804010074031400c299a641e04e803e00c010040014400b1440d01101d40050b210321840e9a1850100700d0408035000c030090040c0001e60100c0c010b644600040e691019410281030314268030303120383d06002d0600340e0014440300a29001400700010402d0200f28181090910184d541460f2501a4075078030000d000044400011000c204082c0c4079801000801c010642565620700b040030300c0c0c1c7d07102d032407034010400032600a10218203102400002c484440002c03801460820b1800c00c00350b03891011400e901c00800d0385070b03c03040c5641c42419008500070741c443c1e900003c20700c841c1c100350340441c071000b4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 230433183 1250 230431933 230431997
    0x2091f090b0d11012604021003050708040f030504091d0d0306060f0c03051b01020a031104050a050111010603050f060901060501021204050d0f14160807030c0b0f120403 74
    0x4841620242c581207500c1c02c045500515070320540b124480100d0b031517203515410400a048074108000300d22a0b0100341d40c0118001e54140301d40c00841e46045d0240c0b4002c0d036003840094403440000e03000c40c90300b58400030164400d1408516265644409070140c0f034a074010300c10130a000d60000401281c0070001c4441451203404d081c040c0ca8a801c002900050b00c80701044e05102c21081c808003098860000c407000c1c01d208a443c2e44500303100d0078501c0d000303411402c40240841d2410110742e001d22422410364040b1000140382c81c0d8482c0c102801100c000d541401000d01c15920743d203000c000038500780021076000d820440200302c246404d80c0c0d01800d40752140d203c103056400c45d00c1c1000642001c0c1c03080301c0988000341c0740210480c00c5031501c1c10a11214510182c506101918051060040070600100310b070a07038040402c41d151902020350b11210207100041400706080420884070044101420011053b00401070803d04800c40c1c41d410130320100c0b4110300041d06c04551118012280301d0710340c4410080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 230434433 1250 230433183 230433191
    0x4150e061024020307120908030f041e080304090b01110604050c0a0608160804020d20041a060403060c1b03020c04050903160602092409150a08040602090d02091f09 72
    0x1c45006520317445000c0000d002022050000c0c810f042c0221403440040600710122942c620140c1184806c0360028051a1004484580504001c500c0070408005aa0320b40d0007840c80c013850082c80800502443c1c01950500c4143ca00d54034510f84144800c030f10585c0144094640102c040c82013090400300c40d0040c0050100e104144086050f2520300002150500e00b8014100d07121800000c0220f0301c003080081c001c0d00c0c1c0740d01f0310322410740740c031000d000c1884207031000d01140750b08115410a4403210b90541346c01c16420f10080000c03c1c1c0c203800c41c03448030700c0034100b5040800041c21100c0320800c02c00000d4015a10198100000d41418802c035584044058060340c107089006480c484400490500600780700d0300850342145c1584d0310141d804c2c0041440c4008041d04400101903a1035030003003150b05202e0580c0760a00300050620300d04903107d002c82552600010741d82c0d66140002904204125a0000c00015000c001a158a40d44a009461f0241c580d00200c80303d114004a400b042c0d0031a401150070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 230435683 1250 230434433 230434499
    0x91006140a05091905060a09140612060d0f020310020301031505060d0f03120204060c060c02060702070303080a020904050a1437020c03030103030c0302010e0102030c0304150e0610 79
    0x4444180c034200d0004407503c081c501d14034441070b03081d6078040e008154040c1b000070b2058185600442c40c0307022540c7c641021203504003080700700310070740c004c608204c4803204580300011402c0c5442c8040d03850790303031081206502d6180d10782c012030b2070603003440780325070003240e0000062003400a2100340205105c0d076005c060000745004004940007044034076004091f070600398004801c06000c0c0a10001034ac12000c81113458503035884c802060351180d04008d407181468640c071070091b1840400c84d20300c20324882d0000c04e039040c42e540c0c040b41c0c040700040c15244000e90900c441030403a0744500669000324a07401c0701060b458407071403400c14448070180c96042c03031010f24401c03181e400d0403d0000050300903444921034510076121542034082d101350382c0d5500c00c82c04004000310415801c01500688075001e68020080c00c00550214bd01701d210907139020500080510009001070811040c00105924443d4041460000c50f20945c6c80c021068070006030748019401e00b4042d04010791200010161000d412550141c0313 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 230436933 1250 230435683 230435687
    0x15120b0d0f0b06040902130b010909110a180905040c06080604090209010504020f1614100b0609040915050f1e0f0402090624250309091a091006140a 65
    0x41e91040102002c480d00c001500070360303c50b4417107820a5000ba05080d00d41e82d2640511004040c2d41d200240464020403002c00c115681340300c1c1321043c0060003c66464400650001c1da15841e1880064040c032200800106040e409401014000e41c820307100752103507505004010300500e00041030079019900d00b04641d405070350b40600c610304503842075600507515040740d100300e800341c450250350b880010111000c50701042038882c000321030f0000b00d1003510604110308132000e05440b800078034154441014003001c5041d145c981c0c00480c0092095140c081c0449002040a040d20b000300d400402c2f400c401410007580c940b0000c40c414034809403c84100e00381c035141c08514224100500041d004601260000d8000e481d0b0010944c514a40c000000200300300c1c9045414040e03014020010134861240c00c2d40d01c1d003505400b04401c0341d035410303298080680d09000d04440185400404540c29441d40048031540382c460301000c6c0c0c000c0840d1142144061708181c07000d850005e235615828a660780811031022426 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 230438183 1250 230436933 230436953
    0x30f12091f120b0f030303090c01030507050a08010b030c0403120807030b0607050703060b0406120b0601020c0d02030d030905160f050f220903090504020d0c0206090708070b0c030415120b0d 83
    0x840300c00b00080e040341040c002c651600050180301c0d426110020901c484904005801c0c074500400741e0f03007800b02c1c1d501c801007100c2034054007044e80c1c003182c1ea03030700148812480640503503031080e0203121803030402d5502d4942404100d00c684d6560046002182442013083d454055034280200c10760f4084c1c0f83c10460303a101d80d42c0345828800580229a0390a40c0138455803541c2003400141141c595083c48412282420280d03001c00b84c0c2d4084c054411540b80082c03c3c1020035072455a0340d0010040d00b00713400300a0040c0c02421550100315a240600300013042d0b40b610388502c050180c000080c502c0d0b003241c2024240407038500101d842610a40ea1000350454080c1d442446001f030004414011440703030b00c41c0c603003901c0c004800e4000d660300c00e0001c9403201420826500c0b415860038540c3c210394694903610728031a210035140c02001c00304d8028482c18054905000f0052104103081340403070340b8250782c80b8042c1d1400042101058001540c10000c111001540c0c080e0310189030081396204c81d9528a0746ea81c1d4001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 230439433 1250 230438183 230438207
    0x201080606210a090b010f060e0405010303050f13050418051608030702060a090308120610031e0c0e120f0f010501050307060e010302090d050708070e04050c010e030f12091f 76
    0xa55042c10003c1c0800b015078100140c51603000c640d1640c9940c4646200c2c10709940f5001c1c0d1000511069444030091400d400f41174100d94240d2a4540b4140790304101c401c444d48410964012022142e05c000f405407103a204a902c2e05000c40d41d0301c1d00151031460100c0c20030483c44150a505082d180b820711085401000b118060740d070498005070383e0b5200315400e85e00801c180d800541084008903214050200c07800b000c5104410844010310310094102003901103a074000300310300b01d0040460b0070100144a82e48071055244a070309200b18258907400c0010b1205140720090501d40c0c01459940d070043c0001c005a00d6075540c140c0080c406c9e0360404001c6582d809003403251200f0007405c65004c141d035900990441e485040050b06d19800c8444c00d08240f560b4148506c07820456104100d0001155210710240034003907640300014244c03a2046c0401150404c810603d11607160140c0d9060464060f02081400202502102840e840e144840100000150510360034010001301e40f04844499500c0000070b404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 230440683 1250 230439433 230439487
    0x2120c0307020a0b090102030115020a1a0c070b130309080d0f120f2c0d0c08030606090603040312050c1216050904240f0e0f131505040201080606 64
    0x160381d2404800ca261803000103001d060103620509001407540c043d00110705940d00c2c100c10030740191001e10203d90380c0640042c082c00c458821010009000c1c121030000e84c00103186103c1508200f072503202d01403e50402c0c0c4040300c507070301301c110000105604200a07100a03c0c111015000c17030141a5400742101a9000c0108100100c00c02c0400070001e5a030b0188168842d400f000b0855803020410590500c1d000c0d000598440c029542c00b45240b0300d000903c080203809903503840f2002400f41e901d403c62608083d11084d031101c414051860f980d02c808000e944164000e40d50035220f254841c40c440101e407070142c520100100b080204c02e1910b110007125035080341c0400310010b0100c200d40001c480c01d0082d00c0d102a44a414480c0860701b100c186081ca0403e21400c164003000b4070703a501c124a81c1c4e80c010340f24614030740101100003003010192002d040d511183c108081c1c0b004036250340c0c42c00720aa06400d0100201c61781d40040c0019075a101000c0c50384008180c2e80d00e45040d20000c00010103030801701d03600307134 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 230441933 1250 230440683 230440687
    0x304060e0118030507020108010806070504030f0204060b1215031b0111010e06010612050c03070c0803090c1302041d040201080a0e0c030601090c020f1f020313120201020309010f02120c 81
    0x88842400d5020b03804110079000302c0e202c0b100d5035180041c0603a000c2d0400741c0c0000c0449001007440360010405038040d0110780c48175840c1a01e0741c0e480c80c0750480d145005907801a0f1301e8200051010240700100031950001000c03003114a010031801e9002c04407074a03114003030b0344540c46800246855004080307c040003424020010501300b11410702425042c1802d1207180241000010050380003008501407000800d000e00255072150074141703070b80c041101c1041c0003410a951010118032000d0045400500600030b6810b44109000495098544049520500c690000c9d0070001500654041c84400f0707081d002c1c6115604198000a01200c00070b816004025070751070b042c25080c40d0812403031300480005002c0c2c1d4010740e9580d200c000240311040040d03015025000c084000c0e03420100d02e03046c030041c8420000304121503441c0040000d40008240d14114a040b034a11004150441c2400d01400300950003d46e136490034600c03039070035074066120038111503006010000c483c0305088051503100c2d08200440b5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 230443183 1250 230441933 230441951
    0x42d030b0c160c08011a04050c09220203040809040b01020309130c0c1e0b06101202130302060d05010323120c03090901061d0603070e1e1503040606140303030406 71
    0x2000c0c2c020b1048004005602110300051180d406411541480e4002400201c1e941d41c0602404280d50048803c403010400c204445d80c620729103544031000380c0810b50b901d140b040303909805404c101c0c0e0082d01c00b07a82d29000481c200b0391928160003070244105082c805541089010000b2a0124010007518a2065100c6139103140d118492250703074243c01c1d0405000340d541c0c002d0000c1140600d000e2a4241c43e032044150000307805e17040c160201040c400e02e036a01ca40d011000310b08680001d403c50303200c020740e40a07600400005a901e04019010700441d07100c00103010752441c5481000000c1c0c0040c95402c0740001080c0e1107000c04040f41081200b8800070a40e80d4410040f204039095200e00c0f0701459014050340300100f0410ba03c0130190740000d5104002d000b83d504500d040012500007110030b000018091074100005051030000903901c01c2c2040d00c55900c1d22000e10014805480001242445d44004020002485032a001e400018030b00c6481d040031110f140c4000c139072030788001071002d040c41e5101d000300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 230444433 1250 230443183 230443207
    0x80c03060a14060f1c06090b0105041103040809030a0f061a0f01020d0503090a020a120312090c05270c090a09090c0302010507080f0f0414040501150c06060308042d030b0c 75
    0x202c01008950b95442003a052038550007e0104050590303509403114004280c0741401e114911802c0008039010f41556215503440c843c03540004802c0340c142c05440c000100141000c100070380c41520415002c68810000d0700c0b0203214400c41c0344110303c2002203a030034107101d0b40c000c1148002000e040c50a40c0d40c0796926130700a840e00c0700b41d0000039001540d2010000e10700c0c080710b40ca40d241a2095035034103011401c980700c6109076403e481c0c018154442d1000200040e2a000515026040c00c512115208481c170100262503d40c080b100884035640007d502d03811454155907100207080b400108010505807501c40501114081c003000703043c460001010014000c4903002c1c2c0e0503025445128659410074a04828203a402c03600c80e50b1011403400341c20104910300b500800341aa03400c00030b01210b0030080107080341da03a41002d4080d2400b941e1104007202240210740203202800e0f0381881c0501c68604100c1c0741d0440081d0729030350540304d0401c481c2880043c0d50034650982042c01000c5458542c0080050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 230445683 1250 230444433 230444449
    0x3190204051003140a021c0c030b1e031e0a03110a0503040311040f1a0f010512130506070f09050103050a06080604062a0903080703020102070507080c03060a14060f 72
    0x40036a000d065020303184400740c0c1c1a08a180c0404407a000d60700c181d200c1882c5d103406d9004001001c0508210455a004215250b900a108c00c040c07601e008500482c181012400b10b2850400d188000404220b142e5a00e0030101312000454102211440d49030081004964a85004200c000c08008450070101c0800004202c008000c907002000d4940d1196681340014104c00c41242a80c002d03828281a4000703078440e40700700000400b800442c080c2c049110740030400c84002100c0e03c0c505120b0140010303084202c0802c2228414800c8489941038214a070034001e15143c001070100c02013064140c1035085681d400001d200403101c1c2800c012540380c03503010702c80d005060140c0040700302d072040f079042006000c004d8010050b4124030b02c00b1142c13080006290300b110028003690060100e01e40c007400b0000201d200c2d000f0044503011b031000500309102944c8050510126501510180c0c1c050a0000002d00c0d052042a40003d2441030400c01215030b4140b41903000001401c99201d1110102500c40310340303c81903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 230446933 1250 230445683 230445689
    0x705060f0403090e010803130e070c0b0702070f14040e03030403170705120405030d150b0a0815060301030308090f06060d080306010909110a120203060a05120115060c030807090b03190204 82
    0x3031000344d0b0b60319036440642d29082103001a080300d07031803400000c003280302d0050a8040d48103039669200c2035401c0c4d2100700c43d44201070400000c620855200061300d0891100c400003400e04013000390107401d4180e0400050322001c0f16401c4881d0010000d10000a400004050381d45605200c45082c0d5580c001c800d9826006000c041c0000d0058542000b040140c0840201000c1403501d5080103020800034480c11307003d1041c0102025400c0c10402c04034054010140c00e64450b16516907018001514008500300b500203034011808521311078140b00c9902c0301404065402904030000300050300d000400212002c820406c00790500c4400002304040e82d12403080103001d002e00c06070500110900100b41c401c42d40c400140031002807602c5100c0440d000e4240206c03401190002c007904d55130340c240030812482e140d28040d40d1059640c1d420400d0100c0f450540710b0b00042c40d80d501c52201d1442d1604028001c40402032584041101920782440f003036074160240d9800902e030548a25403841e85020140003445150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 230448183 1250 230446933 230446949
    0x30f080c1501080609060c03071206090606020309010813080301030b07050912240c09060f070c0b04030b01270b010201021b03040302030706090b07030e01030612031d060705060f040309 81
    0x260404000074000c03003812560084102c82c5a81c0d1055038054840030150b803648403001003000440e1011380300383c0d155920b10383d4648001800d507130340700c040707078201c0300560b21803805600b010640584940e080341d00d080c0d1110420030502010a0181e4407525141b005000041c0701c84052030120300c095208105070b4000b0003000d0810301c18101c5003001550b50f05020518091008400b04017082d14020f080341e2a4040c0c40602003240c1043c0351401008007a4000401ca000d4003d01401000040b41201d01604024425046016642c600758201900d403d003058110b0381000c103040411312095910515960813000000030001050102701c030040f03019214840d60031070b19034002c10060f01d1101012000304100ca01c21005c9550859903440709507011000c5105105507082c003800750a0200e8003803584038a0813241458001145a241d401034100360075110070941c0000c000e8602e01c81030750402035841704040000c55602d03007090900c0e61150f40e41d903001064402041618404281014040c1c1d02c09005800e0395 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 230449433 1250 230448183 230448193
    0x8040306050a063605090a0209040b060108060f060307180b1309050f070c112209050d020102031003110301140f07080a0606050409020a0e03190309080304050109030f080c 75
    0x300c910000a04528056050190707404c400100d14001000405800071152403c40c01012203007102c044001c0c800106400040c0c003448124000590b100c000d403910851040b6002211820300c540010400d880013020a401040b081d00309a00d41d075209400d49501c28864a01034407100d01290a080c001c006c1c0e60f0010b03d0030030000c6401d1400100c0880004261402075404000380ea84544010302c551605881d0030300420114010040860010107140c0700325440a0021514189074401c3c0784840d241014480101c4c9694010074170030400c00740485102c0944500c001d43c2142001c40c0d2407090072809200c024400202c1c81700030111502d0a40044001030030148100c00246408000f0f80c007010012116600091314a90014040c00c2d1603108040c292181c6039542402c081c1040007410003984515000414000100403034a0381e0366003000300000b2000349080c0c03000c188501d460041c240c260140c01842c4113800600061240380d9000c0c3c00002105e4100e10071003420b0360a42000d000e2031282d1041c0e12468001c0e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 230450683 1250 230449433 230449441
    0x20040c09051804020f010807020f0601032a0b031302040e010c0806010908030a081909050d09060f030b10032007082502010e04020a09050612010e010f06020a020103090804030605 78
    0x10303003011580c040d182440740401d6002ca0080005084600035480139003d43d41e6005944215840e651003091030048443c41803507a0402840c1060136401119030041e80b96a41c08040c001c20b5081d888403901c00f004000040c2400c40c80502e078080180f070700210030341c034154030b8081d5a12900702c12400d801c42c000800030410f8080e401001510201c41d110b0120f80c0100d00000c180c48000b048645c070f0300003681d03121b2194481508122010f213024480e0a0003640390394107440892018130221071072010701d03110000c01c0f61410b20094000001103403203000b07161510310380d900c0326180e582c44500d100015250024510b041e06555400f44404041d01540310000420000100712420b4024074440700c5d284d1000808040e6510074400101d00d100009000031040035400409040c1600a0a011609400d091088903203c20100d41d0540101e01d45880c80c015200c01080303194071a5241d0f81c050035100c104001348d40d0a00c60f020390f0341d4030344040080c105591043c1a105000004041d1009560300100600843c20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 230451933 1250 230450683 230450687
    0x40902040504060609150f12020d0c080c07020f06070f0c0e071803050a1b080d0509092d09030d0203090c030f071a0c071a1b0c0d20040c 60
    0x140507240c0118079158011808500030b003411001c407104180100140c040707000d0201d0760f6412000c4075005021440554410030a440d0010348420386c014000011405818080101560005412a6a1801c0030041c410142e102c1c200e03035040c141030540d000b035520360780742c50300c0844080741d10b8018040c06480c42c00400c24100d02c4414500840c05036035100b041c0c145100c503c80d540180d07403000800d0b5602c102d1102002a0200c90114188840200c004000715aa2101c803818060b55603001e0b00041c0000034a03424514104010a41251034004469500401d41403000c6845a452114907406090310340052404a820000c541312140700d8071080d03440b0300385100c40c0c0e0383d16145150214401d0207584640208080006101d004a801c8856400d404007400001c407140c9512044400800d4015103101207081c02e1402100c00884c424203074800d5841003201c0d41600c085100b184055913039006603000354160761700d0b0345034401071725080546080c1010280102c5062444210103242c1c025041c0720b01000169 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 230453183 1250 230451933 230451937
    0x90a0e091e030904240b3f090d1b260408121c140109020c010609051f0b0408030f03130b0108100c0804120c03090306020708030402010e0909070302150d02040902 71
    0x841c1016201070580d240c0070100514003500e085c0320300b140c0322034801d0201c040c01c00300040300500b1920b031070640451813042c42002a0b1070443d08034009274404c5c481e03011002e62048080e41e891100500d228410340e0035950320700c40c410019580d00d0740c1c10204510015113172900400c035001000707c04215282c0018880e20348209411030b10031594281d070780159440f03801546010300050b41c90030b01014015a801d0070590b600941080036070f200715650301c81c00070071048154410b01e0300594115501c10740c1b07041051020400512175801c50f04080c50306200401c140074000040e202c411401003405a10381e41ca0800014000c0d00f000b00c090080f00400c4000a1541070215480c03440c4100513900f88241c018102c401e0318001020b60b0006d08120078a02c00a0800c2c0c0305503455000d1901c039290000e10340d9542d413a244e003030f60054642030311044e1000043c44210340c0c0000b0141c016800a50311401d040c81c00c0354505c2d44a40c0b441c80301a0140213180c01042440d44d042c001c4840411030030b1004c5498a84031013182e0025 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 230454433 1250 230453183 230453231
    0xf0604080327121f02070c082104081b040b06030a0f06140d020622060203090a05010c0308060904080c010f1d162702040308090a0e091e030904 63
    0x6148402d106070070030306200d01501e00f4010054010700301c0c410786900040c0341c00d4140d102c6581c003e81c01c1c4600c40005034083c52000040c1000c0004118250b221801003038003d002100c0054014402c0104202d195404a410004500d2000c0c4038007202e609080400c0140025030b020aa101c0000400c225a924465000c010718050303060042003207a480c0e441010071442c180c2000d540c421044501c01d0f0040c40c0c6100206845000c8288080069a11841003c00c14509800110151300045404140c6040c1030000b000100404d10703210490610307070b40b0041d1004401501040c000d40d02c8500240a03c00f40304100e03040205140001c0009981d1800c01703034003c01d12880190394544403210284811680020010700c0c8034896050504084e250141d0111188510149107255a0748542c001400001c14406400110b00031010243e454180d9401c0101000351900304a80091920052206c800400900f840324031000d051180205508545034a1450003407905940c1d00a0030030f0544e05100010961100f40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 230455683 1250 230454433 230454487
    0x303050d0b060301080c0d060e0706110105092d16060512061005030c0d240e070906050414010203070209040c1a160b1e04060606020d0c08090f06040803 67
    0xc401c00034204002480284a800c0c1507a000d100c3c100040c0c07805030008000349104a800090840c0032840d91810f00d64681e110070003244070700411519018082c00303240d80c8014600302811101c0002d03130390f40c400750340c191460045000d004000710081c407100308400042419080a903031812a0b407064014055031240c40008141d4a0031000324045080c2142d05008001c9103403251800c5540702034800081d40c008038410844941c80d02c51803ea50000c01d400303c5103146100080350040c508014000c41d06000103048101040480f40080084c9580036003a6800d03030f40603112846401d0714003c0100e2440c01002070103075002c1060400e01c800c024038051481d04564079500001030f014409501d007402400341c425201c99403c0e42911070070008401000282d0b01c210440d44103980098503001d00310007401e080380c04603041c0b6a1910280a1650100004490340c5594900360000c001203580d43c48041c01503160090144003207440080486d0344100a0714043c25064044036215018a100b814000342070b403c241103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 230456933 1250 230455683 230455691
    0x30c011104060215150d1505010e040c0e070e060c0c120a1209060909150e070809010506031227060c0c1809030304030c061b0e0f0612150105070b010303050d 69
    0x102c8009014a414411100502c110042190903021b01c003005442d5003040303441c10748004100180c90b0f11b03032268901070048420b014046190520f4135001c1e196043e0042d0012108250422032200ea00c000c01120191f02a240e10f80c603101ca00444900d0f0440407810650b000408503200e0401c100c0001c0d88000e124064181a00c0e1280264070135141c202c0603020b2074001441160050103840c7c2990000ba0035402c550401e140066921101510f0b001c009807501000140e04105000300030b4001d0080c0c94008500714060021001e80a401c42c161b03224684000c03400300360200c00c0c0340352241000012107a42c14003910043d903454141d10156100c0e100801d0481c4911940140d01c8000740507080b81502c50503101e00114590746650f2400d0301c6011041204641c401d0300c844440981d11101c0103014a02d1a00d51a044031314440241000740d10180e2682550042d50188062412400301c040c006400c105212844805104440012141c42c41b40107005040814441300010406a002009144408078808100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 230458183 1250 230456933 230456953
    0x70c0602251205040e0103060c020a0b070c020a0510020a020d06110313060c0c020f12010b040218030f0604030207150c0204060b0307080a14150a09090b01031407080d050a02030c0111040602 83
    0x14800740114005d680700710302540c4c0103000107581944660a10b6159004852200e0b072941d03030b0242036110489206c40001d4081540c1c50071130414070f0381c280107404100c40c0702d90070b029903c20080d982c0600c0746000c0c0c070542650f1100002e000095101e002c408a10a052656900d401e02a080620700c5a0078100c4010b0f00e4801f11051051082280d44032056009110350700c1d1036030a00c20840c403036211504807000c5540c3c03082c4003540341c0e58920007004c07a00c9251180309240d9a04d6030405051011244070f40d1081d030001401c0000080d4046074000544980c0c50b560303800e1040440c0201c510020303030b080094100c0e1414a01266803840c0300080d52245c5507680d91504950760340201c90007966882c0c010520340c0c400d50000b055140c11003000da00c0d480d54001d407810909039a618246401c2d60f035208015a1a074100000500c00c6c44501c5400e0051442014010000d9a140402143d514658913030103400700800403800b4000c01d4801c0c000c44038003000d000024841540c00020390a0300798410710070070001d0f1103440107103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 230459433 1250 230458183 230458187
    0x110301060e030607030e0a030f030e070f0501090806060f060f040b0a05070b1f0e060301022a010b060f04050f0f030a03080105010e030a0305030a02090612040c09110909070c06022512 80
    0x38500040b0020090000007e59513000d403003143c0c0d442035800606890380000391101c5810045c00d0b00400c00c010f0040642e500d0880050709901e03258210100c10340205040001e191a810301c69540c080b0b00746d4405549503140900380443d40290741080c480c42100042c3d040000780c0c803401902d801800f030035030303e0b0540d160302c034000e0720095101c84d26441c5048800390070410340c1c003211340c52648800007070005440d0591500d404180c092501c0700c1d0f094118040342d5900d681120074403c4000505080c0c50b102e142c0044403d8408050090744241407040c41c5c40c0b03e524286894040048130101d901508840300a031480c035000c0d090354402d014507400107180a105100d646070004143c5401030305038030742c0d40c5581c69640c2000e000c5d40c0141d034500e4000508015030a0741da25100c912a100b54010841c101d40941080740100a40d860b4010030b8000105c140a00c04090780c2c1c40300c82641000340790034140c204504500e8040081c0c012405101c901400c007841d0341c0b0601c0c510700e8031141c0c224071403507003140ba10183c0801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 230460683 1250 230459433 230459441
    0x6030207050c130e030f19020c031903030f0f0f0b01030b0a05240301080708071a0a0305040c03120c11030105010e01060c0302030f160311010c02030d020d110301060e03060703 77
    0x8090700542c8414402800c83c28140000d840b0040419800b06041c003182807620f02d95801407404000c410000510213903028044801804040c0b098400380c0041c118520020f81c1d0389552490140c40b005100c2001810107002c8e5101c0243c0d070b160300304180841110b414402000300074180040709600e0030701c0390500c83c96109100340d40440303078010000c1e20722a0038203050201c440c0150307981448540e52107940b01d880807000b20245000b889141d004004507030a000240f42050b1059100c4140420844c5404100940d400141c413440686417500051907a150f042245078107403164009420500703003132901d40c0042d520190b43c1e0305183c024541511110500400d0500b2118248034000c10112203100601909103da25801c0b00781d40644120b80c01e10b00c001151030185d50011500c1132510b003845104c2d108041c0c024400d0701041551b50000c01c00ea05020101944a00c901c0f0f00c1100c009600044400002160f640702406c08070403040b0031512580c6501000c0c14904580380d801c2d10a00c259000540c1152007030007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 230461933 1250 230460683 230460697
    0xc060a0b0901170106090e0319090e0a050702010f09030206070906090f0501030e0a0605100f0501170f0c0c070330050412060b0d110a150903150603020315090106060302 74
    0x4000d0301a03181400e4000f81c1050202c03108011354030390b140010381c0242030103111a07216000c0b000d1650f981c40c0d03203100700c2c000c2420240305040c403050100800c80764600708542a440000300f2070105e02641c40001c124010681c0c404070000491070071900e1424190f000a91a205808907120010155110f442c240c4041d01c0c540708801c06124000010b1080754403c1c1c12200500e800074085031034221644e6202000da80046840120340310b1404010088a41c40100000051400b030030712403074450184054032215000149201c0b0010341d4030300854600205c4030112038101e030f451410356009945a2500b070118042031043d507400910310004043c05c503030160106080c0000c0a48036280f0300707480c1505035105103051404c01e03284560350390800c0c01d182d03c861040741540f80c400c90709401c0350704001c8200102c400b00d03500300304822900d0141070001d042d005882c3d1400e50b138101000402c0c81500b03001c00c20107010a0740000703405015510b10074100e1003030394112500600380c2c03000034804c0e29143e460440881c06005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 230463183 1250 230461933 230461939
    0x6060a08120702040b120105150111030a0c080c01020403060e010507020106060504030308150a150f02060106090303051b0106060c060e060403050f07020a0801111b0607090531020c060a0b 82
    0x72180d0200d180e181d0005001052000e000440d203d2001c1000800d1888032150f5400e07580d4540c801c0012a003646c074030f9191440300c01d00385226002d240c40c51459882c0903142c1c80d03009110702c0c49151000e1080d41000e65031a00300e404000e41d46c2c4c945a10703022014024103145043c01e90f0070900410303990303401805000c0a07540300307682e25404c0c030303241d610200c481000240c0040030070640801b0b81803090b103441c14841c0203016031000d03a04100001c82001013603030515030500d00440d04000014400141e200c441c08044941514140da100d18484801a090361600041c0410940ca03101002400d60b4010001c50440c60240008001072500c070140c907601c6410450700200050030800c105c0c182c600b8428054071501e400a07110140881d124660b29007182c104440e0f00d0342070b900c08100b1120080f43c2c15201e411640302030014025500340003101801c0300555005061261660301721941019224001c885840403484440082000c12400702400a501c2010350145a003e158005a942c203034a006501c4042409 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 230464433 1250 230463183 230463193
    0x120f0c0d021f0509150702010e040b060d0c02010b04020310030c0b030103080d0509031308100f18030309030507051603060e151b12150a12080702040c0c0506160206060a08 75
    0xb001c07201110310b0140b141e414001d007448403003410b40314054043d15030041e00205658a5080b40000344c103100e40c492001d8030803410842c4c20302507074852000359070440c8440d0801213200744d500e80c0b00307a01420103984c0e10b60704140f010003040070004007000d00c41c0440c2d0068080a140c161909480212807000f400302070050341081042604100c9107030b024950100c500000e172401c2c248005040c440b9400d00340d100390b956601111b800300103415644200d04602d05100d00401140456420b0956020300989015081c965901c1061045c10b014404581c64207501200340c802c4c480d41110036a034020b42038001500c509181508618100720000b650001111006500f50b10303642d03800103184120140754003044201c10081c4100860b280c41408914040d0030010981d44890044d8018802031003126840210803c403103042400c0420910030842d580c00d40c0503034001c03c1d40385c140c030302c21759942c1c440300360080c424840c1c4010403045034003c519844291a1070b909440071515400204140b4103060b0058001c6c50b008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 230465683 1250 230464433 230464459
    0x803070804052e02010605040b030114060618190306110c0a1119080c0315040309030602090a050a080c0f0f03070b130503030c07090606020318090601020a02120f0c0d02 74
    0x1101d088040036542081044001c1103e80300031007000c40e41510314201603034503004d0500041c41d00380036645100d40e007500200030031110105039050104d40500442d001c0c2e40f002901102c200406e500030800b44001808008a00d48040c00b408120b84092005850303031450072401c56000040d1404854800c50700a0080c0b4100f2529243d036499501c4403803200351303c81501410412005c1410350190010184031002c1c2c14054101c00c00e250802c5100741c190a910110174040000003070304070702c4d118103032600901d0060b151a000c80100e890780016802142d030027a003480c0005414200092092031898081d00c566003203420103c10b200d140c1240e80403065054020312001d2094030500c1c1d02501d801502e140a0042151741e580120341560302156600d526600300e00005c1c020040a409030301d00403d054070003103180182c040000c4a4115425080d10f210301c40020114640e03a100300009000345030002c001801c1d6041501046a0315043c900c800f50ba40e00401c4900c041d0352034405a1541000d8015002c20b0320041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 230466933 1250 230465683 230465689
    0x5011803030e010309020a080106030b0c1e030c04120f140109020f0d080d0c0804030801170c2101050c090301140115052a06040b0604020a0f1407082101080307080405 73
    0x2e07058405041640d03510320080583d03101000d010007002128000143d45041d0f0610040c8648001c04216040303d00300001c1d0800c41404622070707298030f040310b00c1c41d460382c9540049140f01c4c4a07a07440010b00c0480080d0003410703c07006006410390184a060000001e980c41c03803d01e8281c030360305140658405802210700c1c10f1401c040300c40624061203026910302c1e10140780111011101080440340000b01d500040008042e00a84141d01401118012032001c00340d041c02c040e980c0e96540c010758001c8004210b220a0510345503203180d203015414000b40443d141281039003850b6042034004610a43c207240800700c0382030000103114141c0349001e82074502c4070802c0c441690306074807032508001c0d000d0301d8800340240204020150b0207081801c1004c3e0440d400d15040015010302c01030000c40c45180f0400035402019084141d0300d0b00c0741100e0078041d4a12051040703605090040c501c000d003003110005940f4030002107100881c0d880b243d11100c0090981d8807010410743e04e01a801c4000c0c02c420081000b0b0101d45 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 230468183 1250 230466933 230466947
    0x21005090a05030604060c08090703110609151603030609090308131103030304030c1101090b07060e12040b04030204060b040302090c181011010c020d1713020d030f0206010501180303 80
    0x1000a8500e01e0882d82d100e003c00c0c60071400312001d88411381d5440c0c1486030307954403c600c1a040710010303000b01200c0341162541c468400f00c50041a00c42c6400041c040c1054030765038440c0341e0b490a4490b0302c40c1c4441424a1304407803201e10103001c400003443c0c000b01180f001c020340b1401d130209030181d6801010380d550341175150075030f101000155441002c00c54200d886039001c10055200e03a119a4402c41f20404a00d802508014030b0240e1a050214aa10500007541e103a025100a20b0b041840070580c114030b24100c505064a054040e060341d00d0010703000c43c500300c10724018011280300783c03001c110190361407800142501031404001c0d030015151010800034860300d4090003851001e501030b42410440301e0001a8a1803035210001d000c1411400f003404c940d502031003412120388050001d02410078074030400824a032000304034180c079464104081046c81004401c4a07140c0e545c050051500c85925043c081c1c680080361003400010b1092800100e0301e03500c80c8141414076103460442a030040e003180c3d4103a81007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 230469433 1250 230468183 230468197
    0x70f1d0c0c030a0c0b060a0e0a09020d050111071a090d230d0905190228080303070513090b0303160524061c0507170304031502031012021005 62
    0xc284030700d04041105000030120b40040b51a018807440039031402c00d00785580145400c4c4034200580c420043d202c107074240194482d030701c2800091a140702e0710001e500c3c0503201401074030300c1d071902040e5401d040c6000014084640103010418072a82102c0528200c0d940031189429590801c26542c25101c2c0201d08205200040c5000d00c40030048402c1980030b44d07080030303007032000b019180c904404c1400001e001e1094241c042d00c0e10300726002d0864001c45d5412650048034400c1001c180d0b4404000c00300050480040d0408a080d030b640d8fc180300304010100c2d042000ca0410a1903010f0001420a0040c0b0800b901c948001d8003942c00c00b05010740d00700c0621205007088d40c29004545910b81840c544a0314180d40e076010400403851400e1030300a100d0555217a5840c540030000b14002c060100d1000a01c060454051600c1c075007500110085141c00c5009075400140719801504442c1800b001c2a0040d521402180740d000c0a51507a5000c005059413444030003039041225600c5904000c0e200d0f0009002c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 230470683 1250 230469433 230469451
    0x10f06051008090f100506041103090c012f100507170406050408040506030a06030c1a0301051207080d050703020606011b060c1b26030f0115020c1003050702070f1d 72
    0x18550f500140079041602501170041040da0328010020701e840c3c148200500c3c4040000404c1c103601e85490115907074130940c491141801f80d8020007003d001b940103510300c6c1d50310300b1060308040c0c003110845050b9603101e0300078045245418a000105050f20982c110a03808035040d420080710340f213a40341c1e81c0c000c0034040d005603003050341000042099100d0300001c2d8042d03004110300140d02407450034402d03554800c036005404610700d010320130021061490700b0342c0e05643c002c0310707440000481481c042d441c00502d9440003581d409801b00031441c45130414080d2001c0c6000703400383d9410f41d83c0c42c4011074010050000442c407051070011000301081c0941d03c0102c18181c0c1d403c0c040e41100d2641d040b024244070f9440e08580c4181c50300111703606070420000d482a441400680e060560410010345d001e00c00050044d025803410403101008540d2007003100300325199020f0038107001d02004c124010081c01d421200700025101ea4607000423110380c0907951000703c0f480401030350015811450601d105240c05006100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 230471933 1250 230470683 230470693
    0x1a100b031003022206090c0207062106030f12031103240a09060f05060c03190504050a12230303160c080c030a090b041203120207051e010f0605100809 66
    0x144c80e9504072a4001071207200625032134911902c40801d55520740c0242c5130103418a400c002c0036a80006100c410390381c3c50b0034100e40b07141c41400c01d6600f1141074000c0703a080c2c6060820010510800320a10000c0c070740142141c18120314105000c2d030944207200c0d0900700f44081080002c0031503054180c54100514107075030040841c5402c500103950f1a0064021031080b40e07a4441c1000204098003900b0003c1c0001e45000382042803081040340c890084904040380300003151190351140c0d22030012100a00b80c010a0303160030a4984040a5090802410442d0110640e072404600300d450a01c01d0b02e00038444600841c40c0d50b584240c1c80800211452904090021071907014000418140290110606610007940c66440200000b41000e00135840442180800c0106001520240300e141c400b01c1e402d420501014407400314000000e1040c080c001e015409100040c0306940441510050001c03e070200a00c140d18142d002d8004544040c07059540c4005124440144a40513070700c4964040e40c0d40c000d5074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 230473183 1250 230471933 230471939
    0x20f030610020303070f20010f1d071206020f0c03040803040512031305100e090406050f1b0a030506130e060603070518060906011106040302010b030d09030b0609041103030d06031a100b0310 83
    0x39007034910402782a5503540d100c00c2c20064600342c15024000c0c45501c00000d011140c40e1040106134180c44c0c1e0302c080c2485800240302c3c81083c803c481158445041d81c0304a83ea181c1d99819800c0d200d401a0003250f22642e0300d01c03201e24819a0000c2aa0102c0c00804030080c580d034a420704000b529061148101c0520154115500d0380d640e520104510590292002203102d00e451a005000020002c0a00001006000400da503601800c2d0648584851509000540b41c80c0c1500184900304401c41c4c04141d9820681103c107804000300d503e40c040c2c942982207031440303512141008120040c000321a0070890715100054030b1458625102e90b080b281c181044181c80310354400d078070f0500b007040398290b0140c1c1d140c07004140942410400104450b83e01c1ca8500015411175403007940b6144058002403285c440d00000c42e05110740d8803000400d0707040050407655254508030019010304101d00c815102010890142a011030880b11441d2203950071545a0707a580b420202503e0305078001401d4290400e09002c07000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 230474433 1250 230473183 230473247
    0xf0e041e0f0608010e19031d060a050c070b031603021602060304050304060806040b011d0a0e16020606040b09160e15040e07020a170901050d020f030610020303070f 72
    0x40c028107000140407400600f0302c044642520540440c100041d8400020707101d01650708414a1046035041c03030f010b0514a400100d600030b8001902809601410004449503d650408010410b0002500554030b40d1036072080c901020713000840c1e04400c04000c0caa41606580d1190380108000d83d1844c0320500184415004268503800071601101c55a000003420b004640c0c0002015900c424121800c2c801b202d50340c4002000d03000303124118240200d24100080b0150313240c42100780030300901c02c40d140080c50021581c102d80820208040094061036021030800e0415021304880d4402c05010112580c89280c8c43c10b52840602124100308a680c000040f50343c0d442820350350300d81d08161040341e103490501c001e58515080c003070300b08015544410782c0000000c140c03180d0001401076282c5000c0c0c845c0854401621948121700705900f00b1880010480300900140014500402095801c032018503c0040240c2c0d9a1005a81020114880c401d0301c2032000d215022020811120b5280c4901c034103000000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 230475683 1250 230474433 230474441
    0xa06050108062704030302040518041502030430030c110307081b0106080102120a1e0c030b0402030109060807080d0e090a0603020612010e060607022d090108060103120f0e041e 77
    0x4170002a00042e0402540c41c11065502d80d030b44042481c43d02e035050540e41c100020103821680c264982e000b00000d0305000d98010040c102c642400c51819484032079034501807501140413440c1d00460724020031014400d01c40c801c1201c06001c564000c501d0110301d0f44941c4001d0300b2124000c805901035040451070250280104401051f000001503100e01c5102c29030300c001e00c00202800310080c507003078403402d04240056003000c4440074008001029900700e034048000d40a0080b4050b0010700000c0000b90403030143c1d200d101140e40c004242e44445458031401a140d8100c40d149400065107030420310120324001c0c090306e0b00140c0c104400103d00d540c81e80414656001400c5060340f00c04954010490850203e0510780c0c0124221022450700031142d0014040c1c0000003181c01c4030783c590304003a014651107002c0b4003050200092072218250f9450b80000e5494500740011180380d44401c20740b0401781c1c00303185003480400e42512000340000c0700c0c10500006000688040380d001c8440402d89285410f680f013 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 230476933 1250 230475683 230475691
    0x6050310020301211e030e18060301051609030b07050d06080102031f1a070c050405180d0507030804020105161e0201020f030c06010e1b030a020702090a060501080627 73
    0x603026031030358509a0f0b50f04098040c003000c2511201c240700300e80000f8682d4904141d00b101c407041c58900c01d5455003021581748605c0211242c0185a10b2032250f00b00109841c0340e880385904078000e020940d0760030045401c040440c0c0f500c10100702841c2003800000d440301000d5a00251070b152207400c2100c102c05e6072040d07500e143c0c030611081e58004103101485c0e800d034030880100b81c4000403450030703240307001c1c2414a40c10403114602030313a13000800d6010411141d80145001468000d00900041c200701e940c015081c4940c0c1070708005481980c24030840e003800380e0240c0e240c00c0d401da2101e09842c0c2e510340041d503143e80907140c402c0d561600d1000e07a038006280d00903550358074030a80503d000c011f4840d01c0060b12b81000200000010350040c0301d803110350320700000d40a05454400f01c0301301d85621035803600138000d000421611f00000012042012142c40c90340034001440c0202d2f0a10346c2501d800681408451302401020b002540100024090307041007000100d120340013820700782c41034100301301441c000e4505807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 230478183 1250 230476933 230476963
    0xa0b060a0501050f0a0c0203120d0b01021609020a09031a0708010609050603041502070b041b0518010902070201020a150b150c060c0a0c0b011503110a0207120807020d150e010902010e13060503 84
    0x8503210980b036807548a46943c000c428000ec0040034000e54040380300c0e94580c4500c2032115000194025224400c6440c90010b551040703410400d1080c01d896031140741c030708442400000b0701c04800000d07445e105da0052022950003500b510300e50b4031391340c40d440800b40070070020103410b40c1c003008240001900d504a007480f490051000d100b540000000c0b00b044c20074554032140c800e4100d0084980c0540c2032482c072604540118500603940c030100e00c014de00340072142000ce0a1110800401c52002c01e25422060150b0f0080305ca1400c000380004809543e4020300000b609140e0100d400a00c1c1c18580b000204003c40305130800002d180308599400400c604245c03c40008000d0000d040140e0540601a4905070403511070359a04004246400030b6507505103110304020090072900910901244004440d02c50780c0103482c034107860200e810b0109414110203800c000c000c1c075000c61620341c0001032080e40c1e19a031741603440e085212401420024208502c00880e038441d941c4100000740c0f0b55082001114002802c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 230479433 1250 230478183 230478187
    0x7080d110310170c030304050409030e0a060203180109060c1104020f0403140609060403021f140903030912130e1b07051b0409170318030c0a0b060a0501050f0a0c020312 74
    0x424280f0308616801885103100d58029100c514040e680070041e02d082e14000c0d1400900c44a00d402c0c111500000084019000a01e091020401c00d03404001001e500c10192000c1c6491004500111040c6400744074520005144010100029003400d452010070312008001600340070700c0d02210030955010368421103180c0155480100d60384001c0c001306602c0600c00c0d01a00d070502e0591006501d17010205004045900582d0460348a0300c61507110090044076045c0c010450702d0700c02c01141d603d40c001c0d40c1802451140f20059100388442c1400c540703001440704a000343e401d140c441185540740000c0d02182003510345e0858111a0000440070300541030056005211860261203220745c1342c0e451003102c070f0185042140b181e0124001c0700980c1e000c0140d00c02c0c16552981d84000450b001d0180001c18480340c0000101c058480c540011001d0b1940e0017071810548985590080080f00403041c440c00303005c61000d20014805401d0170b000386c0320100041c00c102d81c00c0316841d0300280c204103074045400c008940c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 230480683 1250 230479433 230479439
    0x5190504050109110901120f0501142d120c030109030503100803130308180a0605040f1e03030e360a02070f020f03160902180604030807080d110310 65
    0x841e00841d40185101c0c07000700001144601010301a11a100d601030501c00c4403050020092000e9212006420380010304000c00d584a15440040c0008100d00034885d23142a0204d0249400c0301c0c107000060341801d40b4215203000d00790240301c140c21036610026814017643c4809407103602d0a004071103c10b0320030350360b03242d89150078a61140000426004030000d0740c824001c0c00c4124040080d5101034070740041e60305850350349a01c8100004035201c04066080410b88500141058201025105a40c42c00322180045929a07014000040803c1400c3c441030002807020400309001e6214419250000b40012440340b0400c0f08039405a4944000c0c229040240006500541011694690071a848810035840c04216440f4005805c8a40c440640b14075604d40c8003442542e01040742d20590a4003290080900d540c0382000802508000d40c00c120002c00445201c119180010884d130980b50b011289500b800207a441e110304503042134a400324455076440e86041d003054410040c40c85914000054035035541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 230481933 1250 230480683 230480689
    0x501033c0629160609150507030b22090507060f0210020414011103040513020306030d0206100e15120c040f1814190b100506070309140a051905 63
    0x406540300380000350811506007086200b8095010400003070114081e100d6803260707142c1c07480301100030004012520703200d82c0004100700505200000c0f40404020080d5a4680c0e2068043c2d400c0f101c1a16440203000300303000c0403407034000303000c4880d180d14010000c0c0e201070030351701c0c1481c01000d40c1000e00403410008080f101e081e4104440190519500c5007541003d1400d000801621005420241032141000f441c40d20300c2c1c07040090314018a0003c00051b68000c480c0d12120096006503561402030090309000f69005000140302c074040c81c551030020040b0b914100c140190303008080c203071486c1e1004d540c50b80d11050350340300500041221054090100601104e0800040303440015030080824208004c8014115864005659035601708101d58004d500c2203032002d090003600c020301001c00c101a071341c1c42d0901405441262066900c00540d16805490f50200076440c024410000c0c0012940c80c424020640040e6660540c4080034180001d040c0d00e900004041703908034101e40700320807003840040002d46 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 230483183 1250 230481933 230481941
    0x30708010f0503121b0109060f09021809060106080c040e07080a2913090204021216030e0a030f021905010507090b091c02011815120e06010501033c 65
    0x840128000d1200130559030b2000d0681c0a080b680b04500402149078142c820380c03c1d0890400307240d00000130040ca81c11240c0c038400404c041c0310309a02132007001c2c1c6602050500134028034001c1c580000204620380c80c000c0c003110340500013401150321010a01c0005071a820015442d8004d019507214003146240040c120006c484d14080819040d00c0400b40c041482c41c600c0000c5094440291040c2c030384c1011032210075000c0e0006001c02908140b0000710942404009800380c0e0207642e008540d40c0f034554142004030182c3c3c01c0d48580b0381c03540c0c001c103621301c0020b40030304001049034245005030b4000c46882122101941000c84003566582d466500300a0015030121030000503104070744d400d90600d0300c401c0c0030418080900c1055170300d4140400b0290103580c099608100310003550201d503409292510740c004811a01100000c020a940518009074101140902825581d448000f07101c0c2da80b038000110082e00740c000c06a0340664004085055000201041c001039054848510a0007482e001d595000c42e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 230484433 1250 230483183 230483189
    0x30b0711060109140c19080705120f0405010b060f0d0902180a0504020a05190b0708090d0302010b0f0616110f030a0614060306040c150e0d0b09060a0203100306020c030906030708010f 80
    0x4170002c01141501d0700c0500e43e0134000810303615000c03145560300718081c1c031580f05100c101c14448005d04100201d5240c1c21075403d00c900e124a00900c0701d007940005100b80c0340550340020081c5481130002000c0455503900c00d551180c00102610520712114524805800054a4480d00640c03034104200541c10085c5100004000039030790328541101070040740c40c10100f81e001e00e04410000240c04002d12680d0415100850401021010400389901d0042d000301091510741c0d000342c01c8041c410b48640740c08400da44c00c401480d902c4000000842d5034ac1c040c404000d89006900001190026401ea10204240c0c0d501501c142000641c00407892421488004000c1041d0300c00d602001c00c101c00160341402030800c461760040c1c03001075060b41280545d014004140e00d160000003100e80081031043d00d40c1d98034000c4504c0c01c240c03400d46d15038100050507480111031026403503100300303020400645180e00901c06205104241c80c00c05807a100028191f500640d00300001640480040c80310300c10481c400401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 230485683 1250 230484433 230484451
    0x6090302100e030301051c0f0611030702060708060d02100c0615180501051534060509070303020c010e01020312041101091202030606090601120603151a0a030b071106010914 76
    0x4c40d0b140000040d604d281d045d440c0041892005208401c103c1c040000740503065000d002403101d00e403010b009401c9500200c440400500c070308004180460700135580c0e14041d020180540b0b101c0b065940034010324400541119040049840c40c02c804240039205000c0303825085650211000d1403c0f146803004814800c02106103440e000042150760303624900355903410503100c401d9480381d19100f01c03940e200d980100380d041c880700461002501196200d4550801d1481008100038030341719005442d039214943d0200070056406850400030540c081d00341d514020300305104036803408404140c3c54200c50f10035a022074091240024401056821904c0303e800745c1210722034800c105c801e41e00042c0c2d5540000c1c041a0055403000f01007080c03a44280d05040000c0107500050180355a0391a11443d881044d1440b00f40d21031615090842e040542c203030320007440710010042e5180034110b4845c180c1001c1b01504007002c2c414200040c00780f00c1c4060226030300070502a1030008240024400f17804045500404001c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 230486933 1250 230485683 230485687
    0xb0405151518010f03020f0a03060603032109031710091802010e031203010b0a0309060c0909050c070209270d02070f060302091020010921030e0303010e060a0306090302100e03 77
    0x8202c101c60540813084039011108880141c1d90031011504203140707070f00050411405c1442c007106068004000342c0b01400c001400410a41040101d6070845d90f1032440240005c100400200c4121003040d00c20750400c241d104418035013555054401c00702c6070a490100c8080c4131641404c4155a04440c4209030355070141c0c013414020418800f851001e10ac140200c070040e90303012850721400c5100364424003103540d000000704641165000d001e08205424410000030600f02400141000000350030f40c0c07500d50380909030311030329110440c8010401c0382c0340b4104c1c0310371142d0785101c964400e0100034a403c0d90505402600d0104c0c01c2048064820200e608040d05140c01000b40310056241d40055450030800d078500741004106014605128079068220102d2543c00c3c030301c010081c000021968400140882994a003201d010074050f801d4480da1085003c95400c2480100050740c4900e2003658002401400050f0785074880e80c442044500d00396041d001680b282e10300c940b052a052080c49000310301074000314 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 230488183 1250 230486933 230486939
    0x10504170a05060a15090e0111040608090f010c0f0804020d0807030f020c0609010c11042004140319120507021e030f210a0509060408060403020d0c0b040b040515151801 74
    0x5e0f001014454070551940e5200f01d0402e040080d841044004540f4000b544d4885d81c4042c001c10141c420344010580e0700440c12065086503051040c08544031503600d405c1c502c0d41200e1810307079450000900c10381e00300709840c0110b0000f9100310014001c1038400e8039240c249a2000d54024503200101c02d00d06d0080c201002a004e940c1c0c2c010201c1d58040740e2143e01c400c06103c0401c0407401a010030b0fa40c422034010800e102c2128100380703001038010b03501e2005170140e03010350440c02c05a4403031000c000c0402e0b001d01c000a400100d2518030405d03d1703044250400c0f514200031640896120340c29242d9808054220140305540e500c1d090001c5030000c28000c0092421029140d907420219004240864a10030001904580c03030b4060301c1900c0343c0b42402054607481d15070b60030b202600c0b010121011801409901e0803440b41500812991404642150302c500c510341d960342d41c0490200b40a0002c0c4c036148500b1041c01c41e80d041e0208485e1158503040c10b45c002002401c0103200000350040503021400e184a0014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 230489433 1250 230488183 230488211
    0x109050601090f0e0109111e18091c050403140607080a1a19030309051806011b060c021c090b1c0603021905270f06010504170a05060a 59
    0x181500e0020b4400200046603101d00303001070140d20700820081d42081540014040107050f0451b08903420398403400340306030f00220452008215954942c3c0800620000898000c541105c031b5030001280080315403800e0543d089040c60059101d505000420004042c401c01c0142440500340b0540d0000074805410060340103007524a0082c45525807a44c0e44590001480f0100041d1500a001800014001e1202c0d580704d0130210aa00047d404034107281d000148606203600a96003059484098120700d889400c01101c00c21114400c20000d17510014025011400754401c1c2243c441d021340061048004080d03500c034a0300762280c0c1ca4030500038800e1080041c0713044e10341180c00c0c0400080d0603d14644d482080c4200a00300b03a0070294104081c01c1ca800c003c1041080c0c140c081d240201e5650007403017510a959035a480c04c1000403204012401e021801e04440114416000321050420320b0400d174444400406048680d040d02104c3d80c021741d040c00c00d000050100940141801d001480f07480f90304010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 230490683 1250 230489433 230489443
    0x412030305220b0405010506060c100203281506110a02010809210c070906050a09050403030902060f120f0f0403050d0e01110307030e15190b2808010905 67
    0x101405054031140003420041010850710b9061010015200c80d03031406050801410504542c200d80310342c6004041002d43c0742020658010306c844200500840306c4581524010b03400151602580140604e0b5020500a05415405d000c010b00500016114101d0182d0a020807840d48480203201d20034074141103403000484c417000b84c0e68080c00c20701c00340e483d44540f203460043c05885110b40e101c410b055011100610703030f0040c110810010b0451318141e44415000c81200c000303218145d801001800c00b042100c000350800c40e445070003420001504e8207d41c002c10419400720500001c02c400011b00780c0c0518071308650b00c54000420b81c0c4804480d01d00240103000400020b007003c1e00740100820140041d401c40d40005007842c0443c2c009100b040484040840190402c1c0c8286000c40d0420000003a2071100051000704081d1203520305000d40c84055070741099014200c4803440300d64071080640e8864032060010030b401c0ca5405090550390300000101c1708600d002c5e4100110036410886070f81d01142001035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 230491933 1250 230490683 230490719
    0x21c060308090f150a050703020607050a120506010e0d2d020d0f050f070f1a07150209030106211a01060c030e0103180b1816030f050111040306050a0605040204 70
    0x610403c0c50701650b00010022241d107500070003130800c0001c81c903103490b6002019040d103921903000c0341c0030b40d12440c000f07482c24040d15903184001220380300024050401504600e80000c0d042c1456103032003580d03402203504441038a10503689046032403041c0c0c0142d2003401d299003c0b00311308425001e0305e111550020390710300c2203110301404400003c0710010a01506000549080900d03800b01c410480d0707901c1c007000303034211548240302441402c2c0259441c005075003402c41e030090350f2041d100c150841d0205100700094020420342c1d40c1565840307030081351f0400b140144100c201c540190701b0408088a00d8920700003a002540b4840c008110001001001e030030000030344400b603240c00c00d11258402400100d009200c101081e8028108080c2d10109000d0143c2c11540603402e660b4480f04000c5000750265074a001881030800344c2a10400b0800200d01d44203064240244200b0003c191002000c0103002e868102d5003007a10032583d15420703c00440c0b4148280c07070003464143d40950800b407a214030502c90415000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 230493183 1250 230491933 230491939
    0x90f06030b0307030f051203010909020103050c180d081c1a0303090901060804080706060b1b030c0c0105070212250501020d0f0c020f030712031701050f12031c021c06030809 76
    0xd0544000c1001c288140d001f01403000b03021913225070b902c2040602030142c4420a80c04640740c4004103a1a0403c901218051040814034070150028201440020000b41c2e00607070b40400c0500c102414003a880c01c0c0b6103010f040c412001304900c0e40c003400d688a94550301e10700500c03076482040703c0340c0261510200d1504540321418100003581e04c60a01d0300c0700e07108904000b0040c61070483c021482a543c00040d0006c80850300d808801c00c807c0110107036482c41514070440e5594404400040c02e5031141c4001d2607002d1016042c08c4e18070401691641c0340800d0b0120950f001ea1144e01200381680c49614100010034007440185101241d41001600c40321050390400c0400102e24010021740d101c200d05003c80301e001408035000181ea909280c000c8002846046000501d12010a12031003004940303030b41a248020080400031070341008118030f42c0d41c0c9030346600041c001403101004941c0301b4414160400007100001d680c1c0c0000401101d801900b2240d008002444c080c018400310303070303812f0a175280c600003a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 230494433 1250 230493183 230493203
    0x160e0d02010c03050a091208032d01050d150504060902100201050c090409021c030302091309020307050909071502031b1f1a0a350c0603071e090f06030b030703 70
    0xd0440d881102031f00040c0003415905c440d01d0401c003a0740000d40c4918030400d011115500c4255030f240070655489001c180d442e00c2d8070010302c42498009c4030901c455100714240d1000b8800302c05820305a44088609446113540c80043d081075007010800700c440041c0e1880200034a14001251010601030101c600c3e01440d6a40510011500c036032504242c071680e4901080086ca40c903190050195004440303440c0904125850510520581e009040c40c46500802408005003480c041c040d44400042c0140300358071940a00007900801d0800401d1704e610b042e8095690b0300315801c80155211140b421100b40c42d070140d5500d1490b03860484009088071148503000c00c0075201c0c000c0c1c000303501f499040fa00340c2c800d90010001034107404850b010f4902c0f46004c000001d4026038102c0446550002409500a075008a0440803072840c04100030b40d4004900c2c14524074900c100700c604032540742c05c1003c034004940402c0003803090b641c030f10b01c4140c0100000d00d4284602d6049a001c291945403d2000800c50050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 230495683 1250 230494433 230494447
    0x5010b0907021c0509120d0909020909010911120103051005150d0b04020a2d0608071209020607060513020f041a090a020d110706050906013209160e0d02010c0305 71
    0x4a07100301d4170001c4005181024090550000984548503440800041060020005456803481c006d5502c16040208a488668603000390b0901808440000d040d810754200301d52440c00040e80c04240c0030f54060401400b208007081ca08a04036807010380729501c0b20107650108081641c400303100340c03e1160300098080c1c0310b403610700c00700d14030041d01d4011007030100301c445004104403070f19200320078403040c500142d0f903800c0d61b102c1742910200c0d030903900d18001641d2070060b550303000e0141d00014040d510203080f9502c4c00010b619600c1c1100c0081e2108801280749050184c01e40c50001c0c8451a22207040340d0411044840a60105070516624650780c010444e1000050021b10558159450100c5601062000300c1184039800c1095010305811100c103494480402c0e4282c1000032541e050303425a90b11552800b4000302030996841003182d002c6200390004031800400e4640d00030540c002c48422580c0c1050b0b5460302405800f03950340e142410f0003501014100350140c0e0b48403080120342d82c1c05042c82c554074a9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 230496933 1250 230495683 230495687
    0x3050a15180809030f25091a060307170c0a180506090d02010c020307030b09070603020f04090207050a02030d110106060203070f02120f07030507030c060309120509031e030705010b0907021c 83
    0x1800d010800c02038041c104100e44851000810008070070844003054030610389407078620042381c082e0301c00c10704491003071903400e080c0f41895801540c020303207076040ca000c2c950044103d0f10b80f481c20440b104030319080e000c52180041900982c00304204c11034007100310585410100032500c5400fa004e0300611881e046445d00c01075901902e00f00c000140c01038291840c0e2600e03407c4c40d0301d825809413241340b02f611030002c000403c07038404e00c00d4441c00004c0a02c01480c091400f00d8440c01b03034000c1d44c0292103500800c0f14580c0181c0d010001c042e0540302644410304200c8849107042c4c00c4404035880641990030800c400400138651044060a460b8119145013140d0f401c1c08001d45442c4402035002c041c3c2c0b0621101100b071000000d018021a44600140d02040b0b80350361045045d00e54001d80208185e41c401810790769203000710040c1c620100b002d0100c5008540101c549200e280c09240310240503040043c80c2414400e00303004040d521141070743c3c2c0f14814100300d20000d580b2024450121300e5441c4014400400f24 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 230498183 1250 230496933 230496943
    0x608131110030b120105070e18010302101e020d120c17040519030e130902010203091e0604030c0e01050a05091801090f0602030618010602030403030305100b0403050a1518080903 78
    0x820050f003c4e0404010300c211560003000c6c180c0349480800c0c08481e030800340b407610030741029611203e90000c01d0a40d2850307091152403450005a10140310411843d0780c041c0f4668915401a0045d5600078004090450350150003036208028060030141404140c15065401c90110120040c0c0d45111002995460400728104440e501c181c0103407074204003401040c554060940590040210b0b140e25000780600b009400b2151600310003400750b0003c3c0000c00b90361400c482c00048204005c00812546000e01d000641c0a50080c1c0044601403001082886020140040d0718050001030340c40c40401d40c00c3c1f800044181c0b0000704200c42c4103000d50120120081c0039004000019031240070f19002103c9480c10202a400441c3c005000360000b28071482505814070405040b07a416801030b611f403d056803405c43c06008010100c02d500f84090b40d00107103011864006000450244010340002c07030716442d0070440c4204000c00d40c1460f40c01c0c0420040f2020181c0b0040500c654001081e030f0790b400031310012034140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 230499433 1250 230498183 230498201
    0x1104180905030a0f080a0614210d050d0e0c091902090a03140606030d0815040908070507030c08011b0e0102152403010504051e120a0207060813111003 66
    0x240c00007149420f650740c0c0004904842000b991248101640c502070301c10b0031284e9070f10a41e1800d4140c410844840d00349503007a20201c00d5641c086080010200d26020718003402c0c880c00c80d000400018410010f041b5500c2043d035524190340c05007854810340e80000e041102c01070900c00c4018200c8251040340d00ca903904a420910014240d108401d13501d040040412500543d10b44c0c1c0d5020342400200702e450045200d1038420a552500555030301c580410b86e042034003104000784c21a0782c4040500125608030b0142012500c40d100400c00d490039885c1070185506250300001c240c6c2e040203a006550000c2c6050001441100d203855515a040040100c0c074141415001d00511151362003800714251511320409403c813420003410039007084070001d06007201c0040340c1c05030454000c48810300340d40080c007910700554200d0f80f080b60114010f082c80c1340e078903910408134800035900c03141040005603048007a80da40f240c50050300700800c08154a55658400d00d42c02c14610801c241240d0207904c44c0a5801131042c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 230500683 1250 230499433 230499443
    0x2090601210c120606030e0a03031a09090c010f020a030503010b0711040e0a1205180904080f0a09060207050105070230010207080702090109020405180603120c010b0906010311041809 80
    0x407815140380060f06100103c0005101e4604040010840344e00900130707002403044550050203109500c0d282240200401030360032001b00207000301e840955840c0071409010301160800307854161003101c00503080c0342c10480800e065400c41c450501c046034022054030704580c01e5004066813440d2519103280d0104004c0030680d8400d140147c4206c101000007040d501d598414041d000c40a500880182c84034000c0c0b45190154081058006840c4d08103031400d00e802c284180502401d04000e0109205103030810502c450000c0c06100c810440d2940c104040002400c080c00c00c1403400010340c0208400c01140200440007242c80c00090740000e9034400307441020040007000b10341310300c1c0300d16143c9007a070700404c000d9102702412000880d40b0a040e1080b2012100c0007010382c80b102d200d200d4440c0c003e00008100070307894021509980020a483c1c402800007140000c000100001d421081041a0002500c540e04141c50955100cbe60480424129402d0380c2c0c80101c098009000e0f0009240034001c4c1f8200101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 230501933 1250 230500683 230500691
    0x9050403020a060c05090a0b0f0d1e06150c11030f1c0207090515011b06051503010c021507030b0303070c0303090e011d04083105011106040209060121 66
    0x4189507000c20028000b510031041403105081c010811100e82c05882c1959510240c01a410814124494001c1c42c4481c0b6440041c0d0a210f451400c02c000c80305d0b1000103c40d920100b9601c9142482640b00b10001b4100001080310940c10544009012060300d80c4003c0000765104404112038dc0c04002c0800b20b8801c810440d85800d803403918050540b03820b0b081640140c440c040300420011001e002d030741d00c529844000b44648000702401110408d07019610010380c80c05a0f040b01000c41e80500489200b80401c01d007821202e56103005060856441d0300c9036001315001013850b40c02c07424040141a40001445ca008079440300702c83c0000381144151b910040181c0141c0600004154104a44404907659a52480301d540c0e60754222030b17400802000748181c008050000900041c010a0103401420ba500071003a03000342d50061010108120317520016050054420200400c2da0706c103600c9010340c3c400d840941a1400c3c558040382110340082c2580d0305201480e4011100050241c08600c0c1842c13950100344 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 230503183 1250 230501933 230501941
    0x60f012111122a01030b010e0f01030c09090f0207030f02060f0415060509150a050a08030703081005041e0506120a0602030a020c071e12050d08060f03030a050904141e04020a0905 78
    0x61400f450316019035001c030b810004034000d0366000301c0150141c4e08000d0301580c401c0c0d0a42c0011801841255410000e02c0181800031600000c1c61003000003d51321000d0040e641d01d00390401900c149061801c200071544400100455003040158071500300344e10041128946407010780010107444903410868010b2986030420105070b001c07081a0040c0d06040c0c4448100c20707114010b000301da0819009503040c80d8001c00143e0002441007009580c0070300e6005400d001c3c1030701c640005003a2421180003860040c01210280c0c0d05224030f201d11030304046d04942e20b4036280c0c1105029034850000c140040c0c138066000c40011070b224134039011a4152003808050b2815140c0b99081120b074031180e800700f040315507011100840c00b600c4146080c1310700d85d0400000c001d101c0080c3d00490300d40d074005100a4108c8a8810100c800d902d00300083c050800c8a41c44094541080c001444219040c81d004000203144c00340910060b0f503944007008146060009401c102562203002081d0041c905074003020666103000100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 230504433 1250 230503183 230503243
    0x5280c09121b060f02030f07030c0c03030302031504020a090e0603010204050603010308030f0702010b1804050a0b01081510050d12031e0603030f021c050c070305060f01211112 77
    0x114100b841e00034480c0d564240c0f10081240c030141a0101c0f0070159100b04406400c84480e1000703004503c0c4a4034006104461540e21500c0c1d06920b913104401094020041c0100c007100200304014190081d5001c40c240380511100401c2c0400c240b0038403c9001400e00450000c3c0c4080d0102c90161401a001c940e0300d503524503152005500849107500d4250040002c07070601c034410300448480e0b0a00804441e1462030f003240b168020640500115400e00c180d2101600007450250300600905250000e44031100d000298030003121002000c0382040e18032024140155500c3d005507000068000103210340c180002201500100301c01c40540c8012005410b204840c06541d0700204190703031003959090303215043d94605aa80c0d48400c485041e01c1040600d400403c0e0303201328064000340300c80c02c044030b0f1529683c3d00e401e030a00b0001c1d550300141b281d0800062116100ad94082100d1880742c01c01610300d04502e031120007510000b08501c610608141850011074101000b01d600003035a00c201440d00c503008601a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 230505683 1250 230504433 230504453
    0xc110d05071a011d060103181101021b130506010c050718140610110a060608070303021203010b090105180405070206040204230417071703040605280c0912 68
    0x12540e15003910800300016420000b540c1c101c0c0e80c000c025030052062140d4820700130000070803041c105580c038407d8085800c00c000c2030f0403082c0c1c0100120760110116100090410000316a000c002031121a0411242d8503696088110018000e80c00611034680b4070040399038071544000600144200c10f00410005070401c604110100640400c1290940715186c20247c0300c1f0840d15030b42d02141c40d8800c402000e0003084100c40e211a4101035400c030260340da036000c040b22840e411125281e40051802e0040540402081055000f02c004043c2550f00d00940401d081c0705004005040040101c7c1007030386524400036032880204000e00500407807408240003540d941c0c04940c268031a5003848480d1122008070641c0035000c0300c41f400800c00f80d83d2a03803112501c02c5203081c0519108403080040300085000c1c412160040c84190b400e4950342c0c00c02d420b100080e964050010441c02c0a40700800182070b042c02600d4003150064840820348180882d8141c5420481d6403000c500d0324007800b5010100941844 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 230506933 1250 230505683 230505697
    0x1206070201050a06031a07050412060f05090a0c03170702040203070f02010b0f010203041e0b130305150f0601110a0501020f040302031209010504030b0406090f031205061e01030c110d05 81
    0x100801c82d60780d48a24103810303110707140301c00b4042c034040500c00f40c07201042d00328981d4041c0380742c20150f1410f13a8903622800e400701c104d001610016516240850040740c9406143c1d080103080c0000c0515124586814603040703040d2000070082c01500148072103034542e00045d81c04040e00180f0071034603490030304405890b0040e294070241c0154a0024000480d140c001121401c2c1c010607802942854100300240300c5100c0745014500701500b040500040304d2500e1001840c80ca00240d000d05501855841d00310300d08503880107044120011141048506520045100d030302201c24039000c800400818074040c10700ca2540d602a101c1d50001030300100505054000b0f000b1a8401e40498018910f01010422136000d0340407401c0c00107000708020404030b102c42841c190060b004a4000521110035911035400c035800072011004a24404444520301c03080d8030074594440004d49110303c0400c14aa40c4105661003031510505040e030741e064400c0d0b9584104400b41e074414a440c129104c2161484016200303800000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 230508183 1250 230506933 230506937
    0x10b2508180a03030801090f0609060902040f091a010c060b1002010608120408030a031e060f060909020c060c2a0a050f070803030103121218140109021c11120607 71
    0x20504540c24002118000c0f2a05907403444900e0b402c3c0b204010161000410003102c82e41c603800046094001c5103d850001d000304940140e8540c6411903c0110420646c04004002e1a0070142c6818903400c090b0800384007803d207801100d454151074900003e1041c401041d4200d1480d0880c1c0c02815015400141500c18010441e2040c045114045000e481140a09951a0018080000c1040c000e030003039842200c180d03240c013000b159611041c00c03c03682258010300701540c00031030070818103801c0794400c001303000c680700258a8501c00c02c191594801c0003070045041808001042880713070030b81c10b45076030b8044008811700030500200c944142c0d03241e02c0410141c2c2c19025030f503450412a500019080700b04c840010195045070700e562140e00c00b490301c070803030704c800d001d44011002c581c00d00714425001c1080c4140400201c610041c180204000c1800080f00c05c1a2f1400c40c100300540d5600e040ca0744441d0b040c0d0300b680001c84240c604502c1e080798504144e50404590741c0c10f008200d5000c98490b110760b0444d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 230509433 1250 230508183 230508217
    0xc1206060801111c0c020c1005030609010b0a17040809040c03061e0302030d0f170f090705032410080708030c0f0123090c0306010906090e010204030209010b2508 71
    0x8000f001010784201e41580328201d000024003442a01a6085440d6030603090041d10004040ea401040c0a007101d181c801c000584004104001c925117021820f024080554a941c20052401405048107401074130081020405200140402071680e00315614100007034028009415a004040d0240071030340603c6060001c650030074074104290344441411660000c0051040f140810802e890003000c060304942040005c0c0d02292421100e0b8210034003484806030580030515050428604003811a000644640c00c164542e644080c4611022501003001c0640c48a01d80c0f03c0315602903043c803480d1f00400070b0780100700000400c01d402002400310070b41841d0640e6030a284000d4414221840c401c5072008174005012000105035810f403019070310084c050102d540f044503040029241003c00d9008506040c1c40d004184002802070203150401401c00c8003c0d420f107400c607030000f00c0c126030500507150000c10104040c1215080100080150546a04101181c2141d0b0420030100e1340426102d540381c2c400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 230510683 1250 230509433 230509451
    0x20102041a0c0d08090111070c080d03060e0a1107290906040b01211b06110105090d0e01120f1a0d050604060507030608160305061614070c1206060801 66
    0x4001d045400242400700a8102c0c02d42c48141074074034140c040d050105a40d6030341034a814110008009004040c0610105100075240c00103040c07078a03900301440c404040c1407040030400e078504149004e400c20501c201c040354480d0011100004c41c001c844d009071022645928030900d524070004484090b50a810302c40103039031303100b804032580c550040d00c000344600d1400004002940d16004141c2d80040890304411120382d0988844044040a010104055241102c100565504444458543c10200d0700902c01d41c0f030603a41454580803007030002c00034041161900346690b13215901c040e40300c0003100c4003042014022211000200380c0301f000d801030015200083e0740a460008000710704194230038002d10455035655550806003502600b95000d058681501007900e217003c4c40083c10040704a50404040ca19509245113401000b6003040d0544101521804079640d20240d298611070f4141840b0741e42c0c001a00e002d28104555500480c0456182c01107902000717079540010040740c2c6010024020b20034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 230511933 1250 230510683 230510729
    0x2040c11010501032a0f050f130507110d09080714060c031204020a06030b060a140412060915090b040f0809090106030b0a06033c1404140a0f110d0503040602010204 72
    0x51700e03000e5080800030381601000135180c02d4826110f051006825283c41c501c14200d020103031039054500c0700105074042d0f403260341a241003000d034002291074542180224640601161285550302035400c424180d0300408a440e283c06046480281725901140d50322241403040f414424001d0740c0480c0302d15000c40300043d10601c02e014403260814002c0c003247c58a016003805071401c0040e0740c072000c41c418040c0f200203280c0420310440c0091501410001c82d12100a2403d5205040c40e86901d65580d460200048045842c610829078001d40c01803100d4440800303800d0160141c068420303102d074007420000001c1085070b455042140d007804d066460303208440d01c1c1c403800d0702035031800520800101401c0006181c03521f1181405003c40003c1d08009c94407005005030b00d41952401e440070703296002d10310188003c00000311202c0c00b0082c0b2140c0a03112043c0b856031454200700e600d4001070f040101203000c800c0f181e5a00c80c240349040354000101d0340c0d01c0350b0328000030b4080c0d0040d114a0102081c1d6076143e0f642d682c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 230513183 1250 230511933 230512013
    0xc03080a02040b0a050304021f02070303090b070b0c07030e0a0312031d0c0f0a05060301090b0a0b1206060c0c0d0b011e050f04020a1b110a05010201021602040c1101050103 75
    0x50b1043c40f1240c200603a070300040b0340c640c10040059a021152142c1c105540207042c0120b0315030305003580030f400c103541503080203402c1c0403007a030045641c0c48041054001041081c882150006031880d5441d540720201c6c01c04842c2042c14a160741e92080246000004004e905e044c0400d1501c0365031410b01c050392420f212990804000d0245c80da8a4000384582e207800c5c1f07442d0000d1030103040001c0049200365100c0010844941090b0024000e00b507031005003c04138a42140614001c00241c1c00d051716082140094402400028020700d004000200302a20414410710248070b0200015114121495481c01d1010b0005801c0c80350312200324291402000101d2840310b00c83c10303140023030701c0000c7e80134840c400d0000a51002c4208020402005061800d02000060310102103010341c06913000c0c0c10201041190480d1250321460540e80704114264403111401d1281c007240b901140c0000d0324151403035060f201d40d103038003408130a10351030040048100207404009043c201c0101680910900e60b031440c07101d9007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 230514433 1250 230513183 230513189
    0x50f010516050c0c09060d1502040303090803180112090609110f0301060b071203110304080405090a050f0a0903030f0c0809010b060c100e07091b1403190b04020f0a0c03080a0204 78
    0x6908070700c002c1c130034074100100c166402c00d101030099191003140792034208100140000c3c011096400150403c00e15070f0140d1040050020f8401031403030855000b01d00d030401c801a6040070f05000c061300000b807622810768401c0780040e4100d60305116101c0249840200398102035491441207903c00440091810148078035000d940821406c80c2c81e00300551034804082a0060301c800405490b03420071624540c3c0640514000c070b100703a20070340c2c4441c00d00041000000c00200410030440c60842006140400361b04c4480c2c000010b604001903205060170101c014042d0325000741c3c0c8003801c6c14903402c14590b108018901c9806583c0c0200b203586640c000b0842d6505c1082c2d001034456001450078008402d0760b5100300d08000d140e0b801c60780c0c850790b282100001d4446400c445203030440d9040101f501517810585a01c2c4044030642e0300c52451400300402d080080c041040e100d00325a6a0a4813a13841c1c03070300ea04540c203105107055295214608103400030401103100d00220f0020b08802e020442c001418000c1c5d03815 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 230515683 1250 230514433 230514457
    0x90311030a050403030c0f0f081c02030c040501050706060b03180115080309011215091e110a0309020a0e040804030c0e2202190807080d110c0913050f01051605 70
    0x60140741d45c07022a01c03034030300305415038004140352001c00004039010259040036216542280e100c070800ca14529a0008003280d082e8412700410822404142440440f000d0b02d80c2424110346401d4603041c010020007250300014020728001090104000250401da00b03183c40040003408401c0c0450b88641a10340d041c0b00d406541d62003405801055030203140044c0040240c501c0000305103d9615401d41c42d100260b00c6213000390364419410040c40205c80b40100160101007090009150301e420703080c0d6510540001c4410141d031400240c0071543c1e0300901400401b040300c9680eaa60078242481501c5030b10501c400c40b4161245c0300300191207516403500700d21408000605140c8424803200f61200041003407001c03603101011000c02c104001e0281414009411803030700800c0c01c4c03803c115405190062451010003404240a010804a0740000d149071400030142c6a0f10f14580307658031100a5041039890041150007400e000d040e50030015407109101d680414444210714842c6c840c00d68540c03056081d1a64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 230516933 1250 230515683 230515687
    0xf0a0b0103030c05030d06090218010206060a1a220608070807090302040507050408030304060c0f050705030d0b01021905060708010b091f0509270105041b080604020d0c03090311030a05 81
    0x20a006628501c9000c0c010401d0f81d141c601b90070705842c101d0b0f240b500300c44d041c180d01080028008140e880c1c47d821a0000b03000510450030480c0004007808201e200da06150401c4000b060395401030b0b8016100300c000c52004441e00120107d40181418440d401104000341041700081c003168401c3c1e041c0f0f4015075032521007142c04c0b4103503020b01002d00b070020581010702c48100400225100104021840342d4001e94000580d1404058014050161007400c6e000f0000248220800316030f01100b2519461900701c030004091081e01c0060b41403240700c04484050329803540342c04040c0440451807900c03070341050fa07031041c00d40c0e02d42c0040c0000780940041190040442d961102c0007081020700076661a1550410506016200c1b0024284030b04102d90303404d0304002281d500000f03401c92086103000d000700b00c80a0141034007908220300740803c039242c8001000318401c040741480d2641e60440d81d01d104940030030320a0444110001c3c028240043c8202d00184030400c03074295003c4084291409101980d486034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 230518183 1250 230516933 230516939
    0xc0106290301050d1416060c060b06030c2d0f0703120207080910030f051509010806040206031b07020604140f0307060806010309170a09241b080714010209030f0a0b01 73
    0x2c9400c5410004085403140a419036140000e0340442c6e001081b05170b85071140c0006a1500030b0070385800680c1700e40240414414403e5181c0f1400c141c40340e92281c0008602c0249500f4111140c414080801c00c0c5131110024041c2004005e44004258042c003d880d0610a038084103150000c034491b050000d031549100b4011101c05150080780c5a044103020320300455104905032040c4101c1c2c50a0394440305030510b840004203213003042c0008a00421560001d040c407481c0039004900c2d54440103001407120040d40c0b184140c8400d8400c19581c4807600035007501e48903501c1c0c0c1d00c141c41c0380c032050780c0052103030380300025580151500049110030340b001a9100d0700140c030f44030015406401200300444a00c030640d80c490f003400386104040c00e0300c0f024540d1a0348400745042c40d031199444d0100503030300400e08000389400410340c1080108002503010840c0304409003141c00d0a2401d0300a9030802481c00b90208014000e0610540241584203c21029208020001010280e444402da10000c20f00c0002c18010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 230519433 1250 230518183 230518193
    0x1505030402010507030e101d15031b0d0e010b010318050d030203101805070f0c08030402090604020d02031e070c0309050405060a0503030a0206040b100305061602030c0106290301050d 80
    0x10b080d446200342001054884a00e00190710200841f0200300000c03d00245800c1e2076030b4001d0740408940055034116030322108586801c0c5c55100c02402a44600c005c121100c10a460240858100d03208298040006140c002c2c00746010705078180c606130008c1d04080407400c907084818103d1803800e0b032140040c4a035500c640320941c06500002d03c010905004000b000900641124544103681e541c40d50015092a054001525110449107040c0c01c1049030806140004d4034107003269005501140c03445482c0d0b0740c5400082c081e2007100f201614990010046c4590140594003007040000001401007840c0e944c2c4408480f041d43c6204c0c05000640404001c02003400c2650025030000805000c085900d0303207540100c0e01c3d42e030000015000581c04042080140448088819004985c101307060040078035584480350340b21300141003040040c1d02c0e1340c05160000d00800840341c10041c0c01c002840010f684114150344014140720f0009000703a80b01c007068030450b900b01204c0c140c80d4010451805c00842e51a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 230520683 1250 230519433 230519437
    0x903070201030b12030a05030405010e0a020604121106041d15031504140f0d09060302180f010c060c03020406080a0c170c120c090f0a03050c040f020906070303090c15050304020105 79
    0x55000f126012940500404c03d000070090500c040e26940c1e62418145004da084802140f442d500380d800500900340182d03604400c80b411a141564041d540c1002814141600d200903070364aa80140c000500092010611a40f202c003556881c1c10f0b108950303505400d0b542000346071119a545908280b91405c00040ea07806441d800030300540c842c40c40d4014a158107031900307400e0388c3c51159070f601c50a6412043c0d0350107030410012b82a50716065080458104070a43d243e10341d048094450200c1c104030f8141a403080f4030445403240c0018050205800178070000e4029401401418001580040010100c0800e401240001107040e40c0703062900c0e026074441265a02d01500260721100204019010040c0ca03420044c001c8a840c51a1691036013a001006030004035100c0403405440c0c60704040002c2000803451010a01040d01c021800f05200c0b005240203124002c00154060030200f1881c06144e03040c1d111410680c4510030505195480303c2101441c44203240207540012400c0000500552003400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 230521933 1250 230520683 230520701
    0x604120c03060f0e06160807320c070905011805180d0e010e09070923030102040e04020109080703120e0117040b1b041202040b0a0f0b0c070b03090307020103 69
    0x411003035420748a545600070340d01c201c2803820825480302440c200c0208140b200300d8101138000c8060103c1e9501c13030070141c8a1140101040c0031320000096010801e152a43e203c41c4082c3e04616660800000b403003107460300e8000d550006403a100300c43e4040748c0c44440d44034090507240100d40b059580c21554040303001034540106428005410342100b1131889004005400b20b94030903071076805025000f18001040c038010395507602d200711010000d20031169007103201c03501510800c1d074003038035442c80b00304111880e5031240b090642c1640c40050001000c0d884000e101d40264400d9030341402444e525101240d4400c00d41c0405440d90032000c105144550081c00300c01d00705001030410088004040710070b1071041c1e508a0382550b00b400701004111000d6885c40345698550407d45080341094103102c489241700c0d0503030100034051a50341d80450107950310303405580024040c50b0200c4a49031740758804000c5680201c1c0005016100c2d408001c02c941ca4110705403441030030f02c5401582083c13a02c3e0011009425454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 230523183 1250 230521933 230521943
    0x110f150904090803090f01050a0902090a150f180e0d0801060c030c060908030f0a022a01022a0f07050f210303070c031d150711030d0c0203010f0b060412 67
    0x1002500000d000c10010318031500485c00640b0005100900d042d094500041048075002c0c90000b2400c016036410b5410758100741c0441e0001a48205901500004155904070111a140081c07000912000c40640400710582001e0140f040d514480c803825540e174612013000010407812001400528441d070112207005000380b400700d40c8112030b516190111060710900b0b4444800010130001c08800030b0410703580013800780408614110140c0003001444080050001909004400c116000c0209405444461000d00384920f18011589030317071070700381802d420303240a41d005401e03c58401d040b01003008070403071340050800d1b5440c0402c0030030007500021100ca00c02c804295070349500e141c21004c001943c42000c0c19218a01102c001e400c1c05002e28102c0415001115600030444000781c07904a0014100301c80c1800a54850544e8075141c8002c030900c03002e40385c040c880c0e015800303607050f0b0180603003010314001e030b000300000c0700c5070038a24040c1d401401266030800c40c00c12082110f81c20b90050540c42d24012 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 230524433 1250 230523183 230523191
    0x4050406150f0f0504180501060f0e031b040e01230a1104060305070c050a1214030c0406050306030a051902011e200c03070308030a060509011d0a0b1c110f150904 71
    0x61b0302e409546560708203000c84026501c2006020094124044042c80d83c610b0a05400c1120203100190f6124130340701c28052880114040c119203512aa040407001400c844002d00840c0030000c20008904000c01401001d183c0c9840440c0d054401c922400c0780d168030303000d100d41c41d0906020301036000e020040c0207913041028001240020410030b00100c890b0313038452410717181c1000400c0e10042c007800011840100f4000200140942e004003881182c04407902d50402503141ea85480019042c82070481019000d40a0030f11000518602810a007161754401d8940006c0d2040d2064600c0e9292080d4498a010031000e00c1050700000e00c80010000900712001180c10b0840c1c0100881e040018690040301c411401106124500155018190143c80e041d17400401c190302d44010240c0050b401740c5011613070310080c000302d010b014554002952620010344504480310281001da034518075004c0054500c81d801c03401210075481c01d041020054240189038918441481e1a280c64603803061000c140d0240d65 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 230525683 1250 230524433 230524439
    0xc2001090e150a061704020d03050408032d070b0424020a030b030c0d0c091503061404020102070f060509130e1207050d050a1706010c1704050406150f0f0504 69
    0x34907031002c0c0b0400c03106070110500709410007404042a4540c1024061000d5079038214442c1c2042280c5a5021342c040380d5000842d01d6500302920f141c0301d80d811a0101e4000040c080000d100603040450f040002d0034040e840380d0300c001c10090005d0184010040c0100d442d0400f01d0046580b00c0d01140c40428281c1c011800c0b1203612840300101e900000110300441d840d98150401454240004041e140081d21050103c54031555540351038410b0f401405111a51074000c01c580d407580c408000301a6034802e50411200c0160101d10320600c82c01c0303030101d0040c4100c5202040340a0910f0010013203ca540d00e03000d0610000c0800c00c481c0c41010503500e80d1aaa03100c000050500c400c2100070313681c8600d0000c950ba5009a42000e50501030700159001c2801300410803800e04907070004040c55908040b4109064689965004a60307911a048000d000703600c0705604140819201d000520403110100d4042110a07601e001da1000946039036400008200c841080c403448030301454011021907a1442d0903441e040d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 230526933 1250 230525683 230525699
    0x13050106030b030c03061501110c0a060504240905060a050702100e010f0504120f110d0b0115110d03090c0e010e01090b06130303110717060709060c200109 68
    0x990000c80001d0701c500384480740c0e082c00c0c070891801c80c0c1d013070b0041c1005207003402000f000540d41521071410081003881e4a00034210a00072044c2030000101b81060b0f6566440d4000c1c81504940104481e403030ba10405441044442c04100d07824072000c1d1281c0107018900010030100d5000340f022102401410408480107940e0b103e004001c80483e5203400e100361048a00040102c01040040c00030b22004010030311406034900c0d403052000340d024501c00032400f0b43e460940300031040340209a800c10107120102d020809510301032030580c0c00070b4101d00c07800100c0c1a411950505070305100203d98004c2c0f076092048030310070303006902c3e2107002c4c1500000c000c1c2d8800c80d4800b07514090744420702e001d80100040c040d0f211503024203508440b040394140c5c2843e03c55106103c1c4440d1900c401824007030390640000d0700c0342d014020320004100d000802c050b0808000c5046864000499070384001034001030010490712b003d507151802190304841f21114560704032045c210240f450800003810710503c8000040d00320 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 230528183 1250 230526933 230526941
    0x306050a050403030e03040e011509080105091c0e010c020d02031f0f1503150903140703050403060b010807081323010c020607110a08090d05070b03010303020c0f060901050913 77
    0x40c00400000c10303180c58100141201c0b013440400300346400c03c0108011407010054918103407000014561114041c100090340c9250042d4440200e41d4208020060454000b140d401c1c40c0c481401441410b04842a008484440030b4003091408030346089440302c0981401080d03140d1503440503045903d04240074155080344258210044580ba4946503040d481146900a06103109805c82809000070308503500d0031848401c0040b034000c000e0341c503071290040c94450000c01c1a41d03000d205480b581c651084c180105180d1041c0030640d10981001d1991840754420540b5900c240e09999880b02c550300c45500000c10002c0b640000c2c0d0f5210024450b10944134084250a1003aa40e2400002284a142200642000030003400340d014000300e4102d066100e04d002c90740c61241a03111301c146590310798010000f40710080c0114058200d2103244e44c0424440740090045040e81d010b0b4007269135441192040101001c0362203a4140c010400380020a41540144040c00800800801410a0042c4801044e00312 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 230529433 1250 230528183 230528191
    0x4030503070b19060f090c020106090c09051e0619090302040606050418090506060609010201150605121602030d020708090d0503040f0801050603030301061103210f010501030e0c1009030605 83
    0xa2071000b420b0054103200c5001840e200441e110042c80458036140c0c403045403400318440d415405803030b515983c9109200390710120150030708030341c10443e0064201e401042040580101d9005880169038990600c1480d00b2004003130400031310051400c01c0c0802d0303409030100c2c940900320520121314404001643c41e401141c02a28036541c0f0942c0b600c0c03411340c2944041103000d22141c821031070609480041840400c0c007035444a07080e124982c1d182450f0300102e00400100300544414004440042a0641d12000906200c0c0c0003103042c0c0d04075180e807100810303945140448100560310402110b0501c182680240900034040c141c440e040442940c003042c246012100c049403281c10002e03007030180e250515202e0340030b04103000c001c108500d00203020a6680c0f006004502c28003080014980b003d00c420400c40361040004440702d6031035030b0303010701e07540e41e10b03200b0f80301a80c444103545d00118480d4881d01ca6040740341c0707400303000707040910116003031041210f6210400c20030045c05000100c04594140140c030b000e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 230530683 1250 230529433 230529443
    0x70f0b0a020706060605030403090905180102070b0402011814040914010f0c020115051509040209060703030f0c0f0c0b150d0b04050c040b0a0306020c150906060a060201020a091a0403050307 83
    0x107144050310b0b02c00200d41d1303590030680c01c1c0001402808040b0340c1c0444001e040d15001100081c01d6128043c03c15030003d64151503805540c0000f03020350410260f1450b4074004c920030b0b00c0b6002c1140049505840c2008940074110035141382402c03015003490603030045c1c003007517015140603013010798441001820340303106c2c40d1403900807a21504118080c1da0709210381030070715000115514400342020001014580c5020000e501403c020a510002e9542c990446d100b128004001642d14600b0b441d000d0083d01a450700c0c0015030f894030070b02002941c0100e2501091904035560013410b450707290b4400d1200e44015180080b1101240748500c0f00d9203a071640b1802140c050400c2a9203850035203403452910b060700203090301583c100000d0781d0140d100c040c840300a582d03000402607110600c540049241502c201c0c507041c0c4120485044c003003104d0300030602c07a000304000c3c0c540702500e64807400c09134282c6c0716488125000a00d00c210400c101040e0801d80ea2003506002001c5281c00e940707844542c03441d00f10b0001521 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 230531933 1250 230530683 230530687
    0x303020309090106080c0a0c0611031311010e060304020d1406190e0f030405150f0d02070302150c0405010f0509030102030115180608040b13020907030f0c0320070f0b0a02 75
    0x10500d0b00c05003035070043c0b90500c1e0125240c03400c41d1031054a0300600e8205010b001c2d00700d0b400c0c0100640c540281c142c0d15074080206840b03203080c1c1044019500380d014140c1d44c0038051502000d413544034400f030811806015000e207245888950078010082e513030000507201c2c88840d02000c01c05583c24801540914407030702100d12a4401c901200c81100c400b10101300740740c2d10000740902c0380d0001200384c40807190110380c145000c140d41e00c289140751144500d4202002800144240c00c8001ca502800d54140a0b5084418150000850001d550030540d00704280e103c1c02e001c01c000744d40c4140d005902c020740070301d04103003031801c45008642640c000380c00191294040079102d5200703680c80000c6211806042070031010281c0380007409403000313101600113010f50b0341007400618400125960007807016809005070301c85244c0090f00400400c000d207001c901160402d800003c45034803d026486404608842c00500b1a04003041c04404e43d206c910308480c44180c80c207800021031009800b2520034a4000005070b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 230533183 1250 230531933 230531947
    0x110102010b01020f0627010203071701090504030903080901030f02131d040c0b03150d0c0602010501140a0e06030c0901092a020c280605180f0105030c07030306050a03030203 76
    0x60309603a901601541150702441c002082c500c00014143e41000070410f00c0d03544e548080168003844014035154100790340c000001c0c0001c081d0720080000d4941c40c814000c41541e40c0300c0001c101511820355010703000664103030b014004100c0140092444150505000581d09003081c02181a60000019444441d0340002c1c01c03c0407031100000c000c640310190055080b0f07407800b580e509020201500998821080110004001c0d061001c01da060200009010a2000813285071039015013146008000c0113508140000409412031800d107100c0041c01000400d20a050107080301c41c0c540e000304035075031520403401c0c0c1c02480d40300c116803d4042c1209e4070010609034117031041340490007112400c0c2001c01820b40c25002109502145940f58080101c551000248413800400c800f0091a1f5818540b50a41440061816000303402041c054000903044442d03101208204643c400700002424040781003080040d1031821035400500482d486400d00192444c0c03500d0120740181c03240c0d0422005a0b00c006610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 230534433 1250 230533183 230533187
    0x1306080402030f010c050a08060d0b040605151203043c0303110309100e1302030a020a1d0904150f1b020f0604030e060a020a17190e030c1e0d1101 64
    0x400f03541e40340400240035841c1c3e00c0000400c1445400f24400400030000701103102999022551364840c1c0e005400b00c5400d0a250911350010801034804410a003440c080710b0328117090030303a00030b01400109006181014541960003802441d4a420324005844241d84541d0700c84001396942c0c00d40074100b40c0d8214803821468050709003920142038412661043c440320617640e5603c900350358801c200d4031f082c0c0e004500c0003002c190043d01310b04208039143d0010080007080111a0702400c0c0c50101c0356251040c0a01d03540d0107140c5000491081c680200341e03c1d00140100d000d52550455458007910002a144001c100000845100b1154a20382500010310145c0c216810440c0b036461801d50703c0540a1401c069402030722040280103502e0040030081209901030f03001380450041990003401c6c00d0454601c0c0440202d4950040072590350305101d0b415103600c00d0f4840c005810343c501010703008141d99041201003120750701a120b05074112440601c10454030f0f4a4610006504511907151101801d50030000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 230535683 1250 230534433 230534443
    0x3060d110901090b2d13022115090402100807090816050f010509130e0c0307080106060813110904020411070302060604051b090910030c0f03062018010203130608040203 74
    0x4500103450364107035a10340c0071000669100c01740104a035400c9645890043d8030300a8010400c101d0000c10b02c0c5280c007080107050300d032006c1c8150040225801031251000c1004072010090300c010b50000001c43c5541d8030a4045c446480c0c05c2001f034200040e4040d40c64a045151281d030100070b1150403200001003140d82480d907003001d002842400c216041c0b29105010a02c4000104140003c40d42c0316616040d50280034480f0001c1c0b40c0c0e01030151516036450b44030403406003413507201d00c40002c1e803004000f07100d01e50040d80030300c080d079408014038a5540000c01048440f500292050303911a030f440542101000912006055440c802e80141c0440d1509074200b10881d1802011b10a40021b442c42d00f14055044070100c5040c81011550400207445503007105140c038000350801807032004c601c5008940202d48041820031a803045405014001c2c0c00380203240c1d0075094400c075030000345041c0400c002e05c0d40004410140040d0605c1202c1c1062041d195036040c441c01580f0810214800c5c0e42400294102440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 230536933 1250 230535683 230535709
    0x20901020a02030607110105060a0605091306090207051f110406030506060f04032a0503030d0203130602130305060a150608070309050d110f0109030917010e030a08070e0a050603060d110901090b 85
    0x3d42c58252807800c030f4050160f100f01126180b01d80b0700b0603024184501c0ec0c0c2c0c0004080c0800e5081192502101c0c40c0c015619800090719000001b0100480e88400406000d0700309814010700101d81440d10b07200040c1c0192034042e008540c000d50522061080030300e400050401940a00f940480c0541007040005070310750400400b52013544241000d001ca518004101c486034015001c0050352507840721440c3c800d98025203070003081c80d40005401c024800b0540041c1c41900e001f0340035549640c480503003001c2280d0041411518cc01c5a190b004c000ca06e0141005a07072240c03031400e02140e21080c0c0e940e0300b41044c5051440307801003845404040610b82c000c100311201980c200c0300030019400f9603100502030742e0182c0320b0074040141030f48501c06904029085010181e0300001280d4031342c1c0d512500a00961022a4070b0400502810b220403450f10f0040d0011084400140145165448680505c40e101890314420360702c0c110781c03204001c0c00e915111005030080c402c07418001907050b85641008010840c1e03c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 230538183 1250 230536933 230536939
    0x71215090b18070f050906040303021f1a010e1c030315050a0b16020616030f031a0a031401090c080303060a08160909420e0a06020901020a0203060711010506 69
    0x24681d0b499042070312030305900a621410b00005901404404907114462816442e400c28000700d0000201030f0005520206011580b8060a00320a0414400205ea0281c40364001440d010030301007481e9405200140050507019090107610004540502c5020344980421000a46c1c1c45040004012034400039402405003140c142e0741d2186400e0700620f542c01801500e80c1c81944090040c0110365802049170220941c48a112641e1555401e010380024170801c2c0c0c0d071000c6810718040001c0203240851542c1c4c01c11b001480c0f115030900355290b20a008510743c0c01c11600c2d65031074400780e0104071011aa04000c0ca140380041d5920b251080a00c02403e41c01c0d40025000e52054440351100220480320030250341c203480000401d45a80e08000c403003860281c0900000807070840b811900001581d030781c100f0000c00c85d5450030100000319004001c03a24170900800c01e94002d900344030f00103103141e00200310b8900140704850760200c05400190030548150f403120301082105505003140082802090b42c030107004c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 230539433 1250 230538183 230538199
    0xf060f0c08010312091518050a180f0f020c03030405010f0e0d0e03031e0d15080304060c050c0402030112061808070605180d020109021521071215090b 66
    0x440d2024080d1081030000038881d00c904900c0c5200365200f0743c00d5200500d444000c40105040004015144511040100940e00200c2c0008038580c2010b5940038101c1c0c43c0071400c40340c1070005600030701c010103a41c2c080360031450300d03581d10219290341400a48002038924021756624209850194210788204405400050070141c2d000c00c01d0388040fa240701269003a042c521410304c440030012f400c612418407080e140880e081d0103a280c07481c59101409480764841d00c2084030b900186031030b000f510214481d1034542d600c00c100130303c00c2c0c9100e03003880f5038031301d214404a450003688040018240d803c241c1002d919a81c0b101e80b1481400b80c1070003595400c50400f000c8030601c0134542c40300d01c51403181c41c5001e48066100c4010a040b000b80d8103444451001e41030680b00c2d40f00d48044000c9c040c2200b01000d9125200e00350341d4455402c2040100e0700d04000a050013041240303400720195540ea0010310100500c065107101c040794072468002c080886040d10324101e00641041081002c0301c15a03032903a4018890703 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 230540683 1250 230539433 230539451
    0x1406090907150507060f091a09030a0302090f090112150204260a05060405060612070b0711190306020909010e06010c02060903011d030c0d02030705070315180f060f 72
    0x30104060040d20304509900c010a0807814041e2964401d1400c01802540b9101048000311500d62250200d2403081101080d00d00800c418034810203810703184075556810802139844417600a42c02080030b60b1028040f03918080b1440001001044264400421649503403100020442d0b000c0150000900b00e10b021070070241481e090300e40c44202c2050442c4589898401004507003410040000001d50241c11220bc070302d4036260a98903008242d54660040020710249043d541c008503041c0140c443c16101b40b41041059210b0190b58010081d12030f400145034403030440c0301508204c40a02840c015200540d80e501c0600c1403000c0a64140d12190000238102e0600c0256a4440c4940e802d00e901200d045482d0301c0c00c0c1c00080d00401000c0c9651500742d1505040742c090b954080042d00a00e4440801d4070241e60891105a0f26481200801003454003c00810320000e101303001801025000c2030300000350301448200c0b404900320525401e4903801025650081008180c1c05056045500b80b60f00b03020ba402c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 230541933 1250 230540683 230540701
    0x417070f0302040515031b0f0a0524040807080601050f010807080a0509010219120b01030e07090c02030f030124020705011209170f030901060b0f0703050a090b0d140609 74
    0x10080c003000f0700c00c58a40c800700702a403860048a400e004002000c2e075407500c2c1409a465481c3e04038107401c81c040c0080201151040c5000d0050a0881d00083d2901e081d80c2242028034031a28024070842003c0c14041c0000709162404100400190070004002c28a650403c0c0c20000050f504034885c604004402c001c110117540c5c440004c581203410104089117644400410318064020302d406001000009000c0310f0989600500042003202d031041d081100e00000801181924900554100d80e64000070080058024990008003403811902c1501e08105101301d800031144e0084e4002c080c14040182402a004070078142c00d500240c0383c4c0018485035203000d0010305030000c8055606c03852a81c887e803606c1030142d1072803c3d43c01c5100800200755942e0040c0c1d00c2003d640c009541e14046176117050030209192a8400403a0745405203c10254148039140da4103c546500400e2242e04109070300d040040c1c01d0300e041000d02000902c1020101d1442d4403d60780742c03070100006060601c03801c881001d22148071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 230543183 1250 230541933 230541959
    0x506041a0f0c061806041e0302010b1e0f0a0308031b0d0501030b011701050708070c080c0a0f14060105150a20071505090d030509190b071109360604050102041707 71
    0x7c000074129044000e0800382c0c018121030203c141c000c3c08198000c01680300b280d00b0040060000c65840300710760038a000340000700d0214000142000c2040011aa80000829001c99000105c0034001d151004448140003074800a0b8021500003403000e00502c80c505084045140001c0c24800811080c075040c080100740c11070240a030018425140c0041d000e001141c0c0c12100c00101d40e42c11504070108615100c0c04100700700f00190307150000030995860324000400d80a040b14002440e50100b075107480001d0340c282e44501501001c0c040e490810450010400507405440000a00075056062801409004e011026032815080010420a01695940d02c4002441d01ea800d8074205442d50814070204640f03107440703c0e4851220306c106000107440d42000000703040305840341c48203500c200300d00018002802d00c1074541d005048126590444c0c0070b000c80e4040c501807624540728080c0c001001c481c036070034541d09031401d89540c3d4000030280314103d0148400c0325405140d0004044040c42c10309000804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 230544433 1250 230543183 230543213
    0x402010816051b03030411030304030309060302160f0b060f03213403090f050112050a060909051605030607022e061806060305010506041a0f0c06180604 67
    0xd141411a03088492180050303c001070381d81c0d054000c509005441e0340c1e659405c21181116807040010f4001d1082c10040291022039a064640d204000e0030040194044d420040c2003148400e51100c104d804103002c0d070b060341c00490080840380042c2c14010b0031300c030781c50708042480740c001d40c45030351002ca42d000040181e480000100c12525142c0c2d01ca1510301d000d042100341c0050301c60300301c950f211000d20411010307892443d119441d007080340381c0d4800d41c1207000d40140c8200d40c0441e0320003100c880f640c03401750050390f401039200000091664071030061108480e00701c1d4058540c1c1d8440750146a03403100001e04c00d000b80c5800c034000c0100d8940014000d565081c0d00390500c1ca40600c1900f400e407134909891104c0080c0408442c107201d400c0d190341d4520240390415031032450003810090000b4105001e480b8550603140003900d140e2400d81042c1d0350704000b00030300022800941c0100300202e410040d001c00740000d5255030f800b401ea9414000b2040c80100e40c4440021140c3e00704105110004049141c48280d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 230545683 1250 230544433 230544451
    0x3040302040e21040609061404031203060305011a0405310507030b0a0e010f090302070603180b0a0903020708010506130c1101050403051b160909020d050d020703030809010504020108 80
    0x20010304a0810b08010125110f0000c108003901c40e183d10110040150050b200c040e9108900d041c0d80b11401c0b40d038080300d442401038015040000b0310200764641480340e05420103050100d095a43e9586090031240d01c0100c54030b00ca001c252038009289014096142c2280e410748141040c0c04036600000551060201a0400b0314030701514001005000e10540700150b070400d08440562034200704040207000311100c110515480d00b140611000194401d2070403c3e601940141030150400d40150020f00e4901000300c00c0b0b40f4049003c10000d00e4203041c0620561516501158400f0076280c00780c604a25604655443d9040204204c042e855103078814200103205d0318042104402660207483c0c041c54424103440550070101004285500700d0010510f504019a105d80c40c640c1c04070800307403140c4e501d1800003044101c20b0000c001c2c40c0e400b81c100541c42c9000030041c100400c40c1d43c5e90185083c580c1150480540c2000b44100141178014206c1640807420500a110134503059000802d0200010a000360b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 230546933 1250 230545683 230545691
    0x605090f06060c070f091515080402060a02070e09030c150420040609140103140307030206191515170c07032102160215120c0702032103070810080304030204 69
    0xd03c0890400403000102024141c0b201c80c1070705c90050602400003691903034006e030031a01002800300c02c1c840c241e0500c840310740d80c0c549aa454913404c1260540c484902e81046100e801300110710100740150190060244070300655a482204002c0381c00c181003801d810740b00214000400001ca0740c1c000075560015100084e50810b0400680001e00420302074101d4003525182c042c3d450440a02074490606a90081e003081c110f11181c0e80b4520b60f01d200b202ca006006030000d5000c00d0080c507045446c0c050a802150b00810090320301080104101d200f540044011a850182a03074087d4219108225610035480010150300d0b028001000c244191800203041000300c0001d100c08060b00304000460080c824400d656500046184040d0321825140aa10440b038108807003a02d20721400484002507403801210200f507580096a294603044000c060340c0602070742807006845007001c140400000c801510054480c00c00c2c81000304401001015400025020101400b9030365000040e501100d604450100b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 230548183 1250 230546933 230546947
    0x1504050a121514190501060c0303020c0705100c1119030f020d02130b0f090402010206071b02040c03061701090b06060f070803091c0305040209010b0a030e0601060806040605090f0606 80
    0x844250b160301000a60070725104010700c1040109007a1402078281c6040c1180d88910740c100e01c811140288140d0700840d41c00701d60600042e009402501e51644640300340e41c031490f0b8620100380001c180340014000103030042e107010200284400c200714000416a80c80350340080c0d641e4007208801d11400080d00c0c1e074024070030f540219604c41500e0160f07030398050400d1006082050050010740300b059111031141c040c00e0691607560403e03a084600c01c6030160300803c590b4440740401c0d11079083c054201e85c108075041c18001d000d40c40324000c0c10107001083d50005101407505e01480e05c0c1d100860944519641000051800309001c19000390300700e03204441c01951603480f040b5035940ca103d030410041482e0f1001c4100120f4100104da03180000480180c03403a81408801c6041b4120342c2d0484009600c001c20000500051100c200034141e40040ea00300000c1d140b940141c2035151074401d81c080b43c000380490040280c581454020302e00100019038007001e81c1d05001d200348450010042c00140034000204400b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 230549433 1250 230548183 230548193
    0x30b22020d060207110406090c02241602120a0e0a0b0702030d110a1b1a0f030103030c29040c1a090402031b131a030112020d02010207231504050a12 65
    0x341000343c5c4000c10802c1265580d0101a000c0c091018440d0058000e1178a072810480d11580205012031017000c9019031a510a5054014810151007800031031143d592042d891800000007400021709980700c402c003070034240007003100400c02600031139803c00713041c014180140c40001c0d07420303044125410b082e03a03c015807002083c0740503400b5401400121411141c4030440006c10044019115100e2401500e01c00d00c1c10004507500c54504081407444007000100301081c890502c412006116080200d513182000c7c0272064100044003401c1aa4006a800e00c0100207803800800001d294074060450007940580c0000f017140100003da90185070008001071030803503100c100200070402c0002954540a0305490030703100d00d02c5402403103d118040361040e03964803028019030b81280c600d0031031000410100c2d8241300504034407010480c198401c0600c00305a08400f4400034081d4004404100c0000e00004c01b08052003d0810b403130141c0101c100014071031038603446c03200020380e41144100c408602c2c0324500303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 230550683 1250 230549433 230549453
    0x909050a110f100302040905010f12080a050909090d021b030304140d020301020406020d1407080301030206090a23031014011203020f030a0e0315070203090d05030d06030b22020d060207 81
    0x150f0b40041242c16520b25150160302070070564002d50400c04c8907a0322400400c40e0740300d243c055051075200326a003150010701c801d40140b43d800c903c0c3c6031403401e20f080c60012a04440040c2c600d0400c5420407000d00710b01e29030410164264280f03001841c12200082030109440c2d200740d015503803010303000044d14038480c4c40e40808200c043d94054000c56a6540d280c00080d120741c01581d44100140211241d0100d0442e401e00b500e580c1c07600000b801c0d243d81d1039036080210907400034030341c641c210000d500006074000060001501000d4090070449291024004250030400011602000c040c03829561101c81e5401c110a1419101e40d03189000210150f800c05a103000b40610360318a55200024006222540c8550f0003040342c80280d040307070343c09800485106901d85040304d41d000164014400b0002c24944400060491030155055a161004020100064905a4009507040303420305003031002410011240d034036809000754581e8400c106c15030002d8402880703541c02030056074000c111031040c4584518 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 230551933 1250 230550683 230550709
    0x506011413150201060e01121a0a0f0905010209030c04110d09030c0c150e010503090d03051008070f030b10030812040c090c08040b280f090b01120c0909050a11 70
    0x1405102c4045200300078040c00755400390303980000c1690000156019011010780c00c042d0300040606000b04025a42500c1d48002010504180d844203103000034000da500c01e42c0803042c040e00c005640c40421006161030100c2080360303a4060b0745002401440c01900005885004511400c04983d22001e4181110130307100d96000030303007010200070000495080d08912500740c985039072141e98011114034011350307403400100e8040550782c00000c84c04140c0c41c441d520050340417594810700103c168490300340501d0911160091900319002d41c00910512601510459200b8103c00102c2c0d240c81c00d558581c6194021100310300d07286441a07021908100d00c0c2030341d40c00502681e000401c00102c42000c024000c1d0416601903914041030008241441c51101460501c1000d06d01d00c00a051101140c6100420610340c2c0308201c107039215504400540520314160017810710340c041821801050504e0b580304240c0d030340700101062402c20190002000400e031610640c0d042450035003e4006040410b1566070300e01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 230553183 1250 230551933 230551949
    0x20706140a0212030c0904060e040203100c0917010204080c030f030a1809090302011409010513020d14030f0406030c0206161215090903080604090305030622060b0a030f0506011413 79
    0x1004000ca002e40d2000a451b182c03104032414005540d5030171500040480684010790140c1040d401900b1031100c9401080da940c00f06c0c50800b00f80c3d513540d521400700f0a00c2504c14032682c0d4000908101d400403c20160300c1d000c2e0210b02510100100e00320f03a541da84039038420401400441c041e2445144111402003009041003e81403000707007e1071400a0007010b51008401d598085403003c1986584140b195510071080101e074000c0f403110a400b00000d5506044048440c0c4481d580c00d2580440180302403c80c0c6040844c080b0b85984c2441806810350300b41800a0007198040802c214a40c100c01c2c0c002c0001c2c4466060130440d40c041c2c0c405000c050540c25a020b4810f80c0c400390700007400103940d804901001e000b0f40c0c075400c3c6600e6400130802030f1203407400007070001041400802c119180201c80700c0343c1c80b0400c210f0ba01510124103a4101a180c3c5a44080c803202004a5600300481d0140145440350480400c2007040d458078500103801d14401185990755818040b43c4140034518000b0400c01408001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 230554433 1250 230553183 230553187
    0x703150905030d2414040b0619020105340c0f050d1214100e060307080f060a0f140a020a0908030403140c01020a0b0a0213030206190f020706140a0212 66
    0x3c01050405030006841003107008403111038000300b11043c0d40c220001c4c0c4100d1101a6050820307181080050700c103a07401387d81d105004026008000381c00c002209000450f07900041020f00d000350810103241c0d4401c103861010030700c6c3d150504844205518a20300307040103007410f0030380340130368200803000c1003005000070318500c0380480d09801c0c1e0750840d841800c02d50702840c050201c042101c3c46625a18410356080302c4c0304820000c180100c2411210304ca600203c0942100c0c01c2075900c80c3c90390326054209599140d40d411034828018520850700610b40000d81000c3c041c4a103e01c044103035808884020b00d1003401130f40c01310304c524480e031051009070f004010383c000301c5c1d4480d92030741080c0300c426208282070002d5209031500d9400550001c1001c0d403000341c2104408025680c0c2080780000703580714440d0581100784c07509010005030b403a031024001d170040c035042c2300d02d160710104000742c41c0405800c040401d40d40400401c11603650f100d810311361900381000e4200d49402581c001a8030303017081030949410311440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 230555683 1250 230554433 230554447
    0x40b031801050702030403050c041d03040303080402091e2a0406020c0f0301061a090d02062106010914010507050c0d08120f100e060d0b090c040509030408070315090503 74
    0x1a840032420a0301000020005910758080c145d0350b034859484010200d800169a01c0c400b440d2645c892140b05024040b11081d50708144807950540c0c0c8190012400b1801100600040d0304103965040d9212070708090440d85a0400140c4103c41d00700100b0071120440c40c200700c510001d0940c00e40c1c41108034444442a190f1740c031014040c0d281c10043e503245010760700040600b00c0790300e0140228412104110302c007003003003c01a20081c200703900c00740103541c1000c40780c1c00f20001070b1901c00c000d14480c007012022840c40c11580070010040e40c40035181904014019005128286056012803043c80003420481e64601052802380d042c86241126240d014281c921030000307100480c0028a62000300101c820b00c1b6681c1c41e0145960440c0907038032011111001c50042c4100205e080200b60489401032141440d6580f0341d40d640300c11002114090040c1c0c018500144043c10a4054540c1101d049005503003454103100002d540e4220601c0f0203486002ca41c0c40c0944c488555038010344059820100390b07991404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 230556933 1250 230555683 230555701
    0x618050711070f030203060903030720030909010b030604140601020709021c0c080405120f04090b04020c0a0606080d02010e060606071a0c0a09240809250302010206010611060615040b03 81
    0x3c8a444140c1c001e004030000201d14071404800c40340300382e0141d04c515040c816051039022503203005144961051004100c180f0b02c580da03a12150b4024003405400310ba90386405810305c002d41d4600d50f00c1c540a28554024012607a8010039020b00f07a40c171840d4016114801c150105421104070240043c2c001c0c0b400e50280c102c00e502c00c1e103070361145001d442200d003c1c6012407047d03100d51107614010020702d0400d0205000b554003c1d000441e00000080016044c0020003a032107042210070101120b806545600400013110144003510010101380001c002900340c41c90004d450f000000c1c0694440c15001400c40c0400421480c40400c400440c1000c0300d040c0380060030700006520142d02100480c0c00850002965001c60340c0407020110000e04031800c1c401582420358014102a1082c40d45000c0e68268a40350407000c111405901601e41c10a146145140000b900303010040c1c100301c04010807240740d041125000106190401803c0c0c07501a800800c01c0f46c00e080741d028603001a24a0880041070001e07402d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 230558183 1250 230556933 230556959
    0x170f0708040803071e0c05210d0f020705010e0f09060307080f03090307050a05060a120e0102130e0705040506070b0a0b06070b0906010b03070c06021803011805010c03061805071107 79
    0x1c4e110f00c507018901440c1c07614810b52403545540c0104203451b001418816400c3c00c01c00d5000f403411610005ca030032400711041d18204080900c114000810160b03a0200d03444d4108003500081000f0708207030481030308060104412108240301d081c081d5034020081181501e0401c4614018402c46062721150301001400c0c64507540105d550a10030311402c28081590314218004030200c1d20020846480c000e40301400f6109190403000b109a115651561025602003c1c0000c12003145036040311803111381485031585002602900f44400c2060922050101d921000308440c0e040e600002c1c080016954481010040d04c0c0c1070b45035640100300070400030100a5103040241c055132003d820b68480d80c0e2101a41f11890004686840004042642c220080b0340b5684c0102030021800851480e500040801b00f0b0070350b0014511071410150036480f82041c41000c2c410165000e206140038403581d45040c240500004c641c410081c0d00d40d07602e00214511078003500d0254203400207102036440d4070342c1c1e9401d901494 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 230559433 1250 230558183 230558197
    0x60c0f020d0506010f08010b0d060f0b09010f03030311030126010e0d03020403051506030d0e040b100512010e1501080a0222080c060708120916081e010207170f0708040803 75
    0x8216400801b0915080c1800390004460003d00046040701c0e55448500203040c55480e200ca049684213403200340c580341d5602c402d020b48030041141d0000340c69071400908a50032a0b00c0700282c240e007440140520143c05030b01c19900707407031243d06011141205112a00400707403080150100d1103443d40020740c803074040d0007820451b8052010303581b5204010f00041a1b000048901c079506070410402048118000d0120f00d060090242000440705030b6040840c2c000b0003280c1e1054003007280801e0803246002030940c1c3c00d0240005c40040301c4ca5041408071605641581da2141d410b100d90300c00003130004801c5c1d5056030019608414061500402c00c035500808000034000c1074854082d1a80c1d140882c00c4c800d044805c042d0780090200c6c648040c0051001c801d450181c4041c4041c015005509150760022500001502c0f00c800988840b00303040160281d17032600c0e01c8915225900500104002c0780c01694040305840141d000140d891800105080c0c42d441031182c0180000008100824550000001381800d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 230560683 1250 230559433 230559449
    0x90903030f020c06010b0313020904050c03160b1215060304060606030b040911040b040b13020310050d02060a030b04110711030c04051006050c0109120309050c041104060c0f020d050601 81
    0x81c0d41d00702a0074805901c50028410119885000100711054011000715840300f24190024140c03415980054200001681c4c142c900354468042101c1c607140a1100c1d5141050010b1500a020318080400034507004160300d61200d1034540b00001d44600c000300d845581184010300745035580c545441c0001c02072140e8001c40740040d181c420107060605107880b441450a401c80300000b2400700f02420080078045082ea160380141d11100e00b0203035912115610707842e0200109025072030349086016011003541386c2d400f40c1d100e40c40c0d070048100980c403403600b02e42e88500d692070302140c2c04c0c2c014800705001c0c00c00d204100415003070010f0320380103006440d0715a0001c19021415240100311030010030060352000d9400b01c1d92910150010001580240014200d1800d00800441d01c0382c1c6e1074465240001d030365264030000c01d446010340340c1000000e100c1e0b1080302e0717030480d8208003603c83c0b031002010031b0046000b12414400c00030410f005105458000381c516a40c028a00310443c00d0f00d252280d1601028030801c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 230561933 1250 230560683 230560691
    0x60608070f0504050120010b06031003060c031103061309050303090a050c0307050319050c060f03060f010f09060e01110601140306011203020604081b0a0b180303010e041b0e0109090303 81
    0x681d144124200c8044841c16524020700c0c01a4083e0340300d07668241c00e40194a5942c1d512000b0190303c9001c080e5100321402c010501c00640b45051034010b0710408452001098600780c0f41241c512004c100303880d041082501ca18070348101d1080c98900601000001620341d22001c801c003d21420001400003440d8030620a481150b0039540c00d140d5240075900074aa81608800c1f550840d20a8560808041a0281086803014522000880d490358001e080f00d500507440003080050500b0440c40f516810030080c6461a0034824580000303020070700130b009503070400240511002090703100d003119440804406064130400d50391420301180044c41208414003d01404000207804030700d41c003101031925055005020705503030f1540d401c589a4001311000e92414855185039036500d0f02004a000040d1140511819030b0800da8408104900d408a4201580c0d0040005000300e09401c1c075201d412541c0710084a21000b14280302c11080400354005003180c1c400e8800008013110b5035000414040e0203030302c0802c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 230563183 1250 230561933 230561957
    0x4030f06090b24010206100902210a0c0813020d080c071a0307030b01020f0a1101030f0e10050c040503070b0f0c0a0b01051302040303080601080405120d020301090b1009030303020a020c0406060807 86
    0x5e41c55060032100c2d01c402d40121201040215055001014100d02c4404a64092110181130810610003542c60290491341d0340d40808201d43c11080458101d084c070010b00340514001d50014200700440c2500030001c40d03000c1020061110108807107005484204d80034520020307500c400140503042214090300083c20700500140650000c16100e03800d5091002618110500da140e08501080c0c51140d11b04150b601d0201d040410750903ca00c42c034030308140c0702600c01800300340b0403507003a14005000341008460403c400c0040759800503100b000c0368444250213844400b1016058010b004070404d072951130181c500c4c00f004100031040c046041c0c174412a005006503014a0302d01089000e98000100801d046401090301036004000050b8014410400c65183c400c000e25050256013100d0010b80c0c8654000c8011300c01001e03280102070390a0410395422030342c10303080d040003820381502d40b001806150740002c25a05580c4203000003060107102400c14000240c1d038183c000c4c15650b08880440000380d1502140d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 230564433 1250 230563183 230563187
    0xb040b100e04060507140d0f06080d02070513020d0e0a0c0e1915030c08010b120a020a060507110301110415020c0109181d070512030c0304030f06090b2401 68
    0x6101514100000003409079500c3c0d45400003000c018024030b080c40554000480d0910b01280142441d00300c8002c045034804011503c1d03405c2d036142e03801c0342c8080e4202005580e406030380005d110045601c2141c94490b1404d1800d000344c02441106642c16596040000b0000d0120b000038440c581c0c070303100780d0888007620750f90000c8071a204400d456078600803a10300441031810081e504000200111005c88000c840c0c0e481d601c44410901c40e602c030354070300c0c4d441d0402ca6403030b817a1807017000000c450090301502407a0800c1d0300007007034401c0034000c900078407a02045541c140a039402e4242c0c284040034001300310b044a622480d038000c0d005480b800000345210143c1540795807000ca5429880d110623142c9a124600300032048041182c00100072541e1551081c050415405507101c244a0001000107401400e05107818858080e103402c904035520342c0100441904040300100300c0702160341194290307440b01d6070f600d00f007006003000c1000034102802e100107200804110300e50780445007485c9000c001c1024902001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 230565683 1250 230564433 230564461
    0x30906030903080408210403020f010e06010302330406020c04051f031112060a09030215040b1b0702041505041803020606040e030405090702030a02120c0307030e1c0b040b 75
    0x10040025040c140844d00240300c01001c1c00b0345102a40180340e0130103800003104c20070001182e054005900c011511407000b4000c0c49102d484080c1000a05065070541d00840c0584070002d8094400b00c620400d20701c4032a44070040c00c0d60344c6100300410b9a03520359488000f541e9400c5c0f080840e1141d0b01c0d11000c205080d2400b50014030504c605003107a0503192450f11880b00444034482c6044e040800580d0b086400c4400340001c1c0c0c490200f10350300003003980150800038a040c02c1201c2c600080c552040a20010400f407220841d485a03105080841c0203503691280d032554060144025017180c1400049604130851001c610213845003a20208480340c01652200600c1c81054805005038009401007442d0b03003800e0308040d40384900c60080300c0c5020343c1d940104a1480301121190016000803e20207115a81808006007200603d400070b410106098401501c921034900000c0612076048441081038890145280b14586078200d04507034144c26090900c0b010104481c04c40d0490800400100c3c1110107900b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 230566933 1250 230565683 230565701
    0x6010f050f0f03100204030c080606010f0203030123060301090f0c02011b081308041203030e0105060a0b0304020312040f0306110705060105060c0a02060403060c120b010509210109080703090603 85
    0xc10254074290745400e010403803210185440e01409401004410300c50203000400c02140b194034a000c2c441e240101c494280100502064104405007442001c80769000041d203064400d620b2252400c0c0002c401c9c080640019010441d410140120002404040d0381d40501d074000110f00080c42142c1c130707501d8204d080701c458956006a880b01d4051402c51a0f1141080550081611582030342c4100c507a00c0303000f40f07070300241d020301c1c410801008410105980350141240441c00c95000f4071982c1800c00004040740c9880c0a14810f140c8040000b5042d50740400140c070321018020300f915030390707600c58a04151a004a02064406504042c160417201c000c00c402ca0340440c0d04030014016a07403c210402c0000c0c1d01074401d560081c82000049009031707865400400080d03100b60303000104001942c00142c4020541c0c0011005a4500107450b50180d800c02c3c110307140000d046555265540c0d0400b9508003d02455219038070561a001c02070080000f02c078003c2400c603004e5112581c02c0350741d4240071415220014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 230568183 1250 230566933 230566939
    0x60c040611120307050d0e0106091b0804020f100c060501030b100b072a090c05040303030e030a0f08090a0609120305010b191d100c06050108121602010c1506060206010f05 75
    0x840c0c3d24450801b400c6a5410140e001c074912051a465500351080da4000c1c0d00b64543c1d03820644180c41910030300c10b50300740d102e0070030505038a0103800107052104000d2045000c0c0c4891000859524424014080b066078007038420030095031282040d40b003501003150410051100450040742980da00300540b84155400b92490500a00303c0c40300725000c3d000d94a007500403040400010030741095500520720000ba056031080d40311b529504000b425100c1c49544042243c0041294a0440f903020482040c0c040d02418400081d4980303296803848e04240030f8010b03200c0fa2030610802d04110301d582081c41c82d895256414080780e40c030f0325460700203880b070701c03034080020904202e00109150080d0500441a50b1a01cbd11514441280000c81d03000c6480b00d01c8800007480b4510080d00f000454410a0301414000005103011000c203515003c942c41910300c001c58035490008010110780c858918004100e510215030144040110390b110041c00aa00440e000750182030004122000c503800100c089400003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 230569433 1250 230568183 230568187
    0x203040f0b18060105061606150302150a020d0c0506070c113001060f0332060402031e03091306120f0309080606010f120e071e0f0501090b030c0408060c04061112 71
    0x2230365034034000d25004050000c0301078a00b9001000d43c0d28001d042100c8640c2482550391808003ca0090800a1740900c1074148040c0d6404100800c1c0000345a56011001d814004002840350411503a40c0b4030400000da440841c0e04441400074000040116400d00c0015030400d80307010045196090320464002d002d00c500e8002030402c003042c040341e004000c9045650700c0500d03100311101e400740c0f405003079a0010340361f0380301c001880110308040000002c6000d516203c055030148441300300f602c1c2c0c40381816103031103000d802d0b03640b620070f4142c1d5100748014860903401c0500c0035130918008001d225100c00541c0442e09042001410071700206025118071016511000d03010f422102c10340740f40104980b246069079454214002500d01000500040c2501280d08070000465082241d410a4203812903020070841e11001c10050f40c00c225524141c03100080d25079203a035a084820140f41c0030b9035100f41e11500c200b03000c1c466070704003940050041d20042d68803c00580801405a80d84110000500c2040b00381 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 230570683 1250 230569433 230569477
    0x403080f070c1113022b0612170706140f060103060f0501030b030c0406030606051305010803120702030909010612110903060c0a14070b010504060608070e04020d0b030a1208280203040f0b1806010506 87
    0x91802141c44e141c00e00c1140d541401380e55160501144d035100304140c5280c4cc103c0c24020310030b000c100743e079600c500c003441e0612459007486102c41c281e6603940308050500d0f440380b21489060b0b5042c00307036150215000c1c10410860740c2e41d0802c04080c1a5505c22280207204e10464007880c0e0102340142416140414011b62910210380480041d54500900e6041103020030b2040c4202e80d40c640304400c1c0204080e076503030403154208861070700c104c40c003004003500070440410281205442c040f41d010390044011007144e4488041840c00d8a0b441c64070601c4c2036003484005140d40400004a50a40c142c1c0d006440810000d81c03200815140d045054030390a0124504038103000951034250028040302c60525408521141d0220100c2c0c54802095003c035407034540c51b0006850981d0204200b60b0020600c84869040c9084100520030010740c840b8480364580c0000004003842a9003082803074099004c3c000008a00d0070840f581c0b0140c80b01d0241c04e115010300000087c0d5490001d0680d0301c0300810607003118141c1c2d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 230571933 1250 230570683 230570693
    0xe0a18050a11120c07031103120609070f080103020f040e030a050a0912020102570d0305040b03090111030702151506092112030403080f070c1113022b0612 68
    0x3100c50101c04004010070a0087e450091020b001c3c0340c0b4000d0307080c0341181452000c01446c103000814080402440b01a20884654000a0f690441c0d40589200780130a0100c40410003500514010344114800040e40703a0550354000c0023011402941d5441d40720081c2c031112002c1401c2c040850180c0140d2006902e99941c00b0303605036a495000c00c0403420b900e070752800707c11100240e024150500502049181c10010100c0710880310b018080202c030040c42070000396501619030700030350103095030503000800003075902d42c4250f0000c821000b05003500d44e12450030104c000c0d07031005880c090940244c0b0540100d60b80c00c40284601d03018140c001c001c0c40c00d002d40030091000410b0301c000c40c151106460009014188400e1084851030001014071a94916050070302400c08100505007441d80e034040303000c10901e80c0d40000481000c540c0496654242c906000c0001e0f680b40c84191100c05180c0700048104144070500702d01c81d03081e150950590310b07400b4801d80d18400c807540c81c0308a91140c40c2d00850304001803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 230573183 1250 230571933 230571937
    0x80c0901030c0e15030709090c0f060512040302030d1a03101b050f04090903080105030613051b190602030a12090c050f031203090c0108091c0e0a18050a11120c 70
    0x901c42c0d46a821310480e0640041e00d008070660002131100e81d142c101805008032032480342c0140c1440c0d20b040f0031241c40c1c40ea0091841c8603050b102134500e0400000705042620038030490302c1e40c0703c0400040c000b01442c102404084050164a00c3c0300f880b69843c0e461640c210750244547c209018410814500f507080b03006e862a6100d50310114205900f040042100c50881c450896910f0081d0380711002e960604081c149452006481e4022040143c06250001000000c0c80030981c81c08120141a40d940300010514000081044580c079080381c480118000394000050810018a595074100100c400c0c1e5a400881d040f1081c0605000328000003030000341400030503400389420140481e1000414141e04c3d8405400503945100c2765040780304941c10a44e8460101c540000c1420094144000540080c05c003d89100c4981010300056041d51601070340d80712000402002552582c12100d64461000d00080000701e03056146203140c03100003a000c2c1c2e02d20080c0e414034804114402c60f03079100d07101034901170303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 230574433 1250 230573183 230573191
    0x5070b0a120203250203070807030c0804050907030c0e01090f1a0f030703090201020d05120a0c02010605060a02060103020a0636090204030b0402010306091e020c03090d0507080c0901030c0e 83
    0x408280c1c40e0300e00d4200401e100843c07141034920000c00a440c0314400d0344000f1104c2c1e2010008541c010712940c4080388000048402d51689400e2859440920f490400320754003443e0721441d4420320440070060340c01e800d9003000309a91101d550310040c000c00c0300c006450710b1085005086008014030760610015090b0001825480d101d601242c0c14000d60f140340d1261540100c03581000291a0102c0204651701000381c0350074000581030040c05e00f0000000464100c0000b01090b0075203440e00d2000b800b05000394400e402911010384102c0c2d84044003030020355100e40c28801280900c0c2004000103c03940702d00d103521141d20124030b050700800b22100c1201c0840c100d8011b0010300381c111380c4002403000740d24030040000754882d454185485c5000c1c00054100c42c10381c1d0040d20106d05001d03150440040f048411421504580401611401c81145181c0b560152208081d00003091880700401d100340018048c089841400c2110442c07400d50042c0f104080003880700038a92401060b081c80f6410001c8c1043e540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 230575539 1106 230574433 230574437
    0xa03050607021f0612060c1202030a2304030e01050a030b0a090c021902031f02090a0906030c06020a1208151801060e0406230d080309101805070b0a 65
    0x80c042440001c2000f0f5440300c544c40711f0740c0070b101c9001891490080c21500d84c64200500341c000d00da200500d4a00d640c6000c0c500304040114900c0b14031595069584807440040000103440e00d4021003105002d060301d03640c04248030703165449003030020031520401150360a0158130182c2010603142100403030050803032200015842c0061910580c83c1082c0307103400c200910b20121002809142019680500c10410018508a01c0d40011080c4d0340640a0160810f640e0a0240d98132488500700405600712031b1140407003207000f02c0e0140c3e44801201400205803040b800012100f10815010303d00000096005014095000c280c401078842c060b03a0400001c0d0520318000041443d1001021200041122244031070702d400d150781c1030b1030340e000b1a125120305000300f44980707a0030140e440059107841d1022151130240100c011005003034002011300f010508180140c03c4603401301d210001 = true := by decide +kernel

theorem cover : BRFrame.Cov 230395683 230575539 := by
  have h0 := BRFrame.cov_init 230395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 230395683 ≤ n) (h2 : n < 230575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
