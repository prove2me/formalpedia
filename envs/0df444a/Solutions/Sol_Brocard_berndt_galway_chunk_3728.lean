-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3728
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:30:43.871559+00:00
-- url     : https://prove2.me/submissions/774331cc-1c89-41d3-97e5-32fb0bc6a6ae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 670323741 ≤ n < 670503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 670324991 1250 670323741 670323749
    0x240305010c110106180f2318071d10090606020109110405091e030c0709230108070e0709080303070e0906060901081519030305030405070f18110f07080d0e0601 70
    0x41070000c201c40100c5040d80000710100c00c0408001280301200401040d07a03107d01c025a030410340703940c3c2000360046442e80d9403d512240c84005010f0a4a4403111181081c00d0050303107084001c08801080300a10307507a48000145c84031050a1084980315580280285020001039511401040702900c050801e07125160180841074080d0101c40c15903d01e2894400008150120710b06c800c0040407030001c0140b00d950060f220400001c104c982000c868018240003c2c40950202d040a40042120f400002881c070308031004c8004429480d61044000d4440440300e602101d0b40f40000401c120030503901c002c04c401105822035000c0c0d460b480e1a01444240d0290006403408140c1e11f0740485c10540b41a480c040c01514001d200c0d500c0c144940e40402032148140d8021808a0004001c0c402003000502207407002e4510881d521402c04d00d003040d0010340c146c080110b039842c25a11400300348851380080c1116280e20901c020390369501640d1038400c9250703005039140c0242510300070a11544030303404a01c0301d040b5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 670326241 1250 670324991 670325009
    0x5010c050702011b1b090605091602031611090c090108010f180504140307140f0105060904020d0501091709040b06040b071e06060e060f0d020102030d240305010c110106 74
    0x4082c2090b440788591103404d0040c2c0310f006040c01015800310036403400c80f018003911000425464540317810f1240340040034200002c40215110f036682100d500105885514441606041081d48039040c25084400300052280d08401002c00700304968109000408040c50282d8603203915130fa0340c400c0702c28200f42c6030060380c01c0c1411450301c0c2802006146c002540050090010900c4480400541c0c1d180d42e102d00400c03909554409142c040d606014040d421050b035101e4001d2003a4034203000054402d010003000288104200305402d01070042c25400910350b2544038584007913020910300710020503007007040310324031990030142010041c1c28633109690848074064800c2e404c000140e84e80980c11100c098114400c0a903190724140800c540d130241200401e0000400802400c005003400f9507901c00c20b242c503011b000003440000050341d001003124075001c880c01c030001e400214083e0909021140500a204005481c2d0000c030034070074190301c440071600498541d07401d00410640d000d802e85040344600c80c13030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 670327491 1250 670326241 670326257
    0xf060f0a0f06030e030d020a39120201021b01060f060c11041d03030709182a2003130812090103091703070e030d02030922060308120405010c05070201 66
    0x7100d800f035080003039510f6080302580c3c1040c420100e800d04a8000b102c4500025149100d0781005030225078810152402072807000610301200130406852078108040200751800c080b9114070901c0c402c0d4181d407145602015102038100b00e241c0401e0180c01c440c020300e109040c003c81d0010f4020300441c01c08100700c0d405030707989440f0100074040100800007084422030101501000d00100c0c00c040c40251710440d02600c072503050ba030a000c002a00c0004030044075031070f5031504540400045804c1d5810044000c01d1407080030f1100210821240c0103010002c0400307050350b000b10400305000100c060455100300140328202c99951740c01c402d54459030011000748503407082007089442d5100307400c221502c50040702c40a20300d4080f4001e84480c1c0c1d0045400400007051408010203d1034140b00c0d90b40d549038a44015418001c001000076400f84050f880f82c1500900240c4035000c40300660050001160484140303034880400f09420900a00704940441f0035501c1c00410303100c818021001d48084a8042e03456001c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 670328741 1250 670327491 670327499
    0x93c130e06042009010602030d0606050c15070504120807110118170313091b031109060d0906060303020d0201060e040b0f0a06081b040e031819030b0f060f0a0f 70
    0xf81800924032180c4150102d0050086500d89444160007004160700655580c01c0c0c0c4002d1408850503500100e040110810117038a860303100241c4c3c1103016039004100740c110b840d56001074502e84520340c0042407a0001003400300030f10200d44060b041c0301e4000c1e0100060f030211180115440c0c008031a2100c01841103c100340200c0146c2c1042c04c00c51003070401224545004040c200040450b41e80c080c910640e01c0341306004c0c580c60381201d05665071b2614101844004001131000c200d901501038013500507240454442c00440040d00200b001c65080300f0100112601c900740292540a5894040055030805100256071004c1d02000c81c451508040c64030819200c02130862400178001d02520a52a1107a5000c40d801c4024802d64401d84130400b1403100042d0b010f0140019500c844c0306810440e08140300340d04d1602d4240750042e2101100301e43e1795103032120300503452030300e00099040682403003c80410421303125190301070b41c1d00485085900c504822261000c001a0f58101d001d00707082007042880c204 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 670329991 1250 670328741 670328753
    0x91410050c0c0d0605090c0315070e03100501030602070209011a070f060f05010f050a080705090402040b030f1204030c0b180618130926093c130e0604 66
    0x101420031204140c41c1505240c0b80000c1e8000ba01d1001620140d9070307003050140c0c0c0e50040000c0c511030003056000d001116015041d101d5a0b00000703009000348251811804130302e0303505204150241400c0d40b010003040d610303402c1002c020740111601300d0040da2591b0001ca4003402e440b00304a03c8580c806004e5260010a9070350010728804400115210760710b69620401361991401818040c19159554420041c9014100100041c20350300410090300292400d01003600e4030054541e1098050301d000ca4110fa01602082c640380d240385003407405002303a207260030704c040c4544024012203005208012304151100d000451a2044103004c4d10819105240707110141000780c060304845403180e00104040d20300701c01003a1240b1108804c0610700d6500e00a1404000700340411515203030f06110307048501070402403661000e2089080052068000075000b4400d43c40000c8081d4007a044203140d40380c101c18018010100c1c100504c0401d218a0350525103c45803a4144180f1580c203030020000c100e5a16142c40348 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 670331241 1250 670329991 670329997
    0x1e060c050309210d0206061e09180a0816170406050a0311090418140105040b0103060906021b010905060708060a051c1a0703050f0103021005090409140d09141005 71
    0x10052002543c039040c080da0405004103005040705402811341850684c081146120b920341c250741000046081d02c5585449a0511a5000c640044e1482c10304c806da00020389061200c8070018481701c0f00050034115000080f8000c0e507540d108000d6048039107006002d110582c025802008009a010703c02d520342d0301d202c1c2d008a48203400d0660303014500620200880d069405504001c61403402c0c3c5800c0c02d080010140c1c821844082c0b00303008001c24201076039540f8200b4810310003c0e020585800c0c1d80d00903c16103074110f030803a2176440c0100441c43c1300d6540a0303000e461362072019141400f5600004100c0c5005058107442174100030a00000c003410300e4100142080d00c6045030310030385a04c480e444009060015409007075103003007100071464641400020150313100204902c40b82c038030b090010801a16141c03100d801c00041c41c00c2c41c40c0ca030328045000ca80188001c184c0600622a6070b000c410301d03103501041c0000ea0f0742c541e65903000656125244081184051004190001d9000c1104511248a0000f07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 670332491 1250 670331241 670331269
    0x60307090503070b090910060f142107020d02011b11070315061509050108150d0c09051504061a0703090308070503031e041a19061e060c050309 63
    0xc044984810200b458030071150070a0458010008002d4241c0c0360030701c10503a012004144401c80c143c01c010004000c4100d0400031000c0c08001c409180e81140c12505889078840c010030a100f400058013600d21035a24181d5400025002d284500c10501d803060003070900ca544280380c180190f20f4080421034031b00c04c3e40f803001c800900510102000007502d06400220b10030381d441c00032510034100b03c089100c0690b903038020340a00417018020070040e40c0000c682603012590344201102e00302c1c10f40100c0c0050031910f030000c1c8081520b40c40803e240d20550b2041d4000c6407400c440a4044003c68184402c45441e13015180380400905511034450001400a001548c441d10300100c41694a43c0c80600c0c68001203c1126660400700c03c000400100400c0c00814031241e034a902c0300d0341031545031800300c04a0349114411540e00c1d400000c02000c00b41c06180c2c41c00002c076100f000700e07d0707a83c040440300c0c0611281110801d80f585100282e9680329441d86800b842c0c200010314644004401041454140203034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 670333741 1250 670332491 670332497
    0x510031e080d06140a0815060612090d030606020c030c0904030212070606060e010e01051209010e0a0c09140108120903010b06040e041104061a0706020702041d060703020711060307 79
    0x4440001900e0704041c1c090011071120100d102030070b2401c0e864654040c04d00b9070f4000d81c0c040d0700801c0f080800080111032000c1745400d952498980401080e4940f040c040c0118140480805114010600082511181d4100d0342c1c2044010344601080740c44840b040030880d855407041ea80700340245008c041e516080342c03107401196140fd040c80c0720501140c000c16070503aa8113940301c404115181c0c12401807031040d02d0920f440c0c03482030742c03840010b0f003680100c50304040483c4898000480840d425440410018220800c41e0042d40d15403400c141a5089800b808401c1814002d02600f500c1d03400e840b03141078032480c00241c5011240d8028010682c1c01442c030720740d032664031404014103545900d0020800390414043c496480c1c5014185680b000c12009255030149190100030000d00d1083d206503011403201d403540b1652450700307080c010068068200040d5000b4034101c00c484100812090a8622203185c00c00e55200e82d80d0414254102c1c001c1380c50141004940804000c480c2c90110001c540c0498641 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 670334991 1250 670333741 670333793
    0x80f0105011d030c0d2414043c02040b0f01020d050d0b1005030f060d03050d09020604030813050a0e060102030406030b010c0b090714060f0a0c0804090c030b1201051003 74
    0x40c0001c5e540400c004419164011030301c050714104000d1503c051080508000c090000c041c10b0307003145940d09802007002c0c16a41055560580b03e84424150100d0b0248250001180c1d040c80c659411005180360002c074400c605d0007514010500301102480c02980e0160003400e1403280c03640094405030712203e06898004e035581071000c181e40d50a407101038a89030a544064507480e08025440742144080c10240c490201d503200032001035032181c100d400403962060045800003543c03010032803c0c090b54000408000d0f0103e44800103004c1003108004503903003194410202560341104040b2044103554550060708108400d01806000e504010900750301031418450350306103a1515440032030169031298cc039030885a010010b003030316101a8403000c07004071080740c58640100000300e90303840364101d56010f2095100c140020f00ca501020385000b0f20741082e040c404800c080100070002d001c203d08070707441407445244154000f6814441c2910450349003600c62003980c1591140d45d0001c0211000c441c210030f041c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 670336241 1250 670334991 670335013
    0x604031e080d1d0a0c1e120f12231303060507030e070503030c07151e03050105030654070f0608070801090e030f0c0607080f0105011d03 60
    0x240000c1c9060400380000081c100d030305900020a203241c84800c04041e510074481071010031101821001207540c0c5843c100b212011b088090307440503495074491412078280d00e9641c0c0c01c0c01100700c00460300511884011059294100050362060701409040c1c5085c00d8075540e50200c10340550080a280401440301c140702566503550300140e6030308594160010b922140f01410140307007004854040c040c2200a10f00304801d40601781d507590264400e0201050074182c4600b030150180031400551107980006045094900c2c2c80500581000c0c403e082c0a8885c500c00100c00d2040c80400d11110000744407000c14201d55000f91a901c001c05c0c1e403c030703845a6021101000c041003074049003561b0b0b62010f000381240c01c1c5000d000d41a8810242d204d8410f0000600c00c000b6140e034802078050641d850b0301d8001800c0007614050618600401081d2940380d000044c5008042c02e001402d284240190380d1903419640d00d407a21343c2038400003032142c07038082501c058145103e002044510310100402900300c0d030001100b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 670337491 1250 670336241 670336253
    0x30902030703080f120117100f271103010605130207110901120507050904021c03021f0218031b1302120705030105210a030f02011b0206190b0604031e 66
    0x1010100107402c0b040014901710407a03214414900402903a409400b42d0341d038a8886036100c01040410f100c515a40d0408402e024031b05502100220440844114041c00000c0b40040044001794044d10b6242d44054040700900c0d050080c8010351300007904446000008400000182d0410741017191290501c04a02c002038541c8807400f8000c0c849a1020300301079401d8100b903410a03400d81c1040307010740304e03100421015803180e141d420001c01c2c540c500d03256051300c28207049091820b111400c0d2910850001003440e000e031540c01400f804010408042810b2080340105907848a0310780e84040d143c1290707500103890385400c003000c41c4040320b940300152600017820860700c0148801c4404e8008590f010005012a080c0390103500d0400c03d00624100000c0d5001c0c1c40d060717950380510b0700141080302011034a10107a02c06c1d0031035401202e0844c0e40202180076117202039298407044070030541280148008c40b05070700030742c01414200203010700003610301410341e1182c000240c140c10303a0702c01c01000b10707400e9400030b20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 670338741 1250 670337491 670337497
    0x304060503071b030203091e0d12110307030527180604060815040606290f0708120712091502090301060315020901031b1d1311190f0f03090203070308 66
    0x220036401b8542c1c03004070b00304004e040480000e4000091f041100385114a84402c1200c0700b4640d04600b01d401c040a03044c030226004c00c03014480800600020a01804050300b08000e0010081070080c030031050303590f580c40308502ca8080500c0981c84480c00c80c00110036480c0078005a001140940040303409521145002c1c82d028042c0ca6907100b8108010070001880302c60f109250103071100e40b00d00000d0074001150056090700c4910301249034140003410449800003c0210f03510385601c10710103921181d83c030400501444040351018045000b03110801e500c00528420b4600e16548001c81401e40244d61000318000e4101180300c5405d03650700e45010001c50380482111107400485940503aa40b0003441c0018281d50030b1740d20254941c03508940c00850035400480f00000d44c50303034100320050b141c6502d00003580c98250403c0030499074074103540601c09003c1c03000241088640c10401c42e509000d164022124528070442c0c500004007005141a21144030f0b4119840e668002801c5807040c13a103079254035250794 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 670339991 1250 670338741 670338743
    0x1a1e1801180506040c0e07090b0901090906030f060b04050705070f050c0916180b0f1303080f070201110c0102071a04230f04050403020c0d05011e0e0610080304060503071b 75
    0x70f8400e01c01c00040050942d400c1000e040110b1352080281030212025200301d106001340c2e8010301d07010440d14142d074070031503e1800504810105003d4035540b41801108002d000340b0941d40701e81400c11034180d170f041c03074003955010340c1080d41d44501e800569105c078944081480030403030303540c0070704030502d10745603603011805000c1e1180016280d6406901c2c100680790f81d0381085030288412540004000311120790081d1000075a14005d95595503c074034911504a100c160030080c81c0071400b00c1d052203070001d2000500251792003a29031038500c14815104030740da040c001d82c0329070040c2d22101c0148050703144480401069401c03c09400d04040e1104021a4020754962070030b04000112102440c440c9082070020800e030105480411007800c03e92002503c40003100e501078000c200f0070042604000095004800c1050031407079400031102105407800c040c0419021801540c45a0750108040001515485003142d0450b002180352524082c010b0750301d500020204010b10504860081190905040c890406 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 670341241 1250 670339991 670339993
    0x918010b0603070923010503040b070c020310060503010b0f0904121812112d010c020a080703020f09070c020d080c011a030708070b0403060e191a1e18011805 69
    0x4c182006881c0854408100c0381080c0e001d21103220480c5030340c1000c107e940050304204070350001d80e12482d0541c2c42912154009400d44180703050319030f016003d64042000d88100710020320a00c4201d03010000c030382090814440d404900000803c0000b0078005e8030035448100b5003030806184000e07070408070024000e40d028098180b8100c006504000700202143d0070980c0864002c54000950302d500301042e0b00381040c52800405491042040ba8040c40118110304c0e8001c1003900c41c9a01c0c3c01c2110784440c19440f003203000f03845100809015151100f143c500c928104d9840c821041c0560302005001c00d02c5400980382c0800402030344d2501c104c00c0c01100e140e00045024a41200d010005042c42c119841e80142e00503000258148407242800d8100c80c00c0303030317004007010521021003035019003418400380b0098900740f41c0c2801201081083d00c280c20030120284e0032b80c2c0d4507a81e030b00d030801c00100d40240c000c425008440d0010315940d00005c04030b460044103000000c1c045e0021040c2a902d444441c0e000c0d141 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 670342491 1250 670341241 670341257
    0x705060c16090207050a02091005040f020c101103070e010c0b0a0506030f0106080c060f1315030b0306010b0d0e010603080f0705071d04020d060e060103060209011d0918010b060307 79
    0x1145180036200006042c1c140003103107000503584520b51a0030305504020310540c15000401c00c0d02050340340c0704010300b0008008200e50301c51081c075400258060400d11503540506003104010890031b11802900354503403d0706503e140c0e581c5404030303103001c40030149505021041c0d0124000c0b4170382407081ca125082003000000c850915904040c900303880800e03111480e81c18184280f01d00b40c2c010076003025520056400070f4846840b10045512405140c0040d0703040c2c0b02010000920841071580200e40040b161001c2042080341018180c075001d0034002c0c40c0380c40600704480300c1b20100d1740e4000414114000d000085003034980d0b5403450543c0c40100c103804500e00200b000003d002c801d0180b00014071f10401380421130800282e1481080c90000e001905c03840c0012900828041d468200620740303415403086d07441640e1607140807070003500540017183c00116001c004180da140448140c2c3c1d48450300900e000b5181d82e840d5080c4c49040203c03101040f0035502e0b100c5800840d1075030360285000f0b290689520701 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 670343741 1250 670342491 670342513
    0x1204020120120d0b030d03090201080a050114060304020619021e0f060406110c0d022131090f0504060509191214031f05030c010219050705060c 63
    0x124403282031032500344a51580e00004052200002d90200d5a14032688094803a680e40c8540c9004000c2c501c0e83e19010b00404010001096143c2c1c41422039502c00d0729145070940302ca60380902210360034000c2851114a0380c140480c02e2501c02c014561091009001e5450300207000c0c01c0c0e21682c142c0c988041d015a02101c2581300b01242c0c0a00009400c20b001c004225040307032040ca85030b54401c06480940150790300d40c0700303210303441e0104200c5248040700011103000b60300035a8000d550b1462035140d180d00f50701d51894041c4035480e0808545464051210a0240c10f882503580c0800c044408542d130010525510002041c0e00c25002d144540d8031903d000152601d00340c2030000960344020300b0700d01560411801c0780101200545a1000700b80c001c2019403034942c041c40c058030768410840000410340341c04010092074400d880707101c14400348090b6608030119581e1041c15a128158402240541c205c401c0552904c1d013880c0c0180f0b0703424003400469140550b54804035005510401031070031150420441c00c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 670344991 1250 670343741 670343747
    0x21c02191a09030304030213090c08031c050105010206280c021e070806150303040b0301091a030607050a050f090d030f0e0f0105030411030a05030a05070302011b170a0608010212040201 81
    0x5410701180c84959280c2107020000075184d1149020017031241600b80000081844031b40d0082c9440c60344083d000b45056102c0b00141c0e5281c211040d800140411140d08118880e124003480381205c01c1070b0000c0030543c407100110341c03811071881d0704403a50b264065102481e80402e4041e5a80c0d14400b90050a102c039107650121060b00040c11001005600003038042000700310004009178401032100c00404007141810001c0c3c1948115440b0302c56002d408000424408060f50001e030340712400075840b0b54004201801e1540300c40d4100c0700040840c4090040c90400c2d03015000600c000d1682e00181498038110b040080e081c40c401f0300003600040e401c608040c82c400d800541922110004030307400002244d00500003066488002c2004003139640368000840315403800c100e01c00000c3e40c444162034a8194010340140140c0085d6002e4005600b0303d000d106694040f8558502c0111043d61948034442d03d1194031840c91402074013a100250780e0f8980043c0d000028406401c1a66190040ca0190b082c180001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 670346241 1250 670344991 670345019
    0x93e160c091a060c0a0515190c140714010e030a02100203010e010b0a030902090a0218090c22081f0b01020318010f020a020d0c240804021c0219 63
    0x40d11007914050104084114201c8100c1080c10125503855456081e03060341400c00b00044001091442000b2003038007282c1303805142c00d125220000b8015810110300c401c1c00d041d65659048500411680d83c03040564422440003801c089019001000c80c6e4040d014000f82103800e9180b075007c09410100700310341156030511844100312202001941194104501c105000406100e11415040d000a40d4200b050203600708404840d0020300c25646071902e84010006984005002103a64460742580c0a0b189400b0702880d005400c4180b200341050402c182400d5019000c3c4107204902d01800b1001500841c1001284003102d07054808540e030514001041d810365009002007410f6420900c0804041d24000c9103d003540c0000340381c2030040c41c03401c410682c01c00400d00800ba401a0424072010b00340203050901e00110340d580c064402c81c0f03400d10114518a120415040000500c0c4039000c0740c090b01d416903a0b40d074143c90014070582c45141070340c0090310081c441c1c4001c01c03075003000c84000c01504c2104092 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 670347491 1250 670346241 670346249
    0x100b07080d110a09120201140a08091207170d0207050f0c1801060c03030507030b0301111201050102190f03020c04180203011b0c260c03040906093e160c 67
    0x145052594101000c1c1c503a80060058402c0d24071582c0c603805c29a03100b0011501c405544540c4a80d403819044401044503d00700d811420314410901c1c5400060400001c6034031850704150b4240d1616841c901c1c401d080c0e841841c8a8207015000d00032200400c20600c0480344910b110390050881403402002c3c4100303812000000c3c192170342c0100040204a411202403c80103a02d0f03d00040c0c265076a000544c01404586400b5030990310701200c91511b094800e008000f200e00704103105096a03603904c01240c3d580c01224141001d10010030512000456401c52082d00c644a40140c40348030014a01060031107411101c4103814003012107111003907040c28402c41131141540751034246d9200600308003800200021780010801a0088101200c045800d40c040141c01ca02c6400c1c1507442d00303910800d5036641c10501400700102d1030014006440e410034840e1042114022209030722a0030008a00300b940c403a15041d0b02844410031b0301d101d070a504004014143c4a0034071a6400d403d14481c280840080047d0304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 670348741 1250 670347491 670347521
    0x6090106081302040f110901033e04080d0903420b03030705010c02060a0504021005032205030a1106090a060509070b0301090c0e10090302010305100b07080d 69
    0x401440441da210507041e5001d03090751a0b1040404030b0b880802c1c02030406011040540e480d008400b04c510f41c00341c000301440c1d24241d0303040c42001100c4c4c4c00c0759120000c8058003194180e135801c010511201041030b41c110580c2c1c5140d500d003041e1341c6030b00301800e2888042a500014004840c1841004070303e101500100009150b030310341442168801c0c0f00070400011042c1d51600c2a02c0031100851080e070082c41d84900d0160640e03441d500185811400792060440c20303800340c0119800248150a14410701d44542d400400c1c141036620084001e90342a80003400c0c1d52040e11044566282d208410300c1400c060340d1051004503590260800b00a2591044a04400b40fa4026100740440c04800007002e10429030000400a00303611aa1310062412140340d01c00419100080300018039206280d225450004c000e0f1180c1288072070010400200405014521020401c001001e0015520a034403007580b00d00c0001d00280d00c40d483d902c9403880ca0f0015a01101c0f529400500702034100860700138070303055104441d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 670349991 1250 670348741 670348759
    0xd0b0907090f1e1e0b120a0b0f090a0f0803070509060c0c10030915330518131112010207050a060b040204030506010905070512040b150105181e04061d06 67
    0x130b1101030352510b00c4000408031a1101007498896850394100104028070404481c011011484c01d66010740d0115240b440340800040010032807000400c000c0001903000c00b544402041950301c03000d032600b000e0000320030800706000032005030300d07030304010041601914024240c008007001040b0300c46126a25540070141090b02180005042c590b08180c0840001000b091381540001c0d00345000c50140c141c49080b140c40941c1c3c082c0209400300030400d031401925000d650083d0900d41c50b541c0842a101600000e0f10440d41e40081a440071100c091284001c000e800040504240036003640c020107001d50300303034202c14802c0d000c008546c0f20f40e0740181340c107a600303600f4149151140d5403100d00c148202000503440c8d000141d0020312410032a60941c400300c03440805402c250400c140e00310f000720398056103000d04140020300c0358000c0d02a41d110700d03890050500010046020300003142c020308000c440f08010041d41035440d07a2140201e0000e0004104004550f840c5018043c10b0300901410540c0100d40724 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 670351241 1250 670349991 670350011
    0x507060e01090b0d0b0a03031106060102061b071a011d090601050a1a090915031009021c0309050607050f0d030c0503060402030c130b04051206060d0b0907090f1e 71
    0x2c821204100c4807003854050300d808084031004080c14041c48020340c02082e2076404010103400c05c1c1d104071980c2c1024226601641c0d020b005a81c0ca00043e21220180c03403800012074805610180240001c07407061001725a29030000320305880c46802a00801908002c0c10b0003480111001d610a0b5440840c0e100140381651500d4045803030401103015100c0c45c0c0341c40c0490100e0700b0072180111005608042c1c90031040386460b00b0084050444052500c0c4a40126001d0510072203990207030300d441d580c00a0520702d00e80310400502030383d20340e94241107051148481000940d940d4250181403058003039070180c01c1c00c080328000541400c0c90b0944000c00c0c0352800b14240d0401c1e51010581c3c0e4860426500181d81e03480c0c9199a00e01405082c1c0808800303096120040780442c402c5c0c010b032040307885c2520400000b1596038141502c03032108403116500300801c00f1f6201c002c5a44a2151600006840e003a24203035500c8030490401d603502c11505100302c1e42c40c6c80e2040b0740079800704c60941ca00c2c9030043c02006225030f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 670352491 1250 670351241 670351247
    0xb0708091614060a052205040e030702150a020a1a0f100303050a3f1503080d0b0f060d0b0307050a080d1211180a0510080f0703061508040507060e01 65
    0xd10300d0980500c3c0b01140110205000700121101c0070031070240b002104a001c1020300c11407446004a5005500306580c82e01d0240d000029141e260364010030902c0348000c1c0580004254101d03480c00c0c411480340360a55000704501260054a10503100d443d40e040d40380c000c03075144884001400e200301d80d03400008108080f942c0602078500401c042e207070404080c1627490000311402043c060700420820030302e0320700e8511600380c541e01c044141c0c11001441640d01240d000c1512004070701c40a0200902080b40d41d150a08a034403806070414000c281c07454030151038001ca4115001074020300103050340c408000c80340b450100800d030002c00c4211b030400040f90070310f0ba040342c0f10f02a081100040c8030303018141e142031381440d8001d4000c0c0c407141070600b62124031500a064030840c8816290380a080a01e00c08031721030401e015240c052500d56111245284c496074079281030b909000f0032203810190340c1c11011400318414208240b0160242e600c00880f401c040c1401780c00d00f1019406003043c4010100882c000d660 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 670353741 1250 670352491 670352519
    0xf0b0d090503130b1e1204080904090c080a050607090803042c040821040816020d02060c07230303030c0a0c0203030a051b0a0507180617010207140a0503070f0602070b07080916 77
    0x1500060302d50700e036030b05900418040d004110b00103114a0002e100800d9070701001807031a14003400f4fc412100f8940b644082074075081907902038014a0340080006011484e2a80b0b07030462004d00c004600483c10020024203050f0800959044480000025118800e28002480003c030449003100584480c1882c0d038031540c0a1180c035215800d10010004041d056580720030800c0c4885401800c000e41c0c685c00d0004c21038840c21076020714001c141510f00c40c13961381504084817000c04400039004524584906042c40e0b510303008078040b1420010454800801a10248040c0070341d640991906134642e0b50b0208180c090350104200c059180e44030005001c00705800051060480342118100707002050909603140150080d0382080030312040c0c01e0742072002c4000540c024451607001e001004c044941140783d554503403c14a4000e801940180104000b00e80e0301440220071038440d40c00145441015a81c99031b44004c111031100c0424524020031103c0407051082d00100c0d402d038410104868100110084428 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 670354991 1250 670353741 670353743
    0x3150709152105010f061b08130306020403030c031704050706270e070908030c12030601120c0905040e01020906030408220b070c0f0b0d090503130b1e1204 68
    0x22050021001d68601824148031800315150119000030503180c1c40c00040c01080c401d00100c4401420002100352040c158000a056402140032400d20315443d00515500540052103d03441016000000108580b0080000310b1084d12941a00441070070007614a040480c40303503100003408010400050f10100303400301625214140705450030f003c0a5072845070079291007554003070b4000c5080803070805444000c0d1031013000c29695210080b40c45103010340c0c503800380e400c0040041d40300c6100710501c240800c1c003039940014185405001000041a16803e070b5007442180404200d030710f00203005034103040c0640841c0044a000940c40d040001020403a14800100007800075400880c90454040c10b200032050f0a08040001011310340d00c901501d40203a00c0020219002d00c08000001101000c211020045400c2041303581c0c1040d0302201da041c06000c10f5082203802c0d00082110349041d03040515010044c0002005068640007460400e0a0500254440000650082c0070710000840c040420175480703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 670356241 1250 670354991 670355009
    0x11100c0204050a020f0705060105030f032a24161d040519092a0e160c0b090a110402030f071b080a050315040b150c0f030a0e03150709 59
    0xa0743d0f401c0ca512000f0300920015604991000032150f0174000005a2a4141c905c03c8094400c6401e080c1d018555a00c144480b070044000122400ca40403c150311a02e00e0100c040c1c2c0c00d07582041c9050050001040f00c00c0b420b031070101030340742c144058460b0b0080c04450079811410044080c11501501e034020861405000340300c0d0703890740c000806454600189114140c4100418095000c071458030340320040f991540c0100c1c4100c10511390030317204070b0041703080120380f800308040e804c80e280c0303216840000d44424101402d002102c2101000a5080400148035000c0380c00580964041e511302085104140320403140301c2c6005009100c010f1038200200c98210b0000d0400300103a10746017551640212900c0e402034010b01e8082010004980c01500443c45142d0380c441009804030104100303c01c8510034a00da5400982d02401106d000c0143c01c02003140b21700701012038103480b005090813403540d03020319000c0c0001440503141141c141400c0000041284544103816400d1400d00b07401040503006c0e100d00501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 670357491 1250 670356241 670356251
    0x3050a02240109020c0c0a03030e2e08040503190207050a0f0b03070807090b0703080402011106040f020f030a231e0d030c0c02060703031b020a0f0b090c0303070303050411100c0204 79
    0x2d410003c010344506c08034003810041d101c50b541d06000d0710050f8812603081c01581c40c070105079440440c100800d0320903852450030010f044140708044806001c0200300f01c90500c002c00031694800c0000c80c501c14000003035801800b0103800d220520021055603400704c1010a04180188120304034001600e622550030f28001b0304907600c11408070380300c0c481580000b1000c000061031800780350b406092244110300030f0300c400b00814075180c1550344c5da6004982c00b51201d124544240018038103803154aa455000508030f0380c01c0b003499129144c100e190981c4900310050075411b0200009402d03c00c00d004038826100310024240055000c0341c070b41d0541c0070795100b0103582d050640c40f1030b030250929044c001c2e00649200c1c0c4500d8140b9005d0000d140100c0040c406944498840d2040c510014030040380d56403141c91840168615902d00e040128050700d0301720b03a4019a0581c0390240c50803c00303810302c117000350340c04506d0342080d0400e000c2e4445103094480c00b4800301042002515048000c2d054410b070f0503038000078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 670358741 1250 670357491 670357507
    0x402040c030e070e0709170706090f0e042310090209070513140d1a040317061804060608061303030e1c0503091006090b0102060a06031a0a09060903050a0224010902 72
    0xc6e0340030190b0480407243d8900d0140c0c19083c503000403405c00781d0701583c0ba00c80600d42c071074a0301c0c40a84803e1241001400481c00001c000400e218810110b02d1070309903401205080503101c060070122009502950b407991050030005511b0601001034101907103092040c03034101020380c0c10132440d00d18001e03900302b01c2544000d00c0c2c8a0701d910540d080d100e6044912104002048880740c60506020b0314140d00007401e00060445010b1112003c501881d0003c003482801c0c1c00e010781d02442c642c030080c0190b420598400c40050720420130310181d8030a0f864940041c1c0075160500c0c010f001c49051055007141030b80116100960712032102080c0c00c1359401420160740703a5589a03140303850078170461040000c0d0350030400002080c110319007050000203404d0f001c0d2007450b514240700000320f80351480040e108039800c0500d491a0440800c1c1560445400c01c4080340c2d0101544451050b80c002c60740403800190001601040154103020201c010a070000409139440c10710300440280f448180a0810160750000c1d00d68 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 670359991 1250 670358741 670358747
    0x301050907110f06160e2e120501080313092d1b0906030f110702060c0f01141005040203090a060b0a1806061106070f03051513050402040c030e070e07 66
    0x49442881030f044039564645150801c51302c00b124883d40e0f01150b0100320525040c50041d04000501203804a00c08003080310211040990001340c0310942400075207104081c02c111380e40a050f002e000c0010085948072040100480d00e9030f0554481d5009524012401004d5170f01c4040e034540e0401c0c801c80d00328a90480941e01402444a00d1540800050403014450038641000380c140840e50117032010000c0c0c044a166030410b8509010309400610310400c01e42c1c0c014a0803001600d040c0c3d884600b160264140301209608469081d42800e6807041d4050400c141c1002c0e48244c54007074501960154110300307220350b182c0c0e6143c0c1001030040616480300440400c03030f214098048003c0181c022641406150b4400210040200c0d000b40e8001400e9103d000154100c0007903090f0048800c0c0d0f60345090300a40d158218010722014003010380008010104024070b0791200e00c119450b804891001625041520402044400705090746003410309020a60961800100740f042c1103400c00e000c990410f5a80305d50803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 670361241 1250 670359991 670360003
    0x603030f09040911041509051e04080c0717063111060f040b0706180201080c0f0d0f0c020d0212120c0d0c0503010305060606160809131d060a02030105090711 69
    0x100340c0180c80e01c18182101d02290655804403401c000c0c0c00c001c81c2d00c91013020b0180c0d403240c500303109c403021115012a00041058004114050720f071415a600c040e16240c0c4000d240001c1d01c8600ca00b46e000d070007401618922a84162009984140e05e900c50311078000a072424080c100394040c0c0f10820055070f109442e1a424212031820703402805003580c664035281e07000501c0d08031101c00c0c0c91071031806c4c12007130303100c41141c5500801e260144c6484c50310f91303601e03002c80c0c1a41d406007405006039501804008109503c80c06031894000642001240c2186d00d01030091070b0440c40307034507501150f0100c2c1102c0e007205101000c8448000c4440c40300d116a980d600400c02070342c4100c2081d4071071030789800800c0507030640c040080c0d4183c91040c3c0950f800c3c3e44842c0c0c20000d844c0912101104038041e504040d00014080718020042000d02600e83e0302c0d081c0f82034646e0b83c11900f01c1000030b05813014150718040b120a0134804998002c0c1c03e2034085003594148030200b850848001c161605100f507030401108680420041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 670362491 1250 670361241 670361273
    0xb070e0f060310141e0d0f05011803031407140903011116140a12030f0b090c031801061a070c0e0a060e060306070e04050c12010b040602060603030f090409 68
    0x90a0b50700c0c100102c501c416141688a20685005001c41190a43c90008000e84003070f501e0881e4402c5010342036040055018100304100c4201c2c45903212480014820b00607035100b009502c040f4000580319050280c00d45803000c0d54001d004034003c0400c5942c60f00701075502500201021f400d84c41e60700880c040f83c014204982c0480d03100c0c80102d8103840841c01481c001d107110303200da80380c4540b86040508040c1d460455203c01482070312804010110b0621960182c002506403d0f4007080001d0f035080031500c0c50307109941102c109800042080301900d01100d00d041e10402c1c0f032000f0800c180c50b100d481c0c1d8002905c0201e000e1802c03400240c04040c050013060340800f5121102104016040807003540008181d0f078452030112003903240c0018510f00d40425680c4c4515071030f45880802e00c2c0d44404000041c20001c01c8156695400e2220b5568160f1051240b4041c0401d903840903600c5080100c041d2610300010000c0340300e80c1c401c102030301c8a84c2198043d500010b0b4182c0300800c107072546d85007000e26001c0c0c001ca = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 670363741 1250 670362491 670362499
    0xe060105071502031b04060504060c020d0f05010911010908340b070204060f0e0a0507050c030705100e0a0f0803070c15141005060a140c06100807050603040b070e0f 72
    0xa03180010018983c01103000d010b080d02c4030707401d40000084e103900e03a00a910940300415003e20007000f8490180b00080289440101400d00a41c0a641d801440484171030054a982e90b40d11030301010060030107040c2e46401c0090034802c60300340c80c0c800c140c1e5031509030050b0700c2600c002011098014280e03445154085255103c01d09109540701c9540c1e450355000904107921940c00c10740002003540c07002e1100415249020085225540d490036400302816005e800c40040100401038824016801e00107400d601d440b0300b02401007540410200b00076541d004c10520700940000030b4000001d600c05d80950f410a901c240556143d81d5444010b4486150510003d4040a004131030181105603545c044207052140e1411f411198a4100f01440c2000380c601030540c01100421110355114040c1038a440c1081c114800c4134501007091304070ba07050440a0b80c7d0780045c42c07032808080c07020140500c0194041c0c84107031121815460300362036545000602804031001e01a881900d0002d40e1540b44442c0140100a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 670364991 1250 670363741 670363763
    0x4050f040207380a1404060e0c030d030b040615080708071806030f0e01060b090d020d02150301030506160203040923090d1119080f070f30090e06010507 67
    0x10f2010300440c100c0c10040d01d15554007000100e03c03030000c0c82004204403d405500140b5522550f60034001c14507075500c01744074401e0b05400b242907075042000d0f0030401243d07517012a054800109000580c0c9203500089000b842c68800c00756950351200b00664405d4152134039035242c0c5c841c010140c603c0386040d841074050b81c264400c0407030540d405070001040c3e071100c51420003000c00700088007800c0b116980a1000c03280d808024803080707403410240100000707000410000c000811540001d40c10400c4c013040004c23004c00800100103101040c01240c0d4401c01d0194107a170302c074080d81e800944038421070040d0809030340e991406021001d964000c4800c071402c1440c22180c181015000d60ba81c40b90210014000500d40b031907401a034542c0030404c2031415003203504103101514156501403898210b4100382d00d83d60000d00008010411075044884158000c810f03001401a03540800e0460103100500e0781380203c14002803a0781c05501001d800200c6000c0c2194002d5500c45100485551144c088003901c0a140c038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 670366241 1250 670364991 670365053
    0x50d020610140102060117010b03060907030c06090b040915080f100507090e0114030c0604031b0b0f090d060b03010204031a0609070f0309020415060f031104050f040207 74
    0x60018091003601c4808503100e40e89140c40510340005120103801600010010005109440c3d044624295813100201d880c43c2035802007450a00129540701c945d0780005420018401056041000382c0203510f8047c001b6403d0002e210f10520030791040303409155603100b204007011106120080a00815400e4139005070315200c0c19680c43c0354080540380450314000224144078012070040c070444013009850310740d50303103000c54030002c941010300c1e451380602590340280956511071000b0320203035200755030a400d003015103544202c01c000542c02c02c8952010821031212900c002c2000e1754400001103038041c0c0881d000e450b05501a000c4010142d40540c00450048200f01d4409086031004200d00700f03440c203a6540c241082058001a02c0103004100400c00d0960802d12a03000111104c0c00030304085180035000d1911441c05000350310180000781400c00966169a140c0148446602405486818603003070200040d03102640f03040c0b20740729503030001d149010020040440190205004d82d51080c18680c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 670367491 1250 670366241 670366243
    0x127111206010f0e09090f03030106021c02121602030a170a080603010513120504030c0b190e0102060703091110171003030f14130b04140618011b050d02 67
    0x12280106031100a62000140c16501c1140e028425125558800c100c0149040c144848030b0005000c030142ca0150040005900038200021350003020240c3c000c01000301c4c0062000d0b081c48c0ba45002604541000491005e01c01e11a81680c41c0c0c0c0318000c0e5000b1003000c0500c00689012882e000090841a50804000806c00030002038125005691100c000c15510102050b089460455100b4183d48603000c2003004640720161041351082c0c03509240d468145c50340c55994100b50745600c107400e42d003000540415190f91448083c00d5181c80d0b0700300707812161118030000c0e45586d0000c040e9070400d5030305c489040500c00c854200318450003000d003000080041004000303040510116448034902e03c1071022032200c40c0d03a03064080481c0c0d0117964401d99141000ca003200c111b0300c00e04d81c04031009418056450805048600c600080c494030746007a55891508080100f440c2c44803108502c540000e02041030080c416840b4400d407082c007480c120740c0c10550700c0e50852214030035441c0030b030140c407038025003251240d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 670368741 1250 670367491 670367497
    0x20c060a1d190803060105120c090a05061e0d0f02040f080c01050f090f0d1202060403081303020c190e0103030810051e0906040e0a050c10030e06012711 67
    0x800201c001d280d1200d055603501c41e00086100080c052541000d00400d0540c0055604054149019450040014591340352103406848104d845040021034170107914126100100409041c3d0707080307081c17401804408051200c42d40d40c0c0c0384035220025565201030100ea000408514001d0000c540b2140c445080320000c503420b0041606520030218801c9032580600240d40c0400c06084403146040411014050064200215542c0104000030700341d00141459245c2030301011503500a120620342420010700050000e402d1072110503030810340201103503004c41c030440e015500380c0d1070074824800719075941700901c0140d00000070381c4025400131080540c0240120702030140501c0d08070100303880350108150140301000c0782000ca9050442c1d03000302c0c1401020310b0b0f8055030060002822241c6034041508088000104880f103410200440f1514940300c840c04c46180a01e1408110910159038038556603a8180903003010100100300400403600b200d110f210115004910500c07904d4204021906150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 670369991 1250 670368741 670368761
    0x302130e070f0e0a05060301060506250b0f090106062a08040e0708090706020106140108061f170a180308041416150e06030712020403050607050a0f0201060f030206030a020c060a 78
    0xa045c840810312070b1a0501882040e00e40045c20180707030100c00224881c401290010056039a0303894112040400c8810414078440d4290b842c00440b00e28040d4041801c54036507030042400c5c0300e040040422407004614800003080b03100084260b00904904184000b4007465100140c0000c99500304022a54070240c60b82c003512403003080b203003400d4480b00242d080c0ca9560041c80c4045580d1500400198481c04407203410800284c140b40c8180175400c0281400ba042200400c042451b12812035000d40e100380c00c00c0d6001d624010304005864140c1c00f0310f80c0404992802408010f00074000c203060052110f102d400754007a0380201c6072146020244414514801e00c2400807140d80e82070361500c1d02d805142c450714281f20040c2800d103981e54607982503a680f59074070480e0396015070902c80840028400c10a00307002e400c15468444e1115001d01e00100071454112020b0110390421000304040301e050082070082d00d0f41101e9850301c0342e44511502d0028091303048110140d10a120034081c50070480d41c002d200305 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 670371241 1250 670369991 670370011
    0x11502010905160815040b041104021902030301141804080306031203070905090705030708010b0c0a0606081501052209030e04150807140114070c260709060302130e070f0e 75
    0x1840745c0120001c03049000c40d00941081c02020014001490070105134402410003807005082010004002900709510161900541d100000501000744900e000e411000030480c0c1540300d0302004006044072440203480100fa911001c408074803640d80030300c0f0b15124034000c14001516441c00c214000c2c600c40581c030406001e0386100c0c010420f42440b840481740320f062903803600c1010342d2030080380760100e0307000034008000e6029100c0c40c3c400160f8039000703040c0140700540007450041540360140d1407800c4c0680c4540c0c03154818520a88030280c820101840c045684140010302000d182020780d40702c682e00010360391052030035044004902e4807072051400e45000d10101c0310311503103a00c0c8101b40c0148119000d4040307032501182401c04410721009111882c46041814a4250350316034081c1510031024201107504030141c441c1c0442c05c0200064401414161414000c152440d000700d0143e102e8010344030f440c661900c1a0102c14081082045d00411040a0310480c40b0354584100c0100c0c0710940b00c540030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 670372491 1250 670371241 670371253
    0x20405010b071a0603070902040306150b0c0a030e0d0f05010903021002040f140301090503310e040609020f121f0b01080105191208040504050a11030115020109051608 73
    0x4001803000c2502c0b00640d2201c28032015810754405820151001440c059042c4158034001c01c1403810782c00504011403040c42c0100c1c24070481e00150790384c0203023500702c404280418000054000c60000e20300c500b440c0c2600303040b00c001c19100082515441c81c49400761008016503200e604000c0151b1040700078900940c02ea8040c80c0000100d64143d101d41e205900003104020300034805c1074440390010000000080c00020782e00c15950301c690942c0c000e136005100f0384542e00140d0088031000b90400f860b101481d4403c0344042d040040c41c03150f038040980040c080542e241e5500c4219207c1003410b4003c40001000c0d80c10000c0a800b9141c0c2d950300f804000749000410744900310481785036009060071020142c5030001286e00b03041c1407040246e81c906140440d10f01c10007001507041060790540c2c4003075000321402c4d07640d5810001813000b610b01c040d0030a480f040c5094000300500254a068a064030301900c4a10100100c002049001d4074600310044d2107800740c004111315400b92042c0c00303412100301034140e8030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 670373741 1250 670372491 670372499
    0x16110108070806060324180103030f0f1209061409031e0702030304030204230c0307090e1003060c020109080f04081608030711011e020604031d130e03091c02040501 72
    0x103000e101a260f840d003107481400860341e191074920341e1800100708840f40740d44a160880c001404000190b0049050101400040c802e1540c03049000e05004000e0412562040c1100802847c6005181c071a00d01d207a902e1020108105d4150405808003036900d8a1041e00d01b4905500342e1a54031003440c20b81c0204917000041410007840041e20405500180694100761a540902014000300c42c0c0302e6020350f01e0000c48100b410380704c465107800390582e01c0b070300d94880c40c24140c040d003144ca95030001d4954142c0b020400800d084045190ba040d00d0340010046085c107044041607014044500d0f0040c450b0a02050b0344101c20402400b42c8112407648040342d001e11203d41c4040116212030042c1c0319250000c021000c081280c8892003840b22a040c50021450078051404640b552a103039600001030300300400748030604d544090700c1d801291480030541d0080d1a41c01c001100c218400b148150819221511064940001c2c003d4412200000d804040c006414070400400c2d05580f200c02c81c411850701001103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 670374991 1250 670373741 670373747
    0x1060e030a06021b03030406020c241305121803070b040e01031b0e0103060b0103140c27030303070f020d0f05090d0c031e11030a050319051611010807 66
    0x48408140a806011032000c1901c2e0300d00603501c5500803250f1208642c21001405200300021441540100c03401030b01c2d8010030030305600b42020f040c0356440c003c4080709085204070f6400059500034010194070314140c0c1041c981141480500a0080d07003198000c95099660484d00280c0c20684a080381030b207082d1915600300320118000c900641a01d0210b0100500c006a2051441c610b1010b11009443c00725a41e91a61b41c0e10510903001203580c0c036201c1c0035040f00e035600360046070005100360300055050320307190440c80d1203030168a51101c2054103403100c3d040075103828080c1c1e41d49460041c0c00e0380da40c1d250040b0041c0140c44045040d0b80144101c20068550701d201d02600044482c0943d1114a001ca2000030001602041c1e4426140010070a50000010303d07400a980d1f04441040c50b600041c0034941400c29040d40d019080c00d0081d00140310080005a0200842d00314059261442d18941c0100800300c941e8026040e03070b44900c03003034814a50188a80000d0300c41250340266034048403995042c3c002c13 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 670376241 1250 670374991 670375007
    0x30a210c02070605030705041229040809041d0f160602070608040609050c0d031d06030105090c130b0c060f07050c0a0b071205040b0402010e060309060f060a090912080106 75
    0xc1005030840c01040c090f40d44920021600800c07240b929038206a01c1d4a0421780038010400101c80300100c4225281030259800c0f14910749000710780c0a00f180e850710340c03155540c51003814407651082d07550302c1078104007105910354442002400000c0b02d56580f410050b01da540c68148084200035a000c030000290360f80f00143d090b0540d0b40941c1d0b82031072500d8580e155005005800c9040f0744d24090b1a00030038540d29141800148071340280c0e40d4a5400d074603000744c95102c1d007401004074090102000140407a444060009030440743e00316849a44820705020100401425003200301044800542c140d1812070003d00e03203004032034a0641c41042d488003402980d1900c141103460b5480e4100410010109801c03854003584410f070b5042000d181d003655020301007214002c9808489044d4050f003440b0955a2000c07281114a00581c0c2003072441c103100c0c9480742d6400d130081580d4100810302e40051040c2d1190698440240f4000d0340500c8410128501a400342c40d030f01d43c068000559110000644034822816 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 670377491 1250 670376241 670376261
    0x1030215040f18060b0a0e1224040204020f04080102030a0c08010e04260f0d0b010504030c12020f09160e03060c12061903150c08010b0a08041103030a21 67
    0x10b00d0200e480c000c4910240c54200341d200d8145076443c013002804107000380041000100540e6008401c441b81c404102e5640191203030000b031603100c00c5143c6c0c0d02d560220402040c6c20310b403901e480c140d42d44a2001030042c1c4150b02516054160115000903d000e0540203507000341030030718003030043e07100010048440c081700b4441c804101c3c0040c008900070034076440d290a90000c40342d00c036480c4001b0a220740c1100d03070702c00070314400341550000340c2041c00d20380c5115018907894240ba04074585440d54842c0d56445d0030134040e0b0280f5950b540f41031000c6584d48400440c0701100a009081d4510300710903080403820701c521080b0085040d001e000c80d0b0342d14000c9000c5105054009500d13082a42c8c0000350904031000a0440390040050b001c120030301c0b0318240180d0700a62084040c08a6010b4085401080d20309803c4c0c16028019030740010300c80c441082003074074800f0196161507100c55965040081c0b40407804601e05815000010344540d40d1507202c00943c0c2c488400d001440c40203105080085c04a6444d804 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 670378741 1250 670377491 670377509
    0x207030c030305060d0c2d05010c0831080c0f030d12060315050907060e0604061115010e07030e03091008040311070e1006030b011403060a080708060103021504 70
    0x8480e90009000b68072080c4c01100142c2039000c104101d954008025020781c1004110785a000103000c44c80410307109805405203400d10700b49a90f40346c1800649043d400150080080070080f42e00d0180114004240610071690003060070041e1100c4862010540c180c05038441c5070040111843d8a410b108034404c0034048058020000044038103021121101c800102443c0607880b01400004559070a20007454040349050000307003800d04c1c0d26002e00d82400d550288080c0f2984007414200e9595400a503001c50340700b0f080114100d5035403003045041003030b0307500c140d425a6100c0c0004912960b82c1c401c400d10586440d01d0401c5640a41e00005a4078001d0000d425800346421205151640c4180c41c1e039608a8400c0c2021400c865010002d281000f04580000ca200b0000804201d000c0704100746a000500f00c1e401c0810500d05100300003000d0000c411003540c080301d00080480c9040e103800c4200d41c010320041c000e55050342d03160030b205034441100788000c0c1d10a644481865140456070304c22682110005c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 670379991 1250 670378741 670378757
    0x60e01170a241d090609030703140d0c0c06060602010b1f170408180906240d11031009020306130e032107080708091b0f03070e0a050604020703 63
    0x40c1040010301400480303505584000d82031079200396070b02c4081002030880000420241001140c2c00404000010b09400240d4403942c00c0c031201c41e170701108864a040d05440d0202e010107981e01200314070703c44d4441d800c4645140205848006d80e1142d04c3d034103400d201c1d11046c00034560b1400201d003030f038044204955202002440284c05285206503805481f0500d00340141d12001ca08101e684a203002c0310144c0c1d44000c0016070799070074460b041d01c03034100801c00c42c0e0b8100c9900307100340031035210240c0811180b0764110480e4107800015020080c0c1e810f02001c41070a1040001c5914a0755490b04195801d550032503000c180030a900d01140203980c41440090801e85070b812410340101d0290050122618890004000d2000c1030381c900500c40c01c0502c01c0b0580e6603076505060a0003040100c0050000c01000106c2e410301c03070192008115541158400b5024629500020001810310901d4100305070341481020000104c0001541403107200d5010b465082100b07950f450280000e030310446c00000c000602c3c103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 670381241 1250 670379991 670380001
    0xc060501360902060f0d0b0307030312020705121303140f0c061e0f031509070806151309050f0c1602130b0d1511070f03050a020a05070f060e0117 64
    0x100514226404a034039011a4624043d004100198000d00d250760000500280a80d4490103a010308260aa0181e0040203c241b440d280140300303428280464403001d80001d079010600604016814078054051407060741c0300900d805411407003803d484100d40d0401c003011030000510b404038100f06505085030240c1030981e0020200801a880141e00520301e000d600c182e03050708400300c3c0241600c283c6c518203e584c0e80c206401d40c1082c54800b2100d43d40719025260401c10082c0c0d004908680184068954960060400340c0c00340d814080c613407420714011000361001440e034041d0f422450013858100c414040c03544616084096a1081c1107241d100002d00d10a10001414590041d214600001e0320018100d05443c002601206228a040d50044500100c0e09a6034200384540e0101c5840c10001d01d16101082e9205444030300c1800010301404800b1134900c801074000e009849032107034800142c0b42c00d0380d03d985200c2864071b000c0c02603000090030030207840d4242d4010494400c0c4210110a8000f02c1e40e22 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 670382491 1250 670381241 670381319
    0x70c42060b03060103110409150302280e060f060309010b0109080304030528080d240810050408211504020406080619120b0105090a06050d03081e0103030c060501 71
    0xe080c0300b5003a5510401000403c4600c074800d401019109d14182c80d0002c1c0341d0f00410400b07088001c01d00000f2403851490143c0d484234502e210b400c56024080f94441540c07110300080529a00050854002d0b00c0041000584541035001000850782603e50070f180c2d41c0ca440c001641c038092070000410030780c000e400500d0108044d0700d191540702115402034808098560360743c1d184e600131070000a48903071140c0418100f811607224880d10031900684150140d171610314170542c0c039240c03003071502c440c540d4410204003070044c03140884001d409840c04440b10920014010030700b41d41c007180c9401c40342e1940501c00a140c03415000701c5c0d0840c0c1c021784c0e4600c641d441e2141000040400c954425001803c9080005074842c4200307a007c0d4024040e0082d001c1d158508400c2c04a40040201403000701d40c07078440e040c0507598650f0b81da40a06900761034030b1401603440e1f003a440040350310900c000b181d50f540b00000104242c0d101092001192003402d05004603640c0d00d43c1454890425454104140101c0d6400c50488030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 670383741 1250 670382491 670382501
    0x5090310050a1e0f0f0b03030a0815060310031e080307031805060c0c10020421080d110d0b0d0507050607020301020712090807080c09070c42060b03060103 68
    0x1011a07000210103103080c81074032110600c00c0894071151307111040f03002e0203a4140300b40782c80700c00744030b00c1400b220844400090b160b2090b0107081c0300740607110001c00c03281070b9580345080c90b00d000030305816520305040259103841951807208440c800640c0d0a03003900d480284a003503108540c804206400c548507101c0540140014600082d0358000014070340c000301d803003080300743d0003000c642c0000340c0d85803803a09129060944400e5502503541c0104001c000040c1d8103500c407a6900584880706060034075500d040d401e244604d4500c070030740c42c0c200a50b10050102c4240108850072800e001040911460b0051041190001d03c001d0f1040c1c00880080100b410040010078006100070001071802c10156030b984516400c503e2031100241d150801482219000c121000282951900501c3d0000c8010b002a28807a0018030b050700300046140310b1810090311403c0c0c040002c02032400c1e405113000e80c1400500d912103500d0100d100203045200083c003800c181c031451083c0e4900c10741d450301c9d580d00c0c2d0f401500541 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 670384991 1250 670383741 670383751
    0x210a0801050d032f010c090b030a02030601050708040b0301050f04090b180c0901030b04030206011a031605041206050f150d021c05070f0812091e040b1c0b070509031005 74
    0x74004081300d913840d100c000c002601c50303031280003034909521140c180b134212080b01c080ca01c00e000e800e540910090b041d10b4140c1c3c0e40140f49400241c0d880da01c42004891500800030020110840482d001c140030f6a0000554180c0d00280d83c8640d151f1088010032080c1d0300100c4001c1d012107504404603003040105100e42c401e8003000400c984580805070049101000264800d9032001c1c0c3c1c42051004040d03060042a0040c2820307003403800c1c0c81040031800c1d1a1480040c22a030650403240c04101092401807058400511070b03080005190f111034200400909002c4449080b070103c4c0600082c4c03003a018850750074030b1410152146507138400950a101202c00300c2c04440b107482d0800c415a000044007088442e000c5d180c0c0e00841a05141380950061130b2010555035400600b00a100360105612040303402c03c42900e0840841d10000c84400205000301107880410341c1003800076a09510070200114009002c0307200d40c11040c01c0f6a900316040b6030078050180c0c095070680064509408103034898200c1030b004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 670386241 1250 670384991 670384997
    0x32060a03050703021b0f0709091a09210306040c050a090b0306041b02031210150f11030a020718090503092206140910060905010c14030705210a0801050d03 68
    0x2e0a1005140410a1a10349076505135102c00c50071b43c030801050001c18010601c6a1041c4400b00ea295640042840e040c10383d1801519208001042d02d1820005505040c500c201d860b0310004101c8420b81040d402200c0f039a002e541884c4e00301098a10950856034103074069620380100d40d060500502c040da0018000c00e5001c5d0304d424282100968002c58144509419002940d44401600c141501c0c281300a0101c0b10442820504104100149402e074010304200e251241413090f13015401c0c0e441520b446244c00c584c1c400800c60310802900007800205903180c001032040b0401c03104211500340c3d40c82400060950f003091112a0a03400d110090510710003280344607140703655103490508115501c5a1081c440b002040b0342c009001c1c10708030500341d0041c0b43d00720714150150130540080c2c201085849042d04004002c1103160501c0310110306030304480001400c0c1e91740c460a40c204030f41c1c2c46840c0782c5030b8001070310400e00e0945d074400b5074011a5040e041a0f00c44d40c0c0c0d03036882c02081010108000206400b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 670387491 1250 670386241 670386247
    0x50d090e070f0e0301020a030221010803092e0e030709200313080d1d0a03020a0311070f03080901080f1003230610091b080c0c0f060132060a0305070302 67
    0x184d9083c000782c0311800c0d09940c0103803240703003030740300700c0284030441381c06da500300e14800014800c80c0408401c0381c00f101c034180c030b003803801c02100f0b0750440300300100002c803494171a100d0306034040b50366002701000700000c0128101c480058807558000c046030368180a0494103500540f0241201c0b035040083c40d40705c0c0541449030076203900340d141c84025500c4031f010880d40795034a0100b0494943c030f1003e00c4c4040a1420000c200c116120798001e50344041c2c0c0040601405004503a0404400b0204045400b40580d030000035251962450242115042810301c0350101d20150300086144a013603009520490036409401400c600d962551644441c841c61074404020040d43d1080c100c420030800c0c0d9004070301d0b00780d42480d07142c90f01101c41d0440390825883d010306c1c4084603100c8020390707100c22000c1c0c201c0303a00e11072995030b0300403170b40365070701c3d1400c0e80d1114030813401420000100d030240440c40780020100c0e11a80c20380e9142c0203085203180240d105141368441c0e0103101e42e004052003540702950000541c01c006103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 670388741 1250 670387491 670387517
    0x112110a06090f0f0501020c220207030e040b032803090312020303060f3102070f050d110105130b100801051003030e0907081f051c050d090e070f 64
    0x503550803035004034021030500202000714503410000000244601150083c0da9401d1200003901c030081001c0e194814141030769803040d48000208606006105100c085599642c7c44c07401411107140c0416051140c0d24180082000c2e041c0030980900c90b08089400340c0d00c0c1078010b0f180c1240c800100c007069080142c045408000105003030003000320451075400a5881c2c0c580b0b64200f08140e050036031000d0003051003005000c401c3c4841e00100d200250444403d018089070145003400070b002d100e03005445141c40000344d00c00d2010200c1c0b5080c0b03404070750b034942181c240c40740d003100d0a8a030183c80003000c403c1caa16a401c00303e8460710510781c00138820840c00c075681c1e039948502805d40e141500c0c2d4000d400c4c0c469108004041d0132400c4240761800130380f2001d00c2c92400402c01b502c00c00c40105030400c41e000d4400b240c00d10310f40d03c00f00301d1b001c0d0000400e02030080502c1c0c000985802440e203411207007031242d110248025801008041c08036880c084280741d440e42c403080308895000005400100303218460075040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 670389991 1250 670388741 670388749
    0x131103040f0209160905041802182509050418063e070615092301080102070f12020a0525121208070e060304050f0d17011211 55
    0x6010303602070703000089401828010000303100c0018028051071025107001c442d485030820f00309401c96004503030004101c4c41c104400c048085140c0d4000b540b018560500c10801c04010035514002c00408100b0b00c010b10003140d051801c2e20300840f224000c1500e035081003002d441d1941041d0001200b24052240030801961044155200582185400341919800d958440b4006104031601c58000c0020884604841030000c203621603100c024040300c0d210010544004550f002c02c000500c1d60403001c01000b00303440102d107007040c5800c0800c1105520500000b400d04414000c2c3c808654015800744440c40316a0f8a500400701c13520010429802a641c0c03020210320103024800c0c14a801c2004846002d591541d0710000d0405a00145200e50020000308042107041c50542088151401d00c254a0f4403a41403c3ea0003000045a603903000200004100802c840400d00e078450030bc040013282d602001548055490490346807034120000804001040201d24000405996901a20b42c4200c06021031001c030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 670391241 1250 670389991 670389997
    0x305160206040f150510080c010302090a0e2e080d09030506060108061504030809040c0f020a0305181e03120f1c020d140103140a081815040f091401050d021311 70
    0x40c04668480e4542000a1f0303030f06002501c00c03a0002d203011407030304e00b642e03000a6580d4020702850080c004640c0004054603030010030f01d903416607101e00540c1e211103094186201d818090060b101e04e405081da03a052018051402c141c15654014060810340c2d0b91100111641d0700c00421043e80641c40580d82e02c1c1e01d00b0114000c2000d1806001c00750b6541542e102440305a8a00401d00c1041184c1d449070210716680c0443c2c05000594149003190347e1710b40354001407055007c000002680582c0401c0f401c03142c444191103100d07850300240c00380c800309480b0406c98038a81c0919031103031741101030030001d00254445a01603962000f040182c01800c00001888550482e002c0d04002c1d060492614014001d00408101d40155007015000501c0d4600c25540c52040c0c601400141c90342c1e80b8180c101d01034060b99084170368000440d140c00c1c581d484560301d40c1d8404100000e03210300100035251108685042ca88026840c0c1643d101501e4120242d51075030a000444880d89044004603a80700c3c0d001c0348581e018401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 670392491 1250 670391241 670391251
    0x9020a0906090f05060603072a050105010b090306070206011406090103060305060106170f0103080d0f240f05090c16080d0e070911090f010e010e061201060305160206040f1505 77
    0x50380101c56544804131813015103e5071040c0c400384100b094165000c034030240c1a80c114209400c4040c000806c01884951001004026501340340001c2240d119440240c030f0143700480c105c504986846909a03100d403803c1c002c0103070b803a082e10700142e42810080d009000c15507041c9800121f0035030703903201d0a041c2402038220b0400101d1100480d011412100005900060309003064a05945956030b014a903100c3c000300750701e0b81030320b4880843c2000180d0b40012166828420b180102252414001000107614001e2280310300881d4030100d20380c108079440607c5030b10a03607450340c81c1c0980048040d64101c100d5100310f41c00c54080107034200001c221300074480301d85264001000d000781406a50010344890781c04452078000c0a00081d5019940d40901c544022030178240420041a0f15004817418106911019080300e03002800c910006107409403d4100c68095a080213940c881860481c02c4070180c040c1000103070310081c0420045448003038400c00c0e032442000010003070031706180c00e00d054604c100e803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 670393741 1250 670392491 670392509
    0x3190e06090c06030f0106121803030504020102190b040f05010617010b01080604021206090402011101111801080403020736050906070504050604090518010e071e0b0a0309020a0906 79
    0x81c410700101c20400d64807000700844003103055180031303e595074402c80144034860070030042d0f0040384039402c0c180d4007981003100c0c19414400b02e8452801d02a029010a541c200c5c014030413402c003d0042444000010a2294852041003640d01c90b6154220140302000c400c0e10302d13540e0340700005203a0700e0b40c601c03007460340320203c00115a0301011070002d402d814000b00002d0089004210381e85502c0311100c11030760300040840d4040d40c1c03a200c6000486a003100c504105505604e000401543c0e040003001910721058a0ba2010040e04010001107800401c10354000300582d001c00005d01446c000f841c600d140310078000c66030059065070490075025030400c209256035600e07134490030320141e02000c0c041d803540003100b0f061551406282c0000b10780544210704c25100f90030f90313810105055141c0d08644401182c43d03135000340205841c2d41c04c5140c45107268814a2a000b60404407070000720644042c0c203040398418403e26040142c4410160058104068120b90200741540080760b9040e85208000140c08134074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 670394991 1250 670393741 670393753
    0x402090f12070f1e181b0909271e0f06020711030a12030f0f09051c140d09080712020c100e06040603020702060d05250c110603190e 58
    0x140c6503151030380454000308484060780c0c6003181030380744c00c007082812900070354103030051003d03404002d8004182d140d08601942030780206c0c582c0d079144d005c241207060365080441002511003900541084414018585108804051072603010800720382c0613420840e00328240d80084c1090f40c0d504140102c8000c1c04a0702640d0100303140e010300801c40300c0340d04005c9098009101a001300d4803588103d0340d0b082d5602c030405846400030444a1810b41103446020080350050281c0e010714076019844401e80305181850b9010300b125102e02920038000c0c0c0145000c0022824a8948910310f0b10380034015404041d6410002080400d001a45419400d4020941a03026000546003041001740041d0304444110030440501e4801526a0b900d01c01c403400c4880905006030b5030100b910210300305003d1955205945460401004001104060310b600c1005000c9944120303d005031400395040c200d042d0340501603202001c901c13195130a02100654101d1900c00c000110706003401040000d130750b9150120344035a0014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 670396241 1250 670394991 670394999
    0xe03281202061005091f092703050409050a020403080c060a111e09011b0b0403091d1303120207051c03060308031f2d080705030307020402090f1207 65
    0x50444554500c166101401041c10aa01000400c52150050921a0082c000403800000807174482c46c002545200411500e42d0f40c1d00380c0e8600038841900000b844401c048442100081c01104191049030305803101418141820501401080001c1900300c40b01d42c04c000c04404140070318090401801448010442840e0008442c02511000c1c480200d5020040c400a401c0b000c4003101401092207940d080d540701d400c1e00e401203845520802000c000710307486200000a111034402018412402502e8040201d940c3d2403101c18414641b0504074841e80240c00810901c040b49100c2d04040790203482d02d1650301180c1d080f0f5104031381c0040021910b5520000c565440f580c5003412a156109490400700a51442d64480c82c90511004001101c03041c82040320f030f0042041d0302000c0c0c0241124000440010000e4001c000b500040310204850081310341800045503140000c8400c00d8400c050302450800754690700f8000030750008a106548500d071400ca0410036240c0151601c02d001062006003901860 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 670397491 1250 670396241 670396253
    0x60f03060e0c070c15020c0405150907021027030f020c04050109141b1b0a050304030809030f120a0513050301050f01060807020105040b13060f060906171501060e0328 73
    0x503407100c5c8035040c0514900940b2500071461000328881940c020485a0790705450f010081202e11286900450107001d0010240d80000c032484030001c1000100686100d00500810703100c0c1e03151556400619581403240000e1245071041c824046030f004448492060600103411f40da026044400215a5500d0303102c5c0c03100b08034442942049110042090016a28140e0700f40b501c5103e2465441d0030b403854040d0040081002483c00751034100301903940b10b540324680940d00ba0301128801d031091040030020b004030f81c00405c014070ba512200068074907081d039a0005941c150450140c44d07110200c000c10005150b10203004440c41845c030014621459810071784c020b880a03802070180c20845e0703d08020800011007a0265a422101024a91405566501d0040302924801a01840090030110001000dc2ca01d403c82c8003607802d94041d0040581004a00c0d51b0360740f410007012117007a04400010000140a1007004840c2c8001405841c01c07084000c6040312120755002d440011410700130380304000c4c020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 670398741 1250 670397491 670397513
    0x103150b090c03150a030501090803010518131709060c01020301031211070e2502070f17070e0402120a080a08181e030c070315140f01060f03060e0c07 66
    0x2021100300a280c00c1c031000b01000d60200a00540c00190452034001c0183d451505c250001c40c0d221000f40800d60443c034002803260030a2203076500030700e0042800d011003401e00481e80e20640100d0f00614000000c3d8680c43c00e5a00c40c2600c14500360f800f0000b4004685030350b4010041a2221000981d07607526500e00800d0b030400c5a201d0f0304c1000801f11550464040220b200f0040795580c0a84030311a40341c070044003040800c960845115201000000030455402280c4402261004102d518409603141d149074181041101c08041035088248103001506107403007116001400a49081044900b810042e0716104074a6401d603000c1c0001b0030b040519980c05444c0796480040d4040020b00d0021130004669200100c10140024029401031900b42e41403c006442500140c0c1044401041e501d0a0105c40c203003200a00080d080e0030088041c6046d00800b42c014024400003942d206160b1a0010403103082190004000c00c164903407000052541c0301c42c2d601400380c00072000c802d07954402d603d81503003050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 670399991 1250 670398741 670398761
    0x8010e0c03010b10081f080a0b152d060403031d100c06181502300613060b031602100603200607050304030308060a060c11060a050c06010315 62
    0x6030600400c0c01440d01c0300c51241c0d941c1145401e00807010745030b07245094010000802e14001c42a6103600000f47c4040004d4046a014001c0407072405540304c40084038010131603101950342241c044081e00500d41440c0d48038800e20701c810b10881083c1c000c4400000c00c5548560310035800580c04080705640c110074450103d019071021280b00e10b075a07143e0a40a01881e0380600040c01c030356641c82d540320f5564203495011601550040404420407103611803000290040c00e80b0404044d800c216058294541d0b0b0990b031084210301000324010f555840401807080c1d102c003009549640c81e01d1000592401c140c000d140261808000c9038510b0742c65501c000d1825803a003844020450810a0403c04900c10030481e41e01c12070f110740043d0f00d4035000c10200314a0301c00c0110040c400d1100040000038503520084c05401500e0031a10b101c049695078608452040f0181c40c05401003074032807039803030311031900000821424406091182c00c00c0b0140c1483c1c1c1c1085401d03841501c10040245100300c00c03c8441c8144e80b600 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 670401241 1250 670399991 670399993
    0x6090c090a0506040f0c0f090f050a050402031807062318130b0312130503060103080d1e14090706170103020d02120a03120b0109080a020906040b0a08010e0c03 70
    0x90241500203403039440003800c100600d035a01d030040303005502c031a001807914800e00c00080c010300300c150130020a540c200c400c010000070090f181c0803581c455011030020445500a202000341801c05c010080290310280014809021600b000003031068103100c890010011502d940b0b0040080f0304a08040c440c403924181c1000340c0c01c0081c000502c01c1020a920f11400660302010381c10440400640280105940b00c2e91620450b0204ca0b00c0e45410401802514134100c1c0e05d44000b80e449080c140d40325000c0c000201400c1c814441401e80c030500e94099030351580e40710b6a402429222120020841d060441400303801084c140411100c04000c02c000801030400745403400240c56001c0010440f06010701009220f504286c03460002d655600d042c480003503200c481603c0e4001e20760315003e001c0407840390074005110f0130840f8500d40c0c0d6000d03511840440300060007414414506071300f000301d07020004261a0b8070542c8e44c91b48603010f4035041014409400e90200008141c8101e20720a45004444402a072203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 670402491 1250 670401241 670401253
    0x13020307091a030a09080d0e0606030712050a080a17040503071703010f0b070c030c12050c010201060f0501080a0e10091b12080c01020408010c030209120706091a22080609 75
    0x75424604040704d901484880c4009030544261410000512405400280703030b40c02c02e404e0301c2d940d080109040340151400c60407505015900c4014400c100b070003c00140064104081040200380100020003616840346801c080d00e040c80c03410701d0441c140030313181034038180c0c80816040c08000403c000c40b45105200d1011605540c07400c810785032801c07140e01031295000c1d0080b4480042104400040c4082c1d40d22603161914191681d0410310304044449040d1001d1041d540c20b40d02c1d0b0350041c0324120613540c00740034070010ac50600340152030800c03001d0300301c09042e40e5443c0c00005000080c41002d8200b0105c08001c02c3c000c41d41d0403c6000329030f1307203030016181c4944a0343c100701d039010451030f00e401143d0240f61580c4501007603607114024004c5601c002595420b00c01d0a400455256006000c901c600300c40c40c0d1a076a020144c0155a62024010b003004502030300418032144103200c413800342900010a5003894076156220421016021903510060413000d40810f000300303a0207100c2190321540030340080403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 670403741 1250 670402491 670402529
    0x815010608131106070215040608060a0b12070806030f0d090f09150e0702070905010305060f0703021303020609120109060605180702060f1e131b060507110d021302030709 75
    0x8054680f14454520868000074031000319141d800c0030060100807441060f41711070f51040301500c10070342155020b204001c402d40108150403020245c51551403000943e140315668100252442140648101e82c58031880030f0031088130008100707140035280a40d1b00c4502151404040c1404507800303070011201c50f82001a00b0f101580b0b880390510888400d03025034101074503400070907400d00760250001706140341090004828440000386590065070b1803020107071a652104c0e4200c0482c061560303403000c2c40c041d0003c1000589050700c098142e00900034501840c8100c10008203084a011200071241603460b83c030100410710f02008a10b100303c845d0461608980382401c0002c1d143c0000500c03800300302c000480400c000150210503080b40d0049110a071181d41000d050114496520b41400c4a4110262005004101d108549030003100d069071582400c224995946a001c0e4201781c80103904059070744405005a030320050030b501e182980b42c03001660790900040040031502586c00940c41c0035120080e8207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 670404991 1250 670403741 670403753
    0x60e1005010c0f0816201206040308070306080313090b040c271d06191214010e0304030813140a090e0109240509062e081501060813 58
    0xd0034869100f440488100910314141419000c0e01032400b07040107420075030004101d00c80b66018070082d540202c0a45940d0044100000344280d000e03203032140e401a90104001900411380340360800344605000ca55070f91140d9880b4610b41140b4101c90048890200411244d03446218074200e01e0720948080c0f00140e01e00001420a80e100f80002c07911a4821a900c270361300484100c01000350110011483c070850b0302181104064005075001842401074803120071060f41c02456190448182c7c0044075082140c544a125480d0001c5860000b035540f10080c40014102c280000c202440c8a061015201e20054624002d00708a0b41c10a105d201040880903285648400a44040768824000420301d090746012041c050b044005000b04861400c4d80010711400030004160100c00005408100e03070f923200d106940e038600c010380c0c0044d0601c801d2040035003d802419002c403207945102d000b1802241c0e840c0c10351898281c2c0d9003100c1d036109040c90010f02456a21440302a003111116a40d100300e03004c9c1d5200c1e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 670406241 1250 670404991 670405007
    0x190c0e090606130e0601090f1a0f06310f0f1a0a050705070b03181f0e120406020a150e07170c06210702030c100b22060e100501 56
    0x201c0c0c403c64902c40744040d8180503404c2000065150302c191105542d56049a0303014100c81d005020a0905042e400150007000300c40094905000902e0b040c0e001d8401d0061103001e60010600c03480002503070850300b01d07601880440740c10442d6401031109103245050004c1c2c41e580750b280c000720301c1c20142180401c1825040103c0d00c1803610402c1d4002c2e0340b4105200f040e0703440d01c10f1400c001c00070300442100140001814000d5132081c21600c20076540c24295115440c1c440b0341400b0515254021b07100c051202c60711076801009141103400450350103045900302c24559802580c00800181d00440c03480d0300300130b0003d20b084001c240700c00b4103000c3e03441311a800301d445114600400c800406001c1c3e9100410340100712045185001070001030361400340c0300c03102040b900030361900d10089030347c80042445544008200c410340c2d501d40c0050300000f2402804c08c00135107445040300d580708148880717824140089440104042002c4800000d80d02d20b4480620341d44034008000401c00401804200010b9801c0040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 670407491 1250 670406241 670406251
    0x20f1c080913050a0c030b060a0203041a1204080904060603060b0d0e2d060601090e0a020d0902040c030203060301110c031e040b040f0810090f030507020102010b03190c0e0906 77
    0x146501c42540e800402c01004055007100510b505090a00c98020b5540e0301a141249036030341c084c0701d000843e00a11960344a081001001a40204410000c0c0419030303049000d00d0001d10f10141c0b81281c21260f44d264440142c40c1034500000026408000b80f510744102c000500d83d6050030b001c41c51400701804900d01454120214007521070301c80010050741402691407441e80300d407000d6150040c03011300f084103054840d000c0417140314144c00300300b041d80242134000845408210110841e0742e00c6000034081d400052142c810300b45c90300036940050303845015906040f0b0041d600181c40c2e01e0154100741c01d48418812400d4402e4080103001e00942022003107034140d03404400c0300d440ba01080285540a07105036031243c0600540400c022440c4405103000c82c048400d05c0048030750034041c540c5403104076469868000e215031000300c4003034000390140d000342000c58014000001d41c00c051a02282c00c140307150810182c3c1c0c65440d4110410420004d038580c016241e5403070314414038604103254035510840605 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 670408741 1250 670407491 670407503
    0x6040b070e0307080d090303080a181e0c03060b180403020c0f0f030d1e0509030a060506060d06080c15120103020d021215101d0402040c0e0d050604020f1c 68
    0x8000746441c00c110312002032904004860107440c04071801802e00d040d0340401c03000075000001096100106014a80c4d071091070b4412405400481d594000da0342101c4419440e2a162208032403011902140300703140158040d600201d0107049070010018810b02110105103655048024400803942c001b07075200b0454070943d01c800d02e000c2c040c00091030054040f54000e5151050b51034102450b5808000000e0480020030000703102e0020941c142d4a030f0083e0030b11950154031924601307000c100c280d04001d40108001e44454034050081940c1410f8030b0441d044095280c0c0050f8200441f410b114101c1c4c6809400d150005040c140099401c0c8031602040c400607208217600e4034070809550311086203041414614044941d20020038240104858003140c4041c40080051400160240c40701103584013202481034019040e9510350822000706000800d400030005074182c0308003141c880d05130554584d402030000340510718081c410051030205c0071540900030350380d40701c1c4442030003c0460040c141720380c04a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 670409991 1250 670408741 670408757
    0x250e010e0d0f0602180d1511090409050a050c030705090105040221150306070c020d060f0b12030715020405061801261005031c0804050a050d0210050906040b07 70
    0x4009085a41d680348080d040940307040d011003c0110b15402401050700c003150070203060a40d441000710f04201180060210030800f180440c080c2c1017548030302d20209103501740d82d05014548000ca8102d401400c07080720154002c222003001c0c004104204003004a08a004200881c20003010a03904101840399500550700440c0c00306c11300b1100d441c6c100e405071a615500340a0f1a0003100e44055003260705416000e40a041c000ca006644a04d144803c266009885050000025039030f070b100500002e0900f0808580d15509181c141c2d48001203600d94990b078034011070b03c0d44101d0804146814008da88242d43c03900c10441084291104819960722001e42c094640401c809000141e8076001507490f030b9031100803103207000101c3c01c3c0e4940425000b156020040e81190340c5400c14190f596000250a00c4107440c00f14102c941a032007a140c840e4841c1c4070704140c814244450355001e2525000e44201405030b004100e030720022034510f00c10703942d0000c0440028201c0c2e0901c0e480d0420741c201e025110b481042014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 670411241 1250 670409991 670410017
    0xd02070c1d1605030c0304020d1b0f14030705030a02060309010b04050126011e0c050408030d06080f0a031b2105190309020a060c0212030301060503250e01 68
    0x10900003008218000030110201d030000c8040400c900d0072290111031460b03118010700424454402d4034820042c100403a813460700d07550204216801885421180c0800079086169088001c103c1c1f00014400003103240c0c909410078a000044003010728085010741c1c041c4000f000070303540004890114940603111142d5036118441d02070b02600c80d403000c0d56001800d14000058905186001d021080001d2100c0f2030300c20810300352242070b90b01c04441c1c920880c0325804803240350314070790b401042ea201c07840c1021854903960300c14650450b081906202411a17a40d1010400a0814844510f4180d8013901078022945180d41c050040c2080500e10024404000001410001448101c0c0c015500001d100d40c05282007403801405544228030f0041a800042d00405101d4000c1c015081c3c0b01da4010108519035007004001c80300888045810b0740e00c070355241c0d11000d0800040c4002c50203440b840e640c41c0d991303140480d407a51441ca05100210500190449007641032540003164400c40e807000d1800117860700708 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 670412491 1250 670411241 670411253
    0x61902070902030411040e370f0c050a080303070903150209060c0a051207020a0b0a0c0b0a090516080c040b04291905010c080d180f0b16050d0207 64
    0x9070011004203100000348001e1105500000c0c3c038110003150705001d100342000c8203603110318001c90301410100c00c421029816034151000304207240f55502c1b0540d001c803069203030301c04440d00204043d03d041220502c1480300c0c4c2030541c3d20101510700c60340114658203195000600746821480050803104030402204000e00c1d02d50104d40113070f0f000038002502c42042000554690101c16011901845800d010008002c040c1c8180e89280e40c004025a0410f4038062454005505c144880c40800c540311104100048091035000e005000b0301c0340000d4040090700d00030785000710f030807110072410104030002c001c0079000295041101c0804c0d14081640000d0300081401380c521045d0145014008a000f204508500701d0410070a55049401c594401920848282c0d40081e5014541c0003548005601001c10040c0c4010032041d01d0010300041c0e0304885005119180341202c0c3c00312603071012310440c0000d10900c0c0b0282d80d000b0403621a10682c0b080d803141c018182c0e103e41d03401420080e03004207840d000d0100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 670413741 1250 670412491 670412503
    0x31502070c182a090611070b121602190f11060409020904150b0a0f05070b01180e07290417010204060914090c1c1d0c03060402061902 59
    0x1003a054816401e02c0311081e6802904102d07802100f614010101c948011040c1c80188142c0041c0d500c0f20040c1c41c1c00c1240441e03089a401101085606c103005e000600c4029030b07802444036094249010701c0034140103000b01810240303040e1403421503000c000b0480c46040da01e0100400d007070b0300100400d0308661515190a10702403402202d64030000218000510303030016002482964400c850800c0b00d00607405140420460500407072110901c10b1240c1000360f0f01800420540307415604241d4100b145a945440c9a01ca090300010020a04034903800b01205050103015000412200645010b5080c0703007682d51050100802c00f094142c200c848900520140c00880700500300300482000080c1e032840030180030790b0003072040d14002100b0700740c00a43c0082444c01c0303100c0c0301801010b4104603140c0d0030350901650095005482e000543ca0038014201a941c410a0b5003503e01c040220155804d0210307031420710541007629030103504003504120043c2c2d9080c040b144801295000703842030075040c0030304a02c0c1c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 670414991 1250 670413741 670413749
    0x406020f0c010e04050919060209031501030f060b0607060f09120c150b060c0106090b01080c0309060604090606050402070f06050105060705060105100302040f0e040b07031b21090c0503070b04031502070c 89
    0x4a081c1f0344240622050350014111038005a08545220204a22092000d00300340300140110755250f2030140040c000785c10922451100400380382c20603d4544840041301c50f1000c1c5045040c1e92402140d04120804c0390f206885075140c00c19550072291b03921418100c2480064541040d41e503000000c0c6150b68040135550316441e01d000802080362513290741c03001007c05a600d98040ba11142c00180d5501380c0034200ca10840700080680040c3e00d4407014480a00744c2860211521500d03010301151517183c07440a080003034060003210211034101d090400031594180c000324083da03400c01908010482c0081c00a04440069650300b100601e540e1040700240515000700c80401c041c40000590010342c015020301940c0101030385c40c40e80d00da080d826011900c880c00440604100034800c0c841d41400386100304500707100c1e1040361078042e181ca583c0300110b8400100c101e030030070500c3d813007406241001c020040103401032a450514207425a243c1c00300324900002c0105074940c00054810420801d10f107100014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 670416241 1250 670414991 670415023
    0x7090b03090d21021c2414030712031d030c03070501120905010507050d110310030f0201200a05010609050708060d0f05011407080f04080a050a140403080406020f0c010e040509 77
    0xa005c1002205010140614011611074140005d0200342c010700c1c1032901503440d801519135082c91525490301003000d060060a82c0c0344c065008000781130400e520b03880540c0b910a40e514900070502a81880382a2401e20315240282c0c03008154006a440010302035050761800d080c40c3c0b02401d041c00c0340c00e0242101e03a000501039428030050104290b0400040c00510641e00000e00584480800c8191a8001103520480203070903411b0800102e0f0421211580f5a40185400b1028411080108840c40700e5080120945da000c0c0700100e09014080c40b03200c000c1c05d20703074805000300e08020390f0040040720090300c00d511030240103002c00100b0402d02c943e4845070b64010b00034484061000c41e12a0480303230840e0307000040b800510000380d107070f02242076043c0700b2580300304981e0500180da4002c4425401003201c58040c01940050400216041c1e00540011032040d05c05603500c9051900c02401c0c041e00040c03507141d69010400120490ba0812001c0c420f014065a0000c1d6540e60100c0f060b00e803a50409406000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 670417491 1250 670416241 670416247
    0x5180f030304090b150315060903101a030d0323090a0c0905040308011d1603021312060e06190f020d0212091b060d0b030717030307090b03090d2102 65
    0x2c9035582c100313008801c0c048403502a4102260021344240c4800c45841244070104003141c0c02c00d28003000a00b0141401804480d4100703401d841013030445070810400c4001c151206450002c9140401010080c43c1c17261030700b440040f20f03000217114044480e81c811011144e882e000111130340410441c1d000310f9030b0031440740e09409990f020b800300103001c15241640002c6040c40046506400b00e0020000416402040d11459840c0c121545c00500280704a004254080010b04403aa0008500c4009031071080700f8030811400d02c1c6080c038106c0d82d0f000425210394108804001c02e007442500001d0350400f665001080300282210f00e40c2c001e02c80c0c01c9406010314408034048480900134484144240d1700001126410031607410042e00100c42028211341c0220104420b050f020034903003085078850005000c0701c41070785e01c803225181050721009024602d0751010007002826603100000c0b10003016648402c501d182020310b00151202d0422158105004010380e01f1a810500c0e106101c0c98a8441102191 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 670418741 1250 670417491 670417499
    0x303090d0f0314130f05012606060c030a0503060f2b2d060f052e03020a120302011a2116120b06030c06041802070618050d0c0305180f030304 62
    0xc1d80c1c184d4051001800f1400001041d01c0d40111114100d003102038000c090041c482418661030710f070001f0407a0b6040304050108240150f000c00141160b080b48ad200c403912803401c041481056060108880d20403407101c0d101408107460010103080b22490759000300044050750811156008420901901c91440d004405190490240301d4010355442603005110020131110480b00759031080d21292202d000902441c51040410045d202c1e803010f6840f01d500c1c43c030781c0e00e40000e8001030059100070284502e950800c02003686c284607240346000c4160040d6050180c900200d901d911a08044030b000c8000c55240d040400c0c4c04101040011060204540e400d0741c48014809000344003003412100600c41e10301041c02c518000c0303400307501110301901c40ca003414a4038035460f1098000a14415206508210311400b18005006041c000c901009107141c8044052900b286000c80e1207960f5001c20580b0440300c40025444400c8833010658000c90250490107840094000241c0c942c41d80e0f80740c400024005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 670419991 1250 670418741 670418767
    0xf0a0f110a110909070803040b07020a09020c01051b030c0304030c0204090b160201142202011101020a0518041407030203090106080a1506061803020603070504120c050a050303090d0f0314 82
    0x8500c00342902c0c4500f0316165840d0701507880c49a0b009600742900144014801c880c64003000e4690680004e01c15107480756101d190800701d03806400c81d1001d5944840c10401c101800c400d20311000d0404420261561800f01e184203c1c50001802c01001c0110103100c041c15552070790002c04d411504660703001c0e00da05100b078150b221141c01103003880165003080d440300c24004095552a22858801c1c054045902200c403000e0540c0321802401ca0501c401c2944810110200744050000028107807141981e45042c02d2040c00034224105411f40702c1c5081c1407158400d03d01c1c0c001802d0308008036090258481d2030760b130007841c0541141d4001550500c10a6a83c0c0207010300c4443e44400303101019070030031032580c0703510003150602d8032000d8981008814540800060074440d0056510124a1900034201034462800c280d0f1440d02180a88281d184420280428a410603921000701000c0340254541134940b00841d04e1805560000340000d09403400307503c140b40c01030002e91070440402c8110359445403104081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 670421241 1250 670419991 670420013
    0xc04030b070e210c0907050c0313030611030c07030804060e030a17010e100e040c090e0313090c1b0213050903040f060903030503011e081207170f0a0f110a 68
    0x140314415a00c034012414507046100f04105109001a2001c94010428405008406000b003820482c04010242c1049403e002402c44400c1000d6258001d03807031428420242d41140e1074420b0600000c1023442506032658044640c51135040c14407441e240ea4608021004000654207170f1502c1c000014044111035000d140600c104c2080e000d90b0885980b43c00340d000c0820342c11100802800e40741d640c184100b820841c219940f161050041c445600c2e11004501c040e02e040100541c4694004a00310186241d140801c0d030142c0803941040020341a41c43d07005004400700f030901014034031030f2880c01003951070b030700c00c00b2303082d2408400103011500304103030a1542d0350b00c648a440180070014401041d814440d03400710048079010b030307903080c25642044580c0c0c0c0710f110008801d441d101885680081daa03a07050100b00c40381c14403045081d407110741e14100118280c050a003108581c11040042c1d01d4a820400184d6508694a141c41c0040c00d0480d0000d580040000c018a1514450200c040080104046071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 670422491 1250 670421241 670421267
    0xd030606090e09030f1c060b040501110f191104051e01080c0f100c0c08070602010c050c07140328030e06090109051203040302040e071e030503090402030c04030b07 72
    0x803294071a56030310501c03800d590242c800c2ca409070420401c100c810b82c0c288020342042c015035941842c1c1e81862903040412100d850340b0041c403110012404000d20340c1c200d4402407001d07400802400e400000c030103c96458008007240b01014480d2030117480148228040c8800040d1009401040175040c001c451103540a0070041c0c4a1001462100219039490007066180b10681c0107050040881c1c0050308000d080410540d803c130401090720404004608440f2a10008041b42c00240c8601814008000d0030358180b04004028824100300640c010100010010704030307600541084200d40300000020700340a416141000c1941c141703600d0134030f510b0280050700c10f0351b842516807500b10030750b100074400d6501405102602040b545030341041103040400b000e403c00b00382c900c20749203020780301c1e80064201c54a10f0130405003513000000600c2030341500420900a807869480703668001d0703c0c55540c40e9030391150b2680c803408ac58001c0045028403807104160f501441e030000c0704a04618160000418404107045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 670423741 1250 670422491 670422497
    0x908011409160311060714030304061505040c05031311090a0f0f050105090a0b03010e030a0518011814060910030e2506030b061207090f1d270d030606 66
    0xd507074501414000b000c11294441201e0070401402800c00c080ca801031303007055804c503540151244101030184000c502c41d600c105800a41841940c03810f40030444560000740c06145446007179283c0c250418141c981c01940540f07407041742141481e041000300d43c10540c05801c0300404d000d004510140d83c001e50f190242d00c0000704505c42c5140c41c00c01c141d803000e22034183c00c4910340d00450048022074000c4468108054000b04a0011000300c15240d503104251200015a0100c4c6407109010304600c071040410b006d18141944c604204030304100304500c3d1051042ca4011f021a140543d150070301520b2a603e002403e1010812440d0005405003c1d4078050003503a0244c0307072130000000b08510014059444040301c400e080b034180f500c280c3c024004203a10035030058050002ca0180040d02d205280305141300e070740c1e58045600d411000c4034001c000341c201d0321400e03d510701401c100da0000c040d40e03a4001d001031039005400c1008181030b580c402d13901030401060f00a07072007a00c1c0c90396056000001129420f60b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 670424991 1250 670423741 670423753
    0x509062b0b10240201140c1c050408120901061a07210e040c200106050a08011107111c050f0c010e0f1009080304080a02010f05130b0a0908011409 64
    0x20b0059018282603010f0070546281e00114144161105a00049402d07150f000000b142c810495281c0e5204404440d40881542d0008061341c546074410780d00000039500c07a4090015003403d80c2d69070311600590207100500e0f0404000108205002d401c03400040c418001c9030902c8184001641006a026440c0ad68070f10452007042201c0c01c5000b0050380b4031450a40e151809015104204006082d045485804012030310113000041383ea259051548442000d00001d0b54910f080700348240d500841e407007003880d6494050710015840c0d000084502d059441899000300162420005202c5401202d4000c005041c1940e031004116001841e840803007004030481e00d21200f00c400443d000404194181d07040002d2010800c903d083c80928020b8694444c101201c40e00d0b10b510400f4550b41150b4003800203a845460700300705550300302042c00391080592815a18041c2404843c01403032480e44034805004c540007a80c24091485070740908003402d10b440c001e21981c50b00b0403200e03000790b50603105940b081c0101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 670426241 1250 670424991 670425001
    0x10f181403130806160f1403150915010306080703030507081b010e0a060501290306032b0305060f1008180703050a0209060102010c02150408070f030507060f05010b040509062b0b 78
    0x10541b40040042903580c04903130010798401d1508540002e001ea500b0124103030b00d200e810b5951f00c0c07000d0344076940d1282d031240c02c15450400101039400c0780d80400c469400c0401c0038400700e580300d021502d0140c1c2201c2c4070b640e550044849940070748905540084154a0243e0101040d00041109520503010740b44c207100c141d0300d4088106422301e450340c8042d50102c4840030150480300c0f050145900030001416030b490002c900c00003c1070b040501c9003441c4c0150804000d040f82c00e406219054110100382c990381c3c0400c00a502040344244202294800c1c84074402c002000c410744145015200032094041d501c40540d02c0c64560b90b0b59111160484c401c410010004003254414802c0300e0004a140c1d0040420b02c40170f541183d44510042c0080e524014100034010204211031404a501882030b070796260b41c0d4986042c00c000311552060844805801c201c010010740d004501514280d074412200781c40d0545941d00040c800801d030909001d0011030841450020300742e419004403910b0b0090781c002c011a0380b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 670427491 1250 670426241 670426247
    0xa0b04030305130501050c1e070b0705030307030515010c0605040f080c0c01110d0203070212160b120a060e01090f090b10030302060f0105031203060123090102010f18140313080616 79
    0x10720140035100e500c600e4812300c00303e80c100c448034903a818500c02d03280d20503111211200344e6132001005417515400042407210f0f166140c410541c1c00806050003413504c07000ca000080c1000450300bc040c2c002d9454601050a0200290000c81c800c3d43c03001c01c143c0c1e50400d410f0060384900001c16901d020901503190703c0c484450100d100c0081a000390b0140d440c202c0603600304041d07402580c4207400c0900c80c5410851483d606400706901620030f00302e22075101c105100300400b400d800200001d0102d0700b0002c0410840400c0100c0a065030300c2c5030f401040c0e030358500b41054010000040007401d401400c0301440000c0c0e00b0b0003901d106580c00395003581d51755601d51707001121070002882000d40545c000c0440206810512018580101051403d0f084d6000d00d015084e0f11800145400c425200b40000c0c00b2480d50703024030030440380c0c02c0c140788140081981240504411303141410042d000d40740c540e038100e0400200744110742040400300c8449076444e0303c5840040d500c1400325569000c400e20202d5580031540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 670428741 1250 670427491 670427497
    0x19020c040c020a0b01090203040503040e0f04060507170f0a110f130f08030a2f010510050d03092d03060501051813150e150a060b040e0a02090a0b0403030513050105 72
    0x24001c0240b482e2071b46001e000030020351005005903024041400089000484405c506008054000846c41311741810700b400c40803120080d050805200c3e06000400e1618015503055a1090403891050450303594264444d002c0e2510a01030008204006128544001814003604903800d0304030b41311500540b94038808089041c240580d492a5205010070840c02d40b242404140b6492643c0c10f155403401d00108444904449081d402c0690f5100d404100030016115590801080701715500507103d05562805040248140102d2400c51001189000150f84a00c44900c2899004520740f80c03541da42c0c00e0900003450700307024181c401c000c1540888103050480c000e641c010f5244001c0381941351425030312240a1015074a00700c042c0e5072542c1e600e507503200c02444091804404040825840e103032044c41c0b03030100c49540d00124440d01d0b050006200d00c048007207606600051141c40165500c0e402800102400c04640c400b05c420540040c000c0200360b8440080c12100c0192f070f94540d032040e00c0720010b4450340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 670429991 1250 670428741 670428743
    0x207050102070e0a060f08010c02250e0606070b0c0d06051915120c0903050c0a030b0c0c0f01050106030c1112031b090607081222020607050319020c040c020a 69
    0x190104000b4043c0412504101e82c01105001d0000380d280d5032403485840003071503940f244100e039541c2d00d0031040442d0103100709990030f2140040e800f90006121058403030624a8010480040044000a202a194882102d07034041c1c100310b14032200c0c98440c1500d8541c0c0c4c03060f90302c80549804c0c0400002e01f828440010030614545180c050585410400c19491094134289140d0401200c561010042401841420302c4810940c1d145039546056041142c64040c0d001003043c0107420300c80e000c10100d1514018690440003d41d20540e540400d000765a2420070f1a0000d10820352034a0000101c11f60954821202c00c14039849840012050514083d220300e48e0440a41d004082080000c0b807900c24043d0740070600c0303040f1080c54240700310300010a4a503040141c0071124507000040c901c4060550300c10140d405443d0302c005c004041c0040da1030728840e040046e0000c2c0110004100301c1d04218051054031011f0b4000014403141c2c0c102d83c10001d6641001e113064134010ba00e0280c84640076840816081101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 670431241 1250 670429991 670429993
    0xb040302010212030a020d0908041a1e03040f0503040f0e0606031608090a0813030c12051b1f090639030207120308090601270906061806080d0207050102 67
    0x441200b584690f519440144104007071542000f48503c2c4145a00c208110b280c050721350691641e0401e0306c02c804c0140c5030000c0c0f004041c42441b01e114100b490004081e074281a648269440340c4580c50003c0c440d50b07660f0402000f6000120f4042000e10680024600700c0d2050116100b00d0b45450702401854130082d10185207081d400c4469098860007000080c0c0c1024800c2c1c101d074040d01c119262003056401036089420b6040c000701d800c005025820200c0d001410403105050f00040d83d035500d02c1d60329038042000032a40d0400d804084044d0b03580452409a428104c9890300301d900d07440c1c0000700040340c540038413404609500709210100f08101c444000c40304094030b68030780407a911011031103003441c420401c0701148101840070a0b60340184a000008074071980701c0135114185106803905101c0d05030840340011001002840205489118030340e11119244000190400c00b400d2100142c074080e0043c0c52140d070489043d044421580d40010f08599491081c0d1315568208003040307840e907006104443c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 670432491 1250 670431241 670431253
    0xa02150f0f04050304090c110d0201020c070e060a0b04080303090d09060e010509040204080d0809151306020711060f070506060f091b090a1403010c080606040b0d230405070b0403020102 81
    0x303122440380c0d40c1d50407600400443c4d0400c0d0b50b415025064464580625000400410b06481d807201c0170099100255000e00095050540c0200d82603034500c003d12444050754a10740200303202d0340705c0004010141520302d1441e42d03100d4942c500550b0703907402540c011350180300c1c00f04400c8034144a4800e4900f80c50302540c0b410b4030b1300c15401c01180c0d281c000c038005035401382d402c000c00510660208800102c1c0b005036200e00b102864004502c44c100448000c01000304460442088610f001c02c2c41001401d81d800040181c8a160310b04185108106100d01d054004e1400180040612404006816103074400c50440360203580704030902940b00c2e4a00c0c001c0b504064450045603023600c8480001c0c1e5080d44403280142003007032440c005480c20034540c0c04180d02c0d0910014030b08490400b0700454a0b180c480c0d080404442c140b400200301303e0711032440b8040d840400491403c03426070701500144c1c444441107015060044022640ca11000c6041d14121500d104600d0001501047c0d001941c0481fa0140c000d014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 670433741 1250 670432491 670432501
    0x402070c03031b051b011b05010c0927022a01060f080c0907050f16030f17070e100e0306010b12060907080a021605061003030201050a02070c03080a0201061a0a02150f 73
    0x1403d0b02d54170340941405420380d82214a074034460090079055001d4030021a50904c2680050480c6500e500040d00718044d07481160324031184461006207281c010b40b00141d80300b038201c986582480f40d42403020781600300149819498001508650240c0e0030000b008603010f0b644192140e40c03555100301f01608403a1410004400c240500040d120080d10f40e010245001254410700e9002d0700b02290403008120285e8483c100d00e98040388504005000c0c8442d2159410850b0700500005502a049403207151001014400700d80300b1103224411b81006400c4490b030b940c5400024034190001c000e81d80070340258800082141c0b6040300c44c40d020381c0c0c2075101c55440703440d1140c40001940c8200b036401804407090856400103031040104a105081c1010100710050a40c03034001e0030340d035019040c071010a00600030300b808200600c00c0c0d0001c89a00c84a039540d50709940f03100ba40540340f689c2c005890348090019a590b4041380c90002e001c00540341c1d00740d0f011140d20240d02e0003448425580c40b12940c4410700090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 670434991 1250 670433741 670433773
    0x1107050904020103110a4a060c0304180c050304020120070b0406020d02060f07021905120c030424080a020901090b0d02130b03010501020a1506050402070c03031b05 72
    0x640060044c0750126841c0e01c560060410b0b640300402410004034980c05580300c0a40f111480038a21a9800c844044609208080c1840f0728080e803400c0c1c3c2803090400e4013001c40c4c0c0d6500031207440126550559841f0742e500c280b029400d028001000040908100360544030502c100112407117264142c4840aa03180d41a01f500e6180342d08189241051140e0403020883c1d4210714050402868941d0082c02410750f05003009051041c09000070b25848420302c18042060b4001c5082103106260848a00d540801402c14a01e01704450410140d15880052030482162021000f0300c1941d101c50a01d88080e4140042c140c03107500320708001000140704801080f40406035400800642ca070516281c07c456840380911b01240e80071055241005030300194525505001c000844000c00c92202c205040d0b43c0342c140044e40700c0d40d41203801406445880071031030425807158442c40c06004050821910f0345903a18002c110741c1d4a500083d004114040f241c0c1c08103030b4410041c00402c3d58042d0160004040810b101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 670436241 1250 670434991 670435009
    0xc06050705010209030a1113060315020a0207030606030b04030f1806030908070b01090501090c020c0f1c0b01030305040617070207050f012102120c0c07140105040e07080601030507110705 82
    0x3107650355020070864550342e40030421a020300f4000c604020803410750204000a46035001c004039455418940c081011598110b181020607600020159551007440022030420072103410007080c3e149403c1000c420321030303400d10040c81075200f602d4407441c6082e84a403c1d18025081c040712800c0c840c0390081071203502d03c40d412010130f10313120360342c49c50a0062503038078034058503000d0304941310295980c00108901c0c4032070b01920400da090b90001d003514903501e50105201040741c01e0180d000d019071007548a400c183c0d080c0c40a0003590018580c2004e56140d19004201e40e000e44501e600041075a088003095464011546000319001e40050402c98a04010700a42c080c40300382d01e41c1030080f18000303842c0c0b20940002c02d00c6e682d5144400143da80400d10022141000058820140040144090711414200107209c1c800d9a0301080002c00311040f00740120f950f8030687e040040c810041400780a1665000b92400c1c1c000d8401b43c07800d100ca0f54840c0b5088852500c0c4da41c04810543c40001d0412050502c003840c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 670437491 1250 670436241 670436243
    0x10e1504110a090c0e0f0105040305060c1303020306090a020306011505160503090a0602010f0c02030304080f0c0109080a03051005010509030717011104080f0d0e09071d1306050102190c060507 84
    0x78040c0345580340004801c4424000804000c16401045c1205501c0d008030700d0301c0503c0003400c10f581402d003541c80d015a10100200142000c48002075013080003101c0041c07a40056074000c080390f01074900519856161701130160128003a04c11716001040d082070f5024000d0700410640e440c5420440c050f5004002400240e00640d0140010408131285485018400d006043c80b41c0001c290a0943c2a8000c1110001e0041e901150001c2c0f0500000880302021295007440c810116600c0307000b50740041c1e0041081050041c142040092084031541c1c00d0b4001910444450f0445200b2540e07483c0191810b12851b9111503240e0001c0009001041d541005550680007a20001812031025041c48580764451381050030940d003d5107080c0701e80b000c10041400a11030b54a0a0309808460a000c00d0031281c021300554240240068180b95202101a00000601e230042070700340302503041c41000c03009100134000c682c010300a4200c5004d0010340c42e410f0300c0c4455400140140131500d0040c0841e4103421000d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 670438741 1250 670437491 670437499
    0x813240c02041b20060105091f0b12091005041e030311040b13231314040803011a0f2b050c0306040e0109021f0c0203010e0f010e150411 60
    0x99001d4042082240742480c3d00c2c280c481603841070106401d030503d0b681c1040300b101164030a00c01848191a4904429045a220810000340780c45041210a1420440e000042d40309000315015500e19003100038140140440025220160b0307401110206a80003205c000d0300b544000800400d42c821810700c800132040c02880c2c0010000481c00c90b01740c03540d00c96800100c034400003090344c060701404010510f000b840c58080c0319182661003026030050f0700040c01810f04c0341c0703640c3c5040c10b100301554218001c81010003980160030325052800300f5035074000b8003405c2420f20921000e02c0c41d0f07902d01e1040b0780020001c81d40d45810a50783c03a240c040c0305c003000da44840c1c640c031084061220004c564010b082c00f5071244081d168491810406003c02c440308003200d8169603041001c49000742e1224288056030400910072100d80e10350408003650030104041c2c0094043d0300c2d00c0740450070001c020403141c25030909a8000d000c0c59110325101b59551440050007584890041c0c0414000742c4400071485030b80328082c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 670439991 1250 670438741 670438751
    0x9030c12011103010e070201151a07030509120f0d140301030b100e0903031e0c030703052208030405010506040b1e030a0807050d0215010b2a07030813240c0204 70
    0x40011501c83c0c000ba40695880140b11040c481030a8082c000d180c442c52100c190040081d03d0044000d68580d06010f14440d020340009070710090500c52011144940b40203001000000603803050f182d5110100011840c5c0c6000c4c8000d01e0034171030700c1614160403c040c117002035070031a42152100580310101a01d600944801080001418800d844007039120380654070145449260548101031548109001c016811040c04108604000010700352500f00c00700d8540056190303110018118091045004110464a814807400401c40148000c600c43c2c1c2c400d5000388484c0d2079180500c01039480d201c0326994010303090341603503441c07600e420030070f40c08101c00a04071640d6800300d031140411540120402d440d2500521030403056160104044100d400c00941603114540c5854000200c5000b060a0804076052174000d00000002810307008a03a40c0c1802c06681c200e50f40c1e07252038082a88050500146985c070300c0c0380051424102c1e010303404a08009010060820040d1800306c8201040c1c88040740e229030f0b56 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 670441241 1250 670439991 670440011
    0xf18030a050d051206010201051303080618090304031e0f0201081e0c0403020f1516140303180f010c0e0103020304060f11090102010f020c12070302031e190509030c1201 74
    0x401451000103115200d07680d50304c1e039a9081e0f41d80340b4001060581968141010311104032010300010f0b019a41510f02114151200e10000307407240103c1d800e0104145c140824070052040c040001c0003200d1040122041103014001c00140c1110071681c0507103500e0290306000099401038440aa00c26025100c2c1c541d81c41c4001401c850707191007629901090b030408a41031046003001c0d40100da403540308440c007a002010f0000d48891500c655140101c6000406088004206121310220249200102130b241c482c50080317180500c00c05924628030262042411110079180d06102d207150714555540e0b0385010708038102c0158080c0d0b0014208407034896031031000d000e8111640c07086004038680e88603055a0b902c201400282550022000405510300c10000c80b903078154009445079102c419180103c0d00c03055a42820b13800c2d40202d00c06142e00010850a8202400000e4005c0c410b18500e05a41106d42d51484000c5400340910b0983e00c0d01a031082c50840d103180f528544c0100752960040c0046450202d13 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 670442491 1250 670441241 670441243
    0xe091203070203040504050c28030b060706150e0c07110a0306091104050c27120f01050106120c02030a0c05210304020a2903091615140f18030a05 64
    0x40320018010f81001c20700740001c1c0340500a050b0007142e040222424034104404545240c1280e0410301980724000b0010381500e80241c0082e407005030014411500c079070441c2030540280145804810101c20f03070b0b01c0045010252180811b02821940d50150304207030040c0d9541c0104081c1c1c10880d60b1100c005580040042c84501900d07800921800044920b004488240320690f1009440d98502c500b042c01500c1c000c4c507190b0300d0f4040b00004180e210440720080004644050801c1490800714010508400700300c082c150844e5040f26075a0707660317041c1607240700507150403141452a1040183c0040062071507451141029420143c0504280d030341202d102540205c030061540e000140120020041006628140242c02e004005082294200149103440c0e06148540f842404101305804030110380044000c01c034660054070000e2074074101540f50854820101ca6084910000981c0154240032b6031800e002503030030803400019254104a454008911403400410303120750144500d003040d001290f4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 670443741 1250 670442491 670442497
    0x7080a020c0909100c1b060515040e0601080c030d0806010c2102010b040b04150b03041e110f10080136061701060303090e060d060603030806011209020306010e0912 72
    0x110b010004e042054003680c589050b140c144420345d0030710400350019000c4458966016440e80d5000400103140d6580b060b54903011054440c8064200c1d20f40046c40040d0f040000322030b81640c695070100e85080442c50300300b640e20100703a40080000703000070022490550043c000c401e0354910a800e0051615114142d80050907903801115005030b440b0200561142000d1107a40c1540c6010781c0c0c00c0c0300310f1000d40304c034600d101c203540b180c111100c60000004091041104802d1342d20101034100c00d009500da400c148003064a40c0000d01c0c0705215116107210307140382011a04c2e0140f0141c0e19a450582c1c80c11519407140c410524001402840102120010442060f078501a81c0c21410f80098245d040c00f2405e09207002840d1468180c0c1e140280030b001207504801010100c4c0c3c10034480c1c01d841c3c1d1f00c40c00800c07074640000178020101401c1c000040205600a801140f0514003030f65404c201c0c8451021340e0041c0c680501000e509900f06400500852241c201000c0d13001150100301e482001030007075224075541c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 670444991 1250 670443741 670443751
    0x17040f30022b0b160903020d2a0608040308060d2102030c1e060f190c031b09052b120203070b0403020703020a2322020d060e060a0b07080a020c09 64
    0x15410000c10520354888649418081002d245c85040d031411540821300e242d0000790094000c4e101c2c640401000c10310500702004091403601c003440380507580c1001900e890f01c252000c40220340004005049400c10031130f003d04440e007140d10b41c109a2400755a044001c000d0b0013107482140420840d001c40329004114407254003c0b9520700340203102180d00582c1c2000406016010362503010001d20509078030315800044012007501d00011000110b103400d40090469001c2c1c2440c8108032040f075000c554000d401041180c100342c0b035041c1c0c8a521110703450340040c680c1c0e00d0201008181c050003004219105030100070001ca6004a9190000302d4072134508003a0304a030100e005074407420090045003042c0e110f03080240344a51040034064000c80380103002d03442c0204910301900030026031411311044c0d404902e0000045c1d9808658401d420000c0d100581142e02880001c44525004505941488501003003103810603503280c1e00b42021303542c802005900c096a80c8085108104264200e6900c0f600150b00078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 670446241 1250 670444991 670445003
    0xd0e01030621050712020a03032a03020312011707030305030a02090612190c0815031501080a0303060b121b190c050d030b0306070c17040f30022b 64
    0xb200d1030b003649401c0154202411600700d460007a00141c440c100c0e6502500d83c107040c00740c0505250128405c4032220710445150100491010030140351700071008041c0d01c40c12080043c100da880c2c0420741c0008a04107801e500c203901c00001000801d1003840555005058580d0140c45d00c00d904c00002e5850700082d414007851034020040c84406810740c42040180f0310b14078002d0000c405428005040c841c07004060400b5814040c600010342e41d0188883c140f460511490034404e561203540c41c82d981d501e2070b80201e000c170385407030f40104d500000c2c2d4060380c60b904070030726040300139640e03003e8002c039000e04090600400071000d110a01509110f100d0941080d80555101c040d4114141002d0f80303000350029040f4107140c90060328103203d4a011601c242c0c08101410302000349000da207001070f402e103074880c0c600504140100d00810781018203221038080b030303a4802d145440c5141d1a881420103140801600c9a52110021204010f04028620080c0d80050702c0c081481c60000150102c3c14161a107822261 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 670447491 1250 670446241 670446299
    0x20a0203040308131e08071203030f0903030e0d091505070503070c0b03060414070c14071d100f0f050f0d0b0a09120903150b150c0609011d0d0e010306 66
    0xf01707495034031603c028602c4018a0354206480d040d0a5911040b0074002c3c02420580400e440f010705009401406200c5a603034020480da40e21410020001d192110258100b030003020542041c20b842000c200381540c0402c04413140c4411012026203455110940c00c90343c1d40001e10030800030030014091031f8020002403000765078910b441410070003150059820651003e14401c02c0c81800b650000c0c038400001d43c03220810841014421403a41382c06415844100e01800c070440d007103000c080d1080924010165095406002510303295204d01c613404501407207542c104c0f040002c001d00c3c6400f48488103280c10181943c0013100e45d40c2c072a200c9000e02200d120044a4941040000700802500c01131317031903089490701500c45819940c0d1136a0b8a2748501c411209152036030f105000c03540d200110828040d2030003405036510914007034a01d031100c10031254070242e94a024130020404078001c0310f501d82e01e906800a0004008501c03800d481410f510f1442030704160fa0380700d02203415603803185600c4003150307944e100c200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 670448741 1250 670447491 670447499
    0x10903082e18050105151602010e0a1206180b040f03050d052403030315090415090f06061202060703051804050a1a19030f0f21030b01020a0213020a020304030813 71
    0x261581a031040b40a43c0f50b0386d00350106030002c6003c0c1c0f150084130619030b03ca20743d0b8900041703504141002d030080d80540e10900c0050030f9a2075004001c20070740b0803441406500c0c21411012001d0058940103003141440394005000101d00c05091a2494468141030b8241215400107800f00d0354100d6210400c00c103490005803190307800c0b605083d9502004c9004501d03614140c201c0f81c2095000d80140ca0141c00d202010500b0000c0d0740c14442041c0110550800100d2454103120456140086099840c6403814801041201800c020800460b030054400d5207055603607641101d40da0f100d20300201040c2050314203880c2c25916801944d0003001052004134401062824000c0c408131080c59562143c4268080d07060707400304109000c02103075041410f404602ca0b940c01d102070505c840340d00c010400031403d58980f20038503200800403500116507600b00002005400166950f940120029521000d1070b1118040580300f50010b00001d0740900c1a42d04180e602c1d40c45074541d4004001025802d004848188 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 670449991 1250 670448741 670448789
    0x6051b03070804150c171f090b01031806060501081003031b030203070b0405030d140f0c0702010908030409021312032705150d05070203040f0e06041e1b02010903082e 73
    0x2074104038601749a000304034401e600b0701925140c0c0d10991043c031340c64000e00305540c1c4c0a40c1c003000e601d1015070033000d10020a46401d034018200f9008650102e0b1800d0040b98102010969190503a507040d203584203141d910341096402840c083e88100c00310b10080118400051070009030701e01603440713100150b444401010b080c000b0343d41d203000900c40a0301142e0403c246000c5081c6e80e59088030300c062000b9995205400100c98040399030300310014900c0002800190003007a40c1c010700713022040c5420201825103030460780c2c1e144090f0050150000da114000040c460030b0310301c0703481d40620340000340c403100c2ca64810200310f5510808085030000b1401080d00408003c090040561240302807010754075045c01d04a20040395091409a50014100072000800c44e440d580d0005440a052188201d00742e04559402806071804510600158000744100d000310b9005000340d01805505480f0903030300d030b5134140101c2039400002c95003440c1c1b16050b40740c0f031903586600d001041c00f074003520840070f02c11180080b6036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 670451241 1250 670449991 670450037
    0x90f01150608220f0308041e0308130c1e09112109010e0d0201020921060708072c010311030105010504030809031c0c03081f091d07060201060306051b03070804150c 72
    0x1d80540c05c015003002300002d074072105503544901050313118000003015051184200120342c204d4002d6050107520803034401e5810a008044442c43d51040c400c088040600c011103008603d1a42601c41b100111b6540080107180d44c0d680c44812000005064400780c1222881c041321707201d9003400750350700045013400c0d41401510314952060524040d40000e02c0c2c160865a01c0c10000d0280d41003010718804141e040d03100368044000200309520285002203542aa10740404485180701e021170702d40030002e01500c440d03070b0030759040b15030584540b41854915100c81c001d55020024155241c06201c0250407130340c0d004400c00084001c16980c0c000c45076494038002d030030301d43d000e00302c1d0f400540b607a035841a224205611b502c0503a481d4400204006403803008040301980c555544044500914402045940d41540079008407070003200c041c04640c54001400d5a44440c0340500d030f6003041c0820004103554000c1c0707c0319030060300c500d10090030f2031495980d013821201c00c00c0014000039855601e80084103046050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 670452491 1250 670451241 670451273
    0x51603140403020c06130f03030e03060708090c0607110904240603050c04020c012c010f020f1e1204060c0e0f09071115090f01150608220f030804 64
    0x4405081c5610041d5680038488201c611a0400142d0385001000c203001c408000c0402c13a20390200070361680b902030000f03115512407034020320807900003e00b0148602c204e03174049d21142025140200c10f500c18407100e540035520035a221481440e484607541c0701c080c030703907846540035460031402015202e103042c3c0151800280803141300e0820701c007400462008580fa01034242c0441d401a69018080d510501404803801300f45100d41e20040c11000e644203150301030a0761420403000300094008031550350203d00039801c609262150a100d030103d500342e06140c82e840303d00182c50b13071410581c0072641c16003441004c4802701c0b041621a540c014210303410170352510303000c45c044420036140a03d14012420640c4010241400c000110060203075455083c800ac421140266203040814507003048007a44ea04a1215801c405603c2e0405100e0400c408440c041d013034807040e54410000e512480e085044507100c10700080a8010103c0314103000415440405001c00c1c400e4843e1081d03850281002c0c003940c0c0102c2c0e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 670453741 1250 670452491 670452521
    0x1020c0d0506130c090905010c0810061e031e140a0903051804020409020d0b0f0906033403060b040f051314010b0d0b0411010311090906040b0301051603 67
    0x1003040006401041d240d9218281034440fa00c541d40505004a40c240181d01c40002d0a15200c40f050a02c401034201c2c1d5119080c544401040e074580e180000c10f90b42651081d00001100800050328036421301c0940c0c1d000343d0151a0100b0243c80084154080c128000c900072086a0707074641812056000440079684244401400c0240f10046c0d14058007510503051101652013030307400c000fa03083e81c4603030544018006502c0215113542c03031261204024440171659610421b03000310403d01a2a100481e80d1141c100503000e030801081941c260040105403204065255180142c5482c001c002e205214000b0760003804007148960445062104960301c03048486940343c141410070044803074043c800700c1d40c194020004240042c240b0030050050000828107944045900c1200781800400380d000d1307004038002c004903070a6881e038500540071175000480c1d0581042007030041d0410340c80c0c407038403081c0d00c2440a0b2001c2201541d40300000d08644081b5844044042030003d40c0442942c54450108003038a504 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 670454991 1250 670453741 670453759
    0xd05180f031315021f1a03010209010f05071707120f2a0309170102030106021b0913081201090515030a02090f100807121406040f020105090316090b01020c 68
    0x304002d031803400340c06554000c140e800540b40c0424803c0004c8881e100140e024500004c03100c42c0e010014141d807800d007001c0e1160741c0c9030404a610301882140c43c01a0161548000c07522411401c0e41c00d40c102800c1610360560074619408003024001c000d242c0c40380b1407516420311030341c00000500f51806406000c0b0030000480c51050b5200e40042c2e80006a2401c104503541c0301c8110325040f07448003c9038200c241d40b409501c0410082c0b0005402550581d074a44d0280da40d803210500c00c0401d0050100781883c0e00010040204044030030400040c070039030340a07100b0b0500d4042054144031148800b84d012803005607482c8208802407100e00e10030b014403481103001d0a072003c9582c00241003448007611110302c44462602082d070000c402da4480d00200004d20070340700f089645007144403413102210760030345101282c03000c4840341c284040fa13060710881d480307a450710003500300d9001114030383c00000d001c0c4d8061141c400406107a6104469100080604a9011600d140c0e841c000904101c1e4080503280960004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 670456241 1250 670454991 670455007
    0x916150c021509030115050315100506030a1b0914060a272103080709050d030f05090315091203070801150318050d0e060c03040603110d05180f03 64
    0x1000d2400c590100c0e21401078003503103405031980b03100303d011040e8191728100718020608a9032104100700d172800c0702661007009203080c040440707540480c0c40000208018800707101d2032506801131a007000f0460b20000e40e2502c9200301703242003200440e00402040c8410020000b0484400d40740d00250380550b1140c0c20401021405061011b88810b02c0340382c0d80c40652002042c0b040308246100034100858088000101440741c3c0b207401e9581c54055000a60f10300000c0c8030b07180600da0300801c455001c2d0031a1196030107070f14100d80800c1490040b80802400300311140040d80d040046810f03070402c810700c2e0700c46800c0030000c840c0f07448080052065262428401c12002c41c0d0170012041c1144c01034103816001e4450130104500500d600c1c05800c000071411b04400d001d00030300180710300c046032081c0c43d014501c2c0090760402506000d90007030411580e02c100820701c41f1505c0b80e000104001d0100d4815030401c5954084541070340c10440d180c00c0d844e010f512030822462020003040600801c0100518034003281 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 670457491 1250 670456241 670456247
    0x105010501033b060c030f060306060d11030a060203100807090c05090907050d020a03060608070c0809041a061219060e0402060901020f0d030c031d0303220803091615 73
    0x2000041040c0090090300d00c801c3d40c00581402268014003c2551414a0315400020541d001903541c40c552840250004140d410001256401480010b20b289150f84850307440388110507000d005690540189107244000580328000346014500c1082c1410f007942c10100c506190640e00d5000503100d13070610441205c05a041412183c81b0a02594021032a40c0d64140c1643d4038410400d40613485c6100040454919501d07900450642d185992071149030b482c0c4460894501d440d100008d403031203000300200c1d0305901d01070f0301c110564260491510342e4907400383c0024031543c000c0c0406503003001c1d40c507003007003a0410760b444415042d02c07040c002042206d007804045020080010b1000740200400a04180da40e8000c00442001220312011141c3c0a100709000030090a84c0e140080042410494050000b1041c0014200b0582d4554021415603840d814417a01c10320b42c02c0c031816486510b045100010403401001141704d091290000e01c5103d41c4014006c140f000c85501c4410142d00a01d0350a80d1264 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 670458741 1250 670457491 670457531
    0x10050c1218150f07081306020d02060a020a0c14150f0906060f0114070f150905030f03100b030403020604200112051923010906050108070c030203090a030f0203010501050103 76
    0x240c107031103100c00320607034024440d020f2140c4091880142d00118642040000440003040c0c000e030300d904070fa10f0140d40d401090780d841c1c1d040d6001002607004035000070150401070b409000303c010796140c00001c40100380c4801e91841e4094400c150a80c0050401c049117010340705910740c200b5140d2652002c0780c5802082907885a001a19083c4240012008034035143c0c4164001a80c030003100d210103544028614203018030362140345085411210340c2840c91200341e100d118441c4125001000f070340c5041c450034040310859200900c68640c01e0101240814080c20301070181d44511b1003030700144804e080c2414501041d40b203030740d45041140c8070715030158850307640024001c0201d8048900030465403034403242c000e8440079030f2038080d071003074a0040300b40032180c14443c8054140d141c001d01c40b80301e642c1b00d0040000303803002800303100d000c1442800811000c5100d402d5120074a8001d1040e6402c00480c3c00000e03600c0c2c11180d209556074030080b54040258a400c0c414030740100f00900302084000c40d81e58000e0304902e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 670459991 1250 670458741 670458787
    0x90510121416050c070b12040201030515010903020910031a1503070f0608100302151b0c1c030309080f040513051501051b060f040b0a0e06040b09010b10050c12 70
    0x440030130814101801080300801802e406000c054949894081880c12804112400d0340068102408a40d610704081d83c070400b103501c10303034415401d0f60854007030110030400600007100c441003810000011a00302d511907906108210070003540d0307051444003400ea40300d085a95038405e4001580c10001c003650384c50b1741001c44085041c1903421799140310541c10107900030742c00a90031281c0b00b040300c1e48615240d0f00401484225921648665901d0130b0116a1402c004c0b1646030413014005016210804c604140700c241c1d4820b00d000321303814001d962881001d810281200c041c0c068042401d205c03d15200311404041c1d14905401c004911b000c908182c15040b00f000001e040c42400221007014001007060030903d101c0f03180032514242030400b10030030500421501510161600c801144a403942d130b008030300c82c6551340c40003401103881f00d885608002c0f60181002c002590b0b16020b03010243c4071400041681d80c5252070321511214840c121170304110904000c070000e9642089410306030061408007003011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 670461241 1250 670459991 670459997
    0x807110d0906122a0318122024060111301603081b030601260702061f0803070f0c050603011404062102010f090510121416 54
    0x180092050300c0006021000d60203584004400a18500c00358544150450704001d9404102042d060020384003803104c0490018041c1f40d0446a101e411445440c60103079a45400c00210001a4055151442c0c034022035030040f6800200490071141d1140308c0b041030f910940c00c0c00c101080660320720b40f864450035010005000c00c030414005480303805241084005c00d1401c80301ca0356560303141038000c2d1081c50a821040340059450800a0f00c10920fa13241d0003420100079400e6421500d9640c01540d854008001c000b0000d001c130803100901d030301c40c00002c5001707442c65000b6040c0c5080c02e100340f18211708190181280f040041004002910000046526403500300e9614080c4580d030786040c00510041d680b04550006c000b20002c2030714182100203030403941040b00c1c10001140d5441402210745280341c00090307900c0c0000381e00000355008800070004548030b450981001c6854a0024244441d61244400000c0d0090340d40260780c0c18502c5a00040ea201012401261520700c131690070b2010f040c5d2100c010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 670462491 1250 670461241 670461257
    0x1809052407230a0207180905070311010302130b09040f0b011b020d1b15080417030a0e01180b06041506050a03060504050703020d05060a0e16110a030807110d0906 71
    0x802c01d0002c180001415140c10582d503100070340803000f5590040c0c1e0007100d12072002401c61500b81c0d0314038860411803541c0200030700542490354031504c50641c2c01e130280750305058080000400c100510b501c440094140b000003240c803189000c051004a80e58400310308012844c0a114841507a0885003018580b10202c0ca10b1100e00c0e40b0b403004c91109000842e000303065040c0140b075082182000c80c00e031015518110303000342010360701200440701e0307042c1902d000d40700700240100156000c40000040d035115a400350041149a4102d00507400c450b40385040b644644c5c145d1000004000c0032008868000100710b82c18060701a040046500e4101184105814001c000640c012068043c0d00400001c0c100108104114500480c02901942c0007001c004092803404c40040c15606e17015511a06903081000c0092542c2d9440300e201040382801140c1c40107210110441081d43d401c04c03c50301303111034880d588603402d50920b160050086541d80301c1307a00003a041507001e01c2c801940081808110f403144e283c0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 670463741 1250 670462491 670462517
    0x405031e0d051611030a051812070803031b0f19200703030906080f16030f1a0f03060c09040924051015020c060a02071809052407 57
    0x40c98450711059507032480c2000704102d09100c0180f54948500001e4903040d030480c107130f800010f80780c0c480d102d01c2401090b03061010700740e4070700c8203d0000308120020742918410503402c07400c185400c166500100c0150310001c1008566603600781d0891070340303141c40740312400c1001c451840c00290060341d50740703100200c201c440d0790320440c4200d80044c07402130f0948200034015000e02c01540c484040e07003c19000300e44551000911148540545441401c28465808468403034034038200480042c501103404050301d8206002e800c40c002e1081400f8a41c1824026103082544d8003803103680080c0b900994440d400030020880500c0317099040b1480c0030001c40b4001182d806d41c2c035040481d200288640c0480c0d14440d1400381710001c1c2541301c20300070418041da5446080c0d0b01e00c5810012201c002d407030700050308000300705030301400c1400142020324441e00680301c42580b41c01c02e2502c1d005410490018058981c000e140c03d00c0005d001c6840501041005e0124a40708000c2c45103258030042c0000080101c035a06440c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 670464991 1250 670463741 670463797
    0x706090f0e1b130b04091415090702120a0c06140408040611030d0f1d0f0d050d020f0a020d0909060605190909051e10052101150603060e0f040503 64
    0x120f003050b02c41d5140035001d8650740da00780b0b00c1d0818040c0012052505007000000074040082c2445540081e09400301d540420341804010328014001800350720640402ca200c00b0110740140c1980401a0b854110200c1e09080c400f058400701e0309100800c074840005e1201040441040b01e0a640321801c0c103080d09100f168800b40b6606c01c80b001c2000c0079140203007400c4078200c0c60b0000003101c40c214a811a2101c0b82c9500591a07689801c07a0007060341c400d00480c0403c900030405841d221408030300060401180b00d03a2088a54003103c0000016046010701c180c040d80c21030700110162851210030403031641007a5001d0000d10034515040609007400792083c54031b5106203d100091b054211081c0214140102040304540501c1500b203160780e0766100103201001c03030840303003000c6442c010b1500310307001c2d04a04196684000b94108000ca552a03501071808000000d80200042c40c1c0d079a40040d1180c81c0c20283c01c11501c0151100302854904418080070600c0042a0b400c004501002c800f100806502d8070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 670466241 1250 670464991 670464997
    0x10b0408121806030106031406041b20011803140301050603040f0204021e04080706170f04052b0324030803060f0a0b03011d0c0a08040218090706090f0e1b 68
    0x2250f07001100000101d90139500d07402885c00b40d103152009044a4849204200503140380701c1d072a401070261400b50b80c201c10712540e008103203844909003c0d20440302d0810301a0940d0340840c9101c410901034000346c0101648909480710003546032480d14215410400042d64510000d040a440d8640c07803a500c006666a07541198480b0201700080120f1104034090402150003034411405140510880080c8080c0680300030b5140907048040380e5542e541c1c030710060b0301902e4054020f94080c418030a05011421000300342640031507a0214030700a506217290010103446040101480499140714944a207071102c502e064160b0781d01c8844581c5070369550010070003a84d242c088260380442d0881000400044160045050754500080c0c04c1054001c42407038060309009642c3d48000450801c03140b0b104610504400743c100c1d20050070b41c1720340c2c80c100110214030780b000d4840094607001100e003005041d0300244d49000410300c0d800300d1400240740036441d1010b050001c0149035a440300b014801c08100c048011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 670467491 1250 670466241 670466287
    0xf0a061502010b0307140604031b120302030d0c0e1f35010503010605092202060a050c1b030d030f0608030a080702060606161113020d090209010b040812 67
    0x24001100300010300081c040c02c590000c4a0103030040d440045036221a018441440d03c202a0020745458510b9940c03210a04d4000d244030010510302074081001c44401c0030808003d8041d900454403002c502c9481001c4440f0b5002c003906001400a1000c17894441e01d4810b42016115400c0ca102c1d040803020942d1140035103014501800c0b005003600104070b8100103c5159000180c00e00e0025030b0329181032500300d62103802507992241e1107000284141c2e1618503031382100740b00b40d090901c0514280d804144a17820010440f004241c0c0802c403c10818400c010026420080c94038146081c00c0070000300703444c2c00546290340109910303590310591450403500040010950182103076a03030101200018190031003034a23284014010700c00801c141e4644403082c1e6994806540045c50380300241d0ba2180d40602d125101d040d00f0030407000c1c070361444802c244003070007840d140b03041c002c86c601415104000421074141c00040d0610810b0205000040001580c405010004d005141c0d5030f03030342454841c0e000050010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 670468741 1250 670467491 670467509
    0x618101e020d08180c060d0207080d050411180c0915040e07090906140105091924020a05100e1c090905090316061e05010312080603060106080f0a06 65
    0x40c2200381c0c0003889840d0000380c1c0d581c0c01041e48501000800300c0103081091000d03648800c030842918a4510001c02058640c500018139006071780d40c4848407908007000c6c88403907680d1f0b0020001801280e1240365068801103c042c1e208001120380078000070742c05022540f00322030214a000098a8200c204142e24048000c41510780f5038522801243c1c800480310940020181c02c0002000201d5000b0203040d40c009510f0851005014001124580c1007080580c0c0d02c42400c400d4109010510401c1d100513200a54014044500910a00c600000c101c03458000f198444281315000c030700042a0540c441440100214540c004200d046142c80030590002c2c240800d240310031950150003c9454080b00c0c17141701c050017144e803051b031060703140d00901c40c286000c030b801140000c0000b825948031030b03507000d841143c220712004641c5400702229002d8104607401daa0398082107040942080712554400c1e001c6004120b01d606000005014003009030201200e14001c8002c00c060404541095001c0d00c0644 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 670469991 1250 670468741 670468787
    0x3060a18060501080a1208040b0601120f020c01060f0503030909011202010201061d070807050906030a2c070e0a05100608041a130b0115051b01020c2a061810 69
    0x702c022030721790a0250003100c170403c4501c221540280a12101e6100e1600021504181e135662001545c0040c00584880b0000707948103040040d00d44144042c03d1030081260002a0481c10f046203500840c586400c072610036401440580e50f6599001550f50565500706605800504c06200503400342080e0340014a040b5446151200d007241e402c2e0b240f44c17003010640e40d022107540f5800401d072424442c1c44207580d000001040018034031000380d0010460b085803c44055220700701400c1100c0c01d221240a81c81c107640110000300042002d220000c1e0300002080420401d9040c10000c040c1481080c0c4600f200f0710042e2000641848815503101400840100c00154a8900300710106400328042404503000d0100b07070000b140b00c40c0c14244908440e00f45440d420700d040c000d48001c117402d8101c070417452060340d020851505101c0c0144030300100740340403010301084d42000810708a1100040b1841c180542014800380604502030701002031504003d49109240c000703031315002c0f10000c5444494200401c1c40e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 670471241 1250 670469991 670469999
    0x90b030a03030e07211e03080609100803030106020708070e1e0411061810080403020627030409141501020703080f0702030f070503150f06010f050c01060b070c0801020903060a18060501 81
    0x9005c5069a201c0c0b10070000501e04400d035161821082c2101800081002c000100c40f42000d111464001e440c107445032600d40c1daa40c4242d881c47d40241c00c4280183c12200d820064040e0811100000e820001202255441e11500000124110814900f00131003080f0200d01405500c014049d144440503055a44e12450384104142c1000741c60900c901985280a8171802c0360b121320b0a15000b0ba501d540540465210b6980109031040f142d07195a1810015a0400d250300104000070401803d040c64049054250500b800600c00e800405007a4145860601c0c800716070b0340465510140c0b5030143d98207841d401d51043c0800e8074001d80314025014490860965a82540094490203c0c1c030102c0460320101202d40500e20b1a09040d94a002128070352004201c056001d80d04040000d01c05140003800e1002c401c04050079240300f540804150ae00c0000c2c010b0510144c400420007410b8603900a624207041c4901180d0b4880004109050305941c1d0311004400d00003c850395910603401c21024006561a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 670472491 1250 670471241 670471289
    0x131a030f031204171809091b0402130e09010509010507020a050a121b03090509060d200d05030a030b010e01050f16080d0f241203050d18110406090b030a03030e07 71
    0xf805c9900ca200d0542140011b2041000007660480e044408950159848002e030500010703410416001e00000301120010501900c2d4902e001c1c40340f1000030000c03410b800c21040841c21544090070000864200340c00b40070201c0c06c0007451100159004000d688a40c0204d1000c039283c20841149001c40e100c00120601810f40c8210346034161501200e42805903203514007008413001500200070309002c03c0c0f5840d2120321182d00e030100507104014080c240780079140c1ea0361900b1980403840c40408243c0e80c2002c0c1c8031303d5a010061016000c42800c1852403d030854035040d03402c4c080c00002c2d24401360300d005d80c40104240b100645003582c1c8841800c0c041003025101440c098580403100b00c41045882a0a9400144240710745084424046502a940c01d0b161422505580302c0c080120341c407030322142e03e0b03115010840482c51101d1700071007102d1b2001800000b00300035600701d540025006030407c1c8088206079804112966015450b0400049100c6404586400e01c40c05074043c140b4042c103000b081d441044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 670473741 1250 670472491 670472527
    0x1109120303071b111f020601051f030b03030412080d0506040b061b1f0c0210020a0e13060305100606030c020c0a05011214070203040f08030408120c0c131a030f03120417 74
    0x945401f0381340d403a030300d440a02c03540694800580d03680c001607100c0c0d00d46140c000e512186103032001070241c91402c0c0e181c15a000d18030410f5003040340c1003400040c40820504807442010b4014100304d42c184054203c0c1270010700c141c06041c82d44654014581d50b0407425000c2042302521020100d2500690220b00c008014010021100c0d031801500407814030700b0284c510380c0708032400c0c80890740b29911b076034001000b4030131002694003e4440003a5a9500800420801c00c400c00d80c100d40c01c4c07030101d0a1030416000800762105101d4990640d4046070000c401c5644403a07504080d42d000b846c055001151202041c07001d411768030b078811008010241802071459001c801081610407048180041540e560b8020b55244290f1080e05100d80244044003a1007201c4001804200c0b14202100c1001c41d4070030010f4011003c0c12120104a60703621200440d03092003034460360004504030040c00c11514030303a581da43c90744203000c0c0d02a80d00c0807420011b0100501d0166a03552600109041522444803141910000c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 670474991 1250 670473741 670473799
    0x9140310092105070b0c0c1e010516110a03050a0311030f01291219240f060e10020f0607050a0206010b03060f040c0306091109120303071b11 62
    0xc102c003554101024040c034126200340ea8841088040c07aa00c41070880303d140c220303103080007040c000e0003018a80b0303083c01c2c00c03c42c1d50101c0141c000111802d000c01882c0c6040008203c100512551007241501c039000429800040c0c2c0c1c2501b0519602d51545004600419a403040924600000300910106050601030507059a074407004213070746842d420303101e0200c03000c010180c2c40004108020803e40010164001500032a5000d803080881030711402c460155200c4c07000303040c100740d02201001c01d440c82000504006100f1400e450781c0545c1050301c010311480708000d10701d0103030000c14155416280b0070000e412146032103809480d068200b50200500da68007210840b80144214000420100001000c9a00940c0700400e09042c104102c01880081d00d214411b0703400b85651042c0c002401034182c05a50100e111128107940d0301c203011410824040e200307070903550040c1c0c418020080d10343c1d00100754000b000c206030300041050f4401d20301442415408110b040e00032051100060001030305901103801c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 670476241 1250 670474991 670475033
    0x111908010f0c080c03012907110910060c240c02060106030b2b14010e0304170703020109170f120318010507081807080a0c0303020613030914031009 65
    0x1142003010111107844068580c0c604d40f410800c0104040f13001d10034006071101d00004020071001701008505110b801c4803800351900b1014544080d000d1920381e03520b0740d0140c0781c40307840159141020070040c1402d410000c0181101d144148900060894214100780d4021480b420300070305049110003519040e084c818232020a040507598002d40c98400f448800002c08840400d242d810610390f0328038541e000400a858900e01c1c18020213000f103003030043d070160111800c0119900c510f8814903c1403200c1941c04140c10342c101d21828130043c0c0c0e0090b40ba50858014042400b40c0c4845e01d02c04604110b0104000c00c59407003070b030510020803030503040510704ca038008402800c0e0789030384c64510354261201101c1c0385c4006400c0c0c5002503c4d46046001c20240004040103d694854a81d0030b881e00d440303501c1000743c4900d000703030702c040041590400020340d01600900c03a96000e00791503980980171420f103008400c6000004400550651000c0103203d84030a18180203010f044c20714200000c1b08442582c08a00c0303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 670477491 1250 670476241 670476251
    0xf15120c0e04020603061003090209070e010e04271403070f0b0109051006120207050609031b12042108120f1513020a0c0804180605090112111908010f 66
    0x10700c41401c815881150007030710180c07956843c0020054082078003a2440145a5991048009604e454010b148140c0864071010442c03142d0342e00140081f6103e84506200303906042402c6410704814000e0a8602402007a80130303038000c189030854500c1e1100000c03031002e100c045001024841345040c0d64045502a40662100d640c8035584101550310483d01006051030401041000c40d12403101c0e466141c06034080141440718580e035241c1458000d4480156a034408913501c1c4030448058031001446000f1001000400d07090a5182014040c52194803034048116408109034181c6d5a050050140d00040351562003c40300301415040070195a16041550340070002040000504500e00d00303064000c00f28104084412034010282d44040c15007400c1124414245000400b244050030181983e03c50900f0030300c0603062194115442548240c0c42000e42200403c8403101d0008900000c5401803920b0a025140e01c0c0400d401c03110f0300801e001c010000c1c020010320399a041d8002c0408109010042c41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 670478741 1250 670477491 670477499
    0x41a1b010212060612280c200312070e06040e13030e040606050403080f0409140f0721020304140706050a230405060c0109021c05010b0118090f15120c 66
    0x1813680280e10580400d80c5403080032417048083c400104501c0c06032000622120000603000a082e6043e01c1c201401041d5580c5200d200d42051484550480c01b40500440c145903928035030203441840a02903000380640d160326000c1030f40b194030407680a0304c401400c18010307061112402c2403140c104802940019801c0320610b040d0702d0140600310441d480d40d900d1906160561b207804019034030414144415100030040012004018000c15000b29220345281d0000e18003200e5400c2918001011042040f00103285400304803501041c1c4000c074100303614010703165605c5c2d1500c0c2036a40b402e20041c200ca03100b001000112260b106c40104848503055a030040ca080800c00401c81c0c05100d04046552050140400d00041c24900003034405990b24a0000c241e81903190003058240c100d400f10042401e840c0f44030942801024080d03c0980c030360a2034101c1c140c0c48030700b00003041c85049011707941c8140d440315011488400365801c00340d00a10030170b11041303581c0d41d52151011207044c5618126100051503000003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 670479991 1250 670478741 670478749
    0x204090c140901080706030b010504080d030504021201090f12020c090c31060f12050a060f05120d030203070e180106140a090311040f0207110108010812041a1b01021206 74
    0x20704803549100101101c46c00c10800742d02800c880c0d407174241003107410700001401d60010031404800c0c84035501d00045506160050090444030032424495036030505a1001c0001e43d0172503c1108203800c00100c8940e00d80030030040b41002c4101941d241d00400c41c000b070060b0880c08000411403002c0c0142e64450594000c40ca40b4142c0b11004031640140a880804020081c000c8103604400d400d2071a142c10b9408005544008588060f15280348007035449006009d00172100400b00040c00741120b03500a1943e0650700e050f41e60440c1d0124404158010003c2000c59024001104600f00001d00b442c00214280103205443c48003407007643d00280d1101c0c40000c150403880c0c01c035a80003580342e0744d9403030881c103507190341203038811025070590019513610b450703201d040e42840544901c5105214000100403007000050040c01c06800034455900000c0d102006424590102e80440c0c680d0030517840084086006603081c0c1c041c403842c0b10441d200744203900340c10b50010360041680c088004042041621560188 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 670481241 1250 670479991 670480009
    0x1103010f0c0e0109051804140d0906020c0111030a0c050f0118061d0316050312090a020907080c07020411040302060310080f060c25060e0102090a09050c03040807030c0204090c14 78
    0x8150043d5800b1b000310711640f4540c0b01154000e0084403111074203c10300314054605400f8132003500000f00652410310030342d46d0601044181050034680041e440136070355880358036889120800f00600194100d2601004070a1041550b8100484000c011007030043d886003201000d465011982c00b4503000055180c0c614044118418000f0940203604202c184400021090003030703030742942e580c80240f214511309000f00410f60b00c03541a020107460720a10794414441c0301c44018040b1824081c01108020104003c81c09491405404480118409081c883c4030540b911517a00b001e03410100010421500741c0c106101542140c1c140c0f41285c84101c00d070421540c6848040d13400b8038201c0703000c101030f203c0d440c9103181340e040e000d6407051072035881e107480d54498003142c00380032a04850380d402040306101843e00541c0200180420501401a0704d08615003400358130008000400300b5401060510516105880c0e039080350350702a00410000c2d6030b500309018107001078450b45800d1244041940781c103040500b08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 670482491 1250 670481241 670481249
    0x1603030314010821040e0c0a020115060f5007080d020306041508010e07080c030c09130c030804180213050f06072a08070b03060d1103010f0c0e0109 65
    0x307013610300103018050000d40046811424001c070148400318100c182c0c1440540940d1010507c03a54a031041d010203425644d0701c1804504104016004108040d00820301d43d001c0e00361450615080020040c00c02400250208141c0c0320b82250306050700e1610417680036103500581c000c8003401031035065459117410320807208002cac07035141e007071100100b0703181386401658008000034008500300030402c181e5442e03620941e010804981d142c11003480d1441050065001600c5200040c0080f0004c80e40480da5418400e5000390042d01e0000000b48510701000202200a80c03014440346803555a003005241c0f41c000340101d1001ca0011004000659814400c55204030400c08145464520380340401c0410b400c0c81c14910f03086801000014001501e000994110039450ba410f41303c0c503001e19104110161144d001801150b01246003070090b12603080c00d690303000008949000310504180340400e031081c0e1007655541c2540c00d01012151140c801c0d04101501140c41e07a0b4200107081803401100c04103038a00c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 670483741 1250 670482491 670482493
    0xe0604091a2b11060c06071701170a0b07020f03030103060603020112020909060f030f0307030c0b070e060d050907150e010e06090a180b0d38010501030b011116030303140108 76
    0x1002c1c4000440d00344080710400c1c001071403e4108101c2d42c20080c105503048840310300151008144038002c9a0344041c480c0500f91820102450785043e50959681c1d105081c0040c00785c1462030006480700c1d1080003501d058070101e038140c030313102e503501d160440c098400350100301d0128810079024112050075109840c100080100040035a0320340c0c205009084940600c130729054091080c0d130a0400c1c200300014900d140c465a118030340303c04982032040511034050305000400180100780c00302c0f80c0e114003d80301032141e0140c0000d511749485940c3c0d4940300b11079114004803140310b4113040c1401d80246840608200030380314080c6c0d0110b80c00070441d0a10800301641d03070108c0d200006008056503a6a040583c1019450004030422a00c0c0020031522105004440c01c150590450300c0b01000a1805001c0713595040c00300102c5008840d1085902e00140a00303810103070380b1108500700ea1721401c0c000f600040203101ba283c3c2481141074440d100c03400d078002500071034140b0041e00503804808201038100c41c00340c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 670484991 1250 670483741 670483819
    0x3082d03180a051209040b0a0b19090e0103030c060c032007050304030836011e020a0c1503110705120a090e09070306050a0b0307060e0604091a 63
    0x85140702501d805446410020b202d160041d0000400420040c280c0b0103000c5049a1161520010401550126510030380140501481008600c3c0510169401041c45601000d040206d40ea03084543e00403580c0201c040000800000003856041001d12418500400e403d1021800c0c050003a810703180344021164001038058a0041d07040a104041c003040303407103101034031f250541d2903d500c06141c00c54000b06443e00d2040503d00382104014210740d0903118102d031110102e10110b00040e21030506000e03c4000d950059041c102c04610900050a000340d0001d06810140d40312a207814095000b207949030042490f0044038940143c2c42c8094441e003640c004002d00e040e034202020a64590005083d85003405020640800c104000682c1c05128044010080000c0c914506019003620405407d4400349403400350780c02c0d581e03103002c1089010b41c4e4203410b00b80340383d00b01c142c0403da0078440c660054150754075102210070100d004562164040904443d40100281c3e0760350702c03c0415004400c1c030f8203064030300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 670486241 1250 670484991 670485001
    0x3030e19200a080d0306061b06050709170c03010e2d0102041205160611030909090f0a0605090730080702060711090c04080a080304021903082d03 64
    0x149551007100002100301032010701c42004200740a10035005a0b08070380010405002066140c8601c1c0000e04051402240c0350b15054a454000c4403910341c0070b0440c03510340d4005908140283d00c078400a1142000282114000f001d040d51541070f100c84407031095007030201420b44404001410407101303180c80c94031220501d200101e18452940102c007041a55000e01c40094490851490b03000824018000780c40000384004440d0008103140d00b05200b0710100c0032002c8030f404800402c0e1410f00740c0c00c0e00c050209860b03541e145464003512046d0511588115039140c0c2c1004550340081c1d000340340000c12144202e4403401268405840e508000c9880b031f0000d003401c2d54070b0380b4941c500c808040c052110146000301a401041c80c0e81e02010080e03502451160138480b8608100031016070018940c21010f05182c2410525900c80c4d80b130600107070403010080081010b641d54032541e0300341c44a402d00070741c030101c2d45ca29041009422004820400e2120444001300c1c07907038094159020351240e0742c0d400707203169a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 670487491 1250 670486241 670486253
    0x2070c060f022512050a0c06030501210f02130c08060f0117340f0e03100b040609090c1719020d050f1204090b0a081209030a06051303030e19 62
    0x580444481c1620f1008000891a120f0903510072520300860140181028908040400c0d0303081d0b60195040500e403600421402c1315012080002c9280d014000708480d8041c03c129015045005019600616400f110351800c90382c5d030312810281c41c0c65203406405907a00ca0410608007121940c0e1804600c8040368003040100e070103110ba6100c40e04401031440d011404403031401c070340d1a9448043c20f9001c0e139450506a1504000b031307407040da040d40c9080547da08546020940315030710344541030501c94a0340b0340240255100d40003407010300542c5c4c00c100100c08250905007241c4880f4400c40e0030351000320120410f43c00001c51070710782c80521080305c8500102250b09000004904100c00e4078140a901c840110f901c42c203000060f0b048211200c415180c5080c540b00604803002c03201540d10a61030303081c04001581c404a1502c946022807a0116150908040401d04290201100600c1c6600e80003c10091001c00000320074414040d036810060001c41100d40d0b5600d2012040b92090307464201108400112 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 670488741 1250 670487491 670487533
    0x402090a0512031b0705040612052503140109060501060804050606061810080106020709020403170f0c0303010b0d1803021005060105040f0e0420090406020a0504031502070c060f02 79
    0x20580b01100d140006410080c0c00d541d8000c41030131000c1d08401010405407500340501c3c405003610610150301e141681c1d4823180e80e0b42c05003680a01742d410301c41c0414001d400030101040115000354030705500f103d5400000c0d001301001c040403180b6510300b400200d0441e100e003039224030031940b240c024001500d0340020062a904403210300000003006080d440c6054071407402025404540d6110542d0b554140f81e400f90402805d5040062040d2040c0702c1000426002000441c80ccc0804c6030880342d462025404011451051101c100b410303100001c00010b2842c0d25000402d003900100d5410004481c0250409641d0303400c103400940144c3c0083c118100b40303a51688919008201414098134280e994015141c0c01c0b5403562040c40185451410801804881c41e8100c0200041c00780070003c074114540041c0440d0320103070001c2d1400703038040b80c042002401802124060b58101068013100c0d40155104400380d441307508100c03840400349200081c010b00038001c00c080e40115070050402942000e9142c08191 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 670489991 1250 670488741 670488769
    0x1403090d0b060f0406090f0f05130b1807080319020a0b0105190e0702100b0a03030c1401060f27090510020d1805010b03061509040f03030e01290402090a05 68
    0x180140070f0040d01d0381d40d280b08860043c900b4030030210b943c4d1501d006d6441150402444211041c0c1030000304082400032080b00b00503664000e51502040d26007030380c079145203424020300784032503c580c0d40c012652050020151020701000308003107800109401c4200d0322000300340c4005120008401c014000c610b0408556038000864401c1c0e903402694070b4900807038000b0103071243c5002d6000158034081a0321180603841c00c0040540740d80f07140c90700d0755400400785100444007500420a1950354005040d080d005003009200d26004040c01c69203c0e50055a0901185c1c2600c59500c450241e2603103810050003a140855000800b43c5138801c0c140142801a41c01104150101c1f80c0d1210044c0365603080c04899030340342d4003d000000b190400300050614104000c0c2425400034005014050390355100c48045034059030060f4224080303591441e081d4044c2c1500300600d003c9500b05082c0820441c58aa404190700031482000b076060795100c01400124441e000c1c60036000704020605020324203200d02002200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 670491241 1250 670489991 670489999
    0xf0c0a021003020a090e060a05091902071a2a030c0c25080712030c0f050d0c0215120a02070f020a0b0301090f050106020a0f03140a0801031403090d0b06 67
    0x214540d001503032801001c48040040381c1d010501010456001c0403000140045016291440c1800c1c0d0000307204001a11620b8450718807c000201802c9090110280c001350380002907455490300e19148a0301000416060b0b0720b1803000002944215010350f05142005080e21454541070301c10561856952008144602c1e4180802070460100d404200d40e20300d40e44c418410502c4507040704010380540015070b0242c440c07548443e0080c00b10000180440c421141d140c01c09a2008015140201d10102408ac0242042c0981615540c4a0f0341061380b0225061084440e285d90043c2160394543d0f42c0140940044004480300000d1543c044032350080840c50302580304a0041c1c0a075600180341d40009030818241406c02100401c43d4030450b00070300718030603c1541c00f4800d81d810241e00940e10b2403a298040d1031089003086150034540078102900c5c49454019080f5550030740c646000d012140280300851304441d845500042ca00303000710640301c07040401007800190318025101d030303051854003400071580 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 670492491 1250 670491241 670491253
    0x5150f060906360a0c020d1b020907020f060a050702072606070c060e0102070215090d02040509010b0118030c050d031407140c0a0303082a070501150b0408030f0c 71
    0x30000d00440d0400040040346004032502800c5010402401c03000e082035002c1401d0020b0400e00035000300340100e040c002d914090002c41c230600000112480d10034000307500120034000b4424040d03400b045014840c2e0720170702140c02035100c1840c010100c41c011141e05d00142c1200074140300000c100d01080700c8104100d6144503490683c6441d1605010042d102400800c2e000d440b05010807030b990080a080c030356850021404d040701900032810900a40c3c640a91990300004d03103d1550307a420100880d030319000b5108010364501707003484a008007240100180843c180485a5600e00e641c0444201942d90096807115014540300c188648140d621800301c045c000302c02c004081c1524240b01610b03000d0f00942e0507140b0b0244c0104000c0c2040750007201e4600030000700d0014004030350410011034206111003098020a0a800202c40d0004414202d4807000100013540c071040c00f00c15084100d08007006100104140c0d5a03101d008010711031842450f19a0700309110194444200c1c10241030003440c0f003415200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 670493741 1250 670492491 670492519
    0x15100323010e100602030a09090504020301140106020309040e0703021305040f140c0a0801021207051c0906020702181e04060902060d05041110050f0f0f1605150f060906 74
    0xe15026005a090840480100b010543c440d061040c010005800039521341046030000900c0b80b4941d0203010304035904d5170042800c54600f54449116003440c81490201561203040c000d40725404003c2441c851400c10602c5080044045454011654010801c09010b40340e08010f01c00f03000024825152050031001002c00304030150b2404c03084100280141c200e400f640b20030130141c40d015400600c0745a2041c8685c645070240b40420540084060801544820a6180559520343e0021540c452141803142e14010084c0c00d40141400c2c510071a214031440c032800074104150b902c02c90b040003072000c0c600703142002103200c5205690490b00855000c542000310b500071911503030000c64450011543c4070104403d01c10103042d0304807203810483d010104060170050040c03460003a80d103c450842c000050300340c242c034a1101100c074140e40018149445001c1c900440c207a880300342100f6505800b41540f56440c0000d60106144620580f040e0300c242070712800705000051b5001003000350040d0741440742c50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 670494991 1250 670493741 670493801
    0x106060f1b14070f060f0c0323190503090c04090c06030b0d020d0312060501110706030e070f080304091103220606080313090e0613121803060207020306151003 70
    0x4005131940140b510040c03490007000078010003003000c148041000b0700307000c0f20003ea13120702446415803101000003118003000400c1001c85c0300c0c00c00f44030300405041000c10121508a4091b42c411081c140c10b4416012030740b814001912206407000741034512469042c4072182c025400403031450000340c003107099040d203540458282d480341c3c00240c010070088003ea02042c1c0300c601440b40035200038030b4040509403441c9040740e030360200350080c0024161071b41900040d0480400c00000200b00000e045d12900d6510218680c0343e50003405549450303410402056294003809084a00801d0090440e661450344d0040f440324400c5006012602c154503040c1c0050609010805003c404603082d0f08107225514140319178044469483d5a0503003a0405420020000d10005c850580c0b03507000110701004032104041110605101c01000244101190740030040c040640c1c0549a528800e03002c0b40c1058450051064846084920702a400043e920424282ca482a0000d002c0d1851100050085525444042d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 670496241 1250 670494991 670495003
    0xc030c0f030c07020909010e1c0507061406130614060a030f0c030516021b060901140d0c0e030a02030c0f041d010e120a0219031704050705030106060f1b14 68
    0x1c0c0b102c1e00c40031855409500c0c1c1054010380100c4000002c020b000d2a1070303146500c401c40800c946d03120207117101c07803c0101e0380903200300c0d29003c1c0e00c00d40800c010b01810014408820087c2d03803082c003030340c0e0000c00761180071107a110b0002503c03450890f00020f600d0034030030000c681d4885101c0600b015155002c0440300b010b240941480b240083d00e001c2001d03c1d01900d05000140200046003c540c0701d801d11111078030042240d003903402c00a0307510940d00c15007800182d800c20340d00c0c5106801903000040d039031f2203c14142d02c10000c4000c81c2e6188070015807988109a90345e0452000a5815007152036420300524004119451102c0301400c089100180c00000c00c250750502403d901103079450b0302c80340e594800d061081303440d403884039140030341000c000d6000256034040c0545a0110b1058124006080c0350081d4071070076645580305072124136071510b407030301a442d2001882058065800d048020030494042c032000c043d1011a075907040c1255a00d54692161920a00000c1c2c4001c02050f20f00c0400301028840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 670497491 1250 670496241 670496251
    0x10606022505131413122604080906070515070915110f1b090c03070507150b060a0c02150a0c030311040f17061b0d05061f0906090f0e0c030c0f03 64
    0x2070105485c64107014195210b00c40c80d103010441c131815607528813105481c0011910304001c034842410781c1d41d80b4000603148a003c1543c0c4e84404041029010800002070040da20b02074607000d00c00715102c4440680d10000d490041001540c602032107400d2461040c049112040b40541c200d4450050384403500e4245600e0300c00d0010308110340c1c0c0a400c030700d040c420003950700042220002072035880c007450024200d0141090040a4010050941d507006509400a5180020041c0301d0307583c0d4009107802814407251080c0032800343c07001c1c0664010036200441a61a083d41c552208900720760181d5080b00180b02840c00100301c043d080c80085084840440e8100142048070000c0c811a600740f4100c03440c0c0f25000706600501e112861001c0030700d44558044c1d500c2201c0380403011460fa160f5100185100d01844566070640c02c150902c1180307142c0c030010102c2103414a03140d0394030007600c2c0d00c140d00d16901c1c0c3c1d00900482c41d42c40004a0341510b600360065912070090305125042c00c20348880301c0b0155109590b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 670498741 1250 670497491 670497511
    0x6031703100911090306101401050c0c031002070b10080d03090212120705120301030804150e090906010f0515070f0c0308070305120106030c080403180e090106060225051314 76
    0x41e0081c1d035017820017030560080c40441c1040d0301946461490312809044000c00d0341040404582c48402e07107010810500c0d8210010140c8a00f500200d00307520081d0040328048e168140c902021032400c008280400c1d0540e400600600703001030603c00c00b6070107481c03440c0c801c9800c014042509949508180001300e0034500e000200f40e501c1416052080c82d10314140b40540c03801100700010000103015808550454244101c0d8810080c4119419a0980781482825401070b0f22003042140b54400030600780c0c1658400401c512502e1340760400c0c0901009000c05901c5903aa0802508020514003964982c00314810700102c0051501c0b46e5601155410400003140407800200d01c1d15035100032150b0b118090209440e00f0440214424070003009050301420160901c035860300c10f00c6200c0e031240010300103050006001102c1782000e2076158001c0c00741e4800d600042c0960440c0d01c02030035410500c0315042c1600074050020350301b04010889102c050714019004d8581d030302d0940c141c2491801c0c0ea40c2c49144428 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 670499991 1250 670498741 670498747
    0x200a03181a0712140406140c010e010b09130206030c07050c12010f050609040305030a0f02090414100605040506180f09040605070e0604230a080303012706031703100911 74
    0x316100c500f001c24000300000303121411414a184802074400c0d141195241d1400711031920f14940c00e201c0c10300c14200016065401d000c010301c030110054014200b02c120030f842030708166071345c0340420025000005000f9809001000460091904240a0201c981c010000e440c41c0620b024001010041080002041ca0351141080f074030700001803044a034004000d461002d1a844c1942d001041c1e840014505a082c680d0b4400111180070140d0581d0340307000e40500304220240780c5e00c0c46c0c10b2062004940791003203d074240b000800c1407031107072094804403103002d040e041c1402d03650b44d11011100c1d4440700340d6070003500381c10219200740d440f50881c074041e034021080000c0c28203161400820074103201d2005401007404000c20031550280350301c0c07115291081c0700480c0c84070300c103040026014061a8410300340e610000c000400d01c0750522481308200840d200c005981d1444010104050358201d1101424149000d00c0190124640c54000c50380304401075030f07144034075444046d540101d1344034582900310b80b130002c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 670501241 1250 670499991 670499993
    0x40f1401030c08070c06060f230607030f0f030f1e0c0806090105100c08070c060206091501150e030f03090f01080112080a02100f02030403200a03181a07 67
    0x2482221020600030328050222088461015000110184c201002c01a05901d0101803082c1984000061305206102c064030b00d40d5804580b1041c854101f184401b01d0070400d08503811303d0320604540b060341d41600c03560000301000382c041d540c0b4100303610320000b41626020386004596591040b541c0c1026408107801640250a80441c2225200c00b4400c4c14401c05201780909076651901c1d45046a030100d501802c1c0d003003807a90848040300c10700c600412a01022814200304407629a42000391202382d42120891b0350742c40700243e55180d228071041d40182003040103128218200e0100d001c00c040c1406c2140440110a002c240b4118091041c84c0e62500042007031b03807107441c0c42680a0a074000901c5c00240650410440d0020361880a0000340b54103c0065001d41c101e000f44288911a40462400c00c05184a05401e0b4003039402190205c0c009614030505444a100c0700380080d0820644400504c402c1d04165030a66201c20301d5020058007854100d00003030543c8480295803400505404034648030241 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 670502491 1250 670501241 670501259
    0x403060213080a031205100806090d14030c1c0b031902040f09112e020f100624030209121e0a0206160f0c061701090c0f0e0a0803040f 59
    0x71900041420b400000380d01c1c0100364030801e0b0345c2a0003890000007841d601c1d0035025a2110b120366010052602030441008945140031410091100c5035490b5400c01400031101d03a06070307100850340000203a405000416945d00092509031400849040000d03020f10360400181c605900e1400c0e2000308442580c0d04021401c1034000d0362456140d04000b40040040e580c0c40e07808582c04105000c0c0512085a045003486800c1290034002c8075030801e02d21040d510b0280c000352541c42c40c00340d01c0398500c00c4107d07004d2001d034140300d0b2400311210441040c0130701c14140b40d0380d203603000c5214800382010340a20a8410320794404034004c0941060000406071003015507449420380b144112882d055822103003110015031203200c100d6400c0d40000c5031400000006c0d08d0041604040401e02030410003c8030700105000d1f400410118038040b081800f45580d0faa603190320700590b030645501c500012800e500081ca07043c0503000002401000a250083e5142c032548040d1030740d0000d600a507042404140308004100b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 670503597 1106 670502491 670502527
    0x904050d020d11120f0f160b09190b060a03080a090f080c031f0f020307050304020f0d020f01111e21040e0411030f0703050d1107050d06091704030602 66
    0x200d02c00405290b031f0300d1010854803d106080441d40c1c11034001400761b0341d80060f80402031804150350b6003040040014040d15009072903a0408030025404c1c0c406080484007a03614480814541041d5040840c056070000c10b036a044160fa141c4551800b0400c0c11202c1e812a601078400c0018000030b0000b80240e00100781c03540e00c003000340701240358000001c2d4001e500898001c45201c01000400c400810100b400950005c41d4140d102d000394014040480c10410090603507520601881d0f4140548810b40952203c40c0c011741d00300b40c0b06091209c0c20041103c0030342041418a402c20081c0c00c90124080c1000e07000f12240310f10081140ea082203d8a600c03000300c03050303c1400e40e891a159075135040c58251107012a9140004501c1c10000040341022254018444012140b981d150f290003820302000680300303152242000740c2101d400768020b00003103114160040c0e81c0c00003a81c15440e419 = true := by decide +kernel

theorem cover : BRFrame.Cov 670323741 670503597 := by
  have h0 := BRFrame.cov_init 670323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 670323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 670323741 ≤ n) (h2 : n < 670503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
