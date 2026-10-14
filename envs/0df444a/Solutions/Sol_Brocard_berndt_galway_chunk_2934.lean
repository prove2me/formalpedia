-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2934
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:10:45.1893+00:00
-- url     : https://prove2.me/submissions/afb6dd23-6015-4e1e-b968-cec2388e9b0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 527517985 ≤ n < 527697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 527519235 1250 527517985 527518003
    0x5101217120907140915010305041b0909051912080a060e01240906081801020f030709080610030f150f060314010b0d151e0c0f080f040c05060903 64
    0x446021000e0040301c2c0c41c0010494212414000380410489600301000f1407020b0841e2680340c0000c0c20b80031403440350320076070000758428800c0d100d62294440e8080c003104480c400360040c5d01e01d42e43d04d07000c90082c00b0b410480102c1c0c00c4000d04d900f596099140d40c820302c42c03080903c2c041050007008404901898600c4d0030441c09020720f0380301740115617074a008881040201001407034240d401402d02c5142e85120f02004019104c0548415000703860b440c80040d101084070300e000d2042d560078060070355071124800c002c600408055841c0c036240742c2005805410580c01801c2c4581007400400100001220001c0a8409580010000840d80160b064880113015a1015841060300e462004020090115180c2d842061070b08001c01c1000b00403428841d01c82a040b41c0580020140c01184c21201144d401051491004a10f498607103601142c1c10300540c0c1003400400702050540741c038440c903031717a2050800340e00c03e0030745803000294142070b1546202c08076140121030040400050800250300c0c01c00207801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 527520485 1250 527519235 527519257
    0x5010f050f131b0906031a10030204030b010b07050f0303071d0111030705062509090f060e090a0302101a01030509120703030213050d200d0b010303030f05101217 71
    0x40551844484810844103c42c0082141160041407151081c40391030103200c0201a14405400c58904029501d018000d000f01010303020040800011811f01e0424001e125165046865040c0b61900c40c1c14000060111043e40d80148204242a6840500d07540e500c020040c4090620150100494208150704e040e005175200005403c0b08212700000c1703ca12030141e0840707141010b0746546041c0c211100c5984107a00117400c0510234481d20781250301c5005603041d0400d00142c116a280000505500c0448152104c1e1700301e50350340401d041d01880000e21000072984200031802190780f00c054407503200c0081e00e0400d9603c0d00044ca00d528200720050702e040d50401d02c283c442040740b4006019500c05640e00d0107180300c1481c00110b41c00d004410301241ca9120313000a161300a0488038086004050799040e5202680c00395210110319072a1099020f540030703070b901141c02c0c2c40042c101c40999901074030305800045090340800000c110b1030044a0441d1740b0000345100410320780b07039a18060080c0d2520381 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 527521735 1250 527520485 527520491
    0x32a04090e0717061f080c06130e18010506060f0f03070324230306040b0a09080a0e0319050c120309030105010905070906030c02030a0f201f05010f050f13 68
    0x4039483c41d0000b4441e1083c050f601c884045100001c2d5690741c408120311645640d41e02c059200112860490b01a0403468880c49076141119075542076602c940c1d1042d102c10001e082d401c0106030044000b0300600394003010988880b8a02134408040d2000d40c400d060020910820210201c1d034a10b109400060070100c1d09503509400608113069040f00b00860322551180340071600c2c07141840c0c0ba8188400b4418640203014180075940e5446680101d04001d2a4504403550382c00d0200006000700040e040707030b440076900c1040d0550000189407405240c0d4100c1e0b2aa07003a28840b04000074400582d40c6682c1409844001c0c04400500115285010300304a6a5065007400004510b981c3c2c160301280c8101b00a980d0f00441a50310202901203540107400280103030800c0003030b005054019408040301d030038540b074009400d4040003204201c40b4030801c02c2c10720036003105901e10f884002440d812081082581c0e8100071a52501143e81c0380302c400c0780300f054001e0700020500c15003642d940900400d01d0780050424 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 527522985 1250 527521735 527521769
    0x60f03180606140405131e12031d011802060c0304180506040513120f0e060d1406010e130c030e06130303050c0711090402030f12032a04090e07 63
    0x100d002e403605025118401d00b400d140c5001a10300f50041900030002c003d203940300304103d511100e004a050542c1ca0601c3c4100303819410000b0715901880e1080340190b6400a00c80d400e60041c21010138400d800700b0903580c1001c012500001c0121a10105543c2c1180c98a50351060f0319445410350003154003c110001040d0b0242c81c92000325002580f0494048504001c41e179a59031800d03244c0503030700070050400e4852241c0c00750118003451212008601604182c0404c100490004200350b00c00d4039814411743c3c94031980490004240c100d19048102401c001000c46005801708104480b005003a901558a9081e00c8140601a621070101a00c080c02501d400c0d103801e900c07212000c002c0b071104900113464400010640070105003511126507100d442d1903150241d070010000014005041a0b81c0b50090021000c400f441c01c00600c0092074004196548910382444e0664000071001c54008500c2411080c000c100c6a0031011035007038441e603401c00584070403100340032031505183d40c00848004101c11a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 527524235 1250 527522985 527522993
    0x101e020a0b1b032406030903090a0501020304081f020d0c0807020610140f010e03011b080a09050606120a060c090315090b011202120118020117060307060f0318 70
    0x8080c40032401241030200036250302459200010000d0940340040c03000340040781c40034811030031105940c2c20b0226071080510074280050525071041d140c0001580c400102c0d0346140c180190354070010310003400034504141ca00f48049071141c6c2c5000805038040c0003072201c03c1d20007141754151550441c61b00420031115440440107002d2001c166070034800342c4a01000200e00e600d2800a28090b1804400070700c440003010402d00001e85a9140e04c01d06001280604a0064400744034400c404040c0030300011400c890341c0c002030120840070f020750204500b00381c070b5880403078030014600e50060016140c2e040040416135802c0d0405002c1d8500900550402e145080c90a0f0301012107c00c3e40e01490008200d030802c00c9a01044802545008003408120801000030a100e003128100203400a08220248804c942e18242198500d00c04e480710a04a96000419568040d10817500759050004c1c021050400300e00095441c1068403e08040100000c502d91295200b508a200700d4007a44030300c21805802468 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 527525485 1250 527524235 527524243
    0x12001020406020601090c020309010c2a090b120304030f02030a0c03060c11150c030c2217060714070c081006051e13020c030f0705030d18050606101e02 67
    0xb00d6000144101800426000755034840e803040110590000c1d807a1824100040d5280340c03904106a90492880800c06a01144804084540d00d00100b0502500d03040035450b100f100e8407200c60f60b014001a4503025240300c0c0000498054a401441e002075408851000078500807905000801602c120074001081220a070021105904107460f02c0700f105e031101400a5485090320b040c5505130384060f01103501d021105c3c0065401001603101d030307480c0c204114401d04a03401141000c6091600318903003002842c00c025490035220035420041d001505242100422040345945843c60030180001e0302c50030001041d0002c40202000c109842c40b42110180d060014012442154001c4c0c070100031811b8480c520325031f0074402441c010601120b00b4440182007001750002004048144410403808a00c0207003c4050001648581c00841d561850710034080155520b0300d49558414139514903500010300d000c255258020b40994140300407240307400381210b40c0703414a00e0110080c4480400c500405038041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 527526735 1250 527525485 527525489
    0x20f0402071209031a04050a17040f0303020708060105090915060d0b010801090506010e0c0409020f040e280c17040c09050117070b0c061909081201080c0f060f090120010204 76
    0x6400da0818655910405602d40886c0c000303115810074520600092414002d64205652095030b15041a480710500016030b0741ea908181d000d0382c003190f01007003d16400c00580b030142406607411714032400c1141d1842d0b07441001004404003045030f440040c41603110b10444155040d040340002940356074500c003550080001c140282c6450107443c0000c50f20b40c0c0e8bd0198540030f071030250701c911b180c0b07807400c0700c0400250404400329684035400c0000240c0f01e54001e00c0e081c054180b00300c0c4c07120702038902c0c0030030080c041c040d2011200050600c8500c000d226040004070508200009074044c26035980d2811403801502c3d5080030222071316000c0041050000340c2890301141d401d10040783c044c141c0f0340001041d68000c02000c050f495000700005040c1d000d400b2521240042c034034074013082c0e4060030707a210709503a0801100700c1c0b2a002c0840040040940c20840d03070403a02015144121025071440c003150a40c0704080348802c502200186031410341c0d22440f250000c500e40d045180610114040f4124003079407140c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 527527985 1250 527526735 527526743
    0xf090907032d18031d01020f0f160909020d0602090d0c091b030b0f1c200f090f04030e0607050a06020703180b0d0903051c0603120912020f040207120903 67
    0x40303210030103c040035048090a8060320b948400021003001c0b034005851125080d0704501844104c1e080b0840c0030040145c88172062170242101725040606c00500c07610707590102c008103090a01c1c05000d41c0b509810700c03a501d40c200101613035428807440413504a1104032001040c50310b0745000001c210350b003a8406c1840c500385c11910b200c0301d91403030b80c00c4080d605010b09107640b00701008581e801c2032505c00440c07134030100a02d00500003404c2548403041c500000c1e000844030030350840841b07003103458085102e010240702225180810b041903410071700c0c426801000241484801c01031aa040e903103030400d82c1c0300d49500c00c0499055904614000010b500101012000304080244115070388111070b15080075145074030040b500b40001e081541024220134002981030040400550f2004101a45505c0c3c0616000380003250302d80c50761421020304003642a6510400c035598905100402c0c4200710019a950116034083d00901c1c4580068001c0c0709182000b88200001030b40c0b402d0081e00b1040035000c403801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 527529235 1250 527527985 527527991
    0x2124011b03020f12120c0a0201091a01330e0307120c031109010302090f04020604030c080606030f070501020c0613090606080f0906040b0718030c060210110f090907032d 74
    0x31300a038207607000d03002d051103982040f40c000030020b010b14000740040b480c680c4008581c601d0a6203600d0b40a402804000b1030302110040144240e04013085001c0b481b909040c07c0c8140642008030f04240d15403c6209802041407051040b40140d8041003c50040c0503c44044901c0045501c4d01601c046041c0c401160420002c400c80c0d1070b40e00d804c140d0340f812a50080c0c9145d542e0740d50048427080712800108102c0e0702a42c180004400310f074004000d0400b0b4034070140248500d06041c0c007054980020404030a0540c4d0200b84180b100781d90200d40c200300c108040e6001526020340b4030100060108580041003040e02d400d00c00962542d001d4031840c02483d0f80c07490b540c4562101100709494036822a07000d016a42110082811503105444840c00c12851040907100c094030384e40c440490f481190302a40040c3c3c000d40070100703010518460320078008045e0702014a44070282d010301c45c0078040c005186100c0c5950302d0004400c540260000746443e9954a10740600d900740d0541720b80c500060900788200285 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 527530485 1250 527529235 527529253
    0x20718020d0605030111040303300209040e0c1509030312090c18010f0b0c0f0607031506080f04060e10022d090a031113112124011b03020f 61
    0x107041c03142281c4203112545046c90b00381903441c03e03148519107100c0e84002d208650a07000c2c00400c450203500ad023107007401c00540ea92242c80104415034511030311514403600302c0c850314819660fa40144080c50742900003507580303e41d02071000900714010f250700d90051700080010884e500c440420300e42c090a00032241c880048080d8100481c00e01824083c1000900c080e00040c440d04003444050400b6000380c40884101d101c400c4030890512400b80c820a0100f40c0307034002d42078030340e130740710200405030000e0f1508030950310307141c0001d103007000c0058005400181d4a50725240c808005100b0704408901e0050195600c0903e0f0707406a000000500b0300302d03034a18051140031962541c5000712180c148005044040403821500c0b4039120680400f0b00960001d0b8002c80c48814055900650f100c0c18240d95619844c0e01d41c1c0444003850340520301e0031030281c6052104008030300001c6006644e004040007001d50009003054016100700a02d50000c000740f01c844081d480416500042c0001114070000c00d40388084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 527531735 1250 527530485 527530489
    0x30c091a1e043228020d090302010632060705010905070b070201030f1811040209040c050403170403170c120309030705010c0e0d030c06060e01080307030f0c030c1101020718020d0605 80
    0x1905a030300100090320f61100340013180c10034440c40d49202c80101c0040c60403043c55883e408803401c01100b00c001d41d4699004010444034100141115060010020902c1e074841c02a03280d82c10504000c0b6118034008601081404400d51141e100c981d4024101d4600e50f403501504c2000741c1004008900090410300322440448079070281e410380303880b84810200108241e075078181d500100b44d04c04c0341e0843c2d400d100c1112959120701070034030b6845c1c050710b895503901d0450500700318114001c115201d012a0402080000a0143e1281e01c030000c42102e03095203507000888075a0a209001d804503800b2100401481310003200400107040c07031880341e0020000d026100c0070070345840c080c0e041000d91001682d00076801207400780b203015a042d4412000060308544074545411001403c2c3c014226036800481c00d0010160400030300f400310860340c1040c4804000640c0c0050000e04011401401c02a01101c580c04590080140c400a0b00c1d50051005070480741040b50300080d04055100c10716642000400a254 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 527532985 1250 527531735 527531831
    0x140117150103020108070c0803070e0a05100503131106121e09030d0e0c0405090102041a070c210f0b1014030607030b061605030301030c091a1e04 64
    0x100c0c000854036a0302e903070015511603400500e100c0520503800c41c41c07400681c501004512940e82031f1104803103a103052081c80b40803030700c540215000d021403802040f4441d800c0400c9c0c07640010310350b0b031000d107051080c50900070a00804031030b81d0f000400864400d00700e43c081c940c0a441140004102c00e03800795000340e4403852030b40075038214010350000c2210081004064200703031940010070701121422010000440e0840d6000c41e9480c86c035960108090001c400c0003408000f02500341306005007010110f1b1030742d4644107414030640c566901010a0101250700e52103e40c4801504114402540b00c4c0710b091096410b107040700c0b1050821640c08001c10b40da034a903c40003d224102400501465032006000d4006011100117280d01c0301c4240070690043e614000003020091084001c0d40d100c1d491490b00c11000038883d00450b0301079040c10340001111022600910b081c2a08a134001c240c103403000e5080c0c1c0e68415603034078907400c142050030000480e490304191b000b6180d413031200d4041d000c6043d1a40d03010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 527534235 1250 527532985 527533003
    0xa24021314010e09180d1706040f0b040c120b0a030f0b1008060115020106090b06073905030615060d05091002030114011d011b060f140117 61
    0x20460000006005404036039048440419060500c1d11a43d140c0000003072060f14102c611140f03658029581d0f05100030180080e407040402410103240d003245107186040c140100408250040307a861042c001c0040d5542c020305c1502d0801360040000410140009014074025031414107880d0a00d0040856414440f502c0401c80e0b07005031007002c070700809544a80d981a0301a00d4016001000840454489014031034a0300030142014103020b40703003d10310040c3c25251a82d118925003481c240100c0301a03180c0101300d03081c0c164002c40400700302c1c2072504010b40080c111500e6660200e030200381c02d40d503160740f14511020741c1c9048080b10313040d80e1181da482807940034006503140c05c4117061000340e031580003a411441c1c0002082059510400384442e442c02280c000340c1c441006081000076031030280d40c01210351000c03404405800000760700b032031002801c8040581d80041501081e80410700600030303241c0c40f080642c00100018046459200d010201d0b041c002e02039200030600149200441810014440d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 527535485 1250 527534235 527534257
    0xf02060105010e060306060c12070b0a060302180711101409010603020a0506031e070e182401032705070e0915150d0b160c08030c0310080a2402 63
    0x80e10000703640c14042e007600050901b83d080f100a002c22110300c2030600c4000402d200c203403801ca071280102d0400341e0700001d0152458100c145040300900240e00e40101815201070b0000300b003070090304e50400894408003244e80c08050390207440050400c4407040c3d085000005d14170118810151a05103503070b404c031182d40c40025402044403030108040c2c14000090350307110444a0840b0001c16202c900c0443d0907001315505400100e020070381d00e0031860b02a43c4405140300e2028a00800e1810400b2405009819442400c404841da280e41d0100d0380309400c0100e000d0f101c60202d1801241c0b8841450103108640300c112018050882d0100c1d1402d03080d00201e124040075002003d00c001c1c00e00200d840d100000e8924000518034660002d29500c5594280d41d61a2182c000c901c2d01d1320302820403040d1307545402c100b18204620401d10501081000040e6604219490501d41d030303a440d0b001012100030300d00e902080e401d01464001c0828403419080307600d40400c650408900320580300a030241280b050703030b103580 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 527536735 1250 527535485 527535497
    0xc0c0a14011202040b0a0e01110102040915150827150403030e0d0e04050601050d0213180c0203042102191e030803131e05210a081f090e0303070f0206010501 69
    0x446c861240040302850481030511503080c0c491410340d41d09a078001c2e00051101e50302c0c1ca685003914504002850005c0110101038483c01d466032400400d0075a02600c0400c200f200d00c0b40907000c07604007102e40d101907008281210710324220714148440003002240d00303a0101e460842018070008000c5510a02207805682c5d02d42c5112404041000a0401500b0281000428040c074000c5041a10040071040d0501074007800c0e06141003c40a042c01c0e60f401012807450501d41c080301744980000a0310b00781c403031076025001d01c244101041c10400c44a40b5020b5131002340c00c802951901d240f64030348020b881c400c0c02c1c020340d03a002d1650010b072108083e2100511303141040000490402e180c4030450708051088000d88040b90008114000e052030071b01040c0c40ba03030490b80e0700c04d2420f0004000c1c0710625861a01d25070030500c1080d4058490b0f0002070a6150420020000c10b040103440745043c0c010b411003d004200020365124080d55907002203a14170003048a0500030000b42e030000441c24121203050b555a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 527537985 1250 527536735 527536747
    0xc12080603060711010f0608010f050705090604091a060a27050d0605090106090e1f05060901062601060f0807021204090903090b04080d080f04170c0c0a14011202040b 73
    0x21181c075100f407913491409568458201810745003500400004090b5040041020380021030340804440d0060503070000d204040141802c991101d000750f0b0101c65419030002205414842900d0786030391454459030784041d0010b01000c545030050001980303520350884000750b149084020007072648650003007540c444400c03149040011210b03000184d01010141c00071443c1c5a4948209041e1041d40020101e41d40181031103000703039604844bc030200c5005103070080c0103a044c0f2401140d405003042c010078040103400b80b100c1e00708a50740109484030b080c0000e00c102041da582c1400501c03500d50f030f0030301c0c50016902c0d00115140034400a4a0b0181c00e5141e00c9441c6000e2611782004005e000041d4200c003440f001000001d0300d081d0f558007900051034188003502452800f410001c0c0b42d00002051140f000c1085000c1c070000ca508107418143c0d80c0d0342071070048c0d5a813220a0f0703072524003241c2e07002440e8091080503000c68040401c0d48200145d0000ba255038000b00d0468001c0f01c140c0c0150300030203d4100e414007075 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 527539235 1250 527537985 527537987
    0x1b0503030d0b0d0b0a0c12090206040308131802030f0705310308030a0204050108100819060b0607140f010e0604022103030702060114010816080901020405040c0c120806030607 77
    0x141d0b686001409244410a15a03688600100c1210740c2070902c0c0d42d5007a0600466000740320300c01a090302c90410060180c1582c0000d030b90303014a01000e0000304020078181500c0b80c035854050058516115145004184085038102030743c022200380c114610141c01003000503000e4001e0302c541c4400b0400400c0a030803104042031090750200500c0003070302d10100001022032116001180669945100135a5850a000025001020182000f101c030100d64030100501171000c5002242105104002c00c01c15203503081140190042e0141c0540c00640003444100b00119200300344403405c850019a01d0360354451810a00702d5252003081030b10394000b040006c006240c2a881c03103182c440e228850f5407005a41d03120940c40c54000b112100c0c05640610700502204294000c1207001c40c40c00d1030044480e26100c4001d0260a03903002055003803002c16008100740681c00e4056030041c0070040e004100241003560000c1c10301d100500700761501c00f0b4180c01425118421008a482080050001c0c142034861641c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 527540485 1250 527539235 527539241
    0x90402090a0f0204090f020304060b0108071409060f040602030702041a0a0b0906071b03030809070312030c0c060c0e0a090c1e020a0f0c0503100c0e0f03071806031b0503030d 76
    0x900c92106a40c200130108601c00b0601c98108901250000141c80307203458600a802c1fa000e160149043c84803240801200603401186444070501010019071902d880c1c80100c1e00301d004440d5181c0c0c0c001c0380072078089210759000000d880203900868043c46444201041c44031110045004981c010080140c140041003480005024849000d000f0700c0c0360048075240c404045106d55424010051009000c0040c107900c049069046100e0344054250710386556980c104611010311000189074888080780e5002d405154814040c2e60054400d00c80c00c581c10500a125020f508500e9204600c0301c4808603880791548035200c0c04c101241c8681d15503020f1201035400e8500d91a82c00d0301103220b070035600e000040000c00158900c51003622868042030401003014200810706242e042002d140440710f0280c25030040c035041d282c020944400b6107030703000358000c030f0b081841c01d421a20815004180a12442c4120751184040f00c2c041c001404113400000c490600740342d01480392660551007448124030038840e42d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 527541735 1250 527540485 527540501
    0xc0c02101d1503010503121c0504033f0e102408151302030619060b0f0307022406090c0702220606020708071505040f0305010b0f090402090a 62
    0x100001044408000600c10001081040c2d20851010004100c0340c1001c00c0441c0448941e400d0050902481c201d00c0388209850042e84412541c0340d8010805040c0200d5500b9001d000c451604102660b1903c1071000c01007880845240d054020400b080c40356160b0701c2410903552910028083c0c081c0f01340705081c0a41a02510b613143c0841c0400c800720050380d0100c141c00101131540180280914141d580f160405008012a040f109003092200045e54085802584054501e04c01110510700c070000100501d1150882e00051800040c1d024445104001540c807a40c016801c598000d032001040301c1c141c1c2000380703084444a0317003103020030003078600501501e52141c141100e4900380382054000410345030030458607803817a88521a00f8140c0700d285000c1c0001030910b6000521700c1034580000d06a81e00441d21504c030030f100c090f219000695215604441c02052110500d0400c5030300c900f465402000003404a611800c4102e0760100c80c0d0510a155a1045800610b110010b0b41c3e200084030142c2510 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 527542985 1250 527541735 527541767
    0x1a030a06120501050601092310120e010e070603060303120207030309080406030f052406070f0507030305040f0f0609150e0913060f02160f0317010909060c0c0210 71
    0x100004035244820400c07007090380380604008503490400400150070185180c20040440c40c1e40d5012040a026000301803151007800d4a41007018614018100c03805144546055040d600340901c0c0a20444150049401310342c0c898144c2c1d0016584440c150304403507945c403000740442c40c110003c2c00171244642c041c0062502904000c07c1005056449402c0399000740c00c00c2001ca6980c0c9400943d100c1c640c42516403040c80a007216203d40340304000c20781559460341919110300f10016680f03003040000d034010032074280d0000c00c40328015100d280c05040d41d0498010315074448921400000c0c0e00240d50401d200b105c0d190b0311005280750500745413503900c5e00c400d07450b40c0a11000648206482d181c03809441e03ca05180c081c1807031050341a181c840156590b170300030423200c46c0c01401101e034180314022850300e005900694040081006103015205030029290f038445400d004000041d00c5511500441c5440344600c0c020401c0500c00035007901ca0301044000a5040b100c86250030343c2003401920011025420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 527544235 1250 527542985 527542991
    0x103120507080703110120030604090204021303060e06163e0d1803021e0310020403030c020a090915050a0e0307081312030c110d0501090f0311071a030a 67
    0x40c0d01c1e5503140d0f0f8040c41085000418041e04080c4403a02846002010084404030303c60b071080c003030301e450b0080c08050005841a965820000c0131075071168102e4a0480c580b2035914030841d90303800c0000c01851810298200f9000d04400124910090264107000c50141e4503084068503d6030507070006406110541c0711220b500910b414803c4482c0c144058071015400001c1001016018004003a24654540196104101c45c020b00059942c511841e88108022090140d1800c074440028601020040c0841c01e081c80014040b060542c0306984012607402542d207030f000d95a4031850311007161404800603049802c1017250000c08a402d80165401449241000c00c0c0382d2145160141164001401150540c00024041c05500a50340a400040004106010141105480191014141e40c0c0000e0810700b00807080c0a0356550705c80040045c80d0000d00800000d441071402030040101003000707601141c800c1811014007032001507680b007a0350020580c450991a0501c1c080c0880e007002e04403d5069403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 527545485 1250 527544235 527544247
    0x40e0103151e091203020c0309060a021e0d0305060f010516140f0606420708120a1505010f11070b12040308090c0d08091513050102010b09070801031205 67
    0x20b00ca604140d00268101000140c0c0f810b140780c4800c0d50034581194509240c01800451403124002c01035889e52030096440300d0317071005e03020390480c1020b400a14401c40d511103201c4000340701c503000038882a07949480d02e0401142c0c907900c04001c40010141421400500100007102c54407404040302d052061086809034085182d044200741041c0c0443d80241045d071080b0b040010520b00005900314003c08042081d018410603541e80c1c5019205013402e02c580c1c4940c400744400315010fa000c907001c05421001907520384880b140021b110380001c0e0391041302d203410540001020300c0500044012210141c551028180d8100e0090b9040c8c102541c2000f0b003030180003000a20b03006e1a50042903950341c900403001291501c0d1501405001010b00b44000341c1d800641e2090040c0c88119440740450f400400701c6032640c1071100010252581038000d02000400802c0c12038500b03a050009a0940d0003d80003440441e1903041401034003101115480006580d0000400105000702081c0070100211b18196103001c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 527546735 1250 527545485 527545511
    0x4021e07110411070218011a031902040608150a150e04021c0b0a081207170c07032004150509040302070305010c12060b09030601170a0c08010c090605040e010315 71
    0x80658a0f0302c0c01c005000204a01107282400f800d0500402c0103140e8182541001091651404d8001d25000303403c4000010a40304890710700703030502e58450780c0415540c403a00c07640021301130071042c1c0300d40c13250703140510002c0c6807854040d51040555107545080c00c4c507101540c00c00c0310b20040c00020580c000380e00300002150395420b440c91407420380c00b2440100d040036001007441071400b59503000d004942c2103040301c8102c8074015403c5441580d08600c0c12030f01044d03d98180d115912a44422041903c6007100000421508000c2c0b50418013500c035044c220600b4080920051b070313110401c41507145c100f628060042e8500207411a800c14000e10445d68060b440399103007404c46511180d400f000ca59030401d1051420300a004103400b406400c11198200004180880d640e20410b016410314040c6000da1800902e00400c88081c2d001d4004c0540a1503030307911203445000704a0320f480440080d45500001c41c025010b101294101c134504040a01c0f141e2841e2581c098249160340304e180d80c140c0310311000c0800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 527547985 1250 527546735 527546741
    0x160203060109150f0b040b0702010905030f1005011d01121a012d180b030f1f050903030717040203010b1305061e010507021507080406020706020c04021e071104 70
    0x42d180180e00000d41640c244200d1011451079449180285141942030103202e03220419181114206002140c45004d0f920040e104150241c10098041c4079070f6000034024000000e0b181090000283d040026903212001000240c070740c07854541450403240010080d01048801c1c0710041d070700620540e0190506061100e8034004280d100400c208440740f0b20071a110861526201001c141c038555900306803410708101121b0078402001c20750f8690303480d0102c05c203440038405080c10101003c281d03a8561a0140c4500001409003219100c083c6840300203103460600008603030094450342c482d050082e41006040d45c001500800c1282c065403242d038180c445494050b8440034150907054081083c1c50490240440c082c0b941034040300c0c4941c00f0121000741e0760420111140d458041d1601c04a0003000503c42003940308190006080c14400200090082d40c04101da07070595007540d080d28410b22a01d0204070580c0100320b40d060107501c11000003070008101d00e005045191056184130750a4007090000713070403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 527549235 1250 527547985 527547989
    0x3150d020a0308041203090603051905180f01021c0905150c04080d0e040c020114180a14010207230d030b0f130e0106050612060904080705160e07030e060c1602030601 73
    0x404030782031030020105034007d440c0c20040d203101e1070100041d1904400310a030799000030790200c4000d40e8410124560282d07a04c1c0402200a215040720003408504020354002e6201d00b01044a400b856141d55081d02d11038080d00c0000c682100090086d205140e04c9402221030150080c2105501084006070404d01402100083d2110b03031624480303c0b0700c3e03030244000d588601203130324116403502000038840912201c449170030003001c030404110200c0307802c0c01d0b84c5000580c0c00041c01400071900d8064801405400074500284114214250340760450081c408898226041c82c441d034204041ea8091079209921000424034010b001660804030b15010410000c0c1240e145800e4540310b05180910000c24000d44c8000e06044d00c50510f0b00d028650000c101c100c02400032842194a1400300f4140041e8006403008160003100703644000f000c4240c492102c0c10a4813515128401e13210010b03c44074028403400000018000c0580195544d17038042d0492a800b0306950606d01d071301c42c655000543c80c00c02c00580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 527550485 1250 527549235 527549249
    0x40b0604120b04142a0105070f0b04170403050a030e040603020603090d030b01020f030708030714030a0501150c0206091009080d0810090c05070b0601120504080316030203150d020a030804 82
    0xb0a030506003130003480a200b1481002d03059000080624110398046090341c50311180d40400304003024020b0040381e0510600b0005484890b01480c66424001c81001007401248258200181a642090802c1150003244400780c0150091001000864003406580280010052000583e41c0c0c81340c1c00190941c000b44c07242c044550140800e0b401943d05407003603404011090004080c3c1c6606200281d2f640e119148005154460220200300e03400d015040c22001c98286001c100d0702d03468a00764100050200f4030507080764810b201080d00a6038000d050550820781c0241c602c909c0d0008001c103200b180754a4070701c480300700098041c001540c1e003018000144c0846203990b90f40d80c1070400d0742d015190342000e60002492075160684041e081500720089440080d80b1000410642c0d40b00c2c80182c9031403d604403544c0c3c40c00d081c802000104541d400086104140002c10b019400e814400c08070100d000c100c40d908505400808026580e00c2c01460780c002283c03008080300a201d0300c2e60388145c81500140c0c0440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 527551735 1250 527550485 527550503
    0x4150201090506060102060114010c1104020708180114070602090a05090a060504140f0f07030b0a09020301030b070801080d030e121306020d0815060c0313060806121506040b060412 79
    0x1d01085001c0c0000d640040e001d10090881c1d5050042c510b01c04800030700d030a0b050000406101c4204486a0900540311a000f0411500c0c0c112a092004241d41b099400b941c0917024400c03580d0303496028038007241c00b0003040c0144909044035599204000e620000001d070340030280800018036a0b841349241c42c4104612800401c9103881c240c2400240d1301219940d6103800d250004012000206c3c0d43c10550045901c184840961990071082c0c1c02841c030000c0d090740140d0748000100d40c0703240c82c1d00118102c030b10031540000d0b1651010340480f01510280542075803904000e511031252407081d00071034554031060058070043c10040d4040600d9a124004001d140001c0c2a000c00c0600d07010b2104001d070210703605048040d840c00011031849140c0d00441c4c0c0703200340004202c60181c0c03c0b0401c1910403a003040300c9000301c4551a00c0c0080c01c0f02c90101c51141c07180384c855100c2c0c45800300120340d40050250351695056682c94000800003d4100360808581011040c0030008402c8040a22000c945000b00704c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 527552985 1250 527551735 527551751
    0x91221030b0301141509040317130c080102071a0705090a170f120a030c090503010c0e030c0301090819050906030f06091602190318181d1902030304150201 68
    0x316095489860312408121413200800201c521541030a20540c002210032030400e50319071030700b0b444c00c514101140340c20201036000c104405000c103071001c0146005589807000381e0703582c18060f801d0b44181203000301041280c0240c00980c030b1968191036081841410300a00f42440d0001141e440301c4c0079441001e10104c0c100c0d0310101d0a0041c01060f0b050312241c40075080c14032a03010000128400c0051000030948d80d0700d682006144a00910000b800700100240540508208010b146100d12180940700380038000d4460410b140509c40c0d0221a81c1c807500850405100303000c1318280c070908030311100074000d00b00244071143d95000015803064100d0540854a420400c1c28030510f45030041610b02c000801c4441d031501c6c145c0005451180050700c03007101c4c14100e014030701102c0c900c01081001e680a080d118000c0b641a4200e03507540c81400c66810200066420031100c8507254015220000080d0000c11410000c14000c1940c1d0120b02d0020f005c4910700343e622846440144c01da42c002e2001030359184a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 527554235 1250 527552985 527552989
    0xc10020d050903031b0d020906070f02041508070317091207030303050708281407111015211514060d020604180e0d020703170307091221030b 62
    0x80d15810000410045013540750804a00f011100110303000c4000c80408642074a6215564044811145c006000c841d141c9581c1d1030b0041c25a005080200e00c00d074101401c0880340d02005c0140740803a00740c14024900702c0e00e1903d480c200360350b1444c2d42002c0703079004001d000300d1903e0761511020008460b1006020b42c528604000b0112100070b440c00c0300300200003003448855200c14400e50340c989000000714140f00d9041d442270004140c0314000e02441d4202d0820000c109411160764580c0ca030ba407109032060402c0e408110710450300c4250050342a00d1038203100307101886150150003854400000c0401a00c0d038075454050b82280d03a00400004d0f1910781030380500d014207186030950040c100b55090f290140e02c030345c002405030059010310b4400c041d5035500031074040000c0d00001401191101500d080245014000351503910341e01040d109074044c845071040f0104010102d170320400d1941c3d1017110307841c24115222942c03440700d00151442600d550721030520400e031204cc441000b0305c503100020aa5503801c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 527555485 1250 527554235 527554241
    0x30c0a120503010302130e0102070204110a02070803091f020f01050103060204090e010b0a1806031e05010524010509180a09051c020318061204051006120519080c10020d 74
    0x3103504000051004200688499404074400807032000c01282c080c5181203414024010b201c4060342c0181080716007010000e400e0018071110781c0b01c0e400d03151030a41340c58926659201da201c1c1140c105c1999450340e60803081e400e161015540c03207031041d22038054a503120542900c4080e0005d0350055800a410030a03402e5a20410f01c808419500a00181e0341e034000181c0c00c4090f0b4450b2086c3d11002035207c1c080c100c0140d0000303001d95800310f0720030700040e00c0040d500204405070a08580a40c07820001c1a000f0075024036a02600341c0d6405440780c1020b00d04c004407920f8004051040c1c004620241d01c000461004100030f210b1644464001110052820210b1410300c01d028208500c0c1c190340005005194040308940c514802455061100581e00000c0f0715188a540c210341040d0a07030005000c20840082682045104407440030b01c03aa03070b21070b18142180469614020155400000e00c0120307020307070b4480d15090070b005207d01414540380701145810240c0d840c0ea4484500c0d400a030101160640784 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 527556735 1250 527555485 527555513
    0x5040e0f160e03160b091503160c020f3d0504050913080a020607090b030106120c230904050108010209090c2b0f050a0504081b070305030c0a 62
    0x44140c941098041e454401616003807001c00c11004094071071954a040000900c4c0702244100d03500c00594800e013040064111504aa2003410445100000102090240c038090a002c0b01d00b0352407010800f03416600a43c0107181207802c25481c0c0700c0c10001d0395559058298044900f2521030407601e00700044600030070f444807103002024910740c40000c0154800c0c10380301a10703003c0d2a4400c4503103d0300410917501000d080010581d00001640074684c50380401c0840c019451a103c4082c40f41c0c541e010510307070780170901810001490108003501035261036040103d02020a06011503044035030703903000c03100e0a110780401d1004180007507926070700c1c04d10707104003401404400000c605200380800022030212000c0d0032045d03103a0011030707800e01c2c510105059000d05401c2880180d44007031081c0946005d0a03140011072103240c54580068500d00140c091244101e03801040c103071521203210722101c00381c3e2170b000350254030340b04016022000400400c001d01c4c0d441c294800500321100c0038034045031701b54100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 527557985 1250 527556735 527556751
    0x82b0f05070f0f0207091829160807050d0e0d0f3e1f2310170304030821010f08030706051902210901060501082403030a05040e 56
    0x1110000c00b80700c1e80070900030142ca91b1405c0c003013001c1c42c0042c181c000007040110007174581107200b01c140000e08804a01c5900c13484001c0d800d0301060f5280440b900388660400f08080206420100003146103210f007006060418418900148821402d0001413814880c2017142010691000d08040100d40001c101d2103081f02e500410001c148440365100d120790710301010500345400c0c030104008100010720050131a045584800c010300d0041c0e10a81d0050308d1035501c554101ca6041650341404010046164030611101100f00341d0585080c001c070300d45418150f080500703070006200210000700d101c07004007a811101d0130180c201030052502ca0842d00f00c1070380543e44120603000c040250b0103002c02038441403900b220f00054241e40b045540030044c0a440c09032501c45100140010b00001140800c24100c801c00103101081da07903000e64070b401c8400a001e0240400c168500090310b045280078102100303a41007045280c241103a501007807454002c440000c01044020409202d030701c0400021550100300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 527559235 1250 527557985 527557997
    0x1225090603020f0f01020312070206041b06170901110715050a06030c0303030905011515110f12090301060509070c060506010c0f0f1406070c05010612082b0f05070f 72
    0x2550780080c41c200300038400540a00d10800b0600a146e0003072044d941c5002441100340703510302d070040009480302021101224000f1103444640f0002c140e4004045c180c0b481d584600071000d10326240007403040c500408030603166403241401202c04080c440500911032158004007100354100704000c0130b5135030080c01145001c0c600039081010031070400c00501260703010b083c0080d0b0890142041c90161169078103500c0185407050740003401864001d4400301c100030342e6540200720241c01c5481034440754010320354226036001c180217030344910303200000b05440c41c001400045c40f10365423001b1500780c0d0310885203a000b16101c2c05102c0300707000c02e40c0666940100246815080e50880e83d8503151004200c100140038000c0c4156403c0412150768090700540040000310b03070451409101c000c2241613042004c0320341d0350800c9030011b602c0301d2883c0400c1101e41c2c4065140e040181c1480000840001074151100401800c1018a001c080c580304507048071300461008901807800704c401501c20742e1407995030010003803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 527560485 1250 527559235 527559239
    0xb0c061303021221180c0405060306070e1908010c140306090c03040501090506311a04082b0605091009051024080f0c1812250906 57
    0x1901084820042082d50780c0142c036118109070b2418510484807074502e07058031840c24040041c1703810740014030101d1036800302c813440c0f01e07440180010350b00244c4040b60164808004a18114040c0c2c1424038120310247c921088420389622840400002e40e00c00da80720f0b551248070034144c0c0e030300c000e5050003009140800380c51818154007107945400c00a100403040740b40803002c98100070003900320020040d005004c560882c18031600160107840703940b40400c405440c40340e0201405480e440000165508500c4801030517407030008904854400400458a21038104290740e000c4258000c001415040750f2600c08800c1010284a01114100e03008030344a090781c2020041411240c107001d8080c0ca41580b00803403140c980c0501a42c91910310307001180e050100c0c0d200d41d002d0810004d0002504411a0384002568481c81402c40c1da08505403070006000c601040508180c82410340c0c2c1415440010340403000849011305240d0074100406c81d41034403103914a01c1003800c00c2120107058042d20021001b001302c18 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 527561735 1250 527560485 527560487
    0x507090509040317070e030609011a0a0e1501031d030c101b0c0c090603140d030e06041221240602070e100317032215051803040b0c061303 61
    0x100d207501a5691155144c009904540300300001104008094100e17001c0d4202643c040d800307003c1c10780e090070a02482d00d01c0c00d03280303140a007240310403503030b040003104e0458440412002e00e44011003c954181601d48040e9444200100c001081c101d4014002d151100108048030b4141450104859135690519841c2c2c1c003006020031000e0018441c03810a0001c641507450041e103011050f5203c41c0466141440000611001c4904d20300440c02e15010745a2000c070b0154180c0450f02603020500c440d074417050000340040c4803103c521805003454180580c12415000c6500c180b071410140c800c49644c2ca8101829003030750b0f025400c0c0b01d400c42c0010305d01071942c203040000759a58140d110340240c0c1550000858403001d005110000950f8110064000080c818460391160f9402501d12610b200200480d50250a4424000b840701c01d81c001038400384828845501d9001c0e0801a10100e44042c0c540581c80f00c0381010030003400103001c5030310782c152104480b803415828540d0040c42000120314080c1600300203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 527562985 1250 527561735 527561747
    0x14030615091315090204140906280c030c1206141905060c070e0a061406030c0d051014010503010b0a030e030f0d09020f010c0209070503070e0a030605070905090403 72
    0x11400c1d100118240e45040c1c000340300c034204002c060030b402e071982682455000310350801c0c9009402a03800380240040c20104c90900d64084440c480c85c1d0f08141d0100e403c1640b0242240c88070f58404103540100c03055140c110044810200d60f020210340d440d021100c100382c021024000460800d2010080b4515040310202d498040c444018851402110000085001840008098a0302900c0d168441c00d03481c42444d0b841e0080e000b11100b008412000881174003550144d0000d50380850f89244a104100301889103d0700050710b45100d4040c00d002c1d00c1011744051055521503040c0d4042c03800d000f4542140c95041704003d24889040140800042c001034a01c0700482e540440245400103281e42c4030914070b81035001d60056400b2407500003c000b0183d0041e504502c640c107000702c0f0040442040ca8005441001c3c100380300030f4101a69400145c8814003c40203142d03c1400c44c28110285203004001072403000c01500102c42099070b03007040c868180e5100c800d510180400b44c40003015401c140d20302400c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 527564235 1250 527562985 527563021
    0x2030a020f012604140708031e0f070609020406060e0f0918060a020c0d260a0f0608030c0f0109020303040e103305210408070b10140306 60
    0xd5010300c407028219900c2040600c0e6032002c80c005041c42e00c0c1e440001c0b800f00c12010f82c1e095401113000040c1402a540c0411030310100c070503034002581341c070a50a809824406d6024101307442c5010a214400c0c0031071101d0001c0a10340d1041d00000741d51b07045841007000b00c0742103405c00c408108203400304a0b4161190040502107076801c80e00000c89a55066030000a00700c032561207182c40c028bd4040c030500310040c0d00a0407030520400c0035a40c110b18860002c94410302900c0071080c202031011006091424082803054005400e181c4c046040341a500000040c6c1d5169444000168400111441e9038103090100ca9050b203411002071003580c3c00c580000b13643e400b982c00395040e42601c04021500d01c04002c003890f0010039400c0030320800e142041c2405490711511035089407000c00100801205140b14404590954051003451450032818195130f211100000340200c440070010002c0b000403070012900b40b4441c1b08a1900000ba8a00b480c69540b012a40d004503c1e000354000c00900c1118140e41e9081700d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 527565485 1250 527564235 527564239
    0x8061005191d04091209150905040c02160807060e0f01080c03090109020d08040617060a1503110d23011802090117090105090c060708040b0c03041d010501081302030a02 74
    0x50416501030004030011014850b1a801841d010785001044184c0c5c062541c0c8031426100d07610f240d5620f4644051a44030b041c1030400141d4221030900c010314040d4001d040c0c03903a8500c12240c05040f900c10213608820150804403640c2c1c4403070300402489500054003507817108180d810070640c111044c006420311201410003c5411404000504513400950140040580040c40312255031400d0410700d806620900810000440740c3d001640300c1c000078000d090254002401c4070103001c0c64440445030301c100fa201150f0070152504401c60859640c240a0300303910582ca01d000418211040100c5055814541030000c0582d00c0001040b81701c03400700010b03034500c20320180540da500d0100c0040714885201c4524903920015503084c800f2240e01540700621400b013120803581108030302c00412415010704d0368020320720b800c200320500401200c4005806d003540c01e202100d08254548407000d01e09071802d00480b03004103407000104029a0311010098200d40c40b8400f0b510480e0554001c25212641030f40080c1c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 527566735 1250 527565485 527565497
    0x503060105060a020a080f030f13050a020f0103060e1009060f031716080313111c11030a05061509101401030c2106140f3d0806100519 59
    0x80725030300034410640780c29440509140e91f0b4407060018609900300303455040a0558403c0000d40d8054805007000300301e6046001002c45400e603608014400d40e04024483c105078071800001440720254290b0b070301403e01030144907a0b59041956140840310603900295551009481c00c10200c1c1c892000d4800301d08603a00004d07501d603903c84017441c00d4403196034000c052030000006c0001240039140c14484040c800c40c101c049968000c41006405106580e00c03da8042086004c14005900001d038250701040113415106545c82da91901800c000048030403c0400c100b86d03c03014601e24140c0d0550707502c003251040c464002401c084403105455150652035061523954101c242e11a402241903404100c10a590725034804401d00b103c0300640860700c110b028481e03420b44a0111031424540f8641c07a000c0c0500040f100c0c008010960100050584000c12046005030030065000d044412216081c030090300e07216030909041d01480000001415040c00b000b4092017145c510410704000d0720900a80c40c5095 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 527567985 1250 527566735 527566747
    0x80c1305131b0b070602130b0918130f0819020d050a1215080703230303190e060a06290a0c03020f07060314010f0303020a060c180303091a04050306010506 68
    0x50404110941140b210b0f600e0114412003004510780080c10b200380c94000d200300300f80d520041d10790741c0e00501e001154001040e1882e81c0301d00b01c403510780960000c4440c2c07040140f2070f0140c48400c1b0780d000c6150246d65846000480d0788115110884c0c2d04900100c900c010320500c103101c100101203000b041206000c01c420206010b0204503a07800c80c0020b41043d003a400109507640200307079a110642e100c01c42d610180480b00e02480310b0402d28804940000d82c01071451035961303146c6907d203501c0041000f05025502c90412000041c10031046105da1041b910000c1c01508141d0f0b030361410b0100080340400302104032034051140e03803e501642d01c1d820660410050700011458184d0604c109450591018412007034001202585500b001401a4210100b560142d132116050700c20511680400740159029501c01030000f40150f0100e29410240d161011611003042001e0682000300d40c0164001200404c0034000300132400480c50344d40c031000807945c0c034003071800000c06d888240c1441071504ca1b0002081c0d07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 527569235 1250 527567985 527568023
    0xc121e030209040e0f100608030c0309060703020a061b0306080105060a091d0109060510060203071208180a0c061202040302150904020f040b0c1002070f0204051f080c130513 76
    0x121311200c0c1e41058825810f803502209035101e001c540c0c20103ca03801c1035000240c0e000c01008a071a2030852102461400140701c040c0f049560140d00c044007140b1800c8210f1012036035a200750001744681c41d802030241121500c2c0281518200d803c000c403035034504810b011450307962100d98001c8800c0140042000640c01d41c00541e0b032450361000490741d5003044004401c008030f5610542c031480302c074145004081d40700c100803030356401010001044240b280ea25440218051a85903078007070520003070480380301003d03642d0b14200030604c8000c66454940302d80a2021542010034019440c0303910104500b4189185c00254224040d01c1d44150a200009100d06c3e181d1600c1e0102c7d00d000d41440302c221b035141d03552500c03100f40e9480041102c007580203040c245802c014050089455003a001840980d17007280580030403008000180c456030b280600c40d41007078200100c8081013001488000701034900c050000c4140100c0720299150311140300d150608206100608200303e0205c107401540030b110107640100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 527570485 1250 527569235 527569241
    0xc011b051611040c2a0506240a03030503040507291e04030b0f0903181309050d050a0305090303010302030a031d03160602011a0604060309210c121e03020904 69
    0x201d403d8009003412130b881c18058020784003484803994043c056101e004c184907640c4090f052200c2c010701e01e4118001185080a5414410b843c00580740c02c030404051680d0002596190741b5401200400e20100c00c000034071400340042002015901c04003011112240c44c00340c64482c1900d100001c43c4004140200130b10b0004110700c0701c00d420b10700400d549030340b82e080c028510346c0c0846441003c029040001424a000441a20000038481200c036045402e40405c04c091300b0034550181c50a6691400420302041c4100a84120310300300f81c56981c0d80d1488420000c05403a001131002120394020001000107880000340c40c40e00d5505481d02e4400382c0078209115100e012105410784d490320651507060107943e0995104021100c5980007046079a0769401c111081e480c0d6007ea8a620441c140070801106000e40c004110b03851080d000e41c40a80c0d0b50b485c3c010040b000304070f03504c0000f0f4400d1130007008200320a20b075500103038524100424199801c00f0802c02080c81007411a04040d00800c50340c25a4440da0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 527571735 1250 527570485 527570513
    0x20a06050108010203090609031908040519060501080705010201020f030403050f0f07061422120210050a05010f0b0705030d090614090c030d0c020f191a0c011b0516 72
    0x240080c022965507824043c003070342007550401c503d8029040450144d00340041101c005644800502c0c1081040c07030300940314000003c0041c1d9160081c01d4862024070030300744461000c41e1007031700c1c0021254100903806160102d01e81045056a10421840320044603490540e40c0c0142d161070302c666682d000e5101e0003554020801c6016640f940898180b0400030917030050300300703083c41030b202040d140d4410703140e5801d40c112103076076681c0300d030294000300082085200c1001c0709110a004a580e0851440e55490403154100e07104003145680302c00502c0001d028002420045c142151034074180806074503501d8403031040300204250b040e0380c0d9a20900304049500441203105080014050b50f141c100c0c50b064444650348402d5211340940101c02d50030a0144841600c15500942500720015070041403041060a0881555000c4081c8000060700c00b62400484080c0500d40f0b039082c1c580c1035130f0004900391101028501c507803040118402030680e522006549011030880300b0510840024100401000b440b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 527572985 1250 527571735 527571743
    0xa1a03030a0306151e080a0e1501030b06190b070f0804090c03061703070609060e0a0807140d0e0d1b0603140108011802010c06060f0e04140d0504090c020a 68
    0x401c8030652190154440c41c2110761003011103100c040320140442c1d10840b181c0b9003900c0f2050b45215103113950b101d4100359601c565800b5000a0b1501d1403070303030181340c114554900a5210300e40c0e40180100980000f0140c3c101c01c040e00c0c405000c1020420b07800030140c180c02200c1508802103890800d10006450944105030800203295a030354941e54110050a5590514000300b42446030018900c902d60700145280ca24400145003080a01c1c2c4d91040a000403a40590f4140e0b202c016240c0140000e2118540c1e191040d02c055940d00c2c1c1500c0c00c03070072009410075182942e81000880b080440d03046640c5030010901200c000704141020318210510b0000ca03110030798120054600030030902d415034001107181e02c080402075002e0780d0340c0305120300383d8003010181c07200d01d05180c000c000194041d6018201c428071030080803409a0b1104480c528031181e69104450148001041c40140030600c4440c810250004010385014500070f1406040d034451440744020055070340210b40314962080c40320350041c41e40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 527574235 1250 527572985 527572987
    0x50106030b03010b01020708030915090303040906050102120a0915020f01050f010609121703060d080f09040e0c010c02060a03200a030b010c24091e030801050a030203060a1a0303 78
    0x114940200141030102649000f5032805040100541c0000762603000c8a0903e00190b07c2c1607a40b10a0040030240c4a4100b03003c040103111407905a6070a001610140600402c0066810302d40400281b07442100041c040c03542c4002c200c0284c4090340000a98203444a012003030605c0c0b0007000040f0328002051940c080703c2d528020070300401487d00352600381221000c1d0b41e080505c0e40c69030102802e00700711030f500502c000c14402001482007010700165601c03c20080c03c502803284552a09102039006070720b0f41500c0301c4000342d07080c51460144904001d1080728402000300380705020010302070150800004e4030480d004500b03611703441d01c0b0b500700c1285410150310ae00301c1025000d0b6907081d5608403201c01e07c08613003041555185544100728110100d500041c211014107400700c0590400500c80e141c482c815901c0e03080c40c50100c0c01c481d20f40d2140440c03d00048188088500700104201c9043e00014480c042034102000943c0d000030305030317070001c3d141f5000203404d00800904001c1c2d140500c0c286500740c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 527575485 1250 527574235 527574239
    0x110a06060e010512031803070302090103031205160e010c050c1203040e070f0221040e040305030f0f01081002030a0e150103050d09030816110910061215030b190501 72
    0x51260061000c44060700125012641c0314003c0148441690300095840d40c0140840480280b4041e0300844001d0003406032181c3d16101d802040e0106000d030804c1e40490300c0600061840009445100d0340b0441d22040e0309a00c2c1c080e490014241801014540e04001d5911400c80c02e200b000d100440c003002d001400c100c00c1510741c0184c03a459420500c1080c040165070000249564019503209101000310b501920018440e81a810362248003e2001c8862200511000c103400d40040052405180240c50309522850040b05508040d44001c014041003914840100801400040e002d608401d003100702603103c0c2e5681c61070900419021481c000d543c4100f0202d00d5554040c00030060580b405541902d094100c0d080080c0d401214a02c00200844010000041401c245484100003144104a0300040d01c02d044005820b101d4156465810303103100b07180c100907643d00b02e0716250f050f5107110000d106101031407116050b5028a031001811000803080000c3c1e140440014007a8a81001002044556 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 527576735 1250 527575485 527575493
    0xe090a1e0f0902030105090a0203060714040305030f09120c061602180708070801060309020f040518060a1b2a08160807030f020c1005090102160b090301060f12060507110a 75
    0x1e0043e4029460318005c1900d1000c0442c04c0445940c018000348800c1c1c5074014119840000b0a406180300740c011f020200000b00c09000800818408925458540172810100280c2c80c5007070321030107240d07840361401c00d40548070b2806440b44a40d1901858540d19141d0001c2004a4031003450921001413900810065680103001d050140e0000e98030300180d682ca07041c041d000c648944501a40c0041c04000780d1010340707080c3d04a2507210720502c6100d03004002e86801d640c503105050340c8c041701341602c0300c42c5498a00c2c641003d040c41c2d5a070929040303120860000490410071903070380240f104010071001180600c80700d502100d070003003035014800f4103d00c05070034441402d402038581200029604032096001030700c00191602900030080000300400109032080c0c1399030340081c100c030b4154000c0701d022800c16030051a4000040c10118a0150340d07540c110b00300760071a045508101c20130f880710041442180d5001a004540c0d9501140001e22038461803410b4941c81c00c001811649886191150402c00c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 527577985 1250 527576735 527576741
    0xb04050a0617030a0203030408071e140609031611270924070327031d0d031709011808070209010801020f0904180611040e01060e090a1e0f 61
    0x440048210030440300e1280b02194907031080380c03070720b100591090001c5400f10f00c0c208014a155881030444d40303003041e040d013040003140b0b41100701950341070010780c107030030440310140b1001d644410000065840c10070301c01c0320442072001c010b0000d841d84c0d83d2105a08038548a00c841c1d072800c1c040700b082060f604e007081010046001d0040744d14a900b40125005060550380307519100072500441007100400d03a403642030483c01044a16800800c1c2a00240c1d06148003034160318090206010303968440131401441c0d89c1e51056a02c81d60b405000d102c83c1d03555100172036440f104030755505841031913484154603501d124074050320540d9442000d25215201041c1027103003460041825920a0b2403a02c0c4907039072140e80c0c500301d0043d17400400440004208034009403929520244400180e605000d0503801c56441c1c40f000c031080c554880c1c817095400a000d00c0341d450402d100303500401c0380c1e28002c0b41100c1c2020100380e01c08405044044110f4444821030540e03498042089103905c8019410003840c52946010b60103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 527579235 1250 527577985 527577989
    0x2120c010207231c08130f200f031507110c0a090914060c090402090604090c0f020f0705030d080601050d0905030a09170303010b030621010b0a0b0c0706030b040b04050a06 75
    0x125119981d1044e05284e00c20f94210b0134030354281c640300c100d680c6080070311104200c610801ca609441900d01c1100040440c1010803084803501c0c103480c001380000040c0006000c0010485201f81c1c040c0d604010107190081c40c0d9580f01c0102d10f001c81c0900c5003020020302c0c010740350041c1f40d030010302410040303100c8440f980120821401303007004c540c04101e07007102c2c103403038040c19281801001130130400ca40b00750515400420781503501401da40c0c642680c0f5002403040310717000360b84507002403012a204070f40c0755410810340341308601000c0504074452601000940d503c607182c40c0340062041d950000b91b8940e008d40f080c2ca1041100d2401806501c43c0c1d49803c40d200c0d40f00307038200c201080e460400410407003042104d080c10104014020351659007000e20200ca02d40000f4151503000080c00401c005180e02c0b01e0748015804000400030a003d42c07807d04110304140b00d50401c00c0c1c004000d004ac00342e030250004549040b1a468100003608150800c046009000c0b120503864209080030f0600181c1c0904e42e0003441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 527580485 1250 527579235 527579303
    0xf070e0406110c0c100905060313051509060a050a06050607031206140a1403011d0106030209010b0708030714090315100909030c0818090702010b0f06090102120c010207 74
    0x1c10b071140244103040e8000c207581610507902484071410b4a007440c0643c00d00700d0742503045c0700210513524400264160300c1100d1009405402440c3d0904011041014181290a003100e5581c24500141081c5d03070741e81d00030880360842c1d0301c0340c0114071014130302e07440b0501070040a400b8035a81e500700d0a0192510300701982c101e6400e0303e001c5000030740d280307103144001c40004000c021088085c40e040c03181104d284801249a8195600c1c5d140102d204140fa200d14115000c0d80c00215565156004004120340160b0100302d4038030007000301c41e001503219411240d01c20468201001920441c840244a60241458481d05407003014141d29500d90360f030411b03500c070f0808840100030044e00c80d54201c060f141c50240c02404242e603241500005844140036080a2101011a5140d02d6205002503c1c041d000d03942d000c0580d5488441c80240d0038500d881a02a00c410303291180782001d1100000e5548000340e54108203c000441c1002c6090802e40407200d400740c12013410f0707200b42c0c0403c12641c010303110041041c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 527581735 1250 527580485 527580491
    0x406020a1109010602030d0e0c031609110307050301030803090f1f051008070b1b0102070c05040c170a09080702060c160e01080c040506060c011b030605150d020a020f070e0406 77
    0x1d480c01221040c142d559a5000d1342c1810003003440385019007000403000c4098007900c031080304603441c200506100303000d414609008492401078000304940104c4064040c42070f0030000c0100c0707250000d044a0440e0b80c007550703c41e581e44d01c41d0002401d1050030b425003d4207002e69058501100340310340100403283c200d640104031548600b500c18110350898810a181c03a005800108800f11a1201920040000703040500b00641904c502e2030890780105400c1700c202d400c60a083c030603400d1600c510908900365003440c03036111100c4603c0b5502100002c0c026032049444468241c02c106405068039034495015080544440b500d6124603103c4130b0840c4c076913860020807080061040c0c21003034100c0c1200c507290042e016007a040014000588401003095070021001c0200a4070003000744200242880c00b080181c44018041000030184c41950303210320f100b50706100035064031300d003400100c0340d9420320b0940050ba5014807120603814141488560310b26030052000000d000303100e075140544241c6c0b14100030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 527582985 1250 527581735 527581763
    0xa03081608060d032607050703030f02131503060306020408100506090c12130219061103040e011e0b07030201090b10140f0109090c030621030203120c0d020406020a 72
    0x403500e5034001c60b0703810b91041065400d1400300c0d01402554202c11421006200100c5440944144030350b015214000020000685441415894458071505042880080d860160642c00042c1504068001c002d1403441003142198101d0003503101c44000c50740110b0554449598020380c585600340004807001c04d609110004442d468071089981c4640b414203000c608101d04018401440d20000b85525843c4800c49000000b42e03403982d406032204141241030020780360400c0c1d00100b03c030035414010b50745a48288014801d11080c0025103055035040240d01c240360491003c44030404d003007035125480710780000599100f415410f400501e4624000c032404105c81c3c5400b00d40c41c4603440c003807280c0046903150b5011442d580c80e0035906040045014074180d42c03242e8540400305c049600405500000c01e40e142ca00b00400030780024044054182c200a00249c4003040d1801b07900e920030303841e5000c4400080000035646101718420348003003281e1420119121911070202941e90080900251481d810002c1c0c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 527584235 1250 527582985 527582987
    0x12021f09021320090a05041e110307021005090a0602130819021807030b0909010c0e10052a07031109090c01021e0a0204090807020a0b030c1603020f0a030816 69
    0x758200c03d5900c00f902e89030b612510105001650480116698028240c1c400010746648500a5005018400c0598900d003240128820704580001c03c0e2034150010070310405c070030141c01003089800b940036240003041607641c01c1d004909000e1a02c000804423880490180c4058501080060681e151102143c107455100c90b14502a04125800254000003544242c80002002c0308942d40081e00c9050200389090310100241c0010411100302480341c0d50392140354001903000800244800c03081d108000700050300301d0700908a200e452001068035200504403903280305220102c007803000081c001d9401d159180d01d01883d2002e0401c5216108080c0c0b0b401160030028081644d14054005030004c03c0140f40544040c100d04261208056980c02031481c0c2c040075813241c0c000d0f21901c03441040341c540e031508a4810004440102d800c41c4c110504280b04011803117460200711041780526103a4101c050081e80380480c80c00382c204000b14070601859480300109504044154022144e08082200710b0811b50701c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 527585485 1250 527584235 527584241
    0xf03030305011e0f090b03010b121b0402030f04121107031506080d0206061009080f25030c0b030a110a030608121c0e15010305030d050f0108030712021f090213 70
    0x40e640c1000315000200031720300740e40c0d02050311101d000e80080341440a0f0340c002520003d03d070500c000703a0707040010340c606034929404035500001d10032901107042d402c00c454583c41c4640010b0004001c000064503480b0f0441c0130b41d913500805144c007008c07903160315181e10304206a9040d50003404101410038202040015001c100e00c0c540400d658000d144a1b61a0010082c0c100c8100e0500014480d00b5000410f00d01d0040c001081c18145590007081135511007442c00c060b03a000348541310300e10904101c0034000034540c0d80102e8102e9060220003501c80c3c641c801134a0041010003564246060000b584907425034040d04004119618401a11010b4203421b000c40998401d03207402e41c034280001c142102d400c0310607901461280300c844c012140e16030540d044460b900176080e001a91141c2c000f050050000c10306010782076100c01440740c070207110752402c2c610035a01d004000b8020031048900503c500070b648200604050280030f11a40c040340415045c0400007014a460141e0040720070503522015551140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 527586735 1250 527585485 527585489
    0xb06161101110d030c140406053015010203091804170316050d02040b040608100b0a0e0913051c080c0f0313060f06090f0507020703110105130f03030305011e 69
    0x28050a440358100c5004c034020203440015005004483e80030038954107128000e44007402d00c0f5141c4959130f5070205201a081c1c0c0a031000c3e2211605040302b00c00c4c8511070361000c0ca0304920810000e60b625402c8200627415070040040443d040407032008010b07015030b660380400340200d01480d850071103581c404104000c1d0388411203c4500c500000120b00001d940729000030701d111008031a0050401d61124800d0f000799006500c000b0010b000c050611808601c6070011b0f50003844048441480c2c42c8043c000035100a0950034403a10270b1080c10300040c8514041003e042003640d03c103003a1a288050250401c041e06101050314000454000004118104031411500d008078143e510700d082d5920140840c40c0112030800c100c0c0c0c844e8440b0300d06002155030340240e601034a00303c50f0100f080c494503200a011994020b0002d011580070072000c0020580354590f06481c00401c0ca40719a448a052400a0400d803055024088904440c0400401e15a055103e5410307075130310420719254038144034290080b9480f030b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 527587985 1250 527586735 527586767
    0x7031a01020d14040306090501060f150e04020d090c0e070e04091e02031c05070210020a15021b060a0c0207080d210e0607030f0b0402181002010b06161101 68
    0xd59002c0324843c05606815a40e0b003080752040c3c54a070305c1e0f64075181540c0c07800c50116000e030746a000500400c1c214034003207009440e40003e00b05074440c004c1401850b81d90240d000f913001d164005552414003480b904040c0c289070300414050040c61b40c42e80c2505281c20115404000914040c40050062801e0701490380f4880e0804101382c1c0210f00503500c10101448440100e07810b1040880c280310811003042460708100c00c80d10b4060f1246030900601415500704900705c4115088034801a0010b2040504401d0350b20301c040006803600051916a6040c001042d0008400d12401c020455402c8441e00318210004441d401d4610443d80c8003204c0340e48005000c402404100b001e103410103c020300c2910041c200e492080e0200c0c1495602c200ca42c00e00d50309648410010b03440e15118003c080d140e00401c8000360043d5401c600d41503212401c10f5200144030745807071292000c2002d03112640c0c400d401c650a8010024030300341d81d819122055003440216110112404040384444010075030040c05410002064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 527589235 1250 527587985 527587993
    0xf061b06011211100507050d020a0c0501032703030f0911041802090103120203270301060f06051803100533092d0106020d02070b130b03070e06070b07031a0102 70
    0x740d080003d1840e440c0e1031201080001c0c801c0c1004100f042000711100823070b0740c02501c006561828220080072003500001c0c14581070060300403020382c2c44030340c81c0c40c019002c0c8000400f01105240450140280c00c08030301013a81001150001d01c0404c02c07041c480010300701c4081200222a08000c0c1c240f104840000e54000790740740040020a201d42a8200d4110403881038a24011000009803c501e5407003030030303144e1620400c540002d10f0600740b00b414080c1c210034610359060391400c14000c20720720078017210f4030500c4c0049080d550107407401c20035000d0604080d14184000e00e01900044110b4509035204000c0001e83c0071241a40d8220130702802042d880940b10001d9980d480c00194038a4a41c2200e4401220864001001000075221700501074181ca6000d041c8c08200341d007000b8076018482c0c0107038041440400184000c602e058458604450301032207199200da442c0c0100703460754280d140c0440d4101e030000030340a040104841c00d080c0310b048281c504210440324210140120341e0003601b0340d409644 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 527590485 1250 527589235 527589263
    0x6060409050c06030c130e010e060d050d180e1f0e0402130b03030d1a280303180b0a0c03030c020a0c05041125170a0203040608060f061b060112 63
    0x5101d802198480c40c2e0b070503514900300800a181b5010111544400880e850403001482035101d8050410f030015012203492070050003070340704ca90b1035018041800c2c0501032450151601001d1448031039006203030354014043c82d840d02440907904640212908103060030a4000800c21050045549020780d802401106a80d182d40e0b41d814024200c00504d181c1c103200034404884140414042d03401a2400c8443e0010005003040600503644603030504450200c51103800505c4945075078030101c044075090303e8614001c038242e00c03c503101e01040e90004884041c00207a0354034119001486591114420380d410007005442d0941243c4428012800805c0448032400800061506401800443c005011650324000520720703002d84880708030030b58801c80d0905051220522080d00400c08200510464180c50101c2007d40291244620301505041c0f0104101142131615000308682d41c1c1d850141000b545c55940f0041c82d0200000d03503051082c1d038454500040f400f0000c0c89142c03c482d0b03512100c4210440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 527591735 1250 527590485 527590489
    0xc09040902040e2d0316080c01051e011409060f190b03041b0506071506090f060f050a030203030d050405010b0607050a0b0703150909050a0803190c080606070b06180108010c0206060409050c 83
    0x746d03506000d032020b480600081d41c4280003071044900481000c0c16004105940e48541000c010b0141d01170140751048940c815155102c03001c40301c1d0703c4201200c3c240c04000c654000220341e400c080d208044072150803500451030001020055000343c0c0681c801225070005600c00403000035080c00341642226041c031074000022003003080c1d411010b8145101140382c85c0c403003180078100d62001c0320320107000e43c03141c104102d12110a14298090503003903901c2e51405041d0b80210765680700310051031014582c1c0300005002d004007940070000202c0300801c0265a0580d5003401e40d40c5644601c0180c03908258503010580c0c09000b88100c21070581c5407420361030702d280390842c800020454450190b4881c01107905040010f4402c2005620038000300c10b041003080a00050041203d000007400400c2c0141e80040c481c040e41c0700310640760070580c48219803029035210004103071b0200100311800b898075020170010a103180103420410060a043c1d00b00c030700d0b42d501c0800b00415107240c1000540035403c00700707940c5130038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 527592985 1250 527591735 527591767
    0xe090705012106090c0f030b0609030a15060305030a05070506090606030607050a02070801020d060e0c0301060c11010e03060f01091a060a1b0f030e0109060305040b0c09040902040e2d03 81
    0xc0341c000b0000040c81c5541c0d803440029100350858507400140c110710140b1049030148a041c26501c010b0711100c1c01c008071000030941c2c070b00d030003040900001042c0c03041c03218480c6580c100c800a150310030140e81e215402c840c0c0c058604e40cc20202103800303014900005401c041d00080d198441c0800a0082c95261108032069899501050482046001d90074020603006800d000130300d01806030400010b060362625030603407c00b00d409081c001009a08200400c04554403400340352044d5044007030400d92214440050700c01c00801e0340299018081d034402c1220030b0040035001412a2070144060003030001d80c0b540d00400d0715001c114070360301181c14000341c00d07141c0c42400410222400f48078045514803240d103808002c01402001280000d6141c05c0c2480c40e07583c00341a810003000c0c03900f814001c600381a900c6a200c540014490345090001090490740c170390b640c1c0c1207610b665130042c004110950070401c03402d4540c1c03201003035454401c060481c1481c44842c044c0d00c020f0351041110240d42001d101248030204 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 527594235 1250 527592985 527593037
    0x140f07050c0a0c260705040f020412030c060b01030603051e011e05340809010209041503020a14101b080a02030a02060601050c0c04110c0607090e09070501 68
    0x810a06001165a40c10204403102c20320380100c04600d1114038160201c0c0009280c07807000c45a0401c06214200003003000101081910000c03035001c030350100d8540f031401c0240540d0344102d04201e00c3e40350510505400210105071140280c80903c41e07000140015020344100d448010710640c0700b800d64444010203481e161110310780a1001160030a0354862646001d042030340703080b01c211359402c00e1111115401c290b81619180f041b07243d0480c8420a80080c03002e010700b905a0003400300510019420a000b90f04444041900404c1040360303601921000d184450f50340401c90040c0b28407200410744034081c10046851b0300300140000d5403900d00c0b1004480900c448040715107464884100d160000f50000c01070145003103640d00440d21035003a040020301d80200940b41c0c03410f101e82004401119a40440c1b1001c900c0e030103407000b140c00405c22804641620070001c0c8800180261400c4c400030940c48220503007103a01503080c0091a0721201099515a04248a40c901284080340948480d000d480c21601d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 527595485 1250 527594235 527594237
    0x5010b0405010b18040f0204150207050102011b030518120406091a071502070f151506140f090604090615110c09040203030702100f0f020604050618160609060306050301140f07 77
    0x110b20360740920100913a000382d0012030420010710b403045460ad1381000702030028902403009003c09107002445803400b0800c4401c403400c258075440001c17203240b21300d907003800c00c0a0503000300c8000529a40b610341303898100d802583c0c0010404400020302c0201c074118002c189010304209841d1120070368400c020701c102e900080c54090b8007801240c02244101c00342c02001c40c0038210264004400914a0341100c114040390441c8d801181018000c81c0c0d4040707140815050070100c4a80c1c1e464581d04180564000c41d61640e500040000f03021501c0708058003c1b00407a0884030102e051142000001e413a040c500c090b9401844e400201062854604216280d42140c0040d041d00e180007800d1300840e041ea4003943d1b050700862650404480c0c1d40380e0014210303500e4072562014010ba410903984003606c40c0000307014aa003060b40300140440e45001800040680020f82c00c6810700b040c0e440d6006800110b07184581000301c0c1c42c09400090a04040c0900541104a440024029074480c04da119903110068684c138 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 527596735 1250 527595485 527595491
    0x7090f080d0e01180b04140d150b19030c0e010803070503071101120e16140901140616030215011401050702010f0e0d080912010209100c0204090c1205010b0405010b1804 74
    0x80c006444c48007012010f8445280308039500c03410b1545a08007400c00303541c1a4021003400d0a5400440e80d591078480c01d58000c0000880c010300040c0005424501c0b09005011503100c2850010400042c0c50211040341c4070000c8103109a80da9003100ca8880c090560050500d030000c0044a001400c1c1e1f8442400819050511402d034200b03000044044848854040c04542e1000314140c0c034a03102c92904800a04040c1c0c104950841100041031a001040c0305078643c502034003984001c01d2741e0300c0e8140d43c84880e05094812410392942402940d0b06031404445c400c0d910a240042803c8038040d407030005008060b11440c0ca0600342e90b00444400c0b0301c29004504100c81c0b420b030840da5944e908004c01000b402400925203901e004010400780341740190f881703d0a41e1042000349010b86401c0a4101000141c0c100309140410700e0006c20090840700a00a00300420300d4004031300c191b400d4044070900d03809030008210701100c400074001214828000c0e103103e80c2d4280404240f5002180400326000d40281000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 527597985 1250 527596735 527596757
    0x30503190614040f0605010504030f050102040b03070207150f0f05030907090f0e070e06210c0907170601090810020901120507080f0a020a081909120807090f080d0e01 73
    0x41411140303503400c03052816800d48400c02c441d240502402c1604500b048003002028684000a0b0030b5215510000b80122609004a01404400e5040d03c0c014000c00441690341d1401c440000e4550889020742c6010f1800f500580101c244039043c1c01600c10129110403400b103482c01403e40702500001c100072814451030502003079507480c4d801641030192040780d02040c4c518603081060700f820013513000002c85250b010304110465071100c0500d2140380c400c102d40c000d40300307600c00501d080c4407003660302640140b500400e201c031007030b0301c20781c08001c1000c0e294000b841521901c0045890b2042803082042d01e0740300c08038860700000c542e4001c0103507110504080311404a0590040c0680b4400c9407140d012486c20020410040030300d4220540c40880110700f10300d0080c4002c2c01809004c406071858690811000c00f000b040030346603010640c86a00090080e015002c2d01c0c03001094174404407081d600194042d803000900503411446082907c04c0c0b5400b600700c49400c3c582c1154075030705204078103040040c41c00203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 527599235 1250 527597985 527598031
    0x80a050d0b0d030224061806010507080c0c181e18150108010e1c03110c011401061805030619020f160c15021504060f020c010207200d030503 62
    0x502d0240b60322075000391150304401c0018030425051244841290301e198420040f182d07407001c508150000740c0c80c000d03200d16100c5000489490041060041120600207695a148000003c0c007820f41c50003220728541914030300f406841107100030303110000e454050340095800d42402c50a4954841c200e068a0796182600c040039030f1410f0000c059100d00c000301540140210a0700b03001d100042800203004201e034045407908450503613058103028040640d0340000c20452042e44040b2070100340010001d012295041d1990301e0198001c2c400c03400442c0210460002040c0f22203104411108020040d000b50350b1404105078085010040c550a0142e0802c1201000e45111000c0e020f403e20081d940d80d48500186881d4041028542007901400c400c8291102d102c1c0d1b0011b03015403080d03915001c0c00141d40b142c3ca0715801814040070b84105503800402e8000107980c0541c06440359902030072105980e02da80302030015008508a54072074206100003002c0d00401c0c020710046070040c00b00d12408a6145000e48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 527600485 1250 527599235 527599249
    0xb040302032203020306091c030b0109170303071d060405041a0909070303020d031401150c170a1b020303040e090a0f08030a0516050306010c0203100903080105120a080a050d0b 77
    0xa80c8010040c03441e9410300a60904100301503101f10300300000c00c1c03014107250903400d1100510b0003000030951a131800e0900c030391040d9a168020102c00700785070340440c100c10043e0f0301c07a0011155580040d007001a41410034034000080b184013007001d0306580c945801c0a040c00090301a02401903040041090070b42c100b074444808043c410b6498501800c611801d520f4000d0420240004440030142400b5080202d00ca00d07181c3d590450f40364a0504888808440040d640b0124114018104140e0700741000c20891150005141100c06941d500000140098a6660b4004c4521020350141c1c4240014010404c103905541e4211840c101240c100e038a842d6a841440e407158042100c02e5040802404110901805003a41018003404022104080484010401c1c00b000349014104050030394542c0a5403000e003d1041180d407000c40911940c0a80d041c06403d10000384103c80c002c403c6000103042c06103000c40e00f580420750184266191016a110883d4960400700010540e40e41d10482500da554445c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 527601735 1250 527600485 527600527
    0x9060509370303081b030f040f020d08040f06090b0f03070c140a020f010c02030c15070503191b08120402121e010b100804020d03050903071403060c04050d0b04030203 73
    0x1207284000603040d480c000307190301400703011315104000c1070380c20042425058094960016640000020582c1d450420416040746c210010b5000b00c03d110b070340f0050280000c001c00c180d4820f50041c03407007180e540c0011200360205100b804601d10040c0102621910b80c9001560810110325044809070901c0e242c412041050031581e034299403001401500b1400c04a421011100f400d0900c4050403c95402080e00e03010710809a038070a800030150348280c203081e24207503815150010100d0ba100d0703c6800c6052951030b20101c072003002c10b484141121100c0c419403002170712a03a06c65a21400d08140c800703112200b20024100f2644400051090b40c200082000503011041d000038045001d0860f0340c01003400c403035100b00b616002d00c4801c08984000c50304185119006581650450a640d009042c00c440c82c2c00707212115503041c09040000034021850b80111600510100c1c16245291107101401c00140328a00c6142d4102c1c400c9069240841e01c17000210340d120b4084e0064030316080181c00e81e021305980d01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 527602985 1250 527601735 527601829
    0x5070602030a0305010e04080a0827010b09060306011a0702060d0f0902120f030a0c081216090b03240d020a0b04170a0f02060d0908190e0109060509 65
    0x204111030b140d5450702400b4010320070000f9069940c01d054503100b900e80b0441034840d040c80040400304940a942c00d14482e14413100b5640c1c848a5040c900031680a0304c200b4141e14891024040031640c24030380411424102c070b56000c2c0e000341d8004503411140c0c9a030000b40040c0c0e4400401d04c40c480c03820a007801b43c0c0710844611100090401114810088644030504d12690306921a25901c43c01c03400010845050581c1410110094070691038190300910407013080b501143e003032601f441181103601c140350305401c55030784624010b152950320810030f07408201c070318101844000e8140e81c204001141e05800d0040701500200d076520441e004030300c0100203a4040b60705d03c0000981048161180760b040850750030021701a09584143d0344422003504c0e43c040c8003138801d00c00081d00c105031380f00c0341d4841c1c540141d012080c662941d084040070b08040c2401030f98800481ca12010440035984501c40318002d4030180c3d19800d0611014000303225866120510b00f0440070543c0d84909032a184d2800c2c02c107140b04c44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 527604235 1250 527602985 527602987
    0x70509010219020603011e05040615080703020705121c14180102090307050f0a1a09090702010c120e0f060903040f060c0c05090604090803070210110c03030a180507060203 75
    0x102400091500464903405102c410821480600503030f5203804903811100107000c40d05408990b000c0d8800c4071100c076440760303600071306c0c0400000d0f2040325101c10484c545100e8840c3c1040f03540e046c000360160710034481d00910fa5000074041c0301d50081c408020b0011a1111050b040ca9181d0001c04ec01c01c8844040344090810440420401c8813080c00348216911a4190300940c00c00b40d941c40440d03940c580602134644203103501d5420150544602075024002d204520021b101001441407040d00e640c420700c062406030301c092001400c0320b4014043c41007400003030394074240103007004414840204030b8015299118010020a1607030400100946d6005011200165030b90754900100c07414111040d40c8040705202d100810a000700c0c0604104c0c20403076409688070a101c0c1c1da4040050002c040410000307040000100610080603070000b40e00081c020301400030000d90301c9240c03041920780501d840443d0700b03a104000248201c00d894100000403151642e20855882c0c041e80d03454280402e9410820050340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 527605485 1250 527604235 527604247
    0x30e04020d0e12120a0903031103070c03090905010e0a0b0105040f03050309040501090e03031305070b0720030303130311010905060f070201060501030c0f0302071112070302090603190f030203120705 87
    0x181070084140c10761000c103503e13180140f8000c040f421400000d1003181e1841d900c11240742454000e4018206040301c01881c0395491506020242020a400343d080e00094030504000c00c0b4482c05104180c141c03032020600b05500c2e0364650b6200d000d0718241545070304004040c04002540b010001081d00a1031240740a95110000030f001d000849038168040e000190501c580712007503000210440703070080710001c407040d490017180c01c003280752864580c0507090801d4001005014818021001441013000c2000048858544002c1642e240809c4d240090b64140d80903401c00001d004500e400303401413600e4000309003400e058030790324101501220072040f116050000c00607000e5080c400c09020700703400d08041120143c4803000415a00111400b4001d0542c002650740c18031091564081d1141c40c01811240315204010380716032200103c0c4000c9024030003035004a00c45207030104200400400d000322407070134510240c5400e00034400491042d4150300040180105802d01e5041c00c6105841d1625019a942 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 527606735 1250 527605485 527605511
    0x3020d0506061201050d0516060905190e060d0c15020a050607020610031205090a1806080604020609040507050c0604050703021005070302150a020d0e0109120801030b13030e04020d 79
    0x25000820051181c40100009183c1c59070640351207041d90f80c00e490684550346a494102d00c3c1041c07103c0740502162251500040c1942c2c055421400d80d80c0c00c2e00d03008190003a200c5418094540b40c001c8a0310302c4800720001c0c03641d04200da9025420760060800d0780920395120411025180b450241400580202001c5020303c82c00b0000317290404064401014549820200e402c2c054401e070200500fa41c91071022050381a00c174070296070100300020446002070b03030380701c00741661070b4410803100c0e0710796060032400034900327030041780c890312907078010f03160340e10b0b009242c01040018000200800709119003444020790341801080041e208911074002440f101c3e04500400028000c0e0701503910421400308103100000343c0c00303c0c5000201c0042107000c442030300d8030804000039011700d5421108951400000241001d8150040010280902c00c1048482c01d030200c00c1311003500902001e4178800b1454081507440440b003200940300b5001c0e140510141d03c5040016042c1c0e4008141500600e40320b5031060524 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 527607985 1250 527606735 527606741
    0x103030908071208090612090601181a060c0a0c030609150207080a030507110d03061701151820091513060305090a0b01030b150d0b0c0a0c1203020d 65
    0x1d4050380e4001c2403a20314001216455410101e002000041c000c1180b828944032042643c1480f04100c5801e1400c3c50648c412980c1d85400744644150248a81019903c0b04640d205015202100d1940701c040c0c03400d64010702800c1d900030400400c16218801038032020070300d081c1c014400745100d1500410210002d04041024034403104140c10007500c10061640011260340856540d008103050114140c1da0301c503401c0c0e4000c800080c4190003401200c0080f1001a4503030720820981e0030701c0b2041140030316910012400c0381e915038440c0c1c41c49000100207105400070320780000c103206039814002c16184501c1d044265420740c86501400c8000c00465401d0180c9082c00c44900460203000301300c1c3c1401010b41d1134000510ba5071060000b803642e0340000c40c2d0168403e1000924003a002100d450309565689402815900201c034412503240707140c0c1007005689410360b0950042500310400340d40d81e880d100d10005980d80108004414007a807580203c001401649515520b1002c9440050710303a03a240e841902a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 527609235 1250 527607985 527607989
    0x27100c05042706080304081006090903020a0f0624050f03061005040b010512160906020706021209010e030d1d0603091002220e1b1c020901051e0301030309 68
    0x280141400240100021001ca07902c1e070084141c0c02041c2410012420002003c1d29008000b0034040001c0c0401e00e1180050004645061103008200850750341c1d913000110b845440380240140c2103c0410800308103010f504082107401241d0008100d00b0f410030381ca2441103000d90160340498003140410080c606244111380310070381074002d480c0b540b0f4000c0388401d080d6010b0107202c2c842d646d25030740396440e640301d2010764502e04dc3c4011082803a05005003041000d0740001c0220f400200a20404908a031000c079140003140c81c641c0040c400c00405810070f00e1290080301c9440d040221144112866030340400c00c605004d203940e19031040c081c0744c45003014590328540140300d00401082003405561180040c4070703040c810640c0300058a80ca01407080c03401c8203107074980744c02598801071000318840303800413244c5000b03c082c010b03816003080c8002810002c60040080c00343c2c00c030b22a94030f00c841c0c441d01034006120030203051400d10715108102d54122050b0b0844122070100c40c1e00840148101a009240b50b00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 527610485 1250 527609235 527609237
    0x180f0d080f15040e010209060f04051512070e040b0918010e0a0f080903070e010e07030f0e06060d080d11180d05060106050a030f050115170601020a0b27100c 69
    0x12a030716001c2142d8610420b005919400f880d81e4681000740c0a81c20342c140c4054010080010b0741d1011f200c1c500c0000d0b5041402078910070b03403035544643d036110301c2682220459480405d03110b13560b0f520560161342000001a41e184c0058941c6500b4507551340e1425054421803114483d030b1080784807405042c1c2102c1c00c407500c410f559403100720b1620224000c03012515005900c04950340d83d034410140800d040607091760007a9454040500041a2502c0ba04e0b9864030034240381d82c0401150030104d07c080d040e140100d821460b580c00071808140720303081006282200038001c100181c82c0c00c281d02d40d4002140c00d0000c0340e406d403030801702d48418015410001100e0004049600f480c1c01d41041e112142c8840c011700c210428440b00041d8403c415020741c0080400c4a00031034104019079541042e0042a486020a9000104828180d810b649064600c040c0640410307402400d01a81607a1042c83c401005060310070503490031401800341804003440e0042c00000714010708031400304680c01000b81e03911042e03104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 527611735 1250 527610485 527610511
    0x60b040c0504050603041a070c2a1809021201150f1d1b0f090f01090f050411070b090d120903020d08130b040503030105010e0303040e040209180f0d08 66
    0x46554400d05640954400b107034001e65a0f1142e2808607600c0101007c050801c890b40801c00c02070a4100c0034a0055a000d00e18002d240101814080d0080101032605041c01c0c070700070414852955078440102c645e4041c44000580308905800060250140d445241410780d16007e110207203030700300c0a03940014801040352410007804c0800d0300906920000916400c03250b2070001039500e14403003a513200c0481256584a690303401782152040690f100040740c40c0120f8101c0c0c00c01d03209510032b00c8a0011034240030074a01095083c1000c101c082c00100d001452204018003880010582d034054150042040d031000302160306081201400003081005100382440c50001c132180802d402080c250740c070031072a142203a06136a9850503800c41200950b805041661440b041100300100000210f05941090b00d6225a207076501081650b02d1049000d8003071581c144502040042c02c0c01303184c254004040034240000d8210f40ba003401d1070901d502c1c0000c06294007200c000c0701e0281e04a542e194101c03840740442 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 527612985 1250 527611735 527611751
    0x12010b04170f0606040507090321090e04050a0210020a0804090c030b01020d0801090903200c01020606060c1b0609030a030c02130e0607080601030e160510020109030804110d0c12060b04 81
    0x910344800001345414052601c9a002440591007505054055a4480c80320031745140c0744c1403040b0104418000c0348011980c10386000c80c540410070039147c0300b44d0b8420300404030303001140c0c05d0042e18001110840207500c1514200d200052800b0042c001a105114001604020444000b416240941d80c0c15055401c581507415080364000b603a82c1c190b81800501203441da01502d8100c1d02510107181c04030003281140b85001c501d260100c1d0816407290240e0072160103458600401003548140810414685d0004600f0b90740381d45002a06c0112400c000d0110f404c0c07084040c080707801c00310350860490000c0c140c0d444540c02c502e48000f0402d0342d180383c035100b00010502c1103086036650070040e11500621040701c0020b0316581c4680c0004601c0440e0320182c400d000d50810041c000346005004a41c404e85200d12a02c844600c1482540205c58040e5140303e50754542da11455049c401d40002e194000070415100008a0304c0f00520b2402002d0b05140d00b0341446003424898116502009998451414480300c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 527614235 1250 527612985 527613013
    0xb0402130b0307090b0c0a050d1404030b060303160b09011413200402041e08030f090d050a020a0320090925051c1506060909020703030212010b0417 65
    0x10420a07651009001581ca071280d2106844031400c40d8400d0500c0c000020b000700744451701040c3e0b0004a44100d00b00c41c10003a58120954050040300103c41007804184010008245460320300c9801c00341c0130b4240c1c0e1501d08000340ca80d510602840003030310020302070403d002c1100824440c80d861840082204411400d0500200183c201c0e001400b0300130000c01080181c8403d640c8002c0304000301d004008554980d500e203680c00300c58824480c40e001c4280d07007001c00554101e0200444041d051103201451034810b1400170400130f04070f1410103a946104c3d1611020050f21011884009140910500060001c03074070720084800400b001400e004040480500a120000181d00300c9021200d0709d4822401a151160201045040c0c3c051a40402c0700e40000081d410f2811441541c54000c0c1040d4070610700070f201000942d4440c1c03184100144070780d5000c02c907003025640644080c0e4401d25000d8a02210766521280d070f0503081e0814002c403840001d0800585103403075460b0b4031210740071020300480450409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 527615485 1250 527614235 527614267
    0x7020303060a0909060212011e050103110d0504051002030a0b1216030308060d020418170a08040308070522080d0c080304061107022d0f03031e09120c03010b0402 71
    0xf007402056601d46420108020168058071240c01c03031407415004540c0c1d04c007041c00721542000017141c261040c4210115981d4841e00400200d204840701c860b191040058440c4003c01000f032068803135004020781480c800a10740010350040c200c000010400311400c1042100c0c00c0d000c01000c1310301c0c0c1c0c42002a10140d42d07041d0640380403a07070941000c00c9030380e5520000c02c0d04284130100c000e50142c54045005600703441004607141050161040500110aa85102d2150f01c5a04c0d44400403c5401d00018006441400402c0e44061549030142c01e001040b9a41c0742480a00c0c2000004c00c11400d105210381c2c41d08202269009040b480c04440c01e070303213582710705003103100151014001079124800c040c144124041114095079014003041c050614528144000343e00c0806144100c0d410f0144101c2c241c40c122151070b003107520003000703149804815241d02e608095060080301800006001c8070030341e503841c054018001881c107400703400c06104e554100b500f11001408550721403807040c0003400003902504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 527616735 1250 527615485 527615489
    0x10e010f11030d022110030f0f0807020904051b0405071d0402041a0403060e03180108040204060510090f09021201051909090c0806070201060602030d1d060f090607020303060a 77
    0x109061140c1c11641402504600c1240401116540000b45102c4004d9908041c0308004550b10742035034a0340c40e0341001c0100a0118480541041044840500401ca2551035030001902c0f0300744e164604003c55000c2550b51104031415195a0842c2e4449150070450289100304000122400c2006290030640a0315480002040125054039804881881e45440c0d044901400d00f0810340c0210300840c03c2c100c2c2d8164854082101c406040c4a00c1d907501f10307000410303200c070a1080c0100d401401900001124140e80041c0241c0e4840d8071290006000d0704c9624520000c50491f03070702c0d000c0030380c00c1c88040329410001c3e51101145c5803040142800c00c800c181038003130565200326035451165100780f5450f8407104117500040f040398541385200082060244021080f1a110000c1d105590b407412000c0c2e00700c400c207219450140c0c00c10484c60400030682da0000d55078224141745440c3c084040514286440d000310340c404a0b0b001c1c02000d008007070608024556210f200d51004614501c2d1110214400c02114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 527617985 1250 527616735 527616737
    0x10210110d02030405012910030f1e0c020c0913030f0c080d0603150b090a0e0a06020c300a080711010203130b0c0406050405060d0e0a030305070e010e010f 68
    0x9885501141000042240c920725050202036481342842d0600368000c1032046480146000c104170308440c14200c000341c041c0c05000040120b007004411001c15409407904645028205648980600ac2c0c041d01000a00c1401805035000810758001c5802915140d180c0e81354030700c6005c212040100c401091209000d003d941858400083c3c040e0403030a54601d001c80d04000e096042c08030758440c0c01c40ca02d51102c03013124001c803101d00d1980c0210f404103045507002c403075054009880300001004264243c100380c1412400c40103e481842d0180c484c03400b280c201c410079916541051100c100254106404c070303060541c05405c408444c055a012501d5144520b481a0382804546000501c15a0143c2c001a914005210003990b030392a0a0300c40310002c00310024102c400c1a002d0021807a072001c01800e50b003e80710b07582c0b1404c2c505403c05d801c0025035003010304e115039007540324106005910401d0104859a600ca078401250905205070f002e00b0a4148010b4181004404030600015a81c4402210452042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 527619235 1250 527617985 527617991
    0x20f070f020d050703061a090f060904020f0418020f0a06053007020607020601140a0504020c101409061b0d05090a021207080105060907050f300a0f0b010210 69
    0x414400b091a0031440103000c0c21501606400100748038240e0052000d080440c4440c04040e84610200b140804054802e0005420300034000350303490600c51000ea0300680010700d190701d4011100000307001d030b545d0041c0520814807000310500850503c50000440001c08032150780641b0b00382040140300340200326200300c4114002e4070758002614007440c4007400c61104800c880040c5403519002e0340e030309400d80c3c51f2401032140000001b424840400a80e220110082c02c1008441c5488100006500b01782104034035400740007440303411060316100e41840b03401400120341c0c1c01d141030901641001001000043c81c00114240303102c445a80400f00c0e541d80310701031000503a0340c4403440d54901d00303000101e009404c80380380040411000000070f111411150050003c0c040d07540d42005015446e00281d5107031001c500e003442500c00306240c510107401d040b500b8548044201c1810a504081905070307032000000542c001c424070224200c507026800194501c1f40051100d10000d40c0002e6580600e5140402c0250b6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 527620485 1250 527619235 527619263
    0x3010e0a02010c080f0d06031101021b090105060c2506110307080d02180d05011d010b09012d150e19090c020c13020c0607171f12031809020f07 63
    0x110b04180c51b411100702d803082002030303164079210400c171b0b4100c03191b0303805449041c01d031004244080d01240345402020345400340591814060242c0d940004401416600a418460b00c00c080d9112125500c1c06001c55029100e80c0341090103880078412020f009050b0f00200581c0000c54509403c581440851246c010b03690345420740c3c0e588100301566022503001c03480c04528001e00c08150040307045070800050390942907440b031042508840080107419040b488000c010042c6040c1c403140b4000c039001103841001c142d039140500943c6040b091b0001c4200502040303481003c1d582c44030200c60640019140b0344041d000701c01e03a0140300b11103031040201c03058503128401d00e070764424803150340d201c5009000004001d010501c1070006e90040c0007030950511541c400100010310030314003029103022040040859482d00805201941e0070305d41040e441c5640b030303400040c10032071001511220780d0103591803544541c2d41c0f600030400d90501c0d6200c81052801030211103101e568040445410662048007050307005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 527621735 1250 527620485 527620507
    0x60504060810080a05010c08090705130504020301140906040c09021206040e1002160210090501080f1b070f060f02130509060a1d070206091501050915031b03010e0a02010c08 76
    0xc600d403c6100365000303440c400c42c100035054004e00b45400040d290f100c240d40c0c0d0721123059030707a02192041c00d5128804284c4140ca100301c0b5030107950800e002500204103000398056004610005079038015403944100108028400148441000b62152200039450080008044000c0e104003500d03441c0b0496844004981c0c015080001c1c14800541100a548509410388101014400800706034091821900c0c20702302e081c41a0340f81d206540058440302c4154482c2104403408507402402108040091014040785940710b5000d004014407800d007441000d119032600c013058400c0e1003940d021490051241c001c0c0d4000300508a01138034802c2c0c440400655801e4000b4034803801c60760140c50064001026148441e10003403100348950600d40171511507444110301c407503490303800301c220030341c00280e0b48018441890302025081c1c120b80383d10004098000c04000003414099581040746800e04408580855400d00303004503070b02c8280e0301d40035290001741600080e2513a02c0700a80241845800601144a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 527622985 1250 527621735 527621761
    0x7120806041407030b240a0c0f0c0e071706090105120102040915061b031202030702210901090e09060f07110f01020405090c0310060e010302070503070f02011103040605040608 77
    0x409251003460301c1c102000040c0052405465060041e0413007001c101d008006c1c0100c03c500c40310034900091a03c001603404864031800200112014520040c04001007001d014000c006041100c06940840c03e1450015046040e1403508041c0d07035007246c040003d03c2d555494a981121000d596481400001104080c0203108580042150340d1500003200b155808801d426000c0d5002606e440300e02480b180c035074092104400704000e00040003132450fa00c0070081070b009150000c21500442e10141c815800d44400c2d10a0042e0b008407080380814403583d5503238001001802000f90b031010011500300044440d8980c40d0082c42550f803a81c281010404880c4034684180d400200002900c03044c2e2040c03030b442c0c0c0c003070360062017283c0c80348100c0004074940080400072680142d1440b450303a01218903043d030603948841d010b40901e06256091041c0030100304240b009002082c0b02d404440381030000380c0f0000d00359007180c000600143c1e1041c0300900407240c01904a40c10b492a500384000281c0d9824800700c64 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 527624235 1250 527622985 527623001
    0xd0e010e0a051807170921090603070e031605010203090613050a0e090c120c01030c0e0d0506040210020105040b0a0902030a02150309070b0903030901030f0e01050c1902030712080604 80
    0xb06003105146540101002000b80c060a2160366441c0602d0070002070041540080d06c2c000b00076004980c00e045c0260020008080c00d2036034840302818001104c001551035041110208081640748650890500e0240501d840e6809083ca01901d403a08040001f941c9019502ea0b46024100004090170003e81c8449404001d08004041c646480c1e03c030801d21000a80907188803c6a00c01d034030800e4a03c0c50310104038086005004000c00680b0b000e00011006400e87d1419034050140c2100707080d000c0d46920601101140c001c6008103513508041c41444410700300c104a800840e49485c091100203440b07603100e40c0d000075401e80b0104110295000203424038196000003503020800034103007074140030703410080e42c802c18055041e9200a56606c198014038031500f1540350f0b2540081040002941c041d074002810100c88210000302d01c418103200b5800c6a41c15240003c483c00089030ae00400340380d50f0001c2c0d0001c2424400785045c885141d03940301503008005a40c90506c038410000966944540e808560 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 527625485 1250 527624235 527624239
    0x403150b0a080a0c091a04090c181e0506010e0d0c09140a0c0e1f050d060303020606131503030f050d090b16030603080f070215070606050a080d0e010e0a05 68
    0x15120341d0b9180d05658910001c0d40c1101c0300d410100d00000c98000314800d8422103400b40d805105500901c0040000810340380404442d40c1c00c031140c01003001c504040e143e44001043d4400090200d603900d41061350340ba4050301c1000c81030300b044100155070343d104110502c4480d0540310307081d8090b502c2c40c1030401c00c48203030415650289480c05003e020880303c1e81241c00703000c00c2c00040000041d03000003141c0498624400a07045004110030701c0081060b801d454844450500d4258201071a01e60004140c1d1001e174030030b600503032107203003444528988100194402810401c04104801c12103c10100c1c040342444007600f840042034100d0001030050b0104d81002e900b241040204011034500302605050546260320030ba0740c01300c8240c5445001e4172507001503981001d411806c0200140081d04294040c4c40100d070450904030000f007600340c040005e8400f20b846410040b52803400d240600680a07041d0780819810360007440c2864400741c0180745511070b0002840d00d81c0c0000d09610101c0c05100b0543c0c0055 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 527626735 1250 527625485 527625499
    0x7120510151116031502031e0603120309010c02010b09091002090105040332030703020303041101170a050a1a06120a060b1303050105060105030402031e100f23010b0403150b 76
    0x45415400750f4880001e50f40705a0402117440e40755441c0d1001ca000c00c8921000c140451541c01e445c0318a6440d12590107000102120000c01401030a00b000e40c00a0300c80280340e039142c0d40525a066020701401c06003030710039030300d800c00c03413600709880c1e41d40e200207074001c0c1c0c00303a640002e003c00d681e4400c0e0125006542c1050390b0f601d0302c0b81040c03800041d800c0016075010124160303102c00d01e01040080100c039081d0703801d50300a40c1562a0ba860380851008400c4c00c541c14031422040d0b030302500c3c100841c02445124191000541481c10b1101241034481d20400c10002240c1461100e5413070fa01c1da0162205004c01c150080e10035510840b00c600240606d42100c0ba03c5c00010a40030907022500010b030090300d104000030b002c0358039003200546044c001075400961540252440d4006807040d500d00c00d0014000c902112654175148440c0401c0300c5100d419050000e0b16004101c156a03560702c4481d082101d0300f000f800c0300d5071401400200b1406140401000d0840c000103000a400c1650040c40d030f1102c00515003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 527627985 1250 527626735 527626753
    0x602030415020a0f02100b01051c090218040501051e01090c0306030c0b09040605181602030702100914010207080316020301020f13061b080406201203071205101511 72
    0x1d403041d002e04d00b107200144100b0b000da03803980d1954001c3d40400401a10b0b81414640b112248400c0c400000c030158800c82d55aa403c0c40c0541d42c1ca8040d501d118207082e8a6607000d0400e4144282910001010001060081d44d48040c48141e00d055540c1100c2511740c0004c1d001d605054110017a014546c0b01822000391500701080341c7c0d400c0e400400d4900400c4800700849581d0701c0911014000301d011382c450140100c80082d900440704010421040d140344152440d00101c0c0e4006240156180d00880c00620600c400344100842c610900001c803009000614156242030706040c3d90b80b1030904103440340f01c40f03040c0710001c540302501035500013036681492645480a400741d0b102200058070845001550b0000c04880c1c2011007070040301a036801000341da04c2d190038005d05403408101c041004a40030684075070340c1c040b02d04c248140301c02c1000c6540c40c01d0760780c106580000d2850141803c0c03580c4052401003070108100d00849502c04030b4071102d00542c5030440c0790b0b2090b03e02c840c03205c80d844000d008002c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 527629235 1250 527627985 527627987
    0x10061e0c020d051005150d171e070f0c06080f06040c020708010608012406090e0c0d0212162c0d0c0e0601021524150d020c01180f0602030415020a 64
    0x451040c901440d210b000d0005d500d003001006807440300058603d0701808c4440300b82c1a090030080c080c00c82a1103900349000d07008400c04030740b40d100300c2e02941c1d091401000d40e010000c0d06007090340149010310300300d1500e04100131a107004d000050141442140d44680049403d0300a21031784004003505c6008000b030741c2e600c0740b0050291481015400301648071920303140b0090001d40010050314525614088910f040c803284007880070b8054007015810f9402d115a8540b80c04138001403280f42c4403040d00c0311840c00e003e6071014911010403d400203014510f410f444680d81d041c044031080c01b40c003507805020001d062010562034521500c02412850000c4000724035044c0341e141c4d05014020a03422280c0c0d01041504007910ba40e0300b60b90031500404003c40e120750074004200f032003844500c010010582a000500d1400b001d80c80304080324009900072998070711018080c41040103500115000c081c1c0221240e4803094540e8181d90000c01075030307012002c41c051040b50100414a40d403009021582d8480d6100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 527630485 1250 527629235 527629241
    0x105040b1902120f0301030b06030d050d11160602070b0f150d150e07380901020f100c030513021f02010608010606091716050d14030f0310061e0c020d0510 68
    0x1c15607859031003d000c11a2420300083d00f14bc04036a0b5941c01d418100031086000140c1484030150304158000d002c000e080800070b0007035518540c49102c005a440005280090444800402c0e05007910300f04d0f410011001d82c5085120000c000884d0760491001403403070400c503540d0b081100c0110035440d015800d001a50300240c40340a54010418409088103440f1044010b045c02f810b0505055400e010b03454001c9000c40c0107080f104805005480440501380c10043c501040c001d01e0700901c41c3c41d8002d0300da0380c2ea09841110303008070503048992090703503040c0c0206103e0485850811500d1a0148900c0021072007035005001a040050003030000c1c1c0d540e000e0041c40010355000720051056402005203891400164210f602072003246034001d07041c9044208045022888000e40d2480c24502c00c00b00e6908042c00280110707001a4001c41d200e041118101c406d41c44140c00240510040030321101043c3c01c1e05d00c05002c2e4202e40c0c6070100c07102ca0503101141ca40c2c41c000200030b1040c494101c03019035041d1550 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 527631735 1250 527630485 527630489
    0x10530061507080a030902061c020a0311041d040218240d11221d07120503091323060f0103060537080c09060105040b1902120f0301 58
    0x45801d000150709a48a0400c0c1c030800200a045420400200c102c2038000d41002085a00090890303081001100c06011103501c0800101c000790790024000441d180c05d4403820652600b03809100d41001d06101c035000449081400b03020081c88944009402c554a07448030100803038211554040905000328400c1903040303c8a402040200e540d05006400e0400d660041c078455000942d140034039284400340802d10008091140c42845100281c0c0c14440450003680c502d8248500280101040c81d0f86043c20608590010b8500145203e84000416000400e0f0750000c07808850145450300c102d03000310000d08040800e1300c4100642140850046d0030b8007122440340c401665030001c0000300c00d00440817901e050042d03503803001030207000c101c01c6007501e0300c4100c5c9841104a00b1070070480d4030136400041d10039640b101c0ca00758049480c02015051140e0000e401c2002070815905003400c0c40c0824089019103010721000a40130044040c4861080001c210b00305042c04016a0315804200005a03942c024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 527632985 1250 527631735 527631739
    0x1908060a052e030b03070617060a0f060503070203070606030303150b03010602030f0f0903011e0e0c0a0302040e010b0603270d080705130f0603020a0219020f01053006 73
    0x90400007158100741c0761440341205010240e04a0040640520340c0560b80384030030200b09591600e5000d6a910304001d0321010300a151589102c0546d640e81c1800400c000400d400c0c0210041d550400c040006d14229100340e940506115850b661b640408900d14025008064041070900b08000305254241d4400d00302d000e40308124994107a01d400020406120030320416006a04c01c0216400c0162040042e04006c0307c01d00681d458402900c2c006420f4850f1580a05002c036000e0000e501440320520170300c1e079000d00341000390a112582c03000140300c001d0381d03200c0a1b000359203d0040b00300100003944820500b1070000c10b447d80302e05010300d201d45120800340201d060320460036050306d41c00b5000990b001c1402c0441e03450501c2030307441080844040c0c0061a4962a2003400200444c0401444070960050328440d500182c0365441d886009240808000a9100480c4444695070158580060006405a007824000e035035945071201c0781080d001c4415070044014083d24002020300118160328000d10003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 527634235 1250 527632985 527632999
    0x224060405090111091c050111040e070c031d031509060115080103080301050105070c080102070303020d0b01180b1b100c091d0103152c070f0308041a190806 69
    0x602d005403400c031260419456a0328005202080c8549851100e00016805c0d4000c81d40d04e100b030715901c10342520042042d00b00d00d0400030070b003440950401c1c01a0b40e03000f880e0b0b14101d0411041914007900c4502460040301d41400d1a0a808609490400c06214024034500b00e030710881c5800030310179442d0710086c090303810014217401243c1c01c0742d4800c4030180e0699400c61020781c65a440c01c6c00540c3c966010f035508031024001c0142c0050019004c1c07014108440c0070b6200036a0f10280302003e40c003241d42009010341400180070301d0014802490551800780c1e6911840b5a90b240306c901034000c041801d0140041d4148a40452807001d041250454141d07005261241c1c10350b1030300e401c1083c00741d8083e1000c8549646003000100042000f444905140c1403005100080a40c00000150100c040031a01c2c0d4600b4070070441ca00c40101d10030002440280802d0410121150859403206150310491140009120448000c031450542c404119075880101588440e06841541400b0300064000c88010307100c0c0003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 527635485 1250 527634235 527634241
    0x50618040f0b070f08010e04030915021f020304030e190807080c031002161e08030411090604060632030103050a0507060302130501050d0b040e0c0a080118120224060405 74
    0x4c001c42da0300251591680304c0320f04583c00e02100200c1084c0c0108190100b082d5a4000110000903004000041c0301c150302400a2a0b09509071580385904000b09030180e07031040040101290f0b011580c00c000000072100a1410002901d00c0000c0d201250018002e038013411f400007a220400040b9024078103000da06030b0700900c1565038240300303e02480f41d0079440300444840d01030000e40083e804211b001200c0d406418003901e691a480442d8000715800c443e0401c041201344403900e4071540240e484242290140415030528000030803004404400b0320010b00c2d80c00407603240400740d6140485e00c2581080e0a030301c03503a42e402d0150f030703405160005582e1070040302c03000f0828500c00e0003140c003543c02e040c0e400715405240c0801150350340e20280700e041046564001e10225079440340600c0391b000d2004401414502e503450100312144400d0741c4070282c1d23030b0b00d403228406c3c9a40340100b1010200c0d4104041560751a0340c1030041c0d0500c1c124030040341030090800130f510703004041c01da00e0310300540c410ba90400440c3c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 527636735 1250 527635485 527635487
    0x4060f090b0114090a1502070806070c02011e090603020711030f0303040308150a360605040b06120a09020a0e070302071208040c21080705100c05180103050618040f0b07 74
    0x84203403a034643c5c02980c41882803110400b400320030300c6140c0d068411560003030707034950481707003802d1042e01c41a00003001c040e400c1c01035681c0000c6107055015400d03080559042e0044c0c0150100070f1501c0781d00c05041d0041600b10a1104aa14000783e6482c06130584005c0071400c040c198680e401100d04a010503402c4011500307064800c0840905c650300540001a558140131541e10b1181070004000c8080782440784095424158480d40401c0c00300e80701c004038209080000700303c1580c034080c1045004441c00d0000490290945000c23380001c800708000036100d05c5400481d59614541e040405111201c8041c041450350603401446441c4c000e8601e000701d481d540d2002caa400e01c0a441c040d0280b00034050a0249507a806a43e1002850321010500c10004641c0d42000c160030080c0103a40f180c1005281061480e858041c54514440601e0b090346817141d81103190003400d41440300a8101941d90000079850f03100c0c102c0b0040426131140e0081820714051070071900002001038200d800003101c0000c51082 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 527637985 1250 527636735 527636737
    0x160c0605130b10080d0513170c090c090d11030c03060106050c06280c03330b0405100309050c0d0f020a0608221e03090603060522020904060f090b0114 66
    0x696460740141c881c071760030f0b0360048600d6002203500f4000109001400200011203a852501c1c00745654050003074090f46208018850740024080350121008000349600b0b83e41d561100304101e903100444d2060b070205000401c6c50003100b41c0e0426014810711001195942c0c21401401c0002c040300c0844215584151002002501880b01358540000c40354244488503000d03040013070001d0b498035000900c0c8090040b070701c0c0701081d40710390200d84a032140380251400c541c100042000e04010b0703812030f01e0070b458000441c0075103945580503820159036800d4031003001818010b1070440c0ac0d004003000c42d124840e0402c000c403260015400c07032242007031071000500c2c4c1d0301540301c04d80f141908207100400c041510109400401c0d06900484003540b2522007101050900c4155003a80c6019a481210040c01e01601808854064220a214512144d000002005518031000030040040c1d000360f181c1000c60b020401900302382d0070160729001c654030301045d07640c00c40e405009040030980e15810300080d0100c2100c82 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 527639235 1250 527637985 527637989
    0x41503020f0706050a0e0105070c050c030606030303131a010f0e3103111b01020f0601080a080c0f01290f3303010303020a02100302030906160c0605130b10 68
    0x1490100b40202c070b0115900d94441035200e110180d020612a4401c410036084410842c0d01d034010032070306040e006c10300804101050840703109038018005030401c43c0000e50b032400028007007a41d02e02d41c1681c0703108005904989016149400404254658440740c0e000e51040391400780c4112440d2550004145040c5e040014501c0b40c002c0c0002c0c44510302c05103021350b58010b2208103900713222402e06404c1e0104020464101c11a03c80f01140d580701c0c0409000a04100c284694180e10742e1212005219070400490040c243c5030744071a8146d51440c01110403070411180300c4d40a0429441c04101031a42c608504001350700198940c0d064076000280000c208070000130314060354001920110000c0d4003c0722143d0a10b5491514020191a800a00b012072071540260001c80040c1c1040081004500b003041c070f10788007003c0909082d411480c11510403581c940004103261290038100d15000e084c240070744001d001d0260401022b10241c1b80c504200240c02c02c03000c2c4112845c5220320000b98a007102d03001c000301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 527640485 1250 527639235 527639257
    0x8060109032006030a09020a1512090618060515030a050c090a110c010b0411070312200f031920070c21050606030c0a03260f04150302 59
    0x11a5a040d41c03160442e289003150300d1003041c110070140551035610040074503c2105010b001090041d040d10611549101320703404a051401401c900d03141483d00046105800c064644002811441c1814401c010f401101000d0410070a0004814203000702a0405031144200311140c1500f0500401896503946d01d40c04050201c3e040b040d0300107200c0c544100c0c50381d0040c0441d14089950b401d01103106510390b00030800040c4c83e030b44d20400c0711094100350240c04800081c400005081031030f25103015007160b5004409800c1c241e1f4440d544800e0406031603502080c1c1c2020035080e40c40341400300110a4550042c0d8100022030708981c90300c48150424082c040640f094a002501410b0502c803c000340f0ba0011030003184c801c2e4030150045100b0440c0142c00451100c1c3c0c611500884169003070450070f1110140400740207400204134640c0e2900c0d0341301d60000b242d510014000070f00e20440c10100c0c0003134400c40300145001c3d000800c20080c090082c0508103031070401c08034070410105008150202c0c49007c1c2c0d001c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 527641735 1250 527640485 527640497
    0x10e07051003091a1003050c06030106080c03060103060819060b103f06031203050408191202030f0106093203010902031002041a03010509180a0b15010f080601 70
    0x866002d00c00c0c0c001d0349041e0b200350700491400c000416134010412084a59840b107100030041003050042c1007140040030705003a51014a55414020b000740030139001070454007014000400700780f1991203684a180181100815114444820221401a0300d807503039080c0e89040c03d00500c1000307440d2486060b030098040f61188030001c8101001492a035200159154550783c0002c020a401d64410720006c0c400e0b441c0c20400103880c2d042d444c1a4207071400100c4c0b80c0c0205480c003802c010009030082d048683d41902c2c41ca0604143c900c0090444002e41c03a80503205409001204ac010701c4001554202d040e1103042e00e0301c2038041c2c5c803006006601702a010703034200c40124445103030a0000342800c14084400b00a400460b450a0a8012a1403c01655008541c103a80040d0402024100b410103900140140807240d00c1d41d450400000c3c00c0d104050400342003180c00c008014105c4004102d0703805050350002e41c0f0580d607d0b00008081c00765007610650345c0402e4120220f495494414070f5010311030a8143c5a01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 527642985 1250 527641735 527641759
    0x30b0d0311120d061a0a0903080327070f0501110705190509072705010c0803060613030501060e0c0a020d0c0203100f0905011d03070825030201050603010e0705 70
    0x1118081e15141544001d4000c0c2d2100b050070045090080a0442214502045051820b00c00410880003902c0080d0f24800a12808030301581c40300c0408101d94000c0c0001c1c0d01c984900320700310301910b180710845150900d8400e4a246112002c14040c0403180000c800c0010103a1b00c000558031080401c002c110a60401c4005102c2c0c1e10341111629200c210300c81c802500c46403640e000c607441c80710640326100428002c842c44201074141d15001e075102c02d4114151090320b894000064034050b1075001c01814101e020002070510348445059415107c0c0c00082d01a1465036424068000c2103980500782d02d83c540c0d800004c5036400200204c44c1c0c4508075500070a02021031880844030034040000072a418042c40b80c0c44000d80045000c0d003229a0014000007414500c0f91802508491000304200e81e22110032181e090710741000b0090b03800c95500510b100b6640c51f0710f80300c00442845030440075034581e0944c0b240c0402b4161305600c0580300c0c06043d0001c2140c9079100c1c0300e142c2d032448948030b050740c000140c07090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 527644235 1250 527642985 527642987
    0xf030112030e090a090c17031c0e0703080c10090f020906120708010c02160e010608041a010905060f030c0f0f0f0409030804051e060a02090310110c010c030b0d03 71
    0x8560102406441c15120151001e0001801c400f404e50300482e00c03035110340ea1407051103c1c449002008103c548101c075402d507484014240c413401680d915030380e100e040d80e44584032500e4607000b1724507000d81007040d504d003aa06d030b2920908036009412580154460360480416004a80c82030f0051a500050043c0001040e98204002d83c0300040c261504044c0c414144c80120008110400281c622100003003120348520038024035000c111540700c1218100500100714a909150110b815120503203084105079035903080c00d1000d6a800258514126030000001458501c1940f0103400b8801c11a1246000172020040503507032100c104065501494803203404a20b450706014a050f00e0802401c0c16180780300d00800070302103d0080c03600b503001c62171120401c820440244000c8022401d40b0b1040014404030032005543e0b03550040805400a03030001d100511a60200038042810000000a102e4101c11024800c0b19400103003030b04d069582410004807209010740503031860000003070a00c007214149a10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 527645485 1250 527644235 527644259
    0x3090e070909090206120a020d0c0212090418290705180424030b0601031805190c090f0f060807050d020409020a0302090f040201021b06030406090c080106090f110f0301 74
    0x22617100400300840b000401003e4010307481003c0c104001078444030580c482394140c4000a10020464000c00044840c41b0228001e40341803880c1505d00240300e20301003c2004160300125000740c4501e00b180413007030040300c00c031100ca42e0148140e401c00c60161a11941950316002e00c0581003070044281c042c0030f001d03044c1039001d500004040300141460540b501c1403c618554150000d13545520030508100d070a58044c000c0e04a40101511248415001a2500e0751100d8152614028100d05c480d4810140420713140103030080d20400c0e50411040d0580310111005000c86105c5524a1782002c000051103000822581d0072104040c1010411100300c1d0308201c000c0c001488226406411600088050b88070010310a115040c00703c000c5403182001d0001900e00642051815041102c415814580d901c4e1740041e03a0304070b5840a800b041e80520341c908401c8411240e0800f051642c40c1441c00034807101240c01510860380c0e900c808200c60510f012600c1058450a58100b42e2600100010480060414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 527646735 1250 527645485 527645501
    0x160903031e05040f030503120f0108030301030605190606021606091401081b0408030310080115060503040507030203120423010f0f090f03060525020c010507020409120302030403090e070909 83
    0x46002c0b441d240d02c1c1e544411060480707810a0358590710104440c50182c1441c0030180e0030081d0110044855031400d52190f580b403005000080c092a15040450388280c400d404080c4040c1c0806000e0009c10784425009588002c90040445031010940b00020094050b0440b0310548103d00c40d03101e2120542c50041d690b0080150044041e4103603240302e000200c4959001e03001901500000d03642c3c9050202c0a07030304200301904600c42d244d00d40b010800c0b103580d820810170102c1d90a030030156102d65440c10400d08046042c0d00c043c0d0140294031880400440b1100204183c801928401d041c04812007019104140e04a800c5c0b070200390001c030441d400354082c054804010319246880c90109841d020b07054148502a40121a425203d20900c888555807546111400c0003840441484216405000755507800c0780d0300c4103050080001d10103040d0748444d0007148805420100200c02c919008100400a600480c1c00b980002c1091743c021400c800c15080142c011603555542111090510390400001c016134 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 527647985 1250 527646735 527646737
    0x3100509030301090b0d0c0311090c130303030504081303120f05070c050d08130e041a130305030606090d0b04020306010807060e040f020c0d020a11040c09030b0405011d0105160903031e 81
    0x30301000070015150210b400e000c7c0d44107001c0116201c9e440000d01c550000301500e8448035075003d1086038101c5a03094003d80c126034240c6004a965215400c110000b48140780e844101e00c805088040103001c00d034a4103110001040c0e44410142114040880b81c0d0300514500814044156804016030703d414200010070a000340416403a100825680c01900c0c0c450b54441069140c1c1c00003040148003c0d04a02e40b0440c00b18111245607140414100c2180c840c0d84400500f4414044082121511440107070f030303010503018000580c0349400d42018040e81004580c22403003885018004102c0242c00b00d002411950300c1d4a4425070f22001078204000f901c1c0003006040116401c4c0404051840c00300000340c01c02100d5000703018810b801d801c1082070903281c5140c0c2402142010140285141e0240007c4110b03a002188844c00e6151460018058070500701c22400d1044612449003581c201988900d0080045280d40032404050900c156034007500c600c0301501241d4026001c2c00d101c0280d20300c903204c4180c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 527649235 1250 527647985 527647999
    0x9280f03020f0a0308090c1002100f1104060e0f04090206040b0304061b180608071b0204060f031505012405090f061306030e0f0d0c03141803100509030301090b 70
    0x805007a00c3c80c0c21050701c1c081e0000b0317010405020703ca480070300417005000c0c42543e0780c4914801200000e50b0350364030003140d02000d6603940429104100b4a500001d03c04512071800c40d0f5440e5109401842d14410f200d280e44144007111140c1004d107018800c040740a68003625540c201031501c0c010110a03040107000341d5a494503421915074082c00013034081c0c000036144d200d207458064001c00030b8100c11582d8000c2814082c5103000e0201740c5800a041480f0355864213001d1649100078030124002e41226405662040c0882e00c01000704402c40b0701c2c02186000f00c04040185aaa40000d0410000040b81c124580595010030180042c8200c0045c4804840500450480501400030a080794410070384180d800000740001d104095140c06009c801402c820300905140e01c46858054403a0b5041c0584000d00214410113000c1600542425407582001c0482d90380300c1c02a01c80071074901d28140142c4d882800b42c6a00c00a031006640305540c040c04441d8015402c5030b080c607001e107004040f04403120b17510003c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 527650485 1250 527649235 527649253
    0x2030102040e01080c10021207032303070f030219080a020702130b0a08120d0c143f06040506040b0429061c1d0307030809280f0302 58
    0x1400d00081000348011520b424041d031502041030b09024010f04820b02c2140d64400c182400ca0780011030303801c0b990b8030092035540d45400e442d00740c0d00c081c02414800c0c5510171000907511190b840502441c8180d0540c0c54850032030b41410b170110200d1107210b013118802d91500744000c400c140715801c0c440d0302a071000c07401458150305800280d0350b01d400c0d0310307480146511110041450304064400e0f0f8001c282c044018040078900c41e800c0b222074000c10350f008940360303030303c6044201c650310405d00e0720290b1104100080d5240c0020002a0504000740760141040781b803409030380030407445e414154220214a240090282d00c0b4581008041c02010b0061a030194595140d6280c0395260701c11004602580c6441200d02e400011103102541c800c60b44c0e02d84206800e003c4d150501c0010104042c00c2a4032000014401b0300075141c1040c020300c1108030044c00c0c0300209240d420542c01c03010750303409881518110b070040c40441416008440701c0844c10320702c1d1880c1032440e10010f006004c401151b00e10034010354103201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 527651735 1250 527650485 527650489
    0x708060f01063006030212070302060301140f09040503090102011127011e0e0901050409030c03080a06260f01051e0a0b090405030a0f08160f0e0306090c0a0801060e0c030c040302 78
    0x1070091440d019002da6513002c208110724110b400002c04d8011040a060b21501d1600011928001403190850040300b130b410303a00059440c603c14100c1064000c0031049281043d051082d0360360018444a40903620705103c0f40c200c54103030401ea0b050445241400b140460410646160102258501c1030620030381c0c100c80e04e0003414103105202c0c1d41985960310046c00001104200e0b00001c1a03000e40d0065141c01525004242d0202c058082150076007800203194071841180b01c0142441e52010203050440c4c0f900c250040059018065610030503c110b507804031014a0580c01c07500b080e98410000f80700f1100e071040300da401e4170f12143c0c01440c10800040c00b01480001c18180b075400c44044419400008511100341d40201824091401c1032030403540300c0c94900c0110064003509030b408000e005003441c5140000d80325500c1800b1440020f000c0d00d8250801200c0207503524a545011846010020701c0491003440c14400c00086032110345c4048030345c1d11814900203040e8805440715050110400005c0056 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 527652985 1250 527651735 527651807
    0x1e010306030b150112060518090a0606090c03050702011e110412081e211305010c0f09050d0f0809011b050c0405070513051e040f06080708060f0106 65
    0x100440300014943c8011071000400c507100e4090700c00681841e111040c03001d07486200b038042042c1903a116071081d40d25014101813502807403100081c0290304100010030940f66a03001507078a904292400d101c6074940d290103a00740c8115201640d2408210010b800071441503410032680c0701c2030400020f14041e2620703d04040300b807a90000f5110000001105902c8110f07485940412418200c0503e060100345940351011340491000301101030005800710707600315501e103800101141c1c0000200049852040090140c11401b540000824540e400009690400840d45491a40e100c00c0c1c00d0510540d550700ca100c250040240c450420641d0a03158a041031001015810140584003d12041c0a503c0401c402d175400100800b007084010b01c0181e120704510055481524000c072a81580d1720000446800e01007040b5460740c0d030050170896094043c02c955070003441550f98103420390b030405842d5242141d41d40402d454142617248601c1c01001242e1040c05c1900c4030000c1f0010303410403959110640214 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 527654235 1250 527652985 527652991
    0xe011d15030702060912160212030a030b10030618180c0f03150605010c0f0203160f150212030f130606080f0c0f01020c061602040c09080d03020403021e010306030b 72
    0x1030380e04004144070400d501001031652003017420f001404190507036081c04c1c05c01d00074403481d80714164124240e18115a0740c3c03d0000c407201000400c03030382c48180c89000103028205040d00c0c180200b14404134049aa8030034002d4900343c0c1c0c4c40401800b80356a110140400905440d4500c0c0e00042c00500d51400050b41c08500c003000b895029104c842042c10b60030b14080c241400c0d00f0f103600c01458404100a641d80207800200c4464104041d803014070355031300201c1d04299000c2e0801c0034030a0110004101c1c441d980d00d0b51001d80703500c3d52041d680e100b9034076400c0c0e965172400f0400b081007240074000651007940300a801c0380c2c02414644100d80c110a41c0c0e681c0f00a4a030300d40c1103001280c000a04daa4034a00040055004000e01212600a020003200020f0b465105058540d07000b150f001401108800390a40400300c41d079800b80c4100070001100d407000704002e040340141000f85c0616140c1140b034a01c240280c030140c0350002c0c04039078000c004403080c8036105801c592441c18140c4500c00000464150441d480c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 527655485 1250 527654235 527654269
    0x7020307091812090609051002010e0f030a3509010b0603070c0201020f1c030b040b030a0605040221190f120e0f03030403050d140d020c160e070e011d 66
    0x41c1c05000c0ca80500407603c200c4a82c01000595042001083e910018100031640300b41d80d480c625150200049014140c10080000c0a1150119050545c04c002008090390005a82d5140701140314a034a0f100881c4c115003c072008040c0e038a104514068a1103040d500121008000180c02d2000d8000c510107810072980400030030181c1d072002d42556010300461046100d400040c0254280091503070700c82020b8074040344101542d07550560b0701030320340b90310041c00340c58014100c0b0840c010518040015100850f4101e02424240740e5030480c0c2c0d84503040140300440020040c0c4401d016050080131940d10065007550105007011a020105015040641c040080c0d55a010400300210045c00b610061411815000340e000700010030200790081903449041e0101e00c1e01c081d4040700038081103030500498182018207440080c40d4207a04400081c105100d1842c801ca4240d00b90b40c1e0801c6640500d4100c034400003080f60300c0c2c2001165882070b03850f0031042620008551400c0e20600100b03011b240c11004c411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 527656735 1250 527655485 527655521
    0x1b070609060b0a1403060c030a1107060c14030405030a1d041d120705191103030a020706030b010c053c2505011403060114030a09020f03011a060702030709 68
    0xa100d03081c1812a03c0c00b804858003500042a0114042540c941d40204a01d41c92400800403542c50310f8180c020048008020403040c0d118022801c060000380480010000800c062003044800c00d24100c05681c441c50304100594105665820240e4000301c680c1124452840b050710404d045a41d644698001800c03a4031b940900720446006c01d038a000354603007038074411090501050000401c00074010450303100d41001000c40303101c0d6240c08040d82c400041d045515000200300404138a030300042003002c0310165503007804150103040054a8640700c9420242c040d400065201c03201303881c41491005812054005100c06000032803e14501c004051203032030301500100c40c5400304200c403101800e003000d4075580c43c0f0780103031400c0b00180440311445003800260b0350100024055038050a0f42e402000d000780c403840d07aa480c0c249480c0b8018620f8407401c82c412a0010f468031014241441a40588101d51201000e40800ca008218003904451001c981c503100354400450098007038001c0e070204540b03540c100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 527657985 1250 527656735 527656751
    0x315091508061003060e0a1202061506030601050318102306151207050702040504030801061101060b04062316020a14063004080a091703031b07060906 66
    0x85901851254070050141d0300030300500c220004001504022250f025600180c014000600c040c1400003048011385404000d42c90145001e8012460901c590b110480307121001e54208204001d900080d02c00701e002032418400140c454548500c030b401c441c0c202d281104c41102c840c803a00425602810a01c00b8040003006010704190003040303200d0b812040464002c905406141d1816108d401800901030310000c0000101d00c1d0240140c04a4130256001b520500503031419003006401441d0a220b01400581038000e00340090300c040c400c030b00c00e07510011101803030b00c1e1810f1400c031030310710090004003254150742044034a4400c1040050030310650501d40c3c01200f01c0a40104440818030341d0121840701044001803400e55640000c903907941916a0741e03050f88145584000e40f03402d0038140d507900c503d0606008d200a1104c00b9028062601c42651081d001c583c4402d4a50000003039030b17140d00803e500500208100d01503c1c81c9020701840d044041500300500c54488105880415006851040c0e640042c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 527659235 1250 527657985 527658011
    0xe0a03050d1704120e061e042d030b070203120f0601030e0a050a030302070804151d0105120f0604020c0718060909020303070f210e030106151b03031509 67
    0x251002031940b409042049203442d485403000c51450790040010041c2281e01e48006542e01025204000040b60940340240f840c070081001582c0503020340448010746041c0003180407400107610890b0741e038020714148401c1c9503643e403c6d100c120190055044d070006100c004043c04000d80e905100c2c0403201504111802c0480024040700c40b001c041005981060072a0700108400182110060798075240040e92911542454400c0b40125002030084d201914041d1400aa01501d951418101044000f00000c40100155403510038040d50386118000c00002030080e001c0c40b441290310140240015241800600805081c2103194212403c0c2911091140221580502c20400a8841c120081002d088550002a50781c05075643c0100300098804541c42040405200c264070049510041481010140d901500b074000c3c0076055402796181c0500043d00110802c54100400202e80399420442000403004540304000c01d0280d00f4192902800c0c0750110050b40e030344000700018880010320790710483c1d0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 527660485 1250 527659235 527659247
    0x191404270b060f240c03040504060305060f15031b1309050706110a0308280608101404020a0506030432010e010e06010b0a0905030d080906070504061704030e0a03050d 73
    0x1140500a0041c280d02510501e480d0400c0f5100c2d24011504c20f84030341800818520f14881c0703402071038100e801c000002040020008205000d40700d02c4c545c1032402c0e83c0d22403a6401d41e0f503189207065856031120380709007241000c803105541081d030007504a050b94903000d9489c1041d260002c800303c1d807070f80c8100802c000c919480070f5010040102003010b01240c643d1614020000700313010f4a050b4030019071020600d00a00c84460710702c05891820f405000280d0b80d01c0c911500d41c00120160084942080ca103884400c5081c0001ca10581d07000340101c505078144000c0c007400f90170042c4104c0b0420041c0d0342800407000040303840000280e549a840c4802e07100080c80c80c0c03e40b85c55450400441e0304000d8044083c0c8404140e031030558443c0350f4855240d6959070030441d202d1039654045a014002c0720b4012504941c48124103124169180840b005602c074084211050f00c103a01c00e010010704ac2c0c6003240840c060700c0d04000c1d0028000e00e0a104420003040c00189121020381c4201c42a9209012111605070010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 527661735 1250 527660485 527660509
    0x40c050108070309020f101215080712051902010c0c320d020f01091a0c1c021b060c0609060708131e05120d0b191404270b06 55
    0x458103001083e1130742e000c214484a400c0751340d4030a0000d000d24112607031140480507400154500d040c05041c0c03a4021070403940900c1c1c0130b65501c1d805103c80103e0400c20004400351010750103001803180001d074402041c8055070540301241000501586c11002c0f81084c5001c030003414140e18200c60f002008035080e0006100009606101030003000030342c1042e41c450b400c0e112019015070340c0783d581408031070040718158401d1b0080381e07245201001c1c400c3c1d07104448001d400d901c0c02500440d41e1070820040c0306001ba070303103c0b2146001a401003484c2290285620450009020003800c0c05082010b010350050400c3da0898420b0708035400302d4200032034581d2161101da00900702c0032006d801102103480300b00351361400200051510300543c900c03504001e8104060202e41e1640200180c4500c0f4400b4014041e1000402d4207205902d1240c020616202601c082c5003100c1c1d040486005030309048041c00040c4c0020f400c40050072a071702a1a01444025060540486101d000d0301d400381d1410008208200c80300d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 527662985 1250 527661735 527661737
    0x3210105040e06040209060616110a090204030816050717010c081807271b0201051005060304021003110f0405030f010e0a031d0a180515030d11010b040203040c05010807 74
    0x20903160b0940420200e0495049134054400c07000c15544c1c900811031a110309408008130100c0e040744403090144104c427040700010f049070042c020036514000c2d9403d078015800054144d200810000d01c80028004041a143e8403503c20755a1a40c0d8a0360614000301000c00080e8070380e5100d4511341d100c15030100303105912011a0600081c80c020058040381c0d94070f81800395070610361011440e915808200a40e022100c116500300b88454000310140391801e00320b800d00c40c005503003004045040c8029071001130080d901e015001c5401c2d995150200320b02d800302041d401007419551243c0b401500d950000809600c92600c64203175482e80360205152411883c81050300301c81e4900405a041c0401c041010408a6090301c0d100d5600810481c4944a00800074156940035560701d0f4005501240901c544041006400007084903aa81c111400c125081c803500c0c090303051b0004003460144601801800f0341030b0600380c000141e00d41c41d07103000c18100d0f442a2030035142808141c80c100b04941c1d1000c1056840051 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 527664235 1250 527662985 527662991
    0x3012907150b0a0312030b011403090109050f011b0e0d050f0c0a0e010b09010c1a1905070f020c130b0a08010e07060c1e1109040b01030512040b0d0509030c0321010504 73
    0x41d40c1c0750b103c030003401e0008117400c05441d41c0400c0c0d6076a208090724881c2c0c100c0804100e07540c0c180164200c6c0200022001281c1500070850310244090040c81350900c010211009089100c110b09001c580f0700c006410020341c440026443d10000c150200540900c0034240c10040914601140801c01c00c03401940c01404001620307001801038110072810748072001001c0c2400c075010710103803500500c000c652520784070250404004020303442c00f030380c404440c6c000d00c04601000680c5807003074104e03190103400301c100e005a0310207400700016042208000c1020110440002402008800004c9410b1200d41c0300d5000c81e134480303032007114032142445808020400e506046414080d50394651a071201c840710ba807500850310400b6001070110039407549001c2d060050002d90140b41c075180c04401c00c0401e003c1600e60780701305600c011141800710215002d86640000060820120200032006002c0c01040208240002e0100d80c0700e1500400280418a442414610b03441504c0041e01e03e01d000164405841103007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 527665485 1250 527664235 527664239
    0xf25031127251403060402040b07060507030615170402010306080a0803060a0b1306030e15010e0f010b09060d0504021c03050307080702030a0c0b04050a021c111503012907150b0a 78
    0x608031140f04034080300c1c1c2e241d2035104c0e6200700c0003034002e00442c0e000794100c0700c0000d0f003401002003d50045119850545080003a10744489281c0324051500f00010089100c603141001c0030100c0e8418168424070500d00490002d8071b40500904080b01c105044803150404003e0084620b020320100c4041c101c80c140d014240fa050500c40c8400505603c5880c0c149650b4011041030103109100a80c03020904418a00340395079103c1034000f101038102c0d205090100101c0003c07415140d628101c50341c4160050556040003d1140480020180a01308a84c401c1c820168404d0803511301c00261103060003610384a48038600800c000c0d0058100920220454204102c8140000e410522147c246600805048078580c2c2e030b0315020f4907004012030003a60010f0b46181d4980c102403580701c0b018086200381442080ea03c1c44d1424400c1103a80200c01d650001020b00051040000d42c010100c2e5410413000c0d1005440002c1500c91101d900c108030640c1c00004604150907485c0d8940205500ba4000303032a500a224 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 527666735 1250 527665485 527665487
    0x71707050c090a060b03010e061201110d11070203060f06120a150f0f0e03040602010f09350708030f010b1309020a0306090e0f2503112725 61
    0x70341525010340325448100105003040000e51011014005590b5803139602e50312045004d81698003200d8551203110080303158500c0c042c040c042c0c00d2925084145450030310031803c0c03004020341000d803c1000b00c103c0034081200980c0d000c02c4010300030841c0b10018055030500c0400d000166640d0344002006900203a040d9002030a21000090f2200e900140002c2c10030718500c2c00d102a002c1280d0805815040041d581e850704404030041088034031680081186000740144102501d118500180c080007480e90382d0f8021122181134421218540806100c074040c0460342c0c691540c03c400c40641d0b00381c4011040000202c1c40d11303002c030b001d01800f84520382801e10030141075901c01c1050061029481e00406c418010303c1c0030350042005001d0f40c030020301808020400c0507964280c521410707141441181260354003105100c529941c0c140c0d046180c80703501c60035a01e89000090b900d48102e6001303150101c0840040244014094808418800da41c4d458101095516413205100074400e1500103003a079003164003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 527667985 1250 527666735 527666743
    0x3010f0c031119120204090c020c130b01050706110c06010b04031b0e060d021f0c0b0708071e022a100525110a0303120c020a0b0f0a110f07170705 64
    0x3c454a00310300340c0d020049031400607020715840301e0344540c02e00f00e0390211140c0204181d800c40030b096400801c059141d48c5000c0940c4c640b08080d81c007060040106801081c880e030040b942c3c1e860800c80080c0b502101548291a01c9405d1f4480e45080d400070805004024000118a2007445110000c0740418107040002e000340c03102070b00151140c503070510108219118128680307140c0105c01d011340e02c03103184400701400442e1100c1c801c1700c0c81d0728000f000554a50040c3c543c0ca0080b0352940d176241d170b007065088441071413800e000c00706819071080d0000b00b90345100c184d840018076015502144070341c4001d00c0902000f440c5110094091204c00d1000b241c000c6007141000c050204840b41034010088141003540680d10840c1c912a000f0305040008000d26820a00d2001400002c080c2040540c0503603508036100c2e6200f00c4020500b1048401258a829040a580303402801034800004e00703205901070120030360701805064401c8407010540906000c40d20b00581602d0301c00780311040c13610140d551446e4031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 527669235 1250 527667985 527668027
    0x82a060622060b0c100f050906040f080d020f0c0c030604031b0c080f010506010f09030f03080c21060f0f090c0307050c01150e0105190501030c050903010f0c0311 71
    0x212907000200c40700c0721642c0001000740401e000c0300e07941e02000e0910644941d000d0034245000341c00e0403071102c45c1d500c0c10702c0344501c10823a41001d0700c5551100c1e42c40512164560344251028141030240038011a00743c4001c0080030800c1114a984100b0001010700346507444000600c02d030080020000440d401c41c9802e403111250440750903403002d03203161990158440344c001015078410703a801c80869941c1582300368020b074800d807622580c034500280b08481e9029503000060110100b0b100b004006030203034400070b030041d1820303c0c000d007004448944101d03880d4492003014007410891007408007504240425070400d000548030f41c4081c0100c1404039171102d6001e00340c48a4410004001000d161082003900c1c60a0022002808800a01d42d0b07205c0307040c002401030a50b680800800000c00c0d01d030a4500020b4a0602c1040b20600d81c9820b00641c010000444088107106d401c100824860380c0c00e1040061000712441c00150300442c08400800700c1d81c105862548200d41005941207614415081d401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 527670485 1250 527669235 527669269
    0x303131506030b0f010302040b030d0509100e090f1510020c0f06040b040b030114092502120a090e0601170103110a0314030c01050f01050f1507082a0606 67
    0x40030041108003000501c0e40390b0010302402c00c1e050034006090400800f0314100c07030089406008001c484020140c071842c11042d0000400c400308600783c400d04040c1c580241c1e480080c28201c0f540c101040119031a0202107500b0542c0006400c00c0094250307480d1050f40d80003006075171150b51485074520181d40d0b6806100a01d1084034807000c2d846855981c8021074025002c01c4683c0d40d1116560141261180c0080c050701c4944000640d1000c010308105190038420b00840034800c14505010040642581c40341c0d0040046000c8c41514207030204c0a4401400300a10590744d0781c0c00039180c10342c40b80800740040c210a04010850340301004030115004080d054a800c0f44c03e011084201100203200c1103400d9000401d0100180000255002d01201804910380310304028082ca640e08407070b004544000b405000d034001090b00004100b4240550150014030b400c007000ba02d0805540c403000d40316004541304040754260030b900c60040070200c200f4182088004e00c02000d040c141000022110001800c40c81c4c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 527671735 1250 527670485 527670503
    0x6040b1f0e09071707030b07030902010e090603010906050925030c030b0a090507060503070206100506030c0d0e011508070603020403030e0423090606012007030b040c080d0c0c08030313 81
    0x3410801041c40b01d00010a070814420b580c410302c0f0451301d40c45980038030094445500786000a8920b038024090808166270503035a0244c6211000200300f00000c015100c0d0750150750707a49501c00040d1041c803442d40902c0e44c0f00000c0c1055603091401604041c1040f10154035040000ca04000040b040c816075401d59030b0101d030108455403440d132038400400160b44007500d10b2003203800004546402000850040706141d080c0c800d01c0e40d900806403a8106035124442c0c210808100060001d1790040103408480281800810ba01504543d0307a400c0d10b85005c0d094101c0500040e04001001c0100b20070401070405040960405d403441e01c02030425021091658061511906030b80e100215484040348a0283d0030084d622034141822703440e5855004640321404580c0001c00c00120b00240f84041d006c540e000030043c007035207045039100da44d000c8010b08100c400480c495004a0102c500b030000307614820441d910110401c6040c1031240d404070f119880104603800420500c10a0040018105e000540101080c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 527672985 1250 527671735 527671741
    0x1e0519110904020a0c05071e0603051902031f090501060225050d0206090607140c0301020c030d0c05090a140312120610140408070801110a0c0b0a0f090506040b1f0e 72
    0x59500540030603004040340610440429400c0395104000307103070480c10707050082c0f16488027029012103600f6100d04102500306e81411344002c07640d030000c40c0d10030810450b41905400d03e006203202d0003e6034011581141d201c80040c0070455042008a5a0302d03490f1100349805140c905410300f080c089409020b000e080160041c000755102e01d000c075000450090132680c1c0d00c03074007801d00800724428249004224069084503031481c0c68140241e41951103154065480c2c246410b0400b801012a07020100c1440410b025001103030f510401404000d03e0725640c01c44c0302c42124020941480075510030307100008002c0c0002c040c0140b0300018154004800c0c4c6189040d40c1c2400425107101d45000d944034126680014041111007001c61403808586ca40b40080c006448201084002030045c0380c5d2103000201112031010204144138103c6400603400380340003172a0f568408211042d00c465000c141ca165100d80144010400480001039100795030514124984900c10300a40c200c1e0b5280c8202a02c0400322004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 527674235 1250 527672985 527672987
    0x12070b030f060114070516050a0b180a03080f130e151e0603011203021c021507170a05041a070807030b060c0d1e020c0d0f03031e0519110904020a 64
    0x908144e0b9010495815154016440c040341c0e50014a107a1001c04113a0750400105814120300c01016500c1d100e0001d42000c00f441404000e00e030117001301c980c1c0315207002d0300040844e0f1500024014283e20200705030340e43d102030060440c28141c9501c03034100c140003031041000d1010845540c507200003046489032881481d6180e80700740345010344035240d40108004000910300910b41441c6112500c65000e41d0b401105181c1540092038000c548100940c2101d030f50800c0c2c8a2601d001c1c0f9a001005042180307503000081d16400da00301d812540b04102030799507001c0c8428440c0000340e4401c024014001c0784803521703025400800440c0041c200005060302c5880500041e640e60090314101003c0034200d54a1406403039005000a09180d020002c4c4411220030221081c40410f40800c900b601520b4a40221030a9544904004140c18180e0405644907001c1c101c0c05040c0c0401e0b070006104d10710116a608095025844501b038a034141749049207481c902030310251401c0c094031401c0320101d0300180c441040f000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 527675485 1250 527674235 527674247
    0x91c09091107060e0d09091506030905071239090b0a09090609061d06041220010b100e0d021201020909043e040905030903010c030b12070b030f0601 65
    0xc07000f44407a08100a242c2d440500155004080307900b5070303602c00c6450341c600c02c21045501a240c0e0181046da80481802200d00a40140b123440b846a000c039401140e64506000d941c43c462141101c201c0d420400c1901c1c7d14403001c0c886582e849410540070416205a40c001c45c0000b050b01c6803032209030719a0745034403465640b0758940e0010300d2008014000e400082c9010030080141d62811207515151040100c405540d0341c080c2c1c40c006800320000c1c96191100d4941c800c0c0f000a9950400400040411080840b04c42005808030f03500c0d540c0000ca0401c10074003c000085000c3c01908003049181c13014248240e44580034284c40d150160b0b840c440300d15094030300601a00c40c504180384c21a64090502c000c200400340340b0754001030300c24407210000c41104038440b03101ca40400132043c41e100c0e22107900c9051074664080c03140c5501c0703282142c2c0307007001d0600400d007903070000c2c0001400300c2d96031810b0000a08086400503114a041d8000d03013241ca080c00780384080d901010b000000300020180004140e640510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 527676735 1250 527675485 527675497
    0x1051809190501020c01061202130905012a021c02030f0309030702220501080118081315050706060e060d08180a030609120c021c0f020a030605091c090911 68
    0x30007015400c411814814043e41c132980c402d02c800d610b4110000f40d181e1440b00da000103541d00400c1c4e900c1d52580b42ca4060068849042c007522255610154000c0c5200034051072320880e03001c4400b14042c080448006800d2030b001818022420038136840c1000455404001c88000400219a407601c0b80c03603626125186004440d802500a6481240800300c20b4440c00041e4922040d48424841681c942030010300f0703110b100347c19500d03210303007104401d00156001c80a0f24051220f07900a01c50507584842c06100e400f1080d02800210308006150030601440340219400b90048080300c600504201000c580841d01c015405002e040010030300da0510502a201e030141d200d802081c1e000306503103a01381340005004001c81160a02d22011b0607502e618021610003c0054004206e00d21007071220520314048122541d00315101c841c00440940140e641c021000043c5001d4500028646480040d03940781a110206540e465100d6008410302d5552141801c000d445d00d812002c51600001011280180210 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 527677985 1250 527676735 527676763
    0x1060b041202040b012a0507080d050c07080120090d0515090d0c0f0f080705010c0f0e030c01080f1302030312060f0312090402180303180a0b1204110102120c030c0606010801051809 79
    0x2cad181005140d4000d020b440c0400c4c1e0041581c562a64801c0c0b0a4201d500c0400d03104580740c0d01c10403121100210300040d040c403040c040c2000d44c1d0034000b5504c0c2030030404038030781c1d500b48806441c0a004409400b0894030003400e14604040711080307182e488403803900c074529000800c1c89960041e900c0c20025030109030303019594004000cbc03090032200f99001d0845480d1074050000140c1d96403803007a1504e000618201c0c581e4040e1104002e646449501c102005c00c01080690441c4084c034031900140c400300001d00c1c40003c800c01140403400c040d41040003030300319950081d11a82c440300b03003c41203007442000c4130b154035412240180c0e2000d0321500c9104030591040c01c01c6c4d0500000c118403500c0f450b0300ba0540030120f0304903a201c40082d110400d10080d80129a1004401c94400001a00050350340068220403117050040380d04105480441180592210020202c10342021480d1266001e040101075003013a024200341c41d50790b06000105200c00d01e0f104001300c1d980c00c090003040142c40144500c8002d4110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 527679235 1250 527677985 527677993
    0x90d0b091c030509060a1a010806030106080a110a090608060117190f060c031e11041a070605060d1104150b0a03090b0105100c03050c01060b041202040b012a050708 72
    0x1030000a001054112004c00c424000c600c0040c042c0d050038443d100480000680002ca03500f420301c01100c5250000f80240d41566036007802140081e4200034100c3c0d154841d010360034035222444140100c0740400c2d4030003107000f414000c003800700070008260070341910800d14a0304d45400e843c642c3c9178500307082c4485210ba44d4240610700000e20006442c600b130041e0040406204e04000184118100c615180141d440f9420018021707511030101d030007040d03c54282840c240c0c02c0a8031010813110010f602890000402c100045a80c05c100050180036800181211001009141c2e9160104840040c0c1041442160796244111407682640302e10806401a140d0403074407045035100c06001400403480130740c0c48100d02c80001445150240112202c84403503503810762a10040c0c0e07000c0e140317034000c01107a113455520b940000c502401d8020290008001040790f81c2150000e5006100445400081c182d04011180340220441480b800700081c1c038a6080801c1800c9526a04000f403c0968036000a181030003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 527680485 1250 527679235 527679283
    0x605040501121e0201080112020a03050d0305040c0b070206040303050c010f0518070806130611040b031006080705070b190608060a0902040b01090612020307211a06090d0b09 76
    0x809555040114414103c06121079480c11501c14041582c41d002400503024070010300c5101d4200e1361065980784064407003070015890741e4510b0700f4905019a281d0010380d07907a0401082c0040c6180c1d800040c12015006440c114558010070752030302c160f0101500303021001038500010314095020701924000a5000c01c91030030140c0d07480300b032030b03501c1c0540c00b419100b40c1c2c0300070885000c00300d440b84c00b1390380c854040c000c200c4103580d40c00d014140d02e4141c103844040a001c0041d10300100e030021446160420120b01c0d52600f4500090980003024010b081008002d012000c00169255802ca8000403080400c111f0040c0c00141a00034090a8028040500a40c8103000014200e900101d03847c80c0308443c24440d200c003520045071014503030310447c0006141204080220881540215000205031801c4a2101c420690703000d090300c04201852811075890320860807000035161b4a01269400303d8009181c5092303000040c0b8149800040078155882e11000f01d440c4000c104054002c02c882d1200c0806449 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 527681735 1250 527680485 527680499
    0x8160e010e03010e0c0906100c1106160c06020114070518120106030b060a151b110918070501050a0905010809010204030b0412030501060201050609040f0219082d070303050a030605040501 82
    0x2400105a07039006d48912000f26000b45050a9040b110550a917180484030300291180005041703440c08158002504000740c0d6a0300c41181c0f0707100030103800342e6502c880c1c0920341b050003800c540741c40c030510f01458140024004040c2e070206c211032407802e03811400da203201c150400040d01c1490600720f10940d586000c400008101c10449003d20640044854051040da2181c10740c5a0103200820040022004501905450a11507039800350782d00581e105130300c00c2c5080b000301c0d44400701510400e2050700898580c0b50031203010030400d800b500b02841c2060400035000c02c05007100a10707004480c14480c1050006000003000d6040c0c0c1c1c000d54210740c110032107081c281880301045620291100010381008008101c1c0d6005018041c000d1034042c04400840d42c443c1c03200b80c2c40b00204141203031300ca04c10408012050503000040405000910003410344c2143c1d411040485455061122990780c80110900b02c8034880807841b002240c0d00740c20620794032238480c101200100010380041c1d40c86807a001c0040707911 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 527682985 1250 527681735 527681743
    0x10c111201020c0703140601030506061201110a0c0212210724020403020111060f13050a06110306030c0a0315020306130213030201080601031503230a1103060708160e010e03010e 78
    0x261b004040429980000b08181a00c87d8424000540258007450109040d8204102c031121007030038010001441c41842c40c054030a9903c010380200029580c0407030070065107008010038200709803440c0108442105c10010400810b0105a24582000041a04014810420000c1130358480c464284000f080040920400941044c04260300040d9000e581c070322140c10010310035000d058000c0402c030550359142c20204580007442012a124041d180402d40040c5031805885d090805240e11140c882c90590203040c0746c14044400544190a03140c004c00120358000f41c0342001321080704001d6a2560381e680800c5030001411095000e03248001000303400101006c8841c41582e100f644c0300304a54036418011803d4601c07010070100300104440d02000003646110b4040d516001172103400102204040b041c508260034100d041d9100e29060000102d40e00d001e111069201c840c0e41480035060425964044041c840c2200c0c40050007480e01e15a00b4580c050b40d0701d00c4000c10010028056004003060036515 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 527684235 1250 527682985 527682989
    0xe0612040b1b030702030405101707030501030b0c09060304120e060309030706060e04050d0c0c0b0f040306050610050a0305090304050901150228060510030b13120806010c111201020c07 81
    0xa200ca081002c8410150404483c029851507004506250a260410003207404e000f050030f0600c00c28220880c400e0100d5640144104003030f44000860b1361442c104100c1d00c0c04000d24010104a003003200c440c440e42d601c0c0560781c010350801c10513585050441003d0701d1414507807162650142012040024201c0300000414100344200ca00340500c9039950b400b50031120082c4c400800c20b401c20600e11690500c562a1020b02a01459284004680e00d50080e421a800400d1400041d8000641032050003000c0c015190021002e45d800d483d540d161a100503d5070040d80c45904c00c054403034003c9154114104291030103002c00412200035541d5542056100000690081026010703070440700c0c8011482d80381241f4541d4101030340810480003591020006c0c50000e20006c0030100d141c0001c008240d2010829200e02c0c070120349604203c1d16400c001c0207515000c0381403401c12600001b00300303075039030702103080c140c12540302d4424001c01580c5d00005007070061042c40d0f14200c1d071010035021104c43c0c0009070101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 527685485 1250 527684235 527684251
    0xe131503060f020c030f2104080a050715020d2f0f0c0703050d03050601032307200d052502030c04020901030221060f030f0c101412010303030e0604050d0e0612040b 72
    0x1501d00c01401f0010811501118050b003140b81c00e004503207086001d10010041c15120b04208254601c0b03600d000030490700810204a080f039640c0c1301d24150314907004421400402083c41c00d00350421944000c25440c03040080720034129402180000c484101000799102860b40402500c2c00c007542010004d0082c13100b01ca020b13000904200001c0040c0e03103440d02c2105490071441000089a84c0c1c0c500644603000f641400304e1048600803000001088180916580d1100c03982d00d0f2581d5601c10b900f070299904582040d0500b40a51002200040c1c0d07001508101c134000c26200035880f440281c0060b4000d001e001d80920880b030181003118018030060f0706c0c107031241d81d00700d41e18109400b402044c141e682c0310340c5156a07103d80c0907050709110780c40d20b08840b11180b0f9251031300c3d04503280c00c1c0c0d0005a49401a403840c100e00c10b01e00c4010b0081503058000c403c19500301c10001d10152400351180c5a5446004d10300c00305000809600e010303191a000102c0344c0410783c50101080c01d0401d8030701002c002404641c2a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 527686735 1250 527685485 527685517
    0x6061812050a06060b07060612021011120409090501060b13051e120606010912020d0609020604050604030b1b0c0a11010921021503060d1707120e131503060f020c030f 73
    0x41a10000d10120341705040c0c02078074007060030b000c0341c104cd210f901300030103080424400c54006a00f8205c6103001000504042d00c0042407040a030300d8503a003524000c0c3c00c80400801c05010384842e51002c5d04c2d2204c200c0380304584c81c000040c2c00400340c1c40c10001d840d42e2030f0303003245040a42d1060800005186030040c0c0c002c2e41c54107406030f030356110010640c2030010025802141c04003c0070224030960400d074a010700060030a46042d55950000d0f41660060744200c0714031107a00c0c100030f10074501c3d910304400300e00c0030400d45240060101c03140780c445c1700b400ea0041442c4410344615035964031034544000600319103a51038402c003040c3d001039480c41d0240e580891090305031112040400304002c090300e0140c800a41a80c103441259a68030648041c248250700d001c0c04244030307a00c08150000d59100300e207503541d00d48104100f8100305200740e6015000d09440703040c0c00c1c0b031030f0003810700703848104101240d4026000048091440b011a00a8840c40031449500d02c000f2501c540e02034285401440440c4410180b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 527687985 1250 527686735 527686739
    0x807050c060315130b0306040c0608070203090a03061d0f010207110d02180403021005040b1f0f090b0109080607052a030a12020c0a050d0306061812050a06060b070606 73
    0x81c642c40121144035002d005450b10703160324140280b80c00c0100c60302c007402060501d51720012a2400408032410340f540c4010500400245030000103480e008100d61010f10302d4000d20a010882051040c030000380482e59880c0c0143c10b20b90722141d0440c207451400181e4900030102c1c16001d020750442d20090f56174552000180c6100d207000c1d400109003c0c1d0190800106c03001e0300c03680c130081550080c420b600394050000340c01c62221892046e98800c0d4800c1038040d0f054100241e554600548021000c1d500a14a030350612080c417034480141c048451800000c240c840d500c40040781d101d01103034000d1019100340c400340003aa81e0007002030250344900344900146890505c41000380c140400c4c915a07000e420070400100750324840d050300300643c020b071900075180c070110001c0e441c54500361034820b072075641001c0480e0316065810b0007600020162031034031001c2c2450f543c5441902c40b401d4445d11414a102402000800c0014400034081c1da03040403080000c0d0380d07039200151a69001d4070342212098908a00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 527689235 1250 527687985 527687989
    0x40609230f010b0f060307090909050a0309320a0314030c2a1c0516050411120c0702010207030519061103040b24030f010b04150e07050711040203040807050c 69
    0x640c210302c1c3e5008025040110096080c08610f5001070310035420822a0100845c03e20018010340c40381d030388200c0c001c0140d0015814014035800080c0c000300e2442120007c80301c12411050541c2c068401505000f240b85420100000c028411544c0014950680d402c046007440d1f00105c05007040b2520f0005488910b001c40702c202c0341c0d100110303603410500d01134000d41c01d00505244c00042c60b401840040402200000d451303407071810700b46540301804009240000d1010741810300441d180842c503005040e0030070705460850000c61030020540059521301040050941e8820001c444c010360300030083c0c4a1045e030303c0e140f24003e04040c0c20240c4100f8107003080c04503518481400c40c0e100303a070803a4443ca902d0b2502c1400750000d0700081c000d400b01b0062035032000e00c00d80e01807080115581001c0300000701e1954150074402522040d150030311807141800010000030020b480c0507940441c95207030882c0d40e8092031a00d1407851a06c9036095410030302c0401084200321408000b8010507006500b100c402940e4041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 527690485 1250 527689235 527689241
    0xb0705030412080921180a051003020d0f1b020705010801150807020a06020301091d06010b07080a090321230a11030c010f1b0e060a08040609230f01 65
    0x1402442008800e00d0302c00c000c0e1140c0c100b59041000c0005a5100c1041c640c00790b40e1101c5540c6000a88800000720038801d84480511314010010694501d190303d460600040c50241c480442c4005268002883c200c2c610030317a91025a412030001401c01850442a0040d50710443c83c00d9000090710914001042643c0a103020074102e40e4034881e61092120710f0a0112200b80c2c01403c0181503104060b036110014016001850203882030f4140001d0180c8000d40b100c4c102c144408c0020071070b0308128018441958a0400c0707454034fd820002c110b40d215130f214411640384680b54005018044070200f0400b50020700c00d56485032101c1c903612114031440d41013024003600c1605441c125401c40403c8442101c90046621181080440702502d00b00403100c480c0f0b6094400340001c1c000c19594841d0003c0040d05c0038481d1031951105454005508031200d408255507101d0f03507040405104600380050200a15a00707c240c055621030616000d000b40e04060f07980008a10000316140d0081c0a0040300c2918144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 527691735 1250 527690485 527690491
    0xf0203330303030105011b020a14030c1e01030b120609011d0c0d02120106030b0901050403180b03010e0a02040510030e0d020c031507110d0903060c17160e100306030b070503 76
    0x78091031031a460040155a11030004018628003501d4021800141e680d05402d2401407040c0d9001102c0500c4e1034040505044171001500d1040d0254900160020f8040707000314001e079000e080c00210084203400190104060a0500003d80318071410030900c1441908884400789419040031006011044801d844130440445a508885844041c00141c542407449103262070400c1c1c000621aa166212000010784c11629103c0d540e4440c41130000b05a4050300500c00030410304190b028807810503040b0400ea11042c481c161044ea00344d00410418600ca0f4122001802c0003041400340000307090010340600b50b400ca000c01c01c2d02945025035001400400c01590060005000d049664107103a40780c16000c4e0044c18800400003e100c1915105204103d1603c00d2544c5032100e206803441c61800070248c3d01c0036690341040145807070064080194401e25039811403c11890000032421088040b2803403040203100035400002240c901e40f410b60154481c01c241d0380607107601c03105582c0b0a54161022b2200b9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 527692985 1250 527691735 527691739
    0xf02040b0a0e0f2e0e090102040f0e100f06080f06040c0e3f06070302040e04111f051e09030303060607030e060d021206010e130903030f020333 63
    0x100c000905850340b1462590341c400150313020342e5107845403180500b2480141144018954503402818003c0340000c03060b00e030b4041203500c000c0d8a480d0820082c60603840551046000070201c031804960309414101d60700b0054010a54421000d640e2000c006000d081c0070349600505000a1001c50480e08040c041c0d211400c50302d89401e0403028184060004100104032804c4074001000ca081c5420b0800c1188001580d481103d940344020350f00344840c2c140b0310050140018980f04100c1007000c02403103080140c4c03154020034504184104138004c13442e0b4206035020340705401750392005000b0b910f40040240503104183c2c090400400010070041d00070384512a03401e5415070051000a48501c9c0c0131004100c00b6201c0c1c035004000310301d60b401041c500e03081395822050341600411010b491100756286140e102c5000d2a02c040804483ea02007001c000d58101d140002503100c1803244e0500d0f0190304150030030840314074110350307a10b0103086900f007604420343c40440328401e8841102524000c9405840f8050740 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 527694235 1250 527692985 527693009
    0x3120901032315040912020d08091506060901051207080a0c0504030203030706150f06080a0b030604030c150e06160206090d091503060801091103010c14340f02040b0a 73
    0x381030840700b2008008583c0581c001e8441403504c0002d1100410409080c1850300202064500c80001410311040200403e034130303a001d036803c06440c100b141400d0b500500d045e02e80603503c0e20540e0040300d051042250720403c883e1200180b04e4140e9001000901c0b944646c0741c10009603d1005045130036118030312001e5070660090042401068403680700609030f2002c07800e00e10401e61740e2148035103214940e42c80400491184800c01049280b02c0c050108070b140205d000c0c103501d150640e0043c11901c21500050b0901c007185000204a004170b9111b02c20f0080b00c3e404841031440e00031110b00c03801c907040700101c0041c0a9100030501e03094000800c03c02e5840c1d1504c0d90620303203040034100112160380c1200702003056140c45d00003503608402c1c803c034266540101701d038140c06280d1109050940305d807991135104002840c00342c065031050702015150001040388000c0c04030501210700d58030040700b2040c2d4000300424942c81030204070103085407940b0b00b4801c0c1c2e01800b14482c08400c0090075a228411444401c0b9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 527695485 1250 527694235 527694241
    0x203090c2d100507151514100f020c0d0c030c060905090705090f0d0f02090105030606060a0e030f030307080403140313260310051309121b02031209010323 68
    0x81c1400c0a5101d4074020328100d402c0c40d070203445941424220791130399008265a50804071450303410584071409040740c4695a1084280d000100700010781c060031108c20060002c4d58680300c113109024141103050b006003c50403004c854101014412078510084071103403401100064191b000750301d11421120001c06062841d6a41c003410340e1580c0c841002c0641c131a4254181d014103554802030407103024060742480341c02c025648140100110183c21040c0700e40e00441c1005003542d03c0c40201d4507c00f0380c40c0741071511001585c0c0420714240c4142d10012160001100b04010554460030361031185000307980d00f41c042d03420000146c8441c0300580d4000444a000c42d912404035074047c04080c1050702ca00104841c48070030301d41c2111540c10a450b0b082100010180803c12442c180715900200008100b040021482541e10003500c103c1200c40d581c02d1102216802c054141e100803400301c001d4018055883c00410311039000055405212000c0c04079203480345580000102c7d5440c11400c017a503049507481a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 527696735 1250 527695485 527695489
    0x1b0a0e2d0d030207030c06030506120a0c140303250c1a0403080a121b020c03010b300a0b0109060e070c08090f0a0f0e0f16210203090c2d 60
    0x20721a01003641980f08505000001603a203a07003000c02860107550028681c00c0c10310811a8602030042001042c0c4e10001003030000c5a14807038001c040b0342007001c19210451050000c0b9085004826040901e040d0000003918002042203c80301c0c550f10441d44c06a406440b040300080c1c1605000b21031007074580c180814400584500024004842d4a04001100c0140203034441c2c00d0305c803d60220b08006e009800007003d05030301004440d191000c118000e00407402c0e0400030501c040c0281c0501080e1522a40c0c10143d010b002d846041c1e4142c130b400c8156807a0a03c0c03030400030a0320900b07202e2038000344d18212000890203c03440e80380b4020440c641d41c1c91000700054807916469000303050215400111100010f10326034030b401c0c088008088486075145101e15003003e0b040c041c5401454088601d005c3c2d4100184552582401c008601c41170800b0765480d40255081e0840703520551040c21036134030020500003013400010710320340015401c0307540400915804c4200c0c07400d40100b060000c119414071f000480e40e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 527697841 1106 527696735 527696749
    0x2090109020c1002130506040e01050312091c0501060803070c0e06010c02030d03090528060c020c030a031b0506070f0315060f081b0a0e2d 61
    0x48401201826210703083d0000b454086603000610300c0d03c002c41a42030030042c04002d060f55880f541ca44007010b1034034030b00f0b000d902e1180c42400203200c0200000c4044075840d0700c000c0d040c90800c0340b106041065000810a040b0f44a548490011803100010405400d07540d005440002e22107150403820302c036800c405002141040100c91201c40940c400180c142205502464001169110350401904046514500255411080500b56103500344507901c2800390b4050401045200e018401c1641d88042d42414190142c2001c0c42840c0402d000e01c1c03c010f01c1800c0c0d608180c030684076940d1007900700324040300c408021a140c2c00140700015810300c90401440c85502144846504100c03018040581d48000d000401c0003080008510302c20030881c490318049113040203902c0d03c3c0904006007100c51140620350041a040e114403401c1030400d00c1c03d207404101e6010700c110200024080c8154 = true := by decide +kernel

theorem cover : BRFrame.Cov 527517985 527697841 := by
  have h0 := BRFrame.cov_init 527517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 527517985 ≤ n) (h2 : n < 527697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
