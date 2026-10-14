-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:27:49.410016+00:00
-- url     : https://prove2.me/submissions/64d50ac9-928a-40a1-85ed-337d5d713665

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 545143884 ≤ n < 545323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 545145134 1250 545143884 545143909
    0x2102d0e0708031c050106030b010c020d24050a0c0504030210120605060d0905060c2508070807050f1006050108070f0915020f010f050405060105101202040906081623060405 76
    0x44440c2131483c1440c1650864106800c20420035151029030f486c0741e43c20008680e985501144d441c4468501032400c4010910b911740e40e41d40c0e50000c80e10402100a0540050707006a641c07420a00000e44a040221a18003451001a610000e5241e002100721b000b0504a2040b400d040800701d1090780b2a004152243d00851840b0201565814110107001c018440540c003d10404d01003480c11b03400f156072102062508425609031406146210100981201201c00b000d52055510307848400c68100b9503120034800a1205040c01401101d8005c500d0798819482074540586036203004d910340910464440c040c002d40c1e0b0092042c80c0c0404110480c401c4254070548649500818000081105580c2940c001c81c40003402c1904000510001800110303600b415990700b60350b0700200300e00c0117008650b80450000d005101c5c40c40044e0125008490343c010909440c0c682d0211b03403004100d100c0c000424205803140800c03a101030441031050442406050748131250082940741001d0b10b13a00014000c04444 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 545146384 1250 545145134 545145157
    0xf030f0606110d140415090504050c07201807020f07150318050303060d020d060e011a190509060a0f0e010311060307020d030507030e060702102d0e070803 68
    0x48040d4009038000c0080000e440f070f15280c9140907820107640c0e60603a01550280c403a6110304e0f61101488680710f010b1650081000600900103802d000795010341070f9018100541e4002c1401f0050f00020024402d401c41144010f8503003070306900b401809000030701c8003a1802086015046c0a00c2d60103c0411914010303204048903090321441c0d5000150849031810b00c1c4111000e10711421030b0108038048203680d481101901c0650b511861440007404603000d4010041c9801e19013200c240600c2030550100d080c4070401840800c01030b40c0c040c10040031004158070b101c0195a40602801142020500a41c2201001d0718480c0310a44800e014110384285410410441c00201c0c0100705020201322100c0408206481e07a510754140078100945441c030b000c12150900d501c603404111103501c41c3d40701040050044050360898248030720004d440760072031a4107000c22070a1070320300001c8605d460782d0a103045050214071960700d100000c0031000791080e55190405801506000181c07108140024107400044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 545147634 1250 545146384 545146397
    0x60918100e070f06050f0903031c0c0f110c01110c040906020d18030f080402210c0f0a080703020d0c0e0f01090c020c0a120f140d0905030d02030a0f030f0606 69
    0x164007140b402d038890740050302a621448041204603004070440c6d014038200d0002590b17030507074900070a20714030a07a07a80c00d4000680000c5000c141e41036600c840030089966503580701c405103002040f500e020040142c400680c1222034042015801980c110307a040450303a05a034980d069400c00078084565460042c1c3d4400e400150365800d00f0701e03510400c01c1d2000d10800480382082c060310010002002d044500049c81b00900105081d951070444c0c0b228152444c2c8103040507201c414605940740e85950110781e0082100b000d503400782d482e2000300001500c0c40c1c040140f0a1500c0c5400301310010581c0f0a061341c0d044000c070408a0240840c051007407080100d800b80289a51408004070300702c80c00e8000301000c42d002042140c0c80c41d55082192021140381c403069409509076405d0016121400030750043c03011651020307692000d2000701c2c3c00a2401055110702c440710344d880707040c90b03160101c5000c2d140068104010088209004440708407020b60246130000702c1d02c04201101d003c4480c25040304012860 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 545148884 1250 545147634 545147651
    0x9050c12100b030708060f0a0b06040b040303170c0f070f080c06040c080a080d1109120d120203060f01080c12040c0504240b0904020705100b0406051806091810 70
    0x594020814500c030300383c00418403149003181046d03d405000c1c00c440c4c682c541090200d8644100d540144513586401002c0681d200c2d41e07844529040c1d402848101d0105000e01c040441d40c0f4503a54403c0d1140c440b0340c001a150070144e681d803030281c1c0c0c0441c0d8121208003181da4408042440c20317014001e00d0800744018503403803c15080c03082c814071250b0300506450303204400702c07000074905005a6411601c0a034004c60300e001c08040862040c0541401d06030041c800802c580046607001070015155503058450703440010b2041c0d000810392004942458004200c080c10401951107120010f92125800313a2030b0303040000942100ca500c280a80d801d07074243c01036201c20b01c414602445000a80c2440c2c070405040300042c0c42050000d10711343d228140001d4004180e110281c2c44030b8040b07540c0d00c3d0740230042d603040c01d480e020a20000c110081103540503503e401008103440c2020003000c00c4981040480c0e20f000d6450000b00070303a95800a01031007112840a007402d5144108004071401094189400700b40400c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 545150134 1250 545148884 545148913
    0x308030406090b0117100c050705030a020607120603240e06010815070c0201080402010e01050f0a0801150f200c060304062405010509041d0703030c0302010c2109050c12 74
    0xc0301030308005e80e0720b4803107240c0c0900c0c0040029410301180094a01141e404116407003504c89008518001d0141c0c080040c1c02c9801c15804107030a449441e0703c0d117940300d07401081c030100c4080b0303100c500006011082008254001c01155a4003000030b80c682c41010031a070030b0024080d401c02ca4203a2101d00158482d10008140b0a610300308294885401e10300f44112100d2900000c0079180c02400180c14000c0300c2030484240e920420440e000744480a40a80d43c903401c03c080104202d0092040317a115100054141d48200d1052131440d142c085a581c98002c041c00302c07071160410007800811400306115100c1604a95100c010146108034000d600c00035818844400003101ca60100340a040304148a040c1030080d680c00606440d903152098500051a0304900f811843c00c0000b450410100d1180b404008201540f10600c03180e0b841c0b10717500a00a00b0321b08601951000e502e2a00b10f01c0b000c41d050600000700d01251301c0300383c1c40c90098046900303182110007c6111050b054800c481c01d50480e100310500c18 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 545151384 1250 545150134 545150153
    0x71a04030228020103020903010e030301120b011502030913020c0105070801090e0610211b080f01051006050a0201150b030105041401030519210f0e0d05070509060406030803040609 79
    0x8200e48581109101103846840c295102a0b8200a050540c04248001c290b1003d62040700320b03800041c205c9503256114106503051030500e10781107404443d148000300c1c0200d060001031303d140c034071900114280420b130300800012092844003196425400d00c1882c0040c0c800b4051503024003043c2e00d07084c846504110091040d91a250030940982d4005014451070032515000c1504841c03880040d1522850b0420a043d451403c010000e441c807420720b04400e10300f10060044104558000c0e00329034598440c818450b003659021140303200c0d2918810000c02606001c0d40c024460040c0e2440005420302d0a0003003031a074041c0319000380400d250044014000f900b4980300d0012a0f043d8440315164941c5150359180c0d5651000c02c55880c501514031281b41009a0007040b82071010780c0860039410b4150521005001c403000005110000362403201000b2a400c21041c0402c0080d08040540009401d0409102100744080c0126400903074070100000843c404101441c059841101e02103070100c418200181b11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 545152634 1250 545151384 545151403
    0x90c2b0f02070302101109041109010e030a030806010531030215090a0b1b0706171602101d0307081207020106050901120f0b160216050d0308090102071a040302 70
    0x40c144100607100102c0e030000b56000c8201e58809000c200c030f00503540d0340c100078050b800c0543c3d00a410185a4416000190082c000c40282030382c03400203000b86041010303904d0f0204000030300802c0102010814552140006090100a080030310325151071008883c0c440b545408a00703284c68100e00e00c188211700d8014a090781c401e40e00c0441c1403c24000070300143e4103075090700c9a01c01d900310000f00b54048100011001e0440401802030b1855182c1e6600050710b041c00440c0720f680861040380c001403408004030721034080300040742e00a0009803c42c1ca0001d009200c420105550000c4000280404001c10402081940e00c5000140d40344c1e200d200203121025000b03000c0e04156414642d0074041919102c0c005411281c41e08200c900c001d0081c06d1601a400000d040504440c0c80700c0100554403004600340c8080c58080e5088904182005002d00b03241f81d4030740250340d4000001c0902101003441542e9098000384000700042c82c00c5c0c203503a02c5400580c41c1c5450a61190b2440042100381034050088400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 545153884 1250 545152634 545152661
    0x6030a1401230c040501030230010608090706140c01290a0e070206070c03030f05181902130f14070f02100c02030f220e0603010b030307020a05090c2b 66
    0x1c5040254492a184c0103501415040503804940b58003e03d1010102480f08186601c0400356a0040c0200321031000c400d0180801007001722020480038640010b10008440250f40c1c3e440b2101e09003800305000b540040e042c40710543d242c52204045007620b00801d8400d41c060101401182c030b41101303002103020241d10103444002070004000540e0780110701c1d15030203003251820b45052401c0f071800382e009003201101886010b00e02010444991151000d54540c003c2203002c0b42c919810501b48040c20303060841d0001c3d00601c03128850310141d04c40740c20080149500340d6010404410400c04080c8500d0300300da0000c005580311100191254051110304414a40002d060140401c080c102039030701d101360040c040c000b41d00016840e03086580842c150740e040002500e528046a903e0650381c07001d07441130700e13150f1203940380805a10f880c0c13070b00004403681309074050003044441d031a040800c050202d000b0080700c905c54040203415502030300d1100403107400d51100e807031128520b01c8030b120000700d8502c4880c1d0003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 545155134 1250 545153884 545153951
    0x19030605010e0a052b0804060f030b091b0c070509151206040c1e0801020a090f0f0e0a0b060715020414270702010209060d0b09060405010b04030b06030a1401 69
    0xc090380f1852a80d1003c0001781e21881201103590003209881c2d05e800e02c1c00b80400c0307004100440c10941c04400303859440c0031640c00740000d1072054108601e01e0001d03650f20000c3c81002c050010f007100440003030705844645001b80e901e0345544001185c8444403c9654561111011010a106240813010395030301520f494020401031901d0365405030351101c24061803a40301e101e200050700744411103003207801420326107000f55100c1c0f0a05002400d00440b500441a81e002d440703101051030060f90034000225400818481100e4468441c3c0e80000c019175480d094102004011000100c0c80350120f9001d075181e5001c005a0721031410031040741825100c1a502d00c01c03000710310b050801802d454802c0c03884080071803810400c0d803294001680207224205000e80c000c0d801050f52540b00070640e1100c8100b01c0c007664010110b556000810003240e409005440407440c0501007800454820701c0344686c40803024080350b8600c00b01e42c58142040002c4040b1102d40da448407001c07048510081c006506180c848000b20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 545156384 1250 545155134 545155139
    0x60406090612080f16141b010f05180301020301060819050f060906040b0306090318040605060a260109050403020d0201050f060f010c0b040b010509090a0c12060219030605010e0a 78
    0x55441c00d48044000c0c040c400046110130422507000e044a40302984003102c040421003038035105030855a80368040c0017a00610788070441181d0032020f1601c011f481691184040844d00800781d80710f403c4500345d604000495284225952000d00c0114081c2c40c03592186909898150101e084807400101c241990608040a000e00324207501501c40c3c00c501c089441904a035281400f0900903e99103500c01d9061003014103006440101200a1049000e00340c140a0080100c200f8031040e903403248680c40c7c100d2420482c0b5801c60f845054034041c1d441c2e80800000e500505583d00902d214020f800035000590703150103010815404008014840300c00303000078032540c904043c41700b03065440100841d004410110b5202140e82c400c000609a490f4043c0c0108114107050078120350100c4240107a500600000001c501d05903000513000b4200c0d54071190400d407080c14101d0049000700c3d4154100c600c141c0900c03000b0420714a44400e07091805660340c0004960346040001428811002c072614011003818405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 545157634 1250 545156384 545156399
    0x8010321050d110705060703020a030b01030b0a06030e120a09181802090901090501050c07020f011404270903110d030e06011205030f0a03140a051e1911030604060906 73
    0x30b841161201c030800107503040c6418100b4150f032090500c000d095000310010049403503010b902030329075000a40d60030009680404e00550444880412980d4022800305003080214403907001401400c0585007503070154800c0d5100844540c01c1820041d01003002c1d92818030103540f40e080d9024511001a80500100e0540b050000e0b00b43e10400f400380c0600643c05c00580102402d400c01c5240030380c0700008010764608903120340c4281d00a13030400ca01c6003c000b0401511fa601c1500c1c0c20b00070380802101540350900c0d0501101003100d2036010b5a070300080940c81440230141030f2148400c0d16000342c4a04620380c41102c40c960411203a0316030031050603e03214956810401c00180d4905482c1a00010030385120182002444c41c0a04005084070031800580c04680303d605810050480d20b00190280054540550311b0080d80d10403150b411101b24104120105928074100307c2c0d401680c00c0d20100c0c0c00d44c4515030b10000f5101940c0c0360a080700307400018008613081c90310403a001044183c908101c1d0900b032510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 545158884 1250 545157634 545157637
    0xf010e0c032e05060412020a0503030c06150102070302060c0105072a020402030a0f020f1305090c22053703031e051314010314060a050d0309080d0801032105 69
    0x400301100d11022904494103500c1c0b0038000160000600054a80360742e104d04800140c51028100c0c055401c0d0741001610b810008140c1d607000c0c5602020348025a10105982600e088206503541184200080000540c640c00c0060005189400005c211440c0401024186035801d04111216560000380507102e0400751210107903075541144d01503503d0700e8885040028000501142c46070074400a440b044400f412801044000c82c0d4041c40c0020300d680300200400d03080c0440d11184c401c401007091485540311380e8a0410921041c0016840042e02d410100e000c000b80d0026992044203d0702122003005503032000c10401c5448841524422401c5540040030072030308941d072003c0408502c14001d0b00500800956082c408001807985944d665031034202c240b041d148500e940801d10b0b140841c2210002140110320404024103641140c92815085c880941c0b2501030a5082050108011a40340e800740500304440c403040d030300d004287d41181881400b0f41c0004400c80413403c0c9082d0000c01c413503003040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 545160134 1250 545158884 545158921
    0xb0a110c011b061b18080712020405190905030d11070503040911071a0f0708060f0907020a0602070c03030e031c210c03090c0807230f090f010e0c03 65
    0xa9403654000c580d0303e040380143c009821080b04001040e40300c40c000c05d07132044504c101c600c651145810f065581c0e90840340c9520650042c0740703060003d10031510150502e50081a00002c11902e4410781e207400380280000c685041000703e03404d130000543c24907140030034010996034400e140d01c1d151030080c0560f03559940b0300c5103105a4400c01c2c5c4542c0712003d00000d207000d80300301c1c40d0040303036060000c09060807102c55940212594000152804045600705205514040c170a501c090165140780307102d007042008046008201c1000c500c2031121000014590b400a444102c1c4031b00c00381c4450905501c1c0180114003c0440d03280280d00c0303109030700c8401141e002da40c031006849040444d02001d10b440000d900791020382d40d40b0441070805900000c0d255140d40080b400602400b080080c564a6010301070700d411084c4101e00c04d40309050744495544c000ca2041d6146528000c00981d41d0481c2080401c101c8001113982800da03e16100041040c02c2104803100e5010101c43c0c1014950310b000040c0080301c10080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 545161384 1250 545160134 545160167
    0x120a0c020d061b0f020114011d04021c05060603010e01021c20070503090102010b12280b0c040806060103050714070f080c0304031a0408040302010c110a0b0a110c01 72
    0x1800e292092010560000c030451000d01c044420041072900007400300e42d00d15500c4c1c8015860440c0c1580c18000e0608079034140c41c45084142802c10b07100c0c0c0010808403000d8002c0e6400008220394003011450b801c412220280704401030b0207545072641c201400c542c00c00351280580c8c0d004100101104000710380c49001041c040c00d0000754000600301d000814000d03040c090703260101c00a8440240304000024102c400c00980c024446000000e050040074194040c000310070380c0c088000441080b000c0350020680480a036000f00076039819441d000300034102036601c614081800142445544024041560301040c203080510450411110041281518900016001502150407010400b28614556035a40c101c150b880c3c40305150480c6035240d82c0180f0045420802213002912503080c50007601d0310598101408509162640c1c0042d940e00c650240c044074922a090910b040c6039071181e1861000c2c201c400f88841c0c441d41a14006015102000c0d40303c80c455002450358440c0780c1c1c3c02011a921155503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 545162634 1250 545161384 545161399
    0x140a090b010527070c0b070c05060a0e0109060c090317040e0c0a020114070305100501140a05090102070905070e010e030a2a0f120b0709120f0314160203120a0c02 71
    0x1400e40c420078015805543c1040c41400400344181ca81c2d002e40c4140c0028090001111540c40301102a10464184070004206d500300f08009a1b03101d44a51144c000b00f001e20300003003502e40031907407404211240d500b0210081620201d090061220309150344666911001c4010300d09070510240c01942203004251a00c0c51200240810301140700307400c61112a40d0340c12102400341819040980501802c0b90000541d107444000015650b10a00c21140d103d100c2c44681d51030410a504200c5881d0700c000902d038103520a5010005138100e40d840340f10b1042c00c03d039a03000318440c003840c00145a02a03500f8014429482640c11001160311074445000564440d12a14a124001c1144103441c801c590311003103401e980c1d158001241000e81e804400e0340c5100f8020b400c51035075049019a405a50b6029401100000f0483c0c90005002e00f010149000c2c000c0c20508044441960500c0480e4850403510a8410020515400b181030800159580701078030429141412032802e00104100000b410280c400c600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 545163884 1250 545162634 545162659
    0xb160203120c040e0f0702191a090f120310140f131805031c020c06010605070f06050114010908070b1e28230f0a030e03040603140a090b0105 62
    0x741c801c03a0b00802016140411170301d00740d2071558036008211400f50160044030750100811043c840315030344541e030180c81080d20000018440d08220001031050b01a071061404c1d480101004210b000d40045001c40240d54a203000100c80d890210260300031684603c000020700c40b40c0c3c1e94041c00c01c182c07042c203403043e5a40741d00a610080c0648444140c1800d10108883c55109121000c001401d1000c01c84203052100601c9000400032481001d03c0b101284c2c02000c01030080b10302c158014007155005036425407440ca981d8490104488080e401240c8980c112203200c161075800c0b81c02d4070000e04054015003109403030100400b00500c0b645887c90128050444002001c1600720152124010b040424008202c591295424424040c4803007201090580c0b0805008070140000c0091840805c2007040c1080c4841161104030740140601d00207054948046000c040801c002600003411140e5002c1101015012a2208a4400351804050b02d0814a542e004902d4081da11411030700190313004140880d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 545165134 1250 545163884 545163901
    0x303050307021606111510051003020705010c0e09060108010612091a3d230d0308181501030318080607082202010c02090a0e0601030503070b16020312 66
    0xc08540000c100d00208040802c196071701506403400680c0788000c59000b544422200c1021a008484c4c280d081c1c4000b040a108074101a021407400f10700354100035080c58019a5160709499503281d101d400a11910540c0b2601e2411104064102101307080100c090b50415400034200504d860300c0c21000798407281c4080400c074801900a03041102c0808649450504203d40c0075112081070071100800a80049401d0070107501c2c0c1d044a400400d02050321107989056181c0171a480c103c030690071207070300b00300c0c08031031030388441c44080c04861083c4d07a002d255261180302140240070107580354072036500442c5400c50803803101003010f05403a0142000f410626055400d01c20842c800e0b0495000b038010b600520008641042656001c0d2107049028882c44140254025141d01c8400000e4002001070400201600384281c8180e000344d0784039000720703000001d20039462500e91f00380c1c03040301e035a840050b44c01e040c4001280003030340001041d502c40101c3c40304508002d41c1d80c018800c01d41c042520442c04510850f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 545166384 1250 545165134 545165143
    0xb092202090108100b030d020a021306031a0a1a0315180d031a04020a02030315040e0706120c0c02010210050c0d090609150605180a060503062d010f030305030702 71
    0x2168010000e44440d80c40b22002500d820207000741052060402c03542110500e004641c00350308070b20f1a401041d03003169640030000390f5940d88007414505a600c80021010a013101c86142c21291400380040541c1071103010b88003140d80d035112045911500e44c640041c0703950f0118103292007001d460584042911944101040403a005800d60028420ba807008092941c043c5c00c041c0344101c482d006441880343e150140070a0788a100f200b03400503001000002d56081080070308004003000500f000070a40c1d00603c8280c90544150014004183c0c40303191790700101ea0b10701540c40b800b201c03031816543e40c1051303030b0001c0d40d00c00c402c188041c0d00688401c00142c038035642c001680d100e1244040d040c4180003050810030000d01c8a0034065414184d8070b448058400b095006101c21640082c16018400700c8038180414204800f601c0f00050980364074000500b40d504008042c02440400303072151940700030304000e1104881c4801c1c41200148108010015141e505001e002201d4050614070303580d0344c41c0e01c0200e080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 545167634 1250 545166384 545166451
    0x6220207061401080f06161205190f0b0a09060602030a0c050c0d0f05010c0e03030409091e06270503090d0f120207080d0c17070201051308060f07030b09 67
    0x2c00300c550000121000d0004a001c00800700000340c1b0000e0320b400004038084144c80390300c1800b00300295001e0014844603480035030320130400b00141a800740c218221000351250020b200140c1c40d1103540303104461401100303000041820316820441d15140520103516402030619140070312800d611030b0420f102082c404449109402420904110030a1a04042c0300d215004140d48542c07030200040d011600415012103034202c0100152304040c40c00094902400c1d0009007142c0e10089a100050074a5510f041036498031311401010415030b80e803d00c0d0350402200c81c5001107e010f08101807030041800881100c4039060300b603c1100e03110200e070800010898011400400c04081c038200700c4583ca40c04510b40c415503100d201039800e00c4c100c1c075200300d642c500b14400103454102c48883c1d50444000703200090504078810304005092150806210244401d07a51183c401904808104154900303505441070788145542000c1140c0b0108078041014280018002c0c610000541c09050a00070000e40990380c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 545168884 1250 545167634 545167661
    0x9020f0c030a02030d0c050a0804120215161404060c110d02120d0e100206012c0a060501081b090d0606050402210c0f0a1b06090f0203060622020706 65
    0xd456903500782c029a280d0122240b4030f0401d20b44100f200d5514030500c201c03092a03034079541c0c0b0207550720345480302e040041020382d0841c01e40c802c100c14070004405500116102c0e200d98194041c0344401c090020b040403008001310901c000d0f00304403e02800b50004120040960400c1d04031440307824480220342155407040c00a540103000c00490002c3c2c00001070815441c80c1280ea88001c2003400005108407013619080306005a0440001800340201e0046415000112880c08030800100030100400030201510001185511356400f0b00455802c50005500b05080014511126100c1d90680f2302c036004400030240b0502c2000304140038012142c000c00007404c0300a0085540700d08101181100b0b0b81d42c41c0b8407900c01b12710800025540c1c243c04003901c00003c4c4a00c441480c2040303022040321030b64008103048110b824a180820b0114a82e4801c24407020f100e60b0210b4100c1d00c0c54010145072840080400d0f2040d044100c01601c030340701c2d403151646400090704015860381141d151130400341400206c41d28 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 545170134 1250 545168884 545168887
    0x40902030103060906110309030a03320417040501091412060c070606080601032103140a0f0f0c0504090207020414040c0612090b07110307050105010b09010909090c09020f0c03 77
    0x100b40721a580c0681915480f8010400c17243e990151b217401c2901003260080f241c3d400502c001d880e420b0298000f00707080d600040f0750700542c1c00100d042c000320a201c07440400d100c3c42d480c0104020000c580c1000704401c2c203800c00081c20300380b0b000002441507119006500450082c0c0241c00515199001d840842108501c103851852424000d40c0321150418030041e50076a0811100241c0001c0115402d07050725003203483c5003580b4134000345800c04200329070f42c0c40040641e00c110340c0000c40c10f003d4109000e11240756001c610b520340d00c40f80c01c00781d0f1400d0100713030141494a88081419500842242c1c111340c4403550260311008540005001081c480705445080042a0100020404811020401d0b940c00745c548200d01c4242e800355004a81a9100080a00e2404c002144545000710880361400a0359021286000010b548a40c20f44e9001c0c0d1001001010124510f1000d42c2c0102480d0060642500f00b0081e1041a0f2140c09420100e0310035000c00603400161651551101d5080703602c0d030485d62003280d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 545171384 1250 545170134 545170139
    0x5090112050a05060a0603060b03010b46031b030e150c09040e03040621111c06060203070b0a02090d0c1202030c0d21020c1c0b0f041a0402010201020409020301 70
    0x10b40142c24221406445203140717483c00304689000e4418041500c2d0400c4609086a09200c0010242e920090041a1000c000240b0f9501c40e0718501500088046140c0140b410081492400340c0548084001030306250610f0004c000d01c0e1000c040080d45818a4540840c2c1050a194001d0500f40c0c680340068070a0107400c100b00030f0190070302c018440014240e0701004018000c0302e440c0e44a0080d0f0140f04001040b07800031b04038402c90140d480d4048076201800041400030a1244540395001020f000140f02501d600d0000106051003150000c00e80c0340051468104181d07280c40c0140790007007001ea24664081101440c2c1d8682c1c0c2021200198001c6903035071282c0e10390705a50f041483c800804ca100740701d4148802a039040c000002014280e102c2002015855050030405021100230705800851089509060955840000f080c03408200101095030343c880e1428031244070307030004090211100b000c00c2488001028030880d00040200031146a00700d403220306c0105d01900c01c03588417800150022001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 545172634 1250 545171384 545171401
    0xa051e1f08060d1b0609150315060c0302030d050a0b0f0f0d080c160b1c02070c09050a0f110405150a0f08100509040c290f16300216060509011205 64
    0x4071050f610428071050762000720103022001d40300081c16403010032740125010840316010303001e040c0046100e40180c038145462903c215045480848442e0b241c0d0351109032460450a10380d90b003603000722003550070b64400010000422080405071800070031100340010683c850340000d0220a1496001002110100f0b42d2400d141000340c102204511600000b000c0c18504045503100b02c0f076a40b5800b000300d0324054600007440f0000c10006180f8010540c5440c09501d540040b8400c030380e8220170000300d0545035420407017880a840e0071400d014100b21001c1260482058200c00c000c01d00004600d841081a03032078000a1441d54525404181c005038018144000c01c4084a07840003aa0b00000e80c42c59400340d03900c204050004a544520203440040100311407480260b0014040822403802d800910310155440c0c0140e01c00034400b000554101a500202d489a02110650310098078801030414000340b02c003082c4030f40002d1003541d050241c00141414117074080c03250f601e90094000c00401c0285040c3d800c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 545173884 1250 545172634 545172647
    0x60206071706010c03050304060e010e01150b120117030c030a0203071a07080103061802030316030201051b040e07030e010507020f0d090807140a051e1f08060d1b06 72
    0x59000204001c40301228101d00d00c5680c00340b141074141d64509203142940c6086c0c407194805441510040e0325003074150004c8400340143c0480100c1c500001444008501400002e80c0d019008088507072010020384016520801209064072801043e135004522180c402900e1072081402446e0a0f0001007200d502280d000b00c02303440d006004200c103a110300b1209080d588020812183c60000c41c0d044001800441c04981c01200203000d0a001034940a5090300040d10756000f03030826203601c2410180c500109503081c022103400c403041000f404074412400644507007901442c011810b000340d040c000103624511a0b0000c62046164000810460074614002921102e0300c420100407442414017000e02684074520b10400c81e51110054106a414030008445440701c0b03640f4164070441c0c034407001c01c01c1d47d40c9805020749034800500340300c50905503200b070141888220b41c40c40809140184880340854205211a07800034084646003220805031400071a02403420710140382d0b080b844c1c41e020031080e41020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 545175134 1250 545173884 545173891
    0x30c0f041206021c0b09041515260105090a060e03040b0c0a02030601140303040306050603070f0f0e09120315010903080a031e02030106020a020d032a15050403052502030601060206 79
    0x7460001d51a5013442100b09030780d104c00c3d0041e0030003510b10001d00844d03140d10120005010b03100000c00c2030b0010941104038003600f0740200400404e4a0031a500381d4051502030070750382100d00001d004610340440c14503101c50390010068040d540740c0070140220741c002e200300d41c041c00c0c4480d082c2d03888151002159560782101d000403800ba2241c9400460314881c00c2018441180c0024000c40c07500e07080d80d40c0c00c0041c2c40094591501445800c501103222152000e00f0405400e05c29800d108440c50141024010315014140001e244c106607800301c1140300c1d03582125400314656007005403005048004986522056001074201ca40202d07081540703139450342140c00440000c680340091f1444050700d8400b284020700c103003005a4001d40400005040000b01c048885000b0f080610644c40c5100f03a54034a0602a4501c441c3d607420309c50300b0f101700028588500304001600c10304000342d1070f00e44c2d0040d28134840d03440e40c01c0501d0400b44003551400003403000c00910383e501030256005541e440b0006542e84500741c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 545176384 1250 545175134 545175157
    0x114010806030c0901140301060b0f07020120030d02030612010e010c140c1b030a0c09050402090a0c0f050309031e030f012102090411030d091e0803030c0f04120602 72
    0x3001007011842c0000300c1c2603000f03100510b003940c2c07a482c140001c1e21500c0813005064041d521075000040c0000d108000e0700560748000e01c1c1c0307550380440344001480c01c65008241043c0381030b080e002d9442088004280d442c0d2000c00a07005075261603610004400001503d01c8860540c24042e29561305003040d08030104055039900d91440010132044851506d003d04004064070b68020300081d1800c0c0710380c01c0101194840601681c80c03404943d00c504003118107580000b03c00035218005d01007103080c5030122550024081104018000c0040ea0060108010940e07007400c01c400400468002001882213680090110454440c00740b4601420315454004544512a603107041d80001841c01e51140b0000380a0001c014078107060440d942004a01400584152000219030044107160340307041045107500e005a1f1100c2c1141d0346085403003107820303030151049504000320484c1001001c10020940c1d4200450460054441142d842d8522442c06150b002c0030700400200501c0050101a600900d01c85224 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 545177634 1250 545176384 545176397
    0xa140f09120307090b0309070f050604140d060b120f0c0405090a0f0309180f0606051201030611040b0318010b01030209030c0d02030a050d081008150a050603120414010306290f12011401 81
    0x2b14001c0005900640c4204018110360101d80c90580c40c10540310700c41284981c0b8009111041200030901c1d041d012345a04a007070307020584012108100b04103412441000302c500b44420718111120980790b041d140720042c201e10075120b00d80105400f500120000c0c0c8070312008582082505040c41001e0240c21140b07101151800c070000c0740c80d034443c20803208504100740d0030300010792170360f13030f84400030154400d04904c1e410b0244800b050810062000b10f00034030030301c08061020810500282d084444c03168280f418144104848400c1d0745010a464503111000c0300e0301ca2011401d800841d0030300c52041801400c0c1c1c001c1060146c9041d41100080e8051082c0150020303403a5290346130b10b13070707161450980c0c800701d03ca41c0300019401c2d802c15040f1580c03009001d415514403882040514007190030941007020015506400c403112540d16106110080294401b2181a601c001440b0255008980140900030100050080611504400300d0b03a480310b022071400c0c003548e13403a41c00fa20400009040903001441 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 545178884 1250 545177634 545177639
    0x914100603140d020304180b100302030103150605030715050f04080a14060106081503010f060303080a0b0d08070201080408131d0f060a06180902030a140f09120307090b0309070f 78
    0x1403082e60f05050340d0000e51825041c480b0f0a500030300c0725410b82c0364846e298140b1031000c0e2209180d600c050380b0035480c096100c0d415450038424104103002180c64075450301000700a5640c0020360740048829000b400005a8040b60013191184251001c240004100146c0002d841c0320004401410300d0150002c004a0140300144a88624080c407a050016604101040b1840701b1301070f965080203402000000c880c2e0907541c000055400607481540400c41c0c08080180700301132400340105800d0704450000c054030300c1d85d484410a00540700044e0400a0800019003001000b4040300d0104483c03081c1150f0960360b0305207800603d4044c2502041070030660022030018100480b0316806050f00402d89604a0700340581111000d00502e0483d0f48922690000500e540c046e00c001c6002d0034100c074010034204920040fa0040040280841e40ca1802100400000040c04030b80d101d0072801c280c1000b0340da900d41d403a040741c17508401d03040441d0601e4000280410a580015604101c5142c40c82407030003150f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 545180134 1250 545178884 545178923
    0x5040b0c030d110c07090b010903150605030f0c18060114040b041509051f180e0a1107030c03030207020f120303090601090c0f0c0c091514030a0f02040914100603 71
    0x1444c90414080d9020050501501c505504000c1c2c49075010700d09a445555640c640c00341d08a205240d0b0214980d940b401480181004e01c55055180b07504c000611000100102084010000070800c2101030142c0000c105540e02c00c00c401c0d00d194a02a1506841c0c13074440e40c01800e140c0c4a4800c41ea1001c1903010071402045c000e68403901180c0c40144000c0303482c041030302c0368003074550031400c00010442406144c410300c0c0c5080c6031000c080c081c80d00650380c403460072480700d00449a03031081c0442420300034400c40300043c1c3d01c4581c03c140d0a506240250b01c0d030740c0302c0c800f15100ca18010741603640000c1007601480102000400740d48a4051442140c51176680d44080d00304942c0390b0803150f40014000803103184d0b00c6000e6440e041038170f84120200d108035a0f032501050300711061800b500c6000c1031500810405c200e0141c42001980070210007034081c480042e55a544c405440d4100203000d02d8131784400b40d00f8450040c452044087d002401c0e614615a280c0600004003030750300046642404141c6980e5201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 545181384 1250 545180134 545180137
    0x160f03020d3c0e040e01091502250f170706051e0a0209010203071406072a060c12050a1d03070f1e0f05010f05010b07020d080a05040b0c030d11 63
    0x4290b0403044104440c1c100444003181ca441503511051140e0702c180ca080e1521a4031440f280752441c0d00001448501916000076203904070720024440038014400210100016a803404203000c4020100d07211300c0359450b01070800888900c1c060b0200c0845c00c4007400d81e4100b04d0041044900c125410400c1e40d4603135044503640c8103070f00720800685101400048400704a54020019010140112030030500706940328040000300b06c0381c01601c0c0c0c004006004815400001034180004030704041040c151803684043c0c03000303025200c003034442525442c1c016101030248440e5490004c4080080c003c6240040c00c0c0800390040c0c04070148410341144078025041d5010064680490380013a80e0305024160740c90700301c06032104400001e2054101c860390f00c0040c404034020011203126600200c0d00c840001040401c8407416405210180d1082002c040140c0d02c3c00c03002e0f40015400707c0e185403100c65204088580340240d40007202c05600c000303050b4000c01c600102821940340030190601203960317003a10768400c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 545182634 1250 545181384 545181437
    0x307031805060114061312050c181323010b0f041517030f04031406060a080307020118050a03050f010b2b030507020d03080a0c140a05160f03020d 64
    0x15030304108014041c8080d1382d0b0070303003020380f0b80203101c503040c9012015100601c25180d80704107440e1480003403110800106111110218004a80e480c807041054010003048140080c9100344500c90260800c04105400300079902c02240d01118140b40d0100320403050007040b441e00280e01c141c1c91402c00310036a1625004d242d940700081240c42c000300e4030340724065609581050141c1900d0005202d40012840d2030700c080c20085008250401000440301142c501300031003d82828000e0351002001c0c8185103002046a101ca903080c80c0030213001243c00d0003800c511078a40c003e80c0d400001d41d0800000d00c640001d0102c8036112080c002c205010040003000585a19500074148104200c0800c140f16841302c08501c20280c001e00740340d0700e824065030000d842c4035600303102180421480424444403600c5031140c1000e120040c10004500c0207403056020b61030095550540c100107000075203144400e451550984c0d00342d44000742d41391360b000525000c3d481c3d080e60394412000442c00e00c7d0003c1c1c00b0001294550b034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 545183884 1250 545182634 545182643
    0x1b020c03151501110a0203060c070c090b0105040b090d0507270209090105130207020d0b01140307081905010e0607050c1c210902130510051504060f0c12020303070318 73
    0x1400842c0001901d50748064030130041d9a014000b07000c000350b00c080c0442885002c00c0d542c0c43d135031020755103000801030312541c2000d1003103031515180e020300d80d803c0422142070781d003460038007a110300b45c103400a90f41c12441c04000f411030080c00d01c0012106640c0a03980c15010800003905100d505a0b1100000c90060b050429403003480400108030505080e05101c00d25115004050300e00421500401c0200300f0119040381c03140c1d10100100180c0e00803078112042c3d0901200504011032400c60096036980c540140300280604040c800020004250320180315607000509644c0c0618020501030b05517000350041c019640980b803004070b0244840881000107001c0f6072281c000c03081e16050075001c403551590480d15120340d251031010259580111242d090312207000086200c1c944000c00d20300321151a88240d0203560712a14000e00c00310b01c401070303030190341140c0381055001200f46004c4030035420701c2001500c41500c550ba6500f030300358040011481003800380c50038001850f1120b00560318041c1d5a1000e407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 545185134 1250 545183884 545183911
    0xd0519080f0c070c15021b0603040c0b03060d02030f16150f0c1103011505030c04020720030c0d080a1407150f0e0304091a120a030309061b020c0315 65
    0x20710082d440340c0901445401900c1820b2000c1c0c07107128914070122010b0b4508096440107029141103407403610349440361f03c015582141142021350381c0030a904c4a5006a03603100720084002403c40c4c5496145145035a0000e01712082144079030b00b5103445428038203134401c03032080749440840c00e0080c9001d240c0c0088025130310854600c4248030115981c2e411803008485000c0055055202a070702400b40400544440c1c44460b4294a884201864002c0d0850060b004a0041c40324802140c0720381e54110420265400c190659440000080d042074400f0140c2e90340701820041d10824000301401810341c0e648182c40da2202d030b0240181c0303680b40703003d5004000d105c0b40d00041c03e070f0b0206101c1e408c0304415400c41000032800d0400b40442a0031a00143c10690705603554203010321b28890312a40a030042107060703c0c2a0f151480400c44c030303502e400703c10001030145901d82e04110b08110781c55000f031607128034041044c02d4881e10400000c0d21907031200c81081c42840b6081e84400c003071440400c480d00070090044880c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 545186384 1250 545185134 545185141
    0x301090b070806010915050a2d181d090d02010203040809010323160212161416151116050d030216030b0108100c020c0603180d0519080f 60
    0x4a40c842d10040c41030b07040041c0c4800016131010000d01a071410482902d585445010180000303102450707000c41ca4041281c1c158044201e08484400404491800e18000141c01c0d0364000c440b000401c1079104540c03030003540002c6560700341002c030003a00400701001a2101e180343c17188200d007070b8001514040c0040c541040000c88540c040d500564180820484414500350f01600b20410007000f02c403103a03244242c512103286440d9040c8101004190707140700c0c043c1040c4818840c04183c80130900028100502500740456a140401c041d003d04d04100c40900001600c800c40fa91000220352111404581a01403e40f42c03071b00003049130840030041c1c4040c5c2040074500420040c00a002003c21f40641c0103424a00360240c0307022109001541c055078115000e940f51401c00d529100403000c3c40b8881901d030031082d03c0c0c0c281d80859420300c962802c58410307880341c03200b0062000801c200c1071411420b01c41e1031504059543c0080103810702818481e44981100300941060303507141d204542d0340204840b080c001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 545187634 1250 545186384 545186387
    0xa090c0807050a050d150c030509100504080a03020a051207050702090105030303060d080d0204080f15010510120b0f19050f0103020f0f031b04090510120b0601030e0c03010f02090f0301090b07 84
    0x820b040ea4007841901044003080c03d00b2408031107100b111900007984540412640840410bd9a80c4001c203a00d0100901c2c40c164507040b02c0f03806003903103540c00c15400003000c000c1e50384507009a40c001c0c0702124401c0020305000704043c041c0d40c0042400c80c06041e00740d00029681c41e01206aa10699000d400b100140590382d4030034035030768042552002425400d00000c030712120300b0000701c450343c00150020404440954070300700710240142c7c00345100f220320340380207190341da4001444a84c90080c21808030f100c0800e00005008010045202c0780c1185074000410940408514040116a070a07203001241d0300c41c2030011404e170f00c01c00705840c03480d400c2001004981440a401164001c0d07031054418403294010f41d0030700040c0d025500132444640c541d018405040401001040240b12001201385003000c0b47d41c0d9400841c02c0200800d05266503041c440c04010380902c80d05404010040c003c00c8201c2960064200039008040f40030f0064020311081e1800342014071400c001c0e5074020320560081c3d03450060 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 545188884 1250 545187634 545187649
    0xd09080616050d02120105030f1c0f02070302090f15030607050403082d030a11121611010606021f0c020c0d080c0601030c0e0f01050a120f08030a090c0807050a05 71
    0x440c2081050403c10700090790401e2004e8108008000703040b580740d500d080c04051a080803040380c4082e641014200d60800c105000c0710004800d06c50a0003000e01c55808810303400c040c002d61000c2c1d004520710f000c1000c1d100c1c0c010812881284020100d501c2400d80300c0506a44080c21146800400c1c0200400c3c401300d4440400380405100d110006101c60040e400661803915041c865824050070210905c1698030081c040d08807a62007046040c1d08001c109419500c01100141040c01402003159111a5083c458820441090740510082c8200703a6100d000039907804c06807031842c291400300788602203040f00900842410955603401440018511030030404403045020049803600001c1000900080b008d1109074000c601518941c00f40a10701a0a88482400107003250b200c0303d000d00050251b552485202800d070b410110f402da00c0c03080b1518105000072030188010300000d501008102d00c03019142c1012000038440c42401d8455a40c4181d05651031405010700d40d40001201da0031700c100e09000c2c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 545190134 1250 545188884 545188921
    0x18170705030f0408010b280b0f0c010e06070e12031b0f0a0f030305060906180c090d050d11031e0a0306030807050c0a0f0b070b090325050d090806 64
    0xc1a42e00d032000c07111202d401984640d0001800b41d44070310455800745840e400185600d0801c0b00c0c4a2500c0e07030107285190300d051482c040c03108211400300d02142c5041240c01a9003501c8140c80003000301c070558031b50295884604482d07041c0090101c520507106401e0240f0300001440f000001036003441a83c1c90301c038160400404d040a080d10509100500c9400104440c43c1c0c40350103a0308a034880c0601e41070040940e0301c01410360380a0341c204402d0040725120416501c1d40080e0f125680c070740315161040d08011611800100a030301c103080c849024140315006c191903070746002d01c0d159004220314014595403a401050000300000017010303100c04035446504c00401c0461014a8001520303622a910805990040001501d06a0000c1c081030b6a03070400d040150068403000d03900310542894080348525a00ca40103000f03212820540104162800c1001a00c200c5100c848401d400024a880410941441aa016034845c40f840c0d81006600e405807a600041d07800e000082c0c8081e9035018544020f203034011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 545191384 1250 545190134 545190143
    0x60501080a0218060d0c02060606091804050c04091a180a03082503021201080f07031e0b0117060c0910050a18090905010b0a080c091506180103181707 66
    0x35043d541c01582ca240042101001d41040002c203c009454000c4c540100149101c2c010f103010010350060703030340702d010182c01c02c2621106400f05036640c0c034003541092854801d20780c000f0300300180311040124056076203543c850a9074800d0742598582d604440b81030700318510302c0c010740c01c61510000441d1049a00c08e0b030000c55074184042c4141a01030441003245c50b10110300000c2e501152070711001c0e045000c10342c01441012b006104507a141c0c03620540f21402840000c2021415100d04005c4507240d0318003103101c40d002581d1820303940e0b5480885010f40c805607503018480c01140d0025860740c0c0c080007928000350000d007001241102c0301c48203942a40c030100fa200c051003809034110f1294a0b840c1032110240002c0c107404116624103107455400d40e82c0d2030354901d1062020003c00e100c0042c002401d00381c855812110802caa855601c01114503122a0350400d070031070030005d1b4402e10850401842d0070f003030000380d85c100502d203050100d14480c905070fa100204541c1c019103560318a800000f01403c00103000c1e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 545192634 1250 545191384 545191417
    0x6130308220812010326180d060908030601021005010e0612100603030e0111010203150409150218120102121609170a03020d050f0904020a0507020409060b04050a060501080a02 77
    0x120707202d0861507046240c03080403008404005204201403d020820889448103810710758a240e50a4441c450040061809220046813002480c603565480c500c1541a0004010460700b0b180f400c00c0071080e8000c40380c0c18054866411041c000600320710503107041300e6001003800101d0316808104050000070f0b003c02c0c810382c403480214202c545418800c000055101e074031602c1d2103000d040c0c009402e0100c00000c0e52210303481402002000c0001c02000000e03100100c0b40040d08410a02d004c0e8008480900c04010403440801c0c8007003803034403007180a0310006045a002c0a20300221128600b80d100740c40d000d903400c8100d80040381c0c02000303003900d5114040180c00c141c080c00781c480a4050b503072074901030340402c0c1d907100350103d1062603010300035411700030154a00303c0c1c40d0000082e010049031055581e103d000d15800103c0c40304491040301a21013041c2c0c02003043c031070140d0034103059000e400039402a030f200310700c0c0c440815420b00207445010102e40040c0c4400c80c0c40e989030510b40c8003e4010500d00c007000c03c80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 545193884 1250 545192634 545192701
    0xc030c021005041d01031103030c0604020405040206160c141e0108061f020604110405090a080a021005070c0201030b040509071701110406021b01170f1b0c0d0206130308 74
    0x2002c406104c0c0407112842100b541c0745040c0841c0610707e030a4001d019402c100407210702d070761010900e254415019640441e5984561002c54880c0c41603051120440500f11010020840100402002c076001807503a0080d4152000c20080d58440c120284028800c41100f80c07291940034816160707000000030000d264001c480d0801443c0703200000700702d0780160030090820081040402e190900c551094038200071502c1d281e1032060b81c03851401c0d000740940c0c0010810705400c603c00c01c403004100c05020414891030402c0070001e003044681c800200c0c042400d100340880182400e209651282e4040d43c0288401407524002e09a4010255024192552600c0c0e800807009400c10003031008103400d80c01410f1903084d251003111000043e00c10b0314100040344091a50154009a1f001d4201014103142556901c0340405903041c141d40707030641103085401060444044501042003003e00d1030306d4003540c5280e030fa036031569060454048002004203403010f0210302c0302d501042c805103110340421072240d100329 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 545195134 1250 545193884 545193899
    0x50d0b090c06191211030106140c0106090515030a03020d0f11030703080103150605090f090109050106080c010207081f02220f03140d0e131503080315010c030c02100504 74
    0x80c445201c0140010b00d42c088211410b0307001c0088130b0418030300302c0108081e142800c1c40080a10041c0321b81d40c20001c0392400141895000021541c0c0e0030f1202008101481d034a00320b48016200494400e8000301120b003072032509040214079031208a9040e0302410305810000810745030010401c6100d020020031959036501c1c00010401050000d0007502c0f00d402640c0b5614104034540e40c071800c070204403414148100004d03101c1d6002141c0101e0040d00d40f1a241d507412201d68010892410302030020740c241480000c400f500070600000890007079007134403a02c60702c1d541e4a5540d04100171101c18195035403c841e2107031401c3d43d80500280104092515904c502e400c0e1151411550340d00180c041c005180000c04c2004030009490014110480c0a000c4030119400701500c503280229610340220501c00c0a035000310a0b035442264291403c20a9052482d281d0800302501d80048810111100c0d546400e05c41c90342c018000511441c0e4540d8800320340d2200b42c1d00b0700000c801004880c0b01407090510001c602c0b403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 545196384 1250 545195134 545195137
    0x102072108030a2f030c0a120203191b08010b0a0c1202100c110d0e040b040f05090601050103091e06060509070c050106060e0a21021914010504050d0b090c06 69
    0x5802d000030200344d46110742d240445506a10307501142503441851440c4040c0482c5003138039440803800400907140c4d1038914090301d40552074400780216500c0001000a02d039401e00b10728180741c0000c01d0030080d01001c0002c600110700121603260100f200750004000607c540720050018800300c0c80d2942e445d0f0140e0340e031025403c800b10f0890000d40c00c1a030000c7d41003c068030910500c4801450204842c00040148a840d00001c516150811050381c2040c0490b4442d43c11031503001401500070001c0c000c0d80c004101c010807061310a40240d005103070000480350310034051a0200d6030840e075109410300050152040140c5040300c03ca441e591140c1d80000e071591440c003951b1003202d050f03c0b040310000161621608550305604040103212142d41c10b0102912811413210075690105544810810203278078490800c80b0300c0030025480301e00840d1402c041d08010302504202d940c10401d4514550340d410040d06e0600075401640d40020605400c280801c09514003550041c0803041030302e101e09402000315646 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 545197634 1250 545196384 545196391
    0x6110406081501020303070f030b0414090d110c03070605070303090f0b0415050114010f02030c030a0504030c08030c10020a2f12040312030203041e060920010207210803 74
    0x80766802003000b11000c0080c0c85400214400d2001d14614600010060500840d0120782010160f032602444540c1d2070326800300c070b40740030b050000f00701c5842e2410302c050b500c3d0190710910380014422181d03451013560010b01c203004041c0080140124606120048510784c001c42030503400c040e11a90b452021900600c907090440c2d002e00c4500d2418500350600010361f0410010384c100d12460030004000c040b010f840d102c080c0340c9003446c103103a2000d040c22080f40b55000b1120149178038007000905040081d0058010405c40e13105030810182c00342d5901e0800d44a0142500b128101c0d0001441078810702507513401060b0405003810035824000f210b40168104040c905100d96400101e00382c5903407031040820846401ca0418601d01c0d18144c295138a030b5104084840c440000e0503000700100c2c1c100700e50f6070004014004a400d1490340889642810400703440c8505042e94100544104005e00c107800100840103004103800400b2494944003c0301c030745150300004054400d48023565000002c40c0030000750300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 545198884 1250 545197634 545197637
    0x609270f0f0f030f020309090402100201091b0501090506030c0901051c0c08100801060302130c021903050403120c110907090803180a0b032806051c060f1e0906110406 73
    0x41a5403d10700903220310303041c00d0030300c0c150750041c441c0e8040c03581d503400383d140d000340c0c16501641d09003640c139801e13405889424401003000440220602000c0d0244840000f1640d00341d89a0406985d030310107014441c4801c2d01c10b028602c000300322080d0300c0e50140000700202d107146021550810164246174046841d40c1e8150b0f4000b038415018441d82c0041c00d02c000c0c01401c42c1c3c2000f0040d8601d10742c0001d40b2980344801419203940c0311401c4500d428002d1012001d43d0180d1032134060102205c1c81d00804640c41400b00b194008031108002c04214401c01420707e02a6000000708401e0020104100b0031140c0213003200b007001388403107010854040900c0584410001d4101c0c405244840380d0400c90740800d01c0e0400403100f407090003040340d030301e51120300300c403403000741c040360031000c0f941c0d2200c00010f4900d682156402805a83e1040d1046042e0509542824002c041c1000b408103031394803540684554071580500e401c04143c0f48000d00e0307219400740e001d0b03a01c568030019445101d5541c10040340c103d130348500c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 545200134 1250 545198884 545198903
    0x23030904020d0b0906120c0103050c0c06010b030f010608131b0506040f03060b0d051203070c0209041505090c011d040f1a0a080c0a09091b0807090609270f0f 69
    0x30f6050811120031908641c007200d00780303180700713404034059540c00c01000c509040503291030210304410a80340844d45100540350a4608560f1280000485544242c4403260070810315000010058440c2c1c0c20217000d0554025004130103601034440d41000e03007010035600711320b613181e82000515507102e0008000500414940b4683c45e4035609242c030032100c071081c1e45030040c4442e26400001039030101d8152482041804a643c0b00d80712040100c1d80409907000c025045100c42c011b100a00c01c8410340704041000c2c1100c248920394078102c1090300e440c240e400c2c0342c1c040780d107107a940c080d8164411000320065502420010302204410031060903110b812003409503980e0210001c450a06202015001038a00d88009041d82250310b0003003291a0070a100d02030400356103e0203a42002103c00310b0901c05000c038061008526112584161205128442d0403c842d203000f5002860b51294040d0b21004001c846a00000851744d26041600f00046d035012540c0c400d98100c11070008910b4130401185500526074076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 545201384 1250 545200134 545200151
    0x1106180312070f031a06091908101401060f09030b07032706060b0a0e06071e031d0d031d0102070803070f0213180f020f030d0806030c04060323030904020d 68
    0x10782220b008800180005d900c84011104580780c034011601d031508280e03000380c811480e00c002d00c0c2c0c1c84d150a8004110038010700038011200d500c59000090512000c1c2100d01a41e40d07501000d803030032034a0441c10001704210700c0041022030101005d095001c20746040114409078017201900c00c0189011920410703411041c00181405500e204c1c94000c0c0407424143c41c600a49208044c200992243c03019105000008005041088011440d0358071049d10105615000300b0746409070400d083c021070500b40d103c00d41402c0300309203001c401d401907658160300c400202000c1c400340c0700790540e50031240505600c180da8000950400c00c0006000041c000c28a82032098a42d05c10460002c0c00101584011828803a640007008066552104135a034007490105c000101880420b00382216080d1883d4135008070015600006e81040f4440c5c8074841c214281c1d0900c014690400049403100d00010389104000b903000c070310780b1000c2129001d00314801001c89090800d41400907040e46c0c0583c81c2e941c5015250b81c03e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 545202634 1250 545201384 545201387
    0x3c08030a110f0409180c0b0304060e01060b12060d0c030503030f0705031501210f06030c12050a12110d09150c0209060105090d02040c17071106180312070f 68
    0x300444980500346041c64031540300e01c42c8545024500400428541d600c00501c06200303a040242d8100707902000c000c5050703030359100c803007181d8204580650b1140d08010201410510600c01d01d0196000410300b50b041070340211500081110080c0216001030100c4040b1000c140d0320805c103002184100020f503500d1400c011116a0010f001d440c1c4030600000740b0078010b40300b00104c203e00d0402020319194841e030103515030f0740e8070030304c50415001c1c03101e0300e0280b403900c4e036034140d17000001503030700480180e480b895451442d00c4091105000c080d100d604010428000034a5011440d804104146084c50301003215545240c00e00000343c140001156040c0c6e0204401f504141541d00902c4260a1402080c1000d40102d241c1c1c1800500c46410040d000608003060740e544580c5c0254244c02030000c00082d5580f01000e40140406d94110102c05102c0c000540b00a100f504141c07480e64450010700702c2a03c07585041c050591225241481d14002400302c00100b0070441c40c0c8034450011540d0340403188807141d90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 545203884 1250 545202634 545202641
    0xc030c0f130b03180105010303080117010b15040501320c1c020c010e09040314130801020d0509070b160b1824010b04080c100201090506010b0706050a06033c08030a 72
    0x191325070741400010404650021201811204400c0c549080e011103000e0650044c505110b82582c0b1000311a60003403503030030b644050000e5800c02e8032003014a078043c0c00c1034807001e8a040d071100d00f40650614030301c8159072000081c05620701040200c03200090801e0701c03224041c110300360b580c0060784480038842456a00c01715041640f9415a244891402d15440060011060140c40380360740c040006c106c82a02c1d4540b59100007440070707500031920351302c4002601c4054241a95001407600c1088804580420303004229116071082403041c0700030642540d254080e0800044c949800c0009500040c6024071042c8810112441d458803a65800c0321440041d682105042c1c22540d03940c4418002404103580000300c807280b100b000c0720303d11840442100200d0140180000003001e83c01040000141020020050300f0418410081401940e41e10b44811048400300d12028003040c0e800c046462007081c00349010b00c01d924020400581c1c2c1c1c40842c5240d6108501190211003c0c2400020810f04141511 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 545205134 1250 545203884 545203921
    0x150507030b030307032a031808030f07060c05040506180a06081909050705040903080708090312040b04140d0f11010501030b0106050c240117060c030c0f130b03 70
    0xc040040ca612071000ca5901e0086202c014240f08000c41d40903540070500c0d5100f0700b020340c08005041d40303021525004240c0403a10750b080402814102c00030076194404026942808504082c8508004454640601078a030ba41000d60078400200000305490301c030b03400201641d0326200300e504010440601801818103da80c000010040d04000348040f001c50848150120700c05240b0114080c03030203040c040d003010745a40c0910b50191901100d0010560010140391051049844544030b5035a4052400d807688642111404540c40701000500050442300d0203a030000e001c0d158845042002010991400800040000100c1c40701144190926844451548404500c80003030205524554903141400e03010b000d414180701010807240081101005460f48220341c020300601c01410415244040402c00e000e014084200702d01c0d07029240c880001e040740142411903405241d980d400508204d1500601c0b0281c3d202030040000040140c0c1004c0c0900103040211078031a500d0070445080c0a0382c3c06442d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 545206384 1250 545205134 545205137
    0xa05090310050606160201050d050907030c080a05120c0118051c051603030b1207030b01031403070b07140d02040e0f1b0301090b0604050405070f0f020c0f100c0b04150507 75
    0x44100700301d548035001540e840a030352030f040302c0e80c105e1540f0060750385e4051700f0208100145040104248680001041c07000c40340038624070580719031242110b0361101143c40d00541141e00102c0720303001c0384901c5001088400c28240002990100c41d500310740ca003103903001003561140e200004000031180d0700300b503500c1e420410b03040940c503000c01d0301d40c034006010303e070500078040c07654540031000309407900300038818a034440c0d10075940055104d1a114015201c02e010681d14a80d100c0940e900c03600000040b201e81301d07000003000456584d55201122141160807050740400c80030302140002441900140001e000c0ca03500744a020325001041c21003a0390020b010380e074180080305004807080c0000048034190744503940003060f911041d0020802e58440c0d64000d58010345014100103000764000c80070403601400b03503038003241c000011070300b00d0b03a0369001c7d080c0c03c0d8000301c201100c0e0b815251006071685441410f0418482c40e56080d25140080e8604807402e0311050355450154039410120b1150651200d400d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 545207634 1250 545206384 545206391
    0x503030418020c03040e0408031e0402010e190f0902091302070f1b030b0c0a0e120d2003120a0b011b23030a030f05090609030702010c1401020a05090310 67
    0x4142590694080c60088207031001d5001421101805081c400c40380a4004094542d4190400f880d109085510440742c004c2d0f588401c03240c035450002185030040c041c940503541e41040403490740401254480743c80d100c800400c8048400135080049405000c000c201e0618010b85408540c1c052001c001d40b44c800500e1000d2042004000003003040748201d030f07480c0c2c0260b02c0e4140501720014250700b81c0259040a46607590360380030440c0c6030f03030000300806d000a031580c5d884080c0c4043c04140018a4480741c41001290056010450b80078451a440b0400500f03055003845800c412200c100d0031644002c640d2040280940d003000410f13402c074010013007603040a01e03242c80007080c1220f1f0302a0321428941c00900e144100101011500d403548014614a80000180c1e540ea240c80030b0050010302a001c0c5017140c150070000024000100030a410b886094034201452406030203500456a203008030101b00c5800e450010203100d82d19003440604101002078407256a141c5000d4201482c2c41802209440030504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 545208884 1250 545207634 545207639
    0x10e060423101703090a031515150e010e030712020d1a010303081e0c03060f1305010614041202040e030d09050a0606140109140f0301020d050a110711130b120f0705030304 75
    0x114926880f00f07c80d0041e84481c1035a02a2800c1009130080101c480180b03e21942d0110300c9409004144a503205591205004104c80400542e45011901310550f8140c00580c000c110b0b50000d01001110188000c0c140c081e40d00e0350f80e8a4000050044034000c8072128240c005004042c1c21101d81a0818090310111950b41b440d40002200100003c002800042c008400308801da16004900d0390b040100070034030140c076481700100c200100401d10802c4e001440d0400791800039000b1004890503110149000a081c480b26024003000d4824038100c80d0b0b0314807040011300d210103080c2c420310940394030a00203084110102c1c01d101d420303202190407550401c48609184986c0d607030808855030446580360046542015a000000c52035410300320010340650000480150b64030003a40118400c10990b40d0800089100303160308002e83c05014001450454801100f0000e40392403221140580007070306010400c0c0c80701c0c00104126a06500720109542c1c400788020301143e5040c8031345006030005400a50500340b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 545210134 1250 545208884 545208889
    0x415050304050c0d02120a050c0a090b0a0506090a0503160302010f0906020616020f01022a1f05060a03060f0504061d10090501061a0a0201050105010503010e06042310170309 76
    0xe440e84981d6103e00e1440401000715250b05180301012001e01c010340c0c4501f040e600b0015103644607540c120344101c030640d00c00f10f454603051040ea54506800781900344034504000034841039a10040c07180b51b1210840700c0000e016a820130080c00c0ca64a00312000c0b003820f1841c40050004030500c11980c0500401500c1448070b10340c001b41c8154400344040c0c06844418540e4002d0f42044081040c0c0300c40755000181e034101d4030001b10004401c000000079240a42035031040d0081d110404030452031050b0000440000550005030042504240003c0c01818050382e2a81c80c98111201400d5400740143c64008100034402076114601c40b240e0b402d4034600d0304100c07008a039a100d58514054501a03541da42344001402000d521880c0500314018402504800350000100181c008802540040d800c0c032001203229442041a00d0490f107100080740c50a407500170800015002e8000d03003400f615640041c00030f2410030242b03518060340c9596410b508450030f081400b00c104680502c02c0f00d040c0e000b04402c05854 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 545211384 1250 545210134 545210143
    0x20d0801210809010c080c070317130e0421120e060403050a11010b0910030b0c09060708250b150d020f1908030f120f06010e040c140c03041505030405 66
    0x82c2c0d001082e180c2c0c840c200b03001070350300c1e03110700b44050011400440c01c0303202d8641c00922141584c0c02101da2040c1e000010300415071071711900000406645500300200300b04c0889442d20b03070b08280b140b503819074103106c10027052040e200140742a000051440d403030f22040c44818442c0c803080303030060805800c051505440c060220300ca4004038074200004079084425000c0d00f076100840026004043c00054100201c025045000d90701050361103803460004501080d0707841c4100e0342c483e0000f9050034144031103500c41c4032140d0014001c2802ca8801181142d0f010048800398100c0c50f842a001200c0c07074200459071640c00c0e00071450b0386010f041180405800750350384060282c00e010b000c84030381003040e41c804000d1100d41c1d030b1503014900600c03021521030039050300200070f045a083c441d03180c51010b03071b90b03e038219801b00c7c4240c584030702007a40f0031151201402c107a00040c80b107503542d0070500c3c50788034140d1400030386a01c001c6201a081d0800f003401c0c003091480f5840881c18880070300c4d107a03045043c00c1d100c50b9201d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 545212634 1250 545211384 545211449
    0x15020d03062313020c060414011d19081c0603050f0f030409020c01110406030f0c08040b040b0a021e04031401022511090a0209040c210b0609040606020d0801 69
    0x500d11007010741900043c0368040380c40e00400a81618500c0c1810300d000c0b54052107001c101078040d42410038800a2800800406a6100450009140c1c1185914916403208151101070b90b01450402040c0c1445403d8113995200400d50760001030b40c1441e60a0940c10001d0202c22002180c001d00c001002c41c50001040e1401e03071390509801640e400300071041c6401019100c03540070314018041000240c4c42d80540c000703042c0c685c4041e010702c840d01c0c2140d002c80781107a0417100100500300d19004180400d035601e81031a84000b91020044c901010030285100d210404860b5130800d100000e418801c011050f0380d20310441090030001d5080c12040d0b40c040444520344201d0400200b51040484140b140455201d080c079500a4202505400c002d40404d01a40c08812220300036400c0c41c1c400351a182c89031100c07041108888410300308036034045541e1790140044020040c3c3c400028052200c1b01d41d41c3e44180e1009000c03e030000d142c55030041001400c1a80164042400d0b910b241c20444036511081880021 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 545213884 1250 545212634 545212639
    0x603060a02130e091c21090c0e04060f0617120405030307081c020304060902042307180b030f0717010b180310240b090a03020d02030715020d030623 65
    0x55a880109091400044a440401010b550f240c8803175600d4000c0c68040b02c280c1044c0700d00031280b194580880c20b843c00c4100c010500e91059038208281c8008281c1203811500c594000b2036a41d189882d034a05899180d00040c903c0c0002c0358405020440070882c2c040c0d0303500000011801c003458003000070340364000c089000e050282c0011300a076102804981080641c11320f090115143c4c2031508141008140c03012080b806185404803141540d420440610281c900c50840c0903c1580c0b1890129500c02480c41d000182d4003d00e100072038840401c80240d4440c0803501480e030300314a0810740c014aa2500000d004c282c222860300180003015230601141e0048070407040c40e0b908441c00f54086032030201400000784080b4038101d55904895000c010124154090600c03d850680d215031046109100e401074640c0e20400d020f40400050a103071071034108090006055903210b031740e9454038100f55851748810000507049102d400125a802d40725030381c00303401002502e2109450058038150103951078100d062 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 545215134 1250 545213884 545213909
    0x81e0a0f080c0313060207170303040c03060f1d0c040c140702010311042705090c0612090304051f090f030201051b100e030c0706030e060f15060408060603060a0213 72
    0x220b02d00800c0080701c035020710311000320358880e0703548000a40701c6000f0301071003058503640003001079005800029a801242c000003215102071443c3d9034030f0024903a120011001d03548500440c02e070840410350200840e2010000703000403107000b0b802c12040b1080c08445005214000e940f41c001c041c901030030707201d042da07081c240041c2c028282c40e2506018003d5500003840842d1061050444c3d2450b58801a6603510000c0d090005441d00302050751144852001c0c0f82e0041001e00160207004480c41134a42c000c600082583c0c0b50507101c01c0840c44081d85440d8041d9081c00c8022000364441e80301010740300420401255000d85425940003e040d842990200e04079103001c803034610141141400640d2846038208020441e0348403418500d80c60b60001c41c10148540038034100019a1400380c00b402032448150300c0034200d255a00e80e4a04003211015141145001103100b0807110b035100d050082010b4040000108070700d24001040614060740101010966401448100c400300075200000050b02c00049829 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 545216384 1250 545215134 545215147
    0x1b030b2d07051602120307060e0102091e0a080604030801080613080a08040201090b0a12050a020f0708070501180b0103021c03050d0903050d050a0b0a0f0f0b0306040f06081e0a0f08 79
    0x83c0603200c1c80e000b020350b101400c500da14021200c00401401c4071380c42034009005030756100060340c0c200d020304031105400142c5031214440300664200c040b502c4c240004d005480c91520350340d40f5803510100312401c5011a17590f00042c48490320400c4140e038402d00607c442d81c0b90007656603c81030369026100e200018088a038020408682c0180000000742c802501c0054549070043c100601c980210040d200e05030b803602002c1113000c9508d000702c92443c5041b18650b4a0001c41383d48000c2c6d15804803c05494555840030b5000c510800042d04950b2540690a108895415401085483d03001c0325110200c07040c084002000094102040d100c2101035480002030000c580e08040e500343c40343c0c24a0038002c5181c1000c0141941c0039038040014407105540101c1c003d616014103424019040c060404030464040c82000328034040001994444c20203040820345c44003d4a4900948805411131040e40d0840304440c0c05c2000021840c2c00d80c44030100040500607156141e0034240303a41404003a1072541d0000c0c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 545217634 1250 545216384 545216407
    0x111c1b060b0904151a090615130f060324050f0a0801020712020d0c08190c30090e0a02070302120c06070e0604030b0f041b030b2d0705 59
    0x544040d48003924280c0b0354641403a1940380c1080e100318000d032180c41e10500400c1c03a146019088050036014100740600d480e20001c206200c044030700d8000c2910300400001c2107020071a038540c07008001c2809110300c007034101140a07040c2e40b12002c41c100039024105c201031031201035030303c003404590055540c410503900c03000c00715400040540080005600014582d01004407240b040c0910090310740c01e40c3d01c1d40480450454000148060141a940c0240103403000203100d040f030440c5000460402c0c0c0c0240030309a071640d440e406001c1d0011440044101d0310f0009001c00c1800044e031081030300d44850302da404c01600b1103421a002d0719903082c0c540c0c0403400303404260081110f50014810681c1460721a81c0c1080c0c050b40c1d481003158140c0c0010100305002e40e61307084c03030000c4c0c80c1030700e40c44502c500c0546d139000311124183c0385c02402074070030101d0100c0c1404001c04900780d100146002e540321400500e420040c0d50010300d02540d10113000c40c40b40c903002c18002e4607100d00039000b0740c01c1d1400a07560140d5054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 545218884 1250 545217634 545217641
    0x18030111070b06041b36060503040b091908181503041e030e01081509010b1b0a0f17070209010609080c0d020a150507050d111c1b06 58
    0xc0480c0c4444002400c8014000200300030b510450381101c013408a03080d0a03c03005042d007800e0300003001040031a139100640380040c500442016404018061440e410102d4004012980c1ea0004012407000030500003440b1b490720b50755a100071002c00500d1540320004555002c140716050241c064400800c621070035068003804000301c5071004110524003141034010317800c158410340d4201c901c0b002c11456a01c41c54054810012883e81544600c6481082c0c1c03c0192100c038801890000002c42e2030002001995840d210a4042c0c03040400c0b840c1c5a4414404604220b28801c089843c03941c01301500800003480c04a0800c0c00603888503542c0610300b960700710105240500d020081d1300803044000868400d600554903000c623807648084400c91a4280244076801c0c1d00d459000e508110911418401800c0e02c41141019450502d801840c0c41056107405041079214508000040c4107180d82220850041006d10320b032030b11000c80641600c01c01c420180c6500c2c4480500b84070203140d01640300038000b4550 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 545220134 1250 545218884 545218901
    0x30d0210020d0b040906060e150a0311040209090910060f050603180708010e0a120519081e090c190e0708041403160c08010209150c0708070b090a090e03180301 70
    0x900500036045c070b905c2c1102c043e1520b40901001e00071180300080c1d9003880710504081e0b10002400c3c890f03030641542c907003941640d18a02416041a000c2140600a40782c015010b44205410409040c07400f0411038440169092603002c48100744588605006035a26181103940041191035103840d50b02043c1b004c00c5c107000c0c007a400640994a0210900f003880c0000c1201904030340716041680c109403600318107036094060041c00c18a11003001098014042c020000e05801803080c0900018001040d0007407000008101c0c0d2110351604107801c026054185004041600d059501103d00700340d040440b00541c500c8018505001c20074040c1c00b14050003941d0151181c43c20b11407040c0c03035130f905421034482020203c61004a40c1101c01d4240012010700600c240c440c4c4800060840b81d949580c078014140c2078126282d03841d0113025101c8005a034150401c135920041ca0480034036512000010f04110408480c0d5109140250510000401c91103010003140c40071461f00f601c0d4020100d81c000441d005042c1a03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 545221384 1250 545220134 545220139
    0x403051b0109150206040c2c070219050a0c060806181306060e1009020f16140304170606030102040f1809240f0204051c1a0420030d0210020d0b 63
    0x1e424a0f80c1680400d02903c01c0340030b4484503088680e11079500c1d071840800740811104110702078212304843c0301030b02c045410890701d104450400501c401c1e0440b2051040004a0b040d84c01a181030b010441c410421400070041420004240e24040d00400c8134182440050710703101c83d0540006011030180030176610034070303000340d405c11409803909160751020307100b0351b0010078900b484071b000241d81405d402140d0404d40198101410292041c80f00c514410004a04035420030134200d240f0402c6000300301401c001c02e059a4510201481e4042090800300041e141c14001d034010442401a0441c82003800b00721a1150358107240c4900081e0030310003d01408100030241c2c001030303047d100703100221151000c1d0200c28074800c000000c2c03100c1c3c80100b2032069201c0c26070480c484042d00844070301400c03115240c59020303a11103003064450000403240000c00702c0d0b040702d1603070102f0840d65203442e905081d003440e03240907401415408214a8041c0d03a54583d14104420541c0000303940300760041d650014012224007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 545222634 1250 545221384 545221409
    0x9061203040e0f091615120e0133050f060c010209180601112407020f010920061e090d020a030f05121804090804030b0a0e0c01050403051b0109 63
    0xc00010f04140080e9a000a680302d803201d42105600103400d440100c0e07030040010000c0386c03180382d0b003610901103481003c201580d0b180340e02031480000303000e4011903054170b12a60089080c04628620000c84403503610129a840b20000e000d10346606c05440800c940c200d8120761500400b0350744074003901c00c41c0f40c51900501803002d403450100412602600980d404d884098119a9080b10241e40b0080119600102440e0504241c4070403010b007403094102c0d10314810f80f44a500d00b030180d1429a0701013003080355500717607182d00f00c0020820a8005034a541c000c5074160700d00700818184220380c075508284c041040c40001589072070f41c0d0352505c02c8050141e01030701034074181d562402c1110b680e5035940c400b40d426024004415444061003401c840c064441402c144036000c1c910000e100043c48400c4046600080410002c000f203040c1442d074a08c04c040803c004602010016006805d241014031b4040c1404001d0009100150780410503e0781d0740344d09052054821801c10040315188840c1e4010302d42e41c02e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 545223884 1250 545222634 545222641
    0xb0706020d02070b1b1c0b0109030219060e0d0b360609120403030c1e080c0a03110c1305061516050105010e01051309050111030a1a040b09061203040e 66
    0x24442401e40720380400d80101d5114001715801060a115004d01807040081140050b49013503620f03403010740080010302d8038503107860b1668080350070040e80c1d01ca9140541442801040199480a6482c070402d000780c4182e0a005010b175a20b5480b618003034101c00d013034543c1c07060010b802500024000d00a980090b001000c8804111580380c407800c0076900d002c524010108114172086a200440781100c0d072580e50010000d025440748103008a41001c1501e02e000c0348070f8050003050203100076105801e500800b80a1400d42c40c9005080009044808582d981042284988540d03e0903015126003207100c1c8040750540c4c6680c0020000085000303240480e540202d81108510b014a00445159200d000204042d9803540c1080380101000d00c0303030030350042c8003070600c150070f604580042a07520f1080380045502d107007d00700c10405800440b04001d110303640344050003514400000f07503c4092401d40d41003128148900c08500030180045c000e60151020524141c603000040040303800410360100a2911421f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 545225134 1250 545223884 545223893
    0x1d0d0813050a050d05070b0a170f150102060c030604090327051804020a0303050904090605040b09150f0c0a110303010902030a0f0218130b0d05240408040b0706020d0207 74
    0x30964000c0c94080d051800300400d150404d5814110401d40103130082250502c0c0051620066101c01214010010514a460003043c002812a401803d9680005805180c680c3c00b00c60101c5190600504650021083c02910040701044a8210f50240c5002c15410000e08040d20100744489010303181d0020551012862080383c100f0b0010340b001199410074002c10703000d0419400c0e40c251400381d030002104900b000041e00480c004d100c034180181c40401c41e0152074840c01e0450b0412141500d00c0c00c458000c00520303200a1082000010f040c1341d01c2403003805d141c0d0b044090031100408400e40002c2c00501008850302501c00303900780380c0f180300071240e0ba0342e12840217001a40040d00c2840047d8101401c010700c13512540280c3e85da11641041854115000e50204008081c0032121500031390750790000060359445a200203140d241c081c100034249248240c0c0c01d10340a20701d81e091500c11096a1050200040250049904403034005008645a056a0030040000e2140c45110031405100207175940401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 545226384 1250 545225134 545225167
    0x40512010501140315060d02040f090f0b070320090402040b0309010b0f0109120308150a030303091104050c1605010f0c03150b1305061810050c010e030a1d0d08 70
    0x3510030b03c1c002c00c0d80486410900d0350b03584103071010083c1c001004d0001070b528100a070040844500007080800c0401d11840c01200f01c8224140a44203066030075502c0c0d00f4414000c006a422200070300e03040000016a00b0140020071051894511000000455101564840d0151000740c4061501580e0b2030601c0c3c0d001c03d00030309115400741d00803080f04501e13042560060098000700c1c0c0521182c0d0301031803116941101d0240004081d6564001000606580c580340da159a0000d503229440006034600030307081902c40e045441c1c0410b480380381840200005000101c0c156040d4403407080740040c008815103040c1c0d025260b01da07071610324545805510080e00f82d060f00441c80c00320210300b41300c0c0d0540d1901500426440b40e48900d0343c00c030780028400c10040c00c0840040003800403030441c0c1c0c5010341a100000c0c0040c846071035454005040890400ca05250038801c006180c80208003c5180c0300211402500100c3c90340c000300b00c0c0640707804990201d40c03115844402a20307880305044e60356261144a040c0031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 545227634 1250 545226384 545226389
    0x9150501080a110102150c1c0e030904060b04060f08090a020d0819021606050903010b03060703150f060c0b060d021005130503012a02070e04050c131e11040512010501 73
    0x88021003529110a50001c180351011b20312030b1101c012503540c3c030110507240c0d030701403c56503c8080024104402e01d003624480c120641c44900f001e10703030358601c01c4108020780e2019003000b05030000030081005004e4100181951081c0a1f080200c00d981d612018203007411400e51000e900420408020010014440000d00c001394800f040b610568151060880c0e4401e0020b400c0c41d000001d070241031200c14040c2c03000d00031801000700003281110074003004c281071600945858004c03985400c10100c040c1d02d0f010044024142c00d980503101ca514100004102030b110940180a05440d0360104e030302915014486010203070003810108000c032540d88010301c01d5000292110800004a1000c03c0394941809661143d00c1304101059060a101400c152403ca4107000f400641c4980303480000c4032042804002d00c598091405402c0304d6444009102c1144070010140c01803629000072002101301c01c2003038032180c072180351000601c480c7c0300c40885114803468105907030148c800c0811107210801500103505 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 545228884 1250 545227634 545227643
    0x1061205070c02030601180204090f06051017010603020913140601110d050f0310080d02150604050c07110102120d020408071403060f0601140403030804030306061b020409150501080a 80
    0x40e80d40707603a41152007920040c4025419000480100100c0101a00e0040c00d18040c110041c50155100701c4070040351414210043d0194895100b00234601d08810001d421a04600380700c62036440c0d02484450010050140505060b8041190003003510b400600c03070710fa042106010880c80407002040000300504840d8035001664600000d00f2074400030038100503c440c5904c5240c2000340350101d41000e508010a00309414491b0380f000120410100a10010b204054015240c04a010000b12181c008020705440c001c40c01c040c10321a41120700404c540c1c1e00c1d0740141404194106940040341407010304040c0d0035a080b004241400401c1c1154010012100c441c0c040340d00881d914209030451121029a041c0c1c50b401400c001150700c00002c40d81d5a02100500d410b0752030070140000098aa081500103500041040d000c01003015054817503080540441c1c1403101d070540b40c5226480d4102c6a002c40240592b8a814940301008400000c090000d0701c806014469580c51350041580c0740b1040c0d8042e034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 545230134 1250 545228884 545228891
    0xa0b0c1e07062a140318072403020307050a050a02010b130e01050a0903020a0b1b03010b03070e2d0301090c090e21040302041a1003020a0e040204140f010c0506010612 73
    0xc2c403441000780c1c3e120031108240c8401c0d10368900030b0948a019040200803980282d0b0307403188042282d00071702c965000381403603c0c1c0d030700c9030385084203a903e03c0c1c03104142d9503d0915204005101000d900002520011901c501d00a030baa00c218200072405820b41d1205d8075044410080340402c60190b64000c0f0303c81140384402045036643e200c159005441560b40090003582043d0364010219240341160b03075000300b206c80c03001144004400d030f190165000742d0004004000201c18000c003141c2c441f00840b00500c003121440c0c0e4071906402d24035040304000c1882108035441c2411622591020340007038000d9a0014950b0300c0841e0313103100200250030f0745901400c80303000d0b0b91810000b41c9040070805100a56100d0350501709070440e42440000c02540c0c8105c2c6894445003404400c035901c00c605542068200c0da005619400d04800c081d08000041540750711941c0180000d1050381d04682034201000c1b000c942c0f4500300c107040401030b101003a1400c2d0140441c01560004262070750001000c4200d90042c2c9008c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 545231384 1250 545230134 545230181
    0x90f0301090c03170c102c101d0604050304030606050a062f061005011b03140d0e1c090e0115081b0c010504020f030a0b0c1e0706 57
    0x16080740c42191006003992440b00050001c035403440003c4001ea4800d4144500d084000e00d1040c2c0b0300004242d24041481d150404a040c210350040c000b1074845203201c0103d14a48417640142c0c9840c541111901d49a5950242146034005807141000814500090300c8c0755040a041207612a0701501050b60054203041001850b801c1030000f0b10b044a08070341e110260312104544611280c40c8010891049840d2002074171103528040c04541d0007000b0310300640c40d03418640720003d07000b1a0b0003e910b4620140020682c0c020a0300542c05c0c10541c1e0f42500c0007a03541d00d1483c1040010448000e001350395218065a4140c0070460000d41c520303004840d10b0f42068039a43c0e4440ca9540b030424000c0c0b003454a01240003a4066000b40710f85500041d1180044c0720304102c3d98558082c0303410083c411403c9a44a1080c0020350410603001134921400b5005402400a10340301d1105443d00680120500780340002d40a050782c1c0c1202c0f42105012030018441e03601d00031350820001070880b600103440c2d0f070140251517 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 545232634 1250 545231384 545231389
    0xd0305090a150207030615053303010812070c0f0e0f090a020f3007050a050301050408031605040906090618060302090105010e0109080703081e070209060f04090512090f 74
    0xc0b1051089503005142550070355030b5550140c00d282c1140b0704d0303695130702d00040345030b81d250820701c200543e5801c540094409650700341c60340e080d2031305000303401540200014000d1010200d003a0703103100013902c902c540d1402d05140032004888642e02c01c0403a504072210101c1d4481000411a005080301440c2a074941c403848106a111400032030000d51294850070001010708007050443c0b02044580301c000329008030741c421801d818080d0044500d03035411083c0e051060349000d0b0f80a40160400354002c0190340781c10f0343c0d203801034440034084002c000d50f050700b4005028807400c00c650144c110031009100a641d01c1162340094240d07400b40009080800481c802178503034500c140c1c8101da800404c4144164a480c00540718500400d011030b04200d4000d0000c1405042002098011803182424564610200064950b05062608070609d03641c2e00704405000341e03513141d2019801c850b0842d00010032149490010b8000c0c049094002d101e40185c81044445503000e00182c141c0d40026103c400f813001501c0c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 545233884 1250 545232634 545232659
    0x41e031e051b0d0605070e030601080132040f05120c010603290711210406021203010b0712030e0a0b0105010206130302060a0b011b08031b03040807060504060204050d0305090a 77
    0x42c5580201d070210040c004625aa0802d40e040181070501c0c0d01c995000d900800c3c00c050b401d070014000c980d182d250002604120200c0804101c103111001070394408840c05000803208041d001512034051080e0480c248101801064072078000f07032000a941c1c1d002103c0c664080c0846100039501000d102240e80c0100300c0ca00b640040d013248480040a542e60f560b841910032100c0d02c0c201808511810303620101070419403541c80980108902d02c01e44451408800910341102c51850b904044000e1004101e201c80341c2d4140d0b0325090380030104141e00300340c0d850200c0060402001d81649071041c4500401070103807100d5414140c1c0c20071790136201c1d15911100000d1250584010040c01170f03014134005040c01407070341d001c04a8075805140c40000340c030201c0114a4030800d1044140c0c0d0022001080c04090220700342d40c1c91208290041450640c507040e25000150b0050303070406400b26490780001001c2290940c101e40c0034140041c040c090b40c1c1c1190400070b100343c0021240302d0155020741d1002c500c1d60400d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 545235134 1250 545233884 545233933
    0xf0e0f0601080f1005100507050d02012f0909130212061e0c0c160608090c0904032012040e0a27170f0c150408041e031e05 54
    0x211140e10b03e44850340701d6101440d00409860500003c1880070880d9690356010301c1d8034061940e110798071900f40c2d003005401d007070341c0300c505105581c0360111800900031003210000d0802740d1b905040c038040300d080141e044c85104001c8250b9100b159181000300c07180218044540117030080e0f41c912025a54161450340c0e5010540d00c034402c00c4201ca0040000762040d045181c0e0003052240406d04160240501034601032840c491401c1c4403280000501c0320380e0b80409000e40c42840d080082100c2c036040f102040f107007031010744007404014540503255002004c03140d200000c8940070b001c607103c0c00c0b444004101d843d0018000c440c00c01901401181030710301c0c80c1c00b0303051542c40303400c01c0302c00e2501d1101a02040d610490f20708641c2480c06a180c1401c000d40c03d0301510f10550350b100762940e1843e4030040581403e51260901418407644070500c00803807404801d80e000d4480c0e80e101402c100b0b211304189182942960301c000c101c10025025090740c40c284650810116200b8012200b8005515099540220111 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 545236384 1250 545235134 545235137
    0x1060906030b032d0a05100902190b0a110c03100209040b1e061e0301030506010303090602011e0506190b0a09120506071206030b07081014060403080d11040f0e0f0601 73
    0xc00034503041c80a4000f00301c0304900d10400c545c00e800d81995501d08000302000003040d419903c40600080d41000070400e010b2618000031a0760540c14081182d59901031107803402c080100c040155a0107000030881e4420a4200504481402400050f00c40c0039500101c08a0b000700c2c01e21540c6110740c24250160904a5082d0746008040c0080c5014815075030801184c48810380301c060740c019414100c140080d406140108060f103c07560640c14050902410341e4042c0c1c08582c50030305c9984d200c0c0e2812020110080f031110002c1842c4d120300b00014040f0031050301c6403520009e559000a46020404010404004c007601d584040f0380c1d40703411071021850f0045014007107810070707400174030405d10070888043d2280300254001010361b2a2348410030520404c5840601088541051066040c4098a42001413058400384440129080e02003001d5000d82d102c02810038801141e0311205600f0743e0414110b80d007410007003544803aa02c100400d0601340a04c54200308414410200e0400980420402d1007044103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 545237634 1250 545236384 545236423
    0x1020a0f06050405010914030d0b010e030c040b010210150f0603060806040b04061806050f061e010507020303040819140303010303050405060714010c0e01020f0d0e101701060906030b03 81
    0x35101c11000e010002c108030740300d55a07085e4510029000c219103800c101500700c02141c803001454541c504441000c0e40c1181400030044408241d0f036400285212280707400d6801094010724200142e01d400300c0840e40307404103428902c0042c80400c444090504656a210742010903a07510b0400f03030200d5085000b0311415800480018010810122041d5002440349400042d010b041d16110031a544414408950030703516003050000c80c24074190480c0e04001d04507030707501c0402c0d403942c1000c581c2e44c2200042414440d000c1030407401d66030103009076402480940140d400c0001070600c0403074449262481107440e111038440000c08c0c10307800010780341644d030705840c0c4901e0309041004000e26504101e40c00c03140c000321150f0129040c1c10178010a0090815902d5031501c04404038006800c01d5692000900039a02c5000b4075141d00d41c3c0580614080001030b104103c040c029808111045042001d00c03c1d4042502c60000070041d0b840101c00c41207407030742e0f0780410211003070000705903e5000d02901001c54888 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 545238884 1250 545237634 545237663
    0xc0f060804030f12020406080105130b0901061119140d0503150607140f0601060e090603031b190305070b07110a150204030209040f0c0b04270905060f0702010b01020a 73
    0x43c0300301c0100c0c0082c0781410041000750111a60680c1d11540201c000a0700010041182c0c0c1040f500745003100600210070b01507004010081002d015051050404006c0e0503500300c0003ea20600460204804614145d0700030020382c00c0611403200d00c000507040134410070401e4000c00c0e104009484c00b6209882d030042c13011079281c0800c44550091030050b1644808e000c1912420034040160141141c030010181900b503243c458090b15907603440c80705e203001e5880c0008000045e5408402c0762003080b49400c1d814240304120303900515009080c03038041c200c1d407031002c0401c1c24960044090803c0701c5c460f40c0051402c4e680c00034100c810030008880109581e000e20000000a024600c0d8a10320700c450010041c1425600c0c2c00049510b0300a82d41500c2d140800c01e500c000b13111404d902c0c500500034503803502d480c19151100c10b128018941c0c07107884450402d00414083d8601d680c001c0d85006400900305d03142803e104164003009038098548002561038400c05808950000c141e80c0e4059800500f200311244 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 545240134 1250 545238884 545238887
    0x14192d0b0a0e0906070c2a0f050607030e1509130b09130308180f011d0f0d0503070c05010207060f0209010206011a0406030f0f0905070e010f030b2d090a0c0f06080403 73
    0x48070fa030000c480300008019040c04107610a10344605d0182e9408a0b40302c09071400c0c040e80351b088c5161708200c0c01a00c0c100240c00219130031200c0c5840c002030a070340c901510080d513940041c3c0340c000d031081d25901040705010a034403035403a13401401041d08111001402600d6285000a40c5650101d004021400c50400220101c404503510860380300305105650200c0b200300c1040b401c60f0300060b41b100b41c010700e214101c00d03840c004100703641034202c0440041c030100005220107411404002c01c90010840720041c600c08102c429016a0000c07a0301500502071031582232142d5000e9005021424010702c9807200003e820303902402c2d0101c50b03038a9190b810b46001d00b001412809030825221900c001500c40c003d5071050320b0144150315042c0c0c00f907000b401c8424101f1040b801c0404040e4880116075004600c140080b1b5029a03c2580251810800103e4803144400c45201400d00144000000f01c15004001c41c107013000c540785010314880c64051841c151909009002c02c405405104001480d080010300040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 545241384 1250 545240134 545240147
    0x16020f03010b04020d0e0705030106060e101205070504090f06150c0503040e07020307034a180604061d0f04021207030c0914192d0b0a0e090607 63
    0x4600540007160000302034001c10183c0e44001601c014140e40d403d0f2501181606010f00d00c00382c0310450080c00315a24089008000080901c0f4592050030495020101c050003000e4120355010440c100384264940280082c105030024070500002d42d08046074410f01844d14841c9000b56860041d098010b041c1300c800071a03000d050743e4011101032000b00004905048801000c0b4801d0840303070f00840e03440100e842c1c01080039a5040c1441c042c4900341341c030703400001c0310b820340034401c01e5007500c110b0040a9020307138100e00701e0780c1c0e4246240c2007800020704881f14001032014600c55101a542030096a6850f8154a04102e4240d20f40310790401480124440b00c0c1d80114080e00140004d000420b100480601e007130038041268800c071118000507204115a400a002d4070030f59040c0800d02c0700f840d03d4940ca505400050040071407541a94541c684441c52550748501c01003031607961007069035a151910f540c40100500d100041c81882c40035030000e203c030b001003455803158419030080e00b02d40e219184140c0301d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 545242634 1250 545241384 545241409
    0xa090b010c170c06010e061903170706110a09080708210d060e01090903090e0f1605040f0b04090b0d0c0e07051213260a081305010e0a11061602 63
    0x214041003003403141103c3c2c01c10159002e8041600c1d080a03a080c03080812046c002c0c6034104074441c0913800420400700c0c01805c8881c20b524141c0400503038411182c60701d2401003200500e0380c88019004500000740950100c000e0040e0b80e20401220304481e107a0705031035500c0f60952820f081c22011a190042504c0c6c0764006003020f6040c00e500130481d1030315146104a50342090b004440c500d0303610f101e80401e00d984042080010041186606110f04040034510803020f001004500001d0880c00790740246440741d400c95005107992508191f42c1519041c0b0440c00da031061040d0194182004001900ca01d0000105000c10340e0060341000120310b09000100ae4020040095040c00401c1c49181124100005128404c00e0b0017942801e9030081454907101c4403a04c06440e06100e030142986203c2204000c0c11240e420095080c003150907596a0214448a24902d800400a50809074094645080050805841441480340189074504102031003010f00404140d0506240180d056070302604208154825 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 545243884 1250 545242634 545242673
    0x2120405040f0605180406050c0405090a0c0e03060c0d0f06050120030d06060c12210b03160b0408100c050904020f0d05091f0b030a020907050c010504110a090b010c 72
    0x307405135108001040700030196826040720f2408402c00003040300500c0340b00c2c1e11080f2a00254182420a07002c2590140010a4207007400e9076070700b603000f0950160b60090f00c00140201183d20528150002e042640c2107a100c00c04950308100c545400030310341c3c2c0034040a4850603034542e050303410345000c0703501c017000c0b20000a4840c1c0410046908030141a005c0d400241140f45c5551b21036204920f8601d0601d401103e035541040401341d008003e0102c0159260354402e1030f4040850005a04800281021914001040c044044c440001040030b0300d813000d002181d01c0642a5001203400c20034030700a0710003902d040000110200b12442c0b035868240d015050301203030500c0450500100301500000c5072000d076074034401a40a155000c114011210741c10885440c42101444401c6080f008242d480340203410082c41054840002080c0030300c20015511103420780300080c400c50419040c140390041400c681140101480c004c0031030302d801c0394021034030030a50680d58000000042d0b2548a24605c3c10100b049 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 545245134 1250 545243884 545243891
    0xf0a0b0601210b0a0b03040201092d1805070906050313030306091d0f031305040b06120415050609070503040b07091d102403020705011401120506060102120405040f 72
    0x21070071031075480544940042c5400003600b68900010002d140c2901d51000d032003030707000f00f00b0000180d0b400b070602822996192120305e50325654104801180e0b0103040b20241210940000007062005111411002107002108009648482500b1142c005090182002180c2c0403c041030a021803407900e10b5030360f4000c0c40c0008070750391120f01c280140c07118208842040b0b80083c00d46001c0c0d010501410641c0389040d03008514003011a030360600300b06c4291003101e1003180d407070807040e43e07549408084440848088001000910700792034080d40600c50b5408901c0c12500d01070002e283c47c204440480d020369000d07101d5138255035960351142c00358032008080310f08001039094000795804c0c8003510f007400344141200d20060303880c040d00003500e03030190341d48420088003003190a80ca10311448410404d080c692482d01503550501800c05601500340c0d2919981c2848180d400095007a0034200c001014030310034800e80d5003d4468400480e80c6000001d1040d15581d0101300408c01c900d0107901041c0e05030303050780c03011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 545246384 1250 545245134 545245157
    0xd0f0219120509010b0a0e0a0f060b0a020607030c020c06090307030b04080706050105010f050f3a0e07030c05060a0207051c05010b0d1e0f02060403050f071203080c0a03150303021c020f0a0b0601 85
    0x481903031825802f40620071008216124200e406000e155803001252904110440c0f02c100c00a60b40c0007420350650048600103000001514107002000c0950b4003c401070700349044c5490201c43c60341c42080195241d920f010001715041d80b044080a4072401c0555815040642d000c1313000031503520148070040714184075400c0440e807002030000c03180d0301b202c504080b5045040842d982820355006081e01c0b00c0641022005000007028815943c8c00d4030b406480880c8c8600e03034802e045e490300601d42c11a075030007501080d0142000d402c400f42850300502c600000c0c40340c0401402800003425460300000c00ca01c0600303455501d02d03c407400c50840c450b80541c40513030380711019030003040c015400b54105a90940180c80c20445443e070401c1410300a00001c040f03110080046d8400500300100a081c000d020079000481e054014803d07007000c20710285106542c4245039591901035030780c2c0300600441840327444160104203402d002050291400d111100900312400459030b92280d009401005581400b0080c10790 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 545247634 1250 545246384 545246411
    0x51e0a0b0307020705010e031c050c010603050109060b06070b18030d0509161e09110409020d0b0f0604030f021507152408030d0f0219120509010b0a0e0a 67
    0x800003800029a55a81d80c20b107001c2c02420404140c2003541030100c13004a080d10768a00054501c48100c0d100c031400200003020b142146c1d1480b6074411615958200b800c0801800019807146a10314800d400800900600b00e084c000c0c50f01030b20302c02920b20740900340050400600d002d603e8641030290400d0302e00d0108641038000c02c81d04191a04d41443d40800c5030302d54201c01007403111010b008882a030007540080641c0a0405039501d000f61049203881e100d50070329400c1c80c0c00685014000008c0300b9901e40314542420b000910740e40c100c543c42108081038140b45400c0203030849098030342040e060640f2050079000d020380700c4203a25103030076084001c20007680441e001f03003048080000030b80c502080303022054010700802204900700700030152202174104041d010000840ba2141c3c0c20050104a054280c6030b240001d010348800300326422007040c81e003440980d105400c5208410940401c01c400d880c8c20720910300300c40042c0c001c1a0071425503030040c40b41100140741c1c1c59110030002c501203070203140b0414 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 545248884 1250 545247634 545247649
    0x1204060804020f0d05100e0109150f150503120c03070c0b07050d0e0603070e01021c0509120c0d0807061509020702040507020c100f1707021f09030801051e 68
    0x4100000c0114007488114070785a42c4001100e441290041c100d1040c0d03458031500d0f90305060102540c2669800d80e00e0760b0700429080500c596400901d0076130740754400303080d0501401d04070900a18041c90001c1c900031041500c091402901c1028004000b55001410b400c891039104914a5015110a214640001c0c40e10b52541001c0c2a40d028001d0f20307013046180181c5810b8840c0c1988003402140301c9203001d20b4072442c0946c0d50040c4140340c148044581200184d05102c1311201c10070182007080c44249440c0d401400821300d0f90015101c038916030555102c80c58492041340c08560740880c959914070701140100d005800c015008400018030310402c00032543c903074681d0303a100c1e45280380c002c1104410362910b44a0603a01501c00d001406d0241e40400008520a50090b041c100b881020000c81800c54452804844400080f16020510b4140100c000c0c1d40c418020740f00010039000c43c03000c00d0180c082801030b912110350648030010140d081000300036542c0d214182841c1060640800300d0381c10344d152903 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 545250134 1250 545248884 545248889
    0x90d0503160309060809010c0507080a03090636021806060d020d0609050c07050a02060a1103042d08030f0703120f0b04061703090d030908060405031909060e01111204 73
    0x315121883e034608000a800c8650040406116914065518421a40000442e112140d010075100c2e618452080141d004102080d00035201380c3c54070565010101d00c62514003003940c2103541d800303d12132100f8525aa82e0403a0317040217410050410028201071260303231078950040b44c0105501d04008040c18800c080381c000d449200c5030261151400c00440e081031040d140c20001d0003510a2a2400f41c0d154180d84180c0321750024002c80000610b07104a03441860104c00c050b030518203607076503103584a6641e15403842d1602540c803800030000e550841e80c190810510304940c100c40c050b42c200300d6540200700c4680c01c1224294140413003014000f102c403001d80300f541040701d2220400502d1750034980520088403140d0300817024902010540d081091000401e8070440402221900c409000915003210200c604d58492030003441008140700801c4004000782c0001c2004911030a680c5c03100c120201c482d5103040c4544004604403030b0348030303e06512503d500444c1c0048201103503012000220210000d60099 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 545251384 1250 545250134 545250137
    0x120f0d2d0b041118060409020d0203240d031812081b0c1e1503271605120f030d06031e231005070e040507080408090d05031603 56
    0x10184062503030080c85003000c80034041d141048045146240228940325501a03402d0f06014150701c0c94441e40c491045401034180f0403001d5468034540544140039400584050041380240c0c0001e000d10300605180d5014604010400300311810151400c0c1c0c0c2e284102500d2640c28031001101042c0d620741031107201c01d014494089240e44000309080d101c2600b841c04180c80300ba4100501d1300f0100d41d14a4004203d001d0452807803406440c54000042c01004030641a0f02c201901104100070103003003c0e4407034500c0f40c000c059480b42000140301c42d61588100c003180c025000205c1420302141c10820444000d92000a04485c80004940c04442c40c40c3c021150408081d61210400e00400c03084a12092507545488010007400d2029034400300d40500c0d141c01650450701d484880c0d40b9a83e000c103c0c5514280c40d12004103c03504100700c008040c00c0e0202c256501444c104008200010f00c074180d183d01c101d820400e540c0c281142c45c801c2018026802c40182d405100c18040007885032031350612541c01900c00e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 545252634 1250 545251384 545251451
    0x603040c230102010c0f14130302270c042103110604110a0512072903092b020c09060a08060f04031710030201050a050c16031103120f0d 60
    0x11900082c02e40318141e0b01842003250401d10034682d9600441d91f00c0d50b2550940e802d5031600c6c82c00203d2200d5103120b83c0b000c0d6100207120340040044000880071002030f8602d5640c0346050780c0c0d549000d45541b2442c42411104071108801c0149002e0081e80025032a120f4035204440c00003074030b105480c088041d18141d0740c4610100c50140c0c10b08d00307040c02d2802420300780c502c600d1014011100c82e864100c0d03841485c051a2a000501c0780c0c4010046800000b1410311041e0354a0741400101030344d0310110b03012280c48022071400070301803078041c2075090390071b200702a8014059202010207114884001500700b035042115110082841c0e00b041c802c0c1c0d80704444030401c02e0501d00d02810014860403100b56103030710a02c1440148125610f00342e860b0403e50b602800d216a2314501c584d405c648a12410030409218020b0780302c110410820207400200701c1e400f8201c04012004610f0416865003c40b00f4401c105080c100308880d009180ca002500c85550700707800001d4540c0350021421401601700300e94000b025403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 545253884 1250 545252634 545252699
    0x70308130e09070e06220e0c0d03030501080118051c0306090f0203042001020607080405031c05090c010302030c070308060a05060703053c0310170c0102070b0307080103020603040c 79
    0x9090000c1c0e8810703003c8071b80003001d0019031180407501c0301da5041948000d440d080d006d0080340d420414400400400303402c040c101c030b12604000700109028003400589501308442c0c260305864143c064070f861034011000c0c0c0480382c985201c240d842c070701d0030703a02c81c081c5604c07051300146d214424484c00160600d5140e015940b8902864110f00f002503020418440c03900d02c0365020340d40d036400501583e00c00c459060400d026216820860301c0d5004050903000c01502c0c1c15102410020680c00c003e01490181045505d9884074500660a03804221a1030391884010b1003000f01003440341c82025013164005d08600c80072916200818181d030f01000c001c4c0c0102d400026044040d09009812802d004200090000d01941400b5a21442408982102d1000078088049810140a07139075100c0141000c0c281d8071240c04070f036200151a441d500724100e015003d9800c0c0041c45c0c42c49002101d2161005949040c1d0f260300b103034200081c80c0c00150058440300d01160021031607801280380140c04448080d0744203201d030ba = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 545255134 1250 545253884 545253899
    0x412030e0a1a03040609150618050f1302040212010b090108090d170a020c1c0f02031207030e03070c090b0a090903121a1804060509030705070308130e0907 68
    0x2045602240d000707400d280c0c02040281880c122020421007285603155036500d03503007086009805008400f6042280c0c000101c615041c0e00d038446001c607030301c50b48400d500701410310150088030001c495890302800103600040250070490711000c19540700030001030070029420552640745a098201c020400c2001821418a40e000b080407648600390304001c0030f180c0a1054014814103040610301c241800d084040b40714582c203501660010181102140c8404a8105c54054084082c0e82c019010658600c030114030341d4408002c88429022042c110b0b10103450300b0783c08070300611105d050181c1c14001032142d030000440441002c001040250b40100300d80d4840820091a00d1842d408841c803d8541010702d0b001a4001466000c140c1c000030f0001419a6803d20940c003a040003180103500c0501d101c103040c0c184010601c1d03140118061007040080f940c550003010750381e210707010018103503900c004000c00c001524031006100805a0040304500c01d662418414030407030b000e031131410b07464001603820700145 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 545256384 1250 545255134 545255147
    0x91603060b0901050a0b16030912050109140c01081b12010e0601030c030207111e0303070807120c080708071a240109050a0e0405070e0c0a230301090b0102010908041203 74
    0x1010110f40302d0301c4a1b480d10360340098511a95400340003010360716002c002030501502c0e11a00400d4120900b07401000c0c103260650081500c40011100400d1002c0b0080c0c182d40700003425105100180c46e01802502c0783e800c60508140381c0960050401c6e0100b058066281815905030700030b000741d160651540c1064000075040d60205141c44c1c0c00c041c4144560000300b500c0c207000c0040290166042c03c505c4908005543c3ea00351800c26032901440009800d01c1008005001420107a0051545104200303098108840e03119940707402401030a0240042400b041d807010040c004c0510928201802010701141200f04d03080459040392a81303c0480c41740501c4c0c01e006c03841301542d0800d19250440c507003440c0000700019118044c100701910141e00180411408010716405008041c00b844111f180864807080c803035014101d50300001d03100c1e114124580401d480d44114204150050500310703800c001c4c49200801e10302000e541159240c584036800b040c00d10340180b01400611400e21070715139450801a002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 545257634 1250 545256384 545256389
    0x2070821061e0108040309150903060b06030f1b070f03050702041d072108030a05100f030803070305130f0b0a14010305071205030708040f05041d070509091603060b0901 74
    0xa44058202096600001d0032003005142c824201600341d40c0316410308503030f0002c85800085002150009222a80380c2041184046910894081c002e2081c09824010580825114544c0e1640c01c0e00100b4140c0080038104014880f440e00d040381007030002d494004000401e4002900030843c002060400c0d418907008840c40c1d24003018985040f911030510750f6030713100118450b91440030b15100c44d08a115202c105200c220301d4201c4102a283c2c10b0082d100780041c030094840524140e08448005480d007541c11181041300e400c211498150751751b000b4140c01600d40106841490503101c989240021036800a108105000340c103900080d01e4114a081c0c01c03580401000c12404004800400002c0c0c030005200080c0c403400080b140800c41240f4185242d4040c0b074000800c000b601040200c0d14103002a450b508641c07040f10140b1210950640120b0055880e80b140c0c20315401040e400e0003982820781500d500b02141c2d81c1102c0c13a204144000d481a214242c104171042a21000c80c2c01281c60100c0c803c502 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 545258884 1250 545257634 545257639
    0x30a02091519080901140903041e0e0109050a0b1809010b010e0d02060c0705060301140a0501210506060d1a030c060a022802060f0306090c09180a0207082106 69
    0x90141581c290595010812541e2420481143c000540c1c2400c2900705030341d100915000c0085034103204c05a40c1d00e0781c02600402c1412102c1c1c8000002040c04412503000300c40003203064140310307401c04d03005002401c8014000f4446c0c544814501160b6190f4500b05031000c40751031582c050030700f0419a01800d442120b03070394070b04104100c185285147e03140891048810b50440f08640d40e82040c8040c0d0381000c1150f8801603100001000005044407110700380b1174107220468070021525101c00040d10070350f0201042d4140350b91101c1e00c00310820919802203400881c01400103040c11901010702c801d41d41c1d0200c420042c84555000720007030703050070052000c64150840d20f19050040c1074400a607030f072403e41c4400c40f08000d4440200d4040c042c83d2041c282882c4c000d80501e0362440c800054071440d81c0242c80440c010010f030000118120900820340b00810801400c242030b140801d082840d840e032000e0510b042d041c1d420068040014100d400070018078151aa42001c45484204521142c0d04010101030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 545260134 1250 545258884 545258887
    0x5070801080d090b0c0c030d0513060813080a170109090c090204051008070912140f0f03091509040e01090311120306041805011118010c1e080708030a020915 69
    0x6040d190420102c1d0140c5500c1680e1030740303400417800c2162801500340303001e81e01030085000340c800c902c1c2d00c9001400d491162207031480701155650012200b000f41100c20303420030302249102d4070005580b00028089004103242001110380d0107141001401070a03801b00d4100c0350b48180e540e04101080203001d004252103601182880e20302804103011290070140401046102d10020b03903d54050440c40b0080d142c0d10355180b1502c1051714100410b08021000c02403030380305141130410b032008000340022807010001c018508040102050180d038582540b80c0b120716020034400c2c4442c0313480d03500c00d955a1500ca0400850150b0b50740c203007c2d005101075240e84419030040889494002840001c07681c01210a460000d00c4000c0488100c82c04011100c00519a5080c09410240e000354400a4071f02160034000c4040c0140b9400015248407104d014000c2c441210365150082c4440808902d261560042001910b4010965150741c0c3c0c0f0790084401700b20b42c5a010406007014204a80041d0b0201d40400145 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 545261384 1250 545260134 545260153
    0x6010602011a0a06030902060c01020f0a030e0d0905042706060905070f08060d021807120506010203120103080d02130605130e040b130302010b040c03060e0717070f09051002010507080108 82
    0xb0f003603503c0c98003820f000c5c183c6600100d0119264007045401140741e000c000c54681c81d25401808283d0311862010b00000e04240a050303140e90045903144064030745850b08500325143c001444082c0101c0c24845d00d0643d80c55100c00d2440c4080069903203018414600018018284000c2004030b80c80039014404119511807407c10150b00408226001a02180c08148074074961000030445070701101c08403450031044051010242c1c121380951904102d4240a100750341e20174004a940e40901c80303402c00c1044d0780e000100045008030004107408002080050700d071002440c000c01d004151355003c80c0002c1c02c000f4004904000042070300b4045e10f01c2081c1c56486003001d8449001c03140010307000c08030f0300d1303140803a15080500035072043c00c496101030424420b11000c130314042c0045c04c0307611407a0040d816010028107898403c1002e134040c505c8400d90402c441c2c030758440480e038120103d00e00d0014008540804522070741d07106045100703051581e0006c2024a4948401002c84a040e440840700b94040c4003079 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 545262634 1250 545261384 545261389
    0x10e06190c020d11030910030b041a0609060315031204080601060813030e010309020a3033020403060b040b010311040b2101060809061003020306011a1b06010602011a 73
    0x84603e80803c1d803801d40140c8648034441d034158440e0340c4405a0050b421541010741542681025200c100200c0e000c2180ba0b0341c240d01c505000240c1052a50b02c8807081103500c1413807800c0009544c0101c20064501610403e20010070b00e810514644008065000300d001c00510208104081c0900340760f190050b00b5003015480001444488400102131041662000d1110792081d400003844a8000301328680e100d40e11a80642c0c0d0300c1110661003c0906020300300c0d10001c7c20091502e8203140e110821420000e00e000140000c221050102050503401c0000d002c5000614000390010358000ca000003080f40341c1904104c00c507812480303024145810b1080754500400307110240c4d400c841d048011603031f0b07a10140c5c0c440002c1100202c03540070014800f0001040095201640a10420080040352503c0c1c4400c0101c44003903065102c0258140c4c0300b07000500920900c50600400382c070144042c1820050051102c51100002801c10b0b24180d0001e00108659542401181c0ca10b180c0783c180a16010340f640301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 545263884 1250 545262634 545262643
    0x4090c05031014010807033b070602010513120c061e05060d170315031005040c0f0f090f090f03020d09060f050322020d06090614060609010c0501020c010e06190c02 72
    0x100c0d40a26940b0480d5400c0034951100a00144c0c4014900451180c030030042072440c100034900f8008d103407040e07000129030701340140314450150007444a80e1030500c10720313501c20501901c1c001e851001c0015403d00071001501070b000d0421181c94070790307501075030300c030a603900c10101c2300c0003400b062080c0302a00bc0840400c0c90b0010742e032001e9001d017120b142e0340d6581001c1e003403800c7e40f5880401d81501ca04c800c0d200302d10000394480381c01203201f03148041d42036a560310404187c0390b0a000310303400d2402c80c0314204007114150384044400c01042d2404220420141c8596031587c080e0320302540942c001c0d61040d01d40c10340c4888408083d11302820003024400b0003082c024020b00000701078400c0410300c04d0300d01c00d4000f85403002c4880c3c20740c001d2000c92600038a18059028209004048400c2170821411040c28145c0d0a006171184070302070581c42c1002c2000004564041c0e00c1307901543c0c81d55003000210070700002030090000c248e0110004100a0907c40e00003803920168a1040103000e181c4146594556400b09 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 545265134 1250 545263884 545263891
    0x6040605071a011512110f04090f0507090b03040c092307030c022d2409010b0f01030209180703021b0703020102060c03090f010501170c0910091104090c050310140108 73
    0x70301000c0c034610f1490010020710006c0703000d01c0c0000300820034000030403203000140152400190140929a4003060000517170b4070a6404202003054501c05010344105100510740c41409203000380b01c1d0a40d240101d000f11051552000740580c0c02090030140b4002044000d50403c0301842e0030003140703118040084d00c51009131741d95400310b801041d40c1c035510021942d06141c0d1500c124282d50551001507410f90079000c41401051800140303000040c82c010341807203900000c5001401c141c15a9640900441c003d5002440d034640c407003205080791154004a20b078591283c40f00d030714010782c0c0b050700750f1402408500400c0070640c150b00105007880140da0209005821500c4102105d0b100d1301d480400c43e09001d003d03001d00203290318110002601c145800300c5810310250007801d4401c0f010300c00040c0b25448001b01c82c0f00951460b001400c00c40c4800e41d47c04420020211070980323051170b44030841a0140d41d8031100e00c0d00001da01000340402e20200884410041207040b10f078110b02c020680010b456104001c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 545266384 1250 545265134 545265137
    0x318021509041112160f0804111f0801380915070f0b01062c030f0f0604031115040816050d0801030c06021b0f0103060506040605071a0115 61
    0x110300d00c01c05840d80d400c25012a41045003003600c2c2c040a20211081500480f48100008480c0c00d0031036009001d042190220062580d4900c0035a40b16103c0d10b81c081d4620300c0e0b2a4109202100d0111842c0a00780e0100c10000c60b03a0703e5203129403400c46030800440303d5010411503002107407046640d4070700e0b10409140426a8041c05521641d541d030005099010b00241024044c000048000c2004008032042031b5041c801c02021010f039072244800c0b0b8111916411207106d4440402c49850a0348070403d0210b50050000c04540290080c030110b141444003200a80340d05920600611040640142c041d09c0c8540a400080c01700c920715102d501200c0f88040c1c0003400c1d6010004000c110010001500c0590310b4005084072001c04030300800400d160303000d2100795010412004046002440842c128402c00ae075150b04840d0380c595841017081803060036809a0605964000000b40c2c3d403500d2000d4001001c803511090f40b43d140c9401e14807055151502500040d80c006401070012406500040c003010203075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 545267634 1250 545266384 545266387
    0x10c1101020106030b1911180f0f041109100513060806040f0c02060f09010c0c1118010f210c091e05330108072304090207020103180215 60
    0x8400140d00604103908080c0050916108108460003842100300309101618000c02c262080449030040c54024035551694201d002d01040708585044410010054001020262500c001000160403a103c0d203010000060700458040b04a180c05980203000c601c00f400e0007450000a0b2102460302089030040d50700384190b09001c105151500d034407045c1c2c08842c04c4410850000312400203075072024103e464030040e001600c001956600c0601441001c08026100d480d00322944e507455081c40079442180079003210541268186010b071030359085008040c1d4402c050482c50500c1c0c6a81c46108080109044001040041d40d00041400c00c040c021140c5082c0f00184c1c154468000b03001043d1807114440807a03003404144006200c0c1e21400080c010f41d8154504034041e110010600d8042080c07001c5800b00b04040000303607007203014400c2440c12204090400407903a00786c0e04c0000107074002d50040c40c00258080343c85411541c062003400000038403c5000300e20341c0f22613030004a89400703001000320501c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 545268884 1250 545267634 545267663
    0xf0a050a02070918050c0f09060f04091a060117010e060402030a02070203010c031e0603050d080403050d05010e04031d0907031e060b120105061606051b0714061005010c 74
    0x100340082c0c4064003003040300748400c034110318110a80048081040c0e9035806a81c0f00340600e4079024252480061010b0b020b01e407130769165000c001c01070703242c0814150415103034440c007000540526849610b101c68140300d0780c91402c00200042112070030f90b1038041c070040322400500c00f4540041c007070340d8044011540965a0380d9141080d0002c1d00600390001e4241d0b0801070740a030507a07055008042c003600360900c184514100100d1240c1075030b400c0c2c4000b07440764028010680c1003d00c901c3c19168002d0003400c1403450b00803201401003c035902640151190301009052000705a4844000442d040445030140081b801e0940002d0280c2c2d8080c19200070f00d42d0f40c1c200e84030b060407089040c00c1180900c1303004000c0c2d15030360104907110b43d001084c3d12049008403c00850580360500c01e903042101d2130255480301c0042c42c1d441070700400018090b041c0100e103a001010b1a141071000070403490707210707890702c4069000880d9020f10345240a040b03c010000d040f0400c0c401d9907130100214103825000b119034000d010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 545270134 1250 545268884 545268887
    0x30301150c030c02240d0b09070318110103020705060903070501050c1809090708010f06031401050c031506040b0304030f18060507030c0c08030712120209010c1b050910050a0b0f0a050a 81
    0x403a42030005ca1449020030354040e01212540700329000c40c01594140525543c111088003103c0611a5002c06246a5025040440d000c0410701f550620181401842c019203619043e181c6202140c0b858080c0e40001401070810000303018107600250070b4007031103040c42000d1022013004c0502900b00c82c003035101880003440780c400400041d402842103400820011044511001c090031741c601050b0b5403090f0700706210070800b10500c1041d201d4181c52041034116180c0b0411100703401901d441482d40f0020920010238400900341c0114000c510944079600c00710a1301d10040e1240d00c040c00f54441c0061403070010000703103410104a40710642d0601d01040408518541500c9028164101a01c1031202149000c02c01040404404241800352103c1c040f90741e034180788205a1040d0004a40080e402c040c0c0302c1c0c00102a48840d241024a210a40d102d01391030b03d0200d000000101c40482c600710440303004010720305000910101604507040c80c5480c141c5600b010310601d100d007035421410080d00044020a00707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 545271384 1250 545270134 545270179
    0x301090b1915021513031107030809090a02040902300f1b0c0106150917030405010c03031b08060a1403300f040306060506032701090212030301150c030c02 68
    0x2119690f0b000007820f0039105c0303c500b04d403803100071004107481007061114150000350002c01c617503010307a040f4034110800017403001101c4083c20b800141c503000d210205001036140064054040c2030445141c10100c5201203410011040c81c0b81480111071000744024050200000c03540128041002c408131044401403191600c50f214290032075503e0060045400b501c910106226100b250b6640a401e60b00c0d0b8840302d071252100018403040351f0042104100c4d03940a4446482050b02a0400145000a401000142c0d020b40011600081c4864041111501c1c1021080340030745135841c1c6203030400b00c0e500c010990b120b05188400030b00704280d42284204250400714118103ca440d41c2c12038807a10304008010b030a4001d404100d6440b8149032001c0381d603003000c1d400c0d01e204903031905989c0c00944003118603503091b11140c1c6080042e55240c102e09005031711000f0822450740580030007540d03a585403a015050140161054604001282d129080070a510401c0c2040168045414803000c03c40060307004001c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 545272634 1250 545271384 545271403
    0xa0b010504030c03060203151f0e0a0b1b0d1701030602220b03071d09070f09270c02060708150a0509070e100f020a14070302060f0301090b191502 64
    0x10034200d443c088100305090b00618040d034503d0890400301e0349494100850008480804603d00140601c540c1070f0b2481003000c000407800183c00b100f581c03500c0c0c00744000d055101c602c21002e40c000031081501801c004000d0003215420a146c40340440c2070001c0c03c0c40c00305e201844043c280030703004600103591280d408401c0501c943c20710000c2c5040f40d5540801100d03604100c03510702c08a0080b404031121a4208001080068002402c04003160f480c0f80068401703040c000e604d1410000b00031804941c607101e4000c001c941520300d407504422600c421100005450b002101c220841d0000340601074196000612541c03c44e15042c01815440703090000304025240c5a0301555000404e0428450300d560080d101c043d6984c41507480d55281c81c100c9100f6182c0c54824450000160b0200e81480b000c1501039221034149a000400d592800d5942d8000510903044030b41345c48110003000004028041081c4111840790708240e600b414141c196001c0c0d01c06c7c00300030707103d0603100114031a242141c09200f030011052 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 545273884 1250 545272634 545272643
    0xb03090705091e06030a020112330306110a09030f170d0504050c2d0a24120506030a02040f141005010e010e030607031512050c01081e0a0b01050403 65
    0x14501e00036803550740072042e00303034843d1070110341a001c82e00c03034203004c07550140d05034044e160007103054041c0802c00c00510329019002c0900803030680350b101603010303800c440a00c40703150481e40b40742604600b481c07803c64901102c010709002d020007a443e0010341081d403050450b9041101ca981d4004203040014264403440700d0780251090000300f00c112590310350b100d64081e40c041d808868152240c4018030000d56080c400841c8801c07281d101d0300742c4041842d500d115006a02400a0700718554900f031401c400c0d201e540203000780c0101c001d03201000715444042040b201e40c1e0501c2c1030009040c1080400e883e598000e4000e030090b40c481c03040f441015450303040f04002882d06041d040e0140b5059118585c0c914050060500083c10340864005541c0300b4004866031640007400741c070701030325090401d80040010b01010944050454400100809855500c602e501c0c0100041d100e00740301200010303c4184010482480c0e07806004c082000c003900050100e40c006082540060981e084000681e6a03000e81d600c000c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 545275134 1250 545273884 545273899
    0x40605190e123313022413150905061b032802070e0402011202090607150c03060302130c1103070305040812030c180a0801110d052206110702040501030623010605040b03090705 77
    0x20300e602030900030706c507c0341d02d0071340d8403601900c91901d01c40303d41c2c1800741c0c0000603036520810b00051404400402c007801c100722081448081402019045401c600940b610011014440c1c041105401c02c0c0031244100c00d1019005460400b0fa072074800e9035024102038100400081300c501c6010850341101c10b2840000d084540740c50551030300c2480c84248035408251075041c041c048841b41e0090107030a080d41c0e4010020510b0126104101c001400004940000c0018209050300b61000074001080010f000c0e42e552541ca03410900c885140c040301e07030b80e25000180e080040040d00c0301c4001c280c1d056076500f5036014000140c14000518030303e40c26081084e89510700991086900b40303410007868000e00650041c8810340d00c1a6901744001e00c1035511111990a056032280010f1042c0d00c2810b0020040c84514201040764010a00f100c00c00d800444255680f20804100340038226401030840d140f4424104080d810041d00401e580102d100e210303082c11010000c24002c02d0180141d00103000080c1116 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 545276384 1250 545275134 545275189
    0x904270602041a09030a0b090c18090706030e03040b0f07120503180606100f020111040909060e0a0c0e2d010513090309120f05010207080915040605190e12331302 71
    0x45004003500d03200100d120f00340e4002250b03402406440d07e0512844051400d11d0b141c140115900c2e481824801e4002c4002c04c00140024181e0f142c41c54441c00e01d955641e00c91926210000f510303102c2c100340c0440b03030340000d04202c803030b658511a0150003a014030300070400c2c894607101a40034000980301104021004580400c4c035080903030003928080d000e202c003407000d8810100321170303115804150060034010b824103042c0b011403002900345401c604512100e02c15070294400d1420045181d030601520051300000420880c6090382e0f0001c10740914180c1007191030026500030b80201014401c1003420710740e16510009108281c415894041d03080030081d543c03010240f4000801c1d5001d0b42c5410b1180030751154607a40c44d0404000d441c15a4250f4a03040e01d03005280314048501c501551400040000c003818040f07450b1590415459481d240300010030440c1d0812980300303468410741c4544c01e8607407210005000c120030285010340d0492011084084800f4030b50010030046441461422011007040450 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 545277634 1250 545276384 545276419
    0x1b04021306031a0d020f040e0f01050903040f05090712050907030503031005210a0305090a1706090607030b0a030f050118051b0402040b0904270602041a09030a0b090c 73
    0x908800300c81d980b100c0c0c0f0114604401c004c80c655004402a400181c402800851400c05601c403551a00412084070103c0b904001702d1400d40c0d00846100002c4d400201d800c02040f400304807a02c01503d81120a0f001500d002400206800e01c0e8418411b04242c40f40e0101d990181c0920566020b1608001507943c0c0b89403a21088400400f944103103801a82038940c02400822401501c00f1901c00304009070600b103140d900c044495411541700303280d200d02ca040740014440844048020107002c040c1c00361a6619068202a0901000030300e94030525040100715022513481980f0401603c0d44541030400000070350510034018501c00d00380c0c0d00300d1100e2400e0207040c0180080c2c07402c2c14103510317a084402d0391000c9042c03005a004c2e07441030b001200803e100300a80c2e4170341500201c20f000c8400c2ca00b08d460203001390181549212071300c01541c1181d030020302070004d107581c0d0140398041d0400541d65440d00e84450301003a030b2040c5483c005007400c001c10000c03400a40781403081c10101a4000c20180d10408190320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 545278884 1250 545277634 545277641
    0x1b0609031509150e15070c060e0d020c1c2310091110230d290d0602070602030a020301080607090e1513020c01150b04081b0402130603 59
    0x41512460212854101c480707440b809180d600743d5110002260f6140141184000391641e00b101901e6806500a90300314264201c5070907200d122142d50700110030800b420500100e440c010300003085904200103c01400f41c0002d20450134049c01d81c0c031541502070120540016020702e4400900344400840070714400b800c008201c801403105a400d65400c0841c001500d0b0440d00d0030407000b001c00c3c0300c20425040e50b19184c02c00b251010307850b040074400a00301c250b94a440701d00d40380262513070740c01c08141003414442c6032107007092046400c180c0040e070f09042c0000d564541495014581709000714085201009215015200c60340e91010301036440f8100880f0034030194109014981c0c0e030b84500e00000300100c2c46460035008460101c080c03420251200c9522071425003007a030000350070408095200c42d0003410b501c002c02c9000e01d5a400061b940c90280b41c51a0382480702c1d071111076a0380090006100c12200400c482c052100e0307400c120000c1d8000c241c08607010b03004503030620100c00c0301d00700c0010301c1541540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 545280134 1250 545278884 545278889
    0xc10020a050c1006061b02010203190906020705060f07060b06070512030403121a010e0f09040b0411060c15040303090605190b03011e11160302031c11161b0609 70
    0x95900300c1c90750ba4480c3c02161410f201d5000002c00800003010ba0035402e030003084801d401881030f60315007504803660340c400501040fa03400000d1082d0204008403981440450302901086502900d000641e44101c0034500646801a018940e600ca110219a4800703044440790b44d4071000703981c12008032451841207900200d8040d40400d40c50b8180103800041480f40c05e02000e2115074641458410900454101d011007403070300e4000c44824402490313039503010282c51103140315044c1d9510614041ca440916006007c071004c3c001d450a00c0820700390107020503021810300306031a903840d140e55182002c03000b5140f80300b03019209603d41814403001e01010007840c50a40700c2d0800500c036402c82e03007040c9400c807208940b0048400c0c110b00c200c440f94003a40d400500b03081da54a02003034104143c45440b03440303154031421704402590000880180b0401d000703035030203a0424032101c100882c0300031541e40d1540d880380c103044c80781102c90510807008112104070b84042807140e19041007222a100d50000d0502800c60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 545281384 1250 545280134 545280157
    0xc0305070e0105121005130902030c090c0406030c0903060c08090d0504051c0f060203011539050a0501060618080109051515060708070204051003170c10020a05 70
    0x40000308094010038241c6921a81a5034941c03425403010b4034032200c040054480e1801d800605000600c580c0c0c5c1e40000c1030b03524094840090b072503000e48105480d040c28a035616006240c1001007100240e4140c05490440e2082d04000ca10756190032002c444084094000406241c43c000c00e5600e6150b205440c980310386145800c48401d0349400350280c0703d901540c860030390b0281581c06000400100303400c1d124801d6101e0105030700c10446582d02c01d4240d0300300f600094098410403070440d6000340d109070b42c803800011190b07880500c0008200e10745207210720f020002d90400e5100d01070b001000b20030480f403129070340c10000801c482503e941e4014040c203901403450182000c660004a01080103200700145c0552040007003441c0e02c2e070000c0351210008002c2c0103504810700031841c08000e40b40d00d00105003084c0f01d8542160345052520412044a20140a110490108001c01c1c0700050040c900d0080144082c80b09944841c0c031b89001501c4c219001d00c60300f940c2800441c42500294210303002c0d25208444 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 545282634 1250 545281384 545281391
    0x3030e011a04050618072a050105090d090b12280501060f2c010c08040312171005130b1c0b010b0a0f032003042a230f090a0c03 56
    0x8107000c000d44040d00c40701c900910000c86020806ca00c2c010b1944102c0451810300301c1c4000d8110741090b040c62034074040309850701d0f5110000c012183c0400d002d01c009905d440d041282c5040d042965940c034600401040008440c0503a012030068065101c005a20055544204520290740f27010034001d00820711510300800c03818695201e40c44d0041d0001c25500003004502403c80ca0700c00c84840d1103102440e0818144102e1b4003400001c07134411001480558098068031103a030b141c40303c2c028910035000c91410075002840042c4031900804130011407c40b80d08441c0c0343d480200c1c0c00c807150028442004007030780c82120440ea154400c110003448010483c000c2864079266030361400074504a102e11095a400900c0121188101034040d612840c1140c01c1003a45000f50008401000d03025801940c058aa5050f8044d064820145011461000305000a0800710461400d03005041044180c085441d03110340042c0e01d10103680341c00c5a18070040d0740051125a01b800c14400d804001c00c0c042c3c2c046d0001909 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 545283884 1250 545282634 545282641
    0x20102060a0b061608040b07050c03160806040b040602040807120b06060a09060c150f020d0e0c010c0f0203100204030b040309140d03050d0e071706010807030b011203030e011a0405 79
    0x3072901c140070040d000644000d1810808020142d545003011100302c400075824000800c001e5405809812050b1040c0000c0014400d2902003524001081c10100d02d20301d1803403424030010302d000ca00305400c071764040c2c002950f43c2c60740e2402001a000b141c0020f000c41c46003081c00501002d003400c080c0702039806544402c00640311034041c011984503c100c003c0100c0e4440008000c071510503004d18405a0054042d0b940c2c8620400072202520602c880107281a60041246500c0c00418400e008280c6180d40c0100f441c18504000039003401c40b403400150581030305881030801e40d141030194694000855801715030b103c2e140d00d44464400000d460550000e10010300200c1c03600041d14000c4032a98004010002455a594040783c00c0c0e40410701c1e00b00010b480f442300c001d05410400040700645203580314000340040740d0342842d280c40c0c0c059000ca80d95603c000800c1002c01c0191a00c0da043d6202099860302121041c20140c02a08080e450480650700c0d01102c55121140130302110402901120203014644 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 545285134 1250 545283884 545283901
    0x50901090b04050f060d09210215010e190e030309070f0e04081b0a02040603050607171303050f072a05040509100213081002040603061509090c030f020c0a02010206 72
    0x91400385613040035420200014500d454000b6000a040180d4042140c44443da901442d04445175500d201d10413a000c8008815030f01408190100b0000340701c07202c02980341c591982d0b61184040c101e07120607500c4070b0348004004055084080c514600c00200c1c0e5503814000450f07a5503e081c1d10136900c805418240115481901021890041f9004100207051580a100b00c50310f14211103841e41c614858240c0c80001038640780145002103000e21301400b401d01c0c204070003402c1d1a28100ca4442c9081c0da400400c911010301143d094030036901072030500e80b20607c120348040c482c4560080039100044848000400c0d14406041e1699200d40722070340c0710041d5641044c8816504d05452004140c0c112901000c10405160f01410302400d6004410701100e54540302c2d2401c0403070700020046069000201803103100d4150140c54005d045040d40095002da10500041400761380c0e001307815515484407581c81c0014401d40205c201c03c100d043c4210f5480c46003500c0d00e59140940b0304100c1c00740c01070a00080c80c06 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 545286384 1250 545285134 545285137
    0x30306041503080d111b010516020f1209061c0603120f0c020d02040609090501020304020406150507060e1006121424040f080703050c15010f09020901020f0d050901090b 74
    0x10b0307510040eaa8103203c41c50f420718000e420440c401001d00017091000207400d0704003810742c00961869200010b00f0b07050400e1141001c17100804807038195803103003000c0d181987c800142b03500310f15003050704145c1b544e054400141443c49012001c415269410290745103881a5074480b8080303038803a400d4080b400003840d0080e108000750208038400b2901804004000d0b0500e06500d082c80380c402000025041c0e1501241800c031102c5420039103040e0350200c10403046042038072a0a014104240e00d8005070101c0240003030007841406070044c41c490b1071316410540900108902d07482d40c03200036410700c5030903142c1c03440900c1d4210800e42030781c3c0204107840401004c0c40100d042601e140c2d12030210248400824480c40e25500301500845204904841d100c000c2040700340a08221f901ca50340c1c1d2680d50f01c10038413507450074a00e0b181041803003501c040108038280d900a0410212a000100540c5030204000103138180315940004504600813285070f1040b40d0751203070040405900c2601c51110741500c440401031203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 545287634 1250 545286384 545286389
    0x10213080613032c03011b03060902040b0306012d0c0302160b030a0b0303040f03030809060a180b150a03060f0e030906070b04150216060e0309181503030c0303060415 73
    0x22940c1c10314440321104d018220390700d41ca040d501c4088401002d10002c20b0851b44101200e50511040c01c01e112042c540c10f004000c01494109019410b00d4103018a2210900c80a4505814084600c2c10f040c0e1a107100c0b100040c000309071464204404c0094031003e80350071101c0200320018010408030500f503540300c1001134280c40f5507041036800c542c0c4508141000b84500102c141d0306100c18000010b940c241181c2c0300000c0c51180d074403180c1d00d0410986043c9492006070a03200403a0501041128001d04500344032503041e0070502c103900c10744074070b15011504015602030315000008240d000c028000c240e006101134000c030314810440408807000c007603101c0c001c903041654004820840240030812078403000b50024015692030460a03180c264500403a8442e1442010142810212100380100d501c20204482d0068020f580740440f01c0d00010611003000c461101010000004187c0c1740c0d040001e101d9140c1d4000e81201d40e540c12004046a89030000c580c50b6208a052103402843e10b96000c1c440c404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 545288884 1250 545287634 545287637
    0x714060a090311010207090e0309010f0219020f0d0203030c0610050d0302070e04110a0f09060e0403080a270f0506090f1c020c0a09090c061d011b0501021308061303 72
    0x110241540c0d80d20032680403044503203045106d502d0340441da102e9980306003010844400d005540d5116402d00240c81081c0741d220410954100700440800501c1c0d694030110310f81d50403520245400307116000117001c034400d43c402a4042c440414500c54801001488600880e01c41c0f8000700b815503a1010000316000c07140e00180160020300d41041100385c03a200e00340d00310348550603071903406c0549400325580c5070503540080c82004140c0c90801402e104e80c804c40d0081d008030020003200e4901074401a04588000c0c0c07543c020302d9540d0641061101250b5000040030103807000c81002c560a60500300d0740c01903251f03020b032a580903440208100e0040080c40f013114082c1b1710040c1800c10040f080d0031022241e050880d10650181040d6030038980d5500c031038540a400b030800001022615170074a44030080880d0081c0701804a119011000e0310f41110110700d1a03403003480c2514024401450b5103003e052201f1006003158004264114400d01c050501801d864045084400070b40c1c55000401010700161300250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 545290134 1250 545288884 545288897
    0x40c1401140d02070209090604060f11190c060c030b090901090f03081302031c080601030c2705060301030605180a020d11061b07051002120906031015020714060a 71
    0x807a1085001c0c1280010000c001410514a034000c141600003c0303c200c3c4040d00400c04000c200480ca201c0c02d0392000804c030341088408102c0d5018042846400780404483e000007000e85081c0f8030800c60781e1071260f441081480950380c101c0d0086e02030004841c4252144d104040041c689010520030f0102040d00081401030409041d10181e03001e8401822400d40b224090900f2405a00d04003c9480749484204c102d007849002d43c5c00081000001a0074141014144070f16002da844d4495013100c089403000c1502420284841840307c2035031199400b480d0056400b200001c18407407503034405440b1340c8c001c124400702c081081000035114011880c00952010324044800d02040c0803e04058403000d024020300c0c9030032070802014020050b404900c444950041c40c060219003444180815142010700041141d500c0140f0030041318000c08008901811300440007804004003100700b180180352071040c1150180754008000d407150b2460040203500c100c00f190410381030a000044030b013890071594440c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 545291384 1250 545290134 545290157
    0x11505010c051c08040c0e070c1b08010f020702030d08040b1b040905150406140604031101050f0412120503092109060a0e09070302070812060112060e040c1401 70
    0x19181c030303421001d0a907036620800901c40c58000000001c503414403c161100030440c549071900c0c0140041a800c0300c00550154400e2001c040c1d040518101115403040400b00c405910034407110205806a1162034290b080c2520341d00c54040380c4e2700400502c0e009406880c42614142c80175a003062080d034000301400e0121002554a04002000b0441d010351071440d9880c0594501441080c3c81056a000e082041d0354044050a4034143c4540d40c001c2125090720803561800d0b80004009001d1484003501c060624200d01915038410011a20701c070001c605800e840301d031102c4504c0381b8a04040b900319901b41143c0b82c0440c405001d941981c1c45a403a07070000741042c081400303003400c449050440640310b4102c1802010103658450b800b50454200690303581d020099802d013000402d01015121509042c810003051001c145c1480450f100c803442c2c841c85411030389034500103c030482c15060020010a02d8118049040e00816001600641c010303503540d500300b41c964210700750b6840c00d080418086130400850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 545292634 1250 545291384 545291387
    0x1080607030b01200703150f060504181506030506041218050a060513031502070c0504182607080315040e03041818050303010302010219110609031e010218010201150501 74
    0x9912541c4d100d001a00d030120b5030307030307440103802c88030302c50361142083d00c5010b503014100140c845c00c070040604980502032003034020100c21100c0c3ca5404050701150380c2100c40e4a02c103251b0380045c00111b40c014201d0380541f43c2401c188008402540802000600e96965061804048020070042d510300501101d0001d00c1c011064030790380d1207060300704a030b42000310340000402c2400c02071292440d110b41000d60ba0302d04501d409004450b0715041644030760303d80034118007101054a00c0010b00c030b60100001174850b02920800480c2120b01101801c1c401000590303208101c90781c00518090b15102c00c4a000c081882c1e0104030940c0d61451503580f4503031007884200100c61666003c0740000309405c00006000460b007200101c6545046000da4555000000400c00c42d40c1c1000030b141c000480b00c0b0381c40c0302400141d030b403c0e0700d40010490b803d00c11000480c501c505a0f0741031158502d60403003032801c1360480c0c001110b40c07400b035003004059000b504812940d0303003103139401805040b081d800c015100c02d000c030f07040600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 545293884 1250 545292634 545292677
    0x20a0f030614270a0204081519050621100e0c0d2409050604030f05031b03040809040e01051605041a0706180b0105040f061d07110a0b01080607030b01 66
    0x100341e404041e0f00901e1804040c18409031501070312030341101690b01d0341020841442d0500f00144802e80c120380c40c0c20070020074196404071100c2620114082010340391000020810300c00c1e106002048032940062044a41000500c50b0b407116010000b80b0810903035403106a213404511054075000b07034601c0c9001d00001e41e500c1c3c100710302c078252040e020038115941105608a6175504812501548488140300902d80c01000b840c003064021f2902c0c40c030314648458076685109411569214161012010804011420094a2000d070002c3c004000d05d21081c17224030301804080c2c0d0302c2c0038411b6200601e1003446101c2c004070340555801349880c46081982c4903107481030340e0081e10140d6501d9a141c800881c01d841800e100740889000c0c00d07080c100c55040c01d0401c012640c5026908281507e004000c20100400c002c1544034014039104600392a0349801e020350340007554801c8140e05d0700441d0b500c0030400c603440d0241810f90f10755a00301c981a0369921000d0301158038140106011580248003c03081600f00803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 545295134 1250 545293884 545293909
    0x806060d0b04060b0f120c07020d1e170a0e01050903070303080603030909040c0f050303070c03021309080a05040603050a020c071502011401091e05040b070e06070b0a020a0f030614 79
    0x82000840780c4e92449408069000200c01d55684600082c005060505c0d4150841d0030043d903107506d502e880c2c00c0e40d00041d41d20341d10a0000f0290303a007411411490505000500302c0d460341100f2400800c1c4401c50405c00b007070b03000038600c0000c640b9645140700c00b544503405540e07903660094001c01001703003161015250050010201c40c0d151000304100c0714140c82d09140c00e03024a11911a51a00c5030400c0d1518403092903030380015000b644244240d0000c076007801d000340101ca0301503c03642941c030b00c01418071000d41800440a0000000010303012001030740a0014070454902d41d40c104441d44859284809901ca0f05400c0c8002d07520024040c8102d080c0c295050800034500d00000480d8088094015482c0c40240e00045500b69298801c0044d042004000b04801e448440200610700d000c0e070365554040c1010304543c0401140c4002003148d80c5905040b01c18540d08003003030541918048030500c000e94004144080010005c0e1814082180240281c4003680c0c07001c100041111210b2060140c02010217 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 545296384 1250 545295134 545295139
    0x715051e15042004030b16020a06021c0903020f01060905090c010302090105120f0f0c39010501080c120d0516030504030f0c060201150806010909050304270c0806060d0b 74
    0x5501d0055551400d0120b000f1940042400d65195451030801ea9207171100140202c9000200c1a10320640660205066008680c018001612603400d1594192000031060005003070924105841d4141500003036048514001c0500030b001e4142c4031701c54001070710b01c10750710000d082c0d000000100305580240c020b490f4455040c500b6030704110141c031980948000c1070303881d8a0720940340e005100b10903035201b0125605c40e080d403c0083c0303003407284550a03100411420360b00790300a109030005102c5a0310001c0c108007440001000f0f0081c0c1d41c4941c102500e0320302c4058490b01c518443d0300103440700c80010840803414500343d01d60f0b5003080e1196120500103500c8640c01c9081190821010000841442c008618180544085003485050080107401c440200e00d2100c42040e81c280c0404c0413600000341241580d000c400003282c05520b5141047c51406642c2040d44034186034a5050801101c1100741d04001002000901081c801244140c60092064490b01e40120b02084403003012003960300409844c4402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 545297634 1250 545296384 545296391
    0x18080d0509010b0d1202010f0507020318010509100207090605010219061a060304030c1703100b07020d050111070c0e04030f030902030f011d0f010b03150406110715051e1504 76
    0x41c3c0014043c5420200201c038400c51054164500681c248660000b0b0602814104050b00303104601035074078043d11030052280e04542c6210101a44200305136403c40c04040d002a10b840b865178800303511400240181d034281481c2010000b80c641c40001c03001071503464041c20b03e4442d070160320340c02d0180020758603c500c40c4040c9504844280c44070402948200d0081d0354609070040f4918089040345002400b04070884414401d21464064041101013150050455540d5031525880803c1034003001038405002d55191080c0404081447e5003705a9031380306099034164543c9501c100d04c448401a500540001c0c08050303440c003124000d90010402074001000ca821a0006201c158251104078021400c1c0c495048424203410070304220350388581407003d009000c0c0d10103000c0405d55845141d002c0d42410300038207020a00388403e9500503490a9240086c099580c6c00030300b0102c0c05084000c0c500e4011625020000f5120103101c0d0040c400c0140d101c0150825490350402c104400c00fa171455107901c81d54 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 545298884 1250 545297634 545297651
    0x90105240f180f1e1c02090112031404060206240a0f140603010305060a05060109030b1501120b030604080f0d051503010c02030c120304111207030618080d050901 71
    0x244002a00101c800714054001c000c0030201800700802c282141c441c05403250826164010f04a0400143d04c840c0c19a00300e204101c5851204250788038103000a90010201c00022441c40007007000d95102c031b03000762146000d11600911a42507071255106000042c2c0007400421244803070814501d120360500c446400380010003c0000c1e244818540c056280015000c20070000308410501c0301c02031000c11290581190b142d911501c0d212400200b400a403155100c0005210ba805041007034003031508046803004526052204070102e1034040d11060210b5104030040e00404100e001d072800c4034001401800403600c0710f03034405410f0380203890b580c1442c00042c0b100b140e50b0401e03840ac0b01d106028158009501c081e050f800c0c542155603c100107800c54004000d860010200001c02c1a40c0c040c0b4510152390347c0d6074a0405590340101c14200301d600c443c00349818110600b002030844c00f540d01a030303420840e6954400401c0e0a42000c8900280032680500110300118810741c0150350100100d00046100344 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 545300134 1250 545298884 545298907
    0x602040303021c0804110d1407060212040302030304092c010504021305040f03231210060f020d050c010f0504050115060f09060507050c0405010303020a0b060d0f0b04020a0b0d0c0e09010524 83
    0x103e007408d609506500034501006032550402074034a00742c1404020314600fa0440d00881c0d200c2c400e41c050a6001501c8000c0079141c510b200b000300c05a2072504200403001e01306044c045018120035101a8131520100382c0030780e050030321889518065036010040100026480e075043e5914031203a42c21620085003110403000b00b60a880050011806516030003e0034507003050f58200c03421050304081c0c20486512801038540d900010740724003149807420504c0d1070303c000c240c1040c00340a4607091110050700340807d2000300a1f0540080240210a201c0c50210b0b0303495070801c58181c043c070201603000400215013000200d0182d03009048040c000c0080d035200310242008601981d000780c0c022401a80401480030901c0300801e5100d4100c10216050a905031043d2604003400600c3e40002e400790400b000800d045650703460b401001030480c0d00906440d1290900c15900400f440c2160740c020504418040c0584e2030301d200d405040e9500100f180c1c507a5032122441985d00100d00d00c0030040c0140c100107044100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 545301384 1250 545300134 545300153
    0x130e0f06090d1b0c06050c0304030213020405010e0405190207020406090507050a080c04060c06020901050d0c0e150708030f0402120715140705071502190602040303021c0804110d 78
    0x2031078080000d1003903481c6804010300403400140d0b84414a400301c01600b000441a8038100d04480203898555114040042500e045100700e80c4001d61200c20303181e401c01c5810140d00030f48104e4400342c90319607004110400348410b8600c200e4001c2031071100e82940440e0328009a0241030b940380081c10014206441d00d1500e000c40e14151101400b01c0d5004c60b40785e0300541c1c041c508690200001d514941000c0c0b030708101511403820401c00420054003c01c1004040e4445c000351a000503d1640038850300c10805400f524048441951174002c00d00300100880e1200800c00301c0d4030240d4001c21251466580840b4802c403500081c004907401002046e0342e002091341009034501801c680d040285549030100c0700039200c0100c040800003080c5050100c2c01c085000461840e00b02c40c1c00400281442030b03014030481c1000303c41c440e41085003003510303051018400141c1c003400c1903921035021140995021225480f03a502c980981ca00040e00c1c220020b00011036803d494241010080d2110100308020303990000f8a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 545302634 1250 545301384 545301391
    0x14011e0507050109200d2d211805060f1303080d020d0c0c0308070c050102131206050a1103130804170c0f01080c18030703051c021b130e0f06 62
    0x114443d0b0203814110b40041d841c90104031040300c80941006d803e680d0340340902a00115845c089061103103503150b84191902c0f0780c0f80c1541c410b9810318200000101030340046084200c002c005421a130200254035090341074078040c3d907401032055040c2030a14403c1e00441d8444800002c00c10004000040044e10550240c02d409540150242c1c60381c0c040c0c40b0041c21100e00c0e14040007000185c0c800b00d070209400a0446402154501e088445002e43c0e04203075000e4401d10030820303103442c0c4403075000801e00d04d4000e54683c698407803a024003044c0c84000e50002660ba44d40309400d6003103010808548007041d44501840304c548600500e90511b540c8941700a116241c40030765140c10b4102e046600030a14100d03201e611007440908004d18a8288043d030b03c02580510101501c08540c0315640b002e03940c1c1c003000040000e6a000d0b0482e079a2a543c4031409003402c010816003809445525158510300c2c8000e8001001c1ca400907011403014000c0702041e201400320340c0464071040c0500c2047c4c184c1d409050043c10321 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 545303884 1250 545302634 545302643
    0x230405040b040b06041b031a15120a2a0903080d02071e03021e0f12071505071704081b07080709020306030703140f01050106020c0a14011e0507050109 66
    0x902c0c1c242444034600900409082c030603031510141c444514008801c078004010b59181c0064507145020324500040d00d121440f0f640300319540ba907000d1010704c1c0c0d0300800e4078103080204c80700c880c0c4501810303034143ea418000c94044420b0320100c40d42070580d040500c034a414100e2602c4040c10b55603844004c0c59900121000350199000a000ca041c01004d10040c0ca180c1c00c11103802440d00c0091714001c0d150042e003a64164407071907800841c4080001081141d1020071200d00381c5051204155070008650b115071400c40b41c1d10803105c1804c406d030400d441803601c070743c4607919441c1002222452131145500d00500460b074805080c4540c0204900c1e104520071100440b01c0141070240c10300c2c160b1458503005074015000e060040040140d6a1404180c3c7c2c021240c1c070106800100340195009405d1600141c9060032031340c40d10000049151f400180d800c01d41806452142c0c9280e200ca500c40d510560f42051103011840481c1d00c24002d80148964004044803403401d039050520b10356443d800c0d10038140e415103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 545305134 1250 545303884 545303903
    0x903120c0309120c0907110a08120609060913020108190513050c0604030f020609010504080d020309210d1d030106060908012d09020d15090b0604110423040504 70
    0x800c40c03c08140a18451600b900244800803081001950b4100018030500070007204421003004c0c02010081d440e18160b0020300350303480304000040304444d414121846480341079102c01003101410084245400f80c10f5103500e21070b003445180c006589001000d0040061003040e82e2410b40031250034480c0c2401254410704c0e25404407440d0410b149866852030603503205e020304003c02c200043d100007402a078581d0607540c80b900d8980420040c2c1740c42c0615070201d5400e00800700d03800c44956002c40184500d10085445a00c00851501e0748004403019000b56a0681d015007000300155001d22061205001400003000344003c80c2d0020a0a5400a50007200468841c000a10241c10207005991185045210346074900b103130040e48503e100101c0141072260390340c800a840c29900d407103440000598100149003282c41030448200000d04804074103580881c00d003008a0030b02d1419028486070014008812400e0600b03045440d40030074603004412400134052071240007aa1594000e0790700c02c0d0302403d8400e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 545306384 1250 545305134 545305147
    0x8270f0106080c0303070219030b010f0315060509070302070c030c061205060d120c05070902040b0414010311091c0b0709080f1513080d1b020f0c03120903120c03 71
    0x11400d580340c5402c400e005401100d000085500d00106881c0f1840d011100320075030304a00b505c6421011102e170405088401c2100001c501c3e070f480c40007030b6012039200300c009590aa01e011040301c02c030350903070040b59407003181c14020400c1c080c03098025203421130051000c114050382d0b07560f81407141c101680c0414007107896104001200c1da032900c40d4a52001054a80d001c2c1401c0955610311840208030a5900740b0858205d000f0034000200461070260441d040704640d5640c030755031202229041880342c005d2042019250040e25403280c0242c10001056042d50303070429404808000c2490012804141210036012105001c283c101562034060407064a401c01801d041c213101c181407440c00400c04006d039110304110207180c0462a10103500c50b1805907100c515041030720300308403688030f0850907a0505062603582588003000c5148146590815002c8650080d00d000d8019140c100c0721000d030358180c1064900d090b0841c035080c001d001000d8020241c8180815540d051809601b000101c80015400231420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 545307634 1250 545306384 545306413
    0x81308010b040c0206130b07020f0a0602041701150902090301090f060903022b050a140c0105240a03060216080403030e18010e150f03010e060f011202010507030827 72
    0x1070b241c00c0f0703086201034104c5152070403801c000303d640c2c488020030503152400041d071100c0c8203004240010000074151200980203042100c080c0d04035004804100008a1808101d41c00503c21744010013030b07081c00b144005162554a200035000419055095501c411200000400545000c6100381c41580f001828906c10304000346406200b200e0249490802e40302c140381c2c1101040164411112490103da4500803008111520740c00500d90340000240851403410121301034102a10407000040000315428600c1c00912022001f82c13103540d00500d01480600115455400802e01c3c44031541c0620204103c030381d5010110f5000740c1c01600010801c0d00130700e14600c0c1c03c9044406503141c51080103e55410540c10040c0c90034060300d402820b1030205170340305441e00c50604504038000d0040080019070b44550a16481d404210f600c4000015000d002103004522844414440c03601030391294148840e81c0c0e4140d42d803a202411020307003400c08429078805244200341c141421622003025190000b0007040f03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 545308884 1250 545307634 545307641
    0x4090303020c10180b0a090803090a061b1407080918090c0103021903150315060501080c07050a0b07090b03040c091406090601121e020301030312021201050904081308010b04 76
    0xc283c08081d0400d0003881c00c9550007411802150f8209030340340301580380d40011600810705c0407801000a07a011041280f10600800c840100a0040a003408035003004074024001000b542d811802041440c1c2d101c22002104d00054440d0701d1260100350310341580301000982d2080003041486010000a04000d081c0100f8030143c0c12034102800c0a40c1000c0b11524020070b04075240295200301655a0019402008071114290045820103034032501103040b00316481c040c0c005401401d02080c590008900341a199804480e0802c0e080000307484420700580d182c11500c480070300284100b103420340001c41e030b105541c00190f02543c4128600a045890801c001007030382c200000007e2812310f05420004552034040b40c56a02050920f4031440780c10002c54258001d0a82c0301c00354810160704203070220108080d600450503a070203600d8250f044182400c102c800d91040000041440c0c50700001080103041000d582c541051180d003d0f07604050712440a2071000341c0c168010140c60303440b466140d150741414070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 545310134 1250 545308884 545308903
    0xc0b0c010b2d060c0c040f1a0901080703080a0903050d080114040504020f101701030f11030a03051210090e0a0308060a05010516050c1503100902090f01120b04090303020c 75
    0x1181480190200700382490701150700b0702d0a0141c00001856460020244401143d01800600400440c0e142d4144c281c02448103c1a45010800c0138a02c46140d2408045007030407501d5500060000302d00b156038403421600114290024000030260100000342e050182001c0300325207580b194a0b42d0b2414051084072032003023103a00d01680c903142c140005a19035a4a2a18050342034030035100d151000c41c0102c805100d07255901000043c940d0010040180c5850301e044403e004085141c18108410100758540001100080204004104c0c3d44610783d01d20901d154096143c0c0ca4501d107991b42d41c401c03902030b1800100c8252064214031484002c060b0011103054014005030740300d02807035042c0000030300140f0a42e00014501038619440c0c40400808003c0315803400c0014080280da080c24410000068005403451881006440b80124181a2510a40705c046100614401c1926010001035450b1141c4107900d009a86c0c444800302400d032645c0c010002c00c0c900c20780d00144c0d90004001c0c02d6091001c0b80d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 545311384 1250 545310134 545310169
    0xe04031803030e0f0a0f17060a0216030f0203072102061014090402040b0d2616150e06070504030c14010c080c07050a1206050f0603030d090c0b0c010b 66
    0x8040c00401da0007109440300200544005020340104c5000600114481d130042c29940d541c1400842c41c17a0503c4211103c003803640089800c00d40384c4001000070703402404604c900d00144140d840021903c90101e074026000382d40141c9140a400f52110700c405038030501345501c080112000c00f006079504005003540441154001400182800b00d41e03502007d42c206010b10172845c0b0701c003260a40d83c40390b02003800c084000b44034115608032403030a81403800485600c480c41030500d40714440d0200c0f40307604640140d02c031a0100140c030110751b0341c2c0003030345410071541c149881c2e56035a02425500d0104603080c000d401503100e1540b503d14501d44155a0010742d0030858104000441d2610540d800002403c00d85601c80c101e50349890540d04c80501d410840e0b8081a8400c050507400a0007981c0c0b4045061801c4c0962014070060b074507a00c8032040c43c0c030190340054069000f0045074412080c16481905528891246c0e060056911424640ea9400c80000303101941d55403d030181300f0341b9001d40c1e10310314201013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 545312634 1250 545311384 545311427
    0x140a0903050607090b190302090607030e1e0a120305090d060b102c0117070c03090b0930011d150907050409020a0b180a0b04050d02060717040e0403 65
    0x400c402c4030598010001b401d040700d807490002d5030320306019130144c44278032402414035034407400641001443e9840760051a4000e030b02c0c20302c100040080e11300d001240d203080949002803c4d4a41a020f00414094041c280c08002c3c05001007038030f0382d840a0000b4100d0307006060210340f5086003020002001200b081030802d01001c5d100700781040107242c001e210443c541c441c5102c1090300500060f00c90141c005060812a2040d404005001d600035540700c400d54060758880b462030351203068121540c0708070301009a02c2184003083d80300f100420030401c220000c411000d4600740340c0e812031070303429076410b40000c104580c1c403060040302c01c5030108071064084051400072203290502400c1c003600c2d0111401454055a124130055003903489411114008090780e29400d980d40428850b042200c108003c03172144030b144180310004c0d400d803c250035102030702c20040c49403141c0c0000c0d608100540c0c0c0182404c444900348020310783d501c003e4032000340c80208002c880d118860318140c50014200900040c0b4220131501 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 545313884 1250 545312634 545312639
    0x605030c04020a0c110a0509010308030f0705040302011706041d010e010b032410030c0e0406150501200106050a0e040501060807060c0303020315030f0a02090a140610140a090305060709 81
    0x288100240e8030190045c800101d89040711010a104070219007245400a409900000400c81004020744c031504c203c0c50340754810380b169141102c6500c102d11001e4001189100203071038001c0c0d03040c00e454102400500014180303961030400f1500441414686d040b42c1d54400340c10900740d41c28003c1c24a00035041b40502aa248020800101e000a00714011800c1c0a4100010703100040c04e00684090b58200d04002c1d40c1c0c0341c0d204141d01e901b039002c80302100c00506040400508048440f15001615016152404d442d09005400c0240231400c1502502c40e40d01c485001490b61034401036400940004480c1584c03903e0030303051460949400b80d10080d45540a120f0400003550b02070300050700306070315160150303403070700c600304082e4a03c0c42c1c0b00e065070fa05000d4000c1d9242e401c8000a040301d0681c0c800d5514030070580e5941d40c1c0b1340842c0c451402c000c1c11003803a20300040b034503d00040c0d203404c068080c0c10410a400401285803595402c14904100071642002d4180103110701084810360110261030500c15090 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 545315134 1250 545313884 545313887
    0x216050d02150c010e060a0b0f04050f011802090a0303021513083f1f0803070305130b03010b07020a080118060b03011d0114060307120f03090e04060605030c04020a 72
    0x1d240d425007004403440414001d0450f0402e40010f05044070120444105080100c5600001d00900c13409910a106010001341e1500b0107016180c400d0b80c03406820110740e880d10355480e01c1045481030300c0000c1e5608000041e00c1c0d6130743c5828040030394081d5001b04031100510f40d80e80081c55000d0001100709803400101c000245a10089801c1d00600718440e1520145100902840c0e0b12001d00100e005400480030542c4580d1041859201c0c400c0340d80340c000c003412012001c0000c24050f009410307450b041041100d02090248000744201c0071035480310880240c3c0d80c4d502940a82080c2c1014040f1900014203006600e070600d03181d40a00240c80c02048443c0c0da802c490f10301403489140003050191120f840702c00b580d5017175200328844442030401418180080346954028002901928440f040c40c6003c2005414002820010f0350551041254040300980f1044c5166040c18411010402d0641e408a500350042d04514003d510501001c902141404205410601920f150364021072051120707192a6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 545316384 1250 545315134 545315149
    0x306080a0f12030e0d0c0611210c0c0d02061e060d020d050712050309090a05070c06022203050a020a1512020d0906090b0a06060203130e180d0216050d02 67
    0x5603882501d002c00e040702e009065001c1c007042e001001c42c9016982c815800c032508005a14000da1240d402000402844001121240200d031409485400c0c119942e40d1024010200290480c9031140003030b06080d595059540740540c0354071810010b800c6030040c0710199101050f000422121904681580d1a01c200428030481109030040d01c59129a00008107119040c00200b01801e8600002800b124417030030501d56a602101c0404c3c00b84416900040c0d400100c2d101d40f42c00703140113948500c0c428205483d981c003e13402082080e0701d030b81c60000c00544603070400a4468000c0d442840a05440840c9004100c08034419510443c0d0580308400503014141d44000908880001c0074001a00c802104100c003008000d04640100160302d401c2409040c070007041c003000e100b05030005060140031788504040f0780340d000c0c03540c20010f010181501481100c4101d994540c2c040b9604e01100038101204548902d800501e890700d0700540c000481d06040a4980d0403c100500010360300300400d00341c240c2c00b1070a0f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 545317634 1250 545316384 545316413
    0x10504030f031a030f1f060e0601080915010f080d0207150c051c081b2b14040620090303040605070f06021305040605090906040b0603030702040603060605010306080a 73
    0x30503664084444154602452140d411000a4101c44130740c4511480d442c0d880030311003415071b40031501640e000301c04281d44c01254142e428013002d1441030740700c1c0b13401910b00c100007400040c40c5d409124200c103d03841d558042d150007488030014511000c1d182810603810540d103d02d1510464001101c1803000840822203451049120b14200001d00024280780d0f092510325100d51010700c00a070610781040d90301040c02401020300c030003031030622100709004111078410008644030259403012400c1d440c1411840d0404182c2c0b4104020030002d02c1d4108011420303c080302c0441c0c0056880311141270a803801a030b00b01c074003200040350518008044000982c1d0b4059481a4000c00c40700007502d008201c20305000c5030100e0703480700003591141c03080000c0320300c14421070180c0c2d405645012800500c51030039644d0140142550006401240c88648400250150003454941c243c802000014010b80761441a60011030103040c00081c4d0038107003000102914120390080d1210b9200e401054041281225152030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 545318884 1250 545317634 545317637
    0x30b09030307230d1107020111060103050705091302030a120e0d03120504050c0a12030e09130b070e1008091c021f090f050c091014060c0f03130f0503010504030f 71
    0x402140801480c0c5413150850501c1000d080c030001a0f000d010b0305018007070f600c3c400d890740e003161146803070303015600e100900c0040c0c45507202007000c010a08001a143c0d40044105110401e01c0aa5801080c94502c40030401c075601d03152201c0f00c0244aa020044000c0110129281c01d04925107450041c1a61540c0301240501399880010804020301007280070341841024210701481941ca4030703007100f0140e582e0b100368045043e44111005d05c0c0f4011041031301c5500c40e642003402045041d1035508002000800d101c0c20301008200009103503841c106406c0301000140e035241114079140c104d95040034220010360904d009200740c401801074002c218165401c0c142c10051604000c1152214060000c82c84007078041800c1c54241000e010380400c50360844401914201101e403a0b00c00c40c0715440310315100e03a44441103060a151603510b0301000410548a03040c1c120b944541d5802141811580704209003030f500c0c0da640c0802c024818402101c0c200070041200200218035040c0c8020744180030b0289400b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 545320134 1250 545318884 545318927
    0x909040b100f0635010323070509010312112d030702060337020706050f01150f020307060204080d14190c140d080702190206121306020703030204030b09030307 70
    0x3d50524012040110840302c3c030484d00c400f940c0d28184078650010102c034401900801d0211080000e00004442c0308a0314090000b5850fa8a540c4901410002e00004801040a202010308036a20200102c215078000003000380e074003444000c841000b0340a0044181503a0308144035080160b900e04050300d602949034200c0000c0410042c4880c64580c520307001c41080705984144043c0300c00240e0380500707252442003804200c252076681e18004042000d00c59014813000404090708400d1240705164984100e60049a0814106954a20030307a009500310200a500022420385078a07800002c10114140c44060075150002c00411504a00000d070400700910290350164020011444d0152401e4081c02090720700030307981c0c1d4000528500c0300303030b030301ca00140710f9102c1805010004400340064540c0c010085890f01c44000001012040e00401941d9400043e888100101d41a0300081c87d04074400d070f5005a0302c505520300200c40b02006400d41c04607178070920420207865003040d58146034194104400c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 545321384 1250 545320134 545320187
    0x150a0312050c100e0303041211060a0c030b030318030d08070c020913050a0b0a05180a0b07020109080a02060703110306030606090c16030207470909040b100f06 70
    0x1900e0705240600daa550b8a1030300101280c01c07a00440610700039841003802380c3c11460b41c2d00c02181e450710000030003042c9400c140c010441c51101a40261121445818040303100d5403000c00003421a00010744583d21a0b02400000c2030781d28091103d062101aa0704000706181009080105403214000e80203000742c24540203e081e18403920001c030340c85503000084401c0c0158900e0b0154105100351008a519400c081c081045a0f140750390075564000c40c040200413801c0d003a00e4a100c103440c0644044c3c1555602c4680710081503d1000400c94000960014010780c209004001d046502045910b0700b200f005005201d45035802094107500544100c40308000c980310840d40c4406441035000407012400208a40000c2640100c0e01d902100c035901400c214041e2100c0c0447c00c1d18054043c003030340c05102e404100509074401c812400300616a003070910b0501d002040401c0840c0170075a0161171030900d00080080c0100e60b80403102c080c00303005903245903107803404401a20204588124204420303220444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 545322634 1250 545321384 545321407
    0x5120f03030412050906030103031205070201050705070b180d090812091806031f0605010206060405130b0c09180117011a0f28030b1003051b04020d060806150a031205 73
    0x16514017200003042c4540d42d5a40c0d290103000121440310607007400d4100000582230038018440c682c89124552034880ca000c03140c0e0784046140e6001040c0303441d400181455a810084200700c4d4214111058840c443d0160603c184945080780100302c003003104504000c00c290b00c1c0c5030030600c2d00641c0d5103400389860548030700001a041030400320f002e0b003540401d200c01c8444030382550840d40444400380c090f98400e46402050205441e021a0140c85c420356101841c0d0004040420b099031110f1552161814282d0000c0003c2c0c1426080c4000d818222280d001403185a90707441c1e5044840b05118000c100c094100c5140d0364402c5034030310b407152240340841074034070030b0703458070400040f4050f42c105005402c5031800404c800c18041c0f038002a119102d1100014001302c1c4c400e0418805d03039400c82c0043c6900c04105103040b0600c000200707502e0b0003070f40a110742c81c400b60050180300040c0407110080c1c5081e01e0114a078400c00d41100d0452031041594a80801c08103c0c9080d0f015070841083c40c00c16500c0d81e15155 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 545323741 1107 545322634 545322637
    0x301090803040b13051f060608070f0f141306030c051c0911031b1203070b010b07020d08030705090112060605030f0405160f05120f0303041205 63
    0x4045004905000611070384103c0e1400010101c81c045c3d514207043c0084809020714514541c401203a00020601515004d42513a250100b00740c540100010040500401c0c003006020422010392a0301c0e20442082500c0c4011700e0089640d0325820b000307807016500500c078841c0002d00c4d01c0400c0d40300d18420822075000c42001c0b103245100c030b500038003880d00034021000120380c0c803005168550a191001d010729420f0780988100102d00074100340a00c0a080d41503201e504681d0401c201c41d00c00070780340440b414150341c3c000d401c042d1692a0781c0301040c42030780101006013030840b0100401030380982c0700d801007a00101c00e036560042450080604030a0310020300801000c104180000341c05000790a01c903a9125002d4411540302c07800d140d00803c2d8071070781034100032444844c0540500031402c0149114541c2c10b004401003a81c080205102510383c0130181c8020b02c0445000208510b041c400c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 545143884 545323741 := by
  have h0 := BRFrame.cov_init 545143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 545143884 ≤ n) (h2 : n < 545323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
