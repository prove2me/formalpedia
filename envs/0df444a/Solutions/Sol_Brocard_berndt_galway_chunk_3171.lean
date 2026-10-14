-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3171
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:24.729245+00:00
-- url     : https://prove2.me/submissions/d9a684ca-508d-486c-9e31-14330e321c52

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 570143884 ≤ n < 570323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 570145134 1250 570143884 570143891
    0x5240601140a1206050a09141302011b02040b1f02070e01030507140604121a280f021611090108032503030603050a0b040605310201020703050d050418 66
    0x46118600c1001c460b0301440070709010600001e05424a0042c0c0003542005401c401000d5001604170b80ba6040000361030b00c411705990b0181e907100103514202c10405400703400150980c00b2107000031088a8141d00d09400a0000308280504601190765000403500c81d40b903001c0b401d521418001d60511990001c0c0100c0e00010b581949140c80703455460391940540134100024109640190ba00c0320100d400501c3c1c00c074200b1000403d10709151301580c0607003821080f0b04040c100003503070090042c01d440044000101d180d51004494a0300301008140350302a48080030303400c00c0043c0301d06104800c0306503054071072010081800a10014021082010307401410035600a10040700e4040200440304079452075907249081d184200d04084014003e80e500c098942d015041ea03c0f410701590500c418803a41c0034500910480d21400901c80d00c5140d407a111091081801440780c86042c0c0c103150f07146500d0700510449018030703101d44400c2e0800b280c041e21403012a5000800700203d00003030950a010540001c0c040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 570146384 1250 570145134 570145157
    0x70e0f0301060803070803060f0d06020d060906054603020a051c170405040204032f03100207080c120c15040c0302090601110615120105150d08040305240601 69
    0x890b645c0c00341000052114101000283c045d031585a4500a01000201004480e990604040c402940104500c008003402d040c80803d44084a0103483d0890f80d0203080640b0204403030f510480b0726400c0d018644902d00220090901200c6c5054a450003028450ba0a100003440c51040200300e200c07981c00b40d4041c42c12100c800c40501c403054041000c481d000000c04600c03003c2c0401c800c4030380c441c1343c00403a8803602c0031030044240705100026002e030b13000310071004041a0b9148061916100c0c146079a036496030040300905e0403880345070058082184030751141828180f25109050800340b00604407901c0d80c00c081a241ca06402c1006058036841410128102070304180d10b41184582440c000603020f12000b0f408188907901c101e070400000d0340090f00b0341d055410102640c0041004c00450148610101c42620f194942e040c0300d02402504190f1001003505a800140040001c0b010800d0320070013018000000441c1044c0804001c01000140304000280341210b800649240588440c4c100b06013403c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 570147634 1250 570146384 570146399
    0x3010f0908030609091f06140306091e0106050a090b150702030303040b0c0706060305060106020c031f0c09170304260604030302090d0204090c06091a030c0a1403070e0f030106 77
    0x2c03240c00c0f802c2a100c8160680e562030516140800480c6030400c11140b01454981038209603110301c0984030b40f0f110715004454103504040c0d0b20310301910421002d80000c40c410082028400340c0b80c003903803007610000c80e002c0c0c5d403680064410403031a0b114000316031312061480c0706442c103041e4424649101c418114180381c050f401103030303483c0070003040101241c4000010941c24080042030b01c00c0c50754040d10500800751607140481d1241803e04c100300151180d8580036021f07103800300e08011803420308141201c288692004503c0035207010203244062041082001c6241a00c056803198600d00e050300450384c0350301e03080d43d5010307180000c0031903035900c030040d400702030916004105150060342620303000d44c60b00a035500183d00c084400c00003d5200b40741400383e00410282003400c400316000c1d0745621403d1991090003040c030541c510560403842d8020000039840001030750141c4a04800b5203030180303400341401c01c015511790042d40c400300403411244455080c0e20740465240410038081d00280702c0705180070070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 570148884 1250 570147634 570147637
    0x80f0408040515090d0f0b070f05161703091f0b010c03141c0603150501030201091502151504111602010503091507110705030111091e0406090b03010f0908 68
    0x9014401c2c4890f4550480020b812016212400f1000384103a0001c0450310f03001e41807501c000c80441d000c00b20200040c030024020070010b50051540c1d110780386040385a401d403c000ca680c01d001210459041c000c041030290810010750b00ca002d156005100d0f41800140c0c0d9030044000300016000315007843e0014580b6607200a8403641c460b4181020005001c514900c3d912a00a0101414103c0b2380c0100705101e25038950003480440380170382c074108240d18102844000ba26400d0101a02180c1030500c01c000310341c1c4524060002080510543d9040103042c41d18801c3c0d4042036034485617680141a0a001c02e01d014400c080403901c07038003812031608407000100901c006113004064140a40400050290a070a2040c00f4000c05080900d42040c6415600a44050781c41040310306070744110304000c15035060501c41c00500600c12440741d810700326800101700701d25486100580090750300300016005178030783e070103650081c0c0810b00000c00c641441c0740501d17084610f2000989981030403d14080c022620940 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 570150134 1250 570148884 570148889
    0x7110a02010c120e060d020a090509040506240901450905030d02040e040b0a140a020d0b03010603210302090f0609010203121906050f030c0f04090b0412080f040804 72
    0x1960040382240c0320360540c2da00c40703480c0465410180006c2d10000600d8a640200403d10351a11039441083c1c0782d50503c80354490844000301241d0010000c1601b015000c00d156140a40103440c02881d03124420115003010000c0e4407800d441c010b400102800c03080c02c8015551000315810b0040882011441002d00851139404521500c6985501c0141030103028002c4440d481c0000c034040d0f581e9a40d43d214890002821203065400301001b1001c11205c1110740255040b1b070114002007581ea803a101901002540480803012505070b40c0c09980106d91028090b000c0110300038a0700206074241500701c01c0c0980d01001d0b11030b04044c0b040024015503074510300c901281a8080d2141921440300c480181e00d1481000410300f5900c040c40300300305040020070305d0034003800b041e82400d126455940042c444048120740080368580c10180d075039546414414009540f41c000188042012000c0f503c59548140056406649818000300144c045c2d94010441c01d42003061070380c0d42241884c10f500c1d0501c19001e80d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 570151384 1250 570150134 570150143
    0xb0c1606050c210f06120706180e040b04030f05090a030f020301061a07030e010e03061504060b070623090a03050319110d0c03060515030901021902030307110a02010c 73
    0x2600800c60300c5a220b010388401601408481e604003500001c034050140c4104e80214010304224001015402c00100c0c02d0380080c0c5900040000074207000050760548041710303400030f0f5210501000256194040c030110700a074090f50100c40d00e800d10381001403540d4020740090b0140702d01000246003070785500e1161001c50360031002d02400c588851001078090410f507404900380d50b0842c400307401c0e8040c10600903c14544a0385507444c040c20a04010f56088100840c050b41c150818000109440294400010448001840050b42c1603c80003120302039004008162210342c1d0320030240d40000c29a4004075880d140d9590b078500d0504c1c00c10300341a6a2a074200c8003d0030414088045515800d8920040c015806220360074000c02c15210381400c02c94200d21384104090741032400b0203400754020710806e8280c42010303101c03450004140b29400201da2024110010a6600700495618040350000340c2d15241a81d6019581d00d04125170000c15072a0015002c01803030308040d0204006030380012a41e41d490740d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 570152634 1250 570151384 570151391
    0x15051509130b03011506110615011112040f030b010b09100c08070b0f040506071409060703110303150909010b0d0210180303050d11160f1e0602070b0c1606 68
    0x40481000a40096520b00c3e8266091103000388440405102d10826a00c042d59280e00001510b03054503610701003a1401e070b00c040c6c290119040d003540714800040c0510588411203d0342003040d074101100d0342c071540c0702d0350a5a402020510401084022160040960007509410101d01300c000400c001d0300e0044400c20700400b11a404100240d10054031074454014540f16031510f07203c0014091140120f0b800c941c580070707070790024407400e0103107030b1140c644980c41d03400a042032540c50902c80141e000710f005409004403055240a20f1400b0401140300301901c03585440c00c5c19149061010404000c0e00c0250a40d040c1002d41c0b005885515260704140d404450420b01071030340c0502039909081020a080d1040c3ca8868084203254020004150248450900b040080300482e0b28068901a1040034005e03160540c03124804034040301c01d072800c600e0151708844110160050100741114058000300c402c182c001c5204818003441c1c1340306541c090002c00b0314611301002803080c80a441d14100004110654 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 570153884 1250 570152634 570152659
    0xe040218070807080a0509060402060901140f0702010e0d0503090d0c0909060b120106050f040f020c0a0c030606090c1b030207051201050f0127020d0209040f15051509 73
    0x11408844030300001150400305450420030310003402540200c40490100e0381400100348440b006100da244241e031090040d002a03291a400c1001c1648481122810001c801e4804000c1550070001003800051465000e44d0301c080307520003d031451208403440ea100e02c074044410300c0499400300480d0850b000446180600710850b1070300700c140c071074141c0000c1a05c0d0f01e0328543d2010080700354409034120701c003114025075810000d034110b0b080e94018000e003070f00304200581d000481c1c100380d0014461300201c00405411700d008c48a90031b04c1c216a40c4000d6440501c2d0f9030f010801d1294a03c5030f50f01900b0703400c00c1489144400c6601810404501040000d001070519054040c10302c01c1c00440040c00d0300901c0b00074a00302c84401540a84030a8840c0d245103111400009030744040c5104003000320404a120580c8070740068a82402074104204110000340c003000f081310a0b564500c03038025510504c4400050039040d0544020654a8680025024014115025140c0d1818000756100c0300d60840740040c6804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 570155134 1250 570153884 570153889
    0x1d0f0906130303140901051503070605090f03030405030f0d03060602070f23040f0f14060d03050309070b0f0307030507030b2206090614030d082205030c10020c01150e010e0402 77
    0x1c205081c00014213450511240c114190020b900840780d0650500942e4151002c141e1101407511a51000c034004124412660620491768454194010180c90a20343da94010a050445050312100c4a80000094144564251103440e001d8010751000300780d02c60a080401e078032101c0b50b000b0301d10741ca14190840c02103100294045242d041e03020744140000c500c0f0400d02c1014114080c02034508900304421405844c3e48540d02d14882c56004041c5000e1580949085d9107691002c0c06408107030050b1038020415860350402403006881a00c03225580c2d1804410040807580054184010142042102d004580d82c0d90603149140c4400da55000284229004000081c600ea03030224035420b081c410000791107000070205c1c4142c0c2c2000e5040e240084403417401102c2040c0e003203c10901310000c2007202c56884040040030303584244590100c910340702441c12050701e0300d0280d031611154980c000403a250100005e0150900c040d00d03031000401da45003001d04680784040f05014070b1190007002d200140655 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 570156384 1250 570155134 570155141
    0x70b090d0f0302070c2114030301090c050315150403050a03170a0905060103030513170706320f041205010606020d0516080c03091c1a01080a0b0a0e01061d0f0906130303 74
    0x6907c500350515450b016081245caa4009108500c3c00914050601c9180ca0240007128030408002284c48003a111100803c0701c840d07410000011090310601001c80045c4d030400800c0e224600a0300d682900d00903114581600010040c06100b01c40d060071103040025030005039a905495050803e19110001015503801c50940d941c41110385400c030900c01c1c540c200001c40c4200c2555520303501c1c41c003039081500b890b0020740448112804420000c140c0d040041009101a0240040c0d40450600e026a110031005214420002c240d80595540700100540390b0100305038520740c445414034906200d0a5091411150340f4440c003c1e001327144c000360501001c0b109008880c0415030051000480c001190700c07503003208141c80400c441705048081386120ba102e074544894100e1320304200620580c201a60340d60040000a03280c00f01003a184e20781a54851400c3c0264000341400c1700b52010410407584a410145002505228456404400744804007501081041d4409024441c0b400b8400c228907046009 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 570157634 1250 570156384 570156449
    0x150d03020c0f03100903080a0f0b0603130215040605090a08190206090d0209180d03060f23040f0f18080a0f1106040b012606060d08070b090d0f0302070c 67
    0x71628180c1c3c0b0f40105904034907c5405500b80232010049024101e0210084580c65040e1540c0041c00b880003500e81d10019004e4a081d44c401f408040a1124401505000c2e820540213440891000300e4800040c1c207021101d1401426404001c0c020410301a2400540c0c20790300e00080d01440c40051800c509440d070a9030b9460f0316901902e516514500405070980c0200320407504030b043e01a0302c081e044003500c02e02072102661908002e000e08a89002600f885500000d140440360700008942d03e2803075603030361090400045032070b000420185101030f002d4007250146000300742c40303e1203102c0410204540b074098034100c4089081101401d10340d240c01303440350894080043d440740309203030400c020081d50740006412100701000c490f03000320551883c04107403144211490400d512a1000840e9440e04070030740500a402204802d25186540d2111622140200d400280c03a500000303032240d1003039201801c0c2522840c0c500e4210700700001d596560414860611428460710500c0c2042c0054001c19210b141c0e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 570158884 1250 570157634 570157663
    0xf1a010e0105092e032a080705030703140a0c030b040510050607021f0504090b061c050c0d14010806250804082701090911040b0f0f07030503150d03020c0f03 69
    0xd6513040705000700541100701d02110580d40511000b22030844003040502442d1051301c4905465a96403011903054200504031001c01d6229109030026104015019014071004c10001c10509000781c0c2c05004c3d5203140ca00e8030b0044d03281c00e00704807905480f81c1e000380a0359011181284e40d13a0303141c0000341a0100d480f940701c2054601032106040940c211004000f00c0782c50002c18014501183d08005e0703980200d070703032220f4071356042050384002c001d803640305075441000b061105051004488404044441d508220302c10441da80740140014441000519403240c2d2000c1501d8455420351040214070103041c2c0d81c5402d008aa10100c0c0402c2465030540d000c00e525403120540881c00401c0134002d4490b4001d0300c03408924120404182c80045004219081c4145008245440d1504105100581c0101114410000c003880640305020f40c850060130b10f940295070722a12400d011441c0000c00180d03005251149862840b50300000350007143c0c2040c02d48046a203145005400c0021a0034207141042d14507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 570160134 1250 570158884 570158959
    0x30209010f03021c0809010f1e030221010510120f09050a0c051e0d02300705061e132120150304150f1a010e010509 51
    0x41d00701da0390404201100d008132108684440e140040118aa60074200500000c2003080321042a5009628040c1800392030328005d190080804014407107140307004c499000003070300001c50784a64540460404c00d5140c03440000300c6103500d081e0000381c0c0420580c0b85030083c8400040c0d00d01e40070365994044926440a15014007a0303141d00d24000c0c0c0c880c8020718080303403003440080b40861107050200200341051340e1441c4559115142c40300f0444a01c0c0c04081c22a8040407190445298031141021aa54007104100403904d40f00340f01521030520a645e000903000b00030511003480b0100c056a8a2641c3c07141551080380d0b00d03000030950005640d05d80d004039010240d11904860050380c002001e401e194000c0802c6403031030082d40141000f14154415240d40059081c8441ea01132681000a6130054481d100b80b402c3c4480e151411426605030300e09c4107192aa54249e4010850514108100110760920b0b00c43e42c46220580081c0141c0100900d00d401404010110310b200e50300380154494142d1070780c2c0b031803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 570161384 1250 570160134 570160139
    0x807050408010513021f08150a170c1f050a140d06030503191e0807110a030305071b150203060a0906080a0c0b191b1b030b010b16020607060603020901 66
    0x205030115504000324010541c0745819000c46c3c80c1d42408281080d05a1784084140e111844a481445001d891182c2d1000710100c0c001703412041c440071442c0740250f00e0007a04a41a0b00070400c0b4609482c0304512102c8000200348281480d48a8211103c400a5080c5082108015072a0842c0b600503051150b0266141c40000f00500800101400e070788081c0d000c00c045011110003045490180345954200c0801480303001c40c0145000344d1401c0e50090340c41c6000310581c019081101e103000d50002040c2e01107543c0f401404155076002074140c1a180744d64800381c001000f03a41d100a1100001582d08405640c044041920340d580c0005010051000000a000103900c460000780c80c0e410400c0c0884012044140c0084c00440714815a1520043c0c0040c0c09980c0202220650303c1028801120402d208400e960b240041c0000038101c00c03109180d21140001803d503d800d10068006030007165040d582407002ca81100080841071601030b0f819038010b519501c3c24941000a002640c000951004448002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 570162634 1250 570161384 570161401
    0x30a0908070606030605010621020304050102160b0907060503060f0f031204060324030b070804080706021206010311030121020a080d0521011505090f100e0405180c0108070504080105 80
    0x12400744d0780200d40411059030782d0391065410500140742d5500500321062141928011070340990b0b80725004800140c54015000520071051601c030400b21442c40d020003d11100d06010040200941007600380b03140f95081140010715000c0918001c2407141031050980307489a201402a1001084000d030302d5074135240c40d40c0c00a03003d00030041d644540c880e4805200c9480103c00c1d4003c1007180d40200c1c0c900410348506c58125030503a00100159241c0004214150001e14284010006140080e41003126410100300040c103039001c1b8a541c0e00c1c149130034001407210811303090a040b0413241c402e904007031106161020450326000b03540449854002c0d81014029150040c00030a030300d402100f0b981c3c2c0c40c04504040101746840a02034010181020740460780d8090003440103001a070700080042c00d0032412840020214030002d030702040050b031075400803910f40c14075009075508240d035000c0300a00418152903c0380d1f0bc90024215904110780680424086401282114040c5c44000028089450160203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 570163884 1250 570162634 570162641
    0x305030a2006010b03041e080d0c030b09040b1612060906150201050108070e0601020307120e1806030c06030c0d090f0b01141f05041e0306060b0a02060705030a09080706 74
    0x8021980d280c0d0305a419400030804280c450603101c132182641d08580b1180c50b00c8a01312030000f02d0017001c1d1540d4038081e022030200000380000c541d0805001c85d50454000d402010b9415940c58035000310701d00010300c4001038030809825802102e1152513542e205010f0402c4802d40c0b01e2100a01d82c080c0b41c0100481c1c990a560050f400396080103524409030001030404900300d6509100d20450350704121002e00c64080400f5800350030080510440e4204050b94031001085039417280100c0c0891004410722510b81080c40d58030140e40c200c1d040b40d00091a0102c0829111130001d1011481040c002002030008041c00c4169281d19048250401801c611468000c24480e60030f13606072142081230000064840c03200c41100c103518009000f10070350600c0c090401d45801c0c0e03110540000c0c030a050001103210b502e00484403140000140b050f2001e549175041000854400b80c0040c082d25404000469150b0b030001442a002061803501e195295640a1034078000c3c10383d071034001c003003917000940b0005000d0540c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 570165134 1250 570163884 570163907
    0x10306050906011a040e19050916050307030b0c07020111061810231b0c07051302030103020d031b021818010618020f090a0305031c060506220305030a 66
    0x20704072102a42c030b424484c0003540e510500500b40110410085c08900124454144c100c580449008400d40348203030304000743c440071203004559910402c440030100e441084100d004002c01c3d000f81a81d14215110b00d01491401015241c1c0c01600094660841e40300b40004203c4128400c1955100c0c145048680d00503221203003d0b03d018842c00406464030742c0c00c0d1003044a0b03103a1204103240b400c1c1c221403000c1c00ca10390041c0581603804407848203103151001d540080405542c031002a1000b541881c0800109070941400400c4051040c4014401038581014882901f5014104140d55000038a20182d40001e0010025040440c01d4000d0981a1400c00c0250056448511000900100b144c44508076041d40c81352084140106c0c0111079140083e9005141e5030041d111002d1400e900c142c04614407441a80c401c842c03d60001449014141c440015511b1005200405019151400c0005000c50145248481084241a0b18281101d46000c02c007001181e0110a6035180c0700000b502800203030308031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 570166384 1250 570165134 570165151
    0x90a0f030c0305210306040b0d0602210108012007140d0305060f09040b010605160501112808041202160b09030c1503040b1e090709180210080c0d020301030605 70
    0xc20064010f01c94012281141404e02d09440e0f0441d6620002c101c068125801103d03040550b9011290202c0c1980c001056208000490f00020140c4800c600b02030301c0d0141d000c0d5816902d480e00403034104c100d04101a1042500c510401d07207800160911000b6540e000f4000c00091144020b040b1265405800051280c40c00702d5802c8600b148003001e0180000c0116401898421a0300040c0301d228040c2c0c02400c11040d08030102c1150130f0303891b560310742150802c17980ea101c820408600291109542e42c1451040c01800e030840203032503580040507021440160005000c540c01c4919030368020b20821040700240d80282c41c00402a40e1070050310312030b6015400d0140030340074880840301c1c0d03414104009061802c104540c035146545640311464031900250401c010030801c52130b61401601d001095500070031b00d00700603002c8071b494075584804507a108030701d010004044100d0301025030f44001c2c5002c41c01c0298244140350341d44181c03681006101381004070302440d20100000c003d00c0882e60040d0302c40e00c1007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 570167634 1250 570166384 570166393
    0xf080d090501021c08130204050103050307060b0a080d0e1810150201060b03060d05210a030c0801080316030e0d08040503010e030412060e0a12030c02120306060a0302090a0f030c0305 80
    0x941c00120b03115450303521481c480c1a2039440400c1c01c030348034581c0181c0c030150614001070040c1c0d4139800103042d50341c207900c00d4034282d002040e100d003400345038403070302c000308404036001c02d0390302d25004409480341d40041c0110f041c4a200810b02c80e560b101c40c61004041d20102c0100812482c0c42d0300b802e0011421030240c0100d4502642d001c6007038500500c04c070402e80d4881804503007559102002c20100c08a049800c844c14026041c00c004d05036007000702c040340000c070142001c0d102c02c13102c0c10040c11030309512850b0081250748001040109000b0007100d5003510200440325a2100605003521418502e000668201840b401228240706181d00a80150b071000ca00a2220504503000ca544d240294040c541d01942405d00b020001210790f07010840d801d490034187c0701003005507100c0c2d460700000118564080b82c0c81b403d200291039814050032031003d144d070100c181103003850b202040040c006c01a0301e1090603030000d41a801071b6628000340b030082a0a060101c82c99441c4d1925030303151905440700f140e0340e109 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 570168884 1250 570167634 570167639
    0x714060411030105070e040e2404330b0a150e01020708061015020f0a0f021017070f03090507170601060305010b0702060702180f07020d080f040b07090f080d09 70
    0x1418043c4030b0017025180d40d05100c0b1500d00c0104002040c8151161602c0c0c80340c5a519041d062072141d00c618010801c92010040c1c0c5400c0c14290300010f03e8a655510340c510482e4564041403042c45922000b42100e400013401e101c0200100d1903001d480d40100500140000d0510b154036401100440c942000b030742540d001503580c9000d1a6560000e44032102c0900e841c0f03005001c0205c2c0da40d42d84110718894811030b216241c000040714280498440140d425200c41d6824805600b010030380c1040c03000c5c051a0400c1c00840100080600c280042c0c408000c100e14202031070b030034030302c60b40042a010750042d083d80e840554624000e00c401c180140703000710a00840000203090340c020f20a01d8126002c0d0030980b49410207a9081184a511070b02c0d00302e902000d0145e00312400300203900c07039610480c403100c0403104a0a00020103840e1160403e1004200401c61040004003800d44900640003030344010321900549400c4400d80e040340d21504000761909a0b81d0f4005824100010318500340901525600f50712074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 570170134 1250 570168884 570168889
    0x12031f03140f0c090f06060f0414041a0108041e020915011803050705040f020c0303040c030c14010c020d0f0203060f01050117070c120207080a0503070510091203020c030714060411 79
    0x30f1000701c001e500088103400504013103c050795543c4c4c0030f48010030321403800c3e10000b07070040f05810070340203c0e62582a640560b42c150a0910413024400031b0071071079110800d040c900080c049080104020701a41c0900d004611104006030607841050f801003d500f05450040312100d0109180b404441c0001c42c004603074811044541854400e40350460090700c40740b420481848064070122001882c1c7c11303420019544050804c0c005940154424522500c0307603455070604004290f41e6411018803150a00344c40e441c56a0000307040d10740a6030544410100003001c0c14500a5561600e002940500600d010407150303200c8503602034103a80b02622042c10014002812180e101411528803020450a200020105412482005080c410b0384100c41180c0c1d2120f0503607051448081080b62564808200c3c1c00821a092080001d0041a01030070019071150f41c950007083c4803403178244c005142c0d00040c1828180014403c98541580018032a034062200c02815640c814040750b041e11149001005003240e403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 570171384 1250 570170134 570170143
    0xe011a0901230c06190c0203071709100f0212040501230405092505031302040f1e0911030f0c100c170a0807030b06030105150d091208090c0312031f03140f 68
    0x1031b8540d004608001e00c0395290202c0801804400181800900020046985206540c0b441c041a40e40340707070910920801c064a04442e825030f1203030402c0305100a20141e64000700694440846480014041a4951240450748656000150045283c0040100ba075000380c11070103455100d900e40720005840000110b4980c00156008121403e00c82d00c00300151a00e5045600c80030411a000242d2801ca407520000c3c160b4481550701c0f1440c1c851040b2800c1c88081f402e4525440d80a07409882c02d407804200950b169500b003803500c0e2085890b002c00800851040ca12508a00d6000407640380f0341c0c2103020b140f01d46070800455000000c0c6040c0008a51030f100340541d01103840003921050070b44e401c12007040554400001030340340c001411b00000082030380c079015555425001e00c8a82180481d002030040044d50020f0221419a00c1200c1d200350907240054100ca05001e4807856685030349071800d08042c120769182c52148900650780b0b02005100c10041e500091141030f90071641c0703449a24015a0300c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 570172634 1250 570171384 570171401
    0x9060203070c060c1103011b030c0810030323040b04090b06070b18280323030a0c0e03031b0601090905150a02070b0108070e011a0901230c0619 63
    0x2500300b400300002070061580b2604c851090500b0f64800c514080401d0841f041c030a00800720b6036800c000c4035011a054031580e16205802d2500200d10318010b00d500c2600303c1103100090400603440422481a00c003485402c00381c1031040112075680da50f80c1402e000c0d9812078007035900054580003014500746451000c560300c1e41d9001c41c4080c8107a50b00e540c00407080702c0d000c510107214001e8112030405205001c1c011040c45080341d070900c0030080d490030003c05000d0300a903401822420481c02444a865100540c3e038844074109021610307004000c011034943c0c100b04070080c0c0521010401034031001c0c8251800c00d48034103490480e10180e985040722030955010b0070002c1d0130b503080064003081c1210301200c140e40c08445902c0142c94510a03550303162200000b6480811540c110003c180314a240e40c02c3e00c00e0050440150345c480a004001c01038425106005200d414000ba800701034881c01440c01000d00d160b040070801c0c9445000d100450f5031900c03170440307412141908504a20307801808a11603440d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 570173884 1250 570172634 570172643
    0x703050708010e2701022a030a020616020106150f080a05130213060302090117100c1704020310020d0204081917031504060b0d140403080c07020604090f05070906020307 74
    0x2200d0312842c078242851405021501c1136001401201150390009000800c400708521006042d0800a4085542c0107940301203da030342d0303800401c003007004241c1c00108150003030340c5a44a0711030296840000d03070050809602107076840c010300f404400da6a030030400f4007040784400e858030302c01555244c0d4130404607101120b032a8100364444502e03001601740304038407607404c1007030443c0081e080e41c44e50000f43e0700002c240e10079000241401070030000500240035402010040c06010f2004c03c030300d0b1002074a0002c0c002c692203a01442c0f8070009055690820a9201403415000219a91441900d000c0007039881406030300c0d294400e00080c503040040a240c40c0950541001b00540b150300d0a030b10309003840d031001c1c1021140d1914184240a00c2e5039511654008001c0038005944d5024001c40d05815500c1180c0329016000c0c20000f0040460f400010541d0702c582031214144d40c895407032001a001d4020760f00502a001e1600c9100038140c1240e600060040c07000342c0300c0703400e500c1d51450704a0b030703910501000a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 570175134 1250 570173884 570173909
    0x26010f061a07050106080601030602070c060c020904110402210a060509090d050a0c080c0c04060e06030606040b0117010f050a0b132624010902040f031b0e0f070305070801 75
    0x1d150424840a0140e0a10520000c103119a50302c01c098034041080e08140c591541c00a105010003908420840040c80705041c040001070007071300040c1c2c1416005002a04410b030040304d0030284e54440d4101d42551500d00b940c0301d8880340010305486030803012502c07506513a252001c0491689010641c0a2044010a00401000a00301c1040b5819005400c112044c440b2030820903002501140103080c074290068011700070940420100000d6a03502c2d0b1009030010307a0311041c403079103403404501140d00100035180403490501440049501154039141d5040803c20040045801c041c8000b0706070803200201c405c1608a500c5101130070062044021144403444803404c204142042ca880382400091112084100c0104511000b810504028030712078031403820804000c141d580b500c03a024098120f80c24110704003070801403940b24881c0517000c040c0a00040408100001e01074039407050280c540070014140742d0400403082c40e4003440546a01020a0400d00010400e620a90038581214440503002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 570176384 1250 570175134 570175169
    0x3010207020618041d01020a0305060114070b07180305030d05070e090411220f0c020c030a0809060f12160f0c110a0b0f070213020304111926010f06 65
    0x31030305401078000c0c04d40140d104e9402154681c603000c07584d84154100c1d8000f603030301d0142c15070040860f03800502c40c0c2d041c00340c2c0c1c00c60a0806100c0d1815503444d5540b160b030303002994894680c207440a88840011108101204da8084100800840603205500d80ca120501ca03540b500303901a00c40e90042e411440e04115400001004175211018013504201d0141880c0d08000701000322001808000d490120041e48903d072256400c3e9940c4181d4007204502e201400700c01d0a0800020346800503c10090f00001002c19001c84941c3c4004c11909900800c40d200c1e9950000c1700c4030005013003001c9a250140d84103010701d400d4410300a8492001c001d13070694604032804855581c040d100408001110b400455051000c2a802c62800003442103882c12140640c44074654810030154510200c80c00042c10b0040c014070000491035840c21800d10422513408425001d110303048120000b2b02d41c0444140110701ca0043c00f041c07801102000c1340c041c0c200c0203000ba904040c0b003500c203840d103911032071220b50b2401400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 570177634 1250 570176384 570176407
    0xc0909020d120504050402121e2503112101060e13020a03090f05010b03190506010b0c0a051c090e240307090501030b1602070e0c1e13050f030102070206 67
    0x7a60592600c2e802d1041c00d103170b142c1c00802d04a800c8540322411b401c0300386040c01314510901100d03e5540d00403081050307491070310030b01b220641e19200007100c8003420340070004070b20b082c000e4000c41c0040c07040c405982d4803089403140b816030518140e100c1c2c1c4148054000049403452046124a07400c410190000e40b110883c114408000c2d400140d504003090b0741c0340000000142c02207040040d0398014000820244c400c1010141820300d10020400c140c0c040000c0000042ca02166050448190a0105480300400c0c1141401c2165a0600400a02800040c0785c10313013100e10300800b14412503a40e030001da15191a41c1c8182000140c403841405001c440e01103106519010304005c0302580501940c10542e038880a0406807407081e01b0488907420703440100702c040e50885c103540c2004140c0344020301a0f9441d0103521034500ba0f010740444002100091501903078142880902441e590345034009a41e0085910b10034990361260051601c586c3c006550b4583c1d614050003910400c54004119622f0320004064 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 570178884 1250 570177634 570177653
    0xc0a0213020403150b040c030b1810150201020a1b0b1302120d11010b0613170a081216020601050319020d0b131a1b0a090806130c0909020d 61
    0x80c014280c0d5020440480040e440c526080c03162000700d2408507110003c0c0c0c0030001941c04086446003018a4030300390240303541c0d0b03440c451001c00441c0c5401c110346854929845400e42d00b1900316100c42e0084010305100075605500402d4800e889954007070854003000c1d081128a1034064010708500310101c082020710082c01402416a4801400288a440741444480c206003000c01c000e008a1804484140074902c00c1c00740001c403a41c102c4138189004140d00d2100b9030108035001d07544e10f2151091742100780100400945401a400a1105454464001811020400441ea103140d00c1050b1840c1d2000d4600020b0209d0507520014041e005298036000c2e6556541074626060742e00c2001e00d03d0300700c00302c0c045042c014000d50b05080c1c0303d41a0031050070000d160140c0c05202c410220040d00c20880440003081c00d4035040c000258109545e20b14154003251010401e8201c4480ca00400c41030008580400d070703071a118a441880800c002e9680c9691640440b1100f030341c043c1d00440a2542e1300300040305800e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 570180134 1250 570178884 570178909
    0x9050612070f0c05120403060b06130e09010b180702160b16020d0204060b070b0c0705150a0f050c22050a05060a0c081206090f0601020d05030603010b06070501200c0a02 74
    0x30f0680c41d200e00c03e8603200c0c50040c40d09034900c07000c0000a41401404401e00601681030300655069140c003006504441c03000c1094451301c4182201c103408203503000f0b820340069420300001000b48803480031840400d4035480042e5012030162050682d2103c5c00304181041d081180c109818190400380c0e040316164164060010032030b404824141c40100698441c0704440c0030f00340924900703849000c981313032080c1c011501034442ca601b042c007445450002600022207100302c601c0c2e0001031040c2c2c0c0354016400c01400241564041c601c0c10001000317034101c1000083c104040e1040c4c503003151140c1c0359105507180c010320b0050703d030429191407081c0031500301080103090100d864a0061015000da403158142504503030a4100a00d148900380070951800580c0550404411400e1504a003000c1001079a100e18010150040c000d0100000341266401c1d440b04961b81c901801c1c0c190303980781c103181950007802011001200701070403842e075102a0701064151400b10710143c1c001c2c810040c0c16003c2001030030151 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 570181384 1250 570180134 570180137
    0x21f050705010501090c0224070f030b030f0a020f01170f1320030c100f0809010204080714180f0106050c070f030303020a02010b091014040b10050a09050612070f 71
    0x10400c400000d182403190500814081c0c800240092201c40020b00b403010b000810050114142120140c1010820707001d60400c810b800d1401c1030b00002c03281540544030008034543c0c140921001004044030200faa000d0403032080b54a580003480300c81c01591501c1c0284108541160741b80005960025140071654100260140694101ca801c3d560070034940200c001c8194000826100c1d44102c0c1001c02c101c440058080b502c40b42800204580280b8000342a1a88010404810b01180c0715020a5048038040c0110206442e0016110504500220210141c06000703020a02e0b000102c60b03044a4207074081e0031100c0113038400341d1900c68200c032960810021821a4040d03804006504c0d1071450040b0000d41c0300e91009601c810900e040a07084501c080d00d030f1800b441003e010040503104800714082599800545204a22101400705004084800ea103079001400707149401075494001c0054015100e0a58076458800e07103802c2401202c3c050402c001040c4d100b000081644a4041d10212040e000103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 570182634 1250 570181384 570181387
    0x5010b04050103270f2105030606130312020309150a08040b0403030b04091a070f090b0a05040e01030c151112030723040906050603060d080a0504090603121b021f05 72
    0x1141c48041e61a08032131811a21140c43c1c04604042140b1490b040d6900743c4403407040748280702d072000090032a00c80106198440c200005500610f15074510445001c0c541010869880c89400b450182d601d80c071514040d1f00c11015400b80c1100b200140085414014032690703804103e450ba07075102818143c0c007a02c200c0c10300d5158090096551214410082030901501e081c44241303140c4c500c10983c026000c0c002604000e00e09144040380d50b00180c07480111402e2054680c0e4419a4003002c40340c80c01a60003212411004100020134072680d408218191102c542d4840b84107010402c0640300010380ca10a440c8507040600440e0f4054203200185a002403942000d010000e4100800c7c5030148070901300e0000b88001140c1817241d104c0c580f0541020704015a507030742c81c60403c030300007803001020103000614082000800e85803081c864029100140744c0018140244e50f02c0c0d01d410001d92000c0c100002c0012605c0954010980007186034500f141c1c5c019101c80480d5020f00d01510000c0716407401001440340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 570183884 1250 570182634 570182681
    0x40f09020703110105070c0209060306040201170606120108010207020a08160308070c2d0603060303090506030c09130e0d14030604050c040512070317070309140d06060608090d0305010b04050103 85
    0x43c2801005e10507141c0e1703500d040c402003003071040101803407004c0c120340c0c040c0d0300110410005076004a03d043c0c10840c00003a124aa0b901d141c0011054401c0662001c84010000d0000450881c1500500300381031007143c00381d50141d1140d043c9540c036000600b2040318001071180c1000480d40a0b4002c1c5140b034040c0071206980c0762607410b880c3c0b03080e100302d400c7c440d04610702e408005100c18054460010305070318507051118504e152001410350600380140d82c410703a00040402c1d2404090802c039030f88002c01400c3c071318000189580c040001d00c941060501c850080c000b050713102c84c0c03090703180310041030754003c00ea41547c840070140001030000421040062200704030200700c65440b40181c0b0310403c500c0f4001c0566900314505a0348840c4000f0350060114401d00370b01d400a0303001116001503480c144080c1c4000019040014103102c000c100185c0464a0108082005607104a50a21503031003d002c1340d40704101880c049003203810034813441070248c00902080c0010b602c03035006001c4400d140003c0792261007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 570185134 1250 570183884 570183917
    0x71a0a060b0c060703061403072711120a0c0801031211060a0b0a05060306150309071203051b1609180b31050703031b0f03051e040f09020703 62
    0x2d00050858000307610007020440500c0e0b142c0118400313056908001580c1c80843c90110355648818000c041c08148010303422040003a120001c2c070320009200205000242a40002c142c0b150711036040c41d442692aa0f0000e40da24a0754055891500f00030394541d4181c0e861500d038450b842145005210801042a1050707203e0502008128001d00d489280010300c40f1104041065000c40756010501404082c0200a5940e172800001d046000940303261907a0ba541d6000d609003022165040500c05c0164040c1400a15a0280c0680542d40c901b10003103c5031800f08a085036600401e820440311007002107002c4c84000015042229030403202e0902080e10f0100e65a0001c514800f210240c0c10300d0078412880c6156075641010ba004c4240859039600001e1031526113a0f1942c040b400080c00707001560383e1600d80402807042145201d074210311000c0c4040503900d4000c105a0118980d05905c103220b05000180c41142812a011540604500ea10300c0e4a000a0140650000307071040e014851132085c080c20b0328 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 570186384 1250 570185134 570185137
    0x51f02011506110c0a03020f1207031a0f060409050705040c030b03071503231302010903021003090b100e1b0c030c0d09121101030908090a030b0912071a0a060b 70
    0x1000a034580e100d5000020300098a00384008924500c1001760400030005a114420a070500c4e0b00e0540b40003403001ea408260601c0c2c00b1859200810760215840c0850407203209082607802040602100040f540381c802c104819154481400f03400c60300902802c20091403d07502040220801d030801080406480001900b0300d4081d5025440d0f42003500120b018451b4184a9483c504072401030f03003403180356003049000101c100240111b83e4201019840001c0da809156018000c690041c180a40091140c03401000341100f440200d035554212004a65007411250103c8151203152504103c0e603650310003003032a03520081c071240c1607550b000c000e0710080540c144014110202c0c42c2c00201603103034010038001c0002c443d80d848000720805040d0764a0018140558520604601346030100d200046800c02170103512442100b00c0d401282c0346800010031a000c402984128131007810750340460300494a848540c4900d150007007583c159140d82c0207040e01d081c41c48640000c0300203000102e080c2c035604807101300e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 570187634 1250 570186384 570186389
    0x4091509030c02041b1b050111030a09060606020c10031a09090d17060d0803041713081e0717030904090803090d03140a0906090204050c0a0f09051f020115 68
    0x30b0318105002c400d5081171300640f900c4100c0c89015296030310036600000d0010b10510160b10000081d140300c0d0040c0407094000d0740c1c4841c024450350380d5900b8081c040303400600c54031a08858950821100103081800400d0120f607482000c2d04410368010131500442c0241043d401e115002e85210a4001c41c1d5154401d20611440849001b04080b5558010181420303011400003003020344034408110003030300c9a414034043e0550143d03040da1262a640781c80441c1d0307400741c80341000c0740a01040c1d0030920046030150030204d9a6080a4609030041907045005040e818449a4243ea0100318100071013103c103501000c08010f034000340c4c2d050905810014040e1480b90f4410382c1e00f014007100b4040d0b45401840000120704150404110382000d4a4241d8602030005109125140c0c0c0c2c0c03000386003400402c0d00001c0b4035a034010410030403031400c0040303a001904103a001500081c0307640a4003004a0089010b00180d070700c0241140c0c00040c451120300d8981040040e500d04554071041600440c02004121201 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 570188884 1250 570187634 570187637
    0x7050a1a040312090f0206030903091e0a0501050f0414060d051303030501050d0309180e0a0b010608010506070c0306021b0303040303090308070216090209030f0d020c0406230409150903 81
    0x941071909000302140c148090400c59140b82901c03a80c001520250882d103040d9040e148030740c4076a50704007418114000c440070a5001000324940c403441d514810b69503003100000720343c000d4541d901d42c3c00440701406104000044100200411300003d448142c030121008002400c45190401030140c0c0000d0392002d4170b0030034104856071555410960076021f007601608041d91000d86440060701d00800c0c0b124640b14083d122680faa2950344401c3d0690000010607481e841107a000244030f1800d00c0c1e020704244100740001d0342a10003c40c80345007400c102d51020340c201a41400c01ca0079500c62000a600c181840c03ca59440b550715825024401d101440c46903000b03407000100f09121381006040030700c0003003c41d803c40d0030003001c3e00030b000c072104134120603941d05100058031110b0003408645801c61040031840940315040781082410f60006a143c1034240030354051080c00d03540c0800a1101e6554450312a02031101d400c4000c0f40d080603804846514015160710150700212002102180c0390300d88246c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 570190134 1250 570188884 570188933
    0xb0a090609050705120a0510082a01020105070c062417010f020f0d1d010207080c0d020d0c0305031315020d110301080c211605040b030106081207050a 66
    0x8880441485110f900003482d061241c0f40500818580c2c0943c03500a1407940481d41e96800310306070b1445c0705489409400964100c1d15802814590f080c0300302079030030401e00d03500e104101041c000d52040c0611030140308103031034240010701950b58101c09004120100380d2201000c0242105659042c40e00100400046090407156003100703007481c0c25a891500700100080c010812903003214901404c86410700c003c5034001820021100001426842c5458020315560020800000f40400c0b41d0041c02da104501d8110f43c1480380307202c3e0070398030740d04096544800304071000100b10100f4041d0008507803006414094840441e51581c8590f030070642e50008014250b0b0119508541c04e845d40301300c208440041508904540c540500c00e41c1d52010301c4685406403442c000d1401070340040403540201c070708410b010303035070187c07001004905c86000074400c040c85a0308042e003854183c201803091400703850b41c403009040ca219010202d000035900c200e408440c1071140a006902003140c0394194481951503202a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 570191384 1250 570190134 570190139
    0x70506011508370b030f01050601120c030e0a030e420c07030602210907062f0c180708060f030f0312100f0605090409140d080603121303150b0a0906 65
    0x9450121b05c10b52041d100da2400050141036a04409603110080300c00c040480c0f03c84503a03074114090200e0f40701c003100303900c02d4030407200c101030304908a00c1e0040e40070b490417400d540344014241d2450300c8041010360482200c1c880440c10b680d00d4103030303075514180e00c400243c540183d500800e441d10b000c560058903055030120f584046401d09015006010054541c0c3c09007a0030109446500c5840d20301c5408240006098a203859910101c2004145d0122003464060080880e2003281c03034030b114031526481042c14240d0740e014624815580c0d030103601030769600c40c80c0d6554241808408214161190741c14400d605c0b40440b501d0040009000840c0c0d950380074940360030092210301c6049000d130400e0340755030741f619814001c03072358040155001b40e40211408208401c150030700c0240005101c00c0102c040c090120401c1c950f0f40c01a184c40d006002c1901100d0000c00c0c2000d21111600401d50072010301745100100304041030041e804004144a000400241c0e5402c113400034a00c41c04a50090a4160301e0705800c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 570192634 1250 570191384 570191389
    0x607051c06181a03010e070b0d06030c0f09050c0a020a030c0203030f0f0409060641030708041b080c0d05010e030a020a030201060609050d031206050411070506011508370b 75
    0x420000000c250001d21005c000786103101e0325160103008640d01d44c9030103c0c0c246e04102d615000308008603003241e180030703339942c50344079081d0000100d0064510310f034140310101d0341c052652030441f00c03c2d00050380034100d100902d51b8201c0c3c4144a00d04141da00d840107001500030f6850440040202011980c1010b130f80340d01d003011403002c0da60254005c0c001d0040c01010a10401181100c007100e0381a0705111141a40c4402075207002e002c11200c0894803030401004000406400041c00c074002c03800b0b20b02e00c0c0214891030034503549621150050320416004045003401b1400c02d0140000c000c1d01c5040049005094501402c0c034640141e5003101c0160f2140b0404e000f41502842000068480c80c03130000f0486003032002064100324441d000034104030329201c1040078140c1315030054014003c018010702c850009602030304100d8103c2c0d0400d031090300801000182c04d603074001403121420900d88500d107440d07507213100b64100070540d0ba04035500c2528a481222031541c01c00c0019410800d00140040c7c210220b005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 570193884 1250 570192634 570192671
    0x3120e01020606090f040327030303050405061b0a0e060c10050103020a0806070206010b03060d0c270501080c01080402030304090504050303070f030b03060105060d0605150d0e0607051c0618 83
    0x1189000c0c04d1408240841d07041082e1a090b071194040c10a00700c40e48030b0581e400c0d2104803c0c40d00e60041030140d00044201070345500b082d40110701031b4048490603243c407803c5100b0480b01d0795654840200c1040161a698003900d40a45018001406c0a04100244003214200190b20010b00c14956442e03006204525015031200050710840000b030580d441c00490181d6140010301a580c000d50000c00010380a030b440e0f41808840950096501a2013a80c8035507048002c803000801e040c0000c540c92082841540a10a8038100c44181c0010314400c0148001901e0306600503001742c0e05404104008541d680650041c05c2c001c43c801c40003155a480c10390802403802500c24007900816080002c641816940014241e0569a040341d0180e5544031000d48400100303050781c07240d03070016107850511852803134990180c0203a00d250032040c0000f40a10009a0321440c044031090b0110b54140b00c2d00320040d00701c180f42c40c05d014049500081c681e0721110344110040c0600e0507140540d44941005003420103d45 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 570195134 1250 570193884 570193891
    0x311090c0c07121e03020708010c1416030c08040f0816080c0f03010e15220f0f0203100504080903152703090a1e0e01030b0c0901020703120e010206 65
    0x5820304001c008a00d007a15a4120b21905480c840201007110501403049940e0201c42800c0d018481d02d00624503000c1d445403420b00c19461554640040700320707154040c690443c0f4203191407480d18a4a240d008000900c084480025400c0048800802000910440060018060201a40da1154a0800420300c1c20007150501c01106a806008020401c0b0001c1e0a4900d12800c68074200403002680200f401000c41030420b603940e202c0d81d10008259021194a94050039910720300300400b101c1c3d54609100420b001d40300400c40c8091a8055022a1701c0c0350b08043c03118401826101421500c0c0fa0705020b540040c2c41c142c91144e40050340b5103091a0070404040141d02e681c0e000350b090301e0f01d6020380c001500c0307110a01031506844141100000b00034402c41c0c0201c0f400402507420a51500100c800c41c14001580c00340031203030070700d0200304250411203450480742d029040b03900780d41d1103000300030300380d04405450382c10341c41150804800250f500e0100f011202d01aa01c10040b9180385000901e03218014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 570196384 1250 570195134 570195151
    0xc0106090c120b010e090103150b0402030a090314071a041110050a081810021809010f0513060506030403110c131a010801150c030c050a030507110102030c07150504050406031109 78
    0x401490217140c503184500340c1100d81190b2030000040f000e99200020b40781b100700c8142e00c18400420400107007c00d0f031040c100640280c1c0c9140e042c03014041d01010390b04c40c251025244020080c0103070080400320102c10350040c0301d09644401e181d4a1300210350b90407251171004010803004241e181d42c0c00d07801201594401100d0086a04003600c02d10b90545400c001b10621251507000138401c000012192001c0e2201c003400385c0402200d6a50b032042141444031400740d07500c1071010762500900c00101c0c2c003900d0309942000b452585541c845a4082c0d510f0308283d40c0d90555170103a00400d0b03040d41d0b00c83c2e01e00700e44d20400ca43c001c40c004000b8a10303209103d502030f0700641442841c0c80180440340002c1c0c1e41e0f0303500b402e0a041c03450b540045800c00f504c8503a03c0d404c2c020942c2c030070410402c04040d0701c0b00162220500c00d082606007425000c00598681c0182d0800b0942640720280410841c41125201d1700e08c91128204240b074039450340041403d5a83c103070070503908140e00409c433155038142207014503441600c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 570197634 1250 570196384 570196397
    0x20913021c0c05041208040806090313050105070c170f1c050405040e0106030c14010f09032f0d05150708060105070803060301140403020c03070b0a02120c0106090c120b01 75
    0x5221a80d01101410007298a60381d40c1e4094858490b0040c030840d4040c0c11951460442d01d1018600304415038481c2c000c021890160401103001c1400000c10340d21001d082c0010794092900380001195681c2008600342ca1a0254800000e40c40b10b94201c6814603041004c040d00c0c0303847d845030032607180c15280c815841c4c504a00111002205d0380c44070540d0292902210003140b06a841a40503000d4078840d00701421211103044001500b0b00c020040c91b903681400c2c0c0b1050f01c90400e5002c183d802c003070380784000341040011500205e40300e407150b0b054480c01400b2111902a542500010581c803c40c02c3e0011213155210410018501221005042e4442581c2ca081c074014074000000800c070f4000d0f100300411500340070000c01c4080d40d081d0826040842e841900c5140761801d814025512a00d60002034002e0188803008221451a0340c00c89645500e10b400034134522695441c0c000440e80408003850841d5a114400b040d0701503a405038a01c00d1650741d032018501ca0800050f02c048035071007401e10781170018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 570198884 1250 570197634 570197647
    0x2070f050c01021b191a0d060b09090a021b0f0f12131703040306092406030201020c0f040e0d090e0f0103050a060504020102010209040510082e05070c08040902091302 73
    0x403101d5600340203900390b825250800800707400f45e1011240c2d4004502044003492042d02505005010b020400105041445840d42c0c40090495074410a0030301e682080c01c0d00000b5619142c0c1e5001003100c1c1d401310003203480c80800b581096090690b0021088225044184c105203054001c004401031640106100e92405000d2016040d116042d4400c1c03001145070101c421200080510607180150b80140041c000d0220301d1500309600e00030215010072070b0960005d513180540b014440ca000340c0354182c00814600c0602c4c0c04114101880365941544107840780302c5e90107024414007100300c4100880d20707601d808034240314113200c1d03402c401020108804440401080450000500c217000745400400018880d181c90004030301a1040200c11380d0050309100c2841940c880b0350003510200c60602c002e54000400340b41c0885401e02141d0104051100c444103d80c4488000780d0041d034201000f03052400e6070303280310b1f6203d0303100780c1140e88000d42d45a4003051034151414140c50030250350f800c0340002c514000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 570200134 1250 570198884 570198913
    0xc03050a0e072103110d05030a0f052a1308030903010e1b130609050907090b0312030c03070e180103020f090103050a150b041d10060503030a0c1502070f050c0102 71
    0x11030040e40b901d860385580030032005250213114900300e070354802c0056070000c1701d072508040c2c21a070050340c9c01e05906250064910382a01c95104541c0100c580744002040c9510300140242c0c5c0f80344051402d8154441040003501c00801d106081c0d0081a00354040d68607840d01904240c2100e081d500781804075088508111203049194990314a991000c50381c030300301c4094203210200205425040781c0c50750b606d804d040c003144650002d8101c080b5200400140001c0c0405800d05885034280b600cc2e100b404800d002041991120340091a8000304915100031034640d16030014040c10b070301003000c2d08503410101c010f00550a00101d9080841e00c00d96003401554959036559a0300d0070b907010086c0148498984c01c60300d520300780d003051032030348001001807004842e404015207a000075207028490364030411100824200c0e1600412007103030300050185083c01640e84007a00e8001003894100c6500307041001d1200c400510784090035882e0b0052404080c404041d00e0400e11308006542c2c500c0c1550b010310b60381c0048c00c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 570201384 1250 570200134 570200159
    0x114060910080c040f18051b04050f1305010b0301030b060d02090c160c06020f0708010603021f030603060203012616141801080102090a060c02010c20040c03050a0e07 73
    0x14402880d02e00040e603200d186880f0b90b400303680c0042801c2c01c000c80340000c001d28020f01d1034400c8940c0850411694981d5070180c01c0d0f40407411040c80e0620030600007042985004041840b16030000307070101020705009c06080342120307000d802c00110608048014400d0010703041d00303640d22035820f4458140038055034002032030380940245000b940300c40c0001c00007070054920ba844107903594001000c02c00300f42c60302e80c081c0d1a80008a0400c81ca442600c074001840c5a0502903101200e40161845224086c640d149109c1c004002e5201000d0640f102d10000001d4403910065000700980c8188041c0e82e03203180b11440103c0500c48100904d039119600313075400113511440d11804c440d214105491020b1215012417529080d2540494182001d00300002d01c041c2d041d002050901c2e011a0400c80b5140c03140c6080c0c514100c00400a800161a210403400007086440e011500d034040b071070704400a6032558000b4080d07403090204100029103910900c9a200410300460415461383d00251049905221400012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 570202634 1250 570201384 570201409
    0x70503011809120f03180c0603020a20031804150e100302130c030c0507150c111006030b0c091528021b1806040e0f010e0601140609 58
    0x420300d00684035030112035485501d2281d4003e5948030101c54050001c0c02e100d9800f108600844c0c00c00e800e8000c0304090841160f101a40709061744c540d1820908100d00940286030301c80f046c0182c2c100f81910402c0380040f018000c201c818006d640d0341d240740c00d2824002100c2901180140c1c1000c449121034015005001c06403041140b61080d03c1d80c95543c034030710700719450740042e4102c00c07013a00ba51290000342c0c21180c000001e40e1000d01c140d82c000f000c11a4103214101020386110120f02c031800390070001d0703007001f8910902460031865078901401c0c40307800c2000c0c80b0390850003039079902000c200304034901040c01d500c02c1c004803240d802c00c00c080000c5200103284040c403644001e800184a0304001b10b0003c1401e404452030b02c1650000031007a00070b0b50746c1e1024002070042c2e01c4010f076035280c240b500c500d01110999000c1c02da803541e83c0700c04060201400180c26810100c0c0942c6400c0f840b020024403800c03e00c0160789000304a6945041c107510b0391040d441a4142c010582044000c00b10303120b42e0901001c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 570203884 1250 570202634 570202649
    0xc0a02011202040b0417160302013216050105010f06090e2a0c0106080a080a1b0206180103051b030c0a0c0c030b040308060306040201140721020a1202030307050301 72
    0x6031101001d405400a1140d9080480560400705000c20040d42c00b800f02480c0854078021205150210000701e480c520030307444000c0c0000c00403c030000c9030001e10b550080000341601c40600c80c0d15046007001d280c0c4d400c458502548601e4001c9204103200c2d0900606004100c60540c008600e030034503400030000420750080019100c00c1d80c1c041a5400381507460004025a50042010341ca19042c4400d20158000801d56806608250001c1540c0d2004a050040e0640c060241490604502000e88e0000380d5008034000b000c96060845000d6180d40d030050021300d981550019880c5041c078005004c81d580600724040360242e901c20000181450380851b5002085008816124081c000e011140c005e0f0914004000007040400001041110b143c1140164426281c010655407032400303165075690100c0e000380c001410414080210144040248503031400340003540c1104142e94026412203000c1c0201d00c0c0143d002132915010b11000d04408215902688003551031800e0011008200780818094081d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 570205134 1250 570203884 570203897
    0x610030c06031a0d0602040e0a020a09230d05030d060b0301150e1903030207031a04110909010b040204030507080712030806010e04180b04020108090d1b062019050c0a0201 75
    0x10902d50074034035030359500000a103144c44143e034500d01710001e904244101c0380340f81405000302d501d4403680e0081d10814040c9544c0c00c518607160800860540c2e0240c07000d120f901c103010712141600d46618400c130034041e004000440d6100f1598500d007080f92071030740c00703030100101c00e000502440d104c10011010390b03491880d141401c4070300703c40050b4100085810a0b0341042c0000b00c00401c1640204000e4102d9005001141d0004040d1003000030459080710003c1c0115102100502c0310314140c0c2c2d00f903800c54142800000c5035900400441d0803644603410039120344e03000a504014040b0104903030303c00f034100011640959191660b0140c408031018012505000c030320110030003141c070b81c0d5000034000b440b182c103403100c4030300785d428017960b060b02c00c0d81c00f40d00281060001440b0f02c0000184000404200d64414048005014000d0441382c0612001c848413519400020251405051800d10010240f043c065641410003040050850707400c050b40d0074008240012400d103240070501c0c0d4201902802e041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 570206384 1250 570205134 570205151
    0x418020f0a08030a090812090102030706050702121803070602010b090f040305361002070e130c030302070e060306060109050f0102010e06130c080c03070303180e040f050610030c0603 80
    0x19207800e119089010180710124610784d1444d4070035010f10444180c04265006184403050119082c8506841c40b40568030400c00140050308503481107034800c06510565512602030306503807240b40c0c02280003c00f0360384140941049441d00348010801403d550008000d031a24020224111880041030b40060624100000e42818010011515060400790001840c9034599411400550344000303905405404610f45584d41d0800162a08505402c0d400901c016481e0081458854034000c14107402622494600000a0342c042c1c0740002451194014200907414281d1011101c10024440d621940c0402d05208141c1d801c02421010b99801380c404440707141005e40140d015140104000301e00f44181402c0205c400400400d00c0b8a251041c11a084a41d544105c0300783d44031100c4034055455049000c0420000c0c1c00761040b41040d1403041d04141032240c1d90b8150b80b00707041d421501a00c036a0341c0b1400c1d5074104074082c0100c0d0b40c04413401e0000390410b1b0964540512240c543d001c0c0c4814160340c0e40ca031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 570207634 1250 570206384 570206389
    0x207140f09070201020d1409010b10200a02120c181311030a0c14010e010206192a090f0522050c0904110a0908030a0e010e0f0409200418020f 62
    0x121400e1b800380300307002d01c0f01e1030b41c0724601c8405440807038441c90f05519121a0502c01d103044504000f00104690f912050a0180040400c1d100c00f40101c01042d41305440022005032584640b54540440640260203028021000e0000e110741a280300c1c001400d1403810420701079007a1030350111943c1c010718100b01100301b004c042464085d4011000d000b2802207100010b0300603000c400d03890001d9080c2e03282c0d0045403890005a81d584010f0706ca0b06540080090350b000a0030407944600103403a4245201001c0804261147c0c0a800d0b003103603404001043c4840510104112811940044c2001d80325605510030300000c0e07075200c15000f15000701031038644004c210b400a18500303882450310020400c000c0641038007156481c03035000304002400f01e040060300181000d0080140d0ba4410303403e072195001c140e8174000440368040a0003c16900091010080c5a5610381d0321401c2c8100348201201002c038800c5c2500c5040074170000c502140b0803070038080c81220303d860301480e0090440c0e06913040688004000300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 570208884 1250 570207634 570207637
    0xc06031a0429031513050309211b0919020f0409020403021504033909020a030b0a060e0603150d03020607033b150907060207140f0907020102 62
    0x14859405820000e901c20201126071034840d0282c1590050307040c1884840074591520b0140711158070302c00c42a0000b881d458000e505000c15a8480c034181e034074102d102000070f1004160052100f002041401e110f000200d802c20408003110340c0c00c5c03482490480402c0007d98898402000941d04180b080552070038059250180d41060700400724240d20745855401a01c02500075200981c810340c0303421150401d5041c4441200d00b5a070b08520340001010300c1040840344207110902b0403162224804820307051070b503809040005003140720030140e90380d441d81134000c054810725118644070f803414000400030030390401d05032084201e09448158036684da40c144c450b09039251403195034014040b9101101015400310b00304c0d1080c1d0310350310300b081503850201a01888942034580020342c452480002440d881c181d4003100000380540b003c5a8030a282034021081c1c696007518281002d500105040c000b040c4c040c80507402408411800c50060ba59110008071401c14804482c2c0c01003960300080b404580c804e40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 570210134 1250 570208884 570208931
    0x70e0601090e160e040f0b0117060d0f05030702041d0c030723060d0216020111010204051c1407060906143405190b010905060f010302090d0215030a050c04030c0603 72
    0x28400c11508508045120140500d04050740c0090046030082a41c2c61a400b11740f4010b60012f8000f018884250340d812450000480c0c041c0ca0074441031101000580e205d000d1164009040048406c90607602e040c4145041c0c0d00e41d481078400e4000d003809200c0c2c9030f01415051480b00c40f541d010845111680302003080c070711070303d41e041007005d00000b040800a8101201200040e200f0ba0301d0303040b02245070411500701e0080e801a1544030110801603007090400380a404000b0340500161070441c910308141602c4c2170f8030355000c5808240286801c1180791703007082490803110499040d43e8030309840d140f040361a5401030150b84000403103c68a0403c1c10040103007112402c1e6004080344c1862007a0111407c0705806024116035440e9058004222002e090160f6801404054001b40300b5030503030f9006401940180bd11149c1142c80c0114003800350b0340b5a0442d490801101741c809030f403400d103074004001740c800040403030382a0036040004000288840301000c2c100c511615002030945918142d0100a03403584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 570211384 1250 570210134 570210139
    0x216031404091d06010501090602030a050d060e0a050105040b040212010308070f080a1806050a210e07030f021003050f2a030a1509231003050a05070e0601090e160e 72
    0x2000d0b00d1241400503c03580440c5040c20115003080e80d0f03074401181c00d020f1500480f401600b0500076121814010f9000d0003504840d5800850313803503150020100360080840b6101c5502e92076800400042c28903105024190505031009c3d480c000041c0303400920f2240610008000b80000508036082c4070301c15408085c504d601c540910340e0742412000081043c515003041e2203182c55141c400041540c003440c221417405c0c0c11515020f80354460114151403050030340707400b20003440c0c0310212030182e071500b80554000342d4426146030060f03000c0d50050003c010240349103541071600c1c01d01485200588840702640c040141c0d0b5850032080480112007502d800203071601020080701005110111081d034002c469070720358210344140d070f0310f5490721010140e03034090311580c0c41020648a00e8000010180d0740d250b1021103182c1c01540c040d80e95503014640054150255019081118284040c6115055168108a00f4a040030150341451811104c0f440040d20f001200400d91405a40007805500e2444156100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 570212634 1250 570211384 570211391
    0x112a030d02210c0a1b05070816030b0609060f10051312021f080a09030c020d0320030c03090105160b0a05011409040512070206040f09090b010801021603140409 70
    0x48021002e44140c1c041003248405010200090084000b40e0548003409025626401003030300c104e802101400c000501030743d1034050306d180420524800c00032040783e0f401041128208038594104202102d070003400145c81064807400b40951139903218013560901d0750840342d025a01c50001001c1d00c8921440302e080291000707102002030000701d514040c0312000c1c000e0351038286078000003180407224007400c0c0c46000450040008100c0c804e81030303030013807040c3d5100341404040d00c00380e60000b910740090340904400241900391100c22148086c0051784121140d8002981040000c414441d240c0c06520b03a840d041080100d25190001b844814070000150402c0b0048020300f002d407a0180684400d001d0341c0e16294090b0344035005414203284a9101e03d0b00701c0051b15000014800000440d444140d041e030b4050f5042c80003107031080f441002d2030000c200c2181d0000c0d800041d03140c845200070059005855507481448141520311113440c5020080c2c0c0d151600c00c0c00f000001000d13071654000c80e00a24002e0f4136 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 570213884 1250 570212634 570212647
    0xa0903050d1e050306031b0607050f0109030e06031909020a09020a020a030e011404180219030e010c0503042a12062405180c090d03080a112a030d02 65
    0x100400b11070340303821040410a5078084600419141c0b884195132103601680021444070301940000c0c1c03050707075001c0010002460180c80e911480c0ca050041c06c2000016507588101c0f90405030400d070300c199031500980e4058218940010380011002c2c224485921060b00c03036614004550303c450b020b82c050940844219100e44440c403000790340d0301d50130f00100d0101e6011400d0041942c0031b13854009a00c031805003542c1c6802d0070031040713030918034242c4102c02226030280654002d02d80e6050840c4151121980c0000e003c0c40e1034001c19094a44d840b02500c24058100240404502c824051600606000c03400022200b100e40312103a100c403190303000c1254040d080c04020200160303030700b103030501c0c0502c401d0070700e00071750302582c86900482c1038032455030301126081d90030075103885448400e030b4403505003a1b52905081c80c82010441d003680c2800c007140002d20030010080300c5a81e61103110a1026604101d82c00c11120800045030341001481280200909c0014003034861b400b00102c0e8038080c1032550079503e030031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 570215134 1250 570213884 570213887
    0x522050a0b06030708070303030f09050a05030c070f060e01110718020904110405011b0303090803070f081605160204062d090504020d200d030e120c13020a0903050d 72
    0x5038180c1044400d2155a40400e500c0e140009009040d100c05401a00205286550950060008102c40c0d50860341751b80b00900842c5041c0850340c4018050405940c0c3d450118807524101056a0130010a91000590a000840c2d001d6a8818041020f007003200031071a0300c1c0d02462401c11282d00c083e01c003500c002e924403090304042d005004048425101440b4140c0d8000c601070050040d805098001034040c085c44905800c07818000d0203c90080c01d0004003248030f5150003906070700481e20748020032140014004103a60040303203a40e100c0c245103698840c007861101c0040840c403031104000104000705044400750b561351741c042c5e0002c18514510400d1200c0803007824003456100103032144000d0702c09100207845c589174040c592040b90f0040003400b003101a03554110403c0700518112850440401616105880f03a00318004c40c41d009884840c0c50190860070403503c16039602c82c5004540100041d4102a00c1e0b62001c0001941c55a00c0035071502e400400444044825500180043c844e04031940707a181d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 570216384 1250 570215134 570215143
    0x1c020c0d08090a14070504110903060f19090605071706031c050903061509062e03020714010e1b090406051b0708070201020d03060e0402012001090c0503060f0118052205 74
    0x1241c0030361f000d1104e10812819003095026a06807180c06030804800101404034005050f0350268078000002d80e15a61a004841100c070400b40c1262025a5001407100181e0003803c1e54007403030b45402c0d05a14510b017000110b40c54110b4220300440442c0d206c0c0044000700d02a5054405140010f03040320803030300e000749940c02082a5014001e01400044000ca13403035045c10006c9001c9400e00d082410401d07111a008001841441c0381e109080581c02c1c005000001d61481d20760380c00740703680e40011804415030000241081d44003e07200c8a5410140c01400940d11030260260340681c10250003e4203941d03403903840004000940c0254441e09000800304100401d03400500700d124001e908403460060108001d5088401d03d0040079170056100d80042e0056128880200c582241d00c06a60a210f8120340c1e84c50a42d09005000c4410380c46412082c0494213042055079031226038460010444c1d4036080028107070403006c01041d10010b4442c030015445030200300c140100c001c902501e840141441d41440da445 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 570217634 1250 570216384 570216389
    0x2010e1c061103071b0606090c0e090a0e10150e0924040804030f0f06020417010e16061b051e190c120c0506040602031c020c0d08090a1407 61
    0x1440c0c0102d501038240c0500c20340c1e00c20559a00d81c0a5414031102d000303440462180d04c02c4030403030303111039010a00300d403c0e01402e4036041a40c0c42c7c0c4003180f0b0050040100294000302000b00040c50251002070740c144c0019805607075032000400040d801100740104e445268a03410280111841c042440480040000c400b0519900c1c41c0c075851041030340f10b50324645090284c8010300000c01c240001e10104101c04114013005208460411040e00c1e2682c0d0a01a03805c1540501d01c0320400d01c0407a45100001e000d2800c2012024028090a0603240c4080403000c642c0c3c0203400410050142201034603070052007d9040e290400700300c0311207071a000540d600301141504100914001c28500452036006a142c00455907402845e4814103820100c4e650360300c4a072404160b030041084800002c064456100420240c00d60f640610340e208801280c030792604100b0b050103548984100034001e4030403008580344a1380101845c14069a40b00e070701d80b80749007000100f400f4200c200c8080c100c508000b03000513030804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 570218884 1250 570217634 570217643
    0x10e031504050327010203070303050a0b0904030e030c04021c021b030d0b0a1d19020409020c0c0f0901120f141506130c2001112209050105061602010e1c 67
    0x189100c1800d4020003001520304d902603030051202800090198000e680c3c440503110000540c0b21000d00041c00002c0290340c20f0700410b40108024245003803c0c803c4108214040d1829031800084c1140486038014100c1c805a240e41d02083c0b22070103e40c100b807100c010001c0707801200e88030f00c00602c650006207008145640702d008010170020352903000100b600528240c0584044039a6203810300340265648404240d11059400c201c042402d00d041c1c40507101400b4010000c040100d00081800860800600481d110708400c07001042404500680010348030381c000300b10b05e1090703114600300241d1008291502c0c45c85c0101e003002d0303100441030380041c0d02c90001204c0540c8803803a04500c0300c01b1140c1a00300c0e00d00250440c1140507144407020240c14503040e461000207100d41641d20300d9901d41d006002d90340020b503c2c0c5240c8449200d03140e40580c0c0507040e012002c003c80d515041c0003c0280c41280c8400340c0716040d86107510103580c007555001d4910580507290301c1d00d00d07081d0807410b4124142c8008c00c44 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 570220134 1250 570218884 570218917
    0x3040306020918070f200d030515090907060c0204020d110705010f111e040504020403051b030d1d0409120e1c2a09140106030e1b010e0315040503 64
    0x100990060b400f28022070060304c803c1c510700540e440403541c0180100300800d44030942d03416900041c10400110615000c5907400044908010141c02c40001001034094800c0000d182801403407000402c4030f00480c3c1032030802d0b01c0310f4015032020a0203030150f444803a099a19000d190090030181030700819216218500802281403407422810840e1807d015100450109202c039548604a810301000701c0703042c43c2030300c03800c0c05d50b02c41c00101640e000c0d80088410760404082011007000c0c4500481c007556044014041901e80d846008142c0035050040b403d4007503981204241b65200c0c2d41c0b021115940050003510310040780c2c0c102170024040c40340c000d40130b40c03110794044884407180c81841d54100d0340181c0c80000c1c840b41c20300d100d0044c61842a914803081d01c1140000341400140300701c1c8074500c06150204c24561410307c02904940440144190340d4000c9030550501c0304101d00844050750090801c917841000b00c9020074174210480009100190010b000e000c1840390010241020480194588 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 570221384 1250 570220134 570220159
    0x105161e110103180308011206060504050a1d0f030d0c3f1119050d1b0f030911061b03030a141605030f0618070c030305010f230111030403060209 64
    0x20301100303004513006000110300720010f01c44001c1e443c84021015020700e6000c19a9030301c0344002411941c0079106003074144d46e95400c1c080e540a404a00d0b8184903060000b820064102032820b50312889400c44000d1030590315008c01c20030601818400f001030f40c1d103804280340d02e5800c40d0440440b910360400120b9034031840141d0b0450381401c2c091004070442e0a0001c1c1c0c2442d0030031030340030a0003503012005000e20a0a01400c407412034540300758040700483d5680011158805a4003503c04e10600031088105414411003002141801c0b1080c035082c5000e03620715582c2c001100003d50150752800904079a800000244003041e010b54000382d01c24030f10f0744040c030031036111302010321401e01050901d50003003030003400041c000840c03200c2c400d50310090113006040d0000490501180084040f60800d020030351140c01c040a0603814450180501611040501c89500700310760303c0d401316410b4000d6020141c1c82065914a40d10540002201119840449480d19181d25001c4065040b820119008140c1d18000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 570222634 1250 570221384 570221411
    0x12060603030225031b0509090307110105030403020c0d05030409020414040e03070f06050a06090608030a020c0f011704080705070e0108010c0309030f03051e09010b040513020105161e110103 83
    0x882c8500502543c400b040343d1445d680c80000225094403c400211032010015591700c0c0c080d03100e442802c440e0051542e90308285400d03060200c3c00e40909040240610421000a40018058100000403115a4020902841e00c03e28500c91034128001507030000c1070000d151254420f102e1540c0d01c0858040c0300140d403400300700703a880c0102c101c090138000c00364560101040b55584190707005151003001141440d1607002d02d0050b54415402262141d00c002500c4120310b5041c00004005841126034030342c045403110009000001510401d690303040344001040801540c3c1d0101c51419500c8401d485600d540d614404c0f55100b024810311105500f040ca080324403901c0f910908000ea80d05807521142d00c402400124020000100b510b40c241610899101845070200c10940c03060b100ca40010440c0030300d08080c042591005058070500282010f03038400140e0304002560125041152800141c61050421020300303010403900d07030703440078540b2004001d200b9940c3c036104017500203132801e000c0070000000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 570223884 1250 570222634 570222673
    0x1a03030c151510080c070c060507030e01140a0509030307150b0a06020d090b070f020405011e0504050402100e1f09030201030c050c0d0e01030209091003060b0d03120c09120606030302 80
    0x1d80b55020030112042198580240540394020212a1600741480e450b5680e818903004180c00400208101090a07001c056001a0381c4091010a180c0a050421044400c0625002e901e24001c04d011000c00c1c6103c0f980c40410988019581050005014290181e81c800003003a2200b155030003000a04d501142c82400050302c80301c40d51944e078900c140103241c05825071803504402c1d0100e031400380d40c880306800340e07807980601400303010170398a20040e00044200070500d2003020f034005405281028100009a59000c11103a400c203114209162100d0307041001550f032030240e5090a0001840101101c0710640c41039085069900c01e8030100840d50b640c40003515140680c0e1280419507103d900380ba45010710a071071915403e5018140503042c0088100050b909240845e14120b25400500003042846054007680000c1001520383c00300c00e80703181d01d0042c500091034038140707076007512240b01000c110310804041c001005908900141001c2c10301e0040041c4c0070f140310643c0184184081046030100501 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 570225134 1250 570223884 570223921
    0x509060d02120c0a1d01090b0c0f07050103060b091e0d06090614220510060e060a0b0f0f030907090e0109121b14012403060f0203070507061a03030c15 66
    0x211002c07030042c56560212200c552105c4a68100b101e040400990744400b40040c003c03400700c10700541403400b0b949050701e03d00151503010a0405042c520304208211001c0112070142d0010b88405003506038048014610078008050f441d0440d0010540030280142033340f2402034284a04820300c1200402c0016001030102a01e4410641c6000d90b040b0088840800061902c90700c144160780c804160700300240e048500950251000a00302d03001c00c9114641581940080d01304400c146051081c42c42102c203190045410b041c0b282d07800080414844103042080300c004080d20401808284820500f050190038140d604648080107940704014546c0903100f2007200300802190b44003c1c1c08a80c46082c184001045003005c99560f500f500c1c03011040006420702e0301422000c6180c5020f141d8a8004100c82d81103841401692040c020701c40d22540c01021505002e4005101090f170081350200305501400702c5080e96498030001035a80c1c0240c0001c0380030480130304c0b0880c02c1d011a41d9071880a103026144034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 570226384 1250 570225134 570225137
    0xc090b090106050a030e0102190207090204030c1224020d1b1d0d0210110d0509061e31080f030306060c160803030a05060402130501050a0509060d02120c0a 68
    0x2800140b15251051019003039941e2640380206181c1101a00c0c4c40c01c80c2c3c0102401295030180c010003080702d54040000400400d6a0002140381c1441c585403580f600c102070240000c4420786800401c280503d041d1641d902011480403d03600c10f0468501c45e0081d480580182403486c1850441005444071021a000e003030a076481d080c00c511a201c002c500c00e0603603032804682c440407004124006d078a883d5a4800c006010340c848140101e04000031501c2c0842c003446d05d00070001b0802c880811500c54105807408040b4070150a2500504202d19a69601032600d12454442045101c80b00c0340121310140070b2244502c0720752152064441c01e2103038489407443e10008855108002144550a001c07009190700001c420a03500c2803020980c0368080c04625034455001c40d031020042c07040f02c120611805400c400c04880442c45e04211040301614444603210b40e0307050000109138054854064030403560010401000c43e66510704c01244a0001d401485600b4100c06440d40020030589580c0304807032901c2903a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 570227634 1250 570226384 570226399
    0x90905100b0112090605060442080d201614060c0706031a1c060504060b030717070e0c0d0b0103021207020307030f0503270c100c0c090b 60
    0x40010107814600070490410004404100401c0307000d1003001003042c03141e2008101818590104401ea40e0340403003254001060381040d158500d041694084442c407541c50110000d03100d000d80c5a22030420b0760008034640242c2c40315017804c6900c0500310200390162104100e00d40c100e031a14a035a05c4900841e2150131100050900ca811100c0c030f410031082500170b26075441c0c1629035100904008403030b44400301103034462419040a003500040301065400030786140d101841c0340d20311070034900f0040d14041c8c152660b5402042c140003154002c12072804001d801c07240e0590307499001803100c540c40d44607520140150380d004111903400039003d41c00740342105815428402c103169001d005003890195103060590170480c002030918482d40803403260390141c01131500e8042500303018001910881c110405c200c81001002808070403c41c420344501c0b0302e501d14806045803100440d1924030f070303400000c0e4098589010300d549a903100c06201c001520070300714400d0166403400c485054941e4100002c0d8007144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 570228884 1250 570227634 570227653
    0x621030901050c0709060617090109020108040809010306090e0a02130506030a1b05030703080d0b04110a12140903030403120b010f0c1a040602091804050703110112050a050f01090905 80
    0x100b04094448024054140e49045a40b41e04404c21100c0136070000c0b000c0307070750b075607100034081d8800c00d12692041480000348142c4600b5400249001d10081004000071004107003091964401d80c4028054903c40c80d08000038031210301c0440ea955032004040b8070a8030010b003038004409181c0520342c0075276806001041c003c00381d0b603607054888031480390110a01d00d0361500003949981c104040340056000301c00d03060780d81030081150826a155441090f010711701309a006814100d440c801c0700c145c40d0311840e101001c00e00c40005000a000c9114462040c200c5580500001490110007140220b11a45881e9600301c0d00b08404d0040e19850074000340070442c0c402840703403c94007421090560750f00c07910760ac0d410f4002c02c0c0d0244115550694023640c1a070381c0401c1001c11030402c0820308980d140311400f101e086140942e56a03075142a94040181440000c441800c01c9034003030803011003903e60000081c0818a045078800c0010201283c08400710300c0b16000010702d103001442008101600007000d0030003510f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 570230134 1250 570228884 570228887
    0x41202090910020f03061e010c150b1f0e011707080c09040507020f060c13090b060f03041b05102708070609030507140d06050621060621030901 63
    0x421140e80760040001041d6070140d07610091081c40d0540601644a0034003806010094440240600c0350348100c0c501d11820760317004180e280000780d2180b40040c0c503510340345200000e410403046064004d10028040710801404a5020480140ca560b440f4480c803080401180c1c5d0300c1c0c01c20807c0750f00c0030302000401d0740c0500c956010b07548800c0c0024200d24000501011604a403000c8960744016001212401c00c5c85c20107214890b0404181c50036103050884a1044c0712a0903590720810088036691142404140c842e40c00340c0314090480700f462a1a45005d0501000d148400e40b4004014080318102140ca86882c01001d034240d48207a9908071407089011440400c414998451410810f91500c00036010030b04029403005003030320b0ba0741c510a0070310b03516280d881c0a0080e001818105500c07051861185c9640d000030b201c0c50b40029010440b511140c0200300c11040c071510208194180c00d1060340d020b0030018100d4003404040c0c0b141c40200030b00382c035204800c101010007440c40e900304000f200d0301513 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 570231384 1250 570230134 570230149
    0x1050c0304031101060512060f0f0c09040b030712030c0605061f20070f030b150102150c040e181e1b01020f0604060608100e0705010c0317090705040e03041202 70
    0x42d900350001400130703194030009080a4540c500003550b0348c408010801a007610050381d540020385040303001c0c0d0b04d0a181c0c2c2203041a008441010b40250740d1482103401c0d0380c5c0c007008030702c000305144146928241c00504006001c002e1210301500c140d8104004525036082c6000d030900c0c280e5404c00503040c0c6454480c801c4804140304440c0401c4c54000b03000826038200d05208100040c444a148000d0305469443d01304158400184041501d84410614804a0741c0110340d00c102000d8940c113400c01c40d95070114096030703401036401c8a040201302d1001c000030b40d14a80d031300e0300c03e40c42c4487c1140c0c82e007000800669000b94516085075015004001d02e086060084501c04901400c1401902c03e03100050442c6403415204035820350321303039032a090308010314030040c0621211010082001c0c4030400c81c0203459540d4000500c1418104144a542c18007810701c291070b0005490590300d0441d40c0350034101a03803591400f49003c2e25105070f02c0c10314480b004c42000801c643c2100c449510949141e5001d80810210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 570232634 1250 570231384 570231407
    0x204020729091509060a091506080c1507020d2301022106010930020d0302100b0604050a120318171603240f020c010504020f0301050c030403 62
    0x20301d20241001d989890980c080c52000340001410003041c40c1920040b850415403c5a0690b00300c03100741072200c03036140455480d600101c44500440c400c281e46c41c04c11002c55025511036011480c203403002c46c003002c012030814480f0b0400c80c0d284128641d5540c0c100081d10468000a5200054a180c0703800182580d100c5408440c00410041c100b02e01040d155081e6403080c01101c110b521619407100040c104a4a826008403003842e0203000705042c04c080d064100e0303040c0300c01018141003400500312071209c00e0080030500c1e805409000f9003c1c07a441c000c0d649070305070301150081f5070074511504c465003080400e407412200002c049410351803615402001780000c1410540c1006100c0c02200c007501003100c0030a0007400d6800d07603201c03d0318148000d2410440b542080300294217030311f2010008200c003030030405101302043d02921110400e21108500900104401c042100d0001c210120604019400b29104600907665041c006201ea02014200c031012a6840c6454505001085c082446640800304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 570233884 1250 570232634 570232643
    0x9030d11030f040f0e011202030a0b150d0308151507020103090507120b04140a03090302100c140c150c06011e031b0503100605010807122901110a0803010302040207 72
    0x54482005481c0210f9807007600074403105070780808208021208041307150300403c40800a00010503555000a84035640954050032105040d0013040002005104203031010800a000b103030304a10034075000c0c00200046071480c0344901520184412410035500e094116044c0c4040c491a0090b2070740190001c2180b0301c411b403020710a4902c027003000c00e5400800c44000340200001083c9140c5850200c00030440211009540d4110400a100090b0011a00340580341d04854415611403180001c8031440500301c5c0c0a04a0000356a00950307481d00400d002440d0359054460310720340389040301d11501520889610000742da01c05030042050ba0140070311540b1282c0c501404101c8282d8035202c0031417801810042c4076000840800810480c42d080216000300030743d42d83c0500c1018900030002c0c00b500402417000040c0441901c2e1030044a02c5588807850042c09480501420302a1044008404030017139070190215904201600c0804000035040840980c8580e41074a141e003140e003444044c0d040b0500858 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 570235134 1250 570233884 570233887
    0x51614030c030a110436120306060e0f01050c15091e0616020f0f061005040b090403050331120801080d12020708031e130b011203020a02180a060b09030d1103 69
    0xc454180c0140703007000c0d01a4040c40107031560319a0134047c19000c0300d500340300241464400200080380c1c000c421413500084c115480aa581404001a03034140708021a41107240901808040040c1c00414418051421401140d030b21940308913000300d400d04510350019055100c1c0780083c20109000705112a03030015131040e150850b050441592601d4560304180d0707210707000f850070803c042d02004110300c0100b40868082c0051a02031011030082c0d200540050308126000000640c1c01402120032030042008259148800f14019001004084000c2085560382c0c41040d001d04210312901015041e0350160001d04051032502e0415138403841514240491540c0a0100f0400315507050090b5114580c4c0540250704083c8008400d486020001e000e03a00060b0501640404900f03c107941606441070b405032035003c00c4581c203050b840c1c002c0100c0004e40c403800c0b842e500c14a0750014101c007805803c0c00340080c0941034a50808458a02801c46442e0f00b41d4411411107a0580c071a03405003043c81400c10649 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 570236384 1250 570235134 570235181
    0x50a06030804080304060f08010302100c03050f0c03130e090d08130c0b030612210d0902090108030a02060906220f060c09030c1211010507051614030c030a1104 70
    0x200603600302d980901e00c0340e0404502009403d401480148101e2650b1801d030301c03250305660010300b070390b210080d4403010070604201000c101030282d0100e4200751400600292280030b4001c0c1c440d5281e00455080504500c0c00ca0001082500600c005003e0100380c00a0220b08481d8034003164507040092041079070075287d03000440410591100c03503020704050f041096a80c0f41000c28031403c0c0da001c49084585521110300702180c402c3c58030004a60440000c40d141d501c40d00707035440c00302409200501075804010074000080e0204000f008100c4083d00b0b4090382c00710380d1007480302500c402040380e078889031100f510400e20710503400a403c51081c51090b407182003032421640300c1e90b04551540d03403500013103a041310040c400c0c44500740da4200100a0701582d02190502903840180f16050b20400c83e06111000c1042c1c0208441480002d4103c0d4800070042d04032176842c0c520003000d00d142460140039018038000d40840341000309403c010304d0f4222179a0401100550305000040542c040184a200c040980c00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 570237634 1250 570236384 570236393
    0x6140708070818041e150b0a2001020f09031216020120070602010b031219030b010207030f11040b06180906030a1a04021f0801030f02040f0f090b0903120406050a0603 73
    0x625010304217101070004155400b045402c11110210b034060102020240d0030820724076080c00700d516452003445c02180000c1c074008038240b41d194403000b1620650020030030b0f10080103040040d1000c402c08074200c40d440000f01c00040c030540b10707007920780e10f114000500b6500594000c100f01000f9040c2000780480394208003a543c0d081c40216008038005075111109a00030303240030031412400a00544d0030510b0300140024111000040d20b009106054a4402a09150780248006001150485079175241c4400c00e280149180c3c1001c040184200d1805580440506103d070a40b52007a840c038565216141d282e004100440c040102031907070520440c11690002100c040c0003022803000410814046e061030f01c104100f941402d06c06440c4110071094410017554045100c1d411240c0145400a841800340045000780040061404504d4202400030226200542c044000d00d402480a40c845886203080d0944a100725643ea1000d000020046004034945030300581c0c1095200348005005581ca554 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 570238884 1250 570237634 570237641
    0x30922021614030901050306090601020c030604050106061404060e010e0a05060a020304080105060603060a03030813080c030c0c310603022115010e04060213050306100614070807081804 81
    0x8803080801c0408081c001008418071940d0340e2500d200c405503081100e94400200140001000c6070301c1207540c1000b01e112a402408249213000e4044c00b40c41c29450300c3c0c24114003034601131160070009400000070f8a01c1e05044816207094076902c1d940d070840e03809200011515a0300d0816032aa0002d0072440014055480c1303802042108030b2a0041c4d51243c0c13a1502040c02c54500038001806600c082041090a81d01e841000b402e90342d1604000041d500d910084000f245101c3d00e0042020b0400120179081070030000c00f402000761204211525083c0410511078062180303904003084030400040004210b443c0d500c5c242881d4090741d000640c2c107135207400080b20011107407082c801208031925450704d440320038402070856602104688038a94941403002800500003403001e4400390703000c04c10403220104500040000c2900400711902401d060411118904052040d540440c0c1d036007000e400c01c0641e11082e20b040b1a080b8248504018290300d4900869119012a80420740316000c085100d55440c0b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 570240134 1250 570238884 570238897
    0x50603100f060504061205070b0c031c05010312110c040f09060606180f05090a05091608030318060f0103141504150b0d0f0206090114030a2a0203092202 67
    0x941c0401c00034504402e02c0116150354001c1c010201c504031000c0301080e800100c150803101083c00456441c4000401c060a6001c1e10203511520208681d01441d02003140d0401d60603603000740121030035040c00c02d4080d50404024110b106142e00030301001600c40c50140c0c409001d0b5a0403850214074200240c2d40c0c0c03011900d0301d4006a0208100942c04211101c0b00443d11700545902e0441c1e01c0020308000025050700740013811070042946400016600c0350080c0076420b602c607940907441003030079291004941c49410442d8000100c0c00c41e103800d50980000040c00b01d0040e401e00a00098590071a103a1404058000200131220f01c106001041c0c20402550700d039100b54081e0102000000c542058407042d40d0052007264030507480b441440c000b24040c1c1039121000c5904492345075450281c2d00068500050340e800c40303445003e010007001030070039054100e8118031070118072031030040d403503242500078080d5100303210300041c0d005116040582c01c0503202212003140000644082c10405591070341680d1241 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 570241384 1250 570240134 570240161
    0x607050105010608011e030b07090308031005010210020901231c05070f0c051b041b03140108010c08040602030a110c0c0f0301051509041a070c05060606041805060310 73
    0x101c004100740c0e03510040450140070406003800034181c1401c0c001901182078003015004409074800b0404960040d5040e0000f194810b11694983c5802890a01c0b000d4191180b00e025001b0011000c5040145108803544000161150030250f580c1440ea60300901c00700f00402c491800400031102509043c1a40b10329618031b10b40e001c1080d1800140051480c0d20300c001d044c0030b00c1040114034000030404281901c00c9068800c0c1d1040038500940090007400c00810480701344e05c5244c00c1040b03500e40c150040040503455007014001643d82d02c0600c0c0c01c035408140c80100050300ca00118000070110b400554000305c03404404201c01105006803442903104420f403180a6100759212051800e1803080344001102c114020072240c5000707441c07003ca00c200e03920030300d22030040304e030019040280f0610340c607040d06c080c1900180d051403c182c0c06400c118110400b178860b032181700001009441c1880c00c07901565810070840b4000418080f185000c4c2002400c456410301a0100710707409400180306003a500e1a22 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 570242634 1250 570241384 570241391
    0x270c070b040b1806070e041e020f04050108060607050d08130c14011d01020c0f06040812041e0323010e16090e01020403080a050c190f020114120103140c06070501 71
    0x1040083d24a100156140700380c00080400221942200c49024803000641e008145601d80840d241c003601011008000f40b00c1c808121050001c0d00c8001070f10982d1000c2e26500b01c2e903158a01040540d004d141d000a01c0c40e4000070309040c0291066040c2a0010b50f070a044010807107640c0d503404190035080c0c03c00c4480c2e27a4045031075400396038010304500c6540c010f02c2903580c54000d0703140002d4503a051440514015128810089030310703214407045070000d040c0f00043e180000c0701d0080ba403c55034080c0c41862070381c0e01c0703a400516080544056080c2101da2004003616400d51000f0f40400e1082440c8040c0c20956070303640f50340c1d4603038801d02071011500c1c0f0082c01c00c1c141a080c11101011a0015000d10820303078414001440000c280c04120744240009040031034589202c06a598501040c00d44008009201180c484003082580b40320514064404d0701c4586d41ca0340c140780c0b01314071340c0100b030549000003450100403c08500d000b10b43c09102000c62055401c2e003101c0101181903a400050101c400360354 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 570243884 1250 570242634 570242641
    0x80604050d030b041b050f220f0503120a080a020f160b0a0c0e06030406021c0209090c09010507120210140f0709050105040605031911030702010506270c070b040b 71
    0x2c1c94800d2400e81070003142c4c20002d40079030500e00301031400b018101c45c0c103000c400556140312203103040039201d195981e03190f02918000d050700c003032044000314800c0040c281e54640021466280c0810344a511200040d050390412101020031030f00c001c00584802c031416803c01c0b443c440782080c1d40083c01040340c1e041c00070b64081450302e000a031a00e4000d1005a05138030b02070405000950000030303c0080a021601285c80340c6590a1a40003489840081c1e100c40b84000300403a0301e01e800b40c0181090a004480381c804559030f1803003690651082d100e6590000b002000b4445c00103000d040e00d41c0da29a810b204942440c1410504081120b4035461003c48405400b010444c11104980c1c03201c2e071040c82490400d10203450207001070002c0c01607000f050280b110101c0000c150508143c0c0406c105010b8040c284030601299a44c096a80c1c000d5400c04019400c00c4000381c1103080610301c6649a01070b8668510540141091461a4060141181d00d0411040100750080f61080c83d03c02d014074050110b2420071b08 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 570245134 1250 570243884 570243887
    0x40b0c090f090705130f0605070f0501021219200a0309050a2307091a0112240e1005030706030e0309041a0a08060606041401021e03041401110601060315080604050d 72
    0x1000c60740611320003001a031b4140611640708080da5403080c1d1084074281400c0842c54418064060350142040e982c84070f004000824240324085089850700c0d50040045801800c500c0044d00429a075417800c1031020094000c80768441d0f4403a041c014000c3c02035400103c0b260742d4150268501241140340c0010401c0d4042010360f0038040a070041400315800c021564612a02000f00380d400d22055043c802d440380c400d0a03640700c5410900d5400c80c0b4030001070303a0329210405810711480c0da020b00815507100c0c800007070503030800c0070017001504d2000300105061460040100c010380080010b142080c003041c40b441e140f07034445014079215085c203911945500d850400a0107880000e44c0c0c0400034a510103030900129480f05011079056034103103075160028600c26001070b4a0300c040c0003600308000880d0180d85811000100103441504d8196504101c070b400500c0044445000d451034003002c0c0e400940041002c24069800241568140f40e803030f50f01c803603440c8000e80c24032a0403901600d01d41c101c3c0528800e090b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 570246384 1250 570245134 570245167
    0x111002031603021606052a0d0f0b21030c1e010b0603130b1b120109110a050d18080c0f06010f150309020105090409200405040b0c090f090705 62
    0x1203406240c21401d040545050030406000500e000d060280c0d40d46c0884c40346100411183ca010001010050783d9001d1208820426071040c9000407815140c2102000420054010b0f914081c1004048408910b04440c0b404540c210007040490b0703510013007045054a035030510036801c5110b40d08060486c03d407000c0015509591041c1c80d040c1c410035081040251008180c003200c001d80e07400401080682c1e84114051a024100d1001c442262401051405001cac4034001240d0590745410380c24004000c1e081e42c00c84c858002c40c54104017182080c031903d52041a241d00c0941a9081c665405006684503142d03184103910207100d407203254018950b03240c581002003100f1401050754010350150646000280c4002c640d00881c0041056201c0c55003000750781c0308030203a600e94407008108000c059514640a041111201d8002203000040c5200c490a4505132050911035074200c5428030702d03070781c440c02d41e140c0c50341c0240070701d517402510381850940741e0302c400300303901d120722002c0d100d20355650400070100309c52 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 570247634 1250 570246384 570246421
    0x1609114e040209010614030a0b030304030f060203041203020313080903160f030b07050423010909051e061504060810030f080c1911040902060c01050708071106060d020f0111100203 79
    0x500c4640c1c0c1c80900d0021b0300c0c2049a9002004000000d551544180081d0552085a1014182c100e4011408080c072005900860046104083e42e4003049000301050b410b90104540c140c0444031900240c4c804130b03603810002c0202080080c240e0742100a6078401c8045114260400792001247c0c075014000c001042c60410303005107550502e41e0406203020384601d00744800f501e252060001c0040b00c0704030b07039005100d03080190080760400d00c00c034600790144a5062180580d09440011030201080d8207051091003219109c540f4000540f0f014100802a107101070060500c2e034080c1301e0b40d500000818a0506083e40b181d01c5001c00c035a4a5440c2c0034a94079060b903035151a003000d62a0361031a000611005c9000144020680e0003288049190000038aa400b40241c00304081d4200000c00070a55402280da1b44141d50546645481c0c1c513420b510141e0f00d030400c40f6455040088601603801500e0400c0c00c021030b1400c140340c031070b000c801038040741070034100c0c65080c0e40c0b041074010051000022030303285116036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 570248884 1250 570247634 570247637
    0x11090c1218060a0c02031314040f1104150203071424130605090109060204140103051f0501140f07030806010f1d0d0807051609114e0402090106 63
    0xe000070307a0080c140d110340001c1c0807100d00c03584d50003d054015000780140d0711050024040013100300e54402101c41030300c08003c98113100303e180282520340c100c0d09100d9410780d0281c1208442c146070401080c1404d110421410340194841400306c2c00c00109003031600c1c2d681200100c054a402d041d25602c60078140d200114030300110641d1000c01c0001c0b40605241e00c1c40a070008808500c0d41c1700c0315031f050300400e9141c00c09030105000180c00302d540e80781c44222004101d8281d0302003240e581c80b108031a08441040300780d4200100d1500082203158811500d00034035510407042c041c0303001c8172114800385036808401c2c200c0102d621b640410080e0360300000b4041c0c0e14071207400c1900e1260322500301612500003461000b0300ca680040742d442c09101ca06016644aa03034404100c480c41c0c1c038440610100100584940700c1c6881c1003540c0019800c444006841c4260300303021210f901003a640794015081000d41c8505210b07410301e44008032084c2a072142c40079031003a0442c0d2a25507420107006001130712505812100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 570250134 1250 570248884 570248911
    0xa050903100b06030f060a0b0c012a020a0b061302070b0402030c090606160c03050f030c010f092112050c0711100206070f030906050f0115080114040911090c12 70
    0x140725454240440b41d105964660610030782c0c4d140c000103050801f043e0402c0010010105079048001d005500070a180001540114084004620307647e911440d0300311243c1c0140c00c11b07d0000002482c030b00d85030750003020003082042c603030440d11081403c1742c1110a05039600d01c554400d20081d0300b41071042c0749400ba0203440c00100c0b0320b8440c000c502c42c0d00c141004203001c540d11201840038400e03042c8142028590241c15034080400c9180c40c90383c0e0b508581300c06a00ba5180040e409200e400034450510603581c0a4501d00c590b440c80644144214104039084062007003080a80302d42d20000d1180d90300c0344018a130705a80343c11544c24280780208080d010140520505044c41d27445a40019400c0e500968515021048522071002280500103002c0f000701030700c3c105020b0044810f09103140f80e050360000c40c100001c8071140e5070100c07500e0a007842100007031303081d0044504039424079420800c8802d00900700041c1c408186000f0412001088a0b4401240ca001c6107882840c3c416a9030250045a00240361 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 570251384 1250 570250134 570250151
    0xc0c06050f0c0f070501090204020d060302030d0c050a031d040903021011070203211c091103030a0909050c0c0f0c0a050907080a0b0406030501090506090d0512060d050708030a05090310 81
    0x1d4880c0c4412000d4044011800c0c2c0e040107001d4007d8100d040d40540195201c10300c0c0100700028250302c1c04120300c2805072104540c0078602c078070388100034250410010a00c1d9256a20291344064002801d461201c000850034821504c3d0383c022450001d2003603001303100c011190f04552046a84408000100a0003040100c0260340d000031032081c00d0321860085003082c140f2400c01c4c0c2441c480c0d05c16140512040b1442d0300c088555580c800d415840c014a880016000701104058592040c1c1d03942001154262a051020381642c1d848540c0c40900c0c010400c0c54a016140c010745402041c10280c0f4295101c1c1c241c10030681001240c850040c83c05844402c0581010031014144903402801088040e03034450b202c04181c1d441d1f0b000710005513003080082048201504002d51240d008442440441c0306180504400520030000c85804080c48461140c140c1c40b22000c2000c001c048140c181c0761403060340804500198144014005e10b41d1546856aa501d420f000345030a0903030002405440c0340c036103201d6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 570252634 1250 570251384 570251401
    0x1d010509010c0b06040618020a0e010806180402030309040204031112281b090506040c1b02060f0c0d1d030111090d140706020a051e120a120c0c06050f 66
    0x10784800c2e0381c1c8543c0348486a6a00b2001c0b90050145a1040d21240ca880741010780d0b003039040c0d00821803014541c2da40340c403002d40180103646010b42500c18a410001358003d02d61140f4200f50615000761005041d00e19008a080018080c2e8206030020744d028040540400800d03c0d01052030610080d40c200901000100e070800d5406042c000301c032803054154119010420040f400b00103c0000781c800d0600d4120781c2c1c49109403070042c80c0c00c0710540d014a182c40c3c02001c007180201c1e1301180410f01b00500c800040481da00b88100ba401040e006d403a6004180b0040716108418414440c00141e40c0e5681c40f1034007944418030789282007600295000c0d900d00007600d4080040c18003184c407034030016503101d5901c545514240d503807801501c84443c461700507c5004180703280c4c045149a01c05026100f00d40c0c0011a801610b01c610702c4400001c481079200e83d6044c200104d0a50240140c40c0041c1440700d011890400f500c000c0d80c810a80102c0000e001820340010800301e44115904035a41704403a00c0710b072428000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 570253884 1250 570252634 570252647
    0x30a032301080d2d09051311190c0501020a0305071205240111120a090509060604121514070305150f060d020705070306060302122803090806071d01050901 68
    0x18000308108010f0490300760a103820b58402d400018107003454916096400006002e00a1070144074881c00b447d0f401d001c21001c0301d01403d6854003500700b641c3d00d0600b82000905240e2850700054091210030f5824501051081c8081c269000da41d4602241c1e51a2044008250754a00c6181032022403074401130041c076103c01d80d0118450001c2070b09070b1081300300140042c0e400d01200c0850084a1051200d06000e64007a400a4044001c81d03440d81d0032804e4481d4104640c4a00440e4003070b400c40000c0c00104600c0c074480031410190b41c00307580040d84600701c0324004000e68443c3c0b902d101002c8850005d10501691600c5640c0c1d20000c40c41f800e000b0340207131313200040e41d000c20140c80386d100e0800401c59504014250341155001640b1234101c5202c1c559031300d003204c060070325403009078481d8200010001134400d002c1003518038520070043d00c104e0018a00395000000700d00a07001d900b000030b218008030314400200801c0c0d0142d0f0303450b1a2501040d0b1040c070710203031000400103424100041401003c4036a60041c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 570255134 1250 570253884 570253903
    0x705010c211805061006120603020603040b0a090804060201050405060f01120b070504170f12040503100203220809040c140f0c121909060804020d060905010e030a03230108 75
    0x250081035100c007400740210000c40031140034140d4080da80610500e8a00405d40301c08a03403c5031600441e001ca80841403049400f20302c00607400607800c00005002441c040364580e4401a00080090091510344a412071908035800490144c0e40d160248401c2c070000f00550742d0322285c064481807003981030001680c080040c41c00c006110441c0980442c1c40d850003502501c01070000030403810110b0401d85c480a0740d030007001d454a00c55000d10108c150005d80d48008450a4640c080c0080c22000e502c40720950096000a107040d1500402d0341c03040065080c14500300400b60f0007040c089445800c100204821036140d4800c500c01e212000c0c2c0300e0141c41c208202944c075204c0c030b020f0005458a4040b100c40d810902e00e03020050380d0070800107024960004034444404154a16540e48440c2600c500040e82d40704002e50700038bd030002c60a090b07000040c14a401500c111846000042051940046000d1654000007100400301e915841840c568803c240403240340403d10b0203100c1203a5160101c0103440ba824030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 570256384 1250 570255134 570255197
    0x72c06060304021302071419150905071505070812040b1515070317040c06021002031918150501080f01051b09190608040c06020307050c09060310050109020705010c 72
    0x4105801401f481d03030310083c0035803000c0c02901c1c211090305a141c18014202001103d00800740810340e86414424804c0300d03052940000184255401c5c004c002c0220041c507800403040020030000080010620b20103440203122144102c011410245030a03481002c005044403660000c40c05034548075914070a2480c1d00342240340c4295502c401c20b0034111142c00f006030914800380c103800140320811903102c072048c0c200d450907400c1d00e0360781010208500c268441610000e02030031058840c04680c1d522a8840450342d0600c00400f1292042c83c0c0ea807524900301c90044007481552a00100000340c001d100740c002452244e4002c000c0b030701e090301010840b0228400380d010b101c00d0100320007180d40c403002160340d50940303541c96590000d2360311880140704c22001c0f102142c02d80400c280000c0ca407400082030b903d295030301801a200440d0140244a0440300003080c00d680740c40b0350803104155004620400b03000c0c2051440141c1d03502d405003021400d440030040e40ca8208043e403250311001040340103003019001282c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 570257634 1250 570256384 570256387
    0x203183702030a1a0c04060207030318081609110a0512180714031e06191d07090b0609010503130c051c020a0e010501170603072c06060304021302 64
    0x10345610849600005100a4041c49410004018401c400600b81080304a400c9111001d5682000d8200140294030031980583c1c80000305100081c01101d02500f011180030720540c03401c0d60394401501c1c200c009420030481040c0c0351014001905c1e00d000701000c40300c50760200c40c58401b05450042c61407086c0050300103251010000f08043d107500300c5042511000030b00c1100c40786625510840102d505950000b8428480e0f80c07000d034500007100d8400070100c08543c0250160350b0340d40445541004002041c000d495688400310b10300d0b00380032070348202c84040d84c000800b040b6090890b040100d42241600c20b10170b01c41070001600030780c1d010044a03400080070046004c2c1c160741e40b81507144244603030440340e80304c42c2070b0000030000c195001030403030b405000311004c14213640c0c0da03000441103440a00070140018145002c04044500602002c1e40020010b401c40d44c4071551440d0045e442000702c0821070306c40b50820340e1045540301851000b9000314086914070704c2c60806da400035030100700146010380030540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 570258884 1250 570257634 570257713
    0xd1a03032704060f0b270a03030305130b0711101b05130306021c140c0d09211707020303010f050f04021c0e0f0114010501180b0409020318 61
    0x156030f0010b40080024a1402e449162200d0102da05038000e040920741ca042c130b030b048402c641c840005680d60024400b5102001182c11510100c024020017000078900402608031503001406001400c0d101d00004d55940c2c0d524400b45076994142000f102040c4100c6083c50001d401101c41d100c008800407081c0e0a0040d56400202c818100700d004d154005883c81c1c1c170105041c0c81040c2000c2c41c089481c0079000040210000e4040d46c10881c000c1134550040d038031024003056003149c80d240d0100c001d80340140112040c2e001002028007040b0003000b90200003480c801e46403416451402e0215800c001580041d604560404007071b10700700703130407882070300e11a02484281c401903841d20b904407988085204161030006480c00303040c4000c0c000000c8820840d01c80e00740c0c1e0024000c418410242803000450076469981d1a0070011590003843c0c903086a190038240a0000303000d0440801003005022012002d40c407403600d0501d100b41d51b07116042416181d0441030030300c13252112800401c200c0d9219507480c0d084580307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 570260134 1250 570258884 570258889
    0xc0706120c0c2d200411030412030e03040509011205060105030a0809220c030e0601230d050106120c080c06040b071202030408030c0f0c0f03070603050a0f020d1a030327 74
    0x2800600252080555080641d01885806003244c000f09003640d003801225140310b00b16800d444201c03030260190b002d1540321306402d4807981111008240d80d404882c205912230700001c500d4282039000102c4040700060300801c0ac14140041e03401800100e02810080280f9124040184200006180308800030f0042c00f0100032601d002d02c40700c0010758000c02c29003000007400b4000f0185444010034074481d0400000b560070b0700000311080324114410140b51007131450140300010400f10720864041d502d82c40d02299100f0300e5419000c2c4140102503848200345498442402d040c42040301a0040804002c280720b5401c1245c200c80c5e00b075510081c13040e4510484802242107001d9908202c005000000380340301c15000c0040d411401b0500941904c1284281d03000f00100109145420368141d000311034200040341c020350241c1e0f48480302c0c1c017002c115022841e00720022070340181d059400b590703030f03550008101c000c581e114501c0c9000d05030003d62805901004804104113507510b00c10f00310b092442e4051664 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 570261384 1250 570260134 570260213
    0x3030c0306090507020d0921020415030f0b1e0708042a090f050903040609050907030f140901051506091c0c06020105060112140c0d020c0706120c0c 65
    0x20b0502020402460428070320094854003030310313000d400042c801000031441c417206205280c0200c0007a004540c071448543d0034407020f404981c003681c412444500d03001021602c401c0515007000c2c8941020005854240d00043c3d40c00d01120070034103401c07101010020b401e60400a0786401030380108407182c1800560f02c0001c03940d881c0544840700300740030200019981941d90480300c56907048407000c0c8960b5507804100717552406240316200008a6021081220741801c1d030345541c00401c60320340803500201401003c82501c0e06517450550122a0a08002c6000801c0c45410303081440041d130303002c2024101b4002039190081e550b900e4031032541307802e04003060070902084a103030344d0f07006030017401042c0c0d20500a0700034141101d4490105400c0008807080c080306109400103581c200c0303405030300c9071951071542000f1f400c100103001d0310395800c1101e03204514040101c080107003a00c0d6282ea440c00c007190140300070348135003407281d50a00528005640000d80b5171200002c1c0c0082c010144401d4812030704400114 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 570262634 1250 570261384 570261389
    0x30a020309190803060f041104030206031e040c060e010f08010302041805061303110a030c0b07050918162d0215070801150903080d051009060803070b09070509010303030c0306 77
    0x582c1d4110b008420888103001962158108540007042840d081c82030100350303100d0528101d601d00c4100014401460300c1c2003e9908602c4054000c4220041031071304480d416001d80d0300b80ca40c7e011040c820450a039001c17094852504081ca03052124450250303024068200600000384aa5100c8104040d0341403a1860844000d4104088944c241480d075441481d02c000402c05400050004850014050000032490421503142da00c0305210480c0d51548840600d025100c0810450100885102980c81b281c10341408030904242c803080d401c00300f07100a0b000d08548d510400b4080840d0542d5030740350212074952042c102d42045104843d420540403400e100460a000e00a86070b00828030100c50382c8071003800d05a542d58005841001c01031001668040780c54440100000001c005040791044190440e5800c00f180c1020640600d0b25801001d066540b90380200b10b255002094210621034000e100ea41c121480d000540000c0e410076001c0350f581c600501000d004d0641f04c1c3c2400900c1d80c030a5010000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 570263884 1250 570262634 570262663
    0x90302010b06180306010b04081b03070e1e07091802090a0b030c0c071e030201110a0b090c0f06160b07210b0f01021515152a0f03030a020309 62
    0x942e00b210103c00c0003800209400c6034083d214010010036441002802c441c19900b800b0020800b01140018900801e008106110f0301402620130020720344810031006801000806401c41070341503aa080c00d01e00c0c0f034009294208200300e8040401c82d0030080303a00607021940c0b031000940d40d0f02c008008558410299400703481018030000c10002c40d009018017170541042e45200340e40d0141d59600c400c000c413440091000d035021028030f00c01c10045d07000e6a21001106114010740703460341000e4454809104044070401031581000c0100c80303103460107413994600c08e0700440d0303403e040c000c1e079840c1240c0042da8150018802c1c1144008154414001e460000c140340e0f9941039410024541c284c41d501400c501c0882034000c5125811480003980045070303407401c8046441e90502d0950b44c03021a000b4450303090551079000003010034081c1d240c1c961039000f006c0000116020b0040450041381d1b244545404485000894000c80306604840d5004807c40b07400003c107407409600d030703154000d0403030504d0b42c018159034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 570265134 1250 570263884 570263887
    0x201050d230a0615030603320a0c170a0803070809190303150603050609071b0204050907060809030708030601081012050a110301060803090409061506080105130e060604090302010b06 80
    0xba2000c4a03402501c01e98041c3c0b2203030407040c10104425416034010b0300005041c0c1503501740c9801d0134090f801d00884200381c01e5000070400302100812604040c4400c1054aa1581c14a8280300400f41c1d4100d00358540111401492000e1040d1150b560501001d0145c5040110b00c402003080340ea810022003002502e141c690211040f43c40c0340141c01040c1c000b110440289182c0d1001502e14000d100e480d00c149009004000f01d6501e01204680ca1000c400a412901810042041c05600e440c820540310b21111401090318506241018011060040c03a43c016030b8410440380e00011a8407060700d4001c9000e0070407140c180c81d0501005003c0e0990b0300024404080401054144400005c284da00c3c64010071400940518241c281402d903905400b515103a640104400c0c0d109003455480080303403074052680040e0003000d0309640c503448600c5922031000100c0030340c0144450b14000324180507c142d007034002c00c0714007081070724661034140003000c0d14030940e51900c048050500030340200c900c89174000c1c1050f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 570266384 1250 570265134 570265141
    0xf120e060d0f06210c060507020609010305040606210203060f0c0d09080d090506150f10120b060f03071b020a031e120f14040303091e080d03020304060b010206040201050d23 76
    0x44c1c9111003402c03e440412400300c000400e580a41c0482c2e002035000350501d440d00d81804015400341c0405042190031035510000081d0111070007e2480401e510b1942c0b00c1034600442c01007604c0e040001d491441c080040d4000c2c00440b080c41030407074a2040381c074000800c02001b1418003a5250040c4004041504c2c02c018810007040000300f0741520030000740700201e02507070591082c07080180c0040c8003590440b1810710b2440c3e00314000c1e0214481c00100e000c011422000200108441e0303008405001030442000c814044415003102419800200e00b41d04a14801e00c40d40010741a03802620000d070200310011580c5a50b4005242860100b507040000d103c01103024090081040c940036203810001000d4408038101145044215000c90b5010f54550140c142401550303014524800f042c991010b840c0070340040e003107a0034040204c0d40480f54500580ba0b18244c10079200365076098103414111340000c4100001070380c003c425104100491140024051420810005840d05a900e40040700c409203080 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 570267634 1250 570266384 570266429
    0x250303020408100e010c0c032001020f0403030e0a1706070c03171014090108070b090a0e0a0501170d020d030c020a1b09110c1b0a0e040f120e060d0f06 66
    0x250545008001c006c212202d4030b42c2085514444100005001400d1100c1900b200020412622210340740a00010701d03002e404c3c035084441e9482540110042840542800c1c4e151a041c80100001c2ca174000030346221201050900713440701401009c80307052000504102e418940300300c02c142110702d50740c2001030090922003500d01c400c4d045407060141e02600b0240d003143c2c6041000c0f5443c101d400c3c1c1001080071906040080480e03401181900382c114295010004104507690b4000380200e078480c0000a1650400c00d0310611280d07500b143c00300b1a4042d104d528921540001c2c40030b440707803451070006100c11910408034104104824043c0004c4044250b0244101030503034000300725103071b14034200840d02c44608030150728004d2941d090626000304d10100d0881004001900030110010050300245841c4c443c030b40030344482610251041000c00c01d0003001c010145101702c0d03114a050800556100325075000621034407440d05404803064480468a0780d4021540186020702142c0840108480030b07081d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 570268884 1250 570267634 570267641
    0x30c2609210d11160c1406090a120807022206050a0605070b071209050304050f04061a0c0307120c05153c0103030f09090504022d03030a0e03070b25030302040810 71
    0x580000401186e03800e126032420340102c1d03503520300c00b0b4000b0701160b140440c03000700d0321404582580c032541c0400200f40140e686c500c481d10060500c8075008409181e14810104480340c641050340162030b14001404019001025900c901354002200d01166903154002c66154036940c0380b203041c036824402e85000300b01c0044060001d650b001d031010707030016800710700300b1056032158440e241565603030b020001010354a00c0002c11a600750182220303d0035440e0380e10b2503210a00c0303020f600300080e003500904041280500c507a40e00c1c0201c1c6242421981800c902510b014400002c465441c9280b032048240c030800001490303080d800708601c1c1403810f0760b5a41005000503081008000008842d684085410311461007881d000b99000385c078446201c03000300124100b00800540c904e41850840b81d01c00034558080004100704402c65548014200d010b60502d440e00c8055084580424010701411000c051200c448143e40285100d5501100c0e410707041c107070024422504508503d004403401c4403a02c41e00b541 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 570270134 1250 570268884 570268889
    0x406091805011431020607030323040309060f02010908040617090f120f0c01110d0e03090306040f0201110109031706061207030c2609210d11160c 64
    0x6000703200c00c21501c0820060542c04480004c5242a4010f0b907500c2c00054040c44511002c0d200660140c0940c240c000a400350003292040b00000d86400d0320f0003140144260b06c1010704e48211404010313040c20f980103440d1031040d001c0c00080040e100200f0010501c02d400014026411041d0255296140c4800801c142554620a11031220000104590982c00070b000390000c4020009044250221000500540d1200160b040101c2c02440708116610080c0305801400d200d20510b103503112202c440e4070050303030b81c1c1d940c1405050b0000d010304883c03920701044041c1d0155121000c42541003d80c40141e5000f41441c0302c0000355032803e0030070800c00d42c0240994402460f100c0803074100e03556101c200452445451100301210740c040002c02d071054000d4101a04118841c00d02661100c02d0100c40d0b0b81c0007005020300c83d40f08034a05e040c40071200e002d024004001c000d82d81081407110600d0710700d0825125110b031582540740d540c0e5190a0301002c00d02502c0702c0341003405080300c608034103007406514600f4a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 570271384 1250 570270134 570270143
    0x150a051006020304080604020f0d06140103060c020c37080a030e040b06120901021c1b0207050d12021018210c110f040203040302070e15060d02030604060918 69
    0x940800c1d001d00000c00c2c0c0c0d044522040040455070b84903800d2040100c80b034001e0580040803c42044005081c50051282040b880a0300b800903616605104050703c040b500702c0313415034010150b022060b4443d0009104400d406000c03e90448054103159080d00c000d8010002516070400303004650702101055400407075000c6d5480c0310041889200304012600040c1c0c04591040040180d028400340846500340e10200110005090000d400b148041c0200e2412f6007880466680c107030056500e800301e01001030301026100518003c1d040001048900d0b48034070010340308a4501104114103842080280c03505802c1042c1800103060000300006400b484450481c0d101c0c2d8000c2c0b12041184444102c041b07901d49070b0355070034018005d86e250030400020103940d0540021051010621a40341e40c001103010305d01c6035000340541840d011502884c030704090041d26004004680c0c0000c00ea680e181a9500004081c0d40144d494441000143c01000310754810756009041202c0c1d005c48406c91407110584034041d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 570272634 1250 570271384 570271411
    0xf01050c0a021008180706270806090c1905030304061409100507030f02010c021b01050d020412210c03030e0a12021f0501030f060c180e01050109170604030e0102150a05 74
    0x4489903941b11160740c001c0302d00140c2c0d01d02690544448003081c11401e014011490310505454840041c2860402c403820140d81c0d0003c203801802d410550069880c00000d088868038580c2031800207a100e10a5100780010442901154140150000304803500c1010040060700c04402d4180b01074030a4001e1b2505402040100041880701401030288450104081d40945200f065888036000c801e48075207001b071304120060214000b1040644020806000114032070290f03c42580340004c4a90035004082e800c21148003001e0102c51307000440c052403181c2c103041c041207524400482c0781c64070030030203801b0300140100c00c1c0d00a0004c0d0045440590341d40221f0032103100c5d808003003111040c1e0718280302c010075009010200002240c1d496021141207241494500f482010811802682c2032030f980142c04107102e03c000401a941c0c000610000030303d40d214101060000030201c0d0342d25010014405014800042c0d41504107130320074010340815104be2403030b00103541804031003900180700840709040740030303c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 570273884 1250 570272634 570272671
    0x320f07050c07030227012d0608010614090d060c09120b0406090302030c060a0f0c0c02010c1506081002030405060708061e0303160503070b060f0f01050c0a021008 71
    0x3090003100c6451114000424040780b45a09000f036114110009009079104041040440840c13592468020030309624089040c841841c100d485111a4903491940140c6241c020414a17400407035190444d00e0a00f130030440170b2110020070955100c1ca901c415800705c2d034070060301e0401285e81c0c005008030075550b0307803070104a4a403480003108004d0158040c0c0140004000980012004d070400300802d4030030b10560741010000d01e4114540310090b40c81c084141d4842d98100c00d0410140b01d08d40700400c0d145403000090300ca80c0c0010f045551a0302001c2c00204d0100c443e80003440054204100030803030982141e210204204410009400c1550100c0d000d0140c1d80c082040315115041c0c0300c0c02208010000541d0f0219611b800f01a880c10384200764142c0014019541d68a00358401c5810150142c000345544102da0718101c414280014503d511494400a042e007403070b1651541c01d506c509080c2002c3d56900280788e1224507043c100d2000a40c04400b258244c604a41c1c04842c083c000c100c6542e107841d8030794 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 570275134 1250 570273884 570273887
    0x4052701020309070521010c020a05120301061202090f03060118060b0a05030f0703140f161409011b080c0c010f0e0d021c171902010204030510320f07 66
    0x403060b03e08800302d07400b5910a01840c600b410303425000c90450800400b12041524035a1300351558901c8450158102010300320a00c0f00c144018400c80058810b01440c56043c01c0c0040c11919100f401c0ba904290701090684294442d0010741c0202507006045919541c2d40740e2940e440c046c0b5008554141c80d0800350700140c82400382c0c041d01e44082054880504544d1141300081d1401c40c02002502010748540c29420700c0010b1410302405808040030404017403800b140c0031215490b10002407002c01c03840e239108100b0f540308441036810b0b060b024070708003410036000f0708041d031000481400500b8010002403c02c0c109100041c1200c84043e087e21510711a014030b51003619070b203e15070380c6150011035610444005260028480d080c0346090b0790b43d04400c8100780c40310300d1501d0040c5050070018a00281000b041226006403c0e00c24045100941c079260640e0760302920b505850405000c07540c0c40c0c10c840b4143c044040745a404210503600c103da0391041c01150700c040c03c4401d580a042410b100340100d07107000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 570276384 1250 570275134 570275137
    0x60109020c12030408030402010e1903050a0209180d0f021608010207031403040803010e04060612050f060907080319030204150203040f060c121202130f0e06040e06150109050405270102 81
    0x75178005649a003103940700d4006540d0903500c80901c40d13003e506007407884075012080c4d690201541c0158020300780c01420b88103008101c40b0241480c8003540d00c03120804e909401c0011003480200345491b151502000016042c0d20f04141140714104950848401052030f82e01540901681806a920304240200100c00c3d040c4612099401404c0041d0804c010b0118451140031207410921610001943c2c0740d403182004c5100c50508021070700c0390810310141a980000304102e580200d0200083e100d401d00c7c0c103085c19980d105034902107840018118010f800c0c43d000c4c1d811344000303210021071105000030340d440003034990740540502c40c16454414004180d041c810600d51000a5008408480c0f410811138251034180240c03103400d954035001c10800300c050703c018021600805d02910380c0c011007800c0612801c042e0000030041d0380030740d1400380c10075018070b030018019401034003145411200b00c403c0c1d030040303d1240340d9400080e0007074144024007821010a1500403a1035200e03406d5600f0700940030b00c415080c1d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 570277634 1250 570276384 570276391
    0xc0e010504091e050a0905070b09030d11010b270c0a050d052e03060608010e071710110a08100b2a06090d02060c03010f03030c080c060109020c1203 65
    0x8406200c14401c031a0b6a60005a03001d51a5032020600c1e081c0030b201c0000e40f141291810170032911600f1190400504000b4a80a06809102a41007010050120b55a0003050188800b0000e102640d10321508080d4403800c00c0c00d00141010200143c6031100d0503001c0f00c1c8040003104044001d000811a08150041e6100811195101403500c169014040050b00300a4808112030310381b8007500000821201d6002030200b84050809403081c51420700504548141c0d1111b161a4100b20303402201040c081044419200200300130060071020b0094035103010b424454039682c161a0030300006040c1050005410000a01d030b81d2801c017551140c00642d4800c40700c0c03107022507012003807280b8001020060f0324559044072081d5a4114000c141450b54988002502d80700113075080354a0080e003d0f41e0500000340c0c08002c1c005100e1465140450309440c0896511000c0c0803c01c4e600e1030700080142c0c220441c1d0040280204941c0c0f15611041040004d40c00810943c0710740c8210010317200300c104400c0c2541d20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 570278884 1250 570277634 570277637
    0x14302a030a02010305041a01031b0f0e0610200606040b031908090d0501020f1e07080a0318050a031d010c0803180c060403110114030105030a02010e120d0507060c0e01 73
    0x4024280c2d0700541c051720001d0021218000301c0c543d18078150219800c450300850261340b901e654101c2c0000c2041102c00765400452034142034840520525414407100354008505171102c03400c40090300000c6866000c0e820204c0c00c207220400c00080c80b44000540c142c0501001c540401c00809d0030302c2050741c0d4260501013125455005400b480106069902600c00800c01030715105081d0760a41d03401d82264050105105c0c0a400070400f040104c43d00c071054080c50780360403202841e101d01c9449454190043d80b03c0c3c81c0426072a01c4480c0c00070003d4000582c9900c0d8880211880c915161402810800c03c503014503640b400f08103504811581310318802c20481348c000e2200c1c1d20750745482c1400d801040d00c4003034122180c45040705055103500d81c10000e000440c040c00990301c00c181c1e0a4001401520b5000300d44480c0e00c4203000620103640c001c501d08840550908140301405c1d511408982c5001410100401c28020301120140e8a82c10900611049103d000c0801c1100b07811030342522005000c0111a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 570280134 1250 570278884 570278893
    0x5061c02010c060e100204030c05030102070c030b130f06020c0f011107020108180f060108010b04060608060103051f09020a0315030c050909070305010c2714302a03 72
    0x5015501070781404082c14011070020480ca52082e050070701d407042d402c0c9102e0040341d0000d01007003802001d202c0e200240508400962600a1a44642e010345034180005403150a0300d0011a5000441e4120542400c1d4003558985002e22a0309008009400141d0210424007501c001c0740341403801071090030000ca41d40c0c50902d0405070181c00465115500501c1c840030408825034080702180c0c10000c80303441c412040010320b4a50304200d0903909442429030020f000e2030a01105000e9980c11400d001d501c82820301e00040d8907075406000c80a03071031203121b00003684802c0070800700e04c208454000b030800110369241841104e124080206440c50540700281020101c04001e000d1481e100442640001500045075000b5480792500ca0845070398804180118500c1500c5015031011303104988180c100c230364116410180350540c5a0302401c0180704d4188240a00601c1c52010b01c03c0d140400d114441d5070080280311100e141d0350302d03900c0404800300d04416480325a002504001494070180300ea10103001742 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 570281384 1250 570280134 570280189
    0x90f0a06060306050a1401140a08062a07020901140103021c0501060917030304120c05030c010c0809010c0206070e010207081b040b1c02010305130605160807053105060d0f0506 77
    0xc230043e604602c0d655910041c0c2410000300400c04114850103121070030609000d8120b80428650306410002940480203004e02c2200090317500c8012450450b4140103070140301c80c0b80b004c0104c00034030510510000100391100c81c14090541680224180c035001d80b1003200c80b980300c0703589480c449400851040700740e0003000042c001038540180d0681c00f00003810324620510050b40c40600316008046040c000e03030b640d100030055035644041120b0304001410003c00600d0210000207403641c0000b0024824001c6401d022070b00343e4420030241d0003e019640585114803502281c0c000300744001a001481942044030f4608503180c03030340c00d43c50b284a0040054440040c1070b8010b5014090003041482030312107004001d00401d0890040900c201c445205e010a03040da070030030240003800090300100c1002010301c100ca1040b2604031107001600c0403c03598406003a00000a441c00d58030f01c2e0804c6800c01004500003604240940000c0c6408e007401205220b035684841c10b0009400003141000e0613400c250003003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 570282634 1250 570281384 570281399
    0x1d0603060d0f121821170c0c03070e0903090d0213090302070503070906060c0f06110325260c0d02040602030408010f090c09050907030c060f020c1017090f0a06060306050a1401 77
    0x140d0034890306c80d0140701c01c4003140d8074200307800c403600c80b1140b90454032480107545401d0080790083c000030440344465043c60320703034140d49018040c080c0d0702030410100101c4c1551780303c4948a00050700344400740248407551a000352105600d00c80e40d4002d10615001007503100003400741c81c040c2c80141d529042081401d45841d81c1406152009546543c3e0701c44181c40c40348203950046100301414410613044c2150b1000d0000d000c0f00b40601442004800303141c00c03200076031030485035030703da41c0000c05c040b50394072501c880c3c400911a0010084031244002400190301d900400500200e8079184000c201d0101541e20341019903a0019000b405034030a000180051001948031130b4114012100b102d0325581c80c1d030b85015011a8540012004c603031108030203400701c1d138104102e03440e1000507164134040304440c2502070000a0480703021080407440a00260020030304201012031601407104540d019400750030894014000c0d400b0580d062400c1030000b070314854450181c1d0729020306e100307000c6445a07c5c1040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 570283884 1250 570282634 570282689
    0x30c0d080a0318082703060a02090120060f090d0e040e01020904090503030117071d0c0d060e270a060b030703080d0b0306071d0603060d0f1218 63
    0x60140c14555a00612265500c0d00c0046030140b81c425100c1d20358404c00c03075180c084202d24043ea080181010312801c84406c4d100891440d8101c00a01e20160b03c1e07401c56001a038981041c80c2c2d110070300d8001c12038611607032000003840e0345c0200502684500746454013004191564600c00c190404200c11051402540c100fa61120100070f031410001820505007000040c240e41c4900000d84080c2c0c004001800301c020a18075001c601d00000c00140001d514201904561180d801020f40b00a40010001900d00350190704503002822003106c00c002ca0b913103070707496200406025100c1e92521407482803250003402c40147d0740501840800020406c000c0b00da40c0c0e4101611014800c6a014000c03042c0000010341d1420281c03040040e04440484c2d00f81409007030606c0c064005025200b04041c0e0f08031840700c1d40b04100c1903035510b60107440c0d8654070360f2201c0101d00107105d0100c1c020124003080c0d500b1000d01012000c011302426172071340c98151103003c0c20302d114451900c038000c207680b803440d0030038505003a41d4210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 570285134 1250 570283884 570283897
    0x1203050912180f0619030e01060f09090303020c06090a030816231b0c0f0301060e0f150904050a020f01031b080a0e031c110f070f142505030c0d08 64
    0x3d10140b20f0800c110081441c680201c409140000130b4040c81c01480b41e0180a01242511035078001c200b01c80c074000661000e20b80314418540d10a0351200080c040c903200b60101c0790360b007002d941200d0707a070304026584603540c02c40c200b02a40020760f85001b10324011503550803e4018441d07941c5080902051201c05143c81c610f00e50450700d0040c0401565164a90458421290313000d00000352220401e16800d10106140c1d102c002440399242c10800c0c043c144c000c0c0c507a00d0300407500800d80fd5003540d80a00d6030b4140c2d034401108640c4900c05d1410001000030000b003808d15684280c8000007180c03030080040d0251006020840241100042031036001449024442e6105121b4080032441c0c0c101442014110303030022112030304005868045a810602c1406400d200c13640d440710141c0303003e00001501d004c2d8043c80c440101500f0f540e11a250522040ca00c09401002568003a030304404260b0303c211102044030b000383e43e140c10300f0080c002144d1a01044460321100c020f0112030010aa5075208002944281c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 570286384 1250 570285134 570285139
    0x2120c09031509070f1a040b0d06030b13060f0506010206010506070206040914071d0d03111005010611070b0403080706020a0c0f08130b09150c1504120305091218 71
    0x5a000c0c2d20030700141c0c08032902800c001800340c0215428071403000e075800210b40103150030044400600e0008072914003150100c409500c101a1210000d40b000380140c1101c1d030014110385100d074117100c000240c034080c690304a84501c0c41041588410380e00742081d20011207016026812400040045052810080032107910081c00d56260076101c5041030111a40141500348403000541000902034100d9880c18445440d607464a40c841d8400000034420300d100f03074000f07080203410b1001010b003101c10451907103014100d500901956071156070041c1003001300700d03440e12640318a030f07000100400c61504031001e8079001243c0528040e15510340b9406544541d40750010406841168800709656292a90700a440386e00d4580d91408000244036031507800f50084040c1c10703010081c0d55071a980380180c042e9282000d41c1c000d0b4030303208204152424128070343c0d0000100c034045ca0400080203c102403100d845101514100311540b0f821500301c0c0c0e1810040c1c60507a805104018a85144a000c24000541b21f0b00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 570287634 1250 570286384 570286393
    0x122007060f0c0f12230a200d0507030504090c030c031d06060d170a21180308180a05071502030f071707020d060504030201110306030304060302250b150402120c0903 72
    0x700d10326080110401d15982c0035000d001c90b803400340550014a941c0c0600c5147c1403d030b01000b151522a4856184075661028070000081c14070415000d501510001c003d400010004d40c5003540028014295042e4680300113441d2168003e0685c004050b120f0380e01d4800b000601e20f80c1d680c0400d100c1003d115076020b4400030b81c202c600d42d0105092000800250b2042d0380c504604100c41400005008080c99000c1c4444c0c3c03d1098985011050100c1001c03003640500e40b035049078840c4121107600110710030404040d405a4202403045c40320018003001119400b1071918081d1550300f2040340c030b90007100d13501d6540c440100000f40c081103602c0000c803500481d994200785410030660015000c0f403a89071040720050303200c49c10041415020b1143e201c0011030305a10b6071640c5040d10020751a44582d01070201070540c08548515121a5450394021413443c9a40c603805844507410b106140e501d003100c020b942042044d105802c1400d1034000da5420181c0d0a0030180301d6140c0b10035460854000c0c0310100e805104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 570288884 1250 570287634 570287657
    0xa08060709061b0203070803040e10050603070513170a021203030f0112030e1804120903030206180f0f03070c1202060a030c0c0c0b130501020102030c0403122007060f0c0f12 76
    0x241484451b0003000200010b5a030b6a00d801000050241c00400004e802c0e42c00c41010800c03511124201d980c08803243c81c266507610800900d40d80e2140c0d260300140c60143c1c80e040141c284140005000d402140200c4203440d48202e181c902c240d5078482101c1081d08400b8003001005404031000300e6900403442800e040800c0150701d00410007000040e8004176120100000340424410116000d0031500ea81d840c00c04411070868402079501c5030080d2060841d03048540f01045001424800300144180440c152003002c0c0440e10519903c0d00708600a80e004080e000c80054884001a505018158050b1a560420540400a40c001c1c030ba02c100800511001c5000c6030001140c03c441c400180000045041d12070900e03103c40340400c429904007034150380c81082403003219200c580640342140c0d4440c1d6400c2044110030400c81d03914440f20b02c00038030070b540100ba0410741c0744c01040c1e58007910401d40c0e400e01100d0f40e40a080f11074032030f907200140c503000725a808a4007041ca441c003a4118041c1c1c9042c40302c00ca00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 570290134 1250 570288884 570288889
    0x19200d14030406120e071a0d0212070207050d050c10050c0d0309050705010c0b01091d030f030a050f070c12110304031a0c031e1e040f020a08060709061b02 68
    0x625050109101c0e080000c050060640054442d40c0c45001d0f0041080380305c904104541d55144680900d603038601054a02076490b41d03d00044446003005050150745a6280e004807103680401580c003e009801800e0001c9007a0401030005109160014001c0503015180030600084005000401041200811a03580018006c001707805405596503400110340c6a281086400c1c0f2605400590410401e19110b00101d008251058152251188005041b170003e01d003440c02c07501c075200005c0d1a80004a01e00304400d004e500039520039040f868043c48039541d0b2441038150720108489030000b007495100000c0100e41b0108030480e851003c0e00b0502c1c1e920104403200c0d8a1600b1662088414101c00390100e0343c00450080d00301d8000c40040070182c25401c003851110080c0759481001103c10301c08600107034540d1800b0a02c5070b0001407480740c014042c109401c28000e0300e00e0703c0e5001e0740511036000d0009120280001d0181c0f0490391669941078150401c501211403124a200001400e81403044100159 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 570291384 1250 570290134 570290153
    0x90c02120d2c07060201020307050405120c030706050403140a0206070803061504090603110f1f020a150c0305150f011407020a26120406050a0c120e0319200d 69
    0x58940c818240d03480020b40410780c6401c003190040c00869005000b40b06002d41c028040d1070079100c1c11900b103040100c040c442d69151550381510305d94144120304002034003642060007002640d004400c4009a41d081001c000c2d5606141036000303400800c10000070f800302d001100907580010b0700402844100342c1d01c403510025a0099008a10002d984040410070444012589031b032032101a91309a111f800b0401c0000e484800c107003060b100d1840b04501104d0514404e20035410016801200c181c071030b07041200301c4002000b010300410007003072510001c184400413040c410520894024002c00303c0e205000b004582d400040c15000440501c28000000160b44d01312000000e03190048003144c1c200c8043c1034910910005d00d0111303c0d40d41110354041c1001c40002c084a0640c4c440e81000c954551001c3c2e811180c02d48451006000300722202460f000c40c076444041a480110101c046070128510500300c01c6183c841100c0041c64044080c0e8480910042c2070480d4803421001400c1f84140e001075160607401d03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 570292634 1250 570291384 570291431
    0x607020607030605010e0604060f120608032502092406180f0a0b18010509180a0501090e030301030605070201020c0a05010b03060708010b0912030409111201090c02120d 74
    0x540c00c00360030402901e9140c400d9500414091901c2c0030700d5000340300490360300c0c8624014107040266031800c0612481c002c82d911100440380b040700b041410344e101c0742c2d65140c0e0044211000e030010b5420446000c0114550075041e030940081c1900f00340d03101c4400c0f0007840d030f41c0b200c0941c02d03005000b0071201280d03031214041d00c003210040000c2000e5802040c100302e0b0700198041c80a215594a003801e1040b040d44100755121142088001ea0300c0189c081c00503203840c082d01e600d480d4020f40201099250034001c508190056414080a10283e40ca0300390f040241d444044a44425030300620040010514a80141c0d1f00500340d400014074000303602105900300324049000343c3d81a03441d07805160060908002080c1d001a992414840a50401a10f0744191040ca10303418452402120f030009509402d01c101c80042c4410202004601c0d00009864255046010341e80071018040c000041c4d2100346000f2420701b101103a004d400000000040f006454000346094115565981c5501620008440441c03d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 570293884 1250 570292634 570292637
    0x4080327190504050a020c0a06050a11040909061512060213171501081209010c11030f0c1c030807050a0309081201050909010c140913020f0901091401210e0607 70
    0x5518284003e00c0207541015000101c40c0d4410480328120700001b00d003428640c0e50210000c2502d4986c00c403414060803141184505001002400080701e81d06644900500c92040005005101ea04238031140110076074071540002d411103211180005440e40d008251b1101150500c54549890303103404140c4210030989400a0343c04084000f1103040e903000e0342c1d801800703100001c20703404c1c41800d19408203002c0c0c1d00b0b40506102e400039030041040410803402c2c1c0b40d21005400c840313181042c0850540e0715041250a5070280240803004058010300c010601c14654040d142c80c855070b00c2d07242e800c031920360110101c0700c100742c0e58429850004d44a48000c2112000c1d0240d40344a950401080201d04400a01620141d0785002e80c0d112002d0b80054079031180007080c440660f100c50402d00441c1820b41140035040b441071001a00c1e00c80340318944040c2412450a0780d8054800d82c80c1c41d0046125a601202240402ca5101492811009010441a441e1401400801c06d013110584403840c10405584140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 570295134 1250 570293884 570293929
    0x2703050f150c040911070506090c120a0f140f0d03090605010501051c020a1809050403110d12020a0c14010504061a01050d020304020105040f0b031b04080327 69
    0x1200304010029148104600e214603200342c1000c81401196106a01c01c1a911a480320195a140d80c8444280c50722240c03c141603444070b213003840700643c1b00d50680403040d11500e080c0e1202d010340038002460b40350240d8440021010b0000c03d40f9550f0300c0c40748140c900f0805100e82d4002020003403081c8410b4034148210380740414109090301e043c00a8400503000241040000d0181442c40030341300c5e02540f012100700100507528110440102d9000c03081d0504070001c20000c2400103403440060340842d10850180c3c0c0c0b20080142c40540e140d03113401d2401e40e01000294104149584040c1c02d0b402440540c20740d0506000085075075032800d816040380b0411000995481040209025660280b0700d504045e500b5101a543c20440003e0018000d2900c2404c0160340440017030210390080c8100c40107031281c20307481500c0d1659820919402d0744111480000c0c4a9003050300f0b1444c185000503601500c025201030340c10046515448807982c02504290300c4040d0039103040041d15210420840300b4040311301300f441c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 570296384 1250 570295134 570295153
    0x10912050c06010e090c0d080405060711040f05040c1703072103050a0605030316060b030303280213031b090f021b0f0303130c0312080604140903030106270305 70
    0xd800c100b816071180088400c00d40421403500000f103104005550103e648001450040c14603648a01543d0031450304020000780480134000ba01c204490103640403a8188420034451005000b51402a0750060503000903441c20702c03102c050440e4024000c1c0131881140d08003581602c0703140c40c0d4001d0006161041200d200c2c0c1c0080d040c1c1c10701940d07900003584513042c17100b5444c0c01c012940e00c0c4204001141ca0300712421110042043c02d400ca4204040000c080303d40304c0c10b0010501c40440c251103e0301307000c0c1890020070104042c1074000e440480400318415026280b450316114016059584210b10300c100d01e20010074569030a108103010007924420040c1c41e0444106030600444a8040515455003c44c0e5030740300c0b101d0004116540400c45501140d1111414601010b00844581000b020503c02140b850481c950048030b85101d401c0454041c803c44403548860f02054000346c038600c0302d68100f00018085940202109260f40c003200c513403049960380554500c0c480304502e401c210f49076040380149 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 570297634 1250 570296384 570296407
    0xc03020123010b0c030d090501020405270c07050c04090320030c03180d060f020304020901121208220c0515040807060c02040615121a06091201091205 66
    0xc00c00200900300d00d10040c180e81070703540001c004051040c6010b1042c0014042d2112009100740c1302d9602c02d509041c80800304a1030080d000c0d4109000d001d00134907800d203040c410340500400f40804090010503035406600d07600308030f2615070701c01d07d0152094415000100811b499038421407407a01d019684800010103240b400304140402074070340000c1c5034010700c0700c08122500807080310034a00141604440201e0380002081c040003000402410861400d00c120851091030f4004612840c400c5a468407181e8940d00581003105c0482c0000c0e081d118000d4601007072502901c0c4070703a00600f061481c43d0405441c90001c00066851101c01c480e010a48441040182400e0031481c0c480607100c1001803c0a003005da40030703940d110b6071240c0000c100750140303854195101c41e48100064407020201c0402d0f080301100c0a01418191070184000a180c444c0702c00b40f100b10280c48402030f0380000d04081c9461403460030003c1d030000e06800300346d41d5503a8400840000d561a100c100701d420312034581c981c4a1820489 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 570298884 1250 570297634 570297641
    0x6071e0c140703121107090e0c03030304060f0605151c0204120c03060b061e0a140d090c0b091005130e07020607030501051008010e18010f0f0b06040303080c03041707030c030201 78
    0x1318500380030900440894070f1001080040a80e104c07004c0c001444510800c1540c5810580300000350140400000d010500181d508880100c01e441a000c0c42555a074105001151441030340c400b8400b5414403a194403078000142004c5043c20009000d030401c0c1d181c074403551540300d1040e01200c400181705020401c1180b01d0045600c4100100e0780103003014441c1c103400300080c940002580d0308080001d069880c10b030041005619040824841584680a20a031030300107021800c000e07200a0010030740000e03500071107400c48425100c003400c00f0052000411040c0c940703800c1342c4e0f98400035682001d00422090081c20603e481841d85a005010074104100080e0440d141038100318028502d0004110704282c1048901d811103400500400700d946e51040310703040d00912044066802d509003101004484401d401481d000340c0c0c1e81c10300308000c1c42c800d0100100c0d44101e2000501140702940084c020f40c1414018640c4140500e801aa006001d504420401d9014410480210300a22500414194240b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 570300134 1250 570298884 570298913
    0xa030e0f030a0306091409070302120a06020324120c100e030a06020a1205010b0f07080702091f060206090d0309020a21152a030b0306010e011706071e0c140703 70
    0x30507110207800c00c001f01030f44411443c080031b40102c0d00000e40d4060303d00204444002035400c10421034172400c1180111100c3e0402351000e00940c3d0381c810390142c241c03030702c00d414098800008001303100c038003240b4080c400c0f14041010030800b800708119448003103840520494203264400c0ba001139440030b01c1040546400b5651440304451440c000060201c01c0e0800216940040301c0015191914424517003d0340381e00c1010002504115440c09005143c164220707000101c41203071814901407a180c9074200c0c0d4442041f107600d00d240d030201c41840130a9010f58401d8a03100e00107885400b0042d12007940c08512040a02c40500b14003c41d0201010301034101e05440400021940c1032140c0f0b10079100401108500c1041e1424090030358850000450295121136031150001e0309840306583d50381081d0032070328002d1040e000454064080d0401666002c600b1038880c0100344c4500c2c0da1048020310402000907440401d000703002444203400b0219a000c40303490540d035002c0000b410030a0a52405008810604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 570301384 1250 570300134 570300161
    0xc030108061023040e1009050d050a0c080912120406140a051c0b210105010f0b1903061a07020109061407110411160b0105010c080a030e0f030a030609 66
    0x1040c41038034514445160405114102071200f0004100010010700f0600700d031301070703922540151601c0c1840d182c11000c0401e018a00b039030090140d9040075595031052500540c00a000b41c0301e40750001d00a0390140c101618058a003c154800d0101c466180903030080190f98a400049030422582e980314080c18041519400c100d82000410031014000d03008001c00702d0541103200342641d503c00699844550b0083d40100031316120808800150114004005801401d5080c24004104002002ca41c64100e480c0452503a18044c10b10040c06004c0481080b520308040d150340340040c2440d80710700c1400c9410b40203000d40d940e40000d480050915039055111340d06201c1e8180d400b805100384c43c1c0071707078082a401c40b840030001c0c2c0100c0000740003001005600c40c090000031404214280614502d8240786d44204950b6103540d0f29840195070703200340c03032030001c00884080095242c56031080d000140001f00d03110455020b1160b803060315065810800c0300d803000030303170380c1000704440d03500c6004291448429 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 570302634 1250 570301384 570301411
    0x503091206220b07080604090203192a030807031209030e21100c090803041d0f0c030402060c0a1221090f080309100906020417030901170c0903060c03010806 69
    0x12903880d04159100144088144900e05c00001c201d81ca540c0c100a03006a402019107100c28810000c281540c40b00d0320b0181c0c0d24650020000f42da650341000300f1004030703000e5140703141300c1032441c0e6803d0701076449208102c1c200040040014031201c013a000d400b610340c3c0701351203001180c0d002c0014007007042d00d14141c20901c480c0000c10704030703928400300d58013094107142500031a4020070480284c800c1111540b1200a42c0b2000600042c20140003440c52104641e100824a00d519081002c1c545114161041e00140c1c0040000c14014500903004041010b1408113450b41c4140a4640c0318030b60b0720a0b50401d021454480c260030b20041d5180343d040000c1340174401040006084e8a4040011224840050403040b001000c41e51841041100c802d8401900320144a9107840c0c0c035151001e908184078070b215840c0000c03075442e20f00c8030100c140c5030b400c001a51402c0b104140000b402c003c0490182014104450800c100602074905101507441601f8481d802a034a515000c215860080b0080c8a070051f00c48 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 570303884 1250 570302634 570302701
    0x10050705011109101b08160c090209030f0f0c062b0c0207081f052505040515210a06120305030103050d0e01140d0b12010b0114090a030602070503091206 67
    0x22000d2581c40709079041b1100070348404490b00c441c51070054400e000382580301ca104000802c116141c0080101c05016230565140c0107050401a0741d03003682220581c42a0003251a885035070920b0801340409031540e081800503960711006241002903003100211080e0f0300d48447c0c00d1200c0d0100003084c000d01445005212401910300ca0100360500300e040c2a140a8850000c100c4654200c0350b4504411151a02c84080e15440040608994414401c1700e0050920080010b1600306503001d55405039052000790601d1104640211003400c40209441085680c503100030840c8818690b042c411144661900c80da654194108546000711889003801000411807100c006642d1012174000c2d002c8082544546681c0075594100241c00144a00e94101e0a486600071010030150441300c6812002e0301c8489907408030040c6980c0c03078070500700302c50303042054943d041001811540c01010300d40e00541c241e078108485a000545580c0c0c003a091280941c0c010802d120110b1b1a05212044004201450304804039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 570305134 1250 570303884 570303917
    0x302070614010e240f040f090b0709092d0c0c05011d010615020d05071109072705061605150103060207120f08060405090a05010c03150f141005070501110910 69
    0x40c622185d140c0500d848010080003001e042d0026003000c0c0c0c2c803041d0b209251030001c4004210222a10030f003000d440c1010014061942c0c2e01c110340d00401c1e0318102d06050030b00107548000103081401d103c2410010410382d440c1c0891001c1c0300c0c1c060310306030410065004c0f03003980b00603500399071041c0c01085182441405c1d10040ca50001a9104c07200c1107414120b84811442c1844d161108080200580100481e41000a4036500042001813085102c80c03416504503041c40c07004a6072440c0c00348582161007005001e088001079981810100d03c1a8111140d016860f10704c01180042a8811504c0ea80c0100d01c1500300701c5007040b14802c0700482d1400743d5000440080c000c0c0090409014140600d41e0364002c13581c0301005105100d461790304103000388401101c503000140100743d10028600c0d0008160b102040542c07800100c1412510845160506404c100040141d100d00803056001800000c00822000407400e000e201c01c0794108654558841c0c2e40b000900c01c8803041c00042804210560310742d00440f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 570306384 1250 570305134 570305149
    0xe061204020409230102191817121317061003020d0609021e01020607090503070b0a05070f060501050414060612190204121e120302070614010e24 64
    0x290100d5002c103014a16040000c035000b04e040105820780b0082c0c01407103500605400900e12949035591000000034400000c846101079200b540f5075880c0318005c02c001144071085150b1400100c0c0342614141190070351001041c1d44508141200003410b400100320747c80d4000c6201c0440036550300035001d01d2610ba12548102e071102d000080c400c22505240b0781c140411030380100c2e0440d81c0a4500d1501c0c80600001419050401622a0052140c3c2001840d22840303483c0c1f0004840c409002010004c0c14209040c2e010b4100b000c440d0100f103400d01284011070031120351504179030f00031440046c039035041ca014402a9031501000b0b000c80e104190034000d09450360b800715805400c100308a0416070b00c0d03030f280164107a1a1441c0c2c2900e16030000c1404107030507000050442c1c00c0c0d41318881b80140409540c0300b00c0c0800c841014007034035500d4811519041540a9002400300910804000411100c0c502c10107044560a0300024881e072952400c02035280000b10300c046c41c9241c1040280002c011080000b00310 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 570307634 1250 570306384 570306391
    0xf0602070b0f180603180c011b0b1509070504080d0f0c0b0702011e140109090c05190503101e0e28060e06070206070f1b020111070905070e0612 63
    0x140c0d280080d0b50742e114019220b001c00e10300f80c002c01070350ba681051060141101994005113490b4043c43d44600d940d0741c000c100040c50f480403c80c0c03510407809507032074000941200400c224515080315407000829070b140c031642e501c0341d1259107846450300d0030318501030f19003041001350605000b0701155071544645c1046001800310b500c492082d205544074003080340134203100503100c051303d40251019592182c8d5500810042841c665861038540e0765844800280c4204d54405006062580814465800c0520880052901100c03011000b199120042071502d540088400f94180c0d03038840088101100040380000008202000e00c13103144401c40c019115030084c0f5454491000d220841500ca6031041d0380101555042007040010740c1500c0d08040c3c87e20000c9411400500032640082c4581e03006080042040c100c9944e030142da0b0a0220803000000346000c0d0903418450b40b40e050000c1181c0422110028116559000c201d41c10105409400c03511160140b40c4201001c1c010011a0039600418550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 570308884 1250 570307634 570307657
    0x152101030804050d050c030f07080d0c02211f0209040506030c1509011101020706050702060f1003060b0607051911010914041107020603010815010f030201120e0123010f0602070b 78
    0xd00c4c44030b4941545007051345892160103025800c0d5024038080c0101d101070484401106031800c0e030091400403904078540c000c000b035100484c00511060034503100080715050540307800705c070050030b494100240b01c083c6403426801115000146403c042c1018003600d50020f030103500800c1c0c2c1c4602400050300cc0482400b40183e141d20124100280d0b0f0f01c01c580c44154041c24000031980c42242d410b142002e824100c0309078015101c0c2e9004182401d03041c2c003a8a120305c0058010b002600c2c00c1d603995002030410306056070f44c012024003403440414024440303600c3c4045001600b5602a540c4e01d031640352041082c3c0d040d414410f00090400001c0101172080400c6102210300107a20b0000042e0046079008001c0081d4011201200121303030b580b400605291120f10071110181c2a0381d07510f450742002100c6000003030000303031808443c4541c108550040211548140001b15030504800c3c8000ca04184141c00341c0740b000c5d00d8000402c080096034100d4400741ca070394030140100c6400e00954007424030602d400c040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 570310134 1250 570308884 570308899
    0x40c08060f0406271103060622050a26010218220c0f1112070f0201090510030f0e011506050c030c0706080601020c041a01031a15210103080405 63
    0x15841e82d0340d610a80140c0808070f9400c01c403e154003a1248400115025040018a03110220b44455181c1e02642d12030705000b041d5600c1c0c06031200c44044020345003031510094604e003c0740840c050380c0f2100301002614450b01034040d00c1c044020342000d4200705010200003a4070400200d4000490381080344481d58054a0140c118411048030102508504440740002c1e49024058542e8950107040019440d41d1590b03200004c05030910910744424596080401c0713080c00304035190001d4a414800c90341c00b0b005040004003142d4032000300c1c6000881107003050000b580d8810f4004000c50500c544604049804c00800a16048500d80800007a19014200900c440490b04d111000030410888508003240025100d030036548107000340040905581c101c0c00b50281c010b4880e00f45c280340c4600350315418607081080c00d085030140158020061500141d41e05400030b1414212a2603c1c003088008441589050703035035004050380c10600d001c441065440c00c420140c0100041440701c0192000e490084a654 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 570311384 1250 570310134 570310159
    0x11041e050a06031515090c030506190f17031918061404090b1c120f0309030905010806030a0606080a0308010f0317181e010207090b03060c0d0e06040b06040605040c0806 74
    0x20301d548481c2e81c00301c111b09040c066410340d101d505400c024061103003034803e001c00300381541045400310214001c4c9180039401c06000c12654001c0c03100c45100e071448100352854a41c10142000345c80d90140d0000c008252602145202d6601c000c0040008110340c4c074145c80705041044c030100c00c0b8401c511401106039114082452a6036991250460112040b02d840c500490240741812415002c2c006c80c03008554003494000c1c00500034004c0090b604c2e8150794420001d03040c9001921405070150446405104105102000404c10322841018042040c02440c182404d0302d002410200c05800024030407040c204104005050600446403000020845503103980d80304507406e12102e80b624038603070b00c81201c2e60034013100c1e0020100c800044030300ba403e0f00c0c50552030b0f484401c203444810341d0746a0944d000f0b10028581140c1180a813464848102c004251f0101c0103000e5450f01d0420b440079182c9250b10418490030340ba291107060f000782404c0d170b8103001c2d6111001c0302404440004241c1c5004541c2c1e09100b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 570312634 1250 570311384 570311411
    0x3020f041404060e01090c0207050607030c0b090c0a09141303020613020607150c03050916050120031315020106031205070c031e050115030c1211041e050a060315 71
    0x40f00945000d458480d00780d80e4030400c03180513081c05052103000d070003004404070346ca0800d582203e01868058864032102c11255a894016060043c0884618001d5426040392541c0300005400284461034000ca46d03030001c0d19191a2440c070182402c1e44501000d880100048e40200d5072507480340d035001008150500d00c0c00411403500c69000001c022282400011004a41c0ca912001c4d40d160140c0e01040a540c84000030b5684005103e01d80c001d200150f00c0030080c940c403c0191442d844031150030900b080d241c0c1c1d04c026141d03403c003103070702000418602c41c00d01107003104500740580401c03948000d009007482c5485100e01c8c0096411583e081010005540080c000c3d0340140c0c000030342d404500300402d191850b840c040c1c8680000002c840c65420480c13411105500c2c0c5101500340ea400c000160452483c140c9041e100b460a02e000701c1c0c1e5240d252146105584d40c612902d00c02804010103107035000c580700201d0302110001404007000a142c0841480410001d0700034030b40f007802281300085c280c10071055 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 570313884 1250 570312634 570312641
    0x1506090c0307050c120a1d0f0f0d052b0903031b1109271b0d0302190b0106260601030c03060e040606090606050a1b0c0b0d090c050103020f041404 64
    0x1300700040d403141200c0c0110102c1c000000744601c1c01c0c16a074040071007081030104038403807011008540c0c0c0075030380f0000300c1344d50714101c035148909040050500f40a10810741d42c15007001240507981040540504800c4101d141481d10310258203040d241085810f0b040d66005401e0344442841a8039480706489c80c8010890f80e1050b55581c04c5d40140021050300d4070f007205c14405014000380c0c260388e01042c4c00e0000702010010342c00701c2c1408100001a40101c0e074a01380401107500c01c80a0381141f01d141c42d0000b01c0350155028880f06070042000d51a03941c10002c0103050101003200d04680c010891004840003810080741a03081042407801254001905500320041d29040d00030345035248109044c441001742540c003520031622520300074001d080da1030000313403828040e01103214049500720000304c8030018040210800140300d0303038491402945802402d4540d8104550441c030981c1d0b81c0b40c3c09802d000c0f090b64510010a02441c0641c0350040400c2c095140b40aa88500110003840c0c2e0591101507980745c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 570315134 1250 570313884 570313897
    0xd050f0403082a0c0c13020c0703021314071106060a210201050c070803190f02030d020d0f05070e181315140718150c080304060e030a020f1506090c030705 68
    0x141c4480d00d44c0d1595469135283c07054018024454050600304010713602a5009840ba02c2d9070100140203642d20319020300030041d810442031040650b50b02c07003d808030035800201c540a03050641c0d803010740480c055a42494040c004c1c2c00588100700a070307020409030800620200081d10219222041030040344010b89142c0920b403807441135409650004510144000301502c01840b400810314240151800c1c1a07460307050000704e400040e04100b001458900a80d002041c0c1ca208440340050b00e420003a00034000c03180151120400555060f0000f8164a81084141c0500f400200d5895084c241141d956585842454004000d04040421203084030f449a000f00d103590b40301e414041c6646800c0708010625030104180310f14002c410034010620902d00042a2802032582c4c490028170340e0691034014141c0c00080007141c1442d100c10002e0302240090001d0030030628590010000070f000d0040c00e42c10034508914100151140101308621b030350f602e0010941001e600c0440070382d01d45420304201c0b00f40c481c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 570316384 1250 570315134 570315211
    0xc02040b0603090a0b01090c140c120301090902190b0a141603050901110601060207050d21050c01140c161407060909141b03130b0c0d050f040308 64
    0x2104103c032841001c21580751091007080a58035582c0c860b41c01100b15010001c1d80c0c00001c00c2d12002410300c1c0701c9000241000d144080440e07500322001c2a402e031207544241c10000d031407910b401c0d43c1e8045040c1034008134001c400440450b4981403d00d82444068015106c900007007140f00d011000c0005a80c038100d41d55000050440b4007154030034100a00366500050b0324a0004110005008012101103049130698040341d01826190b4900760801103450901e400c1034400300c0b0319a0308200c10a040044d07884074612940ca5680d182d030402c4020341e007151036414017080c50b00c100784108400510040c0443d6034034804009002d18101c0c2034240f4010b00c40c48141c1644880c80384480210f1195007003c010001c448091405010407186240030300120602a5011200201c0c0c01d0300c21608100c4440285601401108481c49107024540750340700300c0207007500c50601c654400115600410603502070a580706004003042e90060425980c0203084101c010f0224240342500d141c101c5402d48040e01c2811083e000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 570317634 1250 570316384 570316387
    0x60f03010902210405061f080f0c0112021c0207140f0109061a010203191202040f0305010c020606010518040603020409060203060406060207080726240c04150c02040b06 74
    0x1030740d80841c000c1d4070180700c0480310700d0f04295291003280d04212a51043da40100a070045841e030700ca80f40b00c020700842d03000b10500c80006000c41c0b144d170200020403800e44640c009215001e0300000240c58880c00380305060700103004001c2c1180755005482e2031b001c15202d15100503a1b6000b1402c01e0521000714007a1044a0300074403c280c149550150040c215090264a04106000304540d4800401604184041c056001441600047c600c040500b40c1841d1150600940c0508111900400c980c042d400c030340c2c41c2d005807413420300600c4001d00c1120070410f81b5000a003038a080a41c0041c000b805004065420107100e0034004460f0344480c0c204c1c1c0c00940d80a403041c04107560f20314010001e500100d0310140035a19140340026014400103010b0f0441705040b003d895680d003807402c0309200e100c44a0720002030742a06254840e5072030f01008003405044050032a26402404101d01401282e0054a14120403409020a00401c1c02c1803940020000a60070004e1040e441c0344045005401040001640401d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 570318884 1250 570317634 570317639
    0xf01060602060708100e011404140162070e150306010e0c0d111b190305090609030115030c26030301140a03060603050c0906040207030e0f060f0301 65
    0xc002078614018203d64845506507525100c00c00c00e0600a032242c00c08401d050801004078204095407502d01c2d002c050408070714000142e0074440c85050030b0b8040706038180e40345040c0c18080410180c0300c5038003500c0c3e940c1003030040361014503000d240f00880188041c2190340d0f2054410000d52840000502880b078241c0d15816920a4081311010040b1565542c40740b44001105840c0f0700460494140c4a1102c6d95900c0e5403298400e1400c29003242d606207200783d07520b100a40139800b424015141e01c0052034440141c00c0940084182000b220644510000c190801e00c100001d400c501510320050f001c1c9c82070b6032902d000e03074002400b51420020111b070301c0d00003600210074090380c40411019a618a5403081c0c0b100b415010300c00d440d00d0911964081c0d030f04184014010f0003080c2d11084214a001801d040c4400c2c1c40c0c1c2c03681c0085840f83d81c0704854aa000012030011810480c000b1540610f0840e021410319a46840241643c4052002244250500c00e1100c0050341d811080c3c865816400e000d094032582c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 570320134 1250 570318884 570318887
    0x25080a020910170a060e0309010206071d1f0f0c0f02010810051306030b090304140d06111902070e04150507030f020403050c0901090504080a0503090c100e0a05010206100b0306030f010606 82
    0x5200344c140c40c4281031000c000d030110400003c03540c181d80e06134007c000b5680c1d0000304842c40340d9400d480e2940c0031002000003220355a21803048001e102d4440504c1c1a844111401815054508104100b441050806038002c0b50355800d40e00805602800c0400b440da41c0c08001d03850120f1190051513010401c0381c821000000c00368400000c1c0e0b842500d0b0fa4110b525074a040d6a52405140b040b081a04e101c851240d9031414414a1002d12038846c20000c42d00c4410780e14143d816800c00c00490308807000c01e4a00401190741001050010050010442a039051a4841c42003080d1070400c0385207040e45030b10201e4601c9102f0351202c40d000b50748035400c540782ca840f0b28020b6214002141c00d50b12422050b00040703500702c2d4a2041c5030003998808401e919091503080180c816800081c01c0c141c40703000302203165407035490b52020340c008403070203541d90b0512001100030440d00400035001141107502110421510181c07947e03e40c000c0d0b038100080640c03299075210003e464403084000321007031542810000075405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 570321384 1250 570320134 570320143
    0xf0c1b1a16020105090601050609040b0a0b2205040902062703060c1c02190807020a08040e01060f0f0914062a07091503060c03020702030a0525080a02091017 69
    0x721164000d1100d600c07400245a81c800d000e0040c0b96011004220004141c600355214011100e0083e207001442c650320b160520701600120340b0103080e859a148199201c8251440c9680542001c0700c04101058040d00441c540d03010340407005807510500e030f4102100c10284800101d481c8001811184140707030a0b60005e5180d0024003203840c905203c2c01c06070704554064020340d03059443c51b001450510103a840220b0710110081c0c42e010560044585610106502d0303401000070740608006c064665143c050014842d0700f41095000400c16007a0921040d80e901c400d0030800c0341c110240c05031501c0c00800015007113101e40e8040d90081c41c0d61146200158204407400d00514174540150303895969121003080a98212107800400100e03c0c01c03081c000034086901c43d00030300c0001d140042c00c0c4070141d404a850b04152000a5509602010040c0c5010340e03a680703015034110102d80d200c0e05042c54a00304035076405030f00d40000c0c0b186811a002070200c2455040311302c0142000c01c80c07020182d407860303040b5486 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 570322634 1250 570321384 570321421
    0xc0303020d021615031d060c0a0f0302120a0e010f1401080106170304091104091a100c21031b09050306010e090c12031603120f0c1b1a 59
    0x15018108503041d1080500c401c43c01101c10505400ca002080c1400c02c500800214101c40703044940684e041507002c0c02005034510500d0034041065880c1c0700c5240c003804030021030800c5002c050041000d9441000c604041c0e6400c0000c031300700030131480d030f60030300443c05020f8030885d402c143d038038280911001d05640c1b0b00082c1216800e0008209140d04d40e586410078040100404649034402c00c0708011021255004234039050b051440705e400c01d901c3c0c1ca41e00043d1820f15903c41812a484240d0300c00300c0ca00405590101c10b8141015a8080f02e284d940c6d05a00760310070084031904106071207104401340a41c101c0d043c800740c0e00189043d20440c0c034100ad0b28055003805024020710844002203145042d20f05118000c1040d1001003002c1410102003084a6250040e031101074081070110b0384901040c0008015007034800d480b8030054181074911a4102c0388400f180c0801982010a0340913195000f40300030088402042040d4422007140c03d1030141c03284140c1e1701000079040c002c1046a0032500e01c0c00c190b003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 570323741 1107 570322634 570322637
    0x71208041e0303020c150907060c0602092805010c02090402090907090c050903160f050d08090306041103190221011d010e161202011b0c0303020d 64
    0x10701540800c0342180469004111100214400c2c0208000c1c3c60711071400103036038a4000e810350360350040ea111f242c051101450854040c44a10340440d102d090015010190000744040c01100d20340c002210160403420b0708402240561040000110301500203011016903245d0fa000c1008580c805040031a6611843c00c001604191b540582d51403480340b612081c0e00c13070740c00381c00341800e250101082c036a141c070340c80d00140847c043c82d6030320105a41c000d86450fa2101c0482c9001a52440341c64581d03541841024104802c0214001a04410300002e030141c5408003074140040100e9030120200944c0300a8007480c1006070040040d00071001032100c000811004802100000ca0091001c000c1016944801610005000030001202c85040a0303203581720142ca45500105140d2840310004d040000300000150109102951581096005131640c0e980759520b1a0181d40c40c14803501c41030 = true := by decide +kernel

theorem cover : BRFrame.Cov 570143884 570323741 := by
  have h0 := BRFrame.cov_init 570143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 570143884 ≤ n) (h2 : n < 570323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
