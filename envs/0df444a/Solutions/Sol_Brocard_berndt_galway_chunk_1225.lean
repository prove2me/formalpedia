-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1225
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:51:34.406246+00:00
-- url     : https://prove2.me/submissions/9d1bb90b-1e08-4550-966b-eb078919dc23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 220143884 ≤ n < 220323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 220145134 1250 220143884 220143893
    0x100c050409060e040b04081c0e0309040c110c06090613141008040302030a12060e0a091e0201050f09012304031a010b18010210090c051908030316031107 67
    0x3402801000c808600300100401d840c1030103031089028507030020f000301c00c965440c0c4138216103030420580540d28001004444030b4462580c007031801201c5580018658032108002000112079006908006201e1925909030440d0310100300c1030341141c42660792503a074054140000e0468895010603075043c880500020680d2107024040350040c0d01e040d10b090b20700080ea9502500d14603022203006005034420031000e0301c2c451280d041c1250742c0b49020400300366640c85030301108001c01e08490041d540d03942c850300c4030140046d2081c2132a88131860680c1c200c000d03d094000034610b101d1400d501c03400c05e00010345541d0a9101700002c080c0e440b0707004a0305a0380389228005184581c0f261205580d1960001c2e50307280e20006817080d04c0e0481d01d110084500c0c000080c40f4140003e545200442e055000303044000701921034600810700310364800c2080b82c03542c030b050004001c03002c03840341e07409503a4820300042449018070020440b0b41019400105401b00c1709110300c201c000c1d050241640601200106480c000c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 220146384 1250 220145134 220145137
    0xd140c04020f070b0601030e03031609050904060f05010f050d0f14061006020c03010605010918090507090903020f0c0609010c08090d0308040b07023c0a08090a140f0909100c05 77
    0x15114050a2495450f00f40c011002e60f4095402c0e159113400c1000403070040bd014013090166070101d03003480c0100f2940c410010305e028400300c805841c1c440d03c1e008959562282c2e80306103800341100040f480080381c28007000c00d14190014100031b0128601d040d524083c802503010009075074214604a4840b8600491145040420342c40b50780050705c60020900264034040c000e440541c2d006a4410b1100340c40c08496401802156031101c400c03035a0f81c0e02d10703404142e0503c803e5000c4c0002c0d020124032640e5516009160a100c0b4090f500c843e04800360400c00782e0355110444591040900c0c01c2c0c200c600341030400c440d0f01e1084003012a4800c203080e40344420950062041449507002d283d0b5400e56640381c10341640c4964040640d429065100340c0c8100c110b003005582c0103035000e0340c8400c2e41240c10708104003c0c07610803520810b840301d0b1800b1400144070310f001410300c1c01030f0192881c1900d540c51540e001c03855940704048820711500001c00003401d281c0040142080075020202c0a00c040b00d80d040015045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 220147634 1250 220146384 220146397
    0xe03070305070209010e010b030a18021e01020d0203041409060a080109061a0301020a141b160f0b0c120a030e0307030914010f0503060402181503010e070e0d140c04020f 74
    0x40001d04d00000b00710140c00c1d24103040316010050149103a58001e0f44100900e840350000400540c035650308070260312a00c0450404100200a55001c5000d4100184c605500c45000380115401044240800030340c0c1c91401035004001c0c1c511501513100ca070b002400e41e680903044448950300c0c04030140140305440d0428194000c0c040381c1812002103c0c001c0c5820703841000407403400b00c2c3ca000305401640d480301c0c0080c00a4944480c0d608038802c2035075001418200100080161384800304810f020b0191501544070081100c1c44145241003a22034a20b42c407003208015003040a000402d10741c003150b00a0708038543c00d06101d401d6039074445075031a01134501080390045581c08410843c44000550041010380f4688440d80c841b02c4c1140c0e20a410030020f9804210700e0389503d15040201e1080341c8a580344406001200381e1825182e60520301c0402e100c005c01030480c41000300011084c5040d4441e03108216400e50001c0e21054442403c4141500d401941805541c10a10004240b414041d000016016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 220148884 1250 220147634 220147639
    0x1b061b1506060403050c13020c0304030f1104090309031407180507030c020102040617060d052a09010e24120c040f110322080a05030403170c0a050c010e030703050702 73
    0x80d441c0c0c0c030103200d0300307000c0c41c00010301e00d41c070034042601140340076508080c0c103404c0b443c005032070040300c5c080e0301d0f042d508103030b00840e07c840c09104c0b00300401901580b01c1c0c0703220405850411021a05480050100d0094403015010ba52840f00c0d2010518040c0145405400d6184048442b5100714198074001d28027144d5100c002850954080551441802103404441d0f080c2da4000010004002c240e120200180026a0009802a804c0009242800400c0880d05405000050020181c01c42c80552202446840c450500c0300014440c2d680904400c3d80c000b880c5844d0a48a01c070070005160f001c0014405640d07112442c60164649124001003642042e007068606018509403c080081034502c041c1601100345d1003480021451203601e046880c0c00d01500ca000302d0540c0041c0c035825816800356080d8030010780000200801c0c07581104002c01c60070003d40802c5c0c0e4610b0002c034003160b2405800d022804100c030019002008200035001401c08046410540b540e0b031035549409032555020010490 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 220150134 1250 220148884 220148923
    0x140c060420030d051e0403021002010203010e0a0203010305101802120708070608010e040201111002030403090302090f070c060c0908061303030c0c11060d020d18060605121b061b 78
    0x54241008500030560032215224507041c00c00201c10a040c202c05e4031040b51300721400703010000150742d4112200209040076000147e032135040c03a08102e03014000420381030002d40108010000180e00007090302c0301d85140c14002441c1540024590b103141c0104002a600024540c2ca50224890100343c0034100e40100c02111201d0345d48980640e1000303000d00c5000810641c800003e00554000e180340c2d04400c81d0a02900c2110314045210001c90700155025800604424014011420031080326a0007054410005c41903247c001402807003991036090080445448150360104c25004070101c1000d400c00e08141c0c0c601e171500c0780036206076072801d0a096000a0610981c400d1060061408012103904103101c103012404110034008a98008044000031a41c04c00c40000d0303214040c0b25101145100000880c5c0c2000d25081c0001942e185170041c6114a5901400b06021070f400920301c0c0358059803c1008650b00048000140c45010308185800c0c1c00411040078040a0000b0400c0b2018211005045 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 220151384 1250 220150134 220150193
    0x6060103090203070e090102190302041406162432071b03170103080702030c01031e27050303071b0201080708100504111324140c0604 59
    0x1142540c140e0751002c0d4040e0003810045c05404c1da42001e142d80301e40c90704c0000d46000022000c0c2c001889204c01c0883c0001e9021800f4040b01250b03801c02d01c2c2c201002c588003810401c025075030380609a8114801013152000c1180c592001517000d94991010420403020060103981c0380c2c0d85014081c0312500f044104401c22080c01c94a01981c44490181303e5a550301c0c5800b0f10482600713094030030302002c182e091042260601c00403a4040b52258007842c41520996100c1441d481030500d020070101110341414248004550540d4504044103040760300a02c000c200041800800442071140c00b0204600e83c0e4800c401805024000000f54002c031120360f201c1c0d105023113420141100913642d0000034005501000071561292180c4112034004030b07103541e1402d1140c0d0b217100080488420701d0100d1106a07000c981845d5207126a008100205052030126880707424808a02055101e04d0300c0c00ba040c80798101412007200303140002e940241e0088400c035100c03030515041558051052a40c4483c41a0207038480 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 220152634 1250 220151384 220151387
    0x1213030b06030a1703070e100c031d09070c02010e0d06090b010e041104021b15070e04020f0a05031315020306041a09070e0d0f08130b180918030a11060601 68
    0xc940c80c04d4009407150481c5805000d10300031a0b00181c050070420000f500914643c2d551080e602003810401d4aaa1180d84900d180c0a025050403001405021120b440e290003503440e81925558000503900d8004068a9180300580320b84102c0030301d49404c219901072030420002d85034020704c1410300503000369645070390f14030000100c035008490042c11241c20702c15182c1941829000360141490300039050b5610401d0002c810f20704a4413030310074000ca44404023807201c0c042d0058246241940b00340c0e010741c9800031321a5464103500c10102d06100700304002000405c1202d480c1d00c0c0c074203410750101da50b000c0c0f0310f140c800f040065041514140d100c3d0f03240c454406901d07510703042c00d505d220101405514040e13540100654a80583c4155560000b00c40100400000d510741507014a41d4803552140d612001440b40d9461000802e1300320540180c01000440b00c10311103450311511030340b011240c07180705a54030b03c4600301c40740307140750848214800422409201c07a00700801c9604041910308032481541c0e03c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 220153884 1250 220152634 220152643
    0xa02030f0a080702060708040528050d0b190209060307120b0f011b0843150c02101a0405060901211a10030b0a020f03010e04051213030b0603 62
    0x38000e111034400c0003c0801400d05c640502203050046a0325814180c0d9403010130040000031981c400001d071007640c85070b0110108980000501070903a4000c01c052400d42d02c0741d070212009804030341507000e6800030001159281e0111030141c00040c14045e103900744004064044101c61004d800c0c5d903410140000800d0501d0304007c48030080581da00d414018605034545694070111000b515814402c100c08000d0180c0040c41400c0ca045e40c20f941c10200100c400481d202645050603982c0700003048641c540802e40d0000700c035220100502c0002011061004c0c241e00e400300c103501d02a00141040c00501640d2690240c03440d81d0041900c003400655281000c204154000b4021f01074030782040a01440d0040250500b406094442d000c100184407426444078503a11085810b0701140442d030a0030b200700040d41c01556009558041c0c2941032510464188040740014054964804022800a803d00a080100c0c2c044600c030070228994031288410501d004c0001e500064698030420780129245040005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 220155134 1250 220153884 220153903
    0x50103330608011a0a0f020709050c040509060906030a03050a180e0a1b020d050f040b1306120b01080114030c040e01020310060c020a0504020918150103181a0c040b0c0a02030f 77
    0x8411032901704080300607030b62500340c1100b010842c810010007040304101403103414011111100880d880d5403400e01042000e1800914035401000808107000301394900082c85881e441d07041c140036031240c04a000450b081c3d142c40400c6514545410000a220100860108c5c01500f28950901040c00000700014021144200c2040140d1101d2070507190349101d40c02810034014824109450a035442082c484690044001040102c07219002004640d410401a1102c4c0c0fa21020a00681d940c0e9400640389100c148100c8c01040080c40c138107186507500380400142030500400801055280b009114000d4100311103080d4003071205900440e000c2d001d0343c5000038995006003c500707280d04010911000e0740220030400c4d081050111481e10f400091202d561140d000c182c6904820880c4034001010b0310a041030000da001081e418940c04500301c0c41f989090341c007030811109010740340d4102c0e1f030300ca030b105079405040e858901140141414401080a13444540203c0403141c0d04c00b10038018544682c0080f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 220156384 1250 220155134 220155179
    0xb0f04020a05060307020c0607061a090709051909090b01080c0307083c0102030915010e07030e1002070b0405060a0c02070e0402010203090a06030c080f090705010333060801 76
    0x1a0740c10401d0346403540007940e0103034192040c0c0e001d0150110100c0c5181d01300301801c580325a1038440d070401031290280d4582c01098212014046400d00f24009021030045000e03c2c3d016081c081030302d5900504c0411440020081003804001c0c1d641c8505001d0b541c03a40a024120550050b10001110762600141d0716060302c070002c025001605038400c140f000380320030130316445d15488014500081020070009038088140f80d075001507904d142049855081c0352030300030101d5054a543e8014481d0342c10082066500410906002400345070003200c135850300d0b10103403150001d64000600f507001c003d0480140c5000e140f05074215801900c914038210261046040203400592000b601049102e03158481c1540150060040d40d1400d81190301090f11004c1da80c02c0100441d4440d0524404203501003403e40d0700c40d064841043c034909100d803c09444032510311649041580f0382c42c420440101507001e00d100044580781440388048210405400c10aa0744120342c08160b1020001844200688060f400c40b09e05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 220157634 1250 220156384 220156399
    0xf2d0c03020c1f0902060c070e0a02030112060c02070b04090212091504200a150f020705010206060f010306051206061207080712061e02130b09060a14120109090b0f0402 74
    0x2a05407850000814041407001c02e46501800c4c0140e19601c00906007440000301404025061014000407071001030705a407881407040004003c050740710304401517019802040442d090802590403451300407140c200c040d4076a000200003507000b001d0b074000c1400c0204484010402c0d544c1045035030320740700d0000c058040315401c04e002500140d00c91550740c2d41329440e2884001d075090280081007403401103411600100c0400410103184541190b417441c40603000b40b009241d9903003840d0000b501c40b4406400c5a000742c204c07554051081c3c0c0a6005403029103400b81071404028903041d80d0383d40e5603600381c40c903078000d15000170302040f001c0012170310f007054664510041140601e00000801b00c41010003040d6100342da200070301d00d080341060130b200360740011040c03026803500c100c50386144850041c1ea028124640c1e080018000d03a4441c00c0c00d95036000460b00744108149043e107540c0c2d1180c41240759400c200807010380041000c135240c2c0d016192060043d040f01090303544121010180200644010f54050724 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 220158884 1250 220157634 220157653
    0x1e05060714030f0a0302030a0506030a031d0103180c030b101508180a0f0b0705040807050f06040305070303170c0a0512040212190510020a120f2d0c03020c 68
    0x20340d09400304038035000c107003202e1401c0c000c0350344400a40c000281040010340c0000902142c62000c1c080c494000078114050002d03150b80341d6010b0210741207480b03482d4200000205624043e8040d903c00c03045050064034a400541040c07404140182e814082102d642025002040d524019031700076100351452004c2038240b110004409480d0518000c01000321842a40100c40d4108418040c0c045c1291146810407a840b400b49854616628010400b10070020180710400100100040420445000f81c1e03101c80e00d4038020020410900c07441d00064030310302c1b507841300008056102e001c0421074801d05104c0d04040c0c9600c05481124450002a440019424003560190300c0c0002042e030b030802d00c000e1005403c003281e020304c0fd00b49420131141c0b403200f41d08069041c0910906001681041c09944801c502d03140c103030355000c0c107000c80405507170031960340d1084042c0c10718000e50300c45054040300307880046e0892504128080542d561208a01402d410000300090940c001c1c000e8400c031070f0b07286020f03001c1d503003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 220160134 1250 220158884 220158893
    0xb160c080d050a14090d06090212010b0a030209101a0409050a02040501050901200607200c01090e0405122a0604020109090b0a050607080702091315020c1c091e050607 73
    0x304413031400001c07020031024800795240345d111350b001c44c400c080c0881e900c00348c1d004201b810760300e14a502c1241c1e41405010542035640b003407840300b626412a005401900c410a102400c0c8002c1d4104c14590380003040101000d00302c440140c421207130355040500a40e610800c5031401d80c0074a114544c0490024080c440c1c00c1e601070580040d002c0c43c00e095084449028408403460100e041d144840881d5020608044a211409601004c2000f200080c4100820140001d1503040a0310480e41d503006030b000441c0800c80184840003030301440b0160252501100c0c4c41d501d51401c00310071144080100c4458007030711191301260369807007160147c64a060052401100a020781a608025607114040c460f000c1a19a2102d01500aa900800c881c9403212003500c1400050840508062203044101207114001341c6405152220b4551080b0090703204c1c01c4035000c1c1c42c60209040d031944092035842260140841d03102c00010211000c06c00c1402c841a01d8101c4041ca5036164021150080e2080000e540402d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 220161384 1250 220160134 220160147
    0x210c0403020d15090f1401060504060803040b030c0c1516020609100c0507060e0703030809060c070f03030f051e15130b15070b04051006120b040c0b160c080d050a 71
    0x300808407021502110751703550f8081e641142407040711a039003018061400c8550911a05000c1c180c26141040b4213802c2c4084560f50f40107501c2a03103030340c01c0c0000009044009100c140c400c0707440c135102120b0419866a1507031060400489124007a20342000141c0e041510024549000d5407001000c2c1c8540e903107402548019042580d00c4c5411701004008880c0010a9445101c04510200000c0c00303180342180b6005000c52130107011400300d544400c041c41648040306080318055584071401c100f485001d0319080d0040e1503811428110b00385051300b00300d52542500c0788008206044a03501b0180d030b481c04070381020000100c2ca140c1d0010b003955400203e02c85250f1040c0409180103022004020000f1440c482c56030107000110782c46003884062104002e0100703c08030307600c914520300b0f000072800e00141301103000e000100580302100c0d80000ca000d2248050205c000b40121040980e501e00b82c002440c04529104003040311a06110607001a801c580415030103100425503984602d0f2441c10a411100c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 220162634 1250 220161384 220161413
    0x1c0507030c0201090512030319020a0807050706110706090201030b100e0f030319020a121d060d060503010e03090306100602070303080901020904021804050f0f2208210c0403020d 78
    0x144144940b002c500b541d00c1410140414460344029540d9190109c20001000140005811003d00500070040401d400c0340501d0b62044080c07401d961624014107222018000c0e02021083c2c05000141010901525030040b040c6c05001307880c1801104400003c0c0f0899050700c0000000091100003040200c1c54420350100541170b00070100c0c0d092514100e00c103520390000781c8000016a000b0708249041003054105e201ca82e409500300600c02600740c2b4540c0901200c014640707032140e01d00041190700e14190b980000080c180150080014060425000d0342e651b00c05880e19120b80305100028048102c02040981a1004e0358090b2012614569081c0d40f1003202400064980d502480380080c15107413440600f440140c02d1010800301c0000d1b4050104444000c2c049800211404080100c00841c04041d42d40040210139001c02459805d000070b13505520080b80107005210000700302030000c85c48080400341064080300009262245112003103075109900c402074210400c40c8110002c206400107071005c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 220163884 1250 220162634 220162637
    0x19050402090d060f0903020706110618031201151704080d05060604150f080c03160509060c0111040306060b0403031202090f09040c0e060f0a03111c0c06021c0507030c0201 75
    0xb20b44203580c81006a544182d10b00c40e182d0f944091485c14107030b0400070040101501d04000c0340c00000072904070f403a01f5000b440c201c10304082001184000000300202c40030340a40e080110b089507112440d5544540005002c040010507040d20b0050b410a044925405280c0c0140320b1480c08180740418006480000d040710390016013807000103030140700400500d08100b00c603507a0f0302c010780310110040c1c070490010703106800242c81071040100d00400c50001c0300c04845c0360308109803504000700004907944644246059654240035400f41070880c0f03603003c1c2090702d21810081c0019038071604280b006002d144030140c00500c600410a400c1c0c0341540c01044600006001c051080180000ac0f4400712800d0b0760032198411103040030404038213146641a00500100d0324400b00050200009001d031079103010140c15041d042000c82c12a035a501c8601c0c4004c01c40041d03a081450030b5080c000020903203481070340302502501c42a00240488042140001784158885500744001d589044804c40200340c812070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 220165134 1250 220163884 220163899
    0x2030c060f0601031413050d0e030c0d020402040f181b2c12030c013b01020405090412170609180703061b030b03030301051f091509090b1905040209 65
    0x3c105d41c5910b480d94810342d0800d403c00808101840c101c1c0c602100041500c0411641c2d2a107440c3e6580c001ca50282e6121003110301103020b107070900014000b44260360149034000400400083c0070801900c003802c004160311f0040200c0001c03581e03005a00f03503c80a0390700008180c3d412640b100017854441030740700040b00580b03591106003000412501141d03002d01030916407001c00d49111180f400d018403d080b045004540f40383d03450900509801e1002545800340800d840c5010030340c810303004d40c180c2c0c0c0200300052405016041c58288104101d80c0f00482100040510214850304410040724034011480600b01039890355850420901229081009003101c0c004c031140000459a1405091300d02841201020380c116102d81e0043d0440f18984043c50103504240010006603540003414540d203031514a0480300c5241d0800c0032600900c00346c0100d050302c066240051500d0307502403100303001d450100d001044003000380820400380040c01803441002c40321080703051003d424170b42c0140c100d041c0301900c5603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 220166384 1250 220165134 220165151
    0x106080901090f0b042105030606070302030d0c050a1404050a0b0d140103060b030d110a0b06120d0c0b01081c0e0301090602070528120c0c0806070e0108010602030c060f060103 77
    0x4101d1410002d4041e151061500306001c1404030741c0c206004041400c032800306da420b44600c00076145000061031188540700100c0c2c110f0905009000711490034601030420818058609400b070541c0d00003071f8035840080c4400000307500f255070310011075081d500000c204800691600101008680c484040070703030301a0316a501c0103804c807080d018081c06544074100108045030391105151030001d0550500040141d03580c8088028403000c108150311039000780c2200e03003e9407074801258100440082c29200351140c00f6110303600c40d51041c041d1498510910f42d041c45642d07612042c541d5031301c8043d41e40b10340c403040405403d01da078080c140c1d00f050300c04098004100c61140da00d0350300898002140a407041e81108124407203240c0c1f0040502c51000031303860314089540d0700340c44000103400251441003d03c41900d07155020711a050410740f004186003c1201d00364580102c00030f02901c10a1501d03804500e0040012030060300120980c0c040c1100e0f00000e01e103680e9244040a4028405044a414141e680340710b0f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 220167634 1250 220166384 220166393
    0xf06060409020c06091006050901030b06030109050a03021605010908100504060b0a0f050f060304080d2304030c02041406060f0d0f06061814090c031b13030302070914010608090109 79
    0x1405983c4101c00142c010751030f040e0f80c9182080c400701400101c4c0340c5030074011701a07a84e84000c550305603a001501e07000f075a680d03440424010843c001c00540302d880783c041307120304260380003404203040000c0500c0600b50b0b90340d0743e005640312022400340745a6600400d01400e150605a800241e006c1d01400d404203a10302144041909054590801e0b034081050200070300460400360600b400c411001d551180c40c52409885414040c00744041c3c07030400c2e68407414040c900c3d10324403051003140b03481c204141c3c1c07040c2491300d0007070410440c0107000ca000314140400d610740c03500d4400d4500e00c40d44029201614040c00003020001030340c031521450307107203554030f501d050303c90792461284401914990301e450110040e24060341120a5582e8046a00e42c21800740c0c08030306460784c41c00b998020402c0800302e922600c481110b80f19000c0c0481c0c001d01c0000c00030074414401c242c104500c004036402502510800764440c1111425100d41c4110301c0c000340032140040015603c02c502d00d540c040100800000d40070450381d41e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 220168884 1250 220167634 220167637
    0xe0307051002030c061b03010314150114090f090c2412090f0706020304090216020409050d0905060c0303041b080105010b030a0b061306030c110f0102030103050c010801030302060f0606040902 84
    0xc0300750060740081511080500c003000002e41007201c01b00c2541d02c58007140c03034200051005000041480382c00d0369442002e82810098000d074005500807405d070941c1c5806403400703820f29030012541f00386414000728140643c1c049008d030040004802510510304400140007081510240a4240300c40e003151244040c8813250240c408820f03d0724901000f07080100715103140052615142c9480e4210344c00820105400000300c404823240a003001d40c65001c001d00903a81c1c060f25180c040d400030308000e040030410170040360302c080d03001d06038465407000354403141403140a008400300b151842c0d10400c04107011070034000c202d42c07000d10603184004a407a150048036003599005e07440411014404002d111040f8041e01a543d803804003038030300e1400c00000480013030360600640310f19410300d40c2c1c40003881e0309244520300002aa81c540006c0390030382e048440d1b646000354402d1100783c07454001c00d40000c00da9032240600b141202d42681c000c0010381c481d84000280f03208041d0509034401802c2100003000001c030300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 220170134 1250 220168884 220168909
    0x42a0813020306010803070507050907050313030306080313050310020a1d03030403050d050403020321030f0924040c06030e030403080c15010e0603070821090303070203060c0d1a100e030705 83
    0x14003951f01d8940514005283c9140382d001548181040e400b00454141e10106407a0b01000014662000303041e10706054004021503006210180400a680c040c41c1420f0000101150b100b9800c90b158041c17011480c00403405850055000680886d81a04d03140c03103030b04184500220000e05503441c00395207940e014030b0002c03040c544ea4042240071400b0070551030240300e03d80140000c0e845510000c0d110400400040c4401031181420541840100d050b440d41080020703a9240e103c1d0a0100d04121601201403ca00c2100d00301c0b03600144e505d02007200c0c0d109010b01e0000034602c60055052a040d545e4042050f0407108210819204808041d0711107a10b40c00c03864000c1c42c100c500115030f0700749601414244912500309041d1507000900d20054190008054001c0c41c4003000803903102c00215000906501c0f0340e02c00a5454458807081c0403581c803140c8000c0c01031442e03800c0d081000490a450ba0b00398200000c5e10075920803091500c1ca08410301902d415285020000c003510000c64465002904008649 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 220171384 1250 220170134 220170149
    0xb0906060618150406170c120f09071a070611090a030807080d0615081f120503190306050a1409010608070c020a030c0611010504020f01230c0a02042a081302030601 72
    0x9491185603407805007038454020310486801880d115202d110800da501004d00080e11761062790000401640b810300c608005000d24070501c0800319120312202100d500071200644211707260a41005407406103008884510030080d021089162542e2202c0b10940c0141c401510f001608000041d00e2102d580300d0300000e0002104908004211040010a0450300800c03e100c0c05000c0090a41c0f0380a214140c00122040b0000d5a43c280c00c0a2070090b0650080c566014040300404075038580c400e030035400020030b42d241075407950207407a40c0340700080c8091406031480b604182900c00510002c0d116210303403030384165141454401c40d03002e940850900550703588141e8a00300c20810a2110603440008040b20583c544000c1c0601d080035000249409020601a070510500c4c9a8121400c15898411180400d09008042d00c03500c105a038651903820000040788150300e0543c80e5580081514003c80c0d10345058100c046d011130040d40e09440c1684040d150202044504422800580c0c0801c6410f0103444c2c3e1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 220172634 1250 220171384 220171397
    0x40f020907052b06060c020109150504240305070503010b040308181809070605091516020a080c030d09061b0311030a020c0901090207080a0507061d03070b0906060618150406 76
    0x820908404545041d0003170b00030801030180000140c0c0c1c3c026001c0781074078080a0b01502d203c14100060300d1a106a62003c0546c6140305401c80060300b1952900300070030312a8506200c1e513034981030100c816100c00d0107080c020030340c244070038030100d1603450203062141c12842454003e610142c0008041c80030b4240d48a154514220400480700e40500150000b8002410b0260400c0c02d29000124501c07a1248030210200e0040303030803103a2840494040000f1900079105440c540d03110686107031506c1100150b140070344078070403c1c1c81004e81b21f82c002c40c0840c1d20640d501010401144848510401450402c2e800c025110540039078011003440280031703101d503640040c50b10103c8801409a0198141d0210140d180305020000114a6000448079082814a02159922054a403400051140c04555520480c43c041d81c046030490000060050030f0180c101001203582d00c070b80c055503c40701100c40d140c00078000d02031415408840c90303e03540e40000040c25141c1ca41f40180420100c0e0300154040300c0060b21 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 220173884 1250 220172634 220172707
    0x1215120f1202060907060c050307170706051e04060513050d0201021b0d050906030c220e060904050d120204031505180708154b040f02090705 62
    0x15400c0c0d40707140794045001504803880c04d2441940c450190784a50b1080c807150030319440c02c026062081383c81e506c1c2d00c96039400c001020140c080340709070032041c0100e98903032503c0c010409000c0103e04500c80e854035046c110b042959140e0303450000c1c01028103c25800e58038600d103000003d100748203440003c3d007290b000589a40c0650300e0400904610000c1040381e8101419640f40268003034211140041305403640b5a590312171220502140c450103580384154114454009075480340c1d00500e1b02182d07100c0300083e110741c48207410050303644426100204503a001400000380d580c001c2c60601400d40c13a142c001410550399448100035002c04c0314112800300e5039007041052212107010003d030490016401070200c1030414000560742d8640c2000c00701408d41c44800651613070054405150210040302c0d07aa8400034908420b0340702012203800c1c60003d102e44034000384036901c4400200c2d00c91600041d0101106109400703001d0040d0025200004100080000b49901140c46141031820300b0514502e1442d040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 220175134 1250 220173884 220173893
    0xc13050601090b03010e18030706110304030905090f0a0b060f13030203071208030604090809030a0609031416060902010327060c03020f03070f0909090f060e0309011215120f 76
    0x80711030f001402c10400500043c4540540019065800341d0151014110100c0d0009014990301507074074010315841c181800c11040d01954009107010b98402d803116804161600100098040100c40b80c1c3d80e10803070b400005185000355080444201c1001d00f000e441c009003056900225840381070010f1044000480410441c00d040043d10018022100480040700640e07817104041d100181c40340c2c2c8115101d900032820300c030b04801110001900101100d0441c040c0740b03005009000901400c1c0d0200b40412800c00003a21244111408001860030610f0191610354a1000514441106034101035031500c1041c001c004041000200701445440e0902c1e0194038507098040d03c107194088400c15005000e5000d12001c0c040550360000d000d81032010903c4070002c421110105a41c2c00b012203103007070072491400c0c090300e0021420030380d000749001c2c0044220f20613040d80e24407411480c98000303002030a070300c46102603e0f4000703114040051070841229070f80d44648040303070308115000c2e503c04180010000420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 220176384 1250 220175134 220175147
    0xe0105010e0901140703050405030d05090f0c12030a0309060207080406111b0907210c11011b02031c0207050604150b03060405030301050424030503040e010603050f04060b030c13050601 81
    0x14601402130191030300c00c4101d8180440080e100105145e00c0d40c021a080040500540e00c0240e0002802c00caa4602180000c0d983c01c0f41e011a001c0c3ca0003003889448036410640d000c8980051008019450200550011801485403600a45880c0d500f800203800248c1c0040c018001008203544030b150464966a206040c4180f0340410002d0103001034424519440320a0740030313440700030740c00c000f0100410030104920398480425070480311b91400b1f01901941317420582da005000701c04c000810150304070b0000010041c00ba4541d060169100303100780d03c46056130291a61600e82c0410026040080c0c3e640c60074075141007a2000c03507801480d10302421020b52513200b0407a03841e0045000785040d00f0b06403101e546a10040c05014055902c03100c04609901c0c1c0d408425640301481183c908e034580d40c82c02c0c090340701d4005006800d100003940c800000c00364401e0050b1409590f2501ca8039861b5266507803817000405246106d290140161403400480c3d0f41c42d0f248125404814030b00c00300c3c43c4e10380040010306c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 220177634 1250 220176384 220176391
    0xc130e06010b13090504050c0307150f0804050c04020f070b0708010302040b06031e0601020703210f230724050a0c030606020307020f0406050d0305180a05010c0312020d0e0105010e 79
    0x140c00d050200d80c00a100030f025080c21200d64207030000c1c807074540e81840c500305034548181d181c00d4820306000241c1181024000d103031507592562001d518804416040752550345c2a03074003801c11b5000e00e160710150300d856801042c0000002d0552881c0040c25511400100012141080800c0340d1000400c1542410301541e100540200c48003403071440c02550000000c1034444e1000102d0030200002540c50340200020b82c003441d0455000d58010341030b002070514090400394400002124803044611090059404055003400c0070f2003072035405180b09194843c1d8020070b00c01e45400300000031400322201d0548102d01300182c4000046624600003410303c080c1c5014058500415103404010804150b0100a1f2105182e04071400c2d0301c19024500010082c01c404d801c0755038007103003c030001000c158000e8000e042c95240b0fa08250300390800f00c01000b45681c00ca1203580e0108020001d4a00024810300c10400d68440d80940181040c0c2401c9001c012614442014640d80c0c1d0b42d40d0040c03101480c180d4034143e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 220178884 1250 220177634 220177649
    0x80f030a09050d020306070c030e0d11131b05090d0b0708040c080304080c09062e0e010e06161a0702031c022503020106030b070c030e030f07170c130e0601 68
    0x4448155005c2541c8060080140040080e60001e210405101c0c5040000c05040104142a181468141201203110a000c1103110b219001a24030014a0a02a04030009004001b90011002660040e00c40f940201e00e8a0b902c051403a9a803400908603040c036901075811907480080030710302032401041d8215540c0090604c0e43c014801045507003c0011921001d40c82540d54990f1504c880000c42d00d8840c0340400c80c90f25044d0708400c4040741003400c0c2064000b01407030f40d400083c0c0005100540b03d4003485154240c1150042200000988440b250000510300c02e90701a49525044c2c2c0c210010b640055450000580002462032140c1208082041403058252800c61030004001c2a0290f80505d11030800503108459184000b4035000b0340c80040110b4000700140d0702440e14a000400d03290441030120042041c0e01300c2c400d018200050091690200d03680100b0101d420144603404004043d480c1c050030f4428000d4950094840000010108002c41130100e40485113010050034010160003425 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 220180134 1250 220178884 220178899
    0xc09031b0305060c09030102130806040c0e010e040b0411101809020315011b0507060e040609050601020a080309010e0f0d020c1903060b0117040b070e0301020a090915080f030a0905 79
    0x49040801c01581004828600540e05c04030580400d0190107083e00e00042040701c070b40000354840780490180e03c603d00ca464a214001d4503031400c4d1100003028010002c002680b400017500180c56540d0240d000390044842c840720f030000700c000440304484907590740e0004952921454104c20010503070405403460f40025400c52a0020a0300d03415004000518104039070340c108a01c940315103031004805550408240c405454994001034140b9040d451203a000758500179000869034502e1140f43c0c040c090581c083c3c4038420301901ca403451900003405644195503246140c00000c0710030000300a01400c24006040d4071100102d0180c01c06104004003401009091004070882c0207007080ca1003581d901150009642413407070012a5440b80b0342c40780d4121420100705002c24080e504c10158801c14143da100440d0804000c281800c5c0c0c0501080d44003c950240c006111150064200500c0d112070700c40d201a0955403085040d02c0e02c00e10850075078082e00005100e00c0302503070003620180500000c0c2c4021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 220181384 1250 220180134 220180139
    0x7090b060702031c0c05060a0204060f03090206090d171b07051c0f1502040803090a151407080910050d0c0c0c140109050a0906180608120c100c09031b 66
    0x1a440780741c0c1c0c455411300d1550450a41d5207950081025050b11307500042254030174640300c0b06c440000c2d0f00c14003410380840c00c035500c3d50840034402e0080840d8182d01274010fa042044520901200383c2d1004d4045130340c05c4111148002200a100207400c00001041d50304841e40c402d080d100381000d040c0d40219004084107168a5800344a0440c40040c10303921240d030b031030754009074102090007400c03030840010a10700003c0d0011711b03220008042c21009008980e21a20641c2d070740404501944c2d0070050320042001c68001c1040048501d001d810014005d8009a00c2c06032000c0011308110140311040010034000300300d03200300108030f210300600002c950400c0d41d002000794840404054035072041e0981020030070055102c0ea40304111401c01003602800c0002c5850300c541002000c1d22003170182d0564009144000c10603800c003402004100e824041c0501590841c0c2c6407218615801070040901a200c3c4e8800f411103909544111681226240d450340c45442c00d614007542514000702c4030100804001409 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 220182634 1250 220181384 220181389
    0xb0a03330b031306060b070209070e150a030b0307121e050c210f1c0206010302100f14030f040b0601050c0606190302090a02220803181f0207090b060702 67
    0x50001c1c0c03845010001e4580d0384080e407000f00040c0007040140000d081103400164484d070300f0098805903100705c440200d140d8507101c044800050064120f50b10440075500d08001c12542001042d00d42040e140c003084a040ca42c0110746003509903481642040c034044810400d200600f04c201a4002801c0f855001e111510b803650f680c1c2d0906002914420000e031002c0240600c141071000c40c0d851034090a0b50540c2a40c28001510b952800310500d0082040d13502c1c0002585c400f0842d14144c0394024503040640303141078400c88130a40e80711261030034480d508800224000d50000034501c29103111100c854a4580344ca1300042c104009020141400800c0c407083c40b000d0b1007c1101d0354424803c1c1c0f0194443d40c062620910000c0c62603002039000364250702407003410710141c0c004103190941d05074240080c500d201d0340482d00101c4c41c412007209810510603280c01200c0c04540041b0304800806001070a49981c5180d030040c046c030505200036070300c881d400700455285809a905003d00490300c0604200c03d5801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 220183884 1250 220182634 220182731
    0x1110c03090105091815030601090903080109050c04080601171006060e09040321150f05031f0207150b01021b10050702030a23070801051b070201090b0a03 68
    0x1c0d19070502c03001140c0c40c8502c1d124451600e0108000d5503004102d42880b03940c0c403160403040f044032402070141c3c10011500c1016070182c0003019505a4440c081030b03103407000e0704000f07100241429946184c10400040c02032010021310703029011645180e0b0918200050305803030b00080701000d00210781050400c00c2182c0d08007508844002080d82d40c8a59036846140848580c0e1005040b4400041044a503002d5181242e02242d040026000424607403512165030306c80e042c41a01c0390607855403001440744a0704442c5a46429200d04850016007440034950b9800d40c00c0129403407100d10780e80e0b181039000f41503904010900c40448258000351081d400400440c0043d200340040c5018020000b502c1d804540b010007100d19696040440c444c40455003001e41d59100040c0041100548500840428060b00601c125401001402e003070010001000101c582c0d280c00c0902d003a4103215600c0400941140000b0080c11040060340c2c0010b54055407020380041244a60071115401d46800e100005d000140c55 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 220185134 1250 220183884 220183897
    0x106090501270b0303180307120209070c0c05130504051626030d0905011407110a0308071b0606080f0a080d050415090f170a09031b0806150301110c03 66
    0x60b00c40702000c00c805202c0c80a040c1c058aa55014840007079a0844c803082c605940d51000e500b14191081c881d51103400c03000c07000401802a5103c04840c000c108500e000303c80fa107100303070300c6040e9010070355039030306d000030001c4084070300c40000c00e80c881c02007004204051040003107041d1102d00303000700317903041c82140c0742500d001c2800d120940003c1c405001032110b081041e2100024105001d004083d4a490f0440c044c0644c8100e0741c00b40001ca0000c01d54250048644018050142d03004020344019a18105e4041d04040e01c00000d0224004105001c1d480039040050b50710b000e81000300b40a807500035524601281c030528041705800c5400075900284801c0100c501001007200c0112b0144c8403414241a090043e100050403280f420704a541000512411045207a0156500e20400c9603c41d50b18000d42c42001082c0000864166007800003400122180c1e508018145190711201d86509113103284c80c2e4143e4509140446100480441d8038003400b502c148000d2106549050132525026181d0b24086e11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 220186384 1250 220185134 220185179
    0x10212160c12030612110a0501170a0f06090905060609060d03051c020f04080606012a150b040c1e02010606020601120317040b0402010914060f0706060f080f0106090501 74
    0x2c0380074500c0c4900c41e41000c0c000d003032038040750603044606282a0100c1c504261489000d001d080d040000d00d5070164503051036030114184210b070580e41d842d00c4000100700c6445001401c6544000204a11500b0b100d80c02c0114030404c0108581c5c2410410008951402000c0341e1252902c0c40c480030019611400348c82c00c412031508030402c00f51140f820b580289c0140c2a4258a00402003000184c000f000607911b0700a0f81d003a200d075042c5080c50844151120b00040860301d00260580c20300000406c5120301c00f0000850101c001210801140041c084c0c0301c0440180c40004c00d40000444800c4c9101120400d185181c0000c004081c036002d0003a40303a03241407142101003130420300c102c4141800742114500385c0340c0d4460369070b200e45041e1804009050301980c00360700041e04450085513101c00c1c2580c81c42044002081d02e802e002e441c40d010184e55100781c4003100c0300b42e12624002070503038117115142c0150400501a10105400070016070071104030740c0c4100c0c405428030004101e98500410760b10030720b00c2d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 220187634 1250 220186384 220186403
    0x50903090405090a1704090b0d1a06151c06080102090315070504080a03090e0a140109110708030103060e060a09020a1203030e070902040501090b030c0301060503060d060e010212160c 80
    0x1e141d00d2074109028580054449105d0684074140d19860600910590b0302503401004a8142d207000e004101c0050fa81c010120381480034060f000391007141c0361036407001c03004040f01004400485481c0d140c0d002041da008007600113483e1902c44940c140a404064030481000b142403001280000341d4920445000e10400582940801c40c0c19208134201c4010b0140310f000c441e001030913858000e1041c4194800d40111a25980100e609050f41d409040350402c400c07032410320141d090241c900c0c001d011a018843e070a4404200c0800018000c0303010314029401548006500495810040d052001c02041842e881c0c0c6014080c0d80142e9a10307110005451500c90520803a5101d840d055008050450318007410384582d500000c1c00307a2464000380300b90f03a802c4ea20300c05c010750f07a460144030303d020686507205414000e0006001d010310030800746a0111000f4140c00040d0f031240c82e04003c03940701243e040c0203650000f4660000358011102181c01084034450303001d0760040f84800a103d058100002804d0544 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 220188884 1250 220187634 220187641
    0xb1e121b04021608030c0406080603061b2a061b07170306040b06030f01060f020a030509041505060301090204060905090402010f0c0501020d110309010f0b0603041b26060a050903090405 81
    0x800c00100040180d022440350750341e0500e45182c03101b940052007038030b000501c942c0010340e150602050403405103500c400044822403650b17103840007542280600f10240e60058413081c901041da01440b11820007103202a00c46420140300c0348d0410268190240c0140d0030411a14000480700350902e00d5015000a43c29181c0e00c032140010081c004252052754012300100a000c0d4040741a65424126285034403254140d141000c000d9803142e20703c4c0b001a0103e802807100352220304058100701d021308240c60320b003100c03142c07140002541c5400c20781050802541c040390038040070b90822a9003025140450314a07003a4034065000030010362a0041102c00c1290500c042e504200c02501a15500ca801080c1400b03002140c2000050541007240d14010a41c20611240c43d0780d0707a24850b1404010001c2c091b20f245a0710b68941c03806c1c100c0940c00618205d44000c030002a0320500c100030001d0028a0081f5110000b4054812032600c80c028185d41c104600e00b80501c6683d6500004903059550140d5001c02c260b0f5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 220190134 1250 220188884 220188907
    0xe03040b090d0b0405010b0f010311090d150603051c0212030c1602150a14070506060d051006090207110a060801050120100203070216050a05130b1e121b0402 69
    0x292400700c0201003400f0302060104100c01074001c50601c080550341841c1d078040c11001102607446016680883c0682004400d059040003540c0240490203090480404d40925490808584080c1e02c2541c50ba0003086071b03d12030b4203d8842c0d142e18144144000c01079018002ca23604440d201c0940511340c5020005402a00d07020b140580e00c0406400412000c1c19405c0c200b1111400c2d4445d0801381c0c0080c80c4011040303980344c01d140680c0c20003030304a0020100780d5034460620840f0380d65140240d41500c03400000c5141e0200d2800340307001810001c44056114117003031900000308c035030210005114080072a014081150301c481040d0448800b440c0541082c3d940204c205014102c620f051354407800307081440c0c0015100d5400840c001c8a0304c0d402c4842d41c6844030100040030595025403603218014000030045494202c42400d81c140c0c0c9803500081d244004000201b40e441d43c412106030351102070240c0c1501c2e28121032010a06a400c0300502400b00d00c80030605940d50f1641c0451348600c0c1c0c041100840c14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 220191384 1250 220190134 220190149
    0xb010b091207031202120301080601090b06070c23012313031b030201090b0703050403061521020909151f030c030303020309010c090b091003150e18010e03040b09 71
    0xa40070142c5007101d0300da060500300e4900004508002d44a18903412040005180c1204e0489442c03102811050342806490f002030204000312550081003070280340c0c0407600301c102c101d0007081c2300300c070000c02c00d40900a2859040308038940141030010345114040c400079103a48040250001e001c000c0c0d5122480c2d2110683c443c05d540014104a5017890811000890100e4140a5030b000f41c030780e090b08940c1c030810030050348152200100060002e1108000142c1c043d007105100d4400c61403c54038290302c440003112450301c12000f240c031408407002070500303604040410740e402c0402107010302299500394024494590002d4500750303000c07403c1484062098400390501c000707103074007450388a881e590f00d06004020b5042900d031460154030385444110200d000b43c0c3c1c100119611404c0060610302c016042042283c00d2800311401d02d9116107444a0409400c00313980302402018046000500342106c00c1c0c00c0300329603100b0300d50580e07140c41d06660751144004291411148a8401140e50300e9030600410300a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 220192634 1250 220191384 220191409
    0x40b181e01050112080a030506010c020409060f11130e0a0213060206011a0a0903031101090b0c0a0207090b01051b1203070f030516120209011704030f09080304030b010b09 75
    0x140103500003001001001004400d00e80c1156009009590300d40040d4103104250340001840b403c0208003040c80c15020703410850344034005041001d14404180c0210301621312038001183c406070b0b0386103514807421451181156640a101003d82445000c61380f5550403003950207403072855481c000003da00d400341c80d0100c0d4103400d43c010551600640d503c90195683e07400307001c0d030301113500d02c6544c52181394154400d0754500911582c61002e40c0346151016214414003105011003035490304012030100303c4c0300d4010750242a118401036569125000001e05003001604100b9030107081c1000c013825680e1002c10341d1482200c07000210b80300d000c5101c070381345020840703004c1410200000c001c010415400c101d0300c102862903620144140c0d44c0e508400740c0d031003402c0070211010401c0003100070030074007075035010f071582c0507040c104002c840c550f050303010002d801c04481c01c4001031211200c24004a51245d14a40206016001941441d0865560165500c0140240344406a02045c0e201d1159541c08543c2507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 220193884 1250 220192634 220192681
    0x609011a0f040806090708011a0609120109110a0e060306060424030503090109080d091701150b041706130209100b0c060403030c0c050307060b010203091801060e0103050f040b 77
    0xe81e20303a5800659151340d01240c484a11780194071b0300254054040c001d5406006403a4100d240080f018010011150414400c00350441c50b00341354855144024842d801809000b51400d4445200c24001c001052010f504414140c2d006182400310f01c0e100014200d4002038101d5010901205801e402004222181c401010380e8040c0c44000080c05800301c01040000d0082e130303130040f6440c0c9440c925640c800c032241d00380c000144105400c01c00d02c896410421542c944a1002042840c8807011003a402c104540104c40e00c914005001c214600980024428458140010340000c1c5800a82c2030104200c40c0701c064040c0300b040002549011207407001501401d1030004494507081c4c807032181591600200d03812000700b403518030795003680d500891010040369403000041d49024001d0365800040c20b00b015260381540b00900c2105a240c0d180d4121448001c00d80b01c04803010740c0341c0300008162068800308241494640400c6c0142c400008507003a500c10781000703104020340c440c80b80c1c02c1c6d4800b204203181607 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 220195134 1250 220193884 220193887
    0x21b040b060a030f05151804051c080121031d240705060609060a060c15020403050d02060c0a0e040b01090902030a0c02071e0608090102072004050a050609011a0f 71
    0xc0b52540642c8401003000e4620000c00180c0e0f2040210022101e11654140d03101c1040c03004980d89036813902a296000d80300d58240c68000e81450f1000c11a250702c65600004202482c0c018440100071200c02601138004100c0d0321a88040d07510080c210b010340c01c4d16004a03145500034000284c80d0403403800e540c00700c4a80c241c1c544081080c45000d89810484040303030307a405030300c021852078640542c115005040c02000100424a0480107a80d0f018200f4012103401c402c80b40055445001880500000d5008030003030032501c0b8224400908110f80180965032140d02070000000096001d104e1518030358003a90000380346010308005841c2506e05d903003c01e18107070000040144c55002d582004440c0f484640880d8092600c8401d04410112083c40440548031031640400c210b0388110a02c0d0f800000c07075800186400d40c25210308100d000b040c115420344c04110900c44043c1d04062044560102401000300540d0400000041d00c1d501c8c1072088200040c20104041c01021f500300888444142c4000f055 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 220196384 1250 220195134 220195147
    0xa0809061318060e090115061101061d090f0325061b0905030106080303010e0a020a0c0b07030c0905040b0d02040b01030f1a030c100e2101090606050f10021b040b06 72
    0x80050412401000554030004012402e6a501402002c10310100d8041e500c1000707041000440e441c45145500c90700a648964000840c1c0c0c070b406803000340c6821200b003000f03307071301d05640708a00d4142120f11440ca80e5008200300540c5940b40364040c50340b0401c600c200ca007500c01908004011300011007512401d0403030014030000164103c40314004644041e0000d00440b40c0d14140c880c3c49010900c1454803040240002a10192141c2d00030302c00c0d18a5428908400c0001c0e8884810a400403200500840c0c1d50f0fa19856607142c000410b40011f00003242c0c18402c030410000891800c5281c00002801291184485505030b802030300f14280b4269880b0041200c046104041c84842070450744441c002c0c0142c1e000d0010760708103c8006c22003010107440e0209900d400c0418400074806402c441c07030500c034400303520940b40442802581400c034043c02002c5230342800d100408c0850280e012030b2920510a1810f41c07508a40c02003040d0f81c2400d592103003030fa0900a0080442d000d04030340d0791007d610500000c2c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 220197634 1250 220196384 220196429
    0xe0c040801050910270215130b03060108010e011d0403090513020d050603010204032103020405090f04030905010e180a0603020616030305061516050a0206031003020f030a08090613 79
    0x121a500c0e0703000d6805e01c00c0140c4000001600100c0c59100c4117440040c00822000d810000e07000304180c040509900d24080459407400b11403c41504848000764000043c04515030780f208442d40074250300034640181c4e52400000d45020400041505c030309041c2c2c030001505150007240404028503000c0c10b600d15008801d0002d00096220850000d01c1600c0c0001241c41403e05109480c25294844014652041c0070102c1a03240d02c92500882e0030182c0800c00801d0075120a418070340100745009104990707040c5850054800041604198100030384500003850a44e00d03080241403503902030070100e00701e8403984450000380429400281d04034800040b001580c1005003d041c0c1594002c6d0340400494075640304000f40a030440781c40103c507180c1480840740f071542c00842c1c04e81e4940718000f220341d16207069012502c5030b0800c5070356070450980c040003001542403111950500050840c050b000c2c504055540341d0050051101d80c03800381c0b00214940544000c80300c07030304010749000500b140175010340b90791 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 220198884 1250 220197634 220197643
    0x7150c020a210b1e0402061b07030605061c0206090d0303061e03050d1d010e031905030415020f060106141e1305010f0c0204050703090b0a09140708070e0c0408010509 73
    0x10071540c44288070f0018813244000e03810b42041c984620301c28001904e0399002c11a407a0400c0105402d0564115400d03050100100030b0704000718818000402c66243c82000c1280e5159502144803284504240c5600140e403001c0466642001c11100daa10888407400c0032002040036030031012503240c4803045501050030b02c1c0104421030f8400c0d41200c031201070004040303958090758002400c1010400c0c844162960090000c10a10f010141c120303400c001281d8401030700360a2641c0142c41c15000064140040c04070070760b04540051190000301400c001d0b64141e195196014450720040002d13003070f505410039104404a0303a120b40c0040f203900c88506150000c001d41c1e88a8103414030050004070340082c0550241082c404407440c00d41b68503144100c150248800341c81c000b050007041503602d4040d00001800041054020369609100050304569841c1807003103071300540ba004000e98080c00d0100609032001660340180c4104240d01d82060312081e07403040c0c0c580543e0300000300079400c020800000140015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 220200134 1250 220198884 220198949
    0x3130609050a0618030207180f1e0b060a05040306051512030306010305010e04020603070e03070b0a050705070e010b070f06020702060c0c10050a14090a080601030b1807150c020a 78
    0x1282040a82c000d00d80f10380d1030720354100e002400740e0031040042044008c40c1005407401c54110a001c6944c00035410100308403800b04c00c41c0829411aa0740e80520219035104480c203441042e02c20794508500c084024203140954400200040c1e20707180000c1011020302d0100d1b0300329002400412a8280303180701075850350400ca43c89030000c0e02d020000036054014010361030007070303070050314031440c0d074452941c1180c00b4050002d0458241c801e09000140d58003040f0000c1c4580c001d00c2c0c0e103081d1070b009646407440c00d14445601054081d8031881c010b00440c21b440701180c41c403580c070a01b81004200c880c40c201e0040d000c1c0510184d8041d40100304c2040020b00454410b10516086404407001404c49030241e6050145402113800246158000c00d50301001000510b20800000c0c641c01e00150f0b59018249408401d0700100c64058685c01400640022045100a52001500034185480c02c10090200e40c10400c500030040100082030b4000b907451702d20b0f4a001500350a18103407a60f18004240c02144003850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 220201384 1250 220200134 220200143
    0x320402121e130f1e050f0f01140105060909040c030c0b0415022a0d02090106050c0d030c0e0907030902030708010b100203130b130801020c0a0210020a0f0803130609050a 74
    0x50005445400d52100c2e0600e034030361010780d8040c05000354884d0f9011544014a850400f02200b5400022501c1001a189181c0707182c2c004040301c0080c0032000b400c3d6045105581d0403803d03178400521150f954542503d0301c890003950040e844d035440d4280701008a01960020741070034940300012540a41690045c401c0d40e0001641074221001008100e036644501c06600600410040582e0a114901a56101c040d14000c1c041c82a0710120b0300020451003007a4800000300f0750003d8003403000b4100340803151051200303084c100b08a0100100c09030082c2c1c039201e10349103c1d5140b0000203003198002d0744200c2403d5009030484034040d03101da0a440c000c0c8400004070f4030881c0300b4190500824400800c0701c08050021b490340c01524a41150804140c0201c502e42e000307030001c001c011424080901c003509440023281e00074410f00740e2a005202c144080c000100f03085401c100e0121010404685201d241a0762164100e0f41d69030350901c080b5038210201500808007810f210344141485400110701030510b004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 220202634 1250 220201384 220201441
    0x51f09020a060806130c170a0506030f0d0801030809130e010b03060a06050a090207030201090f061e020403030503072a03030b09090303010509040f08070b091632040212 74
    0x7210401e588030700d070441d84158800954421740c4040c00d130903040350a1804036030a10b8685081c442d01d001c00092001c40300120354a0740c0b1403c100c05840c0812280c6c003c082c0180182850446061b0b00a0120505000280491000051811254031501d0b00700c00c2e4003415410410038000e400c1c0a65020f000700d8124240309115000214035040c01c9441103a04031100104162451460418550040e400c1070b030307003035040d035581340c0d04900815a162854640e451041800040340c4444880244404064411407220340e031041c003081c00080c2c3c01004483d084502420700040c81c0d040c4003e1400c1d580001d40e08a80c0f60001402100304141d0140c10010300220304842c01401a078925135410f5690009106055000741181c0204000c00c0c2c0074090080810300440007079261004580300c4909028059850ac45560b2203e102c0200c02c11075540c034840601200d59182c01c8034500001c003404401e0315020300d1121a00d1040700c0a60710ba40d56411548001031003082400c4030310b82103c1d69010324450b0700c0204d140414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 220203884 1250 220202634 220202639
    0xf04050c21010c050903100e0a02090c04030b22020418050d020f0105010504020f041e0306021b0f06250c051b0a09050705030411030c0a080606121203070c051f09020a 73
    0x4005803100281701038000c041c128150001c64016110428034120076005609a44025859959881b480345112140c0d06955500d18036120051000090003041003240d144401c08403101c00c50140201240c0444010815489841c031008071003500c01d500030024490506000c610507000f00f00140c11400c2c1e0402007100d6a03840c428030050f07104100c89400b190804000074801c207013580e24521400e8946850159140303403a40d40307002c02c0380e0003440c050360005191540615241e0081084202a00700e8202410850500c0005002006c200240c8005a0940000040c0d00380b4465081181e000b6005001c07104000d003540c0031211050024030a1034041c0c190b64401050400072401070740d0080d02160303552451075803551a42c1c02c250301c1840700c95606001c0c803000038409945541c041009802204040c020904240d000c00c048024208640445500002c0f1407d8581018806582d80544581030441c004c45440ca080d6003001982901424054410020700e480828113900248245100b0744641014030f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 220205134 1250 220203884 220203887
    0x504080913270203060c03071103270d0218220c050312041406070201092c13020f1903051f05100b160c0803040b030a0c050306090f04050c21010c 64
    0x80c49002c0c042e41650100300490003d1a0042c004d5034420702c2881c1010010807050b100030b056a00244943d0840f00c4190211581d54562038400240c8100c01c82e484041d4100c0c07940450744640828500d040d000c007003000003580e4000805003540742c1010080301c414404a01d46420388021006024441c002d200e20440c1000c0e81d0b03a550112030aa40c100e8041101006d907007001c0181560000c80220704100b903080000550084103416100c07a40301e007121003001e40c0310f040084803000b24018068580115110500313000340e250210b000749905000e403030360000310710040d000f1400d481155000924520807a0308800f40e41c084088902944c81078041c0500680c2c80740f142444500090b40581306200310300b003150180740c00980040e0b80c0010310560004c00e4aa640c0c000883c2542c010b80d010300b80c0c0070f40000c00c104050450748601d24500503513041190031820a00301140c65030074020b021006015250340400e0a200d010444000e481600070a201240741e2078081591114001c0740340b4481c5982445000b12446 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 220206384 1250 220205134 220205201
    0x1051e090a060902030c09040b07020d050a230909010e040302010c02060f0c0a0c0b070504030c08030a200c030a110108060a08030a0f120c0c0b090a080d0504080913 72
    0xa4030803500410000c003081e00d422004080e140300c1203a240c85419020748050300c42c00109131095024064a407078510700780c10043d051032042c40003a0200241048114410303500405101e03018400603060f44800382283e02804c030148111100940d21070442000040d001e04071580d03180c401d40c0320707500902c00d164902c041603941d200c00350340116108451f440020703c246001000750905070946d281404480c3d510b51517090300d0950507a800c42c00107400240900a102480c05048014580c00b4015407800183d808003c0140200a441d501c00025040003003d210b542001031a92000004056071491000342c60032000322101071410328007050820000901c280b80c507803045001c0b5000c0801461610b4080b01d01150b4800400420500384082c4140380c044d10309007886440c0d9000c5c500c0d110200d142f402803d100c0350001c8020078490351603114036500400541c56005480e00724115403c003054980b86e507c2d00c0855402688070540e0407002e40c04448000040e2a00300c961400131a684036040d108643d01c0d4941c03007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 220207634 1250 220206384 220206391
    0x18010210051608041505070e011103030c09090c0c01020c01020909011202031b030127031103040807060e060d02030f040c0f03020312070221030d0f020c0d030902041d01051e 76
    0x7540440001c2c00c0703000d09a401d034018810304501e001008030346003440480d00f003500c0400002c0c1414075202400d5801803901e54808025800441c01e519000460030003510a80f034000d40a2022480419480c3c0c45c1d1005a07000760300c83c40000e40d02c0361a0742213240d00070b4029105203417090002034000117400103401021040941c019024003068250340c070280c60b86400c100510344e00366590344030000030070f00680150000e584222040c4844c0c40c0071403c2c000d06001c40c070b413200100e41d0410002007100b80d03000a00c1c802201c200b81400d4a014a00c2030018040d8010708035201220ba00000411016014403251148513520071103540c58290340319990940c5400413070100a405510941045000d48001000b170a10300b40300914a6003040b5a000044191313041c0041031281540c004200d10341341380a01d018000014001510460a08413958101541d401c021020641450703520303680e42e0155100c070341100d00040c650b1810b81c040c8041c1c5c500e0060080c1030859803800207a006c0181841451019222a0300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 220208884 1250 220207634 220207651
    0xa0f331b030b010806090615070f051e071a040f12020a06030506010c110a0308070b0a050a1a2103210906010e0c0c0c030109030f020d02060c0f0d0e031801021005 71
    0x82940d4a601b4481110005000c55074844000d0b038501000c000446d0040c0f03003241c450090484410f12515009150404950400c2c0e043c945c190380035a1410400106501215202500e001b5404105191440d9a101c0c6401000c1140602d0b400455207044005902e000c0d148269101496999219021803c86800380c03041800646140a174501040080320f0240d0603d40007000b08860990741d54544c4010b6202c4407003122028559010414a44001c0c0b1072983d002006038000d22810755074101e01d00884028103019403180f1440411000310402c941d011a11b8024440100d03a6909904940140005a200c800d20719060491000034568030b8040ba61504848260820680d96250319800002581001c48411023904c65400c0e4400c3c070343e40c24001c0186040c000d0b01c49807008817000380b0003800c04004a0030b41c4259132000b01442a42d00940040b034100002010b6441c1d11103d110908801034424988628071a2201140f05051140d035880d400c85114001d03002c54041e01104c03960041558400c880049 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 220210134 1250 220208884 220208897
    0x30906180916020d0906081303020c0a081f020a05090402030702010e0105011e090b03030d021b06010f051f170601110303090304090509120f030408040b0c010b0f030a0f331b030b01 79
    0x7616085050423000100340b20380103031110b0b486000040380d4400c603070741d02c46603403640620480715420301150000d100100c0344482c04d51411180d41c0b40a4a039202c0c20000318000c0d50f0020000d1141c520179800a091a44818028000e42d40c2d518001c0303001d0024900e40d448029a0707a00001001052803003040d40601029015508110781c42203100000d400c00d82600c10904030441d035005034050140710300c80c060721084c2880d81c000f82c100070a00c094a00d00003c50700c4240c08030401c4488540e080441d1b040d4500c01030b803801c283e603078405004a5208640400d40700043c032000c404e010600a0100c003404c10703615266810001035680c16421940c4141e0808000d4080c00200002c031400300100d8002c5601a008101c107500c0c1a503254203811142d407000c0006001c0d41d40d0341217898018035003003c0c0d80e4050780048005140340c0d809a103440703086024020000748a0401d20b40b041132102440602402030034a212542d080841002c100c8502415000760410700017502c0c031440415941c064442e541d0b645c401030b510710 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 220211384 1250 220210134 220210141
    0x605010e0f0105040810060612020c06060d060605031f0f0908030a09031b050102090f0901050109050d0203010f0516090e13060b01030615050702030717030906180916020d090608 78
    0x203104001070114078100201000041103544003040115100b1408040c0056410318140c401401b401021940c400002d004005103c0c06c3c042c0018825004039080791400340200480c070300200241040c2d80265010700458809060b8400d202e418156200204102030101121007041d180841e03500d400000c0070014240b001c12040c6459900114007184281003807604000f04c1c4c01d50031118400107034100e90f136a40001d10140c46080c0a02103880b40102503603011025410980068580005030107051300481111100c1401e65400350842d0004411100c0200320034100402000c40018429000e01c020a060700c4000425110450245101c0c01228042c100d030034245540d907c2c090030781800480d042607100c12001c503a11a510015800d80301860f10b0301c5596a26910505003090b1343d0350f10150701103607400b141c0180d403800070044510a007005c8904075641e6448031610705100100c40480c0e500702e14030f031007001071001c54900703050111421902180c21040401b40f00b1241d1360500c4c001c9400154050011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 220212634 1250 220211384 220211389
    0x507020f04090c03080a1205040807060f0b011d0406150c0b150603060402031305060f150d080403110d0c03061a0603090a1b05061206011b050a0f030314090a02010f02010605010e 78
    0x640081d0091f440c0c07a01284484119081c280e40c0107a034161004100040c04600b0841503204046140c18942028404a06440000b0701900c0e90b919410507070703004038403060f103ca0b5141e1341314101620041490184403215107500a01c540030320752003100c401c4100400320741c2140318502089030741d920040c8010300d0b5907110700910020707401c081c021210808003844290001181030200c284544001c00340e4001902e000021820036415081e252402800c00000180201e007a01d8100c6081d2504094405e442d07030207800c0411480402580d010700010002c0c2c00100030000d8941091141b03221850340e191a694a00041184078813041c0c0300d030743d6a503000301c00103030015404504000ea403000c034140a4000e03a40c2d58012030402da00040d64a81c1030030805040100a607046080c0c05036161281c0900618502c26945090355484000405000030f50800903210406104e5040002c0980884c3e2410196080c11b0319410380c1c5004500003240482d401c0d44c2d41c40d01c558130521a4004840c0165124580030442005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 220213884 1250 220212634 220212637
    0x1215180c0301051c120e0a05010f02030301030818100f1205070c110301020d150306061205123f0c090f0d21090f050307180f0b0406060507020f04090c0308 68
    0x1404c0c0258480801c01000c940c066101c10700d48001526403000e0100d0403c10041b02c040d294010301c2c144680242c50751401a40042603d0569601c4001c0d16a1500790700d024400709444880403983c0f0551f01c902228030070b070f480403030a50020580e0f10750300300000c0c6068095080c0d810840e91180018180c4045902251403140d51140f0010701400051410040c4900c81c002e44200c2c1d5480c0b0110655810b08008003c520310501b0001e00580c8299100c61381180e449a0701e600412aa120040384003244200a029440f41030846410354601d01c941d01110780785003144032840c04296003081c2450f1400240c8480c040004171444548000d0107103230304aa095082154850005001342c809110300261034840801cac0500c811001d800d15140e84440c2490000308803030110180d00118040d030800031040044c10321a008030606160842d5011800e401041c00c28002801c5811041d94800d0600c440050b440e500720005214141c02a180c1d01c2d000200407043c0426602403a60007080004e91100410101b5000310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 220215134 1250 220213884 220213909
    0x15081006240c021e090108060103052a060406080108010b030a02060d0f2c0607050f0304060b0f0a0b090a0b0c0601120f14010203010603050601030b010e0f061215180c030105 76
    0x601c1c2d4841e5580c1d401043c11404540103405a074a01c0c064401c825182c0040c040e801031144100070003056041d5a00c0645414070152210306084810000c0c004010804006840d0000d0103090240c03202c1e603545004104100a100d040004e5182c0300304035441d81400b0408055998004c1d20140c58490180035400050050283d0341038182e85c1d9401d984482001c00e590311200c2d9625242c00141c5049007440d46081690103060f03142846410001d16040300303840419254880d0700414009240c55810340882c013a04c0094407210791001d02d45001003401c2100401070001c0810603512240307499114804103c8500ca41445258294800801004142420340108498610680018400009680d242c081a10b22808070001da07940100040c07003902d501d4411240d010409203000e02100c124940042c2070000c00d0b4031003e0148811240180c0c86446800c00c40f052030031180701c0210545001d80c021b4942c0c9080c20340c900d200701d00300b0074010b10b803d814280c19805800c0c1d15001c9441d50740f030041041508180c2c0c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 220216384 1250 220215134 220215137
    0xd0e1002012703020c1915050c01052e06050301030602160c090b1912060b120f06150a081903230d06050405010605070803100503011508100624 63
    0x1c065040c2402032400718000051040350030352201d00160310f0040d040845020b0074a005444000c0d81c0d0804420342818a0301301c40d49165800206598280b0071603080c450403140403059800c00e828042c000e9080340e0146546005d10090038036441c40368116404042140c440e182c0064410300052001c520b49034000d1895801d805402180d603502c0d5501c14001c018103500c41d4075030503076422060016080120b10f45140404601d074411042d0b050140503042205810310142440d680e9200481090721102d150712404c035100c2084543d031000c0c001d14155145811905a14008480c008070307126801c09014400642d40190050940c000118516220788417080320168100306889212041c90307002031900c5000c075800101981d80d602800250b09068940e10342c05030b03010341c0c9000010450710754804e0580c0c0550368802c40b083c1e602d4441c811802c0040c1401e81104e40e00d03529182410f1107400c040d240f124204d44418054031468550080304108a4079903100340901c0e1410285122064142040750840c0c42080307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 220217634 1250 220216384 220216391
    0x30806030703050a050307050d02011116050a060e0706030609050921040b041706070c0b06010e0a080d0c120206070c02010807031b020609070e0411150706090605040b01080d0e100201 80
    0x200c1e21828501204e480c010395558000044030001d0001c28004800700400c140001d00120900d0824034145204440440c05601c0b14824043e08200d02031100d050f800d90045400e0040606101620f519178207248140401b1030701d070446c0015110401c0c016513228580d000003400a0004421100003241c4182d158017a0180b010000414021484d6002d413000d003145004174800c110007001418a0501c010b081c401c10321101a0070702001800410519a101e0821301c0c2c201e40c1d444614020840100107500a03845901070310703404007407075079205a11031034803400340a40306d4030343c400242e0070787c1c580d8000e544403400681c1c024460b00140d4012804103410120300d00d000a43c0f80300007103c0380501c2d2140003034800182c2250082c84a00f103c1000a1006006000d8401c0c03824180769441e8038801c401d21180e1801024188003040050f9040d80540380900d40081c02440a000c680c60081c0040004a03401c070b0302914070100102d800c800002d50000e401c2083d8448100100f190030402c40c880d4455000700c4c2c219901e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 220218884 1250 220217634 220217639
    0x240b0a1505070f06061a1219150311030106171203070c05030c07060f050c15040501090503040b04210b1906050a030b0a051e07030f110a05030414010605010c0308060307 74
    0x180707148204900313000f00320015450703042115802034001210010f1401802c240110203040c82d521010540000c460080000081c05103040d0f4030107058078103612000000b4541001040c04000a01e0050b000000c0f0300802941c0e03110050f601303a081d400302400000f944200c000d0a1442c00e9070f030045800510500740310442c20f0060b61030a02d15400b21328140c00f40e0b04644020400e1a030840300409400c1c034181013250402c01d805042c5999003040c030184c000a00c24070004a000d11078203600048000b40c004050765038403500d400030400f03a03078000d00c54107017801c06a820820346034240ca001000c56039481108040d40c3c4c0c80394017007000700c001a4402c0300b9030542e0380c02d070000c0e0b50f0f40c82c401e0305001103114200940719850200c003440204e030700042c01002d07440b200c04001a1042c01000c0d550703501210380d04001800c41000c0f0010001403107400f40009c5d00600020300c02e07980c43d4001003e10703c6544164003001c00e14216180d4a4262400c62103450b0104403500c8110000034081c41c102c41e48110040c00715903140742d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 220220134 1250 220218884 220218893
    0x6021602060d02070507081f151d090f01020a050a0c0c05031b180601020c090c0409181101090b042105120a0807020a1211010f09240b0a150507 63
    0x18400060307960b0340790f03001a41e201084000d0007100c0081c4680360191841400303ea61010703007101c2d010b0582c41603c1d079030382000341c1c0600e2040d1040b010b8900d000510030380c61b100200281505205480d48c80300b42c481d112800c101000305000301c5001030b54564485042190013101a100b09201050840314124404004180c6d610100048004408103514121420107450240304481e480c2c40b11a0910503412010005d00e03076000201e13844812801c1e1451400c550341c02c0010541402143c00440005081030010303141460320707107034080d102c6010703030700401074451550b00641c2e090316140300701d240070b040c188001c010811502c41444040103510300c02c9403041d5201c0c2e5416040466105580b0b14034040400ca010351250f21a00300c50b8407204500007000d07000d07030300e880d86400380441da04020200501940405c003000800e4101202520b0300c41342c14420340d10980b038006040684200035180715880c48011034035007125402001c0650074050519030f101424400710b1841d520b0341d86d001c6003e00604000440004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 220221384 1250 220220134 220220137
    0x3120b030d0906033603020f030304030903150203090c010806060418060f0f1d0406060e0403081605121501020106030b25050901050912010b10020a1109070207030602160206 76
    0x1c9903101c280d0582402006011283e01c3d000b0002c0614010710000001031086011003400013480b070781e203a005562885d04078545107001400da8010300020080c0410035070000030340c4c0705880c400e1001c1228900c0d1404a54100e0004903012401030380030f000d04164035401081000e8000c2005000700c1c0c80c00d501c81480010000300d50780f00d44040ca0356120b0400071446000700b840040c149a0704803080c128504070341d040004c0d54900344651491054030210381040610380c4400700400788031201c00a00d1070181005010014211400c0f0354200e14070240d5041107202d0011181e601040300382650380c5842d2074080c600504022906030303041d5940c0e624080003141c8050714441c8682c2c03190003515000d2045200c1d40362000f40801a84050000500104030b29a0300182a00d100420039602c81e080000d80d400400d001d880c0c042d0883e6008500100044036099010604006443c01280e00c0c13001d065100302804100c150072160b11006812444080c0000350168005141d0340801c1040303007042e04140e40019406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 220222634 1250 220221384 220221403
    0x10215190e030405040c1716050d0213030611030f09010b011b050f0105190609021e03040218010801020703020c1e0d0309090c0906110c01081902040b03040515011202010c03120b03 79
    0x201d02c00390100d01c0d4680c01000321503802340005130f418075940800322000c0e002e402001180300b166a00070543c1e00303c1d08071202402005541000d01842542903070010340805078803d0302c02d151352801c1350001403500031050080c0400820180d407000314584412030368518804d001039040701c2e02d008801c400b0602c5002400742e14040e03c000030410010403a100000c1c1b08a810030762100f10f01c640140008580d600705c1121604403562081d404550740e60340e070b100088643c500b90300c030428845000c50012a40d844d055010b0400c8500c81e03000c444d0091a41d030100185070b604450f44120a982c0c3c07200c40b06260908403a00c080203480703420304c81c10054445500c0c0e020f5446070303004800003c060060421071386901459648110706074002500740c544800300004c118140040c45124422000700c0c44044508055040302d00403c051880e0f952a802d2a10f0856202c010300c92880702440030320030011a4400340401100380c4035505840d510070890b480c1d42c0a0301c40e481c000f1420380710a61b50785001429500c0600c0007c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 220223884 1250 220222634 220222637
    0x10020c010e030c0105091501060206070e0f03010906051506040509150d050106030f03450503070e010504110c0d030506040902180f01153204090b010215190e030405040c 74
    0x4180c98070040992030b0a2071921590312031071f03481300100007258004c10655000322040c07408a05a0a50074046903c84081c003008076015840c0a08450a010700c50344400d02234a200304c2a07034461000502041124041c9005142e400040000418440e1071407650940c030f030101c050001c09039041107403981400c4980030362040d144192951550720030181c1c00001742100f04540c0c2000300ca10034001e80100c00200305120001d41c1e88c5000208803070044e40090070310009081c000c003201d5800761224141e4107000300030f00c91107004504121407000c0c42d040c90400d664140c18640014004c030040c401085015040182c00305801039070f43c921140150301c60032240e0704140401d0811240c6824140d542c42004032059100c1229071008a400030640c540c8504140c0700745403010703101d24403641ea84a01c51001210360507580800d4000080010b004519608280a400c800340c00787e410075214400c01540b40178084400320307035000c8c02d88180c03c0c0c40c02e0594400305030072440c642100d040c140c0300c0000c10100d8000450050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 220225134 1250 220223884 220223891
    0x3050d021b03070f120302191101020d0c0201021b0d020a062c030a0f03050108120c03040504020408071503150306020c0a0b132108011a0702060a05040806150310020c010e030c01 78
    0x84c24405521085410480030345404c44c50703c0710b0300382000c040c1d2a815041e10100800c100070055102c1d025010740d00c8884044104218050b032a00d4040e00030760010307058203d941ca1108184809440124070140d07a082d10f40c003d0100c28001d40e4501004050040c140c20304448054080c05003c60f00101280c4031519110056942e003030510409401040c000800300201410040144107000002c10060201c02880c030426840b0000021420300318060f54000350381041c40400c0c0081c030001c0c0011b0710021900480340081000055030011010313182080700b2280d01c0c0c4087e0300208001401d60f030043c10044402400d59540b0846a5250380c0143ca00380d8220f0503900307015480100348540d000900706807265244280c8464601d030341c400342c1000c405129a03001030311030310350a810241d038134802c441d00b655000f009290384283c2040050000c0d000b0b8000c850309442034200280404512840c0d40f055079038028002c044685806a11102940c00308910041a540310f82000e00d08110400150100c8e110190010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 220226384 1250 220225134 220225163
    0xf05040309050909010516180914010f0b0c0c2209034109010c12030914010b1810050a2c0f0123031507030e010903050d021b0307 57
    0xb1203140070f4404d42180c1d141c0018404175200e4a06800c00100650070280c138900025050705100ca0440d52080d100039040100038038a0310fa1240565041e0f1b4403070b90b200492030707480b150301141500540780ea8003000e90180e1900f560314070b060512446032501d130340c0646100b609164404000e484403200b0807070102d542c440c0e2150005000c08201e00854030880c41140443d0b21022440032000a481700344900c0b004000380c0c1041c3d0b6446000903113415a003100d00035159a0740404014000c08010805552039025024000440c46c2c042c01182a840c1000b8040c1720361000c6d82072a0250340601500020700111100030001e0340d6101c010381c0c50010700901c11561003142c1c0020300c0c4031201e425451401110038010003000200403101d500f80e810b580d8080355155000600302140c484941000c013055a061055415544800e180c2c50b0300e41340b2580c0d4559040c0140040341ca500d9090791402e450080104105114a40f0580d8130b650250840c200071201814001d09640402411079222450540c1c0202c0c010b2141c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 220227634 1250 220226384 220226389
    0x501020d050c0c06070c170303090706080702150a0f060602010e06060a12080306010c0807060912090803071707021005070611090603010512010b27010816180f0504030905 75
    0x11440e6031030a90401d42e01d40070040c0951610380c0003040006100381000b1030340d00e003071015100c0d07000003a2540c242071881c0e40c40a040305c950f890b001200c42c2c4a17288244c14004c903660384560700042c001d885503002080c00c1c520b80c10300301461381401001442025907424041f403510801d8040c6800420460300002080c00c84001d0342030420f034005001e20300a91004608104030264011645480368000402c240c407501c5400040f5802800010064006200482d0007400d00c0301039448880860f10405402c07004070015082650098100c0c880d504854105022306800728040c08034800c07201d0301146d000d510782042d607400510700600c992100c0000600c04a07100301001030381e1144245540200c9a49410f1000c4100018050b1205002c0c50340981c0301901440700a04c3d003504101c168035401003415032241540e440240400d0742c8580b0514103a0700001c000901aa008103c240031031144410655225081c648411000c0203c4190b9280e01c958a01c4808080c901030311030240200e100b9520b51070807505c0c1008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 220228884 1250 220227634 220227643
    0x507050408010e070e04080a0c0c0b0414040603080a05090d0c1d070e0f040c05090904140c0613050922120905010e0306010603050a090b040c0501200d051b0115050102 73
    0x20f8025090b8400c0500340720028a01900381d0707101d070303220000c5640c420b840081258841b0285200902d5008a03040c049031565011b0301410942d0748032003a103042e40c581c000800003512283d20002d00501410040c1c0c60205205100070700010002030283d050764401035940e20704041e00369005040c51036140a031104039244000240703070050120300c2c001c03402c010303d400007480c2c0c84d211140b90740c420b80d0394010940e150390150003541c1296500134400d950501d414203040204000e8000e8a2070320b03014480080c00e4928000301603030707100100b04000c402d007241820144030190201504022540c80880c0b00c4111540f00f001340e098019100e04912005080c0181018042e442503070822414031100240b003082c29200000c0c2c00c0c0c1120707050324010409880d00600300c00100031003440508000600f0040200b8054001541c000329442a80c2d4150f0781c0e155414400e00403a202d0b86d804060340c00400c1c20508403031143d80a05030f030840d981c030308440c100304000d011401c417070004500341c3c803813031104508020646e014031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 220230134 1250 220228884 220228901
    0x615040b0c190b1906090f090b01060216050904140a030309020a0b0a120b300d0504150e011701081605010f1202030c040308070b15060f0306011d04050705040801 71
    0x410881490703129540f6180c14280081509060b292481c03aa4990036003a0340000c401000b024004008510b654405800039019074071050780c3d01c4105000001e00c0300c0c030004440c005403070480c003000d41c1d4a041c0410802c1090b170181007511038950f13005c1406d08451061207600609486524000340c400c0a0b131062010105850780b0822190000344454102c41e03401501500ba503000315400082c500b0b03000000610b22462031040c0500b540305000485005c2420280c48403148541c0c9011983c141c403181500f00c1d40c600c90b50040e58100b182440001d0031050007001d81c04a00c4005050640035698030b81c3d1000601c850990082015601100310410540361564414006d084280390503040354800040c0500500955090304c24211381c0000060010b140384025240030b0b50b404214103580d41951700349000c540c00244c49011101c01050004483c600e8120122030150501ea1a582c0c1107561b0240117460408500394814000964044540401d03503c501c2442c0c483c01d065100c4548031750505102e182111a100c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 220231384 1250 220230134 220230163
    0x140f0a0818150c0304020d0507290304020a12030e04020f0307030506090709060f050702090405030c10090c09110d1b03110705070e040213110d0e150f0615040b0c 71
    0x200d0b003180120060020b81c420b4502d10070703c0d640c0c0c035039101080d805401400082d000380110080400d030705906003d1010441b012402c003038085586624519114802943d0081d40414041410041003e5001052480a0003030400c10004001e40c408074003680d1201c4403403c4010000000c006e419900740c400c1942040040d02c45c05613300d000c4030090200034980c0150310500a80300c64045055125204643c41c242d40540340300403500703041c80e03d15a29040034454210780d0050511418000d5547d100b10944160803280300c4d0101480c004042c0010440d1170301c54690b0700300411810f086001203010309015140c50000c021a07000d2445d40081c02ca0321140d0b03003240081402c20800c00440e00000d403d03010383d00d8019036100c641d2503a10001d5104503840070280c81c483d003001088203501440343c0140a8a8061400510401c80082c9403152075001107008654101c80f030700d010804016610340842d501c664068142d04802d4030340210700500340c0285d03025042c1000300042c000112310050010792004800c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 220232634 1250 220231384 220231393
    0xb040b19181701060909050312280216051b011404050307210b0106030c02061006050313050304051302031f1212020a2103050f06010c03140f0a0818 65
    0x11408080003010180b051041c034094120a1040500303081d40032500030a0496803c04c2080b005242c0107450b5002040c0390301c10100407a00180c0300500c450325403520321701d800800c1d03c481202810918000d40140301010f8140314410310403000983d040020240060201c6c540d511850584d800040403601d0001c8600c0c807070b10f41072008008030f40300010a0320540e030201074806400d0311100400508034000348000b0f0a004100800003c04d05c0d01544504d042d86810790948055544005503201b47c00800e03c00e20f0002002040081d51134280e0000ea10880c41c42801903a1525035200000792403d08d680c0ba501641a60010610140c41514000308199031002c5e4201c000e081d00e070a8940940302e4100f080a03002c400001c0d12240e06034806c1c0709007140d5aa02c100c2c6903804a42c20941200328010705004900800c1c5070030081507038280030850041c07007810140d54141a888003039404440012202e001007448d09018042030712402058009051b4031251030f999145149002501078007401c1c21000610002e820 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 220233884 1250 220232634 220232657
    0xc3501110703050c0a020603010f0e011406030402010e0a09020f09190b0301210f0309090f27032001020306030706050301030809060715060801050a0b030f0303040b0c040b040b19 78
    0x20031050358109601420126100c0d501041154100620202c00940c080000000820451802d401103010340c1c821101e0300b00b05a0304c1c0c0442003204920307546490790200b02880003074019032007290640b800e0b103400b402900e6013640da01038110a9804c1080811071a0070080741040d101d091001b0140d20190b0108490102c05240c000466a240f006000b0300c0c2003184222484203002e050001d00c41160b540c0012250388180d00d03810000c0ca0103050380104016142015690300c0e011030f890065103071614031400c0b601030800c07003188100c1c961302c1810422401d21403241036107145001c422010304c217100c00c0303000013594070724040c0300b01820404150000c0301400414401480490b00c1641501c0c00d60030700f5101184d4504e0a8284807041c4107031200d54000c018201031000c204003506400680c00703084071407014042550034008140c2c861008031003003541a030080c0005004510b9550000d508003079800d0440b898151100c015080941c0b00340c001e84043d0000044440706036074525544008100d031890801c050a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 220235134 1250 220233884 220233911
    0x100e030d17040605060a0810060504060b0c07090221040605180607020d121d071a1206040b01180f03150501150c1119080f0d020303130c3501 62
    0x1030025001500c00355403013000600d20384074054808060700c60742c812116001c0603c04154090b083c68002c55011301d041c070200150040106064807000c2c0c02080c050146103040203c048029081007011032407027029038114818038814207071070394015806104041614a020031115071015000c910701c14559012100b0420841e030302061800e41c9550364039120803810708106903200500b29501c03145514244031031070342c0c8540340700003000811110f08a1009048524213165001103020307031b0810701071030740b603103400181c991416600110300614141010010014941e0185144003880d802021012042201c207100344180000e21102400c440401800590304084651108001010b100c1042c00915080c100410403a22202289004054503803101c0c1060307180c4246282c6424840e401d0742d40030741000800014004207800325000282d4006528548400c80c2d10f0580d041c92540665143c03c085101007850003c803e244001099402d1250350803414000c00c8403103e03200380504001c2e0380e16045040c016403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 220236384 1250 220235134 220235177
    0xc07061a04050f0a0e0c030d05130b0a081806070e0111011d0c01090f050d0818061c0c0306060906110f01090309080d020109080405090c09100e030d 65
    0x129400000821440340150403030210902164015502504100800c42e101d68080380f030910596519400780074034001c8180310b035143d00010701c60302c1c1c064100ca00c0705ca6040d8000e500078051010b5281000d52440c1e42d4150808050304021501d0300020101420311898016200011141c482450080c203e1418480c0000d882c0d0500c41d068a030521000281081c2404020f50182a4001c000201184402035580255440e4004504031602180051402007495950006d0220640758041d00c8103d02c01d5454170f414003035070403420856480a0070710184070044d0312260050003940b125407420a102c5c8004404005c02d90305824015020189441c604122459000707600000f11a01c50910760500c01d8140c0700e0a0130551101d0400e1625800c0c40c2400c1d08042d03021901c1d40865481e441030b507119045d2024224283d1301d0000740644804801d000074401480c0c40b03100d40d0340221010308094036141000e4042030100804042043c00304040c000f1600701400c09016080c0c40c0310f42440c101c80c108200055804c0103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 220237634 1250 220236384 220236397
    0x7080906010611030c060a270c0905130c06020601060306081b01031503050f0610170309041a100c061d060f04020a120813060804050a0201180506210f0c 67
    0x20000d8030f52040300114400e0085075a00321801c03069810b61714015000348040c2c012a050f6846c0402072010410b0034403000b00030310504540c40070202404918001104015003805010800d4850103960404005014071810500404042c2c018014540c5801005001c64800380c0c002c80302034100e1502210184505500c1e200440c009090005544540410a041012198200071305601c10050784980349580001c81074032030071020754811840354454008840c000a10348004805a10502c503400ca18074080d003000404105160140504000800010382a40202d4610401050007205500c0501030706004101d000780000f810108812103461031a40d40d84802080e454614a5110100e000c640c1c402c4088001440200c6044a80e0103c509140740c0d241d0040b40c1c000c00c03045500f800010403600910049200e55007000c080d0000510030703001954540c41c6281c80903100080040301143c1d80d92110060304041c54148040c0d40701c2020020a83c01001c00904846400c1030303620700308900c08405804440c0c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 220238884 1250 220237634 220237637
    0x30915050403050c010f090b06040c1d04141f090b0307140f03060c1c0612020909070b03010f0501020f1b0d0609170c0105060a03080a0509030304090606020102040509070809060106 79
    0x603140d40303600b403c0300d0b0390080c0d600500c501d5080c95182c203181591904016036060103603c2140c00c80d203413901004101e1314900c02c40e402058980ca125804414010407020075110003800208851102c40c0041c1d90101080b01d401c030112113020b42c00889210f010fa1010090140700c40c00b006604001da00117036075105a072050707801e22074521808014039141c0203413101c0d0091000d0101d038540d04180b10440301540082c1c0c0c80e031f038442200030003000e065001402440104d072118030a0940000840d004d000400c03000130001306582c800c1100008500881c080214000d00940924a6419040c8000241020b601d02d021900716030100401000e8041a40340d00d6080070030817190002c00080700d1900c0b0b006410305010180201070342c09884020400410010800c48400500810540e6510720400c40140c1c414080070340a6901400f0011034140254000d1454440c000c0481c4d00301955084c0c6402510215040480140d4010404005a041c40e20241f030b00f16065082c50318041c6407081e442503941b001440303603d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 220240134 1250 220238884 220238891
    0x908030606090111030307050a140307090315020c0a082703070501050c0a050631030e060c0a24110c032d0c0609060a090b0105040509030c06100501030507030915 71
    0xd40e40c0e01450f580c65001403a0800d030786e243e01d03090381e000d025904138402d4200890314010789030800000c50b40403684105010744489005078190384130203520f94908890103210590170002071880440410003080706600c02c018641c0d030b800308110002c01d1000f022005240e84401008040f0ba01ea81c08284442550020f01e4495200ca504041841c40c00035440d01c0034059001ea401408529004520300243d45050306c164014400f60407595002590207952010b00003840b4155000c105161035402402d514490030704980c04000e51303454042006101a8004c440b0b9810195110401a994080d50356070004510400b82401001e001142d1030b0320465164440c2142441482104015442a51100c0c882c0e4000d100391a9014840c0d16079440d83c040d9004001c521034000000c41c110328a00a11070301580c4800c030520141d01c1c200910001e418040c0c16200c40303000511060101d40c1c01004a10f21401880307103005d540ca49800005011039401030540d00800d42803401c0c110105691624005d040a40d811001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 220241384 1250 220240134 220240147
    0x1a0f0d0212030f040806010306110307021e1c02061f05060301060c061e0f0b032109041d0d09150f050d0f0e01090b060901361b0807030908030606 64
    0x490440c403a41c0741650110b0f002081c0400d0040c00015628160391050400f0040c0d044009100d070018042113845030010b0b8000c00c0090341541000700c0d03c100d0003001604503008504c60781e201c140c6500e200929100103a00c04da00300600304400e5a61a070180f05220b15003030340e19040202040b0303184414011501408908043c43c07040220903800410340f00031100050b081440c0c29941d24005c0c0c00b65000a1248509100c80c030300c01c500e40800d10700010192183d0a50710784140c0c00d040700498205220299010780c0c1c2c3c00d00000280341c504001425501450003070040240500b002900c02034294002c02c00d0085050401c0d06c4030364104050401803403003414501c1e00c030402130b10000044c0c91622050803006040021404088805400105450b031250000c2c084a0f90740205020b05080240f2548200c1d602d02c1c07003440113440301c01e011210034607640000744c03180d10099101c46040d9401c04101c46e022010b200004007190f940301c8a4560005182e1400303200004445e00c400c8010300003d00440d00ca4040003d18 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 220242634 1250 220241384 220241419
    0x705030304031812080a0f020f060126030a030e1203010b07080c0f100609290904080412120f1b030f0918020307110718020702040f0504061a0f0d02 65
    0x3000d00030040013100a0156006190841075071704000480c00100fa11808000352460003c50000311a0802000502242c1e203440c496001a1009000c0724070400d5007030748224003901041c40203000403070042e1008101e4604145c4014641044840c40701c4000e03000344018800c0318607031011148410b80101086840d1140e0700e103541d0614003c5070300d034443c0d482080c0155412000940169045584840040000d8208400300c5400d200f03248070f00000021000780300b01958541f400b0410380007070240c068241816240c01100c1c58800100c6030564603007851955070003445500c0320f031108001c0e00f0703440d00100003150110100c5003003807050740040034040405043d80c8458400c0c0340d40d900a004a00c3e0407120300300c4c060840002584141e030240000340100c1303603403408000b0001788041140d01144000760034004c00c02080000350003852040341d100b034540030075250065503402400e000d02c0c06442c001800c0e05110041d504890342c0c4a400034041c6d10180d0580304269540140070a00c16015502049181800b119 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 220243884 1250 220242634 220242677
    0x606040e09060a0e0d0206061003061208070615030f0f08160b040606140306011e090204031407051e04020c030708120f061807051308010c0f08010506070503030403 72
    0x2604005a0104218450703000284240c0a0480e05030100001d034000070031039455081604481700580c5c00703180403c0c12800c00c443c0ba0b50900d150b40c0b8001031015166049080841700c1c150068800300000304180003408010712404014001341000c3d0481c45241d82c3d2851407100e002c400103400301c2c0c035518000e410301c00e031a4200c03555005030b107003403095003441c0c0e18107070b01802010f0f1019a405883c141000c01d1444030703400d8101039039800400903c42a031924907446804100d0000804005040d590001280f201038000340c4090340c40365005502566042c1d94035803134007100d80c4c000380c41070400410b100d0400890540c00207070000203880142e134841c44d45281c03620314411208001d0144200080b00d000d2415900452030140c3c801c1d01d049506a01c540c01000351010580785000d000b40c24040101e4021030140c8014515042160141104580e6400080c2c0c2110009100380d0081021011a20495a88056120b02501c0f08954207800c01e081da46840303690380030042000302400019100c90490800241c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 220245134 1250 220243884 220243889
    0x1050906120a0b011d010806012411030d0912020a031d0a0e0f040215072f0a1818080702060307050c060403031b110c06030a090b340f0305060604 64
    0x80008959460041c0c01700c001c401d99104200080c4440041800000840c0d401d040b101401e0380c81c26007045d401c99094140d000a0a00814071100704240c40c000c1a0502c003402d250760b105100041d500d030386404c000c0c00010b82040303513504641040407040002600302040d14000c02044100805024414004c103000c80c42c1c0da0000c0607090302c0300007001200d19407600349502c43c1d4401d41c0c0c090000f0070082240002400b41480c010684141c100c500d0000c040400711040044040810a0801c0c0d14540c0104420300056005400c114100e50420000b0700801e0295070141018007900780d0080d01c07035864128540c060148028420a00000494004d42c070620956224845500c259202410a441d01500611400010801100f400f078400d030107490040c0d414860b103079403850103007406c144013100b000103d901c018062441c1603034070b1a42d800420500308200e0f00c07494a0300308051401e0f0074008482c103000200c1003000781c05a07800c1030042881303038010b0703c0e0100c0c00b2441c100440d0940b504030002c1c2e031902898 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 220246384 1250 220245134 220245143
    0x4060f0b120106080f0313050411040b130f050a1802090103090c06110c04060e0a05071407050c0f030109030909090203070902070f060f020408030403110310050412140301050906120a 80
    0x41c0619040004198403820881d00601c044071000f1a001030026128001c41d9045079a20f151803604118030305140d0070011111300341e80c0345949007a80710f05010400746c20a0425050b00f181c0c580e010302c1542448058000138020440b110305102e89004000404212400c1019640e41d401040561099000c0d80240600b03030751007901f040c81c503900c86034000c28030a00020b85688a102c0d0600c56400e604291150100366412908807000d2560307008900c00141401410340700800008011805907101c0d0303900640010f921580107451160714a804100441c64283c06141c4a64546500b940000790000541001ca8207002000f081106441c00001d0a1070f0036680040e5020f03000103080d4040000440340d00d203449104140800c4468400031451b001c84c00395001e400003d43c0200000d001242403000c1d8584200401021170b00e203807440300540d20076108141c0d0201c950310002c81c46501816040000324807a09401c0303107810300b5903144c08001039542c036010f04064001e00101442d00b040180074440044082d401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 220247634 1250 220246384 220246399
    0x31506030a1b0e0f040b010902030c070605070c06020f040609080f0304051c0203030f03090d110709020f0f070305091503072003120f01051509030a1121100501080f0604060f0b 77
    0x144d0010822540100d4048500e100c009002181030240c0d44213690155130118040360800740c0d5507590b80000c08c000340a003c140480c0e448507a001450b00d0004215108801504a0302c1c0c0d850401e01402101a58220728003d40065000700007004001041c0c07011100700311100d450641a03131781008588460524041d4050000044807841c010780c080c021809003d46404841c400ca984000c01c581c085145c010b4a401904550b000300b1400380a90060442034820000d200d00d42260014202082d81c00b28501301c0200d600403901160740d01d4010001100080d1647d1080e24510701604020011920a03040c00c1038003010f2003170f0b00f41e002010000d8a107145100110381e1820f0406204107542040c007403013400d104079198142800c0e000c80720005d403040781001500034090a9191340d544002d10a48840ea00d03007100054004542220342460341c0501d030300400c400341070f50802402080003a140160090a030f940d02c0b40302c0400d071103607000407096402a048400000c20400315004040600b10070105903034004603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 220248884 1250 220247634 220247641
    0x2060c011103010f12020d110103020d06030b010303090509010b04031e02060a02151b19020a02030a031d0901030b0601120209040e03120702120a050901090e04060b031506030a1b0e 79
    0x2038070401981030303c404102035609140d0b5400700b8a032005010300700940201071070180714001a40118400c072280d0050401609000c0280c1c8104200c482c9980306580107000c9000410034144c10404542c040c01c0e054031000c21960500300c0300401c41c0300b5840700038000101c0305045003c9101e004201681300d640201010f91350741d00444001d60b202410030502d025a0b4900c008610206041c100f400102c0036004c8601e400c000b030300f1007034100c0c4480d010004419409544640401660140034000c0100c2c0310f519003007903040c25401c18240100d03d0b910b8040c080c907102d0300180082030000038211740c840d000f464014040e180c2001c12202900407442d00e50741050510880c5001d03070070040041c080d072643d0b001e881c2030030b59514681203a88454a805040d0050002c00210503010301ca0350003000c2046040c105480c050303554035212040d43d0b030100d90640e09166100c4400c80d0b03d02c0c081c40203082d545c1410051386414100303000060748a54030703c00024896110a684c284d0b0300380c0c0e15494080104280d064486d070307515 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 220250134 1250 220248884 220248911
    0xc090c1d0102011116151506030914010617010f0603030905090a0b030d02010c1d0a0e0405011b030b041b0207180e06011d0f07020304060c0501021201140112061d0402060c01 76
    0xc03c60f14041b10007540403101440c14200512800d0240da206c030124040844c50301d48103600510914106450240d40080303400000c4200f40242e500a05030011361a48190711408000c2c2110200c00b009050141003620800200344c1c0700384603000f41c441c00c50382c2e041151120000d5500a0001180458041c01070b01101d4419a406600901d02c1e02c841c0e8503442860708881ca44140c4840048400940c040010301c014040b100d01e407014180c0c403038800c00001a50780e20781d18426040c9130010340c4280c0080e896000c5a081400c141c000d0495502c0c1c44c0e038180901c0080194040d40740c0440d4042c400c1c0071040c00f82c900e054184503412840158030f03018255241961200614441000200c0043c02d5410444011030f000c1480c1556061094003540c0c0518109400d0070001c5800c0700c082c9900760b0f059034003401000c4907010340d022483d0007020020000c0c00c1c2246008000b5180041a0700c401e03103042e140200401002d100c120086480700002180c00c00c40d5640d0b8400690f00d0f000700782016135207620704540f808400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 220251384 1250 220250134 220250167
    0xc08160c02090c0309100e030a0e0103150b030405030c070f0521070b0f04050d12032406050306010c0b070e190e041205120103060b0f04020a1b0c150207030c090c1d01020111 76
    0x44015078842079640ad402c00150162a420400c4402440107904100018038000000d150050300c2001a286400910a80c00c1d240c0f0140f60004075402080c000d08100350f10b480bc13051010440401c5040102c040c0c0c032990a9110009407061824444c4001148640c400310b400c102c501400004140000d00030403402c0c840e079014411b0700210003082c5013094841c120316802c4864001801144000341d552030601a0484090308003400c0c071414445800d045000140b0284800ca1050b001941c92200f070480c4d40d0100071100c00181001044240e821000f80100c1c2c414a45a960060300f00f480c43d06003405001048600748690102102c240c0039003030000c020405281c21401400c0c0c0209c0d11492070b210f82104000c2248680c2d00b02d130003c6000050102888100c070408050106e008001a048142d62660303030783d90f0f11011000041c016004603c050040180c0d442942d40a000340f0741c030810920a01410241c044802e2200d1001511050520580707180e200f5000842c034003882c0e0044548a1a0490055821 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 220252634 1250 220251384 220251397
    0x30311060c190c08040f030305030406141005062127150a05192c0a08070221100605010e0117060f03010605040c08160c02090c0309100e03 61
    0x16000d54404101c14001c100c050341d42ca0340781481c1c03038032050000c1401652954060081201d8550040c403001035081c108051940056009444483e52031030302d80340080c02ca80c0c9181c0c0042c00440394805200303850004113201802d5030300c01c0d10700c5523564403018020408185c039080c6403041008910100a001f840100d8004001c80b48050320340f500741408100da680710303480d600205040584180008141c140c460700040e800500b4200d04c0c0380b411a42c0026a410341c1c2c015049600e01201c4039809440b0034284109002d9510036070005400b12200c05c5d59815010f00c54020068442c8610521035001c6801c400101c0020361030400445170030b1119610094042c00d03c0c0d104103404900c515003141c0303041d40202c40015140a4110043d05d05030341c1c0071700b0002c04551840c692900f66588a60105a9032503601c00c0c215000c2c8a9240c9190b0361601812511a800c1c40d50700640800c07400e109583c005840c1d9200c1c4030380103800b4640301d07a180c3c2e0380c464080e8609041d500001d0101418550400b00c1c900f0080001d001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 220253884 1250 220252634 220252667
    0x61814010c030c210807080411040b040b090903130b0412060b19060f0906020d020c01120e0303040804140604080d0c1406040309030b06040e100b010c0b01080c010f0807081303050f040303 82
    0x2040d1b80d50707140680703030480d0072940030340f48650100f09042c2e640303820b40c418000303890010700000d01c20001402003030801508640074411544005542d034840110000306400030314242450754a0103050000c00c000d01106408000c080e0b9480d0b01849000f56184988018480a140661480d4035030f0b0b65802464140001c01400c0800c0e4410310200321a032000c6072010404d24079400034814100340394011158658098901001541c1c0c810b80500144000d00045001c0c40c0151141c54899081c403a04108a42c41c0e040d1141c803e1604005c100b02c12034010031051544400c50038107848124681c14145440400381003402442d000701800c02081503003000b0502c041c1d07401402d1558296039404148000c44041c0099040d107a8888600d06100c00d4260304644444030042c9406030310314025540e41064000300707822103c8c00d0341001da07950005d540d002c0341039080030000d07140c654405c0c1070125010300040000303000b00d00180b00c0c0d030100c4024180100112401825001030680e602d070760340d050091040d00d41c0815044d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 220255134 1250 220253884 220253897
    0x91002100b0d110906031213051e01080103030c0812070804061401060c02121002040803120c03070507020907200109020114040b19030b061201061814010c030c21 71
    0x715941014240480c0103640a25002054400340c0d0400072811802010103606104494040d80300800c1000940740380780f42d5040da090010306210810041c50741c850010034000048080717191003603a01818803030444c0e406051220401d03820b418010402e2103400088804d040903070050101d80366001558620490080c1020080c8103405102c2001040c400c2c0f00e1200001c0b80c03281c2c01c4015203001e10003480540c1350141107603030100100d02c40c24242e800c6a8008043c0e41c01c0459181100e6107594511540302c1d036480916807443c81c003150040d01c2401500f50190003a0f0318580000d1445010b084a05d4000e0424800e039104e80e8540d00c1041c0c040d01070340303000301c0c0064088030b03150102445000a660940b41280d9589040101001102100c0d1091352110f000300360302c40484520326124a0001d1072030250241141c6c0480d0b040c600090942540c2c0c01d980b1040c041990800c02c1044924100d690001800346000d8a01307165030f0404523a841c1c604003001d0030003600010081d00301c5110203508455002c4c40c0c1c03a0b00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 220256384 1250 220255134 220255151
    0xd0c0605090607090603020c01060f060c150e0d05090102100504080408070e0417070201180b0d0605030c010e1c02060d02090315070503150d060e0d020118020109090902040209100210 80
    0xc0e51921030070f95030f64010500003241030001c503000e5005040350f451804000601c00d40c0c1e40d082c60240f410311360301890205042600d240d06101c05542c2034680e082c0c0c1d4072070500008008a41e51aa01c4c0c020408481c204103020406051b142e109110035502205500c0c010310160909060a44482e030051080741030700d1240900001e01e51000032011441503030001e00d80c01d145a48803e141c034032544104000c90400204000030b10326054800000c00143c03541144081d1191282c080b5601215116048180300303500803039010101d070382c2c044208451803105551284001d81c0f959941c40b290007413513000a500c24001b0800009603d4954042c0441c0c0f10114221480d001d082c05e5444094002a03d0700c800003001080000c0c1c4004c4200c1c41403c5440c0003600f080e40555068949004450f503042441c043ca0300f00c0a005d0329a941d09019403100c205210040e29640361441e0b0020704401e040303100700e480f001d81f145003080641d07a603036050312100c14000d0028440c0b0981000b009407106100b000c00100030b071500c0800c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 220257634 1250 220256384 220256401
    0x20c010e1606170105060d0207021203071203090f141204140a1a1608040302060f07140f1b150a020d0318020904020103021602060a1d060c030f07080c0d0c0605 70
    0x7072168610021850000380d9082a00b40f2003c0da010209018005408101049c01030311342144500744900b11102540d194a007614140c1c01505e040440070301014180030418010403413186034480f09642c4880001410035446c1000c80c18424600c00104ca92080800d00040c070f00c0d84c44070304074107580040740d01c0b040b11034440800d4502f8615a01202600807000d00003030845600c0c1070107014246000d20003460903d0b03903a07400903045601641d6200d01c0c09a01152000030000702140301041c0710620710250046890801543e80d07103148808807604002400300c0e10070959100e8510381c0c40c070b4002c01c200c3c0036030700c10346580702940e0351070349150800000c3e160103212018001d401d03450b403000960040c07084140ea00c56400450294001b1942180d00c3c9541a20002c01640c0310380c0100040305042e22541940d10310101d0040200c440c0b80d0800340142c100b00120355030310704040f0881d000000103000440e244c404034204001507002d41c00c0d603802c0038440c04424008550300b04030041c40c558032541003400280c0d9480c05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 220258884 1250 220257634 220257647
    0x105070f05061801200720060a0507020306060301110315180109050103030914010c02040c030b0d060e070b0304050a03080903070b011e06050901080114010e03011103070f0f0e0d06020c010e1606 85
    0xe0702c1483c5c2c00034048540054180c40c3c40c0d504138100010b20044468100700015080c1d8091030b8100b0201c1c0300010010b0131401c00744015507100400301d000b042141c050520703810107844010460b444102c030030300901c5540d03660814000740440000702040d909603154074070031006190030300065011500c59000011595441000302078415010307995460300c045035a080c04041c1154105039014551100310401c41c42c0c44400b40c1a4146004003404150340503010005424405070340c2003420500010803c210200304002142c01c0c1c0164540f512804079601c400c561411805010001460024003c000213030701d40c91107a0703ca4962414000d04844c19580b01c0c001d0740c1911440a090b804200d00000410031004080e80020b41080107040600410a480300081c1c21a4401c403d04502c0362001700c28409403503400300c0f9031203e8030307a2410600c482d0443c200d40034100402604126100300156036109080007101d4054503046488040207101c2d40b90303008100381c4c035107071b011a00500c1400341d40400280c00b8840e48 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 220260134 1250 220258884 220258931
    0x1d011d0606031204090f0b09042105070b1504061d0108070b03240a0b0d02031e063105090a03021203070905090603010b03031c050618060105070f05061801 68
    0x4685521301407502041c0b40140c00308906240d1081c0d036800e8031442d651a64035400f40320304e1180000c0310720b420070041c071524080da907540c8000070040184209000218507065498010020240c0012205607a8000602030132113070300032010085000065100030441c01003898180c0d0903000558040c035403220680c0150380001c580b140ba458044260315884240c608210402952001e02072103055030303d035105d040c0c040c3d00c00d10351000000e6000040120700d15200780f043c041860034107840360480c2001c1000070041074007201c40c51282c072124a1020000182c100b5044144840506c05010a20340003060396200d01010009030098000c0100c0007a204d442e41d01140e1107611191140141541003200384038031100002c20442d015035031000e002c415942c1c10405000301034021002603024219586150003550005800240503500304441e1a841450020003290710803028a400c6031176a00c0d40c104000f42c032802d038074098102d018090910401c001c20081184554044e10300900c0225800007024000d500d086 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 220261384 1250 220260134 220260163
    0x9020105031306090203030f0a110105010302030d050c151302041d030a0c0203120d0621050a030e0d120206150102060f041b0b0310050f060316031d011d060603 70
    0x80001504072800000301d1032016003d644006602422039010074650303403181c1310100d50808045001e2640991080c0070b2801110518002d21055140d0790100355a00348030401c0c0c4043c080d0205080f19100c0341081064100502140700c080d49041c038092030502030354840c85c140d00441c207100b045145500c01d0381c407091142000600a41ca0300040c604200c44030081c200b012603040c0140724190300c00c118458050660340b206a00b00003030007441c080c00210b00001294000d04084060000c0c100403c402096403c04a03404d420600c0c20303010450001610140403941c01049001c80e04007041c041c50b40083d020303100f80308901122050781c4c051401665514021203800c00000c003a41e001400281e5031050152080134241c1d0442c40030754407021400300c05c0d003086582e2140340300500720800103483c00c001c865201c01c406880451441c02c100702e4200603003100082a0081c1f40c0c8800210b0140158040c007a02044550390081020f00c6070414400a00b100d6620b04984610442012410038074010441411000c2c0c2c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 220262634 1250 220261384 220261387
    0x30606030e0a20060c010f0b10020d080106030f0b0d0606180b03100209010201020c100c020c012105060a050a06020a020f06090915030c0411090310061505090a050409030c0b01050409020105 83
    0x4540207500050100003400e50416418000913403405401d02a1f8100024102004560b105003601031005a5030000220800c5601003444020400e4105001c94190f912a01c4c0118505040300905009400c920380f0b001d0308114026140801d1108940c00b006c2514000203290a29803940c50400055425803560907a15400c0704c202c44008c030803681c1c01401c00341c0043c000541841d00c81665179040508040c01c484110380c86030061034601d035040c4000011030409003003084480d481403070040540101201100042c5542d28081800b965944081c1002410002c0c501031007140c443c2d07402503c0d000c00b07450481c0211107441e4510300c80e240031801d4990400b0068031600c1e251b992201c0c40c510710280c040c0c2c041e8150165803007070303899512107000385030340811030300d12507070340da0540509151800d0050455443d94500d08402402154060496500c5011544c90920348a40c0b82800003907403e1020f40c0460b41c002d04e048a00000c00d40c10122281e25603000300ca00940da6a83c800c188001e4440002000b400101c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 220263884 1250 220262634 220262663
    0x20f0705060c0c19080f010221091f0b04050c07020d0f0314030f01060e01030624050409020d200406080606070623090708010902060a140c030406030606030e0a 70
    0x81440203002c20000c04002c4401d03212900d40461400c03040c0102c90786540030a071105100fa08010441c45a03680c041400841ca03010490810469030f031a40741420504440c0400880c2036142c0401c820300c031208095000408a2403211000401040c80c80c5d0300714003a44c10000044c10030f0302c100c4240c40010360080c19154807240223950ba1034041d103d4803821000e00c03540000300241804c840e4082d605c15118004100017a504010020748035010005c5a03d040505024050081100850610368602c81005801c805452411025512802150404680c1d9032021540400100e201e4000703601d10144c104031244400c01c84480b050b994420390160301e02207842d0300042561030407c003000b0101c01e8003a000025050519000642038810300300740c030324040c096000620144200500c1107900501000008000200ca103501085203801591500400d025881e040a6068070b404421902800d40d0401541e940320f4903610b01400034040c0c0c1c000e20000900d48130603a000d03484c000800d44003058021210489480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 220265134 1250 220263884 220263889
    0xa060207080733020105070801090207020a0e062b1a0f0726040506040b0a0c0e09040206040f0e0a051005061c020d0c080906060a0e18070b1207030c020f0705 69
    0x910300d0010303030700c003002000030000301e404902807503c80390459500105882c201210028804d18068205040d454030400c00d000c01640c9034000102242d01d400f101058564800c00040c04040f8000f0222045a11054500c4014040c980844080510941e219501018035103051030f100d000882d509904440700901140841e80908400140002000d61918000181c0b56007140507690940e8102c03041d52001007400100030804208070b41c040a0060100f1942c21b414400400b0340c1c162100f0b403405012401d012909540350b07074040f40c0107803424204246400b95141d00d14144480d003140c001030107a25140200c0c0200f0300300c0c81d0310303c102d0388010700da03a040030342c0900d1603800c811002e203016206942c200181d9000d0b170140d010344206904151111101898040940f6003040b0008205920503543c0c01c00a004c0500094125900401c010f0b044102c00403003900b54a00d001000d03001103011a0010844512251910750100e10454066800784400c001482050381ea454444607220b0541c1c001c000c040c001130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 220266384 1250 220265134 220265159
    0x902041d0f07031a04020403060b010906051305010c0c050901030b09010e070312050309150a020c010f0c090e09070810020315090f0604150e0a0e060f011d040614070e0a0602070807 79
    0x8409004ca609481d280c610000b0100d911541c0220380d404e0319142080c1c515a0030070b1162000b0259402d00318908860081e07840c0c03a0000d14002e0b02c0c1408038a9444009100802d4240c60140c800030b056503007196107a0504e1034080d4002c88041c4a40c1d800e00d1690b81d000c01010551508503135201c011208000d07294481501c0c070f5040102440a5840349104504502e0a90b521050050b40a05c20050ba10b40c4c3d0510001d003590450814540e2141c2011180704c1c074254000c2c00101200c6000300c010039140c9550540c071b4140010350303000318600e00c120a9512800139040d0300450003199a002c01125038070509040c048603420482c0c0403804882200e0015640f8209070b003045040c1010780c42012100758440702440c40101080e1400c0d141c051b928030044d51040c000b00311041c1c00000e120080300166141090306110064403428000301034400c1c80100741080f0132a040a44100002410b001d110f1a0882c40141004100d030b00152143d41c00740c000003040780c00400e80009440302c2e20040c141c0d803030900d180f0810304c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 220267634 1250 220266384 220266401
    0x712200f010c02030f0a032318060702030708030304050705010908011401090506030a1b06090b1305010e010c0203032b0204060c23030304060c020c0a080d0c020303130902041d0f0703 80
    0x54052807502240a40703007031041142c1e040c422344440351000d141060082c880651802c007240602c1c41000b0704514090400010b11002c803007150142c0c0d46201c00d201003400c20405030b1000c0e45510000c001c0c841041004186a410342e0001e070386201c21669505642c500740c40044143e4823034826024014810250141c00140d0711000141c2200c5e4541003a0f6107060b5042040842071040c201c0ca50780600c505039110552030b000f40b88441480e0300300300308025444480d01c400c2c402c25042c000d44401701d1420383d0042c00750b00d05072600101920f0b1190800142e07406110034401408045140441480344c07604107510030f54040e0f500c1642c4481030134100b0754403404048591228a44100c59854001c00110f108000543c4200e12407100418010100074004c1c1c035010340940d42620075005880140060140052442d0043c1068a000b001a4004e400400e0a40c81903000070301003882001c1012442000d2500200219661140c440e070055100f140c04401814050b41c2d15440c0e0407088012540040c820341000a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 220268884 1250 220267634 220267639
    0xe06061503160509130501090510052b061404021807020a080906090306090a1e0312021b071d1003080708131d01090506030c030d031505030712200f010c02 68
    0x5403203803c0c0f0010300b03400510320304017008584440043c0220b5080d8000c59410003030501403010b006080c03000041c1506c40030302c1c003030300c600b82d0306158404142c52450540344c2075904041c04024000004401d150100b1086609034041e82003080780d203003002ca865850a200303d00380e5000d0207e0304496036071000c0c04d41c0b0203100c10703070b0000c400d00855045d0b603400d000d160f00039290600280301c122454074081060800e02460040034003100c41c0090007080c1c1041c06030b81050040100140d60386d04803a070700d204c0c0324000c07041601107101d8048041000004e0000300c078480c414100b84a070603950f40201c0c040703580f495800000c01041080c406200055a9000a0050b0b01941313035403030f0038071511180c5400c1002e001c3c031500000726a00348010403d2601764401e09401042c1503014142181c0b2a070003007aa500c00052140b0308043d03445051a100f00c4011f0419006020005c0640702820703a0380303603151072006540d0302c00d035a07207104813902100c04040014851400380c009813203c0c403280e9211006440d2440340710360980c2c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 220270134 1250 220268884 220268887
    0x90c030b060f071502040302010509010c030c0507140307240c0206070b0f0103231e0703080309010204080c0102070303020d03200c0d08060114030105040507170a0e060615031605 78
    0x54031035840c04081d04000300303080042a120011400d082c50360344416104c91018074810401840540d07801001c90302126400e0822100701629403404a5070003040c01c0002c4e059000314a400f207204658001c1180b55030400714110b880707003610f4800c0ca185001a1424480c940040000d022003a80e020f2600c1c036400c2400189580d082c00312079200c0c00845e01085030783d0705160f00080018030030490034600c404d95940c0e9082900b0710903010349804696a40c429803106445840786000e910f07841070100980d0001c0c41e801029140c0364144150114043e410070700503603695002d450b4501c6007d51000038110100d0760142d004010b03d07404001d0640062402c900091001e08410008203000b01241000b05171a00c80a40105110420072100800010700504541c0c100308518450060308000042601d054410440f00010151104034090364a40d0000d100c951009095000704900d10380030346c1c070110f00c01411009a5100395100c904000140e1a240c2d03018845c4001400450700841c1c8110b49600840038030706205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 220271384 1250 220270134 220270151
    0x305071b0f020105130605030a1503052e020d0b030d03050603120c0102090d0807030f020705061b070302101205060d030504180e030f040302040b0d080a050a18031a090a0309090c03 79
    0x1170030001ca8103c0c80100e01c00206000401109108502184004540c40180c03241107075159900d581c11036240c2e40443c05442c558203002c510907038600410000c15602155503d06519080340906030782d03003525101e030151010111720f582c0280106440b07908001d01030079403c0c1030300300c2c0051907030082009450259401d0100002ca80c8070080b5814040317018850903525107000c1c2c0f500614401503070081d402107420126041005407640400c1d0340e290098046001003a029583c156032034441c09a00107903208180094030008a5000040350400c001814404c0c000f5a8509c820b02140c05944c5100800040d020002040064180034035116040181d800c045624034900340361504d140c0085040701e15862002404008519044c45100c403032013029aa00710103a1455140c074241801484503800030b004000400b001414031071110600c0d580001c240e2500a1038070383c144940340040000c03142d03001d1902000400ca07010740c0050030305420b07549545c0b1f90101c1401d000c286c0c2c010380a00b80740c481c24942c441c0d40c030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 220272634 1250 220271384 220271407
    0x150403020418022107060f050708030711060702010506100e0111100f0e16030f0c0b04030605011706040b0a15090e0d030b010f0c060510080a0f030305071b0f020105 72
    0x4010014552070350038468000140104162800c5565050b401004500000d2101c0d0201080078012104c0b51f043c0490008280001a00e840c030481d0401042e141d800020814066004082d01d5050302004088541660361168107038202c403c240c5803980d10547c0111b40c0d41020f44139002e42101c400041c98241c3d81c01c01c1c85581d81c1d240150855103d501142c44030512200c0494a1207810a00c000b0340c00104680108402943c01500312400041d00d0400510740007002d001062180c1c10061840300190b0f540e1b40d1750703810314034010002070207840c18482650000704a664000a4480d02481e04810041c03140c0d1142c0342c844000305003548070880301c0703640240c002501030814420702c503081090502610761003442d510010110b803204c0c1455414000f81d0054520b4a540c00000c03c0b44080d88540300055a0701c07141d1100021845aa0201c2200e10801c210031003085900740c80060610320a44041c440e51321a00015074040f07120308180d010004490903403c0104c3c8007856001e007031134010304104e031500b50030b40385 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 220273884 1250 220272634 220272641
    0x2070f09110d050702010507080916090e0c060301030305120c070213091e0f020907050a08072a05030d050604022508120103031d040614010e040e2401140306061504030204 75
    0xb540c4d00036035034500c204800c00d40c10001d4180e00c05002d20250607425141c20b00102e01c4c29160190011a950310004001034543c10084200c403c1c400804081d242d41e034a00e4014207039404000b80c441c0c40c42e00b03070022402020490302655280e60f4010021818030b210724015100800d04603d051710902e13980c0d0700001400720200702c82d444c2207000f56580c61541c0c1d5140140003c880f4050f103068204003081100058056004440700d03040182450700d40207110410604c043d080b090701030345591071545038a566040081c004020400303082110300900c101e658180400089000d06c1c8441d02544c240c41d00d2480c2000d1400200c401c00521802c0c0c01c0d400c000801c00700440e4480e00b6081207011550944501002803c91000003d84400454092040310b041c03150506106900100b400c0c1844000300040206958540101c00849454000c031942244444141d15504128280c04070f03254407060700100d540d0358002c4e0035100c0000060011701041d143d000c00c1c8aa000303c800303200c02c00300b0810322011006035214003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 220275134 1250 220273884 220273891
    0x2071506090f1407020c0d24020703020606010206010b16050a080d09030210050c040335040513180308130506250305070c02090604020705150709050102070f09110d05 73
    0x5000107039907490344505508948021050b003040111450800c00c12560006403264041e000380d407d034102455606c1d201000c0d808989440d02c590780769060030f1520a0959001e070402c1d038007035130840c4ca613031711010016620741c2c10031700440400c08810401000c40d00400b14421003094410301c12030311408007545640c00241c200010011010761218540d609040e0304103e00d12584164620802407400d10201031001d6104900c80103000c1e0406030b018141d04003500c40094a2440410080e00c0c4c11500240803440551250144500c0350312006e100442d6280c50748940c1c82e402040c110740654002241d1801e44542070001c041c07030780600d2845101000980c05111140c0541601c51550f51210f64040d481e120f9088100c008404041c42c1800b0481001d9110503000310311034040d00d40c3c3d0306588074403001c03a01900c107500001c1c202e80704110042d8800c413940100d240c4110b55035904d580241303440300012a1a07894602c5801810b0390712442c01e0000b4a0360391b006c04404546c2000f0645002903100c210340036141c048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 220276384 1250 220275134 220275149
    0x30c0f01021305030714040b04021207111b030a060f060f030309150804021807023c0f0304090c0e040903030c0306050604050a06050c010617030a030f1e02071506 71
    0x8242502c0002046226101604045000c0c00c0c01c20b043c22802d4490070780e00802e0340e200da0340300c8640c0700031a11a0350440310000740c14070510340b90380340488000d052510220307511421441514808003540002d00d1171900c3c502001400b814030380b515500c2d4000501103051164081590301e202c0042d4290340c00d586500154800c0d101c18401d545041d0b08403d640c4420b0007143e0a1000b20b17010030005948401900b0f6040d0f0710107141003156250368001302e11380001060b00f0f81104003500b181c03140d01c640484241c140300000200e00012180c482e04129200c0322031104482e8554001c2c002400341020f160041c030300c99456803400201000341540048c0c141c41c20a00d044c0d0100b941c90308030b6009145e05000780b5001d4a420740d90300d0710b494500701c08a0011086445000c081000204510301381050030340281d40244a10031024012110302c403080c9449038800b1a050010030f180c03081081802180e030040034403a055107003c15009801c0f500c6004081c2d44058400c80d03203041174604140000075141300700030140505 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 220277634 1250 220276384 220276387
    0x31f060906022509090c05060c10050108031305010c050a0c0f060e040c09060c0819020d021005010312050306060712050c010b010201063807051b04091a09030c0f0102 73
    0x10302901a0801082000d2410f1000880e560100454078103006501211400b40c1c2c00140308005040c2a002d0240301c1d0011a0b00100000f821480c4020016518202214420382000740b43d0341c070000256288070341d280c4400c8581040f2020003541d03008411060003d07016006580014290b5a80e40110072500c0d00003045c9804080c50034004554000354802100a041c0c90400c070881001c803014003070243d0b5204400030810851039040800c5010800d407211801c013842d0400e200d01000c90040c0d151a5400e101000510a00e80c08203078510030760141a040303070313000061000b441d0300211040b5030580c40140707144c0d00400c00b0410100000d420904a08030300c12190f071020349441c0c030b00151f94291030140c064035046a050900510010b40d015091008900070001050410724078502c00d00d5070402c0c850000200c68002141050500c1f001160b000444040c00c5022680c004c2902d0800040311038000014004001c15820100c5807409503e000340c000c90490f04481c18004982d01451030a0391184100300366940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 220278884 1250 220277634 220277639
    0xf1f0801052508091c0e0307090f050f0c041203140d052a0315040902030f060406050a1103071103040504060305030423010f03020a05092d0405130602031f0609 70
    0x35800d04030b036075030240c51500b0f083d24281050310554030303424003944102e505544030520741d40b139010b07841c11840b000c0090195030090350f07034048a40c000c1460340c800507201403d0400080807001c00d08111441030780406186400d150400b0b483d02d00c10741c1020411010b2180540501d280d1100800185c81c055140d500041961f02e0450b43c0300444130040d121099010b4070051640002d4501b1a0903a5805400c40d9282404801c024000034007900402d540607400d4060000c042003071840100701c0501c0f541c09180c081c003264841c683c403001190402d029400781c140040c000300300c9586c8905641d5101d500350200712800c01d91581c0010f0304441d820f81c0b040741c0c140d0000804004081d400d15401c140720315480781c0d88a54500302400a0140c2d480c01600c8001c050380050400f5240d800b0f0300a5950880e00030302141c041d803c41c956082d041d21100b0241c400c4018034504e512005240030300840c1c0c0b0510840451070680b146995a0340003a4001400a0041203259880b40c5054610b00c02040d005124aa56841e02c191 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 220280134 1250 220278884 220278931
    0x20a0e0402011e020a060b0a12050303090f0a0201140d0603020301020309010f140f010314070b0a0918060819020a0305061302011e0203030103020603040303150605040911030f1f080105 81
    0x903203940300f0079024450020040e6100c0d000b0480811041d00554041502111040020501030280c0c00841d46c00e014501c040d02030050010103107101303036181d108480101032080d02c070b555a10140701000340000c2000c1070180c5101420070280441c411441c0b000b0030406e440368002400e981080ba400714250b9903814001d81c011855004a00c018100c0445038101400d11100c6208034440c140400381c081c1401020140120808000d05002001c84818a54a032500c1c590018041d5100b031041c00c1102c0e00401000050111901c10074044442e20002070541d001e8111443d45036484490090741e100168180001c0814030070b01c17840e0702c225a1204000b103034110b144005000120b0010b44e203845090755402c50b61030b0b40d800104613810359404031001e940701d0381e03a03141c00c0b00901003034034002c4a000000c0354001002c0703800c40d0140041d0b88990500f07000041c620108004980000c903410b02c8032076810780204040203121020760000d4401405000c2d48151124266820344000ba10114a00045e0701040b45090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 220281384 1250 220280134 220280147
    0x2307061d01030902090a091502031f150e1e09010306061d040b0408030c0705190c1401051b0a02061206090a02030c07200d05030c1006230d020a0e040201 67
    0x195090038100040d41c0c0c070f5008988217100c02888a030f041c95032140a1420b1040a10300442003801e040404d650381e140480c440d02c034003640480d00449110b0282c03c0403410700b10b290340c802c4c0107110a555480183c4044410881c4100035803440c06600c076108040141c654a4031268503003e98090034011a0503860250f415901940701ca19042c0c4e40103018040c80f001400541841c1d800680140c00c054413500c0300856007480c0e10a112008001d8402d9814441c120f401040c0110101401a014808420790b104c4118031030301c0d0302448650028504000d0f40881c148100711034244001054201c2d140d1040a5000c01c46c203500880700d48030070a40e90702c20004035280610541d680500c114405508502307103a00341031034074050300704002c0c8103141c0e1880004464941000682c07042e040200084000700c5142000740c2c49030304c00840140280240680003150042c0340c0240c1c401c5500c09040054035000381252080421100e25416501604200710074015a841c076001d10050070001b0840001c0d41054030015240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 220282634 1250 220281384 220281437
    0x5190504110d110a050f0102121c05040302060a0c050a021f02041d0a0e0102090906010e0d0b0a0c08060316060c050102190e040b0409110d1707060b010801060503060904230706 77
    0x350460f2510301141d980c0440c03114600c4841035149521401c20b200760540ad01b11b110180c0500e1445c18040005141d030000c3c2c02400391144810420a484906000325124452500c580000d43e00105002c0b000000c008a50090b402e40440c0050a19031130740d03407000e03012055401607602c080c0c01c401880780c10b4007588a00c2415a0006000314640889500458070880d0001d0034035042c400421210003140d11114420400035074001030360400c501d41035074020000c00035902d00e00000303914600000c00c070b420300140310346582c40600a59415a440c2200480320391241680498055400380035185161040d44462155110383d80c440c00c10400c5001c00f440701300c03130700540b0851096040002000100303407405a103170b81e6400700395480c0d4045001402c01c82c029440910361784c2c045180004155080c042d00e80e0040f56011000d98410407580d03603070142101d69010585506600100d02008240000e0b94020b1071441001004c6110300d46e8043c2030382980c00c01840341d20000101c2d42400c3d4260002c600f450240d541e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 220283884 1250 220282634 220282639
    0x1009060c1103041d06040f0507201506040e0f12040302091e070f090803180a0506120c07030c050a060f15060c0b062b0209070305190504110d110a05 65
    0x10035107814128030760190101c8124151860400c089501071b11107400034040003550b00c0c070520203401c01820050420b1620000480e81c5006801012030f1100d021410500403111030600c4a04d0380caa0508100003017413070354a00b07a0740d4407134031010208025090007018040e100341044140c460b443c5006001d042200101543c50b01d900d804800b801011201c80c16a03006801480e00780301c9012205015585407541d0f4004800c24800031400c1011170000d4031010003041d10680d0111980f681d22010301c101c9000703010402e260300e1000800600c428407800c01a00c045400f0749030035010f107203107525060704000d05400140c1d10070b42c0f541800310000700940500c086240e45882c41c1c0e40954a8400700034284080c0c0d074001020300320f11402103440c2c0d9950707401000c2005407840c15501010b0041c1c0414082d511184070480c052501040002c0003035000b40309031440380007400c1300280b811103e00303c2c1e50f00811000703000300c0c1c0421f420a000c0a20792107a40081200d50b1040fa0103004444008081080c1c4c440194001031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 220285134 1250 220283884 220283887
    0x2040501020a1b2d0509061005070f120507050f0f03121e07050c060c0a090b0307110102030a090b0c07030906210f1b0908030316021009060c1103 64
    0x20840e41d00250b80d405158208980c40c1c0c4a90f5960002810300c02180d00150700407010001d155102d075506120704410100d80d1403044807180e80c0d10309102010204071442a8810341c09617a5911040c0034000078201603200b0710841d00d89414a54030281c0d1990010100e000080340880d420041000402018074601c90b074900405503d08044481a6244078103071980c034005156401150200d0607880e81c070006000701019003262468080801402030b0071424a1422902c108400300b41140c10110490700413542943da1051254200f50407034605500141008d001c00070364111030240d864007072020b54003070103400f400400e0000d010304000c110014054030400c08034004000c00d1000a400c441800201c8145041c40c1c1c000c00c0ca11041c0166030a44804805062420100c450040711507075408a0403000c20707070b5400616007a1301e2200b180c031030740701d8080c140040e8010008103004c1d500d2001a1005448a8030480c0c004a5240450030161520303140210740040d01c440800c9445504048507000c2c0130110401075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 220286384 1250 220285134 220285139
    0xe070806090a0b0a0b090109051008060112050f0109020c030d06140a08281e1209061d01051602060f040609060804200a080303070f030b040212011802070203070603020406030b040204 80
    0xc2030084c6030300c80c0c1c3c03149820000e10001c843e40101d00301802001c0c001c01e000c50000c0d1900e400b8081c03240450300140000c4500400d00480c01052003018040c8020200e6039080da82000e042d140254401c040e205100e200510550320b080005005901c081c18400b110440c2ca41c00845c103015807001d09401c0b840301034016030302c020409031070708551845140c0c185945440c0700040d42481100e061440e542402ca071018000f10005204a14010b0a4a44070a5817595150f5950700070440c0c01e41e07a00300c1078503524040b0940459142d03214601500c21815113914568031041e199000410784d92011058070485080802c08209254020404000502907030402114130316099490481e11890b9a00b215200c82c2011041c00c800c1c1c407004540c40180c41074000712681ea0600010142c941c4014403018000241400d44d00b40003400c0038001d441788130840495140d0705900b0101101c40c80780100044130f554690a001ca6009030380c0c208001d40003421951401666641820320060039698850314003401580108403c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 220287634 1250 220286384 220286389
    0x13140706030e070e060402070f02030609010207030816020a06380301060515030f0c0403060c0305060f0a080a060e03071a0417040b0a050703270815151003060e070806090a0b 76
    0x12645c003010031134005a841c1030324a0105000d440a810282d0180f00311010402100015402801c1c1503010b500c4256680e5a401c0c902d0706031f079550010107401608126420307000170b070841d0801d03a03611658050850361002141c0822601403071222004100c48080c202c50b2815040a203e42405400261a0014001071455145e0340718403000d41440da800807003000041400300564140c0d07010b0b544c030400a0000354140700c03004015007010f4510920030b8040305064a07807403504c00b810500b1213450030017410703442c1810f455a1005118590404189000800002000628000f60803050348189004110941041d080000d4010a80c2c9001c08184d00104000d100360209807043c1c4a120b0316a00e8103d9440c0e82d581380448440b42c4d81c22280c000c05544240b00e400000c03400816009550581d0200e0780105e0540a0b0720903600d03410303540e685000308100e01c1c221941c01c18a404c851140b550f41004200d1541c0c401400803070640499040c0006044901070115a14004c4491b50300b040040c1d40034442d03104c05900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 220288884 1250 220287634 220287659
    0x306030c010f0e030709091b0810020c010b06040e01060923310509010b010201020f07031103040b04090b0906030a0b07080a0f020d06030b061c030813140706030e07 72
    0x200da50600c600d680c0e120500c41c0c031030110401142030180c1500d91942d5945c00030009003660040886e40a200c1080c3e08440c03000d00000c41b800c0f00c480800401d91000d09282c0b00d0002c1d8800324585021b552500c41e00041d036101d110081c0300901040e040800c1c00c1d0b2400c40010400c400c542c2081c1041070004c08981c9945403c940c030001800411110308039561814210718141403402d01040181c007204030086440c0040e568440c42c429210180203000300031801c8012400c038450f040d0f1102403110140a40000301e44100ca0031980400c81c0400c8910700341d00c074210450a0f812130307400f420041e515108030075810304100ca00150810001d030018009024281d9039200400c00041140c1e0802141030001807803020141c00c54809861298401c540e51805200c851000c1d041074001614412103183c00704e0241d08000f80310410325a491001250401015501110000c42c040d04058000d0100415840407510200740c0248851000005040407840c2040c003405540c101c0c203170209075801448003049010f8441c1c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 220290134 1250 220288884 220288903
    0x2120601031d0604081b1e123105130c02070501140a030c12090c030507050a23040209090114090c04140d0807290112021807020c090c09011103030603 66
    0x44094640c80030058a191484070700706070342d0306e80c403c4800300f618001c014001d02102d81e043e4030a43c1d49034038050031295194403c0c0f0200003807215084044104035649565862a26203171490503240319540e40340011030504019984c041d0721540c50340c20301041a010040000242400c0c00c058051492080465015000ba07031900c03814582c40708905804984a481c0c2d0301a141c240ca034040050030814200b02100c0582404101e0340c920501c20b021510786800d0503c1c10072140701c000c02e000d8044c000e00e600301c4c0280b001c071800d82c2c2043e020300c4601c0880e0765064001d0b0103420507020000c462544182003000c5020080c0c0020a04038080205001c002d200c1d80c1400382150060359041035203600c505d03001c0d015101e0598094851a200070700495881800c08802604403e415a42d02c01a6203d1701c407222400e0034000001c4d400031510340c03410124401d006d132081c3c3c026a180165600700d0002c0c00421088881255180f045441c002140061036801ca581c0d25460440400194114035020340400c0d0360707480781c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 220291384 1250 220290134 220290143
    0xc03070309120f02010b0409230a020d0602190c02030c040e100204151101020906032d0a020c10060f12051e010f0c0e030d1805030102120601031d0604 66
    0x52a514029044245429401024544214580b00e4010045160169400019424000c02c5907462901d4003c1803134072500030303000c030f10001e81000340407040000124030303090030b402181d403200d0140e0740b40040038039103a0140002603074804504008540013108949000140500700c85c101016072000104840901c9090b580019000c002e9002140b40c0b919150f18240401d000041c04100341008800c04040e01400d901c48888100c202a44103003130780120b818080d0030050038000500c10444615071299065002c0c5810001446103440c5203c4518003280d00281031038000030a50441030f010800c1001511480008005490500d40310000e0040c0512441a040220841c600c09000e4148000010503210354030040761030809800c5280030308001800c50725071300d00d44412100464040c5030b140442003c0100a0400d103449008140c9816540032034000103030980480108590301c00748001c000a1154400e0280700d8035250300010150b592183d1103440c8840d4500f58811410000204280c02c05d900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 220292634 1250 220291384 220291387
    0x30c1101050405040203190e190305090604030210021606052a1c02070302180411040905010e030409021305030a02010203160510090f02010f050301080703060e01090515010e0f0f0c 79
    0x9040100e540b40107030340216512610010600506010b4060005a1001815001c2c40400003c111013a00d4040d00c480c0720304105280c049200000b4401e100034030740c1d507034010600e904042d1a6008151108100100e0201507408008a142c0040003c4841c0340146203d240c1286048040024403808208100300c10700c810340705034030310645001c043c04000b64117088448941058104020000c0d41d41c1c03038601c0240d008038100440317a90110b45240c20705100e941c20116524000c0704020500008042c40030342a1041c4d50386890181600304180000e10040c20100300250f210031000e881c2d04402151070b40258440c0c2e008400020045c0d8002c4285e03a0902c09040079404140d01604200c1d0500203038041c59403480f0300c0c0000400401c80f0b86d002008030b40d0f0003030b80c50680c1c89000704415180c0744800e0080928540c4400703400c20010f0780d942c001850b058601c030004203a400056642610b401140210100b040004000612146540301d16446d03102c4c801c000030340e6070390400c186100c045040c081c0103042c10450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 220293884 1250 220292634 220292663
    0x15040b0c010f0e03190507030518010909020d020a0801080304061b0f02041503050c0d11150f040b030414060403120e0a050a1209090626071a180d030c 66
    0x40c20b60222880245145080c00015051601d0940700ea001034034104041070408103503205a4800d9040d900503507850340360365180c000042d408280c10f58010886034104031000001180602d2203001500c2c0e01c0c61180000742c0c86080450001d011075005070060131803540140420000b51f03a200e00038900c500c02c0c0030b0040540d0125030401c11b0118400c07900c041d400c030382800c40c2060156000e4001e241100e028000351131041d03000000b044072101141001034008030f550001c517401c52a04010700c180c440c24401da540c0c500000b40105204580143e401004410b9020041009100d03681120210b84101d06002c1d00041c58280e50152040c0c01d40390342020480d580d404c0c00f001c0307084100a80c01c1503d800004a030308036000c501d00840c0500724292184000358507404002040c1c1114040d00341610400190b1900d581307039440115024502043e6062414415000002104214803903100c1d0700d0f11a01d5500c650b5540040d401d103000c2d40c5070b18003036409061400c6600d000f195201d20b060f1b90071a4094910030300d103117 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 220295134 1250 220293884 220293907
    0x302070f06080f1b0d0614180f150f04090c0e0c040305060109050c0c150a0f090201020c0d020414070206011a0f0304060b151605150105060a08041b0803030a060515040b 74
    0x10010b01c00701480c1ba00001180d41240c1004503104188201d80c0f503810a401d01904105c102416036000703141c007040402080b40c80d070b0f4060911410b444041c0100b0540f0f1410070015013564007911003940c000b0b02e5044140f0100a450b400c90b6882105081814542880c556501d03a561005104848115640d05c1c003141350714040340125409075031500c0480351000c029404100107000240c4404201502d455000c01c2000c00a020b0032803040e80580140400303808400c01d0040c0c209402100301c1e44240e070358459850310b186916050b802140103a006103c19810403240f1440318180240a6034440c00922040302c4404e1003404890b1312591161010424a08030000310f51101c0f6801c40d40680030002203081c1d40864220410f04010b14002c0c0211010441180098500d0090a005107900031404000c118840c0f401442c1c2d50f90003d00c074060b40c1c100c69400703c0d10050f40a0b940e4008080b02d42001050040e00703a0705014200c047e000171141d00080345804802c000c040d21403481144007207031003c6440540c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 220296384 1250 220295134 220295137
    0xf0c31090f02030a06050a060e01031a031509010b011e050c010e0607030c021e0601030b0408040e01030f02101103030a090302070528090606090b0c0f0a0302070f06080f1b 75
    0x6041030300d000d200c00d107640750100001c0d400451342d10002515140000819251450340003040300c006890b0000350342c00500045003c0c0c0310317056104094103454591002c4e29103042050b50f0089003004400e805509003001c04609541d20b080b0014104100180700c01e21000c0d500540c0c403010015801c101d42c0e10640180840d0240042c5809040c1074020a0204041503405400200600180c1d07400d4880c44210402d43c0f1f402e07244103850130a0142d1090005100140c80031014a0300107000307080c1c0f18100f50f610105550701c104260070880707148140304200400c60614000d8100304120a051000c581811400d00c20b0744c0780001050410450f803510100c009040c020b110002c058140988040e646408198088003a000b2800c18151000001c0c0e0b000640c0308003d124540030b682e610742d00c41c2051407400c240300ca084e4020240c48080d6004804105003044030401910a0040c4030750040e10220b440c00566043c5c58070250700c4001030213031708801c0206100300584010750090f103840ca43d811203681143c198490303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 220297634 1250 220296384 220296389
    0x1514070c020f1e0a0f0f0603020f07050105010303030f0501080105090c010e041808091203030f0a0911130f060f03020609041517060f0a0903050720180f0c31 69
    0x1c0f4000ba45040250980c40340c0c5070000f4101510f03c0f0803141d5454030420135990107440b0300c004e2078140000601c5020b00c250007c00c0a81c1050030311600f014615210380382192800c2e402240802e617140510203031902c1d03e01545005004200080299242c100f244603111072803c1410b60411400600f02140e60780c403035000801c4120002043d19007010b0500d441d90096000d28416841200196500301c00708070000100c0e0f1207081001c45819051700d481c01e6100c0908100303c811107400620325030400b0309840b050341c10504943c0b8140d01141840503074544004a0b41c4a4201c01000000c4002c1400540c40b120211400303400142d60000c0e80902c9001e03101e071b042d401501b02d030015004900003480880c40014444e40940300303100040d540354031145001d4040301e001900090100d4024030000c008513007140701901404000c51400c140c80c44006000032002c0a40074000c2044852010500825900c11045c040d440300300c566540703281401103a59000c08540d2130a442440020900c402401c222039411500700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 220298884 1250 220297634 220297639
    0x1508070605070204050f060a030b07020a060509030a120b0a0614372102031504050a02042301090512190807060b0f01080c0d20071514070c020f 63
    0x5040d21180001c149620884050344600d08240104030324000008007603000c3e58005101400c00341c5181d48500081c10002c0400081d0b000320f101520200e035290180340e10820704180919590104004094586440030290a0f050b80c034110141145403244c5520006840043c00e0640f42d50707119600450035849071030040b44042d0b10442e90140140c3c41d00d2104a005c0250114501c000c0406100c00c94041d03800356000b800c00d0f42545c1c2e6014064009500440c0c03c013082075042c004000c070760404141903900c103551000000d60f0001d02000480c05070b800410302c02d403840900d09107240b80e03900003c00c5020700740074040c86032201441c02c400e85241048803c00f400300b01150342262447c10b003056006c0b600482800c3e154141030550030b084031718014484c2082c40b40305171100d51031030721002c90000c60f5412803c4d80b801d020b591034000045211070aa50040a50000c0c040140d54030741a1410084540260601844290401e0107002903107042280e465880186480c090a003070038240002100141141c00300b64 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 220300134 1250 220298884 220298893
    0x1a1b09040f02182809020a051207050408240103030f09030b04060510170d050a0e0909010e01110313030e06040b03100e13050a1103031306030209010305220201031508 73
    0x2003060031040d40007020350504580144d01540c503030541a10194655100b003480b01140034003030100e540d60741c0c00b80011390881d103803090401050507900920350307000b80ca1070004540c001c9820400b6000800840c01001c0440d801d0008000031101a0804002d041c003006050058080c0f01c00d030308a2180c1940c2004582000300ba120504180c204070004001c140c030b030983c600c5220300020540c0d036416001c0141c0304411100500c0c400110100413591034204900000c01c100030200d0301021940c42d031002070f026184000000888a0041c41400d00319490300f111740d039040f9428020801e954000050001e000c0340c05042200e4141e8040c40042c075140f007907030031001d0080408410300c084e4080300b81c82001504c0c801c80300454541c82d03100a044040b8600c0400401951003100101c0018080e14032403100340c4809001ca0381803000e504200c02004801da000307000040d40c085140c600d10b40c0e15000c2c1d2034100c04c840d00c0844030041c40e000007840745224030304080d040c13644808000000c554210000341c020700440c0300740c9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 220301384 1250 220300134 220300147
    0x60d0c06031b0305040f02090411100e0907030504021f0302091e01082a0706090503192a0b1302040f0609060e010803040e04030309060510031a1b09040f02 68
    0x80e00500c62442081c5403000810080d00c0b40b41d0092003145e0203540c208005d082c480020780c0c01c024a000c0020000c640c440107040e15072446403101c4800c07940000b00f5444003002e0a0505050001000c0000c001008050501c0c05000141c1c640828a5040c1103005d001d02140c1822100c0c00d401a00c65100340c1d0350018010014890011318100c6150070b100303000d98074000203803078014980003078144d4140a002c100c850404829444403080c801044050f100f21000f203112286601c0301303400c607086102c145910428021603041c21640c0710340c01010355003503900c00101b2b82038410261324041e0800c92005200401443c0070503401000c100004204990060091000c140d85081000151095129003c4c0b02414070f000495105c0d403114900b8140c600810055080031f1400300d100c1c201c000040c00c154145595807404001040b007034000c0c14030800e03a01007190b1500c1d20750b141075100e08444210000e00750814005003c0a541200c448072910742c00801702e07540340d5410038005002000b4800e0021455803000403203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 220302634 1250 220301384 220301387
    0x12030f070b090708190203010f200c01060506070f0209180607200d0302041a04050612100b0d060302011b1127040b18120405041505040c09030525030803060d0c06 71
    0xc00c9145c6100340c0092100da1548051601a01e809485c841e69a1080035901001c03c00003001a007681065040040381003580c54000c41c1850f44104804e9a00d211856800010341c10710342c1c0d00d543c002a401d49202c43e610101d41e4011b407038140180985041140c90000b12200d1110b941b400307000481031105031042800040c90250096005100d1b4004803035106030181d8240c010842664102e0707101520040c40c1001c481c11740c126510004203d40b9214050600120382040c4800c050a00c03446402d10008080d030a500000d061128401d03098003444030072900d01c200042c0403d10007007003150b0554000c400c05034a004240c03d040702c0d01e0121400c00d00c1070000c000600c448251000d0042d00c03036105080d4104d0f070f060042511000c00d4400c4c0901404108400c100d1400c166103c1e0149401c03e0301c820440e0f50701c0710b00280940c0c04107002c4078000f07000b0f1003051041c46000c0c044581461040c401703144210300d21004100072050b03030b48006041d00001100240b031070744aa2202564190303002e02100ca00c02e8403000c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 220303884 1250 220302634 220302673
    0x403020d1b061410080a021503091e070303090b03061c02030c1201141003020109170a1e020f0f030a020409020d02040207030f080702150a0f11041412030f070b090708 73
    0x144c0c1066002100c3e40098440c0000c204038900540141281800007010001042d0541c00900380d002c0b90702c42c40d04a400b2078804103a000c40000c0542000c0d11100e403941c107000308084a0b940000049480400512400d50b80701180c0c0c10040c2c4c2a0000d0141421050000030700306418000540d40080f00004444041d52040d4403031004107038044120304e0503882d00b0f002800c4002d21400000d01203680a0002d200f17204132040e2000055894604440f130901e599907402c40000a00040c2c1e807013440d021000343d0110700d4440728060940e0b400b615103a10b00e981d140300103581e500152401038021a500c991707a41c1503440d954100ea26850f0081c00c159550401843c000380340c50b409015180001d060301001c9118a84007054031445c01200c40c4400c0141c0c0c40d40d4101310014100303810f5000da0682e86111346803042110b2800341004004c10805108251441c20500042111440d62030b949038204101c0e40c00e45c40205025540302c0b58000c0c2d880340c5913580744030381c041c80d095450304088100d20401a034514507203c0b000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 220305134 1250 220303884 220303891
    0xf010608280f0617010209031213181a030105061302090102010603021c0507090c0c030f020a0f231c0c0219080619050421050f03090615090403020d1b0614 68
    0x44e440c103000031121120600b01e020300d481c22545a00320140401c1c07440c0100f030113081401900d008100d089a9640702d0364040c1000389050b80d009070b0710b800d11048520808003014100c16401c2d4004c1c0000d2600d02c0c0020601c2820030307525115240d011440444a034070035448000078580c0035080d0302101c1c40e0356640b24214200924222403512032580f000c9410302140c001e035102c414803038440501c0045669030950b910400c9490940452007819401c0000c070310041400108103005030b2802e000c0b5000c0d40e113103804603229030340003201540c4036030f41c02d50305c1c1100b070b6052040c0d180c29881d1100c0804401e100040c03240001c41c0180241c150304030340215102c100442d0070782c02101700c07900309404040781c5460720b8203551080303a0261184090b58000c10080d4084201c2d24a056181c1c60124078288042401c0d5a8942050b1000c1481c0d5100508000175445120054000c403d0212001c0e115440c05540c002e5837021400400810000829000060b00d41c4000c074598440d54070040c01d025010100020728004001103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 220306384 1250 220305134 220305149
    0x80a05090a08150105060a08040206030703090b04030c0506010b090310020a0e030f0d020601050a03051e190506090705042007021504030f0b01090204080a1b030605010f06080f010608280f06 83
    0x20f80002401d29000d4112405480c00d40c681d090160b4841c0c0801a0302c0d04000c00c108141500d900c0001c000882400e0700e00c0c41a031103921f4036585580c050800c1490200160003124800c801004803018607500040c080d1440c08440801580c0c0303100084040314014114840c8a8052141a40c2d009200b400030402032001d44840d4202c8090fa030344c80c001c110701c17101b0710b1101a0164108104a02a02140c502021101148901140d00320816600d00c00860900b11009480c0c0d030b080300f41403125210003400180c000b44011a4140700304c0c095070b81d0354200058181560082c01c60000f4104046440c0d2046601e210880840280d894955034281401014504201200c0d203100070000440c0d060070754426603050b215903000400035a591645d0f140d5010404900d034500300000c1500c000000741c0e0301c1c060540600b810500080c5da030b0b841c1c00c90240a02c030b0040d060074514480140140801903000442d5a80300451403264256942075200380c408608050703200c1070078107003460614080580107410402c1103070000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 220307634 1250 220306384 220306423
    0x806090318030607050d20130302030606040203041a040f0c0e1603090b0a0b0109080d052502030d0e0607171e0c060c03040c080307060c110f0a080a05090a08 69
    0x1c5002c240c0c489008403502c001003442400040803051032948010000600021683c140b2480005a0003003030300000940c07030501241800a000710304041c814a508000295000e50031406d09590f06c0380d0400c05800b40404000400c8009010300031041107460714260041d64681c401038403004801245a0301f21500d22000c002d0742090b2504038424070480e0341c40360300811501c0c0c1c1611003d2041c0090203004500d1410000712040100c0d10010501c614840c081c501c1c0c41d0580d0700c1c01442902c00c28103070b094554003600d45d803800604004d0f80340400c01c00c0d804400d51600085501d02107000912501502e8000f07400c40c0f4030429100c0c00d600707505005100300524400545021641c042e1800703094801c00c00200300580000b4007158175016544091600644601441e000350760701d9924217440d61300045020b51f500c507150424280700c40d80044008000341d2092000e800096409001030799145842407009260301400101d40c503410344035205076001c0c8013000f884602c0c0b031903484c14019074824141c4a642c1a0810 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 220308884 1250 220307634 220307677
    0xb122a0702010806011803060b0307050a0803040306050709030f060507031404110f04091a040f1b1802090d0b09010b0a03030801081507021c0c1203090507050604061202031008060903 80
    0x40046000303070805540c01c09820b1f070460340e9103030152440d8000a5010300c1603820204103940c44a0f140005070440800450711145181020f000303680024041c0018415800003c3c0003260a806102c0c203100d8002d0001b003010b0700ca0341b1040b0000c000141c16440f6406040080c04204523815401a001960441300d41507215050301c200000c680350785000074124500803403054480140c070548aa4054081c10400b144a03200e602c0d080f00d042c081100441350303910300d654203200b60414030b000c501044000310b00071403c241002c030204698001200c0080c04106d1404002005000c1c2500b0000398008040e22443c00305a49280291000740c080c0070300d59141c000c442110ba141d07400c08141c18840c83d91940140038400000911461103200c1c0350300c040800582c41400008101d1021076900d41030003659002491080078104503003016441d8000900c600c00c100800c12410303521907400f555002c010b810040e0b6130384403440e40c034800e501d095118402c02c0c010345003000114840403002d001240d904400601d002c85 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 220310134 1250 220308884 220308887
    0x70c080d03050a1116050a050f160b070c090902120d0e01032a050a05040f0e0103050c030a0201080a02090301023001080a02060d0c111618060b122a070201080601 71
    0x140e414103407104ca64000d00641c3ca03d40b000418034900303a03001d002907550044031615004d0034890101100310003980121000c80d40701805c242540020582441c04500b8040c2d15941c03040f800f182c81c42589402501c60111600b596107030002401005a80e204948181c42d071b418000d044180e011f0007076404203240900c8143c694140d501c985c20031100183c0d103002880b80b0b10005031880c1d00140c0401007004014480442c451003140440005403072814a40c134034940c0345240c454074140160b0103050094000055900041c4d0f044010540c0010bc16000583c48044e0500400c2c028010f00d44982c0b1220302080c216a40c00c03603010780c100560703209001c0e444039513a2201902540c8451095000350081801c000c1d00c0300110031540b00e50682c0c803d520300195000c9404d4a1a842c02418030380404040b05810001c11035201612502e02c9000418482841210301c1c01c01c001c80c1c24050300e0704907016441060002005001c884010301101c0c44400b4080c9095202d028140b08582c0080d603089000c07480b100086060783d07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 220311384 1250 220310134 220310141
    0x30a1214090a0308070f0615030210020d0e040e01020c0102180906060a120504021215010509070207080304030f0f0506070801090f02030108030715110a080405150c04060e06070c080d03050a 83
    0x307100203019034030482d203141c0e02c80240340d014410603100c4281801d88000007a425003d2080130300d645150201101d815401000407203811096100155072042641c0c0c0348203500004050844801124000703a050110104a40a441840c0c01d0308102e510001d00e00907010581203005108030010b807903408032941e949051040c644110a540d801003144076021074030300d071503a0700029231040c07029103e1012900007a001510305581c107102080780180304001440181450006647e104125100a0086030300d0944000c1e00d03807107903020107014110052210803c2c040850428844682e00c102280c2142c070344403100801c0f100080c01299140c9003003901040484649001341d81c144d42c1e40c94003441c40c00c0301a9549151100c54000c00c55609a200c02c2c0c030480d4a01da44000c1c100c18182e0f611210418a000c8c49e0a40c10b1100940c1200c414030404014841c0180111050f41d0541e501410300d030440c1c00c10036000036014025454028590703034002c0000b00d42c3e080081907106050480c0d0320140070607160384c90300c0f4054 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 220312634 1250 220311384 220311397
    0x1a0f04150b0c072c0f041b080d141303030c0807120c05010e010219271401080603010608060105120f0a0807060c0e1c0c030203030304080901020706020f1209010e030a1214 75
    0x10014102c04517030328a52040c81250090303c29044801d000200303410880910203240d102c412903402080c18800003d800450001300584c00e03484039807501038401044901040b140c0405401c028008560404102c2800115000a9000007042000401c0403000030014080d48400329880d50030211000c40c034440c14000e65915074040c4502c00185440c2420480d4140d020000000301e01400c1045101c4403588984e079103019140d04407c91030410f04850001d481d192010b40140e000b6031600c10104100b41000c15221305580c000c03940e1103040c001e029052444c1c50301000600c0814085c1200700d4080282c820002c1802c14800c4c1024001d2400b040026119034400c1800f01d07802c00d4000100717203250f49101101d03020711071050031031491054581d000b0a00d56001120121042100040d41c0d0060350780401c0f40800030001c0f807004048a20b812022141c8986925840800116002c90f0001c51a0301502442d0141c2e08098200c400035142810846040381c0030500c0c81c00802d80c800030320042c480d5054112081d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 220313884 1250 220312634 220312709
    0x40b03010611010902090703020a030e06060904030806210c090f0601080402040209190306060807080f0a060f140717090d0c20060705010f1a0f04150b0c07 68
    0x1980c0c80c0100a44415028071800240c40d5610b40c441401a6160102507001c1d41c00c642d00107031103c0203250040e00b29200b107001c08d00d00da8001401c000f0320342c0d650b1082c198081c0d81031a114016032100004900382040d9030800401e007002514905400d00d00c0014191060081200c05801c5a110b80e0848254104160381d901d000a11150008016003000c0d001000304100181030310480110601c41c5030310714000ca8008645043e203881003086400010000c01c8090070450307010308001d07c10107007403c2d0703240303840400200681d440d1418009281c04607800142c0d0a151003142003002c0c0740481004004d2461034000f0b002115000010404c502800140fa51045a03640c4901d0791180c2582c446140042c0100f4050208120039160443d064031103001a00030300d07214900100f004480816a039041e112944100985052001d401349099986c500e4403034002d900039200050322076040340140448a155030440304900200180c4005903c80000d080400ca5100982090400312070391700824000c5030341c0c940c128 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 220315134 1250 220313884 220313887
    0x213171e0a1b1d090d0302120a0f02040306020d020a020706180b0f0409020a170108030307050f07050106051207051212030118090c0b0307180305060711030904050a061802040b 77
    0x40040c40385416031911120195504602c103640e20b8210b01040c0c01c0c01d454074010a580c90a000d00700038104007000710700c49070341000d43c10501c0750303c103850070001d000b0030490406031500034189100d85594120350203103800c03050a5540d035000454803406944808001d02c0103124400300069418458540c003035051003030045000400d89000e100080703d4010720300e601da40ea0700810000514415032302c0107000003020780c1c4079a8080098061180701400c1d0503445000e69400c10801c0220060b070240032030b140140350542051f1541d0761410070314010200754002da9042904030803940307481070300040c03648201d8104503101d01c1000818494161501c60182c1e107401003001c144014844600031850070092844c03001c01c0011044c409842d01c03c0a00d5080e80444581800041030044c0d00340d00070344420fa01810300b41010503240c515901c050741d90034010309840400c40404141c858098050044880c0c4050040040c40a4205005000c004099600c16085010007441100480c01183d009030340444a00d4496a07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 220316384 1250 220315134 220315153
    0x604110a1202130303020604021011070314031306030f0c0201060509070c02030a0803070f030501061e0305070521070e01020d050301050f011b03030b09070c0b060409060213171e 78
    0x1d494034410118038001c616020302c000d0a40c10030782041d0078000c60282d4000e11365810280140709180c10320200c5035040088803d0a407103c2c10000072020101c2e0380c4400d4036980c0313400030b0151900354090040e0035099001e12020004da6658550040c4a8000c8285d800b048081610403042e4221022480384a03040700c0c5403400030390b8440c014001c591106001809071a02c401182d03450000780d030b100311104400301d10340381d0302880d03540d503d48505c0b4090001800e22185446030000d0302d1242c803000c0d8216208040d1200e0000c1c0c1c545101f2010790f41408d011403c040040c82c209565000401400c0314180005010110404c401c0c3d0720000b00d211280c2d402e6181c862469003042e040c4501c2405039880c10f410301145c3d04241000300450701052039024000d030740014039000c1c49410071500102c09000301c010880c100e949c1e5004240f10500c501e400074802c840004501507175140150180c015508001004580c1040000d0f81200c112100415412100103581603402241d41c81e10400d807004100004641c07161440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 220317634 1250 220316384 220316387
    0x5010903140708060c0c0d110c130609021c0b0418060c021905061e0603030426030406051306090f050909010b0604080a0c12030e090c090901030305040e0604110a 71
    0xd81e500303010710a40b8082922110b901c3c3c5000d005666407801448001505405808203112000000d41d95281c907803150b400840e10385940e0031454540e180305888400e1580840c6ca166482701d4010500d019003552580c0307684840151204c8a049071414036030030f0075101006881e05205075405080b0600b5040031070500f9403503420041c40c00300700384825445843e4060011601074003000750701c140304c0d01c010261840c2c02c100da42c1000e0410b026245029040d601889040d03035010007924207844401c140c14440c3c88188131030100340ca00b0004000e60501002801003502135001c070062514183c00a0025285540c43c21300300d440444501c03071181d0080703689400780442d142462480d60400d0301540041003440c4000000303811a4419840032910f50f0048143d80c0804c441c01005800400c507a650350410780c041920050103000764008114171409107440000c03101480d85068560001d405808024651385a1a01030902d601070f005500d0407001c0d149c0007403818a00340c080d5004018082c3d0f11075081c0101e4440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 220318884 1250 220317634 220317653
    0x1005070f110304080102071401140402010f05090102070e07030c02060c030106090302060d0b04061503230708100e01030c060306141315120503071202031e07030c140d0207050a05010903 81
    0x366801d00380810080011400424000b4040150294101c12008054042d43c0e5003114884d1060030244a004810400940c2c1c01c40b00791452112541006a40c03140002c0c0102d0904205810040c0312804a000380b1030551b030306a1101b441d40c0340076000c41d50300d40c071011180a0640024841ca20000e002c015042c00182049000f51034541da00c171a010bc0d10f40c0e012000101034a5032900100151640307035444800c0680c0c14007a00d00780700740c9405100e00d60b000d5002021120302009140b0b106000b0041d000c503e480001c9190032000b000f00c110340003180d5840f490030429810701071103a00002801c02e1808148070034a00801020f0070b10041001d56080303c00d0350110040d03c507815108400b11011a00040d1002d07216141d41c001500c6000610b55071203261800c2c87c250b61500b09040b045500c144550fa01004c8041c4180680283c40c4040030f40700c030110302d011200e172512448000c0009940e07529001030444002244111445a5000e8481c840c1d240c4003404402415403042c1d6000803c1c0160400115042c2c1d10b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 220320134 1250 220318884 220318907
    0x6080a0c061409030a14240103080702030c15040f05061614030d09030203071b08031c090f03020f071a0a1211190801090606050d0b04200c1005070f 65
    0x11030950411050340002820000c41520036150300400a4401d8106e070014840c0440c038070b40140149100f0041403200304901d19050000428400c1f0029030342003596070810a824200b500201010600001e811000d801c03a003051103007200d902411000420b49140c071405071007506004041d03000da034900b19150258401c400c080c0412540c00304002440700c0480900481042c2130080d0011a079076003452402c3c0005081c0c144c002e03006412000030901461f50003008a8842d244ad400160740d51072a010020001080b01d20070040c0b10301c0501c4002c10400d9008a07591031414542d200742d0788a07640e01d100194100d00d2072401c14520580c1040403040c1d0b54021f02440311042c0341140001045011a2a03240350b950084940780c001803240c5d0b10126029134440310041c090b01c1910020701600346414070113082c074010b040603075940e992a042046500d0f100c1e903111620b000b00c1220440e50603020400000c1d0309a110030090030941c01045044445040c140c05042c0c0500c25943d101e52600e0201101201c40d02c6198 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 220321384 1250 220320134 220320167
    0xf030c06020703021020030a02030c0c040203040503040e07030f021206120c060306210604060b03121c0507170a0b010e040b030d0809160b0a030605010f0225050a03140106080a0c06 79
    0x2d0461b030030034400420180c03024401e240c00071903840360200c01540c54988910001c0340f26600400800c400100c020003a20220f8115840c20303603942d110030206601074401c004102515a02c00b08140445e0305102c05403034008d110076a205030f426081c2d044525140c5c2d903005101030b0001400c01c0444d22034100326100920300386480a45415a24280c01401d042070b03001d440648640d5100e03010003840740b4040c0046180b55400b69a0703d403400d000b40081f0030a0389203d80740c0d158025690400160b400b809600401e116401a40c42c10925161016401c001000e0342d0690b54005080d1032015a41802c19106104c00750500400900b04180341e00000c64032140020100400ca0003034040540042d11240d0203007001d00034186a107900c0f01c5021800800319000b0350302c0a41041020040f8001d00c1ea004285501818880d10100c98802c41c2c3c040e4038038000c801644402e070040a440400001c0c07003181c40010481c0c0040400900059079104042ca40d51111514041c101444950040011074064540d01542a600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 220322634 1250 220321384 220321427
    0x6060405031005041e0309060509010e130501080d0c080304020d1b090b0102100501180911120601030c050a0501080c0a090302042a05041802090a05030303010f030c060207030210 78
    0x2544003003410107448401511a990f221024030040000c210444c82000c2600300d0707400015600c0b07440060035000b0902c180014014005094030180c0d10031201e018202d03001508900c1c0000f41c0e0101e07400101004d22070040640504610949424410400018032a070003a21140c155103841c2c0030010310300221802210311401c0490528420100008110020300d640c0c0740014440340e104001a061005941100c0c41c0c036890000140201170161007140c0c1c1c110383e4081c2c0040d501c03d59160051440c0c030034541c0300c2e900c841a0740038101c82480008006060760f200d04500440b0300e07500c0f4144102c0110303500445010404a5000800b800901c1000d0800307002e6501d40403009039940d40104085030b00205101084910926401c07030350410350000952480c0241c80e14a10f003501d000e01100040310090709444031540c00040715040e41c3c0d5030542c03e8026002c010207407950307540e440c182540121600c3c801100d06462181340021510700208a4104403500075101d081c0400e483c1400301c4098411401c031101702c410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 220323741 1107 220322634 220322639
    0x90c02060f04030c1403040b0901140f0421061802010f0809070627081c020303040503040b030402041b0531031712130b131703060604 59
    0x609032421035511303c914901048401d5070110500c070207110104020418664132402821186800d88030070000b01c11100c8940301d240914080c07100c1c032290601c001c21101800407000c005c0c0c41458042080010002e039511310403211700e00406522603180159503011560092020541010541400f2109180c40c0f403519680300c90600803401000f00011a45020059848804005084e080c82c1c0414040c0c0755900540e46074082600c411205456500c0d40a40500100031a80269000750140d07250a04040c00013809500282040760801e685201c04500c280c00c410f07102900001d41e81d01c06545210032084040304400008400d101100e000305589940440701920400312584524070000f85081d60221200500a15110740c400300521004c12040140c0743e022072001c1c44c0702d0748440402c4c0d25450310641032440b08100c010454143c4000312403044a420010310380c0b05400401c00c620789074 = true := by decide +kernel

theorem cover : BRFrame.Cov 220143884 220323741 := by
  have h0 := BRFrame.cov_init 220143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 220143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 220143884 ≤ n) (h2 : n < 220323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
