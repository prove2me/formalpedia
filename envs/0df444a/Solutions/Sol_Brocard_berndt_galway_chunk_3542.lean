-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3542
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:57:58.752531+00:00
-- url     : https://prove2.me/submissions/5045b42b-8888-4fbf-90d3-66785cd52b86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 636870503 ≤ n < 637050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 636871753 1250 636870503 636870511
    0x3050f100b070302191b090506010e090603011b110c010e030d030c050d1401091112061c05100608061e06092e06031104030c090e16121712 61
    0x1128001ca0b003481410f009104003070820941400d82c000704a2140f419540d100d0000c0d26034400030083c0c03d0042043d0990744140352103060107856100804001508010f081c4000815031a415901c40315600d10140d034541c803d80b0f8860858a0f04000e0002c00001c041c108502c15a640e810003124006c0080a60380001d4145d8100f8440d0500282e20b13030a40b50110303990303ca0603860190503410000301007401220100e14034101c4080e14002c1080900042400e80c0b10b20402c100c80100362401d0022036164900207842e2540c5980b0110808039444d215580c031810602042200c5c41696034509080102c0b8506103c0c0580c030450a91102c00c4004080c10400309107070b00605094080c5481c0c500040c0c01f0070410f0942030392218031200c010314290414203000341001e8540110300000382000c5a11600c600038030140d90581e42e02c0010701c00740b982040d00070380040c400e03483e01404500c10300806042041c403860300075010303007103e2108030f042c0d500070300701880c03041c03150b0a48000e40c1208010070780e00104a54401740e00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 636873003 1250 636871753 636871769
    0x210a0f02180433080115030f0201030b06040f12020907020c060703320a11070f0509130602070302070e1f06120e0105011203020f010209371503050f10 66
    0x4005040625034400c03030349000851a4000e0120004508155a494108403188030009002c1424001220001b40f400e901c4000c3c0702400052001e0015030013a0400a00c2c204042c114504181c1d0342c80542450482c144e200a400600303000000f401d506144207040e134030102c00c4c0020001500f442c00801d04620466502a04000c2e0145074901610001a4000814000380303540000f105200000e0700010751003503000a0108403e01070086030142c000c1030080c103c500043d000e4058520702400e0000c1180d006040000d0300380c06400103400100d60f480036140c0a406a401402d60508000c0300540800014010090b541c010170000c0800c0d42212241c0001c0d00c18500e412203410004400a00c06004803414030302e05542041c2c00441d901214040400256000fa800c4031188465114014200e21a40d0000d541004807004070741104004140b05000c14841045041c007042900440b00542c04000d402016441f20351440c40c41c0c00c81d605009294001500c0640c00c00700382802d50120458290b00c0c460302130 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 636874253 1250 636873003 636873011
    0xf0c040308160204110901110708030406050d020c1b01120603080d0207060b0a0905060a090603081b151e1608010302120a0f050a0c0b030903031308210a0f021804 71
    0x52020b10b049803080d41142e02602c14004c0303950401c8032407816008518940e0019400540c407070440c48000031030904486136000076514250030040c040b00d03c0e82c40003941c450003507020840c07682c403c04200001e0082d805111075140d840f800b400b000410301240b100b24822413504101702030000c0b0b180348003120410203010302d0041c1e0311007261030b06002805100200c5940701500b0390000440600c039403c0940b150000315202e55100f80c0310000e00044a0545c0409401e86409111080c201e52104105001d84480a800c03a444562200851100702c90200c83c1c842c0032500303083c804249500300c0c00c0002d401520040031014201031520004241040510010780310b44124036141e540f0740020300002c11f025030090300812a080060600c02d544a065007021074071444107580014103030183e035080c0c074052181040134500c5c644440c0708413002d09404070010f030340b04003041001010541400d41101401040c070000d00b0396602d403c4c520002100c0c4007004014900f03004001290701c07416054440c0701c5011040324005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 636875503 1250 636874253 636874267
    0x1020415081923130c0911090405130b0403090603150b3103210801120807080d0c030506121f050c040302040603052b0801030212161403060f0c040308 66
    0x500703044881d03009000d10700c3e164424460700c1c07203201a600300854001d01856144a94074105881103445400100d00c1000b424058540e451400d60003254000040d89048001d070f00d281c0d15054103803041910b00b00c0129410343c004020054040c00780c4250301c83c2d04074034114854900440700d190380c400c80c59a400d181c0a9803220886a6204c40d0400200d902d540e0300000d02191680303049060110300400400d009100780400c1c031516446820524107941b090f103a06080c50b04035540b6400150000c05040350340c0ca40038007184440c0d0700d40e8410040324803180d44c0c02280c0c1d030400c80c1c00d0100042c1c900602443c03681180010300c0e55012580c00c08410b05680d004002015521904103441c1805950002075029007088000030070b1000009a40d8400400100341c2c624000e400080380d40d10340c030825090008109184010005494041e840003c00c140c80b00941d1200d4092804c000e60500d12500320415914504884240301d0400308a415441030850303152400038101f25a00b4540b80c01a40b00080c500340c80040e0b10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 636876753 1250 636875503 636875531
    0x1f05100b0f0a1202191701050f1201090615141e0f19080601031e1101050c0307240f0e0601090c0c06020d14060f10030c0e12010204150819 61
    0x20400090400f1001c5403204228022004a210703c15900d40000c0c5110603226001101080310f9812510010904030f13541c111001848415940c82240d134049550701c1c141c0310040784103030044500140ca03c18000300321505150034507080a4541c21094054600120729607600381210402c5429003400b1640c0c110808421000520311640e9005c0c2840c080103c42400a084040012800d050324451115099810568046540004006035010301546681103484080c0c0d401078005140305180e00003643e1410226440350242003000066181004140c821034048103030302e510800344200c07802d2100340901e100c1002e2995540700306026230a20255500082c1a05902520002c208107030701c01c1082d034842c00c038140038200400030010810584100203002420b10300d407010301c00c43e0414000300000c1c0c584001e0b50f400c0b4001d0204145603028403101154800300f55a0305061118400760910000d80d0390f40c20305041c100716005041e1054180540d09003444180341c0311440c0c54020040c5014000782c51143d0b8403035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 636878003 1250 636876753 636876767
    0xa091e0503010603150b10050f0708041502060a0f090b2d0a020c100501030302100911060f0d1401033804030203221a0705070302031f05100b0f0a 64
    0x40507501d586096000010401c1035500c3c280719410411040003e03080c10f205100642180c002c02e100041c80410600203440c0f1032101601d100d034050b8141509043e126160702c02004c00303a00400025078444000c00081281900654400d4030345040f041c0005111036403a000d120402a00b291100b05844422060302d0140492086a83d030740d850002c5054200307509504c0085d4011420480035001d150303409501140b9a005140c120303a4150300402d124400041d03654020703c6090022904c100e1601001d0481d5680c0e5805031001c450031440c200c0d52803124004d80804c444c059909141480c40b20300040000c51691400079440b000340c03000b0800a000e012188100508241d64215040d04020090205169000020700454407607414035041d44103c1d84038514042c0c249101b100078000d015100a01941c183c000540040d5102e50300300c81740540c0301d034002800c00b682100070500002d0341c11b039003400280d01070040640014094169602003030401d00004110f12403461291045480045e582020f54803e0300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 636879253 1250 636878003 636878009
    0x1051e030709030308070f05120604151401080a0b0d031b0512091003060810110d0501031103120403050c040207050c1008180610061404120b0106030609020a091e 71
    0x50059524500140080d0055109000a500017a01903000814081c01196032003030461194454900304402d20313020810000c001452281c100b904c40050100c00e80a1359144405855060f25003100c10b0910b80c0010000341c00207040151140c14417000d5140c135119094040211601481d1555514a404400803421000380300c1c01840c1d407007480b500c51440e81c4500003034070340e84104440301e02c540c0140403400c80a036085070040c201141c1241c0c2952030401d07455130110280101c9000b030141010406032031041101d01c244d0081e01d0658117650350608500d408d00c0b962101c1e100310b94000d81042e05586646d541d58451050b0b95000ea5400039a80080c408200160103100200a11903030000e18028001050032000303540700e100e0200ea03101546101080800c205100344e280c104070b003002c1171800314215080c0c0c25006540b14509010400401c244190206407002031b800b668801c035240d4500f100c010100c1380d10768004141d480c4107108441030664040204022103c591401052001c2c514107075907401d0b0f115038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 636880503 1250 636879253 636879307
    0x1b10171302011e0302030f0a052e1d04020a060503101a2709070f08040b0a02040b07061514010e0409050c10090812040e04122001021206060c0c0105 65
    0x10741200f025070f042d00118441c120031040311000e522800464810b840040e14048210410340d001c1c1010021a00c400c00407842c40d48100403400390740c650506c0c8180a105010003403042624040000f90b0410181100c01041d99181072440c509e0407c204c0030030300045c2c0c0a10008050a5021605e075040b91f0001d0300c0c00c0c0c910810842c0070001c0312a044003050443d5000303c44c0140035410000300111f000c0c0400054110454032009a56641d40c2da907074200f541d0050075851070703982c01d01020402c11956400380c103115114401c0080c11040c5541d0218400281d0707405420700c0500008098800d9031f0100142105280c2510089010812071400314140001c021015420015081c002013260341d1102003075049810740f0b0b081e13410b844002d01c1c50b81114402c0d801850503140790075000c0340c00120030607003e40380040300c2e00e491000c144400800320711041a01e002514540c0d0040b480d540124544d2080c260401003c5800c2850415501d455039100c07500d00c0040c41c1071010105081c150308580420807a54a00c1c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 636881753 1250 636880503 636880547
    0x90e010f0e0d1403190509070801090804030314090a120606030813090516170703180305040e061002070504150302060d0504050d0c050a110f031b1017130201 69
    0x541c80440c0d0714011064a000001d408108460b01c0e4186101100e000d10001c403200ba45915091070138030003505014101030510b200710040002c89480a120f6148041d10031030307030180e84501d10300340102004c401e00c0251440303400800003202d49556092340c04049611300c0e00300c0002032000c0d0400038020003041d030014121035000140c0fa00b203a42c0d4214850262078000c00c041020703032030b0f0104280540030514104004110000070444001c1a42c0e5249a4003640928000c034405445d840c10140b00c06003020b00f1400319101040501c00161004101c651020043e1010040440707d150001c0d47c40b0614403880d80590b1355100805900d2a5008900002d9a0050f007d1a13580c04d9030200303000185000c56040d60305004001220707558610070100341020a401038000e2000b840c150316910381c040e0002c1d032540d40c00f4031000450083d5032014000c6108948080400b4060000b0000500c06101200f121000821075000490001103584a0525030003074001708911240c85250700c01a9480c0c440a40030003d030500b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 636883003 1250 636881753 636881771
    0x9010f140108070e0105030a0602130f061e0f0c06020310050604080a0b01081f0b0406090c0305010302030106060f05070b060a0512160b1204031d040204090501030203070f030c090e010f 81
    0x80000640c122640c440071503083d1035851440c9007020201303000f52503154001c0e001c5000480c103d90050001c080c0e140e4184c42d18507540b250f000d0792000c125032000000c19001d540c190300b017694085a003040450a814500324080d04504002c0c440004e58000078111a40400031440e1022204442000340c9806408c9980d01d546484880e03944124068044a02c10b50034000802e29003c0031a0342c0700a00240a000d1840d04042c0100c00c01400281424603002030751600001008a05801615903141c03440d140019036505600615081d42c1c440d40054090010351045000c0d8640c1c09070494100a8009600e91510b0311948001481500c1640c40554001c812030824450f443c00800c0c1f960682901407540c03a100366489400038118010780500c0100c2041c68000a00400c0c02650840412120201100340c440c02c0038000404980007900300b00b809903a01c0005000b14201040205d001e0003001310b00c241007502d0f5a5400b03545000c68040c0300b810903222042d0f0202d10400350003042403406800800e11107161 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 636884253 1250 636883003 636883031
    0x23181b210a0507053a0204030b0603010b040c0507060203100b0f0d0b0a0f0603020d090606080a0302070819021014270d020f150c030c0a17090f0909010f 67
    0x152081d01c0d120703160002041c1d2a0b401081110b40780320300d0040894004001c00c40e9820b24418044c42c40d02c00902000011080e2103840c80100702440c880c010007469030a20409140c2115041001d042c0114581070044090503004030550300302e20b40c485c070090b03600d81d03401c24001030590f5a0340c8507081d04000401c0c503021540409000e0140e40243c02000c00c103c48414003040010311061140c00c440b80e107102818040c1074800c0e0024015515140004103150b01240e588c1390441d402940102c1b2a42c200d001c00104260303050020748000c01400006045d045e280281112154041010007449004041203684c2c5040c01048880d040400b00443c1035290400c0b4148103260100c80c200340c0c18404040b840c03031080d924141071016010b40c0c02a10002c500c9809a003401765840444001201c100d000788102d075a103d00c2000200510622040070300411817180c50084082c0604030840040c005017880b024201c0d80300d00c0c5030200120000c039050f203d291201740a07107004041500803541c00a0402e003001044034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 636885503 1250 636884253 636884317
    0x11209060e0601030501023112080c0f0d1101020301260f0105040c061b0b041509080403050304030b01170606091b0a02062a0d1a060423181b 62
    0x548030681210907905034103813100301110700340d00800c0f00303e40c001d000302d01c2040031041c19a40300e401c860f85801580c0300c00d01d10f010354150330406c103070384000401d40b40281e21a403902ca946510b14029400e45d4100b003030081016102c0c00c3d501c140a04807210800001c141004603009010742d010082025080c6800d0804403801c82d0300440e400714521459150a403956461000201500803080c101c81f6200d5903940b0166540b0703461320b15800d98940110601240c403404c01070005500c0b8000a5580300c5c654640b50103140e0050340b010a848051180e01c0f402c013600030480940c00b6500711a001d1007943c42d00d400c00c01d41d0140d5117842030850000b20f03030040101d4000802502a090314a503e0a189000308030002c0e08400664a110b181707a810302440d01036041a030880c8181054051207070319500040004500d441c0c0040c0c1c08001c0400c82c2e1f13800420070301f01a040c46480c2c1402680d81401c80c9806031405070301d16002030440b1150b05030f054150b100511a030b1040d206144a505076442c11542803a80c2841d8071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 636886753 1250 636885503 636885517
    0x1703181207031e0c170303181e010f18020a09020a05250308090c100305040c24080106020a0b0c0702010c0b01091d010b28080618010b090105011209060e060103050102 73
    0x396002c4c20003c540070071074002001c1c002c003401c0001e40c074540e20480404800455500142010710034003200ca54600c1504044503a03080d45440001007912003112984d05803a4014820486001c0301892400980c88010b042001c0da0300984015940d40b0306201c003182c41c0e10540041000062102d41da140e07082103d032a001110134041c1e92148003039103031032203e59211980c014500c0d51010031038400c03c601d54042c1c0c010a5110740240070705400f00c0c1c0c3e40c100c0c464945040701d20129140b0814005500f001c0c1d040f0307210a014100510060403000101e40e1140c0b00b03584058500420040c010031264110384c4980d0610a0301d036030050060006503981c42405001e001080c0103524001400c50489028140510925491600061503024801541c1c6404902300050784007009500340380e610049051034041011764090b01c031034400044640ca402004500711001495224030402d02d0388010440c6030780c4119804462800b5480005000103107150070b400800c41c0c016000001e001e46400002808019405040340d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 636888003 1250 636886753 636886763
    0x705090106031b1718030702100215011205120d0b10030b0f041a0609130207110112050f010b0a030f3207081306061d011703181207031e 60
    0x80f449081070a46a00c00d0031000f0604440101c4000ba561140b00d1034400b00741c41502c1c042d0f82c034189907600410203190070200c801c8003683c03021800b01c80380c503588054a4018080c201c140c2e6231640042e40d4813621484100f0106594400104052296014546c080f13940c00d0001417100c000f801c1005405000342180c1c144140c0f190a024040945500742070050004551004110550745100542081a04c0d085a03403005d0300042004d030401d1024890b81700404909000362041c1700502001000103000741c2440d049424024106001d004102070b541c00124191540c948a160322003661810460080032a0300c002920141800c00c0192a56001e20310145140007048851203070030390951541e1540001500c0c5400011112000904206544000d241841c1d10400022a03182da0300c2170003030102e1002100e0482d43c0c010031001000441c0c2030182070701461501c0780240d070030a110000ca0700402d0141e410030500030840d0344243d0107e04020b01901001e984d001d030788141100301301d03104200010310300c04c02120 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 636889253 1250 636888003 636888041
    0x10603110f09240414040f0b3105030f030108030d061a030a1d030406050904050603070b04030303090809040609050a0b1c0209100b040b0304141204030201050c12031315090f14070509010603 83
    0x849880310f4618109c14000c1101d60201705942c58140e800d16110700650701400140501c40180d50760030300550003048050000c5480d00e81540c0c2c0130048408503030020650b1a542e59096110b03815000650b1b905c03104440700000e072404195500160140c11900a8080c1c1c000007401041484c0c1100c042d0006e01400e43d001c00c05661940305043e6680c4250040c0d03413101005100c01c10010b486034002c098202c1c4a04140b60800032040080380545072550451315030a919242048900611071050600c14142120b50b144690f551814940d02c00346002000380c081c41c8283c0002e0240294060038030000c01c507000e0025955540d90b8111200c85c1c100341d6040344d804182d2108a8039801001804c0b0780121010692149424035503401511207034001241c1032420300904c007036030341481000740185201d034070500c04401100c40344d49403020043c501c065400c0c000505c1c00e44060041104041c9003000e090b031120b41181440140c1c02c0c910703e80040390780610350110004002007071403a0715400a20201103101e040c05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 636890503 1250 636889253 636889261
    0x3060c120f040302120a03020c0d0c4b0515042a0b07020f041104090b0402120f06031e1629090105070203010603110f09240414040f0b 59
    0x10034034000c02c0e0380150050b8001c141d03114020500b13400504170f41d04941001450150120607143c103118003450301c2c0011a51129802040c803091109009030001e4a07d01a240f002d1600b0042501c11410049001484160790910104404000c146032006420004030752100d00c580400c1c0d180a24100c40466048045080014000c42100c1c880040c1071310080381900c2c00740c108400349510f0341002030143c2c0c2c09451020280f00c0754513988a0405000d00441d03070076035124144a140006d41d0991074800d80624810016000d03102c0707071400c1a5030045007450310401c107520381078002803904124003681c00414010000c02c06c1e4038034001815500020000f45440c8040f03039034640d010002c40070384000d030400d818800d1950f86103030b4541f801003500700c1701410614100300d0f041d00400e08680d11742c0c00c115080c003603d4483c407040d03140c120300e009000c03041200d00c07618914008043e4074503a13100f2a208072103d03540c81032080d116510768000f080d10f000c070066000403920701070501c001030300b8030340c02c0656a0303080b248045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 636891753 1250 636890503 636890521
    0x30103051509070e10090906060f0b09010503013c05011d010e0907110d0c050106090b1e0604050d030519020f1509030405060304080a0201060603020304021503100503060c12 76
    0xc0303882405802c01a181032403030900d03112103c00005100c140e13040160132006c107030081c1a12507408928004c20f0000358450501c0140c07980c01c1402d4101500d5401c05012030084d13680c1c0001143d05503401d000c140120940450b14101000c0c1a81840d00b0745d0448001c1c982004601d4001c141040f2202680d881713040c00401c03d100400b400c0d118640074009501c80c020b855590600d80601c07070304040c0e913107001840030300c10207826401c1644944500c0c00180c00c0e0341480c824807000340540f0024080c042e0b000c112060200340018444000c5108446410740c2c00e00742c522882c0d96207829100200000b828084a403a4a450000c0040d801402b01d030400c3c0c022820300c400c84520003c0d200c1d8040c0c140b00014146000c0c4035500443c2c03904010441642803004100c04652604c0d01d078080c0d40640c1c80f80c0c02d00c1c3c0d2950300040010b800e41c0e01a8101c1010144144200b0000da0350b00d4043c03074800d000c1e0045941c1e070794a4003101c04803c030506401942e054850701e0180810020a400248141d40d00c003000580c20b0307182d01600d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 636893003 1250 636891753 636891793
    0xc0504020304021c03140c0109030809060f070804030509100e0418170705070f03050309031c230903062401020f03070212150a05041205090d0b071209060203010305 72
    0x8082e400001031131160388000d003541c5040d40018060304003200c2c5200c01103e84201540218503845042c1d440760b080760101a080303002e040c0c210802501520f9036150450048114050092100c010022104085004e16000e80c04440c08460054070501010307070300c148050704e85041c1a60b2903000c0e500c0c04a41c4040b0b0b840c2000c0f0200381c0360344a009900c054803802c040a640e6008000309980d24025044000303030051001281d00c0040d0f200703402464540b651181003608118410b0764030900d40107105603c501c1c460f440300a89402d44052007001101445984070b0005034086c40c0c1416030076102c0d6505021024501a0041c2c0e40082002c1217580880080b000482c0c440b1030034851017040e940140007460040c0340c117501405600c50203000b1140c2805503912106568441912140f401e165940280014010302c6c0344880c50050703280c02c101d0b281022007400314444210040300502006111030201d00030900c9805020a940d004010900c05084603040030300007980300b0f20080300c580c0300388030f5002450000048 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 636894253 1250 636893003 636893011
    0x160506070b0a0c03141e13050703082a010f0b040218040f0902280e2505090406030507080601051005120405030912011b3b04090b040c05040203 63
    0x290090650702c848840310090048007040c0700c1455155103c6021000c024120503114925200840c541c0742202da0740c440848101030003031005210b044840c403022481c00178900085980c04031a840e910f043c4880c2003080b032a000c481981c7c3c008020441c1016007001504150305c0c040c48100c003000042169001c10040f48180412113440c00c044804465192606e40d12010740201c1d022008942d0041550010340a044082c00148a1071071807075540545100144800028001406910815050441000075401c944d000e040c0a19101e0030b6100c40180c2c4600184c40070b116002e030040c000c03a82c4a141a60b00d91145015034442e0344105000050f0a1a1003c0c0d081a2510320303460b40c51500c07880d8841182c001c00010015202c81c4010041030b049900e40d4a046500030f00d044000155100943c010703034a8400112101100f0802d90702c1c82c41954022011008041e4140910f41e80c070085888185030b40c40460aa14031980300d480c01c003e0a09205144200911842c420340103c40303000e45840c1088102e0100f0342d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 636895503 1250 636894253 636894263
    0x605040f0e2d10140904080c010e06090304080610141005040f0f0e0708010e060607030207150807020d08041509020d14010e120c1c090b0a0216050607 66
    0xc003007001c40032100705690801003001403440c800c04601c01140b4075020000c0000071030551881040080403d6103a140d002c0d01e50300384841d22030404e4074001003041c00e001e08094a440f82c0012001d0007540c1c03d40c800e0120b10601025503500b071400c0d040c241d88942052080c81c88078040c2c0c0d00041d01c8031540200720800c0c1c0700c0d5041081c544003020341c2440341c0700d003a4605401c18800c0c100030100c0d840126040e000002c081c5664070703c41080c141002c94207600d4003c0c0c4020301b8003040000510070100c0701904030754808003c0d554036460303466506007249131503070503444034040b80450036200987c07561002e8000c0c450041c503021901500300340354044404850444025080030180300e1100340b52411600078264070341c0010017030000005141c035806080340700741803024016951a00114400d03081480400304441501c42000c3c1001035400855498034000c4031441c075541c0826000b410518001c4035001c000d010742481d0300e91102e04c2d900000c0d42e0740710444491000b511981000043c0c9140035011100c40030f503c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 636896753 1250 636895503 636895529
    0x15100f02010c052505072103030c030b0d02040b0a0e01030501020d05070207080705130b12070e1003150c05040305190605060916030506011b051005100803030403111c0806010207060504 81
    0x40c0c4c5030011a140907460403581c2d40110705000070707040780c01000c1e000c2c5d4203040007120304014102d140250071215070360454001c0c0750915004440c075683e0f41f42c61241d140e8050f1400314a42c07091100007900007050b50000202d004c0201c1c00401806015030140c10410741c1c1140410094403009400c1c2c0c0d84580c28421307001158000c880c01d100320709000000381d1403214020804100158040e0028080c40e15980c0440020741c0480740170420007070800f40780e030781110b00050072050203402d41d15030390b6500c0e902a05141029490b403410400c4184508112802548c108080d03034800d251400810403426050842901d0350f504240100e0803518049054601625805040c00c102c4400c2c0f41042d009450014205414441500c2d52807134140644031a45d02d245100d8400f404c0c0c2c4d11070b005001c804035180580401c080d44e403c2e07142030041c250008122038103d50141005a03803403d407888200c1c905400301c0c58060500711074001c600e040ad500308007101d000e51826001e651065031160b00440301406240300d0340c0300034003076 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 636898003 1250 636896753 636896797
    0x1030507090213050a03150c0908030f070206042711121302010c02101709010207030c0b040602160606050f0102011407032f041a090102030403030815100f02010c05 72
    0x7907900034540740780c503981c0303205601d80d545000500f000c5450340191841d40f001300e00900114020701c50b40b0f004031003a041c0341864038203043c08103a41c1d00030070aa50464000000e130300015980d41c0c5058900030425404850100e1154042905100e402840d80988460402001818941410042c0c0c2c00d0700c00351460803012555403da601c041c404644409905000b0681e02410260301c40ca001c402421286484840300351003a0f110805e001500104202c803507074810311210002950000701c4603007160300510519403944403424400000d204903400d20340c084801014150400415030401c1044a101b202c401012100032401a409d80b0a00c0c8540c805401040000071016400390344101c1c0c0c00b02186511f003581038071011a60000f400ca400005681101c0030904105a2444400f21100b0355001e40e10903081c2018440041d41d80d01983c080101488041c000142103050900100c041d070010050130701500c0048414040d020f0318401170717034100550800118801450041c021140702c28014824510500d032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 636899253 1250 636898003 636898019
    0x12d050702060c07020d06090516210215041502070e0105010c17030c090405130c060903150c050d0c08091902030309130b060318100c02061b040b0c0309130501030507 73
    0x44030304d40c2280d002500c0e840c1100861924440d43c0009442a001488044404003102140404560261042c4d00500c15648201405040000c60300b03a0305a4036500380641e4080e100155000b5a040855120b03c02e02e6200c46a681c0040c501045407294001240c150340c0324001114003800500000c2c00f1041c0c080d80015102c92440300131a070001d100c210850409582c14001400e580c002d80704038001294030030201d000c0c001c4076036101c1c0062140307042290095183da907900364001c41503101c01d108542e4500c90040a140038604032168826443d008114244051501803c2d80b01c06440040c001d100d4140d100300d021018038881c240041c0c000b00258140300420003040080f04045d81600d5400b038540c0240051034039180041c50060045e402c0a45251180200300c900d060381d450f0340bc1c43d1403400c00c4000c8500e6078010072202d8009003d00c400030511103910011089a2180307600c410b01d6010002240d80d04d000e400300c05045c080c481103a040d00342c07000c119000d4054800030300020780550050b0804200e019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 636900503 1250 636899253 636899257
    0x101505090c130e01060203190201180b010801060603020304030c0f02150f031009051314010b0d050d020c06070b01030209041a09010c2606060a030b0d0b011e08120901020708012d050702060c 83
    0x40c12910010030a1840d0301c210942441d09102f040f03418140725001031095483c20b001d4000130700010b1808504600e001d03100240100751002020f00030340c103103040c91820354881c56404041480e500082d0ba40c0c1e48000d000c6030049900c01c40300074140300000705021618900c140100e6000340101c072a1043c04490359200d01501410a08581e50f1540d65001601e403107803251666071080b140180042d001403014401c0190803d0001d10100d44205010032100f000070759040c102605594040e5000324150b540c5103050084010841c0c0c0704034559090b00c0401c007846105400030308402c005507035040d080e03003600401d643d60f003501200440940d20910000400c0b80c20104080c01e4241d84620b40402d03c051948082104081d13030a4081d174510383c243c1c00501559005801880a0341000450041c0349840d001e202519811145680c2c00c2c000800180c0108503842001100040c09022000300a0401c3e90760200078020b0030303403242a41286c00d00c028220340078801d100701351265a00c0d4018200e6640d0b40c1840003613070b07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 636901753 1250 636900503 636900547
    0x60d170d06080a030302070510050103030516030c0515060a0f0e040303020c070b04090f06060503060d14010b0613030308010f0b0405090703060b07050d120905101505090c130e01060203 81
    0x9640d660200081c42c1604000c0926200d0080e2170040c0d5502c41414401c2c00e005100c001911440d082900400010b94130108580070103d241c140070403141c1c800d103030031078200b001200040c117213225030030002030107107911041d20b4024201241c0940c030f103d546502300307101c09919100b060011240c8200080100c0c1c0a5001010000e07084401d4414440d210b090849003600240c0008410036a81c00010341d4005103440b9880c060b1072242042425841d0035000180c21480800001f0604c00304200525202c80094011051a1200519490700c8440050b400d0400340703074611096000524281c0000f0303040b001e000f10203080d0f60640300031a00e0603040c2414009045006030144040541e1755a00060300d00e80100170340100ca105030050203a80f4940030f0024440c8102a0080d00c04a02d003c0301c80c2c0000f000001c0c241c140321003140c40402e04034850b00d2031080045440d405950008800000c00101003020002401614072445641ea40340703032105070080700b8100034002c4102691042000450f90f5060f0902400c1c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 636903003 1250 636901753 636901777
    0x305160f05220216020d05010c0806061c0906060906120b0c09030a260301090510052b020402090306070519031404110d06020f1c0504080a050c010f02040b070308060d17 74
    0x20784001c41d07021601c1e010344000181e07610396681109c191b0142c0d1044900b50001c4040741c545040c0400601c5038040301490354043d0360b070306a590304c8400c01c005041d04020003d12011008003d15940c07004c2c8813038500c0160300c00310b5808404200051190f0300700402d40d10300c910007400900034517001c0d80d22002d460f40804024480c00e450656000c0c100030082d40190b010303241a075400301301410f10702e182250300c0304c503900894800e103c1150b107444207143d0703100c01c1c01d00fa1450603c1254050041c0c000725000b403081c2d038261754150140d4001c2000c12a00040100002c0386c00d40701d880f61030180c60030300300c003101e1015641e801003400d040040b4012130310442c4501c1950100520300d400c400d81c550b0b40d80c002c80e0700203440381801480110703480740000d400301c4429000064100c414811460280e5038201e240c403511004900740030000c603c2036074035002580b0004100d007000c1011507031103458018a10075500b04900480002c1e41d4a80019a50305102c00b405181035070204804040c00c000074800d610740e030440400000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 636904253 1250 636903003 636903037
    0x5060d09080714010e120d110903030412021005030c030408070203012301080705030313090924020d1119050c0a0f08132907030302040305160f052202 66
    0x40401c80440040c6041407181c010b8400b080c4504400034255203441c5144c01c819003007940b0140842c44020201c8224071140c00c0d00240200c24100035140301d005114203260940700c00318001c944040034004420300c0d240204ca4201440c14088812102e41c44101c40c0384182c1e0b1030038001f180004204001404a10b840140085441c1c0007031b5056050b00104680b260a00305207100040010725014040030000d000d06030301070b6182c56070016000d504586244070f070786210303951002c0010038449410b2040c0c400350071104041c003401740c1d4112107002940003008810540c07854440341402200c0d82c14111005501003800012420344020b4040d9a160051115081903014091450001607140d4a0003885584035000e61515503402607a641581981504041768089880d00102c445a00341c82c40440c82c840b803660440d5a0f14030f2450110041d00466000500303601c60b00710b20011480b1840200e0050391200c10048140719610010400007600107a4000c85180300c01c0010940b2070b0741c58005003410b0803844002c407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 636905503 1250 636904253 636904271
    0x100f0605130306090620070308010515070b0907061b020310200a0206011505091503040501110d0506010e0109050a05011b0203070b0d051e0f0405011b050a030e030f0405060d 76
    0x90a44804d01000c84075550b0ba04280340b142080c4415070010480440b4807142406129030b800341080c42e041c0035152003001c5030381d0100001c03070f11607044414890380b00da400015800c00009443d0707201c1550007064046009810907200c50740e60700c5405040d1a4000307000b0b0401c0d0711103180020052403200294200300c5500d08244810060b003500620360451075a00401c00c0d50f01d031a146640401e44102034004101c030400410240d660340240b90102420f10850050f501d444902d080341c01410301004c042955000411901c881c0e254652003580b02d408280c949a41c0510440b00440301c51020340580c6622052505040c1300e15486402420004100842c20843d00c01c03464000900d030074069401118200c0d40001ca85124128501546401c501c900143d59020f0b20a000e03140c00300c400051101901110400000d0207200e025003000f40200360b070400c20b0a80580e80d40c402880d5500c108044408641405010110709100008031210028a022428100383c00e2104200352580b003492004007181c0c03555401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 636906753 1250 636905503 636905513
    0x6060316050a0c051b0913052d0706031a1203030703090c1d010f12020603040b19061509061701060c03120510181406010807031806020a08100f06051303 67
    0x1400001c6643e14034580e0711192010000c0030740b4004c140b0340c3e1f000760f0301e0582c1c03001507400501d0410b0b600d03100455031a10320a105240081c2c14071049410018070030103100081d169010781c0554414403000e10115001d0340488103104841c0e80714a81d40752603500400024409038481c0d402185c1c000d100f02d481c0141213980c0c007030134000c000d00303a1f600390725440c2da400c01001540b810707035a000c0c002c10040400030502c070781c2900060390a01009102034000410800040c07441120150405101c02c907141040100030b46440c0c02d0100801c00407120703004260341b0600459658080c0d01a85160440c02014000903070820000321000e6001e0403040341845031000c0d040903001c180e405044d100e200452003044140f440c2080c2003d0303000ca0f140a4400091138000c04054120038201d20301e030700c00c6082c02d15081d15118002e00303c1c0100200914031b2000601d8400780c0041103a80e400401608810782c0d43c4400e9901c402c401090f121f044c40c0b141004032901ea03e41000038500880150a020600303520701d00040d650303a125 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 636908003 1250 636906753 636906763
    0xf0f06031501110f0c010503060d140706020c1813020613080d2303040303090c05030a0b04020301060f080304060305071403070509031b010c08030925080606060316050a0c05 76
    0x500700710704a00040c800125640481e034203010100c41d400925009601441140d15a9105a4420b0405c01c00100180039038403140c0481349201e81c415004010b84961041b550b44800c040e006510040c06044a14140c40c40d00301041e8082c906204002c3d401c0e5240c07107208044000c01e0f072030f040780c01480c00c0c042070303a035007041200c1000101095005001da610340000001e000101030035082d84003440390b00c2002c0550030a00240c0b41d020360b15040000d41e621a9007014400403803541e1086074144034004011042080b0a11440c1c0624800d9000344050341d158130300201120038600911509520a020400847e4800c2d08038a400c01180e04101e4545106d40414440c2a8411140c040100700d000130107a416040c200515001410440c91000c030441d11480000c002002d407143c0a00001008408143d144105001401c588a692100180d041d154039489031040005445075100300d02620380010940e0400c1c00840b03100d0803260f10308030402d041140c4160344079005240b080c0100075124841200090301080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 636909253 1250 636908003 636908011
    0x4020312040f0f0f0e2703030109020a090803091c0f05070e04050d030e070b0a0540030308060d030e18011e031707030203070b1f050418020f0f0603 65
    0x654412082d00b44450910100083d500c80c0c14075142c4c0d030404200300303180c186000c0d80040301060305040340c16001590034080c0e1160005d0701054003000000280d40001070740103014000c00ca80351b901c409a5180c9a5070388134010700403c10307004155444d19188081141441a191030f00ca02584c610345c0120b901c0d0240b030098103401054804040c0018401444002c018500c0902502d144c1408030207989200152184650302c0b17002c80310320300410400c84080c06101035a4000b0344015429204103d20209000f41000c403143c101e45401c2544021541070400c1000c40c82a66012b0f1282c2829484500600c004040c43e0a003e808015030041003030b80c01c0d41c3e0140307030345001820481c01100c294100a0402c4032440043e803000741c8420942010070002c3e4041e01c00c441c0c102042c00c07240d40c5515050400380d0862240010007001000000700b0001010190551a42d884850522200d802e0b520350b03082c0012580c1844242201c0100f0440394001454083d240601c00c03500980181107250b041c1e80031691540040d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 636910503 1250 636909253 636909269
    0x9040305030c07080c100b0402090a0b0d06170717030304050606010815042a020a020102060103140114040501020c0c0f010e1207181b14040611010605280e011503050402031204 77
    0x400e604a006425001e0741f0103030403040340c0c210300d002c1d004800200d66090038030079140041c4010401c05c4010540368030542c01080840c2d194144a910341c000c59444103410302421f0008106c98030201c1e2060710000c103492059034454010001a1034110064480384e40081030590074000c0b64180b900b040d01ca6004500c01040d904240c0404030710300705807034140e40002c0c02003102103500460462002d41e0b400503141e03044941003103c41e00301e001e0046da640e0141101c1c50000920026aa003480100041580180302e141541001c0e28030140c1d00004108081000071807550000d00c0120900100b85408060781d440c203413000c42110b030025951911040c110081c03201c0da04547e9a20000003940c0903240c1400c05410017140303020008030100340000007690240340076040421400b0070420b10b1503002548030102403d4000c01d00222030550380e0206000c0c0c3da103414249410240088001402941d0f694828180c49800110100d40b00c801d4904500a2500400590307140c0b150b4050203d9680100009001500c0c0c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 636911753 1250 636910503 636910513
    0x20607051c02070c2303032502031c050a030e1b0f0102011407050d0b060a0203120a06080303010e0106030c0c0c050d03140d06060801120f03200601061806020c09040305030c07080c 79
    0x13144001d101c5d220f000010600a80080101504140380c0350007001c81c609000b44840d003040c8260012a02d040c05244e110380055003064414551a90040b002c0c24800d0101d54040c094030703011030300181e01d51014030300c2204050100980c1020514183c1d14404a80e4410300c00001e40305140e6490b0381c501d4105440070400315400281035400500c00d03020708805200c081d2881d5250a0310004001c0d601d10a041c440e10507071065002040b90007095421002c0100740c903d007126165611607099807590174080c442c010119180603108290203019055a03008250450490600c20303140c00117101040300d0558003101080003164100040340701050103003070003a0501da00054410308110010300b04080607001002150134001d00700380000c000181b2036102a0f407510740a9a680007500c614282d6080342101e0a14a0140070004503600b9400011203c1040003404070b09180b0b0355810050744c681c18550403081e0400d00c054000ba010038000d40055801403480028145025440c1d154a030a0b90811900c501907900a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 636913003 1250 636911753 636911789
    0x70609050a05010c051207140d020325020907050c0705030106180509070e150103110c0d090512120c0f0d021c03051e18010f1407020607051c02070c 65
    0x410045403019003002c0c00c0500d20138103aa202d4a80d41c0e4181c001c40e02c1d40003000503031681003140282d1006100781240040302d80708404401e000c0c1d04c1c0d800c003003420070b2102841200040d0901c1a005205046900038018a4203900d9500003100c0e607030f001d00c285810621840c00f0014440d1400d10651009003840b141c031080e9a505134040c0d1042c0c51000d400c4030440d41c00000180450000605101c2e003007030a8071402c2001002940059001d044560502000716002084201101c0001304d4102c24612003650b0b02420142c07a01c040081d40041280751400c0b40d03000300c4096040340d80c0c0100400403803c40208640000100c42d803100d00e4441001f0080005030403500c2450182141c071160205581c00d5410140158039206611040b629440c194144407040e941c070204003406480901402c034000320b40024044415034110607809418801c0183c01ca004000c03000514092000c140c0340d0103200c0d02d5551074941032011302d40f204903d507ea038100d144d065007000050005070754181918010598280c07600003910f2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 636914253 1250 636913003 636913009
    0xb06071b051206340e0112050103151413060509070803070f030912110d241d01181b0504060e01080d0306080c19091a031b010e090603010e07060905 65
    0x4032188001041503140c51070b0802d40b0540700150401d8004c1d903d0400c0f68802003a0040b24240c1a4a0746003655030701d44400881406002c0310b9072a40444030311000c1c080c900c2030310f00813410440300f1203400d0110392003064403400254058000c590010210411105403a4640701d0b10341c215840910100c1e120700c1030524010416401415001c02003c8541e8410314520194450460403001c148105124821401801040109510300d40d60090142684000c0c88049410031400a00103020f011303014054211415054100500414050305144001134105030480e03607850f01020710300c409000c030390660180049425145d034841c031001480100382d4601c1651518052902b000c0203888018201400c041083c490741e080050050900403050303800c0383c110041001845540c4010350402e42c002c50410040110380042c02c910081920070450a40340031580c240d80020340c600c055031410f4082050000710441d02e01c1d1400116500030806000403078940840e0f00c2450805d070968202c0c00104071188000d00c5241 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 636915503 1250 636914253 636914281
    0x10b0712021506040207032001020a1d212a040b030c0a0b16080c0f010c080f190209030607030501150527030703020a0e0106030b040b06071b051206 65
    0x2650394000b030284480840860007055500034a8280180d800250070410140300e114400300781c840c813010380c00c0001030003440c0e20b000c0d43c8081d00c020000380c40c0900c0341c1c440041401c0a2402c0000017022140d1521003107148015144601a070a840350040300044c940f4842e5136650880302c0400300c241300c10420600c0003000202e50050403000c0c025802a00032011075140d08098005851b14001d00a40b9014040813507034140c4501c040c0280040c46c04101254070240002d1500381404084c0028002008013070400c1705d101804552007002115842c021031040c65502c080750910088900e00940340c0715029004c40d140070380960300e0f80b00195850300108414010103d43c80b01d200082c0c64000d00e400140f88482d0700300510340642c00704c0540514410483e40e0b9003000008020b5038050702c9030a40c03a07134030600c803803c800e0240300d0300000ca410f2180d600c8007490f0903c0349803104100103200a041c0246034685407480c0340c02070f4560b072100c141c2080200325a42c80c01e4032040c03410f01007801040c0703038503084c1c51400c142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 636916753 1250 636915503 636915533
    0x213171b090f1008100905100c0203120c0918061003021602011808151006051606020d0f060906180605010e010c0606030b0c030114030f12130e010b07 66
    0x244440120051560307403201091038000a01d002c0028003900ca000c0c0d00c65180240307521403605031003180c800c482e200c40c29820202004e40510152852a40710740b4090003550780313807004580140c1040020480c11078809041da03421181c1280900e0a00d140d02010620300c0403401c621440c86c0038013104022041c03410440d84070b20740640349025828006005011017040c00c61480090502c103c249000040003646005003005000180881c2c2c0c40f0040100701d041d040b8001d84440c51000c10380c003000324600c0e00840480c0d100c901500c00804940e42d41d41c440b44003e402c0450140c0c0c0950b01c440305c03420281da160041e80054000884005170551600c402c051003890500840c83c0c0c10340c104981007105a230071118845c211f103000c3c00d18a900b403083d0304d0420700402c401c0d0030003040c01d1198000e1052030a072130b401840c103a030a000d07880e540c0c84c0009010144e03500460000c2d070000b54405401c540d40c3d180803d0140c0030702a15500855425030b1190040320b001c0b2000d070017031802501b011904109000c0380168140705 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 636918003 1250 636916753 636916783
    0x3010c0905130c0e0904060506190f0611010b0a0923010b030103080901050c0312010609050d050706110a0c080d03150e06010c0f0f0308070305070e030a02040e01021317 74
    0xc80c0c0c9880041500c140140302401401650782c010090401e010381e1805034801401081a811031401e481c0210007440d003503407038a008001003c902d81f00c41010180c62003c0d21622020101a60319110007160a4074100da4900309070b548035000061a41c035020004409480400300219400000482200c81689001854020012104010414401030504481c1540c2d00b100355117555003000700050b103081c031030130000c0c803a98407002401d1115856880d94080c1a2100b6a6880380c44607078075020480303018020080a841a086580104056030007600e03901204001c282c19212541295241c0c19154125540004034507040301c1851440e05906100314071807a10584000080c1c603003401048600e280d002801c5c079043c440000700312424000c00303241e0116019449070001c0480380071454001d101620a03252500481d0514000c201e100e801031307003031040010011340106002012502000050b000c91441031480b954200b044c9030300b1020010700c09002d8983c0e6101e020049042c201d8103481c000c416528410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 636919253 1250 636918003 636918017
    0x2b0f0b060a0b0f0c0a2004050115020615030f070906080705010c050607030b010903080703030b15031b13080102220902030c0f091504150905030a081603030b0406060c0203010c 77
    0x700b240c1101080d10f18082506010310b4803036007902c8040389004504c4101034400c000d0150700c9240001408100580d00e10160703014401e0b42d03a6689002207900e425496000903800c5000094840700348000040302081c1b0017401c0f140c2c441d030b038020308d0750a002c02030300031460340d50300c1d140203203c011420481140101002c1c40d107000d00800c9500c820703449110251400742003603156003a990b0700384e11811609024580094400d641d900d46031402030001c00c00340d40700301e000d03001c0e076070384006110580030682e0701c122002c0880c42859840d0303640c4000d8503400380d01200c40030b00410b500070981132000d1015002c500780c3d1092800e0070044910140141135426440449028010420441d0305650710058a41d21303401c0d046159181d491510014992201c2c401d11024030348400b00f400160241107070035002c10b0030403984621008503103035400e05884000354100680041820000500d42403a12905045c045009203800250480c00384005800e851044c1e00c03000c00184000440025480c0030320030070b0821805400d20075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 636920503 1250 636919253 636919259
    0x7050a05060703050d020d020f041404050903041701091a0907290d090501050f07110102161e050a031e0203130308090406050405010e042603062b0f0b060a 68
    0x140407485030110080400c200400c0200c603005d51501600d22100b04c0d42c41c155150003080c0c0040d18550810301c12500d440c48807021141080c1420b200e00d85c0a21200400740d03241a041842c1c16560f8194080001030319940d440803e8085003005e034924101d05d103407000b84059824800480391602c80650410004880c1081c540a14024680b00c070f207072155000242c0c1a01c800a039110040100310004015107a542040c04100c12000b1821001c1c2c40f40c0b040d0780381c48003070311a402c103d1800c0703001d042142c00a54410740c0300100410b10001c030b030001400406074015000840c0703590305400d200000c401107000c01c088030310910710714540c02c0401c40c46030000c3c4000c60510545500d12034104aa910000e0080b00000584605648803034000402070840503001f4801075941e100c00030070641c0210b906482c80b101c1d040d400710a18800c091914200e540104060341141c5801c07080041340c00005000c139a0707600e2644401212140c01c0403005034061300800f00100241018240425400d000030141c51141883c080c040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 636921753 1250 636920503 636920509
    0x20d020d1d0a030b0a0b0a08161221020102070b130f151113051206010509220c0306021305040519020c0f070b180607111905060f0c07050a05 62
    0x2036980e209080740610904400c0e00d0202e4080142d50b00040c1c9941640420045050350700d0f002264a40000c0d90502e401c16034800c0d001d62180c100516000c050340c0c0005040000780d101c1b10101c54210b00403280205000c200d00644084510482c8103a40542d4004c03801c4401c0c02440814140d010415059004a6941c269260140c889400328001d100008092030848200c03e140d0000488407166041103a5a24040030b0440c1040c8181c8202c030300c507502c08410460441030106825040781c0c40507010360b0307032520b5151090000c214800880040680c00c00644e50104d0210540c56000b540a100016992080101d0b04541c4c0c01a940015000328280018480e00c02c018070300d03104d9041640d8800607180ea010301c130030718103140c02050f2010143c800c074000442c0310242400103105403210411400c42015155061240d24010900042c0c003810f045100d00c1d07100c2c20102d80c40c95092050700d0b0142141d94862000030303215003046200c00b40303101000c6a01c032481c0004020500182c9411951015428500000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 636923003 1250 636921753 636921767
    0xf1317132d030816050a0507080c0307050a06020606010c03050d0f020703180302060f09011101230a0c050a030b0f151308060411041508060a020a030501170d0e220c020d020d 76
    0xa9050090419000801400014080300c000f440d03021054480341580c488109c1c5c4e580e13600030301e5240f09019806001a60703103400c0301c500c0102d0b152500a82081e0b0b0f01c0800650348800b48400c00d5040c40f0041000c2a8040c440780310740e04078022403da006848100d28100148102c00101c0c03c0c60000d910741e00140003507594102600d0b001d0200e441699560000d260040721017903d1804005203640c00c001400d11029003011011503101401c0c5030000d00303580d440d422203082da0001c60b030301c101080f000c0103030206407403280e0850510700710054000000e00b99240d02180a111140084c0180481c0205651080d1036003050210020014040200424105a240c042c140c0640c0e244441c41203030b4600c000041400d441226000602c005400e460007403034a00b42c024080e5205140c00c6002900d0140081000100444004d03500c22514000700450b0b41c9418090f50341c05055000700354010141c828181e840044001d60a2001c01c050301c000c1202c1c2491500a443c2808441c00c00b0199000368618901c40781d072000b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 636924253 1250 636923003 636923017
    0x5040e180a1b0e09030c0607092405210403120e0304090f0608100509060711030702040f0e03070804090c0e0108040b04020a03060504050c090f1317132d0308 69
    0x7a00820b40034000c424039116a15501c0000c0315024a0200441104007001901404c4900307025241b0a80d038a0f4030032103c0c03818501501c50450110141d420403e282d89102403601c90440c100907140c001010900061582040740c802c0344000b49104010030503038031984848110700c008009002d070719250b01505440380100d00641594695a1f100300b45078000c0da401203001070030004142c503860b000419014028007000c45100445100d10270200e00d503e44603101d80c1000c1e4001c040510309225082c2d0800021b0038200c050f094519889081300040c0d80d009100401c42d2502c00c00c406c035655860000304906603108136030f02c9402e018409024507031356600103045903481544a55154003a0741c8a100080c00c0c0c40080e0005050300d0310b818200020001c0002d09608803030011217a582c0240e60b0045041c00c1210704841100b0102a06258180003a00000c040301340c152a0301402c0e4102401c22240301007030f541c81d50003002d00d240c02d4101036554419010206040740395841c0150041411510340c000c0c0d0344030309a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 636925503 1250 636924253 636924263
    0xf140d081b0d151203080c070308010b091216050a15020703150e24060a0602120a140705160f0f0e0a021b0303010810290105120705040e180a 62
    0x150302000450781c2d0b2004441004003400791503c00e4444602c15140410b512044000c24055004200489115010343d110a50701d40d440300201da0a081c04070710146c00603054a41c0004282d09100c100b100c0500c1040303400060310385403420381e9150104000802080d40d10112f0502004d1030312040055011039144180d0741c00c940312030a0b100d050314203840102200d000520060040c40a2500b150011030400c1202c1040000e20306615150501000fa4424080c454940580c0c4284d2507001d03a040140081e00c3c075881d803070420750021907004032901e089030b000b880115101d4000008c1c0304101c08000320600b000d82030384841c4c514800d08224400d000300d00e02c0e0180d1760b0700401900000d2120405a01280d603514511030880d507141038603c52007aa030741c00c01e001e0107082d030003010000ca42860483c810525500d940c01c074512006d401c04046030522000f0799610038100181040035034800c0c5106800755000d0041c680e103165903585040c6100715103840c09090202e124040d01003415100c1000942c3c000d2694100d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 636926753 1250 636925503 636925507
    0xf08070201050d06120c0501050a3603080a090e04080307141611040c0e1507030e03150405070b070807030e040f0905030408060a111204030c0f140d081b 67
    0x2500058940740285801100098105079000c111044401062003002c2e00c1400000801038485005403080e025143c6c80341d00040c2000f243d4402d5600426040c06001c1e01215082c09418450080c6270000700d0581045d0390605001500300c513030950090307034100142420084907046041036030300e036001d900c00a8070309000c10200d00e1084410640c104111402841e003400d111840030078919196003410700000045214130b02d015900704041d801000c02c2d160361600101401014090410380c00181e410103070064003001f040381e0b2050400d8800b0807079a144191520340004240c6420700e406480d1640356081062007000500980c070003d880a4141c613461603240c100036600c0100343c00400d00403c440318485c2d00703190134500e0910a0090210041054400c0350090f214250390700020341c810755001102446800300200840003010400c1c400300c45c0c00900c2480d04121503110368480544442d40450181c0384c0c402c118035070141040f001c018003c3c8074074281c1032000d4036141c86294088009840b83c00c5884103440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 636928003 1250 636926753 636926767
    0x6094203061e0c020c030d02010b0102070603020d2c1b010804030f17012601060b0406050c0c0910080d08040809010c0804080715020f030909061c0f0305180405040f08 73
    0x40a40e90700c15845002d1410401070f40f030008025901c4801d00c034428001d006100401807203900c103024981440d04182c00034407180e864118110000d500c29102c02500b10b6843d449800d05807a015580044000209100c40c400181d0302ca500741003010030141c1c0c2025481407407a14840785d81101120b41c0c41605820609005130800005889400081c0108000c6903080320000c945055104402500340029911000d5039100716902c244c01ca80103806640c1c0e20030410300c020400d4920910040c28481100c1c2e080d1401c1c80782010101e095510190750b1526422050041032040e110100000601d220f110720303025402c1c5c203240e121566584184500c40e030412a10410004c00d1240200032200180480401c60b19010703501d55044c0802c01d290351070384005019030b6003210340e94100081078412004000700810501d44813041041084c1c0303441c650b145c404401c0035151801042d294850118208d000f611819907559860440240040c0c007807100a22403860241808007203541c101c44107819541c405001541d40b03007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 636929253 1250 636928003 636928031
    0x102030f0106111c02030c07060e030715200106090c320f0706150f0308040e061201020d09050c010918020f2502010e04060320040609420306 62
    0x10f16400003130034000f20480100c0c0501d90000c01031511009110076140f03440d403a100225501d8040c0088164103a0011006120820a03c0100e81e4484142c2c1018415601c4140e60b2050050190050002c2c0c0d9541e43c400700004100c1c0d0040c90f110620320714201130104100d50207460504598600c40071000c1c0414460240a45000210341c040500300200c0c0382c86d5035861401e4130180120703600c80001e00c9403001e00028071002000d646025203a00072241c034101800c200304003058020050055a02080e004101c0c45801c00030302c0101900d183d5a040860364407581e0600e90310f030003041d41c6418100540795100b000303070f8032041003005c01d02030380307a94003580d034800043d0f040416015240c03948a05c040040c6600310800007081c44550118800c1e2210551214100108421200c42d840050012015540c80904032611130760402c00d9044010000a0b045482d20381c1c40084500681c0c0c00341c0000c148681520000c0c0465100f0550b0b0322a52610b914030b480200584000e01003207110040c54251103000081d8048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 636930503 1250 636929253 636929263
    0x509041109011d0f15180604050102341e0b031b0d06030615030b131203050405070308040b120a0c050f07030905134a011b030b0a06020102030f010611 66
    0x100400420800105d00e8081d8a603520981482c89440c01d05000c0301300c00e007842c40c01e803402c480050b0040c0c22510748150480706070500700c1581074004841441d40003600d8a038000c1032405005071003c1c89161140300e0b403500c00c2400d8140c1128400400500401899807052948161200030070454a03031990f0660000c2400340610303800051881e4105071030b203296009000b00f214101c900038820703081e03070352555181c3c07000e01284658040c01070788000310880f00144c041d40196800071310a1040300c003031540e0303612044251380250300308007202c500000b403414006001c00340ca20b800c481185d8040061503688180035109115002030941d03014400314000007458002c2c1020b80007450090800000c40703844901e040001c0003040c075009414040c54407000e24820b048509041c40c2034440481801030080420721850440308500c1c1c2880075901e507031342404140240d40401d4000c000c15100031400905840410555003002e801c082d045a01c184108981f00340080c3d41c450454005090500c10300700482c007014200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 636931753 1250 636930503 636930529
    0xc0c03010204090e150106050304060c0512090606030d050c070618091b0807031505040f0e01021b0d0819090221070911070c150302190509041109011d 66
    0x552002c140061040100d801189608100009070b0307160341c440010780c0c54411400e000b01e1000074402c0c40010000364465100d0036181c40c0034186181404501072048c054034000311640d01c4150032110901082d400c0801c030041138400389040103402c00c440720750f00659480d024451202000f4541e41c40c01d404000922295020f0b042e41c401c1400440801581c0128200b10640380c40d0028102000103800c0c603129114500303000074098018207480d40340034104005001040808081c1c240c0d54086404124801d1000b01901d244915218101d00c0b94060103504040c3c40c203503103138140403010781005856402c2114020706040341340d400080c00b0486001040e40e40700900351001d40c5034501c9551200341540000d2100460380111010701c85a020280400014060800b00034004407170210180809080070100382a501d00e51300d00117050298007400b82285502101190000c075100180203501414107018801002c140a25030500d044501c40c0000c25130b03060342c42d007005504119408080c6940e5030744800580 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 636933003 1250 636931753 636931759
    0xa0e120f160f0803042004020c25050d0c090501050402030c1603020c220b01020d021002031909080d180f0209041a07020304051c1a220f0201020c0d02060901050c0c 72
    0x484c5017601d051500000c45840c1c4560002585c04010802c0c9000d008481c00748120303001508680c40c400e104802502c1240c450030380340007918072002c602034407462800e0419a010315031030406585884201011070b04113030461801075004000704010803042c2d00488419440ea086000c24800312801c00b2030078007004511065005050b0b000c8004c101001020868a40502d11400c01c200704404005a03600c0301820380034000341e00f06507440000c42c0d1183e40a1a800701c2d5507800001a8014001010122814008200c2d54002c01045281d90610140309404407900301010840d265051a1034402c0c4403400420000d01c41c08030b6000090802500d0b0702140c040012821212810f41480351001e1349035080b030b001c0c890041600f0154007081500000f030660042c6c3d000315110801d600e03064650034040c04d0041c402143c00305507030110441400d1040300c49184c0c070700504107a80d150300d09100080c10f281c1c00c4003a0300d200b0310000c4148405a0342d50f074115200c01c842420140e076031340c040070035590070b14140c42a1654 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 636934253 1250 636933003 636933007
    0x100302090408131a040501020d081b0a0e030106030302030a081815070302070506090706020d091a1b06040807020a05041a0906030f012f121315050a0e120f160f08 71
    0x1381d4841000640243c131801d80a07601c4502a4840450700903c0488070301c0c0440c002c00c04560401c841d400e0041000f14031526000202c442c6203004030303080d81c0d01030b4000c80050303100041071104141d0050119402100c480032020109422400c5036640705110000840c2c01e424a10116100f540070354110350041c1d42c00010b540407403900d102420344131109803003840c01500030b02221511a80c0318060002c291800c03640c0f4440179041340c00c0601600d0304a44100002500580d004c8122403500b0024a07100e1846044d1043c1d0325403651052000005c0683d008034060390418440041c8044440a080d00301e0700c040d6044034860b5180300009103049000f2124244035460041083d02031040c03130200c03070101c0c06580c5003c01e4a081039400c0710041d200d5200280b080c1d00c2400d001c24980c40092003c401428007401c442a60003e0720304003141151400e840c0f101903195070350b03000c4c4803118040c01002d040c28071155046080c2205050b01c0780c2c1621800d5084d8580c100d01c026075000300202d0201a04445801203c955 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 636935503 1250 636934253 636934289
    0x40c030605151b0a1109150d0c090605060f19090b28050c06040314041203230903070b0304080d0e010507030e03131412191104060506160c09050703060302040510030209040813 77
    0x4490100ca40146c4ac0481e040c40f1010503181001021640b01c456202001480c00701d245c507442c90808070349056002045900748000440200c200003900000c4114028a80041001004450004004145203003444000d0006030380d8400301040b2140d0180d09410325100d4a400144c00006500c500e17081100520000c050241c203040d4491619401010744424002134400c02c0b020400c854003440a03034980c541d1041c00244051880310001e0743e080780c4110802400d160882c120102034a512071010580c0b42c1d91036081203041581409610361883d04000074605e4802558424002c40c80140104003441012525032a00d540324880516550240745003501e50f04101c1c1c41080b1080350010106445501544010a4003481c080c401e050031207000402051400001d00003100d62410801c60558080446120000d6005140e004e44e0384101c203070b179500041c0c8909500c10070049030700240c115040c101c0c60713803400e00060315013022607074200e5001004e483c2c441007040b0140c080442c00e0780204440102c100142 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 636936753 1250 636935503 636935513
    0x11503110a090303020c090105060301170a02040f1e27030c12021609060b040317070c030506100b03061e06130e06120c010e040c030605151b0a1109150d 67
    0xd442624803d50076201b14000c0d280070058100c0f400c0c0505036115a0410040114860340039018040c050340f2010f0310132115083c0c0020f82115941c125419002d910344c000903c4c401c2e450640a0089499894204030b0088403520451404e00200c41e02d00c840301100a160040c035001d00300c1c0c0b03c0590780c4041c0303809401442c0301c4002d48a40b06000706c403801040000c2c000c21000118050310060f01e034002001030525103503494404000e44d0801101152210801240010030494203482029501881c014011801d003600709401c000388030343c841c100d042c4040c01400710740c2e510035030760000c002d1923100850b0b41840d020780010160720030b0310442c0010040c1c0080000da60080c2e450b00e02e103d05405c9480304060704021514585851000e1891070024454440381c01551610350302040910105140000f500764544000ca5040070381000ca10000c040c021903c0000f42d0004003005403a01d2080c0050040c030780042c6e60b4103001f50500d40c01d05128007810030024414600003194039220400003020b5001002140c101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 636938003 1250 636936753 636936767
    0x9090a030f0c060501380d02071703090c090907060e091008070602060a060506030606310608092103010b0c011b0f11070506091c05010e0303010e070f08011503110a 72
    0x50704c84414122441c0710506d9648031500c3c8007008008107000d00e031003404403e0030008d5007d02030444048503900483e5500d95101005184111000002480f40c0f49041c4100308000c40000c004d03401030361111201748005907000041c82101401030312036084640398140099402515a002144dd40c455140e0001d0280d13400900e06001d004081d90402c0000c1c1c444c03045c0034003031208480307064105001300a580d4501114051b40b103060f0200001500086440880c020001c1090b54041e00001d0000414001014800d00c0340100e001c200c00080d203030b500c2ca44c848221031400141316a680c00319012030300084d41d50080d00a07042c18800d040d0300404130a07009001a2270102c803810054001404c000c6030f203003032050004034481940c1d4002d10313481c01c00c1c6003542000060300d00d21554000c00c01300040c01078001082401400349080c03458004d541c07a58101032030054400002031007602082041810b05000c0ca40161205040d5188101801802c500d0308505401510b503c03c0410303046580003c03807904103540010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 636939253 1250 636938003 636938039
    0x170105032d0105041a070507200102011118040b040606140d0f060308040e240f01050409060b0403140a1203180212010204080c0312091017010e1509090a030f0c060501 73
    0x2204c220b585c07501c10701151f103401401c40c02030000c0d6040c0c030b0b4a00c3c080e00100c107120744084140b002040201c4400e10a40300c60300080c3c10b081440450020b10806842c2c40d014102c1c000805031002c00c0310b80c0c03901e0710003040303185032114101080c00300040b052109a02c642042c0808106101e09001c019524502140b059000e0b1081127159106003011503ca10007003a0104020298180803041c000042d4040001102d1888001c6040c071070104400110038403240284c90003488040c0c820341d113541c03a6040021044050f84a21a0240c1005540f0000103107984801d411074241031a002610b41c0c8007816a0a0900c0d1605003e584865100303c0fa034000c0205400400542d0701043c1a101400c1560f000d00d503681c1c441001c05c41504100b40807040700ca09001002480b058028901407103010344d65443e803414040d00ba0019000c00c41424108041c02c0300180d40c4111410b401d4500384c03200d1601c1070b0069140c107075540c4c1c010104440189640f0400340b01e034416000c5542c01110402103565a452130480c0c01303001d01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 636940503 1250 636939253 636939293
    0x302070218010e04060b0103200c1e251d0a0e0303040f1b0515030703110715050f06180603030f0a020601030b092a030a080f0307170105032d010504 65
    0x12106580e1540f2900a201c1c3d13007908070b40f509e0b4048503d22281601c40c1c1060034480d0107486900c4501011500010340c65a2a80200e4050240211070700401a89030064290076075012600c10005c0001428050504080d4002c0420300380654940c1810b003006480009440d2002380303c04810302062240040e406902e0501c10311401c45e92204240010240818910403107070300c0201c0c199800d04030042c10740219800f0619180006520407501d12610082d0082d480a6400001d4188206440d401e148030f195000401440e14030141e01e4040d0000d1104020000c00e1425410040e003c01d156031020001c1d907000c242e003020324588401c1c0c401030095032100d0920068034441c02142c003041d85514041242026910f1005440490742040303803031503040343c440c5001030360584140c0032803c0204410002a10000e040e1b200039030350b2414003d0300181150300328085090080d66100c0100301ca658000b504040120f081101010311440440140c00c1400c44000c00c107519509200810007040889440c14001221007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 636941753 1250 636940503 636940511
    0xb0a1e051f0f051509060c061312170403050d09060507031524081012061a0901050f0d060b1c0201122f09120c012303070302070218010e0406 62
    0x507414882009919114264101c4c62104150300d403200060020040d0100c06440c1c14a0034078a400d0152a0190884081c80c42189421040b410002c582282d0712211b145031030019640f80e2840c4201d03200c45d00c00b410081c14407070001030b414007041d1035402c40d5250301d4100001b0005407030154009009003051078036007541c0440014010403149009003251201c500c0d8103031000080701d040b4000fa610568040c1100f503446000860011350340f82d401c401800410b100c1c031408a000141d9404024441030310100c41c9228078a500c0052229407243e0000381c0d00004105c0745201712030a141440c0b00103240f61804260440908268043d50040b07403204055401d03c01c2c2e03035950301007c501c46072408031098607141145d41c0d19410082c8000b21a42152203407027800304510203283c80c0b44440040c4c402d43c030b64a1242c03440d410210712003e866030020389090704803ca41c403074450040a08150300e403407844000c00c0a4107041c1c0c08112902035440344003516010883c01d645100655844048402d81c1880840b0111021810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 636943003 1250 636941753 636941759
    0x90c0406030809091008010c03020d06060f02060c0307050c16030b01050901061403070908190506090a0b011a13090605040b0d0b0f190204030b06030f0a0b0a1e051f 72
    0x144101011603400c48030b65030a00c0d0840080120308500a0000a40c0113200c00001c0b0391441c0a20a0100c4007003562401a603484040e905402a00c0c0b841c0e02c80300501c111041003901c11500428540d80c040c406013034036560f9507201c08c01640d0500030094440c2040c0700e10741504250a0a080b03001003601d0099642c07111607a038032410003070400300900540e400601c54221104c009441100515009000c1d0304007264283d443d0902685062034440900b00c2002c44111803000388001440071a82090290014104001c016281c0c50440780c018403441c403800d4828a6400801482e440c19221038010381134000c070455968240240250540e40601c49c071581c5418101d10f2546028180139546a0307122030071256a80e03c04a2040c201840149003108208a810900030100d10b03d200900183d0310550030110f40f8100003040c585840c0a048000704a54869031000300843c00714414503074081e050b0b15010941c1035070150386060211000310b08420440c181400d009140e0001c400306111904079070711181215603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 636944253 1250 636943003 636943009
    0x2b061206110a0c1203020906030a050420100509030f03031009271103010605060c0d020f0c030606150403050304150e010e061c0605031603020319020315070c0515090c 73
    0x4a05400c0d030002c10b40301846031002070329130410302842c100c02c0c1c1001814004220045a150b038021103461528aa94104000070454900c1c102501c003100395880f4501c04075040c02060282d05083c103058148900442c0301042c541e0100504400580c1c0001540d0b10303800d103043e03442607070b807050b0080500c210f04082109182c4110701480040d030041c0424030004a02d03058a40c80780303c00541036015090b549803100404c40383c503642d00800d884005400142480140c46900a09001481c8e400c0b600c5600500d035005043e9034002826078000d04200e42c0c01101c180d004040483c54491039000a007280008203000a03075a142154075050580075850303040260b6101c0e801142c103d8a1034094551182c41031201090348241005a2150702064450000d41c5a8a07640068074044413103600c0104c4981c8400b0520450a0500a0108068030880103204021450740002d03242e016161a600c403420700d4800140354144200c000c009410f070810161031030045d020aa0039182d000803101c6194512a0a080c1c1491b81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 636945503 1250 636944253 636944257
    0x30209010f02010c120e1005041b0608040b0414030c0109031d09070c060b06070819090626070e120609240105060a030e030c160e0c2b06120611 63
    0x41035611211713020902d02c0d41c280189003401109840d485410303501e071400c500c64402c85005074000c04001503001a0b0440302082091039070001002c020b04002484000303224400401d40256004070148040000401c1461541c020002d20010641c28044000d0503d41c2042080160340200c1486420404012050103c403050907900c00b0000780c1e8104540001c200c8030360000038040030040009150482e079807102401340c0c12202d1121460a080503070340103459003000740d07500185102d0519030b5424070700407600780740b6030b003d4850800c407000310754005000d241c03081104048411000345000b45820307900e82a00d40d075410441c1c1030000d620036409001c0c403642e03e0401c011110019007501e0710780391b030804080c42450b41009608209050b1a02e40c840040300044c005003c2c3c450b9030700004c1c4441001c0d021084c0103200d00d6071200c00548100014402240c8911007101c2c00313084d00381a0501502d00300c103c2c400c1065030ba0700d0304003c190f2802e14003081d101080b20080410600031941070110f150100c0612144d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 636946753 1250 636945503 636945521
    0xb030403021b03120d0219080c2209020304051b09060a06110c101d040908090402030411061801110601060c0f05030c06100312020d120b0307090606030209010f0201 72
    0x140c0c2c4072a266010902000e29100d40040015050318803100701c2d030003540074a402045c907040c5055008100030b00b4100c2d001584101001c4a403409280906010000304103d01c600700d01000f200340126151002110f0801d0400018140e0380c004564928081c1091921070710008040448080c10b54082203091a016040c80d01032074006200c5803da40c6012000c0d0703528011502246480d002d440d00b81e04807540d44807020a801d09079520b0703422074040c4880441e2548641081c65500c16490850300c7d00210720041c09842c4c1c0782206580041c1d0f00d8940d030a210341300c0d016020503668030110028000c02241c0b01341800201c0c2160a0b00da281304130f0100106503884420901499000400440c001000300d403050a403072044a0103032060304c0c9090310310240a8284241119048120703880f55104004000c09100e24420f501901e10290070b8050701ca040c003e118011455039140860f4440c2684126581c092201d180101400d44040100c5175450902601a400503207501d80032030029030f030b00c040c801d006009401c01c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 636948003 1250 636946753 636946757
    0x219020d0e040213080105040309061709101107150f060b03010e040222020c160501050309100e0114190605090c0304030305041406130210090501020a080702011e090f0b030403 77
    0x120807191818040290000c0c8484960f540f034508001408240030301c12240294080d5031040c01c0c85051420190000030120b04200e040c0c000380080082d07015021408600c01c1d905220301103003a054040d905440703805441c01c003a0081c000a04885040019603000c41304441c0585401d000d11650b52462181d0303400709104403405d0600c640c0000d401072420341441581001452800f0b445407004008040c201c0e0046611610350342c4c000170f41582a00300d040c2101005240c02d1030141c1c80d610748641599203440c0c00720304a900c29902c60040b01100c21084d080700002044240c98a401032030300c02204001083c9081803240341500c0c1c42008981c2d03040c0b036050315114170420b00e0201d203035841d2035a00300c000f802e004105686504607072510010341c03038060004c0c0d40120009154400795503614010802d00c0752001d003014081c4a40030300c007000640d8001c45c109a042e03401800300c6480b82068001070b0b500481450107a0b8041700c40c07010030580c0300d030030860300410303031390081e082071501a03c0300000e0956201c01d84002d40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 636949253 1250 636948003 636948017
    0x90d05070b1f0b0d05010506183001051807030507060815090108011a010509031b030319020303010f0603060e2404020a1205060301050408072a06030219020d 69
    0xc0440c035518200341c0c2003980e000c156102a0009100310038840c1e000c2d005114640c03000640700b0b001400701d00803a405003a04542140c54241c06045080103a42d81400b480c1c01000a0070b6110808800c0801040c82e0204409003030503e00903041049000f0002181c021080d0103000da006e4000301c2002500e02c007520b80c00ba0080c801c450030103900362520440104801c8881d2010510703600f05444200c02c40d07009041d2000045100707a1001d178025200c0002c1a40c0904115050000e8005960300050f800450403600c0c0910301084402008a425440b03034260108078045030b403541070f20081e4004002c5040b911070f0846a9019030f100c0804a0940311144078038000217070400041501680e51942e0610400c10007420032800c1c000540205040c0d800001d503140206c0c849608484103036929000c1c00b58806802c134000c000303910742903941c48018060040c0140038200c0c3c03400d02034059000c1403412131310020604060001c181d952017008019500440c0808150075800030300400f0140006400e072050100750316488 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 636950503 1250 636949253 636949267
    0x10e16050309030f0a0309020f120304050f01020c0d0f0201080a09080909060f0901080105071d090114131506031b120b03070302150d0b031f021b0d020d0206090d05 72
    0xc0d800d03000548001c400d400208a070803104450b0070001c06075402592004030381003089004100e00540107502c902e0090107030b501034503200000401160300360303001218001120617050740101c0c90080900403040d000341c0c040e5200340501126855080c5458801d98850b0a10f07920310314440180c0709071640040030326905020680b40c41c908844d24552104001c1c100c0e000031036040c7c000400c040c10aa008080d143d550b8403c0c40032095110181500d0039071b9542d1000746100c04000031401c0ea0405100d0359180c545540b0b4800096601c080c2d0ba06804888081c00340041c5c940c0060011710b2020b58820080480d207452003245104038503025039a06585540c6900402070140800d010281441100030380c3e044c003540101000590fa541a00444005258090350312090003110a03c11101c0d1030222a200b50b108401005029081070503444c00841d00d0100541c560b04401c0340c8004034442041c1d0342d1980c2c0960314954003040d5000a4000360f41c01c9903821115140c0741c0103403442c1c039480e49488440010318100688 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 636951753 1250 636950503 636950507
    0x90606071e080c01020d06080d020a0203061306020708030702100c080f0732030105041d0a14070f080a12030606050706051801020f0d060806152101050c12010e16 71
    0x11a085015511082c580b101c41403e490890f40040450b80305107541e01e00620210b107080080e42c0700040640000c140183c02c41d00080d5440c01d00401c00c01c2c030041804d151800300301c1c0c41d8041d90845580419100d41301e0174030401c0a526203030b191440807120741c81c0a48203d4014130480a02e03003e514801400c0100303488014040340c12200742c5501964100a8411080004a8000c02c070101d00c40c41c0321035075882e0350408003088140d40030500c40050070308812200001c400c0c07011450450711503101241070b01300d00c1805921b0341402d010381c0c045079054008500016a2600101e002c802c610b100d21150b894142d0341007000e50441321580511000100184a01310001c0d07550703840641c00440782d03020f40c1480410700d0a505d09990207035604014035280804d603244100403500502018240c00b1000c4c00031807402549000c0d8000c0d5004105115616002a0f040b0151b00340180c5814640404021b00c1a07140c8418009200d5003d007051000c07960581000007004040880c0b058060740d000c0d0081200300c100400d003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 636953003 1250 636951753 636951803
    0x1d01030513050615130509030405060705070e040803060108101a0a090806070207030b090c010c02040b041404031e1b0803100e0f180a12050d140103060b09060607 71
    0x1851600103252005000c81c10070808548601c001c04c01c2e01000c07640040c01d2080281c116090740801c2030411091141c40130011041d10261901075a40c40e4907503075517040940c640a0303140c0c4504039110020044c00240300c035007401544910800e0300d41c40c441e912982c4165803808407030f204400c0e211912202404061861100911094240c0c2c50442d000c0e41c2c8420300f603810408142d410201603440750724100104180590b95660000160b4081d21086180d900040c0948200250092155503a860300d600580d407140d000184a0602c40d420420a142528010380030720340c58081445015144155a030f50340d8401d240d04981040c000010400c8186982c3e030307071441030300f028000c44400310351038602051110008072078a11407044800441d202d4108524007400302c02044080300c40c1ca800c469610f4011070a40c00705140024110f10708290360f001d01485a100829661950036142e0880c400000700340031541d0403140c0c04c1c03502141c00300c51945400c0104040c512400000038414540180c1c0306070b0208041e14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 636954253 1250 636953003 636953011
    0x70b1603060b030115030509060f070e01050c031c06090b0d2003150601030b012d0504092c0c0a0e0a091a041b0b070602090a0801110a08071d010305 65
    0x80c04110705448a40c00705581d0000d030401c44044405a0740400107941c1401580d0300306012102500c0c081c108030780d000343d003044000c1c01001401007079028004680d2099003114000387d074450589072510f8000c0204c1138694000d0940104007402d140000c0380d2041e640c0700f000900000200000790310303500d43d900c44003010700f0308210207003490b180032500b10b0a4409100641c0502d90400c1303000302d030340362200005d01111003094180c1d040120060f00000c40700d501c416080820514524010080724860700225040e100700d82150403c14140280a070550305070300e810307400e0300700c0000350b0002d000c1c88050340365503130461512041d41c00f00780e00c0300c1049560003040c11103030005203074900840c18150584030400041c000703000c03c5010b41c00400400c41800341840c5030003d040c446042d540c0b84e092408445c1140c40c002d039540030303102c9580000c100301c90f030340c4410a0718010003111002f40400586038000500c1500a54a64400305096400148500307101c1c0d603d4030146031800c59120240740320203004600420f8028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 636955503 1250 636954253 636954257
    0x31204060b060406180e0601120b0d140307151b0c0302070e1e060103050402010206161803061506030605030a06090f061517060603030d0b0109030b1e0c070b16 70
    0x1090755025101e00000b0400b41000f522501c098441c21003034800101c40680c8401040403051050000c5a03034440c000543d803107802c404c08a404103540c40001c10007026402c006042c0e503200e121a8400d4140440940446402085100d1211000c4070412040d102c2c1006814000390300060050130703160141210488082c024811221826114100a2a00300c001c0d03800035841340744d50442e4400a4800440264014030a00c1d0501190400f903002030758941d00074000c0e00d18121000d910b0104103200c1d4041d118100440000482c40e250749042650041c213101032003100c1c0307000d00080801c03400c0c0179008010440c3c60107002071025110325200c09008044848080725108040c0c2c0c010404a41302d80541041c1c2c544c0f40315940b02e5070346880e8400c00c0818141d910204513800400410920350f5000c030517190120740504010070702400810040310418443e4000629803820142800b40c0a1a0014000032445084e06c941a181c1c44894000d2a2806000c43c010005444840000c030210f09054002c58084a64 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 636956753 1250 636955503 636955511
    0x13050103230a024204090c1b0206090d05060a0219081303120b090403020c1207030f0b0c0c0a06090203210a0f0207050a0303020c030105060f030a03051c0e0d080c0a0203120406 77
    0x3000c0b0400380e080c3c80c442e03c0502500108080c002040e087c4900f000040e82410207501610700f142400341c0696040a010340b16450209591159440f24032440016079032003130a450f5185000483c802c0250042d01840c90341030a06d20300c4445450040c2040c900408072000c12549450844e501142d94120f030301940e00445880b01007540c15030b2a0080d889020700c0c425006044c400c204071061003403004000c4003014565012000800119601c00888241181c10142c07500855407070305000045403150741c3c0c8035032040c410701174042c0a000382c030351101d040140308a06075661440d40d661520812140c0804600103000c04002c650001c82c09500c549180c0b034141d0065661451782c0b9000030303c0030070045e4401d40250700510303074513421440c080c070840344e225100719002c003001d0b04900c01103503441070320b10001001c0c08000540d41c000342500494000600d02c1041c41400380c50490890541c40304a2403440c98082440c00c1c000c00ca01e0710004041d0740e4420010f900560805c0913000c0d602d1900c82000e801560841c5d83d03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 636958003 1250 636956753 636956839
    0xc0909090a06200a0e1203040b07050c030705090703020a02070e310323040504020f09030f2a060903010603050f060711071413050103230a02 62
    0x10625014840c0380000041c061250550400310156000d031040072000c00e92540c0520450003804003900d2000c041031924520007000400821030004e104054941c0c40e02c000b2070000350148002005041842c440e400340c680f66400c540030325075122030a001c2c0b01d0344850401700082c4074601c680d01502c03d07100b4910403121081c2c1e030f5020318842c45000707032503412100e40c56203010508400e205031016469800c040364142070319030984005207840c5050100e07034490079a92003207061000040040e6805040001c00031903580d842c1c541d000405a0280000300c0c024060300c2a07170106c840c80465541c00d08810350400e0500031034890860b465552080b4031aaa00c00801e02c2a00c0783d42d02c0903c1108040c510802c000d10102c40d108950340d1078040700070040410011206042032280201042d03400860f62880c1c8230708296240800010342803114403150040304c070315180002080c003209080404110600640c0b0051118880404c0c035103440702d802010750010144401402a01e0720420b845400300c2c0040e808a41001c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 636959253 1250 636958003 636958009
    0x1e02070f020d1407060903110126090d0e10090b09010908120307020f03030727080d0c122604080c03070c140907021b0303040906090501090e01091a0c09 67
    0x41c421400b501c0c92441080b507510f52203004c004040241689080204a20313255503103800102042d9484141081042d20924000340c07110b402020b52040c20405d140c5841c90884021960349103500130f07020001d0718030002000d030f609000490903c03880d025a2240e45130390919443d035a46174000b038005410062141d00005282c40c1c14032461042d01c041048080d503905090800914100710b0920010041d00208140300c40540c11281e035034403402510030f5803000014200c03040e070702a64044d48801c06c03c1c0102c034130551038298003030004108244074401088074081404000c03501101e0300c604802c006044512a001909138201105174014428001e4a1401d001080d074542982c000c0311046440d42c44032442407208944c0040c60700e004010580d03944156260009000790799001d44030200442c804800c0d1100d02e80c1e101807080320054944108244a815610381106000304000d2050340a03851070300079030503d0450180122088650440c402d56000196100100958140a40b411022400820041845417 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 636960503 1250 636959253 636959269
    0xd0f02030123060f27181507030c03060f06050a02010f060f05090c042105010c0224190608071403010b06030415021e0406020c0906030706140409050f0405101e02070f02 74
    0x8005c640800038181000e0408032007030207074150042055005825004800240f0181040d4001d65070b140204021980c00800d17002000581c0000302c144900d054040342a41c3c01a0041a0a278120390003007081d00a28001721040310140d0080c1c07081d5201c0307000d0030003251600500140d004909003200d43c1c606030f80d6a1001d038200200b01000c0d800341c0017920022081c840c0a225690306a03440b030003d0000c3d01c00d0304000e004422201c0c8805a80d4049101c0401c6071f411220702d1b80c42030389845240410400751a240e03220350f02c941d94440c3d20389110f914401074846003810b020b070b400d008502801e01342c25078440307980b120b848240500d4102d1080d50300380148541c00407140d0b144041020140d460300d41d00d60400700c00a08014941d01c8443c000c549200600009031000944102150994079109000900344861001103100303580c050804a17003071005000380000c03800e000328003442c8200211101d58080312141e00545003080251000410754021614460103d0b400404009100b8450b00c00380705060780c0095503403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 636961753 1250 636960503 636960559
    0x90606180905060c041805040f060914010c022109063a0e0d031d030301140924040b01030b040504030906030b04020c030910030204050d0f02030123060f 67
    0xc03948030510380c42485420f0200c0c0d40c2040d1a00700840c070f0242007850130441220320040c1d4034100303030740c8070000f405001c400d20303240284ca513021800748104a01c80c14810300c4e07604118440d43d0103500e0140e400c034040d400012208600c1c4450400e046954061100d00c0080d0307000f11320b00d1a0089010406141c01c0381812000c000d084040c91005ca642c0181480341e50400410100e41d1003185140000c500b030783d840d0000d84100780708080d140104180c03405400c010100042d0382c20b8909103100100011624120070303a8140040401a05c008000765114140081c4144010801c80d110124012845681c0e00b06038110841864040c10042040c40030200414101d900c11a419400903070112000d201d1580d00d4024501d62480071a42541491031500740340b9101e1007030440140c4150800c4050b0b44d1000d01940540c0c00a20b401408072088030424140601c19048080081780310354a00511607419400014030206031411314003002030b5903038484040c400004520094260703c1400429040591003049004c200b038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 636963003 1250 636961753 636961799
    0x406030b042607050c040c09090e010605040c0c030c030c030e0d03030c0815010203040e1302040c020f0c0307060905210609070302030f030f07020105070602041a03040b0a0506090109090606 83
    0xd1030100040507000002d58080016070854104041000701d4400520500c24807030446000510010502050303404900c140e12070054242000000407000c1c90650000c41104c00903034061040403100c0ca800c4840240d0010b000b000b0074819001500868803846041414901c2410b00f042154004000a292840c90325800c40002c2d444842c204101c5501020407070300000b815a0706000090f1141c0040d46030b000740d01590b40840030400c006004a08049040c40d81c240c5c0280c02000b05000506000f5140c81c40682c40c3e0744113100346038101d012401c00042102c2103484d00ea58120150b4240400c1150110b081c1c2e51061200c804a02c40c0700c10710100f40304981c02508000001c2c0040707407031441450308118480f1010010ba40007844800c01c624220320840b45c02c96424600980c2c1d84a140c44c00e03800a01a0382c0244084101c00086a8048428113004601681c040e003041805a9954814101643d030101d074080d03000145080100b10101c8107802102c0164412480450240d4403040e555444c6040660301c214 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 636964253 1250 636963003 636963023
    0x2030a0902011b0c060e0d0804030303200906071e1b17120d0504050f06090601091b091403100908030709080d09030830010305060a0c02120304020406030b04 69
    0x310368000f552100301034090072000c005894181c0b0b4141800b0194403038a4284130824007052a1951940c0042001c0340d8800c41d5030740c0b40c944030b080040c0200f820b1018546410101003410095000f200c0c295580e078400105070394a0100381d80e44200050000c00040340c00c20048281d0100080d00e005103041c8151078900e141507420341340c00380001c01e540559000342c0300d507040ba034800b40003000c50400316038070005151000300c3c5503141c0f441c12074a050000c0b0400b0044c1d00a00083c0840982c021a1a9041b98800d25003444111040d11504543c004900001d40c040361840000700000d01d10510031050b102c0000782030395810152009000b0a0744d0b00307004110791184000040000e011342081c038040141401c84e00802540341050805084508180005890184007240580d00c4107a100e5403da02e10814003883d00f02440c0d4a600050501000c2c00b00b164140107110002d510b03000c4901c103070032007081150b0003840c0e10b0000f0351500c0740a07440540166002607c03050003001050546810724092441041034207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 636965503 1250 636964253 636964271
    0x30519111807081b03040f020303090619080109110a03110412080702130603050d080408133c120602070c080d02011415060d06080d03060503010b0306060d0f0c0902030a 74
    0x70304000d8010004424551441481d2020841030425264007d920000700c00c040e00302400042d20f14010f0b034184551045000840d451490514200c0e6540b025050311090200d0343c0340d40c62502034a26088c0e038068019030a0012600c005d10a801c402e40c51101e51180030b00d07140c3c0f1000c81e00d00d03911050100780e4601c00001155400c5041c08682034103800d0011204010060444d41e8858850804000e00c9040040a00c0403030207200c40d407412110340c06c0c114042c1d48851640c50100420084d6600749d20000f0020301060807944040661003516110750340030394400c01d030b410b141c000d44400141c0c8074103640c0c4513400e101280016028422030000b0f4103014005129040040500074203452403d51540b240030611001d104100080d92446032404208603078035a180c1500070140340c010061640400010300c06ca070f2410042d150150301c101c040c0c400540c024400381201c0c0e42816503030102941c2c115082000050700a000c02d1000f40c8501107184181a10b0742c0241c0d1321402d01c007d98000b1380d13499018075030724442c1c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 636966753 1250 636965503 636965507
    0xf13060e0114150a12030e0d03080105090f07050a0c0f050304080124050603040807140a080d0f02090303030610050c151e06031e07031703150307030519111807 70
    0x1080c0d201041c81e4241c0740501c4243c0201d048a00c591040345050321228031482c0401d80124100364002e000a41003407030b254000c2c2401003c0342400e00c60710303004280c910081841e0398210068a4403074400c0e502c40302d1030640c0a0b1402c40300c410f0f034140300f69080c11010b4640740002d401031004000804583c8004121600da00092098442c41c400e0100311889051204000d15103d02096a03805900100e8040d1242c110741403602026400c0c0300d0060840c015040702904202258000e45049450b9440421004090245000c100e116862030107138154020720010b0202d16103e500381c0c14000f010b152031418030f02c0c0c801e14645420740030141d0150510b604801c01550440d49400302c160100340300f50074505400e016002c40d8503100c105580058030141c541d02c2550202c1d08106180085a00400c001ca1104848031404803030780060718083d1150310030003c0d44a8610b0001406000d80740c004016101400307a0011040801c412181d04950060143c04000307120380d02d414070b1084144a8584070100c41c5080000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 636968003 1250 636966753 636966791
    0x90c06042312100c090503030c06040605060105070c15021204120302011a0f010c081b01050406060e1b0a1e0e010210060f0e040f080c0304080c06040e0f13060e01 71
    0x4560b005810802000306610000030b50301c50f505024420010710220b1100c002c88000095400c09030701803000240d11011a040014028480d40c001c1c0d8080090352550b030011184c51160b81c3e0098095907246d0428412091007440390002e241c50f5004803000803044803d098269046940009560380d00344441400b415028040d00920501c0c014002e001300414600141c101c03c4443c004a04001d00481c200d0300300805102242c8101c59490700070b00b201c522451205000e1302080ba0120303485414000005441080a0038a41c0a8125001c4400401d0440d80c0510013903007000109004003d058000c43c01031910a03811040c603070045a403043c11000001c000a0301e80002c105c82011f403640780100801804001000035410f440c0303c0050307007801d0348450070f004a0004a086018004500020314101c1c1d07900000001c02c112002402503400b55003041c010030260b40610b204c1d10316554a1000000c01c9002c1c4002d565a01014a0404010841082e154103040320441c5601c0c888e96035450b610341244001c4146 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 636969253 1250 636968003 636968069
    0xb0f01030506013203010603021309110306070203030414030d3b030307140403020303030f011a03010308070209070216090c0e0301061d0603150a06050109080a050a020108090c0604 79
    0x18000c4070884c1c1c0203458111010a640311640c4180c01c031400656540d8007908070400035500140b45002c0805108021001064001011075000c40500e0070b07040b243c1004502c0354171411464001d5030866032152220040324030740301d45014480c0010014610503001c280324500f82c0004010b44010b09841400310340c901a114507240c0d0481c0c10251160325101200003044a40c80b0303210b41f4100d0b85000d021180450103000303980000350706010100030442c014a1003140c01e8100c5c2d1241076070b4a00140c0b14900025039110a0002900c04d403800c1082c0c40c09403c2405000b9040703580c4d84121062040003c0181e00d4583c01303604241c05c003d403030702100000d40d41e0202600804180480003080a68a001c4001b42c0712003440407258200100c480c0042d42d2983c050204090082c0c0c15000c00c280c0d8a080c003081c10040010307000c2c80303000c43d2410f50082501c000014101070403030351000c000c000b421020b40055032904c40080250b030452040d030680e00c106840381c401800c001e110742c6400c0d000b0b441c401c41e10745e8803043d240c5c6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 636970503 1250 636969253 636969269
    0x30f06060312032a091d041a04030503041b080607021006060f1220030a06050109060e0f2407050609010c0e06031b041a0a090905060f120102070b0f0103050601 70
    0x10303d60880c44140c840800d0160040032007010064010b40d603044c0c0d04c190740c80e4412000d06c103005501d04440320310064814440c1c0c1c850040c000c198441d411440004104c10380c3c0160014500380005800140310f408881e600e440c03c01c08445030342c0d95400b9844c0ca07140084921000503000711100810008290103070710054a550305024040c658800d070020b0003000409100040c1e1601d0300303064041241e01a0146a40701c5003801c1407592807401c14100000b03800d241c400d2a00042041400041e058401d08a8104811001f44800c036079010174800c00002c822851948003614000d8901d40804102040c010f1610500c5000900340d07a00d00050b0003401c640f0f084e20800c081c446e0350886e0320a41e41c3c644007180d0344001d602d508100d540c071a01c89240c0c8540030719040b240c40c039003074011056070052000010b0020011140e64000c0d1503903c840844050700c0c1c085c0c2d1312540100841803140500e24080310340031001f0401c81e0005003020305507214407481071021740e0781d04190400c0500500130301000f4040a805001c4c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 636971753 1250 636970503 636970511
    0x31c0f050c1801031a041104060206010b0f0406050c010f1d0c100f080405120a03020409180309061103160c0510081512100c0201060602010b0109080c0f0604030f0606031203 76
    0x1820000840d0650b21140c101541d0351016500b114402c1c0c4100c1c000000684104540c840702501c02410350b01c00c1c0030300f40c05407180388000a6820075001c102e80c0e40850f0fa090440c1070502c0c20300241d84a4002030981a020754032402000140d200c54411625040507911031a14042110b5a49508010207010f1250048464000c1a078401d500091034455082e5146401d0754282e4840c1400380c03c4c6081c082c440501400d00107a5001c100340e041d009802551864982001a0162041115880040c50000801017041c5400405c2003900802010006403018401d4a20301100c20740c0d0a1809614000704440d10041000144914145004405419000c50070861150b0402c0000022140703c40340c0700500c03c0082100360006880d042c028510900f651003c02e014088584038041c0c040c0400e80110340c01586400c8180100750700c20f50f5440100d032000405440c03d550203009000c0303500b80c5e242080384c0040003040b00000046000444160280c000c9800040281c15441d00a203c60116a01d00d420913040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 636973003 1250 636971753 636971767
    0x112e0906090909081e070c03050a060b04141f1802040303030e120304080d0b030102030f010e090a02060316021e01050103030f031a0f011b11090c042303031c0f050c 72
    0x15000489410301000051810445c00e0b404c02c80a0314810940010000b028602e00001004800111101c1c050311464081c04020048018001100c40032031010902e411700c0c801048440b08040f40d490b000c03010b04007030443e405880e1002d03004103035403006c00e076004541d0000d010400d1582c58400c1003101c4244d48d02400610580380d08068683c00082c04c054070802c40010140f070b504580313074012580c0200140003952a0300d030220200d9440b401c24894610000800320000b1809040801d1040c0e00e030303900602160864913100c80e45640c040310f69a542c001e500c10180400140700c0ca4600302070315141103e001241c01c1d815441d00078108285522135400381800c1040b2803500c00039040052014042c166003180c1020450001212a141c030302600710403c03a01c20314002c0c00d1006850440a2005051380e07080d40945038018004442d110b58803070948004041080030f040300203c109824801e02e40101103a0408400207070303404c1444c0c804032041030100c2d074a00303110322006511701900b40d1046031b2403121818018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 636974253 1250 636973003 636973013
    0x60a14010b030a0f200304020a17151f0b1c0510050d0302120412020f0d080301050904050304031a0a0513030f0e121002070209090a112e0906090909 65
    0x162120071a2a02c131241d214401d141c42d4000b8036240d4044840e5901020b80a90119086c1d1056034143d000b140940c40100d810000840700d11014048a0014624024810a400c40a5001500d07502098404070314201c040f50300007103031001810306601c5241d659844003ca81803c940e1031002500700500f40410403480100307400c4400e046910603680102c4000041c60100c0c1054040480030700000004100404d0103580c011040064510035079040601a14150400c46c511842c40300051a610040005009505003001c0030f641140c03003a400c90b1b017000d0301e0769101c1c2510410100fa4002c074924003006c001204c0f455001c0c0d1500090000e02d40c20100c000781d100200780e00009100c000034002241c5501c6044e032600700402001c0300c09002520844d441180710103020394018074059201c0d8448070007040b101c46002c20b6103220300398802401040d2402450601010b0421480c1c0003c00341030003a641c4061540420842a0703e0546036a51340710203040c0340c0060b010605c582c0040d20b01902c1d0800303d000050b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 636975503 1250 636974253 636974257
    0x902190e030703032016060f050f0405060a0c050a081e0a020709110f120714040e15010302071401060806100303090e0a09051b01080f07051204080d0e060a14010b 71
    0x81d058030f002e64070384e000ca045c5051266100500c101852007440f545180c40503102c24140181c8195694040324080c82d007100f01d13024000c092252003981010001000546001070041c040e260742801d02601e84800c40d203d150a04243c034005841c02000059031082c000d60181440850440e503120082c1010301090000399136207201d0080504882e505c015941461000c0016500800c00080401c0c0e605c6076440140520307004180c520304081101c0c12030f4801001d0000c07041c1d5040c1d880011400e001e07640c0c1c50540d035181c1c0e100030780c005060580c20800b4001091340640100c156034155000401e000e0b1501d0401c40c03920500034102840c1400807202480001e51100d00c01044034248910b0805a4031030608a1000713000d2803000a0917442074454481007180900483e000e420000d880381c0d4101c1e51000043c0400c000203c501000151003040190380d180303140782016030040d001d42c0f061030522040020b58001c070385110054030302c0c80e070004003085800d000030700440790400108140711111703514203c1c010b0014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 636976753 1250 636975503 636975509
    0x6180d12230c15040c05030304080a050f010501080d030903050d1b0908060903090f06131e08192907032c070620010c0801030311150c0c01090c0902190e0307 69
    0xd00340c101c013103001d000d409070600000c2c010060075a6500c0d5540d1042c50390b980d00c528421903190180b400c3e440f0b003442d418403440d07040325186000740070074210204044005050409048042c00404d12a400300140c6601c0307480c060000f14609020b9000c14540c0240c028000303170341702108540c4502d04200110030b000c01620400c07842620b0008a440800001407120301505000381c0c1a030340f0f00f00700000c0300240c068400c0b40200c02d00040c10040ca442d0030680d9207507651802c1161610303907210310990004040c3c2c48038811125401c0e510100c060881704a54010520949110700042d0b101c58030070184070109004402000e8406a0b14018512a030b0354443d25045148a12410b01019080c42c099841c09120404008402c06008019081c00020040c04411081c082680012491401913194000003d03040c0d4540000d0401400c0076616450142100d40c80403e00720090354a810030500050a03101c03042010381515200503854140d400e0301b0350200f030642c502e6a41000003580c0e141d1403640b008a40c09040e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 636978003 1250 636976753 636976783
    0xc090c0906090a230108070503090d1d1f09052224030302010c260604050601050702061602180411040207020a030b04030e03010c020c06180d12230c 65
    0x8888680700011840182940418603040402c5280c0758020400c0e0040c0502ea00c4c00d0701d86802c142c4505000b2540c5000c121100c8119038003402e1265011801001002003894000c980e442800010b4000b042c561074a40020202c03e80c000500b8070462604411800003820b4141c0e0719110500c1c0c4108011203121a40704402d00155032071248a4000c10b1020340030101c000702e040100e030000d0b41c034503000b4024803800d8080340025414501e0004480015104082962a542030680403612101c080200509011b17002505100f000c100d810010780707603c805010103030700d4038441460030010381c018403440045200c0b9650b034004800007000002030346103000c4400407030259001031b12072038144003056920140390000b030300c40d51500c001c002c10141d01044600261f40306038024400f0060401c426a0741e401c294010541c8180188890120500551102c0e090800004e0414a0041481e11444008407501490000051742c560113011b04443c81441826590322800702c1d546000c606031010754450317124000ea881 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 636979253 1250 636978003 636978007
    0x1202031602120109020909030c01060e061011030c15090601050d0803040602031317180a15121b050315010203090a17150a090201090510090621020403030906020c090c0906 75
    0x4881d1070135449400380d0f82c0e000e03200480604001d440b690381d94001c519076601642c200b90001c54508000d070b90b16800b806001c3d00818036283d4603503040c0c444c0e070301544011280b0311092103040c68206003040f0b1500c0b035509080311505941450800707541000b0058000c5405101100d420500040c1c1c80f81c1101da0040d048880140c50391105107001145d1140400041e04d042c2240312540e0500707007040e00402d4580c0300030740300d0b000b90803030b0105100040c91680300e0301c0315840401c003119038020b000d00da03401900030400031300180e0400780108401e0070742e107202c503444000b51000c000c0220347c0c48202d80400700d0240900040d030130188908001113440d03006001d034132040b190700410b050401c0c50401070300301e81141401141c1c60500d8003062280c000c145640c4242c1c00a6020074002810303080131046422421541d80e22061100d08101c001e6540e00c03500300d8010040c05507110290441a1540b0140c80a103100e50b5900300000d1a0240080c0b9000030060003a110742002030600031507120000440e2110002943c0482d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 636980503 1250 636979253 636979279
    0x17040210050a0e3705060d020703050f0c010c1403042303071703061309081813060e1e060904060b1302130801052401121112041202031602 61
    0x16024034800c040700e41c02c5580b4070200c04c59413a00080201c601140d4255041c9803204e4244100c0000589102e802d81003601000700059024068008000ca24001d00b0043d01c0c04075806400c148a501010104010f80d40d00c014178030100c0d5000c890a42d1400d900d40010381141019101e81e862426034410307040d000c0c0005100031f071039003400307201361054150008607222400c0d1803081c003005240d04c01c40d481031084010041d8140e054119100c6e88100b103400c5549541000d02d01d61000748101103100b1410741c4407a1100451045040c07900904000d072403e11540d00d280d017003400d25000600800c0d80320700c164036010802c00031a5150301003001c0c0c3c07064002a000c5a015444004203032443d5004901907081400000c810301c108145080348021218848002c118a0b901c0da070041404aa0b20b88103500004036070020030303000c3e61043d102507124180a400001d1890205120101c81d6070103014a03244c0c0000039400c00c000d00c40c183c01c1503041445180041c51806001055103031546001e00002803044003804840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 636981753 1250 636980503 636980507
    0x10b13050d0f0501150924050607021f020a02150301030218040219230d02130b0a09051512061501141e071e0f0609030309080a030c17040210050a 64
    0x10b0304800380c000d0000c00c40c2051051281407042094011901e815080c201c00900210550802c0166517105105410700f6a0601e0100042c0d035000c110140e900c41c05410203442c1d4568041d40551034000a50002e040070a481c1c410320a07520b000003092120030105100400168480d40581744502d0b960001c0d4010b999602c1c0700140c1c0c0c50185050000500091400101d101a00185542091a003206107514024100c17005c01c0349440b0010002500203607100040105d044080d0070035400d4400040c00d0001d115200d44460040718002c0b9600a441d545682c102040d83c01c10130006031001810002a00c01c0b85020300c0c2e02841240d0038036005040040f079401da121400400301c26681e01c880074940c00544252034102501f01e40e004004180d8003000b503000103800e01e008504c44a00c4496200303401110100150302c03844010700c2149016424140c42e0700c54080001c50390001030034512800d0b280001c215420b60001082c000d0180102841c00380002d09100159441d4a0200000b060030f140c03640c0e644000940c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 636983003 1250 636981753 636981773
    0x501141204031119051005100b030705040302030d0e091501090b07050a020315161803030f0e030d090f05040504171b15040b0c0304121d1215010b13050d 67
    0xc1e40d0f0309801102010107500c15400d00d0426824018412680c950500d00310b020211070302903034502002c0d485580100003031800740000d1540f003405030400c24102683c075004282011080890382c1c00080039041050090310b0890308041d04036011800b04003100a860f00007130b11805c920300643d8000c0f14041aa841040b0003000318007541903015040d41c4111952011a21407500280c1e40c590038013007011507808100c1e1040d03100715454112080381012961550f00e080c2d51808114078001c0c100f1400059440a1341c9040080001c0042165180080715180104801c400b252a40110748500c4c01c003010701c0302081260b40203200305040301c282c00c0d039200b8038030f42c0a161500c141140510139000329003a90041d14030846a00d80701c0d90140c00310003101e640b0200401050b220032a03004008001d010b07161142540308802861034904021780b40d04504801d5400145c2c41043c0304418505a40061481300c0050031160250303004200c1440b21300e05100010b00c6a400c82d1a00d4040c030f5000d240555200000d0107020303c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 636984253 1250 636983003 636983027
    0x2a05030a0612060f0507110d1b0816020a05010e03071806030c08010b100309030f0f021204080a0507060f050d0507090506030c180303270307091401030b01050114120403 74
    0x30031291840e6580c64041c010b003c07650044c5104e6440c040000b0710081c000d8000c1508401c0040250201040c003c0007558407814403070a205a0144030400e8800282e9440002c000395084512201400380302841008061038054000c5410418200d80e8a0b0080d140041c0300410b0b104488507103908007400c0042480103004bd40e0002d00140d814841c0014a0304041d404190100c9003541e03d405402181c4800ba000e4403402c0000400140140c07184030411881040085e0601d400c52041e150181e100a66007081d54001d82c000e01c00680043c240802001b03410001a00101503d041a0078100c02018014005008000c000e0366076948800008030301d188540c2c8080302425000705619100e09000c0c80054aa03040304d0002d903102c030f5144411000c0c51030f001041d01d0405035076484c41d00c1040e4144000481c81d00f00e01034400c0e01885504008a883c9109001d484004e4204601d1843c8130f6245050031404208182d001710305000030165a2094101503078100c801c1e902041d1440080307600e441c54111140e00c0014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 636985503 1250 636984253 636984269
    0x603050c0d1b08010905040f020f031c09260303040f0c03051207050c0a080316020f0607050a150606231204110a0e16030e070b0309102a05030a06 64
    0x1890b80d0400c190545004058070700c0c0d55802c00d07140c1c0c0b2040c1c52412140207641c098844072103900590018030b030454107002d0654000c0d094400312010803c525030711b00058510500411b01c118002e00403800b192400000c01080d0407401840f000301021a5907d911020f0009013100300043c442e13105000003004420020359000e0110b0304010320054491341543c010084c1225240070300c50b0000c2b040e25000304034109913004000039600c1d180003101180340204030002c00f01d030400d0a4a1038504580c1d03500014240c0c1c1c41c004c0e006091400c456141180450a1400c41304500d01d1500e0790500035140e1250741c050b10804a0300381c00ca01200c1002e140b040c1809403640055040c4040d108010420203006880b01581d40c1c282d03800301840380c443d02904102e02044640864440f00301060b17109a40c400e80120086040000544202680700c5c1d0514419501c2211010440d034440032128010301d516101d0014841982034040c03d44640340f2041c003840c1020802240b0402c000407000c0344a040c5c83c0c1c2c1c0000002c107240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 636986753 1250 636985503 636985511
    0x1050d02150d1a0303031608090109080f09010206100305060106031a100207031b0e0408070201050f0705160e09030a0810050a031511030606070303020705100f0b0a06050c070603050c0d 81
    0x1040403010b4200e10068101c103c840c4032160b46a41000803d6900452010154200e01c8a901c401141c00c2d0304000c1105180d13640b18805040803c0064000f0f007003200080100a81d81c00014001900d8400050845000103007000340810118802007411815144c1c94500031030300b00c01c4200058040c2a0054409a102501070b070030b0340d0070351b800180407000c42c1d20030555032500504e03200e862000340815114036645444110300040024441c01c00800005105042050800f0071a000704105500401c004550303d5200610000c1061006024a40140001d0f00b8420181c58901c050645038040e030300694048c03241c0c090100b040c0d103e407022590090308000d003800420569906203214155840281d4640c11803500c03012880d0407881e2002c480c4142405841540303064602d41d0120000c2d48500000e4600d03002c0c0c11070018440701203005e45007045140c2100420b084ca241003c101c014050340d803050b0b09000f410002c14542c44070209402c41160664240041c0d04da40c3c03a94001a0340c0f1070443c650200d03034a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 636988003 1250 636986753 636986767
    0x40e010b0306150910030b0604030605010e09060a1a090a060302030609240601020721021c14151f030b040309060801120f0204020307180e010513050103020901050d0215 74
    0xd18801e510480d50f02c0c001c03820602c0d10507100e10a0840aa0f08150203d00802419000e600496502034002d44800d14080d507035150101210b03000e07000041800e6200c2c050000e410030410110303070004541202080391094901c070a40025846032407180c0500307a4940010100c40050380200e005580180903140c051500760401512074983c0300c2c04606150740c1c03440043c0b00100c060811441313100c060b00281882c608040c45201604041d83c5407499100801250380b00503154251854440300070781c4019a0700e03031120301e40740b8150303011054044c0b041c0d800505207a42001d44c44501c190054041c40b1060342c14280c80d0740c50000c61280350000b410541401e414042010360007804402101c0c01c560b54075646036202c204101164640340e102420380c00e29201600054502540119042074050074030f00406550540481100302543d03006105032424480104403600300920608001403502100f00300c90760455001680c01c61040c02114010710ba00c8507880210b40381c2d0000500c4201c03c070301110ba00c80078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 636989253 1250 636988003 636988019
    0x2310060f0e06060d050f09070609080a060e031c1e0c0804120c1406010306050606040b0a050f070f1a1b0304080304080f130f0906031122090c0e06090c120c040e01 71
    0x281600e04c0d0156203d07423240061290301ca241580c090b84c091001031302c822507080c1c8030300d000340800342c9080e1940d01040045842c440260710f41c20340344107511240401c403420907180c1001005c50a810050665040040b010000381d0b00809071b641c0590320a2032807020094400040300c034000225001410440e118111594800002503154100c0c3d00c50803080c040c0ba60340a05024850040e031040f00c400003000e009040380f083c007440c003801030a810600800c0c100641e5841e441c50009880360706031152440340764107a14070810180380325444020242c5241485441c01c0c2c080403030744030003003014014900200200c3e0411081008640b018484082c02c039840b001da8480c81c0684056520820700560f504540020324075443d03001d01d8044a80058800c0c1d03421400c44284a400080e086005030407440c2a04400c0c04403c592144200d00d038010311103603d50f80d0a0400c0c404152101821191040410034100242c00b14400c086407044070a2610020f2691203107801c0d071419000d15040102c07644800000821051 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 636990503 1250 636989253 636989281
    0x70f0c030908011a0a060e01050f070f0206220503030922060b1c0c17160c02030708030901020601171f020c0304030b0f06040b01021b01020a2310060f0e06060d05 71
    0x704e000c5a20000180d80c44030700ba614110f142e00d040340400c8003401200045421b00000c1c000c141d01a4801d401c0038041070b40084c00c1980101404262515141040d555220080e808200681000d070011841c008100c000140e40b4501c41500340e18003c44500c01a41b91810380c1c22070300c0107164031502c10762189014207168080002146d1994030312460701d0a50b03441c4502c51b0000c60313441c02d14003034030034069120803c5081c5000c8000510206002c40d2400304401a2070410540d001004d000b000756031070300244d03400241884c5c2e042e07201d00790544503130700040c10b840c0f400305050104210380d1500d10851010003481c10040d0041450362202404081800001d20044400061050100c1c120340880c0e540c403030700dc000413100184241c0340142d00c001d40307061110f101401394800b001014012150b03101100d54407100e4100c1d49818070f580b854034812002030001003c1240c0c0c5902c2e01080c2c0140001420419402044200c0c0d12800300c4000d0f088000c10b43c59200c490403541160361072082800540350003d0580380784 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 636991753 1250 636990503 636990551
    0x11030703091505070507080903010b030610091503020307091806020703092c07050307020c0904060c0801050604030b0a050417120106181a0c010b030a14010c08070f0c03090801 77
    0x510030680000710345060301c2c0300f49449100c0360b0300c42505100580e16401d10580103030428036010341d40c0302c3e14210180d9003007050900c120806507889803164284541e02080e13400404004444520500342440142d801054402c01e40e642d543c0000707200300f0300903807070f092503010314030094891840012001306242c2e03c0750301c0f102595404801041c201c0c800540c0380c0380c070104d262000c0c2d8071491000089211a40708000441c0c2080e22441241c0c1101500030000312070f13040903142211000d9650040e2428942c000c1c00450051600b01d034518241881d40e140c1013007900000301022541682d400c0010b04102003081c410029030001c842c0191641c2420110b8402102d00703000303030780210701131000007400c0c200d0f81d101d980c0980e4003207074900c0090020310240145c0303600442001c62095485020300d040c80e44041209c01041e500030402401c100f0380c203044103401c503100d01b80303084d042040d110100701300b0710341201c1000b0071280f07585480030050700e0b41e00701221400c841d904a201c05500745000c00745081c909002c6a461 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 636993003 1250 636991753 636991763
    0x705161d0606030601021b010221040509010509160c08070803040506100f0b090d0c150f17070c02100c1502040503010b060406090b0706060b03070c1103121b011103070309 75
    0x309444480400940b03010440f5840c0c01a88884100d0b0980412107070b00302041507041c012a00c104d1400e8981039060395158111180740000454100031514150b50b86600621003620302c06402d0410a000100e041c10311070854080c4031108030f064041010030811112041c1e0003218258417400e143c6070454135580203540d40d03170400e008400c010851041c00c2c0f480408440344a0f0215181a07940014441821660340003030b90740f50203064001070394030386030580b44010f6000307a40d5400d07055072a04c001820104040486406e9031100c3d004001d9026040542c03040210380440b01150f20140c103110403200010b5554006016201c170b1a103403080341f815900a007013964001c40003030100000c2d40b000c0c00b90a000b1407040b0b400240e0740800801000182d1401048828003448001c200c6941b07030319114074160301c03c2e00d888000a4035140c807041842000702c420b441e4440100c018120101100003070418170301804407000c141c40100085c1d40004002540511641903d101c6116124940300d4005030040260b0f030380a481c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 636994253 1250 636993003 636993059
    0x40317070b1806150a050607060207031706060913020d06171203100909050f1906180506010e090118050d080906010b0a050904020c15090c030109020f06070516 70
    0x10b18030444088101c0c0d45a101c200901140d0340d0000d103c42c081042001c0349030808504540815652201c600034141d0b18003446000d80d0b50345036854014a0031f070540d160030160001003000e006035a42d4030000c817084150200c607075203c81e0b00795451a000903c034a0390181503441ca00f5100050703008000c2c0b0100c0c111690241514100724420301c901c10703a84001c03115464403caa00300300f88076001c115480001c00700c5c0070f50210740403040c104040c2c0b440d041d46103010100b1040030b40d2400d42003001c1070295603a8035404510142c0c0d105901e03501d055550006000f2445c40504040009048490940c400301c031801d010319004045000a051032038468002856500006600c0c600065460500080080c1280e40030702c0503c1c580b0462181c03c1300c2030b03000400d00360b074060f400700305005030780174100502a10a5070b52081c1141c50f00380080c0680c07034000071906440c000d07410603498801591701d125100c00103110546149586040e1071814a0420001c12880c9520300110400401c802205101007039405a0002c5121 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 636995503 1250 636994253 636994261
    0x120909042406030b011202010c020907091d0916050d0213110f0c01050a06050109030308040f2001020d0f1b050717030307020105090a0213021305030303010b1315081b040317070b 78
    0x203080321266000103030100d40d089c001000142040b890090307002000b1720b01480340544405103070300041e803a0040d45004404030418030512420038403d80f00c1d02201051a040c080b0318040105410b1161200c1c007034801c12413000c4154901d600b503003000070150040b800b90782ea00c7d81e0307070f911414140c0c20041d074100c901d600e03120001e85198054805c0000351203050b10780402d5079141d81d030100c9100c1001403080740d41c0030716400c20070700044050030018144426019680203904810f40020315000700c94403003c04020002e041201d410b5089211120700100c0040003030030320318060400500d0419903602034058004003081c10040d10304040007a42c002c13001c603030080c06151542e0520703560303400c400e0a0203584400003000d0086501055030045c9000e9851810855000f55100002421a00300368030004110740001340e0704a500300c5008400c00a172036800781080c811310040000030070490b00102414054082c08801c00758800120302039800a50740030703a00e02030b0b40302000c02080054000708012694055130700049 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 636996753 1250 636995503 636995519
    0x1110d021f1103010e04080c030331080d090602090901121e0209060108040f0b01030c050301060e0c04150210020406090e13030e100903140618120909042406030b01 72
    0x40350981c0c00c03046902e411642024940c401504000e03004442d505001c00102201c2c1e6800c0c4040c611850f480d1004988101c15103080240c4007d80c910b442281c00e41a203207039800200144103480d20401e94000000d00704225141000092181c2068180e0111001d8000201d005468481c100c04901c84d0800c04042c5428491413015a400508000d52003030b01000019025441440880e84c024040d048000b0101015140d000000c1000c5c1c0060341c03c404006001d10241c1024003d620092210030843c0300680b4200c40222110f02503409044860400b00261602191081054018103160040115070325999980003829103050361042c80869001000003400f00302c90901824651905500c501d250302810380200240400da0005120501c11044000702c04070b554024490900d02e1503034000e1000e414250721807a80c00140d42c0d01c090665201c4c01c0d28a001c200511309503200210140c0d1503540c1ca40303e51a0040c0305044501d84124003043c103054040030200543c011600310780c01400e20303401c640d0300e0f0110 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 636998003 1250 636996753 636996761
    0x5100203030a0f0603081209011d0c06070c0b03010e07030f020c03030a0902060c070603020706060e0705040e07090e0a021903020f04271b09050f0108070e01110d021f 73
    0x10140540c009000144008149421004803080310850000340980c40341c0c2c3d2000d05400015215000c200910100003510000748180305a280502c8416450a07000c4850340d07079503c2c4070812150007410b000c613407603041051442d18070010b400c0c0c00602a4484d03841f5124401c603014201c5080c400a030404181c81c200c07600d43e00c00c40c3d0509200001852039aa101c003200313000307441144800c0b030b00b1520070080f40c11013101c1806941c020701a20b64003d650b0307001c0c0341030080c07e96500e60400d8019208010500c20705c550408101c4046510b03040f0302412a80e200c190a4802024903400b200350034007500100896040254001c1480b035414945903610302180d06801c4003240228024003a050a007040284003408103540f00c14940388901c8000780030b030380c007650031407041c0ca500d0b10121210003a0041c0301d120982d0005404406410192901070700c00705e0150008003558006400c4109000742954020b0050740f0910b0a0034001c04d544007110a20415010025590b4003507038801504c40c150303510034501c0f40985020b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 636999253 1250 636998003 636998029
    0x20f100621110913020405060a0510120207052d3004030c090e10020a0815030f06010312110313060809070f15090e060102070312111006050a05 63
    0x2012016910212070110010744040d4000e6071801a40c210380400c903560040703800d2050701c0c0900d51018588461042c0000d64001524403031082000b001c00380003945035003070740300100c140c24038102004491110118009108100024005010710071894025520407484420720444008042c1c400d00307850389095448944a00070300124100ca006e1481c0c491201d1141e00d421445491009460960f6a80d9201e01d00889a4007007c40c1c161070311100c0300342000500ca001c1800c10210703c00d602d0540d076408000d108800007015444203090601d00300c44182c4003000312002d0a12840110750565031682402c8000da5003000340ea01c0021034035000025810340c04010342d6841c84503222180c100506010382070720740c0c2000801440c2c05100d50301b000102c454070403107840014940c00d00348101e40d41250000a0000d59607400240788801143d003405a240d9000900800b00ca400201c0c42001040940e000c8130400305154100e4090b00c00c003078134106889183d622800484200312100c5a400751303204240011644500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 637000503 1250 636999253 636999269
    0x70f0807080a0e150316180b030a0606030e0f030901050d090b040311060106110316080909040c031130030c010c120b100807030507020307021002030d0b06030130050d020f1006 77
    0x2004501d03440b40501544c4511100c01c50318807c0140d11a00e094505800441d240c02c640d0b5180d24007080315581610a407014074041b6405080e081d051b0441c0e41c5e0350b0340300703c0060300d0400000290485031500707154001c01401ea48002001483d040500303004152030000c10140b0341501425000060342401000d10213201e00400d005141000c3c40c88906031498600c111081c2d511480800211480d95545e15201c0e11a42c403e000021445041d41010030290191003181405030840c0c54680724050048a1440b4404141003080282d11811051312802c50242011040c3d1030b60a003c080310105401c074024208203881c912040180c10000400c001904244a070320300e0100320307801c0204004d02d10903004960310581c4c0340101c80c90494550301080c6082c820019410041c3c00216000d0302c903110070b00030889000811a510340c219410306804c0301220308122141600d141201c0460a591540a035050382841e0300602a03c030314400e007030030203900c8195105500101c0d000d024a03d030903040080c8604002c0e90040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 637001753 1250 637000503 637000531
    0x20105060909030c1b0f0319050f01060b030604090f05012904020702150d11040e01170c0109050f040b060c0706080901020304050a02040e0c040509010c0e0411070f0807080a0e1503 79
    0x3030790b034001d003288007260f0300703500031044165070346ca10740b0200103c900c075210040d1000e40031146801c0c043d0a000d8040740d40c2405e41d06000003001490224800e0302d4000108480000f00b00700549090040c40907a180020125400d01640044003403200124a80c9a840354607404040141101000100c1c410754000a50120015600c80400f80c450306c045c0808180c0303800000340c14031072803c2c2040c80f03030015844144040b007010010301a410791940c0000074090200300900e83d00d146180040c01190032800b40ba80900300c15068500030340d40c0c030b41040e00e030b03080054001d55076005131118041e2101030a0140d074000c580035002090211b081403088030710030358004000d06031000642c0e007088003400702d292040c01d032441040512a065071b81d0307101c0d0900981401d40001021121910082e01c0540d50b050007a100d180783c80b50244800421504030317013141d50310441701d010b0150315161075045130091400c050540c0401240841c030f07003074100c1c0c110b030701c1d50781c00711150141e0b0703081081032900500c422220f00c135031030350b071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 637003003 1250 637001753 637001773
    0xf011103010806070e0a0f030b073f0216080405120a0f0602030a1415030601050a0602150702031e03010509010e010305190534060305071b150903020105060909030c 72
    0x1c0340030402500e500050034a0b6070580e680c0d151f00c41401d0241c00c1500d4a1407180180050540c002000c0301c02d01d01041d103141883c2e40f00548400600d030291800c40c40040c0c4003940160404e20b50360441e11000a0f090740f00741010031500b4a45610f401070f000e140d00441c45088020189a0005027504e0701c0b0380d01c0695040010300d02d942d8000070b9080036240c41c2d0003941b101e85a401000c2c01740d10080c41003001d156070140c140010360826240040603405140208018201441155408900742002c41d0f041490358810392110f2604030b14602c40c06c80c045001080415074481c2d40c2300b8000096040351b074116a290403598940d41e0344501400207100050690b070000101c403140100e00340703091781154090382c01d840c400400e90414083e60414030210364031690b07000001000700b1102520303001c00342c0f200f441c0400891811a0014111050402c1c034076035048480d0709900100020008840954904094144020030f45441d01030701a00381038807400d203d50342e11030004104030000025506441342d4034004080040c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 637004253 1250 637003003 637003007
    0x303070c05011b03090c0608072c030303040521030c0a12060e0118110310230d03110f0a050d050904230103290106080a09060e0f01110301080607 64
    0x5032400201c0d0255250007800a43c4014112042d82e000361a403004640c0004500d00468101119000343c814000c010040c007419607400700300045980318540042c1001c02c90b00603001d015407440460b203640340c8000820082040703404104540c9440404207040c0700d4ad20241c5e14900103000c125101802e55a00784000351105215542c84411072421440004a143e185c402c030400c403030300982007511703101941403805401d00c030503109800f0100c00c2d81d0522400c2d402c19010034000000a48544800020381103920f1005000d2054818003c0c000200800c1e0b400d012481e0240c801250501c0440325400364a0036140f070340b94049100b8108035130042c0a000b242440600588082c1c004402c441d07003090390ba0000418035a4014400680b00c440d0b000002550740c514030303051040c0885a4040b000c29001104d0500140c00a42e00440c152902d03070512040c10b0369148890340060200c103402070303c8241400c02000c00c80201185140e8900c40b024001d0103854550802910310344802e00c074003e1558442d000041400e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 637005503 1250 637004253 637004267
    0x1020303070807030b040515030705012a0c170616050a0807030f020408010e03040f0b040e1603180f02010906020f070909031e0801140a03050a170d0e071511030307 72
    0xf11810009403d100d540302003001c440c4201c458658030a080700700d4111900c1d042100d14002d0070240380004031200d041a44031b5032408042401500054606c07105010070040d90001d00c06030144c01c00d10042882152541c50b95014250b412403115410303030555a005a116000b241c80078a40754540c60219140c00404900903c180c66081c540c86601348404a440107080c0642000113810034015520b440c1890100f42070085140d11908808100700002c00141320800c1c2c90030340c0150203030300ca08030003070b130411064000e0029001006007000c40b01c1c000c0c8003082691802c52503864000c1c1c0e20000f0319515070206a950341c075074401a0032590301071041044074203a50f4100444e0103100385071031b0081460341083d403c1000c080003890030201c0d40100c01802101c0905800d084843c208858902240b440d41d15039948440d03031001c026044800b1100b00d002d104105001300d80c81845040c004010010040b4001078541c001d80c003074403060341c00c03420500d0700c11445200210307080e04002001c0c600c1c41d11007410680e104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 637006753 1250 637005503 637005511
    0x50f060607140106080a150605030a051e0c0d230d05180303070f03050a021902010507080a090807080309010e1807080a09080a0905190303230c030d14090a02010203030708 75
    0xa44d02c1e0800810031100034400c00d0101c6114214203c000030070138594400b40c1d20240c0009020764401c160420128100042040568413040b01104512140500544c1040100c9900507002020100780d4000c05c00081500310f050328000c1a4504404020b59410381c98034440d204500001d2002c4c0701840b102c082c00c6221000342d001c0142204d180081c2c5949a01f0418072081d400e80c04640041442800c0a4042c00500482e040c0070043c4045d0b103d1560010704039000d0190003812240e00411101103003405800e401c80036151079001c9030816541c444035144c1da940082c480500050300c0302441c640900f4100110051010110074030201c0d9541c10341c00f12400030b0000e00008280740c5843d14000410754090003020b8121f181c4d03032000c0041d402e003003d0124040b4600001c950782c5103101c0081000ca580100340c20f5604a0f00b00195012040402c90000103000310120944503000000c1c02c0c2c12600402e40c40140280c0e588070703a0229036039501041f55142c0d4030008020f80942c06c00c00004081620400300f0540c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 637008003 1250 637006753 637006793
    0x4110f01030b03100e0f1603060e01020c0a21230c0312012603071106030702010f051501031d071401110f0c0405101802070f080307050d050f060607 65
    0x182d034030b240041d15010031002818000c0e940c5000505c1020001d2049210340440c80b40201146a203207440401451000c1c440900690360700d0300340c000c0011003034048600c10b00c210310841d84000d9040c1030445070194505002082d80c140061413031851030140c11180030032803d440c0c24242d0074601440000f61940300c0094880d07140000c001c5d080100240c0d484642c0a06040c1c060b0b466016080c0d904101400c0d8080036100b403540c070900c011b0700003c5d102801c2d0758644005650940d1691030b481d509034050a102c3c02c041641c14200070030010588200781440c3c3c0030240c02da900b40108550640d4960000e5034500c0000004e80042c1c00c2070200b100d0081c82c0c190b01d8101850820740c80200d640001c0e0522440c001410007030303002074010440e17912342400f0355500300c0e0000d0301503d411450001c400d40040140521448000c3e004500d12081c00009800440c0690f0040d40c61075a034546508001c01944c800718610385081e240c000495500c0301c0d02c2e0310359031207420003500a03450000c007600e603500d8522400701a200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 637009253 1250 637008003 637008011
    0x30618051017030a170c07030c050c03070602030903120a0206150105070b090a02010f08060325030b010f031b0b070308090a0c0914060405090604031d1c03080601030504110f0103 78
    0x252070358102c0102646560340300c001c3c646a00d0f907000010803525140d100044404454000d020b400348507603040340d00465050070302408a02007440d046041021a216203545406407030740c0041c07001d80220007000341c48021000c0d0307072030380c4600c0101a805000d809240401a400702c8002520050a2003031144d04210505003a4180301c010340e50040c00d117600b151086000e8114104210840d60803450310090440242800300da103190580200366500c0040c80008a14040301215140b070000d070070b40540186410014004c0a90b8680082c01031881d0075120841d1110303890a034260100658441100603100441e5285103045900c0d242280c002c28068881a0039004001c1c0c00710000d10f503c0300881c0181030043c0040f0780e844054640c92840200203000030b00030341c10030b002c11030014000328001d030340150700d810700c01ea07500030104000c0c280c28002d25509030005812040502250001500c1c3d035a0307107100e90f80b80c40780c9960301c40044094030f200750340080c0b100c0a032040b9491240390100c1c44284601c41850009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 637010503 1250 637009253 637009259
    0x21b0f1914010f060b090301052a090d051902091003030e0402090f0406081b03010905060609040c2102090a2912100e190506070f0309051509010506010306180510 71
    0x2200321484e5600c06a45814002402d403102d003000c0c003480d41c0c03103c0300d03c030b1510f00403000c44540c0101440c036800d1088031600c0051440242d551390201d0280440e0481c08441001c0900c2100351241c484188080e441604010001640644844000c0090301d90555a5094860210003030101079002a81240d80c0030110082120458507184100b030018580b5070000c2003804400325004807100d60301030846010381d0402c0f80c54004508002078107a0084411b648401131980ea60602054201880e0040e480e0240d030043c010541040074022000c00310b0007280c0444240d220a00c402046034074011003034a14180360b01c4604150880c651922040d4280500942825000490218100b03250131f401000c2040d5a80c210340e80d040350400c043e50300c03490400684180041280c61b802e0781c1c0c181c000c04a00420036181c0c00f1404c0117203e13030410305100b503028044607607d0b048280d100e10466000c40305803201f5840c1c0390000c1e1003903109025440c11501e0314030700c1030102211039251a0241400900b0b8042110f1124400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 637011753 1250 637010503 637010531
    0x4081e07032a05030c100507031a150405090709060201050c04030203060609190c051e0c100b150304030206061003180206070503220f0b040f05060702011101021b0f191401 75
    0x80c030680111710060710414243c01c174481c007101d0015181804051905481e031014a1382848001e60310395003200c4160360f00c0d1042034140254800c0380c10464000c007410007803151568100e0300800079505203400074010707541e0f0310742c03407050900031484007a5065004502041060800481490308460041184900712007161810b0094581d0215880b000a40004d00c00000340b50140600004421002a045c9040100550f8542e20040210300e9031441d55944030303410040d941e0b15244030354020503240032901d81c0b80034100030351039820483d035403401224000b01900c85d031403007845040a21282980300d90a41c04941d020f0040700d41281400b00c8192204002460b04200c800090b05803001810b00051074141c240650400300050356841f44000d442c082c031050000c0c2940385030300b00a0b10000c4c3c03911a110285800100c8045001444a2003294800900b0640c0c03e80c0844140d1481c60200c2c046900314035a010955965400c0404021020301034031910000050340703120040d29420000700049a060a01954 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 637013003 1250 637011753 637011757
    0xb130507020a1104110415022406190305030313060e060f06010f08010b1602040f06090213062a0f080301060f0e01020d0c080309100504081e07032a0503 67
    0x4005607200241150030080c1c2406100700740c0d50165005d00941c8500070031030080c1e016500800c00c20880f0442c440342c11910800c8640d01c0c0a02c502e4440c03a01c0b1001c0c01419450450a581c217070301a01e03107030294003801e40000d04c1400487e0341c410300840c03070356490300d42c40b40c00d00c0040e1108441042c5c0342d5403a12404402000a82d0150701048001b4116013002800540092154654001401200e500410100403a030050340c2010380300c440c0201184c1103e10004008141140600065515058001c10100c482c0d0340a04041c400301001c40790315907250f49003607507111011106071021407108502100341c215602810100a8884d0348082031403441a078800b00150806d0300040c00141498a02c98043d030741c40240000d5010342800030309501d12030604010211494102c026040d03030800004a00c0c81c02040000c1400344052840030005421b140ca0400181e6000301c41d1900d0300c280618100741a5102c58040f22400e541c16140c2c95240c01d800f04014265480e40c281345000a40d0541c0307140081982480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 637014253 1250 637013003 637013011
    0x180c040e0f0a1404030903020d0303020f0d0e100207020a031b0305030408030d0c030606020d0f020c1c0203060a1413060f0c0305070807090521120f0304051902130b1305 74
    0x107030107240ca440c9041c0d10440720400080954515404180804280c00151309425641c050360380d02c0405a0a0070140c01921030b80c0c005038440d410000b500030103ca400d5028442035810502614400c01000354240282c0c0502680654044c120b5036007040002c40035140440800b03088845100303c1541d0b600c0385030440e000f9510000e400c0d040060035243c01c02c86031290440314102802c0c20019507041000003551080300042e02d0051214107a141600c0ca8001c02a0407200c102c000e0084408200e510702240d110b050200c0201e00078410140454800040b0740a00c00c908010a080220b6566901940d148036250040f01541d150341d660301001002030160060134901c6941e81c5021482d824007a8004265041c000c20b00410000c44410501c5150756005240d0b062491080403c101401c60504890800001030207000220a0010700c0c44101e04004024610030b0f401041a02e0707400250158110b00d841315520025481102c844299160003819071100003564409480f0140404030110031204032001a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 637015503 1250 637014253 637014271
    0xc030d1a0901030f0b011a09130603060c0c0c0f0506250f06021903061a07020103060b07051f0213150c14010b1309050c0f0d0b0705090406090b180c040e 67
    0x141849044c02041703070074907005180e01c4100c5005c1564240c1112168015044402e00c10030068009111820322a0011400346401c0b8038100071850044201a26444050108a41c906166500014030f0174083e442c0c802190030117413925281c64000f004100010301d44814020a0450260712800405c4c055800b0303407115841503c005a42c1c0c0200708007201c14204c00b61f94202010308111050082d07010005810b45041040c11001da01c07002648010303406842c1c0768000304101c2d1000700d4100c00784040050140d41525240d0805010302c2150300801e0103a00c03070b840052210141402c810014142c0041460702184114a024045280c2c00d9440030381c90840e45000c003610340e4441c00c8840d400d02d40300714915680c03a00301000300048156551403076212111450414481c03107074031502c140951240319100202236402030180400c1c4c40d00500141403904060303182c5000e00d1030312401141d500c42c1c80c070a4249001c0020302d00200780c82a02d024581b00d180083c0840740c044402d00001540381c9a4400f02c0d8000d1141c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 637016753 1250 637015503 637015523
    0x702150702030406200c041a060c0109120c110105030403140a0e01030c020705150a020a080708130b0c1c0e100903020f0604031a1b0a020f0c0102030c030d1a090103 72
    0x2040051041840e1505d8038902c01d5007284040146400007070b14100d84005803000300d10b1141e48640442045c50706e2070b40315084680041d15801340441075014000552140c600200002e41c808404c0f941303000381c000000c00d03500c00400c02081560158014580c000e01c01d140280001c05d00050b5460150864054200401d400034010b0700c556815001c0c05100304500e2000340b40681c80d02e0006a4681c0f24410701110f20720000466403d441c0c800c0c0241080301c0e4004540356514155032800564980c0131b021390429a0324081d0020549418040c1115040d00e54400205a0580031050b1b940e0b41c201c00c00c41560030b104010045017040e44501d01000b4480840d6112184c2040c614010b006e4400f003405895441402d08100a1000921300100c10000031508010351200faa11610703138010380c0705880f003003507110000490b10904555000a452a8031f8010600303903034416a5490041eaa01c4c001c0841080c4503802c28415a0f514003015488007485000108003c8141d035481d001107500d503503081e0003d030380003500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 637018003 1250 637016753 637016759
    0xd151502070b090f060d02040f12171614010e070b040303020c04061a1c1118030a0308060d020303040f091d0313050618190614040e01030b07021507020304 68
    0x41c415040240036815040e0302e0f09802200154000c40c80384c0000f445604046400c070b0450090746d050390050b010680c681c140442e1a0444854640700b8000c0480f0441604003c01c203580c0700b10001e40b849480698103800c4142542d03600e60038084031b0040b80400b10740d41c42d81c814203200f80401c2540700904160410b00c0d0b5860035810001e00340394000d86014012814070004101e000311403040710804480070b810b00c40e155240c500744c086000080c40014071105080c0681c0044800201d002001e160002c1c2c040c00d4010051401459103d5840352000b0700801c1204000038407030704242154510700d610003004d907460561a135400e5082d141ca25041988100da0f201740128203484290084000200410700450800303c41442c0ca0511010030300501d805800302240c00c2d842d0355103c100ca0940180000d040c000c80600c110042050305807288075580010f282e0011001c3c0c48185201150b0a4500041c050345d4280e085480d100a00600901ba4004501c55041c816813013400c0d00002c039020ba11940e0103140d44500e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 637019253 1250 637018003 637018007
    0x601060503071101061d091509100501060305071d0102010e060c070614013002120c01080a090506060402090d020d060b010f11030a2307050a0c1d04080d1515 69
    0x1640d00d1011a44c0e0b140c61010321000501107008032104e011260380d2080d03039035985036050a141c074011f0311100740104041403148001002c902110b840740c1660b02000036a070b0380c0900300e00341e03038042c0e8059010609620944d1030300150320a41c0309260f10103000104610304000c00f0189480303411070340071824020101c0c074141046074900076034080c151080c0203d035865040516140350342044030380080242c00840184200e44040c0a62039040c960010104900e001c003014001b9190040c010070079000801c1c4000054522241d48210b5810030381000003000386568100a12009503c0611807551260881c000b010051382c82c040700d001101e100d00c1e408590310824000140c070200011f801d14040c46203401080c02c0d86240082070321002c0d001440c01c41c5200f04a5001d025806410819060a10000058050600c040080c050761903034401c840c1c4a0003681e0f030b028800b01440180b0381034a030010404002c5000300c1c0814015100e0101c6840f4000743c2c4070440b507844c003805140c0d0b40c03124800c180080c1050404903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 637020503 1250 637019253 637019267
    0xf04091409071d0703151509060f0c0f0f060603081c020a270504050a062102030a0210110106090504020127051903060c0207080d090b04060804050f060106050307 71
    0x1050407002880140d04102040c401410b0a81c0303a16404102000028040b03807094100c0c2d460400d20788404001c00c0d4031503920000c150440c006540100301070300c00c0050a144240035072110103a0a0361490380ca0300b510b41d2011007103283c400c019600001004801c4002c5400e521500c0c0080d44200d851030ba68454103100c0041c0609c41c00c101e16240e80c414884183d0060704242080300a40700700e41100200740c0c088a4a00c02c035406074015030703000b41c9010100300c100314040d40448141c2d8009030100e91251008007501d00f02400707080000350550400342501006003480901c006040c9410f061a203686514006110b00719907132503014140554031a0144001c0d03503001203902a2003403d81c2c001d9012100301d96445040ea8410b0311806024054400c0d841510310220043d02c0c0140d0b5110384140413611b003042c8002d5031a8014052a011400b0311404102c1c91030245c1000011200020591410705181050980c0c80403001803003a26540207043c40301d060303803500f484194080c042d0303038540548a00300018018445 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 637021753 1250 637020503 637020511
    0x20c0901120f0206301f03020315071101090b24090411030c04151a03040c210813090b04090309030209071715091b0a1101020f040914 59
    0x8903800039641e1000c100c003040c59418840d0159a455500c01d031840c0001c55514100c00c89804c0009504203070440b0841042c41c2c98050081c02811641030028107180305058001c1c1d1000030341c183d0004020310303a062100b000301c0d80d002d00b441c2840721280410861300303404d41d880c40707030200c406908480c00c12620300c0c0d01c0c4c11206010800b079210804c1720303140000410750080c0081d1000e8102103030a40c4000c0e280d58204403c030580f03040540244060840000f01e0340c8107a80901811081072012003010814810100941317110b680c00c0000d001e6000d140000c018032a8400f220800c00755912003001c2d0303012440640082c000401c000010448413071401d509002225000b5180710300c100c0c180b804040100f544130543c00f013600d804840d62001c640b20035a00f56040340c51008031504180c1c2150801880c04c680d10155086484140c5210b8419a40c1caa0349070090141604480c07078941090094200c458820200c502c4d0214144000614101004e02600315981042d03000c500d00585403000f40c00c120303108821082d08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 637023003 1250 637021753 637021769
    0x4060608031c1802060d09080f1602040b0609010203070b0c070f050606041a1e0409120801060806030a030f0f090305120715060f0501051e0d0f05060f0907030c110607020c0901 77
    0x20f1042540c001005803007219046e501d04c07511503c1c142d043c001034100300c6d40704100524442d9550040c1c080e80c86032001030b50300c0a0f4070441c9420440740b0107040460443e40c0110059010314600409592104900c40d4050301c008440f01040c814400081c0250300c017030324418041d400030324892a000007000306a441d10034075a402d640d08121640c1060301c880c0840743c4000480003000c20034103104c20101d030003070020030310180150140304c40d003c400640041c1103034180c2d451130f625040141c0e502c006041d51401e207014014001080702481c0407505100310081003085416282151109507651105498110800900c80c800000003135040104000d420700c0346020f40a814003840030301c0c6083d0f03000140b00d1041c4205810700c400024844240c0002904000500501d6000d0b0b94541c2906042c00c0001e1840311340c6080102c1c41c00010884a03e441c9076000c040340b1000f0440c03079032070703a86103001c030301520000409c0b0080c000703400c00c02c852905041c04010b1040140303a0040204603052000c201c50348006a0140c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 637024253 1250 637023003 637023041
    0xc03120e2e0e01120e01150b040e07050f09100507050a050105100e01080705010809071503051b16060f090501050405060703060f080729030411030d03020a051204060608031c 76
    0x252660050138111020719150b50008240301042c0c1c1d52409058505e610900b02603c03503001141c451111070180050b40c1d0713229510009603960140544451158425108100340c080c8401102481c2c8550a6050780702d23503290030f904003081607681d603190002c00782003143d10340d44460402c401070b081e0012038402014400254019545001d460680310b01403402000d04101c00c040000d188071000f0443c44000b0801e1124005600e00b4412000f00141801e40e003515070106e80d171403c1c003129003c2d0002d0700c000c2d100fa110840d00106e101e0351410700610040c1e50981c545511100322902140003842254802c07030141000c0d020764504084024221512504125442050760b807092210000008031001581c90076281c12261020101010078a0804007440d1110881d00004020030000300c0403020404540550454200c8065008103506038000d880b541300020700140502c41c140041e07010308a07007050060000140741c40e1076140740e0b421988a0100120110041022500e2036101882441d0000d651141108 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 637025503 1250 637024253 637024277
    0x3120209010801090b0109030b01090f110703120b01090b12061002071a1e04090902040b0a1404090809060309240105060f03091c0908060a090c03120e2e 67
    0x780c800c0b4010f01030581e540b5a5080700440f2039018203005d102440d00000221a03640e0f443c1103290141c251003c0102c013003820f2010141741880010140c40c3e000c1d926464000c0403950040c410350082800000c10340c10880010000212003940b54014000e000c00708a4840884c60044140b003405071a180066045600c0000d0412200482c2c10380340c094022050301207507460540c0702544d00e003028038a024660344080098001034807a400e5000801480c820f55040c0714040c1d041007007150322421449a802d0060781c62140d0f00c00c1d813900740e018101d00340c42980214101010701010503120740080f01e211070650302440e00c2e291841400f003800c2c0d00302010740c1d44690843d81050045400b50055481c8c01d4059000800801d00f01d050600001e0104140401e46c2d4403006102c150050103a030715441180c01d5130141c1c2c0045104e000c01070203600324840d0802d111040003865551a5132030240b45140c10010031805244030140c1d82d9580208070350198188845002c541007910300e05440790400100300d4240400305c0002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 637026753 1250 637025503 637025507
    0x5030306060a0c020a060806030f0105040b06060714070623040b070b040302030c1b01180509010314032b050f040506041b0302090a02070b0f01143007030312020901 72
    0x8a51011003500c10716110311000e103080e00c856400d00402076010380300031030101c0d00c287e011390614230510086048940741e0f00784400030341c2250000d48010b440c450702000081d0075400c001c4d0041c080c19201c0e842a060f203405030550300f800e1a81e00d8000703000241c980010301c1c81d04541103280e00140108540b0451400e860301200314902d110b030400003451006a08009800d00d4000c1c81603c1c004444002521030120301d440e002161401c114500d540480e0341d25000f403502000c0450b03000c0540c0c2014000841c141d00310385401c00022040c0d0030700c0302c0c9484100000303901e2808408211030a000076000300c4d9100d502c454009419910b00901c0710700c812991034200008124002200d0390807981213081000010300351203030b20181089580029402c850320034207020320b0cd211a4024103109000d80c0d0015504e45500004014a910030301c10210800d41a42074009546401120307c80b46040c03550f0388490009540b0b118110315010540c007001c0641100c0c0341081495082001e41041280c200c80c1180b50074504400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 637028003 1250 637026753 637026757
    0x1203010608060f04050a0e0607110a140a230d054e100e0c0d05070216090b0a0515070b040c0e0415060b0405100f02070b1b070b070503 59
    0x5950200040311002c500192165049120b1904000d4024030441c942442e40e070780070741500c1010300b80500c60000040c1441d803068040d06c81100f402c9015060898180c0c45d8050108800100001c0c5030003020340030f0b00041c2c0101480050510034022030805c401c08880803500b007285001c003c00602404101c52900000f5107080d41140300045000042da16040c0e000d10201c403130210a040d1395102c0b6004003241102c075060382c8070b0b11a2681000c0100c0040e00e40d030284112542c00c0e902000464018402411301c007010783c001f150b01a1642c8101c1d00050701c80310300c18441c00265070041c42e48581c9c44101d190036007028044c4001809080c0e0f030621400000c41162501343c0b06000700600347c1c1851002140400010140400042100021a0080f8209400c0100ad407840f200c0c020080c0519208000505000e8007094408445000b02045420190440c0c181c0e44040b000050000f140160b0340045004a00940a49a01820f00704c03507030540412101c005243c90925001031203c50303024802c18001640000c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 637029253 1250 637028003 637028009
    0x50d081f0623040b041a0c07030b0a0e0618010e0105070509010c03050c07030813060e0d0605071806120b09150103020c0a06051f23090910060b0406030b03120301 71
    0x80c2045181071450b00302890b1420354020400c0315280000c0024080b088100030f48180d0f4a48006502102008a5204034070310550030100141d400c00201040850f005680143d4080c0c9851000b02d0341e01021800030b420702c02c003200c01000303030041c6880154101030248a031502c20100d080080249050509020300203004901656042101c0d0070040c0080600c203005840c00130080c84122041540c03a0302d4030460035004401c0d0b04070741c000c9480b00011520710400002c0e00004000d002c039a44800162170f402d016180081280f402e1040000f10104581d507001d2460340200611781d00c885110f079203411582d00395a00100314074413458900d000e002e46194840040e205000090070016a00c030802c4c2c03a07090a1940050340a0203040c500000c00c40810413005020100d0101044032450b10381d00c074292001404c0c4003018554002030204002d411a08200c0001c903000310122040703881e03008500c01103505849142c3c20030440c10f60003250401c1416094020700100b074a08074098038032004401808080707400144 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 637030503 1250 637029253 637029257
    0x1a010905100c06050c0309121c091e032d0905061e0c070e010902030420060c10021b030301030210320a0210150509060616050d081f06 59
    0x1500100700203006a0a0603034042e4418400d1006151030392105046030003c80786c14002d13003d45c1e4081c4850292040480e110640c0f0b844801144c0c0340d9814882c0c0c0106000714044801046815545451350740b140e580a125a2081d600d104045803006480d446036a11b901c00c50700c01e21090449480c0c2c058118111105490041e01d1403a02d80320020000c014402880460b0b400148000038081f02e402000311b1890281c0741c0e60081524a66610303d22130080341310886000c0c15000050829981000c00681d10744a600e0000f4a82820940050042814006021481c001a039030001340c2c140e00003a81500381c0c138200c2420000e54110340c9903401040e0040c05203585002040b00f180e90b010002c500798109031041101c1c0300000180c100001c031420318a940102401d8000d48100300303e0f900d24003414094000c8001c8a07002c2078281d64508000d0004685d00601240d5020005004100c0e14502c00700d410a2031a01031002080c3e0030154980c0034002c0400600106003401040e1000c40e00002e28200250807a074143c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 637031753 1250 637030503 637030519
    0xa1a090c0403080c100603050a210507140f0d0c0618030e120a0b0f01081b01050901051e033301020601140d060614100e03060f04031b080d1a010905 65
    0x9041300c2c1094000d40c60342e09030528241022051000008038055198400d21900300b12215865410150b42e00e800c0c200340009400300040000a101d451010703840c0c0c5041c8046800c1c001551040a09041d04412128005180307040b2040503c580c0d4054840344440312004011282865117009149101c204680c0c1d0150310045440800b4141c100460030040e80c0101d000303038803810040542e00002000303201d42c04052203a15810b69003201114103c5012020507140c640c030f01403000300192517a4024036035000444e011224404104d5400d81c0046200704103800080c0d40740e45007141c1c039450b401d40c04003488445005142d0400d04a0340c00207042815105080380a003085807108001680725214203000800780d0782844000110700c0c004498070310a600085890740c4074003401e00001c68a1030064201e550b410f034090404034240740088401640c211b0f010745032100d183d4452511050300c05000d00011202c003400054141000d04082c0b20382d84085409150044a01f14400e00080001ca15400b4051152080c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 637033003 1250 637031753 637031767
    0x503121003050d39030f0e0a030f021002120708070c1502010504060b0f0a0b1303051b1912110301021c1505030d02061501020a0b0a1a090c040308 64
    0x11500d5444000d5a0100c01c440000c00c1c420320040004403003440c1041c0c1c40700956019804912940c2018004042413040c101c000303000c0d901e003212008143e1801070244000a005030b2195110382d84820059070103001014842c604501c10721001c94075001030039046400400594009450341c0013104c4a14ac2c00c4040e254a03042141025010320340b090b88046a004146800200c1c2c1c40d8041d040705206034015941000b01800440a0050084580910903030010b4550340a00894000401404048180800c10340c03850b9182e6649516044901c8002d236143d0906100c01d001d18908011418800c0c1c110314050122203151940d80041007514101c018404000384000400b0764a096040e50b8042c1d11131007400d44210040044803008103003000f8845844545840d020801782400640d4003210510380e030051290740d4031661004200d8210129a504601860400380c0c04110030f194414089c040042c00001c60b117002210412a1011280c0100d000e17407040010481d400c0322000c192011240c014070304540d90030b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 637034253 1250 637033003 637033021
    0x20303011a040b0d0e060a0203090a0f050c0d05030c1009020604181e09020406090207050c10050f0403120206130201020d1d030106150f020c150d0915020307020c040603050312 77
    0x2ca0f04128500342c2d011504210001c0190000d06a0410180640d452038444504120030303440110307042c010581c04a0100c0c0001404240c8100c0c00501409c107940121034014009246e62800b9441a5421b5102040108003000c2c2030050454501d1950020001020b6560108403d070140788246070b103100c0118414a0850b14075040209450150074098152401d101c08060080c400c82d4001d80c01745150800115003003566100300e0f090315820000401300000e41d0000c001e410600c081c244005c11505019891f1202d4036980a03102440c8668242d0401c040c144100900c0c011004240c3e1444c001c41201c04405030740c001c11070b40200107047c5404600f140300030f58407900d95034101c00c1d02c940540c40d00e000000c0401d03050b000d60135942415901c4000803c038101c01203a4410f1a904a954454440c0c10f001c5e1800b101000100f2844500600114202600703031110400c204100d00e030156180e40002c00c010b1400c2d030512003a0301500c0f00b140c040000e64110749960380d40c1c0c0940d41492020071000c0010403103440e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 637035503 1250 637034253 637034257
    0xf04120519050a0215240111150a0c052a0c03100e060609040c0e0a09080703090317040e010e0603010e0304031208010f03110405040204020d060303090510050a020303011a 75
    0x10a407804404020481400010302a0388034101c40070040c052241016111001c2a4029005084a090100141544564014220b0a2200030310705111640c50710b100888401d0105036020fa03001d103c41d03002c5180c140000d80548005071000d0f000c00c10704100080c1d00001c0c0060745000c60500d081400c14007405d01c00003516100e400b42c8001c0e0705100b40340344900c08244540014803050b011000740c6034a038491005100602d04103440c01454481c207550280f007400701c800d4560741d009503018408940c074100790302c2e5411143d00c440420703400101c0041c018000c0c4039070148292590900b04403083c0c585032030040800302841c01800355500d03c150060100f0000e6400350070003160410310704292a81c0300d13640d1806000b10755210029070301284c001c00002503c019460303034103000c0f41c1d0032007400309514894404000c018680100102da106500740207a000c0400d00b44581c2010b1071003034903280100e42c04d050402c2840d210108901c820070030100000305542d0b0f408400e490454044018425070350301400300c60b100328 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 637036753 1250 637035503 637035517
    0x3021309062d0b03010905070306232409060307052107060f090501140a180b0d0608061609060503070932030601080c13020d060e0f07080f041205 64
    0x20300400000c0194030310b1030041d4465884511a041140218010503d403e981b00d040d030281c26134202e81000c00c04034205411025030b561030490118882e4034060070031b25110206440d0b0843c088248038074500741c1c002521100081800c1221580c070355241080000f83d440e0789034003800b40180d503410440184003092411880c031111240c1c09580d81c0c01c1d01ca400040c04000034003800c0c00001c07010f80c0d00155a5002c2c01038022900f00ca41e0880d031074035220202c15030b48a2104045d001da0040c1840d400503c0108810140c04100c900c1075004c101ea600d071a1002d868503001821450300344401c0b04090b84c5191b0001c1100c0111005230905070b03103170740d120101600da5030020740c804402c03884095461000652041c01c901f030a00421500581c964011a0916580310800d000383c650136881505180514649030560041e503104034400540740c007446508080596103194040c03003404030310005016100c0701410340250302c45042d00d0314800d2454542440030520030060320140c4060001c1c0c1e1804c1038584210100c1e280e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 637038003 1250 637036753 637036781
    0x203030408060408031e04050a1218060302031618033f140a0e0f0d0f05010504020f090c040603020313121e02010c0507081b100f0c090302130906 64
    0x110f01c0d19003444506540110b4200d0032070a036400100c1030f40414401e5442c003031500400200781c10b801c0355a030f1130425015060580e007030000303211a58070000644030b403410140401d07580140c0c40f424042c90340b202c810042c0180c0420b00138001401101440d20250380000c036500445992907201c811031200c41c1e080070000b44444103d41822070358000c1d84031503018000f01c045982c0d6542d08084102c80c0171711103010300c0750325a0000e1303040200440f003480c1c14091584580c1004000b071100600702e603151040083d04200171262651502c0411095280c0569070b48441c500c2598007020500e0704101818043c4607a002d0302060560220100700036207003005480e800c80b64007511603640b1141818002c0c04c00c0500c41600001400c80b460750120300c0c3c0c41801101b0b4100c0803600c500d4106000c0d0383d5500c1194110f01c034088440303404840c0540791010100f00e010b201000c150b00000d0702c8035240804405542d1410040000d01a48040400051701c48007082d6541000e1a040040d5004007858030001038400c404181c50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 637039253 1250 637038003 637038013
    0x3030f09150906120709150e0d11030d030501240c08030c1603050706050604020c0c06370f090e04030309050705041109030f0c0105030c0c07090f02040512010603080d090203030408 79
    0x1030750401130b5840c58054034041d15a40300c000c0c1c1d18411170804181082084000803000c81d9491042d06045030368180031445035040c86c120005420129143c008044000c9000030b4540004204520b604440541e0680709000e00a4a080441c14041d1504400c058014080c950000001e0b0207a46444260b03941d120740c041d02820101c449050003015508075440550312903140c4008102c007490705201f103c0034951904044c2c985446800d04005660b0400c3c80303007c51b103c4001034001c1d0188850385441c0310200007061400005840301500030702c08581001ea00050001049080c08409070400c1d4041e40b180d850718000c2480308840c540181400c803d0791105400038105050011500c0320b41000c0c005410054044030b801815000c2000d55520744200d00b9804110100041910384105000a000c0405844210740c83c0a41c2c0c1c2107588200c80040b44c020040316400324051103e842c22920701c00c1c40b0340380c0c1ca00a120340c906684409201d4450445500300440c1d65003007020440d1424800da800034185201924 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 637040503 1250 637039253 637039267
    0x4030f0e0334030b0a020a1110140106020a1a040f02090a061d01030f080a1e0e090a0b130b0130110c06070c021c140c03030f09150906 59
    0x65004803600c01241d031074041c0d42e50004031500c0416038a03400c03242c00100c1c1c41043c0d2140c5064070000d602152840040195200744d004030724208000504000c540342a0020300320046285c80ea69424060300184219004003204502040e1841d4141c0c407203040b4409128810748992400c42081e400c0703480025002010042005086000d070381c001800c540016806080e070f410015540b14504000740401000d4448500305440456810009810110341c4c60402c4071400d447ca40c2655100070b0442074580006114030030b040c03032508042c6441c03a0800309420040c043e50048400140000380007031807807524107a988101d410603a204641d94080900030711781404207454440e80440f00d251140290024050a0100d2400100c02d140101e5040b00080000340106813100c2c0d4040703442040c0d03840140e074001c010341d8048a5081c0c400f4100d400142c81000a900410002043c040c20301000c2c42c44a442074000744141d0301a00500812164100c00854090040c4052800d0291090107082c0308503402c0796000c6608 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 637041753 1250 637040503 637040533
    0x70807050d05070f0206150a18090c230402120f070339050a170406060b03090606010f02010b01090911040807030318050a05010512041104020a09140307060804030f0e03 74
    0x10400340744d05600340c40643d507601030251100c656031702c5032035000544641300300720354440d421803d8019a00c0500120b4800e889444a11914000d904084604000c6e9949000d100080344200c00000d5000d460540c2003401306043d500a450008110592501403070000a890303503c41c5e80b0179800d400c1c40d801040354411845404e4070560905c103180e407002903001108550610f0080c4140c40d03c00e2074036070791074050f0501107035036411801c00600115a4a6218400412a03460000245210300005001000f091034400b000401c03000b0140c04903000d6924003c01740f4040d9a214a0100c266490000003040615100300800050300c196840310005005204000c01050740c01101e200311444030342011234583e51900308001520b040f0f8440d05020a104000301ea0882c0038049240da4014007440d1641c101c0650103010074103a910101503a4000383c0c0d030301c00910001b101c20b450b1814942007640100000d0341094030283c40102c0c0a080501070000044064080c98071824024400100c05800c3d01c411307030504054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 637043003 1250 637041753 637041767
    0x4090f0e01020d1406090c0a180806010612180510090503130609082a01030e0a020a061115011d10080d0504090b0405060f010e0f04050408040503061b03070807050d0507 74
    0x6a00c13032044800c0042032451403c080300c180180e001d00c0046c1d01d054005039082da0f82c41c10802d0400d6180d514003030000340c4800300303010b428001c040d681c460740401c081100321141100c00100b43c40000d03030381d03140d40d000c041000016406101c0c41c00c0030000807005614104649540100d10041e80624000503001c0340041d402a00d0310b04480c10501100c104101840c1005000c0e282c03201c21801c003036a460490301181d03220750010318020010a0aa405e00e1803aa004078407804003036040040400ea410072219058002040710014140c0c2100c206841c40d414960f0560f6050312041d09440c4000c224000f04506038100901d0400500c17401003180c00010b10190050a01e8209110b02d2005524058200c8800d0800d0700803103100d0f1100904444046410b900103481c201000d000380c60300031401d00321100481d1640d1003168003030383c096400039071620302e000c04161802200034010001d01003e039a2090848000d9401e40e038004070a41815400ea80da000001ca40e00d0086103007038031381e50307052009011a141d0400d00e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 637044253 1250 637043003 637043021
    0x109050d081021030f08220206040e0f060a08070b220b031e0f060f041d030d0f050c13030f030309120309050607090f18180507062304090f0e01020d 65
    0x114140e01c09a4a102921546c0080311031064a40d82180824a207295501510b140300c2d1000b4811814961514030030003001e4002c0f2030000c110740301002030201903d460b02204004041200040111504000e450400c2d4014105040740d4a80c2d81d040d2550401c5041c0202d0000c0c0c11030031001d50720303450030507241101d0b1101810300f11482178420010505101c041c86291f84140e4000d0905000c41a50303405002c01004109001d4008240c80912100030301c4091005142c032801c1e980c80880c01d61550180e800c00c42e14060b01000c0503140c03c100c02c0b08031030081e4000c00c0c2203d42058034444080d49500f01540500070081004000d40fa600211040a0b81c26500140700c146c000d0040b07a280f40e40d002410f90350b20450f401044003d0f00b11107010409801c0d070380c2140c02d56180b01500840c203001c90b001c910301e1030410350701c088865030020a824030200742d001452014000c81031020b151200c8041400c60101c1c032450141c800020b450300c02c29880794110390801c0c0c0c40d040105008660310b41402c828800100f1000c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 637045503 1250 637044253 637044257
    0x4060e03070f05060c0a0b07050a021513020d0f0c0608010305100c0203180a0302210f0307080406080921030712270c0b0a050316020109050d08102103 66
    0x8084612410001918001d0301d03001410048041d00303080400046410806900c1c1e480c0c840e10707480000013101c80107803038000e4205842d620340b02d606140c806820b180070b80c480628504104020090314114501040c04400e405840c85000c000b26400d150080c0e14005002511020084800065855000004a040740d0050007075610045000d8018411348610a00c3d03030005a0040c4880100801900464502c00070000c1c640c50b2404d0742c076808124602e0100c800c1c01c06071840c02051200d0103006108c85a9580c3e0f0f81005945803080340c3e40c07400c269008070701814080140300c00000b40d02c08810801c3c02c0343c0c5506030200710304810710104000a41d034000c407500400521140301d0304030041c007035000312220010180021101060000c94a511414126070305807113464111000003081003110004084007040c0c1c0e82d0b00c0d552441d00c19840745181c05078610400840e0715050000001c0354001c103c614400322145003403c0307552074540c224030701c1034220b410010004240e0f0050718070044041e207a2114003403082e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 637046753 1250 637045503 637045517
    0x40c05010203032e0f14120f0703170d020d0c0e060909160e090a0c090f03020918030d15090f09050604030302031e01151106010f1719080406 62
    0x161004903240c1c002035452400d200e1a0078010580081c00d915100011034030841d0301107042c0d03078030b40520b2812151a40161900d88404c4460710840c10800100d003c411418001082907070041019103a58410610000d03000507000320b0000c0c800241c10003202c1c0f0b0801501001e644411a03a01c00000030009035601344c0216100c0f00ba0006641001c005a0300c100a00034001240d030341d9501c00f03a0604078001e40807a8100448003088801a6880101c8a405031407103400000e682209043e01900c21200c40c2c02c0101d1150300c20350204010b079a8003100300d030301206100b20140303180c0754641d94a20b10b02500001f04682801c7c222580c050f209100f000ca4100c400c41d13a0180902d0b100c1620050071600c0d110b030090b040350811400240441c1c0607800454224400f03584920700403550f07044c01d10f0b51650a0f00103580e000300703240451903107980c0031030741046005002c001b4101ea94900307001402010654403900c0c550480d580c6550300042c1d018091040070000038483c940c4140c01514101e00703030f03911502030b400100b211 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 637048003 1250 637046753 637046759
    0x90b0124020706140c010605030601061701060203090d0615240e0415061b1e060509061504090503041205012405030327030a080901030c080f070818070e040c 69
    0x800245034080318520340350000301d400b41e00303001c0006610070712120705d03250f48a0303c0003d810748003040032034020b0030655102034403640c1c114441d911161040e40710030110351003407004c0841560f6091148160700e03400b80b4002040000811200d0341012607900c840e41d1404000069800c80110b84060181210150789521040702a60100022281d262009a0050740707440001d2015501820091030031700401581062843d0317055443f002c1c0031038ac000c0804819030208604208200c0580101ca17042100034001e8015460000d40c882640b04065910728800c60300d4401000c00c0c050203004a8001d003110764400c1c1640906403d2940c080d194001480c43e50610007801030400141c003017a0380c015140014091864200400c50a5003001183d0b0b40c40070107103a80050b4074080303640c100255190f240c8a10708642e16140c2c0540054129000c542e40a428003d02808000b51580c0c05411160301c80070609010f0090f480385c0520034074207007040f4040c03d000d2082050100b00d00c11442c9a0600c503611407041c9543c4152 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 637049253 1250 637048003 637048007
    0x307090b180c090105030c040909060c1b1a0c0c030c0a05060702121e0c0d030603060f02090f041802030303100f0f231207090207060501080c010c15090b0124 69
    0x40d08685019556506105900c3d2540c459802107400c411b082040c6030809845600c902d00329458074804550450f41c500c1402c3e115500980094075079140078102110320b0000c0d8450100d280303403480402148010400c002065064541e05854038031021038203c1e5169012642c0155803400d0034002034600740324010000c5d0400384001590184c004100282c1070920f01112280c904008070315602c0a9a10700501ca2050144402c1012204180c4245d0300820304a00e5800c0146c21540d5050700c00d04002e0040004640300e8440d040c01c1b15299000396000155070340c9165444030214a1001c009515010000900c00724500741414202620700c5040000c4d201d0f03640310110201c4100ca880b50072003001c0d480441450503501011800440c04018012803119504880c000b41448142e03002110119804180301d810300507140301d86c6003d014240014410011800006844501d1442004201080441008905c10480c0d0000c03080b187d80050b000c00c40b54ac440101210441e1030415450303401041070742140100f8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 637050359 1106 637049253 637049299
    0x8041106160b0a020c0d05030615040b0c0f01050727090c09090506033f071101022b0e06040b0d02090102071a090603150307090b 57
    0x19207514005104260150090250758410b12208280002c0044c22000b003078240c0c04e0058890ba1881c0c009030440380440c96000c0710720404140011614090340c050010303465004151590140c262000d0380c01c80c0d2044030704400007100d00702c014003c0c441d103500c0d410340e102080281039901c036110820302c0705a03032030810128000341221030100600c10541c0700d1160045c0048000c1c000684449040603032580c80d9004180104240d4203400300c04140c1d120702844101c0010200e541c03641081d05121010300100569607015010300001e24100c4201c490415244411121504001120070300084a11424010310f45800600c10032000c1020500b0201510121446031000b51350790f1011000242081d0003948194a42180401840d0240885100744c820043c02900e0072612560707501e459a0780d050740c5822154040c081d00401041d03d1080c0c2d08491b60320b1f0b4054a8000081c00404d0301340d0950 = true := by decide +kernel

theorem cover : BRFrame.Cov 636870503 637050359 := by
  have h0 := BRFrame.cov_init 636870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 636870503 ≤ n) (h2 : n < 637050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
