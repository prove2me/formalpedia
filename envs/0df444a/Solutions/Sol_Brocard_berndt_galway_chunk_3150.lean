-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3150
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:48:51.449668+00:00
-- url     : https://prove2.me/submissions/6e9b9aaf-5032-42da-b818-0a4f5b025893

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 566366906 ≤ n < 566546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 566368156 1250 566366906 566366939
    0x1b030309010f0c080f120c041508130f03021606030e0709320f010b031504050709050a091a06070b0f07170a06080c0a050a0510020f07060906091208030f060a 69
    0x1058800181d050800d46d041e80d40075802c180c2600d0000d0505040c00000070000c2590201ca10030721103201c002440450180c01e9840c3d2555000b01031180740b8103940b401950300e071000001c84d01e1134640e80c6004039001d48030f4425910345074418801061014a00a181001007031222030280d070081c05c210602280c400c0d1000705c1c0049410b02e0615800e02c0c13030000406c0c124420f06070460000c0e00010000e100d00e503120202410409007007103078002659101c00000342c070307654010351200b90403600610000550481b540d02041c200508800300d80c40e44118101041814425030b0070080084078081301180d21000d1124441e5880107150a03c8a6541c035822100e001e2a00100c1c0c0b814901d0b80c0715142800361000a01031a4030341c107801d480404082c1c1c140000540c5520440c060345000d400306c00700a40465108201c00703501161410305886c0403e85440e8020100d103814050400442c0f102040003a07110700510384008404e0b00420700318116100c0c04060047c07054090842e41e4070500c0d4040104401614840130354 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 566369406 1250 566368156 566368177
    0x313320111090d17220609320d08030a110f040e070302090607080d06050906060a0e0414161b0309090b130f06090509030306100c06090605041101021b030309010f0c08 73
    0x401c001d29107541c0103554515a0003070010800c039280108003910a0b850030000100b0800e20323160640c06060b400e0880d02005461540e44503064549110920121100075801101880010f000000060307000340603611800010b1b2000d100304000400580f40010041d6802080b5440d016103002c90340400529190030000c4190343c4104000b90800301d10744c0c81d00c00c001c0108002d0320015480e18165000626500035494084240074900600c003409640d41da003c61048030300600e0640300c6041540e814050307590701c4000d000104030403214003035071501740d00c030752103101d40e0301d9078800002c00c4c1000d10b60000f421210805907000405052540181c45017405400a5141d0300c11000a6440c0f400320001c056030f01c05000900d45420030014807400e61a01c1740007200c03010090030960350051a42c0751500082c410001c0180140c3e240200344000c21541461460a1541c245d00703c4107444100e0318070f0304644070a00314555142d441008180c407594080c282000740c080803810043c400f901d450700c5900c4180c1c080700900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 566370656 1250 566369406 566369437
    0x3041103150a0b0307030507061110050a09031202030f360105091911041d0609010c0807030b030d0f02010905070806060a0f030305030c0313320111090d17 68
    0x1118012a5100740c0e4004401103000b00041483c6d5290f49403070f80c606008a404004981000c41d041c20710811010f020540141001c2004c0d15144451800500c508581280069141c140d20407914003540203a80c00750003401c140103c0341e2640861050413188841c44460001c038507070300c8541d1038010340c0300c5403209603008400801da83c9406440036040080e00d20004007643e044400d00c03030100c1d074142d107441641d180a603070020704952100c020480074150100e4000652061102300700e54403030b06401c071000441c0c80f03440740c04c451740340c1010075416a8030308440c2c50b8141d4800404031006504c503604040050a003400006910701041c1c881d113040100360340005500754170070300501407141480c4410100a100e4589440000b50444d580200f0911000d060038100d04008404181c14440242a03012060f901120403100380300345840d0b0541001500da08021924032429002103170f010103008070786008902c0031405140601c10800c01040b902c58901c10b079809100c8025180e00018160002c00c60101c0300d5910 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 566371906 1250 566370656 566370661
    0x9040c0e100f082407030b03240a020910030f180b060909060702150705190c0b09010204050d03120e15100b16020d03140d0605120309150304110315 65
    0x312180c488142e00c0100c3c0c1d544441000c1110820b214407005510303411603075510064440c06005c80103810200c000c540d0500446410703c080d2410003203511903205000406221079500c800840049005e20354000340c0000303241000c00b860900c60707800804511010070001030751100681d640c0e1080c4a141c1c3d07040751801d445500f409000e240c000b143c160300006a10041110385402c800007910b070786a20790902a0700072001c0200b44981d0007042503801c00500d4140c81c43e140064244000e20074042072200346c911600980c08511982410300880c0c05a0710054410440d40045035421030309000c021258aa450f0356400705108604418030404580c248450014401c0d41496401120508502d40c000c0007048003c00044400d41c41001e00c411480d9012a0483c004a07440d0400b61a41c0b03000e1103001c041000006001500c441055012000b42d030415981c0000900c0e905180769900c0c070030512115442601c910000a4a80410005592051217071002158800c1c03000080780c40c00c3c110421060041c080c4004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 566373156 1250 566371906 566371919
    0x1809060518041a18100506120a0818040608030309060402030d09030c060f020a1a09010b0a0810020717030112060b010e0d23100e070501090303050909040c0e10 70
    0x20315505403185070004508059070b50340f0800f018407a01c2540740300c111001a1404409001000b8850000030a80d00001050f2662800524007160414800d010b49145112050000102505145d5002400600d402005540580c1a04000d00c4240d409620303500302180c002402e2000d940112030203070040c6941d00f442d00c109401d00d0200c2c802c0070700308600d1103000c00201c0d9000784000100c94560134002041d0444c01b01c00c0f420440d00c00c1020b004040e4144503d0520f11103c54418811204440200280c4000004110958070709100740c101139403004203900c1d2340c0b542c5580188070703061141c01c1000c05022040010070003900240d00103006034a4100c020003d12005000d1400d0104091906a0400d260117001600300600c0400140c085c442c001c0d02031004074440d46108034010398980881e0f000d0050402450007424407070344986081c0c0030f060b80c00109940100b9160068a51603103070701e41856188010710800319030051007136a660840c403500054400d00e120f25140600c400c070b40b20b03000444c00c211 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 566374406 1250 566373156 566373169
    0xa1703090a2c0c040303140702120f0d020d0806042301030302150f07020d0c06180b01030c060906050f0d0204120308100611030906160503040807030510110d0c18090605 74
    0x242c80202c1c0c100e07981c1004501d100388011642a43c0e41800c02d940c04040c020441440c41c040e4002c000c2d00246441810b10040d01d000403d0618852808102e51900c84d0b0200100e0301e84103c540a0b50224500300049a41494603412030340440346c00544088101603800d181c20200c020aa009401581207280b0981940211089081d030181502687c90307030909242c10300039510440d03050701e88200050032401104105c1260800078030070000304c1c05501030950908240684d500c5c2888122051030341c6813400580705010700c28110840780903484550070201c1c4001d49184541c0702c540303103100580c4e0070070010580743c10031008890400d0090b0f0b241403091070310282a0b481c403107894110005005007040c0c03606140c5030000c2103941c5c0030005d452032900c1d1030408030b00703201280307000900814500011030f01160751000043c1072030440b40503001b02c0d21030f290303640f035160216080b00c80c201c01411030402401c001030307070300c2e03080803020208900c0c090700310803e50000c4103000c040c950031849186440302d41c02c01c202d240c0721 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 566375656 1250 566374406 566374469
    0x1d030f180604050109030b18031908150306040b100f06120e1f020906040806090a0c060c0b0a051806151021051008030c030d0e0c0a1703090a 62
    0x40e50998a860f0500001074960700c2c85c1e2000138103520a800000e1541922041940c4007942c5103802c90303484003000e540081c2c40301e8400984000140d840c00c002601412144021070148a0150140c040c648880d203500c00035013401003100710a2506800d0004d051100030a22000905565580450007401c0700ca01d0800d4810800001209520100d520181041c000c048281641d00750540160788211200110313030140940c2d4402d03017240c0a000c2c1042010340c030204404c4400c0d4801c80004906a80705c14060321402254000507101001600008850f08910751015400042c00c22402c041d03802110203040c50410100e490540e25165103005400c941000c51144440342038909000b1021290880107034240311008448030f00d8161a880411101085400107801030f00610068a941e4034618500d15600c1e40484050703580149418240502403c000c15042c80c003e0f402806203807580d241c5218812128803601c004843c81c08100300c0141113560f515561401005080900e428040040c510b552160842 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 566376906 1250 566375656 566375659
    0x20100503090c0907020a0203060a0606140a0c0b0604060e091e0c060d0c110d09030c1502190311030c0f011505061e070605090309041a01090302041d030f18 68
    0x34000d0208a032008540341d802c0c8041915104900d9461301c00c03c91520541d400e01075014001d5000b8000303d154950001c0c1c1c1a80d03030301d031288030b91458a0769140030184070340c090038000206900d82102c00610440300d0a138100c0801003021a50507222407030300c1c1402d00c0c103039002a007030350018400d00c05000209a810f40840242d01c00b8007000c2441c40c0103c0d020b8400c0031203540c1460b80d512640b10080d401180b200b44103460311800c80c2d041500c00c140244c05803440d800180d902a840c03100000f801c801c50645440b1001d020380c0602000410041896401416040c00318103010b1042e41840780f103c03017080501b814241d030b075008051a036500c1c0105401c4410382e4072803800c00303035841c001848992540c804803600c00290480b01802110040c0da105c00502502000606490512060101d03896001016000648013114100701b48a100310f40c2003503001003904902d010503044107041015160543c0420305102428401c1074461110000950659001c1c80803443d000b0780101b004e80c8000b80762800025080310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 566378156 1250 566376906 566376917
    0x8010911060415080a02070605090706030b0603010605040e151c020111010e191a0c0d1a150f0706050a06030506090708030315060d0603030503011e030803040209060d2010 75
    0xc140c2e2a07400c3c00c4189a8450500c081c130808240e503450942e0450f808a43c000c1d40400282c00c061401ca51201c0c494410000081d0030180790042c18901001100e0484140b0740340c1510309840c1965001441400810b440c1c000780915040021507100d400203892405403000f60300c00040c0240c800500f14800c3d9041e041c00c0b07a0700d01044d10003150000255a014000c03c210b541d40c1280417482c1030405403100031805030088115806001028018138042d0500c06400b00c82805040740c001c0c00c011084a002802513407045500719810003028020000b00000e003031122510307150124039191070003a60010b40380050100d90311001041402424022190080082005000340d140f40580c0b2654a002c0501a200440e54180d000d295681e038480c11604800c44070170041c0051036890802038070940091290711408a82100c001c00700300700c80700701042520384c003502c91811622642c0038400c034680024131540d017120303040c01c5010100700785550705460882402c49a4140d40004418070903c1c40180c072000b828442c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 566379406 1250 566378156 566378159
    0xa1a180609030a0c02030724121a010e0402090618090c0705030d02031005130608011b050403110a050619030c030c050904050402010e0a030825020d0602071a01080109110604 76
    0x1c001004a98950540c1e19004000c0c1050380002402e1104640c0721040c02410b030520b1144458000f440520001000d40320a070908a403a81c644040c2ca142000319003506201e104001a10740c05024201c4000c20301500060400c81c40402144155220180030079408040e00c800302c044d031420ba8a050f6100141d0310019013410100d40e070346030b03072400b5220380b10b00f1654010000800079480c90701200300501008000c101c1a01064040750002c0400e406001115400c00719030002c168085180d80582c1e00c01070f903606141a2175a00d44c0952040191032003a030248140c100040c4642c2c4c1d240c041e00c0508041510f03041e08640c0c0041c050119400510103205050810200343d0f001e0b90490706950801d4000d0780c01180c3c0fa5582e2004a402c41f846d04a00c0e07501440c52180441800740d4900038108421030395210039508040121140c0c040030701d1250003540910120400c10010325a6005000760310b110b00006484266108500761102c0c0090f00704400c1c1707030f5481d908501400b07104603d10945560980381103240a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 566380656 1250 566379406 566379421
    0x510021203070804020f0604030b0a0c111e0c030a242702150c0c0102192406030c0b0304030e0a0506030109021803010c08090610081b030a1a1806 64
    0x1d0000414800074082c03c1c01c001001d548071380d40a9850040c0042c1038aa0ba503460303141000c10b2207801d8a10081c03403403030a18820522401080110720b42010701c0014001c00d00a03a5803208102c0c00c10409012500038105044500d071004c2006486d954030803500009230400842c0208001c98100f40e0b455401810026141e800d07107943c500b00846850003040040303102403640040b95480e40204512a0280c600203021a03000e80080380b403100410b001d07401d43e07080040290154aa25240180261140b50f140e40c0302404040311108554a1014524012450310b42d20349a51041440c1540140120320000040008060303024101001c500c40854603100114202800325210380814050385800660000b02900d4a41d5103122150007584010300a22980c030025500401032a010307a052242e40c40382074003041140066900318825601d0510040400040c0c40c2c02e0010158003045649400d4028001034a01081c0400704003a1b550f91494540c0b4070038200006440740140840c40000b405070000001e200c01c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 566381906 1250 566380656 566380693
    0x6090313091116060605120a17070317090d0e04150e0604060504021303020108060d11150910020106050306061c150b09190b040207051f060b0c010501051002 69
    0x941c1c0ea4900000750301c030080c0220b620584100042032450a00e08400030040080c56081007080c2d07801a03550f410707501095403c4503500e01445000801d07401da00700b82800061714480103421018001d00e0201da05103010310480e500d8107070950300c036800ba401000c0b200c00019000041c0010140044e1030030484640d881c1140f22450710310340501070301280040007050007561181c0002018200041086645444521405480000c184012030100d8541c10006050340352078841c21f50002c0d008600d415520228008009480c00704080a844030030041c44400480e40714803080e100411100c3e0000941e80d4202410540b500c030300148060310500420000c0003c81c9c0c2c076a260384d503c19520400c101009070181078500003800704010b1494020402004001240750710703200100000f5070007035040141001000910083c2c0c4100080a4080d42c8241e20b10200d10380500b01d05106002c0308100001d10503240d94a0100e5039000d040480314683d11040144000d15100079129081440c5000030111a800032045210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 566383156 1250 566381906 566381909
    0x21501080309040c020c120717060c030a09020d06050f0f01150918061d0109050106030b060f182107080105160f050906070b0f0a1514030102160309050306090313 71
    0x6548440803100c0c1c45000300034000341501c00410080320840703201d1030f088e0340d0062413040c401d8403c41807802000ca00701c0850401e02038483d480c503203440e60f950562550302402d8824412a00080c7c07020080004c13030078030700c5094040c1148000060850404080401a801c2c040e0401150783e82004103a1a941c2d0b0403903400d41c110f405051810760740c2601900c03032a006205a90008060a403001d00b4030340410b60300300700746058805600040080d0307602c42c1800c60803600840c2000c1c0d000724041000e80385d04001d400140400d01c801c2d0030910034418211000c06c40d50201c082204001111425072140b003550280a02c502406504000300510b190061041c180d000301c0841c0c240500c42c3e400ca0354a03845100d04211500d248001e059903954414524158078240003c844e6160340d000c2c02d070003043c5041d074070340980c22070f0001c0b100c9804406403e0102001841c0845509550316660030004404800041c000000c90140a5180d924807103152209041c18814007c01840c45a00204200a40f42561517110070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 566384406 1250 566383156 566383159
    0x504060b03070b031618061e09060909090204090212030418021801030c1707020c01110309030616090f031202010e06040302060f0c0403051e0c0a031a0421050901021501080309 77
    0x4400c1174010710140c480c1c9020005a40f5007100241011660a40000320180051524801450780c41000582200c0982e00c40c0036040010b0124017042082101d1074004c0141d4500041c03000568266580c0000e46105000c500b442d40c0d41c0010a04101c423403d02c1d60041d2404a500380250302e01442a1140007a5800302a9444e050680e82d0103403540c49807055158400ca41c1c191248880e142c2010704000c0d40c1c0d04503582a0500289650202018110010050781c000304006401002c1c1d0780c031140600745070035045c5d41e00c01040008c00340c0d000600300b0315091040025400f80c000c8500980b03905200a0941e00d54003041417560340f081082c00006030307001036002c1c1d22840302401c0d84080e4440d804622042d10881c0e002a009204507501c1416070000008003c200380704000440d5500c0d040c0d17000703101c414405407101030704d0801e80b040c0c00420880300d0300081c2c2e400346c41440080d20020510360668281107c04031002d000441c04a905516960100000d520080036101c00c00c0030bc3d03240a0242d0b65900c111200f05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 566385656 1250 566384406 566384431
    0xf01050906070b040f0b0c040305161503050702010e030a050909071e0807020c181f0f1a0408010e0a2618012f10021819090f0504060b03070b03 63
    0x20309200450b400205c10700d0303001000707200c60300384114102a10b40040c0010f4455001d0181d0310a4034202e20900382040700c0240e44010980e0b05070380c4040d0000d100041405065549540070381030154003d00c0140111076243d200c441c2c8400418051140081c1d000380154140800340c0e40f8a249048002e14030124a4000e01d800ca00c19a07a81004038140300d5001c0481c2d812000b03250b000f84813500100c0c0070610401611042d050105801800c07011a4500f502ca03081802c840f80c4402c3c03107a5005171800d00c4403c4001c07441280b44c03030740e80c222150859a01c00e030052450f42061450b0b4080000d04180760400b541c040f60811400422044010020711032220000d0304914030401d640f0081e401002c544c0108601661640c0f21039050341400b0ba11100c040003c2ea040340105200f0340304d00c0c9a28404e8071100000d8001246580c0324030010721528851501d51207034090182000091555158001d55a007208980e00200e0503003840c2c80c1c0141030740c04550030284a508001c40a014a46c58841920b50028415406c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 566386906 1250 566385656 566385661
    0x4050c090c04050a0b030403031b050d1122170a030504060507060e01050a0e0f01232a13060503090d05030a020c0601150816080f0703110a030b0f01050906070b 70
    0x500001d445142d10040d049040e440c030000394000c0d40c0d4080c504c02c81c0a500d09204014800b214030151480c3d41c480000414401c0c03201c0840d581055002151040c0f01180c410320b40329900303000d584030100c1c41009407480b0110404c02c1c04606074030720300c0c2e21004403041c000304500c4e0019940603203d0300540c0a00750801c2008a00241881030035046074401c404890300800180c2412075001015200d080d400034141c0c8038814680c20b80710414401c404941c40100c01803100080703003010404254802800580b00c1d00c8003040f02640e20030040b084003910342c0c00104019640c0c01c1c90640001d8402069125400f4020207008105c84140003040011001a65141c050307601e542e0b6942c080000d01411a00000d144030740f6002080c8141050024010100300752610346041d50f90040b070018640d0407001c000d00255070f10002ca800001120300a54100d5020308003c210144450909151074100e6038000000984442e44048507040442c50b480c8844000e00c4d00c14a0030030f0b20030209106200f5260010001d6091200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 566388156 1250 566386906 566386921
    0x1103270d08070f030905060c0303180f070e011e06080610120c0e130209010f0c06090f031709060108191106030f31060903031b05040303140304050c09 66
    0x14801003050340070100c180ca0380c40700e0402020150041c0d03012404a5138a960100e4a03151140a0340c445d02880402580786aa0b031940081d101d035143c0028010720b00c0f90072410308a4030403c0c080320018048410071102990b2410700c0700d0545843d0019104110841024148602c0750f00c00c40403548a00c080e210051000d02c0780d1011103d15051440d031005d40e516011040c002c40d41e01541d4400c0405e4200d0b080203805000c0640c0320304910803484210b011440301d803100c2049901507003616905d240030b6080041c0341c104688641da001321510400304c0008008900c00e074504400020304c960003102c0c20700100000e60408045650764510b0058583c0084003904080040141c5250f410700c40000c080c0c0b005440e81030410203006045002d03690940c40442d0305100c00c60020074055504030b52014020040703595840e5490300740c000c2c2220724066003055100d282281545c039030862040d40512031a03680da9a40d62450400510826415a110b030a0140c10410b01002c9100050090700c42c0604440301e8096032140348 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 566389406 1250 566388156 566388169
    0x304081c110423100f120e030a081b03131401062114010e0604050d051602010e060d0516020f01060f05060c030c0a0303060303032f090a0e0412110327 66
    0x40ca85039010b010b0704040213259030b011900f04250081034a441000d003510314450800d5459100030074540e50300a0000c2404144540b03012074024500c0030740302810a8215800101c1e42e0300480e0b07c10071945c0243c1c442030400c8101015007820120490003080728a051001003400f2440c90700f400c244d400c04034209503051000d40e0356031003100c0b07000000811404907680c0b800e580354802140c060301c0501440648a004501075000c40b040c01141050f100b40c00130341c950041d1940c254200700b59030000014008000081c00e1881100d000710400740c040d21010050700d030300a192a500d00300b00c9005904100007000720a044e03101c05001d4840441d8401c1e218a0342200481c074502403155099041d1054440c400d0501d601030b4440c0003170340e01079a010700108003841d01000d205100120005025800c807130116040c06104400740403404002092030b483c056130f410344891000c00903541914911401d02a2520303c54105043d004e01c1c001c040061030a11581c0c400c02d00d00d0b640d01e503130305202e020340b092204071596441c0c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 566390656 1250 566389406 566389469
    0xc0a06030227040e030309010501050f010c03090605132c0115120c0329090a060e15031011040e100302010c03082802070c08011a01180b0304081c1104 66
    0x4c412244c80e85401c02d0000c1c040c110070f100701c0380140580002e00742154404c01030a0307501c030341584503c2d240c1031a042040b06d15038420468190340031419400402c1d0584918070701013102c480e98464020110504407140c03001e000681c0031241c40102c00f80704003c00754220309c0324411030440c04000910700a08030020380c058201254020001c1d001683c40405076a150000d44480031001d580c580c1c016602c2c0d0308500100e50060141c4607030400c80744006408542c1c4900b1b0b405208102070103a0f115508540c03885801d85003030141180c1c1d030030700c0440e060040305110031225034004103806091100700c0c43e540002c6c02c001d46111014007003042140c00203800c025000c9c3c5e801001802892034540e00c002c07280c8810003d40000034100d460940c42c490010b60340d10305000b14545e07a911031640741c0c3e62819850043d40c01e110270401c1c1c6207980f1086180003c201c0d1214001e2b40c42140640700c20ba9072410403400a91408441d20103140e000c0e441c1000c41c030760314101c040545085e100ca5882c025014a81c0100d0035040348002d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 566391906 1250 566390656 566390681
    0x230a020c0a0b13050601170105090615120a061514031c14123102060a0f212f0904020a11010507050d0e0a0206180a090e0c0a0603022704 60
    0xc0ca80006141e40c7d8446120008201c4100200400d4940da200192220000e883e156a0110b607191410b11a18202480d05055040f010407903500180030f5440d1002d84a17810710140d22582e0816040001c914614905c0d038900c2c604601506002c40b07400c02d44c142c40b44010094108020100314180e0a04440404a0b808070712080100300c024038219135401c00141000030b00984030348c850300d5a03801010700448984100307503000700554241444043c00320340301420440c900c01045547e85201c103c0101d4004c032015596800701000c543c0200204041e564021007000d0407103030358450051f0408071a0310b00161341c41c04604907805a5507102041040740e460315100c0c044015035180000f44400f15800600810840000640c00d101410441c1c03503450301c840c00c3c4c000283d0003440c1041941110146000ca0748401d103002008598840d40f83e2903480d04540700d401680d11a540030351140030042c81c200110000621251600354034100244546000c2108542440131041c07096504601240d50303a6044021400c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 566393156 1250 566391906 566391913
    0x40f0c090c030e011b0e061b07080d23090f040f05150f01050f07031b06050702120702031903030f09080702130c2c04230a020c0a0b1305 60
    0xc5454020004000100c05140070030300d400410708150006020b00b007499000c013a4003104044213081d080d6043c000c13006c03003154020020441c4580081900c0419070a50f101c1d00010302c407450500030110b150080400e5143d050003008001c5220341141c1d45209404042c075880010384941a40d00428106100c1c42d00166101d403c10f1001ca40004c55a40034074800c0081e00e50303c0c0c20050720441400181501080c005002840801c032640201d0340020003031001d030b8442e180c107421030601132015440128508208584460322102800f0050f40c3c1000440249107146090138074101150307000a5850201c40d966060700c02c84441100e080c036010380e00c00c030318050311b0b500140200041d40c42c042840f644981030491040c1612140003146415604c122542840c0030703200c4041090b0010601c41c401503041c0404075a000100461460541b00c5000d1396a03034002c10a20311201e6000a8405284550b004191455403031061100351202000040c2d014000790b04484143c0e03880d1141c0c7d12107007210036500e1b0091310324030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 566394406 1250 566393156 566393159
    0xf0506122b0c15050405070b041202090c09040212070f0f050307080426040603060b092211070b06010e090c22150c03020d081306050c1b0c0307080a0b07030203040f0c 73
    0x440d0f03900110300c500e10540c16207070900d1b154901c46144d4003545c018a0029610b5000410050400d6440c19400140a001080c00c0211840018050345c1c0101c0c030314131b0448040800e015070300b03400428041d500380080c01c0c410b1491b90307002401081d90100404013002c0200d68404a4148080c0c0803a1414040d554404c0d2402e074078400c07400300f00c0eaa000344036400020b440c254002801c1ca00c03410558080040013001004000c0c4042c0505c590040d101c104003501603075a90441034042e03004c1c0001e2015510503810103d50313140020000d0300b141220b12505000720084020403000e40700c80c000700c4080a00c05a0824040c6d2000b24140740c06401c0c40c3c120403180e00a0040c05880c49400003e0880f019200703a08544480ca1484070885500005840c6241401825001d80c000112613410441c2d00c0400c0c02074503801c0450b0340250f44400c4a0042c49468580c0240004103198141841610090091403004140884880c0c2e40c03003812800040c0210304155020022804024106030380120030760308840701c150f04030b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 566395656 1250 566394406 566394443
    0x40b06070c03081e0408061f0f03210e1333080c060403080403020609181303110d090e0705070b07020303161b060c0e03010f0506122b0c 60
    0x1390b004100042c0650703148801d8100c80e424203c00c6400341c0300b11202410080e10f0b005800c0a08c2100d13000d4003d280325481d000400e030060005171103030003540100c85004040070f03214010701e4a0060500d01a0401c2004040884240c541a120303002da20544400007031003071080f0590100181400d0850740380240038505000400902028810a0740c54030002e4a2028860004221a0b88940d01c0010720380c0d20b09100030005441e182002d80716824001d48070450b80c01e4650880382c0412021a0103114614241c8102d01c18998444c1698101180d40d0004000d055102d8a000d0f00700241740c0700c0c3e012002c5900000441192103401507691040c0d00100d44152421300c017501a450f40c20464815580886640d0030071403162154500d0519103941414410014131981c6034100030b886a15030380002d000303103c24008a0717074500b4880e4820401c0710000029040c2040000c12400c40c40100c03000d40349074803030700c0b08100e960300801c01540501132195049100e071150890681d01154095405403030807854900c1c45a92 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 566396906 1250 566395656 566395673
    0x30b2b11040207080c07080a05070e1b040602010905010b0102031317070302030d02070e060d031403070201060b0a051c0501050f0105030403030e06070306140d050c040906020c06040302070501090e010b09040b06070c03 95
    0x285c80060240d54005d601c450a0b40d036140709400d00075007582d10002e020401b15444100a9070001c080d0f00550ba100d048070100d02c401a0710903800302006070354411291085c41428481e45058441c240701a5261a003c20b10403a007445507406001c100d100c880000000c0300c1400c004da0002107502a040d0b400816032864042e40715441c42c42110070440c0c124000883c1890b080c400c610350141d1540759080c0e280340c5d211440146802c000c004406540d0385000103c0c1014807000602194000c55823015070303c2d07030344650814001c191070540d8540142402d0050059941e000541c003952602071801588a98a82c103040740036110402c1380a226015050600c0441c6a15070480d8041c0c0d04480013110403c5091418005050100407018009030001c82840b1900e280c9508034185a6003d40d50260800c040c102c505810f0510543e0220056400702204000340d5802c0318020004201310310454201e50724219000310a8800c44e04030034811a0381b0409072030290303246000d03034288030b03003001101c100c2586074602a104e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 566398156 1250 566396906 566396917
    0x15060a050a0c06110c070e040818120601031b050616060c14030406050a0b2205091203010803040509010f0b0313020109210b1003051c092103030b2b1104020708 70
    0x2000e0094040104501e90351014050180f0340c002c28251801200b40403150310442c9a0ac00c15500109241030a081480c00b0403180c2e0103107002d030010260100601407401c448e40025844540911820f120320010241c1091542c40303c190407800c00300c0c0300c010382c940031103a0b0301c070456400350604800f2080c8000d024150340110310a100340d5408000c01051981001040720070b0310000d08000014190b404540750294024940203c151000c46c0c10302e586900d082242070300240c012014541c0042000c0000340340503c070040c01402c2400701d100a150424021843c5480010808a61a06080002811640301d001d0b5203000f08440c6107015911100d0841c814030302c1001d07500079a0300d03070803090102e14600c80320703007000048a5010b4010b00e070b100e4000001d00304510004450700705006040400145000740d9503810b1859072101d030484603000c0340c946005030403114044625401980310040da04000f080000f110304034900c1c0032021410030800361074000c58800300c19004036040b47c004101b640411058001605 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 566399406 1250 566398156 566398177
    0x260c0105011406032712121003050714060412050a06050a05060a050d081b06040302190308060f040e0111070b0a090201080f04110a060507060515060a050a0c0611 71
    0x31060b66102010a940215904443d901c44810004940c00e44840041c07060381c07240f05943d405401c1001e0900904259800f907408110301c9001900811003c54810425407001100c2c8864101030300b0f43d2100c40e90362440e802880e81400c0401c681003420343e00c0b03a0694006106510356800034607030745d14025441d04040c4d4400c4070300d941040085501c0c2ca04078044d0300e120b12000f51080001502e071a08005502c00100c070281e40ca8142001501c245064960283c0c1400b03500c2401486c084c00c0c18034000f403074003508400307051a501e17144018200007a4072091554200b102100d4000c020001500000c00401c040c05c0500881d610f0305a1205030b90130710790054040d043c061000044543d4a07064020306850001d44001e000803080740018060001b160046500300380505020521307410854046400e801003600800007103580802e07410b04115550003826031068007600140c00708410400415910300444600405200001c202160b06d9480703039110a00c0141c0022040c050848281d41d8040160302611440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 566400656 1250 566399406 566399411
    0x9021c060e010606020d1d040e060702061f2c04110310060b0a200a03030b130b03061504020705120309011131090c02010e0607020d140304260c01 64
    0x152100030180300d0881200c41540241980141c000c6c0125001e007021480540502d1511000d040161070720321440c129004030384020809810030310806480c0800061140310211500340010760700d0403074404840103c803004405010101c0740d180301111183c1c0300c40c8440185c0d451b100300b000148109140d4912000c034054080d6020070440b04034040030b980c141d02412042c90070411860107100d1280e4043c0c00d608152020134400035130614041c0782002c020702ca0540c0000e84400b50b61400340751500c1c1c101c1021000c00c00803c04940b80030046038990100030205501d043d1202c1480059443d242c049840403a0702100f912004004030f1500916a04107031045003007980b07000049056403101604641d00701c02d030070039001d1050030091404490a45c101d20020389651021000007113440040c007642c0404100c6400204102ca8124086494030364014418400c41d4800c80c09440d03065004a4012141140254025640d42c0c1d581071502c0243d48140c041e14a01e07000c1d0058840500e0010082d0001a150300001e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 566401906 1250 566400656 566400671
    0x60509150a050a050618040207080403050601061805180a18061a0102070308030a0506040b0405070f110c06090d08090d030207030c1508150102151005120604081c09021c06 75
    0x903c1000f200030300645802c03040c00c20154001d031b908a070170380b004000c000b0009494001c1c141d0b00c119090300a58021509507002400601c0b0150304000d00c1142c0d8401400f80c1c1080313515200001d644010f10300703510b003503144040c408130303940c81440e81001c010b000c803030030098100c1200c0d4034041c00100f140c805194401a081440c0e208550f10120302c42040b25080000c075030841e1113109944009080c05850702c2d601950f0388862240c940c64038014603205043c80c4e254044030031850742e070142080c122440c102049800c1000300704001e80d02c2506654242c0016590030705410b88518000c4200e218801d00d603640a0100b920000802d540051003100742c030f200e928500402941d408075951011072051000f004900a040014100c5682c104100703904c00c41481181d100d9400c11b1000607039001c00b03030340c50003009142e0b80d0280094204921440f0625020800030b00c01440c29494910450141c0303852090410071820780c40a801e130384d0750000d00106400400700e0002c46810103041609200011040325150300300403e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 566403156 1250 566401906 566401909
    0xc170318030a03022d0a08030906060d02221d030712080f0606031e150f0d050c040b190603050f0105190b21012c07051c060509150a05 59
    0xc500c03502d01d0b80f42d001040c5d8201c100d049411400381900d80c0d00300040d41c030000d00030f0410041045040c5940103a0700c440d030306d0a14a40560801000500340d500074083d4101c00c000585401e51020702c00c0031200201c240039040d0380003000107040600025401030520b800402943c040c040010080c0702d20030784003055103000000702500c1c80801220110022420040001c6140c14038070011548000106500d0344c2ca03001080c2020880303801910f48000c070540c070131a40380032400c1c08a80100038103411a2003000407056555400da664a8241c41c640c001c0383c440b03807444c4071034864103203c0258042503203195240c1e50b22443c004009040c21074010b005500003800018440c2410000040000040b07034114003264140060030190354400c2d40c0e090080c040b15851000001c80c00c02e80b06000c0d14013015010313419280d10141c1e50541001702d424000800300c650521400325003000c00c45000880e0b40600002440c444200c42d001011aa40701c42d0701706c00c08000f0800c207000c0101100c109910100d40c0044100c1d2910b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 566404406 1250 566403156 566403163
    0x1309151215020906030f011a04140f0301060b030403080601090f0308030a0c2003130605090105041404060b12060310051b07020411070c09060b130b03040c17031803 72
    0x41035102051060521601180507045640015261030740054946503440011814a5000f251140c2c6104944401031002040c0c04452444501961401505190038104100c0c545086203152602c1810405c0a01c54541c90039007060004081060181d51079241609000e040b280e011503001b40014040140480d12481d540382c464182c80d0003140403811640c4106a8500504958041000340451008040c580c01c02802040c00c07840004006591a0070651700e180e12594955001301c030911105024000499070b1100a4030708031a5400341d424100030b10000070500905450f0040c401003240000d43c2201d510107a810a40121004c2e81110000402c00b4406011600250b91320118511080c40c441c036110900d1014102007800100000740040e800305050242c1c0d40141d030102c07480c21059400b0018102d283c45401e00a005070700340c5c180341c003d6681003080b2a2041e40951903200c4804000b080600c420064180c01903ca100d03450f060700d42d40d150150303075203802010417120384d0290030201081d00c2c02c012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 566405656 1250 566404406 566404409
    0x20f1909030c0510030603050d0504030b0f0103320d0e0112090203030306010c060b130506010f030504032c0a080705040c0302070809060a1e2c1320130915 68
    0x90b140c0c020242004100b080214032822000101504d80c800440452002d000400c080b5440b6203940384d0300c0340340d0703e081d842403400180f0000686203450b00400c0400c01c0c1449070301d446c0201c0c60f4024038401400032403c202c1c6458001148080c840c821803041800e810007070b040a500e4090301c415900d00c10341d120410544044601c0250036420030310100e130665010742d981c034580310320400700032800c803180501103040d035160481000c128680394400c2c0901c550b0005840304c2442030500d401c0c0178500c0c02d074401a06840d0341c00051a04c406a242000036601703416642e01c820441d0040c08401c90702e80d0359034400e40d158611302030380c1d03c11454100c01c400c0d51400791007200c03503081c1d21280042c14169040e04010345038102d0f580780e005210040f040382d088038000181e101c101004503101d60012040a10100781440c9421010348000182e07020f8075925a503e5070f084180000c000440401c0032255011410000b00c0d51000c80c070400c69002c1884595904903035610400d4660310001000510b44019030202c102d0800d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 566406906 1250 566405656 566405663
    0x903070303300b010e12120f090d0f060e030c0a0b04030c0f11040e010605010e0f010221131203080a0509071805090c091e041b0b0d0605030f070905060d06020f190903 73
    0xf410710481c9001842c041d015085c00c10840ca802c0c0700c09c41010460305079400c1d0007121245c40e24101c01c0f08101091050441c2401d07480f00131801c00c0b6404944c190b4031402010b014101e0704041001a00b007520a030301c0200307100d03400348078120088814036204020a12010310b19104a0406a2110700b0a030144a01011104140d45103048284001c0234803d000e200c00c00a10b04500542d90301a882407240e1004c068440c0b80e18000700d6803002c4600d02407000480542044503d40c801003c0300300401e600a50080e0010300382c0d080069641c0f15a030065280c6402c50341301110251059200d1194130b007280d0300c014422801c480c2500d041e11185230400a003d1804c44004086000042a00031002d8803c07600650051290380c0c1c0c0818613043c001c03080c00d44c2d04540d00c4400c0c1d9200c0081c0044c055a0f00d0b014100041505038014240403114140301522005640145a0020f0369500001d0156940350120703507029400150866460925108215036940726000380308020450703040ca030705414410680c12044030340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 566408156 1250 566406906 566406913
    0x16054b09040e030901201e070303090902030c0a0e040f06080a0c080105060105120426040603290f0a05130615050307090306020906091f03110903070303300b010e12 72
    0x6120b1100f18403000d1b070740f084102e403040d00c00c80100700c19181d0105c8659a240401801c0352840c3d0b280c002d20a0989400403103820f401402400360848148080d038018015504101c01002004408900201041c402060440d42011000610708501080400c5428014100304005540710b00c0580d0170b960090b00c110303001840070005a0040381002d0b0303c032500503128503c0007800c032415000d000e00c107007407004c03813800d90a000007803c001494040c86502207004d01c100c4603d0007400d184821044104408000c2c6001d10000d02180e85241d0303940e010ba00c0680402481040c10340310040d0490010702450148030500303400100210600c03405281624402c00865907072010380350545c0d9a40e00070350480c003001c94103e903003403144010a81e1100c14900600e0b4109501880c02ca010803c000c00340c0b4a54168040f049508101411140d14003041c40d1381900e4150511110041c0d031061070342c03400203031883e41e040504001a0000c450041035001550101426aa078041c1c8072016010000f10081c0100b90010590 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 566409406 1250 566408156 566408177
    0xf1a0304030e0105130609050915010804030e0604030602040315060b1204020d0201110d080a0c0c0c03023a020906100c170f040e16054b09040e030901 66
    0xa1150310048030710320040c50064203100030342d820030380e94917616001040881d005800901032070400f16030307440d4007003030030058030309a91440c0c1c0010700022000789c0054204600144071034584d4030352004840042d603000300210354031541c0341096044a601000d101005900340380001902c50f4040c0261a000340030240d041410381c640c0d82c2004044909010124184074a54400c0c1a03109020b0100c0ca10380c030340c0354558102600c0c003251030710110b0384c180002900f030200781c8140c100401c4d1400daa803015654140d6003c0030180341050702d9070250f0040c40040550698010314201d0040c04c006940c21002e01c00d580515442c0c43e24800c1044401c01d80e40c580000504803800ca002244551074604031141c01c81c10004d00d00083d064a5032106d070720507004554452011800c0c0003184090303400d03011801141e447c0c104d050800f003074a151800302c0741200d060340c408040c0e000380c1601034500704011001064010138101600c0760104900c0b03503400422301140310f81e141145011482c50301200310394601d9016590a039441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 566410656 1250 566409406 566409413
    0x207091d0d0e040b0405151306080d1101181a09030403020108060906210c09090703080a1107050d0c062c040c0e032407020304141e0d0c0f1a0304 64
    0x80e420032140651050f100c400c130f03000b5519a8824280107141c0943d80c000241101d1013488810445845480002440d01f9810045804017003440311050550346001240d8030582c1d0035441c0580460010203007005034002080c0e040208100344885a42e50302c804102d000d170f940c5044641c40e40141d200c060f0100b1201e10001d480c030700c0d2000c902540000e00604441001305001c040004540841d0301142460744058040c0d060ba141950100740d000e120b81c030007052190304640c3c400401c0e01504040c4000d00a000002d0140c1010a00401d000741001415288a14025041240400c2114400c0c10082a0311342d0181500c0d90792964400806900c1110785d44142031060140302c014003981411600300b007000c29203003140b80d505102030101c05a2103070382c2c0700c040e81d100d030301010f45074030050420019076008020411010341064190381d0080012102003030700b50025004400345204542032686d1100803030381903004000001e1440c6065402d0300d1b620f000781c1074980107642c91114070384214007012101440081c001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 566411906 1250 566410656 566410667
    0x81501180e030c120309161410111f060e0403091e180501031101181e030f060507030f0603110d030905060a02010209010e010327020a150207091d0d 65
    0x1c8181003140c0c42e12140201d25420305210b055840828103000045c02500e020070070100414016a603510959285000744800000f02c200402d20b004050110982c080c1d035000d03070800c2c419069150160f0301000307001200d0910720781c00030100e018080e07d800004a1140c07a00601a03126030f031706458480c80c944c1400e0540d014601ca502808500448090b008104040400c111100d500c0030308102107055411840d0070300e0075140c0745613102d04002c99081c2c2044100d00308003014003101c410070382c0940e800006d1100c1c05100c22041d04080c044091b00380035903041041551055114401a9900300040040300c0c06040c152411807101400c0b03440c01a40b501e90700c0c545070944405491003820400030555a90f000f080301c5810050140c07016035400300340802956000352110307540a00920303042010300e54099074102030381c407031b51901d0100c0308442c1300c040c046403510440080035210801c200c0e9802070494030001c2d66071071303280142d514680c1000c03050070155a013a0564101840c0746005040d0b80301c0603600407201e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 566413156 1250 566411906 566411921
    0xc0f050319020c030706020a0c0b0a0c1a04020f0f0d0b13020301060303021506010e06040b09010c0b011502210301170a0b0703020d0e07080309060d090b0702060108150118 75
    0x1800d0004004601110407400c2541035100d00c0d58000c3d02c8110314480806050030344690043e0290f40100400c500021203003011601a2046405201c0d00d0300c606620854219100e0307100103040c2203510800c48003410250124900c182d100325082c0c820b56203640300744404911855421500b04545000c1107000403010102c40798414608503054800e00481d400080c2902c180307500540258105044502d007440c19180300c241e00650a007030540d01c51640380301081951090388a0820314800c0410440b00750381c031503059081072035042040e00c0e00a50b1035164640280000b4841c501c0513124210060300900500ca8007900080a040304542c2142c4c40c001141500c903041c85420100c900440d925100000d079904070250182d803290b540140c8030020341504404580000c420052103901c006410801c121001049820310441a0f84071501e030b110365503042011b007d81680050080f1040c2d4100010540e00013503c0c0c0c102e68110040312041c0104109031100f0903002e0003040c0065500ca0a0081c039001b07107400125 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 566414406 1250 566413156 566413163
    0x2060a0e0a050613050f0604030507061802040f2306030d0c1505090723030a120c061109041112041707050f1c030e03160c030506090f01050a06060c0f 66
    0x7280c0400756a14076040030303401c98094010300590a900390070710004000301c880007007010004001c17a05050f2000b0707026005414001300901d444070700504034400c41b039400c001c0c8254045d2044c00884000c4400001500703a86100201d414071602040300c0e094810b40c0b2103400b503540a4050329103c1300929081702e0304601903a007903643c0401e140441401011038810786100d4980c0101411485050400e401c90700708031000b08001030a006a520340c4a9a800f0400d400c0040d444020460720705aa500140e5410601d10310141c030044c0b81041c00c205400c003e80090103403d0086508000c4d0001d08139003000395010741005520914449000500001c29065025440106d9020910304040080c0c0c1c0780e41c03400703c0f0040403134060f402841c61492490080a13601026400c00e00b07041c0012a41200442d5882c0921042c1e00074003402c2525400611181300152000755070400d00703403182807030942c00c00c0e42d445801c00f2044545602c2c1c44005010342007240301d010240e9807075688a08030010755481d40c0c10305c0c0a09003805e9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 566415656 1250 566414406 566414413
    0x30b060d08070c0504060b09030d0f03060914010f050103061d0402061b01090c05150a031508010c0216050609010503070c060e010c0e030709060f120503090301020d090b07030c02060a0e 81
    0x103401141a40700500201403045072518207a40c14102484284d41c555442070b400c030780e4140310752030043c3c0c0c000c03c02c00703205081450720f86007101d1107000031030183c101544240ca1035031610841040f00541d035100c05044e101c2c4800b03100406542d460044003290220b00c144444603240c0c100e20741b4101e01c030b4454a41c009000405d1103091a5104503c640e990751022484038244e076446240380100910000e40302c00a001c2200c551748061480c07043c2034110301c264030100003055545c424401c2c020f07043d482c0c2c0b00003500442000700008948d810300690b0703a9007010010780081c3d034841000285454800100c0b074003c40180d541500750707100c0c40002e450700121810100c0b0250745a400712a00076100344151362000403d0b41c1e401100c00d02d00781c145400c18440f5002194500d0600c03506014181e00f60006070700302e0b140b100200c6a51485400e1150a5000b0140056415400051071b0b0f8003080850300956225030103612105040d4840450540455210303180150142e000348000400d02481036000080d80e1071220140d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 566416906 1250 566415656 566415679
    0x30906070c05040609020c0c030604051b0d0606060e1f020c011b0f05071e030203070b0903070b040b0306331303020d0501020307031506052a012307030207020a030b06 73
    0xf419205582c002811040d40030502035100101081229405c020686c05042076082c83c0c4c42e01a1603400c0e165000e0030501807040040c4040c2c0315620b0320760307000703412030340822100f900c914008102604540d0514070402002c04880382540c2c02c004032010300505a0010147d0842c0b01c0300544800b9941100c10114501118003000031440b20344400b00c00345c0c490030140c11824181041411501d01401d41e0000c0120000e000b0f10040c1c80c002441c0c0e082c1c0d250010400d464040c61000039207410103a401c1054098404134002624844c00006140500da040f01c000810200d24031282c980c0c0c402c0740c2140080c03c0107040c8059000b0a00e50020581020080b85418440d03403a0380104039800310107034084601da94004100080540e1500c13442004015018403d2025480c3c0640100180601c0007008008880d074510070200440c400d060000200122000380315500000070251070803c020300700854060316050001306403510078400c442c14641c2c000c0141d828503045403210820040004c11090b08032480520 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 566418156 1250 566416906 566416909
    0x10f0209090f010b1821072607180b060a020a0201080a02032202010203130e040624090e011b0206040303141b0f09030303131506060f0302030a1506030911030d02030906070c05 77
    0x120070f007004440c00c0141f542616100801c2c1d01d911716003203014040c0e2120b0360050444000030840100722160000e915900058854030000184800700229620030303030004080c01c40c540c010540da03000300d0003601c50a6540c0d81345c001541c16448101d44442090a40c0e400183c4c0c3e103d448054450b4150041c4100c1e4200304500800442800454000c0e00d0846028400c0104210316401028801c007880d00308541002040780020032600440e00510720743c13607140d20205848220960003a03001707642102c0703607109030013190708045d480300819581900001d081001004c0041d40030141e250040c0f03231341d0312100e4002e03442c1d00c0c04403000e80201c05080601e141c02c00c4845903071f80c1d041000c0d5000d041091415002c4034003d10300504c0c95208290343d400e010b401c1041c20495175400402c3d140840b01d250070090303900e80c0d81d010940b00800c1040007952503000e11100c0030031510382c5640a407010911440c0320914401c084002c00d642c403504c6144120040e4070400418015040c01000740600e00d2041e07620b1402c040d2640c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 566419406 1250 566418156 566418199
    0x18030203030a0e0f030a02060f030c0f0316030b040e060610180b03070207060e06250f080310060903050a080705100501091527050709030203010f0209090f010b18 71
    0x10340c00c0001c0e008039061540f40ca080500c95041280807001040c0b02540307980814498000d14500701c095490100000340310070094000c807114a1208250a0303a03a240c1000c00b50202c1c51125008800a03107001c00409442c10184141c540c0e8030052801000b0940e19001080210351149040b0b104200103c981c0419040c03008036104040c1407d030034140d40300d01e80341e9402483d15900c1d03408031f0100020000481e0f0103442e02801c0f201c2203007503501c81700c03240219201c84181242030550b0080140b085c410990052000c41c00241d03000380742050801840541c0c41d0f008641c0301c4464040a40590071440d04140090511402800750703901c55400d585051411a0103581164000d0f444901c0313480c0c07a51030700c20365054502c01c000c01500003040031078201d009100414801c0031781031030310034852550f5202044049011350548402190700070020311004014880940103500040452401006120013140c48034a04101d40c0307050b070300030b0341d0014103004c00c00400510041c1e810ba1030540055034041048507003015007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 566420656 1250 566419406 566419417
    0x509011121070903030912020d0b16080c0f03010b0306031e2104360f020903070f06020d050a0c080403140c090613021e07050601060306060503070801061803020303 72
    0x16038081c40d00c007030203109400394400c1c010103800420644080030b0001a4004401c0c909480e50600c581c60310291520204082c4c00040c40042d10912064040000284040d941ca02c00a2659911301c45141c8a8000c5400a0b018418151810520520041c00286076902c0610350100004040f1941442005002140d03007400300200815904100300c2542c44015107500d0342014031103051480d00d00307443c006503e102c0c0481092040f104c1c041100c00c40c000f080d550120741c0074000007801c2c1084025084201d4000944c40904958002e000d1807800241c000601400031003103a116401806c1c45e134800d6041124150301950112080c003940350300c280041946440680b002e54803d00c442001c45000f0f8111601c4d003004902c2080c800c041074001c200f40d030b8480d40ca81c08034003140c420740980c4418600c070040302c00d0340d22601ca0280c415004100da4042c403000182503412180c96071010450303d40c81d1242103d05102c12104003000c11030710170040200310b1107500c4d40c101481c020b42c007400d049a100d90000e403c42e0f210 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 566421906 1250 566420656 566420677
    0x40c1a0a110703020a050907020a06060b091203040b0703230703110c1f0309050f0d05040303090906140f0103140703060602010e06040b04170c03072d1505090111 71
    0x400c40281881e008115804011070300002005002d10390360001c1c64401050242c44d00074074041c00403411183c020010160032a0b84132506000f820b45a0a51200d15044400f0b103038896038a09261500d41c1e64040708890a4800b140c060600d020800e880641e0070509840244000400d4404410306958a040140201030320903035481401000042c1118507254150110511490b90070102030380600010424503920110740c200070400c07441a08205007030059185d6005035030b0140440244c14a54030030014026030780300e6240c5a0030700b616103610100320784031402200c9040b1038085080b03d040c40c211883d581500380525000c10a05408420052100c20685464012030348903c811300070240c0a01030804c8680ca203c008100f280b82a4851440d0035070050310207480b55410b4060300549403030324421501c51100700402ca95030f8001a2038240d00c0c0d0306103c000c42c8a80d002e107194a241a605181180161a40182c004018809100c00f030000a090252024150f9940c078881820a41074140250504510 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 566423156 1250 566421906 566421959
    0xa1803030e01030e010203070c0320061303030c021b1909021b1e10050a0e06040516140609090601094205030429011e0b0a0c0209040c 59
    0x14a0780014040d1480c0f114070407900d034014000c106800d680090040c11085d01172400c4603505680707400304001600414a04a070b2800f815040204100c850001224070398030a81d0200700c2841c00b214126144d00560003072103900101004d0000d0146854050801c1804007440c07821001da9462000a0407a440380e03101c0c07440011030f410b06400724003060007401e0140c007000811101d4508032040b1307180c45000001040d4a0907a413140429810540c9070f0000032030310854000c032042420716041440e91020504400c503070502c0081c00104e0108210503805003982e80281c01c0030b0400070540104546d040000345401d040003404900019164202003956010f0100071503500c240b103e6510f40164002001c21803205040100380c020702199600c041240e41c0700b41c00402564205817240d408801c1c2e6010889101d404040d000c0022900f5814918036080004c070030070021582d00d40d00c041d040b0142c00307641444800b15021111200160a082c014140c2c402d08c10456155404e4541e0003070000c0300c1d0586400c004840 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 566424406 1250 566423156 566423177
    0x2030106030e0f0601060c1e230f010614010f020c03010f021804061a03130609150507140d0c0c120305100e04050705060d0f0903110c090118020a180303 67
    0x207000780b0403d01c00107400006400c0c0d41d03040980160810003041d40c001d006d0a40000c00301c507000359080344245400c1d8410b00c1c108071498a0002e100705a02c408803849079070301903a030351050800340c1403050b03604655642111190703085035500152819500b4452140c00d5005030382151450769403e100e4000d00c0d2912810058a40c4c40002d2140210072400008501030307440c010003031016079080e012001c2000380009585603660340318540b902555074940350080c0054101440101000a80c01c1e40707011400c86400100015a100074046990041d01c0100d01c4020104200c454005942d07a040441c61400500704508180082d035135000000754484040d41c00070342e0b40c0003400003908003404541c000746030806121a03036090070b0320741c03985501d03407442003900c150f10002d400614403405402c8034501a296840c10050400e41d820007419407044034018610364007c104880d849882d003100042e0507210034a504100564009128400075402030b03100d4400e010110404510002503442140051031183da1490a2071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 566425656 1250 566424406 566424431
    0x209030d02070f080f19050a120c150506090f070201060308040f090606111207060b090406050105010207080a0503090f0109080a0305090406060e1e0a0512011b0804020a270203010603 80
    0x142c0303804c4900703650004080c0c16080e03500090041140e0318000241c1d000c2059500c0d10903c0c00842c2c41c80100032591030101b02c12050b400c050f803003c80600a8503140f0f031825a07280c8200c111102210310780d81c000d000c0c002080b044001d94007a01d5000c059800001801a2a0744075882580c21a60100c0312900070540c091000c818107004800050203541441103070141c01c00d440546942117000b8060b000c2e0070100740b01c130030b10586801540e1a90005803028041c0c4c201404c055001d02002d000e0580540308071180041c0703420000601461480e04840a5405c0c03804c00c0b02000724988648040d681001164100030411841c00e0000134401407003603c0302c83d07a0301c02782c00520080c2da18650000c170a01020304080b12441e200d002500d481091440740c0f003400022240c001030050303026504040c0d00064207a1707188016a00551002d408050b01105019a44648a90444256100307c400135004060b0741010080161720303124000641103945401c0f41e8800d04140c008089820036404070b400a610383c00e090041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 566426906 1250 566425656 566425679
    0x1704051c060c0305070c0f08091f0212030c0403082a0d0306050d0b0a0f0f0608010e1002041a0708160b070806100f0513051e090a021213060209030d0207 67
    0x402c10070708040c801442c0284000e07020b14084071000d41840800e40d50340b8104480882101d41c1110300524608603050701070045500d20042580e10350140c407641c082045544400340680780f15001c40c2641c00d20b800d086076103d9001e50800c1e00c45002c3c40c0c00a58254100c3d102001c105010981243d000b04400c0b40400e50043c00e4410a6003ca03000c0d600607100380c0c0200e0844202940c0c40b84500001159004103010944014941e92140301d113460300d80341020075003074410340004101804c0c0c5011124075010100f45501244243d00c50880c012040500c5402c06100300300262a40c940540003072030605c03060318030142c81001150300c11542690721104200720940c0050302150000c4040c3c59560604030386400c050024406103a03c4018003e000c1030300c1766801c200003440301c064080a800c841400460074604102d115558035098801c01d2100001503e5900310b01c02c7d41d100070b0456180e034407191102c0342e1210f00d040d5019425242c4d00d070200089415a14100400b101d24022a40146840b40c64a40000c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 566428156 1250 566426906 566426921
    0x30909060338040b040f0203060f19020414090603070b04031b060f09170c04110a27050625240b01140a17090102091e0303071704051c06 60
    0x500e02c602070461100140d80000e10769000f40c0c0b100c2d43c1d00d081c0e1664104651501080b640084d03042c0f20744010810100348280011380aa103010041c000c8282500d1013001c164096405440d844901040c102c941524045110700d0b0005070203002d4500850300c1e1031070b4000d20b60094000340c5502d99085940f52100741c260303000350003c01075860410800c0d5a64a80145414110700c0380b81c450b00500c09001040b04030034888100381c40d10080c01000380c0007000318560b2258009405040200e2400342008040c860f00010b0900180e2080c61940c07923031400c0c4410000c0d980c100c0800c40c10f01622410000000084850060000718000d8000408924925040c0740000e4000c4140034480c500b00620341c10603076041a04a4110b440f0206e441e0b40312203100c40704941d480c1c1000407651189031894180208900198024031003020151400c504003001d0603000c031507000a0300c0485405500400c411408500043c0c0c400703218001481845162603036600006d182c01102c2500901d0701034044034140c0800c60588150030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 566429406 1250 566428156 566428223
    0x60806042604051c02040b06160c0608070f031a040f0f0501090204081b03032a060c130b0c330f0708010b0a02010207050601060906020105240d0309090603 68
    0x14980307802c080106030301e07040b00c0c0024004d000c00e2850040440d500c9801030000c0000140c64191180c008454103465460085010b584030409080c000c15194072a030006846040315031540140d02000c0e8030b00300c00038009030811052545006851400d5a40c071400340081c1b101110078085a68040022061f0071100d040e84000e4900e441000200006000820b80c0c202d0b41e1150500318824040481c042030851003450b0b803104d05220310150403561a1804004012201003682c2100d0507513481c41f0906609106500b170040b0080042074041010382040802056880341c0d4205035101403200c0c2c0207030030000c48c4100540030408407916448032004801a03042c0d602080311824210b1a052855001e042c101060044c48400d01b400145030700e80f28001d4048235440d6520100b102c04941e99160010701000c0e19003e40c7c0019420030b0040f481c1041c0e032641d1200d2548948010b0540294610200100000c108604900f0f04c4905040010b0780d01043c0700311802923006481490418410702c81d034583c0300c040e405980303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 566430656 1250 566429406 566429483
    0x807020a020f0f0d06110c10111603170c1905212805040b0606130e060a17010209030c31090b07020c0901050102010e060a090606080604 60
    0xc0566140b800d200c000150542d44201c03846804400301d14074081007100075080c00e0a040c0b554009031849001003444141060607a444445000701113000d40d80d400c000200e0100080c0305525203100460320996100d48641050f5240712803060075910692001c98034030002c0980400c11029403141e00081018113200c5161151034240500c81a015280101010079840f080d581d0020358040c7c1c08400c2001040a1400544024040d42c0c00c0c400240600700c4048604400300c60108820341800001d81d10421446120802c0050401d04034124107c0d00412165000e00c8a420020300d1069102c0104a40380400d000940d070b9021000c103041c07a1144000106000c3c10100c6200d010900750003c224542c091260030341c101c000c03801d904400140c0440310b0080c0041c00000c05200c5c4403500060742d03410100082d201201260b030303100016800c03540c0c1030607902c019070401000644904159440001094803602c0700140040c3c481000514003041141c007103c0001842540d850400034040074ac1504e29480b0703081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 566431906 1250 566430656 566430673
    0xb091602071a040e0a2007020a061d0409030216060215090304030c15021204091e05010803120c12070203040915060c1b0b0d09060501050303070209041e080406030c080702 75
    0x481910b0f11551041e60694508100815290700c41030b0005103c078080d1221000d55480d208201c00059171000700124803402001c00000340e0306000c0d480050010b0880d1040403402d270302c01400d001c060325100c48200e04501804022200c02500c11680d880a0185a4018038500c1440e4014034004040905140042e03401400208000384440f0700e0035064500d441e41140402601c070754140c0c40c21170361192440340c00b0400b14000c80c81075110340c010b40c80b000c1e2205405103003035526000f50040340d41c00c1c01840a1364204100c42c0c400340311a03950755500455010713183ea14141458000f1010b0b41000d507040801604001403c0000d07101c507000d07099191200b0303140b4440403803400704003420004000c80000d21003c400c190209104a6401d018801003281d404001c0d96040c030020b108004181d44001103a81a240000101d52401c0010a88040540c00b41c14401151615195107100d941004111161031460030301c2d400c0010a914003406c01405191400b05140d2180c185c00b902d8882e000f00960300315444030300c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 566433156 1250 566431906 566431949
    0x509060609061507020604031505161e09050a1212020705030703030809010e2d0303130f020303160302010903030c020f07032603100603061d0a0b040b09160207 70
    0x10219000b800c200c503402d1004541040d4202c160080c90030295000c1d1002c140082407110003c80311880c03c105283c10819540c030015106c100c0c540c10852140000d280c2610248a500c0523407600400b0170311030620501d2a650385000400c00e040c59000600518281e1800d8030800c005801030034013052007800a003403001d04100100b42d84000900c0060304000040d4085000c01d2020b62202c80000310b000c090b40d410010720036074000c140e440191000b0012120f0000146800782c084256802403c12040b00f1a02038003039241c80c540e848100400f0390340350000f007140c0d40c1072103a5000c8a003401882900049044143c60a0150840c2d104013084001c0d5006103140d96004100425001c1c15070358004070036204405801d02c10181c0540802035070140c800001b003070080585441c21254100c801c655010300c05140c4508101d0401d04d504441d41c40400040c101040440c01660021104518080d0000400b018000005078138450305031494107541e103d407102c00e11100d0b4184030b000f01411000c0120b5007900031030803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 566434406 1250 566433156 566433169
    0x20106120b0f07050705060a0c02060a0c050910030e03072402030c030a0e0c1e030d02032515050406050402041103130602030a09050a030206010617160309060617030a020105090606 79
    0x602c0c0903070624800e80020300a6002c3d0301500c03076145e04003045a14910300800e1010080951400c004054424031002403602d6085000d00420f201080d65034a040250724000d00000400c03840062080c540c980c0c000c000784070000c0026112240c0641c205129529940c0ca42200d90344014508101041c010800c003d540750720f83c4112a000b6601d604006080c0300319521882c00c002d2000021035000749040e86144450900d4161f07251480000c50540300722800303081090b40c0ea44076280da040c54012030b68078201d541c12042207212507140d00130860481c81c84c8000102008543c0c0455003165000c1e941c00511042d400d103881428001c80c0401d500d240380d401c0200464180c42103211008100a4000000450001041e0800480c4980c4442220222081b500d006074450009007c0e01e00080c039081103000e6078034404105035010702c05041c1212116241100120003911034410195a00d50300c4130000641d00c44c50145461010011201441c0c6414201000900751900908031106991010090000650310320 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 566435656 1250 566434406 566434411
    0x5040302060304110310020c010b090405120a0201020d0f020705010b09042f040908070b130f06090320030a030605090f0a09140f072408070302130f080706020106120b 73
    0x440d5640c0d10783c3e40728500307100d004074168106501802040454125821179030080c0843d002030000a00c101c440700c40c03e0000344c82d8215400342c1154007065050381400651002410f04000510000d49022800c84c52103080e01e6001d1705d281c40071540007503000d00303008082c80f540e004444116202030003418203441e401c07400c0202c3c00042ca040010b10401d02c07042d8010490010b1200005071090205004904104000e90440a800c0e60501800d41c0010300c98140020003a40c3c1030392140f480c8141c00c8007030312060b0080c500d40a0031400d000030988008103d45601c14070982000c8032174025555403c0590009050720400c1e03009038001c1c8000d805000301101389007012a40551000c00000b0000031a0400803044450300c2d0301c0f807031580958010680d580d04003152034000d86095842d070003042c8a1181d600040c58013100c030322a00069038280400d00d0b0b540b0a400038885080e4010741310302c4080d15404000031541d50340d40300442c107500a201c10000130790203020320001810940c20642d640c48103a1110400c01000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 566436906 1250 566435656 566435659
    0x60c200f1f0603020904050c040506030f0307080313020306040f061a03030f070303021c020301080d0806030c01200f0a060e01051012030215090c010905090601050412020a080303090610050103090305040302 90
    0x2031240703880380501030b50000c001180c008011049506150800544512189001ca40501e003400001790035402c000403030280da0301018000310300d030025079102c00489030009031460110010b900f003100003681c0d0401006009601030308245699520901d01001169440c4142e1500d40d03c805c0c5652103559408003c5d50100b030072400507250b80e0101840c0480013403041308040c50000148000f8a0000001c590245060340c5440c0100e400490100c40c0645000c1c804441c0641e066101c0f405d04d403115481002e01c10034150014840c6503c100103c00118200080c0c0c890141c450381c01500c1c8102800360b03c1c05440031103018030f80204200e050490340e8012032102d9000300341030041d100311000e0415100b040301010b80c0c006000820f260b03040411901c1d48810040c00303018001089420082100d103015410b16005000584900d8505460001d0425401c09003042c281e0b840900d48500140410080c402075200703050680c0940964a042040c500405819401c014109441c04602e840040c0e0008215015070b0380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 566438156 1250 566436906 566436943
    0x1171c1d0a0306050106050a02070504090b150312220f050906010f02030d1a1e1c0804030b0a0617070510050c0a0c080105101403060c0a0c060c200f 65
    0x1540c01081e098026940003e00c154544000098482c0e803000250907080344030780c01d413030903660780d0030421040c5c13420848082c001010000110340041d400d95000c1c503400c040501070b58607201c20941d08245940240d0001c68094500c0c07038011141c9912442214090024607000f0341d5117500300808900440c200401d0a030600202500300b02c00c440c000c0013070368a1518003410500000038414030b1840303400540380402e13010b40c0f09a80140d1203074003030384040d040204014108004295030392080800300c60303c0320402d8030715900c200000700c04962042806031040031048800710702146480e0000c40c006030910300124198010141c00d100941d50025a90613845552a0550b150140b03190007500b0103004900003030401c2d522a0002540d4039040d040316104020f500c104090440d9543c0d07a884c4000100740070321340c2c1a0040c100041140300d10101814280c0c0c101c0c540704605c0f0480e9500d0030200c44118101c070300411070300340b845a005a60014002c010b01c100502408101a825400c2c0f6602c0c1d80e10f0010081254 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 566439406 1250 566438156 566438207
    0x260d0216081c1b0b100f0803090114300402030601050a1202010c021503160207060e03070902030a020f0f0c100219031a0414010806010b0c1c1701171c 66
    0x185001500307195260021304040050803e1030480c803107202d4510482c5c441180c0c0c22000606000088142e503030810b0182c541a03613903ea400b210b120270394000140041e465803039105450a4000540003c002c090001d03080d0f0307100342080e004240c035010050b0310013131103001402804e004078184101503400311982070803c800180401d100180a200820302910900c500201c104400c1e0700900c81c010881c03201030b070203441c2c1264441d8012103003240a1002240c040c1d01450b4101708034091035004580c00215841c0040c1402d940040800180d803091322002100c40e00440d4001d44038005000f00306244080d00821071400c1e0102242112181c0c01514840905030388954000c51910044c0c561400807400410404c000c8000f80481100c28000703006101992180c00008034107098132a045070302c003140c240000c00c040c001e021101060040020340c00010004100000c1c8460700040f54114040c001c1c07184040c2d46440c890602a1405140800c5248800482d03030b050140a03030061805d10100300003000c0d122295 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 566440656 1250 566439406 566439437
    0x1306020322030c110406050f190b07030203070b0f07080a0b2121030c19030e100f14010e160212070308010612050f01260d0216081c 58
    0x2104030301c000079035035005010340c94105940000c01c0600c50384600e044110454a02040c4003ca0301180141d40c0c01901c45400340000c0d01e00703074a41150050070381c1c6080500c59211a060307a00b6812013801100036034808186001045801000301c1d61010748080d82d04035a1605050040500c1d0001d04900d495681c0c03006503c0d00d9031141040155a050b0810f9410079240182124a9442d50808421444940104060680441c100007203d001d01540040701303040050031030000300c2c24000051040107060b651360142c0e18584050082580c0c43e0b580d80c0303001900362100007110040e18410701d000090803d480d001404240240e224940e00a503001406015004044005924025005190110340ca070b0200d100b00415521588840c1a035506a60b0081c1c044840205141920b60540e04400060104001031050019101c0382d0360000980312661a075824103124030508015010030b45000682090b01c8040b87c0d4054800041c0003010703c14014a2092140a1246e10400c1c1400f0074804002258003846100f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 566441906 1250 566440656 566440681
    0xe070203092e0518010302090d02010822120f0c02030709110f040305030406020d110604111512090c0d0b060d06021209030408010c030501031208040203070f06020604060b060313060203 81
    0x49045a45002c00510824100a8460381054000c3d1200d4004540400d00c1544203009503a102d10b07000c1c00039030b04640c00e5401540c0d000330042c2403a90b45640c080c15104172040c210110029240515800f059030006a0300c010880100b4459000c20f000c40100c5000042c2c0340011710400301c0307030808800201d800e51200400131a101d100400014240046004002e0010100080007200c0d101e408580f000320200601b55a9503e4400046440e42c0002000502080002e04d5520b2001c1c402804064288080c13544519250403039120a50041140c2c0100054104108041c920f646400c8400090748a03007a541c070360800e08020a0701380241d440302c102000300701d8103405a03814654564800101ea141c0110660b40d41d0304140300c2e050803582030049c00143c032802441100d042e6038100361001303011000c0703100540d000b00014200700d82510071420009081d08441108501520541d8007415803418141058400d4403900185107204480401c14000790291030f817081c88d0320b2a441000580c4980d00e0100c0c403001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 566443156 1250 566441906 566441959
    0x40515131b0503010f0b040605030705011b0201020c10030509071707060513211e02060d0c121a0f0316060c05030903060412030f050103031b050102040503070e010806010e07020309 79
    0x7003540c05d04002914a214941180900c103100755401c1002c15501c03010507581322020b2040fa40030501c7c0c100040301480701c16030740148841c01801141c0405600d580810217036201006800d00180e510828809661003d000710401440740004840034050b151103070503182c4c1411710628050144c00288d00981414602c036110090101d64400100d00582c1200110341c0078101c08103d5441044060001c8842c0d07010f207081c511035401030042802d096180c454000281088030038501808014101600481054000d112042891088990000340f44605015815401601481c801d03080300405030072281e046005201201c000d842d00d844d040b550785c02e0050a41c8a090b0344075400d80141002c005c240101110034507400092a60f04003d4800300300030090480c1d1007808001c00007052461080300e0381d03903000311142e142e60044000520301607913400007905d40003072a4020026803140b00c00400c405141032200d940180442002c1088074035020030000c0d06ea01c2070b0b44940c6c0c420120102107906c2ca0f5600c444241 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 566444406 1250 566443156 566443159
    0xb030c070611040e180d050409050403051e0c0c030309060d15080610051003090f02090712090c060305060117061909020a030608011104030b0a051305030a08040515131b05 75
    0x503996915060101030592045861a401c0c0c02d85c400465419480041c40c1500d20030199102e13820141011114006468042d10a50403c20b05102881c5a100c40410b240203105400b0b01050359100002031030760900c0186c88841e0f21a8109000034501503c5501c1215500480880d002a58100d07102c00426401551f4000400034484c10301005900f44405408005540b411280c10b807000c013001d070084050312038100c001042d10605c80740c0c070801401c2a2042a4100b0001d00b04900300311158900002140c641c240300b60b0b00803c2c1e1074000c10009070544030fa80c0d0000e4080c40d0501d0148031409584c00e0451001d40060b000d0011044c107a0f403e51010303400ca4002d800704880a650b12081c070440207001e130415004407a150351070b00d9645103c02408208503402c40f6408000c0703401c5030392409850402407a0040030703c2d070751000442820000940601c01007203840e05a40b5584c8407420141002c502c0d100100da05c826800d8115028814900310110300c08210b1544040105182c651585400d0160701803035010a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 566445656 1250 566444406 566444441
    0x60903050f070b04110901060210051015030504020907090308030415020d0501060809101b050310090510030c1d1302031018210507170903101b0201060b030c0706 71
    0x142c1045592402a80200c0c0601e16045181a2500800007801420301c6001d000d07074449405880d46c0031a94108640c0700e60400301010f000c45e5a0345099098140b0701e4190000280d0f17501c00c003c1140f5005a029412690031710301190b90b581160340d10945403002030300140c924ac1c12000c005440303900c01d030101c03020302d0240e1500b40015695071001a10080c4140d80d5100301e80980058000c80003078610802180c6c80301411215800101414141e0301580044c045807001c3c40100f40110303d40c022401803070b000b980c15000780003485240d0700302802000a5600b10756a00c02c0600c0e80e00307802d02900c0e034cc0c564000c1404c1071b2151100002e403000030700c2e101038180b5a6082500b440680000c0d624401c1c07403081200d0060394049111000300b081010300c0b0250f02d101ca00440c1060242c0c4001c1501842d046c80c060508000e014a0064408002842d2041c1090102e0003661101c00350384410000c0d070180c07103807003025000910200d42060721120050100070200c40800d10007085580c240030150300003100c0038000441d01d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 566446906 1250 566445656 566445667
    0x10f0609171f050108010507110c0f01050c060c0a0f020d050d020d090b010e011a0702100c020a1d150301091a150603090610080604050705130b09090c010e0604060903060903050f 78
    0x820040d03e03003407003090519485c04001411003030151604151f18545003001c0d182e04d140c00010040c0071504200b0041c1003100900200490728020880305016410a0042070b0301e4071480240200902a125804c0302190032003655407403020341000070340b01001202030b005a243e5032010368070801450450700107031141c5900400000e0405564950301d05950318200680b40c04080329040d01010f20821034025000140108060b80840c8501c82010802d84014202c1c141966100c071040711924180e06550f60685800c0c00b030110b005402c8040511074801a8028000780351070b922410340c410380d481c6188554403202c0001030344a5855404410000d400100019160305080f00348070f0751014200c1d030040342500d44031800308d8002d41c000b80700d52080c3d50001c01085c4042c1840d040c0648402c2003452114a541c4039140868603584e8644802d1040d00c8a5008189440382d66000402c0c200c541d02c489401041304120600000364030048000c10340c0d40148011642c0d400c289001c460302c0c401d206100081c0c0c03801260 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 566448156 1250 566446906 566446963
    0x7030e031305010306140d0807021507060b0117011404110c030a120e06040506011a0d0e0c011d0f0f030c090c040311030d20150108070905010f060917 66
    0x74000c26140d003a40c1c2000b0458441d00c005010840220202d17511016029025002070b4188009208861001d01060341c4668000c2c0010a41c2e00110030031540d043d03c07005544e800e9640000c440b00c40b990203207008103940d4540011003000314120002d0724012915542c1090803608490b00701e803210381038402201e684003b105001000c0100c4c02c025442c145040022000303c0c40000501c8074000e641010142009900e007008111079480301d03850801c8401390138040e0480d500f2080c0308a02c0d512681c00098100da540310400140741080c1c11303a0580039442c10300d0003c211a2500c280c2000212000e840b035000c04074038000002d2500d6428041d10f43d000e5006010881030000100191003203074030507030b00b0411419960381095101c0c20000c030301100085221101001d51a280f00b20341c4481030751442620284403904007000c026a000341c0090b00c440c0c0c4805400c00c03044076180b244500500038401400710860816000814030045441614260081443c6c0c1d80e5400300f09020401a480b074000c0a0b0305020090f0b407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 566449406 1250 566448156 566448187
    0x70c23090c0414040902060a08040f2f0a060e01050901021c020a05100c0c020603061807050315010c080d021b030a020a1101030b0a18020403021203040312180e07030e03 74
    0x110351034a10300c5508203c0c03a0800d4040d03816450381c0102030700d08060141d01e0880d15020010002c1c0c0c0c50016100340c0f00302141c940181e030319030001003200c0c111030340d601507242d000c1d03540f807022245000f06c00c1010304209880d40080d02c6070880d2001d103801039943c000c610042386407030310140500155000701400482103c0d000100c2000c0f40d84618280d804d400e0414070010200e544030a401da010440c070034625001440c0040c0207580c4a600240081e1007103c12002240802804540300c10105100200f030112251034000004515002480c22621500c0d9943c1d8405081c003404140c0200540c020401d84840e2402a800b40a8140f4410840fa11a201c0d600c0095860110045c01d44490759040c00f41140d6512a026402a420020f043e280b4200d1030206801d0503411100603155182c0d90071f01000c00145e8802e03040500030300d241001552502c0c118208881c0d203214011295091000d602d51a010702c50743c00c480d68080314040c56068500f50f48034802500500702402074900d9038000029041000310f00702 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 566450656 1250 566449406 566449409
    0x901180e060906010617042402070b100e010f03150203090c0312091f0f0c0206090613050a080105090604030315030c03140115060504030b041703042006070c23090c04 73
    0x40c0d41b020250f50109101202080054802800c15402c0e20303003414262410000b55180c0204039900140740296a8848440f407a4054a000500701c034000c40420100b02ca8030091800f428203420610380181c595552046e8000e81d1009442d1440c1c5c001c400107495003410301046440040140565034410b0300c620804406611084105104c0d0240c81c02c3d5112036040728030041c801d00703040c0c0c0b076850150f590b1240c1a65242c43c4e0a034100d91100f000c004400c11503c6190150800c2420358a1802000c1c2c1400d042000580b4150040c503810fa25120810400b00350000320641c0040d01420000f410700f90358240f206600b4401e40002e4000d40c10040e0000c10041c21070a0365001e00d428a00801c50a90074658034001d0300103a104a0001640910042c40443d0400f40aaa00300e0301c071300b60300c8645c2c444014060559403c02c440558290100920f150103150003a0002d050221040360098900280e40e0f6540324884a6401845032209035170b0116400c2c2045411420340c02080140a00401e10303201810507025400b5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 566451906 1250 566450656 566450669
    0x30f0614040c0801230c03064002070201080c07050c0a1805060933100c0210140f0304050309040e070603150b03072f1b010804020901180e06090601 65
    0x7481170011254840d00200c0c0ea050320300010800680d00d580c001d071b24064001612170380d0310040c220b80c0142c4802c5031180c20006009078031428215070606040b42c184144005041000d80d5004001c050010b0f84e001c0f4115a21884814a142c2c8449081c24034074641928056003a800078101c840c08206504626105190300030a0354060115030350300c0c014403010ba081a10b412116141010300e031022204a00e4124038000a80c0300c24035007002043d400100c0045246040d007011500384001c19003503052076125084086060304290b000c0410301d40300c0340c0d002d200302200c80c080c02ca4003002003803c102003801201d0400c00000c200740841650410b02c10b88407880c501c9408007003864000c094400c0078020a01c072007144e1400f04000d0640c0d07600c1e60b065480031950818211f00c0e1070b0b00002030105e852900701450b107030101e2500605003400245a1030504c1042082e44d141400300308400c1200503655058502c0c15903581900307800e00c0c0d81e03084803080040d1800d5506107185000710400c00800e0200021041c0c100d039803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 566453156 1250 566451906 566451911
    0x6020606090612060a0b0d0b1003030206010803040b031b0c031305040b0a1d1005030a06060e0a05090a03230c011a1906080702030f0316090807050109030f0614040c0801 74
    0x1a600c0070000c1100060440f00900c0c0c1002c400603480c0940343c0e02c050506a07000e01141401d60055036a82c490400403980c070001e04c0c1c10f011050051650401c5010301400c80c1100540ca800e00b003010070645800f00415600341080281041c1b608025034109032140301404000300c940700c0034801000c0341c0f0b10034a070050750f008600e0000c1d484914607107011140100d908016000946628000d07503800360f0103008140500044030548000394503201007181e10580c81c0121070002c1c0290604044207226100a0814031100e07041c101800000070010503100b1134990306040c41c1400301180c1c04604540c0d420b0600c90454070502080c07208880d0410b410642020078544103031562020130350100304000d224255100042000188140400350207200c01f290800b4050040764103011084901702166401202d0180302040001c240002241c1c1201e60b0a010b8054400034104035801c0c50002480c11360184030141c02c0b0408054040140310196101050a02c5144070619480c9000d0400b8101c00307540b846495201d62 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 566454406 1250 566453156 566453161
    0x518070b0a03110c1e15040c06081b1305011206030807020d05010204150e091008030a0f110703210309020306070f02010237230f040905010602060609 66
    0x101059400590301244452070038060240011070007030a0801540129078020050b20065038410099504d4094050750010713160b02c24a50005d040407050880c50071200c0c110014040040c814903e03a0050398085e1500514950340d80040d80c0010020a47c000402d040c0050120039031840d8210b400140e940a0700c600000e00d40c440080c500b1100140300c0602075030024000980185010303031061518078011000941450b40b02d071115800602c1895046000c2010040d220b00b0360f050804d9031a6100f1a25040205148e2070310300c00e581c503032003180d544408200100d07407140c100f14005c900c6100b02c0d0b049182122201612864107038652801c0203c00780144041c0701d01c0a090038428060001d40710703070140140105480d401420b486d200000e54041041d5502400821140c12229001d400d10349c04800300707440d41d200c1044002e0105100440b81904100c044008040e50348010b414100c0712920401d1103d03924091903c100300c030b50103141c00442c08a810900002801940011501d02880c41150114501c0c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 566455656 1250 566454406 566454451
    0x706020d0206010f090908040812120c0a020a060c0912060c0207080708070e31020a12020904110f10030e100228031b020304081b0d080d060b0c0105 65
    0x100c2c400d01c110020000b40b01c40c2840079601c0c1d900041e050360701c690701c5541800d84440e226803c0c50034590380c1603084500810300400c000034031a031007900603d991000d00d1400f0141800292a8011810041e16150312000d010308118801da8a0304001d002c0c40c0c83e01c03d0501c2c1c1e54503250016082044064006100e580400f141d501d0f000704032942129080c10060451515049052022010040c01a441c1c2c852a40c0300303042aa00076a041d014031040004504142c000740d1040000f120380c0c680000300540303011800c0a0058a030068a01e820541013a440a121000b020000342424140c0385d4203a0007000c415904c215240d09a04907001004081058138013114400c0383e2801203005000001c510041000f50540c0b081b4a040401001c0318038500d008174580150449426050020500c3d00006134030014041103244401e006101915960706100c0c0c52600400300001d20142c3c1d8880c002d00041000240040200302e2984000300402100001c2070311355002208050007030400311501810794000a4415910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 566456906 1250 566455656 566455663
    0x1116060c050f011b0807020c040608010207210c061a120a1707151503061b08180705010f02030d050403030b01020f010c090b090f060c01060501120b0d1101020a060504050706020d02 79
    0x100700b103d0010080302e4280c41c05c03201c0200213090302c401d5005414001c0296200c03406418040d0107084000340c1d941c60310f40f03003441031082c01d0701c0c10780b6001c092034460b800c1059024030204003803a040240469a5820301d0942c0d0090440c3c0c0091035032002c02c3c40c0300c0600c0b85401064141d11580940451549102d407810b00c1c1c1e402d4030415100505580001074102110521a480202d01085041c03595840300d4603070b80e85000316844d0510f0120000d200010510300c490703024405550141300c0b0785046184012144080c0d984030840d01501d8184004001d001c95014820402c1e1088484071107424880c50806080150040010381c06d0180107000d40718021801080500948403003450f2562070440c800d140a02c111103a410000181e503100700d4050a40d41241d60700c002400d03181c11248000a8920302c3c040014100f04095072899200c2810b204120360702d50740b2510140941c91300061108018507901d40100d080c043d801c03c1c01440146070405010074010001804000e0b40c4080e02140c0001901c3d07003040c0e030f8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 566458156 1250 566456906 566456921
    0x3060a05040b06091e0a0614040b0a06050903120412030e01050306010c02041a040905030d0b0a081c0917010b10020f0a11030304030507060c03170f071116060c050f01 73
    0xc2c00c8420002c10418103040c11036980c0004014184810041c2ca07200040d0300d1101a2094103040d03894080501c13100090408003c2c003c08101c404102c0d1550706030110380d0074003c2d4840d8206204000c11814841c0d1401e000d40d040e400c203c0c40c241580d03181c8800e08013417800603c450030f9000420102240031254000c0701101e00480058440000407030311a8200301c050001c11032040c40400303804058100e90b0b12030b40511a070385072043d8003031905c50121031580d4007120300d5100c00c20300c41c0d03900b010108000d04000c100c103046c84501c00c0d072810580c041954244d441c0d05850b44440390110016840090f200030641c802005202c0032a5501d480300c0c184801265110000081281c440d00b001240e0000142410789031a07001c0c4010342601e08050340c0f85c0300c55040c01a5030b44410040345040101030300b01360b4060107c0c10b070007407550349510050402911080404100604a0090080c07001c070107002c4810401c4240b4503123000003980514103885582c014100381007250101e0b06440b80b07407810f524000060065a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 566459406 1250 566458156 566458163
    0x60e06040923030c03122a030a0e0703290a02040513020d1103041208070333080609030a03050108030301060c29040c06020d0f050405191d0603060a0504 67
    0x492500781d9030b1400c401410802603400a10040194084800c000d2014185c0c54030816602051447c01c141101c0c541c800100c0e03d1080c480034103140512004040040d00c0d0013106030301d00002e40c43c0540c6101c9103031551642000c0d05569028505252490b400c11030b8250740587d402518038140c6a0f00c0c455030a9000c1c60003a41c7c0e105d03044203004021041d6690250010381c10980c800701c0d00180100e2498000e9000703550544012a103502d0900210b600200480e4003c03070b5929040010404880402440f10103283c1c0c83e944548130b80164a400c441074420003c0503020a03c142c0f0551b09004030070741d03501d40c062441030300413a060100003c1c0c2030801000f568101c1c3c690b030b1076a0f1501c0100d0f60303c83c2d2210740c2c04020b449104500d40c00c2030b0f090052a06031103128911400702c0c1c080392401e00c8800703880d20904021001c20801c2104041e11441d40c0441134408444041e41c030540c0310611030508a111402c43d810001e1000b044580502e21003002c0455240030f4001601660511703103552201505860701190040e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 566460656 1250 566459406 566459423
    0x90f0c260319050904060e041703160305040201050c070f150c050a0303090305070503040b0405010314061005160602130306060f060203091c0f0308060108150f0d0c0506040801060e060409 82
    0x11800d000c11050040032102c601d14100380b07800d00380c000081c1140c02c150030102c034900c2108100801c0104406901418004501e4942e0662030030100e0310081201c030020100800d515040490308590044003610b01d2550b45c04140d0340000c0c2c603040c5003142c2041070310411003019410a040c07207605003e108005000c5070843e0241c0090a4140c406034081c00401200300e040000c10401140480c0c002d0014002801043c1d208a40e114034100004064030381d0700b4001086441038805200843e07840710080707040c030481c0d0b0401390f80b180e070250b440c01c40d040300c20940600000d0002031000e066103940c006c404143c902c20102041510703250003e81c030303200b05140038900259104004d00320080c90009420803c0c100c2807106003c414800d9170754075424116400044020903801c1050103081e44c2c008003001d40c00060100c980020807100d40000d45841045029107005501e489082e40500c46014540f5026000c0600003070760700c82d55554400c1c002d1041d071181070900703e040c0307010a07417600c2d007805803050891b00103664 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 566461906 1250 566460656 566460667
    0x121109090109212003041505130e01080303040f05030f04030b010f060309080a0c061b030203040312180f060b040c0c060509061b0a0207030c0f08070b0f030c030406090f0c2603 77
    0x11241300c241d5601039074124441804001000c1d0800c09580f0f03009092903071003030388603007000b02c0709401d40311650040d40300340743d50000500503000000203803035003c1d400824454000700c2d9400d01d58250700c5009201b10a070030b00002c0c003200380012480054100d0303500a010342e40c2183d41d038204a08440c2503d00040c151074007008003060042c416200410054007031400000c080e44c01e0104e1aa049005107413500120340c011042209142d003010661702c1080c6008002d00c43e0002d0440c3c441224807951200070721152244410a040c804164444085100c0140042141180401014043c10003400c070813110103040400160800c00c01080311409100c204d104144510143c440054282d0800015003085101d040000008602d800c0810b40050070ba8807406242c00341800e16240c1006107c0d044403400e203d080210b1070720440c041049a07480440c00240f01e031251100c1c5845005000e07102c1000e45041e0b48504218148038145282c0c03812101c2c0444800c0d45420729072000486110041240c43d00340c3c009100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 566463156 1250 566461906 566461937
    0x160503010608150a060f1d0108061011010c03050f090d021519050c0405031002030f040f0515041101120b150a020c0d0602070302010b0603010e0112110909010921 71
    0x42d00e504040c0629815200010403800b04c0c111114030380c440000600c0101402201d980c001041000d1a500540d1090300c0160800001c0c1900c031014240d0741c0076400c0c00090501030f610541310850003a4030480244440c1e069440002d000e80402d03503802e0700318082903000c1102c0100c000303940120300000e90041c084043c002000c14540340b06c010b0160b4000c9840d01c20340c1910345001d10949204000081e09161100d00f0001414985000c0507050b96000b44100184480381e2059401940d02039070100944000000914042d81010001501c4585000001051000f0404a51941c4185c400700785e03075110f1940f000710b01090035281c00143c00790b0003505020341c40c1280c000010007005078086600480b001c040c6070b05c0100344030388051502969030035400b207940020036a0a001e0071141a07804c8903000c0c10b6504040e049a2190410320038101e1400303403441444100800074000400800f00103000c1691440d1194005020b80f110210484d11050111000321403c461050824031055191b41d6a540b0001500f0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 566464406 1250 566463156 566463167
    0xe0a12060b0d05030d06060207080f060a050405240415050601120506030106051011061f140102120412020a0828020a1e090b0102211813020408061605030106 69
    0x1d0000e80103440b00040002141040006064035440303850001031070b600d000c000034100ba0450f005950079412890780400740301800501c503500070007207070400209501c072454014501a0780489669031003650340c291003003219112004902c03071409000e0200092000e010004102d510480b03131780340031540e20080020200e24503400160f00041c05000002c3d495241c40016002c50301c1c0c4121720000901d034a00c6c04440c02002e220351504013810340c1c003803440003c540d4509040a071860289819100980c01100490b82c03003040900d0289040e190941d81d6a901c600115081c541028400da0040101c1800080d101c5000182c0c0fa101410078485203003040083c41c0d9444103000d80030400d90340020700840100750166425241c10481c115444900710581c030f051071a0055581400d0b12905540000e01d5143e20720103001a441c51204d00301c40e080340d442c0301109284243d058116120b0b13412809504000f00c2c090f42d01d9008005440b85001102c2c9076540e122071380600c006000c0540c400148003800100310040c09907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 566465656 1250 566464406 566464421
    0x30a020f0c0d060c0c1b0614030103031b08131203180b030c070203010e061f060e010c0201141b0f07080a0f120203070f0804090c02030702030718060f0f060e0a1206 72
    0x9180c00060b1013041c1d1201c4080c100c0300b0941c2034041b40000003c2100a03004442c0c10a501e0314018114115891500d000d0a6815190448038605440543c3d01c0d0821044400f15901800100c40c4040f00540f503001c00741100d02c0e00300b003c40200b101403600c80030308806041c140003100c1c01c0f0040716166942d110004950741d040180c4c220703015921800ea1408441051200e288900c1030070031144131075410440000501401ca922003014040502c01d8040030341d9004c1d00d010065902070900e004a007105d03a0140030700e8800d4842407800c4420309417074100404000f040d5900c3c444c0444d400c8403052034032150519115000348100512540c42100340e040051403c0102d403a0740c98090040c6d900b0400e032511442049582007001300d40c080c00c00241440018611b01c100082200503200440c00c21585e940800c2c5c0d210254041c0034002005484407030f224025a81160f0007410207a107200101e960751f0102081c01c42d01c10301a03d00418a10590840c1a0500b0015641124035800c00808402420344400d8010000c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 566466906 1250 566465656 566465681
    0x50d090f05191e0e0a05070806100203040e04080d1503121404140d1505040c0603060303021b1c051507051e0d1401080c0108071e1d12030a020f0c0d06 66
    0x90754000120300744c8581c940c03031154070100000300d02031070880c0d8024610000100042d1240c4101c0620128203980001a141620584040950350b0348440c1007511150064a1700400c9840c2041c036205480b81e200c64050048078800c0d018550001c00894040e52050341e0751442080790380b0180310801100b81c01d90404411082c000e025000a0000381e2180346e0b020305001c681031015070b101c1c1c09001c02c02c80005440c000401991408000d000d0450303500039144c02c1440d40c8601d0551500aa0084594aa03280c2200f4401000e5400c0800c01e01440d05a0311442d1000c6604070110700d0000045500e4012421905aa403e000780b40c0c074485000c074844400341d084010004001507030755900d030200480e01d500c000d010b0b00e52500141401796442000402414006041c2c50400c10030030340d01e07591506035440350030039048242089640003100c140301c4481d441c3d50b9002e860b482002071a40719001a40400100b58100583d801d460346000d2610f4016aa2042000042d4126519400703a00106906a2200e10700d40704 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 566468156 1250 566466906 566466959
    0x1b03120204030c06110c010e0a0b03100b0c0a060501140306040221030f120601032711130b0114041d09010e0109030801050424030f020d050d090f0519 66
    0x460f91a2400a104903412450100702d09a4502807180c0d000c00c03510792043c0092030001544ca800c500402e514107414801c2850102011000c5000c049181e46040017404260200d01c1e02e0783d9000d0b10f42e80e610f40c0c8040341034400602d084000300c0c507000c407241091a040cc014005011540b69a420300000c0d0a5034448010400032510b500454403000b44002c0c50684403100030a078480c0642c10200d504904090402814985000c10700d00c1206c2259500079007000040a9990044181c0c0c2800d0890000b10214298030402781009000003906507403211000302c00a0b6520014140c442c0d5100003540b040f03005010b400760180440c6600b1800840300164010001e50000c190881107060842c00c1d12603042c8100e000c991003100500c4642014402c2d00c180102001a1318000c058040490700810550700000e459100c0314103010b410b5480d0491071f04521640181240c080c00041d0708000c1401c10240103103410420300d5580013880c0c0c680004a90f050024030078a80c10050301d00f84000f03601c0464001d00741c89110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 566469406 1250 566468156 566468159
    0x40212070e150109080c0f040c050f030c0c010b030a05060c0703090302120f0606011412060d15020403060612151505210d050703050d0b060f0705100c1b03120204 71
    0x40035a2850700603078803029400742550b925000034020198a4001d0002a4002c81040b095651400344a4962071405c0d500061145a5408121402c0c03140080305104140004140111000104020b244044036840200316111111003015108d000081c03001d0069400840410702449400c00108030040c42800d141428660326400f20b801d010601038040304c5c0d900540980c4021107024002c3e213502400034600100d0340e82c44d503050111940a21261240b641d0044c0c000240c840d210314083c44105031f00009000481460039240201a6025000440d0054141300300081d0301c0a0b00b00d6020442030303000e004000266064030920004040514503e9080b607903241c400a0030b900e41043c002400c1681c44072444110200828191038440e006c080700040080400c054170100303a1100070307601d1a02c049580800d1050780c1c440000c94901868006441d06440000c145013005000030300b248007400b261100340034000f0040c00a98141c2c00c120302d0803507201c0d00251309100092085180030003c80c6da1050060a1a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 566470656 1250 566469406 566469419
    0x1202012712060b120105100603020c210c100204030309090b040b09150102212b11090108060108043206010f0e010f1512021b03040f0b1204021207 64
    0x1401209002c1e11010754402165265041a100c076584081140d0003e00c81405c180c0c28446400c40e941c4134507804c242d4049078829a0340d03001c2c8010340000800c0800c2102c202a0665a80403c0d8011b0b000c56040d44102d00b0081c644030054001d0b00c00720b0fa00b41d00c81441c1c50b454070355480c010700041e028203540036941d020703080c01503910030307454901850401c500700d0044144400064a81007043c5a80c08004908480c0719400803220012038130120001e846954028100d02c4020748011100e4028074800303410700c650002131601000c080e0440345026030f11a440d9031915001503440d85010780f4007504a4505103c0d8404c01d1041c80cbd03000002d6130b5030b010070454a012a010b01424094283c0044101204141040200000074040c0502510030030b81c56600141ca844d444001401c940c0061106114009018003400e09196060700c40407012040d22406201960b4112a160380c428000c000d0900d41d01c20004c59401e00c407100341c0b40a186010311590b8580c07600d808002c5020a00c01e50742d00a031042e0000030551 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 566471906 1250 566470656 566470679
    0x6070c03111b030c0411090d03140304260c120f09060720011b030318060504030801080712020112022203050f060f04331e0612020127 59
    0x1650b00380e0000c1810079081e00b08150404a442c040c6070320a6003001c01c411688540c90048603a6400f00300e4003a0a80344044c50152900c03809114021144c99003c4104000d1210128142c8161b1180403032160031094030a0074170040b402209119034495000314910111104001c00030080008145000390a1641040001d4855031042008403002025003001101d840c0030100c241d50f01c6d51007424031583d20404040c040a084102002c09010540c5802c18441095503021080b40301c02d4000205100a28142c20090321160086c41000c4591150000001d220445a01801c061943c140d40c1c4e48011b07078004a0322400b81d0440c0b8400380b00c64900c056484030030450281c0072001544158042c1040d00e05909505042890082510b2140c400c0b06042200240c1d4900340151403401e1b16901d1061020a00003411690301110000078211349020344010360000c03100c01000c00c2040c3c0b15011300c5580d45403600850744c0a0710000003400303d1520407101441c01e40c0c00701007886070010800c50440d91551041c00248 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 566473156 1250 566471906 566471923
    0x50408090316050301152304110316110607050715020c0f210f09060315060a200706140a18090204060813020105030604090c050a08030301062006070c0311 68
    0x206880e40610400107814203010f5011b111600d40384a10150703280c281c5104000c1d40c0c4604035251400a076a52544a07901d0b680007648012101110680740e10340b000c1c4410a20314503605a80219002d8550035000110024100e4801d54072560341600700203807680c0d205444a565803145100580a2100c201046401c0040c4143c01c102c075001030400d844400a61040040c1c3c200702d2a5440c5030400440e4112032100f400c0312900c40702a1601c9550341d8079074415001c3c50883d2010780380d002400241c03500c100c0da80301c09107098030354100300300c4071418841d180c2c0a90b480449102d42e4010800344c001a03408200800060503020019060695080715513541900b045101d0350401d0760310560118007130000e0340e0302002250b032200c40709411050b401d0294001034498040140903900c01c640b68841002049908404c007401400080c0900c601070340c440d14030310f0b00c0390802d019400000340d03403a1128906200d45107110650340254070103007910391280c2c0300c21208c2104080c8203405002641e0716503032510a04100488 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 566474406 1250 566473156 566473183
    0x2060c010c120603080901050f1b010b0a050315010312200102040e0a0e0a0204020322050102040510020a0b0105011412131407030827060403050114010e0114040504080903 75
    0x80d410701c8140040c045100c0804540c2c0500c0c902202440002c001e00110b904510003420816100d1488a2036140c0d240724808000307100401f18544803401c400c054001c16018001190000459030722102813640d1f0f5120403244590320f1003424010408103003985e81004800c5201c2c50800b00102140a1040105014848035001603500250400101c02e2100000b034025141e42002c0c01041c8408264aa9070030106801034810b950000c040f9681500d122100c10705d4a46810041c07060540c5420102d000b5001441042d001d180714403035801e012840442d002c406541d102901407a0f590801004480c201d946034444103e140382080b814544103007450fa000e00c90780001031640d001c10032900e0080c01203c1c9102c80e81d88582d004000c18000a02c0d102d0503543c0d8103410542c01c1041600030603141c094028000d1900e030f041600050b0102c103200c41908200c45d4424800150142d5981c4c841083d00d00788024814660b8088000c80c92600c1c038074094020a4003d8010940103003000011000039040c00d00404020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 566475656 1250 566474406 566474411
    0x15031b09031109010b0d0b0406152304051806010216030609110102030a0f0309051509070f0b0a050901120e0607051315020703031809090305121003050c010e030a02060c01 75
    0xc00810060b05040d2605040c155691043c9502d000800c1c01c49000b01c070802d941160301d6010030a11034440c0e0740f15a004201012107520801b50a03c000b8041c05d4004002e25254102d0090903c410b2559508540031964050038034001d50080c03040e040c0c900d58005e41020304500520384010905940441d545002c4d5005131000580c1418034a040f1620075001c41c403060644d0800c0c40740480c3c180c6c10901071301100129050200703440006150007414922040c02c14000190b081c3e0a04c0441000080c3e81d2003510040d02d40040247e071100900d203058001d00c07074200000759041014821951080e2083c0002c02c0444074007054802c45210000d0800004030350540001da00170942c0030503d805801381a0040c00c41507000358505007000c1d402900c0381e000d400080d081c0024401c0c03a22620003407502c00c900a100414080000380101d00d801800b86c2d0080c81d00656814085010401c4100040e01c1c0000301e960010003000703840b0700c01006480d2502d100c0c11712a03060007060701078030260711454001d0000b1a03011000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 566476906 1250 566475656 566475659
    0x330f031e080f1209061f120f050601060504170a02060a201c03240b1c0608013903050901060305030f030711150703090c2309070f050415031b09 63
    0x62805d0002010f004d00c81ca004100c00c100c0d00b02c1c181069094070328042a02c1070341ea00a040400100c800031000911a110301000020400ea00c0409031082c0d40192140f0341001d4464015103a940c600f031311303001c2e500c107008000010005025180c0d9007941c180d030845414542d0121600141061469031001e5100000004500b403444d90500c84c00d01c1c0c01d240c8000c03142c0c048040d40c2d00841041403c1c0598101c1c5400080c0c01c20540001c00807402c4016034580c0140714960b180d0000302d01810318840000070034859004190541070614200c4000381c040c1c07030314501104402c0a4200c000d008003811110245d560b84502101140c428002811007010f04650141d6a081c200c10050020002c138100d6a030303540001d40301091071948050a203804c4241d901e0042100c4655090a02015440d41d001950038405407010444115604040c5480221304036040f60780c0e035135400420303160b10445003002000076070100801d0007100116208064054041e240000c3c0c1000000c0c141403001582820b072201140b0074460 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 566478156 1250 566476906 566476921
    0x20310170d14070c17011104270c0e010e060c0706020304030b090f06010e06012604120302030907060c0501090804060504030c060c020f100201330f031e080f12 70
    0x40b2003241d10091100918100094031002c882000d03034000c100c250b040b40400066050000d400080c0d80788805202540e5507070f695100901c105861041600068801100c03a60b100d881c0c51081e00d6103400f0507140c4950040c1040c0045814407813850b6166030041c0b06100c00f400c29103040203200041d01c00c82d00110750ba6402c3d401c1c13444854000034010141c592203081c05d8a1750f100c0100b4010304603000c40c299900a51614001641c50420103078004034240c903686040e4086088440015010360301491554046c421024812030a9200850380100164803506080201910452140b0340c018060400090700500550340d41c100b41c0e00c540c1c4203500184010070240700b40075401d90f200005007101d0030b0500e4500095408945130b00b2841030120305c03c070802420155080d00070f40103036a00380f011264046880c2100f011014191040b9511408549681000400e00201c22407000c1c01342d80d00181455807039944103410712000d43d1990340132907034220240040c07018800c03840c003e84800d9044010301740c0b26141c01030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 566479406 1250 566478156 566478167
    0x71b08010615090b04210314131403072301050c010f0923070306020f0c0f100e061e07050c060411040f090b0a0f060e040606030605010501020304030c0603020310170d 73
    0x1088004c01c407004001c10000054800b12204401003280700325034035155503080550b030003c00862094807800001940300345031050000c014061320500001300c034510419600341a070390100e500030390b0780c5424440340780c0c119441c140703011b044030500524180d49040c40d4107040c503007503480041c5407803800307a2200c444900704070303241d40d48045000e414903507109030b4170008400c0d55640642d0b10004c2c10300c1d5030019207031811801c1082150f50002c582c0040b16040100c85610f2540c0d03003540914052110300d04028542d5010010404502400040340c0e1490b4a0700c20b812031004000c030290000d800d0020400c4a903c0031242031199601c034902070440480425425000d110948501801103c9040e10b01460080000c1034420110b40210300d5940c000342803821107181000034107840c0c01010342c01d013000e42080208401c40d08810180d030b2092005000990341c4200590343c034011404014860342c40203d0034050144254059940f1254034007500c3c0c921a52112915a151060719201419400008500316600c0c1c025 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 566480656 1250 566479406 566479409
    0xc010209153a0f0b0f100504050f0f19050f06070c03020f03030714070923130c0b0f0c120301050306130309030b1f14010207050103020f070c080a050105090d05071b0801061509 77
    0x641c1e5100000e80c801c0001041485640141803040c0181c007034440c501d80300d407900c05903031810180c500c0c0300300c00b0450b050701d03030b000720300cdc45103504c0b8603551001300c00542400810341d02819844002064818150b5080150003e843d110194051100344803041c0890490101b04074403070079090240088504210307001080e07480d81002882d914082c02041e01d00141440c00c0107a01c45404030240c0d243c1c40b4540b4205010068650200302c2d5a08041420398181880c84000c1c04a004030f4011900543d5203a1500d9601d80000d204440d41034001d079001422560500d580c8035003862091500c40c3c032203078903951202024002900c03503880394003240b00384400125219070003001074018040b02d01c2032f0820740f10000f5501c0e00310303016007810984c000c918480c07454100c2050b00c8443c4da2122070070b41001d0310b8442207a07480e504650300b500c3c0c941c00c0001252103200040b0300c3d120030002507650240b8108054542c5260111780341407601c02010800b8000a0450080c031845024240c40c696810400c08490002048602503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 566481906 1250 566480656 566480659
    0xf0206090303011a1e0a030209030106120b04290f0a050901050c090d05030f16050d0309110402071113020c011a03150c0f0c010209153a0f0b0f 63
    0x82005100503c480c0c01a070f010180c6540c1c113917940d20003507114110302210109841c0d0604070041170380d103081034140c1c001c1c00180c14250003c016503507540f501004040c200005c054842d00e030100106011071900715458401c0da58010b111805605e80140b0740519400464683c0101c0f0070880c1841303040301e820f004141d00000c0c560000d01c00d50500d500380d0300da14480c0c070004a1160042080143c10002c080c015030340025001c0460310348610308401d481d40320068005044406025003072403c1d240901a10a1032205034101801c0d601484280701404001d500c500720a4510402440c0c0e1250603655800c201d2041070300441008d601c07440317800030300f50039103403103c20f2010320f0007030540c207110261030000b58104a40842c0c59a41c40507201e104c82881d0f21720034145800b108440c006008141500150020b0445100950359003051031380600c40c149840c06070b080c4e9480700381990740300c202203091061441c5000710300840c0070035200d03841281c046046559040400a6954403110000024030b0705906041a0030b40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 566483156 1250 566481906 566481913
    0x3070914041e020c0a05060c0304030801230411040806250f0c020f0a08030706050717010302030c040902031e0a06060503030a021e07030f0b060a080d0f1209020603070f020609 77
    0x207031003440d01c2c07090b00c40c50380d22600701c1e074045000c0c08030203070800202c4a03040d0001c06440b80da0400400c51009544111070a801103590000002828107518011038080025502441103c445900810002c0c1020024a80c0b440301c090102094022003400300034003518103494010080700d070746048440400481411502481041c005045000341c02182500c3d40560440d0103030b05186400d00000c115034620340201e00d142c0b10100307080f8100421603014a01440080e210701e00d02e0400caa007030740303800842400001d4143d007205072200040e0070b164000e21185403004080d940c00c1102c1d00310b0340c1c07842d0000d9404038120786c0c400503801060250a100d008090302064000d10310700190100c0180d078a03c401014010401d01281601d40d0400c07003840010065588080310344100c0b005030506000420050351b03101d118002c0304200068101c0700050700154110749847d40104000003406c00d071055110002e1015500c2d031200010001070740c03200003c0d0300c00c00c960340350f4076a104c4141c80000e20701a4001c022204690 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 566484406 1250 566483156 566483171
    0x10603080a0c1211100b06040e0403050a090f030305040b03070917010204140414040f030207150f02010c1e0e01030e071d0f0f040b0601030e0a140c041a04020c03040b0307091404 78
    0x42c4c003c540c043d01e1000442c0045200310740c1a0200359984075660060b0281c0481005000400d503201000742110308007555000001c03070300c5802214800c07116101c0180400e0041000b0408160a00040c0d03a0054040c00d02060342c0d6a601c3c6110382c4030302101348010050358009030901400b85d01c0c0000840c080c0043d41e0800a003072800c1c2542c44951409130019024146a90585080510800c5034001800d2480000c0e44a1400d01c0c10240682400c850035001550902c0b00700341e4000c0c45114085440342c031980000a03c101c2c4101e09494100c2e1000c071a80c105900c07100304420010041100034010000070149130300b41e0146030380b03081e500c02028000002d16605003040c42048a00c403030740d446d00300b070300110b2860440c0c0306c40300140c0080094841c0c07009030b406049a00e40c1800444107541d1012101d1409a4842c051254100000c032a50600e03040c2d24030b2289100140c1d581007a9024050000c0e03590101d078541a01c4174042a941e4000f2030302400050071511003400444060681807040304001d036820321605 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 566485656 1250 566484406 566484437
    0xa06020115091d0a0b04020f090402030d0305090c030703080a080601183b01060201061a03180a0f08040503100903051206061b1b1f11010603080a0c12 66
    0x520040c03185810041e00c030f0b004446511400081074200809000c110b54a480301c6142c1a10030b00c000700d50581c410704c2005010034442c28904405485654000c0c090080e148280c00140c0081c0009070620005208203200f118040e2010071900002c1c3d80140c00741a140c8114a00041100d48000c114904100f03180484515545c01d0419a8007030714228040380b00d403038040364008180644c0700804003441e4100c031002e0010710700d224035849060b9030050340280070194841c111007120381e10200c880000110204005500e46040791440c02c200c0400d0ba043d680c40140945a0314284003c0c10401d0320040b00000d0304020314901000440250798a0303181c05d00c50844d40351400b0f007541c010400540c0101c41c4180c005082a40c4078011968101100900c00b1102141c51121076034078a070300a4118000001908456a64075155144608070b80c0c141404010718052880c0c2140c4d40c850070b03088404a5900e0f180c000c0005294140941704541407a036680d11120014200400c03403c05031014042800001d81400500c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 566486906 1250 566485656 566485691
    0xf06080d030e03190e0a0e0622060801050903031806060a210c080f210405100c06090b0f060a0f060f0912030905090a05190504020319030e0a060201 65
    0x4506007400200824a0042c0c18114400e85444c1310300c0c412000c0780610866001080c00b200004243d480e48140d9840714046049558260703141c0b80d0016035000030f00211201b6008906003030a0400700480c10381c1c0e40f00141825520296001702d0103820200c10014a180c914136071300700c00d1591a00900d00da003000d9001ca11030200c82e0103007180049400f83c004034001810b40c03220181a5010360303640e100a9584020944036200001928080d008065071098020660603500007205070514150f4a803516060410080c54000351110381409545030303061011030094803a084403140205100b1342c00c1d1518512510703611100400381c9103c2d54003c403085c000410313141410001d481c141c2c00e003961980c4426100b902c0058031036100d810784500320307a080020164040d0261040710710542d200c440744e4071001861003d980f411a02101480780c401503c01d8001c01541041c4e4001d40007505032203601005500001020002c0c800903008101c503400d041441d8103200e81000000c1c60b041c402082014040c04d208142c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 566488156 1250 566486906 566486923
    0x15050307050304020f0f150c12130905060a1a040f05040905100e0a060501080c10051e030406320a060501020a020d0c0e150f060901050717040f030302060a0f0608 71
    0x15804a800c500141d841d040400300100100402440b51a400e24086600030b23400803c00402600801800051f03c040c0301007600c50b618000c0d01225803c0e4280040310005003001000c1c154006401c000c001703110051151808401c8900300030352a6214100b901c82c1c2c0310001a90300c910302907440c240c1d000000c83c0000c508a00144440100400d040344404240c4d403030001c2d10702d400b43c5520710780f000000702c09400041c811080a0142c60400141c420f80c103041d00c4038083d000c0e0a04001c448651200418040a001540c0c401e00c151000206a65221808000705503080900d185103c1c1c24181c408a00c10007040a56220902036400c1c80480d0600c0d0000303498400d1040700034003400d1984010020003a02209203000780c11030f00c0300080540b5000c0c3c20506010509a14280070b140c16a60990039410080b04654800c10306031079681c80c1507115a0340909070f05008500b0308105a0a0101050b50680c5858182c0190700aa00916040c14145424421160501d0300710760400d2400e2010000f0b00000f250250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 566489406 1250 566488156 566488159
    0x180c060f0d05070f23040b0a030905010612021003021c0c030207060f0b0f04200c06010609050306012115050a06090515010c12020c040c2006070519021c091505030705030402 76
    0x1a0f0b0170f8648042e0800c41c1c003d5421900d8004000f18401e103110b0362680c4070364151401403000340300c402d6942c0da4041ba180b242c2a40a50012503546006827024029002403c50483c8119500c61704114940e0103021140c00e508190300003070700020418244003203401103084141d5015000c0001c100048000f500a00c80500424011625200044000d06500f81201d010a0113030340040e036034260850b40e042d100c54003400741c0001300341500130100752030500041142c10380742d00007008004000a803007145040400d40504546145011942c134420700c046001d06405105813803000b1443c01e003003c80340d000f0703503c2c002d100715a109541100710080b683e01101140c07111b5001075040c803041041450490030f10000c0700c000750b002030826505a402552018014891134614101d0002d001c0302e4010b07558a07844250f0712003000070700900546018144141d954040000d035401255404069045403003d4010940342e040003041c3d0908040011542e07003003500c1d0b4140e21510703004d0300e103152240c0302500d41c1c000908080d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 566490656 1250 566489406 566489447
    0x90d020606030c0d030504030b010e10142121091e0f0d020105070c230607020904020112021209010203070905060301060c0609060f051f1409180c060f0d05070f 70
    0xb0700178075001d002113601031500003000e41090760711004181c081001c02e0f034102e81400c100303031000034048044001d0260034038401002c503012074079401d50202170440e01c0312202c4658041c8000c000c07004041d00b0714030704180c24403440441d00d0386059020450350482c06c1754000c0c44401410069a001c0c1d454001c14800140111401100c07032106000480710340c001c00318005e18050149074041200500441c2ca042d94507500603101c00e41c43c1e80e80301481014011020002e400080350340c007150042d800340d41d40c0d441c150106038005003003001031140040140e1050b9030b100e00c035035800014050745c4d40d804002080909429a015480c5502d4220001c1071b455075400041c018943d0317101c84004004980c1c20008000003e54800d100e6401c1400003e81e900c0d040341d07a410040039222400052144040310b50304035058005021700900c1d03642c2c0409078000c04401d080320704280a052140c0d540d583e2900c014000c2c825862001030f48a04020321408102e41e405480c840c20300000c103081e501e0342da5001340d01051005225604 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 566491906 1250 566490656 566490679
    0x150617090a02030f0105041106040522020d0606090e060a0b0301090e07120b070806040c020a08161b030b150d110a03060c210e030702101115090d020606030c 69
    0x40c200148454003c0d854000c20302c1d800140901500010b020f180601241d41030000150b0811510b8822481416040400c0550100c8040c290b03084219030412503103000343c904900e0a01d54070451b086508001d011401440c2c0c00e01107800098080307a4481d000f5212000325a04240d80081c69000510907032403000c2d02c0b02e16161144005026881c0200340e124603504883d01c10b881e101500520440d840310000c4c203010002442880c00b401410016405a00500510030068440e0000d60b072180040141d98840c15015400003101c050308420300300b2130000c1c082c80107415031038030980c0d00101424180c01546c11400d8020155200340601c40e025500c80302100d81ca9031110003045280340d00e60b101908003842d00d4a0030720400c0e00541c440c0070341c6e2024890761080c001441000310448503101c160302001e60050147c20f00508100c2100300c03204449040032610212030010061600c1c141c0540000660f1180c2c1c203104020104104a01c11581c29001074181340c5012808681e44054041e980da202c6c6071407884 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 566493156 1250 566491906 566491921
    0xd0b030a0206030f0c040504150801050a06060f260f1b1e0a111609060e0c0414060c0d0f030e0c0906090703020d02030103080717070c090507210504030201150617 71
    0x850303001f0407000d481407100395101001800e10020610964140d9421301001500d680001e104540c00e4030010b840b6280c1a8140e0103048402c1c91500c0c01603d00d0480f03150b4080541c030305a01e0042d20496403050785080c0c81c45c0900707101d10400f02e42d072035104035107006010410f1840101070b107031076042542c80700c81503d5003201003080710300c207105024200d0540184840280007140d400c40c10026145000e00034406543d482c054048680c400301c805d681320000c10300062101d140500d1000704040c100401a40c148106844010300342103000c104100480c052441e828203558250141c540c200b40c28a01411482954a0100700c0007200100304038801c100d00000603040701d000341d040e10116a2000d1301152a5a1689490f1042e0303441444265840d42024a00a8400c070545088948482e809010200c445150402d508080c1102504280500c0490681ca601111440400c00300c00d23030f9803003800300e0241018200070b803c540c01d0010f424541c00d0419010701986030000165061024080d030401482e0742c4500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 566494406 1250 566493156 566493181
    0x70b04020f180f07050f180f18040c1a120910060609081e12070c05060d09060f0c050a1214013c051201200d0b030a0206030f 55
    0x81c05a20420007426001420101811184100d240c0c094070a410703210540165098000c102540e404000d0401540c4407102c0f0041d10f02d07100d10301c060038a1001c62121400620b00d00070203d28504403c0d01c41e010801400f40f8060f646006182c1e07400340103030031820400a01020703c117010307180c824810641c0100c0d9001c0b004205001c03005003d0041080080d443e40802003540310180301d00350451207182c2e01700b21440754680b51208194800c43c020041c94100ba0401ca046811102041c0d0b40b40755410b40c0024030303850342c000410350078028501c00961200316207001c0d01240d000b1104828064a01242c40c00c0d000d0304001100c81d010842d0500d410401d16142410700078041303c482079607284020100001c0d401444104203042c60302c07440c05030140f40d15a20325a1b0104889207440d042c4514050714100710500b400d10030901034909500c0003042d8841014880038082c1c1c003643e85800400000035480c0d44141261054242000046001c0c0038200601d0f00000e0031400301030300501805806601040c58840d003c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 566495656 1250 566494406 566494429
    0x203042a051318330515210d0915020105190902130615020f010b0603010603112a070f0e0117100f1b170c0a05160602040f120503070b0402 61
    0x355130031900e107104c00300c40c00341d0310801e1070004802c10440c01003460040b0180144c61040f000f4210a081901008040143e442c601c290f80f40740160407081c08401d16401400851146212512459036440c0b8104009190000240501c07085904d4042481442108111001251011400041040400d44c00003d22020503c0d00c880c40c101d10384140050101c01012200110002c3e94007980c0240126030b15007402d030780103881001d90040d42040140203803070207075110310b80c07001141040504050781d50304406107514450881c504004100d22944d11014420040240070300305040e10000400c1c5480e003902e00d00c4d00107003d0041f812012031003c09203240100940b2211708061a0140708444c114050200142428800501281c0d082444920082d02604d01907596105a05d4000300995556011001a030042c045800801034100300c03808900d1340764003c4440d4140180700060707440b490141c0d68603d0160a61003d00b00030320403909480420004401d62740b001e500441c201180b035903144000741c2c078001e01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 566496906 1250 566495656 566495663
    0xb0103060b22080a12051b0f0c0a08010204050d150213090911040c053705031602060912070602040b040902073e0d060203042a051318 59
    0x2090540030703180d0b03105411102c9803012000480240e03c03a50002c0e2211400100a440f0350b02e20329182d40c03464030400041070010348a040c0e08030203042c80d03400340d0b0400300580200b424a5000c0e4002060f03030301d408480e1100a001d031000842c505450b000118914002805016281c242a0030303050248454680485800904044807006800e46998003200240140102916003801c040303585c1407103040610507504800210345500d418030030030b031000c100c003000f415010110384000000007a01d848240e0301030f900c445101d40c40e00c0d505d038544074141130b582801803442141158030204c140502d041c0702203504881c452090340091394070121070619001030f100340d0380641000c00c0001340005002c0d041c1e0780544900740c07080d41c034844c0c10602462020500e489040b00c42e800d00d0079103400d4010401403625502d22204000d00307094a48001521854100c0e0411141900c0041031010b1507288021030169203000da2100c04140321185080c4004244185102c82e103401d10b86942d000030340017688c1c0c410070710b110043d40f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 566498156 1250 566496906 566496929
    0x909010e010e1c03060303050f1e1b061f0e0c040503030f090414010e180f030f0a08070c0b040624030503040609050103020c0c04021e0a0306060f0305190b010306 71
    0x1840b5504559604101101d5078599003540f03208190785229001301821682c15660395410315960405403150340e030148901c011300002c2d40c0c0202c3c160000460203001e0800d8901450503403841c840d02410b04084c1c0c01809002c542c1d0030151f90481c0d00724139141080c01d640071810000500c0e5512104d41ca01032141c1d4001d5a418030001c01d80c840828110401420550302c150307400c1c0304183c90100a0f006400081c0100041403040a0010320009907000b900131240403008110303030a64160140003030031940314a5a0500b031440001d0140c5a00303030416034aa17003041383c516000380c0341003180d100e1045480c00a000200340351b4840c145084a4100c20040c0e07241400f00c002c1d4000c032513660780f50480c1e03268414851031000c5043d04400054560080c8240c82107030780c100010700140003000d010000294004000c00340c5541c2036008011440340709001074822010b441d100002c2007030900d4000b5103204a125000341c109401c00e0100103203158410460032042000040100e010f89402006801804040c0c01250b82d500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 566499406 1250 566498156 566498171
    0xe040608060f130f061b031407090302040218060f03060406080a0f0813170706030509030c0703080f040b0c0115090b06092202181c170306040b0a0e0a050606180909010e01 75
    0xb080b02c40c6d031185841581c4c60070442c2641c00002102d00101c100e9040d004a03500d0130080000d400e15070010705503000c6425028001c4680900090f00d1074009001d42c514090002c402c006e83c0d810300340f207144060016900140102c0031281d1b140d01c0c1d84100302500408a14011880665249000c090341c2c002d4500001600203003070503003100c1580c0d03500c94030585000074104008641000008421074092211141c0540111811922421242e40c001056511040c4c01000000780072109200138100c00d0b00c004001281d82d042e0808121080c82090300401c80c05c514042d4400a190b9596040b1214030070255a000440c10820b0001114243c6607060844001d000068040411401800760404890304840180c1d9040b0708411620007030f48540030050001c05202d00d91696056048040e42d40640f000b80081620090303c0c001c04c0900855a0224140384444e03803e0140700506406407ea22280036640e560400b1f02807401c80e42c00700500d90406006000090208a0b1a402074010507810003214000388a00d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 566500656 1250 566499406 566499431
    0x203010605030406050f100317041e03050f03040b090d0309090507020312090f030a081807030b040218091b150a0e0307060305010807050f1305070e040608060f130f06 73
    0x591040740c00304e4840b4a002e0000c0c8080d04403112007070040e6040d032480e0500c9400c0d50746003541d9424034104002903100074080040d800000341071000a480503a803014180c0351442c40c120f46800540c00102d9000c0e0000d01003030120b55819401e0700d4a0003000c076420940c2020509080e00c1c00219600315103511801c0c4001c02180c01c0e0000020940c0800302c0c2c1c0310110b603648513010300761511003040105480384c10030080c400100c4d02c5030440c40d804c065040190b9a000f0400ba002528180c80d41c1e2080f5000c0c1caa042c06c201c1985000c0302119002c0b040c01c0000c003101d00c3d0500d441505c3c4c0d04e40010344c1c00641070072041121207407191402d140c06020f401055940e19082c0c2800500b5030040d0804092091003100b50202c1d20f40d1003402114100c8048034020301404c1d041078100040300b4080844283c00902d0b00550340780a0f407190250350f0041400e0788680904010440070320042e90042e07001303c403841d4400014030210104c13001c40294025501407815480c0850f525003541100d4041e60040c2c440d600f040c82c0840314 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 566501906 1250 566500656 566500667
    0x2206090209040b15040608102304062903070501110a06060e041e0317040f0203100b030d0c080409181205190e011b020321030402040c1e1d0402030106 66
    0x4020200807543e01c10a0841003205071ba0700c6024074600c2e0740190070308c000e504000d90800c070b02002401c02c070820b202000300407103011003000b1942551100d40391210600e8000200500c403a031215100b149111011030034022a54440c803034800c41d810004511848501000d00384103050189920580910105a44850143c1d07448001d403800e030307107200c1c06500110100514a80001009601d92070b200014002580c080c8081c0200a2042d00ea00c2076501102005a8051003141c6404110400000311180c208051500d808803e5804038140400c2c000d050000c907503004181c6046908483c000b20700c2e01690744240c21f615140c20070040048403030300800180d144d004405031240c540c9013101c2c1c2c910300d070002d24102d403560a19000300d40407a003e00303104100b032800e920034501560300280440d14000c6068041d80001e07100c5140b4075407440808030612046203418004d541c1544003c0c41c0c000c0844400280b503d04c2d04100e49801c0701881444030034003401d007011000c0000c2c0940010720864903903a603440003518 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 566503156 1250 566501906 566501911
    0x60109050a060c0f11041505030c0904200315090607181a09040209030f1011030f0708150a090b0111010c05031305071809060f1a042c160e2206090209040b 68
    0x2700740140c0b8030502c8141000c1c02103e2040d60021042080a100c4600c2518000500d40519405003d00d150140e0081e25000006008203480002070a0524000707500400081886001c0c41020102040401240c10422803c0003000c0c0c15010f00380d51740c955000014000d2040d00400794150144007030642e1210004580c110305030308540c00034403001d10000710b800080c0c841210390104040c5060041044c0501c5002095401801816154110401100040d006401c0d551003216950307218001c1c01e5295920000840500030754074003d010404001a016006000080c40202401d500360000000c0c050200021001001410b00381d42c1107807614008140648107051064880608140080082d0b6010348035402c040800c15800181c9070786042d080101800307484d407a5803200ca2100c40e000d881c0c581d1f0314030841d144240d60402441c4600746100f6a80501d802503028501041c050005c00140d443c0c400206000601c071407181102d4a40b851800a0041c1040400a5042845d0f84208000c00c44101407090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 566504406 1250 566503156 566503159
    0xa1b0c090903111c0309030302090a170d020615040c090e070f0905180a0518031306020606060406140304020109150c030221070803091c0503060109050a060c0f11041505 74
    0x2803c6030b0030307000c065440e550250b0900013500200d0b0124032441c401c2d4003640c8400e00c07e02e405458100281d00043c00c08100390452084a41e041200e01d900703003010080118004001c5c001381c82240f40071700315a1103420202134130901940c0c480e5480c4020078443c0002002520003b90003010303501b00018003c4c150341c3c00d13100784408290800c0000c51145400803408610300704201024000355904900300e40940800b41051854428084121403000c8080c07019003885c08190303915044a51400c02e009182000184c6180c0c02144204801d04c481c5a12210b82c0580003042e0329502e64a0b00c40f440121070400441c1d10000102c002c102c4286503440c1d1107100a80118025800c585070090030350841c140040000d41c0500c1d907203508220600c0015100700c003031540715070040160b90381d60b010300380b214060040070520480040c2e000401c100c510b6800c000d448000d4642924803c4a07181001009800031610401c081c01040700b00d6100da04022403c425080d09100180040c41050255079904998010500645 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 566505656 1250 566504406 566504417
    0xc0204051308070807020f0a0e0403030e0c0a030302150a0e0703060218060c0d09171504020a0801020c1501080106031a040c15051b0d08130f020415080d020a02060a1b0c090903 77
    0x2047c00d2400c210901e00b0394117011005016600c2c0c40d6410307030081ca00d10100d01c0c0315006550350b5040680e00d1400d010300850194018100400742001c4481400f803006200390101781c0f80018400d281200098404161780d842040107a40c2d403410054134507480080090243c2c006000030350f52080f1540440c0303805c601d201070707202d0700c030616160b0000c05001c0410b5560318410340e015100144c2c00d019041c4803034be0014005050707034015989541d8810f003660b10203042010782e81d100d10002030203107404080e0740d401040d00c5402048281d0440d03580c4420310680f1002d003000003854401040c148240d0428a000400e0410380b80000c20703104201c003a00380d40080f440e400072603140314000d580d40d15021031031241c20b11180c0c0d00c08090340e4034550101000180d031003080d949079410341042c80058031140f0840000c84407000c0910030281c6004191494074009080c943c1c11504464000303001030320340e0304c2a6038982030b00b814103011901002b06154018503021700b003d000c100d5a55000210350542d580310307407441c030b01a50b200d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 566506906 1250 566505656 566505679
    0x60306020d2a0c02151305011407020a06030507052802160f06081008010204080120070c0905060d0f081902060f01030321020c010c0e010903030c020405130807080702 73
    0x301c042c0300340c04484198030840c0011058016501c200020340001e80300400038003603d44943c2150300260000416050168580d034804d02280d0382007038800c061160850041880e20580e54007281301c641c00d901c5480c1c2071588501c04a148280034800783c9421601000b1031090140181c1c43e1400700019404c00400580540480e41180b002d1403007015003540c0e0307e50000c095480c42c0101c1200c80040003403c0000c1c039882c00e4008600340800b07000038001042c03250700100d80140740070300350340d40b10700d804000051688042001d81c0c00194074132003442c11602d01c540006499038455000c10762403540400020700385200280d84108000003580903100300b66203083e8801c1c803402d080d0070590f0365030f00c1640c00300c00343c413044401000080d100d074207019440040d9043c40442105a4006c080c1660480da8808a40303075116400302110503480340d201c400d01042460410f400a01c1e50720040c09007501c5000c0640100c2e254800541826460140403031229440301c1400e90f1a02c190406404a4204110492091030481d28 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 566508156 1250 566506906 566506931
    0x20d120e06070f15180f2f010e030715030501140901030c1a070618151a0f1c0c08011b080712060f0f060801050904080f03040510060306020d 62
    0x152440d81c1d41c01081d040c40507000d0b88525621208504c01118015210600d4003043c0380010025040c9501c501040b2501c1441841e0400325100750f13004006810030b070003444d103036051010b43c1100311040c2d080c240500b4940001020078240002c0e50000c244d000c0c2192000c05070540c1c5680290304a51120780304000d108450800c008440d142840064111820285c00b44100e48a42c203850b01c500300b802070003038904440c5035100410340d80b6030542e4001804250000c10706000140050309c054122058040001c000710091940c3d065500754801402282d03500c00c0345d1840c0d210185601c84c6140d0020765081d00181034a040e01c800140340c0285012942081405094000c192040305a00c0c810b07a1100c3c00c4554440204568100d407140d182c901c896262680020004030314441030001e40740407030301124442d04080c00079041c11410392003540254400070400010840d401c0c00e45605d5200650155500d4846090461a06005041034030616203000000810806980c1c010310900c040c600c030900034020040d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 566509406 1250 566508156 566508169
    0x1050a050108070503130b0f092514040e0f010608070e06150c1c0816170c031b041e0b09011d01050f0309010603060b03031e1303020d120e 61
    0x4a6503001c41c5919000c0f0303011500401c05594031900c0d1582c00c2100094684450020940a0b80c0d10781590300f86c0006d0158803031083c440d0f00420200b6689041e044c592800000c0c1880e5564440d0701000c50403860904416a501d800800038045030710202d44107107030350a04031030090105110f0303100703240704140001514906401e550b510400000f8403940c040d00031008501d45135402112040311070b0041c0380c2a8203491a003054060041000f6594004a03460b010700d0410300d40c29400c070540244254a08406e020170381e41c8840642c8120284145030701c0f5114500c41c1150008031909003d034281c0c010401040040c04598070a030000c3d82e0300c45011031256201d003000b90601c60361402070b00044940008540c05601002c24904031041850181c2c1b070030019003100300aa4000350340581050f5102c0c07100708188002c5000e204042a0120082c501c0c101006c003050740c3c01c500c04140b0030303039080c00031910640400151107002c0003942c024020300e0004141385084600c040800c0700000128000000410310340c203212 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 566510656 1250 566509406 566509409
    0xf050102061618050414041403040b041a04051c02041a1309031b0b150a0506120603010618090b090708190206130b0703020d080402010c0605060d2001030501050a 71
    0x142c1c0c08040302c007050382c02140c1d60400141042e426618250000030301d03803641c0c400c241c02e8180c40001c03c0164202854120300d03040c0c000c2c400c816580e105010070300030f040c410000c5800b1543ea41d640341c0c4154034840f801c2c2c45075000703039441180d102e2808d461542811441c40c900020491007250300700201030418680c241d00314034405c4540d400c4601c02c80f0f480003280190b480119418001d050054146d000b58102c40c03a4002050740031070743c000c80d03903042c000001d4902c02d401d07518400440d44605030b02d0070035001c01c034240516107006030075030740310f6003c1a0aa10f0039481040500f038407035159003205907403001c0000a0b0410f9801111040c1480380000c403400c0c004103c850079921030304040c00002c8820b014020104d94214800d90340071000308038802c07002005c459040c0080082c80d103d00d1302d450040c20041d007411480740c05101803102240810005070380c4408101000c5e9801303440014240c440e800810016542a40700400e600e40391880344007907002c02c20001104c5107099070180a5a030706c5e00c00b4080c14802c00e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 566511906 1250 566510656 566510671
    0xf091226070926030f040603060e07020d082d0411030a030503130c150f1205060a030609060f09030305060a080708030304080f0705030f1309021207030f0213030b010f05010206 77
    0x11240140030f0b02d0311454074940c0c90036240168440d07064101c008541140e101010400705880000f40c1001159098001c040c02400315222190035440e20390380180d01c42d6021801401048071000000303100c181c90410303020340b046114016502c1280d18500c200c0c62070605407400d907507a00d201c1c45651907500e000103910f00115403695615085460385040e18506444c1c00c28202d40e46100d031000407a840c1c611000d1804079409550b900764a0016401e005000101910001a04141400204512a100c0c2c03100380b000c90341e1049000514900504000f0000d20345900240a810b0918040700203040c2d05400a40c0603480c1160300599a82d40c80549642e205494425059160418030008020510790000b9141100c0700c88412440d0549682d10305041d5403200440700d05500e00443d10b100060036980321840a8003000c1d000f141362a0102010b02110103004085900305515000c091a4540e46074050724588411203202400c1c1586a18104044610034010102051207101002985610028655014922 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 566513156 1250 566511906 566511917
    0x311040203131104060e13030915020a030509010915030b09160212091203040303050403150b1e03010f0f0608060c03042d080309030d1508100f09122607 67
    0x1e160b0786190010416485607a13115540d02c100252032484c50120a01c2030f461483c180e0000240c519001c0c081d02c070290896062002d07180032411100d0340006e0700600c020341605210751a40d01050048030810400e801c4042c0810f0801004070340250181c21162141c8004c071000030040ea200b988804131810b0180040c00140e00c650308006034400044014459458054007106c011802c04039141e02d103a02643c801c50029030b000a0800901411aa010003040c0c0e484106025601300140060783c40d84044a41d080c85800f50740e103110850f64250700a04240c8440302007404030004000307401c0000d0a8901c2a03c4d1076004000c00600b0020308003007207910440d40f00d4200580d10300741104125061204906c0320b42a90030f105d009401161500000e1403082c0302c00e5008590311090640f04809030740a4071600c088405030710b4010701103098041403680c081c2510b407900180d00c0c0c5c4600d415002520310707102e000d01040314954042c100a0f0784096034901c0500790300744c0c001e04c503240b0704d540412401c0d00b19004030002c1e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 566514406 1250 566513156 566513191
    0x6071b170a020f010b101d0603041a15010905222316050415050f03042d0c140402070213091a13150f0c0305010611030c060106030e03071b0311040203 66
    0x80c0a1009491401c4c0b40708580c1c150f00c00400c1c0440c03001d85c003da8007a032f074009100d5102d0304810350701000b1580c4400d982000c900e0100303410002030038000c0c080c05103602c60006208450712588004964040d0109181c1c014003e88121030080601240308500d00d00550750580300107200c4503504035030504c0c010030303590b12249050715110000003106c8880149400b000b40402c09490343c0c81e04813000d1401180141d0720a03d58210000a10408070754040c1501e20303020308058040b000c01c0884044c4000c0f50001d038131082d04144158002802403103000002903119034408070215103102954001c5401c24424005e0346148810070030640070f44102140d46081e100c201c2c440b8440001c5140c22110843c2400100c0802d00d40101c03090541910503895a00300001c0d82d900041010317a5101358440c0744a0340c400003552030214a800c280341c072400c0500401d818103444401c84800c10302d042045407401ca420003212007494a030201500341b018454401503e4000ca40001c015052a080c07084a004034101c004141c0c180 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 566515656 1250 566514406 566514439
    0x301080613020d0b01060801050a0504140c1e0712080f15010507240c030b01030902210307020306090102040e1b16061e0207021507020306071b170a020f010b 69
    0x400740814100e810118103c00e0390000341410381c01501034416600c407054030350304000510020300016400303284254100151040305d820600c0c15190415100740030240d80e480103021040e0f50190501d0741d0031620f000014090103010450440803040302150742e58220a4684104403031035080141c0d0150801c07100580420255070140c401030512611522007446030100320894008080a175540b03000110f6141c21411034020350510452941050900302040b01c807c0d07a80105104204851602007020030780160f03011454801c009440c1016401022600d50303107482d00400303010390000c1c0b04040001c403291000c1050342c1445000d1260180f002d200711401d1682401068010040540041d030f1406d50310041c00d045044844040f85070980b640d4000760342c522941c410f0080308250301c0c0c118207014130706114860043c3d60106c0c2c8150041110702e020501c88800380720307401d00c103440010300a0050624000c50440c4011001c060000c40c20140c090f00d03000001c800056080c2d420842066a004a960000320f800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 566516906 1250 566515656 566515681
    0x60a050102070e13110d05100b240d0209040504050a060510030213020a0309080d0b0102060f01050607030f1806081f15050a0c0b0f1015020304060503060d170d0c0503010806 76
    0xb460080f41e04ca07114450010110707160386c4609400391b0301c0380c000141048403800b01e40240301c10000c1c2903070b0000006e0040ea003030441c0c44c074019810702d5000360000355072011221181c040d202101d60080c420081030619282c041ea031807a84070411075000d8200800259000082510b0304120381d00039060000c260b140d070020700c00171f61040e80b20f1018942c2d0303401180c0c00300712140701034069000039880000e10a45110006454400020110030007051700c0801440642c55400c1551081075060030028103c42e04641d0548481c256031280e440304020f071050018640c1e61000c2e03100d00640021019600c0740c5c2125016a250154a02941b125880046d102c001c2540c4030f0401415042e520349885a110f4500b85d1b580c40b0295000d0b2603444c0d015280406120f0f8911f200c0862030018000c580402c0e0031840301d1500691207000e5481484103025004c03001580d02c0d01c1c1c0d05941d50700607502c40620007180361402824886034010742c80b00c0140c54a460f0710300030818000d80449058074042001446a80d5544080918 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 566518156 1250 566516906 566516941
    0xe070c11040f0e0706030c17061302070519050109030f0c0f0b0c09090408190c0f0f030e030a051e0f1f0e030307020601080c0d0218060303040b0c06060a050102070e 72
    0x9440c0c0d0380c1c400e500f0240024420500030306400d079804101c1b000c1c1d07100c2c003c101e01550700990382180e50010501105594862a1141070721066001603103d01d07079814453b0902e40d400a00c041e1201844902d5010450194841081c481c032a0308c46001940340c1000c122402c016072503000b808110303840c0b80300e0040b58150302c42e01d5101070f0700d9a00b0b42c5040722090200b014000203641c11181c00f100450441c0f4440302c8031110294aa201d40b8100c1d44116030307034950201224007420f0280404048010442c18144140c0c804841140043d04440007500c081c500707156a800a2034188003076100f0030743c003c030005d1400b0a1101e20245024010701d50394400440c44c0ea0500b2401c0f82491703a096980c011012000d1040c8061841002a030300507061170341c036289416040c10364285c900c80c4103203031160700c0f8001a5250100c034403040c0e44c002c8220300150383d00030110380b03144540e800c1705903c0c0d000070840c3c19017000000b51030361240c00140c41101501e661440160390b00c01c0c05001c1d601400600c0741c001401d100c42c0030301010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 566519406 1250 566518156 566518181
    0x30308060906041e1b020a0b0c0306060409060b07032010110c070f08060c0a050a03020c010b190612020a05030115030f14010603150b2208160e070c1104 67
    0x804846201c40c910101c40c40a010b04c860701c0d103420072940c00700140301240310441901d0000d04030307140c8a80d0f9441c04200008040c40f13104800440481c9480d00d5590680340a0456000e0401095868021400e00742d0080c020440000306a030810301210f80d421b40e0030400d8503000030000c0107060b0321605000098040007124820b0540280000c5420b035008200303081c0240b40403d00130301c8250400b0500b604040b0014100000f0320740401025074115805021940c0d4403890703203030040e05d50104500c2c450242040f0001c2951100c0c180d58a020b611400f40d882c07404550840d118040d4540b4003d0f642c40603805020001008140c00b4001040308844486155460101c14a40000c032024984103800884900305141e410310740a0500510116400d40300d00b04c006900c0c0c000100b4210308e014120315061182d12034a195803010f80b49060420f08084203200e000d400d102080d0740d40c1f51070030001c00c221300c03030b0500c03558944e484090086100383c0d00901c0809400c541000d20010514000401e02024050170350000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 566520656 1250 566519406 566519411
    0xd0204021e03060a0b03040c15020f060906160c0c0b090a09020c070e070c020a050609010210020c1b0109060c0206130806040f050c0f06070b041e0503040e0109020403030806090604 79
    0xc070700d914030000501e22204001c02120340c50703007015030a000802c581c940010140c040e0810501c00031842e13940d084411500c0c071101e985415020014200d0800340700c24209841032150b8401d101d034200c80070a205d80300c1c0c0c1300411542285080032000722225040700780040e0880c03440005c240302084040b8003c1014000182140c0360903035890724110101c1c0e100a06103040364115000a002d03030404030b04126040308452030005000c0c103a41d00055116a40d41c407a00b0310900c0b001404540301d074002d005880314041009001c5444590522845484480311407802800700d800806141a0358020755851302501c8881da160040e6580541c2401420780c07140040c0070050958650001d0003d0781042607038440c900c031302800d0341d0340340d40740c90001d1401003003451041c401c003071296500f082a01c0b008155409640c00c5002c8821540742c0741003900754054042c020b460b40311880b010940500000200030300460300e652056600c2aa80c809100049010b5800010005064100402c03050f1800c0b1807103940204004000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 566521906 1250 566520656 566520667
    0x19090302150a020c04090206090918030408010b0a05010801150c0809120a0215090105070219050306040c1701060f0306150b03070c1415060105031f03031101150f050d020402 76
    0x1d03101c0c001800c0d40d440000c0300040600565605010098503c0300c107031000d100c8030189030700040c3e2500861400e94051480b6000080001110389501e20804490718283d079504d6480f1460303035018101c1400c1e898058090003200040e6544201c0c80300c0d0484042418060350103504003800c03914680303462003c0d00d014209000f8110b040d9254909459204a01e13070052020a14a106004a0090209942c01d44c4130b002c0c0440c0c101079811000b12000d19038101e50840550b030441d10b01c0300600c09103422007074241c440e18082000300500fa1210a064400f60914140154120481c0391300f0784900d40141024000000000c01c00240c454020460501d00b0713901885240d1f4403025025083d42048412800107101c04c10300105001030104d0b5042c0611100c00941a0200e040c2000d0520308000703410241000030010000701809a5001c1103044441300c0001000140c1e40c4c2c1c103004002d0801c0d010050340d0395103411482d074104a04c3c4a5104100c3d01000c615495251901e020050301078200d0406a8004da0208030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 566523156 1250 566521906 566521909
    0x5030d020a0f020d020a122a1a13020f13020d1a010f080937030c12030504032c0319060c02070b030a09020d060c030e06100b19090302 59
    0x1420052030141d07210a0b40039000e8400910b01112000c4041c2503404c014055000f040a9070120108a18030f42403e801c0c0030300000355480c04606c940718014080402c00d403204108004941403105011101e10758043c0303600c405860b8800c00d135960384001c0d400108441d00b001c1034181000600b402642100c8014280080481207100b0f0f00e002690494004028260300e8800e036030440152003180880307240c01c581e0b5240c4184140d540d40f042c0c500c54810843c3c2c007040030301507201e560f595010041001c010720100350f00504d0054607554013010112208081c0340e9203629018031903c6614402c980513528203030070308103040ca605c1d40400000040c0700101058600c002d81d0b83c404100000d42032a41c204005a10030035070074003c084505c0c2d1000c113411508400010081041c503803080e0b80d00441340c4640001c8542c030300d10009603072143e000070081c0301c181010b880c0c04d882a01a071202c034590f40b1007015681595140c00c0800415643e901607070301155028407200c0001c07a4007141d8001c00589a00f030240107036880380c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 566524406 1250 566523156 566523161
    0x1081305010c030e060c1201090906020f0a05030703140411010f0e030f03091002010e030301090e01060302090c0304021306060f03050a060f0308071509021809010b120f011107050d0c05030d 83
    0x600392003c03a032500920013808204000e240d0f440103418000509160356a03400444003001841681080c40e100c5a00c0414400305904603009140c60b00b104680d100b899070b4000e07100e5002140d441012a2404c80c1702d149c408190110310303120b81d500030084014240da020040d030302001e0001d21031040100059008072651402c0000303420a8810000640d29114408200729889003d00e0419045904001c800c12408000100303403410340c0c07004030010034032603051f05a0324010900340d40080d505c00c0d005402d100d58060760b030009500460081d151002021100000301e0191121440b43c0030000c0e605258482180741b003540200d07040b120b401c0002c41d12994500409035134441c940c106664100c80025100b0401ca07100f8013000c41d0160402d028880c103450392700080c0140305401c2e01403c2010500c000110070340c8085d07100406c082c50041c00180481c4a004501d580c0300030803006078076250f01c2c140e030b8407a440320100c1c2a20040c65200c0c00801c1c0c0503c1c89501201d5408000d90100c845201c10701800b41c0884260 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 566525656 1250 566524406 566524421
    0x50402190c0c03061815020405030c101202030705031e0402060a110c0904050f0607030b061207110d020d030606020c0d060c050415030b0418030f081b04090608060c1303020108130501 80
    0x800205104c03031203424003560420540c86c0c06010a44100010490303900c011411007440f0b0003c4445d001218001c0c9001d5881ca4040b40003185414400020424107642100241d40101202c01015152005801c4a00b115074410758000c4c1d4400c009024545a1512442030309507003106110a0f00c1030440e4a4012408800090f541155150401e101c0001404070401495601c81c4041c038042c0038000d100c5001c104c0d03d1291110100d0204a100d00160119000d030000c1c0301c0c0c140c04141111038101044000a4459070301d0003407030300002d0074944001015440000c800300502e034020704200d003210640ea01c4600429003010700c1d20500074248000035230450240031380141051251408030304426031380100300c200c480c580f07910440810361008031004294481c0c02030700c0009950800700b0721a00d5200c0400700d540300080c11160402e0b800a008640241150000b80848088000301c804d42d80f60207241223000d000d503440b01d0744141c3d400001000550320640401d90413801c0d0748400036a003010f5441d62400c0d03e002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 566526906 1250 566525656 566525681
    0x40b040e06060301060801060e040b0d2414010b0918070314180a0209040309120f06200a050d0603060608060702060606030c0702040b0a080a1b050402190c0c0306 71
    0x109040000030086156194050022202d040c59507041c068098a40a0180240420442044084400794881e41d200c2203258000410107a41c003903040c9040b20014030004142d403d000c0d144405c5e208402d0312030082601c0101c0c400241d4102d41c0c00e20404004030f421142603070340e1144c0c10300080e400c52914121070b2405200165404180d80c80004810b60480d42c002d44591480591066260280280420702d000c1039a4126218481a19a4141103503020000d0b00000e2480100d41c9002c410021401482c0424511907001880300702c030040241c124810211310086000d5100308103110256115070300910b003c0350680c800041c110303129140c0c8400c5031503031381222826501c1081800b45841e0100b10156101c0c4c81100d5551440c50030214800c01d0740504e1000034051904c4006808456036152980c2018040401c11680e584030942410b0350004540e9850640c1c042a410010034942050700803904002c11085d1146000188150125036000d544101038482c1060901e01000046c1d0030b02500c484240c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 566528156 1250 566526906 566526929
    0x108101d0108070815060103020918160207080105070509061b0a0807020f040527030d09050715081b090316030506060103060f080a020f0117040b041211070e06031204 73
    0x1041000e5140c03c1c240d40000c422988025003100300c0c004040c10702e0b81e2042081c41c0c05a155011040402c40c000113015200c1c00c0d48820b802002090300c0303059403510700c5100d2942190714083e81d4609041c2221f40c04c0c0c0d00c200004504015901850600c600100b040c0385541c1202240c0c40001c54410b070601c0400c0e4001c80340ca410004d900307401e5142065000c0f00203c001c072810401414401981008c1d0100e0340250261905084210140f002061043c0c0310004501d00050160401c1490300c251501a54042e04c01e2100302400c00070081e511514119208046440050300c0c4490400341140b182d810003660300340d051145500ea10f200502c0421490020b51203400105041d00f400340c005030607207100340c01c1070501c52131000c002c01c0212000611358158540554003558400c1c407400049644960401c4c41c000d200070f00005020070030041d043c0c145e00c82d030f002d01d0b40400d444181581c11504641e1124840c523407513100d52001e00c07007060100c500d9500240d0007070440f2a03510512985540640060744801c06941 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 566529406 1250 566528156 566528159
    0x320060c0718140f01061b0b102909090604090206160605011205120702030106170f01050105011e0f1107080106150f090605090a050603040f05010b01020d0903020108101d01 76
    0x7142da000e0141080c00c0aa05880585450050410407050500c1100c0030000000868901d008198541000c802d400c03100415036890403162058a400a502c100c102c006030356680002010458071242004520100c40c02d8900a08d100820103c3c6e071010b4125940301d035443d8080b80060782c1d407800801c0c00301e0a0750b29803c443d0190342800c5c011070340140d00165200c240d80608000155002c5000300048000c0d032500e03616000715001103070047c09250800082000b0341004407008000010307406244000c4d040080c0540da0b211001102c0d030f0041b4113100b10310740c80c05c003161407102400f4000010161045150080040d404030b03050a190524540c03019107165500e0005110034210601a8206400141803030b00c0c0100c0e640600a040000350312815007008000300e520035296803025804002410000d0080b40c4909050400c00c910010440d011600780d07207000c001900c1d550011522a4020031a921803845581c0740d80c0066a02c0d0754011314179032003003501344404120b06400d070070f001c8800f200740c20344c60480b50b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 566530656 1250 566529406 566529449
    0x4060f0f0c17070e0d0303090c05061308010c050703080105270a0c080c090108070f0c0c0306141f0504021c0e0a031103030f0105130f060b0d060902040320060c07 71
    0x14103000e40150100031380030600041c1519080ca0300030700d4135414a00021a40e90368113003914140d40da9004194030010001d2a41c5c1340c03501e090202d074180c40440008100e070b07901c0310790240c41c50f115404000b030125000b03e0040145180002d100000c1c0c44422004034081040e03040f03038076001101183c0048240f0f6540f0250103500d070b8400071060340070380d00303545951800c00d0840000c5c203180401009502000181c100c0913402901c40e0030f010340c03074030743c00400300021030340700c0c5440000392028501d01c4820b15808000101d080843d5036070410311a43c1020008001c0b8140000d2101030b5200542d20144094100c107070850b040031078440c1040700580c11010305a95140f92500510f5405603aa0319215540148140491043c450001c4c6044400c2104c501c00c5400040314610042c2c45082c42400f01d0381d141c0200004c0d07484845004040c2d150924604000300b03912010140d080b8083d500024001c0c2d144007450f0080003541889000d00440018010350500021001c50303032400c8420b40110350030b06103800e0010802c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 566531906 1250 566530656 566530697
    0xb0c0d0605090606090907140d0203071407030f111204030803013209070e0d0b0604050a060f090c1106010603060302030c04091a060604091d0f030405060304060f0f0c 73
    0x40c203000c40b11440702d400d040c00020500d000315550b80d8818808400824440b80c000d141c2d000e00c00c00e15613079140c1ca031501014a10700a4004a81c00c3e80802d0005120182d2018070208a4030b80760b5140c0c4a002440c80107080c100d601124104841c00708e48207146100302c1e669542c10141004621420820781d0b00d40c14406c0c2d070343c03500a1012100d5070701440d0380b8011340c807a103400e900f420390728000382d4861003141e582400442d0741d81030031200c06801c840414680400e100c1079108891080406560900a03921030701881c1c01142c9080c45040c141906180080c414201e0680110800701e0f02488c00f609051038001e4028141442a880080400d594400410841c00e0034041149480400c881c104032001c003d41310309500300001e014610007040e11780b0008a069031603506580141c080754404015420303035450203040107403510305241100e00c1380c404600316504000085605541c0046c200c981180c4955603518081c0602905c11034800b511400302064040c20740c400d08080410660350301c0c03002c0700d42108503010b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 566533156 1250 566531906 566531909
    0xf0302040f050408070f0804030b0a02030601180602030d0b131b020601060302070f030f11030309071716050111030f03242d01270f06020312070e0103090b0c0d06 71
    0x4007504240410010401002c262100c5641000386142d80103401d14001410380714940000b46241c003c1002d11400c004140e000c0e511803c030a0701c841e2000000b01c0980c01c080515841140010f078810444076103d07601d07980020318443c001520200300e110300340c010241560204c0f6100700140e400c2071021080b4a60400800d401400c160608610300422601d414840e1406001c02130213000340c150203a100349110303500c1e0001d80c100450680e07403241005e41549840d509544200b902548a2840703082c1603107004215080c0e41048003046055441c41c1038010754810241440e000000d00050018101c5030150300c0c001c3d0301c078541c560344250904c4410341b0710000e41d290f404001e034001c40e40e01c0e0001d403031102178441003501c11031a6208510785041c102e004a403081d107888240408c0000050505021f0189600f050050b6224810401681501c0d580200d030359008181111201488460101d0304450240048213a0040107140201c0c00c00020f48803024191010398800f8a800d00c00030744203400c103806219020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 566534406 1250 566533156 566533181
    0x240020a080117150c070f061d1219021f050f150a052103120105030f150c0d09051b010e0301020906090f040209030a1203060e0403020618070b040f030204 68
    0x680f0f6401122241da680020714081c1e201898100c0459001401a401d0741c00540d8040c43d24017540b4081d15012014001c4c0000070010030503000c0c42081c25860100c0e807092031161000d10b03141030500c80200c01d6989130101c4a0101540940c0b00c2d0220441c0c0320740701c48042c0240c902004074490601c404201c54220000f00280124411000904119501c05003110704a4070115810704401e408903506050000f880304030311802d848002142c02c5d003006a415004c4c1201c10450940d0328140c1c500012686a03102e400c540c0d181c1c141c00c03030b00203000c1880d00b00107000c0d1040c8081000603004c90a507201458484c10012600203100c1888070303d40a0340e845044040d0b80c041c141c0003942014000008900c081c02801c00c168450145410b803c1042e85659056541c040c4009084910340e10340380c1010001080040307800c60010b402c01034080703141c4100740341e041c0c01568903a00030310700703580c0d00b45402c0b1454040c8100d44a440c05010701c0003621032403d20240024000082452801038030314070420003160a03280c15007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 566535656 1250 566534406 566534429
    0x90815040519030818030d02120a060501030e120a0e1305160519050304110604030b0a0f050106080c07021906020c03071d130812190e0a0240020a0801 66
    0x1c00042d600207075145d0049554500001c030840702614590940c05117800c900b05c1a88003280741c401c00c01017501058010525882e080251907104e07030044040d596a0350b011400e984c0308041075100000c000005003402c51061900b6020f5004810000d4044002c950541c40d140b034a40003404680004005460000017042c10b065180100500205c1d000c0c8001f0702c07600c0c0c180038000c0002030a022140098110f40301005052380c0d0f68176202d10f0464000041580c110314000e1600e012204007098174030078541a00d940f80c890340d5466658444c140600c1e807248800302e07048420b442941c0e131103051341c0000d44042c1509030050414500a00280b618125803a409074404d0420181e00380720b11a030503c49a03811200c0d2034110239000d0003a003405007a510031910f0b00b11512080c00200078079084c4401c0418202e200d0400140540343c0c5080d0855078030a00d06802075071003d020b0703403e44100038400c01c103124283d901608122900c018a00c110300941101295800030640000703828000c1e81e03114100f24003400620012 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 566536906 1250 566535656 566535703
    0x5060d09151413050c0904051e0f06040b0a02090a030b060f010203040f060f05070b0901051603020309070501030e10021902150108030901030504030324140102070501080a09030908150405 82
    0xb200b0a05003e003003c41c03800021000d000602000f44588031341c8040c003400000d074606062401559500300940c40c903455606c2005684051003021440001141e6070f000100b049480e40d45440450001c05895407040a0382044002c4203500c82c4526100110300a02c8407143c103281801c10710040c403800c41341d1241103420810091010329809503010303042d1156864446251000314500b680c1502c10440701422900c004001c101c228001500704a224105144103224127951543c41039044c0d0105031103100c0d15400c000414000e95100341d2062046420342d108031401c0d64a0380301c0041c203d0348004000b038490410b90840068198040108400c03041060a4001403580340802c2640c5038001d03141554109521a808181898480d0f0010300d04a009000c0c81c03038120041a00104113080113104042e481d05070300801860960002c207804048a0b0180c40360385041e03403129408001032a0140e02141841440c080109071840e0421003000110a012000d04482c141400c1482c544100901600c0e14414070244 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 566538156 1250 566536906 566536931
    0x501080d05040308180409020d0f031b08120a18050312060a05100804020409060606020a0b010b090f010e030f011401182705010b060a05120606090a030803040c05060d0915 75
    0x1145d1100710601400b0000444150006010303000b28040650b12400790f000510a0003040440c4601591194480c9409804104803202c2a40e4000300003402681d01400b02840c40180350044507440007500000080b030401004e04039904203030f101d034151000c3d4808074401290b800c0000c03032a40c01c46411a103950035586450000340102480315450405c111100010508640b141d40100c08240d522400a00210f500c03548000d55401900400352480c0000390700008020200328200e0303820240291081411260072801174130b014100030083c54141c807130300704865440c010a110307000060000f1a40900310b545021905003280e000c0000600c4021329040a0122024800d0421040c0700c582e82890440403d0900309540101945000300b50072203000154504030326802030040201c0c2d80e50440c0c4503115250501800140c0c0070b00c1c0c044540001036083d080c40400c52580c007659005115810120383e6a40701c50118a55400501040c405591148442e8041101c48010082c04010b000400c0110300048407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 566539406 1250 566538156 566538173
    0x10e070806131403190e0f0114130305010c0f12050106090e040219090e07080f0a0609150e0a060e061504050601030e2b0c080a030b060c010f0501080d050403 69
    0x103003a0800c8071821281e00040003900d0803015040640902983d840e280c044c1e2920b6403484044170034000060017a0405021807500007014104e8240603540e01c0480c5440a080410b541e101c2000307402c07121080400080040c00c01d014a246041060f030703035803041031407262024010b20700741203490f04680d0810005006036a4401ea0190840d010601ca0042a49a5001080c044040000764403514101c0303030000b141e070201d01d070001c4240400f490100c90706e0941e42c0756401c0d1251003050741d0000b160084c2d5005404100c458208012850007000380441040c140240b010440303540e100880d0890304400c141000f4883c01e03100e10100103c4000181805180448000d1044441c255005202c0c580d07403c0480c440b40d11a03804002182d003c44200d03040300030088004410044680602c0d0009041000c4100c822446038a0901803035034040ea0356030600b4103440301076018200001c1d07100c0c2c00100c10b101c0d5081c004401d000d080c0c60343c24032000026041d4109a800b03030614200320342d800706208007000108001244503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 566540656 1250 566539406 566539411
    0x50307060e09060105090424080d0915200a030f03050c0910121112070c0f11011716020d141803010b090c040602010f15060c020a081b0102010e070806 66
    0x122070282d060780e516001603480d402454942c40d0801d10f00000196a00040006403480c0300f1118030706503070956104e00941c0d840803000032600004102950030400e00355403003504071100754181400440b0f0510440aa0109038010402e85401d034000c060718420706d60040703000c80c1d1303210552806000f1031801c00e2046240380300d0280b456014030100c0920b2400944a50036841801c2c80800701400311411880280d0b00d544c111401c1106401d034180e01007107000f03004680400545a00c00050f500390205c41e02c1c0c190b981281800740505112810550031601c020800c005485200c0c0c0e0780013201d0020354400000d20302242d0300d80800074001810700c0b1851600070181a1803407490301d207038421761400c694000701c1d01403d0300360025038100c0351705001d00c0115441c030400b400503603410790b008100e10608034000d541a07070307003108150000303004401c800c0c4480f6125449501a0300e0014069034031055440080e5403900d44480c2c44503800c8600c44a80a801d0769080c043e0001c0941c0303c0c0000d22416003808600394803500003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 566541906 1250 566540656 566540659
    0x106060801050d0309030506070e010e0301020909010b0304050102070803180c010c211b03091d040f080703020c180a110c1b0102070b04080705090106170606031e040f0c050307060e 79
    0xf400c010b501018400d0100c41d02841d0701c0b03402e961403401c1c621000b03801c9141d4005118003203401c8030041841400d051007550515000180444e0b000c0c3d191202d0500c050b88081e00a5455540030000d19011031450001140100e0420500405c101003140c1c4880c188203003261540c0c1003183c0c0303842c1c40c1c5c081008900f0071060300a000e9803c10514251510030b6030060710000070103408048084091051542044004080301c038079601d02c2c415410007030854102034a00311001400c030248801100c0c04111070402034107c0911a0046440d6280c1102c001111640004540388800d13001d8420800044494040c503e10391001c01d65079400c0010451206403610b071030540d5001d201041d611920707070681c800c026600007040340d00d00071983d90740c54401203511101103029441c0a02200781c00041e08602c1070f0a400d10a2020b903009100c0d40d01d8840c100141ca6101502130180155108a85a101e0f82420b4209008602c01c2c2c146261545c42071070511211400b5038042c501c6604420303010845603420442d0320844120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 566543156 1250 566541906 566541919
    0x3090d020112020c010603120207060f0507030c0c030503070b1510050d0c090527010501050315190b1c0e0a0b0f07120f02090103050127110712020607030e010606080105 74
    0x510312800030080c0644869403131a0b44c2008800014490890302140c041021a82076411442c0c4503e029074001c0c000040440024408000941c00b09106110040c0c0c858842c0724200c8055507a0341325a480c0d40c22450044d0b03840310180e4140807885814012007195060103840901d0444103000c80a01280200f40c5610744507501c0d042902c0f9000d1203070b810074011309001408080740c049904244030031100040c40c080c0829006a00204040d8014410307a4429038078100c0103c4502109014880f988024001114007880162008160510341d2001741114084c03000c11084002c001c021450240c502c448000d0401360486092a004a032148130141ea01045415102203641c40320f001c1212410310b0341140541c00d274903080d5144010780240d001006202c40981e020b210503600c40b142840075022154045079400301121001c0c40030707003158002c00e031305401500d071490414640340c0340c0b4003004415454950060b045041004002a01403094840c4d0248040c002c000345800e0a00142c000c0c603040c02094801d58 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 566544406 1250 566543156 566543177
    0x6180614010914150a0c0b060414010510090806090a0317010e28090b1509010806180c1206061e0d02010c050a3c0804051504080a08120903090d0201 65
    0x45a12103540044c0080b020482d5850301400402019180d22401c100e9800c078042020522900d003e0040d5039104513400e0403105140d10700030030800d429074040b500d8400d201100e200054442800e0001034400c51000300900b00418880ca401403005c003101d50302015480083c0c005001d4401083d008940c0504920341d058204400000c881058044582c1114442c90503e070070002085074003203810b80568a02c0d140820040d803042c040101c0e0480902940701c0541c03040002540038840308400b191800700c0303802641c51048240c0701088140d400a00c4116081d80110701348010760401d2540b0061107c10151051380382d82002c0300140341000301050182c104008541c0d280280002032005001da07640c0403201100d070030b0380755610740070425500c2001041909000b903002c80317004403003001c10b804070f621000c03541c070b0300c5c0c14482007003203810302c032045d00e2040c04081c400854001c07404c1040803200c034003409016445400451070000b010000a08070035480e0414002408035448410450b426207030309007404007644 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 566545656 1250 566544406 566544409
    0x3052d04050105220f05040612200d0b0a020304170a02030418180506060906030313051203070c080309030c0f0303190302190302041404151802070606180614010914 72
    0x740f201d0300506016020130784000441d442642003250450300d05440c1401400d0b41c49090280703113030003441c025090480070014032190015100000c3c28000008052060f0303610b0540321040000d20444200100300da000050005120344000424030020254940a1030200b40180c000d460f40518400d031005240744655071040d00903207400030203101e1101c03560f0804914080c10402e07a203950079607959005800b080c1c0416043d041c0402140d03e1a951904501f40140c90074061096003901d2029800c118042070042c03600180000009000038403071a802152a80402020182004a42010207200b8190703042c410000c2d0318003005a401c0c0c4068035415030380c440085001a07000c5d102e041c00d0801036a6100118042580e015400703801610141a00c50348200c3c002000c0c48106c44200a0440900708201004c0005904031407641c40004401c80780542400c86584e10501991140d801c601003070646032501c80e03603c0809101c0c20f0020080004882004200d02c2c00181030110140500c0a03075001c10070065415 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 566546762 1106 566545656 566545687
    0x1d03120403081305040504230d1d043c09050a1713090c0f0c0309051002010e1009020910050f060306030109050a03052d04050105 57
    0x3031a04584981050b6080441e200e881d0401c0300c0004222519140035843c001d91241035020807d076100c032840182082c0300c40451010713a10103000c04c51000c1d4801c0e5000060000d407801c1440541b88800030030003414140d01200107441184200703041203050071f003407280500440000907005840d000000c8040d02c1105202030030561108251101041590014443c400c041580192400000c1402d0642d10b0340581e0002c03540581d41c242d01544136810810600785101d003450a03201001d02550084e0040d021405003d00544000c0405100e01d03000751700070610348800b035003198071000a0700000000340ca00b1200c1240074114003404204400f1800e082141502c01c0103002810b29041c24091090030340006007103a0b030540d05e070300c924400700c0d200f406001821402179440d030340e4079803500248000000c1490008580d9200c0103070100c070100c5a20058070143d48003440c04e00d0380d41c40003402c060361 = true := by decide +kernel

theorem cover : BRFrame.Cov 566366906 566546762 := by
  have h0 := BRFrame.cov_init 566366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 566366906 ≤ n) (h2 : n < 566546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
