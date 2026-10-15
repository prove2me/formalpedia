-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4241
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:59:01.054683+00:00
-- url     : https://prove2.me/submissions/0f65d7e3-ef35-48bc-8ef6-5ea570512896

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 762589928 ≤ n < 762769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 762591178 1250 762589928 762589931
    0x220f02041508060f0f04020405301501060c1a0408090109080c0609040b0a090c0c0c05010f091701022a0c06070f0807240603030f0212030115020f060709030308060a1503 74
    0x51714041d070f440da81190000d0001401506100c03800d111980c40da8001a001c0a12031a904401260130300360208286150000c06251341005d0390030040c040390105499001140c0781e010400909050102c0c2e80e003502d01c2144a218104c0c0d5402c000780c001801200541d101290303d07804040203403c5982c88006680044074140c4002540140c40e1000a0311502d039503002498142c070701440380100350760041d0940882e90085c03481840f00e50740d0340300446041941c2c002c00800550a05e01c180304086074100c030501d1030300f003d40001d4140034010181485207038a83d20040c1c02c207900c3c1d01c04500440810b0050041013041101d560b4108021902d80550845180500401c100400034075601003024001c500c596040220720000c3c0258071a000c010300a200a01090713003c958804201c0d02040c0c40020280b044803a100ba2032800c59180081000d4a00c00749a211310540c0a140843d41290714108035140c4112010750351110501e1840c1805170031441d010380300c64018568028140103401c0844844054401d59180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 762592428 1250 762591178 762591199
    0xa09120c06030c0504080618250905060a031e14030c060f070206041511041223010203130b25050a030509010c080103080306010c060c020c0306060a080606220f02041508060f 76
    0x1d40500f007402d0009180c250b02e0270380c0d0340740307501c05020f02c0c1380415686802404c003e00d80350b010800c1903003e010b200003404030021500d03220301025180b44642d6107a00c200d20305442c0c070200c0302403d03040d60403000e207000141d8403500811402c02c2505001e15003061840c00602490b080c10744030b40450140c107207071480c203160b200c1040c801510a508222801824040c00005000109161440c51554003078235402500c0130458030200c0d038403810720850b40184004892604001c03080c3d0b0750b10020000007015000706c1c880300d42868092890602c0c0d810942016a5601940d074000303101e006d4220340010b482d0300c0082e0325010011120507000382d1064103480d0401e10b40c9460303036203100c0121801c0310340060040c04070741804104040c403900020903611829003101035441981c0d584060109802007071040f01c450354084408182d0381e05158024591018421303800c0701c20720711040d6080302a14032281007a980745a0000f003c015804009010701500440da00e020b4909060440028028140619016100e81203004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 762593678 1250 762592428 762592471
    0x13030905090919030212030a06030b071d0f010e04020703020303040b0108150c032a0d060b0325020f0d02060412030203040b061002010f06030b0406051b040b0a09120c06030c05040806 80
    0x680510000d1126146d0703900d24000400c0e0029020030300c002c940d1006008007040444e4000c40e415940030252031750080608404104003d0181e05004146040c00982c3c04c407048551103600040c00180d01070380086940c1d04003131900c0415403505900242d86600b104c0d640030b6031710b1804002d03103030031418041400f44c50340c55044801c50465040752580d180007903561980041e05141c4005016507411449042201541d10246002b0502c01140c540007496a191001c400400c0240340401c0071129600c1221a107034860b00741c01e441c00010503140809688000304000c1000340f4411913062101091800303609504161341c40380ba14903000b4184c28883c0e0780b655071060b2100c0c07003503210000c1441204810300002c0e640381417030303c107141090f1819076841c2d00705000500210440460070b001c1d0100c0700c450300c0c40c06141141482654010001503010808004030012703c0c505001e211507282800b4482000380765150441c00f50482c2e144120307450a203c414030040025840110310a0352002c40c0c2541d010b0040c0a08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 762594928 1250 762593678 762593683
    0x40b090a0f200303070f1e241d2109060306120c031014072105060a0b0a0e0f040b010207170109050f0a0c0f03020f061e03130309050909190302 63
    0x840b401d90948804078070700b810322012505101140d4043c500115a035030071440300394000400408043c1a42d81c055415455603800301051807250f00c0202000201c08041c40011481081c0c442180501c5070b10400201c1030034407400352050202400c000000d8600150780c008034004d0300008004610900c0360110b44040718109001c1e199081e04000c0640d610540d003408040300811061a08250305003400300090f1082c0d0003240a968500d01c580d1440718105150015003029000c010131898000c604234400060070340b00e220142820040301d0709c2d00403807910001c0c00e100c44000f410840c14407031420322040d8122a600810400f01761001d046500d805034006514039030140c0003090300100b0340e00c184c0021500612021400c40c140c41c0c481c1d428904e61650311080323000d202d000b42c0800381d80101400300004207464010024000c039182c40b1600c141c103c0a00c484100983c000711003d070f54038114142d402c0c04040d840f03104038002e410102c5944405052a004082da580c003108140e680c5146005102410305008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 762596178 1250 762594928 762594983
    0x130312051c0e07080d020703060e070f15020c0301021206030c1e040c03180b0714040303080703020c0c030a060b011407050c060702060d24080c030a030324030b040b090a0f 75
    0x10b10031170340b0b184403510009580302164803041d51890b00d82500e08202c01404110103044817041c49034030000c0c600703080c1010810000c5060300002d51045000d000e01c2c40c2c0b020300240694220307420701c1100d1864080180b504002031104054880c00403480410103140005102c90044001a0790002c1c08031007044060300104910300884141c000303012800010480008441c6124186940e981c0342c0c52104200031030307501d02450100801244440b00020700051280d80030f8880c243c100c10490f81e5104185011030b051002030074042d10340c01c0d100c595149032560410459140e041c9001c4c0b15501d031030000e40740d170341e2604000700c00a4481d00c0300141c2c071402e41d0340c0e8105507602c2e0b6603040020450f05070044044030f801301c00d40900711000c040c0110000360050021444400d41d46d000360140c242e001440d85d00302e00920000640701c160300307545588002551140203080c4080c61007030032409468107003800c0c1035103042c10042608ac2107a010f43d81410006144074441a0019405540b01c4c40c1c0760b8200b00c500c42c1a000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 762597428 1250 762596178 762596189
    0x31d0103141501031d07061419080a150602030d050a022206020d081e060105040b16060e0313061d100804060b1002150405070b130312051c0e07 63
    0x2001e200340310744841041000100c08100340c808000c4190700300041c0c0c40000a8001068044d0000d036420005140a014890141f500c544405480c01b806150307003440c0035001ca00d020b80007880240030058001118403990101d000d490f40d84403110b600d002d600940e28483e10780d1a081003038403140459202030803034068600d034540c0c0142d40c001d08040340f400c016840089108050052107107001040f20b203030107607004a0150150142c1d5225950354086070448405e03001c3c0c000c0e070401c0f0301008009445007452021302802d120f8800101c20290a505010041c1c0394110b250801940040215805000007007554408958081c00d11480c40980d1050706501100002806034200c444120706c1000030754072a200320301c56403103030b20300f00895010b8006008a40100342c0c94240564014038100b101c0c100c0050400b0341c000c0c4030301c01b04c500141d141d209030002c13a00a29100032050a040d0f03000d00c10416001d144010101084c5020b600303000d000c0d41c00022000c064250b80010650395106440c211700107000f010090f00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 762598678 1250 762597428 762597461
    0x18021c0905061f03080405060306010c120e1f080105011107030b01032f03192916050315100509091819230f0601061e0c031d0103 57
    0x9450741411a21070000b00c901103181035000c00c11440704495100c4902c1584c0d048980c0904150a000501c60035a2016244c2410300a0300200400018a40c50946200c40302564a00c1e02c0ca160702c9047c000390203035440031907810481c10304c0da20f0b48856218035000e044032402d18200f0090b5224a03200380c1400480c0d0009842802034000100500240ca4580b012080440d425400034001810044402e034245051159050300000a440c201c0c25200300071401a5010b000a80401c800d00600d2142c141142920070b10710104003401c1010b1440356031009401c02e507050034101d28518040f6101c44601040621048c443d09042d0306001c521407061055404c0d08001505ca45070394205818803044007124034400e80c2d0540b01d2680038031102c1c03201010902180364000030040200003ca040095064001030b032490062062242d10242140200075540c020086505c403042d11021491201d00c000c0c244030099001d020140041ca00000c3d03200c2c200301c40108892000010b00200400101c2c058000d4211420410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 762599928 1250 762598678 762598691
    0x81306080105010e1207090507030605061207030e07030308280c0c110f060d0914030a11010b011d09180a0c080607030b0114160f11040507020718021c 66
    0x150885021410b0b54002d072900300740078940401700300c0c2051030444241d40b5038005410400070402c0a070809034000059080210b00c060300d030004116035802606000300b101500c8010b2002d840c1d0107203d02079040302d0100140c1720390341c25600c0160086c84040e003041c00043c0405880c28400d030322258036068040035680c2c14055a40c1c01c0d0002000c55104000c280c1e0644002441d0013407030319115803420300030340c1c01415840c1071031020185440100340210060b205001d41040c1403070300c0b00c014001840381d602c590301c0e1029045c200703d00341c03401c407800c0c07404c4981404034004425005014850010700f038907404880303840c4155100d8120461101503000c0c5610b10740b068138115410480580c80d40c105440b4060304881041c0d0310341c40100c0c1a110820101c901190070003010340303d0701204500a1030403442c0d4411425a45400c4d07602c4851503000302c0030946181d040b0341c1100322036207014005d264200343c4602c01045a0380c14201201c4d115808402070b207001c25070003e01060458503100840614040500007003049 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 762601178 1250 762599928 762599939
    0x309040c020a02310216050f070e090a0f120908120406080f010e0117011e060510020601230103060b07030216301a0412020f010207050c0d0813 63
    0xb1581019000c03442880701e034079030451500c41210024080c0180b8051000e080038038410f2203000303522100c80c043c908010700b540c041c04954104001d0580c000b607000203140e003614240340304403680340140440d0055007114480c01d0204042c8811400b031190011108900c100d50000251801c80c0c0c00c3e4000000c50007100b0b603d002000142004d801101d00503100c0d00b406541d00207002182c200240505106500080300600250050103000242510346000000310b000d00345d4001e080090080011076071464440006011504150f2560007554400713000400180d414492030058000300c12a40320300900507041e12250b1a8801c0d0460401003506e08081e598030111414002c0d15082210303400b4110124201001940440344a10074048100e0030300c080c1c2e04e000d002c03e5202c40e01c200412050f02c0720044023403a00c18004444a005008e144900000c60403a4040c10001c2c0c140000005081e045920500000001c50710209894004203021142201540c5a07807500c01c100e0701030161902007104109401054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 762602428 1250 762601178 762601183
    0x60c0b0c1308061504060302030601031b09060f0f090b010c0b130c091406010f08011203030209190e010602030405210f03031f05121b210715090b030c07050309040c02 73
    0x6685050344c4248280a400103100030360f207581c4030094066006000401c003044800c550414556100241d40c180c1e155119040400e4400c80d8101504060051200308003104404c01c0d41d00040001c07060a0240d140b0440010b4416400140064507007245440000c29a02c0b280f0085c0c010260711071966000c0340d8840b0781d100010221802039112a035094404101030350700892013504081000c0e5141e0030b2030303800c108000c191188842d4040302416003d003c0c0ca48140c0e201403080300141d081d00008101c56280c035440340b06502040c2e000109640042000340310a444030200b4403038007000c404c0440038020320728000768a4180400d8902409000100c00d001d008102d070540f103000100007500b40c41403581c5030000c00440c00b15001100d80c05030301035a03400603280d8491030300950f030803001015586c11141e0841094a040300e4070070b5800d510340101d00d00f4040400b07801c0386c0c50803802e4135160141e4458240070070101c941c030014211101403007000c10b01204001302042190380101020740103000b0b07882861406523 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 762603678 1250 762602428 762602431
    0x611100903140426031e070305071a040312053309040305030f0618150f27100f030212030405130c12091e0201050d06081e0106060c0b0c130806 63
    0x20101c00c00c85086500940000250340c2060798074045014a0031000b141b5a0861740044000c4040c0003080c0035800103d16807001081c111200d00d600050070703141514000709440190404050505d1900b010701510a009410540520503200710440320780c2410031072002030012207415950f001000c01c04020030160b00030080c6024101d503648400450700ca10007000401a104904503203107c6031103001451101c0b540c0340c4400c0150005e0505a11040f0000104000c2c03190035554603644201c460440350700080401200d50302c1641c004050301c086050a900384082c102600c80a0700c04d0885001540001e00c00780100c034000c3c10004c2c0a80302c503c5c100010140501603121140707001c2900a400381c8860b0040303000d10701c0056409010559900106218034070440465034040e03040003401e211400745d1410034442e00001e04404c600810203800290010300302802030301405c0790240d0402c0c0f0108044e5400c1809a101143d104041c0c80c41d658840441c00301d14010445640c1000c100d0742030024102030302103500d9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 762604928 1250 762603678 762603719
    0x90b0c0d0f0203040e0606030a0209030601081606091214030d0f0606112e0605041103011505040f0614071a010e28110c0f0106050a06111009031404 65
    0x384240041e0041c140c1c0c480c00340c1d00c68030140c01c11040c0010198680700740215072101c1826401814a5041030200e4039040003604850700586c042141490040a041c141c000200042d150010708581807884415041c0f1410400038642480f07050045102e520034010341d522030044480811046030010929006090311f4410000460f40c5241c0d04030020304c02165015600d030008107403652a503010400c6030501c4202c1a400c3e84103955426001c1496a1140258004840324000c141c1c0c481d4141a0980201d81c040c00c0d00300180032003080100050008045442c1c1201c8803818500ca03003541403010420f651044440c02004080c00a0130301c1c07550012400c101c1d041c0e03203101c4440340c00c40d40d0394040915075980a400001c1c2d400400000a144258a90001c80d1090000c805060402e8009260f1a00d04003100d55081c0c0107035104c01e02802182041041c1c00002c040c336103802c090600d20360f12243d4490031040042c070541a126000a41414091003207901d0180c0c0b0180030350f94030399070b8000f032400c0034003100c1c1c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 762606178 1250 762604928 762604937
    0x30703170403170901020613050c060a09090609020910050a0c08030901090507050a0b091c0212060108060601080f06090709030b010f0603110a020c09070905040504060504051c1e090b0c0d 82
    0xc0f060035410502510560381d03040e001400742c0c1e290040d0703003140d41c494900111094441c40c144c0c0f4180e03440d000040c054404043e02c131103c80070700b066520b070141c4459400010542e4814800c0074482e03601c01c426110103280a003031107030b0780700545101101d064850080203411014004140044030805602001d43c0328003800607242c1103a210382c10081a40c0c514800c04040a10911040610740f40c036111030a0122480f12002414403940c1e80403c10001030440d0502503500524010801c00c207081c0310140d4409800d00e8440b0062811406810506c2030103040d160181d200200005c03585801100312801540d00060181340b590303924103490a65480324001c01001905151030f545071440c0c0082030701c0c01260750781c0140680304903070410300182c0540100b6100410605100c00100740d2984d100d058042c0d03008410104a501c2c050500a18080d1050461808500e1b1901607a01b004c0d40f00c05136600c0b4000c00c14011864101031841114035038010b8101c0391440d2000185140008070002d00d95040781c607541c66 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 762607428 1250 762606178 762606203
    0x18080606030303040f0f120e010e100f03021305100c02031203100e0406200c070e010503030a0f051b060103061815050a1e0905070b03010b123c0108030c0c040b030703170403 76
    0x2030084d9035400340481000318010381e2039040c0237402a00a0071000c034040603100400d5903500300151840d10041400d0010690b06514002942810f0040000c0d2000c20604549542016032104409400c01d01c18040c4540c03401c0081010405560412507022004036480c2d5100c07115400940f40c2030748490110300e69845540800035107060b4450065040303e000402550901407800001d0b195070701a001000200300d010044980804c4503503c030781400d1340410004008943c114544403003200c1c00c4240f8898140c64402c0c080300003414005190000301d00c0a8070105840e142d0710729240140c030b28403014145801d404030500c519001d0540c815500c41d03000740215480716a981100c1c0200b0311003802800d620940070080c40141c404600705240d044070582858080b1501d20700d5140c0007a4840310700781c00d00450380c600704801102d82400039030b024000d02d00186103420f040c40d2940b9500d043e00c0403440c0c00f441d11380c4601c6c400b9035428000c1034011604890b20f4190310358050050000e990281c00101c8a0345d80440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 762608678 1250 762607428 762607457
    0x4050f041b270b070209041a010b0a0f0905220b04020708070b010501051c0507121b1806021b04021917070f0e092518080606030303040f0f120e01 64
    0x789104100d070011401a890f04e50366400744444150001d0042c1c42c414042c100c010605900222002d00910849140d640c840c60a40001080001400c0081d420440300a4045c089940c0303807008114035480c54800704034900b101e03c200c04090712021281c2c0e43d0261002c202002403090072002080501c0c480c1c3c0501565030388507001902c842c045d10921210800158189107520f40c1340c0d6008a4008041d800c00103060320b96002c0b00070640e0501c1100c0c042c00e06100c4a0109007030b03040134564a80c080a0480c4603151340c14000001d507980142034120f5000041342e0004103203070712a039046908040d84230844809001c44e00d90040c02405004010310f034045009400180060f01c246003511803c500c60b50362250792181d0004001c2403202c043d01400035000c0e02d0f60454481004007403c14850800b0351555000400c44c00e810b00700e8040c0c580c0c00840a6000002000003941d4048100d81d40640d01511071585e404031070407c148820f074003400040410f0b034480d41d220f050b1508800c0d500b9407032600740c0c3c03408032002071103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 762609928 1250 762608678 762608747
    0x120e0f0c011e140c0a0f080c1926190503012306030601050f0d0903090612060305060f0c070b010605040e0a020a1718160801150b04050f041b 62
    0x100d04030b0b0002d00500504080c00914000800800d1902c0c8115a02409280c8070070b804159040e00c02c98071490000b401035003640092150510541034450b4440b00748007a901c500c40d029074940e0180309503008207060180440040f07401d450b92241c030049001c1c840042481d001c0d020703034028041c01c0c0340c060840242d440d10325852001d203c01144041c0c025411602c07980010b4407140c125016050901c4000c0c0001800c0f44520b210300c6a00b1070003a41d44500445c80d05602802400c81150926501800c3c031100f44040744000812a82003000300749503400980d03a12210b940e1601a03a0401452120180000200380384c0c400080c3c402d44d40314540200450303c4c0d48010000301d01c1560410b802041d82078041c003980350a05518541e005050f410b03604c41a07001d005146061441c610310820902000b031006001202c82481040007100703003000b165080034100340d021103950140b4482d580c894040308603414142d45030341d0071510b2003501541f800c6950010300b00020303003070036002c20010321a41510001844c1c200ca91 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 762611178 1250 762609928 762609977
    0xb0706020c250303031505060c0706090b0a050414010e03071d0a090b07080601030605150d1401030c03330b010225090b030f06011205010605040501030b07120e0f0c01 73
    0x500c0031004082c034684e0260040e02882e95000d01070070b965000050251940c1000303144110b020005043c030785043ca50050911115604104480402403100e0524280c008048a0550701420a001040c040000040b40d030060040200c0750140030b9040002803d002c10381c0c0128a81d400000da00c83c95946017840c0004980d003e060103007140c8405800314503541e0103024425040241031501040071621072011800131584200401329002001075144041049403162864000002007040c50741d5145480c0c02f1401107150001030043e05001c0807074640b040b41550184c3c80300c2450b095009528010070f2800001782541050f850240c014003000308440850201e1408003800c401000911407405c180c26a0f0007071101c1c00c01590907116005074034130700c0c507800c00049000380181030b80c520015903240341850a4905039031155000ba401c1c80c0040c0300261090324042c0e4050b01e0303440c042c01d03021151241803010b40340912014126004001c2c54150070080440d10140018081c1c941c0c83c600000300c0c0151001411 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 762612428 1250 762611178 762611233
    0x10611030f0406050c0f032b090507180e16080c0907120e0a0c1514030603100e01090b0f0610050c0307080c03070c1e050315061002070b0706020c 64
    0x504000500203540540045c1610b56000d0003241c1e0034640000c41b0030b285034020740b0200c603044414921100700d00c1d50103501c11410190f07084240180246941d9090380ca14081c0110040040303070303007a0f00c0c0d034407503e5500910200b00350400716000c40107030f07601ca000d42641c14001c000450141e8440d5140300e042011070b1a0041200e1359070316009018080b00701c0012704100314039020390700078280d500300864001c10440f80036010000400050f0a40d203180a41040c150320002c400700c0005104015a90782e020603d403504525070140420b01007440e604403801000c4d08207000789005101c205110801c1000d4100c01d03c02c1ca03041e50406807000d14104213807028000d880511610394001c20007d400030780000098107101d60b0990440b8101a02580e41c01c1c06212190086403007450a81800c0c40e10400303135100c40e8011b00d0154082c00780c06256240f440541d030745c010702150107000e4101c200c000051017044041c0c000c0c02064505600c6100515001e8042d5004200400c640d01c00e07078159500c0c1101e9020340001540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 762613678 1250 762612428 762612457
    0x313141309111c050106180b0111100203060d0605270102180d080f0c010b03010609090201020a02010e36060f0a090f06052814060f090a0909050601061103 68
    0x900c1d4000c2003039400f001d01c3d15070551000c0c0030680e00056002d001d81009007124003410b0200da080d41c07990004450344c03081102d04000c060341c101648220041002109500c5820016a495135007001003000c407410108010a00d528200400c1a03140c0350b0f1030703c200000702d103041ca11840034402d541c0030700340d009081781c83c04224a51740003c0c80c83d25001c42d00f00c3c5000e110350b92990038120510740714840c5030040d003140300241c1d4490603425100d107801c1c8110741c003038414560200a00c010b0340c3c0000f59100070707010000741031181c2d0a94042665481040070703100d4a18842107800c501045141401500703d816005403075500160011801d18684207240302c40d00342003e404420303c1c601d403000000c06000e0307100d00f41c00c0259913544040350613200d40000c01e4a03000e40c00c04010451003220100032400c400c40d40164001121002c036130030203545880032070b050580d82e06001515503d5000014045c0e06c001c0c3c1c40b520f0500c5c038022403082000300119103a0f0407501a5298280454000342d003550b242e01c2600340f401c0c1c128 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 762614928 1250 762613678 762613703
    0x18120a03031a0303340b040b09010207120f030f0501140103060801140708040c0302030613120806031e0f010603030c020306070207050303070201120b0d150c2607020313141309 77
    0x415040d49106503442040040105c10704045c18050fa203511104015119a102c0b80f007044140500c41c03520981102000000310301c0d0100c01d0316109201e040b100d940742c1c1000a481440c8002d180700e600448010128400100610350355100c180851918480c556804a8148200003e400c0342c10f1240030101e002d601010000742c2d558480850740904014401c40e44161b55000c0403000d0788041045600c100b1a0307102d0008540524241100618000c000581c03c210a200411030113440206046020030140f105ca10103003400752740e140d802c200070361500e003400f0343c681b49002081c15400001206194002ea00341c0d051501c481c0412038032801c89000f09601548100440350040d4410001084a003405c2440003070589500400502c0010030741c2016a40b0304c10381d00003541100524880c2d8807076096113003000041c04010252001064020281410407521258005a441402401119884402c003203080144a444031503c04010503481c04071405100d02101580d807031340316132081982d0700e60018001d4421 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 762616178 1250 762614928 762614947
    0x2030d231306081f0b030106110a02030705060d09060e010219052b0204030f0605040c0626070e03030415170106051c0f09050321060105030103030518120a03031a0303 73
    0x5482c000f5054401e2901303041080c10411140310101c0e0702421011070301a0b601e526188004254051865120f01d0503088200d24000580e80040e400f01216070948900307441d00c03800320800300100f041703e0015041d01d0401418910446042d0300802c110f8000c040701c400b000315078101c1110603000b442510680310101040007035000a1400c54001c2da0101c0c0e520151900351030f542c03260726941c58440204c82e080d40b20003c0c00b0800c45010b080c0006440b40340380c4580c01c5034a00b040410080f04488401c51408447c0e0041000c1030701c11210582007182c05000c4903030f110f5940c0d41d8150100300d408a0a40003504012001051a01403ca8076040b6801c6603141821710b01900704400c00241108800c4c1070040c0d441c1521840094180142c070303d800c0c0a0800347d41c46101e40103e4500c6040d05495105c41818100c0401025a8101e000d4a041d690180740c0991510305aa80b0014224400c4a603560322480031804207d0601c3c00058011410744240d90038451400c82d01c445104400a0300c01d100e515030020b0140d17915 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 762617428 1250 762616178 762616187
    0x1012020d090b0f041e020415150905031b061b1203010306240306152105060901020c03070308040f02130f0b0f150c0a060204080102092107170a02030d231306 69
    0x5c030503000420014208103012002d02d003e129036031100e40c0d12003080c15081c0605800c0f030142070003004154090010341d60828001c070032025100d0716503072190f600801c00c00d0141e03143d01c0751841c4010802080360b00c0000340ca0011803440d08244400c880070b5080c00c90020491443c1d100480d058207280b9441c6031034a042da40c80c14098041011043d0b04020740d0000055111240410603000c15014012a90480024204541030500c01440011182c0c010000e46585000000440313805542514040b552520740d880c00d9500b040d003441c0007035404080b0700000c0c1201f280783c0c2c1c46004400319040c401c1081703160000c180440c00000d1440e86a01c4210520310724030b001000e02c0203101030000701069075089861a691441260855000039000c1da501184142007420014400441c241e00303040b002009402518000c2e40e200d44038002e0762015000c9161402c202401000034103015940201640d007604200340000308a0800040035000202d081c24440d0b00c19003640c411149003504e04600c0081c100c2c02d01406a4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 762618678 1250 762617428 762617483
    0x120109120f020a060f0c0f0c0209040219030b070e09091b132409050f0c030a1a030d08040606150903140a02211e0a021012020d090b0f04 60
    0x40540c00f803403802000042652103406801c8141d40000905c048402d0300040c03d49038101071405c14006100511000343c2d4030042d00e60340c0303c0c0e4100c85101d103060200584070300011090b40020500b040050a003d4590340120034160521016284407881e079544191540c0c0e9842e9065200304002044c9283c13290701c3c10000301d400001164032101086903500160991088010103189110089806c1001e1046148601950b5005035809107906040e04015140d07070810310010f0680803055540c0c40720b40d000108003c1494002c044010b003950105100c21002800f00c0c2da0840381180d4140c500356000c50b81c2d60f00e84d40307403140480c9aa07484405071829582c40e0010b4207074824400c3e09030703c80e501035800142c0c1c6200460f00743c02458005024a88441c642191400400c5403400c3e25820f0511242000400d00050010090b42c0440b280ba4541741c8005050350b40e2800c504818440328000100143c01a0250304a00d03102032041c0b4281029665618035503108160a840042108140d11a48080d40000e8154003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 762619928 1250 762618678 762618707
    0x6010c061104050d030905030d1106013003081009110708071112100f0506060706020d0f020c01020a1b030e21030703080a0c030e03090402070c0302060706050612010912 74
    0x403840d1540f601d0014090034540c00e012070025800345402d00c02d0b07040521050b124001d0f507040000b440e2040850942d25000140a01d0340b0260a62020a12440b098446001c803200b0302009640342001d1401c008006e10011240300901c800400000600d080c4584900d40044500308841d5080000f84e660b400260761041c80151484801e8141c900744945e11800f00200c000c842200a101d640603290b0180190790031600140340f120302d40b0080007450f858400403a130800d41d01c000c0c0180c1d5a06d1000d4060700500014820b14111840482c00e040203041c15030043c141aa13171a2184c6030720359066a04a0140c418501c0001c0c0017034041e0400e03003440c0c104001a00c0b00b01c001102521a820300b56074100c0d19540003004107500060061041c8050500c0314071030140e0050303032807034103004107480400007503624030801e0600e0340110360000703141090141d0710544001070f560003040113a0b02c84040c241080075140a49626109030201c0e035150000500510440c0205903000404008803420210140c42c0c1c10700749500c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 762621178 1250 762619928 762619961
    0xd0c08071b05280c08060403210212070207051813021c06020a0201050a05010506070f080a020c0a0b07060c18061b080a0c0308060a0e0a05061f0801051806010c06 71
    0xd040e14030b1048119002d50741142c00f900981c40303406041c400d40e102180c0d44000c900360040018800826441740704003079040301448294106511602d103030390091003280c00d010410041c007014096540c0c1d003ca8008100d4108994030945c00f45040032442e000c0d5415a401040c00030020151001420302003002e45036244c42c0780c400e0148010684031541a41e200220901c0180d40d95020080f03031211511038540580b4040d181241040ca642d55140202c41c294a0007a1003140d0100d16031907500d02c00c02040140010140c180207401350744251000854102c03a001b15540d50500754201c100070712486102e12030340b0b02c080008070818a08401070f101000c038114544200c002c218148008580b01000070543e003034041c2c0d100c4420008608000b0241e01024105070720605680781d0402059170304250094000c2c00f400000905906e03040000b444600ca190301860f056a140c1001c00c1d0417a801c00d164078104d410940700d42840035401c21038020b0101c401c6a500d07021811a00c01d601c0400d0056000e8840104c1c441c96 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 762622428 1250 762621178 762621193
    0x2092e0b16050312011e090507050304060911101206080303090d0e0f040e032a03121e10150311040b07020117010f03020f0d170d021e0d0c08071b05 65
    0x221504500c03098020000f856200348200050080c06c007066001084a013408100c1400c00040040c0648005000a00b100352225081d105201c4c11304944509503900800c402c04080007100064080400300c07054103080c501e400000a13144c280401140d1251180300b004e040b424a00c8a410b40b0500030a0030781f0f60f0001e0036040040c2c0305031514030541c124038008034001c6480b24441c052052109000140319142011074078506503a58000000b510500307280a00e1980740c59a0f1650a40d1b0a60700c50120401c0308820b200502403030300785420702c03134043d00c0c0030b60044240b120084000360300b038880080114821400400040003030b603010002030311150b44140340c950300a5012800080b51210280c00c8006202103a400401c114689070342c80403081c4c2001d44181503849110345030320341ca080e806050084038140002e8842c0400c8802e504039000d80850498044070392062040d078007010703008a0100003202e850004122042d60080254603c242c1346603590030301790b24058183c20014402c60100b1a041e104106 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 762623678 1250 762622428 762622447
    0x109170a03180f0b070903020a120302030904050406021201141e01030e0f0105060117040b0106050703112509090b0a0f09050a060b190303080c0a0c02092e0b160503 72
    0x1540108042d00500303c818080020b410402d610f60000341041c41486601402000161500000c000840358210070341d0642d2402800d003603045100c0e6001c0340f07a000b07185c0350422041207a158040c1c01ca0b0300b000780b04101a40e0320384180100380c0340c2a0609580c0604480d5800841e80310282551400c402e06242c0888c2c0158034001081c600400b03011b8203980b40e5112410041c65591145107078910042c400541c29103810541c60740e80c0c40c980f0600070003040241c0001e12005140c001c070070078200d81691000302c40c04050444040741d0802180f03084030a940340030140c00035038400d05014505100d034004d04020411b0325174860f500014601e0400c002c00b010b07124000c500101c0c0301800032581080c00342a010401120500402850703451003c000c8101a00c5024240040b03640954001d9201d01081304441c0d40740c2d1440b405807140408000300952103000c0d80c04001c981d15020100c0c44007048022950803c0c2601094154284500340c090100b03002010f100c0800000e034400d0020901c0347c00340c07050f03c3c41c120061 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 762624928 1250 762623678 762623711
    0x50a02070f12350d2c010e030405010509090c04271b020d0c1112031315090e06010c0204091109161403060a080d020604030e060a0e060d1d011a030109170a03 69
    0x444506048400c2241017602e907040038015005500a04030240d03141c60b0600b00040c24900413071080314084d80c8690000341e4145005805c40300502200c65400765209010221140b4078030304040c42410382420102c40c442800d01e040c0600341c44a0b80b98028000600c0d6901040354042207001069620720260044c0c41e16a03180d0038099a41d1b04010409541c1c2d485560b601c84a102c04d690b8485140a0b004150707160f09550b208820700b0a49580c16454001500c81ca8010ac82c1c0001d046d40c041d50083c0740c070342c00304200218960784444034103058070321051943c0e401d0b06451404209030102c038007007808a013480705000400801103a112000400000c440d13034841805134540000c4038a20b5001d030307000c2c0d414841416041004030645a4007191801d01d414802c000052403080091107150003140d005ca8006c180c109a030700020601d03110368002020001c0060030f22406000008610201140703c41e115030201e04048c054140201c0e002462100040351144d456045a4814001c14040640c6c844803a403040114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 762626178 1250 762624928 762624971
    0x5040c1703090f12030a1b06020409060e0f040203030d020d0e0607020708060c2104020d0b07031d0609120903190c0504050f1303050a02070f12350d 65
    0x150041d500c0701000c805200c0001241e90f40340d0300c240306141c4a0100c51200108a4030652040d00e0440d0040581c40001031f08180440740003801140080303004668189a980884100d803a07a251050250300d0f03031000111640d00584010390181c0040001d40c80420494000308a001c44410000500880110710141007442c2a03814500507005400b041007030490402070b10f5003145401e41083e16050306c00c4510b0700710410114078200c0054004001034155a100f8101e40c81036078000d02090400c1c503040350024014460a000e0b0207414036a03c0342c1608120b00014860305c80c1c05154000c0050100c603101e07481c020f411400500ea4140b02c1d03130741d24516001c102150b07110001e114094001da41030901d81000285c0360300801200d452a03210007004064a481e40001d00c4054140c00e00d50380d00c0807691012130610840e80c004294102015500207204041180c42880045c000c88021102402d0307542020402c0389512007500d4031000030000d428500200f079004104071400000006004690b012140911191 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 762627428 1250 762626178 762626219
    0xa080409020301050f061206101704032d08011202040209060d0905010f0c0e10050d020f04051e03060c130e190b090c0706020d15080d020708011a0405040c 68
    0x4002c4010461814040280329482c0401c9031024240307480c0d50303115904e8850047c900b9111340716004a41811a00a0900e010307000b000d0411300c6907501d01fa05001d8808400c4c12010b02140781d10300303492111703495652030041c2d080580b507031004056442c4c20702d2160889140003040c0c2e8499400c0146258a60703c0c10010400c0c0e507459000420210700d00e051043c00c40f0b120400f440303806400d04203c082c07069070000c44c0154890701250100780c102c4840008a071a80500301c40c080c4003d01c0041c400c003440394410060f0041b900704882c210030901b052a420083d098900d5035058060f484500401c00700303458480501034048240e40d404188075a51100f1852101080d02c0c1880d07003640040503480ea0164901861064400aa901d08442c0c00c116140a440788217040028024650109886802c400e582c1c03c00807034040c5680d0512502919410b80f1501c0d0555030500708050720036840d00051904041c061060002c11902c03940710803c400740148405440020300c103c030100c009120109100c07148517000000c0c0103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 762628678 1250 762627428 762627431
    0x31c0e0f070e041a0c090d03141303021f050f0703020c1305150a031e1406010b0a0206010e010e0402040e0109060c0e12010e060a0b1906081510200a080409 68
    0x1800d00300203000319001413440380c9424054042040703a000700f0007261039600c03050320000421601400d04450a0720f484207480c2c4c80c14800112031109003020405441901e000f20348401244601d034074028019aa0f050402c1c01090b03080c0f12007100d034007507075002c1c02c0424002e00503509010080800074051070510010313012403554400612011030004818031a11b88429148a0500380c15500e4028512aa01c6000c1c542400511042d004000440d403005407040b07802400c80d540c03541c503800d070003806800c154414801440740100024240200c1a80c143c100e403002c1c64159503030b131100c0d0240405014081c18000700340d9280c81140d00001c94502c11f8103044017080d5110a0f0001c81c00d0b017000f50500e18015a90390680c108000c19107290030120700d450b0421102d010000703645903000085414a080740c1103400b030701c0e0709030f1000003811600158068410307034a0300a20404c050020301045800c0500445040000345194004507001c0713946558000c2c1030030110129000102540e03a202c503e58419040001c031035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 762629928 1250 762628678 762628681
    0x80102030106090b0a140d1404050c030607020303040f0f0206040b030f190c20070506210f22080408100615090308121302040e010e0c03031c0e0f070e 66
    0x7a8449440700181c10718010180c9440d1407104000c04e04c180c5403210850f031000004060a03d4002c651101001c0702c840103034410f00746404e0a00caea86550000003154000d0086d140054400740c80802141c2c400d43d4401110b541a01c0580c0750f22040c0d0354018002c9802c098100008586041c3c07502c0a1441401020b0460680345013441c2c010164000000a4804041c20700b01f040c200150026100e4255202501c0c4d000b940500c03a0b1005441c18a8950009400c440c0000e05050b54100c11466011404020035048503aa103402c00311007003100044a440a400e0f0b00500401040200c00c10301c0c0001038080c5220360b04040c0c99510030ba08000110380041031990781c40c0002c10100140d8004202070710024101000120701c0d548032501c60b40310704035802480500d4007001620141451000c0b07240755030094002c100303015040352054024181102001d108c0d2045004000c080d19002081341c10216641406242e110050b40700c3c50045e21000591940c10701514444095201d010407081004042c0c0302d4026010303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 762631178 1250 762629928 762629939
    0x30807060c0e0d11120f030913060302060a0903061107020a051002010609053402060105010c06060801140405160315020903010608030a05040e1f060c051603060c140702031507180801020301 83
    0xa212405c00400410b8200b21080e1820280200545048003010760303100c0c1c01480c440d60300340005c10150300020340c0140042003d0807130ba0b034050426000d0303078442c03007040000c0140424016064060341a00a40c01450f0020500160078110300c8040c506515000201e00e4513200c114034800d0719012140308103407100000071078401c00003101083c100311585442d1180101c500640094071403405003d40350501c9030f404251020004140d2010f4003c10240000300614049851a50151841950140c8191060700074000903011200580801c6a0723110301a03074040482212164080c2d04080041d582c15540d0301e41c0001d00701420b10003007604542a645c0c00f50b03038500302070741c1191030840548184c00e2102000209030140c0d0721089490150758160405206250840c549a40340501e00e00c811100104103030f100004101700c6820041c000c440944540140c4415001d40b21098045c24201a6165000504102d85050314408954000590340340803005d140d4180240c00520540341d000003250385d03000004001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 762632428 1250 762631178 762631189
    0xe06010801021c0b0a0b031b120a0c0807020a02090c040306020304111f02191509050c041b080c030c0c0d05030702161d06010e040c0302090301050f01030807060c0e0d11 74
    0xa180300d000d030810820f021131001c182d002a00d03014100075801c000020682c42c0c04400c440c48003607844100b0550750340b9600842c00600701001d80340c41d013100e810074120b1441c0314080c90445121340f22a900802c81c41015030200a00071001a148a09590f8200700200c0499914002140320324024807881c01a0107c0b00c0600560940001101908007070359030b68180d2295000c605601600c0c900c0760000d440c1c90107810090703401e0719405a0118824074084d1280c04220010440c1c1c218450100d8080280c92007041d03404070894440b256030000901d025002501c140b04485c0030710340104030303080210305080081043c2d81ca4681c2c10b007484004150040200058190b04201541105110344c507100241490206425241490b40c08a00b402070036036030004841d030340f0a083d202440d4100403c203001c1e5000021b0054000d6100800342d03400b950901000601c8003100f0320045040320b034081c1400385801081d480364401400700300d40b410100030700d040b03c407011651045843c0c184540100750404120210504101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 762633678 1250 762632428 762632467
    0x100510051803010608030d0f060906080f0d080601121e09030804061104060507080d091e060b0306013b0f0a0b030f1e03040902030f0907080313180e0601080102 70
    0x303119a04100e400c0c8917103030010094800350700c8180301c0415503000e42808000504103940106080e030b490a0700c00101d2001c00900186081c410005072529498034100844400d5000c0f2841400b0074041c0300101c1807070301c80c1d0f0321510030052014489107424214000c94000d54074066402d0300024003000900090000c54402c1c51568124100c50386d01d80780c50240040c1445c02940b502400d81140441c1c0002c920186400c984549640512440719a00ca0f040051744140b12482040d16079a05d07184403000d6501700000c9003810f9801c0001030384958545a02811040e40c1c20490388400c240005035000402c071301011b070640c082e044a00380b64095261000d107100445060b00c8a4501c00c0c2d102d40c42d145210b00d400314144208102800340f0766441034051641074914811503100e60800f074030000c10070001400c03102c0614001c1e58248243d4410980e01e42c043ca0340e0b40a004810502c41888440030048500035020040311041440008210814034112141c10070b0300136801451165000180c8a07002c801004c10360 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 762634928 1250 762633678 762633727
    0x50f0f130f0f030f030e2403090c30160306020717070308010311031203091605220b040b032b0c0f0b130209150108070503040b070810051005 62
    0x4009491954881e0943d0700d071001805400c0c40503090107034121f034540e104208604407e1a00d0f4900e0500b0070f40c50300540c0d5004a40c201c6450085502091551400341c01d0f5070130078164928001c0e80d44400c0c0d0f980681c2880b805860840d244a8140701c1541850050408402140540720050311160075042028580410825076500c00404200c1080000c0d0081801760540350081c1da60051808480042031401030315009250203448041b0800c2900c290000740c4400441780d0781c148039030ba156240f0a0048039203800413003445101b41000a894407082543c404040070000a102140300c0c180580480e00b00440ea400303400070244c0703a445840010220300f4100940003190300d09480c02c21115228040681d444850050200c0c18190200348806c0701c00d014085a26001000207103030f814441c20107079824828108090121304c0c0000001c20f01805081030301e0ec1980c01405c1c42c10fa03582c030760404844003e0000c15101c1301500c4404081341c540c42e043c1901000169903203450307a4511349504810400300702d15410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 762636178 1250 762634928 762634949
    0x301060323100b03060a0c02010f15080c04180f020a050d150507021b1c0602030f1806130609020a090509010c090b07110621040b0a140610050f0f130f 66
    0x4800c03c40d180010a00d030b201c03001c03000004004000401c101d01410680030850740860038011070503510340040c8244c00480300b001c0200c039980808031060209981c40328602e0038585804400c0c140100d00302c558540d180034402410121959215030000740600d48012080c0e498100140d06d0440c030030294820f42d07400000c5400102014144509008e02c4042c07030320f030054041d0040314565400400c4416500d8895540104155140e2500000c508030a100c1166080725800b03009020303654419000c01c90342d006440070ba80c003408440481d101c020103061001c2d800c90f0400c2601c00005043c002621501d4002c240c58400802c4881c00f0003802005101250844a035100e41084010006100940c00c40c055010039160507440304007024000490903400c182c900c41c07414104041004000040668030b120700030102040101e214682031101c2216002c41d0701d1600068204207031440a80510301130011004490a020b2901904d64003862140c1c10143c007071451041e110000340303e4000e09288010150400e881c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 762637428 1250 762636178 762636191
    0x20d0c03023015060d03031401150f170c16020d0c050406050102030c1e120c100f0b03120d09080415091205061b04030210020a03200a0b06030106032310 67
    0x90f0020030000582a0761103001e0034400181054000d4000c010590401c40410340a580d403030805480d080941c00030040014412207501190a0284201021007010324046401607552400c0410140d8001c0c400a00c20b00510869000180d03a090100069a4131074805042014500310502c001c0c1e0340b440d002681550400e001c1c0080c5044005000c80c844400310f881008030503806100503041400c2041c184a4081d4000707940c1001160000d010021050116020419210244510822220104003150389500302c440f041d00b10b8001c08010f130080007041c100c009440107083e5540d2a0541c0950700910302c403900c042441c0046600003064400404c2416021420340316280d03507003900c0d4003004204c442c10940008c10203580c84003803030958000d10341c00b400001106682020107503441320700d00700443c0007589490b107446050005521f80c110fa119140c0040424005c940d071181407054005202c16010f6507a2240000820101c40074030b8401e421281e1003400d01c1c0035043c40c96050036544491840d4607400c00c0e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 762638678 1250 762637428 762637453
    0xe010f030b0609040c050a0602030a080a060b070605330f04050c0d0504050a0c090b091f050f0607060603080a080604051b0c0f06100503101107020d0c030230 69
    0x1d8a01e0303840002200d60861699980c0b0301002c801c0f4071600030f65008819003070301081da542c0010042206d410180c482c6039403903458030314001c10350701c1074054082d10360011f20440c0c00044a030741259410000350603070145140001801c1074042d1131103805540030862024205925424585905000342d182914240114940100c1e50b803110f21844242c1c28090390395030006400e200d414000c400081e60300180e43c0d840d0781c0d903070f0310000003804100301071a114030402c13000304003544840017140200f414540110f86c0e64a24040030440340f007c0c5220816002001000400c0020301944076000140d40304034580da441e00d640440040850748002c14060060b45040c4c18040e103803890840c0c0200b070f11419003125541cbd0240c200d4a504000b8000c2101c02c0c0c0784a1101400b00040e110f2001005844050301124450808203080340300355403003407070444140d1800b00441c0d009401e10850000c12107024029401c8c034150360341d011454040307044011044030601605c4140600206449030801314a100c801001b4000c142d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 762639928 1250 762638678 762638693
    0x3010302130905030f0406030b0d0203120f070f0311060c1309091406040c140405040c0611070807060c02040b060304030f0f030f0501030503070212060f06040c11030d060e010f03 78
    0x60201034400c0c0381810110360004a0394010a080c1e95005054a80701c2090504040854009010f40e5004ca401d200c00e91900b41461740440000540082c010065807181854192895101040d1208021000c100c0c07280860300c000e074118407262195494010940301501c00f07031f0408030003801003002d00c0410810031200348104d942c43c0301615954240081d54119a03e801c00c4401c510f0b2076070004c1401010104405e00001c640010f080b922140113044658034000b0030401111012580208065001078040c03000510412405484031b8400e4201d844d01394896489a1400000380d012400098001c001c210031428580030b1303509425810707540142141401d680c0039100040c401c0000080101c0002c450314450300ca5001424984450b0b50200211f507128104942c0302e6100e0b090680c05900180700d445282c0c60001000c5d407203600341c002e0702c0559886200801000d006154020300821495024201084a0034001820040301d01c00d400103c0b02c1c0390070909110b002c4140d0081c00031202401c801c00118090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 762641178 1250 762639928 762639931
    0x2040b010905092406070c05130b12070f08030c1b01020a021206091b0306040b1b04030807110904120c050a12021f0507210e0609150f1303200f0307150c0503 69
    0x4841c00c50060109102c0c8100070200b0940c1d00b5031080be0046074400381040419040142c641c044c100e00b049070b842d119050323928862056000c40c030380d20020441502175444094080a000c0510503076000b00d000ea00002c03041c03071548119007a2030f0807481c14814600410000433802002941c00c0c000340c00041d000091721894000e1029203005481c00016140d945540c00d8040b4180d5143d840c55290b9480e41003089240e0400181100c0c4e60114403400798140c507003420358038030455000c41440005110a603048940d03031440d80c8211158032600380914009611544003290320503581d801001c20000c860718440c100e922030150715401600e040141b140c010303844400308a124003003001e8016071005034034850700103000b41c1c1d05010503030281d041800401107020801e03584c1903000103405c082c1501d4402e00201c00c10b0040c0e44100d0502d02c03284451000a000d01d00307900e174071502420008482c0b5100d010340380c00c2101d01c02c010406504001260420403601d5440750b140c010341950108442e008959015007213200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 762642428 1250 762641178 762641189
    0x2060f0f010b0d0e0706020a03090f0b09121f1b14030601140c010507020303061f020303040b090a1709011202040b0a14040906141c0203060402040b010905092406070c 73
    0x90003d2a018450328640041c08441c4601049813942d80e40c0d00002515240c8048040303000420f50140020710484c0208000b082d01e400f0280c5a2421600004106003a014203a4882080c000c0013203030307101512851600100718800840110340111221074123066400c00c2a031040a11150001e4425000f05100940764001800e08000c41d13202103900144429004d40009980c41d0741c00e003010050301681c084065802550f00391945d5402070890b034030442c070749901c10032a1401a441400042e012504510925400100c101c06490b400d4806071140d1202d51550341d071107000404001041012541c0c0240742901000c1c0201d000c609107070801209540d20b00c074521004080260f45a840c480107410441260300500c011002013118959400202a0035500b650f4181d10940ca0001107420281d46428210802e9030300901401c01a61141c0c2008005c000803581d181c10008869004103c54980002c01401001404900900e451803070122404d1042c61003c0079009100501c00903000409299100c41600c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 762643678 1250 762642428 762642449
    0x3020a02040b0f0a0902120108120d0506010c0203030a0f4104080607030e0d140d15170c030f010b060d020f1e070606080718020702040e1c02060f0f01 66
    0xb0590000a030000c250800e1a80c1c00700c0c0d42800090040003680c010300d0b02c400c01c2201c4903802d07a80c643e9042c0d190310003040c1d40448280d04010381041f0b810b656200c42d071b01c000141071144949440e50082807850b00584580000300d0000e103c140a46074000c090282c1c01c1503540e0741c0102c0001c14007424007840700c0d0b841107090000381c40b036034081c0c81140200540e4040d10501045448501e40400010080d0148001035421030141a09040d8020300c942c8a07203000b6064440d000740381c002140d041000070700804280c0010001d0190000c0307074214070082040d00700c40d903103802050304070240d004041c1407034254440354555038507004500b102d82d102c020648207404414100143c0b100c03100040e4015030710032500c1c11740306419400650f55031410350074013070b00805026102c10040c6640303030703034803076a9402a07070103102c0911210b000010034014268000f024040e01c0a800412443c03d600c243c1464008500d00341c42102c1e41c4240340142490341000b0051f48210049800502c604100c487c0314205d1340306000d000c401c031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 762644928 1250 762643678 762643691
    0x405130611070f0c03110405010e0c13090e030a08090703020a0b0d0902150a0210060e060d1403030411031c08130f05070807060e04052e1205030405120a03020a0204 72
    0x14010070650350181d40050040090f484036180104031003184e07020803555002441c82c00c40050406201d11811f0311102880d1703c0c040c1c1c0300c445c0408029080030b03e10030382d00844d868001c0b400a41c00d0144074200580324004584515800d04050494a0020807800c131750340c880401000540c1d180d01c007010841b80c003d40300c1640ca4240101a0303010707180307100c0c001c4e402c0070300d001403a954144510000c00d04219144d082d44c03010024240d403503055840ca40700e205d820801c50404119103191034401e82907642e02c280206175013008000441815500700b102d0540d10641c29030a01034180c20180421100540c2100407a00c0301290941c0240c080c04000c0c01c20401514421208020020001c01c0c010390950000100d41d00e50707603149102590350b8624002c01c40020042c2c00380c0f81460400c0c2c022280102e607072410564100303520f0150b615036039040c2108609151021400051516145808038041340c0c01500a0355686003001c00303201c00c070010f03a4a0b502c115800b840c0f80401090f404140200ca40780e04550200b010b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 762646178 1250 762644928 762644951
    0x120a060b1801030809040c0e0108190e070b0301091103010e131719090807080a02091e0c0403030f0f0c060b03070b1204050d050406020601270f050f0604051306 70
    0x15100c0740000c00700c090909400101c00c2c000030402524400707008407810b00045c400c140c8200d520030481c0400c1408203581001044040c12045004101408842d00c0003c02f540b08030403140c60710781036501c081e201c030100200602c20a8030310b0003600c0d111044040041e00d5949010f560b1200c101000302182e81621407040b42d81c04100c11415040c900c01481c1207070b2603d800c0b0601c81d10200c0152610b0007004030b54260b0001505c4040862142c04441400b40070308802c2c0c0079a000c1c00344254000b030039800c0900540403002140340745500400d000741c03a1408130329203460a528001d0300c8201c2107444030701445140441086241e5000c11806660b41c0c0c00303680420b005406001091601003641c004000d09040415000343d4061101a0281f246001d14211140d0b400c280009076450300c62401480010380120006014665414110080f1070012503026840c160501150800715051044d4803c0783e55201e00078850b2004640c0300607034003c1811201004581881c04900c00107040d90b14006110b2520741304070030107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 762647428 1250 762646178 762646189
    0x507020102070b0c010510090605060a050f0918090706030213120c08061305011a03030703050a020a020303030a061502280204141e0901050f0106030b120109030914120a060b 76
    0x10601010155103420b00211340394003034841151039801c035000b2a84002451282070051038201c44c40a400e07140f60441c100011034050380510702902d1000b0041182e82003d40328200082c40070315581c512030313500d41050a1000c0c14502158898030805005010340d41c0701809005800c0c04580c2c1d002080ca902e010340385480103500030541e010702140e0044c01d0801401b295011226403096100e40000c001110308400c50003800b40c150314444d500b41d070003800200e00107030055005007480b2000340100c41140c0a140e0019146a2086400c0d01070304c0d841e000c0c104560040c6811080003503003140060110902c040017041501040c2c80444924481c001c000f903c00d54541c0c0c0d000c059103004a598000c101d141407190f00d111142d68078668100c4552280014010342018465140213040da116202416442c111048025000e020442076118524401754000300c0800d22640007004d100e81c9440501034a0b1400c0103440310f4008118600a80c40b02d0442c120b008400b0406e4411294040400103022400602183c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 762648678 1250 762647428 762647443
    0xa0c080f060310110c190507030303020306061b011505090601020c1908030c010b1503070c0f03091203020c04050117100c05070210050301140d0b06090711011d0607030e0d0507020102 80
    0x1d82480c11300001008403148005102d0554820101c400c0419586104080010710110180403a0441e40742400001d10079001580c00c0070300101800e0808240445c1c1e0b100c100380d403e0a0801aa540b4000030050b88d11400d0f014009100c11519502e641c070f442c10000c0e441d4149000311912602a100204038210b940c1142200900008002c0b82c1c0c5503008002c40c00c2c000c1500f884620b1068480b125010501c04150044038407482c040d542c0c90080228039500c865070b006500e80101c052000c000b00101d40e80010b01d0030080218000d500500180040ca41444100da8042e00502c94000b0303a528000d2141200240400c0030001c442c800080200300640d00325503034014604000d602180c500c00400c009a80000918142d501521460010a400307504200305c5140300310b4010041e4100f000054454a0f20040e0503620850381c1c03e110300c184039690a61800c6903c541c10005840098905950702e440081040d50703444503c03030408200b071084c030a0300e456032400d25502120030800001040700031640300344200b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 762649928 1250 762648678 762648703
    0xf0910050612071d0f010f061815030510050a05030c011209140607030b03190624080a11193b01050306090c130b06090a030f0b0a0c080f0603 62
    0xb100c1c0c0c2c0361216890070400f2813113035560100c0d10780c00d00840d4059010b00300907812034070403008243d1004c0c902182550882c402c0ca059035003c02c11b00c000068080d10100b415401c0504541d800511441c005040b0b086011082e0007203070040940d00d00c24040ba44000030081c4205101742042254001015034410107880420001003c02a4010600c6401640000c0c414040c1c551903c09100341c8030220245a600c40f0601080c1c451410251070300c0002c12900c1d03102c40100030302100003400040c1800103a024051060340412015844465142d0610654070070301500894211904140903511440076003071204180542d101d007000d000e541d07a09408440a0075203070151405035044101d182020001e9683c0c00900c02d0314013070b006500000342c01a9000c240c0d90481c0500411086160751b072a010180208200c201c100d802803020002841190340300001440110700c1860b28100d8215149010b245140b0b015100802d81824441600d90f000d4100141c60b0713004104041c0c216880d41c413080005d10b13080080104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 762651178 1250 762649928 762649933
    0x506071104061203022a01031e05010b0a09060e0d14031e190507032001090f06050601020d091514160c0e060a180905010615090603050f0910050612 65
    0x25031200005a280f4a060194007518907888400c1c416545007030b94941c1280400348203003c05880c66000307501a10a1200c1c880b030709640c50592003003610407980282c014002210011075010303400b543c40500360313014020703d1610f10369500c800004075507403440c524002001c5941d1079480241c500805c000395500c40c0604106001050b14a444001c0c041e40728603162107080350518a07002444c0d0046048481d1107605039249416900c80303041810b8901d59201010b00d0b555260031890001c143c40c644401c03000c900403800081d26051803c00649491202c42c0860280f15010780300b0440d0602c010300c1d54018108900f000300040200320280051403141c544000c4541081441c1d150501414040c5c1405403005910025003c5e102e000811032015994802c485100e4100d0300240a080c0050f0004096640711f00008104a51580c0807200c1c01044901008006040d40c0d60401c040e6905018054018110000128043c18041078568582c030091072481d040b41c5d1a500450380b41d0711440e41c200101c2c50403906 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 762652428 1250 762651178 762651191
    0x1504060207110904081c1a01030b0127080709110f03060d060608060906010902032a0705030a050309120403110d0317071d0f1c080d05070f17010b040506071104 70
    0x90002403500140362000700050090001c2d451b060051107601e902c60344e04288080030b05180401103025141181c2124104010085c0341103400c0075030030083c1c890310581102491198144100e9500d04841548044801c5080c080f10840420784078048680403001001495903e0f511600406c0c1c400b003001c100101010f00d0a280001c1c01c1c078000c03440354010b441e00420f840b0300d6640c030b003200d1043c2e000039140c480e0601884400c50075804146405205100d241e04803d9040420a8880c241150403d8401c10301080001040180050041c03100f41e00614030a40c0945c1481c2c10740d114024401c0ca241c280501039038111102d5802d0500440f00d54410111801c980038180c648080014250828008001c480309441003c59616203130181003134600c45009008000c1000303903600c2c400c000c1c042d164020340d10440200002c15010030346014462003100180c440c07200e86203140c140201f01071454002803845030081d50050001005000456045540840300e44d40c4491803410042a40e03145001c00640c40380c039141c2c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 762653678 1250 762652428 762652433
    0x1707020f0a061b0314060f041b0c0b10080d14090d0804050301110712081810090b010806072106080a06140f090303010303180305010c02070312021504060207110904 72
    0x10800c0d2104280d112403c5082040c03610309900780c50340000700c00e40207021030000031110b06101501c0e041215005102160780d207a0400001d05100051071400c00081c0030054800c24000c4106010350040e07003901c08140c6c8949490300c119220344079504440200300c0c01d00c0c00000102c07034803c155840c00c0d400803c0284107203100d05c1e00d00d08903405403041600a5090002e00c802c0d1400c0300080d40e0405800504040120641c80c404a644460003003201f01142903074200c040d60120304000c3d0b0924032200300000542c1e410301c0d0900d1000c00105902c8004141c0c8880c0411540680c813001021034500750191700030f450540504660b01808158215552510640d038540050240c1c0b0b800003c1e00d06402c162003c500d80f1882c04440f0b4904084842e165242d20400c01040040d11a5034800024140c0410b25041c241c1c403aa241821740e0282a02000103074403814040c828041403040084100395140010b1044441906026441500c01407010701003540c08100704090100b1907868550070280100082444e00d01803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 762654928 1250 762653678 762653681
    0xf030e0910060f0504050f0904050106030f120905060918090c150d05060303070803150409020a0602010e0d0503090d0c021f18090203150d0f080f18101707020f0a06 72
    0x91144400098000c96003e5440713000c2c004540039640040e0032a20303034042103030a12400ba43c0c090000c451307541d43c0e814008046500401c0c1410003a204079200c3e4032144840c2c2c001443e084040d0030451140f101008048441c0e0341750b0440c4012440d4118860a466071004c400d40d0608200c140c4460301b2480382c0441d10341000401c00200300d015046034007008580c40f4507092690368010070303000030a00001000483c40f040f2000f101301401240042000c0390901060780420443c9840d80d10810150b0344540c0d52201d0034006016061104009203072050540c589500c080b9601d0341070301d034400f0034001312801280c290f45401c00da19146242126012469000f07801004001c0150078406a0310340280301c00101d81d00c85180201da020b800301102c14034030382074403108009000619904c1110354440021002d00000c0a0801520f105142d200310a5195030390700342e0900c040d49000251510807040c0c20b060380a6107401c8255030080c010755604031403142e51040343c264980040c422200302c807846100c80d00d10070032107035 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 762656178 1250 762654928 762654961
    0xf1f18020702090c0901300c0e03010b1509060f31080105040506070e1801090203011d010806041407030b01030803060117060f06090a05150d0501120f0f030e09 70
    0x381d0f0b00b608180e4600400c041103010702c0c1051400907000481041e54111484441a00ca900d034414803000d80f26541043c0040b0b1b0f5100b5031550115a01035400d500a01e000c0c42040104801501e03000d5941c4498004c3d45107520640f41500e100d900c0200740e00141060305815504141050228207512441241c1240720343e928140513404144000803000c01c03000700600074580031f9030f803140091401d500c0703405042d90b0240c5260049600202d411100315054404061201e0007040c8090005a89504101c0c070703003210705d007406440d85004034140010851030000082455119400140e001041c043c0d940c140b84c10074206510181120200d81d0000c414400f489000798010710f82600c0d040b030b81080500e0206207014049500c640c0c8943c10011007807803400c00c2401008400e41c01001d000080342c641e4001030020500d14148101540b011503000c071018030f81d21805000d807040c011851502103a82d66020500c58401c90300420b20800404e80804040c0507000c1c01c1c1c5c40d604020202400c500c1c1503281d0b25503041c1d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 762657428 1250 762656178 762656183
    0xa0c060f03061716151e05090d0c05030c04110405060a09030f0c080c04061409060a090204060806041a031009051002070b040b0105090c090103020304080f04030818090f1f180207 78
    0x803001e80017990201c0c3e01180c1072024801c1d101c90f02e07080c000521004580c48030a06640a00c40200011409952040002040c5d180310300e02104d0380da4103140c20305142034458000e8a02480c5410780815101c4080e03800c2d00e040318800c036491070f90740d0000003084510308103030b5100500320401d0260000030840c3c100d90017400d4a20b20f100701c80d19000743c4c00400c829903400d4841c03021042000c4200d1180c60402003480c0c0c0c3d200760082d10b44182d982e03440204804980c4182e0044002401520600a0501d4580118400850108407004411820030300103500e402074044035000c520355440f039400030001c0c2440340a03404041c030701046481e4181c901700030401340300454007140c0b070440b9100080f4451404555035402036a14038001400c00381500c00540083d44007402c00d5604103414812102c0c0c10b40c0703410080001e544601c1a4503110603204000c80008035070380d6803140c81020b0010030020b45c5501600b0f0701e684580b51080382c23250000705155005030380c003e40e042803100355805488807890200e01e40051601a2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 762658678 1250 762657428 762657463
    0x70f0320041e0b0f06090628020c010e0405161805030d0e120a0818040902150405130c0c030309030c06050106090f080304030503030f04030912030815030a0c060f030617 74
    0x480c03d000c11003041c0c0e02051040d0b014070203010003056070034500094541c1150b00207020f484601201c80c071058859065201c4d40050340b00c81c2540c00d0550380440d04401014094400780081e081c11040c04801030081030703e40d002c225081400b0015401d0041c1d150004200150607290340d00110b560050030100541c010358043c10310310080500305040001c040c0d0b106a00302d01400e0411311405100c10704941000800c40e4429168040600540d03207505200041a110910603907865160a003803041340d15218061502c0180380082d51902c0c0c5030044043c0c0701a41e03041c90b001803994510f103026102d00044130300103071607681391000115616030008048004d40e035610ba1070400302940e510035107540f0b01c01c60000409680013840400c5c0300400400310103030410306c41c2c1409400281c4611030014a40951030055001400380c2d0188509000c500100c038030078590a5000d0419000319440c2c071109030f8001d08c10303201006a0800f4110450340303e07510040151040d00e81d1010b5404851030401d0742c62161003901500074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 762659928 1250 762658678 762658691
    0xd02070305250309230307080c03060c0310121502031008071a1209071203210603031b05070f06020a02040b0117010e0a021b030c0f070f0320041e 64
    0xc0100c0401142c90940c141d403421a103c0c1007201005259400d0700c1a019584241045c03544e6641d000d104040140000700014001c8100180c200b40c03034010081c0010403112000c0080c0302c45040901c0600c001d460010742040007024161800401140106048490f514408000c1c001d017041d03880403181c100c036402401c844101c0e8840001204070507a901003071841c0d01040040d440380f6201d010744d85500c1440001903c1c1d12940d00d030602d010840340311804500144c0303c1a210316520102050700c40c4c000481500070071095080d95000750007220842191082034448000035401c114040200401400000343d402e4442943ea07200a03680d0410990120310450600e0400320a81d441248901c0c40b0120b0385443c1034040e4a000242c074010000544003400b41d9400700301543d806681c1f460700781126414840155030718044844280d052003203541c461401a0030200c4100319a650b0071000d40706880d004407000154400b10185801c1a115140d2425002030030f181c0c08000b0101d0000ca1100504440841807080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 762661178 1250 762659928 762659977
    0x706020711211b03030408010e030d06080c0a0603020c010b0a06091a03072010140a05060d02100e0a08160617190f231005090408030a110d02070305 65
    0x9458005001e8040c0d00c15101c83c0e4a5140b00c03105081825005011781e85460345500459003034819098031000e290344002145d0011401d28424040284100b0b4040e1100303450b1400001c002e001c080c0f03c1d8104041d0007180001c03500501f035105418020006080c191007907910a409025008039101d41d041043c00420b00a01101015003144d1040c0c00c17035030f105c110140c504800d00c100c00b49400000e0342240705030611840004041d2042030003e540d40321840c5814039122280d0b4040d900c00801e558000c4481013001c0005840790100c0c1003241c56181404c10041848034081540091603034019281413041415801e501d0f01c1119043d002d0f100369903141c4071000d180108005c0402c10a59102c0071000640c0302c1d40c0c4848241d40e121505545000401250398030000084809818241c44a10310011a51045c000044100019100180300c152200f000390302d081d440c0c40006000041c03802100c5504c40285a04d1407485034111941c400a21404548030300060400501c070740c0041021280490b035a0000744007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 762662428 1250 762661178 762661219
    0xc0c060103030e032404141e0c0f010f090513020f03011725090c050d020a09051306030f02040c090302030303130309050904121409030d020f0d11061b0706020711 71
    0x1482d02172690035115a030f5014200780b505003c0c07080901462005001000d0082c0120243c868a000182a50315110040000700990443c50505010a500f001c0403100c2d0007000d544c007198011150350701054410b0200c10040e11500c1203d0a200704004008242a441c01610042800114044640302040d02d54600e05101100302092aa0001e2101c10800713240fa40e04981c10f036101c5490900c0c18103044000100c142d03004043c0d66400f01d914401c0c24446400c05010304070001c85006000d1000c04c7c950f8031170904d00040c51401030300650300c0d05009182d450240800700c005640c041c1c222a0350340380c45000c824000858034400c80004002110015142c50700144041c003680d000800000c540312801c1054954400c0d00c00101000d40c020700c45031150f664140300d0340c1c42e05007658019250810f000050349061141010740c1006000344000008104c03000002c01d1a803010060304550314446030451001800d0142400003030450b40002005810042900c04103019010195805d1442a5552a1186 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 762663678 1250 762662428 762662473
    0x81e07020a0b0702012a060c2c030a02090403120f112d04060f54030f0b1e0703090f08030c0c16050f06030c0c060103030e03 55
    0x1d52050300040300340180b5101070018500c1c180305042a00003808180c40c031008028040355964a00c2240750120741c2445158004c805541e40b4502d00114007140c07141020700e4168000d900c102c601158610b00402c1910708004c3c0c0c0c00c00f00e0300208148220301d49890024040e80c185c070401040c0d1741c01d004064501c141280120340c5071110803214141000c1d0345426411904400e09000700644c40264079411207408035400400c050805541d45140010b49181e02400180090800c00d5110040c0c41c606803404e4000715217441c80460001c2202050201c4407400c014907100380d003c003070b980807480200000704a20820810041032060603400100c0d0394490308080d011584540300d0340c0021203440095640345c03090b0701011017280310f0782805110502a444a1003190001c889600070b12800007160842c1030410040743d0f41d0303481d5407401101e1840c28040428441202c0422941c0118800300216060201c0b42055440440c1c4200c120f0b0160340e52424001c044050a920b918083e01034180400031040c0310003e0320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 762664928 1250 762663678 762663683
    0x1407060509090a0b04140601031802060712022811010e130c050c0a0b011406130e0a0e030a03090327260601030506010f0e0702060a09060216081e07 65
    0x201d0804506006114000d00010021980c5603619143e140680d6154420001b040308074030071120b55131a086001401b150194001c0010003020105100010396070002110900d540c06014000601c03050a4164a40440c40c0c9a482d0300c0d5038110810000b0044c400c54280c40342e4081c9034400c41900500005445200d0250703603444c1c108490010328023040c62182c004e1640344000e80340c854613003028906201d04125a27290200e03042c120310001041440303c02920580c0c1d001003196510702c0c04900514503600c1140c1442a040c070450201c00040c0c481d4111740c03150001110902c2a02d50355840003900900500c00313404203d0109801c88640c80d031524504070042c80103013603480c82c12111400d00264524050b0030101c02d00c04140d030000150b21200d814007100d80214401d500800655040c41140131408815400980e076000a4408010302e00e075001404681004903020700245c14102410101c0180c4606821000c8883d0029588010402c0c1e44e030041074000b1a12004801c28010380d0340102c45403281c114007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 762666178 1250 762664928 762664937
    0xb040501020606040b0f0d0305040f0b09060304030e011b1b0605030603151b0f0706060602061501031e060f0906140105070318241707140903010906110304140706 71
    0x640f460034141e001e641d100748014a46100c01c40d070180050000140c0410403000240081070400c406100c00c1d000c1c1d80070300741d0078018078103014940c0701123501404003c00c0a410410104a528601e9000e00340c08404115040741001c40310243d400e0900754070041c00071310290b4228200e00003074050b2003202528007a610060207441f0b10390040040649000010b44010000b011050307104018003407000050400c02c0c0d80c0740708242c031b42000303041c6030f0200d603090f600c00010b54004404015410890804010504d1000d0a00140d80109102c06030000341034070484220103442e041002c070711568800420802c40302e0303020003070181944035846007489049540f03880707012030014005080003038040e40f00300c980e12442a1550b14025940c00186021040c1c0d40c42d80c2c943c1c4c5498080b1391030103d50003003007510621005091039108c0c0c2004807005100c80b108410003514464042108a0255002e4100b104169000358040c0800c450008403071042c0c1c1d00030394044468200320480c4005451011076100204c441a0f10b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 762667428 1250 762666178 762666181
    0x305041124180a06020a0b0a0209010e120c040c110c010c0b04170c0a0b071202130315110c010606090501020d020c0108100806040605150d080708090d0b010e0f010b0405010206 77
    0x41e01d40207802041d0507444030a0401031024007512505030a000820250740249007103003080c14085081399000c1e01c1d214000d07004102555850740c0041c5801820542500c200304101e0b102214241401400800c540c0e00c40e08108610184951005058440310a800305039402d140d1550019070320b223a40048000d111034481400100407805041412401d103060380d440501c0c03c406084128101005942d044964215603001d024950758040f6241400c4140a070085107041d913000c5004d0036507a60340c40b0003001d070aa096202601d020842d04080085444106e0413600c0303080034a4614041c22041c01031341c0011300d038040002903075840000e41216016041e005000b4902030240119071162008101c0d000140080034006210401005503d1003a80071350b100082c5403c00240b0741c0c001c001c02c040d44a2144d040070080700003040003103003155100c40d8480c070640c2e030f600c07040e0b000300b00d0f030380b0040380e0141c41c0300d88402c00082c180e10090034131885520b281260000c3c985e2200404980360295001d507a0040e4003820 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 762668678 1250 762667428 762667489
    0x120f02100504080a020d11060d23010503150919060203090c01080f13020a05060309011418030f030406060b030108060412081308090a0f060306062015040804120303050411 75
    0xd654100c83c007c002030114451140041046a8801481a41100d40d22028500700c1c455903645c00094502d0344903103d00325407400f070000f540c0741c0b480c10441c03e403540003001054007080208070803a0380c10345458800380144002e0901e14000d400484a00c00107006e4034050362100c1d88981c070b620348103e09030f01d402c080c00e858881080c042d050071500b040740c12001e03242e00820f10ba512413000d14440d504079400491515010031040c000c42c580641000107a812a20010082c03400c040261034480e080c0032003c44d205d96403424040d0103001c156100046030b4400100101e0b0720040031030001e01c55402482d08500c2100540011204001c1c103c0f2104488184200035400040c9404000c1145100c000d0034200059107445070b40d4201e40d50b5501003000b01c1d54034241007005a400c2419010790340ca40e1107400030848003150603a522250a244092b10100b001d100050401140c10150380241c1049400701032044860720b0040d0080c4003c0e2400c1e0380303414500d03445414520700010030140c4d50040c502880039054004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 762669928 1250 762668678 762668689
    0x108150a1205030f28090303080109020c011118030d0c0203150a090b011e0e01031106030c070609030305011d07020705101101090b1006050a0c02011206120f02100504080a02 76
    0x4901c210ba19000402c02c6801105000700a460400311444032032080001d90101600c070000d8110411040c045942c1042000c83e802c0342e42641182c0381030401590b90300b4070021560040c0b0b600060007034800340104840750241c24401400c070a10704150129a480600c4040030740e40b031810300c400298168401c201c6c5c80f80b942000f000e803581180106c4001f00e440d11082c0e40306120840c098020f900380181209100c00d03048243c01908001308452034000b00c81e541140c440c0c1200340b94111501d4000d49000000c524864007480444040f2078001c0b20811010f4450314000f0040e080030b124540b10031035104d082c41580d0500303050050040d21aa0003c180071407031304050000710304d680d404807414071041d03945500da102c0084c00317540c8043d0b21800702c085a500e05803130501c028442031381081c802c2000c00d1280c03420a6401607101c0b99160380900f009203c102c104c1502c1c001400840d0070028a01990407031940c200145e0100c02c000942c0b08680d40c0007444141001110580542d10032043c0300d6000300c1c410000360034507 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 762671178 1250 762669928 762669959
    0x81b070b4506091c0605060d0c0302040c0507050d080601020106150e040b130204030c0503060a060f12081306121a060a08100906030f05160302060301060503091e010b0108150a 77
    0x585400d0800380300e14001080142a044c40c4041900e03104015401c1010510034039512030700c1100e0710f403040f100320313100e1105082490000034026540e89a0300c001982c001c2c400c0e0382c180e0341d00c41d084074002032110600400d2004e00344d8019016600f0600d01165076a6042c90700c0701698038554036900ea42015004201c09003009c001c6158000310b0566401005901900091001d9800340c0180d500451a003001c0c140b41901c010201a9024a0880180b1400071144004421660b88005090354403c260130607840034070580f01003828ac00c0c80200c00049142e0007445207140c80c0c1286104000b070b11200c2482c080c4500c2102102d0f40d000d00104480c00c0f046000e038403450740103090084021002d584603c032110880300300d60000d803100e00c00520100100041000340c0c001c4003540001070048c2514550204902d03000600030709051160101c00204540f104012182e44118950041001c01303000d501c2030341c000c04c1111646400503902c64005070040300c6001405884400203885c80d182c4514010403850726451307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 762672428 1250 762671178 762671317
    0x50903030606180a090e21040b0405010f030e0102030a050f0703060f060c080c060f061203120612030d0c09060f02010501051c02060f07060b0406080f0a081b070b 71
    0x51404c1c012034038250078821016510300000003404030034564654180e100151074001c445192080000b40f0030b800d103880c1034604941e001c1c24074650710700b12604241d01400c0400380c038031065807010003041090703a0a034002c1350003074007030700704010b40380d184c2e44002c400707031a0f860244400240d0300b0341041100718824020304003614000c0324603a062802980200782845000d481d869107115022062104d0381c513040041030850400c030b07001035103480800e8400000b01580240410b00c1281205001d00d06a9010f000f140c8404146003020404070044240180c00e040140c015000003810801098a845005108941c1a10b030014008010040454140021001d1030a02260803c00074003401e0310460300c4c00e000d0000c0b244111404641e0300c04040a100c12544258440907143d88480510400d001d00810390135034854010400030f81d01c2640c40d4202e51080541e0100c403840740f05803e0009a8400302d48003920071031901184c0b4000d86c4090030800c1f1400300b540c5070300510101001d00311003800300f8034840c074010300034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 762673678 1250 762672428 762672439
    0x60103290108010b0f120c01050a050708120901050a0e0a0813170718051e0901061d10090501030206040b031b0712030c0305101703040b0a05070605090303060618 71
    0x400c414645810a802a031140c0ea00340e464241081e61480c2c01c15000b40d0b040b5040d02c403020b40601d083c594940c0c0d1241e0340e04150510000203610840700344682c1c100c3e010550000c40050741d03166101c2c01c1e455a4002140c115215506e0f24020035840b1606004072184100d074140200700851071030319400340c03680c000c104e0b2050304001e000e000202a1902005041c020341c01d03034060485186001221500f00700009045880d052400c01040b05440d841c1c440703000103000c5940c000865540d40e0100e503004240795080000313100f46d4015a0810884a215010311540c0c0c8004010b440d00e41c3c45050400342d0b03000f8007001303500020034403041c0a12502200a140e2203000f005404100183c45a203807071542d84006403d03a481752a428200300d10f40d80500a00440d2407180c90b08105c90324107041c092908900340c0c02181803c940307491f60940e0f280410401d44000d010304c25030300d0b5994508030601030165030240d48107c070340604120019400311b03004002e80307105500141c8000e181c40401424a514007480c00e040c1503025 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 762674928 1250 762673678 762673733
    0x1150e06030606041e0b06220f090c050f03100807140109151e120903121a010f0e01030605041109090a050108030702120f07030302010c02010f090c210f080306130e060103 75
    0x208ca044103141410391740000400c030002e041040511034041c4a40041c1035080c20b20340030b126040d074480708890010b050b28907540c1e101e03101c42065544030070b055881031889208112020401c2c0d0a100111912101e0989480e04d91954801ca44040780301c40c3c00d001c1c40440c0c0d8100307842020340e0483e040c100f8030540d989019400c00040d004000100c5060306400d0700018003001403200454818454075111b0090041300c00c1310740308640c0c0020481c03005900c00a04002040c44080b0300c80e4001d802c410b000c0c10340140b090040218020111066401126089114900c94408036940d40414411503040c1c0b403208010b185001d60070b4080c0b03e030204050114070041d110303484101610500078403107a00514407a5001251042042000a080d1103074184580f0006d8982120940003400440440307080b52020140100c13042940c602580004001034805014a8240c4607030a003007114601c0114401c820840307406981c00720010040c0101ea01e2501010417030f5104000600201e89046140c0c8202194042800c919 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 762676178 1250 762674928 762674947
    0x8120307110d05120f040b0601120f1803030b18010b0f07050d0f0f0f0219030519030b03010c08012628051c051b01150e06030606041e0b06 61
    0xb01104041c8150020760b010900c2c40041d00c2c00401e95400c881d41080c603000c1401c00340c40f940e18820001d46040d0500080c3c074031140032500c0c65001404031503400d0f401041041201403a00b0b00169440f40c08400203441c2100f0f403142e13442c0c085100707010024104034100b00c80e801e00740040455030080701041d040020070b00450000400c10840050b58038201c0e035030700c90102c00d146000342c030790b40d548003285061141c40410f040405a0000b200c0c0c0c2c420b206080b50701c40c041c40703d09066a10740702d1400c0540e051468240700704030b126010341040307054602c15402000840350350502260303400300a008040e12405201800302d2621406901481d80c03180d0714058a09101500b9860001d04012031061803581034006103441c10322a0a00a0a03642007078520f208400590402000f01076102b42d03040c440001099034110310140300c1c25807102d030343e01035018102500c80d070b11030310700c502140802c4880d2403207442100005801424240520501c6105100001c1c00d00a48241d03403201515802240e940c101002380090f246 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 762677428 1250 762676178 762676183
    0x150e15061503070f0809070b071704090c111c140a02100c170f010b0a080a150f090c030903020c010f0309020a0306140708040c030b040201050903101a0a0812030711 72
    0x11001c3d91200084029054000303802110001e1031588150014941040596100c004031851030394490740e582c039800b4003510030340d0990203550401c1d13400d03901d441d0b080c0f598590040c10300341440002108482506402c4c152250200124120840004410100805010071028060b06108110740150b0b50220345c0e25054000700c03100003903036800241c00340044040160008011540110f224060403d4070741c1031520003120703445040203c40c1080038100006203805a02e900803000500d284941202203580d408100820400a000b02c2108074506105264210700920400c00d00c554160081d00e130014580c00107507141503078034a068042c140c8079803201d001a80c272031260700003852240b40006070300214001e04001d010b000500c110f0030700c411071081c000481d040700352213011203130b020201101c640d0b01c0d840122914081c40841d00c0d018458200110100c0c449500104c00c0252444d43d40362a9918030410060300c40c616102c1c400c3c4580049036920303c0c2803030703400c0290313408546030400040a44106059a2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 762678678 1250 762677428 762677431
    0x605030702010e062403010207080a0e0d20040b0118050108090f0a05070305070f060918141602010509070302010c060506061e03011d01080312150307080703150e15061503 75
    0x1a01c8a000c009192008000d440201d07000c03810980c000c5040869079514032b00c260ac9070700070f40c7d170034000150004041c542e03e0710090310400ba400709143d11001001002214403d5121070040c0c403c905081c2c2c2115954401d00f0412003000d24207180444a514180055403003a00c041c0c040c907540d0040c1a190300a00004008800007107201e1750040008034a141890340c180205500300502070f64052400700603040c2d001040700e090707c003060041015200c0006c1c0d458010700d4810b481044c4d0308513403c01c2060390b80075a510320710b84560b59002032000c2e6982014103a200c0c0c0107800000c1c0415281c0040c4404181c0950140e64800005001135180c080990303807408415424018650600c80d00200600604039000c6207190300c10800c0c114004503504202d1410b45a0103011700380c05006007103000080700644500d1100c401c0070300c0a015240169100c1404540f203180d40d000603158070bc032200d283e40310300070325214880c03203120050302500c0f01c20032001d0360200725030340a0b280030f070700c1500103241f840c0c4208250f0096 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 762679928 1250 762678678 762678691
    0x14060313140a0b041401201309090305030f010e071d030f1213060e0d030e0307030c0f321905060a0909050703090b0a090c09020309011e060501090605030702010e06 72
    0x10600b5213040e1604c40340455850030401000e0341480e11071040c40301080c144001c5042c6103540c43e5101c21010001146100f59a8040724419081002d8001456000f10095004023460b42d42d201443e07882e00c0425007071840035101a070000e03a51441a89420140305248070828000a040c0c0700d14000014159190001412054200d040009440c0340a0600854200010122400d0076030300d0b032400800048089803580300c080c044c0800130110300919602071200d2340107190321920f031550f19034a42044110464681c0544603181d0304070030300c40510840002e107280c60000482102d503907894140050065001e03d00c41c80034046150341c1c801140c15502c82c405000020b030a5900c5101061030001840e094a0340900700c1d105040c500801440801c07c5040c0142d84211111004036042c0201d00e0000c17082c0000740d00803116284080144400d003001900311400082c0b2444829209512940d40e040071030fa010b00c101808030b942c2280402089024401840d4401001d000004002c420540c0e07550810b0307000c4505 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 762681178 1250 762679928 762679943
    0xc0901030308090d02010608030318160b0c07050301060311101e030911010f0c0b1902070c0828030813120e13020a14071103030c030a080114060313140a 67
    0x801103840c0f010004c40400c0a403901c0203021040c50321000b56103034440501018a01507144403281031440c0100064004000e02005804085549000e00c144a80101055034000e002d0398100107080c3c941401402c0540703400030074140d15200c00d942082111001c80c0e00c10340c1400a407050702080c102e0143d189402c2401142c40c0800c1d00c00d2035281a21240340307000351850501080a018024641d80103c0c000c802c0e66000001c901c181d01d5040c03600c1c6010078004c3c001641e0500000d0802d0400544a2444e01240c27a40400c980d5001c4404044024410b80e0042c071410a101107803021000c28410b00700d9507080000c0d0642480346101c0ba0f00e941c10184148141f03440441c80541da1000d040c18080d030b0001c1140c0c454481103040000010000341042a80c2d6082880c15002049040a000190000c2d150511004080360742d2010b07000c50b00c07509d940045e1a20004114180000105000c52240c041c400c0000200120701c1d65540c01044800705c1c080945c16110361010001c0c80124040401100300c2580c01640c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 762682428 1250 762681178 762681181
    0x170f0106020708031c180b01030311070b161101180303170603030a0c032124080c030d0c020f060a12051015050a0e10121a0a0b071403040b030105041404150e0c0901030308 75
    0x85403804c1200d512081c0c0046041101318ec442c03192007107000c00d281d8841403034000014054012990200c0c0074a107281c019003090800410035412000c6107661071700d04006141343d940d514041644034042c000c6024041503c1428050000384500c888018540c80d41014060950380c50000c40e003101c00842c085010328806407918122214400305883c000c1011900400e0f9243c4a500401d840341064000750381441880c44907001150380d00007030034906000c0604800d4460001640041c000d520380300300214414504004940a413400c810103400341c1385030701c1d0541102c1070a80d10880e120360041d01d040381000030702c403410320036540c2e1007003071841c1454a0390711841d0010070b9420403001c80e00d034135500c070700ca01e40300c2d5147d2883c580780d082c118030407204840f40740c0380c41c2c06042c14000c0c20203032040180b00c1140000680410004c0000300658180c81040d5410480c001144448030700b066019100a000201440001c5d070510907a6000910000454016103d00d10424808902254000e800c12404a2802c0c030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 762683678 1250 762682428 762682457
    0x15010519180320190b0a0c0f210c03020601270e0708010b0402120c091233040302120a03020706050109021e28170f0106020708031c180b010303 63
    0x1400209412002c542e2522620008013601115048602c0740c00040380c004206529102d01812200d0141c9070001a1840340010501c1c240400203082c05940041081c4002221425441582c6201400742c2c980c0003812264209100c0320441465002e44c0010008210744a0707211282500030304c1444e2114400414240e800c02c04c8550039500f00c000b0032806141b040c402c1072401500501c4c86608441700c051400d43e00c4068001080340c020540c00100d0b0140b1992011288001d500003544140c8424811001400c00202407a00801401a18040c0041e4008030f6041c1460650070010410001142030042c50001d840c3d9503481562400d0b030000303001076400b085030703190b203601d488800c11401c0f0b915644038503100b0074038070700010300c030301284600c41c0c00084081c40804c850041b1254083d840000381139501c3c0e4075007000703800c21a03002401002d0040c002d90314000380d1074400006039000b07400d00c0b00c96070002c0742d1410380017002030501c80b003888520a00e9094103c0400d01c2684c105020b94003e80e114600407002c030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 762684928 1250 762683678 762683723
    0xc0b07051005090d1e05070b010f030203010b060705100506031e030c0607020a1212060f12030f1b1103010f11070c1d01030206030907081c0206150105191803 69
    0x1c010301c600750051811070904a80c49117421a840c1a0b5200700150410041401c88050260b03a00c0180311215aa002051044006100c1c4040700e10031070090002d80f540005012140c081c81100601650025040ba07100710826002140d0140010702241c62904e0810b10011583c405210640031540000450380340100e0700f032108903880300300c41c0002c06459045594800030070113103d12201c1084940080f0114440084d040080105840c241c1400d051383ca0310301c0e440c11813010b490110301160f021070031300c0e903c0360242c3c1c00b2501c51214800c80120021301519040c00300c01405001940c555a00c0084107010b900500c10003d0015005801039220b00c0c60f8601030700c1c2c807881c0b90070203a802c040c1e84855039a5128400c6e0502d042d60f034113494140e16900c1e6014403038030309040c035084034100303004002181400148644101c5d040309096421035402d5141c910b8a2600302155000b080c1c00288204444000c0541c5510110301c25032951078500d200c20340c41074104280445a4000f00c40d040482804d4103042c1481 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 762686178 1250 762684928 762684931
    0x5310603050c03070e010611190303021c06050a14040e100c090909080409020a031b03020d0b1f0f120c0203070b01081c0f02150c070b0c070308070503040c0b07051005 73
    0xa074000c014450a000d010040c1400c148111f40400c00c0c0e0b0300c608104040300303200c0407040160000a04049100c13500c0c010300030f1740041d4a9016850050300c804d00300090507010b4501200c1025048800e02c0d424001079a90f205040e1007856082030712552404103c04007044400036026052500007040400ca0200400000b8142d20aa12280c00c040c05c0b00302043e410411503084411002006960b8117200209401800240da00c008108503275469000b582609900207112040502e4410405880c1c0d02e010848400c44000d0b08904030010041d032880254002e00341c0d1000e03403900b410804030b40070305800458192406800300d000181c00200b0424204040c01c8c00103409052814040c02e074042039102c80e08264200001d00a08100701e160023103140c54000c0c42004032101c50286856171a04d06a0a1a40140d01803413088800702c01d080002030204142c40189d075074450741a503940d203c40e100c50720101e40703a0304050006c0d19200e4036068009101c4424000500c840d92295020b840c20105c2e81f12010100c503030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 762687428 1250 762686178 762686203
    0x61813051b0f031303090302030d1706060f03060d060e03040902090112090308160909020a05090a0608010302030a06020309010f0204140a090e030405130219021e0a0206040531060305 80
    0x5050042c44040b1044106030fa0b400884503208007a1004a403c1c00c0b120b1141c00e900103501406130011240c078407a0312450007d04040c001035003030780303644500d400c1c0303c407034030820441440140c0140701080715403a01c9100d14103414001c0c0790110b0b01000c3e003050f2030b086034850b84c0089803290307002403455150758004980d0a0412025081042102d460791805800f02800810205505001c440c0b4040c85a00640e50320002d04416a01152580c6100c800035015a1003141418441c1088840009003070b440b55220038140c0380d020300074050120050380d41c040650409460303070815540781e18270281100d0651015000822541d103032098242c0d9140300f072205942c12604036248150402c8410400044c0000403101102c006a03100780802c0c0c00e00d444103001307001d21244400348507174240c03071a29051740c000790340c01031000442484290301c45039401c03d551ba80d1b2071180c004c1d0800020301040165140064920780c41d4030304c403e00078640d03201c0504241100c036201204c0140302607a61000b4014418204040c01d01c00d070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 762688678 1250 762687428 762687481
    0x108120f04050d21020a0308060619050a05160818040515010c0f140d3c17010e1008060103020904020609030a0807030305240f06181305 60
    0x560514403440344200e018150080c1c1c40c42c0d0341c00040001d8941c0400d09100d203204103800c070a050b100c009445036180041600003541d00c001040c09440c00104541803d06000140c2031001e03403950080d45c0c1034105100030400d1103402c0c040c40b2540360000c2e05507815984658490b581d03c210080c0322a400540560b089070080c1d152108018003051587c8560900b0030382400c003603020848510304407d10702c0001d2001095145c1414800d601c203000058043d04e20384840c0c075004105070039144003984010420360840e0292001100303141d0034131034182c102c070b04010892a05180080e90740480036800d05080e8007a81000c6c1c400d504000c03610b00c04080fa8006054110064407240d455900024500342c1d02030000791003410300050b104110b650810a141303010703030b00801041e01c405090401500412045615440030f5159905080e01c41a4210380000540c00041c8803083c8074400f0b0341400003940120305060a0810004100782c03480d81c3d1004550300d005041c21000c1100c3c5022101860307140c0c0b48402c5940500d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 762689928 1250 762688678 762688687
    0x80319020c01090306110c1204030308070c050a020907114c050a020c0d02011e0c050703031109061303060e07270b06070302010e12030603070306020c24010812 70
    0x180c0c0e000360f030b010880790030030b1001c80c0340107244100d6a820b00c10840000030358401c0789500c2c070b0011186e0014201310fa000740c4030b40591343c1d100326098411a1311a0401010b076002100c06000520342094001d0b040441071078846030701103d20303211520f040c00c0e00105541c040684101c000d00c0b204846001c00c030321110b41c82c4011260f59241011603104404144e500982c40d200d43c0090070441a56054900c051b181e20b0071602001460040a402814228422084013148640c1c14600000394046c00d0710b548e01c03641d12140b40420b180c80480040c809040303100c1c2d48001c1085100607a64074030004c4c06100034000d5558459920314540641200d10180204036190403a08081100310400c01c42282044101a07a00310302d141015045c500030405071111700c3d13214001292017030503d5815071015007049034207000c4640030440b680390034915000840305960700d0340c0b0010701407000a8240c0c000d0a103c4404d4000c41304016107005c1075010340715050a00720500c0c41074800400c1400e1f4104619800e15a0070a00680703031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 762691178 1250 762689928 762689953
    0x30403210e030d0f02090312030f091c0f090302040e0f16210804050a030f1e230a0b07081012150e030d0f05180102030f010603090203030408010608031902 68
    0x4070b02402c4100124141c3e154610403580d80550111040f05e040241510a0114008c090b4091508107544c41c110304880200002c002440002c5c220240405841e204903070001d0700d5204807203442c90b007a8080c0801604500000060310355006940d07050300d10701d002e402d130328281055162400f024000c00480b0b05040100400a40c04002658200d20b107081000130b10100281c20000114400c2d036000941140b001d000c00010300242c1220420818894103044001400d10031201802c0318a4160181041440c9811007030700292203449050a400340d04140d50711000781d5141c0c0208000111200c201207010401001101c030b929103400700141c8010a511484006ca0381ca801d5842025440382d103d400303607502d02617061254104117440000c40c8022040c01b44413200881140640000d40d02101105c040001c103a54655040c000d4070710030341c80c07120005078507031030a202140074048654041e80c25004c20072010803980000e014903000303003007200d00445c3d032890075080d4201d80c80c00c3c0305500c40441d0003c0a07500e02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 762692428 1250 762691178 762691183
    0x1509020919030804090c1e0f020a0804090203040201110c09010905062b0b011208042c04031d0303070b0c0706020403150b0915031b0118030c0e0f01030f030c0302030708030403210e 79
    0x10444448c5004050105101810b0307250403110304000c1c1590901117070009034a021900118031840c802e9803002d42d500102601c00c1d0f5200c44504650380d20501d10001801107024170b42c4401d0f44071324028220341e4882504c12800d00030810391100c442401001102d11130501117080c2e05140103001150603040e41c00c00c1621035001c80e0250b8024004000d100540ac1c100003842c0c803404041c407801881060220742460301c5c0c0980240c81380482052110002502c0746020328021050710b00c80341e00301340f411401c0e070313109003182c00030344c2c41b40ca130881d082d603428400071010400610142409821580c000654205007400300b2070000d03002400303c0304c4408220840b0a0f01e40300440e1848480c6103002c00c4007425a103580c0140d685911151600701e02c0c00000c0400001c1c00820b002ca82c00b111000c2c41c0c11050381d12031b40c2da060341100d000d00000e00700510407041c000010780300e2840f90103280c0c020310503a0300745201a0f99244080d402542c00358006401c1d84c0814400349405e80c0004c1514507020000c00a40b450b41c0760340c1d038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 762693678 1250 762692428 762692477
    0x130f0803070f050c1c0b090606030d11072c09120702010c02040b09070c0b0a06060c0f05073b39040e191509020919030804090c 56
    0x2045045040800020800c00700f00c03095405034020000712031002e51544405260b00c0c46041940e0040f403820100c7d05200340070440c0e90003414050094101e40c081e0f0702c025100c15107001131034140344c0706020001401a00301d048402103090b080161440c1e4802c501514a00600d014000a0060308800440740e11185010304031144641d084c01d0141d10704032240001401031900c9554140c000310700e14204910f05601c4003200319190711030071440c00c803070f29002d0510b03003128480d000303076000305011121032404078852100c4220050b21940c100d81c449030b240c403451580ca5561140f068400030b200f1400c80e8201040011515032100c5038842800c45207001d9020030b0958207240c0201130090714451a100d4000b01d103994000c82c041c1c56100030303607403a507407035544070801c64003160130030704100c146c48610902c00ca96020f81d0500b0580000c08140043c03c10b03042c0e100961100c1d10a6078030614644803810b002d410045d440c0c2c000c50107405c0090303c4600e40410502640c6041413007008210785c50f0190b10040d07525512070b8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 762694928 1250 762693678 762693683
    0x2391e100c09060923040f09020915030106090509100207080c01020c010204093207230903010b180103060b01050903010c020703030e040b1503090a082205010306320a0b130f080307 79
    0x4503001ea0a442c8900c0108101b81e00070b5040070044081042e081d0140e2f6000303c49140903402003010581c1c941c175a004a41c0c081d20428015003241407907036042c064a801a144e61406060442d1504c0010390b000c034220303131090b401010389940206080010b041c240c0b2442c44d80314180740046072845000300c0910481400c8981103d1a01540c0d40820307409841001c81e408181950b9910701b4070030745560003440498200c036503060710035800c000982045080c4a40c0c2c00480a503010020100c1ea420356a450000d014511242d0381040000c0c44030907169038090007201400d2489401030041e40b07003175050080608080004490080741003400044083d2508401d10303c010000d218056160b49441503041d0604132004405403540002140c20348451204940c3c41740d080b140c4010150409640d0001581603501c54425100c1d01382028004100044942840000c000300100072034440d1001000012070350401d44d00100a0020003041034a54002c4148880c0043c0450b0400080c94601e0f0007010f80c0d49200d40e4200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 762696178 1250 762694928 762694931
    0x60f040905010b0d1109180613020301092103150b0405130b060403080307030e0a030f0c0c05040c120f061514090402391e100c0906092304 61
    0x48001e01c0020751058125403402072540740c1440342e07400c201e035802c00305031035042c851100e04c004502e0000820880c0703555001c3c0c910141409130364046e00f09800c241c441e5030a0b41c04d5500da01c0b140c000524050280021008500c0c160f884582040000034100d403c0c888508503e244a00c01c2030050050080c107841c1140c0e011641d4040c1442c08074a0400640200c001140d00414041008001c001e0030708040c6210700070580e0b04000e0043c480c0742050303564801140145c0800c2d280300b050070f09a4071601d140c1d1680790007000c05188181d5110045021035610041c600c0001d1a090b240540c03080d50740c05141440b5130f1801d800d00800d0304195203d644455110428002d00080140682000c40000d05440a40c40c000b84210344640e0200c41e200c0340b110b440018a200144a80040907040348031903a400b4554000a0040450b002d840b5003110241d440d626004440b40f003250101903c078052400380c030382c110701b103951000e070001d1600e0300142c000501034000e40740003140d111001141c00920f0340a0b014841c0111030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 762697428 1250 762696178 762696191
    0x1080618010213141c110f0d1a0a0b010203030c2209020c281211010e010207050f0c1f1d101808030a08061002030c1501031a060f04 58
    0x94580c02071065825442c2c08000b841c030006016401544c9140240c0c00c00da4090401d83e10b030611404100f520740900600144010341c14800c2414a80710b403610401c2d01600101482405840e41d0200f2a04050001c0051000a040005111050080c4007851030280011070a500f068080c07056507000d0950f801c2d01295a00090703051742c161040f181401001050000c540c1d030308048002c681c42d80c0903400d21104e400060440c400b0b54201c11410303210180d801611810140c090884110b80f2043e001c100d0b04220b42d00e4994001440000780300900401e07104074003c1844004200c103503801c2030500c03445c061140c400f140740105440788000d41c05160380782134034100344d9102c0e064001c0003003d1403c0014a407c20760311014490003681000342c62000a03d00404914201e030b603420047c0e545e11410340d0b0130700000c0300d40c0e0200d2094244485003040c00c0c1d03068019203092a8524695070714040f202042c1e8044007243d80010014001d580c1800d00020214860300d1404c2e00c0c0c100c01050b110001110124000c03540e0f82d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 762698678 1250 762697428 762697471
    0x30614060c070e040f03020606150913020421120305160c1a01060302120c270f0607081b030301030c0e0406110d0b010e041b0c080c030a0f08060405010806 68
    0x70410000d400c21914503d0542850f007498005002022802c8000d446504c0104c5c0481c40e180f04c480d0b0410801650662914010790107120041c01410a0780140740d07002d00000c105018220207052400c11340840c14150a03865042ca096001181d594940a05103800b0038490081c0850141c001114424286022800b03568035051100c028802c0003241607911080c008130301d0f194560001c1101c820200081d10b025261039844003810302ca01d25104030240d80301003401555030300104080601d200001d00e070501da510804003083d0300b644000750450f4130840c0021208881d4002080c22521144030100850a540c15a545c12900780c034503000d00c0e103099003090001010403c00c4d40090703a034071240303600060f01c0321300c50111a0081c010203d0710301e0224001400d00d5001d070031706200d10354000c1e1031600f1004d0700c0c010030309040e01c6500070b2032030554000100300040c1c01c0e21007081004000500c6248d84d05d041e94a00c50100416004029021520a0381480700400440da40001c4050f08007900c603541424420001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 762699928 1250 762698678 762698683
    0xb1c02060301271401060809070b04090f06090e060708010608010e01050f0f030d0305220c091d01021909090905060103230601030b01030303050f0903031f0b13030203010c030614060c 80
    0x181c0505250b810481c90000314600c00304c1c064122030381c80e243c0e5000340d114100107946039500380c0507800c004001803008000207020343c0c2040407595a4102c00180103501d454603802928902c000c074413100d40c8100c0c28403000ca1740c020002401040285880c207501d5041102114455506101e103500c203125105044115950b076040001ca0400010200c45042441243c040c01410040360400c1070000c07015802d6680380d40d01c0c2902002c0d568445c800310407144c2001c94072001070081901c0b654082e5403200b0b5070b1805c14400d2000b0704280d2045c45400b00d5114007440c008103986010b402c004803060602c2e2000c0c0004d00300285241c1582d0307200d1086180c0401c1480c1c21841d88050080035142445580c000100b170085030300c0d559042c0da003c1d540601941d6600050b22540c03540c280e031450001e90040000481a202c41a0355160319085000904541340d52040180d10642012040c020101e8403107004004500d000d00c140f2442c007040341070134001149043d00742503034070303402d490581d0040d1000100640072103400d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 762701178 1250 762699928 762699989
    0x311060412050a1215080c01030e0a0b0408121e061f0f14040e010305010f0504050a030c061b020d0f0206011d04110904050318034c0b1c02060301 64
    0x42c01002c00100c011009070f104d00300f61521401201c7d005900030507900e54400e02803208030242a800504d5400440d60398400c420500030010340d0841014032030300901c04d40710501e0300e014072100040704003141c0c244543e031400c140003c1d02c81c0d8400d440224402c03200724410a2404926203035400d00402441c44050103a548154055621100c00c0307002030040703106200b003401c2d41d050f24020002004900c02d041403180031a84c003550003400507884040510002841369a81a91480c0f14410129a400403090800b0340620045035201c09600000004e004035a4002900100401544010b024551400c81039603904030640e41d5401d44200990005070910082d90020002c580016080029518242c186652290048020304808143d20911855a454001038002d400c1514140a402d00090302035210540540c2c4031781106a8084880c007075090340202580c80400e07078510b0704003142c090b08007400c011100c010410700d0500744550841c2000562a60f03001d503415180d101100790404401400200c40ca00c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 762702428 1250 762701178 762701207
    0x20a090b0a0504231b0405131803080718030809011d03030403081c1a0409051603031206060914100215070c1406091b01030b09010902070311060412050a 67
    0x3440070034a842c0401c201009266401c81c46400c9141e245c80c040501c21074501003c0010840e024401481545860708041c12441d640c4400050010001000d54a03411400b00d019404640d00a0800c0b08054000a2980c103200c078150b0304d40d558030f00315981ea8920380201c5000c1070421084100035001948200508416124010126620f441c0d41c0d241a003441e5101000c58620510303405029035850030503000d0250301001121190301c405141400f80802068030700d400380c0715403040116182240750340c14510740c0a907029070b90b0001140103041d60031041e141d460303000200b040300c103a204010003102d40c6c040302c40400084481201d03110080c10100d10341584039140c0300c114110202840651a04041c1a1102911500c0014180e000d41ea28403622200308940740c50450700406558180140001141442c2352014140040c00400c041d02080c0e48003800d8220200c0d01d035000a541051581000400c1c800c000014000c002e2440d01d85d403032218002c034501c401d80c02c2c45004210b146001d801400792480781c50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 762703678 1250 762702428 762702431
    0x250e0d110f060c010507030e0d020d18030803040c090b0109030203120901050c0304091a09090a240f02030a270b15060d0209010908060106051605030c06160e0607020a090b0a0504 78
    0x2031083c0444c1c0200f4003a6840c8000c6880d0125004400318041901041050303e0b030080c008450043c48140c807403001caa00d540d0303071403000e041c0e000c00051380c0c01c40914040c60240d050188142d040c00e1448046070f00c810101414090085410801a5170000755050b074800c4030005103894060520040c0c410f8001d0700441c0786240000710700803034421803a5011101c903603059404084a400103409004409405a038050321681140041e00003041964a40e8460a541810035040c6000122045030480d11101d0031000016000428003d03207180d00e028192402001c000c81d0007505000350f220ba0f80324001c20304003c00e070304003d4001a0301e1039948552001880c1c0054030141d034070680819824001d600c111182804903410740d40104540d940021054107983c10340c3ca03500e281501e04107010404201c11074084031184010050042a81700c04c2c00028010100da80c5a40001d038103100002d00403091016040c1d020324001c1c0310b20005a901c1c481c1a008881e10360a00180000c01c03040843c0e0403244d03c1d085280c005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 762704928 1250 762703678 762703687
    0xc030f0d0e0f0610050a0b0904150305061005040b04020412020d030302070b011517060109120f082206032306210708151e070c0b250e0d110f06 63
    0x80d030010400620503c84d10040d00d121503100d404100d082c041c81c3c00b91611181040c441048581010b1380030380c44c600030101c13481000036980d030744861410308115540c103030000ca84002040207052a00035000343d68411107041d41420304100c01e14440e00013680020344612440c002034410700d8000e03811540d84503040040c0310841d60b100c0500c0404402c0d8405840c00048540100400a400f00c3d03c00d00d0043d981651001e50151600d03004040c0f14100350300c240c50700c11091000900041e0400010b000d80780c000c040c101c20030703c4030600351005241d8607800302050608001514a80b4000c0c1c5a050480305080d0384d0500d4075855000100da0441642401c0360a030115102c41d2910004000442d10106d6200000b141c00021856401c000c080d9070a440b002c40320900342c0c00e101298469108a40d51244185c41c11203814001611241c00407041911104100780b010311142c0031044c0c80b414000810b00203420201030026a4102240d1030030107082c2c0140001c4030b00c050020f420390300c10000300020940200520b449 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 762706178 1250 762704928 762704953
    0x1902211318090b1f0308130e18010c0908030703200307032109030203160602091017060109051e0a18020d0501080c01020d0f0903080406030b04110c030f0d0e 69
    0x1020150000c2d510b00b298840080d41495418907030444c202c0304c03003400c81090761450f0740c0c0b0086a0071092401e8000501e5090100f40d130750140219511a00d1000c880000c0400e85400392421103a1104100d000c0048000d010320100030000b080310b0b070301549440c1410038808126405020a0340c41c104900103408006a03074424941e209441c05444019801000c12061000131071408a6504020007800750b003041c0814060f0900c050003082406000c7c1c0000f625002a5030700207002c0400c84001c03080407500201d041c0c0c0700f40d5550303036811703030f0000d020700300044c0c80340c18080022081081d8903024103104074500355407030241e01c50006031401010040c010108001252011401940040141c404c1081c03401000141360900044d041c0342c048410380140c030000c6001c3c082141d52800c1115030314140402e100000000a40703020052000f490140d8002844a8880c0100010b9030446581d19060420510000f110301401008450303104030300c10b42855543d1529088200980f0380311080c20141d0281d00710040c803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 762707428 1250 762706178 762706181
    0xc09060d020918271c180e0705030103020f01021c050d0f0b0f010503070e0d032d120f090c0803120a110a0f0c020d0303021902211318 59
    0x30340036080711900d10b10a110403000030541412103031404e00328201d80101c071150a40408000c00d02c030401c819240d00d41c5c8085e40e14051049201007501c00a6032140503114202c1d80d60035080003a140c0703080620316604002d03030001c1482c001800081d20490950b403c0c0c49440c0c1c000c00004444170745e0819584034501d40341d13501a00582084c1e2412011909101c1840c004614500c0380000d034520041007c802c2c0007240c0011107040e000140501d0601a0307a9a041046954500c00303401c00d0b0b072003640ca11440c0e0910700c082502d0b004042002001110350004d5a100d0250031903e060340d0150410f1001680401d21414200508907d48018000000314200440c40440102c010a4207841e0b480c0d90400546807910641c040b280f00c8140c03403010384018004070740400d12511440b141d010344da00d0202e501e0102c42d0009045299881c104070007103640002c1071b10303807440076150083c0c142040e40041c100d1150b002141324a80d10304115074166940000840c0e804425401000380c028010401114008035881c400560 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 762708678 1250 762707428 762707437
    0x606130c200114250305010302060f0f130803030a060e10060302031e0408090406050a0621060305150f0115080a0b04060f06050a03051506090906011e03140108060f0c030c09060d02 79
    0x400c0f000022141016130f40c06405407904803035001d0540c0b803414001000102c3c09400800303803400390640c20000910b25411103c80718016180c035102650380c074100b010381001260b140c0c0d40812988500d1500300304030140310358a128202d80c034500300940e0700d035a40812040d00581018103141418030050500090008446c080c5c44405c030151001c001c0e4039160400c0124038042da10500d800102c5034505141d2050801c0c6400200300390b40040414030302c0c0c0741d54840d4249090070200740b0710504141d0401000305a061032907401001c003211444890040058014001c0710018211000151940d03000e8056480302c0d4800801070121420603881d103622480014081e500241c1444002401c0001043c04000404000410400004c154900d0035205d00207025500c00000d180c1414450050040c2451003404000110640600d64000071100d14460b104070307100e901070700100340740e900440821148070300c042d994079006030502d1151600d0b0340c1c40711311034000c0307108182c513031034105502003204403500800b0780152 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 762709928 1250 762708678 762708721
    0x40606080a11180c03010306110d061d0a0b030a030c1e03020616030b0a0603050702160807030507090b010e15070807030314130b15040605040c020606130c200114 71
    0x394414400d11843d9040860507222035512100070001000010243d0b406100d004c5c42c460b10796800c108070504a8822607249610841d02040c0b001e01c000f800d521044e401c1a03016040c031000700003004180c4d001c04d42c1c5145010b8001c0c14003401002820601c01c02d5040700010620f60020840ca0342d1481c41c00944410054a4006a82d0031015880d03480074081c0c0260300c1c0800000d88071180152510300c0c1100902006803102e0705500980c140310703001c2003800e075241c030203404417030020181ca901d1131a02c203140083c190311105c00e0929158010301e16a1b8400e04c10a04014101c401c00d007001c82542e6500001d100b952402484c01c0383c0007030000100340d01a0841102e10340b0a10a004c43c680d00d2a10340e052450b6a62001010405064001040781a824044290355030014000040e203640740e0020504032a503003007260026a1140c4100945458900884080e01c844050107000301c4546000240c6204d1400c07502880c0d00e4400f20f017220100c0d10952181d0054240c1c40208082810143c103000000c0c1391800d100c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 762711178 1250 762709928 762709939
    0x24090e280213060302060d090303140103260f030a11040b0a0e040e0c0a0b03070e0d0b041211120307030b090a0903090b1206040e0f0604060b090f1e040606080a11 71
    0x5941c2c9500151080030b080340c2d0041c01d443c1c640802804400020801c0b0641101416614042810880d00700381c107090103184580048040d111601603610310060413800c0f144080803042040007100300080f010b4a8009414540100b200340c503d4540e0071032030103650041810604c01007032202005510030704280441c031091340e0401500002c0042541c5542c05030394041e4101104450411500400c8801564045150700d01680e107030781010700050600c202c504064811424100c10300090041808461940c0441400c2101030060b42e0340b1201d0316442c250075080300c0303110003200299043c0d0107034200a4403c00010264852480c0c032045620060154903000c1e0b0014a0406002c500701058030111801201441c3c0600074a584090401018000c51002c61600340600c01420721484401c1284900903445000041661041070086c00a007034001070240da00b8110301002d220805000420300e20070074640f204840815a285c1c00c00502034900d55104443c907102e598948000d016100c801ca14010004464 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 762712428 1250 762711178 762711199
    0x50d1a0c031b040605090907020f030705010e0709020307090b03041a04060507030b06181c050601030b0114030a03051801090b0f090f0d0b01060f0309060204060309030324090e2802 79
    0x145540140c0c0151340124100708442e41d001d240c06c07102c4a50001c0d292044909200d01b0143e058115041903a04503016911145000d0400d1000d0000310064030390100c0841c2140f6105000070131038545442001c01c003010000208061090301180c0440c4811004200700c0c0a040524254008090031641d40000034a81000f0200d5841c01e001100c0c0d00b00780c0e1680b01180b85e40120100262040c000b05000c0c484041e0581d4280000e00c1401414004c500419800c82258900503000e8a040da000c8101803103a0400014500000d4100007a0780e802c80700c06440f41201d540c0c140041e19000c860360444e80c0803d0011a0104c1c600851200810481e9000e8814111411001c0b00303000e420350f105000203709009072401400014822501070204040e10b140c041101a0b29407155070032648982c0009c3c0002e03895003400c80500da058007611842d056100c0c4d0a1011004c107000b00846040d843c0a1603981d243c40e001c00ca03440759410440100500940c18556898184807021460040c1503001c0c200e001e88002c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 762713678 1250 762712428 762712471
    0x6041113060308041703071a07200604060e0313080c030d08130201051c09030f112407140c070e0105090c0703050912010e0606091f050d1a0c03 63
    0x20981101d0f80b00040b10705082c10003d0100d075008880e09024110b00c414000392002c6100501c5000700007805880404c1d160804503c01404140e1400303030000c69012410f00078a901c0e00010b00319622a401072000071b5030b51a803148803400c40c4255203024030380301020200404c442e940841c00d1428643e00b201102e010905503242a5011082114681451401ca103903901c05940144002d003070010803210f00b0110b00124810b40400c0703809440d01580020241c52980e141d854018040c04405e8000c0001010a020318841283d03402e21143c50340c0480c00310002c003080c0218041d6044844000040d00f030039484424000081e540c50361248031b9507181e2a8540c000040c030f0301380044050300540c09040c041d0724082064a0545080d40501851500000d4804103410300e040300303101e21007150035040301514150400750304000e031484025001c0804006000d41212002e51100c44c0c0744200c841c165203802e5140c00d1401e068400300040b5054585880c201010420703d49603804c0103501c00c108000f07440e0380802000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 762714928 1250 762713678 762713681
    0x11010c0c0b280201110412020a0308030408070201021209060d1e0617160f0e04031806030903170601170429090d050406050a05030901110a05070605130f02120f06041113 74
    0x2201c4132204100c100000d0080c0c100e1f00c82c1520350f050020b00501c420a50b84d40d511140303580125420341307002d10042114002c647e81401060084070941d24030f41c0c10090034200060852054064102e480c680d9001c4001c1c145549086031040d50450ba00304020540e074648400c5052454060b98440398020700f00700009070824402004144e580304d0802032405414840c450f541000d000c2d20039414014001044c070342c0c60520324086c4000c1d082c0c80e036010a5850280c0b5019040e8103151951303042844441c42000481d99220070741c1140503010200183c0140c07100c0c10312042102081c000a02d0300c021014140301e18900d12010640211079a07000c64032054003100e005c45460140b4015640003c604100021400b481040996040281d800c0001115803840c84260040d91003042c403030010a0021840f50309201c00d40c4100799015120088078408441c2c180d8513400b040607114002845000c0c1001802c600507000c02070085a0710604d005c0380d041d41000e05007060022038200c00c03c1d00c282050a03260140c001d15 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 762716178 1250 762714928 762714941
    0x6110705011b02060705031003051b130b0f010c06090605090a020a080102041a03040201110706080604141e0c0c0703030503010333020903031201032d11010c0c0b280201 74
    0x22903015003041e840e0460100c40c0e9034400380c0102c1c0120b108c0e007004004101c041c042203081d610740d5280405820302250034003840c00e14840603800d82c00e241140f0b90102d910752800081084078246011441801240340c40001042002d1010304000d10348420000409400500c542c0c00794000c03560886000da594403820300781e02c194010355002100030440b00340b6010a0f000070b1604244141401082c03140d4525034285000c02a03405035000607420000c2c001d0508082c492404480c1620519100602e4004000355a0f603021013060082a901300340000e4501c9100c1058556407060360045d00c0c1d030036680c1d05005019400a005c00c3e0f400144c0701e50891424440306080a40d15081c504140741ea0004450043c402500b00003105500b42c003040145d04c60070f007031514811f406948214800c0b10031144c58500c0041c0d040124464049034007420034040007050035040d8880e5411000d1030b0003542c03540e0743d182200d0305040e80e03400443e90803004690b90041c44a0410121918101c00043c802c0130f201400080b400d032041c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 762717428 1250 762716178 762716231
    0x4090605030f070e060d080a09230d0b041b0e04060510060c020f060c070b071505010315050907090228030b0d0308090f0d0f270e0a06030611070501 65
    0xf066000300000b9980d82e4105900c440c0c010701c0b2001e0b25645480c2d15030190f2090030301c00000b4400fa4014032009501415406603c2c20314000380ea0f800c03001c5800f00341c06417040c071307400360034807004000107000c0044c0c0d2180119038988600d50620141e03910020350b08000801e8800300c80e641d0800000494a010b554011400c40d01641c1c3c40c820031f45265028070020210400c280d03900524100b040e242c60110070009040100220020740f965460b560074040301d001c0302c80c00954151400e110040010800398901c0512000d01d0940001d03180d112034074410f140c03003480e5105080e00c0380041100001003481000030b5400900580c007a000b00304030500214120380c0c030407803c20341c4030180c01c1404001c0303441b400d00746a201c002c480072506e44680350072009203001180d201c2800012146104c0306c0e8410f50000d40030803511880134a00c020101030070040c24102216000c0c0414124100300040c4141c41c403034002c3d50040d41c1144040010060582901d001a40040c805a60641c01c0580c000c0079404041c003030045085 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 762718678 1250 762717428 762717433
    0x9060603050f0a1d030c1f0e1c0504080a0b04020103050604111b0c0406080d0207080c0a211b0911030f060d0f0b0a021305040902030a0b1f0b04090605030f 68
    0x50340c28100b50014803810505058009504d00502440f01c810002040400e060000500d964450076040440710001411455511820050078001e24500003c0385c9903180341f400c00c001e9054100030011610f5000e507a1000b000341c030500d0125814400c20448140c05a03000f033342c062211795541800e0001342d800005030b40c400c1170010480d0141605500014480b607591040a44640344c854000160607902103070800d0340940c01c091103a210046d01002407600414540c4064040001d4540000b500c0120a02c1501c04040400b002811805440e0004000c00c03a8054812242141007040b00e20001e103042c01420300803490a50440c291220300000e484c402e01c0b80c1200e482542e83e500c801d10488100b82c0d0402c460407010034a000d80020b00807040c483c8540c2d0500030050306c0c1c0b20110015400c161940e84054051842c1c0a0304034003580300400c1444075180c000b10004103d440c2c9031408840d80164074a1620300102244000c200700c0501d00c0100308442d0703119803e11a00e601c42003059101c641e0a40002c0301076 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 762719928 1250 762718678 762718681
    0x30621060604051b03010806010801050612060c070c03060e1e031201140420070201020c090606030a0504140d050409061401081605090405041a09062802040f0f09060603050f 76
    0x516043d008543d0048850080c206103803400d10680d032a94000381c000d003419401c54401400781e68402d2048035404070040f9134039040c1c490b28820740c64407203001820305510003000040c6103081c81607a5940714010746e4442c9040002c403215544440e12030841d807059200c503c0e10944129035905001055984140b603408420445901c1c1003d851083c0501c1050301d6041a200da030350b250902000c00c3c03040120391903ca07182d81d0301d0900f840028103141e11510054483c5508006200315601c035041034a51080031f882e00010a603c1e5400d102d02d200c0e258521900c02440354420503464540d00c403025004880024800748400c94849030080a01a00008010700203400030300014a6501d50400c0c2c00f145400a043c09842c3c04035140c00b10b000c1d540c04480c1995003851007046012140560620b0340e0307020070524003624807030504850409913450088040f44000300340020b001800b200b143d04440080140040300c804860b40c074281c44147c0b00d144c0c82241c010b64070301a000a8110301a006881c80f0307100f10706041c40a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 762721178 1250 762719928 762719941
    0x11010309170c0a12200f10020c16030b010608010803030403170402030f0d02031c0216080a03150f170708030f0a020f15071706010c0206070821010807080c061b0a05010207060203062106 81
    0x94001c9c400380f00032480760050f4102401a4000e038400a18041c4035207a400750306241000c0c105a0044c0c2c09240e1a60041040102096008504183c8440c0d06040c10501c3e442d5800000c0c0b030060741c11082925806405031505c04141c0010050108200c5c14101881d6240303513540143c22030140011303a14101080c030304401c2c0011075410060101c2e000d1401c00060a40c502d86280c003900415800541302c03030ba1045420b10020041200b00c1c02d0800c03ca50082c69403038200004d050320303400342c2441c0c2c4a2a0382e020501c03074000303070084c03008000812000044542c2100d0446200b801c4400c02e82c0d201e0b0114502115110b9189060007100707225150684a852018442c1e40c03e1144550041d041030340d02c0760092014004580c040e0390201c1c00c00d180070744100302c65410450f00b01d080845582c0255101d51003010021515100d020030f882210000c40315007140f0039107103100c150802400b10302c020a25480000c0718010441c1540c081d6000780c5003a41d16a00c0404c01704003206401a145048503480c0d0b00c0040040c02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 762722428 1250 762721178 762721181
    0x18050d08090f01050108012702010e040f020405091303110f0c0112110c01060302130204050f120f0d05040e0c03090303161803050a11010309170c0a12200f10 69
    0x821011001c00c603060207949000c81421288280c024852a9454408043d14100012501c042650a149010b61540502e0780042c4c00c502c8824180390162740c40300c40b4994061615030544005000261810b42c00b0300d4401130800c0d4000081004a0100e0301074616147c0c2c034034001a09660402000d07004101000b00c290054603500688d4800140d00e40d12102c0c11100e0040c81d40207030104005200020661a046104000c0d840f0b144618064001740706120803c40e0303584401841c00c14070300544440c1d07285c1c0102c41000c1d0600d164580c07281145e216030a0801c01250b8818000d10485000e560030800a81391142d41c1113241c442541c00d003140c0d50092001c06c21581401080841d041040e04100340f203064214170f11408030216502c00d40307880d00a6402c003070600070340f08600203610300b09180c2000112010740c0c48a070306030a085d912401d8084040340c810b032140010440c080850b5085400c005610205000081a5281d01180c1255103841001152202000004c1c40482460385030050003005c2ca2070080ea20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 762723678 1250 762722428 762722431
    0xf020a120b030a06060303050909090606030706050903070915080601060305041502090d05060108030d0e070f15020c060409050411030604031d150d0b1c03080606030a02120108030d18050d08 83
    0x282e15001c3c4071010b0b00003400a1060400030740c4a9151552540d100504210524400500d0f00e8400c0d00180c0400c0403955003c107000040c3c0e070340c03030900307507160741401011900d40070058006001c0c13540ba1004102240b1815107021081b540722600f2584280c0e00c4032801c40075038405490051050030150000b4095894903009018004409045804000505c1d11105d14214003a0700c0004141c00000d801704c0300c03090b00d01409001103000401003000d02d00c0c00740d03a00c020310920310400c1421100c0200703000180e84244021503420703500518194645444503080c000030401510201d51590b80c0c000440800c1c100030540c24426901911041001d824406c03009062070303020001d03194070038020b8681e4a102041d01e00a070079922498100042c0340ca00c09028001403062004034082e1401400380321600281c1c0c000440b070342c080f9007540d195481e5112000c65a0190088007021020068018000b00380c250b400005007480309880300e800c1c40812407440d51071030b00c0660750700e0107446030b008607100304440c03402110040e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 762724928 1250 762723678 762723701
    0x30c07020d0204060e06030d0306150810090207060f0b010206071706270907050a0b1c09120305090d05040b070b070e030a0b010302030c04020a0f030b04110406080a0f020a12 76
    0x981d035518a0354000380882e81c4c240c00401c40600000d05000d8281030030030840300000101e00302040f1181c1080b008010700c4100030010800c00607020002020080b515102000a0124040c25519144207113006006002c90b1180e0901061804c6a2456290320001d03900d8082c0c030380e50312a0707c825140e22072807640707085001f40b0880e00b00080c08446013400701403140900e601000c014420000e801d1108045040094503841584504103659080c8620070303145084131801e907812041021801d80300310022015211040000d0311030075407606080340342034054108510a060003811343d0844541c4030400d8130140910b00a118650605000c1d480004a14072080c03038000449081c40b200d0006010006450041184021100d0214000040085050401c00b600541c032044030198100600c100d40102a800241e82806c02c03d900c8485541c0b442e00c1d103500000c8541c0c80c50040a5889468441c083c080c81c1e8191400c251040c60b049154514408074405c0c2ca401ca10103580e030300b5032105102e501300c02900c19414070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 762726178 1250 762724928 762724939
    0x706020307060c0801061b110d0f020a05030a0209070503060a030f0f1a0106020703061a15040f06030b09160e120706020717060c0d020d06090f0c0f020d05210702010605150708030c0702 81
    0x1c0c23144982c0c561100c11001403043d81c1414484c20684144070342069160320180c080e9101c040128010303603808691683c810894505540c4a660b20380020b811407031154000360011580441850501c00c010001c000c2550207044100a130420b20001c04100190074462400107802684003880026041c0c1c12052108211110b0003c0f040042c00c00140c0400c0340c14030a030071a05002404004a0b00c003688640d0003840542000c105602c035407008a0302004009200528ad00181419240c42a005613220740c00850040c1141101c05d105052242d078940180c010100544075000001441450780c899185c2081d10400c00307003500e6155454500e840d07030003c144042c10309809107c0c1c400d1701e0410b4030402d0020511200b01084101c1001840c40c105c88a0b0103d4038204146400d010320002e030001071040041c0329620300755a59038030740c2c80c2110510728258550031901d03010409100d0020350540100b415a07004440c221160801c40c1d00c0d1007102c5c480d85000800c4a0300500001d40ba0b1070078080644295400500f4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 762727428 1250 762726178 762726203
    0x1020a020f0114120112051902180c0d0f020406201e120706020414040506090f0705070204020301030606210b0c0706062403110c060a020304140706020307060c0801061b 74
    0x13219a9064002d80103000f40708440c4000d2400d21404014005403900789102014000b50310b500807464030140c40781d44221081ca0400811706000856080b51845010741400300200041c06a691000c0d50240c440e00000502d4500544039540300e01100d4854000c001008207006107880d1685240c0b200c0c252201c1145020301181c0041c2c000003030000300903c2d845001c00680da1800d003446c24001d050099881c9000e2441d1804011749510303030760101c80e009010100c0341d140690343d035981110107104110000b500f242c00803000008100d901c3e0002300680d481001080c0f0558030a40d681c808134240c80002070a050030580214482c91034110040110310700440b0080b603241d440e01444c0060701e10400141008800051000c1c4074998184116098000c855640074501100100020b9490102a00705403400da80000418100410b24040300d2500e0303a0b400c140d82256070740b154080c2d201c0e00305c0c9200342c0d00d00703007041c2c01500130902c40d0103954183c07402c1d500c0c0d20760816002000460201d072611421140101c2d0b020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 762728678 1250 762727428 762727447
    0x70e130b030f0d02010f050f04050a03030509010b13050a05071404060c0c09020a1d010f0e0402180301140106030b0a030b0c1605010612050c0909070b160f2001020a020f0114 76
    0x40300c2c0d4610f100a40001c90000d03200740001c0c04446005003885620780c100c009000001d000420040701803509854041543d46030b060140303004150340110241c1c8850b880c0400020380b05150000c0380308407065417041105560340c007800d5410f0301e110381d00f00305428030400040c03100d103026800d900c1d03425004010b40e0243c1500c501401040364031500316007022803c0e81e10304c807810900f0b2a00248201c042840c2601c01d520180d013007c1d00000030150741520854010130342c0c41d054044611102001307100203000b4850009031414104440304203002d141c001038103003c0804400e041c81404a070407070303911501c10440c83d540c203403c0c440d4682080c0c01001d12010403900303000c0441d1007406200b000d8a0900d00d010b840b403146140141c03601e0703c10301d8201d008810103020040410300c007140400031120501c5d0342b199100741c10070380c000c5001421795004020403181c860400074072034010103e00342460030881d038400800c5103600680e640d00108100030340c08102042800e5081d449199495140016a01c1e2079040c05c8400c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 762729928 1250 762728678 762728683
    0x9040504030e10020a08190e06070b16140f1602090103110a050a0b0f0c0304090c030c1101140a0f18140607050f0a0513050904110306070e130b030f 65
    0x544081d800600c9118030006940383c0445000e0799910703140000c2404028950f2082514003440c40807101140b000d0100000b03481c00b43d40b14034101c4a000b800160307a1800e030b1502d0091440203031540540a1201900d12408500070902805a400c48200d841d0500e031806061445640c0f103040d80309001e800c140408030058680901c07150196211786510301c030341e0504005000000100b41e100c948180601c1904011100030b28003140c400c40c810560266aa080c01d100241c40c3d071160f0342c03001e48040d1400f800c11414130380c168400c21a038444c0740d50340403a01c1700700e90209013070b5600001d60050f009860004590b4041580d031040c1031088400e00007055181c943c422010310300c040c040d0107917000e00c4480785aa145c0c0c00d080c0f00465110541d0700b065802c054104100c482d51b0300030103411344140040003d0801c003a0540d1000b000c01494011705040c0c01d407525140101100058019690084c850180401d61084c0102444000039001402c00c1020207503003846440074024016006806024947c44850700e40c406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 762731178 1250 762729928 762729931
    0x708040e040f14190615050d03050c011d1c031b02070302030d2606060d0617100b010512060a050a0605131a0712020c1f080c03060a0515090405 63
    0x340341c2d20a95115500f0152980211205103082c50342040d00141810140420110b4849410020000d40c9410390342200d0354101d950340019500100c019040b40416500c400184101c4441200900c003010f9100280c4e03802c021000890110f41c2c2260401c004005500a9951180c10716450013080502030518500400d5004001c03540041e0001324007031043d42010001441c5c0c0b1100780c81c2c02038850a04a50720410f0280441c0f803c1c1181001001061041c1c2e503960540b84500e007011010030040e552840d4001503403030071543e0002c0b940204080c0407100b034418032541c1c1915506840e01031600c00c00204001042000411480c0e01070030308031000c21203441d940401c0000d80f10f503464042e5a001402480e10300322036150b01018440c100601c01040c81402c8009079001d183c0d00c40d81a64230380c0d082140990400c142144a2508041d4440c0a803901d207000a44615800a007502c41a00d2030320303011030954241c4800c55aa0f500b024a04808100301e0408541c5524030542160f034040c01c01c04c1d10400141941c50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 762732428 1250 762731178 762731183
    0x9020406080102071106040807060f0c1a0402100f0504050d0302010f1103061f09051002030c010509030910080f040807020d06060303051c230a15090e060f0103080d020708040e04 78
    0x50104040c010017285003210380140c0300c12106541407034501a1a2503841d04940516410001c0c0007507001c000c03600034482111103030707441403a0300302d54103510604c0c0c03d101008a409034032403000b07490f48902060041031809102c040a0351441d290504100501c40b00c83e4a00c041101199600d6420706070034030b0b051003100040c40c230310003502d9503a040100401c400010107180141160b000480003000d580d8004030030f101210f80949203c001c0805880c016030646c0120304110742e040d420b0074200b100440b000b000818241d60112604505c40090310350442e043c01d8200c1d80206070181c9440801c2c003042c949805402014801480071146025603961032081e100b03103078011404514081404106408116501c0a0091905904118052050710326115050b10700041070041102040407485200007500000d070805400406101034583e030781c000e04000d01e00750f489003509026806c00301c2c1903218070780d8840d4102c0740c00026850810800e0b99100c0000e52020400b01c0d1700402c2080005450458102494840ca0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 762733678 1250 762732428 762732431
    0x3040806071119060f0e0307060603060e0102070b0f1305070b03040302010c141c0b1206041505010e2d0a0e0f060717090f060405071a0708040b0c01090204060801 71
    0x28140000b410301c080c114200d268035046550094210512221018032942d0000310214804a090050038000d00d4289141031a600002034100144204d503005002141d118000c20400c070f20180044a08034018038400410080c000b80215448580d4440c00542108000920001401140d6502171501c1c4103507000e01212880402000113041d020310400040b0030313840c208403130841642c1e0303100082882100c614000c42c10021542542050a990021001400180003441a18000c0d0300955490004036401c41c1d090b6060849540c802c099802082d0488814149094054451400615404401c00010010f450020004101e07544002803810300414034800b0025070001001c000350300341016083d401c043c13540b000080c402d0036584800d08c49000c0030030300e5229040f07031260b648648c2080b00360300c4100f02a100b54402d000500c6004601d0301d00712500c11109a440e0030348031040032020f0003507040c041d201480c03d2008001d0841d10100070401e0303814a80c000100460103500143c1107501a80041c40031b40e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 762734928 1250 762733678 762733681
    0x41203020c01020d05031323030702040f1406283203060a02090406080105010e0f07080f060103020d090b07021b090108070506070c030c0803091507030c12020a0503040806 75
    0x50301488031248140c400c0c03014142024034404c000e0000e1002a04640390070444c0e401d40d0042c05040c102111005150b202d031614a0740d082c1c181c90380d40e50040d6100364841c074038054805090b07607183d02c01c2103e40380b9035043c982c0301d550780c0d502044001e420b40c10030000c0109200360060082d10758012907401400354441a40507a01e07000001040500c18091244002d4502c0e041000341980c1c00030301e150b0700c4150090302590311900b00740030601401290f40401100d6003000e0000c03418604d8102c60358865945030403d50102e540392181183c00c00015500203180b071440390f001c01c0041d48207400500544a0741c503000304540703050341c1e185c4081000c1203401304010382000301e80e4140c610300454868200c100072520316000e9410245038a4403550184140f6204410000e000000c00c40420200b100171a0031050940704d0300c0e070711407500d41c07030350b0080c61000d128203480300b0303c80d068242201c10340b04040e4140d51003e194000ca981c0381010100d02e03032400c00543c8244000400000e10402c02400901400c2c00500303660b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 762736178 1250 762734928 762734933
    0x1507050f0c010516180b0c0106210210051312080c1b010f030902010e0d2a080c0a031505090f01020d020c06090d080f0705090d053901030b04110412 65
    0x2005540801c130000c1080e80c008a0f1840b85000c0c00e11015134412500b81035603025440d04644c01456940c2c001000e0b6983c503004401100c090812141440d8001d03926070098955983e13007105d0a104034001c2405690341c054003404178059410140342d03c0740c460360480d840d10301c40f00c40e01c1d4a48000345001441d405680341c81c070503440d680b180320700e102a01c250405100c1c543c825070020345040c0f409403441b4061a81d0307080d5501805a038014030055041515200d03029144145264120005d0600800700b044c4030b94a0001d41ca41001381b1f403001160b80002401070508a4040e01d00701415000e0b20b07111203885240f18590b1075075400e1004160f420307860840166902521241141006030003400c184081c1c016064034420340b03401101031a4803501d440c1641c2e41d9075032a1002902d05008400d2400e402184003403001080020006042100710715590170030748090703c0925502c3c0100320340c40f1942a1811040c050a41c0303035019030800e8500b0313840104085952240e4000000c40c680003907015207040340c0041c1c802400d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 762737428 1250 762736178 762736201
    0xe0c0310090b060a0e04150611061006140904060e18100608031209010e0d110f01050106020c0f0103090803150108070503060307150e0a0b0322051507050f0c0105 71
    0x10a401d0750240301494412000546502440d400380c0e007070000729074190151780d4940d80821603c200c0c600b058a216515100020100d03e881c0c42190168440c60012584290a64044204851041d80ea1404481c03c808400310241c00964090380c2040d00d0741000f103a41d15051521512510140e019030503801240b180240c540303100b1600f40c90a00f0b2601009000c2d04902004417032080b02010b19021447d03d40d0600b05004008101804055008940c0c56101b0568000300300c620010380d0f00704980300d003880c840040c4e007220028402c2d9401769000016050007424400805600001c050400099000c0c05803160b190991007100e001400325000c00c50b9181960b00080004c3d0040c403240340150840c5066000310b5a00c03551801801100c0d80c0407041300014920076201018061000351411100070b90303032254040260025102c48000740ea035010301d40c0d103003440407611014032074000e0018004610303112120124400c000d050b10003002000c11003006000c1e4114010010041d041000040c540750503d100c18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 762738678 1250 762737428 762737461
    0xf022e09090b090103020f060403060e030a0806010f02060601110c040906020d110703050d0207020f13061a070b0f09010e12070312060509151306060e10030504080d05040c0e0c03 78
    0x1d42a40341c0300c64028035840d48206141925810b441c900101314801000038520f000d190700c01004141081d241d0f80d003c203404805000340c0007040d100d01c04151034180040d85c0c4c0c0300320001d6100040c1d028200080703482d0310403003c926080c443c003c10ba508850a0b2030109090300d8484d0350948200d60001100c1002c845c041c422000b0f58460b0300b9020b41480019a002002841400f480c5000142c000c2242000d41d5220301c40890000b4004001c1c440c0312030300c0d030000805010244901103658541c1510b0000500c0080d048807a2aa80903030305242540e42c800a80c100014041c0841c01c030384d075075a1800b000800d42003103100c484002d500e09007502c801051400500c090b80c0014005485400e03e4020445030300c3d442c0c0125005410711007054546180030022804100c42c1203206900c1d14201080000e403aa00015101045402950303003480e40e4003402000c0c0c050711000e4070000c041c07040401c0024818a9994480342e00140314052020035070b40d4414103808148030688082c80002000800d000383d0155141e12039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 762739928 1250 762738678 762738689
    0x111201090203060d03142a010b0906130f09050f100c03020412081806190201060e060d0f030c05070605040e0603010c090b2208061803070f0f022e09 65
    0x70362543c0307000c90203d41940c0c0d46500007020f2081501101c0002080340040c1c5861207104550901070003008440d070700d0188075025002d9060b51070400701c4041802c0c40204a032040070003074511328070b950410b000c5000601f05003140d40506985c0d0051540010f50510401d0310050548000f015881c4103084610103c4407413200130000d0500c104030400ca004500e84074008151b8012030407a480c0e103c8200550609481940355036030044000644280b0302001c064203d41054496000308000382d1181c10b81005e503001504e5043e48640001e5041000905401c034100f401d03880791801d4400003c07180d40d050703e800d0454210f0008a40c0c0400c051280c283e1950b41d60342d101100700c3c02444403a2070403401030300007400c41c043d02a8100002900d2001141000e04401c070f00c0fa0006152044107989101ca40c0e10b54030180c83c10032100b400c00440040040001082c0d41c440781e0080c204444684407592104107241096204903048051b00039200140403000e0244031181d40360800001e114400c040000b48401480c0d0400f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 762741178 1250 762739928 762739931
    0x80303090d1d0111030d0e0102041814063102030a1a010c0602250c0501020d080c03060405040f0203062a0703021c02071e0f0f06020a1b0911120109 65
    0x10640041519266480c140c00b080c2400c5038402c0e102c91000d0300f10700c11034150644260902115101c038080540c0108100e99907025002203c0005241c0a0140c91072341071030841142c8050085921440c2000c010654a00e2410360443d6130140c8290107011044a0041800c2c80313030b4040200450b07241c950050492400c000c00003840903622403000a80020740380c13038014140b9680030500483d140c00e036691030042e240804461902034503580c40c1c9000708805a0150a005010700401208050b0003404c07180c0c010944440058103603a5404144002014010001e60703103100d001080c44c0140e10b091080754062210722900740c100b210000304442d5201c4002c1d192104404c1c0402040c00440d070701045c131800401e0501416046e4680c0c0300030072444e00d6200d40240b001d8041407409440000c80303d00d113000481d2244215805515a0707054601500e150b148103100c0036030400030340b00e000140795264100400c0c2d5200c2180d50503640b600301d0001154851484205c02d0140020300f103034200d20b200c0096004201c0d0920 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 762742428 1250 762741178 762741197
    0x31c06030c051807081f08031803010b060d05040237151713052d010c050702011b0b0c070201030e0309030c060a0903080d02030414010b06090d060b0a080303090d 71
    0x1030683c3c03500003440141040054004610142031048030b140036545400d642a68007600e0b41032a640f40d600c0284400d1400d0f4440c84507810608040c006c001ca04000202090304029a003040e81001d44801402207911100c0b011411548a00d086980110358820314003024000048020240c10f503505a00004030030080344450003840741d40020144880c244c0d8055518054469240c00d000d030723600b101001031944c00340d02510005400c081650022030f410394515580c4043c1c40c0035485080b03070102c541200000c0c100300081070141d402070040c20402c40030b152650b0f0181400c3d8580503d000380607540c000b821000040c82405644e810700035100705030b590001841c5001c600000007596074049040b46030188a0204550703054034041c80619001b180c00408059543c03880442c441d0080d4021181220101c400721410054004144034152101e40040c00d010300e0310010300e04000111444030000c403401c94413104c44070602d48a05400c40018242d0300c0045445e4104290814200f0048148010401180c042c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 762743678 1250 762742428 762742459
    0xd29120a0b0115030f1b020610030506222310020c030403032001230f090709020c19050d090e0411090601050d14040201030c050a0203090f03031c06030c05 68
    0x41c56241141d00e00c48a009805442d54025005020400801011036281000502c910040504d003c1c1142d1115402d83e605955402e000176464072840c040540150300800000300000100c408040681000007400c1c0e1a090072542e0300134050320024a14003070180e4524680e8200c0e1410002d4815200015009500f0190b481c262540d4900507444003a04110b454074420300101c0400c4400304040142c0c170000d2020650100c1020300c800c58528081489600d01c9000910b243d8031042824020503020300905042c0349003080c007602030b4201090f03904560244689002c10071854011518030700d0b04c02c40203085002840240900744187d141d02c8041d50f41c11400c10400011340b040110028400104e8088405032034900048800f0f01071100d0b00d200452924820314144102e041e0460720480c400d98060118010044085402d0700a080d100d00141c2d005200103003030340c5400c81d1283d105050150840e403d04248240e098440c2001c008103680c03259440400f4000d00c050070720290040c1c6810f0303a070111070380f2400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 762744928 1250 762743678 762743693
    0x1a10080c090406060512011e0c2c030102040609240206040f03030b040501350a1115040f031a0c0301120c1517060a03020102030f0d29120a 61
    0x31400e00c10801c41002408020b015800380004d0100900004d280c203031022000e47c000c00c01003112280d0041000450340e8a0f05c81c0740104c52000d1a140c0d10405146040c0048810700c1065440910b61540d40d40d0089807952002d101a200400c00c950303a440c0702c146411440a0780e0200c059000310308545007076004640e203800061b0181c00c00e910076a00701c0c4540c01c6082c00c50041c1440e42145034494180b5000240e41862100e121085906a9203a0030340744041d50140128141c0d0b0940d641c586130407800c14040815100c403d440b2400b0750191154242c0221044400c007150300070381046218100d14001441407010301d01d0000007407812070000341030ee0304010348151158001407040c141000040190384080200c3d6817403441c010152200c2c090080d0180b040058694ae0252040860403004400054070501e01034002c542141d8068014519000d00c4196807860340d84202c4220000980711500390038007802022080300c0900b0040000e0050620880c07c001070b10700e043c80402602e0740072408800108291 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 762746178 1250 762744928 762744943
    0x1b04050112120f030609090c2c0705160602070f15050c090906010509040f1d01060312080405330c09101101060306060f0e01051c02060d11071a1008 65
    0x30f0070091089080c1c0030040740580398603085640c21a0520b0028020070900090200503203e004000445001c0070000b00210170110819142540b001a404a0b42e01c500130320050000e58070040e02800d81c02076548603d81641d010101c2115020081d0502c1414010314480003089001071039024003031401d0001d44141d5500032001964400c10043c008505140e0050f0200e40c80c483d80a0b009005807600c600200c030017851074411041e0440414802030500c00381c1840b0313100a42e40c2c031081e040c85654122100701e60b007010080c0116000d1240c420382142c0040c01d20f11501108103030740c2070a258518036006800b15000d0140030b049850741c0c02d11100c0d00340c1c2e03101100070103803040c103140c0b04048075088040d6502501250f131015108924002c00410001310140c101802d4881e0700c0d00c594403990780c41c1c050200300360000800c0102e180c0c4c030b4501d4000510f4402c0c01802820f44000c4081451401414011480e80c04407904075110714100940171482c00710082d0480e0700958940307040000d00d00d01061141c0b00c00b032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 762747428 1250 762746178 762746213
    0x1140f0604150302040911090c0901050f090a180f14061c052a040b031c0804020a09020301080d110607050f0c03040e011203080a0207020105160c03051b04050112 71
    0x200d0b80c03281041030001c0040780c0003c58008000340002001400c000700c81c000c0202c0e0003400b070908100042c000044080403104c813030006030358042c03a00d0325005481d10140c01c01c40c0c12a80c003092008000400d00e1920401c618115248100000d0840019559070111460081031850760a0204100301e110754070b0701d4882140308180d094280130074103245806414816049445500345198111080320fa410242c521041003105480810100c481981010b0b0381c2d05001070080081c1110791292114980b04001d043c3d040f81c40500004032860302c80c0420b80981c2c0090f000f8113107941c0044a11560b00c0e6003e01c40d598200711480140c101307410500402051481000c10400c061480012240030901080003258010311544040004a585601c9143c0d2681c1c00c19905500054082010510b030f24000d108032610b45030f050f101c19142c080191410305604440460030f48014101400000200714107200c61146030803042a420064100802004110740040c1c020480244d102441c40000900348002166081c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 762748678 1250 762747428 762747431
    0x120302060a1a0604212310060b04051504120b04060506090f060f010c05060403180603020c19020f10050c0120070803040212070f0f05102111120901140f0604 69
    0x2040301c5c1c070140744450001d400404000c0c07010221a08000c1591044c8202540401643c14042d5603102803401d854690041090740b4204010400040c40c241d40e00a141421091945080503580c40300030020b5030440070b041e25406a14010441088540c0c882da584c405800c4400c0780072420914400140741c00f0060031940105859210690342d0b80c02901c0311071446a11004661180c58585401019a80000002a444a6102c001251483c024000d44a210ba0040000c1c00107188694614a07120103109090382c0000b1070b8a001c50481e10303064480b074040000d603100e0a980d1000d1840450840f110080041081c2c6a94000d02c0b0080c8900811034545580140c509601c80e1122300000d0050342008081c1d4819118490000443d48011a6800211a201c4400350700d01543c0c1c2060000d41c001c5c80e001c1400060761078131005800165083c48401d00f02d04001c2c0020102913202e00d020050f0300c45000488216020343c2000f0340c10b102400390034443c00208140c0c42150400610314100450042d00461103075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 762749928 1250 762748678 762748709
    0x180c080604051306090c0302153f0901290102071811040305060f010f051807030e0313090606030606050f0901020c041406100207060f0e0a120302060a1a0604 69
    0x1244407032105400b0f0f0b50401801c01c2403000343d29040c0209407091104901a00c0010001d0104c0344c0c1e810195520140100e850303c1d20100304100c8501c00041e0f04030a010201038010000307c0c100c41c001035083c4102c01c542c00000c1c80c808050521508510045504407000c0e60001807862581da01090140445013413200289800300f0301c01c030103000b42041400d035941c03203000420004148500003980502990240c0500e8140b80d80310b000c08100304109005487c0c01581c0d6040b100c200300d0304400b40a41c4840946030001300907a4194645042d0340c0b2111446a40d502180030a00100c011403245000500c1242030400c071603840c00303074040c0503401400c040c5019880e01050b10305140c0d0080c030002ea14107400501c100154030807219049440e0009807940c900517060b2075407900065000051510964040e40c1340d00b403c90000a40032500301c1c080030704964002140f19000181d1030380030100b1208243c840d40160846c0c1c900341c0b45e40800c03668400101004d5107444a1002030b1516400c00306c0782540d041d1000342c0d004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 762751178 1250 762749928 762749941
    0xf030f0409180b04050303040308010f030206030402010e0307080f161e061803063801210b060706020304120e0609040504062018061207080601091707180c08060405 72
    0x850b00030b0340010b0f0407080c80200b00420048080000c41c4a00c0c4642c0710341000766210814000c0341c0c030403404000d42001d4104085805980564a590039902c001011501c0780c0791648820303820b2030314114103122140d009100e091011055141e080001c0c200c40c11162064403480c1840c0c2d00c400c12503120b1701003404070706107010b024600c0d198800c90146402c0081070200b450b1051105503002c64a20f250072586070800e41e00315894031b00b0b034056114418140e40b08141e42d150b9040a000074107034244024442551546108169260b590144c00000d01401005807a4907141c10200c0c0306445401c110410080f151100d02201da5518042e202146804e507000a0b5079900c5192810041484510740e00004608281034860f1a040350010115050030028640c900060003007440458042c00540c10319440f0000001200c25225055180d449001458411010b0756500010078900003401d60004640c0c009003c01d12601540c080442c00381d07580800d0400c96641c844500820620018050364840c40e16540400e04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 762752428 1250 762751178 762751211
    0xe10050f0f030f0a0c0203160201050306040f1a0f1002100203041e050a050d0c030e0906030712050c010314071e022e060605070b0a09031404170f030f0409 68
    0x2415000310490b03a2070800660021003a8011a881d046071070820155501283c4044145c41c0c0c0001c0c000e05002c0401680c0e401900d1642000b054990029511801c20044291502440c003080001049041806170280203100c4807060400c031460013500c14141c8104c000d513001940341a40c521490005840352250320b890411810342809030480300b42c000e40c00c0002e000000c12a2207550340310703504440100c58034002c103807044110310300007034041001042000c8070703030402d44400c0d54001d400500b1341d9140c4d03842d100d4074800e203000011300366210b81c454990061256054400c142e1800040180043c02c2d140c248030007400206021328080c40444442c9400724598020842101c2c0745c25588003190700700813914844001184640e203414403140c101400055094000e60441d0074194000889400c19528003103c1c401030000c680d0f0403030801c2802c1209803e10a1200041d10140040007010411803008040c2185045110500c8240300d07042003225a68052260007100c003215445000070400f20381c030040d803a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 762753678 1250 762752428 762752437
    0x3060e061918090c0312090621020f0906040b0d0f051312020f03220527090313091a0312091908030c030910110d03050c0712020d020d0e10050f 63
    0x1090011000004030410989250307100c1103c8687d0388280d0101e50f605030450b203402914031109250f102c5c080e40000755184035002042c11841c3c0c010024584002c1c0804a20a98050350001007020004034884a40c5070f568002c940524100304814000ca082c0305030254043e4514480050500051283d4400c8a50090000481480d1036009603034803000300060000300e20016140c218814800090003244602c1e10ba46042001264240e0030a0107400d1004040380c10040503150489502c41404031312130140c8014004400350100e03440103d1a682e080801220b000d100004c1203110740c2111501c1100404038005a440d00e41d8111101803840311194003030000f95902c0c0d048030255000008842440b12000001080401c0e17050b105480030700144082101c0398044e403407041525401400c0800c010b2031094204a40001c51700700000e00d8200203075100524041d94900c6407003d43c000f1030040032220b4040c000c2100111250400e0399464815200260340184e081d0b01700c00070700c400801c1e180c0005400c402a41c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 762754928 1250 762753678 762753683
    0x60409060f0e0c030d020f0c06130e0c120c09090604050723030105010f0c08030a0c09240305150616210804050d0c08270a030303060e06191809 63
    0x10004944102c00198440d030200308083d010344100f5a11521940c4000f070724500c01e00081c40a0700684000b40100035091b800000624802401c00c800864203801030a0460f000300c0101011542d00c4007201811010340000406645034000240410101a1a03000382c581c1d000804503000540b6540c0c800040e130b866140c49000e14060b18120840583e00920100114107075082600d618040b8201804129030405244074014504402407020602c0401a6001487c820741e180c01c121900f0350300c82e80d81c0d8501d401c40c0b603644030749003280d420100113250f01841101e0304800911b02c50700c0d800807a54086481441840c20781411b40c4c400406a005001c0e55901c1052000c8040c042c021290400c014000c003154410b4406469900034140d250508070f002d11011810181e106009504080031083d0390141c046124864090201c0c1001030346c0d02030750715101c00001962094500252240c1400d8054181c864000c080c54060124000c200c40324954030035004003120124506003507044002c02c40f40020b040c1c0c28800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 762756178 1250 762754928 762754931
    0x19031101060b1803010b060f160b040305070606060e01090b030910180c141c030e0a090624090e0a02041503020a02010e0616230a0e011d0603060409060f 67
    0x22804030050320007490226000483c440c03005242400301800c13904416400b80e4818406c0028000000079003028110341c0c041e48807051000043e544a0201c2480c0480701240065000286a800c11903c0d12605c40900110b180030010310040c0b40007c0e016040320700a0301c1c0381110110000b810040c041003442d0008030b600e441881108480c14400f072524410410407600075010010210b04160b070742c2c40d0b548001200818459010002254800c0907004440c002e80410010f9401701d4141d0310703100122401080c05290029038249032200d424842d4020700860824034400501d501907071644a1142c00a8400c4000700d00d00540311148520024451a84001d80807001c0381c201e08982038040d405400c1503502500240500d00c1c803601e460351521001c4848030301d039240100301410b0140c811000340c155000b8081c0781210000da1301c049181d03560044050f400005203180d02807080ea5074085c0c500e00000c1c00004054401508401c0000c106020060000d80625940d8001600344085a04030030640c040e030100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 762757428 1250 762756178 762756191
    0x9030a0305040e0a051b07060e1c031406090f070912030503041a091b01021624020f100b0d02060a02060a05061c0605060109030c0609032319031101 65
    0x4001e48542c001c3d219015140c0c520a00060841245000300392180d40b030706100c080d070b003503444450741e441b604040c0c0107444080d0f0b941c5404044a2040081150386007500300b140e40c100d280101c00405580c2294406c3d401c11544c9401d00040d42c40d8418402d40146840c05a982d00e6600d940044078611015442014074420742c3c00f07800103042e044030055000e98040e0166007170081d8540e404690484d01500c0c1c0c1c074003d0b0b1043d01416102070588090114442c1f051059030004103640700b42c001d43c1d101503000980c5117140c0100340181c9803030101c0c540305e010415001502c141c0c900ca41c1e40c00d032030740701150681150030344802e0301e4110b95440c0039150100701d50040c001a100d0a0110b0002d40d50003080342da20b9500c526003008207100d85018240c0340d040c2d605072890301034a0000c564464014040c064665030500c040b441000c00040d04800d241000740c9000d41c0d858103c10310b582801c541c8001c445a5071f82646027940301001c92104003141c046c1200d041100318041040d01450222600400422501659440c021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 762758678 1250 762757428 762757433
    0x30c0e0906120304090e01050a05130609150e06060a090b100c030c020a08030309010507051804153204020316180e0c1c020f1c0b03010525090b16050309030a 69
    0x600101b0440040c0d802000341c0c0c0e80b04a449403c991040c3d03985005000020b942400195858004001d01c91150f0b4403502c8240000f81c070401a01c1400d480d490b0580c10a40800c100303420178541c0c0000800072550117200c5140028040b83c0c42c0300d0070f0311085041000404034001413500030b821f42c106847e4080c224840306650782031003549907082070718402ca40c0c7d420200849c0849101d4002c1c2c440400d5146102c60b482c841303174020080188041030610420f00b00c00500062100040b221894026030f090a01e51070f03040b1241000b000a02903801240d10542c4184180700c0251144045003802900c1d81c1814071503402407500700c0100420560210807102c10090801c580c03100654003402ca88039880000001e4500e501e16088268028941455119401888186003200c0c551b124807206909008000032040c840070086801e607403003202c3d00700c075003e00541000b11008110391403080350041c84c50621800c83c2421108092489200a0769070a01528560801440003c1c4125010010021f003140d10600061 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 762759928 1250 762758678 762758681
    0x2071a090301050f010f1e0f0803070201140310120503070c0609061b1520030403081008010b0907030b010908070315110a020307080f040503011e0507030c0e090612030409 75
    0x4140035020b9424000804e85202081860318160b42510712817581003403c020f5243c0c040405410324090a180e90080020030440d074401d02005090290003940e48c4c1c90a47c000940701040b106511526000100100103460700b1010366a0b050300c1c603450700b800e1040100d0034590310b10300503c0070151081302c0311000010f209410004001c00ca4040c1c0c2c81e0107100030900480245582003102000d0300c0c2020008800070340d240c240c3e0000c40154080c01521050480300600000250800c0341d0440110701d031715040c070240c0d45485400340000d1080030001e00240c103026010903070458002e440302040c540c039601c0d0081c0a0f805160100084d000c2c100444820b0f41e601e0402c00420650403018222440c5090045a0105001b0003210303448049900110720300a85503440130382542c09882d40300c0c0640410301001c503d960302070150680e000c0a20303c81c0400000300c8a100c074220303039001d807100301494a000c560350181600030a400000400440d0350114035918103010584441c004250b10740c407800005404a1100c51a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 762761178 1250 762759928 762759937
    0x90b1602010c0b091c020a0506040605070215070f350402010905120c10050910122a030b0f030a0303050c090301050106122304020603090c0316090b091e0702071a 71
    0x5c0ca1404180b140f03406009a031606401500a05560408400980400c1d03258000c0358205403148120360990f001c0419410910b6070989901d000120360002444a0b0b13031f404440c01140301030103412400382c0226009501d020f50b66800800400013040d0b00007900b07680c09000f40c1401410068030b011940068841a40d8480b4445100d180c1b03e904000c103c0c00070383c4d100b0019074200000c06072507940d14800e00c0744151240c00391580450441600d640c0805522489556040c603442c55490b20b42035240038000c0b015060f1804104013501500d24054019010380c0c000512004d0b194150500060f03c0c1c4920100201c1485050306141d0950300b000000503041c1da0103403a520220303104000801c404a10104507180e515008c1c0c082c4105c00d444c08005c00c0141c50908015a00140c0260446910211640101c0e05008066a464601c003a034600e003008664514040c103081400d0440b41082c0030714240b072140c4040a070700054050f0343c600ba080041c2c0c3c924001c2005c40c01908001d601011600041c440b0b04d68903a10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 762762428 1250 762761178 762761203
    0xb06030a020a18050c0c1f09050714010f03140112061512150207020a09020c010b040e0d020d1407111302180a0902161401060f170d090b1602010c0b09 66
    0x4c2c003800035145c4802141691400407901d0007900000300d42d10500c2c0000d44100504510295641d14680d00140e0100302e4000144502c030708011000c03111a0000d00203a00d214070850a150408035580040401038040c3e41c1591510f41503e260380c18141070100c0144104440c0c180d60008920300410184091441491302920074216a2a032164582084040e40104140203400012808050140070741a4000e440045600707000010311070040b40c000783c10340b5440c214a0403542c000b01c142402040c2c0c14407510201d90080e0030880030242154000d62501d1040a201034891400c0302607044050360f0302c41c100300c001c1140078429512140404116070001c40b100c440310384550541074000030074042c0340c02580c2c400000c08040c00118112515003451a01d91418000ca840d5607803034010a012100c0f00700d51000e00b044c1c0d015820580d00e140310300b0385421204c402c40e00520515030010030071101c0c003904980300b8550550500007008411710050b1402112500b001303020294110404c40d03203c1e8001850280c10300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 762763678 1250 762762428 762762431
    0x806151e0c07081f0504170d0501050108070201090c0e070c0b01090501080d0305010b030403270b0304020a1a071218060c2015070f0b0c070c1d040b06030a020a18 71
    0x240d80e0b049181c0d82d400303000400c0c42a254038507014130307208001d40d0141d94440c0c0910240203c5003011400746c02640c5c4001014400b450b0b40d440180080d5a014022640c048114002001000301a8860003001081485211000d2451200146c83c0900c01c81960a100398000030b00c41e02c0e561602d8074100a04024018171545114104404084910034040d0070704072003901d80c1d05071171074503a80c6040710101880c1000380b400600c01c9065460340e100740c0785058010306041030b44039140c0c2801e20420040380034503401203000314407400c4d0708a0009404022140621350114044044960030702040e506080d940404091046400c0d00c00140c13240c0000110398040d00c602001d0095188102c070050400801041c4160000718250294801e020007400410519000b02071007040482c00b5900c43d0842001100c13422542e140116003041080065440c1030b0280038410000b16101c0040312080c409400000c3c009000c0e062404081101600c0a105082002c0e40181c03800403e6516011700e1406076088070490140703076 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 762764928 1250 762763678 762763693
    0x21201030b060a06080f0402011e020a060e2b020a0203161d0106121a060a090305060708070819090b16090e0c0a1115101d04030806151e0c 61
    0x919000010100360b4665850345d054580b03908115050300c0c18006c10032814010700c0c2506c540f0200103019224003411840e40102702c401090f282c404140c1b4540d68540032282c0c8101603030002ea12145030051000c035480d000150500c021010201c0c07506a68100294045c01080d075002015014278080009641c00c00080c0042410440302e11182114240b10314400078005018642c42c401803038000c0c2360382c10200090f04c0c001312800030000746540d106010400110754580000c104002090110071384c4504142030608952034994406480e00d4001404040c004018100c81d401303035030780f59003d03820043d080380c02a00c0528040381e078a400e291118808101040c8080c0c400101d840c02160418846c460940c1c4050070480404d00a071801d50700900000703540d0080701003503600c101c1c480490300c0c42800c00c0703007403a06050302e060500c03060400c1d004850480c10706188108004250000d07401c0340c100d41c0598800e4030b003403140e10103041039003c2d9501c115410b4801c150700da001640d0b03400c040c0c85450680410780b15403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 762766178 1250 762764928 762764941
    0x7170601050304030c030f1202040b0c0f07030308040206090a0803160308100501020a12030e031c0c030c0e1005041508010302270403050c070315050f010f0515070203010f021201030b 80
    0x40c04103d400600040d5100c0000700042d10030f410121603a040c90400d134088182401882d400d17a0441c1e0003980c0c0d044400b0540c208059010030807160300701005800782400e41d041d910700070030150004101900500d00080c00801544030203541600611000080c1ca440c7d141c0903803a01141c0010716029400502801d020404c120844c0400b20100c4005130003c25240759140d8035810701700b1070a0107040a060340d4080340c440140302031008103000740150000001c100c0360300766882d0444250428007010103280504c00d0302d03483c0e0000400c90103807904030b44404c404c182101c011119482190091003a07103088070584a042500310030020b059034402c5513410407065482c0010b02640040294400802e070b110070224010a004100518907114510299030007a522521064038419074119400320b01030383d903001c12410f4000e280c00107000d442540640b06040c0c0ca450000341c000c0403001c00742140d100d400074214003159000d41c043c0130b100a00f11402c1d51502c241d01e15181c20704009100a84018010303030b0010b80f1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 762767428 1250 762766178 762766187
    0x3030b0f100e040b06160c0611010204050603181015080c06070f08070515010f081e071802040f0308040305061f03060c0c060501030b06011d0f0f060d0507170601 71
    0xe051406030790700c0c031001c0400820000641a800c08040e0000c0c006c100e1b00e000850350f0340b0549110360080ca16960f80341d1030020010100c80190441c181140d00c1888103108950380d0b00100ea4110f948003001040c00050b50700040d0626422800440c0194a07004a1030040c43c0350380d40050440764204d06982103c1d216000340f15180c420b0101c002c2c19072282141d1000010725147c050903600c1d000b40220380d034022000f845044840f40a82100d0f481c00c001d14002c0081c00709c1000320b040405000300c00380540413000f540c0c0c59620308040c0074480302d0802d001e03000040100140e0646004001c122541032a0b10b82c3d0307092803405644180401d48090042c034002428404600f0f00e1204240e00c0c1c1c60546900710f00e152a50390041100c0d94401042010000c1c00301e010440038041c060103103000e4100048141405800900300000c200d001c607482c62440f00388001aa0741d01395090160030020740707500d00380410a50010f0b0051050b80a1114018a031805101041c0c1d03008d910b80c0790844688103c01e0703280c4c03212401500d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 762768678 1250 762767428 762767449
    0xc3115060e03030912030d06120b092d1f020a08070504030812040f02040504112b0b09190507030b01090908091003021926100b09030309040903030b0f 66
    0x36015403081041c1100c5081c07a00b003000340081d00005503407c0145001006042c0c0d40a50b114988203d01c00b04040117100540303450380d402030701076001051410350300d84045801180b0380c2c074803104115a203455050410310034081d42c80c010b840040d0b020070f095503500c0d58030002d4010103526800165220f00048140780a001120300380c9420982590522000c400304108500000b80112030a03034003900400300503203840c020680158800c81040c904918400140300300404045c1c1100405d01150080e9043c02d030305607840e071124907003002d4015082c2d601c00071883d213800b1080300c5074440b020034450218184080498803406036485642081403990b601c61030035095800002002d4400603003044100c640340340c00c001d403034049006800c0150a000e207804528a51400d00500c0d000415850003040040c02d01c401c03070010380e49114403400740c2d160510410ba80a00a603600031400c058800041040d103a68040041d50003080c40240180f0000701030349801000740208030f10090164072404102c2010b07203413507003416 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 762769784 1106 762768678 762768707
    0x80d0f060603091b050607030e0d05060408211012030c0206180306010e2a0903010f020c0c030c030d0f1806020a0b07050301080c311506 60
    0x10803400ca11300300f0740700c004c240e106061201c3c1e580d00050700e5013603030540340c400302c101380600200b5803844000c1c0c3c1c081c2c2248650f40c20413040080c8074004060000700601c412020113210008064520305c00d44103075210825080d01400105000300220748524017918081a502000d900400e0403a482942000c200d009030b10024191401d00f00610b40c01400c0f81078101c030140c0361610406540c6201200102d401c601e030064101c0358440c501060301c0080c41c009008120a00101d44c0e100c00039404200034130081d00544900240f60702e400b0400c0001000003502a103501c850f41102100d82010b403101000601840c10303c0c81c03040222a250420151002e80c000b09000030710341c202144000d000801110420004100502c0003aa0101304041da050307007920f080312070391078810b805c0340e030f8440f0440c0c0d444100078010508880030045400205580c012800142d2000303071900000c0310070110f84002c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 762589928 762769784 := by
  have h0 := BRFrame.cov_init 762589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 762589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 762589928 ≤ n) (h2 : n < 762769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
