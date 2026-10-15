-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4381
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:26:04.513484+00:00
-- url     : https://prove2.me/submissions/1b85617d-5c4d-47a2-86d6-cceebdd5f4c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 787769784 ≤ n < 787949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 787771034 1250 787769784 787769789
    0x9031704060c0b090a02100203030420061e0f04030b010e0a050c070b150303180a09140c0a030b09070504090e01050f0105010c0609080406080910020a020c0f210f101104 74
    0x1a0600c2d100410413100081041c150250b600034021003401000340d20080d580d03002158140c40d01d5500c6055440301d40d44900c80740729483c4c0e02801680c80c1884e014071200e10425003182100d4100c1742001409055004400a40f01840c41004142125450a1822070000c20007420105d9810300d80000c1c4403402800310111100b050340038210624640d206145c3c01c11281104140c0c5070107000000c0e0010b9401a1303d0703441119040100c0d083c04d05152528000301c200c03540c0e800b45801c03652902020030202c120400162680e14010300e07011a2842482000c6222032005a450202090001c1014800052140211104100e12a008002c41d2924031481b00e484041031103082c2c14010506201d00610065400420300143c0190b0020b0340e80340e503518000e080400c01c032505119806070385d5825042c58414000c54500c41c01d19802400d4008500c01081800d0440e5000d580d446040b40301c044050243c81080070a442c802d20703019000152614a425043c100000b200729040c915088a411a0312525002d0301c09 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 787772284 1250 787771034 787771043
    0x30c0203060a0b0a360b04200d180609080a03050a020c0c04020315040504121e1e0c020301050f0406061d040b06030f0a0b09101103062e09031704060c 66
    0x80c0e0110000917910920900d0090494000c0d4034620303044101498010300c1c0e2144054404000441340c00540c07842c201810703070382143d014004008410010506420402d801070052204008400c5103642c0c140855004140031038114501044000e25076403d4411396500840307241080d494072006141c0241c85501c0d02c1f00341d074415540840070900c04480d101c0d80c2c080101000d4020040c3e0304050070685501c0d40101c848100003261a40e403002c8021803003226049045640d15004c1254403420740951104000039806801c0181030224100507035030900545000c0c01c117031003000c0340d981002d05000d07094800c00c2d0410445030440e600d1400c4a0010000281d61164000000e2040713920380200203030415800005038080c030300c20700da0030f2414004101001405540504115481400d1402801c070695042c141d02c100e00c0301c0180001140c9081800740e4807640f00341801c882082c131300c10190503d030034401c05458a00040c003070750701801040030a421034a010799961a1040c140703882c0043c000d000703044540c0d0042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 787773534 1250 787772284 787772309
    0x203030d0507180314010606022413080f030f062409060409020316030b040b0901210512041e1202010c060603050a060504111807180f03030c0203060a0b0a 68
    0x54407103100b14041c99095403550b92600da0250b6031700b420707105511103050b610440d51820740e000440600014135900201550840010b051001c5134548001e03c000500022030000321503000c400040072640100641138800c010f807a200c2c2024248003040090040c051402804011401003002c40c4600300e0b5a90707440c801e03000e15039902620000c982c090086606c003c081d41e0001c014010390186640d424880007a43d0b641c10485070000c40100016940d00405d070070b40103004240140b02b01001072000b0030900003d00140c1c1c00c5901195a05880c000d44015094104440400c01f0704c00078600c04200c50b0394041d020240c00c1442e003815011380c60601003403002818005204d000c3c10401129030071a40045030000f003a035545290904002d0003814044408581c084030152000c8101d1401042c0b4401100c0d0300b40c0d4642c89a911401c0c00e841c243cce40400b02c030120305180303034001482c001c401e40c0a8020314400cbd540c450030821144180f51410314040c025400302e60805000b0301481c2c84400035041166003400780f10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 787774784 1250 787773534 787773541
    0x161b0305031b0f0d02030c060f0c03040602091f0f1803050d08071e0807090806090703110f0d08040305120f07020f12030a03200a020a02060315090103062301030203030d05 75
    0x10b031402480910040c49409501c0c503079000a1703000f00c042c10314622034409407480d0345e64068403c08120300032201084d56407814404280899402d074041c184048020300444425680c25103031102c0b141e104800c0d40d0000303184a440c410143c0e03000d11482e41c42c5184050f210003890071951b40d5a100c8159280240800440c01b00003038002d1b00c00c4e440512003085a0014a11040010600030280c41e4200c0d507100c08140301c01070024601a00180d0300c2e20400918015056560466855600c0e981c010310019030720102c1c1720301d005020707601c840250840740e1145c564941d4a0b8590315095041209c0140c2000300d5103000c0c08441e001c1c2d01c0f443e080b164041e07070446a90f4415082140019200c2061074040000da1001007012580c2580503842208128190502ca080b07007944002138014a01c140814080141c00120a40006044c2000555040700e0030100c4200301488400c080f5420210903403068610a4560206d412650031905100d0b00311840084d041c83c03150f05540200c4d56900c542d101c1d0110f0b80b5a04d8002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 787776034 1250 787774784 787774837
    0x90b0f150f0705161d040b06120312040b0a0903080705091f03020703170c180f03060f040b13021809101d06010503010b010915020109020402161b030503 67
    0x890703040c02012481c0c2601d03a19142045607450640e100d8459501d0550400803607035040c403e02e10724400183e014000060340c1c8650342d8000034000a0102030300180440001e1900c8441031015040b003400c800d84503e0149032905001180d52005414482500d00e8048414080f0343c0c44910180e00c4215414002e6071502d940c0c0110f0300402103003586161a891181b1041d00d41030341a0001c101d4103010342d8580464030301400c800c190b40702c019a403909001d0130030880c050091030030000c501d402c404000d0017065958800350110f030402d60203c4421403600c040d0310402040100c080c8046420440c034110541c54a0840d03408145244100009041204030b410f0000381c010204112509601c0410030741408415001000d40e5040d5034000c210041501450001003200e08052051049942c2c1c1607550042552a11880c0c08a40c1c0c000c14040003155201c1441da405070301c030380c0020000540380102008500c00d181c2010010081c002500e81440c2c880c400c2d003080459400825621107030300360b0140899a581190341c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 787777284 1250 787776034 787776037
    0xf0f140601200102030403081f0b0412021801080a0201110d02031b160605031806060f0411040b120a05010b090108072610060e1207030f031b0b010906090b0f15 70
    0x40b44500f0340c0000200000c140c4e205007140d00411241c4202d4140d400c0c00c50004000b0075150040030000c00d41400b00f049403003503031040b001c403881c0050681b42c401d4a14118012000034240c0012520381e203c450010700310b50340300c0c2090241800d01000f80041c2c04841c0f0000703442e4821001c0ca4030101982111002c503100b000e0020099000195840f060895034400010389560030480725503900038401507100c2c1081201045151049000804501c040d080210400c0014107080c900840030000501c0040707050b08244005040305441e925107a40d00e803401004170b20076100e0582010559400a02020f503c990b001000c0c680c0040c0b0300d0070300c0c044088401c046140c14030001d01c11040d86240103400d01401025481504056585981e116001c2d680444280100125022000f00065100b860100081201f40d038240800510a241512102400c1205210348145030142515038114800040100048038854100101480c1c6006c1c0940405200021b2000c0c8401e12400d014016030300045803500100c80 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 787778534 1250 787777284 787777337
    0x1a190f0503070b2704020c0601061b0f021017070806040c09030503070f0510060603020c0c04060303050d15122a0b0417121c2301171f0f0f140601 64
    0x8008641f01c1c4180b1003d01c1da40e41c001e100b1040814480d100340041c04000c0e808401c002c581003012103086000a03070038000e41e032000d00c00742020408242d800c1d25050b5110114070340141c91542d20111541003240812048035040c400c0081402003411040000a2010040d5125107401c2442184143e00c94140142040241113120761381c0b621300840890101d40560207030820951000c01c585806001a0074441120168000903011031018032480003c1c8203580c03c114002f052580707138140d06582c0d03a261091034a1046800302c0d200c19074101c1c62020f11110f0040f0940304200c3c0e0301038440140c0780000006082c861802042d42c904003048007001c078107400300054890403040d400700c2e9945400c40c40703014012468188901c00000c0c10030100c1c08811500c102c40031110452044204090791a00a0004201c0c00148503107225000745400d8200c00c0032810301c0209050b90140001c40c4503140180c0c6042210300010034040e01038505000c200c11200c00b400c81030b80c81318003802c010030f8030101240c1c8500d1821b8440d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 787779784 1250 787778534 787778539
    0x40201031d0109140309060405061303020a031202060a050c04180207020d0605060901080a0314091f051e0301030f02010309080f03090109030e221a190f0503070b27 72
    0x44070030324001c055000c04045809054500d40f042c1d0022604d40d140d100d40d00c41c02d42d201809000030b1103989001802070040da4040304c1030b400340541c1c03540440c03982c11303040e4810f852285800c0c15100307403150144400c542c491030b5204108054502284007400c240968010170f4409030107001d020308000184d074101c60f503494004101d5042d81006240c1380d0301501c021502136004803c4000000784a40c800181c50b4411070307058030782803031005c500d11030703807145030448450306030701034546030842d10a8007400c1004140d103a07031070395515500c03d040100e0303240c80320742c00130401104c2c5410001080411254150460701660900e0086a41b20340b90a0440d21070041d1a50034070492800814400304441c1540b02c051094802d89841d49000e403440c1c20132041e440b00c0b8032079440c444241030714420300c050b00303501030b070f440c0f181103907900c428100030f070010448a5400c1044070a09142c2401c0500c202c04500b08040c0040c078080b4000d1490505010315103105008030802501c121001c41200503110b140b00a820220b0f00c8007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 787781034 1250 787779784 787779821
    0x190b0708040c060e0103110f04050a08030304050c090a0623121b0402030a1b0906120204030b0f220f02120606060f0a020721060b01110304060e0409060e1f0606080f04020103 76
    0x43c4000608c46178040d04c6807074400e200001b0001005d03440801580d21a64020002c1d10000405a003071000000b0000e14154415039070b22750204814450f40d0f9110710214002d04036120f20002c0394140644601502d82089641c1d102450084c404c03d2884008861004144e030096260340390410400040c1424039003841c1d600d007070000e542c40c41d80da102c0402000c4590342c1e03941c000144c1c0038208c0c52049102d10b01014020085d00303000600c20a0051144039040a01d144550340034a00082c150618510303116411a07861400708560b5041d8a0080410440d29034100040c1106003401c4001441a03c555203140100341000300c1c0426083d0300034002c200c000c0450307680c1c10200b00d00e2244040d0040344154811200945030800141e241d512480203d841c00412100942c80e02d4240801511540344000c61258059101c18110000071701d01c0c05044074502030a00200321154041e5500845907401003c101c902519195041200c26030005000c0d80020014411445603216800100c01a052003140c400c4900d08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 787782284 1250 787781034 787781047
    0x5091b010c1e030203130e1605130302031212252007060305271002160c03050115060c05030901030b01170c1308191112190b0708040c060e010311 64
    0x4000c1700401d03200340c4802842450b20749070304610800c14001d40b00e480030071201c0c1d10002c1c4c45900800080c0174100c03044030341190880da00c0c1e00280c540000c03411170300d1a189003c60346010030f10f85c8402054001a81d14499038040f020b01005d000c0404500c4440c0702004010b070448205d000806200c0040030724a40c05032011644c40b00e1024018010955005140380d01a4050511f41d80c40f5000c0075468140341c40280c074a980c66040081c001e5001141a80d0104001c4c40500001841800cdc98400840c441c10010550800c528901c0e0400011503201400b8403090395100b40010380044110350200d4000d007400991902c0200c0101ea81500030045403080c85650b505001451145034080c1c040c0c2c02001c90707001c1e45030340c54030380580e1581e031408144c401d02c00c000401480090148043c44882c1d4001402208003842240406890244001da01c000220a642e2400c0c091040c241c1c070f6650b104910b41030000d51400e160351104c9114880d48528810800f100d443c2c0e601342c1c0e200360800074044150380726542d101c46 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 787783534 1250 787782284 787782287
    0x121306030e060a180c080610150e10090806091c020303010b0d0203041401150f050a08100507020a0f0b0610050903060a050417040f1502070f090908092205091b010c1e03 74
    0x74408d6032035408000f40c1c01c0e00000c0c09100c2d2140e90041900070f650320301e4058403110602c01c044024842c5401484078040c40825440b20401006100310b1040e070041c1500c04150510540100074102d203c000c42d00304000600130003081c50200d941c1c1c04a00d00b0b006a695446040006510170150040c082035400c1056116005c030507080340009032408581101202ea48e5402040f220b404144030f03981180e001052190080a226844164071100600580d840041603555170120041c82480455038490044140100c0c0e05003124121318200136400c00901d0034072a0000aaa101c030001d254849413a224800101045580c04210480e0781c8580815a1540d03181c0d00040c20583c03460140758130b178140c5071500c9001984001307051000c407415018000050380c2080440c00180100803401da906240c100403646541c1c58801c0000079440350360130038207211745500d4440b01c02d94030040c0102c0d04c1030303205c01074218410901c4030310a000100242894a8007075031901e0314216415240101c2c0442c400784000c1402410b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 787784784 1250 787783534 787783543
    0x7020a0905060a171504060b0a06110609070506160f0b09030a08090c0913030521190c02071809050a081c0207030c030c0212121306030e060a180c08 65
    0x2102d00711184841d9540310940300340f40039600c0030028140d80c0001d0084605649030100d050b00940a00c1000c10306c0c0c5840004034112a0391a8400000200c8140d180301e00d9403428011103802141e108090301c840b91520700010f866000b00350245103400c0301d85405100300700270540e084030400e60120501e04c80380350040c511602c2e40c20000030b40d1701169020000034007100e000300f061094000c00a004058903190110f070311040176003a6400b00e0a1110030030100c01040101c814402c5601c0181d4410900c82c078200f8444032110004d1414584081d08118031040d5540e00410740d48180c031a5078001802503034506280c10058802d4200188c140e01030941c1c008280300309080100348111003c0713160000380c81c4a08000c1d08901c41c241020b4000b0758004403c0c1c0020b0310130000d0315043d0307000610481c0c6040710750003094140350514151000074080000c018204030010b4910178000c0500d810204034501c031041e01c0c55204d103401803080708800d944039580c54004541200c02030304250400305424065458080c52581c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 787786034 1250 787784784 787784791
    0x1505220e03091e3105041101030e03090d030f200304080c06070f0201260721020c060109020d1d0105060a09020405030c010e04060801152309010b070807020a0905 71
    0x202d81c42c2940600d80c03107448607503200000020707107500c400d2140c2d03620211022000c18001810140c10149810040002e401a28040e03070041f008010701489100016046a04500d00c0311450b400078080f82d0f02c147d440703480081c4c03402d400d4140003000d182e241c07804a13490300d1250040e80e98000204c4042d0304075000040031f4002d0310401c108403540780d0b04c0710040088034081c84e080104560b00200075400154406c540b0b0046010302da90b04da468094041c0030412410300d04035400c00000b801014014902c3d04154409030102080380c40861502121203410750301c4030814041c0c1480c09800141000c400101039112048030f24288840803248906a24081e029007029510a403207403080d0340d40403800101034401c40e0101c0c0c0c4002c0041400305481801518080c401e1110143d0160b500c0741c00050901c2c003801b401d21844801d078840440d1609140c0602180c082e05071407113000d0300034581c010581c0c4c1c860b0310a250561b48007508107602c40f003580c504507085228064000b9003141081d00006024201ca8001501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 787787284 1250 787786034 787786039
    0x5030703050703110103110f0f0d110715050907030b09030d05040803070f0302040b160c03021906110c1813080a11010b010e060307050d020403061109131505220e0309 73
    0x265070440044050740e1494000e0f002d03100040144004401428005102e4000c000b43d03010300340b421107030714ac034110b50001d22801500c90f40041c030791040120086000034589800c01c070801103418005c08031a668002c6000c002d15a0014001003201c46504000323890a490058900780303c545454070305400950020b94070310703002c1400c2d000b08a02841c0a40291000d40300c0042406007001c40221851460b0300c4164400d42703c505c010b88010015844904c0d010007030300c84d4007030f40321000c92401e80000c1045003c0d440e09659500034020840706a0388081c545406c5080920009a4584581900710072041500c18001c2c0b02190020384030900e950000aa18607404280000704849000400190740c4078001d81211503104204000140c4014001c0001e4090b0070140071005080545964403401283c200d10a400600900890080094609044290150103a01ca400d0000804a5402c03101001450084510031400301c0404c03803100707001142d020608050040d083c000e60500400c550303180d52004101c1070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 787788534 1250 787787284 787787303
    0x30b0a020a0815101b0210020313050402040807050105250c06170906010519080604060504140712080d02070516050a090606080a0221010b03090606041404150605030703050703 77
    0x400401c0f20240b02407001d9009010b041030b8807444e0301d04403142103040240a00f02c1c20380c0c1c0140700158030341481c1c28043c2d620940041d6924458035014058196590380802d2040d03004000a2014078004111102100c1c420f0903e152149011000908842424600209681c07094544101400b03420781095040f0380e2140ca42134441802d040c1006e4811070201c8825903144d011030010001800d01001280e09014a0302c5041c01180d00e4000709400c001c0213880030740d020b945503c180000d001000900421215041c0010844903284c0b4034120f0540c42a407401408003400450703c0b165000c05501101c840176803000903180442d1003035107030b540c40c0d4103140a400d004a12001e030100307960000f4490103064520a80b241482507a6200750f4401941c01030000880c0c5103495100d00c4078600c5460f44130344c0a4118001e0094582c541581e0251510328001c041a106a0600c0c41518018034080402900f1035004544203000c1e10012021130003504c01940100d41503c50420300006200cc082190001d8901c600c07401e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 787789784 1250 787788534 787788541
    0x5150103020a02150603030412060614060901120b0411040303031d03030105012708120a021006030f02010c020a211a040206030c071b03031e0215060f030106030b0a020a08 75
    0x440c01c0307000d01129040941d00030401503d44181194180354000801011280f606407905030041015000e010b003240d00e19111201804202c0683e001c4254101040da09141000d0030103000270080c0801c1d04e4240100350392a480c0e22220f4480350003001c40c11400d640c100d030381e844d541e24006004140400c0c1628043c16407001081c4a0310f00401183e040702c00594400546000706000920140c081d81401c1075005245c00e8001043c1805000e05004800184842a01da03c00000c010782441e48105417490200d00c0c0c000c4c10b0001410b001e4481500d41d8081c83c10055a40151012a400d204660801d1549100e5a6103826450050189090311356102d02c0c0d200801c0c0d220256000d503031000a9030b00030360002080c03001603031644002c0040d1882a0040d010320000b18038000fa410002c121070f8000f600081d9940e40032804240c00d281c55003022501510040900180c1880b5100d54a100076007a18803500604c030744d110081d5403d4111101a64100304c0542e920309000403404000c1d0701c23006660000c1026003001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 787791034 1250 787789784 787789787
    0x10608180a140c0f101103090d0506040201090605030108071502030918070e0901080304120804090507020312360a0b010b130f0605070b04020103060e0414011b121815051501 76
    0x3401104d4800303441c1030a00f030200c11050b9084041c0c3d09500e070043c403007482480d12580e0b0b42d00da9858803e000d9001390045040600004100403056005003041c0101000108941c40303000520104a07012402c1c003d4192200d000202c0c01e52095800c000d40c4800c8404e0f01c1c2200c6140e000000d400f038000c2c3c2c2c440028401005c4240203070181d09200f1000b46805c14007042000d1070210109504503032082c1c0010745042d860307820700030880b1402d44412006900206090f00c0001100e01100d070804219501c07003001e0521030f00520303071280081c0840075407500d804403543c0d40c251040144115841e482116080e1a41e12181450601c9e0081210b2494007401300a000800c24440713200c00d8141d690a0390340c6854549a40c4900c0c0d800700020300704a04165940d0310000d040c040305e40c142401507202d02100040e183c802001d0701e013581d1207400c00b210020701c44e150325036085070404a001200c4002507008115000d050316055404044600c02500d0041d4618140f4803c052070341c0014400c5840705204103100e00316400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 787792284 1250 787791034 787791049
    0x504090803040809150307030218121b130204080c0316120b090312010305010c021e190c0807060f08010e040f261b070b0304020108010608180a140c 65
    0x40140c6100d904101140100341114001d101d6620301614014902d6174005010341030750300c2240d0f10400a81d000c549a1000c01c561615030200e5a022211110600b683c08801500c1d031018440404000520042d820311035216881c1c02803003084990421521a0358a400c40d603260714807503041301e00c03c0c02005445018401ca00c080002a180b803001c40c2c1c00c400d1038981d20100b0441020300301d42c1040c4001e219100300d149440d4049401303103100354000700d014105101c0c0a450000c9107108442d0f10301c041c3d101ca080400c0002140c90b001501580c0014090301c050401d07182c040000c0e00700e503100e4050384d4400318000303070010394121740310241c0d5032000c201c0c0c0e81c0c81004540c1034406070b80c000c099100e51030f491000f242400300400a14a03410f40302603441c4210700d00c52216540105000030304040000102124040103002010045c00e4405100d85540b40940c002401100140100d1051101d41000f14000180030955030841c24040c03070850b480c03110907060074000701e0540c2d0807010003441030706c20584e01d5003070009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 787793534 1250 787792284 787792301
    0x3030c0d02250e0a06050d03051b06070e04020a17040b071e09060c0501020d0603150b03061e04030c080d02030f070c030c111914030124030b040f0204090510060504 72
    0x1403490728031500f88a2400d1400101400e08103401e611032001103442c0c1d60b04130b8082c100901c03941700c01c0c2d9030340c102c00012611300840744102080e44e04800204440203030482050862000c0889005030384039104142a220b02004500c00310302380440604200c10002c4030b10410b8003411b615103403c4030b20840344c3c0c0d808442000c910240000590751010400031180030710305400c100d9100d4400036050080010b615022201ca40d4001d45c5c0b40140072006200310842841404c4160a0039005007d261410410100c4051824008002d0510301000054180b600c15044036180c1980440742c50355980040c04d04101035002500d03482c2032515004049812680510780c070185955064035031101c244003a48455002c3c1940001c85904403540b0000e000008040358400c80240c5848190200014a01020f05003181e8582d911f0001d103001c0d400c4800b100f5940350301000c0840343d00c0299005160341c2c529014007a907601440007900301d0f0a201c00c010400401203002d589405055a0401c00141d58030204004e890303416 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 787794784 1250 787793534 787793593
    0x40b030d0215041a070e040b03121e120901050f0f060d03030e010f0e0f0105010b03070801030f02060d09050a060b0a0b070b0a020405191805160c030e03030c0d02 71
    0xb0a080e04080c40c0c1c032044070f038058040c000c28951800402c5420f070f13030080e04072500320000d4a514103070100307468540320305419414140d0003492403075808441400c451141281c3c404690011000034032201d00101d085900c80c032070600303415840d800e01c01c280070b02a00003512084400d070510740000d00f40c0055640d80324440c040090115182c21050b8800343d00401e117241d102e04055407286000751243d6400c1c00f540c1d04d103818900003041c08129007058507084440603003008038444c0003002842021030707000c440307a81074a4001c003140302001007a20000d00c0500c244007a103420309082003160070a1000201301c0000f000c1c0521000d001ea121072204000f0f2003000c6001e41800a44144404000705904c0030240d980302d00302100042c54140c0720030000e0040022105030002d0844500c0040c0000c00ca0080254984012214240300d141401291a0000010541d0320030812403910061803d162140c40210001c540c0942034950315120713240d41c280c5454000b62918050b104440384844482c000c0302880c0340d0031004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 787796034 1250 787794784 787794793
    0x1e03050301061b02090c04030203211903240e070e28050909030c2a040207080d060e092404030810080709270f0b061801090902040b030d02 61
    0xc110040e1480b015048885a440d20f8852000c00180c4451101c2400341107004442501c40e07145204051811000d8001c100741150881d9903814104101780035500e800d10700e0031380703010344030b808181c100c000f01300c0424201424076a04e91034002484080b0981403c1d0b8600600b011141e03543c0407030940e0340210040966400104010150510300070840c9403061446504603490450307640d40001580450707050b030755444503800000d09803804100030485c0d03c0c0c0034590365580f038950600350040c95100040c481d00103400780390006082d600f0001c1c20021581044070000e4104081515102d1280d90013100f00c40c0110544260313004014200146c1c030b11602c00350421350b2451495599550200d45602000d89102c400020080c00416428401d1094501030050a480002d04480c013110024510482d8201c468180300340751020004200c1c084141c40c800c07600400000502d44608021800320341100300d0f040a01c0e6071030400411650300c01c0c2c2082403454000c0707805112016511003015101c03a103100300c00c80583d10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 787797284 1250 787796034 787796039
    0xc2109100302161e0b0a050a1d0d0c08160f03020105130c17032a0c09010305100c0e0a03060203010306140c1603020c120f060a02040b0915040807030f1e03050301 71
    0x1c6605854501c21039002900680c0c142c031355285d40100c04140c0700a07481d01d031550b040005403100c902c10b00e0b03120440315000c6101208800c500d01c1c0c480c0c0c0e0001e130b00f05c04c000000808078140a03805003212032004d01001003107603d89031401d001070410a0f10004a006508050101c0c081c401484100600d0720381104012490320314000f104280c180320308164840d240003e200600e11092480400032500a440085480034004822a94245041d08824034422490440180080f400004444191040c1d4130300020b080d40041d041070310240c11403d40315034041b12000000c400c0115503005103040360304c140401c0c00312801618500030500c200700e5400c490900d044c8050700c0a28250301c508a2018003d0041c0c40e18052840040b175a80d0404101007801c0b0751040811002c0b032070741004401d60110040300f045007440c2c24103074038210038802c96400321310a09080c0100c0d0040b501e0001100d00070312031003040701c0075030b980c3e031500d561081c00b01384003070b16040c04850300e882c2e0940350f02a540f4803841d8160754040c511307070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 787798534 1250 787797284 787797293
    0x20d0207050f0d21120f060b031801150f03030e04020f12192901030b03031e220e070908030307140903060c030a0e0c03060106050c210910030216 64
    0x10784401007682d082c1a9104581e80131015840c90b45203c0c0d005a0740c03000c81081510000d02a90700c0200084025441e04904000c1101e0300000c1da6000305428000d003070f01c443c01c000d140b0301400d440c4900480301c0b042c2c4400025401c204001c11405c480c440d807180c10398012a0380c10042280141c250f21001014100103010030b604403003c5403a0300001000d010031500c11603515003800c41c0c035440380200c1c4d01000d4412801e260308829038241d0f45800309190601c90012007001291316030040c607040b0548115804001c103180100d0000317450145140303052041c040c41010800703d400390824442c2c8501d041505000c210564031480c006010394146000a61454551800450300d040c080c1095580041c41401400ca284e501031103154000c455001d00c2d07a4032420800c07064400c481075211224140d62005800c24800e417408a440e0341110114180f190f114940c2c112103900b04540703192544004400610040c11505100c1c0c040c2c0212041038600c40240c7ca1024400d4007240b00383c5104180b160603900c0c1c51381c00075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 787799784 1250 787798534 787798549
    0x2042c0a0816051e0a1403310e0405060402150f031504020d02070b0f07110c060c011e0e070603020a051b031b010b0405090105160f170f0403020d0207050f 68
    0x440c450001c0368400c1484503c00d000c0c04034281351109a42d0401c0014006010a503030703004a1110411010314034103000b400d4084c004180d004134100d98503100181c0c68085030320903c45800282800d96640d001460240f401039200c0e08110307000c9205410501291030000540401d44402d24901c1c9521465925807903d0100e0403002140084d502540030000d41305820906c0c006000b0840c8501e440206038100031100c0b500000000708030200304014030035249004500043c4190101c00141c500c40d41da440051061805002c0000c0140d017020f072420307642240b0440d291b00c800c1ca901815015190310f180c40e00412400c0c0d00c01c401440c0000354040c0500700e4600306503200600c96642e00d404030707807411600c004640840034880c400310901e41d42d240d40381c100174101070080562103440c64000300040d1070305002c01c402180003051104204122180200d81c464001e14000e07146c04080c240d0706046250200901a4924045504400502a100034409580d0000543c2c2e0f05444c40107190004264420080c40b080 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 787801034 1250 787799784 787799827
    0x71407111f0c0302060601020f070b0903031308100e3909010612150302010f0f090b040f08011d070b0a050d0203090307050712030c03081302042c0a08 66
    0x2004907940c251a80010314001d040100c01ea2140c01c084a4103040190421600802e2079040d5000000d800d55845400f08000e01902d0b459110141c0b25511640400e00d54041c003071810100083c04840454154000510340e044500c0c484820300c507840b0702c01c0400f619126030b28440342880c000168680607250316070b8048894110504034408141c04c907200010011030082c0d00000105083c01541ca0000d519805809240034801590202441c40d683c0000c14102d841d407018020401c800129075900d40c03144543c40010184034814640321600d5804c0049840100d1044103201e40c070b403c8040701680b10882001c1d0740c0041c0100900242da00c0c140e48450140d1010b0000c40400204103c80112071100f803000d94040d03407024004540b659403514005113007261603000040c150700814007100002c0c0c0d1051200700710f65454035107480c0342e440701035025000b410028402544131381046880d1415400c0c0900600024001d4485a42d45620b40c802403625040c441e0000303091a84200702d10798010392820001e041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 787802284 1250 787801034 787801039
    0x313120308040b0a090f0b07030b030a0b0c13090207211d04020c10050f010e06061e0d1e140606040b07110d050f070602010c080106050d0b010e15070b07140711 70
    0x7074050403a83c03507000d1071b00b10b00003c4170121038110501c60250351611500b8982c810a400622400c61a502c50b180f49107802016100c0c82c0d03000050a4003030790b14030381a02d001424030714025500c0300884d240c03200c0c0116440c0d51380343c0c011014071280f41c5c3c2c691040c10803c41040b00301c2d1491000c004084c0a11010398412100c2210b80c1c807418014070801b080f10301ca860320910300000340c50749079414001d8803842080080d202902c5280148464480107040340c1d2440b40501c00d001080e580e4001031b1100c0b4014059610300fa074010a903045a140608000340c10228803c09000e00503039443e5900b0f010004c050040303004401070080c0502c4004009442003641c030480c0c9400502d07510070300c0032940c0c0b040e1806044042140c940d03001003c0422029409000b80c400d40e41490400300825810000010124029042024500c5481e599002c4881c0d01454003c0720118015220300f003040e038103084101c580d40c0f000c482100e4441501d000526460300c01d00030000300404054126160030542d0716494042c8800352200c6a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 787803534 1250 787802284 787802291
    0x60d0201120e070f23370302120c1908030403110f0904050a1209050f2806090617010e0402120102090d2d020f0409030306050a06020313120308040b0a 66
    0x5202440c001d00310300140440c034524034443e900025809000e500101140d40500001c0006511144030924080c43c0d021009042d1041000040f030306e0124800d0607440607400a02e02054244400000318000d143c0ca10166111503090411030b14402000c04580f091807425042808280001003000f41c3e005e16200d002482d4244400c420000503040702000e80b41140c440d40001e000b0410442c501080c1c1064a60a05103005007600d000c1c0032420301032103184518804d452030105030a403407a54100402440360054051000c050f1144c401412046d170074003c0101058540c1d05910341c09215541d5941680c48190f5004041d807141c0e800e000c1645401b00001d801c41d50240501051512007040d28403032103000b0841202c0c155040d501010f021189a130188141c9101d880c082805615200c660000034001075400003107840703032418101d00900d190b03000aa800404040001842d507070000140c800351811740c000005035955043d40c4541c0c02140c2000401180321340e030004d004100d48051042d80001c83c01f4011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 787804784 1250 787803534 787803539
    0x1180b0a0b0a080f010605031213060f021c03230108070902090d2a12170901020f1204080706020303090705010c020f03010c110706020712020f22050103050105060d0201120e07 77
    0x581407001c1c0c035004c580c4c2e41e956484108000d16041241d0f0100044c1010240d00e010a080000c07102c1c440d80740180d00900510380640710b041d030710030481022030951042c6540c103048050100103000c0e10018062480ea0720440400c00e4070420010011070488030340070001e006c60307450445c40002070f42002030900d5000b211741400340c012071120300f85481041c030070303907160041d1900d1404004154103d58010861004c001c101800024024400501f1501e440310329142d1245d8a00c0e0040345001441c0e810200300380217040105403504030b018054425103864005898848d903c809080b0794038042110145101e501c82c040411495000d01d800141c101c0c000303071050107250010300200342918501c500e02400210380d03004204903000140803500213014184080c00c0d2461601c209002c22503403111019200c2e100d05032100302140c0d2a0b1180740046562100301007030002c0300c0c035000ca0003810240700c00d50f101d50900e00022464503220303400e00401c541c16100c0404496070001100300400f1080307e1043c0512071301201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 787806034 1250 787804784 787804799
    0x31202031614010606030b032509021204060b0301092001030219081008060105010f03050a060503150a0c030606080a050a0b1201240303230f0f03040501180b0a0b0a 72
    0xc03105540107007100401d500050441c0750840b03001782c1c08101098940a0031000c690340100d40c0d004688540e00404030841108110072000c0400f9a000074100e601c006149a020303604604c00c01d00c05ca0050030100b11100c0800207150998610b54002000140303815460400410150703040c420004040c90300504102403c2034094854001103081008071711030b1820040c800f507001032950b02a002c503001500195141c440042e0a403040382031958249500d403000a0008281940000000e040050449080d1054411120925075003a200760030f43e02e0030182034140b031a01034002c0c5400c0360074607520301c07042c0d603600c20a42001b005d0140112410944030900e260b5182e65086400e080200d10200001c1c803425494049140c001c069515592001d880032001c2022a0308004464010180568018071940d5a0480d403d442d00c240515400802c0001c115100705400c0903020b103202e00d00c120020000e0604c5400c43c003500064070100201a00100000603054010039000310216900150010328265203032000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 787807284 1250 787806034 787806067
    0x212a0a0b030c0f030a0b2d0d060b030d0f23030609150d05030405100201150911070803010b0403020405010506070b0408090102160b070c0e04030507120e0603040c09111303120203 78
    0x58148459441d180410150701d0200490000c4c14022440400084544045484050701c0024030708d11a10b00c980d92441031042641107441841070090580e4104034100304c014002c01d01943e480b000055900700844c140103041c0300030a02c940030860900d419651841308210036075100038040c1181c0300045600107166150030340c00726140b91103034000d5900c450804091000515000307200c4400c681c100300300182545107406890040d02c14a01c1c0100b14942d00386503071042441101d80043c40140c00000004d200803064025009584c4220f82c103000d40e0342d943e002c0184500941802500c0b4407188004240025101401004125410300603210020708010100c0c4030340030a540007404d590000100c80007001f000500d00d1014117480d01d24000e5504040d20001c166025104005100550b0100b8100c81c490180c1c652000d8400000c1445940e4585840c00c50307019081c9105036641c8904007018020341c4444001030710380202e8000c5450103980d280d601c0e0b50075a00c0f10389000d00c3c00c1d40400c00c0308038241c880000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 787808534 1250 787807284 787807291
    0xf04021207081302090f0402010918060807050603090d18080a1b0e0c070b040c180b0102010f020a0e09041a100e060f01050f09212a0a0b030c0f03 64
    0x240e03140c5803440c00d614041c003003820041210140e042d40b240b00c08010790340c0304022604614841811001c9030340b40c4c40140d40190454010f001d1030b04440d0041d071060704250304030a090703030f03400c00680d540d141c1d65106005d20b900050f41c2140c520303001b011012404910441c035405094030502400c1411503034584860341840f1700740f5016288a02100001d420340140649210b006112150001c14280b800d81300d0350180b1b02030b040740244401040310201d010700681800c80d84c00342852809403002d00c500800b890000b880c0307800100f0f0155003010007906074002207109451000000f5110f52010401700020888104401401254000c43d82c0c07491010343d501c4108082d20030155420780c40c03401c0341011281e080800e001050700384107010541b10b454a0766071000c10703110440c50421074580c464040c240000c01c103c030f08940c520205601700303000a441d140002410001130703d03500100e205900003a0740f0360343c1d00c4c240303039414941003094010100017403c0e020b402036a000c1810070f90103080c55031520321809241d0056 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 787809784 1250 787808534 787808557
    0x6010c0605150f090108030304030f020a0b10060f0801211505070305041b05010e0d0201110607080a0b04020c070b03100f030803010501090e090a0605091603060f15030b13020f0402 79
    0x240c4980c0b00609000002c901510401c451030000c9602d00003185a4034030004000a04100d803100007040c0181c000c01c544d5652561010795100306207041c084241c281c0d00d5900c129000607075400540d40d050303401482201c3c103940580720854150548a04070903c00100d1200444036140c2d05070f030181421541d44a9140200d440e03070350200e503d003094200001d03c80d841c1502d0b02152142442c08000726a0015117101d003608080d100c6200c8204a0b000603900d2504135440101c49000306000c210007075a12410b01c511030325080e081008100c03020801d110403401800001c000f6a400351200340603d528803000b4550007103820030b5034021a51035089100340c5e1452507000711500740010005226540c0c120052402910034a000c01c2902d2614086190b41c540700034a001c0d1810b80c2d02c40211781c0e9502c0500034000c0c803141d0941116042c0c1c2d0f581c60a14024034503209200e000500d0681074080d584604014541100c3d00b00301c071101d107074482c54000030100e08058000c991092141c2100005500c40740041c04400204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 787811034 1250 787809784 787809811
    0x18100e0f060c100f0b0105031006030b04090609060b0a1223070f06030f0b06210c0c0d0806030c030c1003020c010f111e040f03030e0402070f0c08150709050906010c0605 74
    0x80b0209105840102c845c4606004080c0100003002001c001c1d04422141113180119410804a01140c018208010041c003c582407080c031409200d0340341c00c080307200d220903200b40d1040c40d981e41d00701005088044001b0600a100310031500e2a0700070f0924403110071052815100019034840000c104519241d1044020035220b4151003ca82030a214805100c40141c03006031170a800307000703408002d100c0c0c4085410300c4449080400c8401c0c48980c2625280642d12049030007200003140e024010300300484086101c0d2107040100710f038074103022030007840340705010703110010488010f1001c3e00650480c1400304115035a54550800c2000c550066080900c002044540e40315400c0b40c1d19805450f298103643d00a0700c080004002c08100c1c525000c048940501d0b20a002c182100c002502a110b060405400c2603405c2d240f5005200f500c052040071125204125100c6401d401e0403903a4581c82242c4200101d041094104040e0905250b4980e110304145421245142a95070f004115101039078408902d042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 787812284 1250 787811034 787811051
    0xc0a030f2009010512120d0213150804020d060908160308090606101112030115090617070c03200c242a010203070518100e0f060c10 58
    0x40c8032801021648000141c0012401c25101240041c10107205550150400c401000b441c3c0505020406030404600c1d60070f59a8403010003458040c2d0804122003249440e921000035150040800f032a400350204c0c0c8850190350344a4080001100440000380c501c6511206a0400038400f44001d05440c4016499006020501d0800806810300101001402da02c17520178005140e58445000c4215445440d200030b0038440281000c2c03c0c100810807052009070088000324119806d48100f9003680200d54034140559a0b42c00c04035003d2014000304000d112914005c9800103110b4810b508541d8080c4c108515901c85104a60035040d00001d01ca0400f60411700012695180ca071a03506070041c1c2010988038810113080610351603200d01901100d40c89020b44c6d01c10604520360030800940d0f00f084000710340745e2618400107030041d409010400c0707103002c401130302d55251b140003548884021000d5451440109401090200701c2e80300712047e56000c2420b210381c040b506400c000f1302c00088203c07079021803c41d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 787813534 1250 787812284 787812293
    0x60311210421080105040c0201020405060301121a010b04052103070b06030d1403180a050f0a06050a090b0a0b01180f0f050301020309150c130303210216030503090c0a030f 75
    0xb6082d640c000408000318031440000f580420f842d81034900c100c50000b07000f0400c49050340248140e03400380e81c1000d03000c030002030400c120002c0d0101160203100303006d00441541c4101030b0702c0c0100b4050440300c846c041c4018030413403c2064806003401c0c004a480000400308404903440c50300f02d840d04541d401581d00030003110f4141030050f00700c4020503041c51a00c8103881401803541c0e000003024250400754084a1704081402007000000c081e4000065800024105104c0c07500c5010340841980c0082c03d0001040002038030b4410500c2040c0c22401800d184e0700e0f002010005080a10044c5040020360629200c1d40781220385160002d00c641c5949070a25072400c6c08018050040e070f0301c400e1083c0d1050040042000b0302256500010030808510002d954444c515000c0b1400391030381040c0080c01c1000c0c00300c02c01d5005460400c0d201d003040d10312041c5086400e190300031303807040944045c01200f01e03a894400090203040a55005200d981c1542e101541840114440c013a00390300c15640314400305184030910 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 787814784 1250 787813534 787813553
    0x90312050c070c05012105090114010308120619030b041106030a06031e030f0f0c0f060b0916090506071e050a021e010f0825110f0304050a0603112104 66
    0x2d1101b820003200c0b0b42e01c3ca5040f440060481200031101c103861781e0009104400a60208100320741d80c1415856030351f1282000080c1d82c000011118900c09040b000c50268540b16421500e02c0d20032211400704941541d80b1310341040000b03032088034a12101400001c890707a822001d5403017800803031400034007540342d418460b00c11150b040c4400a84141500b034200800e41c04060f440000324241003541546004110485016122010113865440b540040004100d859044031003905e90895400043e0388a03008190341c221041d00d4188041204c1c0c0b04200300c10b050520103004c2c480c0c000da0a0415086071002c0d4004007041145080701c0c240c00c940f520504514001030a040350340d4003140c404032440d182c9400a00000c0e550302069044c0718114000450450350b83d03c0350712030190924804039a102c96104080e00d5002c160540e408240190310a01ca0035510000c151402c88400401d80c1e50614070b40501039008200c0406100316118042150f003862140401d1812446000d10f03901501918144c113040b920b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 787816034 1250 787814784 787814789
    0xd05031e070b0402040c170a0b0406080c130e070504060806011a07051f1b0f09060309081204050109021f120203010e191b09050312030903030a090312050c070c 70
    0x200c034030601031400403540002e4060fa0241c0d0607100020b40c41e807140400e07640200c2186480029403030b62801c11403458030503044046001130950703060080f039494200954030341184210680d000300490030000e05600850b0040c5940303400e2442501d04580c1c50300301007003e0340c0450300000015800140100a44003103d02c440c14414080010103050608550308c064a80e02c030b90440d440e0390310698882c851050b01d03c3d0701c80020344040d541c01d044070310340e170500107807427051440c50f004003082c00603400080c118024080c0707803403103076010b8401c40c5840301c10355400949420280060300c05641c3c0b00548001610741082900450580500c0b480f40c1010f003400041641d4090002c0c0c40203140180700411004000341c0400c1d41001051900710810f6841080c42e00003040c840d04c040208140e20340e0100b20302e07500160300c941907d00540903280c000c207500d1000b520510090b24401080ea000b000003d024240e260301c01128a0320a10704030f1080b080c03001c10707441613a2064500106203400007969504005200c2e050000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 787817284 1250 787816034 787816087
    0xd1d0705030706050c070909050109150506011b0f0b04051c090b070803071e030b030f07120308090703060218041406300a081308060c0a050d02090d0503 67
    0x21290400c00030a0b1100720342e12544040c0500400c655103421014044100039200524080040c1482401c12a010b04103000081d0b4070f41c4440c1c1010800b80d669130081380e1240704180c42c1e10704040e01651651007218040c02059400d0300c4840710010000b0036070b1107064081c5015070300070030305c1b9400c40c100004c0d45454080b2800c18003401800800287c81c0701005d5607096500101010740702e540c3c502d401c0e43e039800106990304a10860343d0307241c10079607055481032003240c0301a0100c41b001c982d1040515030f585254010444008a800d41410000c1d100740c1f1101e80c000500c0d8291098155240c0e9000e01f40c0e04100e00080c0c2a201d00075510342c49003410b1091000c030365100001c404150501501080151320b445036031181c82e0140da0310181e20a0302c150102a14204030400b214801181c90800b051306410514000950115004000030400800241180038203d00c686440c074107580b01d0310a950a40c4000e0400000a4080c00030440a1380c82000000c002400345016540d1480030000e0b071403081f06108150365 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 787818534 1250 787817284 787817293
    0x6090c011413170102070c15090608041a09190f11030319080604151206060503070303120b0a0302030d020601031b0e0105041107150906112b110d1d 65
    0x3120b11880e00e40707001201c0c055603206031090b000c002a0b03070191091400142010000c401d0000d50010b645142d031441154030341d41c00082d10345400e011138501d41d0039900641003d120366070134410502d03404845c2d50096071403022a206100040e40290300c1c0c018030b0308143c85400c10104240700f17003c3e04945140c1660002ca010f1864032041c5894070590f5101e0086040420085000082840d11598000d0320301040941c416003803140d94164000705403a070b003182101da050030300300c0010b01030800003029000c0d06d0345602c03184c00c9955240b0510009180c14103416900000f118400409601c1c140304a9100d0340040d4041c140f5136045051101102e000c58808100e5100e454000b0043d0042003085207054031b40840b03020402541c03007540360318036010f40000030b890044c00048172001c6c07241a901c00f65189104100c06d104142c000f070002d08850107a0045082c003030450031900440700305224490134541c4444d110011305c02000c11800b01131a0032900000030a285d0355000c00021400f60f50b44a09044041d00050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 787819784 1250 787818534 787818547
    0xd0f0512090102030a2109050313080a0b0c0307210c03051f05190f080303011a03010b0d09062702012a0f2105071a06150a030e06090c0114 61
    0x130341e02c0c444e0581a404015000304501080481c04805452851400400b84503884090400d81c0e180da21200d4500402031690f0070001d90b02c103011a400d69142e400c003544c40c0380c95407011202c0b18a0750000340100200814940b0a22030041100a40d11704c08101032000206111001005000c44d40050240801c442d501850b80e510341c9040c0309404e00362070003551680c03a50840200004150300c2e96800083c42e40c180104042060103000002d0f504130b42000c05034070006d001080d00e08449120a01803c042c008c810440f54401120390b0b003049403120311880c0c000981c08082140c18800000e140700200480720784043d214259a0b01100302e019004004025140d4038003000010f80700c000100784002c024004c04140401803014003152a411610038960f2054001c0c00c1c050020305a6000c440200ea044240c00700303a904030169107115911031100501050710b984642c850080b619008100302d402016111070410086400610240b0f002c0c0300307200c00910405540c0c90014144401001c6c01c810414014400e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 787821034 1250 787819784 787819787
    0x40b0601030e0c0d06180b040302160308030c16050a110a080c0901030605040f0b1f09020a02070b0903030d060f08010e0a05121b0d110601060f051206010e0d0f05120901 74
    0x1040306202048406400c80c042d81e1a24102030070707114140c11401c0c20f2040122040c4061100c940e840f0b070f0f2098ac00c0d144601c110581c2e40c0300b0590749000c042c0c112081800044e101c5001e0350300415603054079000d100c0800055541c1c0c14508002243c00715440c0551210541803805e11b2184840600200d070081c1410101a0001c00c40107601480044e0059494101280c280007194200880c4141c10440c1c2c0c1006181120110076800340000c00054050031402d03002a10720040e01c2506c6940315a41d020302481441e00644800c0c50b001b02480c0c41c4c1c180000c10003808040703c05c2c403688004200803810320a100c1c1c94402028215a0340500701040390b040005520000f84010558800f00e0000122140d150b4243c0f00d501043d0038581d4400c14018801c0da018011074903003281e42082d031034200340100c41d5641c0c7c0f5104105c826251340e640c03102c08503030184011040805c100000c140d020406150900e02100000c0026101400b180000c0c0c0f0309034080200b00307081c01303400c0c0f24140001c10b4004009103400e00c4c4900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 787822284 1250 787821034 787821043
    0x2030607030c02070923060616030e0906061204030c02060d15050f06040510111e10050601020d0c03050c030c0a0c1403070b0415020708030a030c0e090108030301030b0907031703040b0601030e 84
    0x1000445040c2c2c042c0041c07e81e6030341e18203540021041c0d03004c1d040007414500e00980000300880304180303d25403460000e01245460421105400700d50149880d55841c2c81d0317029164045803100490380040240583c1e003801a842c8503030000d000c13035003200c510314500e4081800300d03500860f14007a01982c000c0005200c02d48031400200101304440c0740ca0703d1850724010b001410318000118402c490903000c0c05259640c00006001a04114116001c00050312000d005a1b965055044c42e140425044150500800d021b807002e40040c0440d0b0307055034a04080c0041c21410000c441e102140e0980306450103108041800456085006003600141421801d020030740c4007902552007102c0312007000e460f00501c001d20a0040e44000d0044508a0f500d1b0501d948015014246003144200000d20b420100d1a19203001c0c9a05412a070381c24015526590a507142d184404100a1030324880b4441d0400020000b200e10a0800503d95804c903040e499003084e1809091802c0301038482c070f040504210200f00391850128 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 787823534 1250 787822284 787822331
    0x80f030405060f13121e020906060c07030501141015050f0c0a0537021f020a0507062a0c17120f09011115070e060702030607030c020709 60
    0x210701d1510743ca0300e41c1000c41188107a007030100042003030000c0000c90071501012608a144620010140503100000b0100076008541020750b12031200d001051050030600d00030062040d02d40f040e15132607501e03501c7e00c03030a513003803110110030142080c0308200f1010000c004d110040c2401d00303009061102080c070001c005004408410001120000e02d0680038082088819852a8000182c80700c55a6146900418640384d06c074404105c0d140c8116403100804106a908106500400c801038148401c840b903510503010b03410308403e40c482c181640c1e0110b4010402d000003400305a481101094208054035603040d03800401601e034050071101c0c0b000251651000c0425504c0c402803000c03d0004040d2010700c0c0c204266043c582201c0000740c001d0720303101d9800090800503002e032a001c5144141c8140c0c2581c4599200415010500e550040b4500522808100143ca0b4000b04120b00340605500007a08000781528000b0110f50b50b103101c0c0722442d80500000b0000c12581c030040288080140c0c0d2034541c405481c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 787824784 1250 787823534 787823539
    0x110403230d171314060105031209031f060308030103060218101e21060e16050d1e020a030e010b060309030d0f0e1203010815010b0405060d0b1216080f030405 69
    0x1031000652140d10000f96025254200109030b1030440c014809a03240c100030300806009005a01d03800700c1301504031045800000000d00140080c0d00b0402d403241d0301c012000e009880d02c1d40c480c40000702084041e009035021703500880005940b084c44000b00c1c2e8402c9245032456000b003001401c1c280010b60441c0c04a411a59101034101d10000741d41003c0700d4039400480642140c07022017401c4141d000035644404141e545040b4500e10a0712681c004c0d541c1c20641100316800581e04000c44c602101c02ca40158589101196200300d8000c00c41010b80c0030303a088141440d00007030352800c00c400640001d001e1031181e1102a2500c0b45103040a00c5040d1f201c0c82598071b09c0c281c031030710f0300410801500e459200364402e070605404e07982d104080381c0070107880e64400c3c461514076204001f04545821041001d050407034003000800c43c81c00d807400c0244012600007075180c04419a4074401010507440e0505040760f00340c0444041c0c60282d00c00d502400303150450703400c003072002d500c000d41814010800000b20f805a0303408 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 787826034 1250 787824784 787824827
    0x15030714120a0506010602150901020c1f060509010e0a1a0102030306100207050a06030903110304080304051219050d0f020c0a0909020d05010e01020301050a230103020a03110403230d 80
    0x306410350b1800c002010b0060052044400011b0b505602090302c0144c0441e03820180741684030258494242d01a02085140c0e640000110015900c034001c0f5500c83c10b032036040049143e60351040010600c1c0006d070b0000c114840c5000421843c00c41c1442a00d400300c0d07000320960001000c2c500001c2d40d9010041c082c074011411400c100ac950f9001b0025540106801882410307002c0c1c450000401401b442101180483c0c0c2c404a600005480803054074161120030b8010350600d0300d0300c0c041100403c28240d000c4081d002d42c0704400d03001c10b260390f05c04100074003410040803107150050008000320061104103003103402c040441c0500d40d50324424841140c1150501042d28807140c000260614840d40780203089620f4064448492081074002e18100c40701291414140c907038541145541050306070342410103600c3c80e8250425903009074060490301d85249000940107890500c042da1a501a800079103141300403000401542c001107000d1281400e00c032014000c0800c03505009018400030007000400380c9036 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 787827284 1250 787826034 787826059
    0x102340e0412121103010801020c06071409090c0903011a0a061d10140703171302010206070f142809030b070c020f0a060c050c1e040b06071a15030714 66
    0xc0c3c58010015540d46280300c40d80c0d0b0750b5101c0c0b031903000f03510204018003903010b00000a4401802441d09140c04040180e80a1030210407204000b246800188034880b1480705000d9542a501c0034810701c0d4450b105c0422006000e00e600ec10000301c00040d5005400304044101c0203080d101c5403c40c0f2500f9071806484195519080301c60942d046c4004c1003d80700c0409004c1015030501d03900a0b0042011002c42034211010341f0740741c0c5c4801107040700c400080c2c050b91040c000b08500301d201d8116290110740c54501204503070800302041e4500e500c003095411981c40302801400c039240207868241603d4040c0e0038141c9100e8910b03541d1a0048000400039030030b20441800300c20541d181e02c0d4070300c26a958000c0480c4002c1d40c4030341003c0c3c6144911241038a492083ca0a06003071414030713201004a41420f014864001000e000800000d0144006000d820041c00c0c001d01c400543ca090b2404108002903085d08814941103401400c41403110305601c1c883c0c6d100c0c6200300910038400c2c120390b82d1900150740c0f1005000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 787828534 1250 787827284 787827317
    0xa11090f0d0503090402070305040e07050a051204020d14010c0e060306010c03260c0309011a03030d110f280207030f0b06120a08041a090901060c020102340e0412 71
    0x183c400c4c1c80e800a0001400100b015401001001a85d4607042d45c0180e80e26030f4141100c142c081e170880d940120300d08000202520455070681ca902c140f0003800f8001140090380c40d4003440048000c400c606a4461480d402c2c82d9402005800784442c0030f8820f142146401c400007000f80445a0003d800d00401031006808880040070406003e500d8000d516400c0c102040307405c1840d481210b21081f154644205024135000240301c00440c004e000340114200030f910380d0710342e00418868a102a00800030019500d40c0c0344200c1c090301c04501c0000007a030880d1048009003001000c071030ba15804540041509100062041e144403880d2504182040550b0b907508001c1444111500c80303400d038601c03501c0602c00410010400401c00e40390441240316503280c0c2490110b2042c02250314255002102d100103114580c0300300032103c4214014811290355075125200310070210400105031143c00d110441100c4400c406c0040348008003010102c5040034640b0361070341c074140f07a100031240c010001c441c0040138401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 787829784 1250 787828534 787828537
    0xc04031202120c071d0402220e0a080a0f0f08040303050612100509010b0f090f09010b10090f0f06052d2d0310030b0a09060e060a11090f0d0503 63
    0x82103003002d09961545080c1d001d0380e542015100e0a03401503c01007032000480b03140010a030080c0d03405419003002d084484018402502c42c4841c0704d80c115940c001003210490204101155031707000d00c180c0351b82c51001440c001c0110040210f501c0601012115503004158072041c010b40c082c5d01440d000a194660500007030288000502d0404103102d40302100e09120100d90002d07009801c100001c010000340d02d0240300010a440c108103500c000e0050003c0d0001c1554052643e0150740c4e54000101543c100c0d000030f040c4650381c207000b8001040039200348151002042c440b0098000040e650508915080c0700414600c100e0988910041e901d5a490b0444c180d00c9040284c08107030802610340703d0014902141d0089116080c0e00e01c895807208052145a10800c2100d0103100c01c9402c035000300f0b04540318650081c5014201800c0640d81e0403411011400300c1c03145d100300491500180101703090115060b000c8d1400c0c403140e06003a010421280034a641c1e035013002000d402c000e8072240031040321030802c02d056 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 787831034 1250 787829784 787829803
    0x1031b0c02031207061401060e100804050a080301031b060503040b1303090509072c030d08071806050301030b10080c13060f090b1201020c0c1203070507090e0f060c04031202 76
    0x220340700030500c030041208903040320890200003004501b80303a0307803407004880442d418200e050304100700d0038011141e10704c94910f290303100e40a00100d810300e402641d180360b41941300f64025030742c1c581d400c9840400380380d541c16010001c0c5440d10309503045013000c1c0c4450303141d094060702c400482c04802c0403143c1010302403c075039801428010465401391926540140002090340c24410042c04081c2004440003105401c42e40c085501a0042c03505050300300d400e49036038402410400500014014003a0700c6110780201c14040c01c440e075109a05c175491894441e4038448043c00c0c10b40e81d151840350611645400164901c40c588044450180380c4041c010310900605103500321052084c0d400401043c0c0c001c0e036401040c103c0c0015904440707140e40d0191254200d00510311000180d030080d5200d401d42e4a0046003600b0341041000541e0300c0d000c0c85035525441d003c141e50200021b10b485445884040b40305018a001e0407080401911030ba02e00f111090105100d0303400020240c0c41e03000b501d0b0320401d00c2040070154 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 787832284 1250 787831034 787831063
    0xc0218180a03050a1112040b1e04060306090b0108041208130204140f09060408030109020304021513050f03071d0a0e0727060b030a110c0d09080c01031b0c0203 70
    0x18404800d060050065120140f130303601040d003102c2c401d040c04400060784d841700e20400c1c0c2d0103418a03081c1880c400303059202149000e040c2210144c10700240c02c20300d00400003842c0540700000c14920305843e08040d2200003000506101625042001103580c41e2008090104940351150717090b0740e107401c1080510400140a5040b03880c0c060246031105c030200030303d80540310800000c480b917501d545105585440c106d6006281d100c0030b0004101c0683d040e00503540080c8000c000340b242c444410a0074003ea085001c0f6070040030490a0100014101303440041580f2500b58041d005890074150030000c803c0c482c139010600c488494000460321081940204e40201080c0e09452101d903a6210b107107414031032411000d02e2059088203030240d4054500c03c0000b12180c410a82d8110b07561608090010040d0030710040001104201c21845040d050101f2a50b01c46a601d40b804400d08014000b4908010601443d043c0f501d0a08621551000c604400702e0b000b001c0e15000c02c400580b440131a0428074185180318 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 787833534 1250 787832284 787832293
    0xa09020d050912160b07021915060501050f0f0711030105040317070503070c0f30030615021e0102090d1202061003120f0905030a080405010f0c021818 66
    0x103640000c990411030140452804442c8010441e84010f4442c1c8502c113945110300b0400075005001035401c506031640b000c11030040d1108100703100d00324038281a0030700b012513803020b441151a10000081c0302d8140909028a4417505154101c241d201d024403440c5040f00c0b13140004500702040050780c40c6490103401000c0d00a1129040c149000b03405580408091031070000c4950010300040c3c429400d903403154806030368038412851035880e05a54603511040c00c2e544131400c0fa4a805a8609460241e03030801450b4a5140c01d00880c214001d08840341c1d034104000d50034080060088950303000902c040c1d00b00740303030841a19400c0f4000c4540d00911450385c200380c00c003158044000a00054580909418a40f5002da03a11035407001c0c81a10380c4141c50000a10130310707418003600c0341180b180f0f000d094025100d09120a655440e84000b030710304404010202c8260b100020140a02c3d68403903402c0032007240d54100355403198480e030300103200e02400026041c0d040c032440300000d0b80c0b89c007000160390700c14a655080d40c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 787834784 1250 787833534 787833547
    0x918080a0207030b011d0a0c050c0607020d1103040b22090501080c1c030c0b0a020405040509160b0a080c07060212190e0307080909100302090a1b030e1b0a0902 70
    0x19480b4200d0307120a4420f1180d000000440c1c5501035400c07041c080050b044032500307a032484203840040200019071802c0000911403008404000c01505000c2c0d00d50360002c098504c0702c0e10005050314903103012552290400d00c0200941403411040d21240501206020449a4001d2140c0c4944486510020340c20703050030b000082102000c26441007808054644c420700f620b00000604001203280c00003000115000d0300b0340d0111307054803145c0e81c1101040001501d0607907100b0000c0c0039203030306540c0c2c3c0c112504072158901201000001c02401041c0604d07841d400d041500030041c01e1804000c041e00340754100050700720100621a41168055803201c101c1c1001400e0521500300306000c40880c4125003480c0c0100d101c1c0000f80082620340e401d41c092182d0740b0349042402849552800a80b80c0848800c6640c0d022006079100100702e44074a079000000540306038501c0c050540c0c5c986250742101031500e000c84050b00c919003c24814500b40c25401d0103140c2c0c90003000440c030110516071111450a02c082030b503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 787836034 1250 787834784 787834787
    0x130c02031c29010804030f20030c100b010f0806030709060905042f060c0309031f0507180e15060412030e0604050d15060b070606080609070308040918080a 68
    0x2c103040a481009480000007002040810a5180c2004030f003c540401e00080000307102d9281d82114443c20b15003a01c07144c081d9800c0700445400503500f030307a180d0008142030500040420000c0000b06c5400001d000c9070404000107403040040e000305908101030180018116101042201e00400360b0a004015490369014400010107050310220f800005180c600210451003a07041d0b4108500c4c90110740700a12034504001144e80308455001007030105002101a507541403160306942404090f40c44403460f18041803c08403000200078409000740740d00c0f4080b0307807000041c034030003555202800d15585481c1d489210a421b62001c08044d401140050302261210003034410340d035041e119480ba125040401c00c02c010f418005c1d40035041d0004400c09206021510070100c84a864000074000100503484c1c0c8006811907101501c01c0e42c250307803900410403032103d0030400740364004891009050300c00d046584158080c482e0b40b0649003016250105407020321090030300c00d00031036030204980b9504c400400c030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 787837284 1250 787836034 787836041
    0xa0b19030b0a0e04020f04051b070c0803030a090b0c18010e0619121512020609010507050a030527010c121404031202060c07380a09050c0f130c02031c 66
    0x13012409a000e0480072503050504e0b000d40780c0903209030b0354001c1d10807012800701040b6401120050b42c11300c040e03010020f000d090501c015400390008041c0400c41203428104848d00c5030020f81260b10b0300360301b00b041220741010f000142040380001d01c0e20070749444400000407810700441200b0308101ea00302c0604840c080c0c12100c81c401061a00106210035141c01c451010020401d03c6581e1228440340d00d050b00510340000100300603541414014108242c50f101d0764075000e50f1440c00c0300415000548404202081c582810007520805030021402411000081080500c203400030300740c0744c4078094030020a014501c1000702600107110b0a840b1956401c0c0304001d01400b40702c54015029010110b034000c10f1800c200c86007546c2041464545d1802809031255520022002100b55151060110010364002c046180a1400c4220100e081942818503508284021000b980700f406e04204034091a1611101c0000d1844100b50001d086e0300220fa0590030361203160b00080803504c02000c810b040455903030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 787838534 1250 787837284 787837291
    0x606010e1017073e07030c05061e04090207061b050703080402030102040506070501140f090d08091603050f070608130803060f060c0a110d0201200120040305010b0a0b19030b0a0e 78
    0xc904c1028405501d4215855111500000e02104505502072100c5e042010080c401d119250600f6000481895541d51039074110341c1040d241c3c41d40000708002400064000d6074840301c43c41c654042d9581030524080d10310b210301c20001707040c8540d40000030103540d02035068038000c00c005001c8a130f07210002d2820394028907545c48600618600e03071010038514610700c1081d074031074404074008000f0746180390341c2903078442030013080c9000350300c1050302e02c0d004c0c42a240d03800c0008600c10b02c0103004070a08405503a05110b0301d43c00100800240c08100041030050005034083c42e07030082d8400d5a603848103004909090350640103e50880000150001807690000341ca0b00e12a0180140030b6030b03030308048104940303030049540181c00107200c03e40b40c400041c8406407001415020000020b07210351b031941c400e9070340ca10f004041d01d000f01012a041003800710a005481e209801243c001c1c081f9400c0001d44425405048100b0107034240d030541040090340258040898041c000b010443c00c5941c40c03200c20300d010001c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 787839784 1250 787838534 787838627
    0x4060e0a1e0902010203040e220b0609180c1507021008091228020109151b02034003060b2b020f1306080606010e101707 53
    0x41c104101000741900c28641e5255059000e549002d01d0300014004144001d800c1212554000a6400007000200b190600d420f22810145040d46810010800c00d0600100300f0100c44c800a66240345078600414040c40c1c61004640045c015841020700d10142d00448400a400044564541c1141030300014082d02c200c00003c1110382d0300c7c0c03800300841900d0041e0680c41d040240621001c01000c03645100f036800d0021544000030b020a1242c072000c4089582c00216486c091359102e2141e28402141c041054800c0c4500003940381000d601c44240070031003011140003000041e065004040420096446594503844480d0384000b6200c3c01e11000400c600d02410348103802e41d0b0030038450982010000b29500030a000c2e8400804010380074044514540010a588200c2005603024814502d00c2044083c000440050881e0300c0e0120015014801140031503102d10840031200c002158450056034491203900541c0ca25034840346815141c18040300c01114113001d04074050125600c408140700b1040140c0f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 787841034 1250 787839784 787839821
    0x6110d0816020a1718010c030c030e12061f0510020703060f1122060801120b0403050c0d1101140405030304120e060a1107050f060406050f0c031909090c1d04060e0a 72
    0x1000040d03a1f1589124001030118410400900c04680529491404204041d0000c0e0a440340700c20340509045040310014031300450b15405490701580c1d402b070340e00945010b60b036105040328074000196070382c039491000a1940d51299481d01c6090565004104ae0b510f44814598a4444414050260b1051030446020a03c0c030400005407040c414501941295501903030300c03041100a848401442c2c800038019400e0080402240c500c966042003080d03000d41aaa4445a4840e141200542512410450b02010683c0c0000340008100084200e0b03070007a90000b80380c203a0010100e4184c954510115030154000c00c04035a54060036040b81200540a12031000c0d2103d0319100c1081251890810304c1042d08514184010b022141c0aa80105254079928511506044458603043c1c5181e0000e801000003880300c40c61071401d150012040313805000142800c2c007e11a00190040109080c508490105c00e8411100c1c0401e4607a580301a02520741001c48100f1403901010400161451740d00c1d00040891 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 787842284 1250 787841034 787841077
    0x501050907150f181202240a051809010308120a060609090f0f0203040614160c0209150a450b2806110d0816020a17 51
    0x140800d0201c180c450166003000062244070048031900c0b8800128428002400b60352909a0501003050f401840c041c801100383c8049032040c0f2800b44040ca0b08034505c40e01c4c402c0210150390124069641100c00d43c07420030f841e4940603054517590282c0711040d46c1c0004001c0f0020040c400031100414050303000c00700441d1a038a807c04101c1c00c8134054810000042e41d19002807012b0720503074218280c0d403c010030020844008a4080381d04a030f00540d0102c6800d40e5814040c10403104640c851a881641c4c070381c800c004405600c40150040d904079000034800c411110005035951f0741403104800360507000d13192481310740d125080d0388001c2481d030001c00070b460041060f00c8402e017003c0312415014070150b820300100d202c000364280d0152040da13503402c0e1720024880c4040850191500ca2442801103440980107091804002414106540650028580280c4842200e0359000440190441c00d0781d481c0c902d034000340190403424149030f244011b20090500000d0100c00203054043c1000c00c10350f0400080c00003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 787843534 1250 787842284 787842301
    0xd1a040c06020c0a090507050405041a0901050306040c052110060e0c16062a12050105040515010804080c030d1a0405040302070e07051b0a150204050612040f020a08030304050105 78
    0x1000c0e49164072008070801444202429000076421907008e050050030a501c036000607007940e0042640c804009118400c01e10685007503d00307d80104000da014040d6400c140d224280c0c1c400d01c80c0101030269003000e1515081c42c40e10002d10340e00307214403026299880000011540604190b105503a08000c035800800c21032004c030802c0b106841190008805000300076601c1c032003c3e200c05040d030040d2841f00444d50240e21039168110100010070380d58004810201c2c402030040300c8040c0c1145000354a0309007004407542c031000301c21610300d8090030810350035070703552420403c0303403050490394401c0303000100392450409055084030b103400d02c03940201000d00304801c0c00c2c001100da085401900603401003108020480c0b012000c00e41080092a0040c5414160040e40981408403010b81d50190303c1500304c407041c400100e419000c0d01e10420360540c038080c9848001410780c0110110442c580090001050801040c03600e00040070740d010307050100c4650340d103a107152603400450b8191640c0d400d001c00a80d421 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 787844784 1250 787843534 787843543
    0x50c010e0607020c0405100b040609080106140f090426040e0105040506061603090305030f0d050612102f09090702011404080901030e0625090503030d05060d1a040c0602 74
    0xc18050f402421141c00725420800a4840908401c10400c050580440c0000740c400023000605540d4507102c00d140c0c82c21100e2400c4031119800b20601d0a92040c1c05140c640d250020807250401c00c8804115a88542c100b03094012134201c4a0744501c0c1d9103841c04100c0f0b5500e480904100c5001e0340e10401c0e03030703070789c801c280400c2c0c9508881042d0710110802a880c1c813400070350840754030349000780361542c4002d4407981e606180d90b0280140308581080803030341403824605802a5507120005881000c048070040d2011940c40c6a0000030450198403441039174008e600903640741c0c25040e041e04503a030100c000e44002c44110344c00201e045008a017004005400c107401402841c00c41f0200c028040d440d950385131101c41c081e0b00010300060400d5156006070011a0042011030300a110a12802d05164000d080e40c0400303800c580c461a05000040804002983d0048103480d034511040c1d002040c156030302d1700003c151400070740e4024028a01a8072460b4003a01340d4401c00d07c101c1c4582c84c40000513803104010307a5607 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 787846034 1250 787844784 787844791
    0x31b121211160804091521020a1404091505062805090606120708160c0b0c030411030307081c06050f2e17010b0c030711060d020a050c010e06 62
    0x156104110100c0078a03404280b08048501594590b4203007903e40811030256601c541c0b030b541035000c4011050128608508007001c50841c980d8a24161003401d90206101d1071482c482d100d84400008054403035910707a50029611554001d580d02100054514000c00911060714064091925290318900443c1d01d54a800d00180c0d9585100300654902801c00c52085001454271744c01032020300c0700002e104550103c550144815440c2d4002070300d0305520980c004244208142c04001b400140c2d000803e04000e5902c1d000001450903039901d50341c9041240e4641080a00560140b03c009001002c1c003c80ca030152001d00709882c040424034003440340380700c2940c840b40640d43c0d00c90582961101d561605d8203800c0104806041101c00c00800e21a83c0c070064a4411441c030041036005c81c413101d40018092419015042d603007405403c104001400f180e59000b01c58000705040600440f40002e0751310f59060f520024000c01e025981d440c8224401852904002c0d01d0404175820280140303622070303010888a10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 787847284 1250 787846034 787846061
    0x612060f27080306031204030f05060c0a0903030c0203151e07090b090d11220b120d080c07050d120b04051b0d0e030d020306030f070b030c07031b1212 66
    0x8011500742c49440c043d42c070103003445038141306142a140706c000c2508040d0000b0342c002c880c07100c0120b80724100700c0d04062004040c580050301c20444e0b05101d58001841c2c03015640c051401a80c08115480413034504400c0340f000030301080800040114520210b100034890411020b48604a80c54450083d43c004015010341c424851050028901d6400c0601c110708100d4003410070007001c05a21000b1450415194080b907400074604400d40c4400c11a81c018500d42e00c900795154484661294010b41d1030700980d0f91403e0410815038045159103481c02c0039501e0413034002040c7c844102803184081c0c65004032052602ca0700c3d00702402c00029103045c0c4a154030074000c000314000e440340c03580b0b580c068139030000d285410403903944e418801001104101500030a0466000142d807410f14504052400d0942404070f070700c070f60202c1000c0c821240030105490300585484030541d1142480e1905a905564607070660740c05038591031048080c07111070041c80c10a42c1043d1034000c200100e0385508000d99403040401b04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 787848534 1250 787847284 787847351
    0x601081b040f06090b2404090e0f06070f090b03040b0a020a120501031a0c1305010309060e010507080403180e04021c0f0804080105061e010305060102010612060f 71
    0x240c480e05040c4440415030000348001200c4140340c020314200c0761150801040b40e581c542c0c00a8481c00c0041d044000c84054040300311101c20384140b0000c3c18880c5014001e8103e450705401703040e03880c0c100540c04545502da4107940d83d078500007100602003001035410800295020200082c2e407800102228041e0340c2201140380151b4030040e81a001c3e5010720490000c01110184984003802e040c80b03118061442884800c01a48003101c04000e8200060114003600c0820048101c11056401400c42154004e00300807a8400d4942042d074014284a1112840c43d42406c040210281d444511107120300d01c00e8807450b0001c40107504a07403503034041307000f035401640c0b070900410003502d00780e0f20021824000d05044440e81c0c00d03680d16941010741580701221560000310f0103005400e020b01a00d644144191582c2103142ca030542400d550030410484036040c10b9540c800b04955903c00e401c9000500540c542d8035100714070300d240c82402003002040c5659014a00b00c1000c21040c40d19000b04051060108410b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 787849784 1250 787848534 787848553
    0x12110303090a120606050111031b1c09050906040e10230c0a031119050903010609060f140301050f1801110c0c0a0e040b04020105031012140d02010504080f0c0705151b060108 76
    0x120ac014800c000100c1c64855413003040300036054100300381400c8940d9580d4100b000d150109000c00443c0190800c3d210b241054080000940006160a50f0750005c0d44041002c001c0a102815000c0480b407007003080f0071030385040107510306400f80240000e0003155000c00609044101e40025030141d1610284018441841c07111160303c030f0000b4100c640380c01000010002e680380e0490341165003592024000300c0c0500000c1002100d40d58144100003402d50080c400c0703240c080342120303210b20014600b80703e0044812803003010314401d500402e40b65444580d1f01e0303520034100b224196503008625400307110f107078411800300b40075202c10340050045900181900868a03190f00540b0290001000e01c1da861300d8007200056281082040c0c10022030084180418074000540c01c0c90601210f86544401e6a041005100000f0740c0001151803082070203200986034004d014100741040c91301d512007030344814443c4800a11040c2d80e4024030000103c06211490300501c0d00129440b041c0034459080140c02000f2074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 787851034 1250 787849784 787849807
    0x206132111030a111e0c0433030c080102030f011a070c030c1422020304050a0b01031a180d030f110f0315030604051504290403030506030712110303090a12060605011103 74
    0x954401714000000402124800e0520007000045105c207500070803660104101b2b2021040020f0003400300d12000f9855454100494100c800061250708240748000055140307281c40c1100f943c01495112045c103500c25641d041050400d55180580795008402914445151400302c40d03d44406504000f00140010010b20b40e070025040100252400e01a80f1003650000d0f858526050195100d200705024000e1450384e200c0d0500303c004c0440000031001c04100d00d101c0c40014207958020400c3c0b80220701c1201e007000c13080c0a13042d411030000000c40041142000740c0c91403005180b0a500c510f0507440844100b4040540d90f81c02034801500c40c4d049105c1c0d40d8090002d901c020b80c1c1c0036000c0c0001c421811080c8845980b000c282c540302d075484448500901080550600515410003011070007402c071241014407003480c035070700704100a1114128032110203664505005540c6000c0000782503142d144e03030340d410707118400328591000c035180d910302f080105007980140d420445e054680801075080205003446c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 787852284 1250 787851034 787851041
    0x801020a17060f06030414011103070e1003020d0e010f18020108010e220b10060e03120705070f0f1401021209060d0e0d0f0206132111030a111e0c04 65
    0x200c5800601c040341c8801c007078913020b00031030046100c5c80080b0f60b0103104092107401c442003800d00720804181002030100c1954043d40706442103000315000d00e02404941000d0707009200355503480213400c0c2841d90b4000148419407042c02c0844a2010602111b02d0b06100f0304040c1a5150009000c41c2c2c5400041c81030141c4030640b103500c00002c1d011b031040c0c1100410024010b0601400458102c0003603001c0082c0740c00300949401c002c0c82141404008550302ca0002034130380d1488044c5108032000483c5200612200308141d40040c00d0388034400042c1ea40f80d041c3c3c0d1070100254001e01c0849001c440080405510000d1400160920788501a08004c280c000300321306075100c0680300d03c0c481d4913440d510b030140c001400841041c1d0000d40fa82544904003400203418110300800301001d07160303265111400b10f1003051148109080d04a51540361242003401950100d40da0f0f4000303610780c8004154072000723580000214040c0c910600440707580c2c020410070043d00e42418034040400e50820b141145550400c1c3d003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 787853534 1250 787852284 787852291
    0x6082d0a0b1302030403030b03150601030c09050405011721070f05150a020903010c0516020108090a080310180509070b0306010309020411040914130236010e010801020a17 75
    0x10020811803950030014031000b050514524541e5400002d01c0105a014810f4111100041c4c010304498454030450301c283c0200245007034140b580b00c802070007a152040d000c50b4007400b4024400c0100303584602900d5254241044001c03140c0c40740c07540b482c00d5858000d05440d001c0e4402c40103e0326000790381d40e43e480301000030001242c0e240b1030041d0b241c0002c200041e05a200d00030b41100103842c0c5081d14105820348242c0e030316920920031708010f000051410850000c1c01c085d020300704584c0640f02d20f500149400185040640704440110900c010800414203500c2200c407811003000308031114104010403a1000d5402c00400c3c0c1c419001000b44e410550061544214141800650f2504030b4020400351a042c1701011030321100050148010043c610480390420307041e011a12840c500540b4511101c0101240a80f00701e400c803000b0200844103c00451010340c42c00c29541085040c0e04004074058001c1c041c00d0300c05801ca10021078009014401d076000c3e41829a900c4d40b4000c2050600a040580030307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 787854784 1250 787853534 787853551
    0x311032817130303060b040e06120c0a0801090b0109060b1204110a27050402060d0207083c0a050f0d0f02120405070e011409090f0708010606082d 64
    0x842010041c58003007624140709010440e05001c0c515128600182111070503040794070740900602c014002c070b42c441900780303070b001c0000d0303400c3d11420058000b0302e0b14040114010a42c000c1c412040465154010340002c02032512803103211f041c4d81d07200c101d0300b801e5581034010f119918109100f01aa01104112060f4015008202c1040c0b41d00540780420b0300c100e40d0b5003007900041490703148003080d0701a101c0301c29401d6261280c00c00c0a804c09a0006049104100b05402e50580100c0c802081c0510b10040b28416800340390034184100c1194681440c410015051101c048140c20080490a540e9001c940780c2c0040d03a40c5a9141100c44441c161850308441440c0c00313030682c0c50302c00c01094012840101541c0c6400102e5440070306e0680b07481781c034082e0a50819285440307030301c004000d07800b01400c1700c10422008883c51041035441101485c50513211440d0341489100752600083c2080c4194070400c1561031550720a0703525034038080c403181b0716202c0031400d204140c0300ba40b6542c2c499040481c010380203100c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 787856034 1250 787854784 787854797
    0x50a0c050904091b06180b0903030405130608060a051e060102060c1b060a020301080d02010b01050a0f0c0605040b1e06130903050706110a1d01020d05091306090903110328 75
    0xc902c10300c0707040c00f150040008103540f1b40402d8141000c40610100a0948010492400d1000c8000c40e40fa1302451140c140109a40706400b140000c051f04504081d0010744121801480c1031541c0c1809400f080d0396211940340c108100b01c40c808510780c5c0c480d10402c0103800502080e10b0f41a5801c42590048001140702c0c1081850b50060140c01d0011901071414030f040503840754107010000742050140307007400b03041d680740c40c21200685c1d8108095481035080350410708482c200803001a5203081d10007a00420843c80e110400040002928041e03007d1480054102041400c04c04660b0180c3d406881c8150702010100380004c1c0b0702e40d2500308100d02d0b442032800a0412200d960f0710f20648803508120301c6500ca01142080b50903600040341100c004521013036800b0544d00c400041e403a034440c00c145d0010041c2c0000c80032079a844400d07a41c04045081c24041203515501c55590740240481c60088002030000c00c00740d1496803001094410035500c1402205482814000d0595450f0001c0c4212090044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 787857284 1250 787856034 787856063
    0x60e030a080c03180a06170a0b041b03180312020a02150f0405060c040e0a051012050304080105070302040e010b0306012a02090928050c0406080709050a0c05090409 72
    0x104009407a038004290300468458489442604c0329a00281c070366802084d80381410452507500405007400052540c00450083e00e80c07541d04e01c0a00915401c03180c116040c207070102901401c90740c80221321880703903074108032040880d171800040303050340d00703015000400d076000203444c280c0f00703900130414100c0034011101d0044c26503100385034500b0212409203a210f4080204030a21071700780042c9030f20080c2801d48515160a00101c0c02c030f1a8000360455240a035601c0005184102d20a0500f0151070303990b100c0c0301c0c00302c66132030850b030360b130f0300600500e0410350130080031420290090080d2003d468400030b00c011103a090025412a0f90002044581000074020000e19003000c0e006044019030344440b19203d02d10218018041c460001400c1121254810414100f1800500c1e60a0000303031501c241c41d10000302e042c2441d518121417030b20507551051900740d0005141c0d10004120003203030740419051069644030b220000848041c1c102e40000304204000800301841c241c0c0c051101c1d00e114801c55030400d01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 787858534 1250 787857284 787857293
    0x110705060c2d030a0b03010b031006171b0d060b0613090e0d081302010c02060d060e0a0c0203040501120f060e010812091503040c091118010c050601060e030a 69
    0x1007901c42038100600040c0050b0201c000c04540850809451880c07440702d16000e01c840c1c0644002041403644070381e1156800559502908004014140202110f204803410555100142683c0c46000380401c603132074400140400201d21a03405518100844071111701e450f060110090000f1812600c05544401c00b48a0384c1e14540500010982003a07032107080f90810011104aa040c140799041a501204903299940c0e8403490345a070003401d65511181980c2c4510050780c40c8040307010029030010300800c14454554440e40100c00311010003044c40c0b46500c80d003008004440c283c0038410016081001b0030301955001b0240020f400d030307007203034006100c1c4c010104040c122800c68000c0300c420b40900d801042103100401c280840803980a444900d4441c04400240320342d48510480d40609101000007000e100030010404028407081105100c0c940117078840340c540780d01c0003034140c0c5860481529030305554820740344090300540c48002025543d08110050790540220f1450f264580300301c20720140043c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 787859784 1250 787858534 787858543
    0x91722060c02130207020d080904060503030d020d1107030503071b050d0806090a060f030b0612061006020d0302030c120c09060f07020f090402010c030e03190f06060602060c07020103110705 83
    0xc14035640c510001c207425104200700046507045070081a0b005012010240c0c0d00c01d00d48112680e8000d8004d0341d940070b00b0022030007410b0644d1240c0d6041c000410103035040c90141c0c0003041c0b4010300b00010040a0700320030b0310003242e00820801400041003440090a90707409100c0459681c00f10aa902190210680d500b610300400e007082040018650020300805040000b18183c005403840340a20156003400c200b01a005080d00c0040e1207040010042000364803140514440c1d403510600341ca81038a0310f02c0c01118030050a214200041c8074400120000c248648281c0703000303102e000c484628000c060401c000c140600540346e544240407c000f0010940c2c6c0c0c660013841c4d19003110007aa604c4108500400ca0041e984919150040c01d040d42000010707a44814102c0c602581410000082007020b00800d2800c100f03295811a82c0e0031300010f00e4180a01c01c00e0300e8400d42c0c410301c81400415220981281c4030a82900c1d5101482001e016610056001c1e030000d076206401465298109841038031002e240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 787861034 1250 787859784 787859789
    0x1505090702030711010e2b140717120711010e030d09051903030207030f030e04060303080603100621021324090605030d0e03010212150f04091722 64
    0x250b0710024041040001418003141c4030b04007400d15940320540d070004a07848500d0410454a0041a0070302c082085a40c50346541d00540c02400ba04014038091000a950300d410340142410780041d0544c001000700d00049501110500715140c0781003281c01d40d5088004030039907210506000c0c095030300c0d45540c1c0307080011101c40d168603034510440b94602030a102581a40841580750801c03020004c1c408203400180c5031045a500c40d0003058514410f0408403096601c605030b00354414204000002403507407090299006090440648a03654a00d8504004a8003a445404272554047d0303e688221001c40e000a16158009040b00d10010300d4031f9005003c48840114000c1d9250b02c1401c42601004c110708070720068890100c2c100613140c24440002d5070744800c06445400c00006002c1224a900d0a405a032994004c44080c042030b0f00f404010760303800c5850b1407240e9000b9001100402610729040c028134100c00d8121000d80c403105d40c0060714088070b62120102803580742c0100300f0104e411129040d020300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 787862284 1250 787861034 787861037
    0x1206050601031e06150903080a05090a03080f041d0f060906031002030405010614010c210504031202010f0e01200f04030c150915021b030f030406050405040f0507020a030315050907 79
    0x4200e820000c9214821481d1700d160310400645000030b10019446108903014002d050501c1070303ca00342c060000e108034165030001403100a020480602a614070f0001e030040c1c9640014289400601a403400342ea0b2508989580407003c0550104805041200e800c541055028003600c0c2814008180700d0103981c002d5404690aa556100030803040c00e11400011840e1000d28040c0e04c1042c0700d455841c00d02c207a60383c4041d241c80085050001403070043c0b007214015580200c2620603100032040290003490001000484641080141d82e0803070010710903181c0ea01d410141c59401d2114140001c0040d400003940c488504400300b0003c40840c81c1c03511240010119040c2c854142104010000d0514401c1c0e80300c00104803402c1e030a100308540119900206508a285448154a420f4000b9140007503203811006c90b030000243c0815582d42c0000200305481c01600d0500c074a5401500c10800c8800480788580160040100007001234030981040300c40905c1c80041021440d290780000702c50700004e80c0c0820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 787863534 1250 787862284 787862291
    0x2c0a0f090516080c01050414010e04060602031c060b0f0904090b100618030b0f100b0d020c010b06090604180e010507031e0e0606040c02070e090a0510061206050601031e 74
    0x2c00b0742c2900b0b08242c0150030800c0140000d0449400003070850701442c0224008810390700c1c0000b800da4030034005002c082c8070040050084507614a4060744aa01c641c000708100040300c45d030008101880e0045070220744041d1082c0d480c09891100341052074000819407a44242c07a00c00d80c1c000315000000701805141ca44800384a00c0385010405482140b42e203441605680c002d4401f0400300e085850304550040040040751007990300c40690030700060b0950840e14041c4004511045009090b9001d81030501029000300120782400c41004001c3c0611035003240c0c8004100418802c0340220491501b140d00c40241c042115411303241c10300e0a442c2c04031241c0c000640d8424101041041e0301c09202d0300d1041480c8204100c004003030009449890050040e401141c46000001d4102c1c170802c0840024108855090801c1c20301305041c64484140f28000e0b1541c1c414905003214034010740c03282104448050103a00c4a4010607908c1d41c0103808000c3c0800e041c503640f00c64403108030300410b1000c000da07170134801e001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 787864784 1250 787863534 787863553
    0x40f1505092a0703110d030c0215010807090207050f0a03030c140703091520030a020708030a09050d2d0204181a0406090227012c0a0f0905 61
    0x4000429103054101420b480941601c2c000203140c9026000310782155030355140f8141900e0031094804d420a603449111140120a80d00d0350185001d2040340d804e440b0b100e540800c020344040000c1c091180c2c507070403004d010040001268010304082e44034405541c03c0b40c51440040741040c13580e01301680429201c0300c00e00c40080d801400041003007a1440c000b410700009880082004c82d050040111645101034600d14950069190302d2444444c0300110b102c80301100310203600e81d000821032002610640f80040740c5008040141c500c80d005940d00c41c11690300c1c180c00c01c0890000d41c00243c600c041600c00480d403001800b0009503908080e4200010020306500c1404100c40f0840d02406c2000d580b00360f42c000107202e451044111039048010380e401a11141424002051030800082d449420302c2d8658851000080140c09080c00c502600340147c0ea0301c101400d0b6560b0b03c903240500c0c02a0101c0b901c4a00011034119941100c24017400103040b8040c80c082c0c0c4200e034400501034407541d00900d01d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 787866034 1250 787864784 787864789
    0x70f03031e0f020d0c03140c010212060102010605220603081b0c03060c070209060a173a05180a080703150b0d080c0a02030a030f17091b040f1505 64
    0x507041c0030349494610000e00140000a4a40c1c41c40001e8204002c05030b0460014103214428050f03912101c9801d103546c60100f100314038000d60102c0071104400c40c100c40050029030040c865641111006024500c08040d0981e04000c1040f42030381c89004255150f20201c041030150300602084061001e20074241d42d00c0030340442c6400141c000c0103100764410b400b013150420041060f501d03020b90558a011107901c5d500b0004505000c0c1e42c0000049500620400081480008011400c5102d0b40481d041d80108900e11070000f04440001004005144440d90411445400100750910103130884000c094140d000168107810140d00c0030000d0b83c4036a4007802401145541c26480500e03004c8200103254156011907411007032658080c00303050001c80e1a4140341d03001e008240d10968000e06a80c400c0c2080c0c60050140c03100b402a200000c0e1503600381990100100015501074424003000f4215080c0003040c0c540d0040f8001d044541050700c0b0201308415040314018007440c02040600041c1a44c1400b06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 787867284 1250 787866034 787866077
    0x501090c060806032e0f18050109031b0b04020108090c0904051f06120215070b010b13150228050a06090b060d0c0b030703110d0b040e0109080d0e070f0303 68
    0x1540e01c0701d174950100000422411070003d01c04045c1d052003c1410080215074900600c15606040c030012180c0d04560104901035014280c03162007603c403a070720030305000c00c03003400400e4481c0b0050447d0a01c1c00850050340c00340c0c0115601000040c103c034040240180802d400c50020717201198180d0014102c0c0318421449a0040c50044101c4402c0203094a00a44510f28201c07109001e4015902c000d49005c103410018202e6288a1f00495003020a5a442c0031064003680300303040b81360f02c00350341c8a00811081105000510801059401000b2000c044011504500b4610b001a16038510792100800040e030140900f0b5000c6004210010b000710050030041c044c0c2800400951248100494403000070324185070144c16207800c1303040a42c03aa540e20034150010320f0880120202c0d4000400c03540d640c8a0b0030781100c4042c3c181594248920940d080c440390030fa130010070780106849414404008151074960080d0300c41c041400c102d8034202c2e0750b21240005407800da00183c1c002045c100280541d5101145c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 787868534 1250 787867284 787867303
    0x1803080f0601020a170a021c080103030914130506061c09020a050a0302010c03030f0b06031302150a0516020424030507080331030204060b0a08060402040305060f040501090c06080603 80
    0x44d0140c0035607590b070185003003120046400c04160101d04089014130070000c40c441011258101851044500800f41400c5400d02c0308800180000001050070075040c806040c0803400030b820000e403d503001d07603501b01400700100781c1a0411020720810302e540c121b00303003402c425001020001030140050b006000008400f1b40045010700c420440800050740c0c06529040b40300d03018070300015104111110a4085c1480d480c20607803204c4044184402c21a41c081e00d0184203200b102c041e854580e038410780402c0e902031407025801145041c4005100c48003010380d60340d03642d48000c10015110136810750415054552612141c0c040415840030f00402c04200300034006429040000c608040102d031000e4900c001c1501c1542030805030780201c040605030080348034080c0d41d004200784909510b50003002aa5008501c604000078105008a40c59003064822541541d4001010f001c45e5a500910b4001c5600064421030700c940d41e6090420110311040180c00141c0110b40da00a201c1c00d0000c2014a422245e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 787869784 1250 787868534 787868537
    0xd140c0d0b2403070509040c0f0f0e0303030c070302010612061b02030403050307080a111f0b09010b04090c1205040803070306140a050405061503101703040e0112061803080f0601 78
    0x182c105205400142a507040d6500108199030b582d5842d01c43c111080c0c0600c01445800c541001108458141c120107001f482c1580f65903105103800800030112002845055440d0f0140c10800228001c0b1081c2401800c406000b13000101c0c40c01c2c1d4950981e44506802401903502950b00c0e54802d851800d00c40d80d165801003d032000f5400c01c1d095864041d02c9100d25500141001d000040305c0d00128024030700c801ca200501e42c1542c400000c40c848443c0180455202c0c031519510782030075800380386450709101c2d0507030f80400240b5041a040c82c907094004e0415403080c506124130340403001c000c44070701e00401d8869841003d402e40c03a418255805010b0b02c80e15048041d0f10074200454000c03a84030300510900f100c204841c0422103807500400b0a0145e480019100400c0400000b0810740300498000481142d4075441c04860312171840c001a0340700c0c0a5802068060014800100100d01e030380c8484c40701103070140c0d000140c481510400d00d40720b000b20713100c1200400c80343d0013007100402c0b480c40c115a2041e4203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 787871034 1250 787869784 787869799
    0xb090f0d020a03090905190c031d011104090507030e070308090a1202090f2a091005071208060301060b0c0f0106240518061b0d0306030c0b0d140c0d0b 66
    0xb00e0350080d040c4100d80c05282c480655540c0058066000c1138410204140184002c000345903180030001d01070309401540808111410b404401300607014410161501002c00c80d1300d06217402e1904103c003800014094070105521442080000c020a000302030045105808080d600d28281d0244001c00c11958460020078a050003054050307110300b14410b45c0841c0036070102c5444d03968040209603405607000c28642d0b26001a05060700c55014030010981840e04450142e080c1e540c02c0c01c200e40e144101c5500404648004d0401281c10780102065600500014000b20f0180d4440000d5481900000616217082e0710040c030200580300c0c07e11a502c00f07001c0c0600600030401c85102d4130031034248214132100c00c1120020315000c46403081803035601d08203001480701d0303980e001d4280c0511200c402c1002954050050040003100c05020340718a404495021940c065883d242c1800307400c180c2c01000194203116200c40020042000503211503118802c052203a80e29241b00401e034100f01e48800c2c0d000360040c800c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 787872284 1250 787871034 787871053
    0x70c0906051003150819060e06070e1e1c060c080633040b0705240601080c070212010f1523121b10080f04080a0c0b090f0d02 55
    0x1205004060781d11400c1c1004a440c4d081e240340c169662005078401e0103d4080d01294401c29655100801c0c0313580d00071003062107a05640419240c036841c060382da20f000b15000c0070701ca29050402603036042030310030258010000d40000b40c010401600304649080c11a1076001e11602c100101c0b803060303003540d14091810b0034a40c51301e9004100e4066250214002c15140c0d041e00da0650420703803840300746920001400c0c0c3d07242c0703039109070410894200b00e0040786c00e80940c05424581c1d2071b505c1440c0300ca1081d00d15074010740d91201d0300151400203014104070311001041041a0158403000003103625408904000105d4000d19031710001207810b00d403e500c000f16500354041061441e114003d0314a1440009034020240f4800001443c211217600880014024151225042e581460100c15280030565003060380c11040d8204440300b42e012074480400341041c0d40810003043d00c980140c46010300700c1c20458507032081a1210301c08218100d9540c01c0540c010007401d2200007080c000380b03002c1e44040c002000f8540 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 787873534 1250 787872284 787872289
    0x220902090702061009050a0b0619090b030c040509100806090f010c0f050f0903010914060615070f03030b150c0f120a05180d06090b060a1e0501180806010b070c090605 73
    0xa0178810140e03815100c1b0086102d2a216034041c11141c000142300c155500344240381500c0c4043d5100d454000b01d1042c000001e01c50111204a030b124a86100115250504103400c000784480040c1500740c10700390064010800b044100030042c0503180141c01084c050300140e4119007521081c02415040061080c000b00740d0b107800c1000d8802c141548188551240026404030b40102840e017800b820075040d4901c080401400400c10703034010b5405641905102c41a020131b40500c0c400e51100821102c504414000441c0c031a40c800ca00c5008014500e002c0705041019581098008a81c1d410b1960419100321400c3c0f4400c1010080c0c201c40c01c402107080600e170000c0070740203004222901d22007a4141019410b1640c620103403440081c1d00c010704001c00181c504081340f14402c01c48805000d017001d00310200f401d0851400100c040a0b80c4100c580b403803814400111500303200202403100030309003400b02040700c4106100c258044d28100007051b88610240c00c28490103040c0340d0185401c81e24000781808140c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 787874784 1250 787873534 787873561
    0x21602131109120f1f0b041109010507061e0c08061806090c0c100606080a0b06031504020f040914070908060105060721031d060c07030e22090209070206 67
    0x9100071168455a000e03d0607000707082c40450401e8003280c0c040d04900d20340409100c881c1c4004251040b00400070260302e54180b00c00c44040302c41c03030001c1e22000d0002e201c243d8070484c01810740b24400c400101b1411100740c80182c00b42c07032045031502c5464079952000b481c180d0001509074080d408561881e03481040a04d034004000c409050140241200400161030940784130448070301007182011990000340b2510b00ba0300424450250030b0020314440041812000b0b107000e203042041c0010200d603d1078980c4242d00701e03c401a5006560095000c1c44241c1d0030040380e6024000810361088003203111021810000c503140c20050941082c4403010f4803e00045500217403441c1510000d440c815611051414a1a03044a0201d43c003140a040e0080c03d024455140e040300350400140c281c0d100070303181407849480e1942000c4640700d200c1c41041c0b00b41c0300405e200700403800316214007901642160585817603034103e1402d035890000c1c11765280c0c0101401c6003010303244aa03000c80c8620240c20581045013052042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 787876034 1250 787874784 787874797
    0xc16200f0d0f08160c05101e18081615050c03090d02010c0602070f02010207061d0607020a080d0503060a0f1d0603101404020901090209130e0307060216021311 70
    0x100400c26050ba02040b98501c11102d507032001c40943c41d400c03101480d06448003081d0340182409a6071208003040c2d454051404a8020740c5000c0c000c07184e00443c2e10080318144140e41c00d0858140740c01e10b002482000c00d124240302c880c203403404546031905007079406003041000c00003042081410070445401d01e0010055071900341c000c88030f01c0d98841240c00125502d04649038003402c024400181d0704100540c429034105040d100313800341c0b86a169284070a589644ca024043c8408504098003102c09141c03010051001e240f005010710034441e100c03443c562400d0f80302d02007036010600020501006140c41c0401000410311405820300017802c0810104001d006041e01070f614a2032704c8080380301c0740c0d8123003c0c1071540b0505090420a01c05200f4403014003000546040e40110039000c0085800951030013291980d00000d401030341c40e1200c050240c0010610110f541905010621900c00040c00c540000e0050041d015040490182180100035020034241044881145840e0200c0c02c0c0140c8881a9101c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 787877284 1250 787876034 787876043
    0x80106210819020c0402030115021c02030d0518010e0601290d021605030c07090e0d0c170706020d0c180e271207051005010810050c16200f0d 62
    0x9602c1c00c50b40c00360301e010030301c80c43c2c0c680c024000304c004a003c20f00e00034800c030740c0c8a1503406c54820300741c000d00c011102e880340c400b580c3c0160400c0000044040054004642120700100c00d00e20708900380d0388c090300f10f540d00070011545420070303401000351080445034180d8456100050401c400c80120b14142d20748036400480c6c400e950042001029000980e0741d0440c00ca80000035281d480d1040d07002c40f600c4002500440111f6407a10301e80024240d400929418205005e8642441c00f460303a4583c07211110f41c04403401240d041c1004942e00084090000d030560000456020902030300c01c2c400604600d00703c0c06940c030780c41c0b48120200020141e00003120380210051401c090411500326641d8406d4107001c1e0742000310b1051402142e000d40700c2030001e1608601075800d40f80c00e1440e0507101c1069401c2031280a03081d40c40364042019418647c0c1c042c07908618002809403038820703102c0c0c20040c039548280c01a035a02041b81040d13188207524069641c0c03000701c01c690700849926403000241c07900b452020040c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 787878534 1250 787877284 787877317
    0x6151204080a080c2b0e0a06060815150904051f0603020108090109050607030e010213120605160203040e061305070c020a080f030d0c05090901030b15010801031a09070f0801062108 79
    0x74945c0700354090102c034804942078074030300b03249070520b4805810148130f03184142c402c03680c5031210310380c2c614011802a403843e9088000b00035a14100118840f014100360340500a10000c010181c0000583c4d110071159650b0100f0b160749140000341a580c0000c0080002c0d074109014940000d00100d04194000400d050015150000c04100b500a005800ba00f010b00012000003054200c8444000300040d071061105100030303500c00d0265a0308010301c2e2090005648103001c184030031415070005590280c0061302841d0301c840d032414a0b500f0303180107a50b090301140001600e0025401c0121140380648018030040c00d801140078040c0f680ca10404a003941010f5503122800c16441c03144c0120f40c2e06810041c4000d45a584034100002c1242c0c0a0303076442c0c0d140000314240d00181d40070b904050b04a81e00146c040084405c07200c0440c10b4034400401c00e0480b8006d030103020a1241c40b4000d50400713405050000203405080031b0b0700c95030202d405001c0b6200c0032404c0901b0400100200f04a8413005104101038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 787879784 1250 787878534 787878607
    0xb18070c0c05060a02030306040510030b0c0906160809031e1e01090c0611010b04051b09040e03220e01030f35070b06090402010806151204080a080c 65
    0x10108100d90b4100703551001c030005001c03046560000c0910302441040790100072507180e001912441000c0c900c03006081d10310180c00900d40c06580d001070170032240e010300617501c0c00c820040c2d040096440c40d00e04a80c10480458100101d05003040410500c0031510007401c500b10005409998440d03040c0101c003d84036145403840d105e03203800e40240110a92125000b40e44a0325003001804540b05801e48105640c80d181041c4014034090003030a001c0c0f002c00c02c200708088d2515400402a501031405a03400940702c2c2c1140c800360340104024080303000021750581c80c0001c001403c40b15001c190b809010718a80c3c8000600100d40c000c150003900a6000c2044d03034488014484620000a4111502030000858085565110b505c0310040c000c8a01c2440e03000302c40c0d6154001c020035010140c80103400281d404c00000c080d8181688200744041c090100a0704100c000c1d07068568089044074110f41700310012030950040d40c0c11588194000d0b0030407107030608200c031803113401024804a813010303c00f000c00c0c040701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 787881034 1250 787879784 787879793
    0xf070201030e060a05070f091a0705160e150f0f0409020a030f080310060305090d051e040308090405010e07080c070c050306090105040b0903040501020316050309090f01090b18070c 79
    0x2104028542c0016680d051030505071110050004840101c0440c031860040050680310b120f0700030a4030030b1060ba8010702048041c00d44440c3d04100421640380c8240210350303089000002d846c070010042d05003581003d140c48070074150384507030350880b40c2d015045101c50401203a683c01e014400041c010f94000541c41080e0000031244010381e80068081451070b451041800340d080004c3d0302c140000d141005c8896030340d07081201210000c6603900455001210300d808101c2c030540090100400071910ba440545200f05e5410803a80154030840d00200d002580112600f0140030b0603004059149524103203250408000e000c010b002403038502a0000050391008015240114030b026000203801c9070040c0c500440340034000c050544040d90480c1c289400135441031000011101503400c107902030340c142240d40d1400d0705481d4100000701e4407400144101b054640783e92040c940720388401d407500c80043d450700c0da0010403640340340e200c107024100c01c2c0c030448231690b64010007603000300261030204c0030b1500c1e5041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 787882284 1250 787881034 787881041
    0xc0d020d0807033b18040b0703020409110304050708010203130807050709051503010b030c18100b03090a120e09010506130902190207080604260903120414150f07020103 74
    0x40c207048442407015200b840340348800c5520b80503204ca0100c0c86031400c0403040215484051140007003680190000078006610b540d88140c001c10507003405400c0984030f00702c031801e8521031041030161030400b01c1008140002005204020300c2c4000085245041c0880306803480740c4100d0000e003004c0c40004555003007010400c000c0e07000300111602003180f401d250303d414400024500340b040c469801e1080035840c81c1740220750208203200003460421f640103800b02252040c0300c001e0458410680d0740d07000081c0c45e6800c00042d40710b1507030039026102c0c84000c0c0c6400c3c510080100c200301d0420000e003400c0821070300e421000c141541c00444040f40c0b11503e884101b8600c8420b600404405400812034001a069440304c0f81c106809603001d0322521500d0321130007a038844003100c1c080c0241070130003c1403103141042b174101c0c3c80800c1450000d034904644640803a140000d007000c2c0c1c0d03190820000f402c000c0740000421400d4807250403545180291304102c1261890b019100c094944000b0000c1c11004682c044da1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 787883534 1250 787882284 787882307
    0x30e062b1a120a0c0b0318011401052713030206010e0123040e120c0c04020c030a0302031b030103030c060b03030304260717120928140a060c020c0d020d080703 70
    0x400d220402e440314103140040d04180c0700b03247e158103404ca1104400300c0600511000c0d08a5600d011026881c2904002030351030070298502207014541d40c9040d205271000c99440c8540000141a01d001e006850700a10f8204164041080060f2190041c4100200111300440d0503000c284040c0c04034156200080c02824030a00d061403500c103500302c407080c0c40c0c501c10181288103040c0081d1404002c40d0300a11040c1e214146450740f540d0820400f600b062400703603000d1a081030a205810f83c00c903081c801c04421940c020780055002c00d030315242e10350402603d409000c00ba880c06501650035410700e40d0354182400d01e0120b43e08191540300110519014060701130302d40b84c6030041400d50564100074042050356000c1d0300072514000d07034940021041c4500055040c1038202c5004c00d0903040368107161000d46914246411501c4a03100c0c070b2380001300705007080301040c46ca0060200213120654030750b02a1400342c070340e03003018010181d4483c4c0e4400b5907560700c045940b9940140702c19907205d001e841c0486a4070300300d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 787884784 1250 787883534 787883543
    0x180506101805131b090f05040b010804150902120f060a0905060402090928060c020102030103030c080f0d1b0e0a06090b1b0706020706020d08040b13030e062b1a120a 72
    0x10b016131501c03d5881144603044425014029043c0d5441d0700900c0155402c07032044c0c0e400300381c0b00d07404a40041c42e149000442c103820000d0000c0c4103d282d41c00038103803034410080750f900707503000118001135202c0130b120940c0c11a48a18040086100d01e588541e02e5000040c4041e11070030003100002c03010042400302c0d40f05201c120881c0507003036698185481e480807440c101500c01c00d01d030141c0f00d0701d010300500c2100e0680380c2640b505891060180d5480b010380c1c2c041514024210414415101054414040c0c0c89c41b00e4010501203000600c9850001d0031418180d0310144504030301d0304104807040d0403507200c10564401d10b1170156241460b491101c149120344011403100e22658a00042d0a42c1c00324000c41503c101da800d4600c5019640340442e103414060f200a440c040550022861204c0c130051900d00e81e910900345502d030024100005086504241480c40601c00284500780e004070300c032418001c8411a00c101080801d00c2040d50a42000c45503214501515441210b003400301010007010380e099500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 787886034 1250 787884784 787884821
    0x90708030406050a1d0114032a0408010617070320030115050f040506101107080a0b1f080c04020a0c060603060218010815240f0405100e01120506010918050610180513 73
    0x10610810540c1e01600c10402f15503c4c0240c081010b4035100c030141c103610001001041001d0850316003000c2512080400340d220142c0d110341d807915880a0040c6200d6081d00c0342e0f40704c645850081400140302d00c1e840344610440c9002c04012441d65034403942030030f9a10b0303131403c6c40086901461461070881c264120b005140305210100003007100c82c102861281000e14a120f5140706e02d40f4803410f010009010b408600e13000a560087c1500740340d400f80030140440d28015a078101c4944032201211182c0e00107460b0f036034000a07414840c603400d19418200910a2801d410146000d0382000c0510b90b01600d0f4622030b49501703485009040c02c945d640c1c2d0038820307610b02140d9206075220210ba41c50b44907106040c0034000f000a01c0701e00a01503401c0528202041e110501c1640700000301d0b2009250040c0482c5c1440103c0c1c1c40450324030020821020746800d5038000060340d00344031041240642041c4414000c0104500381000c00e02e80d420308101c00c842c0281c2d50849141c0044910f1000380110b40c9007421020300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 787887284 1250 787886034 787886101
    0x103022a031e0306040b03070605070213020d051e06031b041a15090316050d030f0519020703022b080d0b0d03021506030609070509090708030406050a1d011403 70
    0x11002d00a500684c0c04480030090103103000b040c56112807807442070304082601801440058240305080305202a20800700601c1c000d511090101100c60944a801d078034804000c41e030040c480426680758020004400910741c1f11005141c0460070301307041d8030590003503031107210344000704201e0050303aa0100402408010120301149005074140c0201649178402d00c04d41011028029802d0701c44019a840500b0080c030011058505483c200c1c07980c9885410410104030b0500c40482540300700000586c640e001c2e002d594650f0040144000344824082c1c1940c80700d65134036900b01420507a40b0061603010002c6174403024043c04660043c1001d0140a8100c400d05810504040d80403503240702400c09580348020a484600501d5601d50f0110780703003c49a030000d14140310919140c1921030344402000103e41035691030313011003410758000b03600081c0807074404185620907940040c54120204c40401403440d103d144540024900c00b030304c00c0c2a655070180080032402410741c00803018840b00010079150306220 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 787888534 1250 787887284 787887337
    0xc01090b1006030b010c02210d17010f0807061809020706272f030318030f010c02060402041109030d020607020d090e0606030c040306050c07020f0103022a03 69
    0x50048070700d81c6144a00420104a580c080c0c03140414040d0181d46001d0f1042850b402c0c070200d0940c09403010300d02480038a880c01081d008001c4608903660b076070341c0c3c24810302400c0f032240c404040603046007030703411000d12050012980004170f40d812511546029002c12103101d000486042d0181c129485890000505500b0b00005400c014848a4040c0c105200340803c0100c3e06100301c040b003030040c04114034518405c4013003241248945802080a071080c4903c80c0100024916070100d003103144c410049003110490b41c9400c1c04007800400f00c074030080c04900346212000b034035114010310081c0310302da0300c1c1114011030074244140c40165030b01034111113036080c15040180d0f07105812503060700184142c6013005140d43c80b58448108481a04c0c40305400ca07280c15040060540004064119503041400000080784160040c203008100714128103a80b2591801400705109a05605038140b600420003100d404440710620031021902c4410142c031406030004c0b41d42940b040080303424203043c6001e115002e03030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 787889784 1250 787888534 787888553
    0x80412200304061806031505040e03040509091c18061209080c160b0403020604181e05070f1106070c150903121b090317071703090106090b031e030c0109 67
    0x300405075a4203011340d640d14049081d105144600001920001300810041c00c081c0c0140a000c0714110580e818079466601040c06000c00b200c2042a60340316000c040400103000b240d51841e010300d4a404010602c51011148501c1b0071403060f0400c04c0071058041001018039482072640d945c3c01740ea25a906c4000403039180e0340d000120315800d9002d12f104000500c4040850840303080303a0780507104508203403400c01d0074080c03901140c81701d902c05074403550b80310186480a0340010034901041000125420b00c150020989400300ba860400d01a256010220080300010f0070303907001109240c603526454840c80c2c40640301c240300c00180c101c1410101400304040e002034402144100044040100301c0c0040d000d003151071007012703012020661514050010412098400b01400d5480c86801d1400c400b40d41e804808140010a03045402008000e000e60603000b0300602000381002c203030520508454400180c0c81e1544071551103010341c450402c0c014040018010b4410b550589402003128060604064901 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 787891034 1250 787889784 787889807
    0x3220b040c08030a0c06050a110301121502070c090b010c05070f090e010b060405100302190e0405060102151501020f1c090f0608070c1a0a0e0c0108041220030406 71
    0x1a07036501011855080002c02d84000c01c010742e50f01036000c1c010392a01801840068000c122340c1c1d0b03d8155600f00c243e8550000d60003054038811850741c00d0800d0419125403021200e4010500340100701801c0030903400214407058038098940020340b480b2400060350078245810000f04503001e10080003440b80c22541d041000c0b0740441e00284104020196100e08950038441147e07230102c418401401b0505000000c1e46a000c1d4038140146001c20701e50800d1001c82894078030200240031680840c107242014080c19400105c00e0000b002c0c146501c2d00022081c1000400c40d1150310003031403030504144e10030010f40f4242c0b0030030f030117540c0449100070050401082e0903000c1d03004128180300020300307018442140b80c11100c1950722500c03144c480d04011980f0410600301074034214007401d004081004012840d500500125600040703400300034500e01d04062507194001d052121040401011455139003c03501d8011551410321085604007901203008040241ca06080c1e120110b40407500304e801c404490300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 787892284 1250 787891034 787891043
    0x3030605040b0d05070b0f0409020408010515190b0d15080a1e1205070804090c0e0109090204030c120c0f0308120a0b0627030d03050a0e071a03220b04 66
    0x10000030034043c85494920020020050b40c080c1800f0045160040060b06244900300c0c0360714605079840104400303a0300990040101d99654030240301c100007000c042480440b10a0f03450680722440d803141984c3d4580c5a02ca02c1d0940403001075003000f66034441d0302ca48452481400c04190190302d82c2912035455152001c11140000684202c0800300842000e8028095000d01c0c071004105400c0002c950326041400120740221013408041641c00c00b6005003510550789603500e140300a11013000401f400340d90307880107103028410401400496030703021072001035074802403508400310b220745806c2c05540020b034027800001b56504070100030811000c009024030011480e0b4040c45440302211401212081c07110158130110401002c503402c40180d034130007041d44009044071254500b54000c81e042250402c65800080d0740c2d6810080640c0c1944038031211001220014203265080210b821a801021040340c8549100880003882050511080c005d032800703040f120002040d2a8540300b0383d0001c0c1560100d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 787893534 1250 787892284 787892291
    0x121303050615060403030c0f02060a080f0709060e040b120a03050a0f0516141c030b01033204080408010204060e01170f1f1703040510090614090d06090303060504 71
    0x152070b03140602040c007032040002c0c4440d1416207555010754003240c50003401c492011a1610007000340e6128006403240c0c0340e09898240c003c0c42c0400c03020801c2d200080008081c00500c14043c444540e108818000d506d000351800944049000d0000c0e0101100c4e003c10180703407107096608802c043d489806016141a0754035480310800d035040094805020303115000410800c03111045c400700b020890980802c99504083c1c0310000d19a000d80003141091908042c0407a03251303101240507580c544640510080c0310b072507030800440c040ba100361008000c504000529212000800d007405250b42c112001410b498000315034030b5a45640c00740c00c2c00300c041120703070105602e560400000003101c01c481d0b1007200c40c040d13018465a1001e4840d212605034172104d0110300090784010030a4010000c081c591242c820700156280d0b4038103420000c80282404000c010010004420080c80d80c1014804034141c0710b00c03690944030140840803881c00141d44ca40a02030307500b0b0444a60034580c0540c0700c10180d801c10798007070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 787894784 1250 787893534 787893541
    0x5250602221205030d0c0e090420010206011a0703110303040f03080105120c061305371212030b0607110a0815061c050d020f071a0d0e1213030506 64
    0x450b0384008080b4080d00e01e420400c05c0d014a2050303603002e0400d070003181c1004008120082c010604403401168106d80c1020422605184000e1030316401420034400d00c0203016640c1405c65005805a407040307449000100031801c4010035000311460070900e080b81080b00d85915050509081c080d410071000d401146a41002040508103040c4d02080203019800411181c08842d0603c14560b1000c1e4140b200000c5550011440c0c0c4d4903924444001421210301c2940c14800003000501c402c0e220351503841c65060b0300b00401c0034542040103002c41c1030b0803414a14003105c00c86c4c02a40980707100007400350b110340c001600f20b0420100f55107a0304c126070242c403840001a01c400340b00d40d8542c40c400750400c0303c015003c006582e07131038105c105940c2c6003030003181001880b4440d030745d1030b00d4036220303104103801340e00803000030500f641e420000c3c00010820840740108103c2c454840c04010710980444004c4151155104800d54004100250440528013491596800c1541e103082402c141404112403500911010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 787896034 1250 787894784 787894799
    0x6271804050102090411181e0604120b0901200904020d020a020d110f0307020607020301020c1e06060f01080c030907150e0913082b18021c030525060222 67
    0x195040704000fa107c40c0e940e100d500040001c982c00b0200780005541c0c60304200e000503107454018000506182131007130760300e10661504a00c4503070000d08007801d582c981074020030f043d00000c10f0b40c40109401112182d503150b80e480450040d21514512034500c900000383d41e0b54081c1c0c0040c0100da010610703664141d41c5100e01382c0b0780e529240400c01c41c003440d0340140300c010094070b4080020f010062008000502e0030809110b103d082106425155940c1440c03030451408440c403c1c130015a200d041101c81c0c44114242c10000380504030082c0041a416001200203001e13100200b200101508401c40e40b0f21000c1d402c80802000d0554036008140500a0500825292046400300c0c00c01c05600103403450610400e86c0e40d00001210081d2405003001050b1313012500040903210380091030300309a000d04030740307401401400b20a0030700c0002031504a488810a001195005040e1034400e16a04281c40ca602550a605841122a401d001e003281d4400200401c200d85010003440d010304054298860041c0d5803800c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 787897284 1250 787896034 787896037
    0x100b0a0e150d1a0714180d0507060801170102030601050a080402010210110406230a140f130e0114010c080a1103040b0a0e09070c06091e060603020301060506271804050102090411 78
    0x16a035681c0c40043c002841b85083c03040841071282d402403c081d0400100381c664524140e03e540c80170010a01d810014030000203d00f0042640d4203400b40207501d0340c206100020083d03c100c0d510315007004140c0001c00e046a10138040702801c0c0c0000a01805032800007808100c0941c054803410f4041002d511401021181c02c0c801030341f103010f40c0700f00c035400c1400c403038015940140158607007405448204903280728984481c001d00342c0c01c0e1052841d030b26040e0606564161085041e00121100c00078800901101c0c0e83c064504150070743d21022082c0c032810590010b4600400010300c40c0a60300000c60042608104100034050a56803541e61480c1e801d500414401c000728180c030483d0001e11050000e20102c1e80c15000451071500c03c0b07114011301c07042142c886d14180c07030b1800c00302c1c0d400c0d444002c10000d40c90240a914080c01c41218481e1802c02c146912150020030100f540902c090881801e82c590740d42e28068110b04d41c000340080f60549480d10b4018000e6100e8401e440c401c80ca40042541503c50180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 787898534 1250 787897284 787897307
    0x1302030f0d08100501090b1e0d0e07060305060609040f020c0f100506040525090e0406090c0509070c11120316061107020a030605090705040c030e100b0a0e150d1a07 72
    0x8486084450520b040d00b259035100308c8030308014a0090014140001c103440084c082c03078990401c00103441b5900c010850911025074001e0003018240f0342131100304d0f0340b1034003181c141c203108031000182100c21106c400003034090000c1c0100743d8000c0c146108014040850440b0b6250300c114020442c654070842000219142910303101d2103d090151051f15103c1c0740000841611624180810510b40e00c0d0010b000d000e5040710110703400d80e22000072808004e100c000400240108640d54212480e0443c1c0042c40c141c08440c015180c01c0024a40416548410618203054142041665079640350741688800180000100b102c4030b40c42c0034100e801e404042c800b42c80e01194000c000c4920b040c590344406004d08800340141c01c66000f0040c3c001804d0b40c075486040352a00c0c070b58802143c80d40c80c000c8110f0604001c0c0d42c0c82d1310f5803814108040302c10f6441025000540e807041544200d00c0d1181d2090011071810400c213140c0091018000c2030500c400009130006011494004948507920701030211032440380030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 787899784 1250 787898534 787898537
    0x813030507020105250804030210090b3004141606080a050916150207050a050d021c060608011b1115150405360303040b1302030f0d08100501 62
    0x5101e010300540c800d90040200c04e46401884044050080750604510300304076046880040010b01042142454031510340d00c0349030341c01c01000803854100500b81031300ca070001100e01c90303031404081422000a07103280c020b41006030504002901e880d141c0300440003446101d101c0e0364880e410700824581101081d0006880042d664040c45407202d00042c07015040103012020396014819a0340d2200480e121804011724005107003030081400108060f040503007036040a4018070443c0414400e80e110b042440b40c0071981929510600b40d04905440e032440c03800140280340500300f010014030380805420060b410401c0090444501ca040c0e030741a80c0f03804281440103e1070b001a0001194072180c0900c1c4c40c0d200c5080001c242c0c074029014001000c03507800311006000705070080740b80284a100005905992640d180900744411040042180d8030b0000500c000e1421305076000203030604000e001c007800b2513680038085a0026030311001c21916104111518800110401d002840286c2e180e0f16440460340103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 787901034 1250 787899784 787899787
    0x4030b090309330315130f0b04060602060c030a02040e071d041a090604110a090f080d02070b0a03060909030804110910091a100206040c0506120105010e0a080d030c08130305 76
    0x1204620b2001c4d00000d10f048042d510707070361a104858590701d0000d100c5120101001803071a40c6250620704803a40c90755414001c1d46031200c1442115000295940c00800302c944985c0c132541c9a0091801900c42e0381c1200c0e02d0000b42505000144e40c02001d4141004040301d42c0049102c810002d020440b84507911000340076210444000a90038042540398000101500100c0d18140744a090740b555448500f50800040c410b020030064401400c24180203440c0c0b070740c0500102812194001d60780c159500070003801c901c0005840e01650f010758440f10013002c00c0c03a401e200b05019070802410101040300c0548061040c850078030a140781400d02e039807040c1c0115258001c030a040402402c01098050300303900354980824001d01250b44c03040412140340103903034002c11040c603151a22411030326086d40098041c4500b070110945061103850340381c0c15201d00f03181500d0b102c0070100c0043c1900c1550742c020841801480200b40e02d03154580c018914855098441c00801d48030a4050129501c44d4480600082c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 787902284 1250 787901034 787901119
    0x120703020f030c07030e0424080a11090a0b0a0303120b030d0f0f02160f0807090b01350412030b030c0306070c03050d0501060309231b0604030b090309 66
    0x200c41c3c05003103614002d192090a01044001050440e03180c1800120010b19010320403840003032811f4030710054942d0ba409042c01d0a61580c8024100b60038034801c03403042c442d020000b003030360703055a0081c072041034001c003024801c90303a0f41070103032106003e104841e0349981045040070650030002004860507185d0703550304905840701700c01201c0c80c01c03404c2c08001c00c43c002c068194695000e980317640c030007802d0320488681a89203010081803810549034480803106060001c0340c940790307800038210340c41d803070244280d484420040406600a01c4800c80003010741c841c074800b8081808000c035040d100d00c7e0880e44007000b01440e441c080540e030b41d140307a104030381c15800f02c80001c1003544100c417444201813280c1000c038204648a840c0e1025110240c0280002903070322201c40c400d1100071182096103542072040e6403031444030400256200e44101821040d4200302c00c0481d505a02c46408035002150001e001065500f0080a51f070780320351141390541d129400c0200040e050055418001ca116550000b0710743ca5443d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 787903534 1250 787902284 787902301
    0x3091e090c09050301020c0c010206061005030f1003150506010201180c180914060f010501541d090709090302190b060411090109030201050c0c1203120703020f03 71
    0x80c40026490800240c00b2001520b41c40c2400076144101d20040500084128030000928000000304001d10821401d08014200d0303030008200ca030400000008a4026a60824102c80010050748000d04801c960004040031180346e5002502500b800d078001d008604604000074214094000003804042e9412020000809190000602800059400b107038207403480c1c5030050084072019818100703410070401c000c45181c409212502504090800090303082c28803603241b6603591045041c416241c868400c980f0f106605e0100714812510691560360811170141e48039080c40034a1198184041c50b00402c1e206808240d880e061183c180500104480c81c580061b0a010b0680c0c48400d03010760140c0240d03c40c11a0203000b031101d040d13000b0250685107040c4182440122038030b43da0000150794092186910581c2e00040b0708007142c0d02440c00644500e80d4024090401070741a42c0986c3c400b42d11202c10540040110180017003070b42c81d81e850096607484080a0303040c0d01c2010300d100120701013000003a0780318 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 787904784 1250 787903534 787903541
    0x151a040f09050a030807080a09110d050c04020d0f06080c010f0f110a0606062003030703020901090e0a050105150a1b05010e0f030327070e04080d051303091e09 70
    0x4400ca90300070401070800d8844500301800c0f803000750005052a0304010400e5001400241c000c6442d200400541c03455454880100c0032042c080da1003801401203010901400b00446940c0e9070005004540e03412036951030340007c00d0840c100c50000780c28140001381d0f154000c10600074070541a1140e59403922540c00c11100c10258402c202c0500c12801001548120f04014101080344203c900017507a60a00310090845204040c0301070407a42e182d900c200355150007000380c9411a48904002d6150301448006880c000616004413409ca4400402c1011018564000ca4100c071801d94401007a840e07543d051040f00d20071a08420041089107150310b403800001c440450031240514000104c84009600460421444040800980c0e10200510800002001c42002000d00c195010404040c480c040c00341c440c1520b11507042c4034021400003c0074004044200e41c148008031300c042045180c0421810104240148140c1c00503940c45404240000c909404076070202041e1001d050051801400e01c002d0b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 787906034 1250 787904784 787904801
    0x5070e1c0b0c210903030a060b070c061206050d0501230123120a0c0303020f3c120a03060e0601210204120c05150f1605150a0504151a04 60
    0x1c0603811800106001103a58140e405019250065552030500301d040e04141d420f52740088422a108005d01d2002456069420080343c05909120b0f813051102072a15008120380e40c4505e07005403081c0244800c110040d4011031078403000503011800c002c005121112501000d01400100042c07950b40c0c402d0404d441d03a01d0515030400103002d450358550000d81c207030070003003005012115062501c030180201501404545117454181e0020109011301141c005a11202d41411480c2420f141c070f084032030386a42e200741c40c5a051220341114450715007180c80c032000b584004040c0c4000f074a440e40100b07040c4418a1418003c103016582e045082c0c1000c8046102000c030810045a00c079800c2000154403401c8140034402d0301e0058400c22805482c05d014010420201c40b1850300c001400c000880303801100405491102c5040041201b0303003039451500e189013007408051106c82c03070108000c100d041445900298481d0f031181c5185a4104c400c400c1d02401c0c0c4a180c0e020b03c03d1a00d100341200e2035814075a201e00f05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 787907284 1250 787906034 787906057
    0x80f150c07060609021b0d050a081906081f14060f0d021201020d0e0604020306040b0a090c0f060e0f060f21040b060324010909110405070e1c0b0c 64
    0x1d89201903507440c0c122042640928111600402e4504401194004a42a010001000d00354114000000411510401c48440148000321000c544071580c240500180d03c1c003158801c0001d030b03844900c1c2caa1784024004410b4002c1d05075540441000903180140760064104456074190b40d00e0315000c00002c00d46845450350840c1c503507600100035944551380e071064244400001655a16504801022b6404805400c04194440c0c014040183c40004065a0081e0003261000458440c400d00d04068806490041c00308061204041001001049110100c68554540d01d02841035402484068400c0c031800070f41c010400e0050840710074a0100900307042c0040910200003543e803000f9298860400e640545041c140c0004000103410100700c04a2681c200c4105002c50342e1031805501240c82050051070030076900c80d0309140400040020400403204010410f10580c40c1c6002c1c005d004965801465204010b6085155008100d00707002c061180d07005510108140c1d111484000b05511003481da40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 787908534 1250 787907284 787907287
    0x130b01030902180907060908071401260709080a0b0c0c0703020405090114060307180b04060e09100501090c12020f0c190b0703020f0909071107120b01080f150c 70
    0x10010faa45002d0341000b049038070302014850501107034851a00c0a260072600501040b604140301d051030001d29039086402d42411200d00444040c0100c13207000d161f040000081c02d100800b070301040d1b00705003968030641c1d05948500c4d586960f0724103a50f8543c201070015041d079100e10082107000280e80300078201c410202040740e95142e56a4017280403101e086a0402690b5920380c1042200d100100206420400460040000b1401d000545089445c600d41764a102540d4004590243d119500094010a00d12512140c0c42c50030464552b1210791011103007050310b2402001280b00c4185210341402c5403210b07070340c84181c910f07125000b400941c800d01469511039414808074030b5030070b41000104884045211016104041440c1072004201c002e0712800a0500510150f81000c42c40d800f070b11300c00345080303540d4901921203100030f4410000008100303400f8003030007a0100e54050038072500107040e407141c00045043e80c0d0b00d00003681c540803100c8002419070440d02e0102c04500c5075469036034204045010b940d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 787909784 1250 787908534 787908551
    0xf041107032f0303090c0634081206150c0d081e0108030a02010c05090922060501090902031b06090d05071e1d280e0303040506040b070c02130b0103 65
    0x7002c803024001007003400380d00000030850b0040341030020800308407094600d1800c0c440182c24000d8440e540840f41c684000304014001484241c04030001e0420707030001c400543c1c0310340c4102c40401c044800c58000d80620518203a15011075542300c100c0b500c521034003020340b41c0c2d2500c50604890044011b081e4420100501d0807240b004940d24500e240240300d403100031550762010110107400e490705842e01c20140038007030000da00030352542c07080340e0392044d510720070040402111030100012840110000e07206900d000f0000c40c64007850750040c170300c076402181140c0d001c1c0050340094401044a40d11147c10007001c0c004d900f510b00b461405c90b541180300300f00b5100d5081d194840029482c5020720103841e0250041401c11000c0c1e1041c41140c4030051040020306240341c05840542c510143e0380d28622081c54240301e40e54041419440740120710b51100943c0c1e42c1c6d0600c2d08200d0b60303c0f4401d403030689a90300392343c1c08542c03038a0240b04600e01c203540c050186c1958980c640348910040900210180c10b01d03884803140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 787911034 1250 787909784 787909847
    0x8060f100513080105040203150103150506120a0302070512030708460f030c23071b03060b0105180103021e0a030e011a010e040203090a0804030807020f04110703 71
    0x80c0006401001c000080e0f1b45064010103113400009401244503450a80041c0042000714803403d5154261801c007143d82d440350004140b0140782600701e580d4074003ca0b0501c02c10103602141722811a042140c0000c00801e41d400301648900c154400142203074010801e690401414074100c600a00044503480c540468102000d800d40740c4010040744540d40140f100402141c101700c1240e20b4010511341080140030040c405010a22080c2c03a5440b50400a00000c034100380b601c4c03c441c111030344812066a442d031070703095150f0080d01500007110000c2c200703050500554843e80c16660107120a4002030b41300c0400701d0043d402513001c1c9032585240718200360f6514112070004000c10341840b066400190000d1310305172140c00c44040111150b036500485429201d241c1e404201e05040701c00880c0c005a40340c0340d12101030b2410700b03503003801401d081d80400e000040c004600042c2c845580203894240c10310200d501000304503441000d00075509003050024201003445000560f054280e40c85d208004a110b00c000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 787912284 1250 787911034 787911067
    0x2d06030c0e010302040c0e0d2a090e1b090117010605040c120f0e03070209100909030f030c0203120a02131e030c0b0c07152a060c08060f1005 62
    0x822045000c001e0010411818184030322940c0345070a11340310300c1c0c00b03600b980020500052001c01030001000000e206110f50808240c0d003160001480d50702c510241c0e10b6000f04c003d0b0441007081d0381c00c0e02a12111030f044440c00a9a4410243c00500b00f8a0701c3e0b00b4010f01c0d02c2040c2c42e60751566902d640c0c03108041a9034031188500074a05145807207a150103450b045800f01500c0720041d016590a040c00000c440d0340e000082501c64241d412200d09805030b0b6400d07505000f0b40c07081d0340840d080e141010116424590094001e00041309a950140711070003c1c1c1c8403d9903213110b5078102244011071032000030704440c07040c0d01416400c087c80302c804c899982d803140d01341c0e0310030700c0d0121465405095101c1002000080758200d0000c20501d020301d414848509001616030620340b08445100c808603142d0108944201510b03410402c2d1300318143d41e442070141c0080e50041d9101d82c00c841c4d4038078001400d1400c5000e40022445824014101607204c1104808c1c01103007403004500c1c00602c002404034881103203d014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 787913534 1250 787912284 787912289
    0x100906060804020f03070b0d0c0c051e060c0306060f07030314070e03072903070c050d030911120a11040609180c0618120309090903020c132d06030c 65
    0x81c0c85403800c1c201030040007124100d012000c1e101e13610201d070070044150f40c00c0c141c0b84e113500b4050b030000f01e020100c0420390704107009210040080c0555841400481514400004241c01040407a03001380d42e0310080c80c4840c4010344110b64414010b2142c40000252007008080052081c43c01140c149000001c040c0354000075100100410601c803980021410200064030013460744000d40c031902e070144017185008800d03256600f00c0d00740002000414480c0a00d0000100c66404000c032984d80f00c10719001002040e403094102c0305400403000030501454024130050107520010007030b11000031150354070502d005118000c0c0d90440c1e00c8a00c005120001ca214034600c002602d4018030341b4040d43d24100c5442c200c0d0b500840c0511140d0b0400c1407100e524058001d00b0f803407040588815a903000e0509803210400ca50109074040c9c00c00c455501095404102c1c071944032401d5650b0220050000304040581cdd21444240c6c510004440c0030403805060301d00f8403009140c0700b040001e032640d140d45071100c0096058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 787914784 1250 787913534 787913537
    0xe04080d0f1a010c08070b0402041d0105040b2409150a080309040608070b1602010e0402180901061e0e060d0c0932010c1a131401060b090910090606 65
    0x35081d00101c00d440003400b5403014400d18203001c9544040e0307101c01140c052454003405541e040d100150031074407030b54400f8680403000e0500c1c0c180d080080805502038002120101c404440c950089681c4402030b102c284d9140000980b000d0301001e1a105010b098800140000030100354085a003000d5107074554500080c146010280d40c0d40c060010030300050b80c0f15507202d060a82e015480c108601216101a9103e62031400089001c6248500040b036140002010b82640680700090a41105141000744201500c050360f1021450382c0c4c0320004c4d280e0341d1981b0b5450880120440008480714440c2e49007080705c481c003c0615040c100981c03011002c459003011640003281e41c2140c240305005480141850342288055554a00c9411180324403c3c810b91240c240c0c144602e400c1c0440421005e4003040640b0400e840c00e100c024034056021010b0125400d40030384000c00c2c124020030107070b641802500c0546000340802442e0849030f03424041c0501009269000f2290140341c0800d0b001920300400c00108243d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 787916034 1250 787914784 787914791
    0x20406080a02011701080309060c0c03030f03240306060402090406080d081909080a0813020411091509090106080408070b1e06010527060708030a0501061709070e04080d0f 75
    0x4602c005801548211428003100c6441070040191a400004407102e0700810303034104e901e0304038101c40c0c18641810011060303418040402c8002c0c4008051014600c00e4003085000b070b41c140800201e14580418840959825411403000aa1241810b070020700c10550003601c0001e180e90303111a05410300850b000490700040b525002e0104949000f01a1001e43c41d01c01420000d4001581c2c81003601e1140c1c10070341c802e105011001800c42c4448400c0c4010803500034205000b09000802015546d5100ca003a8611503425071924084801d00303001641c6d580c410180100b1034503401c1c41c4041d100054000e00c2118002001c01c082d20009585460450103071600c1100205d65045c42c1049040c9540000e02c428108501032045501c580f200340c1c1c0d040d84490401003844d201400c41c40100b01e05210742c04c4094140800082440a85c403c1c5500c083d04a0b204d42c0d640e117a940882c0300810002940507551b40c61140d2003c44140000b9902442c1d09410502c03404e040c0d45818850b0012005461660001e01001603a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 787917284 1250 787916034 787916053
    0x62f0304051e070510090b07030309120e0a0504090c0312080103290a110c03070506060312040b1213060608010525121104030602030103080406030b090f0a090f02040608 74
    0x8040008104000b0310182075040400100d01d5503541c0d81e203030b10030140f190554848038501c0314040e418010241c000307000020390b10a0103003009001351080034012a1400104103500315403510400080060000040013552040e1401c4204006803440c5081603d01c44001c1100000003150b06c550030200c00502d81b1032440310340c03444c206083d0a602c031120002428920741d03d11422640544c0c981b5501c0989010005004000f01c5008400f6006004412056210005203d014000d000442c5882810100d00301e0b42031420a4185800d036018910174185009402d10400c481c0c031041c5200d13998050365824520000742c0d800e8031400305030307049a441030b103c90b5501c01c01d00c8203a044003059402c401408104d45100720f880500020060682029410365090b80d421801c0c0e028442d01003214000c42d0000001e41d2696103030b0514010b00c1d8018401c100200b03107003680080c25424105455840703031f500204802e030b00307a031205050005001c21050440341c0301c601002403030059807070f0f00c500006081000c1c01011401b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 787918534 1250 787917284 787917293
    0xa2a031706090c070320160905010504110906070501022116020a0302060a0b030a0b01031a01080a0c03020105071b06110f0a11120304150e040f0c0c062f0304 69
    0x103020302080e0168241100b0044140441002c503481141d1620301180c2e40c114842c062040b5854904034100c141c05241205001400201e182c403090340c1365240100070b030303982e210104811140500300c1d605520100b4050050b041c500300020303009883c0218005850880024107440c4111006031288400c5c003c940f05000c0b00790300001510540d91300c140014128940c4e9900d0107503440d6002811121916111061501a81c405103c040041940101c90f84030310350f1a40762040a0b1006c0f096180c81d0034110000000784c41e80c0c0041c410b2103040d00072100f8036099095400444660b8802201500c20100400206010000350090400200601c4e0f441c0c0142201c03d504160401155000c84102a8840b00106001c01c0451a0341d00c2800006c86604460000c090400cac0c3c114001c50744200c00141e0b015171040e9017160080140356890600321000c010f0b6000c50700010085600119440340080c0c007030203888002942580c0441c12203821610041114801e18030050842681d2400201d05060080284003c11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 787919784 1250 787918534 787918577
    0xb1206060d230a1a1e0a091403031602070e150a0b0c010603030311040e01090b0d21082401080603010b190f0803040308030a0b0f21100b060a2a03 64
    0x1802d0a07104e4460034000da030420b850210400005d09a030007807003c90784030250340d401281f650380d2200034091440e440ca0311050b00c9420444208820b411031007000000d242c07010901c0d5043d01c035160368070034aa8841410a400c40b5914501d1150003d04929000c21008401009010071003034800000c900582103280003415140c00c00c2d0b02c0d00703071002c1c14030062000c01100400c05042d500c0c00f040010f032010000c1c0011381c00001c61750020380388c1151030360380900400d1640c1041f00a203523207031100b54550f191640c4030031000c07000f4140c4116031310700e4000c8009258171503103a50350045401400410702d030031400000b800c9803500040c01e0a02c8403050380c3c2000603842c070060100052489501560a0500c4d41d1507601c0b440c0f00080c410091183e94044540c96035440000d030001c15140500b411504492961451b00c030592900c905111512070b0f10006a03032030040b801a42d072040c2014000790b08190200905980324800003048107148582040340480c030260311601c00506034020760329908c12003250f21300040740c2c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 787921034 1250 787919784 787919813
    0x103081b0303100302010c11062d07030c060e0f03040f17011a06031b070303020d050f010503070b0706020f030a0506100203190c26030a0b1206060d230a 67
    0xc5070414010000b4510503120424101d0f41c080c01e207140b0309a03080c40c012100540c1112980d038040d00114a041101000103003000e039100003001007001c1480303002004e9125000d90b00c401400200019404400140745030001020340b29400110381c40c48044880741070861704650889514074001c10000c0001c45100c0400381d48844500c0000c0150310f0000c0307024102c860381c24003514007840c4008042030b001241c024000000d03a0081040c40d031240098034006010b54440e1714120340050402000c500c65040c554011412102c004009280c254680a0503003400d07000300c1c409641d00c560a20401c07214940d0000258170070850fa18000503240342c50001c2041c940200760000d41154028000d500d00809081c1550070002c80c141094640100a0725103501d0450b559900c2c0d1607014013041d9808049090280030f03601401d10180140301e018605800e2282d08241010301c9241d59000364045481030811205400c0c243c0d004841b04c0d0403102e0f0460581d0750264500c03c08000a510101c01c1100b0711444e090b18a42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 787922284 1250 787921034 787921087
    0x519050c161206020f040f0e0403080a0b090f070302070623010605040303050901050306041e06030b01050607050c040b1207030f030201110301060804020f01090f0b040312210207030215010308 84
    0x1150380c105010400e03100405680100341a070300245d4035041c0718261017510005c100200306811b02c0c503114402c1206120003035038110007240401c0c010810421840c010048000c0f0094107400780c9613200d10702c011a00f00c0103400c0d1814035608000150110300700c3e014500703010404107490a002c10144652100d030080c140d000401f04a0280030900000c0d46c407d0494000007070074a0a551a910f0703c100003401000f0b000c0c140c50300d02c2e10444406c143c02110707401401c2180c0c080d852203041070303a07140144a51072155071001000c1d0b170000271070070110f49042d510040000e0000f5082040e100e021814041c41d2103540c0d00207480301350f0456075103001c05034240601c94a4401c505e00301400c5514040000d0701145010380000d01c140310590444034035074030907100d103001400114031404080d80c0d510903051a40c0d01c5800195800d403a00d00250300070074003500085c600c0c280000b131128050080c034a05c04000b5007042100310218050410382c0020250f00303042027400307107001301019507031640340b0345141305070070451200c805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 787923534 1250 787922284 787922323
    0x1804061206050f0916030b070e040504060507030f0e21160f060e0d0c0308040203010908040902250c030f05010b130e0c010809030d0903020f0f1f050c0702100519050c 73
    0x500c6070b8849601710046030761021003401e56480f0340c4010b888501801080d00d811620302810030047c400c00e0307007006000d60701c01c2e1000c0010040880703d10041e40d4034a0a03410307255200c00700200707460b06c5e880310250f400b41c1c50380411402c00442400285420b68001016211142c00390340d80418814107101d0500e429000030001c09010408100c040d202d015500c0c00501481043c04c00101551400c0d0443c01055a010701c20342c1e510364171600d2007802034100384c0e80600490f92172035581c02c5403540e00b007031000d59940003100003854030316503911403071040c9680008a43c1c554860190300c00c00d40320a4100f9410b20000200030501580c140c443b90315040820f1070b41c1d41002609028400c0e02c1102104407032000800400c0030034107102908041e0300c0d011900d1009040f0b071168001c0e070b54200e1804125a200e0440c080c2001c82e45920240104081d120306075a41118841d0401c06480180382c104002d080d0101c041c1000c50405032049108100001c0301902140030450004004260302001c0c020280720181e00c130402c1c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 787924784 1250 787923534 787923553
    0x161b05090c03040c2c0709140103020c10050417070506150f0a0b0f0c15060918190317040f111002102703050a02010507050a02031804061206050f09 65
    0x3115905403c2c0f00f90341c101d103c04c05c2243c00c0801d10300070801e50180c0e900002e0b4890300b42450300030140c49013407107030704c54040081c02031026640c440c0c022540f45d194640c00402004847c140d0030801868060800c94104802c581701e009001c0c0488080c0000c3d500890143c4268582050301d038000b501800d9516100d01401d40d078031013042d03555001c000166881c40c0c00540e11002580e0f81000203100c0c840b020000c42c422090400179003c40b414170305124810039207007450300351110b240b545a2419070a0888146420070200c5048030080700c2c00b60b207034280c020302d4034440f6850000203031071550800396416180f480300502900140404c04c55110441c0ca4107a980038259803090714000d488100c00c40c200302c02c1c591545600042410701030074001e03c41d042525010a04265850b020304254808402c400255007048006200140664160380a049103034000d9031400125420344480d2440a041c696402540c4400103e411030a805a100c1500c2c407800b4000b541e800c2c80500700541c0f000c018030000c115480441807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 787926034 1250 787924784 787924793
    0x6010e03061306150b070203010b04061505090d150e010c0f05090603100b0301150e100f050304060615030e060f01061b0303020706090c06030b0312040b161b05090c0304 74
    0x40c9510003240302c0c81c40e440e03040750b1802c0303c003514a9080990741025240404075070b100c151401000b50381d1003240208044481071081c8000d50340944184c84006410810040c20140650000c041000d002400c2c1103104100d0344d1030742c5050002c200e03501c440c241d840f4608003910134240b00b0541c140100341000da10700e1104540084c2a1301c120022a1b028000120202c1d1b040c415240000b070280c0f605410550300c0e9078540d80b40c0d0070141103014074040040e5070f0b203005690034100400f0810314014140c0e60000751380c6501e0015915a4400390003141c070941c1d102d000090350404c0203c0d0740501d90f1590350200d41640307142e220500d005405040000302c11080001008506c1e00400c000b8844039941070055180d1040e820207800a01503900301401c000d0170071400d0010049040301c61000d842054804000c1040070300d081c1a55020061750940707903090104414400c6034100b0015040440084c00441d500402c250345a61464029a4100130081400d98080c0290f18200b418242d10039035100c840360940c602501c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 787927284 1250 787926034 787926043
    0x1020d0221090307120f03090b030f0109090305090307030c2d060c05030f070c03140a030e01120e030d0c03062102040c0c14060f061206150303280806010e03 69
    0x11020781c002800642a2020f44007070140c0c1c0c00034450044e00040c040c20500317048041c85940c0200700c0000310388000c04a4000c0c0e80c841034034003400e0408001c00a070780c00c0540c240001d01e221001641480f60500040c492581c1c20044403000d548a003a60340c1c2d1144c50000e640f2001020714841103450460142c403505030a400c044214202d80403440d003c81c0e044d9141c100142140311b0f000758440d00410000b40801407045201c1820200c92048131031080013030100d48295202c02c110740004000881f01443d003115980b0a107480003448808038000a0780808402c1d4040c036550042c82c1da01c0c445502c9e00c0d00e020466416110718001460b0000700100310003040c208000a1181030300c4d0081c0310f80d65421840e00c030107101c0c499025000c0c3d031080c1c6401114801503556035440000b251f5011100d40c001000071078a0030142d01d02c00c2ea45162400400190b16000c0c041c0e000180d04241080d010b10042c048820840000808448412000e041000481c0020f010050900c3c2c002450181070007600183c956051300c0024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 787928534 1250 787927284 787927333
    0x1509010813030513080d0f05120622060e1e0c030112050c09130c0510090b1b01090b040b0601020d050f030a0b030f010e06010e0103111203072001020d02 67
    0x9140040700003032405491500940049038400f0b403003d1408030751800300282200d85d403202d6032034002c520030b900a0708139014404c10b0442c2404448000100b122414080c2c0008800c8500680c65407040b59105043d8044404d80e902505d05900240284001040204480c6110084401918403c0c2c5406804092248410700c242c1124a00303040c50641484030070702484a000e04010166662801c05024200010b0b1410109841c00300700c80c50001214580103000c00c00744101e03a11144132240c50f010b80351400da005651211041d000b80321008440a07800e218240d080c911509a90b0000d0034a4140308882c4070008220318155441060000d12254020b0700380c80000c2c0c881d414459880c0c0e0b0704003e040282c82c1c111402a0988030340240980521010b4100303403545000c02045501a0383d03146c00740d0b80031141c2840054400d101000d0850030509002d44114070b5030300c2e84002c0b00d103071121076501d48090b10341c90816103010a0003d07404900540c1c1c1480301c000210524401070888410222010200d62850f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 787929784 1250 787928534 787928551
    0x15020a020d0804080a0f051614060901020109052b0e01020a0f0303140403020601150804020f010f020a170a030c050306010e091e040c051009180902011101091115090108 74
    0x1403108100b00100c00045401030140c650a80e60429043d1901c3c1c0c140903080f0100712041c0c0220010003c9501d00c0750100400c4401c911040415103442505011490b072004440b5411552584021400300f0000c00101d40c1752004811454140c0940c0c007c1ca80b18904c441404008101c0345001e02c21140c1c0e0700240c0e0100300ca40109000d16084540d14043d00141381d41510541c1060386081048149070700460035604035144008105c1c5a901c00c1c440459103240201d034005c1d4000c40a0750716200d5544502607264a8030007900465410380001d8442006204c9500d80904e00c0ca080001c0c12030710140d0601a0024601c0710381446c50642c20103a0010f00317100c4403655010b0060340300a000605a983c038403030000c802d82484400c0b4007181000d080804000707080b4004c0c04d02030318981c40d2810100e8483d0803603004a51030101321151110525031054050803011000342e042104036070716145d05003402c0c0305001015101c0c280b00e43c803407902c11040c4030003c4a0808800041c03003080c45000b005903000380f000c41c0d201192 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 787931034 1250 787929784 787929799
    0x103030f0305100905181c05030c0304060b0d080c010b010c080702091b2d0406022107020a120501050114030a0b130b130b010e251419080115020a02 65
    0x1110a00101d0043c0c65009901003410101841a82d0001d2a00103251040c0f5000340c850305900082098900d00e100d40c0c5003000503030100009980c5080203405503410511440700403c0c2007a0840000e056011050000d840d001c400180514481c2c4c000d12941829100a0822030080841510390782150702400c540a80501040300015120100380b100400601020340d403407a8907044059001044d0002d102c265460750440070700c00080c0c440500e419203044428507402008403100e120301180380c03c0119031850142800610400005964091414000d01600380018403519a581811803d564041e4020101212242ca6840f96500c021880001039904914040030607140c1c0035408051402c540c1000d020720b9480e200f40506d401540005e421424000c100300100e40c1d0702c0e00a0040c0311001502c03001000300034042d080c05241c03c500d4507012000d5281c10038410400c1c0c00d80b1540c1c1507601160819032590007242c15000e0840c0c001d071035240540885018031000440c01c035806951341e000b80d08080d116002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 787932284 1250 787931034 787931041
    0x1003020d060e011109180f131b180b0406031106090a050901030c0302030d0e0612190606080601030f0b0303070303020f04090e0102120a0c08160917030c0c06030103030f0305 76
    0xa1a8005404102c9140002c0265600c42c40804046030008030455220b0030345698490904640b1341081801003882d103402090750784030f132460547d00b282c91341002c44062521500104100041520881c010f0400d03004043c01d02000526007001c03030781c2000e080351107945068000d10110340d0a0070300314080e0205440e000c1e6200301e44400500ca031000755100355406000c143c004410410400c2410040360710940c110f46108000d21000e80d8000a448103154200c2014000d884046540c03d6400390011035401800a414080422203400c1d07482d0754104c4400304458000380300003540e0600c6540940c1d00c101000300f01d1124440d0000e41c480c42104009810941c000c00e9030602080c0620407a0010702030214200030348849039100c01d010b500486050010b200350800010031100103070143c1740059000ba031f143d40031581e98145d0924004058144034041060a83e8049803031441014240116500c000003142c540d0f1070fa00d02140340c00c404c0c0301c01a0250205200410002e0340040419085407414240400c0075034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 787933534 1250 787932284 787932293
    0xf0b0f1015021f0e0610030308060d0204020405030a1407080c130b150d0f0c110a150b1306210b0106080403020a060203010b090108010b0a090306021b0a0b0109050f1003020d 76
    0x143c072680c000c0c0201541081c904a00958071041c0c159404e1401e9642960368104101d0b1100c0161201030007140040d00010031a02e00405030074a5503100410042c217050310345d00231a24144145504589030721a215000c24410b600700640c2c0c0080040c80020999801c07040301007422840401c0e451030301c1c01d40b10b0002c05203070345e00c117522480c0b201c81e40c3c0d64490f20381c2240e06140c0301901602c0100b82c0c005160152030180fa6229002c04500c07460000c000f4103400300a6581c00b104a400d840d59404120340d21401d9030b40c80e6403681003282c008010240e01181a41c2482841d40724101c2d0303042d100c0c02c9460760034004d2001a004101290442c1e040c0d0800e101e45586508040e800d00328107600c001c2041d440000040380c000640c0000c1d041d41c4000780d0381c07001c081e80c03142e03051003503481040e20040215403d9801040014116001050003d28803558501c89600c0807198521700f641c0305108440103202840103001d440014031800368445500038941c02039040229080c9451003c501020740144400d200045c00d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 787934784 1250 787933534 787933543
    0x1d07180506030c0303070305070b130c050d060b040f0209210d180503150f0a090506013506160c0221032a0d0203030408031815040f0b0f101502 63
    0x164400b5080e00e03541e02d1b151a00038a40c1e0b11810044801c422028046000b0843da003652800c0b0390740c08810b0038030290801c010420143c81c002002c481c041c1d10380d0000e407030a440d5801403004ca00031000c805601c80723274840100703c14110144c0109440c0801d03550030031180140003c1c1016031456609000024000744001020b00d4400341d0130460301071140401e5120700740c1c0d0360b0344030301c0c070450100d0b11450342ca4a80710392201c10385010320b10107851030703004c071006202841014000400d03001349880e581240c0c80080040506824800e440203c0381e0304200100032150b411890010062881d40c604402030f100d05600041100aa910210b42010074416004200c82c00c00c00460780920084039481c0c5511125216003544002031000045144c0034203080c50011600003c19a800b41b03900032131550941d518403c026140c42540040106a0b1103240f0807170b01a0055480340500860041810052540c1d8500303002000c84006018001c40c2c201001c00c0008400e40e0044a20680c1c180f0319040210114000d07089103030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 787936034 1250 787934784 787934803
    0x614040b0c120f0a0806190b0d021606050a0b19060320190f020a030905090405030912010b01030513021c05031e070605160801090e0109060903031d0718050603 70
    0x4100003401d48075149819002e001318401075594803580daa01d40050000524803030031514034000210b2414060b01440c040546290303103c2650050805820380c00505190384d84030001d949095a030424003a03201240c1c01900000101903075403440d000b5040600301445a00e52185004140c1c2c1c071403c2c5100342401d90317208040901680031403502c4441014200c00c2d20803042401030046051401e550740e610740003003070030401c02d50152181c10b6564035110a100c500d040050048549000c03c01c054019507941c050444000780c225000090380388105000501121030103420344180b007112800040c01a074449404403d003a80002007841c9140061420381e140d8000d80e01600101100c440c4e2030141c6c038443c03030098400c0d203004000512082e151061503401604101c0c60f0100007481e40c000621070b104d855001501d8030040000002038041c6961211b800f1548000022000240c44040341c401c2642c8a0114000c5c01b0001400b40509c01d01e007245044101c0181c40399422401e8507000041e42642e01032060390b04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 787937284 1250 787936034 787936063
    0x30516020a05060c03031e10060e0307090608060709060e0607120e15090306060406050d1e0501060b0702031c050d0906020705100c09061d2806030606090614040b0c 72
    0x71160741307001c10781c2d0b100c1d0022141c01c1c50f09944e5004020004260754015405207640b048200449404e0601c1102c5084c24404016014404d500000800180c14458000100281c2000d021607082c00a4024040c0a40d5444103041000005441000b96140421140b00a80c0142894544021480c00350780301c81c881c9110039489440884205a4000520010030381e01c2000c9007600c07001d035107003400c22003290305a00546401c01c04e00313000000012001c0b0010411300784882500680c2c42c04541c1c0b511b096036965040044101d001003814000c50404215407142c4500c3c4450042500f1402c0394010410302404204151840d10703140c114040c01441d81c1210100794100081e92511202c00c59490003400034030a0340c0300091038190001a1701881081c81c580304044658004035071001c200108001199448982c10702544201b144500071664805407800515083c0c90200f240e600d4000b003c1c0ca400b8040d8081c0c070030710100e500041a50080002118207641141203c05e0b00c0780310020342c991a00f000703030120131b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 787938534 1250 787937284 787937287
    0x4140102010f0c0207050a0603090c030609081b0c0f01050c15070309020a080706080f07020a0b072a020a1505310b090a0522241d070c030516020a0506 66
    0x3d882c541c04034401c000e507039050315213008480c0d403040c0890031200001d0000d0300210034410188005070094103d800400c2c0200880c07070401360045640c0c00b01d19266054058281e1121404600300d04042c00c00080b041400d09015040a43c0c000090b5125131959840014590200d000134144501951003020310b00d802901c04070819481d203103807a94505842c002c820114285c54001810011a0307424140f051109a0103088101c0495885041104d80923200009126040e00410445444007071050240c040c401c506900901180c010701c548005107030040340007005a160010703076080c0c200c402c5400034050031580162082000104004a845142e5034912641145000103400503c1c6006041c507000c0440d443c020541d42c0d2410000300c90306c0111000320710134000b84140442d15059104158074080d170850780e0380a0348500340c10925055960408690300e001c0c81881d00710480a600b4140e42b0a080e810840410f0542c0d403009003032805180042000551104099002c54485411041c0200350141449 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 787939784 1250 787938534 787938551
    0x304110616200409081821060402150a1b020402250c23060306241b0601030c0e07120c1e031401050402071e03110d1404140102010f 58
    0x3052051070b0164031800c0e101891011004038030301441070009a030382c080c01c501c0c640130743d0010340b040760094621b1450340a0710455042e40340050102c810945604a500074090030f10f454030400c44402c5980e4611780040c4c0e002d00109420507000000e19406039940b040e00300325501c031407000070040c0c82110105449041c14980e0444080611400c06035428869044014007a0715440801c4000500880915090305800380d4580a401d0500080d904003c0203003056410389a00b21480b85020240200000454800900f40400010071801c06a15945060150516502d1512070400800e0315000d1280c0c800140d5001c103d00720b00174a11070720a4401d8070428413240d9003c0c40040c0031650032207000026040a0710f50042900e12a2082560305250f2030400c1c44180d080400b844000c0d002090100c5d203400411008804a0b0001d02c1c001803c20320a41e02c10b404d80190005007801c2102075003010080c426048000303040051301d00144d4040d18032880304446910300c80760040f809050b841100c41e00d45407801d00710 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 787941034 1250 787939784 787939793
    0x206040f050a240f032405010e0f030307110102100e1e1614030f33040f060504030309080d0f0c02030f1207020312090d0e040b060304110616 62
    0x4a021a9070456201c0c144541c0c03503800c5400810740480c10350109100c08400700c2202e003e400d0b8208428218540014049800c10324a5010080302c0100041d600d1018002c02c00d546c1d04c68111000e084080d142c140848450401003560707405000c000400000b044485451164802c100d0610103c020b203030140324100c1140d154036242d0134000b1030240d1146032082c0c0303500611400a6480a108240c2c00090703401450880054104140d035040b080d0301d40200c080074046d982007040341c0c050715080d10940e2014401c2c800c0e00c40b13034003100600c1c82480e880000e070101700200d24600b1003000615000140803a4550315450b045005000360302005180a40100d0825150003a81d07124140b444c80c3c01404002c040e4001100b41e0346c0340140e20780f0070100002008503141070a10f270045030740c105440c2c0c011a420001051811500804215807540941c1e00020baa090510780c40f044018940c2000e49040080365000f0740894000e00c0001c102074000b4001d202c0c414100e4444c2011940c060b0510620551012414540b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 787942284 1250 787941034 787941059
    0x2270103080d1a090402090c041802031602010c0507081303080f130608011202190e1e130f141e010b09061819180305031f050901061b020604 62
    0x440d2001902d0310401100c11812490f15000d844002000c15203130f81c1e038907030800c45040c6004003015108403041c800012008190b080c04441244460005a01c0b0700c0c100c0b80c0343c20174907840c2e0b1542d8116814016440003079900841250600c60300b021000c2c0e80d600c3c60b0102c130b85080d00c0541c001014141e001402d286c00c0310b600d001800d84640303140140d40d00c4c96564901168422400c2c0280e0445690800312000180307482001244540c0c500c6c031491040555400c441204418200c1c0c207000c50119a001540d0b4039100721a000c5d40c0f1008c01000d40080c05800d0329080b64403449080010b018903100c1c00704601c2c0400400c000d030340024203800d910240c89031001d80c01d0702802c1400c041ca8028848135010407414900100181d0340706100c0f0109a0040c0c5c0c07901e00218805401c69007150b00c6aa42d40c00b900e04646c07114660760718032030081d00d805a5070304042c1c002100c01c14030303051076001c50030188400380010b59035030313846034111071300c03460040300700c001201540780d0078850000d0096212100040007e414103030002c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 787943534 1250 787942284 787942297
    0xf06060512061005010f03180803010314010c02030f0d0e0d0e031902090c25031808031305061e04080a03020d0f05120705090409031710030b01030227010308 69
    0x1503808401010480c81d5995422007a9910286004020b0301848294810042060040c181d85008a45c02c10020381302e1a404e4181d01040c0d07102480000103005000c15640310f85035241041c0001c100d6100700c08070080d12801440000d400310000000c1115088046402c0a624448074038240c880c01180c11002070503507030031070038903500900603948240c5003e401e003010f898480750094044035403640e1710303107191080d51b21294080341d03a1b10007021a03202d440a40e070180c201180c0b094640422140020140e801e410415038001c018a600801000f034010300110104421108166541510b40074084420030000600034044507280d05c3c007084c006070070306000651030301a5000340c09980e07c03e18010002c60f441c40303a0440f01030115204020355110200d809264a41c8546545045800c10040c2400941545c0102d541580051031a42d00c00d5021600f10900302c0c0c002c04203000e2003640314515681c844001005110107449416164049181d41040407144800c0c1017400302036081641e1039140a504580010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 787944784 1250 787943534 787943539
    0xa06060306050105070314030a02070f0311060a0608100905030d0f0f06060f08010b0c010212130b0f07020709050c070624050402070209040809011718060901230709030f060605 77
    0x141c40014254068422220080c0c3c0658400c20143c07082040c0341403990014042061f5240d08000003c007284640411121345031107640c1e010406906600040e2605902500e4036410390f00e004403c0109000026407400200070071300e00030504c111607003841400c50150f1b448821580781068407038603c442c1d403a440000b011444a008000340d070b031181812928486000c841c000420001001400905207141c09401140540b500151500c3c00c2103070342080000080d00c80306c542e001000d020504203c2304200e04d0354422a8040704d202d603443c000200941d50100ba02c600380030703180da400c0410854a040c1d01120511358019805111414a02d00328040f400309240e0344819040443c1d00110716440d050003107810f2244c004000c82026100c5485584060f449440085d0501c200009401442c840e1200d2141c803904000581008260718400b4060400000408100e45039150500d107a02154540d244070b81261221941c507041c40e69915020381e446191074201400f5411074544140401c4510340110701620030a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 787946034 1250 787944784 787944791
    0x130623100612060501050f0d110a110c030109030e010e0117010b030f010602060103030e061602090f160509030d0c14030c010c09080d020a02010e0a09060905041704120206070204140a060603 83
    0x102800c0045480c1401800d001403000c0202191094800c009490b201450710400182c102411000030170ba07520002b0702c04d020400480042c4030428003840540304226040e4000e00040c1d800d994000c00c850480c10000c0e050080000c02e00850364854800380010000840540a10b07503118510300c06903400407948600d000201d4070011802303d1000c1a86c60407203078913480c0c002d40c00c0c3c0310204008071a00018000c02038820000740020150b51100411030052512003001d5600d03080c40c0750b101c03074524060741e09103051003020000442581c07000600e42c01d1914091070842580d901c136180071007280098003a60303400d07480081040c001d26941903120540c81049903c2d01e4101580c0c440c800da898401e03e154210168025070a81000742d4080d0170310400c001c100030891101980c4801c407a604039140740e002034105d0b59480f010407080002102c0d244005c0300b90208082d040518000c403d421810300200e000703000b000081440380854880390040021a629204a01800d183c0f1805100050006102d003c0c0041e04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 787947284 1250 787946034 787946057
    0x2041d12160f0615060f0249020d1805150405030d110615031e03040906080c0312070209040f050a060203161e050f030405030906040303050418051306231006 69
    0x403c000c0340d100055401030026011010004100712248e080f4040304194019881040c01450941d54400d0710480002c00d02d00d4800010003e29100b203074440c1c0d80602a200004030300f41c1303a412154100b1a9401c40c0c40302103034100ca80000100e8042c543c0100e42510030030340311806c10f1ba002406003029124140440d4030030340d14250300010381843d001d0513680581000b00c149136030210054003504882207000031079281944e10400402101d401d83c3c0000390a800c408c0751220146010302414036081ca002c00f0850400d42540c0001d100d00c84050401081aa581084030080100130301000b085982c00c054115100d2070201009030400d4541a090070000d80508003000540c40078415031a02c001c01d541d941824844ca42e02c40408503030016000740d03007034801401500703016650320700280083c5100395107064441d8500814400f68041c50441c886845051000700310103085480a6141301942040000c03510032081400d20054003c00c80810400320450004c208002d40b011003d4000c45481c1e5842c00c20400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 787948534 1250 787947284 787947287
    0x8121501030b1c020103090210020d1116060507050a02180a0b030a051c0203040306150f080c1c151521120f090e070c02041d12160f061506 61
    0x20000c42c4001c1c0e0150003850003a007030301c485012150320035206060002d000c030440d400280f2226a1581d03140300682c40038503400743d0103a00c40a448a0340a202c0f00030030300304140384405a4030240e180210810088040b41d00c800784001003001a600c19005003110340b540085150305034000f0811a0300c200024182100c00c14030b030500092040c40f00d5040030281c921744c0c0c0d0035440c8010080800008408600c418031012010400c20f1084019902503907001c1000f507482d00c014440c081d0910350040c0b40342d810074099010ba5845c0c22a8120b604001210303034480f040e0613840c0c190705141e05266007038089450540c0c4072184180200280003504c0890000b0103000070860054402c060251400418050705a04a00e0450380540000343c81d0b0b0883e824000d00b5180c40d50008081c624040b2644000242c40001c40300075070030030344075180050083d110000c1155003002010355407400d0102c1c1c0803100103800a198603940305240100c030869035011b0420004680c543c20314001519042e884018038150354140001c845 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 787949640 1106 787948534 787948541
    0x152d041a030108010e070602030d0b06071a04030e0609130513050f01140610050307180504090302100f02120c031317130b090d080c0a0812150103 64
    0x2d6141824003030940c1c0e408442144181c110790030511a00341e000c800c485211031000000700c3c0d01c0c8034400c081900c07441802c0d00580760b0311800d41c0c81303900343d030003000e445010701d000b41d039100f80c0404020100aa0391281441d0943c4c0a007200510308020449a000580d0000d80000c0224403d43c1030b031241414407030307071a020b0318499540380c1c05198038841d000d0f000c580201080e580114010503107240681741c1d11000e072980e801d110f41e02c0c5d10040c41c00301d0340d65510090203010704140903401881c940690f580400845501e501800c1001040c01d403007140c801d403480e40740340500e03d250b01c1d107a0403000c41c402e0740098142c1403c50b07800365404000c101c1420042c550000241c0d0f5213030385d510541c039002c0714610a98000c010741c07207070801c101c00701da540d200c01e6001f0164009109650394030011501070f241090840004150900200e5110903441c600c00c4070b544980d08603d0003480c00800240114103d = true := by decide +kernel

theorem cover : BRFrame.Cov 787769784 787949640 := by
  have h0 := BRFrame.cov_init 787769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 787769784 ≤ n) (h2 : n < 787949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
