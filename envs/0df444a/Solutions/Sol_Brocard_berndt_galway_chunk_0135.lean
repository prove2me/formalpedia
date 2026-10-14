-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0135
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:02:50.16036+00:00
-- url     : https://prove2.me/submissions/8af4b541-432f-4937-998b-c4d455c819e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 24100725 ≤ n < 24280581 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 24101975 1250 24100725 24100729
    0xc0a09090b0604020901030207020a170115080606090c121008240a050c070c0801050406050105040b0607140102040b07140d0804020a120213050408070c140d0303110d11040905010603060302060423 86
    0x80303126003205030290000003304906400901c02c860782c40103060300f4103100a00b00620b5950720344004050a10a6040c800080c00c2284640d059900036484840b80b0302c1d05050011544544508902400e040782c440c0c69010b900f402c114000c581c030300780040c100340c00032a16413181c3d0f4005040003c0507503003000c004002c290009648031101900800c40c0c500002441e040500c2c208060300d1040e07105a11842c142209070710295140c0c42241c85c100da210a03801d602074403240d10140603001d141c0c42001c181001042ca40107003c04000d1101a4070038043c1500d61054081c0800d840001065030081c2d089410050140444d54480502541981c00146084e141303100480841c0181e4008580440da02540841c001d005c100e15107400b50007514021626040c6122a14085502070150070b01c050101a12002581c21000d00c107001c0303031070307100d603503401445010410000c00315103503c280701e103c0009242c0400059054864420102076135070051210707207490b26000899050540e026480d1811190580301604c1503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 24103225 1250 24101975 24101989
    0x5090a02060a1d0a050a050108090a050d020a0303050109050106090314030c0703060f0509010b010212070609080d05010305060702010203070f051c0e010506030106080a120c080c0604050c0a09090b060402090103020702 95
    0x81200da49988000d40f1864129001c00d8826401ca40200f5440c0c2c0144941c0e074401341c0c2c3d001503910a103044941a5110082e15280c011843c1d03015200c4d014407925109010703408134140c00700038001d1314140044c1e42c2e03641c018000c8480074420f10b40003904100042c000614241060b1042d004000c08490500200400c43c504003982c60788102c82056840a6090110503d03002c1e0304d6000500c003000300052484240007079201c882c080020b408115000542404105803584501141e035040903085031030710085540d14005040a000942e1035220306000105914814021644511020b80d035204002c48510016515504031003d04034005a0440c0303403454100c0039110311204c002044d400880c1d2802c209080c9401c4800c0c5400100450b08000c80e45004a981c00c2c0360800c1400a52602c09120802030414002c2d90090f81c6010100e4082c407001d000c00d01c5400152080140f0040300d0b14040b0301d6403650500e04031220004001d0115140000080140c503240d4003500c1d80741410b040251805429500244003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 24104475 1250 24103225 24103237
    0x50708030301090c030c030c081801060306110306010206090a08041503060e040606031e020a0509070504031a010311010f0c1b0b041d060909030409020901031401060201050403120510060305090a0206 87
    0x14041d6138010421103503a0502403018643c1444c282045162100000182192001881503e881c40008244043c21009610030340003160031032000c0100c0c1001544002c2e965000303a9a240c01403181d000440c013032900c04030b0708c1c51019a103c43c42502e414a003a00e60821070040710b281d9020705582d8103000500904c5910428811403040304001001070840c0303011b5488401d004d91403c10b4084140c80e100c01612000c40d03e5080c0c841c122000d46032580c0b40b0f0012551840365400040400b500c09032104c1c0b901c00003c103014141c80c42803420b001180c4902c0e00441d441e9005882c1d49000070112005d4001003140109807406d901a11140d4004084d211450250540c2c05607020745c40c0741070103c0e40c014100000d03452003600207030220341e20310a80c01c0103451640c0da0700440c0111848107034002401c401c00d0b80a0740c4250003000101c4101c604ca517135510b40182c0288000c0310280d01064240c0c8000c0840b01e02e81c40b6451290050340d04103c4080e052410803030042500500906451040c110418007503900c000180003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 24105725 1250 24104475 24104489
    0x50319021908030d0e0c0a061b0204060b0c07050603191d0607050c1002040f0302091306090609023d020a05010501080705011b02010c0807030516050c030c060c0604030507050708030301 81
    0x13a45885008104c0c089901c1c16200403007941003019800341584c2d40c08140001c1390034a1900c160740703030746491610b8032001200c0e40003540b0900d0f0420014201344204042c00c902540901552411603a56042c021a4030084402d4206c8502107104041c800c245035029200080402000081c103200300011070703103810000d8600b08003207075011490900c4213008000d500c0d41107009540079810203180641c81e06000041d0302000b0320032400600011400c00b03e1112810710035810600900c036403085811b04070020902c01c04103134000d11011007030006144800386a034000b0f60403951402c2e408030256550203103a41c0c4219200d01140500c0d191b440210f9401d00400b80a481d0102c090070182e0f192000140c041ca250107284012464050b203e40f0251380c111307011081080d0004600c0343c0e00e011a290849181c0302d10719000041041036660724080c400c001030034040d881c00950413901c03248112400c001b00d902800040d0303d4580e01000c00100000e204201a165141c030800803101c2c2951500340c000e00359082604294 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 24106975 1250 24105725 24105727
    0x20307020607320c0d05031218120a0801060e0906100e090c0a030b0102060f01062d02300405100201020c0d080f070f02030d1a06071a090705031902190803 68
    0x862104004c1c0304060360000115802e0440c54081e5441c0d40e12400f40428015080701c2e0070b4001003651040ca504c1c1355400300c50714141c80d00d07419220320004464000324440c0000034508800418514001c421451280310024220251799075203004103c0e075040014400020040402c08064042d01e8120b0b40b24010f400c0c51007101d440710b17602c0c00d0041c111820551224115400b20080c40220554050007505403007071071510300d000d403241c51082c44850301c1042080860f03034100004410300c20350101d107050183c041052291014100246c80a80046004810101104c0704100820280c680509440980c2440c1d000150501740e00d022a1070515141c21035a00204030b034401005003d904034600c0e21b9100c0c0d80c5090404060b148014000d40c0c0c0d00441d56010036080c0d86000d00c3d018507841c1d28281420640081c400d95036103805141400c20404003600240010800102091072410042404c4099410150080c003403104000d030440341d04011842d0580e00031006400340b0300c00002c81066400580341040040d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 24108225 1250 24106975 24107063
    0x3010b0411030105180f040f0501090804080f01050a02030709051306050d120210050c030a0b0a08010509010c090b090f0d0f020306040305030610020c010806010c05070801020d0b0109060f020307020607 88
    0x2000681741c40d0341c19130303a580d4800c0c81041010422040e045030081c0d002541100003180c5840d003a0700510301e03040080d0007200c000c1400204d0110000784440071042c0c0c4002480140c540c081210306030301090301c81da00494000c0d00140075505081070585002080504041a459075590118102005a01c416190480c9a00104840c0c82d01007101884a0361509010000c80c606000183d290380400340c0311851494450105080701d65406c3c5962003c1c1800030300030050f60510042079402031001c0300b081400302d411540009103190a070341c2038034103075030016010a0404200350b0400203240801801101e03013103021f42200c4090b8a040082c24829072198981c0c0d50350b0305000c0200105a803019040c14115408142d000482d0390380080c420b80c1100081c00c0c001010b0f0f00310315217942440d050350840a5030350700c0420840f4026100d5004651403500030b0320741000035916400d04940304940702180c00c1c0903078010001040141820f10081c0f221500400d04080c49010001c1440b1030120350f10b0403122004040c21003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 24109475 1250 24108225 24108229
    0x912050d02061012081602130203091b060d02030606041a090103050606030412030b060d09060605010e010504030305031b0702090405061008012a02030c0f160603050106020604060b03010b0411030105 87
    0x7506822196454001490380c0c90084e940c5940e000401c002000a0307008182d050314642a070030404c8415074028801d0503c1640e03510034030003c0d041143c1e403e2091040c05002501c105009900b00440c5901910f01454580907000e0b8402a51021b08869000942000300040420b1600004809001280300e0710365698800b4000406460001c0e0140b0710a203800c0003440002030004ca03840c5410345150070f01023a00c1d0400c1001070341d18002c8030030598605041051200400410703a000c14160342090300c0d41003c0c818450011121401240401030204804001080c810f0100c14450740d80c3c14a0f030005585080d06a078003090103a60166012a81d6a11540a0008010311103042c80c001e018800d00802514594403911807681100c140d0700003001c0804444112103d1091080711408560070041b40e000d03150398171440340e840503015a4070384030a0540c000842d90300d20a0107550704071401d56000b40b85e075848584030b42c03001300308070607401c1d5042d9601c04034442146c86a01998001030042c8452607265850081 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 24110725 1250 24109475 24109483
    0x5010f06090506030d030f021c020304050105010605090a0303030908040b120603120913090206090405010f0303020607020c1018030b13060f02030402062d0304060903030b010e150a0912050d02 84
    0x7218414100341c01c0107150b0720002003c0c144403005140c049004003401042400910491664260314081e401c1e00d002281d01c0740e001540160b02c14402080180ea954200b20380c06d00900d001c0c285c3c0000344150070001709200703800c10050301e8050b0043c14942659446c10a466038003c0141c0c0d1341c440111000c00040345028407100c0c50b0700c1d01404109103481c08250001c1c0175000e81102c1c5208480d43c480201c4250348414040da0301212025104100950311070780c02e490307610010720084005200700400102540d10208131006c0144016006640c2e1050071038064400c042402141001103800540c00404242c1541001c0c0c0200045c90f044018408542080d00940b4040c41c2d04018080c010014000107848400c01c9034200d8083c0c910014540030b4041444860f03a03880741804044070408010700007401843d9000b0349801e40300c1d0300c08000784c1454000544454140b41c56880d48420500b074100d010301c92400042c03402d88400e15120003c0c0741c41c1c5600b203017180644007042e0362540c0609580c400141e0100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 24111975 1250 24110725 24110729
    0x30a0e0303070e0319080406030c03020904090b0910020c030306060f0c06040c06090e1e06031903030506040b040e06010504180609080403021009210c090c080f060d020f06220305010f06 81
    0x11700b070203150190680300ca18042c8564400d200405950b011a040c01c0cae07220f43c0c103a030340c0d50400a0044c0014259030803d200c000005581000d80d60080100002c94800a84200d500e03086003180590700f90759071041008811707000403400d100121130420980d581d610062284900c20ba1080511203021810003800824140079070700030f10380411214060007040120081c1c024175500c5433100941d80c03580d5010109051480400140030703001d0a40c8200001c15800d03410841c46410151000c00c0030500310b40030807081e02c0b480c02c110100350b00900014070440c03e0640050880300011048c42c84080c00556074034040300d11085003940d0509000c60280308514200117812410345035460003c00280c03d0131159100c540d100c003004002c0d062410012810007501d545031000078500c2402c01c0100d80b80d288c6001c1c00a58003118039143c40d00811000440724075254038020b40c0c064000e044c001c403100d0716006108450780494195080307944c2c0340d81c403000030841c2e640041d0b01540c420000440d030721213131540c8038041e07076003036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 24113225 1250 24111975 24112003
    0x3020d030e03040509060604050303030a06060305070c0f03081b040605030414060103120c2607120810050402130503010e0a050c030d080604090c0f08010204050909010606090b030a0e0303070e03 85
    0x98115241040004181e80540344d040b030703a00301a5151640000c442d8403841e481913030103000100c10009203601c164800021554951000d21040c0e0722120100e40811107903000800d171501e0f0715003800120380310302d040c02c1c0d010220700704001c14540014035000b202d030450b034081c1d000604000100410422110765100c0c8811310080140302a504655914200d40c0329107504408004800d0300c0300302846046041039040324500203008011140c00310201030650b00200c015649001c0c0400308101c243e104880151107020400742003e1414109420040654800441d0101c03803115628086800d0b40e00b03108070024010504014202d03140b503072412605148050180c14800d030007603030a06c407220f900b050015a014800f00c6e800180302c40d0500e044100b005180e08890b0b40440c0079000440c1e122415030007030064580444940c0c8140c1e841080789404c0c2ca10342e01903880003519148d401c01c66000c594014581000c01c1c6070f4089078068829100601e140c0003141e510000a0380751030200440e0805110a999034280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 24114475 1250 24113225 24113231
    0x3060b03040b0c1e030103110120060604020913020c030703091706010311010302070f08030702070b16080a2102070212030c06071206030c031b050607030e01120b04050f0403020d03 79
    0x2d48400659810040c03d0201c0d10500162206000850b0346000100303900358408180c80396140d041824507910188045070200d0000140e04044c4040e80e90030150001541005044d40c0c3c1c0c42c0b005000c040d411014806e90041102d903529007070898140090322503640b068000f1602c0d80c070355040c02042144a540650116003040060034849c100108205054980090742c22904d11216401200240300301040a0814032401e0444000c0011900c01940034041c140e00b00c0d0310450b1030b818200c0d990b2013500307542100681e2014076800060a800058480e5600301e040c001200c50b01048182400c42c02c004c582d407045c990002e402011403078180c10a00d880d9041c800154205135200900e1540c0d18005881c880503c81c060a44004441d0642c018101840d400415050142d54034607140c00d2042c01c10400800c0b07114070460203d0981084800d072866950075030b68800300c0c0036141c0015103102190f1501c900d0340c00d4403100802c60f035841ea8001c1c1402954411034404186c6013506000f401d04100016000800d41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 24115725 1250 24114475 24114481
    0xf010b100203040303031107051c020c0f0102070e040602040f120c06080601050706051008030703030203160c03140c010f09050a0203010b01050427090501090302060109060e070816020a0507120303060b03 89
    0xa070000545041d01e42c54100054401c1030611041898000c40b20b0080080c4200c40443c1040004c0311401220107030641c08a54000306101c0800c002e990505d885280142d0204204102c007230405101715400a004e0350005240c1510303840200300100f0250801c00003075070b04103034020400080c80b004100401c3c1174903114500d421309800080007881102070280105031a40f01140800300303000d00d564010010201100d650f8507141c50054003a4101302c0782c1c85410303880d5400c1d0303410040c041c03804011055071540ea40445038180d00d400b614244c2045400d00f923650b60710130340c40368000d006105201d15140200010041544d0b680b04050940e071052640310f04200d0144402c1202c0c1160624207156a40c210700300308606040d0f01c441a00034185040050920b40c2021000018140c021030703400c1c141e4000c40780500c0040d854510f11201e400302501c445001466202c005403048011641102005000e441529284059030321058130388081d80d08021801c000702c40c0356004240d01071041d400100ba10540041c1146 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 24116975 1250 24115725 24115727
    0x20a0c050409030e12010f020406030b090603030405060403030507050c0a0b071b0f05040b04020903060a020c0601120f15090f081801080c0406050a121103010302130e07050f0a03140f010b10 83
    0x3400004c0c0d5402031602e00c0000c0e014002c00e400125032031200384821910740380d4400000303001d40b180c4442c990181846c4d81c0030034041c0c00c1c003204940c240e8202400803440c180c516942140c007a0300815040e901c600400e9103051039591202940300c000c0504003082c2d9260162418211400c6860014000c108200000100003480300b840e4a070b011241e04482c009591a0280d000c00e000c0e108403540389070305019003c2003080782c207030179800391010303a07405011121740d40c1c0c1f161110f403030500c40d9400250440c8000241080003c001010440c8040c44021001c01c100109a0314000d1105001c8030031140c000d8045015022207a80c6803056128607003d103400e2040b8180341b50440081c2c03103940076000400c100040c88040340c9000d0140340b00205042101000546400c56902c05107030401c2c08100c2c412542e44d0340840454083e8011031007601e66401c06010312a1600040001d212020790445030030011680340080441e01c001d4100e01c000a043c2c016203841d12080103400d0031920300700642482502c1900c000c0c400c40e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 24118225 1250 24116975 24116987
    0x7030801180f1e0c1103070204050a2307120908030406020703090f1206050c04030b0a0903030e1506030f06010b032202040e030a1403090d0e0d0b07020a0c05040903 72
    0x150880c4071021421280d50200300042d0558101d00d08855040000d03140c80f8003203e6200d2444018407000411650b04100000c40e40e13241141c42c0c4207641e601c18400e0f20301515103039008941048481900040c03040d01c03499916611505a00b050001a1403170041055480d0000c200201c035032071112040044002c0741da162062800081d0010f0050341d4003240c05002c2501644840020b4a4188241110a80d0701c880030420000800d42c01c4420509160100d0160003460083d82d094a600c0b00410100c0e90315550058010080100d0607010151030340100e00ca001c40500042c4581210410704180300d01d4958240341c0f03002110b40c3c2010309640800010000801604103694102c13061031101c071482050f8a042ca8403444d03a44801a500c10f1401714020110742d00080181031100c500d4a54902c000c42904100c005c90104a601013441c0c0c01c2040300c0304000384140145d5940150040101d000c540b50340e104d00103000801c949820159012080780c5080c402d0051a070001032004803401e11208016a400520b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 24119475 1250 24118225 24118229
    0xa0e030c06160804030b09060103150c05030105060c1f061409040f120306030512041d0103020105180a0906090204170303040c03030e0f030d1808030c03031b12010906170307030801 79
    0x500c50b04104510100700c900c20480c0d008580001201c140c505010380c50f582c45140c20300c0304441380c000c6d074041c4914a000798001c0c88141320b00d94035941c0c2903a1030316060180b1644035621440b01d40c0108000700d0690310301c180c0490070b228644840007a005081c02040e0407804207544415114034400d000b00400a448180720100850307104090b4040c1a100f4403058000d030102d500014014040d4003082c802e080b519401500c1100c1d070310f8484032030a4010441110f5002402e0002a0010b0800c22a4071100060703024603c0c24100c0107402d640282d541c0c0d440c90812140309030444443c0c1c41d0001070030401004105045091004410b025610b11304155651103034480b4184001414045000c405680d648c1e40e52100c6014008003800740c030f90701c01c001d0741c00030702605001c40c50020569039504081640310340002a41c911640300c900031071554640c1450005c030300c440c031180134080c07000402200d4000e61a5032804e0380200700380c0303c010036007500b01100d4180d5041003241c07004a0b41d00070f0140c00042035202c549181 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 24120725 1250 24119475 24119497
    0x150c0207290706021e041409010e040c06030c02030d02030c0403050105010549050601150c170c120409020301050f090c09010e030c120a02090702011401090b030a1401020a0e030c06 79
    0x1c0d5400d006246001c85d01d8240040da1103d4002150005045a14030704102c2c1d01441204d2503074680e03072070741320410000200383d402500701c00303038488203111446c0030b0741c004e0032868801d004490070803104800c18400c0e0303441140c42200c2250302003002c0040080901400f405450f0440e0b00c003c01d062540b4241d4140b000c8040103024001480f0256900c02c003d5008180784010003107103a1100c601c00d4244140c3c0c440d400e10922362000c820840c0140018030800c10b000119a000d03c7c4d4281c6206040c03012600358106614808041c0100000c010250742d020009000501c910500940c03a503240c9000c2000d42011a12218041d00c8031100704046001c55104848082009013008070000c0c1940011030301d42140072101d42d0304034880c803048140c6030200045402c1494800c41c2c00304450f07076410400f2401e1303440a007485541c0009400c01400b2542c4585c101c24240400070341140c0c3d02d1513654807070401c810b20303050509a45035800500c94424550102d480c03028010180d00410011051401040c814421520465 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 24121975 1250 24120725 24120727
    0xe210120071101090f24020c060a2303040b0108010e0a030f0807091a09040f0b0108070c031806090e06030c060a0e0d020904030306050306180712150c020729070602 72
    0x482d0310b81c0543d0100d0042c003c40b1344245180c40d190140140040200100b500f590486110340103030300c074030016240300c3c204406031a20341040403406060b66600d4088140e00ca8101e45084c0d4400d51007000c202544c0b246000701841c8007954580f40041c4d08403020303029051a640c1040d1311150102c0c1c0c01021410b0013060a00e055101c40e07a42030006c43e42d080e41d9420401941d4128048000e91700c8502018107002c0c0807c490400c03036503040c0b070341e01c10445980207840d6001c940540001003581c0d0080b02d080b01110701a040954100c40c12402c103080c4410960410408601c04c0d04080c440c1d00c8002c410340768880d100b03600901903a42c0340720018015001c6c4000c42003c0007200718101800e6166231901038001540a01940c140d0304162401402078400e601425000740304500024103584422808000040406000b51100500b0864816035164000c401651041404d01800314001c3c180c0c40f80c5590784007141c1c041c00e1100c2c2003404000040c2040c140c5008481851400b0812070b00d0008112800e0640c404401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 24123225 1250 24121975 24122003
    0x30c0313080d0e0d030e03060a0e0114040b01170a08070f0618020904120903060204090c0806010801030b070302070204090b0f0405120408030313030c020303070503091c0b160e21012007 81
    0x480d41b03880b10301c403031503014000d10007486140b10142d00010100c0711104020b00100d0304000c002c05800340200c2c0d029040114010040044a4115448641034408081a92200070850f210401c1c03542c49900111140540c003000c04013488400d2080d00405900e07515401c403070181940000f004503801800c0a094203000c0780f10034010320300600c8810019544510195151907031850404020141e4485a0300842e0501d00001c207550b10610105060725401821240c29440d0000118000d40000e42d040742c000356610358076801300d1071141030740d07116889600040c01c80c0d140500e0030354108410003c881d244504240003d000c0200080140d0380d000c07100028808840b100e0303040848403002d14100107500343c00002102e03402d04c0004030041550f00000d41e81800ca604081554203c0034400d140d020382040e10807408a0014521196003550101c0d1520b4851100c81c00000055460340113602c4009d040d0403034500a20400e0f40a001c1c0007100002454020329101200d24100d815114000340200800500900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 24124475 1250 24123225 24123227
    0x6090305100515030706120f061203050306040213090c020d050313020f0604051008090d05040312030c0905030105131704060c12030207050d030222060e040e0a05030c0313080d0e0d03 80
    0x18824001200508450616943e260050001e500301800e03005135032300388840c243c514420741c040d10f0100e0b00c402c81000210300498030b08490b140c1001e0005540513400b0400d80902c3e0002130030f048040c2400e41000280100000c074041d140c01020202542441420303c10490352a00f20030134100c000742c058a0500c80f020411001071050310030364000c50b80c0503607940c0700d010080340c1c010b00251080c0d4000c411079944d012411030035981401544002071588449000b00e1315020b1003500100c0e100d0100382405400c0546420000f42545d5044800722004c0d1a2580c01a044c0401c101c5040243c0c2e1f10f919500d03207400e06011000700200954180a807141e64042545103105200b5411143d003180c21500391103014401341e10042c040c2d880401d000c003040c091200b224007003445c852618070417100d05031540500317105141d00f84000381580e084001704a000c1c000f91a008243e00b0300c02496001ca50300041d603601c0d90300c003040540941c06900300e03135a141c2c000350141c1d9105410154a06501c1d40071220000e5803106460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 24125725 1250 24124475 24124501
    0x311060906010b0327030d0207020a060c020915040b0301060311010f031406041e0203040b0402010f0807020c090a0b0604031208010812040303030b12150a061a0706150305031201050406060903051005 87
    0x141e00c0d5003440300007040c1e0b09041180c8e01800b0710034403c07100e0280d003650360300c03040b1019009510040e40c0001c810700410550b211003504c4d0304000c08003500100d0034034541000682140d00740d41c42070b186607002411034550303980d20041d108142481d900702044001c8020303c1e0702022031002000d00780550398a181c038a00c207101c01b142042503000100e006640d01c0c5064500f2050541d4155001c9020489200d203582c005030290f030ba581d1182c152540200158608613040110948020380b000704070503504c401c0102d49881d03c000500185004030214100f07203a20440040c00700805070b0056805400c1409030740c02d402102c13022202100d8151502041203204000040c004150741d00404030039115141040081c02d4903196401d02c1550004020442c0d141e0710801d0744000501d54a596143c0ca800300f1103078000031b165902907109210f44524591600e0380701d0755824550740c065082c100c41c0100420040005141c940103a001401040c540303032900341d240d955070700e588100c402607007600c003520b81001610a2140e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 24126975 1250 24125725 24125791
    0x303080a0908160521090a06080c09040902010e0a1706070c050a0605060f09041406060a0f03170f0c0f190308040312110a11070909020105030c0a0905040501030311060906010b03 78
    0x1142817190300201c0785281405d034400e10043d03008181c0303440002406802051018030404148400c54580000f8901304001005140170880c1403003804181441d4540341c000e05030000c0c10305000740300e0080882c040d24500d050001006002040b080580c650009400800d05000f20f0703501c85c001042d10b446100004200a005e4039065402024503410442030210034042a01400203060984806840300814000d2020302d0f40210201e2400b181800c00010700e04441c104607032503924440f00d08107548600000c40591014801c1d80303240e4480028000c5d400002e0244a103180c0d150744440e10120302ca0741e8040e103044401000a0144070850078090025142c2d50842c10024084610040e62040d03102400390210307a00101503455031049100104a41480b8030400078660340507160303242503a07034021064003294085115030f000c0240d07c0d500000c03291150300a0703a0196110307880d81c0350600a214a420b05d0400c0003042459990301201c01040452080d0040303079000070f0954040c80503c4031003000084074103c0c0c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 24128225 1250 24126975 24127003
    0xa0c020105060d2102240a1508120705030d06031407080303010612020a0c020307030308240a03060213031707062703050a09050604030b061519051806070b010303080a09081605 77
    0x89036500c480008040c82c41b40c802c400113002040781103205448086040c805018550a0f41e000344080c10200107980c025048281c07213241247d1408410010364410b85200354030480d28039038400c900c1031b5000c100740300031009000c045004605643c503000d00108a41411401c8414540c2d001900301d0040b849810014282600a011640070715941e18000700021401c807003460700003a441801900c94800c0500d03808425100400c0f042016003152600380095006854500c1c010541e02030010005008410203590203109100c502c1e203a0307490341005011f5a030b01c030000620314000703035108190140c000c3d1490701866805181c419101c070880e0909440a00083e0003640d884140401c001080240840c8400c0c8140d0080d030b1100c2c1c07030080c00380900c070303a6019001003074003420704441c4d4610f4039910810203086009251030280c00c1030040540401c00a0b40148000d480700f03d0380c0001070003459007141030f50703402c80742c600400c1000790b00a84801903240121600c040000a12021031400e00030200241124030307080c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 24129475 1250 24128225 24128263
    0x9030204050f0702101104050603060103061d04030206060603071d04020d061e060201050c0313050307060606050a090524071109190e0102040302090a0b030a05060a0c020105060d2102 80
    0x44940b420b031075250201e81e8440188144449411800007a001c0c2e02148215148064205800e007030411645400040c4a41d041550320140000c41c45e481501103035240212040b03400c200d09041c1002400d0000c01050207029038001c00510166070360081700302c9103000d200354060f018220340c0c40000f4068442c2001c0e00035403504120300485d0b050b04a80c03103044601c0d40d0342d180c21245a5209000e90a907030b021240002e0344442440007520760b8142400c1651498410411340e80707444203903a40c0d0700448195400107400a1000300d0b144100d00d0704048228080e040c01c407034080440445610420842061002c115004500030a1032020003c03040006040303454010440d50061410503859800303024240c1c3d01104145c10401c101c0c2d00e540c0d06200302e6050303d40103401044180d4410090501420300c96209980512440381d400f004500203100490280400b4200420200e8480600078292480a0000f0b880740e44901e0510340003903010003640342c403d5101722a0092101030900c0903030500f801400b48400d402d034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 24130725 1250 24129475 24129481
    0x12020d02030f1506030601030308010510020109051006060e0d2f150702011404060801030201050c1c050409060b0c06060108061906030203010e090109020a0b090301111c0612080306090402010903020405 88
    0x4022a03c14946800304200441558922042541d00c41081c840030f008680705200501a5051800c40603580c6400c9000114096206030740d514038182c0d071100b0410081c0d030760704014052507600c8000300410503c206c840c40808055038441501f2031040d131200000d9000300904c015119003036100c20042001c0000d001c0d8000a90241103101c059111355001ca00040c401940c5440000585007941d090316260703500c1c0e030320681c256030041d43e61b0380c41101e0007485445590b00700c0044070243c0100c009013014554640f40c40e24940015201521016000000402014080514518400502d060303010109181c0f0b409580c0750b440110f85242c2514043c0000040765a102007030441d0150015412150945040b41c0d040d610300105074202d4074003840082d8071407004981040503044110140025220083c00018028982072400e80903030300c004d4100300ea610714861100301403001486080c005144a0001c0c0d1594041c4d070fa180c00c00d0380301c01007415120300343c1070021405691040c64031602656000c0c200b084a41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 24131975 1250 24130725 24130753
    0xf01030b060c071502030310060806040603050d0e010e010201110708090613030f0506010e07020a03080c0417100c0503060a03060507020111070f02150f2a030a120b0108010302090112020d0203 84
    0x100b0745000b94081840138102c25a0b280e8400403c481c860740328040000d4505040c42011940c1104c050079007035020380ca8030400b1000c1542032003040d22114490710703105804203088001404401d217115995042d03901d02041c03003402d44074800403030300c0c0ca45c0c0c40301141e40d440c1c0300800010007034094000100c12404040d6004010416241d440c008028059411184580c0e80c0302c05041810108841107001a00304000c0030000a0007429500d4201d40d02c040098206622503080301c0092400c0010100d03250b01c00b58001c06404c8442c46044c80580e41c3d80b0341989540303804d00c08513010a401b480010880c69540000401e076502c00e6001d01c0440044091007952144a4100000036202c215401d078071800c051a0780e0003d8010b04412580e0b40e420402c1b000d41041d80c2c021245042c124081a4260b00000c40c214180704520288028a80d001c030740d8072110f206820b8101801c04071620302500505000642c0014000342c1d6404200904403a0a0140e41e040307034003944081100b05021110094043c8600d80b00c0342602 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 24133225 1250 24131975 24131983
    0x20301030c030b06040204140103090212010e030a2003070212190305030a0507080103020102100c030e0601030804080709051e07020102070b010b0a02010e12030412051209010b100c030e0f01030b060c 87
    0x80f03008140380c0c1040d07240c0c0c0d0104001c03403156104d1065680c5c0c0804000e01c1e5540250030103820035000418200c102c00c0c003068000c0c291a0070030a9903d00d60000100001d12075003244090203203c51641070b01c61f8204003801520395922800700083d02c1a015000d040034200010450030b100d20307032905103510803221640f4002d46070740c00c2502c0800a807414200012021407081c0910f50480381c050307004010705e28081e10708000a00300c0d40301e10390800d9100e281e130545510007004954000c0d44645d82d20b076aa50b18210055003028820b800003002079040000344600d540090180010a445030030186081e904c40c900141d0081c89041c50081c80000d1200c00025843d00b010080c0880ca0381c2c50700244055580100000e0f2500030203d8641110a0700b030001c68041640055404a050070030b042c00d6143c2460000c542a400c10125415040343c0e45a02105806060140f8100c40400036401d00d1b04160006550141c0401101c01c0401d000e14680902c2d600740303a2184c0c20038003c40300c024007910396495007000d1807600c3e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 24134475 1250 24133225 24133229
    0x9020405010e0f0108070503090307020402071208090d09031506090e0705031011070605060a0302150304050d05031303030509010f020c0703020a050a08060114010309140d09081b0d0510020301030c 86
    0x4501d05501e540010f007000c0e00c103000601c0050b56800855940d8000c06e0350b841e0805070070703155640303c20f02004005807031b076100030201b0324010400c4a1011a15000c01094213030002e00d50903076600200c400c02e07941c54120721100d058981c05a1105c212007803901c40fa10003401d00d40d101d54035060510f801c10100341c1001c24824181c030001e800340d8580154040300d040945180403001c0300100c0c001c00681c00403458980c80190800e400501c0d411485541e500022145a03003030104424183c00001030004010040084012411003401e05c5c80c114a171a4210307880c8111350701005000d0680b600000b5590321001e40c405801c2c0200944110340f075001c2882844d41d0751600340012405603a646101041da0710740000c00c40100e5032050001c10380c907820072154640075104007100d203040c591076140b42c50000d41d424000b02c80300c05110009140442c0101d00c010309035400da40c4840d002c2e810a549a211070790f00d24050301c440308400d48282090b8a001e140075480c08000840001d0001d00c04400030040040010f0041c0c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 24135725 1250 24134475 24134477
    0x9130c050d140a0e0d09060c020f150421080306010c0606030b19110910120609020d090b060f03060117030f04030c05030f0d0512060112090b0601021605030d080910060902040501 78
    0x206004402004d03076960b0b170f400610001c43c640c07031000c00c0000d20820f0743d4060329102400c9079004d00600c1e00808c480b003a210301c00d42000347e000300e0140418061705801070035000300071034158040707041d40d128500a480090840f80c10045500c009400740a03480c0c124200440c2c1c080803081d4980f800481d816103488204450001c00e80c03c2c001a9024044100c1c00d403511114020030900d1103c01404059030242110411400708039124030300000c0c10a850b2001d010300c07440f10303030011030710101c00e10745000031583c01012a44100755407041c1142640300081d035141034410a40342000784080c1d00030462f02e98051000d007910090000900842000f150602403012948160102e892204041c1c000390341b10314540c5041d100155003804265078002170003011a400140c181003141490200c42d9403001a1000d40a099070641480000d100e51543e04211503210b04510441e1002281c0c204030004e6121005884041c08000c0c09402184014005201051161051a508001065450229401a4000388a114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 24136975 1250 24135725 24135731
    0xc030305090a0501020a080301090914030309010f0501050607030e090a020708030a02040806010609081f0912020f0d0903020312031f060c05070501050403110d0303020f0403150b040209130c050d140a 87
    0x83e1940001030001c16a6481200107085a0a0808106c000c1091001c00e880e501070340e100f1052282020710007140200c1c01100041801c1c182e4550010503180c0c180e000c1802800304000003004260701120381004160101c9088100f40c0300c0440b40e0010340124400500349050000600031803650300d074001c10844424006030f5400b41c9c3e8513241900c030134402e44500b14094200d0103844400c1c0c1940c9282c20180700f81c0c210009040d407000d840c0c1000c2c24845418a030050303803003103c4141080304e00b0442c01c84c01d50180d180038030300d250131030740800e8984101250701c480145002c27011604004840c00d5131540e12442d0174484405036a07441d402001800e022038183d585000340b40d00400e803540326200b100e00b52900890442d448040346818048001c42254007070f82050760070300255140043d49802000118003c0082500c148503050048085820080c0c41c24031992041140b00c41e540c8403107080c0c460100292600240ca161448011b075010312500d01041440c51a00f070015000d040d50308100c41c041d5242403810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 24138225 1250 24136975 24136979
    0x406050307050102033a05070305011403101a09040c0e130309030b060f0301020f12010803070302060606030c0d0606030c02010506010c0c0b07020a0f0605030412020a0b07030e0a0c030305090a 84
    0x41900c0340380307a005850058100b00203110300b2180404029140300c00c52210101280520603111648580c00d0903400f03152030700c400502c80b2003607140c015907015121030b1201800c0610907400080d9909450720500c00000d1b107440791013455862a070007002c00f00f88040c004e44420719003860600f0180780c15001d43c40c44103503824041490426045000e031581a0302d525122949070458a500b414407800425155100b03072405211122520300380050140c42c0251400c003078075980b50304a0140340030b40503045039515910a0007003001081d0f00144054020070250fa69a5581e1200c501860a40c403400c80c1c041d4215081c1240007a001ba495800b41c2c0c10421036500800441e12420011141c2a100c0d5501400280d4040030a00c000c2c40c46500a10400380b00078020415035035910104101100c2c00e502486c04907201100b04403d2010b408044019402c0904c042c0210422503521503903042c0c1c2c054015001c165880d10412a0340b50208030040781e0381c1e006020244695602c0c50001c0203540614404c030b00907039481c100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 24139475 1250 24138225 24138229
    0x809030a030c1e02180c091201050a0605030303090303070e0a150203040f0501030212070e04020c0105090604120206010f0b070c0801022706040503120a03090f03080a061409041719030902040605 85
    0x41d000b141c0c0c010401c502d0301d0040c8807103171004000503110308203040381081640104e503035424001a82902030f030008a054a41b0002e01d808841d159403045001c2c0d041081003101000000c404c803030380200c00e802d20079050b4a00b640420201c502681054420203100f403510002960000007410031940c0c808031102940ea141e0004505078015040702103114075142d004140d005016030000c000b41c0c1c0c070152006003082070740301100b401e5900581d14514a034101c44144000d001c07031152051842241e6000030001949400304507021990103201e22103040342e010610008100d0760211440c01415807500940d124030341000e103100081408113003214080d451003519400c600305102a0f6007181c000801030700e011169404158074941c017007141c000406545003104800a5034420700142d42c0c0d8000e82d5484440d04d00786948800321003558204004d40c0b16550328415040c0d440c8014554402d0b0b000d2904d0990701900d031082d08040c003601e4040038030001445080b240982e4103034407040030300f4021503050003210340d5101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 24140725 1250 24139475 24139523
    0x9120509061b0102160c0e150307030f030c06050f090607091802030615030117010c08150613150c051207260d02030f0402130e07120809030a030c 64
    0x20041d030040e5080c00310340d424400d0542482084256400007503d070210030a022100700e0a10402220740d05e049100510200c03e106880320b5010040c403407803000400c09003002036a0341c2d21511005000781c404144d1101010320500f40d040c900f0fa80080d0601c02410070342d0f03005940f00341c21654803038140b241c48001600300d8411058242110822103000f0007003804d240182002e035100510958200488550803510f11804000441c02022800f045503122488080b0041c00c0d60404200074040110002c2030105105503132503841034244040b501140e03261454130589640c04034a501520042d4480e4044240190304861030b80c403418400d20581707505641045c01e40303456005030780c0040d11402d0030a41e60311040e424620070f4044210050030303c50030514018450416a88200c60b0040c0c01d80400c42440114101021950000d6050a80900c04007007690b541680c1c4e0a0707a07105d12404040035508080074403211000700c03142050090192101310707000c1e04010b84a00c1ca0100c048401da0340b81007101070740c0190740d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 24141975 1250 24140725 24140737
    0xc0e0910060315030507060305091905070603090201030f0e0f0d02150106030b1305070c060506040c1d0604051e010f1805010309080d05101a0a0804060e01091203091205 74
    0x44010519035040010440c0280f0862802d508444458900800400c03000c02c50314009003c1941e0100d40e900d808112141009102d17010031240804c3c41500c08006003010401200f50b0b0b61030315000841740e40304d000407005000e000c000303c400c1d185800c07003041a0500c080351070074181c103562040781e0304004035140484c0d481c09000c2140341c14a41050043c4041e0b44240c101d03003c4400004d211143c5143e01080c2c2d13100300c0c1c80503039034880402ea0340ca8a0108200307480c0a0290720000490b420040039601160183c005103002c100e016441a6100011080b0303560304007503801908010b880c1186580c03900303109020107d880c0c1e410301d004c51041440d004075a0720408540800030484a02e041256151a0054001d8028060100c8000900748018842c100e041d10806100d035044000b1b10080d68641108800581c0001c04141110201040030f902c02c240c000c0100e54000354041c10001d1506003403107022b4010002c2c12030040c5510689807400b01c2c00e80c1d02d6008030301c24600900c0c9040200b50115401e1311284290 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 24143225 1250 24141975 24141991
    0x406060203120a05070c020909030c07050f010804020f1908030403060e010c020a080a05190203030a0b0f01090e040204090501050c0a020c041407050315090109060303080603030406091a120a0c0e09 86
    0x684002107010031542c00441c4c0017280780c1032440340300466a0024940c080100c40e01400741d80080f4400310100d070200300b90402040709969114440c045000002c044240040c0003902441c0500c1821480b511040e0304038950080d002e42c002092a10b1b03003117098503907000d8801520074a0411000c4123030701d4418881c2c512403c1c0c1c590000c2c281ea42d05a5120590b0750007944003481408414081540421507c40c1c076806144d40680c00b440d943c0c5040b10522040710b5000307000754083d10030303214240d2060341c02c050010241d4012400d150966900c510003d0302510740e4240040695003081e040c00000c45000d8060308040060382c003900d03104080d000030300c411a50307050300742508050000b0203c2d501340d002d00700a41e0014026495040c0c940004000f040072200c1c2a4081c10b000c5654074820820705500c407c4494220404a018514152030030f03500070300000ba44d005002074000507150303402a50f45001e003144c203984241740480d4828034141404100401c00030284902051509a141440d840c1801c0000c0c402c1e005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 24144475 1250 24143225 24143257
    0x1051005061c020702090117100608031b0106090e07030201120924090209010f081002040b0405010f0504080a060506100302090108040308061206010305030c01060807030302070506070303110c06060406060203 91
    0x1036541d5403040e41031519803081c541a0f080000e0300168a40c0701099000c2c08100d21560f142d5842442c105207480860701c0c0d0f00c0101c0346820740500007020044122460541d00000c424483c50791b401c44e0700d00405556100d141058070380000c100a142000c10030104890003621440b00211030041001d0030364903c03045c0140810040004640c0f0015074045030311000b03261b00030003e040c14459010400818080e04040c001500e40360082111803410030101d55a040d8900701941070070b03d080542c55a901403409100c0c103100c1c0e0410241c4a10744604142c074010300312101120b01656450410b20700400059803810700400c074079010200c00900900840e240460180c0d50480c1b10fa40f551000c640c001c0b0040c00084e40080c0c1c0c02140514070104021490180d80580003440c0c0d0391180d59840c80c02c5035441d0380015903d0b00710980c1040442c0e0042581801c546050b20740c40c1d500c1c0c82c42c1c982100244100e4991849401c400f08440404080000b43c031841514280d404100f00c0f5110001682c0d03900a01546e034a050795 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 24145725 1250 24144475 24144487
    0x90b040501060f0912030c0503070510050601110c0d0503120708061c02060a0c021903030302090f03060609010b0f12010312030509030301050f0409060f020708030a050705040303050409020307020c0a08010606020105100506 97
    0x40030748141c0ea0f01c1740c080e1505040c801c2c2c1c16503480b03045030300c81242960340354041045c0d480010160320034603070413650900780325010b0310340310a240b601c440189100c40d104605454414041c01002d10803604020200c601c40c400c14545010080c0490005480050141d240311a4021400d074544503160100d5800800f203905205550a04403451001008226004410b41c3d886412400c2c18024120240d4842c0c5ca000d61030b1510788052044c840c8a00080354803c0e4452024040c894682d0042a8150b446600e48159035102d8014480b075580b107014900c0419030f01c0c0b000000140107050351401023003042990b09004585510000554a02003030099503406508042070407514a031507802441014403031040420403051030758550b81241c020310740c155012000003041000681c003601c1051760090f083d041c0343c3d041a055031070042440c003a900a180d115607000000c102c840d40200403405449000500046515440d0302405010307110911138900507608010200d03ca6002c100c0c552015944050b10680c1000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 24146975 1250 24145725 24145739
    0x804090921021e010903170901061e05040c02010e0c0607020109080a08211b07020118090e010605090c07020103091505090303010e060607110f0f0901090b040501060f09 74
    0x9103090212011005810070501c6401500442001c81400350050320b18240100e800d00c01c000d00c0145182140d901d4035241c080080d4120051f250804007404041503683d48001405004240540003452221188130040c150700d0604800303002518400e80b4184403c41c2901e40c01c1c2e0903900d107450f1004c4c0d82c0e00444004200c030305119001d48100c90051400c2481f540d591b46403941881c1a00300252554980060703004106c9a42c0740001207003040c03802141032a864200070b04405601901014210300c0c000040744029684038900003022402e00d058000c0105030740d401910003c0c0040c52204059508002000681e440d240b441d13280700310b10442042d0300d09181a4011001008030312300c00c07100907028500720a04400c003407041520440141d00255900d50402d00c214182901c014031140c4140740412170b030000100c04103400b07052042c05803814105008070000244a10420442c890741003100d840c00000d4401c83c90b00080e101040c1900c0821650b604c0d6581201c00d4140e4000710300114880c11001c01100e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 24148225 1250 24146975 24146981
    0x41505070e1903140105060102010b0a0f030b190c080604051303050403080a0207170703050c0919050402010e040e06010306060b04060c110303040306020a080603010f050105030a0311010b030102121909080409 91
    0x1034010002542d00240c50381c1e206012020107840b01500380c2c1d0355030204211541c09114000840d042200c42c460194501f00500c01c12420038080180403e0200700440c042c41144890740d0140d0005040601c020159100024100c0c403085450038850350801001c100a003c074040c122210507050794410749450700b182c54580180c0e20003a044000c500c03038007100241107a0280d400600c8800c009020b0642c2d545142041850609070054031841403041c0d40c01d02844001000507404030003080c4002141c195124001600e0a05020440c660800e0a1402031800d0480119005042c1d034816081040866122055003503e401640100b03808151013910b0180811800700810401c003000a08a924068590f034646081c3d03000403c5e9000890360f1a806e1044618080c01404008503014004105e158509030001e5034400c0072400140500c108042008101c1c8001e402021455001800079076403030243c01c00341c652400d811182003120759108401a080a805806140c625036002a100c606083c1080703844002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 24149475 1250 24148225 24148249
    0x5100503060d060c0c030206070f05040611010e060106090302121b01050d06030c0306060819051c050d02031015050a020607030509030c0d0201060602010605030a02090115050d060806041505070e 85
    0xc030000b60354050000480384c1c010000000b03142d54074690340369298a0b0183c0b4000001c1c0c0a0710038850880741000545900c103040e5030072503009140a200d184940482c19005240042548145001f0701c0c002069090700450168112482500c000b03410b00004100b140e164440c0040c800080000c4a54058a562081000c0c11010102c070200184490740e03a0364200c01100290710403140c1640703a207000c10466800b40203241080000c405900405030b46580c0c0d09072141340350840610745c03038052041807241e20b2023601658400000103c003199a8100183d0000d5002c11511030500e001480b1032106164074808d10940d0081d00701600284035039100c40800f6405004020500c5d00c50340b10501c15050000c800b0002002341040c190000500340d4200364009080d11100c0c1c105a00903031041010034010303181c80280c03504588c98090040d83c078014181d4115140e200b20145075038110300346031010400c0c01d800300d41c150140344a0310070003c0345442508200c040e50000c4982d000800d462890002031403e064130541c00e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 24150725 1250 24149475 24149479
    0x50c040617101202150d150603050601020c09100503060109090c0503030703120207210806010e0a030302030d0b0604120c060806010e06034005060702060f1303090506070b0417040510050306 83
    0x400000710300d401c0e8100e1380110103206c0c50142c85401d54641da0240b004132001801151400740a02e24101002030364828450444a0207a01540c0015640c8080d0785255006420010180c65540d650b40c1c142c94081c112801c0151485000c03070b04c0c00583c0e031500204441107030340d041e226420183c050700f03800c600940041c40180c07000100f001e5101e07540d450307040032404100c5203500c1c1d8131002c0c2081c000050880c036200240da07000b40703a100410301c0400c1d00041560000c0700c83c00b401256209105c40418800d00440d4400600143c00c40b50301c1c4100082042c101003642e50b199280351240da200001100c0c1d40400180c0241c00060810101d00b0603500c00c0c01c0e11011040020300c031880d28039945120300c2115126242104030191000034074041080503c4072a81088240c4020442401d0203a0b0001c5020405040e0031b00c0d41032540485800c060244420500800e4014070302c580b04e001d18106160644000c0300c08841481c040007600b9070555009003600c040c2c2d070000c0c20f86e2124a101190940d415030000d03040702d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 24151975 1250 24150725 24150739
    0x60f070906050d020904022b1e02090307080607081e0106090303030f1103100602010b030d0e100207090f020a020f012007020d0f030507020306070c0b070503130501050c040617101202 80
    0x45d0300b03443d0b50004104003c0b40c40d10028184001d0078002c0e000130840c500e03403d1084c0c24840c01e110910000042c02d000109003034001a900c400d00c00c0002e260041585c002c04c128008cde5410410510b400c501141c0c1708614a000d010605500a580c030014914240140da01062150a040c80030a129611207034071034802c0440000d40c1c0f48140511582d6803c01c440c107010400704101c05000940d42030080c0408440281c0040004910100300030740000401d030003045c020300400f2910888a0310800668004204030041000480703203c0401c04082e5000911000240c400c4c0030341007100c45014403613001c250022400d01091014118201e01c0c46a00641d0140ea009600e40854030106084d1600f000c5524401c0d141c1e55944c82c42031040c94101540109080c043c003403c0344200000c104035a8209030300180794501242e80b5620100f4000e03800d402076402501e6036181804004000048400a20554045840325030f100c0c0540b121407000c21000b1200603003c1a06082c0070000070140907220301d080d81c0300401003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 24153225 1250 24151975 24151987
    0xe040b0a1e090804050a050d0209010506070c180c030501080c09010303030b030328030b0d0b01050103050414190209010b0408030f0c010e030309010203070816020d080702011d0708060f070906050d02 87
    0x19035444003800d83d03a80030001010090380c039003200c41c1c0005000c00c1d140e01c0c420362016000034038440014465140501c00000b110005c0040030b0202101400d48034410781d60103144140550010b003020002b94001c24a403400200d03221400013040300300c8010003410000c40b84c3c00c0d590120081c20140c1c0b003254040c801070003c0300b400210050140002c03a0181d19840761014808402000d640c4106402405400000c1043e800b0403c1141603606541c801e08010605844526040a050b40c42c1c404119083c0240007070f951003682103004a4940a00889040c0c0300d99807224509035961246220704002d0360710402621031403007a0398001d407003c40c1c0d80380c000046032030300301c0c40507400d5600440d510001658000308100e4010b03009200241c02041540380e1590004180c01c010f9942d020420032034080c4840d040000f6400c40c400d4000080c000102c3e60349625140d080d0a0456503075120340900c8080303000c1e5100040e065040030213034038407580d86941c0b00010186460302c02c0d51154458030305408610740070071038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 24154475 1250 24153225 24153281
    0xf030f02070518100909020a030b070c080403050a060501090b0102073c09061202010512040606090c111005070206040b0403020a061811030a0201200106050907080405070e040b0a 78
    0xc040c145890030b5011443d1881c00540b540521030301904070284051800040c84050f85403551140c05580e8815010351042d11035400a45505030b1051000705070b4103002401104000c0b01007071088905200c2d40c418001d41c0d03200e4800d01d044c0c81c524004075006a1010100300302003002c0300240e80c0181705000003e082c07180d44402010051640074105e000040e1900d02c00c0140303113400d100d44001030000c2d4856054070103032940001d080c0c1c0b02d100c81e086400041200820103001f000c2e032042004020719541000640360201000c0c1880a07440301c18440781c041d07203150340303084a2240186442042c0d075501818603550b41742d543d04d03070b040c6010f0010703002c501c0b500340407070b0026070030307200d90800318410540007201580540340285000305e8090000c0d001b030300440148070050760429181c0d40204000a80701e284900e4802407940102a00d500070713a80058201c00344010242c00c130003010300540c0034800307403491140c0381c1d152441001d0080d0ba00500900f4104006100200154071a203140c40120109038880948401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 24155725 1250 24154475 24154489
    0x5090301021201051203040302060307110309030f01061401081506030405190c14030f0d05030a0f050a020d0b0a0b0406050901050403050f06060909010605030703020d020301020717120604090f030f020705 89
    0x581011070710b03556401070141e45000080ba036000039805006500e002e0a50b800314445000241800051041d020303481c036105d070010b03c2595054000601202d01c5440e844640314060f100e1441228055584060541d0055125503d0144030700c51481c0c000e0f003400d80e59020b0004a6100400660700341c001e841120b564034180f042c6100c0f01c81d0148181c804514244190452500e624503600c610a07030004c01400310640010510f400340d0107050400350b407139540320114032001e031001b00b158402d0300e8035110402c45800e42a13405072a81c1740c0c45040802c4102c07501401d100c403078603150083c0781889100f4481004a241700c0c00041c400140c0600d8250b0078695a0741c0c503140713030109040609059802c1541084201d04002190a902a41560003400f805141c01c01007910b03440ba80c000a4002c40d08444d280c010f40d203094044030400d5a100f19400c0c400310460740e902441e500301e03200b0100c0c3e01c400c00000c030f4607600c0c0501400c081642c010071001c18043c800d40d801d42c1c811440801113005c4d802818400100c079035070740d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 24156975 1250 24155725 24155737
    0x303021e011104080a03020615010804020409051009061407020307020d120309080a020c0415120f080c0303010e010f120b0a09020a050603070e03070f030f02010807020f010203040609020405101a09010509030102 92
    0x4009120142a5142c00390504c00001d210989801d8240049112078bc0e010f0706490b041b98055030000340e02e40090400f1418100382035040f103002c81c02c1603075500400c8499440506141040b0b10205000d4440c150300f02c0e201e02c00c00da40a50302c00c40440340000496060110184014640d00300040da0000c0d030754a43d086900180c580b8005a0064110b10045003004c0c0101c010750f82100360345038056410101440740004074000080d001801941d038403001c1002d00740454003001603680440b5203071742e904e01c40f04c4c10620090042c14a02980700383d00048401c0c0300307182c0418459200e0078107042603480c1c030b072808014800b220701641e02412501001440e030b100c03100218000c2581e951035051260000701451714000590303200a01002c4030000c2000070518004804141d143c0c2485e00c00c2440d00c030300e08101d28060272446c041c0f0380c0354800004d0100304450380d8400f00e80070348262010301075981c649144480001e4503100e0048030180d403142411409035040010001c180301410201c2c103003000d420103c0d0881c4c00c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 24158225 1250 24156975 24156989
    0xd0305040605060405010510030218090f010510030c020303070c020d020901030602031f1208090d060e060103060e010e06011511070b03060901080a030e0f010c020d050d0801050a0303021e011104 85
    0x604144014030241d409900c1d480b00c01034500b40481d501d81030200d000c1d14040480c1d80c04250b4081401a010390404030026500c0c140200000310901340201c52211000b000c0c803c1c148604484801180c0e500d0003806403414401d0b00b900510b00315691000c040e614a0702d0144104d91100d100703000c2ca00180d5070b124010f8041d41c015030300162030745414419070b110403000782d2030000100041c1208000315018908082a80c6074015400340c1c5440002001c10324030182400700174606030900a841c503540b0b8000426604a074015017090011004c81c584907401c07210b04042c52201900700a00501c01d07142503002006c0c5642003403074948801d0754800840ca0074081203402c2040542400020301005203003101c1c200703014005801c0646a4140341c1d40e005042109039627011030081540302001d40a0341e004501402d02590050107082032500646889038440081101c12000300f82d6803400424607050072401d04040d66810780080c040000c000030704094481c82140902c0c0d15649940710110400b009002400081c481 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 24159475 1250 24158225 24158231
    0x90105010f17120a030b03070305010b03010b0603270f010e0a020a05060c0303010e101205030c0607020d020312090304120309140301140103080c07080303100501090e07050a0807050c0d03 82
    0x101540c12407141150360000d0950282ca2a00c1c8045500108845019580401a081d65139a20310810313000ba04a000c40f00d035050151280000034048190401804160100c0081203c0b0b00c0501c00c0200702d000903504191075040400f840341c2d0883d0048002c5080600301421104010128410503094a55002450b42590000301c1139608508110030710300c0c09000b04960180c20210401c503e140d5034001403082482c00341c0b050f40441e441c00c075649401000b4202074400380310b01e0702290400030350326070007418422114030900b000220700034804603000a03500010390186240c00368804002d000004003070508446800708010014035a1038036219401040d12036120b0160303c0d864104119008141c004031240641d0400e64034411140c190001141542d9001903100c0e12800c880d5405071500748640c0002c02184400000d2141664941d000306040343c509a9860301865190130b1020060341c801d55202c008102c0c02d2025038401806561401c5d404103007464032a0030074030720700003e03841c040384680b02c1004655 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 24160725 1250 24159475 24159479
    0x22030c060f09030905030a11150403021008010315050c09010e0f03060f0709080606060324090109020d06050307080a0b090a1506031a061003020a03060f0e0106030b01020f03180f060309010501 84
    0x13030007001d050002c040490251095404a0b119503c0000440000c180319080317141c07007182c64640e00e4040e20081e5401074110110b0403143c6c01c02801d10502800181d0b01d008103102005440c142c0d6001d810310070055900c0160a0a89003001510a848284062075003c0b2200d518030700396031820804203219400d8040e03113454900300f4120280039261640c10450103070f00044100042515000220ba402c05019070b595201e00302d00c81c1070303d48900e0354400e40030360000990000160340701c00354014100440f0b100504000307a564440405680c1c140512036051503070048462040428031041c4a180e1004401083c0c490300078160b641c4031404160b0080200301140e903440309005104c01175580c040414014080c0d8552800d005000400803045045040c0c1015000078000070918440d4128070011700c0e0003000c0c0140b240d107e0406858401e024005c640001b8903200440310550b10004041c0202a0900c0c041d41c070348070407a00c048400c2d42e100340d5003d4110081c8040d80e130554032180c00551080003100000140340d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 24161975 1250 24160725 24160727
    0x408010929040b010302010507060f0f06051507020108060402030a060f030501052a03190b030d051b0309010c0602030a11030901020304050708070803040e130204020f0403050d03020322030c060f0903 87
    0x4078900d0030124040603014100400504001c2c406410340c1d030242030064854885107882c1c00036001480314145010304110211030481e00b0b50304010107860341241c540d0503001109000780100d00562001a000403c05000305406041c154000c54100300b00c1c0304041011501c81e2140c40c200c085036881110982e5482d0b0411074216803440329100641c0c1d42640140e09070492120401c01404080c3c803294042e014250300307848070301b00c1c1c0d03004000186015003510499101070390040d046420401c0442c02c900482c070b02e04850f0309404011a101c044050b120844043c50645862009400090001d100c03180d68000950341d0442c41c2c2d003e184215440d200241e0341e441d041c03030201d00381500da50042c6000e610668091100400100c140c5065520211425220307a68040110b0000c658501d030103500300780b00040e1803010340e0b1440010400d0741c1c0100100e42c01d201400d2800c80c2244030403215090420400700401c01c00c603c901004010160003842c020024003280e03101c2c3c8086840c01e28441c0301e85a85e6000110400d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 24163225 1250 24161975 24162023
    0x60c03120501050a03020103050a0b040c0e190501020a120302121306180b0a0209011808030406020d0207140d08090a0b031803090d060504020a0905010b040e0610090504020f04080109 80
    0x65002400c041c40554541008225070140502009041c181c4502c000f448080059008404a4000920600000b00012005040480b0410030030380114150403072a000c40000c11121422150107a00808017842141ca809400310301004000c01010380800405030f803008945255805510046448051861140b62801c100c1d010000c4460500c1c500d03400c0440411000c5c0c80d101c0e03019041140240c0d07500c030b04800407216203030381d5060301d2601c40501c1808118000004060010741c0d0064084882c82d101c2c0700800d84e5515a640f084401c1c442406d0544016410030741036118120384104045403c10f107852000501428854200b150709010110070089134807291100800d01d1428040610f00d443c01041c00324681c10100c40c030141410b901d13034010408545400d800c4400070b024540080007036584903c8600002c0e0300503c540040c0c0032444000c6080c5191051205004c0f4030b5503281c017070035945000300307001c081d4100c0703003803040c0c1e2180c10300c00002c54007820300841142d00d1140c1498250582c041c0103c05103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 24164475 1250 24163225 24163247
    0x40501090602061302090907050a0b070201080601110a062d0903030f140105150705060a02040504050c0306181005060c010605040f0e0d05030c07121701081c11030c0106060c03 77
    0x456001c002031000d084065013940c404245c05a62100d40c1b07070740e9064454608501075100036040007000c0c900003034141510300545080c920036612a1625201c02004440c0c501602c2c0001589401110041c00011001d40c40169000c0007003a601c4400c20000000c3c0b6858002e0700340c41850f05846580c0e400401d0786c18450588410642c00c01000441c03005c2d01c1c152504101400f03458015604141404803451104c4140d8203420350100c2214002e1500e240e900b800383d00103108040c003031814440407030100c844907401d981c40b91002510f60003000c046031540203004000502591403280d00d03001c0118294075800003c1c0071003c59803001141242ca40000e200485040c64402c800203071070710110783e02a0102083c103081351400e52420b15101c0d150a0050f82e041d00c1030350401032030108041b0a09a2140e003000c0140450011805a020301e07a80e207104035511134900c420100141c2840b0304002d02a14098983c20300c1404840046901b8191000c08a50865a040d0090700114080524007001c1590000322404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 24165725 1250 24164475 24164477
    0x303110d02011505060d020d02040314060109090803061003090b0703090b0f01061704080405061b06090109020f010c110d050c0907090b0301140607060501090605100504050a050d031103040b0405010906 88
    0x10003c040c0c0000c4800d406424010b25100c1c1c3d40004042200d486250182c0c5c11074a0340d250115510390341c03450401c50714610030442c801c46005d507500004a82029129401d60240c01024003851070359070004000c40e10794844078001c18180e031010b03c4404560202d4180d442070711a40c4000030f07030740d165041094101d00028400861150220014048243d05c000d0f83d602c2e40c2c910800045640c0c6451802c11030702e0150b604410381008010031000103600f00c55244014100940055400940b03481178840c1c00e80b2020007000c0d401a2a400301c0310030307551042c4030300e012290040400340c0b45c00d181c010001c1c90101d80d1102c1a10b543c0d00c0110301118519011148540114060400c02c40b014600b005407000350105200c0c5608040c503000214040e921642e0459903841c0c5c3c4180d00704050368645080703078020080c038007505000307140c55245c01c0301890203001100c05540bc010030319860240342c5000c00a59030144001141044501c440190359180104007800250208043d4a501e650070100010a90565540010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 24166975 1250 24165725 24165731
    0x1e0709050417030c0c0d05040302090c031015051605010209030606060313030806060d020a0305090c0a050d140c03030d0509060c0f090427060501030611030402010504060302090a0509010303110d0201 87
    0x4000294501035508090071160100c0761640c0c1c0300540000d540c01406950305c0c881c0540c04505907070b158024014000c0c1d0740700b26040d10b21922105618000c50008a40c000000c001001080c880d41040200e07a00c140c094504d8958585200c294800208400140c0200e0f1543c2d000709031543d0310f1509100880d48000143c680508600c2e000b2802c0341c48001100015040c0000796011480c252628000c881e40c804c000740c070540da2090903010042c01407904566000d294001c00381500514a071104c03254040f52002001c0c0400e450700380c0c032040c000c40c0e00742802003410b125204110110f910248054035500e5010040007409240810301541000d40041400800d8941005405031700b6003890255010300300c0956000800e41c0300014985c1e006540c640c51112a50f009014071420456140c111340d050328070500007844280c9015440b40041d01095030004c1c0842d8091106001c07180c8264040d05240740c006295810995480020410f10030f03003030300141c00180c500150444a40000c000c00840c1c2c00e890300c020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 24168225 1250 24166975 24166981
    0x1508090c031f0c03060f03080a080708011a030a06050a080a0b060603040f230106092406050a08040314070602450a08010e010603050d0306060207060804050109051e070905 75
    0x40340b4514284942007105580c0c03450840f2070a4440d90124024041007014502e0350390b22410200c07555000f200580c0009042500010030349803158035403e04031144070045881d004200940e81002c1e420041102d44403c0d40e46400041c1c036561215258005d01d441c0000e40075a245c0381c10004440d079401007009000d8201042807000144490782d00f00c20f0030f508103c50002c0e5164180300f11303c211b29410554481036013485004585200742e0791100c940d4240c50466140d000d072480c4601039a014840c07180c000881c0303060202c91b80c468010045190b01c14480d00d0310940c142c001d070354050015085990265855039010039110412000c480c000b102a29030325200c203405694034801010015078005440c50000f0842c2d180c0c9915846505401e8060710803070303000703000c41960460303024020051440142c0b524460851940030082c02841a10107841c2154040c00400d810b103507040d1400d80c40904201c40d03a660b01c801100200703a0a010300d60303c00ca503080d090346582d080124124a0100c85802c40880c1074944001c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 24169475 1250 24168225 24168253
    0x111011041a0a08010902250501020a09050d0209070f050c0a03020a0309060e0d11030109020301050405160f030b0a0c0c02060d061703090303030f1302090412030606110303040215041508090c03 84
    0x4481e044417a01c400140c0c2d120740c43d40c10300406005240144070a1110b0390226000c111041d000b0381001e615540d50180c030241e98030200300003c03602e400d010703411654600108000c944a071440c401c980145080162801e0f8503480d40c0c0346001c18001c420341c011703041174862600705640403602c500182090314100040c10740700c000040c0160300503074005104041c044405081502c0c02c4d082254030540040c000c109510b05424107680f20b900c4000e01550310f0b404901d02050041c0d60703400020650390401d00c80c1d03034940c0d0381c1450342e030003028043c1c0c003002400151441c80e001a078862000348031079118a80d0124025140100c40c0070219201e000810158200380041c250503180042175035403004011001e81d40d542c9520f5440b251502d00d050019402608680800c0300784002540c20302c034503002c196010000940d49140854000c42e004900b005207400070008100546170041302a91038421702861145490707030351400700741c4040070000d003240440ca14004214024009000c600c84043c410b0f000303005503114400f1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 24170725 1250 24169475 24169487
    0x4120306050a180f11041404050702011e0b0d06050c0903010c11101a090702151f050f01021203130c05030105070903080706020706020f0306120106060203030601111011041a0a 77
    0x4001c80030156600145020021036030030884003540d003a403080e13031ba564403290202e50180346030031202e020b2414040414041031051042c651041540540e480042c504078001002810f0340302c0d20154860343c040b0140b00424201e10902e030240390700c019600d980342d0505003130500b500c07200c8001005008024011800d00a00400c5800180d801004006003081181c030100850070440700b605500300c210002081003054000030b51000224002180c2505642d4a4074040c0d001481c040f02c14107800c04103c1d08002a003480868164602414019202d0441440f114240203800844103140c0e1186409520414070100aa0040160809070024099460042c1016001c0d20642c80010a00d000004a40050087c070703605844401d0b500500c25940d031134075450340704507640058560a11034614047c0040c501d44051017080111038107034010b9400c61313541000640c0d194182240c1e01c8428001d01c1d034070b64109000c038032030b02000e130f44603101440e203503810010b40b180800c905500c10051242c040100b50032481e0440 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 24171975 1250 24170725 24170759
    0x1f02090f1819090501020705010902150301080312191505100305040b061507050304030503070309080c0108040204020a050409061e06110601140a030501090c1404020702061605120304120306050a 85
    0x69a078100408441803042c010003448002502c65480407410031304100e81034003c406100d008403081081c04481540d1058144420b01c18090306a0040102244100c440021513074071000c4d0703016551400c40401e00d1003054961041200940140b00c200030b003d20300d054042d050248105190802c110f15141d40e9005045d039026281034415a046186400500340000444400070744c0817054986550392890310aa6903040210101c01103a11440d0128080b18005200c41c501070050751010b0305a02c69400b03200003507200021000820500700800b0450307810b0750041c8401803e9140700d41e45650705864142c1088042504031100f0400f80e0052004038100026040781135400e007441d8162101108000560307080e40c9035000800d15400c0a4400081c8281d1164000466801d00100300f0340004403410071080340f04003003000b58003403001c0c40300084249060720940709952107801200c031621418225050543c0040780d08071a8444603602124031103a05000702c0c0c0040c04141c0b4031100072030501d0b1002c140b4111039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 24173225 1250 24171975 24171991
    0x914010e04020303070c0807080606040b0607020112020d020a05070b0a020403050d080901141f050306060105040603020d06081f060e01120303091b06030204080f0a170c1f02090f18 79
    0x2420101d0103540d02801142d00d1160311002d201c8029548404290f1507201c503100b5803080340200301c0041c0b01401d00d8000c81038103890027091180703040d441c0c0c0d00640f0002580c1655000c050b40c02d001104a462407840104030386031203516042d4544105291034001200c0c000c02c1014a540144002c10000e00009030508151820382040c600c540e941c40e900c00c0c014090702000c18070408000081c06845048001d09424407a240d180e9002c08544540c28103a8402013526507900080e410407040040ca07100e580945048820741e1800310f10390355104005071510300c0ca41948a4a07400751807803038a50300034a00c9110010109500800001c0d0714002c503035941c00398101401b80a041e00e0702080c2040011560350100300b805445000a0060b03186c240040007900117004900d640d00c038141d5140110340001401e11425a4030104071444910001c2003410160006680720301c5511551340c2d031100410f8409031a00f40719103983c030700580340c8583c40200716140307107001121401010f40841d164685003e100701c041e4801c2032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 24174475 1250 24173225 24173249
    0x306011203050705100c0e030706080703020a020a02091612090c03060911090f09011a1f050f0f09100806010e060c0a02030f0601062c1c0f0b06030601091401 69
    0x40e03040c156800d11680030020301c0f0340620044802d1948995209016a01490750380302c109210800a041e50750381140075480c04903e8050001e1921403094000f0003101c030140c416108503130110382c0400d420502c140d03642c200c0b03804c80310407220600da0301c020f0101e0480281c49040c800c4106540360b100c40011540030103000d03651641c0e00b44040c085040c03c402c10762034000d04128420f00e00340c00d980910030b030280c401460b0342d402c204103034000350303012076a001240b80020200e0b80700b0b031111407030948142100d059101c01e003c0180110a15450400041c0a203055074002031a1b8400c0114204610342511610f02c40511411030706000159034000404600b07047d0a172110341e9960001c00300685400e4103018001e5052140c0c0d0003215401c00d011036094101c0d031807903c0e008000045440c1400c00a4010b100c0c04500b68031070882a4101d141085604486001c445044290581c05445200b078031078404c3c1003035600c042140c051021a050411125006040440701007102c0004c1c0c10210700d8210040c8207481a03804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 24175725 1250 24174475 24174509
    0x30305040e0a060e0a050702010c02030703020c0f0103110a0201020c0d091d0405100207080d0c11030a031505121b0a12060b060c010c0f02010506010c0b1801060504150e15030601 78
    0x50b440d0301c070358050010710900fa43e81c1c0c03500034404805440c0882d04a1b00550a00c40344002003400041590032081d4507401500722100403406012a03d844212030b181016240d00003150844a240c00420311010705070700250751014594611407134a0340c0e003240001046031240e030400c41400c07041c20880b003052580242c00503585503418213603c0c0c040b8000080040d28800100f00707041060205c000c101056101d81c050025645601702a0785c050f05403050107516400070071001040300d10990052a2210103a000d03040400d440d240810705001508080c5441540000380d140103007514030404003091401120740c00e0707140f400e2420003860342c0400000201000d40307034000482c050340c8a41c140c0d4020055500200502107003200c0081c9003440f0100d031000503528150100311194442d061042d9813a0704105850616102c44004807110407008200381c649550b1000d020429540781d0050100500400300143c50480c00e11102280070080a400002075841d6101c440401e41c5001c50550704450790041850380d849 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 24176975 1250 24175725 24175741
    0x411040b0a08010c0e01030f02160210020f0601180e060601020c0d0501060e07170a0209030c010f020a3801150302030709120602120106110606150c060408030105030610030305040e 79
    0x810700e500400c80c5542085580c038007040d4081d01700c00202500740c0e001d10100c2c401a202c54101c0c4140808114008503451220001d802d0039109400131801c60702c110303a2074403e0b407030038030341029001c1e041200100c02c51a59400c0c01c01e074a00551500000c1e00b0090b00d8907080010010b90f035528901100c0d401070140b20b17184001e12000303511100003404a00c5042078246040c160080240c0d01d2200048076081450020468098082c4283c48400f40c0c0680140b80e61040500103554051140c01160210320464080400282407031030bd0f03c40390021a00d0290f01707480d1a0070160303050701040e81c2400f00028010010884017a000711101d0440301a4200141d494841e40c80440d81d18445400c6641400d00d036841500402003641c1c002e04403994919200b04030303642c942c1c41c211000d152000c6c0d030380c00e02d510480c0403a0716441c0044c6c01350026520102c01902e00341c07100700407a00f0141d040350140e0b44100080f0040056040038401c083d4000a144205d14420b07043d903802030001d000354080c2c4c08140d01400e0000b8448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 24178225 1250 24176975 24176989
    0xd0b06060d0e0c03190c090b0a090c020c09070e0105040b070c0e09070f06081509150301091407060e01050d0b010201060f0801020c070b091003050604090c030c08150411040b 76
    0x141c00190002d00c25540c040c800c6a541d80755000900307010788640303800e480f030000000182c408841d901c00c0300c41801c0d5184c4403941d0058220001060b900450413140001c80f0000b030b204196070081c0e03135000f40141a071920100490018010200c005006d0748144149290307034880200c906a0300000c810136211a0700e810100d00344280780e00030440086642e004c1c0850340e000011814211480c1c1c072064154103441303100440e40208240e4121003141c40d0343c00f40101d940790401c40d0303551029071449810207290807400001d0030b4900700702042d161165154074008510006024983c0070340840d0800394551251b02c0b000034914030070b181c844811550364140d105041c3c0e200b900150000e100c8640c0d44100243c681542900035400b4651036051449005000030780c02150009482d2503140044c91030754100e10050054014146c01044594000e035035003905000600c850b00041c0145002d031511101060801c40b2161a1040940c0c000419441e01c02c10440000e00f408000301000009950100e145013112000c01c400c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 24179475 1250 24178225 24178237
    0x1a010c0f050304030b040813150c02010c111309020f0a0e0c1e07060218090606040501030c0203160c03020109060302030c03040609111201020a0311090d03050901050408010204090c0f020105060d0b0606 88
    0x320151a01b032005210041c4c02130482c0c11030880980341101e90b1166002545180c54140c100860101904080503600031134001d01c0b1503014002045460400301c3c0040c681400421803504995a81c1d0740410035420050f9403518002c4042d610383c010349080424001d50164014180001da42c070006448040081040100342000003100000b0f85600c150f282040280d0420a881040034403042414122854a080414081c0101034103d40c074103402d250046024200b4032002500391311040160385651410303010700312001d03030084014811b00f60551000418001041c1d0000c0d08040c014000d1100c0785404000f226007041c1e00100001e014402494451503146510381b080307900012450406801c10019001001c8541c0c40f1f039001c0041007250015054a40141c0d00380c0c64222840140707400000c0e00071801000b044405052407418590f55000c1c181c2a40e0281c0c2191088644810070132001c240c1004100120f102c1c240000d002e1845c00030080740003400c04000c0600140402008a880e032340b1a941183d00b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 24180725 1250 24179475 24179483
    0xc09060d02091306020a0203030f06030604030909050c0408070305030a09060203030411091003060f050402040e0706020307080306031c02070302100306080a02090a020d020406030902100306060f05030615040305010902041a010c0f05030403 104
    0x52181c4a00b036006c0c8d01c6c0c0c2c0040324482002100e520005410340303000b00c0c050303101c1d0798540c5403980000d040c107032114001c0400510700e00e5400d60400c00407403100c004000080045100300001e5558a0b403101000301aa0461ba005009641c400d00c04d07c00000c1c28803030114840c2d0b03825030b207021881d40d8050320541840100e500240040f4645000f9034035012050300704611580c02a1000d0000f10501d50100b641d608952040c0c50050301b0601c0784400045c0072100464003c41c0080440750458200511016116a42801100940e002c40300030402c50420b090060340c185028141013103030354170b04282d954035241e9043d4001d1060070b801000a210b10000c0d8183c4084640180c401c544844e207030300028005080d0400140c0c400c1d400d0006070f080b40c038400d00800080d154107548031840344090740c00690341070300007410295000c00c803180094000403c01d00139000a41c040d000200f410903190040c07204543c8048401000310590510944550740c015091619040c3d010701000c2c41e10619082c0141075000c0e46d00028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 24181975 1250 24180725 24180727
    0xc02030106050411130510020d120b1206013201050c10050903040603060b190804030903020d0b06100c020906101101060303030507080708010f030b06300c09060d0209130602 76
    0x4c0110310520001e0841307212082100301240d6252010460180d001d0004078006901130082c1a015510403074141004040690f00401d0b02e8034000001064a64100181100c81d4801c00c01001001380450350007040c00300b043e4180c20b014581070103190b400001e0308100b1b410302c5400104116446820450b04e4620321010100b00064106a040c0c02d0700d0390f00c1840b4110000e030070081e02042c0d103883c600440e112038900c03981400ba00f5605d45415115200020001c0e014000500700020140c0c440303444124425205107500041841c0500030421108001d4a0748400c00201d038009000689642001c55040350f81103031100c010703052140d4219910841030140c1e840550a000c400020103805030070003030040030b0a45a21000e82d544d020300300d441c064244030b0300501c010716203001c2020903000031a00741c0041010b010100e400c16800301000d0030314450301007403420301d00400b00300d246104240900c403901c500441c0c1001c09800c1400010b011240c1c8100c020341b02d0441c643c0410700e0349001854070141544d21503030075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 24183225 1250 24181975 24181991
    0xe030a081309060506030109050907030501050a05100b070506040803061203041706071107050f040e0a050d020f0304031104020d060e10050117011503110c0f033004030c020301060504 80
    0x11000a0304080021480040c507014081544010390107003100b611000340009046d6031800310050080c00021f04007600340d0040340f0000c40450828081c46100b00c04051001c59503061000300d00d11820559401041401e8007400072000080c00400c120350003a800a4419071252924000150701c1c4940c1c013010451803200182c000b902c0329911001c2064440d4403010303100596920319041e42c48011912f4441000d80003424144090b217410308411400b000c0291002401c80c020100f080c2c036229001c0c000b520306a1259a0203069182d040002403544280c0c1c0c00614141480c55640070b0451301c15450643c4a03980100388000b00c55401e40c0082d0082c1103000170303c0c07140d040c00d09001c689a18140900c0e40050240303504088550000500b160403a20950b241001e04500284114020002e540401313101c14000c106507048402d0400600c24120b80c000040e40c3c2d6401c0ca8041100c41c0c10f424103030303803441d0650440352030300b00c90300c020000380d2107501421300309503191072440001d00520301900030307640c407034502112 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 24184475 1250 24183225 24183233
    0x507030c05160315050906010305070b030405031e09040f18060504020f060403030f0305010b04230d0209070908060a1a240a030902012d0e031e0109031b0b0c07030e030a 74
    0x1c3e9260030b140059017001991200108152244001d01018140340d100c3c2108115240b030400041d6441405801901d0400b0010b5401c0c11549101942000d140c3d80c1c040b031041803900d0540b24001c00400c041c101000491768031070318120003080c140b4024002940d100c0c0040d0640d2105c9d81e100c0031442c002800035030360320b031245405001a41175041e10b0000902e4500042a41d80302c54088501f910715800c0b848100320800002c000590307240c070b40e0580c2c0001291400c01c0060f1074070f150640c06a4110784bd002c41980c00c01c0b82091810720000d002d04900c1e42040c0040302c1007810350108000003042a240c011081c200c00c02030010401c0540468100a4400200c2e000c22aa040d40406401c0e4402d90300c07014142040c20010880c080170300404c208104503450f612000c507010741880005000090140e80f400350000f100e00000c031002400056059440708013010406901c20322011900d030300b00001c0340344416691182c1c403058100900048400e00005054010b050290100f000c0d11740b002000c58403e0849454 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 24185725 1250 24184475 24184493
    0x905030613031404030305030a020a03020c121905120105012015060a0501020303042003010b0603010306090b010b030c032d090a05061503100902010c02031204030b0c03070507030c051603 82
    0x10180d001600001c459480f468203441160200c4c0d0301a0b6455046485110111000b94403804624003450390800049004000500c5520300003281d01c4507003903c8842e00b407502504211f4145a41d41041010450002d6200142081d107054910030319000380d503a494004c0e0010b03002014014000359100b155109644105045e100512a190549000c601241d9074001641d69020175100140180020a0303089501ca44007545d0114507000140003081d43c1c0d0342000410081d900c2a0170982d00e498450325800d080c014900d4695004180c0303a9500b614500d00400008181e00000c1c01d0326120741c8081c00e0050341e100e6103540406440d503804590403038500380000b5903552603103000b0088580d030107041d001a14140301d03460900640c0310060041c0607550194041040108180c48003241808010b102e007501684080005000e142c04050307540350707074905508201c107800600415201030240100300b002075143c0d00c10241c0c1c0c1e9807981400c140c4101d2119190603418100303104d1000390300010891b000803c0c003640301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 24186975 1250 24185725 24185761
    0x27050c01091508040201140409020a05040f1203020304120c0506040602010c0212041a0313170304050708010605060d150503010e10231906050402040605040303020c010201090201080a09020109050306 87
    0x41c90785503115035200907011010500c4907841d004940c180c0002805540224501d48081c011500070340c0c6416107581c00401240c2140d00b8100000d030b0082000d001650610f1210806080e9004495420140310743c1d009540b80304a002c0e0380320341c070385444011041001504203500906801415513464035180e42009000b80b02d0212400300510a50610b0000706944400725005d0b00e0500069514103243d0b600c801415a0002d04410501507d40350444080b070802512a1503e00030b00800302d03921f040604000345041c0080e002441141d2510900b0001a0360b100103c400ba1600254042114060702858200c054031641c040c54255007841c40c0e4103ca18030124928509a1074003a0402c2030768201c81d600200603020120303d0410b204464045050381804040d0700030704500454000c01c0c85078484000c01e0aa8216500080100d800031a05004042d018051140b0200080c4000c00440d842c0e50002442204064203540300b281e035680040e0203592081035444090400a4200e5000d803c1c011040c1107104810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 24188225 1250 24186975 24186977
    0x90209100309020303090609060906030717070203040e07080a090506010905060414060a05040e0709092603070c0206090f0307030b09010b010903050a08130e07110d0207120627050c01 80
    0x10305000c000d54020720549141c02d4004c0c004505041614003031100d01e51001300764070ba0180c414041140303590340c2d85005601c00c0c8040d950380c1004a01004602c1c0c0c4441d400f072302083c1550424030040c0030503943e0442565011701daa00c0c000071540c503003d02c520000c01d0200c1002c0e001d8043c0da00040754480d1a178100b940522030030781e01009080c008490229100e08195003250f4400d6030080e01308914a081e4200000307820b0400d05984865641c0c1c408203049428112044504400702c1c00300751a504503a0401c00019404505458518989080001c000b07010400c03000b0b1260b6070109501003517803142a00d079054014003500b200c2a417900c80c1004020201e003181d10319519030904e00780f030305c05502c1100000c0032030341d10200911040703442c1e0760b6089050300500c581c0a1000200840061000c07841c540c054050101501d442e0054005c40760510b0800c0c10405100e4290b503c6042c08111400301440042039154102c4000103c55900d030a410000403982040c0e0704408190030080b40031b02c480480c00030986030003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 24189475 1250 24188225 24188239
    0xb070809031206042408010504120e01200f030d0e07051c0b04080706090f020102060f010b040504090503090604032405130803042a03110d050303010611011104090209 73
    0x15404115900c1c410040342c003400d100c402d0b0114110703080581000600e007003810390240f0603d2107006451803139502c03648440d000380e440c2c0c8103000610215400580011240e85071a80c40e800c1842d0000e002608031003c0221502100811740310b01d22400d225108802c034001043d2075640900d006030078050030540b401d00e541400707031007800100c51500821000e0b0146d04030444601c407421301c1e160380d00e226034020015250b0203c100a40c000246482c0b1405220621032071949015103000d00009281440080035030702030b10303c0f2000511583c0e082138103a5045400849021600311050310b040e41c1507010344009150010701c0800d02204102408044050b11a182400507566021386111202034072070a4802c0d1182d4a0300c00b0411000c03851201c0216801740c00342c40080c0c4102d090100c503000c6080083c80860110f8420041401082480d00000d402000c0480b05021404201c0d21400c4d10792006201e041e0034403403030305041c2c081a00290041c3c030300300241140040d04c031540c80d01d04034040e50011000d92302c1000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 24190725 1250 24189475 24189481
    0x602070e01090905120313050106030b01060e0d030206060f0f03010c0504080d0509010f0c0519030801090e010203010302060306060903070b0c060403031404050c042003040c0504110c0c1e0405040b0708 88
    0x20382407103244a50f54000c2c0013070081280e0f96542c0c262030b038070241c05104503616100d48000421001d015131401107100d0045075907a5032508038010400b043c003607015072240602c801d20300c0c00700b680040d00030b030001d1080342c0402c000d840800000780b640290061507501542405120364030603800c100030b041200c01c0c01c0c081e6082c4981c02d00e402c899503c200328040713010852034841b02c0d0340136103d40300b4014070702c0c464001c803690864902d0301720020301100c0340c0440000320110300600010446004800407041d0560080d801c41d411f40e40001c20500000f00481d006420105001003242c0d01044105d009007900e96065950707100d5012101d07121207003140d0a401007818444514450706100e468648181e41100107030011411003020440645070200c1180071520651804128000380c0c2d1009500071842820b180b40c40b240360105100c240e802d0011401c01081041c400401c010501282030303402c1160488010282034092002420440b01800312103400514000801c402c0000c1c40500c540941065116509207607 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 24191975 1250 24190725 24190739
    0xf0117070e01210905010e241b031512160302060309030f0307080406051006020a0f0303020f0d020c010506060906030a0504020411070302010905010b090702120306030703051501030303050f01030b060f041103010602070e01 97
    0xc8201c0a2390203122400d528000802c100241058004c5815014100800d034610018061908291210202c40503400003480c218504101910b03201d1504d20302a0042240d11000f0301310039929440042e0051800000180701c4c124148101c030a5542d81d040c0c0b16449090008004001c11021181224403070318060100e009141507400842c11588981d004024041140d41c907540041c0300d00c24100d09054090010041c400310b50805448010a01076006880e1182d415a907401d40f00054030030790043e001041280120b4403110708803540b0460741c0b800482d20f9140c0d0701c0460014a1102486060840d000ca008400c15906400000049014030002d0140303030120b01c10014400429a07070600541c1c0300c52400c03085401c1600240d54420700c000d0a07200f1407580da49031030741048001c0e080f440c41e01080c80010300426405100c0c15802440c081ca401c4120b40c103680d0340304102c90b0050702651054101762072070310441d900c0d03070000004500404001078034cd596504001e9a500a140030744514118981700102d860307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 24193225 1250 24191975 24191983
    0x60f0905180604020d14090a030210060e181501120b1005010509040b0117010603021e040501050703030513020d050304050112020304050307030309020102100501140f0117070e01210905010e 83
    0x20305000c05141e03940c940104100c02503108030319030010369032034900041d24100150f0016115046e020f000d040012580c0c41e0081c24588403841407480709244c00c209015903120496015440311040c00c0d00d040000034100503601e441264044204660070000003c42c00408160140b031080f481051a00140e4550300142d8104a019004a0380010000c0c00b8814242c6419000006031b20018144007400d406a100c107030000102c241c10801c0800c2c0c0005031b50008504980c004000350b41000316817401c0504100000f0200e105040000c5d04058645011918000200d21212591607000340804500020341c501152030303070032031700c5200e001c00c20143c1001403010a07802103a100d42d40c00406140707030182c1560181c0045c40180c406a0451051403841c03602507800f842103501801000700340d0303141c031135600d401c200310880c0319000302d4100010000d030b0800500b0841c1c1442c3c6c00c401a800d00c0701c00c88074840c00482d860b031520419203503070301da4007020b900c5009802d92080080d5800785000b23105d000007050501c5c2d51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 24194475 1250 24193225 24193249
    0x1020307051204090c031e053102010806030703170f190c020a0906060905060d0e03030403020105040b160f12020d0f060503010501090510120609020a0e090c15040e0c0403050106060f0905 82
    0x950b480000c218800d02200d0744440d6010456250341c89c02d20545942c00f0355000000c16829802d0300402800744117541e0446021030380720800b100201a150304640d20404039050b400e140f1424044049102e110f800700e078000341ca107a0440000310a13640000d60500408000b501c040c1030f401828034a00104059449000d903200352601c03910b405840c0c0c0c1c030741403d0003607030380c4144200c000040c0c3d21844124103045c14802140100d000c2d0380041118140341c103102c090700d4800307050010590482c84c50201d105810045c2010b505181c1d08000c0141c40c0020080c00c0a07124402044100928041d0951002655980310801303070751066000300040e81c1c80360649001ca0b00c0070348050030001c21003135007007041e54401d00d03400c04c41d41d10130300300468012803560116103c220203030130002d1030f041440c0401458101c1000700e412400b82c01c0b10740c10000620348200340094440d0707000344884541c42e40001181980020200e030025540540208142640d0fa00c2c020204040c85071034100180101d8800a000d1405280c0501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 24195725 1250 24194475 24194501
    0x3030108120d020906120f06040b01080402010305040c03021507110a121407050607080306030c090f01050f280501080a060b09090718080706020d03050405070e0601020307051204090c03 81
    0x10803000081c0d040c9103640c00c074038118124280c0030007a6881540740d84e4041c0c07611100180c1d1a00070350824a10b00c808610b070060250340194a0140b141610740e034080c031a66040b90302030800040729155030038408419002900040c0d00075040a4146a800214900901c4018020403509513003c00c0e900811107000c003188901204600000840004140b852020a000201510843e0340d0180da40000c0743c01600281401c0c0c40c0700707001208210007403d00780400381d50319104480007802c6250840e4507440210040c007070395005414881c4d00c8080c42d200c0d40c554a20410001410810110b501728507c07150203200d000300c60000e44e40c00042950202c59004000030344107036146d91400c08039460140800403400414010400c40c60701c0d026114a505034015902404031900949000c60601c00003070314015000b03190000b0180380408100204101159442c00c5e1611480100e40039111702d00101e207540905031025015009040c00c4000c9013014900074012115a10400c1c0500284001c0640440e050300c1e032185 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 24196975 1250 24195725 24195733
    0xe030304050919110418090c090e0c1207050a06050319020307090506120103020114160204020904020702100c1505090613020604090e0604020f03120f0703031d1e03030108 75
    0x7010601e0114030040d80880180d2203100309540798045101510285072190440600c005000d04c100410001c3ca8814145000014410444030780c3d40d4600c44002ea100340ea644070f503100c1500d0b000304418803030b40c401c101004101483e002070407960180c40d822580b0915219128001d030005401e030103801524400c0008800035100d4108003003680e00654001020001000034111707000c6215074403040540560301d91040b01e80701640c1144005002128072844030b0b007100000b40034503510490000038000c840c5506981c0562244040d00101d0081d01070700c0c2000b5030004814450307401c4079030b0080c1c0400c00d5070301850130008126101c00600c400c4600503078241c0d01541090b400118406108070707405440c01d10141950b49010390713803242c40c401c5035400c100702089074001101340001d502d0038040007440844101c014105407900c03085154050310170f201d81080419000b04800050500940c0b0030b0300703000e40c0003408036043d198210311151030f4000e410392032072f030320622001542c00d4000000a680c10386558000030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 24198225 1250 24196975 24196979
    0x10e060307061413050d06020a0e0603130f05070506030c12060d03050d051017010605090a110403030c0c05031002030103060c030903020c01050714100e070e060109050603150405010816060e030304 86
    0x81d0035078400c0301d0000c0313450701d44000010b4503241c40a02e5200b050061200503147c000c0ba0600500b0314442d6050540300e50020b2085c407101400340310346030f0000c652102ca8410101c038103140543c1040b40700c0d0b1110786e00210110400100c808403100509082080e203e104030965100400c10207604810707a40940003410038091045480821380c0003a8002e03d030b81c0048800d460341e540429010712189451002165141d090801803070800300b1b0100d422072046d803400c0c071120032182d001a40d60b0040d840040c1c1041200002c01c82840314408540c4042d2402a0542c0c42064040d000390002e54801c0c8812a0624a080000c0d00b10510920501d01c0c0c140d0f05078007401c1d60101160044450f40c0144d5010360b44001e00c002c095064601c2000440c24000340e002c80801c0100000c0d04460521402d5800703010f40c2e0504000b0020b25aa200b0610002c0c2c610840784a5202d48a10350180d20b200460882183c10500e003500100b1594030000d400c51604142000f280d00310f44e00d03801c04540ca42501d19881d0f400d175000340700c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 24199475 1250 24198225 24198257
    0x705011b080f090102010e0a05100c02030913020a0c050d020601051e03061602150414070b031e1b03040b040c050a0302010c0f02010c02150a0306140f04091b0608010e06030706 77
    0x141030403101480049003110f8a08905814070148410459996004040002d010750403030146103030bd8001c0380003941c04c11100201058540b0340c034554504130a03500007204007886000c0c82030000c0d8107800504440d02c100200300c001c1d60b219000c1c010b45100d04045180c4090b0904510300c4804182005000b40c5002c1d1280004001d2074040c451020b01075019030a040c11072a5031080300d041c4900e000f414841614a41502c69a040c4221030300012102041041000038012852040704110101261006203551f81c801d903045100c105180522001d420000500c003c0c4800a840c2900031401446145000c565882c1080b60913804c6d44802404160071141c0c05020035800b8551041442c01810614040d4425500094100806500f101082c4402060001c1c03030550501c601c0024013035100012102048020004807143c00819090303110f00c0d01c420f988010000c004c03481c544980e00851400d41c41d9502d4480140600000340039040443d100400014440d00d0009258411925140c0b1034140107410448 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 24200725 1250 24199475 24199477
    0x1090c03150b0a1d040e06040b01050102060402010503040b041a0103080a030b010504050a051e04051305010e0d080c0304060906050c09010e09040c06050c0c060d020d0c0315051e060a020705011b080f 87
    0x10003403403414059181003000d5290b81c020040c2000c0e00c0340c054006032415140030342509c00180c11071411035000108000060f41c1003011243c209410a1404030725540318a040f400200e402d81d514000542804000030400255401908035207030340c5c1c3c030103004240c1940011250342c0030728400c06074018480300c402c11460900d800310700c02340604c0501c6480100d4000c0c000c601920410340303511720320b011441440c009001c005c3c4202682841a40041d056250340302c0c1d40144144805090900d01c1e100020100f420411507500048034554000002d0005181a40142c08540c000418190200e9070142840e81d4910b40048400e201d198031491507202d41781407840c01c498580001100728034034816400c6245450b5200c2002d00560080d21034096610150080007a0580b10a0050803040c18140410880d105294403445c1e01980c0040c0d503244101c414415a451900b1004000c5a0b004000040c09280c256400f0522405070742080c1c039605081140031708014075032011206c01500095007803002c0403410b01410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 24201975 1250 24200725 24200747
    0x306040c0b0d0b0a0803030105030712050309010503061c05010b01140408070605070206130803090a09140a050916140109060f140f040914010e07050f0d0504020a030b01090c03150b0a 80
    0x514005010410900400c101c3d070f600d50170202032540003200401c958a020030060014204007041660300d03c1981e030b1695039a004400a0a05010010002070540d488030350700010f80d16584c00d007402c8104603900f0300d5802010980d82403130008004882c3c04240882e002e0499088511020060180d10b10702a41118103800161007243c0c1f2400c1040305410346001901040d0140803910091540c0c0c108040802c211802994050900241003022042c941e07210310415036440101c0b4032000c0740540e6640c3c0c030365042c600490b018490086500d240451040040e01140403080340c20b0320764040c0c0300d032111001d9404581e6410414006060100004080604480500760804050300c4040c201600c48104800707a913034a010b4a03402e02c0c0194010407441e49a100429006611030409600d8102c0b82400400c262003028440800701c0d13104d0000c41c04549802d6030f000021900806003007500e58441d0344002c041d20101882c44c00003400c000c1c0c0c45452079001d40880c42210a65088246082c200b41015101c2001913 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 24203225 1250 24201975 24201997
    0x2150c0a0606090c0e030604030806040b04020f07150203010e1f0314060703060e0c0f1312150b03011b1805060a0c020102010e06040308011211040c03020307030b0306040c0b 76
    0x14800200020400c22090065a20a04002c518503003050156012500c101c450941003040e0401540b40e6900e012420701e4000340c040c507042c012030b1b6030314010501408858078419009880050f00c0e91041700e807180580f18951054580340c1400e8200d0786224181c0c0030a010314180070b40d4443c0400c4900d00c8140c00c43c0c001c00780007024414415601c1c1c07592a19802020310104507504a0300c2049502c41c5d140c0b0440c000380c9014140c0450b01d0504200d003130041d01170104a46403c0c0b00006800c01c0407400b202c4c00c03900406440c54004a1b4031034914141d0a20598201600c0f070190408000200500e018040c2c050011904a200707016a031146000726a104601319440700b0500c3c840501003403981300c08004200c0c2e0f210603101c11b42c0789a201e01c002030031074040c400000314580040b4284400681e0102069044030030505410f40301400c582005412000d90080240c0c1c4189461142d24503180c142d00a1445003245031410032014100c0000e00d030721040d00329001000c03000002428802c0385940400b03007001c4204 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 24204475 1250 24203225 24203227
    0x70804050c030312012c06010e030106030c09021b010c0203090d020409020d0b1b0408070b070c08010203010f05090105030a24090b09210c0307172a071202010c0215 72
    0x40700c408241141d01c03041e0811040e2a07100c0040c0003801040e064100148610600c0340101c1003180d040c1d03c41248045c001c0d504004803452401c0e2195801d4022001841e041442a05840e942c0d400c071a009500900941c0d11200001c0729140407444184580c007580500390300550310b0031a482c0104503e4506842080f64080d9841d16524050b0b210381c040c459031684603203a8070180303040848500c032403083c000080981c01d150400c418060002c01291314811110013021958460b03a143c035100c002d03600603402412540d8800b200009130146080c0d0f10b1400c031041aa020900740e40c84030145030311401004406450740c03ca9280d014680440d520b00c2800d01a983d50380001d010b40d84d03554905402000740c603513644544c444058080c030f1000c04081146800255000700d803621886400e0152640500350b0090080018958506500e0724181c08540c1c5c01102004c0980e21501a0b0b042c601d005d94031020301a50500c00d505d40401e1001d601e40d019052540c05860351810f2044039402c004500c410350000a0800070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 24205725 1250 24204475 24204493
    0x6020a03020c03030712050a020403030905060304030507141f02040303020309090907090c031d0607080a11090904060e070501050405180a060e1003140a0317090f03040906050a0909080307080405 85
    0x410701c099802180c4035174802043c004211440c1b025584050f06541209104020400010750840150f0b000c6400c00c0d1100da0301d907903d80c00c060ba440c2c080c2c2c0a01801046001610103185003001c546000200200c10f0104e000c130340c6c020501412400350340402000342e40304100c0884c8920745081c440b640808030304200e4107103a8540000c9019a1415541c0c840465240c100c040e0440340a940c00c3c410302ca1810008118a182082c070060107144090100c80003d43e441c2c24030f03065401000c0031a90842c2003c0e0a402c62410146401e800408202d0f04a046130b00035140045190f40c400c0341124200d46005040d0b4101d4507014003800010780d805080d1240d8241e960000266040054002074420480180c0038200f46183d410312082c150141d003c2d080c02e54016038860000a84c00c4201505c040000406124003940d07102001490104624141180c510020800041c030307064507003041080e1030094034442c14266440d400c89007a1403040c81c0081c18100b0500015110902c81d14607150300c0741c054011a20281 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 24206975 1250 24205725 24205747
    0x5060c0703082b11120901020408160302030f120f0a03020c0d0e0a090204050904060506030f101d010b060a08090313030c0611030c2a0301050901020405030c1c06020a0302 75
    0x161080d18510b100d85860103450f008003501c00b50341c1d041156240f0081c0f00d41c03c00e150002d0468403411194042c1e0084c10404030f081d005003541030320050301340f0004481807414a0702d800600300e046844201c0c868810300d908601d00582c081803036180502a003011078140301e0340041414540e0483c001c00700806509110300204200200a40103041d00b01b0349031100460018000e0280b5401203401100200e40104402c01083e21040e40150b0301940000c1c0025040d280e690000c1e00f842000c220149851080c00031910b0302144540c003440c40700313040d40c1103000180c4010180600361880d5104640c0e00c544181304c5034000318004c504281d0b01c800a0740660740b4011030101e011040403800d400684001184840c20300685030011821756008036490001e504004a2801940c0d40c1c03145008181501c01c18030140d950025032031142070b01ea0400050081c42245050460f43d8004d410a100c1c40d48280314002d41d145090400e03010041c3d6907002c0041030320112a040d1950310181d400f07491968101036003000108011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 24208225 1250 24206975 24206977
    0x215011415120621120d0207061a03070801090803010302100e0603090c0f0a051f1e0c05010b01050705030307030507020304030606030f060606090503030d0b0402070605040f1406070905060c070308 86
    0x511402035851014106041800700e40d034000c1850110302c82c02c041c0d054421302c0001815007180603506800d41d580303012150101010b80a5580003d040604008506481502c490b8400300d454800380d0884401903681c519503404c0c2c030204100903040c5d80c8100010310241c10080c2d200d800403203e40c108a001907200c030f40400c802da80110703410010780d00210f0552455141008000c041248102c0700380300c001d0b0400000503114034400380e0b0b00118507080c020075801c0354014001c0400c0d44840c010304000380b401156000c0d00c04031402d40202c0300d55180008100c2590300903401d4884003600704006506565606034281e005000140c4035030103502c030a100020001b201c2d030042201861280c4881c0e80507a2007840c10000f130390815007041090120000081c00035407000000ea80c3d0f052000200030402d500c4001c0402c000384034220000c4d02c134500701003c02041c085114109a0303858815030082280d2044131000b0360300c842d4151500000140300721420001850200d014010a200c0101566502c6603669182045 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 24209475 1250 24208225 24208237
    0x614130e0a08070b072102090d02040606030b0405010812070f06111b100c02190f020d0c060f020309030c010827010b01030f020403080901081003050f06040b06010215011415 76
    0xb00e80000f03030090401280100640c4c118140341030240b982c108407004030304c4080c2041c40e52400c07654046032000c1c095840200308450319402610401641d074407410020044d050b21460240660300308400001c072140000399203407900d0110074040f400d280641d40c0c2e08a10603c0c00405462070740c1c542c01640141c0440800038410083c81040030410103080301c5c030312070a228500d4000d025641c82c040010101ca90042110700c1041c603001c5e03c0b80c180c031103585080210100c0079a0041d40080d51a48103000300302d85a03480c00c0540300d070703030303c408845d41002442240c0c0c0b4840e0b882460b4054100b071020300f00d04e5006058031a0001e01e5084045082801041d20b030083d5000e800c803424450391101c1a0701c1da1942c00d80b00e60440d030350340c01c101545082d04545403c0d02e2441103491050400a07480300150b6180341d915000d10146901c0400e9541c15404512656581c280c19101a0344600c440b1021900c03c3d8000100d400200c010f07082d9944541e1329151880c07042140f060480b0f0b820200ca8000503403c80010402002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 24210725 1250 24209475 24209483
    0xe0f0d06020705160b0d0f050402010909020c2b021203011202040f0609090f0209060d0b01030b060109030813050a0b0306030a0f0302030f040603060e010501030510090203041106040b0912010614130e0a 88
    0x602c03a24450b86c090705484001c1c0084008074903041c203000240c1d81c0203c44105075104883d01580e11a98188810b203880100103218a00400c0d80781219181c0e00c801c581c540e58070041c0e5080b16158a00b0344c0c60042d2500c000e11543c0300c440d80c2c40700741e0001400d280c1c000094030701c22108001901c035900e01ea0324058400301f19049a02030351035091b01d41145841200300d90020815208071200600960321200e80c2c10060001910440700000043d250f68030030055071000d56400354501d078a48001c40459444101e850161f0352051800380004200c2030942c0c03054a1107070344000d0043c486451281c940c3c03044074001d010140d0840c0001c103c243c0c854217100004000800d000d0b500060090300d462940d2400d0350068101d030b4105402c1505101201c1c3d12444000152081c0740c00040c0d03282c549192502d40c0c14480117400d50007480108000400c174004501500344403500342c03120000301107a0046682201c0140c055540310807210001d2046905240881d03d80681900f840060074410ba690b500d03242c6811042c0c01c031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 24211975 1250 24210725 24210727
    0x60501060507050f01050106141602060c030705010513020609100201090204051008100203070c0221060115030c020d02061302180103060209030d0503010501091526070e0f0d06020705160b 82
    0x5010000f08015040e289400f24008000f03550500c40700410006850210b0000000c002c580c1d00d44071680b405200d680140e006003015a1803010191043d160381002070306440720351803d0006000030b52004a042110366000700341511340642c1401708502e00b005580c41000315940c0324001001600d4510450b80908041f4087c080068901601c640c5050b43e60380c100540c0310b005105010340c45420080c002403280d0f040f80c03c0c042840341507804165601110302007082a00c00c0100004d24100305013078004084c140c658003400655040304041c2e0f681c804d0700307030b280700146c2c070000000d080d240103c590084028401048a000e601050010900d20307102038006441140d0300240c4e4480b2481c0c00c11503d02d0201e00c40c00c10b03030706540c50100080d09000e4a44030311008020000400c2203128494011400020b50b0f040701006801035000341d000c0407800490301207000c00d45078002e003055072500010a10b4030800c010b01005402c1c40650380c40c8007a410210341219584101d000d40c12030090626840006807814114103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 24213225 1250 24211975 24211987
    0xb070303020c1f0b030c180c0d020703030504020f010216090b0d05160602010b09010e0402040c0e03030a181205280506070201020307030506090115030b0a05040608030c07140d060f090605010605 85
    0x4220303640c030100b4610aa000000782c46c0c01d80c0381d03808201c10046040403000d079565100000780c40d0741d12510368000e040d544001822810140c00d540058080c0d4026170b1691001c40d00500103a0fa00e41c0403568041440507402800c2210350010742020780300314009031141d01889055500d80349024010309060b081051524030074031449509100303016030b525003211094255450111000c1b110a0090400390240703494145a9005502942c20f0030701f105c0300602242d07600c0074400d50040c80108103d4000d0000c500706000060712618241c1c900b84032940101c050504021020030441410b2150320103050509845558407010480c148003242c0316400702e070000b40c2e032450240f100a0491709c006080c14454000c2c1401030112105981c0c1c440310030041800e00040e000d501000040c08140150321841d40142022000b040c80079000c0094208640190102c5164a460b000c442c5140ca8044103882d0b0810400c20310031011903502c7d005003c80d01110180083c031a5010b40710303802564005d8201c000401c00c0000c01e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 24214475 1250 24213225 24213283
    0x305060f0702071a030c07170a0f05090a06031d070602030408010b03070b0304060b040e060c0a02010b0d0b0f04060905060c0712031401060507020f0901170706020c03070b070303020c 80
    0x1180c1e901101910140c10800d00b010241a50380035000322200045001200188440d42048100d9180d1604011215100e0607821280200c59104090a4000540c0040c0c0780f841a070241042d43d240300b200078440380070740703007030960480060021020a21050401141130380014205121910180281d50302a551b900d050a06660030f58901204403800b030b501030b91080040da1980c4c02902e410540c01040070030341024010019018060000201c4074070b00610090007051806900280003c4640b60024411002e81c402000812040040082d04880d8910006080c0841f02819160701c48c0c03040500140c403000b69285c013803401c5403c9501c0a1a0396000603580280014000e5070850414185000e0043d4078051010303582d102c00c180300d1035003403003030104040003156100d402031100c25001030810260340d81e4400b80d04001c0700e50030318401d100d8003e822001c2070261010500030078841e809401407040c03614204d0890210750003004180c0c2015170030300c0f018034805014008a1144440340400750b10911101b80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 24215725 1250 24214475 24214501
    0x61a0901060903020102030d0509010905010c0f0e01090506040302040509100c2a120813050a06021b03130b070312140709060302040e010504020706060b070308041a060f0405070e0307030506 83
    0x41c14480710407010001070713a001049600ea4070160364003041648410b45554090311034040c00130015420041e1130540e20742d114a4042c000c2945945503a1031aa0780130054407001d00d01c0c051543c10120800091015041c55080f0300d403c88942411520044843c071800404ca542c120482c4000958805188400e080d084002051001040d400640d50b4240c81d0f46880c4020650940e200a001900001980b044025840411043d40002c250340c42e035200d5281c1100258843c0e2240c408803109250001c00c80b072800002d54234003007003507100101e64a017490503100e4aa000084202c0c00c001514802032134001d40c0e401036110301c640e0400c100f0000c2c2003820000e0003403000c0c0e8010702c00309031041c001000302c00000070541c0e044410550700180e41d00181d0810300c010b00034a802400104130001011001c155201d50010b00c501c0c02200c0081c00230394600807400340c8030030903149190b01c40c03180314841c50070349010303406260482c140707041c600201c00303140000c01d00303103092640151040e4002c82c04002100b11a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 24216975 1250 24215725 24215729
    0x105070206070819050603030f130503060702030a02101a0a0803090909062206020f0406050a0306050303030c070b090f0106080a0606170a03050c03040f0902210106080112050703061a0901 82
    0x10400f000645040b48040f0000c0040150368900140c5410104900352403c0c070413950352003842001d82d030b07a0f0400305100407000384c1140704540c000d1282e6000221040e1000c81a02d004110540c00381c117400b43ca07904600007500451250840c0594101e20304150780e0754064500c00100f0035100076544a015040c1008003100e0000c2090703100760002d508000d492500d032203140300e020a191000d950740c4d90f03a40c1407408c001e01910200d0401c0760000a80415140c0d004005440204060364090181580b548181a1217000c01d4949441e9404240000c1000840304c04106030f00410407822245881e010213456825150309501c0500c0a40001180710240105409039078081c001071017407821900e000c144401d030741e1020032030064104440840c5d4100501028000c45000f0108208294422a10344001d000290320801041403200712992440c02e2015411003200d0403070740d0a4441442503131030a5400d01d424960118200d40342e028814010001450b544600302c04070301103d441003104550344061040074001a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 24218225 1250 24216975 24216977
    0x72706170402030304060f050d02070b01030c0f0602100c02030903070e07030b120c060708040905070207060f1701060e01020a0203150109060803040b0901050a03090b0702010f050604150306050c1b010507020607 92
    0x29800704005a100081100e040791a240b4088007080101c0c44101d40c1401818008146540000780d4082405002107030070341a240158090412155102d00c505501d0320244544805a0488001c1c1005100c80ea40000e000004500560346040c0724100000d007050815040720b10b41d840c0c0c81d011300100e2507151040664820040e240c1214880940c00c03070380d682712050060944124030028060007000007910969000744171042c1c05006909001501039140d422600444000a605e01c9515400c2803140c110700700140d858070003500b070303d90070700e00200d5001c240911881d046d8424120030400588007003014021003081040704a06550410102030141e40701030740111055070040c4010f01003980c5000c21600552400d003405551031800303d030f0270303030282c14404806001006e11074108407051340c06402020a0400548082210741c1e07400003000101c944c40000c41d01142035034034003400040c0147e48000d03001144840744a050241105400981d01180400300d6510b9448000b0302c404503030108205078100f551 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 24219475 1250 24218225 24218267
    0xa020a0c020603061c06020301080c010e1e03030c030d050103050c0301050118020706091208061f020c0105130b0a050a03050a09020105070209060a030602221409010e072706 76
    0x15011000304914298180648100790010210744145e64904290340841022203d1141c10840c82c2440b0b80250000d10034000c540c01a045071149a611540b00d40d080c13600d0051803156080d110031400042c0b14601008103805100400c0414100d540c2003000c0c210141a0319404171b840e604502d0031034101011202014000e81c180001406200c1400107620b1031082036010042e25a81d480c14071070080c0c4568a000340c1200d4070301e03006440c0654040b0010f8071418098840c007103080e2101d4084a0801450020000182c00120304620316620030402041420000301600d91825140d0404402d6070b440720301d201d40070550010302500816007501035640d2242002c00300308a40300311500043c01c01c0c41139003c0284240702070000902c1d182e40700d00c140310103960044011500e8417811203222411040219031030030040380400c400200c4036850340f490150790602030b08540c8c480c0d05e800c62101d1030b480701030502c40074000d104142c641022909030406034026564100c00b01500c2c0fa04402400c2c00c821031009008081e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 24220725 1250 24219475 24219487
    0xa110c070503240714090a09060608250f02030405090c0415050408070302041d060708011719060b011403070203030f01120c050105030604090213020405040e1c03051003020d0c0e0a02 80
    0x1100c822030f80c0c070130924149104280807844029655120b40801c0340c1d800806d000d0086180516680b00c0c0e400e448580e2220845511410a00c04098144d0420300c2a800c4066007401c07407075440f8286813101484140102d0b403c140d159000500c00c03460031241c5550f511070200342004440b001e1090341c1c00c0b00300c160800901d401d0038038908544130a80b03800013038000d640700c03100b0701c00c0202c81020703403480c000080e402d50b01203043c04070005200400a00c141403c48454142e00c1c004140b01080b251a01818803040503815032440c0d0701c80003c2d0602c4010345040c000128800e414065243c0000c605c40c0e441980650b69900d00102c100c40c40c088181c0013940e60405000d0707103000068441040341d09690090a1441d11390b07580000090241280c110002e402c9982460b0f050380c030ba182070b000340082ea2401c480602940c1d05a1000c1c80e0b4680440460002c1c07405548041c000840c02544960740042444400c1341045440307801260810036000403c0360640800302c000c0206240c8614400d81100c0014000d601e022 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 24221975 1250 24220725 24220783
    0x3200603090a020f12070b0901050408010c03050702010b060a052d03150a0617060111100e01060306060602160b0901051209030307020f06070c030e0402041208040f0b07080708030a110c070503 84
    0x441b0700e00502c07000b0b03000000d2000c200d0780100300744c40c0204031110082c4060444014020301500b000d0b5888800340d800d14100811926000c410346080405030758450742007001141011100381001c4052524106581500c055003482400045216129941043c103c81d0122810302c00c1400f00e9502080030400d5000940c954030f034986615a81216003440e00b01c114040d02800d40e810031400c0441c603002c05141070105400301070190480c0c82200c0c01450104591659940c01b80c1c0c03181100d1401460f881c007400300911000c8600380140025602c189071a50529030b16102c000d41d481000e840b101c14039400071040000d416030400c20451044078903009072a507428010380280124cd9040390080600c000d4206500c0d02e40c0301d690540b0020b007401800425030b140182080c000980c0a409034481c0314080040100302844074508441810360301402061410503152603483c0c2c5c5410140c1340740601c0d40c490743c0da802c0984403000503081c4840c0c0000544003061410341058070340758101c0d49540ca8010842001d140d10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 24223225 1250 24221975 24221983
    0xf0906040c090c0e0307060c030212031501110703022106150f040e0f06040308040b1003020109030b0c1c02090a1202030c1011060c0a0807020c0a03200603090a020f12 73
    0x80b501040080355000e0303010820f88407425002c0900e40c06101e03030940007c05a42c002d03e11100140240c0907100c50b0f00d0980403024051001715248001c014505c1c9130030480b0352042c0e000c600060a100266401152070b075001503440c2c070003482c00c0204101004a00f0107400800d000e01e5400003140080503081000601c04105800c4e500d1200c079103c1c654400305a8030301e100c244603100001da04c0c00c0607a0164505071501810a41e02034906803010038120b8005846002c5000305182030f2078058480b02d0314a461965014511f0b48010450100c0001c20303c2049044000300c0c90b000029100350501580b44c2c440901071003940252684000b03040448404610050b860200d02d400c1000c0080d9445200d042c1d145000f5650044145100a9207100d20000c0201098a00740074140c4100650f407100225111070300c040780d865160350541980710040500400005101c404003450590b0751801c1c1c250080c40840020b03840750030440d400c2189070061b14501046190010310061004401c42e10003000d81210200741c1ea035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 24224475 1250 24223225 24223229
    0x6020102030402090a050a06080316050c1206041b3201030b0d0803090307080a0905030c0a031a0702100603060207060b220203070c0b0103050109110402040b090103020915040303080f0906040c 84
    0xc0759448000c01c4c03d84907e6000700c4040d0104034114ad81e51502418001c10a405407202034466001d440c400000394a443c1c0c809040708807408000300120f0b1a1522a1160030010429610242c81201000102c002840d4040e0340c01566044030856801030445580551030702c1c03200b40c00d040516009584ea50750f641d0054020000f41c1241100f030b125520010342c00d01d1840703418009030407110007003401e42080e5402100d040640e0710030360513114140e2000b81403190354000c07804020300c0d0121007c01d24400142c2c420200c0c2c7d01008500c110b440504131030390524112401130f0003d90300b00d0340014580080c4a0039009882c0080c0b030a56212883d0420400d10038202c041411005006a8002020800240c030170344003801000d410445c40220395070340e4a0410300800890804a60100c0703103050804d03062510b403082e01c0844550402c0b1600d04032200004600030752082000c0b940c0508900c040f44c82d680503070710180c0080c6101341c407002c110b82800000b0803015240108804040c2c1d00040810001500501c25203007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 24225725 1250 24224475 24224491
    0xf0807180303180801050c070c09090b060603130b090102040801060503030a090501050c01020702090114040b0405060f01030e030d02030109050f011203090b0d0b030f0717030909061212030901060303090602010203040209 96
    0x200d0070460b04044450f00c9071980c4900031039820f05003400040860f68004200182c411407108004540e01c140210940341d42c420050700b00302688002a00304d042001c002c580c01035004030440307000813541d910320240060540c0e40164580d40442d0070712007140244113040143c0001c400550034801040d80060603011680130321410080d0224150410f01d40035010b8820840e402803000090390f07190340d0000e801c08250301400c2d100300e082903000310041c04c040c895940612409413190348425070356001034014050180203103803948001c015900c080c81c440e00c003445c080e105500c40443c2c03d0611007801c035114101078011a2044103009100000a60820955001c6903189082030751034281d140042030082100755159505405800034000c41c0d07040100b012800d40c0c000c800043c00390031820f41100e40d64026800150703041202c20020a01c64600071f1074456980801c94111020303000800c55425070b941068802034010fa454801c180201900800040058002440214110300d0503800080048a004e04081c4c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 24226975 1250 24225725 24225737
    0x9020306180106081f0207031407030e15030f011e12150e030a02150a06050607030807030c0302120613020c0d0801030c12150b0105040503030c1005010902130306020c03190f0807180303 81
    0x1b004150045040c80c0f05c03484a1203030290ad0fa030860801800680155407624404c1d14205080d024298071407040d45d0040741d00007000e400303d0703003402c80e0211400411460700079001d944803030001c1c1c0e91114000e86040141700780035840107010400440c0060f81d61221040d10b050b007041c02054407aa60014482484c0d170410305648090380c84100e100c3c00103000c5904680e0b003160002640606040c0c00c809094094459607508000d132210f1104202c2c102c1c080c0c10156100c0e5550700d400304001d0b24020010204441c400200107280003205c8848519040c1113613a544040b8483c00300400510000d0319603000180342c0122489110f200b03a603664070b1501021000e68100603694003802c81c035644110b06940103000040c048a41c4c1301150703081d407992421107042c007071001c502701070007c40e81c2c84590083c5e901492600341411003c03410b5988860103500f0010392a2007910040c40b58250040d041c903401000350301e040e12000403680d5041402450010010b1928042c070070038060b51111a60040b003a1001c59806144c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 24228225 1250 24226975 24226987
    0xc050a060504110907080f0601020609030703050309070b0c07080606030607080f0403140c0106080f0102090a0501140913050601020c01020f0d050d06080f030c07080a030206010605070609020306180106081f02 91
    0x11010841c9801c40f00e074000d104502000300c0240c2000820740101082040c0410b10343d50000126500c1c50116a4003016410a1100310300190041000d150400c1070780b82613911081c2c0381c80420f0459080600300b400594004441005068024401d050704413006601601c0c4c1458226005070010070f01806014142b08400d00107028103100f1942010503a0b0300c44010783e965484030300d60034068000c601035000301d402506149040514140308031810001c01920304e01485151000560302c0800702240e01403500c03002c100c6500a13584d81940c505000c41c00c1c0030001464200303000028501001030b81924199400101c2140004000003070005101540b0b280c46d55681a00290742c00c00f504041e4450540d910a8858400c214030011000d4038003118401c0c101c4aa080eaa90b00c40c0780e58101e0410041c016820240050201905c14001422607500585000c0340001c0300c1e41c0864031700442141c1d5800e8031203072044400400d51302801000000e00e514401001e04410100014280801d61024403014550000b11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 24229475 1250 24228225 24228233
    0x60302010c020f0607020d050c010315031a06031009030203030f0703020304021e01051303060603020114040605040b030406060b0304031808070302010512040201021905060106090b0301141216090e010c0c050a060504 94
    0xc17039440075406480b002c040c00403894220b40d82c5e04100240e40c0801c1c02c0554105061072890b1000d400c8a4120240700620400e090004c502100301a14068143c0103502901540c005103001c1d10b0001d42c071990085a8a03e884081400d40d1440038002e40d0406004000744000740e511005814010100542038105441907100140c4203407007800288181c402035003c0010502161380e005200b03c0b4000e0701c3e9500301d5070502c0711040c1709104500920b004a1020702c014042c005000018550003440b440c40022115200d54512075541c1003218110005840d209601740c01c0a0104c050070001c200d01e100400e096821540007030410700450701c90f80c0c1c000400000180c1907a200308040c2d20605c04040c0d821100080340d0410320b4896009000b010302148c802400007903041c8946007200d040340c641842e03288908064004125024510f078034042964800c0780c1c4d00040c20005070304107400070020380f98000341c500d00f0040ca060a484060b02c144044c000d003142080042480462444110b035440000010507540c0c501d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 24230725 1250 24229475 24229477
    0x120106030b09281d07050a1406031b0702040617070501051608180a060c1109220f0803090304031104060e06130608070603021206040b010504090f0b04020309150703060302010c020f06 80
    0x6001544881020350544c069070010407220251803003a9541d03a005511500d0746065045e110880315040001000044e40e003040f00920343d20000c8000181600d46082d41d0006801d8070b00a421035181c3c0b02203001500d2006e0b130100120b4000300020308007030382400344d003e50f46035000c040304c517000d0b02c0708000003001d50f0394a86440c4c1e52005110020f1005d040a07407036150081c8402548042160400c0300841225014900041e040f441001c0300e00c511303403200b481003203902051105558103c9504480c84181400109600302440c4100300c860011030721030345941089451095100c100034001d9103070074000d1100740151018a68018402d030740b4074507110341400c41c0070018019a40200118054610045400e40d419001001c2044a407400c091154440c04104005c0390781080115021803010402080080f12a03084465107000081c4000b80090800020034180ea2040b2035032a0780f90010209441c074817a2078084a50041050329041248904550010344544512800030744074000c04c010400c0603a80c1c0d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 24231975 1250 24230725 24230741
    0x20403081605060a02030903031506090405150f040e0705040c0507060e070e060f0d0b060301090b0103050f060702030f040b0904020403020301020d060302030c01021b060c12120106030b0928 83
    0xd006551404105004021500c40304401c03511401076034089078010019000b03030303405403000308095881c603262500c08000c0740c4c50183d107039900400180300d4259035550380c1c41414412075840800810504469080008800704040c189116901e000c4a00c5200c80340040d540041e58001d0300c00040701d100b003076019107103402081d10040450f0700740103e80d40a500003184030821590941080314240d11840108012500c0d5405083c2e00248030a18280128000c002d150340c001001400028640d03280b0340702d032115850241c105403500d90140341e03ca000703038004000b001e6000400d0b101071030400d8020340080300548510310640140c210003243c40c25090f81d507a811a40250760080085647c2d6981d05540c40c082c218600c805da200380202900701e416540003184140d20620902e5481328401c49210030000769410800040c14244108104959181c803100c004114913030403030251003881e44c036000700123040c0c0e03070712040031400b403030f010018482100e84090010b15950100b51210108101d4203c4282c002d103104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 24233225 1250 24231975 24231983
    0x506010203120a02280c0b0403030e010207050309190f0b07021302030a0c0306050312070b1302090405030310051801090c0e031207030201050a05060916050409051501030c0c05030a12020403 83
    0xe40c1c280301c3d100c03000d58001c01d8000d08015030244c100340340c3d441030030031061450591808503441c5015400040c40003003000368071a200741000070b6210340d11148507003260001441103415510006a440070303450f0007100e101c00306142000b49201c49051000c6000e52640f41e218110140780003040c403d0466a960b1300312105504020b00c1152a8a00076007680b02074100c0400c1640400d14214000c600c504001c242c282042c5401078596181400aa0b2003a046400c010b02da200101451342a40005070740b90402640641c2c0501c000b140c8a0a00a020181c43c1b540390b40702503c06c0b0300c00400000340c01d0035031304c007141113444000700080c0142c42840c0688500c900c003242039900d4095418068511605070010303040f428041c1e4000c200c00d640d450302c4401105c500703640c016404542c010000b950284403084241c7c0c46082032920508055417100d01070141d59054981d1000c04c401c45040c1c0c44107507854814050305106601e401030200010784c507055141d102c0d45000e42c0400c00340c00e0111403e01d24075012240210380c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 24234475 1250 24233225 24233257
    0x9011a0705190605010501080f0124020c0a140a0806010303080403050703021608101104080709020c030c060103060605100302030402090c03060a0321090602070b18040603060f09050705030d02030301090506010203 93
    0x1520b0400f00078002406294080380d04280443c4580d03020422903816101725a02c80c030102c8403801000c4503402c5004c00c0100452052001140c030944540c0c401c0001030515402c0d9140a401d40010894060a644c01142c82030340802c1c01007011a0740100c4027030700140c260804969840b40c41c01c0c2241800c0c0100403201000010000001d0800000500ca4428818007071007008041032103049039456220314032074a15127900a80040c1300001355031340180319441182d4126071400f415082c205013044004d034400cdc0c480f1681d6441c01c0005085c0140ba0440c1e0000501e0300310700e18941035001403030715600a04001100d480200c0099126100c1603031030b8014540202c004031402c00c00c0e0066801020f0502612000a14070707a030700007103084c00002e82c0c100350380c1c04200b900d0600c00c2c0240c406511140b440c0c4181d920948403030380000410620300c20f840d0003440b011408543c808260070038500c0c011896021a000742e0148000a82d240e03408410b40e8151596024040307000d440d0400100c1c99070044007002085101 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 24235725 1250 24234475 24234523
    0x30e1c02030f1b0102010603020f10020703120201090312020a02060f0402130e0616020c0a03060c020304050a080a06060b0301120b180f06090c0f010504090c0c0507180b09011a0705 79
    0x64005900002100c1c031003c1c030b82c3c40342041001207090700c0107440020f41152010303120f1211840c0051003080c00a0803403048401190f925140d54041b5481d05109d200580d542c2c8455405055001d42000c42c040300c03016003940f4002410310700175a41c030001040141c0b0101c80301c0c00700e002c56540d649148072050140e1010310040744000005900c840041d40c038150002428484501a14004110354000f450000c040307040340b514646902d005448492045021404100070204a41d5a5002084042c144980c010b00c10351281d03241c41c2c4102d0307107039410040252900340b0040142d1240803400b2802198004280b6019484003541c2070280940200d80c142d243c05512100101c50000040c090700c10b5001c0300c01c555401c0701c08020b0003c10b0030781148070b90006400300018880003545802c054951007152500c2d803405c0c0c000d915551704050960708600b000c180d42e4007001905000601a04510070b004450840c96545407000c1c85841d14282d07a844404040302107032030b00c140320040c008050134451001c6488003800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 24236975 1250 24235725 24235753
    0x1060e07030c080906070807051804050403050408060708090c0f120d0e09070c02030d050a020a050a03081602010203010513150b040803090109241103040f1508070c030e1c0203 77
    0x71281c0064034000403040000191030007400105c4500410361911072000355100c0c240115416481800000310f01d00d8811b0099945844070b101e9540304602940c2c9240d200d50516458604101c1b0180c0024204181c06044c00142c2070003245a0040c118102d9030f40f40345d00200700c0031810840002400000c58000c071400440c8240e00701c43d401c00500411503101029945101090f50002e11150f0041d405500c4104400501401800245034014081c0121044c0c481d0959400d0700d840c808050403400201c02c8020b00c40050407d1407241c14120a5000075030466040202241c0c1003031009004680250700d8908416449c52250345420107401050b0700d00796296111119240e40c1d43c401c41d107480c00201c01c17810000c1d8030700c0341141d440389000080139074500e4490322081c100c403a00450440309016001c20040003c0c0c52809d0f05d80038004100344842501114101c44010f048501d00030440c2041c4101c4440440000340e210704020300c1800308440e4541d440080300850001d000c20b0031002505071050b0301b5118451 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 24238225 1250 24236975 24236981
    0x102040b0310050a030302071406040b070302010b0109080a02030c270403030605030c06090105031f0909031101110a02060a050c040504110c010c090b04060c1b0608040b010f030b1801060e0703 84
    0xa80c01410000c102d00340e0340c5003400388024042c80054010307003260900313221045d0042010079144000400c0d00d402c054035443c1c078040f0b960104604401503035441041107035658201744031034018860180a490301c4902a00425140c4160300d800d10300c03a203002d003007400c80c40718180c0da40301482100603031040315440e00303140140007441c103401814400c0c443e0300001c1619190203022030310000410303558681184c8500d10203181d510744628484225800b440000f00700f01c01544941c02c40320780255924040740308050b020b01e0840c1c845c040740c80303410304040200601550300000c105401401e41075000032142c1c1c5002d000760003030060f07811003503010341070030305001c4107000b140701501c2401610340080000d154028815a9294030b40d00c03a07020041c50600041122500854880c91000c0c02034001c6e11010f030396000000c4810302283c0149012071001400d01044c4401d01c00e44c00c2c00b42c03424003180d2400758119192805030201c000c110a0001a842c484000101e00a4204c2d5000b0110038010342c0090801850140c05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 24239475 1250 24238225 24238231
    0x7121107050a03020a140304050607060902030111130e0c030609040305070c030203060709170d1b0201021002030a0905070e060a030b06010203070609110f01030228090f03050c01121407050901110102040b03 90
    0x248074150b606060326040084100d230308540000f088a460800256152809400c5100d4240c3c0d15540c2c1c8c0c40d02c00d00310350241004088103a101aa0b0100150400c0c1110000706809050b915a00c0c0050007040075135241c490701c140e0000e80508110703885800c1c92400c2c02c0c3e82096600000c1d0180212814010000c0c2c0041e10002911106900c624032501c1c1c02c0d20135581c82415058100c009090b800740c0c843e050307020205e0000c541d801803041d14150070188408000f642e1003aaa02843c09580780c50040a200d803e07c1070034054075611780c40c1221130520701c002030416400d40c04082d04a250240c04104261b00800c03c44e90080c0d03025905003e5001f4908001c0c3c004202055118080c96414960200e990304c2482160302001c0d0303045540c003002c200c00780610004251750f140c0f00188078441c03001003403000c4100f01000c01503200318010080046048001013a0501c90a40d007070b0040e007014003250403034100c7c0030941e901c000d66280031501c1c0d100410041350600c10513a84a8181c2d44000341c00304646041c030f801148 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 24240725 1250 24239475 24239483
    0xf060b01080105030a03120f0e0303100e0105100c081b1005060406050105040b1206030109020a3005030304020f010e0d03170705030106170601090e070513080607121107050a03020a 79
    0x1c0c09a9035041496229058a14018001803e86004503404202540100c0d040c040d11a8001502c81040c0000c900d0b42e4002d5444040030300b0841c40407c2510914003075107014103000d41c0e84901d540d6007440d028090700300449000300f580c01d012410f0018246248207079441c426040c01102d07810001744120000401c030942e0201e0046081110105080d4090f40c222130465408560440c40d040c9603000c10b45401802911142d4035540307688407100540c3c1c0c0e219603040a04071983d8850030076400c260612502c1d0b000203004a40f00c2842e0072050303000c100040152a401501920603444480007103004031031a0001c0005039a000700301c00c482c40180f40e4800b12aa0080d0641c456902c11a184d0341c3d000d49050009204110000e405901050074445c03201c00d0b40360f00541c0c1070428540d040d84824000c0c40090301100c100000640114030000c1403040f044441d0010000d00c3d014000904045d0030040190002c043c1411440da1a041d1482002120100301e82030b2503001025241c1d1b03c002440c00940710388140304295 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 24241975 1250 24240725 24240737
    0xf07060f0e060601021b04060803070309060306060804020f0d0c05061909080f0d0c03020c0a090b1e060a05090d0507090b120304060807081801061712030105060406050708070f060b01 80
    0x1d080e000503018001c00c4160018500480078088003442a00c408032482e400649031440040e1a40f07042002d408041e2094487c0c0054034203100e00142141d4840d030001d403c011400382408003507100e4003880c020454045e60310701311052031410001c01c0740c1c045502003a002600010009220503e90860001d0300c98a6680d603004aa42d8440e02e50b9198a95800141c40f50000f14021001a00a41032030003018440d0055500050203800020282c006561008a0a0340c6880f1403080a01c0c04110507002c8100406010720000102808640e0502a406440042c0200080c2c2d43d80603036200c0c1141c01032142d00500303c0f0071141d00d4580410142c407481c1742c510700600c644110701c80109004019241aa165135440c941c117561402ea0880310780001408803400c42c1a4030720840b070b8417003082c001d410140025061561501e00400030f00d41c9843d0201c056101c0303600f400c1c80180f00ca9900c510880d4103c03421840c11940b5440142031102e103604c00c203640180741e092148500b40401c24070341c001403803540307007600d8807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 24243225 1250 24241975 24241991
    0x30318050f0a0e071b050703020f180f1009020705010906050c03090c0f01170906010e09010e1e1f0c120218010c03030b0307030c0f0902040b03070e060f07060f 70
    0x10250100c001c001080d80a404048140b00c001d1180b078480e0391185452078038201e40b008900055aa05000000990741b58228203014810341c14000e82501d94098242c03803d215007405001c040207a068090121050402240702161240d48583d004101030081a0811903540c0d60074901301d8028818001c080360281d06103000901c00d1010030094030311401820b40034208100e030200401c0790059800e48482d051056000c154040c0b55820343c0018410085000101015410040211a000801800c840362607040c0100455029000325503c0094415280c0b01360b100c40742140300c03a0410740703580d001c0d22641d6098000269540644c2c0c00c140c21070410394440106030081841060168400c0c400e500c040084a0400c0003482e503c101040300e003140c0645030000e145044640041d0030032110f54002d45441001d0350090041860511904d001001c0440d801c502c3d281c6885000b4103580001825030061008600d0014100d8490314200c039400c4105418065994046191490090510016800a851409042c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 24244475 1250 24243225 24243229
    0x2104030b0a0e10020706060b0d0b0906031b040b030304080f0715020a080304030e0114040902040311060c0a020d050a050607052a030f0912010f0c020d080606090d1a0103031805 77
    0x42c0b050b0740c1c40d03220058280364520010b41d4010f50f11034042120000d541d403c0000751101d500780035241c50040c1c0c40b40800c1400e90201048070090015140300e220b50000caa284030003980015907020301140640e07020829561013000241540226440b119103801510403100078048080340c2e000a40e0700c03107958040f007400300403001c9070340302c40488004200072010004030f0007081c0210703040400b03014145000c6855506040c0711000503040b0b03a011000c881c1d00810240308010b14001036040101044e00d58a0614011851f101e540d0303c01160003a002e460074070307402c505020062000c175080d15003000031200f040c00c0482c0d009046901030201c00c0e01c148242d907459510350382c1c2031100030462041c0c14001d5007092003584200c0031a034030402c40580e0101c3c5258418844010a0246d07041122100340002006981a03801a08100c0503040c001c040001e50020000755030742c2c10098403940d54040c0c07031144980f944d40c42c00071340084025144170303000508800004109544031100c4541c142550892400a40e59001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 24245725 1250 24244475 24244481
    0xe040509070503240109020d0b030a0308011a0702060403030806010c05010213050906040912050c0709090501050402010306050d12030504021c0f02010909020414060705030403022206120b04020409052104030b0a 92
    0x100300e40704131201c1801005101c10a0300070341042104888001460307541e403400246030140d0f0007000c0700480c09074401000303038000c1815040d000f0305d0901385182c50300c1155400140e45206901000b4240004c40700440d505921030000c40100395448002151355000043c18031925058038030406114400f4240015031508050092142503603000c05500b007245c40207402507800345c000d0602020544a001000a03106980340502c04c02c850048000013400e06090000405a07041c0d600032034060210100407a000071289400780c07901c6515441c0024503a142d030b100050103511308004a40c00c000200f02d9420074091030b000902c603c0c1c0e100740c842c0d0046a03a941044010390080744030391084c0e5007c0b403407480c4850500c84014010039100303000b03580c501034982d400100407040380848001c010700e40280242c9001100e02c01e5001a180c2210050313868009171380c0e904000c450003400240225103030b881d1541000001c2144001000c81150110121400c3c00250011a00140300564a06403030201140f102d603050305c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 24246975 1250 24245725 24245773
    0x40c05040c020a0b2e08010f020705060c1e030c0307110c0d0807060906110d06060810170a02030105011716080d0c050c060a050705150c090f010e040509070503 70
    0x18000d445403c0d030540702c04d01906401420741c066010761104d0300c4c0c04070350743d11201c00900344482c600004850030030a0040c00c495001d1b428200b214810000540480d0340003c100b0b5000014049041e41d4801e40c4550052018001c0c021100c600004800c0c8015411480085e52164400d5524003a01c000c03c0c0315942c0d82d81007280344140d0000030504071000400c406c2d00c02404024000d05001c1400c0d05950750313100450781030414004055038080b840d420740d0061409004002c00140c6090181405c1c80c01003007054852a100d03000d40d0450801d200400b40400b07000a00302150018000c102560b51100300d040d50304c50054011100e4011020403070508a20001c0000c16a9424002040102d030040c0c01540c1d261380360f141c10f407182d02c9081030001c0f8550755000240310004040e03481940325060340c9815880c0041b07110500400440300010007040b10288000d440c0744410440b0050708540a60005941f034606c60060150800e0070542040a02c2d503000400c4030403502d00b94102c901e90018a0b61044011200b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 24248225 1250 24246975 24246977
    0x11b08030112030c0209010e0f100b0306091315050117030f09100504090c0905090106021b1003060801060e09150103030e0d03030b0909060a06080705150705070b0c010203040c05040c 80
    0xd0005200d040c1c072901208294600c039007441c00c00805039400040886000f40c2c03124669084001c00c0009072005c4000306900031070700b076810200c45401c1c20000700007400000c00c0c150064400c0000108800a003441201c40301e074000c1903d0007200c000031810320140600f400348600100800b4a0803845002c0001214540c0704c91070445400c24296404000807415900c0c04081040070a10003c142d40c00da52041507000c21460715068030f40b6141c0800d01c204030505030b1180c0155084504180b0041c9000b0001d0100d0f260226038801d00710381c403e1001d40041260341c0005801d90310b0b21101040c0306014005d1280180300303200031540c1e10311030452250080002400010b000551f85d200854050800840b001629446801c0200c0c0b0258003401207650030340100c804403100c2d07201e00140070152442d841400302034102c64001e85a61410074010408a05c1000c203030300302d4010005200424040f090100740f01030222088000d40d60325186050390b02070f410544040d5010170b280d401c00100c604c4c01707105103850302c0c0d02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 24249475 1250 24248225 24248227
    0xc0503040e040204020408030d0b04051806070c02060c1b1305070c030e030307080a180501021606051b03030c0714031201031101030e060a020403060608060103020a0b0f0c0318011b08 80
    0x6145141c081a01c0c041c200326040b40c0c00b4070012803803a0060010700f21000f05244001068402c6204000c141c0750081c0c41106400d211502c001d040700401b1441546c04030581c00c0916101603a440030480c41d210750300540140d0b0141c0b0300c00640300482141840100030b03048403144803990540c506082180c000b41e540034041400c540492000a0041813a0300115400409590a050a54555100f03e0340141810b03000070766402003000600c0245100700001e40400c1c401001d280c410960b0b40010300b20540144000e000d40420404509441300c0400d41240c0072400a4035224284000c5084094101c5003085694020440d0329240301c1200000f40d840c150030300c00f4038202c83c4e40f840e19103005081441340310340c0c100340e01e41e0814400d107a820842907000d02e03007601c00165034903e107080c03150031641d041d0843c110641000300102301607555000400180c60380d0044560b51801400c0008000e03101d580c000d00d591340000705d10348868a1481443d031040c22030a80340c91950440c441e001c2c5107400340c6083e000304a4a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 24250725 1250 24249475 24249479
    0x90a0e15160c050f0319030e0c091306060909030509010908011b0507080702030109110a0608060d0809010903050a080d0b090403120b0102030d050108030711060a02060402010f05040504020703031b0c050304 90
    0x100c50b202020265004030192662122016201821a4003e0310b901d0003648613641d10340b282c56454891014004040340c0984001031008002554145c4003a0241c0c02c1c4c0c3d03281100c1c0c0c10600405d5031081c801032420090411103d0f24524001d043c0d03401c640308541c0403900003407000400c03620601401201303030441c0040019138940703028251419080480f083d1540d08040c0702020058409109161026004881c100c014526002c1000107115031600020200410107040c03100b43c0c3c65024500403c3e55210134a20346840c0c0c1500100d40c0d800c1c4035407000d05144280d49030358090107564030051002e40c0321207a05104202c826002e11041034010ba900900245a05100c1751007050340354070480c0400c50520649241016144128040d41d03801e800c091040e400010702d40f0200581615040281e860075180d01342030000303280c0065221980204064140b1061008460507503225074106c03805000010001c545600c41400d004000742101c0904030303484090300d07800c503411a0098003031050705540600210301d000c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 24251975 1250 24250725 24250727
    0xc021c0806092706010305070f0803070f020f09040f05010f05011820041d0703140406020a0201180308090705030c060703030216020a030f120905060a0807020a02090a0e1516 76
    0x1020083c103494540f403090007500d1035083e14105460300c20142000600c210350441c101142060b49a44c0140c1e25020031361030400180d08088161182c0d03a8021070809150401d45c000700345c0502d45001c030b45511249060070001003209007e06070b03400c640514001c000380404c1125001c111042070003990301940660440c005010301d140c002500031580300003d03d03a03103815002d035105140c20a41000103a50f0f160690400c2d102c050111081d1300400c20300c0d0502044003545000300b032014000d071000d0005500065001c0d0068001d4001502908203e15050381056403810014000b41c4c0548a550b207901038103000140900d030018440740e80385402040203141c001641c1e001d400942c4801c100140b8104982c0461001d0f9490341040300007903014644a8035040f03914a40045031500706000c001c103001040c80280410b072228000d407100c480460602901c5900c2e001c0f410303450511295402940407450a040240440994000010f0b491303216040380c2c0800e60074103268040300812122821600c4840490a0350341e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 24253225 1250 24251975 24251989
    0xf090d0302010615020307060515100c06020f0f07021002070605030a0905010603022709060907060807021501090b040605010206090a02010309080c0d02010c09050105090306010311061209010c021c0806 88
    0x1440303400002040c964850b1188641550300561030050f030404034490341880120f00546500201800f4901e0074049001300181e030074044078002d9020025907100c040b042140daa81142c503640c210701c469a85500c0340b0340c124407a81c1c0c02075000300c0c0684040c0049090f010b000142c00029500662036607030440c0c0d5081d0b103076402408104400c0d03519640703070600040903842d4400898000d0340d6005642e070128840c0f4a1440d1481c4010740340f03082580c0007004101e80100c1c003180d07100541e4400d14000c20700c0d49603107d00724a000d001c8807404410f401460300018404289138410200300314140d07000d100705031fa21001643c4500d03044a0304000d542144805000540c42030344000801c07803040a0507030800c1e00000752030345483c40010501000d40e544090340d40c07000750000d40200003000d0034648640f0307007404500400d0300c8440605c070060800d0080079440c40340d95100019540c90b001000f6042c40940740141040c0d01824010307403540050b0058410b446006040104241e40155140c1c441c5132003902c41d40d06001c44c13 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 24254475 1250 24253225 24253249
    0x6040809060d060308030601020d08010f05060307030e06180601060201020909010317070f0501060302010e120d12061203050409050601031b080403030207021f120c0e1215010b0706060b0f09 83
    0x8040410005689250b80078418070000e14010712500780c880c0760501c001780c6015407684a1409100490700100524400760700418141c410543c4ca140e1641c0314442c041d0302a003a490343d100e940b40200010029603800f5000e08043e10b0442004a48a5991307443c016801c07446001d92854205c04c0c01d00040c0080780c3e02038042c5121440110029151a6168884d8101a4903150044a5503515248100305660740000721034403144048800c0703080c031710012001981d00c0c0c030103400c103006118034100c01201108480d40084002e01000c001c1040400841c903004003158440d016100b41c0c185000040b94403944203201c1c00325040000c1103404060210314005442c24000100b088003055001c00009005032242c09500c1c9680242042003915810704000c090004a00b1043c2c2c0c813002c2d842c2a22110419600420403011110141c0300b00885640800d429030406c070000700c03485400d090740d000026102608800815820340502030412815803900b401d0042481107560440e07040c44240300c61f00184c9049000c1c401d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 24255725 1250 24254475 24254479
    0x6240d0206121815070f030c020c030d020f060f09070608040f020a0e0708090c060a030e03040e0117070603020406080a0203070c0609060204050f011106010b21010e06040b0103050906040809 83
    0x800c10a080e8003030700d540302c0200c49240b0056110312481004400400a4401410118403004481d1400c010024001d4020007110020541c81e4045000414001e04c5505c0e000f100c046d041d14126103124802a40e15004140c02584511446d0b0000d10303030099401089018210690181801d146000002c4484540141041d60790140e015002d9005a03640e00e0460010a00e44440c00810720705400058141100208084c5507074001244c61529984c50900f218405102410006000c0e005004d0992443c01540c00c40100603c03884000310fa002082910503903980f0300c04045034001c0352100780840c181d001d2407040801003034513040441c01000c81d9401542d44488a442c0020080c2c6250b143c40060701e0702070304261030f255400541486076051440b42c6c0c1010680a08110400c0c4030004200e0350745a50502c0b59241c040d401080050300200040740c80350b81031951582c05c1280d96140d610400041d141580c030036124900e03080ca00a4607502a0064521a00382040901041c2c0d44036102c44030b89610560021b0703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 24256975 1250 24255725 24255727
    0x120209070f090b16030e0d150f0204050904050c091305030307211b0e0a0b03040803040503090904060e070e0c0d0902030c0303040b04050f0411070f02010315030503070506240d0206 79
    0xb181c8200500f01402411503881c0c10041124911308001d4265201e24a070103002d808660805000b00e03250312062621541c3c61840010100c1030502c1140003409030340c02c4a81d1101c0c261003404140000000c03a10300c050303004c4504c0806030301c8401041045002d5600c008105810a100240d01c4900420340040700444013410032007030069807442103044038072a80341c000403030311952426100964042219500c0300c2060791160a480c3c141200c00816000c01000100b0028001000508020b42801559820200034028503281d09007403a00002a0503208a440d038503102d950300c001007215821800da4042c1240700e244501e059000c1042e80c0140080300000d0340c1500c980d03110180140c80c01c0004100401401a1494070782c1d046c802040f000c0c044c03100906200e40c1c204036a900324114020120f07002d19074840d401d210815514401a40a0081c80b04003044520004100005000000c0f00410314540f091080c0d41c040d9403808110000c00c60000701c02c001c052403c022030b1400342040e103194020140010151 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 24258225 1250 24256975 24256979
    0x1080a02100f0e090403030911010503060303070b09070e280c0e010c03140a03020901020609010e060f070c0b010603020405010f09031e0c08030f04030201020d02010207080f07020d02120115120209070f09 89
    0x4240c51380000d56040b4006036588200e2001d1190400a9140c0c1d28005d18220740b0714184403000aa41e030242440261018021901040c100c034020008000204803051884803540f03450701180d601c1018141c034128400c4125588902041c0341441412401030560700e45180ea40c110100441d003032945084101c0a10803d03c3e81d404080a00d90050140e001e01d6070340250307a03030b10b05400080c00c1c6200a402c020840c3c4c1481643c0e1113000e80442c0e0303643c1c001c038840c9400b1007940d18160201d507001e40f0508051304140e002000070031082c0e4075400520982d0020707214000c051811040c12a180c030002d100c05407906d18aa42d0340004048100c09030306481d80542c10007101c603611070b4541410b5901c405640e0350642c400107002c10441d40c05100641c0d02c25841d000840c01e08070036071120303040d51090469601c42d400c0000350b24011580c0315015981070170340252652844519102520780209003403480d0038803800d08044d0000780e065200b040c54049c1e5601070010007050321002c000365000c20340c44c030314501032054030400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 24259475 1250 24258225 24258229
    0xb03010f050414010e060402030a1218060203070b010506070c0306050901090203010f0c090b030907061b06050a09020108060d0515090102120903030a0f02040605071112030d0b030601080a02100f0e 86
    0x825008030b02403054a403e58440c00c0300c041c00c5039480b0aa0024a070003010422016a90100b000c001841d0450110100214540e10840b29810040214403058007101408500310754004050820588507002201c543d980780c0007006058020800c0c0181000d007459400e1002501a0308165080001c003800030600807000d0f40060300b954480940b81780c6103a83c1d20840c020f41c0e60b11551242c000e100c2d1040030b61460a1145440781c0700c0c20280501c0040c0a000d02150382c5490000104134101074108a0820180c1840e05042c03001d8080c00c4c42c243d001559940105040d4035020709180b180590000041901400300341119840c0c01001704803580555003803104003860001505d906200b00303080c0002d035a0b2850700011324400c1b40c81c0030045a10240c0b0501c01845010b030840119060643c00c1034010616031800d42c009400307400e00a00039001404041046d1210071000c0d040307480040360480c142c1b4034a07078840003416035a085088019500416810050603c580208040741c0c0818051034400c80c010700403c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 24260725 1250 24259475 24259481
    0x30903090d02030c12010213060512010303110c04020f0a09050103020a09050409060603050d050301080607050301050f090a06180e0106080c030d05030a15060807020105090d081801200c060a020310090b03010f 91
    0x20002507140d400140208900c03c0e10007001c4049c02c1d031810705a044c46050f540181c0e4880301404001e06101741c640752041b00d910100f00905e4540001402995030b98180c1c054040c2c50f070402d00054002c03518000c0c000c42e40750702070b00903690700401035035034100d00318034150402c0003130001440c0c10b8a64a6a5100100100307000b4000610420240d40721145d4951404024520780200101408200b103c184014172140d61140c1d00c480000100303c5907880192a41d83c40c010040c2042d0388004540841801480003004a5400c031206d08003a10f40204820b0b81d851602c50b0b00d6010b103a43c1305078507070020a4084076050048026641100307035143d002400b508249034012481a06e9000400418944000c01510326070901465502101c1d004c0035103c40c085e10f40000c1e00c111800f5200701c191880280c0100c0c5200f60950041131550074101e03040a101e51200d40c5070103280d100c0101040746000344000911840c425000b140c1c000e081145081107178901c0c111002d0014030889900391f81c55500c4118450b15280030340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 24261975 1250 24260725 24260749
    0x1b0d020d0507021b03030412030e030d0905030d0503040c0e071101020a090f0801090f080c0a051c080c0c060109110d05040615060e0603130f020d0803070e06030903090d02030c 77
    0x20340004041c1032010020f481d00d062500310f150700c1041c4401400321614088240c4e000c6410201c2210710040c010702c0c4c2030303030050703101902c541d0584281c1c0c14886180307601031010707011120103030141c3e46005c0121707004030b4962004503170181400b50003500400c0001003002c04240d03c0102c034900001030026282c07100b403e80e40005c800c6400030300c0c14a0140306944c1d07090b04d200c00400070040200800001c9075104104007440703400c064820140490700f00c80c0100300307101800046500c201500d95185c1c0222101006e14000c03412040000c5440c000a10009808000c48a02418180c0100441e81c81d1003406000383c800e4078040810340400f4002c8031840c880794024103006501c204c00208640d8503002212140314019808103042001442c3c13011100d0721400308a07504601841548140328449042c03080a22282400083d002440d070342c03620050140c07000280d8010403040da5044864469202000320a003c00d03964020a900308001c1c12056240c40713440d6040c9148041c06590a540d0302d2130000300c2d440902 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 24263225 1250 24261975 24261997
    0x15020312040b221202120405030a02010e04110a021c05040f0b0d09240f05100501080a02130e04050c030114061002100609140a0207170f0910090509060d030203031b0d02 74
    0x2546449800c4c40d0184074a099500024040c981402d1800000a40d40c011109020f814418035500c0030303c4c1910350b0380003000500200d03050a46c1e1f588682c00001c0da10b00d44002320b825810200440360030894495000c450850b40141c0032900035905012180382c5030790089070200072096840b10400e0000d1304040f800f4007040e49402c0d140301d0805200450609075220070a2009030f0918000800800401c54180c0c24240c3d04c0c20300c3c1490f255551142d08d48000c0c400c0064031300d54030b428a44009200284404840e01c0b81c6c1c810700c2912401c10041c0c0616003690038000c20030000c0742100f0b0020f269130400c04464103d4104a204854182c4422914107080314041d030070642c221a00c0701000289140c00d400b803290001d100030001c6141c082d01d83c4414070034581c1800c035001310190019503004102680815170b07071720040007080d186507024000e0780604075400c00d105041c06412035000051092800d07103400280c4507050f4020f54035507035510751800c054801c122000b402003002440f0b000c0300b4001c148041c062407415 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 24264475 1250 24263225 24263243
    0x60907020c09100303110f10090314042601050c0a0c0f06050708070908070b07110d08030a02030604060e0f1501030e060a1a120304061805090a0615020312040b22 71
    0xe50500511460000d0f0b13481c0c0844c0d202d080aa0400034002235070700100303d02d1100001d01407006280848905a5511881155a03008500400da00e1400e0341c88240140130721a0101c4d030b0411403000c44e03089c1c0d07501301c582c072107041002e014414516014020031090703d8481c1118070301000780c07642c4410031500260342c9100080c06200800100e513410102d0f00300a0001040244003552808584075100d11680c18020803900414148120a403515074015682983c400c020540f24640424101c0c000d41045540c2071007030703003014800500d2a0586040170b000d4104031942c1c20031903861040c0c9000d0880b1603420181010341c0d500e1211001c003000d200260190048003c08200169403c10101781102481000c0c0e00c01d154901c40c81d1280c090000c221002c0340c0750342c10214010a1108226500e80d00c0b50341c0404d400050302000c00c401e00048ad402a401c0c0c81c80b040c152070340c100c0c2c0540100e03581e00550030546000703120040403a010900502d4900d0f44039082d100d4408c100f901c1d8036405040d103100b500046030700d001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 24265725 1250 24264475 24264479
    0x12070f020a0510031a0402090f0609011809020901020d09080a020909030f04080307020a06030605061b011d010209030d0503130803040221060405250306050a0e01021b07120b060907020c0910 83
    0x200c90304070780105c25002c407015414010910001142d1003648070707802d4030603140080d030009603900605244140480d000c85508040342d407042039030003a5020940741d5006020309101b241045010310284010340708c001c03000f40003221a550030300c01040409441603503107100902030f0050350721451005001800d1090701440d1503030342e00e10502580c804a60017040c00d050905409002c680c40d40303070650b513854021504600130b652605000b10b004000002d142064441c4c0650103100c4410150000c140480003981221304c05807000c403007111a4002590040c400a4905e019400440e44101c06150030500007005a8180c25220882c0d40001186104031507641d00f088080000f030040c1400161070781950b4555021b000d01d1500000d998101a40c000100015030343c034003003140f415142e48008505003441000310b41d50050301459401000042c0c0d5000a203208280e000704149050885110700c455006800100588800b81040801e00000703100030b0451182a4150f081c0391348051045000b04208a240c4e00018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 24266975 1250 24265725 24265751
    0x2090a1d060c03070507030c021008070215010503070501030b0307090c08040209011203020a12260117010912050a0c0c03061a0405040b0f070905130606080912070f020a051003 77
    0xd03025001940c110300c04001c015900e000071a035228901c1e240c199541c103494903050743e41007440c03134003e500f00d00310000400c492500101014003d1503690215007840001c0b02491010420900500b505070308459801c200550107030f000003900b580b000b4140c8825a0b00c88481404480b581d00c500d8001550000c148010750030036229142c0034160816150171108000e0710040e50758900c0c948006c00284840040500b0719209030340b150201080010000300440d03901c081051000d000380112403010f40340c8600314400000510500c040c0b01e03800304200c10f00c280003003019140390300a030b40f4034000d03c00102a100e001880ca02140e0000e10702c540380000314031a44040c1d681c1d00605080c10f1303074001c5182209000c041130f1526900d65000450500d08001903403550b90454400b0b0a541c0660b4000020140700403540e40c0741d80107541594881d40d140601d80d95240011903a0300882c1240112000c41003043c1c9000c900740b96410886e09001801401010b542c2d0030104260a4000ea42040003d65943d4168445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 24268225 1250 24266975 24267011
    0x70b0f120f010f060503011a03100305060702060709060e030c100306120807030f03022502040605060c060a0b030610060e0103020403020d0b0601030506011404050f030c040204171507050406030c02010902090a 91
    0x84e1071945082421903060800803501001003902002617a0004000648441a80c540d04000f031a4480b0580b8213504100102a542d104152000c40105e6015040414480e200320302186080200070b0003403a16110311010b20403101c1d400c040000c01c01d0f407171b48404154083d4191888022030b114100320f40d0f03103166a0800030040f580030803280c0f0416004010b0070040c1d0b40b80c010020751000740400c1615001c1e0151002130014129a48229040440810300100e05100810254030403210890705022404030318042544407401259944102c046040c4184501c501c80e035000b8585d88018140140f5041e16078001820148100300e0840b0000310007802c12200d564103000c0c80360019070030b09001c410300f6000c1c1c840c0d10b201c1c080d90141d42e0040076400f0301e8100e2660308001d09415250050011035880c2d4807191008030b0702a0314404950705204828651514200c13440c80c071842034605035205810141004001c4010f00f0151141030215901c1c0c1404001590340c189003d40110401040011100d0910307240d0414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 24269475 1250 24268225 24268229
    0x6040309180203100b0d060302040501170708030906220f0b030405150c1e04030804030c0e0705030402010c0f0809090705090a06110c0108040213050405010903030b060c070b0f120f010f 81
    0x6114014020b0056030940001e031344098491881a20340c5608543c5c41000c010070039070348080d501c42d003080d00002c0d002c862564004d078640c0c034590a4461080d1038045990366072241c1f1055a070091010001c3c50622941039440c22030b40342a40c0c2c010074819580d820391078a44035081c1c20444a4880010074042000801c10081001c402ca0741c90740401854a4490540140102c2003403110005c49a490842003036600720464018590060109407540c0c0c03203041401440c0218052080810102408070700301c40e000b141a0f901ca01c1d4141d6038421080410340c1d03000d000201144088521f02028003032122503907100003a29128031456901c0c0c503141c1c070501003005240d009641c0300205110703000a880c8203669011401510f000c1080c00d1007401ca84491010540300030484102e180c156107080140400c00c0b02c19040440ba4602a0380c003407042c626100704003e403520500f03000c01c410350300c4080100303c0c9016032006440f1006607044401d0420342035505142c6004001c0342c0200b8803103451401840400501c40751500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 24270725 1250 24269475 24269519
    0x10e060a1205162403020c070b0301080c0306010602030708031302012c010305070509010903080a0207080a080306010206010b04120b06060903010903020601050306090d051b070902121e0c0a0c0c0806040309 90
    0x490103840c084c0a100540d45510ba45080580016401c15200d20070010301d4010714a2541c0d06949603901c45515441751010103486111b40181030002502d41e1001040c0ca25003a0050500780c42c0d03444055100c002440c4114089042c056001465011041c41c0b07442c0c00100b0010a10307501e48050503500040440c1c2008188205010090102c1443c80e680003840c04183c036032060210380d8803007070241c003a0302d406801d9100c00701a10030400791100700328119024501480c0203808031111070b41c032003040d001140100c1c0139207441a60801a07000108514500c81c980124024094030b26090f43d034008a401d44240c0441a80541d0000c001080b00e4181003182d1588a560240134010000c0c00003002003092003070780c02c400314100152400054124050000c1802080080700441d0303100340b04002d184044108442d030380307002001c1100e290b08825900082074440e100c8100d51900d0300c3c025410641c0c800c0c07150403081c0c40440e295000800c803200d0030400300c0d011310700a132290700348245441c0702241344200004c1c08039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 24271975 1250 24270725 24270749
    0xb0108070c0b130b240301020f12040c03020402040821070f030810050303190f090302030705040c030219030501080f0a050a02090402040e12040923010e060a120516 72
    0x49041d500400121000740d0244000d03901d902c070700045001440e04400d0243c000e5507403078280310030450100c0449520042c00900b800103c0722400070503080380134086041c000742c2d40400ca00380c1440564040e040e80a4496501024820703140d401090480e0011b82140d00d0340e601158001c207041d587d20340041040441548840d180040e1661005030844224800505000b20000802d4102c7d203103682d03010103401d0180c01c1f41d4441801d5141c1404582000e00203c2c0031605200c502d440e601d119a100009072078000c1c00800b0040d00d0042440020318680701d900c001c26074280504450426004200c0c40c90101554021070b0340d50501c11000d041181c80c01d5501c0b07242d8409020840080ea01040c1506400e4040311408501d60399400814007408000422241c1806015041c0384d41e800302d100508203031042400c1c10401c10308070218040c00300c96952071051600750483c0042040107854044107601c200041c01541813a0342c0c3e95110040c038005000f00b12010341006042c02e81c600300800840009080240c604 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 24273225 1250 24271975 24271981
    0x30e01151202010207081218030c0108150406050402040305010911180a020d020c01020a0908161d04030302090307060825050714010209030f0c040e0c09070509010915050702040b0108 80
    0x160301840303031160015066140380341d8019603000f8000c0e0002408a00d0540b12414800c140700c43e95a40310f540c61031aa1490a0030185140c00c000a00c0e0f2550726060712182c8840c0c039108a42c040c00b5200900d01e940c0f05480d2400440c2c246c540303001410045201d0400840c0c04c078480c2c41d184000300780c10322446004074060044003000c00000f21003c1d0b00440c81c07900050780c460b90400882c010b842020905100d035800000c08a030340c0c0f81e00c8546201114485826200307050684004807140c01041c0c4144a40b00328000540039402d4814550030b500184642001454000094086403d007102070380a440861075080402520980b8031303c4032030380c04e51958122030800030385040c007402c0c6006205000d8455800380e0221042c42000750b04450007480c000703045940c80c08104045036030350506614828003407418800103544849000401004040e0f00408507a81caa494450440d015000341c182c2d18108820b4240c0085c00c8541b2010002e56082d090b85d81a607508050300610058460180115041024030420 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 24274475 1250 24273225 24273251
    0x80f0a180f03050f07110f03030c070314030412150b0609090a0203070c15060302010e0301020306030a03050c15070302041401020607140d090203070e0f0f070503010303111615030e01 80
    0x1855280ea0121404011501e50708003102c8074054401044a00180016904180219000c074808000c00480b03444104403054030074035442c0e019411030f0640580c0725140a00010300d0651607103080e0760420003201d00f03299451021b1a0391101d038040030ba84480c04400184160011070284580849099991901d0001c83e0710108618000007802c3d000c00342d83c0407011580785485030044171040c9811401d9070700315028081d0b04c0700040c040b522049021991040d00c0c46460300701802503d1150600074050510f48403640c900751030682c05503180e1891030103090728603040c00c4d400800942c0106141d41c0c0c01a102e03410400c00f5458518820032060641d80b219040140050b8020300c034180e1420145000d07a140ca92503030480c0082c00d0800130007580740c001d0300f00120305400c1101c1510700c034451611007444140c40b100044c0048100640e841d00c0003403420001840441e0181440640d50b09010044850420000b014408480280c3d00900083c03100c08403011201c1c0d03458040c50500e01d800302c00070070440900703042c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 24275725 1250 24274475 24274511
    0x50102070605160b0702100903020303090705040614040c050f04030b0105120109120f030f0e06100509010b0a030c0903020d0b0103020a080f030910020a0206121009021206010818030a080f0a 83
    0xf100501c2c00442800151050780300740000d00b01e80401c42024010314589240181d1a500100c446000c070303210340b590000d014502030060008407041c0c0007a152081c001d40d0144005005801503240510808000c0c00c031080d89071200030720003140106900451075040800300a01982c504d84c1e00c1c3c200d03a0412640c1c0c0b0108203c2d802003441c80c0c2c0036003896819152280c2050780900101c088845200385403004000504001240c180d1103628520400156203844a04000c5081d10030700030514000300c02d0000d110750501035840300c2c40780e80560602071901956540040d0400d140400100c3e000c5030000010421030500744026009081c0400282c501000303100300542d568003030400030701c1c41020080806040030707000b4001441d100744c010b46183d9039a8000d811030351410400b0381d8006101c0c1e0f2083d0000a01501c5442620300650103a14056240c0e140c07200111080c83c6c01074903030340c2651b100c802d003c0381c1c0090410091111509540310580146001380b0400701401d0000c00440905050103104021446049 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 24276975 1250 24275725 24275767
    0x20304111e1207080106030501020c07050301090503030a0902060904050c090102010507030e0a0b06241804020403080307050c0f0609010b1306120312020c010c09090f060e0c0a020a0602070804050102070605 90
    0x5a0a01e8000c0800280b09150a111384d202800a5203401008028003206400401c064010a02298082d95030741050608813000b1940c0034105030810300114204c06001c3d0080310149000070f1a0509110590000404444c8252080da40038100040d81c1c00b02035070280039440e030050881c1030070001d00021508080d1200a00c81004003070000c41000a0300594a8040703d42c0043e000000203003c401200160f040399a205088003034141518610341c0040380b03482d00840302520340c00150682162560b00003654290000c41c0c11400a0148130b240b20241ca20400c011880f802120b00080b400101c0c0c50180880c10681a00000703815040c410300388041040102484c801c59494a01502c1000c01c0d201198002e004440811099501340106076001c0c3e0b901c000b1400541d0042d00c010881030030001d29000882c2c03454452403130601c0004000038850103107600a019440c1c0c050064428101d00d60b030b641d000b26030180804440340000030605001659042080d10064192810518a003d0324443d941c0d02d15000b00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 24278225 1250 24276975 24276979
    0xe0601030b03060a0903110102070b010305190c0e0402030a050a08130806060d1403040f1203030c0e01080712020408011107050106061d060703031e090501240504020304020d0c030501020304111e 85
    0x3030005c400c00c16118101c034442c10107048000311b4580206182c5005508020312007500e00d80702e4a20b1200700242d6885180c179050b54842842483d08d490b10420282d43c8900420503070341409040507100100d00144100403410344a64a40e80da110000551100c1d0325486401ca814680d2040d000c220142d01c60980d501d0096400105825103800f8401c02c840c550b200d1900318031b0002c0d0402e2000580101c0c42071a500105201c1d84044c48403010b00c1c14200c40644d8203220807400a15010b003c5a0f40324001c8030340c8541c0302c80c0480c0140c81c050701c2c0e0400500b581c062000c4081c46650016a59041c45030078824074020780050318010040310100f2084114020b00d0f0304419104040000310142014041d0348445541e04005000c0098560030800000c02000164415500342d400c000c2c030328080910144001d0b0002d60700312420301020742031206000003504001d108070b170041d1007a4007080c0030400320007010000754403c0001581e45d01d010300d0304004036603869600c540110280c4c00b04660b000c44201c1b80407090101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 24279475 1250 24278225 24278231
    0x60c080405130603020d0c050112140f090f01021605120702130f060e010b070201020d0f0f0309060609110a0e04051905040c0306020c030a1103040f031e0501060608010e0601030b03060a 81
    0xc2c0c200054000c082c9076100035442030054140d402042503c409102c11100b091721807c403510f03204602c41c0295a01300d20000e441800c610001510351210f12000b5801c428500e048509070010310103414220382c0a4107a088090004062034020010100072200f003d0b1510700100e810a020b42d40070030000d6600c03400c003401c1507483c2c0c03500a18105080d03010390010865450914403950751601c1c41c1107150b00031034043c3c0c014002d003804030904501031410451841c6466070b40442000c1080b00c01c800800c0b020100702c0e030068503284d001580300c01d9401402e00c80402c2446072599800702d41000780c2214032a403074050280341030404000074840c400d482d007401000a200046004c1c0c1d07440c038000303086142c10703000185079030700c0410001083c40002018006818441e02c500e0107802d108405103541e801103110b207010040142e0300034400980448a001408006040c94601c80c01460350b845096903419006440003807100c40040000c0d03200c117441181c2094080c03c0400c10180b511000c684c031a00001c0c050440951 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 24280581 1106 24279475 24279499
    0xb0f09040206030604090813140108070219140f0a081c05010e0703021e0301080d0f0e01020a02010e0109030803040803041218060e010c0506070201060f060c080405 72
    0x78000309800e086550b03036010000a4002000200c0300c00c3c0f000d06c05180c044111240c0003002e03003a44070b030480c60b003071a00e0001041c048000b0060b5045601a09003c5403514240384058510381e0843c044030401c800000c421842c1c00e5403c0700601103441000704480611004101030071601490285400310500710704400f009a65082c0145d0010040c46804105800e000c2d50040000500500d01095a40002444503c1941003640181003d80180b100c2211190384000300c0340d03110b401030900b502d034000400d00003981d444096030001c1c1408182c0c02d0901d403580c02035000c0e000859010903590b6892400707251600321600181ea0449450043c2c080c182d00a600400c482c00c14030300f4003110311002a1074034004030b812024a45005041c032014502c00004240b062080911500c0d480c1c0022940d20b00e03003041c0d888819840d82c460300c2003010000d20341c400642d0802c00c44007164000c5441c1650f0748 = true := by decide +kernel

theorem cover : BRFrame.Cov 24100725 24280581 := by
  have h0 := BRFrame.cov_init 24100725
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24100725 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 24100725 ≤ n) (h2 : n < 24280581) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
