-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0713
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:17:31.462977+00:00
-- url     : https://prove2.me/submissions/26f556d3-ac8a-47f4-af4d-c95845656d85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 128057553 ≤ n < 128237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 128058803 1250 128057553 128057581
    0x1f08030309030f07110d030206060108070e010e120106120c15030203070804060c02070f08010e1b1008060102030708030f0402031b030307030c020a08010207050f06090c0901060c0201110321 83
    0x1500c81c03103801c100300012040780303e40b004000d4980304c3c4214000d80d5440501051200c2c0300314404402603407101c0240303e20f66811101140c0d00c0303403451810150000300000001d00010800300700c02d0146074480e0002c1000b850070740181c0d001e4803441c0c9004600c4901410044601c1c401841800307250710340880d03040342040c820f008891049201d40c0300c811081d15986d580100070440645000e045000ea114040784001014090b00c00815591001040c0c808000903841e052808207a500401f1001075000d804441d200c3c80780300402920141003161550341c81c040141d0131449880740050005100000704500700102c10032143c091402071f0b0444100020a407003021078103603641c903002d5059100380b200c1c60010340328100f100d202c244058000b030005551110303031509a8002e00c034200d400340c000400d8450880d90800405601650140062013402c0e00000400d8042070103014600402040900840569000c2c500440b1008140c0003203a03520b00c2c2c40c4a40007510959003404080d60b03d40b00c004180c84d01d69200e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 128060053 1250 128058803 128058811
    0xe0f070f05120c03061f050a090807120323030c0c0606040507091203020c04050a0603021c03090b090126160305040206032206090308040b090607020c13060b031f080303 74
    0x400340c4685480326500c50503080203200c0c9606c105209010600c190403070a0030148072660ba01c3d400d0700c44140d0f080240070358100e90041009607100c1581040b4004000741090301e96034050a1501071542e8241440c03000c064034000c0000040c500005020307146202000428031200420160342c25a00d402040200b50350b8140d90740000030b03220345000e00800b40064905442c26110b80101c44001e80400c0c0824240c500440c0e1131031001d42c0d01e100400039401c0450621403002d40b02c05d10341140b040e0654014007c20781c01d00030350000724008a104075080e40581446440c4d85401c1c14405100c409003415072840110481e202e018100303c2065400d04c090090044500495006040b14290349d01c1044805040c2c00c40c0c100100207007402840300d8003040c3e0702d00c02c5450b014000e961f4204203103494101240005409042c854056000030200844503038003242030300710ba5004960815070710b4018500200540510740184180307010000500194038050342750035003221040c00e000089140d462a0a42c0c1b0381c04115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 128061303 1250 128060053 128060077
    0xb0901020a0311030c0a060b0a050621131509060b1e1212030115020606121902030c030d0e040501051c0308060d08040306090201082d0c040e0f070f05 66
    0x640c0d41c000007401490032401a9404200322400c100c0c0144103903140240039107007540c071160703a5000c40106081040082d03021380010303100285400303000988c0d0a411510b07551104500b50001c03003c1440700448210b441c44454110b2030003201203500c130741620010700f50024100d40d00c6141500b07801e4182410540110440b1942a111074510200030620110031100d01d91100359003d8104520700049110300598040c1ca6148040b41c903000408802901c0d1150140031940300f041e0728009a4045000060000391003030b6020410031002c2ea051020074076201009a05503458015029540c050b254800122042c48501311024080d0b0f982c0c42c01804908000514156117411540c000400840d0081c85019000031024007484601002c545821019400980044a00036140c000c0f80e0155a44000000d420905240d0b9240c0c0b9500540080b54401c040700d90200c0303800c004d95000031240c490600c25540100060f50302c02c0014505804908801e030011a0b1090200340f00340100f05149201c1c00a50b00c420b00301d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 128062553 1250 128061303 128061313
    0x30210051b0702040207060e01020c0d0201140f01091802060f0d060b07050a080c1f020304060b0f09131103010c20070f090b04020910080106090b090d030e0d0b0403050403020103060b090102 83
    0x10740130700c8080c0d4050201030b100c00e030b212140d10a807840244010841c00d60fa08000d410b403098170f6a002825108803031001d0b4110403460050260488501904a046446c1c1040004120300700703000d40d6103140451701000e5407240020800c69040001231004150305d60036410b04100302c94440e01264982c1c06501805803460f4404141e07440001c4840c002800b01c4004001281d80d540c4140c1031072010900700b059020080c80c0c01000f070201b040700713030b014a0502c0b0313070103d44d980c0c126407000c00071440090703008003e0040b40c4030000205080c05141040c020000001400a00000300c5900d801b1f03010b103081d050000d18645100143c84040100071031140d0940b407038148407800c0e26180c8070311076020301007078039165a21590801c004d403101d50300d619030f0b1581d20030b01e61940b2a0380d40c503080d8060000c8050350f00145030742c001007100a03180d544031003120041652605000440030f140fa00451941c0d10000c000030009411801440141604107026004480c0300340d9082c083d00c0c1d140c00340d42546001e0354400c039025a00c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 128063803 1250 128062553 128062567
    0x423010815011211010c0b01031a06040531020a142b060b060c060a0501060f090e010902030403030204080d02010522031d040e03040b190203090607081303020d030210051b 75
    0x40c2c2c0b02c3d0a134240700501d0310100151054440c25821034080e40300311003a81007203000c610550340d80041c0c1035221004490801c5640b0306040ca1501044a0a4049030407104c00e60324407243c1c40718011400c401e1900548402181502d41d4031282c0141410100b0308c4c0704150301200000407441440544100302851401015543d0941c1d80c4d6401404602c51820380c041c0091201203e031007003c000c103034410707552501e0100c0c25514240c40940542c00300301204042049052051041401c0405041c1c11101130200059807940d460408400070b0041ea000b40b01140101c020507400d0580c150080c3d0b001b2000280d2404c21801a001140303509600950010089149441050b1024000f0b01d41115a803201400104840e003034a070140b429984a80c221445207140840d203030b840060398040c00682c14100e40000e519040c0543d0020703804d0300400c00700805110f000108a114098840b00c0d02c801541d000d40710030204240c514000c1d45801d90302c4950422907280000240e02c0181d04120b150349101541501032038104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 128065053 1250 128063803 128063813
    0x90f0a050a02132c07150c02040506030d270b040815010509060f01050904090503040f03030207050405090c0d031404031505150a230901120308011a0a030b04230108150112 75
    0x381d5540885890003001000201b680440da03101401c0c6107590340d012640d81c0d0b148100000c540000c1d210034003d500c0707000c242c07a0b440e4024110118108000d002c080c81445400080f803070300c11840e0400c03810720002090010702d1810001d05141d0304e10502c4820b08039a83c0b40c205110449000700c03180d070751080040c900b88040394040ca00078081c5101c040c04c040344400b2036885891950b03101c2ea014480400300e410040050603030600424001c0e0000700c0d01409103042c4030205581c0c641c0d00a2076036100b01c83c1d8410301810180031341400004110380032041c0d5283ca40c1d81c11b11600c83d21a05400f03079003070303401d00000481c04403119211080005004086000a80c1003843c10f49012402180d00e00f94200c0c020aa1500d030780d58902c04600a0054032004d03111a0914600200750707120690080c2400503640000c0d000605a5009584102c40c1ca071500060030302c80d80000030081c3c50340043d050015586035403020310a10a80b03804a0590341000c048610040044200000c03c090034400c10a8168401e294000011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 128066303 1250 128065053 128065121
    0x11407020f0d080d180b06040b06070b01030318080f06070503150405010b03090c0618010e040f020c0a0c17030304021e03070603020a03060e09030a08090f0a050a0213 73
    0x60001e400c4401031260880400c40c0300580d644241d070100c038080354554180c4502e010300b42c048103e100e0340d40c141812540d01c01c2400d00004d01740a200d1038541072440340546681d015100c100b0340201e405281960359040c0034040c0360b03c50104581800d0ba4080216104200081c6000b240213114000c00e074a81c2e41001c1120950070217410460000c1d0350b582902d080340d403540580c901808502c100e45650b410700e0003640e8a03004d0300006040c00340405220b0714004603200d0011240000080c20011103504039800018001e04482c515400c0d01440420400703400c0b070000a01001a0388200140f01e90f41c2c1e2100502c5003080c1e0000c21006080d8802c00c001401810150230524021445440ca004002880c000203801c0904d250400c000183d8086a030b840d081d9814081d01d4014001c185c565442c03420500c480c140c80e4403809031450140000b02c1c001c911102410858441407031868015a69003205610303000c7c2c0c507030440324816440b4040300380d41407000b04402d208094407036400054080d0040300d5a03259107449 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 128067553 1250 128066303 128066317
    0x1912020c0a06052b0c080a0b1909021c051e09010509030a1209020604081b1e04021c0c09031a0708060d03020a020918010f0b030606060c0f0307050d080702010b0114 72
    0x500040744020030444d0240101c00300314040d030702c0c0c1030b80d189040c182e49000c485881d84120711550200748152040c44041d050181071394210080540d13034a0f003087e800d101106409820382915403500c020000340700f1403092800c4000d0301c405c610031001e40320035405509070742040d80d102c803032034008000505003240a2558001032200240b008100c0e601682c00062258201d42d004013003d0b0030900d10305000e106401c141c08070034074048a2050030620189880d8030800600d110b014001c2e40e002408204c0159500050f46540c4410032041c0110f908d89400145040c28501c411503005003d41c00d58054422a0f0740d48070b1042c16a51340d514815a100c004001400b041c00f4025401e42c020707501003102689601d0b802170700c10b04c41000070b4880d103a01d070001c590858201e010b0180302980380080c1d001c1c02d40d801050854001500b100c405813101c55082100c0c1c01c01001c0c0800304132510000403428100700703021171142030b000ba103074486008070341d2814426401e032041009800e0004080c100754040405c4420050b043e1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 128068803 1250 128067553 128067607
    0xc020a060e12031216020a0b0106030f1b09060e04020c0613080f0c0d0f0f170901020405090a140615070303050c090913060b0f090c07051912020c0a0605 67
    0x281c0e04030019a90304603403080e11481404032800082000c05081c842516100c88050f00c01080b00310401d4980444c0123030180242401c1517100d4814040821094210101c11743e02008100c1080ba00d400703000d008000e8500c502c40118580300f54814071464184203540f49080d81801a110950320411211514891602c0c2110140c4c7c092040c0c1d0500300440707016022179039485000b80b206d40c0c0700490140c414005c42901008100304e0316081e407641c070703813200049860542c01d04494070b0580b03030b035a8064003a004e55001181c1103c90b10b41044180900c581003600c43c050000e021607001e880c3c4a00b0700160119101e07001d035800c20100080000248207a000d183c2c49026200840d003070107880000100800026182150310045000300c030710078080c952241000f02c05081f101c0740f405005040c0400d200314801001401030fa1004a80ca40c14424207014400c0c80185a04c070500c4004981c2c1360403205039020b40e01d9040144103c51072100503041110022043d11850740702c4a08000240c602c03080081202480210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 128070053 1250 128068803 128068819
    0x12021302070f0b100b03010b1602030709020a020610090203130f0c09090f0c060234050d030504150206190b0102010b130f0e1204050111011509020c0d0c020a060e 71
    0x1203451420307a10442c030302c41d103c001d906007401d0410303d140d8500d640102c14641c3d0200010811808013804075092002c48421650141c525030002138249900c82d40420540c83c000114102d51a5010494511681c6164420040580c5902040040340400c44030303186140540030103500842c240840c0255503521403c00c2c05038003030700c408402040e65140f02c0100d034000401b0782c5080c10444000c5040c03001c0c010501c000c0c1b06035585800d6101c0f1960840300d050703a031030800e02e40c42c0c82e51400c0d51503014040c0102403c0b00c007400045150080075580107200c0c0c0241d8240142400400510100d0f4040c0150400d400e4201c0200e43d8420700401085480354090541d940c501c003280722a00c1d240e03403080c000c07a200e840015503001c0904c190404d85070031512009984d0481002c05125400742c001fa2010384d0b00c20b18110f0440350200600500402021303c064000b940400170001d218440c40d0010300d55414404140c90594441c03000680c0c00e146142e4000f507200a440d2720a1203040e11071010440d0990300140068 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 128071303 1250 128070053 128070067
    0x90c07020a030303060303110624060408010e03042c010303270e0a0b040e10051b03090a061802090a20030c0307081003080415030207021011010b0a12021302 69
    0x110704080c2503004801080d280c40b020003d00d904030300a192681c2c001406400546483c1d04036904c1044c070841c24807465024000c1d000c84a03114601940c0c00b50000800801c105044c0c05100b40c1e0700c6c5c0052090303881c0080490406519030354107046040c03007221039291144090f400c50f076041c0c0b810402104c0c050030790402c600d8055500302e00340c03140d90014000030044a0950070011514000d5403035100351107008508042c242000842c00248030152801d84071400100c1d502c403404d051155038528206540360001c01300030304c40014004070350141c0e16072190008004540c50b8448040180701011400703903021580c1800a0b61101440d0800d01f51003014060000c0700c10b402c0c1d1001d03101ca030001d803402d2135a500c01004004045070004900c580116a0542c0311010519561760241584601e005078001e9100030031844070220300079019504207940c001c2441040380b900c803000802c014120f568a000f50b41c200307075556806090154817541a02d040800c4000c0c0610388d9000e104454102446412130325900f00000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 128072553 1250 128071303 128071309
    0x3021e031e0a09020d0f050c03060c190e0f04090602190c02031e100902030111030f040b0610020d050313020411040f091104050d020102121c060b0414090c0702 70
    0x80d8400e1400e003048600c844400103121807980c000034001005185010b290300302503034608904891441e44048440700030300040c81c1150400308518810f940500c5000180914492088094819800c0208998202c585060406c42d1740107284221070390020f6084113401c0481c1440c0d0407800c0082d004400c0540b4110ad00c05400c42c24000110340c220000f881014610300310325051000031340010440e100d460b083c905c1018035540f580c50855160400a41e14203643c000c540302034015244400c4800076058907440c108d1484100050221012919442c144d00014020314028180441c00007095000b4140314103441c0040d0380381d51016200340e0b0350203601c81c010300c01650f4501403051150342d8540c149440e40e01c1d050748003205c038915801600c5d005040c60b9802c18400c0d4010280c03003c41d04220343c01c1034002540d00050327041080345409581d4520300040c5c20a00a0081c20100c21a118019001c010960341c440c454074440c02940911031940409503a03548281c60018071250300541c01d0039001d444c1041035400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 128073803 1250 128072553 128072557
    0x90f03050a0c1b08120a020303010b0c010f02070b0603010c03050c030718180c1205130209060f12030408070b040315050c04170604030e01050313020915030105130b01080a0503030703021e 82
    0x4140e0364a001c0101442810020710420107040d040340300c5ca5082013518400039440e80014014807079990340124240d940d40c00c0940001940403202e00c4215681c1210b0308004411020403134405002e582805075080c0400c0c440e22a41d84644107030542d250544e10ba0ba5411128188900b401c0c42012240e440089040060300e1130341c1c038a1510f1070400080e0321511241c06021142d4800754104418a03290400000c40030100c400380000350704a881c0003007035803002d00040b4545150300072950014621040001080000001402550003940466403d1075071450700181922035400001d14103c000790181c52040041d400c0340b0b8000c40c2c4464854180740e11468541245684008014a650b229405000505400c00009141c4c1e4900386810b51661030a20b080226070214020028001d051740c40020b48007501460600b84030300c0b0010028041c0d0306000c0300810700ca56140b0f000ba2003007885c460000484070800194480c803207901a010310b046549a01d4141c000f9040120703220404070030301d0340b1801d0310307110a40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 128075053 1250 128073803 128073833
    0x1003020f010339050a020706050a0c0812010504061a1c1d0303010905061507030c0327080c09191104050d0503180604060e040b040603080307080702060604090f03050a0c 74
    0xd1864205183c07120001c500c1d00450b0f28403092010400c4a2a0340c039901081350420384600f030800940d101c03002c0c03000300d030404010b5101402c003900c00b140c030080009030007241d64100c3e0000ca9050002c140c403030f9101d01c4540d210120004060504002c10042510001c0202e8030082050100140d550880403c071080c40b100f5a02d00700359504000014025845184241a04142c0546070015805c40000c5d10500706d100d0003402a09200034404e0000404bc842c10001d03443e00740e030b80040342e0120207003c2440e000e00014040c4800e240204140b8054a003010302d1f816110701e80c5480304c0780c03501c0100c000b00c00c02000e412100d000207810030000400c00752071703079000040c07681e224600842c1c1d500b0300714440340d41000124212507c6503c04000030044142e000121580121045600042c0040d041001038000d2910f903000410b505408000c11442ca5000710040f4814003960b001d9440d80c2c4e07039580c00c0004465100345c00030310070412005048042882007002e0b001c5c1c07114a090440703800045484042c90600144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 128076303 1250 128075053 128075111
    0xd05010905100c090303050d021b030c1e06060901050910090216120e060f0901020304180c091a03010620060a05060a0909050c060c0a0c030b0103030806091003020f0103 74
    0x1090030040c00b0107a1040300c42c0c0b00c4240c54440901c90440c0e9004160b4826074413498009600801d01210b20020a907420740e15034554400c59036141c01c1e91020b591902e400d40008040000e00c20185600d5001c045496442010002c00c0700b01d1580c00c11003002504130700a0a00940b0a6403010003142c0115184003c1022101c2c1202c00110710081e0300c1c080042c805540036a02c1001403c7c0100c8925031580c2e000c0d940303060700f403850b070607100c1d455200100e295000d1641b2040511140400b0041c1e41220b5174401c0c0c0e040621952501416a2101c41510203034034000d88030031840e402007004100481c814080d104040022400141d0292507080180d450800103803402000e0035a21070a0100074902062564000d02d8401000d20024689440f25900c651011008501444001860308003140301070014200344d40e8011400703030704a0789900f081c400485007404100c010031240c0e00400c010f850a4401d240c442d070000c1c00100c0505041d40c0c02d0051000f581070302031303041c10b0b11100c0b58203000c05028143d8102031284 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 128077553 1250 128076303 128076313
    0x213080d0305040c090b010e06090d0c030b090114040515040206091905010801080a05030414010e0901090509010c05073504060507170702030618031b03070c0608060607060b0d05010905 81
    0xc4c103200460142590080b8001e40c43e100e04180d040e60040400d81d40c01100b140c5030364460140b00040703407035440250380c010001040b111011040183c40d2101d24019113040e4000c05c084040ca40819410200564000d410340c0d00c01411101c0c1c010f1a40462940244090a098104211000440c066060750310720314070b00526081c010711082d64010192801010140d0040486041e182c41c4c081c3ca84c4110b00801700c42d104200c4d083c0344164000c241015501d072002d82828025a5594800c000812050381c4059080d42000c0c00c02c4c01d000d1041d0b0941c0c8415402080e001030320204807094078a1131014484140900111107205901000070101600003404162210b030f44d280042d03c3d103d5200012245202c650050600140f80540c8001412540c811290b040c41d150300801c101c0310924502401181490440c00d40700c0300b100350f00740840540100c510401c007a00040d0740311401920170075804c603030b42c42e00030b2010f00140c8041490b1760050303082c141010380502040851030715a51309480000303000b62440c1d404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 128078803 1250 128077553 128077561
    0x50a03030509040e010c050417250305010c080601080106030519020a1d0603040c0302060d020c031306020d030e0c0105070f02090a0203180a03020304091112010611010f110703030213080d0305 84
    0xa4050b0b5591101e031003000308000300c01c50101a0440c000d03401149445120352141440c40d910402001c511841c82002b90902d04000105144c1d42c4c80f05404126243c4d400c01c2c0010030914011619680500d00c140c40b40f003420782c20b20701d0440090000410074009002c410000702d803c4500352008028003400c41e40c0d9480a580001860403000c0802205940205420400c02001c0b4030040000700a8940c12100d0300c2c1e0300c15060f0549000b03030080c100e404c40c2da03001c0080e01c05c01c107402034091801203620036000e8500303406060009600715200c00e50000840c0d002026401c0c001c1d031040c4000c0004c3c40c402c14100045000c00e80104070704240488200310110340c0003041c41174411075032510700b010f01e0b5400014142e2a1065030700030b44a008903c00d540000351125400e003941c1c140701c0c0035200540c03540ea180900c03035a035400c0010300c0110b5021200d01e065107000c1501c005680d017801800300b52808080c21516101082d94114000d50000030f603039140c03482644000c902980c00f408940c0d4404440da41c04992424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 128080053 1250 128078803 128078809
    0x522180c2102060f0c03070602040e01090e01090201080402010e03030409110301080715020a0312020d02120a05070203041406090a03140c0414011503090503090d030305040b0619030f0c050a03030509 87
    0x1040074620040d000191110010f9076104110fa0380280c002c110fa42d04d0b4003002d0001031850180b0b0400400e907038004240454500e0001d03002c1412103441000510500010b050018205e600003c0041d00040c0c0300000100554040c041c0c440d4130040c05412240b500e07965441400c1111a001c20603230640c0000001081000c03010400100902070f0640f10102c0c0305044c60000c1c2da505201e49000781841080c41e8240001d10305079047d1111400d0101096680c0c545035003001c044c081c4115420071030301d45020081074440d4400410384056400c0c10010b207059211040030000c090b0890001c007a8070a020702c03008000a9044041d81003004104c0c00107040d0106260100400d07a017102e4141e11140d80000d00411103130040c0000c0e615045071900300003030340385d4250802c2ca0442c400e42da1007a40110b50001200c0825505601942c0308500a41030b81c8816201c480c2003140341502020101c005002441081c40418481040701030124400c8851840c031541da4004101c012400e6401600421404a000d5410381 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 128081303 1250 128080053 128080079
    0x90b0702070501051918080d1d03070605070516030308400c0503060114150306030303010315090519060c0206060616080706051f080105010522180c 65
    0x240203800540116414400000d1281c010070400d008030510f07181c0c03a4450103005007502012420001140105503032174404039030f66081c01407000c00019251740110144003070050300d0380040070030090107455071a01d405401c071800d8000200030b9800c1e00454040003030304240c10b12000c000314421780321801c092500c40100c0c1c45003c00c0360352840f00020300741c50403003c5c0c2d00034205034541c0760320f0400d02418500b000c4c1041060180c40d07400241d018401e80c2c001040801c60100000b11042c422152503059400900f41488a4041070300c0341500350340184018000a07001145c0801c5a40c40d12500140d64401030322501e141c20a100600c1c0e54125079000f90400f480490b0189042d000245c1c00185000c2c20140c02044032842000480301c60700c80e01c0419842017000d540d040b1040c0c2900168280800e04100c404010b40c00c500000c1c02c008850018800680d00d98180907050407203400400b820340b40c400c80101e40203402c522041c04080141d8400040038100e2103802c1c844403450049400c81021800c00f40c204ad541c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 128082553 1250 128081303 128081311
    0x10c08070807050307031e141603090f020409260301050906010e1f020a060204091d0607050313110d110a1205061b040f060507020108060607020609150f0706090b 71
    0x110200c8200b108003a0844122508110b05150029020032074080f07040e40207800882003000d070740c104100341c201103100f45002c0e4002d1504483c1c001d03400c0c429100c1070b412908403040003411500b9641c0202d026250503070140e1b809a0041c0341441116004079450500c50034a201000310503000400103102c20700700510469802042801c090702b281d002031001030086a000100000d0829410402c1103507540309012415901d54011425501c80d0344644110016013404d4144c1403000c404400e0001d50300c01d0004940f4007581d034948070585180c46103490302c01c2748000030109441da080001244d00540d107031a00c0103e4002e015a4241500040c0c5104000c0c00703a00d05e500c070056215803501500d01150011441c1508986041d480320440c40303603030919001038041c80e40101e10190b0f10346070016803160000700a008951007640c8041040d071f22042008081d01074801e003e90041070521038240a0705203c1c034940d07912050503000d20700380410303408880e0aa50081d20111001516200b8000800681190300390304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 128083803 1250 128082553 128082557
    0x60103050d11060615130e010e06180f040204060308030a0207060605120d030209040e0706090602060c030705030a0c02010915090506010e1b280507031808030d0902150705010c0807 79
    0x542d10b45040030395a1884080c24440c0302d6031a411615a10356001001c845101900110120301190b48040403070950100740b144020f9411008000b80709031030241148e090701000132000e130304a078503404c0706001c9a210040c0b0485e00903541d10f0010001c80c1211000c1c40c40743d03011980c00350b5160200e1814805591559101d81e0040005526000e054a070200300d44072141c41c01d10380107031203084d4000020040c044005c26006c1c64011200c002c034015600c0740c401d405031000d0b0f0b000c9610a0716103030720025103031008640520001e07801b070012a0f140d5266807c0040303268001d200102d8500b20030b8450310500744159100d40605540d0715416010820280b2141d4010040c01240341c1c0c2c0b0349001c1844101500c1981b200c100c940030001403100050305086a84d12801c0e07007060b4541140b64bc0f09502030700c10385c800340c4290082030500810b420b85442d2481c1740c0e0240c41190b030165040640a98424010306141d03101260310100f0752100000d1080c03c000604103490003140040b4411185660190600c040030b0032100c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 128085053 1250 128083803 128083817
    0x30619080d0e0a05100c0201021606080103021210050a060f1202090106050306030a0609060b09010915030204050703020d02130f08030a0509130605030d2c03100b01031d060103050d 79
    0x903800011480e03503090314030350030200d520994050005003a401e42d600800d61112142001021440d404507103030204074800e800700d130004010f407864036004141512a5000040b0040010b00042c10080883e1104101035800c449100c1c0b540c0d0000400d40c0c1d41110307992202039445004220089125000e500100001d0103034004480e03990700860815501401203006011002020400540f020490300003119005901000103800d603107045000390040080c604d214544110020a0408031440303058503c003810061107040906d958280009440d001700014141682480442d4004c0e040c5e000504a04854110303c06006040201099886289801c0361300300d0b50003400061585c50300541169130038413048903611315280d00b9035202c101416590704401c1d0140200b40b00c810b0041d4104031580d5288000440c02d4405030740d024910804a5821041c40740d05921001c0050b040c81e90310341c021001c011042c50013181e1082e04a4002c482007089022001440c0d00c080010014400e0a1003000c406030304500c6d01e10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 128086303 1250 128085053 128085059
    0xb090a03081b0d050601050403140c0114120a090813030b0f010b040f09021813020705011d0d12140907030507051509010f18080a060f020c030301030f03111002030619 73
    0x40207600030f45100880c199922008900a0780c011001e0b680119401254000701031440c0c1c000784e80f200d000c125400d022800030305008540c1e400300000d03115011122401c541441e6290581040a07202000007907a281c00d08108042e002484110164055409441c441180d410054948064480141c1c003006007004c09010a010b4071042d0a03c4100b2500c2200e0056291181e5100741202c4d81d1482c0034059000f03e80508059164200340c0141c80c1e101d006900030011100a1703a910f001808008980e03100d02d4004100304041540035407a81450b01c40c000340002100c0080000c074a04500c01929540726562281c00b00f002041403c00681c0050001982c0c0b00b00c0c4c1144c4000400664018801d0103414007a020500d0200280710380b800c11380080c1d800340e00e2a0005d84e58070180352650b211540546e555420300104c03008540d414021074500d030202074029807840e86162202c40f411100c01004030108007a64881407200c000c100140803c960341064010303aa03042110801214451020610706505000e00c020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 128087553 1250 128086303 128086351
    0xe0f0703050a0b100801060e06030c03060106050a1d030a0b0420010203070305030403050904060b0d060605040f030206090d0501050f071710060806040b030a060b09010b040b0d0b06070b090a0308 85
    0x41c107403a5500020f0203c050f1a0701048000032144c54200718202e41c6440760016800d242c52580ea40208010b07802c4c1d0348800e40d51400e15844072001d009080220741c00b00700e03860926200317078807503040165100c07640e01d54020280d00107070500c04020780036145103501034140014800cae000e10622030900d4541c18050310b000e00000207510782c014958040d040c4000400020b0503d030281b0102c9913000c1c0e00a00812501e40c841116228a030400b141c0c20300b81600c1e00c00042426801442101d00392200d20040b80b0159146030308002055019180c0c103a002020300f180c1d1340010304240641401040782c87d03000541e80c0361150b030040400e040ca864004c00c081000c2e0074446130064503041c0d002603a0080c40d18a080303640b4600030a01615040c580250144103000f481420311031981d01083d102001200d150325182d927039940c40c410302d01a6000d1002c12001c208a0404d955440d544040c18141c4040e251509000c26515400280705084821025541104410004043d0f00c8924140e01181c00590040d40550400c11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 128088803 1250 128087553 128087563
    0x1060804020906010903020301090311061006020601050424090608120922150f0f090504030f0c0302010605060309010b09250309020d0204110a020d0c02012106050907030e0f070305 79
    0x30182c00782c2410030100351264414080c4902454020b4001d110792403e9190083c4040c0d85a844e81c0c90900032140858000880c4c40c90800455200f07a0040c00c4603400c1800f0840180b801d000060a003040185004500030000840800204498400040d1a0b4035081e90603003000d14016441c943d10008202e1f22115680f040e14074914816662011400440c48441c000014000e50791035402c0d00484400019036400c920450005a80300014402d41c3c2c00d64034240c1c003060300c0090320300802050203240d10b1851240304030303008641580a40f0021606030b95480220311540d2040c1d03a021016511852070f0041810070650081e00082840700307221f0f407071140b46002c94550310a90582c004240d20b41c1050030555660307000d11908643c008104200082e040c0401d46603541c46144400094010303c000710130454014481b01c946c81e41c068446a420070b042e60710800510440e00124a51030740d0710f4070041251380705c0e00390300c0b842500c0d1a10b001800c003c80b6404140340000032038030483c055126040c140000750300816 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 128090053 1250 128088803 128088811
    0x905010e070618030213090c0e1512010506010504030807110603010f170a230c1306051002030901090b0307110a12300b0d0b0901050726010b0306010201021315030b09010608 76
    0x14001f40f201d92514100701c090f0103aa000090401450f014000b42008143d501100504115a011039200d1007071201800d880c02103508501041c4240001c00100b800c0d01c2c010300400307104145c5484c400c3e02d12400240c040d0000c0e0000304500c88401824804116040700409451420000424121845907070f060380340e03100c420304221015204c0320180010300041101900c0c1050041540742c178650b17034011a20003041940b0815200d10340c91804140414000b00407580d0050060b03491200c05428800141e82c50340c8050074880410540c2c900d545600d407414403400c00c2d040d2040701640070100c907075000100a0a1280e003400000201c1c40d1070980c204030100c44400409000303490205400581c3c80c005110b1f082d1141c4098903807040c0500f0880490f2040d4086885209203445240c1d25186804032442e10b25441c1da0100c20070111400184107801504c00034607480b01051001600d428221004502d1800007503100c410700703801046110f1b031640c0e014011050011400c5c0c840710020740c5000e200910000000d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 128091303 1250 128090053 128090089
    0x90e0a03051309020414040c090305190c03051c0e0102070f050d0c030b04080c0d030209030a020906220f050c090d120311030708090105090303060109180905010e0706180302 76
    0xc0c00040d15511402e003000a0644800840d1560341d030f01c04910181c2c8031440d643d44245e140118903024503005118507015650004002e01c00c4a10350400700100000b0950b041d035201c1c140c1000000003d8080203808810800303c808600c1c50070718004007500c40016021020b0541d000784405000168600c0c03003404c02c841046411005810311414800103502e5250805410f60541504100c2404984001884568880411903e407410b14a504400305d0042940042e8160019000c1c40f01525005041c10f0700310500401c1800f076004051506074442507805084003945440d0044189448161303c16942e115005500042c90250f010000a0081480800080c00b03150030600300c540c940e2095021030744080d055400d19076241000c60020f000180200c80381c0d5100d43c2000000f03140d0381c02c0071080d6401000c068440120765410b10501c2c0500c401210f005100140d55402440e010490901031300840a0b03002d030140407154108040201807081c6100101e16407510403d003000143c8407000410802c2c6804 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 128092553 1250 128091303 128091307
    0xf010f080c0c0106120c0603110301140117090d08090c0a0308130b040b0c061807150311030a0902031014160e1008011811091504090c0e0901090e0a0305 67
    0x801c0300340541d40600101c5100b40d40c600b0743c021402042e8010404401402402d280c0c11140e0f403a0811410b0f2880c149200000c54014001000000c03040640100e00607414180111140d92080d001c05910a0803501c0c8000c0c0d0344105640d1030b540707402c92042034014038100050010062a00b000c9110900c00d403200034000440090415044507241c1400006020b01e151030987d60365464406105940001710080183d004100100d00500c0030b800154401c01c4190340070300304e03580c0b5000d00054442d5100010805154541d0301e80407541c03410a00551048101000000d0010303d540145842c1c00039040304148100e00c2c0c00306800e09100c056081681c4580d049103120003c40741400100c881001515a081d0050070076a1030b010ad003500107000e40c0c141c4a000c41802c6000d4010b191500c01d5035240c8600c4080c00c0f608100c10400ca003400e42c9140541c0140310546407405648032102000c4a1404502d140001c0e400c801d08441c0341b508a072058010140010b050113020300c2c2e9075080b0348400001c0d200500380000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 128093803 1250 128092553 128092561
    0x1d040201090e0c0409060e041101030f0f0204080a03030605060310090504140609010e0105070507021c0314030414100221040201090918020301060806040f0305030a02090a03050d0207050f010f08 85
    0x2207090707001c02800405008541c01d0400d095120103503003242c0110304506041c19400b02d28082c54080d110701c1a43c0140c5040486124107005500402c1002d2100000f43c0e1a00c4003100c0703000c105e000410052419200910f0303400c5607030078018101c0e4065008148500410024030500102c00c0d0003a400b9100c0301e000c0024a500d582c50300c80003008103442c0c44c003d1030054004014003504194040303040b298196000740a20796960031700b01c1e101c1c426000000c0d4800700340c810f00c4100141c030318034400420b4803a0400c44502403071901d5000c15500201c82c21940701c03841900300303400702c002800106400d0403036810550a1003072002610305619202c1e40c0004881d40110001030135a885100f8038001002001c0c0700f0411900b4458844070300481c010016406903007000d6002924a130b0002d07030a2720958000032045208201170b582140c0640c4007420340200c1580a1240c602c865135104034032001580320300001c02e240d000f03100b0064100903550348103502c81c0900c07200c480780702d1b6088a00c4820100143c5490b00160b6a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 128095053 1250 128093803 128093807
    0x170c090f0601090b030712050405030c0114060102070b03060a031406040309060e13051b0c07050109150f0503090f030315011e0503131b0312110102040f030f1109101e1d040201 77
    0x2400070007c5034100301c140014004048028446030b0004802484102e915800c001c06080080d14402d00607800104d00b0040302c400075000d0b40e0404001440f04100542e251526082100a4030340e007640c641245007444101500054a075000703001d80d0411b2034101131b0240000300c0c200444803504942e40c0d11a000112202e030605e0264800d060310091442c1c40d000078074030765662000140940307800702d840c1c0c50010800346401c8000c3c1c6240141c65403184801c000e103007400c0b00c4c40d030006400945103202c0d038110a600e81c0801d0019510421034001000801c5030b11000040c01d421000c028803065071300345d0101d0500503500404884d4090384d0951404060390f0b1601e481d2503120300c54480030502400c98240030040201c0700140e0805e2a255550b80c0480d2a01c64114600701d00c06d5200383d006403081300388208005070500c00c0d042c80c0180600011481409268082000b403241100c80e01000c0d500004140300d401b65201c50742281c000303150302d13000c1301a0401894110b40400c0d40440e07165402400d000404682c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 128096303 1250 128095053 128095067
    0x2120307020904050d11120703200307080306100c050c090601050417100b010807081513050f01050112060e06120f0d03020702030607030b0f040c02010204170c090f0601090b0307 78
    0x5507028204441034600303401d0054448281d0701861001a03e6070204100154000450b407010320030b8912198546495a40d0949854808007411044509980d03011031241c0800d03c050320205015000c000d030749240043c200702824032062030300741c1440301c40003a40c00860400a46e40066500940d6038003c10780310f0780016a2540140da000300790b44480440681c1a402d004030310b0882e07021421000b4011420140c0040d03030018400c403a880b00050341c00c8002805032200d503804c600e6518015210454080c21300c00182c095440840f000c1051001d624010032040d42e119003501d0122022840410083e030400300b40700a4540042c14051140143c1803443c40310b03e400f440000600700d6502d0072030740d13010000c03a8090081d400c01001030788a406a0700000d52028080e0044103031100d0014141e0340c10a4010040000a00c191080e16003199400d120100d00f0082c0e0821490030840c05000510880d0b00c400d04010005400801c138041e611243d809000241c7d0f0420700c80300503910394000d00c644903a10900211055 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 128097553 1250 128096303 128096317
    0x1f020d12021306110111030c07150f1b020f1204090b0a0e01081501050a0501080a020d090b181209060301030f0f02030a0f021c0201020c210303010303090608090d020703021203 77
    0x9214907100040c070744d03001075500013000130102c0240007130325001000d130119020848810549407005c0210708002001a000c0100046000c1c1d80000c2c160020703044101110204541100381c14540c54403912119010803491558425800003441c1e0496120140c0490740180c0c407551f0340a03a03c030b00c00d005032592401d0340c1c14043c040d244280009503a5507006107541e4510943d0003648010380b43c002144030b0600084031030540c0d106031260b031481c0d00c4610781c0d880254400505c0707000030360751946d203c030025000b905650b0064040800c030440351000261442d007004802141e5038074050041001c09030a803035280907030741140d4001001e000032403200d0401034007009428030025071500803241c401040159808044034498000d4804001d140f0012465036503030600054040d000d07a10110103400c861501003000c0c0c170300f801c0d6020801c5449030000d88891070b542003030b04100d0104103000c405111007644050100c0d407081c07006000b07007a00301150b00c002c0d46030405800b002c0e001e00010040be1203262401c108075811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 128098803 1250 128097553 128097577
    0x301020703090515040b090108060d02040c030b100c050705010c0c080304080604150b030703150b031509010b01020a0b130614100303020d0201110d0b15030f061f020d1202 75
    0x345640ca450018880700190003031520035806440088041800300e019a000d0303c0e180c02c0c20920348910180190388501c0002d040640c40b440f18803407030740140c4950007640ca80400c01d07240070400210000801200e031407851030b80820058054a10340c08140b00281d407400300c0b082828642c134410a80e00340100d0450058101d00c001d0b10000500060703801e40068600e1050740107501e081c102c040a900310405440c90080c2c2640c2c117601202d0300340003107082e868142c403415581a400051502c151800f09080194885040704c01c40b4881d400c1003450f040038098540d6a000074030281003200200ea60342d2010440141c900c68229101c0e80107107042089d9584005100403036140201d901349041464810004640e000840041c0036015502041c180140a0712009102e0307000d08600b0140310549010040c0030200011341e0082d4400980700ca070409860065010328aa82040e441c00d00d400002e0064800c141c1c10803010b041d182c02d501848155000c1401000b040c8245040000e83c001110401c01a001c4c0703000e92b41c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 128100053 1250 128098803 128098807
    0x5071103041212050712031a1003021b0c060703030c03020915030a060b1312021305041a090604030f050306030c09012304020a021c170a02040e1503030406110309030102 74
    0x1c0c002000b02c0c5500b003000d00c0340101e480c00d4811800708031180e0046420042001e00c1e8130845011090090b08180890440c2591016400d04400000749200d41c6880d40031000c01d0303001500382d10f0600150940450601c1032002000c0354140d080205000c3e01c16410083c0c2019a2440003080741c1c0e00c66011141700010060140360426a480d001c0030a603030060351468802c6140c802c00060022a03e4143c54680e01c0300c07002c0c00001494046003680e641000030040b40c0c40310061070804e560341c0242c07188030b0007940503804002000502d14200c01680c4030240900303009500a100304000658850780c900405c1005140041e207a0b140c100101c3d10300b0341012a45540a100c607800072404007800b0405101c401080d648203041222190203002c200d110725813000006070404441080e508020340d0007490381211910b8419100000b0000501c020710f030964450312001d4000400300600e50415550340d401181c8182c0c0c002c86421440002580ca12403440781c0001c1c44808110308503050010700603580316050240c002c0d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 128101303 1250 128100053 128100059
    0x1801120b060403060c0f020a0c05060d020705120705070906050f0d081b011a04060f06140c011b11061306110903060a090201020f06040503030a050c0c0a0308070801090216060507110304 81
    0x10143c45108008000181400b070b441b003880780b00081c80100700d41c11501d0720002c141030205118036a440703207118810064003080700030000bc401b080a1a5030040403541151517031043e1a209040c009076a00140206060030410700850303a800c064070b40d20b0401151448800031161629206a0058440401443c00c5e50001e40009a00640121402c01c4074005209441140c00c020001169100d0289045030781c04500103000207401044081c254041c103c0c8241d042441d00d66149094683c2a06070040c01e003c1640d4200c0c100d5040490540b0020010010b080540f607d8204842070300e21882c405004c107500c2e1840316054901e12000c50f43c9144020b01514003d1038006219805014a0101240140300b103046650280e9408104075000d164003802031403568484000c1c10340500005042e005900c0d03010458010341e200b041003c8103d5500c2070f01d948a06180c80394000c0e109440591004004500400540e800503203c1170900258962000c000076482d124035004560060b5a00c2854039a444009804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 128102553 1250 128101303 128101313
    0x415090203070804260f0c030c07080304090c030203070c150b0414010e01080a02090c0304031803031e030c17040f080309060108010b040218120f06101a1801120b060403 74
    0x452240b03004094017041411072650844214020a8081c00e0340032080c0410001c94039034074000c01c405400d0004a074107003000884e81506058503644412665400083c0800c0180e030b16005e0041348042034101182076141c21f11000c1c104880200c001003d0980105490b8241c0c2c02c5684038092030700d03015201300a18040c80e8905800040b00303000c2d0350200f8400310000140341e0130010300283c086a0251240507252105851844d86400c068400c0701401980094010916902d84000c0c000710b00070760300c0c0708000d1107070ba460009030115210800100b41c01c05a20f8070140303030001021041c3d00c5038602522041d036914140320090b0a40c20f1401040c2078000014003c0503207000883c28182c411400017040343d48081400c1108034446c24500e08241217060030059100d141a012140389842c0c580d0a999892070400003075402d1000845180d940d08411010900540f011104c0034025108042e51880c82d2110a001200000c603c0501242c100302035801c80c104480341d02e410001c410b0341c021307140648641e01c4c0d03e00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 128103803 1250 128102553 128102567
    0x70801020a2a0201020a02130f020a0503060111061501050c01020d020403050106170a170307030e0a0b090f0708060a0506030304090c0305010311010c0f020f0315180d05040b0306041509020307 84
    0x8049190b0400395040c008650784030755210103941600100946101d9030300713000003a03922420b15030a1507926081c0d9a003041141c00102201101640d416650340352540000d00b00e554524900840e6a0002041010750f000c51046040c0303081090904a40301c0f00303540f19803806480713000a444038260001c1000010170034150840c0c425203240c0d11840e44043c10700414182e4440e5410006443c07000251001400c0d40c00e0701d80150f422102c41d203000305d14001411505860108409403c968010200c020880c160400780202050f0510203400f40c00c42c545801c03c40703030744d800e005464944503035510004107450b980e0030001c4600810814000f44007881100f0030250042c8424031064030580585d54403590760350301c9003c0418000d5840010300641840a40a002c18158070080c082c1e0507100e150800c030071101401c22141e210321040d06503464040b102c03194943c100780340f100380c00e170520030140b0041c440f100c100d209496111009440000310b1100701401d1882c1041c191740000070491001047c041866800ba031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 128105053 1250 128103803 128103827
    0x9010f1d1c08060418050105041a07020106030209180106031208010303020c0906060a0c060f0f020702030709050f041103030d050c0a0e0a0815130b13050f062205070801020a 76
    0x30a80310450000c0c01c1c4108080c038000801c000048100c0c0c0050f0452600d0351017051a40280741703600c00101c1d115544e0030b084a8099900303503030001e01d88503512003c96941c10303d60391101c0d60b803009011541c6913a0200307103c0c001c003800c42c213040e0302c0002e0346400648095200e94001c50304500f8090710081d00d1100035150791803e00045d40107000b0b0300794101e0740f8140005c486000302d001a1906140044464007240d0203e25918100c0d92180c850b4403171080361015000314440b001c102c000060399410305e481014a000f00c2075018102282c140420450444074016a2940c042d0304041002c00100f8448002421440344000040c00e4170700d0f180920460140750701c003800178034006490b00c2d850440c1040420001540900c00c001d09503012440b080b40140e4000341041e000109185240300c000490383c0c60488000e02101d01e0280040800505824460f04005105580e94400023900503414003544040550101200b802e204000200e0040704001082080c0d5004140d280001c41d03d46020348402024504911 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 128106303 1250 128105053 128105111
    0x501140106050711040c090306020a140d0204050102070e01030b010b030405070b13052815050c01020c060712050408090d020f0a0e07020d110c04090f0602040303050d0e010c020c01030509010f 84
    0x1310310b1040342c1040e100d550403602035a1034211503640b1350303a02c00380658010700c022000c0000911081181e1034954014016030f030420a40076031118104800249403454960002a42440210040011843d035880490558620049487d1740e50354908019191808035030082e000b1903c0056040351003961a180401035600440e1644800c0d0034003220a0002c14482018510f030b205240e4007001180e4901c0b20070070b07408003141440d034100442c4207521822600300d910b0f040740c15000541004805580264000d00341803014404002c14101600d54048078000e01003014000c41910000f41c055640d1090305050811008003008801c94989000810404003581c032030016110782d4103d80505405403a80e18800303c40c0100401d01c5070700fa0b00801020b0700340814192250b10710701d0101c0380810180d00043c000f81d8040d44807507a607001c020052404035082c644001107140d2500f010800d495034081450b03003a401d02482c0c04180c548418200d00d006254000904000f10314080140002e420b4030500c0001c120200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 128107553 1250 128106303 128106323
    0xa15031506031a0f03071208040e0708090c0609040b040213030302010b06092b02030d0503011a09090f0703020c0708100c0237060c020309040f0e0309090405011401060507 75
    0x1d407401d40c159100000300b00740d201c0c8981100c11060400c00040c10700e81100030b08945400d42d8a002d500030f140c5840034180c45403540060305000028541045a80010305458801201d140000700c40d92100d48058005103c0d11000851030749603501c503042441c1c4014002c00c11540c032a1840120443c101382071101b200036508084030140c0500e001d5050f030b84051405406810b1144204860901020b07081c4904d101c9080d02c0000f140141c1c5080004044081071600c803a030b40c0c0d50501c00d00c070000c040c403101d80e082090341c00c110b03841e007944480130182d4010340c405540c00319030346031040286c010380521210007402d442202c40000740a0400220075561b64840d100410a114418034100e03100d140d5034103680b45030080d0502d10708191070080c40c2110301469034005800c90b50075039074442042d11b03080f0840d41d0041e80040754800491405e441191941c840840c000c02071a040065074944030300540d406c0d544160b6505000030f040c0070083d04480e0b401d11140c98059610340e140c6101401c940c1012030152105440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 128108803 1250 128107553 128107559
    0x1060e10030204061403090a0b070c03140f0d02161b0e0a06030206160305072f01020607020c0112021c05100e0f060607050c090705040501031a1309020a150315 70
    0xe0300c2200c055413425a5018000d0310454405003450744042c0000d40d482c41001d1081020900314000240504256511001607030038500b40240896100450400b481004000784680351404804841d02028071820241e2503011001d03a0b40e802e405519000b4004642c42c500b071041055180c00504195441100741105580b512658501101d145000013504154104058250300107022080058984207103011840c1440680c0c40c203400c500182480a4000024060850307042d80c0313001001415071080c4010105440d00d000001d548800b60740704541440702198000400440540488000711504000303140d4400b07800c0c2e01c220062070111140030340003894442c04540d07004058034850068410002d402c8454a800d0104032060340030791030454282c170961140110646607080d0722441648035458103911280b42c81e00160660b11200302920180000481c142407558030741040621b10068820002022103003407010540c1500d1542042e0344c412000c03883c0165141c0d00d85c000410f05203101540111700c82c1e03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 128110053 1250 128108803 128108807
    0x4123c061802030f280203070b03060303130905060406051206150a0e15030f07030503030402040f0f0f0608100b010207030f1403121902040302010215062706030f0a0803161701060e10 80
    0x21174680c3c0298507801c000010047c48400c8809140c010038020305991400d180450395035045a0503901c21418942c880040280c54a0079120780c0b0000c1009403494213025800502041d15401d004241e4490411034a008540f01d8544982c64005810181c03500f810078100740c030549014074000d4403c14824850103000e420070390404200301089940c03100046046480c1c981c2040040c007825012400c00701d548101120664005e0700840b0b12030000c410780082d0550414103141e09100d1814000b40318a403c20618100c00c0c0d07400030f00b00045a8106001d04103411840c50100c0391401070b107617041480e00c008107039583e810b0605146940200090f509048180f0360840a0b0750a9000380d200290250f00300d140a49a0420454240780c0c0c03041e0b00038100041540c8203c4508e00001d804240c1c1c0250001440030031417903040802c0b00c203000c010b091005000001c280e6542e01c2e09807000800c01c0b0440000380145116a40c0203881030b8a0018004098621961715044024904031000d82220700c104001220112064 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 128111303 1250 128110053 128110123
    0x6030606080f030d0b0f180a0b040e0304120516030c0806130804050103050a0b040c030204051806030d440f0106050412020604123c061802030f 63
    0xa480c40b0051400d040d54240702000521360200029040840c18000c011035580b40d2803000e100741e0301c1ca1106e1603d0708001d4061402c481825110a00461034550005c0c1003c1002081d42c048542e1244c07001078109203490003034200f042c2d00400701700c004040800407003045052a8903106036059041118890360310300142c403103036040d451070280c480202040b0601c855482a082164040140f40003c596180200041400c5070f031038070701c01c9c8002513001c1024440341c5802c9001441211761042e007045281003c000003516203024a0500003841580f00c0501407030741e04901070020038052031400300940c20140c21815040b00d11810495107290b503990004442061508629050b250166981400e042c100b6203a05620085e40c10107980c885000c0c440010741048001044c500075101e0400720800040b43c0850036490105204204d07250200a49503e07181c022180c0c000445079040300d070101d01c40c40058001503207090460303c0a034042c00707001907000c418080011100c9480c504008190740da01080181301400c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 128112553 1250 128111303 128111323
    0x90105060a0504090f14030c19020f010f12020415030f05090a0221030d06060e0102061501140d020a02060403110106050906190e0a09030801050105030c120403020c040c02010603060608 81
    0x1a01c1480180414146030f40302c0d1300364138071036800e036048455036445511840402480d07403a8194000950b81003104010b0000440c001d1224120004181c2254006400c8500041032a410480c00d9020ba0703030018440d4401d54001080d04002315540c9844520243c0700d1100d5951420209081071801d0703581150300d04c1000c0c0f0802460000e441d82400c20348c00c0041d400307804681c20111645000e2084c0e90207405000414503c0c10200740054003d15042c0e01070b00d410210611141990400c204200f0443c201d41d40109519809203424515011000e842c2001e0340101804002a207202003518880d203900010414061030191310780c800441c1c42501d1090a0391020f018a0340c100399084045021070410342118a1600f508003601000b036900d4803203004e505401202e13004191500d410000c028560403c42c1c66024001c20320300345155240030128010342e84601101c038490742008000081c01c0c580300340a80114507100500a2010240702c42c0d000b0b01801142c0400d5610342c0c600170300013070081b0b8005204000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 128113803 1250 128112553 128112559
    0x20a0305102103180603060314210705070e0f04020406080f210d050c070c0608070503160201110409200405031e0a020a0905180109081b0705090c030402010809010506 73
    0x1032180d0003a01140c102d402d801040781070020310803941030031403034909031100030b00b40650b0005203540c590b04004142c00f600d54005502900050506542c0d080c0d08107907511000300c4400866a16007152606516210b165800320302d5420071031046c4118100402040d9005600071175040c443c036070b110781b142c9854141040700740b4050341c00580c0300614009103940724840490400445400c200d400300e00f880a94034203c450000103080000c01000304000e0455040142100f880c3c0201c5070b00d0700c0d00e0040c04512003e0b214803040c002c90b07107403002c1c1c03c1d100b50845481a00500481078807103a03a001340303902600c11540c1a505919110190700080c1d503601d0150340071103070020024001e907400018000034403c651440d002c01c9001d603d41201c0945c59492030780c00101900c0a001407680740ca100b008052205685650907141d04000340b1001042842094a025802c8000c641c0b003003110185076585015419400300c1c1d0060054803c00c09900d0b145000707144628001e072030700020760351000c5805003210021200a45c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 128115053 1250 128113803 128113829
    0x50601030b100309210302120708010f0b030a0222061202030f010b03180318090a0902010221040806190e0d090e04020f0d1203151206050a11040603020a030510 70
    0x2c0030078880e4110744d03c842d02a101803106a01c0c0e0300b4001800106015921001c0b03a00003403503045400e0710030041c2d40c1c07103403180c60300c58280c1d41001009600038109200380000240302202190444540e941100c0781c03011000f4220540c00c40703403441042d401c1c4882c032400c0d0100c0c269200303001c03250000d4000c6070300c1800d030510282c15581c01c12404d454941c0018081400384e903c0c2e19049441502e00300020824000403050303220743c1c00f40031400c001030000000c022480c1c440c102040e001c01170360005288290041b400d51000801040108400b1250040364082c00c1c0a12900061202c0140b20407020480010f40c41d409100c1c2840c209055541c0d60003400034140040c040b00c4040120030b81501c1c5103608548001e00c0386004a44100c00144807508402c000d56a1f41c0034907801c0421140c06214015010811070405000107150840b000190760911001814640d190700004071010031942c410030000d0402e4444e42d0b240c82d241d0000030001c0d00543d9890010038a00310105003141003c2a030320041f5400018001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 128116303 1250 128115053 128115079
    0x7050c15070c05060906041e110409030e030a03080115020705030712061b0e03010b0909030702090a06170d0305010f031e111512010b07081b0307020d15050601030b 72
    0x1000100000c0c800810008080c40b1880082e100b40419805051050020b040e54100342c14402c5000d401640303028024100754114200103290380a04041011040303900203000c1d015070405607a018801c810055060107184114030405400c00100b5058030f15410180f41c944484040a0340d5840050160700c0e81641b2540c2e08200262491030022901c502c100408281925a1074407904030a501030612000309046142808030b50509200c0c0030b03001d0000302c60324203ca0409814081c4c40303219a10b0042c2c002e00c802400555040d205401441c0101607038540d0180c4058010002511040340c04a14800070b03060100018280d00c141c0b00120640790800960210120001c01600001d000396404a0b4030b0310f01d11206885a60720003a101d20b07840c0550181d1a5201c100034040010b00c80c058000c858040014080c0300c02107614502662a20b80101610080c03914000e0061032950180f060002d61060041c15000c0421048022809240b400c0340310a020f9174803540015002c1e110655041364010850003202 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 128117553 1250 128116303 128116333
    0x12130209041502040f14030c10080703110c07060509010f03060e0c07050c090103080d0c0203040b04210b150109060c0f120309020406030c03050c060c03070602090619031407050c 78
    0xb107890810419030041c905a0750b07501e0805d500d40075600c1041480101444007203603040c103000300c40407441c0403900d880c40181100700c080c059900c0517102d10101580c2c1e60304c044800c410501125040d00c141011241070b81d98604008110b54030804029000035181000d01c0f000c0342c0070780622010b444044004078959a94042192070715084014227844c68880c04401107000d40305d060009010714003980e15188d468090110038800c2d1050703c9540000c640c0100810007003200f8400c152016501d00c2215500b40c01c443d11103400c003207499444040c090600060501a101107a61100c40c610742081e00c90180310b603592441076450201403040584011307030100141d40020b400c001450904540e60030006080c0101d900460200e4100780c02c1110b00b22140e01060060240402c03246910101c00c403035003840c1440b4a07c43e10b8a900500900074015a0045510001c5a9802068660340c1e5290380c44244204400b20b4010041c103031782c0380c060328100901c101044401d48a941143c207245400d0006190302c0b0411078403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 128118803 1250 128117553 128117573
    0x20a021306050414070207170303040210020f0607030603050c0108060916111e011109010207030602130b1908070203090109060804050c04140a060803070f0303092103021213020904 79
    0xc924465070384640c00b04203961548943d45000c9036649204d409071a0020010b40707408000d40007800040c140006862803a500001200e50040e4140c82c4100541e5051005038500b22140c040b2003268010141040400d03641607100b04226401002203801c40d1302000010754a49209843c141d40020741c007000254415604030240030202181c0c9000e0301c0c901d07445e0107902d080c2a840900f42c05140c1c002c003c0d0030480c2d402400340351041458040421328112907103002030742d0340b00244001032019070085054011445070f845c01d400101407a00e4031301d030364061545201c4542c010020180c0d010403040c0c0c0108080071310000650f44d200c601070b110703220564105442983c0c80180200219810310844401a00720b84480c044c0f4565168401c1111400e810003000007402c0e101580c0100030564414011000441c891200c5150440d4050800190300c0d035407410030000b84410300c214800c0b04032140d00140516070b40b50b030040c82020b0060510340c45503100c003c130304d441220100741b001e50b00005802c08140804c005100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 128120053 1250 128118803 128118829
    0x171e070b0c070f021e030105090f2a040f020c100b0f0d0206040306020c0c030d1707050a050c0d0527030d03020a0c0606080706080a020a2a020a080303040c0510020a02 73
    0x810043c1c03944080d4000f41c8408070044101d4110714841070040c1c064103007401060f400003030005c041c00c0d00300059000155184101c1515440721011007020b8210079200d09808502a40090428009a1803074a004000703075005071010b44162280b080c05001c8114a880341c011017441c000c05c4203201d04117140800920120060050b40c0c00a0100302c0000090a1440188a024401c0020300200d0000380d0030107050482c11303c1c0003001e1054407c1d5200d4600d9540515962090040c200561604041c0340c049940d0301174854290410703c1209001d13007031550004060007425190116250700406040c0614881c2068521134030b401d07520504001003003601a40107080020050b1a00d5540c811454480c40b0a0f10169030040751240c0040c90180a02c035071007a900c650100002005520305116050024040040c00f114030454800110758100d035039091400074241150010300068001c0e80790181c450f103a038030544044405046d40e000000700c5060410a54290300341513009000340400e0394090010302c95101c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 128121303 1250 128120053 128120063
    0xc0f10050d0f050901051e0606070f02030a150501060c0302100203040f0b0a020702011d010f030b1507031706040b0604061211030112110103060f050d0f171e070b0c07 73
    0x440390720400d056500ca100308040b07030b110000c00c2c1c40c100421554215240a0414802c80c000740c1d08400b00c52034000055038003c0702c1a00e2050741e80709907081c01413080781488802581805241030700005d02c00041c28100f40c1c0381c144101002142da89039030075201d1040c0303a0310080c050b0f000000030400005031580174540c00f9000b180d0645004280d40d0391003408603402c44000c0c11450b404078200c000d65070b101006604a0201611546206920780c0018019041c3d0031144000c16494260700c84c4a9101c0307891104141e5800b002031a101e02003880c024101d02c600740c01444004440f00c00082142c41d16000781019180040c180a14241c00d06400722403002c608581c0e80c03d5181c5460383c00081c000845c00460080040e001d2803405105145442135140e00700104150405013429010311240c91201030b110210350013242c1d6005418464034010301407800c1e0070000390081c0c08823980c1d40724090300d0a0003090300101f880c02c64010004038a001d103400d401380c0032001e07100c8500380700000d108205180081844602074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 128122553 1250 128121303 128121307
    0x10c0f14011d0d0e130509010e010e07090b0a0e041509050a060e061008060c090409120306180e0d110c09010609050a050301050402030a030f0516081b0c0f1005 70
    0xc05502401c1d554108101110104100410b50710b05209015040c0e10741c00d00d180280034100c0c50000610090b80301252041207940d1000420001309095100d0704151503803000034044031122604081e183d807000d225000c038180c14003454640c1d51404201c840180d40281403920010744460320f403004231000034000c0e2110290b6883c01c10001c03030301c10030005503800e2180a01042580c1e80e480000d080c070b1740240005940d02c0c502c1c2030611a2100100d250781c1d2004241c1c03102910b0742d0b03c40000801a200c5c44074040d002d00c0c1290542c1c180760390f154000f00c050b00c085c809a904050700b202c51003012141c0400d4020103c3e0491740090032400c2c80358082c183d001206000b1a0320807888140000c0381010300b13a200801040200310700704000d003030443d40a80108030840c000c01083c9040c0e000300c0d88038410740340d0040030440c00b4080000e0442c0200103031a160440c20003504100c40c560700e80315090340c0c41172400e0442c0d1849003c00d280300c80c0c400141540c51000c0607204051900e1850240004c8030b80e4941040709100701 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 128123803 1250 128122553 128122583
    0x11e0b0a0305030c010504060c110c13060b07080405030706021c080414010e100605031b040513050307050a031b02010f08180d020601031a01050915040609110a0905040b010c0f 77
    0xb041016120540c030903800010141070030300c0e0190495208229140038000c4201d13081c144c142c0080b42e16400e036074080d10000c1e0140c032560011b50061180390400b480c1280c0100b2440b051103180c00207041998002e900711607205869283c141e03070700c41808141c0324051644007010b1040c0c1348140b00341a00035115180c05e004c032918130740100340dd66010300b000e22195849401841c082e01540c0c05808000c15098011341028080d20741c0160840c130f1111407050059460b040401c00000c00b40d400300b12401d1b00310060b207841d0055494095114840141c094001540008040301030348020a40c01000940c1610340601c0100600c5040e42c4002008201c03c000c1401b81742c88140d689418455070740d449485901800c1a50306610300802448052201900c0c1440c0400052241d901c070b100c115604540111101010700700d42c100010040e107400d27004a01703402c0c1007058541815103000081c20034801c25446e142040c3da180c00500c0111010031101e240018160307600d10022490102c0c6015505015001c07490391041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 128125053 1250 128123803 128123813
    0x130c1205090303151f0e030f0a0b1504110316120e0a1407030b0105120708160302041803051605011b05090a09020a02060c0c01020c0a0b100503011e0b0a03 68
    0x2a0455400301c0c40e410000401003180e080349412662803200701c6206244003400c240d400c5404008400d9103080c060301014200c3c0e02c0e0380800c45460040080e00c22100440340f00d20740500310074415504403410580041c00c10f0450310b045c4c02410240b4010031107003402c681d200c0f01011030700e0240040142c1400181d140c0406414444c0c0542c980580d04000188003901d01440c1c070300c0300d07441e40b0358058001d5008084180005445030350007074110b80302100e0a11039414001125030400110340e1140340180b1950003040410710b082942c140440c0d000720781c200600b962030b40340d101c040b442881c0c008001410811100c070b80744951041003c103250241c400045d01c10486400311240c2c140d80c6039240041540402d104a1905d03017924400040c0c401d00c4001d506004600c000a0340d00c540203060b6002e80e0201048145100c10258103a1300701d81519811150284aa410000140318042c0d590358034800307204401041e541014000d105039200040703801c1061202000f1840001c060711300038a54002c0d41070b0310001c0861 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 128126303 1250 128125053 128125061
    0x6020a03090f12090e15042a02210a090510091e080f0a0b010308070311030a0c03031505151b0609060f01090c020a0b040c05030d050c0d02060105130c12 67
    0x20740700f82941c0740c540c3d80e0290301806600659004061485003401004000c3c080e40b0f0b0041c140034404e49022a040d2082500400e40420b03101c2c014240b0038800a00e0148581c0c0003842100d00100300501c000c01500270100c42c905441100307540b03030100e80b07802800c12030781c14207c190b401044041c3c40c20541e03030b6032600860584044140d02c0c20049843c000014080b6242c1804851104101c22004101303040715980d03a4422000c2c1480040c090444c046403c800b410f0241e1244092100301800783c0e035440b400d81c10040d2181e1f406d02c1040c2d0001c0c0c0791410703411103440c80c08030b002c040d240d004101c1151038003070f800c9105040e48052000d941101070845d107600040c404014884c020800900034040a00d8040345403194614141c0c00350030524100344242c0320716070b00420680c1d04c198000104c0d1000c0c0d659030416107092845a4481500b44c0300782460114015441806040b007e0030760ba0030b965001101038403c983e104420700907684e0189400f00c400201c4069503104040440f12800c1854940511440400c211 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 128127553 1250 128126303 128126333
    0x1170901060f120210090305060408210403020609120c101104080303070f110102070320070f15030614030303060d0606050306040807050c0405091009030201060506030408040303170403050706020a0309 88
    0x1180e0403403c1e241c114a0881802008201d42d442c181003000c0c0385031500c130741ea550701134006064400000350001c1c0c18034560f0009210041f00000149260405190007580c0d0001101d69040c80d00035045101911202402111903905d44680208055650003030b0103002400c2800190318110300c00c21001034042c200b070000d5841766006d03440b000001d903003c900261040603620701d01070107030344104050800a5000340c1d00c8d15950a4103400c8148081410072818a4400140c00c000c85940201d00700041000c2c29440c41c084a0000303a0f014001e069889c210480741040000346142d0503081800062901e09042c0e0038002d01d0f500a03007000c28590703034a80109044c04419a820f49841400007248014008100010b00f4a041700f03460400c0a032603c0410340c0c0e2907400400d0024221340d00c4048640c1170500c00d4204001605008142c580d03079080c0351901c80001d60051004401142c4610b1203490250b20b1403080c23620a64054440601e05541559500000e6025000c03e009140d03a4883e21408603200f14880c40d81 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 128128803 1250 128127553 128127569
    0x1406120a0b010206010f062c09161403130f020310020a030209040e0a02010e130b04020c1b030f0a02090c1b0120160b040501021c05060f0a030201170901060f 69
    0x140075141c0020b090680507080940b543d5190002000703250341c0045d0282c04003000d58604138610600c10071034000c00da0900d90341544602e8032400d1018106001f03800ba401761030307152181740d688451140300269a0004694600d0901600480900460f0011050020309480241900d0460301700d80c007103008070f030480c00802001035808204002503007407c0c0b081154004907440242450f1a282e80001d2038001c0310034a40c5d019000d1000c4400d00d80c030030f5400a0001e0340e8018010740d02d0301707034038021142d55000c6c5100d0007540f0003074049070396082d0030045006104c01c1c10f240064010180035400388440b1070710150000069403420403013010265410b080c103040c0f840600c0c00104101c9000c1c982072401804424080e900c000d0100684d00c40c800c041c150b00c60200e0b070700c81401c141c0c90391107046c21402070262246c421302d802d503110340550401d40d96900451140b03008861400c0d0000d01c000901021440078003009011030002144204a0381d01c0b00083c43c0c1c40440752001080c029114617644441e510181c0c44291 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 128130053 1250 128128803 128128811
    0xe060105040c0e1c031803030e0f18060121110706140708040311070e010605031f210606090c05040e010b03060f01050304060b330f120405070e0f0612010c0203041406120a 75
    0x452810306540341560104442d071880300bd2421b0940041c0d0741c8003801860601407107210880c19000d807864400b5291008013010040d192014081044a03846004125851468080180800c00307151138802d020344a40d90310a1b0181c0c1c1e49035401d0b107402d45800c0401805215442c2c2c00a00300f82503010040c0030382315560754251641040c805036901e10765540b00700004500b8403402407025048183c001e0b446c030507410b550140381c20920308181c401013410b6000041018140520081c074260400d0042084400000c4803030100c0c2e0307880e2980c2c00c180c04299051980b1217000b60081001d076218002940e0854003030440003403080388100c001007554044120201c004401113034079425400c56a186104070349a002002442c1c40f01450000e0414803c8404092810303580101050601c2400c00600d409040b00c03030b03405141800c182c02c011107840320842e80d4a2040d40d4207524002c10600c10f00038070300d540400c3c0e00114102030801c00c0209801701102d1141c1c1c1c01640600c04d02c0c0da010ba000000a00805041c0c034001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 128131303 1250 128130053 128130077
    0x4030b040f0b150f060a03020409050a091509050615040e010e0615010e0303070f051e07050a081b10020f0615030d0801060503010b0d0f0e060105040c0e1c03180303 72
    0x100201c40028220a448050b48400c0c1c1500e071903c00d113000200008a8549960b10350240040e4020f000c2c030341080b5642460300040050110f00b552040728030b070303000e00c0c10085103500c10350181e030984284200040c031940110006c00c100c5101100c25056920000b4400710b4100c0c0303030810450071594a20f02c5c081e80b90f408070060040300b004503141202c045800307107000c408145451020030743d01c0c440d100c0010040401801e190f0203100342404090307400d5400710303a00c0c3d005205541d00d507a9190464015540f0400f42c480c00054400000900c40c01d4100c4200070465038001c0d11005c0084c001c1b001d0344901e0035405100141c002c404424000d083c81a440c0454a00340c1c0503c0100b41440c1907800710460b014040b5170401404019040070607281121240c03561540d41d201408120005450342c0103540311064140b140c8800e4013140858520306030f90054070100030304d02d11801c040f038100c1d51169000b50031968074510791410001c41300c0380c00d1815005e82440d500b031147c0030100c071065146582c0180c0001d40031101c51 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 128132553 1250 128131303 128131313
    0x90506070b06090915010b0304020d05071202010f0f0c1115070f110a05011205040f0803010303030c0e0f06090609061b0a0309050904030f03050702070e070f140c060402060d0204030b040f 82
    0x109130000c610744001d0880b8212564001c19280060090b090001e0001c030008085580742142e4a4a40c1c0d80642640d05896032880d40740d03d8458000e00c2240880c10a44090200c540f2601ea140007080d52581c0307032920703041c160f215886000e0154640c143c20603100007141c1801002c500041c2645e0b8443c110207240c2c0c0c000c40c10b00c3c5c10280034006540b032007401d40190401041c1e0344200c10303ca420312015070004a985031441c2080c1c000c911440300078000742000c1f0000051542550111840e03494035161890010401c604008040301583d081c10b6202d40180f200c401182000c03001350a040102a01c0146001e02d00a2401020090962103021a82c0700c00207030400c066111200300000c20051320b40958a042a07078028110305040100e0030205541e94000400d41c600c00c0040100924070481203440350b09047d240101100c0e0a0008000403804030085504c0c0e16001108556203d058040078040e0b42d103c40d4200300c0a17600c0801c180600d5502444040041005481362a008a01c10030f04071820403010310300703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 128133803 1250 128132553 128132569
    0x10609030c090902010f051c0606170a090b131506080705100206041104020702010c060c0f090608010b03040b10240311090915030109150b090c03011503050403090506070b06 76
    0x402d10496003460706000050742c02c2018072142c070034181065600d858540f1601c0c01500d190309600030440707080580001c1c1080d00241000b4088140350314409003540c400e1441c1c41618004e0000510840e68400002d00701152901c10716115032040078404003020a00d1035003c00e403210350700500c11503001110208524a0040382c00c041c90f0301a40003502c0c252800e6110840c58281e8018003502503600059141d08680c41015241001ca034070034000c0080700502c00004261412440204011401c80200411058083d8000d207040b190041010351030369440d59680e24500c000942a5030000c1440b8101144603203c0c000b141c00c0e00304440748200c0c0e0400540100800b0313246640c140f40e030042ca041021210070b4481100c40c07640a20804280700c00d00042c000800c2c0148450b61010300304107814912612010b00c1d0340c0000303054800c1290a20041c1d2a2841d008001d80301c01e2050000c2458502c80e80703003d2034042c2d00a154064082d040c80860079a035000814842d070710480d411584011f0b030504201443c076210360b03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 128135053 1250 128133803 128133809
    0xa0f12080f010b031f050402030a050a0b060f031603090f03030c17060d02040c020c060c0c100509030304032d030e010207081605060d0f02071203050a050f160c0506010609030c 77
    0x4501c0a55403510000000c240710140602c10510704107441da008100f8884a001c0c014840644119507910709a9503160003400c0582d2407040060828509601500e0803100703a41000d10f10b0301c06145980c40e074005070790400b45152242402e1588814000700030807280551210305a000b0f850100307010510600003085030041000c000c203100540303400e0001d0b5032034003034180501c42e0341901c0019242c0c018040036460041c06016880c1d0040000503030222000e800300356444144020740b584220b41c82d40c254252510b0080814107a055072003031004101041c2d60704000030301001d03101c001618540009000101d504200c43c003d4011580020850400b03503030400080e002810707040050100f082140c960550304540620070305105400105001034054034980c404680200c0c003030001c565a028070f180540803040d001140301302180c0b0741070028450070007500910b03100e1800c2e2010099181d5918040e1200c03d282d182d001420041f5002e80b580024004201040c0645110b0b11903040e00e501d145049819204590 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 128136303 1250 128135053 128135071
    0xa03080a050f070309060b060a030c030605030105150613030506100806090f03040614430b0613020d0608010614040603110603070507120c020f030d0207031101020a0f1208 75
    0x50204102c2c2241000c205030040814a004036420942d41048006019203074081c0c0d601240000d08460038030340561008010f40840d45003407001c0c0f56107404150032100211103040c0c1c5942030042c804014640100240200d00780707168601c5006859403920f43c50f04900301c80c01d80d1103025099041c4225841008040d81c080b114500030400c19603646801600c80c09148650300034800318101032020400020280c444008540c1c91400c400132034418200e628050010480c98000b40f482c105441d1406c405441c0266550052400c00c000c5c0c0311070040c814854914509011001d6090002d038055030b42600800c0300410b0110b00205010b4101ba0440714258090b01d1b106200354a002401c00003e03403540a22806002e0459905860b0f580b200410741c2c82d48a1032030700909440c0040d405410290b081020507060038026035004034058081d40c28584d94020056041c0f015034444d0808000260140510494042d01031040c3c421190081d0344070804d0884803070048441c4040030002009481d804030040f64080817807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 128137553 1250 128136303 128136311
    0x304110409030c1b08060a0f0e030307140f090904050f0d03020702030c0405040201051e030f0a0903022a10051206061213050109080309030306010f2105180109050a03080a 75
    0x580e402500380801c411004001d1114000c0c03c4c03410007102d40111000300b0308102501c00b80c1c542084980020f101c0700d01080e60440c0b40025000c00c8000000c16030b4450303038854a0781c901c2494035030038032031060b04820b100d100484c03010003001d8415240e09614600a520510092851014000c920b40c01c0070404048081003610504c801d0015940004800303015860545000a243d103980c00102e62902c100c03a8843d400100752100c0c507031034468030310045104a14007a00095182c403180d914409850030640082e0059200c1c0091600400716105804030804080d204602122030303840116030b85000300c201a40118034003098a04403050504452075012008907841c501c0c00c040c0c4e80c41440790050203480403072001071940f04102040425849041095000b40100792240b91140505035213501c1280d10600248410302c2102c82d5034006d1801c4441d8010340006240e100c00b50486501c010203004204000038000341c2c0085441500a100c1c0e0403401e4003070005048800490b0030701910300c0201030801c1d2112403034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 128138803 1250 128137553 128137571
    0x60512010c0f0219110f030a080301031101081308090a0510050409150510080c071a01080c01080103110f0609040e0105100e090601050d03020102130e070921030522030803041104 78
    0x404c0c0b030600c1c1c0290f011600301a5015245c003c50741c1000c50399a031540521900d442c981c144603910000c6c0d412640702d05107a10703103860f01c1c8004540e41075081d00c290600301180b62080700040c408a0180c20300780000350603031140543e00d20025000c104820604404200005000d11504c3c0e100c1c06610440b0586252040c4540c1c0383c1000310b101d80c0500d0500300d007000403000104038801c1c102001c85089a401c03104010264005110302c5041100030300c5100800e105404224490f94029604d99049030b800c1414021074034004401d125001c0c00070009130b03038083d00410448010ba6118413070b98000c44140d2000054515200903088102040307a0080000d40144c481000400301d00000d070301381912070503501000440c02a01e0141d019000d504d44000400b402401c0c003040648002e0911031281d4271565440d000780381c0d600000704480c90003428103144d90807140c00540119000700004c000c10702400c20013042c0440c00280c0718100a0300e0760011540e1820020902c42401070090040070080002c640030400042e03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 128140053 1250 128138803 128138833
    0x10e0304090e030708070c05090124030e03040f08060907061b03120b1c020405180a02060c1501090605030d05160204050c160f1a06100c06060512010c0f02 68
    0x80d8890301a580d601e40d1032600c0d014205000b03691050381d21806203502d80c5450b00e481302c01d003921805003a010f5017920000180c031400c61080e4120085160002d40c4060990500c124007078400c4010302c42862008100001e040c9640e100788100501c1c841010341500d003030008200b428078041d580440d040007145c203c1c40091110644043ea442036241c10150002d40c4024480c4c000360696962942c0e01140220202081150702410229024402c036001c010541d44c601c654214414041440d10044e840600c0f96401802c015006001070407010048030400c001c040170b1100324041c03d8101243d4503450340003c100300d042c20070111841044c0340c01c0040c1008085041403902e03951032a0040c1c41551500c02050401d07240f04102c07108018003010000c100b025030306000194180b2124121422000c61556409a40111040301d008400007004550b1703501403907008070b84540b4940016110643e84000003d1555a002d09141d2207148100010a442c1c881d40400f0707040200c181d40010941d002040101d814075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 128141303 1250 128140053 128140057
    0x4110f070302031306052113060e0a020a090203100302060711040603050a1118130f0b1e090601050906010f0e041404030f0801060905040f0902101e091202091e0403050d0b03010e03 79
    0x11075622100411a0788c1d03024011220080c500c0040c00c11443c10380c604907802804280d01c00c4081c000c2d200a0300603a43c4589030b008a1100321003c04d0411517003181800107240050082c042d06c0d0085c51103140301140e07000040d0807034a05500440e0607a100f00904020024400340340310703030110111001c0d80c6c14120144002002640244040350712981042d0100c20040c264580c07800303158200c800391070b240c900b068050700842040c1a90300c9a40d140c0000285680d00c0000d610b030305940d4042e0585010791079440c010344a5241c004885024005c11804882c6036484520440d1a071903459043c3c0c90ba64202410080c0c480000c0001280030405104018400c56030008110313822a1419100050300141c00f80c14500103044a02009521409407248041050752100003024800390a85c03010070302031450700c8282c0381d4120034801e2006000320040c1440140c40c10440c03081d0300ca0112031580c5440e00e0341c940318100300c01e000c81d42103001c2600403441e01c0000600c0d100380c0c60444d20030341c02002a244035410440d170728 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 128142553 1250 128141303 128141347
    0xc13050c0415020f100609060504020c0307020d03110111250f11190b030702011d0c01030216120c050705030f070b1810050c1603080904110f07030203130605 69
    0x4030425802e0300c2041c0e4402c10289000440400607281000026020700300a4110f034441c0003005e500346113001c0769503d0329100311040810090021840e040d0301e0703400e10061120742a0150248a055203140c0d001074828010009a551400c0c125507440200007249050500c0c514120a20301490001a4000550000000d50340325040b0805411264440b070003d100b04644080710023624404a4000444000e440007940c002c10f1250000c3c480001401070140d426040d20f185017030661301c24014005d407540a40d0051885090080000c0d840800985406030001c01d1110340380f001400e1045c201040c00828812040901001c6000c0c240c0070081816140d0340c0d52082c09281d030035040000380b24a404003089920485440c01606002c48880900006030540e00f20b144201e80a01441134a40310f0b00041540d01401d42c1d40c05040715042034a00018400100320500c005d00e11240100a200c04110100e0b020b030080c40d109038000c55480d80c3c0703007441007030281c80341e40080c1c1440720502c98140c0009000070102d2103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 128143803 1250 128142553 128142569
    0x907120b03030c160518070e010509060301180b0a12080c1e070807150f050c010e0304170f0d0c0b07170103030f021506011b03031d0c13050c04 63
    0x451500204504014014114119450700c00020340102d000c80100324501c0f510010b4142d1480d040d551003e10490340c411814600c290001680043c4156006202040341800d040c0b4056082800f80c0002c10030310790003a04105100c4c242c1c80c0c2089000f0195000307085203100f080c3c80f000d0f011850302c041c10340d00e8008980300401d4003502203040403c90a080003c0e035011883d04d185400000b1941c0301c090784410503401141c1150007024008101c1510007d90b04030760150300d40d500c0f10300d03544100084520b50040400300c078055495100200007010100040c2018002c0c0011503d410b00c4c2d01a9110726085c11080d030040160090040e036040e40d03030040100208550403226550440d07513140b0013281c04155003004012000c406900100034582e02400200c60070314035400700c0d100d100278880c0229090708115800d0380050070901e03003000305062590910301c04074427030304000c1b410082c4050b080442c85085802030010780d01a50b9981d01c14070380814000d10302c80c2280c07020083d0b0b0401d04449001d500c12030141d011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 128145053 1250 128143803 128143817
    0x1151a071502040902191107060c02011e0e0102010605150f071a040308040311010b090105060d1d0c0114120f070e06030a0b010801140a1e080d020106061d0907 70
    0x40c401031091007580c0c000380a60455403552960700300c0c4025040442c0c84405045580908011240900e180308601d05000c4000d04040c3d02d8004100e5003110201b004904000301a80e50f5000703020801c003100c03010140e0752180d9103600b030500002030031140c0650005106071030140b2201c2c900b0f46000708481c400b1b40800c4510355282e46c1c900f071001903c031b280c9441507030b80c80d00f0034204004d141d40030b196280a18031a542c1c1c1940780540f010a1070a0781d48490807107600c4101c9000400c4540340500003080d000c0484080441c50305621404040050012100001680c002c0c65629000d9030b1300030405071540080304c48460a11550070503284030680003c2c000030310300d02540e000c101c0403800352021031080b10f00141003d603a0b00c0c107208444040e1800041c19808504d5800c000304000719003810b41c041200313000d80410300b99441e054100010030228070461121004a003c00b29203407600b030040c403000b903802c0d0b000800c1d024500b00004041d1071003007110704219881d42d000410541d40d0b2411a940001d050700c1c02d25 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 128146303 1250 128145053 128145067
    0x120c0906070b0907061b080d0c021c090807080f0712030c020a0311090604060501051215060a270b040902130b03241008041b0b0301060305010801151a 66
    0x540d051264010180c00b0011601c20004082c80001c0c00405480382c0d0380d902058000749a07150440d04042040007001c40d0300501192001020076448664103030b1407441160f40c0b0040401101c4031144071814000c000545801041c00051410002c0310010000364000713007450042801c081d52110054011909548000d1118205252003401e203520002c3c2c000300340180c41e50350ba2030000c0c14038064800070350003040150002002e03031405110325400c468041c0c5860389800b0340b5203039012460400600c0b05182c0040e00c48140380c191200c2c8094a08000c0d51740317522900500003810307407000c0d042c403034065983c103a502c20701400901c06010550301195900c0d203004da203400902c0c0b07004400395903070307040340c2d10005c80842040854880b044c00d42d04581428801240590401003d000785000380208000c0802c1d007401c081400220180650045048403400341c005441e01c50000500d243e000781c0c0030030000380c3c031000140a6683d082c4140c0d0100e2078910100c060041c90010483c4a030110450007004282c0046007078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 128147553 1250 128146303 128146309
    0x10020a03230f0c0c04050405030a0c150908030f15030a170c16230a03110a0b0304061b05160314070204021c06170c06030a0e060703050417120c09 64
    0x80c440710540c56584442280c40d914410781c12807500700d0014801c01000f10981c0c101441030318005c40d0000055842c0c1104103d081c1c4002e4510042121441031307142c425984900b181c411a03040522651055689050040e42e022802e81c0241545d03040010392034040c1205d0340e00040006206030f0080001d0202d00881c80445424010b40521140c14003603011240b44500c1c0d251090710070303075003000c40c100090320880121540302c0b55000286900403c58000c1440480c155662000104400400004040d611391281c040c840e0800e8601300d98550321396103190300182c40d001c03040a410240e0714100b818070305602030107018010152000742c180300c4102860f24003220080300b02d42002c0d40141095507078800441d4072980f40c001c80c0440c640041c1c50700f00c005c60410311486540341040c1d0420010b10941d44040e0410800b9070000d45880c15941c0d03501c0145854881c1804401e2140070140c400280310714241c10581c4940010804a04008504225200aa034590800c1c143c10007049041d082c1c480c1c9101c004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 128148803 1250 128147553 128147597
    0xb0f15040614040e0f09061509130503090a270b03030a11010b0a0b0c0f061905060f040501080c10020c0102031e0403171b07030f02060306040902040618050610020a03 73
    0x711510f000241c804000ba8a001030000c58028200e15049821f80d0f51003110801d07003515018540e0768014101400308038a5844045860090703401030f4140d901e4040c0d5038001801c52a8150b102440041c42142985840820641001100500c01d10240316004080300000c0d2603201d91400401800382030a0b103400c560170254480b400c2d96601810200c003141e110044074140d0740002801030310303070310916044180c45140400c80c14024000c051000e00010108168031001d010001c1030380b07421001c0304190644907540d5018560007803901001904980001100384011042c3c00c00380030080d07502c4070349025034a9074000f00b25440b0b0029496051019a411200030080d1300c0781c2c5c1c0c0081c01c122085454221841c81c150010100e60180807004000d10107965140b980311346092001500c40c400a040c007101504102000310740c400c4009000080320030160b0300240032281c160b00521100303621042040c1c80b8a0041c842d05030440421148000b2400d0b0102c0020341c1e407582c050b0000c0400071509400d020a500c1841c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 128150053 1250 128148803 128148809
    0x70206070c0f0603020912070e04080c030c01090f05100603022d03010c05030f0906070915110f0c01020c060c0d0c1e0303090b070f080a0c02030d020408010b0f1504061404 75
    0x80b00d00d410582d1210028043d4000031003143c4184110300304c15000c010002400e00860340b601040c0d0f1041e44d1251611186600074200100d510f0104000d8400d96031420f10411a050788603400210f051502800d01c3d6180c14002807015683d1380c6012000d00c00351740c41001c244c0c40403101e59001c900d81001c443c3c0009001c1d03400c1064a1f0103608200c211080b494201c0080c51040316000c080c1c0c0ca19030b460152143d59210140c41c0e040116800000c00d115000c00484ca010125045060400c030040683da071251422941407001e115070b40114180140740c0d80e0503c806e1110440444a4600700400024203544907038190080708140301c187d052400400c2142200290147c69400c0e030340c1c9081035030f424064040c3c2000131044400c20341c80000074040600071140c90b6509001903899034240c0d503500c070100000380070b0998490150720050098814840541c001000030303004040000c03d48000c0b40d4140400d511401040f01c2c42441c13241002283c1d0614001540c0840da55440c0040d0401f031101d00c06610740c82160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 128151303 1250 128150053 128150069
    0xf081911010c1a1501050301060f03021b0f01090311030a05040e06030705060d0c0e0913200d1b05030d02030d050406060b07210305100501050c030409050f040606090c05070206070c 79
    0x60300041d44040c1e601c401c0b885060a00c0210201321101001110740744003d02505010800311506840c801d4400d0b4050040824503850450701241004000362810030008910b0a00b82c0d150b000c1c440415a005d01040c503a050340000841c288405441d000e0820700841c007462804201020009031155001c000c080e00400307000e084140d40b203188036104405040c5110700200483c601c00f040c0d20407401c00c4003a040c840c1e03070004c6c25840c400c0b60f0b40e9118000c03403504036800344804040d144c000c5690390b0354060020080384100710701070030b02034071480e0346001c012141c1c402032213500b20910102d0f8075a004400c4070030f010191000043c20341d86034948031000300b40c80d8101000322003001c10300790108009000c1084c80c005c06031052407440d0450010071026514211200d0a0900c18100100459400348015109540c4c000041d64102910743c480e00003103400c03c891400e14404030000f0f0206000da0791041101910b00fa02c0180f01801e604500071b4107a20544c10001c1c0140000030303000e400e000070054441c0140403c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 128152553 1250 128151303 128151323
    0xc0a090e011104120b0702060112151b020703021503040f030f050c01020f091c0819030b1e120102040305060f070c0611040501031802090601050c03070b100f081911010c 74
    0xa0344c10621040080070210b52001148000c55022400052034904803610000074881c041d180e50349181d02d10b40100d658000e030903181d000c0f0740009030494040d0324104500e44e00503c603280c40c0d4010402d03030704104541050800810800e00c40458441c4042a01080d014141101ca61900d59401c84481c460901e0b107039090b500c0400c100d04080080c1c0c00070000d6441c11268111000c6204c0d030310101603107003c0002000340c00100b0444a0580b00c14200c034110302c82d44e0800154003000700b00411070198020060503800f820030002a480c41c0380030164840c121420100850a1504541d18541d03203400251282c0c0e2030f10002c0000400e00d922850041e0001c07540700006101d050346516110342190050302442d400302c0c2c10f1000c160906c85000c0040f8210f250020303c0038070300c0e07101c10006540d958443d41c81a40180004c010450121707441d58051402414641e40c8403144038900350301c29000e0302d12500b0212664014810740c90403607403030320380c802d6440360855200a100001a80113079442748440d14004c02c51080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 128153803 1250 128152553 128152559
    0x40f1505010608010e060307060809100f090204290d020f10030b01020606030309010801120807050f2b0c03080712110c0d0c030906113c0c0a090e011104 67
    0x1940c000c41c0c100c8549468645041e601c0f50f08103403404c0700480704281c255100001c06c001c0540301d1000941c0003e1f0980540703494030404040141954240100600b00c0707a02d13604960114141441820108003424050410f2503600864060011060060203440790300340b005440107558034030f94201c000c440e00614603d8090b101c8900074010f40071454115026010300070009580742004012207026071016510640141e0a02e00380c031413000030151040e038028201344031a900007042044150440d80c0c04400604d6061003105600c1400c249200b00d880303142e00d201e2500d2200c503402210b00e0306802d905040c058240d549070a021070305414119404001c1c1c0c4d040400c0007203e040300704000c100c03100162042e5400d102030502c0030b40d003000000d41c0c02800a80500005c206c030340d03c40e0f03244005618110069070404185100354091000302003000301c00c200d0b18400700d031521010400120003d00056000742000610040008070007840c80d109420003071381c40d2081060f6517070082d804503402c8001140ea854403561 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 128155053 1250 128153803 128153843
    0x1005120a02011119080c01110f030a06270209040e06010f060207090e07051e0607111908030409021c06060c0b070509030a0809031f0b031515010503040f 67
    0x200c80d081e4003140018424440c96040481c00e8120714a101031000c800c603c44e9640d00442c3e9000c03440313945081d580c454044c1c1c0440c151100400007000ca21201036100c2c2410211b0404951407030348501c80d4455a0100c254601054901d1403d020000d0b0100685034041c3c07001185c05006102c0c00240710b03009250011991400742c005440549a5640c02c03540481d840b014020100e4030402c605c0b084e0f59121240401c010300e000c0403030b0b80e003008003503001c250f0420058020444a42110408456072800321302031074000d040201145000d110100c000040700ca18002d02c00b0b4403071080e40030b045030b10764000072044031035000c0ca0070342150900c2d800c02c100b01017507940c074004002c000c0d808012507030790724a0701c041010345210b0350a6135404107004000c0c0c90500100d0395076054503800740031016054000d00089180280840380144e68000c040030021800d40302000815040005000302668030943e040203104010003100000c101e5610207082843d525251802c00706910301c0031203c02802c40d40702403801a1600e03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 128156303 1250 128155053 128155063
    0x120b0a0b1804020708031b0d0203010801020a0f030b01080403180f1206110c0712030c0506070822050a0209060a0b0a0201020c1608032d040609030215040605040905100512 75
    0x14080e0307004010840110400060784100352010340002020700100701100d0382c00310303a0401d98184500340c601d444812145030701640c109a004810707596000c2200e2442c107801060412011032185000c101c40c0000d400081e08003039000e00b0250412406900201c14820304e12414405020400342085040e55100c402d2a003c2c481c6050465440b400c04462454020b0100700752100700b451080035103480c5042200011608c641c5610950812450080c800e02040c03051103202c8c015081c41d03403460701030300d0001c81d05d4002c50310300350303048070114464080040801c0c0c01184081540e903040700c4004003a220b0704000f40c110015604a005040d20004100d07120ba6015402404412a8403040e20700003014641c454000b50340310312074501c803904104908500700300318080301801451001d881465500c3c4040002e84590001e411800220304805002e2041d031409640203c40c0d4555280e90038501424285c0041c454021449840140c589510100e441da500c00004080039080150800c0651041034110698038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 128157553 1250 128156303 128156317
    0x110a050a09050417030903040920040e04030e03060c090112060509010e0717150103020c0a051903021006060905100309050a1a0703050c09010c020315010801020415021606120b0a0b 79
    0x2a05101c80f00382600c1c2d80400d491007400d032003011f9420030307183c403001300e01600c0d003c42d1902c000c420402c221000d121540380503001500440900841a24080c0f902515244100b06502c1c032960200e010008501441c01c200c5442030000e01c0c0805000d0200d64840c000340c041600143da000b8154000850390b022140d104074416107082e43c070380c4502100f40300c00050f03190050b1205c50345c2c0c858811400c81a9402030300102000c81040d400c4604101d100d0301d6890401000b188100030351a0114141c01c14154100b0900c039040c98040b5080000340d10308400980780708890310a6600485104412966160180d88903220003500034003901c0d03028001e0300d0560724504004031740901d01e40d424404150300d64400c0c4203640c41210200d1599241080710001910000c2d8821310880e4544a4001c0009041142c086058020140040050b840e982020300c00d122000c2a010050119441402501c0036001500020303c1114001c2c146060400046542e0300c014015540c0519000804014005242c0104800500076 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 128158803 1250 128157553 128157563
    0xb0f041b0221090409080c0601060e01031a030a1103240103171201030303020f0d0608060f16050301050411090d03020c0108010602010605090f1806040c030606050901080604110a050a090504 83
    0x50036688421414405a01411114140c1c000b40b182c3e500c43d040980c802031606025881c003608064010540900d024000d030040c00008441c414880382d02d507054001d0110190101301026505d20381038002c00c3d42c8540c040070180003a1410306501d000ca890501040304503a89483c080404005007207814072111000b0310045500c1040c200200710503005080079503008400303170301904186900c0d40d1421000394202c1e5000b540e45c48800c20042c005400076108080051400710040c162928080c0404c2605680003000300e81c0c1810000780c640246030307018044a0560700215400581801c8445227400e450142e83c0340d00790488610300d049800d05400196101d030300c520990700d40c0003171380e01c1d800c040742030b155540304164210050102160703501c24188010b60b800006001d10070782034045201490700c1c0010544059408094200040c010321185010b60f4014040c180c3d203407240b551410b2752595899100074009003525440ba0051605940c0b0ba00780103008000c02042c0c07607403054480040c84018881514121a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 128160053 1250 128158803 128158813
    0x209090105040b070f02100e030f0c060105040501050406030b0406050702100614030d0e060d0e010b09010b030a0b180f0406090507060323090706080709091b0807021605040b0f041b02 80
    0x182540300e10010404484161b024018021030410a9405084040e1600c03101c2e000611010b0400b506641c050500c074016000200800c1d40760400b40401c03182c2c1030704040d024130b092030002e0000c03441154600e50455030040c4005281c0d07a07040c504905260000c8030301c221260403d01e00140c00c114000c1c0b40341c01610114281c58000c80c15901c1501c0c0c1c0b04001201075000441401106d109070b1056000214031400b0030000b00c6c0c0c004500f800125818400d800070b4424036404014480814120311030042d024a061f039211411085059200110305002440c806501010000003410881305da00b1101d01540d01604944005440b850080c028210007440001051581e654402d040c1044a10482c01400000041e00e059801d209040341c40d141c00402d40e01c1400420040000e0b85400782c070803803120703202c0100c00d864a00030740400202403540203010001103621480885030300340301d0081240100d50040310005060451400031130300e811042c440b031316800381c5480b5105502c072002c2802c911404449600f550 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 128161303 1250 128160053 128160061
    0x30c0d0b09060307060f0513121707031b29221104051012050d030b010807080604022b06060e031f0f06030818010305060a120605040f0209090105040b 66
    0x1c400030044620035810703030080c071003041140c5c003440e0380320104c80d1940b1b002440c00c01800715a4800d582145e02005142800c854500d007848080c80a210100c626001031925000341c3e40c030000c3c02c044021250f19403448841c1c02803010844600701200c142210920500b49061142d41d00004030300e0203c3c1c500a1001c10103614a00d0b03030546903090fa903c15405800e01c04110603050600c0000c160007042c005407455804804621140c501420042d001d108600528074045903550040643d9900310782181488203010600021503000007060707a1169055130b006890302000c00c1d030500346204603003615904602280c042451002c40b6084007054071042d80b140d600c0052540141541d44119201d18815609240a402050102034004210b00c004805010540d0350301e0f5245c0a402e40d000302041403059039000c0000c00d81e540c0600506500070f400701c982c00b55071882c040300b14031002e0010b00004d007400e56a00c00581001060715096079101d8000d00800c0300c514017503801500800040e103043c0d40c61a0782800203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 128162553 1250 128161303 128161309
    0x6091b05010801090207020406050316060201110a020607030908041e0e09240703061a0d060905100506090402070602041509080d0915020c041104061404050609130b06030c0d0b 77
    0x1804035030381079654400380d83ca0440e59200039000100e0880e4000e81318400041d050307404000c11403c030706202098209403864401301a00710384d07003255040070082c401c0c05990544e64011031142c0d4040046c1c1004142082d10f403510150500c01c40d04030b4600b000260708032030110212500020151106098500d5590702e80c44e070b020b0307504d1482524080003417841c489898000a000343c81140c01010b90b06000c40c6080c0c84071880c000400000c50644e04100700414040b066030094040c00f0300810b00301108000c5410a4034180002442a0003102d0103481d002408030441d440b20750485105980008045444070744503848010000500e500e803100040d40742002050741540030410350950144c03611064400c61400d452000000042141101507025111151405846e42c1c010410009118503031103907140e003800005050411a03103940400b412080c0810701031511a88219512444100c0b225451105280c0c0001c0c058080c540070907420a2002c0148804400071801815192007029418018601c510703042c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 128163803 1250 128162553 128162603
    0x50f0c030705090c0306060f0712050309060a0b0603130c0909030309020a09020a0519111002030115140a0503060619091409090c150c0715080c0c0601060806040e0a0609 74
    0x51a002c0c000170000b01786140307031907002481e24040301d08401d4100806500ca600490040c0340c06200410000020401201c1c1c05101080d40030f0b42c502070402c004490640803511030300000307014819002140041d0360600c9007002824000b4038040d50148444036a83c80e00034080c2c41c142c0402c9019004007040459104000c0c0291000c208040c0d407201d0404003c5204656182c1102445409200a4040403290b0140c1400f14404841402e4005603513075140c498034003200f05034481d20900f00000806048218912001103804510301d9180007600ca4039654005607480c031030f02401d10700071904041a4042d00e60400e1039031040b035084100365002a079101e400d100035490704940d0303003849801059003003060b46000c211104501d40500b0449060a950f0741c034440c038000c40d5401003c0c1407a0100d400303210710ba038440446a80301c405e150580d4103000092480b56a900e03c103020b12004d009071400050000e0311103501520301d0212880c1250060138050038140c00030103056000744c42400e58111000106041480 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 128165053 1250 128163803 128163811
    0x8120d140c0a0302090409060203100311030c060313020316120501050703090305070f0510060f0f1208040603090503090402030420270406020f0a020607030b0a061b05010603050f0c03070509 83
    0x3411510300b052804080380254003d002d00e03940240d41e40c126802140592000d1841201d00e6510f601015085003814590007106100e410b100f684240c034190410303100c40d001c1d00e408c5111240c03c84c610340c400c0d200103070400414001c641d403606101c1c3c0b40000c4400091003007003100c5004170000c018588800004800b0358020b12009000f2035410400c600000c2c9028006e900348601a80684a1070303c01c00302e01c0b106036400d548c0f0000e038a480c1100c050103817900844045006000303000565056020540c2c4140f950301580c0300314020305945403824001e2101c00c1c000c803030446200800c2190381e8901460142d4a010b0102d410800c00c00d00c3d082481407a0400300c00780018136040c440755442c01090310328040a0900010b00442d8100c0e005d128800351000d40c0e201401e01c11945030081c155a1034015001821140c808103600e100d141c86c6081004801d8110100c4855610400204409110305082c01e50242885a0005000f0b204040c2040d5100300f01080490000104509686125545038200030f01600e05035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 128166303 1250 128165053 128165071
    0x3220303140d060803031801050606040e04020907050403020301021c1b020717030705240703050402060d020a0e13150b0c06151216030618030c060f0608120d14 70
    0x4001d40c080715054a0140c03800905500e0042091500c81600354110381054464582581e001035414082ca8400c0c0189a80480103444050a05240c207051384188500904040d008041d118082400c0c103114408660245070068002d55544110f030350941c000040c29031703030005550b01c5d100311040c40a00d501621f01800400350f00400d10542428402d00f18544981e040ea180c51001704080f1000520a022451030b9800f40c0c12100f001034016141504501401800310040614240400005036100c1d0180c4484916000d801030300d0f180410400d44541c0412442c0c031381d10041c8c106007071214003003a1308000c070340762201d489000d0300654034801c4808a0281511130120340d004080003504004080d0b4030444101030040011440405900046003004e081c0010204d141c41100c03001d20074498140228204423004400c1054900410b460040440c0801080242016100c91703e42d07545620507008440600306030000c2d00c0403540d104c40c440703425070710000d40d0700182030030f10700c035819089548880305101d13507001c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 128167553 1250 128166303 128166317
    0x180212010b0906280801020403030e010908030406181206061502030702010e12031b070608070504030809040b1908031206010804020306040323160507140303070206030405010603050604030203220303 87
    0x46001c000c13107959038071044800c42400208408604000c94500f100500d00c02000580e0b49055040003080c0c11040da00c490706200060b030f001c00121070004125400c42c0c0d968502484070340190780d0b00344032800c01e03540300d800508800d011010a21100c0e5000d0001c8580c00310000b104a000110140d89a01440324040d000c07c010302c0c0000409d08003090300701841d01502c02038a1402c0f80c0b00815a80511003107200e030b04a903001d04028000b90380c1100540350000400d040c410700f0240303540d5800080e845504081406182c460401d0200d07912000c02c0c021000da1046041c10b007190300c5013109656034100c0c0741c5c40002074000c1004128907500805001e80030303903000307006496141e8480d141070b130340a070140440c1f08105556000d40c03460040c282001e0400b05180210813800c6039228204646020b02c150000700460320456088000b03944c0c00012280038030b50644105d0b4403951981442c60041c41c0c4c5070f00240c00303409001c08000415502100800c00c079100d00310400c80a446400c40742e8030314207040c00021f02007089 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 128168803 1250 128167553 128167561
    0x20d0e0d020f03010c050307091d07050a0c050106060e1302030f0408280917010e0615030114040305041d0606040302062d04060306060816030e10180212010b09 70
    0x115014244040780007030140026881100c010074219a84142d841e800104044184107481d5800408100241a10000c140d0a004c0080303000ea003455020701200e042c410006148980c1a0040350171048007134020000300100303a80c664020f020244402200e0744030310740410052146242610075240280340025901425607580d80c0d503103a1903800901c50a2100107a14800c1e0100509a0b50f2805404000d56a215a19140107110310754050f691071407000590400440350b0119200040c0a5440b03400b038a510040f091a203030100340101307408803000044800c910100018950440010300481e1400a00031140101c2441030140044055070510361008003004200b000d0301d0841c000c0c09001d60700f04c401200311086009001c82701d07109610300d08140078010900f007214503014840c48000302250300b02000d007807400c802e100c0011a9440c00030014940d88801c03024001200300001c02c0b600105030000c01441007076840381011300d10381c00c0040b44200f540200c2d0305c1d211181030007078154601c0b000e0302940e0152030b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 128170053 1250 128168803 128168809
    0x1e0f010e043e1305040c09030c03120807021b190803030a0e071710020a050c0f0d1101140c0d110418111914090307090203060a09090503030103060e070e0a020a030606020d0e 76
    0x90406128100406070401001041c3c507108127200452103070650100021000a0190112800034140300940d00301892510925500b240e000b0500e402c21110002003074910310f21510107034441d030442e03244c6220110400c0001102640000c00000c0400d04440440356150316200f684050021003988940120903c1011a4410b80107003050b801c10313062070350030410107018440c80e05501003600091540800d200f920140c2d0400840012001b0003002844640c11102960000e000c2c0079017103c0b1180400140c50300d403003200e40c1c8030591203000d40745181d0740d41d41c4d03a80c440030b81c01d0b58082d26514824640445243e01020740340072640407070345c4082d503094078884442085c3c076080d007002c1c03858945035401c0051140d650f0301070188001034000940c00507180d003070407028444104600e4100c84c0c082e40c5451140c00100300c0c004256030440303a11010103c0d10310b0111020f1400c05945910203050007a00300284000020710360080c0054140ca9902044440d698400403030f6a444038800c0c041c0072680d407000c0e881c141d003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 128171303 1250 128170053 128170061
    0xc100b030a050d080a090213021206060310170309040c0801080d020d0e06070318062003070203061311041a1002010b060d0e0106030506151e0f010e043e130504 70
    0x8000b03020006144491b0b5004125032543c00c01e03103172400660021304102c91a002240e000e810081c1580c2550542c948000400200c0489000d050081c000c00840d02d460906d0030021540d24050103003080c020b0300300d402c10140000d0f600b0702800311180900300c1e56944107440040c03c0c440640032983d82045031000403040c07211540c0300c58815010000102d41040c0c1400c0e0040d60030300288101e03994070182d4542426258001203207040d071040260010005280581e85c0000c0e0030703030014145420780301400d40070710700a50f004800050840c1c0050800ea405a811020b9200310b9000e40001ea4500c01c3c0300f11049001c030300f240d0705011255840700c0c09005d40480001d80d0392142040c001101c00010715985c884e241d8a1502408581000c2c02520b1040c41680504040d0050146081385041d4024018003140000d41240540144d4a0400003200700c141030035544e940104600b01c460080703440400007100c0c44808409060208104042c00581c01c1a90f52680c0d60115040402c9180a5180403401c020800001d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 128172553 1250 128171303 128171311
    0xd09020d06051f05030c0a0e060d0b0702030d050606160b1906090903090b030c0a0503040825050f0a020a090903051c0906060501080402010e040507090b0c100b030a050d08 75
    0x15220300103000503101c0e20485014a5158034903c1140140707440c00303a0007040c1a00b000340030390001c500c6180c403030b00c805480a0503a004d000489005617221008190521030310600075000010200a00007215000700003080e42100c90802809640d4514080c40746500c1202d85a00641e04500c5030344000c545840c40f0175411001400b00c46818009890b2400c06480e43d6820610015035030740c00000802d600401d00b4001001001401820361034991060403190107420308220500c00000000340c10080c20500f242c00b4002e1034102001c480c42ca16a1008100c10101000c50340c81c481c290b04401c0310740000400465499000b446c400d405810019950003810303c0070b004400b8043d01344200c2e4668020083c1103d0792140c16000000ca1011a041c1402500c02c01d03444603040c003d01c00e0034400580da00400c00600b0316415a8041100e84442004803000b020356848500060004a103c400d118400b044140c5101840031062060300c40080405440300c1d507405008102c0e03070152565004050003100c01e642c1c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 128173803 1250 128172553 128172559
    0x13030f03020d0c03050108070614030f190905030d0e0304051c0203070f06020610090b09010b1e0d090c08010203060906010f0912080c010c2c190803031015050d0902 72
    0x4007902d0000c9a000c0d2500c030408007011030380341e0005101c0381d03200b0042040140814506074805121010201000d8030000e0503920121501800180c948082040143c0840300010010000110507080c100d807650042c80c1000342060800c03182011440000003603070240c0b80010b0414131200d1508e5070650a034441d02d54200e8041c003a6071800200004800103031402000035802500701840c080c49424481c01e8150841c0000e00d240c921984602d4481030708190540f110649965540c0015a411582c801c009107103c8001c0580016000b442024642261807400c3c800d03e10150002d8940c0074280c240c0c0000c0750101d4000d2015030000d88650b1140500401242150921034006a20351344059450200c0113016100010005441d001040092003801240f18041c030b402a00c0002501511080c10b15a842460500c03265412561007980d400c24110707040001d115080070301c0c40c0ea8041c021740f41d40003100c040030305100c8403500007502504808a102d030050302d03130340c2c1c00d103407000081c0a40004c103d500e400382c0e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 128175053 1250 128173803 128173807
    0x5010207151103030a060515030f01030b1801050903040609050901051c0c090f021902010e0c010f120915051003030c0b0a02040902070f06050c070f06052d10060813030f0302 76
    0x40c0e800c006200950050070305c03080c0451071905001c1400307075031400481400300c00c9104004100d14101c1c0145051306690340301258010b0750301d0704062043e12400230045500030b5407922090292b007203000401041110403a803581740e12380c3e96450401100d0f0f91b003440782c0303500001c1d5649444803210465010301e4805104031880c0201c56101e44414003254180404100c200f0707030009259481c0c4100307040300d03490034405100074004102c085000540300c0303e903403032100c0c14040010261800d65008641020004008000c10032903042c09080190750503040c944c001c2002450400400c14132007040001109903034041c1c4620f103400c0c500d0703924001c40c03c50060905c070805900f0f00012450318045e000401d542400382b5a045251140350400c082150009411103030044002c0000c440000d0314000c44c4a021904a64001215502c24511841c200700d802006564111341440e041c510401e411000b50090b4141401280400d490306410340c0c0045013510441807401003108203400107481000543c5260f0064903000d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 128176303 1250 128175053 128175077
    0xd090204021b01021c091e050f0f03030a0f060602060403111c05070209070e03120702150f0a080105012c0109030209090f010e0d1e1704030816090501020715 69
    0x18040c80720351100d07102da94002a00f002e400b00603501c80c14001c0001103040007485015524207041d1a000c084031858014642c0f9210207000050022500501140c800c1e0780d040c11940e0300c00c940341e5004449000315240b414441030b1801c81c051140000303a9540b40c00400740d40d112a141501c480e01c42d20300c43c02c61845200440809030b06503a0704003401c1c12054543c1901c0701140d20402c0f5110b44010540030410100d11444406070303800003451300081074400304103981c41c0c58600100c2c103002840d4030608a00f0000107940007403240100020a507032840c9039190000d070b03600ea00c0111a50841200e418500c1c2140b60705004141600b403100d5072041c1014180f855100f980d945c00b2074400c0728101c5645115410031480d03411504400c1c01191440300783d15024050703000aa0f08090148008900500035501001d4540c04009000340303441d404540c00700ba031140d81c2d440d181c90010300c020070882d454000e2048000010700701c9030041c40e02c40e0070360340160003824000e070801440d83c106a0340e240e200810401010034103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 128177553 1250 128176303 128176327
    0x130b01061b052e0c0207090902040b0a0605091804030203030c030a021e04050a0602010621031b050604020114070506150105270a050105070b0105010c2f030606030a080d09020402 78
    0x607120f03c02ca10050302c0c02c48180041101d4081e94031000011525007040f44201c0d1496006c1019070039a40b214200081140c0c6a00102c1c0c01084104046500b105002da004104560040007400e900c07881104c40200307114130b199480d0030140056038001c016900a1011504550700310703020711744c8001181350041c100b046504000a09415480119955400000301408141407081003180500a103000a02c907035494003881a0322240c03803851a83c3c000c0c190400d800201445140c20601c030180710646a5443c41355030420381c1e1540402d440890105906400b0780c14015501000d50340403980202c044e1071243e03140c5a00810301e00005104c5810000304105003042400b10103018a110942401050340d030401000a0010400c3d442d0059418041c0c140080d50010320303581c803510705440c1c0a20700040d140401d49800014222041d50044c0c500443c868054070149054443c012900700403401c0300c10f182c076008141071319000309000260980c04200325901d01c07d070860300141d5441788060401071030001c0c94050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 128178803 1250 128177553 128177563
    0x3112a150a0f18151505060409020901180306020405190e0601030504021c030302030906060603010f0603090221030706051f0515072f030316150f0c0306030506130b01061b05 76
    0x2040302c40003003e09509213900d4a5200f2540116652010104410704050020304076004d5841280e894640008115585901c0b40c12004500500144c6101c04180c4a16100c00a0b401034025607024418140030008001d0040c10007400726440f00f504001261103840045000e070100074004c1e03801c603111411000311759680031180b5042074060754005881e402d00625440c1131060141c0628410b03202807006006111400580c0302c202c41043c140041c00c055a40b010848603042e04140304200180d103844420148004001845154801c50081040e40e490b443c03500e0030480d8003da480041191044140680d013070071003400c0c2031460b00d00ca0721410002c841d9610401e14550322002000d801d07880f1816180c0840908000b0184e1030f00702c020f182001c1800c100294004100d90300074102c19a1500312000c00000c0354002e00c4ca5410740c11050002c2800703600f0103005001c091008944610034500011003040324104c0420f000c81d400f1411a00d030703034640201140d0080c0c0740300c0c00c0300c09071387e0021241000a81c1000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 128180053 1250 128178803 128178851
    0x309060e070b0a0e040614010f0e0604090b0f0919020a0210020d0603031805030307061812020f07050105040e0105060c1203011409010b131503112a150a0f 68
    0x320483d91842c2420000340030401200c8403500990a10900b8885d00510016607840d0304800c1c40d100e658007646d04000c42d4441220000f494108800003404503100301c0c079400c0003040d031038203544081401d0025002d22108850495429400040358401d0340e4008002c0d170002d00012110384119480911415010301c01c903801040742d0042207544190070003c168006007444008524004500c0445203800c0200c1d8407031080010050401b995101c07401e0000075a02c421040e0150481c1c01c0c42d010b0754061501940d01d050103041c3d8000c1c0d1180c404002141c3d8851000c480945e10404071000c1c1e01d03407a00040c010310740c00c040d0051a090203180c3d511445511141e020394001c164000c10040c0c94001507007480407640060304002c030000c000700103283e191810740d045003045458180311380e8410241c40000304d004001d00744454841c610009082810041e0590f10550840705440440c04204244240c0a60b20f4808400040901c40c5000c0006c1030304103e41d0092032058680c1c100807403e204503c2e070403010081620 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 128181303 1250 128180053 128180069
    0x6100308210f10050d1a0a1b08010f080127050a0206070b040b07030905060601210c0809060112030918060e0c030f0609060a03260301080a030f03090804060309060e07 73
    0x4003c0240d010280010040204410b032140742615000c2d0f100c500b41c81290380f445407030b801c20f0403011070301d084020b82c00f00d601d04007a096400142e81201c0002003001c1003c7c0f003140300810703010802156248040c410011300308950034621403406090010101d8000c407000c0192694050b414480c0d015886180c001c180305031080d80402058581481d01075083d400c00342c009c2003003600c7d02066000194000504e503800c04024209101449601c0d00c50a10001c000354103060b0890900380e524400641180001c2e004418074015184980e032141010540c1100d10b0750042c00141900004000395441c03000c07105022100c01070b010030156210100c000c8803076016a440b1811210000400404c5080d042001e904424100e400c500d650508000198248a081c0006090010887c2440c05901002010b5502400e055040c440d182e69403080c0c13072500c51001180030f07404200c0002d001d15229210b48104454141c0c00140f082c100b1b810903504a0090075901c0044a0641d40d803000c40078002403c02880300200010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 128182553 1250 128181303 128181331
    0xf06031a06160311010c120b0d02040f0e0c06070804061206090c0801060314040c0510110d0f110d080a0513050a11010314010b04090504020102070e04030504170610030821 75
    0x2c2d250007082c546450018001503454401004031095200c1a2032980550070340c404500d00b5030f90360000d43e400d0302c8030100a40c090b107400550314880e4295000300320188000b10036200e44802c0f03a01131081c1032042410040c0340180800080c00818000d0801442d007041c603841c0080c4068442c0b5800040b10802c84441001c84c01903070040220b2585402042014040c6198140070390803d540c60b1001c1c0045070203103a114143d2a280c60742c000e840f9400480d800000d400c21110014903101c40580b081210108410000f284840ca00b648444009a80185092140ea41e80890307a0382e00710000c0104809004004940094000480415420071505061a0140280740c0c0c1004000c00007400b119a00220504988115401000702810780310071343d011102c0d400d001084c075580b503100403410302c102c54104408403071440081c070041c190f200c1c0140043d10920350121101460020940303903950000c0302e84030b40700805418140001031204e0041c0100c5d116006000c56200354914020140380c5048500121a00f05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 128183803 1250 128182553 128182597
    0xf0308031503010e0c01050a030209091602010501080d0203120402010507020904060609051003030203030c0f04030206030a0603050c040203131211031c0c03050103020a0308090a15110609070f06031a06 88
    0x11000c0e891444007411802000304005000a46445080343c2d000141808400300f1458035190281d0115814503000425040544c80d204c0341c540d03140a040b2007060015841e0034000b0034041c200150403107649d2103d80040d401c029411014540c14500180100c1c1081740034880030b030042e2100410382c0d00562142d034010802a00780280c1e0700c1280c90052503c0071a810940f41040825000b01c01c5903080144035030303100d81da0f05140ca12409181324a51000390418400001c10011822a521040035640b096007640c420202000070401680419940392049080d13107071220001401c1e007100d10f0422055420b045000203d82c411039030540c1c001040c1003160102c0090000b50628040c86580d6481c151820204404d50540c0c001c208210058080100f980d0000243c00c01182c0e80c0e00085001040c14040701c00c02540411401400d4544c01507440030b5511440f40490200080841d05c1015591505840c0c81650b140450440240c0034544d00c0741c54100040d0300c3e81079079464010040c18000d0602c0b80207007294103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 128185053 1250 128183803 128183821
    0xe0103051b0a030b0a050d05061f030b0105120f010e010b01081003030512040c050613030b0a0603080a05090402040302030d1106010602070e040f050c03010c03290d020405100f030803 80
    0x1100404080e61039507428000700200114400750b41410040b860700180164590022840850b000e4004603448111244e0702400c00100281c000d105215440c600c54203000d118242084084480c0001400340710320f240140954204281c02c54180b4003205d0071500a402101500d6086659140700c1c1079040c0d46502c8016601e5800030182500100841400010f241c910f48006205015000c04801d541070200d0100b001c1c40245003035800500802071105075a080f0b40c078080101c105aa100444540c2d00d18000a151b092072071107000c040303a8004051528010b150303142221503034011102c040d4090740c240004005a1030801c5140743ca0740e220b89030200d400300b09140061800c1030581c001070440d48001d200780902940e0b0220313250055846a8058544906440c0041c140300280714165019803030050240c4025500d904203150800c8448001503003c400504000d08103403000b0349080d04496030706079040c0142450f60046034030880541c034542c0c12a1b01c0d02c82c14042d099883d4815110321402205202c4c01c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 128186303 1250 128185053 128185061
    0xb0c090102120c0a030305100f08070608090a0201170601050c1509010506100c110105040914070f18031719020307020306010e15010c060608030705031e070b0c09010e0d030e0103 78
    0x49a02d000180c24840c000c612180c0e100d840041c0102050348480114480d1100140000040c141800080c1540b540b51150540d80da901c80c850040020842c0c004510140e0300401c10340241074040c0e4850304401c00074a200c0c030384182e0240c54141000b2080015410290382840849016801880003400701d0521141c0b90f82500e20281c462440b40300080b00c10014030f43c102002d01c50702c0340e00171041e952908500c1c0040c0d5990085900000b00541000c00411b2841c440d10321040c030070807440d10b0349a0380c01c003030f020111501c0d5841e40a16244000014003480454904554401003e40300503625203401d600c034510482d89900e41705190701507070011580004501d4207101d8223007d003010340b040c0080c2e450004200d200c13080000d052503040c81040302c01281440116004280500a500308a03a502c0d0074a00d0116a2644400000f40e40705e0f0012201820300540c02c0c1c2103481103030708084581e8003526542010822a80314a0500e4144100451481c825485107128008494026120300b07001d0187d07480094252 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 128187553 1250 128186303 128186323
    0x60d12110706020a05100b030a060902150a020a0c230111010204080708030318010903050708030a0f1506080f010b0f1c050a1d0d05030a0b0a03080c030c0f031c05040201020a0b0c090102 81
    0x87d00380060340b606503c000078010111508001d003c00d018200d07002182d102110345410917481c402c0051510341082c0c00292440c0040d00c50407048032610343e11040c003116842c0001c000050720031041c40c4840b0ba5886110f0742c80d000604400014940340c4c0c1c610810740341902c194408103140d003002c01000101c1900d4610304108a00c40750080c040e0b00002d690090803442603181c01400824080042140c01045030310285c070122800d0390402404508803840420340400c1d218240c0024003610002d515020f0980129040321366101d4511708160807041c40304c51503040b05a00d602e20001e50328101004991502800d40a083c107140c0016a00c0321091000c600448083c420994981c04900c0c4c079040903510000300c0b0340c443c044030320005904d04030340009200e074171031503202803c40724012400c42e4814001100410002e000030086032101c082d00b803945503c1b400360300d1807040389090035007865041c0c0050f03401c501d80c403c1c41403050f04e044180d25982c0c244900f8054440f0b109404011844e03103240d58040000300d0310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 128188803 1250 128187553 128187583
    0x30f0f0b180c0a0e13141906031109071709011e02120f092107020a050d020a03060506040e0609011a031204261b0a090b0d06020d02070f2603060d12110706020a05 71
    0x840380c2940c03510654074910f1688140152f12190006801c64464001c2c50000c14252101c15643e00b025585c0c280a001c0ba440d0303051706d04040742500e500d08449031080b00d54148010341d000802d9076501e08680c40a0800a104500c28002d01030781d48421595141030752441c0c0c444680c40c644075046401801400c0b00c2d80e0f00b0507406034a00f54403d401582d503144503a42100d03070001c400300380c940e1490f000c90040c2003c041080d00038480c84003881a10360064000008115042242c1c41500d002c0400b0076507a050107400650b81d066003000207100d110000e400c0410380310000c282d07001806102d050b41d20710b001d4002c044640c4261142814540500c1d0200b00305004005100b0144030f090101000500c001e255440c000b807a159001940c100440416015101016000910007150200354140015105a404101400580c50f01c855000f12001c41040d41d00074040500b0028a0740e5107950b03200d403c021094080340520840c2c0c07078049442c1c00104480c402070080b65000d404411101c0c50203515001001d0b8181003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 128190053 1250 128188803 128188811
    0x131101110303061302040801060303050915090a060e0d020d1217060135010e0108010509030a0e040921110114060f0105030403030f0f0b180c0a0e131419 67
    0x5112000041039030b0f000001198046103070134805501c60001d10550307000d00310550070400700005154000c0041c20384183c042c0c91801c20100a501c04c1d0a00380310b00d1500c1c0d540200c24281c2805403034441d541405116102034420100e61050350001070080a81910868042ca900c01030f400c0020b50003110000002d4181c039040c0300320300b0110f001920003c0b1101052580c040941e21502080000c0030a80341807001900c9080c0480d40c480a4803410f441c0240209075440d0f09000114030a03090000454280c21030981c0d030607908680610410001e0305601800340c407001c0107400120100765044801c2032001c06691108441e203410301c240542903480c07540c0745580d0f48015504110041d142d0b0603100c4800a0300346001c0d9078a0f515850142e004204029020310074a20b001e05200304828541d12203408d210701140d9001441c00401c01c00c0c7c075012012a40042c20300c90a209c80e030409802400715040342e107401080d01c400f4801c00e155a0086800487c91802c4984a0600b03010401c0381000100d2404c04803840d040c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 128191303 1250 128190053 128190077
    0x2010606090605071a0f041703040804050f040207141b0301050f130510020a0c030801050904030c08090a0801020c0309040b03060c031f03020315100504060509130812131101 76
    0x1d070000c480341c4520b10600400040c034408011003a5030401440004002c80302c910b0030680304c034003000d510880d41268080101202c0010b400b11103002d581c483c5500880f001d2a260a0406000c00c8028815070290003913024415031002604c5040d501e001841310320014000d0401e181d603800e04080a10361164040d0b4509010300c41046180740c2c84581c000b8101034903c3e0307402c526240541c904081e81e10a400c0300d5101185008070a60b1088080030b80318000e90300c0003140e980f100e04011030560140c0f4010003040f0282031100002d00102c1c0a40300d222001849824041e41d0788441509981c465000002c1079080043c41b860285018403c6461424064008000610705428288034620020740720102080015645001400c2c0f80140c00d0083c55024040d0349080c042200a9010a00c0945040f00703641043c0c1700110f01828940300e000d0880310003c2491209403600c01c26050342c890719440a68502c6020010310b0b04800700801410f0059405106c0ca40150b425170903c074003c2c000000703101c0d0402c1070420a003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 128192553 1250 128191303 128191307
    0x1030f0902010c0b0c04030507060504030215040806060411090409061b050703020303040b090a0f030815040c021203090a0b0108030a02060f040b0114030f1b1e01050703050706140412020d02010606 86
    0x103c0025940089480840d85804124030441d00070b60788004c2c40d0f8421030310086115503100001d001107034400e580c2418110601c4038095114041ca00640c0b03e107a0041000528924142c2c10003280300b01b031030100f1842d00d1080c60125041d2041c0309000d56049072220703030340c48130300f41e00200a08481c40a883c2c03450410171240d90094507031001400150042c6160301c082000001c040c400c1d05a074940c000800c0101112500d8090200f050440301c031a01628a440c1d0071219091501400d0400340041d070141c81d13120402c2c40300b440681c0024200340118456042c66400040b079844005c2c1c0a0b01c18800103649503094520000e1910900034040084590031031305101c001500100b0b91030543e40c1da042d6a02d0381100b6000400c0c0740c40072204d525207661144d04140b4108210822102c42440015185000300700c034210300c060000c0e016045810300080c000c01140340442e100f4006040c03143d11405020411103480301410f210024103490036503100002c0390b03490040075010003000006102900091008507d090781c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 128193803 1250 128192553 128192567
    0xc020705040e1e0f032808062d040221090c010912081c1d030909010b03100807030c0e0f06030c040203060103020c030301090507020d021615030b09090a0201030f090201 74
    0x210f4424981441c5158441d5040c403ca000084c0d607142180e444040410f000f16941407040b00507040320089003034040d01030388501c10003482890040e000044400000c1c0c000500146409510310880e5414000e480303896440340000d005005a81d01d00991610400742c0c0300d00341c0c0401808200c51903102070b48030042640c10800706000c546000381c180f0b02060762030820341007a11510140080203200040e00c0104840c0300d0740910070400b81032080da9410f000c0e010b403c5035244600f900c0d65601c0b21b0014010000601e40000450b0b00480c0300c0c0b94440b11a54401e802490244603403c210741141048000b80070350118040040e41c00410812481254140680401c1e11a0060305405001d42d8001001880c0c99020340c048401cac034005501100d58079030b07544001100820301a5401c20041c011078902c11403461000485891603000c0240c161809807070b00304c90145c0c0b40b80e46d464980505840c0d03030071007407075585101610344109215400307803052240a02c001001c41c0c55500c1900812450800c1c8034000d40d0340440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 128195053 1250 128193803 128193823
    0x4021f0c12031e0f200304020616050a050f01140103080d0f060f080105040c0b210709090c080a06060306080309010c080705072601020430050106090c020705040e 71
    0x10040d07001c207281ea04034040c00c0b06002c2c89400c508940545400a03543d41c1c40b03032138100080c0004024480c0c12104c0c042114548110505070048140085000351600304010640c868402040d108008011359270346d03003403403000c21003524035401400403050507940a00441003c2200c203581d4140640c155a520244c0340035030107002203520343d01c0000700003042d000e40c0b052001c5e1807810781c0c2c0c1c215941c0d150352450107041c0403541141d1480548100140168111054030040808000074034440e803141c0c01e00c203d600d50010b0080c0c0401c00b1310580010f035826540726500d0a1107171a91100554507010308107005580450f80800d04251410908110f071401c08000c0e41e0036980242307040740e01410382e414031543c6030003450005030007401004400078603017404910301d0362050308180301c03460501d081e01c1c1d10074202c0c096841040b800d03203074612036400c00d01e06100413140300030307405804d00b02201215101c042c21030b903454201e01c0441d56100140503a0540400450b401000101c605001100309807031070b01d8550504113 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 128196303 1250 128195053 128195063
    0xf081e0a0906110d0b130603030819180b0402011e080106031a13050105190e010b090414010609060e03010e0d030e030403080c010b01200d0e0a091404021f0c 69
    0x264420701002080e070040b40000b07000d0b2640c1034899030941102d030f00510085400c00e1159031904a900f0b0141d80720b001d0f02040302d81685440b140c9a6542c00e40f0405540403021101c0082d5540c10b8540c2d941a030b0310100f4442c01d0140350803070001d240600c00540464141e0022044043d051510500c2441d4400c2d0380506580b000d1401007140300e940860040034540e4052401d6004492040614190340c050340601d04840003210342c50020303d001e8081c01480c100b035014030383d118143c000c0140400c41004005094419018100040800320301e180b02e44035090030b8001c030000526400080003441e51004603040d402200324001c102281450100c10741d01c800403900c2400307054544d2503015507038100b401500c0c0155001040180e503942840c41c154000c014071001c0b0350103d0ba00b92242d843c5860300741104480c01c0603250003401104400c000941c2d041600f2114140d025141000202c1d2a20700c0b0b001d68080c00a8175038107020181042c0c030412000346080c41c03031703400398024000180c02120380c03095007014825000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 128197553 1250 128196303 128196311
    0x402091f020a0c0e040303050f01030f0f080f12010305060901021c0c05040803040b0c0d091805060a0f03061a0d0512070302101d07061b0204050604060f060f081e0a 72
    0x4000d05038180010a8400303018914070850000f4004a4030401c6441a0701c81e9074100700c0c03942c0b41c0709010503131031003808044c0c09003c1c11241d07000020303000c1c18041d0016000d500c00b2420500e184074803030705540c89a214072180c1e00b842401081040410041580c01030004c0d0000d6060401d080c1b800303441c585030116440c014a40340c040b0300e000c1d136000760110350140c4802c000703803661591141090704156115040700035091080650345d403942d512400d00e17102607440803182040051030702292100600380107403807aa403204081000003280002080c465004601c144c001180040300c4410a61100c00c010301c0c041d002e401444a1800043c07030104c0d0740c140c0c0300012201251502001d040032454650f00503c4000c1590ac2c1c240308a404c048600c000b0407100040a048842268030f50388216041c5d00848070303081c0411600880728006107015003007541c6c0104003600000e0305560718600c10030f40c125039602c079502082c0001c030003008540d44000c15551100700103a000c848842c00d00d01d4940301603001070110103103641d1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 128198803 1250 128197553 128197609
    0x1a070e130902040207020402030c07050c010e0a03060f0b1e130608070b1b0a062c060a020a1e0f090f0e16050d06030305030118060e1302010203040909061406040209 72
    0x6030b41d050700c402d246c02420441d00d9241078251421140d100300307030684492040c00d00403d110340c8240c0b84024140005080007802501e942d40340c0740505009650003400949500100e03015445e40320400030b400c00300f03400c1c4803041450741007444250008000d540c0002c42c102039007404066000a03a41007250346202810ba0f4926030300c602109400e40303907011041c15000313000107030040c003800d5000000031041380407004401d0f043c1003492201305100d030303c0c0a041c16040040040c0805800c1c0c0d0152414500714286841c0007918006040f2848048407168404a8402200400e520354040c082030003400b060300c035811a8500700481a059504001c14503e6204548615800344a1052040e1007103141c040f1018841b00f902d038030340505643c200b40901c445031100c80c081c502440500c0d00500302101c203045c55040306501c503880c100340d00c05500f800503030541c8801c010000390604580310705001140030307900000d841c030780e5031280d000d0880000d0b0440c2e210790b0052080c0040c543e144149080c80b000f00c4480040501c013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 128200053 1250 128198803 128198809
    0x90909053301090504110616020405130209010801050a0e1204050d020d02120607030b04060e18071505090f0108040305121b070f0507050409170309070e041a070e130902 74
    0x1070307200014500344412800000754000070b9081540a02e2250210700b00f15503144060017485d000700070242c5d482e0149104a18054186544050340120044030030046c004032a4020405c40b80d020390200071540e64030002c100440300030303208820b07802940b00003501c074100344450b5103a4203000c3d07402298030403118140c040c030071503480c2106040303001c2d4003403d407000c250020503d41d6201c171401c407814400300e42001e090548078a800d208080640f450148104e00300c0d155405002118140d00041d4030480c0300f5000007080110300440483c0c40816a40d40c0d280c5d0305e80f2954144420701303c18060b42c034148254681440300003500f14081d43da00313904c4041900708541e0b6103070503041400803110340025260300003c2e02a05008030080c100341018040c0c012035140ca80c1c0c0700c05001c21101166400741c4880329030210f201c60000400003c50704421182c0441d10419103e01c1181c45184050390202c82c03154a03407046107554104c00b450198820100e06200c510300f1400000300d09817111905944841e40c3c0e4030301441c2d0840d9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 128201303 1250 128200053 128200123
    0x3160207091b2a030c060f2d36020909031206030f0601120c05030601060e01030c03060510050a0c050d090e010801020f0a0503090c1302040609090905 66
    0x200140e1414881d2807400d00b201d50070003068504400c0054106030082440400c007100300b5203006180c80008900f61404c1d02c040701d2503200b01c50115201c41d01c4011a05a20296000f00310a10440141c0540c408021410880c02c610318500e049240c1810030180c811004d103101e02d0710300490a20039941090030441e44100c41c00c483c602000075848419501402001e280c000081c050209451800e0841c54035810b0405a80380c0d0441d890300c00c65400381005012005422403c0422640704a444160300781c1c880d0b00107410300c00242c01110004000009812680d81d15002e11940441107080806c1042c3c10000800c2c4942d80c1d402240042c40300c0080c009501d5032103980c58440541d0002e003500d442c03e00c9180010140c02c42882452105205d20001040d04d003010f200b100d00d544000b041c1145002e850006c00e42d201c1d0401002c1a20300d00490102c0c203815144c10b050600380340016200140d6a90a040d80a0124041a045555a607182a065200107000001d21443c2805d519040000480e0740c0303a0351007154 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 128202553 1250 128201303 128201309
    0x60c030507030f021e0706020f120702060702010c05030307020a1101110601050108072c12030f030105130603150509060a060303170c09030a060b030d05070305030a1d01020f070c0b0304020603160207 87
    0x101060703010042c0100705c04200c1a09407a0507509580410300703079050143d9251941d842d01a84103808114507401880c0110090034040d106040800e540c0c0302e203071291030441d0003c4a1010160708403050010800600f80d4101e4002c6009080015040c0f012441040d82c1c2d043c1400340354140400d8a0100d80418010200503880d141d0495802200a02100c5942003040300c03802e0300c0340103070034054248102e071034048203a4076400b91041e526403c5038640000c0083c8070760646242c1d640c035a0341d614088045199450300510340300d02e403580803c50342402c0b0400d03841c00340001e001d82c2c101480e040081c40000d905c20701c20804180c0b9840c000704680c40b8080344507958031a0b403c0c0540c0c036205084120041003d51780142001c010200c0a5070803070001200b040d035061103000001000210b003000000ca1014542e400343c0050540ca0a46d0b201c0380c0b0721500190b017207a00c40f40038250400c0b0301054080c200b0107040942e4001d000c0c0c40e12aa41982080c0c1d000c1041404040e003181c00004501c030181164500c200b0455000b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 128203803 1250 128202553 128202583
    0x111204151431060b0a0b07080f0f0405090916140f0f0303090d050706030609021911070504020a0e0a170a0b090a05150a0e070b0a0311070c09050907060c030507030f02 73
    0x210b0030107464610000c010702c40c02e6038080c51442070005a400c8a400c141e85c43d4035008441e8910700303034030005075051a070300c4082d001a01d00020701c40801c040d115400d12030700c0341c2e04100040a54401a601001c144140c3d42e020001c500c80d8010064080c0c1c50318092186080300584100c001240c1b4080044c1c110b01801100d140c0001040c503512090140010755401110741c90f8408101154072049031300c0503440f4a0004040c05544030b80690701c4148940c4520080d804c445064808171516038000400b80e81c01400310100203240d28400105c00d2030032003000c4000b00760185040720400042140251250380a10b00980050f403100000703004c41c44240f0040701001e07440f40c280c5110004000e91100d40c04025030340ba00c841454403901314420303080042c0309400e86000003d0941060070401048000d0015500392142c1101d05211b0300d000101003801003406031528001c00314461820308072007850903020740c0c4142c00304000c56048002180d003200c201d03101c25030540b40c040f0400e508142d050789094004610300c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 128205053 1250 128203803 128203891
    0x130302090f010608070206090d0c0203152502070305190812010e1e0708040b10050405090307110307030b1b091e01020607090b120601031112041514 65
    0xc100344a8440c1c441c103840c12a00e40c0d031443d85820508980d550000c482d42d43c10707a40070001001c8200d018502c4200395034401000c8540c10340402c200200003481c10366520301d042c2c514040d6102d2024101c50345000e2640280700074810706186031a526611104c0166000291b10700d5420003040c08454011180b000854101501c01540d440141d000015400c503500420303452030a10700f080c1c80c0d01c10004540903c2c030039500c81e03800d0303150380d162000105d41c0601680ea450040d0200020070b51254040d084c070031210503020310f85440103803c011049203004c100f001e1190700402406c0c00015003070701c001074020041486200e44402c413400001018480c64400c0c0f03910081660fa048801d44031000c0c1102e18020030b134251205500c441c4000e488440d02401022081041800030300c03e0176030944421580b00d401490085031800c980c8152610702c0d400000110b070703c96030300d40401c000d0246d144100040030120100800c800e51121007203071a6410040d241090407600c0074440e9050210460301c0d040c00d04e24109a05e9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 128206303 1250 128205053 128205061
    0xd090b0c0c0d030905090109020405030c040507180e060918060406090302030403061103060f0f03120d060b040308190806180405120f070303110304020a031b0b0403142109010513030209 81
    0x141440410b407044074450f400f820002304411545000b40c3c0c0440c2c5001c0c00400f48055044204005000001c200c2c00402004076040c00454040c00c043da80180b4010b07160351a941440014051100c1e8000d0000e03116a0b003803030520601d0940014810350058100c0000240001d2a00d400c0703081d4456076101400d00b508101248828011000007540603800440f803080c20311280303c00340080060b2080f822503161304005106840000d280004200d0f0210f88034000030100e8030f440700d984168209030400c1d51460000300d1218106001803200d80c0d4002850708003804245011400105500d500766011100515940c01141c10014100301a603c001d4103c810103488410282881c5d803aa0003205054000a00700843c410a00f9a02d104883c0260780207005004a241551519200b000e49540805441c0301540d1001510b05015005440650300c81e10401414a82c50110146861352400024800c0500d9440d0042801140c4080340c00b28035080c03c2c025110b034508010100c4024640d0300194008035240100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 128207553 1250 128206303 128206307
    0x3040614071d1f0c06020f0a08040b01060305040c031709100302130e040c03060216050a060501030209090606010f080705040b07080706110c10020714010e0601170d090b0c0c0d03 78
    0x418511860850340040002c0720714100401400b074a10541c001e82190210b09039114491640c075480a03006803409403514120022172403880c0e1112107608002031009080c4401c200081c0c42c40ca004025a18081c045070506803201c5902200601c0000d08644c40405104402c6603180103072600c2e400010b2074003d601c0948030f00075020b5400b14130300150304080c1d40c5005c03d002c01000c0781e45004542141c4099012415a9a0340b0025031201000c1440714800d2403048001403803c000000c2000d02c00da0011a49516610500c10080e402a1102140790404000c00002c0c1c0d0b03000310740302950201d40c41c056200303441d0805c0135200d5101d41e410a2480000000b604000e0158410080840d944502410007844509910000701c9003d982c51181040c1c001003c4000800349075000b83c0303070140c0100072a00c00a090b1403061401c45001c100d4690355500003400422a4012108000c0c0419039014090030360b558802d50001c280340024041c00740462030200d082c501c451001c00c4600e0034103c0261054510050758280 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 128208803 1250 128207553 128207567
    0xe030105040f02030d030e030904020c03090a0b0c1006030b070806040b120109120f0f11010213080a1709030309010c0f050607050418140f0403031e0605030c06040e07050304061407 79
    0x2a4040d124031407089000c5da20910441d04154549400345043c0400079007040003079807003021056a240710610075070200744c1d16583c2e4100280b5100d84500d6540003007451050600307501c002500d10913441d2003070800205601c4451150300001074608908550340300c1c000100200b01102c2c600d600100006480caa08610540c0241d074100d020780d1101041c0d9420301022941c0b88004902100081c0e81e40b4508241207029160301706a803401c1c0400136050101c40361460a40104551000204d40c3c00820048103100302201540d0100d004d40a086240c40c01a0011903605d00c2010f134920704002c0307034410100901c42c00c071100f01d503034640c0300d025900c1c1400c000000800d0340d001806a001340c0c0401c08001801e1000c540318000d40b6942c9000c1a240d01d07510000c0d02a800d0794000e00540925444900302c0340c80510f10328400c003507007107441d0000030a80e050400303240c40e20101500042c0102e10400060124044605e032044d402a03031031400c66941d40d12031400c800605071405d070400d00701000e1014000030303a8110030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 128210053 1250 128208803 128208833
    0x150a03050105161707170a061a04172a0604080109080403031e0c140c0a0305060912040503060a0209150706050f13030807180806010b0d0509030c03030a0c0e03010504 73
    0x7580c2a004c91120880c03c0e00b036041550041c010400040000d5050303c965518240c1c003401c01c030000201960781c0c4010480c40d80039040c00200501d80010284903c11505000c5841d4842860040024001c1510f001000072550000104020174023801c00c1e1a0350f5508040760702814800c4001d1104588a01e172020540c0c000707000031000b083d6107105404010740b0064240e605110155140e4042c51115250f0308401e8011034100000c500440d6002001a1100d4108000440c45040204600d180803049142041c07200c94076985648400c11040285580005035242c000c03501400041c2e4400c40e06d070002d80d8901d00200d03070b014903d05c04618141400080c2c0d01c01c6108400f402070907401940c800800014003900104000e000c11807540c003041425120f0741c090ba900c1c031448100f299003651914405440e00e01c0c00d0f4024040140001160841e280e803030b00401d034010b081400110f0034a0380e403406017a00c0303000042c021030b03a0560b6101c2c14000c00d841803143c216074010240080103581010704000c452101c400c1c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 128211303 1250 128210053 128210057
    0x2010e0606011b29010503060c030c0a110303040b0103060501120f0809010201090b04060603060f020702130c050d0207080310121a06041401320d030e040e030a050703021014150a0305010516 83
    0x44000906c604020802038840d500d035240484c95642c80c07141c4040160850443e8000f0044030710307000c00b800c1c02e04100441c0600d000c0c4d143d00b00250f16626140c000c2e100140c02c4080c0c16248400d9250000f04183c089540580d80168a16220003000380100d0052460080150482d03115070300303000034032410741d1005003500e001d2030050201e0351182c2151020f9111781c05000b5040411407424480542c282e60080c061454549003403807501c1c0560340850181d070800e01c004d40d13141c903001091000c1c5076540b040220061a400c0c811034403035103440d02e4103840480c641000c1554400003000040d22079542e9800070901e540c4280c0e1060403540c48134603600d0f89102d0b038280036840000c9044035041065049008101000000700f4020940059503400c680d506411030314290802d48840c004140d0300303800e1020303089940d543c0e42c40a4681d4414200249044118546245094580300c05000610319212119602c01c0400040f19507a00355440440c820650382c1d840070781903500c3c2c00b041c0440702000e050700d0f0701181c07070503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 128212553 1250 128211303 128211383
    0x1801060b0a0212070308060603130b0a020a1e0215101a0406020c04060e0a0b010215151008010f090c270f0801060503070303140c06070806010f02010e0606011b 70
    0x19400d40c01c014802c4c0d4001602003094074000400b9403400c94001c5078080031340031001c205104c2941d5421001c08050702c2410741c407500130885040c610750005001c2c04080351450200c080c6c0d114140701a4403038402803071190314900a1000a8040844c0f8203d001c02805000802c2c3c1e040e00511281d0283c03a0420700620340180500d240c82840380ca46401904280d60f090f02280c0c1494681c410b00c013005060200d036007415401000d03080b17501d241c80074501c14401c500e003070302c408042e120703490404c820002c004400c01d0501c2419001803080c041103a008805490030018002008070742740c0b400381c58104100c190901d5804008a962000c00c00d03c00c1010b040720701090a450205460b0340c07189098440c18001c00d505980030900c00c0012034421101a0700b8442c80303841080c50000000e003403906150084900f140403c01c00c1d0184005540e102c4c22540940c000d9200070044400d100c814261203940c0900311604202c800401000d42c0340281c8030ba04180c6600070841000742984c51406098010100340c0364901d1905 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 128213803 1250 128212553 128212573
    0xe0105010c03020709180b040605040212190609110409030905010e040603020303070206130b04030c0527130c08100506130902010c0305030901090803010e0f0115090e1801060b0a02 79
    0x6a40254805036040c0c000d40803050030507103034000400b40c0fa07208030b00c13a26113200c83c000807c0307a0b1000c55002d2806000046524030301401482124a032850382342400e94003d10a45924003813034103499508943c41440400d000c4d05038242004091105515164401d1829107a00209074100c41544202e4030280c0703c03c070895440c03108120803100c03a4400a50160000c2203140010b10704032004041e1f140040c0d805000480d12003c0748285600f01c0d0304125280c2081c4801030100d40741000f0321401c0c04545202800300c40f04c2ca18422030300b24601800e2881c080c0d003480b405c2c030200150b440703580d03020b130803500201c0d090b851848501d2000fa00b425070340035000f40f070300d511b00c908500b11314081d0031445501a1a21042054180d50440e4264002840040c66558a031400b00004660318010b5001703080229048075103044c011850200d0380300682c007180083c0050820300141940000d07401003101c80d00e9411a105a8070402c20007030880c2030003003417039142d4139040c1c0200c0d03c0742c0c5074000380000e0a2264203c0d21120700b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 128215053 1250 128213803 128213807
    0x90901050307081b120106030312050f011203050309010b03060a06061b080f160206030a020d0b10020d030e0c190f06050306090c16051204080f12072a030506010e010501 74
    0x3403070303001d01040c0b13030428071903c5409004005400e1a05030040e01d004101401113200908482151b00102d0000c0c14640360402e60080c640165500101807190600c1d0f40d52528488109504082200a04dc00004000121689000c1d030000010b0f90020b030548000746070447d41c9400520a6014001c0407030020340d6200300210100007800300256000d4245454810b82c040421f002d80c100406040083e4503140031080160ac80001860003072004050141c1c80c0c0001d8401801580c800d200041e015218007c81d00e40c40c1e0798005070703d4010091a040010304141c1101815041221200260307400c006849808505407061424100c115104528940c14198460713008481511080e41c5444c1d00181031004182e181110320000e08003645611000075100015940d0700d820708098000c1401d0315000450300b0050110144040240000300c08050310034454000351480d614040c4020103000f0010602019018071401c2a001f009510702030f0450074555904c0c540956100405d01072400c98100341c100000d0554 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 128216303 1250 128215053 128215063
    0x1e0a0323010209031e0708010c0f0f021b04050a022101031407140613032a0902160b0603070f0e06040b100804020d060b130e060f01030b040f020a0b0a050909010503 72
    0x94010050406003483c82c580c6140000c85c00103280c0c060059030f800103442c44003440b0b034052485068640ea411038030328a001602d0845070380c40650030364106800d400c454000800f0100301c9910202c81c005016251140280024096042010f1924450100c2c0c2e200c0300d50006c00060403a441445a00c440d0036819264580710030041c8030f052441821842c11800c43d103800d80c090602104003c40d006000381c1c6e01e031101000ea040b507281e203411003132803030000b01d88500d81a4400c2003d058004425403500d268005040c0f040d8903003840c040c108940200108009950a000750b10003401c1e0030398800240b9841c1d9554a02c00c41051303815a110320702d0803912421900300b00080c490701d00c03900c3c3c40b034a58680c1c503a0203212404007005d10403511613a88110840e400e5075101c0e4100020600e41c070000600310a060325007031070100007520f4080a1280c88004200150809410561040d03001031701c215414054404140e080300c6a0300400c082c1280860030410303c65001d0040d081d158421960305078141da0745c000b0f16880d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 128217553 1250 128216303 128216317
    0x220f030c03080306030a0606060809070b0301080c041a04050f070e0405060901050105070f1b1703040f0b0c0102040308030f0402240a05130302030a240b0a03021e0a03230102 76
    0x8044046420400705140b400650f5100b0406816524852156a00c2c1011070b800341e08280d001c156040b05002c0e54060411400c1c0c040c10200142e246194103020015988000103149188115241d1040b1082922101d030401c42640c0064000c0c0304900f8064041b0f240300000b1140500002c0c150500b52080e4542405200e01401001c2c02c1080380341d007000011100c661180c0001d48040280402440002d1800c000840060300c0200d0500c600d2403c00c5000541c0034107910070f900a0368410b000a100c0c000342050910100d44880000704c0d600c0c582c800b4028064082c80e88003800002021003044042483c20032003074812071085580072100f00d0069001242a02c1180c221400400c0074000281880d01890040101061801c01c40813225900d40c002480c114005100b1a004048400710307042c020344003440030514110303c60741400503944810100f00c02c44260710010744901c10306400aa00c4102c0d04001742d00100c0b000c3c10004000340c407828882e0070035403240803d803e800811384075602c40d05418030a8602d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 128218803 1250 128217553 128217563
    0x10507080a0908041203030b031005090c0a1a0c07080d0905040b0909060406050a09080c010b09062704060e06240409111003020f0c010507030612050a0b09030c03220f03 74
    0x28142000da0645d55184900400c801341039440d0304504450b0380030010f04842d000c80e224082080e150000340c3c00d0500d80f03074504560240d8000c00c01131140c103c0181b1501114900c0d440003e41b0740707a420641e1481c01d0f940d6480602240100307510311109560042e44003003640d00c151824407400d4151802d0001d41a803c681d17541641c0c000e0408900001c1c8035400c0f41c4e0704100440c1020030003414603100c20000e507000c120a43d904da9507640032010f036070400c0300981c1c1e840081240c00005081c0c0407015000b84248a183e142c1c40c101026002030204407065225110a0141c0d00403141070385410180228020350511a0920059581d84440c046242c10b0140c02000e651040e4542c1d19082058144a030030904140c02105140c0c0a03c030300031101c0c0451014000820f42e0070004a070500342544041c08960180c1c1102c541d4040b42c00e05140450000914100c00e164400d500000701c0d42c4a89146066000e4203108510b40d000010364050703101c545d40e500703100300e490f40c1c1100480f0036611749002000420300e2000900c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 128220053 1250 128218803 128218807
    0x8071a0c030d110c1005010f08060702070b0310210611030c16020d020303031003060606020604170d0605120d080a02030915040f17030a05070f050405100e0a08010507080a0908 77
    0x91044520f03044086000101d9180a060000c0700c44000c0c00c080703060700300c490116501c1e001040f882025401030b070010041c0c00081d000f1402c1500b402500c410729402002c194881c0000803c1c907608000420030b0003094221a18041030007268aa90103130950040c0c19030352141003001d251702c0154020100d0740150740c40c0384218a4540105840d100070403c1c2082603078030807140c00d29000036880610056100314402030b10341c1b92a90451401c0c200b112007e802074000c6500800822000451205031490200503141c0c9030340d1039210482000c40030f80764a4009a412001d540d044481402000809074090205a210b80901342e880c0e01c2258202d02044a035440e03aa4031200e4110703064a11031400700d400500900c180100003240381c68821229481c010050303104da400004020002000b84200ca0300000f140c902100c01c1c0c0c40007030000b0000d002c0c0e801030903c103042c0d407a9050101809507411043d1910003510285115a176140304500902e4100d0b0100c000c20814030015071a0a81c501c0380e007900c2031b07000384903038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 128221303 1250 128220053 128220067
    0x1706030d0c021305010e1b070201050403080d020705070602010209131b03020a0908010501150f0e010e040506030307230c0a060c0303020306010507050a0507050a0f0302030c04050a02090a08071a0c03 87
    0x21840c03007000c501640c104141100039a16400c0c6801818085e00780d00d0071001442c1000011814201140810000f1642041c000400180c0c1d0103011a001c603900012001d071682921006c01009201c0c05800400b10301c11403a000800d160107401401c096a002c039020220260300405242c1a2164400d03403001440d2102807041540c2d000b0707400703001c0944151801205654541c0d0045085803400c0e00140741007012624a100182e901c020301d1007010010745049ca113240d07036150001e00500300030f44500e403240d91a4000626183c800b00252100a42c200307a85c501c1080f16030580703002040c2d640e90040100d0107030405401460a148403c08115216560350f40240440f5403001c800a4001621060402804000010100d0b004000e003c5010303004202806c100c6181204111010031241d0050900e00c0c13000c2c00400141c0c2d800715800300504c406460214007540d403d55684000e21403604000c0c0e020040b440040f80027800042c0da001541e0840300c1c010001401c107244500303680102144189568004c101e44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 128222553 1250 128221303 128221307
    0x30103060f09020909060103060f1a0d0302010b061809010609050907030906110c0d0801080d0c15021b1e030306090403030b0102071a090307050a2114030d0603031706030d 75
    0x1c4220200360000500c01c501a40042c52441043c2d40c020040d5114034010301c140305c0c0703d110740301d640740b43e0340010400107a00c00100100c1e01c1183d12203030b2245612050060a040c000c0d0030040c4002c10040c1140d070785130002081405120380c5150030500401e080400890702501a482c8507054400050108d40d00e9983d04104a02401c1864000c6500903161020f08044c180404003400804814038080e110204c1070400080c03140005a01490041d80002c00034940340342c02c0001710300760302c0c3c00008500d806086004030a019202e0b00d90390110011490050000c1e544c4086004a078914101008840c21880b43d00060703928001a513481d54044007050100340081c0c0640d01c074605883c01030065074141c0b070b83c0b01c00a11500c100503601c0088040e0000d80c00115250034043c0d040a4181103641955241c00d000700b19455003e0395045015810703240c1141e800b41300c18020381c6000c0300300708000c1f20b50341e018050446020705124402100860100b804a0a803030302003200680c0b0412000d0002c1640d21107440c41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 128223803 1250 128222553 128222561
    0x509030f030a0608030403060f0b0d020f120708030a0302040e01060807141606050408191803081303080c1c031b03021608070c0302031903020c010f09080f1608030c0303010306 77
    0xd0750b040c1d941d5010008007038a090000e44021402503000040507011450810280d582c00d1142512580e008000000107960340d40c0283c00c9001c054404146000d6260320303182c034244290b002801240300c003052071260302d54550020810703212601100c92040e40d86c0d42c42501e2003c4203460315000300e91070700c000101c90401c0e94042c0c0000054118400078a101c85c0d100c03401220410703074094412510005000d4642c409000d50340d0035000c11850542d507010303d00070005240c0340950000920008000508124940c0080b0000c4003464000401c603a0700c4140b0304845980708422040e2b42540111071030032000e014044c0c410090040014a14281122409882180203502640903038090b110140c0040c004940414044c1904901c10300000c10494110b0041500e04030790f02c4108607250b100e112001c00081d50204003601c1c2d1b0b174400c1c201403c0341001460103843c80350058200b001144115215948a040001020440b40c00243d59001340036442e22401c0740c4900c90b20140716819402080100002074580d0301c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 128225053 1250 128223803 128223811
    0x905010c0303021606050a050106050406080a1802030304080703030810050105090d03021f020d050108011e05060d0b04061a01030204080a0b0a0f0203070507050606030313030210030906060f180509030f03 89
    0x2400500d03182c079251640303201d02c0300540c2c05d0b982c19039a030041002c034020b58400d00c2d0140c402e504000d4181458004002e01405004002d6072540d074503906d01c6c200c40a20404a9007041da030060030340e504d8942321761850b99a05034034401138000818210104400e038560102d02010743e40c1c107a40d5903160880d81006d100c03906d986c00c00100c0451103140002d4001c002c107400620100310304d585000d079841d0714042d4941d058543c10f8107d002d1f664506440a010308040d4501c0302115800100007083ca9510000003030f09101d4107003400b17840900c20354104820000d065200d07600740d00440107032051107410b0100460890141e80200c1d0400e0317205180c20001325429191080d331040c042c840100f0700411400100c41030b608240c401001040004c1180800c0213418048207912010540041d41014030b18604031410b12042d04c40070740102582d100d023581c0c542c429000015401d4000301c00384400340e61142c10f02000305080c4164a01c0707024040390303a650594180140f90149410400650034844003201c40e000c1980301030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 128226303 1250 128225053 128225057
    0x1c050d0c0905060c010c080f070504170102070503030717100b031503101a0307210602031302031c0e0102152e08010f050105120718180b010906080d0905010c03 70
    0x1000c0000c441c1d0761000240928505040046048000340d06d002c1d0044101a01800d8034090480400540b10307030180c01d4408440090401201e855011103a00c0d00a1254a1300501103000020412000743c1e0040d2010300000c15242070348241d90781d0b024101c140703d00703640140d80d0001020408610900c0c0507155111480328014255100e4101d0b101c1d0b0001140c140c0b40740c280350039204084600d001e00d02441818018004004001c80c0f40443d2103110103141074160f0000c100c194040302003020000c10020062455a01404882201a62101007024020300c9408540085c8000c419181107502c04602c0c14a10b00045401140d1a10382241c003c0b9410845e5039421282e8108124070041c501c2d64114000040140e0300000500c0750004410078243c440507000580500d440c2c80c0844040303280020300d01d088480306008020740118840d800b20107003950054030b040c00d0555811341803d0140000507241240c05a42e41001566521540c15803038040c034040c1d110118003210310030446d0f940511540e00041e0310034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 128227553 1250 128226303 128226317
    0x72001020f03040f06020601061103090418020d05060103061803090e0702031c1b030603080703270e0a0c020115030f0320030705070e0c1b0a02030d02030a021c050d0c 73
    0x50901c649507400c541c2c401d4001155007581004504e406021890250002d45422820307a2406005035507640b140d40b40d9940510740d07030100d0102002d00001c0303095401b81d004001d121303054441d0030301c1c3c2c0c0d54503000e00082d900c1c2c034948034456058040021250a1190b03042d143c1280c96441c00d115180b50120091540c01540800c00800712901046508966203050450b40020a600d01c80000500c40405442c00707401c0c18a40b000500c040344820003a50381c8a681441c000e031201c505040e043c00480300841c16000c0283e100300740440c1206590740614428452042d01300002110700074100e013a60092000a80403c400f01e07030510224038100300d1341c0c0505004c0e08108024203844683c2c9240d0f103070440e01084180c3c1020420408204040c46004003d1106c0c2c41090f21504000b00740c42003030b10502c800740c02d8900300c110002403045001c0c42200b41c0c0540040541e61080542c04c0042c0d16a0312041d03802005025641da05031000088206058800c0c0c83c1c0d5aa07a0304000320442440024452642c00c6000c0c0505 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 128228803 1250 128227553 128227573
    0x402030907051503040b09031e1803010c120b06030f0705210f010302030609011a042f0703080f072a0f150c050c06070c17030406021902010207200102 66
    0x3520b80c60110104103400c156503a45802d050841d00950050300747c101d00d030010894101c008503d140707007084110b00700120560344d5604861000081041d4400d56425500340744600c4203194014002598154110000f4020000b00508005d158442140d0751641da00414001c2641503220381c0180c13889540514094920359010803441004141c1101c1d102040c00e10800180114102400ba141e0042001c400030710850b00d4690701800130203000b02c20240902e50301d07030790381e45001d080216203050310855250540740e006980ca044103160f4844076046d4003140104000c50414a11440110312809c442d035070740c07110040c40a11000405540407942c00b85103241d8a1600c0105100d0000700b9649440f884840075004005400c00c020303942106110424802c06000c104003900012820540c004154940720210071018544507100c1108034040c1c4c0203000020081008015940d030040c9205250710004400c003900d449000c0f8281e11035118020b040450700c0445820343e1248409499146030140155410100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 128230053 1250 128228803 128228809
    0xf0b0c0a0615031103010e0604200a09020306040c091505130504020a0807030b010306050325150f0306140d140c0607061401080c030607050307051201030f060f1802040203090705 78
    0x25441c40c1072010b919150790803c10848461059140f900742500240f11014890003030319102c40000748043e080410341d2401150682c80060800098400140140314580d16011140000d4000301d500602552820140c803c0c0d65004070091000c0ba0081641006c81485d0f03402d04481e1a0000e0280c581410251a004100d69403a4005400820b000d903490703038254501002d00030103652906007500d0625203800b00074061601c0103d500180d0f1008414514028150703551b400504826aa21042101c10b4000c0c00010345a4000341500b41400a907900340011525450340e5030802400c5050564050f0a4142c800c0000f0460240f10038000c2003030043d600c012106001040e810f43c0a60b204541d4103070f960b20a0521a41c0702c81c01c4034090000c080c0140011400300000c280c0da640c0280c941c83c144480031001440703c0b88200100c64091005025906070f6580d28503140c80d6480300c203c0d048441a04103030030304115071210300c00c400b0a810315216010b4102019001d200081d8005000c0d0745031401410390214040d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 128231303 1250 128230053 128230061
    0x406030302010203040201020d0519051608070b0411370b03090a060f150308070f02030703150c080603120901020114010b0715020301050102150604200c0111040f0b0c0a06 75
    0x26000c0d40003d6528540b80c030009051406103540f89041c803070144000d408614050006840104131410688e175100c0c0003201d031404840c05420000c160074000500102088001c50383e00703024a1184168980000806013000000207460b0043c0d20745403650940019100c0410102c0d907000f8189003600300c100c84d1200050f2240c0c0e2300c201c482c10407582c402c1c0c42030b8082011600c206511021002410001c800c45000e02010000302d03440058500d40000c05c00c903040c001c004190000c00365005086521590740c92404138282c48400c4040e1041600c0c00100c0520a0b0082c1a13140c8607400040c081c00724501c201040700d015030000c1010030f04643d03036081b503009100403005840c0e0181000051590f15207000740380000d07428510460500da80740c0144010007959800003071000c0c5e9400602c60035943c664030407020400070036840707007162824030180000d002c0d400e00100040400c14155002809418103071000c84c47c0620841c818089550b0400808003d82250f090282001e0210442591030280710354032284266 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 128232553 1250 128231303 128231309
    0xd09080c060f1b1306080606040806041208060f01090e190f020c121c0902040e01020316180612020a030b060d0e060601140910091502030301080f0a050a080c0106050406 74
    0x2c0306102050180d84807422074900040c01c452030301c05142098001d50f441d14102c80348104000e011150380072410303c5da01c2d8002e4502070310f03e960880d01580390506080306102c14080802000c141020301048590030141d805c41c1d0b4900c41078442a01007032404014040c00c034401810324804500711006401c030485e660142c0805203005481c0581c981864a44503803d001c064268510a42030401010b4001e09a09455020341040c0c4c0400040b500d4860000c9005400403419051a030f501c0041040340c05203481c40704080c03402c1c0340d59030007000d0b03072100c00100000300071401410007203030f0000300310310309803440307400601c01c1d001e09103400300e804c1c0c07101e1011030100c0e000758894007507040d261a251004440c04010032944000c0c00d19002d410100c0034038110321a0301c10502c2050182410b4500f10001b01d01614403c0d0060080e01d605c560f264004000c005c0d141c5d0001e0080e540d46018a800c1202074010005101c9006600000a4100303800a5903071600340394800340000d6215505c80200064655481c440d01000b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 128233803 1250 128232553 128232571
    0x20f0301150f0503010917030702071d0406060b1c0504110406030503031b040e0105240f04080609060c0a080a0e060a0c11010e0304090e030702040513030914060d09080c06 75
    0x440760030480d03803011001c41c640009020360f15000182c80070900421100010841c140d0009503170740c60b00e0304100d040c07402540002d40c4030b01401e8060034041601c00105440340d400345c0300c100409625041402582d201c0e0024500100c480300e16203c0081c102380d402103400903c20180c0f8040030032850049030964032103500540d900d8101008100c0540d100401503005800d82001c07440c5080d003071204a018002e03040c01054000e03d50200c48503007a4407003102c0d0072140200a181291100403070740c00b0b01ca090b41316000302c46140c01102e0203e042c1c0540050400e0084000307400560501c4003078074003120032450041a09a07a00c1d1140001c14585030b05100341c9008295000010070b1000400502a200c5803204018850581c0f5028503880711a9010050381d054a0145401103410840350380a14914020080040d50042c42d090a00189840045103041c0240c07103511818046a61644d0303419603068500f8603290819030400c2402012102c1c1d50040d51942e01c908011803c0281c0000450301d00b0740101e8030494 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 128235053 1250 128233803 128233841
    0x6090f04230a05060a0303050c150a0f0c03090c060302030c0d02040801050411011b02150909090319080709031e0f141204051e12190209070e061204020f0301 69
    0x1001501c86180d80814200c40900403410114085034949115200c041c013001004a91035404030801d01c10f0701c041250b0b00324001036a041c210045001005006007c41a6130715018020380d00303034020701900e0710040e0010303698440303246001c2c41a4080e40c4006c08002c10079004110007414001144080d0005d40744c44000081d5600c7c0a140c8000586074504001d0b041c03112560080c0b280c41c07201d0542081080d415606894200e9108602488a005030701d1a0780d0f2004d00d4030100000e6050001c0a458203980101c0105030004043d00c0543c0d0400090710b070203002508101040c8085009034007450f884000c1d07219682101c25040e1908038074a221f154080f207400740c101c16443c20b800401c000d041c0c100a29508200c1c6460310b82000035003171013980c040d00070070780320105c409d900d4590302e2300607000d22140c3e030340b0544100b4603020080c40c1840d040300c0c1049129644040110701200c4c4039000346001c000010700400c0c9400c0d0b25605244000c20000c008980c1301e1b290789019041901c00780910383d01607590b107103559 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 128236303 1250 128235053 128235101
    0x180a0303020a0312050112030c08040f080a050d1e1b08030a0b1207050d060504051603050307060507050306220902120a030221160510020a08010608070306030b010506090f04 76
    0x1481308a1003020401c4071810400103000607102d8140b0403540540c03505104c2d07402403103440d0014080c015075111941c044001080000c0c0008041820600c9611a02c1942c0081103075100942d026181054551058280e400880c0c1c3d225010f00b1603620844a07088400c01e48100c00c0da0b80c284150b0048a4001c0c0fa50780302e45840c99142000540d00b034010036144040c0c078003141001c02081d2076080704040600f00c0c6807500301007014084284040440200512003004000ba02c81c00c00550720b601403c02110344614010010f03200c54030910549004032001040420140c500308a01d0590170b032480c00e420341c182d59410305000184d50350300c0e1101220560201070130030078245080c00f0703042c800101201c10351001d5940c514030008000c0c2044950807100b41e0188460f186450605528003144200700030089840000e0429504d0307004240c1c035040f50b9103540c42444a42c1c6643c4101c05861691100402441c2c2d60341c01030000c1d01e0f11001601201c0405813015440240942c00076041c1d03401100d01c0310991411749985 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 128237410 1107 128236303 128236307
    0x803130809032508010e03030a0221040311010b010c080f031905100302091609091a060f031501050403150b040207060c0305070e041e02180a0303020a03 67
    0x301c0302c1c0d400507031a000c2030340540ea44141c510000d040c3d10001e00401c0500844a9041ca00000b46041d03480e2809008069009490403101e08601d58262101441070550701501c9180207584507160b13070381c5a12405084036020b507521410491608011004200400101c1e010002c2444c01030b50350741e5807a01c080c903103440e00311500c4012070704200910054008002e1041d05403402110550300c81d031200c4c000030440c1c40b82c0d001e044000c210001400c000191890388042c4003110503d807805003d44003c0000f421540c403c0c01158000c45010003805110752440d5415918002c0a0a0540c50030741543c4840c00c0e0356850410588109844400f01140c2d900c0e2a0141e42e00603502003801d001b441800200507004c0d020844006001a002c402040080e1400e4002e03401c2d600c00d080d08a0004020580144d4042d50003a40c3c1744030110860407030b851185c1c03600c1c04030307034000c50003903018081b400c1d110310300 = true := by decide +kernel

theorem cover : BRFrame.Cov 128057553 128237410 := by
  have h0 := BRFrame.cov_init 128057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 128057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 128057553 ≤ n) (h2 : n < 128237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
