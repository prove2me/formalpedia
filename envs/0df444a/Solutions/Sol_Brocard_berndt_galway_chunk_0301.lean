-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0301
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:03:54.89836+00:00
-- url     : https://prove2.me/submissions/aaca0bf4-7d11-49ca-9656-94ab375536a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 53956838 ≤ n < 54136694 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 53958088 1250 53956838 53956843
    0x2100204092009010807110717030d050c03010b04030609080403020901080f010c0309020f0409050a02060c0c0103112b0e01020304082511010f02030c03031005030d03050105010210020714 82
    0x50380300084a58a80d6400140520140c031070744940b03003520902c03905291000780005c1082101a01c980c00b8440c2014441c60011014052000a4100b1200010b000040e04070401c1d070720f901c00d181c50300016250901080ca405182000c5034120344076140300b68241f81c25615414020007452104840c01d1204010010058a9980c9503d0003040712a01400d40b0043d95040b15094520204551040501e04441c1c0c00040e50307124201000303000190380014140c2ca072450f102e0301d0f0a11622010b0360010011690f001d10604c0010302d05118942a6010700407000c0c820701c103036240d0180e415841c1e03050003101402901240781402c0c03101755200129001c6407640d1044806401c81e4400d59080e11103050008800100034076049403407106880081c0c0d0910b6040c1e054840c000130b03441800105040100441501c01032920030810b444600b0303455000e690796820302c2c001218034180984541402409031708031800c1050f019110380d038100c0304107030090f02c0300300c08104c4814001d500180080f00c28134001c000010031a0743c00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 53959338 1250 53958088 53958097
    0x5160e040b160917031b240408040306050a090215130b070213020309031e07350a051c0e0606030a0b0f060103021216080109022523030d1425021002 65
    0x1506c0141020100032003508206140494466070f0815041051100182180048800312034001d100000d85072214070b0184040c100703042001c0e50120350355034010b01d1030503400e004100c40b404001c0681507a680d1b4201c1e0844501400d040a03521644010490a016415400a42e880301d8058140c0b450f0058520705950b100d1500840100f40382c4000c103480b01001400d000b4403c2501c400c801265401e900480080d6504200c51412045000c01003100c41d192030050003982c41e81501544038034000d4010780035000083c005030105240701c3c4641e50110395142004201c111945070810b4a04100d40d499440301480e01030301920607030400d9402c106011034020184108c6004011214544e26284840b80d401000100e060300300080b1745104002d81542c41c89045c4000e944c401180308a512051800c0c1015641c91121101d01060110b0251440c41c4000c0044004c204a0b1035010080040300c540380c040d000e83c1c09088030b41001501241001c449404004200c42203c40340610445180c02006413180e001da070071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 53960588 1250 53959338 53959387
    0x110a0e010f060305060d03030e010b060c010e0106090b01020303070809070b0406050a09060201020c07030b0c0702060a0210140105090105010503040606030516030c080a0201050a05030405160e040b16091703 90
    0x104a0040c00300103004201d000c010051454103004506000000a84030390800000074240341d47c0b101076182e904400e4201c05d1902c1c034014481500c42c00c00e891154043e100c0c420001c4029441c02c00081071804c107a2150060200040e0300440c01c0d6650748034269030546c006042c1c40c00904c02c1503000070310321010b032004001802c9281d981e00d8403920600b0010b0817840540d0402000d5900502212003620340c0011400f088030b40210b080640c03034a50b0034156406100d040c101a4200c900026201c1c1500c1c0c001440d00407940c56074034104041a007068014401310001c0c00380d26800040c50700100700b95131040001d107400c1030143c400003030075644d079540b41c520704544c800d03180004400155040040c81641b121501c0105000c1c0050203031410142c0c0001d0262054290750018040b000c00800e0621074104901e0341c003042d42000880300d03c1c1e00c2c0e048a00c1644400ca80c111002400321001824101103624a100a5078450300c40d0840381e400c180e407000508a10003e07110300d51006021040c0d403141c0701c4044110400703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 53961838 1250 53960588 53960609
    0x90d0606050310020403050105070e1509010309060c02070503060a06030231090c05030d0c050c06030403021005040b22030903060b0303070b130b0702030406120c050f070318050a030201080a0504110a 87
    0x1407547c60301509486d8002e2842050142592003038003640c59450403c22900d94010109564041100040c0c0051016802c085d140c540380050131040740342c0000f540300544a00702d00b15200f560359680c1c01c1c0250b07985400000c2d00015014020f90403041c02096040028800c0c22a140d01d071a138021980c01211001e0009032401c4145000421160400f488402da0b0096180b805100501e03183d101d0341c1d42c1342d1003161140c0c0611000000541418401e10141145245299041c44141094208030007012015190346d43c00042c18504208107400070605089902d07816101c1b00401861622050018440150301e103801d0f0100308030010008015441c494422441022880103860b0103040c2021103000041510341554010002800380b00e421604056100100e00404604003542c66400c03285c0d0b0103081002d201c80c0a01280303038400c15400c00d040090203000c080c07240141c0c907070740d004101501c4501d05c03000c4d0105404401040524415421040d03106014a10088210710b665010512b01c2070164030488118 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 53963088 1250 53961838 53961847
    0x150904090c0501030516020c0d0507080303010b03090105010b040501080601030b041b0201091a10120606030804060509030f070b180609060a17060103090b0a050a0b090a20030408090d060605031002 86
    0x1c3d80c0610607203030403440445004120244640d0080d584480209802c2d1249110000030000c001080049801604030003055903102c2d6500c03540340700e4603041591061384135400d100022603035801c074006a0b02141c2c8140e64101c3d403616081d006400030102240034a41184d00c4034929102400c041045600e00846580000b0b030703411445c01d20300c2e2200c0e40780103c2c80c4400b07500028000004030b00914802130300e218401c0164121418580040201031b07503400244001c0d4003060000b0019000409805130030015415107218103a0404001d4544c44d183c0901c12160806001d400f80608503442e070341c240c910000e8801481c1031403e60019015400c1000d403200098000080c03000b030300105109050b000b070402c0c01c05100d0507605503580d038100705c0000d01010702c055481001503c00e2103590820300200030040c0c0400c41905200e4051000f07400b01201c007400302200079004020504c02101203074441c6400420087c148209070713042040e550a401002d03141c2940700d030030203c3c0fa990144461190f03201c0060700145d88 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 53964338 1250 53963088 53963099
    0xf051b0d050c10060302060a1209061a13050c0313080405040204081609051303050a0c06050c03090f03040506070f020105040f060309150902090604020c2107032a02150904090c 77
    0x83c849400f403d218000e003480400c000684611042e140e203c045400c0c40a0422a40c401b560001c108641004d03007000d0500c2e1012004800c524040b541450095450404c2011800b0038502030b00d20036074500849102c1080001d450092800185400358801c45000307143c03581c1d4500113000c3c0e80007a00481c0080d0070910f02003600c400502c0c80703c401401d01030402d000900d041241503268160040010301440400034426050314890020115480e904ca001000281000d45031503100c0d40084800706018071501580b029891000400c1d42d0032505c00a01c12403a061032651101034846404c0c004a041c04018800401ca17180b8080045002d04501da500141e02100350030008810f00c1c0300f20100180c03500d000610400741c0c80f10700c2c059500520a460242c3d44d01c0044050a01e0580c400d4150580300e61125020004140c0000c01085501c1c06641d03603004542805482e591282090300c1e2081007a540700c1c682c0750060800000b292441c040110003a81030042102c085070a8940c0e00780300302d9000800400070b110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 53965588 1250 53964338 53964343
    0x915040b10030b0117010516050901050702040209100c02030d0504081902030f0303090a0606050607030c0b06220504050d0306060225050907030906150b12060a15050a0207080c010f051b0d050c 84
    0x184440a403e0201c0191920390004d4950700c246800b04bc10000005550750030341d00d542d011507403440380141114040003850309009002c1c40c0c108000724820b020341c0951210b41489901524140ca0061700541600c108140f15241600130000c0201d0b01401504914812880c050001d540b041d12035401401d40140b2520300b0303000b1201e454110b2881780c0b2081c01510007090380031300000c035070643c40705106202c1d4485000040000d148911840c3c0c0c2846240e20014113802603401003409035100303608442c4995280b042c16029107a4034041e510050307100707010100c2c621080591480b10503402d10315007070700c154446000c01c0c07a6130740440d607000100751504114400c221092140c0e40c104017500c620701448904001c0d40e55060304c03940d920002403082d02c01c00316000da5558034002d002410111400482120083d03000784c450740142040310b001d4001d035000051000300110b010800d03548140d540c403800c0038466405481c4c640100d00400c1204044060f060b441c8181003000c4840c07001103441d644d858102c244165803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 53966838 1250 53965588 53965591
    0x1a011706060a0b0a1b020301230a0c0503060d0804030204061203120b03060712140703140705030408090d030c0c0303030614010302090a0e1b041d0915040b10030b01170105 75
    0xb402020082d10400018010380c090355a0400c080c50014418804006140a00d40d4182006945540b03001c0c000c8290068a0120301035020031021201569512441c052044442000360100480c0042000503c41d250401104840512a416042c1019180e030007141c200e03459070f08100071200718122410145038100c8102250360b01340c424103000307145c41c240210b9262980981564103009203031446224050343c9401c219240200d4038001034540c42c0c09440200900402d03403c80d2000c00340300b000300b41207030712980c103ca20954100625514000c10402840250210ac840c00d500f003040300c1890600254060251400450107941c002c17910500f080b42d1204584041c5400b00d05040c810450a06030b5200c00c8405001c5424140c48400035a03211981ba090942c03006400055890713000030040740e0720700728491a038010f40c0e520a00342d5650340c55a40780c80d43c8914844458050ba03410703000040001d2420b021040e400850015544840c543d01e5507007500f01082a0009042d9034500b8400b00c68441c000d20985 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 53968088 1250 53966838 53966851
    0x1030e0109050c060c0708120a17070e010c08040506120a06090b01080c031b030403090e0a0204030f23010908030a0c1b150204030c030503070312020c030f071a011706 73
    0x70804a44190b40725070341e42d1941c03480c0714021031010440c01183c05040c000d040041a100c000e40d40640c100d40440790f0f40381e21041d0030f24041540c030b100c1964004000d490f81d0344241c002c1d882c1d4411003100c02c8015922030030100001c5643c150108000718003030316520003404a850070040031403580e0a210034820107070361140e00180b20b5a49011701c1125160b0b40b060300300b6008003018403020341d1381e25207491b000c2e0600755900c02644220b00002c10301c001c066000c44600112014645e0000755529440d9400080c2e205501c80a09440d40c4001c44001203003550f2114885089280c142d100910036070369a403401d444a503541a100d03200b001c82005551101c50040c05600b141e1403070950808500c03550326000e81c038030a0002900074480b004450403141c4032681124041d603007105001d0304241da68034095690743d202c1c450440000b03940c034007040701d12076650095464184004014605020b40b6441070480750304606811364542900e149070303010940401e00560701802010409140412204200c82d14008014144 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 53969338 1250 53968088 53968091
    0xa020a1406070c080903100908071202120403020f011206090608010b09060904030518030a060c1b031d0109051201060f062c0d120504090f06030b040209040218090c01030e01 76
    0x10421001c1d842800c9003031250303101c10044c4d05e5480b07070008285044403107003a40715014074228245090126680103003130018440e09104012400c503074000ca1711082516540c1d50f030000d0610003800140780a9800e50800c0c981071528800c3c903145080c501003591681e0381310b01e440e1a41c5c0e110501085000b80118800c0c1383c81504e40310f10074148080451800c05004102504026004c0761200c0b8407800c4a078a48690303007009003128034020703080c208140100701e81d030349007004160b14810321040701c41d0903d0040d101030f805403681c9441e5800d802c0e12003406d07025070040e2810801d8401003c505681c8004102840c0380301c0704c00000e003550600900c3e54a850043c1c1092007401800d2099030a00c4552143c514224110700340e1111380e06070800c011032070b00030201c4402420804001c1c00e40c880282d01c44c7c0900220340c0066000d000c64000e0300264006c0316464007000d000004040c0014000d41011301d0055001840648210810208100301402034901500c0d03c05258000d8400d80c030341c075030f0b040c081c0111348070b00c0f03100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 53970588 1250 53969338 53969341
    0xe0102071223030708060f0f10051c15030b010501050301030804050f060906190f091d09070305030c0106060201140613050406110d0e06010f06050307030506030a02060a020a1406 78
    0x45a189002900e28803204011400e0035150000070645007003200d0b050a000090303100e00700003070041c0401c10100d5005d03001d02c0c00b6010b00f0300d280c5441d1025240501d400307441c07105207445e200c4007242ea90f40004051801c5045005840318020464410120140054000d645015041d4507011660f00c80692106041103824401403011030701d05400c580440300e084a61400c00740d101d2011a600d40508040305500000120300401840074030541d081e9560076507650744103100c100c0320054509404c2400f90341d038200c55850b100b2902040540555400140210448070002d559170b4a90b440c50b40051302c2098242d44030703141002031540900403000501a02d0300d01000c40c0c0b9080b00422000e4a002c1c0c040c10006071608042014440c460748a5048401d0440410781c0d1151100038441c05000c01c054000614800c0c040001164100661620103413503180c5d49442c5951036a200442c05800040d0001e641805480070180060b50361300c00170441e0710407036005010742c500c25050086050480139a4503e40750420380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 53971838 1250 53970588 53970593
    0x81203010510090510030f06050907030509070501030c0c0803130803090d180501050d0f110409090506010b070b0105190e01060e0907020c01022820030f0a05071206151403010e010207 80
    0x100d841d503000c0d17540c0b60000d1040e0800c42c41c50050101c9900080d0009604003e124034141d05402251241c00990704580c035150703179940118203c65401581c84000b0f944c0380c8840d80003505581c01160450035004c041c020044040d01c2d24145580141c40e20700595208000c072203940b84d00400040da640340e803000500101494100080e11034410307800c00d01401c81e0b03251424006030360181c1c0440422500401c41a4a072519032400300010840b0541c2600d0b244180000001c1402401c0e0499089560000328100c25920b0171050214800c886694010150039030b00e0301141d825182c00d10039000785080d980784140c0608440900245101c007400a00c00c54102003485007103a40c00060070140b5480340c03d0350100071140c900d41030110107100300c40104180d07042a40b042020000e1700f50316200c400102c05645403c1d48000d506030f03640200c5600140740350002d1004011300d0300d07000b0100030040d00502d804142d46c07441d41c584002141081d041a246503403520b584a02c1350800b44192a5909100030086180c5003054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 53973088 1250 53971838 53971849
    0x50909010f06200f061006111216020d0501020316080c07020d11190b070203010c080115050304030e060703170a090c0905090f0307050a02040510030308061002070812030105100905 79
    0x40000c0f036404005540042024040226440145880c419a2002d06204a02034003440e0700f4440d860002e200c902c40762040050201392022a041e08005283c9440034145140042084a0300144ea1046085800d0404520280021449032001001d00301c60701244180140c00d505000d09290f1000206104060060307c4041c540700380705402c10070704c2148070744c400c0014503c8210315000b10480c0a6400000a01b81c6441c405000e109200714020321104868100c1202d5040c82445030402c407050303244010081500400085401900a00e030030301611079100d002c00e02e50f0340002421000114a4450016651106074250380c0001000c41309100f01407207500e50140481c11030291894555850700881c200400810010503ca00c0c4607056076141d55060403c01d0f1160101c1100345d0069003484005451110020000010382c1c0d419180c80d0140d8403030700d0030300c01000388040c0c001c1c0030340c07140740c00100300364004000603a005c086420305280d07a581407100784841611582c84507010312149110a01079543ca0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 53974338 1250 53973088 53973107
    0x913030203091905030708030705010e01020f0a121103130c05120a021509150307080106020102070b070c0201170c041404060302030a12050d151d010b0307111606050909010f06 77
    0x84842c80344003c07941c0319040c842806984040d51502c64070360b0000b58580080b010780040c1c1e0281000708041c9920041d618245e2280b000e140c003071404200410740f00180260301c3e00e41c409100040010700c80b003240d11900c500e94400c2d50000085598000701108002e0302443d42805088c0503200818040003901195944078144c0344004c2c07080408000407110b6044c1c00701036421000300204000d055806503410401d072640305a42c18000100300800114005005008075560b90342d002d0b600d1003142d80d401c40100c071016242c00b4224100280c0700c03611602da00000300001e010b507101c41071480e82e80d40b034821503441c00744030700c00003501403070820804001507030b004a44c50f440c46030013818100300c003151482c0407569032141680d04100549494903400e0807809a482203001d81d1100440f02001c8206074444c4541c42c04c0c03d01c900c00d00e00104000283c0901c1c42100007024020a03441100c0704800320080c09201e020103604078000040000c170301c003034052800c15400e80c010080e0f420f0010031141880c5005012004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 53975588 1250 53974338 53974357
    0x3010908030109020a0e030a08030403020f03040602120c0c150405040b0d08040306110c010c0306030210020f070603150302090a090b0c0a0207060503043002010515010c0f0201140406030b0913030203 87
    0x134049044494107004120001c80c1403801015210340001e0362402c0e0300c1d00d400580e82600148601c2da0808a80320001007100c4c00c1c1c48040d002010b800c0c0b24403890400c90ba00c01c140c0000070780a10784050341c071900c403070402d1048000800c0307009442c0c078201024023045442100e14644902d0910300c001c03000c07615807001c44003681d40042c03005c18584c03041c6c0c80942c00751081003e100350a40c03812600d84c480e941c0c1580a003003500d10888000d002e5080e0303050300700e13070740c658200c1c00c01d58130f401030306003003150500170340c803502d0040701c41015041d8a030350780c0d0000307500c00341c0844240b120552104155001c00012050281d07200401e001c80500340744000d00000d40d220101d0041d00c1c01e01c00000045018044101c0a400e05401e41646010810001d6804045142c0c00c1d00f0298000d5170801e404556088e000d58040002c0f08030682d10b00d14203908685902030014034201742a0b0500000202031122025108020009844251004512041080140055a003005000994040131006507400099010048031030720203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 53976838 1250 53975588 53975591
    0x201180f06090f0b0a0f0b010509060307030c140d15151e0c021f0e040612080304020a090203010f030302070503031201030204051503030a0f020f010903140c03040f061d03010908030109 81
    0xd005281410500040b80030140c4100000410806175400c1500417281c039940384801803041014950054400b40184901994002c2c8248001001c40d8801e5100c4041c240c150b1a161004117511104201c907a403200d05401d580e00d49400038014807d0180c141ba1000b0206044502404060044010f019401c042c1450304840000303a9000b004038824468021216002030200c001c040c0740c0458006406c294015800110b0001801c40340c0c1880d181c803450381100c52145148241d001540c1d83c03030314213a000400499000da41407101081401061000d1800781c284400c1c11070b542c074114200a80361070b0560703200a1090380100310400c031100c3e5901901c0d04480e815640801d00c1c0c1c442c0700c0c1c0140744841d4100404e030540310103d01502d030320780d00500c905903000c95502a0784100d101da5400c14241d48c0710300300c046c02042d00c003011503816940c0140240711025800064038182034039085804005241c40d4052800030b01403500d0380c0454281c0c0300b4034011218003203000700906802695616090b000c14403407000d105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 53978088 1250 53976838 53976851
    0x601060f020a020a09050703050f0903090d080c03030109060f08030f0a0809101103060f0307050f060a050d09050705090708250504030510020d06150518010314070f0201180f06 77
    0x5000b00b11208a259006000315040c50301c2c2d50305d00c00109811501d00d00041d0030a03020034001290000a40c2c0244c2642021354900180241807000b41d0040721000c48151004010200c0b01c4401400514080c0580c0a0042907a514001c501d11000e01c2a40050006030810440f071040350021508950402c002406c000c1e40c85c3c0e45120039941011010100c0d58005070030166540c0c844201000190b100302e2045500b011010510b100785556024103014040e00507030411881501840e1070400784c50420481d141c00e610300307003c0c00021301c150358000d1400c8415500440040c8894500404455400b1015250500340c1b440c05d4280b0031070654140e044081e40c4400c00343d00407002e900c11001c40c0d01030f6402c807045420b144255046800298030000c0f100007164035080011030848905064000e0040c072070b580e424200125914801170591100d0400b41c185507440e440201000c40540d00144541225120404284c200340381c0a4203440309280d108454221890754200002c030308170800b0194940024000824 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 53979338 1250 53978088 53978117
    0x20313111503072f06160201020703050304020405100302130902030607051213060f02040f080c06040e070302030c040f030807020117010f030803090102090d080c07060302040e0a050603120a1106010b090102060106 93
    0x21092111101c50350402540040c4d41005000240180501d065035102e44e016070003060100e00700e01401c1e00c0100050400c00224025140c0350308025005440d09943e04000d40c0d41e54001684e001110400c135800e1a1500c541006511703092000c0c581c48041070a2461810b20740744051952594000e09845021003038894103c14082c00303a005021141c01000d085590399210428a0b151101c907202d442e240c1d100342e01c0c9020103800c007102581c04581c00c041c504029910381034415406034000420301c1340700a006200014580c40103200c0c0100443c080d081165507524035000040030903e031440c2d120503101d03170701004004814160b0950012030b0340082c64075032640c0754015098060311038001c0e0594054420407500c000d1001c00c10040c0302c94070302e1a04996026564a40544c00c1c1c0c0914031502601c0d6680000148000c0002c3e0003556001c0c034003c05440c000c1402800b07a6445401c1806c8880004050207605600e8503020012a40940340214000b8100100400000d54550050240030100122801f20482 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 53980588 1250 53979338 53979377
    0xb010501030c030e16170106080606060d110a0e09060a08030a0c050703050604050d1d030705060c010b0411030603010e010501140f01021203010b03160c050a060c020a0602031311150307 81
    0x94259003c002d0300c041c60076005c803942003440302e805601454805503031100007085052181030300311181d210180280f9a512000c0100b0794000d400c034922019100d5401d500030710080d40c010700d546001900e84045603800310080c0900170f1001802d141c06403002200c103201001000090780e00e44d06440c50170300700b085440e113081c0b4200440d0b41d1008101d0b11a48040c0000c001002c10420f5840030180e842810703441113110000504202c4201c1280c143d00811028084c03420000020f21030303010480000301d044c80d031040201d0101c922043c42e04031400c40c04030901c0050325080c001c44440c044002d009105c1035040103044002c40001c8a40030f0720680c0704c25124504c41e4000c0c083c80d4608214203100945940e5100c070141129031085070f0050301d600035082d846280e10301601200f12490703000401400846040c1e0f4502004080c540800c0042d840340c41d00100c00030380c2d0742c001184100782e284803030f10300d5803000d1410303030818801044842d04c101c1c100d20302c03411418000700c04e8a501c559680742101e40720002554224 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 53981838 1250 53980588 53980601
    0x60c030207020619030c0504030b04020112110a02010f0608010e030306041503080409020a02010c091d0405120c0705031011071b05040203043f0509062506050105010801030b010501030c03 82
    0x303411043c0454111410320b141c241d44842619151401d215030001c0c800211680c1c803807800000c10042065020401651294079040b000300d45034030340050742c1405444400c074150015100301e00141e45074241c4601d00c540038002c1c84000c2a6007802446400101032140d038890000a00c0b40e402a6514000c0c4101035083c4090b0000444d00850801d59481e11002c0c40b001035404822420059070a000c41410340c0c07485034aa001c1141c0c801c07442060043c8001f0108818510090400d451074802c1841c065440c41c20f03500180404580d4500420350146480305041c1428a07614a0b0755002e89000000248800400304a50495501c006003005260248084d8041c0d1000d41e044181c21520110411080002d00c2c0002c0c003011002991290200840c01c6d1411000c0f04141c18809403c45042180702451380500054031039150020b0009043c842e00d0881010741811090071a506066100c42070800d001140c41942e0140401303107003840b01903042d0f40314000e0b40741040c41214101a1303030310f03060700c0b0340e51182c5d0002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 53983088 1250 53981838 53981843
    0x41502030103030207171203010909020d17040602070b0a02060c130909032d050931060303081308070b060607060f020c0d02010522050a06090804151704060c030207 72
    0x2191a075840e0700f4000c0d80e92a490240340b21700c8902017860804903030300080341c0c210b0302c03244180203113561300744040007008d00820401281c10100c5441251300003000141014800d01c418481d09440f1494080700901d00060307a0b1203811541e4080005624444c0e0101d10075601c04110000d09540b400d000c09035a1843e80c0c03940c8200100c03441c1541020801d54007010302c0e18910b183d8100c4400342418209000000c81c20340e1081004100c0402c212005414950701c000076200007044240b00b02e001840542030074100c4400b10a10303441e500d040900416070010110f54025080100410007044550b076900071034440c101020f40460081e03800545556525401c80d003007075a01030003d0003104e11203038121004c0c0d004601808224014102e4200b4030610504c5428030a04500e500a40c2d441a1940715019000c00b050003a106030103044645c01c007080041c0070f50b540c1248540340c02a581c0c1d01e071451039003200465210b50810019100a0401559120300c41d440c1c1050b0020130004100068110640003803040c2c2c00700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 53984338 1250 53983088 53983091
    0x1050a140c03030106030c0305060d110301060914040302010c0c05070b030c04080a06060806162c0306071206150c060b0f0a1403120c07060e01030f0e010b010e0618090415 75
    0xc000c1c1000010010350704a80b103d40b02800110001c00f0b09506850003200c00c03035006551203480340017107040d0180c4440c041c500030f400041e826807a03030001000e0795528518050440b10300d200740401c060b42482a043c14081ca0700d07111440110380d0f80c402c0c2d20b410080c4100c0c040100044003085c8900040e43c100d03001040404c040390900c0001c2d1070308a000e425644540e401ca4026000040d40c034401c0c411a405024546270344034108000210303040070000c1c82540303101d41d2911002c000e440e6903890420585004ad43c86458441a04143c06194800c1c1d504a8024039100d4402010b8404c0450b0010309032084160f0143c80400d001200c031011400c2400511105e0b9030201000100080000303114a141408a90641c29191403850b507403240c0801d48a82e406c0740c50319a10a000c2000781038450001e00300e280e00b051401190701c0b030a001c545000e6500500e03d01c0c1d074036592074403003983d107681080c06a441c640003946c0c6a0b08041c0c1c040150040c50a4842e8224040c141c2080028100443c0d00c84100c52001c00c40d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 53985588 1250 53984338 53984347
    0x12110a0602060a15120303020c01060e01030c0f1a09060a020c090c0705010e0106030201021c0c0b041101020f0105040201080126010504050610170d0f1106010324051501050a14 77
    0x34000e40d038980035100003860518180381d9051005140c1070b000c05540794444241d030959100d6a04400079400722112031103d55803214049040c05d130040216000714001c2d003c41202c04d051248080e0580c81c90703881100640c100f540048500814801502c01160b811501380341c0700d06114100380d092514035074010398010115801c01c101c140500c0090034460307000340000c02000400c64010341c02c84010b03002c041c1c0968410960714442111501c401c5040518a26040301410701c60742e03130040b046406443c111002454002c1c102c0c0c131560b040000c03000c1a09030000901807400c141c0c0028240e550f06009400e14a0315070007107042c004030005144022401c2200003003105182c141401621a80181c13141070184400910020341c0408442108504040e01d2015102061490000380c130082500044501885440c0c1c44441540c041403119034004c5000c1c0c00f116001e452503c010b103240c0c071a031030b045d0b4200c589401c0500025000c410022040a01300f07003462030341c8481c5140162503203603604d00c050704c111300c0018 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 53986838 1250 53985588 53985599
    0x30c160506071b051009030216060e1203030721020f070b060a0806040b0106030510090e010902010f050708040302040b0d0209100303080c0a080a0507110313140d0503030112110a 78
    0xa4054032880706561002201010f9141e104042060048054642d500c82010141c419402e070380078200e110b2107801224894610040115560078956003c0000b00b40c1da00346501c040d040001800d1a000d21000181d455441c100c01c016000303e851540c0c442035184c1c0c4249a01c518204e41c1d044480d0609074a1080351600d80c2441e04001051003122994040c07022140d0010381054005051401a07034040d0100c030040e07092803421401801d0040c1005201084c040c0001108007841c4510b00160319200c001083c03881c0e550002601f076600b010000003c0000801c410404140103409071810380381c0c12500451488400b0002501c003003040d0101950204a44040c1704166203a4000070007106c0c8030b901c4900c5656607508605015004401802d004106004001106580d80d0380c0819403114860030050014035440c5040ca103541c2001b40d400031014840c0c5028031102d11026111410f040c82210956034111441d41c50035120b02040c4074441004981d0400c2c2c0341000b0b00d12950105090026000c682d11a9032403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 53988088 1250 53986838 53986843
    0x6110c070f0906052b0204090c08060a0b01110a020d0f060510140d0c060309020a032004050a02090d0f14030304060506010e0306090c010f030e06010b03061503100b030c1605 76
    0x602c1030000d610702d0101e000807203050410303240c9040f820038000f42918114600040440040b09282264001d51313030003501c00003900c41641007001d040750340c005119034038081000c801210244481c00e4103200e500e00c0c111850700800510000300a174140c4840e1a54802490031807200da41ea0301c0020002828201045070b102007500c140c50482c0e00141d0010003a6003c101800101901071902512003100c5040c04c0c00440d02035040040321900c054880005030f0303500d0b1524034104000c0558050f0b444030354072002c1c000d031400c0e005154114044040c21443d0a601c4000070380742e000401c50080c010f420b4407400109016420516040b044c5c1c64078260313070703036464280343c618001d1034120f071a01c0c0410240d003d928040c0c103000480c14450a0200001c02e00b0300403500040d107244040741c140d0001c050302c45c0039078034040c1401d1240c0742c02028200c0903070703403207042210030804022035506c0c50030407180b000d00802c003418a40c00003801c112490743d445159a5195440b601510344240d4010444611402d801c010030400b00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 53989338 1250 53988088 53988119
    0x6150201090c0905040b15010c0b04030503101715130501020408010b090a0203040c03080d090f060e0f150a0f0b1012060b0406020631030207030303051005090406110c07 74
    0xc080d0b8441054a0300c03051402c44e082a203010708150480c500191030000d14202111600405040024000e0b90036940c0020310082124210001000482403141d0700d44000101e0002d0320b4800e1285407484515141503035a010b04d8515988903040708400314039140c003040034200140d9000030082d9034490701c2d21100350107082030501c8a400350000c400014111400b070300c203481c0501d6010b40100051851038031500317400d0704000c2c0b920f030119a5a45102c40000c4c42a0f41480741981f00306804a156106070284604002c56108000069000001c800c02c00800044002d584000825400180002400b40c0800286800303008150030030055000004200d8004051440c50301c540481403004a455105003080d6005038480c840142e40b09070040b440c0d01251112500b01030950604a0030b034415903020011198604e82c00540158200003005d00034194940a1580e1181c2003405103007031545000e0125509440051000c2c1c901c1d40e60310801c1c4082031107001114000b03552041100d40c21a08c030b580c2d0a400d00031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 53990588 1250 53989338 53989343
    0x90e0408070c0f05010e040e0c04090b0402090906040209130f080304081806040501050406030b040b0418060b010503040c0303050a090314030408010e01060e040f1104060b0a0807020705130f0615020109 88
    0x2606000101d042c0301c068103206507001071b0340b550403140142c014031020344001d582c80130f95070203091000c00141d00d0300d100d01c00c20342c0d0042d0f280300540d0030a40103000ea20100907041010980180042101684808065541116450442c83c140c0d03191403d00300011a0f922034001c02c0003a001007030009200c03446000d401010482020f4560890303030743c0e040111605c110b00c10103000c5802440100640c4d0701035801071107040c0011b4030120f80710301e44d900020202d405481510100200455034501400464820f0022240f0b0a00b082460350a00d07444100203900c0701e100040400500090910a461142d0402c3d40110391020b4110b50540c20382840070384a070814080d4000662a150008800c0d400500605044071310004034000141c8031601d234503040c407610442c16a00440300c501c0d02d61b4203131034900c070780c800030051005025180c40022100030480100501020115409080148519a540700c8104104859424000340b5110206100405001c0c15881000824108050100c801d60190411803c2e00e2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 53991838 1250 53990588 53990603
    0x5040302150316092d0308120106180e0a0b19150210140604090201090b070803060a120b01050910090912080108030301060f0e010e060d06090c050909060402030601090e040807 77
    0x11400328202c4400b03485100381c2d181034a0340c02443c02d4525504642c1120010001d4800081c5c94580c1c0f1200155030240f103080c1c0d06481110010800e6070703131125466800720b41301d41503001c0f0546049450300454502500360080a035071104c01c200707180d0700c0c080001d01206105442000e00707031391200c840c5900351003802c410300940566400c0b030811400c144a4603a682040c84060200d03074071400f0901000305582340040303040c00395120010810000c3d080142c25468401c42140f42d8902d070a4007071229402c4d51b944114002c0e4017115031140001c142002d65415640c0680d01c43c00c45680310300300c1030010410b5070f00503450300707117010b0380d071810f00903e84001b40051407191290103490742d031361504695a200900c80c510000d60001020807071207111341004010541c0500d001c84d0001c45074000240309500050144441c42da0380c08040010031711501400e0204c0030396003011411329400401250341c8180041000b44115400000100309a009200400c0075250001d2511500d140a15041c4003d82c4802c0c41a03036540d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 53993088 1250 53991838 53991871
    0x10506130b0a031101050c0a06051914150a0f03030206012303120310090c02010203070909050919170c0f01050a0c0504030636061b0e060a050403021503 67
    0x20150340c000c4894034203024001c110b00b00d14548074040340760044480241000070070070985012044c10800861641d0060200240c64100600c250800442d8031000445413070600015001d40b610300072059a011688403001d05002d0b0ce0100069420300440d00700400c030f08041d00000c81070503800035405050312000e000115203185103100b03405004044080031545039207c0e0001e4035482e00e40324040e680008000c1c4034540d009454854400a41703d01070a080b0050b9404030402c50340319840203200c1c00820700c03036070104501d0418100b425201c900300d000c005405a0308a094504000240001c50300a4017000240d41e11480c01c100d1590312044180380e810429030901000c2004803145214800d41020b0700d440b42072420385181e40f66000b0300704000000c82c07103000005208a0032042c00306034455030068002071515a17001460403a04844400e110744044030541d0014543d02504102c41e403100e540300700c40b00358a4115100c800c5901d8400d5803c002e40000103610650f06034481c0c20040c60080c050080702000c070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 53994338 1250 53993088 53993119
    0x2070812070203060c0d0209030307121b030e0409080c0111070b0c0913050901022703070b030606180604030c090f050106020a0f120c0b010b071406162f010506 70
    0xe0702500001940c1900010045100c4011050040900c4c24641c1c4015040030201c06c0001d045403c078500c141c5034041040b0100d1807142d404485c800c1c445010000394001c62076180c5000b420b17801ca010015000d1665950203c09000c1c090054035a0302942c100244203806440c484604250041081103d48083c8a40070544149503001982c107007150260415680100201c61305003e0403003d0004e1615540c00c201c0c1d000c025540210040c045980c0101c0e14030f139640100203151400034194041402501c0500070701590303643d903004803440080e09110a441e110080c034000341c00d80c4120341c002446804c0e4041d0000f800106a040b004c42108131385000c00260780e85101c266110140f011004107000c43c41c107544c20008007101140348036564286002100300680d583ea0024950782a0070201c010000462048100440020f510140002400150100381013a10030104101c204192120500101c1c00c05080ca040081c803407500181e405801a00200109850b554024401640d030345000d030b940b11a00c680e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 53995588 1250 53994338 53994373
    0xd060807080706140313060c080912040302030a1b0e01080c0a17060a090c08070b030a0c020c010507200d080a02010f0b06090f03010605030604140705150403030809070b0a020708 78
    0x8860258a8034080c186064513582c00301e034001403540c0d0201450811000100b0003030700c1001c100100035260200036082444040b40f411114010000100070100004d1005807004a0340003d0594400b0014030711441050350003c0f4150150809010348400000000d0550000500302d41c8401701960304c0581c4070340f43c0c066003d50503c1c080d890350071540310001044414281e540728108041c00b8045146510303484407031040c00d00e4a240d00181c03811b0808014003c141c1342500c100c040d601c8050000741217090410300081c140c2c0c00b8444c0c0142c120059a0070f03042c640c04980c0b215019108000700786100c0c541e42841c0601c2640c010a500c800150b1800440002060182c0f14804030004014801410030442208200301401e8040319150507549401d400607250300d00700655800366204040d10070035000c0440e8040d14240d41c950007540300791142504034a00984400454050b01c0e01443c040405a5a406989142543d03d60002c07403007004c0040c4ea00030142d40031a02d40140c41c038081c12358007070000c8042c2151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 53996838 1250 53995588 53995603
    0xe0703050708010e04022b0303050c09011718010c08090d020c0102060a0902040b270c04030b0402010f1808030301090f0608070e091002040b0307030605030f0a120c05030d06080708 79
    0x2022440707110061020744001d41350f0541c007910051402040042c1c01c041c1043d80c0062030a00c0300ba0513002c50f816010140c02d0701416500040800c01181040e2680c00003c0000001e14540c0f0440082d83c40440d152042d10500c00c00480e801000a006a40d9500c80051020304200c5907054903010f818003185405102041104203800145c1c001c2100c1c2d03ca00c01c0310001404014012a44180d0b030344c0d98140951a20b000c010a02c3c0d0f4200342080146c03224044403c500c3e00010160412943c0400091000800940c0100d401903020307e424401c84002d038006503200002102005c00003501c004c400119440d0000040d0b0580b42e40b00414807807a10505003840a4800d6406500007540114500f0b002084480700c007594010b2a00e42260907100c5001e03088400c9074000c3d0070515000c0c01c00070400030400d405020303400080c54198010091041c0d2a9800c82c0c40c0c1c0308005000700140c201c4289801030304d07c14000001861f410800b80d0b0f41d074000b5080480d00410007880344440902480000141da04008201d60703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 53998088 1250 53996838 53996851
    0x4020309060f070201230406060501050a02191a04061505011409040c030212010f08010c2604170f0717030c04031202070f03080711060414040203060d0515010e070305 73
    0x14801030b200c411000c050b01000400381401c541d80c440800a00e80090604101c10340c0310040304007044d04050408506482464100c01d05000042285c1c241e01580022100210315040b41810051000751170a02004107445510700f040d101c10382c041c8001d11400d075002c40c007484400c01c07854005a58450040d181c0300049480c4020100061100031401d00742500141115141803034010b18003140d0980d6640c0c584030a8018601c094008401489800f400744240071402260341428103500a10603601c4009110284c0002c03003042081022404100403405c00320402042d81c026203449880382c3c1c07000e81842e00a06000c1d00c0703e4039000146e030743c0e168281c02124060030300d45c0d10b005c1c5054119224140b2404440402c64110702c10014001910b0a0080507040554462402c942d0340ea03005050403401180511030081c484c1c00104810481006040700500b0310b28800d940c0540c907552000001003401213403410260080c00760400200c204820b010000d03060f54110050081c4540741d03080700b18122002103644 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 53999338 1250 53998088 53998093
    0x91003060b040b120d021005061315030c0b090414070206041e050a0605040b09070513090606090f02031e040b01050f030a060906020405030705031204051908060c070b0604020309 78
    0x14808a482900065208480030300041450a50040810802e000e040441d00c1283c02c9a035121084940c18081180c0440d505441807240341405030000342c9440b0394000c0700580c0c580d1401440e02603260003203840d001307607041064038140640d80d040e00c8650f548111030355449285040041c1500d03144070000b0302d00605056006010641e50b03659000000e400007a1790b030001160360f14034480002d0040184100b07a6108000109482c1001d01c0c0280c00e140018064406640061905010a8a920051000d2050244404910f5800c242401c0009142a4114800703042c208003501c401021550021070080b00380c901c0c3c6000d10100000c888400c0304041ea001880c41c200e01004111a1519500e8000a11030007000d98007251301540e940c00840c0c1102e042103640940100e0104101d190511001008080c10307005480140f1082c502ea850501c04e900036148030b00d10409111030708aa42c000710034043d00603039049495508001c0c4d002c0c1d11300c1c4c0180340300b100d50300c00d1000055003508060098902800b43c4100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 54000588 1250 53999338 53999371
    0xf06040c0506130306180303270803220f0219030c050405061215040b15060403170f040b0c0601090e0c040e0f010c0306080d03022a0a060603030503070305010509 71
    0x4011030b580c4154181ca1403842d800701c011011500340c0c0710701402c0142600f04210071100e01d01d00501582c102c00c1e9011210110810000c202079660042290714941c00b818051b034a507500490020024075100402455103911841442001045c9d007141680500841d28584841e288208414514400b17020040c60704211402c00c01260402d0f8000c1900200c00801200b10440c000c0103291804300540c0591508c41c40c00814081400141804150072000c8440440e46d01c2c80044081030162240d840000d12101c0100c00814102d861082030792030782448180b600c0c2d55182c3d181407040c0a5000381d2903403900343c0035810001607200030900ca0b880c01c001c0c803080682107401080040000030621401c09030150701400c403101c2aa80f0007846034090701e00c602e440002c2c4140c14180f40c80c1c645908002400d040c1071040100e00300d00050300e0b0302c80310501e9455807500580c40562008034100400041c00030491414040c0110425400c803016501c22842581c0401043e81d07900c0810040b11401e6400c96080c079110729 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 54001838 1250 54000588 54000599
    0xf030405042703110c0d06020711030309030a0f020307030516030b013204060e1305010e0d170415020703030b040c020d210b0603040302010c0215060108010b0901020a140105090f06040c 81
    0x1c43c0c1840007285015943e0500314171010032118255160110b8102d80d00040420420600104030740c040f15050b40290f0600305124046541c030222007030040c064030000103510301199000c10090700690340c010305640c069001d0341038071440014503020442c2c1320380da45000407484000c0000c90065088041451110300c20302c43d100d913a103d03282c090f580d0342c0107504c540e40803654900400103e40200000440030708246514203100c1e003103664094110320140c01482042218035070022592061140c042e45040c0a5111840d000d80b848003142001c20314240040b8400d414503030181c0c00f0f14000b5000381c8090140000400e0101d0b111b400720b08401003c40c1240c0042515050031000e00310340070020080029031004100700149842e0421901180140e440707000319140f45506000d00c14607010100340e200614100300e0000382c102c5405008801c0200004140c1501681c07007000b210b03000a4210300c103420915190705245000c0d2504440103031141c8503502c202058020300240e214480d942081400045e60b0800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 54003088 1250 54001838 54001847
    0x30f0a080a0f111b01120212040602030c04080f01060302010f0c03080703020c100618060e04080307030216020409050703020111030703140c03070c08030403150507210e0f030405042703 81
    0x901c100000c2040030301030b0665200c1c08124282c221403850001207203180b050800100444c1c280c4908646071b0340103221441c0d0510392011081d40181d40502c0140e100d80e2007407400102c6010310360000c2907910401d1200d640f800410740c405403d82c1c2c000c0c0c7e2203042001c440c1c5000c0d148002d0381800100005c0603640040c440904c0790380604180600001a11420700ca200528000d0b105c603500f00003414141c51050040d155450302c01d41000f004c465040c80b50384d00d03145e00c440c06c03180401040f0100745900024003201c0d0721034884c2c2802c070090740100100325410300c42c00d03c140e685c4502c1c00201d006c0f801c400714050f10207400100f40c66096500d81d840d45a441004c1f003184e00c0a401540011549100a2000e000002c40c1c0c40300b1100540740902c000c580792851030078680c240783d43e00c542c00b0011b14544410321520030f074000c1e00c008424820300c0c1d802e0f14040100200f1401020980018010ba0060700c0c001d80032680c0100c02003003142c0d4100c800b403190745282400e00c0080046408104858005440c0350000640035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 54004338 1250 54003088 54003107
    0x1806010c060b0310150510120b0303160b06090606030c182709060705070b06010f11010c0504230102190302070305060a0203010918030509040b040608010e0606030f0a080a 75
    0x152201080b18010340003c2441c0a101c18840000c0c0c030703200c0303060070409140301a0b9040200300803514500070b44e02d00c09024006040107614003040340d848051240b03c0d038038100121040c0ea4030100240300105501c0c10100c81c9102c1c1070380c03074501c242100000314000d4600b84059034000c00900c0c1c10700b4584410405007810054203803200350b800519544080d1014444002c803a5450306003907510319540d03d04200720500b4014014000c80520505100507030210390307075480e04d941c0304d41d081c20000e00303000100c4826908164446181c204542c2000315003c06258000c025004032101c06041c000d1404002c01840c000140c184402c0d40140c0c00070f88603404001030b4030303079440245000b401500c621a0b200d840e60350800c5800c07201c0404036031b000030040080c0c2c4642d1148030100c0303132680815a0340750400d5500030160310070101602d00ca10b07268900300008c2d5545a015400607c46840204007031401584003648880c1d0803070b2411b2080c000c01c03400c00c8407100e010a078424201c0e80b040707a05242540c0028240d4203400c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 54005588 1250 54004338 54004343
    0x5060301090b0a08150106091703030411010c02040f06080d05190507020105070c03050a1202010c02070e0603031215010e03070f060305180f0f010e21070809030a03050c07051806010c 80
    0x46120002e40f0800c10701c0400c0a032103400e1420300c00d070340c148907014003030018a40c00407505031209c3c1e110007c0b942001c03003070341d4000e9802000304241466920040350050031658010b94414903101103080c1155490384004201e60840044e1080d284205000f9141030090308800c4192100c2e034078140803098800c50041c014030380705040c468109005520384400c1c03651580c100302ca460b844030034650103128004820280f424120701c000d000c0000c040344002d441e42654440ca22400780000e0100b416642d0a0054400089085005e50428a072241500e10610301c0610903e011421aa070f590ba03060601041e40c00035546446075110403245404030450003041c0040004610600035804e119141c0418410200d000007414000c2c4899800f10303d03200e084440400d076982442c2d0010022a00740c1c048111070450312043e12000c55102c1805042c0f802c0305208459095a16000d81c0d03030101304060300702019114403180f4100b11029561910140b00f6240000712841c031600c0c0052000552541c890b4040b110411b1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 54006838 1250 54005588 54005599
    0x16180e2107140601090f020f09010827060a05010902090901030b0709090c02061501020d020c0108100b0f0a02010608070b0d09021801090c030b040501030b07110c060a0906031505060301090b 83
    0x3041a1118000900314050740c2e841c0da00880010800d204d5103001d050107440c9a0b000451602e24031030494041d82c824110b285051084013400285100c8108800344100d81c800e94604002d0190803558580b07a0f403084501e030084526160001c40d000c2274510070b4480b1a1405044951141d00b16220782c4140b8278018044010884141030201e00b040145c002c002020083d81c00401d110304090010b20411000b0955071030455100c0d0020320300640d80040e810340007130703400c2c00c00c184c00f0388440d540c1005000203a00300042c2e140000400c00c10088051009000c01041c079030081010a4986e9009a02c981052149141151090000c03841002e81c56005882040c8010910700328401640112482e61009910000345246d42c0c000c1840016014001d124511904a40030005981142d0b44c800700180040c1041040003c200c45428000f841000b5155401d2002402e03180c4035010a00300404034606802800300090418521107030341c2c1c82d590504c40540300700500c11400c5030b0810343d4040c020f0402088060344078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 54008088 1250 54006838 54006847
    0x315010f0e13081308010b09150d05030c0307110a061e030507020312010e060f040207050a0602070c090608060a1a0907050f040914100602060c09040f0b0316180e21 72
    0xf03001500104140c10644c3c401c00415031030030300c0c0c85086444440156014440e4003081101d50002c048980d560304e841161000002c100e14280640b07107001d00b1144020b640310010f9034105002c01c1c030503d20f110b0001180c1e8900c0c071540b540ba0032210802c0552110b51544000700c000c035150f5029810030390340000144112400c0c4002c0d0055080e040200380d02070201e002c00d200502005003891680c4000310354040c0c405514003800c030b9072401d6075016a0b10000e0001b950124600c0204042c940c0300800800c4060703c180f041c02d848006198036100c0565805410030319108402d4078a002280441203040d00041010b11150340745a400c3c0c03116400300e1072000320f003401008041400041032090300c0e41c440700383c100b031419440c0400000d0040080d60300310700300355402a401c11842c0300c20041110344040090f5008102ca0400220090140038400021580350150710075000007404d60303084c1c400c1120b2802101088000e00c003040001105d048a03c1a5425000031800c6804c41c1004461901500710030190141b03407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 54009338 1250 54008088 54008093
    0xc050d0e0f0603070801060807091424030405010516080402100e03120c0a02100207050919090804080a05010c08060109030623010b040303020111091e030705090a06050315010f0e13 79
    0x40e50b004440c0301d401702e49680014070605500034262070f030081c401d0920245041c00c044980c900f00d103c9604413803103410803a0032039040700720001c00207070710f1140072032910b07168202813170300b6030181c001140d84860019500b0305156200d407207004400d004030b03000781c0464200783c0803102c02c55140c0c400c046030640610403006a010344400080083c402500e601c409000c100c6c903a403042101010031000c0050071503201040034006550b45402650300b10860b800d0340c0280c1c1800340740c180060031395007001800074500030600085003030000c0350100000c0e1140c0b00810400a0107681515401c03c15a1858005501003005000080d600e5020861400b070111100b070701c0c1c0c83d44604103410715a090300035407400f0001150402c01c040d02400351510815086403054141203003503000c207180011049216031520110401c0031450307102809410044e18010b0f00d4049280703441081000540071034400c00d40244108002028558452420541640c08c01400c4403440761078046541c070170201c0540212039414815044000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 54010588 1250 54009338 54009349
    0x6020d0c210c1e0b06090c0f0c01060b0a03050f1e01050607060e0109080903071706040f06090b01091a06041404020a090b04030515090613150908040b1305010c050d0e0f 74
    0x100010443d0303101d0002d119807520a05061025101e1405091322005011021460300103680122511a2480b51949400741c000e5000d0412503100408602000618225481d451b80005115000744440401a07880b40b400d541c1402010031034010060300e41200512151400304000e041c543d0050390045204900c00d2241c50840c1c1400310100d600d40e81c009900802401c00b44444001001d02d90f202003010404148402c0e210040100001c042c100100c5584c01040200d80c040c0620f5070f0050600703002c5603110681782c1c00400034418846001c502c44502d0040c0307403400760121002d98a46203a1004880100c10500000e504103403004014404001c0d404611428500003800007103014000408040c580c00301c9070314038081e0151401c0c000341c11100400980c4001422078900207503100c0c00101040810504145c000c01e00c600e00100242d20008000a1161035600503019880c42190701014042d581d100545002c903c20f080244150000492244841e000741841c1c0003100c00a0445e01888981c0c100160 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 54011838 1250 54010588 54010613
    0x8090a050303190f0203030907140d05010f0902011d130b151c0b040e030702120313030c030b0a0903080123130f0c05090310020c030409090b0106020d0c210c 69
    0x4181c0100310025030455a0301210904c20300000f4005580345040c0036481f03a844483c50700442d9012604082418420b8880b0319114961640050081110f034a842c20b100002e000b685806a00045841d21458a8580003903500414000c0040911120541c01180740014100701d001a40d0701c070301261072115104400748020320309120584509045261001421130840b0611588503025502d405640c411030000001112101c0d5011a03026050049120000340341d881510342384588600301200000c10048155520030940380b00e11101040740e5a41c8440710102d404000c0041e0000c0c19480041105110034040c0d840c5140300c8801d0a2102d04092011514008401e00350700d0134247d5910000045010074031400796040028903210340b900b9034410000ea602c0191400c0f4003c502c1c0e000a2038103c440d800c0080760002c02e00d0443c14019928541001d50320301000744030b10005401000c50524a4600ca40903004695074007514845480c07000d09403070510b02c45001000001c0c400054001c0010a50084420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 54013088 1250 54011838 54011857
    0x3050a05070f0b040302132a0c03080c091c030201020904020a120b010207031101051b0f01060602120f0a0503090c1e15070506060f010203040f0b0307030b0f0a0308090a050303 77
    0x4000795440c14525070251140e5501c0040c034003600b8401440140c0e02c401c4c558421001e02507001c203040303801c80c03010f02e4060792202120030b1070380c2c114000d0f20751035030132607804404d03c1e0294682d00c0e0240d842c1c0d403600c00e107886264107150b80243d0891059159150302d00002000034060320005082c1844100404d04a0b4805494400410328a0041010402d058003440d48503090a1000e80481031440e0340c1e524a1155200905050003404078241c900c0f491100e0241c1a02c1c1402c004580c04020b001c04054020070311400742134018000c0c84890103105442508560b2184102c503411840c180b100071041f601600080c128855501400c000c1c000650b5a07039142180b4011030104900e0b049010101f0040c0140a1091400365800140000d0b0082600030544035440003003a108101110070f03850040782540708503040b02d980700c1c1c00340e800401e8445070400590320442064030100800b80002e020050a882d83c1c4859581c81080c1440c1440011607020141541080240ca40640e40c1d4540b0002802e680202085 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 54014338 1250 54013088 54013093
    0xb0a03021306030c0f0e180a021317030702010309170a030c030c0e090c0705010b030609010504020102060f0f0a0b040b060406020102090f12030d0504030c020a0e1504020a02030a0806040603050a05 86
    0x304540c0703125680e1201d0003007256040c100080b580c101c0b405030030040c10722001d00a00000c003080c05a030b5120b030740a01c8181003080308080c0f610325054180708002d400420902e80404d8610b180070482c1168130600c1c0e1084000e80d001507051600d20f07401140908544030041740c1c50200b0f141030b0140880e403403018140c802c03041d4170045040d025044004003169245400c00b01040680020388109481d01c400d1550070400c0b9800107a84d540190924601401d6003410450705480360740100100a0010b500260095100741e0945035540c03a8000c0301b20055001313880103000c07580d810010914a0000f9401911203c0b0040d002240850340c450000d03095402035401480035035000035090300645800c01d0b04141c1d0700b10480d0546004108002016606c2c0504050707044115601c0f00070805150082c4900105180c1c0203205136502c0d902e96440303980302c0009031940003072200320602e8a0700510703040c000c2d0340d07400c144c0d0360095091101e0590112146040502129001651000d011010840034030031014818010b000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 54015588 1250 54014338 54014347
    0x11e0b01120516030c03050709060c0503120708010f080c1309060b060409020d0e0d0c03050a03020409020f090102060f040b1b04030204110c0609010b03070e041e03110c0d02280b0a0302 81
    0x101800391000c25030405c0401d803812003003200e000d070071000b402c05a41c03252030001000d40041c9845442c0d07214810700c04400c02e04013010481d4080d40101054107175002c1d01c01003c0425500c0b4480f0741da5070784078414994042c0d40302e1000805d8100350361003842500d0041c5008a006240803011494035807258105c1a15580c001030700e0483d14215004407000c1d11030000050090b885030801c018801b01e80050004d042100016420803090301c2a010380340130300001002107503201080c51100d602c1d036105810860140c016103000030300a80401e0301c8c4500c15504081a201c0b1580d454014460400c002e40c0040180038043c0004400b60b1a98400c4c030700452140000541c1c0c424040189915012009140c20072581c1040103074215501c000c00d070581100d00000c1440000d4031149400d000c1c00384d030740c40202c1a51103107100c8182456440341030102642011410b03240300c444c1000c1400340310351603d10041d40201c803000c0d5950030300c0e2031a4a442d03c400709152422859036200c401c4410309600c8800f01600298000c136 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 54016838 1250 54015588 54015631
    0x91802070209090d030b010c1203020a02030d0204090c030605060a0c15020d0f0501060e06310305030a21020705060402060f072a0501030507021b0121050f0603011e0b011205 76
    0x6c20081c00b50024208484107603019503c01c5080c8003444440000c054011403165244e9008005540c103103002100155161034071414807074020702e504140140001d00340407001401d402c0c001d049403814105640e5020704142170b81c4402400c1a1011441c1d0445642008011910003a61140400c21040300303c021606502d0000002c011900202d00a48540000c101800c80c06030254003031540341c416130f01d603092a003240c80401c07007040c1d0030f030b90001d0034501001600f000d0043c2d00c1540041110091800d00c0744524003804180c0880c014000d008250790712030700100d000340c07510f1806070900b20a08204c8600d0081c050f5a90078440c02c10100820010a41304c54082c1a2260341c24020003800c420b21b403c0006180c060402541c52000702100c00c1086900307800c03405a42d22400441a10a0400705071032500d0340c001c001e0720020f1030200c8840700862405030202e1514541030284503244520701c240e1800b01d136a0076410100034004262010b060201d100341d14040b0000c81d0003101e105800341c2413848010307080d0b030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 54018088 1250 54016838 54016841
    0x20903010b030f06041103120d021210050a03080706020714070905070513050d020307050a0f171c0807030609050c030703050703140c090402040e01090504140d091802070209090d03 79
    0x2500d140c0b103034100440c0b10341d030380c1000110158040d800000c045a0000f1030408242072282007904650b52400000d9030007807250a40d001011200303a094a00c0c8856035031520340352100042405a99403250a17002d0810100300060702520242d4050100140343c492155240c0c01e4080c40f607840f104494002c41400c102d461120320400e548646141006403400040302c207040c0345d61015018851040702403510f1181951001c201c2c02c2d016280181141403807689400103402d01c10300600c0382d07240604128409001000d408a9118510b4446c0b90b42c2c0c03504c50002e02c13001c0c1c603100b2004160400b01036585000194003012070140500a0491508060352400d0581e030080031b480700140640300349070514204d49400b8800101003a480f0300080b9609455015141c00980a4801e5a02112810b00d0761400440c2095840e403015004921969900314940788000d412511403000c00300744030200d440883c0800141c49122056419084d1090380145000d0050b8000f8905250a444032040d59020f41d1a00300082c3c1c05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 54019338 1250 54018088 54018101
    0x10c05041a04051e1216030f060e0111030a0b01020a050706030c140d050105010f08090604080306031002030406141b030c07030c051906230a09080417060403081501020c0103090507150302090301 85
    0x245000f4041c146c2c08881c10300c04030705040c440100310114002606d8140241944a003a85200703032802484500c03001160100c3c01c0e0402c1d5941e407480c910b0000c681c60650f000281d01c00c0900d41c810003031b01f1220320302030041d0001c0205440800074040b48031190f600100300b0348000d001001428200060030b5041100040500d280f03030801d0402e000340c24042c00441c11001601036400381d03010100d680d503541c9041c0801d04000d940d801c00c0c10340c27500201c107200c1045210f070009803407281e101401482940d214449055441403043c0090301c4085c1c00c00120b504441d0440082145a000341089000d0880303d0b56050326045030031201400070908550203004001060041c8484031316054014841001002c0340103000c0710f4041c2810079001e40e0b0307a405504000700442901c0c01001d20f9205141c8035850048001d80f58181110708400040402d00001e001401380d03181d00c2c00142042c0e0080c0503495614005400400d0741910540d4540b14030003000078100c120307000d40c04a000c940c1ea80984c8a1294406045c00d5401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 54020588 1250 54019338 54019369
    0x70b0403030e12010605120703120302030c18010c02061215010302090307050607060f02040b070b1e0f07120c0201060501020f0309030a030503100b0403030c02030c03010c05041a04051e 81
    0x10100800c00c0440c0e4058180200e0901c1120303400700f42d26007080c1080c010151035110b00d4220003c058000340c0d1030004030303016046038040ca116038003012210104400304e110440e20880340344c030280034012011441040d6078060803018100b0b0703030300142035030000741894110300c01030030080b05228200001110060b01c08008034400303013820350910b4100030002c1d44450f45802500d0040002040c00010700103d600402c0e4040d40003042107544540b0b60680d49116071000d0020b454507030204c0003050005200480c03004c42d800c80d429800885484d42c51002c0100480500700c5c0c0308100c1c5840c017152504903244a000861b107525000026080d241000290400f030322501c000c0410741091020070460707207010851481d0b1a07498503005650396296046004650303d250009072000b030300400c1c04030402d504444030240340e50088044801c4100c8502c00c00d401e03110030084110000d84240000c0020b2000301c0d4100140700750744400743d82029115004a14001812185040502c80420007103103d0305045000c4181410b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 54021838 1250 54020588 54020609
    0x1608030a0c020a020306180111070b07020d050903030304060e150a0c0e09010b03061c1a0103021c110621040c090c02030f0403260a0e040b0402040305060c0706060503030301080f07 79
    0x203c1a400003921184010240c814260031b928000803086421352047c00340001c6410b8090300c400c581d080070310342d42c041107400380007501c03542d00340e40c42141c0110150364001500030015850b41d6260f583c1c075000313040d0b80440b074040c03440354100460044000d49101845154040e10006600079803102c0107041c0d03c3c6003100d03e4000c008020043c480503500b50200d0781d00081c29604283d52100e44050702242a118110160080c0454102c0c400d82a0342000540d04a90080740c00301801024038103032203500f0f4610b0300d0051010060300740f602540c1c1010400786c0075011140074016891085404504140b80302120700301c402c0344020702e06006c8201c042c4280070380a03000d44000d60800302500c4e1004054401ea0002500c5590484101e211048134900c00e640010b03a0024515117503004104050b2486c0c5200c0d41c201d1150b814102c2901150504d0700c01e503002c590300711005044e19128840344141d103910041043d9541605c5600200f080c3c1c80c108000c500915801c0b00804000400107407660400c1c016800407007103071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 54023088 1250 54021838 54021853
    0xd080f18090c0a0c110604050a0303030608120f120a11040306020d0f02071e0203032503030c18090b0607050102030106080f010e0106050a051305040e0a0605060307030c0e0c1608030a0c02 82
    0x966000001c1000c42c1d0b03100b00310b0021140c2d40e50015125007d103034492544191942e502004050b40740c0c00c508200c41d0720740100c403802c000680d82901c407802140c0d09903118103424420020f1016915140c85d0304100002000140c4c1c031100d00801001c1d610035002510016000150000440401d1080b11503290a2290841c01d040e46a5968005201d03020103600369146500c140e0400e5680500031034115244881849074064045400745240c04034040007034010a2078014075540080c0039420196407020800c208c1c207102400c000002000b085811201c5800060900650001850034801540a001661540740700380c40d01c00524a040c12050b00702001d071b031100000400c9215080016a4094019414180d0b12400004408240174950358403442c0d200f411b210070210340d220b000c6504401240202418040341d82d0700c00a2550f00e640c2840000d00640c403944080141000090149800c1158410790301e2808280503680d450744924030b002513440100020520204600d113210369120304442d8009010380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 54024338 1250 54023088 54023107
    0x1e0f05030c09070e030631080915040b03010608061306050f040207050a050703150606021504080a02030f030f160201091a06010c02030604050d0e0a140d080f18090c 72
    0x41d00d880d2022036014107030601c04119800d0150316010302080d80070b02110150f01d003404000c215484d01610003441d814074441c0c0d04454009180d00c01115139003042080307103841c5115050009846070014400302200d401c0c0000310340d00480130020360007410b86503154a03044c145072041108005110421480603803408500708013648400400c110010011a001038035140301d420081e0600780754400c020098050450084200001c507138502001d88800352042102da81c0301c00c01a0303640c05008100b54113000800c0d00041c00513020340700801d400c4150384183c0303003480404811140c0503041525141607280d1200100701c5401880c220505041d10346200900401c0080d4462001600700c0c41005011501e101c0c00003012a4010005040300c3c0f80c0c080d08540782890b00b03080054403007a42002980000f814070559000c240b80415240c0b0554810318440d0b24400c8191003000244049900304490030312051100052851185014041100407050361092040504003000240c82d0000c7c109102d1402c1031020080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 54025588 1250 54024338 54024343
    0x121b041206020315040e0f100c080c030603031b0102030106032304020f0a0f06020c0906010e31050403021f02130918050a030210050705030606070809011202041e0f0503 74
    0x400d5a0030200050b6262910100e82c0d80040c00782c903001350010306103280414280da0004405400f1039405054030501940c4d803001c4000d40e804041c000001030744c04004204413103491001142c02c13420081c100c9103009051078020800c901000214805654080700410509806028140310346440c0c408000d80404c42000c242c455240250001e03025a100e86981038403500c4140c0c03028003030710060881d0110b140e5130309402940c4d00403507000d05000b2807418002c62515401071444050101005000420300310340e10b82c1e0f20041c0001c00707404002c080f804c4580400c00321114402c41d40603078004d90141045d103d0250490440ca0342c0c40c040074501da4030420100006996080403101628103944011a8490b014001c00101c1d002414000d4004c0c01043d05020816400040409041c0c07001c2d4001d0041c0d59502e00140c0381c9010403503009411240809c40000010700c2500102740022050600c00038120b0441c80d00b1701260840e0b0482c07426030b1310340c4c202c28010007444840d0100521809190f400350608080100380c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 54026838 1250 54025588 54025619
    0xf0305040c060e03010902031002040504060b210901020405090711061f060309050f1b10050a0e04020c0f070602210304050c3606010e0f0d0209100506121b04 69
    0x100304100a0b0b0900d42d01d139002e403c03a1007480d0b00101143d4003203a2802c201c500a51113803240d00d220f03034a0070400040c1d001280003515075440e2070301000c81c03808080c0c100e485040c10700100341c1e00d41035500f00300c04181030f501e01c100640545200d0340c0d5180d5204001785000c1c0b1344070010700310815000d003031802d088003080c103900804160b03046480e000c01da003c114500986841c03005101050319001d1454001000340d1340c2a00038030302600480e06514014502d0a003030315a0b1107036040e9540001c45644041109007400d400a00905d80500101c1c0d5060240303c20043c00c000341500240e005800000030300046200e40e001c402c880031800c2440720301d1400c0a6441c190b69042c0b662081e40144c105c0901203000b00c1c41c1481d01a1514140909400d0000d44c082c0102e498480894101d4003042c0c80840d00009400d2000303030720ba5868009800c007010407036581c00300402450b00400440c0088203054012600f41c84100261044410306c11480c1c06030b040c100400d80e0011340301038a10210070340070300c020003840c0300110128 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 54028088 1250 54026838 54026849
    0xd050f09070b0d0e12030405010b0d05060606090a120b091606090909060b03030301030c0608160c06090503040515121605071b0b0a020d020606040219080a0b030d0f0f0305040c 77
    0x1030b5901e1442d00e80c0c0f006840311000f0b4600b28002c00c01002c081011841c01180300b903118100800c10250320350100042d410494001400a42c0031900149842c1815001022070080042100b00482d540c0c02c50801041072061003102e2255480082c01004081001000c1194100300c1041045a06244006003584001d1081c103646c0c80e120229001406510b40c4000d2030480f01800342ca6807580c4a0a124200e07640c0c42c8101c1e00040c01c01000900b4802240352886d55030542a070b50790784600915101c070005450516000d890b903020800000490b5a941002c1044110403140e04944440205149004803000244030091280d04c9441210700d0541c408104e4440d564055041d441031601900013a0304400d1302e42100351700403800288219226000540c560300b2204d281e084400c1642c8001c2030109a02818035400c1e1580204941e540000c3c0c040c900190f4000b90301c0030b00150455007900060719280300b0701060808100714090030040140d110f21509000800c5080034041420540d640074101d8103a4400d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 54029338 1250 54028088 54028109
    0xd020103050a02130e100b0f07030c020f0406090914120a26070306080c010309020f1c0b010b0c07170c0907050d060e01080115120201050a11010906020d050f0907 71
    0x4058000e0340d8107480030034071308a0352004500d80301c003403541d5203160941d1800c044c41503a100000c1c400554200310f403041d801028909040c51410341e0180c50002400f9005c1303138041d0300f08032a44025100d0744121030040565880200340685c050520002c11080419034072000c0c0c000000c0d5602c58500304085414440c1e031071400825840442c80711801c2d81182003c05094a1038507000c0c4004a58550403032410385d200141038550b0703441c1d0000190101d47d50f02a0083d00b01c2108910500b1a107005002081810061020901c04460503501d0740b0030040244c10200038000e0200d4505204a000c018040180103c1781410041000040e13159640d0007003c440c8030700c15075207032000928062051040c0d8448140d0100706002c0c0948034070704052103d4090240124541c40d0141c5084072400301041c46003100e013204809001d000a5400440e030a50146296100b0320003203960440d0742082c244101d5810a0280c03500680f507814410001096a001400520504590000f807281d0301030081031000c2220228040b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 54030588 1250 54029338 54029341
    0x2d0c17010608131403120a090c05100e0603180d050a0c0602160b10090506030307020a1815150e0a050f09042109080d020303040c18020d0c020102090406080601050d02010305 76
    0x400c0c4080403120314000b05020030007955213440480000c00742074840d00359051042e480d03503400381e0712048450380f4001800c02c1101c0c4e20104050b061001c00048040e44501d01501110040d9000c07510550065400300c0c08107070300c212040c250039400d10482e03c00841c280b82081c48c0c4041300b08014418a40600d01822a1341d00050064401a01400485c81d880d80700400c0383d035501d89456039840842d65441001201800c0c1030001c1c02e07600d80030088440040e80200900c040d5800c0611000c00c02c103e490f18011042d40d18103c20a02c0d6440f0341c1e801e001001c402441d04140d0081000081000074880c1b40207014050600080c030a55541d24901c1192960030b903441c01d0b9a58ad035082000e55014216891000d1415900f00f104c08140d00c840b5103400d4071054002c641c0c410148920882c0c1e207100403940035050310700502c018000c403020003194023a404c6c8082c0c1c0140c2040707015144041118840015400540e42c0002c12490078101070140c6030050103424046e000c2c030b61402c00400d00400b2600740003810550b0300c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 54031838 1250 54030588 54030601
    0x41b0207090c0c0215090a29030a0e0a150b01020109030c0b0601120f0e010b09040c1203050408160501020d0c08030c0d020f0705061801090c0b0c012d0c17010608 71
    0x3a10020f07041d00182940b6076071215804600750ba40c4070f1903039640504402c00300481c05602c0002030f01554111420491018800314009010a80001d070981e01e1403a1a2404074245c80360812107080030328011031882c0e00c1000ca0282c045e084421126559055905003074413507002c20b800c00708031151140c00416a15031503950900490b0100c3c28100d41c2100c0340c1c9428880c040004642e0311010007131840c07400130800b05160508004004030300710f400501c2d8800f205800c0c049040a0303150060120300c2030a01d0742c203264841c000d0a0501014010707082c8030510050b410441503904000c54419200603007480d00c0e5a200300c0c3c6645001c0d100061820030000e80000c1d050010011603030455a0b0200c20280140e00d0b80c02520300940c50700d50558035409140c100505000070000184203000d1082e900440300d41c1d80703d2a18250740301c80e40103a00ca41c0e903a5540c4800400721007c031502000c580100d28803c210244507d02044422a11071503145010814a50082c00d00a800c2d2041c55040d10b40703604140040e40e0f90078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 54033088 1250 54031838 54031847
    0x1002010f0c030608150c09220207030215070f0207031121100c05030c0702040b0f060c06040c0602030a02060604180503070507030c15050d0b01020115030302060105041b0207090c 78
    0x9400c9042498041d520344002d0303050344988103480342901620b00b480a0104c0107560210280c641c030000d03031400c00000310240b40101e2258043c4007514642e0b038020f40c00a204008980007008150090380101c00480c10355585055019403210307450400003085581060000d54030911400014840c1c031280c00e44501c0c41da5103542e4100c40c03400d040d10041e800d00012001030b07214400c0403c264002d500340791082002a000320250384c828000c4090242c00c040503a001c105c0a03110301c1c0e1a00340c02451b6040c40b04ca490303c640d002031000c6000d00c0c005102d103051500e405000815641c2c00002150001d00c0100d10142d8040b070550303001002224041890685600c00980d801e1030198014241d201c00940c1008211011070716a0031a4055054080803590b1034042500192070340c0f1000c000640100050404032086901803c2191010701c000907500303540f0503809051b052150020b4004d640010010080d07407415014503d407045250014005801081d10080d41c0e8003264002c1620341a117031501002c01a115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 54034338 1250 54033088 54033101
    0x2040b0a031a0613030b010501030501030503180409062301090506060d0917030405070603060501051312030306080f0f0c0402070b040f06020c030313120903030f050c010204090501080309120a0f02100201 89
    0x5116556a24007a9041901c407071381888100c078940f480d4400042c8640c007134032686048a40201c0554501166200981402082802d0499000340d40e42010404603405106107089862881d14101c04449201050b90314988140d00c4101514188810807200740c440742e0545610000100011891118510b0451f044007000540011901400b2041005004c4002152001c03030b101920108110743e04c0f000112101e1041c500428120103c141d81001510881504225858064600000e40640718600c080c201440e180400b020b41d4002d9000680c3d030607082c40404104841103c4c2145010701035600d01100141c003c002400540246180b6000c2c4001d940455064400400a4956925110064842d01c10340690140c85501d44d0214068000f80254400f00a03243c041e2a00c0320b00030702840040325164070060102405540130703c40003030740c0c0ca0305004075400303040e150000d1a10f5034842000d110703650f901001100501c2d400780c052203010a403003220b1030804903019201c11702e943c1840741c4207a007d00326 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 54035588 1250 54034338 54034391
    0x61e09080321010608010b070b090a020d111302040509060622060309030906020f1c0504080303040803012c16030b090f060301050a0605011b020307080a110a050402040b0a03 76
    0x60722425942c0e014401c01c142141d01c0108941c540d8132507008a0309990709010300c2000c450704010303840120318409500c50f44040520212420920607502140c806581040100c0318403042c50440f01700c074600340081d0010442d00020460074249840700003040c2d0f039805082c0500500000a24200d000250f00c0c0c44281692030070010450241e0742c69005008124904090740040c0c0f03450000315001d0710105030840304400d01d90003808102072003001041003072a00d43c400d00610404020001e0064400d10165100e90300501d80f940d100d40c9001c54600780d40c1e0f44150119007807039044202e0925a1840050260000c05c03124008401400d400c10943c01018100051036201071100700f04082c8100c2446024490902900240001d840300206003003079580f13502030580442c0d1280e02b800d80500743c4266100d01a070005003142c940700e40e94030703000d030400165100c1034950b028a08200011030402c5040311006040541d41146064500008083ca501504511074105621244083d40c50041d4000c107828004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 54036838 1250 54035588 54035593
    0xe0a29040c0501080c090108160e0307030602031b070305120406060909080c0c010810060507020307090c050703140307080f0910060b09010806030d0905090a0615110c0307061e0908 79
    0x3014207000550340550301c030301d41c0080c414000242d024000b150a0301c00395041030b180da11031034455001c5100b5449141c0e012204003d001d00009009603020001c0070000c50040f20016541d084c400c5010701e2079503100d46501284c0c102000040000395000c8104c8195521403940450075407a14034080001e0704003680b05130704031814030035800c0070301c80ca00006050121202007141c1e004083c02005460043c1c08484d0005003112080080020901940040c00d10f14802425500401c3d26803a401301100c2c41c11540030b0002c1c0022800d4020103070031400700820b01c2c414503149425460401e1000300800002460300341390700201d00c0401c0c5108420409031440104c1400c040c030540740c45540400040e040a0005030002d00c8260206156060100b484599a0044d03582c024100d818482070203584480501742c0701c2c0999444100090622104002515103045032780d58030801010a6000784c42c000d40450618440c0c1c00c9940308104407900222440405800340040100c1e08840000030340e80d40010754019001030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 54038088 1250 54036838 54036841
    0x30c030415060f0b0d18020306060409020409020306090601060909020c0304090f0902100203180406050303030103030806010908010507020c0406080d0f030c0912060501091404050604110406120606080d030e0a29 92
    0x2490b001000d80150402d202080142101b00b07041c5400b21858440069010781011700407680303504141d01304400300c9001070004180c000c81035011034540320b0201c0344005286c2180c0700601c84241d0203444003004080341c510940c00d01580350155622032080b4031480c2e00e070310341d20050140070b50402d400208000f50020421054420854006502ea42c0b007180e1030440d4846000522805140521548050300c3c0c0c05002541235a09507034040d113400b42d01410050606c5a00f40703001030b42260034091588074050301d6001c1c02e80102400c05000035502c480c2c00c078642d1070304074000841c030081c0d110203800c114038018640401d00a09181c0300343c5040429800c84030100e05100311042c28444075801450403078075000801c11402113400c0d11701c5407040c0c080e1801040754000c030012802194210003115040400144001075041d034402c4490000411030104440c40d41d00c0720030400c2604014070a80d141c49810b4142030000f0030140340440c4d1030b607402d100300404404041d01c1403040e510000f01d1441c019030071446013403a603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 54039338 1250 54038088 54038099
    0xb0111060a0e0601080a050604080a050c03040b0403060b01030e061302011101020a091d04020105040e0a1404110301050109060f0506030c090a06020a050f01020906120a0b19051203030c030415060f 86
    0x1914000724200340341d03c5501c0000032691000074021a0154001010f01000d80716641c8462203603200070000701c01c00c60140301c451000ca6051000b00002c0c4081a81d19aaa500d1440e1407001da070280301000c0d043c9803a14124001c01800440d2a907880000c58003a0044090301d840161104a100100f02490798404112800d106810070307008000c0d1006418110f164003102c03074a00b010407204840003800960188020080c6ca00240f00b03140e00502c40c0c00010452108010100329041403c40e02641c404040300001e02c031600b401e200341c41c00f40419070414041c0c03508188941580503454491240508400000240703242003020555021403402400c00c10f803241e69400081d0703a810400400d0ba06030059104882c244541417084880113980586118100b240080307170030f180725500401c104203e17611180c030b007500c43d501ca011841201d001c500c40080b440c1d0030314017400306142c040e25402841b0f074020020310020701280c005583e840b42d84804c0001100f401d0030b2440b000b40103280c0c005004100050700c0821f8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 54040588 1250 54039338 54039341
    0x60b030a050607090602060c0703050f07050309030105070c06150602060c090f03061303080f070806010c020d0629010903110d0201020712060515030d17060402090901090603060e030a020607030b0111060a 89
    0xc030f0320305d40d08942c4540c9580040341d61611640704004c021600030043d20808401520103001c81174001c40a0301e0404010390046400d489003151443c0010b1034070b0514000f0001c640c40307014485241424600811810901d01075640d080280c03500c03c906401143d0a48903650341c0744803500b14403002d411340c1c03084d080150640e42c070010620021000b00300c0345000243c07100480048207100d5130b41d640d40c15000d038071824010750300b45460081c02e0fa048860490080f0100d242030013056580b9190001c0d211080749070820044a1074100d202c22410080360f0003080011070110120340c2031040045a150341100102d100503890040703680e204050640c001c5a0740002d002450303006030321540c001c0c49a0f40035041c01008041d1601a031040d22804501109204455101a0842c00d60f000c440600014a000d01c40000204036034808d07440303232400540355081481040900e0142c51201c81d20b40300154180451100041d488241c010058000c0580d60709030040103a1081c0381d010301d99045002a2440c03070a2103200d400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 54041838 1250 54040588 54040607
    0xf0b0303040f05011b030e010c030c081602120a0b0420100f0f0807080718092a02070b030c0306010306030b07030207020f22330e0a0b0d060b030a050607 67
    0x80c0481d22103d05c510038101c0824014068941c55581c1c05c1c244044da000540f00c807041c0420943c00c05c81c0040040c0006610100144811100c070002030405040510410a04000180304c0d00400d412203403c1100249031821056080b0380e12900c02d809111440e561100715181d01c0407172590000c25032092101c91a0003c1c026003c031440c80d030b40d00380080034081058491200035075894002800c0000001c0d5118400c4030080c00070340032070305c407000500d5842421000b501d48507410100031403401d0034403007186000110228051644ca0000e841c29520f0801c180d4024000104521000c000001c0001d84503071090740454007555010002215900f080d41c2c00400942140000728001c0c7d0074107a13401c0c103a00e403401540d8076114444002c1605402d502c03122001800c1e10a4050030500d051464141000316070364021290f06240c510f0750000d8902d0499912000c16001d040d16a049291004000094407014929820b40e900440081240043c0101007031401040410280280c0500018804180e510030a900d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 54043088 1250 54041838 54041849
    0xc090303090b1206010305190501060f02070e012108090303070f0b06010c02090a0e1c020609151608040f0c03120e090c032a0c01020910030c02100f0b0303040f 70
    0x64001c0d0b88075a80703000c03948601000710142820300b07400503c55600c40e4029960200c00711003c481704461007981d00040d0790382a0441000b05441d14400b00645a04221420080c450b186054041c1c0d4501500300c4c0c10b225003594110008914103003c1c00c140400f08080324010400503085030783d261502d0074840d0848404900894103c40c0751070216a0a41c0b180d1142d160640c0c0003000c2c50340b2070322200a2030b00203050b00c00040460b405286035051060140102410301d140040d00074211514100c184607081011071907901c100e200ea1101413090b810000e202e1b010100c1860701302920070b5200c03408c00c00005110080000d201141c890780c0842008030f00d5680c05020744550312280141684001013043d00c440c1225080a104401d00000301c2d541707074100c61814460041080d00b08040008110f60606521101403000240c0d0001401d05190414034a11104854039242c10801c241c13840e0f0700251155800c072a00d056054442211111981c1581e101065040009044a90b100d9483e2006100d610403841031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 54044338 1250 54043088 54043097
    0x50a1701180605010201050603070504020322080904051008102c15060d0b04080307050702030307050106062d0e0a080a14010b010302070b010b0c100c020606130c02071a0d0c090303 79
    0x521540140501230060400801500304142400305110094000505011035081c0400700c0700210900c01e01c2c0302c421140941c0310599104502e00510050356009090124014006901006151008610703518092040003010402030a582c56a55128030001d80c0240044581c000310101010f000900c6201307804a201ca250351076440c001080962544580050308000701c86002074000b40b1030301c0042d980404141081e508105042d00401d1071341d00300820407075250b95143c5041c05019001484051501c041c0c0306000703071380303100d511880070407403d084149401c0c0802c015a610b1103548202c465000f6180f0b10302240c0d0022094100718140c0514000405421752078000305010552007402210307000c982000b0380c21580d034a4064981d6180d0701060b580d10300c502681307000c6d1041e00c07098000c621103610f80c2c3d4003e10f0203041c204d0402458000082c0c1807010f0500d4207800100281e00411501e08842e0720020341d6000300340c03469550f09984200b030004c030303c51480e1040c041101d82d0420140010389010303544 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 54045588 1250 54044338 54044351
    0xb01080606030709060b1e0c0304061701090908070311120d020d050115050403080706110301180b0306090705041802100206090609010e070b18040f1a03031603050a170118 75
    0x3440303400c0b105c82e030251024620040042c2407070402d00140b4100f11500100059180a60b4044058150703000b80d000140000e01d030f074200b4082048010007503401340a420108000703000541e80c03001054485c4440040c04e0201d4101c094403000310500c15080511404002d859584110a07030050080d8040e412140000c0d282800200d1070b820385c1d40341100c0f000095220340341b40c035041d41c4603800326401100c02142d0a5880c0c205107011381c40e00002550007840521002e40d000312020414005a411421040d8000d511402c101300d43d4001c0000c060040f94801c1d9000511118150380c0a421045540c5010b03402c5041031a10304100c0ba80000d10358801c404820560381d80391290310602e802e84000f840403043c664402c01051140300d00b140020242d1803030b1b030000a6010204140810b05444006503240ca43c0da55404808072a82c040d8130040340400c0080b0003552402d154600004c8403640c04102c050208000456181a914041e9501f4418041e645483c03856541e512042d801c0040690212500f40314285038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 54046838 1250 54045588 54045599
    0xb07020f010f0b03070501051c060803041404230901091403070c0f0308120601030209031605030606010e060f0d020c0303090c1302030708060d02010e04020a05070b01081f09030c0b010806060307 85
    0x420003883c0e0354003d000c0c002c07403441c00c0f00444107a046140c203e108040c1502d5256080c49a602c070702401001000301454032140703024424214001180c441600450400b403000304100300b012882030f061038030303100300c004a07803604030784a401801001d00043c03c41d0010003400c0e001207000005098130380c0c8240f619050098585101a00303500a9200c020100002800021606154030160643c0b18206143c010b052800c0a80047d140500b00c401d1040890c00b054002c1c4040e050a105160388400282850701043c000c0e00045540d43c451680941031640020803000c0c4210183d804460040707010000b180c3d16800d0180c00c0c242c48084294886105d200b070151440c000c0001d60095030322031480743d100c014280c4e580390180410007683c068100d040040303e10060a0b02d030384910180c511f40d61640d481a8440007940b5045624a0040e00250107e0b4010024160038070702ca0030000010300b4a244d0080380303130451442c0984d6201180c0000606010300d600000c1144180003d500340300740c004408881342950f444 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 54048088 1250 54046838 54046841
    0x1090f020907170a0c03090b0f0702010b010e280b0f03010905090118021e03030307030f181e1502030112021306050a050132040f080f0604020103180b07020f010f 71
    0x83c0e001e800c1c0ca04900054440313140355005020b00c075041d050209403041c203583d890007030840c126009105021038406000610750f09101382c0790a00002e007401032070040400c00003000410f90001c14040000c0345a4008841c8502c002001c00030170705000d910380c49a070003000d200141e800034064903992070300e0180001c2d002c0030305019240300d01150354200b9914003041e030207005802a0082c4c0318880842c004001c5619502d0400c001e510032a0035030b5001a0740300202441e030b415144070100490369442890044000326800358012031080c01001d104031a00c01d81c2d490007505c2c5050104d10380c410300d4404800082c0501d40c61702281c1c02c0034802c64211000d1000e100340c5804a5010b8000c2a801841c000004c0c0a954041c9500c42032010780f006002180c0718421058103420003d0f110001c104290201e0100081030030b038a07100700580401d81c050702001c021807142075035416008101904041c1c455401c040108215050050156048200d048185c60031a0010355655421403a00300c06d9071802100c514810100d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 54049338 1250 54048088 54048107
    0x7020a030f03060b0f07030c021e0a170d051c14040b01050603090d030c03021c0b010e01050717090406150305010e010f1d0403170f04120813022101090f020907 70
    0x44e614543c1c00c0500c0e05038051002e410009084003170180c20300700705000d655040308142c0300c046070b8030303004800c0502003040c0b102600560f031012801003d11201c42c501c0300c001180900480e54585407041e12002c0c00300482002c0082000003440c03851411646803640040d22551510a80c0502100f0245d80d80c2d82e000e2191030703c8102c03001409030b00244441c3c84114400d40050408203200d1801508260701c03030341078a00e55655885080486947d80c58402115600081155070080c02406c2c91424901d40c0d44500700f40c65080382e645040d00000090f44042a65658000700c00f400341c81d00d04080d050301038200a002081c00b8042d001d00c5017000c60000034449090070035881943d1a020140c0c814001750340119400a901034011002e0001d00c0350b143d0315211032091000e204c0c040900c8251030609003418548989041c444011082060321401c002c480c0c82d0519017011810307410303190070440301704206c7c103043c0c9006540c845090359420100c443c13090100780d80c08036040a00840c0c82c6462911440405c0e100c00d40b2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 54050588 1250 54049338 54049349
    0x403030b010f0e0405060f130209030f01140103030309080d050901020a09081204031509050a050a030e0301090209010e040201020a080f040f0906030309050d050106080307060203071106040503040513060b0307020a030f0306 97
    0x603c82201c140c10300302508507036040f20014001c0c80d2a04010070024252000c2001b501c0e45090340451014410b103810041003001c0705190000300554030b044504440182014040030f4149a1100c5c569000c000c2d018003100c1100d035a03980d007000541032145016010b980002500800580c0440c1b020810074004140c030002507844000c5140381c64650365401e441e45040060b210641c80d5201c02400104e40d0503c48809094880c102402458246d850080d22200d142c50840b8081d80c904168500148c4401441030b041d500c4154581d01c0540d16840104c0c5040c1d9040d000a1022030045201a14000100d0103002038400d0b4020f2100040c0d204c81031030007110075922010f00002e40c4140c0410045c10038001030000c4500030000031031840d4550550f24616408101c003181c03100c2e0300104204645500804e28142110598003800f001e050540b1401c1e940c0c001d5004042c86400c60041e2408e1169a81c0c1c088070003004107084040c0c030f070310780408069159a003200d000d81c04214110040c10380c203072082c030900b8150785 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 54051838 1250 54050588 54050597
    0x1020606130e030f0408030a0206010603020915071407030b060a0905040503030c0c070b04030c030b0f07090b090102101e051f0911070602180319080304020402300403030b010f 77
    0x21103140d2070002c0c0c0440c00145109000420071420300c07010310030081c00030301441001140d548040c20002032410b141640300700105071040c003442d0324135690624102d030b100c40c44100b00f9855980381e003003a410f95116014040314030710400b500041000480741c1c01600c00c21003154007005040d541c03010a01610070455006201d42c00c1000065a0413018502918441d035103482118452600d441484040345d0040e0030942d41003103410010400c004100c03003040d031300c103034a04482002030070f00b07801c00341015101c1d0181322082710f004500318140c0c1e4420801c9900c0300c100d0703030014414030b4940b0903048818080c50101c8000e080c1482e0000e408a480c06118400710050180c030b05649902c0c00c0000340060403c61020760b0244410403a4030007042150015103442c3d807074025540ba5400c0c1c1241010700e000c81c62000050b0703101c202180a00071031840010390f907005405850140e85c402c00080c9071001080328800c090000c01c0b03d00303c3c030030301c980070900080d100314403d880c02c1040c04640001562480d550307a0700318000a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 54053088 1250 54051838 54051859
    0x30207120c0305070e06031207051f0e01020a0914010903020102150408040312050d060501110d0509060705030301030b0a14010e04020d031e050705010b100c23010510080c01020606 79
    0x54001651449040e0702828004140c00c0c0c99954290406a40d03500c62120450703000140a65890144800d03082c400d4000d240d1890300790316070345050710ba61940c80c00481100b03e08003800b4100815800c0000401d0031030008558a5070f880030041c0a9001e41d01500c64160b0400f44000b2641d400b40701020192a016001030103611520040316110100091003114203200522001000441c90320302c2c10309400c0d032070b2901d548910120011004032805503005504122080c1101d091485000c100c401800b42c00345801541c410041b004501184903c610040c60307440008000010320100900300d90184141280a00c500442005c412840740402c2c0600700317031450414041030040c50800318801d1403034400d080040b0202070f24101d41c024442503216203000708100040b0301081140a101c2c0d05940c09048440c6a8001c2000b4402051644c2d45000103102203801501e240c00449100b4502a80c0300e0039000a005e00c0c500111a01a0003c4501c200e003a14071070442129600e600110b900d52190038040c0004007003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 54054338 1250 54053088 54053099
    0xc2805130f0e040f05030c0d03090209100f1406070210050405011107030503120901090b042109080a020111150717010501020604051218180103050601060f020c04090809060309010b0a0909030207 85
    0x88044072011605c61204003d200c1c0401c1060118007030702c001c5903c0c00070b03080300c05005001c02c9890080c050480096050b40920010250303020341c030180d40c607615010148016070350104081d44507802c0c000c0e501407021040725143c0e0b64010020400d8800c203070303603069020a25400711a602c0701c1c1c0b80001003c58009021615100702c00c1ca2095a000310f100340049a0840d058a800701d0f41042500c054603e003980300880e50503c03c501e104004042624030344041041d00d0054060307183d40300e148009040080c01d000010704008100229006c10f50300301d07402900ca08112a0203000c0e80c101201c14200204100000604c40d0300100d00a8483c6400c41c001e44050014030590961039409041c64604035101050200c400751100107001100b040c2d0b002541c411075055041207440d05405174044010000c508400c0341049501040184a40350252004103121700d10b072030706440078040c459126030007a50210400211038415001691040e9041da04642c200d03071114402e0f420f45020042c0600541d00c03c1d03104010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 54055588 1250 54054338 54054353
    0x6070b01030b1302090420180f060102070e18120301050d0f0503250c09050403020a060c0302040902030705130807050a0b0306120f10230c2805130f0e04 67
    0x5014110943c250410403940c2d00003000c0c6801610309a4580c42c10350b2000c410440c0140c41e404200d035003120786176800b66040e0030151401c1001403480030003000c500d011403503d034005c1146002a1807091060482031a0028000742002c1c0008210710340ea11482d10030314050445041102e041e81d00141011540c1d00464892000900505c0011030700c61008100160507403a00b04001c0c0341c68043c50191299101141c104003040501c2d540044608525040031700002907000603d0382c00d0755501810100d0303498a0080c0a400a0050b5806420070300d000004218002d68003800400c42540c070100010802c50300da04074655a85100d0142617000842901c00b84040311108000d580d020f10b001341000d40b8032410701700140c04e00da605514551958010010458981c1c094014461800344050300f180c05815015840b0f49a1540034295080e004000148008100313000c00c034014102c42200d0081004429800d0010111b81c0804030058040d81b9100c0040380d03103005441d44508031030f800000040b03d80c0300c40d02c42c1c08 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 54056838 1250 54055588 54055591
    0xf0105150d0203070e040f0b121507120b09010b0a08090d090b070609060609050402130b031507030e0d020714090c0a03020a0c0b1e01080316110102070504021b010b06070b01030b 78
    0x20b00340460a41c0300752960380d0b14080d2541f9042a00c8001c608000b03840140103070a43c0e002c4840c80d4039080700b11041500c18112485552181c0e0b1441c000c02030340800c070209401049042d00c029045101e0500204031446100000e20440c40c040e40d50314101d6860b62281522011003c0310361001603c0d101c0c04100c0f8400032405808200d0240d680040c242e10389a48207000c0300c001d5400a560b85480d4400c01044d0700d09501a041c081440408c140045880070317001a45a0240d490004c010391000c07030229003250300c02d510240c0c00c00c2075842122042c0030f400b0f13000fa50320907aa10599404e1040080004e160381018088240036002100c0640c3c00c0c01000842030b8040e401c00b0360010704110040788032101140b01072041c0c0d40180200d90028404507505d1040884950050700701c04601d9004100136015040d039118030b110901e8001c4c00c1504d1603e035000c0100c1c100015503220a40c001c0c00030815104140322207180d9052242c3c920020449241190305000f047c1c02022400b03452030360369030010000f2800c5004d000703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 54058088 1250 54056838 54056851
    0x3090a0b0901020d020d060311190504050a020705240901060308040306020f0c0a060b1305040f02040f0f1e0c020d0804080307020a080403030203070b1f0b0c15010e0f0105150d0203 79
    0x58207040c13003110b80380202d80103034548000ea039488000400906c500080b00040d1541d0540d00d000e40c07003607007510550600195100e03560245503a00009800511103a044d1211175620000342d807000040e441e00e051640200d4000003203039441c0c3c10041a00240305116030360440e0b40c0300d00224100352940e141c42e0000c1d00134405540032084100070b1a0908001400b07290484c030310406c030005000220100f4801c00140013034071382011501c1d00d02840003240252007400055a4101c8010980c0741e00411b000d400741907060b000c6810b1504000d4981d4000c0c03001207a0b0030b040419000200081c407241201241e4402000145201050b4a42c3c049004078403144021a8404031500484040b0507140d40ea00600d60700030350054005805c04940720040090410328140c101d80c502c0c4070800c4200c100c0c2a107607604441840f079069001c2c00091007a980c0001808010040600d00c0740320f200350743e500c03201440c80310800c98810b00900c10550000c24940b8000300440e0f4800d200312a00c60500b014964128001d50010301003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 54059338 1250 54058088 54058091
    0x203100906300606080a030306090209090112020f090a0209040e010b0919110301170d08100b0c1501080106030506070203070305030106081312050d1503110904030504080706050301060f0503090a0b0901 88
    0x910700483c40c03502845004000d05801420b92205500380102100c2054100c00c80c2d80c1d0040044501558030301c8030303450540d4085c1158071046c82c6948000f80c03071903820450f802c2c0c20100c42800c02c41a401654041c1078600003d407414007a403100c89070000c0c221290702c030800790f01c00c030000082850004600541e900500764444000340800c0038180440c01c4e030300268030099040d8002d0302e2180901005002c0381c123440d98030b03082000e80c50401c80303c81c070741005040c05140702181004c503481083c04402c00c40c011001c810808607581c0795844210b07480c00390901d070106840610446010440d103074400130842c2d41c40e43d010f43e1810f04507403c2c080c04440045025121000c55071f4a02c40c80c0001c80d000d81940d1200c15459242e4680d583e0040c076004081c0d45e40034404620170b40c5031640800201e5480202d04400700801c481d1361500340c1d118034050b1054040c075041405588074102d0042a80c07500325000310305030f8403251a40e1100341084202210144001c448019541d0800619070700018160030722280c002100c07400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 54060588 1250 54059338 54059429
    0x2060c04120f08070f23060a0c090e04120207081501030f06060302060d0b03010b0a081f020c0d0c060b040b031905190c0e010605071a09120304060203100906 69
    0x1da04103c0c0c0c0000304140d5003c6005181d15040284029452084444c01d02407180314601380e1a900f521810000c12240c10b040c0c407442280780d80c91049140d1400341c020020a08001c1c01e041c00c103c0003120540c0e1001000d44500e200224841000140c000083c6036a103408000a0f0309654500340046c1380d002c411030718503440c0c0001000581d1a80c0191070000d004500004110384580d08050a40d07042015890140b01c0e0038200703218800c00440c0e0300b244094040002c074140c24184010070000d01c6983e1900b400c50048da103850a8980d030028019032082e002c3c603024410100001c0820084403c4a0b049070381c581d10400380406200c03540e51200d181c00e0b0003041510003840d501003402080f0105020210789260107880148886003100d041d2074003501d0189855410100242e451110714600c0c8a82040e22117040310000c0c0c2600c030100001d20710144414100b507180e08107460608040e420941d2131002004c184100400d0000003032042e041100c0403084500001c49003a01121221b1035032001c0c1c070f0b40c401480b04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 54061838 1250 54060588 54060593
    0x9040207060209040606050a1205091612110405011d0405071703070b090a0f020d050715050a030b010c032a0f05210a020c090604020c06012402060c04120f 68
    0x40504036040c0101c0016a480740c1c000304000445005070003000500609104510030030354813010b030307000c0c0b28001034000178251106400d49240403162001b44810200c80355001c1420350f11100c038036500178400c0c0001100c03411203000700015503a00340110850f0f2409903035000e5a01c1f010408550300280100141c403181034498118440d41113440706900c045901c0081c2c420200006041c603240d120b0940d001030f00c12100c05a440b02070012003000003a210b060300203203036070038050180080d400614601002c000c0ca04100344019007150070001e6044040f91800744102641d50155410200d65030341a07850104000344080c4024600c20109461b5039a061204a4440024002d540c08076503180100700070f01c513038154aa00d001030070310301500410b02c0110a124400d03001c0e400041c0390504036011505a1400d07511500810001d02800d41e510000b07110310b80002868210ac0844044906c00c0d84011048500c3d42c11016a6529001e82d014640400308000800c603c0d0541104158a1071113481d80f002c803000b094 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 54063088 1250 54061838 54061841
    0x102030703031a0a08390409140105070906091409010303080a0207020303070807020405060a08030f0a050706050703090c060302040e0c1608120f010e0423011811030f0309060a140904 80
    0x5e80240c041c680c000c0012600f0038a01c0e90514042018800b03400902c249031500402c07190b1281141117006588840c0904100014034011402c0307000014002c009500e0000e400400019452142d800843c01075800800d05040c1d2000c0030030340072000f4181344c0080c0d20396035040b5590440142099150342c3c0c00e01c88100140c1d810300c01000b500d40035004c3c4544800c3d55004110445a020f895a4030a01c13840e07104008685003c03066410811142c0ea1040d21100c1c030380000d488520400400800307241c0382c0410002d649404d940f0103c2140c0c002d074168031015031205001e50485c41280900341c10710500000140242080708000e060348610b07481802d24048903070380e0b802426042982103c0c1ca0b084003004003c002103003002c819004102c4140b0040721410940c0f110000c144030245550709030007042008019201003500010000404004003084504003428000c8551006001c2c0c1442030103501f04103942800c000095542c9400001c1c5054641580528252017181110701602d140c04001e101c10a220f030f4a9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 54064338 1250 54063088 54063109
    0x21090b0c0109050d0306060c0f1104090f1a130b1905090618030a05030103020603060a080708150c0306010206130f05010606030204051f02030d1802031b01090e0103020102030703031a 80
    0xc000046a101c0040c5001e90411034400496003c15240100410420394481e0510641680200454000d06081d0900d01140c2464403421a001810038000714200118450844540e41c055021a81240d014074420113900409640c0c108002d112005200c0224040c4040e0680001140f5030400021400303054010644d00c0459510009030410010001c0714540e4a03011500001280083c1d45444076112000e4a103000601010f03000f0040440003808540b03038100744c00c1c0a0094a011180348507994500740b0740e20b041c2131401c420034040e9500171034050300d03805040da0300502c01600908002d030344501000d4072500d8042000d0741c4455100d115400440c40a110700c0300a4075040e82d000d43d40f0341c141403c0c0079000f040c1c1103117550360301c03424548400d041c1d5020041c2c3c1e95601d844440401c0c4c0149484508803130504458029500d800741c203501d401c50309400d00040300744040c2a2214501c007583c40d820340e140d560091002a015030000c000e903c000031f01c20b502c0030000441000300510184c0000003c5110040b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 54065588 1250 54064338 54064357
    0x31002070507060503060604170c04140a0b011b080f0d02030a14010506280302070c0b0301030605060909100506120d2003040b040b180d0602040f0605040321090b 71
    0x14000352540034400705018940203040030742091451810001d01050742446548210316503405e10700f5900005581c2401385d2045030308010024003070400d0603074012200c00b03401d8800d1071000c1d1170b003a0840402d50250300b1030b01c1318101001509541901546421190b940105c01e4403c1005040000c150088494405580540c00c00080006d5016103003800301c21000c0184c1040d40b0400c400c1c00417103010b1040e814001c001c9006800d0008801140724020f40c00303802030341e0005002e5501c6503004074510030f40c074001d0750480380038040903c800e1316008140200003805444000a603086501d4180a82d11a42c001641103540030300710402103040c81b0300281c104030128903e03c00150381c00c1083d861801034096610360310240032000c1c0d481c091500c07100e0485071165211700244c0c040d02041d2129480c000d03100c002c9140c00043c01c2d4246038592854410000d61050003030140400783c021010418a12035002e550a41c1d41c4602da250900c11880c0203007414020480da9502000b40310031012500400c075030003801d103110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 54066838 1250 54065588 54065591
    0x9050709030c080c090a020708090f03070b070602090901090905030f09060714010c0305060102010b010c151d0d0210061401030b0f031009060501140904260304030e090901110f0f04050310 82
    0xc1503000304442145c01422140080307005200700c1000c2005e410072a41e1030803044900c8940c01e031160020909180c09035000603588840031a030071044c0035040d00140030940040380c19030310300ea8031068a007081710b1a2180c083c015034414002401c0d240080d500601d001c400c01446039040200701da0311400110080c20059065075114101e14015030380500405421007400d00003800401c0152000030580380b180ba4000d00030740c41180e0341c016509265030049105408420480c0704010420030200c1da15082c0400c2440140b240540c990f0000f00a40b041c5829501b056403001004901040118040d00c410b0503000d038060031485001c0190707541000010802c0c4941030000c22007945c50f050240032208168840d030940d0101b103210845550b43c801c1f403994440d50044107c0ca5062420540c40e1f5400380c0040005006d6100206010901d038026502c00d20b203000480e2000129510600d10a00341c90481c52181d5164600340900c80351a04604082c02d4601e00a2001c20300306581c07140020301d4444568080141c66 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 54068088 1250 54066838 54066853
    0x309010605131a0103110307050a12051501020d020a0c050405060f040c030510120209070c051005040813060e030a140a02040504080705070e13020607030905090405060a0b0409030909050709030c08 86
    0x2243c002c9040381e07440d4401d00b803c1282003e0b58a400c19248030003800b800400c2800a1040b0b07445000d051441c2446c48000000c110b0f82c0340030b0340e04010006191907101e0151152841c0456043d100281c10054194411524100b0b145044180b102400c8098681035004841003006201074036144124400503070b584e90b01140c00c2c00c2100300031416500f0354000011200c0ca8030000c00140e00c9003030380c59810050f2482e107100982c8840c2050390074820f0356106020020704040a005c01c4c80090b4000d8a1039083c00640301c500b8540c0e40805940c84070f100c81100350180c010820080216404040c0940005c08190075900030000c550300203411148100c6046601c40400700e11201401810840340717003e4a45c4660030b10290600c0034030713890305140500c0000e100d0cc01c0050000c0030140b144860000408016005c5d44450800345425a1035007412a4941d02c028039019403180180780c24012030031042d0b0192150710401e03090a000f2005400c0c020101707010b024005c80c0000000b81d60404010040c03072200040c008d035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 54069338 1250 54068088 54068111
    0x3030a03060e090d0c0f0807020604091406100f0e0406090e10060506040f0b030a020d0c030b120601140915030a030c0c060c080d05040c0306050903070302010b120303010308030901060513 82
    0x2c5007014000700900c1d841002c1e064803050700041700250803030b00008000c40c2e0203864070700f110b09440390307020080d003205001c10001844401030300311000402400804070b0030396907802c0904c00d01c10141150301300000c02c0c80079400d85860003010503001c3e510000d48003042990b1652a1241940c240002c800301a42c03045060034a500c416115406c05041d049036010319141c0b50081d2042c0c4298107010f250400200003011800080f5154119a80000b801b6024841201012806402008507011203409085a44450029858081a190705039000d0b9000d0300c03500030a09080c03060405009200c41c042c181c403040780b03210343e175420404105c2107442a55800300004803443c014018540315030000b000e10002d441d12400041882080c1d4080c00302603913001a031656103042056a2000a61010300080e00e04424450301e114088000c0400c1c0e0b000c2e4000b0300500300c1a03014040c2c0b80c8401c0e4460000c6410900040c400a0f0364a402103820415580001c10b0b495102d20000300050341d480540004a951408000764 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 54070588 1250 54069338 54069359
    0x306040b0619180305030a1101060320011e1d040f090c031202030a0504060c051f021b0307020f240c07030b0f10090c03091502070614130303090f0203030a0306 70
    0x1a441d0314415441465861545c4a40d60f0f8080c1078900f005001d514500e440c50344500f5071041004503007100094440e0516004a094282c41c991500c41c000b40720084000c030301e500b07101c18000710310006542e445000601003039051409410000b51640c4642c03610b1010030b418030507025440449005605420340030340396252030040b0380000b486240541d001802441880d60300a4241d03801c65203103007000c00d514070b0145041801c1101c16401d0300303c15260000290b01c4d60b1001c0d40030303080713030300f00c0302c042500043c0e40140050b500d0099007002540003210800800e65814241807200e1101800003440505074040000b605054001a080014039400180c040003882804810300e6001001d480340f8000380d04082c05100b003003407030900840c59810b860f13605140700148030380c0c4a42601c41e08551070291800e181c01e030b20b101a40c05180203840060401c2c880514551000041502840015081940010455400307401401d41d040301070f40c00112004030702001d610301380011304840b40195000030306a42440000c11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 54071838 1250 54070588 54070607
    0x50108060306040b0606090604090c0e040e0f0606040b180112030206061002030304030315080d0c0b0105040b010c110301200306090c0306181005030a0302030c01061d0a020306040b0619 81
    0xd01c00d51084040c403001c1000b6150345a08440141c580700da07681c070321401094143c0304a074005884280740065082803183d000d81c0300207544200312400c0c41400c81c10f1a0300e40c0ea070043c0548074645a0030880c08030302589001d620010041c030700a800803d09140107440500c0300c5109078060005190340c0c41950003010f84c14030006901c407c0c21900080f400054410003503407400000d20043c18103035540f006100264004641d2001001d42c101110000c2909000083c441d0520345400c89998410200101c1e06143c14082c00e40740d150306968a5000280588131b103912030b000310858030703015540e070b0b2218003100320346000e000902c2031a21a07256903818440188088407100805500d981e84062040c4142548c0d14400c801c0c100c9400078034150f40e500c41007102c8032800e000ba4403007580751107803164070720030550088081d181804003d0020000990f890700c3e00401140000b0800841314042000111104020f602554000e00090000120101d459001c104180e00c501c01600032060742c61888440c881e80810184c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 54073088 1250 54071838 54071851
    0x160303060f321e030f0616140d09060501030203100608190501060e0a06150801050315070203070b0a020301051203090d0303050405120a03060e0a09030c17041707050108 74
    0x1862601e2a0040700b103030540100d00040c000d11110b10448008403101c50604070280e000600d4003000b8040350032450741c82c80083e81894042d0080c22514800990045000352140c40c140c4804212038407070080c200d4140c1c0c03080ca040c00c2d080800b0720884403c20950302c44c49803a1031181c88001546e50440c010149041c4441400b0440c5a0074001e0500c40f0746804511424820b00440000b28a040701d8079155016104581040d5101035142c4100203400b1240e8204508071440ca80003040005007000b000c0358011002d000c1c65400d40c1c460500043c101d611565000c0e844401407041c0c07820284180c0e54448860402d664000a1940110040c0f008d46851051482d010003c03900840ca0070f40710202003110310000c40b101809044d0344400090603c2024052018103004411295955032000980a0010017481c00340501c800c1110000650300c03481ca100b40080e003601902d500f0624042c680e01e200100942c0b40c04881494801c0c0000201d03000c0c280311a030098002a001b40a2207410840014111940109032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 54074338 1250 54073088 54073109
    0x1080d0e0603061302031009090b2205030f07140f0705040c05180405060607080d060905060f031c03060506121b03010b1605031c0507080f01080d03020705011116030306 74
    0x14000f541c0d5441c103001c0200001c60001603280d41e5200c00281d03240d285d40c2d200b00382e25400d20010804100400c1e5110b07210b000710704a800441682c078810900e00c03180303542005040e68010400040d401d40404040c00c00c0d1031042c107048686110001c141802c01104040048081e40908400d1100f450240500860300000e85002d90402864440c0a5511219605d823540560f80d03034004640301c1c2e264001102c543d00e80101c0070544d12044d0f0360901e07008110074800e6881040c6000d0124100d032030444002c1c083d149008006118008628001054060760038070102d0501d81d881400140c141c0b1868080e048030820032106510314030b4030711003940e610b0303220840c90600744408000520110841ca401c1d00e0449400345035003031b44080d0ba8a459850340c40b8082d40044110700c00541201d220300c00d41c0000d80f00d44802d51740c1a181e521428150442400b0038007445100760401c1c0c03039000500d84280e01501105008100202d03080b1209041828140d014401c684c513583c03401c100000070f254250140e8001022400c0302e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 54075588 1250 54074338 54074341
    0x206070201050106081005040905070306060e010311031203180a12200a050304030326010906080f0105061003230103060b031c02030405040203060d05010608030a110307050d1b050601080d0e0603 85
    0x7110a00806e02c0c06224030841d51080114107100342003000c40b001e180c2c80303001080500d44038107198074681001d100407188040032499070070705400c0108400050908000c070b00d03425500e0740c10384500300740f5000c4200002c5109000e028404650301c40c0440703240001903160200c002009036801b82c074805004c00c04403031a5102c07100307030800644000100c408480d01850401e520400101d01200300d11000c90720200072250400010444145070b51003841102c2040080f240d43c01c000c0f005281c2601e1081f509107038408070075610004243d002c0d400a0541394401c10000c1c40d0100503c3c03102840ca0030a80094880907a10025021541404c00042000b1101001da5100004a0300e10080d81d0f403050f800740340d0043e5000701c049006510b0700452105010381c401e0080c40580e8071114030700c2e07483e00462086400100c4c0e10600c000d0040c0c001c0101c0340d000d600280a04500003c80d5010b403030a000c40141301480c01c00341510700e40810820700c42d10f80079007030044c0a0a030f00c15040fa001440000b2601590344116000c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 54076838 1250 54075588 54075601
    0x90c031b0111070f08101a011202090d0203150f010602370501090b060a0b0f04050d0320150c0c0c010f030216080310080c0108010b03040503040f06020607020105010608 74
    0x30064428480e092810ba400c01c1c0ea801c507060700740900740c1c0c0700c401c01c0c2c06000c00106820f900451551340d24001c129003080307458204041d590308045203584107070200e4240c03d02a840202c0d160000c3c40a83c0000e86040c0c8480160b901092401c0419024061182c0b4044180440c00c030210b00180c0c01011a0f10051034102c03c042d030705440b03510140c081d458440340003400a44036013070002800c0d07030b1740b40e0004000c00c4682c00d5400c2041d0075007401c90710140b00740e000900c0460403070580c0040d81c050600c0a03600c18280340c206070501501160318841074080c02007950380009085116200b0b0014401e109001c0c011280c5030222501500c1d001420240781e4000503c442c1200b60000a0f510000300d009183c00b041d03401c85d504066009209402d50394410b5184800180d05021803a0025401286800036004849aa0716246a02c810005044a000030b02510041000e998850701854001e8085c3c019a450159141c10200300d1f05c85c0c40e48005c0150300b00c1c00410103055020700c0b0b080d0042500d0f082c0968a0318104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 54078088 1250 54076838 54076873
    0x102070803071a1003081804060b0f070c0b043f0c03060b04020319180503030907050a17030a120f02030a050402010f03050906160c120203071209030302071205030c01050f090c03 78
    0xb00c00d6025420314030186502d1f6503225003001008180c1c001403070b551032004100951342a03015110030703034802d810003000140100401c4200c608036044e42e642184440616210949000b0744440d1f0404408031075a84184101c102c078000552103481400e60030045031440ca05082529018042c05101d2481031042100b0a40c00d07034058150441da444d000524003c00300714280c007030380d0710f4440a0704c00e21020040204a1034000344a000380d03102200c045078000d07610203541c810031a101a540f50795800a1042c0c144140c000c044003221160460702c0400d100703000d105100102e8004407408080e00382c807034040c0000d550f0807401e05e08490045107018420b40c9081d403030082da0f40801a081c4500ca080340300ca00d02d0000d200e103407000c1015a000301c01c0c0021043c4094001d5507500200d4064941c1c40b28610040d0f2561302900d081d600b00d940c55000fa140d032a1515413074001d06682900b0035070381d901040006c0044406c00b031160a01c240444a0b001300b1604002010b1407404c00050301007406a44400c00e50340056482c07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 54079338 1250 54078088 54078097
    0x3010b0d020304080c0a060b0a051914060c0f010506010e0603060906010e0f0d1208011d0a02030601030e10060609051503010902030603010207020a12020414070c030e0102070803071a100308 83
    0x1925030150303680d203841c078040d001c03880342912007200d601802160a04106403508030301d560401c1141c0c01d404264417102080040e03d203a000c4038008c40000c08040000d0041e810034200001030060086040191b07845e2701c0b0341003010441c0103182c165551400c100040d80c0000181421060580f039150851801101240220102401d500e041c03255802107806580d48050860a0115000e42200a03200d0546000700c00314818042001c0814801800071482d41e000c0541480700c050060700200c01902c480200e10020f5201901072410581c5491031910440030030400c242c0c03001e5079054001401e514144000b0140c4000d0b41045100b88140840c22820004540540341540c4040b0801a92929072a00083c0244200384000b0741004200400188a056400380b07129030034020748043c0446000342030b03880401182160f4440100d8010340700d66001ca48501c040c07250788441801140c40740c945402d442441c5800004040b5100040849a0701d051400c9000740c80d001880f0f20250403005040d603881c035005018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 54080588 1250 54079338 54079357
    0x1120312180b100b070602030405010b03030705030d0902010c08040b09030c03071203030f061706010627152d020c0402160206030a06090606030b030606090103050601060c140105100e0108010203010b 87
    0xd208046214407182e50041001130004260b0b45980b00c40a18210010350421141522107510b082e01c1c40105060200483e81c1040c2d008000d94035010340102518010801d1300020380c10440908080700004140b9001000680310360034086864140304d00c1010300d44401c907078a182c081d4010078010003824405280303000e215a410308020a1100d001088500200110360040a03c1c2c0d00300d00d04452a03010200d0007905907000d40d900d00c04045010703a10340320000d894000e000e08080200300c00300700d030045110070195200c22616000250b10380c060302040120440303281005400b1211229487c00c150100030140c9010710907213003035040c103906088030b03809141a040c019004420020018501c060b265001401500f050001007100b20b071984002002058428100d41c001e20070040480c980c1d2900140c0740b41241c4d0700200601c400d07030911a0441d00d20b250407400312451043c5400502ca000000e000302c2e0b20400100c0c07a40600c152070560f402100b00c6040e880100940d01c108010b20110700b80d03d048034040318 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 54081838 1250 54080588 54080603
    0xf030a0f0b150a2001090605010f0b03090c1002010902100f0906021506040504031101020313060b09040b07031104050a080d1e022107020603041109070e061b0f060112031218 76
    0x205540d6a44101c00c2c040e108004d800d5203010034100c100500c5074010703416601540c000110705521403a6000040c881500e4052030340d0300180500410303103055203950a5080c0305200106150990740d01240d102e0b002d030020700700443c0007400160109035200d00d1502c018203451000713141c3d00d00020035414142002410860055407a500010141030149a01126015044008560304d20717200c004120101010b0104075401400c00c00e41c0e0405103010b481003402103410003581c410f00d07102e4031000e80041103081c0d100e0f070302ca00003800001455921307000d00c000103000402c040c0c002c3c0e220b02440103144a0107058041c2c903045c6007462400b003c1c3c1d80041c00c140c135003002c416441c2d4504100714401689004104000f584404000700304410442c1c0c0c108500300d5600f0956081803251501c0f0310584165815085ca550059001d0120f05400c0c9010141107003601d10782410368408000080d009800c102c426000507604550805500d400c050380542c55400201d1011000c00c4010780d0120700b18200c601c003aa0180044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 54083088 1250 54081838 54081857
    0x4020604120f0b061009052b0501020408070504090809130b04020f0403060c02030406080705030402010c1707020f01020706020c090a060e07020d090501090605092215050910050a17030f030a0f0b150a 87
    0x10075042380c0b481c0d8501c15842071043c5601c064035001c1c2c080c0d482805007107a5405020030004503800c00d4059902215071100740c4500b095020018400d030506041584112030f502d40c610b011940c4c803684003e1400b0512003d242d6034680c21820580165455080604115481000f0030030400340c3c0411455008805460401e0340d80c0c48900040792840540340c0e0241c200c240440900c3e042c00c5488001782800340c82901d480f00640c0c8254016611600c1d0b40c821180942c0050910488502d450700c07400307500a060020000d0203a448034000c128800c1d00b150b410001da4000c8a06100340794220200c180202001d00c1d01174826810010014180d0040c0b0b89154007030000450044605a234031060f4121029401070104414042e40340800c0c0100c3c82032240314050029440407d10103080c10300d2035420380c0c00c0a400130b003001d40f52031401c20550104400c40c001c240800d0050505100103000294000e04820700f001c83c00840b00e01411044441d011503540c800c4030300c560351014100124041d03c00c00710315400d004484d0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 54084338 1250 54083088 54083119
    0x60303090d0809090703051501210b041e09020a0902030402060403060b03010e0109230609061501180303031a040b010c03120e0304030c030b090d09030b04020604120f0b06100905 78
    0x6010721802c03994002000010000710344e40c1035102c903204040c0c4900030604420010015103a6601d2440e210ae400703c05030f0007610a044541c3c001c01c0c040d5801403c0000c0c0d01c00750b007040c1082c1000c16144c4900540d1a0b40103402507160806030790010342a82c840c11441e40c105a40090f510f4822031100030304440c2c84000c1c0750100c2d80e00b9800184c10424010080c40070424901d80f82040c03205032a0420380d00090a0003594003000d00041241c0300d6184200240f1440d1980940600e1440c000c4c5015030410a902144480c5040b0303120724440250310030b85011403121071408002a528018500c1c0034091403070049054410b80c1e004030042901605401d02484032009907000d000a030800c030442403034030701c0001000000c0041c021444022640940444c07845501c821640c0384e02d0340f800110000009140e03480c144085545031052541180c07005003841d01e81690b9407224000c0ca100140d0686c1c00b9007009080d0014030141b208039551082086810444490000d030f005807202c5028050240a01540c0344440803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 54085588 1250 54084338 54084353
    0x2070e010504180b04030201090b100e010e1f0e0709120203150a060f0303050712031424040501030303020705070b040521030417060103050c03030301050d030e01030f020f04031109060303090d 84
    0x109034025007400c41c4c0c3d107803a0402038081c12218100700d03010700800c00000c03420702c0070007100401c1c0c40c440e407001075090340707410b04003610707904080c00c0b40b0007061050007180e400031001c0b0096002480c413070244048a02d010031028000c1a119801400e00c60030b8144814010390780450269044110007480e602c89481d00c806002c0101a69000031007440c0c810000801810740103030140182a20685c603804c12282e003842d04405603509205501d08640580007c6a101c1c00c00728404140c100720315a00061a00241c0005801d6a4080e0302c1940465400608401031004c00c0c00300d04007400b00280b00b58501032600c408910050402a6204c000500980315031013000d8040c41168010152802840404103620288070b40301d00742803004030307070b07511a00b160103519040c0482540d0413100003c060103010002510f0980b8500c6000e030646041594070509001e094040d172000d01252000840d0b9543c5030350452910f80c1028440b0092180305146034401c100190350004100c400745031043e112004070840610b003101303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 54086838 1250 54085588 54085631
    0xf0a030504060b091306060f060e0d1e120809010b09070c02060702040f02091807050d0515090702060711070807050607080403060207121d21100905030406090602070e010504 76
    0x41d802181c44003400b0903905c0300740040c000c043c0994410400d4942d68000500494000d01ca59800b1882c02000242c042c0b034000d20b40755140780181c1e00d550041c4104160401c1007010402c0880d040c2558075150031201ea4003044a0b40d100482c51300030810394884c0c05c006048024001c00c14420400074030f00900031500ca15050b591041e50141052060824030b44101000c0e40041792120301440001351229081d1605040150140706640c840900d00540310000744050000204465020002c030f200d0044951202c4071454030170402640500802d0601d060000c1c1840c0c03109080328000d504c42031051000751030202d603e00440d08102c031002c0d0f441455140900140c06541d1000c0c2c400c030702c0840d115003440340e0460943c4a90107140d89140d84800c109040d22003451045420681102e01c01c0a00000c00c0c4854802140e5511408201d6000803030101c805010307a880c12030308031544e07000410100f120710b412240820180c039080c0094000e06040c5280250800710501c607462066444240410711200e4909280f03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 54088088 1250 54086838 54086861
    0xc0609040f0e0606040b0105030403050a0c02120d020a11010905060409050403030623010e061606050402030709020711090c030f0703020306010504150c0b0f060604090b03010e0601060f090501050f0a03050406 91
    0x2403109030700322886183c440c90220350443c041c0341441c8402002e98030602c100da118643c0740e00c0d09414010340800c1160150340e6610200d822054503540001e80709000c2206241054180d40113188070032051401c400e01c4810351800e9814406091028803c50f52000117441c02e4642c200700016581c4d41d11700b4100c001d0609548400c1000c40c0003000040c55242c0c5550800c016003080e241d01c100c90700d1402c03c1c00300d18410050b03d5640300380d018034110b000401e203410094201c0d000402f00c0d02403585901960040307034428081207901d15140f264440701c5060050b0056440500140130318150b150a1880001c5030100520040801d0b60000001c1c07401d81c040c00c1aa03010f01040160151052103c0e68013529018456005540d401c0e41803002a16841c84990355521500000c0c00b45401c01380f902a40e0301c007a00b0f106104c02c1c0e26548402007000801c1c010010300d8020010b03591604641228548040c06000142c0c010f01d040001c10005505080d014004540c0c1c0000249000201039803141089030003041c104080b03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 54089338 1250 54088088 54088091
    0x305090307060e06040302150f040602340506010506040e0403200607050301090f09050c01050a020a0f061d030304050721020405010807061b0b1308040807030b0103120509030c0609040f 81
    0x3a00f002a00103000d034401c0c1d1080e000c8401d0418901d00303481130400d04642d200e248011200001d40029482d07005400007407105d1702d00c0d1601d03c0305c02c2c075661580c10f108031805c891202491800002e201041180c540140b2050703812524141c101441240050402400034090107403c4a0043e042c0c01c8174000c00384080c0036101a200c3d6410312040040141d4030a11985000c41d003030100601e0151468030542ca03132139610200420802c1035000042d106904801802400c0d030082c0482600070072035100f00c42000c0c9104c0c241c006912014082e55104d050f090000400c40d41e4014004c0000040d00065400191606014002103500041d0340c240821092450300a400c0390414000265500c000503490043c1c1c0c12036215450035041e180c040030a64100c2d210090161b42e010400725130941440307518404ca4601900c449803030035441d503104621703151142d8001c9500460400042081c0080e207221a05100c0507860520f14246400d030000383c0d1441c1e14480300e480f400e40050042c906940310340c804e49058162010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 54090588 1250 54089338 54089351
    0xf01020708120601020c010909051012110301060602060f1b190306060806061e0d0902030703050703050601050901031a071107090522080f070c0308030103150b0301020c070501030509030706 83
    0x148800c0c0394100c080c01900c0b04541c0d4020074510360010a09891a500681d40c01d242c40340340c80d5903140940f40c043c0101e030a4950000c404190500031403521101c050181110088203103002050500312081507111404540003501445800c0c0d8180c50a590000764889000c2c0c0341041c4141d40c55054402c005880b2003061100c00c000c0581c2c1c6d019009581103420b95101d411880e518032050040c5032144030744c01039009840012100003000028040c1c544041c401d00300041080b00c42e80843e10749800c1c0d80003591181c1c0a86c1040081040800080717014041c00d880c44411341d45580d403007038011241280390070881103a840000710740900c9210b05040c03001c00e010449175001e9071041c01c00c005000503295400300c0c40c0c0081c00f40c54005100c0a20905055101082500c0c09001d1001d4244980114000300c5144880d400d001021a07802c50146004c1d5008000e0040c12215444110040706c61960101c4d0003a4011704c04045250000b0503100d040f10003c1c02c0c080b41c15a10002c501d03042d4031442d00c2c01040c4602c2e02c2d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 54091838 1250 54090588 54090593
    0x102040b1602130621060e0f100f0903090303030207020102210a0206060402090109121401020304060204090e0f0304050103020703090509010f080f0c0319030c0b0106030b040f05060d0201030b030f010207 89
    0x3001c59a00c28001d0b0390f41c540e02904040040d043d14900d004400702044441406807880343e00c1010707030078854010000040c2083e030402c03a02d0b0030680c041c0e211400a0740703e40140605c942040c881e6925034500000d00700000034059401820b28032103440094181503012a4480a44e4000e00042262100b03031028031810b4404400a0001078100b0030b07690006100e4030780000c0c4982814030072540b1000058442c81611464030460f05211041100211110182c0e44400c2c1030701c40090014602861040c800035803540d09100d4008221060382452603220703800015a1400c201c0040111010b0b5042840c0250f5110780a083c143d0b484021940401e4100d01504000500400035403c014262500720080d5281003e0820420350b035811103402042d8150003041c0e4000c585040d0b4580781c0d0005200303060454030560b15451300c4001510917402140400e8640d10f140a1610700346c8502c207001c80b4035440c200101d017465000715010000c1c101000341450382e40d9814003001d59041083c039500108202c002d5680380c48a2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 54093088 1250 54091838 54091867
    0x20d060612060b070c0317071401061d040f06020d0b120a17030103080a120e060f0f070906092903360c04090204290a1a03010b07050102040b 62
    0x19041a10700c1480e140011642c4410f01c2c0450702c94603041610a08002e0450b20380a00d250100c400102d0128010407003032000a00c06d5011a41e50203209000007030311482e28513411404001c4001c4c00d0480c210a03002c100002d44104002c0310401d81000700142ca801041355a000181002c0c52810380c007000c8000c1c505486c903000a00e4564041c4140110303059180c0641e00288a40000c1c00020881001440003150302e034465000c0710924002031201040c1c04900c102c9090400301e040d40e80903002c0c00e408041281b0128031604042e00b1a0292804c03078003c900e07140004101c28a14068200c99010240950f50340011403807010440e800d0780111540d0302d042c040800e402103291032800418400c242c9159111450004038582001c03140080580745190704030007000001e280c0c0321b04c100c0e40659580307541120010904071001c04900590103100c810071043e410065103105540c0050301c114410703158194464200403d0300c2c112024144481d48401030761401d6806800307290801034400c13202140c3c04031180c510707 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 54094338 1250 54093088 54093107
    0x10605120105100602030f1206010e0411030907050102060603030d0902060f130603060b1801030b010c0b090307020405100302010c080c01091e1a0f1807030b090a0b07020705090402040f020d0606 85
    0x183d005040f4040e42c031541a610b07402600382e6180c54000c24072400d01d0750f0801c507c206903c010149020200030a881340046c0840c0c1c1090b040d000000004070400690031010014403000c1d1009000070540d600e03113600060381c0d07440b54803400e80c078440d1503a641c10215211102500c2a84d80c00c03015080d16920074080385604207000c0d105420020742400300c0000d1080d100d074212600a001c030340300160094620340066000e000d0300c1c07813602d041042a44544001c1384041410a025656420143d9990301050040000740e40002d03000410580b4107200400040c1e8200742d990310425441948540c5030b0181000e454010040407002500c10041c45020307000750000d072224040158441c2003a10000d003d03a40c0000d407030007801c660707009403920044040f5070f12036890600b070014190f0400444d40e03455103d44e103608101ca800d0740d034000151b02c079186c3d0800b00b0015a00aa501084510040a440b460f09002500d6450003510280c0166911103901d000254150111012092182e00a018943d034441009041015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 54095588 1250 54094338 54094351
    0x1050a020f1f0b03281e030201051b0307080133050a1404080316080706060e010303110318010302130b0d02031e0f040f0204020d05040308040302010c020327010512010306021305010f050d0509010605120105 90
    0xa05c80b016410b04bc40e109913401202150399216181c1c0c20001404020500e0f10b080d0401c035441a207051240071006822200c4d101081e42d26030340c07035000b0341c50050607032030340c020302140c1c1e054040c00144101a0b00005442480204800d24400c8401a090625440c4205400a0012030410001080c10340792581c0c01c6040701c7c46030b03130341d5001103002c40c590030303100e000300c0c0031a808180700386024415640c07182c0c010344130508401b0300795048070f1760390000b010b03042e80a4554407ea1036004003c010401c988860480c1940c41c07036403580c0110707103084407142e442194024401000c81c10481541c8081d5200c1e80d0690305c1c60007501504101500307182c1400303801c865040310704400660a048050403058408030607650750307031041402c500044045001904408260040c0030f81000420311100c2080c00c0421511070082d8064030780107270344480c06222401d030384603a030700820705202c3d203e42c0075040180c0c40021103c4000403900d0005a40d100e11804601405866121650042d80b010f0401c0b403074001075000902908 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 54096838 1250 54095588 54095611
    0x7051e0705100b060904150b0403030210050601050a020d080a0906050403020a0506060f0d03051b150115080c040603050a090501020316120504050303010501050a020f1f0b03281e03020105 82
    0x10a81e1212800c0c0c83c501100682c00c000240014001c40c20203800801d1801c00b003400c0780212549138560b100c2243c1041d131003580140e1051040542c0c280242c0306090308480d0a2034810f141040d1076402a66601400c94a5410041e82c40f00007866002c00d580040700720f50380103030248010700709410001d544802d03d540664941c011280400d401d860400c803480030103c000740812400004985090b50f082e0420700d80d1444015500780b031500c90790000e001c0045111204c072014401c550414248204850301310800005020560303061150213156602600c0403a441450041503e0b45c41d00d0005005e061000d2004240398008800d01900400b4048800c4046500d5607689401110205900c025503200303540190242d00704000500c59940700303400400240780c1600484124a0030004040c2c80c26180c40061240d00c21b9042c40305d1224287c03801040c5030502e0440c001c16950450803040010000c0c0d50304444094184203500301d00300466040e84640b42403400560803150222402e010f8044c200440f80c403007a10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 54098088 1250 54096838 54096853
    0x20304050a1d060906150d150807080f01090503040e07050d060b03011d0402060f030414070e0a0c05090f0f0301090c0f050906090103030c02010815060703030f0606020a03020c0907051e0705 83
    0x41c10b08503012440f171180206000303885038040040980c1680544c1c0007001c00c980790440d002500d44c505045030002d0044000804019144c032204034281240500000c0080c0d040030031640c0420000070949040d105140e84000b00c640303504200750b4161040035228410790f410800b0018003008108059412902ca400b9084020001491441d0803a00103c50080d4400000e01519103c40350002c080c550252045e20054a10412040381c0da29014490340506d0000b00240c0400404041c28082e162000038241809410910131100190f00103416414190088050345d10110040e502504262002c0781c00490401c1d01036150004000303401e955014a9003d80d4606c4040b0f8110b04044003414101c035095552200005075076070044600c04d5004e070025240385011400d0b522140e90390340041c50410300c2901c0000303030000202081d1050300c503558401c0065400008252001ca9000702d1001103101045a01031070556424806850300d000304688241050800040300703400044600040071078500850440b080b2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 54099338 1250 54098088 54098101
    0xc0623010602010e07030602071113020403020301150522020d0e030903150601020a08030a1401180e0f07090e0312011502070b0f04140117091b06130b0a020304050a1d 73
    0x13690212103a003412030b80a00b0041000c18802d40c040c01c0964403d500308148031f000400014103041d00c6c803c006160a5001908000f149001d102d070203011045407801ca06aa880c01002514000d202042001b544200c14403040c40c051065044504111f0394800c10068685c85020096481d040884080d01030321030240f581995000c0408124403441059006060307a12841e980c0303840c0340e000580070f0b03100b440d107507051086c860460484540c040c144040b04102d00308050841801920300e03220055115801005104184035400f0035003805035049840c0100300400030b00b10f0030703245200381c44060710b4001f501800811120b011340407040d410031041d82113400064844c0d4414602c2e01c40d02e0110280c003e000c01040042c6924000f45070006501414540c0003c403203200f404480d60350803607956816400045481c1d03003c0842c484032805048081d1016414880151460311542c03915000b0140403080c04121040c000b13108100700c8000c0c0101510520005035603802417079a8260707030b44078810b100c030721040003600 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 54100588 1250 54099338 54099341
    0x102060604020403080a0c03050408060c071b180b13060e160201060806010311030a0f110a0f030b0f220b0a05010e0721020403060e060105030118050601030b070c062301060201 77
    0x1905c1d080300b021403800d550004255a42d9400030070450a00009010004401d8400c2c00403510130341840c80c1c2e02e0b640b101145445401d1840403d40000340d407440c840305010038907612180000440c0ca05100184410340600050001400007103a44030240c100f11000c43d5140c0c09150980c0100b0344640006464806000240d0981c0c403240070f4042194407070310040010030140445036102c0c000103015620080003075194824000e4041c0000d54a1160b0401640103d007048a02c84008041d002c100802075401c55480780301a00d0b01414070390300d180404010070341002a0307518907144030010703404001e07c00301c5924042c5024602117581c001000e18120000a0303040302060054031072040313a5102981041e00c1c451100190221155100b50305a00b80000b02c0050034600c40c0d10741b038806c075000514032503161400701820355080150308480c480220740c105000510020300103040d02d50106520801d82d441000480396141d40c810302170807660400c000204800400d01075040100094070f0614803603030b00c0307120990 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 54101838 1250 54100588 54100597
    0x10c050720010c050124060302130e0406110a0f0206180c040f0f1503110f06271c060c020d0c030e040209030a1a0f01050604030213110a020c010206060402 68
    0xc041155201680080541048840c03030807000504105560f09455150a406c40d5000440303124403100325003402c00f50b071461801090041c2080c2ca815450800c140c2100401d014103803191000400380e020100701000011b410481c0b04101d0f181160b80c558030244001014080020301c000090b01034003000c200d118030742c854180901868000145140c03511982480024182654190702c91581c400b030089180c1d078a0702442d40c8031581c1c0818446180c0c00c600f00a0941150200392510810709550300c1420b9483e20b0301502c000b103a06582c0c96200100802e141c01c8803040a81000350f01c4070341006d1140f5128801d890350741c1c0107400390303104101d0b27100d8165059903594541e4080e000405d441d01c40040000e445155030284a8074040e03c0036041c00d140c003000c40d107003401700780049564590242e21a9010840481150362061264000d60425450030001c140301d40300d80c0c080030340140f10000c0c640501c80601d07005074015a80003103015075141c0301854000d481d5002d04502d18018040e11011034000e103014000c3e40c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 54103088 1250 54101838 54101843
    0x308010e160519110d0f12020a0206042307090617060105010509040c09050303120108060a0c1403090a0b01080102091203070c05040b12060108010c080c07110f13021803010c0507 78
    0x36140012900d40c001d05a250507030890100103600c150044011300902120b80110b00c561110212440306050260145c0b0341c0b001860b024501c140036440b00942c3c000380c03083d00b00350460380241c030003d4143d40c6042d40e1440681451228030884100040c04600d41e8401001c54440350300c40c0e03003101c071104411603c5140c284a002d00007402840a80024a4558440c950340c080310f08201c08002d5031100800d045810072088404900c108500403c80d61605008155022583c0751003008031002e1400007814001c3c04005040c1040300100014550705002c100310030035207401100100041d84d5801c010360103580b00e915010702510030400300c130300c00003000002e48004135403080340515824245400c3c04020000117010720350016511460343c2c62003800b4032400e406080d050001041840800380050143c9001400d41d030310780c6201300060808a60303808403910580c642120a00359401414000400900294807200c21541c80001c51030341303c440b00c101d4401804000c2d0001c0c46401e50742c0c10261542d00800802 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 54104338 1250 54103088 54103097
    0xf09050315040201080612011a18070203160c23040c0e0d0b0901020403120509090601090303050d0c02010f0c02010212061f0305130b0a051b0406020304090506030c0d0308010e16 78
    0x440c00542c0030741700859000002a05000703402e2400f400c000d080d1403c4102c60b40e03103800806c030003240a040501c0c403d2590945840c6910707003802c2c070250003036030383c840c08018802c00d120b07600c060005c00503e24000340042905101d02e00303100c03c08403524801140c1c210b103680d00c03984c64011f0025085004000c0f101c24503000400800001c022610f03808910100145801d105550070400400002c1d00c2c4000c01101030f8542d9640d40d1141c081070240140b00c240940a0360512640c00d008000181c2c2c48002c80700c0315130f02e60101040c1448001300c1a4090480b0012002c03540d42807090105142da8154054441008107540c9117000351030b10014003908088446c0e01142c018025086110114007036003002d60451202c0c00d081580054544a8040c481402c2d541504000d440e032040c096540520280c4225061241e141c061900c1d1424202968900c924883c07003101588810010326691f80600c07000c0320b01407029048076101c20f010700c1c0081a548090240001040a0b0008900901c4003401d420302c0c0250319844 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 54105588 1250 54104338 54104341
    0x103090b0c0d060e090a0311070e0c070606060e130b04110a050a080105040c020d0503100f170606090906160504081002090a090b030d200f07150e09010b03060105190f09050315 77
    0x30100d40e0700310b8802d400360161060b46e1000488a540001c054415118bc1c40b15130346442041c42c21100313450080d40003504210202c50000b81e01e503120210f844c2c6d8188d200d0350024207200c5000205020b010303a417601c0c4080280100b120080070307402a000b030030309003010b50b22501c45a88800400007200c240c0407900d8016401041017492050064000b5a00104001c000f9070715181d9070200d403c1d5002c1d441d088400803100701002d032030700241c0410816400800032030b02d404c010310706607941c96902c0d40c005200320340b00f5200c4000101010b000d042124040c225400955400e000a000d900001e940510400c42c051001424001364800444c0708004030407000802510209010343c401b120010103405000380b000c402561300142c455404c00c203204091040b000a010154540959070700820801103070031090006041e000aa40e030b807003012a90565094840c0345481e9103481004803402d0142c84101c1c900b0250041c0301e42140d40d042450500c02c0d000390780da81400319464006040e1242064000942e0501c840b20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 54106838 1250 54105588 54105593
    0x414010504110c0304030602041d04030e1009120f14030703080a0203070504170f0c0118090f020f040e0103050601050406030510090203010b0a0f030b100b04140103090b0c0d060e090a 80
    0x10032240c8440d450310705143c02c10000814880c11640300380e01c12106260300040800c2610b400001e0741c500e0101280351000c0038900394038040c05650b00c10b544203101311030320b041e10b02260b802915080040d20007003200e00440c3e2854941108c550001510a80300302e52210003d25a001c400421100d8440c0d0655034031503551a00001e58020350400340c41d00050045c01d0001041c44000311a80c4600c100c28000204406000b820026041110300c804450420201069580f4181808000e19040f241c6500c2c0002d5110050b071407800c005d0055201c1e414070313940c0001c0d0002d00c01d40050f45441c1644c2c05042034071941e9907100c003003008581c0240700c010015041244400e030940e0071035001900312030000c1c1c004541060044000303003854249402614a1010b081c200b80709206804150315840070091031500501c90800301da5094a00891054407800800f2001c5590b031079210707800000110341c0c810000107941c00d000400e040c494115001014815241c84000507444201240e030a00070616103000d010414110f4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 54108088 1250 54106838 54106841
    0x604061209030e15070b1f141302130602070506070b0103020d11150a02010b0406050d020d0807020603181b0918070305030c0109031209080a031d0106030305030a0b0414010504 77
    0x1404168140080b141c5460340faa22080611210f200441c81401e5840009103080030051802074100310142c642040e00e00c1d0084000404031042d551a03030607800e2280100e00c000355100340d100d04600440d90010076030040c000c03011424a410354000d03400f0784220545070310501001d801051030242a41c100700d0700410160905494200e81d4034040d2609008486a05003c50300080404024214400000881500966080c400c0b40082c0404641c203003c840c0c0f80c00001a0500070544010f8881d03c590b41d0141b0070005584104c1e15400c2d03010306034a45900d001c0341401c3c1011084502e4018034003a2440300824011228a80800c204004000c0c1c0703200d4607619220746107103149000c4014644100c030f2000c000702d20b082001c1c021254520002190107211494024408540480d11003085828007181c20002400c5030150b0303003e811a03280000384801c454817141400003618440450b25483c0400c04014075511000441c861241c400c41404490349202c144011101040841d5070481b9034400184150b1419 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 54109338 1250 54108088 54108101
    0x30c090f03101b020f0a0f1e120e0906040e150c07080301090902150307050a0503060f090a0c0e030a02030a0605040f0b0106090614040b0a030902060c0312040c0506040612 75
    0x6030841c0c00030010111070320201c030310101c062404002d08416450f40c15a0400080009140010280031105155940c1d061012040d0030010041c8210f19103801c00c07070300d22a115006240c1c11140a0700100d14028019000800b80003165010f01c070700d200040d050f42418020305003140d58000092501d075403a481c1100c12404c01810417008090204480d8020038502e60255018206c40640014020410320400c0405120540e200400c43c10500400019035007080944007100c499040055903036413030400140c80607181c507002c0c1d540000180705006a01440d54420680105c4545504010700280c50400d0760700c00032244025030660202c01007400142180e0000c1e50001e02c204005285001240d40f41c81c100d040c260442e10000d091030804000c1c4641c8100607070340000c807580b0103528081c1040c6000089100e442c419809142c1c44012000440d11050102c403401015002500e0711540c0040d600007a1920a40781582d1b03240c1100c03800b250f00c1c6810b000b114102ca05a071500030b9030306c000b0380442000d0540b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 54110588 1250 54109338 54109369
    0x302060901140912070810090803071404030204050421030b06040308090d02042a03020304020d0803100b03070302090a0807050102031209010f090305190c1707060605030f1c05030c09 80
    0x1000d0000700f18035200c0038407035080d40340c0e02405080076500b41503055250070742e0301e1540e1010034284002180480c900c402143e40121803890028540010032154030705601c51a4402900580ba1004100a01c0207010a603401850800e40702203886045a8045094540c610412640b0640c204010030000e00d640000340369014020b84a100820019000602110084c0241e510240f0350040300f03210170280d1003007041420500341011811400c003900130440420b000c040003082000000081650155480d5a81c4020702810032007561f40d2408100090123904001507260080643c9840031652190100d141001d840040c0d004606041d804c4041c81403d15001d40810b840d950b941c0c80c2c801d45c000c0300c0d00030313148024001c1c0c4405640301180c41e902404111004104010020300101140001b0510442103991840952032140c4035109810008004c05143d40701c40d40c1880b94500901c54201c0206003016200d03040b003200345842c4c031200340950781d07844110b46901340c0c00c0d405c01c01e25030340c1d10f4030381402c940449 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 54111838 1250 54110588 54110627
    0xf1f031502070506060a0602120901020709060803071208090a06021605011b020705090103200d080d0c11030c0d050a02151501021509070b0d0f0f05061f170604152d0302060901 77
    0x1030ba1003210004035401c0d0f8121010a401c00980c29082c40b960304003011014500d4a400c991503d485742c00c0c81c0d03e5880e1140d000300010380000701210036404c0800c28020b000e8000d00200003044180a000c08254500c0f600100075000300b000000e200e00d0184580d504a90f00404100a032401a48514642080d540312107030b8030041980450001c100b0040141c0b070030300090000029003a242002c00f43c040c1501d0008441180d2040007101240540490030003680803890404c0343d01d8205400c000d82c284900c1c0c0e2040749207542a101008080036021404110360340d420380030703102865004010032036404002c036910341d0369030f1201c002003084440401c0101072190f10520001f500010000303070207094070104407060b440380d52600180840f6180c00641e15182a4410a10b820082d5101c08041c00c0030f0105035850105610340d10000300300c0e4880d5000a1504054281329000160300c60380c59a0104003940600104d1400a4071845e039411000c034002c0c020f907030700141458103045a010045030310242c4401d1300244032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 54113088 1250 54111838 54111853
    0x315040203120d02031504091214091801150801060903030e0102070b0c0a020102010e01020903070e0c13030f12020606061902010b120a03170f1f031502070506060a060212090102 78
    0xb0003070350050200d0424103000543e8900340000000d5841c00d640560601c40c5140420000010340d10300c1c10324044046034107042512542c200e188100c6800345a62841d00304800140940741e6540c044c000394183c07080500746000c1200200d10890b44c4a009000f076030003081300d002050000c280101c410243c4008144116084251159031522a6403c1680d01c290f1035072100d0582400c540c0c0a004031800700c0010300c002c5007822500c41c00a5138036001071040c003c0442c140000325900091810460b4590418109000101ca0341c0307260950300c0007071003902030701d07030540340498950594804140b10b8011b44006108a04140040c1a81034516104c0a000c106665880074408020349880010380034010722203024158414040c1005012200303800140c030094001d81040101c0c0440601410b40c100b14a64445e808915240001c6005c5003056000035002e038440da004001104030580060810a20030801e95a441e26035400748040d81d007040c060503005d40c12114940d2070300682500a4183c1810501c1145c085 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 54114338 1250 54113088 54113113
    0x170102070c062a080409020d020405030d02070f12050a02040209030a0f03050a020d0207080d0c050a0605011e0501030207030816090e01030b0406060839090906010602011a0315040203 80
    0x16819440324001c03a02e600c3c0f07401001e440e200c012031002c00901426215032400d9664501c29881940540c3c01004d82c049400c9948a499030705442c0a0b20001e01100d066248070b02c80a03654036014420a21500383c032040100301140783c402e00c01a959400b00007480828002e5080001035003104c204503805101d13047d40a00420242e0700d90300c280c240641c64141d600d0340307544002800c1039801170f4110159400708070100008000001c0f6031300301140d03074649822426214a0450f00300000c2c800042c090504040000c140780351401808084dd5000104003001c07541c0e1a00154140e0140b16070160215080c5800030745075040c94070270041001007902d4240c8000d6160410b00520300c4081c0c02c255010200f840420040060074031680d4003070803842c402001c84c4807071000000d04060940c0380c0d0030702d1038824560850000000c0740c02c024400d5002000b040e254a4109000c0b0b6940809101d204015801d0022005d03000442000101440724050090a410000720302c1d0221400c138083c004a804d0700c182214820b0303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 54115588 1250 54114338 54114353
    0x9030a0309090b01020304050102070b030c0c071e06081909081b01020306090114100309030207090c110105060613030204020702061207020a05010c0e090a15030c080706080114060417010207 83
    0x408500c40d88a010405040002d81c10841e90041c0d000c038107650080100b888503a800042c0582282d5000d05071540d41c0d40d8410048810740a40707004e600640c800c032440441c101c041d1101c1a4a41066001d6403010702d070b030342d0383d08599441c8281d5030013400d2102d442055218280d607801040085006540c0c40d0300d812403031103084012074480510745420381d6000c801d11031580b4040126900500300c0c0c500700044120000005180f045041021030240341d40c3d05c07200410580240315000040481003000c001100e03c4031405084450b49010940481d4a810001009440c01d0003c0c2c88185a061011070f12607400d5174240300c0294040082030340d00031014060314940c008100c80c0140320300d1907603019202c110036503c3e00600755600c10000800b800a0100c8000300c90b21201c00c082e41c03000700342d038001c01e0420101c03c010f2145412074102400d591800f0402189141c5c0000b41c031011507045545101113681c0e180303614120882c2a600040d0f00c030800b000700304102c003c0c905901c111914a00c00051038008566111030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 54116838 1250 54115588 54115603
    0x111906112113050d02150c0a050a0b0118060608010b0a050d0507111c0e091312030204140102030309070b031e040c0905010501030b0a06180f080c0906060c06010905040204020903 78
    0x32400e64005907040d031910340c0941000082c4426144107030000010750001b000e4842d1040d0b102c4407204049130025281c88100030300c00b6030580100996503c0901e03030800707071109a024001c032040c50001c20007420030588648180c604a070103640c0c80c00c00307590034042c0c022a1075000f080c021041010902072500a64841d1107141c1c01590161101c100e2401e200102504182000921500d5044050840b102c51a001a0740c00340b200b104858400d0f1950ba007480540c00c5158120303001c1d0003c20095032044000e034244e4001c0090703d9490319103c80600024004998030f12044607065038540050300104540c06020780550741060012001210300b8100c44142040c201d0100e80c260b40c8151551010029100c480c03040501401c000e203804d118042c58600850307016440e5114040420054102c20044800524000b8015184d0400194941c40c2c4d41c0719060365500e904480d5520a004240200c0e085d4030700719088420b540503040203800c07142c0c40c1010003001410003c00a80e0026000c0040000c5075901f4007502 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 54118088 1250 54116838 54116893
    0x9090a0c080708120a0207180f020d15051512180d030f0506010c0201080610020f0a05030c070803070507031104060f120506010603050c07020f13050103050a11190611 73
    0x4004403454000b4652411140c00d0b0741d6441d90008020b000041341d03022031720744292082004840c8190401c148d8a030001c1c01d414038034411031840801c0601c0300800603044074104440da103400300f19036501c4404110409803c01199160f480003000b110604404511800c1d500806d200d140f070b244040c0e0800f403541000c000113022030020750f680d452030001000902c90355400c15020b1a048131820a513a001801c9858090b000e5441009600010b101c810f10802100101001600c1510b43c0840c0382c1c502103660360041102c402c9580942c2c91f0120f05220000141e8910300c1c0c014008000072072039030710703122458801030385182d0b041a12410041036001110310440002d1403410780c8110200d0702420118249441a08180101130506c014804481d103114180d520b1584c044442520a41350900000c5641c214940d03c1d000050401000200b4018040365641507180a0f45041450903201e40420003d00040340c10014214284d1740140042440381c000a07020705d80b8081180e4641c5465031800e404400354401d503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 54119338 1250 54118088 54118093
    0x50c090a0303090f0801050601050304080714010606031505030a051905070e13030f081006050a0e0904080301061202120103120e040908030105041808040b09010504170c01030e0610030209090a0c08 86
    0xc004210781000300c28010174403000200314900788100024031500c4041c00c09070440c1c50106030b40d0240403681d200180761100e000020441c4c01d5481502401800401190442c0313484000c00014180c00e0200d1040034048d803080141481200344481d4007000c2030800802e5409e440385140119010140050145c010748980c00c1c50000e801140c5070080c010704c1e0211709407041080d00740a1264610003c81e141080e51218100710741c0700c1e140c101044422030004407030960300502a500340801d10000306c00540c141d54460340e030080000b03421a0098141e01c90b003002541400100001000892030072401100f17411642d00e0003854104114000a041c0c2c1c41210003550604030010041000d071a00e0300ca0b60070300031a41403044000340c1c0035482d424200e00441c4150804a203000400030740c40c2e031140c1c00300c1d005014841c140c000e03040c002e4000e0ba1354621401620f00d01003894010356100c0c95400003134030340c032030040c01000050160031582408030401d00648601302c10b2013404060b8000a000a512034003400e507a100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 54120588 1250 54119338 54119357
    0x130b0901051602010c090504020d02090607080a0305060603010608060f040e0105090601060e2e090503031306090608190e0f01020c061009110409180807080d0b0603070f03050c090a0303 81
    0x1100250b40c1031401c2c8006580c90010045111a040482002102d5044078016100c51611010001034440d60202c0c6901190000d825410030082a024281d006c003555400c0195650340710038896284004e01444000c14080b00018203d4500301d01040500480680045111103034413070214290382c03081c3c982750603603044030006211040d801002c89c02402c800321442c44030031303449120920200c4051050028400003a1000100980c02022460003d120140c02c07681e894000c120044150040c60240c1c1000680f002c00c00204180f02c1c48400f03004039680c003480000c0000c0560114010311134041038a999000d4030005100d0110288040c1c07000540c000d0280005103800c0fa10310141019a80105000b60700d084c013a01500e0340410306850030381f82031104c001188100100d00c5051003140c0b51000307025513000910402001140c1d0041c160070301c04c0b60300c14084240c4480070480180007c403401c00010700c080c0424844188a03810007604000f070046164503240c40900850420070303080c0c005401050b103200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 54121838 1250 54120588 54120601
    0x509010306020c010c0203041d09010b120303040b01090603030e010809070f140a1a090d03050705030418051015050f0403020406030302060115031a0d0201110601060e120a0c03020405130b090105 85
    0x1400c100c40326175101852510b801c02d1244005100311b811400c11103005000058084030095200ca5458000101a610102d1030080ba20b6625402120200c03031040c41c1c04c00004030f51049000701004c0d0fa525844030092502164011551300e00700401e110403500c00c9840c000344111480d035840f0050302e061448684020342201c1805104480c81e4807080f40203080c280c084412507011815100c052104840c40c0070031004d14202291503000320600034025001c0010005040c80001d016030445045010040c041c0340e84c0c8081005003102540b003182200260880b0020086100318020858200b030152020704003038a03030f000b00d0112a115003044000d03070300140040c0819110004031110700001072509004084aa4144503c42c0d010088510f0050100d0040482160f0041104003240c041d21800c41e00c040d030307644100a015002410115029520495030f80c114090301191110155405c501414206072840d400e0100030100140250681c01c2c0003010400064800c65585000700030300400403a1504114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 54123088 1250 54121838 54121841
    0x708180d1103070503030405090103080a2c0916020a0b10091b2a03050304111810080304140f03010b0a030b06150301050f150405040606170c13031b0509010306020c01 73
    0x260131030381c8254000c1c0810007040d46c0e684946410349610407042904c034011204180c421041c843e00c402462944004845070304d080040106e4400b4a007101e4103083d0740caa655401c40840d10701900e603401600040303030000126810070051508861082917410003340e40d104140c3c201d13100200d492840810207403d410741c90390320120003801d59110300c800c0342c0014982002d0b05240c5540c2d8100400744540440010240416150411000340c005400d00340c2601010704d024040800031a88403a0101c1001c40c04108458008282d60545040384600190b030545002000100c000f1803103400c0c1e1540d2684a2072159480d80c10038600114400c064004e02401c01d0390030842c141d030445000d840c822900380010070003a0740c5c4d00d002040000047e50102c08860300c0ca10348070101d00ca2500510b400a0800d840018200d0f40300402c143d0360241440d0010182c3c03608045016a8880c2c803a18503040400d6030740030301c041200c135881144030000b2240d001d080360340e80d10003203035070310009900995195501107483c00e01c00c1400e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 54124338 1250 54123088 54123103
    0x510080405010e0303010b07261c0e060601020304050103090f050f060a0b060f0d02070c0b0c070e0c0702011e0c060c0f030e1606030906020408060411010210110708180d1103 76
    0xc8042d45c11981020810004d034080c410016050316036075180780c4400074441d10040120610f900002e551000d0440410002c540b00034001500d07140380c4292049000d20100b8944d0107010305038081c2d4586898000110050305424a0548081c00040003c60002c1c5080014048904409001d014a45442c2c05030310111420b08480350301a02c020008610381a0a66048442c20b1380400c80060301c1d2032290401e007148080301d400442c440880041c0d00d181071403000401408170b07100c08041500700d940e00c0f40038407168018840c00034003140f15415150112103060740c2440c8040d0b0a803a04511116040e1240001d41e2000041500410071080e00c044d2010f500d40108005480800001c140708900342c400c0081000040c0b244100705690307021460104882e54040310004d0100b0000c8503420704150030b00780014081b00401354003520880c0c010320f000d910741e802551440c400d200c0000b810b20820380ca5a1f44580e228000c1540b588040c05c00018481e5900030046c4407503405210300d0028118408203240c58400d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 54125588 1250 54124338 54124361
    0x501030b0f010b070b28050118230417040f050a0503010c020c130204031b0608010e01030308040201081005040e0601090606110705131503060b04050703050106020c09060a051008040501 81
    0x21441c014025801142e00b02c80441e41e000c41c00711640c0d5160380010b078140300100f8402c00b80100c100501d100035841d540001c0c0c140d4105c030143c0000c098440e0b00f02800c175000102c122070642140048400407040000060341c2c407500907604407040b851030340740f514000d60184d00700e84c6841141c803c0901c0f0b6402c0012401c1c1c050541503000300401e00c4038000c06540d07180c9401c003152180ea550720b0540800f8030183c043c2c5006541c030842910422080741e850202c40545401040b00151441000180e4400b810990f28102c81d0035481e020400e071070b0380c3c0045a0040c8002c181403d11225101c00003080d898900c1b8110849142c0d2002d01070650601107048150f5529501940800c00c505000e50b6441c0c034045044412605d0455001d520620007801200260040d0a2041c4d030055130b072840041404107030b40004036403400807282040b07550344032002a030440d1028040d4600503800406900c00c58140402001e0704194001c049030321140d56840010540c4411032180800154160280410010b0074000d1000240e07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 54126838 1250 54125588 54125611
    0xd03050606120408041e15020705240403020d05010504030206060303190e1f050c010b190303030207060e0f0a0309050d02010c0201080c0c03030412080a052205030c01020d0501030b 79
    0x90050000388036000c2c00340d10080301d42e0b0407000f1504008410381110700400c3d9203280c440d4864001d0313424921803045407080860309814070300e5207503c0f544049010025920014075000a5080c012000060910503000208050034204400310141e40e0b40d40400c0101486800086070701d14040c80d0007810100c001e850140658024803001140d000d8180100912000b14642403140b800c10f40006980800c0e1040c8400c6403002c01c00e10200c00e503911000400f2104002d0009001200841040c008141000302c0c015006042440b02400040d01c603800a00c582030060342d01250110004100300c5c2004144c1d2030101c42c0381d0003907040008058008003030b41e00600003200c0358602d02949030006001894042d200a0402c813605000030701e5014100c065528100c1400d04980c3c03280f600c2c0c0f5045160590146401010032212400110f4510301400340c0341c40317130082032100c0114911401d02c5c8c2c0744044038181c0880c0e0500040c0060807081200344040d04400200b003a01086a500d54204040c0449000d0032104080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 54128088 1250 54126838 54126841
    0x14040c0806090105060717031302010906090f05060a051e1b030708090603040312091203050a050603120f0d090b010f050111060c13050913170a12090201090b0d05090d0305 75
    0x250b0340c41000030304640050b40e2036a940d2000340b900107a10107203191030b40640940401030040c040d0a840011907018400e80b0703080a466140d280540e01c1c00000d2041c8403040c100c5420603c064142003010741620340c8103040150604031045174031044101c003518940541440880c81c810080c1c01804200020b90704407000c0e40c80e100760398460300c42c02d03c1205800d0b07004440c0080410100b5104042900717000301c000d04104000001440c00035031019100ca58200040c0c2043c010480b1000d003482040d00484000f0000c0c80100c64444041c0c2d12500824a8914407160505c0b036200c1c11810341c021200d030b04e27206a034510129810050b80e900d2526860300b02c641080f90000103d82500070000700c654002825580703550b01c2c0d0b031315503240040c1503400390030940d000304100c02800311164102000d003030320754481c0380c0c40700145021070b914050074020610381d5030028030668131b01e0b80640c416a208901e000e00600d4604402a1134098041c4607502200d0b0031000c81d0383c0e8004101210300c3c1406407264071012807609010030b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 54129338 1250 54128088 54128101
    0x50d02060a0b06040e070e03030a02011e0501150e060d06061e0906050318030417010506041a0303070303020309030c01151e0605030105093d050a0e0106050a02030403050714040c08 79
    0x6405a0300a1405d03030450b400c0440c11080c083c641d21207100d00010200d03a030301c0c810310000a000e45040c1090103002c0202e1000c811440700c090090324103035907a14244108000414000302e4403030900c05d01c0590460010031881405811500808010301308a4440040c11503035078030681c07500e8116403c1401000b03807100d403d2042c02d070300c0303021070350050114110b44000118008007079046100c0c0d588002c21400404280f603050000642100d84903260448080100b007034005960b404280c00036488030703415001000b121000a029034051608014600f0071a400c0030b041074112030855001c5c2542c01280da0840f10200b00c910800314007040000342c0750048084851410f000a8040c4c00103001c2d151003024880d00055051034441c1c100f102d0514202c070842001488685101c174258103481070000f070a02492004100c03420008503800807188079201d41e80c810f03840c1600448058000c2062a8110f02040000001090040000e4800b4120310900000041b8105d420442101c4210800006100840c2d041040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 54130588 1250 54129338 54129349
    0x30c030601080a0e0a0c030201031a06090103090f0609050a0b07021204140d020d0c080c010219060b0d0c0b0d14070906030b0301020d020c0109060e1c1b02030a050d02060a0b 76
    0x402680c282002a07030354560454090282480c200c1d0a482d61141d50904c105005002003841c04583c000e03241085000500d074140b0703500c0e00008900640080007044842c0613035200c3c0e0700800969018480d81d0061480c1ca5568400b916019641610075612048210b0f0902800000068104070b182c0000c015a02c4651049822806544100e2105c0c0e100c4401000d42e54031742c0d42a801d84d00383d0040c075424000d2800e150010320760f4110700810445204800084241d9400000c0135201400440c0c0c4503900040c00c8d6032b408001c3d010380070072240c000b45116000c00008100140d10409800240740f0180c86d50100440300c1c0464185003810298001d5040a01c21907a0700819103001b61451840c0100f4068400340209029109621801078003510008284059050640c0400c0d05140301e100c0c00c0c02820442c1d0745207239443c3c00708400d11b03000e00c1c0c20303003000d0807500d0181c50303148940c1e61a4003101c2c400d041aa0000b03420541114001c1d142c68103e401c45c2070304164140040345d0702211502c410028540c0d004082030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 54131838 1250 54130588 54130591
    0x1e0a030804030306030605070801060207080a020618030f030d0b030c0a0608160306051009080705060f0301090504050a0b04050a030e0907050f09040b0616030906080c0a030b01031407020a05060903030c03 89
    0x50501036940c001c6801e1601ca90030030005181c0018041c0614100414002c10150b424401c1c18014011a040461205004101c81e90710540090040e414404207003500d071100307410540003d03894811084501895001440640801041010b001440725245030a16061924641400740b080e2001c45061160a40159075560012610408015420308003a41500148559080381d9400800e400006280d20b5001c20b0007000d0b0b0305804240d41005680c0d9050000c40e01411241070072069050006001180300c50b0f00c002d1b840360252045038440c15480d10344825086042d0340550b00c0da08002c21401c1031642105403414400416550303442c0c00e01e0840c90081050280ac15268008240018051401e0b134036500800b211a01c02044142c2c0c2d0b190f0140003085010000303504a001c151204400250240141d290301c1c89909585c850624000030544110001d00451490f2070526586016000001100c100406c3c03244071543c004040706a0309040051601100510766543d17503104008004001c12f03a2810f59 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 54133088 1250 54131838 54131843
    0x1106070c1203090c120203070801060e0103080c03040b040e041a010303021b0f0319120804080901030b0402070f08040f050f061b07120804050a08010b01090b0a030f020309060402031e0a 81
    0x10100302118a0101c002c0c0c00c8040002d80a0200c2004c04504800440c0c9491640f910071412180c078130b40d450b1055400da82291040303486030b4101d1001000407918000050111100e0b58007901e10781074440380d9032101d03900203400c00c0d042d5440e14400c020070843d6191240700c076610050031740701c0d05615680d80256540940350440242d40c8071202003e006031500c01e1081d0b60060010151520890b4411210303000c005c5004084c0d0301d0084842000c1401400750072807502450700500c3c40380ca0307c10000d00640142c5030040b002da4000d6803c000b180086621441205401446400c03c07542c1e4500e44102e0045401c090f07044a803244003e4519403002d95031300030490310030808a401c22039540d44030607402c506240060748800103943c0340250a00c100b000d01c40003031054030401ca4480002039143d80c056400c9a510780f51141c0410042e1038184030040c0584098410804a0701c0c01240000e00b415144049c3d17001510f07102c8281c1d004d10300340301c1140381c240642d9445c1d14031248034903119030b840d640443d512600d66201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 54134338 1250 54133088 54133103
    0x2010e0d03020d090b0a020315011d0d030509120d0e0303040b03040605060a030807060f0c1103070b1533030c160303270302070b0f040b210108030a1106070c 69
    0x442041544d4001a504581040680300d10307141c9000180d010707600840c0d500c0108510058488030560250001c0340d05110b080c3d40200002d65800c0c1400005141800141e09201040c00103248654900003404286030302d0f00e000d003140e40e2613404003601540d0502c0c811842038109000900c440c03003a0606480c0c2c000d81154000c90152503810200713940000541010b0301c02c400004440c024004103411407203408004040820681001c500201c3c0c00d003e80d0f13103114407150020000440450380c9414101d0f01700e103003075005024005441000681080880d1641c3c0081807030f41c0c1c000070048101541e03103041140d450640e10714618180e00a40d10502c152039861141005020407442810f02c40d501840040360054011540c104450091a00030ba4680c03070300300c0041c0314000020034401401d0b01074030345810035280c02c6401c04d400e1072030004403074010086000b80c0500d06070030b0b4040c80030380001503402060005c000d156a88182040101240c11142c0900a0365004000380311155038802e80c1f242e003590b0803415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 54135588 1250 54134338 54134347
    0x20a0602070c080d081005010905091501140d140903030403050712021603141b0916050c0303040b0106021e0c060714061602010c020a0f14070905010b0304021002010e0d0302 76
    0x24604880010b903000010325100701000c4075161500000014058100c61000200a60b520070044030460380700c0c0507154001c4148404680e80380f20745008251440414141001d1100340e4640d40049a0001c1d0210070700b50343c48200d09644000c1c0204070540045014002e140745140c00d890148c841e110f8010000c080b21106204058103a00c03d0100e2803803441c0104890311401d41d40c2c244054002103401c15040940103104010104449108001c000200040c1c100050355403541c05003966030381c3c0308100400b8040b0030011420004410b000551103241304600002907941003180091a00000f04151480f04190700760000f0000800100440296401c541c51035840b10306117030089812402a80380a410320403c4288507070a141c0308150303010820190300800003000c3d011001c90b9100c841c08806030080941101c05008585607c004254440c0228103e44505079100e440c0e0044075401d078032035442c50031b000c0148011481c101c6103030a5401c180c0e10081c002c0300103062900c4c0e1100301640072002410350024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 54136694 1106 54135588 54135593
    0x60507060b031b06030703020d021309110403150b0103090203030c01050106030513150509030702090f0103150e0d180504020a020328120f14150a06020607020a060207 73
    0x40090300f081e648200b4842282e202500f08420075400b041044654040ca000800d428001c4111040300c25190002c10b030700701e964903604024040c1d0104000c00105240300051030148501c4400015582c0480b80160000c0c000010000d4060001190351066014107601440c100c0705a624140103135601c0f862000d0114185201c001c245206103032400350085299800a60f00c00c442e170040300c0c0344c60b54580010f07a491104880d2909250140f00050003041380020540d0496001b1290a102c05003001ca090358891001030600010001d003a0035842d000381c02065030340c0007080c000d0002c655404c01088029225401001000550b9a090900c07205c00c00d1030b20001e07080d06000359a0855604240c0100c0009002d1100c0d464040d1902c41c0c4041c0c41032034040c10340c540258240c01044410220030380c20303c6243d4403981d003c1425500000c1c00c010402e0b0f00030844100a9911200040c4c0c0c482691 = true := by decide +kernel

theorem cover : BRFrame.Cov 53956838 54136694 := by
  have h0 := BRFrame.cov_init 53956838
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53956838 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 53956838 ≤ n) (h2 : n < 54136694) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
