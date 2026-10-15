-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5555
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:15:02.307119+00:00
-- url     : https://prove2.me/submissions/dc29eb23-a2e6-467e-9856-4d4680861719

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 998920863 ≤ n < 999100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 998922113 1250 998920863 998920891
    0x1802071e0f20090117030d02042c150103050a090b04030c0c0f0b030103060509010b0303030a02090a0b040b0306100e0310241802092b110a15050d02071a 67
    0x110ba48641c030b0489290615000b045020040045100c2000140358103000881624188a00c0d1440d0b1030480e007041d800380c0d08413a54856090f40b420160480c201801410b18940036592030000640786c0800120540385e410540d4030000160480b501e07610000e022680249070845a00749410001c00780400c4601c01da039005140d01c1c001508100740c1c1c2c0000c0c101c600058800c8c0c01c2d03a00c1e40d282d1000502d030040602005540b80c0914009a590500041d84600204240162580c071650240500d8003429005480300e80301c1000b050005001c0d0130140d9078081c0007214501e12450701c0d00401c807410018074800a8040c400d0381c040c0071200350305400c401181840312001c103e91404400c8030700851382461103900c0c0760125880400403000d545400804013004040d26401c5020400c070407507138600718400091500b1051381d050b0f180400454044c81c075416107045680780009400c1440d5504d9000848600703005112000501640c00710300f03038058501d003035000301301094400c0c0b0070100e2040b000f004642c043e03000410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 998923363 1250 998922113 998922143
    0x1090b01030516090e22080703141c020d2007290c0a0e030a08040608090a02060a05180402070b04290601030b06070203070b0c0d03061802071e0f 64
    0x6400307000c503e0350360950f840c890418648810300c0407020b0090403400100705002a01e00d010f614142c1a078545a20a509040e620b0107603040003054600342c40000038120b4400c00259107000c0f400d48500d944400d0b6604c0059480a0061402001b400d401c4c514a000140d64a2086000c2c602e40c0041c1c4031a6001c0c9901d540c81c1750314607811629001e0170b0036468075000490717070200b1550400a400f50550090504241815240c0580040d05d8030030000c204881840c40010280440b5520800d0950070003401c50051640d4403256001503001d01594025004204012811741100f8540141d21059024051f0007150384040d94205804401411a029620343c2005841c10080009040103084a06924401da0007540c03110303001140503248100c00d0560017042404110050b07a0706110680040c4008003201c1c2e510500803014a0406c000341031040300f0306182502c2000300c200040c0800c3c100403241440143d0717443c140c1c6048420809042c14100c5525500d0700e0314020001000c44045015000751100602005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 998924613 1250 998923363 998923381
    0xc04050103020604061b0503030c1b0a0f02040c170408070c05100504050402090f031015060e0303030118091208010305010b040608212205090606040609060503040309030b01090b010305 81
    0x14080c88000d40040081108228803071050021b0081c4640602034000b01120b547c941a280d0b400944882c01c100c030000503e0301d091140408c0e0100402030b542c02404508203961103510408a09520103402582c952090030600d900c107038007030086040d00d485541c80d903040c2400c00000c10f8104c3c26044072084141c47c804105481d01d0002e100400e030041c1d035503510b45410903042c04069000007428540001541d0702242850381c040c000707103104030302c9000700240607455240141940b80700c0e58001d40a210500c004800740d614040b0480341910f90f070b6084010381d940c0c0040024010f20701d00002500d0004212500f4540ea64482d06940c107e0303024500920076883c40c07208000444541e4410024194880100c0071248145440090b5154005807001d80c1407a04c9014480d082c8a64585210707500b940c498000d000502e0322003482c9070022425a5000e00b0a41030001c0540b4523000c0740103040500902200003410141724045480140d0783c45803e0103025655a164000a085040302d1203010900341400940b41c10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 998925863 1250 998924613 998924621
    0x90d0c09051e1504140705130f350d1e020c0612060a05091021120815060403150f0908040618090e0f0f19171b0c030c04 53
    0x2c0c48400d06400d4036000e11400d803205030800a03075001502c179450568a105408003641c459080d5846040e80d9484445034915048415041782041c014031035420b02c411880302444001000c014110301c6005800c2004503588140b40c4802000d051203070119100e0401d41c0000c0141b0001c07040c0d130b41042400200c02050b601c038600c1381c0d40140c01441c1030210400c825403d5900703507040000a40301110389a1074101092600070203d40710800b4003510a820080503204240112002d00403881060b0300d520b0554030a42040e2041c8004d804014480c00480d13100042071251241030900201034560b590303a00d1500da82456810b038501203503945851401c0304040d28501501f142a9440701100789403904220003076505c928542d81d007407800c81039503030046100e00700c9100389000f80d890700000341094464540914608040366487c90500d420080a020a584042048101140d44220b60610780800a007203481103009421031282140c0c1079400c802d9400c41c001c5109a0586001e83c140c560084a210911040e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 998927113 1250 998925863 998925901
    0x203070e010b0a050a0302190306050111060606160218040b01030303112803020c0708060103020901050a0e132d0c0f03080d050402060903030c0c0f091e0903090d0c0905 74
    0x107042c100444140540304500410b0f1030744490400604260041d40088041008000c090011035035844c0c00340400d40c0c200c607400c011220320700000c0c05a407408801040307143c014480c140e1805000e09845400b15524090078241000e44901c6920240c0b4003410b0550404c40288000d501181c5440103002086c40c1010440f54040041300401c00c070300b20080304003d40c00e6002c90891041560038030074856004000d00c0580e00820240c0000d264650550040040e08001a48098818100b207401040fa00780700560746a403140c0090800d4140d6191810901911452581c207505041e80c2c11120310020905034a21140743c900a41c000d5034255201e5103110100e00c07660001400d406418004c08000c120f040d08407903400762000c0d04140c100101c1901007455900054941b2045400901545d01142880200310410040841d000030b414201800c0da080780254400001c00c41c1c9607a40009421000104200e4000440c00782090300c0000703450074101141c000e070307011700d2110310b04110118440f040d040c6685054 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 998928363 1250 998927113 998927129
    0xd0f0b130b060f0f1503160306050102120d0f020708030f1b0738010e09070302011d010908100218040923103204120c080408010c020a0203070e01 64
    0x26441d00c008004031034580a90495001640c5444a0b440381c817240c01001595a60203807044e26420104840a40d80f0f0240314000c0405180070010403240ea13000a00d00a04000ca84205990f540c6554404014041100081054500006003030041202c1007004520419070344040c000c050716449103001546a841000f00b05604003030020401042a414600043e258080e48002484032040c104540c0346020003908090500503500420060b40c0a02d0752a0b40441d800c000b40038040d0840d40041d01c83d9a082c8074000d00d140818400320016401407002d1805442940100d071111401480014043e41c829154200d004102e00a160000d0519000c1e1400581c1e02201a000c1840038801001b0307254544840c03c00385101e9400c5002604455100c0c2c0702010f5040340800c05440e001151f180e48080715a500c510410744210100070208003607403516007c040c414500150003503150b042080c1d042c080c0e600111055441e20b1081c014094000a2581055200303501345d070301e4030380d5600205656050920800350 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 998929613 1250 998928363 998928383
    0x17030c011803320c0a051005010509130b0403140702220c03090f1e0b0703050402182502030c01020c01150b03160e0a030b09071806120219050d0f0b13 66
    0x21514000019180c0000f07407508a4171810925103030380340350915220410600316034500c010f103ca0b0508102195025800e14044a0000d580c2e544260340c2000c0200003804200060400395013840e1a403040340e003095002089a01d40c4440318a000003011401000b40c240e0500d40003051600b18002d01032003000c1034220264030440c2c1220b865840b00340756001620b03c3d041c1002d95050b40022004252a8000c07605581c0004e13503807070188107100f0200340d484400354042c2060010450b20070040d40038206034500d540000070f21359031140026482d601400d80700540c1940040b0741e120b034070081507002c43c200b122015682d044041d5a040c00f42c007a44000c0c0c46004c081c0d9113518110304440d0040d900c4140304a0080c3c803540c980c42e6a5200c4104403001603962090795000802c080000030f00e9034244203c51055198104921454030000d0602c451903410003e000b030b03100301042500e10701c6509500d4000c2101a00c10300015019180040380140402400c03210351038400e0125012140c403028080149501c944080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 998930863 1250 998929613 998929697
    0x9190602030714030c0c0105011406070f02030c0a090b0411090a061409040603140f161205030415090303090b0405090f1314010b040b03011517030c011803 68
    0x2102030361000342444248551001c0203d101c0c50f00340c0c011442500c0c0185840e444510016285003520b00c10f80c44541c01242c0940c038080c2c0c40d6169400c481005070b11a050100c03007800c91010a003440b42c447d1846520001c5906c00195000854001c004143c00444003000042c050080d1104a4001e0244440c2c0152006205020a5000d02d0321101d00000000b1820b0800c4c0d080000a0f0503a07606800403160700095441e1016488420000c140781d0f00b2841020b08040344410b001d06c0d0554146128041005035075040c94400c0c40024021240036010000d584000b2410301d8001400114451004a001904a010008058545005583c01c0d40c0340102902e40507280d8042004541c80064510400f64010810b680005000314014031440382d460b1740045441804041000101c801d294a0f20b404ae9040420082402507051141e03426038030071030550025690101c04007072035400307000c203a212150b19140c207903140c1001d820b210700c060742c0c070a5403642c00c080031080110031000d61802c040043e07801001049 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 998932113 1250 998930863 998930873
    0x3040603143303120d1a130b15070f02120f03030c03190606020714031b150d11032e0603180506010906090b06040305030702101709010c080919 63
    0x182e400e026451140d40704071080303030700090805990b1814035801d2000040c142c00300400b140140d46080111400c004007514881c030125404030b4402a004010035980d10010155554a026048140003482d12032a12181c140c03910040c5043c0c154010b0b44140666459650450303000506d01303400314001c201450543d200d02d135042207103820240c07880c48803542141104144403002d1060900404c01340d401800340300d241081c3c41c1c10724010a07100c107009800c504a020400500358030380400300030055540e000010038400a1000364029000c0308a981414003010010011400300507600416520b07002104494402402c1c4c203888401c40041403045800000800c0024029844601042c0030f0843c1c00d1441111750303803a00c0c04c0003026041005103a039181c10510826500d889450020f9405942c62840e160030358846603980c0c050014000d10920f200300200140724451003502c80601403c51484696082040a90303010b440044888070018185100141042e2000919040302084c441041405000103881e6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 998933363 1250 998932113 998932171
    0x90c0e0408190909020a0801060806040e0c0922030905041107030c020d060f0e101b050d05060d060204061d0415030602180918010c050403080d05060d050105090304060314 75
    0x302d0814005600307400240d551042c0001c0100f1100c0c1d03960307401e8541c10300602400c0c0110280c403490284e407501c40c5800d88040001004d507028081141d694805607508101c8444000040400040e1a514100140105038000d0701c01e00179150101e0b030070710251901d800d00c140c0d24001c00f24050001601412020b025003040c60022055500805001ca040808500850150b60f02e48114442680c024503141087c0351003445050000300c000c01c0c2c003066818803058010320902490003000c042d07660f14004104070303582e07901070700c041294002c005545480d59040080d0241403151450001c201d8400340303a6080b40b6161046040c0f114130581e12002c0d0300c0c1591a100001e40004480c50304d0030381d04620305041541c1c0d140100d889201034140104600000080386030070b4a200c00f146c20248001448240006450746081e40c0741624a2203001402c5d60b2041c002402e2007a0300c20000d44254030301400c0c0464110084010010b07034003280c50520002480440820341c0203403c80d00700e5290203100503000f610002403a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 998934613 1250 998933363 998933407
    0x220825030f14011a2103030105150d050c0d0f0b011e05090306010f15020f03090112020d052a04080307020907141303030906020d090308030702011103040501090c0e0408 74
    0x94460050024104003402c4907070044d5074003240704840d19419158076142d01c00b4006a280709190412019003d08490303aa800107002d02840b40c000702191200c498404d205868584032003250610442c148544000c49a030b0204c4014039140781002840300300400f55001d61500c3c400103a40d00895a42c1d00201c407070400381103051f4401005001c010041c0d80f0713603003004500e001c0c00c03140c801d000c501850311140c805040780c51100c6406641003c25203001c0544044182c882c07803582030030719001942070760300e001c002807165210004841e4034207024040d0035072140441c903414007541180d140d4841e0103000341444600403885040f400c0d074402c003c00310060502c2040c288e004010707030514000213118000000c10075001605a02012018660204181580f0080601c003d0680340060094080401e41c014600d601900015040210000206010364400d42c008103028640494047d20f900301481c205003e003030038400543d4001c4c00c8060208400c1c003118885070085501c1b00805290100001d040290107003244 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 998935863 1250 998934613 998934623
    0x70f2603060f1c380708072303060d12080a0e07030506010506090f090106050a0e01030b010503070c080d18020306091f0f1806090b0f2406220825030f 66
    0x1078407102500c0f21552010700c80d504c07509826000d1410a03401001d501008200c24200720150700c0607100301c0c0e00b8540264800c40314008141d640c3d910b4070702154990030340c05001840341c1d03c00304240707062580c8492268052006548140149200705881d40c4d650000d070b00029110b030704203200400451501c00000d0049040240c003608100007582d0005410740001da1108012410001c1d04801c210750000c00e2501080090030100040080d070760000f44540801030021084c0b1000c442c12800303002044041d1007503a140d000c018400442d16002c0005031400d030394000c07030007441640b0210300d03081030226140c0908810426002c108907901c070300b4600648960042c88038080c0d5103c402c0648981e0360024402824040c180105d810703245842d200440801c014001010b21425409106603012900760005450201441c034101544a40c80012074a100c2c1c0c00c01411100880100808505807960240b411a103d241c00c0e03415030740c013528807000000c0071108110a0030040391014000200031080c0c000c090350042c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 998937113 1250 998935863 998935913
    0x21190203011b02070e01050405040b0601110c0a1e08032805162a030503031504060510030509060c0a090b0c0a1a091e03070f2603060f1c 60
    0x70907a40510b040000700d240c00680150710184a446000703e01c4074010902500c00b001245800e86500d01e0078003019108504000045503400042d220801c841381152100410300140c141e501c03500405000c000c2c10050003441c107087c5000550a6021068413101c00c1d81d0f850900140c100300c04441495040c1c2d0400c1020322034140081c200380b00d1395010120240d0b214024008040d00c4206180c12103040c20328940166807002d2600380006400842074a030000c2189480c02040b050320f81c0014086c0501380c1105400881e148582050303941d06400640c0291146020b4448540b56000d403131030180b00e03180e00b400c08903640c0f0004001d141900401403900b60090000d40d4049102541c0d1400e0b03854681303180000c410010000c1c40f02c0d400d001e100107002c2d5210b80080c400351020780d40c411500c902030418090030510032a0b0140d0140401d40040000c4007507000d4841409485026180e00075410030350b5050f01030140742e0350803107050030a540300c074040d03400510b07518580a02c40d0b034500540c0030750078100c8960f00d550 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 998938363 1250 998937113 998937131
    0x5060601050919081b040203040c060806040e01090b150901030507050105031005030109060b031c21021605070e01050607260f0703030902130203011d06060f03010e04022119020301 79
    0xb101c3e000314058414580580100900b00d00b8520460f61060f9450b4400c034410814000059541010305044400d40c1c00c0101042c0d0f1000f0008008110f0001c2400d40b9500f4040700404100701c1e0a140d1344074420f441c001c80035402c50b42c0c0c1880910305003404010542c2d804000c09201c15800303031001c3d50b070103c2c07152107410805071907901107402c0d6a00d620048500c1602c030064084549001e001003000d80d040801c610180b0780f50014002d0040c45002500f1000d0808001c09036140c0c0d000750122050000c0c00c0321940300a5035a03240180e80c40d000c51244100700402c01d000401c203454200d084450083c1c208114410ba8490401308002400d070802c4c050307030032103010020f0f207000c00d80c610003500b021406070314000360752002c50060040190001e800c90042d944104014040f40c03c030103804001140782c03031851550315910400031070104d1240121400755076401000004085c8024310700a481140f00351094503c1c091a8041d003180d041144014081d04d40211014101400d240d0304080c07021800100007164200b4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 998939613 1250 998938363 998938399
    0xa0e060d080f070c0e091209010903020607060605040c05030108070e010608041e05070801140609040c15030b21010b10020d03240b03011e030302030904050601030b0a260109050606010509 82
    0x2810b505c041040c4000b41c04101c02d454003409110140e1703410b100344d24503028203140024121022404000c0c07103050003261075410b100c050b901080150030013400400c800f07240740701d000c1e0aa41092040c3e0b5454400c00c0000b02d026201e403592039048540c41d0311140c680d42c40d140e56088601000d1a03448041c2610f2014a0011840401c0078900400d041400001c01901c0c4076900700b1803407402408103004003092000e00002660560b912001ca508486198040802e2103400300c020380524142640d00c1408542c040001c111001c6180e410100c0c0e480003040315403000000e100e036a012906404015801c03664252100a0080d004040141e16030b00220101c511454200031380382e000c41d0070803e4241d001200602003031540c1442e801096014003200180c0746d1031075900030741c1ca00c1059000c501403511003010401c02e90090f00900f0f198071000301200300b01a26020a05813551038038404006130420a40075100070101885000740b107580007005098107a54140040d5820742c00000865000051000c01c01d01802c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 998940863 1250 998939613 998939633
    0xf051510022808090405070503060f03061005010f021c0f0e0405041104050c04030212030a0207051f0516021201050610030608030d0902030a02060a030605010801230909030409060609050a0e060d080f07 88
    0x24040c1c4590307441e42440e1040c8214bd41d805012580658020814455445031300b41d00c81d000c5030401d2806180100b0441400c80c242290707a8802004108441c00d075038042a000540c0400190040e62004c1403039018500304410f840e4162030180c4030003014071604e509802e10b608011f81c00130a40304494a0240d82c1c0c0d02065038868288140110307908040b03070f0aa07100d98140180e02c01040221003800f426024101d00030070030000c0816400034004001026220446600d290880030782e002448600c0c03d000b0083c60501a20080300e90f144911329440301d25000c5d42c001e104680c141c4c2c0c0703120b0065041040785005500204500300003a0f90601c40d034452140144d440e07d004100304a442c1d500456030714038100c00500003100c1038101d0b440f01280c1240b4070701c160606030341d01c0000300c40072100445251a9017001908600c00c03a00b1210300c07941403c0010a016030000500c008a500075218030580907903404076035041c035406495441c0d010700034602d0900841c07001800b4041000d401c461141c9400701c05d5860000407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 998942113 1250 998940863 998940871
    0x4062910111002070c05040e0303130204090c180b03010516081b03090d030e010b130c210209120c03070303080c041e05010f0e10120f051510022808090405 68
    0xc0b80c00040325020042405c080c2e000130a0241c07404d004000f0000e06640d220f005c020420b014820310850a00b041d5034441c1c02c0751004d260440c03020b0346096261200050600c017010302484545007070900340029428141304040c807a0028520301140020401002c80321250080d003d1450140d02c4450a121700400724010b50080184000400d0062071a00000c0e054880c02d602c1c00c1240d03494809082015183c079003403030383c205800083c0058148443d05054681c600c488001d0b8244401c03140e4031982529456000b03040440c0f0855208903d1501706450079995030040007019016004104100000b0f030240520030b801c0700030104c0c0181000d0f12440b111403002b0360f040010881c0c0660800410055811040c1c2e0070203100289005500c0c14060342c00310f800d04054514860400200c0941001e000c52190302070001840280c2062205040c0404070088041c0c54400345803041001c42c140391242c0c0d00000700304100c20808103421000c07140031820120f022002c01c60585082030b0070041c40a0664070b0303105007882 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 998943363 1250 998942113 998942143
    0x220c110d0f030e10150e0105090c03090a0b10050f0a03020a0b1c14061c0b04031d0a0306150b0a08010b070606080115090b03010903080115020304030203150406291011 73
    0x485e003030122160b40b404880d804081c407485d004006110366102e05401aa21880c04c02d04c2d6a92501c8004482d0729280c0e90a001401c107000364803e10243c441e9800640303040b990100c800b40d0076044285c0c100201c6175010300c0000c0d889409010100724085122019022140d0107442c4100d01e02d961180140c140d4541d03400b1441000200c01c1000103a181c030080c4041c00d041074601004444c50640c2c0e0300441c0c60400f50001d010f0048126900070107680342181081015000b904000c02944c0d681f4142015104105425102004810000c10914a104292802600d03540c0c1c0342c0b0348991804180030041d5001800a503204e6803074140204000b1b20034041d03d1421991455400d40703243c41c0000c40c0040b2020200e182c2d03c282d0405148201080e40020054159015007400045500000788140d213540f05c3c41e80020740500a500c803200003c03820700440ca11842c050641805001418521081c1100d0703001074080310004001c0c292811801c10080c0c150400210342801c810000c81c00020524103221a01140b40c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 998944613 1250 998943363 998943371
    0xb0a0b03070909150606022e020706020c0f2808070c0b0c10020f0d2c030a0314130809031015051903080f030a0b220c110d0f030e10 58
    0x420000c41480c0104070441c4213008112480c00d11030001d4035245040c2c40001103400301508908a2800031200011000030f51108564030207443c40d241e0040c0d0400c01a0410500551640e564a010301003082c42503070622501d21008030303d50840700b07101c8090741c0000703540c2010240004400a400c0100420240058003002a00c4018041085182007a040d0320030405600620131302d0305d280011000d89000588104000c202c00c09800c0c42e20714400d5181d49600c0034031141c0701d80c0e901840b03800f1005000c030010559080c4411015504003840b1032405464190380c1d03044540142c0d0100c2d0864020345003a0740f004060f20385580c8120a0102960102d41e400100515110400c200925080340c1c035440040c400d10082c08201c1c51a02d5203022801b840080d000780c80000400103603811485e5001000114004040c01c1d844c90355014084102c02030794a01001c0c40d860940d005c04034038010444000404000001003a52503e004001c551042c0f04a1000c424503840b0340c95034444000901243c2040061040001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 998945863 1250 998944613 998944631
    0x28020a05121015110f030d021228090501140106091d040c06140409140105011b0b04020f0d0f080a140c03040b070c120c0f0801180b0a0b030709 63
    0x25280c21000b0704003a41c6451a12030401285045006800a81002e07040c8000d9102c1d024000e01d0602d045655082d10310b0000149400e4980090342c090a440ba203051460711050740c8425606020030408140c654952155500a102052454202201030351003607001044500401c5c058aa541d1403e80080c40071643c00b15080c010f0340e644503060300351408000800256810203445150303103540c25000d40d0741007185581000c107044441508130f6004040020040109203882c0c016522280005e000392800600078100034503107e18058000003002d9000f0316408641c2d02c0d00d60800013500c3c219070a45401024052116021400071500d004010b03000c0d1441551b40e03114003100401000d04825225845481848403448291001041c0c0301521002a007075507a40354070382401d00c4460241d0f8003184003008422440c130b0811828005045c1210401c12100c1c03402a2620f20241c01d032603080031221543d4003408460404034060a064a030403480d120f43c00610302c0000c0c0b000c40d080a000b40c01c00c8081607100d00e40c02c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 998947113 1250 998945863 998945887
    0x8010821041e05121504140f060c030108060106170f0a0e0a0503030118021608090112051f06020309030c06031009050708040b010e04080702131104121a04020928020a05 74
    0x81c9003a2290b40003078135040c1c0c178200024500c2c1ea0041c10242002d90000c040c42031045e02040070368410b01c200000c17252985041c1501c0201c0398030034000d01c070203401040000079001c1d0296012030741140da01030201c2180d6076511000356102500800405882344c4808005401c0c21043c410f0103c10390181d0082c55603507060429554101803410410710b443c9104120150710305016034000c0707817040c2d44492226680c50114004031015080018040007440c5800c0078403842d5018104801103541c800706503c1b8101d070382c803036040e80c0700e004d403260054268111880304106450075600541e4800d152450310070015844e4442c0c0401c542c011075940020540368410b100c1408050241d450041c180b441003000c907460580c3d585501806042ca00034025400c8020b084400d10591b0002c0605050300c2500c15212075a0f607a01c1c801c03001c3d01c158252100802c0489210700a1070401e506032150ba000f618510403511007107d01ca14840400c0045903e41800c9800c800424a1900082250505030369415031a44042a10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 998948363 1250 998947113 998947129
    0x3080c0c1c0c0e06030307170f1303031116141309030801210c05040b031509070518010f15020f1204140909060a0b0a080a08070605060108010821041e05 67
    0x1003107040fa540c003002c00440b0741c1d00104848000340e21000d6001025094006034011b8040c4100c0126061404201918850b2901c0e52140490340030740e90b502e40000e142d4064584031070070400382d0015154110300500004140c140c5030340000402501340b00d01c00c00b00385031500403610782031412030001d800c50b401008885021100207003080c4210300c41e060000100c0d682c41d40702180d640700d01c0780100e0f103a94001d40382c0d680c14808410500c000f51402c1a90b07140c61003480e9181c1240e070064034480c11401d1146c0700550700c5040c80c5416550200e0307640c040365040c114286005d0b450040d4140451264030481030341c00c0424043c01540c4070a1500303080e104c0d414203484192550042c61100e0007440c3c02c504004c400000010550303006074080303038009101c02c00f030340220f00c0705051030f001240980f140b020355004102040c80140296406840d0400564460000464010400380328480071036014190304443c2c024010014100302c280c00007000c2c039059a40c03044890780314044410010000d40000100164201911 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 998949613 1250 998948363 998948369
    0xb09012108072a080c0108040c350721020303040f0905190b1c11040c050706060504090b071d120a060506032116060e0a060b0102150103080c0c1c0c 65
    0x28040c03c00702e082c5000b40380e8448001407480c0c10841c078900850300f4011a41c43c19006020070040c519115014803810540c4c003504440050783c0c034807a02d00d0f0b0201110010404100f83c521009100b05107402040400e150300c05200e2003640c0c540000c1100188c1e082d1040603002c0280708000340811540340c1046101c201c00940480c04440c2820040c0c00400c40d950308540808104120354030032020100c500740013030300394010010550413a152561681c0d441e40c000c40030740b4046104140902a6030b0f2034009210030340b4a14907009011003022000b080307505001d0f10b42241c0e000c1404840b860041c0030070000891b002403004014103650800c01480c824008a80156540820207400034268450b5280c1884808401144c070303000e02d81400314228019600303220030701900d1608810b0500890b4503a01840d42c0b201340d901801c40311a890043c0426403540003090901e006815443c6d0940b0603031071604c4070300082e440510650f50354082c1d15110341e800d42d00c09002c0c0c50113281070880700081c081c0b60300d40071686c020311760 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 998950863 1250 998949613 998949683
    0x9060f070201020a090b0d0603060501080c130b06030c0c011514011d0102061605120103060b0306250c110a030b0720030a110a060f1e0b0901210807 65
    0x10845004e034105a1010031030358103002c4036640d030307030601d101100600613504001c0203030b4205400000c500034002003805007000111203850020600000c81c0040701c0d181418241c008000b80005241041d140c4042d0500c000001c0c004112541d072213080003035080d80e5800a603050150140d02c564996400b010a15000b07000952900e43c003003504001070340da5100140b90000c02d0440c0a689083c03c3d00c110f041e140c00c11240b906000341540c582c0f81000280c054440014080e02c2180002180d40300e00080d648039420340e001d070210080300307040307400c071060680b07550f041e900c102509108034038985a2415031401140035001d842d01c5400e10103030007400c8007a250302c00340321311a0494502d080e12501100f103032813014031030800305c4c0c01e00240c58440e8146422081c001d4060707464103d01090084e9290001c00081700c0c0340c000580c06d00c501c0321441045404400c0c0040d00010002d00501c11f08543c8030000d549c4403c1c82210f19030790f00b160350301d00c100c1c0d0340281c40803640721074100c0050000c14540034030400174107445 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 998952113 1250 998950863 998950867
    0x10504082d06091c0c05030309070602150c04090f022a0115051f02070b0d0212011203200c040213080714151c020403050606010e150901030b03100509060f07020102 72
    0xc00b03c040c0e0f0311000d000000c0c94001504203070078078003409400e14441880d0701c801500d8903482d02c80400d03a21018944146005030082d89010b140f928015801e00d8800c140d0b4000580c28141442034003402480e03030310400814290f0821194141812000103030701c4154030301140054503280812110700303403000143c02030000011310308244410b07642e410305002c500c1c1c81d03000c041c03c110100c28005c900d0050315070710540c10a100054a00000501d1350000c203850741484070058580c0e6038603054001031601c00c200140000d040c508010a150702c03d800cac24030800300c060b0106c901241a2500140407a849506058581040400704014411041c4402c10081c6902c820320590504144003092030340186030300300f9555040c006403079a29008ad01c1c21054152090050071911152207141c500c0d51003400742c1e95540420250110704003a45007030381c866440c174810b0107801c80c1418030050056028103400b400c51980360041c54111107010001c1c0c0309661042552000070151401e02405160190300c002d040c80f811a401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 998953363 1250 998952113 998952121
    0x90610051203180607060c050d06140105090105070501060306050705090301050c03071b0303150e01030618020a14030102121312050a0518060c0d02030a090b09030a02090402010504082d06 82
    0x8010381c2c0500701541e10303003a00818200002800c510031000011b210b1840c00500c2c00081d42d200028003d0801d04030400c11060307864010200c0400300345c2507030074002a010040071034a540f182020f012014400c0f000400c034140c032580c1d00c034140c400c04c0f500c19000903c04500d0291034a800d006041c1c1214440f1443c514509010b6070041592a41c0758420600c818043c82c081c00b014820381c0100ea811106883d00f505075030315a440e404081c00203200c00d688581c10100070200c6e0300d02c0d40c14840c200941c002d000d0301c0d0341031419080c283c44501c00007500d54595424065265070350b5007001c41602c105245150403996602510300300140c4254a0561001c01a042c000704440c84e4026088540d4a810f2403002035400420b00005030742d42c45210303100c081c40d02500c10000b020f903800201401b01c100440d25407501031511285003000703502540344110f80c95403000c012a00541005800150002d0043c034056183c280c0f200e030220300d13042c1e81e40e180da00c0040e009400801011030180c102804039000034054103281c24 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 998954613 1250 998953363 998953399
    0x30a0306090e03090d15050109050a0b030d08180106090f0c020d050a05040302040b1302070c030308390903030f04050a0f03020306072d090e0106030504050304171509061005 76
    0x1403140f003136029014030340011051010380082401c007000740c1c05003030040c0c0da161001040600b00640c4d840e9603103400c0254a014516000c50300410810f000d64654843e41d44a15064442124903241c6500c155a0b940c00070500c0704c41805038a20104d28903102048849440400070714000c1080101d104010003402600c051070b901500f16400ca03601201c01150707003085a0001004044011602d0384424800900001007103480c0300128100e9000340c031041050b9484113185010403240b029041a0385000700f41041c0c224464490042201c4034502e441c60400d8050f101081c0703136038032411811522a4021030208224602400702101804074440b240380c7c42031440d03000c0303959840c0107000c440c00d00c000070000d880e01c9081d900010340d050b4400d40e098540e003001d685000d40205811701500260084c041c0000c5881802070250b01e00456100e0300035480c042c500001a0b41c4450250541c0280d402103080c140300c0c00e105141c809001b01820406041c0500342000c0c1410350003404e1740941d010301a05480510011 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 998955863 1250 998954613 998954617
    0x60a0e031803070902031504200d05100803040e01090509030702011704020103090602040f05090f0610081812030a230c090103020d05010e18012a1808030a0306090e03 73
    0x824074408925419411200080c100640c5400c2010514404800c00c61038034010503520303e50800a480070404465417040e490006010b0503850310070040c00b00700d0884885040e500c4550f000400740b45140c541034031044200c1c1158480d0748401c0301c0100742001030280311110701c901d0350030401c603000461407c4101d90028000700d40a1612a5000c901000080d0659000b50003940d1078960042045540303584451401c00e02c0704031401a9409100300710300103201046c0401008d40645001403a060070a1010340342280c5030240200b0009251400b5501d40c0b060890411008080e00710844009131245441d07041c23101120003120034203203482c00746220030b20f0a58030030740c401d60030038005141155102c01d07030801a0003a10403031074a0740d6030914040001030182e400d03016450285076014810781400036030502d214240c888a0000f0a4404110080703542c2101241a40c000680300381d050415090b81d40301c00710600d20b0080d03802184281c100040c0c0c403403056814800d960207450180c500b0802540880c0c81c1507624 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 998957113 1250 998955863 998955877
    0x1503100806041a0a0b0d030201020c010f06030b0606070321022710031a03031b15010b0d090f14010911012d03020f031014060306030307030c020f030f0f060a0e03 71
    0x810602044c3c2c400c49036001061200b401400420f815011450002d000750f00c15480501c3c2540780c0a01420825180d0250f40c044076000300d410030658035200200000b944c0010700c11014000c42641103411f00700c0c4c2034001c041c4007a01c00001600e800440f0341d4400354008824803803070020480310954405982d0305c001310480c0400c030b25001460451940140f8103d0700c498000c941d240c071010074810101071088001d1940451500165010144001c4055441010a00407503c00030b0007072144189410080c0c0c0162085401028100da80f0070300c03034071130404020040241310002c1e51200c03242024016600c0d0090703000c4900303103048101c01e101300382e40c481c0e81d01c0e240707103000c041e5a5480d43c03990f0000d100f0740507580c1203813001040319500d05100009255000d07030740c440d000314041142100e00203450810701340c1340300d594003801440c50444990b400700c500840c1800120390040f01403900e1a03060f20108210000030f1070580060815550b6828120315211004060714042820b142007031056403804020350b001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 998958363 1250 998957113 998957153
    0x15022d010534091206021c0537090f0209070f12050c0f0c1507050415031e0c02150a15030b0a0e1605100e030c1c02150310080604 57
    0x2c0c1a400034012201140300782d00c10b2001426070465441484030a500501c0b584402030085003004005c401885c0a0760811070b07194005442c101c008100d00c00700c09000054200004c240c2c412420b211084010448469410640d00b4280c100e59150860134070052107034100886052090041c03110b50001008a2a0b00c065034200c40e85510216040d4070b800810303100810050300b111521444841501c03980c400640e24040b01c12598130307000c07411050180088900b90313a01815864142900000190060a41c894200c034001124180709220500300d80320340c0b114513090f42d000e450300440d82a00d030100c420340500a0340b50f1030b00d06490300c903008200758004001c0320790081e10014988c0c2d904aa070b074010400008000018014601116441014050408107860080f2903045554200341411294104400d04240d096401903486040901c1c048940030240390422042490512141c0d0109040040e000041100214080184940340f25030b00d07242005014035000515561030586c90b042d024044158007040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 998959613 1250 998958363 998958451
    0xe03011104051e12010209011407020a06050c0c0d0c050315060306130503070803040606170a030906031e09082a0a02010c03090815181615022d0105 65
    0x7007600941c103d406403000d001041440c3c0000c680c1c031694041e5000781d400c640059980818840c0c0b4103445025102c40d95000390504c40c101d0704000c4d01b5541c952046448a00510130b03019464000d5aa00002e020328a00c5402c8002e43e01e031a040601d481d01e00402c48000005840008101460700c1c0080c4150344000348907680380a5101d00d0800504600c54590003801c111400001c100903c40d05400c0003040301da081800705828809460950f07101c136401a001000035200c000108100d5209402201c20541280b1060404014126616007250036900e0100d480c0c2a020584144840308200c401c10100d00503075000306640006481c0903115050508003d051050410308007042c10710a514100c080c1c12400c003103405801007403d4a000702c040850f846100b1507207801c405040d0500c0481d2005021700b10305250f80d6003900748551504034140c090319450443c40f50680a1084510444c1d0104004000301007400891504071016403d40700001c1a406031404400e040810500421705a0a080c04500100c0c1c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 998960863 1250 998959613 998959639
    0x51c080d061205030909010b030601021507090503010218090907050105030c0d06030b131202071412030d0216050d020105220c0e2d060306010515280e0301110405 71
    0x210041c141d0b40c00c00585041d115074450100300000000b031400400455208190341c0e41d51741189607a01c022901e007801038200c3d6101c200d030346660104d078903007041550400e00905612a00441e00326044460000300d502d408c0c000403034090400706152504401c920010b006883d04140018203144406040441c0030b4000166041540d2a50b91220000e1944122078958608001d403180341c4004080d8000c2d500161850312050905000042410464a0301c5440401c075800d0a03082007c801c02c4c6424207201c50100b0031880310304018902c010302d484002030b903040c00425840d05241e4504030307110444006580c940020710401c0c4609030071006814106130480d4800001c1c1c3d290181c154007459100440314000c0030284414114820003031007503100000d440340d480003106004040d05a506030352142d0990002c1005014509100c0800401200c5090055203884400340107030300d60741031141100c107415200301f125008440e072103620390182a10840090080c8240d0582c8941e0901ca08d00c100b42c821181404c0744 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 998962113 1250 998960863 998960887
    0x109240807031b080105010e0f090c09040f24080303101203020a05070602100e06040c03020114040e010b0304060f020c0c010f020f03040b03161d01083d051c08 70
    0x50884070103403031046540c42c00f4441016140480a00401d400720310f214500a20904041009820740b280050262230641c5500c500304131161300c011101500704e5214108880700b0f0800740120281c8400c050140c40b02c044440a44050881d01e64110b8482c1d41c20810511900301355032010350741940c0241d0384010400307141d4070f401e80c2740005000c0024294041c03204002050703500820300700348803e010304041c805503a04135503c075100c2404480040403001507030030078005548524108409140301070013461815480352000b42c1858002d0b44101590a400402c00041192500541c03070303a60f40302d242c02c0d400c240e215512240c0f1001a6141c0c6410400c02e8034001c14641d01c00c00841d8540c00b07411b02540ea45d180c81d964061300590040700c1c004240302207203004012583c4201f0f80030401030000140d10510f88650b1004603014840544541018031030b5009441410281d24040720004900300c854000f02d8904010802c40100e00341d0140d80b003040124156140c15410a40b224a2a580201e2095440b0851205 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 998963363 1250 998962113 998962121
    0x601051c02030616020c030703200d0b040b0603010b060301030b07120f0624020f0a15021c0b0a08240c0c06040c0f090c17070e040c02010209010924080703 68
    0x690b05100d00303414000300140302e605010400200da420382d01c0f620f08080078103585d1002d030300c002820260304000c16991080c201c410300c0b00f1641f0040000504580a840e110340802c0107a4040d04c026029005000b03252400744241c0742001310540b1081d00b1989140ca0b40030810200071701d0301c3c0510201a0307132605d0a101e168010001c2d01c0c0402c0d01001059118484208044000c00e034041006c0d036203c50041d210b80c00080d481d154036201034000c000c080866643c6003c608055a00ca000c020b40900107440d207407100140b0309844080301c1c44005240c0c2c00240400581805582c404540c80d0414001606800c0000020342c692983c403510720301080e00e503401c04045a11818003520210f0007400c2c280420442c1d20301d80d881c00c070307921084141c2420b41c80c0d40020b0200c4444659000c003044660212841c41d200000c202a800281401c1001c0e4120541c03010a050310707640d460f0400140d50005100c1c440c2c4da00041101c025100d80c240f05000078203a4644010070501800c24002440701c00c0d00064946072203508 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 998964613 1250 998963363 998963419
    0x50702010902030f0127110613030c09051e0903030105010c110409030206071d0108041e051f0f0e1203041704031a010b0a0210020a030213030c17030309060105 70
    0x204a480c0b169203413100a00031300b00b0304031100e080d12500d40815003042d07045450000290f040800b20740003443c808208002a8805e0300c3e040c4c0c113000070180010110340440300b070354014050000042801c0c500402c07030442030130154030840c01c4042c00c2c10038850442c4c000400e5a040da6801e00b02400e28003034900308440c013860f8100e5000d03881410b000403201019404076103903008a05641fa403541001d44202201c10f00e00c20066042e00083d1b05070005004a44072400c0015000c1c1c0401c0d1080d07040d4070130345525050410000c08070800702e5100316100140340180c46480e48a100800e000c0082c24000201642c5580d0310740d881103e40703680440441c040c04841c06040516034404098299165681d2030406405d5143c01c0280300d4250200303000240b032440c182c0071501581c20070782c082e01b0314400d0b58800d64001e402000700282016130a0001032940094200a40b020398050619103124078900450344036845411035110403948c1040c03040c00840080000c0090644134103c440311044407a082c60710100c0744030301c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 998965863 1250 998964613 998964619
    0x7180e070305010b09100815060402120a060515131a0c07030302060604050708044b02040507020c01120e030d0203040b0603011b0c11060705070602150106081306050702010902 77
    0x200d0000304002d415031111807004801d90315600b5a50700c460702520700014a11841030207810100e90802103681c0e00f01001e40c4280b00500041c00d091100c070b41018007150468512281c3c5a030b40304148810300d003891684170072141c4102064a0209000c040c882ca1402d05d1150300fa840c14004045d4007090004c209a51980c134962084640341070303803824001c4d542d41003030710000c0c069031420340803c0b845480380ea0202c0c030840c0c000910399038443d03c800345442103405030319203611901c204401e2040c0040c010802c0e4100d00122040841201d1041d00402c022594080c00b21015980001c0840f202660010024440c8021042c0300264541c0001202400d5100b4801d9203001903100000300070802807100340c1e640c01540143c00070000000030072140b503060360144400c1800f007824100c90b600012902c1046071007109010b030400342440030698036a8504081c0f0b80281001d6008006888a071242e00c0d072540b4010300061401080074144000c000380300201c0341c0c01c00b80550b51100d0000d0401d5001b500080c12169001e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 998967113 1250 998965863 998965873
    0x3160e030735010c0c02010f030f0e0d2006070c15021b0115080303130204060e01030503041e05100f0e0a030b090c2b03020a06090309050a051207180e 66
    0x9003010402100000020781111000340b50419103502c414850f000d500716041c0c454040c800c0654005650214003140380104041e160140d031250482c40740140c002e443c582070020300c56110700c0b41c40a88a03000c11028500004448603105d540b100c40010015040f404e90b0401c0c40c0503450500f41408940322894080c03800ca400010350066840703a0340d060304d04000505008020900885600c0742e800030051203400540d41c0144007044105640e100940c80701da10040001400982c0d4098107610f18000341e1081d140c6800229003003041408001c0002e5032000c84541d6142c00600707103400607040c890301c1c1c4003450410a03081500c0f03051030f00070840e103c40384800500607070500d0740da0b25080324500f504648c2c181d0300703014024644a00381000c4103043c03210ba1004030002c822440342c64015901c0c58131150103501318410080c420000c01c0e110710620740440d011303656001141e410b10086c00010140c50344030601425460f80da0501c82040850440e0a44082e68030492050159100c14006803803004000c041501803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 998968363 1250 998967113 998967149
    0x7020d08031e0903071e02010c060e0c0307080115060f14030a0e06040c061d010c0b1b0a0206060109050913120504050a08071e1a0a12050412021203160e0307 69
    0x1c0007000e03140385c0e031080d510003486445050244507082ca07020030081c0440c40d0b018050001403420340007030a1001030038040b03505040ca07180000c0d14081701c07a40310304000e035510b03010300880748003d0840c40080c2c0a07a003401c0103810185038005203c5454407000740c4410402001180c0c4180450704950520030401c0102e9110b070405080c98a40d0350128800c0c5000710f1001007029410000010032245207480503111a00c0130b8030a5211000712107030080c215107400064807146040034007003101a240d074404950007021103140ca00d0002d095040c00c0c1e00554400d01e42c68081151300c5840304112881d40c1da0007440b8140960b1200400d0759240141d0304001d0744007600c0303200800c40c008000703880002c1b0780d0b010500f01c40b050002390f00c150719005280200080d07008051070980034401110000e004034000b501d040348400e8410402c1170100d80b4169000c9544410160f99800c2140d810030070188051465140da03495030030b010554014424a400f640c1d400d1240c0110607040540d000e0080c500100a4600403643c5584 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 998969613 1250 998968363 998968381
    0xb04030c02150a0f1809150e040c030b0105030a02090a090303091509060b2e020a02190617070219020112050a0e0f010605032821120207020d08031e 65
    0x44580000b52035a82094200c41c81445c0d89911400c0409025400600380490301015202c3e5600803a0281c81c0b0300b10005840342106452032180740203008418580d800c1d40b070051001003040c3d1059120707a0002400790003580d01c94040980004100e1350010700d0016918060780540302d0b154028000004141c02c4400c840000c0d001080b0440c4290300800910000108020140d008082008642424148090b9940074407031348440643c3e03a140119400d140c00ca50000346c40d501d110285100030340e848142048038607080340319104130801364400c001d0306280440000396140500180010b80c0080c881044041da4028081c4e92003802070741201340111314089051901415003000b40c04034901c51039003801c882a0062203104183d40005002e80400d520705400e00301405203802c4450308400031480c0c0400050018201407012100500380d01d88160701041c0c025003141c0c203640b0150354040c01004174100598a140c5030400b80c40e44031249548070b0303c6041d020620074801100c4603c0300c001d45410b10032840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 998970863 1250 998969613 998969617
    0x21b010c180501030912080c040f180f02090f060f120c030f010501050406020d18120609050d140f0309030c16050a090606020d03091e03030b040506060c0a0b04030c0215 74
    0x3100480d81c00c1c085652140110120f540d084409880442100b00e1440e00781d2040d0400703500020b0001c90941456110385941500d10043d5000c00350140440400208590b118020300c0303031809405034218100034285011800394607501700010710a0500045080c03c0d1041c54081d6000e41140c65405901481c003e136114103240c0c81aa14428000160000002e407588030f40c0840e030544109602822401203151016600e40c6240f5007a02e035440701c03846021910b801c401c2205c0121900814010030300641c0350030803078201501081c8030310400220f007081d0b462102c500030444401d200316200850740d9550b0302c03464508500620100910f0350203400c071b00e039102c1860324184a0a8a804540340f030b0605903118022811a416803040b4000344e00a80007650700b60b0300991119212502031407110000e82c44000c506416007141c004102e0200e40d46807003800381d9040605c6240c0e485503080c1c50851616030500d034881c0d1b0b6214140720041000c0f5080c1c0000e420544599200003c940c0e01400708a48a0348030f160340044d035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 998972113 1250 998970863 998970887
    0x71d100e1c081c11070303021612020d08070305010b070201080a090b0f040b01091512031404060207090501080118080d140703020a080906060109260303070804150501050102030409021b010c 83
    0xb00c1910420b41c4200c0c01c4a2007603000030540d00a00501c5d09250390303400d9019411603040400820039000c0c070300000c98080740a8040401c220740c068990554001c9000c3c0600c80b014208400305031130400103110101036082110b08007502401d000401d40e0758101c4840280034205002003103030307110300d0502c082e0015480101d4017492144500c600721381c0c1c0343c181d14401c486549000d2905000b07903a078100401c0d04903041d070401e01c80c000d140611010383d0544100c81c0d203503c41d80c0090b00503030211604101100702403007400d01515443c8000e00c02080c100b4504080000700c1e0030040c11040b40041c042000c2c048a500042e141038540100b0403180c545003001070003c0d003101c0c4104001c100c02c400024cc02c01c00c08151980300320310584801c401e0a040c03c00324880c4654030b0035000741c441000050203140500c2003015520840140d520b1002c907142c5032403c070040448040c0803203007860a1100500c00d03aa0080300707980c1070365170398640141c458040401e1880703240040300d1202425464400340d5132085030300c41c100e0400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 998973363 1250 998972113 998972137
    0x30a140927090c06031303030b1f02012f030907090603060504030f0c050d1b020319050f0303040c0e06130e2b020a060908070b0f071d100e1c08 63
    0x25960b20789190300e845480031201564070034020000a01d6203084814107a400d00d01074a40020a1803600b00170a40e41c035510b00780da817075410031070451140c81642402002440070000c013020b4180d408941d41c3e4803034100d0040301442030201c0400010008182084084020f2000c41e4040c04925900e04028000300800c1c0d4098001804400101c034085000f114825501c40c0c0c00703001000802104c110884844901d00115645010110365240c00340c0c1d0200809201c141d480380b03100440310103a10b011850440720b80c2061802d80c1040c4100800f2a117810258011a403e425a058007981c1d544005000c0740c58448241c85254944403203040039000018040f50103680c005040039040010079607206150400044c4a03005a01c045d8080e030000b0800e8110400346480382d0443c40c1001203655a40480d001c0c202c51406034109600c0c10020810790103145031221404075484400c042c1c102c0804901c51141c45031080e01400701c0115016141c1c0c41c0c8142c03601818007518800101c00ca85450030550550101031901d003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 998974613 1250 998973363 998973439
    0x20306010e092a1003150807142710030b0f1f0522060b0f1c0605010903240f0606090b030c070b0a2a110f030a1409 51
    0x1102c1440300010024662043c9002a00415040401c9a00004202c1d01ca00b050303110404e0129140710440c49030040c0c0200005021000c0c141003151039045010410b15100381007c042110000e107070006598070017000c800c070a884070ba5588030316240601c0c10394802064800807108008070204a0040d050042c11041b42003038000b81c841032045903070940d82c003e0341e82c00011048041c80100545074035034006444040c021910b281d484445c2e0f0f0303498008902c203110002000852203040c0d00f0f0040e0350f031000d081d0900108009400c050000b064003405010081440b0140829856482c2ca40003080c000040251424803400c1c42600081d070103002e042c8520000300d54104808940c241d20101076a102c0d85c14441c445040c00c83d0740c2c58003181c054020304612000c1d5a00c01e000c100041c0e15841c0d070448400350710102c49500031500402885082e64503a0944c1c56081404000740c3c1d40c00c0403045580c4081d041c0342c03441c0f0003418040c0800c0d542c810002d00682c0700c103d4032406001d480300c00e5079003078440c400a40369103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 998975863 1250 998974613 998974633
    0x20a140705150a02031f23031207030c0b071b0809030f0115050f09090d0c020a030b011d06060703120209060c1b04060807080604080a030e0102071104050c1804020a0c020306010e09 79
    0xf040c50030b00c0f030148203041c25000000031440d088001c83c0c4200100f00a00711082140e22250b01800395002240540000d11800912414442e2032110329800640030713f0a00a508843d9580722103240488500400403030000884811380e030b808108099015a101b0003c0041440c3c12100358104102885428003441003103c81400a1621509880c40350402c10040d010501050008036265840080c00726030200d201100800842d8000761114080c11002140c5c3d175960040c211103500b000d00041c1030b54070030801040740c100029030060075461044045100540c0303801c1c2c0240080c0050255085000051048030300c451800c441c0d20400b8512078209490411049450342089a160ba0311800345400d9035100001040001d100c0d4001842c89030240c2ca000030303011034080506820b90707214801c2a2034100c40d40059440a00e001d110b11030f0449420611a481c1c0009817018121400007110014410b541c04030b0b800840a0282d0242d54025a001b0156245581c40c3d0703c0c2c0201890040c0d440c1c0000d44940c803500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 998977113 1250 998975863 998975911
    0x61a010206060f090a0b0114030a0c02010b1c0308072a0209090703120810231005030105100809120403030206040516060816030b19030302010f020a140705150a0203 72
    0x10a50110000c3d010344020345c0c40d4503005001d451150300b0281045109820b091082d480c2e20b010314000c2c501e500300807800088500c002802c5d5036031194824440c000b28004640b4078040001e200e01003543c9401d00101d80d5486000541d51486100d0700c0031034480b00c0d540f90f40703000d907041c1e5100000d151084408450940703c0130551596942c41d800000c0c006010400710038140c50082012991018a02c920303080d40c0c6840b60311190019a1420314207a1075014030401410300d18000c4807881202105280a80c1158500703000601d591400c48214000d1012010102d0310004090040e401c200c1e0001540d20f0b981c42c2c2e60b02d402544c43e00304a6040d2814003614000c2101d03440d10900c15001c813140c0780c0e500344d0340d030716606146810b1070540f5500e8402e043ea6040419259103d00000c0c1c003500400520340320265281d4100a402e5500343ca04051440d88104080400076410000c032107608494500303041e49030b22052078291b10f0702d02c0341d19601c113100300e9103000c1001c000e14680003584260030b161410680c075100440c603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 998978363 1250 998977113 998977129
    0xf0a020118032f0a060c050d0c08090d031704031701090902130203060d06090c0510020c0901090c0507060624050702220b090a0507020105012907020409061a01020606 73
    0x8003c1c0040c00054000340c40d49500307050070106100403400350b0407101c0c4540004095000560040021130321125010040c0041400720001000315820805040f4280f40d9420800f4414404124841c800c0e03400f0f0f840500d4490700729400c40101c5001c0f19001420302c2d060140144111000b203a002c020004008180440c007405036407000740d405045620203410300c0300c2e402c020390001003c0070b4104040711304400202e0b105000701c0740903900440030001e20a080800b0700c108020265001e40c199440120003c0c0c20352602d002c00340c1192203040000422800902d011107d07032194903c068145070612201081c03070442c4042c1a408807103406a803000c1d045604909896500552402a600c2490f48030b070241c0d42d000441a00c0c02d00c9202d0000020192441000216110016114407034103507603400400000503024412b560140c51052148480b50b020707541e460032141c0114600814038600846c2c00390031500e4540005001030b41c031100074040c0b4450300c0060b04010740307111000341c010322442010031014280090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 998979613 1250 998978363 998978369
    0x3140d1a040b18010e25030501140a0515030402060415030b130b01050703030509160303020c0a170d030908040b1815031e0402150703081b03070503010e1302030f0a020118 75
    0x9890612a860405c940d50360000042020507003042101d1045482c0700c803100310031014907050b1070000d400e5042011000080102100a50082c81600014005c640e40c03110203400c0700c00b41110f05507580d0380d9440481c400c0d0080ea8445000d203804004120029601608455542001540c20136491004260b550b0107031241d0f020f9450219004100510100380b1a82007658401c80e86e2041b5240e50048100410280d1032943c420740040e0091000c50a030f40c030702110420001c010441250a0b41c10203d02440d4842003d0136800c420725a8407240790080103805001d40f002407107010400d0341c48040c07640d0b0710300c0d081c24180c0e901440394400141c02c07080f145c1000184e0b070080c841e100c00c0d2840740c515210030500000002d07000780d900c17150040e10503440354000c000515400b4803940d900d09050030000c0c1c050b564602801d851002d4040e040c000c2010543e03101c0192030443e104449030040684ad110072074070030ba12744100b01075058000c3c4202c86041080001c1c4d0b1002d003c0c07003a030340c03c04403401c0740d844071180c0a4a80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 998980863 1250 998979613 998979649
    0x120a0512071a04050c1504030b0105030f03250b01031415190e0a170c070b030106050a050a20010615081006030b1302070b0121020a0303140d1a040b 65
    0x858500380c4280b0054903401071040007112007801c2d40e0b40000d00c5100c84031100811075503000a003442082a420b543d140101416402400d144031416545500d0b80030f0160804000d60f903070492202ca0102c616142100c194004103c1d1049503104d0400710a0340740040703040340039485003000b00c0b072003002c000f0030840c81110304100d90044c1d141d0454000d40904040c0d0210001031162500d04004508502c11401040301d011424580e6801142025420011140d001c40307186082800100f2106410008540c41607801e883d1259075108000c0c414bd0b000c40152500308100810020300540da25015441003090b14410320340410900d032040c000f240c2c51082220303500c209850041c000c003c040d0080c0c00ac118185001803089040e6503144030000c00302e030050340c401c0c1d40c10b05180004001050b806510841c44150340801011001c007140c010581800803488000c0c20800c204810b1014800290142e50401541090602801100c030400d6034800c4602c0e540355101380d00d807030342504092070035018810500f00f0b01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 998982113 1250 998980863 998980883
    0x506090c090d020f01180b0901020c061305060d09060903030b040b10171506130f05060403020108040f0c080f06040b0709030b0c0a091d1e0c07060f020702120a051207 73
    0x3d40c244241000d2000f2100e0621000e641c0c580201801080c0e007002412a481d11503442d0794180000900e401421280e89000c0c03a0100640d01007000b00d01070000035540169081586d07600d150203072500030001064094a41d0b45841800410564540c102510a0204540034040010040104030b0702a41c040d15000200b8422140740300c09400c05102a58088107110f200780304000341001007409035100844008030244280d4050160003042d112380c0020300b4080c0c50722070805040d40e00107840424050000340c14017032104001d8040000612401d40681423040a80d841c00c10b107a0301d5240e48070401d613000c484040000c40001c00e01441501d0307800849070810011416600c903840d00d04040d41c0081048810049994008650a4200e40d940d04c50b0b410300f000313811440d03c1c210290707043d02c0c0f10081c20f4504c0110300006000c0110610001c2c2c49040ba001900020380c00744142c0740d10002d100b02e4900940001c40c0c900e680e540340c1404a04040300501540030340e41090041c1440c0c1c0d640d4412103500502110301c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 998983363 1250 998982113 998982139
    0x60906042d180f06060603050c0d0b03070f0b0714010e06040213060b120103140c0121150306090b130507090504030507060501080102040f050103021306030203040309090f0506090c09 80
    0x30019a002503607618100c00035401058149240e005800c821040d1060996500303207404020b584e10501d0300500f640e203070400c03c608060300c942d0b08030b10030000b0b03031030f0080c6d19440c95141658061143d80010712803180c0c0c0341e00450340d40c1c000d00c00f0780c0c12125082d20100040d20310701e151520306016440c50700b005c01c000380070a551a5400c1100310740400d07000b00085a0b41d20000701c0c01440c000000c3c410307031204071003d03405580343d407901141104489250080b281c1081602050698010b102c03183d42c440c01c54455400540000300c6da02c01440c0c3c1180910340104074600000501c10103500207425a40510503a9409076550744100b03525801640004040e68800c0e102080808070030380c40359410600c245002442c0a40c2910b40c82d060714000e0300418036596002034200400010048004010503082c00c0a40c20004503040f000c401c1c0006104820505800100040405108013650390281c03581c84010040c00408403801c000522044540380c3c01108080003017484440500151682d242c030050100304e007034030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 998984613 1250 998983363 998983421
    0xc041b0305130f050c100c0c0603020a030209060f0706050915010e0406091202010506011d13050a06050d030c0309050d08090111010f02040e06031c1409011b0b06090604 74
    0x7100800701000c81220b0052040040c42082041500e580540c0c0100b200303404041c02c0140107400d10041d08180107003505000b0016001c0700c005801c031003443c100141c40303209040c0240e01a01c184106594020300005211810700810009480c440e03000b40c0007049259503a90025654080b41501010f0403020303000100003c5103001c8181e5809841200007180f0380c0020b40d10700050100d042e64520150b5158001c20000d541d114107d00e00c400c22006c9080d81190760303500403c1e040c00c1c00e40526541140c51b0400a400784610390001030003084040d02c03482c0000114100103141601e150070407030004504400c00115407914007517030240f072500014041e1601040c400103441c05032510000c41115503c9040003004a4180d1014000403c64000704000b28a404000c250501071407070361900c2c49401404450940ba54010303040d034490012013622665903007195005a802d91565209121540501c4060108100000d00201e02030343e0300f90b030401001e80f200010482a42d5081a12200848902c121070310004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 998985863 1250 998984613 998984621
    0x150c08130203070f063b01111e030a0e10090e130206030a0218030a050c120a0c060e09070c0215090a05060304080a0f05040e0411060c07060305090c041b03 68
    0x5100a00f11852a0354407003401d60108070035808200402d5030260b0340f0114112045014003003c240220340402660041d9400490701c0c030000296041040c09440e4843c2c131603040002041d5001717a161091058603032980101d030359601103044900000c40f1440b00800a0818032100c8503908525140c01500c5400d00c600f036507a62000524a00a04400c2108140503031640c0000f103000366801000945d9410311041d0f40c3c1400028803013040d000780d001440c664041040410310001c1030104a4007140340a0440b6044c524020220340c001d001c5091111000540c0d941000800366038200079922401d855541b054241d89020035550302a40050423800c01e0800030421500410907140c005004201c815181c00102d0361a0b001203900701c07203800c00012141c520a80009807000c5514140c680740c4c1c40d00c3e06080f04001c207010041c0005000402c5203d5510ba035036604802d0b0754800d50300c102180d0f03015580d154000c001e8441511070844030300401104211a0425004440c84880c0188045200c0584450101c00030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 998987113 1250 998985863 998985901
    0x405152110241511030304150902011e0306300b180f010204050913170913051e010b040303020c13020c0a030507032a1403040510020a150c08 62
    0x84584181036241c003003080b0031581c1c05454101c420f94202e200c19100070307015214280c20101d1035402802040001401d110759481100107401004c2540c00b200d00c010780f00c82d2040c00c404941c0c1e51901d030b020203005625a11210807a0200030240c0e103202c588000c0140880c120003403810400d0414403805020811890350b260b003200d0100d00c006900380312281082c1c01c22004d0000702c440c6940000d0100b040f490305e02c0c00590490750309644143c1018071030399044500540180001980c410100b01e0030b41a6449161510700c50b4040c4d8810300c0149400c4031011951050307440000e1826183d00004610000e04805071006d480c3d05400030030342014504100010648116440c1414540800080072006018444084100e100c0c0e00c0341c1e512000e4070301d0003520040c4120310101c1d40900d1080d066201c0d000d902d5416070f03c41c2d0081c2405030301051180d100b9040d4455904916002400c11750590302090380000c03201101d50080da24074035854010107002082d691241d03c018000743c5180e012800622070040c12640d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 998988363 1250 998987113 998987141
    0x2191401030c090503100203041202060709090504230309010f110304031b0503010c1d0f011d12031602041406010806060c0f01060b0903010e01051b07020402090405152110 75
    0x10f5654490000f031400c038292a0507000240c0204c18407003044407104540c2419125070000c2c1c852881e000c1002030001440307108000704291100f0100d0280101d403510806007280101240509110340c000443d56a40015805400108240c5100707248a01c0340001d0104104690041d5281c1b82c40c589890f1100303d903006010881d5030b0b00c5180080d42d42e40034400e82030b410250342c55680c030210321074001d035490f12040e1a10901482c1383d803441c9015030ba070002d0480765004455800d03510902e10800450000380c450400241d583c03100064110110000382c010703000c1c55200b140c00380302915441030443c225000603601e060218444c800800d0755450100c01904607030310420f00f00c48404010a20550035601203a20032004610001404031803410203000b03044c4450103840090106082146014541c4104500c0521a29002042140855486030126070301110002e0042c0480d0030a0b58244070003022000440e0321800520081158440c5131a80304c60490b00d000c00a000c00644040c0114003421180f001d44507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 998989613 1250 998988363 998988377
    0x2e0603122c0f0f1201140c0a020a0b13020325090b09060607030c0b0f0708090a0b0a0c1b150e1b15040905041428060c020708150402191401030c 63
    0xf9031906003c00225000c2c00e400810094101d907800f1403400005401d481007040f04200b070080707580e000075205c45010752208900501c0e66946414451600030b0400013075040c000e00310214400c070762040d00929030341c20045182402c50754400122044501f000d0b002030f00506001e00050003454490054101e05009003072a04010640e075a4140c103810086a955644004c00d4050046280c0c0c403061081e480700d451401007806031019103a28a00c254018010fc0c03803151501900c2090a100f5650b196100e80036011000c80c00040d450315040c040900001d8840051070004d86104070302002a015a188602c80c00d0007403600c808009101c80d400394000702580c01b0000708000161000305104140c0f140e0f0091a140c1c0350300c1402d2681a003440896042c10803c0501c107800d6407021209403507021034259100000061401c031a41040e820119643d04c07a8401d4060300c508240412181000c0e6885035100300e034800f807101509042100500c6e0035008060149035121968483c035402648000220b10b804c0c24404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 998990863 1250 998989613 998989639
    0x80a02070b0c070603110a08040209060f19170c13090309050d0b0a0c090807050d0c030c060f030e010c080601051c02030108010c090510022e0603122c0f 67
    0x1403032944100b0005201d03901410003013040a90500c81c0c0000e1140d0415494078100551000524058007e04081d102d0300d50500030660350b9a4280c0f0315010010003800d1004407042c0c0307075801440002188298800031406080c000b24681004c24001c0449800810341490280f00048aa0040c06484400c9045c00700b84503021800f45c1d00e00002225031481140c82445c6490400c440900782d507507014404081c046041c00c20301c07500030042415002d40b94251081c080a00c3c0a0800302c0181d80e01c0c3e480908a064403a9007c84e1840d88609001c0d000c03d04e079182031060703120320b014090072600000003039000100210007003002c0798407450081c1010b2200350b0b810b41c4024038240c1401c049034820381c401d8106a65442644480b5600200c12200404081322190524501148040c3d1036034846602800c1d5010083c2c140307180c407800030132451240005003004200458580c50301c561940040080c4c0b4010441d4143e1840a40c544d91507210007801000802260400311001404032501c40d9551305907110700c92003524 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 998992113 1250 998990863 998990879
    0x301060306091a060a0b0a02011b020105010608010b04081906020714030417010e10020f0705010606022b120e030408151e040317071b0c080712020d080a0207 69
    0x220029601030380303000455400d43d1801e02e4102107800c05002103081241c003005030301d50701ca8000904503a000c01690355100a01d01040380109000348400f00c1482000c4150280d46505511440c107851a42c2c4558002d6601d5800f01056405035204450301d0b503100141d1401c01c640c1d6a10103105d514403d460250070701100d82e99405d00c05814204070100c551022804010f003103038203181c4440e007080060081020140d5650003648030403040050f140c8840c0c0014200620304441d4085401e2250004001c0000e20f455080094aa000f80040c07905da20101564000351910b40c01108010341010fa200c4040b09454150395038094041009030f002c1600040c0b1002400c40001d003d41000c09101c0c04a40302d00349800f4a5415203041c10307500c03101d450780c0c0c66000c010000383c000c42c0c0c910130a0f1001a010b2490750b58082c0c01c441f0700d46188a900c00b0107000381d0300c2c40104442c11544506540c0c1130740550302c03200d465038000ca40c1c000c0318a02c003039442000c0d0307490b1101103000040180072201e03861068030701240d101c6400d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 998993363 1250 998992113 998992121
    0x11a12070201051909201908030403120f0c0219090c031b0203070503040303120b041a04140925050a081011040f0b030a06030501051915060f0f030b0301 67
    0x2020150b51a4410840c00103110b013034011040c40c3c0d80808008550b1241c031440752882c04806e5002e251101718141400d10b64401809035166240009504805910740c641c4a8030b07604184421142070700d080b8201c0000c2805000b2007850040140d07640d00b66100c041e000c00c0302e44c200c2e02403020b40c83e0721022408505030704280900c9480d201e090300c0102e5190180787d01d001000d1704a500d40800c64109002c0d40d0700041d4040111001c494140c42d0102042001c1040c06005050101045900906d0201d800d02100039502c048105550225810402080303002180c0b080c0c1e1034100c456060540000c210410300502602c03507008040e4181e144400c0300e507116400700d240b41e946074002100b280e000315098041c210190059182d004487c2c1c2800d030034903103440401c80100d040c901900c01080384c048005801002107a104200441e0000000d0005090801d2146084444040c0b20f8500c1030401040030b00300072424805004071081076032000201c2d40f13503080440b00c4511445e8200105912045035440c41c1d036003401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 998994613 1250 998993363 998993371
    0x712030f15060206010801111b010b0a120618030923030109050c190e04080d091a091006031502031012061a010e030a1106132615011a12 60
    0x1d890510b0401c0d10281c42c2000c143c0c8480c50582c103084080400e50149015950b100c0144081aa108010340b900350380900080541c0355000800180c5c001124200884101c3c42c0b5401140c0400985281c00003008400d00301c1c1d0307406030104162000801414800055802944070380320290122130201d04e00007425030340104429600380d0700c0140c071010a07240440c0800101940303040070003441460469030b00107a55000308080c0c000f83c4081070301461007a10b600030ba0221948210700704509551901c0300d81004400b41d525030078521a840c0320540b038a0a900c9224103982d00541c0740302000c81810a5080071398401840c80307400c40d4075007400080d5a40c003141200c0e0744134841d40d4082003942e882d0084100ea4a000500241000000c4013008540e41b000f00b4510764850300030031901503a10304640815094419850200a801520b0f03c0014841c3e040c100280c0c404202c0c040a07005c0001865427059441003d0440c0000459490004202c41591240b0342058100b884400c1e5090003600200000f40c400d04071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 998995863 1250 998994613 998994641
    0xe06040c030b0c190f110102130f14090c0d0e0d020d030f140a051005030313031208041a060d02040c030207110a06050715060f1203120b060712030f 65
    0xc0c14000c11151652140d484034101804904000d07981c4a070303800300f82000c8051001e0001e0800800725451148a0105100c258940295600c9002c4030001c401510300740300d1550b50118225010418075100d1121000d00d01005000601c1c544440c020b66429a00540b500912280e40354442e144041003400310600d00d0500390058a1800d00400380a4291103a0314604c0c504030f49407002407000301031080c4060381c0005079410000307019500c0302a41140e40d80e494001c00c1d4948404038032b80040042c160440c0003030f2482003c0d4403800b4010514160340e0610140e400074145e107517640d40e0640001d10030004a40c408030080080401600d03035000318080781c038000e0016001a8000bc0e00005200781d00480710b086070f4054451b0781030356180080050031406074103070080140d203004c2c004141520300c035000300029150707041d120300c42c8560b6100011564000008201c010901d109100030829006115108242c200504080d113456859900c41101800c600c05403028140e480104404110181c402c04034555101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 998997113 1250 998995863 998995883
    0x3004230a0b041e05060d0209010c060e0a05100507051b07050612160807051b010e030a0807020f01111603180305011a1c0209060604030803040308101d0610030e0604 72
    0x224120001c3d4458455668020b20700300e5900700019100e180450b140e5156115006813a0a2124012038000000700b002411560506803a5001c0750f6001c0f60443c203141c814822903084800602114082e100100e0f07148000c5038091004000148018150780c5412044005582c51a91508009a100e40080201c03560f0080e401013040824402900c00c5040b0314840d0612419514010100500c148290a50300801d92900e01c5809407022003500510400f01c0389501740d07501c807805080300038a00342c01280c1110041c400c80001100d84603062103840301c0250b12002a40c500b41440010340003420300e49a080781005649050802031288807040d0101a500c58000410035900c2c2d50343d1000f80700942c004040c8a01e0766060b07400e86244841c040410b9981e4151910400e43c0c1e43e440c0094607900441d4806028454000101f100300350703000003001c0c49861090070340c051154031400e00940c24405003503840c665444981c003261705480c0c42c0e01e80610211041c0b07008110440910700003030418034180c07002c41d4800d80e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 998998363 1250 998997113 998997119
    0x1206010f0c05070b09041401030f05010c0f3203040c05090c040e040618080309070801060b03271e0102120a02120f0c1303053004230a0b04 61
    0x403100226503851194a00700d81d007001c45845483e01d400c001e109410450000046442140d1955000f100e01c58100c440300d009190303524101a00b500011080c202d42c00d5103800c58222a107030080c020940c1040c015501c00950b4100c12004007400c804140312180c03100300f4044c8100314040e2890040d4400d610a1200042d0a86808103002c0d00714000341810303140d104144028010805501c40640d07002d600030302c0c085841c45011302c00382c242103207a00010700300b104000100442c0000c001100c004540122008000f1242d1741c4607003007003900003511150300300c405038403680c034024281e42071441c0140701f07030016584000100322801882c0034416040000a94002c50f0708842c600d001110581e01140407041586080101c6008120f2200010700160080e00301d507010840a085003030640f0000041c40300e0704240c0039100d0821075940c015580c40c9605400a00e228402c0c50512200c0007000c41129801060a01c1e04152080c00b00522900c002c41d00080c40303005010708d690320b5400000c01011340d100501d80c0c81d41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 998999613 1250 998998363 998998367
    0x7151b081c061a070c08120315060702210114010f09110426030702090a06210b13080f0f0405030f0a05060103030e010e1002010c02011a10050c03040b120601 69
    0x9103005004100c1ca28064040102109508980f034502c2049074005503180348074901038000050a03000b0b50054880c1501508003017800740001d50240c201c000d29480340c08124410000c0a01c42c4200c0203402041a240160221140785016002805100004500355294600c1180f074400e0903840100c1c0c14202d0340c42003001d02c201e441206405036140780d013285424104194500c2c081b607100c1c54241c445811048000b421002032090b035442607401440061141403070498100682428055038240d500003400700c4500b13551400400520540c81140c07502580d99019214440a050803019a40807000b04624284011000002c140165051091540b0382d4240f006051402810700160403441e4003400c5070310041000000c2d100e04683c1d0519004841d03d010200407210014404104d41e04200b006801c90f00484c0c064100c4114082168020042c06102d481c0b0f44030901420070000e5006070b0141c1c40c07441c070f0070310a00c020030744240510308aa140c1343d0360702c0c10001150300c50002400700700c0003141809059a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 999000863 1250 998999613 998999647
    0x40f051e0c0412210315081b22020c011d06280209030109050105310809040e0d0201051009060e07080702190602210103030207151b08 59
    0x6003015408001a1801d407040340c449100e03500030b42c160004251840d40400c0881a082c000141007000c18402100f0900f0010b001743c450180404a541030152010440620024001498502840c01c1403445039011040c0880c003040e5120880c04519184c80300003640005000611803c0c01361030000030007071143d8498003080c907940d00c110b40c400c0e0005002c0c001e0305400215080c182c1c08081c001c01d000b0380100050f00d4000d00c280c400460301542881031660500c031041d841140305e041c8040c00b00000900b0f011060000c2c01080d9401b50140d841d00385000e0100790f07039001a043c280c0000c0d10024004524405103850301e0300e011503480060b9101c001b04041c250300043d0a20040c4a81a01404414104407a2402180f001084001002640c8001404151003080382d0140e00f400c148113610102c14904210002c0d50040d40c9044002001e802c0c605072000003085041d0480c1e4156010b440402d0a00307405030790701000301407010204a200c04603111424640c03c1c094110350f1040044581d0f503040080303140200303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 999002113 1250 999000863 999000901
    0x30601090c0807031a1c03110102031315090f0f032a11011211121e04080f0f19030f0501050922060606050301030201180312080c0702040f05 62
    0x52800c1c80101c1440030b40006105030884002d05002c00c00c402100304650b841d9100620460707021505440b000706445004148484640c0241d50324881ca250000d101c50a2b07200903101200e1000c0641c0c110408100f0118a02241c0c40c41080007080c00c845540704d40e85a02c1c0c898400750791415440d9840384c201074000002038140c000c0e402041000340c60440718800090601c2c0b00141c6a08680b0924144580c810b0700d200c03150b44070707501081000c0040d49412605a0b0061b010800c641c0d039041c004142410303402d408107841000788042801141d901c0d50b50703209480e00710800303074001402d0621803024903099100c041c0203000c1c014006000c08a485000c01800ea91914444104051400b8018095030719082c8219621600c8007602e0355500d81c1e6803101b40b41416075084094191454000081000d40d0302500550480303000340d803454181c0781c1100c0303445e44021181c071008002151503481c0c1c660b001d0240800c580d1011340702c1c60003428211507401180582e890700003a500483e65400c00c2100701c100c900341c2c594070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 999003363 1250 999002113 999002129
    0x1060f031101090e0402090115050904090b0601020c01090302060301091d030c100f05191e0203010e1503120406030b0105041e06110c1309052407081e15041514030601 73
    0x15421700c0c0d004205200c0040c0079804060010f901540c01c0280500308a075585407000d80100f02c1c00381c441c02c000c019040705580b0709005000b1040c0c130403400c1d8481c20303e50003a40d8000305a00d1035a4030b401800e41c000c140d4203080421203440360108009012090019081d40c0b11110040c02d0a0b01101101c00d0444104226084c429450003013070202c1d03007102c10500002100700342c10000e0310100842c1c202d011803100c080f222818900000c004644143c0c4148442e00403200c2c214562a83c810500070941c0b60303007003218110b001300c6090108001c018403a0308059010340042c1841031500c2e03101c082003052040300a1442d04076203010201000450f920110107051244840c014103002904100080d50000201110890705903c030508541030020030300c01e50720b0388817040450280110401115500d038241c12502c8501003500751001950035100c494900031950402d48103034545607901e909030a800300600b101e041c1c00079961000c07d074440095a2498010f4426030300303845d030b50011401c20545425816045954 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 999004613 1250 999003363 999003389
    0x1608060a020a020a121b20060c030d1109040603050d09170d080a020f0c0d0f0201140402090925050a09020c03030105090414030703171501091701060f03110109 70
    0x542582e01040c00074000d40d01407003e1194806481e002c580081d005220805203280d99031105c010044850240c1c0d600ea003891420342c10b021f00d600700704081402038078502c40e0f4a4204100340b0f4030900c681d44c8210304042400e10040d06245035440424121842ca40003256154441c80111810381e420048000090605401000004680c103020646522100e21003205008420300800c5541c802501a03030440041404465201c100f03007101950717038401461321000851540181d0307a100c140706001e010b080841070307450382001d41c503103a00f0f0051800008040001c0c1d801050040c05d600c038118210102941c1c0c0c8803102c018400d04010801c140748030701e94001c040603131040200300c94050380401641d0448008076101403481c0d40d2804c1c07224413030241c1e940300c004500000410b8410542c0000803044800700107269040c15a0340c40c00c006810341c008030341550220b1450001003000c58a80070050403082c6425001103403940c1d481903240c40c948034070342049070030780514080c0c0c50455a10030703203410044c000c92894203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 999005863 1250 999004613 999004627
    0x703050d121b1809270212101506080f0601052d0a0e030604020d0b07050d050c0d1b1d22050a0f060303080f0709081608060a02 56
    0x103940c40c504681850140420000705200d180d50560202c0d0356a1108044000080e00b8504010919900c102c030f821440380851201050052040c8180e400380c400301c500b840826454695100a100642c002c01c13a440a284a960701240000b0b101c240b038210103001001c6101030300f03000406144069500004100210030301000203a03c0c186800c190407180a080480d6203408085441d203d001c042003200082d0f08082100800d04006080248035980c03056079144045600402019184c0c4010748000e0360050201d01400041501c0c0403030740e50030122900b8940d28000f5900914410b4820440e8051254540802d050003000f0326070041d201d01a00c1880da49000c1d03881644042e003890071907989040e4108461129012039110682c00001405030080030707281080076280c0e03d00c040c24080380d140600d039080c140824100358030790007030708140c1341d15486900481d66440d030201800c501c001d01038030800003050400503010800380400c07a111014124030300070302c07810040c0b854602a03014040b079851a10400a070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 999007113 1250 999005863 999005873
    0x60501170c0d0b041e11190e042d080306031002090a0e1b03010806040c08010209010e0f0402040b03040b040308091216050f10020c060c0a0519111006170703 69
    0x19a40c00d43d00401a490740c0c1c4550070803071940c0c2050030b05800300301d00255010303060140040018903844021250142e008640b900940c1c00305441d8480c0454444000021600040100c0c6280102d8500910240d2009082c5001c1050700702c42000142d410480000030b01c401402d0603c00740344000c902d61003c0d403400d250040810760a48031449a03103045000d8801250244440141d003441880011062507140d586404100d0384800055804807a50000018001885041030091f5103d864050f156400c805100d03000b031042901e04e0421743c4c0d5010f07508000201c1c0640500001c1c0d80558040d0300101e010385068603010f0600ca0340545221517640c00f220b068031001c80d08104950604d585080f04103000c20310361400074500120740c618034101c1d0103142e90300100b540c007a5000d84290080342044030815101d140c1501150b101b40c80400000400402c1254510030351602c003107401e001d0710703c0d1111481e013280644905101002100c0c91180780c481d4070401c400c010b142d0102c4024059840079102440c61990b070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 999008363 1250 999007113 999007129
    0x920040b030406020d0204030614060306011505180d05010623060d0b030c04090b09160f1509030b0106090f0e062107050604081513150b0a050409060501170c 69
    0x34544000d000000020200f08040e010342d80c0f810041c51056403a29120302d44400607140300c03078000d01a2540c5200041d010300c0c0c005580d40c101c5600080450800ca030141048509901103c40d15207203405148040000d515800c3c03030000543e00400001a5085c01d120840140414881210300040c4002c50f00045a40e95082191f48550051a001a4000d00c80c8003190a02d60320107030450f842403600c21703000c051000112109115582807000d44041c1030241c4410040c2285600500c9010180d10b1020302810030b8a03150900301d41420705142d4240c42e540e40e600109010240c120000003480140100040000c04094030040c01c402450f10220f0701e004000310b03040030454500710081181065151010b59828081b080140070094042c03030b03650740c0340c1503144e039501d00075074070001030010700400511102100f01040d104507600c450310040d9034001001c20006000c4400d80c843d03100c07050702030004080c1d4941c865208414801c40c0040303070962400c00c480c903070195482452001030300005c02a0b000e550759050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 999009613 1250 999008363 999008369
    0xa0b090405070c050a15050703090b01031e080d09050c1203161407060c110f100804060204090c0c0b0a181403090d030518030c01120b01031e06092004 66
    0x50000354a50750b410040750b05620003440074000e03005100070003082c04180248101c04116454051105440307240b0120105c42c1d02c901c001e010340c0c0c00c44005100240342c1001d15465540d4480418614a507903032100c02003548078090500046598100c00340c10403030240a442c41084044490214101d1013107042c42d00c0348178403404180504d0400c81200100080d0081404200d09a6002c6854054860b20040d140003558042511085032400c1c06882e1032405401a220f18400582070304c1544032040420303600c1c68005030040310300c02d8003403002240400080c82882882e041c01c3d40c0c1c4440203040350400c080401c41c058003507404a03081c54946001d40e5010501003100e15404105801941c080c0e100c43e9080d4060807044541c000003050304041403688c0280541135454843c03058a0f44040d606003016500c020b00c44005010801200000b440042c3d9548101103c4d9010705002c10110004241e10403540c400b62140307640705585603002c4c0f04000c042d110b1400c82006511552828a42419410840e4000c2e84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 999010863 1250 999009613 999009619
    0x130f1a031026030d060501080f0717040f0b04030e18070509150c06040b0103020a0609051f0c02150a141809100314011d0d0c171b030d0b0a0b09 63
    0x403a0a070410290b000c2544488541c0a4039110114a81550041c01d083d10a403400141944041440898010640b502079007030340c1c468070712852001210000c01080100251400403822141d0004103003801311052280d031083e83e0380d5414480d80c00030010701451031101814052045010012510740060407101c0c140400c96265507451103089010940d4424021055011b000e500103102c10000c0302e11185041c1c1c1d02c02c885041401e5101c51013111615030074030510368803820014840204003103100200010421303e240103480d52100d40c001c070b004060090b400c6003e50b0000551a158690312001603401401c1480d44640341075000c00c040b00403140c1e880f0030030b803040d2417500120340700a0000e907103c2c00650740a551071902c4080b14072140d000b02100030300c0600c0b0080040400e4140440452141c1c484255500c2c1d8202d1009541c50700e5522110703803e440359040700204490b84070f03064084203050148684000465940b08a01d95603820b4850b04844076004445900051041d50181070540b04103100903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 999012113 1250 999010863 999010889
    0x5210316120e10020304061b0e0d0606030f2010080a0c09080d020f0c09040803040b0604020d0f020d0e0a0b0c03092805071403030a14130f1a0310 64
    0x200d00544000c0c0305205241c2c0181c4a80c46080c500c0e84166005107220f0b500507101048841144022025510303c1d82c60340e000011903510042c00d540c60000e00111241e4001c8400080c1c040d1641d9846000080c0c00c4000d030f40c1800c80d1031900792084501c00301010000001c0d21903818100ba0040040c001002c090f08280030161105c0606d24803d01c40c07014900100000411a48000d41444001c4c3d25441c1900c4224480c1c00b843c140074001d401c15000d0140210380c40b220301841c40d5542d44035008404000382c41c0641c459020803009040519034003071171242d1428114010781d581c2844240d402200c00c0c400c041d080303a03040221140081048600d00541c441540384400382e90f0380e55050340300c0c20091484092041c030b41d900750100544440c0d0b10404100507100ba011600c50030340b900c005800e9036490310291a8990300c1004020445e500c02c0e00401501c8204810141c10000601d18046c2d516101e45c00c0194100d107805020004003034035840314a4540d5030401d100d45181403d419521440c0d035030340a1080c0c44019 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 999013363 1250 999012113 999012137
    0xf1d03180a120201050d091a09120f090f04090203010f0212090c0303090108151906080a1b0507060b0a081f0c120e0309040903030605121b0405041401060305210316 72
    0x107240c10002110b035002040c5900310340b445141d205824000e81c4c01c41264403801750840ea109124ac0211800d01c115502c2c1e0340d080150303400c10003036216800100c550b0459102c00c11000142c40901843c0049010500090380f1950840344d40030001500500d050a07075800041522120748011003100d0301c099081c6070035041603881706044c0030000038450300c154011611025001000314444070f140300b900c0c00d503901d00c141910f814500d401071b5400440d42c880d9401950303030401200d501400081a5951245201040284d9802d00003601d985554ac030100054001055030307900f000c008406102804084c11041041c640000d01c002c1070000500c04402c4855650000f0010030360082041d1941000014020b010401040c41c00501800c140e100d8940580040301074581180d102181380714041d00100c90106c44601400100305c042c01c0041e200781c903a00d0002c120401c9261003030041c400610b000300d00a160b823000442602204042c802000040080140244075124102085415040010349814001011 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 999014613 1250 999013363 999013387
    0x108040c1208070c0e0f1807090e010b06030406150f030803060904020d0b07021006060c080d18050307051605040203161409121b0a030302060a0f1d03180a12020105 72
    0x1c60f20760080c1070018070f036400040c0c004411075032034400d0040300150903081d1107008100c18011001641d42e00b082d0000d28046c0f180e845954440301c03c25860000200f40e1044c20404940a036005841c180c4549445a1000c100c00740071040c070340000c044036824400c840340786881e1900c4501028107183c0c0320b03405810200e4155917802e0100d00c05550041da000c0c1c010b0130026001b135640c0c2020341c0780240c01401c103000017a42d940038828009010340c01c01d1056280c21070307500042c401050118140442100380401c03000200d00708002401c2401c0c85140241030003800f40030300701c2c00b40c50690321040c8124010800c105076114000301202400400d03042c11040da012210306e50559001e852100ea0704801000b200c03103040407000400c44580e401411603880300034100b1090103401d010324000980964040710100b00c0c224100c0d4412420200403010019100042c2c4040c111441c0c51100340c042c1c41da0000c01d810f242c0b041441a02851108100e4a100015180c08400462500b5114029040c0306000c1041105c1c0c03c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 999015863 1250 999014613 999014617
    0xd03031a0913050105010f0602102003040305030108100501030201140a0935241e0403030e0d0f02070605070c150503091002070c0b0c01021c1a0108040c1208 69
    0x2800204801070510300107510050320032166809031890b600308400080e00209440e40d24082d904694003410407001860020b20240c4604810804882418104000450400805036005070700c40c0d502c19540c1c6d4940607103540341004120010071050b01d45401000180c0c0c0018501559a5100807034684540358800c054a04644507840300020031031800e80104550000300460400a104008c1311098502c110310a50341d074a5820007001d1000d142881000b844246440c00c00d9000c0c946220a003150390300c01c0c2001c00c2c1d000f000e9800303d003ca0703180d8070581c0180c8000c1c0f081c0d951110103841c21078071581004000941d01d961510814044c4200042c41301c1c1840710030303080c3c50050002c402800742d02c00c07c1494014a1940101c0d00c0d075200d4010411490440281c50088548860300400900d83c3d1038241100c41201c6d80c030291181d0311540d402c101090f03518082251901020000b468000340140310301003c2054901c50000035410041014100320000c2c80c1302c0b41c1c1800761000407109028050462400c00414 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 999017113 1250 999015863 999015911
    0xb090f03070b04231015033f08011715041212140402190305070608060d1e030237170d0606170c2b0c18140d0303 50
    0x1008641090b40200c600014421740c50344060000b0800360000b00702d51030a402d110b01000b80021449840d0b883e03041140c2d44840c503504035102d0782c1c0b200b0700c01e642405d004810307000f03c601021581810042000c0888941000c2d510013295000e80700c64170001040d10364030a4010070007401c500803a2400d841540c869035401d40202104102041044c551b0025421100742c00ca13422403003070144c03080e42008402f1211f0a071088035400001007003510b09014050f150760b030008011a4008607525242404a031550130803a50b281685480e80315120b089060003420f09401085100d11070946101990701c5801240c221650b04003408941c1907400420314002c1e1486214803d1190010004501d001c20101240c0c0310720308545041d2940da092103c0310310090340a50f4111140340d403200d402d004480c0794880240d0698501901c1490481d940c500c850604000c45400b2011903000608055951443e01c501c03444180107406510340321010030b040800014510350494000804060701c6100c90410b007580c50141280d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 999018363 1250 999017113 999017153
    0x70305030613180b0906070311040611011419050f060105040e0402030c0a0611190803151908030c010e010621030c06021c15060203090114070f0f0b090f03070b04 71
    0x8030f542080f144080301920f009180b401580d002c03800080c000d10403170920120342c024050406240c00b2040c0c51019180c0d2a0805954a885600c0c945040e5144050f01c1001066021111090710903071880c00c540c401861604100c07590300600503680e030044203036030440b80d940822104650300e6102080c20505c051107281e41100d2880000320360b0942207d402035802000404030f90840e00c03003401e240046100c0c144050544401040410389241038210f07801c601d8100542402000088041c1c0d14000445580c0641c2480d080441c8444500100303004540010310401c0c024000300d030500e02401c5220b40e4421200301d008454004440805005401c0004199044a000c5407201200c040d24a10703400000044880c040c84c00f001c1c2107000705400b15001c1a504c2c41e90042d8107240742c42c401502e40c800c6289821590400c10310180002445400040303407024440c0744840c0c042c226520304000b4550025102d4020f9030000035065000e0040042601d190740d400644003d0070780c41e1820b00200c511030641d01046 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 999019613 1250 999018363 999018401
    0x4020a030e060c03011e030812061c031e0e1c02120607030b0109081c0e060408010f0209091b0f09060904150e0a020c0a060b0a050d0b10060302070305030613 69
    0x707110480101440c120780b440070442546e4003501c411a0800603460000410024051140d00006112600c0c030f0360b4403034405400040c4912002000c401000718807441100084c03a1010007512004002841c88030700a8075041180007040c043c000204500c041b40310306503043d481e40b1070390410355841101c88451401100300303685481c1010340c002030280c20002801d03804291003040010b003945002a02c5082508440000c10031030240c188110b4118201100d0158040024800400d0b00c500c06e11030301100900c00440141d40e142c045c0140800207000601044002c05250f075200c100c08400c43c1201d41c2d481d0b2000d00e0f290b9070103170300340022403500841520507045450055010b0400000d00141c8007961601038181c03026a66008000090741710711400e90301079400c0040e6002c0003801d9604101328120005009030107841d12007003c40c40c1d801c00b810081c4c0e2440b07a60014011107030074855002c0054145072501350710b05400d0361800303000c45c400503003403500510018011309402c0c40140d07c17002c00407a00ba24400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 999020863 1250 999019613 999019621
    0xb240307031808090108130b040f080418050f070c150f02130e09120315010806130c02100b031203181002030a0e1b0102150a11031003050d08060603010504020a030e06 73
    0x1043c5500095007550200300c006000c101d90070b01716030b003245143d0380c030040682d4071b6911a500d0302d80700b4030000000c40b12018144004101501c1ea52400c0100e0044010009000c1c40e000c0816030700c502000d080401800840c5940788045019030080d00312100c2c43c04004904000742c100701c1402407040d888003458201c1e90040100c3d911540f1200c013030141a078001200e51490451100320064801658107502a0800e0006034007154054000507600000081c8010034107070048642c030003a9962000c00300010703004107103040260015446001810801600205001e2075824181d41c190f20002d0010140752100030348840320644108601030400c051824155103900300305039000080c1054400c950458096442c511090a82c0610b0499816105a00400030001710a0300000d08140c080d10188006d40c40b4400d200740608204025070041401c01d00840d4058034500308542409003d11210040141d8807080c04022340e25001582d0546d9800c0301c0059582080240c103500a040c404202412030092030100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 999022113 1250 999020863 999020873
    0xa29090f09190b0603060703060e0a0e010905061303110a0809011d281d0a0c051e1905030f190608070e04020306100b0f0a03090212010509010b2403070318 68
    0x1082c043e003070685c22036010741c44440007501554168040c1410700141d00c030000d20300060300d8201011040c005000094007074181c1d10703041e044c085c0446602600c039200d130101d40100340e88030780e11002611505000c0c0154503890307030312031f41d0f94803900301500d0411940d2120500410320308211045041c80090000c1e00140030f00306000102d150b0000010001e4011a40c0003880f115090246031038203411082c0050b5503035800120500900a02948070100308040c8510040540e803090551440d01484440d01e80300c0401203410400c0606121a0204001c000e20a205c8490b615441035500001502c1c004a402651418900c1c01400d00d80c0c050780340761140610000d0002c8030b23440c00500a40c0254252440c1c0e68640b0800040e910f55441501030f941000c200e40003008404078081d00340720b040e9240114164405400040d640114592242820795450091007071054003449070302b40840d015503080450481021040c2c291480100111380011800000140308502c03950020f07005800d170b448a80c801c400c030b07410b02d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 999023363 1250 999022113 999022133
    0x10506030106060e0307050d031103040f0321020d0e01180e060a05120d0e0f04110c1c0e0618031c0f03180f050a0b0a29090f0919 57
    0x28090080d4682100450121302c5191411021000600146040e40c44c0c14148000c81e030286505600300041074214110100c030520040c80104810b1400700b44540c21402d02c41010000541c0800c3c034041c246922030901d640100d0040c000c0001410702c030085010200050b283c04c0040034450641545c900750205079000203049a5000d4a0b0549010300f08940b90b200f1304c13505208a4042c42d441e41d210030350302940d0320b100358034035148610003410f0b0002400007500410280c404585024000706004520044641d40c10010401c01c1d0b00115400b150045100001500c03040d03000d04c00078000c0c94000303443c445000e480c590114440502030100d41900f8003821004070b488054440c0302c0b00099400084c0c180c0588603000b01000318801c10340309014101580d5411907190401a0200c0352402000150030100f50b08040061140c1d0361403030040f610b41ca0b11040702140b00c0ca06000a81100041d01421090752107030310319154003103001b020000340c540381c1000d201d2620701d901e100051004021055002040340600c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 999024613 1250 999023363 999023371
    0x180106020a110301020304030905060c0a0203240f01030b07050706060314060f0c12010603020d0e011e0e06090606210f0714040207050c270103050703050d141e16050105 74
    0x40c035030380b01c602480b00301420307484103941c00b50014a90b417005001c7c0d4a0404020031611101e441210f01d0011650302090515250784603041c20b000e0200c40f00111103508110480e448282da940400d40ca605541e0b4602c02064040c01d60400c011010640404100d020f074880300c099900310310724000022000021982d030305011903042e071520b4000c3c0041980c0303000c0d000030345046000310390b86140f0b5607007000e0080b8003d40018814200c442d0700c901c02d0181100c000e1181800e0080e00c0400765040c46080c030764020a9520245192800d5400b40e0200000c44002180079a006802107c4074054600203280c0714840325100080c030701040c040d11210f60001000003800b071040311010000040d114100000700012400341711000380036500901c402450b5450000846100a003480201070034401d00c10705400c0000c102600111000d034040d107803e000303105003000305000391141464070000c01c0a00001e00312440c040d200d0303801200b040100c00812074207444400e440908207840c0c0c50f000d4419490510901900040ea = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 999025863 1250 999024613 999024623
    0x13050d0b01052b030503060a0e091006080304030507210b090309011209031b05030408070303120b15070609020609060d051e0c1819030807060507180e0402180106020a 73
    0x1a00185810944161510010f40710014002d0020f042c0d04d0a40d0540d2009000507071210072140045801c011850b070b041e001e01110802444005c81c9000064110f50141d00500c2542e802400104006900028888292020803481c0c1200ea1140c52180c0c03401c0c1716890001f003000e82030804100c010440007001d8400e41500340d0310114480d0708000003030300311496190040c000481c80c02c1ca1007541d9000d42040c11525100d0422640303090341e9000f505041100c15042100043c507048c0040c0d84148590180481d5500100d03030341446a03c40d0060428140700711a00140303140e840f00324aa040d503441c8410313211a42005072034140d88071403800031007000305022200c1e1602008155000d60b00e0140f01610b43d441400036005442c40e1403000c1c60240c0c2e0800c580d204440d84103a5030500c043d01c41951410300c4009600c115001c50311982c0310314100341520401040d13141005240e00c0700700c805821404954081f00c05046010185843e2400803401c40e001a00100010f90207410002403196400030740500403034091 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 999027113 1250 999025863 999025879
    0xa0203030a0c0611040b07081822061a04230a0b030a200d020912030403230d0f0c051006150e06091f05070c1d060418030513050d0b0105 60
    0x2800c03040c003840c020b41c01034003591b00092040700002420700c0000e200090210b030b1203406003550000041d514416050700641d580d507411070055400d130010702034800905030300c0000340764050348021030030100d0080b4400c0000d0303280b14000f00075500d040348409a224100242000720b0301c9860b00d48800141c0c0c4159003079403500780b603c00707800c107030009500c0c1922846945980c100d01e0081400c030800c000e9041403a00e2584481080144601034004000900086110b807014203554a036a1140b04090014018030414641000c40340003c03c65005401d84140840350802c42c112141e01c0c10801d280281003082080da4602d441c00101e9140305002c14040d5000c9140d882c80c252901c40070902100b4010891101e4004075200e55114503500c3c285103500c94140036103407603410b008458a50b84620038072907100180c0514400c010340c0214980c0d4032910342c4400144c90034400042c031400ca95058101c5050042c1c00c01102158012010136403c8845004100040111000c1d50050030045100f5a085c03140c01d2190301c0c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 999028363 1250 999027113 999027131
    0x102a0201110c03300c06070207080d090b031e18011a1f0c0b0a050403090605030c0d0c11120d060504050402030616031b020c09090105270a0203030a0c06 67
    0x10b411140c0940038018007100120f1911902c03481c01c0003a01c0050707003010030101006168450014046a900290003000e103401c1036040030341040d0f185d0b000060641c00c81082c0d4111541c0184100c400c40c0c0806d00f1503640ca544059055000d04d440100c504880036541092228181200803510003d56485008100384509810212000c0e80440d680d250007850384007819440080464004010740342c0c5060214503a411659940740759201140c0c0031046503541d00c144410305030301440c14006481103007002c0d803031400c1502082e249400740041030a0402d0300d411710705401d45d1203501e4500c09000d041044880d000340500708042c0c942c102280085819140810000d03ca1a050203104c0c040c5070003402402403515a00201c3c514482860600b00074141c80c0c0038600600c007051070091520b5003555000d0042041520108008207a0140002919a06000c280580340840400e0ba4048aa20000003414181e441ca94641400b9051001951500010a64002260b000090100081d200d203030208403001c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 999029613 1250 999028363 999028397
    0x512010b0c0709113009060403050f070f0215040305060901111b01021309020909060306040213090c030b100f1e030b0402040209102001060311102a0201 67
    0x1852918806540c8000800c10038400f01d41e1015407403083c200049840c01099803808015411106215200c1081081851004200400d0321031b03000760003e000380c0f6081c10180c030700610b580100b028403886c05d44001030311400c00100c07160040d1025400751450040085091400724207410904c010f171070034040d42000508460303041c1b040d40903a00500b50094100081d07158001060241d05e43c1c2000a99400c201e194090a19400c05000420800802582d551001010300044082c00341510b4040d9014209000069a840c140044084070454000038600c4260030080348880e032b207a00c081c3c410141402448400503402d140403055808002d044500642c0e01d5205c0f81d1120905058250025403040051000410f40801c41740c001d0f000400c0541041c4425000070010752a400c1088040f514513840c400703002008401c510036203260705000b0001c080c0b454607000100b1061014492280040c1130105031072a0045200340c00c0c00120fa07141c02c44240441c081b6007035121034110306a02040030200f0b02c100c203070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 999030863 1250 999029613 999029617
    0x310111b0712030f02070803031003060b0105120f0a180c03050d0f21060918060b19171c020109110603011401031d0d03023417090d030512010b 63
    0x2804600c042d002c00c11480e102116100c480d9240c1d0300440c092640001541340781000a103000ea2803214019001910314a80340c4100c0e84115100c505011040c0010f0022081c1c44120950241c81c0f524072106540e12010080020034a0038113540605a62420050522024485000540384038801b114500201220b06442c1da6a502c02300d00d001900036000541c103504103143c00f4183da20000701c0803c3e0680c580b24080162291916580c4031a03544004031000c2c4039440c0245803141e441500d01c0501c0b10b042c050342941400b500c0c055800c1515480c0c00280c680d02e01013040c0405802400a406248180c514009000e4080084107a030381d1903600e80402aa07140c05e00450b4122400c02014801800a10f40154054020500e8554007000b0010345030001c07020034401c0700e03a01c010542d00140d8508158401e5110301c51a09200307070440d40d412180d0040790030f4480c4044001c54020b0000d84450044c1c506510b000e00c40c01d0440303900a50b01510714002c164020000d080020300040760703081c40e60303203464150b200c0f4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 999032113 1250 999030863 999030869
    0x30312060e01150f14030702060901060e15190515042c060103050925052407171c020d0b1806120109050111040602150705180310111b07 60
    0x2c20f00842007521070240481c540d5210702824081c2e852080c05c2546216500215114000350b00500100300c1103180a121b140c0107044411403140450400c0c10b40c0140403020104032502412400000c14842c45a9030b000400800f4020011203064550603e024603e070454410300320b030845810064128424110001005080000d60388600340d52071100440c0609405496140907004818415640300b5203005003500982860031551819403822080c0607440c50010300a148001d00d00350103c802d100c9107800c8a084940024112622103104a00744044e44615081009141e0b020300000b070050016402400d800305079600100465404c0320300341b000b0801c841c4da1061587c005180040e0217407074400c8d00c0b1050302c2800d100008036003200303543d010300311004419490344509011801b000007a50400c1030040d040c4c16550780300c10904080c14007130403d02406d60307455100c18555130250101d8404001801580000f11801c0c48003559080d40c800a9610070000710807900c8585190011458002800d4412 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 999033363 1250 999032113 999032129
    0x117120301090c18140418050d0504080d11120901050408011e0b0d0b19090804080c0a060512060609040e01020a03090b060a0315050a1b02060105240319060807030312060e01 76
    0x15a1900301b00041440b00070070409100f840020300003003001088070700010040da0321819070b920700340740c0c00f44d1070044450314440802034002c0e00100f01e10700104802d04802c2d080315403a40c07102c015030700584041c007464004401940c6055a03082c284220a40038a4944000c003d040101ea40306a007480380003040248003401410b9141d01240c0d08041c00d40a00c8034401c1c01d00750005201d400c40d5255102a40941e204d840c1c554400810405180b410910000041a4038205103140c0403d030300b07411480000007007c1621800c1e002c0750f2102c0e507071159084001900110802155610303228a070240085c8103910060351003400a40003c0c010b4100081d038882584d411030f0000320102a00300d090300240130f004015151440c0c5901e58602d01c0c0005410161780320a403030700680f1b1103605140c24480701d040420400101c072000410703280030096400046941000c00030840c0a591290f5076a040068211a4030150843c41208800001d03d5407000c0c5591680003201c10900c03046550310f0388100503150a014640d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 999034613 1250 999033363 999033389
    0x6060f110d08040804090212011d0915070c0b04081216020312040c050d030c03122a0c08030c090111030c071e180b0f030706080117120301090c18 64
    0x6110740260b4a00d0340c45031140308400d29007505c410382141a0b0704251102500c031601d000051200e08071401180d0b8840715120040d141c01c1c50010304e0365540705180c000900c0b50103084c1c3c021901c0d2031b108090303915120390009803c4081b42001e00d0048203581c000b00304192581d03a02c0c400f00c3d84032010b050703110070084025130046050086200c05020501c0700504115001d84203080d00142507107559415046a07800790b250404140d15900340942103200a58007940454030303254024a03080603094403002c1344544104004d40c0000d0500301520007910254000e01080d40100801a418804400403c00c0300e000780c1c1c40d400015461a1061741c1c034000e081c01401d050300481d4041c0a5070b00b00d0202400760707028100200000c04ea07695041c51503450840c01e00e081c0c02d9215078000300f5600780003410046640c015002410624549a001410900113014003a414050790810052540c0100300790000f24041d01e401a950396551241c130f00c01400841c141802180e080c80c841e8080800314282d113401c40e206c0025081c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 999035863 1250 999034613 999034633
    0x1b0602030a110f0a060209011403160c031b110a050612060d031b08030a0605030303040b0726010e01150503091b120a060624020c041d0d020106060f11 66
    0x740b2144000040300c1c03558420308011040d21401000780c10401c5014100c0141c0c3e0b81701c440d00040040c2002407403501148810001c0c420208130180783c00c120800b092070503403050100c503c1c086440d150206200d8480194941a034030501c010070050540592040b81e02c00c0080342e85005124440c01004098421030080400280c141d050520072a48098070900d01b03900720906952050b6400d00c0170300001e5840910200800051014500c2910050b01003200154103510b0540d070b849104401c0241690200103024003400044261002410340d40b4040e606042c6a540c0c58441c51021050248980a240e4140040d03c1c0c5050307001d5421a030003060032402a10300c4981210440940c0792101e40300316000458542c0502000d80b06200064a4511515000c02c072946400c1c2070810700c450a2141c1207120f044034003044e0399290002010b40304107405842c08620b0300c4840011903081c684c000005c1c00345010703d5050341d00f1660b0652000040ea001500c07131403000d20300500101c401464511425041c1d61262901c0c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 999037113 1250 999035863 999035867
    0x37020a2006091203031f0b1e0f0a0203220f060c2918030315011b080a0c0308091f0e100e01140615030c0a0207150c1b0602030a 56
    0xd0022200504040d1900c003201c004200b52040070319007840c070b5030408001e01c0070035008501809018a1181c03210030005007000380381c10380381c4143c0060000382401034440a04641c0b804040d039003480c0402c2d24154903140b000601944a44c0212002c414032071008071501ca01021051243e0b082e00d40350202c80d0724040c14080b00356255414002d00b80c40d00d0354102ca080700402005840030b108800d0703078180141541801c42c52000c9114000c0540c1c1d4076030f00203204010180c6c0c55507840c40e20700c03442442c1910742000418000c0c0504800305101520f000000104a00c0030740d00120040070440c0710b03a482402039943c03012156100c105c9010010345520020144104c15060b40e00558004050002a075005400d040c000300100c40c1c1180c03801241ba51a41d020b8405500d44a4480354000c80655108000100700d00550a46100007072807200c2140011800040ca40d208211b0480604550005c26440452030b07036000c2e00d000c0b5491412076105400485040e2000ba05000c010b040f01c1c1c0c0b98006600b0f203200d108007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 999038363 1250 999037113 999037163
    0x605040f14010b12132a080d090311010e0f041103100e040819050d0e1c02010209031e070e13020f0d0f060b030f1005040311030f0406031137020a 64
    0x8140c072141003401700c003442c0d944861288441b901d8a0380c41c07404981c1c0f8000943d0704011801c0034120500c2102e607c00c102181c3c620000d2815410300f403038130340401d0b942080001c141442e100343d496001464030340071580b042440401940900c4101e003809040360741d02c02145240e08802c4034001c04020742070105c486c000801040c8a04190f42c1820a0750400c40c0328940102141c0050b100214a42d001c5440c414030b1078040c1c1075506001d0120300c000e516026440c408242c4c4d0700c1c13443c0c060400b4a81170395420b601c104414003524001d415010381400c400d0400302c15403011a58648400e03417083d802c0c04840c1105240541d01400080da1001c01000f6101c80750310386c0e100505620803181d8142c0581407040041e00014001a114000f440c03000145604050500170f101c060741000c04031440d401040802c1004401320162005c4441c14600440c3e408090420307104603020310500c0300721040c00c06070000c3c030345035821510203018000c500a1107425000f24404070707a288044400a48030040d00c09040c01c4403858109 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 999039613 1250 999038363 999038401
    0x10060e04110c0a150b041a090702011d01020a021b0f0d0507080102120a060504090302030d022212030e0303040515070618030908070506030f0c0901030605040f14010b12 74
    0x80703a040002e00d00e001c506058601078100c0e04103282019090066041d846040000d000594042040402c10248955540c3c006c018280c030130200c400009031014401d404c90151200201c10a00084003030710141c0d8042d4100380360b500c01500802070550545000e01c4091103c1000041001c101500c1c0a01404202110307041d083e200c07400364910105800790240018580820032000309643c508e441180c41013113801030741180b841a4201618440440e500000307584c034400b260000140c4c1c030702c50114085402030045c1002c548010307005400050300020030700502405402612109900d018000c00c1503103a20650040c01e50210512200c0304064a05c08090450180f01c0d0704c001420300c9990440d10400032030032030210005007910005000043d005d102c02c40090100b40c90080c15410f001c40300e01001e4500820600c0c250038040350101c07950b84a90050001084003600410003590341c0c402580243c4406202881540901c40000aa020f00c0c44100c6002012101072554140c030b490719450183d12002d2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 999040863 1250 999039613 999039641
    0x3110a170901120606091a030f010e0a0f0c170f060a0614040302032b030212060105030702150a02031503030708070f0c03061a120c0a06030506030a0615050910060e04 73
    0x80101c0b40c0c600c1c207842114003170081901d40254092078060080d10150400752425401c25060050207082803007031010605440e02101c0da0380703841c7c3d24034413080010300c1980000218181420340108900760080424416201d001141e031042ea501c1c0d001e01841044184c0d07145801c0000744000300001c0b44203441050521021038201443e00d07580340c00087c940305040700540440c0301600718203003003580300a85000905c01182015800c10000790b58658000c0d000801142c1808000000035008510a01005904188141d1225410706250400342c000b508201c0d8844810b6201c002451303080d24000040c3c0e04455030040c5054030b803140d270383c0da000740c1030100b42c4080718245c1d246400440018600e0003000784400103a42d240e10200c10490403c08072034034260004d00a504007104082171038946005440580707569050215498a40d0310200b850300c0704040c0702800c80d0b443d00c1d580704101d81380224000708480c001c031040500d41d141d00c00c0d081012403540c400e40c00421480309040c0c10b03500303140d00143e803000106 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 999042113 1250 999040863 999040877
    0x61801020d060e060a08120d0218030f01090c051813080c0607020102070c23210f010b040b0f0109030b100b071101030c030e07050114190c03110a170901 67
    0x10786807840549450f0f42100c5500c11001041020b6428084912002014058020301c500b031521044055a0710480951107c080c0e00040c000515100032800c40042d2400a001c441d8a01c8110f100f644c024000301608451948242e8400202c51400c040e00d40d8414515441c400401d8484040038890100e40c0d000c11110000c0a100303c01c4001c0e130601070b8034412861500056900c0b40e003807802006114071a0000700c07180890586c1c03034614019000f90000c0c005015901d2a00d5100b122250b01c0111007011030418842c030600149101400040d080302c801000282c0e81441454080d50401c8110480380c1d09290024004000800205800b00c2045410050602003420010f846080d080e81950100e103050368030290403c10141c0740d5a241c8503180c4490b40c0d6140401440701c104100f01c1d1100d071903101f0181003002c04060720f1250b40d4003800b111080ca0140799404144206da5002400c0040004425004501203c405880182001c96401d00491f4006096460a280001185d070150031140650b4100190 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 999043363 1250 999042113 999042127
    0x11031305120715080709061803020d110301051518010e040813080a06140a05090309060a031d010c0f02060601090e15030703050c03190507060c0314040b030105091806180102 76
    0x400c89003d09200760380d0301c1026602d004039000e051840258084001c00101d2440e42c1092015140000b0030303203504650407080003501c1c8c00d0002c0f0003908910340700ea240d442c20f414014800c2d082e41c088461100180d0b2072001c0300045c00c48030201c440302482842c0d4100e4009000900040380341004040c0c0c6000101180c0c01c01361940201441c15100990465100d542ca140041e1030700441564035070f01408180d000e0181e86031040e181c503240e0007041607081c020000482e01c111802e00070b4004011288280403c0c01e084200b060145001c5c1001d01d00100c04545004421400a440407814604c2540d06846140c1d9403490404050100d072401400c00b02e02c80030703076491080d580e9001d00c1150002d5028000521030020980101810a601602104a031401e1554040300080021a00400302d4250741800300d156415810180c40d006210004020179903c006400b080c0d00045d04051410380d00280e607200140da860044156290040c2c410007041c87e401040050035140c0300c05481c81901040d40005400c03c41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 999044613 1250 999043363 999043379
    0x3090b180a0f06020706050a050402030d050a02100f06090e06130f060902100908061317030901020702060a0206040627060507110f0601030510052e0b0f030403110313051207 76
    0x60401c011180b00750005517120521016005554001c220b0180800c100d0820f5030002c0d64801c41d04440d503050040100380407454074001d00007890b064012071f000340030f01c06045541c00c0003003100703000b08141c8030300d4240144030340c54002070020700c0b400d1846859507a210349512688220108550110380c03d50b10396044400680b039001c40345541c50041c0c0c40b001480b07420001c0076800c100c0d00522014159100810500101f40a03116a03070700705803648140360f9a0380f600382582c1e019114908019400c8400000c0c5102e4860340050340c54880c03405050208094032034002c401010040c841869452400a0103540e03000c28096032109400026908040201d1060001941d0a0822410800f500ca4000c0030041003840403c1c40032014140e030110f0108024901100f801e002141240041400040045080782c01003440f08007003809800d003890b4840c1c0f650080000501e46500442c1c1c01c13000904441d44043e000000001600c0c9000c0040c61503014032030501007400003868414100103d80d100354080064005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 999045863 1250 999044613 999044633
    0xf07062f03090607030c020307060302030712050a06030503040b04090b0a0f03151d1b0438150c0f1227060a0905011701060c0807020301022701090603090b180a 70
    0xd1310039214005846c64600400d410a51203074010303c2490b004201f0098610f5101f541c0400000015100103207548130401c0d4007006051603080140f40d4400003801050f80032058015104070759000c0d40501440350158240b246148243c0b080c082202c0103a0350500003e41607844064005200c55000100d82c600c50304030400010b168071612103681c0114000e8014034000b03902c2d440b9203581c2070f03c0074410800c01510400300c040180544140300d400c00340312203a000140280d81c85c0042ca0060108203903505001c0d451030564411282040c003131250303060741055202e01240c1d43c0d0307102d0455000c0d80d0508a140c4c95448001281c0308466541c42458103145100b40d031070001801c8001039983e5510516801d04d0000b4101d6000f4400121900f4040c20040005c2540562220220b0703520080103521040700d8808640680074030500d40790340ea001070038070050a0380304000b080c620b5102640c0b1008499943d0400b50100c03444090003400d070190490010f16550f00d20300340784051145103004c0312482c000e0b03512824181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 999047113 1250 999045863 999045877
    0x2060103020d1a0a3c020f040e0f240a0b0c1002040807081905060a0f0e010504030f080106090f051e0a031b0f050609040506130e0f07062f030906 64
    0x2540ca207843d5201c1240400b800f070751640d13a000802d40c4540001041440020040071711851103030002032101048407204151001018100c01c030001d1402d155000024216040307402141d8401c281030002040700700b189042724401c0002e003000c103010703040801c4500b80b58132111044401d4425038444c402c0186007403004000400d51384010b0072455007071010307550428100304ca003091410702000c0b070340c4041003000c16030b55004110058005100c0841100010181021f201e005040d07521f01002c1000f80b680151800c44020700755a510243c503030b00c41ea82030350740f0185030040000041c0c5401040c0314038280795082d800d4503840001034024504030031700000d0458005410803282503c140700001c81080352108801c000d01a0101d60304c500604120100e201800787c0829148680d4542c0302042183d15501401540050b8481d828003040385038065080c1d41d4a03102040284a209801c40064600c1c403412400044109480a000310480c028980c0010003c0d418400907581c00f007000382d08091359500c03009002c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 999048363 1250 999047113 999047131
    0x501050f070302070305120703060521010b100207030b040515010b0a020d0915080a0f0509010b0324011503060801060e180a051e1f0506031c02060103020d1a 69
    0x94541400c0c039030340080000c1c0c12a0203250042c00800b00180d00201624504c0030700d620400415a5130141c11005058268826a0403003c00c5400b1001c4800c0e10b200000c03a4a1048002e01080383c0003c140905040064104001600300c03c100340006580c00c0100383e0032500a4044039401e00da49464010f00241c01ea0210095800002e8541031450701800500341034101403c011038003a00d4440c0002c2c405030300190075070821105000003184034909610940103201d0441c810013007464207a800710b00904090781e203144644a0400740001281c0c404011a40000f0407000c18500c0d030f440c1001c851140d1320021401c200303258448102107a9100300344102001000064a441550b0428140103c65401400c0000304560815040c1c40003082d40022100a0203042540428091002e0600d0900b00010714100c40000c0c902c40216400076402130300700d107004003011401d59503c40e240318601c0180403e80c984000250304041d00400c00342c500b03001205841401010790f8154441451305c100742c945400c403010b00c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 999049613 1250 999048363 999048371
    0x130516140703120e010e0708070f14180c0c06090106061101090506010b0a12050f102102150d0e10050a0e0601031217070e040b0108010506120a06050d0501 68
    0x28945501051140800391051035540c6004100d4400802c200da5203242c04a0380c585070146200d004400f54084141c0d9071499050310765040d22200802d464241d01d2051101c00c0c03000041c04103000441010412480c10300803e02d210010b51141d00c1034403024018401801800c0500048414500603c0380520032861400002113240c1062405400030ba0485e03206100c80c0c1c58a000360002403000900c02d0b0544124107540340d01d6a0b8040001c070b41e00c06200c850340344d5060900003480041c240c0c0e90051402010900740300c900702074503403140421413a4841000c000c0c211210a050002d814041984a0341d80c0f40c00745d03941e03c2c1c54a0090311000303403601a05030704110342c0a1820060200b00328460303075400c208030420511810340e19005242c2c1e950300600010b005d0f502c100b50850402c0303000341d1b0851080c4010113410010f500c0c003494080c1c161014119854001c80c2050114141988210000d034140d4100400301401c1c41c8919207421200440202120390030350340d410011400b9524413161600a40c4074a001003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 999050863 1250 999049613 999049651
    0x1b0a050a1203081531060612050109140406020906450109051c0506090304030606060c0b0a020d150b0a02010f09080301051207090204030f030e030601050f0607021305 73
    0x1480c848000300022000c88490000f5500c0340c5d070350101008404101c811845002568260415110f101404044603407032130071380005803054202c0306040c06a140a001004940c1c1da40c450441540c0040d104e490076000328500150000c3c0e0142d01510100d003000d0000703814103161500e503040c07240001d800403000c00701c1482d802d803152404051032410720701010b0b1480309510403000040c149543c00e0158510a1a03500003241c2100b200c01c01110301035030450704499550034465007181d181c1d4840d000c240c44150401c0004600c41d0300640070300300b4890b40020407002d40c0e611011100001e4100101d410041d43e203812400340101c84818054002d8501d0700102d5a8403600304002034215500d010250001508111106003c02d105005070303070450344144c0c1e5560400d0244081141450b425070428082580301041c0070060000910b5071150340c9110303444080b00102c1010030940d90b500c0903c15a0740c045400b8194549508100003e481660300c06019040846d080c4c00d803072410707100129070350500c04220065031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 999052113 1250 999050863 999050867
    0x40f06090b0a08120702060702190302030d050c03030a09260a0e041503020d020102190c0608241003020c011d19030804030804020a052d01030e1b0a050a1203 69
    0x1501c01002107030031060051500c4203503610b42402413a500c000d03c0000c1607001c15500ca5a0486202d1070f4000c1c03400350324407503203100400e0f812500d00085c1d00911a01420040b840e0164040341d800f8201100114210380c1d030030124101400866000312404548420f202001c1c1809400c040760b00d01c02e02c80540d840b03603000c5100a00084051140c14452410030000070f84000c49103000e50181c0f501030300d00e12070316505400180d00c2e1036204074042e00c003041c404007203c007845024a460030669a1603641d10740c550b210b07644520005407006040080c2c1c3c0030100c1003641240307060030200700d0703441c020309000d800d00340c407060a98210b80c2000c81320310340c40b503d001c040c892159062122844034510b0303400b40002e00526880003400c40038024801010b000000c00031500b07541c1c079103401c2002041c00914006950100488044001140800505524481c281203030704941c0a030190942c07426000c002801621424080c245e00c00f0172812003590803600310200846c25480b03000120014103016114640310404074900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 999053363 1250 999052113 999052121
    0x1e03020105070e04020a080115030b1002010605011403040b070f110312090705041808030c1b0307021306210813120c080c0d021215190509030f0316020705040f0609 72
    0x7443c0d1050b441001809100d5401600c514199550340c40c05412035050400150f0060611004d01a8410319034000104400d07815004031064900a90301c00c48059070030f80c06640507000690f00105001d19800c009040c0d036200300c044210901d40d5141a0030141e012030b51080c00d40d030004a084414043c204200300740c94108000c2000100801d40d0100010068552101900c101c00303071000389481d800201043c189900710341524158013100d4041400f5181d0b00c409180da036406010102d001e40729410040321322090500c40c581c200d44502e400700c0c1c3d060b10051003002c20407180380f60403100c5142c203002200b0078007040117480f00680f010455900c02c564803401c0c081c07107203d00d660102d9a6584030f0600b589203600c81802c0c22001030303410746050840c500000707900360070201041c84242c0505042400c10051082d10009221050602102040310345c4443c03001641720311071010080701c02d42c0c080000c82c45d0303030b0910b05e50a400c0c42207074415a0b620303e8850000030180d410180c00b007071909072542c506104034140362203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 999054613 1250 999053363 999053387
    0x2060702013524281404361b08031201090b031b0103090b07031a0a0e040305090a08101506051905090409060905010204080f0f191e0302010507 63
    0x1081c0300001e420044504010f1282c1003050060103442c0c001c01c00300380040d0f2210011040380e1543e065468841c3c40c0050703001c6906a4552149080064515524040310303015915500001200140d015100941c00c2480c40030079811244a69107128203103d01c000c0308600c401500368003011b9030303031140e040300f00000603001038001c030a025141400b02001b5950000300d048001e0410100b00f40d190070b540d00180e0091901810280584a14404201b48079505901100c540607010025001c0e1090740018820300c40054021040341c0000301002c07402217401500a00a41103009121035411034035510030b142050520115400001d8440903500307500c108005100c4040e0040c0d2410a003070404001d0107c2d0303107074001104482807020010302c01120740c446411802c1360300c0e0024806d100380b4810385001d074001c2d03005108a071664000c98401003505039000c40c00d040c61300f5010707005282c048840708201c010100c1e801ca0841c1d0500100034541c82d140000d441449035030b4001d8000050900c0d00c01c0001e005112502 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 999055863 1250 999054613 999054631
    0x608010e0f060f040f06020a020c3105040f1202060402030d0c080714030c01021b0f030304020112020c070e0703050a050601020d140c0a06020f0a030f0902060304020607020135 77
    0x2060603120900016100d540158244000c0f003550701c0710704042d0040d0340b07034103406014240005441d00366180c000030210590241507d108642ea80300c1c0310079840c4006250300c190707031000001c04214001642c03a004950080c0c050911040d51305026503c0442c0c9030701e00007801d00580c00c100b040000350302e418000000c00700510708101403076140d04d03513806941b0304c550761000b020300b03421812031140d28008209480901d510305000315621b00d654043d585d51840c3c5034006400380d126107511112000004025038bc003855068441d141c0880c10b81040c640a0740200d54807440d00d10034168001000c14450815a003c0d03daa51000100c5003040010076054803001032043d415035200d0703a20803420a50010984840d1038500800c0390321030111103c941d0821030060b42c060603490002c40c1d03100c80c46100e800105401c203e1524100034001548003198107030b40c1000030180d803280d001e000290150800000409246105240095550f02c080d0a040e0700e1268a2408100c850650750314000c50b003854025880d0412007071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 999057113 1250 999055863 999055873
    0x4080909040c090f051612091217010f06050f0f070b0705030108011803270314030c1005040222241a07020d0f1704151416060c1709010608010e 63
    0x1201020b600403030010349406c104041d00085038400c2c241c1c3d6209400142d480b00c480b400c0c04400810080c086c071116080607110703e00e5540000b4400303102510040071201151901820040d074403610400d9600144004c091156080244a00052640d41e10340c0c86480c0070384880741c81c2c1d4101118035007194804040180800c20f01d01030740d40401d030403000b01041100820360f00f101e541c8100c19011000c8180d40d00080c800150b0525a002021012018200304ca00f030f041110500d04403041400c044c5d42c001c0d50065000308c452600d400e40000c954001c1c1312080c040400100d40c05101d00f03000405424056414802011b402106014000c00d000f0100380e5513446002241c2409002d800081c00301603981c4008110210b85404e44041011201d20142030050f5a01c42c2e54541e5603035047ca29860035001d0345440051451007500c07074512403203001d60720600c900851840310300c1d00e184d407007000034408820380c0c50501240303001c1080302e1341d540c0020910807161000040382c1c20346800e20312400c0d20751001d044207154102c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 999058363 1250 999057113 999057121
    0x120d1127150309010920131503060e010504050c2223131205090901090207020411070b160f0203030711010e120702030d1b030e0609090702062e0501050304080909040c090f05 76
    0x42005504d440d1b05071a070000307500390488c41c000022800f90750000701940c1c101503022002d940103501440c4280d0080d000e648404e1044e004101140130001086590041440120b03042212960300100011a0000d0341d00540348900c0f0004035092001c4400b0f1500107484038180c0100031007040d24540840890508bd400e0500f004005080c40c0014010600615800b1031004195034998100780d02042880000d03d540321401d040c490b101c001c003201d803030134020103000840c807245104008c20341d040c0503527074095401e64036051012100314542599000b083e6407110303a52040c1032810320203e05007401504a2598a81d070320704c1454200420b020032001070101200b4800040399130703415295012503062410300d80010b403603170020380039000b24189203800102e1001003260807a000070708640290071030300c040c84011041a101c8000300701481400d1003c08a0360b41d0801c040c0d401003025540080c0b080130418200881c2001050300582c0848060350107000d500402c0107070326024400c08900919800083c021440c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 999059613 1250 999058363 999058369
    0x4200a1205071d060708070c08160b070b0405210406030609060602150405030403150509010b03011b0c0804121a01090209030a15020903120d1127150309010920 70
    0x201d1001c440f4031880035881c04001d030b660769204a40449520106042e111400e0f404d20b140c80c04101d010300e60291240201d0500c01d001c0c0c40450070122030540110742d00d400c0307072555a0140080080c000311068401c00c07120282c0e440c4291400e2080d6046100b5142d1100d18101000702611200c0d440903030030b90701e000b1040c0441036011680380c1031200d08105010761070b221480c01a00c0c1d8810381e4406041114980020040c81b041d5800c010300550507540280020440001058202c41010300504141e042d181d4181c80300a01400104044500403c21542811340c1e44d40304041110300000112002c0440c0c81440b080303000c10040c0e490151100540860400c002300020075591591102e020f072183c0c03d44600b0700e40460a5404507030300b2900c040c0556444212810f011400c40e004524800390036410000c065030301c0b05a6100780d40c2084109421001000948040c101e0603c00d1404400e42245203440054031011030480254000e802c200000121100c6508100b01c0c4201e404004800c0392601d4201e14103559 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 999060863 1250 999059613 999059627
    0xe06040908430f1214040305010c08070203131e030f1b0803070c1806091b030b0105070c090203040501020c1603170a2c280f0614070204200a120507 65
    0x3e5800004540010581e000c1552401c071190030b2000c0700140020048100322042d040b00c03048009a407908485c1d625028410b036168062091540035150a820080000b590200400201011640415080903441c2d40f100c6d04020a030900603203043c210201c0072003c52048088000050404c1c50186052810a41e03454000c2502481240c1041c2c8940003025040d640c613500c0b4900400140c601007080c2007004003400101240c181244c8040780c034062095a041d40184102d03124954410742c407002d61410045480001e4002400c1070300d10b0341d030901400011071410041e20750049182060000c1140c503503d44509902d0959990f410280010b000c491282c50b08012404400d084000307003e40c3c04101e000580c1504200d909000e5408001d280d005070f200c060340b40c00920044005101040714a803280d550141588c1c0324460140054020303541000c81c040170074098003c10740300400105525601d8041645448403200b0740d0014079000092614a180d00170080740d1455a5444d001e1110340b07050f00e070181c101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 999062113 1250 999060863 999060893
    0xb0712050306041b02010c1101061406031003020d14060c070308071d0307090c0e0a03030e0d15020f0a080a0606080c0c07081b030706090e0604090843 66
    0xc0400880415116500c64000c2c0030604c5242e99492034052003010001d01810090120901141c45074548a8070088103010b03038015a0910005128841e065006104144e8802881540e420b000300300d011006948502d103461038a80194420491480408202403d01c0740c0901403490a00080050200080d000b40c0025480340d07071410031100201c41948000302d00c00c00303100c902d075041c01002408200c0d28400d5003c1c18042515036580c0c000040c840050082d0b800c1b60b4007024001c104c84508062417440c10031400d000262003100445041c1408903010400e03600301e2102d040b00c10030081101080c955020248947c8140407075402c1c071801746030400c041c11f031032809000500c0c06140014423010010007009030f01c0c0100701e0303403003151104009091288c01c0d080f40040840d1203402402d0340020000e100d50800000d0342c4010070003039165145d040c2000000c040c2c500c0100c40072102440f580e400f41d64429010b88500d241031829200420a0004c802c018040112a2050100041014002103280203c0740882d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 999063363 1250 999062113 999062117
    0xb010b0d02070515011a030105032e14150108162006150906150a1d030604120e030f070317041a0c0105180a1b05060409150b0712 57
    0x80c94846080000103845014400361140c825180c0c0400407000c404040303412078803081d04041003a500f107440540d0921083c441c40f503141c0c1c41041d001940b18075200c0e018003580c0c004505152201c9009804405569241d00c11000e50680d400030800070002d4900302d0302040d2000d107010542d528105030a0551a5100d44030302c000c005240d40b0401020305011007800705050020210798041c90800030561041e090030f510035005803401400726610707041501210b4803480790030b44d51310304080e807003442103032900800060704201d054070a11548158038140801e501441c019984c403125400e42c45405025007418201e514041c1c1c4c4000c2c22640c82000100f008010749602084012107a2014090705061b405642c0044659106118070b062401042d48001c00300f42000f0030080c8859540c50002a802e90120b09a80700c054201c0414400040c54507034018142e01580d00b1401c1319a525240410440e4010b600f011090030340d15034210303142040b0022520000c4c00700038802c51500680da6101900c0c07181d400f0640b81 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 999064613 1250 999063363 999063367
    0x203090c011e2307060509010f2c1005181c0e091305071d070903170904060b041403011a06040506031306090f02040c0f0f050a09120c0f060206040b010b 67
    0x2142526143c81c50040700d09002101c4d49515541c10070000070131054521440303540ca00307049244442014050600c8041c84007a030742540c8240c220191810107104411580b182c0101c407400c010318000c9110701800796500003c0600c0400e05104914a0801007585180209041c1c86041c1311041c0d0212255070600c9054071000c8a075240c2560b001100000148014614080c00d00d0200301b003d603400c3c0d0308444004204030702c030003522222000d82e404005070002070940b070806070803841402040b000030061074001901c0001c0d4980e03101609445c903040b5401032950103004a00000480c5402d0054001d80a00040c00e9076290803101d00007455071056100e1980071325001300016440342c034105402e6001a130014824000e01c0c1c0341d8030340890304111440080788a240303845c0401a9540c8100d6402d0b84482040d2118040001743d61010340d6950014808102048180000403921900c900c103440361851143c901081039500b0004090320302e201c0c2c0c1d0440c40840d0b00c60b404000101d051114854115140414441c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 999065863 1250 999064613 999064637
    0x90f090408221205030304051603020310050c090405071d0312120603191104061e0501200a050a05060f2a070b10030b010602010e030904020d060f0303030203090c011e 73
    0x207254030354030002d50010f0800d400418060040001d41c811031041040d20340007801040d080407260210b002c0a034040d403001400b01c003900040d80c04540c006012443c907600340a100d90007e0203840341101e1910019004007c00d01030756043d0003800c814003404601800c202d01001c1030040060080a40021140301940003244039501c0038000e03038503207407244c100390440f07040c042c2882128039032000111030280703103804000650301c0b800740d02104a90300c84002041c4030600d458011145a40d01d02008400055014949543d101c000c01c44030140f94820005007a13103140e10704109050000050029003002c82c5081004010703601c8280040001c035a0542c10881c0303050305840340840d4004d4000040a0481620034040768507400316110003201d100d14100026aa00c868048cc03d0b501190b2780e2003550707132043c0510784003440c090700074100c00b010100780020601d95600900f47c0a1307c80c0c3e4010b0b00401d50000c14403900140501c01024480700c01c0c03d0a00c03c20046040b402140c07074410a0f00070410039648481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 999067113 1250 999065863 999065917
    0x20705300d020c0d05060f04031b06140c0c0628020a090305010b19060c03121e0609020c0d0305060d05011d070801060b040e1f140405130209160201091205090f090408 73
    0x440ac84400d6411128200c000b51402ca401840700c00891910078048a00040203080b0300c4d0100c0e840d0000c180007174191a1640e0030040c40300f00515030880d221000034030f940d00000086201900660b046555400d62043c0f85003025030844060890791401004900711610f90700650711a08812111185460740340900c490904590104e0784400c000c140a0030300808000300001da40448560802d920b204001040d5240a81c404a01c1800304514550f08851045c3d020381d80070758401d0394450b0001d00001401000b13039445900b1110000004d01608405814141220004000ba0f01c05010030500810000c1d092140c0710042d03020318402c400070303c5500c4001440d12450745050304801c0210604803980241c171500c900514142040301c0314002c030b18140c00100780c0d120079059400856005003169a1589a0918002160320980003020540d900c0314003100004035041da40c1c0040414658540d40c4071200201040400800085030034411001c103014040411000000c6035038a10034400e00c54001d082d86050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 999068363 1250 999067113 999067127
    0x11100516030f020c0a3804030c0e010b0306241308030408010c02030f03011509080307031d010804021513030f0c17070303020705300d020c0d05060f0403 67
    0x440011035030200c000408041c0c004001104441454096402c00d081c00740a01900516900c122541544c0d40d1413a5140030b0022400003c0c110f40c0c3d0180340d0f048856490801c000c551050344115040301000400700000319184c410603014044664500c0e18508101002031524403923007090000078640c0d104803580c0080c10404030303140140c810f0080c8108607038503111151650420b109260b00395080c41c1d800c00b00c40344040308840d00034a030240d6090459007411078581c2c1540c0314204500500400141c0410101410030103840c0d41d0b44682c1d44c20791010340a0914080c01c4807210340e45410f02a0401c1030000594681d076088a0000142c00426212840c0d400310340c011070b025130300150010311003003602c07000d200c181c0300c106007a1390340312085100005a04c2410f543c2c45843e448042d0058200900034480303490300001c15000d64082d17400414120107580842040842084020b050b1503001d4901e650100d40c0501c503041d1141400c84154603499255101c103a210307900241250400c1d580035002608042c05860 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 999069613 1250 999068363 999068377
    0xc070b03061f0e04050730110310090b0607022d1c06050618010b0309070f0b070309060206190b1f080a110a0f0503151c02090a0603111005 61
    0x515115140c0b0301c4000034001500c0c09540502850914000404083c041c1d01002180d400f0409800215131180c44641001c84002c1d0440b03582d1500e82d88449046a03681001d14041d1003511070946809250140c0502280c82050f601801414103200400242c1d884036804031144100b150621146062004510340000c4010401130b404610f00501100e8800400202c200c1d1909c9030008200707580b42c042c100305c10b4002182c0310341b0134640c1d840018848415070702c02843d04250400200d804030398540c0482068600c20ba00089406030b0f001c0b59a41c240740c1d2004408009040900140280341170407036a1840d03c9180e0390600220320385032040c609032529100101100b5614203290b1040c84a0540c100800c8900d01342c0f404c880c0780e402c00c00450807001180045803680204c0d1744401030644101c140079103941e0030046c42501d0b01030003920100d0403038847c80d00d00095102c0d2114224645039140c030400030703903082c041c02e5440722626041c41840021440da10110407520f0031582142c02c0121600301315801d115450b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 999070863 1250 999069613 999069649
    0x8030a02031e13020f09040b04080c0c0a0e040605181b1201020a090e09060c07021e09040804080d020a1104050c16080a090503060708010e0606162102030c070b0306 72
    0x501001a5000710301c0110743d40d0791003101c1034403c0c80520020002200e2003540e0141800f040d40c0081800550968014413407003070110240c40080384e1a0700090030b110a95406940c0c6a40101d0030401000128800c50394003400801003280c2c151900d4074140d990710348051104043c0700a40000480955640c1000c41000078400000d40d0b4031b450b1080000d09007480751140c07144480c1c000c0d003c81c048410200c3d190b84a4450703080f1507410900355800b005036024107950178055580c6112a45003103515038201c441d11135409040c02503651407038004814544110b03020f41100b150000c07481240003074a0702d2011007000004440202e01c54640785201e507020b10034100c80d50301d41424900f1403410081150003401c81d000d41e40e12943c115075598401d145c0c80d494100c503001e00041907480144030b008511000546c1140700645454180218070f1800a102010b00c282981c18114452502401c2246c4004042407207046101950405040810843d5120880c0c0140713041e80d10003100080307040d1a400341440d120503401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 999072113 1250 999070863 999070921
    0x30605010b0a0f09080a030302130806070f091d0a020d062303010b060301050105070210200c0a08070503030f1c0204090506100359070504050408030a0203 68
    0x90804291940c000c00c02d0b500030403415416802040c0c05810036004a0319410050600700c1e0304d0347d070120020b610540c100a400040400003094402003000324910400325503c92030ba501c1030304e0001410041040e40701442c48400310000c1d601813086840c00c50f4101c5841880943c0340c408019004002d40301c60741000940007880078018450a40c0a1041e0041c840d003680200000c00508060001c28407003401400d0120340104030241c01420012151210820a440c203e1107100100c40c00380c240302e2034191180c2c0c40b5404803210000d90325014135038000078940c039001040c0c510321f0000804d07160b00812540306000b0001041b902c100c060040e4100c400308120200440d525070b1139400c640b000b080f05643c030601903008100400b10141c002d2041c01508a034600c0240c1f074041051088a80c032409050705030400100300343d95846036082d5481e40030960143e0102058560203e10780543c0760900ba60301c160b00c01c81c11700e000d02000c603050f4401c40707401c40382212000d81d5030b40e82c070a1410012600100102004215 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 999073363 1250 999072113 999072119
    0x521030c240108060609040210020a0c060c140c100c051203130516050f15070213090b22030f11070801020301090605220c1106070e01030c030507090302120703060501 73
    0xe920118954a01801c001c0c252030362a003401e90340d5030500b158070130340161705800850003501d00121100700050b9244125041c0303205640e0b804803941d8040e03000304049101c141c0c00204124042c031440d06000602c0c40285280303049680064180100c0c40c1255041c00802c02e9200c0500205200700d5400a0012401c982d4904048a180721491090301c03040e05c503030007410309000c4001440c010a05c11504e00802d13544400244c1e8081003518105414040c180c0c0000700500c4006031250030000303800d078045440c005503440700c1d41005940500c0051418a0b182084840d6001801d90107000e24a400c0d0180b80180e9181d4075200b040d58119001c40d0321030390903c50721a0000c0c8121b41500214145c411200d030511070180ea42c01400a9808202e90b0030240d40c0b0036085104a485e101c3e48290f02100b034510380300c0c1c40c4124042146080c560142c52800c0060242c0c1100c0c540c550b054007600e0015070ba0b81c0f40801041c03405a074020240b42407400024860719005e010700c8408441085054081c42c2c002c8420062965 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 999074613 1250 999073363 999073393
    0x522090c030e28082809060305040302060601030c200d03052211040914070501030b060c1b0d1a0f0c040302090411030c03030a0c050f010203010308030f060a0905131b0521030c 77
    0xa5441a02c1700050800c0c8000ca000d900c240074060049506400510484e04d4060055015100207210041006406282c8002985017184100f1040c914600500420309013210002d0a4071001001d02c10419503030f10fa039402e82a009460035490507004000c41442540d0800054060000c441f00546422410201c10303892480c041013800c00c5400c02d0b00c1c20444400d85105015071400f03010032000940e000503044010210205400c031450601c018400c803000c15031075880f50030600c13684002d080d145083c1b00821114442d040300d40d680121400e8425404c041c5164000780303841c140180020710340601e00901d11400d4070100100c1104001c01001e4944034200701e42c00500020308945c00b43c03110320904001d8070300a001031080300d05803600305801310b10b1551003c00402e80c07450054a01508001c0443c0e0006203248207228079402080022000c4040e00c6640c205080035241c0c00d2400780500303000c00740c104010b644d00104100031074004100780341c29050011300c45003507015401600d200f40c0240701052603410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 999075863 1250 999074613 999074677
    0x150109021c1116110d0305030702101a06090a0e011401091a090d290105090a0b030d030b0f18181c0522090c030e2808 52
    0x1200c540c549241507019a0031809503208100d09254815007007040d064410150f02c2002907460151000c40d0144013a540400e03000d6000600940c0022008030038020200da040c40612102880041c1c00d102c207039590044020800002d606040c801c2c0d41c0000d4504950320303901c141000800e0900010001980e695501c5242040c21202d920700003070040201052982900e90184030440e001c0b40680d08040f404030034452607002840007595080d03003000041c88242d0241e5030000e00c1130a8041210100c0d423428042c4000207201070b02c3d21038140c0c00c08038020803c2d02c0025424481001c01d1070007049200100012030181c0d011030340c00d40d4103d081c00f640d5914200d00c80d000c150160180700003103518080030f40d01035a1a401031101245040c20080000c139000d5210308094043d20b034003003a01c07006c01d040307a500d58544894940d20070030347c443c0c8440d440400e85030588201a06140f00c00050103140b89141c6151041c8244036520040c2c01d04a0b51121092040d1042900e88410031071031442c0306103013071000000f021 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 999077113 1250 999075863 999075877
    0x11060c0115141302040b0403080c1c030605040c0206091b010504030f0f0209071e0c020f100201090b090a03090521030a030603170702090f0403110a0b010312020303010608071115010902 81
    0x112003030790079643c40340c205100719412548869035590030242555a00089640035400c90310f80c0344120f004801c140700240a901e00410865140022a185004140300a558030065154150340280c010007d0b4404081241e840746000e02e03008031510890000180d809015540016003400c01c0655510204a4400030202103d402101c0d4171440c2d540303040d8110b030400c401c10f202d04440707240d4500422026005001c50402c41e440200034a0100302030f0382c0810820310002409a0042c2e454014000601c05481d4105800040c4600903060003001d40c3c801400010145c0300d00c0d8000d260f85501e007a54440c090500608160925064a40e601d0200c48014040c000c0e40c0402e944034101403607414281100300d0101d5051503405003210b4060343d00c504280d5805031000300254184024502c86d410550014000d401c4064070030103c40d0020750550a2a44034015000c200380c0070b55108100501661790001c3d03925502a403207140403280c01c40c0c140d406604100480c0303070102401400a0020414100c2c680140c801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 999078363 1250 999077113 999077119
    0xa20030409021209060c07060207060b1e0112020c25030c03050d120207021e0103060302121e07140d0510020d0c12090b150f030d020d12060311060c011514 68
    0x200da00c82000c0580c6500f016941c1c1b22100c0b00400180d0000f0344590040c290301d9001e41d10020b0034400440100308028844e456001e104400440c10035200d43c0c02048503841c0140070a8214140162104101d03661010243d04c00c22035040c03104890b81e10340c0e080014038091640034078440f000300c1d0f8900e82180c2c2c621140b81008081008006409102091031082d0b5891b1a0024440d0101c11710205080d908500c40d40c40180c101034841e2004809138440f80c28801c0000c1405000b0311100c3e0101040036002c2072042c50310305958000174410040036107010704070119081d085410741c515a1451505a00d46080a0b6294044600200d1005880d0507a64002002c1240e541c4880c0d061391266001001203c5d40f031240200807040d0040800c40b032076583c40040091036005071000184410000c0004d20b815a20404080103a020030140c2113080d03480000e01e06940d2a419082c40100c0c15030741d07031441000320181218054100440d9005840c0300c250407461010300c00c01403c050302c1e40c40b448600401c3c284110842c1c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 999079613 1250 999078363 999078397
    0x26240106080c030109050c1303050606040b010e0303030408031f2301020307051203100807090231060302071a040308060415060e060a180e01210302030a2003040902 72
    0x103605401002854410b080b11040c1034078580c2840141001844050320301208544140441d8000c0c0140b084001c0195024500620541ca0b1020402c0151841e1450040c1000088018101e1644001081d030360010fa1192501d82c4a50750b118000f80c213600482c0c1200e4541e41201c10000d541380c05010703002b540e2010720041760805036221006a0366031240748030040c807076484a01c0154992091101840e04409041081d499003960f03460580e01d400d003603070003500c412640041c218400900443c000c005442e0040d132010b0b00c207805c082031080d04007614070481c01850380000e0305004101da1104c006040001549190304107080c1414004c006810444086026a2070803084c5001c8000c9400f1071021502c56648034180b440401c0213201c002e40080c0200001e2200c41c00e40300780415061891039014082d0780c0500d82040d807401c0d04141d00c0712101030140719900c00c81c400f00000729501004036040420581080324919640f580300d249150034110441c84640404500455000103640003460040303910300c9050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 999080863 1250 999079613 999079619
    0x1302070b060103050609040f05031308030d060501180312050f1c0b0303090a03080d0e0105070f0314010b0a0513050423010e1e07020f070b091e0901262401 68
    0x143c1103900554030240e110500178001800524030f04002c00f0034500c10402d80342040b04081445203041803d070400b01030341c0c0001ca030080c644101449000010a800d00e02100c1c0010702840300c0700210007a01010388a07100e801d40700160107004c2c000700c54504100d030203400c0c2e03a1083d1119625000b0401e2024000e000c3c03d10603621410b180001c01d40e81003c0e402800401c1c900e1850b541c001e415031059966410807038444608214581e401c2c403d140c4200c0003a2a0320384400000340d001821185032480e403500c0328411034018040010000140d41e81102d50b414207a43e02d00515000c0c0c2c0b941b00c0c9940c4495800360074141e41040000102c000c0d44455408a056515a0303600c40582482488013220450040408280b40c2d0b030007121003140443d00b000c00790064610350044501c02e02d0915105402808140038001030220107400c000745203240309810303407180990011300c000000c0d00201c0c041c0301340c485811010a0b00114009480c00b80890304039420100c440352401110540644601d0400074403024001ca0000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 999082113 1250 999080863 999080867
    0x20619270e070315051c05060103060c0f03061409180601060207050a300c030b07090302010f0e0f241819032423090601080a0807061a1302070b0601 65
    0x14413601140d024039071003042c1042c041c0b012000948203540c0510381079560071008101c1c144001800385014101c0030440c0300760160003819080c00d40814404052628004010240344801e000a210008a80ba00307001d886000140e01c15030710b44908100700340039000000a8040c1c0008151003203607000d50700d6551150381c0300c4220381c000360f26003040c550002e00d02c01180c254403000d01884040030f1250844003915074494075559003554040303035080c01062060005000f55070f001038041880071001d240800314072000c10040340f0084050280140a20810300007401e400c0d00c040c007000c2c0070718a00d0151a48524441d01c0280180220000c10b9014202c200d0541c808a03407841184401c0d00c0c0c112066144003803900110400540705488038034040c6603540ca100f05407410803e201e200e011400a42c200041c10000c1481c3e045c01c3c01a27100044a601055074903001810520580300c046400c104005500580050350b030100d01d4804480b150b000021151940f0648015030250075035900440303201c0a40d81d0b0305001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 999083363 1250 999082113 999082121
    0x312020a0e0a05040204050109120c0f03050d0836030c120711010c03050a1b06060e06040506220f1d0f0f0a030504090911060307030b0301051003020619270e0703 71
    0x5101d0010b00910020b000030b500664600e90074621904401c0cbc14165030b103080030007510355a00200c400f50013107400c2001c2c840d400823120b070f00981110030320740b10040d003003250820307145000050300c0120251014220b40c0c20740178001d485024040d407085d0341401e400c2c08144040c950025204640245c0321030410507003544034650009401e80d05468403880d082d41c84900b42da04038941c686e400104038505c416003001034100d0041000400c00100141420f0410008100603250000d0501e805900318001035401e400b605050022205600c010006005a40c0c05505015100100f41c007000112440c0900200344c0c80003c14080e440307228400c0d00c26003060040c1c09911681d148a024002501c1070005010015042d404170300c0d031501c107802c110840d08554000c0b6030b941e00115090404242d940101d2041800c081c00303000c0c0d20444280301d00e0b141c0f40c1180c1c001501c6000d409d20189400000b200e5002a07640034000c1200039500318410101d00c0d03152094285000707001030080500040d154804602202e0090003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 999084613 1250 999083363 999083369
    0xc100f090e0903120a09060f2324120f0a1208010f0308090d15050a0b120d110f0a0b07140309100e2404030e09040b130312020a0e0a05040204 62
    0x1444c6044440b9848001914010780300c00f100c145d0364080413000468a2042e080030700c08201000c80c41c0312103e40c0303500d40c1780c214410384a5800440403c10010341410a80b080342000850f504101404042c004039226003224400d042d2144180c5025621281d400107410b0401807003086840c3e80001e841c41e08540b11036080c42096030110000310240005201c01e00501030b0f030a0040c00240d00c6240ca42c030341481480c03e2805e0945510f40e5142401207126072030007410300d40d90003595909030041c1150001540c0301902c00302c8108201076200c039000e0310b04082c00082c410320352000c00c030341070f201941c00c0c42c1404801c151400c50104806003102c181821402040c2c0e40300307282c90000b50075846c0002092401a040c082001c41c4640604815070038912980006000740440000300540c0030b282034a00904011305900d41940300322101000c100004c3d1302d0341700c01756000011000c003a142c1c051030300d401da945140b00c0903032900441c004200d019480760b220800c44014101140c020600c140c2d1b42c1c050008030300c1140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 999085863 1250 999084613 999084631
    0x1022d1e061e0103020607150231060503011e0506030108010e0c010c150504030e030a0516050102060f01170109080f0310050a230a08010e030403060606031107060e0c100f090e 77
    0xb00040015251402c0681020750041e200c0c144410321089100c4101e80c881c0b201a100340c0c1203041d1400a007241005249070380304a040c208034805051000240103404148540d07011701e90003030540c2e4151014016544014400901101e49950711001c48902030701c4034100c110801d2098000b4240690310913004407604c6608110481c00c94a44200020301810000307100780c1c103100c816060340380e00703440410a00a50f1030154000e000710305100c00c6400145541e90707201314110350001061100c145203d82c6030300e0454802040050407004951940c50140c0151080680041c0011480c0e02400700d40e0002180314110a040e4426040d40740d10800248080d14040e0352240b0480d8a80101602020020400b104100411050b00b00743e407402c440742036482403600000940c001040401c100146405800094001c03030505000c11005110b10794484d0291010141016031202c0c05000d07060310134022034004e080058000d02c55000015009007061070514040c900041d40102e00088410005038000e004190b11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 999087113 1250 999085863 999085921
    0x307090504090614070512010801021e070f0f0305070506060409031d010e1203070506090c06120a0207020d110a2c060319060c110c01022d1e06 63
    0x8602408000e02d452842158203503968581d02c0089503c08540c144200c20136610160303260420302d151042c04e00b06034051049680140110070071042c000324401131440d000441ca58940c0c815013440c2c920304030300c0030380074019041c07042001d1306041e800402442410b014000b212182d49850301030008407504860003500154001d8032400702c3d0040d014800c40311031814540b06008000741000100407243c12800c441e03980d8800609003041080500c800c03688480d2a002408034800710101180d003504c030314000c0c54a402c450400003501c01101d1b505030b944040c3c000c1c0c40102c560b465031800c20441d030401c0a446221320101040040c001000005091841c04000242034069030115140542c0701d80c00f40041e54540078180040480803101007203588070307902809002c03a4001c0c200303401601c01042d050303440b040303a0040846c004140c0d800050b5210710400140e10318803035580f007070440c45805449a007580c6944c040c6a14002440c2c0303605403841c00e410788210541d80c260305c4814019018107003001002409061b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 999088363 1250 999087113 999087119
    0xa0902120604241401120308060a0b09010c0c090203070903111507060b0103020403020d0c030303150e071257080919120806010201060602030d050c19020d1103030709 73
    0x241d070405600300d29610b5000300f040c45404130300704a5038509800c9141c28258802c4080c0a140d401800690003a0007074807405c41d03090816a03210741c184102a4940d06110035100950200544080000e00401442c00308548a04200400400c80c141a20080e600b10b0760030540c40c030080c03902425080c4c8150a0000303c6140031030507900c0c107018159007021541410741c240070002c05610f030201038101092050780c01480150541c0b4000d000c640515040005081512005000d20404d0001c0c0c6904103401e403d05031443c0c100c6003031600241010900201c0c00c014012400c4842c41803003900311845222142c4050841e0401d111729003249c80c0411b6062588079907801882c07030001c1c016002207800c80760180c02e803040d01d02e1a018499901d24a80e404a4104030300d000c05954a0742e0191380307550004800d10083c4103191038800025035900405140c001410342da240404d024040350b50885101407020654245900c00b1000042c0d01c1c0c00c24142040701050440481d400d1103040801140c1c8650f2140d01c0d0b441109003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 999089613 1250 999088363 999088403
    0x1104090507051b0f03071e44070209040615080709060902251109130201110105150f0118090b0a091b03230f061203040806060f011202030a0902120604 66
    0x84262100c2c2c40d014514a030140455015280c1d911169201103042c48c1e9452542d8041c103000500d42050501000210280b00766940100100c910303c54044074090100d0310f480c2880002021440030040d020360010500040c10381c00810128201c3d28811001c104440d13032100540d06034419482004c64184003002c11581040c540c1c26001ca150340903c2000c5004e21200020951011065845100858405c03850350115a0300c02c01c1d181166030010001c0c0110706280c10803e21000540c1c820610440803500c60100036403250309600d083c0400e0b20914a0407640e10a0490014000140118080c1e180114041207070003050151f104510342710343d0503520805808030114024400c40d82146041c80004000b00981c191a00716035000b03102214000800d41400810854940c004141007012500288010080b030035010a030f10f94420f0045e504030495001c1000100c56030b07490300c401d07110074130700c08024031100c0d004030340c02180c410b0b109584241c055071000400a40d40c0004940080c0012103564450000803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 999090863 1250 999089613 999089633
    0x2e030f061d010203090c0f1c1529010806090f0403050307050d0903030c030612080306090c0c150103050c04060825050409030e13021603031104090507051b0f0307 71
    0x107200011645801900c01e181c00d820790744107a952031001d0740059401006440d0054a0711210309041b58400041c5003404c031064407440c82131402410484c0a20306126507070810350804282d0700c8403d06030308990768004072034011800d251101a0700042c90400042da480c1401090700e8041c50120740800025600e40d0b80417552640000c001c0c10030020305200d02c02c0000428000e040000384682c4010a03441d00c100303030060491308158040002d0390911541800801c0605003200d801a9054850304041c1e5035050800300b00d4441c0c00805d00319031085244514040003842c14a5040c0e0b440354090361803100081d020801075820600401d10746400641c50041c0c010588148098058026860540306550b180f00003400c031800e4403002e9001c22615010032a007450108081d107022941254114181080c44504940c074542d80c010050615913a00407030801e075031504050307400400100900b80304503d8045401050380e001980070008004566a0002d801d602c0411751105801c01d0000079400e240490b1680da082d8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 999092113 1250 999090863 999090881
    0x803040f0311121b180c03040b0702061b130f080a0614070806120705130605030c04060b0712230a08340c050d0e030f03070c03030809152e030f06 64
    0x45a0310501c0055217110700c540d040e02c00c45025002c1500c91a150500c00f200311001072600045401c168104070a9510582e019005148400005510317000c200c4908180400030b9044003030b500c0000382c030002e00b2400018102000520a1101b8411b48184840d8111071041c10b454040100b00408002003503820020b04089040d20300c00c048407292a500c238080307020101c51608042e00701c0d888186c103101320300303041240d041641d100351010130409280c41c8040c1558000d040d401407a044d0031400c8030b0841c43c0720700310040c000200d181c05003204142c842c0c02a041e5902022404000c1007038040050040d040b090010300700141342448410a154080100b0540c0c0d660100e40c01d02444402c4540d83c000c00c808000b03079002062952204840300e0b1805080500c1c0101d00140385441c1e5004000d11400505a82c481200f100d5140c01c02940d10f45959a80c103041003049461000001540f908203c020b504e0f0908628a8804600b8075807040c000c1e03100640d00320925400084c00d80c0406d585040000b40481d403003040740c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 999093363 1250 999092113 999092119
    0x11e0b04050105250b04122303011e0312020102030a0609090c0501050a0302071a060102070e09190213050a1409010608061f1d06191514040803040f0311121b 69
    0x3a01d1203507920724041c3c1c641940c0c20388040c0d1801f1190b0020a811403010b4005508105001021210340001012148014080ca020f60220304031036280010303802e0801c0c0c0203103910180030340b61181a042c0080c002e4100316000c0040b01c2c104000040e44c24403900c07450f000c075a000501a50303114100300054a46034001d89080702015820802500402c0300b80c064819902a5086507101d6410454002480c050268008451543d11802070080c02000000c0010250716400721100600100f03000146278480040b240d6001c0a05180421142d4640b5a01a208051590002c00d446480340b0b001c180c01c071032140c000c102a0b03030300200c040750003d6031a440c0c04c0701c1c25404135a609406603c134a60141880b4240300b8a21234107148000b0304c015403030100a242220314030100e1443d142031900341c04005900d030b01c080c80300034042c6450b038200e0305507480c904a4000d4180c0404403540c9555404002481081505c0140c0344e80a42c0204200310749450800203103018183d40080c410034a10b814000c000d074103031140140e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 999094613 1250 999093363 999093427
    0xd0c020613030b010e010801020f12060a090905030a020f0318010804020411040b0c0c032d0115151215050118150c021008041e0507050603011e0b04050105 68
    0x600d12a03060741e503805144610303036829181d450140143c504140603008800b0990040c40540301c1003041c81e083e102c6951042c0113610150300c030b000110f1082071082e0403c6681c2400c0000c0c04040c068000300609800f48203a080b82c1d000d1b2041d1801035120f010742580304048500c1c00c041d46d00113620801c001c5800c20b0009000142403c1c2c980115201544594428440c0c1c1901140002400710140444900c02c08250301400308610402207004801845200f012160442180100d01c000001d42c48016020040e803000e0300710b07580394480d540c07601c074096061500050241d03500c01d0703508440f0b000d00301003c02c1104040d40060700340b0380196a0307130204040400d411050100e0019a642d0f01450b82602c185041c2c682c80f030045514018003458520001e07200042c00b44240902c40011142210555040c2815450003240720591130418140480d81d032000d5441080030002003042020803c00780c0641d900320030314001c0183d4580d4107041034050b51084901291061207050010741402181a0a40c0351340c0705941 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 999095863 1250 999094613 999094627
    0x11120d0f090506040528030c1128060306080601062619050c03090a0b13170904051806160309050a11032e0207050c030d03140a0b030d0c0206 62
    0x140440c0c082290580781a0301081c14882400740910450114149200060f0311141103000d071001107183c1800c00808100b40341981000303202042089c8c800408004010110350800103029a05210105080ca9911502c0c491700050b0305002c0d03c140c900301c44049024002c4c9a2802e00140c6466140c198591020610f0a142c4a810766840030700741d00c40d101c0e00b540041780a10712020710741100c1707008040c52031083d8200240b1110b030a0000d034010a5541c40125185943c1d40c458403440c0e204501d05008080c04018100c1440c04046100540f44211096408002a941e5550101560030880310701c0e0100d9001803000c1030a451103d81003982552050a004c5040b03541c641d6650b00d409103408054031640b82c0341d09035001c24941440b2008801c3c80900c1c044c20040403c0d40320141c0814540000d40e049030340004e040302042014032a940f00e100c401030076204120703014100540581106000c2d0600d20b4044030028a1000302845854040540903004040038802d024058405070780ca80001d9034020b4003070010b2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 999097113 1250 999095863 999095891
    0x13231f141204140322080706030e03070b0a020409060801060509070305070c0305030606190507020a0611030909100503070308121b090613090f0c0e060f070b040602070503270111120d 80
    0x1801045c001c4031212458075080c13585d818603440343c014004050401c09210001100002520042c3d45c01501001054455082c480001d115607071042800e6400e104002452041c1036000c242110001e4506212665840d0811400c64901f100c00c203000c1400032846a020920410246900c8000545400c0c076056140d900060000032940c80580082c00003d0340c0b604500700b60340c60340028070907420720108034030249450a880b0b008004840d80a1580e0070b00181000503030f000340030001c180c0501501e0800e61a402c00940a621a02128004880a20120345450b2185071608041d82440115508204d1080100815a03005003200c15016148034000310740d4941c140f01d0340f02030103000c150004004201074400b030460752261014911804c4103101c00e103006100c080840308850360082184031076542c0d6244c030344024015601c000d0a14440440c002c2c0f64104080300052509030250f1200040f05101801110001199103031a621a005241c040201032150000b8140c40e140c681404039410f110396410b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 999098363 1250 999097113 999097147
    0x20c030c0f100c29040519080a0c030c0816210f0509011206080303070f05090a0605070201050d020301121104020918151906110313231f1412041403 65
    0x351146014406005c20088100404900f2011180f001c203042e580b5500d40c003881d4040e8507912414010080c2e00c0f0020113114071548182c0c1740d8043c008648504100540c3c0702a180050741c2292101184020418130509017490004544980d41e100c0d11044266941100c098010300c0456051044038031004e501c44096000c2e060207040140001c2d40c8034507200718000d1022650713108031420300808000c1620741d80c840801c12000d85049050403a0788404510048a0502c034035007564684a1011002042811400e5880901d550144100303041c00e4510000704000c920498030070070740c864801c6058070100c07040103500070b501c034817128900501100342d1000f00790450301c998503003504003800203801c2c80116040741600182c40d10100c01541000078601480751100e103280078900c02a038043c4800085500a0260385002c50001341111748510441d03200c0391000c0300303107100350400b09010b0036144000141c1d40d8262007221a40048603446034546440d0000b11070b0000e24407901d20f000030404c480c090624600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 999099613 1250 999098363 999098423
    0x1140d0b04030804060f1505240307180510050304020f0a230405090a0506010306020d2a020706030c0c0f02150c06010f1a0307050a02011506020c030c0f100c 69
    0x2101e421615140c07520408940102c5038401c00c1c6c0b480d200504401c250700d14000f000395441611310100c441e414201380d242090095013200c2c00d00300008100b120655200c1920700b020a01c00140d54440e40d00c802c10448080e05506103000050f0003403000030094a0000c0403038800c03040c05010822180d440b1840c080308607010b0503e5005d0704405c403880101034140740c487c0507807014000002d41848404c85c3c0c2d5507521100b0611001d0252500820f44200360500ca07800b00c0c5c00ca014842581c42c4c8030144500c0380c1b2103050880c0b05800503000300000041e421f802400b840c00401d44654031214084e4180d40c0f6000b0f0720310b4004d01079030010f04020564865800c40002042c0c5e008065004000315854100c1025000f0513a400c07403a000d4a2000350000f00f9052001038076081141410300d02e40301d80080808030300401d00a403491030301003815900001c03d1a004901c2c416950000e0b0103554240d4250010302c9003601d0640075668002801c80b40c2c03a0550340c400d54000d07107403500c1100c3c8150a4141c2c00f00010600031022 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 999100719 1106 999099613 999099617
    0x23010509040209150d0b0f0a061413060803042402010c05070303020d090b071224061b0c030c0e070c1109070908030301030503031b0c0601140d0b0403 66
    0x41000d1070900c00c0a025174000201c5410561074000064075580031007289031010450101c410302619094412452020b80e8041d0440240a1381c01d08281690807407540c0c903500443e588000b880100010404a98040d03101444a0303066071401120070920700a41e07241001c48070ba915040350590340d03d00e415040047e2500d002405600c003418910310000c1482210a00300f042180d00010400c1030305803400410000000d051207030390315115916030182144d81031500b04000c101c1c85000185d503500585000000d0a10081ea108410030b4060303001140e00306103070001070100c2403581c075081c0d600c41c1182c50048031025980d00ca6040e0202d0301e4005034060746502c00018180743c001c0e841000208054402c8035540c0d07949040603600c0340c00c20f0f5403c80d003200300035103192250440303070051354404c0c5080d00c064840b0780d1030710221218086400d0b5907079811200782000c410205000100f10340c8500c3c000e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 998920863 999100719 := by
  have h0 := BRFrame.cov_init 998920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 998920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 998920863 ≤ n) (h2 : n < 999100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
