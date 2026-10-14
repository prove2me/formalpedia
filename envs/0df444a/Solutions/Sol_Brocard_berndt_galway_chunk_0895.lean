-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0895
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:32:42.467817+00:00
-- url     : https://prove2.me/submissions/39903377-7dcb-4517-9153-edbb47809460

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 160791366 ≤ n < 160971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 160792616 1250 160791366 160791373
    0x3020310030210020d02190b1801060806070e010e0109060806150705422e0b0a090b03010308190513030f150207050606040c14031f08060f0601140405090405 69
    0x100506c0d81804502240000c00080304244101502d82110400025101d00c0e401c2489640301c51030813000b540f10000030081c0c80d083d1266840c203180c010f4865003469818030b004c00c0350201001d1440d03200e80404010b6603003544070905035488010520115a60545152074401740402c51080401c030308100541301148075044190118640d0f05002c4290200c0b0154079414040c000000003001903203200d1598032080741342c100390b0410411807e4522a015000303e0a1141001480120760302c241d0100904840c4225250701c0e211315903a00c4016101e10007403102600030740003407000f00004840da0391b01e03914101e050329220b4100340700003114102c1303d85190b208840359402d8880e900c0070454114501c1e0340c680d44140742142004840d44610351550002000c01d845203644000f50700c4140e00030b0b031280b070101182e00c002948070328142c4010150003175000d5408400002d40800042ca2000008074140708012880c559102c0341c4940c0c0045d906580252461180207005000103d22510791040407441240141e009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 160793866 1250 160792616 160792633
    0xc05070b0c0403111c080304031e0f0212130e1512070503100c0e010311130305010b091005011706060f0307020303070e010f0918020705010c020a05160e070302031003021002 76
    0x400c2e080030581681d40108081c0705d100640b66040c004100056401040c02d540d20f42e41e902d812584040d125030490b880710014090026102d03445203116500750b180d03400302e40000d10989050021801a1112038124001c1c9910900140c2500380c01702c1d13042984040b101d84500e11040c0010314a07809401b8000b00c56014003c01c002500c2c0401051440c0d51546404025210448200038103000b44444c440c0d041c5034a6000181d051a144011a0107811940d50103a003c2d68403450001e0191450b40344191241c1c2c1250302191108150880040841d10141c460002c11400080c441195400003444980c0c041001c2c0300419881054030000c1d1b20075000f990140d41e4901e861407000d0712400214214504000720131408041c0b03203410400d081c061360a090f85043c5802000101ca1001e40b1a84034018025400c0001e41c0a0654000a0b503e104502c80d8080e210a82d40c8088200c1d508000c034440c41e1907010004020450090207540115007040310361840e00c1000da180d40100308260f4500440c0c400680c001c3e240c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 160795116 1250 160793866 160793873
    0x1a0c0d03020403030e0d14011d01050619150201060b1602031b090117030c030d0b1302070c05010c030e0315060109050a2402072c01080606130c05070b0c0403 69
    0x40080481000d0604605190560303c00902003a500c0b280c46000b6200b03803035941e050103146090b00352030703442400083c8490b0407203040082d50340300d004071802440d600700750100d071140c58803612100c11140c811088000c014a00200854110610f40c00102595a116404a1041c400c10001c000700040c1e9510259010a1481414501880f00c0168060010041c1e4000c0039a0b8403404c115044601d00580c840c40302d0545015035003103204540e14180207200c005141014113016400003800b10908079110300d000404542c80000381c1c0f14039540105403585249083c0410360003400303c0e8000500a01e0041540382c40c002c00f00e85454400319680030808922130801601c0c0d82e1260301040501420747d80801e5081c40d28103140c603800c1281568900302000d0424407001184200030440041148082480780e404000121510014000c40d9191400d4030900002c51030b001c0004030f49025002c0504580c0794074006203030764001403607584d02036008c0010810282c00403441c000f50440c05040c440000c41e075111326619 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 160796366 1250 160795116 160795123
    0x507140429031306050c04170d08090a0507150e0301020703030f05070203040503030f1b1507120209221113051c020306070c020d0b01080d030f15030312061a0c 70
    0x1d5106030810820400c00140d90202c05403061a90b03441a00072805407103540400c80180115004200780c05d0000913608076101c00080c41420a0000e03131140303a01a101c10030110b4842c6080c0001500544c0810000c0009600003d5440300211040ca41034090b21341e049d000031b003668003002040d4006071f141e05181c802011360344103040c2c2040c0c0e940001c518103850b180110340c80e0300030642051a0818085440041c419694140c2d107589080e00040c0c460360a0031000b440c454007003d841c0707040000c0042c2e03241c2c000d080c401c0c0300300d961143c40105070410303460042c3d1051300850102c842ca5048641c68040007a200e200303c1000d400845400c8194404841c241001d00c603000c140440c03034241003a0701601000150301d0214040e60041d40a00d0040540321081c00030580407258000000e1410100500001d1041d5000c5110b291805003541c00b48900a07804075100c051f9a84034101c2d0070b103010082404c000013030149130f010140881245010580581e21100c80016002480c0f2240403080006207056407500c061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 160797616 1250 160796366 160796429
    0xc05030f0105060a0207061b02040c08040506010902090f06030916090b091f1a1201030309031e0b06011110061401181208090420180d02030c0405071404 67
    0x156001401d0107581180203584205510a080a0014000b41d0b02d03580c040b0002030800231074000e041404480401400104950700031078003540e00c2c0c0100b40c008180f07a003460089030940800148001100a01c0c0c034104601540003610f22446446000e104203901c0b4012486040102052000003d1481400c3c060040c402001447d1200702c030101c0058003000100c290b42201950826005644107000b0743d002c1c4520340c45141040380108201d6000002050350062009055038416060b03d14480116a00d28440d440c1d070000090040000a0015103103521410004580d129200211920280d484d074003041181c41a401085e40224500c00124103540c10a44041d0071148255490380b0b10303403521000071001021064002c000c1c090004480000b43c0da250441003540b03081403158030301001441c0915080307500c4400720880101c0450410080b0385808014140d07a04d80140182c1300315030b050000c0100a0400030400002e02200c29403c1001c481544007510140580f46004c050205c00c290b170420b40c400c1304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 160798866 1250 160797616 160797619
    0x30901030c0c23070305010f020316051207032304050a0212061510120509070302011d0310051803030103030c06051b22080d031b03051e060406090c05030f0105 70
    0x1500464000030f110302d8480c40308012000d0000c024401244000750074081a80d00207041582030841c035101110140d802503004a0707401072404604020306800361850b00130f00300d215002c0442c050000300c0007806508142d0682440f240244c07850519442d22240c0090705031019140e582c000c5d4040c0c021805d28080d40e40107910214014251407902c007110104c2c074162032144034000ea100403210560030f4044c1d00595034500c0201814025807800020840d074800030752005034006903201002186d103900c110b510950503603000d40605880c464006405015000152003a2541c01c070300c1040b548130840600c01380d0301031440399a94001c0341c03003035042c004144d4601a1440f0800181c0c17001100722620064200c80d0210507018000351000e0343e6244510700f10340301794440140c501962031054400381d0315074481e0bd011a45042d103845144035180c01102125011106020081a0681241c10f5000640a20b43e88020002d00c040790580c0c507000701c02c1c15030f40e024100c540030400200c248003071010f0303a5034002c1c0074120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 160800116 1250 160798866 160798877
    0x7051603170105010e0307060c030203070b01060305040203070e071710080a1506240c02011815120506031f02070203010609020304140a0215132409060306060e01050f1b030901030c 79
    0x905c1000280c48404501c100070900c8046204282050f0092054074081900841d0f042c3c1c1a69603400007802912046500728400e02410390007051000d818030285000c1d81480e511040310701742c44561007108140141c00b440f80400c8d0010000780442e000c12500c622075200b6661000d10f80003d00c019010b44046030803401200c0160841b101070182520b082004601e0b140c58011a00041c030300060303520142c3e11a00e99145d00c40c2840210b5110b010410f18241d02285030b0341d0100d00100701900707004480c02034038800da0640203c40c42030b03426002070b8000d05c400c5200d0700300189811540e600107801c41d00694445030603a9008404c200034090750703803488468003a0280140c01c403200705a00041c60440b00f0f10384c03000580700c0414100c0060304407181d80400b40406a040c12801010140c0d0b07818dc1282001340c1800148828001041070b500ca4024041203e010f82c541070072441d10074005441941000034035078202c3c181480111009045d0600240209480b41c01542d03889081d90300050640f80c46078542d43c10300a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 160801366 1250 160800116 160800137
    0x30d140709050d0303020d0b120d0e010804020306041205130806070e030604030906050d060302060d020d150e01060305153106060801120602040308030405060a0501061b06050705160317010501 84
    0x11101c0025601103641341ca40141c3d100614146840140480e0b20401c0e0415201300d001d45105000142d181000074003616074041080c1c56400450341c0f030340300b210000d426401c80c00100b400180e000810581c10034441c28541d090903c1885904a00d6001340d1000f0099071004080c00f1940da040761800f01a1107094000d801c0034641924090300c1c580c110312880007005000200c02446103440e52022010310741c0105080d42d00c6c0c10300f00e00a0041d400440c0b01400f5586000d00024600720724404040880b454541e4240c0385038170b809002c0d00200340060040c0da50f8005461040c40d036541d5060301c8020030684a8410401c1c4241400c442103200f000303400d000c10585022014412640c1060003d411a4590414407100e0590b40c03824601074042c1d03074402005008040b040c041005404950184910b089110403c0a40c1e030b28a001c50300000e40c203d01d0754841401c428803901003005a04140c1d8422142c1c10324500d441141200151000c0100c0010b9002500c0219803000310491400c8050040c4401d19140e681d04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 160802616 1250 160801366 160801369
    0xf071401090b16020f0a0306020d0b060304030c060c0201020904050106020604030f0207140d050c032e020f0703050a020a0b0907030b060901050102030f0d060b040905010e09010509031b0a0203030d14070905 90
    0x42c465201003d0502d0b030000090002c6603140804c8400c160409401030040a40d00c0c0340900294220480d01d204281c11324100c4141c6060000a8034031850301645c0f0005031046948a40340101901d103058030441d5020017941d10035803202d0190500900e00d950003000e5500d05410014a1802649d02010840d00801d0040010445241441c801d0400880e0201c608444030b1529902e018401601230f50903020700d51071541c80c024001200d00b09080c1c0c545110815030101500b110880c4101d04090030910300c1402140003091040001e403092209900498040d107070715031541c980700e507000c9644c0840d0303521510040c0308000c011030f507050f003020040c2e4000361194100300000c1d45038040c42e14101a0000301240c2c0c140603884a0300101d004001c0d0b0900756079184d8607510582c000d404240504103244140f200496000001441052303c120004000b07541800300785108032504861103604075000d8820701c100d070000340c0e038203100409400c500102c0000700a620f001c01e081141e2001807280f400d01100100c00c0019 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 160803866 1250 160802616 160802639
    0x5030c0a030b07050a0207031a0709090c0807030f020c0a24050c220e1006092115060e090309030c0105040602030301140105040305011803141305040911030f07140109 73
    0x29440c0d04256890b4481131780704071700c2d10901b40d0001d0406c4107d0b240300002422005c0c40a80141442d03996441d201d616403402c00141d9905204010000e02072000140e04039220398481c4622880455016141070300b90140c1c07a241800c10ba100b41c0c0c010410041c0000004240384481c840307150003003405e11041c9005045000c00d4043c41d584202914801c541d41c0400d0301103104a10090103014004402604220310444104c0d916401441d000c10908000441c6000c1c25501e1209150603103d92007034441820f64994200d20036078503007205600e0702c03400d000c07480d00410320185100e000c00100035a22040c4074810145464643e81e049414400104414002c05902004487c107581c014500340c150b013901800101c2e021300c100d50018009500c0c00f50721007003000074000c9041c03042c0d00035aa030444845100800380c4c003510409421102d8408411001c2015080540110a485010f070880311850415040424100030100c80f80e002e264005510a009007281e00c8c001e04071084c0e081c07800d0f01d074032824454640d24 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 160805116 1250 160803866 160803871
    0x603011107020607050a0b070503010e010b04240207180902030714130902030c09040302060a0b0a050a090b0607080c06071b0312091b06050c01051602060105130f1505030c0a030b 78
    0x1070700002510b04c24010108414401984c0c000c0b0130300c000380340025008196410a0081080000004000103900601c0038150350540f42c000030070f181e10207400f800521202004016510035805084d2001501ca07000444220001416503004115410548101828422117030041075103001c15442c9540c40d40c65803803151450b8500e07074400152001d01400000e24080e90403813081d5021018400700000c06030b01140d110300070030b5101801d1011940e00800c0246505547c01000d400000e025020000c00c0e150350014407918101a10b442d207041080d84444c0b190768880050042c02c0d0b07100381d051100403540040c803440d2025422060341058582d65034001d1044001c0303841c41480b2030321421203409005400300e213289400e03102b040d038004255940c030004e0001d80002444505651030200001e160403280e441d85c041403050384e03015108a80c2003104001d1141030800d1080300031a40c0f88844042000244a80e1070f640103100904c4811625000c10145401d8483e03204a00891055408100140c110448642c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 160806366 1250 160805116 160805119
    0x60504051212030c090f0109080c01051b1002070b0106050403200105211006080f0a0e031c02181c0308070509030610080705092401030b030a03080708060301110702 72
    0x10620840c90188500d840080200a5821803000013402942c11441c4d00405c6a80000c0c1e694607500b010950064440021900c00e20242c0d802003005c0e4070b4958468401419a150a0b05807c800411150b16051138181550701c0c0071600c503800900030041c40600621140149030034a84507140504591381c0d44220742e80d01842c200100460b82588030242e000360103070340070a54070b407655001c000101141c540310f000c020784861038101d40104c80810464804c49a0500c2411030f80c1c04616162242144031005120030840703400540411b0000300400000319003129070b0342000315400b603180e41e0180140100c403280100900d100d05141c64000b03100001c022542d402e06034060401c0195582d911006445500c202151542d241c041e040410190003442440803065406c1941150815900e40301444404517080d121301802c0e440a5035410101082024044400c940600d03002c00d07100408004685001504402107000c00d02100070008410b9004055039408502140244142030101d21707003c515101d00701d0040e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 160807616 1250 160806366 160806379
    0x402090f090a03031a0904030315050d03081f120602071b18050603010b040e01140106030e150603070e070f02060901060506220302061902060601020312060d020a090c0302070c05030706050405 84
    0x30140d004240d51103500b6980f000d03211b44454a041d19006000741800781e004800d10320400780100f42c0341813000320ba44a0a6050b155585651180c410b03000c80d1a0141744848588018514007188100361080080300e090311903030015840701c0791486c03c40042ea0070306017032030181050b44400b0071040840c2640e9004075104500009080d44031034002c03d0241084a0b0203030380060034240f04210000d01540005004a10750302d81c0324850b602d620040f8155070b0444c0b00001d0950218510404540f0401c12041c1c0240f030040454644c16030300c003102d0410b160200d80403004945281d500400260b014010258085c20b80c40003045981d0410000400e00d0082e03090080d00101c003070323021003140d62a11040781c02941d001007032540c031020100856502d081806039548018000c84001c20701c2540000140c520301c0030000e410080e50b603100010f018000034420380aa9020500c4080010346201500c40d0f130480c0402907a0142c0e0314290360401304507000041d0b006500a900c544020001c00b035005098405448003190f15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 160808866 1250 160807616 160807631
    0x50a030518030c07030c080c0114160b1e071809021c0216020102070b04030c12030e0a08070501260c030414150601171303032708030402090f090a0303 66
    0x9540300c10703082488040610001900600000c000100c040071a84102c2c0d400d40e80c561503004241e00c818000310850f000c512601d008c1c154036000e00010700000705540089175595076203900e41c441303003000039241c0e1a00408800c144c0420348001008003944803105040041442c5a4004502c02c0e4210a00c00d4240103980851851290110080c2078000070002c1d80c02991225484004408a4204808100c7c0944a035000c005100750f07510040c0c0702113980000382c1d0100c4600d040d000085200c02403070704070b0410407a0703020880c0543e2402c0d80c010241c1902c00c0207010007400c140014060104243c022107a040e0700214180141c01c4000c8400d03404150500360f261207856502d41020401302c5071403800114000c00c5894140d010701100e00300d20814007607076002003245504980c400141c005a402c480c110f0038034502440400d000360000e41d03103100107084056203507014080090b06190340d00002c490314940041448254a04404800e4101d05904580ca01c02c0c24105080f0ba0f50b825105002003d0548071000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 160810116 1250 160808866 160808881
    0x130602030a0b061b0106050108091005040614090a0203010c0c0510090218040515010515030601140405040608030c10050603070e0703020d0c0305070f02030306030a0204091502040312030b030607050a0305 89
    0x414020b80d0003509458440c00c1d200101510410098030518241d071812400103000e61240081a0160401030080c2041880780e080c868040e00e0001c1040d51096280c0781841642c2c2c03c840f00307181c41000000061302c0720b0001032040509442c41120344200300b200d4001408042007000c1000301030944041c600080010040c80031848003500d41464140c22104002004203000d0049500345814811101401c800da8840300cc1002c01da01c3e06880024494040c0002010f0b9401343d00c400448190301c4079018281681c0320002070581c0d4807600460704640020820b015a444108000c80010b0419002840700d8688880440da446516104420310411520040782ca42c80c0298111041c04009000500000c01e940d01c01801070030302034400f11300280302103520542042c4044280d074066100180940702c0552640c080001030b20f0000740903210211030b0144100d01d0390700c92004200131841800e00d071034480c40c4104040d0464a100e0b03a42c1d4025000003081014140d48441220020103650130f00040c1030300d5614 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 160811366 1250 160810116 160810121
    0x120b06091504051312090e0c0403080a030f090204020f07110409050d050a210c020c09070801050402071b0306060f1502070b0f0c07030c1e0803030103121806031b08130602030a 77
    0x80005d054680b840d4100840660f20031810b07810b130b4800c442d07014407617120036410001230701c0f9501c0b0140c0614024171059000d03910035005004240b00440c40819801c4082e00020100c0e4800080b282e030140d0700042c040208610008803100a0008942c200b143c3c0406899890721840710301020810484006004038080d4010440900021540103030003001340a1002c1d24402804450000f02c094410400b481c032132494005601d9106541540c3d4034020b903440c01040c040a50000f0300c048032074100300d500306241d0103d001d020400850040350701280d00c03031802d00660502d501030741004407210b4200410b0801c1a400182c08412102103402d600d681d6017150000da030090044541070750041c02495000024040c10705460025074440301c058503d5011300c0346030141094510320a007045074205000400201e00c025100340103e95031380c28103051110000d2118026546a0381040740420307503c00d074010160f40031034003401c002182414842010308150b510340b02450490003006260780e8001002440d04925074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 160812616 1250 160811366 160811401
    0xb0904021606110a1d0d03030513050a0b0a050105030a0b040b15130e0606030d14071a0f0106092106090206090a080a05010e010b0d08070c0f120b0609150405 69
    0x40b03010480d03c415100125080d600c00c20b11000014440c4400340c214802a08500000d440e00408801d000f040d9541c05502401d001000f144c4598225038607140031a0301441028213580c071500a001c0c40d071401d020001c040710b42c1a084103000394041040354001442c8203440e41d40090f0880c0102c072403662042e9442e118900c22042d21a0403124946503075480d0f46107a00803190058954003690050343c0d4040c18169222490b00c00c0c08000345018511492080110005044090003040c005410941d280a440440c1c01c0c01c0d035035895119142001080343c00c1d80a8058005010b40c0d0004c1c8140c101c9480e40c809195141000141055036690102401c550b12007040720141400a40310800d0107565111860701d81d16904130982e140d502703102411a00010610a1000c0790b4801070805142030780c4c5840720070450f0480141180d102c00d800340041020100c030903044009040c001044030b400700c0c0c10302d0b200d032252801901c211301035000074082c400314001700c1c030810320044c200355000207c41d980d00303000c0c0c4c6805551 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 160813866 1250 160812616 160812623
    0x6020d0e071a03100f08010f0b040e030d09020d0218010f0b0a050405011206030230071212030f050f271b040603060c05070b0112020d120e151809010b09040216 70
    0x9060000301b0210641081b00182e981180402c041385040060105541041207015041d400410900090141d5a448a880c060003d0901c290081c49907010900ca030026000180321031640800421081000c254044090040c80072a14101100c03100040c115000e03500038241403114421003800900015400350b40207540042200015603503000450351304118001c8a9841856214007252092000044c0c5400300ca580b25500b060050309a26a094042ca41010f82c00800d070b07c070780515104c18400e000c1d20740120030752054a14241015075041da46603540b611440150701c0088201c440d10180864226000041c0045c1901c90359501c200150060085800050240f8035103440c0c080c6031640b100150417134911070f0740020030f03031390300c840040f43d1180400d000207501c6100e518907040000d403180c000240400f00e50610002980e11a0b0001b651000c81549003e0b440402003520703d6042c1c030316070103114003041c00e40f01c840e603550600b562080544902c2608a0003a600015800c1600360401b0100d48020307003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 160815116 1250 160813866 160813889
    0x61206010203160c1502010608121309050403080609070c0b01030b09030418021b1605060f040306020a0f0806040e0303010312050c030403060f050703020f0306040905011806020d0e071a0310 83
    0xf03692416507144a02800b65180d0390754465461504103005220303200583d2003e400504191000a8081d2420b42c01504681d0120030540c2e07001803004d00380e00400b4040d9100f900c605034180762110612000d1b4100814020130880d115521401044d204003d050540c5e4200403011a16a00c0c141c050380b4600c04c03a8040920440071440d42843d8851540c00b40801d11143c81a02801359074003a0402d0b07403100d011f59100350705954207000300441c0c60007000910b015181c42c0c001c942070070f9803529051304036008500390700041141013a04c200c00584c4104010381c0050101c408110764510712010b165640030501005254a4903a142d48842c90b020718140c5030b6590300c0504413950366842e8900040500202626940210300741404186640d000f8000d86400d00d00040e00142180e5519042002a00146d907040d01c4555950710207001040d014000040580d005e0b540159132386001c3e44640f000c030b030074110801e44075401100707041c0301211418000c804510100c5401c0e548030746400c4181221401194400c4000300c0c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 160816366 1250 160815116 160815157
    0x3031112040b0703050408030f090109082b051306051003020904141005061018030506010f03140102041401110f03030f0a0c0804050723150403020901090b061206010203 74
    0x851600d4203118030722818404080d07880740e00090313095070000c0e03c00400e40c0105100050300b0020402c800c980c00301000c4008035260280762103c40007540168880d4041200040c1c0c2012241526004202400104103041100d442e01525180e2001c9690030001d100c02d807140701184005242e0340d0058040c0d03400410703071000d6060615000021201d0313003417040b05034000c2c100d5034042070b4003612070244030b4207010b005500c08a080d01021240120081220391312076421000120101d0b40c200007442c003030000201c02c074604a05500702254010040b4895103010381c01004144980005007212190401c400e0800000d60501801d02c503042c49008800c0da0705900c0084200700860501c02c1c400b1303000d136061940c104204038050307004a600e81c1c003c03078014145a010074401c101400c1b480b0b200c9104140c01d10100c070040100d410025810040c0c41d032558441080c041014070540c0740500c202801042048010000d29140f40c1c0410458003070890500060b000e814002500f59000348119285550084105070048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 160817616 1250 160816366 160816387
    0xe13050c060904060e010b030f13030e0d020102011409030904180203070b130b070b070318030206010e0a0f020c0307060c0503042001030603060905010516301b0c031704020906010309030311 83
    0x540007180d103148240c2720075001c1741c032084042d09401c9090b50141e84100301c0ca103d120a00c0f43c01c00381d40400300c0c1150b507640b44ac40c10010007042443e000d607a103c8085c6503103074541c4040109892458040300e0100403442648070041e58009050702c2110301401582d92180c00710503003610215441c1c2e1040f001c100d000240e050800507814001e500c00c140e280c03002c2206c2030078402c0d8185030340d1200000801690105005000810780382d0582c41c1e000495031008138086400d103440c08240c0c0c0101e50300c0d803102d50001c1100420020a801200605540382c82c00b60b007075152075160b10150301c042c009114540c0404001c1e04140f40d101e50040310180d034102d007041c444d0210603c0e00a00a18046517201004c3c80e42141c824100d030720030515240c150345c4100c0703220503c10300d0708552500b03143c1d8000d154501d1603450820070030b44a1401081042c40c091078403030b004000420700340608106041d403003044040c142e0b01704010060351070803603198008600f131a00213906080c40c81d0a03070081c07000441d4010102008108210365 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 160818866 1250 160817616 160817639
    0xc03030c0201080a0504030c030c0203030d1404051c0912082712010b0303070b090a0f0b1506040f09020a02011d03040501171003020d08130e010e13050c060904060e01 73
    0x198403c0e80d80540c0c0799940c91210040f40c42c180ca008002400114039a004a440ba0340d4080341c0e10700040580f45040511030000b03084410a0020794190b404110820090010501200525203005003000d90714110004005047c58600d0141c882c0170104030007400d060110180a46804031034001440d03c1c200004030002d0300011003840802e1050f4015100f40c0c80c0423006015400224601134000c604022007aa034100320482c0003005500b5a10401e0005004500010100c00b0580e02400095001c3e040034032800e0f51101d00399035500c2c0620003c000802116080c0380407003048503960240140c9490303006000328054a590800202400449606503006560100c010800c80da000d0b200e4031038004070400b04030368003101152401851216001e00f080581030400da0600500d200313202491400140d0350030031050008680003819200c00c880010b00c003070095687c2c2c41d500201128070441c0c40c11102da881c6640e6581101002d4001d40e400b1a024056450341e801c40b138080e001c1249180e030030f9a1546c80c807145 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 160820116 1250 160818866 160818887
    0x314070807090e010b10091a09031005090f0715030207080d09080a02010b0f0603010b070305040e040507060306140306070e0103020c0307060c03111612050d020c07050102060105060c0601090f02070c0303 89
    0x465460004032034806e142c8842c555800c0b02e100d4a4103090185084405003010554140d96010100b04001c00f0702d0f26981846040c0c0840034a02e40001c0034246140c01a03d0710f2604040c0c0125548030b900148111600e00c03041641300350780b40c540540d4411041c9030000c1c2601858100100d0541041403c03002c200020700a4003c0c3e02c202c0e40200411481c100401807640701c3c2c040b4040e0840010001407050a4110f4001c00c40e9500a080843c035190780d0340c8141415a400303e4040c2ea41760001c44040c0540c2d0b81c1070250400070310f208103811003401c0e8401d0000f602c60401070020414885049150401640640c050725103040112041d6502c13405641020740c0500581500040001d1400c1e9503034804103000001e442d080100101a00325070005079684011407090030380b00320103000c0700340110002c0c1d031118001407d09000202c00342420710b240c0000a4603100c01a0040761040e0005c0c044015104000609281154507c280204030100e00d8200c2c40e0017880384410107001e610400c03030007000b8190080b02c40741 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 160821366 1250 160820116 160820141
    0x2070306050c040b040302042028090302030312090f0a1505060118030605130b0103060b03070503010509030904050411030d051305010c030e090a1104080c040b040213031407080709 79
    0x603649411071240c0602c1a40113070010080c0034030050001d401c00e503010010700201d41e41301880000040040200035040490655a046039502640441e640d40c454030750801c00c2d1500301085041d007141c2c0080d85900031851030520400008001448a140800c20301c900800820242c405407410b0742454010b95101d0002c0da0400b60804011071820352240003891038042c60740d20f501c4030042c2943c0d5000e014040c0644a800400040a000008a40c0001c1518000c43c402d540000e081a5808285410400e003644105d210740d24040030044d44200100c22130f000928201c90000c1c03265a2850070341031000c450940c3c503800d0301c80d106400365071540041c020040443da810710702000598500046510494104005000543d00c10190000e42400903409030012680342020a0484800b565420103070010b0303010050f9036014444007440e84c1090304c112100c5001c2a5070940c42c0410007071480c0500512403200034154051038000d0070342407000744030200c00b6000060603251312960f69841000274010412010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 160822616 1250 160821366 160821371
    0x4060c0b011d0402010c08130f06110a02090a1805030a03020405120a080a110a140127020604030308061801090506010813030e09060a030b040506010e10060507121205040302070306 79
    0xb062244201001150781606810000040d40d0360f80d004582c26041e48604445084085c4154000c4607000740c5a800a801d181100c0b00f0541c3c40c0c0b00008040304200d00e450340c101d402c8111448056202c4034182540140c030a8000b0510104603060088038940000c4090010701002c1040c1c00401d905400820880b481200c1c0d00f039803d151070181c1515800101d0004002c21000c100320074803a80507406000c0c4650382c69040c2d0700030130070301c1d2547c848260700202e02d4411655594500c0100c204881d109250350340c40c45200580c3d45201c0c0d400b2900700d205601000d81401103400c00505507581e0140345a01004012002d8405540d680130501d011308003c0d50918082160800080c0403105203891030138819030581e41e5800c11465907030510441d100c0c054030f083d07041605c0a00c0440403a1004030198002e80c403c400400596140c000c1004900310082d0042c0c0b415254030310300700030682d884401e403a00e064005982c4041c504d20014140c0c3c18039042d03001580070a080c0070400041c11f030041421400c4a000e05001d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 160823866 1250 160822616 160822619
    0x903010908071a0106020a03180e07080901060812070f0c0b0c070f0603050603031e0f0418051f0614070209010801090201030b010e1c02030106030c180c1d06031b04060c0b01 76
    0x8600740c03043c0074000d00c0d0059004030400740c08240b003035103001100714901007002000c07515001403804801d02140c03c0f20100710008240200c0c40700074403640c802410400083c080c1d0310ba6600e86408680300b422406002105070b50810402d000e4040702c0c25004192003190160744034031780f100d10b540301c500b00e00c01c0c20500c44c002400015140e010380600c40c072403c00100690f25100c3e1f408102008041c8503517100610f4001401100f02804c41c2c040100050002d402c4034502004001c0100401d903000240004400d4011546e00050544400440380607a00d00d81400d400c1c0301406800501c56005151002e58040141c00c00050580010340c44000118000c4c2d13000d0081c6c148803401551194030348044160400c1c1c403081c0c1e480000565100c003e021520090002c601c0e1560b0362108a42e0340d0054029004146840402100d9500d071481007890161690178201403603001100c61a15003004112054021540040090418a03940340e031001801f00d103c0e00035880d25205c0c0c8000b011440310110444942d0341c041d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 160825116 1250 160823866 160823903
    0x120806030705130216020310020c120903060c0a02010e1002191409060a0201090501050a0e061008030d0b011b0308061203040503100c2d0807050a0c02060a05090301090807 75
    0x50003002e07601d014048120241400020300000d51045116a2141d1400c0000000591b024801110303000320101015845181102e2850300f0314140c090b1080e44054100900c2001d41c4000c034003070782e01400403105151200c8181e10164054017020810070000d000b0300348013220210a035809030903210014010055601110881a076282c1d451440b5416108014070840c062480c0c9103000b0184e81c00a8030001c6400c0800355102c5007520750a55401e8005070315196071589100c810000513601461001c100c4890b01c0c03031300e4445616445208428800240c45140f68100303a40140f400c18650014400381b41440010350800400300d001c00d503801d0f8441e842ca4522074445041c004140c506541c001009040346288030500343d0010509a07078043c081c0050034620403005400203002012304c2c0038130181d00c3c80d6065034040003008110001d00d50001d00c04203005503001141e0044045070b08542c140c50280d90b645080c0300a0303540b4000c0e600c0b041d60541c24407800344204442c040150450070301c601761015041c44d0701034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 160826366 1250 160825116 160825123
    0xa0b040c030606090203152205150405061c0f080c0604060b03070506071e0201030b060c06091c20210403060e0106060503070e040207020a061d1c020909031612080603 73
    0x4594142c0d020802003841340608d0041c202200091044226481007160346405500703451048a031202186410008400035090034098a94402011200c00c0d0102c02034140d0985207610300304010741610300e24400d0508120340711045440c8130519004590b0b4519140c509500500564031206000e170107001c0340000d01e41801c00035103040980c004440114401241e5000754149405d01040e410161034514a10007904c2d100002d10000200c02c02515881c513044c0d1040346042281c85606d0110b00c03d8190481e6640d41c4400440e03180709006100501c01d0740305010a03443c00040030060f28801c5a11502c00c040078028a0081c01201d102d081c0070b011081c10a01070b00e0884146104040c08602c0800000d181144203101c4250f00000082c170050804190350041600e15090360416404100315a005902808a800202d812098100da0700c6603901c0c1e9201501818100c40b01c0024001c1d425000860304480051003501c1d60100241d41000303511000d42480c401c0e14007800c250101042422010503d182001b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 160827616 1250 160826366 160826371
    0x21203030603030d0e161e06080402130c030f180309090608280f0b0103060b031b04150806090c10031104060e03010b0a091b0206160c050a0b040c030606090203 70
    0xb000341d802e180844408402405080b8002001802040d52507040643c1c1ca44c40b04003e446485001d504100f1a12406042c2204c10342000c07082c408080b0420006903100c501580800030082401301f00940040010b034040c3c0b01006514001c2810086010403126001c4c2c0e4400c6000d0281c2c0d208851142d48a201c44111403140c0202411a0009c05c1c2c0605500e0301c4620203031580e6001520040c00c544a5160007211002d081004c98420441c0d800400512000d402600d000f400224090062100d04007540c0e1040301c00c2c002194010340d1240848150070b85e041602c1d100604100c0155140b903e862103105490b603880a00c840c0c41030800950844a1612a100d003041482c0034541c41c515242c00c01070103035030360800b10801d01d9042d9220300148146d51542070410005005040001c205409110885c0041400b104d10810865001804000c0c0e01400945491b02e1038816003000c91404c851402d0482c18104400070207040c000d0712106100802c0031008644044a00a03402001095180c1030440182e1009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 160828866 1250 160827616 160827619
    0x110c0c060c0601091104030b040804150f0e091305030f2a06070813060c2c0303070f02030a0f0b07031d1507030204050a14100207050109090e0a0206070b040212030306 73
    0x2d1001070190410a62106201d100c14801413800c15649a503103000d03c407000c035070403980c48502003803c001c0500380394090481100d40d42000e104112404038000e281c0c0f880400100d01c1006102c0100b8441e2402030203d10074070390420709481d9922090103551704035600c44401e00e0b0004841e8846150102000b0f252240201c1b64100949202e441d110011a480710010f00440500e18175251400c00042e654800e0801d07400f65512650fa1110100d03800f11512100c11640079080343c0314000300d500c5030745c001c42100c0f8965405040e580c0b41d0581400407a02e05102850300400d00f48401880e00c0030701503580b414512566040d50280000000100086117910b1170540038060b0b90b01102e00c041e20003044441260740040d951500500b480d6550740001c5038070101e0303805142a101240d62001407410728202c65080024107000504290340740500082a4100c5407185035503036992640143d0191505104204c20f02d074005004584428039414181c1d1246c2003603c0480c41008411500030440d60040182c074401d520 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 160830116 1250 160828866 160828873
    0x6061311040902030c0918040308060406080705060705030c0d02030310150f0809210904050c0315060c0c04060902090405090a080a030c110607170901020f070201030915110c0c060c 79
    0x6007800c0c0c40040e42000d084064a1a028090301c05580c480ca003003100d4407d200e502c2d103003981c2400e09001e46190300151540f4000d5081c580180304078000001e21804803102510825070703030605402d00d6400d5000e02490f04174a4040c030055500001c1e1b002000c3c2d80a1340b1a242cbc0c01c0c003442da803022920048a000700300d80011402c0500381042d103600a42100368014488030070340c0c000c1501209070b84000542c108100403244804034584449081c540304a6a0080b050a022807a50504000012045414080c41889880300044180100d907060041200b0136401500c1841203d0300e0341c4075034000c1e4021044040c043e03860100020fa100c000001d01c409071681203a0401c0ca408540d80e401c401505480080405000581e5403101034000300300200c51141a49a6401c070f0b00c0000d5040c819148000a8845441c03030f030051120395050b0445400701c03030001d50b0900300050451103d00d41300d106850600842100c0074501001c410461910780000e0500341d4500c41600c11100b0034030704101c10b601071410aa1455032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 160831366 1250 160830116 160830119
    0x20d03020c0c010c0609060504050d030e010614100c0501060801020403060e0114060f0303070209160f0c03080f041104090c03110d0803011e05030a0615060801180f0e0d020606131104 80
    0x5005130032480c0094040c0e0404210720b1066110401a9001620111820341c003072503030000c005500d88900e010381c1030080c00911074036190942c10003445094907561031080d9004010000402e002d0b18035080b071607611000911007295100c3c640f900039005880309685041c00c014041904640600c940d41001084411304446520340d8002e009424844401d80e9406200c00c02c04070717002d83d40b21030800b4402d40521710030030450311741141c0040820007041e400c40306105560520000180d0080da41d69070000d583c00c0c07001c90660b16030a0140d8032400d00445250841d01d04404503044c40150880b100980340500b0700894500c400d2018020500e82c00d11014220520a000500610300d142a0b10080c1301c59404408001c26100c00000703080440c0703020100d0300d590360380400300c4526000301220b4005200ea41409489036142402c0100000701036954029115944c180d00580043c459000d01100c01e20b120407a0005038000001075950b01003514030301c1c4500b00200081b0b007420303e24041d80a03050340c1ca01100e410613 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 160832616 1250 160831366 160831369
    0x1707091a1c0224122806050a090903080a240e2e120c050a1e0b0403030804060203040516090e060f041a0405100911010e0d020a140105120103030f020d03020c0c 70
    0xc4030190002c540410540305525a444805c00000e03052456281d000a40510305010454040301302e9119010b964100503220000c2600f10842c558012181c0c41e000c100c50b0070910030015110a01d1488110444080c0d00115102c1c004240b414456491801e00101d0280d10460500312070003c1d143c3c60b40001d02e4000103001016040840c0f030301081c81103030303204500c9464000040484240e41c110b4810a00c603055100001c2c200c140c1c81c0d000505018045074941401c584004280c0359001b04050b00441c0c00101140801c00c04000410900c1e500b012003003e5261030784190000f4102c803903500e4040388980c001160140d00095000340c080ca40c44410720001401c1059442041c540051007580d440c01100304841c1240c40c01d016008884d03220710203c2c01016200c000140060520080c1c9074014601e0603403c2e00180c0302c84c000b88040d1101020305a02c50f207031443c01218544079503c222041e6031506030000040540001d41c12660380d42039002c1d150b01d00301d0b41100310100e0084049461a40e0b00c20011009030b07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 160833866 1250 160832616 160832647
    0x907050d020403080309010903020d030507140304020f0a0306050901062418080102160b150f040e1905060601080912190302070203010c02060103050105011707091a1c0224 75
    0x38001a10409070030301d5030701d0700c40e40c035039403c200c1d05261641d445091980416030b05100c14030000d0032030308042245003007d41d0010843c2e1802d035800210200000041420355468402d8212410340007030101d0407554403440d01e00e000c6c02007614105010760070244040344140c1b0480c40c0c5d0701c4212803046030b240c8201c080704044800d00501d2030030604451440c1da010070741d01002c1c00140154181603280700c50458040c6052051084028044040c031030f100d5404a4081e61007a00c0c0756200b10781201d0201d1100328800096090558655102e90740300098100c030000c01002041c424840d480903224081d032030303440c41102c03900c6000c1f009108004040c10400180c00509880c01340f04d0b024079a00d8014200b07120355020a0842e0000110840035070702400c010000c00c9170074002d00780503102d595203440011209040c07040c0d550030140260f1051586a40d02c00d4172541007041c1c220185c0000074010380f041c14240346003150840e90080140e015444c0300c1c541e1410490b811640d11076800c198404146820315404c100b564 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 160835116 1250 160833866 160833877
    0x311010c0507060c03021b0a0210031e1109030a0f1703040803041202010908030408120907060e060f070219080601080105040305070b06032a0f0a290412110f0a05090705 74
    0xa00d6402e000c82d00c1607c540c0b0030014072810840000b400c403045207004112100ca10001840105801c200c514101141c004c0c81c0018240352840c0e01140b070213001842140305d4050000a680c052040040e90b04c24016200ba04030003241c020182010410380050840070310f0701c0f0458014040b990100041000212030002c28200e81051b4800040c0004166480e0130250744203841c162288a800f09070019a0f00170b4154840d0403126190040064a00d410806000b5800490040340324560110313807211080c1e01501200d00050b40200250300f1a40d0031101c00b40505542d01442000c0c0c403039030001103043e200510a0500958140e141c060902101d580c942c82004001828540c05000300780c10b85109106401004044c01c944682c20b40800c8030b11028888458400d42c0c0302c62180e01e40c910304012088a5505074194140d00c2501c0c42408941c184c07014180c1e00c503560100000040c201508024800020142c0c94856401c84070301a520b02c00c50108450210380c0d0150700d0f030025500c0c02103002280030307500404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 160836366 1250 160835116 160835141
    0x507020c1903050109080702040506030f10020705120a0201020c0d030209010903110d1208061816030b012001060306051515091201060f0e071d100c020402030a090311010c050706 78
    0x60380b40c4a40d14207094520240c0221907008022401b882180b03028060343e0791101042d0000c1c6050310380c01110558a0005802540009600041607000e014081c03192141c1c1d05e043c0b02c801c69448034101d200038000d40c011006604980100d940100105210703008030f6080c000d0507034980301c1e01811911841000d01c0d004000035840b031000009640020340c0c9608907050301e500b0b600c036020245008070500507010000c2c0d030030b05022081041048005982e01500217141015894002642c102a80060342c403150546105480180b54512280c0b001a0540110041d00d108403030a0020b0386901c5028009011141c000c50340c0071a645a0040020010201401c0c1d0003000614034150f032000c15100303500311b42240d084000c4003901d00c0c0d814003140042014068215049140103000c10920014590900c2c2454080300e201d203440c8502240d40c188942c102000454004108556a062403500600208202b10b0120040398400f4501030500e8018490510300c2041c5d5103445240038050341d02c42c00100044c04806 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 160837616 1250 160836366 160836409
    0x7060c170a0b0f09040c0e0108012c0c090112050c090405030703080916030b040b060105070503070f0c09020d0e01050903090a0311041401080a050f07060c0209180d05040501120507020c 81
    0x101a5131340e40032440c01980141002404a810802000704400c0160407880745a8108046800482c80000c0e00c1c6a5000e0740e1130902d40d042c6415244681000719082900f03510103100000851005955804d450040380700300202da00d010980c005101907007030112405803d98109200c1d00010a0080711015030103410b400696224403c0c60f4140040d408840e00b0a458000481003000100000e12143c1d40c3c001800f400c06a007461300356507030f00c1d0b92849118030080c011107031561240c04100c030400442028003c3e000003992241d411142c04002031a41d0804280d2075801c140c00720b022804040200e0340200d40107850407000a0a548075845203004c0032201036013040c1d540300964050320280b8074440c080c294982c007404e040182030030204d00d005c003180c0303942d9042d812004040043d0394000108800345581a10b180000d80e4450701c6800248071625028080703801a44039491645621000400c1a204240c175140380b941622a03101c0c04490007110002e001d44c3c0203182e03000445ca0194800001c82040c030385c0340d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 160838866 1250 160837616 160837639
    0x605040e04060618090c080c060316050d02030a0b0f100f110307050a080403020307090216020405070c06090b100f0b032e08010606091706040201030c0201020702040e0307060c170a0b 80
    0x1007250303005103444d078240b0080da038207181010410000c1d20b0b40c0c000c0c6802001000590741400000381c0c2448060601c0100703401150081c3c1c9081c0c003c4080c0e508449400400319160701d808000000a06424ce80c8940b2075001c00003002e00318030300450310210100c81584d407100960440c6a0a540e03030039200d004c48099100c05c0c440940000c00800c42491424032840003952141d2440c030605107885910f800c403102150041c04040d0344005074101122909804450105107521403540a07903a00031440c44c00f038005818036a0340014041c0f81201c1c113005070700307100100483c20760300c10002c220b9170079500400e000e282e010000f0030085036980301b04141280307500030b80f824000488032508412001c542d2103030001380d4407035004008940d08410008014080303036010f1000c1eaa140e480068407441d00600090505545001455000c2e00c00d5060b16a8203501a0042102d1107a101d02a41d40341c124140c1143c3c42420f151000c83e0f007510802c100228881070135070b000001d440d40e40505c0050080000c50300c0d003107440e1040c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 160840116 1250 160838866 160838879
    0xb04020f040e030d0c09060503041a0601090504050406060312050708120402030c0924040c020d120219051206030a050601060503070c060c050306190b0a120204090914060a060605040e040606 83
    0x140000349400d840050a040300d501e0246c049107555211005204042c001c01020074410008401e9246c103114021000c0c1d0784800c0160744085560300f003141c001e0f1a0008200c1000219071041091380d005416100311031a8590301100c1038403c0440003442c0b50000d00c03964902030070b030540803a0450720080c01d65180414400100d810f8400403540d000d1080d0b0444001ca143c20044410300015200950301400851050f0340d000e90b5643c0003984070070400c1104e101141c9413400503810342d149429041800c42900c8080500203140e07401c01d0189540c0f1100380004281c031864000755005c0d0342c0741d1140181c180e5a2a003038068030141c01c02440807050000a20300240096014420340d11181d03a1500d0f500e440703060900510104100d08220300040c9030882109005980c4041c09464081c00b1310715190000c03110010581d40039010f40e506c2600314508204d402020010100103c50041c001c21007200d41a50f1014429000e846103446450040384003000305200f00300341c1c03440080c0d0003401114007080c8590380e00c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 160841366 1250 160840116 160840123
    0x909070b070317070206131b0f060207060e04182306010e040b060904080405040207110d082101050a030201030e012003070f0819020714120414040203040b04020f040e 73
    0x30040300018103c075000c80c0c81c1401e840c00a40c1100032840100030614064803840c1c1070200c2618094455149620000c145046081103c40034000c101c07221501c181c2e0302c01001e940d503903d900400c00826441805075a00e42401d01c5440840140900c03200c058002607210420011081c40c0074801c890000c4441106000b01005010b000b048414441242d500d020b0804d1441c0e04e1001e03001034841c0c1050824030011807003d10030303034003035500440d001030750354001c0d03d0320511200460740c6803508852500300200c00d00030800042d022039807410241100205a0b00e850441e000001d0050f11781c0480c00f8072003440994801d0340864405070140c000081d02a82100c1c8550aa524400c442144030000002300030809502c2000c91101d039030941419422401c219070854402c00707443c050126003d60119611051000c10442002d041c001c59081c0d0300b040c420000003a0240c1c1c0b19001d0506007843c85540c81140d17080c41c1c400c030380c0300315003003854007500b52596400c0010981d103030300c1c03003e501a07203402d00d2981d04070090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 160842616 1250 160841366 160841377
    0x8040902030c040909081c0209010c110d150209010206010f180906090503070b01090e070602071814090703060c080f060409111c02130c0f12111b1203010f050909070b 73
    0x320900f07500c0c4c00304059080d44440203044030b21f004500501c200c01469030829901c040d1143e0200c960a4260883d03804038803000c0e0b0140b00031308140c589070300051025642ea030061100e0b00007a800e55a072070f1f8a42d03096004040c01c501c19071004030038a4170a41024000ca42c44510241d226007008a0948007680303445203150403405003982d098081000400008055104050018003c0030250100c83d02e13012006c1d44401c0e00d8440c00c02d1a6030089108482e17107207943e003e42040c040480c1e100b001420300782d991941e07485080c001140d00c3d9180c00e4140e11020b000c1c02d0031900c900d100d0200c4911640d148000e01003d001e0101040b9052100701a0181c15561450529010320b52500c540f0308980c1842d00402482146840613829140d140c03492003682c003a44040040d02000030360034164090342c2c1c0780304503000400c03046040c00c0003441d003c240c00c000c130550740300d41c060207007599411104031003203500003980680710a1003405020070b60343d80e0130030031410400419a40023103042c043ea112155a25400320321a03201 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 160843866 1250 160842616 160842623
    0x9040903050c0c0a050604170a0c080a0302060603060c09010518040c020c04050c071205031509070c21120b030f0102031e01410307060201150e0408040902030c040909 73
    0x20544561030101008820300f01c54048030543c4ca22490b040101d81c00344551b000b10003031404031816414a05500304481242d05d0b60108408007520340c0d13403038629214180c1c0f180440050081c0780c042a55880c0c009402401005c410704051b00c3c0c20090001912181c0c00040c40090a0300c0c2e14003000702c0d42d512480340c82c04074450768010f0812a0340001c1003100310352000344040b00110061000b5004034000400c454010340c1c141c180159645ca907900e64a8102c0044071036a0760041091040040c21035014402c041c0c80c074424100300d030700c5142e041d600c40907255041c1c042c000004c0300300c014540c0c0c00038960450605041e014060f038100d440c03180a0b081c2680e0003240c03890401c8584401c5062841007881c02c29004110640300343c1592200a04072042a6010044281c1b2440801d49650685045c0799980c0040e0303400182140d1240e541c401c030203030207440b080034000b400507040040007800c081c1c440e0f640d51060f907015020615141c103002070680290009060000590028480413810444d0f520035051a41e02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 160845116 1250 160843866 160843877
    0xe13020a0e15040b010e10110f07120303090c030b09010617060402100e0111010513120813060506120d020c040f09080f070c0b0301031103070902160b060103020c010f0506030105090304030f030f0509040903 90
    0x254123510300e42044010041d803680d110301003c03c501b140200502490a0741450007080e0740303526041035440044141c0003d00704010f0b003001c1c008440d07415070101d03007180e803001703c19480c2003e1402c0351070320f40c00105e40194020080c02c08400f862407080040250300641410814003e10f40c1075802401c44104407044c0b0540d0381c0030b441c0700061062407100c5021403101e40c0303071207901807901019000811626210040c41141c8400201d0095600e81d5115002c00402c5000c981e420f00601b2070003540c84141d104054040c502d0070519607001d08103070265403c01c0ea0010f4819107420f88101c50344056600858042c0d4800c8070b4044042038001204004600840c0110183c410b2202003030308260408107241d124565140c41048a0704944000b021b110800942180d84c60801da42c40c0380059001c1d10070301c003090659528004000043c00b0b402d0384201d0240750198020001a0784a00f034440d5030340708500010389800407103444600000d100e0110210750b2049841c10f54181800c99000c80d00350355415a00310040384 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 160846366 1250 160845116 160845137
    0x1203040f030b06121009020409020402030a051e06010509061308060405030c011103010509010312030b0306180115060203030c0c0118081c0603030e01050903070e13020a0e15040b010e10 81
    0x40581c1045030030807001c41d501d02134440f5034100c1664840300e40c84000085525001c000056513101d0b0311010b0815009002996a80fa00c003030888000c00e0225001070b80070320000000e401c680d0b00c4480e4580b0070201a11598944000174013001255000800070600503081c159020852620074040c0301c1c051486000215141e88c00710b10454291524907041510609003030004000603611a102d50341101e800146410103506034200032000742c010824403d41511541c002d11101000d015a019500300061000704030005403001e4140c04c50230f0b580304540060f441840400c03030050a02000b4072804800100010380803181141d08400e904466a05440300c42002c41c144c5280d0141b5003071013403075841e03d4100300302c00c40c11b654010704003540d43c4a40504000300401c0520091310100b2120b0080d00c40410007100c546400b1001d0114480e20002c12405915656400214107240716000c80c0510018a40ba0210b07140a03000d0000401280301e40d181005a0380307040341890380340e800c401040b820940c0d5541c426030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 160847616 1250 160846366 160846373
    0x120706051213020a060c02131a01020f060606070305090607060c17090a05060c0c070801110405031c0918020403020d0f060b030d05030f0612070902030103120903020306040201030b1203040f03 84
    0x4000100070b40e20b10354610702e14500580d2080e540d0801e5400a041c034100400860010805005c221584d00c14000d103001c904040612000d491102e00400907400c0f20f01d000c500903031140c0c8501c070a84084e84c00140610218000900610180040102c023901e100e04060f055103411003680c000e0b07107021011403011001c2911440340407000035808070031070005061800459886030303680d40000f0640c81c00d4800120343c00d400020241b21070402404d21000a016070030f207034075900c1425071280c410b16102e4403d8500c2d00e0102803a0a4154050702c100e61113840405140964a252490040440141c0b0580c00c100210043ea0b45a02e65070602d0702a01c2000a5006c0c0c502e80001107420450740f00c0c1c440d600c42c50041d903070030360720000f16603202c041405c1e01905070f102c020100d0440801482c10303807100d0007984400704080549601650480f409244840c164100340076098600d41517500029415030017607000240954060340004075211310190228690b4000404c4950468100d50002940c1103241c10041090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 160848866 1250 160847616 160847647
    0x70204021c050a1505090406090804080d0915030b0d120311030c0705061503030a0c0c0806180c060307090905090a02060c07050909011503120207150807110109021c0212070605 77
    0x2107050130004404010704000028020a10052000b00103d495440d04810132200c502910018040c1c10b085800c220036008004e0301592490140382d0180300e0940168000e10710034040d801405201505a81120200c0c1d110000c14005a03001d400034180c681c4449800f0303140d50030040d07100f022110760b2030352142d1044c90f000303080413409080f101002048031101d104541c1d000c021076040019608080c042d40b4058a000a07003510f41340e00c0300c481ca0042c40b04020b41007254040742c40201000c3e90650700640342140c204103907400103841000019240120a211003585d69011741e4120300d002048551a101d164001000d0340c0c40042d40c60f10b00d40110004110a04100300301940240c60754000b802409911540d00411601a1001a00e0181c0e41001d0301c082c98001e212620103007002559010282c0619400642151810303103501c40003541460440b80854818445c075121103600800d180815908a211005000302c40d10040e40d05c4895402401e501c1c0408001030300c001c04460700c42544400440365440310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 160850116 1250 160848866 160848881
    0x3010501111b04090c0b0f07021306140907030219120c0801140913080304051b0123030a0e070f08070509010b090603071407050f0607030207030212070204021c050a 72
    0x1156100c44140c4012000e002c04041440c1d2054400161103003442c00d0243e0b10140039440301041c0c40b0001496046081d25200818002d80203940322002000b000040004880062280302c0610103034401684651420b40306860700b203242441c2c05814000b0380f040e11004490703507d008170046203800c0c10f450400304450141d2611141c5604005400e985020b20007400d02c0341100c14244900036038800100300d00140e0a04480f00b91300540c006840749803c0c50000d40d00c03001480814000702110211040c158070885c54542d040304001a26000c1d1980500c4044280d000540918055030301c0d05880400550200301c2d880041641c00a1100542d03e0810783e13034142a5903820103030007000180010702100560b541101c00c01801561080d80d81e9503111400c03942c5800e840020710082100082940501c0000601d5440c5828110241c1e401521641c034107404034440c000e80100580c00003205500038110f035401500480e40054005868150700e0700c0c84e2085100300285240030203945070140003000c01c40e4482e149 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 160851366 1250 160850116 160850147
    0xf0a051b06132028080a060b190303020a11030120030a06080d0f08130c090c020124060c08070501092003010209090114040902040f020705060a0c090e09010e1203010501 74
    0x600d440e020700081481164100300b00a04d002c91540e440f00b588504001c504001c261000c2500ca80c2c4c10300e0700d08140a00701c0c2c40000e07440755114803e0400520007218010f0116036158004010350079541d5103e4403882201c0303c0107945950380e21282e00c00c45080f0014110036040180c0e05035500d241985d00d40040b00c606030081e10361f0f1342c0402da0102c2e00c6904010a0504501d0b00c4c01c0801d45540d41d0443e1819208100f040205002c40c0d428000039a0320103a04000324904041c0c0082c04440016541840011114602201716500c001800c0006038080c0e15488a120300454440c1e2600382c1795242d103070071b4807400c4000311841400c00382c807200440c00c50709403448050b20850096240802e6030000480c0004180111400300003007909898856955912121b40c80c0d40c00f038420300000d6900b055000082d08000000d0318a806018001a0b060203584101c82e11020142c40b000805030500840c1402d00d0001002c0400641d47e610840048003800c005034203108011080156503581010b00050112801041c4035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 160852616 1250 160851366 160851413
    0x20f070801060e0f09010b030a081c0b061803010f0c050304050f06010609031101051e04050102010c09030f060b0111070909030e0303030f01090509030f0c07090608030f0a051b0613 79
    0xf409020404244660407089841c01c802264031141100b03401405006465940352264407049010400000003420015010039070700044440d54446210542d00503440e0341c2c0d40324400304414464083c5c0d466135218403000203000043c84030840f21140007101c10700700c19103000c118040100302c10440100100e140e81500783d070103401a94941180a0024080d9000040242c4225000841d991f4891010743d100484034034078101450142218030400c640c064058180194204001e034814103000e50341d11411030f0360080d032903540c041940c2c803a50014404150314504014a4410044150074200081d801030300416200150920040c43c01402122070f1900260103a0024810405888106080141169a040e01c00704055803440c000b603003035114070b000d80c03901c41c6804200440c94510020314881030720300075030080043c15102d2540756907074003034a20200200e03402000f0040209104071701070200c1034401c6125005010700350f0049400d26004480d042c0318401951012400e1201c0550070001104946050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 160853866 1250 160852616 160852619
    0x120204061205060c1b0d0309050d020c01020c040c0507080423010f050304031409060c06011806081c140a0809010b040213030807021f0903030216053607020f07080106 73
    0x4443d12110010126148a500841c40008002c40240050340403034002068500380c04e9803403000380040c041d209099510381700d11012081074130300000c0c1404031820140c00800740d040103034040102031300e04204040100700f400c5c01400d0004040101400c040c03c0d0418410045483d80029007692081c1c80d0285030410031a50500038a0940000440782c0003a0940f8000c9490221440c06034043e1042c010007580141c0005040440c105001c51138074103803014100c400c8880c0c0b48440010301518224040c110654110b80400b204088004050210001c01400c2c502c102c0042c020416500340c202c031101401207800c09082154032002803190380c2d516503003140c0441c00c10000710b1089010201a000c000d004903000510001550703100c0c07690588400350480b016250380d454810051604d422444118007503c15144442c44031039086031208107440c009001e1901011b458105c1107414409000301c8042100c0c0d03100c0d80c0031a8105400c0951140125400506642998800891170f20449030311101e4580d241110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 160855116 1250 160853866 160853873
    0x20d05030a020702040b1f03050c0406090e070905180901152402010e06010f030201170115081306061511060405070e060612010f051003050601020a061a0603011202040612 75
    0x15250800d07044400140c03280d1462011030300400102c02907a070320504001c03072888410801386540c5c2c1d400250343da00b0b201a854005c0c030b2107118001d0b03008c0c103804608800420301c5907441250942e91b0041407442c01c8080c140e50f69021034041c00342650b50074100f1402ca001c010304003009010783c903000402c551004003400e103000e03e07618100c2076401d8401e0142c0700c0c510000070614400d400009032004040180c40155a60318500c8010003001d10040340030a1035201ca44600d55240510b60b8101d61941c080450040c901c1d000440da00207000304030820400c10390022901048652003138201612400c20b14101d012001c41b000303007101c0b855008006043e03200d0000c00000800200741941111074038002034000d61980c400040c0311b40101e040c19007490310f503180000307503a04818943c101220001e5448a48a5010002c200c080c3e9000f1150700380540d00035006000060a541c0c40340100800c0401c014049182141c00503003294020b92010040c0e06a400409056141034420300c0c2c01000d11034482e080c9200d6954 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 160856366 1250 160855116 160855127
    0xb0d09061a0a060f090b03090c1f0c0204110d15050a050a1a0a0c050303132001080f060109180f0b060909040305070c050901120308090d2316050a12020d 67
    0x1810f0800c0801c8542980a6000e640c0307010181c1003590303883d0785a00e40a0b6146584d110554404c07441078403400384103100440c1c02400849020305035612058112010340900c409014501e41e081d0f0300500c104000701c00c24046106200e1429a64194010002e00e044104240901d003604002e208040d40003003000008540644e00c84102c040c080702a4403420f44050030f440c0081003107405885800b002080080509a034040c1e40c90461040459804419000b07a4030708041010340d046a0100d003c0f6008140701c2c04c01c00005640c003100514001d080e541d12a00b56100603078907603c8461101b0b0b110355020108414a00960407283c1058405e1428611700c200003a030341080c040e002070b0a000340090644144407040400d00003a08014182c00c0003943e40703200c3c00c0b0385041c0003401a8005204800411f6218401040f4141a602da50b551040e44c601c0109401100c180d2216281d4598542045a1b0500420311503070460014003403000352803000f14070f06041c0c030303444428400c0004640001d0b020405958211 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 160857616 1250 160856366 160856369
    0x11b150b0409030203070302070b04140f030a06150807080f030406110c0406060c1505090705010e0f0409050706021b0901030807151a040b010302090906190b0d09061a0a 74
    0x80416400224002022802401101032680e0040d05106002c020f058002000b842a18840d40c01c42c0c41c40b5907112035505040c000c030b0003000380000750400c104045180601c440040c1c000020f090f52040038803940e40c1003c039282c0b442103500c503184680041003040010b0000e1002844030b60040c103d900140480a522440b440c003910060103540030310780c0c00f4018108290140c680e0083c2040100549070340b00035210290302c0f02c013100c01e041e000440700e00c194007900a0f03034046d82d40000107045e2a810900159006070b03900403019004080000c079100700740c4d11400741141c0c16008602070103106080000080c1031400e554041046241c110265410fa40c0700d10f500b043c1100e40000310780d5121209031511002c1c280c101c402c0c5005090620b900d0110440d2034000725002a40b041324108a011002c80054044e4010702a54660180140300020b1040c1403800301e12546450134041c01071483d444074149100e540041f04d0390f02100b90341c1c1200e182040b4880c49031250201e02d1040040d402004000000c10480340c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 160858866 1250 160857616 160857623
    0x31c030c050705060106030f050105010f0839030403110313050f0a090f15080705090f090c15130e0606030a0f02040f060e150f040b07151b0e011b 64
    0x122800e00c0030003031095007610306859101c002c0e40e1003075a58800c018050302a2941c2440c0e21071030b000c00010658051f0318560020121511000c0140da40c0c40c603102c1c40e40410040c408400c07520b0414555801c58401d442c00b4182c69800411912030400d414010641c4a000705414101d0b44200320044042101071001011160102c1e420410b954404c0041002d02c15a0380c00486d11078104038241615031600d400003d60f400d05030008095166550803c1caa0b47c0546100c0c0c950005001c001082810121a02c40e07503010f4903a03c01c40d200ca0716210085590000c040d420204190f00c0401c060541d0300124852100428000c0640e0900d810b040c070000309140b0010340107074a042c1d40e0380704000e0b0803002130b01600c000341514518030f088a03586900107404454000140c0348118032154906442d411803d00b41c80e9080700a101c2c190030642040c4121185600201c001d468100c000c2107038070019095401484039903201c001c400e00382e041880301c001d0b1080d41d001300010306000d0201c84c1e040b4410040903040310714540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 160860116 1250 160858866 160858871
    0x4060f090212010c0f02030301151d0604030803010e010803030c030f13200916020a03050c01020c100207060e0c010e010c0204110304050d09090b0612090c0405010f060e031c03 77
    0x50000148000c00181600a40010720b19004080c840019404801403904e5034030352642000c400390080381ca92200340918110341c00000701d150340e00b9115502c0700c0c9020044106600000d60b0600010710150020341c01160900d00000041c88140d84006000b80100b16910045095060030228103040d40002000400c96411000c0001d00686c40c40501c04d620301c0d008515058001d01c0d452480480300a0050014011404680444c0040d4075490014800d5985540a03020220b81e5580c03c49150b40303ca003040c02d003590280f0140110b0102404805d0f0405046800181d40c0d50385813034078000342c4892010400b4142c1040790741d510700c1d9030803101c486031802c030034681400da41d03506100040080044609000c55881c01008100402c0300018107881c0002290322144810ba03039680400c1d050380d1200c607203190040b5003448151466400d0f504400e4100e40c401003601c80c521484804a800c40d00240c4c8011040300403400100710b080d80002d120280010160040d00454020700210344014501803010300c00c159 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 160861366 1250 160860116 160860131
    0x506040209060d0b0408030a0b03071401140f0c0109170a080c0c120f070c12151e15090b101d04090803100603050c0438070510050a0504020303030406 66
    0xe844000d0b942c0f43c1c6901c03414010f1103040030700309040c058100701c030341407026032800f40e84620500c1d000508900f20782c4204555580301c1c003207600442d00340e06614081c04100d9000c1c00b080040c44500d00103005804500c500001d42e2902c02d05160388004448074400108030703400c00452010f55400748000e544100201d150b5640e800a4004a41c50809000070004511202003a1100b0954070075000745a81d60040004d0245981c43e050400c1103540c2d004070082491004c9e41110416403482c3e0091180032200300040103004041001890a131002c4061042407229200b4040c05160514480c0700070100c0c068600c140c1c1b4084040000e821a01c031002d10500003401d0136a020741585d1160001e418640d8024038807501c90071b24660035036010b109402100302090515002079100040e6100341d42c100d5800e00204284085e01540002c0101e00900511910040d1ba241021721a0300c0c0000074014640300300c00804a40906041400403254060503400000c3d040c030040c80050b03600081602e03045034000d0000108070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 160862616 1250 160861366 160861369
    0x50402030c09040908250c0e0f01060c02041404110312180103110904150906050102011107020103020d0e070617060603040f080a020a0c09060314010504080d0c052206020712050604020906 82
    0x240191b40850003102c10251a21040c582c0108075400580c0c4070303c500582d520345030300454491390002c030740e0041d000700710000410006203d03041c1c00c44903a0001d0000195001c03101c010190400c021201a01c0c40c0800408014540c00c007045000310b40c0c80003200242c10408400e1240340c8810a550640303040644032419040114010700840e501003000800c20840004107003001280784220381703d5080800e14198001031194010301540f2101b44a400b2124682101c683c0150000c1d0080100491a50303a1507005104500041110f0000303014107843d242c00a0a004022044405d03008080740d0041c08180180000103811900c0c20030030030782c07004213180c490894800407403800980b04006001a900000001011951540158150b9005242103001c00d44030051043c00c0e11004e4a008085000400010070807a00766881280e0b039545920f480c0e032614a00220b850004100c0149005002190140800407150100305d0382e00200140460701805400980741ea6031200d8000700068000d40c5181c00040c1ba9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 160863866 1250 160862616 160862633
    0x1d01030e030d090302070618030b180601090506040e1506010f0210091b05011b0206090f040510060f02060108060106140d020d0e010b0a181a1002060402010207050402030c090409 78
    0x100c018104030394850420714581d00240181c0784094015000e03850000c602144214441c01840e4810b9002c0c0041502d19510000c00020007843c1d0308482145a62101c0340e4402401040d000340304415003c0352605000041200310b40c240104070159134003c0040d09001131400ca009580002c090802207142c10075090140d00b8075100d148000c0d44545482c03084800c008c44e06002200f04045a0030240d41541c0340e0b0b00554a840005219241d40b07281600703084010f25203c0c0040c550710001a01008100d12581c021506407242508e01100405d4001c0090182079841141c403e0a00c0c85403000b881c1a5150061140e2501d01c1800f5220400018414003e030040041c012252501e0003880115070b501d0341060800c0040c80076101000d41c65080007074083c01403800c1036071041a034140c094a5035070002c544001c4001081000105888000450700c944002c2d914884840285172880d00070b42020714052000908004454112610507881841489600c00080003540d05200094600080b0065103040c032101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 160865116 1250 160863866 160863881
    0x110609040b120601080105071d040b060c0a030305090d0203030412030b03070b03070201020703020f07050307061101060b0c1f110702090709080f0705130903020606060307030b10091502010c1d0103 86
    0x10000d810041c4038004602c00141141260b00c1d07000200590b03191113134100d4030983c07001c80e414040690414500420301c3c15600408041000a041c1e51a24607040901c90428a078082c003980841e6860b0704000e902e4a007401484454440341c4007079480d528107943d03010b03002c0c08242f44280400d95104110f01c0c083d00d003003246402419420008a80f21724002e98002e01039400001e08400501400d0b414802c0c0610020b092010781d0401809015180d051a604070b1362040381080c1042c0303d6486010000f40784103004010a009240c65020382009a0100c0031442c4030301d0703159080300196103018003000c1d00302c2c00003003640c41540d07040703d655003c0d07107905008030f51224454000a9143c0914661485503540001d17012088410039100815200b0b1558901c004890b40080f01401503000703800004c806282210003180e0150349801c000a62031400c1c000301d441b40b089200a04041221001c2c180700e0740f021507041ca8501000740c40203201c400c4800400410b502200c80b45d0180b03415402c803103485607038021f410041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 160866366 1250 160865116 160865119
    0x6030a0b0a14180f010e061303140403030203071403040e0112080702090a0f0e0312070e0d0c0b0d050a0504110f030c0d0f0b06060711210a0b04020f060403110609040b 73
    0x599414914a481803d20a100c003031800c0c1c3c45020300c21022007074103001b520282e610310f2000e403141d42e40b03091121501e11681d2108400300170b000005038820140c0170001c1d0000e14003960046858104900c0c2a2030040404031407c0d555030304c24001044680459080b00c2e054900c400700e03100425011b49851aa24020500b0007035200c1c2040c010014000e003e0750140210000040041c4800340164070603d03200e100720009000e014449000007410103004608132400b07180c0181c54035190404035100c2104614194001d050b0740007001503900f011b94164040c03280c000c0c1c0004800c0101d81025500e440111346405c8045010350f030703800389258041d9402d00c000d94504402421410b0b198a19240600c0c00c0d80e5002e42c00c0750940782c44800300722581001070a5074110b9a02107842003a40c18451f0030800c1c2d0861380b008038207941d0031000e0003161100c1d0500c0b055891034400c07140d9200d07a0516204000ca02400302d0403943c00f9981c10b20080000c82c10a01d21108083e0b003e0f141c140da1101c0000c003103000b4141042042e13 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 160867616 1250 160866366 160866401
    0xc1404031e061a1509090610110f01020703031b021c030f0e070302120d05030a050c041221030b0319020a0306060b0a0f02030306010806060912010c05180906030a0b0a 73
    0x40c02d11280d60310b141c41850b040f01c142c0c1c81c102c0b113494940002c1c019140f040390400708a2000800c94140209020360302e4860b401c02116822240c0041444c0c88402c2d070140d140390350007146038810036030540116480304100f2070522014480c0007600035036525140c280b06081000c0e4190200c41c50303009500c411068249620240312401404003800d40e541c01c0c0344001c031700074802c2c070300840350081000c10001c1915a036540e60300d00d10b48640c402180070701005000007100400402c40015404042500c0440d40e9110750a80c210406d80004021055800c40031072105041c200104554a9078000c190804003519030f61140d0002e4030140042a800101e64100424a41c40d1010115a00080c034014111040c5180d940c1ca41d1403040e040126101e01054895a021545040c04280180740c040b024000c90100601100c58031750602c41c1309800d40c0c403100c030b01002094002450341c0c03000300c0c001c4041810310b00940347e04003581008804290f903007030300a5010b030899807000c010520383d03003150b0481001d01103000c096 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 160868866 1250 160867616 160867631
    0x2100e0901080a1a060904080703110318030c15040603020a11010e0102030615040305030403021302210105150705030d0c05041706071b050c0108090c180603010c1404031e06 76
    0xc450380c3d1481420142c0b130212080b043c07491501d103003950351841000007504802143c2c41e540e4800c1e1958108550443c1445500c20030b4581c11542000900034480c2100d10400802d00035074245420880e484c00c4182c083c22a88440311800386101c41110119a0755140040c3c0c0d404000380100c1d00a88a0f051851055081001001c04003034150061401201e04480c030303d400c10b480c0400d1380028410381c071004013180c00070b00c4104050300e043c9004282440300702030b0142ca020000c14109c0c14045074503500304010840100144450300b4140d045007049015040c81031314000d402d40320b69581c2e0091452004409031129401d8014a00c038005031001400c0f626005640984050003168030744000f00c80e040001002410a03038038031010401e02040c01a040700280202011840c0111039402006100d400c9922501081840c2038941103d003a03c259600801c82c019410000105401d44214103940781c200025016500400ca0781c460454003141d41c1b0a10300b8041040d20415000140c04441000d4520380c6040503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 160870116 1250 160868866 160868879
    0x1103040e0a1128050702120d0e01110309040b030c03030a050a1805010807030903090521010b0103051b070203120f031009020c0c04020c030c03030103050a110f0d02100e0901 76
    0x50060003000c08003000d000160000011510078007901d22101d04202c41800b84030f03025020a581e02901040501e0300300e2070200e858010504401036510141c010350300c8800a5864158400781c02c0d48100000d10f0032a040c00c81444010350f07240529440280700769078030794203070b00a5074040007040e00385040a41a01d40b02d41110501404980001040c1408200c02114005045810449410540740b0503141c658064946800440082c00030080807024404414004501a600d000b524035030f03e040c07814101d602040d10200e00c9d080d40e0000c011030f4141410b000c103110a4174041c2550848070a44030140343d03100c000e01c0c00044c1c0b07030114a1403621212100002c0c440c40000c040d80086108075003d0808900660703079072413013a0492150751510442c1c0d4109001c10000352815800070300c02e4800345011a4200781010540c84d0441e4001c2e44112034030313030149180714100310b4007020b603020001080f115601401c2500021922036044484028401c601001c50361843c1800f40c11003076415500a016004650385442 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 160871366 1250 160870116 160870139
    0x50f060c03090d0b04050c09071205061908071e0302060304140c04090b1515030a020a05090a0b09130903080106080c070501060608100806132301021c0c080f1501110304 74
    0x5d0381034605016996400030035091125802d4042c42e0703990303240300802c0034852103000201005070251b070b84940450119000604080c1784600a041c0b1200070300011442d0114040700f50038101d20007007100c60301e54001c1000d039890300107036540103400c4501051120203c48007542030140c1d035219130340d02a160070610000e02c00c0d21a10203108400d45480303c0383e50a502c0d002c00c180340565660302e03004000c08000240207021103030040c22000f4800e0a182d0300340308881c0d000034005045500002036a240124022880e071806005040d2041c0307030100108400b10264400034402da074140030b480c091101c0140400d02e0707078030b02204540b207603a00080200b100540302c040c0182180000d40c1e038031000799149103020807882004140c66018003560030a4054000ea99941e13980d100c05449848183c180d101411582e1419003030004004081054006684c0724000e00104411901091700d90b07030400482404101c891700b2034050b413903001504c54400394101c20980d170048075104070311a0480c140340004140001c190b1080e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 160872616 1250 160871366 160871371
    0x7080307031103190b0d0b040b0f010f15052a07090b010201020a08060d0f0c06050c100204080d111011030411010c0201142203050d0206010f050f060c03090d0b 70
    0x160303000d0024440303030030441d02c0c2408181e400c1070745034500c3c0c0c00000804d07030a13511203005000301a04490748042e0340d4549807010350088a05940152a40040003481e0181244403405401c922100104040c20f105003030f0b29690036040864107100c40003d103110040003810340003c90800f002d40640c010051800030584640042c81b4848a050900215803880c0d801802643d440000e40c0d5560052642e40300c08004510203c0c94003580c0d808203030120030020880c103440c203c015200310307100c035540c4074401e03181140b82900c0103d1100c10544140404e004617140030a8615621484d898818680700000d915141400c5003116100c02071458400c500604000ca4009148030341d02801e44910008282e44c015180e001040300000e0004100c040f000e000d0078410000b5000c0e11040d540c00000c43c41100c40780705001042500300b501d040d444100080c0c0d002d1f078100070883c05440713a420201301e11403400e0007041001808140b042d202d10000320b0760b010b00060420aa4400e45002032080c0300b40d203805c5c20301c40b1107443d06 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 160873866 1250 160872616 160872631
    0xf06050703051b0f0903010c090e0709150c030215071706030109050309010f0203040801060b040513060503030a0e01020c0a092909040b090a051c030c0e0d08030606040b070803 77
    0x249800103000d540640304041c8200b81c609901c00801020028030507182c2e010354914038421000f07214880207501c091051180303c2c545501c400d81c185040442d18440074070700408840070010081403c0c081094211080ca000e80c00d40e04003002804040e00d800d0342459681061016290454410009900d0f8851442c00c102c0a46d41c0341e080b155121507050600b0f0315000240684240d100f04203008440d4402e107140404680b080c4162401d0030303100e034055400e585040e0b00c01c41000c1008101408549014140490a040007220400ca0107141c800425201e000746004c00003840148600710820380d000f4070000c0040d01e0300400404078070361a0b4542d24000e100036400103000d8504a10554000e1011130221851460001c01611040d9101e90300c0c21010800141007210602440c040140017075020000800382c8440d440483d024120941d6008045603e80c074294802c00c0b4251a1511040c1c44146000e5021900148495566600c803000f01d42c03103201719808004801e000140880074030800c1006035010784003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 160875116 1250 160873866 160873871
    0x303110d0c0e24043f0210030b0a0b09010504030c08030c0f070e0411041407080f060d020904260c010e151e090c0d0308060f01171911070f06 62
    0x240020600b80b00044541c020400c2d481004103210940c2d20300c140022001e0100c41c21030000d54180c01103448000650110851504040c100300c01b14503000000107600b214502e41003101c006c5c2e100004081d0300a52198450444002610040d964400e0003180e001d9500102e90f90407440e03890048580e070790300c1803207012014000c10520094984011507040101d41d035401001d0415255500c42e548407940640d80070790302036611821141402c3e51101c15611807006a11100403e182c03010341c901d40c0380402400d0a100e4614120800d005036103402c0010340040d00503201080001d8003801c80300c0000c003d80010a9403040104204048140540003020106000003d1320806500680b2542c101207050382c0d110510080d030f010700000782e404c0458055001580c2d008031005400310501140000c0d400040550000b09018104003e504060011103140c1e0820b180c10b0940c0c0302d0b4000414081c01c0050000c0408041c80d0807107015400c1030b90400c10000041c80d4610799100403500e400c0481240c050000c4a0003030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 160876366 1250 160875116 160875139
    0xe190b0103120503011802030a0f05010602030d050f0105010909091103120a02100204060801060c0c0b0a05131d040f0f0203060c03090c15040b0705071a0a12090c030303110d0c0e 78
    0xd203c0d4081e01c0c1228480c2001c25541107140c0003000203508002e0038640d405648030380420004c1250b006141c000c0400d40c026590b9220b00b1a50740c1d0666000070404101411a880100305a07644403d0807002c139180200300040007016454503d0b800c2410202056241c45117034880d4021300b280000500c8044d003a50200d81c01c04480340031580a9005030300c1840d001c030362604010030241d40242d041c0e0b491540b00d04030200280b61910402400c6812142d00000040d401184190714620050011300c05010403480c1001d98400010f089014000f004000414980742080303080f0402202c070960f20305580c0d005050303800d946400220601d21380c10444188242e40318200080c0383d0360170551030101103030041021040c5400d05081884501da84140400c503441d1140402c0041c003030000c450304078030035110403141543d41c0ea40740000619000f241c21002d00b903645000309003000200e2001c000d2049982c50306012810180642c615072041c0108502e0a070303440c3c1028910b044007036020a24131310040080380c3e04030700306 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 160877616 1250 160876366 160876403
    0x3060b040b040e160c030c260901031404121b060509010f06050f030717120c1c020303010e0f04060e0102030405070801060f080604060f09020d030206010302012607030e190b0103 78
    0x1801300402d600c000c5030440100a01080c0b04120748000f1600038260030350725103480640c882c403010004141d0000a000890400110745e810701840800035030440074501c1d00d0034251640c0c0d55001800608800703206540340340d0886802c0c0b00032030f82c0c21607820110803c05031614103036645c003070074500110074100b620b46100400e2030f140c00c00000520703600103001800c005080c050009203030410050b8141547c82030550850301111500000c000fa84085000b130400d145856851501905044001c0c0055400610040c044840302014143d841780c0343c0d030a44803003511642400c000074000b0701300c0c058a9500000c20001484000100c06080302d00401c001c00220b035403071450b803481c2609401141e1080d04005c1c045404540d1315004280100614140001c0c0401103600007441c040c01904100c016030071440041040d50b0300006084100440060020306030600170201c200c098000400348410305d643c503000c0b1984100300700400a541400690154000d1055081031101c18100b40700848414900c4a10040c0f013 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 160878866 1250 160877616 160877641
    0x20a0206012904080303060f12061f0f0303020c1806060a0c111302030916080a0b061f0f17010b251709090109020901021513080406082a041503060b040b040e 69
    0x127003400714094001c580b03864285507000c1260b4081880005004040801c1300c4001c11a010021880b9400816a9411690900c078804950381c02c0005a0014041001070307070b4035900d046801007615071424900c00c103000c0c90180e42240074960b0041c0c225040320304400000060350b006500400c8000c0454a1803030101001501c14855409091070640103000f080b0f000414140d80260030a00c02411510054032140400812402c41403640c0c0002d15030142c0584c4c102d8005c680400d0610740c44510010540c10b0501d0384003180f0420000311500030b4040122640f401c0ca06828908a1345c3c80706e03032084018904010462160408200c40788240540d90002980030309038801c9840705041a0050520000114000200c0160040481c40c0c0c8500032104000020344190051000d0125500c400c00181045421144049088a61941c80e1441c01d201e00c48040d00c0c420683e0b04854003000400d03403041044400b240905566400500064030200340841e0101c160005001990100404185680e6520110900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 160880116 1250 160878866 160878889
    0xf04050702120705010612110a080a02030705090703022818050a03080702030f1f0b030a0312110c0106030c090507080c0405010c0f0b07030e060a020a0206012904080303060f 76
    0x1691288030104019007001000e040414015000000d1069560310444654aa4050112488e2168000c900720070f103416211880640241001420070100c41d42c040303969283c0c17078011a031141029000180c000707407103a0119856014003c0f13518010030f00c01c03a44119821124142d6001040050042c2c07010080076075034a0f011600002c058601051643e1144441540a610241e0f094020b0f82c0301c011003c90200042200e204040c41580392454103d0700480480e0801c2c1080d44c40398201c203880704003081d803010324000c13400d528a90000f0350485e40c1c0d01d4894148910507400d2995400c1c40400001c3c80030700c2e0060000c480040905100350b50b519182183c0e903000844e0895940f81040c003092015512400880c480c140c805e100c4007440340d03519150000310100c200c0350703540003c0d120600c2500312001801a0b03a048218400250300b0a58040000b94031018140520f0490700711844460b40c0302c540601d031810a1801c20035526980d5900c1d000719540b00d51085a0660094915044004150078205071711034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 160881366 1250 160880116 160880131
    0x3060e07030309170729070c1409010303120b21061503060c0a0c060204030602040803030709140303070b090c0d080c07060203041203180504020309010609110301060903080a180e060f0405 82
    0x8200d824030710b0610341b031101a24000c1c00702c1d0a520b01c420445450f1401131100500036402c0c0101c452420740c082c0f854050202e2054042c0c60410300402c0000d40100c1c00040313000c41d00c000810408120320104245001b211507807031040b040c155000d82c50200106480f4003907926000020f448404101c141940ca840c203543c42d82d0f03c00c4d03040101c0c04140d0701ca0b251440415200e05405890b0554030f844100a1b600545c0005526802c0041444001d6801c85c2c2c0d848014401000002d01d040003200029440340940a0050081c1140400140c14542c05002800390820000e104000d0501039062210f542d41080c01000100d10540c080800e0240c000020f40d000c4a860340407945100d000c1795011651a0f0751240003540f038107558140407811f0760b50b50014601c01e40d03200000087c40c920f0045108180c4070303101a041c2c6803c20400040c400d0a80c0720b1011800c0e81d402280e110743d01c05180300120340a000784000c00e0150303580800003041154100100c140554411100c01140c2200c0c98100411a90242c0e281d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 160882616 1250 160881366 160881373
    0xc1110060501201504111314010522110703020601060903050304090b040b0a080c040c050903030909090a0804090c091d06010806011202033108070206031003060e0703030917 76
    0x140380415500551440f0103c0c0a800e503840300c2ea440010380c6502d00151001c5600c4442c100e060703e01c50820070154442503000705018402c1640480c0c4010703a01c0380c1801010b00601c1c079903651b10624103007601b48491222851a0410201448840100284e0003442085006001c0c1c02d0000403500d114840010a40c0d4020000d1403130149480840d000800b02c800300b06410640721081100e01e0740d2603012440041c50140301030102040034000700000c550341c0310042400c3c002c062010001c2c50328008155640040c05484606c00c030740f0b40040051800466580042c1303c20000940882d103c0d2441c0c00001d040ca6107516504840303515040044164110f03551000c1d841e020034000904150722503080181c0000040c1012000c5022050301c460607a8400c95003600f00b075a4071400b60b10350f01844003410040f106071916540030580f007551040200d1040c2c07a40684922404004103105420342c0c20020010b582c000c104000f5251940c40340e60329080144416404a80f038510000b6004402c1a4030591415412014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 160883866 1250 160882616 160882637
    0x1e2217070806190207020a03050d120b27090307170a0e061603030902190602011b02030a0c121701030f06141605070804030c080604050d0302040308030105120a060c1110060501 77
    0x80e4009412091086c1e034030560b09080000410030604c44d04014100d19568840a020180194070a032004034070700d039004440c82c500320f000302d42200700011040c4080300801a0755480b4190031515600813500b0182c02e5031005224211907108072401022032450750340740d0b03002854200040045a01802e401b03034180030149260b110000748030f6171006143c18030003800c04c64054281c200aa104400c1501b010000d83e644203d00f50701486a02c1c030f184a52500c510003986803110904005103030040400e4014103916040500c4a8581d003d04003a0324828032a5010040c2d131f696a007013030490440c40003019110f003807030104115412000b2200840c8100314207a1882803111a00c2d000703c40f1640405415110f40005000201c0022145440c0000030030b003200083c400d9003802d0420500f8024507032200e0042c127204000401c000394072001038030704540d07080b120705c1f15030305032127185a0034450011402844285010340850445412600300201110b143d401c54400c0c1e440180759104445181c02900d0116816412 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 160885116 1250 160883866 160883911
    0x6030601030608010c0903051209060f0d0e03360f01110307050105040507060f0329010e090c0307120506060318030403120c03030e031e2217070806 65
    0x15a044081032600265896942c4443da003142c00d80069180080d0100508105000c002c119800603011480300040c13400c1c00c8003000440c035100b400c09021a1480124203c2031050302036201d121420032900c1640c0c1d85940002000380940395541c0541c8800d080302100090508210a01510101c0050480c58003100d2040055503030003000b0020481c148001c000c0240098402c0c0a01d5000350b12840003020107a090400c060303c11004580c41c0d100305841c00c0b10a000c0c10700784a001088042c08100104100899080101c514000000c651a0014560ad00340524108400c0c020740c8106660759894040d200c1c190545019908207507690b41d8014014408107016018150f80a4600d010a6003242c0c03805580b5910032200c0440d00b040a0f01264458100c0418160036005e991560106c0d030010350718141c100440b6101c007140d0b003180024581c40120f01c0e00640c1c0e4824441c031000f0900b0400d14646143c0d03a0055084031411150b40b000540a100000140001c00042c038501584030100038025100100c039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 160886366 1250 160885116 160885129
    0x20a0e0108060604050d050109060b060a0504141c15060b090303030402090711060c0c0d03061d0a060f08101505090a020c010908030103080a09080d02070501050c0f06010b1905070809 80
    0x246480d5200d0360804c000030f825507800a14400b094030030400440c0980003420160201d507104442580180b80c02c20103003002c00e620404450603a00f0185071004d034a100b0102045203c03082450b980d480c1101c40381e910084c011703030b20030601842d0f0600c44103004450720f81d0b4805032140184501d0a0309548140b02140c0107107480c1540385e5000b1f00345c1c035100c042403007028026450982c06840c007030001c140002e10070729042800c0c00094043e501a06090200e5441d045c807100d61034060484000405001c4008502d194159801c030b20000d290f2000c82e6000d0f1600c4e203c00540300c80310302107081400e501e8101c0515040203041d682c80c080301c8006080c603043e0358032200c8100c040d42c401002c409140d5072318940040065201400341d4080c5010301034840c1c4509101e04040e00a2000360410240ba0340959083c51034540d0000b03024060707d1082c685207840780c524080c44c0e0301c1c0100c0c11301451401e020701c03c00450103401c46000391405140401c944840f40182c81c40c00c0d40d091180e10f00140403068100042c005504182 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 160887616 1250 160886366 160886371
    0x7021504120809060705030a09090506061c0b12060924040809060d1401030b010303031a22020c0703140601151b0f05010501090f060503030f0702010f020a050f0601030c060201020a0e0108 82
    0x1904c41d502d000d5190b518181503912840f001d0010680c000307400d000c1c0c001207201c0e41d070b441401611234500d440484d5425002d40610243d1510b070103515042c0c800340e00c0d19842c2c2d11860305110f00088421030300707007004099102c00c03041e56404d802603c1802d14038540c410445203c2d00407900080c203d440c1603600d5040c00000e03070203900d1748440c8548548030780d41403000012125000314042c10405034a941149001825103410448504450044800156060b6907000c240d004000c50b5000708000040d2401c0141e000c0d0143d0050221607005501d8000700303014984045455190305102600c01581e00c0e074003003001c1038a09100d4140000e4010030b80f5010003400d4540041401e00032409c04032001d507a035886900b9248260030a10605451b040840710f44400c40c003c1ca006000201c01540c14104a020380c507119010b0160042d0402000d031007207039007060007800a031440b0384d080000c1c0c50842202c86c02055035407900b0310045036a044090f5001686a20610a4030088810396641d80d01c0c540c4404011105010301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 160888866 1250 160887616 160887619
    0x3010c0212161a07082d01050f0d020a08070302012607080406060b0a020d030614090a0203060a0b0423041119031508100605060306010c0b040305040b0703030207021504120809 77
    0x42c1507044861180b001034644078940751755800a180c9020700340f0b00900c0a40301214201c3d03204080d410f4011540e101c0e14039040d41c1050710751948000c80c0d031001400210244001940100f1850008644614046084825a4000e0b01c403e0072500980307101c45a850f04901c4020b80c0c002181d0003180784144a031040700c0d0424000c0c800400d099480303220320581d82d8031a10700b00300968271045988248542500450300101350078280007545030f10240c0851001c2e20700500c0d00d8400d96000001903929610701c2031110203081c1740c1c10019142c50f19440294078105600e100c044005d10022000c01141c54a0302880c0c56041071116500d00b440d0810f800c0e00c500f980020494401d064441c640303e400b101410303100700c000b0090312006000c060003000517a0101d074807a0704540e000d00810020825266001130014494981c0840701036011b40d81e40c00c1c200c80c24000c82c0c003c1d4445610000303250044c543c3c5a0041c10b9400e0080355400454810342103100382a01c154030a040b1301d043d2400800010403080c40c054020356a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 160890116 1250 160888866 160888883
    0xf0603090f061415031b04020f04030b0c0304060b0306060f0108040614150108160c02061e0f19030912180b030109140109020c030d0b0102100e06010503010c021216 72
    0x1c182d60b4403043c0c4040b240101c808810003401c1010300d000039400800c055100f600603002c02030f1016007404034444564030f86402190000b880640d4543d035602220000c540010b160441800c1200d5564016071007a035056070864107000c0c04240a04e800300b0054056403008042d0707000d018198005617225071005100355446039a811940f0000715070b003000580f00d400c2c003140d0768212503d03e42c0094003502c8003074840440b84140c4070500d118980c100340a0340c03100350101d442644072070701428424040741c2d141c034010340a4680801d401529040741d501400100e40c030400100d010440070f80c0700b00d040350151800038145014034100d00d81d4480c0518944601c000082407039624050b201c1041c801964000c1c0d0011100075a00e4245c0c0460041c600c168502411070724409614090f8010455592070085869142480baa9020307801c12503802080f00ca541031210240070700480600d0103000703446400920401c1c5c001e50070030602c00c9034207201145004c2c0541c56031403000e040c600101c138000c0d250280c1c144111800f2a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 160891366 1250 160890116 160890143
    0x80f07061d04050a0b12060f0103111207080307060c050a080a0506060412050c030c01020a031202030a1b030e06100b0f03070905030609071d010302132004030302030c0105010e010f060309 82
    0x2c955000d031601c01e00d0700c49030105d000c1c05102c043c00120385030400705110680005040c448840300700c0400e1411203400000c0f10070140d4860700002e8294121140d5801e00d44906400061000004005800b407075016480030001c01d41d00080c26a450310903442000009131807a0300240c0081c0f01075011640050003c0c2c0748504003603d0b42c013048950014044142c2e5203600400404003986402c101c0000568000e01c0a03000f6071040c2d0f41c004c3c0180001540080720381d40c0100000c0c581141d59400440321607407181e544000040d0b246009001010ba2448482140c040d840010b00c4198110031070600701c0390021007031494080302002c100c0d005d4002038005030400050800010306681d080081038016446400030f03012140c84c1c44440003244054010041210480c840108050795410508040d00001c0713160100e04103542c080c0140300e0240c0c1c98170360180900c001c20080b082c194000302414111120100030411a6240c035400f5030600400d1181c8042c010b80c0341400d20825220b9080618241d100d000546d42c200c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 160892616 1250 160891366 160891369
    0x30509120c1018080106080a03050a020c180601080f07090b09191e06090513090f050706020706021009120f020114010e0a0c1107090903020307060e06010e01080f07061d 74
    0x81c00e90303049160004400d005415142c80054110500900504c0c000304840d0b0300d000c0a86031516003450019041c840f0104044c41041d00a100700102c0031001081400f810384282c3c81e620305050150740d864002403440d4009407841c440412181d00035402c1e51a807040700d031300e045401c0d01d4690010b103c00b50400b00419400340380040b0641c80c1c0001e03219016140354400407510101c1b20300c40d520780c449010010100e40401003601c1d01d06104505440c800c50108080c0481d05140081441c2d0300001002c522607004001007060303000c20010141d4005034280e80300c141d10b0341c0000b400d8030080e00001d00032211900400c9005805181000c001402a000120343c1045c84085088a0300d426489000e0702e00e108810032100060a1250101c101c1440c2002001b0303071607100040e551201540610140c4036039400b0a0350038540200240c4a209c2e6100e0004d0014241e0700a50588a0000303106e018082c54195001040c0f20002040c90700709281180010044c652030060220b07451555030483e00e141d03182082607414903 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 160893866 1250 160892616 160892629
    0x1090507060201020306030f0102070c09020306030307150f0b0307030803072105100501080a020a1d040f090f0209010506280c0602070c0612141b0f07141603030509120c 74
    0xa01c03881e0001030b01ca01e0500140f50522144280680c61640304124140c00030b4005040d0206981c2c0590300143c49a48010204e031031442034040c00b61107903001042c620100700c0550440710950b081d4010034098154081c003407550300c2c141804000c0028030700303000290089116400060b4400302c40d0913000c90342180038040100f01c5400751040001c080100c40c0501c9956049000c064002c000c40e601180381c00500354000b0302c50200e2003104420602800d802074520f6403030340c004940c40c84000c1400c015944d900e01d8082c1c5c0c141115841203000f80c0c3c1d10000000d00d89860302c2074400100d0028074401489040940714840100d141e0f0040c000d01208640e0300001c80e60303620207044114880d071914440700d41414070242c000c0184072294204e150600040b281182c0f0b0619081c1d4016004402d02003112800000e255a01d000300d41310741c0a403900121303489060000c094001c417a1a400801075031442148015454071b484031900018000c0350341004094040d0404c5001840058a040d054500c10520540058030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 160895116 1250 160893866 160893869
    0x6041a190e010608070e010c05120d060e0618070c030306270509010209011407050111030906070806010509010e211b0306060a03050703020d151401030b13111201090507 74
    0x44203514028044000e903081c1242c003501180c10407400a1070925001400b001490302441c0c100300a0301c03060000c000c07040014290304180702d020031307031510241260400144202e04c03540c10750401c4d07500418918180503941e9aa001c22240036480340303a6803c0e40a41d0208400c401c11001c2650301d005c00116a50200d0000b0a900c00b0201e0304070105520b040507100b6100080c1c1070400a92040040f080607a0f040a070300c6c05c07585d41c1c04442544825060918900401035000f48032030b01080001004003031000800d20703521400740f40d100c90201c1d440e2180111418001d41c45a540440c07132a40c1140c0c403625204090b40d05e641d265400d184c0300d21650348012428110990803001d0000321044414403189230620280f580840103a465121180ca50b480e1a40c0c3c6410601c0080d000b11410307401c0900f8010b2802c03d04810750749449060101c1d030409864042010b10900c4192049084940490072059000a00113851500071040c08104066001044001511060007800645d0f13281c940c030300043d400344188130 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 160896366 1250 160895116 160895149
    0x30a020306130b03030a03090c091a031207021e0f10020607090b120a02031306060303050a0f0e030706360f050907051e091305010f0503030a020606041a 67
    0x1612030400714248030894080403600c104281c2000074558a9032000410360f00c4100362460f01040128140c24124a0208035070450020360303090960f0044010b1254007075900b50031007541154489450710011015130700403d0b500a40c0003800304181422150408280340003641c00a0000f45002121400500303008858240400560000010040141d4000c43c880004003140c4c202c0d5450f1070f803001e00552280b0b0b4014511a1241c5e40800800c0016100c04600121150700c69000c000b40b0762281000751003900021081340008028800c4070b422184603219004151602078028175416003820400c0d1026101c0364004030044c1c0801404c00724515030554244180741030b8a15400c0e150303090927606c9490b100d42760082801206500c007031100046c1d0000c00c645100ea1454600f41c025104001900040d200f000c00e410350000c0604c030a00519409503200a048890150500001c15030360024507480f400f03001482005600824006581400c290308043c2c5010100b000c1d95941c0c2561200040221141e4500340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 160897616 1250 160896366 160896371
    0x602090a081b030705010e0d080a140d050f0615070f021527030f070603050601050415030507020610060e01030209130905030a020c0307051f0207030b0a0b0f150909040512030a 77
    0x502e1a080900090001d80001e00c0c1c80982a030718040440c03041301c22000014810180003500582280c812000d041348058203c2c807681d6113104205d05c0c54058003054070300410f40c03160361000c69110f140609590712a011011710280c24105144c6450400740700b2440c0c1a80c1002086425203114402000249503901d9400c0e042c02045d40a1200400140c1907202d0060081d0f00481449050000001728801140d085182c003150300d40e110001240e0500482d40401c1c001e4403507030301400f10190581c000c188108016405c80d51255201581040c40300510f04c40c517404103901e48103400f21540300703400501d40003101034444080c0512010f64941100c88d002d1007034a65400120301c04601c1c0b5814003c2d0035988008078002c0840d107040c8000108a1501c985403600c0e580c0400c061600e107140203111700002180c12a0b110102c901d0400d191102800c101441300748181d1250401c05014035007013810505006034008802c0c2450744035400d114240754040c0c401e9a103403240200250401200e803008520800010102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 160898866 1250 160897616 160897663
    0x40302010e010e030d0e0c06031801061a0a030b01020a0b1621090201121b052a0f07080304080717120a09031509020f061303020a030b0402091f030602090a08 69
    0x41c01c2124100c500160103500408000c0f42c06564850584c4d4001c54000c84512b03d07444120252801010f055001c140d103098401c1e10000c00c683c50001a050030107568402340409540c0740012600e45800d503000908001c41003012400c816080c80044c2c0c001c01c0741e42414502907410540380500307010b01d0b8a059514540311030540f811542d00c8040c41d001c000e0821001d1100c0c3d8054800c0e2501c80e031030264442d04101020555451481c00c1e05c140c01044890700052100901c280328407141c5490040d1000101071050ba0350001c0c940d0800012142100c80c144003624400e41004a00241c50141c81c03000d18043c03080501c10b103100382400300105000c0d065520380034111803a40c98000c0c8018070034000945114030703080f80980980c64001e404c0e149640110740c2107669503801100503006040306c0d000690092407984010003003140b80c0ca0654040c03030003154030714155652504034000303140741c2c00000540308200400030030020b12160043c0c40403420040c40c10200d66211041c070ba180c1005034045040c4440c2901c00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 160900116 1250 160898866 160898887
    0x1e03010914030711090106090302191d0604051609090b1909020301060305070e01080f190207060f0b12120706061505030a0c0201150608040f0807080c060f04021305040302010e010e03 80
    0x107404c1048251074041d25589403d0025058400300c1c0300c0a401851000c074540c103a0045194400084d001d0240d02800d466080e0280007044001101d0160140f0310300004170b44560011807005080c05c00b00e594540d842400c0040000c046c2140c4c6400a80107a00b0354540d1400d118204245009840700f01070058496142a20080543d100a00800180300417500c01403000e981c48481e03c2d0740204840405640354aa1410102e204e1003a000c01629562001c903405007042401c0d08408802c84940e0350038401e42040c98100320070a0842408520a50f00014001c0300758070020000e17045a0b405508001480c5658501e0740b07902440b02004040014000410088002218820420040c02a01c000c110f00f02200582400d100f100c6c0c0101000e02c0001300018040010036054040300c144c2c4280d05e03586550386458030421075004800c902c10075014036000605407180d0400250300ca9a00200f505608008085c5054010030002d001501155228001e41081200034040c4a0901c2d1041c1c000f19642c0b02c4080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 160901366 1250 160900116 160900133
    0x41b0e090408071407050a060c05250501081503010f09150c0503010501050d0603080c060f0c120402040506060c0106080c01021e0303041e1e021e1e030109140307 71
    0x5500c0c40340d44a002400041084142503a485035030001c0344030280b114075254189800015400164000c50511002c603100341d018648044035441041150204482d42090102c9281d11480516004288410030001c3e584912400764006480c03040c1940e0a00707110780440c0c2590b4546021200f10380e1141c1c0c004040007400e440404a140c0707000010840c0500c1080d00520031722040c41464100007001c108001841c02e0717130380b1142c01141d00640c807d6a0b051524045501c2c0e5004441c1107030300c1c0514000183c0c884070250101c814070f241074100d041160791154200001058054009500000140300918105c0b200344900310240414400801140b440c4100091503c1c03a41080d84800101981c1c80760340c0c844001082e2500b1540c42442100c0b034604007801802c5c640c040d4480904010380901c0304944070070040f000030345c880d402070f1000304c000c20348081112021440e08142c88e40044441c05185090011456410004000200041400c0700c0742d4440d0780c40a0500c80903901d0b40c0d00700040b1102002a6035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 160902616 1250 160901366 160901387
    0xf0f02090906040209060103150b0c01060f060203120105041e0507120b0616020d02060705030313031805030d08090c0a060e030c1507080c0309100c0510050c1e09041b 73
    0x1d000780b2091070507501180c2c00c20780280905061685034084c902520301c200c0c40308030140c500303617903007030f0722100010082e07406044a0b2207001c4075400c507810040b0783c8901c080211102c0c0c00d404032642807607134a04414080204000c02d088032913004a00e40f1712500d21102c0c06003a000310304c1a41d1741081d6403003401d00c0302c0c100e6402d6400548228400c0012687e000880091030f4440e64048418902c2d102180c00410040d11030b41c10010b103140400820403103601a050030f6080d1290007581e420302481c054802c908900d0034103001d407562503840342114640c610321071320b0119400800d24065982e10401400462090b84143c2c103c0000b0542d940040307241c03801c04004040843c10304486252094116003c01801445240d402400c402c50000b000002d0440400443d00d041c00c005e024102241180d000003040d08400a82c1114a80030b5058112860401402040d01842c0c5000b039507403034290a9149a120102089940208440b0500c00b07501da983c0c49201c3c50191240c081060540c3c015850b50082070f0000e036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 160903866 1250 160902616 160902631
    0x60705010e0d03020408071838090c040e04020109090606170606180607080c0d11010516020718090c03060203090d081b030a0902030a051015050f06070f0f0f0209 71
    0x520042025400000320b100c00c5860078840000d030710310000000002743c075501d11070403028180380300341d641003120854448904180012000c11140c07414403c01025200a41d0044a21002400244848010842c1c440e412a205040005d01e0325580c240d0041a110780380c0c440f102042d0480580021840c003402c010b40e005c0c1045138030034a082d030200c008482100c5410210f0b4021040403d211040140c1e06080700c0751080e018048410802844600900c403501040c210300065007010b01003001ca043c400c2244145c20b00c250003030292242450941003e04456a20241180340c4a51064020428018880000d50702800d009a560f02d080340003180f83c02040d032400003c102040042004c200d4142e4a84c0c03100c603241c40c0020340d0f203441d0301301241c020f000ea001d0040c1d80f50081e0046c00040000020340b9058009480805110280d10084480c0c1340b070107a8841c003504001a007841603000d10b00f0400a1195a21030b0f01c2e000810308442d20f6660000c00b0191f002c0f500c40385c40d5101501507180c01c21651382d10548 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 160905116 1250 160903866 160903871
    0xb0105030c0f030a110109032f010e030d0819020c0f1203010305060606070f150515030c061603030612060b09340519020a06051305070e0901020702060705010e0d03 72
    0x1070b40801d540c1c440d0801c0c0500042c8489000381071a030301c40c03800c40380115041849161030001c20b0789070040c0c1c04400041034030041c0311150340041c1e5500840c9000041040203003c0d04003510f220381c055564100c002c0444444084d900001d60060b0018800341140202120080100041003503009150443c0740841030220740b07041c07004100240001610a170b01c102b081e61920744413201341ca8200480e41c801000148002125402c100840030703d50300c000d2041b4840c1d442c8114407a20241819200c56801031842d81040c8200082c180003600034803280d0f042c1d032092800081845c1e469070042200000700b48120f40030383d01c900c05c1104900d011750f0394076002010188203c14013941c040e03120b40d800054845002005041c80c11a804103030058040e202800166001c01c0c0b50300710508402521200300c04000c0302d0f494903200c08500020062041d914032198030100404429060041007043c1030402488803030b007507408214000051320b0f004041c0c59201d108000101c0c40440324501942030462060b100400c052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 160906366 1250 160905116 160905139
    0xc0c010204060e0a2913090e0d0305010509010815040f05150103060c0203040f0909030201061a12090f030a0c0f052b0e030c011d090411120f0604110d020d0b0105030c 73
    0x8008051861121101070f085941b02441d41000c0401d0603182d03c0803020a10340300445015103c08660220100c90301c0c0c0d005c01241c0e89803400c01010140a0080481c0e5500c04030703414628840c00d07000c80b90003c1c003a03801c0e15182c1d0308503aa2503141c80b9200c841c2420039888400100104941c074000d07403d24601c130380040c504090034080e0b450f1100000b4462110b5403511203130594140350003940001c2c060b060400f445070348066000045040c41c1d1000408094803028080040d002102c00b06090042e803040501451401c500010704a034000388907042944c3c2c035045411041e0009408120901c54004d00c42c00d0000148020020000040c50010741c850502168402e007244a54010402440000c03003420302508075914602401076003100315015582200c481d034244018080d543d688080e400c7c100f194040c2800e00b01c401d07840e4541070a2001400b81d54460808180000c2c4000c0c892480401d002e0080c800b002c0d2544c000680341d9000000c282c505084c89001401242004d0241d2414004183d42e08a1b024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 160907616 1250 160906366 160906409
    0x1006021203070f1b06050a06050f040603080702010e061908060901050f010c03140405060f0910050708070f15091101081308040e06030c100206060a0f030206030a050c0c010204060e0a 80
    0x1440c8107900d0f841040a146601d44801e45058030b61241242c000c0c42c200058646413043c4001414217008691094032407407011702580c90a0b02480f03064036440141c840c1070204580c010740360000c80c8a00303150300100c18802581078103c2d82100c42c64940c0320307503110789050800f802401100c68068003c1401030b12849524166641c1050076030783e0041d850324000381e0910880c2008a0617010b9a040305030300c02c40008000303211412400181c41d68030000c94101c00c450b640703000203403010311904c0310051021009004140200f08480c400082d003500411305c0500000034000d210045581d6000110340c0c0d4050000300340002e5a019041d1648110305a01d01c5045032015161707801c07a4003a9119078264450703140d0019001d51800c0c05210044540580040f13510000ca000294441c60121207550003070000d460b001a00c06d1410b15070320b04407600540000d1842e15411030035409458001c10b986052041003000a0310200240700800080c1403035030700d0420744c400c0001007041c2e84a0b00e9000c4100d4014050105019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 160908866 1250 160907616 160907627
    0xb060a050616030905180a23071803080d050a0b030102030912030402030c030d0804060b010c0c29160b1e010e04050a05120405010206061f2105100602120307 69
    0x8500016010400d044840d01d804c42e00d10007160082904044203130074100c0100c11a45089001c3d49007070a090141c840502890064040141b00d09202c0c45601c0e4089600e540c0a011209400e1159a10000764a6143d813a10b01031a44440031a42c411a030351403c0105490091044244001007100203500d10300702450300c560f0303900b078a40141c000003000101140c2103640400c400c241c1c10802500355602100404d601501646040f0f50594420741407404042a66201c0c1060b034101513072103a90308444a040c4002c034450303140219500d59115000d4654546140c980001501c0030384040300c503600b1602c4562416145240700641103c001400300c05c80c10000040b1404030b0b50540701d400c4144681c035911802c046240903106600504180900305000c0c00c034240702401041524400c2c0c080315660740b01c1205100051000c000b05044042500c02071812207885200031002ca445180c6500c8441c0d120111540700700c40059a5983e89080f129000304034a40c0c06014650f80035503039500807030035840c00c040043c08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 160910116 1250 160908866 160908877
    0xb0a0e0a05012a0c090c0f0c02100302030411030601031b080a1e0503121914190b04060315020703020c060310120206190806090c0c0c0f0411030403020106030b060a0506 74
    0x1251050340f003101c0265440744400c0c10000e810a58032015180c2d034029042c010b0480424100c00180c030428000d40180c06691710341d032030503409800107260301c10f111400c5000b03400280044410b0402c0c10665040d5650801030303240618040c00e2003010141c901e03003c10781b00d18007d5001c03080c0380e0840380d004c0700480d0112100302040383c9090140280e01c80300b03103841415032041c8122800c035004268140109101c031000007580364400c0003002c100014952281c021082000c6404003046440c0d40e080c00a108105c1e00001d56015020700b011400c0c90316075540c1145000000011000d250340840c0c07580c103050b4104010000860142c4409155003000341c0a81e12040b070f1350040001c5160340c0f400c40c0045448000031070b242d030b49000f2a0800440d02c417010003007440c0c900351601c0744101d210394081000e002044044615504424004040070302c503003009d20010081e001841070740540c0d074400c000e40540c101b00003148507030322036400010b6441c11841c288100d9940905200c0c0603094981060115440341000c589 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 160911366 1250 160910116 160910147
    0xd020a170405030a08031b03093a02030c12040b07080a051204060b1f0e0906060408060915100302010903030c0c0f090c1101050f01260105010b0a0e0a0501 68
    0x4101000800c0340300400e21855121a03054484c003003031541806000b902450150054016800c550100740380c590b030450000369a5818a60480301102e03002001d4140f681454031041045801401010f08501010001003881000035800015040414940c20320400c00d4590908080605040c24000c0b0b80321f450140c00301c0100b01c0072001840c105541d00907002e8030310034140c0035403c140710700e042d141000c050105e04040750b0103480030825105114002c00380c00441c5038101d43d01c448281084004010000d5006846d241d00100108030114507a0000c0c4005480f81c810900100103100c030303000ca41c081c44d0034014400d04084213010000d10041c0c1c2c0c0940310804980e00343c17922141c0701030baa040c00750554869500a41088080140008a41c0c8613600510000750703086c1c44107852800705610342030903540d0031a80440035140c548018010b011100d0909000d14000c03540402c11600540445400c450082c3c00c070300790025010540059145d401880c0329820181580d582d240390f4504000645103281200303045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 160912616 1250 160911366 160911383
    0x30703030623010f0201060f0603091b06080a09030c02061305100809030d021c060f180504051504140f070527010506030a090b1302010e10080708040c0302031b0307080d020a 76
    0x4d50210b2003501b001b00540240e00e505040340780c2e86c51001e0000c00310200100c1c1c5088030080346000080c0300305078510031200300340c803022030550303446d0700041c01048071007000c1342844120304203040583c41e4200680100000b200420102c9818141000101c0071300b48807403010410b00900f0842d00100c08002c4c0c80746e81500000c0907803a40038014141c010305400b01c2e0101c0c5000e213440e03000980204240380da041120501001e9640f0000c003078041e8000d0340d80c11a4040d245a00c00c00201e980c4440395a06640d2007802180c8012100d0403030260103082621800e0300d40380d0382c1e005507014042d914000c3c02c0c3c0c03924103c455111102c640c5a8043c1001005014800d580c4078007400b000154845c001c40d0820003d5560155010030705250070f00ca0f40406450718841640000da40c2c04180340642403246030240300301d0071919140314a60355044202c0f200c210040003101c603802e51220000051b203042001800740d0f0b483c0351510a11100130401c0c10b00c0c24649501001c4290320242d45a0812500411800c658940000c1d41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 160913866 1250 160912616 160912637
    0x8031012050c010807300b010318020f0402040308040b04030218071205070216030b0114010912110609040246110114190c021203010512100203070203070303062301 72
    0x1600d01b032510200c003540421084404881140250904152003642c0d40c100700300c0b1469140044040350b904c60144d480803510403401201618002c028070b070000c2001040940b40c40c0d2203035980c401039086070380000402c050100e400c0c8118a8030310030402d441e001c00406c5004910b004a8024241042a41b4107500f6650380c2c80815a6140b00b80181d006090741900010740c2e042d0380749455100303141c003440b52041140e60b09000455540c4140515012500c12807440c015514081e1241c05200d5058982c155000a0800280b41e82e0340b9a400940100004800c00c0b8080128800c80711942540400c0501340102c140024000061004407085582c0803103171601c020050380c00c8403201c1c01004001c18a038401c40d0810b0401c0156241d82e0002d01c0c5102000c00140003529007008180d0343c2b80c920020103481000203000500c0b0310f00308000e14002141143c807c49440c8070704070b10004102e030b000366014401070304005503610916405015440c0200504252017140303109404142c034000711510121030400091103503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 160915116 1250 160913866 160913881
    0x209010309170d060e01030c06110f0709091101090305071211040501090902010f1701061b0b07020309180609070c020307090509100614100e04140408031012050c0108 73
    0x1100340010340c44501000340c02c42e40030510200d07400030110101020300f03100c0d0109039030031415602e40c1203e6001008641480c10b0800c01d40d81a100c40d42045030601c901010180070f0101040410010301d079803080050741d88264103044450318483e41846041c0b00400300100001400082c642c01251400700780d01c3c940d8070f4030f0320f49101e41c0354068030110b51060901c8004202e10f00c25500035054035200342c84058102c0300120303090310300f003252003641403001c0351403401000298020b10441420241d003204004003141310f0f075194209002c0594184005a04c0443d8002c1141401080840e11120010340e80b1030600c1d00d5400194440320042c021020400b0f40c4107180c0440d00d0800080f070160960020070b0005141081c413a030395505459074480130b6030781420fa0005001c1c0c002401d170026820060001d2461030410503060310211a20401241c005688807031203220741d443c2c550311b9030159109942c415070300d0a140b60306109941032070b007040082402460081000804c00106940005000c0c20101c0455542c8007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 160916366 1250 160915116 160915121
    0x60807020c09090c0a17060402040c090320030d020705091605040314010b180601020c01080603030d1107060e0106050d060b060f220e010609051e040204120b0603030f070602090103 79
    0x426694225420000f481640400820b080c82d000201361420a0310070741c1c84807021008011420301407440e820660104025041031f8200721020881820036551290703496603030708401c5052146034400072001c043c642510785400c0c40112540e80141c40180500f9041000103204604082c0110310701022009425003c00d0040c0c040e02c0046803c80300001014003440c0d8401c1c080c0500d88040c03071085d900e21050381700003003e15811500440040e401003a044607100d0054a0ba2034000c2d01c01070313141c4414004070380c07981540c2c02074010030b8136402e907815101c80042c50b00c00c055071502c41a0140990404005018541b12040425000358108030003140103a40900071844510030718030704180d210030000350000d240c40c0304c00d00030103500451994804216901d001405041c1800e014101c0010600300082000740b0303044009400e01000840401880305120000500300c4e440b5034000109910255441001c0c01101c4450560000d000d9014600d0010340c1e41070f1080c144035480d0020b0401d03034041032030160341e4400d9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 160917616 1250 160916366 160916383
    0xd020c07090e03030906010608130807020f04020d09030e090f1902090d0b1e07090603151d061005030c070201120f1401140307150c0227070f0302031006080702 70
    0x1408010341005210b80c1610395100300c410300081e1080c07034000680c280c03248003920300c83c0400c2d40c0740c10f9240c0d503a680c40c2d0761154000075060380e00144a4101034900d5880784001c0c10706401440c1d0001d400c44261401030030303940d1320a8900d44500500c0f010001460f002d649050362240694a100788002c0e40d12141a00901a11401e290000b035998156420403103240490b034001c5042040d51800629109010000d40204440c0300c0f002440720b05003084114000d4000d0207481d0340c001158a51151a1642e0501869020128030340314004101031062038145404684960301c0d00b494040c3c95494022090360307a038401c1000003410000c0316070541510480980c040d0403c2942c50710140200c88400f584513505c85020300070391100350302121048442d80781c0042e0b220220317901d111551035502010b0500fa03500b050300d81c4050341c200788416400161070826145100074591101c003034814905101c40020030301c444800500f01407510410a100b851492031100070120790321450070b68515911100100e0518138036 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 160918866 1250 160917616 160917629
    0x60109090201021f050a050a0c2c0d060b12150c13080f0604030e03030703020a0204090206070f0614070306120b07050d1a1306030b0406020724021218030d020c07 71
    0x548140c03006084c07464000d54010f400b04102400070b1349454860001302c4000110040110f0150702d140d4074a0a5a2807401440001c0d00c0445141c554590010400040e402e4a0031151160b80e845815828904500390b90a01500348c0300610322200740300200940014040d00045915801181c0f007200070704204542000762482d079040e00d061038100904e040e612135007a40e0071404070703c5889482000d81000800e4440c80f5815a000703010740310701034080c04001c001c001c0050303802c24803c20a00d17000c58281d03048012894411400010b14542e0010300651400001d480c1c0410503040c00c40801003100c201c0f01721030707042d60800d03240c040030340b02d95a098900f441000704509405090010b020400040280d481c5a0888240c036282c0000c0118801c950490351030740802041c4c00307481d07400325022564640c0035220981c07180100751282480e040e200103903810010090610b480c0c0003c1c3d0296038014020b60076030048a6550341d90800510840081c1d01c900600203171b410340c154003280c448e042440030003404008100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 160920116 1250 160918866 160918903
    0x10f050f0105030d0c1712040c0b0a0909050c0403050312150303031b161b09050a020306010f050c0304080304090b121506040b03070f0603062912040809040609050a060608060306010909020102 84
    0x60700c40c0500351f04804590685101c6540200052001540021582043c05c0c65455a0645007044061030013003801800751000740b98140000700000310100000d00040c04001c14040c80c40c0380c180200320305003001400c042e010741c00910034052007050030f4031403c08100342c0305801c68540c022021880c40c444618a000350010342154003000000d80c204080d0010780d03000d030006010f90307600c40074181d042e4402030340e9440c0081e10000010b01c40d2446040501520031030f81040d03a02e0305075a00410341c03660f000340c2c01002d040750b524285400a03150409024441000b4031000d415407d80e6001038000c114802000345010310b440d1109290f40d41d40520091028012801c01172030201d8542000600624180c041c02d480c0c80703002880c0001004d18088108508803802a0880c6440c0c11100c020f01c42d10800307401140d0116003400341010b650707038600808020f00030355000040d82e864201c040100f030350040d134810003d00074003c003403280c19240429246c0c15105801004100c03c115031004078581032060940c1800c10a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 160921366 1250 160920116 160920127
    0x60219060f021c02040503010f06031703060324011d0403021f090203070e041101020a050a0f06020f0d0903020d0c03050906070f0206030c04030c06051207031508010905010f050f0105030d0c17 84
    0x500c0366018000341c2c6d00590007045000801a2135504030740481c04040d1149130f81240700c00001112500a6074000310103015910703401c0038496081072400b05000c40c4860201c07402d005000300554600c0d0300d0700c101c03009242c00c80103046c2070710043d44501b0131400c5421001e5946042218400d4150006003030590302808860b0303020750361019404400d400b40c8044034043c92511004489620008031500b020341c12002410107001d15a0310401388031038030481111f0f425020301c407800c0c03096800000781041e40365507400400d40e00e400c1d1400904210401e910790080c07001285000011942c04006d541030640d0603924030303607580c0d02030411200444c01070000070741c051400010803016111240150045910800017814820748450054441d4000d82c480102c0400100b000078400d0f9220750001640140020340070100103807200540d03800c0d40c2801c0020799140e0b4640e051000e1000091003000d50102d40b80d02818620350402c80040d44a1a41c00c14460400c41310070f0308001404600d032617403903001f10403070281550f91 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 160922616 1250 160921366 160921417
    0xc0f3411090907050d0602071103070510120b090f06011403070e0d1403160b010b070308241207060810080a0b041109010e060f0f03100e07030b07050c0601060219060f02 74
    0x8d6012660444a04629460000c018200001c80400703680740101250316038510705404a682c0071401c00c0900030581c5070044070401340c9440c001580650461902404945419400507029a41b085c1c83c81c3c5400104208200c190303580710302c5508000100f16105e550500c0181007104000ca889107541406000004000030010410f5403500803061040c10080c07010381e65114400390380d00807020003902142c05400054000c2220441c407500c0c01c00b0000e81d80e1029075002002c034441e00002d00c000380895100321401c0c06066003168003242e210101444e2024400e04100c0529220b40110310001c0c810740300b44020030f00300309602e0b42d6140394400140c42a0059a51100e820201c00800c0d1003040c0508180481100e10341030545080100103009402800d903415072000c404000c11941e680021240602a0003000144452440d14058425952255150307450340281303a00305181a8028070565001d0110ba080e0182d00003102510030f50080000a0036038440719030140a445a1204084101f41c02417844014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 160923866 1250 160922616 160922621
    0x1051e150f1b07120204020c01020c070603020c101b140d020a05070c0509040f080c0c0306180715020a0b070915030e10090c0302090c0f3411090907050d06 68
    0x8800000034210002d00c00b981031588601c2c407409855800100400803c01605140d00103010030350703c90700014a003c28829685082503419000700d00041d400049020700d280003000030b4002e10901d070200b00300c0540d512400c0e0070224440e0150105100a000041403c0645c02c0103580c0c542e0079035207003950b1b141c1412900504075400b800d0201c404c18210310001c141c82c00c00b2895684100d038018842d5416059079141d5045a130440c01000d00540314010712041c00f41c409114890250001c503620001e08042482100d0800700e1036003040e000b801d038100c43e03548943d90000381c1148603500205103c14a885072a0100c2d07200e111340d040361941072202c07910b483e042a4941c0c8410031060280c030070349001b0081407401f24141c41c4880800350225005850600142c0f40982445411074101080a4902842c08c410403070701e60455150b1410b4000703408a080c002400110351585603103000760900d16510b05c41c0d03a0309500c00e2101d040c8240281c0c08940069124402005040702038100184603041c000d000c0e00e0810301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 160925116 1250 160923866 160923877
    0x4030b1e07030c0e0112020904021204050105060405040f0602090102160b0a02011a180a060e04050d0f021207110a0b181c0816030c17040e070801051e150f 68
    0xc5140c180020310081c0c443d104241000c6015619807120150f443c00454119815501c50502c8a81c00c002100071030f03942d803006241094048400216510349400c0031802c450340204100c2c09103041100700800a108240c181000d264030000068030340503005c0040380b074a103042607289032410140001180c202d4200018101d806003903030007480039001c44070100110f18264996560040b02d140c0503619125071000d41150300600702480002c0d4a5070b80c1c00441c507400c0c0140c50580d03103600102c0b6145d101651000910b003440350140020031914a940440e0f86e4a440f130710602810301941d041911207981c0d02d81d1014001040701c06041a201c00c20307400e40711408136040110600c6071451a070181581006240303840c40e415000340c8120f04000310300c2ca4084102c038110348101c080102c51455100040d0141c400200480800280192100e081000c08a01e011016180d44140400341004000965484098921641b06102200252400350002c504104525440c416070800702203000030800030050b01901 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 160926366 1250 160925116 160925161
    0x8031509070e03210c0105040f0203070e010f0302040b060c010e030a091a04031205040b040303051206010503040b04031d0406090507180b030f15060d0504020f0a0605180102010204030b 81
    0x4105841e0030105070b5401000e00001ca4164015207101d100c00c441040e03444804460386020301c0c0c0f0301030120808908503081100c04440b01c0c103580e404801942001c2220300003070700045140201c03a50501d4644080c200007440000c1c4070706d40701c4100450f5a01c0340020343d041145094020f01649141071480b40e1a90042500c0100081e1a00f40000304d2850408103180c6900944d850070b0300e4a070131601c4691508a108502605100b0200303c000340c041601c40040c00118000c0d503980c1d4030f400f000c41404810810141c00c0604100040c814000403903040c41c0c2c42038001c0d601d03080001105100051041c0c0c0742c00480103042e40a4903083c0d000482100540019225807041d540c0ca29603108280044ca50301016401046610f05051000401c1140e04a40035500440700e4040036102c02032600008106900c40102402d4480e1104103020850502c0c0264206c150700c229440c0c64010700300f5100a04038007581c01c05030103044124020b01182e0f4000e40c104c1d4051074000c240720070705240015500720203841010864 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 160927616 1250 160926366 160926379
    0x50a0b0a0c05040506070b070212040b04030303050a020304150b150f04031e0309060c0c0302060c0d080901060b070303050618010b120a1407121401080a0c0816050d050a080315 77
    0x80035068800c104860a81e10010017584c10400076032546201120300422010940c0704601c0240ea1003004603020b40020543d040486564504526000b8259034000c0c024a0311340340140107000004000d481c10270b50500e0040800290041d0100c00a4080240c0b910000c3d01070100090302840c004014000b402a00d01440c018160200c1c0071400d002d4601179148081e0000f65104400e102c400e11440745240c10034001c50b50344c60f1040c2c0300c1e0006030341a84214031700c4020740d02800070907040d5908940c030143e02019840080180c1d900d043c04200e19446811002030400d9074580000c0d916659116084540c07201404103c901c540c0c46080e26502580310000e0b181c0746040203070009589011502520058070510300802a46441700ca205803004c1c0701c1c46071060125611400304003007040020201600074070b40321005001d04105401c003642d0991071500b02441c0d5803c44e04035501900c40441d03048040340e405903200c603400100c2c1e05110f4200101a84010121200041840240f95180765042080d42044896 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 160928866 1250 160927616 160927631
    0x60303030506030705060910020a150504051506130f06031205032a07080307031e0b010f110601050d021809030703030605030d09051009090615030c1722050a0b0a 71
    0x20144d80d4030030b030311850f540f082c82044400070ba400c0c140d50807881c9248500446140c080540e80b010321000c20220384468980c1d0354001c000034060200913220000080b9840842c0e035040247c04140d040c0c1d0b004414686031034440401c0d000010306644440001d603046080380003003409400d8000d0041d803094520800d4117405e0009405078405200300e039040d42c107120542c245491815501c420a58100516000506586007405900803c80c0ba002c900c03182d58100000540741d010400150644410a20740c50400c07a000c0586250842c1c00078065043d01c008942d01d0701c4640142c030000301c65809a80180c81c00302c54110901c0300c03100303002010b00b010502c640c8040c89503944070020305a03542c0c1501200d0f00054005a4200b1550800c3d5605c2e2040d03810501e492080b441d2140c2078042520034984c810111105640706080f000340d49841440100c030040e1030980051007180c1300900d41c840020b042540c10300504217600d040c52107101c010008042d800004e036010018541000710702d051049580403086410840d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 160930116 1250 160928866 160928869
    0x8161e05012007110d0204020313032304030204050c04080d08090c0607020319110301111b01060303080c03101502010203060a06020d050a0503060604031a0411040c050f0309150901060303030506 85
    0x202c441c04074400b00d4007414601103488040b84001422003103600101d0850046001da210740c00114815035050b0b00c040c405003001e00d402400c071030102d100d20b12107101c03080501248038030b5a4100c2e811603404807070200d9186c803501906d940394421039018128501c42c0000d04101c6135040a042e9205860a0051b00e165110394418400c052003448802985600520050030b84090b0b00d100214405001c2c030101030700c081c0c941c004242159103070302203001d14180c04580402214035500c9140042040f00c002402494656940500001400f60180c0c4003007901000042c80d003c100c40b0080014021458254110705441501a000390700a9400a016503042040821103600010b04601c09e40c00940c0c915280900b00202203403560000390005501c140c04110000c0032941507650fa075030041d088801c0b45810709162034280f41214817107549501640c10068810100c0e50407606884200701c5840d042e0750340e5a1251440fa0410424449640d90b81c20000c090000c00c000c158000c0007a24840c0e20204019140c400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 160931366 1250 160930116 160930151
    0x8040e1006091d0a0e12130f1706071218061407020f0607110a08040b040608090106060f0806040e0604080307090f0506040918080409021306050a0c08161e0501 70
    0x100b1004002e9001070100d00010241d42c80094111140c00a03944006180d071802d032407c1d03000280b52440a604e422050005c0040c4494440041c403007500401e2042c2c5180900c9510f40d04028440e82c03d1000000b0140014881a0421651118454000505c040d0030b8a0700c10010400c2030b1403042201058000610304a000090740c40602000c80010441d940e9112000c40d411068a40c1c4452507024080840b40021030640241003d000a481e0f1030351102d0030640f0041920308020842c16060781024010800e00703801050808082c1030303520300f128850703070b40c4c01c0410050300c5800400c0841d8407480341000b051002e5800030b10300610300c0da950503060a50302d50038501203a081780681c9900c640c0030030040004202070340c00440a02c0707042d0168054400d0549403070010b9000b0350301c04c0f110360f5000203003a0040900c03c041b4902501d05410001c0c10240c075000010542c503d01c2c1c0c00249801400103140f00b06418014040214a0740b016041d040200d01c1800802c84442d0b00b1000c855560902084a0301380c00c104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 160932616 1250 160931366 160931399
    0x803041707150e0a0803090304090c170f180307050c0f0f03060f04020d1a04050727050a02040506040602031209010902010206280207061b05030705070f08040e100609 73
    0x1c4410740d0055003216640c0c0c001c0c100d100d040f085500c581045070f0000f540110103140300d2485440656155881c110032402601c061981c0d590400808800154149400c80c09040e0003801c19040c1c0d002b15070b40d1000c0c401e511995011561a10320000c01c0540400c0300000310800381d0304041e110b0841d050140e00600906001c0c0c8000c0941c10b40240b0001034050411070350859100d0300040604480a00c00e445001da0f0040e0062954124040e1800304018403008008100081c0f070900d01c4113111801c1f200c8083c40d2081400c0c5492803050311200421104500350b0143d030042e120090609650355980c1031b0196a99008484090301c1440f08000541da05106100b58000d554068000d0001550355815005420586142c00c2c40c02c02c0c81c41700c03400c2482455202801d000c40c8520b000143d00d40b55102c60b2040709651115901c10130000f001006030540e44402551a4180c0c00341d10300700d590b0404d00d4008490b02581c1c0219000b0704082c001c102e2481100505841169400d4640206241d117485d00c2c2585603050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 160933866 1250 160932616 160932623
    0xe040605032808030915061e1009090c0c031715090405101505041b140f07080f0301170d0c2d0c08010f02071707050a0c030803041707 59
    0x2a502c0040e10200d110062080000301c480c00e9480c0904a5640c880c10780c00945483e001a80045054035000b40c0c40d4803090303040710f01110295404c9002c0100d4031002d00c0d141d18110f008140107182c0c0c5000b070b07005503c04005003041c40420b009908480d14020300c3c100680d0300070360001d6125401c400c0c00d00c0903035004600882c00108504610055602445a0590301130012245031240c00c08070380002c2d25901c648400c1100c00f031102001c0529010030041540c0303010a0303401c0202c5012000071101e175044811442448105a4072545850662540d10028015940054030034180051603035039040c840001941680c070380003078007440740fa044062255030309080750001001c518850448400f0410740c480d070b02c0b64041140031280d00707660907100c02d0290a00714a4112a00000d000c024004640c1c203019003a401000020218207200c0701c1c1e110001d8102d040c40f8109040762001481c182408810300083c0f00302c9402c0006000040d83d80d00c0d1051311540f040f60295042d03a00152a0b50000040000300c0f29090b40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 160935116 1250 160933866 160933873
    0x80910021303060b0109030803010f030210050a210908040803030105030d09030b0c1803150402090105011b14031306020a050c06070b060f030304080a032f0601060807050706090807030e04060503 85
    0x840e83c82d08010905011100e0501003810710001c00030b00031000840c00b0303100f0560688400f9103580305104509035122082c4050280034010403210aa0280c0c1e01003660b11080c03940014081c46140701e5009000c9444003500c9070344005004a07143ca00000154100d403001d4003141c81682c89240c1c112625905801b000303011b66110404200c0c0c1842e2000641007601030000303060107000310782001901d001072104454141c81d954000300002e501d4003c00b00c0340182000e00700701c03010754490078450300000d03000500104904401d6000c003012201c20802d95240400042d08100d4407500d40c82c0181d903450740b1850448091081e244122503030304241080e2810340740d001d61500300544440042000f501108803031643c261100344000509448100301785541503019850b60760b000050103440594001800c01a91440d181d40c0c0c0076040c69405c001032450446505251460007074843c0203040f0307850301c602180a01000e00340705100080c04a41c0c0c000300440d42c403d4840c21620380704001400103445903442a1f0350b1580 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 160936366 1250 160935116 160935119
    0xa032102060c1603170a05150609060706090f0b0103030c060f020906030103080a180f210f030810050307060324080d0c03021002040906180b03060103030c030e030d0809100213 77
    0x10054215071858030311a0071700c0008030000b803603009640107040b00d01c88074150b294014490101201c14002201d007000396100c1d8903141c80b000108005105401d402802c669842044409021907901c803890344a5000364214401c0d656800e000740b401d2200001560028508100c8040074400349c801c8070f42200700900303090300b135078615124031096801150b170b50000d201c883d0b400c0d04004440c00449402802c521900031811500f001c5044000c0340460700741d0308581c2004d00400010926080040300d00d15450301d0045071942d00c00d603a5140520a0b9032000d6054070460b08041441d6405800c0035500d54820045440b540440708908041065203115210341c9400c0030203090760b528410140d6100c0c0c140680100d031214180401d10000700ea0081e44500841ca0350340e1010300019007440ca103042000c030481030034050102e08400003910780304c2c10f200c01024031481c003102004250040400201004000307041c0c603a440c11201c80070709a41c204403040c50701806000e101c0509182c40c0e100340c85507024007080b10042103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 160937616 1250 160936366 160936387
    0x506070e03060105120109050706020f0d02010b06030c161a040618030e13180602040f08070b09060a090b07060b09071803060c0e0d0305040f140f01030504060b0a032102060c 76
    0x70a0321100c030207a00d54072607c1d83e00c0820810016980100140e42c000c01310005a110340608100002c19900116418030b1001e40305070381c1d0002925040300e108407804d544e4a0459405190188004030020000043c40c1c50502640c00e00d18200c6100d0350007910107100e00d02c5a00c401031800744800720002c0100e0222142c0601c84c0c2000b05000340054004280028030034106a036402210301840011100c203900040e0501401c8100e4100348000c004907001449646c1c10300490000d5400381081d014003401c404100c4841451180c2a01d4008000a2443c1c40c2e5500c3c4a0034441c02401c02e4045c041d01035410310b008110329a1040c814032228620800364803040b2401c2d952100050720300d411400c2d04004895000309211b50352009aa81014800e4540c0f503500c0389480040004805c0c240d201034240d80b0740c00c0302603803070380c80303640c0a008250801d10300060240c0e0f6615181004001da0560540c00400001002c810082049825000c45409031035008072900d03420402c03a9903507030445140c03003084803d01207503110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 160938866 1250 160937616 160937629
    0x90618010e011a120c010206010b180a061d060a0f031a060c060405060a0204140108130c080714040203090a140c060310060807020106050603190204030803130506070e03060105 77
    0x48406001098006030204418299400c4010b1016a81d2000c42d8101891a008030080160310504c0f001c0d1140c3d40b104000031351202414032a100c4110000680d010340c0b104964404c82c2d803178074001c180702487c58441000800704003c0c40100201410102580c414910b04402500e03c4207800741e446408004441c1d000701c0140c0f03c80d4034000d4100c0c1201c2c13140354250b980d02c400740c00c0540c9158000c0a5515041c140b05280c02c8010341010352031481000248801091801d0503142d000c400e00345a0059218804400010320355440050941b94a410b0040b40350f0078003084640c01c60f4410029841e0214940e41003100f05d00c0182c40075844c0340d021150300e034000380e03042458419169010040d1601c81c00000701195460f0f20496a070034403100e031840c00307214254104c00240d030040f445200030001c050809011a02c240303c05010148100303030709030b103919013120540c0489018580c44820751b5201c0c100544030441d0896030306821186130045c0c0002502503442508030074440c0c07400800806c403036460001800380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 160940116 1250 160938866 160938901
    0x1104210b060d0f0602071101120c0e09090f070b090f0306060d0204050c070f0f0b070509031e0709020c0c012a060903140705161703040b0310050d0803011d0906 70
    0x943c0041c1c1c0031060041342c65440500501e43c090250303030049003000340004011340c0c0e01008801400707103882410f01ca0280d014500800b00340042d6442603168403400c02c542e06d00000c01b408074406108210000c524102d0110140140390000e41d16508140c0d00b600030140c984c1021100650400403c006440c05440c01d0b8000701e4000c00b5550b4494a010409c1c1c452100c1480c010070700b86d50100c04413408404000d00e8104081c2e00c00c0451500c517052a40340c03000681c0350082418107070b40e85050b00349404045181400040c00602c030102045680f403100c0840c254942d0810360200740440c400c0d40c10302d010900c1c002c00c109070300760078440030440c03115980e65801d00034010410194200701402e120f51000040c007200412070b49000e5001403500c81514024403400a07801d070031071250480710894001403180700200380e03003e0320407180d122134495442000a184a4006600260f4040c60200c040c505001c10100154180d07460042403020711800c038401e072102200c058803000c0700ca07449000040d071092035000800e03d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 160941366 1250 160940116 160940123
    0xf0a06180b0414070501050c0d110f030d060f05030d020d110111040305010e061b0d051308040b04060807090f0e19021c0b0f180403121104210b060d 65
    0x5100c00240d140d2040c2a94120b80840c0c84a1140d282c50005800810151009200901c0e0503860448c86020301925040889040001d100030781c8500494150b0520298007084109422640c59620750040007004e04039a02c200c807481e903001c040214041c20046070540509040360024a5604d415610480c0c0c2d000c0c0d2641014525581e4a0f80c850410b100c0000400c0190f0103000041141088014103506113880034040314440e0318250300f40340e004103411007551a215150f0700005a2035545269400445c0050311005045400008000c0343d8038842202a20a5034202d9440110341e41e50a40d060b01c0e80000e500039003c2c2600c100700100031140340407581c3c80c0c2c00440c2c0440c81b9031035043c00f40244145c2c0c0000700c2e14820f00c815446c150700c0d55125440341c15000641260600118030500002c50441d1088400821243e08108005010326004681001081003481c4080110311604041d101c815001b602a2000840c222010320400d0200c2410700052203400079095201c039126081040b004903100b0a00300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 160942616 1250 160941366 160941401
    0xa150203031803190e03100c140c0a020603070203030f1003050703170c010e0c010e0402030609070305070203190c021809060609070306081c030e1504031809051015020f0a06 76
    0xc2c807040754076601302c12038943c0c0c549401c494214207404250a104801d090b008580c0d2400e01c0040702070380e0041c0e00045d0058005030065a0b00390156002c0e0030b045401002030340203140003040c80090741d40000110b10403401d80c1c4c6041c407140c0381c0c1066950740b88194440a0701940c82108203002160010620812181580303000d540340901c071060490a40f0300c921403000316608458104809560490021050540704850452452400e000094000d8802800010800d5030703844c001011540200304591805a4000f5504141801031400811f00701c190001280210130f90856480c040f60000c189a004121090103001c444d079628080c8420408000d040038101500c940d170000b00c0e0181440170084d241c0f01484c0d040d90104000350301a094036901d8818110350b0784032256100c914601c244290381c2142d03061a016509260000162080780718941090501c1440d0409104a0000d40484d640407a510b0000172510603203500c0091380c4802d038a03111a1001d230044103008000811a0b4030210401c002103610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 160943866 1250 160942616 160942627
    0x50a0902220b04022706090607060204140103270510110903190209011a04090507020109030e01031a19090c08091603030e0105030a090203100b0a150203031803 70
    0x940041c2244841850098000c1c224518640d06006004001e082a1415858144059070240c03502e1081c44003410a0103041d0030742e042c196105c004881030f41c41d0050216032180c40906101c002907025100301e03c00b03600003800180301540a80a603154000d074000380d4000c510755118200240c81c0e46080c0031034090184d190303072005074586440360001c5240002d04464650300500c050500d0201e40b042e4402e51a05a882c0c95401603440b0010340703040d43d52040072400184038440a03014940116001040748500f0b190810500c25415480244058020354a40e0f5542c030340c450042d400c03543c800501800b138082001c296a240e00f08003154114282c450b59001451503503604001302100d040d0500e51300050080400e03c21140380420020004109455100001c0d900e159006041c003080036000318148032000c000140988030075880044a235030094183c80503500121020001000c0c8440968400c0b40715072000710f905068140c403107c02c447d40707070021407940c0c42c0c00c0c0d1440484407030408050160f01c4100103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 160945116 1250 160943866 160943869
    0x190603020303030a0e0c0609100f0e0414090d0305090c010509060c01020c070f0e07090909050f1b0a0b030f040803040c080a0b040b010e07020c01030209030106080105040f0203070b0703020c04050a0902 88
    0x218461072445000142070071090711000d0402c911800306c1c52059000b44120b09482c0d43e03c0b458048180c9031030400749240307540c032070080d0f6030b043c05d6600d076980c01850b040b0421201b41048600500c62668001a2024104040c0d01a003c8401c217440184e1594490402c4942c2540184028145c41c0c0000340302c42d080501412200d403e9921a085d0040c7c03d8005900801000c41c1c00f44040c1c0191841c4070f000411840c010400030f202c6039251140f05126900c0d1500007041c040140040d4120720300400c02e9804122f102c0c07010400340d0081085403030103402038040c0020545940b40949009440112452007a5191900c13000202d400151040d201003078101c4d40040c41074010800500356a00c507100c01e000a00c7e16040101c15100164805405402c0c12010000c485602080407007c545003403e00588031005500440d0042079140c100884540ca420b0502c81070222104200e28a94401c400b120551504c0b006da13500070f4007a100c0c00401507406215000d44a00d4940c024560140003114005005d6100d0340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 160946366 1250 160945116 160945123
    0x4150314010603050606060a080703051504051008060a020403050705090406150303020a17091c06150602010204090b0301020f310e0402030f0f0309040f06050a080304060809060c031906030203 84
    0x11034802a95510700030030410000b4010a5841802140d030981030a01801e000341c103421000b41440c04055079000010028469043e01c1c0c1d001320700241042000303103800041d03045680001d00881c1168810301c40081c00807905402120242ca5208018107a81c9281c5400d00c03200c2c90010304220780d1282c03074148910041c40a41707414001540264024540000c25040c0320010084001c00c1c1c0385400420060303265203403100c544000c2c29901c1c480c10550841214280030b401801c4220a80078034001e0036500088aaa05401800554811400801c00c04c10342c4001c0600300d100c0c0d0011628101410700103112019041c504060b140d40c018841c0c010310302520001108008840d40000002007809001c2c8425800c0810180c01e0050740200140f031405c2a1f030300011b559019110700b081c412a102e0100b4843c84c5a20b1304603400031b1501030a07202e049904c440120351603402c01c1c059040010b003490001050104001583c0b4000e001007070340c40c0d1558a45021280c03103001c0c0003001c10041900c50400100584040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 160947616 1250 160946366 160946393
    0x7091a030307030f0e0d1e1a091b0303031501120b0d29100b0a0c0204050f0403020d090b0409090602071b0f080a0510020a0c050d050307120c0e041503 66
    0x99403808000004c158001e808468581080340c0141e014604503000a89406d20034400300540e080c1c0c004401c1014604220078008050044440b0f0b4018000c0c0103590304002100c448a041c0400d03c081004201c0c4185650390000300c2e01c4070645115402000300300c1d4000c1074408a00b000e4141c0c04a41b4065107000720f1111131900c0b10441e15985000b4500800c40c0b103443c0d65858944440f040300e038040c00c00a038281090300c4540503850241400040c400c81640c015000c1c084102d901a20602c5a454040740030540281c04807000d070054001c1100161426105201440c1a142c0303201c4998242410401100c0090440d0803044929580c20056103022601d001103408108100c940c03c8403171507003445503143c3e21030030b0307070780050300c0b60340021400c400051000c1407100500d0204d0b04010380b14921800c08a40907648120054070500940035064845540800190b200700f01945034207880700c030603107800070031295141082c00c00203803a10013000591810303401c0b02c02c4044901020282c00f54483d100c04641c500720 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 160948866 1250 160947616 160947623
    0x8040e0105010807020c03060606091318120207080a0b19020d0c0e010318021e1302090301140601020303040b040528110301020708070f02130c0e030105100807091a030307 75
    0x20001040300c0d6902c446410740c003051601c041e245181c0401c0c08213079034041c0640943d2068001041c2a025600c55043c003002c003400030b02c0140950170108507900d0580c240e080c000d4886220884088018a0001880000321a40000240b0719000f90b501ca075096240c2c0944070401038985207445070f0b085d48050020342801c031000c007800070b500f00c03a000003c0d203800004c01100f8140350400d551000502508143c030625542c0517102c40151100c0381303010a40c6480070801e038070f51011001c491540d900420343d010b0140d02005500801550101c51618070305404d04860a40c016801000010001000d807903226401c0381c450070803106d400c8481309030800c1e81e0203410440c030041c3d4540c2c01c1041c00d1186500090403841410780085203000d0550f21054100e1084030000b424602503140700f0703004c40d12080740540410380d8901c01000780c0c00720140010105080746440911940c2041e0200e40c0c071303854115070041112205801003018501e044900c9016181c08068500c80c02403060f2143c40d540c400780000c0061911 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 160950116 1250 160948866 160948889
    0x1112030903070b24010201051608090102090303070308011a04050d020d0309031202030903160b09060a0c080d02030a0c0207060203091e18070f02070f0b03090313080c0f06190e0a030804 81
    0x9240310b1441c10201d11303001c0320704581c10f041c188842c0c0034540c05a01081d1009140c802c2480c0d54200045019105050146030944400201c510502d82e00c07600680c1641c000703c13034858400482c214402d00328040c2d0f001d101d51210b40e503034040c401450500381084034544a803c1403e1015940e441d0140000302e1008110301680000400b10801d24060169480107800c00c0c0f0300c03008980c01c1c48024500c1e402810820303406144001022102c86000307084a485295024405036600e181d20071800000c2d4100703480b401e40341360509090041e01400030480034191380b4a0b500560410544108114064545a6500151424003000010350351240102184440e04280440105047c0340c1401040307407030300394015800c40d005120305005d1131014403400030482c3c5035601019144d44030040030b103095118007040180c02d8101c103000003035500c501240f191203a4108a80000340c4080d40014401d00344100504a4141c020b4854005c0c5240d001c2e151004201d28090244800300f0340329a42d08001c2c0c1d0264102c050b40c0e00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 160951366 1250 160950116 160950151
    0x15110a0305041403010536030a030209010905090601080a0f090b0901050601020f0610120606081c02010501050a0f050409031b0302060f100b0d0e1002070b04121112030903070b 77
    0x501d0707180f2903290080203900802807454190494040c031400c0c184040401c5422504980144569055410441d0880c07000e80f5940c81b00101c028000394010240140031a4610200080c6860710143c007a101d02c4042e1a88075203a80c8420182000380a00b005015025a4a61080c2c011501844e00544900031202c00000d050400714000380c5040403046120800d90711a00c1000054080f04428a0481e5a070a80c400e999005500d05400540825002210a0310034070980c520201c0500ca8000603072896600200300781d98032202801074890030750258281d40b07a4141c40800c42400c041d44000000c500a10700791040e00944010400c8405c62804181c0c0143d2100042c4101d60a260152a41100884d0481c000d1a4a404030440c882c0c003d080300000460761720000e034111983c0c14481840500d48030f010071546d8100c1c80c64800d03540c480c00e441c00d644109054400142a500820780301240f5000e52006045a075030f40340c48000706520052040c2c40c140001d0050030002000c60144074055141900d03c1d48402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 160952616 1250 160951366 160951379
    0x7020c090415112a0d0c03031d030304060f020c0706110a02030d170604020403030e100201090b070f08010f05060405090705040504110d0e011b0e010504030503070303060f0801090c15110a030504 85
    0x120041015003844c02422002200106000500145e00100c6040c8050400c02d40c1c2003d40003801d42100410f001c950070403000c0303045980030000b9481036201da81c04010a1040d09040c0c400c90203480350141d400d510bc120700b44002070056201100018031001122500301040e40424282001c0c2140742d03000c94803c0480220040c440106141c1c07010003510210705251035504e0007008900c0d6628107a00601520384000c090a00c01c2d04011a0260012010380c1c583c03d102000419010345920f084d40002c9646002041c0e010541c81c6d0320044850040c106410f003810001004a030600c054810014441c0821001441c0e40b230b45d000d80010403940340900d549402c1e41680040556442c0104802c6a07450400060610014003024001e000901c0c0307403150780d46e03d254006072040d10540e00054540c0c4070100b001c41c10150b25400a205480100ba41d44da051070307a50000c90b0a980d1541b00040034a51203020500201500c01102885061280f90803000f000049840c24141440038005900280d0f0014040c480d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 160953866 1250 160952616 160952647
    0x2190203030414030a120e01090b180d0306051f020f061f050f0915010909020c0709140c03040b06040615020c03060705070c0302060a0507150e0d03020307020c09041511 74
    0x41107a0f000c041c1d80380c04250700e0000c04582c10441c07442c0001d5503801099401190035031080b4800d41c1c0c0306164032350500b081d0076407070315402c1c9401807007440d0710621800d201c04900c68000d00b011210050314000c4d120902c17031100000c0c40850003a010451041c440c005d1114201000010301845078032440c04100da08966180003104070700c2d0000b40c018892240e003032080e0f4581c0d0102c0c540c04501400e00511136100400101c4415034903600840307840e400891006240c0201191400840f0b901280410000c1211402c01e04007520448600d41e1110091000501286135507005581c880300c01000090120307195000d6400300c800f00d90314200140d01101c5020081e0508001c50f079000354050038002d0a0500c1030351946510300050000038040c8001040c02c604050092050310021a0b02030344040d28920700c014501c0040c1040c20302100144a1061308034140781c060310840b40564641e601030004440124140038030740030050700c1181c0742c0405012aa07044a071704c0c0700e11002c0d807201446007035550803140c08510b0b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 160955116 1250 160953866 160953893
    0x10020703021912031b0e010309061503030503010f1502030d0c03111b01060b0c0c010c02060d06080d09050907050315031e0c091008210c06070903060e0d08060f04021902030304 77
    0x45c0002c075808400d503540104c3c0c48800020300340381c01715800f00741d8070300480a8110b07a00b0042000d07810301030120401d50000091410f860300090074001c7c0030380c1c0781c0d5101c010400381007425015030010040d41c0e030b001c0047c0d00800d01040c45030402142c44050b0f101c9003d402d9000b030480020005203030b4880c4061441c00e001e003030010000500e0403030801150102641c0ca4903c80c040032030501180c82c1c884400c40d2184026610080784030380041203419980d00b2066200c00007000d02c0030020b95603000110302440d10158541c060101c0343d80307003411a9101e01c0c0c800051119100c0c2550700d0702c2901c0b26200c0556901c0461a111045400603048414116007800304080024092042054910310184403000000803607a02807104002d01030340c051824011314415121b80c0d40800524003600c0d0400000c582c110300c503142100c1c4140f104020221040d100d41d41c4440740c0007044000100709074041802c51601400c0e00c03880c520014030040c98440c2420340341082981c00300445002d604044100024456038880c3c108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 160956366 1250 160955116 160955141
    0x10b0304031e020303011806150f180e0f0402060d1a0a05090f0412090803040602010614010c020d03081503030d0e0609030f0a08040309090c02070f0f081002070302191203 75
    0x1c0c2640c2003000280d01c0f40814041e08401c15800c087d00c181041c2581c12034401071805038851700c0c038407a00c400c0061181600d088040c2c007185664140561514800a00c80215000310003a02c0c8640c941084103c02680c002c4c2050780e01076014405043c1c1c444240c07044841c00b0310408203010200d102c942c00d01126498590240c0d1281e244e41d400c01001400c2c04411aa1066004c41c180603000b080403026115501a500006224403002c180860340c01e4055218400f0303218518441c00384440c0c1c0c1c0d401110504d5810300c000350018803440350440041c0c002c561440e00850b42d019116035940c0e552000c40c0c550f4002a20a503211500d07060100c0e80318a0a000403a000310001000d54540050288144283d2148000c224100900000082c09052250562038080c00da251014804250301040095480f0741301c0c041c00094080d8440c3c00581e4603e0310350900700b00c0340e15002802d010728a0f4076075500290070541e0158198041c240e0a01c00800803a01c000d0076545c0f20303a140c400c0e0306401002c014101c1d01450a041e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 160957616 1250 160956366 160956407
    0x5100207031502070507240806040615030506041805061e0420190801050603010c0f02070b16020409150c02011a0603061f050a1403062b0803010b030403 67
    0x90000c1030101c07a141030b8890200e000540e43e40d401e441c11502c0c080c0c03180d02c0201e0b107840034003000700b524810740352640c10082c0f240e0307807000c007500c8800411086504a100e4411406d81211498030514000d400c030b0b50380007070010000aa43c0d501d018810030000080c1c141114160898000c00030941d1215550030403d001c1c0e504035950301e14160740c4074101e4481c030030400d4080c0c4810449107281c2c1c1c0c0e83c81c600f070001c203403030b440610301595582c0140d14042d01e01526124401c1d400c0a41c0041040c0c410b1481d6902002180e00814181e031415581000c1780d03100300c50030304850708500309940142c0c41e28041c1c244014428a8009088060051070380121049001d1140441e410024103544850100300000c6605400315502d941c2c0c0e40394907001941c4541218018201c403a0105103180d8100d4201001d0100c500054440581140700340c001c041182c0b0088454660100c5410001e003120100486040b5490000c01d110355002965503d0b400482d0f0030992064401810000410040513440f0203070402112500301117 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 160958866 1250 160957616 160957619
    0x90501120209220b13050f090c2b020d030c030f080402060f09060c01050708010f060203040807090b060715150b031312120905030a0807050a0906050f2205100207 71
    0x249032108100c2100344605036114142005000a600c400c00410000303011905d00b451005054001d4071007124100355070034203900002c00383c110104160b010030000070203507a2900501c10845002c070009094021086001046010068440c40d0080314071300e000b6112203440304038074a802086c880561501404008200040c400180c4924042d600c040000d22031068a5051020100340d581c013a002c542109507007000d062011503908081d9039410f80d00c031001c0c91662142c40b240280d94a11603032040d5079113584038450802000f586a4001904401c00034141442c020305600d6072070281e4464409120b0490b41d0b40d840d4030394410014111001010744001e141c0c00c614101e0b02c0790302000c90109019050032460b2407801441e0b0320540700d090541c0031000d4200010806410400e40d84c0c1c00040100c00883d80a40101e07000c1d5000e0025078158454907074480803002e04000080b501038011100344d1562503000e00c0080da0841c4070f640351aa5241c0529585030354980f0b0001004002d0501018071025500324031070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 160960116 1250 160958866 160958869
    0x1e060c0a020a08090d0b100f05040b09011203020a050d05181206040f02040b030a150b0405040c0b0f07060204060c2d110a050d03020a05010614130504030915090501120209 75
    0xd20740c2c506a00181d416031607114020100e2010722440c9001401040d4480811007540361507840780d01600d41500c20a44615100d20030700c8211800100216413111510004011403012643c0c00390304244a03205035460ba044a0b07584500e411000d02d5001e01290f40801d00300403801c2c041d60350340c0d0040c0c800c40c0c0740f006070100398104130386940c1e000d00702600010201e89004250b480b650018141c5407009403c442c124011070504a00d280c5500401d09000b909203081e030310440c5018050a030045401520450405141c115111116808010a1450f1080c20700401e030126000e0700c00350005150301d40307503100210203134070700311108000007500e845820703203071b0844a2480d8a01d4070754488015400301d00c4098510707140303001480000d030310b07480a544a5400480e0008140d80400c43e02c450f94441d000070f001068603069004a1681d104011640220f40703c00e20341e111400316000700740c0003070007824004200c9444403003e04483d0103800a070349c049030503804100515640441c415402c4d818803030045081590960 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 160961366 1250 160960116 160960123
    0x70501050f01121119180506090405030306011d04050106200d020c040c1806170901062403020d0c020f1b06030a020a02150118140906040305030a0e1e060c0a02 70
    0x1803000d0160011450f00d41140d846400c070344020b417441c020040d02150382c0c03415007009000d07810400341300e118140b0010444038140103200d40c1c0615886400785017907076218001115a81903100b05220029480d84c0015003c1d01c0703511900d0b001e415140d6403074188100d040c040403103000d803800c1c0000055001d0981124010360100d008401800102c4010810740d815984c1200c00c1101503540d41c1c1c0d20990400300058042c2c0045013480c217682039107400e101070317582c003100242200e01d07a20841d100c0300e0180b0301d182c0070310321000040310b51510241001810800070304414012030701c0c0f0341d400300050b80c000c01c46603c642100300620122701d1203044c080051442c0100204190b808041d207017411140e0041041c4070300c1e5000b4000b40b0b60301d04440805810729a55181183c583e0503407040084200d924101020424100c0b0403500b62044404100500180d125564102e0b10ae60008008002d025500c0810018181c001c4c0808c2041c10760317030f55404500a20f0040d0700350501801414040a011040207220354030764010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 160962616 1250 160961366 160961399
    0x41e15051305040c02030904110c120f0409020306180a050609090c01170a020f1801030c0503070f0c1704031a060109030b0c030405010b120a1b1d06030f01020f070501050f01 76
    0x140c1c0d010030302421540080c5d00d103000d204611580503082600100940380448040c0c002c002c00d030700440d18000104440303030003d48183311030240640c40400003031040d54801e07001143c0202001d8503220600240305450144010140c40e21214107844000344040c91400381c2015401c11181009450b00032000700000e44072460821125040e5003c400010b240054968141d8040c5030140304a5592858284c45000380e043c0c40c07040d0140803074030f0002d84030f0205115100ba280f2130422901c540d0803407214040300780c400183c0000c3c01c8504e48107640007820310800f00406440154402e0300c41c055089150704440e480091b004124504001450508001048514200c15040403003048131555a0300ca509001c0d0240061402d0781e41c000c4205000084d15000000700c0309030a500842c0b8140c00041480d4030103400c00c50a1150701c0c1804d40c000f8011402107800519036411031001000c4500036010f4004407420390f000300e04802240e4101244020900000b070055580c0001498001d8401b903043c19100b20002424 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 160963866 1250 160962616 160962619
    0x30306030124140d0c060807110105190510051e0f03010209010f050315190305011b020607030b03030408190b07030207051f230a140603150903041e15051305 69
    0x1406903881140c590140800450303800504100005455030301c05001f2840548015001520b1f40c81c6008440301c1c1131141c00d010700200100034400084d03159411000d40005032803200b03c002d05000000f03140e5a00c202503007140039115030354814201c03500200300b54480c1e0300001038001e03401000101c9a80c7e82c08054034000c29a60b00f09143c4a0710b80e45018000d240003d0b00c595004032402d4203001c1d81402c00001c51003260320a03002440540341c001110b42d41c00c68000784a40150b07001d900440c40080c02500150b0200a0140c220b0303082645d54282e9074580346401804c0c400d58005c0d074480b038061241106c07516a00001e84e003019440c0104640d201c40e034444241c403100300c05141054080d02c400c40f281e00030000c01d40003e4480340000080c015034021003403007031320000645483d250320038415400200302c8034032664006018121000144480c549041c4000701480303103d0004202c08114150341d1a121080c0d0b845481820400a04001c0c62403102c9a5054038a41030290910170360b412461078084403003d8510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 160965116 1250 160963866 160963889
    0x7030b010b25030534110d0501050f1506040e040f0c03121107050a0501080f07090f060306050f01210c090b0d1407080108030a03020a0c080408030306030124 69
    0x900d000c1c40001484841d890050503101e1000d00b01415884000b402e40c0300111446094141c099034503000c05210301d03d000e071000004c09542000481d1410b0014001ca960103414103503440143d40d12075085800c11507030a02c1154140050100400001168101440f0706680c101c0c0f078242000c0fa075500c0070780d00500c010b20854144071088100054800458000c6600110103660307034280013009000c841c0c0c1d45040030564800e03c1e2000bd076512300350b28034804903401a184c03c0456122603012091400f80280309030144280302400040f10741c0a0081d40f4014000d6540c00100d0b01c0c1070070304020000c4a4196010b0402030108ad0b1600322103c1c0c4801c0c1c07844014000c00009100e01c420005864501450744003001d0340b0004a2140802c44481d009070720f240d03810429144042d514440240c850400a0007096480c0e4003d021414078603009038020301084c0041e084c04020302e00d0581d00e1200550081d000300c1590f0b0004028407101d42424001ca051a41480040c0b409001c00301000001c0711400e0322a0a0524a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 160966366 1250 160965116 160965127
    0x3011703040306050c07022b02010302030c120c04080f07050a180e0d0306091d03070308070e06070309080f2b03020909010905070801060f020d0804030219030206010f050307030b010b 80
    0x40040040700c00556019800740002d180c210300f4003407107411004e810b034080d000e80500400154000c0c41000440540e807600d1240e11200c0740c00460080d00021710b40741e02e15000f000481821182051401d1285591f028001d0741c1e9402c084245082001030320010303c20307034080310041c00541d4440c074814007a40c0c4408aa0540c0d100c40c080a40e0140c004860141d60740c2c02130206010039030303526800080c00d4400c2c1c21011b2051038401aa0003d2860070070712001d03100e0b041400b100c00000e2280c0400c0e5003007c40d80ca007088030480c807880010b0103070b44120f4040b8045410100c0c1000500c42c207000d100110703682034004e070a40300c001c1180c0d41c1c1d0b000e22045c41c1c001070f1852a01180c2c548c50295040c0c0303069090103002d4003190360b10791410b40b0003080f080e03c4d12000b04420340000100c06100c1c4020140c02043c075406000000c07048130303003901c00690140c011019406401c0280b01c250b0609203800d482c2078080d90040509500d03144910582e400b40d40c00c8280290000e0006101044082c40003c3c1101c542c0020980c3d141c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 160967616 1250 160966366 160966409
    0x10302010e22020406110303060d0f0212030427090c03121101181e2103020f0309160605040305030f13080f06040210030e0c010c060b0310140f04080301 67
    0xb445202c22160356190030785803018045441e94054420703181680c076841c070000c5c6108460781d41ca00040340c1c8070b0341c030142d10084d4200080c4948581c021031340c0f0251080001c00744080c85181190415003055086142c03009072640c109003801a48810901c12900400182d0003603195009808035078040a0803941041d060706000601c80c2000d0000e6411010007080b20300341240c0600c030000d194580950721031f0080c2402240398803090340b20700c2c11203030301502404c50981240c440800c41d00700b281c009403d2603400c1c0403610303500e40403200031403003a10244050308072400c0d0180725200c400b8035038208404100050006000081000007203414480f00c81c20000e0300c542c40d091261481981c1c0d80c000c01f4060280302c0407482003803400210b1a00880c0b00302e85200900b580800b040b0100c4955070601302c0d1a5208030016072155000d40d804115407070084101103604494600801d1a246070700c10718002c0a0396a02c46242220749140245420004512300c0000d2810607440d210024007040c02540d121211500f05007060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 160968866 1250 160967616 160967629
    0x10b07050c0f06091905090a051003030c020303040b0a0503040605070503010b0d0b0a05030a03020307031706011b1109090705030709110936070e03010605060f07080417010b15070506010302010e 85
    0x410100400b245c03051002c00c1007643c00c14460b40306181c014082840440c42600640c010380748580c3d009140407044510310b03282110181c15100c4140e8050004000c04201010218000e1404020342d4a6140c3c1c0e90400745001c108452004000e24100310b020300060109500c001e0881c2d440841250020440545070400640c00040a42c8085c0d4544240c6481204241d004070161403230500a40380d03011b80c60300e0300011a008101c1100d950b40000c001c02e40c802884000380c2458680320f80600a4013a0034680c580125041d0802074840008940c040751041049140402c034280182c08100070601ca54922182c00a2980c09004980b500c500b87c50903100c0500700341000d1031004540203051241e40480395003440c1c5a00141903403010005034001480310440d060500480048405c0500400d01c0d02480184101994000c440e0880e421801004001540c2083c1140c102c0c080341000000112082102c0030446101d0003031059611304107082c8000e4010a1011803140e044036020309003a0f900710740c0fa1000a81c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 160970116 1250 160968866 160968877
    0x303040506030a0c020f0705060d0e0c03010905100b01030603080d0504030c05030d39031107020a090605040b01110d1409040c03050106020606191202010306120f0209010b07050c0f06 80
    0x4106401000300603c00c071290704000841e00b90390302621203464155a41540301c803c1400b5071030b0003520070084000c0901c219842030040b1100c0c8000c2ea05100e000c000082d082d92000c5400b641c403170f03100b04040070384100c05115440100c0000d0a080000c41e1641e035803004c0601a800c110350600ba0303110009403e0501a404031641c0a6200050f40d5a602250405400408100d00080300c0301c0300070100401060710304911070035003054603c01c0c00741d00c00203444114040c1c100000c12a8541d40c1c203100c1200103850b08080c50000d03103c444000308500f070600d414401166500c402c010b0411000d841190001403002c5132450140c540707841c000c003540c1c13805591500c880c42810600d83d01b0902e04002101a680c0c1503204d503068480303e5003507038040e454100401552102e102124030b400280204d081006a88202c456503543e807041c10082100d564a039075140070080401026075103c010205402e045141c112a00c5024011440655091007000e80340e940e5200f15082c40c842c020700040325803541c82c0d03441030165503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 160971223 1107 160970116 160970119
    0xd0f020702060304060f0b030703151a0a120c051f030e010b030304140a05030303091b03150a052a280813060915020a110f060109020903030405 63
    0x3500034001d20100030071b0700da1313554140442902c042c88854003c50050000086110f035650280040d40c0b695103501d00c0c554642a0300c4200f5a80c0d4140d10f10940d00160034241500d111450054046081900160390141120005021803110075030038000c1444659820b00079144460b0b403807401d9a1039500d010b94160400c2c0003e2082020503146c08072090b200a0805002c5542c5601107411076009a5107414660002d0100448800303e102d610440424103500406544180c0c40001010780070160003160300030f8a600200300e24401200b07140103051143c0164510442400c00084080e82c0101c54185c3c00c6c0805c08072524200440c03040700300b0f0150180d12a020251340d440340d160280c2c1500d0000319409552031a4a03008118008403210583c03102c0c010040e0766441d07009015107001c070a554400e5880d4072140e1104815540400d10a044802150f00540c80c2c2207960002800c502803500510b = true := by decide +kernel

theorem cover : BRFrame.Cov 160791366 160971223 := by
  have h0 := BRFrame.cov_init 160791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 160791366 ≤ n) (h2 : n < 160971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
