-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0677
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:05:19.192976+00:00
-- url     : https://prove2.me/submissions/1884a2ca-dbcd-4277-a6b5-66a12b505dc7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 121582733 ≤ n < 121762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 121583983 1250 121582733 121582771
    0xa020a0305070e0d15020405060d020405010e1005070b060a120b01080d0905030703060507050c03120912031501030504060e030409140c19080a0b1e1008010506040320030102070311010b0a1d 83
    0x501d1300e4200c20704032b1080a81c0010304001e40c0d038000c0401d85040704140c400700620a03640901a141d8040c02802074071400710040029184d0340c0301001c1401401d4481041030a001c10f03403c2c4103024901c00d0003054550304c6091054001036006800000c120f95008006002c0c05045a4909001d444068914418008103000100c0e5694040c00607103400c0108104120003490039a400300c5c078000c884a003143c15010308109110040454041c01030300700310300782004035054681d4a4000018191700d282c00e10325000100e4049501040b5802040803036404006410170707600c85803000c10340d611035940c0c000d00c00d80d0f1440541c00c1c00c1d4020403420764481064140050f141c005074000c0381c0380002d00f52a6001e42101d01100c12207a142c0f560005544101c0c0707103420103166044c44003003011841540006400844d0304910081c5140c1040032082c0c2c24a030280007951590010318010380303080c40c40b01c1514940c0d401c1c50303100e030b03420700b030000702581280d030b0882000a0329181070343e2415446401400c02280030107102028 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 121585233 1250 121583983 121583989
    0x409090501062601060905060603010326040f050108090304080a02190e0c0a02010c0f0801170f010f0203040c081203040206180a0e0a060608010b0d020f120a020a0305070e0d15020405 80
    0x24000c080040f540c4004290402c038840b802c6581070381020704010319000901ca20b41d2904401d4905680d40010305041d00e2494614103149202c100e940c13041018800100420302c1e62a442903001240c5082c0ca44c414140c0b10300e035115441e0f0145000300303d03003580f100f106540075140a29480c9031058407054003c200c00c0d01c80e00703091600c103004c4031004818900000d01d0440f0384d6091080800c01221454006941a40b4581c000c044800621440e181c01d00101c0c050801e000c17051048400d030301508002001884001003000000c0c2d04120360580d40194519000a214640407072003184038000712030b0461035a034403a4200819508098068200c14110043c00ca050340c4074240088046c05d03040c0030000d0549010705100c015030b175903a00a81d04100914004114014100040d9401c21464003409a01ca1451310380d071680a025040c410529041010300744420200550700030702400c0001d0341c050089507102441035503920b028034502d0740c01c943d150030550f01060054084207011903907044003500d0241d0751000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 121586483 1250 121585233 121585259
    0x21111306030809010f0503191112040b01030212060106050f03130203030d2007020a12020111060708010303090911030601030b01050412061410081203100b0409020c120c03040909050106 81
    0x440b4182e000080c0c080040d03030010070340710000195260451a500d4078440840e2035107803210080086d9926100940e88034564482030b11450380107070603c400d5074a0941030500b040802032105034003500c2104441c603414540072038120f050754415200d0380d10f0b0140c94a1144080da0005004000903014218402d0050b42c0500040c01c2066043c080071441640382800000300700226103080108040400c410b90042e100c6503e0319040720811040780581030703198001601c3c0c0c980c8a0b0801d1844c1d0280d5000c00201036000000782d03040e01d000383d980c2030145440c2c03012502240c1c08205014913990050000520641c03080d003041c1c4c021134040c50030900313195459526090007650810110707003a980b500340c034035401003001c05102c3c0c2c0700014001c01c0e401c1d10301c0c0c0881c69403680e0031a165007000c0c02002001810000103000000002d180085007180c0e40e590720030420000390000481281e0038001c41c2c40d02e1400d0001842614140d004c15805907150030301e8071840c01d000b0b0601c00b0b0219180c0d501c80340000703441d0031540c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 121587733 1250 121586483 121586489
    0x60d02090405031909140906060f0301150e0409030905060c1e030c19021c080405060703052a1905070b03090102130b070c050913050604150621111306 66
    0x40195101c005844522102c013011010724820804e900f0300030030942d100060000302220081e201c2041c10744035038011584c0752084c00b0229416500010000464807480070901030b203d501541c4000e40803081030200002d880c41890090001f9428500901c0603103814401010408480000c680c0c0c98404540c00e0400c0040c0c00140d451560030200d0301445290050204083d01004450060010141d96002440490b01c0c4136881d4231b24448042d15004000034030b800c880c090400140b980d5210300032460002c100e40e1042109482d0a00304a00c0c4a421803030300b0441584210000d40909006680c0c900004007641c01c8060555180c03148500004000240704000c40c01031503070310000347c5e940010180a00c0361030760907444444074907400c222640c049240040c44900359079007290410300d99221a079821820700d883d28009001405103c06100030030000151001c46024004401d00003980d444808440154400c00008500c100074120080014044490340016500003400607020740310a0011104907070143d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 121588983 1250 121587733 121587743
    0xc05010501061805010519050c0a050f010b12030304020a0504180b130b010e1315140a0501090b0f330c030309010f0501150e0102190515010504090804030b060d020904 73
    0x141c4600f808080664940080c0038282480c520301115030b051008500022044141000000f040b400d05154081c4241034029400a00b107a81d50811018114005c02d20741290174421100f000c1c0e03602c0306040100540b40300b282c00030f00e5440100c1c500400d001c0640881100c1814a51070701010a0005c1c10302c062050244131485440755641d066441c04080d03060041c1c201e1480b003015031040050404c036140f00c101c2c411394048210301d8076800d800300c0c120240c0403c03100d80000710510350811285d50180d505c12812a02049014413402444006001c861050505402d800c100d9107204d48824614142c0400c021220345c0314041c20201c0f044c0ca04060319001400600803d41001041c400b18080900075074855103030b041c1c000c02c50b03940341c20040541d19602c1c1c410304003801001000c0b400d41d60b00074401400e44804441606008031007a01d016500d55480003015100c003035501001007203605162084a0b03107554012001441d040c00c50300d84136940c1c4170080c50598022500021003006803a41528680601e22070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 121590233 1250 121588983 121588997
    0x3031b05070209150901031b030b0705130509060105090d0c08060f04060608150a09170c01240609120804050312030106030b010c030504090b0a05030d020a031b0209040303020a0c0501050106 83
    0x9104003c808180a00401e096107403101c0b09089a80d200c120090450340d0000002d030074100350100090445000340d001800c108a10420080210713044001060008030305a03e180300c4980740c0042064075241a24000d0004005120101483c14400842c60900e40100c041322001542e841d171561801400b201d03410180c41c0303030a051008210142c0103041c040e290003c01b038503005807040503040440f2001001030011a850720307032100521540a0f805100c2c0450944819524044090124003910000300080a040d01380010542d501038140b01e0340040c1c821a40c0ca043d5401c2c03420004a8516186250580e21000104000902940d081050103407942c2d00d280d607561a980740603409411600441211410b1040b032403988030009030b100c002ca81c01d4682e0707600005070007000c403004549816207a4000b146c0520030300703180c048000d400041c04410203220742d4491400c01500c0007616140c103410803009400c48203d04c04140001c1c044d40161010f090240340210415843c1d8a569007515420b81c080c10101d022 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 121591483 1250 121590233 121590247
    0x203010603061409060403140a11060403080912093601030303090c0603020910050a090308030907080705010c0512070611120a0b0105090603011a0408150109061d040201080403031b05 80
    0x400f040c50750107100342001d4031032885c103a100903060419500701d0611043e00066810b151501418840d01541c100340d080f5a0589403524000e4481038003a102e090603071003007000c0c41c40050519004c440c0c40201c094146240c014400c2c0034143e00e40c504180c4002d06858403041034001030031008040c0d0095019a4011842c182541130440c54840107401c000c0415004000b0510540c540b40e1100100445030302e000ca070341780c2d06168201c03110030483c0c00c02001c2e0340700081400f1000b24005124800d0350258001c3c0e40710961b0319401913070150014080100749800c1000d00c840d010240790007514500d40130b0f240118624680000d445290f51081020714040e1403014140403401001c0c1c421010003000a0030f0841c5400b80322000545513002c1441880c0e14511001210071500c541c0e07600352030007004170b141101d40d17040a501c01090201c0c004d000b0200c21134941800098000307a0311100a0900709034001e0010181c40f1500110344040000b0026014103454541c40c1e101403032030300c0550404040c15520251110b075 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 121592733 1250 121591483 121591511
    0x90f031606110f07030e03160902090909010c080c0a17070f030e0c280506030f07030c08040218070327030216080d11010b0904061a03070b041a07020301060306 70
    0x1c002c4908003200c0310140120340b010520a411544080c2d05800e1500b6910820400a840c10300007007281100054070140c0000c1c7c0320040c0c1c000e0624954100d036007a07501c0d41d03051019402c0320500b512290001d5003040c08a8140c0c40590001d1109410030300c1e00e00b451040300c50710147c2c2400152000310010341c40803500008107900d8071525154410b010b0103490f80000c910b0006084004d03054101c00b00160044600c0c4601481e070702808010500034040c0c6440340b52020316a80290701c1107410742d012a00f004c0829001c648105910740c81103078020960021000da039a6035010621000b40031500b4595510706142e8000d201c00220700719001410628105640c81d85030003810304018503940c1282c40c05840e801d000782100484c2040c1c01034941e240007103203038041d034846034054802142c20b20b41011807030707050000344980c40c0c01080c45120b2011118450f000c044040c140e943d0000c2c8903240940c5420f01042c000400820149800c280c403880c00b8609094407500040c1c21901241d100301c610340c0d6117040e0164868 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 121593983 1250 121592733 121592741
    0x2160e0106110106050a060509130c050c0d140d021b070e0702120301140d030207030605130b060105071a1003060618060f03110f06070501052a04060215090f031606 72
    0x702c0070700244400d41c03808020840c5410b49000e440b050203000700e202c000a03112000000c00100800c8030500400c40c815001808030341c401600b0444600540002311515401084245444910402d4291078080e80c203071040000e401520184270302c0070072800c0c1950040c404001042c0070b024424a0320210f820040300103494440c2c82e0900d4682e04030144010099a500300b01c0c900380d4000150303500d03403841906140407030030038005800040000d4038100038824445142113607609120301c1800560711035221500152070b0f9001d00d45008144e0350f880c041620380c014401c98010340081d921564141d0b070300e03201d44e62041505e00707681040620075041d41402e018040300f4052140244400b880050103182540c413140d003801d8100000381c2c006e01d5282c1d000c0080342c03a503c0c100e0b581d117a00100200510b09151a03000b0703052604400d0221800002c114406c00c0b0b80e0040300315003c642ca10740040071103a601110b003000810008080c1d15540c010710900c11003510040c001410f101c1c246160120922034586018400c403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 121595233 1250 121593983 121594007
    0x306040e011b1e0801031205041a04151b06090c051507020306060108010302030703030525200604140909012a180614070204090203030d02120114060304030f02160e0106 74
    0x40f0804110034400a0b03048000f4606481e003100a1072a20215807030309580703e10803503100500c02c1981200c081214000c44028105442e0000b200d0112516850000c88488180095a00e071000c001401040007841d950b00001109209160140101d591074000461060364103814038205040005d090381186000d02071254042401d08001e025941540c001c20350b44c5880c1c2c000101440700c0041d10400480c4403031020640307001c811441040350941807500741210b10700072180c0c03040c0b207143e0521520b0610b012016038040c0e414500004080038000010409004406854003895541e1160302d0301101c00c0031290031a1604054800e401e00c800641001080c07181503c1c008001ca10300c501c400d201044d400040080d038590a00001920b8008034000a0020182c1c94402545440002540240d449450f0042d124807480460810314170382e41c40e1024420120350f5032146074030210400004000900030f1440511007043e038070465440e07070302c410b1072006030081c40c1d044207600c200700c00d00400000f0381c040c19412103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 121596483 1250 121595233 121595267
    0x9140903040b0909040f050d09030302100b130902060424020d0e01120504032609010c032f0c0304060903120c02030a11030102210406110408120306040e011b 69
    0x2816180402c42a41405600c1c0c8052280ea00b880100b8244404070a10b003c0c81604181620503208000744040c089420038802103001d800b0b070705075403114161103200315044600c001e41012808140280c0140051030ba000d41280d2100050002203095984110b200310440340f10f81041c44100321111001c1d141c03c201070005400c204214000b005540d03405410f0068aa078901d0020426488501e000e9804889031001c00901c5522030768204541c03181260301501616000c4020084aa21010100d064405640c102521040404413600460720b0040301e042001e041403a0702410102405c10310790a55100758000c80002c1c0d2048000c3c0103101d4210100c0426041c1414008074001c800e03404a901d49440310006484048103601d0012151000c2d0100c07094192400e00d0000307458040240d90045007025541941c401d845c180185000526480c1260181c0b980800100340c0c40c402500d0b0560b082d440109001c0d000b0f81c80d10b07188a5801b009008604041000d80404404c2004d204401401512071040c0301032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 121597733 1250 121596483 121596487
    0x5040f02041710060b0a1407060209040507020601241403090a08070501020703030c03091e030e100315080312130c03080403120806060918090106050a0f090606050f09100c0203060109140903 83
    0x100f46c2d0840b40c00f071003030707c0c2c06c44c000c0e03444482d141440c0000740281c94119030440d0400080001055000c40d865059940c0c0518001c00c4528400310510307a00513109040021546008802a8062524025690044244003140c2944203590340c0c098168000340005c80b80380e0f4012540c0c104050b050f0184a80490b03e500e420462458580c50300345418000b58082211295440c02000a140c8900c80000d034406d0301524a40b400950040001c005160b0010307242141c40e81c480e00402d0980d4048120307209242d5401c41c00c6526144c0c060103030003134600e104080b50000f4004c8000400100100c1c00b03400103501500f8000b403420b030000405010484010840d61141c1d07000c0103c1c031141e5482e078070605d0715140c3c45140c1000070f80d035040c40140180001d0f04180c0d07100455000018528404518480075200c0d504001e2007059a40c101c107440758060b0420401e82014180050302d4241003242d00c12a1055091810f0050300d80e55070040f030304110081e0456001951074001100110011900454115090000442c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 121598983 1250 121597733 121597747
    0x20a062714011b0c02120111031608010e04030512090f07030308090606030d080a0c11010f0b010f03050601093c060e0a0506040b0f040306060e04110909060105040f02041710060b 78
    0x100445a10200284100321b503000181070380340e09500c821085415181160342c0c1e414010810000314881502c0100098500000881c803034010007880d0740a550325440780b034113006058040f00c001400042420505215000c1031005072782c400c01070703140114040d40f910307030385424200500d42c1402d03c020700c0b0034001c0e03214919940744a98040141c036889011000e00103a4512041c0044869903d941c2c01010035608003021002210010341c02182c7e281400d80b05ca0643c116250400c2d016038204441803404a918a201040b02050006c4001e07010449040d2101d052044030b481322400144101c15840d5440e5076040c00e129040d0401304911581c0d00888600e0203c5107000000340d041d111742d001d44800b025012450407420f46032801620040e680c4807009020300303501c0700007091030b0340c0048034196400c00f0020321255450400f40c0c7d81e24054460baa0180119a09240c280409003070102820b181c482d500708030028842d2000d402400d500e1911002070b0080100c00c1c0405001c2c0d61a50300301d1542da0303c1c100065 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 121600233 1250 121598983 121598987
    0x1605010e030a0b071101020403020402190e1203030403080402211e0129040209030703290705071103070f0807030203010e12040611030d02040909060509030a020a062714011b 76
    0x1c10350002e80b45c5001801600b100c1074080c00780c012948000e40090000c00c015207466940101400110170b565960740c2440381c01010003204e00101108040305400402c0400c020034822294582e00070f0000e0304104154420840d16800c4490001a42525821640402040703184080b5000a2000280000d00c03004907000501888080e081651002d241e0141160b4081615607405444c030708000102a00d06a9950741401d42d02da60200d40c510382000d08400303907180e04202c80c403502c034080c2003a6504e0b18106074160340c07a4038000b6007a0060710f41c10706c101c6000140c02c640d1202003c01900030340001d0902ea40c5148180350a58a1a400000d2160444458664803901c031205544c00c466481c03500c40000700c45a6412400e602c54006144003550000074041000c1800341c015030362403031003804204615520700500903128024941c400c07006812a81c1e40c03001051054101400d0590780507440010081c0c030814201604035010002c031110400760b00c410103564803e200c1c0030302d0300d1000901381c1181c031048180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 121601483 1250 121600233 121600253
    0x1021507020c2403010806010e010506040b030105040216021003020d050c07120810081c020f01110d0902060d09030c1509020306010509040615140a06020106050612040807051605010e030a 82
    0x24600542e5501c103521043d0682c200041c410303128840500b0b03902d58562001c42d403102002d00482d0050a401d0000040c01d041c00b40032038089800c0440e0207400c0d0303424641008080d5001c290100c0c544601c680101000d41d07a1850320103a51011074400581e220300340d0401c1d406031103004015000f884018030610340494241015402904554070301212603aa610302180d0381c42c03140d50060a80c9106643c501201c2c038540d507400c1d0940b13421a4080b180162282641c00d07080c0c1c5c02036011150125401e000166940c00e042d003140400d14801807400d400d0003203e24208d030440d603c00d07a054001800c07812080c4180840036002d02000c2000e071409000c4c401c16900030a6603070070180304643c06800100000b60034026164000480d03068101c9030941100ea072141d10014082d2400c4a00d48150005d90000a0541c0144030300c00444802601d10ba0070100140501400d1450007881038030071210800a04c8001401408a810000342160003695024104070006100112041010f0701a5002d0b884a2021480d0030b00c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 121602733 1250 121601483 121601503
    0xc0b030c0d0c23030901060605130e0603150106020601050906090423031c02180904031d04021908060a060306180e0c090c1c02040803031f05060705030304140111040312031d010b0102150702 83
    0x80088403911003001007460b01c4480011114403b40180001c5a540d80c00300711103048801c100e88080e016140d2008010800d1402d9400602c07400c028401c50012000502413070714080da41c10b0a0700d05254242d400511030030b8001c411130020b0342e4001070017001307401a41c000042c41d80c800c0e6261a000d1a065401404410364100e0810410303980300118151903403a60101d800d45172224440f01900c07003013a9805800c001b4140c414a1081c4650315010501500ca4071484040b910100480f010031311704e1012010003401c88840c502e506010365003840756a0b4076440341c200c1c0281048220039940e8040c082c2d0b00824010301c4c050161032240100410405514000152a0001800115011a00900c101c121804011030740001e80204000c201c020501c0400f04c045c6201d9030203100c0e148658101403c04030700703c1d50100301d052040c040034802030002c500a6200d01e07903071040e0f500700054200009000450341131501d150321065a9182c0842e849a0359050205194044a01c044480c103070501c1034021b5204d2280d85 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 121603983 1250 121602733 121602749
    0xf0d060f0302150702040b1804030e010201020c0c01140417030423060a120e01181a0c0316030e01090606241b060b060c0a0c0b030c0d0c2303090106060513 68
    0x11403130b00203541c2c40b40d10507402000e000707000300d01510740c8545090105104460640205650718100f115650041c0201d41c00d041201003d0010280000e00560340c29180c5400301c0c015840900021443c1c441d4011203855a101e01c50040d900c480c175144105140010b8a26841c24809003007410008940364002038645050181c1814000d016078081a80001c00c074001111310381d50300b40312040414840e5000c04e005080c3c003c0d0341c025032801c0c48402c100710342103080c0c5200440c10007c0000506410201030648111101460040340034450390703240c542520ba250b00d043e103c25a6400c07040100d030b60381070410140c403d031401441c0401f07295440e0141c0905505100540c041b2749440c40031041182550020742034240061503030b92150349800c5000d66601410104440c0004442c0780440c620820b201a40e10030344918000368506840042440003402004402e0824002c10070703004a0010b89401d00620440100c1c1ea10729224500710780a03e0940300564801d205000080200c6103c5c0c5002a0546041e00c50a03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 121605233 1250 121603983 121603987
    0x1203080a0b01020a051c11070f03020d050304080a0b0f0708070206150a03050304090b0a0b03091c03140f0f06040b0105070618020a0f14040209031005040305090301020f0d060f030215 80
    0x20703401070342081041e41c07005080d030080c1007400c02500c144007100040d056a550b0750b000e4049098a4042e40c1d20002c0c020642d07541110801040140f4000145181a51090068a0400e50388420180c50582c0d15032048880390900d200300011844403c0102d0750010303192402c6501818480750181d11a00003078100d04451410b0003400340a40c942e5100040119401402c0faa600e50b520b89894008200e140915441210302d50790001c0d40b10b40321802d40c0d0103001004080c001c508480c81c1c0b01c61900a000e07020303e061648503070107a05015502e030903079882030380b0600100c0707420310701106038408280303004082c10710a514218410a240e64800305480b6151f0f0f2240d0005147e03200b4400c2d524120b007240c140254800400c2401080034480f030a030b8882150070310704801640c50741c6d820802c4140d00465251a4059009071006600e03c01140c00c07031034126001e8103182c0e140c801003201003030030380c0d100b4503002c012120001040c404000d2644141c4004010000500c69154219800260100140c01020344813041c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 121606483 1250 121605233 121605251
    0xe0c070f0b0a02040f0b0301050a0902040515070c090903050d050105010807090303230a02030408010f020304150c111b010801080f211606050412080c030c0708070206040f030b011203080a 82
    0x1070743e04a802070301d81c4000e1315a10300c2d500c404100d001d905c24040d06004040c031440c0080c43c82114000d40d401c0ea040140241c29201001042c00f059800041301907401c00400b07a03000030308451600c60a4040c1d806a501c075540c400d0030204101c16550180d215504000e100c03c100004245d0041e100019243d15142007411803e42c002c1111380b10f410a001f81800c0300c80011180006900000140125000d44009000a06410748400124001141e011b480c140c50300b01d02c2545403c4035800000e0300f82c414209003588682c8800010b1a20720a802c24203143d400700354555041e90781080078940180342c0000103200550406c1700700c0e916040c0c0703045140011040d02e030800140300d40b441d064903074200c440d902c605507010300c6080c0203010b03103800e440c1070340d900203212203010a071403140c03080d0f070f12428800c6a45403940d12540c03012240c1d50b10200003920086824043d100050b500c1000410052541c0d481c8010403134154180071004034410303031080031000e401980e04000203821030101a840642c40100080f10a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 121607733 1250 121606483 121606501
    0x40327030203010e070305100c0c081b01060f051503090c01030b12030f0d0b011b030e010c02090c03040501060501021b01030515060c0709050a020f180613060206010e0c070f0b 77
    0x855a00001e5055083c444101c040030800100c020440e0b001d1812079980401002d1007500b00c4096404000001d01d159852002089000004082e12103941655882d410310603c5034a08549007034010351701c0e080d00070104001c9844c0c41c81d03820547c407007036800c040e21358206200c0140d0396080c034a400c44d05260300c80b000780cbc00c5603950754146030002d0600d07400c0d00e54400342c61100701490303800000584181441c06903940d240f944600010400c40c021015600e85507919a1020b50740e00c014286a1410000c040062070010b03211011603600622210101a031a41050300e02682501c0494101c10304550010403100c0d409442440d5101022a0070300300040c068540c44814074a001c090586650022000034014000c00c0d03001a14601321002d07203004204980f0b0741c0c03003050706900c04c01c000e1400c06641413080040c100310094041c05403072030080481d03240c850b080503201560383d100d90000300560000c0004100b074030210411190b00c600342068003850801c065651120800f4060000307002407203404d0004420349 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 121608983 1250 121607733 121607807
    0x91006060504031b0b030106030203090610060f200106030503040807120201080a0f021902030316050405060d05150a03050723090117101b020f071d04030e090a020406170403 76
    0x303100c540e1b0381d40e120b4501502075442510106100d201d000700280003560320209880c00e0310341c1666003500c07540c0700101c11203c0e01c4142c3e20a0742554014051190b407410244070342c0c40118465000346482c1c42c80e14810a0404030391303502c00c004c0107000312407001c0141c1c0d0041c2d0250740440c510b080000d4603010f000c3c19400900440d81c3c2443c3e80340d4090130102301c0c1e940000145104d68000307207140104540031541101c1c43d0084d072281c940c01290610045d0840d02072601700300c4d03001c0140d0080740108004100001c4400216078002e40300358026203024088043e01203a40c1c0148400c960061028240d10b001040030f241c4140314440f0880707440c1c0060210501d0601c07030000d1003210a8001d00c181110080e50b1210a040031482101502c1059511030103800d000c580e55044840340f40d2a400b050490b45060807605900800032400c100840e081c05502d581c1d00660580244090b50700103031500c2c240003015151880b800c4c03042030450000401c000001e80c0c444400000700c0200110f8801f119190b01240a001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 121610233 1250 121608983 121608989
    0xe0705030d110a0203030403030c120c051c0212030403030501030b010b030103020102100908090a0f080c090402030606150c0304141219060b01120e0c040b010f080c0912060f091006060504031b 84
    0x146c040003038004140f69000c12501c0007180168121841c039100740d074003a1038100e140d0800a20503001070014020000c11828407079601c01d00c03401958009002039a4200c40c0742d0040f50203d001c44d5481c0014030910022955581c050031030241074602e154110380021356a002c6005030b4044140e15200440200400182078420300007000d4021100d254840d8082100803c9030700569902d44111003c40c0000d15180c40350a00594021b0080c0c00c0a03100c800610203500c0c280b4250a4002c002084100802e91341080148010541d072517103d200180c030300040064104480d00040c44550219184985540b2214181c0c800346602200018003000c51800594200070241d02402c500340c90700420320008940420384020f4890211010050b0910040041d14502e9482d43c0d0403002501c42400240d079620600c0c010946101d004010346826000891602e10300101180c0758005500c18109004890104220500c54087d41190900c20141002c4000b032181c0190f10015004120020a402000080301c11b0f030805 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 121611483 1250 121610233 121610239
    0x5280c0921060c0302040b0405060d110309060907060504050108160e0307030c090c140f2116021c170402060f2a0c0d150e0f0708010e0705030d110a02 66
    0x8500144403185810030000c034030540b2580d00300000d2040c80c92003403085409681206440b14102401c0006000e110f800c045166001241c0d101150f00c009206207001c1c500c5800e04800801c020b142c0b090bc0b02d410502154022814084140030500c100c1e030f088400b140e8007852200b6840300c14805103004070f0b882d9a648070100d4150242810100034000c4540525042d107910300310500490030141d100304c0341c0040d000200c043c42c0e5401d10261000f10703082c0e8014a51110120140589100d0a091003000e23480103582014028040748003001100360144520135006460fa000303101c40301c0d00d4070000342c01620101c40710041010900c0005046507200c4003034601e0312012019060b1100d80d0b58051070540200c1200340e4a80c00c2c0c0c407000c18400309100003034102d01c208018048100d0385d01e080e6036007254604080e00050000d03884002070b03003408a08000703840e82040d01c0e1004103042c8c0d10305400d1508403842035660800304d82010400740074a0b14001800501c1c0c1a8620b0111500f50030303a00c0301420164000d90082d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 121612733 1250 121611483 121611509
    0x10050a080a0501150501050406080408071a072d030c110a03030606091a180d060c02011b0c021804020a09060603050a0c02010c020c06090a050913050105280c09 70
    0x48042000681080700e500c548001c002a0300c20b600141d20380c0705280702c2c050028004120a00115100f0642c89400c030340300300031441c1003085175500e00f1402d12850b401d0074801c000d40c034108510b641d8031000c0c01400303024641c17a070500d040c0141181220403590080c00300a06031245500d031304491080303030541d60003c22801501d1000840d890010040c1009106101c00203100c0c0c20045a051504802000e030600f0109034070740b900214002c010007440c8426400c99001c240c82031000c0c08280640512582d8045a6000180c451343c0313001d4890807000541c2070401002010030004006889800d4102c41d18500c1790800400c517074039440060385860140e005644154240807001902d550550003141c0204080c46003800002500c0c0e00072800c8401d44071028005078841107116245041070001800b5a01d07020340a0801680c441001c55031001f41034800c1e0710070708203c1c2212018440e081c861a5040710354440380c0a0003142c0c40c2e2100c0c0210044d40b143c070207a1070340c8071114880303a40a907035441c000308541c0081d89 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 121613983 1250 121612733 121612739
    0xc06040c090605060c070603152606011a04050607020409020a12030801060c050c040504060f02071b1520031b0f070f05130e100920090112020910050a 66
    0x101a000c081e00c18040101d09145010540e45481010344000c8203008000b03040d101e28100049000e08128508881e500141410100b007003050307043c8040105654110145810340d0560303145140840591280350406220044202528000b03800c550448401300c600030b40340d07a07103800017400810f04280025030010b41c0c100001000701e44485524541c034000e86807000103a0340d90704152070000101c6c100400a070088000c0030058a81a4841d540182c054400041d035403543d1030182c4100e07400075109444240b11100243c0c0d19900b818000d001a090202449103560881c0a01a0070202e80c10800c0c0304c100054414420f600000304107903140e45034512401c071407649000059940b90404030725055494022150042500164400070034100c030310141c00c0075040308003000244020300e8007507804581809500d01f8840520860300030008481c1c000c005c2071980d581c544a0358039807040c48001c000e00940c0f269004000309a010142c8005042d0151b034000550713a54100851640030b2075410055100d04a00e03404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 121615233 1250 121613983 121613993
    0x100504020c0f0d0c02010507060c110f010f0e010b0303030105010807140307080a0f0c140a05040b04080d0f0207060c060921051305011d120f01091109150901090c050c0604 75
    0x1070302c1d9960320303080c0e8081281c1c1120465080302240c0c000380c0841c0c410012040092445c1c0e2280b0400750b95880c2507507d8100d0380004030704119054400443c140c0d103802c1300d400c5000c3c0500c031b40d40013602044000c01003407543c0300201e41c4a000500c100340c1840101000262120301496441c640c0d00b01e5035241c00d80d60726110708040c101035401d58003615078519142000b8078500c0648034809910300351b9250002c00101010510b541603208590217001c1213418007001400c64120382c003900c05408160081d2105000c420b01c0200f20049881014003154072a0f1020041141c000c50351090b0a40c1100000c80c1d413041506000040913460b5204440004c07075000c0028046034402c0140040b80015141c4003901ca40c9e91004440c41c1a8900e07124401d002c4800311580f1a241c43c0184507200680d1100741c1e0b024000c800c001d1030840300d450400751184000c61a00115900e020040b0660002140030703203d0a0840101c041103000780140225204140da562a501110b030040055a030f00b100840c1c1129040d1406141c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 121616483 1250 121615233 121615243
    0x10c03060617090a200a030507050909070e0c0d060b030a090309080f1005061906020c01081e13051f15060c1502160210020d020d02010509070e100504020c 68
    0xa080d002070001290012000e400c50380550060400301c00502248000f07840d1185c0f52048001440b600810102d8104050f44a0080a00007103005070050b10f040b40c13818081c40002c00008000741c105402408041c0046480d08000079000320b00f02c44d1180d00c454079101e48400611a40e082802c60308070100401031014190381007680140d100f81e8030809031aa8070500707181e540902c0581c0e100f20390820102c5000d000c29a500281e40000000d1041c1d034403a020344014440c000c42904002e00507000411110655604140301c60380082541590000c0000440a1480e6151001e802454001110740b044000c4c4501044610f2585021045040d603240409480384018009901a014a041c0003640019150b0040e85100c6101c0d17000060700c281030350107120304402540701c0104440641404801c000140c2c94400340c5501703200594009104441c52501c01034907005050f40c2150841e1b060034100302c811080442d28904890f01c055085100e512546807981843c2c0183d000540c0152000c0351005d13004d500014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 121617733 1250 121616483 121616489
    0x10203070e0609030a03050d02070615080607090e010b07050a1e0201020106140306010e040f0b0703050a0b03120f13080a0609020901060c03090b0c150c0a11070e04110111010c0306 79
    0x80780480101000c090120783c0c098007a031568990014000100424024030042040008641006207032080340d907218000ca60083c02810300c0c80e42184c07400c0c4000001040461313041607582c2030401c0200d2a00c0c2510150f420140581550b01034045641010003004005086070300e540240d030f250710814070110440d420021030505a00540c01c0800026410703c4440340e1070100100a009040301e80c0c01c00c494082d00c0e22018104407600c44005070f0721004194a402424081c403042d540102d140d05048007000242c4410b144410302c81d4120040403105003880c03008a41818140d520899205c440c80c5001d800052305030343c00300080b80101464a800c021865000080492003110714800590700c610045400151405000380400c000e0401404103104d804007810304a141c1c0000c84903640c9581030032040460f01035a012010aa022400e014410340204007045007004c0c4c0401409251320b80f49681c001390790003401c0901006a002c6621401d40d10a84583d150003515000131b00c200711000100400401141c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 121618983 1250 121617733 121617737
    0x201020705060a0e2109012a0506040b0c120103020405100801050103081308161809020402070b010e01090c020604020405100b070c030c0f0302011e0203130e041109070801120201090b070501020307 86
    0x968440d2480345011903020400e0100d2070001e041041780c10041d180f0323003017905680c8101c91032810003411082e0104c2c18100344520440152403e03017080d00d00300c0c0100070007800c0c0c0b100441c414010208031581c0381211750b045903012500800c00380c4410110000c1d50aaa4200344010350800002006010056005202c40700d42401e00c00d02c3d21350b40300c0625031611030030100030b81080d080a004102e6441d00b100c0e0400b0555541c01d00050404241d40050220703448643c3c1101c05440c60340040160400c0000100e004202162007402940681c802c025218080104000d104958940214076210045100c000c043d244c41d04249641744800d041080041c0900e100480d03d0050314000822405000d462020880e941030b101c1d10745406000001a814042c030186141c02c500c8240801e699042441c00c02074000d04034986501d500d07090a04008025140507800075009207901c2045c4441d142d801141d09045900100050040940500c012900c0042ea0362110218640201d21a014040c0641c01540140066 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 121620233 1250 121618983 121618993
    0x81b010b15190806010201020409020d0504020102071a0901141b0f060901091101050c010b060f0d0b0d0321020f03100e06030601030308070311070c0f0e010f0f060f0201020705060a0e 80
    0x44801c01403148180014500440b5240490710b40c0507000b070032800c1c2c1001050002505003511f4000c034900f02d8112540042c5450303243d40a01007956010300001c00a042051402d0644031903960351541140700c2c2281550410401c41d0001c40200050300603108584004c2040e80103070454001000c1d035a1850600798460b0707018800115160500500ca4440703020351000b205601d081b117640040d00ca58018a80b40c1446540780c1c0c0c6440301c42c0d0341e050010102005240822a2030300c03881d518070307800c54591200190041e5491001480800d400000c030048500d01907400d0080d910750000424068007890940304600341d4080309000b1940310910304102a00c4c40c00401040a5440600701641c80d802840090003040500b070210300d9244c801d4014201c08078040500e2441d0082540c1d0300003c40701d269001d0451600d0b14041448800b044002c10b5005015040151440a04118810952803010301c0350400f48902d030b013041100513000303405803030b00d80c1d4000042c0c0720319143c42c49881018000601605142e0b01034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 121621483 1250 121620233 121620259
    0x20303010303180e01090e0f0a050706390305070f061b02061e0912040e040b0105010206070f0507020a09090c03050f0d090905150307031209050a140409081b010b 71
    0x7201070108201c1340e01c01c101002c2a480c00d101880100a50325007030b08680034034104c8004100341002140b1541d0701c644010885e9518044005007081d8000d4070b659942c0c01e81e8402020000815009841d504c0c0181408441206044c5000d5500d440798100c014081c4120800303420a000603030b4003c6d0400c5101d602c64200c203030b42e00c000403a1036140c201d800c040e114881e030800c01080000600e010f6440b50382c6404483e503c07a2a07521420160300b2582c020030f2481440010442004011032489006000a0004007180d00300307504040c00b0000f5240e026401c1002c007281910965030350b1000a070050821341000c000c044107500b40300744110414003042d1454880c0481e01c84400c080011485100602030365080315040c00c040c0300d50083d01d4007820007150300d0b02000d0b28000b07540d81070142e0002144101201041c0607031400c405000c0086030341c0403620070b0900540c00c00c42301c03020220020b2229400c440000b500000c2746060301d454018001d4403901404840846820190154060100947c0450358880d407480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 121622733 1250 121621483 121621517
    0x40305070501080c0d110c0a150f0c1403151512400209070c031701030210031d07060c0318150c080904095703080a020303010303 57
    0x40c0e40c0421010070401608818034001d0b840707005240010b51b507061801e4001c3c21003903c4c00e03282000c02e45000f256200403807a40c042503c43c42040281920013440f004400301d801074044200702004c003140b900f000002404810004240440e84400284000c80031109808945402c2d001001e03040d04400d001004140400740d0320a5a1602070030403041c10400d2402e00290018a014070705c52045012780060031140181e0300c0d000b880c1e10590340741e603c6a011b01c0031801c0080460440101080d012441100103001503254441035180c841a54200400d45182e01c0e8540c608030708244940385c2c024050040c0c003088880d80714103140740e92030280c3c1d01c9030700351403a03540540d0031488544076510400500d01e003c80136980c041c40031010003e00800c0c1c198180050340e400b10701514051101150610400000310032000d100041d2881c8510481009901c003045689031004d501ca82c4000f1030350001100786405404540c0c0c0c41c0280040c40c1d2000c003047e1904941c00010f980c80e003003804102c01188103400c841060078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 121623983 1250 121622733 121622747
    0x402030609060105030c0f04090f030806090a271b0611010606050c0d03050c1303060b04050702011a0111030904020c1e0f07030b0606071b0302010f021615090e0c040305070501 77
    0x240c0c010090040b0a000c1000c0026251151f881250000e884071650f402040d614101426a02e000303403030386a501d282038010000000c0c801403c145180d8901046100c4070400d101c480300c3d00c1c0702400484401104035040185803410115400c21a0700d0b4015804980143e0040d969050011901c00a01166032110700035140d5005060004816034004031092400501c650061504988107030a03e52600103501801104025143c00a40c0d0f1280c640c82c080f8641d041c10b10400340d00550500c003c00c0440c1c000c04540e03407441440c1c03000314104440103041d10f0034404240201c4074400f400610071541e030038000c480c03d074940e031210b12100024109016012007134500801c0da5440d140b0b08a0143c840341d41541e403044039800307024103900d800250a121200010f414180701014812a150211072620f14502c0010806400141802c0c1150031805c80207407803607036414034a000d9500d02200c11201c00b0f842c01003180c40b040158018044140e10400b8020741d540c20fa001030041e00c2c06070055450a54541e4015a000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 121625233 1250 121623983 121623989
    0x20a02131d0c0103050a1a2e0507030f03020f090906010e1905120304030b0103081602041d06011e060305060303160c060f0305190903020a050d0e0f040e030405060a0201020d1404020306090601 84
    0x6005101141c821f64506042c0e1240c02c0104840e070720241000707145403652051450005000400c0e800140300080c19000114000100740c20314056203004400f046c03100c002e0083c94801030090050341c0210340307507a0050060f40400e920143c1000c80120509a000350340ca2102d104241c000c1a200c40703031404040001c401c5034141e980220380d4000c83d91a554820b4282d50007000410340500d0907401c3e00c2c1c010707600c0c1c1c01001090404074005c011161012a20a400c3c0001a40804401c400c41c80400740100440304205040710340a0a0014069560700040307401c40c1301e02e1034070241b801021000c6030100115114180c0030358001e560389a1203502201400d40071102d059130f04000340d11140040c0c1050b004250080408240300b841501d4041b4042d40d0351510b8030801502043c0480d02815002409041c6400c8000100400301c409111074003100100503280d1040d8001c0b0740c06002d00060200c1c542d8002d404031800c80c20000001c0103800410f400d0f482611006803401ca10038001c0038003091500300006032650503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 121626483 1250 121625233 121625261
    0x50a090b0f0d06060302060f0d050a0c021209010201020f030c0a1e08130221100b0301140103120908120301140303030702060f070309060e0f0708030406020a02131d0c0103050a 77
    0x710300c01d00801c00101c0401c0070000c0354001d448990100051b200e00c400750a20301000a0620344418601e800b0105407031005001800091501000141c50f65002030f180314844288550583c0d1643e58a0040380a881251074041541c1c800100b401140f078038460040405100903940e64244d0315003480840408c101d0f04900740002000840841c1ca40340c04098010341c02c40c801030076580701e0120307890811404502c09000c194203820100441d4003112032405403e1111608800800c40c0301c030301404042c1500018000541010130000d110a0494050035009019020340c4084590222082c100701116900900520101d828000808001410008160383c02150f00d60090400c40d90f6200e401d91076101d000b0100e40030540c442c0d02c4a40030a00d28496142894032120107840ca070a202c8108501d03080740c81e4407140c0543c3c4200030802c1102d50124590403440d50484503180070291203456000688403645030844031144070810504480030015a181440c44280c0303003031000307031b8801d24400c08880030310313000e004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 121627733 1250 121626483 121626499
    0xc020c09150301050123100504052e09031703090c1903111509010c0302030f070302150903030f0106050a120612031707020c12190b04060f02041211150f04050a090b 72
    0x143d180103000b00d47d901840e071034000d06145d940c00c006842160f050040e03c5d1120200c4521460291549034001a2413800307050000d0604d14564840707045a501c1c0c0101045d00c00c0104c081180010144003081e0303c203400420302540d005114100b250070250f2440f08403245109190384a41034182100c102089904881c003060410380c007403005640c83ca40c282d00c00c40450000300404581401d0f004040d01c001400f9900405130f00d00a0b021241c1400c0001e00030205661050041002c00c035000000503047d81c505142a80e12550840c0003900c200768022082291181855404203007503c03084481040c890280d641e0890502003c15051038001e02540d81c2d50041c3c100020305012820310203c0002c2040328030085a2008a6550380c8021000b8980821150107405006000c2800494040e248209100300700840c5094a41480c050303100c04010350082c00000b018000040ca650741c403214008075907400e840340b0b680c0e1030a030200002d2a440750207040d21803003d45001042c5050188680304422102034036001d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 121628983 1250 121627733 121627799
    0x50706020a031104090c110f03071b0b041d1f050f13020c0106300f081c0f1a060d0209060714010b0f220c020c091503010501 55
    0x1802a50000c2100c4051540b00c0e08418070380490700008100801c8121340021701030064036001002d413002c12681244c0e9902c0003890030380219001c021102e580346e200a0580b400399004802c400c80300c007591f000b10f0315004007060028040c40780c0c940d40c0d504c1d4075501c11040d4299a41e0b00e0303004100400d5141070f20f4184000481404035060403000d9001c038140090031b103a5408031895244050b41d000341c10343d203800d0b510ac6804105102c3d41051072100c051030851030301d000764041011000310015803a806405041c6501e1180141f1000804803050021a40030700c0142030403503214100541003010140000d01d2501c0103c944250f2602c05c00300e121305000740300c0ca1810103c400404041d41014200980c44901002684000341c10000d042000c8480030700003041c06e000c0c0e8001c022000b411049502c0c016608022407028801603c945110001007a90703000a00e4034840000324501051880c40700e0300210308806020684d0b845d06a0350941100442c002e0005a032100c210385041c0008444c10700d11004450299 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 121630233 1250 121628983 121628993
    0xd080c1c1707051b010f0b010e0109030f0305030c07060c1d04020c0c151b070e150306071206120b10080d020601090b0d02090a0209030d020705010509040e16170606040c0507 76
    0x1800c103486000b8032158042e0288984c82d08681c401d4110301550b50341c1d50042400713940c01051442c0c01c2c1a090a2408c0b250b85161501852102d151400404100700013000907046104041619030f5140c00c90410004001c2403040a0300c0c280b106038200e007010300c1240d50f4030120f10300b500031101c4541d078090141c0100d01110b814001a1681101c2d0790b030620300300780100c542894454a58504510902c030040000501d0039002c0c41c4006806081c208000c0c452400504850b1030010300e080d08810b4501d4000e0170580c84800e428000c00c0250800a0200003141c0350b00240025003402a02418021411903c0c51340d98001d007644d41c0c40c84191840158021000400c020b00b0307541e0001150381c0d0050b0900140d552239900280159104440244e000759001c6944030aa081c20480301401c110300340010301100c2d00304800680349020703852085204640f074007500703410302005018403180c107103606d031600b01815110f0100c0d0244161081d0554018490800090f00c01c0ca0940a41940140305444d41c510b46101e0740c0f0b82c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 121631483 1250 121630233 121630237
    0x11a040311030703050610150f050702090a0f05070306060311040e040b07120f020403051b010806060d06050607060b011205070c0f080c0703050c03010c0c0209150d080c1c170705 78
    0x107650600403214008003158044c41220712580d00c1010410090342000700754007012400c0c0c4103050800c00444c000140c0542c001c000c4489940c2c04403400c03403940c1e40d0100884050481141da045200d8140418420407540542004041d52a40e0310103000c1c451210042d001c179401144a421150f06003200450041034088221700d4102d8220302e8030440e1407490812243c02d0f2505042848000e5070300103410000d10809100246401080f04503551001944030300081518402900d014401c81e0002400c1d8940701c8913078014402050f0140007a40c070f5400303d00b8400005d2880ca11120301040d140c0c0c007104458401445500d01c038004d039484600c190340741510303000c1c41c3c417096250494a12504200114104070204141c0000310720078001070011810346001d160a43d400e0240e030505000028600b0801a581c52504e190f0100002f00050040028040003451402d09a00058410a00010142c54a60307000c5154005024010708585000001180890306d40307006104812201420401081c81c040c41000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 121632733 1250 121631483 121631513
    0x31f060513090b060412050a060c0e09010605031612020c1002040509010b040608011a1b0a031d030717031c0203010503010b0a050d03230408030705010c1404060e06070f1a011a0403 79
    0x1101da5112307060759104221508209000e0100320345050401491410501c61805800300345030890541c148001401030340d448541c403010920100c3d080c006032404160f0305490900e14014102d4000c80740c1561071400035803250003618003400701c0400106503046414121012180142d80745000e5030310704001a0f100c110342c0500c04240540805c9030055000600d1480400b1f01c5800014011800300b0b890050b008604451021a881d440320038a03000c640da01050b40400c45002400380c8020300030060031541541f041c01521300021280034000c0d009140f895001c0c5043e207070241c0003046a108090100001e07460307103210319580401c0d501c0d11100064894007002e9a0010b480780a1042244021180902070b0060b402a491a40c40840d000d02401070034050800c814210341400c0001400c490003281e51442107005600c10303c83d600500441070748130142100c00107a00b103100388201280600c1c203081d8501e619091300303071201d240d6000421130560030303820284208071100e83d0700e02c2e003442d5550b115a078005c010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 121633983 1250 121632733 121632743
    0x70503030a1e0c0e03060a0e0a1403041508040c06020115120c1a090a12080306061305150a020610230f030a140607050f0708031f060513090b060412 65
    0x2070304061144115001c1d2004000b01130303d80007400d54004041c1890b00400038071000c462030a102030b030340e48003c0110301140440d0300003403029481030300b0852035861482241d004251840c1041850907201d42d0224407140241c1c40f40b5060f2200e1560703150220700781c845d028003402551507201c50400278404040c0034403041920944455820aa960303580d182030704281c254504c1c01200028039481c0ca8540070136004040c043d170000d14604940e080e114904180001085507000b0300c00001c0000a111001110310001c0000074040e1001012100b941441a0072006c007180140c8903580100d102c008544094000b41c80ca00c40c41d0515201d03404540180d0000a90202900150420046030f03070340d00c2c140103807490700b07003d0003a00705a01d003040c0c0128500340c1f004052404005c000d000c07082800c1005000c441440f80c201c060345449440e20260407604001d803408001e02a000c01e1400643c1d1900400a0010707000045c6802140c5039541c003202c401d035075000f85c2e2540e018400f00010701c4840e07040c4440c420306901075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 121635233 1250 121633983 121634021
    0xe04050c03060a38060309074202100b01090902030a051506070302121b0f060906010f0506070f0804120602090a09090b040b06130609050114010203070503030a 70
    0x30402282c2422400d4451001258a07a0000581c0103850480c01041c41892101d40070740c2d030000792010121960b010000c40c03044800001044030a002040350034054501001940e41c030305c1d20090440068001407154409149800300b001080d44038480c4072141e8038007a038020b0154a140307180385170004c000417500103060020005010442c4c003d14809580320315900c0600003450b0074081d02c8080840078911805214800c00c20607007000a40c0840c4401c440e54600d034919489444612401c040c0344029209051984505180d80b8645440000d503e0702981011040d07608030b903264039402c2c08424a80c081d19402c500304103e2040000ca10300e001400150060405500b090380318021200b0003807400f5010384980c1c2c1c0206502d04c41d03103014244c2c0c00050101c20810441310900b6030b14440c08080041000c0d0409440400044050301d8500404c03140e1103040d50200603c40c2c452040b00014003080c092007041000b001c0802c102540000201c95405400400843c19030751120b0034000688868442c2105143ca4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 121636483 1250 121635233 121635253
    0xa020d021311090f0d030f08091c080f070801050f0d060b04111209060f2d0c0d0e0f060103240903031406010c0c0603020a0201020f0406030b09090111040e0405 70
    0x7284640004561030748001d41d40c0301c109a082041e100c2265050b1441600010b20110000e90131112041e55030345241810081e9940310a030281c1080301c8800e1804500140c408000c0758940e00140360352098804540703407455605c0301d074400c60344c84400b406040e42000803c00c00c2c0c9a10f24040c0c00d01180701d8810306011030005010400b080603150f015810744c1c402c01000c550900340c0c00818454560000d589001005c1c107103005400c2c841c0e80b48000d4400310f00d1401c0d6500711000480f060394040650780141d090564141031821789060982d11401030180c2c01c901c0e1030038090009502007020400c00c5492001031140703901315101c255950010045442000b9881410744022070464001e14209a020740c41c0001c03d485d86601c56400b681000745054108112066140000f6518400c040180d401601c1d0051b01c2d078120081c142c0c0284100c0041c0301040a012400040f560b034540c1180151640680d1102402d40310547c10350f0a941319000c0c4184a020180014058030f40101e805a40c480d0080d01102d074102c80e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 121637733 1250 121636483 121636519
    0xc030903010e0c030f01020a050f0708090415080f031215120a05280201020706080703021b0a17070f030c020604051f020601080309010c080304060b03030406210605030a020d02 77
    0xd28a520b4514079008200641c80d0381c6400e0100041e240e0421000b9441c1c80b400403002807480c881c0941c980c680324008100c240074001d15030252141104094002c2003600c190044a0040c44024840e6220501c04d4010a07000900007100341d5921070b400c4140c1003c152642c00461100300c0b0200300194200a0002144a88180410002c80414010b0014141004606003412144244001c8c8810042c00000c1004010f0742e00107003040465000f85401441600d84420480103441851240f00107589880041c0010003804100d03424118030070301d681005403000d004085e43c2401010b0014004014117450303880424015102c10028510060019140075103650002e4041141c000c82d958520a00150181055404104003405072952100950401d020000000c0c000c201c08200204949400700206040040d035400051288400a054903296500c4031401400d4448035006e0341114240c01820760b040340170307910408003914405009840340e0300302e81d0240720100010300c0040f43c0008560005600001d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 121638983 1250 121637733 121637741
    0x109050d030213050405090d030c09052d150d090501020403061107050106080304050307180b040608030d0c09150e1201020409140c0a0912054306080106050c03090301 73
    0x8030651801600c40c0444207084002c0242a0404d50150345000107001403a4000640c61142d00420b00d8081840300f000b80e4101c5040125511094114811400c002e04441d0380e081d89404d4640c0070700100c15030340640002c0008446031038580240e141d0040103c0c0c0500601c03a0490b105003070103007001501c4c140e03480c1e81c0c180c1100c1023650950900e400c003040078810000c01f801420000c0141c54025818107003048000380d161111485482005075455505540c0c045d825006881d040c18002c01c02c02119948002e503503182d0b800f41c0d05260078503280040031040d42c0c0c051203c41003a511240f44135050041400c0060315050b014001140d8460302c1004109a0b4a03000d0000300084e202807840410221000f00c41c83e000e9034005081e0542e01c6009001d038034015580031300303403400708c46a21100e5803c407141400d281e400c058014010104900c4038a6001940035405400007005060703500140103080000200340c90075203001d01840c40001c1f503e500402c03000e80300c1c0c0c01030001c903c080c0065900d02000c03600024211 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 121640233 1250 121638983 121639003
    0x11809050307030509190b030c0d110f070323162f01030f0e0a1101120504050615060702010c0314040b030901090506060603160f1709010e0c01020c03120705010905 72
    0x4c0c000191001207400c200400821080000200183c2c2c6805d010260740c04d03010003800508032280128950108103003a8012070500b29030301048541d1042081a481d400e035104000540c0411b084020692001c4050001c680c200304400c0869814401109014450401022015070380108400441d4007110000c914501038040026003034104c560088001400303580b10701600155551401c03005504100c00400c0104a559100d9150841840442c005980b8101d036203d0210b07400389440304001c20002c000820a004005125864127240d17030801c00c101080c416110000e000034101041b02001a00900007807640741d4035091020b041c6a100c0340d105200c1c1c2c004584060740742c1c0d1a5040c04084c05420300030315404c03c01c1541c4441c0b45103030042c0e4084401805012081c10003140d03070424480d5901c20080c2002d80c0d640300d0208440c904215182501819810700540c5060180c04160607070b6600006510000400103000b40145203803580d9450083d4000c504181d40f1552104600c00000f0703c00d101084107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 121641483 1250 121640233 121640237
    0x20a0e19030203100c170403020a0f0b0702011505241603020a151104060e0301090f0501230910200a09030b06040504020a050d02241b031201180905030703 68
    0x500c1d60040601d4241c4036035a01505502d441d8040e1112a0301072010704c036910354500d07001082e459a20f0100c0c9000c9004201070241c27500d2401c03941c10400d2884103035001c1e141a0f40280800510024020100640362240550100a040a000d4105060807110340b6040d81c62036020704009907141c0e0704480c5603029404400680120314501d040185d06246141c0300904100100b00105240740720039240e110b00d02070755003407040d124202012a9025007210300c0c6546e01030303541c1000d034030b0034502180030348010310380c2010040b486130781c0c05251002d0340d4029114007030210091540c006031007401e4000b03041c0050840001c8142c1030030107180c003803400020000700d40141d6641181c00c1c558189901e110f00040c04052103281404140805070707035410703148800d0310411030700c408041e0321500c001040c0c000445129016004111038404000780494068654540c1400240140014404503942c03248101c40e041c0c00e1881d40c0c4801846100c01ca80e03002d10742101802800180140c007a150546550445001100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 121642733 1250 121641483 121641529
    0xb03010b0306070323100501080c16080702040c0e1f0e120d08010b07050a02010509060904060e0a18050717070b0c0106061b0308041103150103050102030a230a020a0e 73
    0xea0107001c0004203020600f54210700138982401b00c86511104020321600c2d04000481c40030a1098210208440005694030100c000903031a0307151000c0309421564040e48900d1405080c1c008640c01202484c82d40c0800034001c0d182046045040c100404413519035070708100c15010740084a880300c8060941004220000b40060000c0110082000005801508144500b03000390f800245000032070810065090a00035100e05200021801e14040c034140d8591180c10800001058250002c844c0d00401c050380702882903040041c400e00c1c14248081006049900004003044410141a42c8140e08171646069076000c03503a5082c8085140c12003d85440d603039656000803c0002c1d0800f0000c02c02d8202d030003442403040d40c02c2d240034080a4000300054080f9441e508182800da5052080009102c1240007560803940c4906184d4000c0d0011659030030014075005040c03003108084006030b5144c01551103002820740d01d0b0301d0400040d421207005131050050044960103250740d0b1082c019265620144000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 121643983 1250 121642733 121642751
    0x601080105090a050604030f122a05041a0307030b09090c0f0d050c041a2706030303060904110d170a08100b041406090406120c090b06030a0b03010b03060703 69
    0x303085900140440c40c1c1c0c1e82c40b241d5400001070012a00f103034401e4040c2481d0410300d140c0041514401401c2c41401e1003189001e000880e000c029a0902030040320280810301100c0050001307641503c203501510b544003071603440344070002041c58015903000345245004a107800712580481c4041109403010681e94100e444d00c800030b803e12500040c00c52004071107204030780407680c071103907100c41018170b0580c025611074103035071781003682c0504110310b81c400036100c0e0361030080040c3c0e11400c1205000804181d042c510300890300c640740000c241c078000c01004003107001503205d940d00c076440940c0103501d003500003500c00940000b1481d20300f591442000c4000382159030f42e04c2104001c006200c0101b032941c03804507410050004040344010f49054403100000988034100000001e180c40c003440740301c00d50250a107035022803003900f04420610000d00c41d80300108c026466040c2007040e50101d0b1a00340c0c004805100040074600075070000511903801070000286001c840010a0a00d40116400c401080d01c40043c030b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 121645233 1250 121643983 121643999
    0xf05010f021908060a17030a020105012c04030e040c05030402030f07030309060e060403060612030f090303300e1b090c0a0302030408040f0602070906060507021810170601 75
    0x4481040d0941046252200c0e41d04141c0029582600700e408204000e400199141c4424411202900704840071030032800c400c3d00441d9880d13000b1039410006500780400040d40480046441801041c025a001904400c0040c20418110014002e508001c00b220312048180c5407446408100c00d910340e540f1303950b498140141490800701c035005402c40e84c00202c0400100b640a403512055802c3c038030300308900246000009055002d546c0025000d01d2510030005081030507001c0c00c1800510a49034482c0c209444a030a4560340c94600c409408030f440b0040b40c0c3c110100c244001d95070800010418080405c68040b0b407402c0300c0350303140e07240a25802030445100000072144102d5000d84221002ea181340b80030b000030f242d03501444d14108241900800410100f101840981d805012040c848220f95540c802000750b0380c05680c401c01280a00e032490100e80a4425012510141d4000e00201c0a086103c148400c0904000384100230f2142450004501c081c0c10780042c23004001024000d0040754141400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 121646483 1250 121645233 121645241
    0x120a020a11010c05070e0604110c01060f0b0705070b0a03020403050a0606141009031202030909040302070608150904020d08040b04030309031205070210030b18010e040c1401170a0f090f0501 83
    0x24503042c0444003c2801c001240019001c040e9401d00301010013980300d28022901901400310700700d55174800807070415001d140541c40308007191004114070000c40c3c0d440151540742d1240c400080c1940d000303241c0900c9900050002020358104e145001850183d50b03031103ca0070091744841c00c442c0580c03902000c0040381f143d244920032940003280d2282ca10304003d0006011740c03080f44001016402d074154010b00e418024001d88000c080c2c06004000079250501c0d000303407600080e001300c401142e503000c0030076102c00b00c00d503a00c007030440d001e0206056500e40381c003007104840c19210101e0300d8540410001c9004240e513000f84c001580b1980b1030903a5241146842d03040c0d244084501d00401c0000d02c09100545c1da00440d600742c01626080000f085510480480c218641c03042e56405c01c1003e0000010b00840d03100b4502d44181d010b808500c4009450f45140c8203454420302000340040c00100c8482441140c5c12060750700044402030014012030386074017000030799a004806a50600d4403000c1c020900c0b0003806 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 121647733 1250 121646483 121646513
    0xe1504060222150804060e030703020303011d070f111f0e1e0a150609020304350301060518030604080405030f0303011809020f0306040510181502090102120a020a 71
    0x50848010342400b80324103c4605183c14442045020300c082010302c43c440d031201130328403c242c054954420290402071364990081c890300070945452003d10045070b01c40104580242c0c40f13503942101c200450b010031a201c0040030284201030248030001c207030687c0080341e843c150720801e4202042401248000c0ea041c0b840841c10510010000c3c5400e0900441c0131601c07003045903100d2a40702110050800040080803141c0255000505c0082440b0a01c00b001d01041d82c41c1c4500704101051020120702c0c2025564200380a01e00d20101b40014020b05020700701900392050340060b00b442c42d50448002130f24007401a103042c0d07914180003805010608061000100f0881c407803004502d1545400500202010443c1d1807050301e0f96554900c80441d0b03078503640c0160b40c00c801802c0340c105080604049440321411628500118913201920701811100c180e1030f00103a400c02e0b0300c102c274000c03c9285100030358440d044060440c0074010341c842c1070580c0302000d49448411a8000c044501d801e2619aa030403030410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 121648983 1250 121647733 121647787
    0x9070315140f060322050a051006050a0b09011409040902030111090102070b030f010302041e0f050f221407051f03051005060a140409021615050402060d0e15040602 72
    0x10800420300d505901755403814044400c8400801c141400d50402c40e1004009086003d0741078080403820017904200244d8030f048400098650340e41c080c0c00d42901c20040a10b000c24640c0084007080c421081c05070004190103000400c80300c030a540001c0c00c5480d01e00284850140101e0010031f04d5170304110344000380c5464402146181402403805081910501c170007485982c8508101d01e52400c0032100c85414034031454280140c0f1041e507081c1c4040c01c011a840309082120100145c0d170078444505540d08000d9840c400c6545c0035658650048954209009a2161140140c00502911400a4a1801c0740110f4003458001c03c2c60b1001416200080c005c01d1040e0f03185a01400556107410403103485414074280b0f07491503260b80d407007102c01c0d0042d03500100c6440d2020444245079032901c401c55092901c84d0300c0c028141003004031944100d65064802940100060101403030ba0041c40d40850301c031072445400c40b05c01500c0b03440c51a0740900c00701e808841643d00480c00c80240703504440f0311070010b1030070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 121650233 1250 121648983 121648987
    0x14010201090309030807050106030602160302150610080405070312051803010626010b060406020c0f18012303160501031407080c130504180b0c0708040509070315140f06 74
    0x382c600401c800c00e0740c000502207900001e501c0e401c004095010078011b6a01200c00e546500340551240ca01026100080d00540919880480b003074803489544c1c0e2241f04000c0044048990304241225801d200600c101d44900c107181001c4003040301e03688044c0d1004003ea8038143c0c2d54007410305201c0b110306101b1603d0300070b0f810810180040d01302da0101c071000b104517038001d00507180c2003800c4501414408a000360800000240410f1040e401706400c081903078142d528005101500c41444201c00600c0600c2d200121800c005000320a824201c5084808030340007003c2400004400203801e0080e80c01c1c1c1501c00d0355051204018658060054020f01207052003503401d289000e000c040d02420004020b1a04481c0c0000e901e010b041c1e1002c0204013600003c0d10401160000d000b2102c0141c1c0d07641303415070380180c002c000201040044001c8500d2903911804080c20079142509020118402810034001d00d900c4450f901c4180d43c5100241c1d0090401e02d00c0340d541041540c00b480350101104071101e02516003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 121651483 1250 121650233 121650251
    0x150302280626040507031506060519030b0901030c0914090604030509010c0c26060708060f010201060b0309032101140609010324090f020f1e0c070b03010501080a02070203100f0b03030f030114010201 87
    0xae0b044d55112124959000e52540b03005500f2401840e06484043e44415402e0010080c0074451200c0e20550710390960800512210140644209000716540f1b0880d612020000d00001c5c032400c0501401e20060400254401060f0341d407503001d85068005003c80c2488044000214502481120b02f004041c1c0c058582130400d00c5c0b00625680300201514054601502010000d034400d61104008000c4405801d03140d080150855460350b024500107036500b4070081035070507420b10103003002e812150b0022280303c0d014400c1c010320081ea0000300046041c1503403007404041a0a0303c02804000602c0303a2094580301c0c0c04e1003a05400c4a40140c0828000e903c1403040440159001b800c0f1007040000740e46010710380c260003080003560310402c1f40c0f5040302d004d00d5200150008012001d141611000d894020903a5110040c90301240039549002e98161700095140071030094541c441d41603a034a102c40401c6884074440420b295901c2425440c60000002004100d61590180c01c0c00703030600c0903c003d0061440d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 121652733 1250 121651483 121651487
    0x24070201021e03160819030b0f031c120209090108030a030f051b030408040308070803150607080a030c0c05070605040e0a18080f070615030228062604050703150606 72
    0x9100d400c200584e050425040900500c1c00a07641d42200320414445e50040b1107800130080e0600d0001c080c029800285081c000f4a00402c1d40c0281e011001c88000100c6440d54080ba04510304002c610ba42580c20440b03c14180c984441050103042c103100119520784803c41c0003002c40d601780490890440c80c0105005800340c0e6002000501e002440820f902d80e21607051100e100e2051b944000c001101c002043c200b00103100010310302c581c19a0010224030713400f40040c801d1521443c100101a820100726120032a80694050302d40c2c2c65503072034180521801550340c14a040e985030062804950049020890100d160446030b83c01160743c0420b002d48003044c9541d0440e0851080e00034134001e404501041a5000c01c0140d45201c0e821110500c04003051108007581c1c1d16081c00241c0c01000141510100350305194610b0020142425a4401c1986400c00840b070703980040044200b000c05022800d10700070300c5a240700340a503000d003026001c01c524610b001050405040211429503040c0b29007002a50303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 121653983 1250 121652733 121652737
    0x9080f010e031614070e040b01080c060306010f02240121020a06081b030f10091503060b0325060801080d02031c020412050a0501050604090f080924070201021e03 71
    0xd01e0440300d90b20340030a078a4245a05240c1d03610203240e501c60b0845c0046d002c49100c2100e03016030f001d0202014140d89510314541c0343ea900e02c44181c1c0142d410008141e0f10b5115402e00482d4000c1031044d6a150740000000c1950405050442040f15602000501c010041c200303050780d6160080a034006000400d5000c5a00c034469881910240003c10000446042807009001825150741d01d5881c1d591415402900480c98280d6442604450b608000716182d202489088560302c010742c080c004151956580b28050076240201c5501070143c0d54040300c071101111440180380083c4024400510f0400d0700040050310141e01c05800d039484100d602e0b85440e00482112540084000b5503030700003a691003024064422603000803404c1000300c85210506c100807071110f51482c400e100901c200d4869400700416a481010301070f0603527041101c41800180c60500800c60840040c000d02a00b205a1480c05000400d039070300c0e100640300009003a0119a07042c81030080d99030380064840c140c08412182c0c01c0d80d074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 121655233 1250 121653983 121653997
    0x90a060305060a150e0403030903080609060d11010e03011d160506040303050a0e0d030e13050c040b220303080723030c071704080c010e040203010305060f04060e070609080f010e03 79
    0x400c1d44e9070116680c0441c404000070103800e8120b00400d0311700703203440c0c001c00809408500341d00051a04e400b0801c4c92904920041c050a80109503030101c100035261030051681ea03240f00c42c1071102d803001504454500380124550500d80040082c000014002c009050800d094040010f44158104c00c0c040c9903035000544003a030b0340500e0701d191514100d82054420305000b611240c4e01070044002c00c0101a8801107243c40b506060310380c8011210400030300e00590b1402da5a10340804814402840030b003194802500c590000b00101c542a08420a101c04515503d90030640014450204101d00035410000007032a0700302c0080440b948070500c861444c0e403030002a003414a010320000301700b000c0c0324020910325444d140c8040b00c10380d02d5998040803960381d9104031920b07001c00d80c0e03a81e88182c20710f801d10a487c12680c0000280c02c440e65500030ba08030580c002007084610315501c004020b040041046081c02034841502c9800416041c006104d103003103062014441c280e230504000b0319008001005903404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 121656483 1250 121655233 121655251
    0x3023a0f09020913030c020607060f0e0106180f0b0a0b0307110309030c0f030a0b09030d060503010603110118090608060103300e0127090b09040314090a150c02090a06030506 76
    0x4440c107172508031038501c1041800703544414017203a80e40501000354405007a41e20000c508101e0b5800103909182070350024071981d4000c4003034211511074240140c000041d040241e480004145502000080750f070701d4142c000c1c1041c8080842003009031900b1007042140d8003018802541007590240000e5900e0924050180c01203880e00b21002080d101001168581980b02001030064a4604695a070341d802c022500040303642001c6d400145802c06100b03807000c8da034111941450302c242210040d510560744041001030701d0400d07180010b0220380d5104000207420320102030b00c0070754918100300440400301c4410380c2514803080c40441d840b54540300c6030801c5101d5420700b05108111580160382806019660340f492801000e408010400700c51344200942c0e1410004001420301141400a80501191f00401180342d1010b280081d940e03d9002d0070214500a00809042e907d90303007042c400c404110b0201c00851f807a000c0c603070110310b40180c0855229102c14003c02078585552255980c41d00090905a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 121657733 1250 121656483 121656511
    0x3010b0405210303130314070f061d0a29011202130b040e06010f080a0309140604090e01090308220b040507080a0c0807060503010501090603023a0f090209 68
    0x25a411045245061032144503060f681c480c94058001680c03030030309400c118000350b2480804416072880900740c824081e0007114100380320382e040c2c1d1194010a82070480740f00c031001b03101451403099010804904400e21070815461101e0100d0f40010554125414103140d8052100050100c08805407885005540403200035451a015031444001086440b100d41e0700716051107900601c8250000b40c0e181200c95044103a161745a0f2690460345882502000500082010070100800a902600a10046c800900e1035240c10350300c0384440d0440d02400d60313004040e5100c2001105054214070429441709261000c20501c800d400801c205036035081800038021054040070805204040000c000548400000c0b5032000400c0d003030580d00e104091003900441c0c8180039002c00d80d40d228400390703070480f20183c44000c161402c1200c290040d4105003026107144181d0034a0004a100b0180d112a903d44080041d6203201c6515100394107507495400910b040c00d09090400005844103011140d01032299041d840c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 121658983 1250 121657733 121657759
    0x10050702010302030a0b0901150e040b01020601030209090f06040317060409020306130804030c080601031203090b0c030402120114180f060612190303050f0106110715171603060b03010b0405 83
    0x40007422001c6c00c15412240c140c0021a1014105600380003489064079882855980041000103403081c030b810301401a085a0010401401c000711f640d078101d042101030b02c2d050740b400c1a40900d414001c44098001900300d00200d0142107850b405141c11040945e000c0c0102d10460b00480d0b07841a024204285103036000c01d904051180d4402502c010b141c0c4803501648450381c601130640d9420702030000303440403c2c241801100207800303841070701c07042c03544548010703c15543c07081c02c1c04040c1c1005005981064001c000520305500a10030092007003c40c00d080c080a007454081094041907405004202d9841264204010040024410b0b07000e001141c9003a030345880300c8129800c0000b10945000f882091040c0a020560950445407282c80880c101780020380e602d0408980810038008400d42503001420148800740f010700407851402110f082812000e0784209058001100482d03004401c00154400980742a42c18018000100b1406180030708650501d02d00c0d040b644a544501482100044080 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 121660233 1250 121658983 121659001
    0x12070e0108013f0c030f11011707030203060d0510050f010501090303021c030204050603070c0605060901140d031e080f09032a100c0c05060c0a020c0f0a080d020304030b061005070201030203 83
    0x1c3c2c502c960780700d90f05240700c664a2404090407251804100c44080003405008080e5201d03891110a501c9030398142c4006032500f01c1d00358000d50001e0f01c1c031600504a4210740d00030540400584490036154030740080c9500c0d0800141d6510141030308050304000941c0c40c10804207030f001550302c205039000040c6159a550088050700244503580c00ba42e005400807080000007a0402c4000c25010b000302e1060219a407903a04020000740240207292101c00144070f900c0d01803d1644180840314800d0078600e078070ba100c11489011000c03400c444080001d040e403081203041c505107100ca0f600883c20310300441c144051f070342100d0b658401000e400a07500c46412601d005241e130400c0100c2c40c408140204004081c0381220003091007402c40d00039075482c480c6a001c600d020b0b80d01d80444018045641c054480030f19401c00300101210f0051a083c2c1c070105000f00402c207000d081c4441e0840348031071340041d580e071451898410b410714002010144503094841a03194520b8100084038005a03091070010b0381c039a100007035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 121661483 1250 121660233 121660349
    0x706020c13240806010f080705010f030504031205100503010b030319050f120a0506040e06040305160c0302060f031602070302010c0b1816050310050c16030512070e010801 75
    0xc8080082c80100d0000762503030000c244a4140c810b4040b400c1034182d1203400d00d90756001944641c0d030002e11124039040b5240e119070301c0303240c0003407184c50110301500c0c0356101401038403019690110340c20303201c4030108070038038092041e01f4241c0c006030055802c0003a4042c01014611032440c0c41c0090050000c0c1c0201501103240807145048021076401d0070905220034075000401d4110f9501c0e000b10b02d40002c95490220000c2c04a101c0c50349a41d030689450300031901c03a24015401c80045400002c40400440184c1d200000f030328403450810892622450304860000d801c40c82c00b0803a00564224140900250368845042d12201d50400030000741d07a1100c4601c18000c402d0070000524900078203000f095031500011200003140e20840444414501c0441840100e030380a6401107010709040001c03040300c6258007848806039000e03081860400c1a002003082d031b042000c40316030300040c021910001c03003580c001f10154050440020403116a4a98185e402504050442203022010651003c5110810750800d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 121662733 1250 121661483 121661531
    0x6121c090918060903021f0b011412010b090d06020730020c040b0a1e06182103050909010b03040519030c0b0603071502030c070e06010903081c060b0c0706020c13 71
    0x46180c0361f03284200401000b052a68442d60014041e8401e10341042c00c40d1060341e0030098070408200781a440c0a0b01141280d00440c41642c106200c0d603442c90104280344054450301c1d00483c0143d00382e4500d80d58940750200001501c0107000c1003800e0501446a0004e0700d501941000e481c005240c2d0203080004030a00c00399031100c1c40c440104054654040740e801c1c405804c950198555100b0b0740201509c3d4007100c142402410301c0160344030f0400c000d40544180310b014450080c10101c1c580800503000c1410441c09801080102c0c800005000c100401006100242e03002c14582c02d407801c01d41c0c1c0d00100140b0000e040501048a18004101c043d60144407400c01040c45151090043c0c20f1080080c0d265001404200b5190062140009524820039100d501c00c4d40140e4070000040d086503204140c1d070308021034000f6181d040003880c22006006100700d80c09000b14640041c1c071115144510341c90030020307030481c1b02150030206806959450302068103108076030040020485955118480400c1d0002c00c0b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 121663983 1250 121662733 121662763
    0x210304080f030c0a120b100e041b09140117040201050c100606170a05090a031101060e04060f0b0a060917010207020319051603080403060506121c09091806090302 71
    0x180050f40d000007000f05240b4030389032603a01e0b50717203590750803001250520b800c01900040f0300d2950954551003016510f5040c040200700141072000c401c030034504801c28540300070110b060000c0900441511848507451a402481d010259080020740c40340d09140241c070003414000003090340e001aa10922407180700a000e0401040080d81d5900020072064014200c100030601100108841104600a080c4511030305c1e00104540f946d240d400b12002caa004085001c555a5a1070101d1000d058903140390041e4092040801d125805007804011501d5041f0214458041c2140802c400750700815100101c1c0d840c0302da0b101c901c5e40705205c040d0180c415940000c2d418001c08110f101c840108103401c0c10b4550081c4102c8001d0031040240c1c5581e0030b2103000291444509002c200001303017080d004581e205901400701120710400304042450308030400c0c0c1205d010103480c0030004844e64040c62031001400d01420a2054403501c444501444800d400040c002c0c0c1d0b260381c0b844041c14001c04c085420b410042c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 121665233 1250 121663983 121663987
    0xc050a110f0105240a0308040b0f0403050604050309041410060f03060b161208220204091506061206140d0302030702090a02030a0c0c050606100207180e010608210304080f 75
    0x12489140550040401311038135820340d00b01c0c00b41c4c1d040148503c0c05a03a480740c0c030b940c54141000004991038102c2c00c3c85640c2400200408400142c05209c0c0c03501481c401c100442c1c03100c12507070400068a00400c40f850b034200f1103c2c104010111282c01030740c00c0710f24604000301c81081c02c003800c501808640c0c200100c04100010321802d5140542c1d2280300036401900d0b07a40800718103074811500d5040958003070040824004081200c0c82007540001040ca00c010000100e40d0050b031707100d4080c030790860350000c28250788140402985400c60490a4520050031f000c000b001d08041d4908031403204150030310b0007145c01c1408101058020030449100340d80051200c0c07480c2ca080c02140001c1e62044a44207110783c00c0c0240105440c1c040c07425a900c995206001c0e11a076500c2d401407160000e40890382204521402d200014403501c100700960301c1101248020401d420030001580c03d440c07203903000d043d03594004100121480c1900d03400d005102071070410b07a0b680761650300b00350708079003d4504440000d0b500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 121666483 1250 121665233 121665241
    0x13140402100311040f05040e031309020c100f020a020c030c0d030809031201030f0c06020d090918060e0a020307120807140f1204030b150303031513020a031401090c050a110f0105 78
    0x2101c00c0203000c4072402c48088c02120b0244043d0743d100d0003001d000000300030781811306026607000b0303802902005080f01c0c100c952042d0300348007580c19215181c900e941034550000300e142040780c2c140a20030300c444c0305400502d409210400032807001c400030070020b801c20a0140c0418441b24050045440207004580300c040700356145d00300b480c1000300c40c2c04211100e89100600040e428000f2403110b0742d00381c1940311150f0342450155040042c204056581c8031280021001c08001303021480341c42c4844c5484070090034038000302e00c1407500d010103c0d042603d041c004001a1000070350000226415107a0105220705030100c0400348a25100780c003200316140d40902071116213810800d801400440b4005c2a080c41c240e10b5488618040300d00b00c50319150036410030800a4450356400c411220b003201c000e01081c8070280400c4140301260400c40644c0006a02c0b10700c40d80d0301030f041001c03090140440f92410843d0803c0e10390050320922030020703c8030501940e02d403c4038580e8400d01000ca00038904038000e2200f80b81c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 121667733 1250 121666483 121666499
    0x110d150308030a0b0d060c021f05010b03011403030d050103060b03010b0f0d0809010c05060a0911040c120b0109031502120106140a140f0a1808070806010b0306150a0e1314040210031104 81
    0x501d00d00ca0b003000c1c04003143d00702249c00a4015141250b030074042d52441e517424120082c400001d1a141203405102c2004150034810340c9104840c000e5014000000c0c0e840703101410076003900e1f00896118850a250203421496a480e07100d01118181d21403c0e065591240c2401a9400c1c4980207028001d800f80c1405c024820b080c0d60450401e16116000318044103030344504010448204c4d032844000250414012008130240f503005030300c070b54814140003046581e640e0310000d030188035200c065440e54011865007040c0780d507280d006014041ca4180b03990315038600030122009001e503496140410000b0940e100301c610b2144c1c101c880c1c0fa0b41202c4c44a540308503414014060040c407680f42d49400544c003200040000010803118140d4010744058201a4642440807006400190401d58088520900c1000310080d010080a01025985440144098000400030083e0841e43d5a80d0b18500342500c90002c481d00030b4a45911540c129901c00f034100c25000d04074004c040000702c00842081c00600820080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 121668983 1250 121667733 121667743
    0x2120d031401031a150402070609050609240a020702130e160815090f07060c060b01080103080a0c0f0c080a021203070804050d05010b04110d150308030a0b0d060c02 72
    0x261620305100d600074200d150018910248030182842e030102100702496140351001681000d00ca0b4074000300040c030340c0001422070307201020440b0b007180e540d2070940402005101681c1d0210f0314001174a0000b00c00c0c110001c0c2e000360701410003031410703008001070282c107560f60599280760f80191080785043e249451900060900161280c0e40d84620b8400c0141581c2200c0d100f000d0b81c100f0360203000a045a400d551035241000342c250707449800b0390103018041200c100045402042d0603503501d03008507060b00344002200c6580018504100b5502e00510102c0c401504489540d80986050032039045981010061903e20242c0207044007140c84000400c0d1a00050401d0340314000c492082c25205d800c43c2c0b6507941c2c8601c132802040b0807403d1100f0025842c24041c60320203d03001c1c40001c50190106000101110125840d440842c40d01045010a402503441241d00b20101d1041c82c0b0080c5003180c03915a143d000c01030860203025103540e14021aa2110307520300c002c450b4080c50a009408074171501a441e1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 121670233 1250 121668983 121669003
    0x3040608091911040902010c0f0c060807050a020a0b15040f05070201110c0703060e12040305060703060605070b040b0c070c031118010608041104021c05011401090308030c03040f0212 80
    0x1034400c442c0c091441c0e403900303a6802c400e41e5000743d102c0003d080d01001e20016080c10344090b03040c070a403802d07524080303842c43c000301010b24070a0000b41092401c00c80080d10b00b03e405048182000340074050340c2001600051602141c84d0080d1607803182c1d1380c581c038221054548100c0e44e1500301d418921800800c00e5150000e0740104043e8009015040102d0a041c85902905a480c0140c5c0d004210410101d00c86610031005d201004c01541c14107400c40005044540c40390b07000700c60076408802048045c503454401e00303014190310310701b40340f800f98151141c0c1200d801c0600068400d104041c089070800c402002207a48140e84079503401070071592420050003414204c2c01590103000c00c64040441d148900321020b0698215440d2140d568441d034035aa8240e1078514800c5d50810350801c011101c290001241d400d11010f5903401064641c145580d41c84006031080e01d4a043c0400c00d03c007800002c140809599004902d2000c8944a640d5410b1035210040101000b035000400c25080038244903000c2807031110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 121671483 1250 121670233 121670251
    0xc03080c0d110a1823040f0b0d030c02150405130506010210090303060311010908030403110f06040801090c05150d020d090204051914010f090203040501063b090601150201020c03040608 81
    0x4010341c0c1d01c0b448000000c039400c07041148080c40090a4452500740c0c8a1f20380196400320014070380b040a00840c5c2d51030002d00d000d80102e18100d400c1400c514140c2107094180307500800c0541058542800308402145425448402c0741e114070005525034420000c0115a41c0b40b20024442d0602c2c50078060300408160006980c038422072550602c155008410b000101c3d200c0c0802540350515544550480710010711032142e12540884040c80ca03a0350304c0d4058405003103044000101800e80d45400c00b05900c1a0340054050200344103900701c0c40500350141e0b040f507403640c41c002da9580c4540d81ca0300f004103c842c000a502c2441c142c04d202460707502405004034150071100c00c2000c480501400c2021003800d03c1a80304a164102e014070000b004c6802a603000b40c4140004911180c480502d00c105000f00886031000c400110900f40c1182e0440c141841245c1c1695100b940c40e0824401603030310b030ba6050007400050b2400d5268900414400d5040310305508513001076035111502c0d0440104903002c10307503200c84 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 121672733 1250 121671483 121671527
    0x908070905060a0308030903090607060c030e0a231207110a141f0c02130203090d091a0f121906050f090714040b030c0306100c03080c0d110a 62
    0x51590920301c25140a071100070064103805280d941c5040d4107905c000d1401000740020f0103a120f00c0e480314400303002403a10901c8081041d02280780700500705c6001c821031107041d600488100010038461001412022548110301d2540016003403240e00e449800c149410500c07d001481d034050148a442600700c07800100c03901a0035660b100b800e09203d00c0d07a510050b41c4009050440604451074490110400b891410300d9000c00e0f0803034000400d400380d42929070030b00940002c2000b07040103060100c00381244807030510003916801d00345080f14964982000c0000340d41c0004140b010301e0010400d54011341e071403824803003251030b06c6e001440240c05e9288015040500381000811a460100b40070039500381d02404044003039540040460f54807901c2c90844030300700d20400c40840d00641d042700461140e9586040709607607091800034890f034040e400000008202e0000321500c0040d610507010358002c00d800d501030342c690031101c98000050070104a41e4106542c0050448c881d60f0f00400806010021640702e56 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 121673983 1250 121672733 121672739
    0x3070201060f030506070e011101020d090302210316020f0a0303090507060302030906150111010c03090b1501020303071103300a020405150c1507110f072103110d090807 74
    0x2c001100140001001d40e0454000620500d01c50321000f01420b405140100903058088000c908a1707011000d88404a034a401011042c0f41d01003018000440c051040c0940090304d02018140074000945003220424200800703600b207502c20800a80281400310035540c121100c0d02c1d0103002056001c10848960180200018140d402803080e02c0c80703207446401400c0c443d6a8401041203070f00c4602d080d60b045c00026003411080041c00d22980030800c4460310000340e00078860030140001840101181e006810001d4401401d9a0200c242e9801c85501d003054502001445211401d6006160fa5a040b154040100b1030241a8144110700c1042c0c000c0a4030f542500c071000380106038400d5015aa0304858400008007601c02c0c003000400e11410f07030348250b0710390300014107201c441004207841090008650031905001408140801200030202d4002071000b1890220f030064400c000b204082e0070043c400300800e0605000d002082d4018070090199100710700c01013806814400240114081c500c01d118000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 121675233 1250 121673983 121673999
    0xe18010207020a0501030e12030a0c1805010f0c03030b030a0b04020f180114030106080d0c031706090a02030a1b110d0c050a0b04080d02070c2d090b06041a0307020106 73
    0x803182079070003904880c0e00c503003810019005845620300c0d044c10340c45410805507408072140041c41c050071100c80007240c1c1c500b50344001801c40c40c880c2e407420401200c640c010010743e030f04040e4102108406041040c81034000d820290b0041c0380c01c130003103234142c016442c500041103284000c90b445140300321445a00c0301150307010700140c940c03500b00031149600d4401c014000c00c4042480f0254003000200041100e5440b507289500303019081107280081540c501407c0101358110035071944070f071152030b90458546003140004085000143c82582c0e41640007020500741c480c11b400040604c81c1c0c0b805d40b14040080c03014010059805103104841901400456400d018401c0c02c000307000607000002003030304441e00d485402c0f100f403020b0012100c1d4130040101d5410b120040c00a0000180130b030101040c12450a1003007081c180100100b42c00003200f00042c2030009441502e00c5058550103000010300c000d80d03801041d418481c54003c3d514601c819102000700054220045102c0c00c2e02e5402802256565031032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 121676483 1250 121675233 121675237
    0x30a05130804062a121211130e06191503110c060105090a0e0312090106031e06140601021b06130e090705010c0305160c0308030712110315090901150e180102 69
    0x700174159415a01e8000f60540300750b10610782e010a65000250040030842400b074154004584819850360f40001040900d50307100810394804c03015181d90921140d20300c3da450300924580180802d04c1c000e82c4200066910a6000074640541c0308081642c0b9a801d4610554407903091041c1e510986410002038a81e50242c007c01891500c0d110056080110a070000c0900e6800200326140070340d81d540001011415110040d0450044000c407400c0c100b80d01e09000d0113a84400342d850481c180100144600d9907400a204015400b0704424541526090000142c039842846200300185050300000f142c100720000e031807070054034400211078a0a985100650700074088560140100e9014007403114040c5054510066641c86402c00151042d2240d50707804090300265000c1000901110040005041511801c03140100706a0050306614006852042075044090881e000c0c1004801003101000d00350001e182c000070349401340d0121910380680b1202c561049560549502e1440110b814104040c07007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 121677733 1250 121676483 121676567
    0x3170a1806110c03030c0c1c0c0f030c051606110105041101050d060317090102010c0c080904020a170405031e04050901031118072c06030a0513080406 66
    0x460008011501c40c440100007403503001d481c2c620100b10203004082c040c40114072a0b0303419040240c94600c007003021403403d08046032104c8409017020f10054041d0300800301c48510b9601403101540030301031346012a1851152600142144613580342c00d07640d5884c454811066403480d50312140a181c0b0148541d00340d420648002d89040c84003030142810f035200307000501d07407003034242c2c400305805075281d45020210703160300f170900261100131503400115030b820301901141c0200c030710b04003454207242e48a41c02c0502c19031144501c03882d40040c02010300c034011030300c0140304a4495200f83c520725150901c251a40e202c80d4643d8036203008841c0c2981b000c01c01c2820344068503005088038a003a829559070314894043d140314150f125450b014440050f244c2d050505101e2280d60346d41c9020006040800c1e810303099407000241c9144080300310705d880c03034403403105583e031003150b210000c1240d0b100d9101d01064201c5026024100c008000f8020801c03540051848004040e05491455805080140349007a001c401c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 121678983 1250 121677733 121677761
    0x3010912020f0a1101080c040b0706050103020f06090a050112200a180e010501030908070803180705030a020d0f0309080304060f020c060415030509190609020a0b030c030a05040c0902040303170a 85
    0x20108613601d5108142d020741c402c10380c6070000c0c81c0c907888240d0b5112980000c801120710f90389550043c02141011046003c086000307075503c0b824500d801000488c4561075005d8030f8100b101107400c1070800221500500d81d9200105c100781c1c0c0d150040344801c0034940c00190300b9004a081d84894000c1284465405401c9941355004061799900b0080114094511a0401d480c002d400340802d80c00f05002c8030041d40920325852843c1d01d00c0d070740810602d0800c0f1159000c5d501ca034002a02c0c0c00056191000b80045e0264400c1000c11021168941583c0d4001c468101200a02c00810082212500501d814029a105801321496050400c080041074031881c0034190742d000c01d04840d0341c0c030b0500940045030031600785000c1d51500da01602e18664488555001900d205403918a010306604068440c02c000d400d061440b0303803442c40c0030f0b404840184406410890703800c0d0b85100140510100035000c1d005480c890005644c1e45589040040401c0d40003102d82640642c001c010540a10040c031a072151801a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 121680233 1250 121678983 121679003
    0x40210051e030702120a08060a060207080703020103180503030c0c3703020c04050901061a0f040e0a0906020a11010509070f1e090c031b030b03070504020f0903010912020f0a 76
    0xc00c00c0c280450b0006812401940302d903044d02400c0007403900281460103002c2d030340c2a080380b074280c081010f000030036407180c01550014036040c4100d900210340e40c0d0580c0c1c1c081c05c004c9040700c03000ca0280c501c5480c0c0b4002800b1340c0404000d0140f0300c0d10290050880003a24012a14120740703022401d0103001d0041c0941038441081e400f09542d84c41012a200d00c02ca0082c0151340c0c200745d11201003401c0d10750403501d4141030f075916641402001d060b8044201c0e041c0718007020a09020394001d04a541c0d01c510b0194610050b03c90000031116680e5411002c04242d01030b0b425919103c40c450098840b024086201c0302550070040011031440c00010036004640c80c000380f000c1c0700d61a1005d1142c0310590641c203800740040d02200400e6240c980d003e1045c0a032a0f913030b80016644c1d400d0b0940450101d22043c071030100f50900404c036841b42d0b00007900e0000d0350000c8a0043e56441803107c400304a1084d00c6200b0380650901a010080c000d2082c00490560074680130346166140091009481d41c005000c01004a000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 121681483 1250 121680233 121680277
    0x10509010e0906070804030e18061009050f060702031204030b1006050a080a0b0126040309050307030305040303030f0221012108070b0907030b040606090b0d0201020604030c020f0d050604021005 85
    0x300c5c0c0a001e0708580681040d40300d61042e003012441032040840c24508044a400920440b03003070010300305074816070340d28180180c90300b80000030350088141c030880d80c446d02000c6483e8040d980d041c0165400a803d0700000c84d0384070381d2850301e12000366045600e20320301381149500086080c0554100c480c00c0b5072580d2103005696440100c1e500609156400e00e0410180b51548214144a10340c804001d548070004500146450300d07005024440035080309000e03402c6450b0400c0000c0c0c1220598007039a5041c1030100301c0380840102c02000303000d42442000e034000d1819510245d0100150258103035801d1808203049001007100c0c030700ca070340009140100341240c104007040201c1e140902c080d800003200019142829620b4030380c01e20590342603405480d000c0c2c0d145400c01c4207881138400d00300000016580c2100700d104980020351602c40041000d024002c0072480c00701155034003001c82c02c3d03a240c01481c007030040245090030340e40c0d1007084808900031b003215001c811150703005a094841c6144414085804511 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 121682733 1250 121681483 121681487
    0x4050105090a090c0801090b04050715050a05070303020f0f0a030c05031b0d060b1b07050f130c02010e0d050403030215040209070f050c030406032301080d0f0e1008010509010e090607 80
    0x3d0b440058030360828811002c1202102030040c00340e403501992016071141081d06040d0b0910196500105c062511080c903454065000401d403804103030142040e9442d50003d08058000e84110080da0b010314000042d50f142c1e805003207024282d11852a501000050301c41d940c01e40b140d100c10f440c1c1c01c01c01d480c03a04100342d2401445000300329641c140302c4041890343d41d650180c1101d80240c409843c044900614480b46168100b04210007000111b0790300f249043d1400114400d0304524409045040d02c400c0b801d04514001d42040300c88030748031001c455500300310400052482d00300e400104c0c018014655440c00110300005500d00a6800500f0b07540f01d03403985a802d0b030b134070000000d0403420b2090900c40420042010700180004085a45021981132210442801c01101120000c10f48400380e00042c08961800070300c016824016081048035018524815202c112000c3e00360703a070001030a00842c1d48168024801412a032003590100b8041c0d1300c602e01845102d104403143c0d00c00c1e80c403a40010314114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 121683983 1250 121682733 121682741
    0x3060103150c21020705031306110d0207051e04140108030a0908061e0702100501120b0601030911010305070e0d1202210702010c140f1507020a0b010e060a15021b04050105090a 77
    0x601c244200c0340341004020030400c04604a40c0044007107290400103042b103403414840e010a10782c0a1005c5c00b501410440003d07612803200104d20030f880c0c1040545201e9482e00d50008100d422200d103440400d6035900703a0195264040703c0c1e0240000c00f02d80002032101c04c006481c40c01b540a40481406015090700714448901c0001e10000c00c40c4a141d407005503c900a1007013034080e1160422100444c0707841d062050580002421107810146091030050203d03ca0303cac800c49140300240390124480e2503000c801ca512004442520ba0b22007440180c0c9801c00000a103100041c40715a000d0310040700700646017079510701050110441360501000001c00542c41b40c00c8100b841440380e01409240c2118035200c51815141c140e10117080e901100c054100300d00e10000165220b1024170041c084a11150795080d0444c0c01031158421418411002c550155142c0b13030310002070000014900900340300302030000e5440400552140c07010090a00501c4e0904041c02181e042c0c4102a001203a40d0301c407107907003d00030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 121685233 1250 121683983 121683997
    0x60b04120606121b0b0f1209100c0c141615030f060603020306151908040515070c0b0109060e06010e13060b0a090b0406020706110c03060103150c2102 66
    0x76596494011800084008072190494041d0200c840500a0403420380e102240719000007108070700038054041c5040d482c3c4200d598020103490303248042d031200007086103460300e1482251000b505000516001c160b012012021050142d400c2c1d811039100010703603030349a1303000581080c03004076a00003e0001c001d2003544030040049078a400941c03400e00e0385035001211083d82040001980001c1800001e151007a442c903c500c040c40a021300c2c1003032140107081c0302c5010082c03200c01d202c2c20701c00050078010144030101d5042191102d55216240591004000230420307582160361850000001c81c0c000b54910a0300180c511020511030540c0740c0790010b603608020003100340c0d40560b060720240f41c3c60003580110301c0140040d802d0203803516820342020380500495040032010034418003081000302c2d8001004011201c0c141482c01001c4a41c291890811034500d10141d00b61190700f00002c00c000d0700e0380c0e54903406503840c0b80c10007000b01009022522064000c40c0440c03050200104007001482c0e541c010518 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 121686483 1250 121685233 121685243
    0xf060d0c0f060507140105010f290c1e010506130504020f04060311040b030309132f07031202031005130e0f01020403020109120510050604021b011e060b0412 69
    0x206565004030074210580c0b0303040309000030004100340040203500710034540f810505400030300c1076604042d914400c2210901c1110b91988072200550413940079031065004a4282d0718080f56101c145000490f035401c8645c070784800b8850011407480c00001c061245a0080708005c0896004050341080c107001b61801070010380c0d0200c00440c1c00a410b42c1e603072264500651003800442802c7c50500b04010403105180a1540203030001c00243c100350341ca040f205080d02040000005560031500c40742c40300c00c3c81c03169003c500a440c4000c580540c006280280520520a0752a020016002c0a41d68141c1c0001e44402c0321801b04c017202031089140610710001400c108440004a003200c00345204d2501c0454112454541d42c001418010f40d40d0140350500502042c1c035640340b0152950351403642c0c9a01d4078124060b09030741c51004c04d9042d60356804030f40d41c4d038440b6844890b814900303100807402002c04280540301c2e081440e54500001601d03010707880072500c0c4c0700041428180380000303c3e40780d0140500e0843d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 121687733 1250 121686483 121686503
    0xc02060702011b0302010902040506030a030507140c0a08010b0a05040618050702100906060e0a060e0115091502060a05010e0603030702130605030d02030a0f051206011b020411210f060d 81
    0x42c461002c11a8034110344c0030341c0c0086034450341401480100c2e000030700528000d410400010340481c3e040400c035024903034802280c99152610800300c500b052844007211354014940c000019001c03005400c19007603048100d4503070702c0c00c80c0d98400b04021200035100354550600f0011600707484001591006130b000100740141d40040d5008000d0008848a094040340c290395100024040801c203440526448819000c08002c03075810b1900e845601ca0b81440f07841d848450a0900c00e520307601c200111402854560008031080c1810304001c0e4650f60120f0b40380021615060000030054014030600c0e000310805009945440c0c056024007640000c0d136031080a4180d164040090540c5041041c03020314020f0741c0c007540d16030074101c50091524001e034119904000341171101002e04107804140340e800900c02d0a140031050400312107000b4800c484031004e503010385030001807203144804c18002e00f10029088100f0041c0c040342550703604044070548456a03421140000980182030401c41c00b11504d0003420808 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 121688983 1250 121687733 121687757
    0xe2403060f120307060f02030f1305030403080d1e14070c0206070206030a140a0507020c280609060e0603130803090f03040909030912110402182107050a060c0206070201 74
    0x30410040c000a000e400e80c000501c941c144049442207603410042c211041d460b41c142180c1c9d2440c40e140191100c9400c041c5540c0c41401c00c4010030442c0c00540c1c0c0a017a0b01d0f03d0302a44524240241102c2d003805040925141c0c00588454407881510807158044118035140d481d813200031260070b2a403000880e0003c1c0c003000b00b03002683d28800a58880c60003840e011403110b102a40c400300509001e004100b040b070504051054151b00400d1004800f00160f40380b40807240c1c000c0da10042c90204007108105d602c40042c020500c0c0c0e0b845543c00b0190758094641920300c001250070b02a4a00c03048030004141c4c1c050384580e10000750030b03000031a005030009045501c803510301d8030103604550060340034103101903640200c1010581c004100c44000c2c000003001c1c800c2d80750141c90ba904101440cd52141c821580052401108007001c10300b00c614800180019061400c4120000d4529041140c4850140b03e800d400103007170301d01441c017441518107503501d01d18082d001c4d90030300c041c07500111022414071030102484 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 121690233 1250 121688983 121688989
    0x30a081303150e070b04030c0b0306060f0a030501060e01020d05031305030c0d02070303030f060b1801200a150b0114130504110d0c080c09011b080304050d0e2403060f 73
    0x9141050702c2c5000080341c1442410241c5002c042e5801a00509018030080002c903026411000c115000c0303912503a0707aa641d40000410320300c15400d080d0400c080c003048000200b43c0c10350049040c0c6007103458402004500c4401a603a43d0210440040002ca040000070844402841140d0001e4814000c4900740705110318890704101030200d2100069000d180204181a898001c0410341d00c0039400420405082c441004458480ea08140e100d8040e000c0400b0300d01d910900b040b160495062801000b1115101290380c0c0318507030484c007610f00c2e06c14250a525416810321034440201c2058441c5110444010081d6500d5004101d0003052602c0c11240007c903a00c46001300000c0107491003035240c0d03d019100403034045a100d05140010041c03407204100800c003e030000c81c1c10000302401c2503c00e9942001e80301400c51003424005241d40404018402000f00004500f8202c643d9916038030b01440c8108280107480c00c1d2102242d9030754004440c0500c400c00da0307100440d08980b02a0407890080110008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 121691483 1250 121690233 121690253
    0x21503131b050a0b0c010f090804050402211303121505152104051b100e04020d02070503031006170403030507270503010b010305060f1011010504030806011409030a081303 75
    0x803413003030800001019141498203104182e4001650001084507640035103c0c403055000320700170103004640c0022810035040f402804071400e040e1140760317060145441c443e000e9182c1000942200803500000751408010348501503440c4002466440200a510b070104000c05c1e0f00d0444010400b255080000c05c81940840410a41540340d9446680241c00c040c40c0043c0b0f0b1441c01c001c0d40b42030780013811032000e00d82d4400d42001c104240f1480c0a451a1035480c000800a10860848001c034502c000b4100080040201c051481000f9a5218405d500e03078801c4c041e90031607200b500d0031148814500006000034041d0707008a070070201e9486c02814a00f8440032407002548050301048100c8020901002140341c04d008001e901003007840c040c081800c040c0c001c520540a0002c0044c400d4511a0301101c50f03510400071604001080030090040d42014107000e055044203070382150005503070703644200c0d01046100440b0315040b0040d004108511854580e440c1c1a042080904641c0c1d03c844400400708000c044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 121692733 1250 121691483 121691489
    0x6150a08010609060c05060105060c0c0a09090c0b040e040609140607021c02030f1e09060301091406150702010c021207090501080c09130b130f05010504021503131b050a 74
    0x803200d149504101c2c01802100361a0310603010000c090034070b0800140c011490a046545c140e139156110b40011a0b00e07402c00d5003101c440741d007104400c40001501c10703003904100c0d50381d800741201181d17494684035251103d00c5a40a0445070f541c20602013400102c50f0303404402520302031101781c0c080a0700e5416050a040c800d941000040c1d000181032010500300402c2401d11042c80d0000710b180c40341e50b00c4160550b0050244d6050107031500403071107a1805022046a180e01c40051410740e4940c0c41b140e403c03008081e11148483c02c40041e0300040c9140c2800c0004060803106d00c1607aa0420322070b0360045941030400c03181240c0143d098551880740c2202003102402405071400040ad856050600203480c04420100b1140304200e81c0d414058a189035484c2c801c2d0751a00064001c0c10782e80c0710030202c00306400e4604000c1040f8011800001801810344c0038901543c800c550042d0320200416180c1d0860001390303489100114045241000142200085682c1041e1607200c45401c40d61500091001504c5074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 121693983 1250 121692733 121692737
    0x30207061b030c02030a0212090307030602030f07030b0901061209020f0901270c08070c061512060f050c030a020c120c010b1203040810020903010b0339060702010806150a 75
    0x401541e6039405004038014400148015401c02c0c08000703000b980d400f0100705000c0b1035100054079040548040c80341070050b580203101035583c0e0500d40a040300d880313022114480003074601810000c591508000d441e04070384a956548007a030326000a660020b020500049078001ca10006545003926403024642c000c2444800c44102d02344910404901069030b0000000128a0811f81e148c00c6a0400310300c5800c0504c629084122200341c1c1382002c000e001200c01e81901c0d080c0f80100062414264020000303081c800d8a062082908507404802620000e40f62096117100502c00900381c1509940940f90a0b8070110481e0519404805c104140b42d00030352288015944480c0380303941d1420300381c0903011807840100c02146494a0304c02550b484d0071100c4103034200c0c180c002814907400d540035001002055401015500d02e00074080750449024101d800e0010084c13401e4200103801c1800c5074000100120140c030842c5046a943e004454000b0001d108640c88a40007070f1055402030307900040e000b035120a03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 121695233 1250 121693983 121694021
    0x8063c040c17010204120f050f0a050a140d080a0e0709050406050115050c0d1b0b0a1406010c02010e040b011b0b010303170c07020909330a0207020108010308090103020706 75
    0x2121108415042c1e1402d540f40e00400042121503100004807031495000304400f00c042e101031400e40d0526032104441000c07842190b00728428000c0100341c0114440c46001894400f4014082040d110000e02026001140c07550002030510120741e0440400310746248107844105481d41c500b00c1c1110300584083e070300c4650300d000502c45032441e80e450040c80c5440e420a58140900f543c2d00ca6a01c1e40c056090208022074102204030041d132810344c0248040e0301446200040c07602d0340b6000001c01000551078028000e40011034115405401c62002682e0180c0d1808011071103c0f0030b01025100e061002410841500702c45503038101540e003400350507445400c0b00085075246040003421410801c00178261609400240411145440b0885e00c0f407640c107881c0c9006960301d009640b400d10f202e9001d00240403009443c003141071000300c1d41c0900d00d02e0b0300494030b1b4180c0d15010031007401c07806018030090200303003260f005001141101018180b00441454090300e083c51030350780c4c1e0301030300d10303041391004100d41c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 121696483 1250 121695233 121695239
    0x408010608100f02070b15030102090d0f030906081512070803130603050c030f0a090303110a0e01020114070f050c0111070b0609060411090f011e0905030708063c040c 73
    0x80c01010300054083c0c0040d400d0a0580d100c0300d240040c068003d001d0984110307c601d4807030300c1c20b4040d9182d1020081ca4003171000340302c1c28034443c01f00d0103400440c0092800c8101260036406081c0303207401040b06083e19951400c0100600c0000e50540903110700b18410031000246450040000b000304200c03048158112900c1c10801800303450b8003510048000005108004081188100342540014142004038003075516050030f80040030a03800e00d4050000001d0f1990a10fa04201454003160081e03008100700721602c0f5003541d10203c05d4550348001a503004000c000c0b188118040c1c0380c28801000005068514410850700943c0103070b43c1200c00140700001c014449c41e003801d04541c0840c043d01c00780001c0e5582c0c400740510780319481d8643c3c8902c000620608150340b0501402c0c6140d02800141846001051006480840e0354070405100748a071020200e0082004502c0e280500c85117185200180d441410400c90790f40c054000c1c080c05403600a641d81003060500810340518010f86000c203000381 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 121697733 1250 121696483 121696513
    0x90604030516031a0606070f0218010306020405030d0206090a02060304030908031909090e0703061509050f010305010b06180d030e090403080a0c09030b0c0d0b03030d05010509070c050c150408010608 87
    0x40b407034684515104007403041001d04d4a0307040480d0f00065001280100d204d070719100080700581c4202b503a030055110780d4008800c01c03225030b00410036104124200c450004c40c14030200d82d1400122801291364000f1034061005003001c0001e150014420704018100a403900b072070902c0d640000b00ba00460102d18150303040c4840e004071109010301078007031060114000d4903d002c0c2e90f0740c0c01480300401c019619990261144074000c06d1201401c01080144854105807105211241083c081074441e9480c094901c60645816000c82c0d8100301c082407001808800c650400401462808096061001c4401c20480f00d5480500542c071462194840c0103103410507603030784021216044401c00a0040514062001c10290309405912085803100a6a03404002d08080701a000132250030f90184404a042030440081d50041c0703050300c83c01d543d0f451080ea11141d048483e403101a801070069042400440d81c5428069911000d41101600d0180362669031400e103421550268800241074108484040080c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 121698983 1250 121697733 121697753
    0x10020d0e010c020d02220e030c1605010c1202010f0c11070e07090e0c130b0406030c090518360c0a030308012c070e01110a030207090209060403051603 66
    0x190003842d08034550a00e960116048524010002e4410550f0300c500c0d200f0309502054441e10f0b039030a0300c014005c6005c120380490341c035080301c10802418091844134151003890110641c0440e50b059481840b40c841907110014600740d040e2154085548403032202ca4203942900500f41c0d1500d50340d03500c064504a040c001410305080381c0003407a0426455040c012130561000026040c0c5004001c90501c41e01d40b003206c1841e13803007042e4217958041d040e00000512111a500600101c508075102880f12080b04441100e508529010312503000d0003034150b17205002c50f07400c4c2031680122034a00703a0009587e1035080b080780b039042e9429080ba591142d0749080c1d40c1e420500540c1c41c3c1b030100340c2d941c0020342e0a656001c0c0c184031050195030311242c038020568801d24880c0d03071004180300060003440942c1c1442c402c0200071078580048a8003240c280204a0340443c00003a80d20b0180d901513002e054003500b420020350180d446291015030080050201101060007808440c01e54043c407102e80c00440e2640c40c0c109000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 121700233 1250 121698983 121699007
    0x1b050102040b0304110301050103080d020a09030b07050a08011a070b0403210609140405031207090906060509090c12150a08100e060c030403090303122901020c0a060905060c0c10020d 80
    0xe1f0f4140700c0100001100b00058039000b8941721400350703c3c0c0d40511800c69025001da4400707402042544107104502d82c024009104c0c00304c4c0d6994000c0c060380c0354400c100c100100d03080c00c0862850108a403201180860070b4480e0010306c64a881115001c1d241400096418080c500080e5541d03a07107810040f00d645441200848000d075203e002a40c80c00c0c2e02c4550300c2c0d000d6122070300804a000d40015030036510031482c400181c41030244c10030045441e8400142070742c00290183e070052903c10003282c0601d501006560100d0340b4511103600b0365070b407481d0070600c62901c1000150440021400400c4441c41440030102042c10765800151002c603000300285403c102900900ca824803c01c1031001203907105a817013003501c0c2c040c1003641d102c6208201e0740000b4801c4042426800340c1802a070002c40c581c024141e20011026402c881c03402208030200030f2129101c0c0f090b08081000c1c520100402c2c10046d0160107001007100548044000d14004148d90f0b0202d8800f440058010b140c0711111a50407800642107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 121701483 1250 121700233 121700239
    0x306080c010e01050d02030c0403020612010e010605041214010b0a0306020306041107050616020a0b0702010b100302030c090f0409060507020618011b0c140d2c0607031b050102040b030411 82
    0x10b5080880003918900c690a40040745a8000001540a46103201100c3c001e5501a121554914544c010f507840710801707000740717031000c00300700000504103106805860959911940a00302c000c0300d980c4d040c0094400000c0320149548980700200b1960b15160841e006500400000d690f0b03151a208100071102e800c0314a52007080d0600645001c0742002070710a0744201c5414644054900361202640b604180210060080301c0310700400c20040da06411031074038044107803080589030150400940a80c04221500c016800050202d5a000d28000400410200010744009100c5800340c81d502c0035100b044541002507407040e000d00c03104e030303902c121010305000201000300100050000240342604505c2203150402507010521800d1100402038481c1e60047c0c4021510070740401c0502030812052051810312881201e00081c010f68a151120410392600038100791a0015554090f81d01c8045805c00d02d600100d0b00d07602d800000d80920081c00501130b05120940c89140a00e40790850090089120340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 121702733 1250 121701483 121701497
    0x6032f0907021207030905060706020c06070c0b0601030b01050f070302030a12090f0f030509040f051609030c0e07020f120315030f0a030806030c0904060207110d030210020d1b0306080c01 82
    0x5039031030b400300b4141400f8811032440703039903981d40381821600e1003401e4001c113a1004002925508101855008002c940302060030b07030751142c0e10190309550480c502034000d011084132400003800ea6100354840900c010050404a01301590380d840300c0115006540210f026030303c00100c19480310f4101c13110407044401c80c00188212120340d40c030808100c840c0c2c14020b0801c40d0095440042500030b40c19182d91501c0035004001442c0e0010300702016000a0340c0741c0a078900d451000501440c4640700217400c7d20b03000014100003501c0c0c100014181da000501d44000c41c003c00c4d044180d640000e101c0000800c441108050b00d82c01c00c4e9850210340b80d005000301380300b6408102ea08092034004906510740c6134041c14501c26035910280403070300740401c4010865108600208002c10403203190b002d003081034041c07100c02d610a401d240074131418491b022409805039209803c41d00c02d43c84941c0081c10740307068560b80032070840044281c40b01040030415500021030780700d80e0140181c0c40100842c004008003487c04c84 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 121703983 1250 121702733 121702741
    0x11d0a02031501030f0813030204021305011805032a18010608010b030103030f08060103020c03070b01090605030307020604030605060d02040903020f0d0203030c1b03070c030b010e0708060f090a06032f09 89
    0x14506140b45c090042880c0d0010420324890005010a90019a00644150765170820701418000508003401800c0c041506410316408405503400a00b00340c4601400808207004810001d100748070800842004044051482041d103131140e80880b40c3d064260344e102c1c6030b19410000040c00c0b0101c140c0080000103824001040030a900501141c078860071410b180080d0b403138180c01200079200e180e074000c26902c000203d0741c04004e0b4a900c114122005514108060740d180c1c01095220b21036140d0113984010203110500101301c50703500c030fa500008010401d21502c10542e0214042c2d4983c1102540981c004203055000b0b40028006101e0304165440034600d145000031600c5080e0145d60200701e144848a00b208a0041c9c040003100d41c0b407078121002c1e102066581c50201010b07202400f52040c121072080101d0f07003c90041c0c00403801400010044440110110103026480300300410451256032102d6000000c0ba84c212240f440c09800c0c5650b80d40c0f01c442d2101c4014030000103540d29809111910200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 121705233 1250 121703983 121703993
    0x901110702010305060a082a030106060206010b030a0626060f0609160c060f0b15030702030301060e030a020a060e1c0c1203110303010906030212160b0309011d0a0203150103 76
    0xc46080e503090800068030f84030311012501c080c4281d00320740024442c0f603175010b84403103407400403800d00090141c040003071508001c14182a65642c0c82403002681c000390040c400009001c01440d40003c089400003103003a42c0308040d0031544004e048500c40d1406000300007106003000e01c40c559200f40380d96810900c0342041004519289001080c00f90036400c4140e40b804200d10501002e509141c20540500640c020706802e20300910801a8440c4502641c007500c02d51a28620140c80c8600320b030f5000395003980c0c6890342c11344424028400503a0306000c3c1e41000c5005a03900d4007100068092541d84500089201c802d200c08002885d0078042c469021b02d94900c00188003501e503e041e0b503521209981002d9952a0944032080f510003460407502000c00085049243d0354007180481c0c0c02200d44e4407000c0f101032012030f113034070314440303a2071640308c5002091004441c01d0300115007010710703807000207038400c601800c0c250020b0303010b2a1015a5045420084d040d485c0800c034868444d8900c4203c10615403542c0e40e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 121706483 1250 121705233 121705237
    0xd06050601030207060626120904110409020705060709050a0503060a0c0513140103050a0203060d03030c090b04030809090603070b03180c0a0b1e030606040501031517070e090111 78
    0x140519114000120103074800d40684220350380c04030080c052152501d50781e03801a07600d000303c403040111044501c1c0304078200060340400c0c0d11101496514016603003080c40040d02000051151034a01007000050496044c0f0007000c00d1400390014000764103241c1d000500102c6a941b00c00d10428004200b802140d902290641e0060040840081c8400130008161141e008014500d20b4508601c0d400040c54024800ea1781080e2400340da0422043d944e0050101c100e0000340c50003500188502e042c280002e0003135004c00b0611900d801d280d02055981c01000d1043d61007900200e4402d007022401d00c0550030070100030394010308200e015041480c02c04064501601000305a02140d180e903c51a64070503505100c2038280c1c980c0a407038001c1c0640c030350424840b99031003510140c0c000c44001c000c0b80c20f00c1d180e01d015680034800090400e46070a14200044028003900c0002c512881d40c840000210f903101030010314000302055010b004403901d0000b0391183c18130004d2400700b841c2d0501d42c9060304110002c007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 121707733 1250 121706483 121706509
    0x3090c03011116060b0d030c0302010509190803070c0c0801090611070302030f0d0609021908250c030509090901141b070807050109050105090c0406051804060b120d0806041a 76
    0x4400c15540b4103c4c1440b070090000c4407880c0b40c00000090a40042c181d03c00d100501c100c3c0680c000340100c0c7c07204400140d0382c8951504081400f52040e503c0400a07400c10300654001c00d2610704102000420b03211448a68002d91005c42141e646900c05001c0100310f0003007c916411402c469400d04000da14069103900c00c2da101c002c0790340d00010701711400b02c8469001c1c0c0d010b00040c050440d100c00c4100c51076000c80c29a1031642d0040f8207030fa000034140f0368000c20a40001250b0b502d0210600a442500340c40341d500c4c5500880c00d101080c488000c25895818100c0d100d03400e40800800d06c060701c2800306c6508400501290301640b403480c0034015a45001045a2200703070f01656499450401d42000c3c2c0c0181008800104603500b00814804008000185104109800c80301000340c0b40e920010819010308000d0b5018810411400003004180f5a82c8110700c0d0310b9001c2c02d00d15580b1200c0d02c01908000f640c000180100b03600100b03121450610b44107415070852041c107901c26405000d40000d0902c00148 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 121708983 1250 121707733 121707757
    0xb04120807060509100e01091a0702010f05040f26160c030b040c030519031d010c05030a05042907020910170102071a0f1506090604090203090c030111 66
    0x160141040001640c2125003240d00400b0801160034904105a01c403140718144019443c10718405080800040c89001040b03a40704000710303800070781161070308040000180750390195540c0700448500681c0300d0044511a80c03145110304d11015003441e184086658a03565103020754420040e11300c2a58091045651121001ca010801040140341840400781c05400081ca070031910028003041040a022160035248a20306850f0b40020203403902c4142d070200300000c0d00080038640c404e986009135421000c2e00b8030061404840c543c0540e103490346150710a80c40c02d4009100042d0400207030800240711901d5880c00c5011369101d0031134080c603a0842c003070544041d200d2a0550046003403001d0300031042d0020f01a0425070325400c1540d6000c2c9000350400801a500038011a42c500d50700e4030290781c040d11507480c812208209880b4494101100100c2e110b106070400c82c1040000d40c0d03551200041c10040501c1d2201603680d1034141c03005405c0140400e070040c0240e04111142e85031020310300541d10205061 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 121710233 1250 121708983 121709009
    0xe04020301021314030c0102060603070501030902150301030305030405010e0106061205071107140117040f12030b09191a09191107030c0b071431141005040b04 70
    0x2400024020720074007031070002004640d0400182c002c494600483c510008605030b030307101c8881d03e00590701c454007240c880350315421041080c0701c551b00039070003010540e001521f008026500b000141500303610a8105801240f804010001005403d0041020010625000b0301000e403800c0c2000e040c03040880090042540c0780c0c2e0021722124803520848000c0006c0703030100e84c15155146500c441c00301a074002d20340020256900302c4401110b2000c050700547e400b100c1d0350141482512541a0000c00113064420035071104104001d969803010034900955520b60764220f0045003034051401c89603407075080200303c40303c01c08041c581c1da0f80c0c1c00c50b15480440307801e0700c600da079a0240301c02004203403400c1c2620104d10080789080c1455404402458854403030904030031251100703c0180c03403064050292021911040103071640300034000140303075a444d00309000301d001002825040319194007141c010785918074121340c0321170452910681d14240c1540307600f0a6441c050621070040c810b41310300d00400c2034030215 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 121711483 1250 121710233 121710241
    0x150403030c0b0a020c01240902031b0c240604140402010e060307020c0306040515091207030e0109090f090c0b0c0601210803070806040605010e1c02040e0d090509100e010e 75
    0x1158046617842c00c5218020480903071b207100a4007212580d00a00c0c03440c00045c5034080b4904405108030703030156000d0047d45200f01007200c1c403414035034002c00032149203000b01003540c1c0c03a140d100307103d0300e034a840414981001460200240030840300030442c4454150f0f004010700c8050b0b44c01c00140003e40f1000d03210240d490b620010241c0c07620700240000307609441954200001c0c42000f1403420b68a240051840c41251202c420455548408028603444a40c0401c030510000c1c1c0581c0c18007001007410305140482076170706d81003201211082001c044445890300d039200c040000304011b8901600c4400c00c1903041944020075940e0b03402c81405400034483c0306140d0345002101c002c1070f16880590100004d0360340d00e04000020149101641c0040c062410b11f4400310b190f6010350f03070038680118060103800c0d40d02803003544c03454100003490003aa0850b17545e00e11416018001d00c240740342c03011140c8a406190f03280005102050344010203424081d1130640061040c044c02c091004d04446048080484a4039 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 121712733 1250 121711483 121711501
    0x6191404060b0307080f0309030d0e010f08090c060304240c09050f040f02070804061806050f03070908030408030c12040f03022215080d0906051611090405030702150403030c0b 77
    0x240c141c020020b06d00c81c42c1c000c0035001d0700010050081000a8041d201d01780700303c80c029100c1552055625010850002c80d000d0781d28810b4400c103901c5200301d02140e86601c200c4000c981c86500943c0c0c00d6404070300c1c10081d00301c4109150500800014030420401080403000c80080115207940903040c8246c02c503a0061403243d0740e5401c50014202001130440d552030341c0e441c010125522602c03422003c0f072501090211104011407220085400c16210704e0715185190710004c140d617100030700076400c0c4400200e010840e140d0820141c4080c0c03c003180215500d003880108207151a4485400394480c51040205002031815420031400f16a4151400f00c440054038174141c01541b150045800428500b6690984075a94217156000311100c8c2c0c015a1070000c150941159590140d01406010547c10004010510306074400510014020007000840c3d01d00e40e80014482007007074500341e505a00110713000c808e5281c1501140802c002c921320407460311703295070340c040c000c0d08071080701400c84079107400001e4140d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 121713983 1250 121712733 121712743
    0x9090303090b0a09050d0201020c030a050a110601060201150503010506030c01030b0102071d0106090501051306080c04080601090501061b0309050409020f040509070e0633190206191404060b03 84
    0x20307844402c0720310038640500840c0042c0311607001520720384101d9581d040e0950040c030855400d40c03840c5001d545014807454040d103040d4040e813500001c0052001c405e0030450800c0c4100340c080c0505134000b140d4425107040e00c00984060b504007520076458007080c802c65542c0060383d002d01c2c80003820046005486100140c0c20101d4980c062405035030009020008160b4030750a090503101c2c51b4039403081854650f401141c2e42c0c0102680204100341010b010301c0031a0040448651190040c2420b070b24150312002220300f000402e82c030180700103441e2801400711139042091600c65544560070945141c0c4161030041a40d00d040c82030b03900640e503514440c4150b4641c00d40542d0700050141003403001c2d042100f40355a030380b0310030311808950085104c08140c4074580b00c2120580d08019002c681040c070442d41500810000ca01c140c100b0803801007010051003d040385000d054020746401811039864010100e045464082081d601901c0c035003417003c82c0010491143d107401c6500100001005060000420b20305 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 121715233 1250 121713983 121714001
    0x90901060b04031103061302062a0f0303090705061908070c080c0a11150f1c050f0709060302072109030618060b0603010b07020d0302010207170d0c0908060109090303 73
    0x14005408402e02c486400044109481038088032500d44d02ca500c000700b550b110b210020749c044030403c480449509400b1020145141405c0e0303550103038403403007880c900e49002110001100d41020003040905103091000700c005060540d100c40c035201100c448940358400d1000346c9402d004228002c5980350303226100310111944d018404075500d028000701c80703503200351403170044800d8519508910207501307080c00010311408071042c40d00d081c950480380d01c1d0543d8001c0b200c01c1000050000103d810059035000e018040d40030100007004a050101000b4213256144d00b201007814010805600000c080c801682e103800d112500c22043d1304100c003021281d00c031075588050100c0d0304003d507140307110010800d0108000c1c441e034400c0126a055405020b202e01003485400040c901c00d000c03035400346c1072554248050b03034480c0c400140b8044050ba1100901406000a208a110b011894070f002c58000e01ca980201861800c069100b04e140050023559a5414000c00f940c090311a9642c60416010750410790f01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 121716483 1250 121715233 121715249
    0x3050c0a02060f04090b01090303020c041e151805040b0a05130b070f09050f0306041205070b1005090a0b030a030e010203040b0c011a09040c050f060c0d270506070209090106 76
    0x2484520000c1d200c3c075504603000340b076840c0d89408070000441d801006441d0440354907802500107e500d400811004080b2141c00704101d030301f00fa00403407865045110b0581c141c05002201c1240d43d0400b82c0c1c6c0c00f10802624890601d10385030100f03000200c0d1000c5a03066012112000200340c076682c2d0006000340c6841d10a0091501d10041d0070b000301709802000c010f00300460b956802001c140d86404100010f08070400141d00364201c1c20200e408100e0f07540c10307800b0181403424207518159207990b0b00032400300c3c2240e060405034920344007841907140c413041050704030301c0a00041c1701d0044446c00003525880490b030004c080c0442e01000c018243d001380151002880c034021302c19150103413000c0c4039000e09602884c03e400c0b80000c01c220300f17040c81d100015502950b0001410710741039040030140402034401e003165513402031050000869030b020400464460717041903994201d40a510441442c559683c0c80002114115812824072039034031880280c5075840d0301100c07098806d44171034100a0044c510798000041c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 121717733 1250 121716483 121716487
    0x60405040f0c02010e150a020d0b031002090102010b0609090f04030e0303040f0302090708040c122d0b060609010509040902060408010504050a05060f071b03030b13090b0a0b0d03050c0a0206 83
    0x86442002e070b01001112001c0e0700203010a254188009882e003140824161a00005038003081690341c040d4042c140d280200900040c3c500110382c0041e1419064521001d0700c0c43c1c0009003012a075034280a480540c100c10b0741e04608108141d0002002208020803007040e10103110b00207424140700d06405070040d05d02038150780c5d0f200d40712008820180303503500040e409210a18040354105120341e104030b120744d8000d10f00155030b41c00c0039070595201c140301c05c1c140d0f500e00100c0320302c1120b41210f03250001303608680c4030200c4071000c0920303101881c0400103181900c140c10a00110030980d800c01d044601609046500181106a0f07100103103450140d43c12100d130640c40c0400300410010005211842c05005a085a504d60340f907428403c11035008481407000145144003242800fa01304100d10040c0b44241008030b080031010300443c2441614440d2180740948602c01c00d4144140a94501c4d0494030f10742c0180030040030200420190b00170214010308000e8002548054401c05000354544250b00500050b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 121718983 1250 121717733 121717751
    0x402130b0f040602010e03070302060112210e0f0f0303040902070204090f0b1b0703090b0d090b0f01050117041a04020a120501020d052206150503070f0e060105040303170606040504 79
    0x40701c580c020f0f000b000c015610704601c0e01d8000c40c0000030b4545441d490f81c01421140e091010f242036001025100301e640c603164400201682501c1042604814000c1e955084440e005000f00860746c2d0b0142c000e14040e40c0f011940841d6602c0c0070003120180c0320315400240c0d8940070f51000c18000d081c21400645804d1003500940b04000800308064050642650121106080b10804548a202d034240080c04210011010440d010f4179030081d0100c038840001c001a01905600c800e0700c0040c085445180103220000141304035a001654902500d0300c0f184200182d1034590340d41c64144800d00001c0c110780900c0d4001600b1941e4480f1104042e020640300ca0042000601d0118042d401030b540c1002100d0400c0000784481d018103003e046483e003441c10750303088000507071500c3c401400031400c10704400e200c0039008034040e00c08108036802800d0f440c49885a051401c41c0200c4034074005414241081010802000400d0f8081d007070800c03c3c400d81020030600d0700c0e24400180c40d40f103030354440364010341858042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 121720233 1250 121718983 121719007
    0x3070201030522021c02130903080c0705150c1b100b1005090f030c0a0e0604050702010c0503070e0616140c030d17060a080601030b010305010f0c050403020402130b 72
    0x5040114400e8900303101035120681c410b92040d0080361490111090701c041d5201610b0036440d40300c0d4404901c0d40c0ca0854005503008149880c5481d060290305035101d40e640d8081607400f509095001e020103200d1402d0141e0fa50722642c54400c104c00b550400400d4001144c1c01440160440b192424912064031240b503260598031740311000c0c40c8642e0812440c00c40101c40071300f8429025000c072211652103034030740420385003002440320001c0c01843d010300c11182c09004603120803002d580501400021143c05143c40c0040100781c9600400600869040c51041c10703079036400206480e00202d66050200120321500e000c5052401013003800300b54178240c000f080d000d01940740c03e401049000041943e0b003c0e8020024541e440b2038201c1d0700c00000320807420031802959214952500000001c211180a03603440001070316110b800e800c103075820080c04004108000092190b050040c214210600c00c0d03818084018203d40a0b82c803002c0d000f1500029984090510200b554000e010b43d0081720340c55081007606 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 121721483 1250 121720233 121720237
    0x1031a1002060a060501050a0c0b04061d0c19050306060904060e06010f180b010f030e031b1c0201090c03080a020c0a0b0a090503062406040e0a020703030b0f130b030a1403 75
    0x10b03000c00e213251810114180d489101102e011002c4c585542d50a80480d136698400d80e0300081c41035801031780c6c4807090a42242445c40c0e90329081c81c808000c1c10394800d1030041000d1010b9009155842001154082045490104085034005c03422030b0424840e07a15801e00201406074001154014041c40001042d0301c40b4624a0030b0039920304040120b81804013081d084102c4414204250200b440c4242003006184250840a0200309210a0340d04112510300b4034087d11044990b240c206400c020500d00784401604000c030000401440203120790703403058540b42610000e5000c05003000170005075031003442e07000f00026940101d0190108500c190f03201020707407076500540710307010000d85000d81c0000d0038a000503c05000785000340301700401401e00c5000008002c4003040240d000312060000085c041521014984203a50b81d0710b02594a2500740360007000c076110507088502c5003000c01031500854503400c88128928640745000a8101c40420000e8988544080c1c024951608811800607500001c40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 121722733 1250 121721483 121721491
    0x60206011a0307080115230409200703120e06090a06050106020c1f1b030e03120a120903030b03030703050c15010303050a0302130e0c09010e03060c0901031a100206 72
    0x112890301c0300e40001ca9001840140c419500207503a49005010420f00b000d0040300150751807d01e40c0000d45c1c481e4004450305030201032a00d000d100420104800c200a01032854841c069540c80e5518443c0b80481100c03a000d8410b02408220004608951800b82c2d030b0320440d40f00780307071000316441c9282030390303c00e03907601071000d800c4403480c0c140000050b40d54000214401a0b400040428402013030301481c0107210070604400f84204042410025001105842e400c0d500d10700955607a0285110714090601d01194011341418186042102003010b40c0e00203103c00402d25000004501c01001d420103d004e018241c441d50342c9804006480001c2581040080412001c10000e0302c1c0c21403c1d01c0306454820009210140101d0010400902a10b210381c0c000c0140e00d01d44400b85c0401c1c0e850305407100030200c0845890032820ba0024000400d0340c0c01c102c40d6401c00008a00070710540c904411940b8043c0500c01501c4c1c1450b03101d80d040003070302590744280d41c0c03513810242c10341030750f00303800d0100035a0707050292 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 121723983 1250 121722733 121722749
    0x3020f031602280212030f0f040906140d020103020c1608300f0304080c07030309090e2e0f020307020601051507020d1707170315010c0b010303030b0102030706020406020601 76
    0x89072210203640d16100080ba0f58800140c100500070158013800804a00210031424070b00040089100340200c0c00c000e003201081c1c4040a9881c1c0d0309101c107034030454030150841007080e0b40b114800d0150341c2c2e4036040d61014580c28a0056201c19054216900e0300c0c1500a012071400b034040c8020801c803100245914468140d90106e40003140031800603020850090b5030011052000c000d1141c10427107032401150098801c50380c49203003105080381c2504102c0c01e50000c500248107564100403405460240c44050303482c510150140405109682007a0010000c01c8100719080e0f44a410441b8025030010701080400c10003595249402c3c0b1000751582404d0161510445200d820300150342d04010980328503030340c082d1408100042c1c1d40c03503000c1150307101c0391040b4041608000303900c001400300c00320b003039101c407403440003a141c0c10407041000d001d0240d0030fa0f99040048500b18980404d08030500c460440f0380600b8001210511640100c0c19071154800141038207000180c00510b603a400982141240c51032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 121725233 1250 121723983 121723993
    0xc090c1214070c0201121509050114031b0109030203061509010e01140409020406080d0c030f022a0d021e0109050108060f09060105090a06081b0403030c0b0703020f031602 75
    0xc68620300315000790368028680340ca0400000e2403240540e5040101d607005060040c3c44070f00106584e0b080d80d101000c2000905118034042080030b02c18052240548a016401c032061105500401d64880364102d18400302c0712141010621a4041d400c03040295030041d05444007803610b0724401000c1c0d00d60001e0345000b80000c90002625200035441c260503201700c41da074141c40000070020840908945a000c1e0b038819518400003c07003130010803a070f40380307140e2540f9080582030843c200980035451282c2d10740c040d500100e442680d05a42d1803d5483d281c2d200d5036803642c064040300701144080202c088001d4204035107400040c11041c2200d400031603194240e80c0d81e4502501d03031004441c200402d84401d50042c40d4151180f000786002d8141c107034841c50601d052402c00c80b110000901502103a400700000c2100c82007880718080010320303448618002d00081d546032516550b8024090030007200003800c085143c0c400b01c4d00303580c441e404840c0ea070072280c2c6440d82c4030705000c0c101c03540b141f1490301c0e08800b40c811 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 121726483 1250 121725233 121725257
    0x210030902031902030115030b10090c05040b030c090301021b0613020f0d0f0203030315120703030804080f0702100305240a05011116080a0201080a050f06011b0c090c 73
    0x440d014100d4a2a809405011089101000401d401c0c0015a0882e41552508900d001040b041c20b0054002c501503075514038541088122503401c0c0320326030041107429080000c100b114580001c1210700710703410948403e50741ea851501781200d03401013164250b40342d4000995120000743d803030f2984481c00e08074800e0320201d803514503000440040507200290000022161440b0b00d10f4072034030544805001d112a54072000a90340002d043d0340c0210380c00405040f003880c1c00c030043e040c0100d07160341d01c0410000034241070f4110f03180541040d40c01080145480c00015400c0c40001a400507500419806425646203d05019028024007411540745000c1003a80151541c03110942c100d16821280141c00c11a00500385001103501070b1500700d660505216203444d60760a240002d840700700030042600039040b4041e584c400100f00c000040c024a502c0340c20401030081c002c0c0da60b40000c0c2c00c01003d084c1880290f0a165001030228240d640c05444100320020004658081d60010395400285d6a43c041c11000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 121727733 1250 121726483 121726487
    0x20307061b0609030e040c08010f0605120606220807170616030f0902060d090209070203030405070501030504020120060f0c070b01180209090a02091e010c230115030210 74
    0x112800075001c0304404810210041209a070120702402e01919000c8000c42d00d91011405480d807900340d010000d00004010000603024a6182c4040d20451800c1c5203410b40760000c3d43c000c010301400301d03441250000780c04007900089a8800320008440c080707600546503a01c1d01c01e500ca205910820460041046009034900e4020954034454511b800201010030016901240145410583d202c5111f070385281c4800581d803440054010401c20850128140c049032050103100c2001501c11829176006005210014001042c44c00a8600038a400101c0e9512400100c401c0b0325107007490b1002c40b02240b0704080c122408030b1031a100c0c00030046104055120b43c9043e110522408001a1669446000500c04a02c41c6921401c0e0b4006516001d42440d0480c00000c1ca080400d540043c0865030004000240741441e41a185030500500011842c1c80112030010303000031140e240041c03500c1508400c2e038000c20072007031040d4100d0b69800002c002c2d5514003210f2155043c042c1c00300340d201c0c809110030356042c14 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 121728983 1250 121727733 121727747
    0xf140f0a030506070807020304092a0221090607060c0f020606010905030706140c16080105060a03020604030b0a0f0203010f030c090e030f030a0207050d0e01110a050c0105090607061802030706 84
    0x240d22200820f03465580402c100c1d01c0d0b18002d004007045000403c000100c420039030251103400c0f0000300c100106241186a942512914101940250b41083d010388122142e00d1b071441c0701003102c1c4880306a450380322600041c0d01b0b11407064020a41031910240c228000d90021802041c000c190302250301a0721400c2c01911a01040e10031290700d035004e9032040c004544502d02c004401d498410043d4200f0000f440e00500340f421032408130394480a1424100032225003406039540010082e00d100200b941560080b0f4154441e5010103801041507001240e0840c482d03a006041804103403000315101e507142c188001402c1c5d01e502c010394080003410300115a02506100300034003800d1080040d03240ca1200304203480150001017425148660078401000824414444481110200da5131000d0601c001c5001415015021644040951201c2080e600003200050010b041e40c0090034002d1302d03050040c0c00a00e4900c13034400020030035800c010400749140001e41300b000a030307031007102502c80d040c1d2a154112029 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 121730233 1250 121728983 121728989
    0x507050f0703110f011407050f070603180209060105090a0e061315061404121a130f260f0705150417160b13030201060f030302070e0c040f140f0a 64
    0x101d569012012010300d40150f00013500b07401810302c220460700490f00d1003040d8020340e401741d41c15080a44110b10080007481090007803c0f03036080811a203030564003a40160340f4501c00c020702410900011414603805082603508035000204801c0c1078a4444c943d0076503084e400c4e03c81c28041c50130560320616114890007445c03010150030f40d0003000e2919088040303a22403080070303010304120b01c10040811940ca40742e0240d016240100c0c4429810a07400000020310b001c010140002c005490703003084001406481c04068240d0414042c2c0c1e0440c104a00e41c500300240c4100b4010164400030308102d280464801401806000354241c500007a01c0340250100c0d010103c400030301e61407a45078078491001100002c2c04084040443e04076510015659010141c2c00c140c0754035103081d040344030000802d0f0782400740402914801c0b003c003041038991b6030065507441d42c0780070b140130f268403401c001a5480f0140054034020703d40c141808240340c0da21003c0c40c841480e40642107000f13031114150002541000c003060012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 121731483 1250 121730233 121730243
    0x1027030906080603011416030207051006030507050105190f110f070905070513030605090c04050108060405210f0d0e12030703060b030106051b07030210021f0b03060601111c0507050f0703 82
    0x1591f4900d080041b00d04103044110052590030701c00500482c074204182400d18451020000d13095081d070429a05c1c200440d4412810440204104002c0240325108000030385a242043c441200519800f62442030142d010883d8034071511202064a80f030000e000300480d00f178154200aa40c669100454040c400c1c29101c1034001e10320141000020460340c44507138801c949000b80d840300d9040c0d500050507a4405c0c0d0004099900c0301c4248001c0c40b41c240810141c80a00000c0700303081c10015407643d50f180c010403000ca91411008280811260082e42080303030852182c10940e051022111031003000764109a035000002890008080b4006c4c0030401200e041e9200ea440b03940c100703070710340b10180300c8078030480c0c081d180c0e90040070b00000c01030703d69461541c486500c58026040c0c20540404003020920b40c540d5030103480d070a110380030440d070303c000c906c80c2e810085c28600800190a0700100c0c3c0c1c90846403002c2c01c003100303441c0d240805039a40d01c8800b0307000e4a4465011740d06500d0030840050758560752030102802c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 121732733 1250 121731483 121731521
    0xe0a0f0f020708040e090c09160f0e030c04110403060603230c031b010507050d0201360f0305190203040303090801140c0904110d020a170702102703090608060301 71
    0x70445c41070381001640a40c010741200c0540c441140843c1500381d05a8180040f8101c211941c05440d801c48444087c401e1585002404a022100000e0340c0d001c14070405400385507202c15814501e46040200c03006180c00880900c1031a0756440c225013019480460380b81d1001c0715040990aa09021410241050006004140d03038600c405000703001201f0414101d051100400084000403414001c002043e034051300000341004c040310300480685941c0558000a202080050202400b07615103003407003a801c0b00c008441c49800c0d160650f150300c01c880e404101c402c154050002980c1d4004018400c2c0d80c842d80c1c40d0304085a40300d4049080e0b4600d42d0445400c0c800820002d100c6980c040050001c00d140200003082e00c40040c400100c5640c0084050110302e50000b40103070200303030008407130410042ca540100300c03149000203000351103203c5080c40204458071382001e0b00f0741503003203a050300784078242c1030018541141c0341c980075000104c03d120300c2e0b0100740c90600090301c2d0315040c459002001c008008044d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 121733983 1250 121732733 121732739
    0x6070504060909151503090303060b04030203060f06010c0b0a0e07050d03050306220c180b070803040b0406020409060b0307030c0306060507080702030a0501060b070501050105060a12050a060e0a0f0f02070804 91
    0x140142c1012201101030000c042c200017441c240c1e5000740201c8003150740300000c2c143c1c01420014291145a007160354411002c002c2000141c8000810f40d80c05142c45003606802d46807031004a9044180000180980d00ba05050054040b2160f01589031640c13018101c81c5800d541b04280113001d05120340c0580850010f10008070a41000e082c1c11781807044038012407900c5c540821100003200c51026085c0005035100002c064517125101c030800c082c1640d400c01501344040345d84c0f40c00342480010402071004003200003003020000c1c150190340240100034000d0040d00d44480602085810032150500003030304251090030154042e200d41411740e1060b40d1550320f04031498a070b082c25035010300d5007245c15128161108000c5107080c811200540031602c4407564918039800c001d0b00b5144180c01507803003940c04114403444e540c1c102d00700c201a003141c203801240c16601c003020140205450381c443c000d07402480c0300b00500518240c0c480c0d107072284000170400c40e41c003010701c88900704d00400a0043c0307002e000308404c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 121735233 1250 121733983 121733999
    0x7060b0604030516051906110c030d02100b04020c06221203141005030c0d0515090f0f030406080105040513050a03050c010609050411150c0d0203071514010312050c011a0102060705040609 82
    0x40d8441154408c122542c03600308070081313403418003500c6903840141c21040d02c483e04621a8080e894407020221000d50420200b5032308907860304c10241c10016180740d4080d407003080c503000f18181900c4e81d41061190000d0f071034080b4094054010a100d401051078400c00003104140c00307030b80007001e42c0c4014004081c5440380c2010300a0b41001807e040d20b8038458842100365030405403141621034002031300500000c20380404d0380303460000502c101e407400741c0040c44103001c01580a0f001c541140c0048a0100f090303220740d01e20081c94030715580c020742030303018010300d16081c10f4102000f06a2110314200070490507940e0340448081315003e80b0010418010700442c03020720f06d00f401004661800c1e4148e01e6180a89a000e094070740301000700399101581000c1020b40500604290180d992030882c8401d019080e50014072a00d840070500004020500950049406c58484d406035071150304450001c002a8030114582d1485402141da528014801c540005981910801c16101100c0c8161903001d605810300c440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 121736483 1250 121735233 121735247
    0x27060a0b18040f0b040501230102060c0d05070c0b0717060d080d0f24030c0b03060f150408030f030a0507030c0c0b151305041703090a020607060b0604030516051906 72
    0xf94240498540c40d010265685620400b0b00a04050b05085039807201c2c0e110000e4045003c0340301c2415500714500704001d00e40910101c44a00f0b1031400001442c0c0c0c1d400e0001c1d120002c85000240c035203a43c400421140e40c5d04a40710088011405540a03019501c9404005099201d500010514841403003684140642d0750007410382606e040601061314074601d4410310401010340446068142280300800a10030040b81c003802030072000c51050b1440c50a42e0120b07a444007041c02c00b50107110300162290501d8107040070364000c1c1c1101e1095039a1145011100d0340e0641090b10040e030880d25180214610724024401e4810803412600d4090100701c582e2a018200302004000c0142660307240c803100c0b0350340c3ea41712036050240d092450000f04e0341014109800c2101c240d00c02224800d004009002440b0350000d001c1c091558115007030755489455142020146c1030401035103030849070202c0d0100c00c0050111b1385c2250001148162880a070760380082020901c4001480c1070101035201060020920881d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 121737733 1250 121736483 121736501
    0x50a0f120c090905100f060e0c0d0f050c090a050612010614070804031202060f07020c0d03020f010e1c0f05090907030219110f030310060e27060a0b1804 67
    0x8520300d5603540d141070340310656107400402c84040d00700c54130385d0600400e40e116803844c07031a0742c01d001c008031410f14503d6240d03544003512440741c1d039001298521a807141c40d040904070b00409c48090105007042d242c0e0040581081e144248203048142010889040c03020030744008803a02c1100380b0850746800d6040d6200d0700407440d814000b02d0100300c510045403c0c000140300461007045421849130340550300a0911130054055000d201c02403040c81440380d030020701e0180a5204071031a4081142e00d140c1a4a040aa01f00c5d0300b106508004071510000c034046982300c01e000b0076104c540d0b080c4046080407101d00c12800654030108a0038030901145003070801c5c059030f020405050052900d0400058243c0801c2c0c031340e00b20310000e00c030250003404000c03091101801c180b911000031415401c00c0e422004045c1a5402004104403d20b8000c82071030380d550301035041c0c2481450310040c92200c0c1d00b14442d0848811500a400703850240340010b51913003d03104035025451036900d0700d40e0344061a41004080d1540e8a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 121738983 1250 121737733 121737743
    0x20303040e010b0a030b0603131709030a0c050103200403080702040609021b0c041e090201021e0a17070f020919060e1806040b01030f0c1505030709050a0f12 69
    0x840301041d03103007510745110701034107400b0300b0070742c41d000d10000080030341d0745040f000e50041d6000e005020141a503940c068110b65808000712040c020090711203882801280c000d61350520400c0c0c902d1080c04440c11402d401e480d401c2c0e0b82480005401407502d01c80180c4003208a04610f4200000c0000c03030403407000381c0b4016200400104461f942e400300c40702a41c0140c440c0c1540d11000510001a03d00b00300b10040d41400c00340d505103d0418400100d4000c500c8a26000c0c0c1c400b0f03110414242168400d0107100040190b1150b02c40c100782e011512140d891030b56041c205c0328000c400715988810746021040d40d02c96640540490001c81040d0309000c09120041c0440c0350207026960f1006540b075480c01903074041d200024504040d45030003440300c4c0d00040383c85010811500040d080c04049040310f40a541540e0700708222a1100c0038a10309400c1c3c0c071015900c410000c000034403000002c294000005c41c0610019920052516100c0c030400442c02d050f849445411020a5020001070024051502c1118000c6c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 121740233 1250 121738983 121738987
    0x1b010309080424020606060d0203040f120503040c090902090a090c08010204140f15030f04050705060f0301030b070908071503090515010e0114180c07050d030516020f060601030207020303 82
    0x3a681c20255821a810146021404100c00c0240c0e0307095499152104100d44002c0001d801c0080108203203104400c0f1460700590000001800e00081011001c01c041d4010310300722401009000c001c086d500300f81c0e011039003400c0300900007179581c041e4042d2070f003010b4008000d000ca80d203d460014008120040c02122540c40000c4002003030700b02031010708001d000b01c50240d0880025042040440f8001101c1c1e10301c504081041c0140302201201a01e6000d0303c1440c0d41740b41c9844505199182c41c24651190740d005030b00141121036064a040514100c0340300d100d07540106d840b8030405480800c0315000d54601ca40c8100d03802c2040594000c1c25000403034550a000070a4040b42d26968204800f075041e044406018100400110712a03110b403500420092355800889002c0c000000c84c1c90010102001094a4040100d0441d440b21000c0311845a8420111104160220030250203040100c800003480030100d0702c0c20052500100e55400b1213000c0c00302400603507549000540c02901312000036070f054801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 121741483 1250 121740233 121740251
    0x6030209030c040905060105010f02060907050415091505090a05090606060d060f08030307020c060418110d0e0c0f040903050405040c0e12030909060604030b0a0906020c100e16081b0103 81
    0x10f500ca0903441e240110041c0080d03605240c00501059450784012045510100c10041508000302c0c01d1820f803a01102e0225003190480d5001078407690076040301035942d1400c6151002c132110032400c40c086540a80e50040d03155510390f03815044600844074405c80c0c1d00f040d00003441d54540b020040000c00811117002614540350100d035620f800046e0050040c90340004103009050b40c04200700e8882c0385044825034900707802c0c00240c4c20741c51700c10320001c58110f0704c0d82240c04d1841019020381d054203180442c10040c0c0d620300b504050340c402d0140c12582c0900140b80c0e140d0103c1c00c0134003030070000e00e0701341e1a030760701e842e2502051200411291154100308230340080c17044d040e6039650309500345012a03800110b031285011070801812003805000d503449181c0c10401080003030f102040c916030007030340f44200085818290400c00060320800b140740c1443d005400d81d101c0010080e42c40003010480c00e0707040b104100c205242c081800355190041742940d9100c0600d8880c080c1c4510031803c50104103140c08206080c4c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 121742733 1250 121741483 121741489
    0x9010f1a030106050f0d1401180303090b0a0b0d11060f0a021507020303040b0a0f090206130e10050a03260d050402122b05130f05150a0906030209030c 66
    0xc5401a80d03650a003003902040d4914007400b880010303000455109901602c2d55002079040d00600760000c1011083e10075000ca0083c0a40c0400d108080050040110720070382e150003801444825012190324442e000440c101c890b107485850715240303005d050103040306940d45500300c03030341415605a54008410408600200c0c03ea80140956200baa00244a1241844141035103460300030600002c40d40240300b048040303581c0c0154540c00020102d40010040a0000c811010300a0740358083e400600c001050b50715821b950902c102241d88000c6401c029468501d0300c2d40440c00303e8850245c2c0a2260f11003400130500482034005814090f105001c03442c0d855010000c07003500920621060f0b242d844042206505081c1c0440520200c10b60241a2040704c08801085080d00f4039108030341d102c0e610340c00702041c80c01041202c64416a8040311000306507580300107000704000b401818007418003401a1032866050f001601e60009080d00da000f421414904220020340001420300c0c5c0c5071055195401c19a1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 121743983 1250 121742733 121742741
    0x1a0d0209060f03160302070f03050306030a240b04060506090f06070c030804060915020d18051915230a12020304050c040b0d0506041719050a0f08040f060509010f 71
    0x98244001e00d52280360a140404281611300f01081c149401000784400240d0b180d81265800703075060420503140d86450b40031074a0b1072440c203002450394040404020103020b69542007000d0b2050400148203081c030440074441561500e102e21500305406012038081d0346440d6119070400f10001e06660300f840025107400a800429a101381d031040c03800942405a01c2c2d201c903184006d0408210541260b40341601c1c003d41c1c2d0a0803828890402246840d01104080b642100310006c15000703010071780881c2420701c042000030951041a050403459072000164034040c2c0090508040a400e0702404e40f1030381d40781d45009912069130b010410640c458400c0e480348a6102560081703010304014100400c910f000d0101b10340c000905d251003403d10000c0c0c07100058001807000c4e07106500042c4071114502031200302d8850302031811450016541043c4640110b64024007a00018030701e40e03112450b00501c000d00752103000040c0c401905407035080e20301d84c0104040d60801034000804034000150b500c014402d1104071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 121745233 1250 121743983 121743997
    0x7140607050717040506031513021201051c030207090203060f0d140d0e060d09051002120403020c0a0b0301140d0501050a060501120507170711060c1c05011a0d020906 73
    0x400e2010407200e062080c903403440303e009082e07040003034034050408000a4860100a0905810155149600c81c09440340101040d800325904001d40d2903000c20ba28040e003900c0240a17040c0180d426500d60074040c09248123002c4403039010780260070558108004d000103940020445908072052241080240d01d4000e810441039002d26003002c05084005016401d140d04911640e08218105c081d074917003036607140e040300c6803114410000200c2d21260700d841401c2001c80c01c0700100042c408144400080c5403008514440c0c0e00c40e900791103000106e01c0400201d42c506004d50000d003803060005010401c2c8508500241c030700e009101c0102685aa5607580c25503e04071200110603848040402c41560802c1d142030700300c2d550803428040d501d0400c0340188a06110009048440e44034008944014011803004c5034007581c0000707071840c1d031900c407440c02126484400484140b1100030a118018801403080320f050b1128140c400c041c00404040c2e00019810841c140d00055600700000c3c0e40e00c1c0d132410014981c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 121746483 1250 121745233 121745237
    0x5030c070f021c030e040516031e1a0907030207081e091002010209040b0609030607080711030301060f080a02120c03100e0f070201060e1003030513080307050a050c0d051207140607 79
    0x3051201e841c0045c8540810b070304c81ca0049080c0814040380c070300c03071940014400300b55140c0043e0030000e01a0600d170341141e4908030030fa510b26001220400940e134034a0500307240d005036840001d0f40c5580c0da04030102e100b08140a4461181440041401c2c400e50f007008840da2034044074142404d1035000012444c0070207000c0300016030342c0081e4080d07203400c260040c4051030404481c283d003841001c02c042601c82600030041d100b04104030002455540c000d04018544105031f0048a441f5030310f0b18000350600c0c80703842040000c181103d00289090a07140212084442c0401e00048251541001e0304c0881d0006410401060800352010450088a0150a200b2011400259640d041520010f42190015004104107600d908200f0440d40f840c2e182d86802c90ba03141c68140d58468070000da6800500e210380018140c0d0200048000c2402030014039640c89601903410340d2041541c1e4403c002ca0722015800041850b000040340e42c940d000d050700a0a062401070f007000d03121012440f54181030101c22141800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 121747733 1250 121746483 121746529
    0x809040e06060901151d19060203041a04120f03030b0301020c0c090901060303021c0504090507030506040b0a050f1c050a150501270b0111070b04050f0a0605030c070f02 74
    0x3035141910000e4010084044841d1061500785e90091403000558841d408510708407410031400e8a4502c42040403c681c80790b03440009031100b40007500c0f43d10900ca03281c0351003a050110b80c2118002030403903040390100c440054814040ea541d821103136040ca042501419a6644d01c00c4141e00c00b0300041944810b02005081004401e5040140c00c440103824045640e16001007400066000901c0800c0c803d40c41503a0154a98080342c100c036640f00e99000805614141810312a0054150b08954002d400864041c01881c070841c050100d0a0041c0c4909903100e21004501091405c0c407021040030030306611312100c111901c0e82c0310603140c000702050896265000d5a085040807010344600390150403c8015181151440c003400f002c0c0c43d01c08488401001e40d200d00300c00d800e03802000245403191441703080e10042991b03200c205055420511405008103030f940ca1440380340c82c000300904192002170b00c60504540b0394000c48100d44d00400070441c0c040d0b1502920801580d40d120011400300100300e4042e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 121748983 1250 121747733 121747741
    0x801090b0115093317150916030b03030708120c0301060801170f100b150f03010e1b0d0902040f0c02070302010809030f040906060207120b040209040809040e06 70
    0x4912640140c1c0208a00d0100110b401d1800f580652500100c81c2c100f40d45412942d5045465030704c524400c4c0b000b011302c03030070031602c10001038021400d0701e1990042d5a10855a0781d5420f110ba444181c10410258030000980c00100301106122a0307883c0070030a40b0b4005400700084020070b145610980c0d0940e100c03480480c03896620540c2000c3c42d58004851003d41c1e0640d45091406007070b181040c0280102072484540f0a1020f102c02c0000180c280900c4049906189801d10b208009280320340b600c41c091414140003d14502010342154030001340700c5c007031518680c6000740403603410402405c1c0c035080b41c1e101038031845551070300301c0134086682c4c1e41030340000c10341054410007003150000d105180650f401c0000311000d1075000300380b000441c0d03020301300301207156076004000741540b00d166441c98045201040201790390038540d01240c00d0f20843d80071141c1d401d85684c03210340c0e8030614010051150303c60f180090f0050600e4030b0600d400a05c1040b48034140086080028191491483c407400503074800c000300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 121750233 1250 121748983 121748993
    0xc080d06090908030a0b0a14040b060c10061403010903020c0d080c0d0e04140103050615120708030c06090c060a030207061104030b060a050603090a0b040f17040614040f1403010f0501080109 83
    0x3c1c940030100d50700720102d031420308da1583d82218a90034510450b0b4481e114211912034030110340d41c2c21078010964005954164030030000f0807041c020808084e2020000c2d003200e040502c80c01c8290380c3c040c0c00074490b0141020410070711340134104c0111554401130202e08940c950801c65900300d803140c0d48800e88103424050912040b84c1c40d00521000000480004101052020034840d400c0000795000300c030945000000b20700981038117480500d507072203444000500e10001001811114403801b046d04c1c51500c0f40c54110340d492110104075948080704201580d030181c001da0042c480036100c1d01c030124101c01e04404645d00341d00658015940030080c507042100c107142c01c02000c80a49405c8464030b0550504004240c0e503605039600040c441c2c8070040224040c800360461f103850b4140c2c88104080f114100e20b40112003a007041c81228042007504204002082042c0300b600c0c1940d810100c0c50304030a1406c00503230140b41c0602850b42c0c055507921602c580140d11400750070b010b840d0240011235826070901c1c00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 121751483 1250 121750233 121750241
    0xc0301080f160e070c0c08030903060c0702030c0111010603050303010603050603100507080705130e071710030308060409060e0a030905241b070819060515010c080d06090908030a 78
    0x1600e080d421800d898120392400100d000c2c10396400c259401140d54601009030f800d01d506010141c0720061031440007851031000030090400380b0059003a11070949500480d10024026240001d5042d00140d04544542d48a642c2d140902e113980d400108565a0320f8861500715442038100c6c6002a441d2010064981802c0200040d11034041c203040140e0300e02044024034002000c0e10007403c1150015150707001e50660701c10b2002a042c55405500c03141003218000e801300010105c440009801e04002901601459002c03204884d016110720405075a102c08200050041e0001150030341c5c2e460501004a500c1040050440c1d4401d0b1140350089041a00304007000840511450088408502082440302c408003070395280316000d13060850014201030058144007542c0c014040e188503848055500c42800c61480070100d014013400c0049031588110880c994002c00b603098080340c61907403030400181f01c8500038400911060710001e5625151000582620143d200c142c40d0b800020084c010b00d071455200f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 121752733 1250 121751483 121751503
    0x816030e0a080d09060e010905040608010b0906180406090206070506090f16060504300609020f150a0807020705100903140102040305120c0705042301090b061209070e0c030108 77
    0x100400b03d000240c20010070000c400c2c0a50001c0059a0724095a40e9014085a4002d4000100203028048c3c0303e66019008184110300c0d0740c40381003c44040361090a001c0c10040000c000300541c00300954843e00d402c000351540305400c80c5c200b00304210f4900814418003280f402000381c10007910340b100300c12900c0c074506103224946038a0801005020050140c104044070100c0b018000c103d4803030310500c00d004038a0b0360703038800110081c1c8121700070070104a459442140002e200703c849861126000052112012100c0080078071030108000c484211400384549950206281c811148419180c10203c1c460a0502d040c110220700307001801e0041062400748205080b04040003141064515110f541d034515042c0c09402d070406e000952010880b409004a501604001e04140a03800c44d0002d1040c00204885009151988000003c542c402882c0138041c1c0340000182090300389000050300d54015840501071032400d2060745000148002c1c80a29580705003c00346c881da0b102e40c1741109403410400350305 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 121753983 1250 121752733 121752749
    0x911130611011b0c03080406020c070b0712031107031107050a06030c020106050d02030304060f091a0c0606010201141f18090507080309010f03020c0124080d0311040603090816030e0a 80
    0x420701080e0380e101341c2c1122055094078010131103443d80c0c20410300901c0350b035a08450a000d601030114880c00c00c0002400c0d51441f03610f003440004075991046088840060607490040810805000031134800c0300229011940d0405850681d0f55400000d42d1801d815406603010a480c0c143c4500007907028842c80000700801d5407030010031101b60b8002a1648140d0245800740442050480804c600c00d84255020707101d9066404070402c0310030304031906030b0884550071045100b014009201c551060282d0000c600600b0b5002030b0b0b50f00c1d04d01c085074444055503a2030360302c40c2001a00042c0101c44002042c03440c4058240028008014108181029840d82141c0c02a0b4400c01003092181d900c403816070702843d0140741c016129444036030b9103405080e9a10003808191000c1260380c1d0001d180949103000c070b40714441116110303400c00b001941500e0032000341c1d424034a0f062008001031360007500210f00c0244a030030b13140d05d40090401c1c90360700f4800115080d00095041050b0080c1c40c28042c003000e014001d49 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 121755233 1250 121753983 121754021
    0x21100b07050a14030c07030b0414011803030209040209060301121a0906060906120a05010c02010e0f0a020f030a140d0909020f09042708031006030c0207091113061101 73
    0x40e26419036400c00c01c84003c141e801510000c409105003441512040b18441d819107100c1503490405604046058074161103003c403a1001c299095014880c845d402514454000c80204240c0c4040e0000c1d00243c1344075070407a80030824150640e844030001d5020b88070000b0340e4442c00328982403403070009034034a4940c2c0040246500b4401c00d100006669070f03010200b10344c04001580d41e030340861080000810301500c24894100b0100411034190008100e00240754003c11041c02c04c0140c903545c0304040e00c42044143c12805210f4050b003030188480c035102d14085c049810a00403503848540d03004640c480165580c01000005402c00d601010a400401c5613400c154104104540011042d21840b14500c3c45140e55900b00e011000c83e00d07020810b54210010310b00d18640e80c505081045a20440d403140e0008010140868014041d105076481d40e045540200519070400c1c5588000b084d400c0c18662007a02e00380100000808206070f2517000d0035081e03440c101040b0503001c0c254291002228824404809 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 121756483 1250 121755233 121755247
    0xd020a020d06110d09080702090907050a03020d1a040309030c050108070806092e03050c06030c1209010f020406030204031511180f120a1403120c030c21100b 69
    0x40d00441410041d0020400030703c60356144041001031240d15a00b03a0800d0a0940d91420320446030060305110b4026104407a0aa480c0f901d559294003582c012a41e000140742814005400e00307001c0400c8640c410284e040c000c40100020b8001d0100c1103800300c0005240c98400d01c10042e1350300344500100404e00b088400e41c2000c0304090080d510050450f4080c40c0020005804082c0150340c071089801d00a4216021402d0100380805c0c10700140002e4607103104000c802c20a50070010100e902c150103030598281044420401c0001050000c4c10040b0251340311a4500500394051005000622498400680d254a11301d04865070280304410b01c001907240041102d0b503161020202c40c00c0480318111160300075015000100d14001d41c98800b03821030301010174030664410004c0c4450019005040601085190080f032030303540d00c500800541100003a1001c2400c420700c0801640c0c028803140590750400349207858074403d6003084601040340b0541c0700306101c2105c405070042c9001d0492005403901c1c1c110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 121757733 1250 121756483 121756489
    0x50306010b160f03080109180209040201030c02070803161104021612050d06080a05010e0303070507060917030f070e0d02060306060706090b01060e130b010f08040c17010e0d020a02 79
    0x100500c5008468079001032100308051840091212050380410304501c0c0003000c0c02c0041c0000b00074010b000782d00d498a100c1e05c3d1448103042401e04601e500502c41140e41c0e85590045001c1c00d00307080f9840070362180d0780d0007045458060015000c0e61808840c100008106814041d21510284500500031841005400742c040ca00e030300c0842202e604140012640380005008890a00c0b41e80c0100303401520301000424180008a000a0301e940110000e0003000c465000d50342e140d00c400e907454004980e0404c080c50009403d03030808280c3d18011454155118010700c481c1195510845140c54a02c803148200b006280c0c0103800000b01c140c099a03210110315090b40070503c603110180c1510b20549001c1141da0400c09960444a00c0c00c0c1d0119031039045583d20700c0050410100c80717402601c14401492422895900c038030a007036014105075250300c04054403800a40c0d841344050000c1c2d0b9548540346c0040f40852540303070640c41120700100001440a4507900c010305100c140c80081085400000344c840c0076a03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 121758983 1250 121757733 121757743
    0x501020607080903090d0503040f06090608010e060a0905040803071d010903060e0106030501110310051c03050a020a060e0717010204270605131e0c14090a030c1202010210060503 78
    0x241c00d090070280780d1a2142802e1440c080c6980041c2e002042e1114402003050210207041100d112078181c03880c00d5290641070340c40120034040c910000303103200c0c010000146a04421170f0001d0018190400032900d400602040c0c500840e01a10800f20010512005540c890b0848600002e051030215200240b00c000170020782c028400a89012b46402540c01c1070b641c21340c442e000465100f4000c010308099036104403d2900100d800080340c0b507074840002101c0c00c160030407081e451150b429201c00800e80e994191156005828024214401da04504000070100d00c9890190343c54000280364a52426035021031030450f0b810302c403007217034010b0204024011050050b56106411210f0f4000c100e5403849404c4010b166552143d40d10101d258441d80d216003490f801401c80100314200b12241c000d00030b003213070140d4000c01203610000c0d682c12444228840c1180c06000980303c020310f00948103507680c84110342161150400c900515074150030008540e010801b440000c000314500b4880704d803600c1c000030f40303170 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 121760233 1250 121758983 121758991
    0xc070b0a062111030601060f110a051f15090213270507020f030f0a080108150402010302030604020702120f0105090a0f020f0103020408010c0c02040c210b0d120e030105060a05010206 80
    0x507a100070340701001c00c8041d43e411940b400014080f602c0303641c0d607044010300d01000d200d100c0000c01c000d8140380c07203070410114500702c070f030358106000b061041480165420b0820000412400300e13a07884140b60251604989410002e010842c000341e120f081110100400c2503445d4000c800000c1010303440141034408941c0040154103940c8001403550baa814140e040c00090001c104560200049a00100365128080c1006040990700d00c074051fa00c4141d601d0f0b441501c1d05250b000540c201002a00540c030940081d07030710110140c400341c1480d01c254041050b40c0c10316400d507000794215010200c10800c0900c240c5601207501d000a0080e1162511801e1900c0001c1c1c8001e030281e001c0d038450361170a90207601210024030016008104141c9a0180107020a61602c0100d00c01c0381012901001c041c441e020041c24448200302c007221150000340c80000a00c030303c0740b03080d400a803509521008146040d0300c6c5c482d106082d4031900800d0748400100750848c3c40c024101813113143c2c501e00c148480d0342e00060860384 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 121761483 1250 121760233 121760279
    0x90114130b01030e0f2a0102060a051801020f1e030105060a0305070c020a140f0102010c02030a110c04050112150624020109200a0f0509190905060c070b0a06 69
    0x10103000c0c00102c026244401c1c0740e600c03511400710010382c1401d00145500c3c0c05507030000440048142840014101c606c03e0300450300581c440404101c1c840c00680c080c58010300307480440214216100c00d100d09a0b0020800581ca580c80403e0020b4099813401c0c0401c0c000124002e62171a56060500040250080e410307004109507442000644490282c1c00768411250000c088441940e80c800c07170601c230180c00f80f25160146500d4940b0741440d5005000d06000119190042c41c1000c2c2d600c1c00450384580b0001090600340328501420496032254420640603000108200011642504212002e182100c0c1c080f1001450300e00c0402070114030341a01021080d4440301c60600c05140e100c124007500c9055005003c0c1d0043c4144120b104401105000c512401950030081c81030340c540030410f0450851040c5500b110b80d000004600061a0b460921301800041000441c1e101c10346600b032030b0141c120f0b0000c1c0b200340c0002c0c181e400c0c03141d0841c2d1543c4c0301140307030014080d907030a00b55800c00310044c040301118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 121762589 1106 121761483 121761491
    0xf0f050c03011104050f0a1707061e020a061127010e042702031606030f0f0b0307090f020904090b0601110a081614190209011413 57
    0xc0c042e0100003c54100751501c0c042c03094240d024225154000c4510001280c036414440c1c0c10020540c202c0c00402d2603030300740880a4080403144600a0b03107042e12030442160a81d001412a5545600c0080420306141c2c026095001740204032007981600a2900380c4403103d103500c1154400e112003640d86200721541501400f0482e9a0802c9008100d0070717507081d0018000040041c545214405012280c00c600c07910128002c03011a0381040d00081d40301c10fa9230740034962502a2600e4450340030410001c0c3d204840029507603210600c241c49840d80c540661404a44440d8140c1c0c103154005031007032142800328680344000c2c50080b40c0150101b1300d0b900424869410000b4600310035584005003074603140c001106010503040c2d240707044621058901c49440c4881003405070005401070505400e035849070f940b042142d600c0058000300f541050081d852400c9542c0c0c424404801015810002 = true := by decide +kernel

theorem cover : BRFrame.Cov 121582733 121762589 := by
  have h0 := BRFrame.cov_init 121582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 121582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 121582733 ≤ n) (h2 : n < 121762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
