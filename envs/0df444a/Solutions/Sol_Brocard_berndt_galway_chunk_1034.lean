-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1034
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:56:17.010484+00:00
-- url     : https://prove2.me/submissions/ab652e34-06c2-4b28-9a5b-8a07f84d698b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 185791366 ≤ n < 185971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 185792616 1250 185791366 185791373
    0x120503270f06010f08100c05040e1302040506040c0e0618090703020a03060e0127060b07081e0c0a110a030605040809010906020f100914030408061501051201060c06060b2b0207 77
    0x4035440d0030701107401b641d030350001202c4a010b03e044800806120b4659a0140790190703c1109410661005a0040782404001071052406c0d106101181e00e4a442d0041c005402d0018001c194005841a03100c0325040000740b421039840b00c44061003140a55000369031400c4001c0700405941c440d40c04102134825210040c03009581d6402c01142940510520002403091090380318081c0c4117503484919030440000e0800c080c02807500040920705500c0d00e060b0200b448280d034854040c41041480034003030700036490b407900080b50401c03001941d11008105031201601c90321124100d5400f55401c0b0340c0003400056495865821107448801403400f40080c048014100e00c071607071034411101d01c640000c0c2d40e0701c001008210712039410b0300000e40f404040b81d0701c50340c603a52442d07540d560030348241c400c15100b4a1107804561080c4125000c1d00700ca2801d03281e41ea46011000d07100ca00c3c1d040c0c0c0c11104070352207680205190f0411006400055403560010b0200d060950344141012020043c480d1001c0c010000700011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 185793866 1250 185792616 185792623
    0x211606390c03120e011b0c030206010510050405090a0b130b04051f17070b0406030203060a0902030c07140a05011a0a050a0e01141c0c0611010207120503270f06010f08 73
    0xb43e603180c200c04074200020b81c142900409401c00303c85001d9800017505c101081d40020030f0004544a41c00319160b0780d8a410802c010240c68030103038030000303074108020302043c1403081e03107250414001c000105118824000084d401d64040041c6400d040d5038890741115460b05014454200103114404040508441c0030341c0303144855030066100e5180d2484040f0704040c0304128043c01081003103e526116910341000070040d52007035070b80e14400d111849000c18a09003d00c2240e025214a00c0050302d440880c0c0e41d041e0080c0e1a1040020312303405840482008140301303000c2d4080300718620365a074200034804d404101020010b5041035000e020402418050060345440c1039054a501441210300041e589000805081d406020311102c610702d002c4103000c000d1001c0386481680c62945581c81145400c07150f441c200d014601020b0316810050341d034520151f000d0002180c000c4d42c403407241980000301d11143c0c1c100da00518210150f43c0c1c0318640c10001040180089030140000b06e41c501d079031034a020300480c0da = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 185795116 1250 185793866 185793887
    0x5040f060e2d040203130803010306020301080105010806330405040b06040606050a1d1f0e3a060b0d0302060a0b060307090605130e09060405211606390c03 68
    0x115400004501300711b2002420300d10480d401b00d00d0b26525a100e18000020b50001c0c4201d032065800c2c0400072588403000305000344502d040b0100403034a90058050408044e00900500c20010750701004c101054550307002e8a13100c0d500030b218000d00fa040c190309200495001342c1c0100304002d024090015040d90007900c9412030301c8909035070103101c0d20040000d590f40a02c0c08403100140c02810088000540088007080c1595040390a032420341a0411b0618521702c40c0c1c0e50500c011000c94802180b40b5000303424020603140514030000e542043d8001280040c007a01200780c1c0580e121204000301401c00d030141c4190502c0a50304107040d801c2000300070306540018003a80f0180980400d404008402c9a041c101c018041c1ea401c50f0301c681005500c81d40c45030001d880035602d40c061580100420070030020740c40443d0000104840c0b0700085050345682d581c040348011100b00d502c800000c00340302d843c4600015240c28035011452020f81e100940340c0141116210002030210403c428070210703400030704059 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 185796366 1250 185795116 185795119
    0x10b01120f0204080d020a12020606060307270b07021504031106070602220e0a060b031b0f03070905010908010608031207110604110406091803030c05040f060e2d 71
    0x4000300e1550401e0041c0c0625000002075100351240041d01640c0020460005400707560391030030302c00d00601e080b0388810007110850740180081000c284440d02c60780d01a03c5406992401070003e171005000041101e80b9684035a5180f030010070010b0035840d207945c24450704001502c00e5072800e03181daaa55a2103281d03081e45036110b06c40100b0301c4070038041d5507012144042412121142c08001c031107071400303980c0490b006040f06105000300083c40907043d0710403581507484400d2800d044d0344e140d4407001d821413881941754003003c60500800030920100b01c05103000c3c1d032164486150450a110004003e4120742d403110f00c040c0c1c1400800c009180011080703400504c00008000c2d182d666820701541c040c85604500d860030b00c1007004000030700c03030741c5c12190320001800c03074090000715a9640f0010941e5605840c000103030844600140c0028026070040a1641d00340c2049410141e441c00b420b46600203d601404c0420b8400203890708625000c03c80e1424940b0b40030000309021044a844142d200d501000d1a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 185797616 1250 185796366 185796371
    0x20d091404050405190c060305150f1c0606090c020c1c0f1103030a02010b09060402090108150415060e032103060f040605040609020c070f0303080a050a0605060301030609030e03010b0112 82
    0x1a0078010240604c0c0721500d02070084081d0f141031854006d903a400306118030b400003860580420340c030091510400200060040c502d4810300c5400c002c000c41c0b9000d40c600c2080c841d0300001d0400c0000c8440c0100c01c002c0410880000364154400d8000c2e0414038040d841d28400c042da10501020102c00243d070040058101d0140c6102d80301c14501440c501914543c01603240c8008111400781c81da0542190040e031070141c903e070001d500c13070300c044c40140d010b9190002e0100c0c207000001056240702c0d840184403900c0042000c10486140c03020b500740c4036040e4005500140c05014000e442d03040410004d204102c02d0f0300007101090743c420500c5010300000e084c0d42d10552441d00c40d40c80e1031392550084005850300400402c0007990b1007101d00020740c0301c028034900d1805840c0d4001400842e90400707008503901501c40185590b02d040030340c2d0041100419500340140e4540010501d0341b02c0e400994003851164400043c0c00c100703814043c101b140082d0711a84030b80c0c1010740340c0c0e6403660710031890700803030710601400f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 185798866 1250 185797616 185797621
    0x120306040207080706050405010b090c04060305090a020607030c12050712050730030e0606090f04030216260115060309020f03010f0207020a0b1204030f17010312020d09140405 77
    0xc02a2207601c0000c0c00e12040420f000040c09250b91005c1d000c1c5115030020050804a0700610600107401c5407a00102c0b03509000400c48580290401d41c0e0000000c0280e40d0007845c5a070010b08140c011000650002d00c503801c2c9c403420401100f0b0070f880d070308100b410681d00700316141d6030f04d414800818a9600801002090810030002548003020071801c05500032540803201c02001098a0f10300980f0100103418908031100c2e144010914600800c40a40351082942d10f032038241e168188082d0049003140300b5024411501c0382c1001c0e503200a0895031303403415001006052003441c030359662061050240d15042449a4841441c5842030441c2d4042c100032400b081d083c00080c4e01c1c0200e000007542c055081000c0440076002c5540100065442190454810341d1903a080e101d450192141c07450703c240c4808007080c0803134040d05002d024100c4903d49011250f00708604450158001c1e8800c4444400c0c44032000e0101d0303014402c910620b04203183c04800540350001d0440528200d403030075030066544101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 185800116 1250 185798866 185798869
    0x2010f0203090f0d1103070303021c030b03120f07060608030a0e03030a020d080702100f0501030c060903030e04150803120f071b0b090304080f03070b06040b0904020405070e100306030506090d02120306 88
    0x81031070100c5c0c801000d0710511641c074140030b9141c5004c8902c4807a0307444d5004c1480c400d1402403003007102c44180640141440c5090301254182c0f42d00c40b5040d04d0a180c0e0070300c43d003400290180100400380c174082014549a680c0200003400542c0580d031081e04c030f600b00344040303160f15500080211102c8098036045125489016040c0d0034109000c15000b003240c2003100c0208100d0041c0c0109040328460144060095a20704045038101c50300d001c01000150b1050140d01385c0e2800d60040c030310200244003d0003505594100300c2e03246a00c20300d90561001e04030810054100503000c01160b00000506105203050b0140002a18802c400a00100395004103030215406040c00c2082e507000d0000201264448000c09903e41d0343c0ba000250129040761400d4005080d6060034080c00d90080806040504076460715408c21020b04002000007040110003400352081e9a240c2ea075220764051142c400049150841c1031807400d1650041004540c0d50150303111189440d4001a0020880341502c90942c0b00d031a040f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 185801366 1250 185800116 185800133
    0x61d06031509060f270c0c06010905150a0e0f010b090604030311010e060f1006020d0807030b31060b070209060d030c02030619050702070b1b010b0a1202010f0203090f0d 74
    0xb01141d820404440702c1088072444c0120b00e500c0e84080d40380017082e071381c0c0c1c0b148180800d01c50f581083d1010f0300301000410205e00c2c250040c0d81c02040e003401c81006192302c100440e0200d41c0c1644201083c3d40074106000b03a08481d030340020301400d01d5030b55007441c2c90800c3c00424854892444000c0c1084503508001d06a000300303600c9164031003c208141c41e01420900b411501a01c0c094544d4a8080341003500003a1107800001d114088804580310140a42d58103841600208090070381160001c4480e100f44003014460b45410388001c86281105040c1004074500c03404895a0350026021208204035520140e07580840442d0f02020072903206c10458828901140d10048008000350544116402d11901c6c024440c07443c40a00c00b80c0303a0070841503540c928220381d205418403840480d038004100341e1b20640b102038500b0950040900000c41c40154020100e50004025400005104420401c035000c56030300c0b904005e0110a248011070504d50070f01d000501d00412012490700c075078402d001000800c400d12 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 185802616 1250 185801366 185801389
    0x5040e0a020a05100e10020106030317070801060c060912030f0b0607020d110d05030a1e08070c0b070e09040c030b01060f09140d0602031801060503030f030406110c07061d0603150906 80
    0x6d454040d1200c0340d00c5020f0301078a02d0380400c0340801d6007000034040e402b88a0383c51521852590340d03050901c0e46030850540f80003c070000c1c1079030500d071030b1f01c4403101054145820000c2002180d400050728020360101c6811a00420940c520802e4104544809070340c55010707118003241c00990250b107030b03000c0f000047c248600c1c1c0c440080441c0000701c1c1800300e0a07001030b05c941070ba018084003090808218207040720940030031944000490036026006004c58011051107601035501c1c103045901018000c00940d01c0750044400300d4649120b030700c040c002c100c80044001c0c01040d0702d0401c8203050705041c2018102140ca4081e003151a40d1714156240b080d9110350066a10b160005400c40d500d04002c01100200b40104d181daa10660910034000f60505000044481c0300c00e44000c118207540b20baa448001625804003800003e610502140c640e0000500031080100303502c3d101c030050b100c10000711000705442509414800e02051080010042c80f040014041403070448044105030303280400103040e101003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 185803866 1250 185802616 185802619
    0x120d0b030a03020c04060b030705070609080d0e030d06061e050a021603030e0315090c0d0606050a0f030c0f15030b0103060b0c03121f1e1206050105040e0a020a05100e 73
    0x703881c94001410740100740100c0c2c2c0d960030789040c84425103074120b1008600c07056640c4000207608110443c08120140d0000084600c280c1c0e0389890400c00550100c183d8200030442181e6030000070300d0b03481403080c51040c1c2e00105400d05100c400a03a100c001100300340041949541400750001760301280500c00d1110041d0704514000180086459083c0188400017046400d4060b100d4900441c210311038607410648200e8101004100b0480014103114120014841c00c031512070702c910300881d46685050810300500300503010403180c0d81c654101184103400740d910180c1800e07500c200501c1340b010955020180c0c64010308000c10303607051510040303004240507880300c0014000405d4005400030044010080c03480e50981c2800942c440401403062400e4030701d01c0741c81d00c0c00c1c48082044100c0d80552107460000c080010542d110340d40e102002d212200c0702008680e016501e0307005100c40d26041c410318111052440040040d402c159000c562811080d01403e841008607414407005c4da07225160b007803038803c030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 185805116 1250 185803866 185803873
    0x316030308090a0512090315040510021308060c03041203050708011a161110031103040209060607060e01050402012d03110702040e010e06061c0807020105070602030708070908010e120d0b03 83
    0x141c02c04185e01c5500309421080c4607004498014a03828030741da460600458205000c0d01204107a00c401c80c009500c24840009143c0c0c030a03900040144d0b040c0300d15845503004404141d41ca241c00e1400c440c1840050243d0002d2525100a1141e220b0b8404105410f40e610100903001c800310004007004140541c0804416a0080b400342d1383c02c100002c600765504500a80e8001d1402c6450602501600c102c1c2885142100d070900005016107061540c40390840340c094961494452543c40d03400aa501030b802301d0000d691240144000c559020410011580701c00d807001039160106d80702c00340200c2080d003031407003010b4540d034506038944081c0c4110362150ba4001d008015000c0b80b01c4211707000c0d02081c201916180200d4001544130308009000700b98903220144001c12170742c40c0da81d52030200c0e00f2032001a410000e06000304c10001f14144019030080034281c5540c5058070342150001c18915051b0808081039041c00d003400155840083c80c1c0c0003903c1100f07440d075181e0306142151002415030000d019414403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 185806366 1250 185805116 185805133
    0x1109100314070806010602070e0c0a0e130207050709110712021c02060f15030d08041e0b0a0f0b030c0d081e0a0e0109030308011206380316030308090a05 67
    0x1071002660368112480c1a0544503d0303a610300c02a42c41e10f180b4400c040016504500252001882e580100085221810042d11400659004c590302c0904c0d1007010400c103a0019049091110030003044004100303520b000d02040d0541403a207a40c0c1d020f10540240407012100c0740c0e218007030003803281040c100300014110203070b0000440020341e070320001e603060301000b550980400c03d44240c0d50303481c41c410ba4000d00200031800e4400000c80f00d01074014001e807094800b80c42900d4000600e4a582049140680c0701d104032030070810381401c215143c1119180210389025246161510086994200310000b142c019000803000e0402003050f1281c00032400600f85000404002c5004002c05410a0051541d80f1200000340c14015601c002460102502140441004012141e1041010300031b0a1052602080e5503032080d480c800c62a030a000c540800368000b560541d00010501d000e00f860840031001004174481801441d004803c2c240000341c1000380100002c0c0741c140042109088541e488012200280b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 185807616 1250 185806366 185806403
    0x1050a021209010c171e0c0c010507020109110402090109050603070c05240c0a12090b01060e0105190503040201020a0b100f05010c050705120c0a081e060411091003 72
    0xd41c040d5149254000d141030102c1d109041c14419442642200d071100040b6495802400100d20030090842d094003600f607200c0440c905446690a01030700300581c8050311034103120f520b2030035601c0c0104401c04580c0b42c451288040344100c07a00089000040e100140d03100302c294012034500f000c85d009690811000020f001000340c1c40070100644a0044058990721443c11900d0300602400007101c005142c034040118003e01c0c005401070489060500703003481b00340c0403140e00d10b0544003880016900403006e0401040b80d44e81040f60110040d80034601103141884601b0751001d82c24020910f4010007102000107411039000f0000c145407940c2003124a0068644400c0c0a940441c03030b40184142c2102480700043d495010701808900c040c2d1081c046d200c401d0600c030601911041c000c030003291034401c1034210601a207034034400d00058aa03080280c09400001040858400d410300891801c6503c02c400304404a102c0b040707400410401242c000000e0380b140301000040d11556000031f040c0401851b40031440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 185808866 1250 185807616 185807621
    0xc0f010504110a120b040201050322140d03020f12060d0c0807050f060a050a080603071206021308070e010308030c27100f0906200102130306060b07020a0501030b04090501050a 77
    0x30b6040c1216030a52840d1034000040200350481030041051000d80c0100b001036026501955010b03015480310300c544044420099542120480c0664404842c1d00701c5803901501401003c44403c024201540380403a890000101441040628a074462911000c00c50b181e03102100241100d400c510004103171070300c5400c5036865548511070b07688100d40c000c030795110900b003203010f407003280d8900d07100c840c100041d648054031003072002080300754140920480030813000d400300440c614150086600513290612040341c03081c100e03100e403c00d4907543e0144104002c400d85656440381502e500401640d200e03290092a455075000344c03295491010060402c410350f10043d92004603024100321407000e180340d4207106c140c3d09079408130313403540000740e01d00814022503001f100c021450308580c4a500e0ac103281c4801d581402c90300301804658081401c1c01040042c40100c0c00f5410203404042c15146c5401d107a0340c0040d82001d0184142414551a641403050582d00c517804140c8550700140240b00340e14004458800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 185810116 1250 185808866 185808893
    0x7060b030607050a02010608060112061505030f07060201061d160315063621020a08010c0906020102120a1d0d0504050a091104060e060c010c08062b06020c0f010504 72
    0x40d0701e02800022817400000e409412105622014802d2901c0e98a07100e00dc1d089080c503c5100c0350303d511002500342c4040050060f12600c26020303280c014200f406c0282513a03100d50180201c1c80210400031151014600350320341004c60b141403c040b5568119090b0007501c0c81e5005a40940c2421500098940e0041c0040b00110000400072082114800e20030b40510006406602e9680c10840d06100720140ae504180c840f85007598400141c4496500041c2c001d5010b0f000040d0036511503141c1c0720b00607000010744018006038002982800d0500314105a540e00080c000c0d840d03151140828201250ba0404000c40701d41b41d082500c3e031121190340e0140c2503a100d032080300d015140301b41d00003843e034034a8030840758406101c250142c40c0500d020300454042902c004141d6129008008201100341d091280ba0308081c201e4031000d02c00d1400e44104400000708540001d40c02040c107018a06948851100510155026100680751030020580903e0650346082c0c0803103a41c81c0505000c00c0c4440880f0045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 185811366 1250 185810116 185810137
    0x703030206040c05120a0803060301020702060d27030c020d020a030210180906030f0803040201170f04020f040614090c0c030a020703110a0e0f04111503040606050114070807060b03060705 82
    0x7074010340d845050003941c0b000c2d160125032a410444010300050002c01c011908408024005403c04dd11600003542c2d6901c071841548038aa40c0710140c8040c001207011141d400729201000ca09245043d80f0060410003000c50024461000c08126000710350714401d07808059070f0090700904420f43c02350700207010702c0e0448016a00402c43d920000804600c20700440090b00c0e03120a030b807441d01c600c5503200c10568001401c101e040c803c07a96130318041004a415000d12900c0c0403d0004154103050040c400d00943c0181c00038083c5082038410f0001c45100c2c2e141201003442503d41d07180580d200c80c2c004010340151800c0c4200c0e4040010b04110b21a030001e030078400d43e401200c81505007885403041020000c01c620415001d111242c002902030764540390b103c0d6225000320202d0f01c20300064000205495501c83d1328045d001e1000c0244001c3c0302e03051052402920013030801c04814410504010103900606000400505c00010400c040201e82d0300040c0200d4006000c803201410030300d0700603090342c01035174252 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 185812616 1250 185811366 185811383
    0x4020307080c1509030c15030406050a061520011a0f060711100905041b2c040906090c08070e0702010b0a090b010c0c06030203060f030c130e0708070303020604 70
    0x490380c5603002c140d0103900840240901c032002a20b030180c012940141422603414001c4000031580303030306c1c5d1005440c0000110480b90750b0f645010705d808401c488018000b074070240d1074450140030458039408010070541690804064001c0700b00c02c10200e9415203020103055508014880789000d82408005000c0d5508a81c0d81d0340051a40c030a11030a401168006801c41803100101c00c028146200b50199180c0c0314505203c0d09900e0b40c0128007618040072040400120442c00200d0003580b142c0d01003c0c100000d0f504140c50111040324084128280000503c01c50307a400e442410001b5503404003281d16401842090f0130b0766580840c543b0382e0030340d2040d40c0f5a0241030000501d49441031058850540c030042c410700c15582006d00072002415000001418020b0810382c810128809000c1c2000800e580d42e00969685090028000135410b00441e9070700951000420744066900c0c400043c40300040340c10001040320b0003c0ca210300d8074613103600c5981e4500415001009069020036294491401101c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 185813866 1250 185812616 185812619
    0xf09180830070f05030f01061112041509080c0315060103020d0f0c0f0c0b16030e010f090201020c030304060c0f1b031101020c090603030910030e030d0e0706050901090b1c0e0604020307 81
    0x6942c00c5c8402c030ba5500302e82daa83d0005206003409038802100344840303c422607041c10b0080b0441840e030361040c1c01000d078290307002c4c0c01142c20360b62200c1d8240107050000c018014150503d40840d66414001203030380f950584c04800100c69900ca0b074155505200e444c3d0051001c4030081c060340e0010300d550301e01900010a20b605c0100785502954011907041d13844203404455541d1a4004841041c5401003101011344550701e51508031000d0084182c0565442e01c0040c0041075032001900d084448416207000b0303002804204403441e001a0000540381d001410780c0ca8183c640d01e44010120140c1c480c001c20034840d0000030080c4400415802801d07003082e001c540d08162504c08001d410501210001c0e41503100f0420f40886041c52201040c10003018280030443d048061035050558001040460f201b50f40c41c041c0b500d1440b4100240002000c05040051420300d440c00020003010761402004000307030300000ea51007640d0142c00e0f9000030170220b48040296014001c040c60b01c0b0002980d0680c801d10500d00c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 185815116 1250 185813866 185813897
    0x90307050a0b0f030606090934050f030c0d060803030109060902031b090109030c080c03010515060f18180109140106020c040905070b130f0918083007 66
    0xd10742500d10b01076005082141d00c1000b0300d0207620090440da0080801e00031160b07a6264003050500030403582c12a0042c591154440d010341c81c3d50344100c01c140080458140c150140c10a04880c48940d2a450841d52961140600c4040b84180d4013482c0005140080009280c0d00100203903041c0c03401a1401d010440d0789505000590005640c40841d40c50001d00d0342824400c0c0000500300f000042c1400c40c041640da07100c0c00080c1c10036601140c4290020101c004003480c0a10480f80c0c0607500550100c090b800d0b05020900d10f00605010128626000440b031100010341c40034030b16145001010346030f44885030070403007109900a00c0755641890078802c0410f100c0c10888000c5050300c50f0341d0b00a0225011410810010b440301c07038400c0d115402105c2c0c000c90720f0a810001011840d80a0000c00c901c14680f1418004ac81100e81c000e2415914008c0b0740c500e40c0c640b100c502126160801300403512540c4116100c0c0c9850b0103061000203d0f101d0018060044011200c214450410f540ba0f040d210404200e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 185816366 1250 185815116 185815129
    0xc02060403170901020708011a2e0518010c0b2d1006170f04021c0203010237050409050c0c0109060906050a02040e0f040c0308030c03010801180b040b0a0e07090209030705 75
    0x303101005450341070827019620300307110044c00b4003c044203a607540c000902d42484620500c1a06249002403400034140407900030841c003400d501c3c135081c0b91000d5511704a450351648404058410449550012117090b0040c400101d00d10a01d001c505c810034240c10038881e00c0594180030702c60b645c04036070040c40c1c0c00003086420400c0d6115541c00a4110758959444e0f00300070000c402c140d445a9100c00c814441005a10244003620400903207000b2060151940300d0300040004035100300d403024440085080100992020554040340c5102001140301c5e102e62103101d04602800d5103203215076181018100502c9070b143c00c18600780b80110301c00c01041c0c45000c103000c264803490103402a0507940e000070a0822680c0e41030117520500401e182507141d03032a540c1742480c40d03005403180300400c880440140305409003845007289d0030116100c0940c20b00800e50300c921310356100030009860f9021023000900501c03103c1e0001c3c0c00119a04c41134078501c0d034031070344140000c1d00210f042c940a07118820020500c0d040c8030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 185817616 1250 185816366 185816381
    0x507060c080316030f060f05090105040203060307120206120c0316020303060d030e030a060203070c0b0108070e040f111c2003030f03040c03080d050105181005010c0206040317090102070801 83
    0x81c05949035030344070316022a00d007180704210710825075508420590160130f441800c000c2d12103841440d086070b203841c1c2040040101a00024402c5104000784102660000380c0241220481c911901100c0880e00010b1841e0050851240040664800b0030072030343c0c4080000d500c92900d2a900840e00012040102e070340b4001110542d40104484040b0404039014159280310b03000020112200c1d2110be54550007a40c000703884038008140034508590820a01051032809812800020014a0700c0d0030780300a0300c841e02400140084841c41d09400074400310310200c886000001e004800051006208075500b50086201650f4102c4a081426a1100359a42c00721801000400a5040420341d0703019a0f981d03880a4411503141003030320400000100008054010055401c0d170000312585803c0900102d40311406003910410307060010800205200100031042d00d80a18001c401001644041007044c0300300e0700042e10403508482001d081c240c030380000b014000000e07420389001c165144441d40c00c3c2c6038075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 185818866 1250 185817616 185817623
    0xf14010e0d1d120d0305180a030c0b150a06080a0f0603151104080a06020409050c07020904110310090602030402010906050a1e1e020105061507080d020a26040507060c 73
    0x10b64802a1101c2040c541c41415180300905040320301450882c0246090200006078010076100e104000000f00c5a200303412003115100007420703070360865076401003da00310070f80020715100000740481c00f0790003681300a00b949840039100c400c41542381c00006e841c51000f241c81e5000507040410725418034090b40991000c485c0c5c07020511343c000011440c0c02019024450a01814007424400055a00e03000c100141643e4040d442c01a0340c1c42c20031040e80d054840082011200b11000c000c00001070300c420148650086d00280254070301c030346200000c1c1c200240500b4405409050034040403c1c80210343c01540070300e100362a00c2154a03551003081e1010f004400c0010003198502082c100e07140c0034032000389001c62440c900280303503950360b1310002260070b6004890720041c1c0d0b4800400c1b0060600804401400d5015807020b402e0404503a00d1812a100d8120448891034010070046141409495160341e071410003508181441c40800c2e801c1d00c2907008440c00d6901d44203070781000035000d025900401e0450340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 185820116 1250 185818866 185818877
    0x9080405060711030706081e011503090204020c03130503061810050403200105181b0d171209120f0a0815040f0605010e040c08070c0f0f14010e0d 64
    0x18003010030141d03030401c03102602c00b14505184450b9940c0c0034404417000d01665145d000b00d500742044a002564000d109204050080e040144036040e02c044000511021601e80800c42da41c83e440400d02a0080d01e03100d041910000c60b20301c00c0011869015810380310107400301d034500c0d034070b14200e042400c100d22462030058006800301c0f5070819603a0001c1c5d60141c02800c01230b40d904190f19100e0b031059901c0c8600b1720265514000e0243c0c4048100880c8181840f200003002c040014103a9040d800c9a402b41c010b10808080e5a07285c2001203074070030000081000124140c45902e40c030101c454115040780e80060f07500070183d081400c2001e01e000d80d80300405000704107042c407103c42000d450340e8801a01300d41d0b5401404824034041d59030b5020f04070320044851008904c0c640b03000009005e010752071441c030340708a0810503180740c05a403103110294400c1b03145c82c01c1a040c00d6030b42080305060301a04005450424503030345503402d02900b180c1201400c990800208610105013440c40d85682802d20540700050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 185821366 1250 185820116 185820119
    0xf0405060f0d0501060806040b040302150115031d010203010f0f08030307050403060903051210150c051507120f02040501080a0e0a03030b011101050412300507090312030b040f090804 80
    0x20400c5100148600c078070f000180c501e48402050313140102c100c0d42115004ca40380e041000b0503505201154041807140742c01c050035414080841000c410a2140c041010303510141081080c0c07070180d06403000105c0d000210754a58490003451445411070007035101450090380700280440c00041101e129031210ba6445080c10709581c1c1d00700c00741224001c154100501445950207401001e48414010f000225a20740da55251080f0488400446070002080c041c6060034000030aa0101354070b05084d1900409400642d01d44e007044c2c620750140c070224a1407515060390414450101d600070020350b04c00740c880c1d80580d6552440350003035170342c0072040025075009692800300080c042c3d042000d02e040d050520b00001c404541420b070840310100c409403600100c50340c0001e40c5036044810302c200c42440d10ba81c0c804800358080ca07d4220302d4400542c40903aa070f0707000020034443c440c94294001e16446420081301000901004010702034041c02c1034801e501d404189101c10f2070300d11480c91034590041140d420107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 185822616 1250 185821366 185821369
    0x12051501060504050112091a060301050a02120a0b040905061e0610020a030305060402091207051833131506050406020c0120010501180e030702090f0a0603080406020106050f0405060f 80
    0x107143c14007808860307d8581c4880800101a901c0d184042400000d0f41d00c0d40d440c1c01c40415003950b0000e40305481c1d103881007007650801160105440d41c402d009140c04903040554201103001000b2840c0701400c580035941c14020070301c001d0030b001c13074242c0c01301c0d0003c004e5a160710080040380c440d0307125070101681c4120031040c0042d020b0780001d40d0004008100504002c05a0b010030b00301c01800c0380300306458112120038040b6280582129610401048285c1441d2800c02d50149400240d4030980142503a035103040b4203902a409071051074610064044c1107105060301e41913018183c200c100000442c48600702148140c400c6090b90101c0f42c0c0c1c0d5008040b011300040c0151021080c03400f10625107482100316046d6481c003402414002d100c4800d0018a0201035000407044036414141e0b2001c94004100340300150b66542034054210448003083c880545502c0c00e40e80050455034802051100c001c1000141181c041d48840112081540c00310b8841882000300011920211201e036404070001506e110f25 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 185823866 1250 185822616 185822627
    0x5030d0504230604181107230a081309051602030f0a111b011404080d030506030c13050709270e16080106090b03010c080615040e01120515010605040501 67
    0x180342a07400c07504041804007080090340301e6040050129031098502190170b5603481540c0503d0030012800c0d040c03490658940c4004031106100c0d0b80881011210f040030010280305c60b802069000342d0241e96140c100c000f450b07040b0b650307104900c07041d8907040000d1464001c0101c00903d110056000e10300d050450014440d094000d2a452401c00c034074160300e00c80960f0200705a910600c070031019034188003800b07000140fa03000d00420b08410714409210030001e8600c0080e0f60600000b09080200b4180c2e90703480442d15183c4045615035004103a00d000440c949410b50226000d82055990a0030254613207041d81100303040742c079103000e021400e0f03584031442800300d0348444c401c031100c2010b0310340d07002501444291034289500f2801040c0d54401d0208050b40f03442c400c41c403010009400a0154220340c070005000c1090040090b809a8031105a00d000c14140d0803c035406011540c00614041d6103607d10a10020401c40d0300300e070b00c0c2c402c1d501401c020700003242c840d82c101c0350903075102031030a400c0c5001140e5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 185825116 1250 185823866 185823899
    0x9030806100f121518020c010b060a09050d03030f0912020d0203090315041e08120709030f1b0504180b060102151303030212090c03070b04050a06050306030a0209010b0705060105030d0504 82
    0x20941d13000a404540281001542c0a01c01e445000268a81c00b08456880c2119001c088080c81178400b00300f4400034a4000724080219181100d44c60200e509609042c1c0260105046130b4034042c1c50200c0003030800c04005c81100820030940c2c219112240e4420b41a82c1c2ca100e0103091755803540c40034a9407c8480c00c029482948a803050400b83c20f0141b1040211200410300c5000700c7e0038440118040303009007007050350517910040078034047c005140b440d00c540250b00d000704009444030307198240c60758903000700713000840041001900c100808403c00c03068003130141c50b413802106d240f1105408250035601c001011070400480940c850b0580e1a866514202c000364820f0840515800784041400309a114809070311450204010741050324640b81010f003040701540258603158024030041c00740d40c880e048210151080d906100da600e03212200040c2c501188000d00030b41c0814210004622481110090001c0a200d0030846485903200d0701010b0300c5a05074501880041c030b043c441001050040e002650 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 185826366 1250 185825116 185825141
    0xb062d03072f06040b0f07020a080a18050a12060b12070b031b0d0c0e0103090c050103020706021b0c130c05071205190503070207080105131b0909030806100f12 70
    0x708485400703030420300f4100e04480c160741800d5050200700c80c604031011925800581d610107070040903819640e003c0da41c05200c0f0210104004030b070031034105110b400010300240000a240001480d130b80d0070341c050501089042203d8150030100004680d0501c280c02012050b1054041d0041901342480404d1035000184104840300c1214007150906500000070030415603c0c42d0040745910347e04034060b201c3c10f0488581410940307002031440201b84e000040906844007403801607550011410484040c2c01045201c1d03e02d0705140c0c5c40d100ca08500001c2d003209900f001e5030030200030715900c058101110030b90550600441c208120070000a0b0003030240326882c03503090501c5030518040706200102c0001100700580420000024441d00d0794040010100401d100310080c00341d440c01c0c0511118503000c0c000001c01210040d20503450000d61003003954040c200e921010410003046050003003c80e20706441140c050842c1503c0128800d1042d4038803540d10031703075451300c0c44100c100308801c500a105008150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 185827616 1250 185826366 185826437
    0x11409030a080702100608150705031e07050408070e0106020c0117010e07050c101e090215030a0212100603060f080d20010e06060301141017010b062d0307 68
    0x190b80c03c4040303210700009084481f0042002c1081ca458103070745103a01030001002e0110a004006490120140d11403c5014031200e40034a0345803c4030580b2a409a50007c0020740107103840411141c412802c8141283d00a1740ac5402c2980d40100644144107181c030380354500c0651f00010b220307907180c90901035005011846e00a14003000d102c00603003808940700b845e03a50303036480709642c8410400b110b9200e030580f04d07a16020025103c05a0010b11000c85551450381c00010210008140c0300c465416207101442900440d003080c85c0802820040000c14001c2c00c010920300035020808031186000c850507941c03268001e209502c4820710640d0660301c3c0240500c4101c180c060004000c070000c1c0180341c2c099000d18000c00c01410301d80201420b64800b251681e400000020410450f50f010881c07200c202c0d03680c40820b0030403a51780f0259034054041144203a07001a000103000b00009c40c011652104000040003046500c0725402d000c01c180d11060b1548800240008a580e6070b0340351241b9508201100307210361 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 185828866 1250 185827616 185827633
    0x318070911030601020c040203090304121e0b2a0d09050f1f290607050a0609080913050c1801020c0a0f03050607030504050607030e0c0d060608011409030a080702 71
    0x1041d9801c00c96400345040002c82800000d580401c0700000c0070000b10b5042d821440c000e00410343d80d0003248210402640e00510407030610043c1c0c2c85010700010a003000346810307a49810300a02000c070903160002c2c860f00f050351070890305000c4400462107a204800311807403c9004c0d10454082c0c640b00704191580d000e0f46088180002003000100c917003000c03924140864502355009882200d03081040c55007080300c02e511200f0650304901c440074410341c04440d040e482d1051030415528020600b00001c00c40342c9403403000f00c1400600c80c0901403a01c5c04840f45201071010344544010759030241ea491444600a2201d007940814080c91441e84030011703c1180c60303590090000070301d8001146d20071004010f00d04018400d01c00280303c5180e000000341818001400d256441c240d9901c00140075808260f07603a000c0c1c6041e042c05011801e103680340100f07014448071060a015005241c9807299080d03640c0390040c0420f109490020062080c03500300003039410200300034406e45090500a0810f030440c00381315075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 185830116 1250 185828866 185828879
    0x20c03010c110d02070b0702010315030b042d030e12010f0212090124030803190c210b010c0605040c0b070f020a05090c18030c030d02011410050105031807 68
    0x9122001c0c19981e41e240003540301002028208007035a8040c0d0110340001400307016400e814011514801d90a00c3c0000b014560180546200182a0401071002d403034003052005005100d130448642541300440300010302c44085807840c0281c07140d480100400da61040741a101e251410b0a64000c1010000104071045ca07102c0c0501241d01c03030300103e4a000c0b40340302408200c00c800d203d003000e05090200341e0301c12400000d04500103488944002401c41d00c1c0000002d0061201502103c545001e0000505c00e482480c0c001802c941c1c07210040c40c4035840ea4210040081105002d0841c2c1810180c4a0000800860303c41c05c01a00c0b00030401d880203a000d4500240b015802d1005011490254803500000e200e00e20420280c18541da1001d4800c2d14071f0401d11504415100407210441c1285241010148000d404242015101c618140d81805042105800560103401203040c960010510b90580d5440c0740c0c481000030614040d06e8001641480050851a03880c420304102910b0384c021580615500d08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 185831366 1250 185830116 185830121
    0x614121b090d03031508120d020c0a060f02070201030b0319080d06031b03170a051603090b030106170a0e0319030608030307030f0b01020f0d120f05041419081207020c0301 75
    0x240100e0019988800d00c5c00a8141c482c4d85a025140c0c1101a2500002c000c090032200e020b182c50003102c0607400280c00c50666000c1110300b0503254402402d00402c0c885807a02c100a40042c0d41c103030b000c030b41413402d40c1e4464a40881e101034555680c0c429140f8843c607548070018035170080c81706050328070303952140032000c10780b000007542c003e80201b6a00e042c0d050862511580110300040420400311040c040351007955001b10650702440004992400303200104c0c10121035038401030380700c400c03100c500000104440ba0b200410309071320300d100405210703561551070f040001c40c0e4110726040000e400500184500c4980c020400b21301200301c1ca4046903c0b5160203410381140e006a800c50082559015200f940d02c0c0360340580c1001c08400d0000c2d04040940280c030f40d445240e415170250401c481242401c8103895550700404080b0700480b0204000d240c18540110000c01c820b0703804409215a81c500d0101c5c440384181b000762194010290381c14014280e200c41c5861070302a1100702540250711580c000e644092 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 185832616 1250 185831366 185831389
    0xf09020301021815070b06060d0f060b0309010b0a03110d1506080105100501020c010f050309010212010308040503060921030604090209040c060e01050702010c1101140406090614121b09 81
    0x141218118211038400300a108007500c00d0071381003c0014800d80c4041030801042030b6000c8001d0303030a55510022005020001c10241400c00b4240e840d211000c99400100710140d481400514020009180724504008112800788002481d540881101c50400e0408100a1580e035115031500c0112940b00007881d420355a441d002038810360340d504c041048901e0158030b90340007480b003030022700042d04403d070000700700005510040c8240603000004c0f4182d0642541100e000309001000000345584905e801c4136903034020b00c00d1512901c160b8000c00d000c84c01c0401c10241402c0111980c0c408640740d1800480f16030001010150300c99a240140d10240c0ca880118910540c40f0304540c89113542011005002d110780f00f2003040c1000b006100e1100141d80000c0d400c42d419412160702c500034140310004940da40611440d001501202081c0021440e4003d0042805d4403841d440c0d00072086084107015140d8000d070b129540d800307a40d02d004180c0b003445238664078000c1c0790401c1540e8903200f60303003000ca412040300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 185833866 1250 185832616 185832637
    0x6160c0f1b0e061003152c010806012907060f02091201051506090406031e030f0507081902210703200307021e04060e01080606040b030607030f0902030102 68
    0x140400d2038140a0755240500180c025151030071064208000802d07034180440d484c1e5070505607030301c0c60255034102c0308a11000a00f09242800351800c40704888080a440704001c400f410301030200081080040032454506a030140c41d007803080100c4211410303003040074240d8442d00c0300d8010441207012408074000c45100c0500802e000d81d8649003c01400402000c2410043d40780c2d1400302400444850824000105401254174945501141e0002801440c90b94030083c14484042d41e4030f025800c00300001c0b06030034000d40f40e05038070401404040d5450301c2480401000500d040048880c002200c50b14251110303081d10440d2031482410862440380b5144442c0c00c1549440070075071030101540104401c0480054400304001c11b203c94608541ea0b010308000284942c2144540c0389018001070151204104002d0090000c6c40e076624100b20409028010303902240034500008609060a000e042c2c02080080c4c024a0726070f03540f0310300710f004107034203040301c08200e8845440703c0160b0740034000742c990180c6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 185835116 1250 185833866 185833883
    0xd080a1e0309031211180301021b060603060703090c060804110406060504141c140f1f140403020a1b0f0f0e10030503040302150f0c06090c0a0806160c0f 67
    0x4041c00c002d80542c0702e60100311102070402c17100f540e88001210076181ca0080b010130004124500400090182c0224400d007030810402003440c142c6040b002a2480c0115815001e0780c03a1034860107c1201038a0740e07008050400d403449841080000d00c00c400a56025000d1071074400c0000341500010142c95403030b400040041c50100cac0900080da45008030510454088036034000c425218080480780525a0200ad02004d1a01c2c0e8480d201950500424059007000405c5d500450b022500800314107038811300b0a60700c149040340203940c0c902d101306898010782d0503800505c81300300140c2d5810003031a00040c4196000000101c0080d0003400f100c020300c080c0100d002c00c00701d2142410500e140184009100c40904002c0e0601080401c00c0482203805490301502d03070301100304e21b00f8504841841064403140b004400041c176412203c03004902540540c0490007603440069030002000050000303070040c40002c0e040340011070f2101c820310541c04049102424529401c0d8490307100d0300064a0340f601c054902c002e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 185836366 1250 185835116 185835131
    0xd080a020d2d020a0e0402090d020907050d1103061c110a060305090f120f0304081606020703020c030c0307121401140114060424030908030c0a0e030c0d080a1e03 71
    0x480101180c049502c84010460804404000081200d0b06030b4445901403513002840c1c072003036242c2080c0004016006802e420403401d101c103000f0503a80c0003c003840c0f420303440c14010000007002481200d0203020014858480580d44241410308481850000c540742e8950080c4000a9114030203100018025510000380a203000a00e890400720340d01c201031580d4204140040754419000c064441e1004040c0d103041c1c40780c0e07442c50920b280b440740000070106074001003004c4081003410340003422524070130340c02c0e206c1680711001803580e030b006401c801aa040d04203020512080034842032079138643d8054403a000500401d590403900712440032080c1141005020700500002000b02d0041d80b219809a643e685403d10f41842d1040c201065015800e800c01100000242c079072080e003200c440c0b1504030018540c0c0707040c8041003000540c404c005190104042103164695842c1c0429141c3c2910000b07024a03602900c56a220280c076408043c00c02c0c24025180d001c1c0032001c645c0040d1585400c05a2000260b48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 185837616 1250 185836366 185836421
    0x10c0e0109080a0c0b0a0201020c0a12021006030c09091e080306120303040302100c05130e0703180210050c030f0a02010911330d05042907020d080a020d 67
    0x1024581109034681d03c19200070001405101d403000440f1919081141c581c2043c0900f03c0c060720034058241c0461103019804001c0c80091011900070480036002ca4440002c2d448089040c0c81042c0303c0075201110802c010030013810f141d00103520f0648519820104016540c411000c01c4039071810640e040c40002c01040001d003404101d10b8010b8044500550035440d06aa00039034448000b16984a01600c2e81c03440700c10b0178021025980100682a03000c1c1c41d15403a101010500396044a040c00024244040300891111244680c000c80c0d4014000310410511700c0d4043c0c95a500074199541103102c20080c4140c020b04142c054038800d4103950000c900300c1c0c00e500303119940c0701c60303440380612a2aa6402c460207002600195a0303142d0b50090781000d00010582540321180607480111204a04010400003042a030601043c09a4094444101110100402c10252500c00c40344100940e201160b41044030780200c8800d0ba108955070000751500c01482443c0091300c80040c2012420b144c216842e4040307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 185838866 1250 185837616 185837627
    0x9060f060801270b060313110f0a090e070302120f0606010305090c040903021c11010606090608010e0c0f0a020a02030c040203060a121a190609021602130e010c0e01 72
    0x40c4940c0c948800c195041c001804003000300380c10302d08443d54100061000482050300010b205010060540d034032071030005c003203880380040060100e6028480d66107100b800c1c44c2882c1d20750342c006000340c10207a5003030402000100418944200b04868425000004010307a0b90304d4525510b0303091000604000402899a50f1410401810307440c1410f01341806c02c02034080c0098038200d140001c581c08640c1403200e0070280d01709400e030840d0060400012100060703498201200721801140c40b03008128441e07075540204d60020740c6005900c00a6004030040001c01c040910b020380000071000200e1501d08440141c80041e804015100017607000f0214480075407400344180307000075905035800d40c554a000300001e6401d1000340a101c2100e180046010180003e21090400c58580122001c08a0901c482c9040400c07408501c0740e00c0f054108030740881c0030b000c0c6002b0349054445011106031083d2065080043c0d810600741804c0302c05641c0c0c22150826282405401034183d040d8590f00c5080f41f10074001402c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 185840116 1250 185838866 185838869
    0x303020f0d020a0809040218030303070201021305090606030f0a02161104050a09050606120c0904031808032b0b0a030c09061a030f0403051306050301180c0f0f03060302040609060f 79
    0x654001c40c0380784010440403011180d4111003146c0051355070288080c003201c120481380ca0786800d44008010007011b10b030154000c0080d030702074610136500d0507521400c00140d14000c42e00c16401503814001326000e48034071803e41e03030007030403103407025060003501a042840c08607034200585070440104403c2d0341c5401d06200780c640040d0483c10034001d17401e240c1c42d10781e960a40503050a000300244820840400302c2840100c0c0510030080c41c0000e2414141070050880f40100c0b000c03c112071a1020008100100004030344540842d41d500f00307543c0300d04014564040c0d0030000421209034882d819403200740e80700c022480217144202400001a07040094030002c6030200d801c84100c11505a00121014040b0000d8950214507448120f0041d51245801c4074240101103a580d040300d00b031000031645a0700803000c4c5040c0d400320543d81413400c1c0240030b10019100714628880103d00c041003507403040c070f125000e5001600601e007070100c0d5175560395011030708440050744070b448265640c01003440517030b007000803d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 185841366 1250 185840116 185840143
    0x130608070807170c0f030f04020901050d0507030f170309070e0a02090114070206090a0305010506090708070c030c03090807060206040501110a17060d0605040b0702010609110901081e010303020f 85
    0x280c1860941d1000d050f9840c00c58040114100303a4001400483c0000c0c1150035008210ba03406849043c2450120b521260580b000c0f0b00c640c403050004507680c10b002141c030704181d8004004000c55443c0d80c8551036010003e080581d40a0705025040103406812402940141d6040c801000403c3c60000e403698407507800f916496056004211942090b82e02a8044260941c40540150380700441e1000030300070320075000d6858100b41c000b00c001080c032030103501442c45084103480d92801c0d0340e50984110303170a110450b80710000c9005201040c01191094184020302486420200c00c0c5130389484501d850400a50300807401a0b2003403007080100002030155184c072100c1e028400b07042120405011b401c202010f148208220110000901c0700d503120800a45040c0e00400d0070002d03404c003818040001c01d0201c5000300558284600042c400d141403240c3e0a0100002c0413541c00c02c91000d00448500c28003800850820b4066082441c07100c159621544c0294441e40040404106d201c0083c1d003025110300c0c00c0f8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 185842616 1250 185841366 185841377
    0x7020a0f060f0e12070e31030c0516121103070b04150c020405070e18100b1605060c13090501080319170708190e100513050313060807 59
    0xc10500da00302c46035890402960405080c0d1811110104502e10600500702e01c1038403901d100015407260001d8014003d50f030303007000608130058a1036000f1101c6540d00e035a918120101c0c41c45004a40b2031000d00e4607030303132194050ba50010104042c1c00304804054001e5415031810034464030400206101d603c1c507040055001d003036024904020100203005a10482400c0d4844050528643c0d11401c100d440d0254010010065030420260041280050210450150b5000444070710001880012180b03d013400405403c061420702c0e5515450760802c483c1e4541000025240d400012014401e40d48500c0403090f407151141950440c4000d0844540c1c81140200c1c40c2c4001070180e004040121108034032002400115412a05012508074104595000700721080030705100100b80d11810007801080601f03608400d81c04240c0c4104121a0040300340c2103075a008001041b24844107800156100c209003d805075135030308a845050071a88506410070000c00802d60a200554214080c540c02c0262403822 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 185843866 1250 185842616 185842619
    0x1090501030b1e150c1b034e0d11040806010b3709090213140a030c0806041505010e130606050d0f0c06050f030f10091107020a0f 57
    0x20030390204861a0030741c612007082d030f28a80c41d40c803042c142c2c07600840450b01243e80c5e10000a022911110381c80244540d660400b0040906442c00081c3c45003920280c00d01e6115aa0140b51141900c50002e0244d486000c021000340d5070100103014960a0303100d1754480150f6032410080d07002c0448800750851098814140001e00440e0b03400a810340c15142100307031856451003c0c005017400042240e603100100500c84007c03203205c040031000d8104802882d00c55209154840c141541680105000010725800303050080082003200868581c1408001c0c001c01d02454503602d424009060a810000c1603030311070410303c020410301014101c814842c1910400840d41070000d00b4461b103070003614036000341c0c0040e2060000c2c00f1242d44010000c01c0f000b441c0151440f000d10b0140980c110400c42074810203400280090520b00907011200a840040102440d55450720700d440d24151004d0702050074150300300b0001c01c00d55164880c800b16101d28901082c1c035066148100022045142c20a88440484190 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 185845116 1250 185843866 185843869
    0x105070510050c0f070303140a020406020c0103020912030403030207030b1e0a0506010e091009060f060f050708070501020f070b0604090b13051504030f0807050301050f01081302090a0b01090501030b 87
    0x1c0c00d0194801c880c00c081402d803aa504080141d0150071131110403031038009030300383c00c0540550000d048a10450041c42055480100203804c83c00303144501d0780540c12126891400d0f611917402000e42e03000043c01002101c0285a00d40c0c80c68000e608100c0142e03004060038024091010306041e4007080c05414055000c11240e40d007110080701801c804011a00c800c00b041c0142e01800080c42005406089035400c1c0c602910149203002c85445003c441e146030400109641e00c500e00d01c4802d4491350b44030300106080071081100d10f07500c10344042c0c88258080c0301c0c8000040080c002480c0202100030031039119911403c2c0a4903104010b0640c030703c228a8014554001070404442560141001000070140042410514101100c4c1500301d4010140401000b0405811445100c10241644d90342800c0f69035203c01a241848203000381a800b60401c50400e5041d031140000950143e22240c0e240c40488041d401b02d40c80d940e0a54800c000c1c1c1c1d86034105040f031942d0144241c1c0003428246000d0010070121b00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 185846366 1250 185845116 185845123
    0xa09180b060a03020319050421080103020f06300403030f0209010206180a020603130b01061106040204200c070503160b0403020409020a051509010201050f010e1602120409091101050705 81
    0x380b008040c10780100000740042c940d4240c00c80d8a4605803018000b92400d0720b84500554150040c4881c039107102d211805d41c1c0740c0300d901154123a9602a000c5883c26030300c1401c01401ea0000c8501c141c102161010081c45620302c803402d41403200d0005081300c100d04062070041c0554540440714200b0300d00c148550569680d001030030303a4100c0010414204950360200c0c000b403c11405400c06508200b001040c00203000d41030503500c1c1d516004034903421080c0d1321207508a450820f007018051441c4d2010021401614095100d0a14119019081010860015441c0055030030900f81d04030750350414403042005050611020080c00c404c51244111070b420144024a180560b010180c095aa1804081c046494100d0200083c1c4401081011004120320201001394000840300d0b00550824000c034840200054091341070718001d2188602c259103401030448103803518084081103104440300001c041710501c0040004d098030f180041100c9191b800d10908c2001c1700d03c0010b0401c141000020041791012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 185847616 1250 185846366 185846377
    0x203100218010806031e030d0f090302030712090e1e0a050603030a0309020a08031303050c0114030a0506010314100f0e04050a031101062105190c210501020a09180b06 73
    0x900f07200986481d1200420718200007005c01018003030b82c0142c003100340ca6001000e02560150b542c02480092041458081a280c0c0300c0d00c0280964418003500c00011010790b40d5411030b40c0e91f07203044400d0581d600550118140d05891480f00600040e0403089000c0c40500f0507940125414004d01c214186400400d507a4840c1c14500703410036030358003030341d508641c2c0e041031240c0207152a1040b00e45070900c2582400b0301f003840d40f0044440c0d205542030301d1804d5001d40707031510b00c4101c52a0f400b03003107a5628400300054000140b0690415640e0380d01c501e014140b0102c0c243c0980e81001c604024141485001e4403400d4a94110100e54640d620410000440c0024541c00c1d140e45807520f00c01d00e981c20b443c11805020240c0140b000d0008071405141c100341208018075036640142c003210301c110060f0f480d110100d03401100207000c0c1c14a040c414072000c1c1d080e0080198401480c0002140d000c041e0321030a00320380000d800040080c01c45c40e0100405404441c030101410b40c081c10070007040000b00e00080d402d1142 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 185848866 1250 185847616 185847619
    0x3070b0703032406020708060906010306050a0b04050a02090102071703040302190e0c070b010b120a050c091804050609071818062409020f03040b130f0606030203100218 74
    0x40c0a504040c0320350810140344041000301ea0070104030520712101c550440c080c4d00018070451000044401000602038003400084c005092203900310f4503a40040d00c401003d00320296147d01d99080c1513203c40c422544501a031020058541070b0003000203081803440c0e40900001c000c039841c240b103c2d44000c02140c046990440b2441240e240f441201c525000d8990b003d021560034000c100103c0c41d10a00040000e1480b4403500201d030380e00c441041c00c01d40a46001d99076288201c80000d01e00b41d51b15030085400984280482d0308100104001605540300340800c0307081c400d401d13000d220030010200202504005820040d0650504007a01c4804d2a200300d407100102a4441740e0044210310090411800503030441024490440c000a00300310000819a4003042403d0b200000100b8000520a5075003840c81ca61100d455501e903030f00c0c0e8035109180942000c80703031804d036100000011288448a8005442404045030302031550040506010f0500c0c142076034280104030a021a28002442d40f004100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 185850116 1250 185848866 185848889
    0x18060f0605220902040e06070c0201020d050a0537090f0b09091f0308120f01080607050403020402090402091206010f05060319050411061b06061929040b0403050c030106050307 77
    0xa0700000c5c000e4000c5c0c0403d507085014503000d2004483d80000d03800c4080d0f0003a0201c3d125101081c004072568400d00d0b800d4000a9001e008040380a02c010150340100065000d00611a00403803400d4164160f51243d1800420b603011070030401c1840e4103140600601c5c0d00f01040303080c0140e81c030115240e1440204148121605400440301c1d03403400c6800040950340103000103480c1c0380000d801c02c2e0130b040162003400d0240150705c00011101000166540b00f1046c558456060034a164244030182d04509050307548650240907904040d11080b06090410ba031f160300514031549001031404907152035400181c050341c010404c101c04546058070500300c020a100000510f42e07560b05148420030102c0d070300b555000c41c00042c0b06140004182c2d602544d107071703204145d40744d40e200d01d42000210440d608603802110790680b41000a260f00c0c01d209000c2003420550308042c503202e682d80b20940d07803040e007107c4000b010105051041c004104802c6411001c254002c010403400c100c00666100c07458440c46105c2030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 185851366 1250 185850116 185850131
    0x309090212060d2603040201020105060a050a060302071110020d08090a080f0c1903030204060207080703170309030408071e2705130606140102060c130b0a0318060f060522 75
    0xa114100c0c01d450025051844100c01440342144c5644c4151002d90056082ca00031030401e1400340300046c2141c100070105121185026415406504901819a88482c590340d0043c8143c4981e072003140e48009030307405006208030840c0d001d082d0b0000905100d40d00da20800003000018020001c54140c00c41503220340d510f48100c044802d142440d01c9218401410444000f40c00709134040d005001074072150740030341d00311684600610360764281a00c0013030a80510020502c0c0c06141b410700441d004400c80041c0c92505448080d21881c0407650740c0465066508156504018144503490380041d0180300038200941c4407401080052104481c0b050403070f6076440340801c459805040d83c10301b126a12980c10b1090715942c4080d03540b5802000b651070701500652000881e035440c200d088a02c01c90100c1c4483c0c003400c0c10080000703803d4100c1c003103620505035140016070b40035640c4495070749101d1080d44003196000f8000d1501090340d0303d030750156005121100d13407807000102184030141000341480000400c00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 185852616 1250 185851366 185851373
    0x70810090207020d020618040f02161407030506040b010303020715020d030b0f15030f06041803080c040506040e06010f021b13090b180609030901090311010320070309090212060d 78
    0x4013010300a40c440c1c000524160749050342e040894404404503000c01422100404c004160b12602942c440d603100074190010005078040c044408508480c0101c4098589980e01e0740d2806000380e038195641052400100101641000b0aa0150402c0030b0f41280d082c14001e030196407000004501c06c1030688642490f01203441c0c070306c010036040f80005c05203040e01200038014500c80c2d2054482030010205900020f0741d0382014022654406052102440b08040c40c3c6c904880c000800b8141d2a071000c8100400607a41d65000c000d8805807211100091031420120005030903288003618120030b541004045901c1e030f0034241544d6034131510a5800f050108041d54800000b084a440003c101070f01c5001401804641e02085d0f0340f031042c407002111810303112010344a54a0291001e880d0004188050070300010780704030b62a20b240308042c113001c02c1d003045c950079041c1040d0348162900b40101e0041155001e0541c0412000000d0080a80c2107240c41d0485e40e1005540c80d0082441c1d018050705007848042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 185853866 1250 185852616 185852629
    0x804050c03030d020a03050f070c0b0a11120a1406031c0c1209050a06050c061305150114010f0c05100903120203010602010204180213060e030118080306010807081009020702 76
    0x26180d0003030030342c0d50741c00002c090341d8001d4010300000c200092418000a040c4007190342040e0042043d9140c0003801c038141d0f40c03000d040a6000f000307480c030039485190004d00ea001001c09401c4140041e10150b030b95180c28481c55084407032003081c003681c0071011403c0c02a103071000701e0107504420494a062140c01d58840c015200c0030b49a00004069140d40b004090200e039201d10b4038001d90340c003102d5512010380d95242c11240d0307000709128600b541d0009804120106540d1031a0483d00344a02c040d5858507500003004d0a06a40c240d011001d034400540c1007040940e440480c4440c0300d586428500b140c580c1c2503c40c41e54554001c8242300e1659594a104821b050141e01e00041c1010350301020765903507031a11402400b0750040d100320740d10400280f0024ec942d20980c02610a20030111250001641c45c2042c03c48030f000c161503405406540c0c40b400100f00344008241c0d00301c21805016255a2070402d20001000701400828407803c1102110900c00c0d61150540341c1402c0700c20b05a005605c07840c860000440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 185855116 1250 185853866 185853883
    0x40803070201150f06020d020a050c04020a0c1b081c050301052418030d050f0702040b060d0603030224090604080c0721120801050114030415050108100624080405 71
    0x12200f0007480c2c001030f030007410300d40301003070383c14640c2500c0079154440d60a90380c4418440f0010040e030030040b1000f8490130168041d0094199030b2800903c0700c20140c9070b00080a03a01410360907060301110040c061440c0c00c020350a68103a45030400c102c0081c00c5640200140411300030f29200d00281004002c00e060b001e003961a1042000c800f00d41e554070f40b5822400c06144004006010307005128010501c103004506076544a60001009440c0c418a94200401011195013380d4007190a001c0b406043d450f07482088040c501c00d40060000c0c0c0354500c3ca05914126580c044d0318070b1500e4600300500310202044841d045640810a030781c0b14104004014104102900a03141c2900b616650340c1003c0d0741c814140400324020541100b461103460000c41d8100001d02516001c1210007280000780d601c81c1000319402406a0868a1200e02c1c01840e081034801c00e03800f5922683c404840075403006028414000101225264445111906440703498040504401802400941c3c0005001c3c05014080082d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 185856366 1250 185855116 185855141
    0x1804020d1104060e2205180111070203073f1b050f120303070e06070b15090c0a02070509070302221d0f0103060c140304030c11030105040b040803070201 67
    0x100715100e04600e00041e801c248540e50002d564180707000300030f040c6882c1e180c0134005110581007544150b8165280684401380c00031007290307451440000c0c294420300c039286100412070000c1d40d58261a0042601c0c14406400078800c1c81c504a40c211444c01f802031895640c0c0161210496541d900c4203503098580030909005050034126182c0c001d00086803812500c1a104100c440c0011a003950043c801d00e1000c80d00c201c0103c0e0700c20004201e4141c0503100407600d0903002008245003910706da49104200034140c48145205031a241d41d0000e1b441c008407265400640c43e07000c1402d21541400003543c640041c89100c0c050500200410b1105200750115450000317010200080074000400c0c50410014610440752003036038030350b8040800120344407030724054000b04440c04456400c54031240001c00ac00041c0509122490201c41e0561403114081c41c4900d001e034960405110460802600f0044104110361099240c10100b20000d40301c200c85607006900400e100d03889545944080e17005050f0f407070429 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 185857616 1250 185856366 185856371
    0x170403050d03050106050918060a18050a180b0103020f0105040803070b0405120a020601150c0c0e010f30080f04140a0503012a031b050c070602060105061804020d 71
    0x4024014001904407007030840355010842c580c0c1e211011600343c01070f100e085501010105a00603200048507515070404070003000b248160341c0d11010000c2086440b060030030210780b038904200d011541d0303100d80502c0c182c550501c04e508c00b545a5801d0407031041404000d02c1114242090005a4803440650380034080c010100c90307581d01d0b50304055407408070885e0116003034424071103144000201344098680805094000b4119a428440d058603000d00c0c919a100800ca981020880411046c9075900002e0005144203c1c865042c045102c4200700540c0040445400c915a040c80040c003810300000300380103804c2d9030303007070300c1d03510b04d004091841200b8188100480110b40418801e0301c1107141408400c003180c1c0000001d64520903d0b081e075100300c4000510b0415008403142010700142044000c91046c03400040e12072b40d006e0800032036604454210001800491070b040d00e10003c11541e805458240010809980b408001608904c42c0c3c03c012901588800402c00041d2103176010355510f60840c0c00103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 185858866 1250 185857616 185857619
    0xf0b0d060b0328020f120717120301060518030f07080d08060a050105040e0a0906090f0516140112090512190905090406051806091b0103020f04121704 66
    0xc0103005038038445840703401041015055500820303104042141011001501c03202d194003040310342280300c044140c1000480c0c1c880245802c040c840e90029003000d4241d5619445d125584518141d9041000c4401d44130400062004c0c6820034243c0700c0d000d5404e801001e07081441000b190070510001d41c4241035218802c00400cac1803c02007404100c1c205c480c0e4801d41d4990340e00c2c0811035030301c0c602d00c502c90104608000c01c1c0a0030100d001011350100c00c649012030011a107680e132a08464542c1c4c1c05983c09019903c0e640104102403106207480d1800007080111203050045205080d94803251b61414440e10042c240d5064080e0740141d41815005400d07100903100301b42c044c514036405100484000d0302030402c403a00300c0780506c03541c2050b108098000461540e640c3d03285002014054450303515898a0155411300f06410007240c0d200e0418040030f080154480ca078200480600510020305150062010f42e580010400a40f03003201c05000c1165001c881c1c0f4113000106843d0340c07805030808140040d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 185860116 1250 185858866 185858873
    0x20a1202011d030913150b0f04030308060d020f0111150c0a0f020f07030f060b031c080105040902030a0b0c040f150f05031510021e0a060506010c020d060f0b0d 70
    0x1101c0502c501103403440d110142250040b5440e84034200c0307034540c0070240480525101c9001d81c05000100008004013081e241caa01103805550405600c031140010001014804c25600a000300d81180c025a00205d28528941c0041c40d0b007911211020b04000b2442007001d6101070400c06851300c00001000d490060a05002c900c0740b941c007003010070010071424946c0241451001400300d00c480e0a11018008842c02c5a842e40f40841c0301c5d0710251041d6486406240c0190b43c00d124460385c010003a906481c9410300c20703802600e0154140d0100d84214503112489025880119901e21285c0c0d2201d100c250302d07039401d019200d807409581c01600f001140f00748042000c401284464542c00c016886948003042000c104499511044402c0341c0c101031004108003160824111021410169006031b8104152469500100260700f1407582c0c21503120500070414406a4400c886d04440f0a280c0030078140c4141c2c0100340e1540600d40010705d840d5540f2480d4400070596400700c0c01c198002803841111301000d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 185861366 1250 185860116 185860121
    0x60b2b09061a0d0302070605030a02130e0a0609150b160f1b09020f07020d060b060a0c060f020702090f1005060703050703030e1c0e01050f04090213060201020903031801020a120201 79
    0x14194201039800409800b440d280c808007000f401c0d50701d42e008081513404c20070121f038541c1015080009a6409005c2808034240c1e0700f48040c00b13050300d228102101d1070002c1d00101070fa1101c0c0d126030303805c1c6c0c036201a060a0303d01031001c143c166514100e0380c40d80ca6070140b21a546003168400e0181c004945c0b86038001c02c0000100800e0300c0c0003c1d04414003c0a5145c0c5440c808a10903801c00036441082004400014200307200044000e9000d1740000031030b85a0301022600b20740c0300c4803204001448a030701100820803948150301030605070300030840c28030102da804142c030814050b141d089072100700c2000840c400c151000e00c20103040041c00e02501c8002500c1c0103011608811800c5000c01d00388200d110207450002580b025405000200002030741c1035400548807400340300c0384c035130412070304108218600011200400040040000c01030352412001e100500c81c1c81d02c2d07041441107900400011207550740c0041611190a510a0400362814901005030325020040d00010a00c0c901100b40c100c480e90190b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 185862616 1250 185861366 185861381
    0x90105132001051b061e060a030210020109051f0e0a1505040206040306090312060509090c010302030c090a0b040614040e0f0a0612060605010f0e03030315030703170307020c04060b2b0906 82
    0x8180c0c1804020000040442a4200c2e1f14681101c114001000980382c1000710041c1c0b0f9040e4000058a07000c540c0b99242411120309130700b00f615000c92007407145d4401e40c0c0f01e2404414407410160044004995810324030510203e0450400c1d52610041000c0d5590b10044038000c0d0381c026820040000240740181c07000e42040c91025826160000000e070354200207001d503100707a0035400604010b0b4400001034000b500301070301881e400c840c10703c8101c1058590454010181c035220841949603071400100810500014540c0383e4038045c1440b003046208100c2c00580e1f0094983d50a40ea80c940e20034003c08001d010076408500d007040c0c001405414854030b40c2c00f450990300d0a0340c4a644881151000703407098404000501d81503441000010f50300015210b03070407030000d002402d98007040e40e40d1326488441803616000c6500310200209201940d40c0400c070000c4009000e4030b09004070743c40d00310401100d0140121502850400c0101582001859100c25002e8842408100250101c6042c01801485031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 185863866 1250 185862616 185862631
    0x703060f080d090506030c03042301110c010c0e010507151e05040212061618030f031d090606070f06112106030604080a0f0c0b0a0203090105132001051b06 68
    0xf012002c509070a00404807441403079102e94030740c60b58030755543d10760101c003185102e440404a01c400c00708187d0300a014800b0050150747e20035881c0d406c3c0c0c03145682190340c410208400d1003c000d91011103641c000c400d50b8085500201c006001600044080c0302070060382c1d001c0b508400c19846580500d1071180c2c4100d001c0e034000d480c0d01e02181c1003e20410740e101010340b82c01241d0782c204602035800381d02c180005504407188414618000b9582e540341d0051710340c01c1004401046503c001c4d4480181e54080140f010502101d210003030381401340108407070384076103640548500c4100312014103020003508108603102034280a640d40e01580070a5001d159103410b6403c591604440110b0344910700051924080c0d9048100e81d0f20340000a40d099544600a82c2c000d030511294010440220349204902da2003405802005a03403858540380c4507007100c0c001020540018804000784000c10703c6031000605400c04a0303030f07089050f50441d0041c1c4d0b05014506501000214a031107800e103501010074501e000340c44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 185865116 1250 185863866 185863877
    0xd1803061125080d021804020a0305061e090a0207030513140a060539030d020d05180a06050601030e07080307020406240503070509030604110901080102041d0703060f080d 75
    0x40310600c82a0940409001d00f59407024046621014626070040c0b980900f06010300b100c0d090001c0101e41070b070f00b0161281d0b020959880401c03102d42000007900c0c1d100580d100b070b100e0034010484e00082c0c2a060180c084002a40d01143c2e0004050060040ba0303a41c2c02c0c9007400d8500103580d0510501d00d205900c1010f80258440b040000380d160146055a070012a010b01080c00d1032400c0682040d90235408410580742000120000c80071001803008000212109101582d41e90290b200302c8190340e0003a04c8101314265010902d020140081800c0001301c4d406407000c182a2908401200a4400d0354042c40550044c8440055521000801842141d1003030318280007050fa210082a810b040c0005090f4041c18441c0b10550854403c00085510210a04017941017041310b030082480e00c0c50855084510440e0084450210315140c4401801820640c00030740ca8075042803031001210424202100100d48558080350029002c0c3d00a040602510840481102c1e580c80d02e0690700e031822043c10000c42c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 185866366 1250 185865116 185865157
    0x21807030e0f030405040c03021207030525020d030c02011b08180102130306020a021e060a14150f0a03050a0503041404060b180d122a03020d18030611 66
    0x4202141c02d403050001d020256080a00e89018040a06001021141050307400c200c224107613492060014040c0c580d65800040c0c9103080124403044401d0b41c00c881d1078581801040c902100d07400540c01c402952075280201b14010100b00a0380900061484045090002400d441080303500602d5544140401005200c655110711101401c0344540c00c3c203a0343d03801500e8010320121365503030010a099481c0b032044843c103044040d803c004610b2400000f1299030400418030049003014040d161180850302e403446081d041845101400328502100c1c0c6010340799202c0c40e1300541e17a41d464600300454001c410340b418a080e41c501242c0b6640180101d0980c01440510030040b82803510640d0300ba2402000000d190070508544030f0700760f80c0000c14840d071104120300e24074006910100c0e04038842c00d07140c039111160104490584001000402c5007000c042c0904054004030344d00051000368440c0504148600c400200707442d0540b15440e030005401103003003200c0040c81c008070030020940d28016056108818 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 185867616 1250 185866366 185866391
    0xd0501110f07020301150b1b030c0102030a0f051506091c120915020304080607120b03010c0207050307060e09070f02030706020406020a022701060e0a0320090c0705030703051602180703 81
    0x91b0b4011022422410302a4200001d528001c040c86c103504e240c112800c0848600507a426a1300481d040030703055480d6655060001d075503000c0c203900300d84422511500707074080c400860842e00070b143c1000e10414585040030000201c0070912410150080000c0300701c580103603800f07402c01c1c40c0340c400d107400c40b0040ca8560900e40c3c400700548090320045406080308e40c85402003218100c000b10b000484d8141d8030b00010030240c0e000d114840100d2001e40242011600d040209424010305034041c078140030344200903a03002c0c4d8a20035850750080c1282400b5016503e803c030700f2890350040b170900900b0580300150205282e5000a00310044910807a0400598201e000201d50b150b1000d00200030715150003070040c00054010704007282c10100281221040303e540c0d8031860141241d0300c0d10000c064202d02140340890420200d6981e014008110942c030304a0307030307603180d544c0e91003044000b80030440f0104540f0700390103540b507904100c5a0014003010341064a9400034580368016503200300400c0c60802c507001c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 185868866 1250 185867616 185867651
    0x706020c0c030d1409041d0d0e04150504020d02070f0809040f14070804082a070f030201090605090d1401020307021501061b170a021b010804110d0501110f07020301 72
    0x55072460703132420840705160340910100e0704003442c0e4640c85900d40c3d02c1c542140c2c00e00340504062400850082c007110941780409000e0300134048403c1d00440c1040035130040301c20030f09402c1088480030f41300160384018607924240280502d200c0288a0703048400e42030f06011200c00034100e0104100c0d070801503020f01000d160304685c00100c0c515141281c0400258001e802051050780c024081c2c181c403447c0000401b03403545c1014141281c004400b501e0508600ac4001c20410301000d850444604008d0a0543d00064913038007103842134200300540041c00c900b151303c40c050206025680889072807010301c59164018041e40080300c2c0b0b803006100e0704c26080d103034501c4101c0a50486d401c0c2e494680340020102c00c04503c0d107201040603220902c0c80081c0240c906181ca000f0b24030070302954090720f150b110b4030045103182180380c0141410046a40240404100c944581d83c26026040340c1c600455196460000c2c00740c034042d40821003840c008a08410400882001402e4052007140204150300d0201000d545 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 185870116 1250 185868866 185868883
    0x40f030c060203251406130c0506040f0e07020709090f031815030b0102031b0d12020406050d0207030309050d030f0609090c05010503040f0506100608070e090403140405060706020c0c03 81
    0x481d522151422925003404c0b50100b0501801032080401d00c41064400610f00130055880c0301d0003113002e011240601c5150013081e000390000720351003454140390407002603503c91a80524040110500c0116180764020415500103100380c0300c0038401c8440504042502c503002030415808100c1c14040c001050000145c0d50007561925410a45c01b0300007007104030001e0115410042c19803000300102132688a46016401c01520480028002c24241140003000c41c4000401d170701b480c42c014031041c080243c201007981c01e030a003c80c000588032201404c080340948031120b4081c2aa026140b050164684e064021000301d04082034180b01c1755543d00084021282e007103001400c032a0340c0c01c0e4107200640c401c000440c3c0180c010005400a240c540c0c613054100901070b164241540c010300c03070801c0040c0d04250801e504ca007071800d05082d0081200013280d40768000400080810181101e00042d44502d41c0031381d000742074050a03003a03c4d401c0d02e24114000350f2004103d14060300c07900114500034500010460b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 185871366 1250 185870116 185870137
    0xe01180b1003020a030212040f121403060415030b0907091a01020604020d0f0c0f0801110a0e01080603030c010c020105010f0807230414130b070207050312030903040b040f030c060203 80
    0x19041c90300410100e009402040801042540800034030803214501c0c09418051405980e18958400c0c040c6071002d100c058141c0c030441800380c4420352000d41c80040058941c80700c81580c01192007400170540001c0000d86404c02480d0784034080030702c800b840c00041c946045c2e444405041000580c0d1030b0150b002c0c4185018001d0040e44004001030040c02c0091510b8110780c0718402401c17170361b4081d586030515000990401004190303003550030802043c00340684e018040c1c036541c40c14038000c0c0f00000100040c1c0d1a41c2c40703d0610032854003142642c0c90400c12205c814044a000704550110400028041c000070300c0703004103580d404040801c0c039903008624802110340300341908804e81d090020249206810103075a40d0700a54800040006036007003082c1e10b11803078030310549862484c0103160800f8403a001400d20400c40d8044c0c2c009000e5520005080d60749180c44c0c402e070a4072030f5207003543e542c55845190840300101c1c501003000152406941400030030b40c2d104100d03240c0100c1e2108002c0341d0780d00500001c003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 185872616 1250 185871366 185871379
    0x503070305061504031e0c03030c0302060c040f03081e03010f030b1605040510020a0203060c07150605131a0a03050c0112050c091309050d120b0d02090a0506190e01180b 74
    0x4000241241c6c2000d0118503910444020910740c07505d034072501c3e0740f00303906c240c02040000460004050b81404000d0f0301a0302e800e00141407900b80b41e50b4407125841800f0003030080c90001414072040814007200d000c0071a440c5440c40e0342c0d43c1c540b600819880c031079210803103820b4000004240045080480000008655034616040601c1c0004000400c19801c1c00f000560042ea041000540c0b0180200303485000c40c4000c699644007107107002d40c80980c8084440c00020714180c0207000320b039500e86141030078240000780822074680e00038020350101403514000c0d038803021020f000010400e02180100c0407030401d0701e60501c800161080744c003c0c2c400c1101c2030210400c040100c0c0d0081d161552043c0490013405600144023030182d500c00d45410008034010020620340f110a40c1940b001d03014429a40f84103654075030000c00180d0204203807601c05041c0351441130715003000403125118841103002044030468022882035603916203c10075102801601000c14440c00c580d041c03d0501e02454880c0100607062 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 185873866 1250 185872616 185872619
    0xc090b0f01030b100c0c0b0c0705011d01080a020306040f05040f0201030c0c0f121e020601050301060b130506030c071502090a09051306050417071406060409030903060c0207050405070503070305061504 88
    0x126034a0309000011554041c0111001c1400c00787c1101400250700301d00000c100440c1000009440e811b050000c040505840c05980000c41c1d030f0203032040390405c900c610090b1f243d03265071001030040c0c6000440442810b00d041e0410003803040004600e42994003e803400c1110055400007202d40b1500038101810011180b5450300029102401c4208004040e1401e10424090810714041d00d20450366200e0061388030000510080c44c1c203116010090004483e11440c0c00d44548103d0600341961140c244a944080005014030040b0f100b203a0003158010884c206203081018030300003e42041c090540501440c000100c0c400d1801d02c01c031405070401040ca10031241d0107544442c090080108200c40c6545010b5003001c00603400c1014109481c03095001d48110303005c0346a0b5900d403642c020700103440381e405c1580100c00301c0c1d0403c0144040d2500000f010465407281e84069141c080b00360312481c0c215190108018207690b004000c1c5014225540d01030016884450400c010b00803aa124100d503110308000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 185875116 1250 185873866 185873899
    0xa0c140d0f1b230301061503050901020904020c06040309120f0803070c02041802041109010f0f0224090c0a140d11030f030406082a030a090c090b0f01030b 68
    0x25201c801841902d6502001c240040400805a42640501d42c01c1c40ea500c03022104002d0842003940c000401d0303000b00500c518011082a185000c20400c1083c941da500100320b403102c0a404445900c10041e00035941da0f070014901580d00c110465050b40082c04226004ca00080c10a150141c01c5401020904082c0c01d50349a0745000e41c4007806c110144005041d0781401603c4030f00803120f070071541d042059004c4201d030061000fa22030a010031000e01c0801c00c00f80f0701a83c1c012203c082803054503d458800c00d41401426031904a072888405c43d40e440c40804015161000d880b240d04c00c1101805882c151401803040c049140300c41e004148107200360b150150110f007890f00417151400d001e80c0f901caa03000d90b08004039043c03044c90078845c2d595410000e414400d040e0844145c503004a440407040c0ea01008148103818604050b1040c2000c1c0000000441d190b101030b40c01071801d1715080f1442514207503944503184001c041018161307001740390200e2020465802442031120300740c006070151040041000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 185876366 1250 185875116 185875133
    0xf020a02090624030a0c030b0306012d090b1f080a0209031e150906070c0f15020a090302030106051008150423011d0124020f0a03020a0c140d 62
    0xb01000d400c91120351510001e0640b210114a035240f1030080540c0e03d0514031141d9045c1c441d03010350340303040c94100f84400742c46440014a82e4110b80b070304000588503541e12010b81802c20a0b0031150184501c4081c00817401c0d8182c2d5004c0c1014070b10480d401c0c1d81c0070314103062000e0300150429082e80030076074890008032155080c2e001480300403402011b50f014501150300c40d090304040d40d40708165584c0702440040101caa40c10f582c54100364002d00428280c0f900303400007000314180759401000030004a80203400c02c04044220311140c20410010b41d01d500c0304882c024510052480300781e02c41d42c03c0c41000602400c2c2040340b40b243c40d540c1e03601c01c8038940da40501d062049070940803c0350403694900c900c03c00f0325599400d0b070610b0350a1440c1c0015552615a41d08541800240c40207008840c501c010820041020601100c4004007a505003140c01c5c6d065042c0d0400a0390b05000c062070081107025000c1580c04210466002d1113000b001400700c2d00da401300e000b007a01d0381c0c8501e03410541007074040e4045120203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 185877616 1250 185876366 185876371
    0xa120b1803190c06060815010b090406031a060406060f0f03020c0a02060f03252705031c02070e010302031207060b06040905071d01083603040501020d0f020a0209 71
    0x400c89103030916150303031070340d610015a0705000040c0f00350768420b0401c4000d0143d100286a03d100406c0b0251100c1201c082c030a8042c1304010542900085010341303230b01e46801c1300e8021604030b50b203145101020041c9110407030044806910642c903200010035024012880c030300c00d14500303035500c0c3c0c0c100c08001ca09030020f6000168089140c031854031035400690700c05004208100c011074010b9102c0c14545907030900003503602c8113064001d00c41805080102c1d8418805416144040e034402000303140c80303481014010003504181c0e014018080500e035008080d54101110308495070844101564031500c24201c11400e000c020b505402400c1000c05aa0088000d450118000c20001030410130710000603d03d60b1140e4400925261102d00300480581c00100e52803240c10381c3cad13504000311103200300000d04044000b00300c0000b03540100540311003001e0a5006c01c0709031a05411540e05049030080d19640c9070003900c54603006120b16601c3c40100d92240c0b00700801c421303103a00140303031110040d400c00040c0b4200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 185878866 1250 185877616 185877661
    0x100603050c10170703090507060504062a06050106032f090603100e280216060c02010b15032212030209040b03010c080a0f110301090504051e0c0a120b 66
    0x41030204485070410411660040701345031000500030102d81b03002424404e0b01d038406000e000d400d0104005454005401c0d46010740480d00a15902e660744403407020110581101401c50382c0b62900110f04160107500000c0c407000c2035255424540c2c8104142e89585480641d0349524000501962072217040c018050354028000811f82c01c0000d40b0b9864103980104103c0725000003a4803188030007801c20540d07480802c44403442c403040d450726005108400c4100c01800004011f26034440304c02410724800c3d0701000580400408420284a101080e0b81140d00107690130005803111a0010901d440d400000e145002d074082c20010154400d0307002030b402034000300b98041d0090341399083d4407200e0b41c0170700c16200240e8050310b405030b0b1400d00c200200111028800e499544910b8014502552044941a03070f04481a0306800b19031651945001420a00300482910300401c00c12403503d0585404103c1d0b2005800c1940c501d42036a40d11a400c00c800e000b02e00d1f01400f41030340b1401145100c80c03003c8520005445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 185880116 1250 185878866 185878877
    0xb0304020f0312090a0603180221010906020c0c03010212070302091c03110c04022106150408060103030807170601080702151905010f0b040e04111e03100603050c10 72
    0x5590300440d0070040d1003c41880d11000010700c006076490072040f20700241c10b4038a0b0402c401712110b400c609400310310401c068415020030345152401101010080f518000550007408074070194988500039400001e4415560f010b10b801c4840717503050510a0b030700510032604103003545440348581500254411585c4503000081120400d8007000602000720305103100350749421a541005005a09110340f52500c28421801040442d02c9910311014201006030070f8130341c00d40036480300c40c0000d0700480c84a003024910701000c10300180c1401c01081841c126402500d030601c0f20343c2c4a50b42151451100701450810070b00f03003804038029500c122180c5c0c0d0701035511700403a5020420b50004407108041143c003401c8003030182d066000c40c41228022140140042d541003030302c007030826400d0300c40e6024502400119109000c0022b00740b04540c4c3d0381c02c0ca44d0030003504001c800a02d48400380c1c2d1001000103080d000f407107160307004140ca40b2a1300c240030440742c110018000000410040002200160088404005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 185881366 1250 185880116 185880139
    0x91a0d0c050d08190206010305060c1b07091b05031909050a0203150105011b0f060e160b130e0412210608010605010207060507110f0d0506090a0201030f0603020a0b030402 75
    0x102c429984402003401a0a019114026041071904040e940a00c800454000b00c0c01040043c50008940e87c1043d034080c022510b500c8807025410791034240da00000101d204402000600791090380c4002d61390321001c0240b0b4180321044000380c0b820b00c020341d00004200707e0304200c585a6040b65002c031001d617100c1c10544615681c6a00041d00e40844610700101c2070500000400c490768000f44030b02d1700800c0e0904842c2c00e010a640359202d00c0d04444001915044d01e4521000e0900c0007030200b10300d05d402a08404880940f02d98000300d2603003104002810001c0000c2000c00c000021144461040b640000c10010380400c413801126409511030700c0010060850322168a06240c81c019070025108440001030002c0c40e00e8002031810950350f0003402808401c024040100d00c0061042044c15000e80f05064807004c1740c004601071a542c41009001c40c00b5950512141d0a404104114103034000d90f01445140700c8003d050080380c0991100a60100250104214495006002e55400b41c0020002c24013031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 185882616 1250 185881366 185881369
    0x4060503030d060509010f23190305151b09040c0e1206221509030c140f010c090506070303050a060e1608101202010e030106030804080f07091a0d0c05 66
    0x140c114141c42c0c480d4580b26142440282040a0720a0041031480e894448885c5004020068605c1e403501c054108034440d203100c0282c1d01e0b02002c43c40c1d0304c0e9516002e0f204080c1c3c0c074204540c994501c0e403900c0c080703021420082030410001c284080301d6090200c51030340c0307001c14a500b0800100411b421030310034000584210040c0b9540c91103502032044014000e04030b41c2c580340c0c0c904c400045550b00340d01c140488403030750b001c0410281d401d404c40080340741d6400540310207281020f44144c40285402001c083c641c00307550540680c0443c1c41070f44c8100e450006e1028444001064500c1141809810f070402e405008990200e882904800d4100c603414000180c0075849000100b0300b40c504a4070401c0c0d034056401c1c0620b0107503011075a06d40c4110780c1c80081c00c90906000e00c0005048004c480a41002000c84001090b65420f501003401550700020041c2d4884d601e011840d1034520603a030ba08914010341380b00040c0c80c0b00d2401032070480129000307204000c02080d001c000c0303841c018039800c1c0d591100e081000320b040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 185883866 1250 185882616 185882623
    0x1052d0603070504061103130e04050c100e0301050601090602100c0c0f030503041203050c0703050c031201030c06090b070c2d0b0315040b01080708060f04241508041104060503 77
    0x74032590f40c0d4442d507032420201e01801003100c502400d15164010020041200f0104401c0d4042c1c941481c0904038545132420001d150404040340a0360003003924102c9410507410034400c092014054000b408a65540001580c3d0000e05101d03400140e088010301d402d80861a500c010300021139400c00202180c096201d0070718001980800324041000001440280007501d482400c5140540c0350521052415510202850103070304402414407001041c0c82c2c242c1141801070f5000807a554028069969403400c1039000d44a25100b00b00202d5070580000c9940402e5008869505402241c60000c3c10701d082c01120341c00c1d4030b01c03040c00d5440402102c403101c40726000382c50300c0040c49200320844c1c403800c1c5441d02e8580c3c4501c910246120701c2c40c1440401059811801080e80466182000d80043c2d84420200c0c0e12440002d504c154068a04180c08001c00c004210102d85224491541d000d810f450f10b840d002c40b00c1d9040d68500100b00c0c1d91002600140417890030040101300a0702c003040d80c0381d403000401c1c80c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 185885116 1250 185883866 185883871
    0xf01170109050f01050d1e0201050403060207061e09050304030f0311030d0c02060601050a1b03110a06050f07170c030424020306040f0c12020c0309090103080316020601052d0603 78
    0x21034603034003400403012a00c3c00301c0d0b000d400200da003c00307401c40a64601411600070f000a01196800110032401d580c007e500760740007035810800c19940c0307800a00d0075200400c3d003004810f00755001910303030400d0600c4074460b400c03055520400440c609410340d2541503001400c0344003202000f01d4095449043d00d014006014000000d040c0030844082d40d200203424041d00610f11410840140121001183e000e148001c44149202c19144000c501e0304040b56006071700c4451028a100754820101040003981c00a80301c0c0c2401d0050031100d864964007210501c58900740b092815160700701140725401008002d41c0c01900c9203644d0f88010701c070700018000c0c07107030724a4661050319804020801c480c2004c2c00b680402e401959402c010b840c0507448060400689082141d40707065000c1001120000d0406c00c80d564041d00420310b5446607524a445481e40d44120340c01e003510900840318001c05400050102d06a4030014001d0b6018048164014101940d1140c50f104450451074056201c0d26090000d50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 185886366 1250 185885116 185885129
    0x609090b040506130308070f0c05011508120301030206030f150418030f09231201050a09020120030406120213030c090e0318060c031e1312110f011701 66
    0x200c0d8681801d22074141040242002002441500d1960019074081681030740a0780070304240d5284002c1080842e0440517205000748107620301001004500b41c0d4882071011542c82004845e070100f01c0002e852403500080c400290401410301c0800e06526a07000003503840107a070f284000032031070003070002400c0d0b8030741002e0700303050022544120080c5a03100e00d003100121414144405541e03d011075040e80d180443d950010780c0409401490890340e1202280c48a401d4030030000d100314204198544014075040400302c0c00305040a4403e00502030701255480c882180c60055801d103480c04806607526001c4908600d19150308204060f205040ca24000703014500455411007124146105281180c040f84003c01aa5106102c280c035200154400c1d03042c49ca030203441c0741c0d0f1a00170120780a459801134001050f0400c9404410b860410030100241618412000311003404550714036009296501601c000303032038000483d11007112803c1950701a250001c2c1072624018a0100c98103048900c0820307001f04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 185887616 1250 185886366 185886383
    0x1002040306020702010311030f04031b0203010504050610121a10051206040219030507031707120f02011803170411121606030c0804030f0201020d090807050708120d0f060909 76
    0x3c42c15075a0500c41c034101414502889403560500c1c0220b9940c048004100404120703041952068240d580d035100049250301400038886410a450101d03203130305e0202c035480411000d820340007500600003100c0d51400c42e0494a00460402514401e910014009220720580340b200071002503141c803100700d00000000070a014010608017481005002ea10b010604500d03001d501400703101080d00801c2c003000b265400324050800e00400b41c481501401210f2001e4101d41c0b0031480c5078650f68000304080810300c103030b5000f0806014805907251000040c0302c03014000980c010121001c0c50b00408500b41c000d4002e4110030110940b402c00294603150450b003000f000e4010107010440d203500c4180d200d01611035400c052040000444006000110040000c1e003000101100586414002e60440d6001c982062061041c2403440c1031003074190f4000f9004980f94880c41600103500d5402107841c040b0156410080e0340b03404400307562100685148509800c01c41c0d42c0d60400150107003079100d19a008c911a0381c64 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 185888866 1250 185887616 185887627
    0x3050a0309050402030606040506090f10020601150309030f0305070903140c01090e0f1f0e01140306070e09071103120f0402030f0c010804080309150106030516050403020a0306020903100204030602 86
    0x1407014880b94881030280d8014418003510f40c2c1c13180160340695030180c900341d0301d81da880c20001d50003242e132a101c80d410452028003505103a502284041c180d401c5450003890514481c7c104808a445040015002034020084124454840e030002a0015243d180440c030082d22030721344507104016003044d14031940c0403103084030a958001d07100c41c00504520500104d6464910b80c80c8450040c02440d080c486048569207900c120030310160b40340903003a00d030640b01040d030f1502e6031688011101c46415110b842260005001248a030341c449042c00401b600307200060322788840c03d440c0b10103041ca64403a180000c0c8080340c220a000032101e0b103d15500801c034102400c080c0141400c110724450030403510b03000003c03841c41c607982150301c4c1c5400643c081c15180c0d81e41c0c1c130baa07001805c010802c1c2104103101d1581000185031541500302c2401910004250469040070803004d0b07030075224034400290000031a8400b00301161240e805002e031000080c0a0310000072400380718604030303070058004503015680440c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 185890116 1250 185888866 185888873
    0x717030d05010b190e13090201110d09091d0c190803130f0b0309072105010c08040203060a0b132c1b010305010302130c030b060a080406151203030b0604030c03050a 72
    0x3080c0c2504001c2e400d14a4581d41c0da000811b107408240962044d10603200d20001d801c5901c1000404524041c10060b2580310030310550041c29019039200766900070707007080c0c0d694240c2000002c0c009440e81804000700a007010748030034400746c0c0042c0c0e9079200e4460041400003461403000d10003007002030407010500d90164281081c5010345091a0480c4001140520030032144100c0014060700361003500e9840c00790445000028a02211811030042a5500300f40709449503540100c0da0601492003181541c840b9074520b0007030800c843c5004d8509901800756800c1c450103584c99802100307000070f05103019841c034440001c076650343c083d4044c0d20388459009000f141080c41c075405080f04511030918081c0700c20751558000071591400d48541d842440c1d41d8281e10141c05000303a20804a055000d0212070304d5a2403654040c11110f022038081c7d9606042941040143e00600c1751642902c040c00c0240031842490385080f0001c1403200312040c1c00400403c004004150768040c1040158440e10050881c0c000318a03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 185891366 1250 185890116 185890147
    0x20c070906031502030415050a021b010207020906030c22200a03050a0501060e010f360801020307020a0f03090305100509010c08070906050d0204090513030807020c030717030d05010b 80
    0x1140c21003914414018071000865040307408420740c40c036000c0400e031525040f00c0700000740b0be85800c40b6550340c26089102c14454041d005403000c00d0080301d100c580d65613418241601c60b90380b1000386a01004075910190300c4401d14500b0305c648110740c5000280c0c0b00c2801d507003160008414a50038541030000c5007400d11190306000f500d0380b1202da00c8041c030055152107409004a0200308442d13043c00004100d400030644603072a51403d940350a8800d036010b100c064007207203c81c41c144584030741126412401140324403050084034000c0031207078020202d411a64407481c0c46401042021003c00528104c00400302d0010031005440c013410910005003406c01199860840d0501e005a0b4140455901082007540c2c10a040da0129805810706990340d135044111240244507942103103100525050130301c40340c803100d6001100d2581c40b980382d46034580c6900000742d80d105961712605a01d54000d203000d10600c0c090803080c05500041c041203e003403072040342d103000960307400760042e000b0300d000812084100100207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 185892616 1250 185891366 185891393
    0xc030b07050702031504060905061518090d0309080d06150305060f221d0c0103060503120301090f09021f0f05040f0b0c071e0501030b0f06030a0f020c07090603 70
    0x50400c0c0b40703041c2c0c6541c007080d150342e50581440411071081001506001d007581182082c01d500905640c0c092a00d44040e440c2c2c060304050440c041c00700c075a5400d45882189200c91b02401c9004010407800b04010801c0f000f0348445a0100d844e4078092011859a0401d0b000e41c4010304050b218070100310402d03604c02400c45030020702040c801c050f0400c40327032441d41703d010498143d0030070300c4640242e0b1445452400d000e4410501d0a00d64140c1940e070800443c5004140290300c00c609036428410b5a40c0e0f88201941c546802e442c43c13a101008100400400c1c20903408400b0305105448040b810f21295000102a0390107400d25403d0300c003001c16a101310541c060340d80000300c1903906200b400c085c2002c2c2103449214042c095260000e4001a00c40241d60742000890010410010004603410521140b034100d24464440c5030701007400d00d0140c03020391502072a01c01d0b07042d07c00f8100e14107594945072200d025001d41030102070416030800c041010050180714081c09408162000300f81c2d03d1843c03602100b1402d54 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 185893866 1250 185892616 185892631
    0x705010212040c05150909040204050901180c0302030d08070503011415030f06040506060307021203040212030a050d0e0a0f02060a03151205060105030a05031603120c030c022401050d060e0106030c030b 88
    0x10400098182e031042c1e47c658100c2c0e01664002107907038921486600404d01001040c290b580d10700c003281e00704a01410200e09a030f2080d81036440002041c1c0050b51701080580304ca001068062005100c1c7c0c04000a2403440007034010141c0d0211303190314404142c940c0c000d58036140007510050401055003001c1c002d06401c070009860300d52642c0751240d0002d40319240c1b00c4081109070301c0000850b05642e00c2030348201980540350f066982d54824410041c0a40e0710060035945007030f0401c00303054222140850030004c510f0708000303500700041155007001481e52040c1c078103d00b0305585500030540345000d140c0c00030240480d461503001c0f0b421141801c9260800507400644203501c240742e0343c0002600407040d180c4e40300d001d01c60070760300384590310f416107107048801c0f02c0b8060140b034480e0795669070743e05420001120000b9000e071341210002107860300c107034420842e4807a110b010010040145080106a07620002d000d020006214600103a0303281c2515050b46c0103482d48440241d0034014003030700080307243d00050b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 185895116 1250 185893866 185893909
    0xe0402040b120d030911060d0c0207060305070507141005010f0501021501230d05010e0105060906060720030102071514130c05060a0c05010f06170304030302120705010212040c05 78
    0x41480300540d6884080760490101340c0c54090790000c200d0052074000301c03038000910329510b03000c10360440c900400c64210200d006100351030001072028000c3c41110301408a40c0d0700e1518082041d15440e02001254131158040d01c142e031030844000402e032141e107018007081207114001c1071401000903c0d00301c0c18010642040140801001441d840107500d01e0100c1780d030084042c840d0448000120005030251015090b5401d11016805510040d07001030300c10b15080fa14024580c9900080c00074074021603500800b03000d0b1040207241d40b905540c180000081000303001614100281e56095020150001340103525921103811003200381d034012a0b941d2080d0044892800584661148280302e0154403d080c0281c200199440c0020300c10a09141150340080080c030031070310007107013020042900f486810441e0000c03e403a58030b13019020040302d040703a800d170b07005040708548420480215800900700715500d40d82000102c0303c0c1c030981500c1520640c011480380b0880c0b80b400e41480f6030056a80c4110041c4c29 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 185896366 1250 185895116 185895139
    0x6092125080709090602090306040c080105011401050a0e030f0a060f0b010302072f121609020a09061103090405090f07061b2616031103040e010618030b010e0402040b 73
    0x1c00241c0300c012102d00340780219100303a01d820700e00001e12612181c140c15008050410089c012290640740c200d0b039540d4020825607a84600c0c9091074191201901c1c0018000c201008485104646100c01d170b0000806850402d020454003501e060000714040764019181e407011241403000384654040c9140c00c2c2815441c00c402c90b0b6541d0f1300240003841c18120501c0c1d0f80d46503042c2551585481c00b01c81c901400c80c45914003c440226515203420f5100329100703007446408140d00350b5034000d4a4107072040703881f10440c56042c0b0500303840540c0c02c000c016076a84400e1001e4000355807940511402405050040c001c2140000c200034140461900940d05101c0100101c9039088440d25004403501e420031103210120361782040410380302150000300845074901003242425120030401e42025548652210382c0b244040303051464981c0603521524401614000040000600880b000786040c060300c61008607860302d075070751945024001e0300600108031007034080104608003445109232000741210a030760480d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 185897616 1250 185896366 185896379
    0x2031c0309021c0f0f05120304110f03010903080105040c0201091a0f090c01021005072304230904030c02150d054302150108031e0a0e06092125 63
    0x35000d06500400d40464405c0110920500f8030080c6550214200700c00d5403400c242c100340c1e0b615240800110303c10424002d502401e4a01440bd8500380c65040d01c41003c1686000200001490460048015035485200715400500209401e00c0f902d105858140468109030300300c090303241c1e00101405d60992001040003140d0b81c00280c0c2c01100840784001180b40d6440701d600301d0b40e040c0900b00405000780c00c80c6400d24880500030107030080e58519000c51100c0e0218510010004e0784181c45160402e100c0c0e408a40400d00c0703940ea01c070b900c5001415a250424001110080e01d60040441014495840061041161a602003001d4045008a041c0c2904c40c0e5241c0c1c4840907106c0601040c1194503000c2000c1d2810f0080c049580130101c4203181040543c0d560302540e899a03c144010480f1074212020420341d1001300d001d4a480c03003915600d220701e54480700c003030140366030000c0d180a40c0a403c03925107070811002450345040381801c5601800810100d0000d90818144c68072000d00380114800f02800308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 185898866 1250 185897616 185897633
    0xf0607051909050d0c03060b04180210030207080301140301050a09150c1404031103010e1501031502070602030403261b1e04150f020105070503010b0702031c0309021c 73
    0x14001c44007196841d090306002521010700301d61200790002181c1d1107070024002c40200d4201141d00861042c00300c3e106c070740e04207c200c841c20104c6016031600c001e00c500c054146401401c91a4026040061070103603191a00e410741d8209a1003451441c07003080003c04542428000c6582111f001c0ca801d20456a040d50b500c89080c2101c00c140207082d55480403840c2280c0704035540845107000c4819540c1d1561030f070030300c030306510300c004a028000c1d0b00b490014000c2000004010303007410041c010050142e401c503034502110300d80c14200c815400307030240720040108903248025809a0b01c02d490b0080d50809004020180c403208052312010000300c8400c010060442242e00b0325045141c611070b40d5104e5403032061a690703034800106450208070200b07010400080c0b00341c614042c50080d031100298910120350890aa440c100c5049001407400e1004101c4a00303e8009412203e10090a8880780c2c0811a4814200c601580c0c1032400070740c442141105504020203500786440003102c4210810b582901c81c0e510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 185900116 1250 185898866 185898877
    0x609020a120203100509090115050d080f0d02091005030702060604110f0d090f0507050a0e16030b040e0d121104030b060d26070209010803030906040201030f020c0303180f060705 78
    0x38042d8002000034480c42070038040f00041c140003000c1640d90b042c19048903000b0040140c8805107000d40600c041401c0c5030040030030312560382c07200000d80b51045400c0c0c04595500054641406103409104041d0a995001900c0700700841b40d5861907181e01e000c0c00000e10f06103010303242901803403820b500c05608600e14400c99126079030818040d659002c803240e080c0001d10034840c01034204c02c25145080c1c200800030034000101c582c125000d0444c280c039800c0301e400c401c00644081d000503c40e00c00c03c907541da0080d000b4140c404001440042d00c0e0fa5080d001906002818051000240202d00d40494500d60341c403940790341c07032110300c1d034141007a095030f40d024117001c006090030f4414040c9050000030450650307407034420044020340800d03075180300990030462074020b803000301d01c6078017440008500d0310000010759100d44102c0b0002d05007030300c0b103400640003000d41c2c5000341700440c1c003000b1201200c0001c00043d130041032040d40c040244002d220300786d4105081ca501020468010505200c4085c0d40101900e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 185901366 1250 185900116 185900147
    0x305120d0c0c032c0409080408010b0916031802040213080f03120a051f06050403051c020a0311120f1305040203040b0a0f020d0c0e010f0305100b030a1805100609020a 73
    0x6000d884204c3c0d0302192444079160455001e828441c482c0c0400500317034040c00459070000024005c0c9102c01040000141c1c3c111007a0312144800d0107600c600d103201e50412841082c480d52014100007085d0003250681e030101680741d80076012400c0c200040035080204d9400d01c00108050741c145030b507400b4002100c0b280540920758094440000c14078402055031303a048400607001002d924699540005442a0006d05c0142e48070300070310b000c114103040d15040b0b405080c2156030180105400e21f81d000e407144108203582c040c01e485030840040d0800368030701c0100181d4912015440c2c40d400c01e03843d160b000b0009034205900460043c814040098803051480e50040c00046000c6030001098101100a01441c910700145508040b0003d81d51074105000388503d100c2030b40c91540c5200f408006500352601500d0280d48211069000c000500540b009036412102c0c600340807900b824070203002c80d4580803040090300c0320b820002c541c9c804881248146c0c2e0040a80740b40942c10f00c160140c0160031005088c4804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 185902616 1250 185901366 185901407
    0x120c030e0f0712080906040906060909050619030b1803030114030c030a050316030302070c0f091d030f07151a03070e010609091e1109180c030408090102070305120d0c0c03 75
    0x11011b5660900740e4000d080360060400c01aa030382c02c4010f221040520855407014034100c0841c099003480c40280b0302c000d0603180f004004610315030307803058042c0d8014130b0160b41c03000599a0b40350788a02400190300915250002c0b410200e075070300405080002c490541c0d0700c2a44914002d1340000c3c00030080d01c440031006040d0302d80000303040c1400d8000c0d100b4150010030300c4402c00302c08200034091508800680300c420804201c25514920300e10401141042d0204640d44244020220104c0c1400103200301d901c1418803130030344010420780c4030545d85c8d20b2102143d9038140f440401e4840c00e04005031720042c043ca144481c80c035450914081c0c00c3c2c046601a0085003602c60708100002c0d2034000200e58000003a01c2f0030003010110100b1480d00341c003c2d12119108000250401c0d0201d000d40b00c0f034500aa0030600c1c0300340341d0744540e80c860304182c0c4880d410b1415400b9000b0004003091f020b0040c415940c480c0500303541c1d102c068407410400c40e144140d10801780065050004003280c2d2100d0748003041c03032903202d08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 185903866 1250 185902616 185902627
    0xc10022d070905010308190507020f060f040503030403050f0d0525060207050312070e0a050f1905030a0b0402090106090305030a110c04020d09060e120d0507120c030e0f071208 77
    0x102030400007580c00019405080c40000000c101c0c00c2001891000380710240c0310103000c99000121160b1081503000ba50006034142406880c1c500b010007030820461600c00740d490241e84001190450700541d0080e9840e401a500c085900c03001403007800000145440d0441c40c5c801c0d505240340306241142c8801c20001e003407104100400c5120b90440d005650003d084035100c014201c142e0710f12442c211000d0b8001244450381c1842c501304a4000404d60300020304581c803498558003404010b0404100110705003600c8071001030306880c180700203000103015080342041071a150040c420090303c1039114004008220204201040c0040309680760310030945440d401d1007200c130240318039080070010300395803003440051040b501d00d0050780000c00710b0b4414401402030683d45810f19480e003420f40340d01003848900b04070003207132088243d01403a401500f5042100400c80803913400c40868800c9202d42d0082076998090002d403d400b08159441001520020444242010043c1c00c4190342c07414018513040000c0380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 185905116 1250 185903866 185903953
    0xe0106050f1302092b050d1809150312090603180206030606090f0a1823041203020c01060f08150603120a030603020616150b01020d080403020a020d050c1002 69
    0x180c18001743d0352815815170628400c8052118121003002c1240c55101c1c0c00800c01229000d05401c40e541d003c00005044854030340704407000500307034000d0002011415804003000040c21913104003c1587c00e40d85801e10345060030005411515058440c100e50540c1d194840300603a00c0c02c0c212680100c059502d1134582039407102003150203d20000007540001a22070218647c400b4061601d030a00200c00f0a11a580031a0300c1801c02c0c10107145100d101d8a00c07040003801142035801100c1704910340f4034006140c459040041800c44da0350707401020182404030000c005c0c00c10b0070888181d038020003021391121420603400180d0741d441481005a501f10001c01d00384d408d41d019134866401983c000d0100c642d5440000400e10b080d412504080302c14140c441c014002c5500c4c6485200d00000b4181c0007030244069a290903580010700078030031411480394144101c0180c0380c0000e110328040c03003103005103e480e0441040008040600b40d40408560103c0a450100e08861610b440e101c0c0c4420140030701c40c40c0150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 185906366 1250 185905116 185905129
    0x90608030309071a27030f010506010f0801080c090612010e011d031204031d0d0b04020a060f0f050717070f051c0e060a030612050c09130f110102031308010e0106050f130209 76
    0x50405d506002d403000141c01711f030040d00300b130388520741c240e9408058a00e400c1080da03440c00280141e500c1070740216002d8000c3d013080f04001c0d400900042c040b8045001340c0341a0303429a080c3c01d450784841c2e51a1001341c0328418007801c0802004076a080030b9410403400785216001094000c00140800c07601080207061051003003001a0501000b824017907074204281060b0f04442410340d4105d000b00c10010340010490f1248100c202c100d445650340c0350010603c2c4c80200d445070000c04042e100c0c44c59141e1096105010107000b41861441401e0150817024942446420861202101d036519041400035031009a8480038100010754201d038810385905003408200c00600f441d400075062100303400150301c00e1000002e00c40b03102410840b5045003a64501650724592074440c81d0040000020b20104000203007012074284032003030188102c0c0d04004004600000c00402075002c084180d54400841c01540002e000300d00c082c0100b5900c42d480018007402181c0a20307141c010303c1d80c0345603000c83c40b02003541e5042e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 185907616 1250 185906366 185906437
    0x70e060c010908090901080d1d030c040e0c0109060f0c020d06110703050d0f090809120c100903060605040908190e04020d0b100315060e0307090608030309071a 70
    0x20380081000308020f01d400d40190b80080015846440110000901a030001400c002903103032942d22041102080d0b26243c803840c0c3c400c02d4095040c0039400f406a0191200c1c0300e1030401c8100c4c00010007001d07891030f001401c03c000c0c5030007100401040101c0001011341101100d5021036050b900c4a0185541d820302c00001c081d40c6e024180a031034005690014981e114000d01074202c108801000b801ea10b43e080081121021140102001420301c04c0520034a4902d00b0040e0311910142500c3e5400b1a510002d0b41086050100b440801e12042c024428404140b00e458003500055504100e400f80545400000780200c0805204000d030200401c6840c82c450381104045100250056485800d05100300000e01185c60206003e440481d47d52280c05120f8007d0800394a034054101c00d05a0130507004540d01400f19204c16018410280001010000c910900e030041070900051a100e0511920503030400341503904c07003100c1612000e40803444240c2d030000c5800403280000c800240c030b20048030f03141d60341008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 185908866 1250 185907616 185907637
    0x90a05120c030d110a2a02282601090503040e0705120702030901110c01170606090d0501050604150f0608061f0206100f030b0a050a09140a02090a0c0503070e06 70
    0x10301043d01002c0c42c02134054055003070b06407a000c2d80b0702140300c006a4a040001d049a1800662500c001d02504001041c95070402c41c8800ca0f044e460750078002c0c150400a254040f078140d2010a03e801840903000801c205e19508010090001e521980c60716992030013580a600c0594040d04041448940980200c4002d510000c4080e000340c035004801a40f01d8000d4101640819400002d41d81d4010b000710b59100304d0b110507195400b2040a03402c0c9031907452001080c0a810010030401c00c8420741c1d94640441c461441003001190a2038846e082c48182c9180369100b03540300300710000c180f100c4200c000c1118191809860290b030103584c0c24000550710200d10311109207603011072051000099020404502c60110064003c0c1895a100c0742e00ba40a02ca9120103001d0502c20000b043c607504041e0009500f00c1c42503032021031441d803142c0b1815410035030004a01402d038020440a021400d00d40c58469210b4680c210030072485d19200800b50462000800031030030802c245010850b2035451609072151390b2075 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 185910116 1250 185908866 185908871
    0x3060213080715030c050405031f0b060f1905090d15060e040f05120f12090313080607020111120103060b0310020406030609060b0412021905090717090a05120c030d 72
    0x40d981e0880000c4003405480c0f40019090000016409001d1801c48003212400b90050074013169103400c2c11542c00e82c9a10110000752503840c200b02580e500409003080703a40540780301d555480726400e140c1c0e0340c03003ca145035000d20106000d0b4402c16038600903841c00c0103402140001107607100c0200710b4010082a040850f280c1891414482400341d010b0038592030510500480e8002900f9035061181d5010b00c1c5031000b80810108160311032000c44c0ca0703c80360070000b9a42160306109000c007202081e03a0040d0031a0240ba0b20080802c180341d80c0c24012150385e50900600d1a10303006450720003000000c41404007170031203030700c407050b04040e628200880307400e15102e1030381191601d88811004020f040e140c4a43d040300e90401e100403405024820880f0202c6500069003469041540d0911207442c030407040c04205488182000201519507a04e114801da03026a108940f90345001c5408402e09005030403c5c01d140e0284c00c2c030400155001030b00003542d2014901c0c2c540c03214000558103240d4030034156190143d60 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 185911366 1250 185910116 185910119
    0xd060902090414040215070501140c09241204030e1e0f03060903030406050718030b0406140f071101020928170d03050c0f070b01091b020304030602130807 68
    0x10000e601038807000c07508035801c2c401c8041000c5810500e032010348010354007242120450b01144120401080610300c43c10001c101e000c080ba10b28100280222003d0000440c0051914114688004040c2041d01c188003042c410b081690249001405034102901d015108500410107150007091a050107503001020103c0d111490604519200640f1039000c1c0506060400e425840c50007150345445010550000c5040d03035107940320b040281402a1400381030041c018450164000f244040c9000385001e0080c032903c0c0d081603e00310f012034101100d2401158155014049280100140740b5044100391400d0320040d0418054a80207105030310b58141d00003d042e900b003504001c0908080307051740c0341c1c2a003002c00640d29107101803500c401c0368142c0c1d80f03604082c4021450b01d01a610180d08041603244450030039149140a002c41e03404040c040e506031038410300402c208003c0b4001c002c000316000314114800100c4203c060f41d2809240002001990040b13000800222250300c1c2c600201b040d00119071031103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 185912616 1250 185911366 185911379
    0x1503060503011d0601050319020607031b08040e0a022503031116110102010903020613030c020d0302030d0c020c0105070209131227030f020609030a1202070f0503010626030d06 77
    0x101040300f04029501a08000007110315012403a659074500455820b60050500e0707003000310701e40c0300c60003c41c280f200d840485a441010255011521442450003543e503509000402c405000002c12600001c2c0c0100700704c1180a044817010320b540b16028061070030369001e07450140d01402d02e2000807640403c000c42d801c20054025200c02011a009000b18030381c1e100b406004a090b0307441a14080c2c09030307002402090a144c1992401a1174a0003480c0521380022580c3c0000c602c4508460281c00580c000300b1200c9070040d640c030601d400845140010407424002c080040c089000d4080081d1080a04400150200e00c0f05611103401585c000c00d5030b8050700000701c001c0c1c11100c1a1a00300202034442e841000388104503503041c0c043e08d030030011059801055031700300302443d402000c2c5280c141c000e00d9004d1f00060389440c400340052485401a09400381000324008010f01c0541c072a130701c680e0402d102045400c164542020481e0a02140400481d82c20500c1916602c504000b02d5403d91800ca00003544 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 185913866 1250 185912616 185912651
    0x90309180c12200c010b060f070506070804030909330602120304020901050603060f0406230303030f0a0b0d08070303050a060b0306100f111b01090e0907150306050301 73
    0xc0d1042600d405103640c1d9a488904101c03568001c00c46900c4140322107910f080305646000e00b0a80400c400041ba09100000c0460800d400c444000d0b15014808200a0100312041c441c9583c05100303803030b041c1010719142e2002010b0821510030000007035625441d03d4003000d880c200e1a00e48020846400000c038550030080040b510083c481c100c0140034003109450844034820841e8041e603001000c3c040305900300740c10805a41c0c40a000181e12046009035411381d0303203850184000504110320131004121034440308a00c0020000000f500c26041001000f080c1070200000da078100c003007030790006021042c003004035894407410300c4007400c01031000c90714108040e0315402451084807814030a22070f8540e1280c0a00c143c0c0001d0b1041e69120501c244680800c9100d28241039245105140441c500050540800d00b0880300d40c0c2810420310821901c4002541c00030020801441c02040e0f5140e5407800840d401d8031a5010301130174449101103122140145c1c802c0d00024068000140200710113100c1c02c01d44240b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 185915116 1250 185913866 185913881
    0xf0307020705030a15050c04170a0c1a0d0b03150c09010f0c03020c010e0109050d0b06181b0d060e0f0a0b100504050904060e0109080309010b0a03020f010309030918 72
    0x14441c54002181c14200407680f00b10499004501c6661101140b042e08058480200120380300841807000003142040c502d222019455030002406a1b901d45003400c0081c00a00d1300320481c040c40e11404484010480c9c01103840400042c1d000080f811515800641003143d10394442c203280101d0001c0c031003019403000060504141c00d0320b505590130154242602c2454001da00500540c0111071005c0b20341d40604861003995005141201301a51a100066005c008080301030310350800400c1040000e080402c1c4c850810440920074003031781d00c2d101c06019220782400320340b0100d044001c0b0b4000c21642580e0411005403103048460011031a05142c606213448007183c0303032a00103041c649582d41d6410400340c101c51001c42c90395068a0107003850103003c054080680700b228056950300b01c0d444100001e1080f15065440340f11119942d08090080c14250750f1513089040c810002c9201c06c0005948015400c1014003003824040340480d80e41c1002c0e1245200c56025620002c0c0b03c100084000406070310104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 185916366 1250 185915116 185915131
    0x60a05031f060f0302060a05090406183801110102130905040b060a15050a0203040801090c0e100806010909150c02030a021b0a030f0510020703050702040b0301020a0c060c090b0f03 79
    0x400e50340e0f0305100c543d24a5440301940105042120010700e40c81200148a040000341c070100381655544510010300b10103005002480da9a11518600d5043c0c0e4618889801c150a010840b05115440703010003030120015114103016410f107814440a00039010340c0c02620041308900900c550741d0303003800042c20048404131802c40c40c0c040000e00030300d4120003490075920f1449041c0158100048203441d207601003003581d01544410b0000280c411000d0080105461003804000080ca02e0800c024100d0440540030701d505103540300041c000e21300c00051480c116400e55002003610f8030582040600f0b4400e002c8403a407482d0400c1850f00b11144c0000050584050366400c0b10841c400312150720b104542039000903580203802e45000c01c041000d504a90b18007034014001d40d44c600b51015a564100c1e88208011000b0a0340425a0390a500c1c0510510220241c00c0d0700951034402c003500c0041c98881d00360030040180d60b841c900e1044030b612074500480034007045480990b030345117000450900da810031580b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 185917616 1250 185916366 185916371
    0x5040c1d1b030f060f0105040807180605030706021b040b040e010606021204050109050d2103060807140303031b0d06170705040c05031603020f0403030e010305061e0603060a05031f 79
    0x446610303040703d20560340d0721440000340d00c5010401c180c5228011415041003002c1c000482e0f42e503400c4c45220002c186111f020010300c80400500015039015506c40c5d4441d0300302d02020400b4070307000320760342481d22681e200000183d1140341c001002000b10700700554009280c505002d980210551044080d0740307041d0221800c11b030b85481d081c1031904c03843c000e0707500040d1042d404201034200ba07101c400d00070b4460640803035864815a0381c0821540c81d5030020700000d0311281c080124681c107114240180c102da0340c00d0340300061140003081e580e20003c0d00600c180c1c090180004d01c0c1e590b1400640780c010000d484207210707442d9640c00f140000300340070603207100c1c43c0604d280c0054145410321908619860903140c0500355540d0520480d4800080e405a505158003001500703600d2800f00300031300c0a10b100340c881883c1c1a04000c001800c903540100254020942d60355904507001152240302da04071811502150f90340d44010101e481c0f5885907200035010301c02c06803180b600b011a1903100445900c0c0c24000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 185918866 1250 185917616 185917651
    0x80c0a050f10030506060d14040b010501020a1707020109090e030403150e1e0313150f1112070303110a050c0f0d0816230a03110f040905040c1d 63
    0x20022007048148099911100005811200b2400f9421680e401040284020f080a034801c00010545480f8a05400c01e241c4000070071080082c41c40d10b00340508020b01c001e14112241d6501d942c0701d641104032154600e180800d1076011a03100790b89040107400002800c0c0710f44211400210342d207030042c0c001150310200d0046a80300402d6640b2400140000304070041040f041e105044c540c046042c1034045103107000800269044800e01e490400051014440c0740c90311120001c402442c61928030800c07000c1200d56401ca8910000c0024402c4d012410191040d80c0d800013840c0c01d0380100b0801d04d148a45881c0843c1e6480d240b07801501500c000e44490301968221612500e109450b0380f003110701314020030040300c0400c0040ca00e5480e5001c0401c0a8103014403020001d45094010004541e000500100002444910203a040c050120001c84d54030205003410318040034820075008078040d818600e03644000050a000c0c44403001002001540c024414001c400b050061b140c85c81140c800b024020f48904 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 185920116 1250 185918866 185918869
    0x905090d0327350901030216060516030f0504020a0b09120105010f030309080a0b04081e03090a110a0308040e071413030b070801120b10150504030b0606031b091306080c0a05 76
    0x320300f00449074070b200b51803600c401000150001d4200f010455542c0904440442c002101c0b072003050300612204074103501000080400a040c0c07a5003aa08102c03903401d0070140b00c01030300d0f001800010303520a10031321600e0b680110046415640c0f080d9200e1165802c060000444204001240b425640a03550ba44082503e50a0791a51142d000030001c1450a071000010302041d400b402425040c5105944080d056540c090125426041943c9071005908900b00c48000c2003012008400c401d00207542c5481084d141d51201c10f0540114811601c25031001d80010750f0b100d200b00e01300ea6907603600204064882000005802d130030500c0d07010403103015400001190829000b940b03814100d4852083c80d9485041542c2e0f18450301002400c00c0c02020903c00011480c00220740c44030186d0304080d0b84680c0c0391440c0d41010403440d1070240c58a4020320040082c051002840f50003c4041303401422071650300d103400300104000322100c04840746161302d00391000c904081d000c5508441040115000c2000584610 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 185921366 1250 185920116 185920193
    0x190821061008041e1b18150501200106030501060308030414060c0a0f140f0d050610020307030f02070803030708011706160f09050a030c06090905090d0327 68
    0xa5001d4141003200c1440d80344540140ca51403203643c031070400c000480f01035400c26060701500e1b0704420307075011702624000d4540400e8465100e041c40180d00c1c84000510b4a4006000c400035013202c0303103130741c010030010280d6018250000e00c011548140204605592418030725582c1e0410381e41110911181c4451400078040028214050581e001e840740c5000c56480702038540c08600301d495810b12400d0040441c0003820307000901410201c0f5040b207503442103020600011540010f01b000d1140e07459218010380c032079000054410650340340c00e12460020b509001030b850400c1940c030400036803000104100d5500c2d031141c49a4100c0702030042d0104504820070159444640454422a05020701ca002c3c4a80c244a0402e44100d24090b042c000f0409440703001069200205400941d4124082081001025404500301c0002e000300032040105003041041691101c202c03c0c6900200b6480d0188ac800840070f0343c3c0001141100c00c5c90400d5021018038100784421029a5200c0700f03c9414610308810601c0e16 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 185922616 1250 185921366 185921371
    0xc03060c030403080105010e22021b0102040b09010809070306290904030c0230010911091005060307050c030703020d090f08070e0a0b1002030d05010f08190821061008 73
    0x16203e0004d16800c2c04011154542d0400c0c0302d030b51004c2c1c01400c0071440b6410544e21341c4c071a00003100141c0d4641e2215a06200722100d441403101c43d81c8104400c10070300c0e250300e06442c00d0301c0003480c01d0391180c3c90705000c0a103400d4a0703420282c440c92400c1c4951060082140d401928207246201c990501030b00700d802c1200c454070446014003c0b8030701c02850001403612841000860201350b00240180d01c0300014500e43c26103004072a041d03603545240703100520050303030800040082c1c2181c15011a00d403012800c06030085038410340d4000c07140400455042405442a02c00d4401000c046a48624250030001d550702210641c11022503c0c0100c041a500128034031802510303d010000c10000b4076080780c608500400400b24004295540c02c401c4003542d03000e800d9409000298000c0d41c403240742c2d00c40031003141c0043e44500c00401000d28200b10740301e00402c82c4201d001b100d03192001d24001a04100e901c5200b425440f100001c1c0100d2041c64000d046c114850180c03105444282820402d8002a62203850a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 185923866 1250 185922616 185922623
    0xb0c0306061b010e0a030207081c021b0420120c0a0507020111011508031206010c0309120f020a1511010515090705091801050405061f032c0c03060c0304 67
    0xb0003004007503880d45108404002001d02c00044c00c051402002410803000d8407003100103800c1340d042001303502420403060071050401000710780c840e01d4540c0d000c0c0d44c8140004a98401011007101d0601594845e40100009500300350b160040040c0102d070341c50f042d8081d528039a44265040d003c81c3d1204626010356501e00095142e10340b07414001e800564041c0c00740640b40e511907483e101200c50010601012000a007260740041d9119003044145100c00200104031504000e0485524804a5808041e01044609a041062242c501401c15006e48070800b580070303400c50b0081d42e002801c4101072101042c0a155aa00c4112400d100d039606803e0300d4041d0358228400d102220b11113050b2404162180c0c21000a04109241211503404038030003a0a03021549002c2113000010405030505006195000c0c0c0200c0b840340300100e400204a02c1d5030070b4000e5200c2010382d5000d5450035100340c0e642c1440c04210000c0c032541c2ca03039524000c2503500c0300203007000b074003d00031000416a10109941541d0003940d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 185925116 1250 185923866 185923879
    0x4060323150402070c0530010e071710050c09030c03030913020918130b0f101404060b0c0708010c090b0904050c071401090311030c1903030e190b0c0306 67
    0x1c180030003000e50040f0f0426940c84010000000e0b01c0c6d9036420710300e69810407522458200000c2000b0b44407010140c0c04001c1a5a4140b02000404c60400310307102080d504030210100e840e02d0f10314445403614034250f19002100746020188030503c1c1c2c03084003030010f0304d5040301115810b490140c240346d100d02070599a02d800512200340700e4182007450f0090103101d00c003d4801e00240aa0f01c0202e480c0c200b041e2201a0103000b44d03400042801808070007160301402013040d60b00c484c1032041c0d1807000c1214a01c2401c07042c01002c90700f01c0300d9a896400030001041c207000a5a1600d50103107900b0348540907031080242640c6059a200e1002d1b002c1c898010464018041707540c2818031050509c000780c24028401e0205c0d4408102e11000102c0004104400c20065400018954510314014103a050b4000603000103600605c61031540130340003d68440b41d506107d6a10341068024581500038129101c00302c2d100d4054080e607900320f81c0c902102940a103001d07001c0080140c503442c2040840f1b104c2036509941154 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 185926366 1250 185925116 185925151
    0x7030b16091a090d0c03021003020406050a0e0411040906150e0307140102030d09050a02030c0108150d02120307080c0601120b0c13081f05160c02090a06080304060323 73
    0x202804584580c141d990200c061500e2401d80c002035818000131000c8809074035802c010300641c242000e45400803007050030114a01130400d14058100d00070b031591581000810b51406001c1e031100d804c1810b18143e501c1005407581c0e00c408086000d050940a00241402c0c1811710001e500d1041e141c1c1440302c840a005000c115042980b1607014813903440e46503056200030402c03060340d07003818807903007040c90b0281028026183c080c8c030400d414008000c00c01810130000000744224006401240452050b040700d002c01103214510204000200c0b1084049050002040d43c4045c011120300502c5020110416100e07284e880356000c0800968802d006800d01c0a09030004d04060324a0300100f0610712040c02c02060107aa40d15414602084000b00c0002aa561580d0001150142c0101e43c3c11100e03501e90300061444080b001000540e0183c00a4400c5000c400442c0444016902060107006c41c0d6054035520307a04e030840a80500f0002c400380882240d1740c1c000700d904102c5189814000e01c02c2e142d800e000103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 185927616 1250 185926366 185926379
    0x15010b03040501150f06030c03060e24032d160306020d090f0c0503070b030c0a0302072306060909060411040507030b0402120604150f030305070c051207030b1609 71
    0x5810081c821202c0d0743d6240b080081d00300c1507841e1880141140500c81101504100b8001e080c2c4040001400038107044c61403d1280c411140700385948080703c0c4a00c182202c0030001800c0301c89a0307514416400d0b02a08110100f0b00c2488503140110104c005510000b07607a88a4090307135a2940100c1c00320b10000d84a006000244294000780200b070480e620100780c013800b03906c03440442c821100c811103000d0240c0c0c200308414142400003900070321881c60390a00394507103007030034040d11b00c0b408941204140e400681e41042245608005421106000e580d907001c48151100654801c000e0328018881c4543d1000039410380000900a84a07580c80038080036004480c0c0140005004050091420b0688450f400b03215600c903440504000718428140c400b0b2401c041050000303e54031900381c0144a20422000d00c0f0300040354218004a90385403818564070762280c00c10b00c60811080d00620f03400412490300c003100100014042040c0c5c1d0113400041c030103840344408058482508406c0310081107100e42c2c2001403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 185928866 1250 185927616 185927639
    0x50d050a090308120703050603070501051602180901050601120c050a0807261801020915030a09021c02010806010302091c050f010c020a060606020106140d020a030203060a020a111501 80
    0xd00c403240c20101d40550700c95036510400d03001070303020681c004000c00401404561500501343c02075400d40180001c0741c00e20b0002000c602c80c15144a0140c0b0f503081001d0f00319100c65100282c032903480e4200f488641071040c030240c081e14081d41c4a80c000348206000c0021900144204003440380300303846951034455000c80541e08420000c0a04040c048031800e40d0140504d0507183d111000106c6006200c240f8100000741e4112841c0c0320100500da01c1400b06000135101c0b0200d100d911411311002035120794501c00200023034038560320000e4200c869840442d080d40d210380c0400d80618400d0b00c030910550340e90b1004408070301480708030f540d100600c1d10240a00500c80c54003400c40a001d5000d42d40324602081c0c41ca425039070507501d0030005074001c0032880c0500c049889114003030b0495100900a680c5401840c40d00980c0f2a500380c0d00c02c52048080748110368910321680006c40d4054181c42041c9858803900f40217400c20124000031400e0700b0f030924055000484d40c000d4001c55120308800c60f90038a800c0200c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 185930116 1250 185928866 185928877
    0x105010e10030e010c050a0201060e07020a080c0f0106121211030f1602060a09062c0103020a020f12090f0a05060f090303040f0321030e0706030b060706020708030a05090604050d05 79
    0x741a683d00300d900b0761141c00e00450038040003684800b60b680d00340c12002801c41d445940400c1c002e80c81a070a000691b64041907142c200c617008554107842c2c0402010b41800c0c046000e0300c506040d0302c0e02400047d40800c60b0b60289a036405200f10061081c961001074031518003520152031030740c1040008004000f0f040c2c010300504134001c0d03200e40442c20698045103086d844142100c0210f0440070082102603842807400d801b0000c3d801d0308901c0d18081e418103000501c001d4100d9030501d0340200307612804510030418241a400c07580101c45020499800030081503016205c8240034040890080c0c0c006c1c18030200860413528060401c0b841d064105024801940042d008150716000400c8000364140d0169030140146010f200d005000024081c00c460507140800350003800d140c10052042031144000c0b80140c102c580f6400c0c081020241c02d000900e0340e2190b0300c1c00904441c8003080b450305009910020318400e0810b00010000758480100d021340d0360504a03030041460380450213138550248070f10302608 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 185931366 1250 185930116 185930149
    0x60506091006110a06110403230c090705070506040c090c02071211040b03060703140f07081605040f090b0a06091203050c120304030804050c0a060e2b03090e0f0105010e 74
    0x4c810344001e80c0c0d5038065596008854021600101d02401402070a2440c8401500d403c0701c00c00340c0707000c451490741d1180068040c032842107490000046909015504458403543e0004c1501c8003490245404180c1360498090b40b4106850502c840f0741d20350000a0940545415003200d043da40d4440c2c1d69100c0d414041d880964006480381c4c45c5e055591402c003c01406455a034402080210404907001003d001c020b20f00d0b190108030106001da004e030800483c40c0c2080340c2506042411880030019140340c4a11740c09420b00361758840000441c26000d07400100c0f402001c458420961f9607a4100301d03450780880c02040040d810391401c010000340180d009001614240702038481d848510600101203810486096000c1a440020001001001e002065681908613181c40c1828240200100300000c0b160300030740218040c809008403a4240844002c017528102a19000805180707001003149066124104c0d000e003e12011030b01c00c0c00d007100b00c00d06035101a52030f25040c00504003002000340c01a41c1c4c0c40c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 185932616 1250 185931366 185931373
    0x70f08101a030304060f1704020904020609040902030715140307090e0a0f0207060606110a0b0105010c0807020901080f07081c050a0c05070b04050a0b090306070c020a080f070306050609100611 84
    0x410701500c06001510044c1070380d46484404089448002e4010303d01203110411618607a401c0000581e144880c26412940641c1c54a0f120130007540070070f000705507402c0060360502c5248030000e1020100380440c04040d120f96116038181d20318906900b0240800d40c1c1801c0410154441484040c04200c10b0030b40c07007501c21030041003810722807102c00304903407041380280c60b0191103c005022883e00860412000f41103480241142c96960b118043e90302c1d411302417107040101000c07141003446008001d4400207500140201d049503503415881340c4ea12907200514a0034007416400140c0b260001c98125141d125146d00020a50b600c6c01d0100c41d140d2003c0c0c42001401200703903280d00864001c2006402a10640c0c416170b50740c034103080400040c42c1ca26800300b075000004010590590714007296007a0480c0c5c050800b43e824078402e20005400ca40ca0707405c000e60703610034100c40e081c4801c800541901128080d10701001140c0b1120140b2220700d80803120801e080f200080c8c1040964412282401c5800000068 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 185933866 1250 185932616 185932661
    0xc1009031403150a050f0f010318021e010e060705070608060a090c0e0f0a0501050708160807060b040b041803120204120309140409031704150c0809070f0810 69
    0x503007100780c0042d210b040004142400090b001e08041325024041e16044541c400000003e40000b003480d002c80c0e101a040544901c0c0150107020700d00c00301281542c2c02044241e2901100b01c00e0342184a008051030b001505907114101242801c800300d0701ca258002c0060304c881800d2500945ea580b9018002c10341000404c0c100080f048503074404c00344158082d0355070382c003c0a00d543c20894100303003940107540300f0f40f452042049280c2e080011640116480103113603845036544801c40d108034520000281c0f481400203184401c1014913031003810400d108860030000240000c0610084609151041c079420a580003000c01080c058a00b0b0203d84041c15000f500d8075071030f0b139035206e0082d26081d021000302c0d0b1941e9060004c100300340f41151149205540c200481c0e103175910020702c20000d0840001c8850783e100080b8042c800c803101501c1048905590030701880c0c074141001021040b08880e480f081d80121580410100c095201040c103e80c400c0008180c00181e065910f4000c00010205501c0002c402c483c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 185935116 1250 185933866 185933897
    0x3030d111308010903020606030f0d1803020301230a05010302060a0302030405250602010e150112050a050303040c080c030105150105090a0519061b1a0a0b13021b030c100903 76
    0x10035001420a900000c00c0303010740c4e4a80a45800400303494248660080801a203c01200040180307003421035150003400c50b02d0401c9090148031654101940650070700300c244001c40421103803403208118400c40120603662700d43d20013040303076020300000358800410400c03408114883e8015603040780c00350042e60b40003110313881480842c2c00600d14545154140311001c010181d0284030b07424002d417956010303110140d40702d010151035001c14003070b18840c0c030042c6030300e0410312004000466a840e0321104482e03403824942080300b03104106106a2020f8440c140c502c007103d06041c010180508805101c0080100d42c50300151100c1e085020f080350003101c0318400080030754858030141c014100c1692026001030412800a115640303010800c82050002180c44000510700c5008002c00c0d190072071030b016251078212102001e080003484040e44140e401110f8500a8516030003010f00c1c800540c0403090300d00e40000e06589034001c0c0c011a10301ea0300b00108074064a43c80c0e812a044d2148245031210340c0c1e218940 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 185936366 1250 185935116 185935147
    0xd06020c070326031608040302122a0f07061d040501171c0503041b08010f1508070501200a050a260903030316020f0a0f0b0709030203030d11 62
    0x1482658078401d0810f00c1c3c0f0401ca4548480003d0f0005502010b10311703d458200b00c0e1a0740d0f81302140300d041211400014082c94030903c81d00480394500c2c91a00d40e80c00c0d00d0b00810200140c844a6080002c0e40c02030484a03c420010300d06540f803551001402140345000b4007a280d040040b001c03400c03200500c490340d549940d1b03503105643c0a880446c03002802d0001e20001d451400341074030514840c1c0c140140c0841d00068110081d2039000781d029002414003100c040c44801d43c10750301d90103a880c0c2d40c2458441c03a062000303a0003070b1052407801b4400c81d074025034503460295101c1c110300c10607001c15102c80c00700c0c003140b04012030b110f00060f03e03070304071150f541003603540b54601141a04c0666a510320201501c000c7c0c510002d031405c44242011596080c14100d40000f40c513403101400f010b1640d00d041c10f107244054020b00c905500041c110056030248500c1c2c0c00d18844020482e00e003100d60340311000000382054000c0080d9000d80c1c0d00940214200194209000c009100705203003503004040a2244031234844442 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 185937616 1250 185936366 185936369
    0x182203030f0e0102040e1006140a020a0b09030706050f011a16051f05010e0121030c02030d0f1404030f0b0907031b080f0a02130b01050408030403030509130905030304020d06020c07 79
    0x40006a4440c42c044000305603803005021f810f0108540c840402c411540109003102d1441d0010b0415516030044406030710703240c0c241600a02d01d83d24441000341e80b00020025043c060700401c0c092147e650740424021050400340501005175049000c040502004d030405401700150000d0030056130300c000d40b55513242400c5d006010036142024900c0451103003d901032a4010404441090859410101c0222056400940c10071101381750344410001d0522401240742d0302034014054907101d0302026001041c0d0301048207040c0100341000b4061080352440411a400c5039081b9401450294480d07980c002c42c50400346c000d480c00d103d11200070021684040c0f00b250107030386022a042030340e4035028509040441e011400c02003500038907485405030719510813165820454680008006070b081d00140e0b03031405203802c100c146100100e004420550004010884440122503612850118094100c00e0358000b082c02022034100384040340050401c030302082c60b0313680315034809400c001c584651186414003d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 185938866 1250 185937616 185937641
    0x201020102120a090c0f050d02010c05031c0c0905030604050d140c01111201080c0a0b2a10050906100902090103060b070c0306050112110d0302030f0307080105182203030f 75
    0x44c1c000320020007914402480040001c00700183e0202d141400003800c0240c035013401f90502a18000c0c0104001c02482203500b90290b002c11886c4d407110003106140100f0300a046030f00454807101c00030520f8900001c209211703d9108000705194441c40ca07084a000300c05030f0000c41072010074031400e50150340070b010308142da941d01060103032a02e000b107180b12005841a404040c090304030507262001740c0c84251581060704c0301411400d070750320740c81e129000c4501203440c3c90005082d050b1000750340200021038401d1065402040038800c80e100d0110b91601c814054510031000b9803885810400d4500a0700500000c407014107000908607a0350a8180260340200000c80b0544414681402044150f100b00703030141031100301e103049010050f42e51803602440aa45030784520561001d80b010988208100c5184200e81b00c1c13110341720304010601500102003801040c2c80b0304845000d06440031500c0c0f190500c20340501c102035090881e000d0030301d580c03002c20050980400d80c48030390300c0000c1646406000d680080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 185940116 1250 185938866 185938871
    0x102040e01030b0601020727090804090c03020705101812030603020901030303020c070b0306030705011b0609080a0305010602010c09121401050c0d0b0301110901081008060103080a020c010305220201020102120a 92
    0x10320800083c24100f080d000308c402c043c425403000709504043e00010b030150031110783c0020ba503a01d41c1010700781800b9a501c011076141c1001900303081d0aa158003e0310b00d2034882c00841d0300da42c1c44500c0c0340c42514603421880c44225410313480740380403030038071300740500f414500342000551240c80e60081805407009810a4010a0f0005003025200d00d0410102c401840440d8409003142032040000780c80309064841d040c1044102e00c401d0348001c0144010001c1076512100800198506180001723540d040007112602003444d00000240c2c0c5030040c050300d07001ca0029545c03403040c10700740032200c1409035081c0410b684240205620074041c0c40244512405080d161031801e4907240e10740320040a0321185448240280d05100c0e21540c1e428200781078032600704090800c0c41140e030f40d5040c1610141550340c4080f00c03e12480c1c00000500c45e10000a09900c0400d07800d86a0151004c8019001c0d6041910450380c0b070080721800c1000700c0d5166860541c0688144005450202140c01681d081d80b02540c00d1344040341d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 185941366 1250 185940116 185940121
    0x2011b0507150206060306040c05130b0a080d0813020a09020711150c0106080c0604060e12030703080415050f0402060c0f01050907081509150a02090d0303050403030509070b0403080a020102040e01030b 88
    0x640400c1030585c0000100c00815143c42d01d9902d6440c02840c034400c8501886801064001440341c9030850019101d01038004080c155481401b90341c0c81c1c86030a0441c0c0403c2400020503c41c2240e6a1000c100304d80182c00703071103600e08c1c000344c5000940c480101503822a42c61078420790766985229140362141d00c94034440d510798850103070007821a041c0c0d44c8501c165a01a480ca840603480f04020340e0100d03411800d0800c03000314583c002c100740084100c3d01182070300000410354201a01300d46402e02590040794410103900c801c6844108030f541c16615814140d2204000400500d8010014a41746501c1c2c17060780c10030809842c0203401d40b401602d007596103420884050046030410070400350082980141041942421b500290302e0300381d00c0203603000c0070644c24001205034800d82c04440c1003800c040c2c203684059070241001001000243c0d81180080d003808041144004d00288440c1a02c1500200600d06072a40d034440f01c06500c128a8503055540900001a030044022901c1d0300850043e8a86003061 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 185942616 1250 185941366 185941409
    0x609084908040203240f0612070905010f0f050105071218181121100b0304060e01151a130504020325020d09140d051c031b0c02011b0507 60
    0x402000710b4103015200c0074585c0d06045d806010013a41001104411a030341d030f2200f0004c03451200100945091030300c07410303d0000d1030107140c0e032145040340d410040310003100f502d030102d55880100520440d40056014069030b4041226030b04100b00e00402428240020080984600d41e07064031540400c2d859684d041903d2032490b110700071403090640038040c080c81c090300c0709049414101612450754005000500003894201d410003060042c06280900544074681883c2140180500321083c5034154207000d41400b241c07400003512025900e2650b841088903ca12060045580002d0600080000f25110020b03482e1607500c0154000c00140350002c0c1240284003010482c0d01d40d03524100115808656841400c0340d2200712503041c0ea9211400044800d80c00002a40285090101034a0b600986c403034215034aa854100032400d001a450501c50001c0e00e0700518041150607540b0804281030034040b80043d0320901c01e10001d950611001c65110391107844492070803100b904944000300303d8090300341c80b5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 185943866 1250 185942616 185942623
    0x405090d03111614010603060f091a0603030409020d020d0e0a020a060903020f0f0f120c010f0503090303010e0417030109150e0411060a0c1a010609084908040203 71
    0x3100415901545040c041e0502800c0505000b0380240404c0300e40010790000c014290448030055400c24810f20280e900700054000800e816401250b2209484001c000c0a1400d40e85051240000a001e18100fa04d4000e030000070350700200d800d0085590821291800740130754410116084540002020302c09018414030811406035003044003803100300c2c4003c0005aa4801e03a000f90724800766030740c513403884041c00030610450900d0440c43e03120030044c1c074650989a000030400b9550100342d1381c0d003640035490719056942d4841500c0074036080e04200010f0050300c203a50300b43e40c0c11904c12441c5106040b01203003200241c1e0001c0e00641480c94031194040c4001c00700d141520060042c0b0040e81c12507007003d65075035a1035800c3d81c0400d4080c00b03001c83c1560466024071007480560341c01c0102100b0003002065407444240c42401560081002c02c0310104003a600040c00314020002c40c41007900c00d10045004900440690f0003000e83e5070002c1d11030850400e640310b0715612103117180e16261250300b4288101800c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 185945116 1250 185943866 185943881
    0x3070c151803020103021305061b07120f0609080c10020909010b04140d11060a0504030b0c21040206070804060e0a09110a110c090906070e1e01030e0c0405090d03 71
    0x10812001801c5290900e5041403400302c0390309090050351150b16007181010b090301588100c0c2d21041c0490044039091481d91031104001520381a162125202d05140754000d03001071014265640744c840d50700000b206a030210812900485500c1d0600d510314488910300020300460f0303c0441d402255103021801c00c0c042050141044201070b03030030503040c4a200641c4071001c51040f8070401c801400441401812061051150800740c5419a90b902c0c0d5580548960300c184000c503400814100000e00101c050020399a10305055140829031000c80984075a94520142050344e010004000000028100d40001d200421540c0c6600210f0a040390400c009140268840141d0310700303050404034501e80003803c07194000b4090400f040c2040044004528185d43d250909400c198010207102178914002003084c8074100d0740d520345551408040c203000001803014070420000c00038a64004003980230360410b4101806000444a0309414a000142610000d450039034081e00038682a611165040c050b80c1c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 185946366 1250 185945116 185945159
    0x705160605210709030203010c0e0f060909070c0312020304060507111203070518030d03061806080703020108060d0609150614030a08070206041208040e010509090a0803100803070c 79
    0x50074140d0507540211a00c2c00e00341100d203008145400908480e01850340d510296070080d000b0413049c411018050300c2c6e0140140550320030005005130350300b03610b4081d0490b10203040c040d0241c40180c0780c8040035500035101c100203c0a0184280c0f0100c050007a0384050b511580c0070302c4001c912801d140c64054180c2108001f000e1045e048500c072445005908011281c00400a2411554800240100340c00c141001c034495030b4180102c50b02d85040e1741e415000704080d9480c2d40f1040249100c581c403180116960303031040c3d0155070044842007000d5030103090300c11790101740601717501d0120b00300e5031302c0c14206c03410303114121180d281d611f010710307410f8030b9034400c0f0409066450059400e4151400010b50b0302d200d410001043c1103400100f40e011501c0f001c06540040c4901c2d29400e051505503d007925050b001030255440d803903100e400004541c0b400c0000f43d0b018100c1c0380050008080c0d207440d0340e020303540b0050006580807000c120000364078404000411003680135004041d00d840c1401c10041c10142a00d0210 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 185947616 1250 185946366 185946377
    0xe031903091a0c0405130f05010605070c091e020706090311070305061807030b010602060a0b090402101103090618190e240604031103010501090c140315040207051606 73
    0x30005841180d2010b85072840e5584541c0c0c9590340c0340c4209840c4039507007000b0781100e11801c01031a0b2001a4110001115504000340680c0e83c86102c01c0303806d405520703005010881800700810015540382e02c425001c8001f5000d1070f015145500600c0144c0e0b004800841d20369545140c20303c1410b91040c2d00c482c0440d80d00c8040d101c501c6c5581c0380c6c00d030340d203030003624481300049003a10840e4901c10401c0010700540e440302004103d9a034a4402170b4584008039a00e072401410f0551030200e61400320060381c4035641c010800a810490128110782c910001400c00009220400c24039000d83d59103070207003550000717403102114004810340500400f83c0142100741c40301c0e40891018042034808180c015071000128001e2031480c3c00da00c0c1ca400442640c290346c2608804000f4001c0203000c0420500480c9250a400070310059a8542c000d8044609100016001a440103c00028105004c00860700420202038200f41e0310120000107040344c0c4007241c2101e041d401408403440440401143c4c01c010003190404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 185948866 1250 185947616 185947631
    0x8070912030302090303120f0114060a050f090112060f061d061207090f0b0903150601020c010309020d0203241b1b1c0807030b03030310150c060e031903 67
    0x2a8000c0c65400300004060607004200c00010b070318200284c40780c1c0745401112000904003074030420240030f030130b00915a99001100440b0b2180c00c082c0c00702d91482070540c0c0d0340b929001d0f0700007404c940358001440782170400038020a04045403070360703021b80700c042d101d00080d02422614003040030703004070005089000013007010001c0840760b41e142010381d43c0440c50f5a0041c00729a452446c11100150903400910f42807644440210780030801d6001360658081c280c0c1107544200205001c02c10348031007250700d280164017006240c0e82c00e51281d00504e0742948007904c3c0320680e0201c0c0d80028144600700001c03100c90b51010f003410105504001c211504604101c540d0241c0e000c034800400030030700c0350034440501594201c8a21200120412205010240504900041e02d11022004200e26401c0d01c040c0c00181c104100c0e0140d910300031045901580c502c0c004120b5840c54030000e5410068400301d480b09000c0c00400030000700b082801078a411500d800040d560b121454100041d1803c41d040030b1008041c42d0054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 185950116 1250 185948866 185948879
    0x3020d030c1d0405190612110f03120f0706020415020d050307020a060203130b160e040b06030a0f06270f02070305030f0c09180f010e100b0a0302040308040b0a080709 73
    0x85201080c1c502141585e560001900359800300b000e000140e074684500060440401c8102c0304540c0d02c20131460003480e01c8002081a210114001c041e8540c110030010600c1940c014014107641125801003070818102e40c130307590100d801c5032340111f0384a03c0008101c08965414003980e94020b515003855421030418410080d9200d10540c0020308240c2c4c00000328142401040304a00ba0562101307100c625880c1840e60070004103209100d03d80400c031440c0d01a02140ba044c000c072244400090411030071560313450038040123405aa044200343c0390385e41c8008074100790065a01404031404000d081c44d285141d090480844001b000084480c0c5c0c41400250002980002226081407421034041356644501140000b20311030540320035400040e916014050054034580d0701e04c20000c1d4885180709a07070311580d800801101300c602da10110040581404401c40d56005405006140e02d00141003031744a5030351507899441600600100800032425420840d48040307a00c0d809410703443d1904040340743c0074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 185951366 1250 185950116 185950157
    0x60604080304092403030201092001020d030923030705100605090612010e0709060513050402010509010809010b0616050105070906090b0901120510170607091715010303020d030c 78
    0xd206180da00e400d1000703203d130000c0300b00c88051401100407210241c0e43c1e1401074024203151604030740c40303505810318070010b458101d00d010440c3c10607000781400b0740243e0070850080030201011104c890b130360080049003c0482407954a611040b900855030352000d4201146802c200e1540100d0f420b003425414002521000000d40c1c0017402900c801c010050380c049481c1c0580307030044c03120740d1920400e035000486a2080c0c102c1002c480301526104103800d8010702e0181952000c0303902070b011910070820822254402c01986030300c6183c0300000224014007500207052540546441090328004030f548005004080c803442e40c200ca150708000201a1820802a2a810840c460f0010303030100800d480380180d0068100082c01d82440004000c10b00d4040e14913420000310b03001d81c962034804510182928800001c0b07060280d0315588501e00040e01e0100200c646c0f08840c40c03020700a0040c0c04404546044801e0300c81e010314420703006070059100c0088000d046030103d10140d000c101d40503001054040004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 185952616 1250 185951366 185951369
    0x18130203070201050609180a030f03021215010e031501120804120302012307020703230109140115030c05101b11040b062a0a050304120b010e0c0912100609060e060604080304 76
    0x505083d06a0060214103030000d014031004401c41e0781e0706004105840200e44080140c502c0262241c0000100042c2032590b00c0800f40050180b012c200401408200300000003203130140d00c40e9208030b02d825243e20100000c404c4c44801100581e4440500300003484040c100c282c068650340c1018019883d0821000f5500da4413440041c202c0c0e00401c0322504c00c10010442d514903a140b0f10001d00050141c2e25205244450b01c1c0160041c6520b0940b4201650000c10300340c4003100d400c000c0c1d43c9415410a020000345800d482c0001d000d00c61071944103035040c100302c000d41000d107000301284104010340307205010940c2c92603400d8600c00c0c0c01c1040860900140c0c09007201c100414240e503104407801c41c10000e0301e01042c0d02000f074807501c000f242c002420800e000201709100d2144806030210b90765034518004005054512001c4c0c50010301440045040103031210080c60940740855800320b1b00d080000c001ca51044e002120490748407242400302c0001c1c034502e80d40100060b5285854546001116034607070085 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 185953866 1250 185952616 185952623
    0x30109050f070c02212b020c3d0309061103010513020313050a0b010303021b13090204110408150c0a020c010c0c03020612011404060b18130203070201050609180a 71
    0x801d080030301c12104565201c1941a1840101c81d4071440c007030481010040000207590306c40648000c071240c00c61002c60fa0014030b16010300301c5910300105510840d514103804118507804c20000000614085040c009403030386102a40300010280c01c035042007000d642040000c41c0480c24100010041600c1c0e000c02d86507090820500180c9035203c40b0300c520484428400042d0061059a811074140403030a040d03d4103c9109800f12101a2410440c00041802d0000c40c076900c4199546a103044d4611382d08190f0b0300e40d10082002850401d10343c9400c4454000c4d4000030042d500c0300c1c0d09507070704040115100b500054a92a941d003816130810000355501921242d040c100075031020210200058410780001840c0d0080910791201d103404100110403009102c0d01078004a2074201e00c909080903c102016958202c040d035140a000004000501c0780562450307810850700010001104d4051000c2e42c043d2859500204940c10b2440c1000305050b8040e01006a50b9110350003280080703c0081d0506a0a41c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 185955116 1250 185953866 185953879
    0xc0801050d2301020309070609030b0601080403180b043809030304170c01030b011707081305071410180303080a02190e03061e0a02070f0507060302030109050f070c02 73
    0x219160403001e41041409200b5003072115a0301c890074107010340255104203c00022507140b5551141c04452130752051001400c03950b2404081040d0b07503c984542c95205002c0d042501a107026126070380c1c403409203640854061840860f0511280940714460050400300b05038030200d051002c60b49407824500085032481c02c500000b4101d41c0e584080c8141d500a0400b00300d00d54803c11032680b09902d413040c44082a0004e881d1411070a007641c020701c02c0a20041d540041d01c441940ea003002640c0b66100504020349843c0c140c0070400000e04204400000f404170071003c1e428408802042c01003605088807004144025000b26807001c09410708600c0031a070305864096003a840c0d44000a00a00c2078102c0d084003404104038083c030b1f07280c01c050785c81c00c0c20300203904544441d91136410f84ca20705250001541450303417494002c2410f49c4516005811050b01400480d0104040350b07440d203243c0000c0c1da02038004203402100401070690b0390b1003540d074071810080500d29140f40c8882c1c000d00c49010440028850700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 185956366 1250 185955116 185955139
    0x1080105040b01140d021207030501030506040609020102070f0305030c0105100506160305040f0816060518011404050303070b09060702010c3c05090f0d050d08070c05070603021c0c080105 82
    0xa11442061942c4082d0700c4c18903685004a03c00100a54032680360341240f40390b92008110140d00c64810141265004005801941c581d6612840034149040003a411481012404103034000d881d04848009e600c15001075a841040300d180c50300395180200007101e0b0545044007082161030314011592610b40d40d14a84541100030300e426100d600031500701c0b03880230b0302e61080400c0d42a0001019654003c00103d440c03451035450008031070b80c1c03007610501c070000a1440004155035000d0f01c07440d40c1c2d40058050903810983c407000480d1075034015240c1621038103025400d005608030103114540c1c00c1140c0788002d2000c0b41c0c0400c80581503540792640300b4254941c5032105624180d207101d41030055102d418040103030030701280008005405c24000c842c490f07052560315410310314049002846031a4031601800780380341281d109075040000100080705114a461000c000145d003404103c3c05020903450050f04d5008800030902800d115410f00103040346400c0c1d00020954000000c10b04440080b01c1450300103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 185957616 1250 185956366 185956369
    0x60e0601090e0703060b03070f120c09140103060305012c06130b060409050f010203010602100504050601050405070512010f060f030507022e0207050c010e060406052a150a0c0e01080105040b 83
    0x82440746c2c44803461090100901c0b18203a4081905500981d0b030b40e81e60455103074481040030455810640c54008203603451410080305088410007044000141000a40e09503030782c40d007a0a440707110181b0742c02c0031108114060b90340d69108014540440b032200070171451030507128010b43c07903003a1b82000e4440107a1400003442951681c11500c2c040b503104013560100208000e205000c0e400078040c3c8000340c06916101854031115200d01c0c1d114030380201c01411980d28240a01006240c00f504110030860300300031032882e80d03440d0b0071117030b0003881440d074105c0f180703458107800601d40c130b5a086083c02094140380034070100e030794000381454030041d503203c2d0414000ca450b03641e0191045045000c001490000c6000c0c002d000e80803543e00d14544080e00c0303410104c0101070812a15204a02906002c500300740030503031541d07040104803082d0001082070901401e1407031121381e00d800f00814410b0421640072081040c2103000340180701e416262820482d0303010071400001b81130001c3c140500ca0140e540c03848a0104d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 185958866 1250 185957616 185957621
    0x50a0206030628380c011104030b0402030d03050c030601180f030b0105041a0d060b0a0b0301140310020a02070b09031c02030301030c060215010b03090a0804061101060e0601090e0703 80
    0x406281c0c503841c150720300565070301c0e074241c0596115410380d003070001c444d06a0200c080c005041d000901d00e42e401003141c1d1400159035090700320344000c1c0055943d690300f10301e4a500000040010f54050f01d034010817464284100751504168490a10815003400d0500480003549003d076a003105090070000c10075900f85805d504000b0003035000c0900503400400000034041000f048a0694109660501030252085151848100c24400c00364001c2d50302c1031340c0404103c541c0e101d64000c0d800200000003003a41c0ea056003000340c1080c0c110610416480b50203001346c0c68204a50b101038840824150f00f4601441c0b400b81d154680ea115021140f50002071044107540e0600480140b00202603103a04100d00b03c1c440255039800c00d0008035092103810320042411400000c2c5140c071002001042d040307031b03800e1405602e15a007000e000412640318801c0203800007007102002c1e0025140035901c200c4482510030205094402e42e40c0000c070152003074414001166840107844060f1464407440d03031070f00d46844100710700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 185960116 1250 185958866 185958889
    0x90b0403060e0a02041514030c10080a02090d110f040506090a11071401090c0b0f0307030f0213080d091707141305040c0e01080c010e100e060304080301090612050a02060306 76
    0x41c024070306002d0a81509120b20094181c81802c81f4032840d00300440306150382d1303240c1e8160003588610200d61201c2c5035841001c20a84c8056141c1c03016040c1012403000c070302e110700c90000031103646072084040306050504c01c00200134000c00711428030007802c2c4000400d0703101c003020f8042d05099031600c0a00a5501d00002110303a401c0d0302034800391503400d60301620740c000d042d418030031260103454071320014114801000390703801d00e000e6103400303460342d161007501768014035441c281d40c00910740a0155030b59280e9210a060000c1c900080505661016800c0040001c0c40765042051070042411204541c2c03840000c3c00400d07a041c0c0b6015081c8201d012001030900d070300e4040001415130a1208110410406504400440e0300310a800c1a1603621803001d240c5405c0c222070414001030841c03036640d1692400001c0001c040079a414412100f09a80f00071880da984111001e85260034000010041842c04d8400e6000828100c00c2404001d6490780d502c58649180f00e1010348104c2d0040023140d09550b41680b0040f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 185961366 1250 185960116 185960119
    0x504050606041a0c150f1f080114060102010c0201020c06060607022202094f14190c0503180c06030f0601020705100507030c080c010504080415090b0403060e0a02 71
    0x1000a0044001000350300c40c100150b0342d805810503803400c05410081c01d46c0103102e10008022140e8400c800481954203090710000b05d0014081e0006800c3d1080c8201c43d076200311b49400a400b403806400190940e2104242d40b811a1710400506500b00d03404544a900240d003256503585c0c81007540001108031951514048486600c04c126070800740441e4002c0a8400d0180c03640100001004105c0034155100303c040c1c0c030002001d101086076012513004849041406207110207409401c0702080d021290405541c0318000c1c004d0f0180425204070002c0700440e9002003001b4084c440c440c403001803243c04003900c010b0100d441c44e041c2280b90401440032020100c0040c0c0703029100d107030064402440d4074090b1019400741c05440c00c00700d010708100500e0744140190780c0343e15140407000d940403a82d00010620645c3e5000040c001c100420401303005044c0aa4007030403900b91103070700340042d82408450880c0d95405028241744c0400135800944190341c00c6a070800700000340c449414010300d05003043e46900a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 185962616 1250 185961366 185961389
    0x5060f01021e16060f09050d0c030210030f0f06050f04020711060c010b19060329010e0d0209010f08060907080607110a060507050d11040e0c0307090e0702031c05040c050405060604 79
    0x4511264803280385d0082e0142a80d420b0b07485e59030b071014401e00b44091b00c4058006408820240003508000c001050741000c20b2500207503440401028004981e5000840329400303840e10300c200f10f285030100d0080030300305040b40c0443c03034203100382e90b03600703508603101d5056024000c04587d049144900303610452136000c018003403200582d8140703e5103002400d0350180c5c43c04a403510360100101c401c0c807003810447d00344840210207000d000f1401524806018215684e00c20307110500b810060300c560320198000d0040f00e9080e0315032420441c4280c2051001001c00307100ea400304404111ba0031000a0640c0c224019041482c46e2040f410946420710304110b00c094011400c0105009110f60303c4001440010340188080094102012211100340b0551103200700141282006c1107000385e01d41c1c0119041192400c1c81da41442c0d90741c001d2030020710304031040710150300041183c80b0008050300e08070300b4130b9101140800040c9850b5407151460800c40c042d85003c1c80d903600c0002c0c06900c82c0c0c02100e01400018006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 185963866 1250 185962616 185962619
    0x10b1003110d0609020a080c0702150f0d0f0e0c06031003110604090510030201030c03020702030c120c030f010209010906030e190606050307082808160c03080d020306030105060f01021e16 82
    0x1340c4040c0d4000298000080c1c00d0000007210200c0c91000e0740c0c601030340100103200310a69000c02642d076420180c050414041c04002d940b4681c0c0d00c2d03107e11341e0800ca036200c01140c0b52a00710701890071f14480a03080b9006000407c03c100c418907582c0d07000c0054951000300d408002d080d040114038039000b2504880e142520b0503060003a64200301c401201202c0c0b00b40d90a10451440081c110244d008915000390154030140b608409841c0c031207451150070703661000315003800d0b43d4140042d2078044c80c04291203c0b6540003601a4042d640010000050f101d10b0400784200b5a650034910707901e002105100780d01d600c0b00c4050303404010b905e4001000800000701101d1619032215461511313109c05606141c058a40c814803070003071a2248101c1c14115400c1200d41d814521250007041d07440d20020011035440305060030210003d60300388042d1001c80010000141c4a1410005040c2100c0d40603190380d1113100600d01e40181030307900080300f620301d00c1d440380e54600c12140c4080c0d003490611501d00d4841d040709142030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 185965116 1250 185963866 185963879
    0xc0f081c0c020c283308010e0a0203010b0703050a020c0a0f091406030303010b0a180e0604050f190b15120405160303020304060323010b040503070602010b1003110d06 73
    0x202001c210408440d07560918081c0e060141121130000103049801225240400001440c400e444144102011203103c4280400c3c03581c540100038035032604003080a0301d005200d41e0980040d401d90010855504600e1541003141254a40c002d40200908010000901c0b0341c40a100380120140088040c00c0300d0702a945503119143c1d44035003409a044035503e0030003c04074910116450b54091200900a14503690074070074107208030390000d09640b0902201071101c80441c5900c03803c08005100c0c10190300341c18202f110401080da0030150016140e816080c0074810300c40128820700d10403440e148800100260344c20003181c04010001c0a1020600005c02c10740038510300802c58a00c214414015070301e211004d1420314024010a000150041c0d1044c00103014090080d40001881050103488002c50f14035407858102400d001d8100408104020030200400c1c103040050101809603400240240001400440c4244442d00d403204109a00da00c030b41480c0213401021500d002c140200140207403500c650 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 185966366 1250 185965116 185965123
    0x507112406060d0f0209030f1c080603120408060a1404020a050103020319020f07052103040201180503100c1101020f070f020f0d0303020a0206101811190e030d0c0f081c0c02 76
    0x400c5002380aa1280c10501c041c003c14003482071000700c000c0300544400302d50202c0d016a8001c00c5207806210341d400b0801580b02078000f40c00180061001000c4a2605803001400e880040b03105580030381101d401c1c040140e9031220b101d4244c074401e20700140c0f25034440c01c4421803000c10302d440b607180d07520010700d920708500300b0030003401c032640191b04a943c44d00754458072402e4900030315004c66040d48188081001503100385e907140e8013000d2f181442200b0076203580009040c4214030500c0d428095541c0d0b6602d04887d000305c001d250004c1d400c00218184520b140c1160098440c80f40010041c0303a00d031600c00215581c44007600c24261000e0031201d08945203107000780095001d480789230094807901002451048410ac013070801c2e500c54921917090032603c04800b101400d0f650b001811024010303c04144c2c099496031901c00d084801d45c3d40c0d83d12300c116072802d1508041c2c0d414040c108000b5101c5420003c00c4100603103100c00c1d5841440949d0302d440003401c1d80080202801244034960921301008815540007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 185967616 1250 185966366 185966377
    0x160506041403030106080f040c030605091e160303030b0310061e0807121202011407030f110708040608190f020703110c10030b0d020a06030507112406060d0f02 70
    0x40c060040001c1805100c01c2c0d90340000d1045034001020503002540b501e0201e81243d030464498642486030300c1e140c0d9203010680b003003260156a1980204c0341d40e4841c01c1c00302c140586141140c8090500c0e00b5440c5200e0604640c2400058103054403180a085241c03410449040b840e00026400c02050341c0b0f900324202007a4614079052008005c84030007151820020605104580d0000b0b803e0b491152103a9402008000b0360114030203656940c81c40d0742c00b000d2801003162169a0b25a00050018240a801c00859032040042c03c6401c10511044c40043d50810440f01036880c18141100d1960310005070428240300c00b801c4521060500c501d403182004142c0142030b94921036150780c10300c9080a145561b4503160155299030020007034940c001420f0095000c61000380002d040c1b40b0b8519540d1700407a81440c4903a00c560b0010f071303403181044005a4401400e1801c2a01d032400342546d545038481c10540b28a40d6418000b0042c2e68001064140d5229002c50b0442e050103030082c410080d60300101e90094000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 185968866 1250 185967616 185967623
    0x403150b030d090f170f0604053417030d061206060b07020a0b0a0903020d080309060106050309060c030a320105010302040305070e06010309021320181516050604 71
    0x280c0d088090704034040c2e407091040c0c403c0c2c1d0313030420780351480c001e04034010019220056180340180202d081d50366000703000c041d00c00c0b0b0195000f041440301e1441e411002120300c40f422821044d00406003d507107000c1b000b01030100c60b005203c101d80c81c084101c8040c00d510031030300860300c0d0318584400002c44072500300120500500800c0104010707a82d50030303070442c0b912414400070b500c0742d00d442e03040c44042d4089016007401c819078039003084075a440e5804a01005880f210a40360032101004000303031346d4402c01c6014094905860841c0c00c3d42031041c851a91590040c1000c00c0b1580040002000031896501c0001400341840002502c2d2086501580c0314201e09500130800c50502000400e4650083c001c95044030f9024000300303103030b925000e10003400c040058840c074101501e540d00c5102503960030b440804508202c0600246000c1c40c080351a031b81c880300c0340581024480500040e144041c090910380250481038692000c154055154900648240350003403040180802004c0b081c8800058440d2140d4030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 185970116 1250 185968866 185968873
    0x80d0b19030b07050c0604030f02070504140406050907030f0b0a182603010f06080a110c0f0105150a030f02190f050f0406030831060e010f031401050607080403150b03 73
    0xe0312001204c29100304040a189940004041070000e44645600f840c0c10341e9a1055540950b02d071000201039070b1000c00c40c3e40c002030580307060100f8003040348102500041400010900a031441d41e40401c4a920340c04042c00d209010800201c0c8440e90350031420701903191000510b07015034180f8016200e0f11090300d17034250100400c90950840c420381011a8142c900b440b49188417645004c1045a10000040a080c1044c0d121800008103406960180c062000344001416031100c140c4441070850710024a4003031510360394001c909003502c501103403070182c03500801890350720314050011615480d45221243d005005040d0001420201068845c0940e241203da4034000400076040000381d402902000c0c024000c100700b14418030300f01c0002d041110501c0340800004e40c03880c0000c240740641552005000c00c81403c07811000b0340e40078501f101414914141000001d4a100300e80b040008140a040e000c1c010000301441846156410745000316440880031104140e284e082c03101501640410078001e10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 185971223 1107 185970116 185970121
    0x601090e100c050702101d10020a0f1110020312011401021204091b031a100c020415031101090b0a0c08070203010c0c0b0c04050d080d0b19030b 63
    0x10029160184c4981d094010b2251081c80c0c41c0c090820400c0c0d4034042c0d401494207003804142c008040c0c441c40000c01003c90160718000901d540505442c40150744441000300c00542810554030a851f1040195140c010690790303401060f2405070b04c50b11110060111608254040c0c6000e181407048403100021082e05000e03660044d040007641c0780d1101105501c0b016440c81c0c0c640032000d1441c08001240c0714176540540100c03c103c6c220710500000d8210300d602c0b1f01c980302000713103160000e00400c40d101c00b20140302a01d5141f4841228a40c0003060031350383c01e6008010003800c45120b00400740c80e291050400300c40b000c1c3d025504a481100500981001d0b880034858004c03280c02c1601d0b050840300450612040c0c49a0080c440760a00d8420002807040c1d071161540c1541c1c00d5408910240c80384103142c41032018009100c401d50f00880c08171300d540c059100d08080e03030085074084c3c0c101c0e030005e8 = true := by decide +kernel

theorem cover : BRFrame.Cov 185791366 185971223 := by
  have h0 := BRFrame.cov_init 185791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 185791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 185791366 ≤ n) (h2 : n < 185971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
