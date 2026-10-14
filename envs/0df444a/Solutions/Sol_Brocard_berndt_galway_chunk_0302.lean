-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0302
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:04:31.963646+00:00
-- url     : https://prove2.me/submissions/bc8269c6-b3a3-4d51-ae8a-0e172752b96a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 54136694 ≤ n < 54316550 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 54137944 1250 54136694 54136723
    0x1210050102101113080a05010b0316050f130203070306050109172508100902040b090907140102030705070609030c09050403050703050c030702090c090112150501050c0f07060507060b03 81
    0x11078000744000d200380c1c007400f081820310b600c082c540b02d0240082c148140c0360340c20010303054012481d00000c010f8244601100382c002030b40508600540d540d40788245c401c048c85503070b001d03c03d2001c80e0183c95854244841c0d003120092011500c0742000c060003401041745018482c08035211800c0460502c85242e1a49000401d010081180284606483c1c0640e50704004980701c0c1c00300941e01084001c1c05114428440ca0103440c0092208084d0040000341c803502c00175140500d440e0402d1144500340402c12000340c0308040d4482e5070b0b50f070410740104c0c9180f158803c00740113401403480214520381e0021000702140d0240443c20400c90300c802d40c90301152010341300103010510070406200040e0007800030741080d5990748140c0e804c010725600444c002403000c84400f00d0155000038810300c00d40e0401603d482c4000c03640810440c03e002001804020644c42c01000e040c0180443d5000900200f01300785103080480d0000d481140b641c81c4d80152064000c28021a12107090905200903418001465041c80c91031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 54139194 1250 54137944 54137953
    0x405030a111204080606130e1c0e03070e060111030f1c06050616020405010b09030c0d0606120f02150c0616180618060201090f110a030212031210050102 67
    0x141502600d40c075291280710700490003011111080c500307419001d44000d25014002e4082c40c50910104840c2e100e802e00401340b440d1410510003120000000c501d98101429445d0700002c6c40542d03000d8032110440c1c241c0a1b07252017404008a20b0b04210120140680e800b071300c0e02d500c80100e4a00030b9883e4020070300c41c101e145000344084484900c4018602c06100100a400a51a6150b00c049255640b268902c03620181c240c12088046040612a05004182c240d090f41d0a250748800000d4a41d25901000e910a90840401c02c09101c4203500c0103000b48070400c1e565070b4001461a044002c0c00c0e00b44070a03489481001150a114403021084415800c3c0350400f402c2c081e510000d9002e90985011020010410580305010390440804540000341189440340120400f5441e40b0a4100da810b4008001b1641054561400550ba412803543c6480c2d00003940500a001c40c00414800105580003079841082540f02d800e03440e201000501300e03104258401b40307040d5a405180d0500308064460640103a10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 54140444 1250 54139194 54139207
    0x5090c032104050a170c01020d0207030201140d06080d0e100804020603250e03120a0512090a06180302060601080103030207090905011506030606080106091d0601050d09060c1106040503 81
    0x104a07000c50301e001c001d9a449003025100c0000c00c000400c2034009600794000d80c85582c5803403900f000003081d808403d01c0101881c2d001580000d444095510000741801b0420319614a10000113054800141c2e1203402080b00d15507948007190703600c110400c0c0c8004a013210320401e0803810304a00e100c0016500d80c5401c0d406803990b60a22140368002000100310710550803030402c2c007561180710b03101c4800c4c0658134601000181c008042c100b41c0340c1716503510005001c201180e051030300314059a400071400240800304c0d986030141c07542440d407405c0d0024000381c41c0040d4203030310194220b141004103019a085804a5803444015518010b0038000034004d607100f43d034104a2080250070401840348600b001040d0390607004082080d9011070b40084011a84420081c4000ca602c0301d03445004040c03901d00b54025601c1c04000108076554910350b030510034026800281180d029a08a45041c03aa03100104602941400d1010007482110742d554001029007155007103e03a00040c0380c41c040c54008001e03510341320 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 54141694 1250 54140444 54140473
    0x61206030206071203090c09150806010305120a050418050a060902030609011e0e0c03061912020607020a05130b12010c050f070f0218010807060c03230d0906090605090c03 75
    0x41c0780f40413203c2056200d030f0f031010004002e40b456074000d10329182d02003034090003401c100c01041032a800c201c91a521040040000ca00006044890240701c501140d5448820307400440e4a1311440d04294102ea912600c156803511840e03018521584081204120941e1546000011f0b44000d4074080d500c03c10840051041280040c1d6010600c0c1c1014003903444aa40d40d072078003d038120b0403603c12203286000700802c1030504040310900000d4084210100003282400703c4140c1c103000740d1102034011800461250b046483303182401014203c01403c1042010110710f80308094414107074038074011040303040814801d020500500800c4900750303d0305801e0042c1a45114520b42144106482a02002c0191809611100d881a0354140050b420b507600d0740c1003402d800d00c0c04510350b210404100c621a0b0304000301c3c2e801501b5142d0020516064091405000b400e05000c0c055607010140691400c0d0303180c01008060b5201c3d45c14144036041c144032955800e135281e9103581c2045a0182c054104164030b800c4e41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 54142944 1250 54141694 54141713
    0x20303031501031e0902030d0804050a0803070507060218150c07030b06210f0613020603060d050f010c0e120a030503040f06020d0510030201021506061b031603020706120603020607 79
    0x40d41c040c034000030725940f400902c0300b054507503500072040a41e407041c00606600702404180c1c3c1e4a01142072910280c202642c0e955926a10740c540030b0b0008801201040140d4828030031a010341e80c2005042d234684840c020510090304198080c03502c2142030002c0302c0040c040d0501541c3c00da040000c050007945103945c840080900c001419950721030340e1080d0884404080d0a00e210320014903e008010086a40301e035146008409080400000f04007580140107a480b4401c503a07106000384e468411650842c5000ca1400203660355146841d42416541075869901203100c44c3c58200444030040b14455092000c0d494616400015001540420026011400342aa000d03000d6208240052a0038030110944046580030b50300901c115a1400d400c009641c1c1c100100c1150402c90f03204007080c1d0800b000020800c0c81102d81d45961480c0c3c0310995005180309200b6602040c0c0042080100132a00c1d2038001d480b40f00c1e502038640800c0700315444040010492040e02c00b5283e0140201d4604900e0f07884040b080c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 54144194 1250 54142944 54142981
    0x1101140408010212060a0f050d080d0b100809151501140708040308040504060503030a0c060b01091701020a180f0618031a04021302070201081f030b0c030105190302030303 75
    0x519800300030000d01031000348000c00440800c1848030460b402c01c501004160f400c143c4c0440d03840000b103030082c40580d6a001c140e41042c0da102c0d0410781d0328107000d004400980303213014000b07500c2114919108001904074600b00d100c1c1c49080c040c0c4032140750592108100d04020759030303547e0040203040170490f00e5000b4928019a501000324513401d100c0c0d65a00c1503601d51040d001291001c501040412403424140500c8003e800110061342c10a11602e4008150403500c110103400c05446812918969009040c40030207000902145404142c6407006075000c0d5020dc20344000082c03113000c503c039201103410041c4041d1958132041c40515881d00d0710440b44104005c4a0403030301c02413080b00000180031144111880c000294802d546c80c5014010400140c22040300e54240500401c420070060380d00c00707100b682c0450389070b502480c3c0e584018803000c80c080e4541c0004208098036401e1010032032410015504840003250b142c01c1ca480341c0500600030f01d07000d01c00250564414804612064240c40d0346808 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 54145444 1250 54144194 54144227
    0x60c070c030c060507060b010305061305060f0604080109020a050301051308070302010b090702010c09050108010b1b01090b070206010f0503070f15020a05012d0203090703080d0209031c08070c1101 86
    0x803015141d403a540840303060b6038081c5000c070300d0010300707a400c210007401985402c103000d080801282c5060800b1a050b0000d45241c8290262b0f10400280f081e515064603564950b0094007054480b07444581c1c41c0d009201e040c20a070b100780d5000c2000111440c0502940e4480c44915900f030b24001300d19600c0b401d146d0450301046043d9504d95403c00325544460401c64419111036001044050301082d0142c02048075420180c100291500140002122401145c0301c0184014204401d9a401c9108034014802c0b030380020811401c26080c42070741d5a0018006d8180d8601610b5640e205681e0b004042d618162482501080c107403441c0200001d118000c3c28000158240c0140d40e5680000e544040c01c4442c55040388101c3c3c1046240b4280a58090703c010380c400001440c01c52960030700d000c0171a65514940300085c050240002e0100401c51503806036408050081c04841c0b2400350f030500711004442406211001551030800541041c2c800c0b00c0d01006c1540205442c49481c03500c01c011a00445500c02855 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 54146694 1250 54145444 54145463
    0x807080d0504030c0b15030606130609060b030405060907050102060601080603013314060d181407061704030f08180a060f06080d020304050d02041d0105010501140a02060c07 76
    0xc012505801910700c95480381e07070b41c101030100700c1c074001444080141c030444404001039080c01d400e80f400036503503400c580111100703400a510401701c180681030302d4200d9040b0034144000014803554520256014078410010703601c05541d10396544e582da01c450b1042900590116020a50707071350003402010b8010034041c001007070040e031481418090115480f444000c0394814212007203e0305903802800050412030310b09200044400001030f203a03002c0d901180344190b649600311b240c2c004a010307410304000d034000200d80c40d00c1c0200394420745400180c4120b0011a618183c0c1c0c2ca1409a203d144503c40c6900da180d120342c81540103000ca03141c1c01c0040c030355841ca101e190000e00303d502c81000b0101e040d0340f25a90205207140040400d009a46c516840030810382d001c6848559001d03008016541500e105481c81c245207c00c500005020f01003015001804106000e4151402401904210305031031003a2074111300c240ea8400d60041030f00c1340a0b0340c0c400680160740428441c482e00001400703198018a180b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 54147944 1250 54146694 54146707
    0xd03270303181e05010501120b0a020a020708071d01050121050402040b0301020c0102030108011b020706030b040b060703030c140f0d050606091801170102040e01060f02100501090603021f050403080708 88
    0x10303840428a088840b118003e070300c0d415010041d09004442c05045d81000c4100c1c0d101499403015014000074209103c10ba4003c205102001d10801c0850010f00c4c0f1101204c80c01c540c0c42007070828020742c01861007800c204050000c200780d401100c1000c18401c0382d000c01040342c0c1d590710140008001c05041203a20a885e40c00c00c02069400b400680084404000016500d500d40200f040c210358070f01580203a180c140100c00864540c0114010b030449074182000304400342d0550005008140e00e600c4554084808201c400038142d1507800390035008059240c40c883c1c040030044d02200390180b95402405a034041140058140c51600071641000020b45a0340c21301605100013098002d14450414988155000411600c48000421400314481c0e000840c40c0c03c0c10902e15131003022050203000248001c4800000100d44200060300511640860800c19541c407248101d001d0000d07403100340e02c95078220b4942d106a41c0d510544d011001c8a03030f110640fa20780b66590389000750708690320a88002078280040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 54149194 1250 54147944 54147953
    0x100c0203010510051815100306050d0c1e03051209010201090c14090f0403050702210d0206070f0203040b07020d080415080126070b090406080f0d0327030318 69
    0x640f40500050104450064140800e1085002194004076181020002401449120a81030414041040d00c00a44500300c00505a003d0301856101507001710540c0c3e1940b0500500001110503260104c1c07425500c4030200c1f00142030a00c103800b016140d40c2102000607030714992440203100407441800007207141d46007500d9609805190340e2200c510030301d800c4900c010920380310b07074a990f110345000540000b50a10340c800038118014140c000340120700e03429094000d06010752803004095000c0003195440f01840070000d450301d5040d50040d01003001c69900051581c00401500c042d00d440f00013041c106010383c1c003006a02218004103840180c0c0c00c0101041d95000c1c032140c020400e940d5210118030354503082c0141d85440403400042c511140d074100a040b0441c020131160210341e000901907441c0d01c068800200105040d5201000c0c0d8424610410130828002c100c00e400d11001e03881c200300020007403011003010340781c02c104012340007007000408001a01aa1006040707061091040c000501d56548 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 54150444 1250 54149194 54149201
    0x61c0608010204090b0d1106030a061214071202090a0209040e10020403120c0203060a0f1e0608120328090204240902090109030b1806040f0c0603020f09100c020301 72
    0x5040541d40009041c01500464083c607400d0300300580311b22290030810b450385c10000d40c09070000d501c610000408208020b489800c5803010385080750802ca440c0d856840c01441582202900c0c1402c0d0254520014481c582403040c955010307000340c14140207503507402d4040700a600040c0d98a5001d0f0344c0740c0e083c00003510100680014000c8440c4010798550960a21100019141d12504104210603529400584020a445800011072580490810304000040c80608040100203190000401ca018501d40003504054101e0702030790256142c603000c110180c0000d1204842d60801508003420006407400c01381032564019400650000320081c16a000405a442c404164a815100c0e0307001449079107082001c040003069100000c500e04a004000a040042548005841c620b01480004c21a6503400400946a20300205a50300f500d020300e040a1232030301d900f5040c0c0d12500101d001103075880c028422201100800a18103040c840354a003000384100c4141c2000d000c11900c05a11300050b2824003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 54151694 1250 54150444 54150449
    0x13080304150801050306100909170c0d120203090a020108090f0706050a021c0207090b011e052701020601030807050f06070201060602010e0a0c0b22030503090a061d061c06 75
    0x24807068441c880000d01c444010303002640329800040c280402d12880e0401c0c00c0441e0403203c408541c0007050b050000f40039003140d51a02c0240f90008954100c250301041d41d152034481038070f841d1903400040190004034002290b8425031a03000c0800c000241d80181c602c658002c14450844607628a810416410003005601010120b00085194910603406005205500d81c210351000005d50100c440255108041e00c503444015560b401e4000741d992290f803c0081d09a415028100034800240d40100703241d1240300c5201420a088645080006500c1c0c41c82d101d0410580c028032160342540c4a40d8001d51045604403030310300c11210131480f4100184500c52050301d00d90000903043c0c0c98588042e094880c3e481c1c24800c90b80118024000044030342052006541026080d1a00c41c4500150071a018074424040300031411140c10000c02c1000020081030300c0308060340d040034059640c60b020390300c1c0342d40c101d004c503400300640e409584a81403803005031080b90040c01c0c10100502103000410b00300c40494 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 54152944 1250 54151694 54151709
    0x30c0304050a2010050705150a0207021206040507060c05030409050c0c010c08060906060a1d06040308030f04031808060711010f0c0504080111040e04031818020705010507050903100213080304 84
    0x81c4103a1080d444d0150f920b2503014903c0c180a4900a8555030300e036110a8414516030451501001240150500703506075014141d01a1240ea14010400703001d030754681040758111000c1c46071a20124400d13105900e0a181907600800550900e400c11003008043c090051101d09009000d02001003852002d005400c4410504e844010040c10300e0070501c842c0072030082c181400f030070042005a011991190100070014402031410500d0081b210010f0f595201d1680040c02c0f0312070100034401e07007070404100c8500451003500c6030310a1100d00e1056290b9840c16202c1d90045802080008203880d010b00d915003800003240000003035030385550381101c1c11196a44800740010300040703810702c1448400d100e0308000d0115503481c20b0601e13140008800303911000400050401200e00e0700d12030014030307500302d01c4068280f6042188040004030800e0f0029001800161140d60a050108489501407802c42d5080030024002d446a0303501c05004101030361000c828809044c04070000040e89482c28006000540b00b403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 54154194 1250 54152944 54152993
    0x20d0c1d010509070905090c1e0c06060a030f06050a0f0507030605010201050901091110050705010c1d09090601060302070f05030301140306070810231f03060614030c0304050a 77
    0x124048030030303000580040b402403444005100f401900030000c041104c42c01c03213035000641e4482c0254543c0e1700a4a0003174000e44031200a0300410607400c00039000d010a8201105c0041d6102c070100070344501d0610001e031041c21307420301207404900310b83c0101c0d070311142e0844041255582002e00c1000c1300c40440300361000a40d14041401550390a004032600300046c04024032802045454810f91040e23074602c580d1040b040c44003001c00d518080c03030903074010fa50448001c11910341000d0011b80341510250041000c0840b070070301d1080b6440c001c002d032401040248000d10540c2c0c2030032020340007544011811764039501b04155001c00100c081000794041c0401071b2110a0b004512020305250000c00f41c505001d00c4000c0d8104010301c402045000112001440346140140810400011441c0d442040d0740e0820140d500c800f9092140500340c50641481e0360301002415a26001114000c8030035451110050b8200302044180303141001a503001400b4174151044003506585003a025030302540c55103d400d60 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 54155444 1250 54154194 54154229
    0x50d0206010510030204030b0f090a050724020f07060810080303040c0603050906070c030c030e030d09030b07050f0405101e0806030d0503040203060a0c14040803070605010506040303120207020d0c 86
    0x800340c2c1c0c4002803c009080c15410181565500c0001600050451181d20742d140d0005e000170300c00304124418940c005099515240c0c0b41c07603080c01030a1080c403510100e14100c0c6154424144001200510b030381c08000a00059414003000300c45000029101e041e400f4041c0401141030359092000b58003940c072641c5034001d66490028040e040c0c40000f0102c2d69140c21072002c20080c02d40000480004a50514155205a41d41d145c2a0380c01b400e00840303150140b080714a15460990801044000c1da40119024000d6a840720342c2110140300300060030300030307010a0008014504014a14842880140c10112641e0010b42c81418007c00c2403c02d4000152010051050350709091204004ea42c0c010300d080c91540c541030b00803d594180c0540a081681d44e10700031044d500d440341031481002c54020748038554440e603c400c0156650000341080e94554501400020315180c400304031303400c495041d1950849a02081e0340503009404c00380d0140d0b00520101214000a904038003d9005880482080500b022 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 54156694 1250 54155444 54155449
    0xa05060d0b040c0201020712120906060305010b01030506030105090a02060706090501020c100605010512010b031302030f250521070915030b0708011a0921030a02150403050414010c050d02060105 85
    0x8072903c65420943e4410132440e00803c407043c0701c0600074465410304841480c210600480103080400300949074501d40070005c0200070042d00b000d0002482640d0a11aa072188402c0600300e400a03150000a41c5c00300d00c4c0640103050400250002500402c000070b07441c40c0ca0344406017664032800795410290000b9024640c0c450441c4902d0010b042c003881e0250601c14036095020b0101c4040c024001d20a00200010700031340074240811654650207400c0d00d1480544182150762940451701b51405601c0d20301030042d641c0c00c0704011100f100d400600980340022802141e641e0400004002c035003a025922010800d500c840c05810385116684101c0c42510340703141080b84404802400d4041040120801000b0403034401b400660580c205004096840000030001410041d0960f990f80181c162003280c0c0003405004001361071100c4064003900c26400a9030312140300500e0445000300400c1e014070003401407801c000940c003d804418102200c10040c6030711044e1030240304a00140c0140c0c42400140506e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 54157944 1250 54156694 54156701
    0x40203010e010e0f071b1b09020913050f040f051507050307031b0207031b0f120b1305030a0e0406081603030e0a050102190203030f160b0115050a0e0a05060d0b04 71
    0x1502c0c000000d1181d04151600420354801c2846c02ca013042011350600051203070052800401a002200419000e0354600512020f50040075040d4401c543c0035080100c0d4080c14069107101d220540703003150a5660f5503075181e1203155440360546d0f0038440c4d0010300000b5208035240034000c000035140c0c01d07101c0c40c4c554001810b4803001c6110300c1c031444214950440d4cc40d000203a0005603035100d208060000c00b400c080901d03840c0507900036102c909000b02c00140c0b9480004a8180560048410300161380c0c0c0c880b0100c0d40401d004000800d903600404c4a210038500c95444006040c0c4c006102140c920780d24a00d0618201c6691109024a10319a0b003c01c100354202203140c00960742511100e0741c50340b8040010b034441010040c40c600000c04c8400304400c40d5802c1c0126001c0d002030302000354854007140b2040b050003d002000f152240040c1001144542110700880040c4000d40d891520f041041d40d402c50307022085201041d0003141d0090042481e503282c0c406030a007200c011400148100c0a1020030007039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 54159194 1250 54157944 54157951
    0xd02040510090305011a18040302120d050a140402060f0c071203020c01022107080304171b100b0f0402070201090305030d0209150408030a140903010c030207051522020d02040203010e010e 82
    0x506600c404259058440c03081d880c0110386005e1600917590344a050580c184100041d00c407044041c00075a120f0cc2490b41e612050280e0104a0f08003c5c08019146400110340241c802a6118100b0701242c140901c50f5401041d801c0d0801e029900d46a030364004003540c80c4d02401d4200d0158202d0034203080c0c2d03540d0400c185004606503900450404250602d0342500d441440704c0503002440000c00035044c08010324841c060820310010207552007900342c482c5050154016100205402103102c43d01952259002da50480030004040782d5803001e00b181004025401a03004034180005a07000201180e802d0000d010000c560650150340c2d0102d0008210100d112110140c1c0d0310882444248003c0030000b003918000d1507141806814411522900000b602541588641c10740c00d01c410101172590503009001c0e407070b21035402c450172041811020540d6210444011415154038a110841c10f04070064869006001400c59441515150082016079000760000103180700070200411044145212440d403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 54160444 1250 54159194 54159221
    0x8040b060a0605030105010309030201090507150207080c010503012321010e060903071101091809030f26131713080f03121009091a100602070302060d0204051009030501 74
    0x40307850426101800901041c0900360400d0390780d02040003014000d43c8500382494010302140e9600f580c50204540400c41d540031900180144880040e804000180c8481404016120181160f082c0024000c200e8480000e921010100c0c40d1300c000b0a468803d0004511a100e5006040f17203600c2c0c002407800d40300313a82c60106c120303880503082041a030400702c01d81e1581c0b07038040640d003002d0707001c003004817480421a089201c04a129054125000312140e00200c1a503100303459803006040025800c3c2e4048100b21040f6285000d060b000c8a0340142c0070344480c3d44407181c0503003040b02c9078543d151400a020102c4d008038407140300203640711003200d0414654008210110081c01c1010710f130060a516070080340a10340f0201c1491021561150300426504050090301d0800c100207600341c01c0c500d403e40d1007251039448154802c001319500014101d04601a18400d4000380342e620700e035909010f62540501c1660020350f82c01e0002050aa44400c200c807140c9031203942e060a841d056040040c01c58002800030074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 54161694 1250 54160444 54160459
    0x51207061b0f051b09060904020904060e0f0f0304031401050c07060203041a07030c03050601140a110c0a0b0a080a090c18150f0e06091b0a02070e0708040b06 69
    0x45580800940c5040d586a50319403200d040e01c1c50300c142d01000d280c00003800c9008102040c10318004203001d075813400303108039820350060704c448050105444003540c0203034100450500040c003182c0c10b40c224450304103000d01110581055011704504021300d48000703040c140c000180400a010380701e0b09601c207000c00303400208181d04022503a06d000380300e0020001d100384c0c1c003c000a803e1040b403008280840c146170002150038608a04014000c1c4045a44074000c0780c40c04020919652003000c0600d0a86414003101e45003240d040740c265041d4009072003446691241080d4914507850f40d40002c1c0050445100054441c00c3c6910003a000640081207010020b24041049002c02d1075595440112072501c0c10304070604810702100d10160055549043c003844240034005041450440c2c41c40450308a140460b6107511400c04010040000b80d50201100303441d0240b00234141c3c0c1050082100790a00e0040350034031507a85000700c1c8c44030821101c501c049080c0c44100420311120b07040096126400715201e5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 54162944 1250 54161694 54161699
    0x1209010b0f010c0c08070b0403050114060105161e03020d0f050721030f1505030c010e060a030c022b080105030a02090106050a030207020301020d0207050f0601080c090406020f0a09051207 82
    0x1c4140100001035410445008040c1d070034400c80c01c0301c2d00f0141032407106071a031098603000c80c0302c8180c2c028401100d042d80f818007410301c0149610601801894140c0d555454200300c0b010407600c00303441030f0065912198458a4080c250700404a1200c0d481c0f007038028143c1004c078640081d05581901a00000707210041004c400004c0102c23140000c0c02c611909400d154132070082048000f840d4195900c8400351614410310000c13402818140102c4008608071189000380000448803000000b80454000005200b0783c41440d0003034003c4610b4081c140304486001c910b00c1c135500240c4030066400201d8000e00c4141e030807000d80c00800c0601424003a0001d040d00403090340441d610680c14411001000404100000c2284c0f1980488000c20f400400a6480b44411800310000354800c200c11900d5101d0f01d445907a0075000450168121103001001c1d05010310100c090106103c2c008000301c445a0b0300300841c2541c0b4804070068000b1040594480e8074460404090040e100000e0020681650014004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 54164194 1250 54162944 54162949
    0x90123040b1b0903010507030e1006050a03020d06110a03020309060709080a030e031903020309040c0318110415030302010b030d09210f0206071505060603040b04080903150108031209010b 82
    0x642001590359469000b100000322107009002d28800740341d043d401c140c18050141d13896007101888d50880c0c000d41c0c2c10071034008601802c0310790504c1080d800c015003030030400c058982074040d08040e0340280b501140340a00880b0012181d8018100302c0c001c04d502005002c0300f04000c02c07040e640311049051000217941080c8805a0307801d284070008040100541c1c2012440d1424800240c0f12240b20500101941c103a1038080e4498000c00c003018019440c068010860307500ca8010164000000020840a40318946441d42d4200300704445542060700c41c07403100c681da110310000c4c8006500aa0002134030314401e030201400e0010f00700703401042014030300090004140c14002d4460030b000c078903151280464185040401902c5408000e90300500108405c4180b00309888035402071401070004015640d100d8042251902042c1c40c080d0191100714002800261400d00401c0504002401c0700c1c0941c2c941140c0b40354851007604040c0c0590408280424034010034070070b95400206580082c8030400440c0003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 54165444 1250 54164194 54164213
    0x2010c050f0307140d06080c030604020a03020603040f150b0111060c03070e030c040905010e0618030a4d010e0a0b13060e0a02130e0d05090a0e09012304 67
    0x21600d040e14400800f048540d0b0294081880091074690025101c502e203001303100040c1080d12400c40503001b1910a0741c80c600d00850502e03c102e5008164440c0035007142c09104980d08020402c882c030466030100c400209500c01461110a00c0c00d840120742c40f062100010812200c1d00000f01681d409681880082d44400040e04da001500b0f1400c00c007903602060000e850104010056030f0131510741400d0784140407040d00118074406441c02160303080e8a03808103910018210541800c0550028071840190a200b10380e0060b40045414440186400c0400a084a51318680342c108034401a51202c2c441007100d40203044194042000802a40400b1401a616200b003240000c0440007404002072008507281641c503034298108004004150544240a81d00c03190104281c0c0f0603d034486100e00c1d2a02070b8080c540200040c400035009500000f44c00341c03078a401c48400942d00100e030103404100f0b40620801548035415500010403124402d41f603503040004512192580000e502c000c02002c61102e92 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 54166694 1250 54165444 54165457
    0x140a05060909150f0d06050a110f0414010507060f09050c010e032d0f010903080109090809010f050c0a03021b0301050105091f03140c010206010905060d060b06160c1502010c05 77
    0x98104501c0700d0140c0004c00c0350b10611502a444940b9038507100c00e0007203170341c09588100804803042041c284880754080450046840b204241c40041009011903600d280d4138000321481030402d00d003041259507850f0280c5001c1d0010702c031601d03601c07004d02c000c0c8a0204481710a0030f10a01702549100103c0b0046600c800201e00e40c03001c844c111410032140c404489400507588140704003a1211400040d100c0f50180082150a81c0017600075000428046518480c1880440d4007180308c0d488c2c4544c0600540708000b00e041c8000c240304040c800300c1d41048050001c030541c1446030340908450f41c0014008002048082d00a034001d0b85403c5c0184010b131030702c0701d0142d00004070a503d2080807824801484c0c5410741500010071071034000d520f003e0b400b0303c005001010a40e00f602030b14420703030300c17144202c0469008590003548011100620b001044043c0c3c00328100c0030014100601d404042d90b600103102d1a405400c880007115824208a6032031384800300220100b00b48000e200440403400300a0040c026507 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 54167944 1250 54166694 54166711
    0x20603130c141003150308070f0b0a0b18060a150207050312091c0f020a0f06020f01090302071e0b0a08100f0303120b12010e030d0f14180f07140a05060909 68
    0x218901916203030603154034030085a12007d425a2110289440200d80b840002d04660125030140071600c101c02d180a4072901090150400800144010803400744040280626070010b83c181008954010461020b2058500d5900100320851408081c5458121a4104900884400cbc0001259030340c03001c0010103011100c0e9041c641d4181e00f8101119034807480c00c1c00a6200052190000782e000e00c1d08100340c103c0e01141c09a48040f810741584901b80e030001003001b401600051414026888907080c0300000c0725460350840b03041d54079902426a694002c02610010840316010400c10202120200010741148180c1890651a50398080c0030711b03c0c6507400341d0001c2e071944130300ca0845c0c0f00d450b596880c41c0010f000a101d0341c032190350b100762242d01074260b2031002814800c81d0261420980558084641c4a0f00829925a15a6410407412043d1400900c00b03008174046d00a5516081141c00040d102d501000c40c52106034400b0000040c4d01a44420300444041c868541030f9580c014045601c035040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 54169194 1250 54167944 54167951
    0x60c06040605060a1e090501061d01030507021f0b0a05030d020d05070305070f0c0f0b090f060306040207021002070501020105071b0f020f180a0506060405060f09030703020603130c141003 82
    0x144400034148100e140c10540d45d200e0690f000b19024050343c1040d4084800d020010000d80e602c80700100d4130300c8003034401d000803504080719100540d44264409a0b00140728415100d020b12681c50124550100c80d01c0c00d4802d6459240d691418513090003801c0c010b010480042140d0040440702075102d000c581c0b614018088042038170003d05015034103c8050b030764413000070700c05065540740c03020f0f44150314010b804800305844004100b800d50401141c11035a002031441102c090108104a1140d000804881c1c02c15024030400006840d03a14070140640c4080d0007602e9054100340009084400c02442d04c0100400800d03139815020001004801e100d801c00c410306900304003030010444944000c20020f4114030500040c41200810009041c001c1010460601c0252104010060a030085020720fa42c00b020400012180c140d0a00003017244100c007400303488100da965000562150000c681480003407141c10080001c000e80d140d4100f003d800110062007107a001100842d2043c6a07000c3c030102850768 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 54170444 1250 54169194 54169201
    0xa060f0e0607080a02010c020706050d050c070209010b0a0e0406060e0f010201060b0c1b030d020c1908010c0314090a110d1401050c070b09010618050c120420060c06040605 75
    0x4101090451032101801d8039503200258900102c0c0c541c4400f24082c0103511745038000b4101c0b4804507542085522950700c1f80d05102c110305c0090700400b80030b00200d00441023049180010b8560812441c024910307482a80d480310030450b8003820a51b403c10383d0f10311507031400c1420f02c201a0443e204891104080d0f40b2121894100c00050f070050546070480c4034050808103040c076151500042184803110b400c2001e8034401c505c00c003815503851407a4002c40260300981c070354440074245a0341e51110035146e44481c80c150366855030f243d421940ca08a4101c00a82c0340c14080c4a440303220b250003500302d94080e00030306080d0381907113425110b0320207514102c0c403602e0003a01030014402e81c0301c1b4a400c10380820008001a0401c0c401001c580c0d40702c0d050468043c9001000203d400d40103100e80390480c1c1c43d0101188910039101c03100070040070005c2c40c1c0b903076440c0d00348410104c031890400468402ca00c100b001c0202605010401e08041740381800f01845154208900c1c010482d020400c40d40181d8400360121b075584 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 54171694 1250 54170444 54170447
    0x3020d0c1e0308040306022217191502130b0f03010609140f040507030204050a120b0c03090615011e0801080f192003030a02010c080a0207051b0f04020714010e0c0a060f 74
    0x32002c43e403c0861440c0803101044009d0100304100740014100101e0743c450840c070070803d1a0300f03003101b03002c3c11001250b424000c420780c5c1764006000034040182001041074840301c0c002225082004001d10001003c40140003d0760000184000740c038107203111805030414880080e8002c01c150f00d00c0c501450f1200c0200d20700c280030350141c5001d0140101040711254a0f00e1030200f134a0050f1b5800d80d84101310700049030034500c1500c1200d0040b042c600180c00e5071f548007c0c00d03094284003802480d0400c441c03008da050a0816070200758500d80e0030f5a5515026504d4907104074900847c3c90a040007d40ac0503d000324000c02c1044421b800543c800c0b071090000d00c03420b4005030301542c00d40020341c144c04005154100e00d136040d0310551084901c0d8546031125100c40e4440310072801000001041c036031051444500e0302c6248110041600c4004164418020f075080c0858189d0304040b008440d5034084179440680c80038280a51402e410307010000300051040b0340001081a02580b18000c180500e220000003010f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 54172944 1250 54171694 54171727
    0xe09070e0109050a090f050f09060f04051f02031501020105100311030f060f0a05070e0d020d050c060a021006080c06070f03020a02031501051002061b090a03020d0c1e030804030602 79
    0x20700e0000c0c0b80c0c4c1302850f51200f40c82c0103450400146540c16180000240b010200c5002c454054046400180741c10380d600c40315006c1e58070000d0401d60b800d12070308020b900d0010004c4020102101007505c00742c1c0340c0c10015080042480c114aa16040d039041900300804601d040070740600b01d81d0082c0a9a403059441c03c0401d082486040e01c869881c01a1010008800e4450305280d0050a1640702081256950402180d6180915102c6a80800c1910b4a40c015240061446142e9800b0384c040e9164200b2940009500390312001c0d0b1100136820100b8800d070060900d202d04801080b081003d00250281400010480d10403654018500d15000d013010341498402c04c0910f8079954050102c0c1e9401d1075030000860015401d11516204100a418100b0000e101045890060b070f840e40d42c49c0038410131010764642a4005103102c503002690f4080020140ea12080c0e00421039000300c4032000c54904100103600580c5041c0801c65018031000806c00008031884211012240c12150040e12190400c4503000f84 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 54174194 1250 54172944 54172949
    0x11041d060403050901140f03061302160b07110309030c0111070317040f05010c020d0210140d141605090411160b010f06110601050f0d020a06050c0d0e09070e0109 71
    0x100d1264200300010560018028401d414003600c81192a06d664000d280a07482040303100c5889480900c0403d616003001e0042d8a80c041e001c43d005820410001c01603c0c1e144145001540c000c084101440801030300030310001501504180a54a07142261010903920740c1030001980c10000900f0810b00c200c2800e12120000d560307c00c800b4000c10034009e0503081e80360410b00520391103a4090708000f130079600480303c82c00c1c0681d0140101540038216001c011450400400d00c03c1132102084180c0c1b09205103000506d040101140000f41c007220600c010040084010b11031070101c2004420031103416044400c0e203100e00001c40b030103c0c890a0030071000045014004001d004444504071150802c001e00c1e40c164140c80c02402c8081c0426901c00044504a0103900c4041150708481c00610103820150010146880c024040002244050340820410718059100f480010000310780c2981d2018148240c085e2103000e80b41103007000c0c3d2180c00080307808901800f800184070380074040c151540d02400ca002c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 54175444 1250 54174194 54174251
    0x30c11030f0f01050115031b11100207061409012f0f0307030c1106150f12060c0301030b07050304020a06030510050301020408070504140112020d0519140c01020a1104 73
    0x5044400c0c40c0b03824007030f14007030081c82400181c0748410280207201c0c0c0b1690142610703030a03450898010f03400c01620320807100c03160b040712030048404a01d07400b12580003c0001f0b5204260018040c0081130110341440000b8182c940240d0614545400d61b4030f4a2644a000301380203089400c0740c002c221145000c030302c03030b1a21041d5019004020054500d8140e0b010030b6a4165a0712100d00c45425200115151034045030f041001883d4042c3d80301c2c00e4101a4901c16001501801c80b001411059018602e000c1c404c0b5a94054030b50004018410004810b40c09a04032140707080050560801d5800034803840024040c00e81055039910000c0c2601d5481e00300e0900808028008540d100d499100381a1031b00d000b4011103010341c6c00c00d00e141d4481c0c21404070741e904a484107204181070308020ba007000f80e1000ca800c000d031158031402d01c0c044005d0030b038506405001032107000203040c05107038001c04070300f000d104580f50740c1035410405046000c03540e00038030b4403010740341150000b804154810000e241ca014039070582d81c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 54176694 1250 54175444 54175453
    0x80a0605030604030e040507140f0c010b030304090615030207031b05160b18010c0807060506010504090513060c080f010e07020f0604061a060a0e060307050c1b01030b030703030c11030f 81
    0x10516030030851185c2c0181080e00d06020a0351828030039940003000f180450001981002400341a46401d030182c6070010300d860020601c0e000034000a480c640154102121007580c990003045500c01038000002400040d0800354200000c645010700316a0049000d290050359581000003040010f114024141d42c00100c15091a512545140519002071800c01c03141e4200120001d5107600a1907811305003a407080526142c07118603524034000d4030024080d641030250134003010a001289000d86403040c0343e2145136051084040c2410401d6503c1c50754010240f0a0300300901c03c2e610f0000641505603402d16040803100d07104c184e0224a00a0148402005405a5800d001c10400030380c019910b1109e22070700c0c00318202030308d004116107442000c2c0c801c1c0120703009a0703800d009414041c0107540e0015041c10b0071030400c0742420320241404a940503640c0c076140035210003011507030148621101d1410079001012101d041d41ea020f00018800c0601a10b884803503c0818100d0b175080004c6a222244081501c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 54177944 1250 54176694 54176701
    0x40f080d05040201080a0e060415200a140304020f0405071e0e0a0f080303040605090109020a120b010605040b040b2a062d13030201060911040e010b03040f03080a06050306 75
    0x3000100000e881c2203000903000804103000585902894100703020300c00103040981c942c3c0c1d880620750244c0382039110146440742c42800d00001d001344040780501204454641d10101c0d10001400d803c0213000360082607405200740005a01c0c1d0302d0455240000a440008a645492009480c0e000044002c02c1d0bc500c01c00d41e1900b156a03000d4003000e01514103848901c03209131074007449a0560300d64094071034650700500c0080c01203403154203c50741081404000050810179600404c0324070070143c0041d948030080710111001c001e01000d400d80106410f1501c2c0742081d060201d0031605100350320074008480d8005c21800f0044090610f10b941074099044408901c0420301c0e00c2a0b1654411115943c0040d280d0400d440c42030794026034a002403464aa100410b40e50300d0000b001d80c001c405c07a040e011990307a82c0000c220004944125180d20300032007507540e125894400709002e00315050b0010700c001c040500c00e0100062103010440b01c5a6414189545030b599200f01035070083c40e499011030f91510814090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 54179194 1250 54177944 54177967
    0x503070603060905010905040302030307180503070905091c02190507050a0801060302090714071707050d0201021306020109020d02090408070807150f2901020102040e0c0919120308040f08 82
    0x803800f1030b101ca1105000a03a81d44140c0d00440c3c100721809005600b081002a02c00c0307100c1c2101301030b070200f40d4410380c54080c0c460001c40d260031484c1d0000b4a456a0707803003d114020004120800400c01e040c1c0880ba00040100c1c0c00a46403004289003402c40e08500741c2c00c1041040c00e125600107020090a01c160044c0c0d0b410001e4040c18652200340e0141c0d008070040f4282178030460561401048200c401c40c500341c041d0b5144000380b07000b0702c20707404482d01c18000400001d1062295122201c180d50001d80c8400b50b958502c03003014070303981c8203000307680c944800200162980c21048084940481c1c0b000b50300c0c0c0d03c5050400451182e440b006105103000140e2070208080940c1c2c41260b280d4041040010380e5040d600c00003200e1490f008041c0303503014240a005400304245010681003418030016080a035260030380c810003503007034800c031200d95070224010506040000c50310038aa112410300301b14451603d107903614007080418001d02006051400682880454645600700e82e50101b80c41ea034a05203588c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 54180444 1250 54179194 54179201
    0x803031303030b01080f160504030516090c02070617060f03150907090b0f09090c03100902090609071b0204022b1d1b03010b03070608090105090318040c090503070603 73
    0xd007100420724001d0000540d5100d400c0c00d81c461101c01c451958141c13601080001544d416400c0c00003000000c11002c0001079045c010780034040464030901d4221401d0051502c15190305011030000c43d0f111140400106900050114000700e000c0c140d40c0d2181c48000100d00a003a182800c0c9415100392151a070503620070304240da1140d5036040030750305140c1c0c07103a600e01c041e550020540399010300094100c0d1814948a4049500300c0c14007401c4a121602120110b8101120003080c80d4215545040740c90a6061030008194400004c40f40c0c442286008500a04280c4be00600e40e90070700d41c903107405411501d45504844040708140880c5c0f50300d11029118a100c042a80700d500c02e12410103000c0040c1d401540b0745400c00a0200001e00107054202401401840c036125200364190348541c40061651030601140b0b01a0416540319046890900741181c01e440000c2c0c07140c0300ca9401044021110300c2e019407500807103e0100d40100301c1071810041110070241940080d58103024010000804642613030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 54181694 1250 54180444 54180481
    0x6040b0408060106020a020f1201201209030906042306040e0711010902090601181d040201020609060402010c030f0513080c040c0801080c010513090c050d060e06130e0304080303 78
    0x1d003228a1aa25507000300d889103000c941c000d40184140d60010800c0c60042503c001a00e41d40700009189038075508103c2d08030412580800c4810000580645000e0001d01c1240d0300240e090000c51410280b200440d0052080f44100001c3c0c1a48080b2116141c44444520b2610305004000b0f6071510749070f100c07580d6501d00c20f541d61400710702c1104000c100f2507410701038500500d400a1400e60203a07101c10041d14035641d0840710000b40c080d1008042821400402045070030800103800301d13041d00d814400a85041c0d0b01400384040c81e031140c420000141e80c001505454182d06241002d0141c030500710580c0c1c00c1c09203040702c0810a89212021505280c0004c2d0030f200c0c01001c9400b8481c0e190b22038001d1720300900c01e00801d20741d50081004d0355915405240102200964401c2d5480c44075580d44000084440c2440721f40c00045002a082c4459206401904040c0c20301c540c101c5400c0c10490b000445d02c0303010700d00c44036250391a8006540802c81c14029035000300300840c2900e69a1516200e070041001281 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 54182944 1250 54181694 54181709
    0xb0709050405130c03030e0a0803041403070b07080702040207020d05060403020a0b0c13050d0206120103060b0a14030606040b0a120b0f0a060e01060c021309060506090705162006040b04 81
    0x382c001a1500090341c20380d010941c10900c42c0d04480d080d9142190f45860008403190001da400134009401041040203000070410030500028004100d010107042000641c08000c5030142403181802140600d030841c2c06442d4121001641d5030010b2021500d03150300b40e040030b00b550003a8010001855004104654200e01c185000c0045686055000d50705011b501207050140881500912283c01c2850519140600090006040c58202c10320100150002d0b00b048803d02d4444600890740c2c140619010060440301300302c180b0069007100485da5801c030007403100f48a41e840b041e400f901525080030f00b84c080d00d0344068005c18004a424510440003058981041d6511390b4070025196424610900c41a201c58400a588907440d02108848031351a56a041c5e9201c1c0201d510304918414500c1a05421481f920020442d0305c2c1040822003082c070300401e20b00900c481000342105648941d003001c0ba10399442a02e100600c91003580721245060b002080c903420400020b00411003140310b0015100300d0b00314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 54184194 1250 54182944 54182951
    0xa0207060e0d090302010e060405120708071a12040303060b030c0a020c04020c0703080d020c060f0105040c02010504080904020711040f050f0702071208030a02090901030602090a120209040b130b07090504 89
    0x2a0000c0e40d40c801d0440e50000103d500b90103100540c070488861309082e100400c520b08103a15000000c1c1139000e203080051107503100d018104100441840010024004210b41000d002401040400710303119922501d0500b44201e400501058003c2d03020303d000d4034403402c13220307141c3c94001c0001410360b002d5442480940b04031002c4d240e0750326090017150440d00700e40001d41001499541c40c0003d5400202210600a4003032040701010f0300108041886030080d0343c0c1038220b9525010602c81200c6110540c1d03021a4180805c1201051007501242d68a0105880051b80c0d4061421309600d149030601c1d40700d80c4581000e001120003055600f00718000c000c41c0403c3c0382141c47d00300060382c2c0c0c2e104a00c640d0610100201503503000c94403c8001e15800b15102c500546450002c1c0c002920480090700112001540410b12035864103002c00701d4000761a04100ca0361180280da0002444401c3c014001400b41c030707c0000051070003000100e21501d10744c0c0504038078140e0170154405031084000740910b42c007039441c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 54185444 1250 54184194 54184211
    0x6203301050d0b07110d031b02030712181703030402040e0706121515020a1202120306060f130608010302030d1409040b03010e030d09060b1207060302070501140a020706 74
    0x64080114100d03400103190300c6803002c0c1c0ba075642d204140c008000301e091061901e88401d02072070920140e00c0c0500640c0c1e0008181401c426421140d40408a00008561092201038009858035041c441e04214a0400602500ca240103055112413290001d0704418103000c2c5000d00d100c0000003850041d4400c80382807000548050213140d5070354040c4035850014003040d103c0207445005030700094014506a1030711580c1c60f100d11900c0401409651083c0069115071518414014090303007450310020144003529440d84102500c880310301002c4c1c98644180d00005095015401010845d007a911102d8135480284d035803410081c5c1410024803060780240208000705960718858007503403a030b0303500150b07025003860b0140301404002c100b5200540d8141d075a90103007540c0c43c1e100b00b01800c0d00000d1400c000c6518032451a140080c0e034190030a050164840030502281c41c44042010781c262025483c3c0162280c0ca13504004d80586541808140100780301414009103466a40080010318000c0070184606e69 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 54186694 1250 54185444 54185533
    0x703050c031c0212180d14010f0b0d030509060c07170c010c030f050304111c030e0a120b09100603201005031506040e090304060801061403010620 64
    0x1042d0400c01801a0040544009a40a050041c083c00c4000448080c41620a4004600f030801109415640c0b00c11000309015000400d00412055480003801032003000d0070100803903411040f1040080603c5000305040049456010940b08110102c100319854181d4230403049054034050300141c94580604082080954041c0051400066041d511801c40f00c0707002c101114203400c041c100302d8003901e103400402c1070b568072841d01405c440400340b8062001c0d40b09140107014458281005409140340d0f0000b000006e9424225601690304040c1c40000381d5684540c490410408000c4000c1451401c0d00c00300c04c0c401c40045501c1189040c04640d040490620300300821131441041080c0068000c10016001c0c1602d401c241102241c0904404d06054407200c0b060181c0320100c4045010303074004202048003d5009466500508180c1095045118080c4010b8514401400f0305001c1c8041c182440180f0104650482c60911544040c4e50301c41c220507100703c0202090246a024801091b444032840c2e0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 54187944 1250 54186694 54186733
    0x911010f050f0f0d090203010507030606030f0506030c0f0d050d02160b0c0c120a15021806040602061501110d0906030608161205070f0f300318080703050c03 69
    0x1c00b52403140c68100346019003814a030354070003105080c10a844c1d010301001603c00340506400b54406407000702c1c14508100c6c3c01000c40711284081020f50b400d20b401e01402d6180171807241d4141c003055403020314514010300031481000203444018010301c600d05140f01200d5000c50400c070318004407011080c0413a070700c1c0b003e03000754051981c8aa015800826010055183c1f101c1d03006003441c56603041d03c107038459540341d00002c4d100741e0220f02045500010f241c50169160034024202e0101143c0340ca04150509a00941d0b5520061640b840c803001c00350203141340d0303014a070742c9440b4050740c10440d00080c4c82c0007002042d18441c0d11942d40402d040041c0881c000343d000c200100d500382c0354200101403518044141100b8103804030b00382c03201d0089034408907038490381c900a030001d460003c2c14100b49500c5c040310910129a1108d40d0440c0315807000d56002c0d440080301e400c100d446c6e094503003044c1070a291481c0500900ea0307944036440c81d110300300d000001c10401054006404000300d040c3e0300307405685110321b4400f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 54189194 1250 54187944 54187957
    0x5030406020c0d051c1101020a0305060f0108010e0f060a03063b0a02012105010303050c0c090103030e09070e03030a030e0c03030a02070b030a0f090309140f03120a02030705010911010f05 82
    0xd4020400040f030703100c1e4540603903004017030a183c54640486803c0718982240d000300400300000c0d4944040041a013001c0510b00c04c1000d0138a0007038060341c9044804400300b44003801107506000744101003041540c1d42c51000c009580c10481c100483c03a0569918410008800c1101648200d2000d40c48501e503c94007001100301000e10143c0301c88240b59004441015141445c4103c40005000380041000c503441864042d510079150990340740c4e03000841ca440c01a0120001e44522400c03401803001951000b0041c050a00039a95140346441e28603054400e003004201d1990140301c0400e603246666896001151041d5510050303da0307490400060644911642030100003587c4400341c20014250100011684900c2d101000100206000d0384000bd946003040250001850a1400d0020313299183c5500c5e818171702101d4444040703011001081d26021003140804640b072011030382503681070083c8122900980d010000b0401074411b0f1a0400e420440c8400c9079000900f1110b109075850700400c1122903 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 54190444 1250 54189194 54189203
    0x150c0203092b050a14030a020d050901050c06070e041a0612060111070602010507091e03060b0f120f19030503040f020609120606040b060406050415050708030405030406020c0d 77
    0x1409030080706202c2d0075a05019014030a1800c003031000d00d5401006040758000384550080e100c8000d4500f01050b1103404050b03980a25001080b064050540001c6d190460080714201140c4507401d4600584290041c40b45001c003900608007041748140c0d100c241c41c01082022103040200441c041d20a11842c6131a1240e16001103042101440f050318a03115a5403281c014988168140c043c800c1070b9050445c0c0e940810b01517074548042c0304000d604a0111000791599060440715041a800b041e102106d681c840a0320f241ea03500d40c4401c81d5183d000c0704000403980501603009400085003ca0b65600d086002e46601e40200c0b60207001684038542061880382e0555200350950701e0ba5112988000402c8808907400f00341005185440e4880c0303440000300d03e0a1201405092802c541032100f6601040c0b00342e88180070070441030210a13008000c2e035080d01c509442000101072085403d41b001d01c240c00016001000210070882002000001841914415400e923556003d00303c06004884400050041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 54191694 1250 54190444 54190447
    0x2070206030a05061c0f1208070503060411090402040b040815040c09050a09020d0303020304020a0608060d0b090703050703142b03020904110301060f02070b0a0206070507080706020a0309150c0203 86
    0xb4407400158201076081300005040c1066180d4054494200c0d581504003262114100c0b15140180203110803190884c010305d003050f44641c030346881d00804134440205040e125654500030013585d20700e01426074072801d6010304110b40e82c540341d0f2481600c2e07030800c0c482d9086910a6200f07081d07401c2196099203005961113084004a20701b0079070808082c04c001445120842d5035007201101580c2c88080a00740d450007a1001a80d0781014014080c07894a10307004001402105000e0020719240c0003102c6404580095000500d91180e9518600309409540040c018bc07140100c040180804c0051800381d6401c4602224452450b1310171010000741d00b15500282e081c60b82da4003a000d180240c000b003515000091000491244201494481c0d4200f81c002400140070300c4c10804110b501089104041c041454130141000c1218100035501c000060451003004000b081d01e10801141d0030650f45e41960004083d500d801034070000900421a11505440e0b6102c5a51104080100d074810001e40401d10390165 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 54192944 1250 54191694 54191701
    0x70c0c090624050d02040e010509100e0c0c0123010806070305040c091a09010e010501020d020606060304020f010c050a03020d0f050703020a17040306060b070218280908160302010f0207020603 84
    0x1902c0c5060000c8103401403110400228004d04800d20040c0f025200c10030240a0175418501131002c000c100400c013000840402e5400e00042d103e1448155004002d4000c031541e0300745848040303014210a1401401030807480c43c8080240700202c801505031900b0740202c514603500d07028100c0980c0c0c0e05407405000700000040a01c00d00d80c41c0d80154000701a410f4142188a0316180441c9405909900c117080f03500d03184006111319a410b0150095408103480100a607003004000501d8600c00075000921605102c5558401a4014905054171076081000c0e140341b20308604003e5200d202850702640001c04600c191007a1501490076070b00c6094041d4010494501c1d40e035103000304160340640d213080b580c0050000000242050003060058076a07066116210a0301e4410311041c680f21407c11005012281c0412001040b07115030705c0003070046643c00121070490f00c42508021320307101d100500303a00d60014121a4040a84166140407482a40204008903e035080d01c0c00b01d02034000d00035807014080010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 54194194 1250 54192944 54192989
    0x5040311150a020f160f050606010207050609060c0c030a03020307030e0901030f0303111902010b0f090c030403121d010c080901110d02070c050904030f03050c121f0905070c0c0906 79
    0x390140001c072800131880c1c20b06212003900318545a180c00c54140d40c0d052820341c01c0003414840b0740c2e0401002c6c0000c00c15141807000040350350003240c0025005500100d1a208181f10400000416410184c00d80b1106112070400a4032517209040c2580454410f1007440414188901514100d0b1340003407488090558540d030490141000e03240b4527540c1c103000d01c051540c0c0c1003400101d80309818260000206c0c1031940e42481f00070040901110b00c10b01001c42040742c00540d03042141d6100d6814606403050b2054030441c00b0040c94403450b5425098005865003013075240c151b218504449041d104c2103c5640c40c014220b01b80c1d0381c8010746880140061240c6640011550041d0400611442c2516603554540f000324045200c101c6065000601500603565010b4241c45942c2e081607194841d50b107400e8942408414416000c1d1001247d99080c1d844001070307514032020304020309a0450244442d0500d2080204071111b480f009807040d00000380006244282c61013804102d41c60010100345481d2842038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 54195444 1250 54194194 54194197
    0x109030809060c120a1d0a080a080d061a0307030b030a02012a0503030a021c02070f150f0504030503180f06040206030c0705010203100609090209010215060307030b0a05040311150a02 80
    0xc4802c403841364141802d59001030350302601c480d40559613605031040c1c070030a00b8001c01007440da415000d010311060030b1210a0300030449100321500559280d56507076900d40c41c08014a0361364040604410000902042d440d907040095009540b681e400f402000301003c1050b0b107d00030208000d010446042c8448240444089138400080902410340c00400307541e00d03880e0840c0d00c2241d180c0a0b1aa00040b50100407003251340c203c0030300c40d08017801c42c204480c0c1c1d921800100c411040240071095495030001110b4029000500e0204403484140710b030303040a1402034010b4005594001d194035a2541e00c001e0002d0001d1040c035100401030080a19032529020f200f540d610241c11a403006108122600c003142090000714045c0b40e60040005800e480c20100030903408880c0c1140701ca2900411040803240e80c0002c420741340480340740051a4030b4445d035000a00c1c0140c070764002408a6404000c00c41e02c510b40d94401c61040e800381d1100c1222810840c0712030344419440038001030f62a070383c00118019185950 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 54196694 1250 54195444 54195457
    0xd0c020313050f03150a0207050609030f040b09130906050621030403021302070f0b010305070f06050307080a18060618050c0a08130b1303030f0b13020d061203110c010903080906 78
    0x1420b8034038003001250300540c1744a003101d480821076000100c000421508215040d032008024002e5414109050580c1816102d1071041000000700459800300d07541d03c0109450011020800400c1454040c0c900440074043c102c0300c1d00c0c410240d04ad000c500708141c120106c4500300021024502d00b600315801c0240000c00d040c078070180c06a09022003400a0010b14a000105002d000d01c6136556142d45050b501d8144950064000344200c040204000382c2c10800740c80c1c0019042c1440c04803a9605585c10b0001c1400151584083c0c203142500410301c002c41d802402500d40711440c1600280d1511249c400b0b80300151002e03181742008000211005114210241e0030007640000d034000c04002c1e44485207038101c240d606500181c61048603508154045c402d0542c405c10319203003481a0744a0030700061010a04540800445400203411603001c0e00301e60100000d0201c0107100b12a48800c0e08000340f14082c3c685045207244148408991198041d00c0200112940928032514180003481071202c40d40001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 54197944 1250 54196694 54196699
    0x310030303230f04050d02010b0a0e04020f09010609080709020901020c01081803070308070e090702060606071406012907020901091107150b0307090501030b0402010c1a0901020d0c020313050f 84
    0x1103201401441c001480e040c050007541c04601e03c80d0400f420900c0c00e2450840e02042568544500d0200d552245400c103004c55003030104008c0c1690b55400071441009000300ca69500c50b00d8880080b03075041e0400400c034244c0d440e01c01141c071069243e502410072841400700070340c056448255440d51540c401d454941e40610b07038100d0340c0c4220348100d62043c13943c0c12400044012809000c1000480c0780c0c0004c0091102c00111030790191400c201c1e1002c1c0d212031000e85414002d120018081c4144041c0c0c441410305196002d0459106681d0b40030001c440907030702c1c184400c045100304000f03524481c003d400e4035071540d0000c022050340e074a001114402003100307074619029110144007520100b0582c4280d00a01c9075000030101d416200c06040500307001d86604121803007850440144082080214a1039002c0e5080c00c0070a9180c2c86800e05000400600c07020f01c030541c0060b82000043d08040d000b0341a084410034040c000c1c40030b201d1080ea01d80c0541030101c5000c28404104000500d404402845041c002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 54199194 1250 54197944 54197981
    0x1509100b1903060203010303030c030203042d0506240a060f0c02010e191a0c0703060c09030203060702030c01050106050f090114090303120105030c01110303070c020301060e0721020310030303 84
    0x485090415840266005643e42a0b002c03004006141c0c0502070109203480501d4110719514045e50307550088260b81c0c42c1d01c0041041030306206500e0009000c00d03c941e503001000c0368034500d0136100c0300b0f104220303400c01201001010074034400c2071704050120f901510960748451254141c1a002214840345044040c0e040000c03c0b54440d0380e0b9260051107090208040042c050103e007008030105181012052a0084076402c102046480310b000c18041c081d00d0303100301b010580701c422200c200e070341d00c0f42600040e6040c0144014410660740000043c040075421400074455684c0e01c03e002d490074040c8201c407400c200c07005c00103100d80390300c070300d481c1070b00c10034010b04050510000001003072854001c1c60404851000803070061160340340400c5000b58019091801008182809408076203a01010f804c00f414003041084031802c540c1d0a40180c3d000c2d19081c040c40e450751500f510010601c1480520103d41383d8991016003030018401e0089a1155802401e84541c1501c0c5941c120b00034805c5031404400c1009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 54200444 1250 54199194 54199219
    0x81009050c04120317070509010c020108130b0705040e061009051011070803040815010b120a0e0303070507060c110601050d080f0a0203040e07181809060e030c1509100b 74
    0x10700c0118443c2c401d000b5920026100c0540c0080c545540c0f01503c08400d00c1001c0c0000c0540d40e9021401020050342880c0c03c0300d0688804540c01ca11495051b4014441d40304031381000036460744100984225140300c0460f0708035448900c1445500360b440c3c001c00c000039642c00c80c140418205040c09100d40011441d01c001a00c180441c22810207000d6040143d080d040000c08011560003082002c0c03801800c03460503007403549000300e100d903548075029009440f282000c0024440c044242d12032100320764080140ca41d40d18103e01c000b000c66200c050210b0b45e0520f0070191481a81c822010021140c0e003002c01050240d08141c10001c00900f0485c08031400d60b010000c0d05950155440503100902e40703600210b8845080803d0403c0816004003040c003000703020195031010752112542441200c0e0f039010400c281c24462075803800a400802000740c103403420030040d1001010000000c01e854800d010550f0242c1d010480d005010303d40076641200b184d8010180b0310240415a44001c1c1c4401c07004045040c80701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 54201694 1250 54200444 54200459
    0x70c051e0a061d060c190302030708070506040201110313090509010b0a1401080f090703111528021b040c0e0d0302030d05060406120321090605060a0501081009050c04 73
    0x40c000d4029400050714181072001c0c80c0c0c1582002003c40c0c2040703a1540c1010a0920348a944101d00000407400d1060025900305050007441140d1046800040640d550f21040c2003450b0382e0a000c0d64100d0000e44540781103034050202000765803046002e0310a082807540b800b10710380050306010b8a0581c95550358054101c2940e240034041000300b002e2041540606400c00014118000080c00030404803596402c010482d48082031280949900400f04601300075001d021036a60440d01644803000980001c80c030345400308140d00c42482c821108460310b4606e940d47e03000c0f03071142d0380c010300400c100485400032134a51410f9009280c0e44522403400142180d01140000e44083c9d00e69000d0f009a0400a14031304c1183c00c3c0d000b4158440c1069400348603c602d0407840f002171a1a0081c081c08100e0445d651101c181c1942d4840342030b50000e0f05003404982d03070720308042c0010705094070260b104855a50780080c85500a81c2c40d280308080c00c1c0b040e4410540ba011507e400790a0081c0b104081c50010403022a40c074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 54202944 1250 54201694 54201709
    0x3011503270c0504020d0b030f03040f12060f060803191416082506061208090405070306180605011d01050313050307060c0f020607090506190323060a0b070c051e 71
    0x110804100420303400e480303009250410f00b08035000c41d910740041005000124400c1c00c1338040341c1030391031030203c80400c40c01c05000801d45038560521440c108500069141d00010181060503100822407420b150b034003509842400700080c000c40810014821134101c2e0a101c0c01a05126001d0700180f0320300312000d82d0350b0080c4004600c164039021105e1226000b07002041c443d0070041c0011154505154500340c0707e5250b075001d4114544d21803504c03080090b2a00b4401d070451002020102c0703014000d8480003180801034a00c41c02001c0c0003900c03010050aa4030f80d01100b114070b10106840e15840c1d9111030f10b000010707681501c0166643c0c40104400400a400d41c8201480070002e03696003143e1407078188000b800d0440141a0350100038490a091100707603120811107101c49001c4c107041c00c40e0f05203c0c20540140ca540565040c0c1828002c1c0075041450118040500c00c250031551005000d0721403440c4041c038002d40c0e5000e0004010408207200600740840d00c40020f070b03c4090031446903d160000580c49 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 54204194 1250 54202944 54202957
    0x90501030b0d14460212072702030f0a0e120f03040213020a080601080702072409060813110d0204020d06090c0e0f0f010e060a0503011503270c050402 66
    0x40c0c3c0325400113550030080c40d107603030074003102001a50340444103072084800303140c440d01c00b0229507086142007004550f165180b00051a4525081e51a1142d407403005001d1069205051803c40020f201c1b041a899814401c491248000041100c8517489070015031004240000640016108400012941c0d52022001e42041e062564155075a440c0501c14412444107040c0301014a900600c90303e42e5494210800550040083c6032141c031503520303c03038100e191103107540c00544801030480d00059079890460880080703480039284d42064603a5204112022401250a90803000c034880321040004c40c01160050610390042440160f8090303600002c0c04c80c1d0080300390a00f0156226000c00c5000c425000741506520b0384c1c180102c140c003048000c83c124600c190b40091151203900d1030600305a018440c5484081c8000c1e041ca41c40d0070010001a1666200380141403610441140c40c0c01064030a0251149070b440b42c400c00c034030000c081040c4055910b075003201202c002504070382c00b1500ea203407440070b03116 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 54205444 1250 54204194 54204233
    0xf060303121306060501080606070f051e16060801080d03020a2f010501050f010e060d06030816030e0901121103010e16050406230105030c0702030118150903090501030b0d 75
    0xb122401c6180c0300044405075070003d130520910100700503242d964402a1a8a1504001002c413000c407a450031504010071700420810290304020800807602d0001007002000d107180e408003070040c0d150303c42950224000d10030840c1c02e0b84600c0c0b1001100d8402d03005407041001c00d04041001c000303100031440350004903d0b1a5000c80005401c0850040c130240a8580145400d03280300c0018a1402d0000388204654001d00d809000c0010311a90788040c1540004021034008000d59250020910f101c1054008007070280c0c00550709203d44445460f003441070070704946400000715000e0b01c1c940e54080300200041d00c036692656a0f292482c0310110700340828019110300d88019035096003001c08210803640c4903005400005244030071902000e0a10b200c0081400090070226140d03903e040c0150a20b00c500040250594280300756543c0010074010000700280c45802c0007441c4103103035a06034080300c00380c407006030015141600801c900d5010398442403419601508100d02a07c01c0c1d00c03480100800e4108802 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 54206694 1250 54205444 54205471
    0x30d050c030601080f06150a09030804090209030607050909040605071b0503030a0f1a0603040503070c0e0709091803080603070b030c04051005040320120607031d0a02090f06030312 79
    0x42d0307980c3c4441c1c82c951001d80c1e8001c00d20203050540c085a14406408080c4900c0366000507002c0689000710314082c0190340c000380051703840f501c50490340e001c3c0d040880780074000c2c49204017240c104d90051041d40c0c90280c0182440040c0e54031901e4050141ca00508117500384900301c4128401c6c4a1081140a9440d0240c00250f80c1c0313040a0010030102c49004500f4021940390518425980246c5071800d200032004480c825105e45860821505510401b100101074001d540c5001a04400e5924424882c0300703613441e42003440b42e54003000d006443c001506540c400321401c420100107401080019000500a01142d0762541c590050300c01d1030f4800e4551014569000c030307003080145041c2c01510030348441440c1c018142403859075030300c41d0359800c4100800300020300d40c01c103525501c4152040c41c62140b02022220907042007600540104031020301075042030020b03610345021000008414503020f5000e001040103554018401011200140415500d80010060080ca10181c40b110301c0c02141ca800055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 54207944 1250 54206694 54206701
    0xf1003151a0409020318030c010e01050609070c0b09072102030609030705030d1a0d06020d1a0a0513020708071a01060207180c0e0a0b040e0a05010305031605030d050c03 74
    0x94480306031507403084000c1d000e0714000008a0200d8001d4504650b80e00c5009070310303600d80c0740440c248103001c1010000a48004101d0207184501500036403800102d00000f040b4076221803007401100c0b181101e83d080842c401085100010340046602c0394004100400e40e00001c0c1c8440c02900f407004030460260b4071f8182d860421007540750030b02c00990841880380040d480c055041c1e8850b40c0301d000b80201994035541e10b14605054201d606403203e400200109004011281c0c2d2500400035001401e0550312103180c030020010703800030034420801d24a0300420b0306ea103251402040100400501098813503164080c07081d04c00080c80d0703002402040d4031520302580392101208007a1468201644510110f601031a8100081c0c9800f44003a00c5803107409601040501c0c1c0e02c6410f0312481e40c001c0c039081d005480101d00041d6110840c02a00564200c80110105611492040c0e025030b0008c5c04082c082d07401c100081d003a0305011005440006205805a0b0308159400001504480c002c9550141c406d0f000400c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 54209194 1250 54207944 54207971
    0x60c060506040203041a07020c090a020d050714180301020d020711131b0c030e090403021e0a05030d02090a0e01030f06050a0e07061404090e0708010b010206070206150f1003 76
    0x1020760016081d1403c5066151a488003400724810394400701840e0651008035101c40d20910115880c044003410750003d6040c105e65040c029800220000380c003616042c0800c1c0017522031a4a001c042c06807001130ba0401d405000c650150929660180f0342c50f65082080c6c40d804040e82c000351070100e0040c0c082c0115864410180112000c4883c8140911890080d0541c05144030804100441130140b4000e01040f485150070707240c1100100300e00d544413101d6000c0100b0560300143d160b116404000c142c401ca8140038401e203070780e410786100040141d0000d028040241140b68040c241800006203c111515990311692140070f0007a00140c0c2d2031521031101106002107805900e070020659107003000052000075402d81c842c25107003c5c900400c858035000d0314584101c1c00c207681c0648241c500412843c881481816920041441040815404e100d4034841c43e60010a04174884d4240303130040c10440e51b8031000074031070b8054120307d0381c0d0041045603812095108c1c042940412075286d2800910704540403074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 54210444 1250 54209194 54209201
    0x120a020301050c0a05030103150b031606021c08011809020a0305010203060108071b0f020f03011802030f06040b0106051614150109060b071118090d030c0206070c03050d090b01060c06 80
    0x6043d0820300c10011004220390040c2224112900200c001d0030200c0105403c5010341078480700c00e13525101e40509003100c1807280e158907044440c96001c40f00d84e03a5000100040f1040303610041400f04540d0303001002091b01008084034484124000080c8502103907000a400e17a400b5001911940e60210401903030f035800c406883e4101007d420403034028840f9044103224010110001013544c0c0403030304940115100e40c610700484c0c94008009000e25a804503503400c4541810030180d21a02c64000c8a410540000c00c1c0f413405a40c120554005603170030001f060f00c3c0c40d4001c40105a20000e007041d1a008940c6040010481806810107081e1885004804283c29041070f08030314040c0c0c1c50a01d04200c041203000854280d80d03808825200081010780004e40c01d40585501400507a000000f000035982020900000744811a1010003418103c01412a41c2d80000c494031030104d4800305030300c00807074021030203040d80c000800404582021640d5820707800300e50a0707200304081480e682420701001268007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 54211694 1250 54210444 54210451
    0x30e0c15030f0c040302150901020a060e030a091d0115051309060503060601023004050405040c050108100e01030308130c0f060e040b0d06110d06030f1101020109030e04020f0405120a02030105 84
    0x1103c1801e05003150000788032089900b007100e05030076002640c80001e900074400000101d8000c00100304030320f81907851503121740c01110502c0020340742e4030001ca02c8080c001001300c1071468a074110700217682004250b1300d1280307845408405120080c409e40000c051010341d140054428001d000c1006460304040c035180101c082e05041c1590000d03c0509562444052115500b04c1030505410101403180c580e600584250b411990708181040100400d101e0606038920864000b030b0b9032000c0c1c2da0b4030010030680f0ad940c1d500407001808603a0740100007107403042c4589074010510462003090780c8402e9a40c5410b10748140e100d240b034107107402c40402c025a040b044007240d03210280ca0038807441c005c0c1e10004443c00c1440d107005100319512040007104c9c2d50340c0c0701540d04003080035108001464603400c02c0725006c0d04507c012540c0d8003085140400035413040c0100307158160325484000c0310021107400c000103504100802015114148000212640c5140c04102000043d601814440d6018010302d4207654004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 54212944 1250 54211694 54211711
    0x3090d08090a030c030302160206040f1401081e04031b030207170111040e09070305060106030605090a020f12041419050d0212030a0209010201020910030218090105030c01030e0c15030f 81
    0x40b09840007003500000f501c80001c2e03045c42c4c0107a481d210752098148541c40c1132000307174204201240116907940c3e01022801035540038540028a4400d1500440e5400380440c1c503466002520500030080d220805411a0828464144040c1d00e1806041000e0003100401d800d0b40180d01c500400c20001122001da00201d07020300d0024001c1e1850640c80f000300b445584240e0700c1d21340703000e0300160107000184994405558003005581103561348110040c054031042c0a40c0f8072508a05020605480d0144201d071200d590a502c400e041c0b910307110102c04a41c000400130365071a044101e804450324070a0041032480c10401040c400200540e040c42403400e0a02c0d04a0b00035540010a80c034500d56900041e01da11880340b40001d030b551445000100d01a01405d00c103a500070000303a00100c00142c05801034250341401c401d0b9101c510540703200700303c1c01d590300707110305c5402da081310340d660130154480e0b0084070043c65200e0444004901001c00326203403205946e05c04600010100c00e0000e181e4803207400c0782d00807245 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 54214194 1250 54212944 54212953
    0x10c080c0c1f0906140d05280c090506090406350604110909161401020c0103060f180b0303040e0601110607020303070c060e0d1808010603080702040203040c090203090d0809 76
    0xb0030b000940090014020700c001d2010106010b40442d07200800c5030902201b0040501c401d082007501c3c07541d090f03051031414070f406021201d0954120801d105804035009207659800e14a032420051020a6002c050446d80181d210074000c02c481d15540800d0030112880e00410030610390710302610b04414402014204190411030500010900b0f001c00003444003030031160042c281c0c441801c0d080c944140851500312040b21710074000351155403140100c1280c1c00c2030f002d8540c5d40d0690401102200d480c0d02400f44a41c25070141403010780084032198143d9420040c00240000e44c282c000791030b40d003140c2d110b65001300001cbd00300027655078060295180000458020011030a2051000c0e4503800010041c0c1c0412a030443e903007081c03010603040224070b1502c100640342c200014100c006e140c40340b840310200c2c0d2141c1c0c0a0380040c0072141440b6102c1166007050b000c07030410180e90300b004003070752000c2c1040d243d2079500c10003c039003207200784001c5000c0c542c0c850080121b00450080034110308401489542581c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 54215444 1250 54214194 54214249
    0x1b082101080a170c07060332070e0402090402130609081501030809060d0c0c060e0d0c020409020f09071211030402030d0c170a0207030b1003031d010c080c0c 69
    0x2000a4a01c0405901c0030980b44514601420f1040b54020520184018800c5d44400584140c05a001030324010000124011629100405101044403201070100800c030900c000351841e84503002203aa992401040580f412040000150681e0032800300d0860408103400100301c0c89400045420081c100c00f40030b0081d54120b48220031403540c0501c800b0f0401200003d030441981d84402c12151400070040d410040c0c041c4842c00140003d81c8408203e9519151541c0300712481d00005580d1860805a0384082601400d5420302c00030b8000620220380020010300306654036520400c456100348010360303540d5040713440580f0400a440505544130021002001440b000d80c4021403500d16030242400d00d42c28104951400c0d041200c0d50545000c0201c201050510005601003120400c4900840420f0f0894a440c7d0701b0003852510f910000b001300d00c070b01032003085260314400361040d244414144182c01c0107043d00e03894502e038040d1111542942015045460620f840f01948003d1060086030b40d801c3c15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 54216694 1250 54215444 54215459
    0x10905060403050904090606080a0b0609060307050f0409061424060702010c0f0822170d080405150408070249050a0302010b0108070e01140a1b082101 66
    0x800c090000b03400c00800144888458030b507a0060002c040e0720010801240b556406111348402c0c0e00c0743c0c1128243c081c1404141189852100c5501178580103001e090210f2510041100c81220075140d40d40054480c003221000c81e9032880760040030844401017010500e401005100103840e0309600d2660044004c01462081e204d00f0259640c075603080c00c144030220914281100380c041e416000902325080000e80c80004035140e902a92810042081c0b000354907100c408002e07481281c01e640ea0101d0307101c130812a1000d0b10441c000d60b00607001c3e100341d51707071120b049404089120f021502030322024800219002142401c07010200511a2906c4800a02c001d2020b43c140c2881e120001c0190703410b500e40e80740d064080446403070251039400030031980d01800c949000b174045c000b03000225010648440c000b0f201580604076170821290143d4920302c0202da003084104198105442240030003030307a410310280b10640c1ca43c01440c028001c4100c0d5071120000c0d545000f800080e64102c220f11138108004002c4807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 54217944 1250 54216694 54216703
    0xb0a06090308121915050f0906060d020906040801050c1e0313171606050105090115020c010503130803090a0507050103060321052a010614030d08090c0a06050903060108010905 77
    0x4200035480b009a64070380c40c00185044413030300003030800c0d81d180c03943c150a001101481c00040351070503120401d41ca0710304401c204e0069001c544442c2c0180c0200005010380c44290b00802107498024881402c2c26180e481050850341e00f00c510184040380001c0444151020301c4060250104511100d403a41c50120b0403c900c016510380300074442a41c402d0340c3c200003100c22060340c00319a0300140c22201c0c3c14407414031348082e020030701c1014080c440c07650010075284689000c401018400e900188802c20b4004011103840c1d00c020107004c04130040804403800241e010f001140107440100044c21201e441d400c20a0802c011540414141880c3c62000c00000d042401c3d9a1040205480711004035211a40141c4a03440340c8214003580c0000403040c0040c071950038101c0d00d0450003000003080307510380300e00741a44189400107071254154172003010310418620505680398041c414000360b890303501c8003002184030b040968000b0004541d01184045040c2002c010260040c01042c00a02c010700e05901c9080c0c0300d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 54219194 1250 54217944 54217957
    0xa090f02090a020d021201031203020a051b0c060403030809010b0909120d11030c0d05010801020f0d020306040b1509030f0a0807080c0708120307030c090308042d06030b0a06090308 79
    0x101e002030001015207040c3d60565800c0760300d03d0415540e8a0144100d500e5403031090200300e4106444200c0086290300c24400c2c0c0f200c091203a241c00303203020404805407131042c1f0184460105440340800085043c2c0b0307050702810086200fa140c030790007814101c90307e03425205481c5076180500c8045007008209900003400d0560140007032100740ea40c903480f0000102a28804540e1840800000240005140b100c0b00411036480c0c02e8404201c9a602c1d05026801d17403240b1329451150721403e02070105011640d500950300314600070000500c0003d02c0000c10180d5610a420f1802104003045070025420144a44da000e0800030014150b09080c81c0e544412500607120040c00300d0780041401643e002080080c04080e10042d400ca0b003411806480c40c0c000c0d40c1c011114400028107160302ca1098500945441040d250301420142c2000d04000c0313980341c1040340350b00e02514804a81c030102d550b03030490220f0901400250746e010540e28040000d0100c10040d55000d103003000b944100c20408910441d090301ca2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 54220444 1250 54219194 54219199
    0x1401050408190c0c080706080907050306061e03010f05011a1c1d100618020306030c102001020a0e0118050118170c01030b0307050102060406020306010c080406030e060a090f02 77
    0x2c204a204542901844200a05614084002146403240054102e04032091a82c40418645da189005074407240307148501e58059100384041a214a009484c400b000003a601108102007424070009096030442480b03c46420354800040c407105400c070b16501206008500d60503d011000002c0c1d156880700300b14a208059900d15280c1c0740c50b00103012800b40811a1001c4401055464880a00601d414070410710702c00061683c1060a82030307802501e100b51002409042c24199410074402c190169404007820002d008a040c04102c0c001c2c5500420800404001078480e205004003400414403154a541882401103040103106114000d100583d00286001e103000302e07003088840c02c1601680c01c030406144241c4202101c0c00c0f1f00164201c03402c20240d80c01c3c0040040403041c1a15820305000e90341c0160001c0b000030380492003d800031a004403040c07500c214090400d450340300305a0455002400007070f445500c001000e0204000f4190040f007001003c00103035080b42e880701d403030103400741c0001d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 54221694 1250 54220444 54220477
    0x603150e12130b03040809030706140304021315090b0906010801030c1a0910080406060515040905090309101e0305010506120405151302030609030f0301210804121401050408 76
    0x1104040700d03400c440b00500f074841d0200d03128281807800354140d07000f00a116011b4481d4100c0000c140b4071403c0242d002c0b5025442d0146161503d409120600c500c00d00003034041030300c078992003d41d62090303140303003004125030300d4001a0752104034200401080098105810403148000600109501031241800c070380700b0100c9070301442e6460704201101d0083c0f4209a6200108050f484401c580202404e44500d2040c442009501d03103d804216030880c1c41e1a586102e0340c0c0030b00013800704c0c81d000d80c00700b5001003070441107a0800b03010324000b0702d5054646026000040103500541e01043e00b00c40101262642810140507540c14200850294080c914103200700c1d80c0e40c007020030148482840340c520745a010400f034107001e1401c0d850300c4d80000f80c80c002c03c90081c814040060041d18003c0b042e02c511000b4540c07014616468558020324030100e034070950404941c5c4040380c0d0001468180140002c1c00c510588248850640c1403404000012060024490f410101001300249140c0119040c08226241a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 54222944 1250 54221694 54221707
    0xf0f0e06060a05180d0609050f06040506060103090302070e0406020415030203150f04140108030307020d050720130905060a0f0903080105190801060b030402030607050a0f0c031e030603150e12 84
    0x100c2404d211445266000141d030203460003030129503000f9030103545c001d00c1200d1007050304004090380c03241d003100d0181c41508000041845588240c005001080c000c1c411902520b0b01d4440c0d902da03424058404031030f01c99002404104880720f0304441c1840c0a101e090071411480c10046c0c00e0b403d0000306403002c1c03240c01e00400e980c54960b1550b0284100440300c040d01080c6607151800c5603034175841a110034000d482400d40c0e10030b07607500c103404803a080d41d406603102c2c82c0000b11600711030b01c0c0003815422070343c006003c5230b1010203a81e00303100d4055042d0081d070040ca82d40c14502c246100726010125800d5420b0b04040d18000030940000e581811140161050a4200d14078980c40c00f0b1407030a6000b80250f5400c0400c00104840d94030045c50060713008800f503031000d0b10780c443c050380ca92040d40c1c0441c0c08290501c1183c80720302e008039140b050690290071b000c0e0560080c4180440c803d00e406058102095540c80c0c20f01c180407105501864102114008010b4035916206c242c0d40e0b051003980901c602c605c0011039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 54224194 1250 54222944 54222967
    0x1009020a03020f1c0e030711041104030209040b01140907081501110102070b01050f010302091c05100501120b010602030301180504050703060e031e030103020a050603100e010f0f0e06060a05 83
    0x40321100d894810f00c541e10303007040726100c003003050b61030300010f4006041142d802c0980401000329401141d115105402e0040001c0074080904040c0003040c1c121081404004096111045003610440c864442d440c210b40c103201c0905101d100080396180035560b01410042c540f900030200300d800c00308034206011000100c800403100c200070a40c280c1703665400491030404000d030b540d1410341644c034200c1c0c10f9803015115000440407400f901600c1039209100000c06082c0b9490152244801d500450645e06400f225005070000e5950a0b1700c00325600005000b440b00380903a81038064098070803440550300c0d5500d007a015150108012004804059031000800c0800c001086040000c580c049401e00c00210b10140c5103450f074001c1780ca0f2280ba01c80c002560510440d480c81240d0580780c0c014007140401d8140f100b030002641009010540072090807202042e810b10b0141d80c01c2c000e00c01100706900c0b041c00c201740030468103610360240c2240c14404003808010369601c01500d880080d2071819503111140c0044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 54225444 1250 54224194 54224197
    0x2040e0a120c0303050a09022b0c0b0301030618020a1412070b090a060f02060c0904021605030c12250201090f090f141509090a0602042301081009020a0302 68
    0xd201e1448040000401900030303815109160103510100207940d25280d68000b6580c559074000c1d40400041901619000c6121504801c1040ca00c12105003058a03503611042c2041c03900072070155140072004104004450103150000b010184140700600e0300307030307010401e95503990040ea042a01000c00e02d40c4d40b502d175800070883d01103821080381d000300ea80d0b074100c1d00d043d0301c620600c0d0301030350403e00e0200304c0c00d01641c40c42c030030a851540105055542c2000400341034102d58400c0d6802502003083e901c2103041003c850000754010383c00b544d901d2661380449807410141542ca02c6114605001031410a40c40040d044107803103606081c3c61201d500d51004072042c41380c80c3c001c40c10140c00e00c140403691b00c225500c0003c01445a0004000324415281c019603503400841e0320311803100f6841c1c081981802c10307400320303034204a00d18100c45440940c0d58400d01680c00940001000d840040390220b6404180d50007d550003500b0b0074a4425418410620507280d09039001e1410355540000307805290038440e50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 54226694 1250 54225444 54225463
    0x302040b010e03010513050c03120a120915141305030714120711010905060403080d09060216060504061401030201090303050307180806061918110f0a050403050106060302040b0702040e 81
    0x3030013042070b85480441d124086d56000c806580500c201201c07008241070000b2429460746511485e0341c00c1a510103030448000d40e080c45442520340d11000e210b0b000404404062410200130000031540c00c030095410b03030b000302c00101404d0000c00b0404001c030204401000711014590004070400614a8840350503141c010380200a1280e6403002a00100344030491501e01c6178500b00b6a14a40529562002c0000901640c040a04205401c106012030344900342d000f81400d901c035207405420030a00030822001050140010740e04540c0302c2d010001040001d2090f0302006024840c11500303035044d600028400c3c601400003c09001000010a0405004981340a01d0b6130320045c5030782e021030725a010940c070703550195482401003992000102071030070201c0e2600c0984046680140041c2c3c0000481009040d0fa8410548060030800c038680300c4902c07600007440303107051a072141030b9610700d13500c0e101d800c640c5181d1004040500c1448240f1010010b1011030f005150101c9000c10f40c01c3d06001e845051540f800d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 54227944 1250 54226694 54226699
    0xf0302060c1e030c0c0102010c170414030307020c0f1203191202030c07050c0d21030e030c0102030601090803030403090302010e0f310e0703240504030903021215010302040b010e 78
    0x400c0342c6110700e8002006001952020703095809640c0603400580c240d072001803040000c980d1102011403503506030308165038418042c0606448204c0078002681c115031083d01c0c158016004201d094510303040118104000c6001582e1096600d070030340c0c18040c4c6070700170405a841d10301603480105500c00d22420301c84800481500302103540c0d0a2041280185900580081700d0074040c401200c0c81c5884c00040c3d039044140c01c900031030100209092107510108040d580300050590340c2d090341003016400c1002e44010015034000503500e00b002000900203100d01c1d80480b4007036004008101c0065803140030041242d13420f0926405010b44040044c4034140c501c4103e40d04260701c80c0d0000d5420500c00131030b0f4910100703440c3c400b2011401d500941d00761800b00700300d000ba41e80082020800a04c9103064091802c1d6001c400c154043c5482c0070708415500f00381c40035400942c5413441881546880601094400383c40703030003030180810120001036401c0c01403002034410f41d51400c07000c030103034028270b615245c80c1c400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 54229194 1250 54227944 54227983
    0x32019051c050a061d01030201050a11010f090209091b0d020a1701050105090c0403050c120708060709030c0603180201030b0303090a17011d030d150f0905070311040f0302060c 77
    0x1c061041c0020482241d032580c01d07504188000a00800310114460007030141220310011307a0940d0019181907200320010707020804000d06c2ca102c1e5000a00c51820a40022100462094110700411009100150200030190444000490a4400340c140002c00c92419120032803070420600025880741c132190703c4100c411408041c2403031030510651259050340c004480390b84454403901e0104c0014012400010102c2e03100208662044c80c04d0b0509121280260b800c480c0c0858807100c2841c1080030550700840407800941c0180104000d6440c40c6001c1e00c40c0d40740c10894207514100e1040c01409004010303051698815a102d2079440a00860b81040c3c40944181c1c115a5035403c420342d403032040c8494002c0d41d480e2103810070004444100b0a002002090002c42c1804610044000203100018203140600403542c0c00081904049480384024580000700003800d2505690240030f1711104217078401c07400c0c0200810b0000b031009203805000d494050b10481e84405200300410314000c506400242090070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 54230444 1250 54229194 54229237
    0x4030e06071a01081207020405060a1208071103010b010f05071a090c01090504050c0a051605060c21101a0405040906060609081506040b030109060509030a03201905 72
    0x2541407100354510401c451824541c0e62103020681700e661284003080440c1c0200300603000f40c54a034104a8000c0e00c01003060302669070f5403402415000250740202c400d89804148842445403600319000c0c0054290024091140d2600008100c003000c0c42c050310500a010070705506110407100100c02d030381035100001d403c0d07040c506040b80d6921100700c280e90001d010b540b400328960510780920360180500c003200b01d040000340141038035290818a004c0071282e41c0c0c4100d0ba40031a0003004141d02400002a01b079a0310440559034040701c259410100d503110f4141b906101c2d060310301800f90000c89060021401c406515200060224419540718a40c86818032090b5403d00c01c491748548203e03006602e5180c1c06560f1280e110b0b4540c500002c481244000003000641c0e1806c280d001121000f80040c00013442c8441c69450030200c03030b401e4a54204950011811595907501449140703810440ba401c45d84c86188100c1000c903d078414907a001e1950040d00c2d0b2220100e600410545150f000b0250803c0710404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 54231694 1250 54230444 54230453
    0x409050105010807170303010e040516030f02150a0225031a010503071e0915030515041101090b0706020705070b0316030f02030601050a0e01050405121b040b060d0504030e0607 77
    0x4800c3c000d182070307401418000070b00707417034401c05245442d0003d001a6007140c2c6008501100070b00c00410945250040c03409906541030024180009140301d400c0c85140703060303240144010114241410000c9001c10041e2090007034000642c003050700d1403030b05c2d2203110850101c1c851100102582c802030901c082059203c1c1490040324807281602c106504840010356241e0f0040c00541c414000b60300c404c51381d86818080000281c12001414455844500d03035140e80e596410724180708089040b00711907240d02444104038104025a00021003441c4c422800ba091080c060b5245c880e01100818943d80040c0303801c1081f5046c464140181030000749a40c40e490041600701c48080c5811f100c0f000071b807401d003003041c04e400c00d032003901c0c01824103a66860a0121210041d04e0049007023005505120f011302000803282d403080802c5140c180d004028050f407143d074109035808218030b082030034412410903000d180f42e611014155040d162070800041130303d44981c1030641c3d0000c1902c000d02d07007103980001c0540030310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 54232944 1250 54231694 54231701
    0x3021b01090b06030601051503040204090c06020102090f0a080d1b0f050303090f0106120b09010b10020705040e0102040e041502040803070c1707151d0406080120040509060402030a0b04090501 84
    0x2602842e81c0701c0c81d036641c03d4200342d124a001d00a1685c081c81005989000c648480d024641c41440500000780d44403032501c52a0850310141d00c00b000503074001411480c5400c040a4010070b42c7c5094500b41662810040c00c1a03c1e482c0203004007003001903c2e841c424150321018010a90160040040800004182000c9440307910448141e00c0e28829480102e00351401445910304031000c03c000c81c100240965224020140c001d0710200c11992192040000c41d41c650f055a460080c81b500204015440d040c02d03c810342d01201c12861031644180420404001007500c82544140d10041e0780d0100d805000c03010000f8013031504142070f40d1001041d00c0c4100105c0d4039426040c3c1c1c0c040740c03108080e11081c190195686147d40581040c21428011241215000b19900d0340003e408a074140ea00320040c4000c2401c450148e800211141e440341c0444101e00341d60080f001200b0303a0b800e245803400381841f022501140f00a00410b02456000000401482c82d590103520000d40c000d006002d042084e0504078040c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 54234194 1250 54232944 54232961
    0x91a0112140a020306130201020c040e0d02010f1515021009030306030c0e060120010e0a051516022e050a05010f050103090201020a0204091407150216050904060504020103021b01 78
    0x4529400403a41c0851500080580d5650342c0140207006030342e16083c49003901070041030101d043d0b10802c4080d15031a074460240c00780c11201100105a00d0140c000c0c001d00b500c1e070000060760018901801092000ca544003e441501e2070081c1200c00138548078401c0b071603c40d004180d41e2140c2c0c82c0c0017940c02010303415003005085901a0034400407003602d840ca026043c0005031241808074030300700652004001080102c4424002090000134410030260601d0300b04000c02400f200da03030300700400061251040c44000c9030050000d40c442440b84003859800381d036130305074203d0f46480b174624402010a199220b5048640100c05180b0610240c1050460600602001e001c1d14801e814490030100d000d510074030502d240c50750164000c10660500fa000d000c000c1c481382c0410707109481540700310390040700200000001880101d80720b03101302030b072607200a052401020006800071b00c0058100200d0382c607010500c0e000340d08290005902d46941c40160300a1181c00007071304981410028900e014581035002d50711 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 54235444 1250 54234194 54234203
    0x9060f040e010503070b0a02030315040f061710050103020306280f0207030905090714090a15020a0c0e07091502100c0c020f0405062202070b130210020d0206010504091a0112 76
    0x709a15600c501c080703800783d440d160006a009200040c03611403175581e1188c0d07210001d00b000de584005640880103a50305904a100c2d1012520b4803150442e90070401440107001e84107041280e541181c2c000b076290840540080c1c500710380d00300c200803c491031103000018199640c6041141003414074201019400851041d004180c1100000509081c8200114860301090f6503100c4150002410b411084e0044680a40c0100f1031120200362600d40b050b81c40450b03c0d941d002481606103a03c0e01c807034085455000700c066400d9200a0010064000702d0780342c10b49049a081c10503607080340d04124030300900c200f07002245a0400314074042030740d001940444501d0003555005400207036030082c0000d580c81503c109801580c01140510381c1c074032a2402d4190038018003005454502180c0b1707862045c41050301c409101c4102851b0035021450403078401c109200403070020700b100310340108002c0e440f90014070582e80120346450411041255405410781e130458039400600c3c095841c0c201c0c410072021070b14030445 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 54236694 1250 54235444 54235453
    0xf0f05030f06071b03020a02060a03050414011a040b01020a15061a0301030c0302010e0307090e07060e0909060a05090c040501030b0709080316020609010306080114090c040b090c09060f040e010503 86
    0x100d168202082d190711a030341c140c0742c0c8018a852401c0c2c1d00003c0d1480c01d416011409410000001a40d03004010700014501c0e540120f490f040504105039607140c890141d00c0300340c0c9001c0c48000302e1852180003052504045600043c1c0c00c00d40c40c0103030b007864004803000303054400364031100c0001809907000f0b0003920403503141007810003405440b07442c01c1c0c442800090040400070500b0401503100f96458828440c0240c241c0707206ca555204070205031802e162256456070800d0300240085640580105e41c0040f08031910849424169406a264000a0051400b194507000059140c9108010407403104801803c100030943e524100318030442429200040052070100300040c0c00480002590303000851600341030f43c141031503070800c00e0350303070202910605040d2070b03050000d00e1110078450007040c88008920f240c0e0b50300d00004c0260800b00440440b034412441e0102c9142c03d5280d40c2d81d51980124071a040507558a0044d000489074000d40d10420005140040d02081c01401c00e0080360407030b602503040b035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 54237944 1250 54236694 54236713
    0xf140106090515130e01150e010801260111070501090b0c09061207020a021c030f03020408030a2a1a0112110603070c080a03020417060112030f05040f0f0503 69
    0x1155200024421180e12240d240031640f51901580c004201d81018811620243e0355141080d01d000c00b800d0303021022990b0061400b140842d0450780301080700d807092a15001c55810034a100304120007548200300710003101d5401944400d0b0950107140005a480040c41d140d280320301c1c0943c040c3c4031501f011504804420041014018064290307420640000c0045003444200c500c4000c920070b0040121003140314900d211000350b142c010400e01c0f40b01300d11300065803014040c1405044075010380041c500300351041008001100b0080156010600c913403816600c1c080411000c281d920b80c8461071501c07c21050900701c2d0801c0100c071154511a0003a603542420b40e07a0f41ca0b03001d00b55070740301100680b4229805001e5041850f041d00150313441543d505002d1204143c5449488807038000320b82d0200425400034051000c003140900d841c0001c0342d124000c282c03940c180a0041e0841155110040074441a0007410411502400580d00600b0401418030201603880c0e0f0010010289403050300d00902400b84039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 54239194 1250 54237944 54237947
    0x90501110903100603030206060d030912080d0506010c03020d0c020105070b0c04050306130b040f1b03080c07050609030c040207032703020111031207050a050c06101401020304080c0913060f140106 86
    0x1201308880c0c040d009808160780707501c00d0000c5020010701c04c8040001086022450f061200541f081880c01a8492502c81180040c6070b412128007500050500c81e41c2c182c040002a400100f1480640c42803400d02d002e082c42d84016100c80c0100c0ca401048200403504104034481d1445c00f61040f21800c508992180d01d840c09600b020a994880c043d180fa04800005030104540400820106104041a010740a4542c4290700c00c02c0d01c50300101c0b01072a000070161054102000440040d01c03046400503d8071130341c8c2c0d00195a9000a111040c0100e8000c14070100b0305010b411800b182000300a00740c070420032024148003181000303000490114003018201602180d00005499070314000594a40c2e5a8132510010346080e0884840101000003c00014610200034060640a6510f19003140e01c140c0c10006070b140d220b0303003002c0b0850456109210130050800300007070040b01d6000a0300c1d41003030341c0c844890003443d10003060300141686091850310407084070550300c010061042a82d8070307115a62503190 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 54240444 1250 54239194 54239201
    0x10605072f04020a030507020618060a0c030905030d05091b09040b0414070e04020a1e090b0a12030206060f091006030f06030614010305010c0201020405150d09050111090310 76
    0x8064600c912074101c040341400500d80380c80350326041c24800d0750385141040015050341d001400304000a41c407003007840100c2d601080341681107490190340b80c41c1003c1101e021070b81ca107401000f0f21451500d4101036145540640e011110030354005090300c1da05c1504c916480082c107026100c201b01c501c2050360742e100c2070300c0c000704480303d81400510244031078032180c580c0102164090030a0701e10400080360142018000c203c280001c20400007042554640f0740104082101180d1004080c000d2070030101043c2c5d0000000c020503a0489030001411437405004580c0707510054102c6d605120700c41e81c5103020f05070009142c2c0e108200490700061455804000e01660000640e00d07500704541c0700900b440a180640c004009545180c440090300d01d0742e80d22084241d404050351111044a00030050090000078015080074a400c0e00095103040c0c600030201e01141c48481020110b50004039079100c0341062038202c00c0301d09400c040244010b01960648842c1c550220005502c2807003003201000c02600d0500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 54241694 1250 54240444 54240457
    0x2090c040812210402031006140901090207020108071d030303010f15020a020a091d1902010f030b09040305070f051609140105090a09081b0a031b0f24180b010605 71
    0x544010b50f25a204000f4040c21902a00403a4140251803074000f9103902c0c1d21070003004108140003180c4164110091100c10750043e0403500e42c80380100300d00d80160740c000d00c0d000e030007070b08a2a04801c90001000001112202c40900640c1804004000030300720004031075240503550151030b10604405c0300442aa0341d40f000780b40007904120351903010002d45460b58800c0000c031422074010100410703032400380d504121401400580c50489094014150b50784040c02c600e059000382420000007940c034001403001800180001c042040000380310040200103269000e000b0b80c003001300c03440360b8285201d5000c0341d40c56000e04d210461804c540441b1901300c0c8005030341201e40242c03011301aa280c41c1002005803c1c104426500d60000b0021b002d00906c078003000044050742c1c0005031000c0400c5180040880c01c0a50111144031440d07581180400d103190f4175024420b0713021181021801d99442000c100000c00b043d0010a02c0c44d24100a4101482d40c001e0340f100d41c4a404140c94581e00d56a094940b40246d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 54242944 1250 54241694 54241717
    0x10f08040303050601050c0106080a0506130c0b18130501180c05030109050a090206040f0f171e0c0d050c03010608010c05041404020d09080711010f050913060302090c040812 76
    0xa0204000c02d00980c02950082010325209182582c1c1520031820b642055018418030b90015105c0802d0000520165410402400d00300088554646403014109094050030194a0000481800c006081007103400001c401400c40f41c422800440600300800c003d2050764629565045407100c083d01b14462602c0d000e03215140c990541c0d0070f14444100500000301854599941ca203140c501580e9640064001840286000700c1c1050401520301200d0005a1040324100100b118039100180003144d509184034030f40a030b00e11228010b142491402c07441d170114030f40051304c100841061001c080380548102006130020f00c9a2585c45c01200d08a41c0780c810000002364051106000c04a118400240d800c80014400b60414220007000350489011040403541e5200025007807040011400403545c1848090820000440c00f80c1005803280c1300c2c104541d0302c03890351030410701030b01052644042d014640103864010355260035000e000c07140c0d106009104003480b4027400820806044000c9540d0750029 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 54244194 1250 54242944 54242957
    0x6010305130f050a0204020304150e070506070818040509030c0c090601021e0109050d05091f09050402091201091109010e0903070b0403020c03010903030c0f0c0b040209060d080304030806040b010f 86
    0x25210300a0107280c1c55000c0790f00380a00d410107005aa128006140a1400303000041e440041070511481100c4e14001c840c40150840ca1081040343d890805841c00e482d000104107036030303040182c6041046100c03a900342e03030703c07a20784010310100420001c0904520002c02d07040300c2d52004100e0800c003d205084502d140141e202c40084116090019030700840c40941034004201504a50748503030600c4804d408080000f84086040034161802e1006522981c01e0508944080b0b001c107400141940c05901406000315000504001c054940018100e19124814000c1150090f54501910b840300c1c8484258031901d0104004a001421184079a001d03c007080300940c5040020740c0c400505810040c410342c190300900315441c1d140e4500303009051001d4465035000595100c071003c013415805a21801004100c926070701000010b44101132560810f8040361000800d82d52400040c0c40034046180c02043c401010080c40105904a40c00a016003c100e409100001d4541d00441d40c2044ca0b80040300060f10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 54245444 1250 54244194 54244231
    0x140301050d030c0b160f080f070809150411010305100f0303030b0f04050709090518031b070b0a05031608041110030b06070804080c090c040303030506041409010902010806010305 78
    0x2000211540910b00c40d0601061020140d150f02c9051481200e1000843c503101d42000711050307100d15130702440310a5080c0031125060002c040800b120000304071006100462020442c109810480201e0800220005103414645441e110000205028117903000c2030408010132041500d00d00968191500408048402407468030114060100081c80541140300810b81c0d640c1a140c5001e100c0c0303e034049465070340c1801d103428240320480700c0080c40c0907602c0c182886190311300803001c005c40d81100a0107060305000f201400020341402010303800040c0d80c0c1070004210701c03540d4211018521400f180350700005c82c211241c406032008e4008840013000d0050103c159030f41481d240003c0c40541c1014680040c050107034801003085944205802d80342500301041c1002040001c004d0403443c10001d5848180d141000b4942600900a9000040c1455100c41c00519141c0300c642c4280c05040648101c07442030b007000000340d8000e110b6410164000707406040003591650003400380798080e515003125006c1640 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 54246694 1250 54245444 54245449
    0x60308030c0d06091a011e170a020f0a08011514071e02030102160b010f030c15030e010c030f05091216060e03070311060f010b0f030a02090a141014030105 68
    0x740321010b42d03844603a07902e00c0480c1801a501c42c1d0030b0461900c0d21600c1a580c0414000740503504a919004c01074a002881c0e1b1030301c254000c40e50802e007031504594207c0341d114090100064000c960414a00c2c0700b01080c0c680c070700395111080c0d0341200e010302d10402da040e00641040759000010b502c50300001d00c0411034400007a0103040790084c0014000041040c1c52000d500207822381e40441d6441c490b401c9521160030a01803120826401001b441e040f00c1c801e0361540d0f6500c41110785501c5500f4a580404003108100c2d8082c1c0c2041072140c803140020400b0450003031000d0020461400581450361809000031146031001400e21465075041a40d1400c01c04201581468420304040c02c5a0081d10340c0001c00407007030200040d01c0c3c218030a440b50a050b41100202c1031030184010300c0742d100320081f01c004020f10390000088030b0258071012030443d926590001d4180107031064006c5140c01c00304070b00000880f490301503194000725008036244070040c04100412122010410070780b4408680406c010051403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 54247944 1250 54246694 54246697
    0x9041b39020301021b01060f0806060a06032a0c1203020309070b0a120203040b0405060601020d080402060901030b061b010615120b031f0203070206010e07021c0e030708030913060308030c 82
    0x110710080000d4544000d0350742c100c0501c080200440281e0307444101c140070289100c00c080024000c40c0009001030b1401743c000820410b0703d0320507034062566502c2c4820398510b0099000d41e03d00c0c02655000301d0030004110040c8044d081060641d5941d0409a0703c8000390710034002c0342c0c043d08018000301041401c20388251015072280304402e041c0141044e528400c0d205c42e001540c452409000f4a59440c034060030141d092000007804c0c5811134000c0d900c0c01e502c45400050f0190895015284a03448051090050740103001c0040c031a43d000350049444081c25011841030201e1030400c90080c49100d680700300a44000c00381012213000f05002d840340810481c0315a20081c0342110041c101c0388050b081981c038180101c10b007020321845a40010801000540410000e80113045841c2da629640c41c006034000c1d02c41c21944910f20600894140011303e543c8100079031207140d20024140d4044545e521031380b554039840000f045009130b1010407484004c20040c03003080101ca4204800300c3c95a82c580409000c02d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 54249194 1250 54247944 54248057
    0x6050c0901020c1915020105090c030114180106051c03170c0702010315050411071407140d060b10030617121c0204080a030305060f040902150a0509041b 67
    0x4d030b18070000b00181004000d440c0707051401040d000001e4608162521604101020740954000d80c10160074400301c0c03c05120140c0d0012a01c400700300314800c0b170702c40d45006d040d032640415481079540980d06580c1395420740c9011002d1003034a07038003006c0c14030907407860f045901282d9191503107009100282c0554040d030000702c110047c850503e0000d644035030000302140d0b5409041100d003080030403084c082101d980c039001040001c5c003000300310341860704241d00c0030010203010315401a65598904420803909801001d1114001080c4803039115400c3e00040c020403151052100d1255a0076104103803c00100320803400c0c88450020700d16000c00e443d03556400c0c4505e1560034801550030000040c40703081c14004070210500c0307a42d02240c107051100400070710a65034400c0501c03440c034000151005940d2100c40070b5441c1d001506260b164881c0300004d45040c041e50300710640040c1001c524450a0f00010543c92000f40d86072222128190f25104490107a1035450b00d0000480181d801d01d01503217501d00303807000ca = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 54250444 1250 54249194 54249229
    0x9030306010e1f020f060901050c03150301021303060b03010c03140609180a0302011a010e180c040b03040503070210050a0f030510080f0c0307090b030604260304030c06050c0901020c 80
    0x540d000300710030540c1d02d030000f54900c40103030000008400c00001c1444800d80040320b50000f07001d2130920320902c6100341f0010b8400c10901000f058080280d4900303405481c013040071005007401c0107035203040c2480500040c0742e4030785c465403030810014000c42c024400d05460004424900e1140c1c3e03510418030000d548003800300c8140e42a883c7c640d02d46204104010351007140b0a03030002c10420001285a000850051101d0741404041c02142c201a250a103050741c440341030041900c00780d220324241d0000d03072099420803c08010004104414040000004c040c154406c1c1d80360041180d80000440f124003d800c40c200c0042c0b603400f568180d180c480d0b0130041c0c004204084c00a1703401eaa901f51645000a10500031400d0703041500d03090381c240384c2404808018680700000f1b000040844002a48800008100912032204200c11418040320300740c0d2240c0c907610307184410303540e0704080c100507249004800c41280c14908100c0007030a20440b03142030702c08545041e00180613454029080120038005d80300c0e00c01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 54251694 1250 54250444 54250459
    0x3090b0a20161202040e060c0a0206010512030a03050406021909050a05040b0109090b0102010f0c080a0605011b061a03010212010e01051912031206092403120507050f0109060507031409030306010e 86
    0x40007510501ca980c8c000e185000140703030b0300e8440041c064108070059209502c0b80d522140d00110703007000403046a4882c485450001641d03626450200c4c000c0c082c3c3c5140c2c400340d09043c1408043c85402c12a00400c4d9401165445000c80e6a54200015101c009001c1800180e07003070300c204120007180c0c015840b034071030500012a007a180400124100c0c3d841655550010f0300c0d14080c424075503154401c12015241c2031904071084aa06240350180c8604a07800030b003202e0f65081480c1034440708454007841c881000740290742d101d07a05900802810420b01550180c100624000030380d8ec600060843c41e040030b10700806850500d0310000c1191a04030301070907020700c00d2001000c0d540340300314401d82d8041d1007503043c0000c1c0809009004201000800442c86520f924040706002003111507841c4030070001035242c8a60f4449051800509207a5a80c04107801d66003018800420000107411946c80b500b041d5908001103501c003524803510b0601500c0c40886500100082000d85d40325041001e030000002c0d0860 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 54252944 1250 54251694 54251711
    0xb010f0801141005310207110a060503220c08060106120203011a03040305090409080c0f03070f0b07110106030b0105100e0a05011215080d02010507020601080706080403090b0a2016120204 82
    0x12202480d0035030003090b170070b034002035440400182400300d03030201c1410398075001c0280c24007002400340c2c80060200845070505461b82e81c504a0030b000c00e00350342030b40640d014000740d6031b0b0701040342e17911803e0003044046102c040c8a030800385041e20981e412545110040503418001c0355420b030301540080c0c13013a030400104004d182c40585560003000d02092084085030b03a00c0091912450420440800420258000300000f07004542040508000590040d0030b0740c1d00d03615011002d440c0968001141d15865081180000c01d00128121060480d9800d6a95451a40c140b440840307445850024039540002a40c005206552042c040300c06800b81842c0000b5128009005440341010640c2c00400e540d880380c201d10880c583c2c21700840703800075940d000810300b13541052011900c4008601448040200c90000a8141445503d4400040501c017100741d40d0f503d03260000501101849154002d40102c041d070900e86d24000107405201c49a00807a06c2550340d04000c03400c0800d5442140c1668020f440d40781c3c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 54254194 1250 54252944 54253009
    0x90a020d021c05010b2a1e03120601090e190612050304080c040e030403032105010306090b060a0807050918030f031504020406170709030b010f0801141005 68
    0x14801c20b040d1982191048100928010540d14140c01c540250301041c00890440544009400c440b84101e01201c202c0c0d0004c806840d20300704c40074440c10086034814402c40f5170070700040001c0410486d540d84869440d03039500019985903829208281c8103608e0213000071481d00d04a40c20180c1c9030031503000440d4455440c182c0424405e40c1c02e03025070b5140c00c0001d04020080d0100314040c6103880944003400054031801226031a070003a8400035040c00428180040d00b400700c5443c0d80913600e580f0718104042d5031a41400c0c1c3c01061100d900703c41c050102800301c1d26520b40076002ca012540100d005240a5040c10140f211a8034090014501350500388003d0144650a10103480301c440c2c0c108109807245498218007032070503540e10b205401584104424404554007110302e040722038841b000310300e107522210380403a542c0d140c2d82e10107018010080c002180f41d084d0403414900711b54500d0000c1c0403080792805003001458058802002c5100a000c0801644c144500c4000540642005da030a9000d000a60b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 54255444 1250 54254194 54254197
    0x18091305061008070801050c0702100c0f0812070e0a090e120a0305091009030507060b060c011104090f060f1e0e0106050d0c0e01020a031d03030705010209031c050405090a020d02 78
    0x1018100c020300c5602c01c0c4508242080044010610070300280a64104425800d0007407144840c00f82c0110701a10103039110174024200c48038500d5200320502800307006400e280c03005400520030b80b62902d0500c0f021038402d038829002c03c40c8155008080b03260b00d03443c00d4843c900038094080d0b203280364010011511400d00300180a00710341c0126490200d1240b0308098032900384504000c880c101d4034036160325040400c2d4804c017561402540000000340410504001400b01d00402d1081240d540c03c2450840c41000d002004c1d0048502140b011f1000f00c441117090402e031a51400303241d500c44002c0800b0007610f520744444030701a0490300c034180d003a41c1e10b5126405542100f40c0140700415000100280030300580d1249c00c108000619003a5030b80e064900000b5104c14685801500700480c0c074100c924a40b080300305980b040c05004003204d03940c2d0581c0c50864013035008040400c1c8a80503203144481c85810342c0c511102940c10f1039682e14500f6040400b080010440908810742c0d4507800c1c09000c01c1030f0181d10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 54256694 1250 54255444 54255451
    0xc0c080708030109060b030106080f06010908030a021006050d0f0b06010c02060c06061305160309080405030a050703060e0c011e0c061a040f02090102030a0e030c040507081b1809130506 81
    0xc1c07601e07038039814070b514074094680603401041c04000400c01000340e0f991107450260810080c00d05d01c9a29115400102c07409842c0e5040304916000001d03080c01c5582c0c0002d500346240c5a003d000303120640daa4801c0000495803c40081c00d00103d079210040010070307541010b5840301e01414031480c1060a5000308095411558003110303139501ca10140301c1117181042e011401080002c1080c807281ca4110070304482428800701040078540c40b0307100701c030410008030151805024041d04550300780d4040d08185580d0845480b003610424030b4a98405010100480c0010036440d041e15620105849012140300c100d0081a80c4420040c5a062040c005020780c0104c89100c1e003a084034241203001d142c10001203461078685581c080d4070401844615907004000d80c0c039505043e00744a5140031070340700801e0822421281079a032052030007042080060700a100706000309000c0140200e05c070880702581e8078a11807190051005010103002c948180340000a16074040c410b40d0812807804010b50b00c00d803400400382e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 54257944 1250 54256694 54256703
    0x1e0603050609120a050901030504030207050415170f0a0f0807050610030201030b0a23030a0605270706020c04020313050a060c0219020904080a110601060306090b0906130c0c0807 78
    0x240d042c04141c1c42c041120220b003c250b0800c1d03c0c80c291000d10040c060740700e1412641d040c5621080040c0525000748043d800410001d40f0500c274921804180360b0b00c41d14280104520b880803264038a5100000040b58115401c4490051400c0321490311181c0f0a1610140211030b82d81003002030100185090140d20b001300d590580c40c1d0030103810b520000d01651407000c3d0035405a903221000b002181c41d2a00b0700c8013404000f01c2c000c2100c081c50401720341010621000542854180424484100c0c6a460001c00c840700300035203041007a600c1241d83e43c40305810301c00c20f80141d01c0140120308a141c294015a0011036001c218029404103a80e200d0421014180551f10244d4a884400c03d154061000082c0004c0342d41100c0540c2c04a5800103240480c0036001400300301010441108840c0210103919002c05490120303840b96950310304c0107000c4c1040c3c1c010f0111043c10030046841605020341128024400200207240112591172104e0040000b669100100011031000c4004100307020020301c01c4074081c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 54259194 1250 54257944 54257953
    0x90606080601030212010e090c1905010f0c0c1a22050a09060e1914040c0303021e030319020f0706020301080708030a0c0602130b0d02070b10050102101e060305 70
    0x4118014118038001004a070506004100d9400000c0e20340704140c2c10340342c49402800ea2510303110f1347c00340340c0514501384030341000d100780c401108801a03000080890310241d031000b0080f401c0d5042182c894556070f00080900d42c055605029032040d40450080110200410034102512001c060005500c0d01c07003040c803002c40303086080c00380d400c2040703281000e08424442880f000f0300d005000c50402d080105010b4048007201c0c1e0f60b0065141c550401e5240c150498400d80d050300b0207081402e190111448100c1c09849400b1098080da000f15141c0a6460a80740145083d69220552001c41070781400754001240c2d800c01071003030511f0042d0040c05071203000c0e400042c0c896041c107001928140700c40c0c110b190154000d02180300c40703652200d100200d1544c484405610745540c690307100c101c2c80e010741081d2480640441c1c207400b03142c5c4507800703054001c1c0103c148941e50b4651020341c0c2103c41c0301380a55401600312a001c2d5043c011941c2021a24604407440c00321111007555254089940b2600300722265000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 54260444 1250 54259194 54259199
    0x1f030305030a050a020406120209060d06030c060809010507090501121b02010c1403090a170f160203010b01030506030303010b1804020708070c0603060b030a110d11032202060706020c0a0c0906 84
    0x242c42070136401005014118900f5051040140c03298840451120040e50000380f019100c0d2112010307140c0d8814444c105109058032858140d003401d240d4043c0700c000400207000035000c0c050501900f802501e803a00d07642ca181c3d0420740115904060849401d00e042c1d25003030300e0866550548100344200c0b5041d8000179440c1c440d42c0d00100400e45030701250f0f004800c00e2003271150802020441e203c100341d000d03900308502400106100418010782000c81c1c1002008140388100070300800401c01e485101710020030a012101c40194101c410075540303e0381550042c40103110f82c603042c800402000b099007504206e400c0702100081d0030ba038495241200c160001081082c00c00c212242c2c0d030303030240045007020300100781000c112030300d0303408010141d41d171407600d4008203556554038004690982d06281d409000520ba8010000c01c2c0e42e2069400420a800029000d103000101516030108150f00400741880c052072a00c90901a40103900601c2c0f1902500094400080401003000300034200400013148852 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 54261694 1250 54260444 54260461
    0xa06060906020303010806060405061801060f0806030102070308041e050a0804030303150e06060f0403050a03030b030c0102010207021e030106170106090501060c020d060c02071220190e1f03030503 86
    0xc0564014000d550003440107026448021444581c0700909590002e41d07540c490300000e406500a91034011561445000072520f10341c40400e1203a850050303100c0312034540307440c8145400c0348507144024000498100118000810200b45909000001000004041c40720f0322164208500c0403002c03190424002010010141c02d40101032a00c240141c410a40074503050b94010740c00002408030348504400240d0794442c125090540340030716080805c40346a503800d4540a402002803440d103174441e10901d423604001350310500803904059400b60001078402251403200031501404044141e05540b92034020481c98090b001c85000c1a2000001040d80c5141c604207000b00c42040c1c02203c1001803c90324080541c42c0c92460110f800c0d8402c0740041c54240181040b402c1010a811000440141e200310a00744103e07002c1080c940780f51161521301c414150010004082c040390000d54451006000c2000466440301901d9840f288041c1190f8802103040c0354003498949030303003040300450808400c0c0403548 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 54262944 1250 54261694 54261707
    0x8010609270b0103030c0201090e0901050406060e06060a0c05150712140f04080d060504150501090b04050d0b0408040519031e02010207140109050307090203070219020a0308070302150a0606 83
    0xc080c48182041c800403a21402000801404068103001700316800d80d04591003803100d98014040000004003a00f0301c4082d4a01801041e1415103400342006400314426000f009240c2c02110000c00c42c614020f00300c0000e440310091a20300760389600a00900c01a00d015540d1035504c9912560307102d1036100040520320317044980e846440f0710124440b80400c060008008440b5800a4200d4642601e4801842408001e80465001a500315081107410b5070b20500c00f1440e030050b18026214a081d141d21407284d034099014503c9025880720598550303a01084100d600941c001c1e01500c6960f10705a01d500c08035180741d555a0111680964640c810030920495201e4034800d40120010150103d1107500000d40c2c44480e07000f2030000d0700300302e803420302168054180400200000b60a44007002e82d0340d18000c000f50800c0794104050302601d07038454110f03032007402124101c1d80e000f001e500c0e0150035500d6441668001000031800e5214400e84000701024001e0514401e4124070785c045543c2d402c10710b004200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 54264194 1250 54262944 54262991
    0x703030621080405010305060f0a031412031003060b060409050f100603020306100809011e0c170403020316062304060605010f02060f100b040602030306010216030b0f040c08010609 79
    0xc0e040701902580003030b51203800c60b030440c1d200b460041038a454040004414000741c0201d03030303803241d15614000700300701c080b584202040214205443d07040352110039100ea1b40c40304961480c5d61705203049080c000681d455000070700351070b0702410680c20203459005240031100107503244908a040941005801100c1c1c200c45006410645000d505506015021036410b0303d50700e41801c148504900007503041e5400354403110341451001e000a0f2042000d181803402007114804510000d400d4444004044803c0303507000340695450390083d403401c01c510000d0311040c0808036044954031340b100c106217411800b1041c0c045824504041d040c480b4102454601e00701e46855004e039040c01600440e410629401084250b0b102805020045903640d8030b0301c1c8180c4090007500540b0220001090204100354004040e51040c40280c0886007e02080d1100c0c5815000754030008010302c41d13200000720100b4034000703d503030410300c00c0044004107516802401d082d5907954000441141da100e0410302c20080e0f51210802 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 54265444 1250 54264194 54264239
    0x61d04061202040f1104030b06040515010f0809121803210706110702120717070e0a1a040c0201140612060105090c070219151107170703060207030306 66
    0x40070300d80380c4940e51202412002910469a50301ca1608141c155003001030407800c480841c0d541d480e224500301c80d0300d80c000d5420a00444c81d0400103100314030a04150700403c070058407601d40062000800720759000c401015180a805140092a099244840034100101c85040118104c203c0e250905180041c0c008400d041089002290001000c1102c21904000c5c0c000e0004541ca49541d806e0384000d1103440c1000f0f401c4403d203c0e40e11107030503021030420305544c8000040916081403c0c086c607a03a80c054003456a4480c20700f00443c0303a10700582e0190155004113411040c2103007275240010219002c1e1101c45025035154221500d540300e000541a80c000400c9030080d44101440d8461070762884140200b600410400001c18451000e83c0161004282c1c010300480340142034a01c0403905640c103115500703030103401070f80c114007090144846445c050440030080540d503250074240380c0207040005012540d070045400c04004030391240003d01e0b4240c001c0e20301151580c0b820010401c2030020108030340 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 54266694 1250 54265444 54265451
    0x1801060501081308040b030a020301030212011b050703200106080d02010203090304090b01020a080c010209090c0705100b01090306091a06100c0b040212030a0207060e0612010b130807061d04 83
    0x200e070b07040300750141c2040b5043c0da9602000403e14005200f4491604803140c002000701c10844001143d4008505070780c401c1e1180380030601802241800e0f2010400d2441e0300d03c078401d0400000e18030a030003415155010740b6100c803407090b81d42640c20030006004008107a50751a1101849015000c01c440264142207200840c80e524084010703a850b80280d028808126864005c0c00c59960b00c204040c50484c1d41181801c3e541d0001180218000d50101d0b02050140a1803800956540041d00c2030760381c00c58110000d07028cc90310100c0c1290040880c41440c0d030600090070342c0480030031803e100d40303210300707202c0e0040f40e0705500c2052669483c224014400c61140340c4104006948540c00328400e1050ba6001d941601c0903101d91002500d050401c400103a014400070442540403a030008108003180d550342c407800c5004e0030340c20500019225181d0701c0c0b100300c0303100e4004101c413481002c01801c41d00103411211001c00c0d00c819200341045429030040e400900e94000c203600b0740ea4640d041460010f0101c4040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 54267944 1250 54266694 54266699
    0x30905161a0f0c0607030204080c04110909060a0b0d02040302030105100302011e0207030f050d080a0209060403020607021201090506090d0201090309180905010f06090e010b150a090503070b03180106 87
    0x400890540c400003401072038010541d202c03424945070540f403503da01801514030b1407410380c60040c001c0d00680b03e000114030444003a04101e09052180360344400c0c00030001032401ca0000c052041500000d00388940000d4680e00008a14505001900705000c401c68056640d030310b035004042c2929800343c54009040100305080005030707044504070700321814108500610880307024041c0d04101c8150300142020202c0410b40e0200038001c202130040401945039031801d52074100f0040d040340105042c280d0007080421092015190038400351030b0003880109812402e42605010341e00756060382908036140d80c0001d0034080041c03404d0080c251445000d10003003007c1002500c000305071031305601c14031041d950f0302502c0e10315030302841d0041102141c121009000c0c441441c2000e2008104034858188400d1a0030030340c00b00c2600600030899000d40040103e494040d09100c1120941d00404c14542070180510f40001c154806008403002049005022916458014000c41404003465540380c200d0340342100c00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 54269194 1250 54267944 54267959
    0x14010506100c030c02030a150c02060603120c01020405192606060d050c0907110709090b010302010f1e050403060c030219211407020f0303010b0906030604020d090303090516 76
    0x4005070052501807408030b01030600b90b4544000f1040a90107014140460082c000c01c8403c101e07541c440c5420421501c1040c85040761220026070310316605030000c8010724000d645100242c07020003000000146441d940e00000f400c00c01d4540e800d084080d0b00e403541001080100740d4244003040452040c42d405100078401d55803105030080c80d0302d03c5a0428506601482020000d100340036402520310190303410004400342850042022150040c49101c0004c1f500503c82e0003003940c52030b480082c01d8a60303401c43d801034603606480150102005a41d080d4829240242101110b0134681a103542d5070ba1400e50602c0c2041e01c0006240300281401000300d00e01240d500c0c103560211400a02e00718008104280d07104d007000d8118080d19411303074142076100c038207080b01c03500b00c501446040d02220b10186605c40c0058490000744030320804083c00380003600803810708030002d56006900074001498094201030300d10440c0c1600c1e20650009a54012003c2002001c2010040307201112205a4115250410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 54270444 1250 54269194 54269209
    0x1021605240609071b0c03060509030405060304080a020a020a14130e0303070c03020102090307091406100f0804030e060304030309020a0509150103090c030c0b0c01050f010b0a1d0310060314010506 86
    0x2d4140604903001c0014580d62007101c85070482d0781c0750b03848000c51510301d0501d0506007240f1f02003903444034900804907100000020840d002c0303400c0944018119503503038441c200c80b0b400c001c02403415800340462100040ea504c002400150211000020520a954080c4130707540c95140c004a20a502d4104000e812000010590740e001c542d500d4642d04c4c0d00903a00d0200e0182c0141000f6a40501c03a00c1c001251014254112403004000d4480c0c9620135a0f0380410801401643c245042c08a240034103500401071148016960080c042e090003081190908085003140d8001c54060300065505c950140840c503012070000001c0908a40640c06420700341d0410304c2d40c8a1181c0154181544e542050003041540400c0b4001036801402401c841561001c2e060715a0b400441c84c801e803946003100148074845441039990580e07000c0d642d46424141412010f4804051a10704204108046012a815903400300061105102c0007403010075864a50702c0e161200418641104219034100010098039446000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 54271694 1250 54270444 54270451
    0x515091209060409022110050301050606090603160207030c0e01150908100f0e03040914100312050c030d060f08070f0305031815040e1e060a0312030204080102160524 73
    0x480042e500c40102001d0b0480c0d0041036540504160780c6d0041001b22148424039004a4a00750001d01260390350300100440387c0f113045000c56201c9005c2c40850b841c1c240032031058141010500482d8041a201c0c0c030340c04620416a409908200ba00d03500501403402421250007510700e4904050504c103003040f100c1361704e56040c1d0703020b001120b549020207034010743c8e9038000b1100c0c05040010380b5510f5448840c03d1020f00b2011490746c168200c958003140344608070004540807030390055108100240400011103255105000b150407600c0300340541c04469200d8450354006161410030400c0d25031416044900b850066888045c40151550f0100041840401158181c61500e51a07005440100000030a0340c07012103184002c1600206021074680040319405009181c841c51400301d40c210b491800400f1002140d8046d04401e01000820014042e41124020f14445050150405454130307402422030f0040541d070607020316a00d5040d41070150a1029082d007c1c8045040c0c0c00c124030080142c2d03103802024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 54272944 1250 54271694 54271709
    0xa05030f0a030e062104060605090903071502070602190207080102071109040203030c06040507030b01122301020d140a0e031306050715090803310303021605150912090604 75
    0x20805044aa80c0c4e40c4111a007110041080c040342c000d440c8580300d00c07107000b16401c5507a41c0c40c0040100e490b00c1c040e80300038415004600218907020b555559850002403d100c59a103031502400350200091103030028210003400c03400b40200181107418000e142a07a503520048148e40304110340000b0034802d005045420009580e1828191910720120f450351107088403207141c0c0d00580c0c050100700310000c0390010031280119400c015590301c40b5440020380c0343c105d100403d20542c42680303000c800e0000c0703c0a01504082d80005003444420f140c0c00c420b454000300089980c100030340800400203103901c13409030350084440041d42400f10103200255254241c3c02040203100001ca941c00400038818200200840400f100b8403250026160000b2250401d840d0784c0d0f40000d4404c0320740440c0c40c0002c2012a05d5005440c114030700c0e00107860a0700298020030503e41085054a46e04020400c10000351681040e519402401031034450559802d00000d1480c0d204103180410043e04150b441c0d00c1642d081c0d070341c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 54274194 1250 54272944 54272957
    0x815011e050f0a030606170f010b220e0714030f0604020108061507081611010309020306010504091a09160608010501020c010305180a030f030c030b13050702031608090a05030f0a03 79
    0x242d4000580480e425440203000505044000c502c1a84c00c0000c1c0340c2c6030070448111481207030a444c2e1a8280c903440380d2481d4000541c4043c084014400c0402d8040140510200080c8040d1074002c2c3c44c00c020b0f2070781006d54108900c4210071110300742040328222000072803000d404541446e03800288220700c0505120b200742c51500b00c20009103020002c84200613071003c140d5981d035002c40d03601603420311752460989102c0d107102a45401b40d40a4004c105242d580240078100c0c5038240300c01c000c010312000100b13507168007620380034500b0280450001402560b0300d00042c02c042c0d504007450460400c90350466420001d6540c01044140d030001007a0724240c5007420b010681d5070f02d200d070440d0100f83d50100f066640c4110802c6c40305264000f102e01d12017203196a014485100300c55000d40513540c00b0228103030004030712058001801c070154003c5402040340d1040d00d140660420b04108100b0114034141d40400c0b00061850f86842c052580c0001000282e026204102800c1c20702078850a0000b07003c5d01b407000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 54275444 1250 54274194 54274219
    0x40204050c0c0f0a020108060d150f09060e011d030406080a1d0a12091502190503040302030313080105060f060324181902071e0f06060815011e05 64
    0x1041c009544400d008501211080380285080d00c3c0c3d03c2e1445a400c3c1e01213071106002c02c602d4104170a1020005811a0002501007603880c5217a0081c541441c005550700e6455100100040301030141c1c030400503600c00042110801c103a00103203100b0024102200c03562003040b0420100d070b003015040b680955440000100b5061156250407002d40c051041c200078050358800c18108940011410014100c035079840d03490a8607030003000d0443c2d964a90b45030159112424150441e00840c83d100340f024440c20a40b4241907580d8007092031034010941680c2201006141401140c0c001d00c111a4018411a8a0405014000082540341c40301802c02000c030001c0c0c1c00303a4041d10b2905000440500b0000d081c0015080c081ca81e00700003054150b4501c0040445c1e00c001c4d0030b84134500e00030344d0001d541007011610012130851811702c84d404003442c111002c00561070240b01142591245800505510000e0001e240720502003464600058000c003103140903800400c400b001c100c00e511010707601c0a072814020400e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 54276694 1250 54275444 54275461
    0x2180604060306020a0c1b060903080313080a020604050d05030403090306020d110307170a060605090904050c0301020406050c060601170a090311010c02010b030f1c0e040e010c0203030702071a0304020405 89
    0x2070240c00c050000c03400010114056644101800e105602900000c03295110745c0c41380c1003120826124540009240d003000788086040c140065812425038a0012030035062a42d4640040e0090440d40e00560040b00811080c083c05100c800d0b0106a907161080c610320303081c0d030003411603005404003902ca103902158045541c800c03a4090f452011020300300985074130f08004010490101c0c45000716583c2ca4900224445402c20f0166800b45da03d5500d41c0e074200a900c02c1800954ad07401801554540714490344581c06803800e10060003c0c0600341e44072581d94503024849458030710054282d5041124001e00a104006129012900200310400c080b4140500e8101100c80320012881c44006500c2c0160803080c0300c0e0158071102d80080d0a41c02e44200a030180b0700c1c2c0c1e850340c1c100145541c1c01846421000c080a104240700f00b100790b0010000217003070103440540c600316245403541d403015030b1002003844041601002010700400e45000c083e01c00300b8102000130828080500024025a181e0001c1040304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 54277944 1250 54276694 54276701
    0x10902040602030f0d09020a03060c031401031505060607060c0503060a14012a0204060f080f06160c061806090b01081b061e0d0c03060b0c06040201180510090906090902180604 77
    0x40e001070540b231010b074880c1481e1004100d040ca003680820b1400c82e500b64040442035165040700e400503058440400900640006040000c05c06035104104201100001d02c03540718414030600300e13a0790769442e4509441806003490080d04491001040d80001d40030300d0b80d0112200d500c642c0c80601d458ac500460f401d03981c1515144040095015050000104041a00802c140100c590500403035451540d81110030703450b8441036031000c502101a107a2100c16074001c1901c00381e090310503000003c400c055041e07540b51421101c84200c03100c0303031034884480c03d010015050601400b8540003400110039075085107d6406030040d01c95018903008203070340c40c1c000c0c422052480f0102480580c15a0341c184501c0d90341c02000244561004640b90032004150700d416001601c040040c0c3c20300030030040d2942d8005482c84c140203070411030011005100459180c0f6005085085c040b9180ca466459a00f000030790320a071407030b45d0000c030b07050352030aa0703c0d20250383c8006850114419213544c0d0b5145840d12404680038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 54279194 1250 54277944 54277961
    0x51e01050408010c08090706030510120804030b0a020a030b04051009050c0405100f09090603020603190608030a030e0f0a020303220911250209061012050f0609010902040602030f0d 79
    0x110752819a0304c43c81550040c6916105100d0344c1c0a54401913254201502120301c00d0318104003088818a050001150451100e1603507802400d120b414250340e0b545075002d4102c2290010038203034001c00c4a20a0030307014002c207460784100322014400c2c0e142000e110b19403011180309000101d612040412074145091080f2070180a020301100a07005001d0fa0240499020722082400a80c040000103000301841c4a8031080d030ba4010095407a50702c620080c0b5102d519111094030950341d48000c0050750082c1000149000034103078074085a00085080028200600c86c6e84a051a40040141c1c60040e540070045440240815060798184d40913082c200c20299501e800202ea40d500d030508103a00f8440c2c0001403e18010344030680c80c0d0b001c402d120441c00712904400d000390000040740100d9454507001d14190303030101480c50800c282517001c80b800001e9410507034000b0118000700c0b00384045802d201503001e01600e11000c041d031030f0500c2c0031002540c91181c140c52110b04500820190030801083c2c110100c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 54280444 1250 54279194 54279209
    0x7032304051926070203060703020c0a02060c030d05010303031b030b0d030f020f070e10050105190f0c060213050f1e0f13051806070f21090c060f080c04051e010504 72
    0x54850700c28044181662200e501031b0f120748074950000e40c242c1d2180c021034405002403005000300140603400c1c00700c01d4000047c503000300d000901c2620481030251050074000c6002e9a00415281183c80a2400010480f107080c002c143c10302c48070042903141d000030b6050090341403409484410349035a00b2828240300540c410598000c0030303800564581c003140c605001d8000400b1440c1c01947c2e400c01903881d48078480301e60031614000849002800c1c09459003070341c0c507151030070142005122035851204a078000c1e8045a820349858006000c1802c2c07181d800344540070705a4040d502410102e5000300c1c20100503880d1440b407000030390117010a407604200405460002e0380140414200540d00d9a41c0b544448a02c84141c8500c200154501d80300e01d640c0c03440c1c1d106540300d00000e0007218041c4403003c0050040d5600441d16040b140e0001b40306030f0710490080009590341494807660107002000408090503e81292906000c14403041d96181203006503030849000f480aa02181d400603242405117510160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 54281694 1250 54280444 54280493
    0x301030b0c160303050f0109090f0b04060b0301020f120a0207020105070f030507020d0501050a0b03120d050c0c030f1e12070309050a08040909020a0e07020607050a020307020405070323040519 84
    0x4250f055000507014941c560301182507030303884207004c0d000c89400d274001410605a0400c03220204002110094005004801c089a41d000b03940c080303802d83c1d0201c4201001d507000003820150752012420115000807820006502d0000c039600024000e006140c0c018051b440b44031080000c041c050402c0701c4400b07a0151920115040c1824518001c08040b91000605410150120041d14012608030824680601e840b8201202d00d4043c400902c4010050100381004001c440c90300801000a8080d2500000315160b8440752446c1c40c0c0b901e00d03100f44840f65008010b0040b0004011110843d0b03500c0142850001448034250400034900201c0200c007071b202000014020440da4041c0e00130f801000d000351040c80c0740315501d8001d880c3c041011200680181c0007407001c83c203841d00c0703034000b094024010320440b030030b00d00d2030380000702100d8050302c0c03c201080c1d80d600d41c03402da107542204201c05031150100d508030600c1c0c5a01c5254480c1e4051111600000b00518103d041068660f5107a085040545204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 54282944 1250 54281694 54281737
    0x1090b21070909050a050106080c070203070b0706090c0902031006050a17090303180c03060601180b030108071a07120302090612090717160501050703030f0c020a060b040606050301030b0c 82
    0xe40040c0b034a0150345056818130001034200710690080c28100d644a40d1000529030358010710031444c0d042200103d9160062036800540680c241000d4985180a004005500101450000d04406491303001c2030b0058018030800500f0003150841ca4122480c1d820155906c901501c01159a550f0440c044a012802e94050100c1c602001003d1442815800306040f04440d090345610b56900d50405010743c15409140050704d1944030309017000c40e4a110401c0e034101c86846029046154109800207181c0c3c0e03110f52401c004e071019404003e0f0010b001000716614110903500c0791100131404003070160034141c0004030f030341450f1144800c94103001d0000c09600c1d0103040001e561a2101c03580d11034580c2c0c0840342804440b01c0c1d03002045003481e080c11151101c43d05881c180056079103800c6810168181680d40c00c641007445110700408940d032201d603000d8550840c02e403030410100c98603105590301403031510300217004541e044800c50341501d4001041d0310301030380d54525090446c0304420781a40c5010300314005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 54284194 1250 54282944 54282947
    0x2409050402190e010e0904020409020406030210170105010507150e03130303050408010b09010b0d0911060342090613060605120604020310050d020f1e03070b0901090b2107 75
    0x1644420745903a00c40310b043c52030004541c64188200d415a00203811404070b001407402c0d501c020321462000c2c0c40820307019583d40000d28054079075030303a1502080040e200e410b1882a80a10315001d0301c800d08041d4202100c0707440d10020b02c0c041c110090022a5200103404c01020200b06441c3c5000301d00c40c1400c507190b124078006010382c20030b1061007225030034084035208500d081181503041e00c3c10244640e0901a00d1517200000c5c0004000a1703440c200300c0140721103240c40d0540110310810103451a01c542000c00c180226802650842090500c02e00b1030f00321040406000301b09040080031154042a502d50200147c208a94404000255480c0c41c10004419030400b005d001e0645205d0120185944e4190501040e48130881e0701041241c4400301c2803120389030944481c4006070000c0d180440918402001c04d1032882c001060004400c0c40d034401c0501440c00f0400c840c05040740b04402e0781803114440000c0d00e190103900031903403c05004181c02d00c40305003604c41c08048081c512845034050134160320 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 54285444 1250 54284194 54284227
    0x607050d0b0f03120706140702030a08040303090602070c0e09010b0604170f0307050c13060f030b040f020306070201050108160e06060a051210050a060206070e060d09081c050601092409050402 84
    0x119105424400c2c640329107d00e00400502c5420550055854903072448000c0390509002041181810395480c03064000c11040e00c0604001031042001790039460415594801005c0001e01c01c0480e681070001c1d0010b2612200c05642c01c0f2622a80d0035145110350100746402c012101203880c0d002d1002103807010900c440055144440c0e50705903058400300303031403814440550340b190050071010041c42c02d041000506509031a9801400f0f03150100b5005140e0b40003d0030b00500351160070040c0e44960043c81442001d0240e03a40046140c80c84c4103040340307004286510204003d0400d8032414020644017440d034041c0080710b40515074108494914504030110824100345402014043c8103210030201c0c00c0d40c000640240503a0080e2100c00305d0514120421001e903100005000c0d485450f03840201c0001c00140141c0341078000956802c4220840094240460760010141c604001d18900c04000b1141c940b440c0c01d00c0c12a5001201090b23824000b002e03034030909190b102c990814800201224000d01014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 54286694 1250 54285444 54285457
    0xe010906060806040f150e030a0207030203060c09090103061119020a0b01062604050708120403020f0a0b0f0c03070c0e04150c050409020d0917030f090607050d0b0f0312 74
    0x810032980d07458140b500d9a0388021900200f030441c2081c05000810342160b1500c01d402003210020840c1101e0120250550f08200e03100030240e03110000c203004510302402004c0d48004080c5500c4e0030000ca4200180111006100141c40346a0324000400841c1e030080c01c90341a04a0b02850b100c0b900c140c0c0d1002513484500c61000e0720072161075000030525621030782d105000b5500d21408102d0400c40214415000365004d8012642480340200004e41040c0a1201e1140783d40c04116051300d03180795005001080007148070700d51158000801c00d005144010054a0001c041b801e00c01e51507403840b0314041d240d03128443d03028060954925001842d8958101c105200380d204480301411002280028016201c0903152a808210b00303001c10702400f030641e80680411521800c01041600460b151942600c0d008850520708400020400803070078032400076660040d5504006001c24503044030010403a014060301d071105152100c10368031440e40d403043e1071050600020151400c0c000701d407003e01042d0707201b80c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 54287944 1250 54286694 54286703
    0x30306060806010905040b030705090c041403010b0109031b0803120a0b04140106050f071b150504060215090f0d020606040b01020c031903110304120201030b030604021806060d0e0109 80
    0x440100d40c0910030501d2500500c010b844400103641401c0c01c0001424848080d03903058814400d0000341640e90f84e000f81d0080100c0000b8503541c60508022195050f10350a49038020384c10300400140d0f59910605500c02c5940010100b00c8039180b501d18000759a4295008402610011900724200d10f1504101070090410160070044c8442d0401408141c2d013a01c08050711009131000100403282c01a4000c00b100d00c0d80103c0c40b480e204080e07030350800300382c02c040302d00c030300d031110000c00b440f900b0f040380d0849400517168109503007032518101c002036031002e8800075254205000c0000c00d124100c1040030800940d2800141c0d04c030f0051b00f0030020340da008201d03203140c46182000156503480d400400c426011547c00341c0a8010514142c03154401d07607804600403010460801443c1b00703001d0082c00600041c0810001d60068806540001415502c404501e58400d8004500f4080142e0341c0381c202c0c0c1c01c81c4d080c0030a45a441d656010008980e4010304540c1500300717040c0300501103c4481940300c0300c3d00074400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 54289194 1250 54287944 54287951
    0x5010209090f150402030c091e0a061e0c03031e05061306060e090402010c0c030503030a05011706061011030406090f12080f0c070f1502060c0f09010302030402030c040204120303 78
    0x62000700074110506542041600444a003e40030f941404e13002580e01c103806800a502c1c3c4080e5201080e0b41003029100070584600c0912102c000d441d00980720b90090000346001c0e14110000040d40c586403070a50b1000040c080016050b10801d070094020003030b894181042c4000c003e5a007101301000c1c6c8400c039045403140f21102c003039240c4041c85101d544180c034030a03a151b0b28440e40440034090f06800182003681880001595480024042e200c144041c502c19400303140c517818023047c604107581042c1c00002780300000000c1c2d0701c6154000a045607000c0310450306010600b00840080e9090000d0170403a110a000000d40810541d4200401000f150484c04411807200d40e0399485031680e089281d0010104841000300c4000c06245e403002d003206401c02d0702565045540c0b440d150405440300d030700551010044031032494206405000321a4021800000c15250505045515480744255182e19041c5540400440d040d0349003004044043d0030090802c641c2c1d55142e81149410092120086000906 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 54290444 1250 54289194 54289201
    0xf1d060714010f150b1b030705030409150312080402040e0105010b130803040506041701060503010603030f1205010e07030c1701030501021c020a080a0506030a1b060207050d0b2701090501020909 85
    0x1280c8503071000e12501d15481c030002401c1001e05c19580e400144203d030003018482c1c5982d1007600900040003501d00c2407006540c0e491400c01c01106a03103a00e42140d41d602144130301000031550301c148500050009250020300703907032580f0004008200b107051055240d860180041080e17003c440c000d00a007507044e9000c0d00e074581d840050036543e1045000703040d0400d2041c0300c20032940d450300900c040c0c0850413a001288031502c1c0c03000b017401c4440d258015400911070076028a4803d4003c40400704040f2440360610a56040c24400114003201500c200304050707581040114051040000f45030080c4801e48011031540c0d80d0030030a001c0e4004090200c2c03403940150000d1001d840501c21250481c00c281c950280070341e07400c0500c50007480000d1200c2d8250140442d05800039201c009204c0600e03c20000c800c00407410004002c0c0740c105e8580042d07000b1400c0c0c0c04820f011446c82e64806070710200f11490f00304285c08602c3c1e1540c14120703030a810311507503080000c80800c20406401901c00c441d001c1c0c54903041582c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 54291694 1250 54290444 54290471
    0x70f0e03030c0c060310170706030f051003150204031b0609060813020409080c16090605010504030b04081e0406111002270609120106050a090b010f1d06071401 70
    0x20070140760307104950140000d6040340c14640003840e031020036200410b03140c03687c3c0c1d00001d807951003140710fa4616420150007031142c550180f0405080154100d410011460403248000e80c5510900000d407546800d0042000351145c960115809035034816034000b2500c09131025188003030b200b401040040703180d5040c046440c82c401e000180c8181d1120b2051594005c0c25020300000b4070312950165050a400c2002c65961403041292250341030700c610814031940e1030000030328102d0300c440d042181003200410082002c60413803261150050f420081262b80d441001c200b003c00042c3c040c00c11a0100c10104001070817513080712031070100d1032856041e40d50980342809030384103c0c814a0b90030b000700c002040e407241284030300d54004020342c2401345c42030340b80c084c0080c0010358000d942038614060f0303915104140040c0c1400d031060802011703a22018484a5000000a400803030305607091410030903c0c802402e40c17813886685200780c01c1d001034250b5a8a100c1800c0411203034a02800d0b1140560903c44080c0c0c524 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 54292944 1250 54291694 54291697
    0x833030d0e180a0609020c030703020d020601050609040e03040f03050a0c06180b07060b040f0b0406080a0201050405061303020402190f0206010302090115050919061b05100507020f06070f0e0303 85
    0x103002071040784a4011880c040b481e01c4009042201829a9044007040c2c80c400c600c020140340c3c408800075600ca05452030028544034540d1545021504640700412894541c041a6605440c0848011641541010401d031850003580c4c403143e0211902e000000174881c010500d00c03105800388003040b032460b448071011740352060b404c8000c00103000c2c101020021207054501500c0d02c0d42c03203544081401074101780003609541d01100e079000b007503a40d50030400f00d0307180034800c50700104a844090620720405400103415409a84103150250070700181614003590107a02c4040a103500410454035511202c030810220a200e480d01d01c0072030070044050445500000d00c650403280d00500020303450382000020724a00d07004a04180901c1400e01180b8041c0d910900005101c000b8101a412240e2600b40c0042c80740c8500c42c13000c000e4120000390f02010600100310b011003030f01d0851b404900d0341c40c0c0000883c0340070b06108010600e4020a4107105034185e0040d0340804002d62a030b03032001c1050210040540b030b13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 54294194 1250 54292944 54292967
    0x303080901021303060c0e09010b0d062403090c09090602130501051602061605060903030702061605040b09060405120705090115050702040506010507050604060c0f09050d030833030d 80
    0x10700f030220b0010000185c898000e600040ea06140010b00103500e000810b6000ba42a0800121101d01054031542041c5a209560044c824482c00351101c0c00d010005d1f0a200144207180c00030562101d03d5001840300d5103500340d0051450200070480f503101402c1030f000a400120030290b0542c06060005680d40c820340036a00c40504070b1545d803514481b15030030026a5800814100f05201c0c50440c1d40001c02da0520046105607a0800519901e1804880c028205507009114101745003030b1186000c030040d404410b690545503004c07960b80d62407514900003501d9000d030780d1003e5130000381c240c0728511084001c0742c0c9904803881513038040703440e90320784001004c543c03109015400095414000c540143c42c09400440d000301060411514040182c2c896070700b801021503042e2291521440040c60f040c1c1d0052110710707030b25964034169001c2406c100000c2c4010100d0030024040080e6900425044901c0403d81c08c51050001140c000c40760740b900e29100440c0341000428400d02600707a0b1420018058003413004c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 54295444 1250 54294194 54294217
    0x106050307080415060308090a0e0403050304060c0212041503060b0306010e040b0604210308010b03160305060a0b0c0c090c040e010303120b060d091203110a031a0613030308090102 79
    0x1507075a898011100202e00420690301c5030090b160108408030944184c00165001e9907085581d0482c0b201444480b001540c03012803010814070402001c40c0c5d100003a43e4105078007200100c1c00c440e607464200d02e880f00340a955168080f0000e40015526007012004080c41480d84081c0081a60781c03d48010a000840d54140459000d031448400b6292aa01c0203165202c01000035092940ba84c1e001c490006040c4462208500a01d24050a154100035000c0c010003e6400c02465843c12120b04541070200456017000c2c5912040822a0390303943c01c1510000d0700c0711076083c40d00c8000000b0000d07540c41c0303204200790040000c4004218441c100e40c0460f400d030340241e841054a0713403a42e0340440c1c280c0024218402c415550b4400644030360b0b01c0f03600526518400b401d011400420b1400c3c20410340c005c1000800505180c0300346081d40304070140030f40d030040205050001d0f00030441c01c02452910704600c0740b2640031000040403100c005001d030511095a0181d66032100760380d07c00f01e800d401c0b0f100742d20340c00f031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 54296694 1250 54295444 54295447
    0x609180b03100e010915050906090703050c01050a02190c180603020d02060f0403060501121a040209060f030307020303030a020c060c0412150908030a09050d02070e01031b032f0108010605 82
    0x40d152402600415144005030000180751205c90b15050002c4170b800b05419040703a222030a101218030100001c40d00290613001800b4503030b2450f0364041d581e028858140e0b060190100350340018500a00142d402e80d141c8409071000000c1030b14011b0782c1d2500f50b00071003004d2604002d40c0708120345036110b6102540c0c0e010f08182c1501c502a02008442d0300400060b1031704140c200400300c002481c0b40100c500070705281c1c43d0900c038036a10386003801203d0504840c41c2040500c0400b00400341c3d0700c1c055095086034042c1d4004120302d03043c401290461040c0d42019416100010902c98415800da0041070b10020701016141c0c45d0b1280e4140910900c95032156a00d240403c1656501181c581aa03030100840e103a00c1c00200d0170302d240e5a0b07003125042100d47d418025565000392003408014050010f04580d90f20160052500b030200c2ca2011500c1800702401c400c44200e1131212f030020503510716000d1508101101c01c000d54900d0340040c9452060340403032080400c8940c048641d4000c60f5a24141c030055143c0d203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 54297944 1250 54296694 54296713
    0x1b020607030e030d020c0f0d0e040605090f0f09070506121515070b0c090d0305070b1f0905310318030809010c0f0c0f030b010506041508040515010609180b03 69
    0x9101a4100940c03140040c06244060701e010041003008c4000c3c96581e44490101201442c2000200d0b100769100702e002d09034860411500146246c2241d81c0100e4181040550380c81e12a880c82c41d001c2d10f41c002d42c0c7c10820003c0c0b03071504170244403141841180701072902044203c2c000d0a2101d0b0301013440c1e0452140805105000000700c1c2c182406510142000046044c14000d80000d001074660a9040d030126000007068011b118810602640c001d103441d002001c0042c003403481c0f0b08850340501c1804647c55071000840e05142d00e02412050719011254104410101c420101007504150141180451035070304d50310460124030001001200e4201005030308000c59880150b6a200440000b00c0e41601c03040c0000300040d20104002028050b40030340b4500e46420743c078020803079a4040c2c0210344210001d2108001d41d41044000030240550340c901044c06440701d00d080e03464802c4100d001c042e4201a2000070440d241d11a1149048503002e4101c40341101c001d4001408903000d02c10b0300c90f0585c1199050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 54299194 1250 54297944 54297967
    0x1311030d050910030e030703030c120b100c080d11030f01060201050408071403130902040501031d0303010b09060c010f0911060702030d0f11030c0604230307020103051008011b020607030e03 83
    0x11901c1c60f0b0b0070f414089948110985030500b0755000318412400711355a541014181759001455183c40d00e09010104201b4039070301e0014a4103400b101008040140346801c04040040d500255816640c0b04034040c81108a1a481400b09030805c03603a10754407a0f551f03000094420b20500070580901d4200c20542d25010054591815500d014142c4180f14402003000000000200912500510164400603141d50030040014241c0d01d4000418004849400312500c0700d16000c000c5074115000e00446a603610b000030007040b5180134000100c800c6502e0001b00c0303540216590468500a40310b00c00e0008044051800c001c10750046c8207000c2e41684c040070602040034007802c003100c04140541459101c03070070102c90142c6194800c0500030300700e802880a01c01040010307400c84101400020a0501d000744030728486540380200f000180c10992500041a84140521718400103001010024071030440058614101076820f01d02c1000103118003400201064032a100f0001040b4100c4082c5181c03d503160803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 54300444 1250 54299194 54299209
    0x80c030c091809100c0504030309230d03020706030b1206070f050d061d01120b19090204060303030911120d12060909030816090e0402010507060f051311030d0509 71
    0x41e5190060001d0760950107020420003501d201d004284000e2603100401030481058072840d03004001841001d10003400040c1d0021209000d40384c1c42004040311650b0420140c5c920040b00308000d130000d4044054100385940803c4c00000d40700d0f00e0310b092000340250000e000390101140c0620308075400c180701040d0480e100e801c100d20751003c0380c60020300304241480882c2c11503506c0e5105400c446000c0e083c8903031403c90b4000d114014609503090464815082d04c031140703542c0d8000c00f00c81045410501e00d88203010143d008816264000e0001c01c920f075100d16020f401003000110aa500452042d4000e54a2500b0402685580a81e030050210b1140340b44003541c60391042140c3d00744150302e0388004981c3c1c40c1188034008445e4000c1d40d0f40d00b82c90401e00902c4c40901c00f03180c4541e0401c44a0074042c400400c91200c0907801c242d081ca46555202200c0c1400c00081c000d200c0100e00403814902403004003e5840c0d210121140201d0070460421640001c00d0354420781d410b0301d440440c0c0107000f214000c0c42c000c6e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 54301694 1250 54300444 54300457
    0xc030905060403150b0d02042903010b0d0b100b1308010509120406030f0b040906020304030f02011a0603041b17010b03030403050613020d080d050a060503150c0309030d020403060204030210080c030c 87
    0x6c282c4228400305500050596030a04c04403072001e203401c0d0381d103090030158002100c0d042c2010340c02048400c00f00000b10b00c202005075005401e100594021070f0306000030000520040c100030500580303d0421540d8015180c0e02c0d84a18142d5600708800300b100288007140d980280d10b05a00361034031f0305141c400240d02400e142140348100c0e50f5225802d041a03100c034020048400d11a010050381ca00c4c051401a002400d0b810038481160315103000701c1c1c1c07039026460020800740c10071292103460780c0c2c1341e1400300002d4041800e20f09a5114440c000924100280281602a070b0000001e000d9400742c1d2041c90359038041c900c000f5200b50b100d000072a40703c180c104c0300b51107140c3c00500403d81c8094262201216a40880301c0185110703a2841000720300215407140c40080c160850140103800a480900041718101800141e0b40f58000000705d04c80344030410403981d5082c1506000e5450380c0d03407420b00713500039002480181e005802046050744103900c690700d40b80c442d00314005400d055446d010030404041d041103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 54302944 1250 54301694 54301699
    0x907022406010e0a0308030402030106291c0216020102070801021c090326060103050105040506010f1d28080106060f11070e0117070f05030d030513120c030905060403150b 75
    0x20301c01183c441e140e80d0600c1001c0d60294142c0c1d40c0d81d05281c0b041c1403c44201c2c0d0304c120070954008040d0704070f071900d01000f04455800300c8140340c1c484001442d9007803c029404a6061164400518009074042003007245200e42c0c004d07000c2e9000d0315942c8202d9403e0340f103454081c42688070070700b101003000c0e0b20300d0b07002130100d82c0285042c100c8000f480c0d90304680c00d9030054944007540017803001c0062660b4180510780c05402d09a60512103410a00000fa060880b04000c4005201c00c64441c001a40700c00c00701d5115519004040034000461590fa5111608040d210081c81039104000031801d404140210707011079074240c2e50703001203042e501c00407550300071101c1c030b44400c070302408000040c50341d002807003130780605200018100645072a100551404403242e10104624100c6c1384108205d98002c1040320811b80f4900700422a0b85e09c807600d110b440800740100401031000c0455500b14141e2140900c40d000e40300751252400f10f03443c3c4003001694000c0e844000d116040b032803602500e000e1560050348000a02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 54304194 1250 54302944 54302957
    0x1110d05130516090b01050403030e04020a0c12090614030609010308031003120905030f0f0304090b040905010906020304050709060e010b0c42010f090504050304120b0105090702240601 81
    0x1e42d881e2401d118000e10304001c42035440800707000501c0d603071180c0310400c0c109080c600e01e81441c42c0e40141440451542c084d10031076000c1a01c03140b10340180028400e05a1011059442c004c03481c8000d0120f14040c05014001442081c50607080c0d60090101d9003e034100910503403180c0c0c40d5564059090307100030040d15011100c41d0f000000035488010341c1d1001c44c0d041e01c94a030818204018946000c0001d450201c507940715180d880f14114020007120290744e4613000101d4412130b20400304001c1c1609500041140d880e1416000c240441d41e4080c5008a103d8025034048907503400100d000c0c0c4120f4001c0c000b0784000e117001006610302d600002c202034028035090303500a02c919403090010801c070ba50f010b1070056041c0b4a40a810b0314151200c000443e1300085060154101504248211040e000d400f1120340da40740800c0900c40200255001090f0360910004110910f00c1d200625160038801c07a070042d1601004521a5400416404810014480c44d507415415001549052080280000703050080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 54305444 1250 54304194 54304231
    0x50402060706090309062c010e0117041119080303010e0a18030206071211030c1b1902030c010c110103360b1f0e04051218090901110d05 60
    0xc2d07000d03028950340a61607424a02c0d1801d800036083c0b101c805044900091036000d03582d42001e207080c0700c0071046004e2070300d02066a429001a01d80040034203c500c100c0c280700040104000440d201d1141c3c081d4141ca0b204200300301560402a210201e0064070200d80050005201480841c00a03503441a940c42c00031941c440300b00e007503807441810558140c0060b00914200200b0940080b40403070002c1110a0070410038040458051482c040908008401c003c0002c071001003281c0c90071101a03446503c0183c403c4000c040100060720031204074124040d004040018065600500600200310303000060000380080e10700c0114010312032059924442d522880032002c03003400c5000f484800369140342595220040078100300c2d0301040020a806083c02000d001427103242180c0b204c620131280041c075001050b403268504141000b0b201d162005800c1004102407000606140400c400c0c42402d035550100c2e80c40340d2044500303850f000080009440c09c10840e100c1d08586690195900c0600e6000e01c214a54 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 54306694 1250 54305444 54305453
    0xf0e0f040501030b0a1401081b030f0303180706020a08040302060d0906020c010e07080c01090510170c07150b011b030e120d260103120e1207061709100504020607 71
    0x28401e0300240d0f05000000100202040144140500041b110071030200c150304d01170070240c1d00c41c15004200212110624008800d40701080b03180d0300c0b08851400c0e40e03120700d03092040a1040e228500140058410304900248560005c514060010b8000d00f90514003070450302803056561044c500c442c0c1444d0b48225540c0843c9403440585078806001001003618078006040300e10300340161300010b01c15048844011500c0c1c0e00014030004440d0160f49012218100c841c0550304556125021500100c101040000880340c0000400c20740d4841e02d80301c032206284a00010440e03070000c080c00d003c41c40c02c80500a000c414002015919442883c02000c43c219060110307021840341c540c0d85165074099240c011110b5000425050807410804054054020503403207100c8005040c0b00c081c0c00e8924005103480090301c501c19003001c9040c00b038400400403030b00309146075885110344104000a6a41c0c0c0700d50000183c60b860160051201c240100314100c030303801e0044010312002e0422640040104030800014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 54307944 1250 54306694 54306701
    0x20301060902030114090c0d09030525020a1d0c2b061a1e130b0304030206040309140f0f0616050106050f0103140a090c0801020409020414010c030f0e0f04 68
    0x14614054090f0301c035403400d0f42040e0710600b00107116120b01d00795010004c000120b40e0a131343e482c100c00302001c41c0b039101c107050982d9948900480e074007407940c07003000c1408621400840c040701c90b4425164070700f620b680c3d5041080c100701100f04014111a0a0011a89030082500684801d20700341c0f4a83d10740c81640c68042c4075031420a0b0312940850744644041246071507440e90110b41012400c1c1391450035034200701358404402100d0844d241c003003000c109444c445440c0005074015000b0286d00320b1b520300301400e0203035903414102d80440004450840101d1810042018a114884064006030038502c0d601c04100a5030070072036620313400003400e009004030081c0700440000b5030f80c006c0c80001031240c20201403007405001c2d90041d030305040c20640036070400d000540c48583c0c41034448000045141541c82d0a100000b115480040c456001160200e000c1840d680140704a413030319506255640402801910600d2020001a010a5900f0600309000340031384902080514010300d10040402814001003c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 54309194 1250 54307944 54307949
    0x501020c101a06130603090602071203020702040b040b030703080c0f0d0504030506150d0816081c1d03030106050a09030203100f0f06151101020903030a1707080906060402090d02030106 81
    0x1c070748554401c0c2d05071203218042c60340140c09a4a1501d401602614a0300e40b501603c240020503a41702100c00500001c1c2d41520700716030340006180540300e00d441d80200a0b4001d0074043c2d10661030600365882c145424030030984d01d84409006014424a107448802450300800e007034850b1405080c440300d031859414442c00c2d511244c203494450b00c1d40d082d801c10600c1c1850040805203044442c5003807408a42d2002420920030364041804c555500c2c1060081c0ca24080440008045500c04510700b0070304420f0116450011750745c1071082003200c00c2e001038200000140d010361903080e0030401c01030044600c01e070001c04150343d0718140402e5155580d40803900d4440f003030000000050341c80c070103290200024000c0311004681c400c0c0901240d4200181c0030610602815441c06001c46108440c80d0442d081d015649038940090541e40c440a847d03401401c1ca092080110300c540c45640002200c080c000c40a2901801c0320703130014205c65403600180301c000d51182d10340550000f52061084016a801d0288002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 54310444 1250 54309194 54309223
    0xd0c050316080c060a02090a090b010e040501300206160203120c03030f0903130e07030b04050103050604030212130e1003060203150306070e010815121002070b07030b0d0f0501020c 79
    0x640e0b10b440c112140c24644c0141404581500400c64900d041d516031013040306440500500080718041f59005a0701b1030105845250468244400080d40c4070030180c10344140d12040c91440280411126041d105010150000b94400000d20100c8105045440002052440602105c03000c4c50003580011454029040071602544000704011403002916a1a40c0007448032009605015101e030342c0c84601c0525004840441c5a02030000e8100383c0310750800c0f880600d015104000079612410007039200d500c2140c003500988150046814044494003c5402407205204400d00c00da00302025005010000b4208800780b50000c90044040740c10340c4000d5008907200c88030401006455006c0c9070510308010080c40c188075481c0486181070b60489551fa40c0880040035280c45003003030000007034160b082884d4500c41840750082e8800911550b81c0102121809000100311036030380e0b005c8c12410340700705102050700000ba400400740054681011001c041e841b0360009401c20000301c046c81c3c0750403004c509044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 54311694 1250 54310444 54310447
    0x15021204050102090a140f09070219030203070204060e060603040b0a09080a08060103060806091b0303070c23060301031703090a02040c180b04030305041a0705030f2206020d0c05031608 81
    0x21140350240485c4024843c00c02d001100c1c60294001881502074400000e0007030307031403c000603d45442801801201e40c160100c25440c1510707418025070765003111000701d000c1d61a0000c08502d00158000480c450f00005054a00d1507070346a0310190a26406843e03001d9181d02c99503030a001401e800042c280d020361982d90030384a4070b040400102070b20480c0e802101d050300404144041694003207003080e800725100154202514902000c02e10303601c0b90620150815100382400320b000e8440000c5550040d0076444881c004070050320400009100a107c01080c0c409060050005101d520028641c0020b0550a4960210450300480c2c19507001c52000c4001400c0d50f5054000400a828110050910401c41030304060440e903000d807191245008090484000900e4019061f000400f1104400e80c040240c903211840c10050300c000303030001e41d280003e40b90301c190b5041c01c80c0c400d030300c00404440543e4000c000e07800c4070301c80a07620070b52030483c140c4242c00b0130082c9011500c1d40e05000904d86100390f02c40b0303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 54312944 1250 54311694 54311707
    0xb07080703090338150d021f0201060305070f06020307030c02061b010209040e0102030c04210602070302070e010501020c01020a0b06040b1c0501050601081006050a1205130c080304030f15021204050102 88
    0xb04c3c0c0030500d1594804001d1000001e1001503250440c03c440400d42c29035100c3d200340b650b0700028481207444070700003a00e100c84108441a0660640080c4104c4e0b100750121510a62960b0960540c45464040c41e4010380c070030700c0900b0100348100552801c1500180a8500c1c004030300c60320154000304800f1520031a900040c0060450400d48141e584e0900364100840c1181050300c250318151149119001d0039103041e9402041d10030b40349040c0c060150303100008558a80e03040c90080c2d1650030500c0303607030f05c03600da0780700000b401c0d5001103851944414143d000d4030554103a60b48855000b0400307001560007540d034031800d0103640c03240030403624916543c040c40c509802c440d25040b821340d040181500d042000c20070501100303091ba00b440754161000d60401c60303264003641c0700803100d104080e0720700741d00c95040c14280400c40600d407a10407046405107108000da2034981d000142d4a2081d0311000b811100c0500701c05d404950b100140c0c903003012420b107015140c80b11180d40343e5801b1400307541c159802e0b54005400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 54314194 1250 54312944 54313013
    0x303051b030702010c0f030c080f0703060b070c030b060607050d030c02010f0e060906010b0415080915010e04050d02030f0f0d060806101409040206040e130210090303090801060b070807030903 84
    0x1101d103030090700d07040c019005c0c2d44070009c2c1200005030104002200c000c02145e142400382e00244041e0541c504c81c1a21a169420903450b07a1540784410360f00510010701140307440c00c142c07003120b080340d030000c008000300c0c600180220004c00c40e0040b01811556901e000120402d02030154010480b83e00000703011500b4a822158101401070b03001412036103040008100071400c80502181c801d10508001e80c0c2c035911038043d0380c00d01000200c3c05d86582d20350700002c0b903108801c803a454015405001143c850b02c802c074000b039a40e8800d20108422049042c0280921844040b0013002002c0390004042081584d404019140c00380648000100041070701c1e0600ca40000c140c0f100c3c112310811984e24003181031a03008600c061007a400780400c040038000000d5030540380210102440b66010f002d035204808080001407404056000490010b14640000640450140034030030589050311455498000542d0b540f103001c0d803022204805000d0301083c00408159110301900f800701d0504181021044189031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 54315444 1250 54314194 54314207
    0xe010c050a18030b0a09031403090a030c080d020f0301150e01080105040c0c0f030f021b0a030213021e04060f030204081207050708060c181c0305090a0f090e07080d020a0303051b030702010c 83
    0x2122423a90400c0c41085031a4100083d0a240340d80c140c180081c2060450500020600c55004490398641c0006281e510305c03031140e40154100c905584d540c01d010910507504540411144001600007102a801404a850280d011038108965424210b00d01c004035610a05000702c1c1c0d0740f003078010900d440034542701c06405000c0c0021036400c09012000c0079640e400010b004206c0380c00082d0088015021908461206030304a031041000d24075401103200e9486100070495101d4055440090f0a19403039140c01d500a000740e9080e5410440a02002c003070f2044070501940101d2002d40d014800d140d000140d01e541401218040c46034040a650795441e1800c9281c0280c1c442203071725004544201a000000d07007054041090380398180740007039036103032031400048417080360f9001200c4140e00c1400004544030294001300c101c2040c6002c0d10f0100342d45004142c0c4460f40501c00f1009600812105c0000074442e502281d8014030030200b2420740c00b50400e805105820441c0c11a0140c0e40d101044940a50001c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 54316550 1106 54315444 54315467
    0xa140c01050406061a030610021c0305040c1a09090601050d0c1d03060c040b0304060204090617060c030c0d0b030703050307030c060e010c050a18030b0a0903 69
    0x120818000e003020358084410b103107040350000f000c0c041c014030b00c2400d200d4894000c0c1980d43d034806220038200c40902a008500580c074000d200c00d0400c8440c60080403580e5400211890306181003103403000304be0098132114441d82102101c4540c0c0804580e000c0c0710684800900d41c0368400140c905001c0c4141c040c0da030700e0400c408801c150703500094502803050200740504e1130401e4070061503140d68003070f200346180440821003844004401001150468841e003401483c1650b5aa0043e0880f503043e01f01c2c55400c280711403584940301c41000200e0300900c0f86102e141c5141044c0120b41130f94411500138500d095202c50340400b19035000e0050034025500326050360303a40d14107860010710f41c200e144e04c1200c0e01c62602030140c00405052141d58a1540251141890441c40038001c0d10302410b2050800001e21005102000080389800e40d980503001034000815013440302d01c0c010f840b100220 = true := by decide +kernel

theorem cover : BRFrame.Cov 54136694 54316550 := by
  have h0 := BRFrame.cov_init 54136694
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54136694 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 54136694 ≤ n) (h2 : n < 54316550) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
