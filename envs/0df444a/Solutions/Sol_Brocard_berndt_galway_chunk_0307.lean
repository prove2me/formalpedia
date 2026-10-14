-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0307
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:06:28.503577+00:00
-- url     : https://prove2.me/submissions/4cc1df04-30f0-4542-be01-cf886048c269

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 55035974 ≤ n < 55215830 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 55037224 1250 55035974 55035977
    0x1e0509060c0d090902090d12030b0603040c0602120f0d05040804052d030102030702060106030b0a27050a02090310110408060f01080d0801060f03020309010b061902010b0d080a1803061b 81
    0x3503c2c0440c0b81c0d042c0d130003542d0700c0d01744c0509200310301d14132030b140e00140d80341d15501c00003419940c0500d0000d540380c000040d44903034082d40b181c202c000c1c13800000070302d000f560480b411806c01c81441220300b45138000c4101c4d40000141d8401103510341f20342c100160f181c400c031380c031443e404035003445031544e69084600716a5900940c5200164443e000000b410700b070340700171500d05005810410042c44610b00952102e000f540014003064141c54440e13003212818401c80c4503d81d4202c4492440c00030a101c1400760b030781d21104040d03042d81044c0703411000c00c0e601c01a40c0700d1070b00d2043c0c6601c07501484044c050140c8004016400132a519030519802da03484595082c065018030340540d50401490601601059040325410343c0c450b005181e003004100c0c002d410280c03200031595200c0000d900503030b44040180495181020162107602c450400c060700b10380c600f50b41d8501440c0325014490100c1d25210554101c050303a8105072047d20040415640002c80075000104151301e030031808441c400394040c0c01d8103d04103d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 55038474 1250 55037224 55037237
    0x10f0e090a0e060a0c0c120c0501020d09050105070207210201030212070507170c031b0109022206060306050d02040509100e010b0109120b061302070803090a050c0a03031e0509060c0d 80
    0x40304140400e4650000751100466000064140001d040c0d1f5001050b2400c01d01e469540d103070141e542c440c07e90340501e5400010645407140b10b81400710a1095a40014941c001008071924140004c100840d2480d006501d40810f00441825a4040c2e01111454000c80040c981186081e08020306a43c11541c403c0c0c4403005e10100d0301101c03240b5242110710700e9010304021820000c01d94000c001c6014010369051440d501e030703110000144c0310703480d88903200c00d00007040d52055420884506c003120134075400f03041050705191040100380c17269036070082456019180895240c2c1e90440d600c1c9441200340c07040c40700501c0c21011090320041036020306600306090742c49150743c1c3c0c1c0d0717030352048103190001101a214011501c00328a1f1031401e0032181c408054041e4000d0f042c41541d450b141d040d03800c116881e140036001007641004000c001d100150700d420048400168035400c2d034070010840700d56902149581e80b4000d000f924640d00035001c2d1082c00364000c00d0a9600c00000e84081d440b90030040c40c000101e0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 55039724 1250 55038474 55038481
    0x1d0105090f0c0904110a0201060314070e060d020d020306040b1605040636030303020c011104030b07030e0109170c060106140901030203040c030c0f151805010f0e090a0e06 75
    0xe22030452402940e8211401c400740c0c88414656515510410019070b0050780c6003200140419044090000b407280b6030000100146542001c148227503c40040350640d80041d40180070502421036000e0f0007010a803040c0c0030f038920074400f00707448440b00c5e01c0c080e60500c10141040100000d43c590f45205881d0b1040590100302e20f4001540e9071f00580c041d28001c14030401b64020700ca880c03c04074440a01000900300c1c0540411401600c0c0300100350000d5001a40000c1d180403451024051030ba110340c1c00041c40e9181500e19194104411340c090051030400d5103e103002a4400002d42100c0078071604000400082041c400701e000595000b8940e640190058000005a09020b104042c0318120364555640c0344c4000303400114020361004000701d07969070800d280400400d48101030800a4032000d07603107000d04c9041c040d811828104030359200c820070041004c01964030071807641031012500e081c00c005054101408003a1100381d03200344419000500c00d0200700c0591420703002818941c091344107032019a02c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 55040974 1250 55039724 55039729
    0x3040e041e030c110a35030c0a1704080709090201030509010b03030a03150f090b03101509020309010e120405100e060a05030622020a0801060c023003041d0105 70
    0x380340c0310050b01240c10000900301040000002141c60304000740319080381e50701e44010328140c02c07580c211155a01c10121204101160710004a2010750b21200114201036003054416502c00351314800078070b2900c62000e0980c40c0d09020059502510f083c0c0c058560382c0780c5502c1d50b00002d092400061780001d003041c1c0483c072461018407518128a00240145140420241c000d41c080d200800c03201c40101c412140000758140f501e414074000d0f080713001010403200760960405190602c1c0d550840c3c922450a00c3d45407126450b407500300100d9022000150301e0f6036a031004c950042404400f500306a0003019403903100d001e802e00080090386d6080302c09240c090000f038811a460751302914030039007100040024464150203000034540c40380c80101006214150640302051100001d400c4007a120b03008254480d840d608500c44501500a6152005691507250001001416050404000020f900241f00481c401c1c90320307101d01c0219400c088903a16959041000b0704d00790103060001461760424004200352 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 55042224 1250 55040974 55041023
    0x9090216060f200307050702041d010e0312060f0a0306050f061504080312040618150605090403120c050d060308090f121507050403060608060a0e010204050a060c1403040e04 76
    0x42d0010001000d0341c1c904400400307020341c401750140085c40414490000165071f640504004940300e40c8101c060500c07031010890035a0802d81d548100c03504148030004a48000c0c03000e16502100c201c8010808040300d10100f84500c100d60000307040389050204114a420000550328040d4000342c030011211000100041c103a40118000d0548030b4004211000c1000c28000740160024010440020904021144900003001403031040f2050403902403003420143c1c1d6442040300030402520307074101c1c528040d640205640592400d54425950382c94000300014808c2c41540c2c4680c10350702081140e162641002d20164200f041c040348940d400c4502c407121030034661061181701c56428000c6c03a030b410008510f0b1140d508020a10f00810006000000104213980181c01c01084d0150150100d4102038100342d041d03640041e40e1428680c0100010440d613143c003140e54049451b81d01e0410125030b654034000c2924550010881e07554030020402107080701c0d0401d1b8103400b4900c07402961011090403540309294 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 55043474 1250 55042224 55042241
    0x15030709060c0203120301060804110306060604030204091407090b0a0503070e01270f050105010f020c01020d050f090a08011e060e310506060315090c010f09090216060f 74
    0x1168503400308081c500a4420a07440d900c010166030440320040d041c1c0c0410740099111100088182051005001d200301c40045403038030550140440345440f0005c64481d11440c03000902a50391079080c002401004015080241020002d40340c1441d5030704205005401201d90aa10500c0038000000b0b29107000103201d07003203404801040d400b6a182c5009401a518403681e625030000b480034400001410078400c11014000d86400001c965050000061100200c458103500f50f40c01440d640303495a80000da85622138090745090f99982c80d003c001c060710381c0248a01c0b550080480040800d00e002c0c1900040c40c1c00d40c14030044030801c460390124400381c800621803008030310754510116020a8481c04002002c40c0e01480031040c031480318a0344600012085015169500440188066450709006c01c40f59090707468243d8005c1d041070442c1c9512031100346070440c18444030002489003e170040c0349076001000d00c13040454940906504585c00d420350050101e07041031402440f40013008051241410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 55044724 1250 55043474 55043477
    0x5040b0a110c07030f03090b131a0702010c150e0a0501020408010c051801031a060c0a05010507030c020709050403091214010c0f0e0d06060506041412030c0a03050f04091109150307 79
    0x40d50704c0c503281d00c440c5c40d40a0700b042d410801c2c00301d004a0340c800e4000017400504c207080b5a003141d070f81c500783c500600d02c02c1c00c1301d00385644e060421080004d43c0e400080074040e2a0480f0011080c8030041545000078041d614420129010307a100348810300c801075014204540b18031000b48150f101c020006c546a100360380820b0303035107906c20100300019482903112828000800d030307100c40040d20800003e101c0c0c0d000f8190540700c507440382d110101003007000c2c0600d9410110311304080c04041d45030100603454004a0140a004a540e140000d090600c50b00705140100029410380743c198000741403a19014400030380c50000c80d0700304a9002c103450700c54088a000c0a50a80c0d802c0c1656408100708080b04060300300517210b498503001e000c501e030313583c0000510042c0240003662910301001010b00071600380f0965250041d8000348841303081001c0204400c1d0605500d4a402c80d91014403442c605068041c9401011213a890640c40801c0000303c0c40003040b0500040760344514507100031400201610003103544e00c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 55045974 1250 55044724 55044733
    0x6040c09020706061703190f0504050d061b02070e010e041a0901110c030c01060b0405060405090c0c01060e180f0c040f06120f0201081303080c03060102030d05040b0a110c 75
    0x21814035800b40102910400307001c203685980c2c0c542d001c03100c208403903405100c0d0800124524114002400c4c00c0901070350f8103054200003040000540240074512619010700c1084041e68100a126800344403401c5446030982c018503601c0e50000c0d541e43c81360141c0141031401030004900071044000f03080c03082c0d50010124007100c5c1c00441d03030b80c0c0701c9030090324410f055034843d8040803c00007008080d00c03804030400c0007540c54682c10a0360398251480b0350301444100c80100f200707004c10740740c1070112000e980d020746240740c003600c90062007011445800301041e02c2d0752a2031800f24004903100c400c107000307070751a0f10780c0c3e420106400c02d4941ca42c0006403640045601c103090901480c2840c0d008050340c068100e8001800c5a6102c0c0000b1001c03540500840c0c0e4403400b915084110341c3c000305920342005079022100000c0d0001d59001c0d003161005020503102c44004000948160301c2007045a0800210180500c21400c0a1810102c44102542d2180b40306003400f5406c42c0380e140f04000c5d141c0041c42d600040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 55047224 1250 55045974 55045979
    0x1006020105010315091103070603020a030b06090d170f0d05010609080c0f040c0e040f0c020105070c0507030b100302040e0c0f030109020f24040f090c050406050703111906021b06040c 80
    0x148014040c0070422206c1d000186460001d03075505004510040080b070320301590310403444000400300c2e07c0e50852584520004d12002e11603071200709001490a501204601c0c080502e211690f00b2800f8080036581030020000300b00c060824160030042c122921a200c1b101c92131385481c2140e0701c03285e001004541052500402c04941d02e0306400003055000c041c00c0112101e040c032408107040d26603c1d40140703001134a6615040f8203550910820f940880145803941c4200340302d969607034a501852001030401c00204010401c17144074190702c5030003164020410080381d4a0040c00a4450100311585442030150291600890406025651a0540c001c1141c440c1c0d0b400281048040c1c0e003500800010303e135079644a44115440c10340180b002e0100c2070040a0347c5071502e1044000d4a80c5220440100301040c0810000d150f0024103170781c2c000d40d0501300b0a0407413003120000303440e0a8882c044446018101c00c8080c041c494607a004000344e1407600d18004030100e0b0780025aa440000b61002040c405030b0207404c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 55048474 1250 55047224 55047263
    0x40b010c0609081b0102130f030302030d0f020d140a05060f10261e070903080d0c030b03030313020909010c050a05030c0702030601060e040509010c020303150607150510060201050103 80
    0x1c0c01c865106031080f034100381610141c0b14a007610540304404c140e500180b01c1401501000d50704000b01295001440d10702c0c2140d134002d442e030190b08108001c1980741c0b040641c0c1c0c00c04913010358020078400141007000c458281518140603074140c0728a91001c0c41c0c107011401c40c0c10854a4000078080140a011307a0040c00c0c4822905030101c0c955200c144e0700400d61840444024072905409040254003d44510002e001911074600000e4419010301000b00400c00000d601101605c2e100030683c20005941020100150701400c1540a9540e15000010801c070144109084882003180280d0710510aa59100d520b1400c8405144c2d6038070101d00107000848186101d0030003035a112140240c0035050035010750200f464602d003a0030590101c0c0107180b4a60483c102445051341c0311072824004e01c0031110303811000e034503880058000240c10000d411840521740340c01c011074420a0748240c18001910001d81c00600814095618800021420310000307445803050090a050301e4000e0b50381400d45905908 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 55049724 1250 55048474 55048481
    0x203150307060e13090803040b010807060c0308130201050c0114160c0c09021b070303030b0117040c0b0c0f15060411040e0c070f050114070306050406030302070b0c0106080601080c01020c040b010c06 87
    0x4041134164840c820b07003000031016006940103921600f110010b55060003451340c2401a02e030400e4040101e0082007001107640107c00a4000d00d16410701c0c03043c5226800100c8444c4140c0f03004038583d6003452101e60301a284d26481c075205901450024602000810046070a407610301d101500b00c08001c1d506101c004110384c0200b000c1e030300c0d040d00070044d000303d5520a8101149684107801181e074500d01400f0558005410700210102000d44406625040d580c801c0c0903a402d000c0c0000d510000703d0000d422503010000042d022001e80201c50600d1900c07041004000c50032204d50b4056810301a148040003e1841510251502501c8010031544d405140b80f00359002184161a061400301c010800b0400c03e10850f01e00c141c03045500c5d102480d121101801b0f40b4000d5000d58011860034804101103507010a00c50181d40d03101a00681d40c040010515000d801680c021004034020100001000c140015020070254420303020b41d07200c1c000c81e10400040300d240c10440390102c2d1f0b00d0401100001d1542c1e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 55050974 1250 55049724 55049749
    0x1050711030f0c010e070608040209010504050115031a1801051002070e070807050d0e0124060e09190c0207060212042102031609020d0e0303090a0b0907050607060203150307060e 78
    0xf40005480c00c40f0780d2110f807600b10780d07600800100e22920140f2066041445101d40941001d49080c8099450114007040038403024501000301070b66098940a0030038280c1c0b401d0f070912401080700036800c0b0b1010b4a28643c3d0001c0c07240e1071007601100c8a0032419400428034408440c2c2c8444051b24a0355006000e4a00c0e00008250001700304082040300400000c51041ca880181d0200000542c145030103216103680c0010b0081480e08032402c2810800350790f0191201605040036106540c942d2620403032014248008524064807070f061142c500102d0394000b90207401c0b109254201c910b59554103854035494451401056a0300745007201c48041071500204103074030b046c4003604441c0c1038072130404003e0764945a0b0704280342032500000d4a603500001406054030075291000a540b0b03604050012a540745101e003c020300121403c00005d6107410107001d03544c0200409800281d4401103842e01000940c812507841c100e200b02003202e40c8542c1400210303070f4190750791034450601c1d0340c504c0000c00180607180c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 55052224 1250 55050974 55050997
    0x1908030a060302060408100f1401050d0c0e040809030c040603080a0509040b0a03050d0f0804021f0c0b0106050a1403090607030e0a170910180303120b0d050a0b070203030f0c031512060901050711030f 87
    0x14dd100085203030a039094148140d000303034007041c0c8070201503040600b003c00e01380c0e44030b11031820305100748082000c0c1c0c0c040754110221406c01c1c3d0b0369110301c5030104025000e05901c03cbd81c083c2c510700707001007030040c0842da0b01c07202e030306c19680c03d0b08119900d181595010001c0d6000381d000f400c004064009050b02e0000304031040c06504250a03014150703521303415030490982000c000110f0100c0e04034801034204180181c03016110254506501d81a072059a4408000300001e0415866040e120540101400000e041607000140700701c480c4072114161006502210400d802241d840c0550596148107091000310700707a070403001200c89455170314110341503e4145600701c070f000d545075040d41c125036880c816411014482c002030010f40400e404d000d44036000007889401550400c00070045c1102d0852001c560284001c5801034a0741c84400303404402d20384c4000b0309504200e00280b581440345002400300d00c0782444e400280150780e12524215441a400100342074164424044125210781c030402034151503002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 55053474 1250 55052224 55052243
    0x3010b091503070215070f050d020f0705030703030204061d03100504151a0411030f0c0a020a06020714120c0a020f030c03030301060807080601021908030a060302060408100f1401050d 80
    0x3810154a40c642c820703624000560312602c002c1414034400300c03c80341e0160040c240030355141042c04000e805031080b540040c030303000c1d070010f444d0355005964401e84020513004401c50343c40342d08504d0068002d521902030700002c50148540d07070f01050503081e007074014114003030090b01c03808240c41c611401401d00940111942c2900000091400c5120703c04c52403803010141844888003030507030900044135034001d075a08090000308204913010124001f40c50b00b0010340f80e0900d68078440501700300d04060341d42000a21742c0d400043c282c0305111100f52059034508501b0280c0c2d07402c844035103810240e44607210300c0701410380040c0e11000243c50880302243c05076901505844400d140f4500003811603000360455804a82d030700d400d1000f019403059410390320503402e0000380b000200d480340030b00040c07154100003410031a0010000f03076020b0442c1c119400540e8090581916181c480c50410b0b00c4031b035242d1109403040d01e0031003d4407a9100d20b02a03122070680e00591403203107034240400e02c012580c0300d0405494140d039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 55054724 1250 55053474 55053499
    0x70816053d020c040b09040f0b0406060306020307050301090b0306040201091a0d020301060324050315040503091203040812130308030705070f0602030106110d020622020409050307020906060c0303010b09 89
    0x11411801c0700606007a078090101d0300c020000700b100301e40e0341841c4c1c80e0040300c8900403c00000e40d00b0707900c154500d4009050840b1a5501c2c5001805001e49030001042d40e4004020300a456400001a45c1a2004520144901d01a034000d0543d01c101c2110040c4c0000e2b0040000c0040d224001030200140e0f0020342c11a140402416846059a02c00e0b402280002e0f0b807401d540c1c0e2098003801c11100e8550fa4104091905841e08000982d190000041700d02d400003a01c0129042050801c2151602d44026004101504522001f661290003178030a5945600544803000b031145d40e001d044a800c8401800004001410b5458205241d0002070910003030000c02c010200108980e5080e03038218078400c001c0540e496040603001003001c401d1204a030282e41c444440d00a5454000c6552503008001b1022019660710740c0501c12008151200d000e5003261030a00fa203424420040010102d50f0300a9405c80711070b440d10b50501105201c1d0707201e60f0840b80c1043c0014041d0b035202d14010280490000e2041c1a01c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 55055974 1250 55054724 55054819
    0x1c090305011e0e07030c0b032d01050306010911030a02070602092d06030403020606010f210f0606020a030203040e0c1c0209090a0213120c08010e07081605 68
    0x800920549145080b25018007039050b40c94054550000300a2018002c80c41c5503680300010480789014480c43e1101c007000082c0e00010f01c0c583c000c58218510a5150107101301c40c50b0880d05042030141074000c1c0903480021658a072140940035640a484584038a50365440d001000250802c403c1110019001c000d44200c0750b49024a100564070340203125140346100d417003a5140d6111405506004010030300400000c29000b14a40760302440038200790750300141c040c80840349806c01c12011401c5100100e40380149000f15030041e0309401c0030b0b01c0704202c102e0700d80200381d03030b00e0101302e00080040e8230411040c032520480501c42600a2000500c2a0034501c00c00741808560756088203141400d6804580302501d4540344020580181d01b07010218603005003580b41008090080c0200c020b08548070105104102c582c4401030002c0c68414002c0180f200c11400a075180c0c241d910851045c1c9c4280c055200c8032705260307000c0d80210742004000c00c103040c500c2c0c40142c03845100642c01d191503c852030280c40030007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 55057224 1250 55055974 55055981
    0x10141207030c060906030e0a020120120d0b0a05030703020d031808011803270b0711030307050303010f0b0c070e0c0d0e0601050a0e01030803070c020d06020403050a020108090d021c09030501 83
    0x1001c450304d95440e9503083c540024100c8100e60941a0907034041428a00541d030062019030560303a0300404802140301050342d50b4501415241c5402c040c00001032400b81211072644154035913442112000d03000b50741ca0007050758904041c00040e61000a0f820401c1c0001c0c0a41c0b411480703c419480024502e5070742c1c0314121308403018030032452a42e03018001c1030420580d11141c0f020b10403200089010718400650a085001c4006020388110440002989020301034810b05560000707030018103e9a0303031030326854510f40b40d40007032040440070440c0b90341c0850365420751000c0c0e401f511211030003007049515011050140010240010704080c0003001028203004403401462280348900d4020f01c41949048148194980954050040142350038014000600c9450440b03800c20300e40e141034074141ca4140000f8014280c03041000b8145440080d000003001400309203120303200e0003602c03141d40316501c681100c0d031605441d0900d10b005070440740c803141444211a8070700343c5440280c41c021054641701c2d43c425084 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 55058474 1250 55057224 55057229
    0x301051c0c030f0c080105100303030209040608030310050916051602010e03061e06010e030c0d0201020102121302010905010512131401020f0915040308030c07020402070c03080a020610141207030c 86
    0x44141400d03c40140000c8040d00d000811140c0001c100c02c0c9440402088847c0142c08010100341c0c0019080c5010f65654202d940900a5403094076901c5c00c1c400001c40c8050181d100d0180a0003900000070200b0803800f003400e40c8450f0340e803913191410501c150a060590704075101241807113100b00300140c4585040000e140b04407580341c0380c6c46200344208401000d1080080a50307041141400a100c0503880200b24002140000d443c080145001e52006078064000c95280808183e01c04080100d03060341002c03480a414003e0b00c410501c9034840004603503500c42d4a418000000000010034002c564a41400302414000c2c100044079a032030084050036a400703450749102c4020042090442c900e0817001c03141c10562481c5015107050301d1f5a8030002c003400014910851410f001c04c00106646507501200c20305a80617010710300e041d48034078145110b90400c02034600107202d5074002a500b552080103000907500c00303038405600c3d84ca46408000f001c1c5102d08002179940101c110000c0000c42449881c0c02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 55059724 1250 55058474 55058483
    0xe0a0b0412050f0706091e090203190e060601170403020c0613050f03030408060f091204030b04150501050a17010b060a2106180e0c10031509050108030301051c0c03 72
    0xc00e41c400d424010303d03100703960250159503005204108801074100543c6021140080d02101c00320001d103140c000308560300e40c0484007070340c000002c00c0f880e02e4a90b015445100e661003000c100c20801c024400b036030f80404445060101c0c1d001000c00049060034010141c0c404d00c68030460303018074000e20202e0100c1d08107200b01211090790350300600c0f16203090340194402c1311056004506180ca4155042d07a41c2d20081c00000c51943c002d40403c0c50182d0505c1100400101181400d94403952450070144130b0741c1c11070342502d400111001103011001d542c01140d0494100030840500c0d80d040c108503098104445c50100c445650703038414811142c0314800a080c002d5030f40d840d040545601c01c0001c3c5d1042103c2121440c00e03501d030038000d0092100450110480500c1d0301d800098440010f0203061410400629490348003103040c0403458515855000a49890b016012580710140d58101c1a07040c1c035070030b001c2e00e0034641007880107000c0703400c205c10b06141d182000100d0150092450710b5070303c0c41c1142c0e50025603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 55060974 1250 55059724 55059749
    0x504020706020706060b0306030c060f0a08061c0302060a0b04022b0b09040503030103020f01020d02063705010807080a02011407020d0c0803030402090c040806070818010f050a06060512070e0a0b04 86
    0x542d45401d00c50ae006d0203109580403441c10000c40c051058a2043c0030b90320f030038051802c01207003090325044170718000e5090400e540c58510301c582c01e001e90f50326030032134401c1441420020020401d0a1500176207815404c3d00384160355803105030050594085000d180c524555959186035030081e130311080390078001c0340100065540c035410b500500c680040d19909490655212040c1c52020355030020f10320340e10510b01d50012500e89480000c1452a039100303060b82d0003900e00d03003c0c0c9140444880e40319504a42400044904041da00d103034164a4000f100c601901142028942c1018680803d0043c0b0700306200800950803040349035500000040d59410614a561000c81004118181b1040c000c0c2c010804e098828105840c3c1411075542d500d00900c560100600352010504c180207100d1158030003180781c1c00074006001404030a10040004640414280d4245400002d1f014080d10488200282201840000740e607921010341d03995104045994001c070400d100080c444074070780090800f41c80c1031203505 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 55062224 1250 55060974 55060981
    0x230706090b070c0c03080903070b0c01020a02060708010f0308090f060a0801080c01030203130f0201020a060f0903020c0603160f020f0102180f03070819030203071205030108070b0301050a0504020706020706060b03 93
    0xc0403000c070000c002c10103218041101e440400c44e68130f40d140440758000d40301b80c2d03240c41180120b410f001840c1c0c131017034071040d006c01d6042c0b40c4803040d0090400519141d003101ea841e62021012a0042401e108148404074107550500101e81c81d44018680f039107014201480030181d10b0701207005c1d94040c0210100059041c001405541410b1240500c90701003460305500f98101844117100002d81040b0040400f503418444c0f0381164000e001c9080206c0c0c03c04010000000d00c0d0180c84050410480124014021104081c2d41890f0010039070303005004101c10380f09102d044080a0301c5407600001e1940c154424800c41805041c424002800414100f180100c440f41055042c013241425850340c85101381c002400501c070010000800212503003000c0304074035100005003000e9040d440780203405000a00d800946100840d04080114120780c041030407905469541c003402e1540d40020300541c1e51020800c80100300c0c034500b58002d0f0003082d0080c0d00c014540511680c0f16812945254030444202d1303804401c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 55063474 1250 55062224 55062233
    0x60403080a09060203070201050928080615012105070504030f110a05040e0d180905010f05030c031b0603070917010b04200304080c0705090903030907060c02010c0323070609 76
    0x2103000410f400e00055080c0092580003074414000c021603d0700030100004c040c40c4500d001a4200c2658030302080f851501e50703c0e00c4006480c0c020490340403010410b4504000c4840d485007505040e4480210150320741806c4c1d003c09a8003900015068204118080c0004000f0074504c4021800f110f10809407100301071080d005018a408060340a544154500700c00b14412150205281400304024607080342050545e07030354505020215002041c80d0751400c40007040c0d203010030403580c00760f030b408070111303103031501c1e51010103586032620f03035161032016940d20240703140c3d060140c00395030010708900f001c0d03100540710034024001b018400c00001603603440e50180469400e00344036405441c44800d6000c044920002c0000402d80300c0604020314401000441d00b1064034148002d90103003134028160025800c0103071101da544e0b04203562540c0c060260880016440303025082d420100d95060316a01c0308100580c506851956800c00e6041e100ca551040881c284241d0320001e01660340304200009414801d804d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 55064724 1250 55063474 55063487
    0x3030d090303050f0c0d0e0708070e01030c0e041e08070b070c0b1605040501050c0a02090f0a0e01020a0801090f0f240906050f0d030e030304230d0b0a021305060403080a 74
    0x2c44c0f401103043c0a072807000d0901300c4080144078640410703103201c6410103616022090703000ca01c160007002000710b840c101d101101340c102d9000360100207007039494040801a50806030380c001e000030781120208007510645040542490b005071055410800e0940b900c00350ba480860b0840f0008a81e0840e260030004502000b07074000c0c0f9425a2216842d008510240192040f40220b41c1481400f20b50340704450000c0280020340d40d40a0803410540c200218441140441562400c842c07a081c0102c010079680148251034031000310760740c0e68801d640b81c030740400c00902c0c0456641a010b40c683d6008410700c046400383c1210360b4114240880003481c0030802d912000015000f002d00141402000c11159580ea8070141403442c00f103c003c0c911903a0352074241e40d080a803901040d0580004100010102e065000740b0503c0070b01e80350400707841c3d0b40d000b040044910100c0c00c002c007245090400b180030030501d0b41c06021035011140d150307140c10b41c44400240094002e0380c0212446100024801d022551015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 55065974 1250 55064724 55064731
    0x405010e0106030e1203061c061b0207060e0d03030209010e0916030b0105040e070503060d0b070e0109060e030709021c090602030610110c04150b0304060603030305060f0a030b07020a0203030d09030305 88
    0x406844c09904400482170203201c003902c1c1501c01d0141590304180110039095916109030310280400210251000012441204450140c05805180000655540a40c0d00d0411a4030020004203400a0302c0d6003d500a40103022024100080240024025207886070018040d00180c03074181c10f0440a00b0005080d1041011040c0c108003050004125404804040340e40048142c1005604c9540d004089281c2c00210000904243c002800780b0104075000341900c0a00c18083e42c2d0990b2a13601c4003401d0340c00d50038015500c3e0705548440000c200449150340501002100641c1707a41c0c0070001608004143c55502070140c0d0f801e0b50000a00c411842d00d480030200d250014100088141e9a142d44107840c2c04a111410340120b451381500c54603240c44600750005012011402910b0b41004c4c100440246240d01045011a20b0030b00494103500c0c01c4000395104010003480302110394103580d501c042010b0081c01c2d05055126085a110040c0c1e0103001406400c409001c0008840703001e0f0900070155503014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 55067224 1250 55065974 55066001
    0xd030e040f020f16140303040b0f0c03040b16110d0203090a0f03051908040e0403020a060c02031306050f04030203030703080a0605040c050702120c0a090903030b06031003021e0405010e010603 84
    0x4200c0740f03d4a240d40010780c0c05040401c20110058070a0b03040c2507000aa0100c1d034603c4601000003000100171001e00824054100312919041c0386e0307228100b00116100990b006082000d42d1400034520034020b62407107041d0700d070a01e400e00140c07581c098540d1405415a440201503040401c00382d04904103007421b40010501d040e0440f030344628684034203440750700c945041d0510303041c000008818031048000f120000c000e01069100c142c6064100252034100211089415500b04901550024400004e681d074650041146ca1403041c5000410348a55010025915503090248000805a07400340094108107000307481e14056032404000380da003210390a401142c032440c42c020000001035800740c1560002e9505592100243c50214407962070704a8000c540341e802004141c02082004484d00156a4240309490601c44601c2c2075007005840d00048071150300241c1c110300c08102514008800340b0b440821588805000c008a0011500f5030b14240c0140818141c201700401415900d403040c0280003508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 55068474 1250 55067224 55067227
    0x50c04230c0a2102090303040609050301050907150c02210708190c051c0506010902090f1e0103050c0d05070917010c0e060f0c03070c030b01060c0305071707020d030e040f02 76
    0x1c1e008040d01591420f29000303a9404804004800c0101660440f00c0101c801021252100d90702c0000911020350703401840e002e942881c000c6030000000062020996601d80d0410786032a40c07144023219402c071220426680202c081c032008a0188001118042039408203018200c06130910340341d146048081e40c3c545058010581544010501c039151803401d440049807035039003140141111070040308403203602500790301a560000407810104da0042c59049401d645c2c1c6e1442085038020030914006101400300308050002c8203030340a40c401d503c2142c0c041d85200c2400e0419042c12081011a03000b211100e0200320f82b13031802d0101e000c0e00043c0c15400c0361780074000d01282100000c010801c0084d000c142d8005c140c085159445007024105590004610104494640503076052555881b0a90720080d100000090004620329110300314040c1c0b40764140c2c035924904041d50f03030b401c1520740341140311041c01407043c007017140141d03109214094464040e54580729642103403800c001c02c0740d60100d44080520710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 55069724 1250 55068474 55068487
    0x90e0108060105010c1a09060f180601030209060616050607020709020306061828090c0203091c03020705090403030c0f0305160e030304050a150206090102070c050d050c04230c 77
    0x1001074018150f600038030300050584890318200606541002c219104107544000300005c203000020024402e02c01c2c0c41d00b60900351110300b001268091500302c1c51035241c100e03c00520260515100d01d45d08254050301c0c4e203150509506500788a0700711030300200c480303402010501c00c0c400e80c10440f85025100c1800110b103103003480740000340b540c0300d88a02c0100550307505000078029582c4e031078489400090060141003c080300e202501501505010700c650035450810301d014414400026034a800d0400782c004078114511030040c00082c1000c17041101144209040402c0c2c94030380c0c103a0b15006900c40d44001c00c05401801c0094882410340c4129001c241ca400f003009000918000e264540c2401804d02100201341c005c042070179449581c000c40c2e04003085803070001d480d218101e40c0d2810800c1641c01e0740d040d601c507115940e00b40e120b14900544046015201803015142080101d001c142c4500700b120f003902c10b200302140c1500c01940300d000d884c9104000b0312036440a095442e5034030044039002c85144c040d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 55070974 1250 55069724 55069739
    0x1050a0e07020109050f16090b060703050c010207080d050a0e010e030f07060b030a050f0d02010203040312050705070f14010c081b0f07050115060e0609030c0405150406031101090e01 80
    0x411a00c26544001805008101014000e502c90542c182d009000c0c0c6480700000380e04075550f50310011404089058040c0002001d00507845240042e0348020080f500d0300d856a142200e0740e402010150003d550700f00181400148054000c108441c0264004038440c540890f40340221120351074000350607410810800c400005c04030855902e0404039603240d85681145c113091008080005c410340e0148640c2c4026014400001000341c003040c1100110344803144921001ca003070b80019240100440d101011003100c400b040d4100a0b80b000369864400c1c20440703543c444104820001e203003030710034060703181708146c83c03203001c2c016441c4102c50b0342000c4102e4101080807045103400700802c07607241d2001084d0207a501c0240d004648029822400034040c96801c0380202d1042050344c40b820011403020326101e1050f00f4042c3c01d88030314500c000c1c05491034481200502c405440000c261a2080ca103801c0d4405441d5103600c00c48000d035001d698000008100c039000504039800503003003913803034820381401000900b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 55072224 1250 55070974 55070989
    0x51c05040c030c2c0a0b1509121f020703111504020901080a02060d05070207030206070302010204140405090309090603250311010e0310110d1109010306050a080706031d060405030c060f0105 83
    0x2030f010300041302d1969031a000560000c1418004240e40101100034001000c12181d018202411003220f0f05c90300c2c510716482855803141e00c240d5651801320a032042c48220340c2c450303010f044201d0080c103142c6032942c444030300d040c20690760b4468100200c04020a11040d07003889801e003070250043c0c0c001091b540809400140d02802000d28014040c0c0e181c4000030060307032003808400002c541c0038002d81e0702c82400c0e00d00a40030750483d0090700d00141c0d80c000b0030780c4246000c0c041e0b140591901d5000c0e5223401030940c20b011190000610540d01071103030348010800c1070f240404050781c0100010107400c2c3c1030309621f80040c0508a90b11403d040100c0380c038982d42c15540c04640c0d86601c0e00c2400001852040d40303010003000340a4494107170710719440c0841344070600d2a034200030140c944c02681c3c2003003a10340356810000321000b0f5000300041035001d403505000240c040e520208003000400e6182d4900300e500040b2030318242003118101c8054101203402e9402001c200700440d0007440e06083c0d07158560608011401a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 55073474 1250 55072224 55072289
    0x50a022802090903040e040503070b09060103110402130b040b0d0b0603010608011502010902060d050f09070b0a1409040903020321060603041203140901060510020f0d051c05040c030c 80
    0x4412000100b000183c04200701d400511104010701d07014901400c001d5107a030800d04040d95000015030000d600e040003c03070310307a060701da201d20081088240d04062000070340022501d1040004102c0001c500d59800c03201030401041c0c1840c500e03aa980d1010b1108042d90422080140607060074030046c4001d07030f000300d04c01d815181c148142d4070680c000858101d024010070600070350450000240c001645410f90401841468081105071558541d0007606594692620504007504000c1c03040302d0340702c2e00ca60812038003110030060460902235060002012605048001c401680c40015140d0101d40300b01c00c100c840c0d89200c4c40344180d514114002c9092484000d00007044400403132650800240070b50700208144185404e611100d03d464009a4001c12044c05100d202d80501c1c06000401c03031001440d82007881c9003a0181a04204080040c1d80c02e42100c00803003e495001080151034a840e03201741c510843c01402445601440c5080c01e00c6e040507960401d41e0030030901845c000c8404d0350761703a0b11001d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 55074724 1250 55073474 55073479
    0x9060e0f060903070b030a02070b010806070f0f0201060b0d020301080c0901030f0206030604090f06050a18050307020922030513050a08030909060a080706020f0d0905030706080403020a12050a022802 87
    0x6480b0054800607082403a1a049050385e0310020040c007102c0039184d4050000f0620031022080a641c0b00c10055603150401c072054800601040004000715114450f500c400a0240c00041000e50300c4400d21100382d007100d882c40c20f10640c088010044910208404a2041c9081d0361100d1954119200d000f54200f00d4480a8042c2e0400004139200d604c443e800f06021540001c0f0f00c5007000c41c01e1500c40e01501050b10501401c9041c0410410a04045d1584800c820780c070a005610b0101240d0a200382c01400a10501c90001041e00a98903e00440040060342c0d00ca942d4003030365200c080c09101c01d002043d401c054060203c559040c00b43d003e00008a90b41c8a00c1198804000d64030140001c09000709074001807664015104002000340c0c0020381400354206100c00da51050900000883d8444407034450541c1c507501c000d00401c060b138003900f002c2c0d070058040d105581c00801c042d00c40781e05e142c800310000400140c00082440503035030f05100c100c00714040555070b8900f40e100542088010940e44601a1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 55075974 1250 55074724 55074727
    0x206010b0a0e2107052b02030f030703090602070b03060904060e0a05010e07050103050c0f0304030c03020c06180f0315180c090a02030403080a050f0408091306080601050109060e0f06 80
    0x400240609101c404804000f401d9100c00030f075030700c411081000c04860668440c800c0030703000b16403481c02c500781c4d04c0200c0c0d0301464551207032040c280408200102c8003003031380c16000d154102c0950a0042c401014064000d81b543c0e51201c2c50000003d00e4035580c0d6121395080309091040c04103640d81c468031250090b41100340442d80f900c62070007c508000d0f00d00c000802540c41c08516281c0404045030702e400b11002600e081109a88080303e0351130314031402e0068210010100005000030340541d2400300d0309806407048a08400b809400b05401b94800c131600051045003407002c031000c0c505000c0c00c07400d101c810740c041d054500222030502060f03503018200c112015080103000e400250100001d40e0045c2008001140a040c200c0c903000c0250b00c2074905034006480380c40010b80a03a03660140304e0003001d41403d85020340d40d45031616100c0d600160358596112462a01d210306107155800b41001404c3c0000c042d015035490b00d00090200083c5030b21140c1400703900b4801a005545803070a262003a0710a84905 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 55077224 1250 55075974 55075987
    0x18060806131d2b091a0f040b03040c0302120a230c2713080301050f04020c060702060126250b03130201090902030f04060e03040513050a06090902010206010b 69
    0x1c094407810750740842141d00c81c5503114a00d41240f00c0003c40380c515944032004520000d15801c8071507005600a0080420001c2ca00c488040c100303100038020740d40394010080c1031170f0f2a84401e40455106550559064281100030f10075842d020010203101c0b140c80006040c01c500b203070744011f1110000052804c1305007581e05c1041c808181400b0402d145e950050691950f0040901c03524040c410f0303207094030101c040100c00100c031300418214081c040d03034010060b0ba085030328002c200400c1c00744000e210b03500581c00b0b00c0b402d000302d00200702c1c1c0b50050150740c000d80055810112100202d081d94000c000403240e044006058030240898030180c0002195110040200701c0c4030030601d29103c2d0b0b84040c1c1c9d03000000042102000080c008180f4103803007640d0b6000c8690352199014103074081580d000b01d0140424010a00280c00303980650382c0c40c1c00c2401602d00b829520800603c004122608030703084c1a4560701000a48130341d51240a0241070740e0041005a200c4d40d4000030341d14171050103002040880061403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 55078474 1250 55077224 55077251
    0x5040e0402151e0d0608070b040905070c060903020d0e0103150504090602090904030206042906040209030705060d020406110d0f08090c0306040f0210030528020f0a1806080613 77
    0x858541d03050f528032000883c8140000c1e544294482c0000c5a030031403030310201094958000c038003101100c0346039158a0429081c000614018900904484180810902403500042c0307103004440d030041c00b9401900d0300c0030744200050b01e48904000e09a04040c94102039403a001c091180803425220142d1780061000724078a403c1000784240343c900b5500480120802c0b08141e80010154402c91041826001c12441c0382070340a4a00d04094800800c136030804001406828951702404810100404032040c1030365500100703030103500242a005501c5d400050500030607821041c01119594100001c2c200c2c4541c101000348100003400c14078080240810118240180400022801810040a172444c0d400c1524065041d00d5420380102e004078510035206142500a1040e544102201c0d580c1d08800c8810701c58115400b80006200c100003a401c0c00200540d2182c040584800e403020f85600150790101284060719100c0d0398410420071076890100901c1d62502607064242c030b540c00d0360200b50144102d18 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 55079724 1250 55078474 55078477
    0x20102120c0a020a080d02030301030b0402030a0b0406060807061b060c050d0c030c14070b040b0c070503120108120301140103050a0e1903030f0905060402090702070e0414010c05040e040215 83
    0x30031146101010801d010410400304940400ca4400c441002804e40d984484684a035254050031016800c20720041002c1a120220b99510a10040c10360b03801c94081c1d501d488544206440c165041d90b0f40d4941070011031030070415200689182d04100c45290311107802c000302131208580042450b907c1c0c544507100c0a0180c03041d0355039040c640005002c55185814010020001a0302a8000030250381c244080d52403882d04070b42c60030340c0042d401101c6581d940c6594400e030700054021130300c00383d0410000010a0b0140043c0c000401e202c3e50398072040d4580b0b046240f0b03003070200c02c0401709a2000c000402c150040c011341c402000d802030074041780035030f10400d40720001c0c190280d000703480f8045e080040700146081d100c015a401e103e610200181d114510035072080b11564240100198401c0002c54054030785031810307030b0780410144102d035410b64442c03481c94404041900d007107400303001e00942e001e0700079028007031884503044610340030b41040e00c0c10180d212142d82c0a44041d000710400810740d602c0703005040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 55080974 1250 55079724 55079743
    0x9150a0903050a06050402040c030902060d0504150606090e09030a050d0f0b04020708070b1b07061a040c0203040e1f120203100213050f041b050c010e2b02010c1b020102 74
    0x20984100f210740b4106034010f00713400c0318101e01c00c500c4c0c289243d01c464040c0c4601442c0c2070f00a8005030400140030004402004082c20969541c10000704054551103140202c0003e0456070380d40d02c0210b0701c0d01400100d6040d001d482c00705180c000b80b1000340d8250b84102a88e1a00d20f111001180024047d081e43e001809070046141c0c010740002044801c1c02544001001c0381072144240039116030707811109510865850303842c50003069080214601144590700001e0300a52281028692800300038001000c54001c52450030141c1c1000c181000001380791b009440d1b100a500e444003000c9101503030852030000c0c0500400c50188500c05089040d9141000004880150035004640c0e41180c0050450303814150b100d4144501550511101e403810103000740c10308540c9684c1c01e0a00408040c01c255615001381c002000a9981d40b495070284020803ca903e020b400f03080403a4064200c8545102080307582d419200c8103680c102040641100e9101c0881d40c0c0821201c07040614501007440100d09003844031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 55082224 1250 55080974 55080983
    0x7030c1b050d1103060a0b01020d030f020f0a020607140403020102060601080702100608250b07240903080402040506010e01020d120e03030c0406030606090b071203060305010c0f0e01020309150a0903 87
    0x245084800c100803000d01c0f44010400704d0403140d865580310392142c00d0780c00d40004180182c002d5141c00e0111806508805030071011054003508049528004001d203070411550040142e0152050051850b0484221000c1c03420044c88d4515250451300041e5a07020f007d0481e0b81000201000100f0452090060800d8400d00c1c2c202881b26a5030f825095568281840c0181070032040b1410002d40c1008031800c030f104441c0b0400034a801c0c81510b44481461203101d96000322000701214101045600c0c51040030b101c98400d859110703060801e8018482240e00080819051090300401e00c032050381c0001c1c180c03c201c28180380486101460603001e41c0504486c42c141c400b10710010050203180d03000302c8058401d807801503404103e41551950215003140b0240300d80104000f08021402c04958280c40381382c81c078039103401c000c1a05940c2e56582421502c0d078080c1e4100060015141200c420350041104080d500300344015402c00c14013000042c203010006007241c02170034000460407000b5000714580390045800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 55083474 1250 55082224 55082239
    0x10b070206190f08061801090504080c03070b010303080a05090307140708120403150501050607030c03030b0604140405090607021209031c02030a020115060906080402150408010605090c07030c1b05 86
    0x14140003400d0400d00606030f60108004c800061250705281c0da2031001e90f55004009035640e407030602c03140000e240183c404d0796803031410001400f501d1401c00007030081e0380c444c00d0501015032560070018826400a40320300b082c54189002e000c100c80c00003061b2002540c00144d20a81c2030b1042c032505103001019484200d05019444858417400071810107003003200d018003601c0e0009022040f0a4080398400d018142d0b202d1814010000070130710035401070700307224800c0c14000790116220b000a2290b42140d48401141c1c1d40d840300c2c000c00e0f41010b0192036082200c0000030000390800f100e010b500c80801880c0c0b442000303000300d55010659000c00c10708407031068003032030f0088681307110301c000b91254002d00104015608040f060891074002d900c00e14225411030b500d807070a0341c0c20144108c8061002402c1a41d1003004100c162000d20032180080005185e641c000058039880e150504c60700e040000c095440400080c02004086034002c01c03619846948000902001380c15103001d0a180006a0410b40e0407612 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 55084724 1250 55083474 55083517
    0x60f090a0c0e040c080c0a03140a02070312050411010302070f02060a0807080121080d0b0a150909140c2812060806040c030b07020c03011104030201090e010e010b070206 74
    0x1960301101c034118480d907507101c44440c81c8080c0020f54034105030450004136a80f00081850b1448005841c0c034541514020403404d0001c1302d64102981c040ea11341c1d070038a80c00152641010303000710b0718a20101c1c0c1a0300a1001d45499121455103090185609041c5a00010314000704081e81c09030003200355004210315110340005800a25020040310740101080160300045a268441d00d030645c02c40002e1000358007441e009940d5048a5008203008850b11a241c0c0d15610295865100081c041d02094232440c890503400c000050052a15070300c02c4803414500030040d061510005010f030351100482c0996aa1400380311380811400c4807000c8801d08034000c1c065a03000556204c0c06030101c45c140c009051245a0700d40c0050350f2582c0040c0d500402d6400040b50400c001440560002c0d031250990060b40c040628403404642540d03440c507035002198400041c00e0003190b8222011101a200720790b0303980903660412448600301c1c00103015111104401081200455441f14111a1400500a80c0e54000e07007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 55085974 1250 55084724 55084741
    0x705090d060e0607090b03010f092c0f0d05120402040225031205011505030406050703062d1e09020c010213030b0a11090d020f0a0b0f040609060201020f12060f09 71
    0x440540d021300009042100c002440701d00c0c0e5003502d0680d2424103409021928200b45600100846c44a40d07252213004511078071541c0c18401c129880800400c040e000c900c109072603030340c10b00001c54480d030140b203024031910b0172480703014003010b900c9503040d035005a40c1c110741701c0710800c1c0e040008582d00d41c3d82c00a000342820103901203003007141da2a9004040c042645ca509521440c0c40390f0030700b0315001440c284001404a1401d0700010b0304000a418002501a11816003c1a104038220011203550010304401c03000701080c0c201d88000c0c24080d0030240d99003411507410030501014030500f10000c0d0085484180b1410031b5040f162070300030308815603080c0b55407403424184000013105d241c03520303528140c29100c513181e0703403400c913a0309103070082480968031410b50800000c50715a049280d0007010314000828501c01c2799000700300b425826440340380c981e840d010300107040d8074580c1c0001c4216401884480e0500000e031060714030700c8059064442841c1e40c2c0c0d0000c07404603030b0700115a50b4000c4c8031005020984 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 55087224 1250 55085974 55085983
    0xb070302010b01111e01090b24060f0703080a090c080307020109140a030b070e0a17060a0c120216020d0303090b09030403082b0606030506030d0806030a0206031e0f061c0b0705090d060e 81
    0x88000490484016140360100410b2f0300810b100d61320842020070082001900c2110500e03441354003040001100b211513101c080d1007548031f03040010720303a20009030f110542d80c2002c02ea4000301000940c8281d241146004074400c0071080c0300c0108440525400b01700f41501504903112000300c094621200f1075650a0f81c40003c0e5052407002009002e400c02145400009000e29043c0d041c407a241c2c1c03401300300c005407440003d40c012504004030728441c411800c01655169040038130b1a000ba500032401d40320a05010000c1d110141c4a20500c1d0300c108020000141490b080e00c10429243c1c2e200c2600c2010b189400707111803005100b03403205a1900002081c01030b00b507407000b402000168100d800ca0b40005038240c1d0340c41020303a6403130740c07684c020300d00900145811401554840390180f040e00304001950041c1084490540b114a81580c8220401001d42084010620105081e01d402030120b41952a43c034142440500400c0030070070001240d03107164941e00d03044403006600a000300b01d4442c00f480c040c0d459 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 55088474 1250 55087224 55087261
    0x40e070e100201020c070302060a0306080105010b03060315011d0a11070b090d09290405090103051005070c0f02010e0f15040e07020307020102030a05070218010b070302010b01111e01090b 82
    0x1a41c03020000c0501900c14400c1c0d038200148200240003090035070f020040c190700840b440200f015100c0c40049000b480c2030046500908807000725a440c1d041400426007440d00d4080001c0030404450300400070340d860788035030107030040f071040c0260030640310a0700c3c1d60b01620402140c04070f08000054003204104a0111140c829642007060750090b5900304000c40300320845d8411031042c1380b0070164000784c00640d88203c1030075000300d901c1c02d881c183d40c5801007401102c00368000d540c40e801560b5150140d91b401e00880b5401078442c0350510803100c155039241c488841c0040003070f04100c04061070440b02d8880e40001410724400515a44030020307600b80841d8a40d1241c05445065080305000c244200d000005a501c1d241d0f05801035030030642180c8040703401d900485000c1e644103401c1030148001c05501d0710020301030300000c0c4066503030b10194100a425a951500414104900f0410120301a1004103070780c034001c01c00051044414960042450160900d004c019200c481c4240500440d48040d00e81a0b0380b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 55089724 1250 55088474 55088479
    0xd080f0c070f06050d020c0f0a051c031103040807020307090510051f050417010902180108061005030607030209032a090708010e0a0e0a0606090506040f050129040e070e 74
    0x60312910b5801d1900c61290a105400111300c05001612a080d995005010306030006d404030b5804002c0c44262a1510b0140b07081615030380c110704008030000343d0b11280703074401b680542030512500c0705100d9860450b01c40100080d007c0306011902504643d070a0010000820503100280038030b0a0510004040746c01c0d80c0b090511400d0708070212088116403400f000f9241b000c503101c16040c0fa10b80005211340d00310304c0b08119100e541c2c540c2c10000599846211000341079a03200315900647c10100024036244002e002c80300c940414490030880c56800040071988072000c5e180260700c17810100082440c0410101040b140130040810b01071940c040f076015850900310847d012022900c40002c00e80c0c030a4002e016058000300c04100003180c202c00358007d003951030002300480c0c0740d0746a2512960300302c9a0603001000d045481d40103001103850140540d42d22907c889104001035454801c207030050301c3c0702610312a04038410449080032410100280d40003040034100c82d4440707181502c8000c004481c1c1159040c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 55090974 1250 55089724 55089733
    0xc070501020c03030a0e180a050406050f15060a020102040306050103050c090106140304030f0c0803070e0301050606090105040e0a0207020319021c050a0f05011b05040305010c080f010306020304020d080f0c 90
    0x1515840056050b140d11030103405146803c1e1010021141c0c1064140207035084803203010401c00074114207011a02c20703230000c00002641e003030501c0c03c84191803000e804a01213442200600c01c004014001151010200b01c8215a80300d072007800c1a0701a02039039201a2005182c140000140b00c4045189034100030100c80341001aa202c40c0c09541e0201d4050204840c00020b10000d40003a00403d94001250074905000c0004501c0b56120303c070380c0c0d0040300d5280000706802c1e400c6c10a07003000d01615801c00c104960300d60a044103400000c119000301d2007446200010703400031a28203850360341221011500a4203071204003102c64000804404e4030a4100d0044182800b00b60403080d0302405031922981c4032015003c2010540c407412007100c2c80d004283e030203550390402c80d5240041c00c5c0c1e41070f80406041d164a0380392859824458211054103241c01c0a0002d55810451561a201d4281e815254441d40060b201d844e030380085419015010b41c020170180001504070044a446005049102c12090485 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 55092224 1250 55090974 55090979
    0xc06111c180c03060c05040317090108090705180a090c030f11090408040308180306130c080105010e0f0a02040e010303050405090a06030b0a0c0507022e03060605090d0302010219050c07 81
    0x1000990a1024200c040c41d5901400021354075003000000c0541c0c0e1825604007522500d41030742e0300c080400340800400340052940c8007560000c68040d4400c000001038800b2910708030200e109210601100503440340c0c20300015a008002e0b9016401842d08084d13203d8000b5243d281c0300c0981e901d004002c3da22420085412005490030a100b644102e5129450ba8185841c544d1409103c2e003100807482000070280044070641e403001c1008600c100084542686450302508000c90310104a0304420f13041d904001c01800550800c10080c1d4000d0f11180c07445c412075448600c0400207000f2600504850342c0d03840000001d1585c003002900aa4000700d420403500c1e00d071200001e040758a40d21006080c0481480001d03a210091391203006000c1e418140740f071810110341c1c0018a0301015105144440f41060022015404400968449410181001c008a905085010b4094081c0d808440d10440b50340010b103042510039016100b00c004600d0101d0b000c01c036411805052034024043c082e10030311852500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 55093474 1250 55092224 55092251
    0x602070b0405010905040509211803010506062a0102040f09051e0601030203061801030803040b10290d0e01060501030b04020403022206080322051008070c06111c 71
    0x119002c880c0141c6030340c10b10328500800d102c00781800401c1003815000710070030114401904c1190401054a001d459991450f020340c40c3c00710080010a0b40303019030315100400c040d80d1209800c48007000c108200c00310801c400900e10031511003d20200210a5001140011b8051205107406090f5650342c4030600003a07448900707000300c20310030401c0440b9010010b004112903502990041d60403040180107829020880d841c00d00200c28213a00c202c480e864000100b0041c401e2104083d80c01c00154940402c8241ca001441000c04140c40240c4109401c0001e410f40222621800c6610b0340d03405d40705c2800881c00c4c42280c07034000d00a40c402c040c00300341005420300b00c6140501c01c44080c0c035030041c1280c1243c1d10010901b0200d40c025840c00300ea0a5503018007207014401080500420340380780414000241e5084c1422410380340c6603202d24043c02c1440c80141c01c20350090038580c0c2c00307285032929200c210010304005000c0c00112400303a900400000e10f0741c03686d0480401800c1140c59000c0207100c1d0700c000208 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 55094724 1250 55093474 55093477
    0x13090203010e1606080714031b1e04090c03090b041104021b011505010203031006030b030a08030405210a09060f0306030b07090306050c0f04030311011e050103060b0109061b020103140906010602070b 87
    0x11007c059060420005a040703003100390400802e0003d014003070070061401d4002e50707004070a0380c0f032000c5000082010411600e6031700849517007841c685010302811000d1780e0350150841d00a080280710400c0e890f00e914842c0c84550680b5100d403003801054100001402c07045000300039010942e0310040c00b940c4042011350000040780c2c025501d507102c80310050710b0400c04400502c0d611000c1541406032111403004601031a000c0c5010354020741c0a411400f00c514110200055001141c06d03116400f40714841240b5000300ba8034080304c0e0141403502e03c1d42c0c07007004124014170361600700801d1940c1d4081400071465101c03081e00140c92044034200300c0740d03d0340c1c101e58107540141e20700071030005010001400003922601000241d640e824002140610810440600c142843c410950110b03030741d4001001481268010410303107502c207007802d9004030305181c0002c04041c0148403407042e15030301d148243c0469202ea80310000071221302c0240e4049052514800e0b80342d80c420b106070300c0184500d202c0424581001030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 55095974 1250 55094724 55094747
    0x3010b01021b0303040302030a1b1401050306040c05070b09030301061d0904030e1801060e010e120703020928051006091514280f020c13090203010e16060807 69
    0x1c000302000600c11a03450080004041c00c250940401d100000050320108044c1d0103140c468012000d405400e030381056900f1000d80d206c100c0d03a161a00d100829a40c0080440f0b411001c10381e070128803000320400540d45c0f80701e0640e005203041e04140c100260100084051410b8a040c4d0f644d0001c6804c10604003104880c0c00f5a40c0e0303030301914074008a00024000d0f0031400f143d00c005010701202909145642e06854801d80c09034001c20054520080700703603030003144003e0402007100e40003e80312450651035900c03161030000900610741007000c42d0804180011040e110040240015244449102c182002d018240d030042c003580c41901d004103609000c0c40c00c031001d5078040c4180040c4106010022903c01074541072220150804029003070804030401800030716403403207607100030b84500d4080e8000d2803030b040c1c0002541150000b4020488c0c035a503034103200c2c003800360480d80814914124000680141440c1c0701404e0948182c031204101c00b1a102d0601c03084030000e4a82c0c000c80d91310010156025000d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 55097224 1250 55095974 55095977
    0x11090c030f480f0d05040302190b06010e01050301270209030709090b0903040e0c0a051308030a09081c0c11040903110f06060114030421020a05060a06060c0201081905180c03010b01 79
    0x13440940700032203095010320342c032500070301c101c5000c40707002e405110a072a48280d050303c02450a200700161755030890b824041d441020b00c0c00038610340c5800c0b00b0a88030030300f202942c0017001c6a100c880300d210241d038050b46c18200340141580c000300d0391020307104000d15600008071804d03079220001401030703400031007900d04580300b1080320a1690f4503a0072001099010011007014040300744200c8a000d411010381c2000741160b40019652210500c2000c1d001740c44660200407254044144000d28004120703103001ca0050501f020301010384540f4010000000548041f60403514101c241000e040e8400183d200044c0000c0c00e603041515214001601c170802200c0990100d40400494611200000b0055501034010040304108225000324040b1040310700f400e21005a101451842c10301005000170341d00f05003203e00c1048800d15224024220504402c03010b07050104c5480081c0d0810034542c03a1120102c680d110820540c580030f9031602d900c0f10140c1000c0c1c014030038150840704034201441071042102c0705 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 55098474 1250 55097224 55097227
    0xb09030115210602040305030d0603060b0a06090b09030109050d02060115080105030c010e040b03010903050c070f0503070e0405070f030606061e090e0604180605010311090c030f480f 80
    0x100d41da05150480d00302c40407a0143d0382000001702040060014000d000d454220102d180781c950304245041d51850f000380391060340c1e54041005100c0d001700b6030000715030000320b444d034544107048000b038010007002002034401c1c002c3c0440c4c0414160701003030060689100c0b040f400045040c1030700c229000072003406000e03015400703616500601d600641a107100a140140301140448024001c6801e49a10040803800715a001c2004c044812007440786001414004084201391407070702000ae03030f80c2d4100c0c0c071507034002c08001c0e400305003400810301500d40a4200c80c0680214207680b85042e00050a4621036100019895540c800001c030740b11400014142c15980d0b0107400c0c2d810701010b581c880c9000350580394400e45e03403032a0419031038003580c49154581c040c2c040001d140d0314500308042950366500c4920322600d00e103010072600c1489076040d6a0040400c680040b016900c1800703208500b00e15031000382003a0101c0d00150700001289841450750040d50a07400354000d102c0500b006240034034540100d8000d030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 55099724 1250 55098474 55098509
    0x406050f2404051305030703031a03011107020405150306042604050906150904060b090a0801020708031603141305010b011b0204050406020919140d021c03020a0602040b09030115 78
    0x8183c0c01054208403070f2058a00d20400e2962003500c0c40d0303c10344040b004a81c8803035544030b1030b02c034000380c403000c81034190000e0002e04160244092144510350f4000d104654520114100c401e001d482030f85808405022240e4604041c10f01203054418002035201c5642600c0054000c001030030207a03012613502030b00c0703001c50380c440c03004100300d0881c400c0e00040080750030b204442d1265078031f0007110b0041071540d0026550702865000d1001302e00d50b0341c00ca4241e603030041204100003681881141e5211783d05011450411a640d0b0044029110124002600500346010b200906c00c0c0008540c407400c0c1304000812030b0f40d403494010b440c040441c0000c40d41c82c101e190a20070140c240340d00300a5115124880052400e00b901000611251418034907000c500c1c2009401c3c4451508240b0301d00d00a4003c0316102d1b0401102d50004a0324800c140301001624000c0748000d080600030001d400ca502d0b80608155120ba0b2103075107960711034000d00241f070310941c00d01c3c81081c2241b1100c90320500b501c041d880e1080310b856 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 55100974 1250 55099724 55099729
    0x70f0305030402030a050d030209041505060f0c0304050301020a050a021504050c0103020a030b030601120c08010207020901180e0d0e03070e09060424060f090507050903070504050901090b0406050f24 87
    0x700020000c2c0d070580a243e40c200009041404015030b00036a5440050b110440d20301400101c0e0b420a8628603401040c4109200c3c80e5556000c1d100c42121113951181c1d25101d00d002c8074114041c680c0142d415600100721500c00c20f4201002c2c140d01d0300181d01325440c2c60208072400e40303003000503034010304a43c0141c02140d4455204e600140300503001400d02080f00501c03200402e1030250240e21031189044420496001c22078880d0b40f000082c44884025414682c0d0f0f5000a4111101841001e502d8921050700d5400304c500c0d90001c0b21141d1648090710323303982c000701c405000804030005e0207119000da01d41c0411018030429416019081a03c01490103030b507240c0d69200803c3c0d50800c21510300311b2030000885d14202c02e00a020140041c112103c82076440d0680c2d43c000e0f80c03000750120050103c2800390020303c0d00c0004e1010119001102c011406480d400895401000d030000041d00020102c0204018042c07581c000d00d0140d010a81c1c003903a01da0b120703004241c20843d08000561540310b000201c42107031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 55102224 1250 55100974 55100977
    0xf021305010807090320041b0206060402090a030206030406051005010207080303060d05120a030905010c0918090201090513061d060a090902010512010303020c1f02030f0d0b03070303120b0105070f0305 88
    0x10003607042001d055901c90b26448020365040c1c11b00280c0c03428500c40c10009042c01e000d5143c8014101c01106040901d84101a481d04001000c0c24002c0342d002c030f02500f50f681e400907102c0046030003619681c3d803400c1906002001c0c2400b10341402c030b551900c8500180f80e5200040d25400ca82242c0003650858851b4410001044248201914103100d0f4156092424000c00300401d0301c11101d440004031511646402d03801d40b2110030000e01840500203040120000c41090280c41d0385100200140341034180c80181c8004440c1d0f00070a400c032500c05481c2070307103564682c003200aa82c1102070300014480440c50300ca404440807180942c002c16201e108000c03900c441c0e0403c64040d0f105041450174401410214070030980260b00c250b0040e8061311540809060034000d1200040442d00c010600d010110000380d41c034070401550000d03240001525600700d5929620040702c0ba4030041c1590401c550304e003001001d141042031086500340c5040d00c00c4103d513000e0f404440c41c044d4001901c40718a121074400303503000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 55103474 1250 55102224 55102231
    0x709030605150603190c030c1e11011a01110607050412080403120c02040c0c0803010b09031f0b090109060509281d1005040812040201050f03070507060f0213050108 72
    0x21001d915202c0302166a80760702542c49405805250f2040c2610001e0040585503008004030070f162a003182141c1061f8400e4407446210400e070a110a140251401125070340e1148021004035480c0c64000e20602483c00b40741316005a090741c40400008803251403688480027503449401140d4100010009048200b10800030a80111501420b05540340c4954021140b281b0031500080c0359070034a48110303d02481005040d501c18035016004504c0b81d030711107803144010701078003d140c01c012540c0c0c1442d07501085001400d004070202c60103201c001c48034400245c40c0142c0f159200750401c4001154000551080d901200ca00070403a8880707881d480ea104024034201241180c010351500c0303802400c0702c058010280c205030310307640d0010410706081c401c41c280341c0c200e503e0200c0c450500302840702091803002694210b151200401125484503c01610540320f00c82c0d6840e8003da001c420480b085c0d8100c4040c200c00b038001c00c820b204013040c0d110007404a108051280080001e81c92090001d54495103c4692 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 55104724 1250 55103474 55103491
    0xe0112030f09080d2604030806060903190f06050903070302030702010309020a0e09060601030606180905060117091f1e0506040605040612021206130305030712050a230709030605 78
    0x50a03207030110300b4240020b13044214041000f40c5218142d210034145425039292118030000c07441e0521380e80003840018060481d5202e000c01003807035086603030203200341001c5082214064114003910325107a001002941c4040d13445500d48400544800c00c0841180c0700782c1e80c103502540c6082401e034010750042c00c1804050783c20101242c00881c05401041c1040e00a211201c0205654076003400010180d0350385412000400008110030790122013510902801e540c2c220a0104e01540c0350b0004076810b00032405003002040200c0c0c148012890041171858102107003c03032103040240104080016602c0005091b040603403d02e01c482881640341e88041c0d0803c10041c40030401d55a514005401c2d41d103160011518400c0d01103010045141510314041c88044e90f101400180c981801070011019000308040c0034400000009026144184840e144242c100c1d0000c00031418404829001072801c1903c1d8070660f04041160b20001c8c10442c0c000e840342c0d000b60345809403c1d04558413900075200103000c90700d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 55105974 1250 55104724 55104737
    0x308071b0509072d05120408090d0807030908060c070b0a0609022b0506100f12230912030a09050319030203070909020c0601060516051b0a0e0112030f 66
    0x1c0e0603511841543c0c0079010135034070001803e8404101a4120903c5100100d00e00ea4a483c0a1300c19600301d0241c3c1c1c850f900718410750049540d542051084d80c441c03042915071200c40102e01e4010081d002000d8048140a81c1d514282c041c2c40381800c65035108240c0e10903549600078440d05000680d200d503107a61192007808045901d60b03603440140c3c26a00b100040c1c03280c018014094080e000390000c90b819580003000411711403030904d24081050b03040d00c00c040300704022440003082c5456011701c43c2410b170100c95030342c100184101450260360403241c43c0d541901c5000004045501c0b41000a00842c1600d00c00c408d451860322941d211030024014500f0171211400240400503041d0f45625501c44c0d84543c80e280580c0e68904540c2c0104800c001c4d40200504070b10600c40212200000600b03141510f11508015030303100420300d2101e8603104150030080262154402031010b00030450031466840b0000d0303881c844550303107441024010036000d0050300341010400041501083c42040207a84041d02404c211 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 55107224 1250 55105974 55105979
    0x504050a050f030a0e01022103041a01090b10020a02030705010e01020a0b090705120f03030406090303020f0325110c150c03040b0c1204050607150f0c020a05010c02070308071b 77
    0x15802e2032425900c40220b070f0030114841300144d4000c0118180180c00344013602c0300507001c4480204150304180304400b4003001200180c2088808075250b4100e00203101c60340317100d43c0d44c1c0d07850720050f100c404a010b004083c00c6000141e001d0000a20341c8501303500901030981182000c004446014001030792504500c43d0200341d0020984800140740541d4110000c0c1c80c6003401c2c502440142040da8a03507d0243d8030411406c0040304021054a07000350f07004101040c0f030075030307810b00310302074000e404d04203400030800828000342c0c00d0924100c07182401c0900011008900d0302c0c0080e2010206d20503007200d281c0201e005201d40d4901103e990100e0111b115269081c141300d40f00c1ea514540180d00b100c001d6500c00039040703801010801c00042c9648084554624182c100004202c41c0c3c0540c0c000102400c044101091600041e50021400303100061303010000b5210300c40c03000307513104240c0300305030fa0551a101c00140342d41d101041540c1601d400c02c0f1010f1800c6480d039210300708285a403e01121501c9240000f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 55108474 1250 55107224 55107233
    0x90a0903030b040c02010212011d070e0a05100f08070806030d111002070f030206010801060b040b0a11060903180901150503130b0403090501080a0c090506070219030804030506090f0307060504050a 86
    0x10b109400e48139600058032100c0e1070906002026041c0c001c4014850b500c03090714030390114050342c079500010780d19040e10429881d2003c98074100b076580001354400c0e40d0502d0707001c080380c0c0a524400c0000700b60b5502c0805448003002660180c1c000d84100e03425410841d031045419024040000c6161103020844000740e6040036444200d0b001103004a500c0810b4501505c14550b0410a03070340581413401c001c0000d0b41c03900f00a10541d00c00c900c0f0361500e01c10041002e01006004008070802c000e0928240c4410380f4100c5061512540422120302001020715100b072000d092541e001c5041e10400801ca02059103811000d44a90704028070001c0c040314110303100c0f0001500d5040e1107003e42d22a03100d9581c0795090800141999500420809101e450101c5108440c0e900c003003801c0840e1420f5441c26540c6101d800860b0074000386030f04407a078215690000208000702e01c0010012280108143e40c02500c0d00020682c8170700359036900100c0c1da40280800300106010368489074110b449001101d140204986d038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 55109724 1250 55108474 55108481
    0x60f0e0604080604140105060310090201110a080901120213050402131203051c2003060102070803040e1e0708040213230a0605030c03030d090825030914090a0903030b04 74
    0x2c0030300b41d0014000d001c02c02180c98403202214256400070b2080c2c1c07519401084c0e072803480039810f02000352685003980569000e039103991500c0b01030b0003e540300321900c0d0400c811740d60b200701c0d4100e0001e04400c80c0035207140c0041c03085d1915400e0f2415003070465890003003040702942080c01800300c00751045500281d084130f1840804071591081c1c880ac4d48804003469030702d200f00459503034402554107003100580340b603950140711180c00c044d00c0c031f0719500c030713121600104c0c9044450f40000c041440b001401040c2418021490f511642c110b58221000841c08540400c4101041e900031011403100b50100c0c005242201c6121031510960200003080d00c41e000d0701034090500414403509240f4941e050041e400d880d4061500508400d07802001e18008100c04a82d507031260300c44922078180c0d1400c1c4013040044450845000c902c440f0340e4007426840f083d000102c12520311313400302d001c1042c40b403000911a0403903c40c8444c0e048020a091260345d500d40240c000b8118440c4100d0030541d880d40c940ca1b45942c1c511 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 55110974 1250 55109724 55109729
    0x3090307090501080c0a080d200f070503061008030d09050307120c1103190b060303070501060f1e12060b0d0204060f0812030606160c0510050309010507080103030504060f0e0604 78
    0x10703400b1445516100a507030500d082130624074015460b14a052204200000d01c80540f103c852030200d4601d4104909401340040c107080c001384500550141c0c81d0704420005058042e9103088041c2ea64a0b1984002001c40003103612078001c0d260014440c642900c421540300c1000039000300d0503030b441c012946c1d403458000320507200c5060100d00e517004c1a10910040b0b01b01541d9811054000304124011142d91602a49481c0340080c000e4080200082d4035440a10540d0085980100244045500c41d03e409455003e00d00034038010104940c80040140e804101003422110100c11300c0c03215030080e44802c805810500b12a0b504410601110401610f0714441c160040100d010403c0d800c07814503001034103141c15403c185c200b2290030301c2407150702d40e51001211141160b8a0520b034405045107003c4001800c2a800980e01c0056035020182454100300118071480807140204201d035110101520328140c00c0c00090300144080c401403201900420801195600d1410702504058401000940d0741e031098 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 55112224 1250 55110974 55110989
    0x50705150708150303091309050106030c080d051e07021215060102010c0c08030105190902040306020901080a0c0c0b0a0605060d0608070803030f0a05070509090403020105060901211403090307 84
    0x40100514664042036140d00280c085564107945100f04001035964007418100070700c01d08400c0c2c880143c41910303500c8041701c1e65025000b0302c52030b0755a0610840c0034102c1c1c400d000b640d0080e00d001034480d500c0750080341e43c51009000c2542c2c8038000e840040c4d1712500980000c9030003801e141000030040400b0054400c07800c0201c40328842920385440021b00303403036050030100284003103444104000f80180c42034a05452040c0c1c0c442200c44503054080d007400b92503501500801307200140100c14042950002d140000c4280c80b0041103458000c1d0703d0f000c036031042080c4000100f00101c03100004d0b11700e5042c650020070b83d8a0128030151030300d00082c010707407194080e03220b03941c1c0e65003080240240900c0301d90700800c2c880c000745013940303018004c29440c180018011003000c0d6031440051400c6000780142e035060038000d00400781c030749081c4c50007900820013620b526224520010001a03154450158600001ea01c00394288040b84660f076040c03585200c00c0c5495a4a01081c0480005074a08110380002068132 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 55113474 1250 55112224 55112263
    0x60d02032512170d1508060604140103020102061f050a0b04090e0d1b05010f0504080c0601080c0102100b0d080705070e060307150f021203130501060b0304021807050705 74
    0x400c03041d41a00c0a032640400c007003800300004000400c2145000000f424070384025540c0d202c070b000550400411845040c51000001c4000c0031034078000000390184a1130303003903400300712641440034200b502600920000380180c3c007400000382e101c0300d0701069060700c030445507180030040e4450001504a011a8000103c00301001c0750421910380240a20640c1466000c0034101c801503010008251600c250b040f1141160320301000d03410000d00758000b050450100808002c00d003818645400e50707521211000059108a03000400c2044001c94403000254058006101e10b00107064200058410302d0703642a80072000115003c0402c2d90200213000322031064003e03103203550074403003800d8201001a10aa000c0e0348600c0303003480810a4424028040d02485c00c1046000e81400302c205d00e8a2001c90543d11344500100610100700754200300c0441c030b24880d800a11007640c5600014001d0302048a01130750011031480c41114044508032002c6c1c005215250007803820503030b030700d500380741400b0b040308028807401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 55114724 1250 55113474 55113523
    0x130614150108060a141c0819030e011103070c1103010c030e0f0a230309130608010b041505190e090601060801170604060e070f030501060914100905060d0203 69
    0x2d01c801815841441201c245551608182d540d204071501040071600946c00503401c00a00c910403c0204030803540440306903030314841510f000031400b10341c034580e0011a080c4011194148010f0080c180c4a41078140030704d0841c1d031134001c11102403e4240c800d640c180e0011800180310b440070701a00204001540700810310038040d03400246080c85d10986000f40e034100d500e0b02c600044141030641c01501c0141c844084040300207042d076095100d00c5131055030281c01000d40d40c0106050380c000034201c61558001304100d0900f14207220a50b005940c4014a121142c0001e00552401e01d04a107003013038080300c208240c41d80310041c035144400b086d58003169070f0740544010000c10ba070110100f40544528032f0b040039441225104140c0c1c030743d00a8002072905464140c80b01520408206002c000c0c03880035140003100c0ea0340e08040f40204000d01a041c1001d043c045055962580101c05034000c001c035806440c0c040d4a840ca01c007006040c05000140d005030b04240d20405640c007040135050354400e00e181e40a01c1c00c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 55115974 1250 55114724 55114727
    0x90516061107030308010504050601170f04050f070e010b0d02040305060a150504020a020a06050a0b031911030c060703030e0307020406031109011703070b0903040e0117060c121306141501 82
    0x440450322101c6990294209100103075105083c0e604569003544c000c103403034940710016591911030004203154500f696040001c800c460303008940c00381d802507007650303490203502440369200c40c02800b8a1800c0c1e1100e1004003c5c1540c540010a400480c0302b60040c00d0a450760369440c00d0000a0b1030000045840350036030901d000c2c981c02448010322040741c045141121903107003e9290440c010303000d010a03580b0300c0010410890398111681c00c8074018140c0724411080850f4400c108403188050703440300986540300480d414009100034500d540104081c1c04c200b002d0740e0403006000c09503034100749030000780a40e00c01038480307020b80c0019520034850308141138491803d000c01050140d0044002040040001030561004002ca1721401c0e04004030740b03900d55445204071707d94030541d84200544050132000242c200c01c91030a11400c541e0004c240e8105403204400f1810354041c09403142d1007401800301060149400c6503011508600c14007000c140300010324440200305408a40c081e0144031480d0300040d840d07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 55117224 1250 55115974 55115987
    0x40806071e03020315122e0f060806040206030405150a0b0117010506040b090a03050a2d050d030e100c1227020603040311100903080a0e1f09051606 65
    0x41c040c1e0b2a086096180045c01c20a04080d03020320940500d504840c2e400340c4040610031400481ca18014600b8a00c05800b0350700704815204004c2a40c07140f41801a045540d40f5019030f03000c07100d10500800c540e450b40c2d0200f21441e40060000c40c0c00e88640803c5546038404135402c00e10a141200f80003d1490b520000503154540716103000414851000051242e0794036041618140d4040c40b80c03007611540020003290100c1b9071740d00003600d144190410340c010040d80d10107016000c0c87c0d0091200d100302e80205c260150544404000380903420503259488014442d0713001034581c1c22032504644145d84072414500443c2c405034102c20005400040c1c002c000d14060207486421922041c0503501c0500b074464001c0d403da203100009101c0c860020215007854400d02040e03071001101e50960b01c02001c072288150041203220012004561800009008010b5610411520448903006440b072200c01d213422590b240c0d909494032688559038519070010130360800c40c420340c44c919034140741341c050b0a000340540350 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 55118474 1250 55117224 55117277
    0xf0f0e011728050106091a060414040506010905060a0201060e0c1804020f04031a0f15060313020a0b0a02010213050f1f031e02030f160c02010806040204080607 70
    0x284040d80c00110360344900182e4220400040182d100b50942c101400314041880c90102400641c01d080d804146507509501c1140d0740c105612001b4020401b800510a040c0a00d114044682c42c006c400c0e0091400c0940105500400501d07020b08000c0c2c031400011480c1d0800d1001c100141e41d124810302c1040e00c151b030100d8010711400921410721135503114102103441002e0b504c2d4055600031070018a22440c400558001d076612036000ea9058422500656040c00c0841b644810b195100700454861041103010482c4190094140751466894098030382010360380b4501260840c81c00034000405a4034040a0308050006900240c2d560380082e40601c01000759070840c2d885104142c440020640d80d0046c0d5005030791001c0c40b0100300215220043c0c0007003020100d00300400080c1c0008a14000c0680d0085200d43c90444800c55940c41e214071184c0d401c890403129101050f450001000590300840300c03a98050001400507140c44d403100c60641c10850241c6115010418074141881c9995405c3c0c0c0681c04c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 55119724 1250 55118474 55118489
    0xa0516020105060d060207080d020a02030a080a110304020d02030a1514090606030a03081b132d170f0304090c02060a0510050d021201060605030a0e010b1008060105040f0f0e01 77
    0x103070300b0603100241342c0004140004003125400283c990821900c08151524a121800c08640303402c104071001c1d4076a8800c80400f00000d0103c00001c01800d160310454121207507814a082c11950381d07900344070317250558050691703040c4252812000080d041040d4071040b40c1d450080420032210001000c2c045040240448015400500820169440c000f1f010301220381c252500c0c41040e103c2140d41d1850500d441d800d0100c040d000150b0b014000c0c002030807501290b561441d01206c90f12542012915070464800340d03030300442820401c200d82012800015824004801034800041200c4181ca2641d4015070008421507100d0404d442040d4050141c030740c0c804100a402d001d81d00c1c10110107010001140500d0303218074800c24010081d5112090303115031860050008101e10382e1a80b0003d003807030308101c95031a0132506104d50130240c490180201d034000e1502030b140c5180e840e6891029078284030024001c9042000a0000003500240d101059005100c0c414044c0c8034181800d0302c446465005811055 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 55120974 1250 55119724 55119731
    0xb030c09011520070308070c05060c0a2012010f1b02061f090e0c040509010b030a0209042f150a020c0909011d0309041505090a090c09050a05160201 65
    0x1000d10440b003000800103401e89080310400004884000e0008a8482224854490340c2e6000c020042d18200800115004d4001c42d4401550b402c2000002d205440ba4080c0d0f82c1c010600f0100002e0107003010000c902090303145041c1554105002c10580e02e032800310f00300207079126114640c100780c0da407050451104542c0140401d60042c08006555410064040458055407680c3d040e071428003106850040d1800c1142070043c5203140011640c0c4668102e0032512642c6054045919540144142c00380040003030090701e120400785e02042580000188181d900e40e145445140d11800300a284402c0580c94052603901412620240b00c807140c169551201758010802c01221916000036181d200c4c41400c49a02c0d11555809a8050150011000300d00c03207161480d000f5032040b240131001e8042e070403041e1010441000c1007103070050780f034100c0d00c01c1d55045600500840d0000c00c035600f02d88420340c0034801034449184d0301e01d1311508580e0110f50007244a030341d940a1080013032001c200312801c2c4400d4402070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 55122224 1250 55120974 55120979
    0x30c02180c07080307090e040b040314090d030302090607050f030309070f1a0a0c020a061d0306010b040506030907120305090f0904020f2b03080402030d03150302150712030b030c0901 80
    0x6210780c450310300b001e0001c41011000583c0280325041d6400070303040d0000c40c4065810149084480d00006890803004603609a00014026400030152f4003c0180245000e401c6c4074683c0f003e070005c4d0b0080c07968a070000820881000410401c11407000d806891000642d524580800001d09100c11a003020901000219080200101c40d4042c5c5201c424500e00745565550105010343c0c04030a01f03003001f50032410201c40000d1050300200f00d581c00d1804041921010b038006410181c88a80c01d0047c502c2441d000d00040c095410140040d59021105a08895072540c44422103c5162440c6c1d408400086000072031001c0e0382024080c40c0c06000701611460b503541010390008120080d180b241c2ea005541c0c3d810b5080c810310a04900541e502c1c40203034990840541403c000b040000d04440c168080d2290150480109209100d844541e1000e00080c1000c03a080d07a01301314040ba20040701000310901800b5a03004925810a00e0300762074695200015141413110902d400c0c01c3d1400c500c3c510030390040004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 55123474 1250 55122224 55122241
    0x5060705040311090606120c0409180506070309020112140a06050609010906120605060c010203060102120c0d14041707031203060612020309011b030c17070c170f07030c0218 76
    0x21007880d030840341138540ba503428010030580e02032070060b140310b11061001e010101060f07100610503125010014801c1c005185508a034142604a00402e1644028001090324ac802c0d800802020720524180c201c08480f8219402611190040317030000d20710740703014080b0b41c036a6803088200401041c0c600340d0402200b41c001070150b00081c450078042c084041450300303410886520010203840001c0030541c0b41c0a00d45240c50007900200c0d00e0f140540f0403030b41820b0011041d882076407400400070380140b18480441104890385003556985440c0c201041c4800300c1c0e41c1e05000c81c460300040034040148002465410034403000f00742c10401c0000c0c03600e480705c10f200072a8810407907130001c40d1640d4003603565210408420300410f504241d001c58144080301995802d41d1680000362181c03000c0d52040982e45c203800040d13002210580d0650b0104910a0a180018656007600c8514030070221401d801d040c9422094902c6a102072012000155088041d100b1840c0641000601441e8800b5103130003850000d80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 55124724 1250 55123474 55123493
    0x12030e0d0f021e160609050f0f0603070507050c04020706050f0601030510091508061608090714010804030e040e030c060907060e0d0f05010c08160206070f0f02010905061003050607050403 82
    0x81d5207050034034040c2c0320035010010424001d900900d1880c1c452138a0b55441c00030401042c5000e02403282030b821050001a140c5205904043d100c0140030618544401000351020b500c45502254580149100d1803c240d0b1284090081300b8002c2e0310124882c9007130101d083c11400300902b0641810301e000306100c122200194140e040c0c807190f06001940360660848900f40c2c102551040242e441340b01c0030803460041500000e141180d145d1240c807041d480d40901d503078031032940340103022602c0881c2ca51400c4c40e41c49010505c0c0c00030301a08004064202c0c20003c20241d9000d600200c4140d40002400d41803c6020803c10313500003044030107001e01c0790500000a1207050b010580c0d92252455180c101e080c04401d10807c05210b51010081292003084503003d4075000b02241c103044030421b003c10b10060b10340046081c51150b603030741d80c401c4507891070600d040d10145464210401150358070b20403000001c0c01042464000c540b18049070b01d4540c80d6140c140e1405000600c1d04041010511081001a22501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 55125974 1250 55124724 55124743
    0x17060a1418030c010c09060f090305030a08060f04050705030114090108060106051e0309060a1802150d0204090905060402040b100203090d140a12020c030a020d080f0712030e0d0f02 79
    0x3124040031040c0c1c00006461070148803400a59546042000c88040340c000ea483c40440f130040c0c5481207803841c42c0c2d4064030300c2c0480b0705c005003060b0000c010080d105446a401c59901101c01001080a850440007050403140d040b03903a0004100000018007821000c040b06130014601281d0a00c110360401488544810061140c40709020010401c2800c1c4110012003a08502150700d84540300d10701082102d03a07407103096500c500c080d850030f00b84c000c1d00c882d29480e1148094010b0301d4103070760280c04041d40720541e0003241c09448031a400d1201091100e1903004d458012406100201083e0419004000464071120314241c882c49140103400701d02e07500401076500035042220b601c015070340b06003400070892815440e41d80c241c0c015001a042000040100015514466400c0310700907500d4200740341d80c610110308043d40c03180c4022101c1d4000b441c0d1200400101e201d81c0c40f41400c06160355100145140b9100e02240440d40769a08000302d00e10400448040da1220300d480a00c505080344083c0d180c60300e05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 55127224 1250 55125974 55125991
    0x9060f0b04051203160302070510030e030306150f04081005011e0902070809040507110601060f0c020f04021204230a0f020d0201091a040801050f0601050f0a031517060a14 75
    0xb524000803440c00c0c4251407918683c5c403114640c1d00511b2034000d44071810360041521424921019101d0b0030b20900c140784200712200300852840e1600010460f46001e00f00d1240c4890300100100110403c01030003500044c00100c0c020800c83c001402040d042d514141c004100d82c003201528034000d00c200315268070444180f1100140e40702d0080c00c1c0050385110300c047e495009400c00f81400201580181050803020004003a04c5c0141d8a4000848200302030618502c000f4040068100143c54045d003440b00520008000500d46010480000e4032500215000e55942009080206d1100d41c0107106064562510300904045002e6580e6110128148180680030f4004c0c0c4003113100b164090b80700d52014184850070080c096000901905441d8000c5c02050f41075407c0001241240f4526031110f4000c1405031a8603040280c80400d4505130b400100c006420141c90750040c0c08841d1202d800c004c054000000e5020210400302290361a20a001c1c015800b1a07143c000010f84101070500e582e034000201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 55128474 1250 55127224 55127239
    0x403050d0f050103030e0f03010c0e0f04020705010510051314010303030b060d050103050303060a0f080d0f1b03020d09060e0f060d0603020603090d0905010206100e25020709060f0b0405 81
    0x59400c0d54000c2148404005565182c080048241604244400b01e1a08101e95002c94041c012050600b41c0d040091f1840c081342031080c1c0680b603842c02c588182428400034000506191003601d4032801c1d1f8500382c80c15100071091100612003401c081e40300c100d4a00548000707000581d20705242c0e41040c0070500c000f80c10980e9648600c801c1d603070303480300f100d49009540c00d00340500e58490600d02e8580e8000d4031094400c07a20340d00d000980a80c3c20081c402110000806000c0c044503000041c1c42c0d0780c00410038402040202a245e400c0680072207000c00113a40254020040010894800b408140d4207402c844140500200728035050342d41c1d403800103c080f100b51030b02d0351141184440c0102902943c1c200070351001c408000c100145c50b000960308007180745582d030703060310a40e1070005a846980c20344124040d128a11030034400c0c01d801044c0e65070004e080101c030f00d21122580c8400d0201c0c402801071180141c0080c0380070481096031780100d1020705518070424286901c1c01e41c0d456404d01c5140b182e03e02070f010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 55129724 1250 55128474 55128487
    0x10603020a0306030b1906080d090e0a14070c02011409100c02040e030f090306012c0405120c1e0c0d030804020604050604120b0901050c031503160b0c010e010e06040305 74
    0x1081d0000c0f0002d642c0f00c40c40b01c1181c1001c0d25000307102198141501200303032a180000803054000201324050420303d4841c02c44007030800310b40000c00c00004150204950322564240881104e40900341e22078209071b80d80c503240505a00c00105408545c005006100c0b809106a804654900b00d0740ca5441015081100b0306031054400308001e00b000343c54003c02c0780800300b80c2d18034400f01d56000b007965107001c4050350003982c3c90780c42c60300005c0009510b1000b005e060442c3c0341d8083e54000d0405420500900481d59020985d0020319030319800040c030520b40b9000011003040d200c020842c0303e050f140e21200508507003a4054040b4407403100841f0041c0c100144540840d040d9203138481168050704014003282c1d03a40303896481c0b03c491406000000c8031030310443d00015401e50f2040c49030900400030504030f41d10303544601d202802d41c0b44000244035458040c3c40700e030b410199814000720008103c00b44955032078100509009084411540d00100c460741000ca002078560350100f2203d0340154141000d503190207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 55130974 1250 55129724 55129727
    0x2030622090b0109060302030f03070506010605030a14070c0213060303081b09040504060212090a0308010b0a020c19080c060301050303123106180b010302010305060102030c1e060903040e010603020a 87
    0x1e1100191850840c4030011440c0405030f00003800380c071b00036800c031150410800d90041d40e070f220b00c800c00f60107500010018005203204030000e540254881202048020901c41001d00e094070540c0c0103408100e8049040003103080941c01d040e820120030500f00b244a1546d14040d240c5980100000a400f020b100154400001d500031341c0c1c003850700030303008219034074042c83d0900c002c1d4000b044440440300d840000841c2200300045d98003000f40c0c5030b600c0c00c100d44d1034541c4c041017075004074015070258000c01070000c0c1c051b01c0302400402c4070b5620b4506503c0c541d2602003801e0400885030742c9070b801550104018006501c0000031a0002c40f080114480e03d51340e032460b00200c405460302803203c01d07428180c9401026442c1c84107007010500454040082028038940d4504038445d81400502d099410b40041000d5070196025613072201041c019680b1301000e8a141a007496031446484517a054541d8202c1e2862000b0850154000c035980c0003186400d042c5003051480c10414881c02d81010380024102c1c0160307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 55132224 1250 55130974 55130981
    0x501111609110c0a080a02010e0f030702040b13050a091502090f100216060824100305041e060510060309020a140a050a0b0903060c0405010509010e0f0307060512060402030622 77
    0x1a1810f0303003034941001081c03501131a80e03031082d681d0f0030056003807040b10040b204e0041240c151500744c003001980390401d03a60070301c00600342c0030440c203910903d180f20364901c06c40030380105e5120b01c40000c000100c20405180c40301000748006443c0d00c88a205025044e081d44a00f0242c20341910112410a5045041c5804901d041c81410001c8040b842404c0d00180031034026030182c0c040c0c0d10342d20584d1038200104035141080c406818204d98441d0210860740444c84c002c0d8089a0002d0090404502c442c9031005108091a1040c0040b0340c3c07259980104030449070120f01c520058100d614050008941a40005050103c1800380c81c519003075181c0c000c0483e0f90b5056824000301400781c02664100d545401e0031500713412091265010f4052980010600705481c0e0071102550f8050719142d013850440401103800c002c0c4010002e070402d00900b00825566410803101004260b40c2d51110360740d008254030900c08410242c0102c2c00380d40180184071160380c45914450f1084020105101040d19014480b8080c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 55133474 1250 55132224 55132237
    0x40f12060603060216050607080c0301030b0703060b03190b0402070803040803090307020d080c060f0402100f0201020c190215070209040305030423240c09010e031c030501050111160911 81
    0x8030f520020b0f8420b40c40540801d0442c43c10700650a41e11941e0b42d12006451440d421148222070440030401480020004410940c004443d4500080c2d0319840d008001142e070f109440310030144940189900840801e80a1030724000d4040d2015070409940756a140317568000600014000c02000c400a42c09100420580d0940c940040c102281c6183c0e81c10503070050751183d40c16146078043e0100182c070200305541e1850007180c0c00740c4607603003122004004132041d00008a44500f155000c12150880e46400c102c59901840002141e031070440d81481040194a07040c6000e4020783c0c01884100c0142e0b03105440755501c150103041040d9a90350341d18241d00c00b10228042c044c20a0241001203500da80c000851002012140060780b0311030a40201480d104c00707007140c0030954403c04001201c25540f00b000388446d1401c0190480b0708041010f004041c41030601d40c81500000d40c2c0d42c00412076903a101501c1185262900041e0a0181440300317002d170001540d000f0340200c81e48903010704d45903100b039030b048503003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 55134724 1250 55133474 55133483
    0x908070302270a02070b06040c0206040209060d0206270d0c0e070e1c0209010603290a03020607050114060607020607030e1203130e0f1003030c0203030403060f090201020d05040f12060603 82
    0x107140c08020360000790005c00043c0d03111450007000806504052144186100c0c0301c0e0000d0981d55a95420080d01900040c061604100320b5003a0303100507110203016000304d003c21845500c40300e040d0034a001c0d10300102442580700701a07681d100c5011a18040391300c029541c0b411384000544c0d98000065840d07440d011480703508015500303034003007003109a0303080610207600c21107072620f85e6646c52904a080c0c0304c408001d0354540c1d20310101110b145e0880009884458405000d4078816592600003d489420803881541c490751142c01c02d440c0281042602540a00d007242c145040910940219a05008042e401800c1c4140c0580880d40c903030703881c2c017110f00d007800c0d0f10300320b82d82d032100c580c6400a0b00987d0f124490b200b01c2d108000c070b40003210317500340103104d1903e46620b600303200c0ca1030703e0450300740b0b4a658050383c0500080201001050300c0703000d2110340844544000c00e01007060710009280800e4040c0803400c00c18240814400590081240701c2120ba8081d0b41c0501c004203030070b1250081c00c49500040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 55135974 1250 55134724 55134799
    0x60f0203090a080a0309051009050607020d06180302010c0807170613020d0c090f12031b08070c0302030c04090302070510030f0504050601051905060a12020c060408040f060908070302 80
    0x40382c4000195292019200c6c0c1e07030740358069940c0d106201b00c0681d440b0826010a8904038213001600f082c401900b6804d00041c00c080c0003800603207408084540840e0608807401940d15000b09150b0240224800d01905d8500001c0074984818018003000007180d6400108885a0208585a484400c242d50390f907000e28017107660b00c11002c0c04000034080150750300c02103020300c000002e1160500c04158200d4011001101c64001e05a0303040750041c40c0300e44c91020f403420842c41c200100f002c080c090050540708504803030107641140109032a07c20603000c071600c903505003c031b01000603901190341c0040311010398502c85105440d4a0035000f90490381030602425107080c0411090090008610b4102d1b101950005110700caa10b03412000c9a00701c3c0102a00061304002c440e04c1e00340700f280d06119034010642c005052604100d00c050504a082c1c0b015500c030f030400315040c01003035002d0b140440100940d080001d0f5207440c049009450300600c0c40302074401c0707500c1120684d0903194810201c104498400f0641c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 55137224 1250 55135974 55135979
    0x8100914120c0d02060402031c02070911040512030901120c0c0f0c24090e060604150906030b03071a0c030c0d03060609050d110405060402130305010e190201050301060f0203090a 78
    0x801040e004005010554821403000070f400c0e5001140b000d014940207009024080e201d51003190340b500d45000c40700114424010005060b0380c542c40740f14680000e1014840d9102c2c80c00c0c00b00004143d40e214030b2003042d08100b090302030585e0444d44c03c40c00c0014040000c998000d051038152403000760381c0301c007400c038998040ba01010041c40201540507503240d0030f0764011300c40b040f0b181002c040c000b4803c54000314401e80b10600c440c1c0f10001e070441c0d003c14010020b85c5010740303c0c116070800c1e540310203131103012401002d01408000d815000b40c0e04850b04c00e130010805149001211032480c50406a203070301c08000028840c81e4160140116035a00300600102c0300c00b10000c40d40200242400c0c407440c00014100e190100741d0740380640800b80f969800c4045410100007010411001b0308001c2c02a41d0b0069080000c25600c8540701c42001c01140110000111105a208001d0030145882c40b41400441e83c040a040181e1700001524103542107841c0150782c42c40c020405900e54458a80c01e00ea02960b0b040c0c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 55138474 1250 55137224 55137253
    0xf0105030f0c09060a090f0806042a0306020409021201050906030c0411090301020406080915100603020a02070807120605060a030503030c0a030209031203011508010812070606050405250908100914 86
    0x4650031216203500b044101f603901c0c0c8942d512a00255002407101c600c00070100b2000209200703014441082e8013004500554075510903040b80e10a49c4551505900070400c921400d04100312207004040a41c3c943c841d07841d08400180d1203100d44600e6a01c1a80d6442e0203410501484044e40c0712081b02034000c641d02d41d01c480001e09040c0c002c48400c0c42d01d00c1210940e40c2da10700100007260154100c4404202c8107400c140064000c1d402c207038810b40440c49107820001c0c1241d01000300740c00070514000002c0f130b0a90142481c0341541d1004240c01c0c0140c29002041001500000c120395001c41c40c452800d440740c292540440c040d116041c00981c0c941300d40c0150780d0301449104001c60403140052400054503000c00f43c00d0310b80180900c21071042d6007065050030380f412200d50042028610031400010103507101c400060490764140c1306402500750280300103100b20a000d40c0d24803000e000e810300c454000d01c0c1851080da25400c1451030380d01e1035141c40d8403c007000301c8140c0681000780003505558200c00301e402d6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 55139724 1250 55138474 55138487
    0x70212010207021302120f071803031805060c0d0503101205010f0e0a0b430908030408060403141603030b100e060412080c03031e01050f0105030f0c09060a 68
    0x1400da1150703011240e8804c11030300c0b034400c036002c03880442036182032569403103a01c0c4034000000745484240202a41c2e040303203056885440401451094035030320005040d082140c542104a9040240a4001000300e540380420014000c00030301713910300e041507507036503503040c0e444004895078440002c405080454004200c01900023032818100600108080600c080c0700a50320500030320013030945c0e40c9a8001c640142c0e014a0340a07460840351462072032039800c80d00c0c41c2e07074594802140c0f01490800d180500590a03481803040c03000f80f541500a41c1400d0402003610745607800508014140290308505a83c83c0301440c1c00d40d04240003070310700c00300c0c804401c0c100074024000203071a0521801030303202e501740968094504010f020001401042c2880d003400380b108901d04440c801039503418000d11540c004001c003000114070139111542e2040751405140c000c000c4008060300704a00c03e000c0c1c95030442c406c0e41d010301580d51024020580c4105904c860942d1043d600c40c150341c2a402690000d00c609811340c0060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 55140974 1250 55139724 55139737
    0x21305060c01140c03160305040302120d06080c010302070506010b0c12030901090606170a03030209040e0d0906120507120b040f020301060e030714060a05030403020115090f05060d05100f020702120102 88
    0x903010a9484e001e000c0c04610003141c640d86020071a402c00d003980d074460f41c4103e6000c2d2090044076254680f46c03d20211030342202031401001c588454083c0301150040c81035141d49035080c2004c3d820314050395034643e102e500500451090701008168491030329410054403c003008290010750340c0742400100e86001c2c16000c5030a035213140c1040030000d2144000c1969040708501d00d07010780080da8841d50210080c0d40700c3d13080c0f258440d803242d0300e40180310800d1108402da0402e549403481d4251400b480504401202a201c003440e615040800c100d442e003244541005501c40e200000d000c14500d00010020302d40c62180c031803c14404000403600c02e0b00003a000c51130400440840d60340d01e58070001185040c80340c1c0b10b982d0308802c081c40b052410720300440285400920074000410509088842c55402da44035034443c103010742d2201401d5850030410302c02d0700d80000c403e41d207000d00c24001ea12090781da1284c5014400c03065665800341128152254140c880309580141415201040d07040031034043e41160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 55142224 1250 55140974 55141001
    0x2030a05061905100318060e010e0f01060302010c0f050a050616180b072409030f0908060f060111210403020102060106050a0c02040903110f0a06051b030406021305060c01 75
    0x10106540420803071140d402c202ca500820011401c0401d0034201c014003040c10159140c00c407050032003000584140200c9100e0b88403200009165060008042e1401c0b01c02100025940d2403e0011710240c1d9001800b0401c1507004181e03500840c405103411440c03c0c0745a0005011401a5018000100d050784003018509490342d94103002c5100c01e00c401940400141704200a00c84100800c100041d01800001622850510004240010600004141e43c0445030440024680c0042014041e41080f49800030f00f42c41d0004001d42d2610b28951002103101400103410b00c0b220040d2803046e131000f0001e503101e25031038070b48010410144d1440c5002c1500a80803c03400760141c00c0c004980c0a2060045d91604c2041d65910002c0340501c0d000d11005202d00d400c25410060010b1f041e410300d0204010859040e4102c2d801003000e80300e141000021110098002c1184c1e00da0361040d40541c40458fc02c1d250865048400181e031030000c920410604c0314035502a40d000040821500b54254040d070181074041450b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 55143474 1250 55142224 55142239
    0x5241209060702071d04020f060a0905041103070f0e13060305030301030c0915090216021c1b140603090a0c06050d0b040b060a0f090b0408010b01090e070f080c040902030a0506 77
    0x50300b100b03130384800031801012211400341c2001d14040f002c0401c030b5900940040e00092001d5500408030b4500d50041c0c0d040d0002c04c4c05503401f048141010700c510b154140302c6008040c15030400010040c40c03998104500001c0142100300002c0c90383d0703180812059128601c2040083e50f560340ba045450360024441610781040c40007002a140d016401140d080307040c0c9219070b424050030072020300000d42007105070460000000c1d8021005841d126400c01c0c0e40a00442d1402e00301c0030030300d4111051092003100106840b0020420440d0041c0c21403820b881074012242e0540340d82d100c2d580585001c1015002825030410301e0b40005506170840002d10764034414100070f02440c1404d6061009039688072110f141c003d50308100544481c0d01c580c0e2541c0b2440301714500310f10342964451030f41e00309070801d42001d401079540e851540101e681005040005046c1c40011a0340b500d004a00680100c00c030079a1030060122000000d1401540d680444025066001c1c04540303a051410101c40101002c64005024604 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 55144724 1250 55143474 55143481
    0xd060e06041503080703020307051009110a06050417010f09120f180603020d15030303020c1b0a0905040c08030309070f05030c0307180204030c03060b0f06130524120906 74
    0x41ca03006401c0c07000d000e0010344082600e590386622143e44480700580440c00144003407800280240003803c4245588100424100c0060905001d80240404603e00c915a0445d08008583d0403205903004c0750f186080014540400f1600070340500340018005006074606900c00040183c1e0f1311152400f006640e5800080b0341004000ba00c20b450100306114200046801c00c0000a00c03d4009100b0400c0b4901d010440040f41c820494180038036030030480109402003450f04501d00c0800c001c0740c1d4000e9002402c0c454001e1000441c140b44014002d188082e030300c500004041c40b00040d880301c000c0a0032001c41e0764030715141c420b858803194203000d03505074980c094000150600e00000c034882850b81c001d024142c00e80ca03008045078006034100c0c04602054080c00000013207103d142e0140011801a000810b040008400301b2104054902d41d1503c82c1d4003d2060030100c05880301ca00055030010b032a0b0710858869000c0c030342d80700b01d01040c1b80402d1003000034000f8000c80480008c0381c012000c05040300d5850701c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 55145974 1250 55144724 55144729
    0x5070e030a0c030b220308090124120201030b0a061214010608060108091c0201051509040f06270f172110090c0203031602030901080a0c030e030d060e06 67
    0xa4000304060580707500c02c2d03801e102143d010a409a00071220400f01e83c1e410800e454802c1303011074030700030581c00310350b01004120800d00e0a00540801103440b40c040315801e003180e00060b074078204174050a5215900000c0003821a4026405001c0441c4000d0126a102e951054010300342c9180003903d1101e94100903021203000803160f05681a0355658a070442143c0d44c5500460344800300400d444114896844c12485001425080c141040a40e50011949241078030f03008041c01001e212141c005c58010341000086001820301d00d070b46a0b03212101003070740300b2a00c0748000c0000d0007440440c0c41426100f5030008001042d00418074861148144860000078030394840d07540d015074100031000206600785855000c0156000a52101c0105419041c3c951038004a2044a00421100000d45d2000040c000740034074900c003250124203036100651030441040300007000e40c0e2002d490801615114903000388032a000740c01500f504100601100d8440105d4000f41000d00010302c2050304d02914507011546a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 55147224 1250 55145974 55145983
    0xb1009060b040302010527060f0702120706080f15031902030f06010b030117030c010f02071a09030f0903100c08010501120908030705031b160b090a051002031f0905070e03 75
    0x7690161520b83c00c01002d40c100d07d1410991500d0241c29800f00e65140025030380d6000a89881d9424812058603103a040c410721015400700c402e181129400800308102c0c5035030085980c0d0b4440048011003500352103005005841e203104410b030745c3e814018850007400003110190040401c070f0089080f40c1c401c500101040d51504800c0c020880440d07000c2006100f0a0545a080c2c3c1c2e44116100803646080841c1c40d00b07a0841d80010444046c1640008100c004d018a80210300308109003500901e2440c2407640e0320310b59912400b944164201c1002c95040c00c5660103000700c80485149210501c05507604641c0241802c2090281601180400c841202540c4c0a4401d442e0400e41c0321301003502e10b4507005800c0d11103410050128034001c8007603000305410703040c44c1e01401f505141c40030810802c040600d49003100042c0203124003096070050100c2004100002a41d00040c00c400d1001a620340780d4180e134906007600200380c8018241d48150010701700c0d00755801684180e25039901d000110562108040c0c41e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 55148474 1250 55147224 55147229
    0x5060f0a050610110f010f0b0f03060705031306060e1008100c0c06050a06120b16050906090103090c080a1b09020a120f06030c080a0203060c1908040f0b1009060b04 72
    0x70010705440041024094444140880410405c903070060003108032803829542c4a19401039015210741c4191889d05015558038110340088014100c0c624040300c009003107010003003078981c040c3c64805000301403002580c0700300042c021038040440c0c42d1411801c9003103030301114400d0400612a114007907189445521070f014960300c41c0c0e0ba0f20f08801030719072100c03000782c00085d01c840500b40e80e60000146071010400d201c00110312801c0000d070186024981455048000010202401420844c074880d030355408003182c030408424200090354581c2414003080024054006103290720841c52050b0901070326141420301003424200c50070b4590344a0310041c081e80640f15040d400300c0e040c0030308400e05100980140358844128040040e0f1360b039481c0c0710518011360a901052003900f03e200c200066081c00d00c80194405011007259150503003107140890002d03040160203041080860100c4d0800c403114412600c41034006e02e12036860306103615600c0e00c0c21802c0c46021101403a140c40002d202c58560240d030704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 55149724 1250 55148474 55148479
    0x40f0212060412140a03050a020f030106020d1106010b0d150302091504060b0a0c0312150e07030c0908070b0903010902030307030206090d03150506030406020c0105011e0801060305031e040801060305060f0a0506 92
    0x10b261a219007503016100c040c0030012303015020b2003510800718071403001d1402015150f004006044052002a10a000034891110345070040030046c030410301860100c0b1856584e00710000303a10300000c800940303802081e40000754030003400c0060001031200382c0c86410040104a034200078542e9504c001d80341d14840c5004d224085810410036001090180c141500200f000880201d00c1800e88010321040300481e800004407240110144040b40780e0502c1201e03001d1500d401c0c0000b8080c107187c81d081e030302c0785548075070039480da03000450040350f4a0a40149880983c0034080f82e0701c950031443d01a4076000100c1d16040c4500c42c007100d405c12180729026266001c4c400c200f1001c080382c1404103028070741d84020019a030050b004c0040b910112801d2103002c2c000c28045003030b02150004001e4103515a0400d074007140b00c3d607060030320034808540084225031a907504611900c00e02d0006c4403804110b0b0144d50b101c408154a481c0c0c00009004000c2440341c4a401d8119501083d56240d4412500f01c0c2ca09072003254 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 55150974 1250 55149724 55149727
    0x90f0303020307021c030501090b010516060b0105130e07030e06070e090408310906060503010b030a0b030f06060301110403050a030e12010e0a060c090506070b040f021206041214 78
    0x8280030358011a0020183d2060340c1c2018692511848400f040004080003c0c1d9920b004210581c418400c2401345a42441d06615006c00322142214501d40c8210107400305503a6945010303160b009070b048514001200c009210940d0ba500e00c455130040701150030b43c0c04281000b51072652001c0c04030340e0341e105884617111601d480380604180701100f04001e0044038103034801c110b4a1000401010020b14840c0c8035803500e080c020958086035070091083e801251501e00307043d03050120f0b50300300381604d054072540554180c50390b44d01500c0c0c40186c00341115154041c05107036040030100c000070030a070344901400da0090000c001d60b4100c1c50680d10a92001404a40042c2003020009201b43d442c1c18028800801004520400e00421804c6800c1e01d045c0c1803c03540025024001c1048500800341018114100610b40701d00e4000412120f205002000f01924100307400503081010f185003448115402600130030038205c140315081c1d581c100a44060b00c0c03e1110400449100d41303d00604007040b20380c5446103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 55152224 1250 55150974 55151003
    0xf060c03010b0315121e030306011706030109061b180506040504090501090203250b04060e120102040b070605040b150a0519050405040c060f080601020a140a0c0915080109 75
    0x702c00941001d0311070100181c8202d8402030966548044901c5000d0074800392000045180d1055682c0010b030040700d00310b810a1003041300607a040303011402c50700c66404800100d035842c2c90004e4014098403900030011403034071500341c265011018000000e180c0984a1019140b5000107505504c038507813040560001c41000f0070f00c51414a504880543c030311400022908040d190300103804c18842d48414181d50003030b40014203841c18204550001041808049483c15040040041c182c1e0380316800d05010309020700c450724607a842503044400421514510070784850380d030710301800601410b440a5800403019800b10b0718020740a000210003550003407000300100d1411003030000c1803103207000441d4540000c110008040c0c0341c40c0183c602c10b61040100112990030507101501e4825a103520300104880e05081142a90700024609512508484401e46103c044e003a5a0304d8081c0000d001006090701c00720024190080e034110805001c200d01285d80e40944401a00f801c80c0c0303135440043d02550442400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 55153474 1250 55152224 55152239
    0x11107060b030c09040803060102071d010302040b0a080327040e0c0f06090a2907050a080304060207051b03070b090306010b030402030a0b010308090301050a09050606100504090e0f0f060c0301 84
    0x407054a07a0042d0503105109020343c0003500c601000c1780c055034100400003c00056681c14072181003d09070000b000005000c0000d0a0807010a05000090085581e43c2c00b0384840d0303450340d066900520702a800c0b07995072110b48080d428407004c00032902da07440002d00b800d4a254502802281c100014060003418a443e0b034504016002007041c0d005600f0401c2000014002c0e02d4445e680409081003244540c0941240d07000c280004951500c00140305205002580008a01048400040e82c00480a0f606e948550804034028401c00d040209144501494402020801e0351500d00c11041102928209a13030303004101030500c00c2520442d455040f420050112115540155030041d00281c103c030013102c801d54a0303a15040003030304141c074840740c049035030300103481d003401219803001d01140144144441c0d681c400356900300103012a44500d581e00e2a05074201e114005407002031030300a00900c40c141c801011103890311194408082c00b805016000c0c04201000200305024108100c185499a880c0044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 55154724 1250 55153474 55153481
    0x611061b0c030a02010902100c0203060c0a0e0a0603140703020a020c0909100c0206011403031e09030a0605010f030b0f0705160c0f090608010b03060f070e010e120105011701110706 79
    0x20494480c04144404007a07444100080c0040140c180c00010700c0001900400a0501030180320070f00b000340c56000c0c80016100820000d27000241c0e840c0e0a86c0b0341340c0961003505c1d01e4200010940c2c0150300741d1400543c459150700143e42240b6801c0e44c540c2c0585521608400303a00ca000001400b5900c030403907041050901c01802035010f104a800d442c0b488407000441420307030b98400103400c0103900ca08018018031a407140e000c148484114010b524001c0700200315142006202c080310311501c00454058902c0c0c400744011018154001d01c100801d40c1c50700d51302802c4044900056607940200b02c000340c5065210313030115004170a1030711107905200c1000c00d121502074580800325521500c02c8030024910b0019100700005d40001e00d0302080440c100388085013190080030700715200e0340c0b00209014504c07041320720080c0c01c10032600c1c1c1044402c1806006031a4401003d2404d5000310003083c404103044419444281070b10f070032108466580309034010150a035040425441d0740440200300c54000160340c2d90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 55155974 1250 55154724 55154761
    0x140301050f011107090b0118050a091802040507080a0b0109230102030708031311031501060e0312030a0e010605011806080a0b03011803080a0204030b06040203040f02030d0504060306061106 83
    0xf40209070310a81c1507407242460301940c46a2000e584805001c240d075a040615401402103400c0000c5010381b03000005098920107201d02e132481d0340d540c40d9482c0704d220100d00400201d07801900c207001609100740700600300300040700c452901d5481d1640e810354a6108160110450704422184e140007403028440142541580711510305521041103c0070005915074082c0d40304840b0071401c0c1100802d28140742c2491003001500e2440b9030010034030408a504000100c90550b4054a04680000d04030b0000c6403418000c02110746000c5004030400030316940d607410800008596000030300410b941ca0006503403a0046e040c0d403409000c001c60081c40b0062044c000c0903440f00b00c00b0300100d50303000441c0c042400c4411a0a04a4054612015000502d60042a11600018040b00451070b084c0b540c2c030749000030000a081c040c4039940020107d014095400c18038070b540d98009040c0c4410300003040015090313500910801c0040703424901c002510f85e02901c403041650382c10b80050641691414007100b804029203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 55157224 1250 55155974 55155977
    0x70c0b030c070506012405040b0d050406020f270a080703060c020a120c050f0705010c0f020a030b0f0f011d1815010f17031801050a09030807081207140301050f01 71
    0x144030b0b0a001c207008000d407034000c000d040703000100d015010181e079680303e142940a0f000c1c482e0400040009080b42000c5038140008400300103841d4841c0d26081c0301078400e54400340005240801c50404a00422403c9080a00203181119880760b0360b00c2030003c81220f6125842980d005004100b0104846801007100300e5154419100c05003010f59071040054109103104001881c0b4850350810442d0802a01455111000c01844a1490400024440b4200010040000d08811004070854a4011040014590004900f583c3d8075051912802543c401c5483ea441d103118140000f8695070303119905503091180c0420307807190380c4d2500b034542651040d1898519007481480400711070311006080c2140a004c40b4038103d05060324054500c0304030a08c603911220290810481940052034244850b1103030042820601e40b507846111059480c1300751544090841100000c80d0801c00c1003080082020300417840702c104540d04c034404207ca0882c511030800402c941301300010b00007460700d0420001c00d00d505 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 55158474 1250 55157224 55157227
    0x3031f030f0305071b0807180e03040e061008090307170c1c170108030403060507090e0403020a0b070503040209060609040209060c060402040e0303370c02070303020d05070c0b030c 79
    0xe9a54041c282a04984182c00203803020803410304210b500c5401d18040072468000024a0342051002e5885428034490b84c000721004020078801a60310350400628581840c003038a441d40d9582c1c08a00c4012011180e551245910200e00d11400d4022640c042c050b001450046040c040b243d40c4460341c001d190070346000032034400d0004212201c810004d1914046809048415140705800c014280b400215961558403055100500900000000b5a070441c3d401000100701a10f41000c241c2c0c0110703964000c42c801c48601410881419000580054132600c02c58040d42a5924400c080b1228042654001d41c89003804020800d1440d000010b080110001000181b620a8080015075a58030550410707106030014001c010561506100d111300303556141000c0c5146203480c000a14041030190444c05500fa0040e5001d000c3c01d410030f00c1c403404445628020019005100c4c00a0744e01c0c0c8062104030010311a07800f038100d60520440940c2c000320f90101c0403507042403c0c0808a58180c00080001440c08030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 55159724 1250 55158474 55158479
    0x12180406080a060c03060b09011706040b0a170723010309050304080304031b06030c05070609030309021c060b0a080d11010908130e0702030909060d02010e0306090c010207140303031f 80
    0x20144010b000507403159400062509094401030f09880c0d880e84a80f11a04003842141c220340d030401c2120300100741e00d601596090f5100c2d00091300511800c0b20094120388945004602280ca810540184c50f404008079221290380d9000700c1c12103403000d5910201899001c0416045500a80082042e544282d060328200f0762103d42d03080c40e40d0443d81c01034440040b01c8804002071000d41044001806181c0740500c81c0041c4550050981e01c202c000017010207640e0b210701014035101c2c6c1e102d00e210315401014155418121800025140c540b02e00c1900c04510700001d00302d41b403400f100780030125a904005003558611500d0140c030703071640f46002c0200c55500c5029100015203683e0052004131805211107040710704040da08010043e0081148040d94020401c0c4480c9a4031003000a0b03020008a900640045c940e1004a5203d108210032035003600c296810b200d200c2c5008504044e503c0400c1e0300f164002d40e40c400c481d5091900001c14140c01da002000400e540307544c0149148a504102520f85681d80d5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 55160974 1250 55159724 55159739
    0x10302150c010f0e0d030f150b160209010b0c011a091b040f0f08060a060b040302040c02100c020705010e031f0b12030706050609150a060503090c0a03060c080912180406 74
    0x4100c00145a015040480d042c54540d81510a01c00e0090780341c10100300704da14800048008585a000707827402c1180120302d080c0f09098441c04011303a25806403500c901541d445080000d03030f4110340c50401e41e0303500b400c2040c141c0c080040d50000400c04001d1600100e0748038012003c0f240c01d031000c1501284601004040307040002650410000c004050b03280041514200400d070529402030044510242455800c011907100281030701d0952390102c400007000c29500d1016031030076001c0d0b0741c01d50b1564103060040030101c2d0040f070036104850b001c0c5c0351540c0b0b0718104400c2545400d40c40001a40300d99585184035125a001d6211280c3c0640180c00849a101c10a4026280d41c2185034101d440300d440300c0c20400300e418620145500041c0605d6899141c040303c000180c6000d0346c6010301d000300b08000c800110b0014003000540036030600509043c070010340b42c2c201380026141a61511001c14944404506440d40001c1c80720309015440c8051030400904101c000c1601060300c0100d980161a05400b0a188 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 55162224 1250 55160974 55160981
    0x601021e0601051801081f0902100e120708100b030f070905090118080a0c02040b13050402032806090309150315240503060d05070b0301080c09010302150c010f 70
    0x2044000c0c01070409625010400014000700002c034003891900500400c40700c4000502a40e8010485036031542c00b2218060881c01080e003400040c0d480091514121116500080b19100b00d45080c1d0f02d040c80010355801d0b00760342d01d0880c40b90181c554440915401c075441c160b4003041500d58000c0c10303580800382d214241c1d40b40400c242c0210050343d54550500460280034803601140d1032000b00300c1038808040303481d040c0c80c1c1c0c0940c550260601c001005000c00f19616640000101d00001b0b00703070b00d00d0a00d1012014001d00084800324041d10601d55590061400703415a08150002021140d03514125a525807002c1c1c10034000c2103003448210000490300e500c20f80083c0b03c03500d10a030b80000e00d0003520990600c800d64290702003600400a04400d07114a00ca1450707000c0c2544c003e0411030343c0c075103584009c1642c01c0c5008102030700c07600038420046000c0c2346142c0214101c4a00f0310803a2407034074584082002050082c44000c1d8000c1c1200711400c0391081040207459005041c03000016210415180c0d2020b6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 55163474 1250 55162224 55162273
    0x102040503011b0206090a0b010e0a1b030f060902120105210a0609120c02090c0a05040f0303050c0d030b090f041401060806190e060a0908040b040605031506030709050108060102 78
    0x1030960741d5030821120f07981040b1056204c02510000c140e00c0b0160386a83e68248018010380f4080b00c4000d000a03c0e03081d69807c1826400301d1415070950040b201c2000900414001009a62a904108001071151224000d0f030712041084030148050740d1074582007001c07022008a075100400e041c18410064514180401c014803400f910002c110b8a441d0321300484240407813100c420a1005046000d009a220f008109620000d101c0306030341e0300c00c21101d080d100e6004036481002801c1103040040b040552050203481c001143c0400c60741101c0c1ca04006806a4182c008440c0c0c00a00040000f51304403054410a038019000b6208444a8100310038078500f510f04941080c608cd600480503c0140b403c03c07a6405410f1b02c3c841c000b08a4a10202c05884d140c0030050300300c103480b50701c80b040b940c20320403a80100c40041c810b02507104d40c0c5d00e5031004003524a400444035114041e503003040901a070304210045a00c9035405e943d5048046045c00e005580e00000540002c4c110701c5016490f140c1c2c104242400c501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 55164724 1250 55163474 55163501
    0x1f0c1205010603060504060902070b07050313020303070c030b0c07030203070602130e1608071403040b04020f060a020f011506052208010207110306090d1b021909050a0f050c09060c010204050301 85
    0x16138a042000b8082a91042ea0040200c0340c410403101c0045800440c400b03401901514045640752507441c1501000400303090041c2d410301000451710300b0081041c45502c1140e00c80c3d00b44010503034543c03100c0321180c024a41c000d00540c0041110b1400110035a000700003240b03140114840e4161207806080100c14200e1348403500a283c81034110105410010540d405120f51070980c0403800c4a6400c1c000502014000901e4082140042421550b440c984481003d0024080b191070f1003801d800295149140100031890b5440c00e000c00c103018402c82200c0e030940e01035841f124a01450300b00d51101c0894102102c10000c1d201d080e000ca0003001c00e000401c84079000b1000001c03a1207208042609054003c0c2000005600c42d0915000e001d40220704910092065911b9200351840380c0089802100300c42c881c0c04100e8805e0781d01003842c0d0340c680e000da405210911400c01c1801301c07100c611012254190f80c003c1126006001c03d186910307100c0000e200c22001e90303001500302a40c500c0841c0c01d403500e5502003070307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 55165974 1250 55164724 55164731
    0x30f0301081e0d2a0618030e090402060316090306020f040303090b030f0c07030c0f0b01260c060702010504081603031206030317090c030a03050406020f1f0c1205010603 74
    0x82c420361044803050076920001c400740c610000c034034601414100d24201180a00004800040b1204941c0e915134031060781c1062052042080105100d5601411103404501003110a0a1908035003030082000d84a158050305440c9940c42c0c2c000e00070303800c012801d00f41080200c02000440025210f0015144464010380001c1c3c03214294540a002d000c02500501d00e8503000780b0404c201c4444c9411800d4001c90060347d171660328803203030a00700c0381403070007110180c1507150781d850200400507120fc01d80e0480c0c0d004000c0001d060101146411610001265a244c0ea480421030140314a04503004001407441410b02c6494642d440503c07d0511100001071400009440e070200141234008490300301c90a000d0b141005424203503a0060a10000702e0408200700340b800c00051a900020032002200b020b0050495884841c03514000745a80d119000e8a4014050a1b4651464640005403118511060ac030000c10700d10348903100350010810003005008014842114000c19290341c42114060940f50344c010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 55167224 1250 55165974 55165993
    0xb0409061406120c12011e06020309010c0b150d0501050a051e16050403021201060302100c0203061801021306081509271002120610031b11030f030108 66
    0x14221001a489000e01d6224044421030541e10301088900500d809a40c45005031219046064180101540c4002e03042e44c2034000301d400d080258030200900f00400744140c1450b16980d04a17142e003d4850703c176000c2000d1310007d00020314640f00c01a48a00102d43d0030240e400780b8000909417520007031056031265510030901c034200720f0038000c1d9507004191a02031038000d840740500466003074004020b4601b1245d00007103100f00c0351089003280c0c001d43c0c0061500ca4426004420305000b41814070081303200b91848101d00c4440c6001e0301044c079101d90014040d1219030b480101d16000407405655808081d58204060204218a0190780000d4589a942c1b02c05a207090f2190412070310040105612482a95003000103804644038410030a00003100c1c211401c00e0f04901c905c0c034150506030012007450020079203140358022190244d100c0c510403101c4035880079080c5401c0c0c003140e2444240d040c00464140001000741d0149800b0360b528014002228908034036505401200e030030a0300300118981202e02e60 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 55168474 1250 55167224 55167239
    0xf03150912040302100f03110d020a12050610081302030307050d09090207080a0302130e0a090308150609010503040c0306050114130b0105090f031006030303020403051b030a02010509190b04 83
    0x480780c120400040074036142c02c5400003400c0d6880c20401c0f03070411950352900069184640c2210000c1c0b48402d602507212200b040a42c00a9003180790060300040c056140c42c802603803140036050060802074001500825402800c6070b00c0c103801010a075105005c0402c1c003006031810002003013441e00800283c40303032201b09075004140c1f100551003150ba6500501a94004c03e0b9094101c074205905800e0041c0d60700e22840d081c0c0401c1006600184815030454100000c0c1002d43e0040c0c14024030a56403041650b417a0398141840310a10041182c000006010050040d40140c00071500306018250075280a59030341e44078001c3d21000d0700700003101e03034211400b50400d040c400102030000082d04000d1200c900c1207000203041c0e00a4483d030764840c0d07a4402c0d0303a20981d2014401990800803921040c0a140d846e814080e010798003503c0100c5591007080c0340d40d882c0c200510204101c860004008c0d040303500e00b6400442d580e030009404280d00c1441d20580c1021446294007603801005003134030b201d8485241100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 55169724 1250 55168474 55168483
    0x5060d051618060c0f1202011a0411030403031805010c03020a030b01030902240c01051305070519030807020a2705070c0203060604090309080d090f0504060b180f031509 74
    0x5560050006a00355030142d5075030014128250781561034050020103003400d012800030340d40a009850386c03581250191300c0f1603041d004a40050882c4107441e0000c6603a8050004a4002c0c214007458200300f800420002846900a040300a82250201100d4859920b400742102e0100140c00080380d40001d07050b04064145c003402d111807409080410410702660042900d240419000541040c200480307290b540d40c1c40c0043da050070000800070811450100090205001100c0c41a0760074414010009000d2800881c41c003800440c03110f1070503180d13145a1b110156600103040072680700908d50804510f20049048403036610350061401d10004180b0080b190454201400c03280030000e0b48090440545c400081250f0480c1042d10300280c81da6443c00c080300c0c041c080307800c05111805070307541d24520160b00c00c04280c1582e2907800c212007001e0703680c0b0803c81118a14454042040c109015030b08610142d80e01031048988080c05000e1001c041c03000090514031740f0103403405c201d1012018030106413810071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 55170974 1250 55169724 55169761
    0x6032c06061003020c0f210319090204020706020316030f110a0804020307091103091c081f0e102111090a060503070e0a050601031b0507020102010605060d05 69
    0x184041100008a0155500c0310002441e090207a5180c1c1e0460202ca44260304980511403080182e40101000443c1640c0b5000e140039403071950030404508007400d409603411603006803050002000e240102c02e03102e601404142400307a900c16424011035011544900095100320010b189100511920102c080e00b1610070408102070b4902e003088a0040f00300403011202c40701403c0c200815607a0700d07032000919140581e000062950305000c644500b5400a101550050114009407040d00e42507000000214490a072030380001490383e0081814001e00504c0400d690711565064070f10940c46900c15040c42100341c5501400c41c0c1c0e52141000541d400482083c3c1412514a80c4c08041c100c5845e809061548180e070350307200741030040201e100240f02c0e9209200030480641955141540d401d07070b03103641c004112400d6503c1803c240008003192311034440d0346826480c5103042c20840802800448040d08604800c03415507507207980100c0c0c142c1d2885c002d0902100e0030040400e8a01d002a4010030038400030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 55172224 1250 55170974 55171031
    0x3040f050111011a0f0a05040c030504120c030c021309200f03030405152214010813030f03051005030601080703050d0503100506030a1b030902041107020105030a180503040603 77
    0x6240202c5684c0c03166040b2181810480b04800c07030b04451400540610f12aa0006901a03e400c66006460703406400203403003140a05014000d0801d005000d030b070300344003203040140045c0160a0030801403401000c00c2c4995004c02c0000180c2103034a0b03442542d032a81083c11008028444480d4900b6498400f030310481540c400d902560915142c04041103140f00c100c00c00254a400210710005848404050803150481186c000c0c2116951003a2003000c43c00302a90060004441c000010105c000300341d10380000540c10ba5900041c046160001c900515010f080200a00240c0f4000211550200a003501800401c00139001d100d1031813404500d0400b4074030f581c0f814040144100b00050840007400c000700c40058540320b59a031341d6004514028152003580f404003c645401000e60039505500c0b04481600c00d803000c10640c88281c080c0c00060041c0c50000340005c0003080000c150003000d03006501c0710070030b98485481c1840c80765a100e0550300160001e03c002580c0300b801e0780f0303812410503050400400a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 55173474 1250 55172224 55172231
    0xf0c0810091406060307020a08070f0c0905040206030402040e031b03030f0108010605030a060b04021e0d050106081303030f06051c03030605042a0e0604140306010503010b0a151103040f05011101 85
    0xb4080c11100b084402451244501008400152810300a000d00c01a43c0d500148090360344480e40f400f01c00039144100f05840e00c441114000c40c0d030703031010f1003451b000383e0300100b60509594031075081002500756800c000c40f46000034030104c0c04994051500408019180b0080c40c0c5074a0903004428941c401607122260aa0600d1402c01c800d44011030b1142095030800c00100b01d49442c0d0001c20044d10a10507244405d20700d00201c00c08000f4020040c04070f0b107040c09814030460341c1ea081c04031850141a80e0107141c028850f6035600c0004c1c0240c2c80400406c0c0001d4001c9801c07941c60000505075000340141007254030000c0c004a0130036900d4490440900000c075020010b601208080060300c03080a86418240301155070301d514000d004088660b039201004000c0c9590b00d0300c590380000c2c1016111301c2d5a00030310611780049040e06e0107006400803400c000d000801d842d46010f01c1d10a1344690300101201b80300d844222010b20030f0302880180090400d01800007611031500c000144011380441c02c445090b40b6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 55174724 1250 55173474 55173491
    0x14060402090d08030a15060801061106040210030222030f02100f020a080a050c06090313061412130807050a0210020c090a0507030605030709050103030e1503060103020d0f0c081009 79
    0x1500500e440c034180e00300e8a004c0c0c59a98980c1044024120720146181580800600141a9030301040c59411381d4169aa15881900202e202955920040d0350003036100ea000100450120f2003139000d4114296903081200540c420004200361f00f151603003080d0383c0848010317101401d6007081c1240c000b00c12603e02e000202c0030741001000351a0042c40400800c0d4100001d0f440b80c07403e20841c20349030050b50000541302c1c20f06020840c16a40d034084802c001a8441400c000203c01d4081d8003d1032443d00410901c4c4d01e000ca0103400f80c109074100400e03581c881160314030340c0b50114034a034019003d0144075200420b2901030a00402281545950200c401c56005422807035868480000705030300b082144070080350503221550309a015141603084107402d4410900c0000d0300c450181c1000d8100c0c1c0c000d0f141e80f90150081418801041d4001d000d50300c940904002041c0c04c0e500c207900401146a22220005044150701030880541c1d4415201400040f0404240481d10b000c0c480541c0042c1040340c002c210404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 55175974 1250 55174724 55174729
    0x9080d02060103020d02040b180108070f0b09040c02070806010914060f0d02120c060a030218060f1204060209040e0a0204050c19030e0c040507050d11040e0105040222091406040209 79
    0x1401400002e00503c0301709980400c54550740c01c01c0383e030400020030408020502590785050300c10300748100881445008000601c0308540c2010034281d8000c005c1c401e14060854042c003025202c4c18452000b188240400080c00380403e02503103000c0c04d0410302c0070074911910341ca061040c0c400601300a2286411020481c12592907105083d81994141d0300c001650130707020710139428a40000c42440e0130860010300d03644070540c15802000d03040084101000e6403102482845102e0080128400e00e1010030800c0c003080e8101d1410841e4032500c5100058a00001340c00420261a114624403000e64485181c1c8802c41c03602c0d004250740f107844484d40c2410032a6843e0f21044c642c1301b00fa56142456915502114206428400310b000a0b001030024490b608141c480113141c2d5121003001c0c0051440c1c003a84901e1090040b0803030302204d031700e40154040f0380d0070301040000a600c582a0f810780034803811400d81844d1001c840d400010101d010000070010300c0581745258000004100910540c81040892000e0b07 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 55177224 1250 55175974 55175983
    0x70f0603050f0112050a06021b011a0102151005030109060b180402010806060d0605190e090606010801090c0219050303010503120306030a1202030c030d1a0303030702070b0d090b01030605010609080d02 88
    0x1590f000071481810700b113a040c41e03030030441d403d40c002e450f6500000b102c00b07084951030322540301154050000c00203c504281440060304e10190b00ca80180c02c44000e20300105081d110b090b41208000340c3c0399004070f40c2c5400080c21951483c07400c07640c4a49896410b42039180000303456541c4a0000e5007007000d1710341640003d107001d2004000341e2091b000450780810303880c03150f07000602402c0b003d4007410043ea240c0103807056082c154402c2281c3c900083d40001c85101001c40c000b03000d03400613140c601c40759017400080005070644e55040403c611130303122810110200ca40003000d489020780c01071940d07035060105040c00e1685071744440901540810034400b10b07440001c0d410600c03c0e04203410b40c958083e841c0040b402d610800b4104821440041a0081e0070203c0d40e0280662245000714810620380c0103086c55245e010484805015812201c001c10000000e100140a82e01c0c3d43d10b4001f81810301d0340e50720806170b002070300709880e0659540700602c05190024410006020140001c240d0801c903054000c2d5036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 55178474 1250 55177224 55177229
    0xe0c010f1e03020c01060b030a05040606060212032a03040f050c030109081b070f0305010501050f0108040201360306060e07141909030f060b130204060c1e060509070f0603050f01 78
    0x2c0550020310b01900120070345c0318034042c105001da62540c81c20030700b0045000e04819a403e48440e40380c0301000a10500008011070198107820200d42550317980c2080305140407240071142c00b41d4000c00350a214071403400c5d0042d80302d030313203e600d500341d041402c0c0c01c0c028904005410914040d031701d0400c01d100481c01c140c0075602c0108080500d54580c102c0300001506000c0030350f0080c00d5032032200c1004010844c040d00881d0507079000b0b880c600e400002e100011294000282c0e0040d001c180c208091440b04034103036030211100440705c1c46011000400c0400003419075000e5009881c2155180001c5c045030303114042490b08410240303820710001155980d02c4d8400e200d1400d4044492041c01034400000d8001c02e10140256004418901c1380030543c00d280c00500916a110741c0700b02c200203031901c0003104074400d6905031041c0b5030301c1961180090303540c404841090390100481480d13045010001807903900844c0c0c460305c02000a0820f02d885c0103001c0c07641e0541d58010318281400e0a041001d0f83e00d440058904 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 55179724 1250 55178474 55178477
    0xb031905030909071e03020a0804020405060315070905010e190e19090602180a300203060108012003010e0f070e191a03090304060c0302100e0c010f1e 66
    0x424a0a4a0058a58410420180c1c0c008184904200541d80c0003100d6014103030541c081c0c0003400600d524200c0c100d201d031040150120701d50308049000360403d45e1000790700c1100035045940902d072000f40c0040c406c00444400c400140215020702c03955038040d02d090f6035900c0030348001110b5001e6030208020481c25000b0961055a11000240c041005a800e04e0008580782c904000c01106814484080d500108415030f01010403000e020243c00c200e8900812182e0503c04125952100c13080991030100f08015001a158000c0781b0101595062050314002e0800a000041c07040c008500680194405203410704021001d0004020700c40e080044145c0c03040c0e4242d5501c815030341e0720b241643c070201c40c01001900000c844a501a800f0364501c01d2000f61213034549100394042072174044962500c002c032441092034000344010010300c1d0003488000542403080c0195441303151440b40c042c048507148584807800d40e10802110140c0d582000010304111000c2c60680c9050701071550542c90340303004011040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 55180974 1250 55179724 55179763
    0x2030a050604110f010e06190c0f0302010c09081606080a090204060b091c051015120b010f0f08070302040903140d060612050f06090a02041502030c070f0e07030203040f02120d020c040b03 82
    0xc80c21071040d2500340d0102d07402415600030720322b10b0900074000c015004000c0c0210301d442501141c1d095000507140c02d50040d010f060540d041c1410340c11a00c515001d022928603503100c00e1340b0001a6101c1c0250009046040300c6641c441400c0001c10a00703012100f03902481c07201300b180030303400f1030800700f40304907022070100c40407079014078400c122400700303055500c21030a030480b01c08034000304040b490b1500d04840d12078030381c02c2449072291402200e40f100c1e886410326a51006d4410001030410b41c00032541240282406d5004045205030740c40103901800c44001c800d80c1d604028010741d50810b01c030711140c00c04d22138208200e140c8404481c0d02d16030054142442582c1110000d0b10f000d600d5011076020b48600b00b1002d0000850f1100a035807500310b884a6802030080032004104801071400400465542041b084025210140309030004d600c060700644002c0c02500002c0c0c09a1070384880c213603031154400014080349084e0704009082c100d0a08000b8070880c02d09003d21250344c4c001801c0b040d50542c1c41400c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 55182224 1250 55180974 55181017
    0x1170f060a050405040302100c050309150c041e090c090f03061d0d03090b01082404140102070305030a0b1905010302090406031703060102060c0c06010b0702030a050604110f010e06 79
    0xd201041ca40e11465200e0300300000c00040590101e800b40002c1c1804000303220401002e00c099845006c00c4600140c80e502120102d00700340c0c5030b100004d81000d10a040c0c1441c1c1601c580c00070181110320811800d2044542100b04401503c0d84281600158940780c03000c642802d1040300340e03081640b4840a401c003625100c50700c1c1203010000a4131b0030030030341c0f0003103030000022071202070007901010788180d428550240001695850110790041c0d9180c110010000e0031203410b400d0b4054030f40140041d124620070020707280701032909100402c0200e02030b0b01c85940381d19081d047d031400c0e15565086503014050310401c202e1030742d4040300b221040d075009007000740c2c40b001c4030808600140a00d43c0003510389040c0014000b007401e49100114046c18007070b400d440c229603c11000c48418494000b04407040d50054004001401020000d081d250388000e007516520480385e101d1502c1e2100c103960540d1843d002242c0070103207240480006102000c2070a00003032545200d40001d9803401001180052818510740d403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 55183474 1250 55182224 55182229
    0x303040f0b06040f0e07050f03010b030d11030f0c0715170a050c09030a0803010e220b0a1407020606120c031b0d0c150207051806101e0e040b01170f06 66
    0x44c1c5003080d249442088104185000309a1720703142441000d000708002c5c4903d0b4070a0406018020072460058000c10b15403007400412210300d02c0c4d0f07001d1600180814000f04051880400c003c0c403404207520024148141042d4204a03c8540c3d00b07504800c0c808449207040c2e0000640c0031040d400750502400080300d5444500503807a901c1030451160f0726024681010040114160265040e14250061040036507140405188480b4500ca10705030000804485440019240800141c2c400c4141d0004242b0003207800c68068104000d40307140000d13801c440c042144504221080b414080d0901c0024018549054003081c2c03103281c8034010300c9020102100310501074a0700b00d20180e200d85d0000010300e1032650350b01c024401410200c4039200502520030002030524108251803c0d032110031b0070180c03003912280100490054964440014003c2c091403070400481e40741f203016440341294803a900d6240360002004120381c844400b4a05204c1c10701080c00d03e0f2440398255540c8003030000032900e02030300c51200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 55184724 1250 55183474 55183481
    0x70f031d0406030b1009090c03170f04080a0219060e0d1109040503070c1d06010e0111070803040906080d020a120c0206030a1407020a05030307030b040b0d030305090f0303040f0b0604 80
    0x35500036042c11000420061542416441076200040809450703890703da07608160f6060010151044610600c2400800d110b00d102142034aa1041c0c46494030103090091070103504544d1201c1d400b90040882042541482540741907005c00340070704030281509120010380140e07221102d4600a190512404040004d030741d041d56a0711200a05004451034140f03810366aa82c000c4d1170444d070400701c0002c00280a10440c10b00c5c442c0101408a024a44e50744100440390159452401410000400005038044801b80000d01c0540480c00113180d0399810441400e06541c8198440c1c42c00da8000156050900c0e03001c102c0c421400d501020204520300b01c0b18081f148175201301030283d48440b00205000b410407255002c5170810b4058441d55103a6525018141d0b00c0307014000028245400c10000588002d100f82d0140c0900000144001038034520000814141020340340200c0100e503645060082c0f00c801008501029200400118070b0b500d4942c0d41d40f50008032800e0000d04c0c00c80c0e0080400c035141d4640c2c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 55185974 1250 55184724 55184777
    0xb06040503100507020d0309050316150501090509160f060804050a06020a02060103020109230402130905040602070c051207030201080a110c0705040605060a0c0b2805010f0b070f03 79
    0x10300702c50310084440c5125008100c10b9640ca0050302c1401d800c601543c2c00b900840301007540080107581000024246419913040b200781c2200c1300c41080c0b40311a0401030901c6106d020302444600024186044480c442c50f041c1c3c858007000f4000a00c0508000a0512580c002d0550b041d5242003080e0391240d141003880c051500303100501c1c5a0001c5240c0c0c440381d6001542c00d040303c1c001d0ba101005d0340e9842548a48100101c40c10900f01c120059516110303041c40d4000749840450802410005955042200120303481030710200c6042d078000900f10700b4096078117500c41c09401308075500c0d84062502c0d140c0b2076945045210003818460403800083c204011a44007886059090250701d0b901d9500391001901c0d084075028461007180360003000b2806027800d0041d55070200c0d5585580841144c0c60301c070708000e404010a140c6080f0861301c0c15801d410100c81000d15051010300002c203140d41040010011080c1c5034010082d801c2c81400400c02084869041c04c0c0001c0c0c05007480b44200d20030401d440035003180315 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 55187224 1250 55185974 55185979
    0x60305030d09020319030309020112090506130201050c0f0a1a07050a0315150f14090f04020705010b06040e0103050601090c0c020105091906020a1a1005011d09040804030b09060403120b060405 84
    0x400c804414135403d81c02009032341d4800d984125140c00541040b00454204180180641e4400300005c0e41d40c1c0d0400303d12030002070050602a04200301e00024500e0000403007040d180036004112001e08004441110b00c02502404024141a20300218018200c1c0101d210980c101500c907003c0290000314032034078001415000001c0c20803144507050180100780c2c21501c3d00b000070380c1c2010f2215505042c0003030b0f46010034000c2004003c0030380b1314100b001030340144100344e43c10355039a0f022441c19030312030005100070064900c010300150700d141089030400c04140d1046102074285044145800d0b440001c1c100103030b9090030229140c4200c000030800d074201d4411031011082003500701044094000480310211440354020140e050004100d0445540e425a00460b6082c00c0880c10b104a60207045110783c4030754021510703002c1000e0f140001d01e0103501a00c0942e0081c0001405009001036203030f84580c44601030004200b03508040d60001c0583c4d400b02c45c0c1da24129601d24520300c00da40c48604840040500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 55188474 1250 55187224 55187263
    0x4050301020d020306030f0601050919060906090507020d0215012102090a0203180708030306150c03160204061202150901050c060405030d0501060f050304060c0504090e0105040c0603060305030d090203 88
    0x42d03102c260000d41c0203403842c0744244140d8078040007010700080d1580c140c03007014000d17120503107620326950101c40404000107011500c600c004104202544101d4008064071107002c5040c1c105004080d040100c040113a40454200b42428414400d0341980181103460501e04003d0758602694140500448041d00960040d800c0060001540054000e1400b0300d14003c245000301d02c12068455490000d03100d5003002350024000654545002040c43d40c600592480c2e00d880e00300e05a61250856001d0700c0d03070034108a001110b0300c00b5400e00e4402e400280c000741843c80800031080d00090724078680700301160381902000070703c1070341d40e4070940a407103100107500202c1d600f60800380390054680c0c200310b046d0b0414521300720000604900c40c10982c9045401526081e1850315191210b0001d0890050301c1d03000e2113410440017824500d103100e800000c240381000014541001d00d00301d10f05055507400343c8201820500f0a202090000c001c8900e40034402c440003807141110300c042424442541d4159107454130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 55189724 1250 55188474 55188487
    0xe060901050d050f0a0b0612011203020106050307080703030306060f0509121f06030b220602160c060c030206010603060b0906160c0e09060a15062d050d060902040302240405030102 79
    0x290601302e140176554030741e030501c0101c050f40207025803030240d03880c1c440a1140c44001000090302c4400340105241c06403002182c2c09440c0c0002c1380c5070081682c0140d0080d44aa40e04209040e814401c000182007645044440c00a030030000800c05d0041500b200e02c100b0340d000a8941c441c408202d50360002040190b0001c2089000741410010080c0380300954040b9800c0d0f0000d0074031f842c0600341030709802e0412020482c0f460552101e1009402480301d054032001c41c0b9008902207402544a40c000b8007803130f55020000000d500d40281801310690014080c142000020300c0341002410560700350040589000352203010004268142d4200c0b020b000d032117800c03403c1000c945d4814801c00d4510a110000c1251080e8903811804011103054040800c600c4035000028012148600c60400712421040d14116140030028125902c070b0340d5808546000c40d8001440c0c3d00c1170301d414011302001b040401c804600f82803958000c2404121b200e1114520041344080d050f007c101d9040076100640340c040c00031512408e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 55190974 1250 55189724 55189741
    0x2011b0605161b022d0315041b0b0a1103120108030901080702070b070609020402091002060612060c0f03060303040b210109020315040b010e040f05010510050a0e060901050d05 77
    0x3000b039145400045030401a001880248960030100e00d0f8040e100880c00c0d08245580315007200b1410804108a1046007005001c0d50104440011411811241e201505062a00b40007036100b0a041c1010742101510800140c5081c1040e030b1011841400c110b0525001408164250320a102e040f000007041d540011482040000103090021020b072520304042d02d8100080e695802d07541b1880c204a06c0801c00307880000c44c075811824070039101600140c180b181c808000703100001e02c42170f11401130b4419000c21030745140910700d40440da6020405400705042c10100403100b44905c008105005000101181d070603182041140c005269a0104548842d228440070300fa007020f403080c0d00311005880d030010070b00c44000d2003240e0041003110b000d07a4072000b00c101804043d114100d000c90600c680c0f4110b13100703107032554051151101c2a562000800358180020040002c2e02345080404010041c010000010781080039503400c80740488040b500c5802d4800101c800d07108480140f12480e040000380b101c990b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 55192224 1250 55190974 55191001
    0x60105092b020405071713110904030e04060902070308041412030a0c02010b01030c2c120a06060b0a0813050a0f031701080c030d0e0409060e1509010606080402011b0605 74
    0x7184226410f01a0740ca56007800c980d400001249454081480000f207000180d0040da885d900502c42d690741422036860038000784007240c040b6410b8012030102c5024144520b0244122809481040b101f141080400c1c0c40040455100a200509038101c0e607a921326030722810800b161016541402c004e40d24078145240d07034007a11000007140059824040042e403d5802401030326017420003651403480c082085031001100c2400140354680e20018004024035a40340c0d0030410485c8503481d8005c2124680a1402c0c0046270501da00042c4622014025191241ea00940443d00301e03c00c401400031071045800d03c42d00f0000e00e91002041c070b0429200010800d0b400c02c03941d101c1641c4440b03140400f41c0e40c804646446000030400c803603054101102c1414010b004d4001910000300c003801c00645051680d44000864851a0300003010f913105580721070b40401c41014540e48030421100a1080d00e281c6800501102405080281800510704118404d0714504001c050065042a01881a4103204400ca10007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 55193474 1250 55192224 55192309
    0x90907080a20010e0d02010c1511040503100603080418020409022106220e0709060303051207110d031109040c0906090f030c0902030705040e010e0f01081506010509 72
    0x88181c0700b04481c2d80226541c15500c0b9000e0940784410206600444449110a0048030303902c2500ca032242c00000b062288182111440807016502c5050100705032500d617804228841490800000703000141ca014283c83c1168001801070298200701806a00a401182c000240b4140301081184070f9244501c2e00b460041c0c5a01c216440d00c0c3c40d141c0510160740c14055904680c90040f00000f0121a200c0d4444402e0b2680e8034180c50074141c5591075030003070b00c040da40203400041d000300d1070340c1e010503c0b0403440e900044c2038188080400400100316440c3d4042c500c840d014140d6400180e45800c01c1801121000d51005104101e448154440603241e003c3c24080c800004ad021000850120b1141c8038490036280c00040c407655043c130b0006200c0203503200402d03000801c801400005603114990710054082c04440340e030400c1700d20701900102e0218005038031001d020b9000c1340101c41e0484142600070340195080c42c0c890768851222000c2024400801c42c100190b041c070302c1000e004515003010f280d08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 55194724 1250 55193474 55193513
    0x9081f050603010e0d12090510020307030e0601080d030b01030f02120a0b01021207110a030807030504050f0f10030c1806020f06071e05030a09060c03020310050618090907080a 77
    0x1a01da2005050884d6019411081c056102d0503241d0b03c0f05005450703a8020440510020800f034500b503490324107107102c002c2180c9070315030003105214000341c0602840030144a0703400188200c0d8500f40701c0c0fa1359510f45422103014940d039180e100300540d210307400c00384010001c1402556980c1c0c03016404904450100c640d50b440390f20b07014882c9015031001c82c00040e140c1543d03203150300708030144c3c951549200c03100092030340c810442280000043d4152000d080c1c4c09019441d05a11a03180505100c201e01503070014521540405092000b15135500c1c00d603003000c032010f00d4006080823220724182c8514010284680920381e01c1c00002928a500051a400c100c030070100b80c4200f0780361004141c8598540840084401c0060709200c40300a1155020310f03881200c0c80400b048505160312500300704c40302d44003040d000a40010030005c170a100c081808004060907180546401c02488805038080c0d5201f80305403040c820040815200c332070400928014001c0707007080d01d00c2c240c19481e0038030040454900054 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 55195974 1250 55194724 55194731
    0x102060106080601120b04140c0c010b010c0b07030209032b03061d0402010f1407110306091528060b07140703080406080c0706090308072003160309081f 67
    0x90031032080902d03e01030803040e1100d03a61050310017400c101500b0102012600641c0d55802d290525245000742c60148504005031581d030f003901703ca03640c02e48440106e0710b1f0611489607031040c0006c949442c5958402410302d00182c03980202400a07041809581c400002c1c49002c101605105c94169042c00315910961010010a50366940340d00b9101c00070b0040313003803103c00240060301550144400030b00c11000c84c944500684210a01d008440c1c210380c0d4161420340c050403c1640c2c0381002c00c82540c05c410a04010700030300351050810766130140000d01e010b0b113401c1d150140e030386690000c000c1408401401c0301d0602115450b4803039030301c403504509800c0d1010241410a2001500082514000d032900000e03064a400e04116003600e0b9407002508144120b041044400d000c00c0c524402e03d100d4501c00c3d40d0b09806400c2640d0300410000340401400200e1a80901040000400000300c2e0903042480c140c0c044545018103081d114400341d540911404d00582d10185101c24108081c58440c4031412401c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 55197224 1250 55195974 55195979
    0x30607050406090e0103150b03070905090601030303050718090b01021e160f1805040305070204090b060102010c020312150102030c07080d0210060305030d0b03070b07050102030f0a09050d03020d14090c01020601 92
    0x6050f1030300b01b03100c060007144010301c1144040200b504200b0310a84003504440826a440c081041203d0048031142002d400140060041507030601807140c000c107413407a1181403035000700150440d44a8074031646120545d100315828459000344540c904880c104104000c3c0341c420104480d88a458211561071550280040821764920380780c407040c01d8501c0031520a24105140e200000140b0b405401517040c041c082c44050700507a254082c00710b24520038080d408050401c0000a82500d1032800d01c0c10554005001342c4d0700124080307800700d610440002c4480c0d03240c100030006070305610a10341e04607414000d40038003107004180011043d01248aa80c215041c41c40c400c020082103800d6400b001b0481d810810202070306505540010600c50001010b580c1381c180d0310364400400f41e0101c401124642d4000c802c10049464280c05076501c80c0300742c8018880c031255540d925885061181901040c50742c003180c003401c420000d9022614003050508007183d581086489290b851601c031104030b0041c400c0d40d001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 55198474 1250 55197224 55197239
    0xb0a050904050f040b0c13030602160215031b1803070807030b01080d09060e0301110c0114060604030507050108040614010303050d1b0f030c0e061318110711030a0203060705040609 79
    0xf41481030790080c10301607040e00c9144040702c09074402900300004845581d40400800c0302480204000206803600a910a8a40c0f05004011364000c1c07856040c86400e104204003c04454009071800172070100311b40c3da405004c801d5400881d44416000c3d010322800c1c0e00490108400111503098078080c2202d80d04ce685c1e6030701ca0300c1c5c0c0c0e2003c48602c4400034142c13010801506000c1c00c01d010410780c00500120740c10b14055014840c2d50030403180014660f44885415a501d102212026004102030740c2d1070307240c5421070b11502d589034807074411a41005202c00015040c4049580000602090030b50008200d581d41d040042464110040d480105c52070b00e540080c0c451501440c04240d611162601c80c0d200c40a841d059004100441541d8203010140c0c0108051742d58180003890060b13491142c400950341441004840b203c007070488081414500b9450b0342c0326426040544540552207481240b8aa0300ca5000c00c1c240300342c1000081d094441c0d0001d100302944c000c4090030035103070380f907036007181c403a9a5500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 55199724 1250 55198474 55198501
    0x50403110d0e04270803060109060201060b0a0528031a04020304020108061c140d17010608060f0f0306040f02091018200408030403060f05010308091002070b0a05090405 74
    0x20820046512019544000e04241c0c200c01038104000520707454136421084c6020320101013003002ca940c86000010048a076070421039000c0a414030b8030003081041d08080f10391005118560145041c0701d40404e00c5c02104105001c081c904950304c00fa107a00001c00c00c50b0103000742990b106a0180c2001c0c15000c2e0b6141c0c00e062080c2c80c402c0d90160b58484c1140c840c0360a012922440c41120b00c1c070003d4008185000c01d45000c0d0591550740c0c9840100b030404051000100040400e0045000d806c030150010091168024401034000740115440c0b01c140001c040000c031a03031400501c1301d4042c041c6204010600842001862680d8029200e1660940d18954607644641c0c0038061711003801061a0b60b40780080d02030380049151300203003e02c04407110140840a500d50000c0e0f1040320161320004050040100e28080c2c01142444550244440c2d4199500c001041c003400140c0740c0100a05c0c10a8214107208014000040c0710f1070104954402c000f00c1d004241b80c1c40003200354092070825010404006a414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 55200974 1250 55199724 55199743
    0xc030601090e0604062414030d050c10051e0f100f180209030f07031209080705090105060901090f0f080f0604080909070c1502070506070f02100f020403080304050105040311 76
    0x80503106a035921703600d90005200382010086444e031184404055030381c0401c01080680030882441c070300e28410b0b03c00c261620303001c50070301010850144103160040390000390521100f40b203804003060a5444000c0d02202c0c20480c1c00012900040f9018840700c07001696a250048800ca415401e01c20b84030001c01542207881d210f00c4c4180303450002e9012503000b59070302900305540d0050a603003120f441580350616200040d00305848000144051000720360b0820310310001040300a0182018a20340000912074042c1481800e0240c0c00028130087e041e03125010b59409420b1200402e82040d440f003140052041b190b02540400348140292950300e0200024064412175020441e81e00d000307601c0e0240001d505e00a8040c0e018060004a2100086d9a0a11030155003611000c01604c5541a0070620b1902401500e917605101c4180140280c555020844a856140d5690302082628030b006c4020000c1c803c55201070b04211300072060004000381900b190b4020b80c000da039510546140101541d85402101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 55202224 1250 55200974 55201001
    0x10c030207060c030908010504030504081902030d11030c0601140f09090304090905030409050a02032211120c061602040c140d050402040b04090f050105011403070308031b0c0c03060109 81
    0x40c1c04110540c840c0724004111407007803030308468256a8540700c07170075100152002c80102e04046018050610200442d211a00d000c0c000d294042c5100e4010948904e00c400c5020104107250500025104040040718140706001044642c150782d41d511840c601c0182d08680b502c43c801c5460040503915004c05001d01411000300618038061501310100000c141c680d1080701e081c0401e1000040c2e03130318140314041c8200c44032840582d4a280141c150340369550241003040020005584810100d40c41d60090350250005171071810b840ca0001213240d103001048455964080ea0000b03940311295030540c01c00e0840c51080d1428021075852540548050400e0540310b144000244560405581a41c01a07600a070015100103180d12040f40450b0940741d1410b0240d4020711503840060800000b4031880e8010b1a1040b001e42e13540d000a00002d446010500c006040c0e05004008110005070310381c158660410035150b102d0390307513880c01c0090f81c80b5000810f040d44640074000c0000f0320540c5a005101200100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 55203474 1250 55202224 55202233
    0x20f030f030a05060d0812010f05060a020309130e0d021c02010506130903210218040605010f0503040c08030301030c0609140d120e0a080a02090a0c02030304021c0f0b15010c0302 78
    0x14a2602d4008200c000d00301ca601c900a0401c14002c1128540100502040c2240d032031190341c104a407282002e540340d0b100502551040202d40ca00e568044143d8143e01811145080e652071821001c1020f4108a00c84030028060b9840901c00c1503000070340b04158085940c668881210000d405030b00b210000c440300780c0c00400300007680c060b082c03090f84003200940c40303410510366802603011414510720420000300c00466000411a21040041030100003507034048500b03115090030039000030811812600d16105011f0003001040c2004064002075001d442c1302802c40c0d0302ea680d06d007004c8411003d1442a5000304500340c01c0030030704650b226602d030721950020303044030421811179542d16840c0707401030686401c004408940440c1d55a9414600005001c01d2000340f4008055004203d4450310180500e20b146191080030800c0a0700171080d030303611640443d050104030b1080c040425401c00301c030400070045c40d0000c040408004400907001d00400c154604403004406103001940d40c403038560301c0170300075030701 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 55204724 1250 55203474 55203481
    0x70f0f0201020403080307030506011d0a12050a0b0a05060909010b1c1406040c0f05030c0a030204090201050705030a03020d0e0307020d080903030705011a10050f0a08070c02120a03020f030f03 84
    0xa40011240004510005140c00d40c1c83c0c65040c03e5420503600b110010381c99030188071007581d12180501c2148400707009650b00100c42c200180314407800c0c1c451a60208200d0b802c01c01408814802d03000e60a41280c04a226450100c85101c000c1c03008880b454400c010190118856900511031480d41003c05811403c0e40c90070040340c1c005844488004070f030081840880b0401d0070340140038a90080740728044c1010101d040030b10541e061046900440d00030340c0001d400340785c2075903004814001ca0707805a40002c4d2003800b038001203546204114001d003091000003811040598554010301e803061030f8440c00c100440242c00e0054607482980c40203035214042509100204c1e00c418010b00901c80018220b9107800a03958030315003034840b901080200e98408001c040e4140c02c00600e0001c11219500e1704901d00b4008519104050040d60b11900402000c0c000140c0c1c654000c40c20040c01d00d070001d01c101024468000041e548803d80001240140541c916003050380310000140c40e40c150b1710441c1c45042d0340c4c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 55205974 1250 55204724 55204727
    0x4050603060409020d1103010f0b060f2d040305060c03010506070605070e0d0804030606051507080d0f050a05041203020a05070209040c0905070215090a0206160c08010c110f0105070f 80
    0xc1001d01100d40c0079646000348401a03548407a9034958622480d008000754212800b01421258410030005d0180e003414101d049a0fa0303004210b424a20304440a5911240b11080813011043e01c100320406955281d04101146044407010703100f01d81c4507004951403036031204c145a155000a12074190000404d20000002441540100e507020207903140c88101c80d03901000044005101c2c001c107032040d1000003818800d00000d8001c5c040603140541c1c4081400224104651039845484409440075001052454194500d50800c0c1c800d101010010301c02401d16141c101b000f800250303001c495445007080d40c4c1808900a00a03200c41000340e40758241010070031b07002e00080e030314000c0048621030b41801c8041011003a030711400e40920342583c02071800e00e00c030460a410394500508105d4107588203100c00401a80c0d49801c4420320000e8030407035820340c450307403810314014852a00006540d5080c180c05200ea10741c49003214540a0a20049501000d0717014002c03801c8600c00c0d6500c500240d80e0741c80512415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 55207224 1250 55205974 55205977
    0x1704060f081302030601060c0501051b0324190501081605040506250302060106230307050901020a02040c020f0d030506090609131202062e1701060f090207022103040506 74
    0x1401c00181401e100c10250700003805e143d02608480041007818400700c00303014091107113542c411840070500c0c0c22240070303880c105c0e514000100b840d020071600b983e42200040e402121588800340c00b400034020003501504100b00d801080c0103007400900207400140961403903000000d03014401b40c03500703413820b81048140012a0300c10b038400d105d0102900c40c108a1001c4103944410202e00903805031000c0d5040400c000c240105038202900300e005c030f191010042840c00d40440390000080c0c240a0741e2601070b4001030741409800f610182d0312a2421000007000c5801065440c2c4183c440e0341a03810041c0140c1e41542290300c2a035082e500046100009113040c14102807080c0c200c00c001c180810700c15890f40d0313081c800c043c1c510a03050050b04020203008100300d00d00801c9020b06011250494542194981410f10030407a20904e45c01c8200441140c1c0e561b2000c2d840030001e4010495540c03071958480000e40040e6020f22002c1b401040d1a10a03c20f004044a007000101040301c00594503091922042101350f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 55208474 1250 55207224 55207231
    0x170403080f070e1005180a090204050301060803030108060c090406050612010e06060c0c040b011b080c1507020a030f050903120903060105010906081504140403110f0304050d0f050a1406041704060f08 87
    0x6244881034903185951280d00d087d0090242003405079485d802c2c50705040c255112a4808409544188014000c20304080b61f0740d030b4072144a07107040c2c0d01c42c03618100140150500e50300170758002c0030025854110708074850060781070b182007a00c104e00c984c0781ea8081c1b0441c0d104410309803403641c06c0510402a1841c003500203104441051405030b01e00046454811250780c0c0c00ca004841c200800200c000341058280206000840313151500c00d0203260241010303484503c0d4190050400001803544c0e03410b180078806513407010030701030700b2101c043c1b095907903080c02035000350342d041d1003840740714000542c661240e4421003d0341d1165881ca00d1980310348120031500c011450281e9030040d1540c03400c006410302c0407407080c480d07030003a9100405000c0b20318042381072001110b400002600b04010a010a49456150503070465110b01c41d01c2524210713081c10303403c1900000f00100300f03400305000e6540344440010014000e602401001444038599041d01900b80709502c640000b0031500d8001d403070194051400c1907803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 55209724 1250 55208474 55208497
    0x14070207120c171b0607020603010302040c0c06020a03020a020c03120f0d0b06190f0801030209192703090906060806060d0207021201240807030b0403170403080f070e1005 75
    0x3041d2140d1201e500c0186000d41d25900b64440c890044d0842c1c10360002c001c02d404107550241c0b6201464011a0326803005003c0030740540c0d2540001c03001e4610840c1c08132a4190000811034403100d000d407009010354024142480103120b0b654450009103004250a01c900c4402d00a079460582124400809a0000603285003526078400c5420b8058541e1b1000344081d1f2008086c45180d00e07130100b4054034001c61100300004000707481005000503160020843d405c0004460101354545001d00c844000c1c0c10710391444108210610920790b800c0034410150052644203440e54049141c6800d2000115406d51140c0c800240e00c3c0008035005040c40b0009150740b550621000d0300c3d0105540224110f000021120101a0754070088054148040000c5056661844401040d11864801078039621629400041c02000c3c8981c04101054011040d6030f40c0b24403200b04101c1c8500e441d080c040c101d814104c030200e14540d08000090a043c5c410680440d0440d0020201160b200420b00201c0305030700b2036461084c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 55210974 1250 55209724 55209743
    0xb0a14010c0311030a020610080610050103150f0308030609090f0601090513060c020d02010c020a03051e12090c0907030c0206041b08100207020414100e100b030f0a1407020712 77
    0x1030f00810501c018124821141c00414540c2020021048000d58075031084000e500b082003441b100f0011420820200d54092801242c40707410780f09042500c10031940460025400950000104003860000d144a1003086510041c5a525929015155149a065910a0303005200184014845a0f10075504100000200b035004045991001c044405600c1504056444501c2c500c4005609000f00d983e04503031031014002c14bc807507503005007081c0920f078189240b82c4980c66502c0300d4094034800b40c8100b8600c101009140d4280042e1080d180d00310181d2480c00340c0c42181c00149918024001c01d9010880ac0e40201310340d946e10b4548070100355412721040c1c50b40b103442c40c002402c075804104410000c90310380d00060750340403640304100864002d00c01700d43c2600704480070425a0003625007244112424441030114030781e612441000c0e4000982c000300512000031007485841082680c0d118800c44030078404105500700b42d810b0741d442207400c51710607006a110f078205102a200c120b00788160703148070302c1108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 55212224 1250 55210974 55210997
    0x1202070b07060207171603031e02040605120a06120303020304060902270112120804050304030510020a08060904081602060c0f160e090703030518030a150b0a14010c03 73
    0x40003268403940703040e1005600490403009010b401118010b01c076101100fa80d02d0b28021208015440c852150003805143c0e80b024109900703200c2c10795907101041d035120308541d103c0d1180405403081d000070140c044281080000036441041501c40c0c103066400600801d0302e42481598128040d60000700304444041d100c070342c80740058a40401d081a80303400014410ba1094100c1c2c000b0000140c1603000800081c2e51505250119011030014240302d20145003009095540313082c994554425540010b20620855094416041055001d800c0b198019507403c0c0d019118041000450603043d1070180c01d9400c20000c4440c454000000b485101e032018107040d003031a03014904d4904041d2a4000b410141d0044192810720031000740707503240079011035001000282054000d2503074400035400000c041c40800207400c3d4041d600000206a560b000508907281913070705142052400b200c130001c8040300f90078132125485a103417812500d03080c0c079030103c000c003803100c0014011038a0894202c0140c00740700450245 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 55213474 1250 55212224 55212239
    0x50909060112050414010c02060f060d1703090105060103060510080f0703140108030a170106091a1b0706091202010c021905090112020901060305091c02120d09050708061003120207 79
    0xc05110701e0240c0d205d80034407100c1c00c0e0140d00352410b120340e60307085401107000c12040c5420f202a2130740066081d110074503800941c3c580341140315100c41200810315404020001b508105422440c8542c0d03013070b6014040180d5031000d000c0c8003110b2400d4076000c242410009018098589001580416145400b00b14240402c1032511464020f81041001c0c0d0030000d510080319802844200d002080c225110405600d80316004201032901c2c003070b210b804480709411035803c809040c00d8444a4485565446074980c089582d6680c0b10f16a21410011841d100000240110100e4285042e9501a1150848081281d00b000034200501600030040203a40c0d402243c2600c0300c114036400303007440d0000186107910301d004015032280e05901220406003000104840d035030001c00c014582c070030000c10116500d20807110a80c10b005140401a25540002c1020130313422266800c040344c140d010304144c54444e40c0354580540c0341c000440f0085c0d80d45400c003108000046c60700201c08a88803051050b202100c0e2500c40f03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 55214724 1250 55213474 55213481
    0x31c0201181401060f0e01060c060209040218030705011409010305190603031205060307030c03030c06060302040e0a0606171c020a06021605060f071407030c02030706170106050a050909060112 84
    0x1026210701030624240020042c091242c400506104629245c09500e0243d03c000103c03814010242046480c051880800540750103031160104c00800954035104185034041012000d08100e502c01e02c50300310006007a50140440c400303101e810b00300e0545460170040040d00a0725000c2d12680d440c0601c420f0030b4403050464403c0c900030318405d9803a04007103299007203100217481d40078050500c04d400c0300390100005100b003d40102103d0749400c003058003402c00d050240040055a00c069042810300c0e1001c0e030000c03000b0030381d19090f41c070401c1d00f04125619044a0507000085910382039041d48a6440540b00b05c000d050040e01c146640c3c4102d07503000c0820b0ba1110300303a0b081907507620103c041b0401c600d410083c041c040319920462000e140e030304605d00b0940013406119402c00081092500089040501d4031690f1505421500581200c25071a507801c0000c021b0240080d060403030401c0c5000101e15031788150704071240b1458540e600c0e170820464200300624614090004c034103209200600c1c6000c03107803500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 55215830 1106 55214724 55214771
    0x80a210614040b061210090e01090c05060309030418090c06030c080c0310030209090604020a120c1e09150f08010c050d1a0607060605010914031c0201 66
    0x404130b01544600020050070003190002c01080b542c00c0c0c4020360498900c050b0030000242c46001d558201d840e88603009085082c001e0003000706280850246030000352035000d813407500356561003c81c41c070044107059000710741d19082d034002488010302c07051000302114141400031152100340142180d10041181c04030720004400300c1d110982c0300078048061503001d404007805007040c02500c5e03a034060482e001c80c400c195245010035015207040003020080c1d403101e252140c450904c690454050b9421102072600d00d9034920000320a14207009201289160705441400c00e0b00341712902e42e401d205908200ca481e810003441c800001d6008048440d40003060380002220000c81030070508031640d00c095141e100c800464550180b1403035a2020040720404d80351769040d640d590310000b0707450742078016140d811380050000201c1d96840c660300402d0300c81c40303200000303509c840c04c00701c10b0300501c005 = true := by decide +kernel

theorem cover : BRFrame.Cov 55035974 55215830 := by
  have h0 := BRFrame.cov_init 55035974
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55035974 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 55035974 ≤ n) (h2 : n < 55215830) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
