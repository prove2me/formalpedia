-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1493
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:14:40.538925+00:00
-- url     : https://prove2.me/submissions/bf4e77f7-1180-4843-ab30-9d66322a9f72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 268345323 ≤ n < 268525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 268346573 1250 268345323 268345339
    0xc010b010212130501080a230405070806010608161809140f040209160306050301050703020a08150312090112090303051e1e07030207060e070f0506040e070f1b03050a0e 74
    0x350300f0b00c0310326080c140c0d0000c0c6841e40c1c55035641d848031400703041c400301c00760106010906502114600000c81c0ca01c41c0780140100c444d034680e02d050345559541c3c02d104180c000303410840810b158946940e1001c884048503d0300c40b039088020112070318454500e51003120199621055552440c48004600b5848816202d800381c040c80c240e0045000100001c200124038600300c510b40080e0760007076100340e01030a805002044140f8101e0400b6000f9800750030304401041d1281e0006080480b40424011041805005402039501d0032150700300320b0b003004079a503043c02207000d50014002068402c05481c54042e41d0041254201072240036030031801a01454a12a1800e04102030700c03c0325151300609005940c0c801d0b01c15035516404400038040d055000308480c0c02c2000b41d1000401c0000c44000b03450040300c0c2000c09964800802250384502c1c4180056080b110340003035421402400c81201c1c03242141001000c3e40c45022580c2500d010354803044020070340209203500d80a42c031820305026442e080d03407030381c2d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 268347823 1250 268346573 268346587
    0x807050a0e130206160b040f02090a0b0f0105210f040c081b0f0d08120601030f27140d030f0605040e0606040504080d060308091c0209040f08040b0c010b010212 70
    0x4002d5004206019024510002e903004140e181500c01c0d48001e40c00c4080412182410325000030030004504080e485000d100011035075020030751083c001500c50040c051220000d6850065505030001041d100d180120f00e5000c00582c940c490245200f02c1e40495600c400c0d190038a4107103442203154105064a82c000e004445410f004a071900c00c225604481c180994103003407002691035451030034010403c00300400d01d15803504001111f24014602601c1c10302200200300119000c44000c0802c00030004219040300414001896500d40010f02a480c402d40341c08044920510b0440602824400a5501c444a1020403594030528000c1d04044030244829031220100da1350305d640240c0803038407807591140032908000207d012550742152010080c02116500e082c170342c116030442040607029032030200700d070000d046517003142c5082e081e0700625108803038407291108659481403180454980754100004200c0d00c1c41c84018115550180e000454a11301c08000203050100c100091b14a0700e805000d84 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 268349073 1250 268347823 268347841
    0xf1b03060c07110a0602030d0b01020c06090d1e0c091a010c030f090f0f030b060a080303040b13060f091103010603080307050d0b040203010303020a02011e020715020a0203070807050a0e 81
    0x2070340004400c81a1a114078160a12480384a0300d0201c3c168002050900007070205d0300800034141e0441d40c81d42c05c0202200410059850320080584282c0c0903800b00001e2034540f5200c925069400d000d81c5020005c1040562503d16400e50000180ca100071819410400105240140c03a1100e04501c81440c81008807030001e001c49418450007400d0000a0000d107030b00038800d50b02c000080000e1034000078580d91380c00300140784986074003081d1503c4000200045a500341a00e08108552b80c0c1401180b40d50340707540302c6103144c2501a00040307031003440f80141404200280504100076411764000501c640e01850070704c400031903c16006001ea41403140130008940780f101904d13402405400c1c0700303a070f035000e01401000030f1000040c840c0c0d0041c030120010091660005081144900c02e0325113140118100070003d818005406200b00168015001486111b02c41c80c454800401c1c81d00407a1585420360340000e04000302604842142c0c1e0050408014500d0859002c9004000f14052a0544c0c240a03501c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 268350323 1250 268349073 268349083
    0x120906080f04051c030c03060b0c030f1e0408030405120a02010206010302010e121509060705070c05040911030f0f010f06050a0b0c151306110a081308040909050f1b03 73
    0x840d100c1c00510303400003014000148140b804c000c02c000105030036681880005801030200440324000680303004404100c5010100494015403410001581840e00c0007581a2080d889900d40e00030f003400300700c3e5074001d01c05c10001400203420204003035a1143d00f420300f030102c1300004109440c003036482445640c0140c2d8010a40c1d41c103503031302840c01d084020114400310b00647c0d580d90321300000388100041c0c4000c42520200702c3c2c0c050b440040544100e52181d41c804c0740c0600609801406031110100204400c1ca49030b03100e8160075210b410b6010b12542d1a20000e802c2507038010442405401c1118918400807003071044004c1d50300f250b0000c0001d60b040401245404d42240180010340c1c400080300056032804210278050045e10440e541050324000708503c0e224020507804644050406818140f0740c6003030001d6403006410703980c414560365546140002c40c2043d4a400307607680c84042102081500c0e43d0f000310a100c600403001404c0b086503c5000e24901a24081c09641202000390141400c3d900815 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 268351573 1250 268350323 268350331
    0x5150c07060e2d0106060c051002090d0c0902090f01050c030403110f030f0a05070e222f121b060310050409030816030e10020703020c04061212090608 66
    0x4001800710850070480b89042c10702900f45200c010540044074001c10361003020f01645420390001d2115907600c0400351403a210510000b001c0380c0202d8803203c0920a240e015003a020001030160840340c00b203803600d0341d2080c616005009001c0c0c000902092a0a02c500b00842882d03080ca80503141031158458592240258000100182d4191009141a94030307810038228541d80101981c3c08204814002d0743d441111450403500d50142c9903000aa0f011440c0d02903204000000c40e0b6900425516039041c87c00c1041e80b022108004084421030503000b450b00790880307020a408001d88910f94007810040001500d4080d14180d0740000c18122a03049800301e02c041142d01030314019242d03101c80d94508a051441d40006411901e4000c2003018035134400d01c218011411040380d000b03a010000c00440c191001040c0002465102c41c0701c02d110300307030542d005040c118003078815106071150200010382960b46a070f1191604c4110482c20030240100f42d0b180b0f042032a40e50a101e50024a400c0780030f00540741c010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 268352823 1250 268351573 268351583
    0x110703150c0813030921020603010b0a1209120f0203130e0a2007030c080f0f0a1106040b06120109080c010203011511150402060702040203182107060f02040509010602070305150c07 79
    0x400c1d00006c0034104a00c03449190b40c002d0100380c5035a1246006221074011108240005d0f2444040d16032080551140b403d56030341101480780d004101190a5401d10040746408045120400c02c51070306400e12280c14014003110412100c10707051510b01d45d41510300c80d4154a060070080c4004c000c1d0001014200e40307409505040c41c0310020003c1c1172180c00b50080700740300da0301d0050010700e813410000000000c0015005588400c184901c041140a80c0c40401311002840d000441000c00c480f490b00058030f4856103d0340d0300100b20304000381e0764800c40d0b80010800080b142c1d004001800018a030f003000c03122034040c51400381c0c1e02001c110300c0c0c655907444695032400c4070032046000c00c043d0340700c0300c0c01c42d52500e8020b0025540c07420302c040c030701c2000340a52996424078000c0d5140d220080d9503403020400001c00d0480c0807810b15002e91950300c0240300a05034805c007560f003040f0000d202d07194a01c16500900058020300f41c81803441c18402d05003d4031001012840c110702040086901d00d01c1c06541032543c201d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 268354073 1250 268352823 268352849
    0xf0a020a03020c061c0b0a21060f02071a04060b120606100f050d150b120f060406080706030e01020d06030f052e020a0e31020702030d110703150c08130309 68
    0x1001150b081c000b00c0e0400300540700e46231034175035124007424008c4000f244a10020066079007010103400803405032400042416000c941c035a1350420740c00030000e401600841002400e10400000a1540b941420440031550401001c003c40c918262b081d1050450150820b880d814140103030048c401e02c507131000aa07020743ea0b02040003002e607040c0707481e00203070000c0403103199a0b5259039551000d4040880b84542c010b0841c400151503800c181c0a24411911044024411a030801406901038403005002c94081e40d030903c04002001c4040c00b603100254080d014000010702c99090150408600c0d440d030001d0302c5489041e041d19813200040e9500c10500003900161101041d190480700c98114143d000e510100340c0c50b403100b0504402c90a1401d00f1007541c0300e052001d002c4910441680144103010350702d600f2928403c02120b0041075020502d40c0403070700361007100d9141c0c1d5640502800d10300310446110754440b542d010064000b0343c012740100301180891201c44143da0300410016040c020300700d182c118 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 268355323 1250 268354073 268354091
    0xf0f0903040f060509040f150b070f08070c08060a020a090b0a030f06170f06060307050d14030a0f1d0306240a090b03061b0409020f0f0a020a03020c061c 67
    0x18000c0e034019010308112140745542c3d511009226820492072144600d10341802844080d820341f055050a0192241c10820f071031134480494001d401243c410364a040d84030000d10002070010000303110f0b030b520540340c04018904040c0c004e89821402000356103100c0c03040001584150300054000c00304e581e080c0f85236a544a00c038101310080e00324030301c6180c44c09050010204540d001c0d40b10b200380300e40159046a50507032801c44a40c2d40d420064818030780580011506100c1030810941c1400620b00410319050b07200f180740c10702861a0302402c000c000240034040c2c440d819582c4180703440304001d079107003486003601c80c0303240000d0710781d44040c01c00b008000c5c280305a52910042d04040c072102850041140071032580e11114403019000c18040c2c0c921034000c032000582001c10840b810030003c00c40990040c10a420f015186000354018035400f100d0503403c0c04030343e040709e100704000d0014010b980e014140f1301d200c2d464081c3c980044040700c14800d910500c4030f861400c46d0706007001c1d01c19074502d0001c289554 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 268356573 1250 268355323 268355341
    0x3130f080c060a1b030c0506060102120909070e0a090b010306051e100306050d0c0306050708160507020a0f0b07021201021c020904060b1207140301030305040e0910050a0e01050105090f0f 82
    0x40d1011a1310030908200c81458245608030080007252402a000d40d103550f0340710001261a821001103890420b203003800000d003103041c000501548090700c2e0418014605501c030000c2e4159419510401e0300c01e49034103070103840b540c3c1401400000c003c20b807450410000080c011040345240320100034000c0c0503902d1a081140e10941020b0010040a0060045203080f41060501c00c030050200b40e540314140804a40c00c02d02c00c0181c2d074850f625004011510603110389041703c1c25800880241d80c801ca4000012814004e4031031054010503020b5222076465106205001e00a40d100e82e40c401e46034410312001400d40300c124406e07650122340000050340c0d1001040020020441a00407030405280850f10b04c9810300c0048a15020b05c280d40c480c0c40002c100380b0658001071200f4040200014800e000c10010346051650864020181c1415a8130b4041c000705103d044400444a0005070764441200c0c14022a080c4642e40c050f160a0f03400c3d00c1c02d45428544c0c03640545014240b0310031001c0309800213035800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 268357823 1250 268356573 268356587
    0x60506070c050603040c1e0305060c070302060106050a170c0d0e010606080105010507390f0b0702040c03020c060403050405130b061803030d09060f0b060a0f0e0103090f0503130f080c060a 82
    0x20340134000c2c00440940e100400441f20241c041113416104100110360500d95a0307003644c0c0e1350f030b0740f60380200202d038281903048800341c01c0705040340280010388650510340715021600d1403207850162600c944a441c40e51603842521802905c006c01649061410b01006034400307212410345000b0b0806507900c1d1210b280070049443c0c07a90705900c120200c08a040c1c01c0603403042202d01d642151641304606030341c641c9000441780c01144911307a40d40e07001300300050040c207042c0c000003111001410300600b04a44c0c10300030303418080d0850b02200002e100003024003140c42c062070010a0301d504c2d04070401c4003180c0c08020402605c04c00c2a9200848490030403401aa40d08008643c90749821520510030040e442c94100064000080311140807820012070f200a0b003000c01c260352148082d0307660f000050010007410f0310500d1006100504043c1c4820828001c0ba4000c08100c555a21644c011a910900050103030305c0d40c0016040340d403c80714065820401e040c400900c509141404a4000b695400402c0081ea842 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 268359073 1250 268357823 268357829
    0x3150e102304050f011a1603030504030512040c050102010507021216020f061209010c0e030a0f06111204060605030606030703060209011205010b09010e120d03091a1801060506070c050603040c 84
    0x300e4180420050b0701c03c14a0101e6040301d416145001d0b00500d80100c014540c05051f0095031382e170030200b80f00008070f4801c0c0c02c50b94000c1d000e800c20501d044004004200c500004480c00c0ea0100b03296501002039590920406c0e600c0407440c070207020241038100100410344a070a00520124400881e25420743d5030784c985001484400501a17544c0d200600c2030980c0c43c0d8000c4915600d40c0d4a4881d0403000d66000350601c81d14003400038044c082c1c544042c0c1c0c600000700c0890900703559180c1d5402583d54016540002060000400c0303900c440700d40703030a141c000165007064008074041d4215000340906510001074203030683c4d520078009602c51514100482d9595502134980114a0900000185101d108401007007112001ea950b01081e40b03510092008590034000b103600c09030710a08080c150b052080d80301c00061441560341215010719441c00944d810340641d01550401811a12400a04405d201d02401841d040e91802d0802d1400c1d19210141c884600c90a0701031040080001c080001c006000c6000e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 268360323 1250 268359073 268359079
    0x1e040602131512050622110313150603110603191a040f0603020f060c010b0301090524040302030304080307020f01060b0a090b0405030303040201030b060c0d03150e1023 74
    0x2580c1e10341410070350502c10400600891980c18049854032864058603100c1c1c1400303480240340103007104c003098110710704040d02c002030365a0321070120600711300d440250302401101d002100002c20b88d041c0085c0c80680c60700301c0e011980c0303820010400103d2034030304554101c41c1103450607220703a9014a003182c005c0e001c00c00710070110303d000240b0744c02c001c800c16038183c1b64200380e400708100f21443c00507400719001800f020f0344c458000e40d5220000c0ca07002c1700030301e80001150f0006c030340181c03d580440c1c01d480400008441503001500d182c40980c40c62000c1e01c40414514001401c81d003010b450180d101d01c40584040e00700c1d90000000b030007441c005c000c1035007400080700080011541c0d800000d1415084a0030f4500003d4652000060340340d46c60050764160303200107000d545940c503503a005500a00d4080742d0aa0401d40501002c82c413240309000c0410a00c50907200442e40403400080491022081e800555191681c0000d004002603900f103050161400c8224440054046ca1028624404800c00481e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 268361573 1250 268360323 268360357
    0x903120c0f0a0b0a0509010b0a15030f0f0209040506031b0415050d0b011410020304170114100312030c1d01140f0909011202010203070b1e0406050415051e040602 71
    0x10403c9011142d90348a880101030420103500c600468a00741c42c03070822000d60141c280b00c814040001000c12521490201c0e0900040307001d01350705440161001c0c03803412402c0310b5010880c8009400d15024050307101d2400c5014010840d1000c58846244040c0030300180117035036681d14548601640405070b4054480100079450548030bc0c07400c014151403d000380780c040141d10032100d5031408d103030355a00d041d40c8141e005582070074140001041d4910101d03905210325900c1d108110a100c02c0b40d0b0b4110700a100c100064446a821410000c81c400b40310f8410304105403410603910801a400010007140240d100c02c0b0303c3e14519250300485903001101d0301d4a4200d80000380c4106106075803001030001c07120640740014560b036100501b11844040200181c05a0003c1242d80002155039180c19030240110307070342042188006c51800c800b400c080f1012a8401d540b00c052109001446440743d2003020520001e100c60700d403060b8403602c902c025208110005207900082810845180c06480c0e4418062070350321 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 268362823 1250 268361573 268361593
    0x9060403260f0c151005220207140601120218070e1c0204060b03010e040318080307060506030c090402100c110d060b01320d0e01150504060b0903120c0f 67
    0x110381d548010f1044125120f141802905450035640c000d1007010400010404a850035040c1705610410880d069a0700229006244003155107101900206005d45044001d8800201d2403525048040e00052001e042d51101040180d603041c025581c0d940c88821005220345401005a90301b00c000707580258007010464246191680c00c650301c1d0300c01c0d40200c506204043e078680e5071411310710082c0200c1c2c4188440d0703800100070a0081c0f2504911001c15070540d078009907296005800c0d80c0020303004640703c94981c0140308482c58200480800540c048400d41801d08041d40062080e070300f400304007024000901200414000d02c0c00c40348400e00c002405400c0c03405c00901d0306800412000c40801e01003850107030504461000500714810b4885007056204050f00015200a84c9802221500c1c0807151984d0740c115482e1000e0207103c1030440303680480690142000d0420099410329040141c12107424054415903580014410314940c80b1041c0a07541c80700401d542d81c0c14401030b103142e4809445070110503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 268364073 1250 268362823 268362847
    0x2090907120b041b08090a0b0f0f01150c030f020a0204022a0d1205060604030609150b030d090e0c040305030a02060118050f070e012003040f06050906040326 69
    0xc540d603010516040100701d0300b0208100443c1d404002c0181e000720300d81c54001c11280030340100d43e04552418121584998160746140b40b00034100c0c0d44c00071041a40080c012031000d020300d120301400c491039040016400701e1074002c0500041d448040c041080010a0000081c0240891014950003a00030740d0344070350030007402550480800c4990340004103004000300400c404507803000c628072940e4070f40004800001000020301f00260150350b00860800002000070950322802c112a4401d40ea40740c446513058007103a080b02c4034440100d000750030a03c5003001c101c1c1d000341c0400913150700c8115905581ca842d46011394074091900000e02c503200001e4801c0e42e064000446a04941c400c1404000e54181613242e001070792000c5d15001c01c125000000300768054010462000e003800107250080c0007903045640c24040004019000c990b0342c200040502494542c050010050800d908105143c405000e010034841e1040e0301c0060036074540603034025007090b400f9200d00c150f01070000aa54a814240c801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 268365323 1250 268364073 268364087
    0x60b070c06020a0c0e060103140f0906010e0c0d020309030403060216171831270803010e0406060f0311121605130e1e060106020f0303040f0602090907 66
    0x20a4500038801803001071124800200f9500c102d60011058900910306050f14a070480301800180c103050321b0312a007072240c54028100c180b00b0342c100c0208803818100020f42900f048010703040014840a040d0030331207004181401c4074072b05a606900140d881e603e1451241c10350041d5000145954000590b413001c1314000542280924051800d000aa41c0800c0e20040648501c507154002082c1d8400850801d1900c45040d070301020f001c071003c104407801c240300b0344800f10540000c01042c0c0d0ba2804503441440060340300c48483c190388031145180c42e0300358850b0103860005100c1c101a400507000010208800c80e00103c0c010310140e480b104200340ca034a170140400210300320541c01001c800f0355014101c90001091840c5600d5000316118086c200780030311020303d40c000e230b90300031040d142c0c510030780482410044a11654118844007a84980c00107041c1c0c10714806134441c20855104510903a8140c1000c0201c0b1f400580c4a48200308490840c0b030494080d0090502c1ca540c0000381d10100b0084035000b0301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 268366573 1250 268365323 268365337
    0x13020a03080d050f0f0103020112020705031c0e0d0804050a060b06040e090606120a12050a090b03190506061912090506090105010f060201020c060c13210b07030603030f0f090801060b 80
    0x10309400c503585113041d40c417006009103c080d000851070091a00d003d40c6580c014206203001e502620310744414080c05480c2002e010110564095840b0200da103213081c1481070311042c0a078ad243c10055030909072a40c0d40c1d1221114405800e81c0c1d51400074442c82c1c1d44030800c071070080019a44405d00d40c03410090a60311035604031441402114405483e42c4951804102c0d8039500fa031262496032150f10041e0308661540102d4482c0d002d00070480300210f003500046000e180700e14240c0040000140b07210701e000090700c3c00030380302c5405441d0902480e8400a6041c0803c1c51007032039483c2c845118025548003070040c00300d024000d8418015603007400030180d01900800d040c0e44080b40d425100640d9114124200c0c890681031380340e190080c002050260307410100425080c0390081401003d680c969914098080d145032205485100c2c0007400c0081200f450b1085602c05040d04041047ca032445d140030740842c608100b610100000401d03940101d500030840307203001d01092002000580d481d06000c01060340406 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 268367823 1250 268366573 268366591
    0xf03030905210a0315080312011a1204060c140d050702070f0605040e090a0605090d11030a0c02130f0c092303030912030c0d0c060e0c01050313020a03080d05 69
    0x11060728418a0b80c000a0507040c010311038949030404150040f0001c00d14100f0107505a041c00720b0000c3c0841c0c0030800b4000a20070301502d019554580b18044800d07a201810400c0c0c01d00b028412101c461050b000b0841c0e100d40c200101080300801100222414251122000c044507400b0881c2440c5010543c0403510031926502107132821919403c4175060b101480c4100070015100300002e21542c244501010740000e0040202c40d2024081c0d90303100b05481084038844010f610038105d80c103130a41d03c031146180f90280c15020b9490041320383c800074001600410040e020722510000c4404010700341e413020182d41800e210402c081007100d14001c2ca0b15030740384a000e0103001d0920b0060031400782c0141c5a440341800030021464114080280451030051040c0395003580428406502960002e00c95aa590085035a821001c0070030b515004040381c3c070303035540700b101c0b80e0040c01d1100c444e98101080b242c11038819800e003c074907030380751000070092010741c0c1008068640c0460300d030202014903002103009076541 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 268369073 1250 268367823 268367833
    0x6070c081009050d1110020c010c0f050c070509041a0f01050f04060e01150903080409050103032705090c07050f03090108061203120a0b041805071e0506160f03030905 73
    0xc840c0c0c050645507207407000740940c4c00280b6066402c0b80034480020540240c80b043e580c03040c80031150401242c0040d54844c000765101d50601c5501580020404903c045c01e003481403c0200039a40e2598070038250041034051102c80340410240284004500408841b00d0035002141c40c0807511154991000c2c0b241a0003102c110102400034680340c0502c400755000c071780ca142e800ea0b203006d00500341403002c00820002d1101c480008004540c141c0c1c0244040d0103c044040b5455255150050180c1c14200c3c00800302c210a0003882441d45d00d00e200c0740300321101101d021907242c842055030f443d14420440300601d0352003502c0480a089102002074001940c098a810085546050500945240011000d2280e800402080780e00e040180c105607084200024002041021140817400b03c80e03c0504000c004c15103401d55004210040252070098007540528007403149034601845407410590265520444000c04c1196a810882c0c41c1420300c0382c1c202e1458101a001c81c00e0107001460080320a0707405000f1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 268370323 1250 268369073 268369093
    0x30c0201081e0a02030408160b010302180c03060112110c070e0901020a1b1a0702030d061a04090e030d15081b06030f0a060f0617010e042103060506070c08 68
    0x140301c000b018403021081d4007850f0f844a0407200250f00003001141c075010240811420801c20300481c2280e01c3c070480d6182c070b4030f50650040041c1a0040e2000110f092100c07401c005034080c280050701e4120100b0300b401c031052418030082002408040c080601300000124404000801c0000c4080841d402902220120380740c0c0880e59080c3d01c904501c10000c075000c46d5801000d81811000290750300d005100400300c14200740c000b500d05c060f05460450042c3e20110b0800314801192003150014450300d403183d10703800000e616043c0280150b00c12900d109540b880e40440d048424400c41c0c00c180c1c40103070700300010000f00300410303424a035a020380c0c0700b24440c2180d4102d10001c120112207005000501d000e040d80e03181350b00ca54903003c00410a020031611242d000402c541c0b020401c030050882c586400200114110103e501c41d80c05910041180402d0303000d00c0003123624840203183c40281203085000e001a01c490950103801d0b103601080d0001e07000078000090004010030041528007440a4404c440740f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 268371573 1250 268370323 268370341
    0x20402033102030c090a090606121407080712020d05010606030203010f06050301140607020f031002033301051b1b0909010209090a021602061c15150f1b030c020108 72
    0x88000e400d0350113015400329a01e803015a81c0e50255680902084100c460765981c010381d1116400046805030040d030340c00801c9414410310408003000307002044954600801c041e82d40c001c80c420706001e2401c91581c1419910f4840004004a40040c002d010700c6030789106c02402540b09115103825103802c004007198291180c41102d040300c0309500c012030325400940c104a00c3c0c2c0d110b2034049a020703812200781129601c00703016086406101080c0146c903460000d41041210b00c54001d05103111141804205040081180c1c000b00d604c020310f406134840b0381e1520400700c84858000051054130135284100c0000b814501c803154024000e071002d810b1500d8440443d400d034000c43c10102d501110b8100001c00d54991076018002c42a1000104120304100b41c010032030b00c1d88503421101c40d05030030300405881c3d1012070207251004060b01c07200c04565860005c1c0c0a510300e111000400030881600050b0720f086100f50700300d280d10f162860340c0c0c0090340ca0500d0003502c40003d1601c100c1c042200a030004013a96 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 268372823 1250 268371573 268371661
    0x1305150618121b091e15190503030d05090331060815040e031306031a090403120c0e060412030e01140a1b060603051e061006030e0a02040203 62
    0x14407541e0100d42c40740040041c02c81000f80b40014800e50000c02c10485c2c00d19412950044900030f403800300d806040814884543c3c2c280350ba0001414551404000c5614000116103504c28203180001d401c0c0c95280340707075007140308900e038101e0001013441070100000080003000f81190b843e00e43e80c601c129642c8000340c921060460344441d0502200d07006072a181803e8209601003005035040d60301d083c948150001d0780c0b0400da080200065520b680704070021448040700b40e1408011074a507042480e03d994020021001048000d840700d450700301407400d030340c011044034446010003404603807140c0d00c450a0004800aa04c03003680040d11500c4c540026501030803124841d86000d40d1024a0000402000d03141c54441c1482d00c0000070b4450003640100c1c901c0d104e818041c5201e503000d0004070f040100c41941c080001c545404050f000282070144500703003100004200da4480c100440d50b00c4824900908102941d04040d4200e8000010009400f1020030014000218581044000580203107041010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 268374073 1250 268372823 268372843
    0x10606050d0e010c090611011b0c0203010b04020309030a1409030303040f03180b1b0f03032701110417190302030912061003060b0a03150c0801090506130515061812 72
    0x10861880046c401d041c0b245203039540921444c070001c91448240740b0603001c40b1820103481e00014103810074202c110701e400e0241581d070101c01c440035819401c100030002e842c0e2103480d900314244010034200d102210181c4007030710001c08004050f69140d248c54282807145010301642100020f10380303d42c40c2407034003445051006541c80c607404c00b805c14141c0c2500c44e88400ea40850104184100d001e900251241000210b101d8002101c094002d404984040044542044011041c41c1d04000100c1a2640180c0c1030b11300f07d404146152038080341100e0030f2800d02e480340103c0d004076070f01908040207054000004240741c14080d101a1007004840c502151944001e840c2180040b0340b5110400c0403520300d801220103040d0042c40e050301c40355a9030700d07081660f80c10249981b0340340e12002100300c5181c221543c03600501040d0b6042c00340c0d203003401c001900d1415002039002e41303580d2a40803c801d542d030380b00e80200e80000a00815620f424251880195070b9580d250039108103080103402d140f48001040d400342d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 268375323 1250 268374073 268374077
    0x61a030307050604060b0d02040e03093c121504150b0303030f0703140403110105070c03020c10091703040801050903070515040312090b06030d0203090a0b1b010606050d0e010c 77
    0x1884c0c9840d6a510041d00f074030134405502131114103815016036614800c100081e40e00034001c65540f0034080074000039400c03c4000380b047d0200c0c05003040600d00300410400b140010340401910703c1440400040c2414000a15018244102035400002500700d10707070540181e000d41c15001040616115540c1070700c408103e2142c06820510216150b0851194195081500c605000c240c0ca2070060724041d040340c0c11070f0154005903130324052071003260b000c0c07090710382001d240d1400302081d006031744004e90b480c4e641c048514000e07034440070b08100240c4200c004070040c003608401056843d9003402c000340d41e9002802942d103e94640008205603100000c02c494081d030f404009407841444003041c10500d101700520607000c0c8804001c841181c00f101d40b1914050a2140c4604580c604240c0c06040c98850395500c03140955000304420291641ca004140f400c880c0c512aa40b60b03128040155006003212200c8401c1c015800e000011031100d400c130028105120f54850200024032281c0303401801c1e01c040528100c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 268376573 1250 268375323 268375333
    0x2090f04020f0a050d0603081c0b01020c0f060304030e03070906050a051017070203041e03110102060405060c090d020604030606030b0c190f021c0201050105011b050303160908060103061a03030705 86
    0x10060050f001707444402e25036200004c1083c0d481e00c03202e02640c010401c80401402c05c0013900b244620510513644500000c0c8018400d2924201c0820180607440c0302083c844c40012001404042c07040d01041184440907007510043c035902c580703180c05040107000f202c2c807030546d0042c003060034241510b403d0f440030302d9075031025540c011019803119400c0c0054812021400104400305036844c0c2001c01d4a030b0504416210610145907050809030988e082d140707541190030140c240408038000240d90394001c000ca100d480d9540b45070400140040c003402c54002d4015601180000500c07010354003100850b0b008450303100701a52204a50205d912981d039011009424014640300307524030600381d00a445000d401200d903920702c429a050030880e078051240c0c005030344400043c0a11f590040f08400f82c0035014500007580c1d8050b03a2004e44a010060002d078a0a500a140070714191082c2d030858011b00700364098030700c01d50712410f0910141402035085001c0d04901e17940c0340594100001140e40aa8000d40540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 268377823 1250 268376573 268376587
    0x708030c03040527070e0a1202030c010f020c031c02060105010f02030a0f120509011a0f01050712051201150216120b180f030d0e06040209040308060102030d02040902090f04020f 78
    0x200c004070a003105030000e01c01c0d1070400d00e03080c01c1103400a070050f00ba540351040c1800249042081147c3e80703400051044481102d0200143c400281112115000742460861760400310310881c640725010302901e90500c2020a18030288940d01c40400c003194040d0709940043e030700e800040d0340c2d60040311103200c01a8020040c10203614411508059252514034000b142e440404428006540003510b808401c0e940d038551001a6554074251017482800a803166103040104c4070002e801402100000381143c10b81410140d8201e100d0740441d609282a801c00c550b6a503140c81a8250003012051100007510904002812a17442101200d0803281c034240c003e80e02c0486a0348403c40c201c0050407259030b010aa009180741101f040c400109400f40b428025a101e4480303420313400036035549581c41441900b002080c4005138490060301c561043d05400c0c80041615800c5c0100c0c594425042c44030043c9101183c0803424a0302c5170020121540e08481200c4001202e40c1000124425442810343d40e113401c00c441 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 268379073 1250 268377823 268377829
    0x9030f0f0303181905010c080a060b121b030c031b12010b0901030e0f01020903100b090403050f09030102030a14060103062301020703050303070503240307030206071509080a020708030c030405 84
    0x3010540c012541614600c00400900c0d203072036405040105c0d101e0351102d44c41d0250036804000541c2c00034030658103111080c98010382c000f152007803402e851001500900020700d802e841c8412206d14070a84c8104030380d2858032501d0740d589034100303403603412408540351310551002401400380d030b03a00040020080d85d02d901c1c2c9008084c0350350020000c6410304d0f845030111181d0348000d002c4994401d00d03110000d42d071465031404140c1414069070034036007047c0c90a11940d100c0d849542e0f40f1640203525080141ea00c40e40d24002d4543d40c002d003802640d0640c000000c00000304043e411404843c003140951801755202c5c08015000d0320030b54003a00e45401801010060000040d2540f00180344060054444d115100c0c1c40c5e050949d80220f8070000403d00000600041c8420885141c0c1620348842c08016a03100e540002511014584406441904c000c10040700748803141c08203c180078100c02041000f1103040c0781484441e04004495805402081c0b40024103600100c125031b40c820036080554170b80750601e410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 268380323 1250 268379073 268379101
    0x50c0d0c020f0f160621050717010f030201090e0f1f03020603100e010501210f021b010e0d0914060f070804080615100e040504060f1109030f0f0303 65
    0x8000c214480d00340e0301c1c01c903804103000320ba800c0c2024a02800405003410710b1a080da10580d44580104084072102132002840c02c0c2034030003001001880032805885200d021681c0c20800c148021141d480c3c40000241200e50064407000c4902c01c2c0c8070b01070311a40c2e40b01c0d0100f00c410b0803144080c2600000c00040c0000d80240841081e820840c9601480a80c0729004034081c2e030400c549101e40c1f0741c804c040600c4a5011a0043c82c0102400d180c01c1c0e424400d03210f40d001d0ba40e00e03894820301016403a1101082c0802003501943c0d00c01d0881c044001903800d259243c44e003e80001d1a800350540140b00320f600546104507921015990101d1940d0110030340030060103004c1d1f10148001000c220b0601144000a440300b00410042103900b0090001e03040c22f0b8941240c8030b01014080e44a2034051115002c007981001c01041008001c80300058169110304000c0060308940301c0c1400c5003440d12800b05456001180a056058801d0702111009c1d41c2100b0030fa44d80702244904030344984e0003400054400c41c0c01101d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 268381573 1250 268380323 268380341
    0x41b06050409180b13032c030601050f01170c071202210316110c060a0f0207060203030f060f0a0f120605010503010504030504050d081306081806010b0405040c051c140a050c0d 77
    0x40c11090b42402040807034100011078841c694858030310047e030007a91404001d02400361500b156180703104150200041c0040f00c8904000d4600c080000004040c0180c20301501e2404d80c01500d01c000c80300007074000a4071242c4076040c4c5180c0940444542e400442c0d02015203219418500850780b034060443c00c2034403400e44482000da02c51240e45200505074403004c02038048840e8544907042603440080020742890340a402040840d4001d0041005004ada03070300003034000c5000d0360496084094500401d034958002d4100d13001c00c200003400002c0214881c800c0090360b03400b590301045181d0b01c6004160a840303081d01c002c0d00150050005210924061346000501480b9941042ca01800ca041c1c01300f003000d0f01c0e4040c01c040b50422041000342d850150140308080401005440607605183d0b4088240c02140181d500450392450701c90b0403e4040e500b260010240043d07498a512000400100540444c15084590841c02c1022500404503802041d0103507907400d4180c0d040c85000c079004001080701803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 268382823 1250 268381573 268381577
    0x4091b0504140d140c090a0903020304210606171e060402010315150804060e032a0a08030901020c19030c200405190605120a02040203041b06050409180b1303 69
    0x140f00c2d80008008061004025564002130f19148000700c00b003141d1848010a030030380d8181843d205900082d404000c40c0c00b40c0f010304820040c61141c85a1f00000c0c2050480b0042c0030034940200480d8a003000225900c1902004046a558207815038000c0440051581c00b5030b003039409140070400540c002d4100320034824400d861000401d079501d03850b0303100200551a03d8085401d5006000501070640915040005408000c500c0c180c500d6004151083c100101c5206090ba01c028841070000d0910100040d5500b100c03100d41c0324140303950760038000d60100111116900c903450128981c4200014811501f0350580c0701c00c5100341003503e0b03171550710004110a0441d65141d51881600c3d0ba80d0b0300c40d4034081d41030b64190440443e071030350b07010b011540580c211910903c041c6000039410b48000502c0030002c0d90641d005601c07034480b80741c100d0b484800005100c641c2100c50502041c4594007001808c122004003c060061162044555020740440507018250050340c1001031030f8a00d0400113020b42511034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 268384073 1250 268382823 268382839
    0xc02101b0c111516031205040b070e01030b0a080106050925080901060b0301030308040201230a0309080405030607111b0109120311060c091905180a14040804091b050414 74
    0x2c3c480710310f0348201c1040d06814115130310401416440300da01071118000c41002c01c0241000d03211000e588000034120010051004080b40441c0d1103038000d0b2032500e4000d86410300c0161501c24150103011070b40542802085070303100081610351180300060841032003000820032080385940441d89450014500483c0b50b4803400001503000c042c1d0001c50003140603540c0c3c240c0d182011710005103038034040c80c01071000c6200c0300c00788495503065a045820081d000c0c04c0000c3e480d00c0c18a00700e02c80380555440b0300c3d40750140a08008030ba541203400c56a1102d1600203076516915030b0124105102c10000481d03000030703400d4000f80042d1058070045041d96009080c4050404003004000d407400d42c04482c514049080425680201c2c101000c00703010380c003e0176120300c04650a080114500d443c4641420071240940703c04140d4031079541d4402e54044402103004075040c80c1c079040c400380f00d5105224103900301d03190001c0c14240c1074849455860f074444a40d0703a14a02480c08400407600983c1c010081c3e07100c501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 268385323 1250 268384073 268384099
    0x9010902090301180c06111c030c020d0e09010b09122e14010b16140304050a0501090509061c0c080303150103140604020a090e042910030213060302040c02101b0c11 72
    0x2c14a00400123842e030f400304420038121002420020b50144220074080d42803000426659418142030640d108042da0f241c480c01044001480000c0802140980f4041c1d100080b00c02c00523484203400c0343c407402000741c0c0c1c0c0001c160007110454104119000080c081240184102a501002040094951220254007448907142c01d1391240000582040a50000400300320a0502d020300c503006000c2401e00780099840c0030003149629600600c0d040c13142411403501110754403500ca4103140580c128003200703103c1d5110304150b5074960040e64040c00406074040e2120300c1d90710900644444941340d9130702c080a80c50316401e00c000307900120008001c0c44084640440d0300c03625050300e5441103000c1d2500e07002d404c6e400c5000c00c3c2c030000e9044040300c4e80450a01081f40349424440d0034001c0340e9041e150180c0641c2410020340060221781c100030b43c010f007031490126100b03a00050081000d1210758042001e03d04084501074800c06100042c404140e07846c40144c04a600d1b001a031110a501070140e00138001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 268386573 1250 268385323 268385353
    0xc0c0b010315110c1510060e0402031b0f031b0f070f050c040c20010c050f0c07090f02030402040b22020d060b030c0a020715050904051509010902090301180c0611 71
    0x10028040c0c2c00d80c2c2c00f030305c0200d540c804602c410715004410a0340c4509581c0c18498010000804030044501558000020440c01955545402c1c0114000f14403ea102c81c1c2d0042c0441d102d50040d00e181c40480389565a40000c0d218180440d80602001035489190100b07640d1a6800c103020290b0980e42801004040c1005407903d009007040c0240035a99650b00205110368a00c1c0d2440ca040b000703905030702d005154080c1d141c000c009c41d0440c043c20400c01e0744825182d10050301d0030701c03248c200c400128100700040000c26030940185016a00c01c813000d008950000080c040521189004003282103800d01c25101107802c15402841c82c1103441c2e0b8086a800d840f0410742040d9402a078065042840001d507038020a81c0c14090403003d440724008002d00307081e020100614901400503190f03c10b694031804500000740a0900100110020340300b8041580d44050400094104903807290095080940c1e09401c0c06140040001c42903008401420640c02d11004039400240c1601d20340080c446c4000c0e07c076a00e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 268387823 1250 268386573 268386577
    0x2120106060909110c0d14071b0303121413060204080a2312030c0d020c0d0f0207061713020307030501050a0504110603061005031b070803010303030c0c0b01031511 72
    0x41903110b0480040c40e180c0198201d40c125540011016018010750a0000012841c441184018900b914200090000340c0d4154800c1c90030040c00b8800807003d818803050a0319546088a00a843e00800d4804622140c016103184c1c110f18007113507400000003800d41300c800c162507000034058280182405c5d194001c852904086040550381e100b00540801803c0c42200402207500300000301401c450b01d46012034403864000a800e80c0e00b012404103c1d00c1070001c0540c1070b0f41818000f103080b01d007140c0f001e00c00a0f24051800805000601071802c0104600307002d080140007948200c0030410840e40c03070f19401c2080070240c8104907850f0042d21400004a5000d00429010b802000310000d007034201032a111860070b250140d0760380128024801c02560742c0d0b503062002e280c030300d40f030924903929035421014042046034441c40f800b81c2c010100c0e2407030a00070000080e505a92203a142040429a0381c04240c07a03007240d0364030091207122803200600005510400000c104514068042000391101c2003c04484e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 268389073 1250 268387823 268387829
    0xa020f040b041a0a020303130f2012030a082a0a081006090b0706050414030408030316031e02130902033301020a0201080402030a0204450f02120106 65
    0xc4008901070216800740c04003c070f00c8040c5040e80d0362400062000c081d4403808010040b14030101c64000c1c644c14000030112604003e94402c1200b2602c908010504001c4010040c42a010b10a201c3d8104841c01c0c00004070381c00240551110b14059903201058104c65600c0940c0b0101c1c000c1d4010814002550a0064008800c03141c42c0d026107464100100350130080140e101c1d5040028648040091403242c01c11540e542d034001074081a01d07a16401d188409411900b01b01c0c165100c00a400038801070040003450041c1c85516000003c1c0c032003400202c050b036007452407140d1034141a0514480c03404c01d560082c1207130100c000890380381c1c41d070700c040c140b00326003040f2940d01004d1048542c0458401420394540c9220528010b02ea1402140c0c000003951400c042d00003c0c14400840c0200d4159507041080821490340244103001c0c002d21030303a05440107050003044080f03030110016560340d00c103101460444010781d840f900c1c4005081c592280c00c00451035042c142d802c001e40f814041c035210406c0c0642c0002d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 268390323 1250 268389073 268389089
    0xa1112010606080103030e01090e0c091504081501350705030a03030605010806010815210d051e040503030a030f090204240b13060503090f0a0b0f0a0510050103050a020f04 75
    0x103c0e40c510704000c1e00f41039000000c00d0420000d00c030b0070b010800c8648001c54001c070703580c4101074480e02e540380414000804500c0e0207002240c040380000d07540200007456a080c100180011400c1c0e41c1c0c902d1501c04d0308052150702101108410b00003a0103507160301010400e0424070003141e86070740c0c0c2d0750040381c1418a104001c2d0000784e2509001c0c880f550300034010b250040d000f80307403041c1245402d9200e00d068146250035107200d421790448403401e4007050013a010f60500301c0b0050b54004a100d5001920382c3d0300c0721104ca0021802c1c4031042c031003006000107617002c558010300554500754042e1421801011950002c0c1070555480c2088400340c0ca5074031401d440821406082c40c90304224a48108500b15242e0014008034010000f201c8804004036603182281c020781002a03c80d00c4602c81d55040080c0300122980750f01c00c1c1d035404da00344151005070038000d4041024200b0592104282c40f07051342c40490b0369040c0626004030030000c0f540700e90306c40c40c0c0c080c00e0498010300302060710005204950180e80301000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 268391573 1250 268390323 268390337
    0x30c03050709050c1e0901090e10090605010f0203030601030f0617060a0e010b060d020c010921090b030c19020f0d020622020312070215071505070e030a1112010606 72
    0x1282001500c101604000711359241818007840a000f61010b0005051075049200c020444200703503401500d140c400703001c191421449170b00c1c240c1405da00d503020910441702c0181c10080000f82550040c02c800d400d01c004d07540036500d90b07034480005402a00c030001c440d240903985c6400c00590390302030900100340c0300c2500d00a08150308080090006507201400015000e0341b4211400442d43d072100b04498030620840000340c0c4450300344450741d0041480700800345c101d040949801c01c011600400d80742c1108500d443e041d440640b54001036400380021600c98909050820140e1000241c0c1350301080b6042070361048401d50890480c05600702403060500c0c9015910500c1070201e01403800000042e102c9800e08000ca170150f80d40c0029580e80030718401220060307400902d5000759100e41c5061000e21019900c032585c0c0d4599894142d1500c1e03c1000600080e1f0f25100200d0002440ba101401e1001c41c001e00034400004a51100f0105105800300a0347c403410160302c18050040030b0080c0e00c010142d40d01d480ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 268392823 1250 268391573 268391579
    0xa17150901110702040518010e100c030204030c09090501061701020c01050c0f07030f030b1e0310060302150a2c030d02010903020319110a05100608010b0f0f030304030c030507 77
    0x60504000e000c8110036418407202c001c440041e00150340350141c04403004a20707925902840503c030b54294440d1211942010b0300140c095000142c4905c400c030108000b0008040c40e03500481c202e0085000003403c20031144010001c500c100e80021850307501903000014002d036500150511508181e06808460350040703101c55040c0420300c41c80d0348c40800250010700d4100a840212030b2841808801010300c40b980c500c1100040c4a544901d440120141c070005032003c1040540f01251407208e20540f103031281c0044204502014002c000071170754040c100404d180c40440c00d0b00001d4000c041c2039000c010001c407113951008142080c1c07030402000c29145945010100b800d160400105200180c15607041468010000350b00108884c441005540c4041c1819080300c81100c0002400303035500d5143c810120107000740040810648410b8103c01c0017089040c0d603541d80316086c2c07652092015031000c1c80404000c01401c0502100c2c1401c0360060070b4925180d12640c4608850215810035101980900814 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 268394073 1250 268392823 268392853
    0x17090301092d050c011107150519020d0f03240b040504110a0f1d030a06060501030b01090305030405041d1b0117060d0201110123061f09140a17 63
    0x1012460403a80c4607a403031086503140d056803130311050781c002c0c10071442101a0b41000390510001d0080e0014807400070070b03c21044d800038142d0304000d01c1d07141039a03014526044141e00002d00908401e046827190454158120700a90007810001e50b2241e00d2529152500304642d00c0c2c0d892030001e0681e5011041c2c03600d04003c14042100d800443d8042c11030810403000c9501c9800071240c0c60545e006141a6011185c242600c25691800d000740640610490b02410f00700003841d0440d005a410070381e01000b80d405510011075038120300b84400341c2030f50000c000502035800c0c0b5422956a640d201c0c00b800640c1d007560718001d46000096614000380e052800561401982d200440c40c8441011066600c2c4900f407000000c0d0600244010080c144240d0708483d5507010020b40200c03400f200400681c54583c0c039101941c040f03c4e03004075189407003500640605540200c0302c404018030b0101a0f0744000405081066100020740000f6130203921040c00c803000510b0200817112001c250004401074001042c5020310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 268395323 1250 268394073 268394123
    0x7170712090c0e091f02090f0607050102090f0303030105060a050c120f03041703040b2206020a0c0b010b03040c1701060b07060b0f0307060f0f03060509010f030506070503060604031709030109 84
    0x40b04d145074005030f60104175440400c01001c0366a0f80303001c0040c3c1d1610000c0004401140f20404a9003161002c110300c0d05001041d0b01800c00070b00d0544650302050b2545c0c003015141d100c240a281c2e4046024081d00c602070f031180010b0709901d2542000c4414000034504074402a40149032001040200007082200300b0207416425164509107003030f840d0643c00c0c02d0f507030f10b46440c00c01000e0790f841e04076901030740d203000c880d080703900c0d01040c1c01032800c44d030b00c0303904140061240240040960300a1900000010b500c0388000440340b20b01e4001c1005419141041c100d8405000c04810100300c564a5900100340e024154005200541c41030000140d10680f080030310900705000c2d04010311070b0700509401c211468102030b8410503c1024a86200c00300210b4405500511258000c241c201841900104d24803200c000d012040c0c80c016021a4090760359040200e450b0700c0100d4056400280920040001807940c01032118a0080100c207541000c0000300402d007100c1520100b9150082d0b20505240e5080100c08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 268396573 1250 268395323 268395331
    0x180c070c140109061b0b04120921060c120509031305120d18030804080322120f0201090e090a14010603030234090504020f010807170712090c0e 63
    0x760260281c1e000e00000e0091010340c0320b600b090202a107040302030103035400d075400d24160740b00444c101c00741041e052400c4178000c0c5130b0b680b1010850030303400401e880d00c000c401300d644043c1c5440e207400c2100c419038a09019005100b43c4c1c10902a1404403000b4080b81d43c050680b0a2070700340b00640c0c0f43d4041c542da03403001604a50003580a60b002420b11800d010703000c9480c443c8140d0600304054000c40003018500500ca0b541d002030240300004c038011401e160b01000a02403c0700d0041c0d41c80580c1b00040d4842c21a4595100301021482d103d6240070024460003814145075005061104906039a0714118510400807038510000d0b0300002000700070040510003881682d0034541c001c1140a086580107540c4403901591200c080d4003e407241200e5503100c00080001184104100c11000d6a56801001405003514101d00c14151212401c0e0594410354213075106000c1c6036620840b42d9455030404142e000302510720020045007140c00071002885020340b14155200d4804558030324076044001d107008201030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 268397823 1250 268396573 268396589
    0x20d1d06250215060609040204060512151e03160e041b0f0506030406020c0a050303070305010503010513140a06060602031b0102040b04210507140f040506030d030902180c070c 77
    0x96900d55682e00080320244040307603040b00102511194001401030003141d1401e9801800050b002c18000e500c60041c000008060b103072108142c4a0081140c880ca1400c071060b80c008840c00000b03c289102142c0c8400183c0b0080c0c03d46001c840600c0321010460200d800c004030481100c0140005c2000204484090700340c0c000c0c0740c1c1c1c1100d0030000242c8540049105040c03060710080003090074405c82e40c0c110b880d28240081240c82010311403030247e49039001150898003080c90030300000307043d05040c0940c034410144040e0304d00c2d00041d140e5501108840312440c9140c00d124410b03406000071b040c0e10601000d0300d401d4008584803161b6074030710808011029292100ad90061004015443c1440113460030741d0b60f1003602070085198030750381e4030300c00c86a8100a0818845ca00c80010030b009a405500f410200546201d505c0402c1003051009840081d50100d400d580300303ea006500900c41d5019079440e0f403000b40035822296814500000340c03a01524412940300b00000c0704e9040203164001d02009004074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 268399073 1250 268397823 268397881
    0xc1b052a06031521030a0c0c090911030607050403110103020706090c03150b0a0503061b0f0d0c0e03011505040b060c030d0b030f06040b0109020a2703031101060b0d020d1d06 76
    0x10661381c80d101c0c06600c05903400d003e084c203214010081280094405059208030801000daa6400c144460481c13a80c4c1c0180030780507103001304c0e1145119208031002d480d0007640d510160361103d03004600a40c070003903040d204e182c0d460344000c00288a44081d41e00950091012480301c03003070003044000702d03081806024414003000104004c1c1d03440c007144881c2c0c000d080801660408030a41044805403081010303504400c5000100c400c0f0301c51481d8030042505061b80c2e220b05c241d10b24181450300300c1e520051030040350744c4000c074108107518207034202d04081b0a000e800c440c140701008041901d590814400202c1c416140c1d40c407210541400c0016100928102c3c0c010592410a40c0700e142e46000c040c001c1d03583c1c154001500138800c6000d45980c0080c03031a03090306d1100c0301c14854251a048070407804207d00180822103030781c0d0300740300501030441070f61610100f940c0f070880b84441c4c2c040250b01520072031042030786414000001d0810f0305c44d01c480c4090000003400032840d01a61904111802c000d001c0121080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 268400323 1250 268399073 268399129
    0x190b130f020409020f0a061e03060602061b0d06080321071b0206130303020309090c0c101505030106030c080f06070503040f050a0b09010c1b052a060315 67
    0x518280351681c0565002880741c0050010560528602c416a41c000348541000624641d000600b01c11071140e0051007800c1c4008420708505917003d621540740140d000102290522517059407058030702e041081410710f0105010006016203115030b01c0300d40c09070004940c83e140d900c4400d140c250300d80c0030001d00400900e0940d401074405051410f603400e115400b18851f104540b5008100c960f2176450060408101e42d03a403a0095590340124025400781c240304c000704803100078200668019402c004081c01075036410200c004002c21088403000c40d4101c0c00040002d4545003803140c8000b0f5170003070304000321117810410990f2400703455030b1030340010707910160401014941c40010f0700c0e001940444000d0140c2e03280c3c240280f17040d0030014054540180282400007000c415440b85113a04200d403198145086080c500d11064510754001401d07507000812121001d55100d100911011000034002958507024401714200340c004a485442404070b1900d00360303291500c4581402c0c0c0ea4200780040c018811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 268401573 1250 268400323 268400333
    0x7050433050d0212190f09120507060219030203040c0e150d0813080c010e0d02100c1419031106060d11010c1505040605071b080318190b13 61
    0x5229200300100040070600886910403601280c1c01e20640c00003031809800c002c20200c681050700034150210903e0600e0111048481d80218010340e50807203036142030940e0701641616641d00a03c0215001d0b9800c1140e02c60a080840d032107e09015a9940140c4071b01e050b1511050380c0f0b250343c1248a20011100030000c0240b220602c0010440c1d098038078125480c81031901e91150700588440700000c114032000850301e200000760520001e031090b0f0b5500018241c034428000b6180403a000690005654840c519909010306d02c9110011b21940c940031704503514008072800e00d0010543c044500351401e080401341503020b1118040502c81a0280c00b860800c103001603050090301c84000c1c8440f04401c0c146900c0d0303000d40345200025400c00e0700e80426598428520005001c1160210350461408000c01c032514403441d103015611880714074081d0031200741d442e443c889070001071150b016401034030812141e41005010303002901210221409251000b481e00000800b8010100c240c0340c40c0c0700c150a40403130 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 268402823 1250 268401573 268401659
    0x11d010504020a03020712020604030905060c060c0c0a1b090507030605100e012102030a0509030901021b0a051314010b03060d030c0c051804050d0302161b0e070504 72
    0x300d0440d401641d43c6000207041d400b80c0600100545600c00341099801456008101c0c180314030700c641d030340b111810346030781c100580c60040f4001c00007942d001900203110200000000d04c03038092010200c81c40b0180030b44e50700c1840c00c07041d51400c001c005001e0003000480d80300d010b07994000d0080c2c142844240d0900021510003101c088000040120181061465074001c00884001e41d4a044d01706002c1c450710b04181c0040c0d441501c0701c41b11a0301c0c000000e10f03400300100a481042c1c205a02418018441c62034210b10520503019842c0d100309046400501136030350950100e401032882602250070b030040300b9216451344050b4040322a12a0400400c42142d41d525a2014441d40c0b50500007070b882d40b07509026040220300d40081e90841c0c8400e00b03166107050042c1080340304034800d00450380790302c20242d011410f90043c50895000c03594803441da2000036444541555443c0403600d544000c180d0380710600c0c8120b1905030755507008110009000e00031070a807698850300341c10320521482c0454001e420000c40d04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 268404073 1250 268402823 268402829
    0x1401051302062d071103060106091a13060809010c031a060c010608011d06090703021c1103060a0f0606080606030c030603070b12010617060f101103031806011d01 71
    0x1d888000b610343e41e540d031200c0ca0030f0801402d088061600c80040302c9402e07444d502641080e10004d81d0322013072807010b03e0005003141c103940c0315a0380e00c04911719207052001c200b8256100480074032010b014420103400d100c84100000d00041d070381e0542030700702036054508440141c03840c9020103041c4240c0c10301c041003004043c1540c4d942030300c500d5510603218901c01e0040960341c020104550a00d62071501d00990700340c91070707184516602030f030740b558854100080e07a941c018480207401081034088510720340d00b000e83c10114180a07083c281130280c00800001c1c10013400704da0000c040c030303502c1c403c10070f44401510902c0007070714290510500a09003600026107902000b402c4052030b0100000143d40d5803001d0010303000071300c5901c030596120040f408820b504034009004100014107401e00d140202c03c800b1284501510029040941c81580041800040b1000f5488030b41407000c3c20580c034041081c104001c511a1061000408001c020101300c0d03414424181d200340046400e0802c0640001c00707910b800c2d811 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 268405323 1250 268404073 268404079
    0x21e280b0105091e0115021c09060513051809060109090b1f05032b0503150d05010b1305060a080a050d08040f08040602060702070803040b04051504030203191401051302 74
    0x444c0d42e8030074010000da0384403805075100107140000065194008070150801409a4090368400074901034100700c0901d00e105024002617200d034003003001d079024400800e1554000c3c14005409900c440c0410000c0150390341001d004480b000030044d05800a0001c00d001d01440700c3d0070300c4182607a4881050084001d000c002c0d01c0c0b510b81106503a00b40101a0f51401814007800b9503101100700c40d00700901400d012140710100140702054844180304508591040000020344644c03141c03038800380000c0c2c8a651071704840710365950080c00c0482e91141c041408214104c10f02092070b241441c10b104a08025a000c0c0006500421421001034808140c0c0403104400c2e251505070f507a0f850a00304c002540c41d075409070011900160205041d039010a12a20480303803602107450160340e402541e0340c2c03803245224807080c0100610080c410b0345841c1244c444074541c080402c50409480e600041d0803c40b400703105034a803148082107402000206c0b90340d401200e0440008120510703104441005c45090b600d0001c4c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 268406573 1250 268405323 268405339
    0x18060201060f14031e03180406180c030e061501020705060f03012117070501140405031909080115030317040807081614011e050c040e040201021e280b0105 68
    0x4200e8078200030703400c040c0300c464100f900017010030880c130b9441c4d6210482d51021940c3ca00e8007803116003001e0042d10121181d51040030500070002950030001c00c40e0020b140c00301500c888202c41400b900704440e500480880d410030019044d0341c030019141900961215015003000c1c0b124902643c0d42d001564115501768426902c441d00d1040d003902d0740b0000b6100180307403603d00c0c40b103174a000c98820301814105100344001c1242d0b10780c889000d00540c104450050490b0b01c02c2040740c40310004a003003a0408142d500700034024544400c036903030940d00d0440a503000340a954904005065001c442c542d20710355004020b02d0701c0d007440d84a2044a102d0f00e40050314010000940701c40c8082906911140290000903201c901034102115034082c00028103640c40300740e0096202c104a0880d84a6580201510741416140624284c4c8180c04c8400080c000e0781503000d03801d040c00e02d8411003645681d0007094603010300f4540c901e8141d801301849500c055007158441d03542404001820310030b01c40d419103604480d180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 268407823 1250 268406573 268406609
    0x501180b070219090603030507020901210206130509040b1605030103051b15070f050106150806040b0d05070902030610030b2808030c0c090f09060106050a090b0a18060201060f 77
    0x40340300f9072580c0080c118a1428a002040c1980070000d05200c510840700380e02c40b42d0340e66440d044200000044681c00d6510303001c40c00010f20b00440144401da014185c003000c1d69a4410006891000884d0140c0c0c00820027400c00286a10722124140f03459640d0900324255411900e0341c40da2199401a01050490034183c0100f180c1e0b102000341e004c1901400c4140c0d0349907a01d00e0800c4800700b00f08000c503074079801d012011a42444a45071181c2c0b07035005585091903030340e980017008060440300300265000300c0d600c0d0242c00495014805403029080c4078602503582d0920006001d1803604c000d03070800805203800c00c4800d0030360350090b6165941c1d8802045480300040b9180c4002c42099542c02880a4407002a90849141d4041211f410310002101c400a16558070580e602d2411300840e19070300309401c030784010300c600c0d8007405c09400fa81280f40340042080c2c1e01c54840006035403040000c1c2000c2a5400c20084079812102001c1000e071089100a1002d0752504004890441c1c080c01240c20611804601e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 268409073 1250 268407823 268407859
    0xa0c0207151404050405040302010b130b0f0d0602040302030a080c0601140d030f033c0b030303160e06031312020703081b0c090c0304140f0d03090302160308040501180b0702 76
    0x20f2001344c000113000308440d041030b24001c1d008000038180940100020310081c140700b002c0e807059800400000d030581600c4400c01041040e2004450300403115203a0a210210250f04c1c10404001494428900c041c1d0300c030b0304825103074581013050b844224101b00343c035843c00381c44d00d0b5041d81700740440d41030400c098080030505058000d030501fa041c071a4460300603081941401c07503550020b5001105015407600e0a8a01c0301c420040e10000c1c2e414030341560003000842c45510008821464290061410342d00d628085170001d040c9a1040d1180f00703080b00d0f1071a0f00700a000c2a130400300034500c0d135400201132740c500d103540325030303190142c811035040c0001e02c40501d2500d03440a02866804c844010012800751a200642c079800f500181d4040d01e0200751b40000c5204031310000f174072400c5201908001c041035034405d030049020700300d480422030071030007038440486140c0d103c0c0019001542c45400129199420200014040c01d0f400000c00b400c0400d140080000304442d8044525040d0143c401d051005824694 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 268410323 1250 268409073 268409077
    0x3050403210203220515060102070902040e06090c03090c1011060c0c1207031704030c0503070b060111071d0c041d04150903051c0608010c05030a0c02071514 69
    0x80070006060054100280c0a41c550066101e00c074001401c4e02c200b2410f0020302040381d1001c1d4010540d600c0703001c0841c082c0c201c600034154000014412240025290364800e016a0456030000031055255418080c40380380408045a11103030007903419040d4981480c4141d0340c0c0a011107500d010b40744161034105450322800d00d030310000d0480e9044a09504090020110590002c0c614081e0ba0090310980100c0d140840110f81c0384a40582d40c0c43c00ca0340c100400e5803940304020b0400c0b01404800360144000540610103000014000e00201001d0710b01180050040031500e20907070955000403134207201c0380606504030340c1000a464151400340c0d9500b5010140c03442603400040d8070007107104640340c5025885183c0d0b071040c0d104c0c0f04030034074001c00d41d640c41080e62500c10340140400d8090040c920b0640c8598a0112090420600400c901e0703901c4a0190031a00c2c85c0d035006001135400410404074100c039016000f4800100e2004000c00c0d882d00240a011a51902c0408104007030750242041c0311104800b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 268411573 1250 268410323 268410347
    0x3070c0212190b150303070312020a0201091202061501050c0703030509030312011211030715050705010f11040f1e0b0a020f19200609060f0408030d0212010e01080c0103050403 77
    0xb00c041a29054204180744400c01c403040c8002c203060010560039410044240c602c090361540307651404042c01c0c0751040203900300c00411400c66507103400e040082a1a0420300751000056006020203081013410b1b02614400d0080207410b0050402452901c0c0e0400540c2c07034216a01413a05684a524110010741140311b00741e508090031044000110b5141100d008141c00248200141c50f18140b0100078180c903212648155071b140e2034034401500c4258000c90003400d2061144000040241c0c01c8031503001158403c1d48a0b0b056400040707070600508441c14220406440a4011005150800c0012020001107405a10038808003c1040100207000300555005003000f84280c07200d4103d81c0070642c1000446038815581c07440103121411200582d07500c500b09031100074181074038224a40f414001503034070807082d0700c1725145d040000140c2c0c810140f002c0c11040032a00000342c0d407054020058030000106800108043c01c2440040242000005190207c40380030300340030030241d48a050a030303025541c81c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 268412823 1250 268411573 268411603
    0xb0418020d060906180c020303010303030b060720010912020a1a120c0d11031006050a0203070b0f0403030b090c03240607140f0a05031b01060b070309091103070c0212 73
    0x5080460803e0303880d040b520a88040f140d21100004500303601d841174039505500c0c040076800400050010900c6604540002d10020781010310f450159038900612182286032003060b070544059400c80c96a01c2401c60000308203400100b02100c0c1c840c5c00042060b0322602c105101414036010014090074a0b6054440d0f00e2000044841241343c004188141640300020108070103150188804d0002e1000e010749000e261004080700d0024200a41038503541e00018a0300c05610052200600086141c04038a1040e07800394030401881c200f51a015054506061480d0b1080e1032100030410320040100c00d89030701030250500300f4004030300c21020813000c1c0412101c1c41c1e0407401c0002c0e803000f440401c40d640c00940e080300c4100c0703941d0403503010203a4840c0f900d244001d00c01c2c0c10400150010643c81c00b0120000c5a9500001408644d54490074405521400080380481d481200c10010780255100f1802e001e400c150841d4518a04124001c0c1030002d5400020310400c5400ca8034001d800b02004480c0c11803501c1c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 268414073 1250 268412823 268412831
    0x70903080f1605030408030408010f0e0628230108010c0f0c02010309020406080610090c0e150d06030b04060c02010b0f010c0c09060612060504060302010503060d03020c0a03060606180b0418020d 85
    0x20f046d0460301e03035100f8000c100b050360810b4a100c1c8091403610468000b48025030213014291111440d0b0b0000c994652810074015805022420300300280340700b0350710019002082d0240304c01d040c00c80d085080405034031120003640f500604e64001c1b0340000040c588500c951412138041411031006900034058a24040d4209280110104030840002161409100003034020500566502d00800690303c112404600092102c80801003d0400310300c042c0358105504032207030600c01100340c00811100350b40d0090b101d8080500a001c207209191043c842001e00ea40f0007030280e9003181012510107990600c9450410040c0c9154030b0501c44000c06c20301c09001821000d2094070b07a252030050891216510300c8405910340b5000003100e280c0340c030175402200d5041e10f44a0079691000c1c06c100301c0c0f0000c40d20030380c00e502406408031a641e81d10a41400654441d00f4001811030601c80000c1a04503082e00310315121038008814490b542c5550140c808451400801400e60700d0410711100c0a4001e000c1001d40413810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 268415323 1250 268414073 268414079
    0x60824220c030c020c0d02011b020d0204021305130c09140111120a1710060309050a0b04050a060507081b0f0912010e010507050a091a0c030a0f08070903080f16050304 73
    0x2c103401028840c0ca150b8221140804090308000c0112801d020085c00318028100f00007400801e07104d0305807030b9400200061030700c00d290b4011070142d9004070a500a040c5010f002440245031a5041e012200080310f81008481c002160280c01c04d0307424020142c600107000b9020303603e81e104002e2491040110810384014540d04881040c15411500241c0d0105041e804002c50b8401c10814451050312443c2d80310485078a03258040c0d00502d0766003803d4072103000b40001d241c081464050658000c521903401000041c1590074581c04542c009080d1004000e1240b0a0040c061011a40c400c842d02c41a02001d542d4070060307000754601d1080c458501d80041c1451031003d40c1410641c401e42031001600c000340b10b2070391180c908487e0b5118141c0d8040216921000a000c45990300d2040b00c414841100c0c990314014601c4685440c44d000350000b000041d242104840d480795000241d281c000a284c07c09214503070540e40c62402502400c540c00106c481d0101d800c0c24900080140c800207150484103903035882ea2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 268416573 1250 268415323 268415327
    0x2011d12060402090a0e060105060f04030b130b060607021f02071703070506091f091104062312120c0a022206060c020d03030507030b06040f060824220c 67
    0x2c4505921034900c0c800080d0000c4041d004e060f1b000c140002c003600b0a41e00306010070006800840c041c0307501d0300c0240070100000b40b61000700d600601034980b240c09015180e06c2c0c0b03010304890043c112405482c003070000340016120780070709070050401d4094460302c01c0c1e28110100c2c60701c41c6d290300c01c01e003904091128400c0c0c02c0d03012008207051030140094070025070310005a0703950b85117041503100100120822001c0b003132405034003040c82c0d60300c203098418001e0542d10009041c1c0c0e44940040842032401e07184618101524031081c43c0c60038064500c1c1c040002070440c010344601c0301c0d001141510030000352030040002c05024001c022a4000c010404034001d24007040c41341c007003062683c510715240c44004503640307000c0d2186124090b802400c0d800d102030341c1d0360304030042c08001d84071006264481c064800d007a9030b200c4c003400103000d541a030082414500007004003900405031255000040407182001c20400e0f07924070011040040c2c42c0c5904181000e208050070308000740b02c2060310303441c0004890301e42c0e07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 268417823 1250 268416573 268416583
    0x302060a0509042c06060d050a020d03090b1308100902030c040b030c0301050f070909060b0406120f0606030e0106060311030c0f0705060411010e030607120e010f1109010207060c050a02011d12 84
    0x366400c17100103542e21002e004450b07100b0000609140d0014030f60a00510b001090844014800e02d001560569560710090a54002c1408401c00d0141d80300c040c408030108008420702141c2d0114103006900d07003900800c3d210b00c01100c100380555141c1141d03000d551001c01c800c2c0184c0501030020800307460300800f02041c0d8542510440001444984000382403481c9001d92015242c81c0c64a0601d060701c0d002e030640d07005054080e496101c80c1c450031001543e005030702c01c42c4010324054401254a080c2001110308450300b58008006241c607068000f840c0c5031400003a240d00103a6072031465903442803c2d0850b8202d00032188001c140340708013810001000044103d0507da80b50030b881c7e032441140c481041548501c01194010005a40b4120001d400107580c1c1001c0071082d0040c2c0002541c4c414032502d40d054503140c20080c8002c00f00000c24000e6541d040000c0c100418051a0061000009130ba499444000c450000390410030b000c1d08044803803105256210303800100500d480c48055130494403985036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 268419073 1250 268417823 268417901
    0x901230106090b0a020705190905040309031b061e020109081606060b12060d061b02030414030616030903120f1d010c02071a070c0b040e010801060302060a050904 71
    0x70b084110001061401d8100380da1403641c203600544000c030f04100a010a60605240080007207541c0d02c1c0c00a82d1895030721030140514026510030060b6411130906094420001424104828089000b007164561041145071480290043c004403040d00c1d41003240900a510b0b0040c144840c0098580e204811103905a6100340c031079032051044a5440500c401c0c98090744000441e2484d9000000d120f602d008501d42900314407469000500480c1ca81d021201c050000c982000075a00c0040d043c030a008214020343d8684038100c0043c5000d241410a81448400c1c141144090586074049003041500910481c650700c101080100711401c00900418042c16160b41c007500000101c4c0040000c0c101c041c001d601d1010003d4000700852440c02c2c00c000e0241400f503050110012083c00002c0000390200001c200616a41000549450826804c3c85160006078800d0792180e240120400050711848155090040181481e40c1c0b60000381c3c02003000341139182d44140f80c00903050a5160701650303100e40b840c0703a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 268420323 1250 268419073 268419077
    0x50304081020030a0905010f05011d06090112020d03270e070306030804050f010302041a0702090c07150c02030d0603030306081204050a030f03110a0b152202030901230106 75
    0x4900b602c8008503101802da88401c2001441c1080051a00500c80d00001445441500006048241d2311807040407074800780c0200380ca00d04400c4241001840404825401090450380c0e04115413500b0014101c40070900700c0280240d01150480007458002c0049025100c40100e0380f0040320040c0200c1c6900044c140201c07c00008a100407502a912034410b0340c06072907000005074945400d00042107940e030780c0c1941c0d280c1019000c0102240040702103100c603500c200d030108910340f80c001c1841003018a4400401e0510800400c1c010b0f0340c0425080c595409500c5200c110000380301c071105000300e00710702c98841c00802081c18517100004056160380400100c581d44000c1d02c00e000c440d143d00b00d5451185105aa61000c1d403d0001e0012801c982039203030f800c40c424101211080030440240d0308081c0c0b841400d44254248a04200f1211000541c0181011080f50f191845070700000000c1c00040024525808650f4080001180c004007540702d030f11003841640310100280c81410341942d1002c2c0034021000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 268421573 1250 268420323 268420331
    0xd2306160302130302040e101a0a120302030a050d0615120501060c08040b090604050d0b09101b08190905030c010f02040b120402010c140d0f05031b0d06030503040810 73
    0x1108620034800e4490005030786041c0f481e120301d182c003004054080b100702e08580c0c1c0940030140300004640e100304a80425a542540111070503003040000401441d0702000716480540303446070001e503011044030803c01e85030400c1900c9035001c01c1403a000344000e0f00110200400c003540a896243c011410002003114442e0500913aa01c80c0070480c0c1403c80450002d040c904284401c1c8070621581001e80a5803070040c2070903003400d035100000b41c9020b090706410f031103090304a010300042d10800c1c89121101040f614041c0050111503030485145920350410720108400342002c500f0f0446e1b902c02080070100394003c1485460414106151641d200d03a4804410f036192041465090300c4500a4600f1142c00e406d490b81820081c5c4c00c000380495005104904001ea8030004400242240309414003145404004003207024039050050030220341142074009028090040145404004c03a08103e0400c900c001140c0f5000c0001c03d40c1d000d40f900381c20043c00c500001c00c0114000b50002051102c034040114140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 268422823 1250 268421573 268421611
    0x80a0206040c1a0406120f0203010f03050c04051302042d0e01050603071a0a02030c0d0905041406100f050904020a0c0b241e030706030c0e09060303030103020d2306 72
    0x80480141c442c071034456000107000801180d8011046c03000710340c69500f00412014001e2483c2000c03139209812602d240980c903034050060100030007070144030145c240c5040019050284031001f28403030b0310b80c000780b10342c1d150032048440c8030028003820911800d08260b100e240c441c01590030080c1c0040c0d60704200035841d1100080b150700c2e001504904890030f280d00b01c1cbe11000300108604103940094101c100790320003000180ba20a03010004803601d10359035a280341805007080c08100981d012681c075900725901d07102c03d0243d141d036175030100b1280d01e000b401c099441012840013610140500400300341e0152000ca188065203812000c10b941d51342c42243d92040d140e485500e200d00303802c51070503e0303103d80c11048104c01860900d52846e00041c46c1d03070300425402c0700e00c01c2c00080c81c0950750b800c9140001d4031203200d1034501e83c100300110b501001c125008c3c245841c1c2440804e43c0c0340014800a481108008110b10600c012181c0f904808401c802c82d4031205a11048190f6803514207845452400005003106 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 268424073 1250 268422823 268422839
    0x504090e07030b07180b0c060f071d011803140304090b06031003110d02090a0609050c0c1c03090b0c0415080f04150204180b13020a08010b0c0703080a0206040c 70
    0x20742e60301c0b80e0240d101d601e4034103044036081808440c444e0144212034001c10070103544c00c042c10300103000d40010102851b254440324401c60f0050700c4081402101e043c4010840300640302400119400c0c81d1500d5401d402c5982c81540c0700f000d50024008100e0a0705109000c003010000704103440c000b190038000b820901e414800b803848211414040c2c115040e400b07200080c041800d03038029a8004001e00054802034000540828099807451915070340ea640800c40400c0c0c900429074070500c01d11000341040080a4090303100d6103034031049050300c2010b100310b42a5074041e40c400c0f10921b4001d000300540303183ca0000000035600501a1a4154041604c0c03a0040c5101d000c40911a0f10014400c81140d102c0303039102010105c1c1c5240b4004206c1d02071001190915660140d00c108d1981503002040c952b00390003c0c0a603e1404016181100f4010800c142405412442c624111481008420741e034002000b409410f180745500000e01e422400a6005c401960000703a41e40200e0180380b000403075030f50319046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 268425323 1250 268424073 268424083
    0x606020a200429240306041b030e07060e0a0b130803070308090c040908040320060c0c0a050409050d21110d0509060709050d05070f0b0a1202030603060105040209060909070504090e 79
    0x2074050f90003250131070f68603109100d000c2c40c1c2110003e0004504503a004511580e4200ca2000c643c000a07a510002c407400c10003041160010710341d03400c04604450008001c501040070344d0107111411400043c00004007090629190700511013003094946480903403400404a0700c0c03e42c5c804645124450801441d89010300c5031000ba01c1e0701c11081860f00f441c580d80c0c4c2c00812059800e804400400030f90100003030307c0707a20041c0007035030b0900c029200c030504c030900300400c0954a0700650f01a038508806400090000565002070001c0d5040c02c08004000c140400000010321007a0400d8904040301c4e41c10004004000d0314901584490500040d80c80c000b0039a03031110105c0d40d0200150105100b001035080401c0d211454a008006650b5556155240300c04420495400040f041c603000591a940550000c070076400d0410340f0f8829441c42c00c00c00c0000b0340d19203041c0140f5125940c000b078012525904c400480314565000760680c135580c58912809442a001407291844450401080d401e4500740428 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 268426573 1250 268425323 268425349
    0x703030207080c0d0b06011817070905240a09020a050a03050112020d030e0609040501030f0302060c03100312050d05100f1d0a0f060503100e010f0606020a200429 71
    0xc0a134940d0310b0251128103030b0402c09040740c0e041c002001070110303207442e0f0069200d000d030120f0680d032300d2808078120388949050055401880c5042c9401c1c18408040c032000389203070010b00c40c4400d27810644031103030000f4401009c9600c44400b0394800266640401c0d0001d000e04400f400344c0d1400c2145a9850440e114078840e41b1400a40c01718007006000d0004e030040d800c5251110020300340d94140350f445804030b4121102a00281c4911104010724810154104001e540c000d9620083d603056092040c60209122010300008094803002c0030f003030040c1881441900c81c90507030350200380720504005640c03c40c1011070340103180c54015980360218158290210500003038411100d0030b00c2e1030342d07a000c8030001001c078221307440d0215413a51400620b681d001c00008106d00d101080005001c80302a40701c0f0700316591811041000c03820140204800c9401041c5850420b400c100c0c1b040303045c1080e8100e46400c1c81d2502c00c1d141e005144c808000c00c1c902d0807902500c0e400c00ca00e440741d8410300003031041084201c1582 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 268427823 1250 268426573 268426579
    0x3140103050a230a0c03021011070902180d030c0b0903030c0d020906040806040b011409070504050121060b0c0106090b0901060c0c120f0204051305191403030403020703030207080c 79
    0x10070000003d00c0058803085000c046002280180300a020f8490400311101e80654181d040c00b102441540343c1819850101012420320f46019500200c009840700c029101340542c4c1c1c0d42c0407a0b910040304800f030b10610b2840000b80b0910500c850341c600036008000449007510b141401400113101d1a0000085038003850300307810b0b491306051205008001951080d81e10035003101c81400009030340c2034108100c3c0d014500c10342030140e1660501d001d44106406001c85948110145828851070311703044070498040d00d20a20301109500500314029050130014485409000d250503000104951780301c01410310702c44600000c2c0005980c0d20200030549950320304d02a07100d007095004110450244800c62400e40c07080f6503003070071141e584003110401c0c02d00e40c00c01c0e201c0381c404a8080b01103142c00c5c42011351201c400400070400300c00742d071215580c0f04801c01c49a0b5142c401d0910180c2807250740b0f880c1c2c0c92410401d41c12070b45e40c1d10f000c0c0780c000c0d140c803010311046004d40306520003c2200e0300d01050114000c5009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 268429073 1250 268427823 268427833
    0x22506020706090f0303050609150f03070807060305070810030309030b0c0909040602041505211b04140109060f120f02040f1205240c030406020d0c02011b03091a06031203160314010305 81
    0xf1010002c2f0350254103140c0d0740c1031180300d0380020545400d026030340c000e02203a01d002803540b82c0110058005507005010702003145803103e050000a40041860042e01c0c1c1160300b83c1243d0f50f54130580349241c07140c1d2455a91049000381000f0400150760014000e0b1812544c3e1070884029064040d2000d0082d01603400118520f490b820b285004480070f0140c1c03005040420506a185144200045038172a07000f0102ca002010291303180c550b082205240100010b29001c008100707450002087e0100301110b034129151108080034854483d030301a58003801c00720002050f0240d81e25008840c1c01080041110540100c0e4109a03280c001e0f145007052607107003102c0b041c3c1103035242c22281c80d02c2c2d440140300300c2c0d080e507017070003060a581c88901c9203528130102900000313082015200e412002c10444001c500815041585120000d4040381c00d030000c4d90f491425046c402e4480c640041d0170b04440c10b40041801c0d1002c020000900407034004032100e240780d91010000742070400f480914000c1e090001030305940c41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 268430323 1250 268429073 268429111
    0x6050607111512040c0f0b040815090708032118030301090903030f110703120b0f0f06040801140a06060c02010c020609010215100315022506020706090f0303050609 72
    0x1164400711400d14000b0b04618092890307907030700c034040001e03901034840d03c0954a0a218680b5105440c00140c0121000d1605003490801182da0303038040d10141c07031018030407003004c204102020484100908100000d0725141e2040b903070703850038000c5a40884d0800304100c0011507001d04c40110f0407403a50300810051841d603030902c807100c0003400540004504259a4029180600e000c80c4141051000c1c0b404407035039070700d00500300280b1031340c6c0500708aa1201d141900550039a81c60724414860a5800c2d40c40e10300000c0e445c0009081401994011800e40d401e0200e00303450b000a000046200b562607000800c01d41d03481b00d07001c55082120040003404100001595005842c1c4031014040e482c0e030510440f02002410407247c0401c401c01e844001b003081b6450028802c01484200c20740740d00c078076001b04505002140c200e410a1101d00c58001c0051103a0801071802e01ca820b8044540d030980110041c0440c440070314041c0b89a082c20340041d00024501000700300ca52825130f00d01809a000c40180fa058905 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 268431573 1250 268430323 268430329
    0x302060315040204030b0405010f0501061b03090305011103010f120503030606070602070c080f0d02150f04050721020f010503070c120201091e17070b150120060a0605060711 76
    0x3001800705070706180d040181089036515030005101a41c402d28013500c1ca0b003403601e009420f5a980c184942c85003401c3c40014000e030b5611491000c8080e04100c43c9442000c00d80c14141c1740400241c1014202c0d500b420003000325000410b0095040303c050f2000c80200958542d00d4906503d0320f182e00400e142c0040010901a1074510090803075280100801481c042056031007204603881540f000b041d030b1f002152503c82c4d041c0300b848100c1081d1044c0c000340c000751240c1d0700c02040c101030003403104407001210400300e4140281049640013a118408410003421982c0480030550082da4000300d00c111103490b4101d06651080c02600d00031701607501c031200b1a469a42c1c81a0190030f1440c070030f00031990303075000d05000300d141300101d08520300340d0b16001341e254400303400d0417403500608050103000c0304420405100080e1144c28500e900003400e10840000c405040c2c01204c0c0000c040c003144002000444180d50400c00208905000d40c00c01441000900d41d22001d126182c040c50720040c080c00f000051034030f40c1742 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 268432823 1250 268431573 268431577
    0xb0a05030106180b070c03030908011107020411070203120415031a01030e030f04060306050f0a03020d111906050a021606140d091e060c05070b0610090e01080c130207020604030206 79
    0x11000160140001c4d2104061841508a450252101841c0710750800606400c96074460103055003078000d01003688410862800c0d845503c00080c0515910110b454a13210003006480c000303603008041e41c81422909031507403400c0e04240a2880049000300031075070268001d101d0003c1005101030404008042d030001940241203000500000d80010882c00c40603022440c0244040c20040d28005541401c0030300388502d04500c040ca075030090b09a50801d00150b9a50f0090408155003c01c0703040c1003034055008600384c0300c00940ea1012100d08807001140300d54000020b0301441c00582d00f101d400d07020320143c0d0030b0090964030031003000c2642e030001c0d2200840e01320014500c0404404000c506d0030030959403204607070462114181100c05030f010b2501000b1107030080710104600d41c9019410040151248500c00f0006000544140710b004849840d490042014800922440c0c0225450f0741c2e483d0f040c15107507801070b00c1091242000c1c6010800301d42446c03080d1401e058001e031029040c2820741c4c0c01d024282d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 268434073 1250 268432823 268432847
    0x50609010209100818031b011503080301052107030f0605060906011b0c0f060e0909010203040209160201140c0406020c030f12091f03201207031e050103050a0c0b0a05030106 76
    0x11038141c5c2441d40c0b07401d40800082428110808814400360920b00f84039085a4103802c080c05054103140c01080031131018020f07241510300864522170029551844103146942c58080c0f0043d034001e8500010034001c80350320303032641c0c50701611041c4a6555154100109000c0460700107001c1690051964524800c81e450602ea00d4400c100c040082c9443e6400441541580da0201c40084d100645020560821100e01034000c0000d100a50460420740d0000386850b030001d0082e50140d140d4141016424403d42001d0b011401c0b800d030103003181c1003050040040f0340c45401180c0140c41100500d02660400060121403854010058000714103400e8164040f5489181c10355841036081c40203614121189840948001e41900c00040300c1410303010b649880002503169140904003403180b2a80d89400ca41901d43c40041483e0001da46003214109540c4c1a441e801040e4240d850900080200000052440300c0d40d8040c004901829545000c1c0445604c941d0300c0c2c88002583c28001040101c3c0a20040001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 268435323 1250 268434073 268434091
    0x10030c03090b090f1e06070507020406090c0c0203070501050901080604022808070311030103150504030203131202130207030512060a091e0501082a040204031e0506090102091008 78
    0x1906181e4030781c2e080501041d00e814070340c0d4125908420030301800300001660201c48104403030800c5005030900e510b0b200300801081c1803080008005045550f0740d800710f006800c80041c10000e618181100a12040300d10758224068410194045165801042542e88400059641c070441d0707075036070042c800a034100d100030321480a010303580c19141480e0410410380030001962000c0051820000003030585904000030703511100c081005001044101c0407192581e0550b032004602a00c41c0d02d009c034650b2003103224501c802d944030b03003000c2606916020900e80260080b10711203007502c4846180c00480c4207919005000ca4001c01c01101403440e4900e540b036000700000c00a040c0b09030341d150088266002560548104500c002004030580c2c13207071290502402c00c00e0000c1810404149070000e842602d00e0b260b6002c9485980100c900d40d03541d4040750080c0d94851040c44004210b10010f400c616040c100c00c940030300038800001c0004805209440603400003c00380d81c3c6852201c0802d60711014041d00b0548 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 268436573 1250 268435323 268435331
    0x1506050301080c211c1b0b01050628120501050301060f0e07050d1a01030509060f0c0d24050319051c03020c06070e0a0504110901080c070f0f021e10030c03 68
    0x10355148244515158088901914401c2d076004120042c04107081e211b4501e0749003140c4519a011607031709050035042d1003041d65140d984d1905600400840c02d5401690700c6604506111480d40c1c07580140381c0c90507135406280500150741c80c1e00405080e1500f500441103c032003600e9003086800d40c01c900c03103508030b14a81001850040b0454400c0c00359510b0320181e04d442120682400d006582c141b0900758031a4141c0081c00d8641028042c0c1805024080e000ca400001c01040b412580035075588690100e100c040c4a8680c0f07240c9034103040080c00c2e52031007180e1003070103400603c04150200708003a221b0f44e5813141c01b070022440c0540c814203030390340518000400c05a0900110800381c84c10444107014003040d0312036002e1045214100140030f0159001a80624100030141d50704480746425039000400c2420900310b6503581c500d442c00c40b0b0084000207030205c031004d2160018401d4001c4180c110340d00a544503136482d814510301c00324040440e03005c40d411040c9140740f802030501c43c1d40001e0b2144017a01c3c0c046 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 268437823 1250 268436573 268436629
    0x6091005041d0f01090504021f09120c0314061506030a0b0d110307060f1707020f0a06050a0606050f09010807030f0c08150a06020d05030901020f040602011506050301080c 75
    0x190b414801501200410740c08002401a41c4000d0302403036004009180041c4110301e000d82c0403d00d03c0e03200441e10b0800e054a04034603040280a02903000103082414040c1c111a006414503070b903084510301c010340c7c80d5011000d200302824000b20714144503101c24400d00f05291494014400d003940021b0a2002041e540d0b5599455691454035480e0611300448050842d2804841090f0421646901c83c2d01401008400c1c0d12202c0d81006241c881803901e074807001483e60f6110b206078200700841218000f10300070204440204a8242d03c0a07000d440082d004102642c6c40e86d0054540f4070488511040307406043c0040c1000d50311803840c03030b581311030149030100750a80c141882c0019a140c8a9400c1d02003a1107008218a890a8442c03a056424040b10382c0342000f4a4040040e4595007062511030420000100040d603201094040354011400c00c485036aa41b541d80760300034000c5c110000c5404a010b000680010034901c101e0030390707042e10311000c00782002c1c01900007000b180c606a0a407802e002c1d000c0d0001d00c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 268439073 1250 268437823 268437839
    0x9030b011215060611010605040b150706090203010e060115051216090b0c03120a06030b0f04111e1f1e03090507030b01061103041d04050a020301092307050609100504 73
    0x1000040207940c0362211714098100056007174901640000d030246280c00b5400361107548880c20390241200b44011913554001508114002d01103441c0d005c3d42641c2807803005603a15400043c100d0480b080940b0b00c8010800f40041180c9603c500b01c450078021a0b070001142d0f070131190110a80c1c40102d1428100c6a540d80c80c2029845034001140424840c0c002180500401080b00c1c0d40a81c40a540c40c01000f907581540c0e1501c000b07a9018000d4003480000c04002020002e42240304842c06c040186852200400d40124a0f403401c10307202d06030300550842c42000c50b41803d80c0c1030a03140d040f498440c0e4055841c401d02040d00440051065000c00d40c5628490011480034032403000654010000b0240f0396040c108040d05820810804d2451a4001c00c420002d01e5000b01603241880c80d4128810000d45030f42c01c0c841c0c90010b00c12006941540303000701001c104003c0300c50550400c03208240380a40e042e1a21000e039141c01c11b130b105050b00321804001c18440d91824035000d030108015814035608060321a03d0b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 268440323 1250 268439073 268439081
    0x6020c06282309031e120c01020711030d17060f060d14010b0a02060103081303150902040c03060503072c2a0a020a02010315080102070302061609030b011215 69
    0x460760100c1e00081e10041228a0014400c00002c1982c5680386090650404265174642980c29820303e1a003400090006001c2880160308080a9030300b8652030701c2c4034102441c000e5000700b20445407040342c406030070308500300416140740403003140d11001000d40303440464400000005010940c00544541000115950340024110391030805000041c61360b00d00c0c000d200c1d240d0041c0c1106240030b1040c0001110345900148250559030b0100d0710700d4403003400f1402564040c0c031035007005001e01506100f402140d41c495100c1540c80f40200c4080c84543d81c104d500360103c0d0590302035103800d500601c6040c003000047d8002c0500000d04100a0300c000c1d02580440b0504d070390252000302c112207502407080b1050101141c075059016128240c180782000b07014002c3e42d83c9a1001009062503180c2c21400040d0704101d64020081130404000d6582d0a55440d00a499190807503115021788010b0684455592044c2800e02c16240d000c3c0395082d05e41d003410f03201c84d12002c10400851b42801c2c0c880c211328001d1030b1801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 268441573 1250 268440323 268440397
    0x906130e030415050f0301090f02070212060925090b0d02040e0d0e01170f060f090901140a0b0d030c0c120c030b090c0901090906020d05130c0803030106020c06 70
    0x8095512141481800d01ca02c0f645481000108902440b1402603c1c5001c5c01300d80c1190440080003a4040c40100036101900482c030f0003079401030b0301c4c04000d4100d40d004286140702e0342c008419107a12428280c0001c22840c02c1000103110348a100c5014001228103500c000300d088030040505e15000e400741d0010341580c501c5e4803800c0c030325046118101d034844d41000080007124401d0814001140011116010341d0070f008042003800c5900d5070219209032145459066808000381c65a0390a24041c001e10f806004c41c0400342040543d0003000524030b050303501c6080c01d00d071002000007149116a4400310b441500c4010181c802041340c58001034000131015000d8521031081000300081481c504000d042004024042c0540d50007000000c03100d50f13614500c044c15607050140014015266061400090082d6034400c1d070054a4081844840f044002d600303142179101d42d102440c84d80c2c0f1244a583c59001c2849042c0160340b01c11088000351510001030020704240b44500d207481c60701c80d0b8150108450740c00c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 268442823 1250 268441573 268441601
    0xb0a030216150b0a0911070b0c07050d02210c0304030b25020706030e030a08010e09010e01020d0b03120a05070605040f0501020a0c0201090503010e0c041d0d0f0e011409090613 77
    0x84020300908024401302c00404c04c0c0801001450540c051702030507807142c5c0030000c00415006000544d0302001030152401142c01c40700303d600a100000c0c0c06940e83c641d006480384c0074107110441010b80c0186004841400e1000c0303003d1410a444c5903500388510101900c00a050390354100c620740007c200c04200210302902d0f038004c10015180c81d034050100c40c1d030461b04104c2c980013001990440ca400915031411500c000c152132003e81e582c414624014a00c0c44180050ba5000003107400240b00c650704907040c080021019560700320b0b880e05180072103101c2e01d107240340444c030284281404150207901c0309910900640c0894405080c9a48481c05c981c00604460301181580d03074101c055580c4140050081c107000e4008028050342189070613035401254100c140301d59141d40b8028001038920418442c0049075008a1b6000c041601c409452000c03865445c40c006841c540d10030803690b20501d008100c0340c204140c0545010040d40501820000003001190080a2446501d0800e90b00d88505800740d1007039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 268444073 1250 268442823 268442831
    0x50c09031209010801060903051c0e0613030b01060809070e0604090204020406080a0b030c061210031e031412060409020d051e010b060724110301180b03070b0a03021615 74
    0x20b001516000b810f8209004001c916901800080c0340040c1c5141c285000c0c00c0c0f480c18840300100c044510705049801c0c83c6e0001400b1074500d6030000412824801d607485120600c08980e00c07071500702d88602003124a280c95030b200b00c4040120880c403440c460341200c400340001c1802a002d401250a80c0e01940c450070010341940c0030400707100310b1803003041036101d400ca01500381e014281c0e00203800c48c0241c800700c03030340f50240c1808903800d034804038042c000440e8003813038082c0d1001c080c144400d07084400341401d4001c114501c90341740c68180340320111032200098040180b0241ca8203014000140080c60089030810402c0c1002c10102d5810040d441c1010754000c00c08003083e074004407150030355500074845806194180404000250510030038481e01e0781044002c1d0001d000c45042c003004e402d00c040089900e0400100114014600040e10844141399000c1031000410100515640340114442e9802e810402d2000101c01b9109400800c1071141607034048191019a450304030b20719140100030914580d803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 268445323 1250 268444073 268444087
    0x10924140d0227010309030f0e010e04050c09150a0816020a0506090d0f09231507030e010e011b02041e0f0606030c08011212090806091e0a15050c090312 67
    0xa880c0f0103400040c800e2a05202288456501400c0c10150900360342c01c3c04091a0703910501c0e4420264002e00c18070082060096080c003480107081c0e940141c61310b6001d00c0c02c50001d882000400401c40319011400e958101459031003c010146001d00c0060420840c041e80d4021030202e0740802c2568010f5000d1401f4003420b0031111805020315002503000401d10000070302c1000780075009119524000075a64000f0814071100b0001035520172040d8034940d010700041940f10034181c3c800d14000f410303182a221105035004107001500c80c00e03001d2040c0100750784071942c0c2c44014202a00400f0b4440030004a0b07414001080e440300060712858200180141d96481c801c00c40140e05000303011b080c500c2c170b044c00d0f540340d41060024420040c01039809880c030503141401d025044c1c42403c03208014281141034070320070700b00600102e450307260044500c0700340f0030b0300004840c0c0b02c0c07004940441d040fa80f0900c043c8000751039502030800b900b80200704032450368051000c0700c7c07292001e0000001c030a850059003551200f03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 268446573 1250 268445323 268445377
    0x12040204091a010f0801060f09110f040305031213110f040e0a030c02030601090e0304030807020d0b0c1c0204060f0c060b060301061205011a09040b19080705010924140d02 75
    0x1794480d41103a13040c120208002070554440d1000d440e07a201002c14424001d903c01c15441c0f0500000780f80e41c001c000b0b0300100340140400940f000c40d42c0d850707032000d00e42c642c1100b801403030845201c040c110390340781c0260140514004800a2007070b0005070008c103410001800c92030400654440550115038078184c11003c514080c4101405400014420812005100340d803070b50768029400b000f4a080e81c00548030040d90b641030001001070358072509080701460099410021500a00804c4071103041c190003500500780c04d402640c050300d403030f6940c00d414203507401811034418040340020340e40217543d41103030042c64803560001c41c003906141e140e202c07820540b8444a4200e8805900110b44420007403130760621542c3c4036040307403840b0000311350103d422420700000603c0c00100040006c1c040122030307400030315010702080e00c40440c0d2098840703600361556942e0103d10500c00c0e580791903900d80c580341140c9000e0701545040b0842c059070b002c0a0f04100014245804030ba01040080c903074000c80b0704d45203841c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 268447823 1250 268446573 268446599
    0x207050108060607170f0f0d0b10020708030a20150906130506010504020703050c0f16050d08030a020f04080a0803010306240905130204090c0603050c0f12040204091a01 74
    0x19081d01c080c1c2c40e044140e102d4400c141205e1308840440a400100420849401c0c1e09540c1d1030614400a2541c030b15040f02c0e0b60000f06000c2c4607407070003002d002d0704001616001141003005c0303807401c6014605d46428000200c40c0c8440304202c6010345411020f00044005c02000110b10080500110310411705140d40360078a801001411511081c031070140082c00644c010500e241112001d071405a03c0d07848034074069907240946401b40030680301e0000c0400c068640010840512002006075001c40382d111001e104499104600251234110204041140a80154020007501201104050400f40c403950301034180000d180050740c1216011005200b4041d8600c184001e4544030a44489004045a00b00c88030310b80c1485407104203650741000441c011100c000d200031056000300204038503500c074900031022048602a810020340f8001c005207003601c0b144216151540d46c2280241032240809100c00c2c5840d00500480c0c000341c452821500181d001c41110f04000382618118143d0760405646c0b221079 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 268449073 1250 268447823 268447831
    0xd0b0c030417030c09100309060e0a120e010503130f020306010b070b0f01030f022e0203040e150d170702060705010f0b2b0212031c0c02150c07110603070207050108 72
    0x884010814001c0e0031005104417038840c1410b03074540040d946606401e400402d100b0a000d0160b50520040440c28070b408151004020301c80c40c0b0005400b025007000b1600c140001ca8424013041081001c601105044003080364501c0c4202003000700031400390b01080c2418001e9114007121240401e0345c204000d1490307102a440030152852607095851510b90883d240112040a4052542032003401c54002c905da1a040c1010640c003e070080c0000c840350002d60303a5000b4410b50341054401c4000c900c584000500040604600401e11104060300303441d640d4082c2010030103541c14103400c01c50f00d40141c690340082c0110034003d00000600480c6186a001034810780d1440381e100301e0030209404016680c1c0c580802c3c9031081c58181e5051128240b010070695480700341446c84d10b2001040c00d0f808000c0f03604182d442080305d03d00c240000d020720202680d41c0c4d03842024610700600b012000407072000f200d42c082d08180740184a010560042080403840b5580305071010300068110341000d004550b004020f50b504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 268450323 1250 268449073 268449113
    0xd0c080f06090c01170601030902040f0501151b02010507080307090e041103060f04080313150207060203010312080c070308250909141302010e03151f08011e0b0d0b0c0304 75
    0x2421074811316100c4117003004000b00d051503501c3c4402410740d00c45910000c07130f529202c002040556111031108c0501d0040c5c1c020180010b120059241c14035030f09690000c4a0f42d81038444034280629075589242c20380005004000300b001042001501e450f6146070580510301401c1c2c40442d1100e0074040c90b00305140201880d000513285000d000010341480126588202c4400c038029072601c1500c0d000b0100892541030392031130390002c1034035028080349900035030480784106503401840400800035141381100300c880b007404200074415500131900444080f540042d041c0c007180d120300e00c075201c0728505c0021200c0c443d00060340c0394801e01044c00c03148140802d07030b0090304c1aa40903142400c41c490003401000c50084c10083d0110740304c210754404008a54030b24150f51103d859910f0004400c5c2030007040c2c0e2201010962907008001820700c07040c0715080a100d20f07004420010001c04040d500500210042140c1092085482070701044900d4401d40c010400040e0032680e90034182020000d10504d2014251 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 268451573 1250 268450323 268450337
    0x11210712020a091509020a0c0b0411040c080f040201030c140307080106091e15050f0403080309011a030604060506150a03020d0515011b03030f0603050a050d0504140d0c080f06090c01 80
    0x4101e01ca204c200104a5000c12005a83c40d1101c680031540b024543c680181459140010711080098881d20b0b0f02c414030042d00d0800c041c2001314000c60341e40c9010344699884c1c61825022802651180e007100381149010300b4881e1444403000e9000f20a40d0007101c002c0001604840180b20a40d03110460000400b01041003001e00324813810020400c2311588510803c80c1d20304180d02403910b0281042d41c07032a030414040340303071926600d0401c0001540100e400c00070315441c100302140054814420807020050146c0200380c940d0b62541c40310300910014000d10703404401c0e24803820600d001c041c0141192203c80e50b000d13032650740c900c7c0f0001c26658003030011064100030307500301d49813a6440103000e03000854020b031007900d00c816811f0a40040c81301c000301c0801310381810004018840c2c0000c50300301c482d10440480c1c0e28400010f03000c1b103940c041e50203840011500d000318030302603240810400020721f000c1c07440207890b19958a0b8241c5081c5085e90f0704215604190108010f61605110b0700c00e0454080c20008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 268452823 1250 268451573 268451591
    0xd020c071a2b1506090b0f0405120a0b0705040518060d030f05070206070b010315050c19051b01050f01060309030f08040f021002011a0d11210712020a09 67
    0xc440c070300071100710a40000c0d1152910545040400320901800c040240030007607803510607074083d0f0110890103680081036000340c0000b040e0b0040002c0315038050310004141d0619042400300004881001121000c500c2400800804145440f500318000c913081c0d100c482c0e40381d14000500001e51100c03282448072904500c20044503840d458064000a80d00d45030910180c15100402e0ba014020300d0310285d00260042940b07000c00c1283c0b603403581038034001c00b00e0540e08030ba10400d06054600c00c6940201400060058902040da0f01c1a04501e13482e003030078903900303181c85043c2102c6000e500882004c800c1e0745850034001030340944404d05000d44458941403003c140390342c8014141142411181d0308124106d4002010320584240707a4504a9005020b00040705048500901800c850210016030500c0402002c00740d01d072000c100240603038071001aa0201044000300400c000c1e40000011041d20402c800c180b4a1703005111500241165901105500c22603005108108130150021940b052502c0c1c440 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 268454073 1250 268452823 268452869
    0x15030105190b0a0804031b0302070314010504050c010509030316050109020406051206010e19090c0e07021501030b04021503090a061a2421061003020a080c0c120d020c07 74
    0xb07a2900040d4140210151160310b412141088020101111040d0a001f0103080550201c0c8100450740212885807090f41d9a0718105d00f01c50742036800410942c040d45a440d00741d4041c4001c0d026280c0c004060700c2c1031010940903802848a060300c115226552003c0000440c0b82034810303840901802d6518281d00c1085c00307a203943d13455060090526900d43c040000b1589210404a00d0b1002e40395181804010890315101000d00f02a01618913101c0c040c41c00142480c0c8000381d1841d44041c040c24089090b4a9500c4845081d10054010b030b82010603550082c661011800083d8000e0800c00c00034003c0d012142001412180301c082d1030100c1c0c0e406062070700e1081c0e407101c0f244038140c8500441d2801c0e10784642d51150052003000c0840c42c00315500d41182140d000d40c514490f20034001a5000704440720481e10480c2284107040100010803046c00c003041201d542c950142040301e0158080712052030601209020319040400c591040c0b0b500040ca50180c03c006000d283c005040301e142105041d00c0060302 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 268455323 1250 268454073 268454077
    0x3030a1205090106030c1e0b0a120b0603070507061d07120302010b15040b030703090b07030c0219080a050a11030304080a0e0a0503071406090a17060906010608010506070303020915030105190b 84
    0x810850468003d10b0004079210350091f200208040c03144540e6452501c80045c2c480d030901c1800c06079852401000301c20504048040b60b125503480d030741d004c0c500040c035030f650380052100402102c0002c0740950b680400b4602001000082d00801c0c1d005014110913140090079100e88040307550040ea41d049003050700100e0281035030182e6850700d050640301e50342e04d5811001008030700e4016000f5075040003800181e603003591002542c0401036080d01c24403400003440b002010480c820042801e1000c003c03003070900d0f1048028004841a51170040440d87e4403010151035500281d405540e40c0000085059100303801281c2141c2c5448240d581524940c6408002a10761410784030b4243c40301030005141c1115650b0600b1620151801070440c8101d076102d40744901200c2d0b0083e00305403d4400c8030040f810841c000120755040350a25610078801c0e03824501486841d4100000840034103400703011121080c0e4680b982126102ea100c034410351070b58940810410124501c1d07108404003000b0042c203004091001003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 268456573 1250 268455323 268455329
    0x170304210c11010c0f15020915030408090409290a060603090c050114040504060e01260a020f0409060f0b0a050109080703110a0510050304050616020d12060503030a1205090106030c 79
    0x3404211042c4c0c40c14440c0001e00412001802c0050562140c600b10901340e01505601105070303440c4103540c1030045e004850348401d030390140203100b051141885900d01600b004000702c1c4906100d12005250500c010114003628480320044c09000080281681d41d620804000f0f02c1c0e90b180600035a422600d03040c035608040c1c0507403810426080180c00c1c0c20590a4200c0b4020304020b03004002c845c2c3d5512080d2140e01c828001c070078425084011155100088004040c0082c8280020f81000540c80e400c004030900722072282074000e611469554040b800c980b0440055000420380410340c05d03007880400c05071425541009060183e0908107020760380c0005018802d07a50300036121120302c26081c0001d000e65a240c1d0109a10402040c8140305091740400510b000714401d0341291525210720070366918640e14010903c00590080b04840e031000d08c180700c0036040144d401ca0002d0315079294800700f821a0300480c158800300380e81c0c07903100c51680024441c4a41c4089080020485d00d400e542d25480d07150740070301c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 268457823 1250 268456573 268456577
    0x3030209011e050a0e040b0a0303020114010509090303151f030c20070501030207110405040c180605060d051321021006141002010209060301060804020f1813170304210c1101 76
    0x21071005698503503501c0029407c4004020110f6543c0c1c91038000c1c06443c0c01450f540c0190b0380400000782e541021808140a00c4265014504680c2c410075030a42480036070140d103505ca40420321b40313258202e00410200d82c56210756404180d120f1400c50103071200d83e00b80c00049003202c159203004044400400c2010645109103030140e503412007420490b6111032000301c038990040c81c103804c0c001009143e11440084603070b8522104282003a440c441c80c1224164880e09400c40c20401511009a1480d48440e5000200321071640641c0320540703800c141440c01c11034600004c55100140748ca4190100920906844802000e03c0503a050210301505a004140154002e004100315200e070399000b074041c0c03401d140001e0b080c02c3c5c9035a900d560080900c14142d030280d000d11a2449500c060742861150803201500c0000072000e00c0d00c610700c0e100d444c80c40d003000545100448507141e04a105601d00158042c03400703400000ea1034000056142c80030000e03841d030b40090201181034000013800b0341b001c400c2d16080034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 268459073 1250 268457823 268457837
    0x708070509100915030501081015030f060f09030f20150403090e07020c010f02030c0a02060306060705030706050603010c21020a090b0a030903110d0914120a03030209011e050a 77
    0x2c100b91820b0f01542c00443d02c03a0002404092107583c59400a4100c904007400c440c1c20030540c05401048988c580309082c07049241034001c2c0041503145050380007032b912503800083d400581000480441d00381c0101180001e04642c6002d001550000d1043d510b00049901c3d40345111518010907660040446490902150034000509040c000d03640709e0000e101a0305440017500e01980700035150700304581002e011400c1c400214500d1803000041c1c03011780b994130005001c9100c8940802c00c494100078900303079220408100c644001442400506010b5115001c0807074203050441c20107007900d05144110081181d81f207024007080c108501009076200031030400680d00c180d590000c44005032250040c584404001600d400c526516031710075021140a40e44152a84040f07040842c0c546441040c03620004981810521400200b40f00c5601443d0b0010994403c2c0040f0399500383c200580300c5000d4020a07800b0030f013151196088404d4400e014041c0c80101540501d000000c3c01c00d002c0c0d0100c0c0d100304500c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 268460323 1250 268459073 268459099
    0x306050a15030b0306070e0a1a0306010e03100204060c02090901050408030c16060c0503040c0b040f06120f06030804030c0f05010f1b050304080d120207020616060f0612030201050708070509 83
    0x1983c0031480c0183e000e0300365001c502e402c81e805000010382e40c4c6168003902c0804c40025403401ca05c080c84103180040516189582c0302c4c00011507164110b84000c1c2d038140600384003001001c245100401c01000c40b514ac584054a80b80100064810b0050980f042a4100810800003c2c81c4900b16030740528070883d415220000e08098007583d00c04208000c0ca00780c6004e0400c000150000e02843c4600d2003038591130649a00c03900030603624040c40c400c1c250182c05a160074450103000d080091814810b08074000740004607084008265015984181c03680c55002030140140400765104401070200c0903501500c4600d09800204035650645100303080002c0b055824451120407002c070326617150482d0841e900c03070303842d0300513280c4500400d024080840c44040d11011019094020f03649840c0c3c00611190400308003101c42142c0a40f1b45204588140da15003a060562aa520484026100105410040030402d24010f801c403500500101c0501a0040800201d181d026040340c1c800d00c01520b00c1114154 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 268461573 1250 268460323 268460327
    0x1506080d14130b1c060306023006060c0a0503040e0402010f0302181c0c0b18010201050c0d020f160804171506040b0a090f0b0f10051215040f050f070306050a15 70
    0x30104401c03d500a003400170000902c0304c950080c00c00c1804400c119442000f0050505401840b001086041c01714510005201403801c0005404003031103c0080c0c0304861402e6641c0703421036119810022030b4110000a22095507031141c0c014451099a06003145003a40b000340c01601d80301c0c644180781c07054080b0742c4410b034111564003d00d040b2560004220070141c1d218034821100340c1203200c5210807500d000f1801c070010341c4140112800703070b416030081c44d14140320400e144000e90f220b605010368901c810400e1f440042200b200407140c05000309000341e00c403270130710b1925609009402500c00455000b00700e502201d8080343e042e290880700403540013800b01ca1180114408030301e40d5008458a5242058054006000b6044171000c0030041750810590050f14007004040c00300c0c40f1898000039420320240150700c80040140360000014410b903046440b0321b00003d820f87d000d6a05e06240140c83d242403245000900108540089803420b041c0022400e0a001c528404d032a480b4121005690340303807104103a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 268462823 1250 268461573 268461607
    0xd0201030b03010e010903031815090f0b0709051005090915030723150c100f060b03130b07050901020a0602131e0611160306091506080d14130b 63
    0x44000340c0207000044c0c00b619014002c084100054000c82d04110f418411588600c0783d4420080c0d1203401044141040c982010041011507000c40b44003032100d0740540810ba9400b1501d2048040c5e41e1020b11060400050001c3c0c3c14208a6010900000780f04410381a40e60002c020b910400956900e44084e001e0000680340400680c810310f007942c05040310f813180900d01250342c02210340540705e08955180600340380b482889050001c8013503412808480c0390740c2e800760300701d0803942c0c20020700071038001d1301c48401c102e41c2e07403040c0d40210005031a903030100108450823591a034096603074107040d4200010303900080d441d0705c15110020180e50703000038162a6900b1001c0ea050107840513840003003101410740454179602d0b400c0e00860001c220f1100e911005641c0c0040d600b031a50002418501006246548040140c210383d5404c1368001c1c0c0b403410224044040d031160384014040310008200820a0756005400440345000c00e200c014420841c82d8002c000c100407600c01c481002141c0c075039036050f1140f044034003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 268464073 1250 268462823 268462841
    0xf0405120f0904320a151409090609030301060f020f0102030103081e03010f26150106030b0a03020a0b031f03080403110d050d030b01020a020612041103030a0e0d020103 74
    0x3420101c1c0009941040c44050100300c00c0542d4200500706a403501a0000c0020321060b41e20100b110820740e2500600707a0809800125910011842c40005002c18010140940040c030107030b16910200c0706a80303017088402d40c1007040c1c2d40c06801541080c0c002503489110501500d42442811003a20102c54401c00c1110003c84001000315100d5840703103030241440e4010f8103c43c0280081102c20b919044080040300c7c12a6040c1d120064603d291001c03904207421030f9464002d954010703000c10082d00e401030001548121007404251402d41c148000901100e0710b82c0361090041e030050785d0034001a100c103c0c40c0d20a0302c4da80c0100707540345e640e4140003c041c1d0441d1066480340180f50080041006046409402664880e80706400000b05400500001802da0302010f8410b40c8100102d4510341d0003603005003519403040c81a240103005980206e22035a020b40044900445030130100f200340071601c92404d4241c40205c002d58a00600e00000800200f44103205500c51000c246a040031a80254407d441c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 268465323 1250 268464073 268464103
    0x1002031f0e010305060c12012c040f0b0a090206070204050603120c0708070611032b090809100c0203030d051302040509100b010201060b04030314040305370b0f0405 72
    0x64681e008080000428803085450307100761303001701d40350100d09800d543c00c1a00d40c1e540104a6841d0051484070b000400140760300d4024458503040102e9500208144224020f40410a030440d480c076000c0411680204248111860321100720010307900e034403c42e5039164045902060980390380380064108480031101211500c000074001c01048408184102210011010380d02b8003541c60500380c2e1501a0040e103100310b9002045094002c4035030035002c4144510300f100805c0307000032000c0c91004503051060280e40713003040401e4102580c0b8080415155114a51820200c691030790b0703010940d03070301801d40407028013525500044c1c44d6405940402c07616a0b0001e00500890600c1e440254550700310f030445100050030701c0d0203000594014043d003000c0703c2e0580300c81450242795440c211071668914481c00011101000000045001040000120158000d0942200340c0c03024002c034034030030048619150082c042c960140803034520221158042c400b0088070300701c2e0b6210714106050004810303910300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 268466573 1250 268465323 268465381
    0x80c0c01051f0501021b041515051806091f03020f1209010c020705150a0c080403052a030604030c050c0d060501050a09020c070603020901090b070803061e03100203 72
    0x1d038902d0320405420b03003240b0060380c041980c2c466004a8907813140034500356008003401a041d8450429030f00030340914020301c5001ca901a203c6054010515580540c0c200184011500c0e904008501092a80c1c0000499a903482d100e0302c400414074881c2030040305000c80e681800300d02a014003d404032036005071000300442c0d554071480c45058800c40181c0d02081190720f0701c0940c60b00031b40005826001e03140010840b229010380302c01e41c850507601036042407013000b507844109400160742c2c002030b00c0554800d00c0541708000401d01d8034110101046c3d030300608022004004040d03604d000c510707250006d80603e804603d450751130400c0c80c40c00b811040a2500034511450000a0040980c07107a81038407011500ca00300c00346c2d40c00c0c0c41016405020700b0b08030190031000c2c0400030340713000c1e6005001e880700c181010080c25070b0b5240c40c062180c224030700603541004c00008221503440e00b50106c140005107200e03110b0403c52034402007075448407040b1412600703990000110744000c031503150307028040f0381c0308404107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 268467823 1250 268466573 268466581
    0xe06070e18010f1401080f0609090f030705010e0610120303020d0222051f1707021203090328080f06011107030c080d03060608130f0803130201021605010c03080c0c0105 74
    0x2001851152081100e00d0100c0e2046513029842000340502420028144096913168181002a42c08000c0c000d840340344240e0501c1c02d0030b0704050005d08111070003400005100c0702203444042c10039800601d4180c90240e8400103208554030003062403203c42c0c1518005031183d400c0d042d100003d118024000135a10102d1652100700f44410b01d00345d0980342e003650704001c0d6883ca0a03041c20b50348a03a1468a011500c44031403500d501e01681000b5030300a034184101c0b4003040c1c10550000341e43d401511628010f0b0030000d2940a019035109001c0ca414681003848030354030b040c5280003130480c1805090342d484910b0000100e50f0684c4125840c201500e0f284041ea40070310355900d02040c0c918030306d205010441c007688100c00403050107031003104212406922410f4040e6100000086c2e071031035903003048800c10781517400300c1c0100f001d182c042e510421541003030048440b0f8500002e0300d0304011152503041c0000c1140c0038022640d00500c2144071a5060402400f030703488a12441c2c4050150b0241985590300c0c1c0401c00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 268469073 1250 268467823 268467839
    0x30a05030d0e0c09190e030a0e06030a0204170f06090d200f030a0f08060904081b010f1401030221030d150e07050405011202070b1308190504060f02010e06070e1801 72
    0x22041d041007110100450000c1d822802d0b01e071b00890343d82300041010020311306281d0600b10025a8088500c2c00c00510f0503494810404010410f41c0c82070060381d021420740400320a04001e0150043c0004c802403007282111030004001011102c0041903460410051541c100402c01007620400300c80d0060341e40303030341e066900100525012842c01002580f800041161400d01030b00c800c1c06035400c00100c80c41c14120846808035001400040d80c055035880640913680d000c10b1081e50520036481c40c4142d604e500d10300400c2401c82c140c60108080242002000140031000421038004001036031000c0303040008003c032158841c009622100042c45031314200400694841c0040003079440036203842988000c2780d2140012030040d40f100030001913103a00454403c41885040204542c400c1706841e180039048441d200c55004d40800e002e005c140b0100d401d005490300200800c040030500c2c802001031410604440e9900d0201410f8841030050000e40c1040700d884542031038280412030045102c4650b551145 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 268470323 1250 268469073 268469101
    0x2711270a09061d1c05030423160308091003020306030601140111070b03010e220f060615090e130c12020a0317130f05060a03110903070e04060506030a05030d0e0c09 72
    0x25200013011440500c440940668142c0c0d01450f007210015522019000400325807560034020154140710380150703800f1005208030104003441c40b980c80c0c240c85da44d40200f80105d0310000c07600241031500510401045441c0000c40904440702104401070b01040400181d80c0d0310340e2070707110750090301803401c001c105007004400440c1210f05070601e030071082c0d84506001415981000751170449400c401c1c034031000301d04d503401c031000c0f1240981c400148241c1c0d1480e1400c2c0c441035183c444c80c04140107010412048074001902a802580440c18020341c000035507410342091040e01900030242c680c0700d011030554a5500754080510341c01021507011428000e00080d0301d41020440d80040040500080380c0640918466400c595010341250f00702a208001600a040d192282c0240b00300d080c48290090340d0708003c41c40040c85019240d0740c01d07040c01d0620b28183e40e0001c201c42c0c002d9215030140000035400000729840f114000400085052907103441a0621140192080e403200b100c3d424400040e245102c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 268471573 1250 268470323 268470343
    0x222090203060105030304080a1515060c030e011b03031d03120108070f03080405060702150307030605011710030b13020d0308070f08060307092711270a09061d 70
    0x1089a080c2d1307903101c04060b62880f80d801014001d410503880000014031074203000241040e4082c0c04544401c4404903c0c0300072940394041c8000600d110980c1085c9a00725014a681d15002e103010000444040301c00c05544050306c000030209942d1752412440c1140e034016140c3d580c14070320241c0350745010328501328080078800e005240f01c900803224006070700026000c44008580d13102c0246400c06240404110b01ea0300400b9007079801c5010481d4401d418038100c0f00a6215407019140003e020381000c000401689000034a40b107015119818014950340144201c81140d51180d0b51103226582d0701d003601814000403400130341045409150808154100307546520440d6103a4a20311000c00d13075101205d091109880d080c2d0503401c02d240038080c4203161707008414140d18802c4d60b860444911240c41401104003034091f039403036a8654120200b845e001000a00d604028141c00410391400c14021006a201602000c211642c404140c010814940c00a01219207500600310440384186000c82c0c85000400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 268472823 1250 268471573 268471579
    0x14210904061e06081333050403050a03110903101d0307030c17070201090e0a02070c0909110603010b040b070c031505060301050109060803092e0905040b0a120f02220902 74
    0x68009000b0f0380b041461854455000728080e10004020541004107415071030006e81101d5082018101d2a403843c01118017491081d52a9561292003100040807244882d00c203a4101600b04865035a503030f070024a4000f0154030460020340c0403007590800c40e000d0514446e11515000201c3c00d08203040e04166514860742c010b118205c2422064030740c0303179510302c1102c00003400709403482428854910360340c1c28070341e0118450391300524010344d07a2155071914030135521403040c440d120b1803203d0801100c0d820341445484c09860450555041044800b0103008602506003907000200307040c1e00f0310841d00201d00046030409a1955070425141202c0302410046983c41e02a60902c0b000188054692040404650081000e14249034844041100d00c10b2140c0b42e0000b09880101302080741c4060b1404581c21941c2900c4404c040c40c600b2040c4005e4488580c0351302c2c0f041424900401400034070226040c44d07140c2c090800c00c9116500e100142c2c80a144000c1260285840d21200c40700311402d501c04081d0701d00071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 268474073 1250 268472823 268472837
    0x9020306031209030d0f0e030114090f060106051b12030a050f0c0c030405010c0f0209070206040b010602070b180111101514030c131803050714210904061e06 69
    0x1c15140003403849000b25964243c1c5c403601003046507921900018a151042e480c210030445000c2c0e0009003035507440410100d80b0000701d8144058000c04111a041d407880392800360110358503081c4013405c28003442000725000041d0581c1414040c0d010b004807501048080041a00da041101c0380a000b00001c45040d8800440c0f5000710301510a0072003a9400c5100201c021440c00c3d0409004485160001030f0441d0101541d0020000696560040700c2c45010140e00412143c5041d040184040c030b4181d00200641d0070444c410300080c0207490072034682407148404050045140401240c1c101001e070302e102d845004105d80000030f0446500060100c0605100040c41c01d41c603010040601080620b00345d0381640541c40c5507003603007030030201d00d1540990084000b0349094a9035045247c1520020210f00040b000503032401004000a8030798410900300c1c0c010b02e0a10036007141202211403c1903014040d49022034203100c203994940241c0c024080e00795410550207040300d208a80c100043c0501c902250380 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 268475323 1250 268474073 268474093
    0x25020a091d0c06030a110f03040501022205031c020f1b0f0901050307030b330a06030903080604050c130824070503011401120c08070f050705100b01090f0902030603 72
    0x10018201c204510300522903032441c0c55030300c64540102051590002c07180b86c248149500018640d0255110782d018800140c1d903050405241007044044220180902c03101c800709000ca41c0f40020b42d0301c40c04c45030486003000d401c4a080280c0c5000d0048590301d0b080c0c460b427115180c1101c010000c60500710003e80f0040d40c070100d80781c1003090a120902403c2e405030300103001000416a502c140300d8205400c0703600504c1ca031600c10f810000d1100c40e4602180001c200c00800340b03441c20501c0c00c5c800100514541000480c40f29a0300400a80c4080d00380c5100365202c002150361010307150100e42038809001c0b16403040f00d58620003e51039504040b035902c079003480001c014083c48641c04201c1d104010a98501789035130300b01120104840b9122103d40c0c1041320400c14004502e100344907218200303099440e61012071401180080003540d804145100b0448180814030005100103200c42c65400d450801280740c02c000d030b00403102100303290b02c01504200c5010300050010200e5008501540d025800e0b6405918 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 268476573 1250 268475323 268475381
    0x90411010809010c05030a0506010c02030a060603020a090207050c120705030706180f0b160c0f0b0c0d021c0e030109020d1202010509061014040b041a0405130825020a09 74
    0x2001c0484e82c021a8040000600700105e5500044e0b0080050610444299040e00400c2c600b0140c400216441640d8038028819490103a40540042c0764a5006501d008840d070344898a49644c008030034001d8810305070203105c0f88028448100501000b0b0b086032081070b95a540186807055502c02c500d580403900da1b011800045c808210b005950291440300d241400f60b08500c0a0141d41c21816070340b41c1640f0380042040d8003003140d0750004085505002340c41790580400d00c2d0034a880031043c142594040e06040c3e400c182000d01c4140100c070a41004180f400007400800e01402460500075400140c442d1410108031400221703400000b02540200030310390311080c919a40344026110070540349138403003041107211200100540d881c40042d0004c287c0c40605030120b81564140e00c901d0b0303014002c1d400310094074142445000d074024150b10003071a41042c540ca1b5080b0a21569036805042c1c0c0d202d6244c18122814a41442d13444e40e406000c0300507081d500d0308041e009080c42601ea1610a143c0403207190140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 268477823 1250 268476573 268476581
    0x22b02040608191b0e130903020601091e110a0807030504030c2003101a040b0f0f060712080708090d080a050a0e010f050717090703020d0f0209041101080901 69
    0x4007079031580002e5071a0310490429500400b1041038190703882d5000f0f625040303807220101121280649030b51480310404010090320510321950406210314000e83c0c1c0380401d60004580381141c014580020303055a0000c0b01c4d60b4286c200034141cbc0a030a00300104c0744950b1002c0300040032140100d50302c1c64056100c46804400359103007030360094001910802c4070740114641d42c40c90b80c110b800030f100601c010800100800e040c02e403440c0c10640c01e079503200303541500c68002c04a26807080304c04076020003603004100d0001c0d030b0410f095107960740540107001c0c200b03086031661030446103501c7d00403950440c01c600da07800041c0740c1102110030f07400040210020601d5206c00055050304155240c550800381d6440034940310081500400c8007590549030800300554100070701c41c50a14010b85c400c040760303a1500c25030142c0540840310032144005504010840c451001240c1c09068960403074a501000d4440d007044007081c0c1200c0c901961004941003400104550700f01040349a410a032606484d664600341001d00b25 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 268479073 1250 268477823 268477829
    0x60106081003111009050409050d02100b1c0c1221030b0102031206032503110a050d08070314040e0907050f0307170307080301030317010f0b07081b01022b0204 70
    0x3e400e509012544920381844c5070045608a071800158450340e400010f01500c280941c150360b940c01000002c40c02c40d905100820344000441d00034001c0201d00302c0400c66a041e581c45103208004102e009034200280f09002000405400654400707000746410120640710300d1006481c00c03202070003200550035009002d144100c0134160050b5040c00d604104081c071042c002045690b16010300744014001d0100b0110302040000304580f00d203c51070440c42e081d101c4024880905110b107000d03e10401c40c5036140c1219205040d8001c1440340c031843c083c94260b490030705610300066020340105020a0800d00229503501c2007102400300c58506a0f203c0c00d102c6101c146503009a05904401e8043c00b1000c80d08103506030b00d640311402c0303e2404a03103172521002c5800c00c1c0c10880018402c00f2908038020300e441c05041c00b4280c03204030026803515242450045101f6900000c00710030000c24803004008203603041c03003024900711000f5559141100d6411040c2141c4141c80003d0080c050015100c030b10342c1c0c0c4292019 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 268480323 1250 268479073 268479083
    0x1308010902130515060a0201020703080f06090c0705070e0a0e06060d0809060703020307080a0801080d181701020d140109060611070512030c0a031d09040b07050c0c0d05060106081003 80
    0x5000c1072801c04902030300006007526118101d441c1e0b41d103180d03103c1c5c900400e0a070010354001601c8030034524005210000c0a48a040190b40b100140034540d60741b000c4590304400e0780c01c1c5180c2d03540c415241c03842c200724483d8402c2c0c00c4a400700040002c2c01000d5004084031804031801e0ba10299221820000200803007600580503480500c0f9001d0340d07052000040412500074011a420708003a580c8030600f41d446030081100240c0f0440c0104001d010401c6410070a039454108112507000e10100a000882d143c481c10ba9520481380420010800a60480304980781d0042c0a01004414081d91644031800303204204106103040c0000480a103d8103000c003070741d840040070388002d030302c0c0000f0480440f54880751442680410000a91380020410040da0214405d40b600c0018900c07aa9149245585e640810341c002c11502080000013251910032a034844243e00f011501d858010100c1c13407070b22000600c056088110084800c042c0800080c0b40d50403240740e45c1d0350103400d40c1c901c0e0102444401d03900c0700600e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 268481573 1250 268480323 268480339
    0x3020c0604030e0d061d0105090607050708030703090b160e060a0e0d03020c0d050c01020601050d0b061e13060f0812030411060d0612060f06051011030c010c051308010902 75
    0x192151064080c110f0004002d01244030040d240c641c1212100c81c0e003840c507038001c282001c01030320702800b0356540408243d006d80310314508188007424500c508400104904030000011384e489020358413048440e40c11000c0d1f409180388c46050044624102500d031400704020140755686860a101220300078240740e0f558524001401084c070030041e02e422012401c3d0300444d241000c160b240c04001c220414003c40c0103141c0580214006030810340180c00944c090758148582c107011034481d09800f604460240c030310a50440c1a00c80002c03600b101c0d40744c0a94492008a555001d0217400d41194064440c7e4007003224810765200b0959544039140030300e20340129010300000c2e0120302c0095001a1900000e80354a14000c1070260400c2107948580000071800c02e9002240d050185c54460250400f4011408100d0345090800082502088403003070020420640f9507907030650001d0054481a000c164000c2c80804000030000e8010740241c20410524010303000001a45501409086080741e00540f202d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 268482823 1250 268481573 268481581
    0xa050c041b0804110619030507170c090a0806090c040b09010501020601170715080a0513230307050102030f06090f04030518010512040302010b0f0a0e0105040c1b0b06040c03020c06 79
    0x149103601c0081043ea4600b220130940211516100010460a40034203901c1070842c0300c0035006021904007408200800102d1031402e65000d4003003000c1d03070700401f40c05d0115844d107101d44005041216141c00c01c00d41c6020307070024404200746c0080c0250b6a80f200316020303c4040250824000c01142c01d00c10680107074016401003110b81c8441420304c403c2d82c803440a0300c18458540509050444018003e040085c219808004601d1014492283c0190110f203010400240b03c1d100c40c2c629006000c16001c41d01c0a416140000280403c1200c1c4941e80c040002d40d103d1901ca40102d02480c012070f00980104d00c3c1c0c01c0020f46001000304090320a95054803613606013076004502c0c502c0c2c402d81900e510705004040103003000da114680400e0340304501ca907001160320000310b024010361311200242c060040801c804e040c09103151620310300741511010340f400122039451200850394103140c100d420f081540201b51001c103009584201e10720815064905014200c00510101c0032441400d041900c81e8000c00c001c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 268484073 1250 268482823 268482827
    0xb0d0f18020907020703080c030d0c1b06050705040314010902040e0d05042102030f1c030e030d05060a030b010906080c0901122303040f0927320a050c041b 68
    0x780c000f0402d01c100e56116480e541e40313081c0c07940185000c2080307900c0458680380a128501541c6100c140c5842d20312100960b94402c4119500100001013911351150006a0b049101307209450045402041034080c995001d100030340200300300d81060703000701d0501f16211000000001d900c40c0501047c2d5a40389001d14100260316038000e03030014038100500395030754100980d4081020b030a41203c048040d020031042d42c043d40400c3c8000030600024107040507909401000e020007500c03d50384240714045840e5840d038000813400700c025040280602da0b404004102034030340e5800b18043d42c0148044960301044c1e40104a0102424495030340940e540c0c20401c4001803c1001d0407982250320360700300750448480f09860741160041c0c2c01200e24001c00b02400c010500e0107000b410180c0d0f174000c4a02c0f0390546c0030148100381a030300074005003285100040020703291424620704440100324805107006105120462a2982400a402d4440d0301c82d14041c81040d241501c030321803250500d5540280c40514102e42 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 268485323 1250 268484073 268484089
    0x51903091211090405060a05250e190810050a020702090a0f0e01240509070e0111070302100c02010e120c0409020301020c151b0903030a120b0a0b0d0f1802 68
    0x104403041c502c40c001000e502d84078015401c0c0200e2085024160f58500318100e18210b400080c40b207981040038111205088484c0148a043e4070004e16018030580c1c8950040303001c0c441c40328940c540807107080c2d90000e5061000320710010400b8044c0400c1c40030341c0300c5a4500060f8029011f000c0d44c04800d9102045442d04203a00200b40000d0703401d00800c0c400e03260b2203a6803c5410903a401740c400b41c09020300f03598140d000e18801000c0c12040b11540303e1800c04200003820703218040303222410b00c003c04070b0b12400003c040100000030f6900904810720242e10312001020b20360325220490104921030307000c521b01d1a00411f0318201d86480c00080070241458810880035100754003050760595402c1004141d41c840500c2102c850211004500515060030b4840586a100040e81070007034603814400800d50b980d02004840040c1100e00e0911425004100508000c2005404841d40700e4085031002800b1a81500a0040569546010003502e182c84c4043c0080d10300383e001201070340440c170ba02c150040c80c0000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 268486573 1250 268485323 268485359
    0xe0411040230060307051806040b060408010903030b01080117060c0a110a060905060606070f0b041502030f0124052a06090c0a0603140703110d021605190309 69
    0x40000c8140b0340c810080110080400310304101c8204100301040c00c0802c0311300d0082800303a030040b5451084a0051806080160200744100c0c3ca5007070b100103a90721700054030003502f0900001c005240c0145000350040201922450114200500006411400300004850001e4000142c2021342c1c4902196009a11140a070000c2c403400c03103101044a0001c00600741868400c500c000b90b225000e0605500c1d0080041070503114560810078000050201c101803211a5400192060703030703855074a42080d91200c4112080e240c0f51000c0f0801204d07801240a0504070381e800c0e402c50103208140c145034605c945404c4d4595000c144100040c40e15018810038605144244846020701c2400400700e413400c00ca400d90f1364805a50019001041038509426980c000340121700302000781c1c0c0300540300d4180c1404010018010700d641c54001200140c1c440046880d64640708400b1907131103017480a00750141c3c150001c1a0f0709441072084081e00c031403040056161b0981c0589507001c105c0c0c81d2403030301c1e034a501c036000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 268487823 1250 268486573 268486597
    0xa060804051e010f0204060503010f09061212120c0c0b010603050108030a080c1308070320101116151707020601120f06020d05041110140a021e0102070c0e04110402 72
    0x4d8260615510034409800601803950f43c69a07a0751400800030300c40641c5070810003e251400500f00f0034024a001c4080300954408022181450000300a40b502000c68049041d1107003003540150b9000d522a00c01d8041ca03100d001100702c1a62140d0044003181c10034040c044c9194010000c60404a020300b90b0154400003c032440c0d490055100804c880d14510f03a480b40c88a503200090910030442203141c0c194440303800407140f50146100c040014144941e00280300c051003440c080b90141c00c2000e000342a10340424109210407142d86221040300c921084080c200000c0040d0031211042c0e189200c0355000341c200d039000b07041c540d003020400310040c9400001180d0032a201035182d13000840342c2c0042e003a8013146010000f0149070904114240183d41002c0c24801c42c01e003842c4114a541020807181c0d03041c00708985944135180c05a080c0d140046401d01103080c419280070718a0300318015002009824425106528941d03960460400480e40540b4001c005d41c1c000d500c500d00504169000d0b040f19600c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 268489073 1250 268487823 268487831
    0x206010512030d0f1b0c021e011107060801061812020f0d0c061e0c02031f09020d081b0703150504170c0f070614070f06060810020301050a060804051e01 67
    0x41c25500c0132500c03c000044400c5456810156004090600a242d00c0c1c0b80da0501b0f0500c3e080c260300050360019021201c00d641301c0b101d0300c018243d134420100c100c80150080c0444100c1c071340b19503026001170400d01c6201c0c0040c1049c0300040d0b009451912440c02c0307031002440503051522a500704407035412400045a004022103d07401c0100301c43c403c040c80101466156082c07040c0604442800d11910305085030140005038040718010303100024004804900c4160f1030310308003240031024004c0d003140c02000c3c1d4030140072081c040a00c10060001e10354007404030b485080c4500c0f40b0411544405c1e1620001d404800c880110280c172140c241c100b030354041d00c9010000300b01800141301401d19001040403030b002d076020b810509207205040000c100505018207100031703079110b41540102c0c00d100380314005011a030002d1030b100811280342c100d01d0140032010195104860340c207002400075002489140d1140390303503410004a11340101c1c03d080c0920f400c032000d00904229120803350600030001604455903071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 268490323 1250 268489073 268489087
    0x8070b09010201181a0f0f0a0f020c030d0f0b09040803040303020a0207030f05030d060f080304030602071e0b0a050a0203040201120917160507092f07080d050402010807030b01020601051203 83
    0x30b040444010103100d54141c3c07284040380c000c179103c2000014010450080901c040c841e00c2e61aa54080d6480401034a01080444c00c1e207148501034040c01c0c0b48002103100c042000380790100d16410440c1c08448401c01040040007840402201100a46000e09461340400c0801c005c00d10079001407041103054012140e901342d070780d41c43c0040d41e03554040c1078640780c0022610601e5180c082c001d250007403000940d0860038500301344006171a881544030040c1600e41c005001000c00c4450080c43c40d2000f642203e440d0000c00a050a0b2100101260300152452400c400224940140d200342c0f40620303010b80d0f0740040c504803c0c420100602524005a44203200c0b0400ca0940340c40d0300c0e0040c4032803000c120f60005002900e1030440d1901d21070340c006240e42400c04600e00484100d000a0788045400c100507a202c01e80700e001c2c040d071540706024014140c420001410301840c031054200030f006c0e0b8400c0e030340c2d0902c42d520910210222804030401600503007142004104070f241c8440d030300780703c210214192454080e0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 268491573 1250 268490323 268490351
    0x503190e0303040804050915011e0c0b180f16090506060702090408180906060712050c0708010c090501051608090102010b090f070201110a050403080f0d14160908070b09010201 77
    0x208441c221030104c40010184203505000c03c596801180c246414500d07201c1070b00000e0a400c101c000b1241096482500c0101c1141c4584c408101154000c50250b0242c144410b40c206a9280c4229200d407a214200c41c14150740c000003494a241c4000d03602e800081400d11008030f025100c05081282c7c050003c1c4120000350303591603085401030780300d00072055440718511b0405425100c0d1045891107031410341c2c204021030f00d40c0022610305a0f4805c1404c014101c10000985850142402c46400c0d84154400400d030014154020a600c418076140c841c02c0f01d54031801110144940310041544a040c3c1400354006441030010701a2580140000300d001550040890304c0542d085400e440b403503409406101c2c5150b0207100d900d01c1003c207030074054034080007041d0281c00c1e485280701c005d100070400035481200319807034000c1d540c804203205c0080c0901c0c0c070324600c450300c40f15060740e1010100410b6000c05070054080c2d2910400c48031b00c0c10107803014a181100e030b6895600074104903410741d500c40407400c4c3c00d82 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 268492823 1250 268491573 268491577
    0x914031c110d020c0d081302010c02040203091c02030403020315091e0f030706060510050405010f110c09010602030a08090c0d1506050910090c020a0305161502040f08100204060503190e03 82
    0x201c404c001840b03d01e00125000304800d2003c0c200d1a8560208540f500c05070342d00500c1c803840c098050b28056a6611900d5146113040082031416010101a440d11103019a000c802801180d008408a03008850301401c401650781041e14040440d0784910326000d41d2203030f844e084c8181c20b52508180e8030300021036034105003554044002240c0b090b0740c9040030300c050300c1c02001c184842c017241e18010742041e09000020341020311141d80c0d03030180710524400c105045e008010b840c031501800b400c20445541d480c40d000e0354940042001748041f9185400041c0103180006480220b0100108400c010550584642c10780c1501180c1c12a420340e204d0001040076101e046000f4000c0340000c03040c0410034034001540c41220000300703a12003150401c0c103c10003c00c2c1d1041c1919400700b602180d0342020481d40c90440801410100b010240900118000410fa01481c160340d041b114807105031080090402c803c40203d1056006202c0804d0b4240041a04051482082e407110450400000350422210701c5042c038507 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 268494073 1250 268492823 268492837
    0xe070302040302011803030207060c08040819020f0f130e0c0312040303020708060f0a0c030b040e0d0201060e01081b0604030f06020306010e0609102f010914031c110d02 74
    0x2003a0006010421540c2c001103038142d26008002100d491829a0b6000352201e845110300700800c0b031842100c00500c84004129001040300400310f80707445400036494a00080d440c81c4c268441c4400c401c0011450501c4120700c1003900300144141440120b410000000b820540c07401101c80c0300e584100001da8404200194100b403000007860b44913860b51400030b140805e150400003ca4100cbc000740003614010070281134001021640118020b022054201c004102d0500e03c7c80d4054208400740a0f0b9001c040f0300c11041c202c40e136000380011500c403003804161706020301c581042d55018003004440002c541d04035807040c1b02c001700305d28500f990b41d850b14070202c3c0c1d29490503603020750700109211030341da0016100000c208081d00c46c14144051040008e0310004c900c08841c06100302251038645400e410620000910551800240810040d525003802014505c100302d45a030034021400c0c4000c040002a00c2c08400303e80c45821002542d00c000b140070340868502d00302c3e0007105001300620400340380054100303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 268495323 1250 268494073 268494077
    0xc122406080f0a051e030a030c0302070501090c030b15010219060618020307090e070f180b07050c04061d1503030f040605180103110d05040c080706020d0f020d080105010e0a0e07 78
    0x3a07081c2800c04c94100001c81000000e00704021110806261010003954808401307801c0c0041d441d60360050a80c0030344070b0740000420552a0503100006c0200391005c0ca01580d0044000c2620755131400c1c1410300d4108101c1465001d41d20110b4204102040b046110b10007601c10b0740301261441d038865188207113030240101840c00c1703a008030401c40e00d65440703899080240115a4085c12070f081100014000341410001d0f841001070740f1182c01c50080700002e10380b00400da04101136030b0310000d07810590303214603c90004c144143d0924000040c20241a988a119032004040b088140c5c2c6640c95104800c07007810b00d0b80b03a0180020b020301d000360014000904000d00351038464076500d560900e41c400c2a128102d101d64185450484400c881520718010386210f404003020004d900d8030350b4182021402d9080c0d00140d010f100342c200c04510030342c1c08509055500016220140c45000e80700050307858000c00301c1210000b810000040280c3c0d80b0030003180c80d451030007030940901203803901101c0061500403207110740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 268496573 1250 268495323 268495333
    0xc0215090d033209091b03011d090a08253c0b0a02090103020c1c120605030d05180901150e03030c0712020a080a0f0c122406080f 57
    0x502007580310b02d01c3c200030018840d0800e0700912182c401c1080d0183e156402e004890740f40000741e82618140800307030310410902c1c401ea101d60755100b659802515050750391140505070000f00701d91000c0018142603181c4d002d5001c509105810784200601034450030030190614000c40c0b01d20129140c1c40c0c1030541801001c540c1c0340c03070305c150940c10700308215160041c02420f00181041004141891005034010340c038804c0c0560354481d0013004034040d000f040f4070301032180038171040c0c0100c4a5550003034045400f50354483c2c2000e03d1100746402d0407074401d841401d4040d001080c0c1018800c0c4140002d240d8002000071000496502802107111101c0c01d801a00c40c038045a18900c4101d90000b44000000d00b044004625008042030980e8441025206881d00307030910010314000c5640f0072045d580508003010803141100c40506240e180342100150542d41c60003c2c0101040340d0810503608000550404e5150415010310080c05001c40580400184440d03a50030000c61010414414440c000d01d0140c0149 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 268497823 1250 268496573 268496597
    0xc09031b03020901050f030606010f020111041503060501020a0f020105070305120f0907080a05210705061504060b0a17040309080d03021209011b08060a03060e0105070e03030301060c0215090d03 85
    0x81100c0f030680001e4410b0707942d06903148542d900082c00030352004080c80c1c00d5031400000311007039015151120f03000b00310600100c1c01185000103881c1145402c0751a58047c00069503940044e61200840d07d0050405075000b0020005940100000c0c0f035868800d240c40c61800a100e44411580d01c41500d002c004044c881d03050048445081140902501c0c0c0b000c0134080846455480c19507400c240044003000b04007485070003000c80c20711010f0751b0408c2e4118041d02c2092030802c5090403046d50720480e00e8804d03890901c0c0412066458826548181610744a180d40c181c0c118220600711880140120104049582e001c5059982404404242c044ca520007503251131140c6258641c4070f40c000c0c039001aa80c50080c610a6004c081d20000c209560365041000b4143c840c02e0108042c90b0075900054840e5043c01000645080c0540c480342c4900c1d6155646c200e0950060b0406450340b00a1013660002a0114401c402600e0403c81100b10494242c04080c509442e60006c140c020000c1c0c54140d020407850b83d410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 268499073 1250 268497823 268497829
    0x30305220b0301090c2c09090a080c03070c0f1d100801020d06030218161b061506120903050405040e1e030307090b04150509011817070e0f04060c09031b0302 69
    0x1070070020389681080180b107010621076020159465010304c04c0c01500041002850240480c09c0003540040e00c15079507010031481599690b1206d90f0403200c1d1041d40200152826011055005484481c441681c070a10000e50700ac1844030040c042c0444250110380006503000300f44020019030600e10004210180755004000d403405a54040c1c84070403840404100c004070750134040f1040c592580c03c00112214100c16100d0110340c00b0140207040510388440158203041d0550340c5012111240d031007002d68112549054140c484030800100070071024441405a450700e50008020000c132902100c02e81314003170003004803141410101c81500e4200009100700a07a001106c140504881d0200b240b825140ca0f01c18104a5180541842000000300b051040c5a00c22140d075035803440f41c03c41e00010151070300f1070008103080f1a040c08116101d0703400c00042d20342070300c0141031150780c1e500440b007e10394681d10740c90080d150394041742d020000240c1c000710001e030660b004013000003207200c10300c0010344c11b52040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 268500323 1250 268499073 268499087
    0x3050706030f0207170f12090714010e030a0b06030307051c30090303060510020106180606020606240309060118020304050a11150a02010b0316030305220b0301090c 72
    0xd02000b2900400040011403075403805c40001c01c1c0c09042c405c4c0e6842d003071803001c0c10a0046003450681540110244040c1402c0000c85400b590b2010b5423152a111000e00151400d88001c0845a09608079010510205803030280a0707502c0f00380903080c1c9140c071b40560313603450400c515a00c0c0202005519242410010380c8011034114a80e1070b424980b01c0109110314000f00400540c91900f102d40d2945001c07000c05110b87c01ca4402800060504102d1251030782c40a400b821882c020070403806814003090f0a4051107005a50844099801070f055640300d020600c000002d46100036401d800d03034440302c43c038400c02480c029889000081c000e8102541011408020038001e1300a60f036416005005100110340045080c00d440c0c4d600ca8184442c4400da40d000c9003085001000700401031034041108c060483c2c042d006006440000c4041d034410003081d80e581018100140809000200103224040003100d40c82030700c46200340f010440e885003658907219031800798001d802c503182c0117407241c46583d80c80b500145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 268501573 1250 268500323 268500341
    0x3070521150606071b030f0b040302060c031005041a0d12140403151d07080d08091c05030901140c21011a220906080f061504090302160305070603 64
    0xd41c041d1608000000803110700801c00c015003141c5a03a0300b04004417207140e00d040d004581c40640c2c0c0301c008056040c01300b4008000c4400b54098080c500c0000c84020350481160300c204000c40d00c20000030b0816080c0401400300385c40c030400d940d000c804002c80513504c0b0b946c00d210940c454000f103840d010350044000c2840c0c82c50501c907400d410090005100260605400780c0154418050015440035464000c04c8040494105240680100400402c0e12172010400300040b0f00c1946030900941c0b10030056654485202c0c2080002c21808805428050711070b200035500320862100200341c7e6951407000e00280e20b070560b860349401c0c40000300425070428180703901a48607298a80d0244a40c50b110070030078000c1d841104600d94403400a107442c2107501403c8018581051501074502554646203100c0080016000319002032154110260f00700a001800a00c212650800d60300f952130420706020262034400000c60650050707024030908080c2c0c030501b4a000307602400060032840d00e40000502240c0b42131b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 268502823 1250 268501573 268501603
    0xa0f0b10060f050301050904150e0705010905190e04030504150507060507020c03060606130b040e0709050a062f030d0504060c0f09290c03040303080a0204051e03070521 74
    0x3403552642c95080703401c1e01d04666090752140000c0e5601d18024135a0401c08000040c0240b8100c003c12114000140103015601c084e21003824050b203a2003000b080c0240641c56507036124038640c0900c4100306440718150030034400e09201d0f00345600e4554171310038600c0ca901c0c46030006002080800c1401420b009850f084185070002d0500c1143c4100401e86030140180614001c1e01c000503d01c60403012041c82070700411607000b2950b01c850300d44503070980c0c488065640800050f00b02d08086080d24141d1aa04101c0750704c0e4680c071040b00707200722460f1170b404100507485003024450616080c0c6c040e0113000401251205000000d0103182518103982101c8001203110700b00200c41088010b040e401c070307074209c00b80c0d03c2c8020b03003803031300e00040c2980684001380750b641c9280440301140700c2c40c1c0c0080020141054030311a03103034441d00ba0385040100007280554480c40e6884240c40098030791000e01c00103121014200501600d41407034a8001041c41c211400b6181481e0395107200c4003900c066001d1090805680d0fa40c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 268504073 1250 268502823 268502837
    0xf0f040503070b06010e030d0309020306060103050c0a12021603030f0608030a0c14070f030b01030c06030c05040506132102041a010c120c050a03050c0105070c030203040b0901020a0f0b1006 83
    0x5a00d4140c0d072402103520003048000490041901603004003080c25286030018200c450800e6403000050180c007800300124082d220322400703d1055030007070103042d01c43d450a050207810804080c07012114502a00c00c6001140e5082200c056003075031a5000c880c845009403008500396401011100c100c80b01e60380412070303a0704103002101040e9030162034080002d401c02030401c0c2c840c0181c41c02071300b08540c561240c42c031407410550001c100300007041203e0480e4001c40b4074842c2c2036170f07580d4146d06884c8ea60300704400248040206014902e4810040c0000c40380f94040c030f440341916465010445a006103d140b08500d07010400e40451a06024400c0c40400355680716550300004000a03080d0380e1070b4440207181071205d000340008148504070000119801100716814140b007800c02070480d5211142d000e005509000c009043c45024003080100954958021842d007494400c581e4510340003103010381d04600805142c40086801010030807402c038000c82c542c10f00d50a22851107601926554440d10034000701c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 268505323 1250 268504073 268504081
    0x210090501024b0303040f0201080a02040608010b0c2a040e0307020f0402091503150a12020a050103110409060b0405040606080709050913020909060403110313150c050a06050f0f 78
    0x20036010804110000e5a003420042094150242072242c600180c3c032092001008020a018001a2110655000b03807100e40c800e882d0150408268421400ba030008031b1045001041180740301e50013012800c000300166038000c0c40c2c3e51440c1000e2549403076001c040d65007005044110785001e01c507514180c4140801107280900590200d070032003004440d210310940c0c0c08101c1d90300035121090f030300a03184200400160350740341c122001d0319003026100b181405070308010004648040b400349075404c0c4c0380e00200740485035442c010046001e003820182004102c0c1c018480001c8054007800b503400500004405186c541d070401040c00f044644503440b00081042d034605106d04030360044425000d0361f2050b64110312503a0b40c0198010000001780000390007807445c00421009040104056020b18820b55410021001003002c05959010350503170100030251403d010058042a00c0d40d510124000c0e00b406400b407000d64030740a0034000c2d812000e6460a84403000c200070400d1003146141d0241041c8a804c80c6814 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 268506573 1250 268505323 268505383
    0x9060d080c010c0f03021201050907090e0106170a0203040b04060f02090d030503011d061c1b060c0204110f0d090c08030c0d0e04060b0702120705120102041403010207030804031b021009050102 84
    0x1f0706228050095420b84086503500e031060310b445001e800c1200352200c89507034411004004481c0840762000d2014940c002c500e20154500850b0f000715049900c86503242c80c6c3e9119000144112081010810f908020005031621643c034010419030194440541300d43c9014032010f084240100050f418001e0401080810756074600240780c50b8a098100345011a020b20306186104c5440c0304140003101140000074415034009026080030b4400d2398284913030404001d1881c00c0380a45200b15003001d006001c10402101d883c0e000c0d40d0f500d0300408070710001c0780e17172140c0741e0703045504c00d40f070850058102c500c014050740c1d08401010301d40300d015602040f03901d1400d0203c1455029034800284a9862003440c184014403c2019501400d8001d00c42c08048680b40c1c003080c004e5001e482240c0a07810060721107400384c541071003501c1d4a03d402d521078026666560b1f6007100d01003803850030181c0700f520112204001da1501020548281c01d55141c40500030f00f03250019103030000e003012030203410030b5182154084d08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 268507823 1250 268506573 268506607
    0xb1305012307083105010c0f02061506070606080a0209180a15020d0c0e01030c020a0804150504030b0a15080a02130b03031b160f120209060d080c010c0f0302 69
    0x1d850385415442034407101282900358503000010801c940f010203250f610390104c07441084425101c1c20082001407a11102619003441c0284030300090380211001600480096040300103514004119a1403c00380e680d94904039003070740c0c001015940c018900c040440c1015996950402c1240614038502242e02e044681d83d0914080000d0414815074400003403c100b640650b01803086001c002d202040d4240c00c01044980c000d1400c90000e404c0c8005850b00314008036200d0041c40d00608528039060404001014201684001c5c40801c0802c2000102188145145600900c0c0845000c941801e400102d1458216540c0160150ba0003c04035400140c2d0303034580900e00c1c071101641c081044400400004d046014503105504c0100200c0c204040d000c0c80807e808194102d50009030f1a01e0740c03034088000024146018244501d911058014003603e064880581e01120084c80c00301b0b24030556980800b183c00003001600c6aa445858000c80e294220000901c000000d1504500b0003240c00700d014818 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 268509073 1250 268507823 268507831
    0xe06120c0d0f12020f01060603021201050607031806321b0c0d03020a061416081506070b1005030309030307021e06030705190203040e06011b0b13050123 67
    0x41c4603001d6500308100c00128418400c039088848000010f035141c60103515184540a58200ca518040004c00d031107000f4800e5810142d0081b015440580c206014004d0507800040c0c02c0d41400102c1c0b06035000c04020412040c007070081980c51403a042642c0b42105040d15000a00308003810104150600d4019071409a4040503080c42c41c00e1140880c0007500d81c10102c680544503002042c40c6400014141c000642700c1c84541302d01020840d8004441d25105d00020a8400c0404034a02c070815a01c4d0521072188650400c450300c040d12404c00a40000450351f078400d110484540c00351104014220240070101d800400d81500651700d403c40d20000282c4910850200074070a030034492405814005030b0f20b09504203c0090722569403410955000b0740745070401c2035160355007000150780d03889092020090700c08440038683c42c00303100e8640a00544621001168034603095403801c0c06100450041000580200c0d403080754807168000d1750030308030b09540443c01101d020031100201d502542d032442448542c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 268510323 1250 268509073 268509079
    0x6120c051e03060a1a130f060206060909070e15011b2d08070302011d0304180f230a1103090a020411071a0601110109030801090e030f04080105010e06120c 68
    0x1507990383c980010b200d4542c07a0045110b00d5174041407100c0040c0441d0040050032000e001c1c0403485950b07800800e004a8103805040300503040b0b8404511281419101960068070450560707040d00d40714040640b40c01c0e000c65a40e544480a50035041c415600249040500c8003c4825480c004c4000e880340400000d00b0b0f4150b0060706130388909401c91341000c05150013041d80c8102c484c0c0c3d540e400d60400901070403054040c0d8000004808050040741e100104550441d4170a501d8102808002d44440d002001f840203074469850b2036003069821290000021250380b6020b10f03252009090010781ea400b101c420300c078850b0b5040d804105010320b40c1d01c0040c013280344c25030403600410b40b085803003000d89a82c059900018003900701040320b20f072003150f800c9500b84181d8081c0c0e0742c40e0f8800d40e2032034124240c80750798101a01240002006024100c141d0300308984c00242001140e01d4942d82e15200b9403d0b6020345d0000140d079544d88014448140c0880141b038000c6c50885004100220041c040e903120080100e90500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 268511573 1250 268510323 268510327
    0x405090f1f0906060b0c060105062701091d15010f09090b0a030c0803031b09010503060d11060403080306030d03060605030106121119021015050609041506120c051e 72
    0x40306081c2a0007080000360300c10010b00c2210707612400382003190840100304c00c06000e20720021402e41400001e44401070a0041b48075407070400844040400e0300001499030401c000356601040c00d00642902d041558000b4005904515161619140c4070151418035810132046903180c013581c5502065071004e480d900d040c000384600a080c001200c00c842540000c0c030100842c200000c0303645000c00907510440c292061603111b03001d0012400c510f88034140400f0702040040c80414418100640300340705c86841040d180d000c1c03000c9100001e016820903442207070b22000c004104500c07810203100d5200703800c500d800d050003824100a0083c280707000500400c4100f10810040c400b2945480e0055070300b444c007242441d81c1d81c2007400a84001c0e1141810780070054400c0700e201c50807010062080c540b1100e80c140b0410002e60809080100d03a40c441058a54840d80346d08400d50104070310f5035480001c0032103440e142e121864900784103041d680b02c07a4041d400d006050000c1100080f20303011410240101d074000369 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 268512823 1250 268511573 268511623
    0x306090603120406140d111c020310180e010219020f0307051f0207150218010e100c0305090a06020607021e070b0c030d05240f10080606040e0907050405090f 69
    0x1200d400340301c0344040000d0400d07500460482204008180e0300c811540320342c00740c8d024047c109041e44030668a15588604042d01007101034400c85c0410494825542d022600d6140030001d103099070806818040089680b03410030f50740d16010494441c2c00005e0b040998240400e40d2942611003d036081c04001e085202c007c030070032a1603264115220700b42e002806001600d2030100700c00094102c00c4020040401d9032210241640c022160491201d1000b44130451000c10118211a0f02040c0f500031014041c007805950003699a0f941040050143d030341c0104010b18241d00000d01c0c1000c10044810010000b0303da0940c0b801010943d5000e49010b210001c0e070700e10946103450700e1442130481003a000d07440d0070148250381034002000180b10801070b0040030462040c808101c0601040f460140c0c2c03109243e940c171042140141c0c019a03000c01c3c014aa00d00749691101541a88002241c640000b80c000303840c24460b6240c6032240341d800c04c161078010080c00c01d07002c4a0b070303680c2c20719880381c0c058071129034840c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 268514073 1250 268512823 268512857
    0x5121306030618051305100207120e030703060e1002041e12080301030f02180403030507031a010c0b06060405061801031a180406020c030f090406080c010203030a0902040b150306090603120406 84
    0x480172080d40300044034414100760601e0303070094100306022501d00b00c207490350b114500e21882d4100468440103001e05119441e507584c240003005603440c8081d490080803881c620080761440a00028045000e01100203540350f8200658003c180d08039980c0d84681c0130a08022030101000d41c1d0650394822406122904c4500001c1d91304584a45114003640000d800c1108042d1300d0b4228a0240d1803a4070180052079413a02c0072100c10b5084211603000400f490b504401286030440000d8000502503e0989415101c00210b01543d200c2c004e10351000300e102444046c1560305108185248190344d040000c41c4480300002014601030391005a020740048000c034090141c2030341140c02d070342c840d03004403079a030685600701c00b61a03041014140c1c822441c010f0002408840464043c60400c0140d020394515a0385171300d13140c001d008402e020707a001aa10100221a42c980031151131220f080740001da91645000d40c204010b0500c01040c00c3c1c041d4024a0713103146088507210981c0d0a075001400c05000c451507485d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 268515323 1250 268514073 268514101
    0x702010609020705010b1021020d0e0f060411150f03060f04021303140f0c0915150d05060a050307270c090602060714250512130603061805 61
    0x1180715400e10010712101080f00550014202081c02c1d0368461001949901c01d42d81d03419011083d0110000f03016481e856503c2c264020901100c1405002070803071172840d8500e1401507c480030320826030188081c042401340c1e92410038040b500c101c800d4109990038940d17038041401a081400141800803000c11901c0d81e600c17443d40309110340900304544400d401200307a900d010a601c002e48001040c0391840104441c041002008180b0b10801070a4410416044c4010720000400b219a03485011100030b415544003801014000071040c2c0aa849502c1d0500e000b04891000c0c0c06a841210034000802440c0c40200d0260211080300c1108030382080e103500710b4809109409003000d0308628240c0400300a5030440720320300540345194200c0c0d010b80c2e5080c1d03040d911034108071100e4400c00300c10700200c05403148070340c01a0020041c1090401000d12a607440c9490b02818070790304170b04d0308408158001241e40301c6652000411543c5000c0c0003e0345000450b00441200726168020651140000f0750143c00d4848 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 268516573 1250 268515323 268515329
    0x807120e0a06050a0b0910060e01020307020306011202010c06020409200703020601030b13080d02040317040f0b07141f0b041e020c010b09180601090c0e090403030b0303070821070c0b07020106 84
    0x1b02d900d44409820500c1d5510701030a00841c2c03405102d45000d52001042e1000f0b02e40c081c2c02009203900308404a0307140c150110041341049102141c4000255a03400580300400c03061202040110030f2040d5000d0321645213001c0390720040140038040c04030740c0c00200b02e411642c1066804140d6150080c00b00705204c843c000140c0302e201e0004a00e9001090741d4010b20869001d0000250007845407424030071184540d00c219040740b50100c0040c4005444d000080c001988910102d03285540040452400c2c1b00513403400c07141440500510907103400241c0a4090701d482e0490702044640b10244801a5916a6070345d000d040b994003044070f00c12010f0175030041044040c010140306142c0703005018690310340596402c0a0075030082200024045010f130281810703901c01520384500440c1000241f10507220700034015000c00d61940300060503a10203000400506000302c07480b0b5521010303641c81102e100c4880e0190071542c1c1030f0303600700020907501c980100381c2036500002a51003911550412405054250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 268517823 1250 268516573 268516579
    0xe0105071a06031911030705090115030b0102150106020109050601060807120b0f0d0b10090501060c021e1507020931080904050703020d0c0201110d18050a030807120e0a06050a0b 78
    0x103030062080c40170560083e215650110125405503459600348409200c00388a80621300e8084588000b66502903000000f8121041c0f046a07600a000343c2400303c103100a134442d40150f5990452803042c41024003074076003d0155803e002d0360300e06040000600910b600ba0052130229074640400300c241e550941d141c000d4a0000342691480d040e01c0c01c01c05903106050b1030680b5110b02e550000071380110a406014100d6000c2d813620b00d8002507503024820402c2505403000321004010080349025503c0c040600c0000c081c00c084907440381c2e100c0c4144414510090708006181c1c1c4508292610402060f080141c1ca0714034480d01ca100170800d1030091602d01602c14403540c0903091008008140340e0540c0585400560181c00b8828240d880034180c0c221079025404da00d00000801c00010400a035802517000b080788001d115111903140d4407040d0900c540c0150450000b41c5403014011410340c0580316001c0340c0c0d05840100040e000c644410b503503503072040a00400ca5900e40780010045400c40d030101d0700b003250107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 268519073 1250 268517823 268517863
    0xe0c030303010306020316020c03030f0706140403030f0c0207140607140f01020d0f0207170f0c03040803091018030f0c080d021510120f111c030e0105071a0603 70
    0x4d01d800b901035013084500d00e41c4414098401c1c58480d00c0010401c21800000d00a1807400540c0c0449021a6100d4001075544607110000c241c80303100038005d481d00c2580265800108481505041015518030200c01c80455008040a02a4141d02000d58090180c11201a540c409207454a401c000b154508665901d0046910303c1d9090503042d00144010151211304210325001c0001c80412801281c42c00707400c0401d140e00c0c0120300c14a0100800c039110100090900344020410510301c3e580c810b0b0040403242d040420700030b22500f084007101183d050507007082c40341c03c991f684460142e40d80501c0042c0c440001c4210003814800000080070150010038190342c0800b00c4040082d41d2080103140d4010500c1083d40080c840079050f00240301a24109121800030280304d40f207006020088203403c1c1c1d882000c0144010b07070765644501c0003807240300c02c505000e040915810083c016450030310a03031303040c0141005888006217600342094030040000e41400300b40d40b15140400d18101c1c00c400e11034010106 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 268520323 1250 268519073 268519079
    0x2070206120a181101080a0204061b0804050d0f0c05090115030b0105040504060e070906080105030307060902040f020703110c011704080a0c0b0702010603050618070608130c0f1d06060306040e0c03030301 89
    0x490134800e0f1a48070280c0b20203000307440d4440c84000b2071060748214000130b806e404100c0c43c6145c0d4540d40b456514004c503c850f0605032030304005046034448200c103c3c2d0302c410b400c01101c00c02807250b030420010402220040103a600d1710f80c0f0f108040c203a1400302d038201560b44410038080d80c0503031700307842c09400003800803c24103031510f030340f050110801c1ea510404602c00e8107000072400c1c81100b00c10305035080a4050f6041080c60b44d504000b03004141c0c1c041380e016449041c0040c907044144098007400e4080d5952003440c000d07001c80f440c1000072100300e090400c5500d07031091718a414100108d07034006602c518040d6030794031210003c4038080c0c183e1030001c186031109000d110310282e054000300700f924021800d82e04152135903e03142c13902c54000011410241c01c01c81c8204030050207412899031203100c4a226070240c5510b540c8800c080e40441d08040e44118407901d040c000401c088ac81889910b1585120300c046040002c0002e4031808001e207000c0c030454a440c0081c10700b05052000308455840502103d4403561 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 268521573 1250 268520323 268520333
    0x40308030105041a012307050d0302041e0f210b0f0a0c090812070804080105011e08010506150901090e0f0403020c060708030f0c0702060c010f06050402070206120a18 73
    0x100030311580f8419420038600b5022a0680348040c000200140c4031340c4044030005982440d610038584406e00089401c4c0003405c081401404240840c20740342c2d070016070faa81001e4610324011980807400c2121000c0c4241032120195005074101603a0620b040c503890319a2840ea5040a43c0030b050700140302c50061800c1c4111070390050391031801240144800e0211100c051001c5030071101a01c0360540740d038003150803101c144105100070300c2c0d101e0003000c0c1685813589454601d420348130300b03a004c0c0d015101868405036220800b041e40102609483c0024441c5003080360004c0d603901c6003c1c040d40d20f160400609912542c0c080d42103000201b00c007407404085032071f01000c10b48125104550541c05809003c00c01c040c0c518001088078400c641c00315565056440c2c2c0f80003c4d000280c02400b0a008000c100022800359550078050301443d400180003003542c0403d9804501a03a4203a80f00074050b40c011f008000060740c030342c401c0d299440f90841c283c81141c2c0d940030402c40644031010050070711921744003118007881 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 268522823 1250 268521573 268521577
    0xc0f0c030c0723030c04020c0a050a080406140f1e130b030117070812030a0b06121b090109090207051615020c010804030c06050612070906140a05030c011202040b040308 74
    0x6280714100700e140400090400320503d18031804168035401c4214084903d10b4180d000d815030311102c104a0310000c04507030ba068541803203010705403034400e00860b0030001150b01500340341401c0501d041050815190300034140c22405900242e8019000c008000b4141219441c00e5941c0c00c02c1c0c80d03210b0307103a079980d0303002c284070701d500030300405041604c0c80c0e24a0019240001c0c2c00e504940d800b030f00801450040000f8421650005404980c84e02e80310344500a03183c1c0d407030024000e02c0b4000c1407802d40a050100001625040703101d400c0d503084800b40302280e4160380040c907400440b01d100b00c0c0540c1d140b006242c060b080c0b84080d9529040480340c07010200d0307400040d1504c445280303980c3d0200d601e240c0114005440c0e06004850090000d140340d41d0001c002032454100c40d1300b00c0750140c6680ca081d1268080035041c0f48642e000f44150301c1d81d90b802000100d00b034016160b58100c0981d85014030303034200408a80c0310610b9031815410722621030502c01580003907904807401400491010380d21503407645841d565613 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 268524073 1250 268522823 268522829
    0xa090c2d060c0515010f05091302100f030e0a05060a2007080a080f010b1e0c0d08160912030311070503120406050c2a01020c0102030901150b0406080c0f0c030c07 71
    0xd00c02e502e0240140d05413001c07854180c0745d007065100703521403402080104d4144014840050210843d25080c01601d82c0728846500e614580c03248038408141000040c1200e404000c4541194880514800410008942a5080b42d000000811348007100e065100e95203100d06850b042e1441c000a001e0107101414018010f00e5100742c1d03507569262a4141c0c00301e81c0d5402030151409103a000c008120100411000b041c0200410101072030500f4072141078903003000304400d1607401188041c400c000006540c8644400c0505150034203000e840e052100141c80c910355604010309259807644a0b07020400004c0581d03c00582c044112070740d83c0d08010300c0b8207d4442c103a400311002400d0001103030b94100d01005036080c40002c80611000340c0c00700807001c50781c2c0034a0750a040155600304a05003480c4402e0000794800c02c460000441e220760451101c156607511544204010758041c1b1007400841d07408080d440c1c01c004281c0e28a91142422290030007240b040380c8600900d4030000408402014000c0794503012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 268525179 1106 268524073 268524083
    0x606010e0a120f02040609020705280510020703020c1f0f091a090a15020d0e151b01450209040305120a090c2d060c 51
    0x81d02c018007001e031900f02c29941142c0550805014000082038030301400c601e00805515142d440312001201343c5e88075442490781c001031904100c8040c0ca415000f2083c0c5d007494140501c01402540414412000740c001c500c01c1e210140362016030380011008a406012080140c014101c03a0f00c017081116400340420b0000216000c0b040e280c8500c0c1182284d00c00c0303661040e182081102442c081d40c0410318003500140c150020303d50120b10141001514104040003030744c14000510811408141016940d20100c0d0610ba9030f00b040b00e11211000100f00200500c1c440b01c5840c585504443c06013008807169600c440380403c03026511211000e602e010307400d11260640c0d0008074031820544060340083c102150030204132000b190b590343c000c00071900401140346243d60f4204582190b00c2464540e4000090301c1042c0d005a864200c542d1400c1c103406000740e51140e03005040c05107180360a0b24 = true := by decide +kernel

theorem cover : BRFrame.Cov 268345323 268525179 := by
  have h0 := BRFrame.cov_init 268345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 268345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 268345323 ≤ n) (h2 : n < 268525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
