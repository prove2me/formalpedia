-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2336
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:24:22.080722+00:00
-- url     : https://prove2.me/submissions/13bae570-bd89-4d7c-9d85-225ba9410b07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 419964028 ≤ n < 420143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 419965278 1250 419964028 419964043
    0x2307171e06071b060212041211010c0f030906180c0614070b0604050403020c030111040614090d080f0f04030303060e0c090f3006041122020a03060506030406090c09020408 75
    0xf00701090400e010000c100155045486900c100403080c00d0910780341c5004805c0c160418010000a0041c1d0400e0b202c4120500a20310b408100e40c0346c000115003080380c22001882d5404090711000d4443d98402692800c500085511034040d48010804c0c5007801c00180c0741500141c81403e034103500f000498041200c40b4002500628212000700300c46e100c03801d0803031903c21840040c1d03916510700345040540c000c040e4010421035601c1e4031458407d00032488544401d005070b050b0550048041c03150100015080d00c01005840c181100c8030b0300707004205606d51190b401c10703001100805d0781d941050025503400f10f00c055012041c06900c40c54201003502066010103180150784c042d801c500c1c2400003d80484007844a01700c6403142100402e01d203480d24a41c0c45505417416034660b1645600d5030000e040000700d00e8041d40e1191241c000c00312a0b0044040258007041c2410209591000003145641d80d0034001c0d07000381d0080c0300c08a014105400d18842480e0b2076070080f0305091041000f00440b400125110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 419966528 1250 419965278 419965307
    0x1060503160f11060a0e010507050a02062a0d02070b0f01050303160c0b0708120708060604030b040816060506010207060e0d0b060411071406070504032307171e0607 72
    0x310200c0d11032030382c2555502d074807510095090251000300161988540e00032820560058000c3c069a120a4030940701e81c400c80f500d0200680012000138400742404000700c0c184101000d904070310181844030401039801036484502100d03000030340c01d42440382a440c460740052021381258a1940b4050001c0d540c0e101d400301c007408440b10158000c00307001a40c004080181900306020780c0d285841c3c1b401007604e6005204140403440c40101044445100d079152520420000c3c040781c1c90241540c60f607940040c1c1c020001c50320a4800c112b4912038000c8a940007d140707114020200e11400c0c1140064140301064100350100903800f05104078a9442c05800000e46801000c580b0701511001c0c0030601901d0001d075a00525000010b00c00c2c00c101446022005910200040c0c845a886111040320316124034400680303510500301c800018005134400003070f01e0803d8481140c1074642d45540c80d1703490382c4203024461420f400c25075140d4401200855003411000100020b00418901040c01608401442c0c2c0305 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 419967778 1250 419966528 419966537
    0x32706070b0703060506160209101a070c030f0308180a021509010306050301090f030210021806090f0d051c0801150f1413051804050c100309020d1203050106050316 72
    0x40b51140b40640c0c40b0750003400c0003800440e0741e03041508882080000103d4101d0003400b00c0c1001a440c021044c4e0614181d5400300300e451030449410001c90a04e400c81003007035a00e1030310094004005620380c11900740c03030341c4203071078101c03003490b00d950101c000508841000001e500010102c0005a450000381114049030460031070320742c550780d001240203190581055230950b06e007100e40418060003400480060788254200c920195031150114140e0046400311014642198446005031410b44040d05810b9001351440517101000c45c0000d10070b121107003003600c403600310b80d10042c81c0d081b00d410410b58481a9041228503035143c641d502c072261141d6200c031020400400b4454410038072581003071030384110798074100d40c480440426486000240f0b03c00c452096114185c117140170710b1f505034070a00c680e4100c8003400984011200740203040c8100d02142c2c0c10560780701403940042ea07414444c0c2c10307014001c3d094180400c01c542005000c45406801c0300301400002d2080004600c280317540b299440695142 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 419969028 1250 419967778 419967781
    0x11100f08090c0d1a130c03030f170f0103020405010819020415270f11070b070e0a091b1b03140d0515130c0c0b061f02032706070b 57
    0x8026082103200b821182c0c0c40b503624000c0106000301c1e054070f00b010302c015522403003090b1a440c0010070b6009507003400801d103080c088010001b007401850b04506070000341c03d140380c503c04c940900d07040c41c40d000c5540b030001414480041c0151304041c82032a02600c40e1078020010540c1c10958542c0341099890020310072a01c0780b608040c400c2300110584000c01c0b0101080340c0c506540d4500c0c01160f4a12502900c00d0385c41e0041d00441e9140d10b0160000082509c40b0f200e140c81fa0540b50000c205c08000e00e40c4051184010314002076440380c2080e20010240c4200001d504240e010401c03254000400000040182d44080c803d02c0682028070250701c154942094114004030512180b07250044114004045142c1810812140c041b561107280f4944d04580c07121690b95034558408c2101e070400f201e00300080b5411100400240d00341070094011200a0a4040300442035034202d0f00c0102045a410040c1c0011941c1000440d20b540e05000b401c1d0110b0100c0621901c000c0460480e01810201900e1084880c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 419970278 1250 419969028 419969041
    0x5042904051504170313141207150210020c060f0a09021e030f0a05060a0b120f070f080d080a0513140f1002030f06010f141611100f08 59
    0x325001000302608102c4050424503020340c0315001442140e401d031505822000342c0d6030010048840050000c918482c001d42050540e20f040c0d640a401c0c2d50b04000c9104030180303602c40800603540109a0107808400c90320300c0e08402410074429000c1c24804038014410b801100d1004507102d0750180018000303440b550b036201104400380200180c0079400140e8812104d400004801e54260611070a4044400c5500885c04a690740c00c441c00c005061b40d0060030100d010205036030402c03d01408000c00303251942214810060818500c41e03215a081d07031011404000c22920703c02d105006190000c09025108100c000150901e0001800207000703a958000003603030569001080141242c0001e000c400880c8407040c11555270300050800c144034829544640f41500e501c0c021a803166252140e07605054a9010065400c0703800030400400f40011540d410001c40c08010180603403416400c03110307205445505014894041d01c00019001707046400080391540c0c3c205504050007881441d0002003a6944e6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 419971528 1250 419970278 419970359
    0x506030702030d05040605101e0e090a020a09240f0b0706060e10081905070b071a0f04110d02030c1912051006050301090b0f0702010204050d12020106060504 69
    0x500c0310f10b90540c80c141c144020311075a03601543c0f1442206103842292600d6650640c82603010410f4448402441c40c000e21403000a000d800b50440081c3d070441d041e02e1401e60000f4440d0110f5006140ea0703c0d60345c440343c0c0c1d4031592201482000c100d01e80310300040a05000350350804030f2960054500030407000502c2c0701007154640c041c000038a406001c400440c203000f446400f107a0f00900c602101441a240110381c481d146084011100364004001c1c04218604507000c580ca420110341a80e40540e0703449580c0e00407055000e03136031240300103e402406500c2d00c0d1a203003907142c3c000524203025042e0a5640310060320002142c1c04e480034216094040f1218034002ca9034201c081c0c0d001104496500145402000030015180c91104e10546c0300303011007520f40c014103080b120802d44c058991008000440e2a032508151600d8010740203100251800e030700c079404a04e0094410788111107190080725005405e96080c410720025000034030309145031924040386864a007650f0803880c505861255508840121034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 419972778 1250 419971528 419971537
    0x70807020a080406050310060905030304060309080f07032325060b100302180f06090d03020307060c050a02010c030507020606060f1c0933020309010b0a230103020f04050603070203 79
    0x881683c40d03464000041107600700792101c40c0b100b00c0d06034000c0f8800303010f85510310540d00c0c0917006506252904401f28080c20b4424025501100104045040002074000400e41c0b54026100c48070400035038081402d083c080d00344d030360100c80018480b008a040704002401d03c0d095900755822142080d03414440014103c96007c03e0740588044122150039401d60060203400b5820503c0da8050403415040c0000c01c61292890359025108100c21103d03490080e080d10b004038020308c100c909101e0075641d140200d80540c01d240d4003086010071801ca2081d0709004d0301401400900d018850790501810103592000058021032055034081151800061502c00f07680e80000170062000901000c2210340000b4001c000d41a104020007541d80c3c040e41074030a42290703200482103107078000d68000903506030094101500201f05552100800c0d0700603554008001e006d80400900c80700d80e02104051170340c150060990940c14540180001c1e02242402c3c0d01759030881310142c034600e560b580c0b0500105e05620a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 419974028 1250 419972778 419972783
    0x10207060309150e0705030f031e030c0d060b072904030e1201021c0c09080601140f0d0308161b0b04140304030507060806090606180307171506060f03070807020a 71
    0x41c141543c03440c5100044d178001110320a42c151080300c11001000d90322445416009400541e030007540240421a1400440d841650705280a09001c00c031030404040d9081035014010040e0045000003c1c00b02461282c20ba2028070008604001400094149041c0004002909000207400e1542498803940c001c00f0f03408490400031540c8801c81c444000c03001005480b1203a23894600f216031410540154100804c2d58402d4004005580ca00800f00103002044a80182c0051f01000c1c0000b044c1c4840d01c0e451200c0344a81c0703e201091500d10001158100c0e030340d4004080165080303203920f05140315035005c19900c3d008213074000e50359107074101000c05000f6201422b032035100000b4008280980400c0ea2401d41c0c2160340d80d498181c449030100200c2d0501a036082d94811420011002c910b81072046034144500c000c0c0c151444c5c2c580c3c1e001c0a6954603416514005240c0015080c000b401c4514000203070300040485155081c040c08200c800101c1c00010a154244404800420b481034001c02480c0c5030f155 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 419975278 1250 419974028 419974031
    0x5030115140d06090501140406080312100909060b010e0a0627030507060503010e15060d02090d02100306090e010e0a021002150c0a021504170a270f080a0201020706030915 75
    0x2a604d11503031300204001d2003040c05e6400301586021552415000c3c69040725a008021070808005480c912820071000c1c1c2207465500d1101c2c3d00040c070050f10300940e05141d00401002450124a80014280d40d04070104070744a1410b0001c10f200341504030f0ba202e28144a0741031010800070300f00206411484564101031305c0d512a50b40c0004401743c0c0000154181c030449802c060603a220034202e003a886400c2c2d6100b591116003070201c0c500b6205136501a10800d00001d1a06409403001c0e004650003425444a03540003a032156170178044c9804030b005003624981a44002c000c034403040c001c410b4445c1c08008009104440c00090f040145108200b030100f10078a09030041c1c06424155070340300c0c240c1c2c4494142009405455034201c021102900c0d040d1140e074001281144a4101080d240f1069200c0d14800d400d00841c91a4000e000700181640382d0840003000d0703085000c40c10255003078035800fa15407100d49070358004062240140d901007210741c11604c0505000c82c00703900d40c1c50300c0c060007104e000007001c825 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 419976528 1250 419975278 419975291
    0x703110601030b040312020c120918160905010206060d0b06130c080f01060c05060c030a0e0a05011505060a0c0b0c211602071a0c07121a0705030115140d 67
    0x220080085006505c02e8541000042041d4078a805a000303103031141c81a50045100b41845108007001000303002e0000f8a080503265001132280761841003078a0a81c940780701460078411305d640100e4000042c2000740020900d51500000280b840010310707a00030104000e160114030251509168110f40840914052000070900c02c001418020201e03040b50304401003100000f40c05005001c0810b200b90400c02038150387c1c0d584481324500d070b8005003049103c0303965a60502e040704810b00081160038410f038004508180100030110f41400560840c0d4411034017040115a2260003c0b1803000c0507a00002c0c0c240142d4818102c5a054094070010700800e007114440c6501c4079007003040036031040f58030b99240141801c071510200da84400e140203040800c2030140f85400c00c9401c200144ca0a018000304450001d038036000c8401c1440c0485408032607001c07403401b0304101410400009544808070745802825589004c4c1d140c41c01421a26080042c03124010303c1d10710550170700003121004080b40c8000d04c0303103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 419977778 1250 419976528 419976533
    0x501022b09171014191a0d0c0503060a0b091801060e150a0b091e030f0f030c0c0102010c0f030510031709210604120c060606030b041a0114070311060103 67
    0x4842119400c003d505181403007134400004000302140c0103006003100c80c0010752010503101d0041400801c00346901780101401003d0340c3c0c3c2d0f080600c20f5107120f007000c111110b01d01001e26151600c00b030721650280c0d06140d00c1115645a1040446d03000700d0410011441940074240d0900500c590f0700b01d00c03100002c4400b00807015003200c100e00c841c03403025541ca141c004d40d100c011203414001d5514443d0302591030f61080f8449160019242294040181610745200340c046020746015041820704005400109446103001c0d000c0c0903601c80b6082c280024802d02d00342880040261080050390001e144c0e640c800f080440d00499040b1002d0b43e40301ea2100702401e8800000032a90f044510081e20408003034102004040c0100e10040007208104020000c9407250b03602c00c804448004511010407489110301c1020520302d00954000704616200001c012605c0740520060300c0101024540d600c02010081c4d0003030340e000b00501050700f54002c40e592141141d1800315000d08080300090098801c48002105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 419979028 1250 419977778 419977783
    0x100501060c0b0717131b030b01120c0b1b071203020c060c0102130303020c100c0f08030c0d020d0b0405070c0314090d020a0f05092212030e06070f090501022b0917 71
    0x413203010f0340303862265800c0d60580302c018080d6800010102d2329031100401c100300e29041a07149403842825801b92841c1c80d00c24100301ca41180400d048416071040341f1102085007845680082d0255498010b00c401c00c5840c041c0d0b0f50300091a11030b0144100003014100581d0079410340d8078004003140c1092680703a132400c3c0250348030744812801d44141c5618645210060059141e903110541c0300c02c0080c040c413195210740c45207030001045a0883c0340c2c104912003c0e00030710b1000b03100d0041c21480014450004006010441d6001003040c42401001e60341d4a01003030b0822003c1810b01441c00015580c1d070140d0000c14070410240308020f4001000b03150200720b0411003c40c100c1520000e40d504181a0b9420760ba41e607445840c9812052240100c8101002152800305280658060f900300482e0015083c601c030742c41c0540440300c04000607151085c00b2000da51041c0d0800041c0f100340b0003007044403d1580400d40f402c980500b8100c1188181c491221064003442d40680204502c10228a081c200c003484240c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 419980278 1250 419979028 419979061
    0x100c0201030606170414010b090a06030501060504091a040204060b04060305040b060a03080f0f090d11010e0f030705010813020301020a050a180e06060a0909180203100501060c0b0717 80
    0xe0100e8201400460b50300d102d118101880750b056440460b19454a0721540488a0710b888611030554846040c00300315203400251074099010110009407817491400c0c00c0d07007100c1d600d40089110301d0400071940c01041e00d6814070780509844030382111080e111032000500030031040e07109802c0a400401c0010301190141d002a00c034900524090308a03a94402c2000048105404000c240755007d021407503010143c8805416003400041c2024503190882d070000d49100c507035403001c58003060b10b442c6180d400d50380f0240686c1d01d178000350765030810101e00d040040d445104078000c0d40e042240071400554100c8803c004c0813400c0d50051700031540c1c1c1a064400070f28540c8010040e03000f28114640c0141d00c502005480001c84411840314915900c4d604200f2555500440d1000104141d07050301186550440c0701e00c60000c490340005051001081c810705042060080061100070701d00380041003002d420103403c0099039404000d80010741d031103100c1039800303903121051a440d140a20f0100004400c080d000070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 419981528 1250 419980278 419980283
    0x90f021e04050c1b150f0c130b0705010f0c050405040207030e060a05030f0906060303030f093a05040807090b030a0606060819090309090f020f03090a0b0603030f030708040809100c 79
    0xc56043e44d845103055921007015980840c100c036400c00040d4890000080c0d42c1e044011390b40882d181c01c0320400300b000c820003c1c0c0c0000814190004041c010000d09205a240c40d00c80603105200f49441c1110281260003944216401580c000031a0810988141c240d00f01e1280001d0100703850300d400d21001840e68004462840d611743c074000110303512000020300c0b0b500c641d100800440c6165105841503003081005044400700d4030414808000b126a6446054203205805182820b007200c042d00411141017809182818003400300700620034a080898a10b00b0f403048080c000c507444052030040781c0303065080c420190445103070032408600c80303603c02c3c00d40b4002c1d1107085150908a4201400c5c00440b04511401400b040620804004e00c01890f000f0401d640100e2400505110348010580078652083359180403640001104504008002030900d401850640096013400c00010034015503100140000d014000540c000804024041c403c8410802010309086142000e079071000d0054501d44004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 419982778 1250 419981528 419981557
    0x10030c091a1305010504120615120308090610030f2022110a0c1101120e031312021c02040204050a090209030105070516030c0f05060721090f021e04050c 67
    0x119903201781d0980d825180c0c0c0c625400c20304501561100020900c2d0081c40e80918402c1c0000280c5c0145042c0d007800241c0651550b02852500c0c1144908000c002400d00e4101c4000800c02c2c0081184c4290b50a040b07603001c800d000b2000d410540424100c0d0b400d0104079880000c00200c20b0044000c0d070b09108000b480e05d20b081c0081d228131032204059016904130340000403c0c1d00041d034041043c0010141c00908181080250000b0b221f003000300780c0f0b0140c56080c182e42d10005142c0d0b0600807074030610300107081001c1c0b5190a50801d50002e181c0040789800c50180303090b00c2c0c030f0031000d641d5240d04a80003848010f001a040966600090010b03400100340148a135180a0005208501584c22a00382140444000c041d00300680d8041d200b40024440c02c0d19204030b84070015000601c100b18031805480c158469100c807a545010380014030b00d58203040d00c6214202001980082e01e0812820101e5904850f040c540901950780c80307104551011406070300c00e0416040c8800900d4420081c8100d180ca01d60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 419984028 1250 419982778 419982817
    0x40e01180c0f05010203124014120403030f032307080a0b030d0c080c0a0b040c0f030c05060c01020d0926120601080601020a1403040e0f0610030c091a 66
    0x40e138036400b8164a2100078601140083d10141d61b00c0003010145234420303440b940e103100248004a6131101e824544401c420364210000c10f00011a118150301a90280285911758151080c5407541c001c1d440000e041c04041803044c192030740a90070103c01e2821480007540079915102c2080c2c07507007200f03440c0e000220703c048002c03420049240c01100c2007080049c00608005424000072508485001e03402d480d105c01c18020182d00300d07014482001402e020b190f91042500b0030341042c00341c1d145075074000150815a00e900b04001056141d800c4200d030003c540ca02c3c2c4035912600154060700c20340c40b02c1918140fa00000d0350402c0100c0c840c3d0414144d02500d05906217109075400d061340d00c076100071055048800c90004219600c9142030550005061060369464030f0030380c1d107842e00000700390100d0f81c9a4101240501510510a101d07991000c000606601c040c00d288010074810300c0c0c0c2c00d0b40013080503201d1400100e1a802240b102000b0205e541d2281c04103031042a114855070410003068040c0380911a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 419985278 1250 419984028 419984039
    0x50702071518080c100509030118061505011b02091b0d1b02010b13090f020d03050307140403030c02152b0f050610210f0203070f091202040e01180c0f 66
    0x1e5401003440c014005117004c0d515550251001d8004005055240d034032400b8509200800c0b0b0000314950340304440218000c56801c00300c111000254204074100032803005031140c017402e400140900103805a5601500380c807080b81401c0c020104084169a181d000160440301034150343c4105100e94400100c680304e07015510040f400d8074810015075501c0750805600c02204801503120322500d5200701090484141241c1c0403806522280b207094010074804070401200076045821041e9040c1004040740c5890700795500904114907e05000c4e009200b422091080d14290380e08498191506960f444c840105030114440ca40650104040741c05050400051071500c05014560240700010b0101c041c134039810400f221038a0303c01003c441c60b185284c141010440c0316209001640c4600c0c074000d61380303103010361010b89041081d01303400003080f105000c2000204503080e5501e81140d030403140402e0040b14204c81c140500f034004404a100200c000100c3e0801114141d014125100301c5c1c000c0c00165501d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 419986528 1250 419985278 419985283
    0xf030b060324041b05040306060902031b03091f090302190b0705130e010905070320190302271f0e0d33180203030a0305070207151808 59
    0x2e68580003407000412600c20802c001000c2800011405407000a00d00440e0030050440b21540c0c0300381e40400e0001030705000b400500c0c05a81e001d05421300b420340c0f650070191004002d00c1c04060081030450000710100313001070300c140008240140303110501410035920015503401050f00000441c05840b49070030200c58400300380c082003d100c0e00203400c0401665614419034a5034008050b10592444080b80401c07241280d0301c0590103000c45840004251402e040c02604440920f003071080313011100740c8072092946075481102c1480201c2c036410450b403006100142c01034040c0319400318010b41e803c8074500c621080804082515041100e0102514050b02040c5049128140e4100001101c411700840c0714102011811003c0384190071150701100040d1441d207498103502d0b500b401602c041c109012054843d801002c2e05500b51004030401d21303d02d540000d07501c5c440d01002d00141519072000840302c6d0b0003070007600300815010700c124070681035021000b071415114240c00d08219005550214405400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 419987778 1250 419986528 419986531
    0x8070503011104050108100909051f020903060402010e150c1b090106020d200f0c0102010f1a240307050706060e15040e03041a190c0308011404110a0f030b0603 70
    0x1e6120080ca41402d01e0300455148000400400940007620400555629248203211270301d409800503107020089100c160038200da018204583c1d5900610107940160b9021800f0323030304030b42c4c2401c205014180c0302c0c02141103003604062503203031f03000d020600391041c21011507070a07202c1300383c212001282c40301c10040007810380c000c0c0035003401a40148400c3e04a18007401001c111000f44400881c10011000050b510b00303040640b03848101c1d0414520342006580900401c5540100b211003402640501038442d41011910f415241c810322105140d65141c10604540801c1c4540c0c21100303d03036034035240e8400750031a4840798084030880e1820600190340000c0390000760260000c10b040c6d1010031900020800a00f004011600b1180010440042d054664442000c0fa20003441c25003900ca0644005018450004006100c140205400710b54000780d800108141510611880130045141403000325000300020103803070400f900d0000f10294215084120140350720740300e54050050095a0041c000f06000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 419989028 1250 419987778 419987801
    0x604150e0327090a0e0d0203180f0d050106080d1b0305071209080d02070810020f03010b0a090b03010b0417120901052101090213060201020708070326100807050301 72
    0x20a0007000302c2c030307500400700c1092884105400c00914000b04001000d100050304c00c0c420301030382c80c0b030142c201c0ca90501212220a0302c500195050840d024400144103100941881c81008000c400d440166603a8101d0454190040c0c020820b09464800785582c079541000c0903800300d1001003031589040321810400302030303590507910075003001d420340d0301c2c00329000c0c60000c6031003070002c00a00130902c2d00341044440e04080b904d81c002c00701645000446400c00c0c207102010b240050040141c04062085203045034112040406030581c1c50000315012580300307003a234000a0b82007200000020b50510544090003d407545c00060140403501049110b0740e609001402040d940024806410b2030360250010b0500902d040c900c607212411040070701002403600760089100698089178607200d91481240f0032018101c03e000842c5015100d0f1903800050058000050800c805400d0205c0029503a207400c000d04000c1440700712050403c0071203282031550707e0045003403601c10351200040501d414094030f083c205 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 419990278 1250 419989028 419989033
    0x8070b0901091a1b0607030e01060f060c140f100e03070c0306180605010b070615030521121311030307230114070c0302060105010c02100e0406090e0604150e 69
    0x900d040d680c42503680e864440103d440c1c41c14002e0814079070112100240b16082c4034068226031820703401c00b400b00c0b120390884c00941ea1520b2400d10000c42e074890b46a058511a0030010000c1e00107261520028607141c3c0b0000e0540a0f8100d00d2104850000310f400c0700c0c1c50015000d000c0c003211104813641d070b8014110064480074404900f00045803c90b40020f00c4410f041d001a2020700c0c00361100c40035076000780c0c0688201c40d00050f145007401030920031130000448410380301134072030310f107407111030742c89408c4040c60281d018120b409071050300f43c585c103c1e000c0c0740d06103d940400d840d143d4000036210701c50142c00e4420305103003518900180780203c1120040b03039000000f0109100d6008c13000b511590685550300c110b650300c0d2041c0d55112102c030800c610032862641c03000644019803070024101101a4002410700500ca048200107076500c241e05600c00c80c003490318403650210b440006024120b03a510007030b170062030000751920045021a1040c415402403e1841d421800e00500e10220380342070030580f081340c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 419991528 1250 419990278 419990297
    0x1061b05030d110405030d120e030408031210030204090506071106010b1c090b13150b1005221220010903020603070e130f0b030a021c080d0501030c08070b0901 70
    0xc5603d611240300150780d5004a81085d4981011038541901704e2035500105600d00c0c00410307140d03c18021000b40100c814081c6041614011a00f07075030f07014000e011001161040c000071040081d24072100000c0d40c004000380000c40c4a4200251078080503900000000d80107402858140c0c400160381d4125003c00ca440b42c03804601395034440482500301c141a01e8280c8844111002c104006902c901030480c0702000032020300c50349404010010401c81508074181031403e0140b00d0341e5003a800d0003103100d80e400c02d03030354540031403240455903411800e2050b98110440004200f0b4241c02d00d200014030700c10225000c9211031609200303800c0c102d0680e15400036410300c1c014401418110b01031500180941040007111040c1400110102c0b02e9082c0385030580d60355021250340031101c1c059000320349005c0d00981507109090700850311082d4a0761980d003906000c00100010401c01400722007100f003a02804005550312031174910180e09207485400304901c50a030000c180c601c0c640048501d0448142c4454090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 419992778 1250 419991528 419991547
    0x309050c011101090c300302060103060906090b0130020a0b070309090618061401080402063105030f0303010602210c0a150510080307081b0f010501061b0503 69
    0x86140d030752180741080d5212000d15001510170140c0a0161a058440703100384100c06041d02040805c802420800c0c14512040c240880d4000c5110b034150313034004030301003550410be003400c130060315240da0010f02d0366854000024001c090250303101418502c500201c8078808a1500403c2c4a10482501951180c01e40c0303002c00c003042c2040c005040b02c51003800d10010301540c1e1900481100e4050b44a00e803c43c0a40c40507004404440c810070700a02028941c41009002c6180000d20342c1500a2000340607440c00960001c1e008423103c0d80030070600010901350410500b00305589550f400301d1142a00900c122040400c060801000342c90595040e540140195068242041880f4110082e0402c034071710100f00825041d4400e1040c1c0b0b0205003d241201c1801d80c03001c213040b00312800149646582d0740300c0c4030b0070302c00c04a010044030542604001c001342c43d11714800d0b8000030020000320b2180107218160f01c500c040790064101904a9805842d2079130101f940007450ba131000080c5000401070342080244030007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 419994028 1250 419992778 419992787
    0x140c031b010201060e010b0c070b03070806011d1e03061b0316030b12030a020601170d0c0503130314010c030203310206031f050d0c05090a0f02030103110906010309050c01 75
    0x240c1081480003040483d9a40f0350070091001c00e0308001002000042c1101c6418410000b07400180b0032082440e15518141c400241018400345c01d00c1e042101000e00810400c2e134403c0000f4240e0b100a00c410004441078564403602c1e00e190040d64068003e0034001050100500d0b0f59100714004da4100a01d1640c1d94544008484280100d400901d0383d2244900c3d01a01d51001110101312102c0046a483c6a4140064904041680404080102c6a80207c0768180100e000407960820703042c0242e0082c03040c64124214000c40c4238800a000305100000148211072014020a082c03400080007810701c0d03e00100c082e88000c840c0d014514080000b2048180150b000c0fa0007040854034882c2d21000b41c5500141140e40280e41d088180c1e50614550f0851010320142c44006000032a41e1044120203555041007898040c4180341c410b4a5410005226412903000002c0103507002c5411596582c40f0700d0070004c042d0140701480d01920000d4001fa03203550191069014450700440240281040300c0011034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 419995278 1250 419994028 419994073
    0x3030c0309150a0504060e010c05370504030c090204050108041103030c1509010b09060a0b22080706140c060f0c070507090e0c2407020d150603140c03 66
    0x4149100e8210401c1c812078144a04034000e40e61510007091368102414404e0035036096640204035645000c038805104e5030800202d8022040401d02c030136502d100c9401c14024204204000c10210306d00611807440d480d44800184140c1c0c0c46584485100c40e10f501030711049004034001c0da40440d4604000c00e01045418039240b2140d8001400c40b481c0800c80d0b1509403d02090010610b0f44201800c14061102c4003801580304111042d01c11608924003000051460038003403181807114040000c008042000350420a80700103403105844103441c1d034411140b42c2e0342c4041c1c800d8500042d8554440c04401c00d180c011120004d4203180240001d440d440301c0c1c0484618041c0c070f102413400c4104003c000284c001e000120003031841c000001a0b50f4070b0000f919003060f00401c00d8502c105110551501c20907144001c04207a00290200075403103031694030200398103e070301c0308000c0c100340680c880140c80214140c100c60141c034400c0d4801c404440314001910368070160041841c0c0e06401001c9903007107400c202a80300c2e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 419996528 1250 419995278 419995291
    0x1081f120b0c0c10021303050d09080d02010b060702060d1d1b0108010803120730180804030f0309090515030f0d0e040b1f0c1406010509280c020a051e03030c03 70
    0x6d03c10b2a0740f541e81c0d44c5840d00351040f101c0403036081c0c1e104001820044c08041d030200c9003800240f046000510001e0302c5072166040080c810800442d0100c5c4403220395000c901100114003410f6a51044007090b541d480e825002600d10724130246007280b05551090404a0403500c42900441c184000d00180382d8010000615500810a170811854840115540c0d003c61841c5000020907000c0081d001d400140d644a2140c40c0084005c02c80722000140841d04031000ca0340c101d01c0303804111480e4030b41140c0c1501d17507074040300390903092000340214a00302d40c1c015040200201c0c115203c1c03002520881e519819242c0103280801c0c1241650f07542800c0c43d8101d029000401489010b0782d4003c64051000c5040e00c800d0100000d12680300b9108000301c480341001c0b4040e12500800c425032503c00019602d1a00822024604201707500c040c4840003803002d11980380c41903810604c001110201c0c002d644503c000010340d41445412104180354080a040107048504440510b180d0303511712201c0310b0340f80e0019080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 419997778 1250 419996528 419996557
    0x90c0d08071104020a09030303110a05041e050405040624080d1b1403030906100f03020409140106031b05060c070e100305010509030d0b040c08010501081f120b0c0c1002 74
    0x400b1550360710320003021002201d4030740c40109819400c00400b22140c00c41c2c201c8000703d081220000e090b4000341503800315201c0c1c4621401c11442e90700c14416070500ea9000c580c0250a10040c8404c1102c0d5800401c5001210415110502c0c0301c0024411851803a21484100d600150300d13000e1102d03c904481000c3c00c00c5050140c50109150740e480040c82c0c03103403010255680002c018000030410901109801c01844036446500328107045154a0408031888001c1c880ca585195850801c07146800e0b0030700f2100350800803c800f030303543c0c00c04101c8040b50a52250b24180d20680218240c03600178140ca80f10551240103001c61410001c40f245056005004205288843d04000000540c24041c0621413582907019580780c2c2800d66440c42500c5924400300c0c455030034001085045540700380810f044413002d20300085152203041d10560504061640340320a44440d80020800d441d1980040301e6039407103081d51305031a5981c01409203081c010591408101d80000f484041810b1058019000c50090780c000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 419999028 1250 419997778 419997803
    0x207170a210b03150405010c090305280b0f0a0e0d0e0d031404080304080105060f030a02040c03060510030605120601030f0b1906170c032e1103010617090c0d0807 71
    0x3d2a000c0b1074030682c0301c4d030103825080004008003800f800c0a00304240c10807102060561b5140c030344400c50200440d0031250401d10000301101d042c2d10850885810140a8a1900b04911307044202030044524598080c20180030319843ca6001032080c45c022002d90303603441256089410041580e004a00a400f0465003240c88400030100e04000c20050050340000d554031031412001c5801d50b0002005644600801c0003148156103020070041c03505a4111070010b9080f00202d8260001d058541085410440006400890301d405500c40d209441040320080f00e04c01d624104180c1c0c4030000d010080c40e20b402c281c9920001000610280c0e0401c040c1c00f03105484a1241b061319040703071181d60000f01d489001d00d81d8010a0070040c8908000c070728080e0090f1070f00d125000c12124480741c4035041c00711103494a641448140e000c0707600c1034420b800508000740c0d582d6500d00004212440c4082000942580840407602d8074800140030700300428040c095400b0a196603c030030032950446a801d4130038080055 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 420000278 1250 419999028 419999051
    0x402030415051303020c18070e01032429040509040302031c0b21070b0d020d0c02071a03010608160c05250e25090b030106030207170a21 60
    0x190a1040c1c50140d0750f4030b60420f00f0b04009180091040c9001e000e1009003010b00012082220700552100c1c03d81420503581d0f0034100120021701090040c80c81d514203518184a042800901010485403040702e1010451ba00907a00701500f500382ca40000030002c02c1000f0041420641441503006010740180e82c24007016920b0600000c0f03a0399484100940d03121116040e5241c082c42d50050901c1300d21203c54000e803218202c82d42ca07007a600034903400540109004100301003580440d0703551419aa02032280707202c5c04102031342c1d404460040b003a01d8061326404115801d404004d80b4103da010f5518550583c80301d06140c20940f881e05040d80421824240c4080491820081040300100101c3c0d4040c645144c0c10301502d143c810354003c041181130003014001c03404160780303241c0000d001c45042074070702a4a041c001d030307040c0711036501c04009541d0100001404903050342c05440c0060250b10040c180101540c00f1411030700c11400f40c4c4010401088500030000a1070a000d0003403c0019000144c510029 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 420001528 1250 420000278 420000281
    0x180b0a120b060111150f2a03090105090a0305040501050703110a0c05150702181f06090303020106090204061706030f150a0605030d0903062f0702120601140402030415 73
    0x501055070111901c006010440d6030061079040b148103200041c0c1a41c42109408010740c0c107001c1c240003200c03090314010440d6000c07803241030b0364490341c1c040700314058080c1d017114a8510b400031220040e01d035290500081a0000200f10080001e91568441d85007d0414005440d241c000860550802004005203001c2c0e10081001c860418001e10f00c0d16125480c0200f002521061800e180e9001da0086c0412401603c7c3c6160284a03e04003601510440e9190070070740e000c022032499140b00c40703a100b0701300181d129001031031002038034003c0d40280845910384440d4070a80c801c6110305400501c1e03501e002180040c004d41802c0e00020002c0a0f50307410084a1840e40c541110b1003030069000c1c2122040c0300e994001c1c0e2095030002d1905030003902241801c00c074058a400e00c00d1001400e4941c0300c000c961540200e044410640704510010200c4c0440800300c000440e800c0071034100d0240c3c5401191907901074001600c54101c59409041c2c4201d00510380a01002c1d42001e4004c840440d011841e0358105d2010303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 420002778 1250 420001528 420001559
    0xa1b02030304060f020918090a0615061202030f0a0b040f020d020909161b080409180b0916090903090803121e040b0c07030e030706020102040f06030501180b0a 70
    0x15640116100e04060900c071088030720070401592450320422403941d19444d880c520b04079009010380c0c2680b941e500d0004540c140407580a00030301d21381c54180f18070150445001e2640940e80195101c141e410309200f14030080348401c1d60f10401000c003030400507000c3d1116802c4149060009000842d0601d0400c07000d6099802c0f500d290120305030003080703800c1141000c07070306242d001075000c1e8040d81380701c0c05a102421b88c1150080c642486d02803640140140192401110000e2210460030481000c14401ca080c10411004084032140301c1080420341c0c0b2040050007412030070305403c0e2140c91510381400200204042d00c421421f200c00080009086a410b1002e40310400c28000d11407800e140841c1d006005103030300710701c059140707004105102c007040100000c5648034442070102541c401003410180c60b071550710814943e2510550744085030361581900500225680014801051926404183c0a85200b4050104409000c0b80614655000d5802c030780c811220207007200c0941521001720a264004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 420004028 1250 420002778 420002831
    0x1050d09050c01020f0a1205031308270105090f01050901030e10050105010e0d050c090c0702042a1b02040c030e07060302041d060d150b03010c02010504020306010b0406090e0a 77
    0x8442d21001d507010f000008031901403e0145c01001110390b01c0390341e0600180386481c2040408000205401c0e44442041781d40b035003106840d03445405002d00c080c0302d80740d0160500c4100c6090245c00219500900603504200c07002416002021507074070046440703400448610b8101601c172090004080c005101c6c41d80b9842c002071010683d0740c105400500004a005215401040c4901c2407a0200e070b00441d1060540c24200d45800c1603456000703581055008036000603510524010038200c50848803076100020080340300000e40358061b110800c0d1360044886400c12210000ca0b098480145081d604c08486581c1c54100020803d00c074001103442c10f031454221030b012944c0050f0a01039402c08140d029a40308603c0f102c4a401d240030710100d04620000d07400100903076100ea0015151c00c07007a400003030017848003500800c41500c450000901800080ea03084c0d00a0003214008074010b50400c04075000d0300c1164030340a164a00c0d005415122540062446060036680d22021048a9101e15007070010407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 420005278 1250 420004028 420004033
    0x204180f1103032508271302180f1305070f090801050c0415030f021c0b03032107020a05070b070b090106180f1e06030c0812160201050d0905 62
    0x2111498000c100110740c00c0c1d101d119038014060a080c240683d030303014040202c16031101000110300e01c1d005070640504242e002c6d0803040260109401c041d40d0700309558502088810481c401e14001808040f0310400400c42d840710902c0f1801034107800d01c005c0210501f1000b80809002840c0060321204644095414400140c041d0140c042134580c02008003019100310700003008076061914600701144158482c0c2099180351060000400f80250f000318001d40c8024015507999000985015003042d007601c81c01c404901d01b460803040e6080c000240c034403013910180038459903010108290f4082000420301421071240301c0d070800008500340f009000800c0a8840242c480f003e92030240080c290041818080340c1c50158100100c880c6800c8403080c842001800040400902e4000c01c054035540702e188618500c0c8940340cac081407a0a40c0b08000716405001ca80308210746405003c0d0300c1c0c10a0b0440e21086523014002c00c5000440c0990341300b000d51050609900d0100b4045c0b0310f0b020754040500a44268 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 420006528 1250 420005278 420005303
    0x301230d0b07080a0203071706120d0806030d09031211071a13092a120510050a0e36100615020d0c0b09010b0312030610050705030a0c020418 62
    0x20b03030886265034000304d00210550a40c0340802d8020046c2001440503a003400148000c103240c0e84a086c1c4144070a40c881040e100c09216100018001d0305064405031300030b22a07169102005d901c40c0c54690f05895200e00c1d0b40b08010300600d0f00300c680c1c41040c040b2188500644000168490066800e50034601c5010304007510345000c1e0710312103908002e0340d0001c03440b0340c00c01901058480491002c0140c0704c604519001d4503035900300303084644040e43d403111800703a841c0c0018070020000e10409003080700e07401c5511030101d80e250b0001c01d034408000d6510040c5c540030b140b80030610102c40c05244021300940150060301c140b0740340c145454141c180e411005182e0303a03008240a0000313105110b29120945000900c00c409140c1c50052801a5158005d42852045404038400a0083d0820120b20100904880b1228540d5110304076650090302c1562051120701a0700c0126802082030300d43c081d801c80080c44c101212550191200906000220b9219039100c413000202c0721040c4413010700c20302525901440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 420007778 1250 420006528 420006541
    0x1302060f070c09050a0603030e010305180f0a05120c030a0509040912030f0e0f0c0105090301090b010b041409060a030206030a06030204020f04260307020d0512070311011a03030301230d0b 82
    0xb2500045c040c2880b640c28040140082600900c01e80040d01c020b03c0c002038550340c4e556060348a900b000c5000422030242c0c1c07503141468034000170300c20b00700350040c001e850068009510507151449001c10507030344c581041c0700301d0684902500207081010409040410745001996034008021a04035240000c65543c2d40c0702c41c903415131441500901c42e00100141413000700c059100f603035400060071050402c08005034080440d1020741194149503800301c500c8049584843c2c10840b680c01078090031805c02041508210076260410106001c3c90020700814000e5043d0307000c0c0b01c01c59000400042041c2d4841c0300000068940e480240407030501c0c0070036151603a0500c41d00840c485505484003c180d09410b40b82d45030310074040101c03000141d040b91801c607219410f203083c03420007001c058004904d0201141c60301c01d02d90009025680d0105940080204142d212044210f05c1d0303c07218040d80560041c00140000c01c0910700629820300460400c0c940815190002038808c42140341c1202c400b00c1910a0051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 420009028 1250 420007778 420007781
    0x60311010810181b02010b0604170f030d091a10090c0e10030b0103061202060f070c03051209010e03190602030a020405060f091c2103020d05040605010e060d0b1302060f070c09 77
    0x3c604c0c5248024000e000802c00018107501442c0202c002d070050350412060403800411810300c0720240707441600d854140410015005000c0094181c070308070309440d4071414031005100a82d1060754000c081c005640d040c0303120140103040e025040030510106803241400d40c5d0f80c10044a031007451550380481e04880798400101a81c0c0c0e00c0d070100c40707051840c0402100603580c2505585d01254001c004035161100e42c01d20a2010801d80d1020b0502e00840c803070840240e03030850081081640c2a00c0b1098900d0850702456500c1442c48255454140d4030701e0685c1c0001d0783c1d90000c0d900103540040c090304180d00d4000141d910381c000c180000b08014000f4181004e41071076400d64100e00d000742c9201007141401e032120441110300c88071110281101c10101c070306040c0a5070580d0460f40204504100620745490400d000382020b000b0f0340c407403001c1c03900011490710305980705540f200d504c50600c4030680c440401200c02003c03d030070200d0f03001c54240304003040030000c5c40c0a0100e8602480c9007201c803d00c1c0110100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 420010278 1250 420009028 420009071
    0x1b04092d0c020303041202070e012d0303021f060b1605070504090845130b0d0b06030312101403010204030c1224020c060a06031101081018 61
    0xc900c0c5080c025016401c6802005507a44640c018040290940300307134004078284012504036126084c900000440c4164041c00c1204809290407400e449a5000149035811040c02e0303c40140140e10440c04d070303012130003d808207004503100024003150498907103e050340e01d07070072000c07044500c04414044881072260070414800100804d44040003e00c8450301c3c0e400c0188070354407500c0c1c01e01000c051441041c10720100561a001c11800c100500783c84078811380178001041d81c81d10b600c41d6801d00c0c090301c9140e8152260b1007180344000e2400c50105c0ca80c2e680c0d0035084000030b0265a050105110707101016122480700b9116203414a50205007904040241000a400c0d041c00c80c003a0f0700c103010610000d01c024031001c00380e440c0c12040101882e814541104a210f00d0005104422a160580818044643c000e403003849a1002030704c903140c1d1040040c0045400c241300c042d01c00c403144500c1c400b0700d50080030704075048049800d0480005031160450750900b1f00041d00c2d28002950313200700d0110980c21001a8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 420011528 1250 420010278 420010361
    0x120e04051005180403140403031205061504050d11040e011d070807331101060605070c0311060c0304060f0801050d050601150203090301091b0b0a081b0409 68
    0x1e50380301d0501010414802048049100303540009010905040c01480d14200d0540c81c0c01140c0d550b55180c0c5070041081101071403c0143c6410100800c2c0203140c088190006a0b0072045210b08281c50b1008014040d001e00030700340e460381910010894140ca49000b440e207102165400858000c1c25000350286031010300c800b90f02d00c0d411008007400780d00303c042a0442142c0c0790300700f28001c441c120186404040f82002109800306480e5048140f00e40d007020006100340b01201c001c0000541d611000c4da80c2e88281c200041c400c43e4403074028800603c0f074a4140c018200d001d0401c0e4241611074142e1442c680c895086034001c500713059540d00c0c1c0681c0c4103a0142c05000103803004000c01050f9684c5968508041c0101590444030350480f1042c10710800540e03c174014010b009014014483c00c00011000e5841e100301200c1f280600702103545d14100c1c00301c80c00c11810f960380305101d554803a042049914000716516030040b040000058094841c041c21020407454040710303000c0241d00d54107962080c00e540c1d90 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 420012778 1250 420011528 420011551
    0xf030c0608150405060414070c0605010506430609050c010509100804050c0a1e090b010507080706020d110c010c092d1a0c0f07050a061b120e0405 64
    0x80000d02d0720081c0305181c2e1000242c0700410262a618002400b41009003400a00c0404d16010805150707031000d2800d0740c0a0184030704101d103980310b0381444000e00c41c004010148110000305e003420036100031a01c0c003034681c0f180900320348400000c18420454000c000d09440e500d071220441030034407006000848c04031209081061418025202107420710031100f0030101409801c50000301440001d00401c5d0418000400c08444140c0b00c8034400c054070304840654403081c0c101203010402040c1031049107048030050b12101d0400d4555501d603030315607001070300443d221a001e00039401112014000c1071441a000c00215032940b40c035100150031a40140c500e0390400c003481000b0010b203603155407010303140d0900a081256a880b20248a403080d48550300c4016180301200b0341650408400d400b5002001e200016103c01c400441d0002d42c0d10300c0f4900480d580300a02d42d90800c215130003000000c48401c68103030868075a20164581c0564440352010312070102d1218003042d00c00e03190500c40c0ca940301040504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 420014028 1250 420012778 420012781
    0x1207050726012304060b12030d060603060b03060303070b1009090b06040f0504151109190503070605180d030c02150319090b04030c1e05070513020c0a03030f02090405010f030c0608 79
    0x1da1200f800c02500161449a4901107511151209134030090710645080c12641c0e2203040c2c0000600800c2c16200300d0001034a803001c0400c3d26607445044070b004000c020010741c01d00c9180c1d00c4020000c80054822032169904800c0081c0146e03035070048810780c0e4040c00c41c44074580b6004042c130065905103102c02c10010300d0482000001400801c1d6004032601900c0c00043c04a500951904640310381491181d100d6144825802d100081403141c0b400d4460070f81c00d03154459510318060b1031601a002c40d880e02c54074484828450b6003000b160300c41c400750091812042302900c98000c1b1b07040d00000030400070710341c0c000420442003d8040081046201982c801000142450340b079000d0503102c044c1c4010b081000b465000b44c11b110075110a00c0030ba020011051840d00c101d458082d50740c0103e841150300030100c40002500010181c0300fa0b994800054010f070035401442d40c1d044004005001c00aa01554213005c91045600d0b40d01c41e0030b002c0d0140b46000c1815030304500340f02c88005500d078851340c01c00c40c1050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 420015278 1250 420014028 420014081
    0x10b07050703060e010207020919110f0301030f0309030609050c0a12080405040506012a021806030a1104020d0f1e0b0a0e0c0715020306010809010c02120705072601 72
    0x41d10034116a00003100290102403108114007a00c5202000395109403517009110540c0c0c00d8140220356602c40c0942001202c0c68030600454078041c1c1407150071008010302c0100b01061041c0503051885109282903248103449a5802040320502c08043d1116844060400528280920024060300e01c001103850721114a0355070141601c102e000d4207014540b21004511264000c100d080016058510015880311040b545010300c0c00c1c1c0c804003a44189a40001d040301e101981480e68016580500074150310585502d9400381d0182c803101c2d00c1e410680c00c000c075031030103190b80c415112090240c0202284103c6141441c105214554042d503014518010050320f0070b5440301e40c804221001e9140040455807179681d0f030381c00c5000b003050283c158010b03c0c24000a594095000314131410090701d0300e1550b612061203480c00c80f08100306513000750340041d00d51003018003210007030200340f88180c00f224a11511101c1040b240055010001000d002c0d0070480d0035035507000e00400c0800302408001c00000f81004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 420016528 1250 420015278 420015283
    0x2070b0901141f180207021c030e06030c0301030f0512130f0f150809100203070306051201060e011202030102040f26010b010e01050c030d06290301030f1202070806010e0a05010b0705 80
    0x14801c450707452844e0140c00d840d02e03100750190b0b1940c0c0d40082c0072a01d01c56100a09200b50b0007005001c40000711010000b001e941f81c910305680c09030450aa07990704603070030341ea117012800e004010b0a582d18421486d03000c0040c0841e40050000904d040c131245041441c001b04202c80980b0b54100241c4440703a4001803212070300b0000c0403c115610f41c03401e1011515258040c904007240100308480890001040203003054160300640c08491090310301003000c48104041302d00726809402a21344030440000108081c441e00f90007070140c54002800103181a5a0704e20258601e10280e02c1140c0000b0b040100050300c0301c45140080207542c1c0710380240410701e02d060000f0503c200c45214181400030100304034044071410820b8440c100c0713180c0b0080185603118505900c0d5061014003d001c40b000f50441c00620f5208081524100ea1307100150403624041a503072070207041c82030103010b4114840c00c2c0000070750780c1c03081040794000d103200c0c030207110306e4142001d95605445058009140c211401c114010029000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 420017778 1250 420016528 420016591
    0x905150a031d100501051f08010b210a0c02061602070b1c0e160609030309050603060f0a12020f09150103110d0929071b020402070b090114 61
    0x840c41d00065000181580e503040c401c041601c22502e200d21000701c00914a1a40814143c9001701c0342c14144a010b20303403554803041000d092000181c07100004101906002016100e241031140c07450300502e00118485840303030404c03030304940901c0e00d405640b00d0850b0103101c3e0681090240109840400c8142006580c6004511030034086007000582074071084024140d03820500c1e25020140295801280c03100e40d1121020410400e0003800325000906d01d0103443c25104603985525507901c060318100402038a1b400c0208802d41000300420b1100242c2d031000702503006884071080503483c00681d1f006005100e2035039281240079080807018400407102040816403400800d10300898203400750b10100071540106c000e000480d500b842d19410401814030708152800c119107002d00e00c0481400e940c4008944141e5948012650170125041d0b040003042d0b417540b8a60000c0d101514002956031282c28240c0101c0340500d00e80d54031102588240c2c60451615000400040002e00d68010312010248500701c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 420019028 1250 420017778 420017797
    0x43813060507060f02031303080c1804110f03010b0a080130230d17070e0d1a2502070509071d0a030b09060a060b0405121603060b01090515 61
    0x80381d40e0703040088581240560764507400d07085d0345900344110510304514202100b1008964050001203066071150159050303c45800920081c866034071040c00001c1501c5e401c4c03d40c1c104c0e41009020b85038504040154002c043c202a0340340d80329241e2070010206003041e00940622884807035081481c4c07105140941d42d60740320f00d2200d81e0340f544030318043c002404c10682443d51040c1c408d00c0340143c640040340301003107200d254a40d001440003000c8444d4003258202e40950128002c440158201d0070001ca0704500940b0861002031140743c40104400039150880d950130941d03056010041074a000e024010501d403480740003d015407402c150006803607400007043c10080100c2181c0c1e1108909204800420881010b841e03018141e850b03080c580b04140702110303554414420300020174118081d070b06c240811130b500d104101e418a81000c3c20010302c4041308126451900c601400160320510141084008501c55400013425540041c0050400c07003880d448184074014401c41c2c90588030711001240d41703054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 420020278 1250 420019028 420019037
    0x80d02030405101b060f0f0b091b0a090f08031b010c020d111002030f101710110910020f1b130b030102120403022b020a0b0c04381306 59
    0x44c0e1001225040015044003070040e505200c00c1105952035540071040750b040000f410700c00c0b140114144110319030700780d809101007008010500c440a06010191080754060b2402240596941c100007880b01001c0d000104a9000000c5105100b209800d001c24400c92040003808540d035080700c0a5201c07055519036806001c0301203502803a440d010310140740c607001448021902c03810a050817500c007040c1102c170030301d81203802c82c000b01e122903200d100c080d00216004010070881d91500409400b400801da245207040c80c051102704140d6841048940280f40c00d40d0080403061390b01c90a19107000c0307030342d4062888000b600890190a466a13000b500304001e004201250007030ad402c000c64020b2040d0400d0800401c51802444205640070800c008070781c00400d1a04288480005400c001e10100000345000da4040014800081c02540d1003652294500f01c0d001d00300b55440100d4078146401070300400c2c503460202200105900c074454142c02c1d81c030029042e14100b000d0300e1325505804003180a90400d20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 420021528 1250 420020278 420020297
    0xa060215071d01140408070e0f01050307050a061b0c0e04050120040308090a0801151502060717130203101d01060b1c1e02090f0103050601020309040c020c030a050304080d0203040510 80
    0x403802141110b000742280c00440d407e5691315070b12895034501c1599500305014543c000081c0c07502c0c00040c06010b035040200046a0313145000002e9071841c0031000c0c200e2051804003140804110f0704402c081c000e04200c44402640d10f8503150050848811002c074400d05013a03d4880b0061182080aa8041c4c1b41e101581e65641d9034240005a403848190f41300002560a1a40d18140c191040044c64100c0e1401000038034001d2140c002a80c03561070403640c550000e51012607402c11080d400001c2604208007103611142401140c01190400503aa010310045544909044c04a900510002c1080007085002005894108003040145d03104140600c2d003151080c1c98048120b017065403140d010301600c01d0070903030f031401c410000300b02a4125244080c1301c0d8420b014008400c0d40a030140e284030300030580c0558035022080d81040300801d4240c0c020400c512418101902c5030300d04103c46405940510003c41e2075920f040413040c03070002101c92600464000303010070461600c51030380030a244001d81c04d08100c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 420022778 1250 420021528 420021557
    0xd1418130e100c080c0f1306050403020a12050a020405280b310207031b0c181509020a0219050a05070f0e0a2d06030302010b010c050303240a060215071d01 68
    0x140c1c0951f1881048074114244002031250f04180184202c038801d451103284a1b9441c0e0b009100c2003560107001d0403d4100d00410001840e0a07030201d54420f6a45a5001c0c4c207100600c3c02751492071519162130019076445860102d14640107100246401034141218007213624041041e01c41c50700c2c420041a00c035000700d12001018020a690b01e4020012801c4005000181c100b030f1080720480e21031000701c08007084009680f680355010b03440c5070310750940c1c04d1107840c1c4c038085110009612210312602140900c41c5c9805c0445520025110198024001860014070038104181000c0950b0722144240c11284420800070660040b0b09034049298200042c500c104101d284d001071802e0140903801c0700703144109100a01e010b41c032503010380303000354002c008180e107400041d600f0b03480886000c0d002e40d00c1440050701d44201c895540a00b041040c18200b03039041e842010540c1101c06820404c0580c000c400305010b1100c09c151610b501044510f800e50416100031002e030803101d0f80d11074180c100036000907901c90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 420024028 1250 420022778 420022807
    0xf0c0907091502060609010905010806040210020c0402070807110d02031e01061503051501050405010203093604050c060304211103040b13080d1418130e100c080c 71
    0x2048000250b8050a2010400a4030ba54003120b4040c4100160310000c00c10728164403e590580d00140000c14130f58a59800700000c00044058010440c07107009031002c1c2c207440e0f600140c44664890038401d519907090f86080c0b80c004d094074081310f0141541c0c1100c0005079400151320844482d01c0d19402500180d14242d00d03001d0a0305400804000210030703d0780c0f141940c1644601c1c401c0d110703040d075020226256001198203104a11946005074014000404a441d20700342c096108212041040384d0504e100e541199030b03010310f41c0708482c1c000b0607100b003105003e0144198030800e0003c4404502e503151030380d14000c50400400b42e1042040c2c1c00c44004603414011206001441119021641c8440d076980305840c0c1a4418001c1c0a44110060310005448000081e40b20b00120b41e03840d090368030300d1250240502070700101e0b056804815078450020740368481c80300001d00c2000c0003202142d01496480c0f81850500c00c94070032a00315140c00f0304940c0b400c0c0e00503507040c0c00c0341c182501555595040f0b9101807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 420025278 1250 420024028 420024047
    0xc0d0c0503041208070b1e06060a11070303050403140106050904060506040914010f1d06070f0c080c21070b01061b021e030705060715090303020708030906040606080f0c0907 76
    0x410108442c0320741c0d0309100d134880c043d249552249001801d1941c2e00d0002900300010800b0162103089000301040c02494484082c0204140b14680700071283c40c114050f074a40800d076807050300428000542481030213840d413210364000244030020f0000740e19002c0881d4802d9001030000e408540e860000c034840e0b507120b801c05400c00d9040a01800107600000480b4028900081036010071841c0030210051710303084208082c0d030160540040c103070542c0d44842c02d9030b010152181d02402c1048051000c4009640754004e03084030014000104616000200401c0c082402c10380380c1020250140318401c0003400c0744407000d0544503985007500340d4040c001e900d8024202402030083d8000c8400082282610036003151061081c0b0807011150616902e01c2440301c1d9201d02003000c0c044800c1020315404e8801941c0100885c1c6210b86401847c2440585a20360389400c155003e5001c0c1d00084140018045a40181c901a003441c4000d044107588040f1069940c10a10a909020f04510700c001000381e4044c06004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 420026528 1250 420025278 420025289
    0xc060f0f0411011b0308090f0f0c0d020f150a0905010804080a110718021809070219021f020f010605060f0406141902061902120402061c2904020c0d0c050304 69
    0x1380c039954076140280409400300c0c1c0c0d01c00070b441603017818138201c900000d11401000800c0c01404801d01d5800034810303400390403c030682e089006122402800d80700c01170030301c181c2d0441e414001d4607800e1100000340040c1960b40100d04000420050101044541044811914460903c4003564468103102c1d03051140316800300000b440203401080c0c1c2240760b9002401c011542c0410545d0105940c020840208010f6800500580c00b40c40c4013904d04141e014400e810310700041c980d2400c180c00005c0006035852050341c00d80160080c880786007d858090050348080c1030115000750821201d0b0703c5001407400b4510600b000c100e0039a10081c06a00c1e030a045900821104c9040b0851b182250000396503004141d03011082c00d004820080031104042c425260818240c546400d510f0701ca50702000440d4024a2a0b070030744d05010307040c4001540e244d102c1d070038a510891124120b01c83c0c80c0c055041c07501e41404c501c0c60166004202010200d00040340c4201c21040d1824044002511070074010301c1c50060f6040b8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 420027778 1250 420026528 420026567
    0x1053c0604080a1106130e090304030b04150c090b031f03050109050303072a020f01020f07090606111209010c17070b01090605060c0c0402030601020102120c0c060f0f041101 76
    0x2c5401c000118051001c28050704500000410100a00040f031083c08070484803245007040510070900801442031b0000764550880b400c1c07039280d448a89a00308280e40171201900078802800c24001540182034020625050000d0880d181c4002400b032448000e005040c207000000b100921800c40240903800366401c400204104401c500c0c0c410303078a52043c0c510a012070b004100018040d5502002008020405174680010f0189035090200a0720f444040c0341c10350141c0c001003a01c800081158a000301b075a10000309110b850840068072040d41c0901c400420b411076080349103001052803c40e01c0d440828070b450403104286041401ca54010711012550709240000c0c101c2c01c0c000404001410381309200010408a5511000c022403403145000f10ba000790440340d428090761801d580036540c0050706000140c40c000c0c11480d5015002800c446040c0c8003078010603042c042e1401000916484864001241c0c4103080020b01b8102c070b034800800051407412107401079a040d9116240e5140c02c407140c01d29 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 420029028 1250 420027778 420027787
    0x604050f161b35040303030506040b090a06030b13031713051204140a0305060a0903090b0f04080105070806150706060e0c0a020f06070507110a0302060304050604060501053c06 77
    0x10083d156025030480d00d62035110803005902601c024890700a40c05507031030900c1d8036091541d81c054000c1d040040c400c55003d599581b14407001c0e00c030020000e00c11204094001103c03419803034094459000907080c1c0212000034902200000c0c0c0001a035a0b0301c4c2854820000c60795101c030344c1c9401d40b021403c0002c2042c080c1c56030340142c10801401038401d0b6004400300b20603049240042c4114a2032600c0007500e41d60200020070540301d0310b944007910780d42c082e2500140c0c80c0d483e0b610271001c61b80107401c0f24844920016040007200002c0c441c10b13411801c80d01d4800308a090420010b90300c8550700845920841000812004021843e17118500901846a942c0b900345400000410b550700030083c0c01d8054010000703180411000464064440c40c0d15440301410010300ba00c031840f01d1080c46c1d43d180e41100b49198040b02682c4c1e002e010f148514480c0d4020f100c20302e42032a00340c05981041e4055400b4160b54059040390040c3d1441a500103100c401a90f07540c46080b040d00d8140740703510804141c01400028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 420030278 1250 420029028 420029033
    0xb06060408030f0d06081207030e03070503030a02070602010605040510170c0d060b01082505180a08010c1107180522050606121b01050f04080d0c02090604050f161b 72
    0x401820082c04c2030901000140d0b50b48040341d45070740800503501d0b0402d000304907000019000c2c0d400242c11003406011620b4a41c0c41d44086072466000b0800040546e005003000c0024039424021000a80070940c0d00340402d00301445481041c02060041d28000d06041c0c0c0300c818204030030441d000386014014820308024080b42816170041140c4100306000510910014501c022002c001e103d0300320b603200320041648940380c0c04030350a80040320320310014244c1c2c2d22084a07c0c1d0b02c04244501400402000140c0e07151804409000368803000c42c109800c3d00030f031800300312910f400403039548080c4030074502240d1503540460b581c4140780e81c0200c507241400d52001c0e09051040010b100c030310980c4140d801c0c03437044502c980c204e0b50712603001c0560b542000005190400035440b5101400409032880201420035459241075414130000402c1400024140c11402c415032400245664100c44250303070401190400010586408400400104081c40e42110142071203120308094086040040005100c400092 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 420031528 1250 420030278 420030307
    0x1360c090507080903030603060f06190b03011e060813030c051606020c030f3d0c030b060a020a0212030f0a0c05070503011104032d080c16120b0606040803 68
    0x42d80c410001440000c0000c180c0b5500104072806130300300034020843d0b41d8a08050200e400b1000384404d400101d540ca611088402204005010b0f005d04208961698100417002c0200f07820b030030344041c0c40c0b007006204014840c1c11646160300a10301c600d010080e11042d0400780e0381804a080c4c010000c2c4181a03100400160800000c0151202e035400e1310750348442e01003010350f600d9001c5404092078000c00d03a032048800040161000a205031022009402140440d10010b803460700400303501a610341c2090108580d161103a50039015007118040d04100ca203a000039035508001c01c0c002e0280e0580440c07040030315403c10a41d043c0001c00c08803550703aa0b030b02c030710020681c1c500640c0440b500d2150410201f520701c1d060050343c2000314a10700140c1001c0c0742d901c83c1c00242014190080302c48142c2d902c0000305004c0198040f4a45010b2941d10360380302c5045c02043c2c07900c41007580712a0301241c82c400501a80c00c0662520848903002003800801c7d0715407200042a41c452580055070354440003079504e1139115003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 420032778 1250 420031528 420031531
    0x3020901020d050c1027030c030f02030a05040e04230703020103061703030c0d02120115170105060a1211070c05100306210516090f0e01360c0905 64
    0xa900b40c03815201d10100a907210b010301ca848071030640050968116520403a802940800f00208541103200c12034000c402107014001010b400245240100009154210340781400343e40c0c15200851401d066160005c249010318020301342020b0500d00818280081c030036010b49000c0041c4030610b61070204042c0e0b0740c0d8403110351004a012074117000000030420241c007002602e02c0b5414000e0740c610390740c8024000e8107501203403c58603180e909100c0003c840c40d10b000801d0103440031179000d01c00c0720074544000d8030b16910a000321260002080c018000c41c0c40ba0002c0c0c0745404018200405c880700c07100300401c0a0329000c000641005408580795051142204c03003031007141e00035129655110f01c2501c0c21070039a4010700454100c5030752005528a00103184500160117400b82040c2d80341c4c01c20303044854809904503070000c80d4681d164101c0340780d2400da41c0310762503a0280b0755000f048104100d2170b01484108900c58066200c146c6101071803c06880c01c4461031205038804800c04509843c0c040032002040c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 420034028 1250 420032778 420032797
    0x9030d11120f010611150705070206120106020c0103050f1e130b1312170c1608071505062202030c09130f11160f0305090d0c0e10050a0311041b0302 65
    0x1a03171101d043c41943c1c041076811000d10304040b0328406544191059034183d101d12812600400304100700c8540c5102450964007900301503001d07146021303a0400040c01d8940280080b1200c0c03040b1014800304401d441c8040d8070351071044503007118540d66078141c2c0038000300107017020b81230402000c1003080b81c0d1115891920141d2168075581d2180001c100c0880342c281151a8641148200001080c1e0b00c4507648040d14100d0030314600c5100e02c8000c0e07920f200c00340c0c000c01c9044502c03034009200c1d180e024025010b440d500500c152021440a14222029100c601c000d6a01e01078650b8004081075003860544110390b00460044d0114600701b501e4016140105260120a02c80301c0c03410f020580c014488004894040394004102203a1f040d40b5196156102321101302103040c03080400c0054400c2d2102c2c840c24841901460030485071300e1801c1c54850a61800406044228950320024421a42c9006800c400d0300e82048001c16654003540101c0c0081850180024001184242d450300782541500104107900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 420035278 1250 420034028 420034037
    0x60f0a081602030a0f080405010b0a060c03140310030204020306040f092f130c0309200a0503010b010203071e0203120d15050a05060c01090605100602070e09030d11120f0106 76
    0x4001e100100e0300d03401400c071403200207045050fa58a089205000645d04035014400020f040000c180026208400a80c8024041521310764442c3c2030503081402d04000b581d1000c9818694680600d44140322509408020700c110340c04000303e60076484640c00300c05111307034000007040032100c24240f03071104003240e212000101900d202d480480a8940c0ba0303140b0140405058144c7c1d032079407280c3d41000740c444210781a04140e40d94032003002044c0b08014081907142c2c8100346c1513100c50610140070044c80c2c1500217601980c108030b01d190b00341c0da00100305c138603050b0890080d40c0410302c6000130880c0c84480034000395262054003030642003038148100910943c0c40c006170400160b9030340158000c030028548983c0b03a004444a100700540d05007540100041c003014000001c940090b40c0c1d45504a030400d840c1c4100740f03812040180203040e0104a11030152282c0c81c07802c000d900e0041d03001596840390b6025000f5090b03c0700540201c214010007a0740d1400b204941803421403405e00c6807520604024441c403070004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 420036528 1250 420035278 420035311
    0xd030206190b0d080a02160f0602120705030703032f09130b090a0509010209040207080d0c020a0f02060a0c050d1706011b0809151602040c030e030304030e060f0a08 72
    0x14441c51040025203200070300350650b00c00e52a10f40040d240c000045400650186520501410103400c044c0310140218001d2003004d00c2c20311000034901041061995140442004001e02262001091f1514582d1600e0040f0701e03804080d10150445030180e891500300000030600021210b2080302074092001c0584008980c0114000c4c648107032805128102d42141e4170102082015259030411740e807190b2514009484c0c403100b8400304080342d02894064411740c00120f528290244213010f1441c00003070610050800d208907460784075103130301e41c094024890180014030346055405900d50003010380d001829584180d42c10240541000e55802c800c941520003040000d84960080108806610040354a00081d000b1070303480814540c80040c0c081d84c000d60001c1000e1070014200c0c0107080d0b41c8800307030000364104d5482c814041039580802c400404e04d030a2944480c0740f03c40c00401c2e41c0c1d00640602d007a1008900510100d0010b105007810310000c0315001074403c04640e040030391240034031403d642d24243c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 420037778 1250 420036528 420036571
    0x60c1502070f020d0620070b010602011401440706030c050d051f0314010c030203060d02091315024311030714010305070e1f030b0d030206 61
    0x8911607041c005010102591000015003010070640746010700c80c500000300c00080c1600c01083c0d1804c0c00e00403582e0300340002d0034810881422039203070041800f0f000a108800046104444811050290720000301900700c420030300301603100c003401d500c040203806e003621188a90900b003259075000707403030f000706115050b40001c086110b0322483c3c0c1c20f50398035a1010b0515504111150141c200a0690704500c00c01405800f080c8613201c101d94019803003400c901c0c24003074400d8a010b003961458440c180500d841070041001c591205001e400d2800c1e411140070355280c1e200340e42b03100e4202c02c030a8081c006940c169810b54050050380d00a0807100d04070011a07400b643d40e60179202d0074001030340b000c5401c0c448074085c0085546c0418802c038456482100e01e01c900010320000300e8680b101c2c0d60f02c14102c0440070301c0c2c11111960035104881d0040003a180c20541d100ea01c1c40071880d80c03200040c81c242005000c40c02001101e20a90020245240c000e003580c07410351180c00d000790750340025194500300c80c001ca006000d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 420039028 1250 420037778 420037781
    0x51213110a051302090420031f0e060904051c02100b06040b041202060c101a010f08010e07090819020405070809060a200c070e0a0606080c0702120304060c15 69
    0x7100c000601c241c0807126000900e43c00f0b508852007454206403500d4104a1032010000310011408540e5426034a92410342d1050110790040d042d44580d08008404c1804490244540d0b240c0c400340550b100141500c65141a41c0740030058035a50320f0214000035500e004540c080b4110203040c10204040c01801e00001c00c0102138842c83c4240701401d4000c102c10004c0145100598500d0344c00100000d0814160445460800128882803103140d0782d500d64001200042500000c0030900a281c0503140c0150714078080d0007800e041c0905400c490740b80700010745103881440301d00040c1c0084016280d0f031000c05c8003694000c0d04400c0c41280b0650070180041e2036039204501c003910440030000141000e40741e911120006008041100d0548003640780ac8424281208000b0500c0300390b000c1c010b00790140303801e040d95079805d0041c2c840080e190401404004081d0310144e007070341040311441d61580d14070081c400214415444102c0c40c1c1d03c2d02001c500029001c0d0002c0d0280301c1d59000d000c1868161100c1d100120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 420040278 1250 420039028 420039049
    0x20904080405210f0c090a0e0f060f010f120f0f170c0307050d111c0c0c08030d14160806031516080a0b0d030e040e0f010e0c090709030f0305121311 65
    0x1508020b07940009201c4101f2504521400b02c207003003d882001e076518076000d0415a085030b83c0502490500010080c00d144040f80900030f000d45425014030050355910712a03400d0400070081c1c0700205000008052003154280020300740001217002d65698041a0041c0d200c0c0c000e0f1400307491900902203480c1e2441d000d190036109602c0b512015000c1e0000c044c1d906211504010b8403c03003040b0080740341c800003491503195440584030440c02103440c0d031006180c45041c0d07480c00052000b8003580c107003032261403c1da00000740f076010004c1c2821700c2d2940d920004240b405501141e0104501c40d9041802880e004508000441440d1546ca0b4082a0b94103204081a1541031585035084505811404042485008405410705004001080c49440300e45090b1824400c2d4001c1540c5035540c010a143c150010020214080001c0d80c10081520382601b02820302c0c0b081c0d110180c08074a0b503400c01401c1604c200220742042e18428000f003c503007841c001c0e03135111003210300c2d00b280c1c64414280100c02c585006103984 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 420041528 1250 420040278 420040303
    0xe01090b09070e161710150903111002030d0c0f080108190303022203030e0f0a0e15060f0a1d030303160f030e0102070b1e010b07020904080405210f 65
    0x142a252900c3d41e441c540302588030f0211007040b84070800c4810101031515418080c1406c4103408481c107041c01059201d00b055540701b0018031909071740800c00a55002c1c10074001c2c4a0071118801008030320502a0b0561250076510b412113881c0c0131342a10115004130f1a220041030950340c030320880e070700c8030180b1b0755a20012030848000080c2040c2240041d01c00d4000b0619421300719035034503810401c291000c5a00106410490101e580c0010311415814035038081d0840c5441211440403035031070060f003c2c40740000500a1882c1d40c50448900d2116110042161511704074400103941e80c1c032451500401d11101c80c68815150000007811408516000040d41c0c02520386038070200c00d562030f4400c10382e8140b0305010320405058464410626144082c809044070902810100d191494040e5a6500e5801680450030340600707800014480344001c1c07410758a4095055446440c644c40303a0802a00b14029984519031100400c090070300b492055503202d40001020400300d0350205403d80002d42c03241203c001c45c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 420042778 1250 420041528 420041549
    0x360305060609090a02090711030a02071505071502030a150b03010e070804020f0d03020f070303120501060221031302060f07060b033d0203010806090c1f0302031503010e01090b0907 79
    0x10140ca4006c0a4680200b05e86c10615207204003250054195005406680302581000008000501d214584403000b0511072510340d19000f81c680d80d080c3e040e000a109c1910140d13001c80000d50283c81d980c000c017406020040e0314803045940b9005114158000d0007440d000c652100301180800303001d40003140c02541d004001400142d0990103100c03000030049002d5045100c1c0124494280c00e080c82102c02a500030b80c1c604c1020303040c106980d029190103a110f001154080030700a403941034200030180640b0207448449a482e1191076508500c00748142001c1e600190009030661581382c2c8400400025100f902e090014002210400d0340340c00e0100e40d8045500941c011400c005c4146040040420b03201509440516011a0040040340c100340c00610f017503881030052001c491010030138480d1040c811104407100c03d5124101f115100f800301030090601d90040081002c0400ca2001d1480850019000f00000109000518041c01c03891006480658400c00480c0c1c0e8840085135090541d0b62803541d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 420044028 1250 420042778 420042793
    0x408010b091909170f0a0201060b031015020a02211b13110c0304060c17030403052506142202060f2206081b0c0d36030506060909 57
    0x40303400282070b6009084032004c00300c2d00008004000c0c030380a048030307801460300310340c4610303020340c01030b0866100b0f401a006a103070a208028110100000004c01d681016008070310130b01d4800381c2a80741028125000754010004152454007400c0c04c52691240101d40007100d00403802000403840070f03080742c0202d64008130242400070454416410241062420032001842c100c00760000b10b0541e08a6000640011403443c0030388140045035010040081024002c1455808c00d0b030b40c040c1c0709101d80c404450f0680751000d00b414080c505115088002c0c0c3c0c000c2c0051001c0c0d20440c400c40c0c0d140c8001c0b54044a0131002d1500c40b02c0480c00340a045e24441da02420843c60f000c0301c0c1200b0149a001040d410b2260044e0764084d41041419042071402482103403600b102c0d0b402c3c6516801151610700900040410301403141c4518000001020800c6036210b0032301c240c40100c03c02e440e110a0b8240701c0000c2d02c0c482407800390480e007030107800080d04407400b0760305171125a110b00040210940d4192907050880c1e004a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 420045278 1250 420044028 420044071
    0x3140310050d06020a03060e070503280e0d02100b0a05041109060c0102090301113c1c0b030f1002030c04030b01090504060c02060c220e0c0408010b09 66
    0x1103400c020341600204905036140300040c90201c48400072618580c0115104190541600545000c1c00c440d8152040a25207030b00700234414003005044030101c043c400c00740100728040d10084030749d0380c1101030140320b4140503c07002940d900002142d40c0051080c07000f24405036805208020000c6001403c00500c2440c1c0170410015098410020315156000c024010160b61007030300510100c0307816000981c5600c5114101030031600024004010510100842c124017103605810502d00392080308141c849403004083c8142401c3da082c8681c041e11703800030701c0ea90902a18624000841c91014091020749654414191034000c001490716140d03110286916000c49907401840d40561010300c00b500349075580c0c48849804c1801e901840305030f5903403401d21003841000e00428880d04480c2c00185424140100044018851242600002903500060340f080e4004284506e0042c5001074404480303041413041c0700850340c442d02c505482580707801007250702403c03c82d0300c1d94070031410b00084681c40300c00308 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 420046528 1250 420045278 420045317
    0xe0a18020c100c090807051c0201051e130e0c1201060c05030702060703030c08130809010c050c04050411130c020c13020904050a0506130e100c0212030405150106030903 74
    0x140000616000b00e022555000065119202004900340d441c1284075181141c054200895600060300441040c1c140f0703042c074515104025107096081c80e08607a66a140c401c0003a90010410341034104100000301c950001ca003203d456015254849441020b0b40c80304030f9002d0180c800d1801481c600d400103001004014014500c1c596414001e4003502e10381242c680c00034190740d1007400101d000c680d5808000362913079032000c4076562008000184180001464440a40e180a070020403410401c00045110030440240b0222420340d0340541305201c1401d2510309214900d05401f1124059541a200301c01844101d010301b001281c081c1c0c000d004806800410b012400c8003a0303012040d800c2c0c0801154140751201d02c2064850743d150600000e00e4140501080804524102d19600982c00d185a289482c030010402005600e100100081c044a900310160309107080d51111070b0181d4004000c02c02800b0010610303c0300c020004201030b129a072112001e40c01c0b1800c003070010b40002c04e001410340c00504003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 420047778 1250 420046528 420046537
    0x512060906040f030c0c090f1b0c1b0b19020616080708040303091b060306050604030206030109020d0603050a05030306011211070b2214100b06030a0b0d080a020d0e0a1802 75
    0x60300d403030401d01900d520b075103103500203070340c84040b100f0340e1803003014035040c0322780300310300305582e9502da001c81800c4090130091400c58100d10140c0503040090b01480400c00021001000b0030318a581181c49012890f910f88000c2100b000300300c050301490380000c1c1010380c080c4c0e4030040f9080300c1d1200000b90329000421034145000034401c03801c2c150b854842c107010440e200c0541e580614420390601480703041210060940b001d9900c80d078000c02e0306000910041c3d0b01e10090780d040d180e801800503240d1000c207280002600041d03001070002e000c1c0e034540d41e050041c04402140300740c40a0b01d0f580c18a5031008511302c1159200380d1848814901800010300003040412043c0d080410615003000010000e8580307211840c01007021104011120f1514940a0090000644c0e41c40b010200b0000003050a0200c1c2080c40010071583d80f0f01c1d510160307110390f0b94884044c0e03c41076802c22403c80d156a402000650b60b18030006071000802c0800c0c00b50411f5103805603a075020f840745942210600c60310340444e800603420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 420049028 1250 420047778 420047783
    0x409140d0905061605121b16141c08191b031d0d0618060e010b0d030c03050f0a0302030a050f0103080d0207030c050f0a121e080603250512060906040f 66
    0x30100849030b06e0280034060700800031030030f06d43c20864458204880c43d103010032030524a8400003034010480c0c0700c48980b60002140c401d650300c802e141100007c45110a85400380107100f0174020a41c00d445d40c18001c51010070100544a0900c56400000724551781004070100400040c200b41c00700c0c0000b000f0000107004158003820b01004c0034800c0d650801600c2d207021a00390066440f005240501210b4060900b038001340700020000f40d0382501c0814071040351480050300780401548504205481041140c003146d20520b0b006480700c0614100401943c410386080420701d0030b006c08544620031074541a4100d81c2c3c4101c1d502c0c6000b4018200d00082e400c810300640a014640340e01c01c002c02c00030700c509500140711601600c0c05011500d480b403880005050500204500c4c005c0d102240b45c1e04078108a4910594240240740d6616040040d20384196484410700881c8070340085101050072121090543d0012502c2c1c1400c0f0796550500355440204136040060b950040780171030b020a039140c2e05a880c603030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 420050278 1250 420049028 420049033
    0xf030a212007140402120403030f1d1b0d05010216020a14030703150f142d0703050c040b07050d09060507030e10020c0619030b0a03050303150604050409140d0905061605 74
    0x200d076165142084400c035425170120381c039003030aa040c0710301a01c1140d400c3d40ac02c070003052f0442003490031260358501000d000c8550101c2d25200c4002c0c3d6440b80e4080035000d41c00340095507517014651402c016000b41c100c1c1213000c1c020a0101042041500111003141132019005000203032542d15a211194801d4034803244c0940c0e2420290707400100c038003d001c1c0c2903003400411042c40c03c00d010481d55002047c00003c900380380e414a10641000d003542d600f42c208501b446e0200d1240c8a00b585850705c0c1c495640280d000f803800295440c204a00402c0d0319001c6542a10742c0000240d44040c15030700ca01c10054020001081c8010380385551411a0402150709210310468034800c2c0d1100104445600600d1a100001c00d01c000c414072080c3c0c10b001c1c4040041c0181c0300080c0c05460751f9151607580c0000741035103901e42e40343c00c2d040910b5201c41041d10300801e0f00800901405646040c855030102c813003280b4100e18000c1c2a800c04640d07000f0310002d411920040d00d40c0c1c5c40c100401501440241210404031a41e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 420051528 1250 420050278 420050287
    0x1d010e060c070314030306030d0309020a150f08070e031908210103060c02030405010c080901030e0607031a090402010e060a051e0405030613030504050f030a212007140402 75
    0x162601000350140600300d8000b00402400c504042c5007039401d207040f40714070354420002c00c100d0b902d01080080c5003510314180440c40900314400950400c0480d08031011040035900b038500d40300e603c0341881114252940b0ce01d0000d4440d110100c0c2e0413400c43d00640e800da4030802c03e0000132044880c40003015030260180f10b0401e44484a00e4002d003d94040d0382203042e444000520a00000d4070524002c0003550000b146890726013000600a907911500282c806580880d0f0f0445a07402601301c10b0340c4d64820810395102d0726204c400900102a6018002d90482040300c1c080381074180138000500894050f103e00706191405d804028003076122034044d40800c0018401110003c101003144992404090981601c0d14100000e0524042c4d00401000c0c10390362004003113000c41d4001c811079054410030748101c1d0032007200d0070101e0315224240c0300060440552500034402241c0000d4412095000c3e513a540000d0494155094001c03036080e00c0c4042e560700312410400030101c4440741c18140c2c90010b000507041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 420052778 1250 420051528 420051557
    0x90906011406040812090a0801020903060a2712120501030b060904140708010902130b0d120203091c1202060408030f0a0617060720060105090a0219020c090a0c1d01 72
    0x10142e017000e000d865400045400c00d060300d040199140030348040300085091583c407031700107030350b5010281c500d118031035a40740100c80ba264914108140712000605041c0540c1c1c5629060b8130900540c0c112070700148810003592900b000c02c0c000c0c07504894002480104a865580070071110b400c1c0644200c0b40d080e0382c291400020182806800001d011490002610b200349005001040444624200d0402d2400700302d102c50b9a50b00d0603002c000358110100418550794040b00b81d10798854002e403075130301c05c4a4008601039010f10900c0c03000d40700d125000c1c0c144009022902640d680030107803401403000c030080c800141143c0301c06c0c4080c1c0d0300c9a8115404681143d64083c040b6980704008003220b07154002104011b10b85400c103000b021004800020203c040000078440f944030364040c0161440340d601c0101042400300075405441114042c44841c943d00040468060b5403280400d060f18018035014000030356400300c600c144000604162a00042e540080f828014803030199640c2506012107041040c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 420054028 1250 420052778 420052783
    0xf22030f180815150a17160605030420060d09050c040903050307052b02030f011a0702010e030307060204080307120309020a0e100f0b0904061211060d06090c0305070e0909060114060408 81
    0x1b000c8020030b00c000c98904940d03a50a06032052030f0b510419070341c0c3c2d2007040000e07400f100b16640990021100b4480c001c452074103411510204101700e81c0100d0200d00c03500c20103425800000418403c000301c441c002d84030303005e01c815550f5017000900030501c28000904130901840c010030010324844070440b0600080d0f0f01c000d2003c92503000410082e5804410400c0810b031526402d8050003540140c0c40324894100d44440c240d100f40c0c00001d04010710080000b05e241c07000c000380d611407540302c4c20564485407034001c21aa2608800c00640720240c0070800d90802901a10402c120301c0e80241c8048030f52818040424450352019014580c2d01029110001e42903810000e0400644a00c008056440c201d9504000a440054001d598078800500e00140001d82076903168600d4041500da40c0d85070204001c440740180055800701d180303982001c518019180e45640002d1042089844821110b89820240b02200f0801c03142002d860307100e8030050040380c10700c02c0b003030352100f41c000d240f18a81034903054181e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 420055278 1250 420054028 420054049
    0xa020424020607080118020705070f031103070603020a08040605040f05060c090102071a181302122202090c030910060311270f22030f18081515 63
    0x25461103031450010680d9414041140c004040b494942099410203e020902e000c0c60f54a402c199980007850f482008028403c100080c5103041042c44c0d130550b01d081600c880190584002d2081c040e10b6400f060041c040d100741c4407400302c20b58480003203a0340c41d0745242c01460b000c1c000703950445094000a0002e0400c001c86803140d01c1c0540d440307444640c20800640b9104082c0c0145484d102e80035560a01a070032401178500c40f180003e1904044034080f400b107050440501a9400594000100d01c1001080030040b18010700313404800c0340a2860400711414103001d0520001d500104200124002070000b0303010755002070201c030039550410044010384040798626801151440b50700f40320340c0035a14003040000d2040707002d000c00810004d6141e0304a1a4480020440d0711080c3c043d6000c590751500d1461100c000e03000501c2c000c51a603010b400c0c060076108400760300c0c80c0003440705000e00c40054500c0030103a0807155004010891000e0320010103031304c104001c18043c1002100c03590740c61641d81d00d00d07078107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 420056528 1250 420055278 420055319
    0x11030a12091e140d0c02091302030a0803100e150909011113091404030c062403050606040b040c090501140d021215040209010c1e0b10061808150a0204 66
    0x10003005600d480d282c10f1400d551046001d99801c92a00403d01d1030300000c2c06450b20754116030170130042e583c0030203d04001c0c0d49064003039054400e2580040c1045076550040d03010b001101c00e00010f4680c1c0d04038840c51440c04480c0913114010300240f55140382061144503400510140012031010a8680e104e041a00300024050240c1101881004400a50310641d0443d114003001d03410140380540b00509800750408008201a0f80c4540b04011040007068030414481c60484102d0040d0750380c2011540c80c0001c0c3c603880d10691416181010310328140c400c54904180c59199412a1450a0015907000107613603804902c101040185000da42e00c6407006041000c2801c05008490a1890b51489450015812103008502c10403a10300030f6a088030000d0310301d6502036884518080381d44d50040254181c1c03032005000241c80345c1401f9200c06150000010f440903a80c50107000312038170000030300c00e4519100301e4000b0341002c0d4805560000c90311842d0750021003540c001d4075081d03450070140c01c0c280d01c00451 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 420057778 1250 420056528 420056573
    0x303020a020c1f23031303090306090803090f0a0c0911041a03040507091e020307050705070e060f1813081902010209090f04032f0a08130611030a1209 66
    0x10f149207039006a000c81a50349113140002c41000004c113000410311000c3c0c0024640340030b004502d810588110700c1d13032001d13540c8143d0a0201e50814a07000d002070f0005d45400c581806221921540b402e8001007184590b6040b034070701c102c140d2600c9a1300c40203145d541d0b070b0640302040400000c160322105028030b0380c03080c481c0002142d41e4940b41c1441e9041900b550480c1140909005120740016154003901c01d111070740d910016540c0c0c41d440415120b62140d008010305500031440c00140036509541030074440c074401c1d00c2e001c003601564004c018542c215100f005503031941140114505003203503684619000d12411005142010100700300380700021451010f00140e40000d10700c3c48506001401e01d4228035203100345140c60425035800b80500e8481c6034900409103000755800d1010302c5100072003506040000c260b4600c80c1c141d0422300c9166020042e490005030681c00d000950a201e03404030305001c41001b0103035081c004412811515942e6250310180d07031039150340c0b6640206140210001079440344600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 420059028 1250 420057778 420057829
    0x90f04050c19090f090b0a06090506060906160c0806040b060f15070b0c0d06060905030105090f07060c0c1503051509090d1b05060712060816030303020a020c 69
    0xd00615181416101d90b028141c002d601e40000300303003401d88206560842502040c2c116000e1310300701c01001d107040054503c50b510000d00c0b2049490740d0040007508d031894002d002ca9520380e0705210661082c501050b030071800030072914031410550348148003000d11481c041401a075440002c40d2500c441a035050b9010008181401414a042c414046410400703954100f40301c209a0704007880c501500c4000350561038a1800a1080f0415508848030000d005000300101d0b81c842e88002c3c42c0c0707034540c05114000d40c60b0030302041c2c0d032100020b00005000c204000030010329041c41011261681c4090080b02c00750498036010680c01e403506030b04102d00318503950004c1d031450100d0081c64040360034000d480c0100d407107200340702c1e0200d404514100100c0003414640518111202040d01302c0b0b00291700a051400351070280000294841c001c490302045407801030103038070345505150307407541c40c2d0a1514540c3c0d0341074202000001d0281d0003901d04800e540c01526850503101c1c01191000341c0c81800f408a0902c1e094 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 420060278 1250 420059028 420059033
    0x30f0a0512010e131115040b070203011a060906071509060b1309171b0105070503040215031302101824030509030717130609030b01080a030e01031802090f04 69
    0x11202d00400c9421150b20250500c5541c00c00c8000f01d210020b0502e0b20941d0081210b0303118170319149003071140150816903540c0d0305c0000b00e0140d04000b43c120301c20f5090001f013100d040048090240111401022a45804074030000c000040d80501e10841c1c5410303641d6642200541e50384521550396001318400f00341120204100042000e091030640034240c90443c04001090f600350301d6108c10f00c25111080c0c2d0342c600182404031500f1a620003280c1541c2004104110b02e07070b005001e18051072003a40d20b03210200c1c00104041544c007003164500b162425007c0d80e0405490000e50031400040c0b40d080617020100c084812024005c80c1d6000501162080c0f26581061441280c2250503110316140c204914104414515220f11441d4005030401800c80600703e44003905008071112034030080e141c070b420750756510000307484109544800d64245410303000004601401061540e1890740c159038014910410a005500804101020814840143d8413120041c1c448e46103041c01400808240301c400d00e03141c1b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 420061528 1250 420060278 420060307
    0x60509131503060609090b04060b010504080a1a1305030f0a050d050403030912090509011a0f03070908070b0405010e1201020c0a0f0c08010603020108010315020d0504150c03051003020909030f0a05 86
    0x29406081c44031b280c0a40800850b40300b0780310941080c3c0c40303403000c1074503d44140121168042d581005105020380c0084400b000f09a00d40f100440741c00076030764200c0347d807202d11144845410810107000c41d001001000280c011500040a07a8505410102d080100104414044a604450481c0403c0d9212030902c140901208010f015082a2528549640c2020085046c064041c415039102c15035000b030b403508a603080c40c20380c1c02c08890fa4052548900d455080140301443c0e600c101540381c090004003055181a69040720b00381c070010b84030815441481c00501171500c517030b00030131401c5540c28001a00303110014840780c09150b006014880c0701e80c1c22401c0566456046a0110740683e00d054001c00050b600480c5581c116034000c01e0b04500015a840c4000191182c2030703030540143d1a0208100802c540d09200705d8002600840400c0200f40341c40b000c0d402c82e4410303590254800002780b001c200500e0108015039110b9140340c280ca0900d0300c040300c1000550002d00041c00440c4002ca240480302d07204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 420062778 1250 420061528 420061541
    0x11030a05060405160309020402071202060f01050301150e060316090209040e010c0219050a050a0c06081e13050a020405040822050f10110d180b1306050913150306 71
    0x4680030483c0303051000c007402e001c07918844e060040c0354840e2101c6042d596554140c0f02415008141e100d901c03100100002d44695044840729428103440d00042140e05051181503103080603819205001410304c0d05981d480040141342c4e80d07040c42811902c11081c1e181c104403d008001005016840307180c00d000b017006482441e0007402540c0e00d42220302916950018004030682c4102c5050000040282030032070510312080409000c51080c54614400c0080b0800443c08540c10340e80d0b81e003c00d450711542d480360a04020301c00f0303828081820110311111900750005850500c02c50071540c01c0801980818241d42d4119000d54583c0b0002c034003180d06001d001905075518084072583c000c41400c000000300480034411240e8081e07074940c0f44981c0200d0050b046540b982c0380351f00445103c0800340c2001020348848007105400d05126140000d0070ac4070800503a0004008000034051103403c002d011107690b040b00d01410b40c4070355009401c00b54000f652042080c2c0c4610f211611110b20308500306942510364 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 420064028 1250 420062778 420062791
    0x81902122125020f040504150c2f0604110a38040602030403230a0b180c0105041203050f0412030906140d05090705030f030417120714070911030a05 65
    0x184081100c0051350342c045803000c02081100c00046c1515039041c110420b45d80d00040c040c00300d01d0214030041040d084061340d00c940540f40000340f2149600c400401c61085e08480b002c07010b0344280042070018203200441214054003514510b109607840541418114420340629040407207450f43c1c8600407442e240310301c1140000e9602e14503152800030029a0780c0304503c4061700041d00c4042d0120300404c41340c60603444c40340c9042120440c40080c1811000c50b134054460b142880e0b4940e03607038440c810000c00d43c3c0e4800c0005840c0e00d41040d1500c0a0740d8040c0c400404c00718200b0034108800702e1070306c40f864040e00c0549031a0940901186007032601800340e0215801c00740034000007440041000e01d02d07004a40c1c450f11014400f0070941c490401080c41c1c500796810082e40b5007c2d80940303801010b40000a80112943c1180e850010081080740f107460780c100a0544107020420000100820341c60003100c010321415130b045580141e40e81219000301c07140c14440c107040c22000010b10160b01464014250000b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 420065278 1250 420064028 420064087
    0x60e06011106011a0d0c12050a0501050634080a090b03010f12050a170d0f02030106050924030a0603060b030106140114040b0c01020a08010819021221 66
    0x11001c425965940b18140300b2100f007035100030040000303c00424142c605995075281c06021030921494060300900051100c2da60907841d2900040c101c00050181904075000540403a02d0025488055001c5001e84468508000741030761a20040b0000c2d0150201000d0246a43c2034030395110781002080020107610546119909000500201a04500396401c544c0b5042103c3c2c070403003092030150308151070b84501505041418450100c00d00701207005018071840d459042001485004c0020200e000a0149400050050281d0b01440c14040d040603e0120f4a03908030110000c0013011003402d07442160344161403078030b500d41002041203d00903541c0c2501e045000307100303507421310141404510a046101c1c0c1002401d0b181055240380c080200c81c00b82c89a81c5089964104600141e8040d51003040440002640c48000003510300b004242d05c0302d440703240414180444516000c1000811031050a0003860180b6071002c1c00f020581c2e10194a559100044903880d24070b0041c1402c030500130388185e00c240b907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 420066528 1250 420065278 420065297
    0x604020901141207060906090e01030b010324051510110d08070e0307080102070506010b04060c260a030501090509030a090b03070e15040f1202030a0b04050c03010609060e0601 77
    0x5036940c004440c1500d5145801288441d52400010544042d0400c52a000d00a50001054035988501d441c0c003030b14080d0301c0d07030050b10780d460f549021890303424130000c2c002c44644401840010305503445410306510b42007100140502ca0019002203c4066680202e441c101007400409820819043c610b0028181001c05600d00001021900c460314040000101708401d00050903480c043c1c205c0030340c0080d0150441e0b6413a911000494001d5000d042d05039010b220300783c0000740255801e8202d406030380d02d41d65440e0f66800b080c0d4a041c0c0e03408a40d410301000e940c0030200300104c20034000c09084015100c0c1d4010800c1c0d4504006081214030151407506a80c0080000300d60581d003041d0444100c4030744135003103607490b07079000c0040740d0f0340c1c006080a0340d0000c0701d162602e41d44041d18000d00305460000346090300e40c0e5034a44038a91201d86812000790103404c0100303040003003034911a0300c90b8414000c1c026180703904070701800207003140c181c0d801221481e0343e650402d00002004810300ca503c01000c1c2080d8021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 420067778 1250 420066528 420066533
    0x20720090105120c010c0203070f06080103150e10020a030204030204051510020607020307021c0b01080f010606020a0c090504150204120c0816051c08031513140a020d1113170604 78
    0x3113907a4400c00c14144115506500110744080000d00010710141c080d06c1c107026290780c0000c24020b000e10042ea0200608420500407008074415800b4010300d100003014001c81d0381c050100650002030016061590a000000140e00d850003854881c4040200070055141108100181030320341d0080f080443d442482003105081e000804c80d90034540444185250707030000f41101d004030540704801003040e0034050000440440010310024070203048002403260646644080382d9507a40303020003822065407003108201441c4168000c64000e030107080f104018880903071074482640d00c10741c4414000205600d42d0b1060141c003071000c2c0301500398200035100d600310300d50500d42c003c05030340030701403242c0020110600410b0481281c040c003d0340c02001d581d26807402d912180303041600d00068a002c1c913105924040c1c0402648202d284030081011040d140b42c44001c0e5183c002e400190725034642580d0b4403101074240d400c500c00f130840e1002240b6101246400c0080000342c8400c014a414125400103090100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 420069028 1250 420067778 420067783
    0x3060519140610030905030903030a08071b2f030a050d030e010515220f0603060506030619050711070b0702040c050304050703020409020d06020a03060509160806040b030102072009010512 82
    0xf031481c03041c600403c84508a04009045214526009030700d4803000920b600802d030822080d0340b00300c4054643c0345201c01c003148004111518000d000780039100040c10810310f880d081c1d02030b080340407203c803035413004080590219203486611501513541d0f1380302c140b5008426505001d52100750280c0c4c3d000340150306104001c12040c0414140c0f0a2080707258180780d08020710030200441e4441500036051001c441e01d015400020181030109035529804c150014645040009402c0d004080c40c0d4010050440c080812030024400640b1402c00c124983c142c0124ac0d20301082160094521604003550700c030142d20421080390001c0c010342c030031307c1030500800010503004511882242d40613100846c2540c0c2a100040e0f40c0460007000403c07031807020034029480340d410380c81030058800650f0704030b0f41620360b80120900d08801d04046800200c1040011b502030070309030480360344803201070000b50402c02190703200c01c3c0c0400e04510b01d1180000d0240070b02e000d40740c2a0961801080e05840500c4003814403847c954 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 420070278 1250 420069028 420069049
    0x405030a020607061104030b06090c040e04060c0207082d0a0507061101020d020c0102030402010801091503200405011706010603150b07030903080d0f0b1002071a04030605191406 78
    0x34400c550104405003131002c2178100e540504141841c032599139480e031401000c0b030f040507542c40c1e0103548100c0009031014030301c0701103038242c0d400c900c0004060365807652150701503c0792807140c41c114000c4250000320302d1230400c01007090116a000307071216015013049900522904c609107425950210400101185011401c4429600d0a03e003e17040d07030800f00c040a019102d1489010742c07440c070005844110110660140d03006074402d0780c0c0c10000d079076980205029620200d480092650030074100f04002512014190284210201c0c41d0105188000c005021900240c2c0b113402039a0b004060800c03048014031000b0301414840c28200321410071f850741700d50314900310300507100541400a491010b15018416100003113a110481e03654515030780d011a00075000c1000100d03034903400c06508480a10f82291183d180958942c0288582441c2c0280c080a03035036011030700d5030350720340401c0048041041c3e4020144518980600190008000b41f400b804a4a8001340c01c4240c90000d030500c161a603500e00e241c0f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 420071528 1250 420070278 420070283
    0x3101a01080a140106110d080c0405040221040501060e0c0a020303011401051c0606020d030e0c2119031202070b0604051e090c190303020319030603140f0609030405030a 74
    0x711140d0301c51019000030b18564200e81d82e50300d03140b0000035002e40c0c0014082c0f4000c0c11982912040920480d0545184000b41d4001c02904814401401503082583c050108806451394503042d06140c81c8240b46004070a66007030740c2d04d9444110600c2000d0540c6030080c0c100b5100070b0411f250a150130f800940700d00040c091b4414540c80e241800550381e00c94010303200d00081e000d403006407094244000704010100d41c810312001d4050348540d125614064480e2070f58251500024013181c0d0000b404102c40b00750b0485400c0d01070703880301444184442c41048071400044100340d80240c0711140e410f01902d4402d0001d0b48881440c0100b040c500014446001c1e08c0d0414425903021415444901c008a0111441d00c0c100714105984410066616030025203d44150420b480e08085040c3d2034446ca00390881c40c3c003010780581c1c010084407001c284004110f42c0310502c1440d00058158403561011009402c0c9480304000d94031810f00d217a1441c00c10f0110b60341105c072282c02580b41034030704004030f5251250311001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 420072778 1250 420071528 420071537
    0xf090d0507020f19060207050a030305180114040909170306030a03110c030a0c050411160312020403020a0905092b1b0606080f0c010c111e120c03101a01 67
    0x14200715203c402e4842101e0100508102e00b100d88402200b050b400f4610a40f0014400c0f40300000300f03800c00030840f00580750590790307545c64250304e46d040950005155001c14104900400303960407a4441c0304c00382001e8804810702003203110712800d0811005800300d211645509040043c012181e0b0005074442600d581810a400c0041d4100041820121540704464250140ca01e030b09042000c0c18201034240c502c00c803002c008ac95501c8404000500401c001e15400c0e42c0c0c3c120426010074041c00074980503c090940c090314050301d0354085410080070f40d100100681d04e0b036040c41030a110501804802030b409903d075016401c0801d00c1d03104034004090702c54080c0011000d5211700d1104159000082940100042c08401d40d10100c0329942c0c0289000c8181600400c91590019881055801c0b003c83c0c0040b804401d00760a8010040000b4480c03034100100541e020150003240c0380c100c07019254100d0380303010700309074565034050500b85220138035200903151030a0f4003000942c8904000ca00740c40d00031710340b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 420074028 1250 420072778 420072787
    0x5090a090302100c0e241c0b0a0b040e06010c05070b0a1713030f020303071e030209041113080703120c02010c140a12031506050f091e090f090d05 64
    0x509030b0419810919401d4210306110151180c4d036040b040105000e172040c1e4000003800006080200820100002d4142041c010403580c44c900c0c0d0030300807064110805010025031405020300180b100c040035402002c45400c0402e0400c82c4002d00600141c0c04107081c00c00341c80040460341c5007a01d91040d0b001d00028458003040b01d00e4454031603107800314810031b03400ba0101c032400c1551034920962660201200001e40c08001d114985101100340d07405440f490712005000350a20f0300707030800c21032401600000c2690902041e44655114028014869203040d4200e0f641c1e100d080c1c011013032480a82080302103501c190800c2000803083e606040d40c2c2e61007480c000c1100e40c66480122140c07503000401a24185255070305006e80080403a452041d41c0c4100e86105002c0030000040d000c2e03819400d26107107642402e01c001c0003214011001880313601c00c0c00c0300c494a45050400095108003500c00010700000410110030114180501d250741c00c000280fa182c0ca107483d103159625680d8101002c4141001000305 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 420075278 1250 420074028 420074033
    0x61a0109060819020c1e030a020a061d031801110c0f1903020904080405040507030b03150402041b0509120102090604170106030210170a1509150902030705070302010608030405090a09 80
    0xc1e0f20074003001007009660350b42406080c241d43d00d90020100c0760842c0c01203018011101c1c000111000b03441d141d0054504040e45132135400052420128980c3e0446000c4885001c0b001c0501c010038035000c1c40020240e40443c40800113250340404222202e942d48040d4000c034007959170380b89001120300c003200c1c00800c0c40213402c04502040443e0f4002034205620030140000c00000402500603102c0640d820400c564450b2030071800d0b00c540002c10303a050340281341d10340020200c008005030f200d4001b078004210080603c0e00f518044110a04840000c0d102081801c400d1074165510b000c6064918020340c2000c1403400000d215100300c0c49034009171114060621454102034010b0f00003560010061540302c0c1b4001c0c00a468884441e0034081c514044c2c0001407140c41c01c2d0b11600403000314101c0c3c800200d80c10030301090300030300000059401c0e040c090000060725070190300045110380880e03035469880b0300440c80c0103801d5882d6030b0002c601e44c0e00148014000764654480060b44404a1100461406140d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 420076528 1250 420075278 420075301
    0x105031b060f04030b0a051f0510171e092d01060503030a031d0a03140901020a06050c071403030705030403050f070218060a080604110f010216080604061a01090608 72
    0x20101d0b10800030204000050000c42c10320035206850078501440107075110001c4c1110380c1d1800d85658040d482d1000c003840703142007801c024030641c170380783c01c00c0c1d0f0012001c504d40704007400c000c40380a00842d00c080c400c041c070b1901915525400120b01c100a00d0401440c01c444c440744c0480c034001400a80d1012800c4c0e2880e4400d40001c00200340142c01d4950310b00700a50024058500706103481000d08554240d08921000050b03201c511507015625007000900d8000540115400300720b1160451080a001d40003198552081034000c21401c40f04554403c091b18100d5544116403a5030f00300f9410902c02c100d0f07016009000c807a80158181f0380300f90313074011610802c9000d0081c030002039000117038441e882c0b40410007203d0b03007401298111021a45943c3d912141c43c0d49060440340100620141c02e041c07029801d100c02030000b000c00c1401540e1220b0b21240c000e042600c2c280e40302c07070301c2c9034401d030188428045640b180c05544021101c90005035001100040c0801981d840340c60204401500090307045901d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 420077778 1250 420076528 420076537
    0x1170919021507050106060323190f1a030d1112030a0204080115050406050609210a02031014060109031101080405100f0207140105041a060f04181a0105031b06 70
    0x50081040d103d0b807041c2041402005140520301c0428584800e081d2a40c170b40a02c080c5803444000d00c1d449141e80e400311404103405654022058054450740c400c4402c10040c0a5015000f50750f100203030f058150301c02050300e80010380d50500103008a0300d00001c00301c0f2000c2960085403121100481d92900c070986c4410091040d43e205040795482c00c291078202e40090340081d0200d0300c040702c0030f0009070344410401c07009102e800c8903150700c030685c8600c8003852a44c0e00085042e41c07035140300359140404207401090410090300070804a0654401d220b101c0e1554580341079030405820b182107041c450542c0e94942d60242d1080712281803103004d000140400504010b4200340280595052000640c18038880000e900000e400f2248500c0340010303840060014841c961040f6044406a2645c160700303800742e030208070090032070360b0080c0c0c00e0550410701b80c9580c0690030740d0500103a0018140902d5050140d010941d00503821000a84140100090380d8002107980495009002400c85c1c1c01c1c1c9a030024100340b14 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 420079028 1250 420077778 420077809
    0x5150a2102030c120c10020706090909020a0909050607080109021e1c1b020601141c03110a08030108060601080f060f180a0e0d0503070518011701140117091902 70
    0x2407025082081d80350100d04040302c010700765015071840040906c00da1720790405004800014403000d40400a88846030042410540054034103050b15460342450310035646200000c0d94030340d01260511020302e40c0451164010a0090350031410940403e00300da00707191001c643e09203e07003000b0603030402c001c40d0348802d00a0042d090301d0030445c2802c8000f40f5000ea4501900d504c0c0540168400080c1041c50401904440301c4010821500c0401c1c2654806584050200540810891802c001d156040c1080030342045c6004002054803980342510561030024024000382c100301e07008c024000740d078200e80006600402d0880d25081d800404801043c0800044c02c4440303083c0f01201c0c14480e4040d9143e00604d4070700200e1090300c241501044096940d4841075034100e0014800304000c402410030030051040900d0145840740e0300020310070b00342c400407000780c11034206900758201c100d2656030827014110803c015503210415500d04501c0303a5032503528203054001d5020003021344204541d202c11549540c50f2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 420080278 1250 420079028 420079039
    0xc030e03060910140f040f170408161409060f030c0402040b0a09290307030e0d020c0906030703031202030903120f0703150302060703180803070605150a2102030c 71
    0x10385504015501c0b80d1103103842d03d20300d280105031a200b8481440143c0324924400381490f036030711103540c0c201740040c02401c180c0d494505403000b42c10044054000f000140b003440020036a03990500550010100554403100d07181c8071103140303040c0945507050265031242086916400d00c83d0003d01003824a504841010391052001034081103503030701c1c0006400e41024554410700d441e61103071841d018030b014803100000c0c802079140d042403445900000031940041d40d854003161b119006070700d40d849c100000c0c00040c09078014030002c03412400c1140d0815440b2000710014001c0d40c1c80c540f0003800303500c01210002003180e0000b0000e22107800c10000c9a1030808041c006220602d0321941e080743c059001e940c001c0c0000d00f4070009140d064410310700501641d07001412180307000555941540d56549400061a0048152000003801d02d014800350041c240203440104603072405100c10049800780d2900148a10520381c01884401d9450b525401d07182c10240d1104200d041c03d000180c50f1044803920786a005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 420081528 1250 420080278 420080281
    0xa0e070308070c0e13060203040c030209130303240b0c010b030a031e02010b0906010c06061703070b0903040605040513060506030a0912030902090615161101080112120c030e0306 78
    0x7070500010108180507000780c031085601c031310480785004000c0e00c0124240300c0c03012801e00416550f0b801035070424441c903614280182c1d213501252407038a0840341c6e54940074840305d040c0280f58150140c4005035440c1074128034000a1150781544c50700050040401c08400030a0f1280701c1e1409502c0b40710843c600504440d000219843e0046c1440b03020265111a90805200c4589450050060f1891600002c000b42d0740c07640c0380001114940c403611410744d507264413180002140031a0024146000c40014055541c1c2c91480c10020342c0000c001d4072081d0325a008000c100a41a4403034142c9045c1e0304215000b03241c0321089020f0102070280f58001c280e03c03500c00400e201104820341c0c4200c6c1c1341d40c803c4104003040c0c074142c0c405030100c803007a600194000c0c0c031400028141d0b00d0415002400b0311441c05100703041203404451801000d209a004407001e00030b42940720604d680250000d80100001001101004056aa0f100b6a00090b21a500034081440460802c240c041d134070803180901c6c041c2c01c541c8107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 420082778 1250 420081528 420081533
    0x171014040e1603050d11030315060d090302030306032401090222062003070b010b0a02030d05041a16050403030e0a081915090f0f030512070905130509150a0e0703 71
    0x507070b03209100c00c03143c0303214001d01c21800324041c03484010465070f10005141146d0300c41c98480100b0b030216501c641d0021041001481240e02c03032081d01d041501903070042d912482c003402418a0a01902d18219007050103440850045c1032001c0d0090540e08609409038550009000c0310410002290f00c07103104490030600450141d900004110a041e102d00402d020801e048440c9900c82c80b4807100a40b1518981006220b03090359100200416a440d10441c2c2c44c184500b088601110360680d82105d0400c1900c0c1d510301918460030600b5006200c100d00391401c08a00740d005800b034404d81c4030007800d00442c01c00f403100c40d42e1f0b5282520003c0585100380d039580d035901d00c8200703044661395070700b00c9040c050514010640103141c4030300c04507203500c5500b036100c0d600c254482d004509a250412010042d080048060407000c40e42a64000c40060f20740c410303401d080004001c0c50f004008844400701c0d00d0401000600c2400080440b4405200c202c48544c80d01c40c401c0f410050410000d0401c401e200e040400000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 420084028 1250 420082778 420082813
    0x7080403020d09050d060e03131e170a0b040c0f0e09010e0616051c090b0a1a011706133303050a0314091c03171014040e 53
    0x20880c4654203481c4a501514415202c040d15409025000202c1d481030000051450340420b202140080c1101d00306214508106020025500201c100d506840d4040040f1082401440086c0c852a0301c1d8403004100e980d00310b969000c03100000b501d00340050022806110310241400c000c0c0c40300703010002d83d2685401400c00140b40580e0401d01561804210840400c008100d96001e000d660f50303c03440789410740c9400c50351904403468942c2d400000803c3c0c913079580788521512034164811207001080740741c0200350307004aa05107001114100030401d40541207aa01a00032403a014040b00720305c0c0030b900c5560105454405450a224516141c10204491103408440072140c0401c035100c525a001d084000c04100d0b5615840b0041c1150310640c506000603001c3c0e40307c00a414032400030141403190000000f6010341c00c40880300000c001c1240ca00c0d0500d42d105c3c03200c40208049480260f00780c1440c100509140d6024480c00400c01030b0212181c0e420380e200d401c6442280740c2d0408441024480d0a400603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 420085278 1250 420084028 420084031
    0x10501030b09160609060c11130b030d0302132c090610080309090703020c030c030a05070c1d0403030c1403090616020601080c0409060905100609050a090f0f05010209090708 76
    0x780a0f200e484403d141c0c2c005086001400e4403240d82e10350000c1071a0820036034171402c0d5001c2c00c8030b0728072617501c010889481d03461140224400101021038051111000d050521142d800c0000426004000c00034051020140040407107200d0798141c00c2480100c1360314405154028990500806644240212400001009800703007558503406030b4003c0e52040381e140c1c0ca100d444100d42e04958110000b45241d4040d0303001d000303003000c4003003541d00e01420451b10f90b00759880a42ca40c00840e80100d1440b061003041040d59024203692003002c03905040800090b0403405006200500b01341d00c0c1c040580615124040038508480c222101c25101e00f4015140c980710781045504880300b104030041070380000c0c0f002444504880c0c284016280407440c45090101070102c020703090b80c01036101d40c10800000c404210460341c04241040004402d0700f00744500e07055403030152650a40070300340480d00d400708400d080404403c80c0d1180c07003001d0802c0e80d4030f0000d000e40505401980c1c05001d070800c014030282c015200c01e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 420086528 1250 420085278 420085291
    0x120e0312060f0d0f1209081002031e07020a060b030c040603080d0b01030504030f0305090313030303150504150501032f0414030604030e19030501060f050a091406090408040503010501030b 82
    0x2e030100e8520509000e00004010b01c0902940070003011030010500364420088550803616003420b0140d22001007901d0700e5909085024450307400410440003014451050446000200d00702c2283d0074032190080d80d5900d4850090f190a50300c0411039502d540801aa8040e0180500103104290752410700703001d141c000b036004c0425181007098074105d66209205a40c0710310b5040e11541205407510404a00402004003101110b00c01001082500d0442d6041e00008610a68021640c0c5a00c0b485031910380e82c459028034000d900746144291036040607511502070394000c1c60006980309103050005200c12018003c0c81020b101000c0c074007030300c601030342c02041501c500308142c0881101d00300a040c3c0d41c44080300c019000408090804046260000c041200650b04000c0422001d80b691611421920386034032003200010300314000c20860900c00d13001c4000f8607241c2402c0010143c03020212055240c0240020300c02da4581c0001000c104044040d14007901e40a0000c000d60b684a1400d030708200320644c0c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 420087778 1250 420086528 420086539
    0x30305010f0f1703040b12060f03070f090b0d02060a090302010842030d180e040b010b0c03160c03020f09070c1b1e06090b130501120e031206 62
    0x10600212152004048400100d42164810701d080308061504204a00030040d1380400c1200080034803600d0b000c0d00c4a01c2d21009100c00c40d08182c020081d00c0a0140f6a0b01d0007030704465000c100281600174104200c034103065000c81d80744e205100042d0b0030402c40900a5010300041224610f569000c03240c0000e17a80700b070701d685207283c69495540d0a41484071801118004211218014250807900a40e50080f160b140c240316420000c00000c0c1080c0046103150001006806d401024510320101c0340010140e03e281e100341400c0c19200c1c014010414050420221b1b000103507020454820000c60314035805401d0f904075071401d289031200d1b0090725448240e2140c1e2000c28000410b00e003a0b017481d030280d1b0a0b41c4400100b03480e02c0c0e172013491400341210441c8511200c3c1c540044c59081100c460b03a2500102d02125a04a0405d00040c00b100d00540050100382014044091445500d44540c800d484003400c00d18007049094070440003810301a065201c29000101e03402c1042510350214900400c0b04480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 420089028 1250 420087778 420087781
    0x11806150b0708190909050a0b0108070e1c020d2f010518040504110d0501020409110301050108010e0a150b030720031b031213030906030902010806100e0a060309030305 74
    0x69140540c0140b500160804001304401103003440302802d940d002c442e96040070021140c3c1c0b5400300007154002ca07400c210721501e4900b00b500a60344003810341c1d4401b11504003200c0f12141c580104100c03261010000300500c102007454015036540d000b08425840d40080c503d20312111041020b004a1083e28103103080d02d020b42c07190303000ca6020b070054a04601200244540807041c003001c2001408028006031041100c03a01600c809031110258005000e001d080050380d01da02d81074083c4116812290038000048041c001401980c1c0d001181c6070448615610035075242d150503e028008100403540b40b900d42c8544840050544c1c56100698896130007512101e840c0421200c14960340d1400481c00c81c0c06030010403940c034900c803090855840081c1c00008890030142c041c000b500703584000362a60981e00f0304d4003d0348403c0560041807039001e44034a140074460320030154006021041c000d1310b100d124680c1c1008050403244925107144107141e004010502c415034419004e4014022000142d000a05000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 420090278 1250 420089028 420089039
    0x60f0714010506180a020a140f1c090c030f031e0c0506060301050103080d020a090801110717070308060d0204140c03090106090216030f020a0f06050f090c010807030c0201180615 78
    0x40841c0c00603005413013030809540c2d81d02030f08020f600000000007480032070070602000c40c4e00300300908010700c81003041507611240c1074800f01d00c0a1000101c0c0d0040ea0601c2c04841c001030424900701c086030390280c141c40d904052840d0564566410140741c19000741840f1450714010713400203060704c14034000c0b000d8500d1512000c0034182030b40e80034000903144001c01c1000e00680071803640148450451883c010340b000f6201c840050a480c1000c01c0402d4078000451000b003841800c1001061046104026a240c809280d03000740c54144002c141a214000c6841d0750000d5440f5500702c049502d280151074409450003440150145c0c100340c0b4402000d40c600000429100d860b84202c8100624100c5040c10b049500d9904445400103d4840c81c110302903080c030100081d15480b02c2010a510801c4085014130f00552990340301c0000a140c000e083c1c0c003003642c01d49240d810031102900410702d40340c04a01000301030340985c017400301c4500d0005610182301c00a402e0213190f9200c03515840d504061070541070f81d9003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 420091528 1250 420090278 420090289
    0x601020303160e0d050f01060e10060c11010309051005160c020f13110301080c1503011203030905010608030a020a120f1704150501140a050102160504020306060f0714010506 76
    0x115040c1c0b0465040c407001051440c0151200820358a000b00b80485440755650b9480c2003007001600c00d0542e80d1a000103100c2c0c61540075140d5032040440c0852100e861030301100030801c1e290020054031059602c400048603034801d0304190100c981200446a4008405610300014030040380d40090040c09031402142c014801c10f140c402041e001016041460507540402104800c085851a41c45545040216010003c000514000d1400f407024015200411080c0301d24810700c55080c1c02040ca0410041c00b402c5c1d811110f900000381c1500c2c000543c0007440c5030540c01041c881e0005000d621010030840c54042d8005004005a803258620364020b04d04408242d684064405c07050f008100c501841c03504202e885540140d00600441154208803040c031113000458030b01fa0041021050f600141c44c149081036004a4000d0070280b0003003c4c090f851101040f06001180121441603400001082a80e43c2d510144e0b00140d03603400100d65100480d10380100c4044c00115113142039420100000d00300d1408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 420092778 1250 420091528 420091531
    0x70504050c12090102070c0807080c010305041e02011107090609062c09160b03071d031b040f0204170f07060f11010917040611010e0d08060102030d0906050402090601020303 76
    0x2038040c0e4144080746500a0031942c000b00b141846640c00d00c105000b00389800c035039400502a20000c1c21126003803004150178900d00d0102030741418240424800041c0e00d641d012100c2009020701c10381002605d100403100b0150392844580305109000740460b142d8200e900010440303140c3c000800a1954a00c0044503000c04038642d00710300d030124403860011040740b502069000c404402501c401a600c1c1a481c544a041d81e00300c042e40131400700070405010340148150001c401c44640c0c0c178403503005050002c1d81e1800080861131142e506144004c82a446d45c1d0000c802d60071116000759102c035150b83c0341071041103280c5a608007070302c0386069140884c40f010410100780c03166560703940c440f1140ba01007079904040c80301c0e07200032031f43d40c0d0700310f18001c500f803543c40201100f40c0200c0203903241c2c032b810300041080c081c1c0000302c401645000c0c0500305c01c003030024540c3c0d040142ea043c0400d03d541e4050050342103000d1a902854100c0c04c000c6103c1c10081c0301d81c0070303c0c4518400c80c0c251602e52184001241e40b07020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 420094028 1250 420092778 420092791
    0x60f020109020315062202030109050f09060c09040e030409020c2503020d02060423010810120605070504081209031b010e04050402061b06040c140105041a071a06010207050405 77
    0x31200e18413a403180d4002e122588503002038810f50129943c1c81821400346004c11048502d580c0c0480140024a40c601a5a4222100203030780000c0e410300c140030503143c64003d829250340c010000343c041e50a8466420020070a004101a00d4540383d982c0c01000c0650312030b41110080e070282d0080c0d01c80380c4a110601c04a560381440048001c0303030950f421b1082d0710b2031850080c2d03480321052000146c1100861400c45003942d60303161b85c001202030000050703c5150007a02d100e94080c3c07d43c01c24050319003546c4545a000d500302c0404a0305031240c0c0f0302901c040c0304941001a15000c0d1032180504a01400d00618120f08260115100c0c100d1012189032540302e0f40c861640000c6c004070300c1211600d4540c00ca550014001070149142c0808500c1d003010342070860462680a400c031104010500c0710303001c4034200426110b4401180007858030002443c5100d90b004015841d1804881004c40c212110207442c4095401054010031003a62003400143d02002c6030714600600c206440807030a801d0030f0144600408 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 420095278 1250 420094028 420094033
    0x50906010302030106120906090609060c090b09011d041d06010810061202130627050c07050a0209090a080319050a0e03041a09130510170703030309051c0306060f0201090203 76
    0x200390300e146d009403403100c0307050340c10307030f40382c0c0c2d40080411014405c3c56110391245400007484242c1c2035014088442641c4480241a014081c403d01039800c200d0b202a580315182e82810320000800018000703141440d00990481000342d0342d840040700005030306058030010402c460b05035064591800a0b500d49000f043c082c407147c0f00b071400040c20316900029000c0d2a44e400030405945401e160029440c0c0000d001c1c81f4080505045226140d01e8403038160850900e294a82c03a0400640341c41d0703a22800220000d005034004000541c600c0410f0151004a81d4001d409a81d02e0030b11801840e00c1801d510f4940e4030051500000c01d203980340b50300c58881c020040e00091402e02d45802125001c1a0f0320301d40d000181101040308000d00d030303205502d00d21550501840080c0500307207146680001000394003c500c240c800114444441080068801c080380c0e854a4041900b03c0325203006801c05881030309101003d4100020b1003801ea405400000a0341c43d20364400c500300040320403c074288d5411102c040d4258 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 420096528 1250 420095278 420095297
    0x70c080f030903150a0e06251403040201141e03190902030601091a0a08030a021c0e0607030e04051602010c0c0c0b09010c020a0303080910060b1b010e01090c050906010302030106 78
    0xd0010342984d540710142d007500046001003009114244036003194900250703003955036040071041c0002184090640617103403001d45030020b1040c030051440042d0010b81400340c0980442458007000d0101d407205942c100070809203611990181c5615082175501845120030180c09000d0849644940ba0301160010002d01040e440e0030340349401001048640c4c1d02e5034080c2205840640c0340e002e40c02d80140b40d190000d69a41000d024028100012058800300b41c10555400340b134181d500c808014881c2c10103d5400740d0369105454161640408505800e4000e4109000c004402101031801203054045400034800c81010440c04c44041d02140b000600d00c1240e84000d2240c0c1154101420034548181030440301d030741303981e000200743d0ae5a543c001c40006504804101843c5014440040510604001072001301c0c01d2108014990003881780c18814101480040c0c0103c020940048001c1d240000003001420b803182070124810310785000c1e850041d1098004110154030900c201e82c101c5106a0340c0078400c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 420097778 1250 420096528 420096553
    0x3070311012306040608030a1d0112060b091824030a0209010b07052b0503070306090f0b01081e040b04050a02040f06050108070e060301062102070c080f030903 70
    0x11480d400e1800c5045650390780d0015a40d0310010901c00e849402d0100892542c64080d003004151261a00204490381003070284410054001140010b0810442c1d29a0703c00149030b40100e84c524144080380c650307107041140001e8242110402414010000c0d035213800b00f20f211031228110075400b52040c40c0d07560103008170381d0440c1c51102000e80407520300500f038520040a0b40c001458502c0c0c01e800a21021900283c0b03907080050400c030104070915040142c0e144410b160a016650b0405104000c0611800100145829110342d1107540500f09814080190203c4034980f000108110320585000c9003889000c6402c1090301070250b5030400c103031280f00303003141d5895544104410015004455a10a0048000060b90366001d00d5040c09200040002e10615080006002c8480038000c1014004400c6003140d0b10386618003124150fa40b61300384240c2e058180206504107040078016004454170105140080103214015142250780311030449115000c10110141c0728840d864407940e141c2d200c0606e2100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 420099028 1250 420097778 420097787
    0x601060912110409050f0f011a010c051024090203061e0d05030f181017060102070512070603050f10030204110712110607050f030c130807120c0b07020102030703 71
    0x140610440d40200707400410320200f000d40b1800382c2c088840d50040244060b40e810100518401c442c2c0380c0c4024480c8c01d9201110b030031602a0854294100f041d84a50070382844420411404d078401091410024030f855414000c0c09501c804007004000d107094500046c19038160b000703590290000400030445001c04129062070220103090b6903800880070f0a110f0b01203070003800030700118405d0581e0240d40e540d600f201072040c048184c410600c40c0c90404e40615403241d002d034a0b8a00e10142c8900502951034820040c0e103018410341c0826402503403124071640c51140412541c2c102e0f01c1030f80307050020f0b07180c0b00c000c465810b10441d1406505140845c0800251415411204006481400072454011303184c58101a44c840281c685020400c2500b04c0c0a096000700000359000c521403030114144040c90150300013034400075060302003000010910b880200c607200712010003001202c040716200d940e91032000d941c0b002445002e032600d0041100000d01c1d00d41c40801c8444444d4142d019514140499800b0345 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 420100278 1250 420099028 420099059
    0x2130c0909090f020d0b040c051c0b100f0b0c0c030a03050f092103130b0a0c020f0a080717100615051804020406020a060506040b0a030b13050d0f1106010609 69
    0x5442c1d440c0f101c0c4800145e102c1c81c4001d50b034107014000001c0d0b41d217880d0a01034181745c0542e001134080c03480c940c0080749848200185048541e401804104036403030b1601140442d04d0141c010950030150b05000181d0400c03000e00400c00c0b038644c0000c0e100c1208000c0100f540b02c5224500240100e03008000510085c103104000704038071140106864442041e2104802d007040007101240d840e13134400a200785040c48911014070082010032105440c0c50413061004044150741c0c0350085c090070001859003043d07616565408081c02d110022551010350b2400400441c46001188140078007858803c204820440c0c0241400e6031001500e0305070314440754604444a078420b07001d011180c403460905882c66503a80c0020710040c1110b600902c092101d03420701c0c800b00c1d00040c20322441070740703494015866516203501040880383c0080c081d6200b03548185040049041060000b0081c2c000e04640d8555140c0001603824500e640c8ea0700c001490f000110300a170744031001c1c003441d000301c0c1200740c082012403c2d41d0f1210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 420101528 1250 420100278 420100283
    0xe100614040803070c23060f090a090f020306151306050309011517011505100e0315010e011701020310091d011a0103110f03070f0e030d020a02130c090909 68
    0x5600d0203540740100342c19a0441d5808845408615401b04042903102c65201160300340d01201c2e00e0182c00001c0001c11501c602e1312051031412002c5540c0b45e542c0c1e00c4180c034800410001c0d00510041c180c00e5880301c025441121114422505000007011901005040d03030f040a01103031a1707820381030401d4000c4c7c0d030f81d80004217012919034032400042e05140824215070001c080d070160f11350290341800105401e4a13142545080311100c18101004650307503d15003001d400c03406044c42440000f031880400e003011400c6050600602803540001f4900e4060705116040303810030800c1301205013042501e14213030306c002c0d5203c4580c0f0040290030f0107510078039481a0500c0d240d0b5080c2d508a101550000b90955002000b09911062101718507030565070580a9018200d1210002524041d85101c0340c01c01804041c0c1958200802c01c2108100b00e402003c4000a0301401002c403200c40b202590025a9000410805c0b4001c0c041c50700480c000c00014001c440444100361504003d590078420b00900600219600303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 420102778 1250 420101528 420101567
    0xf140108102714070b0903031e04120b010302030105060402030408090907230d0608070303090b092e1101150e0921031e040b01050607060b030d180e1006 67
    0x10050000c802c1c2800b20981e0344924404030844081d20303820750a19402d41d2000080310000c006003002c2e0359012003141d040c0c0d07003060100741e02c0740d402103201d507442c2c000c2d608680c400880c0310b800842400782c150402812a40700314024442c03030b40d94a040c402a80026100240102c4040c84114424a88125001d80c440d15500e0065919500309508007910500a0804101244000f4000b051401d0600801c005080c2d080000d028907444c641c1d0003040710040344155840042c001c11a440283d0340c441600900690208030549105244918085202c0010f041c50b03010410507208043d0501042c002c0c8031003000c440700080c5210385400c240c001041c0d001402400e003405948041d0a014140001c070540855074401750a0f00c1c1c0c80c04a201c010f20290740580c02502c0b030003520800c0300189401071564107680042d1100703511601c0714607064000d4414121802d516001e00030501c041ca941c04020303184149100f03046403030015621604a0500341e401c1d22900c1c800c80300c400c0c080c003540b4062100100b021590202c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 420104028 1250 420102778 420102821
    0x1501020c040c050406080609042402070206070605070810140f010201090b0a0504121d01050f0d092402161113110406030608030c0a0210120f0f14010810 67
    0x24101c0782c20001c0c0c1404244080390600c2001d038040c0e5040e0740980151030f07480ca40c0c14180c80f0300c91802c0210f04440e180c522004811003d03051aa0140d5020b540e0203003402e0b840d0301032403400001400046034030900044410000401150a00550b00704580041d0052108407140301d0a002001043c102601d055649642e81c3c40c00048600041130f11880203841c00081500f85442c0055588006012040402c01c040e010012240580290090510000d0074100da941582e14175150103800790460039a40341c0d29040300701d414810000e0b1203c4040c4c40f40a45004900721003144501240150404100c8010b40081c05400081c1003c48450181f01e0040601e02e080059060746d0082d1501800c10030440c481c04903041240f0758040c05094040d001c03134006141840000780009589000720900130744240a0002a4071031240241c000708174240081d1400e005803000c003003081d008be101086850030b105d444c04100001048200101074141c4101001400424a6686408010b0b2400348090344036100b001c00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 420105278 1250 420104028 420104053
    0x706090b07020615010e180103050a11224b15090b0d050714030c061801120f020f090a120b0a091104060816090b0607021302090319062003150102 64
    0x2041d10323000317601c00c100030241d500091400103840003541040321b01881000c511004071a02d440200703408078403504000030b0911546100c1400f40e188907062400707003c0c000520280e81007480500c80da04282c0f0008400c000c1503012140c0c000712801e0001c3c0001c181c0c41d1139030910070303240342c0d421918400300000c0002d20880515128503080411079031106074412944901006182001d100c2c01c4922202169004c0c00d007500100840c44a02030080018104914034071801444100ec3d03001c4c40e4503003000700046440d40800040e940d15a80920302c1c06220705205c680010380f40500c0619558140c0e0b0100722607131030f5203c0201e4075010305800482200c4291640e90726089079101c1d82b203144010401003000f05030745252905c0004c0c03018a542c1000101078104081440c10fa115981100e4050b0b40c1a82c41005100c0c448010400901a1418a550501810903404001070261500300219400344004106001c2081181c068080180c004206e1292b028000a0101046008070005a01060048d590a141c141c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 420106528 1250 420105278 420105319
    0xc040f29040b0703020d14030a0c0c15202107020c18070305090d23071421090a0312112a010c0f0204050601140706090b07020615010e 59
    0x140c220b403007140d001003220403d1540c10400c45648098030305240e1070b856054012010035110003483c0c50001c0c4e8891030315140080c0b0500c244540320780c0204420702034883c140c12a00142040300c0b00c00305850a045550483c507455001100c400940c050320744001c00004690070340c07000b40014036a1041d40030301040882c181d1030705c5000403441242e4030030f051014038000c40b01804540000d00103c596911120301c4420690308031110900c80720744100001c01180e80422910b401b88142c500003002e8984403015004440380c00120f4940000c45040020846107002c03416248030b000b04449036502c883d14039070400c0459102d80081c845c040c014545440c8076010031685c24038148e0344800780c0c0c00128081c9130f250304032162581c407541a41000d1a00c03484c031b001603444207032440c092100c2c040c1c0318965480100d0b103140c0c050b10380350040d0a0801c08550703c9040d242080ca000380100c0c0782c155035130b10901c070019410510100d400e910558030504d5070241200d40c00011035100c1e600706c4072540c0140310f21440400007507a8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 420107778 1250 420106528 420106537
    0x60f041107060c0905040608030a090308031003050114090f0a0f020906040222030201030c020a05100518070e040b160203120712020c102003010b070f08071401050c040f29 75
    0x140c490ba0191407170402844111111584103905942052058022183d030241e280742c00c69400c005980e469445a62100000300181c1d4001032140d8a4080666140124400003607c0341d8041d80503140c070368003411003c07526000c40b00b40040401098110500040c40d00e04459900060b0103072005050103680340c0044d01180304001c3c418064414107a0400071503138140244c1800c03540520181c501007680c0d0390b070566070b4070110303c5042c040c68a42002466512001461121a006d5002200d1348203035944032a08912070251030540b000d804160004e00502031240034010b00d030344568015450880c0c0c60004007034061015143e0420842400b2a056003245079001404503042200302500762519141010021a40074141c070036400d00d40c50603104041c60380c0005076411515041000d9940ea1502c0c500a00081001d410060406901140b01c00c1803003c2007000300040c1131600001c000940340d00d0041002409588212a0350f00c00461061000c0b01c801480030804c450702c160341d20400540005010982d811 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 420109028 1250 420107778 420107801
    0x303031918051f061d150607080a110303061806040615020c0306241002010b2707030b0609060d0b0a082802030a020108060f040e03040501030b0405060f04110706 71
    0x500083c00c200030b040014100315260007402004641c1c5040c5154500c4828401d10f08982d54090380018201b02d40307109254480315000f01600c1c1d0320140e502d0428142d4100808540002d5001260690294800000c49000398001003a000f100f80360007020004c41c0301e00401464201d611403c0008544682030030120100104c5d401a201824541051514001c0c0c02481d1406000072101a8541d42d4420706001c0205d03501940e9115809504150580c0500401002c0c2c039000344280c0c0d00007240c0e05070741d0344003000800d0401a50070f0a480e418130490035541441031459010f007007005015168904040141500085a00040303038283d02e860000d17060609646c480441a00b003010402c0e14040c04958804d04d24240d21481159184c95401281d500c0403a6000207040c4112140443d41d641c2d00c03201d4100043e500208203004820010b2201c580301d41052141c1804a401c060b490348141c9401d015561040b10040e01c2d0382c0401040e001000041c158000071010032448c01c10252010801d14050a4041031303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 420110278 1250 420109028 420109033
    0x4050906450103020a0509090f030a0518010305040201080a1a0d05100b090405061603020d05040c030b0601020c010815040e060a02130b030403050a120b120a0507050a05030303191805 80
    0x1030303015909001480700c42145544004062006000681d501140d01e0160b940c150340c51421030395040780652900c229110311007214072010a14640f20781e8040c005207500104c412003c1440d0801c0d8006505807081524024082000003000030545440c40e8414103074458043c2020417039102650102d42c89143d5140151a207400c410101c2d040c04c011400344c404500c80540e04070641707213000d8807001c3d00e50f4000351508a44a2225440d000d155109806440d50345104c1d840c200010b0810707140012000e0380c40d2000710b6030b4100020000d005036002195010f80d450068503050800da03994502c6200c11404416003a43c416a83c2e0f90194248404000c2c0901c07818126000583d140350350510540d8000c0254804a50f0000070006c0000081d0702c8416981c0010413418641c140140000115000d040b107040d040e42c001c00b00c03900030b200c541d80000f9520407680c0280c0684440580312400c0c024020003070300a80c0c0c0c1540c410400301d403000600708000c2c0981d00d203030741c070000c0e5811300d04c1c0c1e0045008030413100070b0316140d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 420111528 1250 420110278 420110359
    0x61722020127050906090105060a0e1f020c130507020a0303111306050304050c031f020c0a080c070f171c0c0813260d0c030908060106170109020403050304050906 71
    0x2d0130309514540d003010341114140d40303540c034000010354a03200c3c24402004100680149904039191030540c3d0f921010032010982800241d050300a5a480a1882e018402c50102011207866085445140d0080c0380540c0035000c1c0c880307030352000d0b0040e19414811201220302080a5621440c4a040c0b0030054811683c580782e481c203140c2401032900c00a003901078402d811181800038030a54500c40c00c01d2011104402585030080e1412203410300703448107805000c0010014011000e68000309004003922001110031161130780b1840108a40080e03800c0a9106520002c01440002c182951038440b441e003518042c030142071690340715030301508078255011142c2103810040c0079001880c00c1c88103860f1401111401003209003a00140d6a021140e8000203108291f41c0f01d074207062280380302c5805004014203c0c1c410b949e45010091410041400c0e40741600720000011a40c1d1003a802210202d98011004600781801c240030002d007040081d0142d948a041c500c56040c0315000b100c48041002520381501402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 420112778 1250 420111528 420111539
    0x6030309080606010807120216080a02071a03041403220510080613020a090305030313140a08030408090d1a0f0703290402120f01061722020127 63
    0x4224098101c144290041d07410001c1c41d9070f0142d01c40c0e40c4110b007482c2c2001203081100c515802803289400509280c11010032079020f10103075200600100c6a6642150011a6190080e91002c150010580c5800e9401c001090204041d0000381145003c110180c0c0d113071680c461510002c0e407120381c0d440c005d0903201d000e0411052030a5014603100603a20308100c041382c0780102c009004881c403000e5100d81c0d242c0c0482d103011558462080c0d00055980001183e07640d0901da4050341c4c5201d84403200701ca102e460f40c0201e0040120100b4585043d603444072445046485590f01c55200f908441d201d00c1d00401c01120b01408500e428148803249144068003c4d02804d0002d50424a41d400628107002d050410f14860f00c20080c5070301005c440d09144000c19505030b983c000050180c4140c001c64032f1250070f0ba4042c4200d103035040340c009041f514070f521020b00d5504054004801e8413000c0350309a404001c0804461015000d500e040300392284140341c002c605241004120301d203103410381e5221a2860444c14103011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 420114028 1250 420112778 420112787
    0x60503070e06240703031a30012d110714010605010f09050d1104140a06330c050f0708060903070210050a0c06050a05070e090f0106050a02030715060303 67
    0x540c00b54140f030383e06191400c002c0101d8510409000030101996000c0341c10039040a41800505094010500700206415011880300300042e841c0080204004070b640c804060414415402c000c5070421100b00390070580c0d000d00000e5101c008106460640311078a150003600c0d00c40c01803941c1072203101c003e240c0250481c159804c41341d03550000780c140300402010100300c075005040d03001203550844650140028528101c0001d0001001c210307081410620303440c8216920322400e62092000d01410044280e0310100c1c20780c01704117a05900f51004510120f02c190150564448070001032030f0616440302e940716078501d850701c28000ca070000b1642000c03000f40181d540034807809411507141402181800c2c0660001a03141c80c4081d00c01c014481d000031149515800740e00707080301c1580c0001c01080381340751040445d00508030841783d500005019445614561401141c60340c05000d50490003629a03003008030a907072992094041c0c50540c0f000f031240394001000c80084a50014840707001090b000d00e50324000c0c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 420115278 1250 420114028 420114049
    0x60e060906040302060a0e010209060409060e10030807020f04090f050303011a0415030e0a14010506130510090509011d07150504240c060f060f050307030b0408070501060503070e06 79
    0xe003500454148400f195000444642000b038a04002030070444003050140203115555065130080000f0400103010083c6034003510485620512030006551040c03200d500c1c0740a00d001c0101001c40c28440b200c0035003444940c02c03d01c100c0103000042c81142c40d0722000000364070803004442940c400401030101c64911500798aa030350144182074106410452601980300e01880c943c010035942e84c9010510510400c8082c1c00181c10401002840b07100c0c0e04014043e220880e2030600031a5244008521301e0030911500d4440c241403a00000201d0500611b1005480c015141e4441036491300d50900b142d03017009514454400d102d10003032008924111038454101021003004041c000e003400100451103008e5034031000000d01d462072000c12450420107982c2205000e00141500e850400c1300054040340d5404401540c1d0904110b11001e40e8a02c105940d0340482e0000409003600b00000c40c0c00511048003400ba064411000820419181c5022a00e0000d49078807803d2410000d2080c00014284540240b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 420116528 1250 420115278 420115291
    0x152003181c02010503040f060b120d08010e090a0b0a020912060415110a0813060f1406030c010f0305130f05060115050315010c030909020d150b1608180409060e06 71
    0x28401c01860300041c04601000340040c0034035103c1c020381800c1203140d9100b200c2c10000100030320040d01031081d00340c1d070b01c01d0b0640905010030300362000411498603070b10411303114414180042940c047c0b01e5880030b01c0c0c2c41000c1e144000040d02800043c50030340c1d412240402ea42d200718001d06007071510307040c02c000340140b000341180c046151101660950648070200c4040341204e00749085a0b841e1081e004a030550340520162900e8904450720f5a00345640c2c10140555680481003449500c0303900405448441c40324000f400306c1c0d0040d4560385140d0080c0c120a0340b040100f4040300454030383e611035123418000701c202150260408801400f416940e04580740c00c8400ca450709601303614141840103030640c4c2d1000b5646c1071110900c01d00c403c00d4803170380c401005071000d01021b40d100c1d16a400c241001d0042200554464110b4860110780450380c641030b11451059000900b000e050180c980d911294011009180200c0500d0135501c11500c0c0d90051050440c845d503800101c0304100c000642c103001000c1d108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 420117778 1250 420116528 420116569
    0x30709050a0f03032f0d17060d080c071206091a0705030126070806011d010f03030e0f03100507021e1005040201120c021e030703120231030b0f0115200318 68
    0x501065481d800f2107915600d0380410740e60390300d000c0c54442f185000d205074014140d1503040c072507240c10483c1c00c0e084400e4452003030030703161141c2d20345682d951680c00e012602000011014001001000500e002000040042c0300010003800c0a6090150803c0c409070000003807030740001c0040249881c80e20030b00d11362000c01a20a005541400b41600c0100380d50321003c0c1c10885500f00302038166490720814841040003c08480c48050f4801c00d07c009408200d40e2800035002e1040c09622a051b600c10070320100c4c0281014118007040da04144d07004185c054820780c10800f01c1303030718418440001c0c410000719680d0f9400405011848180c07480d502c0c01c164501100ca80c10910681c00020303000341c04c18035070084900f0050b0711a10341ea83c0c80d800241109404e601001c15080120400c02030804c02c0b002964061800842607640d00407015901c0403080c801c184025a162a8500555101d00c6a000c501240310740d003c051030075a0b15030308ac590b410010f040710360605151501c0c0300a1071b240d01d00100e1600031150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 420119028 1250 420117778 420117781
    0x200c0706050408100f0605060c0f1b01080a0e120f03060a0b0403081204031413050f0306040b0f0c1908070e0406081e12040b030709050a0f03032f0d17 66
    0x40303482d100c0902c8110340d6070040d01e075500943e1794140b40d00810f0151001170030341a01d644544540315987c8241c1e00280c00c7c18010400c20700c5c4144010000d44d64405010b071281107080d03c1d4031840304000d100b503554160321f5000d02e00d03011040c0c50340040104603050442e182c1d030b80c0300e0030000c081042c1184554094a62a0070070001000045e4003602030350500d403003007013088400d80c1d5281003e031840b51b40e00c03109901d500c40025250302050303080031129050348d0b0103450b902d0414034000103059642038140c401070300306a20100040d0510200d0100c140c0d0240306107030440d0520103080240000b440c1d4909515000c9034100c0100302c034890b400711800c80300c20000c4805001c1d45280408164503100c003441d040700d4248242d03420a5940e030080000c4901200c040580da641c807685c9039280320326500140c0e1440e00055801c0c0b00000d0518113558080241c40130340215824036480c694060711103034880e0440800000d18604421071114020300350152480d41e200c081c01002041820085c5100480041c0030814801d010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 420120278 1250 420119028 420119039
    0x717060a06080c0c07081002070314091f0513260619090201090b0703030c1b0519060e0a03050910020303011a090619030911030c010206060f0103200c07060504 70
    0x1481207030040383d80d41c082941c0380040d0f10b40c44d00304205600710b010b65124810841c43c9601d480c0d0300426420340203540e54022141d100b801aa9140300300d005240d0b102c840303214401400d480203400c0c3c1c01128a641070080c604524201003040d800100c0d4421510003052041c0000452404549069031004980c041d203118904500c010700c00d070840c5000f080190355285a00b80071a4000c0c03010a02600161450b243c4131a4580340040140098170030050001344c400340321094815031051110704480d0311002614800060103048858110b5460050f207110386ca60240b0041203000b03200f041281e070301075941c4541d9000340390103000d1691500d0b12203400715801040108980500380760340c0200d0211500145030f0750340000c000a07455014010340049400c000b045090005c40e05079000c610a584500e901d0302c8605400004c160315040c82c145503a002da0082c6c0005452890185188101220705042c00102c01001d00d10060851201c1682c00b00c030800c002618590031481005503d00404091130290318050419 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 420121528 1250 420120278 420120287
    0x70c050601090507090e010b0406090611030304030c0206092707230c0a05070602010b19050607020f1203070303020c070e130b1929010f05090d050c03060717060a06 72
    0x5110351550107030f4a07008075020600c25282040184100d4203000c415507100d103c1c6003241e602a11601010504502c00011043e02803008140c0615001000c1d50650303580f51404d665442c0c444404a03030008003004501100d0b521101e4840c4000f00c034020300b080340e1030451401e030896500904042d00344024844050364051041c020802d01603454100c89850305103a4804520307040c9540002000c0740500080890020f5056200f18458001202c040f10131031071401c003040703900c5c14900401703800c06000c019030405401e080c1d900da030715098040c20070388281d0f840000440c119000540c0440010b0740004808400d0740341041544050604c003000100541000c01452000003070544c001044002041c0000d00143c00641ea00e850b016244117007400480340104030380c401e0307120401210780f0f0242000889582c651080c40011402c10341034480514003040c000400411120207441114a48251b501c048507580741444454000d040c0c0342c0310a200d1550128030f208002500420700e42c0607407481d01d41040400ea20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 420122778 1250 420121528 420121531
    0x1060e15130b100810120c060c0318081005010f12151b170a05190e030405060703030203060a12030210181403041703090f0126010b070308070c0506 65
    0x44801d00036480c040501031000c0e11900c1441680981071040d00680c2c10b0700801e0151060604280d03007110030b501e8410354101c0d011044805820780219940500c211402441c500c00014060304041d440f41c1c608107007031405541e240d080703c030349604a0b403a0a81c000055000d403c0c00b4119111a018200d42000070640341e1050030040a00403151402c0e10315031601e03d59200c205001002d03c80000400b044c4076016212010403e03001c1c55550140c000601540c805101e40340c044d20070b482e401084107111b40c1540c03000e400000d5000302140802c0200041660b900d400411100e07100391401340c0c603481c00d0320411030b000f502d81d17101e01c8c119030045641c0c6002036404100710405180ca1030001a0f509c8100b401d04116003455007009041e2801d041c015030b01d294000010b40210f40c11240040850a82c0e420000c0e100d002d0800c995811201c07280a81c0055030050b00030f0044440200500e040c000c01050254045e580f0030b90140712802c100180c8907050503071000c40b40b51b114034141407104041c07000d6610340b47d94000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 420124028 1250 420122778 420122821
    0x606020d1d010324060f08070807021b0a170c0117090309130b180f0709060c0b0c12310206031303030e01090602280c08180604030f0501060e 62
    0x1902d44029040c0d07110400300d55030070803c000114161644550002d0b00485070f52040782c6c045a101e00020784581c5c03040050300d1207040140d01a2980c60100900c496407090b8010b54954421040003000c5180250b0f00c0010004c172100d54001c00f0300c5c40310343c00050080c40d40340031743d4815800d00c4010480d403040c0000440703603500015116071041c5161300316000e0081c03100a03840c5910015048062305044600d2004501659003d450b5040d07680303032168184da03424560321513140494461982440801d260420703950f40200102c000526010312038002d11070074441250544040440401031b50844203049440200d15100c2d500072000c10812500007030740b6400010140d00080020904500826109401c120000d0126100902084100c0e2511030003942003031004003041614410795140e032400b010205240c80e0490b0315884040301d80c40c1c40d105c50130341c4072086403003448060720709034025615600300810086018019500b0024140c0c6889070a442060f840450303818804014401c464003410b070b03048207900c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 420125278 1250 420124028 420124031
    0xd05030405010908030a09030e030106050a0506030907030c0e0f0a060b0304060b040b03030307050c190201050a05030406060b130602010507030c1b02190b0702090a090809090c0712030606020d1d0103 87
    0x240c840c03400c1405015a5030000301040c2c070120a0026120540d004103000da4882c0c0c071001080c170480420f01d4225016481459840050300303100f00440d0525000841d084100c01c8180c858190722030702c442e0400b02241e840a41904002c0c3d0030442c9040e0340201071500030000020600685241841151082c080a00081d0169650b42c5194009544680c024200d07440c0280550f034482c0341951011386185c0281441000d240203480401251844207504111011781c141c550a0a03d540b1510455061300010005c1b41d145a071410003050304440c1c44098040003183c00da1034540b80e030030320000032700b0b50b000035203090207160070102c5100d4802d030003980c0c1c2c2000500c0700c036958800c0074240c00042d00070b000c940042d1a003407070310080110314600d400e401012007a000352180b01c1241c4134800683d0403550880c0015010007024029070600c5d01d45102d115400c0303c1161030013420035485407180800900d01d40407450200395a44403c010b119018425100c10700c000b410805096238401b100b000e100c2c0301d4020114100f5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 420126528 1250 420125278 420125281
    0x4020a11160833100f0603140a05040507180c110a1208070302120c09010e0307180b0d021206071812140f0d05070201030605091312121503170307020d0503 68
    0x80e5030800082940da80354420403150620b801301c0a2219101d0050644e00c801e03001740811907500a028490751343e4420011380e03801d641d0302089400240405442181c49000d810740000d461a07a9484e1b80001c1150750000240030140e200780a481600034445503103680e00802e100402054070f07110000c00784222814144034075900c6660031802889070485060a600926007840500103510024040140b02070300e5100400b0a030000301039603070080340700307410130340c0301904103100d5902c8950400000c6460152040075040030f142d000400003040c0c1e40e09050540c0c0080d0801200680c042500290000303d01200c100716403e000d034107030b40b074460300b40054510b201c80c13081b07543c0100c0200104d480f000c441c4001ea03003010240043c001c2499004840680c0003e0a152001c909807600070880c501a00742100c510800340f40303e03568201c2078200b44185109020f041e601c01080c0c107999015944d007848901062040503829481c08615100310504489030811082c010044459000618110840401e0509075100d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 420127778 1250 420126528 420126583
    0x9010504090831030f02040c08010e0c0703021009030507060b0901060203090105032d07030b150901030e0705060d2f0306120708030a09080c1f030b0f04020a111608 72
    0x2603145601d40d12403590050f0b00d002052010017400862840d10840307080c442030711410411030b8039820a0003041c4501802c100803405000c507020080c142d042c403900580d0f060b110507040c41800c84240c0e440943c04a075001480204125080c402c1d01d4001780129503100c071950404d230000356a030040d441d20b61b052000c000f000c1541c5501c5a10070105000c40280c0342d0141085141c0541034092056440102190812502001c2c074644010b540c8500448980c04504180d607180044001c0d0401c1c104d401114000d001d408901621400d006190107200c0000103d500c2c1700100c011039401e605030b40d81908494030802c82003e828006411a034000d0011186d0703402d0380c42c0085460342482c1d6103503c865005d01c030019800e85803503006000c281c11540a04203443c000e094400031301c100303030000c003203a080d542c4c0c3d4040c05005114001d911969014402520900390481100082412603010017004000b10380059140c58005030100550074468141402c50340d4000c0c035140741c440c3d44101c1e4031402d11100c2d01c02c802c400c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 420129028 1250 420127778 420127837
    0x70f05010e010b09160e01050d0b0a0b1804060b0304170408030a09030309060206040c03240603060603020a0f080c090c19090515040e2a0301060509090105040908 71
    0x1001500400204800c0641d0300040340249441440580180b0300100000c089584d0103500c0569903e00c0e0b25440001d040c940c00440d900d03402010313600500755580c0c40101554486528083c050901c050005a890002e51150401803030005400da01c228103106042c480395140c1400e136500258000c1500400c011110354103116800b580d08003811603c4040342e02061150b016042100320303130003521095030f030301d8991204a807204800c66001e05640c0c4620002c00004488100003c03140e01c000342402e2194079822050816a0f41c10740c001d960741030b25640c0500c00d5141480900b4020f00003421408151071800d882da94580d840240690f2045e1418000180346250f07501c101c3d0380d505108010700458041422000e003c0b28158000e090151908800c1c032459507461104941c207032021002076101581d25908042d03050031107801a00ca1001120400320804031109000c7d601820407510fa00d07803149440810310101c030070164081032096051220000c04668034801b00d5580d5405004c15041024a203000790f038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 420130278 1250 420129028 420129053
    0x6041707031704050f010302032211060a0801030611070317060f06030f04030e040e0a170c03070825020d020d060b030313091a15032d0919110607 64
    0x1c00003081442d00c0d03030110030758500410556904070b800148982010b0011400c80c04221080e80c0440c401c0b00c2c1107408802c004080c802080d01c68050580c9401d10340740800c40c1c9400030300711003020540c100d00503c01c0101e14090807000c0c0702c032148205c0c01c001440c0c41c0201440705c0e248423940d03110f01c900045209902c0d03424406000c6039019140c15900d0503d01c9801810307001c101c0d016400102500c400100d145040d005140f4103040203001021300b0007481d00e402000c2d02005000540030742003000021148031042c009018518000c101003030b26040c0d80c0400c000382142d0354142d4200741000c4182070380143c0d904405808450340680310038071404024a000340003081c011841075450311001c00c6030200840c0e010078903025601c041405000304a000c0201702207d112035905c065002212121640c0a0590b80014590144032088d00c207810551000382c60060900512282084000c03400401c5443c06040001c051000180c7c9920400c1c0c619540385c0101007101c08110a200e42c90010f240c0f01880103400094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 420131528 1250 420130278 420130283
    0x20c0303041202100201060308041503090b040f02010f020703122708030d061403060a09051504050d0917060c0a0c14010c08100305100506130c08070207090b0604170703 74
    0x8907501e40e11900790982100c00c05104a1007148041c0c01511964030600415080300d61042005080c94142480102d44583d0250761038101a1341e40e1603040860341c140030b101d02607402502c465001c084c00e4000105040000700048043d540a194104001060700389401200c3c8a00d142440d03035504010b62400710103018503801c02900d104143c0100d0724210200041c003824039660810400156503002c50800500320540e1164141c104e00005000842c89400c0340f000c1c541301e0700a68524401c0e00040340c6000710300f0b5805a600303a00c507001180c003250308140310002500084a41c100c040a040d810640d030341000401d9000b0040c000b060074070700d80e80139100100419034800f5021040f894045030841c0200b036036000b0400003c450001103000d54141c800400d041d40d0b0030201a107108405520600d0192201414071500a0141c840c0f80e039a0031a280b00e915489401592a90281c2c01c02d010000d2600340c080e04000d585915001e070b1031031241e45030011602118001020f000c3d2100c0007003a194204002903001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 420132778 1250 420131528 420131533
    0x30703110c0607020601050307210503160f020f2d0f0a092415030203070504030c06030e0609062a12010e1e06180406060b2b1104030210020c03 63
    0x1040d40c0740c5000c20258402c914030750032101e41ba80d0320010103645110701c0c4240110302d0310891401a00381c00fa4802c4814031400740044925000b181c611044442048001c02d40d07821394403003082800c61608240303610980c1d40490f0318081110440c11900c020303203031080300d80ca003880b403907401c041c4961a501294840c203107008001d60f90700f40d5030341500300c00f414401c3d500c88002d0744020301c024003003101207003404195584e041c00801d80340f4000c83c0580080d07201404001c1407120500001002403c0309001001928090350049104100c00710b0031803412030003802d2403605d40c0080c0b00300860203107084201d104061505280a154100000000c1c41c684184640300105d0400700b000400c0c045502031446000c0c0701e801c0d403505401804140390500302f0390305a490070703030003008803e054420350081c2c00c0d4aa001030017054009081645ca50b0b1081c2d03d940aa035020b04441c0d0a01c08e0140c016180a089424004070148140f14504002071514814425400b0081c4101d044082da4034034244200300d80004984003a08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 420134028 1250 420132778 420132787
    0x15120e120f0c06091504080a020c0a090b031b090705071b08061602011103010e0a1b0806040e0a020307170f010509060a0c02031309180611120c190503070311 69
    0x880c00750300d5000710780006192080801066801400003040004c91181c000e04098540740c60351040c0300790b40148041c40441c0300d50303a0b0010561391120100c0f4001c00d203585000503160240b1050508003129802c14a40304040c04940c14813039220043d07020b0340494a460155030301d4005141103400242104459650203a8015000c6000a400500c1a00548203440150381800403084200c0c2a2082c042e0b00c0d014000d01800104103861000032100d42000c19828042100082411a542540301010011001441c04014406036040901c41e5030851040d600140440c1c45054000c03070342d182c042e807040b0f010405060f0940c0800400601900c0324604800009110505120144568030201910208061403402e43c8210000f030000080b2a02c02c21031110002d00d50789032080c80d00c0205070325040110003210300c40c18000080c01b030384505400b030b90300502c071039864004107240c504507050300500d240d0185100300001d4000c40d61028100c0240070b05458040c0e035980d503052003100a407040c0d42c80d2070908100450b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 420135278 1250 420134028 420134047
    0x705131119021c0f0c0f05010e150603030a0e150f0c0703120306060f2001020c0610140d38060103050709050f04020d060f1e15120e12 59
    0x80c154155981c0070350071500501d814500011640d6851100540424040f04413408035900070700c040741040d80914400c40d150255503c0325400d458030500d22038242e41010410309802d150515210b50058016002141041102c0c2c0000c1e00c54080c480c00c031485000d095800c4061414514100c6800c51007024209448040108080f070b035500c1180000c5070001e0040d89051803d500c20708c510b104a401c50380c1c1c1e400d0248007c1409a96140303950301030340e00380050000c2510988100b4001880700c0d90420300105168640b800d410349000b481908400107042000850741056564034003801c8000381c10035a510340d032001480411405441503c0e507035103001c0c28044048400e062a103581c5100d91000e803020700040c6e40d019402c49032a00f1038010650b000900c0d4100e000349041560141c0301860b20b0580c0010b0741a1200d8003c810594280c1c40b038186c0358207901c03039419028075402111009044c0f0458412050500701c1010b04212172042d004509507540700e900080300c080c1008103081c0780c024500d48582d602d0445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 420136528 1250 420135278 420135307
    0x80d140d0c0c17130306410a061505030c0c0a03080f0609010305030406110106091a0102071406030606160b01030b0114011d0d0203070e130605061207051311 69
    0x340c0c001d41d805040f00760b802c1c9420f0a1401215040081c914580c1d42c11421903a480d001081a140c1403034404080d10004034005062604240515640ca000b580c9090a100c0020b012103400402c030400150030010100412440e446010017242d0440c1030482e2a03503161050b00c1900d005070400d4100c980b05202c010400c0c5500f0810150150180c01c00d52445e40c0d8401e02407003407070102071100400a41c403c1108000d240c9c80390a52920690a00e80045525540d40ea0741d4030039900c10366210400e66145008109040d0f0701000308000400710888110600c1110400042483c00010075440c011400080e202c90807000c0324a18896150380425012501d507140c4c2455606c2c40da09008180403040086600c204c150300600d00c4000318000c902c0c1c3d60610340c000c4030612000da0406681240c00d4400c03094081000d914030305070a441150f8010440c202407903a81481820340300b0207040c5070f00414039010003e000000108081d81592401e9400810340d0ba801c50340c00000344504114014460004140f0110702c000c40b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 420137778 1250 420136528 420136547
    0x319060c0519030519090f11010905270609130b0402040212190e15011701110301080d0f03110306010f1112070c060f0c060906140a050f070504080d140d0c 68
    0x41741c031032000d18500303178203414112191424050503088540c0a0382001401d008203c498080301850701040d103682ea00c2c00300e001040900402001c0e40307441c480c00400760704d07a40006640020b040f5034100580c100b603040c5214001e04a4030240c030700da021000103801d5444a804640d0809401c08c0310300e80a00d08001645442c000100740300866508120310000c070494002181c0700800c032000c0c04541d40303900c1c0c001c10340c40001440034168000d5485181c03140e0190300200c041c40c0203004010150a001a00c0714008060b00030101850f0281482d000403490040e405201750303a0700450a003001c00a003003c0403026620340c0c0300d10544000070b1080588014147c03880c41b01a200c4107200c3c1c0c9403c08500e0300c41c081603590070b001005880000300103030622004910381e80c000002890040c5e500244201c4400303035030800c0030001c480c2e25420503100d809001d0003400070b541c030b1640443d49240c042d003400d05240351a601c1d0f407413407241d0000300041c08100c200304035002030407200c00340d0907444208083e000020000d032400e200d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 420139028 1250 420137778 420137791
    0x1090206121e0c0a18030203011509061a040510020a051906060b0405010e0d060f05150f03013305190f080105190c020322090b0319060c05190305 64
    0x8008101088054584020f01402c60381d103c40e814051a807100712905c0c1503040d03420354416616980000961800e02c42c17400101d288001c00c000c55030521803000b0995600d13038801c81c2c0d0504524404090254004161000e865007150904141c10204a04929001b5041e1024020b8000d4445003035191550115000081c1d118401c02d1040c2c1d42d0701d40d80380005000701e00c101804604a81450a11854800705c0704056621903400040c511601340500c104407032007101d4004451400c0c1e14101b85a1810f0307030072484d00410440c000d221140d9020142090054501003000c0c29400c4020340203000300d800700b4120090704001e0180200c06541c07018146a500c218840d64241401c0c0b59008520080e0601800d44100752095051a506807802e0809000b4840c8552080460009004180c83c81e1910203000b252081402c4120680608003c0c1000440d00107030000d610a030b10401404981014519103c030b0f4441d0041000031342c03040d00b440d0556403403052490504e00761010041d00044160158400703030103400d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 420140278 1250 420139028 420139051
    0x110405010609062705100c080d1d0102031009050a060314061e01030302060403052104030314071704020603090a08070303061e05061207031d28020a0905090109020612 73
    0xc6035071850304c0d0340c0c880d400e441d200c074110220052145003805d60300c10300820001d10f85446150a2500c5001c00360704060015260280c07240c80e0010390f11102607668032401031200085285003442a100380d40000e0038414101003684980020f5281140e59000c0d00065400141503401001074401d0240ca603c0122010301007218442031040c00f0590007100207050702d034160020200c46e1600d44003905c2a400600d09950181001c1a007103494510364031055010f2403181d00c000c940380001c0310800c0c4641000502038010880070581d40034074109280340c09508144c043e84d0301075403034072040115030034041520805480020f000808008159241e4012400c9a00b51010284030702e8000200a900c40c00e51310072558090701c00d02031030f6880301041e07882039040715190800085091100031491000d5200c03c40b42e0120f60031031251a01c84100300c40050400304400265002e642000d41c1c0082c00f6640385000d1303c8141690307031380000e62291095002c014015001072020ba1903070800d0f074506001120840f1041d0014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 420141528 1250 420140278 420140297
    0x2818050c04050a0905030f0706023001060e10140706050c0408120711120109020a18060902090619030204030803010905070e01020a0305030703150b040306060e1014040911040501060906 81
    0x5103014410a0484c6a2100195117000b10000b842e21031030304611000d0710920b500b00305460380c0c0891001200306040c040140301d80740c4442d5050810200d4016840ad40604ca0701032500009607407104042d80b110300041c2069401c02c0085440c450aa02580032300a009030300e00020301c814903006001030412141824100c6414046907070b83c40e02c40e4000c4a80040034408400050b043c6031400207664248260204000a18107003140c00181c0c8020351980840e001402401180031080c81a01485000d0071102c0c5083d881c1c480000e0104109109070b81000d003440c22601a480019403007601103800464112060b40c0e22561640e1841000740010394278840418081040c2c12010350010405840903605516130f02e081d69604003040c1c0c040c21080c2c07a018500c010700c0c0e00c0031a0303030300303010001e40083c60141e40000307995400c015a180c4655806000100c0640720341108100003000e040c0c00b07a04d5a282a03d022900321309602c0c10322038828082c1140c50b07019003054008130f1142c4c0e111000c1421114190390341240d0703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 420142778 1250 420141528 420141541
    0x106020610060e030303010e06030f0124060804020d080a12090804320909011d0d030509070f03110d0f060b190308031617010305150604052818050c0405 67
    0x8500e43c4010311905a0800c0c4010006050505d004551002c1d000d41a90540422044e00c1e80c212a5100444e56010682c940483c0c8a0810464444090100d90074680c1d851f04041d0001356031107a0f26040146082000521140b1560cc105c2001c00340e4106040f051104203050301c0c010b40c85801c40e00481d1005000e284040800c140124019a818451444140c01168070711041c408000c10007400c138030080d0340714502c0a410304e00302002d81045106003070103060200400c5900a003035840142180b01c884e07200203030601030307100d001e0040e004682d0b001c00c0200c000c4035220f0105406241c0200098801e04404e0100002d11402d50803c1c80e20b90310489048041d2000c000b80d208814000303020250000409100190340c008914000e00055201350070a8210f9004800340300f41c40384e4090308100d54541010701003200203400511003075045102210148503d14042c8051000d0022000070031003115000c0c0d0b0250805550744c3d0003042d43c903044440d0b00000d10b4950500b55030300c003c0c04900901580c90100050700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 420143884 1106 420142778 420142787
    0x15150b090f06041802030402030c0f0112050402040b09010801050403020609030f040315060915030b0603191e120f020f0111030613020d09030c0302010b0307080c011101060e010602061006 82
    0x6d80385010301c141410046c08225442c0a0f0041440d0f45a4507a006030072842c1030400610f00090aa0f10b07030001801610002e140d49410080101c00419044810340040348901d0007502101c102d80c5607092526504e03c12401203102c0ca40c4103000c140006540419100701040c0c0c559004102c06488080f00750480b00d1000c4030003044400c1010410030081e41d0101c196101070201c020b070803201c0d01400032135040342c50044003d21000e60f8640741000361880c00103059089420215401410101540150998000682e040e015202c0c03160808900c0b8014000ca1020b05408039289045484901c00d00452100801e5217032a100e8003440241008441d621440310f40900959401c1909006c074100a42100d0015040078000c0c2c1000400307002030f5000044d400c0410000b0700e00803994051000c4202d004150036001254003000200000481a60003d0b103036006207100003080325056500e503000e44 = true := by decide +kernel

theorem cover : BRFrame.Cov 419964028 420143884 := by
  have h0 := BRFrame.cov_init 419964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 419964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 419964028 ≤ n) (h2 : n < 420143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
