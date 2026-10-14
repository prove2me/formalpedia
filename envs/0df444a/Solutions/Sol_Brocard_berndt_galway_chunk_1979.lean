-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1979
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:22:31.953761+00:00
-- url     : https://prove2.me/submissions/17ae85c0-bf8f-4779-aec0-5820fe3ae955

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 355755395 ≤ n < 355935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 355756645 1250 355755395 355755409
    0x11803110127110613030f030302040b1b011410150219050601050a17070501030b221a1f0e0109080d02070f05030a03090b0f0c01020d0212010f1a07030e 67
    0x84108210440310b20510400c01c0301c0ca44448050000c4074a54244071a03100714040c506201d001c002c117000d5045030014101400b94040c0c40260484480755515004505040d048080e01c0c0d0711226510760800300500220450751a1160145061140003540d40781458503020085059145840461180340701c0d0703034948051180e00d2000d41d84500080d110f15450441000040e1801742c1000342e80c0d003802040c51036007410001c1ea581c2110000e00380428416000c00006800700d58a4030700301c80180040d101d1002451495010641112044098004d104c62040c18030011200018200c0440400748034105030700381c0143e01d0041840014580701001c5a03c40c11f046040c5180c004201002d0b84c880b01050004003001c0300313880081c1000358005d00404009843c014101784051141303200040340000d8108000300e410701110031090a80c00295511074400d0030800007540b010009503c0c0303032001d00020a03c400c48007105400c5980000c200080380744100011400b51f802004102c0034003031807101c5c0310341c2622090303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 355757895 1250 355756645 355756691
    0xe060612040809012007091107200a090603020f13020702030a0309150c1a0702010e0f1f0506060d021c05130606080106061b05010f0204030f140118031101 68
    0x1102540d110f0300390303d0014004507010320300c4140f2070f04807000004245200081d030900f21801001c2c0030900b10f0b845641c030b8203584540840a031001c5003d804040c50000c0c800c11030740002d94292a04103034282ea85440408651130b0f400300961100c201d1202049500d0001d0904500707043d4a039006240843c0d81d40002d00e4001418011004a0b041d40010000c149c0c0d94480341c005d5681504054400c40080d40c0c0784c10189034482880c6400005040100e140ca034800d61004030760b86039a10880d1075110030550b4569940e8110030190309405d007803c540320345800d0f081c05080e00890300a09942e09003500c3c3c3d8100380194102060043c4c1030452030000840e01103083c06003600440c82102c1c0c2a540d12414104007081c1d40d45600041081e0f8104030040007100c0d403007a5560085007244545400000c002d00d0851b01500e200f25602d00d000340046004400e00a46038011807400c1c0c401d0b034441200007510421503090314070401500b907204c02c0d54440b01010a024101c4074410728100000090115105403030130b45100d1110b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 355759145 1250 355757895 355757903
    0x270c0b094c090b180415080609010608010b1f050703030213030c1e061b061118010f0c0302030d051e010303080601030c02060606070204090812010b091302090a0e06061204 75
    0x80711001ca141d50700302c10341d0000380540746102450500e10b49516039013010b143c07407401d000c4c9555201031113032000344c8816440501a4030044e0740d031505041040d1406405180950380072540f0b0501203030603e01d440c1c0400748503550a000750192000c06400c068416410590060b000c5c1074080000c04614105528420042c51044040082a5041c200303884182803038025140303510201540d01703200b40d5070807491402c088201d1900700c1c022500c40d4a807072000303850070742c000d9a150680030039003610710407030002000b030018400e0760390400d200c00d141c8040b20046c8105c0b00c05000350708100703c00c41e0082026005664403c0303024031408000308811031400c2c00e614090340705400141210091198960b4140a050804802c0c1d00c01003456040070700c006000d612039040002d21a568440402c0e0803c8026810399152035020007505030303103694441440a103a40f001610502c603240480160711079820300d10988040c0d40d409414080d1307141c180031079210b20a0024120f26130108080c000360b1004a00c60450b00d110710300c5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 355760395 1250 355759145 355759279
    0x3010b0306010e01171009150b0f0906060d0213030501050619150c0309150810050a1d090a0b09030a1403010e0a09050c0406090b090106020705031c03270c0b09 70
    0x507118100c08441c9c00d000c110b80b1502500030b8400d101c0d90303179010042c0c01400803900641c1d540904000d0b10020702c520144c02102d03d07017407a000011f004040d8042d0348942c0c0300380d03284025111201400806440c0e1782c080c8242034601c40d00c1d4584854403401c11510103510a041a0b8242c2ea220b5146000a000710708510001901860070041c2034050000340c0c03402448143c80314004981450f1105c0c9446d00350a43c03c0c422031740400d00050b14040c1c20410400e5841d04010013144e181480300100380c6039800b0320001804070352030300f250031038001c00603040b64104e40c454400800240c480400802c0a070400c58001d960920926500c060300e03036900d22448000385081100003403410085014498180c805074803500540d04482c1007080f05480204810755110006421108030540c6648168000c0c101070708070038852102188020460401d8410815001e4062440c02c440302e5a518048101c51140c800030725000101c00303443c11340d0b1405001c4008044a8030b440c00300c1e03444680303218104a0030441903060029140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 355761645 1250 355760395 355760423
    0x4060506030a240b1e0108100e0c040819020d260a0c021f0804020d050a06050a0c02011410060c0614040323071a06060c0a1103010b0306010e01171009 66
    0x5441d00ca513540c00041550070a5910302da85800078890049000594180700c04035000800c14201d00e40780602034041c14400a0150a00703080080c0c5a8000e8007a4045900c50300c3d0320400d0034030006c99948010340c0c0c01449940c400f1065a603000940e031100080268401100350b00001801002015014190032a80d40b0140806a40104140741030303e1440c021198400d5200b000400d0b61084c640e59100d60141e0364492040360501d4241d01d4001260000b0300b520340f4003014844c5d111002e070810700122110358000e00c1144000c26036616010030545000c1c120460701c03401040700c507000b400107a005602400002a00ca0500c03075405802c02c82c111401c50000d04c102050310041c02d042601030306407030a04502ca5040859541d9480902100540c0c000e045d00d10b00d10006115542d02c800b2208801203034401e0350b80c00b00261601d00e070f0290000784854400c5d42404060f07407240c04c000850504071021004803015a0b483c0c403d4080b406107800e0341051041c0618007040024035443e00400b11158070418108650038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 355762895 1250 355761645 355761713
    0xc07061e0c050705091306062702130504050a0e070f060216060905040b06090d230321040204090c0b04030c05010c080a030b0a0f080703050105090a050604060506030a 73
    0x340c00c441240501c42400c8400022a500080325400d07600b09855004072515000f0a100702095400001401701c1d003007140100d08000c10038904c032030599030f0600854103074101f90725410603405080241c840130900010100070b5403030160001038004060100c0002d660040140d03442c01d03d8042d411040b03100d00c03820000c00005504000000700400c3c41003001c842e0504155004010b41d10b03c3c885c044c0700b50f0311038400942a50341d0004580403900000c0070392654464616113681c43d03041c03442d280e0034410100c1e550940c1c40313400842103880906d000d4a01c0600c0c1075410000105240c806001a030b00207545480c91000106e1020210014001000f11a0380780d41c510b1501c201d0f5182c0c00d801ca0350400040080c1c81d03001400c003005442c4425440e0402080b40c001c82000729440010680c0b28a45513183d030000099001000b0545106490080009002e030380d03101390750155154401d12000700241e10040019020650700d0f444107403c44001810303641d158074141ca03070803c12a49800c10340031003214460b043c0418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 355764145 1250 355762895 355762937
    0x20d0518010203060a12031e111b060d020d0f050103081201060c0b01051011030a050d110301030b01030b070c020603040b090f0610090c020307050307030908060f09030706020a050c0706 81
    0x1003580d0030000e600d10315040b0301080360120035200c2c490944060b40ca071541010b00030700f132420400c02034544007500f000000c2001406d400a4001c1110f90f4010404451203a03091200c5480a080001e40307481e1820080380c0700b240c029401901150107055035400c10000d00d49403030180c64000d5000721030140c0c0311000c0c21036000d001c00341a40304006008031940300c0000280c00c1c011281c1150000c032880e041c0c0710408d42055071889c2265412020500000880c0e054844c0c218002e002002c003120005c0054441c0300984003040e00c001e00015100d14402801040020f020702c19035030340030b002c9140888040700b0079030100e08140c00946046900a03105001c00a00c1c0300104245581241e0010050010341442c21503c808404503000340d890a9480d10800300c0140c0c020412178160650042c00c40755903058504004008090318081c1c28624060040403c0000d80364810640c01034802e5006180b800840b80d45c2d00b0000d5002019500500c8401c0c001c11803024001d01c1918000d00745038a540448400001105000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 355765395 1250 355764145 355764181
    0xb010b0f0c0f0a021306030b0708090a0204060609080f010e0a080906072010080f0c03060a05030304030501020d0b100509190306090b0604180812101710060501142b020d05 75
    0x140f586042c408101045550308d500d41c01c08103034245a282500c0d01900b031410500c10220107900a1f0034180d000a003240c1c40503207002190ba400c0103803941c1d5903000b0443e500341c54100181802c146d01c0841c5070008181400010702e2044002881c90346000d40690381d188140b00b40002c2c0c2d441038080304081d941941807610b0040c2d0b4041e0b891415108500e80645d1200c060a03001e030450360100d40110000300e41340c84204811000d0f020003000c482d2070315a64075080d4081e600c07141c8203600c3c131800d003c1c58280c82d081001d40851b400d28140c5031281840c0c1c0300b00612070f115010343e4540485d070428100000108080d0f11450a01c40d016000e030070f02c5490f01c1c000307020070b4400400c11564038003004c043c20380104082800f038582111aa0030040c9090f242d0040c90b28400f90141c114103140c0700b0700308050005007000150070b46100e03040c0606009003543c0710010f41380030000f040d8420390b08000b0082c14a40d528212050407891150001d960480c0516403030100413a0441c3e80c000041640e41ea00303100c116098090302a50b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 355766645 1250 355765395 355765429
    0x103021c0615110a03030b0406170609100c0906030509010b0405070e01090b090109030f060f020316180e0c0d1d0a05060f0103210302090607200a030b010b0f0c0f0a02 73
    0x1007002c482c1116940d07030013004051300301a80d8210340c1e96213076550340100d001084200003000c0498213a941064036078106036224211842681c100c008294a03d001c4c8101b00c4440e9280c0031002842c102c0150082e00b070040c04a61a5540c68241e03161fa981d2b18030800703008040998031460703d540204009010b045564110800c0400140074401d00350380d0021003c0260390380841204030819280c0703411006480d10b00141d0310458004001c1082480d550300c503000913100700341c1e1000208218245c02040025503401400c03800840200028401421000100001030240c2e900140c00400c125000c20300010907101080f543d0840c0440070107001013000b04940080411004181d41e51559889050041840100c0e110031002e840071510258025819107048100c0034140d25501c004600c0d114002480940b41025903003000860300700c0c24200100080243e039804411400142d003000b521900641117081e1081441700f040003003c0b09a101800f41080c409598801031240300074903c10170100d0803c2c00c58800b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 355767895 1250 355766645 355766657
    0x1d0105070908030f0a030908040e04170708390d0e09011805060d0803040c17030310091a130e010e1204090b01030204051008090c030309030a0b060103021c0615 70
    0xc445a5404011110000004412139503120b2142d4000c1d80a13080241014040c2c50001c50001007044610b0080f03482607215003441b500e003180011305031041d40104140607020b40310a005a003d0440c1c0c01c920141030b41c407102c2e4008007000c1c0b81c1502000001079640200701e160401801c1c00162500444040c1e04910111401038140d81401916840070322162852100640c54401050080c1c03039864000c22680e070044002a66481c0a0400079500c60341845030316401ca00b846007202d0340c07400c04401e49002d03a4048018440b214540f04409010300703002d204540c2d14807413004030070070b0950b03034099400c0c01c0041003600465a10550144e4908682074403600100300d07000b400240c1c3c260541c081c100c2d070076212084400218505034000490080c0100d400060b00020103130140c260254021001e64415499001241c4031444050207040c1c40c2c0c02844840c1d84c156001d10068000185084146640010185401803c000c00301c8841018000c510b07444502c141d9a074541032007000e103102c003100c00c010300d542461 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 355769145 1250 355767895 355767899
    0x60807060e04090c0e01060302040311012609010f09050c0f010203070f06050703020d0f0516141c0b030102220509240f030d030209041d0304060f02010f1d01050709 72
    0x40c0800d690081c0c250710807940c03403040000704030481240b50003070914403c0c001010341c1c40e89070142c004e5000d80019580e45a800c03980c60280d40c49901226070012140c00d9006000c985414103400d10340c40034011440035500c030580c200980c2c2141c450780d01c0310b0340503500034942103a1000c01d000251114400c504d0454002700041404120300110010036194026400542ca0b51141000c6009001d8441900c5440e801c1080c1800d04544030341015002c0d0107806680c001410300410191090041c40c4407144000c8414030419862407052601c1740c1da814651100418004850340001c0d003281c0c000d440b400f4207d12024860340d4058100e43c0c008001d401d040d28001114189011842c84103094100c202848401d00600071800340c03030b90215411312240140854003549842c0001402940000341e08a00070340c90520701842074185070054140910308140a140b0b0702d42403c50031107280c1925031112080d5034032020b940c12403191503c1403c0545c1c024040410382040e1010542e0709565014203e01300704040c400c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 355770395 1250 355769145 355769147
    0x1e0f050109020c1f090506012c1012020609090901050f07020a030504090e0c03010501091d1603030e1f02030301031109091509011509050108010b0d0c06050f0405061801020106080706 80
    0x24000003103603400300c4d00000384007081da1200501451000100340340521000040d14820201081c0c501504d1a107440d8041c1802410100d8034003400c94036104c9000da008410000e04d0b040c00e14180076940050001840c010080c0045a109001514a00030030780d504c01c1005403c20070340c98107580003505c1c0d2000c2c01d05a09107450082040c0158002c03405000da40d14641e2059803400c01a040040801a009001f43d40e550344440004069000c038601e18203600013124002d0031404201e00d2207003650a0b40c0d4900f401c1c00c43c0c43c100c4000d111520250b070012094045100341403c01c00c40d40d07070000d08590055a496055280c42007000c1c3c54400c1041c01072100d4001d1044650300440c0026010800320716040840d135034800042c5c051729040189034001500744102045850701d03504400d041e6810b036002030202800c06400d111301107816200c060480030030b089051105134800c800030840403030700d49a214102604d03200090216800780180408001c5c54a8040380701d56020300904000f42091005021101e1800310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 355771645 1250 355770395 355770403
    0x20a0b010506130324060503030c0709020306060c0717160323030d0c020c0916050a030207032309040e0619090c0f150206090601060c030e01031e0f050109020c 70
    0x3420720070500442c000c1800304803c2c1c00312009542005c44403a142d07036402821403000c400e500c0030400031400c180000ca0f280c00c001044034403850584008109440c0b41c50700100083d000600307580c1d44030104204d00c02c04142c08010100152000060b00182d040210004070b01e84070300001c00020841c0580d100f04080f42e8842d00c1c4480030a01460154616078503245941c2c00c6109010001e0300c1e03145004081c09200e0360004d0200d9110328203540c010b40e10b40f29064503e04011400e024900011410802c90300b6041c800d030090541544242822460b04c240314407005c10800c0e140c048404015004900000141b406020b1320700d4440101c400791200707050141c40c81000302c94010700016290344481c2c00404000140078110010040e40100980c401d440d20400c00440c041e900c0c011005108200200710b00040c0855202e0407200c0680720002d51000c0355a0031342d103000c4511101414142e46071890324402c051010840940541200e0014801d40300300306440c2203980c180c002050980c03040c000d40c1e81d1458001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 355772895 1250 355771645 355771649
    0x822080403080904090c0f050a05030303100611191101030f0902030615060f0307020109031428200105011508090a02120a1401050604050a0e0705060f12090d030c020a0b01 75
    0x21038107541d0f80303180740c010030044c102900008202c04800180007032480d01c80c4200e081902d00449000e05629650003c255580c081034500e0503d104481004214003406910721070030504411040c1c6080d44000b0440d40410900d0701c0003030342c000d51a054850103c0d079042c455100002807440080014550b10b0300070a5075080b00400004d48050442a00c5155580c0c1c03100b5120350490b03030580c140e941d1501e00342c000d010f04241c0c0011404100300310b60070071024a15406848240d0188401040c0065484040d2515840f14203007000030f00103c0010108c40c24025040f240440034150008201545081458516104001010002c00c082c800a203d142d080c0072510b0100180c0445021909560389005c0c0d0381066008070000788118014400e03070392541010b40100384201000c4400704096910001c65006445415080d07c1481d042802c4c140300c94035001c8058080740050352015414150000040e00072484241d0b44043e4540c8141420115654036018004140380c03d48040c00c00280d1550703404e02541418 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 355774145 1250 355772895 355772903
    0x40c09050711100e070b0403120806120102030702070f050103060b1206031507020c01080f0403210b0a1212030e1c030f060e04060605101d0f060a0822080403 69
    0x1900818202071050b610400041500420740d28240440210840100b5480e105004e66004610300014010081026a800c91f0742001c500400903d01c000c08440711100140b440d03502001c0e2910f10584100f091024602c10038041d0002e040840c1000c1c09800e5800150b4000c504042c28020148000d00002007a1a900e01d41d601d0046181e842c0c5a000905012071034403000e201524807401c005400340d0004641d620541e003038a900540761101101c00302200000c840150120f0303048203c024421b0042d0b58144c8144109000001eaa10b00c908002024400035074445829000310026a500744031400da40e608068006040400c185600298081e0300c070055112500d80403e150754040701d24034041c1c0c100c80c400e41d10f4500308004042e00c40582100ca081c050b1002e0390b0340d92a020b4045518140b41d181065003103540d44640c14086200300e80004601d85060105400241100744080789032111b06c050094159141c0390440d0500e0125502e60b1128201c840784400e55100b8811503011031301801c12036003030304c0d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 355775395 1250 355774145 355774151
    0x51309050910020c0a0b0c120c040f08010216030e0d050106080a020f090106020616030f2c06100504021803070b0a020609070312050a030b030f100b0402090a092c0d08010509040c09 79
    0x14150107107566000e48001c0c102300c801e03400d0401ca04003048030002d1049d40d0a107800710610035101c40102d8201c0c0a1074800300344c42042c4600c220046070090182440001009040e450f4012040d613406003580c2c0650b0280c1025030010300c01200314906442c0884d03150409507400140d5600d4007600039036680c80a0500c45c02c21407110b8082e4516032094205a44580c0d4104080c0000820401030b40c40e04142d068031400035100460307851076102e0010549901620b0350068104025041c901000000d5118000c102c40c2c0b195200f41500321074030300303200200050075032454041d200d170a5004042e060a20051404c411381e0000c03141803002948110075091400507a03d0040e03100e0042200c10340c0100014061140c1c14440c44c040c1050141c0b00080c00340100070943c03014003403a035141060106a01422411590142031560244240308080d40004d10307155500420440c030400445910040c134008030190071854201e0704060311a02e4101500c01d005050a41c2d80e90744900c1e090320b40800f55803250103040c9119031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 355776645 1250 355775395 355775401
    0x1c020a030210020a0f0c05090606130b0c0a1505040308010e0f01060302073002010c0e030606060903070315050603121615110c061f06020a0b07051309050910020c0a0b 73
    0x100c20001e200141c1c0e40302e00d80c001141c5c52070400741c01e02401351207590310031009100083c10504041040e07030003204800706a454001e0809c1c44542c42d94100d1072000080384540d001103404500014504190250401d10005660a05080080c14501c05800c01140ca25104007440304018907911441d0440f0200d150041e112091403414804c240d0b10b503144900c40c11126003000e03007079880440503180300b00d0301030f0020032001d200d80e00240c811401e4007400950503003000300040c0450800d080102030181b0000d0a4a9000340c03a0303030300d89081d40941c4014142c035076981c4041003090300f01040f058034080d0800080d14200a00114170300741044051200030308186c481038031003980ca4040c0d0014081c1820b01c80c00b10780c9410343c2420300e42d0755002c1105d46c68500d240c0308440c91818124000400180c1703080f5400340c0000c4a198543d024009009003600b001c00c40104641c14071301e02018458400b4000300d044c085801e0820300075440ca4074100ca40c000d00c1c0280704010602c0b01010005440c2160340d848008103c40c1c2d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 355777895 1250 355776645 355776647
    0x12040f0f05060a09120f0606090e010e3d0c0203030109140c0d18080a1205100e340f0e15180301020706020a0804030f05040b04030b090c03070e061c020a030210 70
    0x304006d10080400381071410109142106422904202802d400200410020401005e82e1000b101d0401540c0f0740f000c0d46080483d241001d07007200031070303c068610040c07183ca0300c0140e800c036201c00185100681000c801403102d55400e024920080d040d00126801c1c609080c001c0b10720f5480f501120003005542d40d13001c0c0241005040f9192203013a0000a00c44d01c0300c480f24006082c1d0841126080100d40c41c00c030010704446001c80c0720200390345103541c045001d0b5444441d5882c50142c08050516030245035003001480840b0340108940150300740e0790300481240c0c8490054245280d44c402e0503c5021040c0001d1b4000c804001036404401d100c41c0076184014030311010070300900c200030015020500010f8941152034221a6960241e07100f0b80d1800101c1540c024116007902440c0a000c1000d0707003c000800118600114031030704074011106440c58900400002032400c121036010300354112841042008a00d04014004c0e1a400034101101070030307110303a0008400e044103020080c4902440710301c0003642 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 355779145 1250 355777895 355777913
    0x40302030f0a11061515040b030c0a02211207020606010c20060f0309070b0307080c07020a0b030a0c03060f03020f09041a0906040b01051e0103050912040f0f05060a0912 74
    0x15901482c10b1303602c1420103019003421221200103031400354820180c683c2e030001440c0308403001c540203055114115220082c0e8881158044804201144509024070002c001c1481c2e6084060007a0036045e5914003480d10346000584005140f8402d41d0020810040c0f0343e6044500080100c1e80030024041d0301d5070341c1007080485402c4100a90300400041060285229110300540c05484158116803e8036900c1c03080903058441200d4010028600300e0119180c0d00081d400740c000700784001c2032140c1c00b54031800d2040302c54100300c468210040d121100e070100190144240c4000d0080c491509100324215004980041b841404403401604460006814040d0030802080000e04000854a060410313101c0070b556080d05072401da8901e43d1440c0001800d1600000112000e01c81b10b01080c5e1302c2ca1018019001060018414241c60185062520902c00004028006400d0300c841c0400c00a0411079840380821030740e00418040d000030481001e425801103410303030440350711a0034025810104e142c02260 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 355780395 1250 355779145 355779167
    0x1f02010f0608030c1501211511070c050f102a03090f0f0608160c0b0702030c1b010203042d150210060e010504020c012a0206010806040302030f0a 64
    0x25645480000b198900020005155440d450012620420b4440c1d0082c40c02041c20310403034545141d0310250f0104a20102c030b503142620f004034100e85402c0e2401c079565044e2240d69103214403010700007508030204000020301e080604010381e000302081d5061340200d003110441e45802c10910070503183e1803130701c030491a40c0d40500c0b25101402400e000c00a2070060a009228051108151602100410b1892100310081c048540b141e5501c5100d03160224a41014a80508480200094800001c0200c0c02c240305680c014101c80c1c1c0110f989200241007641005541503a91210120506030850503070f074004182c0c0d00b40d07080d400d10b104982030313a6001c040090700ca1080e4141955140c0b40002203184403640c600034041e0240d002c1e0385040e0490b080c10000c40f449070240300e81007501c2c00c0050065050030740c0502000c8a150000060320000b0040000711562001070383d0207000400100320812a5041c0300007801001e81400425041c2000c0d50069240d005280800d04010404a10102041c0c402c00c0c152003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 355781645 1250 355780395 355780421
    0xd020d061401170609060601110a051213060311070201110715200c100e010201021c09050c033009060309010b041a0310050c040b030a0b10050301051f0201 68
    0x4a245408241140781d0142440341070782034201d41024400d000310100384a0721400c2440040d00443d90341034019a84041c42d081d1082e1103101d51400840012410804041d0401c0300d2240d4a450390750600300e521070b5240365007000c0101070510a110514800341410740c1d8000780d090034031049480804070b07403d250901c503900003594003a44400040400b0740182040d140110303c288900c03502d0b000340400a0b520400c080145401000e0700c00c01c4203185105030f24031070802c5414800903190103030300c00c4954000700c0300c07014520074950745081400401104201042c0a808184c028154040c945c0134881a400d110700624185018100302c40a5102c1102e0308442046000801490b100c5c10180e5440d8000e100ea0050070380654680440d9000c0c08034480300444091500600400c140603660b0b10b44000b07488080c3c1040710440e010f110104840b100b282c050f40c400c0c164039500203011300e080d40801007880c0c2d03000c003034400f44041040140120307106c400b000b010003e250107200a8080d4000422401000c0380c1d00030390 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 355782895 1250 355781645 355781651
    0x7080109111e0c012702030607110a3201020418051902070501110f0a0906141b0c0409080d050604090f0204090f08031501090e090607120e030a05070201031b0e0d020d06 74
    0x60910200c5200300305d1164000e5040311001d0f03447da002a01c2507080110b032015143c1c4401d4a5100095402c00c00094410000c0c40242c06070319203540c49005140321030180071031650042004e1000c5005241c94012455070054103000c58100180d04100c1c0e01c91240341a680d06030005900000e000e400d40007640d000310fa45104039510340007946503031010340040001c000007800003030001408610a0440d0b40c40c0c17140c1030003070310310704000e0782d0407070ba103841d20022804640d018692000711140e4883c82140c40d16401028000d540d0307074140390f0b090308444000b003045105901c0c00000002007070050b9034000181d54155400243d407401c1c1d0230070040003607907544001d161000c00030800c13040d850740c5041c01c0050003003030f2180b07400c05403036101005150f00100d0303025020740e03c40800038000743d2041800e110182c204100003d03214245548041c2591700080940d0045500003d801e001c5590520074114211030000c00340302e044203020401864140d04149051181b926070400300155520b01400383ea400303500c40010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 355784145 1250 355782895 355782941
    0x2150f0615040e240f010509010513080609030a08010605071e0327061101090f0f21090e060103020c060109020307090f0905010602011b142107080109111e0c01 70
    0x3406180324841d21840c0e00310444201c8540c3e41070814031517050a00503141c2c40d0500341502c00445030341d003140c2c44120544500440c00102c1c12000c1c0446405162494007440d4ac401d0a900050301e07004041c1e1000081060420411001c1007806142039120001013180d81400d0486090807034607075090f01540e00c0f0020403581040c540c1035100c020034042b250951141800c0603241c090f55400c03124482409000e94114030b1689000503503080d01c41440c1031041c070740380e45000303800030300c409881741134440b0079004c29490300082c0060001405066848542407030b040d40b4100d210202d2603168101807007101d8600741c0110204940900900c0480c028240b15401c3c000010b035104d0014001d0f01007841150b025500e0940c45400d00306140d441030445001070344a400c16007907040c00500c3c0903440342d102d25880b4400d0f803c88000c40b01042c078070580500f01c20381d5a0050741d41000039041c100c60603849071007040071041045040b40071000280ca80c2402c81da51481c1e8483d2042c3c6a007a014004c042000014500c000c2c0007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 355785395 1250 355784145 355784161
    0x1060807050a11240c090f060703030e030c03070605010f08030703030e010b10030213050904050a12030f05070e031e0c0105090a0f06090e0603060c070f020406150f02150f0615040e 79
    0x102d0720f001c0084044e059592076554030300f8118403806c03040da900030032005070417400d46c01e01038000c000d030b14403074940000c03d00d005030130290940d001031035503074810b801c0081d184061000c180035450141c034030082086c1c4c0452403c07542d2540c82c40359240c024141034840042c0243d0500a40c00010009000360a12260801040d0014001c1d0701000005640f0b8402c11070100703c0707041c401c88040c4032319800b1004100d45915520744110301c2807204230b10400c254555840001440942c000d860003841d05480d60350a0248280400d8180031b1140081000300d00605e68642c2016400100715001d08800e0900f0b5a8850142010449855681e049a02c0d90032400c40000392150b40802c0d0002101c1c2c6a4800070b000742c441100301515510b054650b40d08030340c1c4c20300c4a040402e13081c61040200510003080000c00d5580c400c2d03403060040c4040b041318081455104031110964050003c0b01d149440000380800368605040602d07009200944081e005810302d100c40c0040c4032040040310040d1440f101400c480b803030b02d2030f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 355786645 1250 355785395 355785433
    0x11071a061c1a0a0f060f060504030318030c0b030103030e0f0102190c0306050f060307060f09260f011d010501080a080c0a060614010905040510030b060411071110020601060807050a11 80
    0x400d0040840c0303171400000d43d95009401e1103090390384581d521480c1170705e03549046038092040c2184039003003040c0032400400103030548042d00080c81e152100e0303a100d61460901500c5200300c0c0c0c60550285c402c54071001116030b80812000008110303504140c0c40034044d0305211186000a410080c48249008107011f0445440b030041c0d032003a031048007200c003510f407510300860740e02e08040a040c0200d200c0c0e840511500c214801801c90089810384c0003402e203041d0800c3c01c2e1070212807015503d03035030759503852a8007041848401e503c03206a101c0001c5c00194903040d009035440c0c40125000d400c000b0049804505454103000444105410660510034561504c00d41840300d0000340956002c11003e480010f402e0410f4020a4402d012403c106030701c1c549941c90304c40d10030700d0007002c0350361066440d060130341039003080c07005440c03114040c06043c90100590b1062000d80b411061888081d5803054004100081d407040313865921490b60b2034030706d8584035802d80507918404090480384003801540b062280c042c54503c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 355787895 1250 355786645 355786661
    0x92d1d0c0a0c021207030c0b16060c030e1609060501110723030a0501240303171510030902040b0306040f060c0c0c0b07170313110f0411071a061c1a0a 66
    0x401f43c010700550399907229aa40c0300719462403400c800320510b42408144245c0c00440c0c0382000e0305003c6911000e8401d04e40c100f00580102201500014109201c1403500b4030441d405070400f820442108400540e140d5070b1400310b4850b99003a10a800c0940800c2d10049551140414001d0120340c1003010b00d280c42c40c0600784ca1400da40900042650719403683e10412030150440350540c0720469400007800794a03d036981c0042c01c403041041014410203081d03d400c1c442490004160703a00144220350b40c81040f05a03032030741c00c10364420382c000703000c0c400454851a026251941e010341c000403122040310056441d08500304d4054015444a200001c0c003541c82401840078510070b042c081e6a0000c0d0240d85016800251090249801c401c2d41482c0051400d9140300742a0b1002400c4a20110f10030000070107171036261209103d00c0a01080400c01c00008184000303802c800400c04110300d18151020030b12003450010060401140842001e051080080e0f00510318104c103602c44c21140b4112180c0e0016000d46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 355789145 1250 355787895 355787903
    0xd1b060f02010506100f0212040605090301051b03240d1a10030c05010e0a030803010602010c170103050619020d0921140405010f092d1d0c0a0c02120703 67
    0x50310350030340d00910610a482c45800c004003c1c907401400c80c0c0d000c40701451010307141c0095115aa0588a200c21280e015100801440d5150303552011050240740c2511005441002c00f8940700c003403903a08092a80c00d80c3e900c940d07401c0729400900c60241340034441c00844c50103076800204c8440c05074184591001811003203200039000042c0e17070300c400600b506102081d00c4003404e03070b0034445400d024a61203042101001c0000906103000d0a0310703900d4483c2139610a90080b00540e548031000908540c201840c51310555029014410962450319026203c1000400c005091081c581c4e5854644540d54150b504000148100b0400c2182c1c0f40b90040a004004c0d09038842811a1007680400034860001580050020158182414a03210054580da010164103c0620000300740210b000b002a400030f09001140c0d1240c0f0000800500c4240908210703600048920003201e000c1814801c0301d01c0c20923070803200035000155160031540302100c0780c00107000c0c0291700240d19940242a02e4001030310000384c81c01b0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 355790395 1250 355789145 355789157
    0x17220b0d0b010c0203060f091f05090708160902090d050d08071206030201022a1c12030212042307030602090a0b03040218090109080403031d04020c03090f0d1b06 71
    0x4078005642d9000e010000a516510000c0020001403103a0315450f000211081202d602c5900e20310088803615581c404001c407151341c0c50411440840170420320004180c1c0e2000b40c080c000d28240d04041508650280700f103a02d800140b080d00c0e503111444412006070b08001a201c0070701c1030601c000c181c2e4405070350385030006221018804544015208e0f080460703034140c0043c2440a406034450640369200000c00000789051801e561540c0c4461003420303040d40307920074071546914036480c0c039280700dc000d0b640041c10948144a2030994481d02e484d002c0e04140c01a144800720300517101d04104611800404d45050b00941c17000008014140d0098204220212244808913407503e811b10650300044a020354485041d43c660b0303640d8000d20702c0075504841054000b08a942e240d4869008907441548218001500c1c00354400000030140c0361421183c0b800c03203095142a1005014595900605405c07921650707441425808603683c4c0303a1020b800302d45c0582c0d082d54084440502880f404e0191003100d012400b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 355791645 1250 355790395 355790411
    0x60501050408100b0a03050f070e0c1204020609040e030a21020a0203160503040b1b0606032e1d0106030c08010507091223070f060203030417220b0d 65
    0x2020328156000d8450307100041c2440020001514003038220324880340d8201100d401d0210100700244600e408082c50200240b4009107004918508694001e2001c0e0120700188001000540700141d000d802c540c04490b280c1e2200401c01c0003c0041c0715a000d441d20b80d2000089141480e60081e81c0485c08038103940b071489162408054440c00e074483d500e40400142c004009212000c264400d000034102e0140c1d04482c18940c81c3c500342440f542c0100c1d290170030f641412802e10707462802080300d5a0300c234009601030500e000f440c1c03001c2c5400750541d19000860380003950b211f2280c1d0815600c034103071000b000c0080e070841c0b800184001d40203001e54002616040f2000310042101901406050300401850303440b00700c03162824201003401c0a00c40001c45019a0a04040c6c200861400c0500501c1416501902c010f6240c011ba03503a8141869026509540080c0304000106061600d0a40144429404180d139106190203c00380c40140106030400d1071000d95010540c21500006400ca036801c4030300c04c0010070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 355792895 1250 355791645 355791647
    0x1401020d02070305150c0c060702030301091a010207051002250602011415010e1507200d17090d1e0c0504020f0904090201030609020d090b06040509061305031303080904060501 77
    0x220b068000a042ea60098100003031034500c0c102c060b5885070746142c520b4100ba01c41100e403418800241e4032000143d10210040c050050181302c0c49140c41140c02c4000b000051000010b5265a824030500d8418088425030400007402031100394044d910245024403910b91490811013114138901443c001580391400d1b075a00d1000c0048107034012100e829156140c40c8040300115210f4264540e010b42100b0400e403541749a50a8102805010303202e01c1d10f81d1410200b03802d01440032100940ca481c0b040020700342640100e0706080c10043c09400044500c2daa40540034040b4883c01e14010008041d880c01811072001001c2100c0c0c40e01900d84220b500c2102159120b0401041c1d000d80e02c0000c25900c03040082808914140c1d01509c4107501c10305020403441e50b1201c09108a82000d001c41c404e0b152074042034002c10148640041d80154221020000e5050011070a662100000c1052994541c404444010300404006a41202850b00010245070380c4a10300841070b9042030041e03600071802c01c04041a19 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 355794145 1250 355792895 355792903
    0x309241416090e060307091109100311070b0402060915120105040b06030105240a0507110d0308040f0c080604030c0203150f07031107080a020105010f09060509131b1401020d02 77
    0xc04540e80d140032090500001c43c002da00068516130b4940305140300000c0c0003c2601078884040401030455455010782d07030602c041900070964030700c00c151070308411a410220072415109481d4100f102031549aa8500c04118184240b0740a0f96210000d03212511219124800814101805403105140c5176070303400c2030000303542580802c1540f2000c2070005001c10300b06000c0c2510741402d614100d441c540b2816510494903030095400784002000081c1500c00d0004d2104c60a9101006540301c2c4150191514000c0124001038401042c2ca0403003000c060900002c5280f910240040030141c0380030b803c0c41c0ca4080c06808861030200d01038024404407960101c0181c1e03080c3e202c0c0c004541003c955580305281200100851006265000414444600800c44010241484101a40002070194100080f44420340c03203552085405a01388075041c0100e8035500b0300d881e08440b10b01445601000d00e450f1960710048480710001e011260054005480c100c80340002c20b400c402a02a41c42c00c03064ad44007240c407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 355795395 1250 355794145 355794181
    0x12100203240f040509030904050c0c210d09140613060612020d02060a02120708070c05060f0a030902061c09060c050a0912030c05060103060c02012a03092414 69
    0x40402c1d50300e50700304541020780200341d1186030b00041da0710b0b141c9400001001c803001512004030424006c074055400440821030106103401d09403030f40302042d40c400c0c0d94108070322039210101d07122a1541070800c100409040f220403014180e000380c6a291030600340d26411a030b042d00066842c241400400103065181010313800300030b0b80292039402c1200e800d80900c40d16070f101e4080c0c036045214081982c503c56001c10040c0c0940740c8111000c036694001401d24000e280b80f036810042c4160010000c81d1144001c01e001c0350102101ea0901040040040c00054014090f0b08400101a0080c0b1003407034114880b5803042c11f0b9103109250400c1042240c00084030305024104581020440c10070040c4007008158a010380c41520030302c0d103003914410990f9601c0c18200b0a0340b04a402507251a80741c41000d80a0040945c114003001c05240400003220158101d940c1200d101c0061584d100e03070407414810500c227242c1502e1107003801200c1404101c4110340080c2140c4510000c00c0f6072010204004080c21049410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 355796645 1250 355795395 355795399
    0x18080606101b0b15060a03050402040b0901050310150e04050a1704050a050405090c033009010c030f0e0303161e020a05061b160311010207030816021210020324 70
    0x1071500390703558621618000e06039411345441e01521001a41d100d8004100d06000395a020074141414414402aa404144560320800741d203801804252400a41050710300344410001c0743c00b4032102c00a107200000703900101008140d000c1000184540002e020a203d48181e01e076203851020b410300d003000707070103940110340e441041d01d8020091450150401034101094a040d12400e0007144000303440c041a03e1041052007020b4a40f200640340780000800b20040c0058019141851020000342640e2120b9002014480541240000300c0e02c20f84010144507005011640c0c0c03100594500400c0c1110540201c442c0d074a407031201d01d200d4a0242081d20a1903001d042800304508080401595030082030400c026543c600d030454281c10360070001803040900c18011003a280b81181400d06050740c200b030545056500010b000c2000030030340401c884102055044442d010406440024008203803580002c000d071045031103080400340240d00850140768507440030052110a070300503030031428507514225 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 355797895 1250 355796645 355796687
    0x712050304150c08070e0f0319120305070509270901061802070206090418080d020909060607020d030e0a03051516020706120902010c0209180c060414101808060610 72
    0x45d513014060441d40508403030082c1a030031b6002107500400d150551180e200345031000d0f9541d9000038031001105c4007540490524050160b850162000b0b0840e10442207210300a810f27100c0030710180c13160420320805080f00c903c98019141072145140380070704130368000d520040c0c141009138081c0105910844015950192070390b810079110b60100030040c80070306c013695050468040388a00050003140140459030700c079080117850314640707020702107240b600419107401107100300056070241e51101d10030041140c5c54a0090359501c1c00b003010840b4043c03680d01c02003c511819800707141c1c2c0518500320038416112041050344000c083e034012a984d0380340f44160004210305d0f800612450b0003581105400c0c60040c105000702c03010540c0032a001440c01c440062907203940aa007210000310a020350017000c403007101d8250425003000341c84005807100d62101da214492441040b141c050050420000c1c002610f2440c100c030359940d02c1c60329203a200807159075204071032003020603c0c228042c0c112070a5590300e0701801 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 355799145 1250 355797895 355797901
    0x60f0816020708030c010207030210020403110d03031b020109021203430501050f0f1006030906091a04140d121a03072d0311090c0712050304150c08 65
    0x194034108100451042140240c01c0e0100c1d412504000803c11054001c00041ea113212078140241031100c1d41240f0b20090780100000c00100d02d03d5400c0c800b1083c8111961483c1402c1c503c1c047d0006c00c40310401000c141c50032a80440440c0d010b5110324078140c000c4c0d4008690744c204640998907481084c040d86460300c0794080076071012440845444802c0c50034850b854002d039144040b45441114494100c865a440e003040256041139080019009075041c410340141e0b040080200b10700344610300802040550b1104082e0902411740c001301c8000b500110410341c80c41e03040b4000903074440100c2c6c00391240c0d00d0342e0036904a00000000e0500307408140e90380711426001c05040d0365003e8805902c94554000340450701c0006e55405101c100001d024a141d8504170307441c68aa1001503072100c100200701e0051030701e01000460aa06101d140300c40b802c940070501681c90b4200c01c505070140b06000f606400d130b00d4801011050700100110300030740c010030343d040003500203603401c41c01c0d941c8002440340016206004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 355800395 1250 355799145 355799161
    0xf02090303250b0a0e0d02070f0b0c010b0402280e0d061a10020304180b06040b03071202030103030c060b09093c0c0a05010c030e01140d0c0f09060f08 66
    0x4115407051415420401009515100700341881034a00498003a541c4c0512845d031442041030050011040c0050940c030351038250b65240d060306a100d1b503280100c00040718000b901013036100142713140c1c00400c115201e2842c080307044800040c400c00e1015264003001d03804440c9003e50031400d1144002403203c03c0c128001d039109000707082c0301000e8130907107250541e060105541d0031018080d80c4a680d03004503240c901e8041121074940c440c00103072508034588440d20102d03444060072207040e540d440b50307a01d54940361941c3c00c8a00100408500d00b4562000c4004002c2550004050396154000c6c1d1003449800c42c4907040041e60b00d0160342003001c6901c02011050b0a801c1010380d1f04020390041c0345e07a04800110030190f054204e44486049040e004a881c42c0c01c1c9103011840c050250034286840c205100712175034094105c0d428921141d05010315100610380b18040e5100321103114000744000d204a0a0614000e0072888070358801502144012001050b59403044c5038903880060a80d42d0300743d1545501e14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 355801645 1250 355800395 355800427
    0xb03010e04110111302805040506040303080901110c0307020103050718120218010819020f1c0c080f070303110a0605010f0e070906050415171008010f02090303 70
    0xa001d505101c808542c0c80d01c060f1042c00822171107a101000c030304503c05d14007a4441d100e10100d070300b2800a5024000c0d80611010750f045a945c41d122031480c0c101e1600260b00030b0b1102d00980e442150f20900018000c0105079105088074040e00c2840c1c0240a520b280c6401e00c0341502440b040030105903c20b12444000d98800e400c0760341c002c505800c014400f0f80d8140c140156104aa070008500000840c010750110b0601e8078411b220202108121886941085c07107480d210b0324003031100c00a03031159580440565071a02102041450010070300c50b1441680031300084008203581c41901c0e1003001e07403000a910360003c00e00d045201a98409002c400382541d0341a01e1192502c103e0900300e00c10b07246060002002d5210f150b0181c00c007240318405031440d081000c258403100600b240c04001c0e411004014840d0001c060b81e080d1041d42da06003010049488040703820703002e0b04040c6c01e48803042c01c0c2484000414038402009889a110080c0500811425004141e118010701e060301a4030412011403400d0b1024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 355802895 1250 355801645 355801673
    0x31b1104021c05011e090b030a0240050a0b03030d090c0302040608010603021e01140c030c0d0807030b0334080604030806010e01020105070906032f0406090b03010e04 73
    0x1000d80140e015164008400c0f50001d0700701d00300c59012038000702201c40340d0640000040141c0030302400380c01101c070040b0380c41c2c0c403804c8030080c0550580407914240d40d40750102d111759213400880001d8017030341d8511074140100100720408034080c0340c400424001c040c0c1e4040c017540305201a00031450210380040000080046e410280c4e2a4a01060007100581e21030051030020004840080b03421400c5004105048241d140c40c1c81340020400d8410700241d0708400022401c00007141580c0c0c6540041900070b0075882030303078280401c90081089129078550031500a900510040e40d04100f80da1b542414540e4548100d840340170b107040c980745128074035420302c08901d148103511140046c0032079035200b40c5460072030180c40031004524048100b00840d42d00141c1000c68201c248000e1015007403001000d40341075041c0c000e0504050f180d00c0c59140b148000003128611404504103400e00303081401c2d40c0700c0107410038054640010300d24817001030086a0b04007524180c0c0d002c81e1800c0c13007682781d5030307225100c0301404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 355804145 1250 355802895 355802917
    0xa0b041e05010e0313061d100c0b09010e1002130506070507030f051506040203011404050621061906081c0314010b0913020c1002091503040c03031b110402 68
    0x364242000840a01401c11645400f100071a100c94603042000a01e5001d034100400300182285901c6031500c03500d007140500034065940c0c0c1d4104018640890303032140b01e408080c0c032021000c014403103040c030b05510445110501c18142c400150001c02c001c001d80c41a8000b0300c0c000a0450300600c1185072010051944901c13503821188107583d2982d0791011421000e00075540b940100900b51055245481c00550144045508614541c100b80003484e07917038544000903020340d0340c0c0d00c002a081e483d00e02032484c0204103907070400540034920a407541c0e81c010444008a01c1004680001445441d5018401c1038828500107401400840810f07000d48030700032134036641015103030b10910500088010b10a80030342100210184c0d26507110041c09641208032100080180c41000748102e0300c44080740a80b102c14800002607684d20581d00000c0c0080e80d0883c1005070f00c0000014041000010a1844101c074865103810f20a00055023111519011003d8081e05c0c1c2854040107a00e1407034182c0c0100684000d07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 355805395 1250 355804145 355804193
    0x1205070f03230c0a080601020304031a07030e01020408010204080f0105070c0305070606090f0b0f03070f060513050a0620061303080915090d0e2d030715020a0c05030a0b04 75
    0x464540040c0402c2034a4849002200161a100d00743d4003d0869a000c4801c6c0011850070b403a65443c4500311080d8a402e1170f00010707a0b000f181d0300500c0fa030000100025020b0084d500d8644540300503000b540035200d940d510b0300c20b420740d403d4540c2c0103006491054840341c50b440281c441e5a142134130355600c4550202c8105a44030804035480d000d520403d60500c184160001d00502500c09001c00c0d540d442c900d441c46130b403000200700f01c02d11061290030155452482e0054441d441e510891081c1c80954000d1036111062400108c0d040e64016008032401040003103101c072000380b41120f19144d034425120400d9540c051512034000c24005c1a0f0260030001c0d207812594008601d005059901c4400e0b2540071103504030031610200c1c540d1140d01046080c01c12517804074140c8103885003500c2c0c6032000164494454100e81002401e41d400d010140041c4800034014400701c028050080d11010b0595003190000c3c0c451170089514200080c4910015600910070101515191a8005041c50b80500c494460038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 355806645 1250 355805395 355805441
    0xa031107080c0a1e0c090e0304050310020d150609060e0109030f0308060a091404020d03020106050d29010b03042a030c080606010509030307030c020102030f03040b071205070f03 78
    0x201100040401850391400b0b0400362000d0301c4c200080c441c045000905511201400c03c0204124015450417540d060400180382528201094154080c60780166898090354a0050014100d9001414404850340c0c0c20810341e01300100407074680155005a10014160040038044140220300400307c0030014107020507545c0d5207a031032541d1100707200310840002d0701000a1107003034242003136603202030491028144400e01c4042c0220017540c40084c0060b115034507200c000c90900d4000e5100c1405020050000a042e44a07170a200340150755607030390003d0687d450904082d803a941c00c050795041e140c0c1c2004036840c50703d4580303640c12100c1c3c00c00071484101c1440003018504c40182e0b0001c0004603c41d011100340349140100381800c04c01d000300100c0c18400108078000240c0c2c2d0200c2220360392685424648171200321800100d107123009003400100b041d01c0c0001888140190340412500c610070b203645d0b2140c01260740c003d0380d040c0c44090302d41501041e00401c050300928026003003c00034000841c9000c440c81 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 355807895 1250 355806645 355806653
    0x20d0302130b0a03020a08071d0919050c070c0f0b03010504090203010f0f2c0d0c05010b0603040f020301051005012316060c091202060418020c1209010e040504080a031107 75
    0x1a01991041c00413a90002d0000c3e0300300d81049005a103c20103050100e078010b10024815010715241403d61701c00c02c81d802c0050566040d011104410902c42281042289440e070f0340c038400d940c00f2030f6055980c0b01c401d9500048055000075808143c0d03642080c103509503440c20007444064107810f03c040341e2654031403004008203201c0744180ca503541000c80022444a003800084004508800368440403c8904542d03428038410005d075600c402c081d00d04d0608680000340c01c0c05801002c00454040d030014000040c0300038000d00f00496070060740200c00820003511146c140c100d540d0064403a0b50f0102c0c074456601c11300c3e9281030400b42c0e0400280c4000b640b509000c00c400041543c0c2c044c008a0300704e65034000211030b0590040301117003d0460f00304250901c410507000030301c15000c2d5202e2411681c0d41d21000380311b900315640686d5404c0104030b046031040070a4a24840160300180203060004132030803142e8030f0310700d01030040501441d0014501c512b0a00c1c0854100e001c5c00720704004848452003001448002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 355809145 1250 355807895 355807897
    0x170a1205070801050f03070b07080f16050c0103060e07020d0e01020c0607060e120412080a090312030e060603010c090302090c041a0307020d0c03050a0825020106080708030a020d0302130b 82
    0x10703208aa41d008401d42c104000c01c03c05040300740360350b8040d81c80f12005010740501c801c120360045070013080300740d2180d004541109a610803640300048901000214008000000440703a0146500342c8040c0708940e00c0304020b502c07050045424000503480180390742c030181c1c012100040c26a4042c416524101c203180b0208101c0c4d40400411206103070f80d5800c9005464080c80704094044141074040d00e0503251401c00640300f05144d034054030200c4000360742c1030800c0c02001900000c55014082e45000900d000c400303002801d4400144c40c00c0d024030400a04a4503061113440340228564403007100860454007848642c4400a24028444100304804507010814480d10604502e6140c5040d50b20300c3c02d208002e08015007003848409002034030b0030b148000ba402006941c0070659510700480c0f0b690781e90b030301039408135200d01c9904411460301400e24440c6606400010a4841880c111070031155100f80d25980c912078910b0501c0140c0040c174a5403d59440303034005180d0750030100301130141c098540301441b481e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 355810395 1250 355809145 355809151
    0x1a070806280b03040213060e0f0907030b24090105010507030c060209060313110316030b09100e01020901020f030309072105070906140a0b04090e120318060f04170a1205 74
    0x10729180881081308516100c410301d8815102100107200c600d20f01180d10520345805812124411100c10020b1028001003019000540e00042002d0460400054800c0030f12080e6440c200b80952500700b000c1281031070304403035040710b5041e518645090403030384044600c06080e072812248660200401101c42d520203024500a00c1130340c084180301d50b01d901d010f450790312603120b8440c02a004640b503c96545000d2001e107007180c0e0440555110fa5a03441003aa0611301388100c05a41c41c0d2410381080f07400941503001c1c00507007c0c203800b00c4140340b05442101d03580740002caa03c400701e50300900081c03040031140d042d05403004008800607403011841342e0352541480525080b8001007580e88508001410301e1404c840d03003296040c0c90710030b0200d00f030954001a52059000f0702e1441f030344841e580a20003c041021400f00d80d290f00341c841c0c0721f041480c60384142e4913040780c000300548500c02c08110300c0000c40305d10900540d440621705502a10410003089a90800c4103444140034040504501840c0d150282d244 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 355811645 1250 355810395 355810409
    0x80612032209090b0603060108070506030105040b01030f0c0503090708011406040902030708030424050712050c0709061404140c160215120a1d03250c030602071a07080628 75
    0x207245d00d480c40a0601d800b030140d00001031603000a00400054035080100c0307054070740030788000c21010003900050b406005094400e4941d1480d004524070705c0b42c0d000d40954010070446c416a540103a84103900c5098840305042c01c0d00070100c08020a85074680baa0208a400c0e2028098a04c5a591803c100c0d0543e0480da01400c01c2030011503101ca030b441440c101d03c420741161810103504104140d2a0080d41e044015404801d1020018400c0030070300c0c1c20091500101071070042030040c15150008910005014000c4034055401c0200b14522125008203162082541070080350500c11106104007804040c51030503a041642044c007502040d0406004007501d001190fa40c00050801c804d10b21f08032010310300024419950882c0c2114000804400c480c2150b00c244400510762490001d1100c6540c107851008144502070740e03001040081580207881158041d0f4000b029151030fa8800d00c2c2012800c9407144009914940010010315000e400c0340c00402c00701c4030307190092080c1c0b0b0070344042100e81d403c000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 355812895 1250 355811645 355811663
    0xf0d110c01051005010305071b05071203090e070e0d080d0f05070e1f0c17211f0b040303110c030106060c0c05040608030901050a0c0605040804050108061203220909 72
    0xf005144403545118000d0101b86420415880c0c94280141b0500000340c1500c8060501d581e03a800384001044280050308070203040554100407850060043c03c01c51045e000d600d03034a0300000ea0703060300515002c0001e0002414102c60802c5980c2d03940403544c4a022810082c96841e80980c0b00c801041c421540f10364083d48421103400c80072401c01059901d1100b1b090041c5400c041c2540c0d640b54003d903400e1503035901128202d81c0c44168032140c0303064080d50720741c1d00308000c00141801001c82c6210465010365008030086480d005502c641c400c1e10012402250304c1c245040000700b00092150301c01d141004005805d0350301d03080b040c0b40000c0c00e403100b0341d001c07030002800070140c4410f104c64521040018036084030200034440c641b40b100380c0c0742d001b415a114180a0701092440c0340307034043d10f00d8030b681a62280d0100000d15092425418a402c0350048500145120000448034244824000145440030300114101484122080b160600c4140400d522240c007000c0001d00c101a4055843c2051003417820f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 355814145 1250 355812895 355812901
    0x90c091a191116031104020c070302090c0304120203030411120102130f1d0603060417070510060e0a0902220b0612040605070207150f030e2a010906050f0d110c0105 72
    0x14500078012002403801045403e04000003039082d10015040d4105440c0941c9030301c01c01e00d0b0203090100a80c00a5000402031003003108044c1400000c51103148a0002440b81a04d07103a8202d07680d000865005203120b075910451005d902e403542c1c0c100c1c070040d072000015181c800c0791505115400a01d0340205905990910b0a0080710480e0508030904101c1d13a030b100c1a43d28007180000e945a001038009803034107100c5d1440003c8070307000e01e040360360203600803044681c420b0b0002009c400524885c4504810760b142c00e80420001300c40740c0100c0c40c00d25001080c3c0651002c941d4202c041942a0b0403800c441c0d142d9890040340b15898407005004688820f4030403000620f008d0a084050340c0000304048215000b0300014441c0c9040400324807140e048524002000d05000e8005400814040710103040500c02c5400540701052450004181d0301c4c21064240030307207805500151110225400303404080781051154000c03038003404018082c80550004041a8000201e1080c00320b6440215036840f941d4487c810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 355815395 1250 355814145 355814177
    0x1b04090f0b1513030b09010204120803010311060702010c060b032415040b100c06110315030c04020c070b030a14040c0603060e010501080606030403090e01080313090c091a19 76
    0x2260710002400030b116803500c00c0000d4000036100050000402400d0070302c001c00c0040d4825410340e0301501e040030034a09400d0450800150981003413204580c0e0b0000031307028128030b04100c02070f01d94240d81a110b04500309144e40d03614010f002d07820305403034052142d00300300c0d0101c000061380d91401740c00d1600b0110703981c2003480560b0900200d0301d0b0301c94050790901082200c143c1721181da0083d820038a240200c0c8a4145140c06e4010341030180f01800006404014440c0e040900c514424882030220100c0392040c5c1003100b0f02c02a401110096609900b05080400804181000540d0310503100003000508400005d8422031100041d034094424911592003480456010f2162002030103180c008039000b50714000c002015018002e09280c0907050100c04201003500440748000a050300c001403400e25030310396003106c5c2d80e604021901c1340c042c101c2050000300c41c1d4491142d0307224031150381d480620309420043c2c4840c0200e4501905800c99008212440180801e0400c41f490801140d0f00c419030380c1c200b400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 355816645 1250 355815395 355815409
    0x6030e0c03030306030703150b0901030b0105030f0a08161406010e0106180b0a050702040e0a03031a010509030721050d0c031412010315061d0a050f07081b04090f0b 72
    0x3030320301030381c010418844e0360754002072202e04503584011088001c210208200c005803d5010795190050130700b81c00481003201d85410681641c00941c00c44290250310083c0c9503850b80b0300c0001401c030110070030000801c01c83d20902041c1c0746010706411412007036105402881c14801b40d01400c00d002c40d641c014084240d12039048100d06610051503207016003480f0034610644100b85034003044c0302c00000d11400715111030304420b07424084001900d000e0000b03820f01401a06c0c1700c0303c070003d140740d0440c03001256602542c25a411100c02400901180c6d00303145c0c0c4c02e698001212031004540d00750030050ba00055041110309582c842550720300d502d5100624001c0c1c500d041c3c041c1e40d0520303078a0921010b0132159501e2029411030b41c12640500c2c80000c1c01441d04018519a00148104a02e21071030081c1c403038409509900071742820204000c01e0f9140000c805000d4800d507100340000b4040c5d4080f680a003403049400e101c0040f02003a8a150a503203515010841c1c840040000e44940c9401c0403801d28500f0306 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 355817895 1250 355816645 355816663
    0x4050a120504272a03060609140904060b0d0507051519230711130509030a03090503042606090c2b020d0308040b0a090b0f060d080406030e 61
    0x2041c15070034542031000b0745610292024406440000d100d00c4000402e8080c0c0101c0464000e020038195031406031a013850310801d6040411010a061020005d040c9114440c030710203c44080700b800c1e01c05850355080082d40c41c406401030303912644501c11903140d81c1d1018000d80007140f1402c01400f03901d1601c000c0c85907c0022080e0319150210074031a01c40000d03203e0b20200450361b142d00d00140c0103502c0d81c104c01c409100c0e080103d000c06001150791070422110004402b90b0600494210b0b5813441600d21b908252882181d088880380c00c103110310a041c6000717400580e144e0f0300c40c006403400c1c143c8591046000d0040c842c0c21800300c14034a80841002c4105110303c0da04032075643c020305410380c0490b001c240d8907416414110548003d01c0c28a00d00040a46005000b5070350050003041d0802050800800803141a50b0903500c0101c1c14011401c150301d68412508032503840201c059442e91290912450800c0041540341c000110300751034000548044001c0c4040c1646881c001401c0000d070034081e00e410300351 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 355819145 1250 355817895 355817897
    0xe010806041e0f150b130e0d050f0f0a08040210170c090105040f0602070305070807030308040206070515010b130501140d05070918020a1218081602030604050a12 71
    0xc01d00010a55882041d40c0455074582d000540310840e00d440c6a00c80741c66040646015030050340c05120f444682c210072146032003100d100c40c3c10004160303820121403001c801e6403c1948100341d040011405003019008441100c02c12500b000c441102d40341840e44210790710400036102c081040704620341880050f1580c25a4030b4029101d08803c1c250b40700800019000f600703504408540c0c2c20640c2c2c80395040360050000800d569040965540b00030395200040c1c00101ea0501404001142d01b680000c1c052080700d8055440d000c19440d10b400740301240c2e00c07261083e1113071b00540b00d2030504064111081c0d0700030000440881d5039806c55106908001d0411780060b030400c1030804452140d03a021000340d500d40507850500048070389030744c20240d4610302e02d544140f039003d000110501350709000b50b024101c0911252a034002caa0308400d981c0085400e0020441d5444038044024808151104083c00381c80f100000c1b2001800701da9000240b40110417501140c01e03903c00c001e41410021a41ca06500550072 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 355820395 1250 355819145 355819153
    0xe0d03050a020c15060d02030102040f0602150906070e061603080118020a02060a0c032a0207170a06090302070801140612060118022b1410060c02060f0708040b03010e0108 75
    0x14a803c0e40e450384036610b03000741d04001d0480880c4495440c0c1c8030349503100d0760080c0219511030352800405c444680300d00c5220050700a0f10700302e204915160714000c6c03103087c40602400b1a9a1380e4a403e40d00c40e805c848035603800c0041032202c003070700b040b20b261ba800c581e9002c1c2e01c441e009585002600d42280100791050740c0700600621881c20b40355000220745030011645400407940c581550300840c010554001803103640c1c80d82030650408c0c203014840c15000d081c01c40c1d003610041c580b1003000c04013458190304c01d40055403101070302038003054040d070190b40000e1003403055840c507660300d1a14500390352803040d01041c24000b02003885020300c3c0103c2500c040345a80c00c003a200d02d41c03400190745d960143c10752480381c103550001900407100f860f030814039400c100e0a00d40300e84040d01d112121401000e4407030023041c00f21007007008111a900307420111003c84210350f48034852202c082d42800b545030000c4581c000d010b2014400200040c12400142003e09200c1d00220784941c03500544940201c01a404440d641e00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 355821645 1250 355820395 355820407
    0xa050c06090f0a030c1104060323030a080103080d0e030c01020406090f0f0b0c121207020105070306210501021309090b010b0f040b0f07050f070914011d060109090e0d03050a02 77
    0x2c00030400070801905130818400410032421300860700008000340643c400c2c50f0403004001c00c220801442d00440050702d16031401c114220000ba644c0c403c0407541030209101000400c000303010f00d00201300340c50400d140455011000c282951840c0c210541d0040240d4010a05019440e4001184001400002c1c0000861450802c150200e041d4a000d1481e03010000a00740d410200100254050301101e2510703150790341c1d0403601c0120a000e040e200c0a0055017420042a0054400d000340340544400001181240039180d00d2440444040101112030313540911902034200080303c152001428400d5002c11718912900e1711380d282210580241c90b01c03480600400c076941c1000400d80c0e00740d0783c00590080da80d0044501c0f41c440c0f1b0107140001441441100315201c41c013200451220308849900b2004e01c0140159140340c00b107403800b40504005000109080c03502c4e07100000e12135400c0341041c10002405074032481d0507002d640c3c0620b20806a60b000d00e104d59900c5070b141c466a03901100306501141400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 355822895 1250 355821645 355821673
    0x20f03040b030610110706030203010603051f0506090f03070b0706050c0301060e01051608030a090c060302070215090118060512060d120e0613080606090703020307020304030b19020a050c0609 84
    0x4040505020701a205010815003d13900512000300a52882c108443c2626034a01005010358401d000e064000390a107004184034080444030720112140c143ca9264880782080c080c86801d400c101070055008484075003201007500d0502c0a0b8000d809070004c0c0c85d5a40c1130f5810301500356400034020300c4941304100b00410105600a01c40100c055003468043d548012042040040703000c40074010b0100c000c000f090100e00e4000f0760102d81c100f407103207013a44081507032405e00b60201d016000d4003942202156135030308019640d00000780300e11a8141484184401564600f10201810350400c0c00800d600086076400b040c010b58095601210403035100140050320765800e10b60312050018175007800300d0401d03205c90a0307980100340c03081c402d042440030040341d94542c0090f07034464043e42c01c1402007100c1c0001c509058428022244690035640045180500e156640b0803103000050406a01c00036001c04409185800c0c00180304031328007070303542035126001c4c5c500c0c0d103041c0000a8000c201c140d200880a490740c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 355824145 1250 355822895 355822897
    0x12040609030b13080c0309030c27091e0f15070909090c080d020a030e030d081b07020409060509010e0a02150a0201060f09140705043002040e0607020f03040b 69
    0x501d91140c01e8401c0c0341c4992103446070000c004180100145004245d101c04e0400010151900e030500301d0407218881341000a10000010300d140911100c0b1001c2c101110100360402441e810020201c2100c5002405141c060740a129030b516009031034021520f8480075500402c2416401c00b40128004202e0510032030140280391203204104459880d1391000f0180305198145400801c100c0c02962200c80e85104004d4403031100305000c07001320703004042c40031031400e0001d000c111401c480d40b584c40c0300b0b03203d031401d683c0c19031980103080307540c20000c110f11001a00c0e203006a01c116403294502041d0f0741031045030507094070042180d9003e07552080b050080036035500381501000c90440c1c1034071555000800008c90141ca216004201c2a082c81500000d540b0300a82c4034040283c00f440b1071a8003521140c0c000c076030398402c0d0702c1a0160400000b41010030104074a8031501140103a2111803080e8445a01040a803914107090f03171943d402040420043d9a010300c0811204800000030314605070402d10401c8107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 355825395 1250 355824145 355824149
    0x1507020a1a073e01090902040b07030c0f080a05090a05030a0b06100c080408160506070309150c020414010302040606050702280509090c04110403050606040f020912010e12040609 78
    0x280040ca101118140360f0500031a10300008004034000202101c901a940d0107031000c020b0078005109000000b030040302c14420755041d1041413411030300d0f141c21030310121690890700b1401e031040b2041480d001c002620340c03001460010001d846503a215101d50080085608455126600a8000b88034820008029030302c500c2e841002101c044e02201421002200c0720043c0340c1d0000e100d1400050042111107001803c0816103030f140310259802074031941030041c01d002e0030b48021302060700100d00b8410a20b0394a1030f081e02c0881c0e07240c4030802c1a201d4000800380c9413901001400a00520010b00030750515020710303805005541086032038040140e0118580d101c03100f005803c80c0860640300c007200a20110321100038a4002c02845c29803d1981c40580c4031400c20360074a02c05c40c900000c0c10781c00302d003420555017102d8110020f0599591182c041c4800340c80d0801180021550805c40c008041d6200a01190359002460000502c0018592294a0003020940355030100c44184010072240d40e003d003030502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 355826645 1250 355825395 355825403
    0x20114101d19051510020307140106030c0b030703020904091203050a020406120e03280305060a05090a051b1909050a0521030c030301031a0708040c05040908091507020a1a07 76
    0x142d907035a00c00810200b1100082c189070710032048507003c00446d5002026019a90184145039255012a40043e08840c814030005241b584031541c10000d56000c50040e40d809403260801500e0056400300040444801080131070b0a941c82c034000700040c607814803685502440c42d440440ca4542030440107003400200c40e560f410130b652190725503d000e1000b8400d940300d203820108440328504c000982980102122502c4500285c5070100186441c600980e007001110700281040c09261105440000039110060202440e504804450140000d6200c02450748000010110581d00354801000704041c0c1150f002c11301c64090b0034130034006552066028520814007030081c500101d00c0030b030340ca07041d0b000b41c2500303540d6400080000028800a0401410400e03c4111110800d80d90340b603054895a006503800703410318204070342c140aa42829030040d00c2e428043e8102904200d01a0001059003040720b400d120640d6003c20f0080450601e140da100c0600a0050040c002d0300103603140e00194010b00f88003070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 355827895 1250 355826645 355826651
    0x1140f070f02070612090f1b080610060507030e03010912080106090b0319050403020709021804060504021603030b0312030a0e0f030c0d1b02061207020f070f0302060a020114101d19 79
    0x801c040ba0f1f2440202542c4414000400504050480b8112025200c0c0410501a0070f00280b00b5034650307407000c01507030110b8481314140340c0c071030328201c84683d02d60b21110740665032429440003050341d08050991505c0d035941c0e01011581407100c0206a101554045100104103000b8044841030f040c2200c04800c8002c0360000e480d07910382c10100d241810541c0135000451000075054040c031111070000182c1401030701d05200b074a030f0398414031049200350b8a00030540c03c0a91200f1000a10071307040345601e800300400301c1308210700040541000341e009550f100c81e0719544400384400c1700001d00032480400715a802841c11b01400e054410344400032107050a08000014821a9411102a2951020715000317002140c40d800550310031001d0b0f14095401a01600c24812000401c0b80c0024060007503031454203101d00120f1440d070900c0070715040504c1c2d071000d554a0b86140c00704c90404c0d22144c0d00c2002c5400340c420000d0b18264058107140f4142648481180c40f400410106260410f81750014040c0c1c00342c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 355829145 1250 355827895 355827911
    0x11040510050f04060306210312050604060b1206040c020604030801032604080a1104110d02030c120702062e05011d04020408032116080901140f070f02070612 69
    0x441c0d49100302e400d4290300420129002c0381c0282e041c1d10032420303918030088510202d034800c0c95400c0e103803504100040c0000c0c44003d40241ea03030390641201d9048a8080e101041351500c0d0030441c0d0894000b40c2107428801c002208100c1545858000d049260710075001800071030600da20020300c5003805010150030002d013040c103e2000b107122046a804c80b644141419140e41c1c0752403955880e00f407140b070141c1e00010394000120543c5001d20800007410001d40c19070746800381403600c150103504000c200720300b406803d000c18040c0e0300300c40c01d000e4803030413480d03025022600c0c0c0b442c1040c0c039403500c0076510030100b03141010f0340b000d00f05110660b209488007401c00b00003000851030b900110f00c40700721505030030038000703d40014081800005425106900904845042c8030b1100b8448015402c4948039640a03c03a407041542c28003a001c0385810400440010550000450b0340e804020703001daa8446503510740e5010401010760013581070744900c4403071014250f0a85070090040001d1100b9020a00c581c0d035501d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 355830395 1250 355829145 355829147
    0xe0a09050103020f091e0c0301170c100f17130c090902060a030b060c0109030513060311030f0415151508070c02151e091512010306110c1009120311040510 68
    0x1210b0300d02c008034404501c0340340c55070711241c03150000cac40340701d010310000002101c0c0c1d550003141c1502280c0e00034040101840f10307880304a441d00040b216000034441c09650f03054500101b259070a1065454040602020f00c0394903240310107030b0490b8040030405240015403030059403500e04580c140c06d5145000704000e001100052014401c00340b1010056103400c500030f04040c0c210014002020b0349840c51035405580b000241d098680040100b000c080f070800000740e00c15021040303203821900071080804101e6620b118041280c05000100b01e082906850420a10300c0540700001080307802c1c0390072100ca040001020340415000c01000b80706d008d61141880d001403600d000e0318040742031071640301d00d05e9800300303196601d9034425002d95000c0c3c1c4945040440d552203200031244081c800344520903041e842c545484d0010000c2d80520b0400d44400c01c8420081041000349e11002d45035003d002918000030300c9e00783c401c4003c840105d810b041c10b189a85040d51f40000540707007162000d603030450812468140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 355831645 1250 355830395 355830421
    0xf090105040905040c0e100602030f2802073006050402150a0e0a080f0d030b0a050603040602090a05090603070603091a130501050f15010c110603070e0a09050103020f09 74
    0x401900b80340c003042005122080c3c100c0c10891b2103c4440e075101d51a0350070700d00000e5249000e54009a4410002070502402c11401030680001c61440300c801010056580d6048040401c412001680190000d1161b007400710301c2e02603012403002100d0305503541c200f50710007861614140030f040c960390340c0c0004095407120030485822034094840c03d940c82c0040e200241c5803c03801403101b4005c20018802042d114000645004c61071412002017a403000111011400307841c0407542c0903000034010704c001900d9210140078600840c40741a001d601c2d004c0040520040407000c0d07005600c1f490b0490103000007600c000c140b0768152240781c030700800e0007e247c6c20079110a40510310030030310350712041d0100800094840f10344960f081c4181c0080c05640c8a8a0100c041c0c8501031380c90f00300c105250b1030b01004960080d80100f02041c402c000d14003900c00040001002a0821506440801c84128601e465880c0c000001d00141840c50000c1103d035055801151000d0600144513001d540128081002650111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 355832895 1250 355831645 355831649
    0x20a2109031509030206090d200c0303031915031709040b030604030e1207060e0904030c0b0a02030702010608060c040e100803070303020d0b01020c03100f0e0f1b06040b0f09010504 79
    0x440b54004056000440300e00921507010140c0041c000c28001c2031a08002203011071500b03c050b82d031544100307040b156040c3c8184401d80c0ea00e0040c824100346515544062010710710841d10303400f04115282d58060f2441c2503990019540203001112002413000503110101e120200c0404840940c880a91401282c01420699000f035414407078070041108065000e500d640c05e000041d07680403100440c0a140c180d640b0494000c0401107140c5d201450741c1410910400c99100b4028a07121a00c00c01c2a194110071001c141d9295038039030340001c03c010103103409004001c010501c410003030840740381c00c030100c034210302450082c1500a111000400c0307841d40307a00701e150b0141000b502525a15401454050000d500c41040c8864181c180171606450758004148181d901d00b010300a40291910100004008c1020881451020b41e0b10000e07841036260410207039401c440110b000301240c500d00b404161200e40e00d40400c6216010401052000d480c0c2403043c1d8040209103046691922668001139680703010759 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 355834145 1250 355832895 355832903
    0xa140715050a020714062a070f0f0306111c060e01080a0c17010b0909030a0e04020906030708061212040315060f060c0302030913090209060306010b180307051008010e07020a210903 79
    0x807011f40750b2982e0f048402c02c144125040300b21510341c0e6481400d112031144078030922003041c400341801c0011401542040000b40c0482d00f80707900d40311105c81c0d803011219142c44a00c007000d503525800d0040c000c10416007805400e81c81c00901420440f80e480158000303040c0225800e01818400a034480102500150010302e170090013080c09141205585540b5003001005100081c1c2100303d01c505030030709100300d0f40c0001c070180c03886241d0303a80c9030010f46104201902180d0860484c41c1140a580390500007a0742150407010307110380d113501d1810142070303c4c500b245601002070b280070700410004d015191108100e501a0812000304811420164294068a45c0140d0071001000422040302015449040307003d00c2281d4200300380d1288000d0640e102c0e000d00414020440c20407680b0580880029241c660303060080464802c02d031036501180c005c501c1245203401007a0b0074001400344409403054241e00410a10050804101c0381c2ca5004400b0b14400d0107a00030400102041c0850b4881c4011340040c41d04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 355835395 1250 355834145 355834177
    0x20111131a09181f030f0b0711011a09090705010c0f0f06052d060303180a080d02062d0412031401080309011701050603180a140715050a02071406 64
    0x2070010307085082c0d9403c03079900c1030304503040d0103041d1307410046404201aa5002501245082095030311400745a20141c064402e201d0345581c403c48443c024000c01160001d0011280071101c200800d02402c0540039041c0c15440e08515000c0c040c03664403a22018440e5080258286545c40c2801d2018a024850401900c2e03035003000108240040815540342007203080340c076a906c88a0b05021200e1003107100780c5e40194035410401030310412420388510505070300001012014207940d224041c5d484d0408152201c0d0160b04414104028084180707030350324600e0380841041c0d028ad45001c1004800003001000240b960b480e140307595900320b1007a0b1041d48003807196001c440c29561200f4510b40c0da03404c05103205001031403000c1c4c41010500c2248505040358800781080d800c58607000d441300c6400c8000441c402701c9211b40b4050b140030682d5801d80c0100795084002030400c1600f011001d58001032800400d1041c401e08200200b02c1e207600040e8041120a03d100618194500c48000b51403485004080c0c2420300c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 355836645 1250 355835395 355835419
    0xc14100c12051608160c05010c12050a1110050f0609010b03040201050d06121401110f070f1103030310180b060a0e1c0605090705010903020a120303140412020111131a09 74
    0x210061030441744e14001c024010080d075070340004446903040071900510910f40401c454594900603800340424080e00c1c10681c03411810642618a0111030580b10740c0303030944035824005041600600c03550040300640b0b517810590b0502000c2d484d18800540002d0400c080080e04008005a0741c0c89400988010403049200d4411400c0881884d58901c822824551074500b5041070075112600301c40f4108030642145041c0b1050303072150600c48002e06410360343c411700014440c806640a0004611590103c503a6030401400c0c5030408007a01c040f03072802c80100c0c0c540001d0703250a69070300c4242c0d60404445d107010a80f00f005000415482d030303100c060310031062003040c0c00e800c2042100d4020502c604111800c5800d0f00c1e40e514011508a00a444044d410100d10f15080c80101ca45c50b0310f84240c0e60103400c0110b0712002d0500490500c2c0e004480c251800400100034944441d428001c041036808646200ea0030b003510344403652250b00c030038440c43c00d403d0002e18023042a00d40d51310944101c2d0a004080a400207 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 355837895 1250 355836645 355836667
    0x1030b060c010506092518030516060908120405040e120a030207020405130f0f051203070509090a0917070627051c0f0e0303070c14100c12051608 64
    0x81e9000b17441514000c2c0040c0880314152508080c058441c4107041041302c3c40142030340c010440030312040740e440e4900004000701e40304200d0000080440744000c150f8525202000344070145e19000807545810080801e60002401c0058400381d81c02158000f036990740c90b160300ca103000441704110100030004500380c0d01564040c0c1c090010940291400c0c001c44da500d40100d180c02c100d280340144803e81504034000418503000c1d07005401c40c4a04200e07000f40c44840003002c0c4641044071000000b03000014401e1a5091030b01041d07821800004051280021961303c1010202c00d1990b00310306141c02142d0362051240d1034001d4518204031300c141c00e82d1860425030381200452286030a941610a00f400d4041d080c04419502101500c29964100e8900010f9400c951000240280d294144401e01102c0003160380c005150006109242e480b03820b42c0e0b194001d000034404001030460910014251030b401095281c00341c00a54942850103995903600306501614824100501800d03a150104850ba815 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 355839145 1250 355837895 355837901
    0x1030212070e01110f0319020f12041d062409040504060f050105010c050d030902040b03030a02060106020706110c04050403020304180e071a18060c01092a0f0303080601030b060c01 79
    0x110030303a5400c401c01c0c02e1310803856031420403c902c000c06030310802000041c2c4403060300508a2528500c140d0342c140703141d08251850110f00004207425004001400c00260a2128810041c1801c850088406160040000300e41c050517444003080401c45070411298655402d04484076110010020422802c00c3c0c01c20780300030204004402200f914040010131558041c0c030760b010f0310607400340c020001d41048040c11009891140700032604240c50325011001b40c0c0c4c00380058a460000e59000300010761504100038546907090b40080248585441c94442001001c035000d03032841020360780481c0c0c0b0b407280d140032455441035600c06034041c4031f0b821000380d00261507008283e90141c3d08040b246241d4030303129043d0000d02c501402c0c00c0c094000b004000c41700c1c0c000301400c0fa54141c0040c0658100305507440c98500395440c80c28200c8071901034464038000b021018241100b00c4004c100050b4446007041203820740c1c0e01860001405002d001400038045a00c20342042d003400401402c500d031100e80d1260050b0203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 355840395 1250 355839145 355839167
    0x1c02031c09060e010608100209030c040c02030d0b0f060405060f040905011502070f120b090705030102030c09090c04080a080f0415091517340f081812090103021207 72
    0x401e43c1425408188103405006102c1a41d04117000f6100c0c10001c3e8002c43c1c0254040c02c05190180141c0c065401c07244d07600e209081b20a00240c0103103a4901013880b03000110760420488038416502d01c201410552510000c3d281030320015a140741e40c46080000c445c0c02e5001340d03804148011b06000001c100c02045005100d410655a004c6410440d10b032000f0200610480c01414034811142c2c07ca40c012071503840085802000c0c0c40240da2000d5246c90100f401c1e89e104450f09085d910001030ba480060070008001980620208032450915007062803158882510301000350040724080f40400c140386020040390b0080c01c2d00c201c43c0806000040015000d2105842800489000040c0d4040c90601030314a084804417182c0c58443c01c1c0da00c681440c0ca0500f085034980781c00a00801107100703035003020001e03040352100d1502c40a0700103145401c010172003000181460315043c1c081c1702e545010038000074049140a00c04100f152210505001280240540710f0b00940120158040c09401e503044603030260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 355841645 1250 355840395 355840403
    0x4080105090a150c0503160323011809020622080307031d030c0f0103051e010b03090105070f0210050c09041d060108030421260c0c01111c02031c09 65
    0x71102c0c00e0765415002c403144d4180f82c1c008140100700041d0010424404040c40c07840038140000c0702000c0d02c00300b00c0244114210302080310310200042c016101404146001006140c0c020311038010b040c0c1c08180079002e5021031480f55a00c141411960038415074501c405455440205da40329980350600030014084208010110409100c1c400d20606010540d80151040a03010110705907069004400410b8001c240c0a0320107401c8508542c0180c40048850090090b83c1c851912030a00100050854101800c440140f0000000d10b446d070076008a05000d50b072904100024a569951459040c0c0b03100e910600b5520524040750b110b0803027820300c0344600c06c021030800c540701c980c1c07515070460380c0707210700d0040605c0701c1000d04c40103030001d8031026a4070110748682c852503040d4100099007a070902012110b046e0264010900c0c42039143e040004040110007468070207a01094024207641f03a12106240491101d10700487c800d072107008004840c0c1040c0c803090303550b40d4140ba0184c4040101a0000225 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 355842895 1250 355841645 355841663
    0x30f030a03020a090504091e0611070c03060c050a081b04030609030c06050708071706060708070506070e0121090318060c0c0b0a080f090f0a030f1214060402070203010204080105090a 80
    0x305242c1000c7c0b280340011640322108000c4080465a91140054010002c07111662074074040c2070b039000d03080d0103080020300c601180006141540380c08416210b0342c0383c0d120104001030050f05182c0d548101010307045003c5903024420050404091151442980c20103403005040480032010035a10010181009002c0e040800c91600c03480030032955000152000400600340918880f20104440703480c682240004013540d1401c1480d03510f00d04540c01000040c0c07031a800100c10440c0c0a90000d00e5903c1881e4246003542aa41c50000003414001622040101140c1d540405a04260048010a207111100707424480401e5032120000c0c29440313508030485090340314103800140c080c0c43c5015100c0c3c001c0303580c444840e180c4d80c0441c1c000c0403e100420a034002d1040d80188800650284101d5400d18081e94549061141c2004042c1040c1710110389a0348080c50010708403207000c04084903a030001c0040b035004d030780c0e0602d40c0006800381c02540c1002845501c0c10f014081c0d0703803400060b07100e50706106000348 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 355844145 1250 355842895 355842899
    0xa080712020d0203090103230c041701060b0403060902130905010b010f0c350703090608070f0c150902120f0105130b0601050a03020705100b130209010504030f02030f030a03020a09 79
    0x1c0b61294600602040564401d00c103c10b03031507009030031507a071105040681050303200703018400031200308043e28250200500000d05222802c1c182d01c2200221188000912030986402d502482c24821484082c150320743c2d40c4013090842d5102410f005030314480f05400d1007500c103d070420a000b0644002a43e004c0b90f85410001034090181c041c510045800201240d070180c800701d110103a03000002613148004031a0f49046500c0518040581074107030007a070711b818810b82401d1000d000c8880103401c40c014040c020080b41c605962060b1380c0003690f9404405980e050309802c14580181010f0b01000354442035481842c400315a000039802c035584032413002480180c503016150818101c9144d00507200c1c0031800002142d950180005090b4620130b0b2a0051416100ba12000d081000722100e2000954079144196507924040f802540950b007542c9007181362008039400a07113940700b50300c001800307034010204050a56a01740020100d900c0c0131000d4075581c807190b02c0004d00950240000c1400300c0c8131aa40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 355845395 1250 355844145 355844147
    0x5090d0c0f0801060e2d0a020c060609092a03030c010f060909050a060b01050904021b0f011b080402120303040309030605010b090f01210c0f11010203070509120703050a080712 77
    0x50340c1c08807841c0c0700094805448103a00e041c451003946c803c0104500c0d800c0c3c2c211a10040011059210300c0c03403013000603141c00000482d242041c1c0042e00941c80341d4004001e05c8405280400c48504005601c00352002d100c252807400c0407000025900640d240c08003082100d003024043d00b051010803158407007084181d8680c0d0800040b60911100a003107644540a0900040c2059204001d01541410954284144200020281e9000c1d0303901c46c0341032142000000c40c00104005007150790a200c0000d02440105104001038510121001d800f0000f034040810305644548640141a89014040d00e60301c1c42d05003000382440c1c42c68031088825a207800b000144d1500601e06803116030788000d1640c507182ca681401191400d1030000f621224101035111942e14101303a10a010003103805071a41c10861030030b000c0c00b400c9070460311451801079004002b00035220754040d044500c140340490b0920540e0060054031490300d40c981c0c10040207841103440050030300c00c050000d000514803400081051044c07141e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 355846645 1250 355845395 355845401
    0x10902031006121413050f0a0b130c0e16020f03070209061018061d030a0b0c0307020a08030c18010e09010620100c03060f030308041205090d0c0f0801 66
    0x10540e4000c07600c0da80901640344070b88800c6003078000760400410041c0821003029141308013a1001e05205000c01071000030040b01348504502054004041c22240c3d03407948484018100060a40444440001000e0304001e1900e2035000a00206071041c40c05140c0036414010010700c0d446510050300c944020704c2c080c00000011210340c00d9001c1c044490f00d840b00d10030f100c4171146107148202880442e541c01940700d407600001e8070040115039030745490249404060001884070101c01c6010707801c42c0e814040031480b1844101d0b0011311030128240e41381d85401040703051007040c1d10b00611208000051182c0c420b1004040c0401c404140c513071401042c0080b00660b5070700300b04250107030412184001003180740d01410100c40d40c1d1041614210f1000785220006080101c12061683c2e9156240c0109880a51510451018180c900050f0040c141980c8001e084480300400043c6549100d41410040c50720540a954100388007500301819441c181c500600c01c12a140a00043d01001038400201010140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 355847895 1250 355846645 355846651
    0x8040f02120102160c0635100308070b040b0a0e120309031201031103120c1905030d0609020d0605240c07150531060c110303040b030a050c071110030e07090e0601090203 74
    0x154000c20454587c0052066800a0984109444442d03000010a000ca030040500c03510170a0713410743c10700d40303441c1403508000058201400340349808040d958603000094074040807240e401c010760300c0e0f64900d0005891032045820710041c078115000004200080e0002c0d40c030070345208400f40c1c0c040c8245519815018007800b06070548581c4595580d0980c0c0c882035030501d1415001d44152880c3c00700c483d9054080e50383c0703580008901640041d031010009420f110f4007019090481d011042940080282c080a45000441c0300c41210001a00c501c500c03030401100000741007440703c0100c554400c01001e002608561403e400d410051104105004d0180408c441d250a414444c0110b403801e180b400c40700f221007007000702d8000382007001404c450703076040002e000105050040c090796464002600c009aa00241070903030892400d00420001072a0121200348503841a160f2025600311504124060f003040c20115809000d0a1008120200280c00071038802486100702c40580c0d0344ca0650504900c411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 355849145 1250 355847895 355847957
    0x13270605041a0f010e040e07050a050a030b161205010303091509060f0e0d0c0e041a07020a0305180406091d07180507050408010f06031208040f02120102160c06 70
    0x82d0500b10515062590200040e8185803e01080c121240803500721071600804030700c1c0d039202090030403040c03a01d80401800341106880e4028000d1079640c581103006000f0b0040e80c2074a60550070706d5401481010300441d0500580c000b13000550703403406c014040708040c2c09502481d071510b002540b01c3c03d000b60ba13602c04441303859680c2c1c2100b01e0b030b02c4030840704000c800003c3d80c1c0c000c07000c401d0b4101003103d420101c1c4c050603413039920203130314101407034102140c884016074001440d140e84100010380d600450415055501402c10b50303aa650101400b84200e607198a41c10f074002d00d01207003c500981282d01060f8002140f00c90118098060f402003035a0340c0b074511407100d59060540000558411a4000ca42c0026150030060709140d1106035080c00e44005020000845ea5600b90410500c503000b4148ac88c0005d090900745224200794840e0100703018041c3c800f034064030305891003940c0b8000035411502003502c881c2c200300481140b403502507107003030980c45010700103010150054a0740b02072005030507086400b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 355850395 1250 355849145 355849181
    0x20901140919020c1005060102070f08070e040c031a07230702060703090302030d02030304031e121109062a030c03030f0604090b04050109030809010b030705061327060504 75
    0x2d641a081c00312011070102d480095003d000000c200d1808100310004480300c0d00f0040703000c0c90544002803030200142d00135030705000d11a404208c0c0000100e00700003a103003809008502540c850600002021065000500700801079001c201c2d060264594a80240307090f41c1c1303042c02a1410f44426030304105401e68286403100822004005162a1000f00141352003030400850042d5a500020304040d41c40c04510056000002048101544502114102020058200e4281c1182d0a005000d8501d100d8166a030640c0e500c038000041841d101601d8401c08010844d031f964900100540581c12090280d002840c82c1c101404509030754080700359910304410310000d5046641d20081142c1000c4060480358100f40d03030700343d000080741c04500107174441c40c01100045031103000e500e0002c01d42c0c0310080c048a0140d24004680310b80d543c0c0821070200b11030049070a02c2d210600466400040c00b0f1981c0200ea45440d03400040440600700104070b0340c00024200100526551030382030109980c003e4031620444a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 355851645 1250 355850395 355850401
    0x901031505181f0323060708061201060b2a07140130050723040909170a02010903090b1c0e1009030206010f050d02030304151e0305040209011409 64
    0x346040c0100e43c8203507258107104801004480030880c603426034000741d0b420305a004920403030080403030711200744d02c00c080f008040b586409100240a0342e000342c400391044840c090300742c81c403540941000e4060441591030a5496009030b4601c103002402c035151400e070040c0030000380e4207240085903120886095043e84c80c2c0c01500040112543c031030540000513107455524550780030341c00c207440602d20314000807000140350410400150404000c1001d5421106980c120401e0004c82e2405031401ca841c00318012418846510300107134030f0915078041507215900410350f6041a903054124003e50780c0a901c40822194980f000705c0d00c184100e1090804107902c4682e0f03003009808a80c00046030740c80300015170f0900e90151414000351404030100b580140d2000d40140000000c280c11100101030840d0391441c0d010356980440d44174000c40c4520361040081078181e00001e405202244052002030040c507092000700c02d00540203120588069015074138031000810010300c0c4841e000c18250008200a003959 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 355852895 1250 355851645 355851679
    0x6010b09061b1501080721210c170a1103070309030b191a12070b180a051c050d050a021c031103180705100c060902010207091a031203060d060c0215040302030901031505 74
    0x1445070306804040003258270000011a41c4400080441140d8440c0c2990351400124014488101f950803c110380d00100b2a400020f5084040303c3c0440c3d0703000000700c44d030b23550310030311400503018070b4140701c032480d04200c501005007090914441050201316050080c03420009501580c2d098103000c0d0030300d1072004004210051180300181901604000c3c84810380580b600f0206404010440b03111420401c209140400c20209001014038920245001e5082618010009644851003c25007040e6079152000d5082c0c984607811070380803984100205036030390422020040062994004280c070501074124049103d280850742140561a140e03500c1c80d84031801c0e1114402020710000c220705505c510040010b0b408914011405900480141c2818a808940074903080c40718405400306280c408100304a820340e10f040000c1820754001400103081e04048106034a804826610a1100e0005004000415a0000090114400a076024820b031205520b9100e098041c1d8000e4981c06106400d4040e020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 355854145 1250 355852895 355852943
    0x109020a1e030606171515060c010b040203180d08010f0626010602030a1803020d0f11131a0a050105030c0a020705100c0506010b09061b1501080721 65
    0x214005074008805035901d075107000890310b19602040b401111420385042001c02400040f0000112003100c2c6400c2c54108191800500b00800c4140304100100f26942084002d500107207003488042d00840d84c904246a07101d40354190595101410b00c50020588802c610a40650f412142d5580c040f0706054103181f0150703481041000b0100e141c1c1c03000c5107010442007644800074000c1c00d031a0040e556480c5031a600820b034141d00c07202605102e003540010130040e203c0d400b0ac6054107421110488105225203080e42c0d2111507a0040c0f684081c094004910398003903544510f8801084a40f40308652a000e81800102c0f4200e00c03500e40070850500000b10320720003820081c82c0172807407803054170101d139103510001d0b03010780003403004400044059100360704001080180d5030150840720032450400d01c5182c0014000d1042488850a070386070041410702c0441d0801290084000c1d0034904501c940e116000e00c1c1d901c00c3d8921130078415100080980510030036103d206101c0e103130014401009004910640710391 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 355855395 1250 355854145 355854179
    0xa020303041206150e011d1306180b0708010f0e0601140903280308100326040e161409010503040b130b04150f0b060a141c0207020907020109020a 64
    0x52151100480701191141e4284d91000d00403039584241c00c1d506050903c1c24290716986134020f1410180280a416160401d603019102d42c08000412185801c00a044d039440558400400108005083c00368040e04080514140c40705e8824448026941d0803060142040540d2601d000c00c245000483c0340e4480e010042c040510b0180455103100c0c000c1006c050344000d680070103240308244921a4042541c800300c41c0d6080026426030301d08180c01c41e102d40314a00102204c05100d0542e110f64080c0b003103e0a41910003c244110b01c5040ba850a605148140304e40359460200040340c50120400350041c0505480521906940705401c6543d07650303c04051a1000d0050881842c40c00c00b20300015150900551003140700b25090b500c030300090b40c00e4a06441e0070303425040ca41404c1500c1804c0782c0c0c450006542c0d1700a85803520b02c2c09007800000c9030b02d0174850f1941084030004401da5a82d040642c030740003004030780c0c401e81e0840440d90360420103d003260004038000394002203c0004103c02034100c0c11800c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 355856645 1250 355855395 355855403
    0x504120e150d050402040b0925090e01090f0c081e0405030906030403020f0606090c07061509020a050a090e090604080a170f01140907091802041a0310080a0203030412 73
    0x440c900181001e035001e4100c0c400303410845442d2001c02c011424280908030f504102581c1c12480ca0516030441c10034084056452402d04011204400c03907548031341e0303080005107401300349030321903503103031100134015040416a414035541001048440d80d0f1040d4030b041c1c800d90300220801c100f41c0300320050400c00130015105942a00c01401840703d19501e00000b540240d129030001c01e800b00c08105e1841c00d103a0001e1120384038102001c100a1022170180072030b10707801e0340500001050401c0c09000c0c02c003440381d071304400e417031a10200310f18090036007040040c66183c101e0384038103100d150790360074000d030f044000c980440d81340e00041c0110b000280c46801418407801d40f800c0910300302d10b002075000c141d000111030700c0f14030045c002c004001b642004081460161000c0e2511150381c0b80001024000c542c0c58850800c051003822140c880000250307043e1805800c800360302000750305081241d0f004540040d580c5104501219100151240000540109041e4007030051403e01385041c1711200ca40910280540d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 355857895 1250 355856645 355856659
    0x1c030b01090815061008010602102307091a09061e0f0708030f010905040b0103120c02030609010e0717100b010c120c050c03010b03060c0f1213060f0504120e 69
    0x440c4110050106588011031800c000c1051302d401c10070410402c0da928200ea081c80b91070001489842c1d40455841c0511300c0c01c4501003a0007600740c50306e06028403420095803851603208280501e8540c004d40046c04c5075a80d00300031540035101100c000346c9108020000d40c0c010303020404000e03080b050502903200c41c030000b500541080301449201c5a0340d401404200c448140020402105200c865290b9000d4502c0c44020410340c0340954405000d544103000141c2102d90340d1148005961048400301c04183c0c1c050187c0d0360a003040050103010700115011548140101400803035203e0341c2c0c582c41d0f01201c025000030300c258507240e42008000e0402d01b202d03c0c100078a814864000c00d560110300f901917400d6660f06407001d0072500300306d41401040c0c00858031990409950140c2c40c0d40000c0c0d041e4010101050007a43c5d6800b1000c099420702c107060840318030040f040100510f085d449134103003242c54003420051100d44010b0400c1d0081b9003086800400700240590382a007940e1007500d0582000c40c0151001f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 355859145 1250 355857895 355857899
    0xd080a0f1e08270d030b03060a090f0f050c120a02030c030a03020a0311031b030705010501090506060d05060402070c0e01080d05040e0109050411030712150b090f0408120c0c010c021c030b0109 84
    0x2072400c1081c0e0841d0000171030380b54440480242420000e087d4007020440c030405c4040895030b1000b4038000c40400c050100e00d1202c10100031702105000403a80d07a01c0050642c080c40400500715a00c81010f076109a1290242d0b6024070a14100440d000c10244d03403607405005840e01a076410741d451040140d008a0304d100505c10294000c0c1c03018045100f4040200045858505a2501c02c3c00d4540c140c02c40a0014100b50a0180c0380e114542514804c07100c501c00881c1070b230b559001040c02405040c101800300008040001030305072041c00900e0507141200296088503410346d1050340e49200d07511580b0306a181e5000100300040f065488250807902c41d8010b01c0a050b00540020702d081103035045034250024071440181040100303c2c030041b00c0c0342001c0303040c442d06c0b5403080040c1d1000b41c01003200d1075810904000404001001046907a241d400e240b080c913181c140010481c1d49500304038800210340d0300c0d0003690380c242d41c000600d0f446181c84d0f9611030321031030007140c100724050021070702001c3c148400c4100c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 355860395 1250 355859145 355859221
    0x1005040e0a02220e2b0f1d0d020607081201060503040b040201030c020c15030a0c090f0501210906050601030f02090a05060c01020c120a0f05120a0504020d080a0f1e08 73
    0x1072801718400b50051689404508071800c00e400580d01c80801440360b544a04507505030003c0360100b42860140d41d0900000048000c034040c0c1c0341e0950001c0d804100060480d00f0484600c0180078110f07400c0710f440c40c251380c8031034094500384400d83e409001840d00c1e100040056100b5080b5114000c0d07a071054071341410460020500051081c42c0e240c00940000c410004001018400d480c800411864031502140c80d10206500800007401000c6c10841082d001c0100f40d604080d03c107120000410041243e1039043c1046402040207442c0140004c1c100990704440c00c1c0301b8002d6454003c0c0042480d011103243c18100000c0d0b074001c200c2040195001e01401c0707030340c078018003042c40211030008480343e60b03a951000c0206209044800181440b000740a00d1001c02c44205003249d0100c0000000100c0352210300000d510303036203103143c014801d031000901c10000a070b2003044000e0055550301d035440f00391030309499507070111030900c000c40008210500041c40028665130540c4040480413245070700340102c100c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 355861645 1250 355860395 355860403
    0x1e060706181101140a090e0c0c03070507030c06032706110703021501060504150c0606091b0306090c0e0105090d0609030c0b07080c090f0a08061005040e0a02220e 71
    0x301c141c03404068200103441c1541c0000710b004002e211040e42038601040c40e00064404c600f40d00401c010352802400186140c019001110364600c1c1030b9041700c6d1201803526080b5511070541c0001c490340d050f800e80c00035401d40603001f60860540e40401ca928807981c08a2100e003000d40c80700e426108942c8403086041c400111500401d00c45e40203a014010313054500d4000000e00e40306900c25020002c08101c104034400d21f95101202030f200a00e0122954001410850050105500303c900444d1401e24403c0301c1074103d0528111140f03464400340000c95569085004494511651102240300540300701c1d00343d84501c2c020205950f00804000c10905240c0701c82d42120f25400003200800c110f001082e041c0051145429486880c41c80c02c046207280800e000a0300740aa01000381c012807500035414501c3c0c3d0b441c902070780a00031a400f22001d5240051541c0b44c1c850080c45581d008030310b402085182e2442c04204101241e401508400c1040c5036003140300e855104816248640700d81d240710180c00980148 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 355862895 1250 355861645 355861691
    0x1811130b032707140d0c0302010f02030910030b03060601020c1c1707050606010216050a05092e1406130509060d06062417040b0c040807030507060e1e060706 69
    0x300140a442c0c1040b0305a07440f810070340e04103841900217000703180c0010202e0580c071050340e90a1034100d400c00300d9000140e103140039004072180d014002024a880607503142e4011204080110202c45464680e0001aa120100b4840c2c1580201020000300c10652803a1030b0408903034810a1598000590103005054a0b000780740100c07500d070083d40602160b5070f41049840e1411000c90003826840f4039040019825044e0b9200b00c41c0288031107400a6030101c86441030428035a01c0703003644c1241c00044d0320300c8003048049010340022200394805021080c02c12400755a00008a00c0c58045030a00780010811f035010300a203200d9000550019034000030703000c3d0060300024802003464a10054036840b49141051001b003010f41008880e900c4582071101260800d500150032140801c0b150701c4e00d030700742d250f1441140c1000318144103200b8000700f04240080c00000701c13001075485d14000c01040d0304100c0d0100200c3c000c82059001c010004c4514135000008040844c803a11001401c40c0c028a03110400289030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 355864145 1250 355862895 355862971
    0x30403060c031d0d03090f06051f0b0c030d0509010905030d09020f0607240f0e030705160503030415030b0d03110c09091005040218011811130b03 64
    0x1410780700c0d140c181c040c0500f80c0350386418608442d00c03442c050103482d074441031208824101a101c1116034148600000c1c50121213030421f034107000a140034261600d8440030820307410910300c2c0c0202c0001c2d22020700c1d41135603181203218010310b01d8074113039040301000303043d0250802c3c186560703410400b03002030301c201b000340601e1004042c00706912185004210301d01031010001e5018540c100610400952003901d60440c140300740c40c42c413030300a840103400c10051083c0d1641c991050b10305030045810400000c080d1007424802c1048035a42c6400700c0040e0710740b05543c8640c070f8140d030050005000860110307103894601036480c41c0c000751855110000a6502d20821070030780c040313952200792401c140400c0c0840d42030b03840180c3c0c0c07503030541c207042001d81d03512140c01901d99000e6030b0380c2001c1400c6654500400508a282642c0c0d90700a50f124180b20541031004003400c0c0007a8680540d030606004840182e03040d07410b4404030f00f11781903c1c095010740c4540c4005c000b2401003040d04a00844010304203140f5136580c0c21 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 355865395 1250 355864145 355864151
    0x901060f0e01020a080322080309030723060106050a12020301170f0601050f06090d0204020408010b0a1703030c18040e012003010302060f09130e0a06050f13060203070c020303040306 80
    0x2100a40421216500c490443d00142030301004074100780222504650001c7d1085203244103040c59040551000c500185860800811b00107a104000060007d039805410318884000c1b07126140100100d940e85910065000800100a0b0741e01074000392802802c1e42c10803a4a90301599421001c99009130072010400100d030807080001f0500700b000030901c40c0729030000c1c040c7d541002c0000b90041c611003a528892640000d511074607460700311740c41b000168040c106544903a04c50302c042e0301921811180a010300d81c00300c00010343d201281c03091421070b0841c0c000b031441c6441c0c2001c820055401500c5400c51540148150629910755104031141d5201b090000240d8100b480c12003045000c6403500040303051414030040c005070b0f60b544210b44105c0f140a0400b81d0301c400104c0461111028011408400c91405240319606e08010501d40308442c40f4520422050380c0710004810b07001d509441900190307122a552030300080c4258000d40e00440b0908211450705081e0b80000d20707650045d001122882d403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 355866645 1250 355865395 355865417
    0x120702010c0f030507080f0a020403140105010303030e03070305040312050705150f01090605061602271b030f0f070e0316081207240f090602120105100c0f050c090106 73
    0x20b441902095101c6481ca010300403402c2c05030005000200c081c01e9200c8801605000c0b5040140b02c2d4100c900460f402428041b5071120b04030003500815091001b500030900701884003d0292000c02140c15a941c0740d00c455042a0071501c2e0031585141d0411f14105100302000a60b0100c6d0302009113140942d12a6444c3c0740602d0a0040403402a1041c1d02c019000750a1103030901040da100d00c11307101c1031418241a00c0c110782640c0002030107002e50300b00c031959002c80348000140c00d207444e0f0051781c0f086016400c10407568101c501c540c085480100e51110781c034a0382c040481e904560300001c2c40d42095a5107452020408402c0c0001c1c10200035804090810703041c00000c02080d0b40c00d11056200034603031210709042c42e0a584982881708070403a949a21035007464000d03184032300307a548040441c2e800c0c1c5008000d02c80341864000020f60015440080381c24503400001800d180440c8000f40c000903030781c2d8422440d0900c0d5102e10038443d40ba10700b180c4500072000360103d640c482031348841c02008160b032001030141c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 355867895 1250 355866645 355866647
    0x305030306120303370c09230906041503080301080f0c030d081306060b070c0e0901090c090b0102010f020f0a140301120b070e040e030408120c0606040b0105120702010c 74
    0x55901441155281c00034001c11100700d20032060014201600219441ea1300d00604031005140c224445d4901a54036140941040310b074021a214151441c90180180000d00301e40c00701c0c800c40151041d141d00102c1d01001486a00f0260801d454120520341c030ba494403912541d845180f0303042600400895404000c91141c807045c1080044000403090300074115803040100e0041400703e0042560b808440c940307070390404000345a403200008104001d2100d40f68031b00740c0f40500700c1460510a0100061b400000308060354410b2150420040e409400d0b0f10000d484d01c403084010740b000d140d5075410741d5641c009461803484140020071002c0940d000f110354900046401620b003808852402403243c400780018002c4084903500040b030300b070700b0405101c4140d44008040350b0710f81500402c0ca800a04022064a510100001a100f03823070407d800d6a000700500c240c0182640103004198000b0351061004c1034146c10aa8401c480f425818580f031450400d102c00c0100c40c2210640f00400103070755801c0032007807003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 355869145 1250 355867895 355867909
    0x2703030b0a05060c07060f020709051303030c030507020607030e0a06050a0e071505180418050f060714340f15090f03030507020c040e01140114010203030106050a03060f0305030306 79
    0x1802d0704588242c208040c505000da07441c0c0d0980902400e001c11500079054071802000024010500a00b042c800c5103000e5050400708601c00c0800c0300480d040400080425010303000d8203100300c14030381c003c145658030000210050951051406401d01507980b555001c1915802510311841b801800482da60001c0c0c0e0506142c1202c41c0d000001030440008543c4c03106500104a81044d0b88414011014000d000005002416006600541d4141502054080020200c1c0e0b03901c0d0300b112030003685d07680d544480003912140483c04030ba0220030f808010780c041d4a000d02151112003121240e816000c44040b0200c0c90701403008100079640101c600304200c2c20000300179110720800c00103600911824820ba0b40d80c0300c403006c501500038241602d030786c00600c840c1d108009000850034010801c2c031118813260085030003415448480000043c0100002c900e001040e5450240b03828180d004600d50303840c00700700700c0c0d2540041004804154452000003216406105940040c50142c0003443d5030b420708004011301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 355870395 1250 355869145 355869149
    0x905130204080307060b03010f0227030c1003020f0c0604140106050f0a0506031b0a0f08010b030108030a0810051009083a05070203030a020607110604080a032703030b0a 74
    0x9080c0108818090084003000703403070707107107a0009010404401500c006405003980da5140c0465034030201c0d0900300410700c414415641c6400007114400700c9885020715072240494002c0980240e202500319125601c258002c10640d142010341d00d0170604134102160038500e065600396241c03d00341c64024660368081c0300e01c0004107021242d01c00701c0c40f400004569042e1241c0f28107803040f040800010b0f00d41551841d01c0c0d41c0f034884040d6040c0e0f5403d22200140c113804010010b000021074440c000305046d00301c20110b9042c0c507081c6005600b010349403403007120b210070000d001640d50040c1c80c50000301e90b00c0303203419294001080d489042401d420586001e141100040c3c02d02c2100544480300c840c00c10039284400244244944400360741000760206490a225800e0000d406110000c3d85200307655006c2283d501412480d540c0211024803140450365604003034401074210300702080603071440307402135008581c54203000056121000303210070354030341c0b00381500310580209850b0403c42007245060002000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 355871645 1250 355870395 355870429
    0xe04200301061706030a030f030e07180c0e0f0d020a08150a0e01150506030a020f19030c050c150403110115050a08010608100921030f0f0b030a02100504150905 70
    0x20f4500c1c0c104000b07541e81615a5018050040800300135981c280b2035040307c142011a44212848103544880e600705000001c02441d45503868014038820742d40c0300d0b002c401c43c0140010f20802c0c28000301c01c00c01c000f000e40b040b000c80c0c0c03141c4481400074420030700380f004d0014050141c1c03070b20b04245440d4072000140d41d14511800d400e81d141552840000300c826501c01c0a40310180ea8194890b96042c80d414000c0c45000062400d040010032000c2624a030000440aa000603503421311084a0b00c0e04140c9040c015010003121b1604001c3c0000b106a05451485910501900d40a000c01407408109400c650b19041c0c4100046441e1078184003a040c03062030740c0300401c0560020060a450a20b00300d45a9000141101c0b180740c40304081d00034000c854846402a906009004901c040c0c2800c01400030030710f00f00d072441d0482c182040921190728900c40c040c1911009000303403280c43c415038204405481142100701c1400400d010200c0c1e403441c4103d06c56040c21098075294001801d043c1000102030070603003c04c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 355872895 1250 355871645 355871687
    0x31507031e0c05031807090f2a1403060109051002030c0c060405060d200406080f06011701091805100905060f04050d080a0204080316061b0f0e0420030106 68
    0x5503042d60720008495000d10003091a64420308400d4a05042107055400f01100605002d00220100150341c4140500c07519103a582c035402c104108007182051b002540c00b8041820b204d98401c080d07030488000d5610100500d03080f080c017511080016200d003041411880141e0000c01c075070740030a804001c446071a4030100c8105090901d0320f0300281a03841000c40c54010305d41c0394010010309520071951050050710109a141c0c40e6a02c440008081d24070448403103400f0402680450201d5016500c080b600d89440308074014642e0030307c00301801034910106120b80404003100320034003240302802030304440e1118000100c0d1101040c10424503002000d802ca00360322f03490300248000503c001a5424043e00d0904010340031b690340350409030003400f030341c2d000420700e000025420f00303100d0000701000b80711446050200b1400306a904007400d94803c003914400410311080c0040c010b54003912140d05035000c0107102103068030b00c20b8410030b1031040554a40010140100c014414a60400c8222041d40c81d49141d003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 355874145 1250 355872895 355872911
    0x609020304060e1506040b0109080f06040b0c070f06020f09040626010b030312041b080d0306090c082e0b09010806121914150103030e0109030b0105040209031507031e 73
    0x2841c1046021704458130a9907102e4103c109039001e091040e000304004e0040d514400d04c605100382d100c43c400c42e01118080048e03030010701c0c03900c003680564020780d03000234000380221840e070b4403240254860006501d1000e01030010396140c0ea194000c00c0007900750711402c961a030300581c6d8007940220086031a890564184002c40005440000590b12403484844c0100d00c1c82d1a20b0803c1c840341404590309032844210900b02140c40c1d440010b80710a60301c02d5603810030110380e440035142c2c1296400041c12002500c058089504415400d40d85501903d0440a0314103403503c0b101c0ea01e416001d1584400440e900204a130b541540c2c1000c00d081c1d104d081a50241007698404448603110940c0350031094a0215156a94080c8022a00070500002d1070100310b42c1c1001030755081c5960301c402440100e00040b00806a0541540700d91402c808595014075511126420102000003a4020344c21186d050701c03641c00420400c4044400280c05604251000100c15041c0424000c42510550003040842d09003070003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 355875395 1250 355874145 355874173
    0x1b0405070309020607060b120f060f01171507030b032506030203010b070b1b03040b090c06040b09060c0f01020703080403121b03051e092d030415030b03010609020304060e 75
    0xc9820042d84180001f44924424001901014140c40d0b05051449082c4040414845c00512980502c0b0080d03003814042c0e03610800c0300c09419101240801c25000519183c443e18a0181601d404c00d0302d031305021401142c0440420710701194100008924460800680e41f0003000e282c640c1c01031308003072905500d1903040c104072034072520614000400002107140011000c403e030941403411010210030b480d54a04040c240002d00300c07800d407448a040d0043c00d150101c07902c0c2c000120303402c0700e0003611003a0400c81a44100b086582002c115194240101c0c04161441c45081c8001d03d0147d100e80c98814840c140b40c04d00810000e5402143c0c4416460301d0220280e00006105d00d042030342d558500801d450361078070f100180c4020251039128100b44045e040c85411040032030310965284040602c2e8201f40c402c0c50b500480c1d02c1c1a00001590f9400400040c0046415828464104411030070003040e0911400c0100e401c4800d00c0e0b120710905503002c400c0c041001614041e48903505500c4000700480005400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 355876645 1250 355875395 355875397
    0x9190b0603280906020d05090c030d09062d0201061701090305040b09061605010606180312050306060f0d0b010f02010c0801171e01090302150f0f181b04050703090206 73
    0xc65401802c8011040c40400400d541000c9142944048195202c007564480f10004d050180c0d0280760f2401091103e005c50300740083c5c07041c0c0780c0e1040d80e105950149030040c160ba4240d95604007281020050716180395210304000030b00500e0140d980001192171a00121780c0b005600c030301101b03520364105480030010951100030f50301640c0030221407aa0344c04d803500000d07405220f1007506c4c03500c0c038127260007000503c20103520090458400380c0f2003415141c582071249808101c5400028450b03105c101c085503226220300042e651100f4050310661412003044203845c0e69400000500b07403141c1d103d2030041c03441c0d6442502c0450b4109140000d1060080c02400a082c1c484140600d0011445540280b44585400c20071083c3c100242c400b0500b40726034410b1070345e020b070582050940c0035100d0504008407003d0300c600c40c40d01c580c5007140047e80d291910410700c1c00d0480302800261101c03140e400d0400300c0c00f03418440701c28189400010080144150f4082c0020344800900d4907051516056540e405a12444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 355877895 1250 355876645 355876681
    0x105030d050a030c0e10031506030902030307060506150c0109110105040308030f15060703090f1a070b040c0302120604030201060b0c1b0612010f030515061c06060509190b0603 77
    0x41400300d0362442c1ca00c003c55400700c2540c00c2d10341c4000494034420429405900623842c83e1040e900740e2002c070342c0320719040d01540e80042c0700a400d5402041080003003000c9034881500301000030400483d640031079041d1211604250348008569542e1350009041260041905401c2c901c00e080040c1043e1031600c81d1080703408020300100c4042c4016000400c0e12900303082800a244000b800c8030b481d071289003002401c40c01c0500a0590a079024034012403048060000c0481c0c01144540701403420300d0030344d84e42c510b02078058012105490540004001a40d6400000f11840d495000410780e07480c00b41402401d50f8940d60108002c60410421600114008600c82c0608c0343d403000c0c2d04c51080c1036030011502d544150390340e04601e1382d0f20900104800026110000071240204200c2d00e12a040d151503440038001500c40591040144898070090580c0207030342d4000c1e07400782c1d10010fa015680c40120740860400c8030940741c100308104000020300c1d00d611443c215241d087e42c4190540c41d101402c402c0d00b580103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 355879145 1250 355877895 355877897
    0xf06010f1b030c050303181908030106050a09080a08090102011505210f0f010e0706020607080105040b120609030318010501050a09090c080111071401020715320f0105030d050a 77
    0x78203007052600404403d10381c2507020084a58a1415054104200c01c03a5484007087c0d01641c41030700382c800c40070241c1e004000d07081a882441c40c0d1800a06495550003e820502405140300001a09075420b00c4844d200e103000b0358829641d00c402d14002402c4440b4010094802010000240501d454480741d0240b00d4840d40c80240652840d02c014a28100c409000d4212911510310100c281c0d00d41908101c450355000130440b841c030341d140e49080c2d89a04044582d070000940d6440108030524040d049050905c401506c00a000b00c480d01c541c0d130801d40222140caa80e5800041032100c0d0070803182305580040c842c880208650f504100004910841030701c030b960382183e100e0700f0b0501440a003800d007000424030003008024100b18110b0712400c03070704992426502c4c0d82c0c0c0c030280d03900c0d001d006000b268601584014111174207000c0300c2001008041020480800d46d64400380469940307844040c66a44a048000c04d0350613280c047c012040091050300924000c4d0800712207954041e420100340d901001032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 355880395 1250 355879145 355879187
    0x5091305100c020309040603110f0307031205030c09060c060f060d020105030402090406020c07030c030501150b0a0c1e03050c060705090132041503060602070501020c040e01150e0f06010f 82
    0x410700700f240b55002e5000003580c89407170308030f000080050613216400703004000e0725180c0110038000100b545449541c40090480c2074040762a117441c52250008662226105a625092500d64001b040464004c07180715895503200c603060010522030b00e021903601540884015215078015030009199000103071000f809000c0d0f1501040421803240c0544140003501d100f1214841d54900f011443c011951100b40ea85501e0541281d02101c000c80443c0b0a460700c00b02e41c18a00442c00100302c480111540702600d03040301c070611080c40c10304a11088102113006c1c4e91503d0b100c4558990b418180807020f0a01014010100503441d03c0340d03007003030300440080d0750446102c02c17104e8042c1401700307039019003544299601400680465074591224100303600c00300c266420842c1940b01c08040c0e075151001d002e172030b0159000342203150301031034590410580c40440c44004501c8282e512042d03a5105200d4004803480c502c07500801c00c0c480140c80600c0d920400919108a003207803491000b03045140b0110240040c600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 355881645 1250 355880395 355880411
    0x806090901181b120f03030e0c0d0f0201031e0c09050f0a0611010207020607081215060d1a06030c0c1c140a02011404030306050103061a03010e070c05010c090509130510 74
    0x50248181c3c07000708004c421562a05001d4034103c40220345982003140803903c2c1c070100c680000d03000070301480c400d800a000b0103c01035041d2100799030300000950403410540c5400000214405064a45008481004010900400c2010084e00d0030005401c01d034044c0203031464504039640e402c1c1c00c80041f158035040c900d018000c0e103018070340640300c0c0080c0650410b0001a6590812880800074200410000141c4040752980c401c12078907680800e0700e8580c0081e05015192249610341c3c0500301480603018180702f603200303100110360702d07030800c50701402c448401080c141640302d01401801420051401f01c1d400d02080000050100482c0d1020030038105800f10b00300710f0b503038000d600140200d11180c28455483c501840e00401a000340c0c00303058002400d10000003412454a80d40400100c2c02c4907429040d82c0c01d080d020004504024400d40410a00c91104400328200380316103800d440066458001850518083c05100d5002901a520308603186001c130010540205002142d05405440410204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 355882895 1250 355881645 355881683
    0x6130b13090501080d1106040506150a09061707150507230610080d02010908120417030901090519020f300a0501060b0f030721050106080609090118 65
    0x401030380041d19090310b0000082011003000801d90701418035590388985150b44049500d80350201900c006100703501002c04521011125400d62400300710150105691a030b82d58002d2058842c55409520281c000140444018405000707410107080c82059040c4003c0a0110040c010f101c0d544000e4401055a002c50400360078031300000c0342c1e02005000b1115642000b032494203500c0c0e80342c4100310705031084400c8100d0302c5006004014003039412001a50410340c012907043c1c0700c0c1d40014400c4500c401d0600d407080d071310701103280a103002c0c030303c0c408c00091912520f1912610303000003102c007210101110000303600180d40e003a51013010f06000b0b031151a40f40a130110900900c040c0c22441c5407885c1c030003000d40c201c00701000a449900758000c3c002480040d60700c58100c41c0f02c1c4202c21014548000c10400180e105004000c80b040043c1d882945159110301001050110707402a00980006801c20381400101c4c64942082070704000d0840c0200720840c01400c401042d521a071700010406609103118201d60 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 355884145 1250 355882895 355882927
    0x3030e04020d02190201200a0e0a091103092a010309050f031c050606030402010c0206030405120a08060f01080126071503020316170105121f061406130b 67
    0x108480050079916800301940064044070160340c1c104c0107619010719a2491502405200502002682c4d81442c0c420441c408841742c880710b0082d10740100f070100c1d0026144480e40702e036a40054801121689a040c1810b429083c185d600c60710941c107100040c2d980009801c80303180c400c80d261003400d00140c20507883c5003813030400e5001c0c041002c007800040b43c004006414060466280c1c0c00c1c28204210665550080100d18001502d0190000f008103080d0b60042c10a4402940c000b0b000d14211008520310402d00900c503846440f1070f40000d500403051010030b04003240782141e0740400742131814180d070500205c1031a0008640d200c461480c01c10350b044030130310414003409020701481c201d508090155200060080d500649500085440380c00315414154407546018040c2049032259006903481c100c200241c0402011424142c2e01910180d2168413000b03407511100140d0f00c2d41c2c003141e254903092444682071840b0014a00802007000102da0071100840b4031020b49a8141c001901c3d005400528949 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 355885395 1250 355884145 355884157
    0x51c0e07121a040305041a1603050c150a06030b07020102070b150f030f03120f01030302030904050c040e0906040b0c0705070e040314030a20040605070b071b11040e010902010903030e0402 82
    0x50000740000c1c0411301d540b0034000c0080d0341112210f008107148955030f42d04a0700c5500b1011401a480464400000e40710348014440c01c140304003160031401c01e08070000035925069a60308010b42e0b0320b5074204104000da030281c07940041a030000f18100b110685440c03800400003008a03041d81d001d03480e250f04030340c0c0b01100d0708424071018044400744404542c40d150b41e44d10a0101c040003480c507000050360900c2100b64141641d905501075070818a1070390901001c0c1c00090880c030101030050001040300036580d40c0c810b128a0815000b03010034101410300c1100808054100c507103c81c410840707000401c400089241c100c4e00b59003011143c80d40c0d1800c0445034191002015801c80718000184414010690071001d00700c1c0a01081d41455a07000b8080d02230382c80785200c2c0501045c0c042c088100460110b1b0038031540200d06050402d000006c0f180311200c21520b50304100e0300460000144405402c0c40d01c205441d500c1130200811a00520b0740002e890515207120040c20014048510030140d2926010b84034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 355886645 1250 355885395 355885433
    0x206040909050f010506100f0f09121a150604140307080f033712061a0c010513080405091b12090d1d041107050607051c0e0712 56
    0x10a5601d42c0c0b9049031a5a00c00c0f0440203558240b0001c245d2900c0c0c8060b414200901546480001d100400b0080d20b620503401d41d80014401c4030304002a820740c40d9a0001d2060b0300ca07690054101358032905501c10307440d01030000e44159414100e0031006031105800c90b800e6854050000181c0401d2400003481d10039541c100102030f00482c04426002000000038001c81e10501d18406002d1145034034855441001c041c0c446107545841c0521405d040c06000d82c16000040042c020804640710720004890014114009985501c00540080400c0003846840d8000702d2030500c04002c02031548036010709d03004a000c1d40b4490807001f804920308462410280750040b0f040c054054413500c42c44220301c502a000c0381c20680e42d000f4130702d03103448280c86681050708000300341503100030550301d11040c00000d0102c1c00718501304e0303001042420041001049007a200755040d5a8041d501ca0034138118403800c04802130141001070130900914070155003c11044151144107407150340c5201030741095118405145c1c2110 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 355887895 1250 355886645 355886651
    0x509070c0807080a09180b180405010b03060412030c03110d0203060307240906020a0308040b090a051006170a030f0c0206091341041b060503190606021902060409 71
    0x11401900548040f040751071a140318886030141486102c20385407c981010340c4086088902d032010342c40541226005030048000203602203115010a203450301c1030301c040c1c55400e40500000701e15980350040506503d00c0c0d203004d000301069041c80d85014091600e602d5001ca401200081458a08100740320084c20f001d81d0303500840c4151070314441007040600c1014001040745e48040f8001b400081c050021a034140c3c1d6010750341d070707840e00e40205170070000d801c100c105d00a2045101c0440c0d002c0140c41c4d039134044a000011703894901104105281c0d4801c00d051000e400520b0680302082c3c0045c8460110b140f03034200340012645910001d001482449500c541c00810f540c10380303044198070351002c00a078a1454a015641001480040300507441c062143c605031020b00c1454003000103042070b80d800510440c800600d2440461028204100300c1c0c1000c000142c1c04800c105041c1781020400100461003030040100504141d030081d203400105014201c3c640000c00e50300c00310740300c4400720ba0061050000070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 355889145 1250 355887895 355887907
    0xe03120a0e0703210924021c0203030105040606080903190c0c08100b1918020712171312030c0c140c040b03060112031209020a06090314070509070c080708 68
    0x2c0b00012061340850805418030300022240d040c06580a00151178140c1900c403200310046406400c0381281000b64411030188400c1010481025100740f4050205174002e961a581804180011281e03903501403020818a502400348025010088031a00a1000320200340202440d40c169103402150030010726000b807c0380c001610381d80200e0b0540c1c513200380c0d03481484440d20140411060143d02c00818490045c0da0b6000c01202d0b00500012111800d40c000150910015071108008111140404004200c61503200a00e40c81003048566000380300700e0340300c60000c0c11619220442d00c0803015050606a41d081180c903a240204c241511803580034000480c1070384084842c5071160300f6028024001c0d800e04080303404c54500840d40506841c0480f540c2a03101e1b205450484d0348102c445035a0700300550340c109210150f21070707240307503000b0b040651603418407030317181d49440d24940060400c069105d401074082480b00340e440c1d0b40c0c000e400c0728161a22540014046c02c080503035120307465004198a00c00564 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 355890395 1250 355889145 355889153
    0x403110a06050a052802180d060903091a030114010513060f020c03070302100e1f0203121807030326190e0a030e0d2916030e03120a0e0703 61
    0x700a100783e50249061040b0380721520401890582c2260502c401502a0281c5600c0c4540e079000c0d055043c0c603084108010f802100104004a10b41c0c0007d60700b0740c0e1100700c00d00034545c00800103002841905078034101d41d0181880300c5a10300040c0180c540500c1116400221a80705000b40c0d5a40c030031081030151080c0d07494801418400404800d4030150040705100141840c0c0400c04100f02e0b90080d1501241d10708540381290b5041e8800d800d25880301020700e18400c00300c1007041030107088650380c0007907a0f51083c2400b2800d214030000c04000803400046150020300030040740b00c1e0201ca904d4141800e401c41680700440d401054152540100da010000f0040d0201d9000120522a40d801004104280100203c1600d80040c1035020300812118840010700b42044240000e825000d070001000040403038544c800604260306d00409500504424094980400c001400303088615040c20400b01c80070320801c1d5183d0080340c4000305605102800078454541e02d4004450103c60b65082e138452603100d240c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 355891645 1250 355890395 355890401
    0x9050405090c150a0804080a02160608040308132102031903051501020a17130e0a020d060b041503020c0c040e0313080c0a12030908070b0432090403110a06 68
    0x741d0540f041c40b426860400d2545890100e5481c81c03100e903540906980c2e55200c44034075500c04403800e800c610400e60228094141c440f10140581003541e12070449040a007402000b4440140022001e5507040200303100282c0342c1041004410500c1c0005940946c0c068016401c41c00381c0d000c14070300d0000700030760301030100d500d80d00092107a502c01c480700e5140f240b160012a514007000f00014188101d0681c0c0c6c0c2403c04084019011000e0215820200039071075021151420005554082c0000e8010500101e07141c00c600600014003803030407038142000c0c42c01d04865508a4001d41000603d0b030f00041031805444248111000c048001e40103100650305c81042c280d5a41c880400b040f0481c080c01000310f45101d01003194800c09000074002007526090104901c2c204250b03001c01c5061210381000001c01c07c074180050001070905d210307030350344079441d24805c0d602191071002c00c50b4401c240c0c9045d41402c96020313100307401c1720325059038541c40d1070743e6916040c0d90315608418040b84034481d41d1121410010360360 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 355892895 1250 355891645 355891663
    0x90a11030a020d050f131b0308040303031b030c1e1103040b0306030f0106050114030703021b060a0c0309230f030301082a0310110919030c061803120905040509 70
    0x181d0200b01c00d1740e030403555038285241a1044403094402c1d01004010070f002c42d0345480d5440b5810180b050300d50b940d5076032803565841907000720040b0f0303200c003c4040c2200c0040c400203040c0e18141420301c8140ca03004402008801d0701815425481e0481d48500c45e150700c244910020800003008580c1d8503074880159940c0794104445403886842801d41c8540c085106004a000311030040c0c50f00c0840c0038441c40c2021903504000d0000c01055030038802c2400e5a1000030480c58000c01c80006854681000c481e50f0095540c1400c80c40306142c188100017000502a04070395030342c0078824402280d100c40024140342002d40c00c10618a1070302c80132001148083c0046449180002c800102e0382e00703940c015461810103201680200d51542007444402c451502c1c54200304034190418100e549414503150000b0000050b80800030415070600009008014100c54520701900c25414810b204403501c1e000382d20141d4507400002c00c03025024400c011400e0003486c41d10040e18004005202c01d10301b4104460380d4640354 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 355894145 1250 355892895 355892917
    0xd0f14040b0c040e0f06061903090b09150105040f09020a0303020c09010f030503090906062a061b07150b220f05090a02040203040f05030a11060108060c0405090a11030a02 75
    0x480d02060700d400c20b0b40115001c40d45100c2d280c880c103a0303400d1160b03030a00000404054004c1c00410600281790841030450001d00c02a4800158412107410046c003008402040110a98170500c03580da15255002045411544100c8012070f0603c500e4079174501500c45840c009410110000c00401019004220009040c40540300b800450381e941940e014158114400a4403d400402410071035041040f03043d940041c01a11840ca400b02c0103400401c11034040300810345030840014140c0c2100010722119800010081c0c0103400072400ca154255244600c900082c584042c0b0f1000c8d1801500d150460f452108005100780c1c1035140c41c040c80c0c044004180340c110015858035002560481c1135100d0a03024000e008000d003210f42c069401d2000a520280050701c41038440c2800c00c0000e2000c000900c4519515501e00d2004850184401e03d0300c14103801c42481a000801002070500c4480161000c80d4002c0300c400c0204d0301d0356940400208050507c40d424103000000300801141070750000c08880c130320 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 355895395 1250 355894145 355894163
    0xa0203120606040b070807020d050714040509010c140729040201110d0f0e1503280501080327030d0504060906020313052209050a0204141303050d0f1404 67
    0x6030000c201c003e02c03e901802064450910100c408561908041d2400078405841c2900251940c0c440710700e04502544500031070b9140f00c1b84601c0781e0400380282500900d12000038400c01d444101c024154010502900410080c04103468052041240f900b80b60404045810030a0603d0010000c0d6400e000300d50a03404106004001c000c40b0100280d11a02d0b043c8070351b1001c40200901104450285581c80c881e5808442c0004e010320007004c0000860240c0e11818214000611040c40502007416500d42850968035201c010449000302008135201400b142e00c512401700c0c441c130f03500341c00c00204200e4281c1510a500410b8403080d003043c0100300f03548450312481c29440d03661404a9407407141c00002e103844011460704103c076090031113080e000d180b580400e294402542d0006c4108503032041805807143d40c0b18030880015803c151044180580703251010a0030351400046240f455828410003c0130000000f444a10403d8180c1c8007003112074024109220b05040750a8114010f1410303141a1900c8107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 355896645 1250 355895395 355895401
    0x80f030a0b0114190e031f05041a09030702040b01030612050732130e0d05030a060e070f0806190803071b180209030a0b2a13030b060d06020a020312 65
    0x450141965550505160944c00742d030304e00c03802110f441840c001c442d030b014424824001d00e9100c0d240041c0c1035490784020006594a0541440303441c12207a400d172108100e545400744007411a01100311001310340c050710b001c50020380b0207004030010083c5620062030765108910300010084003240e140f08460744020f804c942100e00166640b0700c00b07031411803140819204104007816013011102c140300c007002c450340080c6550303100003d40e0500c00c11650510025078000100020300e00c19200305405040361915000c16403a000d040603080101440b4000c051220800000d2003980e280c00c40390002c00a044441040030703585005943d565088003000f100d80c44000b1100035036010b20502c40340e0413203081d140004042103c0d450070b000254001c5001c1c981500442e1003d074041814032071018000e0b006000c2c01c0c01d10000801000162510341c0c080082d601e007007044180070030201580d0a00940360804424015500d80000007040003454a000900040c00030444150441d00030025000c1e0079071102161314281e07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 355897895 1250 355896645 355896677
    0x209090609070f1101020d2a0201090f0f21050703170408031305030d02030106050715060302062a060709031b050904110f1201020301140913030c080f030a0b01 70
    0x40d0040300c030388002485192080040512031031301d0300030f41c03810031000501e0207074841040310540310035a003038551242112041c1441d00704e0003080380d025950180b000f001103480c4c41c1d030745401245040c10081c01c0700c181c87c2003e07000e016801a20070642840c03500c06500c1c4a031079000c0078080d604420b4042e804505e0030a0048600048425814483d503803003a4603500e144c0d50040c00302e80104101c107041e030301440240b10b40502c040443c40203601819280d291030340c40d40c10034a0040303507204031075014560042c00c185040005848042c2a40c195142c000d601c505a2051000014900780102481010610502d401d200080360440d5003a000c0c1d0b40900c070000a0702e1441d42c7c03404100794061041702e4200c1074a200060120301c195000420030350000f0f04072244440108000740805291203951607030b995002004100204841d20307644400c00f416a80b8101614001c2045011010343c800080c0602c5485100141000304038421903191000c50300c00c00d500c80c10112450001003441e2884140811031112000f400c82c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 355899145 1250 355897895 355897909
    0x605060403020325120b0a0606020f0703031d031902030c0307061b2301050907050f060904020d0921030515100c0c1205161d0a0203071205070302090906 67
    0xd40c1c1c020f0020008108021102d030f20381c4640e4242e280d22045180c1e0085441c82d101c900e040c4210b40240203001d018140f2200c02d004980c0c1c41c0e4020710a55100362501804904003088441c00c81b43c15040c04220300080701a02a1303110301840050350b05020700b80c07000e500001d500f44813000c1a4001e404840120058005040e6500780071b01544000c0f80440c031103103a06280003800308804070301c00c0d43da1880100c032b440e11403c003c0707110007142c541c10394441041203054034040140c039009040446007010620701c5000410024403500360390f00e0255030002541403800300d480e08251092944500404a281d0490700506526221905900c0c0000e04100124454086c4e0400840c11103000070900c4d540440415030076a148102200100d960ba0b00150002441c80c00d00041c000c40e582c060009018011580c50301402a440a50008100e4900c0e803c0380c0b0742c562890440386a8016450480142d0b01d444807402541d003d044401100488c40c2040100020756074160050070358403a0940c0c0f07030314580e10340c81308004036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 355900395 1250 355899145 355899149
    0x6080606180a030606030b1e060609061326010c05090a0b070c17010f1d060712090203030f0901020c0d0b06130f05040f03090801021e0901020c0a090f06050604 70
    0xc02603061000306049848115402a2140700421000b84240d070f90382d83c0b00c2070390a60780c0107031181c0040c0c5007041082c40c85c001d20080c840035086c1080701e4901d400741c0051f1280c01859a41d500503140490707500c1c1d402c82a000c2c0403005c1c110001c01481d000d03400c1040c554454001c5c000c081400e5007014204030070b0380d019400b0344080d07120041400d0542401e0141410480c1c111306015903d1614038180001d90203c00240c0b05045106100040307084440d450036401540c3c0000018034802e008400344002c00b00c2d0102e90141c1020720303032802c800d4015507001108007600e01c034100a0351502000604507060952040101700c60b05003a020340d402c1c4080c40c130400807011b6480c40007034000c1e000706001075210b00d408082203440c00300c1c0401c0000c0c00c0c5040f040ba0b0084a504890483d4600d002c40d444400389a004040344004050302e100942c0707003214072003003501c691002c2c0c003030128129004030700d4044580c000d01c682c6441c01e0019041101041d81e03001400041c1072020f11401d41d0306d1030040301040c0d5003031050494003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 355901645 1250 355900395 355900399
    0x706020607090902090612070513081b010813080c010207141603290103080403060b06030c0403030309020a0b0a020c012a0b0a1d030a08060904051b030304080f06040c060806 76
    0x201d0701e050310f240080e6100c441e520364400003c11500b4407080f0b402030928051000ba80d82c66840e10902c0700144450300c0035800c030400707540c070160010b018141080207102c010764003031030031440036219a0850340a820384c01800400700d41002c114000301c4013056000e041210f001c6c1d034884403404281d9490707640ba03040c11001c603100c0045992041c404910316036800302c0c25043e03443c036400341000100b0030003c211400703801c102c2d00b24000060400a00c1280d000351604c00c0011128a482d40c01c000824510034402c5100c010706060301c032107d40c41990303542e9105000900486192a03941d0280b04402500c0d582201c00c00b9005c20030301c0e09820304e240d0840d0394081541c014291803881c0f855041e00c4070100740c000141284c501c075844201c1440e9081808000d80ca0028030f0800850b1603000c010b101520760100144014012101c500401010403170009481c581d020703810f442030082100c4040824154441c6801c0349000f403003a0011b0b03400015000030803a10450103441884100c03511010101c86005e02038881035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 355902895 1250 355901645 355901657
    0x71101110a060c1413080c03060601050706110d0509010209030706021609020d0609020c070305070902030c0f0d091e030e1002030f1804060303050711030d091404020c120c0706020607 80
    0x5800154154018451070f9103c0c02c00b810424030a040350320b0158402d00004002d2100007000f040400400c0103490a506021070141820b0300d0500002800c0340100704001c0c0002c2e4454421030b8400c20321504984204041303da040c8042e14100308801c0c040e40c01f0980541c000d119078000029a03d1000c2441181030f1416010005003070301e030400007006500041400240d00b50386e203d0006403810184000c00c0141c501d03d01820750030345903007481400c2405030f42c0040000b900420030411220f100300116155603028011813500c514861480314003c200003c0002c00600304100f400841c0100051150302d240d1090380c40c4e081241d81c42c1705001000e1801041000540d0062051900c10350f250300151201c0c080e82400840003054060008003a038282d58010f40c00714800082c42c209200048080c0340d06450190f0007002e10f5a050ba2004000750114031400810040450300c1c072a0542c1c4640403101c1014040f011659104081868812181d00103220040349202d0003a0004a540c00030504501c9181359445403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 355904145 1250 355902895 355902913
    0xc0503030a0c09150809120703090504240801020d0f142d040803100504021804050c0409050108030d0b0102060114060a03111305040b060c100e0a0f0807110111 70
    0x14005000404108001c0c0030090741e01140400d0240364400c42e0f00c4007a031740d4104504290101d10305042c1c04181030810781e0010003500000c2078200070044d040f204141c8002421600100301c8564085255101e0080f00b2240a0006210030054004c0e00e40980d01d0700b800c000d845007220040741100c0c810818500001c0b40368000030302c11050403070081d004540008100141004d010707519101c514003183d0450b5030310404414400408428164280603280c1542d04505d4148119464100c0341c000c0d680b0035109644a8000450b03215071841920020084030b0f100381314a584a54825072a908104412201d0f1403070810b8921407580b002400c0c40c1261804a198030320303244001c00707006050f0f000c01c215034241600c900d48400d442c09a54010700c10f2000c2d00300f195408600b407504020903551119500d5115603004d020044401a0118400c01036a004000c00140480c00500340da081400506000d420180d500e1280e00034460003400074007480c4c1c8038605605c2c8101e040c40055035182c11a000b0201d0316401203440d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 355905395 1250 355904145 355904161
    0x607050901090509180a081201050d0b16140f030103060f1e02030901150909051c02030a08150d0b0403121a090a20120108010b030c19031505090d0c050303 68
    0x10307139802210425a443c40300e98041030440c503014405600301d0380032800003030f2144c0821580354401d02405013104c08404084850302d915422003800f4103540c05034018511842d405601a003c981c41c1ca0080c8054151142c440c020500c4264100344002d54240e42403240d4015420540d01c1041803003241007151a40003814811a44000c0d0002491191a5075962108010702205540d4000082030401d4001c200910a850a02c2c1084a0211040264a814040c001d40a0303004820348d4030700c504605d00b0032103982d542e4003e80f004480800b4000d400c10307000070200c4180940801d000340b0a9000e0385400b41059414550310044440144607443d454500010504080c903041c05c88580091440c00c0c08243d510b4128504510405040e10080003001c0014040c1c01b00c040800d00c450042c0102c030020000069103601294441c06007024041c41100c00c04150f0220080031104003000d5600404c80008144c094481d01c5d00400741541c40310f81511592001c54033281c401c11005048560050141d8156200c1d045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 355906645 1250 355905395 355905409
    0x12050417070b07140709090f060c030b010801050f06130e07081501050403030f0e1e120106030c051207030c0902090109090b0109060e030f06130b07110703020d060b041b0206070509010905 82
    0x10f4a6028000d0600004a46429002e2451f5540c0039a044450742003140c54040f08951388070100106150030300f861000305a0b040000344d411900141c450b98220782e400c0300000c01034451110108110000e1741c0012947d00e040c811b0715132150003542c03240c03682900c03440049201c5100c14004103000510802c000e0002900c10099a00c2481c82070400a20303141c2c52100080100050f140d280d60700001401f88103c2e070307203000c03000281c0040842d0001c0098a08540311032211403164004d0500030364103a42c0001c0ca00e04200140f000558000c02802012078455410310f010390711000c90b550010b200e110002c18150f920303101c0c003045110140c60310441285015402d0750041c4551002560500600040c400c07141c1c014007405105214196090f40f40a01502d481c058106002d40010f00301b08080c2104005580c00180070015280c04541100080b000d503e07110002e810300c00103040d00305040ca03a031070030750f14854003204402c0c00e500c1c0c0035901c00e83d5608804441a001b03103202e96000604c03110f410446030802c00d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 355907895 1250 355906645 355906673
    0x1022109010c080c010506030709060b07061802030d02070509010b040b0307080a0e0322080f031b21090a0e060a1e050301020304080706060f06050f0c0a12050417070b07 74
    0x20400380038081c0b681e01d07038818940084000b000309945600410000745070a10107040600302a50b802c1010506007941e2030b146005180d4014407a550701d102420105040a8600415503070050444201254014000b52168400d1188078054569540042280000503090b2001d51b40361190742400c0d50740c2d0000458001c0030140580a41c02ea0b81c809040c0c03120340070300003041340c8580c90340c1550441c0030607880200858065070228645130002c800400c40c03400c02101300c80031403c211000300310f06601100d401d410174141c10464804c112061035404841c0f240c0030b014280d6103000300d0340c4641d000ea4407103195611080455030641d0000b0104010710094055542c5824120141c846001c8040c1e00d950100b403c80c5c1c81501e0035501c0c0000490000704002a0f40146000f1b091400c0c03012031403e2400760050151b01036000c1d41112100042401c030805201040070918454010a100030450035002001d0107a6000d406504080b150794260990022000141c0d141110a2800c400c3d103406019281d00c0c00c070304155 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 355909145 1250 355907895 355907897
    0x5101b0309030203060705180f03030a18090507030621033203010821040e07140c12030a0c08090c04020c031b0d1205040b0a0b03150a02030103110102210901 69
    0x1c0000310142e102006401e21031003d40e140e1035603d000850856020800041605105105031520144a0788003c01556412541c9040000c540c030061003c0c01708141e4180c2203444814a404200192160305400000440d460345600d070078105820050b00e5404024208094040345005881e01548000081c107101c2100741c0454145103661100403262890344203900a503884d44c00710840c15100c079034000d0f141d0b255440461000d1301d070a141402e001c024040040c020400d0000d5424080390002c5064125515010914152005641401c0804c00c1c20f80083d5841405145040c4081d044180070f0142640224000001403151201d40c0f400c20002c0e42c050880d44007240004d001400c8079540c01e0003490140c2207944090220030180840060a400140000002060402c0c00b40310120346d844035a260845400d0001194420f8442e010038584901017503e510054288001c01c0070500036607019505880c481d510404c0c0c1543c002004aa0b912035036010280c070304a1a4140310503007603002d80207002030001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 355910395 1250 355909145 355909157
    0x30311031501080c091801060906020d02060f07140c060403090b0f030c070317160305070503070e0409020604120b100504050108060a0f0603080d02070b0c34020904050703060605101b03 81
    0x50785c80400c503180d0100707040307070f800c0c80c4040014882190410310b14006000d5610003043c4811040300029074480d4054041c80c68640d02002041c4818454030002880c0400c02c0c0ca150707a00e081d2082040d45d01c4404071810350005880040c0445c101d50003100300e58804201e104114256181c45029204a500c50385080f01440048918082c500d50309081c110310850b082a083c040350f02541c1000340aa410040180301046000c004102e5039175000104111092402e0b03400250390314082c03001c00d49a124941000d000000080c80140c00c2200407040e4602c1803c5540403900410341d03400502054803000e00070369820b034112000081414503190300140080c4441c82001c1000c6589865080c45580300b10b011011040c1c00003140b000b8801c008005942007400440c5042c500764100c003000d04004484180c0588008074500b500202013018200382c0c224a40040502504c0c0c1824503040743d80d90458401212800d0400030001064500880c108041047d0780d116061020007000c0c3d501121110801c084043c020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 355911645 1250 355910395 355910407
    0xc0105090f0913030f0306030f030809160b0c1b0307050d050a0c0e0901050f0f06040c1101020406031b03022113120305071709071e1809030311031501080c 68
    0x3032200c4060340140c406144885514203c0e00300140390400b405003050900d800c0284c1080020b11403403441d8503450305031400030392986405490340d0410084064103000c42c802081c2c04603a03115003074020300c540e070070702805c40d10500c0f44606a6080c9000310440c3d540c1c140c019450400940c01c107005640070742d610503c2a11418001d6949080103003035250464000351542404005000c1002d2080e25041802d60f038042d146850000c050440900004000c03602450301c0e0032002c0e40b41809a01291300c882e032158002d54803170380c44d84001002003915540b80400381a0030307003c1601c0f140c080c2c400c0ba60381e481255201042c51016a004644a10019242e2808000c40310280404201c400c1c2c0914003503070560b41c0101d418107003440c00401440000c8070300e2880c503d1303810501c09032180000e450350031204079030340104007800081c1d20360000054562101c44500460b0100099404469001405080c402d88040000c0701044034190b0060001302d070300d0b540704004403019079000d60007a81c92a9210300030003100c2c0d25086d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 355912895 1250 355911645 355911649
    0x402010c3c050607111911190807030f03090905040b0609060a1409060d0f050601030b0f011401031104050d060228090e04030e0918100b030c0105090f 66
    0x400700014280c41401c555010000204185007040300340740492201030303041c0d00e6540b592038458001808000900010309164014054107012080f100c14140e198040c8820507801d0088140100300c0049200d0440110000a000c482c0484c50050701e00450040c030301c0d181995101300e004a04448140d051220003400010007007001e0050030310403403180000d03c0303d500300300b000e0001135840542040e20941248200707020b0003011400c460203403c42210207280030384070b02d008107465152409020f440c00b42d0030380040e42400000103509040341e00c142120199551117186004078101c0c28014180e1a5140481d0301d90360f50310a07044100d200b851981c0b258034065a071000142c10900400048500580105129401c01401c580c07400407407010b1004001d00000000d8010107070950360088103100584440070800b410300ca9001404a0417007e41071220340d06010080700300418018000107402d1244071480c5030003c80c04e02a250b10070002034000d0581c18020340055802d034020040c1e01d80c000c0c0071005003d01035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 355914145 1250 355912895 355912913
    0x112080d290f102c040504030503090705010f0c080d11040815060a03020108010b3f1e0a0e0c042a09050303040605030a0b0a080106050111060903030a050402010c 71
    0x8078101c1d19039020140044014480a000141803951007990b000c030702c4510058015080003000d62407000009640440d800c00100e03040035144601d9000380c6000c0401040503004001140161948011a12143d60307030001101e800f401c1c007254000040004e002200000c8100001d04064500ca40d004a462a50004402c01581065000c01c5041d4420910110700c4128104d4a0760410019244103204a042d600080c04124042c440d402d5018400a4012651554650000003000720014240c0d507074801c405049070b4005e07001c001d54200c41d1701140070070101540c14003121440c0f030703440c0d490b0300095403800381c0c03e401070200509031050341c000e001c0340c003a59030382e01c0c4070300c1134000034601c80b042500c182200455407009000c08404188504000d05015a9600201b924101e46031072030301d1030307490b81d0b581441e8001d0701c80d0303882864025920103004a0368142c10740240f42a40c50030390b00c0c1c0b800714050094042da00e210a6446907599002040071407900c1c4480d41026a010303006042402c0d017000035a8400d40703e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 355915395 1250 355914145 355914191
    0x2031e0c0d05041a040e041b0b18040605040c020c090702010908030a090c0609182711031b130b031e030a03060b07021c0303180605090d0201050112080d 67
    0x41d030024052244070940b001c2c60504c0c04a100c00d040c24641001d905120ba81d00c0504068024601c01f070251107880d030410025070242c000c80c2c0c0602c2e04c4102400740c00040c0ba601204040c400c2c1e040c22030100d05403c0c030784102e041000782c50780100f407002203080c2480040c070809400c110865403078a01d040042102c550003107020342603100c0001944c0c006410302ca03010301201e80120041042028041048403150500e45090340044100007d14072030002e42c008118002d15203c1c1501c4200328888418440c44002001d030720343e4180c0a80e43c0c81034003070910a402545070110a50b000030079400303040710035a05901c04c031600d500c06400c03500780160090952030b455544141040c00f5074000940100b4040e0716020b184014003e0035403030390070322804d41d0028400b0b400c00b80c03901810707403891017260041c54440d810548503198031949500178100c4a003060000f420046441c00e04a10034060090003144c4144501c07812140e01c00ca00d15a0003155070b03200d207510307484084282181c641b40c500ca07022462604480481d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 355916645 1250 355915395 355915397
    0xc0a0605090f01020105090a1419030c05010c031517030c0313140603040804030809010207150207030b100812070311030a08190c0e010f09120f0b010e010602031e0c0d 73
    0x244a102500810849040218a4030f045904000c14003415100002d010a02d240d4410000720504010122a5141008001c18500072a1507554117009060f080186008154002c60081c070083c040b054064050346d6282110f2140310b4800803003002041421490089000380d82400d41c2d02e001d103003140d03491454000070840418003168150402441ca66061041c07840c84040d0f46882c02d40ca09501d9800700340c050351001a007021310000704444540e10074405480a081c070341d0340c86907802c014050020764407100c9010480301103000744040303503d030b40c902312227038040700d0402c0b008041c2c4d944a41210041a002140101d05102c03140c451040d58100a2018242000c0c0030f989560300f40c40d00c1c0424002840c0b0328170522400c14500054181440d9005403482009802030070003694800c00302408440d03071212030303110100c008101100d840800886a126004040c003841c03a40045903250981240d41c10420b109030f0002d68010030141e1090307240760070391131080410805600c0c00c202d0003800a5040004921a0714 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 355917895 1250 355916645 355916647
    0x170120090306150117070e1002160501090f1208040b0f070b0105040506030a2a09020904110408060a0f1410080d03020403200604031401090c060806060d0e0c0a0605 72
    0x20350034200100c039030080351040e2000c400980000041d222004920900c1c000144020004c1d150b103004500c00110190007a140301300042c49100020b4a4880c607212020045085640000c1d096100311295000d6842c2c4060250030301e40340c50655900c00c8483c1c002101c0c004401d1000140804a00020700b00010603c2045642c4140b1032800002035072050b04042c0c412440c00c0240915601d00143c41030702158841c001d402440c0c90f01d800d0740c94550490b00b109044e040c0c0303104003250800b031580103004000c00030780303007030100b45d014040080b107502030380c000c41d20264840390000300000b1158000c807400a42d00c24000480c022943c5503264076010880350515100140b5408006c0314904021400510860345411410030741581e40701d81c000407007408501d84600611450401c10764480080310015940064a0140417042c00d0350217018111201c41540e8002c1e110000040e024000c1d045d0300d03c5094001d09441c07903d1110308186004045c00c00170240746209101c0607105540365083c0540103001a901d03070b6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 355919145 1250 355917895 355917907
    0x3010f09112407240212040f030e130e011a010c031b02060d0e120415030e010e0102040305153103030b0a08151e010608071101060f0603050a15170120 66
    0x2c0c0f40f1301903600e90340000030780f04001c2d102c4007840380405690070980c001d1744020000c9090804541010380140030a60000b1002510320b5101d901c0d0b4441e44030811f07040028003078021010781181c000c0a604800d2400b04000c03800c0035000904c074400c5500c04065603492211034420712b80215101c0d40040001072004d50f82ca08401014001c10400311401102010506c0c0c0350500702640480106d850303c50342420700d0340713400b01b01e01203030000c1d0001a08010702c18021920350b541c9050065440c0c03201010850001801d1010500001803160851202d4242c00d0202c40c054298680710251030002c07805c29404c06560b4140030042b907640825000081201300010001010b4030304428072404800303070101a04403005142007107003c01176204d09044608a00b41150360ba07950040640d04251300303000410055180102c0480e454006910083c195181170750100016503c401d00141104d14400d01c01c1c44a2501030402c00c40d004a00b101030a00d641321030004282c00d0a244000c119005108103184c940034404100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 355920395 1250 355919145 355919183
    0x8180d030608011a151e130e09030c0706080606160b01261009030c06050705040314060631020c0a050d0504060905060304060207120c0203010f09112407 67
    0x500d11141442c141e410a031031404400184900d170110f026800039500c00b240b540c007501111210360b0740f0040c9081d00d25036a00380444d0101a00c100c94000d1442511091010968207040041526054400c12005084407400c044056403d103100609240c0e1040701000070b40340b458060303403803442400e05c540035440d140e50505014001c48944010b03080300541038696100070b1801c1c0050301d00384001c02c00500280456140c103003200c803400c09500140907541000203103d540e5a10078000e004490151308142c10440d0064600b039180e281c241ca2007540030400305a4014840c070714403003102070640410302d03500744840c02c141d481c407da800c410714400c010303041100302c2c0052027410300c810080f04032545811450305080c500b0180400c04070303004050161001100203020400954103e404041d00240015200001038000500c00c1440c030004030f02030b50a00005400032429401421040c07a845121301c00d00712405424081714204101703e00f030801c15400d02a907c4400e21800503d1841e02034216580d04a0814003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 355921645 1250 355920395 355920401
    0x60315040e0f120f0f090301090804031a10030503030a0b0609040603111201050403090e0a02040b0304110f040209060f070c3c1202010e130c23040b0a08180d03060801 73
    0x2007580d4203038810401d000c1d0702803144c42101e03400700300c91880c90b40ba808084046801842e005c071b40204140e000050200034020b0f4081000541000382d01050111703904c00c4281c90884407a0700c00203007242e00c140041a078417400c81d04010000074000e09418100807215001409440c001da000740e80d0605c0d640f8007008a400c00d4416185281355110086c4002d04155400800070a6640301d400c00c602410004a09100c203030f50120b900802d85013408039101c2c10315081c0150700400121449101d000031022040403801e140c029540e607500c00034603040c10704030f4001c018941980320b00320464804480c003102050201c0724040c1c0311905043c1c0604441d140030341ca8540d9006000c200380c03000d858450003008110010b144001500d400340d083c40d1480016945101103201d101c40864003401c0e00d81800220400c041d48100c56401e164000b50f40d400c0714940b04030007000540710f14014407007403400070400ca040440c041d2600329004042e003000c80c51004a81e01a80b801e001c0701d9903d003000291100420041414240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 355922895 1250 355921645 355921663
    0x30a09060e0d051204050f0a06020a030b1906031e050405010204031202030909061c12030209211e070905040b040b151f050c010501080a0c060801030c05060315040e0f 73
    0x18000c20b4008181d58003e0418041e4003151303259140500c002804114041c45400000c0341804c080b21000409441c2c4000650001e01c8200002403400c0c0d0000014903143d1400c1103144140b00003460401e0608170b0440181000e18a0400b440c140311460030304011891140d0741c4120f00903000182c4450440c80c0099407040030100c0ca500f194000c3c891811190340b210412500140211041d0445100b861791071600480c808202518200e486d6503020202e940680003007056100441e95000c4040c2800c0304c1c030305451506c0c810003200d980401440340c0ea0703032004400c812200c120702049440c4a581c502140b402e68130102e808650440c20401804104600c8808032234110000251b0090a881240e003c00c01c1ca544840c0e414480e800e80e05185141180110308032a00d1800d110000c1c441c44d80c480c400c05581d520241030488810f00070810024825200d07800c2c450580783d002c001d1a226074507050411080d42c001801003030300c40c0c50914030140a5030f902d1080d08500e86424020b0400306054003011030504003c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 355924145 1250 355922895 355922921
    0xc0f061704080301050f040b06030403171b03060603180d030b0f040b011b0c150e1302030f0c071a01030f0b0601080c0d0f060f0f090e0712030c17030a0906 68
    0x140c0510001074000310070341c0c0c10355905032569400c0c004890006805403040c855490b411210010070b02041c5030f8000c41140300a6980d03071501ea070079110a40c5814004414a80d0749007038407014004222a8075100c0d00843d0082c1c07152030032103042441d502205040011005140c40403d0380e600c1c0e51a81414001980d0743c250004460401200201400203172011401150b1610501c0b00f86020b00b00300a441c0007881d010700328805014014030844030000e0029154040c02600c43d20400440680f44503070303070086038841d0060005000d003030f441e41c0d07500200c4c0ea000304004544544010424112102c0100380c0300b070086000301600809102a4100790344080006408107041004940403c8090b01c0c050b400c031011301c46074650029820060310000401007500e5044229000000480040c1c074181d1032800805030f0303402c40e03003c0000403420704419503694220301c204005540c00070303800c0d170100340980d03961841d941c0a58000203500410320031007416607000f1990b9034181a80d845c040810b118040c07080c841841c001b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 355925395 1250 355924145 355924187
    0x121507090308030604050a110a20030a090b03090a0503030c0d0f0608060105210d030902100809060703050c09040912020106120b0412020a0611030105152a010204030c0f06 75
    0x1d41e101c600c0c082c030005001e40d00803504e501c089862001ca0758400100b03880300c04100c0f0b841e030300f01000080c046250010410784031100385046402514002c001c85200c02c4880d02c400e61414608400040103800040c0615030a00961040002140c4180011885604013614079035030340c00c41c21041402c8403021111384044034500603090002c0d80700000d156041d01c204440c0e1070560621080c00c2d005068458003006020b002d6480070f0440540c164211855240c822201001d5440c0079200c100c4c0c509100300c0d10b442a5901c81c0002c200d00750b0080d13010341d1b000594081c016184ca43c20101150030b070b03100b280d81124000c00f150700008400707034284100000f4242c400e0382c07500350304401e485802d10818080c10241a91010601c01c6034071074005c100d80c81900f40d104400340304410121640c541950024030450340924038140e00301c0110a000710482d0300c106050800441c0c151511a4003210014080d80400030325907082101001140800d25035100074031184d01e00120450500c0300003019002d40d5200e405500517 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 355926645 1250 355925395 355925399
    0x2070501080f07201009230a0c150e030d020a230604080901090305070e09060c0418090501060512011b02030702010f0f020102070602220e0603280212150709 69
    0xd4080c14075241212410130100c48074078612005400c0c020a00102644146024000000c1288150182e04042440403032445008110140c00f0348842090000074102d8050920521010000074a03085d9400454174004000b18003107800320745048008500c840241c1e207c60b01d1030b800c01c2494070b0042c1c1c1c0c1d27010790031032612601c41c0c0060081d5507910142004004e40350110b1540e241d039100380c003014000e41c0c0200c100e80f40c0e180d82d02090700e40004c0c141c4000c2400d004081c00904000741400c102c404480301407602007001c0030840350290042c070001d0300850f0307035540314000054269680c1480703c2c0000e070000c0000444110000c10780c41041c08100c665029074205000c4040941e030031860103c2c4607015400d28000b41112800c08034020300c1911001080300c0d10205205400c414081140020544a00c101d11003454032103040180042c4201d9840390315034040c6480f451810204501c0c4545003d031040a1030b400000c1c0d6002070108801c0b8401d5104640c400124001c80300b683c2c80c940782e0030148d68144052624 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 355927895 1250 355926645 355926647
    0x6181218050607063803010c0c02010e0d12050c011d03090603090111040f05120622082106030d0e01080403031a03100b15031e061305040302070501080f07 68
    0x900c03845100b060b0100c1d0010074841150040e038002c000c0c021400303c03003200c069800c03035902d1050544604614502c20700c03440d0908052190400800d03d80e00c0d02c96400800d940115100b4808140b819001241c061182000554881100c03010400382c0d1181c03a1280443c0c200c0900b107681140d140200b4480180c0507400b00c0c007020007180d4900c01c0070355100c0d80d00c0d41c8422000f40500f542c240410800107002400041520158900c4003c1d604121001000d0448080e4525641c020584144100926127103581d01180110701800c9400c80c0f250300030509120f584400c3c0030311640e003004000c03000b035407280030000a45000c0c041101d14103101d05180c00d0715000c050008100180081005041c940d0304c2041c00b21094042e8801b0007140303401411288240c1e45030000d00043c1010943c060701400e400c1d81c41c1e00e048042c80d001e5074450310703082c2c070f00a140c14a410300e0300004d05c101400710b6410445880800064000301c1c0035442c810b42c000c3e0000c1032110f00e0080011700700308008041c0d000110f100b10a11004e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 355929145 1250 355927895 355927937
    0x30a0807020904030512010303020a020a0e06090604020a09031704170a08180f060703030c090801020f0f07020411030405060103020f01050a0225050307061205070905150d0207061812 80
    0x103501510481c0e8159142e00e802d4170a881000403900c100408100000201070b400100c2c0c041d4203200740c0d01c1c41007040c0d03030380c0c2e4416289030241c4501d5404a192800510745003050780c090300c0d1548151070300040441c0e03030b51526000700c58928200200c1c08130001d0240301030021070032a498014466001801080156121104940107031056120201150350500c7d2544d80d941003400040d0100070100c5580b41c040d460003800a000201c14034021501d01c3d2000620980c1c18800d442c0c40b00c005149042c90140c805d844050349500044c1c040760702c150350308441c1a202032010701640c4694031600c010042541140100050b00c40e80b00c4056042260401c8480e001d1075001c506150b415000c44c2c4900e003040c0d50000101200b0741c0d10341000342c03d4400c0000c0001c501d54005040c0480d0034049204004984510030211000c44c4103014280d00141c0a45100c012454090014000b0560160700182484020b5403942d09a07083c211007000e42101c20100081484040b508007841014242007002e421101660a002d103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 355930395 1250 355929145 355929157
    0x603070303050d0b1507140613032003360a260f010903080f2a0405040f020403050d030b0f041e181407080c120a0606091a030a08 57
    0x80100114200e00442543d4100083c01e80d0020603e655031710140c0340719012a00715220650340c8800c0c1500c0c500f0804e40c040b445502690351141035000d2159030b80c40a8402c40c1034400500c00c10380c1104921102401d0600252071101c14601ea03e00006003e14400380d5544c66908003d41c8007242034030300c10182e54aa08040c81117441c51300d0503103458100d030b001c07a25600f040c10120322000d000d071859a8481040640c8100c800d94401d840300d03401611412010032040301c0441e1540e420090040051000107504400d003005624040701180c40c2c5911000450141c554500030040c4c581d401003070610402c031050040036a0061a0306d4100300e4540d00400003004504598042401035030303161514000c0c8985014490041d2070021001d01000d001400c1408565118603800d462200d941d990503001080003140d520104c1d10000d0040001e1000300701081031a0b000c10040f03038170520580c001980002d045003da01d0080501190000ea0b0344241d02c800b91600c400c1e80007180c42170704440c8091001910311800d0383c0b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 355931645 1250 355930395 355930397
    0x15090a05101803030f0e16050a06030b13150b0c03070c0806070207150504120b0a050c03040b010501030b01091203030606030b120304091a09090f1c08130203070f0b03100b030603070303 81
    0x400b507041c180d0000050040006c1d02040740581100c00c81e40034480c1a140048035016546096295640d4604400729050002d6096210140b04a0200042c1c803640002c4500f61003400b1a904659031240a14030036888140001082e42003c2a00c105100c41c14031028020200000980201e207415580251a414680190205001301109594441e48900256406414541c034004000e440354181404c031000101c0c0c018074150b0404001030206c100341c0d02a43c1c0240d03808551500240d00b0a401034020b8044a002141000703180540050803400e614411104980640c42c006066800c065000301502c1c502c04525002e404010b0103131054620007c201c4007294555030f03000604021405c0400e11828a500350b07d98031031421414801103020107d00d01603041002012907103621014080700b0440c050f81a1800d000c1031480d000140342542c620304242206200a060b65001501d544280c202c01d1000d070454155400003004204203a01005900d1300038252210039141140380000000b90b8405450100030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 355932895 1250 355931645 355931651
    0x302030c12010e12091201060e0f060105090414040203010b060a020307030503091905060f0f06100f12051e0a051b0d02070b0c2101030209061215090a0510180303 71
    0x10740c008007036000300540c81054040d200182ca011082da0610f800c900b503000d200e007a5141201860b900c0503c2944219405803040d814a5a21480c803a100d60700028009410b11404008090060341c40b4400e0510030040e281c82100c0e1818507005041c00c5403c89038205014000c100701c081c1030160000252030003150715280141d40c03941c4038211107041113205042e0342100244400218200100880c1c1c0521500d10302c081d0300107d035600000210541025118035800c03030791441503480214800c204035031484415060541141000749032031411a20300319001e070000c030400c0321407146104841501a80004c50504188500c2c00c0c11000d46050400323554001c050904001b90742220211340f501500c01560308010b24040900c2c0a5941ca5507542c007010012100300c1070300b120556141c440c0605141a244c01811340c00c01036880000340044880100400480d602c60101e007030600d45510f03000c040c4a01d00da2170281c10202074500d004c40c80d041c0c83d00014041c05040540c40300581c2030380038041160036050b207004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 355934145 1250 355932895 355932919
    0x11e09050111030f010305060705040f1518230105070b060108060d140c0f031506040f0204091a090609040f030c2102010c0e030c0a171509010b1003060302030c 70
    0x14010402d0304942c250110020040040c1d01105a400504a1313000b030b801d840f400d5559240c111042e2080380aa030b07603039441020051041d40606c40300400f41d05600d007061960030b140c06806400c1020203500018407400301b070070950180b509070140f0b0f0082e034200703091507410415541d030313400c0c10b0038030085c04141080300c102e0001e11582e88800b0440704d80380c0c100c0364401e0038040b10000581c07a80e105207071081c0650f2150b83c2585190400184104902251600024158590408000280c0921884260340e03070b80901011803020514402d507095007000008901e1000c2200b41802190036004001c5880f03a600e5804020208050407035a02a00b5031514082684ca01c0d18607000c21420342e02511840320301c8031680c20300c0c80ca68055202803600145034075142903140c00c4108241d40c407218038506d55000b05486808000d550b644841002500d161181500d540b40140b41014440d040100c9003012580e4640d640d02040b820058611851002107150a2007514115000311b961080007400080c00b428810301c517 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 355935251 1106 355934145 355934153
    0xb0403080901150b0d0e01020903010f0209040c09050a1202151207080f0106022104050301110a03150b0405011808190c080118030c1a040303060e0702011e09 69
    0x130149840c03154a10080500080d840301d01d0599000c2c0f1110312142d4081c011061b00e5495900016158220300302040169003101c51408144061240d040c0800d807105c0707400e00706464400d041001500513900c0410469103808241c13009030700012400d000d12a1840807800e008040a6440b450310352240790442001e42428490300001d03a001d12680c1104000c011f413000c2113003020803611802d266403100860700f5250840c40242c0c005500058514080780c1500c2454042500c0761a01c0001c141080744403c045c0c40746019803814060300c0240c0141500040070414080e00105054031403e0046948082d10060104420bd40c1103040d10380c00f1440301414480e2041c800e0442d801c0b1541001d0703c1d1002d540e221001c84003a14928059110349609140721090580554841e5034002245890300122074070040001d0076150441e410b00281c15500110800d109103140c1c2844c40005590a0314a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 355755395 355935251 := by
  have h0 := BRFrame.cov_init 355755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 355755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 355755395 ≤ n) (h2 : n < 355935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
