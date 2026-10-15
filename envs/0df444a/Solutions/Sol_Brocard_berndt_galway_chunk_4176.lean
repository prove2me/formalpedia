-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:47:21.591634+00:00
-- url     : https://prove2.me/submissions/7ce5c396-32d1-4621-95ac-880bb90f4432

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 750899280 ≤ n < 751079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 750900530 1250 750899280 750899287
    0xf071e180b1e031218060a030e2413030522030b0f0414120a08040503070b0f060a0b12010b09150706060e07030b1509030c0607140106050d030e102706090b 68
    0x441070503090318089002196260b42c2c6030540942030300644401c00300d0304910f0040500740c80341503840424500100700b000710400c801eaa0382d5900707075107130002d00003019000942c2403010f8ec0786031034250000041407581a5060170b101d9a00d03a200c0d480c031a030032110741c04a01c0c072210a0004000c0700c4a20000e14a01200c0909594801a034000c81c0d503009111248082240c0345010405009050003250707002608064000362903d403500f440303d0002030545040e4051303c054200040c524076000d0640c1c000302c403100050101a4a0180d00d10500e81203001065030017294407442d201a080c420008056941c400c280108600349003c1e601c0400c864004c083d4403c2c5401d1444103842603640c07007074411130b40010b00443da8403103100c680070924001a5000582e045003001a41d2400c6c800c04400a004070f4071000000d0000c01d81f0742060003650700c07105000401085000d056004107143c141008100700b400c074034220704404075442595048000e0f4160491003074000d4842802559402004400680744080c0d03840e14 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 750901780 1250 750900530 750900547
    0x5040f0f0603110c0c1c060509010501060f031a06030405030f0a11070611030d150b0427150308030c0d020406050d060e070c08130e090f071e180b1e0312 67
    0x8030365455001d224418000703082c110310381d41806d111580728541c111038108802c1c130f40003064030300928080c0500d0010942d41000c0d2072000c0d1281c0034440462a4030502440e619100409000310340d00040d00c1222240070500c0b9041c0094031b014017803c401c543e103580e00040016540c80c05400c2c4955a044141080355070200381000509c00402c941003a2545000001c42c4090310012003c0d420050f0841001a0400580007521035400d41c0b20b1413144180302c0402100b0f40100d00600102c4100c00101b0100c1d090389002000420b000c14003456104200580151030020341045030070403640290840d0012403008900c8005042461041c24081d0560051003211400c00002c050020910584010305185002035215490492900c458005003a600c030b0000c40e07428954500c0e80c88400c9041060824403403020001042021002c090842d540038200300f516880c213003800e00801c0d2030500a010350741510381140c084c60740c454565100e110450300c1098160340c6103800c201070414840c06000c0300c02600500281c2c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 750903030 1250 750901780 750901783
    0x160515131101050913020c2506021903021603030f02011b020c060d06080703061b03020922180506070f0201060503100b0102100207061a19060f05040f0f0603110c 71
    0x7400c1202400e14039114041d0300009402d1a00b01400c407144180003090707111902200180e142c4000811030302e00040032000012002c08a56603100d0f810041c2d000807100510f007150414510300e024002c0c81030328142400c0c4029100402803603030084001460303424501d10b41e65828841c080440074000c0000011030002c0d080250349204a00145103d085c0c0011000040207403503100000804014060b03850055890521600070505a030321000c0b40300a186841420902c00d1003241c0d140000100403001c000054880140549910300680d03001c0caa0f03c17482c0c002c0300d01c40140d00d142507612881c010049880c01000040002032081c1c684070540e8146002070010307580100320000c020900a10002e04058140d004030303d4000300450303400009100042203002c4c040c3e9900002c6d40042242e0407051441000300c180115008d0740704603886480884103090291502c100b005900c1a061450b143d03080a40ba18150074140d0202d80c4031304080c06c7c000408020541d01030090906248040003a24107110710707503002a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 750904280 1250 750903030 750903053
    0x412060e060f0c0a030915060f05031513020406051e0406050d080f0f040521060c0324031e1605010e030618011d0109020a140a120816051513 62
    0x241d02c6000114500f090139100c0c1d44502c022641001d081711810040c41082c0303004101078002c43c01039a410400c089407e040005520702e250440c405010000e60750700c00f20480714141424201d910a4030713400d00140c03942c1e645056a85040320140b064142a15000c1040225040340d44850b0054805402d000046484c800958190101c1c0d202c03010396440d880030341d004080c8520b401a6a009099030b0f41810070b08040d40b0041c400103c914220340d95500e84101710280ca0200310f584c030303003044400101d81b200c900c00f802106024940140440360f40808059803e0000d06d505070f60710500e54440c2c211400084007550710403000b05020700300354000c019440003103600c40c5c0004000f504058818103003044421000d51080c3d4440401000341003d14402240765406420048800c1e407241d00000340214207190115104071640c003006001c0e07070f0001e107011408a00d80880c100705035140d600500042c0c1e80c401c80b101c04140b0072842000500003590240341c2841040a0281c074020362210403040f0140041e0062000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 750905530 1250 750904280 750904291
    0x15120a0b1509040e0708060c0403050607050f04090b040608250b12070c0c030507090e0d0206060604120812040f051c0f031a04090c05030d0e181009020412060e060f 72
    0x106804d030386000788501c0c0040ba40d218208a00c100300410003130404140c090010789200c0c03010b4903219100c2070f00454407800307043c20303482c040f40041004000d4041968400b1901c1da1001e0f001242d01c1da44c9034682070814042404020300382e414100710240460042042001510f4050001800c1c4004c2900c00030121000802c0a400c1c0170902c0c50039000c0c01214030040009503409400c40710101d4030b0310b26031000f8101d100e40030710451003803162034074075a1b0000c10080e1050030702038259070910b40b4103106401c8460f02030350180c1c1d401c08200500e01e190380a603045c69125a000700701d40c1601248915015144c01d00040040c600f0170883e00d94007413000c3c0e00c5800314030800c1da40d16010405040f50041100c0b154000c03001c0c1d5500a213080d84400c2003002c8109504112441101550b140d00c24001007560208104a0181d90000d00440da080d010030300022926080801c03100c8682405480700e5903402281c1c4640c1001400d80700400b0030000f0084030380911211862800098901820049409104e9803405004d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 750906780 1250 750905530 750905539
    0x406031203020f0717090406060305040f08030c09060705070f0e070c0b0711010c021e0703080d20161b050619180e0912042315120a0b1509 61
    0x1041c1000443d150b043d200d80e581c026154000100d941c0494080315840482e00074040d6090481c001490790007403052902c60b0f50401d02541c001682c0c2d54a0702c0d03450748001c0044040d107405120001190315040702074029035109400402440341040c01e0522030310f1043e84041120500c00d01000b0708c0c1507214070800c2000b94401b01284c01c544509106641e580c54030500d4843d50340c038008200b858185d00084c4111145004840c0d00c01000560348001d031226014000544090750070805c0781d08480240c5d004483c01d600c4603d1248103c0080101d0010950024500000000001c803a1006004100c80000542da035580d01d103400e03080c41c210214050b8051040412010070900c010680418041c2c1c00d601103065099982c8180503841e00e21464a860054441c54628410005508a2803d060040b902518012025100310072040c1c4600b4041d003000d40b0206403c0100320801d071451119000140140e002401c081a000b441c2c8005100f08032041d41705014860109000072a07040c0c1072070800c0710b80310710b000e45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 750908030 1250 750906780 750906787
    0x90b0903150a02031b1e0c010b06030f01030c0e150409050a15060911070b06100c0506010e0105131b05160218040302060c0910051c14010f05040603120302 68
    0x78140310700300d090407001c000c140d020089100842d6000314400d84a0325045905003038560f05030103c034090501380e424501c1d040c0d0410400003500e54050718810f001c240c0041814091400450500d41003074800b513218010600040c000c20040642072400780c40050051012490f1212100d010b880303a02d9000b0b80101e80c0d40705850240b0001780b100e10030054201ea81d44454a40464001b002041d03144100d00ca41ea14000211640b03424440803a440349d504107540019603181c1000308819162080140018088121310080001340c0c184103860003000000341d200050f42c5007006016640c50104128900a440c0000c111010b2401640784041c0c0c170745600d49181c681304100b0081c0c03181c824400e4061f5025074180800c030488440b145e1385910840c843d600f0b8808940303039140040264094440c4450740702042c040250210780c42880030308031202115850702c85404045004104840124000c034140a5500c40140221000415801e0003814161010000c0380e240d070721400341414410407203104064001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 750909280 1250 750908030 750908047
    0x60304150e011a0a080a0c1401051207050d050f040c14060c0a11011b0b060402070312150323060a1805030c0703021318030804080c2515090b 62
    0x168809541c104240c80200000b041c03180d1105901440c0074030301840f80c3c0c103a1002090301200480c0c204002036200c030ba440000c500700040d00e50038412003031500b8100030043c40004008010408454040c1d100c13500e4080d503030707544c4040303400658030014040c910844120f800e02000402500c2c210040324440381c501c0f0310b0f070f50344100020784600c80c000d603401581c41089040d030140250380320100c00300103090325410041110228118540400d00601905440c03074240003898a0400741c000b414031600c0707850024400c9201c0d860844c219402d0307641004501e1240382050040114903071100302c0c1c5d5642444690506900c510215079548401800b1003106500c0e104440c0780340c1030030300e03140c0b4a0917400f209481d190000003032a0b503600c806a110680c03040d90191048544820b4510505150000320b402c0ea002c1120940c800703496100c805031045a25890400950f000e10009004900c0700b210481d1400002050180c072100035003200d0340040c100180c0000c007a0b009542c1211540003226803005010740c44143c1f1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 750910530 1250 750909280 750909323
    0x2d01110a120908030d060e0108010905100f0207020d0b060306071b060e0c030a051020031515191d0306040210032a0f0c1101050721050a0815060304 65
    0x110343c40148148800705002d030751003105401103410f80b28820035404030341c1e980381c04c46c0d030030790f01c49110291564002446901c0c0c04101d03074101d403c0105a0030005441c00189501262802c0d100c030300107407003440c07042d814007800f454140a002d4102c01c09207032070340c50355044894000c84401d203030b00002d2145594080c80c40340c08a050081410a6100400707030390141c00d10b814540c2d1507001e0b801007240d0103850701598504c2641c415030b100b851000105074480c2565140b0800304149104004202c0d4841e40c5101003400c043c10210060903805001007100203400f01184c000740041e1440f044075202000301410078030301a107001680d694041e4040f44c1c90341031020320b203c003a001890703566a50700c40207541d286c5c0c1e51199491410041442d50303590391181c070139010395402164421300650f0024101c0c2940d4102410941c0b040d07015005080c09111680340c03440c15040d0364120242e0902c4100b000c00c4000c240c6006440d0400303042c80e445105009024603500c0c2c0315000502d14400104024403424201c2d0b1089107a001c2c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 750911780 1250 750910530 750910547
    0x606030d051c09060c030203040309080d0f080621100b011106072307030801051c0312020c0322060e03070b03040206071a2503060b0d0e0c2d01110a12 66
    0x404c40800c2003e519500390060181d402101c09402150307880d01c0c000340e11400010b16543e01c04080e600c648402103010301c03c035020300300601981e5011101404c9034001881c0c0c509200f21081c40f8000825004084da0b00c00801e60300c18100d1281070005030700745081e01c0100410340640c014814500803808404101c0c01d0000302c01c800200317602115010903080101900000b0b82416680200e03a6000020b500c02c04030170081d2000080207002403880c1210380344105486c0c01030301c1b100864401707480c100b2014016441c2d135003040130f00c0c02c00c40b402c541c0001c0140c0d43e00a420500410803d070040d03c0811300b40601e1a10314403020384024042c14000901130300340031800421861702c5031014031001c21424a03100c008103080c03c407840c0350f8055034050484034050303010744a4001100c00074215541400c001c00030301d400401c1c1403110100f917409031040075070080e40c031038008080004a40a941180c805454004201007140c42401e6051111002002580701000500c100e0800c1e8080c502c820304012260f4221003820 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 750913030 1250 750911780 750911783
    0xa1d2e0207210c2405060405040f03111f020318010615050702040605100c030206092e0608060c03010f0b0f030103060b0d0503030c0d05091501060810050d060c020606030d051c09 78
    0x45000c3d2213610503140b20104068000e500d02d83c28062a00c441040004070760f016100103203034292079400800002c0c09422004401c40110090751801c410721700c940f91204c502c9084103490340385e00000708400b55420424030420310600360300802c540da06200c55524401c00340e01b2064140040414407100310740c5c454001c1d0024083c0503060038070088000350064008032020000703c002d4002e1000083c60b0600000d04000034003010420403907400806031202d0400c100e03c0a070500607039103038080410a2101004a140108490071701d081e500e41c50203820440410b00b40d00200000d0b0010450240031007403120079241504d81048000a00024410004024410000005006010201c1000b90044184002d00600100d10780240119951921020703241d0201c0c20101041003284401480403920880c689548880503902040340070351100c000a00440d001c45e022542651a512640c6100c0e50600c00160841b00c140c009200711824840060b14600642014441449100f826900207022036006022032a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 750914280 1250 750913030 750913043
    0x80a020d0f050402030d0e031209060f04080a0b01080a0c090e030c010f0b1302120705160f05060714030708040305090a0b0f130b030108060a1d2e0207210c 68
    0x1901d590080800b40c038040381c00f64480d001d9650200701d00d6000d40116900114000c0c09401c03042c50210903a00d01e60420100c5d260008000c2c468002e804c10800300400141c01024000d20a03c03007140f0302400700030b0b01600502416041200808000f03410381c07105405030799507a040810284500da00395891802420030741d800304e42c01c0c4030340c21159821035400300d01003100580c5c855107404c81c07108040c0182d20075030506c01d00f00d0003c4c000040c40284180c014007070307800b0340d08d200180c100d107180c9500b082c0c0d410001d01500c2a411950900c01c0300da07009403249a4680f0700126003070844c54480006442104018005401d00400085808031035407450a403c0c05050344c002c4154803004005c0c004c40e6160030481000c49582c00c030010100c4c10106010959040304c1c5881c0081220790355150740f0102a0000d0746012201c60b03421a480107510506200000c0d08482e01032100d10141c0b0200d42041403000300c2412000f58a00c1086881c002c0360262710901d5028940700140d12580d01c00b204100e815011003813001d00207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 750915530 1250 750914280 750914291
    0x6070309081c1a010e030703060b010e090a1b0906020c012d030501080c01020c0904200402040b0702010207051c0f05030d09030f1e0e0d050f011517120a080a020d 71
    0x40b01503940c4454444941450a0041806440c0c01500c0114440001d2503141e40a0642000010204d40003162100302c18900b00740850f2002d400310b045da80d815658a010b070b58440e000076405291844010050a440d8503040480c14540440039441703d01c070440701410085100310404008600c5101103101001d40c00005412141850000b401084203010b074145a000d8040d80c504150710004500340c59106c0140800041e0725540d840010030340c120350018064007610050914155500d20141004000460202c0d994906c0d43c4002414220f01e50441842810047e0501580c04d070880c1c02003c2103075000050203005030035801c06a01c1c2d4018055880e070014185002d40341099480f441d08007129010751a400903001a08070324180e4245081e07804030000d6180c418514041c030708001c2c104406800340003901c58400c0d00e0b800250a581200c6203142c2040310160040049005c0d150001a401c05104003030400180800b9100440d44104045c650070003404601040c0582030640c111541c07200c46c070004208 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 750916780 1250 750915530 750915577
    0x12060f14010c0c06091701090507121b060903020108180d050706020d0504050319020601050310020904020c06180d0908031204051f05190207020a0506030901020d06030501020414120607030908 84
    0x45c0c090094a00c1c00b00644e030050079001d41405100c00881d80b001c06001514240071120b10100035900098402c6041c01c6440a4295200c41010010304141d0b41c8001074541180005482113802400b0a50400403000618520003000306010040980ca0310b481aa615503900341000a4003c0d071010352700746881c2100740410400c0020040108549a000c40006d5421482041c0d840300700910400c0c4e01500300c0400124130a150b540209203400c401840142042410000d0038034081080711450b03880b28a40364840d8041400300300e1542c00349194038000c4803803400d043d81a9241c0c01035445001407460b03942c01040030854140300b801d4551a10b241504181c0e02d02100d504068201500c41c0b443c3d1054455500d002c107000381c02100c40312030b00a082d59440a1400c0d042c00b0440d400105103035200d5600b48107100e5a9041400f4080040d070150001503155400c10494400120507102c1551107007400c1000707159864004100075501c55050309001a02d4401810300203410300c12003001c1e07415074a10511001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 750918030 1250 750916780 750916787
    0x1a0c120a020d050f09060c0906070602180307050303090622030b1e0106091d0702030c030f0702030c1014030402130212070816020718200a12060f14010c0c06 69
    0x500e140e002c1043c0501d4445030f0b030340030f43c0f54815540c604054010000180318007003d640282003004001d07018a142c04c555445144c100c0e00407003044a881c0c08000d00201c403521f02000510040c01c1c00310055850800c460b400584039100e1080b2070513442c0701c20b02c4400140040504038400a5070010801002d03840d000119400c4031804401408000c120760002094441c401c210403c140d802d4000b600c1041001e03c031140340f00742c2c401054601144030400c1080d0100318240040c1c58055003d6491b151115410310400d42012216155980a010306806444146901000340110742c920681c40c6981c80e1254000329200d2642c00c1190454680005000b6075482c1004640a200b00441d5032403001b6510b4441000441c422000003103001a0300c04042484400540091051450402200003071280079030f11207440558201120070180301c01c085640420603400240c0c040358229840c0e8200403580c14200d001c03898100900454a00c02c2c100060a1801c0e4060301003d500d85420486040d00c142c0d480c08000e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 750919280 1250 750918030 750918037
    0x60403050709050a060b070b090a23060f060303031602070503030f030a05090106050f370f0b13030b06010509131e09112209050c01030c0c1a0c120a02 66
    0x1c50720703e40780c0020941040d5200f03c03819134610110961030300609032564118200060501485801510014800100c441082c4020b4600380c500514003c0d0342d00c0d001e00d05040d4000c04180e040b083e4602080095600402181d610043e01108000f02d0001c4950407440c0291070b0300310f10703003600c800141000d40202c00400386100d0f0381918420300c90fa0369000c111074282c0741c01d44079240e0004210b109a4280b850119241082d0180d03109912110a2040c8107062007842d9000c0401032101401601340701b01c80c01400102c01130b000c40b014181c0382c1405200328090700c0102d4440900300d08c03010b40c04110705038130810856511030401014480501205800c040040c42d00c040711045c045d00e21850341055074294002e0b03040144d08289034200c0801200148510000446200c1207401c04414085190f1641403251051a60145004064111001c0d00142c1190403020751201480007502125000504c07806a80c080c000310200031030b0711900e4059202d5924000d10400e08a03510400080061b021410f038043c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 750920530 1250 750919280 750919289
    0x31407230f01050c070b09041e0c030c0801030503031b042c070c0305090405040c23090c0f030a150503010f02030f06041b1d0d05010903080603160501080606090604030507 75
    0x300a40074411401900c4500c900d500c1e2400d150012402000070245400280141c104040d00100341d0780e4600c2010240400904084000103036942c0c1d1021a19505104840c0c1c0b9080c00d00707140e00307154115240e00e42c1e03d0000900a220700c010000c00c1003421a400400e072070040840f015000819240c9107020b1800000c0c881000d60398100a030b00240c0c5e514401c40c1e8040305103400d5215103161000c46400d100161000030000e8072400c100c0603001602c42d84494124031704501d98403290442d200b081c030401240c03c1001d020401403450510007410700d10446421a03411500c6070000040071240180c02e4040b0f500e065006035815407804181c2c000000d0160020b51181c041421143c2403a80c8030400c000c2203410900e03050742d203244040714101902d4050120350880300e256600c03800750212070100240f5500a004000c4130140d44510450302056000307031480c0e40010f802c41c0501050312140c2c074418101d50140c401c081c1004840c1001c03c00e6a240c50702250000302002c0d020750b40e140c0e00d03810125911000d43c440d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 750921780 1250 750920530 750920539
    0x41a0316030203130219031707051507270f170c03030a0c1205300604050403021b0d0b07030204050a0f03020d061116060b030f01020c0703140723 64
    0x44040400e88039100301d034440e40049000c20780d0034800d41c090182c3c801001000d1034101060810100104060b1045280454400003c00d0703600c20301890485d040c5041018100403d0030709500341700306682c2140d0b48800542c0c0305c04000320b02038200c40d1125800a441e42c880004176115001c0031480f541030480700f4041c980380008545407926201d0030703d940c87c03065228050001d01d0034001040094840e004903040c000c0d10f4503200741054098442208140d4415218200e0020305082201c07181440600181c1d005008460030444c52902d43c401946500389144070b90511000d4003541040c5a41c6c01152084054010020010a00c1e10440203402940107000d8103100d010316142c0081c82504400c013200c2580ea0181400010b03018950b1a500a45092030340a1880c46041c0300c00401d000d00d215100eaa0346000d510301250250720710080c9810154616540c0310700c2c3e401081b20490802002403a00300300d0b43e0010b030054810003500d50081c18181070b501311000c4544480b80f400000c6c4032400c401380070300714100d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 750923030 1250 750921780 750921811
    0x5011b0e180105060403021005041a0712030b090a020a1b0b010e0f1320060d1b090b041a09030a03030605010f110d1d12010f0509120f0304020402041a03 67
    0x49185480c03801c244521a07001c0c40802040c0018200780c44a89a15405410443d04094584284610150716180d01146071040401d0041c14402802407421030490a401c0c1007240a901c20040307514410b004000003405038001034070b90000c511607507131a149070a41002c0c2600c2c8024030320340849803820071f104680800ea6004c2c08290010140311819004c0d01a403001c40480c1915985c44501207030000b5540407002c00c140300c40b42d00c280c407032000428041c2d415081c0010000c8589214164031002300d100305081268162040c04001c4c0038404460607030304c03150601c014a201c3c04112540c14400c0800d0685c0500a0030a03100405406400550944000342c036100848014410100c2c0c0d000d0340c00f81d11145540c0301680461000340201c0c002c1420008004082c1c04400d540b8000c100240d106092002480c0e5440e12101011501403242603000101c90025150300000c4141c400007501031001103400c4001c0000c08281156100c1d4100c030010440880114140003035500c0d400201d80045861281820004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 750924280 1250 750923030 750923059
    0x50904020706140c0901080433090c06030c020309040513023d052b0c0906140c03030726040c0e1305061305100e07031b03020a050d05011b0e 62
    0xb000b1795404403411b87d514206036840d0388403990b01545000e00143d42910245184000350442e4004004410f641c15000c202800c19290410110500d035100c9010540761041c01c0088540c04421214165411540401d04d5103a002c803118011242000c02944610b94103803040c1005031000b141b0040c0ca00070700d002c1540035030345e049601480e00000c0d0720000180c400c2040c0381486052411401849602c6000703404540d600c15600317412202c9141061020800351a0200f112640c4888462112480c1d0881a4100900200703096600e01001e0704140030701c10305691061010700480c4061440c8040c1511003002d90903d400c0c050114a140c0c000c40310302038210400a200314000c0058008482d81c000300a1403280e50b0201c0d04804000826001c9a0500400901a4148006000700807510040101820466207036140513220700d501c609003c100b02c4848401000541c1e1400c0b2040304071881500d081c0b840f201c06141c0f160060922076403c900041c030340d000ca010300e260301c07400078084e41c00290b90010301d05001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 750925530 1250 750924280 750924301
    0xe070608010f050f0d05010f14090c01050c07090c05070c0b0301091d0c06032d0610020a031707090b0a080f1005030712060209093c0a090305090402070614 68
    0xb601400e0340200c0d00856408580c18070022460500f4001c1d80002181c80e0400110b4050726044000070140154580910490701014070441401c80f10034203000e45410310006800d901c54240d881000d01946c4e0b503202d1000741e203015504a46984e540324000c4011582c9500720030034190400c1c022183c28618040c0c0107124002142d55404190f202d0000034054108400c00b0881180d02c0104202e1241105c03030382040f500300010084a400c54400d0403044032034a8a8414403910f4800820b840381190b1116000c00086a0010807028121000c898070340e41d260344d07590040c1c80c1c1d024a54808042c1c520005080076140d94030025080c0100816080c00515484800040c005c0a0407030150070390540001c002041003109064000c00848d108250240c2480b441a0010b42c22950403190303c8156907910034413510300311982c06420041c0c50a43e9410701c2441c030020760790780c19520090a905c411a9110681000e2600580c140c07112050b000304203541e510314502d8045c000c0c0124281d44d455441860000c1076500300d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 750926780 1250 750925530 750925559
    0x15010c08030106030f0f290103230f0601020109080403030c02150324011806080a0e0610210b04030c06060f06110c090721020903060103083006130f0e07060801 70
    0xc3c7c041404107190180381040c03c0c020441c2e1210705042d5074020030000100341500310440308070343c4803e032030b80c0c0e00d00f08502404403d00102207504591502c0c9803440081c4810080e10141c0350189000d85030603440c1c0c8042001d000121000018942c0e02008025010004080c4a074071000381440d00c2c880352885400554245111907191542c0182503041440f086105007001ca90142d6203030000318010100c1c2c02c20b103040c00c0c026038400946020519040c40383c40440040350031071a100145203141d510042c1c82c0d4940c85000500002c0c100128149810b0500034180c200001904543c245000c140340d80d07401c00b0746003403414070100a207801190382d6600b5510300384041c0d9215140d261100441c2040320706180d01c500e0600700041021950070f000713460a58804000c194069403090034001e82c1c0d15035405c0c11040402c9081c1c0d519952109228001c403081f0b5401d21f0480d00458203907000250b0024805400e030203000c4001015032a40e180c000700041c02400042c602c0d01b11403031504d0f0840d2a98858148114134903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 750928030 1250 750926780 750926801
    0x1502030f0d2a0f0e060706111e030c03190b100f0909020c03090904080c0102030103030c03202d0a121403011a1602091f0902090915010c08030106030f0f 67
    0x20300010600300c43c0da0149840041201e001090586000b080ba034407841180c0c9108000140709101040c83c0411120800714202101c104844060540c98408000342c0b16200060460a43e20100c075000130700b40c603071904551400100103110512031500a800103007103c10240d440d000040b90420001079240311442107603480900c41000d1071a2580c01d1050111084000e07001702c420380c004004840c1080d03c00c0c400355002e144280e80b0035219642e5414000c118148a441e400400340342e036503060030312120003d0071134022207980d01c0c0c0348108401c0d00034170b0001600b0705c881cdd00c001d4021041d8450800000d0702022114041701d40b103000e1703259800244031b03c55001c02d000e0344540e0704d82181901c800380022005003860000ba16044074812929030b002c542c100711f040e51016a140c0c00e40b15404c12034a121040d500242503010001c505240c0b000300000e8001001034042c1d0544009103620b407216034840d00c110108540c1000b8029a41d50b900c03500180100300070b013900c44105180c05071070081c005240c0680d80004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 750929280 1250 750928030 750928037
    0x1020105280b010e2805041a0d060612061b03090308150a030c06021b040506030703080c01021308030a020d03150603050703060816050a1e1502030f0d2a 67
    0x2500341c1d682000402c5107540c1981070040303440c202840b59503400c418810700e14600d1012031820541030101200c00d11140c200030300c144e09040b440811800c189451040e00b42013107440c01d03040e008504000c8000c080503004036141c00500c01c00c84051003215004201648034108814074240d01d102c500f241121a00300c00240003c0150000c15801e0158544008003032100801e0701c100d1650301d40d15100c03203074890380c0914096000020030050204a02524030004001a03074140141d00c1d0107400a81c80e925503020040c0312400200320584521801d5060b0b81c0310400700103000c200ba41d2a6800c1580d00d03082010008010f2203003055107800d051107070140c0010800804610200141080303020780142c10028403107000c01da59a203000030950300801406004584103600381d041c407420441030182c521055080882c085042070381042655564a181d070b421641c401e0907000300d40c0ba008a0480c1103105680f010301c0c85200208400790a030381c0780c0d03002c130030030092140b440341004086038902d40c0705414240416012 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 750930530 1250 750929280 750929341
    0xb040311010e06010f031209080c041509020307020a141c0c050328030608071503020c1504030e0a0501110a11010201090203100e120c0703060915180201020105 70
    0x10380180035400c08039030a1030010501c414007502c45803a00009078484a0000345580040062003900c06841000c6074803031600500a50400c01000d6444900c140c195008075a145041000440c02148a101804c0a800155500c5c00c003400000c0d034440550b501525600441c0840300c0003102c0004000c10b13150601601094a421209016a2502003100040d0380500040013202070020202c050a00034400b01e1101c9025407c0d040d200408454198119401c40c1d8490308090086d0500e14401e0080c425180c60f0240e80c1e1141302c0e41d42800c10440c01405400100b403481030004050704284403c070258401d803086058560f03039000444160b02e08000c41090390300105a45408541003241e4184039074410300000c61a800d0a901107441c200341980b0f10383c15140e070341c2c12030100e07444140b20354113903600d030700540c1402d0294145009441e028030340710040640b40d0b50007210042103041d1002e030b120340400f08010020f00303500c0c003041d40d0003e09081c0224015440d1000254a40058800b03c5041c0340004001b29038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 750931780 1250 750930530 750930533
    0x161a040e1e241e0301020d060e100e04080304050f0708070503011a180603010b0303071b0e091002180603070c0201090f0b1b0c0301020c03070302010e0607080f2a130905040b04 77
    0xc180f1420361082003281000790600385507840900082032903010a0500069036403601043c3c0a81c4100a4001e082d4000702c50810406104006c1d0030300c0c0c00ca504960540e0b81d0391501d2900d10b01d01100d594543c1c00c81c0c01110310000c3c4400003c1480d030103c50040e8028809543c46040c003d00c034132400c0613010340c00082ea19808501e04849280590700a0010300001602152140000c1c03458002040c1112141e11410041e2103051101c81040004c100103005202e25041c0455103544170916800100e20130396001c24892000c003071240c040e0140c050003400c1c141d80c9080940c80141b680601500c1a030100c2d001c0e050010300600400717420302c100c585800038107042c4017019003180c01d1800700c502801c1d65845084504442a074080c0f00804007040740400840c1e0310f10b541c0c81d010b03003550100501400c1c02c3c0c000c0d00c10090116017081d4055403110424207900802d80c6e40c00b0b000150101d49801130b4245040705001c00b1041da50110040183c012204404075465075034462100c10780b40104c4004100100901c003080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 750933030 1250 750931780 750931789
    0x90b01140405013b1006030608060601020d08041a010b04091a060d020f0903071d090a05060601030b0d0b040c061b1703040816150608161a040e1e24 65
    0xc240803000700c0d080c441c0c00600d0500c484c0c0d00c24251007503008109070500820100da01071040d80000c6c082c03400903104a251200c0040d40b10041e0400040900038900002003c002d03c5070300d90b4828840c4102d00600f107507120941003150340c00c01e010320980945800d140c1c07203001c3d1b0546810110301c0c9006004034031700a42d09500202940014035403082d90305040c0001001030707805002c00e42c040d100d10810031035982000ca03803009800c0e0001e0080e00081e00a00c8460780800d001052540e404982805c020640c42d50280c0401c070400003443c40075100d025040288410000da1142ca0000c5134056694802c1213201950042c80703402980000078142403190445038031401202c40036580c41802a6483c40c2015002c03082c0c0f40101c1360f0303e681112068952149640d0f07202c690304c1207801130320101c0c005110302d400c81c0d030300407080b003e29015136403e41304000c142158030100003003200c001e081507103010251414115200d041d01c1c881c005004403090b00c8440001c0c050110f1040f07a00b03040e4814100002c0d0f000181081c032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 750934280 1250 750933030 750933089
    0x7030629011101111206011701140121050a1406030f0a20060703020102130902040522180602070b180325120815040b0d02060f0d090b0114040501 64
    0x406552144c00c02d41081c00d541000e0700c422000105010098940000010b2415199003040065151110014090460298034a148802d0207091001c600e080740c5400007041c0144640e40742646041c03004011101c000c070340141a480f0085d001c10415a03e681041517258844070700c880e240d5510800b605804240200380c000c400400910441c06510790032300114a0b550b00022040e8003603034002036610b511906122406d0010302c0789890450505043c4400210b02c110b03054081032031203018a001c9004d0815030381c083c0c045c2190090f4000000fa485142401c041c0d001250251480101000021032a20b1414944132700e200c9000040c62521003000204540359850b101105803221041d0001d000281c0320580d804050306090b2950925403811040807401030069601c968015404c0540308625521108903440800ea03048803246d13160001030002c44624010200e031240143d0400300590f007409043c085150684852100c400000c10386c0300c051005803007081c401d409041200001a50142c0440e4046 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 750935530 1250 750934280 750934307
    0x21020108100321020610120f060e06100f050901031101051b07091413052a1c0302070e04330c020705030d1403070503190903020703062901 61
    0x1002101512502d40180301000d024080d16100342e24440c3c6003545804100d020b0340300882400c1c0d11041802c00d819281d002c14407100080c0404030110702c5104100158101c5621000030f01c0403200d540c54000080c1c41104520f05c40c00c000b0650100c004681828840d00c00c5058940001b94048044908401122681d101d07400c0ca201b032042c45c5115180f02a03050000d140100354031000402c09290807402030071540c0c4041d1401040c3c4494013520300c0004c50100d00710703100c8070803a500031502c128101e9892410256907010250310001c5201d16094202c1c5010a055145009900b2110550f4603003818100d0b034030341a078025041020041006901030712410290761215002c5002071011000000c204042c0c40300b0005000150b0000c0800b400682410043c0c00003113122440c1604a02c07031524090170103840f016059a0421030000300182d0a401811072000081a568804210820003400c0080d205c05e6240822075800782000c0b260f503035009240704001e029034040c3c503001c0e00d040c0c459001900c481804d042c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 750936780 1250 750935530 750935551
    0x90708040813030602121f03060c0912050f1203190f11120105280b0d06030c090c030b0a081c020c0301090308091507050f030a060909110a21020108 65
    0x1050b200800c0482a40045106090150316210207511400c03822000820900b1080600310690000700c01140110085a0308840c00280ca00b0100c2d600316035940d0301381c11035001458400503000402c4000600000845d10b88410354040c0c2000d034180c41c06038030043d0349849246007000c03c4405110b006600c025001a00d60f0300000f4140c41c010144107050300082c00b0710f40000c90a01c0100300c0c40c2040c1210b90018001d45244201600b14a5001c4402108500840c0a0004045104002e500080c0e100700c0166411030030120740a0307524410031000d001380c2d5a0a0300040d0405070300703000a040c1650030b07100f42e462001c06804005443c046505202e1513a00b625011842042e0bc8488980c400303200d0440000d0103580c481800d40740c6240360519080340c03000000c0d45000160200506168020150307a21440f444106039529200d00d03010001601050300310069003858600840d041009545584c0308902c0705407100003e29580f804a400f46030a00004500f03600742103504035006600c15242e1503800300c100103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 750938030 1250 750936780 750936787
    0x304030204052a0a120b1c0807111909180204020c031e0702032806050f090d09180c050c1209130e120906071b060e0f0907080408 57
    0x400150648209803140c00c10f0010781d07210082ea03a89080d682c4403c19140701e59851a00d02d0740b803401446025200c49049100c1d5443c4c100000d6550740f00c4101080000703c4c45c0704007040c01306d0b00340502e60380e100c120700f03c8440705a40118006800d03c4000303002114441468401d05a01d0800c18001509100b41e03462025411000d01d00010f0380d6500c0900074402d0100021604c032500e4070011111105504542160004107001640c0160380015041c20119040c20f2490800c51400107010101440c42000408013820442045040b038480c0c80d405104221035422140c0000e585142611025040e01403590500c0b80d8540c100d14103000e0b41c01a41211034286010ba1070104002101030410310f5184030f10480400001d581003191904408902e000704a05104005041640c5403440d981c0203400c10485002030f0105040c0c078140c0c0c40e5030a03154a0f0b0b802c41d041c003161042421402803062850300440020505080150301c2070708045500143d40e40e4042c01040003034803003000075124000b005000f241d9603441003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 750939280 1250 750938030 750938033
    0x105060405010c240c030b0303042d080a050c0108011403060406050c0f040803190914042c010507090f03110d0606030507060c1505130b0a060801060e0402040e030921030403 76
    0x942d0550408107140d4001031700e440711140080580e10300e018030034800d0f4070038030060000000c40441300d01c0c90109190f0090700b044581d0241e22400460741d20002c0c286c0100386a140600002085401c2490000d9950305010307a2108036448100700f0302c55000307030107a12400025000400c60740c8041d404c8524652514101b500c0c211080c1955407103078100c1c0d1100c0c2c10129107081c18824003050b01003004210304104110703a04100c0c028081c113100c140c00520032a2280090368078404041c440c01d2208850341100308103494041121401b82a003034540300002508602e00141c0c051199420f007058a6000c100d801a03000700f03c0820001017140c0105403000b55807403000200003078040105400404140c1c45480741005582040d03403090901c501d44400043c140010800c04440900030041c00c0c60b4809460345280d121000c000b80141410f4010f80915071078030801141031129030807520301c100d00c00c039400e000c0211441d901a40341c0c050b61403025040b411600f5652001c0c4a640410040b04c2603d100300c0c0e042590300d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 750940530 1250 750939280 750939323
    0x200408030a230c07170d050703030b0d150b0312160b0912190f09031109070c140a14070e010e07120c030902211b12060412080f0105060405010c 63
    0xc00f0f25002140c3c030000302009100c0b2266510486026000090305413202480e4000d0318910461200404040d03039a4007518003a95a041c400c0412508080d07024446020b951000004060304105103210344560b050b400c034407404070300c02c4a520140c0c40b00000354800a582d2070810000700948804101d00900211205180c0c00c10302920070002c02245000c64800340c4039002d000c6000c5104014204038140500303101107031400740c0c1c1d50018581900e8004160f0350b1020f0440c4d03a40c03180c0c1401041d03121140303c01650690009170352541a40143c142e0504419019407881d84c0c1e100ca88900c40301d141071000100007d1603010500360b80040c007030074001c0700962404a503200725040012014003017075071940c2c0d1100350704118569a14034000c50b9800315441703043c118801e0ba181d1010780c07008400c0d60918003600d496294140c056a44071013035001c403603a0f0309181c035114464402d140c5d80e20700003174540700001c1e40c0c41c4c0400483c64100c03180503110f9898182400011610380140e0b0340e05581d0407042d0300000655245 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 750941780 1250 750940530 750940537
    0xa030608030d050115230a02010b03011a1005160303050403020a0b100312050a09053001061e030f060c03020705150603070b040806240310200408030a23 67
    0x30072070b0001200d40c149010f401289101c404003104102440303441c0e04003d450040b01b24101030f60340c4081138507550074103412030242804076a8190194200f1b1204c02c18181040341d80040d44104650200d03600300c206100f07d1701806003511210700b000081d1014800303e8001d901c80754219002c3d01c140e41c076122850b250b08400b10301c01d4408026144400404209200801400280c9000546011131416014a100601c8070100740101446140d00f51001d000c1e02681645000080e680000320f58840d02e074841800d80205413030312403d0410620040d10140c0c408020f152a4152540401c0d1415103e00c03d071140801080702c00348e420117255007008842d0100b4000c109480400e0007100c10b4128603c0e28505043c10170303150b81d012a02c2c100050009003c840008141140c0c8861030318203241c1074005c420440b504e80074500341d20300c2c0c0602503511005c00d0755000390001d400412050320807040e10b8808800c000c1c0b1500c01c1c0d2240410340c0e0018462140c11901c10b407142c0580445041c0380740200f0100303007040c1d01c1660 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 750943030 1250 750941780 750941797
    0x3160302151608181e03090414010f08011b0807170f06012007030f02130507022104030f020105180a060e040518061810060b0c0115060509060a03060803 67
    0x9010034a0741c0c0743e41c00104650301000c0b41040240300c00100810f20341c2c0702d440d03603554040c8140072450000d0039803040003070b12960200104140b00b05020000351117507c44081c0561400f6000d110000302e01d6810500400d115007002c0700008164003030003d02140d414001030001420404094408043e8481c41721006010b06541d9001000a04041c000036049820041c0c440d034500e00030301003d03d00640302040c1030040302d0308450500900c00711440054021503000441605c0a0310b02401e01401543c0010b0045007400031280c400c80320807081c0302a1110b80500e201c000c1c00007941d92890030040d4420b00107012180c1c0303052005079074a0200c10000744160b49035003261000503440b1480f048545040d002d01038010034004004a5203e60b038040301c0e83c403520b00600314504800c0d9860b82040c2c43d1300411180e141c02c1d10b08502040b40c1c58686c041c00881d5482401400034940c01e00c8110350000402e0300d02038040b504251603881ca490805428844107420510104061554500000a01a20500003044c191 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 750944280 1250 750943030 750943051
    0x8010812030c18031f050a06180b03010e06130c0b0c07060c050114010e060a090525110d080423060612011e02130b1204031b02061903050106050c0316030215 69
    0x1000e40700170070400c0340d400901030700542d403c088081000140d05c244145880800c40e80101d000000f84010030302400d01d141410b03445101e130408001c0e64144130091036901c1c0b07101c0c50715020b14642ea18807a00075800340050102c010b40082c1b40401c4142e000f1485014090311035400855841c3c1c1110f44001016001d80c00400825000f80400a82c0e1510800e69009008007590070403c50408820000060b811307215204014080b0207094060103004441600c4995820701c1103032600340c5050001042c1c51000e581c125481c0c0e42495601840c1d00c0c0c110944800e0350942c60041203e80d030340001b000000308440301c1c15a500d558806481c84d0040c0d8903000c2d050b600c0391051001d80c0da04000711004010301559800405003450600c0340ca2048120304001640141e010301d0503011161410f00303240b81c00241c00038000c1d031000c070004611b8081e0007840e0620180707800c117890812160303985400958503440390310144111500200020843c0301d0552010307050440c0644100c426800c90320b1000c5040d00c3d825a9126441c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 750945530 1250 750944280 750944323
    0x3030c0105060a0609030c0317071221090201170c0d020f09030715020d030504051f092003030d0e03040b030c0408190201050306043908010812030c1803 67
    0x50401c012544000e15017890b00068407451502d07040d032030301141d0200500406212401c401c84443c2c0e5025214042e0b0024580305002071702d420003625980a2846100321034200307034555103c0b80c2d00e034883c44040c070760103846150a41b0441114110f00745401441c0304a0030100b4048010140980d20140c4140356001440b0390f95100032404044c0340c08001e5004005000f039900d01c200b5441e90102c0c95440c402d00318100800d107078480d86404c03403c000e01416038420703241c2002c210106130146500407035110340c00b807844429505604800851100362044403140c00d98010002c280d1034a0307140c0e2000750352010b52003d507820282c80e04041000d5602c15100c40080300d1004c0380a0059500c14482d01914501521008450080680c00600b0500008101d5442265111250308400180c2211862501021032500c0e44046069101c0317001c410951020000050300540013007800c030400150f2242c0384410b042d61078150350b10540320564541c86103c9582070b0001d122542900742e102000381016642c50303e000d0018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 750946780 1250 750945530 750945541
    0x20708040324022a010c050906030c040e040f0204230c0d09060c021f15151b0b090d02010e030f1308030a02061501180302102001020306030d02150708070e03030c0105 73
    0x1110a13031030a22003550f454030000c070003001e03001400c40d10b546100f921085e07101c8e41c9400400c4103e00640c1d0007031655049080810040100400c09001000d05c2140c00704009039900410a42d4540c174086100315049100020886a9148002412200c680304201040ca940180c1da40b030180c44841c60540c0c0580c0c042c10311520f54113048030301203085d594032440c01c00c9610a4110311650320001486102203100b184080422814030440540800a5064801d5451056149860100500200e5041009010312191580c5552045c080c1c4c0c09058100d0005604100440782888203076400428403030b0180810f80c800048c06581070001e09452107882c3c0240009180c4041c01c00188614060418100090380c000600781091903600760090300e07010750b540320300303903501c00d034191103007803600c0c040d5a0820860100c0883c40c00e4150002c40c415034041d8142c2c0d083c0a01c04c0c6060740c0c0c070001118080c0542c256200090041881002c01d6030340084d4928040f5500ca03070000100742507520030f02640c012079458108000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 750948030 1250 750946780 750946837
    0xe180a051506030f070510090320030d0201020f0d020d0204180b0901051f1d0402040b0d0b0103111c02091023131811041701060902070804032402 64
    0x340e00c15015405002c0701340d01141402e8450546001c2d2504c0b4503d03403080003920394469504200919842024180030809200513404441618900ca6100340300b0705c045001410b00c18025a0362448480215078200056894120065040000e10a803402c0e428000024004001f01c44615196000701000900b41c506205110035400e0580185020704001c2d04203840440c0d50980d401c040343c0d40c44ca0074444500744200b800012382c6070044001e51044c0046000b2a44c083c03500c00610094420010402082c0440350065042d90035100015410740c10605c484000d6103907001260495100f07030840103181141c400002104041e59044207400a1100c2d5048400300c00e40214000d5a01c1c1c00d0200d4074101f40803c050700e205170744903000d014141d00f040c031a407017804485504041c0311804000041500c41c0d407503907412250340c8040210700e600c3d9801e01074000348100340b41c400c0ba01d9040d00440341d1403800b41143c03100f81e801800d8044402040c0c522000c42c800b00300151000c0c0c54000088000040b0805481e884107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 750949280 1250 750948030 750948073
    0x114040c0f0b071a04020102070f171005010e060d0f060c081807030206030c2208030309070e0403050d0e15010b031e06090105010f0908010c0807081f0e180a05 70
    0x76201e142d42000702401052006a140064030070345403001900d41c0e210700c0103c0c1800c0f400e6000150008441034042503030001030848a11612610f01150300c500301c030300d0581c010f0340da0a200349a41d05444030045030960901400600c481801240c50310484000c9550f0b16003100d40308000c2c50f0001e000780c030900040000404805c503208280c60001d000003400c58001a52038030025141908280300001e100701e80c944040c961841d40e044510409202d10b0b52441ca00792260b00423540c1e0412170003810000300342c264103803250600603505550340b10700340700d05520032900512040e119481e140c410340012a02c035500008100e8060654110556240c0c00c0c0314144040c0c08801d54a0781c40c00c10b01143c10480e854640401c141e0443c0d109103010303140f000203e5020b407140700791034100780740039402c0c03020500e40660844162030080e5003e6844200700c0d560320a035400304194044c800d8600e141d06150800c220300305148015001303000c3d2026110220b91411030107103041e000c490210b82580004001114518284059 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 750950530 1250 750949280 750949289
    0xc03041a0910110a080c030604090501060e0a060f060f05250f02010e0d03211b02030c0715021005060406090204030506040218010806010303050a0c0812090606060a020705060c0114040c0f 82
    0x20f850500d0360800002c0c14522004110864801000c000103c003551035070010010250000006c004282d05c4800030281e40c10200c440000071420800006000301159200400322a8180c3c2d500e003514002d9001194180c0c00318441c1042400142202559610f1600d01e941209104490b1002a401c02e0300c0050a003000d400030340c5102d60b03019040c000100350042c0740308034840c50401c40720050b03d520f541240001c240c3c1d2810030123844080c4040d00300f00d640000041a0000c003000c21907040303664850040700b440088414850042c0c000181203d03220000782c00094104400a0002c5040768403070340400708980140d40113a845a1100d0180f10075420314080708800c1e0310141540b4442e5604111744142d03128018400101081400241e204c080740c81009078248032640045169a0b4400280303c0409940d0705a50303080d12030080034042540c0d464100c040781d85940f200c1d006440c04511786000c20242d50005960800d0743d5403544081000800c445580500c154803a900d401c04081c1000400c1480240c0c9800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 750951780 1250 750950530 750950561
    0xe090f1902031c17150a170109050123090a02130207020a0b0a03020a03050615070b040512031608090607020d0f11070f080f030c1b120f03180a0e0c03041a0910 70
    0xd8000c0d00c6d071607804580c0b0035038030312041c3d412640d00314807190f40c014256400064201e5181900c03050358103100d4a0380c00f4001c54000022052038403140b1035241c80740c049010095000f04404032402c10003a042d0083d0400030b000070445a401550f4940406541d1b0052403000b00003a400104a0141174042c420150840010384681032900300840c44a109803080550140ca404000000036041000c10807500113580c411140c0c4a8582c101104410700403001c0c500100c011409010010759561303000910b40348903441541c0100103419580000b0784d01c0500703c4001404004141d1515070a00707600704003641c0203044450706201c2c0039282c00980d0f824600850f0007107250740c0081140c104a0f00303001502c0024400039403070030b81141c1443d9001030036448040162040c5c60042c80c4150200ca58048041d01040c96003030700d4800410440700800c0407010050107100c88451262000c5801c41f0000030265500a2081000c03000012082c240c4040d203c0c02250104603984c069069504124140e000b19030034002d4501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 750953030 1250 750951780 750951811
    0x3010932060a0207080f13050a1431020c0f16060c081b0a0b070306140a0b070317131b1508040507170102040e090f1902031c17 56
    0xc08507511500c01400c640d200c10b0f0046520f00074014a401140d076000d0340b10540a5944800d00000303400e44506128507440340885120004400d024144100c0700300ca0008c1c2951481b403d050f00000e40903507010080c02011440d08003d4903500701034402440b00420314001091540041002d0b946003498500180c0c12104c1580000c020154000840ca0b100c00d071300203082d6071109401000d400c02000198014015840754912240511801c102024014500740d5802e0140903150003450304c0c8090f4400c440e0b038019442080401c40f84035601c020f810964480c5ca00424048447c1d5400d00c00c25000ba05c00c90011085105c4000170442003646403042240410601c0d03a40717914040c100200c901441c1458400d01c90881700103410850140b20450103494849210000d100300190038034002c2d000b80c01000104109400400e12003500041c01e000c00c443c0c544000c040d4600d0b2008890000d00c1203a904907090302c500d1034140e04c00280d020440000030603554805960101045d0704a040100c06850324116880b1034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 750954280 1250 750953030 750953123
    0x60801051507051506010311030103260f040504151e1403060f041101020a02040606031d01180201210c110c0a030314091809060415050c070f080702030109 68
    0x10038a0200d035070440c040b071300c61a554800141c01400103441c0b5180a4080040044100a94510926218024040d6a664032742e9075280810045c07180c50798040304040140020042d81c42c081c0c10503035011100e06441005541c0d034910444000704041200040000d0b2144144070188080f07840c440514422401400c443c01c1c02e1400d020500e0015002034480d81100184144690081240d20784040e405002040910366030003005005181c0000135840e44100003030b06101c103280500510102010454404200322030070703401595034500460031000208004480754105c02e0640c495500c40c1c8019072a50709070504802c410500f007025620f0700e640b003031030b2903001880802d90020310400012045c030b800c5540c4101c60800030f04290402103031906105041c81c10020f581402203000c60003035110b200d02d602c05415110b100010b94808136406032040310148054004a40304d9014800c16a0181036a2450100c043e0086401e540c415002030300c039400031040c0065288003082c42c116000c0300f260804040017068 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 750955530 1250 750954280 750954283
    0x40509070e0721111c020c150402062a01090f02010801060305190f09080c0a380a0204080f060f0a140604020310050d030f0801061b030c03051306080105150705 70
    0xa043c4802c6160340e000445000100541105c0c41010301108840103034050302c040300040e41c022940000c0a0103003804004001106403c0e103406654000c02c0c05080c04040da24074050140d5540f40310201842148070700a0102d42803192255840c000c40b030549030300390940009000e40806030302c4401014508010400c0520205540345082c1c50300303a80100c4c09115808143c4040c21030100040e1410348001113060340c40c0740021b400388086104001409140d072983c28110360b088844c0c0100d00c82035504043e01602000a0a216540800640c80050030a07864101151400e0184018548135078402000c1c004525a401100f50340819040000d02032004000d1915400f00c1c409008140200d4011001c0303688000c0f03640c20000070f40703c05880700da600c45581c05c5c02400041c0c0e0040410109540000219259120354420b803e0f004000000504209131981c00b1103a031020000c00b034041000074007442c007809180c4148507000b0600c5507a41c0285504140800696106510004003180c50030020140050320 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 750956780 1250 750955530 750955577
    0x1150305040302121305040513020105180a0e0c09041109010f050304140a030c0311031611280906090207030807050d230916062c040509070e07 63
    0x146004a2191982d2609918003841811445000b42c404101d40c25026480700017042114011a0f040c091a254000808016440404081c0c0014070030010340c2803900c070300c40c4014510503025018a024690760f8016541070344080d500c0c0300680300c0020b148201842c11703002e225000040712a13402e240c1040e0000280c03028040c62000c0062001c0440010300b4045060301c0c500c040260300c07090f103130b8006041c03900506c0308542807404c038045480140071355240034001082e01c68154079050785000c200f619481d01c2502d2100464900c9d40300380c1e610088101d07450082c03607200803140000454403030030742029841c4003900c0c0c058101c214107900c11300c138100100fa441818507800c40c01c1400e2040d600c070030352038044001e0118500c515800201040c05002440698001c09200c2c030403100584101c02450036000003065010308c1102c000030b50079011181200409a030341019203480b08061592a02d090012800b03494040f200d9480390340084004105000c421290241d203d0051300e4040d0100c5144010400002c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 750958030 1250 750956780 750956819
    0x1803020c10091a04120516170a02010e04150e0601140f0a03090212160f0509070915111903030e2e060b0d0b10030204080a080904060329060901 63
    0x50f020350311180b0880c4001c088501900780180c00c01c485100b141055a9101201a5001d10340c204c003a4000440304140e0002500c04020107000d8554031800e5001151010762054100c3e03400340e655091030102ca5580800900201010320100d0003d03c2c29400140000b04140c0f0a0380703041c2c004129021606070070700c0880720340303229600300080c84040c580045000a0100f112041c1544103040d880290481000a903000b1500c420603168081901e030010300110500c151114004950300e1102406842003911540504c01c0c0980f03441d031188032491401928210741e0a421048114040000380c080c07603850300411030b900600c10014851141c01d40c0050030f0f1400c810900b11082001c0b815010060001c036000000100506d0150a0704d5112580d0760310002d044c10b10084d8400c0045503600d03a003030f034040d000b628203c40d41100a007900c0c50007910f038200307a42d118050030360784030b51384200c0407000914100b80040d0002d41c080100060590b6000100310301c0e04c000c4c01c0d0038440d881300d0004004140c0c0c6200b0485030300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 750959280 1250 750958030 750958049
    0x60a02060a05130c0311090c0403260c1006080606030a02101b14010c0e0307050d020f0301020403021c030201050106090e0106051e03091b0d2109091803020c1009 71
    0x166640005072043d070741c48800040c500039040c01c2c00400c4c004500c13410f00309010708841c4054680c444008481d018859488010490000c560700c2c030701e2502c06402040c980b00e802541e41403a02c290f40c05900e0610015000c1d000101d56100c10501134414200101030740254181c00501010388a0307000a01d0382c24041100f0410403079051036440e20614220705010a8960041c08262542ca4810049010f00018240742001842d039515031580ca10740015034108858000e003245444c4001c0d9002c2c081029446030125800d076400300300c0000142c4030303c8904114061107103850f600134a51460020700352041a03002c8010003121480501c51400c038406090f044501600344281d0300c1c01e10b184406031004016140424650020080000ca90004290115403810168061895240708801c010129017042e20182030907444070410f085510380e00b850b82c07856107a2820a03042c90360b6200403541c2515018042c04014005d180d1400040580401041d04201c60840d861121440d9458004081840764401c10185 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 750960530 1250 750959280 750959291
    0xf02040f1d19111201050906030d0806100c020312090a1202030d0806041419060801150605090310110d050a18080919030503070c08060705040b1c150302040506060a02060a 75
    0x5400c00c2c0d81c0310400c41e0500d0302103035071150114010361002c1c000911807140075408504c0025a43d1602003618940e00c6a240c03101c82d030b961201c0c401d101500c10b524080c102400100c01d0f410000d6070b41003258120710350725890f0160b5504070b00e03000e000c0f0802155004150b003004e540c40100040e85c000c41d6290340180d0924003404207549540004000e040b106950845080401d428001000002d600d012000340d02d4481c2401541c1c1c1c3c0c0c04003c3d08845000c0705015512480300400d0055a04c511b0040800d200001c1c111482401d120b407940c811603190003040700351400005030705051214203004141c1d01100a04041081000c2044080340700f285150004001d0900005d449401d0f0342c50158403030340a0007201c81c0e83c100d5602d23843c10564941c84014240c811540da1480026038190002d25288220095503503503003441d2501c40035104940000b1152100c0d02c2e03005208c068000c103030784039208007900400408400c45140d801440201c0328080c000a018480070045a00c0494000035665000b10703c2d113400140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 750961780 1250 750960530 750960571
    0x70207170303060d0312090c08010b1c02240c0c0a05010c02100c05030c03040b070213230702190809011707200708011409010c0504050904060e100f02040f1d 69
    0xf5080290301036182030a00d07107242c40044c0111423054100fa59144c000810550b0030080410950446020240d2404c000c0700c04088014200b4240c1802240d070380c03491800035803091401100c0c0c1c540000c000c40302d5071b501040d0440380d20710b400c1f078540009201c2030a00228007103541c1c0104e078034803410954240c14440008600780030030030104110b949403c0c50b90300340da45071612000780b00d0103036001103400c1e807140d40080500c04d14520b0302d01c511059800340315296092889203074050940d10030020048425409541942c1c1101c2c0d22001142ca50345100703460050391884180c0000d08230304016a00304d40315032685010041405e8004951303500003214585014807981d41d403400c0a1800318241c0245069508040b90360b011410030301c1455019120340b0000380300742d14040c4801c640314011845035a0340320782e13401d0110303000c200203134080c0c8140500340d41500c3d02c2600b490251415030b942c0c1d00c240d1107020b9000508000e4864010030203800740c800f050090002c02201c841d9038030290070181401481d402c1018030110f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 750963030 1250 750961780 750961787
    0x50105031008070f03020a08010509061602071e230f010e1302040e19020325020c2e08150f0316081c020f07090c0e0612070207170303060d03 62
    0x7801000e00302d08403000c10362101c0b00411010001d1100f00d019a2203104085489034040c02114403503500c4c6c40043c20640d5485940304115007200000f5800d501400402107030110071000804004e881401d0345414161801002c0b03600e00219440d100740d290660010140301d42c0d900c40789070340040c40900e4a08420560800040c000d070302c401030b055071072070710000340041c4e85c0801e000041e10070080450100306000a0340d604100360322044803400011a01d844241c010980007119002c0550040c4c03040b50000da40001c007040d4110801d5507441c1c0100f880940e1080004440d1840124008a500d080704080c10458042076103042c126890f41d2241e0350214107104c207520100701c0003000182010065100c00d40d1000b030641c448820300307900d0303419984c06075072202e20500006030b140705d10750760300c1c01444501e01c1c01c01064004c043c4000508200580f401c0b180c05166104130207080d54484070402c0d2850350501200180c81d002450b488416504425880004525004000e80340d0007042034542d007014052a01c1d085 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 750964280 1250 750963030 750963061
    0x40e090318190302011215240f05030406020d060909050f10060e0c03280b09010b0a05030f04020a051008100e01050312090a09060b0703030507032f0f0703081e01030c05010503 77
    0xc16842489900080e420ba03012050388c82036002d500310021001c090740400c81c3c2c400e44030a01c0c0000b0500c10408034001454070740c001c112813041ca40000031256150b80d444000d1b1012104141c54603400f081d12200c110805015440c56001440300c20040e83c0c0c90325500c0000018020b1010589801c040005984420000c1d0002403440220300509075680d264032618000345001d40c000d0b070240424400101303802810004541c01c596481d12101d04640d40d1145102e01c043d8002c1080340c2008141d5000145134644e00c00c81c001c0340300c454841131402d2801500c10306082c40941c2c05210107120400c0104031903280490350810b24110a040c85a03140c0302c41000c542c02800650110300054903222000604018420180140c548281e809000c540c41c1c4200480a9410041d5120f829240d5001d22203c000b480e29002c0d05a43e144101c441d0400410180c400e031140c0215600307601040d620b10030403182c103a01400106a41800b540504425415525200f1f600000d500071107050002c0000421800720050742c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 750965530 1250 750964280 750964301
    0xb1f0909051005120d082a1303290c0301030314032206020c0d020705150c0c13020403020a1e03060c1808070503010f1a0f06040e0903181903020112 65
    0x2404134444480c0fa126070314040f0aa0f0b0000040b99a00070914003154601c881e020201d003024013080900401c0700e003150b55401308142e1100340000c0003000000a00c40218400e2070030021078010980350840c0d065a1101600410015401c0d408000502c00207030404032950f80d040c20b0f0508103403240e64540c40d5401703171381c10b4544440320f50701f40040302801c100301500180316441da018265480c0500b01602070380c3e208803e00400342c1c041c40c500c2180c100f21100300080c01c101001502120012400640440c80903280d80c0034148949030001000c1c425400c0070a0300e14001c0846102c4881103002c44076000c101c145550100078035032902c0701ca0903000d4a00c5455440c80510074001e050103c2640c805041da81d801091013280c0c001e5007003101032902c3c80c18a215001c0c48090411142c0303e000710f00c00c108600892115074035544240140300215100d109400c5046c443d00c280c800a47d0340c0d0250642c504c5400e13a01281c01d900c2415000c100b0403100c0421100030040300c0c0d0a0030044071003000008030f40041d00c0e03100c20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 750966780 1250 750965530 750965539
    0x12080c070b03040201030b010e01021507050904180201020114010e0c030a0b180f07090302130c02010905030408060121120819020a03060f050105070506150112020d0b1f0909051005 79
    0x4041800301d50303640158003441c0300340c0f8208103000641005552441e402904d80f800b6800001c040f0781260100b00e0f085078026a00c1c9001464411813500044c03c48d800c185490805100d00c560b0002156024440d0702d0710030014200551407585480000c10320070400520884038190044007207210343c1c0154000b00c3d8080c00081c4104440a42064814040030007112900c010540007400700c1d909500410900042c1d03500a07188440100544280300d029281d0722808000b103644c1d50507004089141400036102514032503020b001d465240403400c52241c0040315042c414003071032085010000781c403040054000c0ca910b0600300060380e00c9024100d1803284110780c00b0405030000030400314035685907016005440005d080c01c0c1034541c48800458aa0044d0b44006000c3e9000c01d0109000e000c1c0000d09000c89041407601c40000b0001075004002e0340c0006c0d0140c006152604186810307450000c0c00c0c0068840454004100f01c50b8482c0000c1c004c205a03c1960b41c0e207962000890010620396003560f014010250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 750968030 1250 750966780 750966793
    0xc1b0a1a0c0d05090f19030f08070309090c0906080604091b03020307080c06090d0807080708180f0306070309080d0c020309090c0406090b160b090f150f0112080c 71
    0x10480d650070750100a1031107403400345500c220030050080b015203d111340d02030001a178800e0480248148203034102601e000f010784605c000000581d064a011080070b00c952880d80c1c82c0c0c10300340b03005003680241d40c100f01c1c1d0060600d00300703901d81036001841a0440c0c0071890b02c021243c54100200d4000c09068070003804404d4042860290681c0040ca40d20840c0e2080d001c550f04181d03204c07159910740415414123a4008800c100c405100d1901c58618101c0d503025040c0c4614004950340d03603461a503c910401c40750500003007458000542051440a10880305a6440445420620009444101c02440002403558404c15003052043c0d036000d0790611848042c1c1003200c1030300594041c1d41d9401200c8036502c0f81e040b030000500f121490f041918101c41d0652a0300502d00d080110f804103d400000151b96009411001d100c0400c80d0280c0320303800b07580c40002905502d400c4860060504217000014407054007800240180102007820b443e04407084d000d5011414082450200390790302c0703a51112000751203400b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 750969280 1250 750968030 750968069
    0xf0509030c0c0303030c071704080d02060601110604020d06050703200301030b060d0c0605030402120610060801050d051209030f031801031812030b060c0d0c0c0b0c1b0a 74
    0x140346465800c002c6038441c0d0382003001c15aa920049948842109081c4190307400038a035948004000d6151078242c03400c01e40c88a100d603242c02980305c0400d005a2106090141c02d507003124040c6a0710110300d01415862500b074000c1403000e0100b12000304820342e2200010300d202c1c4a41e10030b407481d410340120303880700c940908003030f6065820a0000f611141c00e40d101160280c0f6200c203421108507440f4611000b0323685002d0b415260740e04024000e90700012070081010302c042041c04078900c034004095560400074100303c001080d220301600885d02a80c00004150040740700000d88182400748683e0f00c1d66281d1403400460f09000b800038102d440c0303200224808168504485001c4100c84003070741e08200340740c0b21440c64000214100c0011780b45400c0c44449103036140c86134000406c05080602103501e064000407209140441e1803002600048144603e8801c014110b0f482000401041060900b13100c909101c29444079840f1031000584118907880309440c2c0c940c000e42200a141b9200d01c1c40140d07210707 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 750970530 1250 750969280 750969283
    0x190309150804050d050c19080405060d050a06090c121a040c021b010f050a18051f032421050d0801240504050d02030a080304082d030705030a0f0509 65
    0x80d1011100d07809941ea42c059010701c22825904010950401012003541d85400342c00311411f44402512940c0d0f0800c804030f405d480740300003450307403840241d00042d252270400140401c030356603a0841c0c0c0605041c0b0030098002644003000e2000d141d5510000641100405d048201d03c8204134010303500642042002085a6008550904190710300e000c40740c40e000544004680015103030441c2d41c00700d0710500c2040302942c0f20b0300480c207000c4040728050703441303c3d02c1380e00107501880c10101c020f810342800840c0b03403c80340d414000c5500c10b550007000900700360b41c02502c00040c00818015500e064441c003002c03041c542c001409007410039070000d0585544000020009100d040c0c2401100c000240d8200455403002d0000d80c1c1003150f1031543e031070070b0402c2c0c104000c018455078000c505a80c1886629644400726004000444c0a903104052041c0d50b000c00c80c031003101080f002c500d2640b50307101c00c001c42d0007038225a1048aa2260310351400941e20ba40e0100d000d0024040c0b9441000c42c203141c0b00402960040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 750971780 1250 750970530 750970547
    0xd02070215220b0f25060e12030105030a11150315090105190608070c061505011b050601051005070f0b01031b081906140a05010f0f050319030915 64
    0x11108008103034070440b2100c0c2c254401052184940751242045450981403242020303191103d840380c14031401e5038180e050032002d5484030700705545560355041c0c07881290b1000c001c41d0408811011840b41990314281c006a02c5500da0314014194007203420343d41c00180d0300e1107420000ba184405010381c413401c03d00c5a4502020300b92071003500034040140046003a1400108a8000750161101c03114650708103501100c8201e0040d280b0303814003035003040340c1d000a00384e03004c0c3c2801051301201c1001c100d442c00f400107140a504030015145e4000034000d08010400201d41e2a0640d2410f494001d5407440010703040300c1921030310360044d046c03075404108d1004112565144034122401490417425030854130705c0380c2150800900c45e070800c541c0b040191982d51a001d40c03080204070f004e0b0760000b5400d001045c1031404c014003203030809001640c550040c407411500c440700c080a88a4155142d00c03107418000841c1c2c1d10a0000721040c1c4202000c2c103404209481001d00c0700c080c102c60180314000f03103404003003d081200b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 750973030 1250 750971780 750971797
    0x901020d080412140d1e060902040612020f1606090204050f06010f0c051510171b06030411120102090405090d0f201b010305090a02090c0d02070215 65
    0x1400364680046101d028240d00031508031554040318011400c06961046442d4020346802c0030070302c5812401c3c1d04500c0740f520200c030026a489041446000c1040c211803080e00710240961041c0310905c10540e0010822104800f5850010f036201b42e1a00203204078090203542d2034a02105080707402c02c118182d04100300f80c0340300703680600c029111980c0144d104201140e445000405d00c8844c01c0c603041c880c01c2c000c3c4040f4002c506450150f0b43c1c441c03032026898230407203082c0071241c00f920341000100d4016002c0d8910900e920081c1100c2d000e400100ca1400314524959842840c010020409014545005a37141a8010040707003400d5036410303416001c2e400480805115078a01400101d101001243c003034404096030b0344400c0c88107240350003907980b081104c01540c442d02510206034003018007041681d04a81e04020034030320600094000505039500148080030301d8000d401441c0058543d120307000d4100d5240681e9903111000ca0a00c00000d00079000d000e0347c40203039200709080310f11018000301a000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 750974280 1250 750973030 750973033
    0x3011a0907030b101b020a080a12030c08240a0e100806040203030a050f1207020a15020a1d040e0111041415030402040f0905030a020d02190c0e0a1e02090102 69
    0x1940c0d9494140c04980a059003550004004c06107070b44003900c5074041e0b00405031102c000074010002a008210040d01b00d400000550b4040480388090001400d40c100740407902e85414000c6200628004100240242a54070041c1404a000d01050440c102d407030403140e00500910412540c4540e00032030441c0c01c0d034010901849421000c281c03c0c4000c12401d10464000e4001c0d4645103171614101e94590042c21240c04008041c01040c1d002c6800c00b03001402003520b540100300f107a07118240351142591a0560440c4c0707a20403c41d0720034554006410070720322a82500840c2d1003034250700c0454007070508000e01410a518203004541c447c404400a80151424003207000344100174401804101d90009074000c010750700074000140146069040101240c4880d08081080502640e8641c6103810010b4001c0160b00101c0c1c070746250341c0d8104640100e01c120205110b19448040d1070f40d202d519480e00440700c2800d00400011028051a00298134401a5030507442c00c460080620070000d40140d0304e4180103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 750975530 1250 750974280 750974299
    0x105060f0609090417070c03051b01081e0414010c050304140703020d060e071a19021c05390706020d05030c0c0124081509060106140903011a 62
    0x507820104142c40c00400e02600229042c0c079180c0310b6100c540d0035040241020b910030803401c2c0008007d141204019032141000700050038810000940c06400c0d543c0a6040000420410900381489502501c011070555404003031504c1c0c9003804062010a100707000700035800d005684203a151702c18015031240380101c0301a4024160400e8590f162010b51001039441a4120314020102d40030307034480482400c110341101d40d940d03900c1c80f8440c810b480d803000803240501c1c0803640719034500b00450008901c00c0c052024041c4c50455055105e9036102042c010810400041501d183c0380980c81180c080d484000f036188010303030401d4200540c039204c16021a5050340140c1c10002003960000606d0105900e440e229541142d854015009280c0c101c40c0700000c2c20f64940321410a00802d501520249640c0105080d5019060400841c5440c1c60800030300c80e000d0200003081030a04010030070505652540c540040d007030120011081040c014800e8141c1d16503e8420303510520049040b406540d0b42c01545d82c0010b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 750976780 1250 750975530 750975559
    0x30609020f0604120c1d0f1911030a0b030606030d0c1e05070f08030a05072a06080a0606140306010c021219120c050d03050705040905130b010b1602040c050c010c02010506 75
    0x2001c82c0c6c42c0748000100d0105403064042c00c170042d4014601c03104442d00d00c24002600742919900d101018000c4000428040b03011001d02502c01c440409900804442c100440420364456407400c0d032008101440050008000b101b224100c83c990710700c507100300c2d2240903050064540c1032604c103081c01608811000940e842c00802510801c0901d074803420f00341000d41c2c0302d140a180280b04411606150307000140343c650110301026003c0c00d05035440212501d017403c800b804442003030300400c0034009801d21038107104594504495000e6000c0c40c24503200c80c01440414107100307200504004a0158600302403000001e004500492802030300c4072030407400e400324152901c3c42034034070240c015040700c4031000d0403074000d40007990401e80070303c1c00c185055554007504040f07481c191803100607080c0d00d020320401d00070200041030240078074052291400200ba1210b541540444030001e008640f07401c0c40a0040e8050380c2507446902200c002401090f51541d0000d0007040708440c15481100c0701c0803c8117 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 750978030 1250 750976780 750976799
    0xe100513232e030f02030709060f021b0d11090702030901030f05070e10110102071514010b030f090304091407090f05012007031a070306060315030609020f0604120c 72
    0x5002e200507600c09642d0310030301c0041590a0198100341d0007416181e9094400c9004a44021445240704d551070b0a034250401c08001c200810160000d41150301c50700c0c141c2e00650704001541080d44040780c6100c1600c24074a8001040704a100e9100c1d845030141c401c0215007500400103008191f0240c1c0e0801452140724120b0003150016510400020050280001603040800022503285050308005118182d90480d09003a42c1c8900011203502a400c8005c0261580d0f500607101e84102c001c044040c20342c140005500140802040000010006800314102d01c0342481190080c0030461002e10040c01200c0000b010007401360380b000c0c00a465503900040050300003081c10f0a45105965000c0701d8011103031410140d403006481c5000e00c1c0981c1d040000003440b001c6005000e441c0700580c2c940d592409175005011209240d1000d000c1c141022041c03130046141c00712550a40364440000180006c40b4004902c405034a440442e4105ca0000384c04036500c644c001032601c540c0d104600c0f07034903d40e45030002ca4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 750979280 1250 750978030 750978049
    0x30c121e0303010e01050904050c03160e090304050d0206070305160b0906071e0c0201180924050d0213090b010806090f03071101140d150e160e10051323 67
    0x5003204c409190041c0800d1400501c0160454086c00c2100c04240b0a01e0020341041500b081e444240c02c412042046100c1c5004012980142c500018506252809000c140b0324031403094000e11440c0000340d4030f0101401007040d0b0701040c4030300c2841107031031a241ca07056044200c00e41d0702c0d040b10300c41c0c2000126402c0c1b00d02c0003800000d480c2c2040302e1101d00c0c01c103c1640d601249000890510201c2e5418007065040521401c0080000480c00700e000540d0301105000403048c0070307000d180c0b814000c1c402c0c040c6071611301c041c1000d182c2c1a11844200300c09400900700422081d0350040001c5403072030000581502c000b5032503025001a0381911505c03919101129501d201d0240c00400403105030031000c1056002c0c0020100c18018003000c580381400044150040b10705418680d4950b07104450244411012444003540c0402034035086410221a41c0019200f4083c0119161144101e61780d0801607506c51015602c0c220030700030000c0122078a95041c150040740d012700401094613180501078480c070f007480303c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 750980530 1250 750979280 750979289
    0x20c0115210321020d0903031b080601080c190c170702090f04112706010e130c11070909020f010c120311120a1b030501060e010806030c121e030301 65
    0x101140c1c042d64041e2002a280c800c0c0c080c0d08039445111030400d14080c0020000d107003407110001450743c20351038041c044071490040030f40c007402c146e44000002900450304a410280c00d0a10900540d00c03000401410700c43c6403114a400d60561394030340702e641d41002c0070010880c0326445001402090b640c82000074000c116002c0e500080940c08102c50410100c0316503001401012010a2411481e001c1810360080074025280c40c94084502110400c0091905421650910307204c901c04c101007001401200c0c00385014005190b4034021043c0c01c500032085065501003030380c1551301c040c1c0d031981c5807001081c0c41402030b80544581c100c90300b195031150071120319155100c0c044d600890340a16044000300400303030708450503400070071191810f507a109034400d102e64000c280100e4414560454200c40b007000b000705d0300030306041200521490342c0003411040701810a10b0300c40706503602c01c00000d00d09440c0300c0b441d5400ca83c1c01034100320680b070040741101c0150040d0f965824800d1042843c0c5540344024843e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 750981780 1250 750980530 750980579
    0xe031903051911070b210408040306150b1b011b0918050c190210090f0213090b150a0b0c28050d051b0714010f0201060e0f130501020c0115 61
    0x2849240c05d08006080c11090b294001c41a10001e01c1e5026410a4180e40a40f43e9410120302082080480e02600001c22030b54040c00c00f000d03140c804200001e0060340c510007100d0b1340c13031810170041240940c44a0f801c1c00c4403101c08440d00d081420042c10407541c0d802202103210808403c2c04824906020300e40c00743e5803198240d49041d03058850b000051607801400800c43c050f252071000c4100490080c028507500071035803a400707d840ea1040210701e44480c0c10a0303100034181b40102d40855201c2802585c02030a801510017821b007450000744001100e50062041c94002285100700d0090026551074118145a54113100030003480f4040e401100851000b0702a81c440340c82d0a011a01c650042d088006000f0003c8042c103007a800301908055982d0440b80041469214503902581d1225842c02c1c1c840d8140000c0080509000d402c40703540780f005000744113583d010800710721031002c400c101ca10000e030050000c5448990001803107000c2c000604404590401e02c080c089820140402c845030b2a5503040e2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 750983030 1250 750981780 750981793
    0x302030a0b071106040501060f12020d0809180a090308060a0b07060c120207050606040b0114030f071e030905060a0c0e041a0a03050a060e070807060e031903051911 72
    0x7a80c0c1080360303a0040481041041c2c1c101040c500100801c1000d02451003000042003007401c2044404c0300401d6640b0038040d20700c500e6018005611040001000350f0380014403507595202c504041042040c1c540c12001c2c081c8450010820365010310b80c41780904607c41d5a80c810b0944a036030810040da03110703010320356405c20304020b0740303002490550200c24205c0683c18441a4040300310246400ca03040a10f098815812140c1080180e00d403622410041800900304140946640c21404005000090035990040040408210031324018529481340700c003144805000840d4081b03005014200000089a240c03040e0408908040402d004100c0e110f00c05980b80d882b011807100400c0060a14000810071180c0000c192010fa900d036082c4080107540250f00600f01010070786001002c944410050703e0140d04040810b02035140c02084200032a0b4207894106105c86149000031f00f8044055441c1740c281034184001c42c201508400540000d030388035910981c00440003030041d1119900c881d00c0c01507540114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 750984280 1250 750983030 750983033
    0x10120f0c140703140309060f01090e031b01110c0d02010507210c090e16020f0a02060f0315041a0306100821041502011506020a05030306040506031c0302091206010302030a 75
    0x2071001e091180c0c002d280070501c501c1400e400030910352050307882032403d07080781c03082000c040030301c20445004103160101004882c4520303203811303107030302600319420402265035015000162094109003100010b44001e0b980c1c4100180b600359031509034001410240d401c5c10700103800700d8050358074139081074a9407000e1b140107804803082e0b0001700b045030282014090505004503d141c50f09481e140f051a400e0381c031820810f13000700080d14044149640c10883d6224008201c0141c03911000e880d2a401101d8000d610307038666014401c0d40040038070705a50070510341284135844803064445d104290b00c0a138184c801e01e49a403d4444000e20b05801200107030f40c00700c021450640441e410f10420110703802c41c0340341840e444050308000001c1c00411440140e444400302032a501030003036020000d250500003011107080c42d554158032408024001071082da038510005615032410b010b481c0690141c2c0c4641c0c99503020309100a0001c2d044420024000c1e2280f40ca088000d510015106041e20380040040c014a02513 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 750985530 1250 750984280 750984317
    0xc0c09010603021e16060c0c051605031b0d060209150c1c051614030c0a050c030f0a05070501120b1f14040501020307080304032307032c0d03020c10120f0c 68
    0x211100001002101a000d48c0825070510048100f13007491081110014500820149804c1d21a03400b000014007180b0045140c0d61030044004a89602103405030701c400c200000100c05442d0710443d6154854002081e042034500800d149616410b9030902d0848440d030504c04640c07a019070008030001801018540020a1b16440c0c24500664180100c034640680380c003116040c1404140c08450940c49598a80c0c86441c3c103100b5405020304103001401d0130001c42e03e85940d00c130a50712565041c4245458040d500101030307040401002c2018000c020f0a4a41551042c0368034031498100c00090340019215907010341070b200303c804403401640110300b45030440d2650780d80d9a101a0084042c0246007518000c0e42c40101620490000d0700e84e80c2c0c5032200101e0070b006e0420383c0c502000f031f5070681c040450311030038031151880c540c4901d0301a035640c2151000d5140c2a450242107800d0140c2c02100101c0b101b2001d580b102c207900e0500ac00b0300d8103010f401000074040c401d03216555020004107250703041c3c03044581e00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 750986780 1250 750985530 750985541
    0x90603052404020d0f0f0b0301050c07060b0a0b04140a0b0412030e0f120a0b06040b150901122909090303012709031106100503120c0c09010603021e1606 67
    0x20002c1c001450018000d01300012503403000008030703004d500c81400d07050290349032049455404080d002409685440380144400e403046010003401c2036036403541424240c030b070035001c10040c154030054569031f25210021100c00740103101c101d40c0300740607030300c400f00c2c158241d8170a80d02200c2412030520104541e9580658880c582e0603015500000c6144c00010113903101038080b05104298009080c100c0c10600b01302c880c0f12001040503001c0c40c00c169040c1500c0e2aa0701050441d01c508035840c80e152600d0f94012105a101010380c1e0303038954140815642141055021200c940c204100e02d80c69010444e01804820481101ca40311150401d0004122a4205400744a481d808a0040742c124401c900c54000c00c403044500240c0004641d0450b80e100d164080000680000c4030364543c0344c01515060000781d0b1101d0388030703800c1001c81010170700c20103805007046140711a401c018000304941d82c4a0b40001c0084d0032541100b00790880342a034206001c0180c00403146589221041d0808050003500d410002e0301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 750988030 1250 750986780 750986851
    0xf070b0c030f0f0310091a060a051605061501210b240301031a060f130e0a08070b100b030105010e0d0b190b10080a090f0f0c0609060305 60
    0x8200140740e9410902d5000304040214801c03030503120300707042407850303000c040304e400c00d1442034504000502080800c007000c2d4011a4125000e59680f880700e40129800d004184c0d2241c0300c8000c40f09407108010b00416501c2c0300303170400044920101c000c1001154800f1407003000e9140c0074030700000c1c0e00c000005074200d94013121000e0000000700180c0780b10002c111802c28191040400040700510422032092403042e8200711022541c80c160518900003510640d850305c10500c101e030507080a07114000c1941110030540d000400b070300c0c04414581024440e1b54020901241c0300d0300d481c03000441440c070312601c180030342e520140302609581c00c000054074121403074480c0661115000b40700c9030018000510507071080184002e9001405815185401074a00c1e018045102d0315901c6094020591300c2002c8680c030a4255901190102039410502d2030041a4070016240740b840030704440a00207e5800c0804580c95030b618150b1a44d6101400c40443c2c100340d44030b114249000250300714103e481a0303a0190b81 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 750989280 1250 750988030 750988033
    0xc0f0d03080615040308070b070906090815100f060e19031a0a06150c0204151503051305030f0c060f100302060d1413021c0c0524030c0316020f070b0c 66
    0x540701d0301c8100c01d903044000d0031030710048c009082040c925404000c2000600090821042003410200790f00e484044072000210131040b0f0340005041000c5507201c00c0c0090280903202c004040c2c460a000304000168000e2074062165852a0442100140e0584048a41040200a40486074442418000340103044132903042c0d201e8101007030703400c0f001500707005001650f1201030800e0031a01c10700064030071609100e070b00c000c00400100318000703240420340074034401403074006515901e608044000728503500380603120b4800480e416442c140300c43d0007407101541c0300c1c013125010350b100d101040802c002140c8250f100e4000203030030001410890081c1075640403003100407841d03007840c0740d0076290313101d08560303411380c44080001200550502401c101c1c1ea0040104c0020a03070703040741c0c44089240b0458400d85014100284051a41005d10380c01b6903904915100c0e219603d0a040b07980404640081e1803038001c440f468039008030550b0000a04d07605084002000c0c1c4072aa14040801031950805c21f07034040349 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 750990530 1250 750989280 750989287
    0xf0c0a02130614030105090d1b0b070c020909070602070504050702010209030d0f110f0a02060906070605270a022b02060f0c070509070504030803041a090c0f0d03080615 74
    0x607650703034404107102038941100007182c518260100b44883e907106021070190345403000b032080e0310001096040900c100c07814003910010128451201036a0340c01000303010310980206001c00c035640441c40009850089548002e2500c0300c82240c0d4480f0300d10311030f100240e07110340400c2200342001d403c140d40c020300e607000060900000c81c000c6420980d1200380741001038502040ba2011540241c030005c0191001c000900001a104e114191380b03070740070039000c1d01c1500d001c00c10811075940c060440380034075840300003480217042501400035540802070440d0460110507030303000b0840c83c000a5041c8041d40042115a40001b51000c1100d040f010000e400078901d1598080c10150301c80500804404840c07411655a5018501e441c500701082a040944a2001c00d010700541d15400700a542c190381d0400c2c4556940e031100d1404103100c40c24100d0445464010201f088035810020a8440358104242c400320510800c010803c0600015410018085040c5501240e054203155020742107105140d40464074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 750991780 1250 750990530 750990533
    0x15051614011a040c0c0c05090a09170414010302070807060f15031b06020105060303370309060507030b0d0b04060207050a0c03120915030213091104050a14060f0c0a 72
    0x25120381c408003840b528090840d10550782850321420040040d0f5190090641c491030342d0b142c85258281c03013014411040300d0040703242c2e03103040c1d441440b280e07a00c410300c82e15261451462101580151281c80742ca1000c017071000704a035000340206d82c00300c0c0c2d101d80040c2c5070820560382c00d001002000381100c101941d41480403c1e82414001003405580180030515800a10710220281ea0041d0341100003164140010310a40e41c41c00020768454104442d201d031003400385d81404009040f40c0f4030360504441c0c0b0704c0d2025154185c0541c020848103004a03000d02150792020411b44c292212640746070381104a4909202c04215a003826079003161003001c01501e4015142c80300f5141000303e100607140c221300340e0303004c004100f102d031600001803031141000228146007840307030786054080c0c440b410145078001900002c44234900382c103c0040c09880608103c0103c4181c985241074200b07010381c03405100079240106520a1280c2c3d140d1500c000180300da840d020343c0030a2580381ea04000e05107142d62160080140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 750993030 1250 750991780 750991783
    0x140106061413050a0b0d15082107021e040f0c0207090b01020a050102040605040e0f040b0402120c0d0b0915060a050609060d0203041b0608100509070e030a05010f0615051614 76
    0x905c40152059103c030f0710b41c8080822199074104c46020000510000c01103014041aa940c6603900800700020200030b14101c940c1500c0380d408000d6204e001c040300880c4910600c6800c94040c1c41c01c4d103040202a00d030b00c4441c4203d88e41c048911003d40e01c9803600700804030a5400583c40180184103450101301c640d601c1d1803d9800c04c1d0095404501e0100313040c84900c954400c0107500969095401750b02c0c0c10039881c2e10310b20041c042c0020b80070300500c1c2d12200200348100600c044600e00030b000c0001201a40c00c02d040081c10541c4c00074a82d001b198480d2041001014005009036030040c1014151450a000c1201c00d034884005150001c90500081000d02030502c043d40c071075801020818410041ca02610b54600031941000080c400302c40244900f02c00950801c005440c400d0b078440c0c40e640c803056010707980310b42d451080325817621540c480f040402c1011f4125100100d018031003404020788582031411074141e1009040b00264083c40312500c51200003c08012032400f81c0c8070003080b501c00f1840203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 750994280 1250 750993030 750993049
    0x201020f18030f0d0c08090a0b19030b0d02030304170106121208012c0c0c0d0302090315070c030e040b100314011a0a0c02031e060414010606141305 65
    0x1e440845032150440240c1c18188006030005014030090540c078006058003038840d50b2480e00180011320041110b6450b91105000303e0080c2900343c80403030700d80c0b000d40b295070807404000c1391150000e82807080811842c2440000c50a2460380207018500b81030514403000307140344c50300c1c6444c03026640341c079000600d26240080b90148a8080c40528407240551107002d84038940690041c00b2034007500f002065034002140040a02d0b812840c00c0309156240c0030501180f034014050030034118003400f00c0398000150107a0013087c140c2001c3e410740386120318035007400f500c02c1c0040391035801040f124003491001a105001c0c030b101c1504000c2000a46e04480300128411034181d80d103881c01f01e5540c40c46448140a91381540307004060140c64100d000ca141c590200c2140640e1292038184610b2104540840da014010000d800b2400000d4021065101c0704a65031442d042d1803d4801c56000701031000500410300808050392501d071901d1001880c84203030006954021350070710500301c8444034081050703038401e07408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 750995530 1250 750994280 750994297
    0x130806270a021216060518040b040603080f07060b060c030a080405010908030412110c03030a0f021f020a080106030203060303070f051c1e021f110706090609111815010201020f 77
    0x20701c0b00d00310503100964816126044002070041c188004914007600344a000003000040c2d402003027000c3c170070700070030090f003030300d8100070106040841d0f1402c010560b98098080d50303015280c180301c40418941440700a12601e0b541e042e19400070010340300c14500a40405170454820800000d05600a84903001b4541040d10100c0314903580c0540c40800f030f0b034003c001d519a2900f090103402c40f200c40c2c00c0080e03035074030450f0003003401d008200c5550904a402840f040c0c41303080890058007610213400c01c4800003980801040404100444000b0900d00e1080c0300b40c0388140c00160046150201c2130f1208290710103240b008481d00d1240000e04a40400d01c110540014511500d40c1c1d80c41c00d150181e412008030031a5031040031036126001d00341c06a100300d1115503102e10f64200004e007002070314032a01c1e00740c450840c001d4501401d10181c0c1c0d042000c02d5000310090b5024a444012941c180010407a0b4505600d00c115441c159120208081e00001100301c0415141400011f140416032081954250440300c403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 750996780 1250 750995530 750995533
    0x10e03100609092102070306050c1c1d031e07022b03030b030a0803152107080709230c0d091a06060403200105070b0c130806270a0212 59
    0x5603407080100301e803082007000c9810704c1000c0982c04c1d120300003990703000c10b0300c0040d1803a5104c10108600d40014411282c807141e1000200700600038010f200e00103032001e03110071901e484201030701c510640c0000c0191485080594400c08a50b002c0e50030669090304915001c5e0381c804010b80b120f40f1511041191250f0207036155250391491003c03814060b0459104000090081e04545842c0000807101c1e0122680502c0302d0030020002180c800c08511040b0640080104502c1021040b020740b07480010355808450a100c01c480c0700d180c9804400d010f4a0035151b410000030034181d142000905102001e65008407085842c6090611a03900075055500688064882607440318082484011081001d580520180d908a1405e40f03142d403142040f03001c46420001080c881c180c0152560302c00c00465000b5500f1090281450500398038043c216841058440c401d00c0c048100003440007008524284600004070851003003a06020460034042c402e42c46500c40b900030307040640c0040e40c03950341d483c0c4903802550 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 750998030 1250 750996780 750996791
    0xd030506030d2307061b02030309151003020607081306020316030e1912050c0612180708031b0607030c0e010320030408030106110c0a12020d1202010507030b0a1202010e03100609 78
    0x54040e468101c6e02002008640040042080f9a140014164981d100481c0346550550310b8400702d480e00650342d00f0003980030800107808000d010a0300040c020040c04201029111a9540002d80e568400e46d5203100c81644100c040502103800b4468403070380050041c10f100c42d1606008002100c881e43c0740c0190450042c81001442404010018481034003000d03500989017004c903c816000040f00145080039049005c541200300c100240a60401821401c084940300d1400050701c030300b802800d502d601388510400b400607480307a20034010107008061a458462541240300300440180c01e0f4583c1005442c406090109662200c1034025482a03006102603070312941060f00c010301d008541114038425510500f140c04156550002d00f030b003100c104200c0c400c022841840810812001150b0160501040741c00c040302064040d0842c600c030b42d01c0c2d55010821a0200d104011406c001030048043d42080d55071510010350182444c06000c180080031100240c00b0b000440d0107894107a08072495064551 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 750999280 1250 750998030 750998051
    0x9150108071a0403110f131802041a090f07091205010509011805120717030702150709030302060c07030201060e01080c0a0b190c02040b040e030301080d030506030d230706 75
    0x2945142c29800b000301e0039103014610b4554038040b80c084032030b0030f20071100c6161405076541d4550b500d075100200716005001c0b0303918040d17034900e02e00034114050740928186501000c48007102240015544d030010514101074a510342d84c1c04603840700510040a000700180c0102e1008000703460f40301c00a00c18400400c40d0301d0980702642c00d480849074a05d01d50310502c5c0c2030328001a030200d805126007541005590b02c2d17841c00c1c10603084610340302a8074032141f89d0000c1488510344e4042088113400004000d610074a4440f231b0b00c2101c01ca0110301c000390041c0c0100010a010f50001c02c02005a58040e02c0007082081c0c6503005861108002c1e881420240e120802030225402c020309510002c2008460041c00d1401180206842e81320050050b0304004a0300a20703c11540c1c0c47e84418038108004d00100010101d101c44035640340c2c02030142140c80e200b14440f00c00094400d0041522500000e000707032140407032402c800d82c1d468112456011344082003a6669180301088006004598080e441c045146c0121 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 751000530 1250 750999280 750999299
    0xa05041415040c05151e04180b030114070f0c0c0302091602060a09020f090613060f06270b030a06090513140601030c120c0b03090a050601060305090c090915010807 72
    0x3c0307900080c013402e840d0307018a003c00141c8065407000c242485030f55592800000741807615200c1d82d00019034503c115254600700b160303107a2080010100a070020040c0b0103120307082d91041c50046402500240340320b8014201144038a451140c803034401c5910b041805c0d26940081d1554104540c80490000301010b5660a00e82c104a26070300720403014410089104d45401003154124922402802981140301003429034540300d008044d040f001e528208130030740e120b490502501005106180004507802e614034118030f000b03904240c00b21340038543c054840b0b1030a070051006400081c1504846640c0701000a2000b24501506200d0754500c1d00b0440800c5581c0740046147c42000d0945032a50702900040c400103c814a6240a4900e4503850030404441c2d4504425418115000400c00d684048140080100c00142d0717079602502c10000c0d07270516a01c5110440c1150012034661099a002001011481c109900c0143c0c001d03107240256401d40c40d0304c1c500b04c3d801078801e074460714080d0311002c0108542c048 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 751001780 1250 751000530 751000553
    0x80d02030916080a03030506060c010e0726030301060c020d08030403031e05100905060406031b031412030c13030f03090503010e01020c0703060e160b03060306010b120a0504141504 79
    0x10320740008a0310500f01400c46603549003060700202410342d600b000c101160380d05c00982d007070414110005d1114822100714142c0b1a17100d40309041040d4801e540c038030b010090090090844009a400031400c580c46e00ca0200c40c1e184c0340c0340381070342c000c514407034080085034400d0001c6203e50b0003034034046178400e0032010381e0040c0d4500558214099103402c003030008511824940c1c504440e118180801c06440e0440001c0040c251980020014001c0c4065111945028950f82c0f00f12800f88000c0300c0b1a0203d40703100c5443d501c1403850158041c1003000000d100003291030290011080c24200c11004540703e40c3c40e121070700a40e450580206007401820403251809001c1d2a605000c20402581010106106075940d4440d6000051005484103510020301da02040310049440d2003561211250f6551454040140d0041c1d44050083c06500d002040305441002203030a400c41c10a502c010990b0380504290092101800485841011440710103840d1001c01c001c4102c0c2541c2d0248688a003824900b8000300c1e907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 751003030 1250 751001780 751001803
    0x1a0d030e360105090f040210030c090b0a0206160216230423060a0602120702131803090806011527231e13020412060b010e0f0f0d020d080d020309 64
    0x101d405c0c100300050f1154020050a0542401c3c0801c044441d04c1050354508210340080309561000300c1e040a0965000a50320b00510b1821698114290904000ca80321001c0c2c001c481d080d4261600200301d2080d07001600c0c0481c071548154540c0f802d40000000b8152100c11420020b0404080d203900b16000070380d0720303030b0350400002c4841002c01440e1000c042d48500301740c82c0b82000220049056801d540354030410b1081c9041c0d102c800c01815201030301d013411500140740c0a03400500c03107040c041009074002034924141d84ca042c2c035860101460001c1110340110046c42804510f017406460061240c480885038080e10200307080c3c400c440c0030700000c0c0d020586000541d030b119410b42d10035007800307581c0c1c040c1340b081041050b25080c92720b94600300ea810181c4240d920084810f5800728140302071003016841240d81117003d90740c40400c50410401c1000f01596030284c2a8031a86c02e0701c50344d12510304208040415440035207051000da43c01e132500030003a00045c901000f91030700001000743c25401404403c07142e4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 751004280 1250 751003030 751003051
    0xb03070305070e030606210d090e090714040b121203010515040e0a0908041505031602010b090117150a09120203070803060105090a0b030403031a0d030e36010509 71
    0xf0302400c00025030742d00c0094800b0340203030f15070025500302403442240031001031007450480f100794603035000040149003c2e00c80d8042022030790b80401d182d14004200352003210003003401c1c0380e0550f1f528400c200042404080d100d5010070704a01404810400748500c0c603000030f05041140c2c03070750726020a21141e502c0d441c0c2051001003040205018200c07006010716004540b401d00065030990a2401c01c00c01c2c80b4907003105000380c060401c00058284d0200c01548100003001e080410000441402c2e4242c0d10820b0400e0340c0f120b00c3c0e0b001402019a104010880c02c2e09030011590401d20b10b102d07a61074900151518440d0301d8035110700740c060000710040c81d404081684000c1d40303068040d031202d8905000280003d170401c46c00140e2413107140d03180c41c201c01c050250240c02d96641d00341850b000c0e0081103030311441c0b001600102c0d416076075450040e0120034119010780f0f030b00141550720700030452206007864032102c210ba255980c8805011190700c03108628032031070b0b14104c5254100030801c001d8035001008400c05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 751005530 1250 751004280 751004297
    0xc0a060b130b030304090c0e092e12020d0204021e0d061202061803032a0106050405060a06031d0d0f2a1202071a040501090e07021f11040b0307030507 66
    0x7030f803000421a000c954680000160001d620301c0115116403262815640c041485c0d024000c0c0c4809001d608088011840030700000c9550708020351006043c2485202440b05410400c2009810443c058500c92403000304018644160703516071500304100d141d0218180000420024075911140c42408040d05015860350042e24440c0c1c0001d00c944219400c031104000c0c441850005a00c042040d64058401400d00d01111440280c00304201c00080948499941c20040c0c00030b20350801b40707d002e00038100902079206c20b03820440b041d03015001d628200405120300cbc800c640c60f1400144200401c2255540e0342100c0ca00321003c0041400c081c070001001c04201852001c1804035140080303002c010f80c80304005402c5222039009a0030092035134400c0c800c2803030f154021082065450014004c2d110262503a00d2000d440b21032460f40688102c609001691141040c808450309405c0d1000082c020311201080c02c1840100080c0c0c25000359110000002003c000e0020894050060b142e0004039417401066 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 751006780 1250 751005530 751005551
    0x2a0a050303011503060902040b1c09030e0607230f0d0206011520010c0e0307080c06091c0f0b040311010c022a1507260d110c0a060b13 59
    0x450344810311501c003010b0300403203c2800d0b8900940000b4010800c40c2c500315119503a6040b00340003035002c1c205a4040c1804c0280348480520941301b0314580c00d4155980e80340c403210244c1405003030f5000b100140c8050014141c0c03190130701500d21003e0004680c04014001c0c9169000ca0585040315403203207607041d5000440184a03944040d844d0b11150311151820383c907034452040f400d005001ca81048820594207101603107a071260880d50443c07003084150100d0b404070303588400d500d4980c0c1c900c0003c540d100804200d07074641450007000c408407014505401303100314040b513510f808503d2618031048132207a2005081105054108a488a43c0c0751428028007203904030400c02500d4003900200c0c0c000441d1181c12061b41b54043e400300000c0480003408000208031060072a0890780c1080f41c0032240303454001056440d0450044410042d20054021641050701c4440c00034040d0602e210031990490040c014120800c0f1300f005448440c500503000020210706110034014040151082da19815080c00745211 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 751008030 1250 751006780 751006783
    0x90415110c0d080c120906010807120201121a0307061812080a0c05121b0c042304050c1c0201080610020d080a0906060f0e06041103060909122a0a05 65
    0x1e148182d0324000744207a0b00d6654aa101e4003030022081e40f40090740e401c019a6900016407070f81030740e14810442d08900c0ea200f103403001407008901c000780041e64100c01e4010074001904201c900142c10611048240f08450210b40351007095403154001074001085085000410103c04000e02030810520804118135241c2080c2032040b0343e010410401e0300c02c5c9440620100340400541c0c0d102d00c00e80e196440d1107a24149980b0304143d1640c107880e0242c920381c0051450a07120301084e0001a44035804020801c900003a80804000c0054409001d24409507480d6980c08020005006007a42c04022446d01030000611400000703000501031020f88080314104e50700000c2030041c040d518903006861703544035481a4064801c264004029504191011a044849042d81c0d0242d4240c01a03615144e035483c82003005484040c0722100030b580c802c01c04a002d0342000c00031554041035070400c88420003441c00b4a41c00a520184060025090503403038860940b550b00c142c11030401c4400c0c000d00c002c200070b0b1640c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 751009280 1250 751008030 751008043
    0xc03031b0c11030f0708070303080a050108060408071b2606010e06040c091805090d0309080403110303070213020a1101021c0b01021504050d080a1e0506040902090415110c 75
    0x25014025003140c6a8043d90100054440369110000f0307141540c0da0340030765079038030400c41c08200c0c04501b01c140000c41d40a640e10a56048603040c2004003496101c13612080d0340c0741d02c4801c040d00c4642c0038a0384034011408410038a002440240c0420413480c0ac0c160030342500200c01c00a0101e1350708002e004000503400c00c88503a42003901141c0002c0c074441d007180140c440c040d5030340c42103e20b40c25506c07030030046a00ea40c1c045031081e00000c0c02da840031800c0c00c0b400c800300c1e01d0340100140416001c0c8018008110040a91200844c0c05011a8a0912590000b452648216003926030b41900007400e064000e80c00340545409980c40c81c020b5050a14a41890681d220b100304001c4100c1e07038456003181241e00c20040c650010401003001c007410308003030404980742c03030200c9403180118500c4000302c0c01d507084911400c82250314407003112582c1c21208802e080a86000740070349a116480301c1800340135a449122050043e481303007200c540307c0000604c00400b035908040800c0c84c000003c1c01001000d00c000b1829 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 751010530 1250 751009280 751009283
    0x1b2c0703020d0f050103050f0f0a030c1203020903060a0615030b0112020d020403020d060e0111030405031c0b0303040b2706040b1c0509010509070e270c09070c03031b0c 74
    0x540c45003050a02c00c401084543c0c01ca0200905100c0004280100818608000354010f020740d032005a00400c5180d49807112000200040c118404642c041611240d03000802c0c0300c140fa02524000070a400030b0310300501a0340c0405050f0b612182005895001c0540025035005414180300c20415180040c2000c0e08014101c0000394001480ea01c0844807641150095a8010b091001070415428560700401e0a00b15050359503107020159803820b0101d10941e0711495100d07000307614120032044600b004203600f0302803461150700e903d4038004503501800504007600e00c541801e40c81c1e8410241d01407104040342a86516906030710040180c0d52154022502079448008249a82d421400000345402d44400001c0c003187c1e2038907003800a00c490640000340505120003c03100d8058540000e200e6880094802d031892100c016010380758041c4130000502e0b80c200d82d1069036a294404030104000c0f01044400d08001800910b42d0000c150305403199001e0340c0da1103d108510510b00c0200070305203d105540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 751011780 1250 751010530 751010537
    0x50c041d1009050102090d08120f01030f02011d10170609060f010804050a0c030c03020f0316050d050c040212101205030304080f13180e0c0a0302060c07031b2c07 71
    0x120600f07000b801d40499902c9000507102c1c908800c00b5083c1803207141c0104040498582241c004030760091100005981aa038200c4140b00b580401e035401511959826000c281000140042c03894040c0d03549044105105000e440d03000a442d405050083d200784018062441505d05005104c02c580b83d44407034584100013800c21304215101d50401b5454440c00c080011f00010000501000b041a40348142c001c8910079540007a170100200100f5455514050410903495030014040000d803420350b004541e481d0040055400f551082408181a40e000b01d0042c03000707982e45024004000c00f60802d10000b0941d51702041031081255583c941c40c2e100140002e48a1403021807082c07414883c540c00c503060011701c2000c00384082d42d2107030440200c05888440120031071401007100300c0e0702004105903078074032002000900c0d0282161300f080b141c1c0e0401c107080006c1e84911140400040d68042c03410074608104002900060300c4c091600069140e100b640364010310b0381c0401c8040f115000ea2080790880103505 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 751013030 1250 751011780 751011791
    0x13050d080d090c0807030503120105030105190c0c0501050f04020f06041a0a1e0f141303020d080c0a0c0515181003020d110706060b091e030c0d050c041d10 68
    0x10083d5244445402c0103046000d40c41d800401c0090000040c000d85c03070f2034241c2144030b80c0d0720010142280c03422100e00000f5520f48200c5448080f00b580064080b481900301400144074548805007198001c0f00e80d440600911030074001946001503a8501c01c034002c40303000e17240c81c0c1011002c0c0303c00001c5488502c172001e030100d41c4034a180c0c010f8040c03400c04031041010b4800d04004000c000c010100c0460200c010078420403614520840180454400400580600801d0307407541e424070501c000803600640d01c1000a20004031181d00a1103580c800e94001c2400e0125103080c4001c0010140c0d0800d0071a00680e01000960810403100106001000b4100c44250183d40032503416400f030310410303c202c15000d16000841c0d202000700d801810b8042e00810703080103802c0c0c0f00c414450305e078411070b44440d602100002091100114882e420b40c0035190142c203640c80c024200d8040f4480d06030b0440204c1e000d4111460190940c101403040440b088080c5907060701c0d00004842040d02ca211441d031407540551240d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 751014280 1250 751013030 751013033
    0x7050a0e030109290601030b010c15060b070f0b0f060a120c0504050a0f0b0d0f020d060b03030d0b1e0a0b071a07030516030507090b1c0c020313050d080d09 68
    0x2035205100154010300c80c040f5084038084100d0144e0309107074030382c098a040c5001041176544248506e00e00d465044c0c451400d064507507140c141481c1d045049810900da211080841c900865102405e40b603440703140011908411840c0280c521003000f040c100407038610030200101650b8241e40841142d07500401d4490060103070900032044980781d04002c0d00581444140180e0100300d42c85810100840c54080001c03401e42c804101000d408100081e001d003603104070308400f40c64201c0c503074070301988100400500c50b0492000b09003036400c0780c1c5030030b100e15030703100014a02030070a10004e0010615030000c1c940c0165009000400e803180c2e0b800b4954143d54042011410080c448400450907400c0406154040c500400d006001e030100300c3d42200c030a00840c07000040b1500138043d01d0f0041040c1c1d1141c40c0360030b003814900039040d0081165072544600b007590f01c2521892500c121010025107070701550780c0d005500e006502c241010791096004076500302c1010701142101041c1c07503d0708110036000c1121004c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 751015530 1250 751014280 751014283
    0x16080a050c250e0402151309090318050111100f0b040204030605060111070e1b07080307030b090c040b03190b031902090f0106020303040609034407050a0e03 69
    0x60111081c4203105403002a0314510342e141040c003220303000e1032074504602d0701c40b454940984402e8900039000201e9803448420380040b5000781084440e03d0158444040d80c54450405480098030290f002c146108282110f0810190300100606400c0c01d0196003004a001c0c0c40759604c4620701c0c0c2850680c5e03030362195604521260403550b60b041f4001c00039134503143c072802c004000744010f6400b140401c00070340078150103d074085104812240b031010420342560f50021004c2d040e4200148002107032030b040005e00005480040030b5800f03604540d07030028280072030209021040070090144d150319002808200040d00400301266817085100b41250418003690000c103010303101004540740c0c9809000d0802c1c80040307052003400740a90003241d24407410f88822a4000f4407031428041ea1005030810000200400d4154011503500c5204c1e250410310b0690004070a00e48505804542410031409581c004001d030300c42680449442c081c101c56025030034110806000c0384a4000c0170301c10b11225aa503d241c81d41c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 751016780 1250 751015530 751015537
    0x40206040519090c0314220c060206100503300903071203081509060607150501181401050d0308090a020303031e0702070f0911040906090209100516080a05 68
    0x8000c1c01c03050151002c003151128001c62030259045081c50415030308a101d1190069000488601001000c81c0c2c954410141a4500c1c0030105038038191000e40072000100d811010800410082d4041c240070304080200340c40c06101c550049100f54050303640c040e03402460740642495464400c0540c10602681c442d030008900612902c10340c103004000700040c1c02c0440c94002408282700382e58001113035484112020902007182e40c03c582240465000a515040c048002c00c54680180440c50034805680c0d000c1054078003d800a41e640090134000502c425074a00400c1c403100c0308080094101d605100100e0b5906050700000740400c0100c50208200390028840030703c0017500603007582d990f4940414070700e224003a00412100c090080ba00010280ba00c0032136041d041d14044c034415181350785094104070152500d042d006040420400000450034114801d89004151100001d40c072000120104040715915030054414060100807090086507403601516425a001c01d0071603c403000948105c1e003500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 751018030 1250 751016780 751016789
    0x5030d14061f0f0c0f0c3201030b040b0a15020f0f0606040c11030706020406110c130e0c090906060301052a0a05041223010b090414012c010b0d110904020604 69
    0x605c409800700600a1640426080d9180b025110b00008400d00002a400c00304043c491904a0002d40004040d0321a8012a440c60001000802d007038800c0720015903022030661007424070360310402d601d01407150180012400e100040c409481f480310b007080001d0f16088000e092900c2603540c1e1001000c000e0140710410100a1a401200d84a100c03500d40794000b54000e015000104d2400401c020102c0c50001c0e803140316010250441010031189a2408081c2c242c00d82044003c1c01003440c042c0d1552911034810f4821b03201f00000b4016410942c003032500311940504240d800002d00c61a00300310108800c070071400e42220059182c0d542294100c01c8a40d4011600958007000c0800d80c403a0500107400791040c580c5840c04032070b84d900b0404108440c200c1d1140484950056030a60006010400c5042d100300d103003400340004075071020f8144417030f10000c000c2280d0341c060726410303041c05000e41d1003442940c031100810b032841c0038116070644880040c403842d28031092060542c41c00040c211744603a0701390740080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 751019280 1250 751018030 751018043
    0x216120c180209091008031c02091009050f0102030307090e070203040b031f061806030b0f03060c070605010f18050910020d06030b0f1302091305030d14061f0f0c 71
    0x14030301010700202950207510114070400035039010441400e450740701c802c2140c00b140015460002c1861b01600121403048103007a0690742405640f5481e00d5602e82400710080c1d680c0c4082c40709040000b04a4051244940d140c1150310500030400e025030040b09000582d80d281c52020043da507207810491441c400d44e0002e9035001400300a0200d030b20300c003840c0c01d071990584008140e06151038500c04c40e00810b0b610a03000c0c1c1c108007580700f046540c0c020341c06503030f02440203040c08403c0c08a07030010030316096040d0f4174030511140c001181e0090103074602c5194058610450b58006051900e08070011302c0310300c04802c1301c515075280013064280c6020000c101949013040d005544400581074404005c1100781b2064415075400c0001076080701a016003244251002904020101d4164091011440005017841e00e03805484441501050041010b00303443c0120801c04100701910700b496214495018040034001e2071520202034016000c050031100c50441b600d80504085082c0c10121401465502e024006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 751020530 1250 751019280 751019309
    0x5100e0103201f17190c030f0e03090111210f090901030b01050109090e031e0c030f09120f0d03181e1e0804030303050604020409020316080105010216120c 68
    0x203030031011043c07800c1c0e0f601c64907000d200705912469244443c50440e60240c001501c000602d1010f8025031200a110045250001e500b0610720954021243c001ca038106656001240545140d80c2c0250f0800d1042d15490280c1340d802c07005d10850148801c060341d00c030900f4902180b01925400c00509490b200b0300f0040c207864195079603080002c40c018081c0191380c0058401030700412085080c0c02843c1200c00c3c03000007075217824000c26211030420b00e2460042e86502003084011502c5800b040a40394011030390340c80a540324801810802d0101241240c0c03800b40e0420388503162000b0001ca00c1170000c40560a01180041c05003400e4040307021300c0d0f4002491407007029200415000901a400c450f5031041e10080c3c1080d8612914010008102c2001003402804110910020b4800d400c400e4002101400140c107203038954034002c040c0c3e00100d6004500000007220710101583c05003040740100001c0c00904015a01c074000d8095040c0c0c2070040c0905c2c0b2525120032000c00c000c01014500800a03449480074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 751021780 1250 751020530 751020559
    0x30307150b131503050d0f0c0807050718020a02010b12060406050a0b060d020306041a10050a02101a09011a0403020603090703080f120106080f01030308071e1205100e010320 76
    0x46000f038500082d42c0b1845410038408290340594640c2c1c1c019403103038a88071501d99240d80c40c40b8055010060032074650051440000d49108141d0f42680e081d1031034000942ca07102d4800c1c00030308442049441602c1800c0624000040365070209044d41c003d074020001103165501c4031003410146c0940303190560060b2001030034070f050b00e025901550044104a80501440c00807801c00035105111000e0f203a8824800000203001034024402410f290a507401600c1c2c500c9000d80000044808490340b000301340c04031010301c0e070042c03500c0c0e20703028090b0030303015107281104111110094a500031030100a00508002000c02c0010104100c0c8100555001c01403a036a412034040100c1c207608040c4c049052803041100205141d4052480c441c070980c00b0351094012070386151012541d406020344a1014443d007000380300c01c0c2907500600c0803030324185911501c40014034060120304070750300102500030102c08100c0a1101b031254020f1641100e030003000304134690020381141c0d5014a008100302d0343c043d0070703102d5089 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 751023030 1250 751021780 751021811
    0x30a050a0909060e011716030809030d140307030903030608060726090a0312091208090c01030203012103090b0c01051005010f020a0323070605090c030307150b13 71
    0x5032155241e5286141c6030b5850100005482050258041103145100140210318820000c207540203c81400c0354002c241c0642a0781450720190400e945403240050603a00c607003020070540300c0b420040d141c032855a25000c0004040d600011b8483c0c01095281e19403d0141482604a43c0251a650003a0303000c9040501020b00340e8140d800e030b01c41c1c0707031403c409030750158541000031184241d0703003840a4020f48111759412240d198036001d00f10b0308160b6404c1000c020030b06150341d51108001036207640d801e03418000c00c000d140c8000804100d04140c0100b005001d000001030012619000d0900a4040e01c0414a03003038400c403615030081100700c0008502d540150205410441c0924005c0c01c0b002c0c1c905888a004464004159018002586c0154071000020b4030800c8640281c0d00600075050100d0359054403085594001700b0300361040c549407400d00031041404c2c0402031101c041200214a4100316030f8070004520b0104841030700c2c40b65540420f00268981034042030810741141d0341000348802c00700010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 751024280 1250 751023030 751023037
    0x90e0715020f0601050607020d060e060601021e0c100306080a0f06060f0501170907120b0f010503061611101b120204050a090f021207110f16060f0c05030a05 69
    0x314101426803030461140d0011481a4035507028001800480c1e09080520800703900c1284100c1e008002d07003180d000414818807507039854505a0001d8111403e04c00c00081c9884291984030426804110100b0840900002c02016182060390407000c0990048015402842158002c902c180103d10785442048817240010182e24401c5a04004940d00c82151001040190007000d02080c0442c0c80e5401c1c05000c81c807082e80c001032540444145075282c00f00707030700701070386803103088807141c2c0031205206050008465007405044190003c1040c0d02d4800300011703407508040c5200c0c041c0541003d450032219403c3c05040c0000c041e0078401c4c8101e0002c4008080701000f0071107170714006110f8400080c0411080d008640850300000d10b401c0e00039084c000d040c0c00804001c1400004d40c0c0d400c0085030340340e0000b401170522079481900c0300d480e0301100484440c184030348420b6210094124048003a008141a898041500c21a107000307040c030441ca12003034803108401c0c000a88948404a8840b0032107a101005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 751025530 1250 751024280 751024289
    0xe0409020909062d0601211a0f06070f020d0f0b01030b04150b030c060c0a02040912020706050c060109050c1c02091003060e130f2009060d0308190204090e07 69
    0x16003404005070150030140741803404c0806900410300102d40c0c00d40c4580d91074803180803140c4200319600b1025448004845420307403902412005c1403001443e03440d10710240207203081d0079281145040002d0f0740b0bc1402218800000344101c2810784400b00340812030800400995021000c5c0103196100e040080c0c4030382049800b01e071050441110824400994000c0da0700f0890003070020140f407940002040402c0d04000150310482c405c905520000d079450340214201c00d8000c42d60403181320f030311040007428410290020420302000300562094400009403031411107401d40e8001034136840d1280201c546108641699040700c82c410501c031103041e1140d0042410410490702c1c0c24030502810000d07019581e00e84680d4001290890000d9128030018202a02d8a4840c28480080f1100d95072200c01e14074002d1240c8950159010012010381004a0110780103034045403403c0010b80c5a65005145032402000350400500c002c0302003080e40703079540540d000f030450114148212054040e441c0d0b9102e100d44070b03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 751026780 1250 751025530 751025551
    0x10801020319090b010512030d0213060e0a12080a03290405011a2710020a0c0b030603100c0315031113060602070b030702190609111903030e040902090906 68
    0x41d03240d801068030a0036a01c83d880a4944d00c1686000300300032000c1b6035510340c402180010407012031001d1702c5200034800500c860140c10306031400c00790f0040640e01400907280c05a050403030305020311003900185000e0640d0080f01d05a44c1c00640c0801c80c0034081d580c000c00105110902d481203907015240d24159000b109407000c0286030799170b0407001e09000141c0701101c00c2803000c01c0b00d01e0307644600190a6580c1c480c1c0341c0303000300c40f040030300080345140d0800b52a12005800c00c0030000d0805c00c500070f506005090010701281141003410000c0d40741d16026038020f000503620022440c0c584e0090b040400c140d44010076251400755030f42051040c240c2c58141c403510600310300c460075641640910501c41a030700641e0042010b2400c0403480c001c154405440c00c070562040300c81200740c202e0307042c41c1408180e1040c440450656580d15004003120950410107204803200a646442c580c660322602048a4041c5000840071440300c0124005018a540103900410030804000641c0c00c0010306074050782c110813 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 751028030 1250 751026780 751026811
    0x1e06040905010e0912040b0913150b120109020f040b09041401080115050303070c0e0c1c0e0d0f0806010c1406100512070303081302010201020c100f0b01020303040506012c0108010203 80
    0x100c5c041140d1040b4011091900300078003180820b0f0818890103800482444000a030000e14010001a801e10f00c0d070100c42a40000a41d09035400b80c0903607503e004000c021003c1d400c1003d0074071084130f00c1c0940e01403640c60441c0401c0400290740c517504403030300080050082601658443c41218064003a14040d4186d40f2500e0340000703518140001115610381e04049190340b200c4c140031001e030340c045001d8507101c030070a01400017450041d81e00035806503000c507910f0002016000d146040382040d466455007014002182c94641853360004405903101809103454000902c0358500300c5031401800702800c055105184c104510748003211101010350f43c08803070404802c25048400d590f15202030000900061041d804a1038105903103006100b0640305000141c04c041c5100c202c0ca1600c56015143d03d00b00d510765144203a692607520500d40404030038400b40d451460070391680c0d03a5520040c454450788500d405c0c01740c2c4015600d04a00244442900e2261a49513500c1607018080d40060740c10960f1b584100303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 751029280 1250 751028030 751028053
    0xc1222080a02190b220b0c040e090303060a0b0313080f090901050d050c040504020d0506071706031614030c1804060605060711010f120606080f07020c1e06040905010e09 74
    0x800c00e0008660f408010704e0b83d2580c03904803040d80d202038000c40b2100342c44041c084030000384170b03110700324070a1b08450381c03c60700c962508580d0510500090038a00070790f0001c000f8015a9201c4560344030940d01c90140d22650394036084044000d0008805025245003000700d4011055030415004100500d01210820500e0362224104180d51199050007003036a800111500c5036400c20760485903009000034000740000c40c80361079003814040c003241e8000001d01e0300c0c801c41c0c014200149500d0b811103030603401400c004815034a800c0070540705010325601500c205410380d40320b035002c02c59203005540242c03160041840841c05014050000d55003103d0325414485e010403e03042400a40d800f064000c064400d84020680054a00d009114901000c1100440080c0c243c50440e0050400500155640007a68509082605500c100241c118011500650200016665441101d0b4503c09007070b0345580d841c0000e040080c08600c40c50388043c02480c1040000100520b014008510402102c1e080d41d0a40f0b805 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 751030530 1250 751029280 751029313
    0x70e0a060501210f020409020f190810030f0809100809010506030307020d02090604090b01080a02040b100c080a0504180614011715040908070f14060c1222080a02 71
    0x4a6400e454819841440b9041210f01e1300103001c031410a803401858151142080c8050768021015103101d000006155458007650300c0700e1111360391603850990380701e0a1200e01d2001c844039500c03028142c3d0034002111418018880201c031a0450000c2c0458075600c0c1c1504003515021045581a049501c4d01000920b40d09021003100c01155004000449010701ea508001c0f040402818454006a80da420300000440034a0f503280030f030840d0001401160304510400040d540500909406810240610645650040e4600080590103011103450303429800c01201c1902850303004c0003240303505a04d03400341c5214551001003921f00d00f004000140807508010744a4041b002044800013030400d000403a940128185803028090080011804d10b49039128048907401c201c1003960079880b10001c440c00c0100040c4441e01d00c2c601d40340a04004d10f000003440c070a41c080c400d001600070040ca00040c62002501444403110762a6007c2d414250101c3d08012003540c00c00a071b900003510a08031465500e410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 751031780 1250 751030530 751030547
    0xc0c03160807060503090307050f0c03012004141503010303030605011101091a1003060218040b0a0e220f0516090e1c020307290604060b030406090212070e0a060501 72
    0x1c224008018075490000201c48a9200801684981c0010700c680030004605026020300c0810880017088145007901c1010308480300450401405045c180c818082c005203003064608890304120390443c141b1501c03021031040301c3d03d1214400074101c00000402015015070069051710020b0ba10504102c1070303102c2e90750880d1070f0310300081c05520000078124a08a0500c820b15400251841014400c9176260381d4001646c001102c1207020561000300601ca40c1042d20480c0302c00d41c021189950305900e00b455100d0b02160140446c0510b0309a00c0d4900a1700e141804010310071544035038881961505810030503210446607006810341e58104000041c0c02c0007138000d007102043c00303402038040e85190441e0b650301003002c10f04100540c0802e0011601041801040007030012880280c0c1403005190100415103d00c000c11062085280a00c00d014908503a000c2d690703c254010780002d141040c0740001080703480d05a1140104e0704c0b40000112740e5401d5144928081d8034400c1080c1302d519103c9005540010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 751033030 1250 751031780 751031789
    0x30405150405031603020f0102040b19050909010306110f070609030e0f100509030f070e0a29012f03120604050402060a12060b0a0f0f09050108010521030c0c0316 71
    0x740180118113080329103440f0028114400d0049039490707511003200909907001580844111940400c088051031140035032040f031103880f807504619008890f000100031030418013001c0c1c14a039498000f42d42c045455802c8500c0e009886100b15250340c15441e01c403010300540481280042d001c40041d8113103041c0840f4940f01d00100400018192200d04004c6600b0b0b0800722045505100f9407000d00131099061180c0c202030070400000703e24900d405c0140c07405440103005c0c80380302c000c554265640044540c0c82880407181c0300346000300442201c40300c0c4040d03240e54802e01c011b01c0c101d1a0a00d0410400000080040d02d101c01c10400300e640d500001c00c000c070750f001c0300c010750000c004214024146209006d0305507200c0000c0c100045040d140c03c00040c013a00b24034003182c042904400d0300c03602c05070040a0507907020042e00c0c01c40411810140020858981071040c2406000d0b034440022224501c034440c03000582c42202100d40f0ba100325044695681e8030026041c0c000e0140c070307042c0020400061b20300c40a90303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 751034280 1250 751033030 751033033
    0xb040317240303070204060905040c0806010b0a030c050d33150f090801090c090509030310030206090f061303020f09090d12110a02010c020c0d0c090f02130308030405150405 76
    0x400420307024400d15010510040d45404100f02883c01a91035104200140292100c000b66504d4145019140c0d40c03510f41007443c641d03000754010880e4158400859840c05080c0c900810644030080c42071350b0074080d000d102c0c58410304060003898244102c018100f050080750600001c00c042408140007180100d00505404031800e0700c0034031003540503103400d030701d03603015403400c036403456070310f50f070103421a40404070031a410400444100f06a810500589400000460156196080c00500451505101e02c0700a009400c08a00004290340e40a013041040f0300280c1810b507104c00c050440030101c1303500c0c0000c03403054811440003000d904000201c1407040d0402402080719039043c400c15204120300c00d40c1a080b01d0746801e68403100300c0280001c0d004080340e07a00007080d002010301e0040d003403c0e50780340240d00905181e00a07002141030070160074100c48000c000018051650440d03440030b17100b507211003520510000400800c005260b8029480b6500900a0351012554400c1c08600030f4000c2d1002380c1107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 751035530 1250 751034280 751034311
    0x50601080c09060f2808070e040e06040219090e0c18010e04030c06090c0617071d0108041707051606030b0a0b0a030603150b030f070303050f0f04120b040317 69
    0x2040500e0004145240d000480310300304a0114080340d40c0d4405e5414114001800ba105000d4840d802c031480c0c4000810888003805074200001000c0d0307590f000144040d02c11120038103402e00d05155a41c0c120050300c030b01c40041c042c0b105110031042c2d4078852605020b0180b00050346541491010b610158107a9480d0410f080c040d03102d50b142140c2254280c4070507156503070b40b40b00c008001039400515400402c02e80d141c01090740080c0d031030700f130034802d0092941080c00101c4903801c888400c002d030051041842424580c45c3c945840c01c2424032019103a48079528098000740b85c506124000900101519604882c0c0e529544c4400040301a0b4441403030701900300c1580c040074061204e200001c2c1085042c1807800098640d80d175192841602031201c60859482d582d001c0000740f9003403c0c00400f000b100c01d42d0051100500d50340c1c0060092198100c0d07110102c0000c10080c2058400c1d07002c8800520b416054481c9842680c10708111341513081e10201d000c2295515507400340c00445221611408041c0a4080f1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 751036780 1250 751035530 751035547
    0x403020c0105220909021305040320070e100509011403060c0c03090a170c0f1f0915090f061d0105030603160306020904110f041e030609030201050601080c0906 70
    0x40b103401409882e001d010804001c00a00c992075140c080080c031903444041843c0107140144904075000c0c2030490b486a042a04010109400c00d8445441c030304160031040c80784c0024410b86040c51645c3d00044407901c1c03120144102e940490701c201c13080e1101180d0348141ca903600c06005084448580c2d0340ca4160b04005d0001c0e44a05e911000781c98104503d00070341c0d10301182c3e080011165030305904a03d0591450b0030300e9086030300c400c00a282070548240c440d03c00120101d8001140382c0419071501d0214a00c1e4283c0844640c407408540b4002c004000801890b42c50a2502410000c11070040c1525a1401c07480013031124451070702d140c41e004a01071803201c200100f07001140e0b59480200070036018401c5010740c02160102040d4a00203600400d00161601241c000f04000c2e110703882c0403204141400d00482c0003510800040742c0403141820320301644d01c0d140340014040c410050380041c10080c80c0c18801c2c403c0c0341e0103420a81c810300b407da0303405038180d0b00e21001c084140900420140c0080301400a40b9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 751038030 1250 751036780 751036787
    0x19050711090a0e03030f0117010902150306040902120616090605070312020f0a020109110406260a12051e0316050d021605030d0501092307031d0c09010e0403020c01 72
    0x1d0b040300c000c40b004120104082501d52641d401514109129298200100401110618204414810300000b8400d92210b500010300c203505c0043c44c100e01c040004003044440e81c955000d51030150f40030b094008030003908441181c55002c01c0f1200e214501d040390641810910940702c08081e00ca4a8840030304102450300d00311803101907040722550341a400c0121500a110110140c8582c900c20ba00102c0e41d480545040d400055681101900460511800f404412480c1c1080681301d030f81c811200d82c81340714648060385410003103000a082880700030348a580a0ba4800018028101641c100c40e0805500e050074118074032007100d105030b58003400ca01080e80d90348694014042d0b00700046016080902d000c0f031000f50302d1001881248e050307000107101006000c8600943d801880001c03400c214041c150010559028060b01032545c00441100000d80d400e0b0107580100c203400702412800e00d515a13044416030350303901d004150300e110340b0100000144542e10a22498402d507070660151080003007800054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 751039280 1250 751038030 751038049
    0x40524060a06081e1305010609020a0504170a0b0c12071707030e0a0c0603020705071e030308040326010603061a1801170403020105060108010b16110402071719050711 73
    0x862400c8035802030740c01c244c00a030483e80c05011582c40b0504c003002646805030854a1642c44685005d006210b0805a180c0002c196421140b0740c8140c1e51510100100d030704d042031000078001b170240382210140109505440040e0070200c0c5040034040701526400420303160300c000d0303040c81140d12050900240010b0704c21703040311161050f003030b00b140c96212195955210401203600700d04000381e030201d030500c1444001c001140c01003042071032042042031458041c0f4510241c0b4007014050020a0000c40c0c1014452407180b01503602400032030703e94025181d501083c500c4203114000010381020f00104504034600420a00c40c03d4800c3c00c9450b1500b06034040281116a84401c0d051185200018401d440300361480c6101d18404d0740001403d1070a0000034080b444181c008018100c0c0034007900b546e03807030440601405942c0059580d0041d442190004007c0e2046140081800f1f03030203501180070f030245001411100c5461001610880407840f4200e41034041e9102c054440303e0031400d040500c3c140b4082c1c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 751040530 1250 751039280 751039291
    0x15090d0305090d020d060b01230904090c12060c140f040329040803012402060415020903011d010b041e050406090f0f171e03150306040524060a0608 65
    0x30250340c0483c903000102516015041540c20a8580895070310540c0d0103540d09100341d200c200d800000d0300c0000b080000b203026a01320280181e685000b004288601000139000401c40d00705900e00c0b603591840c02101510078080c1e0140855104500644000310800540e58a0054220118100303891074480000800c22403041d194442c034000b6102c01003134095800c0d02e00c901e004402031f603902e5161a003c0000c01118264a000b21100b00006142e6507901184241d0000c0e00079003e81c404e01c14403480c9400911800301b0300c41c3d0540c40c00303540a0903601c000420b500903c4002e0003c001261540b4240000e1b9540303001400d80f0418031185541c0c0c0c40f50b00d5480031390454010b000005034132040766a09440070060440645983c3d403101406410030000c00303090f040c110f0f2420708590605140b5603050001c04c1c4041c0c0711008241c0007100003840c22a00f10115811010010115606070415017061a2603c2c2c41103e0200003060180e41403c02071201c0d03011314044d0ba8054411491032345803800485414001800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 751041780 1250 751040530 751040539
    0xd02040306050106051801021f05090f070f06030e01050c07021e090c040321120c1205280204050306130609020310020418050f151302040906030215090d030509 70
    0x4003001088091180740c2c003030041c0c1d4640c00d5507000301c1c0c8100c00e0107083c001217071070441d03100e0428240d407140040c00010602e0f072040004075403522401c2c01c560803c41c121440700b00e40d10a08000103086060000350340d0440394a80c40030444107040345607650a0b560115681c51102408200c508018201045103400e104101d0301030400d212550400104d03810380a0b600314030100c00c041018424003840083e210729980c0c4800c10641d012080881c0500f0709820410304400386980c1c0d07072038949a140070303004000905091030030030001813a01e10702d10b080b54446400c1e107600010065240450f000c9591080300c0941e03078002c0003000c245d0f89000d01d065403901079444c11a81581c40c3c220b910010384082090f042100c8014002685172424100443c1e01c0b880c80ca030940359618245018400814041c001c1e42d50444103240d9491000e03142d143c08100a210450518441c440c800100060615034507070002090b00d00c01c0705c407200c0e48a01d0140c1c85c9914051440c40d90b80c08040c00030a000080d002d08010310300904040c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 751043030 1250 751041780 751041787
    0x180a1b06032f0d090f14150a0e0304050d080c0d020a051b0a15030c12060b091302070b07030e06071d0108101203021501090608030f16211107050d02060d02 68
    0x2400f0070a46001c040c086982d0920000c0f09002c1004c084446001d0b141004c0c0240354468245542c08251007016013a29216640c1d102c203500308100500131030700501000b6154680003125450800320700d91007a40716071514000d5005001c0310a02c00302e80608466044801410700554408011050540c0c501600b87e10003030320000001c149030b914100e814280b0040d00e000801c0c03106064064422840c000d0312001c1c4516141080c40505100425120310300800e81311550584e4110146200030300c01c815015011400340c108000701c003503068110740682c031950015150a62200001540c49010003460718440c081040d9469105501c03520216034030901004955039031640d940b00716802e140d080c150030740040e00040c440800b0024011400c0d40109002c4c4020030800307203030806180d10b80c0194443d007801c3d0680020a48100a11180526011070700005400e050320514242441c00c0b01c001000c0201080c01707201c0b06802001c0110700c0e202220301c060446030703842586a080003d140d02c0b40200a0800d603090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 751044280 1250 751043030 751043047
    0x1b07080f1e0c09010b180609060f0d0204120c03050724031a04060906050f0a05060406081e310b01060f020115080a02010216140108180a1b06032f 64
    0x191030303e9009114402c40b80780c1d01c00c0c00011003074004544540c0d0382e0040304104414202616007808481502c10040103541c0c5070391070404002c010b07100c1c503407154104004040400051026110b113100c222485581243d50080d034540d0600102d051904200020800320424417030600e000b40c1000111009464000d042403608400180c111082c40e0004040d02c2d40c0c2d210140309604022040c4c40c9514030440d12061500e00e4640020307400d10450180004100ca8100407860203080f94131100881040c3c542d5070001403400c4d1000846101000c000089038902c00014500c0c00d2546020f10481c042d000090241203a00f022800e0300c605403400b40600440d980c50a103442012404203002000d00000c00c0641216402070000a207000c103181521959040914400c10020510342442c2090040030b007064040380e81c6440c10140b00350340c0340300003444030f005080b11401000010011548088a0205a90502500e42c0021012601da42060f0034040d0b50428032080240d2034041303851181003070b070010075140c400c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 751045530 1250 751044280 751044289
    0x5060702061506090607060b0d150207110904050705060f2109070501090e16030209130609050c07031409030f120a02010c0e010c060c05040504021b07080f1e0c 70
    0x121880801604040d0500c8404804070501500090b0100c030302c1402d041c0800002101c40c440c2a90042150341d4850499055031280b000c41c411954119a440d01201c01c00c40d01e00c8080d602600e0100c4400400c20304500080c50100c140318001c0303070804000c1c903400d42400c05112143e44550740c0d03a5441c03002448110050854100b4198a080d214403070000d660400050081c0341910540105041c80182082401039400e1446444d034810440d02d03503140340d09481c15080c0d000b07200d080c24503a084408a040c00240e031903282c129008845050f4020441075072001e01c84c4049006e541802030000700b246c50590743c119091000741c41c45d214000e00780d8a060048090b041c0c6032845106824007861008140e4040aa4080c4a249000b03541820041960407448000034421108250020501c86d0b54080c0641c4e010301c54400d40700981009007046584003c00b10400c15480319504c010400340c46580008210031402007460405056580010084080c2c0e1000359600100c0a04a4100500c10000c0c450819602d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 751046780 1250 751045530 751045543
    0x312090f02100905060c01020702030606060f0304030c02010e10030e060702010605030d0c081209070e090a0c0303110f0f0106081636020d0509060a06150c170f270109150c05 76
    0x1086e20005940700c4c0548180340c100000101418440c04042c050034600c0c501180889074080ea0510309a81c54656510041e983c404c0120203071900010840900101d158243e80b2000040b4bd81408541181c2d883c01e074100d0030f80700d0724015503400d50085c407017201000d806060b10444d09071050a05500f0f22040156900d1030318030440301e120180e07100b617104200c601f1108450341c0e0018031a00c00344c03501e80b60b540c450420600580c4001400c10421661505c1c004006100d0900030307116100640f540000503400f098040d0007280182203280c02840c4140b26210b4082d03050390211801c03802d03441c0c4583c600d41060251039241015801a115010b540704010241c1c0c0d00c02480920105240080d46091510445140000040100000d42d1038200d041c0081c02c62810110140f522a1500c04602e4100340390440c04c280081c82d0384d015004d000f0408400482e88000944884442000a044402106224200e100103150012408111260024480341607913242c8103c50000710700348001c8448550751751070329000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 751048030 1250 751046780 751046797
    0x2a0210020307020a0e0411060912011b0f02071a0906070c15141206060d200a300f020906070c24080a0e1e0a0312090f0210090506 57
    0x7040050003404514040c10101c020744070700d1240500d02d2401d40e460310f10056104081500c10343e80030800369555920400c1d251000108640240004003000d02e010b913180b5015034031403005c1402c281003000d2492000030440120381c60b00b610340e801071000d850520a01d52111060035000b4208000c44004914840601c000a00305281e15200005003100c00030140c1c1c811100382c0e0940581046500440e0201e4503089800610840c4c010b035841e4613151150b401049220380040120030036103102c41c51004000094903070041c464a034501d040d003011907100054801502240b01410b682031130605803208942c4400004108580c0051400e2980c0e40000c0c9a50000303141101c03050b503440340502408140c21443c80da804090358410f0403401d8a11800b40c511000240300c114000e64802d90308038501010001e41d140c1c80d040c0c06852000c0415581e00d542c0340d01c0d2100d000e40202d81200d11141d84d94080384501c960407a013194854900e280d0b9a42040481019011540100010b40d80003040d140d41d002d00401c80c20303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 751049280 1250 751048030 751048033
    0x4180803040b1b040b0a08220302060412020109020307030809060d0f020a02011a0a05040e0304030c181506080a0923010b040515011b030908010f0906050609072a021002 74
    0xd02c0c010156034684083c1820107103c1c0c3e40144020418000200c09840c0d0003405ea00780b0300d69695a45004041b14204420742800161402104a040c59000702c0c0e0300380914011608804500480340c0140e0a9411102c03000350180d120500c10008514910058071500c8401414186004000c0030711005580c2040d03891880d40380d000900fa20407580900c99440c00075056950454041c0c4804c3c0041c496942900c51180590344400c0c182c0d80d0b00b23605004941c0590b42c02203052018503240d010501188848032059103196103810034003500030b1403102440b400c40315642e480e042c01d65110b030340100180c290010102c8180d80300b04069402e04821401d03402032a000340c000000e84c24020003c001c1a0394000e07101145490b01910103c1c10360b41e01169401c042004548140d2040c1c5d8103240494246170150b00c0303104154a48400b000b01c50242d41c008d220118081e86c401e0140b51610020001c84210968054003c560125a20000c803610080700c51130b107091000b14107a4220640e0041488101d480c142c25005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 751050530 1250 751049280 751049303
    0xc09051206010303080703090302011b02151b0f09010c12050913020913020c030432030c09070f02070b03040b07180f05010503190e010603060f020901050304020418080304 75
    0x500300040540c9218081800500d03195165460191000b8009850030040503150603440080c503000750460800ea5041c1d4034040444684048001c0d00c40c04440841d0744104100d90104100c00f07088401c00c40440403400b4014640040d8001c00c41d000d038446c101c2c3e1818031035083c5450f00800e124000348000d40350540c547e155524031481c20058400041c200c0000a0f03481846144116190440d01c0340350484601c00050351200c8110706140f65026950080500051210441e1f09501070007840d003031100641c92803101c0310b0344128205a101d00c0b0250342c0c260440d1074040000d01130fa11440481681400a0058500c12074440c400104550300813134080d984907120701c083c00701155000080300c0c40000001a00c178000d40c01c240500e41030500d144182070401c1404400b1440551030107169819079954441c0410440d034044030284d0203003100703101c01e0f545a07103410001c00905c0c20a00031150b41081c144c0d510351841d500c5500300001452980030401c405400c080300c5c80c000a001c00020f5000728000d1420101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 751051780 1250 751050530 751050539
    0x909021201090b0307060e1c050f03070201020d080c1614010204170c0a1d0406022503120b0d14010209030105070c0b1620011506030609050f090a0f080705010c09 71
    0x183c89203142154000d500c191402c00c41140e00c101009100035084900c01220781c6851520680c0034080d030710250460241e828444c0201c00008010840c00d07101ba000d03038240000c1d10b5400d880500c1d003120a11100841000304a50b80d17000481009c0724a4881c01e044d0725882059070015003281c005401c5408400d00ca07484201d00d440c030030818600801d43c1140d04000040c18181e20f40c83c0a2007500403001c90070b00307040109040020907015160f02c040866000ba24140d03807103c800010f0200038000754042021801c46440440b428010015074800c0905020060701c0d641d0f8600c1c02c00c0e04440050106035600b80812441c5a40a0040500510f0160340c3e12001c40402c0c02c10141c480d20140c01581c0314014051450446ca03040307034161000303413400440400b0f11080c00503a603014010b460480105980e041c07401250301c0340c0551040c01503034038150040216035a04200c00e15520007d80b0041e156074002c003001c4002403484543c02072141d200f04c109034102051030380d9003400d40c1c40c01c40b2074001050410300d0520 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 751053030 1250 751051780 751051799
    0x207050a05031c0b1005340821070206071209060501090e07090227010c0c0803040611030403150c050f2a0606100e061201030606090612120c030909021201 68
    0xc0340c4c203c116481c2206403601d9070301a20500c29801182c2400d803100d01d20a10248416040e008007021020340b52120a125160042c1d066212a0160314141820622000b000c144510041e20502064004010b152100002a10084d2207000404086034940028100003000e038000d540c0209160b01010400c07404041c03107a410601b05801510945105000481d9070320b000c858449060300e100d0243c0030300340348600700481c1d641c09501005860040031000000e183c0c40000004c1c07049428550f1810002c64103224002d440344951300c0040d00000112280c08030303003c1c2640c840408120503050040c84c0004650f4485a1600540081d81454aa642700c0c0e0045500c1820844201031210f0090300312850501c0020b1a981c11051440080000c00e802c09152a00d80804070f0b804da0b07034540400c031825079403803401c072024080e6400703811041414200300050040000c0c0d400c5032016413140f511605030540075021540d590f1014400e0301006045480002c2d4011244000d0481031005002c00c00d9642c1010701c080c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 751054280 1250 751053030 751053041
    0x30406020c0d0f03140909070804060e071d0a021605010e060f0c030a0903021f0204090e0a0503040303050d0f0606050310051e1309060e16060f120207050a05031c 71
    0x1c40c001c59009050100046582c15030091a503454140700101030000201440c950160903038054020010801307005c2425005054940300b18032480e01032100918015441e91610090301c59508030070302c13159a04407001d440e0040c1550140120b0760050070048041c0f2040140e62040d041910240d5640b0107039415008140305095200d130048074901784504211004d240d6610000301010085507407103141c2000c01d4828851855802201400c0b20b92030305440004800a43c41031080694140ca00b0203d0022030101040100305103400038003560510b880d54405035240d81c859800d502d580f40ea2400101c0c583da4040c49900083d1035280ea030191245460090010400d0158010511410044c00c2c0c1244405140210045800301650000035480c401420b08026000c6120002c2410f030038075a04075180c031400994684034060070803400c00c02d20345c0e41c1010b0300c021548140c2c80c0c000900b000302c9002c940d00b4a400400100f032050b070803106c0b402855111607041d60409824000300c0c207c0c0c07201840c4540e006c1e0141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 751055530 1250 751054280 751054303
    0x13030909060e060103020c0a080301091d0c030312090127031106090d0e010c0b15091b03010306180b0a0506030705030f060103030e060403120504051318112103040602 73
    0x100030031030928240b119015001400e45040680000d50344100300814081d0500c40d0382e000350105c0d02ca503124408040505960543e41c0c01e032030001000e5864031600015041100340c0c014024500e04209456100d41e10a0020890311840d901c03900500c54003000500f94510f60380388110002c0087c3c110b440c4c01003001150840385840c030740c4442d0038810309080103d030036a940b207040c4c180f4003004000403005882003e0510301c007808022041040010708400c244400b00d000da8202c840650b43d03a201241002000d40c2c040e100687c0350001d00044c000580e50f41c0c001c51b007440c2401140c1e100e0b8480390780e96140810b0116031b01a5140d4446c0244000d0741020016040070702800c4000e030010ba1000fa01032551000c05200c090b0800c0b061820a18580c2c0340e220465010b1500300080c1240101610405090b5500c18400c00f80200ca010050282c20581803007103c1035031000321010b1865400710f03140c185001f01e10403c92648240c40b00b404403046551442c4040e51076000201540c0c039149001400f1342080107107140c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 751056780 1250 751055530 751055549
    0xf080c090f0702062e0b120c030f1b040302060d060e09070602460201090605030603191502070f21090b07030c020d08092d12030c0105130309 62
    0x2842540b40c0c001c5100e5074840001e03d520404012200208103610742c00301030070850b0501c0c00201140286030100103200f50f04011000000316224003100e0455840121000f02021001da804200c0b443d100940e41d45001c1608240c40d802c20351250005030f0356034041c0c6201c90141d035407130404200d102e040703005030781c1e20a42c0c40b4040c2c0380d140c0c0751640280d280c5100c26079161101004010919035012512980b844801903603d10319000b81100c02102e0710003941d403e0507408901100e0000494910407411284900c00c050090f218100580f00e00500804072000f0803607400240011940b010ba0b024400380c00c409009481c2c3c182c0f0031245040c4404a0150032010300c0c0b444d0340160f1401051038201c1da1603800c46d041c050301d055843d00b245c10100c5010440500003035018121007890700a1150003c0038000801c0e0071549002c0306e0070308034001204040c600403143c00c44014441d5182d1540381c0010b02001300000d00051381d00e080d01f48041c81e42140c1d0121100301b583c4800b9a1070030140356100d010307040035068000c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 751058030 1250 751056780 751056811
    0xc0c1d160e060901120e0312010e0c0301060e040507030b1207210201050405010f021609020405041b08130c03020306070f120204050a031e120f1101021c050603070f080c09 75
    0x70041541440f400c020503062000c04510300b200088107910030b40b0810f00d2003040d681c4803400c001005005079401e200d1007412917032840c003007008022504109d90407105540c40d015110b0380d41500744005420000c2040b000d00d9a038198401481d2103c2201c001d0402d69403025000d43c6052486610042400c1b5001a003803010720510b58005076013041c2209c0c117850090800c0c4822003162041240f40c110410311600c0341c0b0b018404000740001c5941c01a000b9900101c03424083c000c07000d40100724a201400038480000d560a010440780c007494600070305003501907810324084985940101340b03090310a4414000043c0084d0800841035030002d810850100b003034406500d828603110008a00040e036002c0940b0544a1685000d00c80c180a526150701d00d600c410165041d000c0d41c8070160028100c0400725010410080d0310011820041c4203c842c6000340864091807030356221007000060800900441d05071040f59404541940b50003030080040000b0070042c107140d950f2030244012124040c00180c212083c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 751059280 1250 751058030 751058057
    0xc032e09080318030408030f04060806120a031202070c23094003020c0108010501110316060e03030108011a0414071206120b0103020a060513060c0c1d16 67
    0x7908903600001a07000030004034001c1c0c641c03036096214591040c0c02a110010b5000350004a58010784100d550036140c0615030b6480e04140500181c019500c034076203806c0084d94a00090040c20b87c0100789c036085000600b055860740e5880707040d417290380100d440b41c0c01440700305030050007a0004840c0501d0a980960040c100580710500340c60b4074003605030030100d031000380f0700b0480070208400b0300c0320800b0a203940842e0b50b1410003035114078250054500007404a030001c00c1a5029007215185445401c00840c5051804c0691004a14107000c00311131300d80c1c40d07002c900d1251100700040c601a142400002840d0900c600d2840144149061514051410140c03090000f40f40c05100f40e60200681c2050300789810ba41311000d00400094000900741c00e05a5009014043d11911050607a44259403180c501505c68206a6290141c04d041400c05038040409001a0744206842134400b0300ca8182e0043c041e80342d0152441c010310240400c104001d9003820407000f4075061100c5075a4807410304042d8001c403c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 751060530 1250 751059280 751059293
    0x601021f200c0d141b0a200307080c0105092e0203030f1605040b090a0b0415080f060319060e07091b0e03211908040c09060609060f020c032e09 63
    0x5542500c0174004800354620124002803104a69545d031016038150b40c12280300903044007103651000d1500910462001051100c0e0000340043c010380161a40360618034030808000407120030003001c0d088025400315004040e044e00700004500009a005142c491800c07204440d0071010060048088070a16400b009006030004110350650b0300c08070045554103483d2011864000d0b0a520030b0040442c001000500315400c040035525254096807011906d840b10000c1c4429540240d0300b0302e0381600044503448100000c000c4244003a84950790106445000d01c8aa40c01d10b5182c1e80030110043d00c5032141402451a1100c20103580c0d0103081c030700310200015002c255220030701140d01002c2c0b407000c400800c00e9900203040e5281c2031111150800c005580420050000409450895030f40b0f14251010540018030b001d401c0a55505070740b098855460708504847d10440017184000358042c8805540180e181449140c00c64042245140300b003101010440a2070b40740b14100c5140d02c1d10340810318000915 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 751061780 1250 751060530 751060537
    0x7020901060807050c0d09080c0d02130914030d0c090501180b0c011410031a010321090312350a2d0e010b04050601021f200c0d14 57
    0x110b01d4036403580d41e6265070507103036403203841c00d144402d01c00c03c84034003400703944080c079a0250758501c01034540c50010501485941008c001c4002d47c40800b800d00d8058020003030f4064411540180882e482d12100110000c1c2103a10a202180900d610350700c08440c00c5421050300c8009000030318080da901155032610302c513410380314000c2c4071881200140c4c0e02c542c0607007500b100080d030b40184c0204c1c002d070406840400c04080380d444211010864812080c084c0190354a0140c100d90b0000100c00c03084500d1049049c40b203d0301ca5541e014400400000302c04512800d01c1c00300d00619a17116400110100c01010000d90680a01c5120502c2c041140440ea600306c00b02058122041c01c00c04150200e40d81040d940c0d20206030008025040c00b5100004803100030741200c2a40085d10303000304410583c10082c0001e031007040b1800c1d80540e00148001c181a46038005507011030000000005000401071829180408041c6c4007815030034010813a4400c0e80001d0140c0359460602e4102201d0301c028039000e0120b00d02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 751063030 1250 751061780 751061789
    0x60c03090117041a09101e0e0a030f03020a0302120903090111010b0d080d11030c0a0e030106030b04030c110603150f030105011410021501030c030b0702060c1b070302190501020d0507020901 83
    0x2503203d010458416040040050580b042d25041c0141c11200c0c1b100001442c007c0140184141444440b281d115000b003181121180c2541c2c500c0e00c07149000740190069400030b0080c10425508201c116820044250428021076804d40615940c000c614001000503d010b09a01c950b40d00d48841120959260520410010f0344984a0380d16407941140030001400300c03000c0c43d1142400007042100041a0b00c004240404440d100c607008542ca030810305080300c049000080250070104086000f29000e1407182a11521030b00c52040d203a035802303010035940e41051f03446c0e141c004000e40c1e512003289050a04040030280517402040b00750315240010711103000d4000f409020711500c9021407106e0740b0034480306503c4083c4220840751540e60b0720300740c0404007440c40f0070b036401c3e1240340201c1c1046101040450242c4401c0c80d07036034101307800d01110b5008088020034907080b61040300720010041e00c0d02100070320040c405414000c0300380e00c3d120019080006079602c5104002c01006094010383e20840e2146c10745 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 751064280 1250 751063030 751063073
    0x160503030912240f280b040e010c051b0a0c0e070909140a110901020601060f02241617040809040608031612020a030c0206030a0902060c0309011704 65
    0x40380090180c0342052400460100310740b0070240480088922070000074050b00e10f04000740d6103540c50780c01171100d030107004616900d072280071640320210004940040da0406002480003448424a00c885800c50390b00781c0f408400b0071008500842c02c90b10011500d2020f076814006000046d0140e07441c000d103661203000d812226a4070901140110348034100c100042e14401500300452110f0755a0300c100d920007110009481d5040c18076054280349103d00751003040c1d41c181c0092545d039090803425581c5840181c14182180b08003030b003500b02020142c450340140c16084041400c141024203032031814070710000c800014842650b011007440001c0c9032310030707610941028000d5141e4512030006000b41600f54440d4095100c00701f40c0800f040b8035800c1c000c001c0c3c1d224000d030307a002495119046e40c0390140208081c0108401a02040150520100460740100600d00c002441c0e01c0c00d5002604940090001c80420ba01c049000501542c00401d03102c001440204c080101c0d203041d96520030031680843d081e0f40b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 751065530 1250 751064280 751064299
    0xf0d050c070b030408041d06101713020111300307020d051309060e07030b030601050d0b19060609080124030f0f02060a0c03081e0708100306060e04051605030309 71
    0x34000c0391000e40340a0007c041040000c1c2442480c6940030344c005807806031050403901d62841032603000300c0003441910000c000504040d5503444484407602c1c10020182e0600120390205a80c0d80d1080c88070344520100b4030b00d44e03113441b40500400442103081d8500b00100000800500814039000244a490300b102e518009135140080300c0c2103410411558410f03aaa2400c140000c148140381183c818030503c2d251b81c0c104075052401081542d184400c0c428581c002c042d42805501207080d410803a6403240d600c41c0400131920400640340100c1300c0661100d40094051001405070301c200303001c1e5050b80c03808100b2014100032101e80d0806480c103d440020034040070100080b040006201034000002d8004241548803502444040c0c55090b0341c0504800203a00c0000040d507544e02c201c102401882c403268410050b503181c81055503020800f40119035072942082e4000700003169070084901034200780135103c2d0701e805e09180a51078407107000010543c44000310720500c403984001064a030030f004e08540c209032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 751066780 1250 751065530 751065533
    0x120403030204050307060806040b0406260325120e060d090219030b10090509030313050f060a0f18111e1f020d020f0316021503090f0d050c070b0304 65
    0x203208543c00f00e6018000c0c13440000f04103030040c600078400e400035182402424418420007048604500441e0141c15500011074540040440841000c06040085a188c0724004001400f600301c90010b0f40040682d58010100f000040c0c050143d595440e401d20084445c0f07060700040e46030088807020036603141c0d0b600904041d541c4042c00c05019440c0b030104417158030740340d04001c10300c0003042f600001c102146401c0094540c0c001d114142c890341500020f5130075621119404038158a02c554142c4151084c2e1a0010208105004281c02604c07009400a0f04000e65010f40040d25040c042e82a441541820300c0c801141d0400a50000d0b4002140c0c80c001034508072150020b61010b40c00030a800400301498680c1012050340b403d4503810040c0c00311491408054412640da002015029a983c0c00c207024084020040240d0703440780341d01c000c01311702c519400d0604403800742e0011250072030280d11044d01035401079424071640041280c0ea140051505805030400c90b600c0c02c1a120790b075a8820000000b80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 751068030 1250 751066780 751066787
    0x4030f120516021908030a110715090501051303021e010621020310090f0b04020105071218060f0507140a0c03141203151210020a0215010b0a05120403 66
    0x155410280346042190742000d6030440803103041105010050b11400b150744a181c818031031042c6610360302006091450303a40510f0000542003644043c0d10f2240c05200b58400106005c5020300c1c03001030501d0000e80d9007aa418010300b9100c1c080c141344018004445000301007540456141130407012048440c40d80f03854032280500400c1d01e42d11050742541b00030303111210b55940482034481c0a0003142141c4840054003010001c403040401d0041c0301504e008400e6002840d1400f0b0b0503401401410b0450a142d04d503140d5524501c0c40b198001c000440c4010700e4000e0680f45451500034100320f2511417a8010100d402038140e108901029010f0625a1240303018080204440c4801a40c016148080d0300d580c0e103040d2501c84954903120b18070707008800303c02500c01c18080560b0b100700b41307000503900103502c0c060030300ca05cad41c50306003454004c1d004440d00200d1406007070000b0b04d22183c00354000c00381d41c0d49a0300100c1d003051060304810a51030b02086910b54887d40f01c1300361120f17082d010001d0352a607151032070185c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 751069280 1250 751068030 751068047
    0x6050603010b04052e2303090703030f090305070e0105090a2d06030f12020601080d120b0622080c0f030a0618050115140616120908070e010614030f04030f 68
    0x1a00100d100041c501c8010307074081c1610040d242011031010f00f0b000c082079006c0369030001704c511a41c0c6500607042040424440d02424654042a0829004041d200c3c0c03a00d0341484d10b180c02c000b0680f03048400400040c00c100081a520400509041141e03071540c803084150f420708008d60760b40710804811740341d0000e2682d07400b0b1001035078030031111480c00e4018070b805650586000200f00150144000018907228081540500c5800d82d0303446000412000f0360385401000c3c10115640c00134014810014645050b50740000700000c854190418245007110345441d09842c58012805030240c03620010464030002000e1012543c4041e000c140340c0381d50804035501408564003d030003507003007602d400c100c1c16881c04650140d030308400d030340e0303000110301001d02a261241c42d000e030500782c0403040000c0106200d100150210030062a00052140e41c039101c0d00d244c03c01d240c10000c0035005002c01004255049844bc0318001d484921507815031038801803107104840c0003403001d0144170200344e481101c80d01c240d524 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 751070530 1250 751069280 751069339
    0x306150e180a0e1902040510030803060405150d030c0212010204031a0c070503071505010b0412060f1503200919021813150b0301150c050c06120a06050603010b0405 72
    0x40712a40400c44980100b41c03020080146d0050340341030007290a00380788510030401e03203410070303e5140303192500c1040c40b006050050548060b1041c42c200801d940e514217440b20010707030180ea1150911942401002060304100e072080d45d10341e104003c04c00001d11090342c290000c20041e014070b03e0710759811114042e28401c50300010f101f404001100b10400c4680e01c1680e019029010042080c0c0e80c0300c000030200792203103025003c10a17030016100720004245e40c00104607928480b5000c180c8400d00b001c107098030680340d04225180c130203440300409884008981c0410f0110220341d420a02c1c148071005111101d032003040514444d0700000e2405018200d0100308038408800380c00116060b4400071070030011f000102840140400303101c00004c0780050703402a00d042e40d002000c00b60094144103000c1d00c4800d080042150140201031440c001940d4034005840d01c46d101ea002d40030342d803420f003142c402160100e07002035106150620044c01080e00100654094900545240c2c05510354140200340740c0c0030001c807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 751071780 1250 751070530 751070533
    0x612020904060b04080c01210203091e0d08060604050d1b0e0a0501030b0601020d020606011809050405071e030b0a0b010e1003020d0b090105030a0f031e0306150e180a0e 74
    0x700000e00f041080002c0c0203d4600e0070617030380f1000d0350400440b407214802260015112040c1900c44100042d54021608468841c080702d034502810040f102c00316181984550003500854004400300780c024030248c4d03200304c2c1110403600c1c08c0c1c01c107000240d031003800c440040c0c1091134050342003009200c407581d02d50282003250318140440c46d00720204000b422090100f101e0303400203100415403d500024101c0c2d10f003007898010384501c1c0e4550004584000850550700021400c0390000920103009120702c41c010307800350016050140c208a2109071524040d5020039031030790b03200c2d401c001040b041c444c8280c000400100100300380020f00012248100d0942615610035010f1a0500815809d6030041c00254142001480402e0304e040802990460901ca5941c140d084014000e001601d80c21174200c074944a400c00c0b00c2d608400320320b4400c00e0644201c620010a075159400d200301c0c41d4410140c0c050000d50300e400c42c0b80424200108103a00c1d0012924035982c400c00011421003840d0342c0200000000020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 751073030 1250 751071780 751071791
    0x612210504091b09080105060906060a030b0d05010608010b0108240f03031305032401030f050f03040f1e0b091e0d030309110607030215250203120108010507090612020904 75
    0x2e0b003801072044160303500380450130a14000078039030f1043c01103d1046200414601d0196503050901035961300210320101016236031198000b4540d685003020000e0742c0a1400015080d08102095085802154145050000c0c0308100541c0b99400b1020103900c0e41040442402c1481240211300d95003190400c060b0b0600020600c54101039141c003081c800ca035000c40c21110300300d00b00e030441c50318804400d59a0810058500c01403010034030300e101c0c000c06c40d44038804440c18454102c210b1408c6400c00d4009080c000c000f64020070844000800d41101c1e890904c0b20601024504030031010280705821015004403140180c032041c3c154a001240303000c45000d40350b04c40d50241850700138001c00e84010200c0303150b6011649050541808001d407158180d15030020620304000c9100c5910842c8014060742c4540080c15040d1150648107034405081e00c0507800440c0ca4407592806031820240580180c9410b03032520f020802c030b080d4008000000c541d03660074402550055050000082e10408800c181c1181c1030a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 751074280 1250 751073030 751073051
    0x1f0e01060f0207060f020d05160204020403150c0201050c04031b0302030601171006050906010518041404032c0609060c1923030706020c0a05060f0a061221050409 71
    0x820120915002d030b0940b200c0c0e40c1c6485054a069603100030490050740b240070040034150148000f80502d90407182810071440a42e400141642e01903002102c9084003183c0c05100070400b4011070500e03070801d000a004c03619000000f02d6480c05070b44805003025070b17001e54a45080c4030f000c15540207140c018080d51031541e1203124081e41e6142c2e130103c1c0d00d020320a081d20302004004920810060f81c1c00100020000d4070303904011100b035001244100510140b0130140480f55132940700e00d11000f04203034440140da160a003005000c030742d151904d002100400e4550071031080d00d860030b00100c0c08001c60f24a40c9480301900030030060f000e000b51503000741c8188200c80803154240c0c03008034900303482032485424682d080390018042500c4070780e2081d15640b0900c00100005e0240c5c020380903120300c80c4200d440c1c0e0000f0380c860300c2ca4808107035249070307120f8084003e001c030303020650144a006d0700a0680ca142008003698804030003102176001007150030360310039440c15500d1081089500804800506020740c03101e5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 751075530 1250 751074280 751074287
    0x1503121b0309060301090c020f0a03031b0305041104021c0501090911010207080c040b0f1806150708040e0702070e0916060e220b130e010c03090503031f0e0106 70
    0xd200c0003045060240014403880000821160304840241003582141d10f000c1d403540241c064140130718250300414503560345540382049404801d80c0265004580b1800c1042052814442c028680c820581010100004a072503a1110140510140d500603503540030807081d40440540401c65082d514100b20000604038006d8104030f421368020304501c07100390440001640e60306040d00c14491581c0188117054010b18259214010300c4c00302422180070700310404001020a07100c0c1d4230f15034070018400d0510409080008485151800d03c107900c0c0e107407240644514201d4000c51040922401c10314001940780c03842800103100406200c000000d4508010100c5510781c11418000840300c4003041e40054418421b00c4403001c1090040c18415555522800c19510100503c0c0040101900d0340000151904c80d0340142580d00506180001d04440b00200c1c0c9080d6281c0036816000c05040404c40c1001c6600801225001201c0d40700741e80703280307070702d001060713501c51840e40541d81c1c0b402110b0000071070710b42 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 751076780 1250 751075530 751075537
    0x20c12031e0a0c03080c0f210702010605030a17190507060b101d21160902130e130606030f03030510080c0111150103110a0626150312 59
    0x460441000d004602035112403070300e0254100b8100094001000d0001281c0141d8415070002d0702800c0c00c6107025030a040d100c005610041d154580e2955802101065144151105810007070300d00c000e2150600d00f0b000650b032082e0b0104094440c400415104c0c401900840450700c3c1c0e0480050340b80074842d000d03007028149400c0060300ba21050304015000490f89011401c0c19409181c0e91500c896207034640500585034480b901000d900980503500314041403103405090308041079400700400c0c140c1c0d400c042c08210303400d090740240c0805005000c1d0001900e41e1880c2c0368140c5210200040e00e555548442441218441e00060595450b1034408030030300920100d141d0301240079031420300564441da20b421400c404503101d00c0c0e9054115115180881d0320464940c0454042c620031194200c0203c00500d185c4070342a80119560b0502401460060502e5529030b030090041d401e1140186c030b00c140c0f902c881000401820140c0d41c0c1c1030800603050300340440101c1c2412030040c007142c02413514800ba4150035807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 751078030 1250 751076780 751076797
    0x70b0d150306052a0403060c020f010603231b012303130c0b0a02070302130e01050c030907080304060f050a031b0e0a0906060c0605101716090506030c10020c1203 71
    0x400b0130780b11310140b5440072610031160003002c82c12460315143d500c0c1c58000f0440b0b1b41c01402140100706082e80108001d0240d03402550249004d0340b00c40011089034507002660240b0000700303400c00703101c1038000843d203086049424400e0074030710400c0038039901c50b0055140d0403d407440340480100500c48148044000212802d1052840c020280d40313641e4061024001d180803900140d0182c00140300605044116094410748407502017070417034074114850b0940301c0498628840c4d11010040040348170782000300038020b242c0034001d90b150a0900900030700000302d1840d040e05207c40040d4802d02c26103c0e6009001d010012101080c50f401440b1000380340c101d4058a29100340c519010105001802c0e20904044840380d0b02c82e00c466110564420002c0e08000b45860803d06c1d5113a000148030603038007040010b48016a02901075441c841c10144032000180e085050207902e41001c01030b054a00088481c034026046880e410816844081280782c40c3d40680420707042040342c00034030b0b05410004050111380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 751079136 1106 751078030 751078051
    0x80117061306110c0307020337080f0a05030402040f0501060c021c0209090d0f0806060702060721020c0a12262203021011070b0d15030605 61
    0x9400c138000240940e0000650a011441d081c09401440c0d881c00a041e501d481084443c200040900303400d04242c850000c110784288580d48040d070303500c06201d082d210768a81c0da4410050154205a900703d0150381011443c084800075030060505032800c40c1c0d0780c008174100c0e640810a05228441140e400f1032900c50811001d621001c440300c0c800c000840c01480d1602021000a007800d050404807020001000f050010554894084820554040f034070b40303840d0515424800000c4414031150b0030203000400d00c900469801140651020108441805429554070b1060709041c05601d802060920848502da01c464404584a0310120a505100381003c00c03880f4014400c61821603024032110914a040046150004540d104072150b49040d004101a00c1c8101c1c0d03495a983c001c09148410100d0003071620441540846607010600680045907640c9090250040000340c4848096 = true := by decide +kernel

theorem cover : BRFrame.Cov 750899280 751079136 := by
  have h0 := BRFrame.cov_init 750899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 750899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 750899280 ≤ n) (h2 : n < 751079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
