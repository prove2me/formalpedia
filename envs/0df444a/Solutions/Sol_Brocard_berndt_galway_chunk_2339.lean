-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2339
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:24:42.098223+00:00
-- url     : https://prove2.me/submissions/60a03f86-b2af-4e01-9e15-edb1c4bdabfb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 420503597 ≤ n < 420683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 420504847 1250 420503597 420503609
    0x181c052a0601050312090112230a1b1202030a0b090c0c0105010e010e06041127090114130b1906021e0d0504050d02060405090f0915040f030315030c060306 68
    0x41c0d0942e803240d0a140d030b0741d4454041d0541010007070002c8583c56100780890140d4900848010803e11401c292104848204080d52000201041e00700600702145101c1c5420121b2080c07107000340d000d48000003800303100c3c00340170b8440307099000800165050300c16001080401d10103028000c1a2404140343d07a060303006100540e11a500b890300008200020031043e41c16100d0010310416543c41e541c0401c401044880406200f001040c00a90340010480e070402c0714518224403443d400314464130401161040580100c44112500401130f43c05840719101135000c483e424034002a40101d0784000b03006080c0038004a03044203981130010079841e03408920629a6115501c00d0010175803010035654036808000304040003e07200344400c0042d41f61008144625900140c1041c4c60b00b5220b001080c8e1b0300a0848880c000304205009001f0070a50030402e00ea04030310f2009400b4001cac145640c0da40c103840d264240103030405440f100d40f080381008242c81d1740021a4030484550364a581c400016014021502c910 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 420506097 1250 420504847 420504853
    0x7140706020111030103122d09031502041202090a0e030304060b04050a0e03090d030908030313120203090d12021e01050105040c02030702091611010f090b181c052a 72
    0x128500f280700180d0303041c1c03684022585000328031a10101e48030481000004001080c060101040c907032003005110030314010b0b84d248280b0a0940c20720380341c030518a540316008248104030401140d14040c5c1803882a681c1108e1685207900c55041c650050010907230041134501001040c8130400001380d12034030800400390703800e04c01035481b15120001c03a020310419440325001080580258504100c3e48110341c0d1181c203010201ca03880f642500d145800c01c5880b582c800c00ca03400c944c3c0c2400202c001c49403524800348020b51500f000b04000c11003240445800400980140c106180c441d070003440b07100c0e805500c41105018146481600703a001c6c1000303101c3c0d540520716042c843c043c02d234130110844075011b80180410100b034583d240050b42140401e070880d8104602403490b03a846007001e0103440d8242042d25804115000c09080600ca1041d02811003115505403104000d034205012075080301d0300e004405010070b03000c14410250b42a111704007201091621400342581c40c0c26204111500700c0160301e0031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 420507347 1250 420506097 420506111
    0xa02070201031b0206181908070b011707290d060f090e1b011e030e1009120c0507120803011a070201021b181608070504050123071407060201 62
    0x11244003e14036688001600000d00141c0381c924036070340300c140c07242d00e207011104e02c039002085500d802548228111248a4006050000e10842d10081c1707014201e04520140b01c8541c005100356612800d20924260f008624000074110030302101e0f00307510315440c0ca0a070790f075841c1c0300c0702c010700800c0c0714000c1c108201c201e09004901e000c6281700d14480c5442c2c010090000c4051a44075600302c2c11102c544604000c0303100084808482c2c20590820100c44a482c04a110448480001d00f4500f20100320043c0603e000c403241c011480510703a0100c14100c40c1003a81541d0000d0606030706246240c0c0040f142d1142ca40022410820210021812900e900c0010302d4584510a80103034035105d070300c1c0c0103070041e400f400c50130340303802d1401a039820300200091410122442d800c443c262000c20440d20490461403011041681903000341195034404082c1c1380041c074181c20000040e16011104172403070494011545281c5201048100f2652000e4011800da102d0072092409a55200b20070b004020055081c201 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 420508597 1250 420507347 420507371
    0x30e010c0503090a0f0807080703020d0306120f0602032e06272709030e0108060102060712020f251a13320f0c0105070c0e0402060d050a0207020103 65
    0x50700d0007640c48001138030084072103031901c019204000318151902d0404000796800107491034020710b01c0c02d03c00c0e0054580041c08800c0a811115550312407480302d107031009130b440001d031000400790f00070340e00950040c3c403503c1d14400b140c3c24007607502481c01c1c0030346801ca1028660f030345502100220340c003603910b444841d0450b03034500ba240801c402194403009100310060100c10300140d03a020748130268004801031031200d004060305603000284141d006c00c01b24540521305581c003450b03290b4001001e0004001178100001d0050005007590080c120040d80030582c40d00074000c0c20308403a51030700038044992294540f6804600b43c00035801e0102c2d5841d51010300203d8110880004511854850031030b240c1048068a40d90b81c81c60310b2040b08040c0391002070b0500070189500c1c2409040e080c0e008020b00c000b4004e04101894421114941410710200323204080014600d40082c82c180c070b108141c4907455840da13101003481d0380500179558810740e04100c20004003200d9940030f403451390b000741c0c1c080c0f1030003a03c4d103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 420509847 1250 420508597 420508607
    0x503271e010b0901030602160b0721090210030c0908030c1006060219080708210105100309020a030f03050408100c0801060c050a110f040905060402120601120f0c0b030106030e010c 79
    0x307001e41c00c107503c0c40c0100042101079000d040401c508040c210000c0009540d60b10014408680e21804903444140400b4984814015040c6a039452403041110401540004a182e03040d1080d490806840d0401d0b481c1c910b02c030b602480001e041060441351100101798242d03890780d0304d000181d24802e19000c070020380a803000406004051520301c07110b000409a8940801a5000d090113555800d010440755001403030998000540d40c120075250512541031600704101c1d054241d10402c100350400b010760015a407601c014104882c1d0040800c40d4401180c0303004d03250b038011a48107200351b00070315880000c9400c189c1c00040503050155500241a0f8031064281c4401000701d1002d440340c2c0c005007500700051045d141480c40722038010540b14608841c0d900160644841010894880d00701c1c5041c40110305107030840b1020450b041000e00000d604240001580056008000c1c0c1040310342664007080c0811080700308080c0c039560549030390f25030712007101070040c001c41c2111100641c60326041110081c811 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 420511097 1250 420509847 420509861
    0x11806090210020601120f110a0b0a0201141b090414091005060312040620030f04050906091e070507020406060306030506060409150b0310051e09060403020c010503271e01 75
    0xf0400b01b103c55134a0380303400714024410398040394001c100300640c010030754540d55000011304003501c960355030b008490402425581030f40c241b0040300c00d4035000d2041102e686020901c55140040f000381e111b42e5080c0018020301281c0840031038000b0b101e030030702c05070840200c1c088481401621043c89980c86080a050351288030005c1f00e10355032000d02060140c94802e040940002d2005040c01c0382811036081c8890071a48003090440d400d10703002504100794106219150741c40719040301e00300301500d400001450001450a0a030301da1401d442d00084009004106643c00c90360054410400c3d680c8810002d8010300c00c0c1c0c00107444a00c078100004515107480d0003268001a40014041c0021100c1c81c0540054101c04000036458000c02a01d01d2280c80e1a1264901c14101007000c60618044903040314a045070142061245e600f08000304000300340c00042c0030060b000280380c21a9a039890344070940760381a250658664141c85240b00301403560000407a1100305100c0c16116182c02c6404846601329100c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 420512347 1250 420511097 420511109
    0x100c12050c0303190e06090d090602161e0f120b0603030a0e091803030a0b011407031b0c0b130302030f030403020117060301020f030c1c0902060d0509011806090210020601 75
    0x41000021380340d0f1407054115100f401210408100b080f1140481801e00c801260007803600d80c00032110015181d0f12200e1703c0001d007864006800182a0840d1342d2954071802e0080a07a41180d5810f0b40e46540601e004d40802800601070041c94151914202c8403142c0a151050300c28542100110748549004800c0350070f0340b8880d4491842601980c020301845c4840100590946081c407604403010000074801144100c003542c20002d00c94070b01c44000762020000b00341c8158603000501c121800a60400044921111440c24214600e0018a0030010b6040b254100186908000c0380c1e9503031042400d03242d1400ea9100300d0643d080078540ca0103066490103107120103800526488402031004814840158000c88064005880d10720109424641c83d0b00613102942180b00020741c0000c4a00088000c0c80b115119002c2400f000c1599000154a809103141034843e660340c40d00402d504003c258440c03080341807100d10a208100940c100500102208e22003a030182860380ba80302d0710284040346c04c40c141d4035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 420513597 1250 420512347 420512353
    0xd020d08061804060608030f0c010606020a050303360d0e0103020c10020c2508060601031e0c0e0301110d0506040203040b07180504150314061005100e100c12050c 71
    0x4004070b1690a040303002e88141c4100d90b680f5008100e1901c14001800c6c0c0c50481802140c1c1c0d4820b9800c1903007114000d5228104540000b4002c0002420202c11a0b130040d000c02908580e602001000002000030050144806403080c3c1c100301406102080040c032140198a4001c80c014a41c0015403d91051a201807203035040346158001c1c8581c1580542071407190802164606c50703200f0031078201c5806800d010788a00a580c0c01c10855254100100e80d444542031038144810110f00d225510020404015104840d407100e0540303041c94407a00c0c6086024038014000c2c040d400f510403034400c00d03a10445600620500b04800144141014002c0340e000e190f00c001d03060a29540d1480445110211501060705003500d0345d000502d82d5680c1c041d0301c003002c108002c2824681d25502d041c607498500007020b040a5044070040122820030f80080d601254000c0d03400040d01205d040040f42c045a11119040c2d00400d039540d40d01441da40070030f1650070f040c45241841c61940e086601a2000c1c050480341c020198 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 420514847 1250 420513597 420513619
    0x60206061e040c0302040308070b01171513150c1e02010902030a0204181401050601030b0d020a0510140d050411011403060d02120a241122170d020d0806 67
    0x4205540701d0203c04610340383c018100b940b0396881520541c020310080e2070728000700d0300600c0f16861a00d40c2685a5200e14000d14407000e880b200e06640d11401085000c44400b2522740b503040c0003810210070080d0f01e00b40ca00308030407031003588050180c4010821454003a0442030760310a02c680144201401103070014020140c40110340d00300005848044001c020764008000b101e000522031404503440880c82000201d4185405d074001400c8a604104c920b201d144903064520140c0c1b182c030840c07000c0d201c0542d4092611070071a441540c001003244242c1001d000c0010313284260314816032050303004600c42e28200c940f00440e10011154401300000c150490401040481c2c0c0600e01400c0350b00390544044d2041d4404100310a125040000f0400150341c5a080104080000801946000048803d0180c100301a115240081055004005034002092003544480306d0701b200c403141d002e00501c21100c003100c008039600c22030303511880c00002040252046040c181c0c281030258107543d00c00c00c00036000240700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 420516097 1250 420514847 420514849
    0x9050702010221070215042105190e0f03010c0f110c0d12030b100504030b090a0501051003170a0e040218030613050c060408060f0417040e01060206061e 67
    0x141405848a41503650030422080f00026a107085906000703036500c103c1c0f01c0d24007042c01a041104514444038213986000401c000242d0031319141004500b881c40e00c02e41c1418250050304d8900c81c0007002d1898140e030b41001e010342944400d60304103d800a031401c0441130410303424142601e0f10511204041364011533040300080c030400d0180c40341070481c02207a64104520010490185c50340e0300a4961000317086075a260390760140105520701000341c603114101289020001e01c240920f0000800c10301700c900c041240600700700300300810190800020071250802101700c40010326148821100700c0b5400e50701030340c022500c0007a64810405078982c2e403890880c5904100c02584202c81c0e207a6001c030711790a0805251030410a0f68032811540940d00a01896410f1040c40e20344170001c00ea00c15081040706001900b00865152340100350f0340080c060644072807500070301d5103c942000080785e400200300065000e50840e0654100d0781242c0a81da1641c84c1c1a05001d00c00790681334040100400a00050781 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 420517347 1250 420516097 420516101
    0x6210a150207020108040b07140403030503161728020d0b15040e010b0901170f150a1a0c0316080d05090604030c0206030a140114011b0b0103061a06160308060102070e0109 75
    0xc004230341d14040ba00008002411401d40d00590001c1e00000e01c08001c20a902c52910800d444144040c100120f11042090180a49810013400614036101c258001c03a500304800d4204c204444c1c0c1d044040d0b442d207032049080c8000300340b4405403511a9842201103400b40e40381c0030807102514010000d50316140c2c03c0c05450317051503100e0b000f00c3d0304003c140c040d0b034601d148030307000310600a4031810482034150400144640c803810f1005582442242d404c5406c10100800114158011885201003901c035040040400d01354000e54104420340c071300c148c0f003210030010181d0003012510040c41d000c12103626000c2c3e1240da144000c4900401050741c3c00192800352034050061079020034500e1000c9070784103011070b26071404042a40001c00e5020450401c1901d981c00407a242c0c280700500210403242191a1940300e403010044c03002400c2c460f41d800ca005864086000490f1240f000074010a42d10f00c2952240a001900c0400a400203100ca6022898640c030205001c021140c20070749885003a42805c0d00303480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 420518597 1250 420517347 420517351
    0xc0114010f2705090601030b010515120a060b211b03180f01180512030906041b0306060e100b0405010f030e011d07060e0405060d030806210a150207020108040b 70
    0x2203602c03214a905079015024010507202e10380103001350025501d035241802c040403041e0440c0348586007800e4100070112904040e507628100c501d200e100a52214490500100000e070406000c000d000517811241d000b4204051441442803058200305544140d20a1184500d462a4620000741000802c400086188124495400d04026a8440b00a0f0790070700d0708503072141c1042c0b5510050b551700b040910200b407101e01c140c154454810351541c9000c00d04a034031a0b40051008000d41e200c045aa6080100c0c011072002030b40d0302c60020410280c03602070805590608460711001c040100c2c038003042c220042c406990490340180c55804800b000007d0940150650715660f1080307640c2c0750b00c1001d1060880340104406c500600c00347c4025403d10100078429595241158062420203040c030000d0344400b05034079100c0760585021400e45e200c40c80051107000f020301342c4c0445450b1190904007035110200f1141c1c1e07018405c000c0c0803900c401c14848071059001c1d1120189c042a203400004012071b10b00c0304469 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 420519847 1250 420518597 420518639
    0x7020103021b030301080106030308160c021512190f0b0f040f0b09010b0720061c15032001080c0910050705100606030513200a090e01020c0114010f 65
    0x4a100b0080525052941e0005d0b80044441c0c0c0d100e800c10028190000318681d00580b00303140c07c148460b05918094007804040b0340081c0038002c61640c0303904440200040d60585c02006584242c5820030300f02580e03240325481c203a0660989401248520341031103200d507410050020301118440c824400810008001c00304400c0d0040d07031118480e400c2c41e90f0711007c0d2806441010303002c03030b01ca1400d4141b641c0782c002552120946d0740c04501021801c0d07510501540e000041c1014514807645c544c1c09918080c1c50000c0c241c030341410582c0c6010041082035800d404491100081c074902100c5a04011a803880050314498644c40f1b0800c070300305103406c184a65000a84103800c049242004a0b078405242080d079441c4540003a41e0b07800e0522109615001b10b40c3c001c2c140c5d80c200114103440d5182c240c46500c0d120114610002c1e8100600c40c00d880d00c07080500242650003080100034201c070003c601030750000f40182e06951030b060500d04030558840320941a40c180d2a10452440d041c05c44900082000307180311 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 420521097 1250 420519847 420519877
    0x703090309051201201e03190207081902060105030f030f031501110a03080f01090e1b21030c10151e0b190201060501030c2703050f1609020a050702010302 68
    0x1401210b025000205e00c0d0720112504030381d42c00c2446d80b607841d0408030441104421004000740005c3d10030315015540811900d10b00140c1da22824545070f102c61103403039100c8480d04d00f00c440368040d40d038011070b0b064100c5c0e2082c5c00381c68294140d040c1540e22841049290400c10609001096a0b14040c030160045100103040510310b50700c145070b0107450200c0908088001441140030450400c1c1500250740c01001004802d2000c85c25039640035031039018203051006c1800c11512510030546c0c2d0850701108203c0e010000b200380c03e01c4800000c0d00e0758000880701040b8460182d400b1519902d900c29900c079102c03640d00c2049000d041595070048105185c200410710001101c0106010525800801703292584010000f024114a030000c0d00791a400d5010a040c10300e08040c429103550400891040c0380c0c014850000d10420013981c5480b0300c1e2668101800301c0c13103100c2ca00c00d1a90703400a030314000d580c822001048441c0d52032441d50300b64451100701d403001800c11700100005501a40103080da412030007201c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 420522347 1250 420521097 420521111
    0x406022d01021b0c0f0904031b020a0617090a0b0402010c03030e030f0406170c0f070c0305060408030f0f01050102070303080c3c0705031206011b05150703090309051201 74
    0x5826608a0801841082a000e07100500f81d0740401004d03064000c140c81307400c9070403043d1000400c0780b030008001070709200249414142c50381d050149601e0195004003202ca0550315844003c2c0301101c03051141510740800004a48001d500090811040d64048014a81651198011134102c071080c08100d05050710350324a000002c40030b0000c3c1c0600740e40d0906054032075280c10360007042d82c2c00300c1413248402640f01f4140072240e030f41401280c009421a201595845000340b03400002c2c00907503800500140112014002002441802140a02020340510040e515550313941401210284169409a030007813000300000f078040e10000c2d0380141c8580400381020700c90b030a1007050136078030640d402c000d140086100203100b0314541c01a008520400034682844c501d07594035a900d200b080c005208440d1403000060040c3c0c814240006000d20b1a140c812051841d40b0b8402d43d40c0401001c0700403800d030083d0000312468802c1c407610400c00d4240d0b407030322821440c050521100f07000307000c0589000c2d501c81107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 420523597 1250 420522347 420522433
    0x12040201031d190303110c07051012020409020301030636031b03030e010c09080a1e02120d0e2b1b0311030705030307081c140109020c010b030102040602 67
    0x2c01001e951076240400307030510203450005c041b0307a104880c00b90300c0b00c41070001c010501000500c4005a40301901d5114038414050310584040752003010361a40140001804120203034a600510b0481384591400d010340485900311550484240c0001d110100e402c250703481ca16022400d14044d400d000741002c90007c00401180422207400780401e43c042511000e02e8010b4804c24801d000a0312811700c0d000e443c150801c14010744a148002c03010f4400b002e0b6080004040c0f040100c8031a240d40c1c006e10040740c0808140a042c0c40709803090060000c12200300d00345000d0306054007442001d421032841d026003448511039903200000e040d041651a000703460038000c0051581304c3d405015500610b400e800f4180c04200701440e01c030160f0007083c003a4200317100380c80c005001c0a01f43d50b001d0100703100e01c05520400c041940024189071801400e82075040d40001416981c03540284a807101800090100d120080c05042c280d1040d03103e614010b902c00150310100c06c80c40e281c6040b0502402c0d188041d6001d00d21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 420524847 1250 420523597 420523603
    0x10e10110d020301080d0809010501060e01050d0204080a210c0206040306020304060b03030d0204170d02030a08090a1a160c02060f1b07090b0111011a01080705090d03050417010212040201031d 84
    0x1810034031241d40081290b6410706e1f003000c00194030065120092046605014008111101a1940c14180180416009a10003080c0c040e80d02504e5608115002e24106080504040740c10100c241c0c40b80c41e0304904e80914038419a810803203213801920591511b842c65880d64000d6000600035180e640e07072080b031030340f89680500c010080d0840507100540c81c3ca003800600400300542280750303034455014514600ba00d6030040151820190103040292580c2d4038203840c03900341031a0641c02050600e620340342451250503d07804900800780c1144008040800c2001900c0c0e6521054001e540220300380700d0155013003450300041446003801c1c1c80c1029903612140d4180d03d480041e8001134080c03501d0700382c515100d50b440180902da050b100d1000380481c03ea590028202103450340d05d00d80c108000d205c00a90220b01803000c0310501c4501034511002c014a40c240140317030313030014000c2c00c4040e080503021440b01c507014000e852140c014015044d165484503401500100170b20b41a4041744144c600c0307141c8000d8028 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 420526097 1250 420524847 420524849
    0x170a1802221103010f05120a1b17030301150809100b0409170301030303050f0403090608060105190206010603050604090305040e180706020303161d12032506060503010e10110d020301 80
    0xc0000b291694180842c20344110328907004240114141290781c80c4422000406031406900008a4000e804004007041c1d203940f941d40001d40d00751013075004030300740560010080d8120342820354101c1c2202d0540f141242d00032000d071400c885550051824080d1322426a005240c1080d00a000141c000c020356192005d00c014041c0400480f80040010801c0c5500360044070b9001c5605103140080c2e00d080d54000d044001d05002e403d04005039000040d000d64000c3c4221007070a034200090790301d19100b16400942e591400d025080009050001242c040d007003a0003942e00d0143c3c15201c0509040c10502d41c00031a882c000c180c070107000501c9200c40380388401401414042d002d140c0c00303142d40e03150041101000c1c0315088124010081404030380c50b40d01050300d8500c000c0050407101c20203090791050450345540954a07840503040d0542c0036003404400b5610420040380c0c441c96050100e16a03960805d801c85103c03d40b000925005215004034039132041d880034041c0c4103852409828542d40c1850f070001c070703002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 420527347 1250 420526097 420526121
    0x191101090f060c17040b0403021906021908100b0c030403020a0b030906010e0103081804090210200a0b06060c031903092a0911090907170a180222 64
    0x1441c0041c2440070758042c1030744511a03400c102c9004d40940031100721080c4002d0014040c4405c0801050406200740320403403001145000204800120b410104000c1d4806442517000e8134030041c6900c28140110710f15486000480281500286403900c40354050340040f603d92054082000080010307542c002d0000050002d20480545138a021002c4914003101a048540c2d42c0c085e01c0300400005806c80b0441340210054109940c0380b40d0301d8404500900807844000307501100d1034041406880d4000b403101801084125a00014090a03103010b49036840035002920310209240050206e04150009144403c00c1004403490308002120007009820700104000000707071035041da6418412141304039016482d141030319260300001400c0103070302c1e80000d1180c0d040c3c5a4440750b400f545140f440080e41ca0003c4082d204041500d058480204103070020b0705011503000b81c003400709002542c50312408040c0c1c003240c20100b8041d001e036002c001c0e0741e0030b04400d4a22506100383c01c1d0140e068440c041c1c0d100e4508 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 420528597 1250 420527347 420527363
    0x90218010b07150902030304051507170901091202060a0c0c0909060615052d0405030708060a0e0d09030b040c03060f0c0e030f0604060203060d1205130509060619110109 74
    0x40360301c0c003c401480d01e40d2002601609085904026075000720440d411100e08481d4142004054652810745015485020b0414402203002004d407802c1c40c0d0060421a07001d9a40f1645183c40d081e007900180141032001c3d41149046c010107410a000f103000002c01402980c0c4001e0503039640c820784058035480402114420b86400c4208154206ca61000c00f490f0100c1c06e00e00e080c02200c5003d419030880d0340404564070202c4200168042900b5000c8401510010f0203442031b05843e070303106981d240420f40d031043d2901d243c0071b00502c9102c80810301110182582e41d0f000c51440c65500c0c1c501c0100340c0503001b60703103910035444e001000070b42d03e208001c5498501c0d0000b00740c000040c1005030502c260007002da80203820030700c0102c8003650085080c80d4010341c002c0006803282c440d10003091a440d140f1000505140c1d0038a01c80b50345540060141c5840c05411169202c601c3c0c0350700612402a1041d01c03444d030809401d00c51250045241c0c1c882400c040303103e1030003051500384110036500b52051000143e9107030b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 420529847 1250 420528597 420528607
    0x60102121b0705090c070b1503161a0301120f05010f1802031519091112060f0c090a0b070201030f0c05040801050f251209060b09060a0303080a090218010b 68
    0x2078041c081880186011134000c1c1d59031500218801c058803c070440140f001d41701200151014019804210090101404030740000305e03180c2c526003920032a4068901c0d072010300382c40040c0841110023103a0603a5000c112511500545564618000000c12800c50b069501c4160b00c2c07a01ea4940d00c0380e007071112070214900c00d03c1580d9006043c10a4400e03a02c0300401032001080003150390302d05001064103d4407036000031300d50281d810b00b0940e0110313170740c40d003544258445841c00c00150300017250b1b4003810709080c01410a859503201c00605200300ca02294110900b00400c201d00c2110201400c0482d0040c1000300d0040308187d0b00e8001c40700164880f0002c00c001007814802c0040c01d201e540d522960900f116103a90078400c040768900000501e0210b99414603810391459980b240c0740c00000400c8810b800e01c100902450140c010705580b000d824051034202001809a1611181e4401242e03015181c000003502d4003102407001c0d06241e0400d9800003541c3c01c880b0b00003c41c071079a182c002c010f101c032039640311 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 420531097 1250 420529847 420529897
    0x91503040212011401050d301206050306040f1a0103080a031104030c031e0b010602060a0c0f0e010815120a1202070305060703050a0e190606060f1706010212 69
    0x808882d441100c0142c1c5810528050451140c070781c9410340340200e803050300d100a01d18100011038080c040c07101520141041210943d2803400c6c20b248009466111451103120000c3c406048075214801c03540c0c154083c002040206d002192030070b008601400300c05899610010001c510036a080c3d00450300484005010103040da807520603420904055100346103480e1071034a4468100c2c482c0c0c017000d0101f021105c015141900d0a9404602403540804079001c0f540e0344004c0130b51180e0003100d81d40c1010741400c064040003885003007610713011030b1540c80340c100c109c0c1803500448041d400180700529056490303580c03c50540c1c4443c8611040b40403072004000c2400549441c107104000c038104a015980001c00c1070001a00110790964488080e01d40003d10b96a001d011201038002e208081c24240909464041c51050415054070310038041c0e001840110f540300f10440c0d40905418080c400280159058407032000341c0d00240d43c00040510441d80180c48040340c00713032283e00c102c2d5802000400d0000c81100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 420532347 1250 420531097 420531109
    0xa050d1812030204030803010e2707030b160210111c02091201051003080d06030606140a0f050d0206181009170c010807111e0d0e0301020405010203120a020915030402 73
    0x74030054a0709505042c9190790b010203a02040c01810b400c0c070f20403c001448600703400c6419013600101000900b0340e401e81c0c50441d4590816010954103004110001118031084e0b800850300300741107038000d0032506101b0350500010711515400004051080100e000201c52000701c0d031016405041005a440c0308000400007980b000e1143d800079a41040c08200c4100b00c6500b02c00b04030381e002000c0075502d807019400c100040c0140d80004081da4500000400c4600b400090300c6550390059401006154662030703100c884090307600c078813580141c604081c0d074010b08140d030260000030440c000500700340d0742130f130001050f9046100d0000006600c0c00410055110201500d001c6000385070058a40c15000d000024405400149220280040740141d0804601e041046c0460038003644030395600d486000034250b8032120324400140024030b111f03104102c42c1c41e06208440403520140c0056290403c0f02500c0103441070300070498801c00703a0900c03c076a290b031124a22249e00c0e61041500e160359107130034810818 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 420533597 1250 420532347 420532373
    0x120c05100e010909060803030f040611040e04060c3009060c0e1305010503070e04111f09060e030706080417030403051b01020a080a0f060b160c050d05060103080a050d18 74
    0x2c01390341405000c20500e2400304c11640c00031101241d103401e55843e424640003400142c2e0600d2188900040d00161b210b09000d189401103214800500910780d0144088a40030301707185124460010001d000d240903000006580c15010034002c010a14103180d813036980881d040d04086101040b003080c1c0078000d07072504107407000d10703523031448000c00903941000003091740c0f80140d0040701085030070600801c05025454490b0000f0007001000702c40554040c05804000b80e11140d11100841c40d080b2010a11fa4054498000013030009001000500e2401c1c1c41290003240103001501c02c0080347c2030384241149003500841c855402919019528820001000aa10034540020800740d01c140311441c1c07a6544014402e410852135500443c1a500841000000300416442280032141c0040e510150544001c880949680242c0601c00c0190b61681885032030004a1002465030b00b0100041c400030f40420b001d024a05041d103802d83c1004034548100341124051005101c04a1071041e107601008000b04180c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 420534847 1250 420533597 420533609
    0x100c06020d15080721030302040302040507022d030f16021e0321090114040f030c031101030c140a0c080c0a050105060307060c0609020d020409080a020d08060a120c05100e0109 77
    0x215503949015403454817040700d108048007105440701e001062500ca80c056030080d580040c010043c0d4244004041d40d2920103441e1460440031806d121a0307a401036034420308080b1107401c05075162044880c1d981f4000d900842c03a071401c4c4c500b0880e205025840b0320010030300071a5032040c03c40c40e949420040510302235030317118035000c501c0001040d10182d0042d070042d5038240100b8200988420f01803a540000b6003e1904040004284828000180041d889200044038021001d5902c0c0c65540710044081d541c0e010b059102091900305400803640c0303100002d14041c4080c0c43c0211040d2929a259406a844160000e9a0350700424004090010a00c605508484114001c104080c9400e0000d4000c950003078001d400716540c0c02040055440b5414110700e04e6500034820416510145080380c40307030700042d120348014800c41c0640e082941c007500b100d074040c1030001c000b1b1030058900503031072a034a082182c0c111101d0920b114000b8054407020b0030b20403000b90b20345800300b161082100041546095501907 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 420536097 1250 420534847 420534853
    0x61407111903211b020105240d020a0806070509010e040b0f12070504090b040b090706080a0e1507020102071b03020105030f0702030903151522020c0a12020c180402030c100c06020d1508 81
    0x105230880286000c0c00b003590082c1c0307414813102d0003400010501c080e01e83c0100894021941001a45a0f00400a2000300026225928480c0c0c2200c103001c12242c00b02681e90308400c0348003120a09282440c21000d180b9602d40071110302c243c944000c10700b82d640b00001100d0640541080c04100304001c80507950000d80c5100910030742d0302d01071004015400c0a441e500407150f50380045000c440c001d2201821582c00003030751110714146004000d0003980300b282c050b60789020702c05440c030040700314110f61011260142e43d000e065840c0e1000100250101600201c15441700708094102c80d102030000c9104914014119001454502030404030001c821801603c6150609600303803034801e02c0281e80078400d1000c0303801600e514614620074508507000704060041d4a00303842002450358000b4007244e22001c1900c1071040104d0300b09903042200703406c0d54001d5058002d82c0b070340e0009042504003040b20440e5458008070071541781d110300d02264002025020310580380c28116001c000050007080c004d00c045001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 420537347 1250 420536097 420536131
    0x4170706030e03090307170f07140907021c030c0c050d0309140c03060c07050a05030403080c070f060f1101060b1204051c09061407061407111903211b020105 69
    0x5c0c4d00c40d01140940d154500002c44600c3c00c0c0b003c00c0158054404050302120782003903c60120203c0301d070702507412a1182c014a00000c824510105130454141080301400c080341011007001e80203403105001c882c0402502c000c0100210310100281d401c214039030f45000031300c511207040a00307501500203441c4100d54007900b407880064600284456114411450b0241c44040c00c0c0b800c0e03403c1c0059070a0281c446d01c808180031003848485401055840c4022040700d20159031561003c030100b001e8880e9071b0120348003030414480b00c1e01403074001d0702d0701080b040000380890b12205075a4041d081040c000756200c1d6030204001c00c1010802c404034101c5d0148000a03914104000020000c80349402550100941907620450361601d2a00390303024a580103005024420300080b000d01c0603941104d00100040c911204c200341e050300807034070702480341e40d1480050440f40c0c00e031020b481d001600b444200c1c92403910400c00b4030000551003490030028042d20028207135170f25544001d0948401610054034502d10102d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 420538597 1250 420537347 420537349
    0x1002031003020906030c0405010608150f0a0b13090606090528150201060302041407030c090810020f1605010b1314152e140c0607031104170706030e0309 67
    0x40e15808903a4111403802480e6110400701e4108003296003055001030410f40003040740b03900310360454450021504c07601000070102d410030105000302c0460720707009075951a090103182103400080110b08a513083c3d4101c115520301d920001c9840c4ca40c8980f0008a411a05000c00d103810a41204a08101a120610794480c0c51495040a81510070402240701d440c1220300301500039044503005640040040108620740240ca54410f0340c11079040c0000703450308c00900c80d170303500408110090f100004020000741c0f41541d0404025880079201c15aa8041404400d00255040c002c100403584a0400891512082420320103040e038400c2d450142a4104203140220405401200c5d600150380445440707031020380c0d400320300602c200805c1521006103c2401c0800c200d080c042169070b51740141d6411040a1107100400254054848039091503081003010907603451080c2c020500c0701c007503040610300d01940c3da07205104c3c0900c210070328059508001d50420843d0742500c01d05c0c60b0381d20130401451403c00064 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 420539847 1250 420538597 420538621
    0x4080903071a04050d02120a062307020a021e1c1707051b1302070507060809031305090c040e0a06050307050406080c150c01060e0a0c0906020a0b190203010b0c100203 73
    0x4000e00b0f000b038126003064021340d6105040c0c2180300e087c40007039900810b241d041210107803140e02c26091112140d40e140c017120602c009580c9200712900d6014008100683e8204038016407403400a10303503000c07410840207156070b07a851140140305c8206001000e604003440c10b285a1441e13101d0f05840410144186008900e000c21050780447c1c3c20490403007480a5040014605003808038412000d80c400b1480c0010010001005021f480503911f0f82c07103030f581e01c001d4a40c0c0d4a00c620760040031030a44441040000d400c20003038498015400d9295581003d80301c00c8a2a07c0880842d4480303911a100c1d0740030842d03401c09002c1d241c0036040c1a1010b1040b00c3c20140380f50703038480f0310202080c080c90041e03d00d60712665120042c0d0b804161008002d003c41079550604120485080e02c08040b1640341c541440322031405055400d0886906401418150005803240c0c1c1c3c0840e4024282042c0010f404030714080742101d84000c5000c0e14982c0800f0303464000c641d0b4030303915011041820080701c920410034490402001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 420541097 1250 420539847 420539849
    0xe010f05090c030c100f0203040e040f02040b041514060405100f090e0106051c0b060d0f050109142805040b0103032316060e16030b0c19080a021204080903071a04 71
    0x350625903000606d42c0d20481c03551141d41d0041108011020510040120a5450406080c021207040c040b01c007100c070400c01103c01210a4050701c0b0524001005031404820700600c4800c1c005007290b0800c1d61f50008a0135903158010304000007100300d2007150480703400c00200006841d00c42078000442d07040c444080c0180c410000040c14107282c010b044001d004143e002000000000b80c005504c60003d41d5032040034019000b8059400350a210002c10b484140d80306181c02c144c034821903001ca03600e884c145000c01286d40c1d00c080c401258800e1000025000e5409000e000394400c655030a942e40c91410300800101c0c2102a114038280d1841d1018021120241aa400b11040180207a071400842c40c11400402043d00640f040b03002d051110300803c0c09806001044074000c0d91a90800c0d0784003050000c0a109140b80f00304000c06a0814905040c41aa000795020070702c003000500c1c02242d0412403c1e064003c82e000c844800d4001142925400c041c404040200b0030000c00d50840005a2014129030140e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 420542347 1250 420541097 420541129
    0xa1203050d0b0409020d050607021e0c09130c1e0b07020108012114010209030d050a090b1803160503011505030a080a140c030a03150302010c0f060e010f05090c030c 72
    0x1e404041d1803d80d107070780c01080229401004001403880301e2a0190b102d000465140016010f5400c02d00380000d515032007208000301100184c07000c134204104001790007002a2040359509050441c510004d044450311201402c0615a0054205190754000e00042443d40001070400414030803680141d8204443e14151001100d1600340030150100015159120181c040c00c0942c090303504107001d43e019030041003100002e90039200da09040400c2550a03101d92111080003514580c81003010246500192505c1000c03aa044d8690306e001e100064980354138107070380044078160540100130619091050300100c4000d1008540c6c0e5500c3c1c880003c1d290041c4035409840014001000d081b124803c00300940c8074039000356020340303071002da4048560b81c1d0800c50b4a080428605114049000004a075070801c03130ba4140c0d135054007181300d5500d05000c080038203022241640c5540020003650828081d900941440b84400609031820b02d2a0601d40b90710347c480c4c1c90080d00405c0722001151a194415820540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 420543597 1250 420542347 420542351
    0x5090a09061806090b0907050901140409020406030b060405061c080c1e0d1227020d02091303030b1816021c050403051501150e040e12090a1203050d 65
    0x2058107010001d071070100c2c84000d68004039406841008096802200800d000c0d6950402c40e42d101040307039a13560030b82e0003156405080c1a00400c103440341040414070080d000303007011a0800e01d59001c0b070190b0303110b0780003220040e0f010f400300041c0781440e220351944820229001e04131242c802c041c1c01c0c0306880d0704202500031000060102c429110820450001140c0421000740e09514560341c0742c1c545007800c0c00c4000007490100180b004542078020705003c20307080440091550888110700d00d595004040c12600001d0600491000d80e640c8045035100e0440300a0003d00440c1c5494020f0880d00342c1000e580c81303000c42c0300c21030b007484c0d015070b03055984021302a0783e05a0b40c68901e80181c0c07601c090f4400c0030342c0b0351003100700c9103140710390081c09082164820760032501b0074410040d08919900003402070310038200c44c8400140103240b248058082018010384002490820803000a0612064102c8000d2000000407410412700304009004024103c1c0c0000303da0050700c50b47c0040c454882c030600301443d55 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 420544847 1250 420543597 420543611
    0x3060f0b040c090b0f0405060301080d08090307020306011203021515010e0d08030a090f1202070e0a1404080307180f1a18010309020604051810080c010e0d050309030a1b0f05090a 78
    0x40e245e003045401400300104503d40300e40e03440d0601d0f550b80300364001c80c1c00058090b901181e03c3c0240081568a130a034018050070240c0e084c0142c041c80e074241a14260f0031880745071001840b028500d07120902680075042d60007520740c6003a00160100c4540d4003000e0040301c1e52074060003c6400001039076000384440c100491300c1d83c480e06241d4405988810044c000c5880600300780c120390740004a100484041081c040301e250348016900e4110b0300e1062010058540c0100020001903400c00110340c0803011f414140c85100101e806034845841a8228204034842150240046070681c0c84500d40503050b0200c19280003022900c5c1c0c4d10060383c6101e2035040c962a0702c400d000710f64882d420343d0040c0a01409980140807061200a03045409403103003540034528600c017080045011610701410407040e1070f200c0303121041d42e0910004120b000d0040e1a980070a02a200d11650140030711501c481c041c040b202400000c40b958610802c00d2640211301082c6581c108204540350308810590104854000240312 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 420546097 1250 420544847 420544867
    0x2030d050a200d0c0c050d0e1203070c0810020c071712120604050f01051c0804030b01030b090708010501050901150903061d010510052b05030403060f0b040c090b 71
    0xa8400e000c03550b940d00400c0c840648980d507400e8003401e4000d198107420301003803070b03c1c00007034842d680f4030b030405051900226100d40d03400d40285480c6003082c2010f040392031000c0c420140d050454016190881e46401d100c00f003004010390411405006852410045140440e0131000c1d40d03075400280b1500061810581c016a41c0d64014040004807084615265664811072001200f03214412102c0c94071540c5000d022908035006c04402605850015180c4412510b5040192204061a0904680018081002100044001600d2070003140300d026543c0150504200f16404d20a054210168603031500b0010481607035103104150464404900b80c0e185080441000c0b0340d00a03242e00090038a40c14022520321074010105041c5120482c000200250b40f12030a50000044851007915802a600c654110b5000c0c1c0480784001007440300020120821282d9036079500316046640107542c0c0c3c5544030104110000a4018014200d1b001c803420410541d1139070004c1c1131146140a200101d41c0042070021034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 420547347 1250 420546097 420546101
    0x1020a0512091c090618030b01050d1b0801050906090114010501050a021c02070501020d1103090103020f1207020a110301150b0c010b040906090203011b0e100903140d180602030d050a 80
    0x1250036881c0f010103007203407085001d00b04200c03502c1081c0000e51043e0300000207016400d0194141c070b41c00940c208469280004009403114000d809a400b41d190034002a280143c0c00c3d9800010000d4000200e813610b05407035014200b48000f0300104070391341003803813034941a00300400d0203055500900f4a152251501d0030120301e070400c44482c1110a013910070701054026000148074040343c409a0854111564014044841c0a80c0314a483c400d68000c2c0018045503001c0e402400101d08440707103242c142034031901c07101c194490031b66225001d038000003456401e00c69040c0c80a0150981038009101c000840014100242ea0310310032484254808100071125481c290000380c1040401441800801039500f407050080440e030700203d01ca0340c40c052801aa000c1031082a2101e42482e03201c0c01c1440c0c1592041c4403019221081c054108001c4036404000105506c05c50b5100d401d082d00200366007a0000000381640c002a1003410006070201d08c200030603940003044928a000040010505864000701c582c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 420548597 1250 420547347 420547363
    0x20f0c010e0109020f0301020c060a020702040902220f020304150506062101050306071806050702010912060902040f0b1c11030d020a0c051c030305100504060f0501090801020a051209 80
    0x842035081c403007004500c0034150440c410140c0200c4251402c4181c1404040c201d20405100860320b07042400003c0c45240950b0141c4ac0300d5001910100e101401540081c0070a0300c00710402110700c019681c1440100c4091040340712107250404211b186051a4031200c100303482c200100718103543c0710800140c45840700d80a4559010840f9000c10300018184040c80194a0074000c042c0a8842c80000411031445003100f401480200c907945d100c01c0d4100042150142c0c40340c0001e905001e11840002503546414000d03518043c0555070004100850b0300c10003094034182031000403000c2c20800e6911259980201410317040425a24640c1c0c0c3c030070706141606e812020039680380d45c580290214401c50a401240a090041c403511207040010f0315441000310300031900e01c285007405821114000080d00940c403c6d500840c0302491100b0450303494002800351195600502c0000200c00020070217540c0200500d405001d400e00254109042440024458029040d1090b504151480403518101d02480444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 420549847 1250 420548597 420548617
    0x308090d050601080a140c0d03080406230103050c0a030201050f0d06031205190c0b01150e0a09020a02010b0105160b070c17040f0b0c060705031b07050a0b06120307020103020f 77
    0x5034040d0f039a104c400e603d0303214104042d50218a0034070410340000022031200d8802000030544d09500e41c02d5203084034054402082140d000b9038a0700c41950b149842e415601003180341458540c3c2c80d604500e48103040c00d07a0810014040d42c130040d01480141c1e0840255048043c403c00b0640e02c460480028601a00e01640040c1684440c0e905035480d280d440783c020704440c40347c0710440400b0390703030704034121041c2041c41e8000c0c04000481c1d005001c4050001640040640e5514004d416900214005810040c0560040318100c0d4001564010640c081c09101940c041c01d0900a00700f00e240d00c00305c01c00a0300703d40e00811040700e0200107440f40340918001c542031600084c2c0984110a0b0b00494400c540c01409102403000e201c1c8070000303800003040112498000751101030300e041d403034145003566642c0010f450b0003100c3e121000c0c1a13075001c00d03c1000d04035090140b8000c010180c007504100740c2d1090b010703021138001d441403a00d21080d100000200c0e80b06980c2840e0059030b030907401060030300c90700841e0006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 420551097 1250 420549847 420549853
    0x2106060420030f0609010812070312020d1e05101a091c110f0607110d02040e0f030409050a060609032004050a1a100905040e0307080a02100509160308090d05 69
    0x80642d5010b40720f40d841c814042910065000d90701c6a442c02d5036074054841d922070b014000c10140c00040c1c402c103403188040740c20f05009030504410040c0d02050729510b1066081c404842034404a81241c10f00903540c000f00c00464860590b1305140640580c00c9441960b4102c0000000c2c40000302e8403110422000c84a4040c000d102d40b41442c50b041429000781b0f400184607200203074001e1541d04d0800d0407500081d91210740c0c4440700501030140700000c0341d0b50300d050360312541c1d4185007007541c8020f00241c44204a2039010719030311410002100100c400c050000700c0007510307080c0f042c8146500508480309503500420688034a001c464460b60341038092007915500541020103000c4810b41c83e400503c016040d0544040010600700d01744121a0030300012140000d0350500b0402c11030500340e020b050419281c0741500d00c3c00c1c0031510f0b5034586078000910349006912040c01c4000404051050a070010f11810103840300d039003180c400c034000020900000c0c000c0040081c8801080c1e842d1510308411582c000f041e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 420552347 1250 420551097 420551101
    0x80702070608101d1f0b0a1b0602030109021314030304050d080405150c010b09040b1311030d080103020a0f030c0e0604091709040c080c070627060506210606042003 72
    0x262104101681d00c0110406174a82d8607064081c1c1c18600f40036500c0c2403d16504124426030304aa2400c1042c5c1d4212042c09407041440120f0024002580a0040c604001d40d450004000508088c602030b0b1004140500d545110940c03540d000c41220b08803401151501c00e041c20303c1c207210b0181d2080754071282c1d1048a1251844c400005500a00b10000c4010005c01041c05441c0c14041c0c540d90442d001010140300b000060502d000c004001001c0900800b40060100001c0e000711b450b00840d480d5800100303120100403c218504603038046e018081d07541d00760041c01d00d15503e441d080606c5000c0e41c1c1c00798400c80b00061407516079600030780106802141c2d000c80078064443d081160343c00980c07101d024602340041d012005006825060044100e007041e20314083d050b8840d02c0040c418210240c201034225040122040a81c0401803e0180603100025443c20680108800803040c0500d1070750760072101e080401c0d446404140558022000c0c1c1d404103581080c010400e40780083e0107250f4a80600c0403007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 420553597 1250 420552347 420552389
    0xf1202031c080f01150207030204020c0111070c080616021902150a0908010c0f091e05060f03190504020108040f02130f2004030507030825050307050d08070207060810 73
    0x14160f805000c20f800da0059507601d0b00440c200c0c1040c038242a4001d42c0c0301505c01c00040c24aa8010800c0c54600c200020790340d450300700c5480c00b9030310813441034800c0038a44c01c0030f01c030074641030141c10b400244000d84100c40c20b04001e00a525034545290608580600254010554a851280191650001c52090358605140e8009452001140078150301e0f0341ca4a640d2262090040000c251003e245807103c80040d40790000a07480049204044103c1040d04d642c006079585442000d8800d1030f041200c07003910703864405c01a80b100341c0c2550b001c02d80182080c1c140b0000d030760094003450708103030455030b040740c1d052f02c500200d421381d20070581501c08180b0340341c0c2601c1e94104542c054014654000d0307402241c6074841403880070b1380c0100d0101920a8010900810004a0034801404200303c80314040e0079807854150501c11511941c10140e69035080041e034942088021f00031010200c109040036140d074100700d07200030b44e503038014003440d000c0c03100302c001003440544503604450042280003d1500d00044181c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 420554847 1250 420553597 420553607
    0x14011803110f0604080607030e1f1e15060806090103031706150d06170c031c020c060409092609010509030c03160303081311010305040809100302031503070f1202031c 73
    0x5480c80300103442c1011042d0f071049c0101b4910344e00d0034081240340b18400501c0490006020740303a03c80c0d01c1c0300c403807000d15075442ca6540144000216108212121540340810182181f00010195486540020018400680c028401c10b103110060b0019803210f6464070040350500c0c1041c050003115070000b00360103c0384500ea800100580f0310104601c036800c0ea06a00300c50396144081c2c030155168009200317401c80300442c0f165a0900d40541e104542c1200c480d01c000ca0215801030304029695915640100c00348450103240850024060603000c02003007138841d05880c070b4018504060704005e80040e070500260b03020010038680810080940b4500048075241d80c401690f42e01c41103010a03080d50025050203a0010b4010240340c11505141d00781072900d0044009000080084441960a0020101584481001c92102500307070f1001079403420040912042241c0c4052040d12903400201c2c1400000d103071101c51011559004a5440c40c0600c920009040a00600403c4940140440c00b01000c40d440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 420556097 1250 420554847 420554851
    0x705011508010e07032102070f060c0b0106081302060c070911091005070b060118090507020d14180d03050c12030f06011b0f061d0714011803110f06040806 68
    0x848001c0080700c40d0740340d03c40e407919014440075058119141c1103070642c0d0f00c07009881107244074600c140c661181d19510400c280c51400c0c1c01440018529905000800c29107082042c054030680c241100a0315011409030b4525000140c001c0c0078410120f078101d00d801080240c403000d001000005e104249041220440c07a400200103144502c0c000c2000d8211503000d4011982078542000400c04240c0d126001524540221952801080500900000c51150a2041034090041980a0b06a682600b00024920140b070f00040428040810a010303682c0c4000002c040480d00544030700c049030030350741002d81d00da000340816900c0602aa031074900340c23007042d4001144500200c1c41c003154a07407607880044848030680a131100e85807080302131003004551049680006e2600c24803012942c241914510344005103081600c0c18240d01c0b0440074000785041c00140a0000c04c01e103020307007016402c100400080241c501c000b810b51164658480e035281c035004400700c1c9400000e048141d45d40c0d1394038813503540c0d0301e41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 420557347 1250 420556097 420556109
    0x2704050709050105071b0504110a140901120e07081c08010909080301090914030409060e060405070219140601060801090f050f070e0103090506070206090d0e011e030207050115 77
    0x24110014030224068001c40381980c078180c2da4a4185800343d516050241400c04585980343c09081c170000c0e0382e07aa240181c1c5201c2c1002d156a40d00d980c054a000340415444401125184505012000150764030642e0510405049000800c0101c0c2d0b00b1545810801c061704240f029004420030040c1e101c0d0408843d2031400211703076070a03103681c0e81c0c3c111403401c0740c0d40f04070b0003032008800f00010001c0130601d0700304205c030342d000d9641448130200301c106061442c0e01941c032039403400342c541d0010080d803e0b55001d0154403001c1a038080c8000d1400c100c0080d04c4585842c1c80324408030b203c4140313030188550709000060301d5402c101100c85951711110301070140800ad1003407031841d6007842c002612038085402041d024002410350003905846103142902e0280c0c401514070b0400d9603460011010880802c0000d000340800d4000d800c880c180600003030f0510503251200d005200081061205d240d902901041000c1c07240002034641400187d0214080d20490102601035030900701e52144005800f81c90104450b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 420558597 1250 420557347 420557351
    0x1406250c18020a050f180901080c04060b0c03070b07050c030a1218030e012610090c09080c0907050d05090601090f180b060307050618040c08010311040c02032704 71
    0xc90721641038140e01c1614030880020300d0601c0480c00030700d400ca019240401c0b8900c070440010303001401244964909034803010059010404001c182d003454800c6102401c1904885480c0c010704080396aa41e11891134003c1c48502840002110301e88110141c5403038503071030004c0c0c90340d41010007030060001103d07038002103800f80391002040601c0300051404581329411340341d54034809449001540d01012113030821100007104550f031386145804e962468840c1c4100460108414285400c150850f208801080140300c40e0301c005100400c00050100d07a165022580c0991607580c21900711468011081d8440714103041a040c000170440120f442c9050782d4841008126100380151100d0558110030786c42d45075014014030500118600d541104e42c005000341c00ca640403681c0e2400300d105580040d19194000c5207850341c8130031601e000d026030300c1264203034035020b10706504603107488890303004042405126a41d03401078000c0c0203000703005403141007007038034450381001c00340301c502020040e0010070f4030748958 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 420559847 1250 420558597 420558629
    0x34020102150106121113030501020418110d09050a0804171204140f0d0503070c0e0c0f0a030c030e0f0a03030608030f0403031209060507050706151406250c 68
    0x8100031007103040359031580e00e0a01030b046528022000740140507007044072041c10060070444010141c1d500300194803c4000581c0d8601d0813000c00403070102440448040303070518241e280b00300c518005603003141311f03141c0c40028901030301e04e030191034440e840740000e100d164041000140091b4600710080b404034000e0a4070303544d8050f103a500416200b14082c11030f6880c3c10000903c1d0724107201c0b4055601c000c019020601c03a80594942780e1468000e00d0301211000c0703030f60000f44822461221a2a01300110039181c43c1420a0032001d240e50340142081941090383e40c0080d11551846a04031400700c8070501c09803a20b044000d20240e131a00d40040065011038100030b0b00184403d000000c80d195100c804400d1424141540e030104d80d4904170041d140002621b03014440046006481450300503400343d252165030b0050780c80c21034117903803205425071001a05440c040040850260710555584d5080b21019074407070503150441c0803002403203690b09803162001900410000b99a407100f00352401c16030100300720 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 420561097 1250 420559847 420559873
    0x1425080309100e061602030c060103060c1103070b0703021c090b01051509091b040f0b09010905030118170403060513020a0e070915030b03250f05060301050634020102 73
    0x907078403039110750f01c955202100048404444074200c0d00c1035034891050b6454100000042442c1c004281c00c02d8903196940c81c00c0d409442c0d000b04103000c80c40f0f008005503040c8003a030b446140c54560002d000f0010b0540008104000a4010311040b00c1400301000402054600c0e007040c88155000b4040c00380141c2503200c46a07140d110820507103a2880703009040810076515071800395082803035104a4010389005000115032040800e0100000d00b6610580c0c1d0b485076040c0000600154140d17004c0c50103a4503000c4111424200d9a20350780429401660b07041d070351403140801c10001c0c81564809400907161500340080340c110316080401c071500032109000d959844000c9490380500940c1d481c1d0100340101000c10000050709400680c0c0309107410009040c0041501181c248a00001c0703050b46a00410802c4505441c40c580301070251403240440d10b034007424400450124881030140901c11038003c80d501c140203402c08101d1501c4c4038082044284080c0d251203080100c40c25900890150003411480000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 420562347 1250 420561097 420561101
    0x608160f0620030c101107050c120c060a030c1e050a0c02120a06050f1b04030b060a0f060507020301060602070f090911150d06051c110103110c0f0114010501142508030910 75
    0xf8682041c09421468040010415400d446400f590064069070bc28603003140c1c1e90001811158040b41c60120340060319a400401a007000b88807045044400b0011241959100003a2090114542480e410141043c00020690185a50a04642d100d00b011460400c02641c01181c0507100b500c05181150310303411301e003e9540c10041c250441440082c841000841c0d103020b50b0541040000d002c0390b00da40e88030740310080781e100542c200c00c1c0030074400103406003103003000d114a03401000e113071029101c178906041780303c8101c001601c11169000c0d2111056001c0c08800402442c0110009207030042d99403024600c1900c64200c60000d002c3d0b40d2a000e4002500d09000c8564000034440501d0001030070041e603034810b8684a80001c2604066980c40142c41c40401280249410100c0310010041e0001c04070101e42521a40c58214151062210040107540d80002c83d05005040500f071803502c81c0d66407161b41e80c03210383c001e11508020004000400c18003900d840254081c006142c1900d2000d401d0510840c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 420563597 1250 420562347 420562357
    0x8190e070e0a02390111120609010e13032604021002071a0309030903070308030603010605030c03060403050a1103040f03061a0d080a021f0608160f0620030c1011 71
    0x241a00114070016650344c000c150254140c000f10015083c111481d0f440c1d02d0071100303000340740e05042100080b050f05040c081010315910010885003000c0c00d40c108030000e01e02030005807001c01c42513042c0a0310000c140c010a030384041030341030740d0005a42402242d150b801e010070942c0c00341d0080200001c00c01c5041d10104082095550001c491040c1d85d11807001d199107680010200c06c0d4900003404a2086581d013070200740011401005860b403241010010182118911342c03140c4d100341d024000550b11601c012030340541c8140c042c2840ca44509141c002912000c0c0d0081000d00c0314000080c001c61402c141d151110280c901540f03080020303a24640a1201c3c400300e0036055075110100fa90305500144d40d280042c45030f8101441034910000e00b100140b0b02920f0076020241c0040d4480409102c02d01082000006402194098265013854601121740f80c402c14041d6004014071484c0d2034004101c10340551014800c1c0000f00ea59402c0e9592000340c4500c40015015069814960740d00203401d5498142d807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 420564847 1250 420563597 420563617
    0xc1c17040818010c1a010306060902040303120b0f0a0b0403030201050c030f15040609060f170109170307090e0c03070e0301110412020a0918060b0d0804030308190e070e0a02 76
    0x14903214040d140d81030002d01900c192030400c0f40f01c0d900a00000d004283c004080d07030002484000c554114a80081503403415000304040324418082000426842420807541800c2848009507400302d060109548a981506c025003018407101e00056000f03480d4010022640254001c006a440300036650000d0701c010340755110030480c580082588680240003a00001d9002000028000e42c0d81c4103000564120340c1c403a694544446030100007004103850b40c4084040281c001300203a02403541d40c5220980080c00f1041014008030000b000704d07002d913180c0350241540d8521702007070f0b281408220f07800340d204443c0600003d0ba448189000740c11b0501512206040e10b40007982804c0c2081402c8001032030074141a039012171101000034015890f481407403009560140f0312040c1c5070345414440261203066505c0d5000c3e82c94070482002041c00401520140ca03030525103480c80381c503a841c250f0485020060404203881c5802e04465034040000703524000c90700d604450b000e142c0c1c1c0380c1c9801c05c12030141030600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 420566097 1250 420564847 420564863
    0x10090e0102070c030219150c0519170d020405150c0d111c200f060f040308060d020619050405100507171e0f090a0b0c0a060209060c1c1704 61
    0x500c01841c4c8200240c80c0c4641da010000f10781b5a4940d01c10742e0018403002190045240c6425200a10205001641300075400304040381c00480fa0783c1d5814112141d90010312045c402c0826003030700040c8150101c03002080c000341450190a0070702140049980305004901d01ca00c20f10a110003814052034003c400690150090310402808850346d050f0798088004080030024034007240321103241210f02c8000366108060050031440d0703442d04c1d440e203064409801140c07464075540405c00000e41c8128601e0f48028151200d00e0100c26901c0882c00c0380c002c902410b6a01d010f50341104030081d0784040603104032142141c40f100455410b500a035150310500c2d10140c4008042404070f180d440c8008020800310301c0000c05600c8043e03103400c0c60380950300030500c440c0e01000c00040104292408a2224001d0413100761150320301007503807a290303589490151009003015000308840050341da41c0c1e003c1d0350000010606039110201440300314064184030295601c08602480c0c48200b0024081c442e16110b90350202d48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 420567347 1250 420566097 420566099
    0x31a1f030e030c0f0705090c033306030a0e0705040605060304060209010c1202010509100e030a1d060c0c030106060c0803070c0f321c1d040510090e0102070c 69
    0x21030250000c00400c02507480104120b0908510030000f007400c0c0c20744640a80b0b482070400303040100610780a00105c03103800081c4144442e071044c3d0008156600c0c0410281e032150030280314030141903ea0421003d5001a0100c20880b010070a0782241d41070030f15080907101010f45900030402200c400c0c0c0141c176003181080c0700040003e01594004c082c0310505042412094900d40c0d0350000c888038a0400d200140d44a206020080408010300100510598424030040e035a424031705071f89014407501c0b40304005008421000484000d46d62080c84000135004558900c0914041c540d0707500207035070050007036291020010f4624824001d07101d00e0b5522041c05442c6031a003040444181c009440140c2d0f900c1202c6074000000764030f0180906040d44205c4069082c0d080c0c8400c1410701c06284208208190090b405002144005141c1091060030030b0800030f0301904c0e4604041400e13106070240a81061030310b0280300b07070f03100580148012624103081c2030143c20301c078100030703401e03401042e1001b0300880ca00c0384 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 420568597 1250 420567347 420567409
    0x301180207080d0e0d020136030908030d0c020f01051302060a020c031903081302150d1503080c1915050c1908010f05030604110d02130903031a 63
    0x200320442c0207508440c140020740d03080d401111009400d6428a0740040015410150203018642ca0088038101c80108000003000f030b074450b1001c5100d400c600e404c2c1e020710345d01018004c040c2d003800b6100b400100e0f51901c0c03240d07000302c00520034103902d440540305103110702a0103601401558030034800341d0098070840c00960f0074403885400108000c8150701401034080c206403820802e10150419846070612909154240941901006400c041807105598000d02c090384032030010503560344214a00381e40d00c10380c0307441a400403d01e24000400c11486000000306120010001e04103401c0d01c1000d5684010710a001d84400c05103040001380420411071810880e182d096002c1c030340c03042403c2e40c0e841c43e0480c0212010116203102c40480701145040b001404282c1c0c14008010242c8001e60080c10b441c00c0607240c031019130050400c1580f00702c0c0c0c200c1445046482d46040740580c01802001401404203928001e4044c0c142500c001d105102000d802400c0c40c81c1418001011500f0710f6000303034100ca1005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 420569847 1250 420568597 420568601
    0x101a030c0415091d040c0504050603060403110118060207050606120d05090d0b130302010501061b0618020a030308010e0601050a08270a08030a05090f15100f2306030118 74
    0x7004200603c4802e000000f2010642041c29a010800d00c2c156603043c0b6051802028010164200304d0040c0d10b01400c0245603100010f0040c2c00c5501410075240010341c4000702805400220800d280d42c0c0f030940c21130420456960040c041040c0701b8030680300c4c142e4800040c440304110038011954a40e001e400006119402580108004000600000080d0041e82c6403013641c4070059500c0c0da460f425840c001340c203140d420300c152801340c0901d1174040c00036007100b508603038003180f41d078805400580d9a03030314104400c1105a040171003030b50240203108520790300e040151414a091141d14a0b030200d260018400c3d600c40d8044a060600c1d0b17480e94030303071030305c0740014030500ca130604511205059041c1c2d1038510301c14007004602045031107800c802e0381e80d14096944005496025014a416910189442e60a0003012a07000c01c24840c0c1101a60241d450500c80030b0505030320b03403029081610607400440c2c404d1542d50711100d030f4035607801118201c1410b1030a00009200921604034031400d80010360031500c5582d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 420571097 1250 420569847 420569879
    0x213051005040b0711092e050d02041805060f091c050f0d200d060b1213060908030423060c0409020f0705010e061b030105030c1201020c0105101a030c04 67
    0x2803041d5052002100020071424801a030784003229407404550314801008287c411901d101c0e5149000c64101c1c580000b044072241d0040c1c0c000e01c52600c45c2010031082d40214080c01c403054114085484a080030081031503442c0d000d45101c02c4c14042c054580311080b280455548080c03059075156440d000d01c14858403030903086401120007442d1100c00e44a80681c2400d4241003160140d040f040d0b6502c030316090700d0102c4810b54031102010b0f406200081d03502d0040d44800343e00c030039689240c0c00004c1840c40c2c80750043c42a11001402c508003c800d020602c04901c0b251019244100c14403201c1100394109580c0d95034007164220381c00712003084240154082070b0080d04100c3c4021500604041003907656034207543d111480e603180c0d680040c003000100d400d0f500002c0c11003d4010039061440d410400442e86800030302e0549800703210301c07821043d0341084c2541211f41807a8841c00801c82420709a81c21100c207080c52080426490220851202ea00e11090880740100c104500c4a0314203450324841f08004800c0e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 420572347 1250 420571097 420571103
    0x30209071b030f030b03120a270501030b1504031505281a1302030703060501050a08150d15091403130e040c0e0c130f261c030213051005040b07 63
    0x441d08105c8194800f002104150b400320030b03034a41c5900030300b00010a00b90a03040d00720140ba10701000919031181c0007505100b40c030428a008244000070001140d643c500e45e640800310000d00040010038444185595002000c80c400180050f8039031071312840104468052400607000c81c0090040d54010f19808244800c1030b102c183c52016886a0018510303a000091400c02942c0020800c04540d50500c0b072800602409d080190600d070040c90024912000100758406025045011038090f076521081036021992200d030502c14012082085d00c0640034a000840b2420500b8400307154200340030081d64800c48281061000c4280b800b60842d5882501400580c4d0303200c1d078444c011414904009296101d0b0009441e05030792a110021004585600c0740c0c015402d12261110901c040303841c10584501200b100c1d5104030102011103415030601c107103481c840c1000030500c1081070b00c85405401400041d81480109891240c0e00d03010b1181c0c0109060300784c0001401040144203140da520040e00030140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 420573597 1250 420572347 420572351
    0x30f030507082a07080904050f1306020a02010f06060507110f030a111203070c080607090311210303100e01150f2006011214120301140f0406030c030209071b030f03 72
    0x1422004040316540884c40030f4622000020b0b0102440c20030f40211b6030840030b0b290000000d0b241c525100401c0e8409900010300c015000103905000d50300c00d410102258607030000030880955100340150240c1c1c06550100d40c40880c90300a15814501070f04ca00d003482501a000d403111108036a61103100d4001d41030060f82c040719484a400101038200003820950344261768103440c032410180000e1808100403c480100610302c4002c0c000070703c04410f116503e04095544048565800c84c0050120110040000c490701c008010841c0581c1004440350440380f00020017005640c0b1810190140d07003048481501103421400081001e61040b0b80d41210307041da102e40c030000c04a135005002d0815000b07a12180041c0c0a00540d8030501c00c16014480c43c01c10200010168002402c110803114003051140c44c103042d540340201790f45911000c0030107a200318014003c100c407645038900a0341d480120300059002d0205500000d540d14052214182050300c1c01d40440542502954111106044440500c003091307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 420574847 1250 420573597 420573661
    0x222020d0f0506030616050702010e0f040c030b040b060c07060c03050d11190309020a060503070903080d0504030f020a0b06091008030a110c03210d0e060106050403030f03050708 78
    0x145110703401c5607040700710000c181d80c10700c00d04044c0b801c50060040f402d54401c0310080f588150f00002122101c1343d0a090000c1c6242c00305001920800082540940180c10710203d010501e51550100089107030031101000300034030400500089008070094085d20b64005041070001a000b5403800030070610070720340f03a40341500460381d810540342601d00d0100441c9000c074554525011018800018001501e0200700300d83c13150b00020801050f610880b400c1c01000030100d25528803c00300b40c005103800c143d10554417262450300200404d02107400b80c0000301c021014200191020a81e2014190007809403012504d480c2e00704902544094a002d03a00e18020348001130000007070000c0c1c512214191921442d5011030a507071420440003012091183e0071045100b40010344e419000d03500e440211009075169000024000000c103034041d034866440c80b030000002003d9a01600900640e4400d41e51190b400e42002c0080c0c095810079035080b8082121900007403c032514180311054200144c0617a22200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 420576097 1250 420574847 420574867
    0x10b0f090d060605090c09030c01080405031b0a05060601020313180b04060602012009100c02030703020a08031b1207140c0901120b060f063c0d0b0d022202 68
    0x1c0103014201c4040d6143c02040102d1710305505400d500081c1c80320b00c28a00004040000e88468008011605102c0c1c07050128042c440d0410903a200400c3c4000c0c2d4084038101540c500d5504d901002c02220148200e01c0050745552021050ba40d281c000652030a184605085c2e00207500712442440003211582c840903440b440d84e65015120050415400006040c17900021031980c2140c3c02e86409141d480c1001b030005c850311991b12407405452280340c820180c1e040da10000e0f061605540c0040c2d40000300f440c0200719900c0100080c0055540c2a64014800741400c0e1078544511140d4407802c00220b041c04030303001241e00312001d10788058409043d59140c1b5044000208008400e80042051410140d501e00400c2744030b80c2c0729500064102c0b083c000c11803a01c0d00141882c030175510044440e0007510f6041e0f0440a05400032000000030400200038801c28901d50601078000002c49007031903090080c05402402c021611030791181d0050070219041030741002800054145d100e400b11029820016542c007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 420577347 1250 420576097 420576109
    0xb270702030c011407120903050921010f0b0108090105040b0c070501020c0d0801090b010804050709091415040614090601090c170108010608060c0f0d0c0c051615050a08010b0f09 78
    0x1030403400e0084c0b403e5040c02e0364010160607090000040891424400c4008207400c1007e9a105a100300c0311075506500c007820201080385040c042d00480d600740b8541e032180304030303030780001641e44800c1e60790404990718220168241ea40a42d00039140954000100d44815002c80040200310b0103100054a0f01d001d00d100c9034a403c50f21800200020641001801059580c3c000c0c120181000d10b4004401c2c10541c0ba805c1e110505c0c2e2040110065460440d64204000d01010400d102d01140550301c4080c1d01c80b016600d10002202c084a140e407900c0342034540703110708078005401100107400a16007a800d266460b401011400000390030300c520040841a40405a82d1540c0a00000400821424030b0020020b191207000340468003000f005100d494a04078900c0e065403184070824034040b401c1c072103540d4180c0711629050b401500d94080c1d1014210f01c20000c100003000c41722940c45d10f400e01809903000f201c060180d00300e00000a070f418001009041d00c00c03005056020311542c003891a00040e000020381d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 420578597 1250 420577347 420577361
    0x41707030c0201090506210717042418061515110d030506010516020a0b21010e0c0a0e03010b122505060f07110405090a02040b270702030c01 62
    0x1580032207884085503440a080001042e003618294242200d00a441f241c06031001138801ca500c0d0b0000000d0b1b08103118120050005803042940301607030070309007000384d14031703000030340034101c500c400c00825061290901c15940744010300c0400d24a10065990307440040c0511410201101c3e5110502160030500021880e42035800d94481940c0005042d078024107001d140442c000500d49007208110301a43c00a0840b04400b04000c2e52040b610721320f1000030100002a0030013506c4401c049448000781404402c0048802142c40150401da030380d5403240703a000720007200e41010000084c0849500d0364007e1910139040d090042c00856160355400200d46820f0050082d42c00079444400100c9810303140403141d1000d050010200c42c4207900b880701041d403500c100404142101c0d40041c2000500900c4501c440500c00002c00038000e606000c071006550700d40061003a80301c1c07450031203001c0c442d250061480103038540c42218a00242d030504480781d00b51800030141000d500040002482e4100e082c49041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 420579847 1250 420578597 420578603
    0x40501050301091802120d1413030221120304020f03011b0c051002161a07090510050c0604080406030f020301030c05041107140d0801050d170a0903020a0e04030201140c12041707 78
    0x71544007100005000310340e40701da048048c05c810802991058040e600c17181c10340350103995010b20300240010144103201d800d030300106107002c0c00390701002070071109004600441c000c0380d040308103c400030101801c9039141000d54181014410303000c80424000c0e64808140b502403002e48a208000400710026030f4030028001c01c0492150f00032504018000b141d50b51080503600c140c050500c4e02e9440a000c0354814085e480c40380302110b034040b44061080701121100c01b16501920712505140c5010b83d15a0000d00607180402d0601019151007802d920980f41200d4122100d6448070707141c401840010400079045c4c10000d102000303a20003090801401044030075005000348148070242c0c400800074801a0025440765204520300b80c01b20b01070080550b03003004a803880658a4810920a0300d000c0181e501c003e4200c400c20b00001401004200180e128034043e400a100250108001c0400090300311001140120705000021203041020607465200d880740e0201d90202c140200401880e030400c1d4011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 420581097 1250 420579847 420579853
    0x10e15130209041b0909090c082508011415150720041109040f06051824010f140715020a1d0d0605060a03020603010b12010b04050105030109180212 65
    0x10b00300c0d6041610819012604400f414984040c0081380100740c0380e001d1160920980e16090940144040b180545009010003002ca40d861801004802034034a4016004a03c03407860040000d140036040c010002e6010210001007004d0b611000e1040a0540040d0401d400c810020b4688a030496008010300e442c3c1e000340c0c0800710403140d55500c000c022500c40603580c000c03070134030100c0721030404107006940200104481c0810131560343c071120001001c4031350120340d001a100824050720741da4400c1c0d99008a00d640007810480071740212041d02c01c440b403c16180043c4540c03200f462006d20509002e0700d1841c240c8203080c41c0c00030589580021840c24500d000200364000360b51213486801000707152204a41401d00c0c400c800d501c0d000558030691405010b00a2900c5030000303921642e607600e04070041c56005103902d803203584492144092340c01112800140301d08840020070f50003000d109940844105948440c6140e007427031109006014000f00c1010b41c42c00e521400700059507140d0840c1507081c13000b001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 420582347 1250 420581097 420581107
    0xb06010e0a080d050f2217010b1503280902030f123007030c08060306012d0b0f071a0123010c02030d02010c0207060c020a0302010c0201020a050d0c0b011d010e151302 73
    0x3c01840e4410414607000c223038940752660708540ca55240e903040740105920485c0e00d9580d0700e08010440d291080502024900c140030b1143c603681540c0c05041518025411900354145140b01182da442d100076102002d400c00740481e00700c80c01440d2a040803800758400e0900a003d072000340d807840d1302054039043c010a4403011030740c186591180390301c2e07480b0300c045008007203031f51401040c280345079080c20035120340c080441c91404109070542500710042000014281d5030781e040d840b0000d4107400c0004111110401602c103500b04901c07201529058a43d0090440581e15409400200d8140c04803c21814000c1c548006000f580d814003000c00440200e4001080d40f154001000781480d4064000354203003c1310381e9441d0090703180c014800e010b0782e03820308016400010900040c0c2c60441c0522000348180314960824820030351180401c1c07507143c0720f50401882c998850984641d42040c1c86410803248103140010003034048181031141d0802d5210800b42c07400d9900c01d0209a410207030380c01c401f5100d500010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 420583597 1250 420582347 420582359
    0x2030c0115180c090b0903250f08060919020d050a0309030b06010306030c05060a090e0a06060212120a1e06080102030108060108010b060d02030c090a030b06010e0a080d050f22 77
    0xc012101112000d00c104000f080e0414081e181c24410300070040e050901041c00c0340c07503490800241c0c01121002c0c0c41110803c0c48400490300d940314a024520301d008041c0c8000030b120704001049809000c480016195204180e41c2284c03070a02c0c420010790b8000001030b02d602c049a024008802c241c0e000c0e554050703102d811410080311014014052904051800100b00301051404c00d829003a0742d02210400c1e6100d00001d0300f150414500c1e0000000103a80c00c003800741ca401143c5c01041210b90765020b0b9000354900c0c0901c03400a000d82c94000035000040310000d407408078164441031010b164102d50520100f80c29030150112505500004c443d0382d400001440491401c02c192401409a00028480c1141c804080741c550700503412a0380c0340d90f40100118100c1240341055410f03240010b4480007420340d49052407029020181e401c0c60108021440101150809806003010b5030101c1004040c1c1902407074040b80c0581c040302583d040003109100c8240c500080b03142c02c000a5004020000000e82081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 420584847 1250 420583597 420583619
    0x618030818030412080f040f0305070504050601080a092d021203280e060d0f0f090c05010e030a140105040c06050a0206152110150513090302030c0115 66
    0x7800444150064848181c0350490010441c0c2c181c4420340001e06850005250000250203003415000445001160100d20f0b41c50302c0f9011822a40580708a484650f5038602f48000c0710b10503504540000d11520024016050580102c135020b4070800304070a0041c5208942c0081c46031003200b4004040d4144511015440e10101d881d07004070080c0095460b184204124400e0b00b140c0551784200115a0078006035058083ca4801c80101030203010581d8406240c18110000c108481d084260b192420340c1c8800c00c26010700c554041c59038401d05400c0c8440c1403100559550002078005641032007120504400281c00d02d00001009900d100003203403034201440c1c6128907200d04d17004101004070030300441c3c3d412540001c0c8943c0205c0c8113400e0364015008400420b85c0c0c034041d111454884500c0c2e6548001c0c4e00e0000525a00a0540c0c180400512922a500703400d9800ea900c5150740c40b04d072481c1095100a2a81d000b4504a8841d00450303260015001000d4251254503262021400040c0001c1000c0b030100c5c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 420586097 1250 420584847 420584851
    0x314010b090c091009080604060204240e040f060b0d05010305010b031b09060a080607022d0304030b06040207052e090b1801060f080705041112040807060906180308 72
    0x88800807901c0c80e00c0c04120b00c0034040c6010b070a20642c204480e1090244c042d54596010b803a550040c2c0381d5501c0c2504003000a9070041c070a03900c4a40d0b480c060094005100a0000e200500301d94a030a00c19000ea000c000203032680d648001d000d41d039141c40025202898a004141609641a002c115989981040c90858444a200c1406500320301c10f200c0c01801050342e403488013841114404c2154aa000108074036000541008610f88100410b01c0840c903000078168441c110089400e25610f1813030340300c122544114050908103580240310030300000d1500d196690f40301001400040c14014540c03a09440d22506410300c903d100c00e81c01316003010190704414444040c0c03844506104880242e030b5041d82980c4014110300c0820152000d091140c04d00303400281c010041210ba45030141d48030160702e500c42060b4400c20b441645445410044c0c1184042998444464070080120319900c5d51202590395010300c60489080d80e85040c4030002489910800000c146c04504004202600c0d03e030160404c500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 420587347 1250 420586097 420586099
    0x41106071b0801090c030b1506031320030a0b0a2c070e0f040602030901090204290306010b1c020d06030303020406030b031b130213060503100b130303050903160314010b 74
    0x108800c050108103100700c0380041b0703039001e117a4070401c2d5100e280a8044861001841da4046000014040c1e6000307001a101402d07800f40041c8000c0b03420711480e082c014800c4241250301904142070302c1c0c01140000740d800354007600b404008916103070070319015174005591050050107e000802d5020903803500f041804081c000c5040e41e50614185034100c0400c064004100074010380d00080000d4041c0803c1d00619045540503206115020150b284400311500e0309403602c4461325502060740d028035000134618102c030140b003e158641401c101420340081544a600018280c0030040740ca40c520308c2d0b102d140300031400380e54016200c0307003490030040549102e0f0400d06c1c401e500414918403c4e00c178004998600802c200d030122013480ca1005070310302a005002480042d9003c0322800036005400038000c501c28000107034441c1308151a4200e00c141ca014003002c4d01c5850048020500c0020b000d9801800711031001400c039082c95500040f0204001503541040358052039194181c031181900f40a44004c1c108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 420588597 1250 420587347 420587351
    0x30906090303060604050f130e0d0f080c041202010c05030a080a1a09010e10050d05071e0e06100917100b0f090606090406081212010504090f0308041106071b0801 71
    0x7085400131304c1c580140e00640740b04000350803900c1000c1da00e42c03d183d040a0700b081d4082c409000c100000f252200300c40403008000c01c1b01442207049051140020034441e039118000c60f41003608200e09621541641c0600300d061003550200200031031800c1010f482c0f284007941d43e0000514000c105203081d40ca960321850240440803a08405036550200668151012000c0c801a0340d80c0d8100c24100c0c0c284168882070300030645440000500101050b00c00c290b6101c1c200c11160310080c03c01d0108911602e02c107030260030008801103815444c0401504491008916081e81901d817070700030401541c61a4005c11099500910800082c80b140c1d00400081e054210381c480c0564000c00041021000014030042c491500081c075444640c0c1c581d03112001411144045401400c00e40c3e500310f14640c440506a01e40800d0304000040c01e2070b00340110418540e0001d50703001080d10381d503000d941007100580304481e42844007450f0f1080d6164000039066260103040d1110303600700d02c1d09030b401c0030999a40011030b00d64 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 420589847 1250 420588597 420588601
    0x100506161401020f070b1e090d0815040528020c0705040e33010b090a0b0c0715210507020c060d02040503010c0c061b081311090903030906090303 64
    0x920040001894150001c4010344500d2486000c030b8024071451200c071503040c10100c1d0090600030f0f0044100d102d914521004d0204013202e408000050000b2240d5100903400070704200b1300c50303201e810090f070848044800107044041d1000050242c500c22148042c4040b010308a1541c56100840008400e04040d14118a407100403141c50b611220346014290049860384010300c1c20440c10080d6044012903c68000740b250301510034400c00d0580c0220200c500140c0c0000031810004079011252240b100403d1004820304d04440c140603a001402a2001c0e030040c0000069000030080840400c88070541c2c030304404a1181d9149041541c11003442d00712180317007508109101d80c00060200c4208812512070b40c44001c2c66a0b0316010b4429900025019400c2030040803401d0341040080132218401c1c02c05000c070003002101c070f00340c0d85202294880000d82c1d0002250713808617500200b00c0301e01d004164803007500c0c00c0e460110f050340100f0f44400c0c405602c00401c0117243c2005008075500020f600002d14598 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 420591097 1250 420589847 420589867
    0x91311270103050c160c08060f01080706050405030a03030504030c1407170705100806030a0c140406080102070302060411030f060c07060e0a080909070e1e09060604210501090f0506100506 82
    0x40c010140c0010b4a0344140c0a017000b4000084140e2008100d820220303801481d1000b800c0307207041800e200e074288500c65001c0119000b8040c0d0261425200090700070000c000c0b003030328202c0107003801501c194103014085d968000800d40c20001d10842001c000001e0800900d80000510303070307191203100082241c105083c01d0119940e5400140c440749941d10300042c45860f0440068101101c05600030b0032203038003507000210172406c0c81d113100300035404503410001c05e40d542041d58281c1c03080c88801030058201c00d0004000403030003040044003104c054201caa04552b20002180303440c4003550711205002c004030b404402c000d014003812440418000c06803004a61030350380e00c4068000d040069202d0304042c800200c0301889070300b1501066100a02a0403010402014540c000b0320031010340b07010780644000280c160404108803812507a01a02201080c0700380080d4141054561000700e8040d502c949801022030315450004210b640914090111410000c5440e03000c60352651000303000c2c5006220640340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 420592347 1250 420591097 420591121
    0x12010b0a0b131211060a0807020d090e1305071a03041e0206030c0d0207120804020103060b03010612111e130e04020906040509070f08030a1205090309131127010305 72
    0x1100c2d000c102d0f9504008051030482c50018000c00d1554200c0c1e000f041d1241c6166000f09410f0140d00c05800b65541600a20030856640d03140f0f000d010311030360480000c920034a18001c202060b0a0245060b61200c90300c8401800350700e01c42d505a03586224002c400d1205002c2c00c007204010441c2030700d00b0440c45002660203e5010f00005050401003c0b001ca600550707280960100c65105511a1122005a40301c3e0b00203410800c0aa41c10390002c0d141480c082001103c020403241a114142c0314542c2e0303030702c4500c0158050700411101074071445042c040c2180000c3c601d9001070040da64041c08076269902c050b64032890300c166500c00082d46040c07000303002c0940c59298000781c00c01e00c1500c3c0440c19941c0e841603d40341040d5580000007119021400240580d40440600400c407030703036038402e00c2c04541d101c19003007a211b098591010f00c0e0010040118540751200d20210b120300c124034003091404d000c0304101410b402c011b000c0202e086001c41c02c00c41030341e900044205003800c24201008513086c02007824070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 420593597 1250 420592347 420592349
    0xf09140a030807060905030a05070501140130050712140601060c0b0402030f0706030b0112060515031902031e0601210e0a06020309030c0c090f19020912010b0a0b13 72
    0x182a80004500013448429009090143d41040c2201e035110003001004126902c61001920b40e5403030710300c0a08108008065480c1210911400180c00d000054040c01801c038600205d1450402d0070140540010b131705018038001010780c5050380151480600f0401c0b50210302c01c48800c1c9540141d001480180d400c42100e05542c0c0d044031160302b9559507031000c02e01d42500840203823070521138050006442030b4140c1241c040b0420030303650440303050300440c07001090355401d0207140da02050000b1021659145038003c1c2d5400b10810007010109240b880c40e1074200d034000d4441c40c0c98990041e0407030300e149561007201600040f00b031a00030341000320001041041a181d0040b5482e02e61182d4011990050030804c124020b41c00003811952410245002c039602e42c45040c4001441c0034183c5107000038542002d219110f01c0756460a06000d5840b203605030300c12407020300c01450b15a401d104641c4c90752142081c4218240780b4170000070710394014108110680600c0c2c1d005045841080180904042d01078030960 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 420594847 1250 420593597 420593603
    0x9090c051519030e01021c0617190503070f080304030f050c0d0c05030c0d0c060501050108160f09030b18060612120d0b06031009050f060604030209040318060f09140a03 74
    0xc41c049103514022400b0f803061070684c50300c03580081035600c428021100d2040010b49900c801b0452555a007403403843c8003003648012002da41210340700e041445011840808014416801c2d245003030159500c1e002032265007203050310b0f8064040208410190812147e001001c2070742005414032445203040f40d0b803051614080320400111102e02800c2101c00c0007a1007010441d803054800385d0596000007040c0140b060402d5510740c0c100000000d0031b50040310007a005a42010000710042d0030030000743e42c28042085a0005c00803442400004242a900c8240c020401454407094001c8880405e519105001d400e00d449110080059690741c80e0001c3d0800345148408211a141c00785e0108650007090512286500510000b003000201d0454844c804140ca6004000700501e495450682545500464000d41c201c2400c2100b400036140c101480c40e802842841d0111074a9050601d041d802d40b5a5401500441d01c0c01c01801e600e260404101c5020308440803c8070a01e440300c4000030404000d0384000b03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 420596097 1250 420594847 420594877
    0x160303050a020f0601090e1b060a051b0a0b06130c0503061e03030406021f060501090504020702040e01090302030a020d110d0318050a1101080c03061f050c0709090c0515 74
    0x20100e6280240300d510403c09400c02075481960307440300600c019213644084004c0c54010904100483d5440d80000d80484802601007070400817001820b07540ca0317000d810880094402010400c04a100070401040f085103c1c050030202400c2c40c0301808443ca0b10ac0001c0d113101814440d6041686512606895018404440e240c5c120500c0515045120444400e4a03405007c00900820710310f800107407000003040d09812007844181a052994225407550047c1070024155204c10051032400350003030449079000920005000c100c4103200c0d400c4030703403044e0120301580010880000c1550140640744001e00f071800e001d100300302212a1a03450b100070110f004180b42d40c80303c101600d11748101c0400e159960107030498010b1516801c01d444800000034200b400200803100203024410001c0540303006490141c03040703189040280c6020361000c0c0003018001000303014010412402c0082120300011f000c5104001440c10803424005e10341c1c2a40c0c3c208501038002c01885a0507945041d00b05c0f0f004800811030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 420597347 1250 420596097 420596107
    0x509060d150213030f0215041202040209010302160c050310020414040507110706090e0a060b12062b02120c0d170d0509060f0901230a090f05060403020f16030305 71
    0xc103070024011205040964065180301008101049129040440c021210000102d15065405510380f0507402420301081c1401c0e00c07100142855009840716190504003d8109204807039041110444040d059170040440c0e0003c100600b41071001c0054200c451409601e02414022028031035901d10b10120f00441d66200010b501d00d105000e0f16229148010907200c03810341e00d0600520f007038110b0155514001503100403659003101842601c2c200c030010071980d81403843d0810109000300c0c0c000e0410340c01199003001e015107507045480c12003413100b0840007541000014014410102000d03400080e090748040302d40007491f9504144070000682c004a03c01d4a02c0c440a42c2076128010f03030950840540c10f14080c8a803080f00071605510401060554071029500d001c076103401d9411919000c0c1207560040d207548800141117203850350049003904040340009490340c0396000f07803031403480c15111034000c1001d10041550500019564200c00002040c00b452000d424010303461b000e200080910100140f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 420598597 1250 420597347 420597383
    0x103050702031213080304150c03060f05010507051f240b040e0a020f0a0306060f020c06030a0c090512070305070609180e1c0e030c060c0d08190203041505010509060d 73
    0x10954139510a0f615130b1a41030514009081026010111807004d0400b60716001080c444d05c507000454600d407035035614051500c4019201540070103c151094090324007840f40e0881c0c4501ca0b540d01c6c0c02510000181800c41e03c4c40f207503030500c1910900040084503501000703100c0d00501554103866100e81510301940b50f500301d0728000e1084101e01c180300c040215440040e4bd0f0142d00c90011144c180d1510194580c1030342007280c440241c0e150081c1c1c010300500c04610345000c0c1d41d05c003d00d0402941445510300c2e840e4000141ca6240d43c890099050b40002014001c010090040400500007810078001c3c0b04e061100c400c81141c04d910100308010781e80c0006204048040117a1071620111400d48000041c122800404048070500714601174400c002a0881a0501c2c2d001c60b4210400380014000b2904240700c103e480c4100078001c050040181450002d1003500c5200a5004034400d0003104480c04039000390b8420740310705030701461244042008000840e250300703ca44090a81c05010306101582c821 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 420599847 1250 420598597 420598621
    0xa050901020a1703040c21060c090b03040602030915130618200901061b12020f06071809020c10150b0d0b030c0609100c0503250c0501030507020312 65
    0x2c00180600d4500010b1100e4260751100650040e4003c08145000b151101e0310625030019a450b1040203040e5044c040012940030307845030241190310310f402000141e491800702d060340c0040c1c1d003d0f14015400418041d00c441d040080540e258011205103400d440d0003c520355000c08001c81c0604443d488a03240603a94525649102c00303103605ca01c2e98041d01019502c40c1401e0321415003458000c40c00400041788050185400c01c0107905040982d80e8041829034401400d00d40c80e45865096128502004c0402c44051080c1441070f83d141d135a501c51002c01c510070410300000c0d640b040441c0d920400840380a101e0125258076102c103980800b040c6480c801600c81c100e400c1c2540f00d0080500b003c20b881140140b9a0411000204200c0c101d80d203880c400000c0008510608111581c003850018030074280d5405003880f0318101d400380e02901e0400c0b5043c192442d40041d0403406c01c203d0107078111068100100c502030000074010071b180800c0703585040000a5681c1c0300c0c1c1070f406004407400c040000c56082402c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 420601097 1250 420599847 420599863
    0x1103030a0f0b040f0c0207083004050603071205070509090103060b030a02060a020d12060b041a09060d0624050a1416080306011704020901050103020705030d0908040906090e030a05090102 82
    0x2034410481d00103001a040001e2a03061050030060051507c00541d03001c00080480c41c1035486080400010441441c2800580344609207203402e050074000002c850381c8000c003851182200f130300e50100c01c09409084004443c030042092040c06020312600c0070940380c00d58100e0649070300080c002007803199240024640070001c400294000000100e40072210f60100b0030121a0030140c90384514424060000400d8404902403030036040001c1c0702c00c200c080c4403c900d4030031841c54005441d11b440341c01c8010601a40c031040c403130f0b036880e80c503424200003200b92000b281003044486241d0000d1030f88143d600805501c03078000880304002c00160074178000c403102c408a4078000b8100210f44070199551400c2e1030103410032240b030350104942d40d159480c114401480c071841240d006040c00d246a081c00700650081d000542c0035607281c807007031210342e0010341e00707100d0440350b680a841456100c074602111801990003d4000940c001d040038508600d80300700000340c810b12002e03070503d20f4881c1c00c81c0004030310340014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 420602347 1250 420601097 420601099
    0xf0702160b0c010c020708031206010c150b01080601020f070312050d050f010f080d0806010c060902030105070e03010b190b030402040e0313060905060c061305010227040b011103030a0f0b 82
    0x20800c0004001001c5801007540d225444000c3c031039080a000107a8407000148500e8066400070401c1204c0c407040490741c6036121405052081e10007449407685258144240e0354002c8040d07917603c60907210360b0415106680848244001d01802030914515601c41040780300052105512601d074418250080c0c4c03d03100c0303110079000100501e1030034a10317062a0764428818031100c0009190007007884a80450780c802003880e02d840e0704507c4d80b1100011a43c09991800944000380d07110042070041e9420302485004203401c0d41d440320b078840110101421101d102c0f10440c400e1401d14001600c1c0c0b485846124210342a1a480b1600c07a640c07400407030080c04540c40300c9c0d4858000041c581c100441e014803144260350540c0e8413509910703211070038400a8402c0b000311014070b6000b02c0002d201507170b01c820300340e02c00d0740b02e00009030410ba00c044541e192050100020400390041814030325440c2000e1040b000318080920707041c3d407610031814002e03480344400b50a03d1096911606003030881c4686402c07600706124 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 420603597 1250 420602347 420602383
    0xd02010f020304151a130203010e060a050d0312020d020a05070506070813020d0501020d020301120b0105010504140d11100e012304050d0501060305150609071110090606090906021b01050108060f0702 87
    0x10300d498446d009600034001c0300c0d00d0703c3d00031b0045200c0d0304002c407400040e60380c041c20380e403030303440342d6403001d4500940301c0100c16082ea400f0030003112148001c2c00030b000740708099200c290719141185021414035100400c00c0d020010850304020b8640204204109543c0c3c054030380d2100658541415030180c407401110140c0103000000000d2542c46080907409590b000e08090545a41ca03130004440ea1310591240d554803e1001000d01030038506942c0805005108132075000d000c4a8220208008001100000000c101d1481c0101d40175604012501c08000c9039100d10140000320a40c00101402036015440c02026141f0054003000000d603c040d0143d508042164501000c41c50b611010440c01c8918501032040132002c41e034000d0090410781d4544140102910b50540e4140c1c2c40801000c05540507180a41c5075280000e81160358400c0580b0503000700c0000d42c0e1000310baa101100c2c8400c0e249140c040f40e1400c0010000c0d00c80c041041d64021428292079070880d1039110049140c0b035a0f200c040c41c40c0354 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 420604847 1250 420603597 420603619
    0xf15020c01030b2d0d0b180f03070618020316090612020d06021e04080102030601030b010e011e0c06060b030901141003080f07050f0609070501321207020d02010f020304151a 76
    0x4a0100040f511800e40e006809100141040d0707e29120782c00c21182c00301ca0381c810f01034080020394a4200c1c0901803140079209106900e6500042c0c035200d0780c40c25104800d0032411040c41076040c240146c50240c1584060054103030025400701c0c03001b40240c28042c02c0b40b079000c24003003410075641020007aa0150184056240c548400d0b100d4000c0d03100741c8055005c02e03c0d148404401d94001c5005c2c0319101c0c1d05071241c1d112518031349451000ba40c96018518100080c070320f02d030f000150040c841c48015200c000c85190703c924050a4007402c5a0721840007180092080040101c0011481c181b0401e5035401803a60740c45a90350400303482a4025040000d29034042d800c010094004000340d0603120340c12280440c1c0c851a5034000660700f03100384005e1000c1c5440c0c03203021450b00503420f10308c0c0c504080200e0030702440c0c0260b51440c000701c072b442603c40304010b03003041414000c019824025011040e051813011840c5090594901141040b84212100d00da91201c254030030071700841c24004d0000101031f068000780 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 420606097 1250 420604847 420604853
    0x30c0f040f080c0f060d090501020910021501061707050d0b060c010504060b150405010302070c08120403050d0306050906040902041407090f09020c060c0c070f15020c01030b2d0d 78
    0x400007802800c00342d2051902d2482c0344d14040c01041000c40303000d09030303900c1e143c401e0341400b000c0c000308803007540c1540d001c00c2294080c1e21604079545800d902c0e40e020702a0502c0c41031420414190680c071200400c041c05c00603480204128182e6a080407041c20034658440d041035407030014021504075150b10840c00324440d8084001900300500c21481b6101c10443c036205002004825030846903503050004080c4000d100c0d0f540a540146000303405220624605170b51043c2341450100503280c003c800701008102001040410003c0c1301040e60641400d10001d41043c012840040d0000c046600c92a15260808299100ca9004854403000d28000b1001d501d05010050703c0a4000e1203180500c00a00400140b654000c4c401e071023071552108090304454036020b40b800c5007038014144070342c6070340680300c400510300749082081001402c902c05030401e44104140043e04120140340030034141803c2c100d07030320026680c900314031b100c03914100440c0b070120703002c0043e0210284c01d0410143d0001030080d00f203414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 420607347 1250 420606097 420606119
    0xc1401090303140a060f05040f0906020301121e050604320606010e03010501120320030d0506130504050607120b0a300305030c0304021c0f060e030408070b030c0f04 72
    0x700f01c034842201e440d681c4030940440c0855405104141209955990034006840c060b04801a464030182001c246400707a903d8510481c3c0c82030b40701c038040c0c11200c90b14004000481e002c411108202104203000071915440e010f4172024010700080180458222041c0340d0305002601030704c02054400850b8400c010f140080380d07140e205a450501103100200c400700c1c10300d41401a03034161880c4815030451841c2550b016a500642290300c1a82005260342004c59900108064410a407582d28041340c0c81c1012000d000f921041d0341c0b415a4550305003010480030441c0000d80c260000b540381340450741c41c0b481c1c501040040c43c5c0c2d400c82c207074000d18203607000880c01034a41e2603024014905100321b50b0006111700c0840d8115030164000c01044040c000070300c5401618003c0c5600c10300141801c4180c4070116804100c0788540c0300b04032072071442d001074001400814802e80b403c0d00f08003401186007900b00140c007a5140d090f40b00703200d0600b000000080c030180091b41501e01002d898050141c8550300c4c0c82507904 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 420608597 1250 420607347 420607361
    0x40b071a0a0b0f060c1207020406180b0a0b0f070b060a08120c0105090d0909090204060b030c0d06051e1e0a061205090309060901030203150a0b09030708060709060c1401090303 77
    0x21003100001c3d02a803640c0f030310b48200c518454100000700740c04400c12091030a5504000810380e80300d6075800c400601c0c00b904201100030503182e02000652200c40ba000c00141340c2980c1c004104c0c2100a01000540140100c02c456150b60010300c0200555116800200511141e40021095014101c55003080c9041c04003c0e00c090101c400c0240001e50380c14554550351944400441c002507090b800c100240c00e403035400b41a09a0002d00003052482d2075000c804a03075841507070300341801c20002544100c0610644629806007108036240c40b02c1c0781400c40d6540c010445080414071885207c01e44903d19084409a2201594040c103180651a901c0c02c029156074038010700d810038681440b0015075414808011601c54020050039a803d00340800c00440c02500010803e94211410450424030341d6a814030290060403403291a81e0f0b25009501414144480c0f075000554030350004090102aa40102000c0d00f0fa07400c918005942400500340340d869a0f00c9074101e19225460641d0076000d01d541504141 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 420609847 1250 420608597 420608599
    0x7120902043902060c0706150e0103060e0c01021e15090f190b0f0c1605071401081911040306150e16120507020c03010f02030403020706090b040b071a0a0b 68
    0x40100d40b0207000350450302180c8904880140c1240300000d10100b4107034003a05095004620016071550911002c40d020710440d0402040103c0c08c1d401001000ba40b80121842100d009001e440080d03604030011b9a2008890030500042c4e104000c0c911030070008000900798000c54032060701d894200088803940320303501d040d92411039000324848081184501c251441032260301ca40c00a40c0c1c5da60703040134107c038200c024219054004c1d0821610810300d0560380b0030381100c0d0241000c1c22565160002001c0746216501400d4180850715041050700c80e10f40d003000383c241001c220301146c0240711180c1010035202d40d81000f0310903840e2400c61400f0503c240004001d42d440d007190200c01da1525030003102103c003070070701c5480000c010b003501b600e0310700780e94110741e4011030384d80104c0303000d4003d03400000d01799461040800c031083d50102c200400e1690421003a0300900060805000b204d003840801c01040c801e501884504103030000720382e010400c104039281c11140190304a0107280c20310240c40e0014015448a01d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 420611097 1250 420609847 420609911
    0x2d15032403030815030d0e0909011406041130070e030309240a0503040b100602070e07140c010203090c040509030423031f051005090712090204 63
    0x44440c6000911105400005000386000c40c996681218000310040649804029415003010282c81c01c00c40107010f04043c1d2510359000007041d0601412080040c21180d00b80e0400c41000506401c401d2015000482039902080d03410381c0c8590500306105400904003e0b5200c3e9481c9441c003403200310051032072004d00002c078240e500c07100c4085881c0c11101800c543c1c190020040c00884d8944242095015400d203480c01042c0398134107160b0b481541100d00030902280f400410001000700f2074079403e44c0001c141c80e410f00344500300708009588203e90f0080c603034001d0030a40810280d13030142222001c281c103150399113030740c0d40700a00815020390415240b0883d144a00c4480380501d1070a4042c9500c510300c1100254142460142c240608030b80d401101d50840c0c05110001a032906e05106444034040381001254045110540140444000410600b0f9000f0904010b001e581e41c0c640d03016400813130030301e000c2d0312089100400000405e003107440213511030302d454480c406d030005200d142c20102101c041c91f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 420612347 1250 420611097 420611111
    0x70207080724031a03100e0601080d0c03050703020f03030a0c120902130b010e0301050703050403230f0f19030c02070e31050607021509162d1503 64
    0x148602031210302d0500700a180d100301d4080b42443c40382e40010055801c040c140081261800301107400c05005041411009071a2030b40c02143d40000c100d01401802031500810420090784401400c4000d51140141008000030302d00d0241072080080ea4410740541041c0e954030305000c042d940041c4021002e00c0046020302c3d01344a0643d1080c8108864250043e20200c3c00d4820703682c07004010861041e041d4140103110790210b040d61024410680324180c142c030002102d081604020b080c6600b101040e00381602c00410707556160031540e0075a038042d688036101c2034a440c188000750b07055024102200c42d0096a40d80300841495140e00324503a1a01640c00f6265620b032589480040000d04036252403a145074000c450a515124030000312401162440800e000c40c05980e90505180090301c5000041c0d1242d03480e030041110178000070360000c004400a00003005139408040c00400d0510400040f11014011a0703110314210307445444d03c0154022055804d82c07204604034810f108400c14400103403a10700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 420613597 1250 420612347 420612359
    0x10b0a0908010c0c1e1e020415060e0d030c0506190b151b0109141605010e09040209060105040504020d02030a0609150909020f0603070807080907050d0215120702070807 74
    0x40340e00c00044044e915401115066103610095491034440d0b09040c150018140d00070480700004960040c2200741c9006200c0001d004100a5954000c0e01d4280110b00110800c101034010280481c035000c1511086000003250605540140c0c00501c050080c5c0510350410494501c01c00400503a4080140300f0485240300c0c0d001d0040242d0030402070510070800b0041c2422100280b0803040300150030b14004103401c52181d9440e5581d0848025103d81a07200b5082c0c0c080c00300f140b15401300500002e20f4040016146140020f441e03030b001510180c050642c032004650164410000c03680039100280055580d0340240081500a51007140c3c111103062074488045a51981e50241d181e920a29900800500e4180315106009040d0004126400529003d40c06004e480c1ca44c05540f0443c51525506403524103c0300c0070b0030019000f0034040b005d4212050038006690b840300440d11154040d2141d508400b140625059144200c10110114545442c1000b90300e0340d0020f9500244c51340002502c59007641c0d10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 420614847 1250 420613597 420613601
    0x91e050303061306051011010f0e0d080906071e2d1b1205030a0603020a0b07020f1f032c0604120f05030105040c0507020a0605130519090203090307050105010b0a090801 74
    0x200545501481c40f82242425621825441011f22081000005c1001544900c0c0c000c40700c09c09803c0300181c001d4640c003c0103e030418051980540c0082c05003802e0325010800420f49102000c0c141c00e03281c3c100e01c0150509104540419100320702c9500d90740041c0050400504880d81c0400050008510464040340250307101c200c448540e81c01b012500102101180039202900001c280d00b020b1070361803400002590fa8104124010300c00303007000ba0355940440c01800060746803848c22602402c4506848401c20451841113940e010692600041c40e00d1100340d40d01c0e1882c0d84128000300c241900f40e1400c0013043c00f190142c00f491150005001c01541c0f40b50560b204060400034001003281400104414105034000480100031850294600f1015500044c03940f041500040002000032400740360f007034a904030700c40103020101c0340c08000c0c420043e01180f228605004403415a5004130204050038000c00503200542c6d8000028484c03583c484035455400d030855004007000482c46640068255018 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 420616097 1250 420614847 420614849
    0x906091e0a0b1e251a040b07030524090c0912030d1b091505090d0c0806060114030402060d270611070f030804140d0221030712091e050303061306 64
    0x701e119461340800801401120003280c000950309243c01ca42030501e10030030310103481e110350320511a12085091645004086810046c02c0d98072100c2c103c10300c81800c4803d55030706000c00c442100c9505c4990b580e080c0b80c540600a001115401080011417610031080200207809030100344401000150064400d10b4201c500401ea184046905141e05204940d405075000c602590281000343c50499201c000c03c1e01001715000507100d120340880e007442005402c1c004a0b030444002d183c0412911251fa00c0d81090f0310024200030300c6403000144c03154046140d9080345104500032120100000807801902424191689045400500c0c09090910116480c4180c5001c80d07007280403a0709030100d5a9040c0e8105401800951f00c2035060b24041403081d104201c2200720840351340c05442a80c14034440d60711811030300044101880024020810001d41c064442031a02c08000400f152100c018140900301d0707a603000005031240da1006064043c0200040194015401624403424140c0101100003c035956 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 420617347 1250 420616097 420616117
    0x31407060929040f020a03141e16270204081501050a03150504060e06010906030201090902070305251205030f0f01030b0c0903070503070806010e0106050906091e0a0b1e 74
    0x6a04081404641d050f010704c602c4602c05881d90032020344a840704040902340d149220055032198107001034410310400c8051444030080300815403052100000560609640102e505482240e0780404003582c4100e1241b46100c02c100d011503655031a56401510f074000070300301b600151000000014582880a070034130032290061604502d060050102d013014140c040c100703850715a120400116150024411280240001c0400013400c91840c8009000143c080e032240000501c10711501002c03e030420200c814640f8442d011401280800c10b003004030f1501d00c800a0185103c4000f10081c2c02d8200c001580032b9590040f039500166240720b40d010280c94240401080301d500100840d922036060009020000c074000c0540700080e449070082071030a5102e41c0454502c4c4c1c032000041007141c80803a07032a070240c006450111b142080c5c2c0360116050f03108201c1020300501c11482c4044142242d00ea00c06104c00d80204020441c56450310510714a411460012095050310b460402981e01140202c2d10f400300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 420618597 1250 420617347 420617423
    0x60810030201020a020f181504060b1602012f0309120d0c020918060405010903140c060c0d060e07030603030e0a0509150d0c060315140f0d0314070609 66
    0x6042e9003800382c424010141345030480c00340c040102d40301c00c05603d5140b01d003843c95036007588c01071920704000607544654480c0000d001c080008001055502c411550495020b003011500c03140313a28108904030740203000c100b070000340c21004007030b042c0c078080020880b0701030440e1107403001c0319800d103401c0e100c5e0181c00010001c240340c0c9240b0310040c03d0032084542d1021880c540900c2c4221a0f2940d2130910b64110f404031026507440014604051f00180c010310b4a00c007544c0c855040840210001c0c0d42da52002d0f0000307580070000305407258480b500703030842d01c05011040400d0200781885100038003d0074071400101c0c04039100000034089170510041500840f500105030111a4944010005005c0720407442d6603001070041c85924007181122801100034002a600003850140240d00d80c04592032030b0300705016200c0c100b0b500340d200d0b075a4503a854100010445440c503032030440f03203070540e075101c40e0078082c41100d4408514482401030550169020340d000303e081000c065242c0c440183d41c580e1242c06111620 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 420619847 1250 420618597 420618613
    0xd0b04050114130c020309040c0201021314100309110d060b030705030102031b03060a080109050a0b060303030123011815030f0209010903120c0b24030a2003010b120706081003020102 80
    0x460f2038011071440144c50064914161401d0081001c1d119140e8602c80940e40026140a400c001e04120383d0080081445a0041801c2c2c07000080d12208000d034140c04060b2142828000d200541c1c40d42c04c03072403070f00038503000001c0ca9529081003d8206a800c05129015800d000140d43c18103000712446080300791840c01000c50b0024009005400190401e500300c0100e003400f044902e82407080f0360000b80580010b144011207480e0522000a00820381406a0002d10040054244500002e0703120303064145540c12244114004a508e90b052840c60a44540b59100015581c2101d00130350100740b044d0399050103182524000c40b000d07480b80280080c0042c194400400c0800d2142c2c8a8080804140c50806072860085c0c607440051002030f10b0020450129000700910740c1d0031f884011150307080660144c4401e02c0c280e154030f0031007144040c2240321640d0314400086607560070340c40080c03103200040007607100107070074114550369800b00c0c026400450b25182c041800b4445a0707010700100c070781c141d00030010030b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 420621097 1250 420619847 420619879
    0x12160807050d090302070f0f1e03020a230307092003040519020d060c03022106090105040f06050604080a060608060c0406030f0e010203070c1509080d0b0609060d0b04050114 76
    0x400d00f9a10941c114002d002000ca00010748800c0c010090030030900610145061202c048610b0344118440d036020080312008000586030001034500321001036603131203440106541c24030500c16030190b0950341402071880c0840d9201296114032000041540d0303085200940c6407410b08030303110947c0d000d00a644202d101d82023401401050001c2c552020340481750001165480900303543d0520b6044022903004507600b1010800d59200d0401c103000c11198084505003040425808281070003090b01a40e103403a1000040200794018900415001c2d041c59907480e034404449441c0c1c0c00c80d19044880c24189140003422600001e0b4060240c003d490126107000c3c5410790503402002d0f0846840b031440d860315a00032a04800384040e41c0300e440c543e12400d040c2c02051400a2043c0c85540c410b00d00c15280a8218010902c039100f0b0744d9041080d11030000740e5a0030280010554007501e00308980c00180082c04421060854016101d90351058809001c41d90b228403904840125aa03e170b60b0300013941100010304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 420622347 1250 420621097 420621101
    0x130302060d0b0a03060b090601050703231306020c09060f06030718030204061502060c0a051803030412080711060405010f0c0606030803160905040b01023012160807050d 74
    0x405860440003800040b010041524421164000e550840c1d894404442c603041c0900c1c0300364400d0003460603610700200d03580c01410b003030700d4180b044010200d9074030381c1c03c84840a402214100621022071120b21a50b4400080d607590441c26441d01455441010404504010700344018070301c0b0041c0010b096580d000740848821017040c030f421035403180754080000540c64520480e40501000000780c1008141400c001e480c00c103000e420000e0001c010003883e1800390303208081d980ca2030482c9908000d075911000009240d4000d41d008400c03c120f0700c00e620400c00480310f00401c1d036540305503441c0391040000d20402ca81c0740558481d060210700c0c03000300e801e50750380711314031031403103030348501c0d00002c0d1a0307101c0c1c4694026030404ca4900203a0000900103440c0e854001c103c010040c28102c4051040800b400c00003512145000e03c41c882e001d45903020b40310007081200080c0c0baa11681d208042e2207120340d005902e00000141e5400b00c0d0510000b11000700310348940701d01445031143d625a149401905220030700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 420623597 1250 420622347 420622357
    0x2105010519060504020a080c0a14190f0206010e070c0212030301060306031a01080d032307050306040f050610030213080303040302010209040c030b0924092409250309080714010c030213030206 84
    0x800c282b51010503070300000100508442010601131290b0001b5184014104840d0401c3c1c10081d903214000410000c10b4203040c030390340154686400c0901040c0c42c4003240c81483c01d000c0d4841503000100000c98443ea140e4442d00403640200c0d51040f0840143d00d0303210140100b8010041075402440300c00300d020b800380e001401050b003201d088521b29500b40c3c030f44020300d00e01900e569000031000000c3c07041c0ea1915008451050039820703020801070410500195106001e8000d210516401146680465005003417050050038890185c0766030f89420302d0024001d5101c01d900358403591402d0f085081a9100f07104c3e40040f090f0143c110321260300c40083e103201c08160f07000040301c001144074460a90b9212200b15500400c2e168018103030f201c140c02c1e511102170300030000c0240603d80c0b400c1000200358004854040803e202e050340b040c007108100c011000344c496081e0181c0310120015005041007841c2c01c10b045c9800e41480200004942d10000300c09034814003050302c4200b160090305001518040000700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 420624847 1250 420623597 420623617
    0x3070b1e091302210901060b0711060712080f18031606060b0f09090703110711010306050904030c03091a0f0904060914071214012105010519060504020a080c 69
    0x100030b03484070074034042e40d12141030784041084807000d00d4101c10441c05465041400c401c000e00401e410000f01030414006c2e0b65015000a40700e07800100580c6900302100d00d0b50b0340201440c1b00980304880080d01d615030944203440410030141c0020003015044c0100d884426044010350700c0c1c528080f5000546c088201c4055455554540c00000d84400d4039000300005a130712500350303803500480410031164050090981051600740711600032070700b1140f81141c40e040c0e80a000c000501035002c00403002000305421158115401d981400141b640003410040d241d88640e684d081815110703503011241050130306130441d1080050000009000d54400540300f0001c010704000b03043c5a0390070300c806c26100b00f420452030075820041409415580200c440d442480d074440f00340020007407040d070010701c584140b080074240e4041c1d107095051030f00040d0043c200c194100d030003448941062038944d0240b548034621000c1007450803074005120b050134001e40f020902aa105d0f0409981d8489030611243c0c0154450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 420626097 1250 420624847 420624859
    0x803060414010f030204110702032d100f1d0c0103020a0203092110020a1403150d030203180a0e010b0306011e0e0405130b04060b060d0e0c03070b1e09 66
    0x1054441e218096007600800c0707980c921a10092660051104503040070031310003e0b114080125102688000030b0841c1070040603a24104085140390b8445d603031031134a155003402e41c09880990056141c0c0b40d0402a0841e828080400443c600051100300602c0e5101c07140d651504018001d501c150700030703070181043c4e003054016240b404807503c0c001400e90344070010b40354140a021000b0011154100030403500c030b0055400861505100381800313401460bc0c1e220b00da01c05100040099481c01211440300920305000d86400445e100342e02e0069102d40064514060150301840301520520300301e040d10085582441112003941d08204001e0b855900c0200154103020702032500010b61003010312000d0512859680b03d4804d010800e08005c2928409000700300c02040c031b00802400b2076039811410760056407112000595180303840210b0824054000c24a8a4520b407401521b005207000c114110410012416034540e96180e4080950074011881c0003050460840d900200101a040052446030002050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 420627347 1250 420626097 420626111
    0xc12230114010b070b090d1b08121504050901020f030a0c0905060d05040501140408090415091404060e0f0316020f0a030305090108061c0305071e03020604110108070c08030604 77
    0x180201c850a90050380581c1002a500060105524034280c01071401009015009101e04c0028611030340585000364001402c0c18210800c1030b8201100c1101c5242c00002c1001c0c0ba244c8041c1e80408408a11180540e007000b000512200040c401ca49401d9480c0c1c10403411911a654a00002c00c00350301d0341c000b40202c200002c1416914040a000c030181c00d00b1011542d8681031038420f0944803042ea0710300c00942003e0501c800201c805044d10300c80e183c107680c000fa2007510510f500846000329840203c00710700d49200c241c0943c258400d41c920450003003006020070080491001d030303107015130302c5221910f4100348005c1781d41d114000054480c982c0010803000d14004204000303522880940d0007100450700008010031156007203004103a000000311080d03015101d01401d1000d040680200041c1003102c0040c501d010040c07214103200c004420400d030758210360315500e0003a5840ca010764094604000c4450700034950742c46100d580d4401c04030b44d521543c0307121055a0710001608068042c42d40592180e05d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 420628597 1250 420627347 420627371
    0x30e0d080405120c0d0e100507080d0f06080102070c29180612040605070c2102070f0e07080a0e0c060a03090b1501090906030b060603071e0207030c122301 68
    0x64500d071000000504008107681c840507007100c07402d0506c1c0e802004003107100000e540d00103051b101082e400c241072558503081050f101e0000c05040368168801490300c1c2003c28128415400380400511400200182d65110b91403000310707010b11405683e06141c416814841c003034584020701002414030751715000785155000011641d81000003078a0031441407400700028004a40211500940c842c10040300b1044a0345620008d5907a64a0740070380186a101140c00c45442080400c00415a034503d070021161034003022501d00800391008000a0300003800f1400210040c4101c428070301901d4001c00310070002c403050041c0761704a029610249665040343c200441d43d1151021f102d0f408098145161102303482c000340c0380e01c800e5000418028a09207003440062046d0300282d821000c200d074100c1d141d42e03031074a04550380010006c0c0e054804080400e09242d0320380029005094911070301d59848ae890712503100c0d09911480329006004580c41016100780c13000303468580303c26626003e0010605008003e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 420629847 1250 420628597 420628633
    0x5040305032106010503062b080d02030117120a0e0a0b13081c020a0b060303070807050303010f2c0c1326010204060804080306061e0c010b01030e0d080405 68
    0x8819101191011460020300c94081c1d07082d154094424200300b400c40c00c200340130508c00702c01c410090b030f074450001003030754070100040a0300d4100e42c3c4c0c800da986a407250101107000281d00b081c030509121015206803100d504c480803480d06164940d00c02a2420300ca0000412150f0540402c0311941001d1110740202c2c14050400060180040750028180072601d81046207142c0f0851003000c400d0100000032004242c0e0f4045038040e1a40d17040f240c0c8003c180c540c207000904610540074010010303240041c10804101020000e0341c103ca1030010a0800b040d80c582006241c0884880e01d00b4000c919040880030826841e210280c00c0701c560300d5280e081600000305160f0302580d682100e46288034100080100f030142685410900851000070f5040a2608501800e4180f0151005003180c41c00f10014960752184019a20340d101d00f0780081004882d1031022420380c0d800700800c0c1142e03500700418141d0303a50080c040e01e0080d004002c0100403007008080101c8d4511405881214540034075500c00344000006 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 420631097 1250 420629847 420629857
    0xa0603031b2d03140405011403091c09030b06060405090f1009021303020a050d080f07030e04020d0509060f04050303190e060906220c210f03021c0206130f02010504030503 75
    0x20440402d50391200c0c01c0c0548081c40c100740210700b0f07001c1003000b44183d9030b1204e480e41d458440c81c60501d850781c4400220a05010104081c1001140c81144469039140c0c0891420202c0b809030320b5030303241a1101414000039200d18018a9000400740340800c04901c000e0403d141d0080d4240d242101050b2100d1291003660720440c0d49a5800c17110700010f0044d450031881c04002020211500684850136680d101c001d409503000c00060340c140860200203060282140440c0001c2c0100115901d484504209006020507920386250784141000102803008013a0660702964002c4000c508541d00c890001060080c6d55014400b901d45504442d0031080003008124050411040a8601440c110403202061816000e00f03084201c004000c020200710310340d00340d03029036255001c940112100740d013129203501d4201d48000c100507804134403001410b501003102c0e00c0300c81c84c1030300c2c0803a035000c40901240e403410145d40c01b09001128600b40000903620701140c0ea034181c4181007280c1499620b03152142103400c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 420632347 1250 420631097 420631163
    0x828091701020c120f0d060902040603050108010c020c12030f0408030a0e0d030e010c110904060e0d05090114070c030b1612050f040b10050a060e04050a0603031b 71
    0x50414024448444610260a60003000031414680031034003184c2d90700655001003031980c400040d490401c25000c4125103903552400f005001141c0c1d10b0810100a50051150f0302c0001d183c10700100b0821818001c40c4000a4591300500d055240c4100b008680000054104c1c3e141c4030400c0903040424001c4050401402104055030710f905140c0b0f4040d04211800c4511440b031303d24a00302500103504845a006101c00078a000b00002c03141d0b141080c00c0000c0022003d6000407810100010001d00350082c4c000e103100203050301d00180c207465081e611030050800060204042c030451040c00d0401c2d00107054120b00400807510348030381d617031283e0280040a0760002003140210f900b0408036a0040481100001d0000080040d480c0441c40c03031119520150009100e0010030002c01d661000e442040d8003e484000c1a2011460b500c0c1400303072210f0b41c00001e0038004c0f0b04002c000b40100c56148128021a42c00d5265240190903407034841103039915403141218410310000c40c1c19900440c8102d00f00e0707440c007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 420633597 1250 420632347 420632357
    0x3040819050c0306010f0e06010309150c140306060f090411130618030305040b0306240d05130f1707230105090601260a0f0605100806130828 62
    0x340604180c0c1c2004011401c1602079401140100300c9809040b10711400c4038007504941c0c0d01d0361541c4004030050300c00340002501c006440d075030070240f0301c81550040307054001ca915036109520b07442e54507850314002103036030a5119400703200c00404210500002c1a424000900000d0910021a0300e0811500601000303070000303107622000d12450742c03c0040b0040d10002e0011012400b8616603000700f00740709a00645265078004000b003082030310351042c2d03801a0b002c5240c0e685404d0f4905803c9082d5500803c103003408a0f81413a0110728891601c0400903c0d050300858000122486a202c0039045402c82c4200d411000d0200100d00c089241045022106000b0703a031400d106464140c800780c251440039091103a180c001c00010005821401102e0f041076403058480c0341d03040300354402c41e03060039813111003d00f030106001d01d400304021207684805e20901030107015040d401d88840e44c0ea0703521507045507a4232100708030080703010124612202405051509140540d50b2086000c1005040901460010f01241c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 420634847 1250 420633597 420633643
    0x3050a02010906020a0519081201090209100e1c03051b1f0c080f0702030706150515040b04090209040204030515190b130f0b21060f0c030612030408 65
    0xd030744505000b000b41000d03c0100403083d6980ca40ca034035003c602e440d8580400000304003408001941090342c204003a2000d00c00d4066035680c01c5d0038042c0d400402e14900c180074580042403240d00a44221001d000060003a4004100d2100440309203410828240c080c008107001e00184040100c004c0c0050107a5800500301d45400c0030040c10f01c0c115480580c841041c104130208100b540c0c40000590300c00c0c01c1d10b2030b080039a152080c0680c01d51107001009040f241c10040d10b04424440c9042003421514140c41640d0b181e000001402c0840c0583e0090582c104810030041140c00c10503005403010740e20040005141596a640b0301b40b408110440707001c20070300107004000c0d80810218010b0401808a8814006c4086500005040454003c40411060f503151400001c1010740e520200c8280c00c050714041c0c07048140401d8060440d0f500200c00c15900c9480c00180b00f4084402440f80039440030b000301411510f03010108003000d84205402c0c155444140400950500c0c104040581d144214008040e04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 420636097 1250 420634847 420634849
    0x1911061b0a02131e0b01050c10050402030607030c080c0d0f06030b060f04062d0905040f0b15210c060d060302040f0501030201050a08070c0819030e01050105010e0d0501060f03050a02 80
    0x2410959070b2444050b10380510800035403003089600600d1046540001010701401740162107a004a60210106200d14240e01400c41403e40c03149000b18021001c03292160fa40e00b0741117066a00404903a0006481e24000c290750b40040700c050300c0505101036022811107081c2d81e8990459003684e0054400b46c01d28401d001142c10111800e040d08034044c1c3c0e05100c1c180c1041c003500941c268000e03004d0346007039a0301c040440354401001180041c01004106102d1030500e800d1146011041b0502588c0c1000d9203c00f05900d010201851848005d026043d0941041c03a0aa0340e0700d80d00c803001c00d01c2c801e400380342e1b401c414a40c0c0321300c0204204c0e16401000a0260f003103005100445510f0003101070890b20780801400540e801c2000d0b124949460703d04800ea0b41d540c80000c1381c00d60071001000700845004242e413003007035041070003004d0742c8040d65504106071410340604900b0303100203225050101d14401080081810120110704403d8010400411142da452000074200090740c0e0058945030071071a258011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 420637347 1250 420636097 420636109
    0x1208030a0b0d2004020d020a051c18080703031506020d020c19120507030605040f14010b130c05040b0705070302040b0901033305070f0806031911061b0a02 68
    0x12001d00b6103460180050030760300c0c940031074494051604000351550180e0300e9540c85404650305480001c00c25074545240660290454116440400148200030358040c8800a24070414080203000c682501495081c1c4e282c044059219050a034205911040c0c01d0143c4030351346040d240100010b900801c00584191002130900c99a4212240b1401200f0403600301310700b50002c444103846107200308109009c13007490002d00d400e0056000814507414142003000f8042403464a00b4083c1c0180c800301c0c0c01c00d80300400e46080300c040c0500540e11241c03240c1040c1948041d136010b42400d05d01818442d01c6e0030384030700d50101b0f903030000350048a130741e400150144210305082c020715040c0c26007500c0306841c43d4199500c0315030070090700700b002100c03139100540c0c51020040103c050825440e1440b080001c1c1c10003035001480f801c0c02c3c8150f0070110304040c0c04035400e07003000524903104a1428031603085440207507031513190b1000404000e990010040c402440294064041d001d1030700a5500146109940380c4113002e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 420638597 1250 420637347 420637361
    0x3031b1a090f0a030818011404050c09010909030203180a17060105040606050405101d1c060b060a02030703050c210d11030c040306090213061e0b030c04060809071208030a 75
    0x42c81d40c0203d411100001d800035206600500c1c51307136002040c5c80c2e800c20782d5401064000b12a2200c9050a03052005114000c44e1000c484581920344120701da0b220003c903015910045001001070784104040e036141c00a07a114282d1820005001c180e00703582c8d5050401a0b002c1001104c00760342c0001c001000180f40500c1458014a100d00301541098034010000b6010002c54241c030041c42410030304140203241c910f41000d500c0c40d0003402061031803c040c2c0d43c0d001e44051030000302c81d8145000060007980c40c1580a4070350a8904c1e60080d8030700340ca1a501143c4a400c522840c0c012071107402e000c252217203c826140c4418541a42015440c3c0c070094851205840c03080c0f105d030202c1503040042c400d072080380034101c03000d0b660040c00c0440d001041d031000c11030981c3d02c0760840c6071144c94000c1c0840c91000b0f1143d101d07916151f41c9502402c1f40d44031012224144000c1c1c42d141c1e0300350300030001000207a0040000542c010307280c100359001c16a4400116101035000030003101c180d032001080201c8800a4442e810f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 420639847 1250 420638597 420638623
    0x115030510060806090405030418020309010c140412050a05150405100603020612090c090a020903010c180504050712020304050106061b0320190507030c0e1003031b1a09 74
    0x34142c40d041d4040c00040001e07001c00e020300d88040c001414440208112002094000601088010801d440070300941042d26402115420409451b410902c104500615920406400c9140510f40b0f1a0a0540b110510303007181d96004000481c0d010072001d0214072003142540300d050049280c90310700141000c201c0003140340400e00d85070342880541c80b10340035945584c0c0f40f030342c4010098036185861032418445041055005008808000c00440326401520603410b00398024450030296034019515004440601700208400041c03c011514098200d9900b010181c2800e07140f00c181d42158409130307401100c081d20280c1d15072030304014280d4400700900c020000b511070210b09000d160790040c0460049a0350000302a000107200c80f440e1000d01c8bc007404104628038260075000c0a00d1704944601307071803200380c1d4a1100a000007507a5426140f03003900c10f0080800d0b03980700904540d02070b5210340b050001c807000e004000444c007000498203107940c0c40d41c11401c603542807145490200310f407420801c16451 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 420641097 1250 420639847 420639871
    0x15030b0613120204060302030a1110091809030921150c0522080f070f0e040c0b0a020106050d15200d0914060f010608090a020108070806011701150305 66
    0x4007001d411a002150aaa1210580c1460020240006405803a00d41c2012350b16000c0c005224082000c400c0c000e816400c0d0640d000b03648044034580a44094a02d03115070004600141a10340c44911240d100d51318241c4281000000151150218595102c403028008040e424042e050002d21540b6140f04a824101d08401c0c010544075400080041c09908401201007408140174608085415811710140160b5021607000000f401100d0340d540e18503220341800c03035640c050007040131494110054441c07074208810205041c0340409076007942d40601c414000b15580c07100c0104495451543c688407450040003201150107024001e1011211510488801c001c0c00c8079802a110780040c00b526200c40080d500042d1b00b003054101000b0400380038150b0030182c007842040100b41b040403041103068482d19034595100380d442d518403503a0b5940107030000c3d000c5019200011301c99445912070582c410010700d003c8140b403821046440c03641500781c01800100d070b00d001e05a06042d5243c840c045c0d1041e50b200030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 420642347 1250 420641097 420641107
    0x6021b0111070f020d0f0203010e011d0c010c0222020403031706090403141b030a030e120306062502180603010b15120735060108040b16020f0715030b06 67
    0x241c0241043d0014001c0c00391101d41400d40c24410346c811203459035074016000b400070a40302640c02c4c0c004e0058289503480c6107028080707070000c544009000d21035180107860b0119541c01540803c04548801310850907200c841031804c8240070307480c0c0080c000851294a980c3c0c2094406003514124440c010300460240d1480d000304070100c0e9215600d648a401805281540c0700c1c0440400b0101d5481000038012a201c005241203c042c2d059000b62520041c1c903065400c8010142546400c0744800d40707001e0790022081c412004170541c00a12a524004840380e400c0d0905030550102d0704c21510b01200c00030104401081080a05081c021184088400c95561501a15107010a07105008070142a2140010800090140c600484e01410b49406a03a5014844100a01840583d603585c0100c0380250307002c1e2011032060b50285820350300984e40200c041c80956960120241800c840341021811031107000c020604003039040c08041c02601034212005000506407501071305691990100d903025504c1001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 420643597 1250 420642347 420642353
    0xf0801081501031103030903150108070e0106080601050d0e2506020a0312090317040c1d0403050306090c0f0a0e030d02070f0303120f060602060402090702010b1509060706021b011107 80
    0x141042c1960740c000c62450141440300003091441c02400141600b501c00d40800115038900004034a0480e510001210901074030364175040602c5a00f84100c3c00451440c002060309903024901074412400c001200048240c2010741072032402030b405500c0034048100341c1d6414441c424032407810002d00b080f4001490200e200d940d00420a1812086404506039074140800400d841518001d01d4001052030400b02418541040c03031130349009201d40416550000e2035460b818411140c50b0340b240750192030380d40c2142c2c0c44805201020700020514603903020700b040744080f00b1950740d000e00805412030340c030440c06482090070b242c0f0341081e040480c1d066610400c410002c1c05840c2a241056070f078185000c0e01a20802c44001700540030041c540032201c2d003410000315600d6030001c0e106105078000c554815240c0c170390301000e9089070014036410760070200500810310080c0100f401012007110182107035203001c140780c4521049801604618203001c0740400141d00c1607109009000c60154010249444e040040d0303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 420644847 1250 420643597 420643633
    0x109020402180a1e17010f0219031505010c0f03090e0a060305240115020705040f0b030607030509060a021809090d3c0c0c0902090a0f0803040506031909030f080108 72
    0x2200c0c2001d061010040c07110b40e50300039004401080e1f04080150345074100040c1c0d0041030a040288240003070b281502c40d4a4003100388185404860041c1c65461014210b0b0710380c0c0081e40ea00000c1036081c0030070b41c540018150103d0941510480308004001440741c110310344141895812101c4400220402c01d442a8007802480810f0449689410040c515541640280e04100b030543c80542d1040c5032201c01c9100000c81e8104483c1b1517800c60030340d51075076600c01c0140c3c1203440540f100d061641c0031800103001c81003240d004108007840360500c1c0b00c112200400240c0c43e650201d8000a05410410300c181c039190300144e02220424400203c0d0808200000050342c0d80c000d10583c02054000c481042c45001e4002c03e49050b6540d08001041440340e2550305a0010b54060030b51130307018846103a03002542030f50241b8108140c840038006545000d1400003040080d41015148003402c0001401c0a1511001481082919846034580102400f19a24003400043c0164080c95880d00061561156503000f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 420646097 1250 420644847 420644849
    0x91401020604150c270312081504050717010305101404030e090402120607020105070e06041211040b030f060105030d03060501021519060e0a1d1504050109020402180a1e 74
    0x3d01d42c0019034050309402265640540c4000070404e482d01d01c0803070402686240f015080d6401655000c4003401e07015001c80c3d440c2812264402040a02030b40c4004520b01a000960010f40925240d0100c10041c241c00d65000d001307074001c0fa0340d41c0c40b8503062024800d581c020032442c081d00303889400c039518003501c01400c040c41d10306415104212200008045640e8076004040d500c6881080301c2c6c86262101002c0e00030403060300c000011a00c07401c803004252610a04940c280e6182d86c50411451300b250f0394001400ca140e4a2440d03000f615805400c3c010b072410041300c004550820020a0300354903000c1407505000e80a420b140402d41013250038881030340c0008613000f007100402c0c00342c0007039a1504800c4a20b0044491240f682c0f5080c100d0000740d050030f241030f080c0110f10160080014400d41c0d007001340760324040a609012504101e5250340c4201010a0b501c1c0e10034010310000c0b5589031103500060803640078800032902c8488080311000c1500b07011341404050401d000c8450b01020816088040d42a40307 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 420647347 1250 420646097 420646133
    0x7151104030b0405032b060f06120f0f0e16090603170d0902030d0e09010e15060a05040509010902040306050a090314070804030b070f0210020414060a050c0607091401020604 76
    0x140403c08002d030400480385040c3c20f10050a41c01d010042880811402d1a000040306609080000c208140520000030845099846003c1340c03036600400348010300b00050050002c03541c0e854500f400e038070090003003070384a000c0c40c0c004c1d008484e14503003050704c019055040030045e1031500b0810300000c0e502000031800481403005844e12920440a2003014021100c0c0094042c040c2140c3c1100d540d800c000280f0303540c001100d40600a80e2100f0303000004440440301d0400369813003140802c00c6810f0801c01004204e82501d096882c050319500400c2c400c10003030b44404100d42e4001003c006020581c42941d401c04064501845803000c00d444c010700c00e5034200382031240c1c120300103141000c01448004413001103900c0f0510301e02c5d614103507034060140102c0240f100d0150246a10640703070f4000c144220380035034082d80910251030b450002031010541083c14041d00780001040115a1041c0421250344580340f20f6450015590501910300d07101c030303000410541558089001e110000324104001209001e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 420648597 1250 420647347 420647363
    0x240e0d030c081c0f0b040e0601051504080f0726060703110403152408070b0304150e0f0709200721020604050139020f030a050715110403 60
    0xb42840360007480703070140d103074151640c100c02c1d0904001690462550003500140030844881c172141400243c940c0c031040c00e5001d41241c1d005100500d001c2034001c40c5003520309509804e00c1c1e10345810f2403401d0035034510703c042548078110400401011008220f01000600ca0680d020301020941d682d503204040c0003502499112018005058582c0382520025500a118030303c00b1149007203040024500009845640d5807019110b1903000440204441124142c0000744015850b0003100881ea40020b8021100c90040ea800c5c0780444038a4042d05000c052040c02501d549802d5118180c5003915940c0000380050902190b046404280d00c3d50090301680c06000c10303541d86140c544410841d80500e84144400382c43c441c5022000d500003105446203205074000c004071050411600316401d840e00d00880d807105400c24118030f800c400603078010040b0540c0110307103042c2c503000d40050035900302d5003103500012070201e030090a000341c01e440b44100150301202000724603803042c05504640314602029040300703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 420649847 1250 420648597 420648617
    0x1d10020307030f11160f05190626091615050406031814100629070f050601060f02071401050304021507020d030801090e010b0306060d03030b030601240e0d03 69
    0x341c003c450000e040f03a01082960503e04d6803100b030403217001d010b002e040d041c104460300105950604010940c0181c146001820081d031818400302d8411382500011110701d040c480c00400d11003041c0ca000e5010345194005041320180c010814240540d00c4d50080040d8182e4000010019170004125010703600390749004900c10441c45410303010390001c00d100522403c804500c16111410104800d8603400c0b44800502c02036070b40b9100e440048029044401e05040350040d8403d8200c82c0304010030565206485008800100703444050500f40241d001402043c042048002115030601840014203110304d01600d49074241c0b0f0009056010007440280640851902c00648908410940d00d55990003000c4141d008010314004002c41028803c1501c181d0400c00e501e001e5903018020518030580c0607000308100d40d43c4208100000f03240032410303428103680d030003502900c1d2020302000340a0b00f1405551090000704280baa240c20301d04001d1001042411540b0342d5096441d201030006027605490080108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 420651097 1250 420649847 420649877
    0x10b0a06030b0d0206120f0a0b01020d081806040303020408010e031206120f010c050d2a051e0c01140105120616302007021309121d1002030703 63
    0x907607003181c3d019503c40b00225021420490000c40c840c812503a1990610083c0c4174074100300b0950f484501c0e2980560001e001c0c0c48a890311030070740030783c0c842801510b882402c03d0000c01c040c100032041c1c50940010b030700080d090188035000d00804020041400080d85020f82c134800b09014910301070403c6200701c081d80091110180108100e4001c100b90400030081c1c14401e000107010b42e8440109610728904024510680703848100030359070008541c1709090441b801a241c00c8401754818070490300e21120410451b40e641040001800092010000006140a45503504001400140d008a100b0b0a4040a140400343c020070110340000c01c920f2000981d080b060001d0b80c0400090390170722164280c2c441c0018140003e112013075100720340c5400c20170142c0040c144000100703d2800c0c1c00307500440200514001414496400103500400344030024024006070f440454103811a94102e0005c0c001030701c3d0a06400111840704441901111400c628000c281800f949034080c88601030203110504920341d03c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 420652347 1250 420651097 420651109
    0x90a020a05210f06090f0f06041d01061e0303050f07060f050f070306090606021906020d092a030f0b060d0b010f06090f0602070b0705070b030414060702010b0a06030b 73
    0x140904529085000b503000c4090010400c90444a41140c4440310011401505040056034002d808044d0a540d0540e281741c0c220405c58400713402541c000d0360300c0c13144980742d09001c50550250781d070764070000c10420725205009103040c400700701248003452449000c0001907040300458280d00d642c200f0a5850709468141741004151056440d58881d080000300b010403561601d0701445804180c40c100546e0341c40d110200201c82c07042c00b0340b5000d6400312140307241c0d0401058050003030328880c40e009403610b10421040c0d404d54807001c0040750148801450070300313404c0414113240303001c40090b60a00c400e07a15588424401030400540903040109600104504c0d849010742820607940112200b909035a441403c00c1c030203107652142d00b0001e81c1c41c0c000803503130301d0400410304221962640244282418802d060096900c91f00b412031b003c2c800c01100207400300801000c2c0d881580100f01600d03c0580303030285d813405e00c60004c0282c001c6914150000a49945011040c01a1016840c00080d42c103000008100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 420653597 1250 420652347 420652357
    0x5061e070209010306050a0e1b120f0d03050709060809030306060d0212071805040608120f041205100f0902151b01021206030f06011802031003140606041505090a020a05 74
    0x24200303070b01900100074403650303400c424000c9907071103020030844900d0303070781070f501c0b101d04420541ca084a00c0c0d00921a034906017aa00120001000a541c0000c00351004649040000819400425210400c100400b9000422500204920b040c4094903140c040481504d80c40000c249500c90000480c507107002543c0355040e08c042075040801c054450900d080f02030f084001c00e403103001c400001d116000c40c5500b054000c040c1199005401408403035900d400c1c401003508807442030ba1190b901030000203038200842001200444c040c10252244880500000090301c20480d259204030f81820b17036050050703e400003052540d402ca0705149845a007058250400d9442490110030650300208408110140c0440c2d014020318044040719000c41d9451281c0f0340302c49091190b515800310b802c202c519014080d8000b1540143c1c08900d940485450350781d1242d01c9260903030011950b41c0400b0400c855030400e84604c0d101448403a84110340c240c540400105000303030052034004400e1300030540b400c0b071070700940c1a50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 420654847 1250 420653597 420653599
    0x9050406110d09060b030f0613060209030d110105012301030903030f020711100816081315140901020313080906071a15100503070c021201050c12060a05061e0702 71
    0x79554008404000d0701800c900501500ca07a490300110704103501d070000340303003003480d44200242c81d903551400e02002c800e080911040e00c3c642c2cac00700b10001c0540e5083c4244146000c43e9102e900c0c1c40c40c43c070402203085450513040b060070900b2507501c0c0e610f00a2134030f00001c1281003d10340880d0070101881e0840180041c0f0b42c02c20346080c00416054100000c1001130440248151754060303030b00c03070300550880d0080001d6441344084035586e1819150f891250403815072146402c18040744000c82c1c3d540d80c0c00d8816407070b44148420382c0d640905c00900d60100300c40c1d90300660303240029411070600310b60003501d400d41c148005210401c0007400c84089c0e01c0380d00c280c03132815800a111106044902c1407074448608100c5112884c2040c0b5002d01a15107071032040301c1d001c2e01c40c80da56a415a92100c6080c0c900300c400080c10f9078010151000c4a42540c000d00855210342c0403c05240e44401c10100c04400b9654050920361184c544001706020300c1d02c40f0b0b010f40e1081140d80d40081c605080c1e070742e500c13803480c49001006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 420656097 1250 420654847 420654881
    0x70c08010606050408010f060b0a12140c07030806030a0512070521091804032a0203010e0304080d0c08070b190e0705100c0209041202150a0b010908070e0109050406 72
    0x9034143c2000c00f03030003100c0c281c0c4024030111040c80007440c00c4a07410301401300d00c41020b101d0100d402d481024408848088407074006260f00054a007086031034002c8a03a010001d1000540d0303405c141d80303c4032184c0c00100075002011144050382d106a22864425801c0b403100d4000b003124010f1220400107031002904803203c0f90944200700c1800386d40c6a208185c2d4500400c2c6d4801c50002c52440c401ca03240c840e9405564072147c0720b88801c043c01001c070800c002c4031050421721030b81e4405a982845008083c4001c0401166079500d000095401c04a08100440c01c0c80000350a07080407175854411224543d90041e00380102c0e17520b940d41703074180f111514581a8024502800d103101207500040180603207004984030550610700c1d40040361006089140290403482c6ca0000c03900081d49001b002044601e43d00644034804800e10041d008643c04460860006484450305141540c01101110280c40024044c09209040c20007403030701c801d0180310700301d02c1c9551500000e06003d619407000303060b0200c7c8655 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 420657347 1250 420656097 420656099
    0x31518020105090a0e0c07020312030f0109110d020a110118020f0918030703021506101704030203040513091703101a1218010e0309010212091203040303050c010c0e0a0b070c080106 79
    0x1b42c1c070300307600710030b00c101d000340718091004a00d9500348003540c1c8035001d00598141d030340c0c3c24100010050061803a400d0781c0117405002d4901800b001c1e001800c490032680e80c90014101e410700c82c0500391000b160728800240c03c180d02d440c02584607550601000380b41503e140c0d01640310000c3c041c900c103014105d030421030b010215950041541c0400d4410300101c1101103a0180d03104c950420407011420030002000c20364244900d10410070104800e41e00c136020f401540d0a180c0d0750400300302146220240c0300300d0165100742c240100300390104242803c10240e10154150311301313103030605694a01c038001c0f9200803043c81c007202d0018000c0402c03900400034101b40107c060401388070304070400c3d0507010561120350030001080b90200000044d1040000141e000b82040e1a001c08070160a41c4034264245c1c102d5401d4808040c0b05c20100000c00095110740d40e0543d480c00c1440030b29084601480c1d4010410401e03038007544076503a8035050b10082e03548051840d03684107441d241c0340c80b0581c0b00ea801403509500b0498 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 420658597 1250 420657347 420657361
    0x1d01050c070305030a0513050f10030e0c1c14030307140d060801110301091812031505040e0a12110c040e15010e0108190c170304080313031518020105090a0e 69
    0x11f0040140150303800d80406455504026003000450011a00032074000e141ca01c8203842600008084c00c0c2d0300041c1c0e822074440502291942c0b0300d2060144004440c4a05030042060050340b5a0005070031034013960a500744a81c0051044e0800001143c0005010549003801e2332181c3c0500000c262700380007040302d004048080406a0003d1155030b141e030b031518426030140c03c1c68442e1041401e078042e66811040c51907110a60041c00c0c5a144840316032840382c0c1c02728840d261440703142c2c1008100c0d4014240c03040380c2c0c41e00c0408614549440420001500c611009503000000c604c0000030b000c0385c000c61003007070382400d03c0e103082c00c20815040002a507000015651403c5031005041e00c0c5100300f0749050b00d0b821441403800074580d80004100c0c0e40b01c00c0081180085022001141102a0044c0c0340b0b4903a42e00556072650300100c551440040120310200100880402245120401071000b0300801c0300c6500d1106c07881d5820380019050000020300321007103503280c2d0282d81c05020310207240c2001d410801c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 420659847 1250 420658597 420658607
    0x308071d030a140f1b1f0e130608060a053702071a0f070e0402210c130b040603050709080d0e01030b1306031505060a0303111e030705010b011d01050c070305030a 71
    0x601743e0b034014910301049003003109080440d03030010109038130b44a840340840803d0144207001d60211141962342d070500030400c2c940511646000303201c90334001c41c2ca0700303152103202c4071050501d0312007103400380e001501080015984d864410454007000300586540141c2070010260042d80c1c1c074000d03035554000c10040020b0010f04128060201a6200d4240640403c1404120310905401485da402414048104c103140307000340750790040c41d0440580c242001121440b1124505811001807004007042c140941d680c5071051640c04002494100401d5140035001602c81d000c1406030b404100c81500d100b68164000c0e041010700100180028484030b00c240180300c0140928081150064000907800c1f642c0e05250042902582c001001000c0181c516a0207035000c01d05803649020a00807080101c00e522490741101c001014003401869880f000c5240042c2114180010107043c02015a40c0d030750f400340c50b245810003070602070914076564406034411134608441540001c140d4480019001c00e195801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 420661097 1250 420659847 420659893
    0xf0b241312051605060f040b160f0b0124080718030c140306060d170c100603060905100c0503060105071103061003020a090203091b0d0f0308071d030a140f 68
    0x30f0403020300c0c82d61103600b00030480c4600c40d04595900000d000501007805020300801c0007803040406580084026a50551515040d21091310060f01d078400400c002c1030a14041c0886640003000305948042c2e45c440605014405040e480801403080b50b00d4403c0e20a180c1140055600680000211652400c5d044e2480020300b074994000d000d0032002c90502e00b000c4c90b002c014960720503101e443e44000e145080c40c0680241644038542e100341c101c07a1000ea021446000c014501805000c502103000b4203000d450300d0b4008a0300c0340000d00c1d01480d60b0f01740358001c0a480e08800c1c24a01103031fa6040c5070401c81c880d0500d200baa542d250003520b0911140710141011a422241b09443d02114290759008880403030108850010701b0b908091010b2243c08038104c00040d000c030004000c442200800c0d00c441d1200b491442c0205c000c114a402404030040e00100402c60251000005000702c004c80000720746c54034107038480100246214102c070103d03250240a84030200c0201d400b120b070020100c4080220803200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 420662347 1250 420661097 420661123
    0x4050118080a0e0d1709220204140603060a030303050c0702060d0e0f030c03030a0519050a050109110c0a0f0606080f07050a0501080106020604031d03010c030f0b24131205 75
    0x56440c01c600d81d4102411000f038855008008003100c3c4217240c2840025a0045080c650f01070b600360f1100030301d818444081e44081b196031200603107035400c1c075a0b40c85151180740b602910864052007003110035982c085401041d66414580858291103041c00d4201901603038100035448a004520300f01001c40a40c40481d80c3c0508004684061003c00c8400e5164421218101150703081000003625008260700099008624a04d10980c0c19a00110f450103c1b074040c1c0364030b003943d0344842c010081e50383c06001f5240d03d003100d2400380f46045010f001c00303562210003400050400140310380840901c01d0591100c4018840326081d544081880c85409440340718500407076201c1c1c1401280032480b5481482018140c1d0760b81e80040034281c441da18103603001070807840a0070103412202106009900c0038001e90310140007944010403450880300c0b41005440004103150700982e0103400d2945540301152814035000381c0d098005503607159003912003030340783e01d6600010304110701030341000304021001030b0a03002410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 420663597 1250 420662347 420662357
    0x1201020c06010b0f0304030e0f100305040c1a0412020d060219022104170a02030102040609060806060306010e090903070c0b030f0a11030109150305011d060f04081204050118080a 78
    0x3881d850400c3d8103018020b0381100440003440002c0009000da03036180002d84008140c100e007081050b00107810318001076400e0001a840d48180b000700100420008094186502c00e03041c0601500c1e21168140580e2150131b00700744600c0b02240554540c100e00c140020f41050041d5503489500b0060a01108220304400c0144104800071001080400f030042e0906000f040c041d103468035003981d9414804200d9151449030140144641c01a13809100030401000282c9803507258030b01c0d0000c042c040d2a0010070450103135204004002e040e0381d11a81200f8454422640c0f1811741c0c80d84e1030030a02e14028440c005282821112022841011090245101c0e900c085107282050740c8100b681c0c81a11601007080c156000c040c40140211030741030304030011600e800303915014a140d803030303e4071429580740d07038003001d009068000e000c00c800700c042c05001d511140b400500f0300d01c2e0801d951034505a220307841941c408180084046810840290082c902c8007004010291001c0e0150600f02401d034013070713890760307001c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 420664847 1250 420663597 420663599
    0x10e0601090510152f010612080f0a120c051b0307050604151401140a080a0b0423060a270803040204050c040e040602090306100b160804051201020c0601 67
    0x103600382c01500d00c030f10840f8661185540c80d110b401c10306030f00b0300800c034002d21105440c550341c08500139000100070ba101401315002d0f200081e65950843d9256000721001e0b03078041c0b00c03101c00b0030a50380071503019a0802c2c1c0540e07039070b0b4041182204c0a040c00706107021613509103e0301410031503000700a01403107898070707032a0800200101c5049035030348140b030b6004182d90000070020300820072060603a59090003068000c40c0002001e40b080500c0c80b070903040100142c0c0c0040c15031030b890812400900103014664010074000c2c9260300c7d4200c58210042000f00340c0d00086503031048810090596101c0c501a02046500034180030750f40801601454142c222202e0003903568000d210625031840200c25040905d20307103035407215000c1c04040e0074002c000d0f04400d101040001883c0c000b244500d807146008074001611580041d04041c107086020303021080d4460044400c1c492501d015049401200803031049010b801030310310304a91075011fa0340c00384d9805100707800d81c24480541034000701015502d103400d41e00d0a07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 420666097 1250 420664847 420664859
    0x50d05041505041805060112020705010516080103081806091512100b0a1413060801060f0206070e0103091511130e010602030f07140a080c0c010c150b0d060905010e0601 74
    0x5009a01c0340380000b44d00ca0700c990502c09015804150811410325000f40e0740d00390103498030180c0c1d1107200100c0d0140e43d03170b508000c8100c0d56010881d03030714981c03882c02008551440e00c40c406607001e0100d0b0081117880c8080011019520310341252502c150107442c2c40481180c8010b200c08542010910491590070303000000c004044140b90042590440b0203494140b41000c4003c4900300c40d0780c3d2204e911203204100040c2d1100c02c42004500070000740c0c0d988042903040000051103e01c0800c7c0c034030107552100041c009225003110408045800070302e000100d0001c20b08051801c03103500410030304520b02e0190b41c417904800030030050402101d041f8000020a503214081d058498091040382c0c010f070020f01404106111f90002040c04a009440500c0203154500d11182000c000e0364046074450340010b49002c060070b042c40400c0d08864242810020b05d1003907202c08011100c05d01140d40500d41c2d171038034000c0c955201c110000c403403500700700c0070050782c201850114020301c0b2528041d80d0f5886544000140303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 420667347 1250 420666097 420666107
    0x9070509010e1914130204021c021b070806040f1506092c0c091f080c010e120d05130902160318030f0204050c070b0a2a05180409050d050415 62
    0xd4401d911401c0100d540b0200c51880051540c5c034102e13071043d02046518900d0025081c0c101c440b10b48407100594a4425a03c2c2420b2846105c01005c41c07900f00c20740c1040040c0001c01e2203640550001d18141d10f00286240482110048a261880080ca045030114014000f5070010081442d0400000980070b42c02406e1002c442d82c2c01e8003180580d01005400405042c1a030056030001401c031060300f01d101410881342c0850f140d03a000009a43d00654051005607030044005c80040d10550308500d054410314003040d11091000354680c10301c00c001482c1860020400d0394500103000081045480d5607105000c1c2804c03804911042d030001d0346445900034004d4166420400b229441240c18840010690902c800f42c0001072403503565603010711010b40130522a2050b2449600d0030b050000e074011607a009402402d048032003c04000400080100b05690040110f488510040b03c1030814181888005800307040f160000803d28024242114001a0400003403c15500a504640320881011004a40b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 420668597 1250 420667347 420667361
    0x1305070503071818021c20090402040b010504050a0803070209090d0206150d060f050402040f06230a0329070201020f041512110c0f0c1809070509010e19 67
    0x180480143c103500315180640d03000c4540400703402c01449010b215500010005003900391214075240d440b40402041120180994842e00101c804806401c041a03000c0380302590002d0009000e10341c0c401c92242141e018000351401440d004000b40080d0352a603204680729003084e44201e01440c0904046140391030042403c113002c8050360b004000990301c05000a0820080503c030941000c1c0c411740240c0864014000d00c040c44464001c08519414588107001c02c480344404503200381031030408244589644003114503c1070361440c03194034011022000248030f200043d070000f000e407031000345044c0c8902c1c0d0200c2c1c4040101c40303241d07005c4041e54030407200340e082c1c3c800c082c450b141d140800c1109010765004800740c9588a0034600e0114690070111404134101d410126040141e0000407030a80e41514003040000014806034001e451400e03400d2021845200e50310b030503500707000308410010300c1c0c840080040c1c00081000900180031541e541d55010b0a070381042c0c802070001100102120341d0b26800e801a20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 420669847 1250 420668597 420668609
    0x90c0703080412090f0f1508101403030409020a0e01090f050901030f03120e010e0d1404260313050a0b0c060a0b03010b13050a14090c01030c030b030105130507050307 73
    0x20000380c1e120340d00c40d51810f02c01c0c80c0c00710611403c0403001c00c03e01c010389603550141c250046642a21801c0080f680c0d55140ea8410890401c10000c0401022040b540043d20844034419103488214046a0010741140140c1d00413440c0c5a1003c51a541015130002030040e020741c00703803a0030b026162144004406071045008881e00650103000410008620880c14041180203282080075800310000d00001ea94075a01070990310380d140e040300b080820003400880038030402030400302c00c00000c0caa16088540900c1c17060800071a1090400d4610b6032075884900c03041d40841c41901d544030b0284803030403041c48950003004c1c09184c6c9800c000c500d0b18a00d10445214145610051101c5c2e81c0707038000103000e03120b00f10256400d5500c1303c100000a440c1c0d20302070386010b102c2840100b41403606203607c0342210080e20546d45510024002c5c02010700c000305010f2000842841d0106442050100503400f80c0710003c121038241d031030710040000d11005002e90400340d60bc40c200b80c40142e60f445040503525681c1c1d0247d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 420671097 1250 420669847 420669857
    0x31c091406220305072a0906050d0f060b0a030308090709020304081c39020106030f110604050604230102030f091e030607080907121a061201020309070302090c0703 72
    0xb650038400d01c0071603154041d00c6031620514024841d942e003c016080322261441350003800d0405081700d442d40e01c04001601e4400010400146400000351034540c00365406820900550700490600043d40c00440303002d000030b8042076800d031366480e0040600c074085860404e54010340300301140030856402124000c076006080d403410300c041d29080190902135610410056030340d44155a02401d4074200047d0312080540c0340c09014032450190380102e1409007042c9003107914120080c0700064000c00c80c5440b0581003841036201c00c004030042403080c41541c004550101001c600020002003402001c0d04e559070b003103601c041005c80b00d401641d4078000d03a00070300c0e034020701400030078464141038a030b00e4a5145405100b450021441020a00300b190507030f5100009003514013001031103030003008180d00500c80300e0600d41180216480d100401440b00340320401e0004010f000c6081d5503103504020003c510314030000c641d68142113101680e200403910003207000d01d01c4100082c182c00480c5c0300b661120b0b6015150 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 420672347 1250 420671097 420671131
    0x50c100501031119091803022401030803070e04110702121b0d030e1804030206090d05030106111f0f0b06070f02012a03032a0e0f03031c091406 63
    0x20810344a03c006024403044e0005400010856454050410100c0c080002c3c0000e001e183e007002414981c8403c980c120000005903c1d8803100840660281103030b8002850540f6510740f080d04840ea00c0002034603030381c031904100e060100e0311461300040031098403c1352280b0060841c041c40c10b840e0240e400710404d01c1090300c1c00f82c65503400d1404441500760300c02d10300300710300c0e10b00035000401140b0325100c15803040f44064104410141c0412007180c1011544009011840340407400810f0352205004800421941403040c00b10540d04000400c000303200300100b403100b017000404400c001c100c001402a0241d0a14910f000c072030400d841198071098103e99016602c02841d00191020342c1513401440074120320704005061441101160058503100ba42e022802e10003401c103c40300000440e03182c00203801c40e0710300c0109050300b110900100010a890072a4240c0d20400082c0c00d42c0160505000c00383d141c1483c61020794242d40c01103203031901c2100b40f02c135082c00c02c0307031040d66540040b1401d202901c29054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 420673597 1250 420672347 420672349
    0x706091d18070803031f0611030307231209010501060309020303160503040e0f04050105010b2508040506040306020c0708031207030f150e150f150c0f010606050c1005010311 76
    0x5103041190705204111a2569a01d01400e031031540110341e6594210041443c003161412082c584a00804403454000c060703081031000f450f100d21025000c0400c0c842c1e03031001c80783e0342c6a903010080014980a0501912006c101d0040f040314641110081e20039481c0000106925010740315010003280c001d8020b41c02c00d940c0403080320042c59203a00694840c40248800503511f058000018072070728803107007401d189013032910b485803e540040c0c22400040c18203120901c4822581b4141c0c4450aa01d401d076291044100d0400201c640303d141c000075049800010040180002c2d500103022901d0500e00f21940c40e5070740c100c200e84901580104048000c880c602107206c41e0f01c2034200c0388503000142e800003688505841c09022400d11a4415030350500103008015000300121541e400d103400a80d1110900205071000079541032550001d041b10307000118004011000410a80c0621841007000304081c60312aa0083e041e90803403000340b5518440c44481006041c3c1c0b5024460490382d0110319140703201c0b030043c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 420674847 1250 420673597 420673621
    0x91b0807031514070507030801060305010e0406020912010221060a060c080c01180c06180e2206050411190b0d270605010918020f120a050d020706091d 66
    0x7251032001e09403641c0c0d242001181890f4428065003030f40d111103582d250140382c09407500c40c05034404401d061901004122030b481061070a617116038007400040c1c1d100c5501d40000c1c540c5000c1c012030a01580301040c09039040500030b40c03401e05084030300c110b045203a440c0c1c0200403001460303028240c0041c885038031480000d04240040d00c100301002c40041a02e401c070511b843c509020204041d5108075040408110640d0010b5880000000c458203c010729420041d1149104001400d0800722000a91901526080d600d401e01e0343c03158801814862424a4101b1020007175500c41014803403ca009204001a003080030305074100c1d06814851410501d400341044001c0c1107910b5204002d07c2035075411405a940b550140c10b040d4070481d0006125414600004120307000e110f8140141e005140102e40584e40c1c1d0109021618000c44078052075068515000307040204082d0b008000380308000450384015000720340802602c505030b035091b60701640d07013600b01c04580a021080001b400c240c0040381245040d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 420676097 1250 420674847 420674873
    0x3061a090612100803070c0303320f1e030a0c02030a08070e060c060717010504020a080a05070908070306020c0606010305011d0402210a020f010f08150409020d0303091b080703 77
    0x540690a160b44d50200f0781103604c803c00c200c8408410310014070405070000003e200242e03a18018552880d440012564858805e8403151020301c000f040c1040070b00b204104031002003440101d4843c001604400145040d0403d4400b024040e052101d0401c02610000c00e880c42c00c001507680b02041d8036030100a6401d02415841a90050010040c0c05030350071040201d103003e0310300c40d40e6800005a040e4455481084107030002c81c0f041e03004126080400c3c0e4000c90a0350400141c07a40060a074460301c00540f004849503024000b1401800710000c00d200007540600310004003102510b04c079584036001101103420074003600c0305001096400b0100d075117608505991048c40030b80800d80c0e0280d0404202e01100d080032610384c441d44040c038500b08504120070554007003002800d0218000080f04400307040400020700c1e02c10280c1400030004081d65035500b20b0f20506802601e001d0040d00b06042c0103003c0c214000051b2400480c86500d1703d18903002c0304c89081143d007041c018141090a41d902c007201e1200c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 420677347 1250 420676097 420676111
    0x13082e05100308030702060708060105090123040812030a1104030b0109021804021b10060e061207030f08030717041205090a0305061501110105010b0307030b0102160603061a090612 79
    0xc05200440003d000c48010750158001d50014403040c540150010f00c80741005201604001c002e00540480366041019002c5c4461900c4950804190f208885031140c0901e51240355a0306c14800c04441a4500500460180a10550600130034512a0002c8082c2c400c030311005002d860250010000c421441d4054904a1041840f40090907a421700242c240d801080000a20042202d4a850710040c100b2203041e00000240e400c2c0211072503e024410b80c0d030360050070710f4040d03541103140311980a400c0c0940005142d20021440039400f0508051000350811511807002c1076417454541416200444543e12a65101007201e10030f03040218200c0d441d40040e0642604403200e1200800024018002a849800810480c0d101e1400300c6000500030b91003007449036080c1c1d244c00014412420f02c14222540a140c60401003041d400303400040385040a1510a5041d46003080c0d07000c114a5030541020044038903004d070038038900e04940006130441c030079100c955078441000c04c4100da0040310220b000b035110712 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 420678597 1250 420677347 420677371
    0x4050a031106070c09050106020c010c020f0405070903060204030c06080601020f060c0904020f0309100c051821010c0908010c020f0613020301060b0a080403180503030706050a1113082e05 82
    0x201650304c90a0460180d00564600c98845005110a55040040d00050070303003460000044880358010a200241044400340110f1b00c3e18000f0300154080c1c1c40c00c1e40103540c40b01e03003190b03102c0da203040540c1600d050f4010f41c000201c8000100c8e20759031000071082500b01c1b0b003401810451f1140980003141d58010700c1c0c100d4000c0d8003807142c14000c4060002440c4a600c07450003410310240c2c0585058200d030351503c250010700c841440603c05148480e64040c00340c02c4140e0b0070040c40071000400c003110b413001441c42a0b9660a0405101c0b200f0743c402c00071000c4a0040e0001c2c040d2220780c0d2402e0f40c40da070508094080c0c82c2d014a0004916000c5a0310042c60a4009000095207170b88441d0b80305540e501c000c02c5403002c80c40a000703203c01c040c0d021804507403c43c40200c01111090616000035164030420802611640c1c69002280341e4241a074414030641d00c001840b65a00c0202c00b44010714a51305104401550241c0400e910420000d41c00044070000c0d1507285808420481c11103400510001e80380f072031004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 420679847 1250 420678597 420678607
    0x509010b0303070c051c0b0705070203191209050102011a06072a0303090806010509010504020304051018050105011a03180109050714040c090605190e0306070801080607030204050a031106 82
    0x601c09000a061107070240000d409040c0c240070600412916040d42004181040420f11011501b4102c05076004030903842d01e242ea4605030300000e40380c40e511640640700307421001d841004000b502c54645030000016122000b14a0341e82c401a401c0310394280b01d0040756608018450704502d070500c010400103100d456100d54003500e000e00d21122005112044885854580007071050503000400c0b80010140c0c60002d20300c0358180400f0072840401840348030b00072600030021608201052104200c812070784541041250011761202c01810600351094620354600702c0081055124070310100e203a0542c000c8100e00d9070720340035030030914500303428855401c555880844500203042071001000800500d402d104001e08003100b0081101d0f00402224148a030300f000800602c0e030020b0070f0302c42c40950000e034500b0b0820b0304101a03421207013415845916006036410003070442d4001c28070506840c0b00800711500c654400405508912030360040380ea20070500e80341080042e0303046030000504c4001a01040c101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 420681097 1250 420679847 420679849
    0xa0911010804201503091e01060803090d0303021b0d1704050a110612150f04020712050f0418090c08070b03040204110f070c05090604180803181e01110a02030d0509010b 74
    0x3034000340c86d88040c581290105407007201816101d0811410400004c210742864840c29030380e648144052103015007070898010b020305000e6410303160001c2500150301d1101002c00c2c07549803503d61010401d004605401e212710340004208000910484d4420300900c0d03094030300d07102c181c3d0302006e08d01581c1e0b011404004074150200302841c2d5a004109003404202521801c0d010800c07202d40b10300300315015600c1070059030f000c00d03d111074400c60748005040450fa43c1a0a007419020b5101e0f6800c048151081058144400c0d1b459610100440d4000d0a41e69010381e01d0304101510780b500c40c4250b50720001c0c00d101140140c9010703801460740304145d4504500d4444605645020364002d140280c0300d1000c40f0404100905100701680e5001000b01e504000380b0140b03070310314421501ea41002a140348004070018040110124001105d890110200c40e4695458040c1c24044c4440700c1c80854a03500304018000360101e12400d43e242d0b540d4070f0300990f0a0a10f0015080e0051100030105000d641d207519a0a81c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 420682347 1250 420681097 420681139
    0x5190302070f031505040813060801150f0503071d1005040e090304060525061406180705040b0c0c060318070b04052b0212032a0a08070c0e0a091101080420 68
    0x44c40561a2b282140d0f00d0251140e0007111000d2410051060f480585090164080e048907400b141504011f8000391580c03003003c0b400300b640d424070741e0410110a42c0c0b0035005c0c0c200018104552008607240f226503654020207441c0d000d1485940c0200c7d80910180c11081906c1d41c03442d0340710364061140301441c150780d10b80c1710a40d0100381d0f2041340c400d500e10500801d8100100000d00500300410740c9034a6040400004015218074424181c207088c02060310481160103008840312650001d05c0300741c890500400c008018a071541418400d07100703440d40091041d41080a4408a0f07030028100500300c50480300741007942c08910002141c0b0420031130001e00680c1c40400035151104200020754950009205401000103004c0d80c00b42d14000100e606030110400003011150280d009080c26210900c41c58903800b0450140c00c0402220701500400203186c450346d0201041c18010480364060640742d00043d1215002514040c2441101000c0030464005000060442c04406407402086865168030459 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 420683453 1106 420682347 420682349
    0xc090b0c0114090105010503070e0c0702130905060c0c070618031220030702010f0e0906090903070b0a0207050c030303130b060a0305190302070f031505040813 70
    0x58000e401a0356551581000c650003803d280d01040d000e01401d015144c0244149940003480340035000c00c0600030183c20124030b06d0450542c00740158072201c2988200c203151a1400400010010401c2602c10481480c0303d070307240c15080d510070341012074944c0700d081002a84890220120300c01d040103011240e01000c1c1ca0301c482c0c1001c1b03007a1b401c003c0020842100800b2015041e480500120044c079806200342c0c2c03414042c0e50300c1d03602540d00d409400501a000700c00c41c40000d9550a15500340d1390040da115044074104516661340c510b5414040303c1122440390042030980801004204000501f10120061811890440303200e1160032241c1802804030900130000c07402a8803221511800f664000065800099014020540346041244100c00501c00c030203001903441e0b03090b0414402c1d04d51159108040076441d2007410084d01000e4001e031404402080803008a45c2c0a41030b01d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 420503597 420683453 := by
  have h0 := BRFrame.cov_init 420503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 420503597 ≤ n) (h2 : n < 420683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
