-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2820
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:50:06.689788+00:00
-- url     : https://prove2.me/submissions/3e74b888-ff05-443a-ba58-532edfb89b6f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 507014388 ≤ n < 507194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 507015638 1250 507014388 507014401
    0x31a0901030c180207080706020702032509050a061410090f090912020c090604021b03161b0612050402030a061a01030c0318031b0f08030f01080f120f0c06 68
    0x259108243c034a81554900c01244501c0400c3c2a40305001d0700606200c0c2c213000280010368940c014218440c402815102c411140b03000b0140346d140d42021103281d541c040c04041198242520543c0e03007040001100740441d40c141f010181c4a2038860400c60301440c5140e020080c040d22412040c40a4400900d0000460f581c40b07203142e020b030200907010303542ca02c1504d0441400c18000503400000c8440580281c00c66035819041000039000380045860503440003504400d9240c0c01d00003481052509040030040c0c481350b00707249914151100c6400f00305070050005000990b0441c41c5100c0e501d80005011889603198400300e400c0941c0c03013100620716414603801c201120310315503140c120b0b40f034203a90410440a20711012025184901c40d0341c03811007512002800800c1c4a407526412071180380150300410000c41e0b0310603010050740744041ea50b208000c000d00c446e46400351280c90041c007480d402803148280038450161680801000c0c900380c100006a564407004d28031051b1042050302e481918198605171 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 507016888 1250 507015638 507015653
    0x20a02031309140114060c0f0604052802040c09051003060911090f150408030a09231305090c18090c1912061503030216150f031a090103 60
    0x1501103215100740a9404218800c9901c2495040000c0801180380c42c3d00e000781c0d9032003094402d0100340e00144c0801c030003400c5100c20041924001e004400402c1503280908005081054004a0110b1540c5005d0140d164806a6010320f2030a50100c1c2d00042c0440d50180c10f50348107206900c0740d5004094000840e525640540c0020100c5403c80360911501c0c00821606041303104640400d50700c00614914144181850904012981840207480b46815245d0402c03610316040070003031000140700342c6404d03c20005001e861740540d0100d101e4a109100003030b0700158032040810240301c40c5076903880c0020700d030001c01c10072420680b1020f4500102000780b10b01c1d107207281204450074415407052007a03112943c180350b1444c031045410700f22203200c1d181c20690b50031022040340000b910115141c0c81c040040d2012815041e008510035001003411501d445850004024036030702038401c038214014050b003102d4020100b40f850034211b280010300e0f11000d0040e5a61a00a10506608082110008020001c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 507018138 1250 507016888 507016897
    0x1031212110306030105010807050d0f082101090f052503270606051c02011202040e160e01030c021b060714070806100b0405041122300803070c06020a0203 68
    0x10b50080c0060b0f038948046076502c4c800ad00c40c60760000880320b00d075030208081503003a880c01480342440c6d07850300d0100b540108640c090b01c00c100072100401c000421840040c0c3c4240c09002c0c0400d00248024075202d0040441014551401160fa004011007884a5031181e80580c00482004000078114151040303074145180300d0380c00445001c2d00e022804236141c50008403806521010b000200e107103504030307801140d41d848201d02546410b6004d001c04a2a5070714002002e10440341d90640810b11180d600000703203411b10148480741454030b00000c580e0741c29400b0940f20710410705d80302c1d0342110a2040000c202c0754800c443c2e0180009100300c1100300c3c10340c4040f4110040300d007401e0440b45603844030100e000c202d6416104074040c12100f00070800050400360000c910b8140c241900e141010940084881c041e41d11105500704900b807120280408000c9208804e8481e0b0b032074a403d141900d4002070514003544c03688014003506000700000b04850320400ca001e003045d40c0709070b055482d50070032080650f40e5080b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 507019388 1250 507018138 507018151
    0x150a1e05030a1104092414060123030c0d05040b0405060702030a0801030b0a0e0d0e0a120b0609060609030a050c1302070308130c0f0303050913050c03010312121103 72
    0x91140000e52031400041c2103260b6070300b01880724107100c090410080181200007044411074101013010038401500300c00c4414010000c48081101600c80641c04c001c1107005103c2c1e0305000004040c045c011815007400e12180c1352030201c65580f81c0360035080040c1801102030042c08582054200420401c00403000340c0203900c644107c689980360301900740e03100d020b455188030004898900410204601c3d02e18150000c02641000611000c004030060034012513610803008580f80760150f80590801c00d1007400240320794040075000e080c0a60301e54004a40282c0401d12131800c0c280410003550b0360b0003c60300b04207030042c22111003481c10302c0d003991030380c4c03210807501d00c10108035019000d003820b40c0c000c5610095159452079410341c0c40e8001103001003903d842c180c030303954040b14002c40d0010034812900b01031800394484603290741d8454104030440c41c5072140204d01c6401c007024001208422000d59041d680c1c001c0e9505002c0146550888042d4404a0090fa400d0b0421128200d00e01110000318090503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 507020638 1250 507019388 507019439
    0x1c090b19030e07080d20010603020d1b0b0721020106270b210106090b01050a08070c060606050c0f070b07080a1b06050609150906010c150507021e0705060f03150a 71
    0x1e146c0c10f44c0d080764194030029402c44081300498001800c183c048031814404207603103503041a01c5550910b00760700003420459520600702c030828074504034050f0407091800c25100a000d1035081032075a45516003903101c4a00307003201d420201c42d100c42264001c0714031898041d1060f07014a0030007059092148014403003804039481c008000c1030b0440503000703040c0740100c1a19210700c3d000a041c012107461382c00030076000410105554402c0050846c1c001c0c0401000709665081c0c480280c54807031400c2020341ca00b14502ca0f40305c405d08000c0c10b040e5400b941c5145400440030740c3c40e0a500c290640d06150650500d1140c900c1080c0701740108411f40e8401030043d101601d42d610b107036803011540003440300740c100d0081e405240e03a000a59250f100344d15040c003052099a0701109469822162000d03508140c2d00400560440960200f0143d0a6194280d0081016000300b640620740000b2400c64414541d000e190b030f800010005030000814120084074540180204103855603c51090055200000400480c50b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 507021888 1250 507020638 507020687
    0xe04052a06070542241f050d0c0207051302090d0602131409060a0504050717010e070f020307150c050909040b061e0102120d0605031c090b19030e07080d 67
    0xc00c804807900d4413400c0581c910104444050305002040c4c8113001945511059203008000c15041080d15000701203007a444e8191075030803023a449010303220390b608a4030443d0b00c402da08100c1569454080c09912800810040c2d0383d5001d0000314003020441900508400e00000d0340184102d10806842d0880380b03d00c824403c501d03122001c00520100683e14250710441c01403040c4030303d10f00b6910694028403241481518809158a402441320f026403001c507000b102902000f080a4020418941701d00091014500c0d02e1802d5076520309800140c0c0740c03220030070380e1075801046080c014001c80b4110400240f140d40545821b1405500140301142e155010741032524411112480c2c42019407005081600075000c0c1142c1c1c0c1b81d0100b00d036044101c0365000c45485050002c0d85890034404c08042e150003440500461042d448064491102e903440058000c008211103800b112100004c008000802c0c540441c6594505440d44d2502d40c96800021160155084101105401c0a0b00d1602c1c00d43d8004c900404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 507023138 1250 507021888 507022003
    0xc0308060607080d0509070504060902180d030c060b0a05150901110f151509190e0703020901210506090d0905120604032303010e04052a060705 63
    0x307004411000f090b001c414030800310f10346a02d0700560340c031211000c102e4132080c3c1e90385e000a040e510241d200080d502c0c0d00103030305602081001c1c41000d8601c8140c07158901090301d0364008046400d1000040c0c0b44540e9900441040e5641803e101c0c01810010b0843e41e4800e8600c0045805502008003540443c0c00c1e52112501c148000c104000a450380c1005031046442058101c4048a80188058680d0000415044c4540e40f007048150191050740301408030030300c030401c1850840754590360004242d80500f20400041ea41e01d143e132415a8418100d500100605030002c8031b20280184c0014a203008030010032002c0000098201030903c8140e40b036000d075603500d1080c0000c808030500c01082c503800140c001008a4011050004c101c900c200134422445022200302c0303003a40003a04419448543c08043c0010303c001009903801c50f031000e5402000480c00e140c05180032804070320f105805800041074403004d00c4014002191000c500b8201900c90146114081c0072060501040304032456400b802c240300e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 507024388 1250 507023138 507023149
    0x80a021c030219020a050714060409090308010e100509041e21021621051c0309230d20011503030201050906010602370605040c050f1507140a030c030806 67
    0x1109030000040c10050713040c02300d0149894280300e1101c3e00110304020002d41e0380d02d544624981c41c1d001c0c0d0703510145c0b54142041426880800360101c0701c8a20505c00610650355056160380c1c003d41d000300241882207000f101d000c4900300005019128036003031100b005c1002580280452401640c0d0309480c10764040441c40028a0791600500c03140c08014400341c41c0725000c1034240c01c56103006400f21403038500681e001400040010840400181e2240044030402125480d03000d1a5100e00701840101e000a1010039540c81010707003000200800c080c0d00c2c2c8a4a02001003021241d10740c41c00a100d60f0050710098580701040d844120010341c1b8000008948000120b400f0f410f9412a50151202c00861000d1a20300031055414001d0040044450445004010103215116107e8503005c9018030f01400c051444104950201c0c1c0108a2082e4030b0b69555200544943c2d46405608070b6616200c05043c2984158480800b10301a48a9450150289038105494000c0e4910030b5031020000c1d1b881005121 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 507025638 1250 507024388 507024403
    0x20a210c06050c0312071b0312051e1306060b070305072003120913020408010b040b0301020c070b03090f0321070318060e0111040b0901030f0612080a021c03021902 72
    0xb0f600e410610403100c408203038039032094001580303191114400d80c107031200219941c9100c0c001c5000c00c9068642c40200140c1c1d0050b5130340a59149140d1031040b959040d0079003a6480207012000300306080c000300c020010b03e54031020186c80b40c1c00d2580d071141414a0081c0c1913510450003603030b400300c6018850b1044207040910702c030680400380103050841c108041651540c0c12454820358005207414a50541e50064806000104008000442e0500025080c04200c459446405000c0d9004008400780c840307001410804441c0c03e1600190b5a03a58100c0040c104a0040d025070054040000c60314030100d0b0800325488440318206914400341c4407280c2c1a000c0380c040300384c0f85040c010090114070102d04241d000554000c8008008240721985401202d440d03802500802d00e4400041640030465925100300a01141841001c0001e1402d03c10f6136812142c0a2200401d080d030002840c0400303d04c203210804001c401007070042d00300c0000c404003030084d4000507010140b400518106c603190a10024110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 507026888 1250 507025638 507025657
    0xe0103121407020d0f14010c081909021302071505012103020c09010f1707080a02040e030d060b04141012020c0a1a01060912030e0d020a210c0605 64
    0x12400d040859500755036228000142003103031a000d00c0100c025860b4000e01200140c4900240141c148031441d04202c00700c168000f182c0b541e03260407184041c81c0d0b0000220f5411a2159460b2421a40c4e042c2c0544060122034500a4110588019503802c034803968000e419928440c001494080c0310340541385085030802d1103240c481085140c5c0f000c040c107400d624509461406441a01c60f1280c01c034000ca04868400c0e80902c1000c048490304004e808401040b02039802501b0b005001c81601c0c0ca040540d640c2c0d20407401900c516502c508d281000c100400444220646600c3c06100070b90b561840c035030b401c1e00140f0680c02c17100000c0c0c008502d146040030344034082a5168035403000854000a903c2c0082d0485c05100006100342500907000c990700b4084850800c1c0d40d1822120b140d07040110040c10311b00035602c090098200f900d0390100107a08440a9041d00c5001d681041d05a0114000607021841d158402c07070702464644107a80c000e4940a1401c40501e000b5803080002c0c2d0b0340c82c00c0031100c1d0320840890 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 507028138 1250 507026888 507026903
    0x30a0c0303030c110d091e0e011a120c0301053105040212071205010e0c011e031401080a020f240c010e0111070309050109030c0308090a0801020c0d08010e0103 70
    0x50000038041c0c0d0040340c00701854641088241c8020322010315010340317a0040c0e004a246400c080000004403400211403030840481e00c3c005a2134202001c0c0d860300c06000d1f2882ca40d020041c503201a00400b0280c691101040381d80380603600305110208890750007802814081d01c4040c60200041801c00400c2c190300301d44a00c21141040401e0f0310800a090107030089900c5a0f50250700d04080d03c0400040307000e4040c111241108a06529003142120004600d1454a030003c0b09441c0a40e81c001807840c030302c580c580000512500c0d0b040411002000c85010381080b0510110000c541c3c01d00010300f414400c0e02c00d80380005808544020086610001d070008040f00911107100700d49060f1103006001e9942c0d1500c00442d000c42c41c1d14030503080d210314850700035a00700080341d9941810752000740c01e00100800c1c201001014150385800900f82c00710301020f441c0703403000170304170030b03261510303005e28005080001c02152140724a0713a069440d500780100640c0050510000070030010680c195441c101d0f5440181c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 507029388 1250 507028138 507028163
    0x4050d08101203020a080c1005061c12020a02091501030c11060c070201030902090708100e130b130b160f03110904050907090608060105040f0c020d0324150806030a 72
    0x10b611a908600701000c40440c040c12a6010000c1c0b141c0f000f8110003601d400190141890807030701e10040700c0e80201301320b100c0c441358150504034648922051303820640101260300040d01d8024280e00d0130502110007908180204204807100c100349025421900e401d980500030b044120604603000c04100050306215000759020451081240d80145038141c811304002c6900310285c0c00140e5000c404036a41c2001c6031803030003004105103502522201030290401d0340302203410054912030440d40706040042c80110000040303546502c5915281045a07070184032507000c0c0c5070191003ea442800340d809240406c254210381e0184c40c5c041d003c0c034007100310241c514600304800001000050b0002504e188124018064041881c1d111801044007a2550400601b01545858280402c580b4411208801d0601d40000301c4d151a0f0301160b40b0310307a103100345404a10110302450940f01d0300341940f2420319146200c140012900d224643e0303000d451020ba1583d55540d507030081417645035805914010718040c107202 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 507030638 1250 507029388 507029399
    0xe03031e060111070902030601141306080c09030f1b04060317132c010e07051204020a17010617071d13080403050f011a06090108060d1a04050d0810 65
    0x3041a41c0c81001458455a40d59540c2a12414803880e80c12208074290004200100d95800001420011040c01d041616003d101e8103541402807590203503d08100d0341c500803070043d809110980704000b00c01401d03503800302c1e52a00219500d0390480c4942c3c401e5010b422218656252610034442229049900d080e004480044401c1080e4000a000da0b0003904007480401d152a81d41081c130700c07020031078405404104680ba640c1c0c042110503802488903e000c01e04020680d54008103075030011000a039000400c1d00e070341c4001001e00140340c00000c109007501c0710049482ca015003000007200d0075040d0840704159844d140d80d8407001140103004100b01400c3e2800210204601b490350301603070000300b0311151503441c0e45240d0f95034031a0340140d0b4240d0241d070304911040000e10410384484404a401c450010201c0013040150141c1d18030203060110720400aa0251603038002c1d03910140d8422402021801c1c80b81c030207582c0160503503050741e0b188144141c80002a00889400c0d00032003a81c0c4010304542c0c50710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 507031888 1250 507030638 507030691
    0x509011203080c0f0a0c0c091419020a1d01090305100204030b0f010b09120a0f1a24042304050114010812031305030712091404020711010302070206121003060e0303 72
    0x4201203800010006c0e00003104030316172042000c2741c02803001d048650709011842108032010070f022814260301c10440001d5a5410007140600a81c20a6542c0045c02d01200184c41082d031540c40a0078a000e400c80050624902e42e005100303492091400500e19100c1044291808400b4000c07c00d41c100200005a0740b0304d00030300305100c052140b404440d84c402c2c480ea500590108540f1040707401c41b081958894286120006656101c882110040c0c0344215a8000c480320340301d1000004d000c0c0f41d5610600025406060381144d4007103030101c000005091602c0c21078024030144603980d044402500000c16040c2c0e000c80e46065404401c1c05c90b50941e00c03041100604500c0e4100102c4161204000000c0020031307880b072100b10012591a2a00fa4610788182408080016000248200c1c410421100010341c2c0000340f6007108000e20300181c9410541c03010600354441e030b594441c481c01c903074000c11900f000c0380705034003040c2e9200741030a21032443d06829055076030000380e071050b0120342191401b24104481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 507033138 1250 507031888 507031907
    0x702030a02190b0703050307200604032001050c2d0301090507121a12030a05120a1107060c020106050a080a0620130305070b04060801090905070509011203080c0f0a 72
    0x110b0b460601c00b03998030141d60f600c0e40205022408190040100b1030895000031300781d001c5100582e1650604502c0c544402c2d100c0c03100810040c00d208550f80d43c1c41194500d9600a01020440c0d8002c020a0070941d0019070313660460045200d1040d4005419544809116180e60405c1000b5500034116400d140e20b0340c4c080e1000624007000c10644034240021440c40c1c1c011440001c09101c003000b84442c1240912080900b22400920349502c20089280c039142c0c001e080307801078103c00c911185140c66099444003d000741c0503083d41d0488001c200701003405074683c0b044c2103411141d0000c1101c196206e0600c1016004c505c58419140c0103d003e40000c2200b6400840440c000540b012030405104881e0b0441c036048046601020311000c07000b801044410040b04000d00300704000b4504040c90070304001c00802050003a00300e081d480740a4141080b01c10071a0202400d0001c0c0320035403039a16114000300d586c002c4441070b00099500004200b030303940808220b501da902da121400d4581400c03500c1c16281c9005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 507034388 1250 507033138 507033169
    0x30307050d02090d03050903060624030a0e120307080106021c1d1903020a08033103080703031e06060f0e0609030a060603030206150f0f03031b0d090b0702030a02 71
    0x10204004903d03a40c07505281c2044621035185c1d55151004007050614000c8020302c1d460003600b96600400520f04190020440c0c3c01d4000c600b65034a40d5001d10f210041c10040c04001c0144c8031790500f20010640e504051840b0b0501c0e032340d0b0b141c1c05a9881030101c0e603a4030740b120b0804120f60388d010801d44d0144500d03120f540900400301602034045c650b00210300c640ca9244030001604100b000144114540354004070b0040421400a43c2403101e00d65070740c03044031139200f031002079030b900c040718980a00c1d01030050000854008100a4441ca802c2c18081c010b4985a541040c44807240d00c1400700204140c810901582c000d030b0b540701c9505641030001d4a0311008811030381c0d032150b4148022299a0f500300510240705101c2c1101040300c2e0701d9854081d15040700502404a210040f0520802d99140e10210b40b5401e0403c880e48002800244082400c0d4400d03d49807001000b40da00ea01c580640e00010b142c204ca803200e5840010480d0303215680c50150069400c020f5043d0080810703000540344c95100407181e00d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 507035638 1250 507034388 507034391
    0x1b030f050d02161b0e01030b160c05060f070806010c05071419090e1912080c0c0f01060e0a060305060a0b030c0303031906050f06031603180308040c0611030307050d 72
    0xca00192140081a110b0044840c1341128054108003100c001d006001000d00311410b03102c5505540d03601d642c00d18010300c00188d0a400310250103405220752101c1400c96000f42c1a282c05080c101207403010b04904443c404045a6204042006540300d040c0d0480c080d81c110001d403000c50300302244c8078003102d0909a4507070b2101c82e61074110820031143c0c586000030440d4280004208204401050130041c00300603510128411780d01400215043d402c12220103c010310380640c0550340e208901c4081d008a101e41d494900c14019503580d982d01c154007900503280c00700c0c42d8a416a58004a4200f42d0f8103e020003804c0e0b8101001241c19403801da00010060103004003540d0b0400c0404000c01d01d1604100d5800388c9007900d0550040203180b1501c100d001805003130743c040e581600b808022450511015011202c62521914240481840f99000241d01c000054040ba0320f8186411300906144003074030143d50800141800003401400744424030590340240e0080c50440c0e407107410980755900000d2400308450b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 507036888 1250 507035638 507035647
    0x2010c020f1002030d05011e090507020109061d0f010e030702090c0409090305120a06030f08090a09020406030b0411030106140714100903120c1b020a0e161b030f050d02 74
    0xe0b6144040580450050780c021038403103103104000b00c00d461040e4030010902c100c0903408e150a05400310307148152070501c40301266507295450202e00500d6511030148c100c4c5e203001002142d01070490540020303805d16908030382643c1c5000890300e00300c808591000110f613104000d0000142404e411745503022021001d01400c00341c0d155174200c161500a1403c40000c1c100060121110340c030502019040a10304002300407540c05c683e600c5c04652102e140c0506080c10201354605560b8580c0081c00280040910941d182e554580002c0c0207002c100c88a140b01d10705084c40015030045000959040f07622580d6550300c210f10079013411030300790300c1448140c90420054400b001400d10800050344035075426400011601072a007801400c2822072000050094100300500a01e29403140012004042940000c0d10601c01480060540c07800350f402403a0300201a401c0100444034070340707043c640c0401c41e180c2081002c0004c0c083c640021109400501040c080300c40905a03611650203041207802c0c420340103240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 507038138 1250 507036888 507036919
    0x50408060f010303110a0203030d020d150303031505010302160f03020f0a0c05090106051804020d0e010501090902120703030f0c0201121404170a08011202010504030c060c05011103070c02010c02 85
    0x1421400c403440c401c58500c0c440100101503100c0d610000d00160b07100503141d1001a9400261207201d50070541d0040c5e50089130018941d0015400070f884030301084890401d451766803030f002d005000303d80c0c10b1400360b1560740000561540280202e81ca200d41905000d45a48510740d510800d4646c6608298110301c1414000b030b000c04410402d403d440b900848410700c0440c40c007002c0104811050b0004004c106042c0100a0a0080c0980c40020b840c003c440c0961203515040040d402002c0d142a01861582040700000340100c4560213080c4042c000d43d00c060415191404d405c0d41d401e104c0c400100025000c8040c02d402611440c01120303080e205141c00810b0800e403c03030603002c2e01d41c0d004500ca9824141400d00c010001441c40e8003000c0912a03500300d04001040001821040c41403141001198240c00c480c403c5a2140003141c0c0a154012014000c1540350301d0001c00c43c0443c0c0d50101e50070344c644498110f02e43c1040c0e0527244114280e68a80540c083c056004403440d24448008a82143c00320106071034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 507039388 1250 507038138 507038143
    0x9170105070929210c030a2a08070e100806030606010f0503041506031a0f060f0a06180b13090609091101030906110c014a16090b011d091303050408 65
    0x41d17003800100305c1d240c0c2810f2008404036481302c0758580950010000b40740c2641100502c002c40c47c82c0900b0040340c03907030342e518041d966140800c0030158480e00856030309032500c0c2c110040c14005d410640886049a82c4e010064923000c00685024010400c01d00014000505803050710112205081c07010421a9695070390340e2010b010500340c12214114801001400c180c100c480580c000001c50b00351030034118003001704100d012180600710400907040321605010301c40003a400300a0065032800c9a6502d42811443c820300900d01480030b541e41000400149003005001d4580c0194000480581c2d08680b01d0041d070040c00324003030480d071207600d80001c0600303103100501614000d01084004100c41104001c070020034040c0e000b05a03141d000422240458100c169802c000e0b04241446a0150b071000c034880c01d241c14128032407103142e40c1c10305c0310214240c0ca80740c02c064000074081c1c8a12149912180e801e400304548604016003050301400007a190a09499290300090300900b002841c00da11044000d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 507040638 1250 507039388 507039391
    0xb0a02120f04080a08070510051b180a0e010602060702160e0a090b0a02030129040b03041a0924060d03032301090203090f0d05030c0a0917010507092921 67
    0x303174044400b141204c1401000e01019441c905009001c010718981842c2e0341101070390030b0020140801c80402c56040702c40c10955540031903d001400c1c080110355500411142c1c0e6003d00030080180100c0020491181c0005034401444035410901800c0c3e80c109056840107910080c0304416407920f5014160204851a8200380074100c40c0c40090f0b03480d070511200440b442c030b62482d01d0111001c0449120040c17448402503a0654091241003030740c82d1900c0c10200000780d110040c02d40e12032508418005810f0380050907040c4070007020b00d4030300e0030061031449801201040310003c0e0017160195400740000c0c4254407a01a0010640302c2d010b242c1e0405410880e6007409822040d60103038000140845002e04124801c03285441400030941142d03054402026804058548030f1000d40101d40722030032a0141030100042c00251100101880004540b50b000e0f05d01504c001001c9a4829004141d51291103000000c080031480b40b001400040354001040e5403040e817501c040704540f013001505c00180260500e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 507041888 1250 507040638 507040643
    0x18041106070f0606170d0813170c070e0705160b0c0415030b03010b0301050106090b03091c02010219020c0f010818250b12040609020f03120403030206010b0a02120f04080a 75
    0x50a2170410482c15015164860400240c0e40700702170421020394054000c55100c0d55440c0740c5003001400c0d180c20205a6000070480b44201c0011860364209540054041c08454048080e20056114002c2c03e881c148914680003035603c0344c0b41d40540125000d04201608a161154402d00d0950388000801019145015a2000176200c1d061000300e487c0074068190320700d804500030061540b5080300900440100d12034500040c1d404400601804402d10022311100c1a030061110b03c86001c06000b0b00075406101146039400e005202c45101a100042056182101400d510202e114900040d1040103004100020140c42c030580034080040603c0103400070030340510400d8000c8269240001c007074040d50406840c4410500c83c4240c1c440b20414541c0c3c01c250010000a000318075400800d550100c441c40503500341c45041240e000003010140203000701c902036400c1d5802d50b6200c0e4001c0e0618492003000900680c080c2c1c414800c0c42009000608074020303c2c0360010310700b1380d4440e200c50070007120a006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 507043138 1250 507041888 507041891
    0xc14181303080c131809050a030504180e030906070f0203010e0f060f06032109150327030a05160b070f030b0108062b1a1518041106070f06 61
    0x1003804160304201c20036042031020b580c071400c000040300a20030100d40ca2040301e848610410314a0029095135024545035908841910302c95003980c20090050b6200d0710800040790980c04003403404107450b12400f841401290041d629184e2420108850f83e008000c0c00d071030158842403c90300580c1c1c24444c032091480400c0c0a00000158800c1745804c1206c005c0441140050003010007407144c3e00482c0c9500402e15001d9480c00e005044c01d0020035a0050380e04040d00300000d031182e52001d00444010310702c02e90f81c0103000c02c00225140702c810112040e404002045030720502c02a5007460161001d0a1900b41c05001043c00c140c0540751002c1140040d9042004035503281040c1c611103074140528140c466003030070004024248500410040d481c030000f45c1c2c0c8601510762014410030300034030141d200290003031603058401c00b0541d80e81000001c151842d6801c01003244502c13115013031480544070170000340441c4114603581ca44a280039088411a4284c3c0000c0401010b0002103c015a20302d0301d5026050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 507044388 1250 507043138 507043171
    0xb10080a0c0608061009060807111e0d0e03030706020918010915150e15040906060e0f0301091e0303090204090b040b0705041511030d020f0c0610030c1418 68
    0x30054281000030380362034010300c00c5d04216600150000d0025080319500c0c80c060003540c1e40d404080f03841c00a0081c401626000b2801515515454a1070082040e9a0031050b035040c000c4001c0c043d2410903221894503007640091180d100070402550240a41c110050191804003d1142d07062640c04000d0700404600c6594030a0491a0325020768800c01074a4494108010300040c550054008419249103a04c074425407003c401d5a44190b07020b840040540f01e0043c00f40c50707214803020b81006400c02d610b502900d010304004030300b40380500800d81d1003600000016034010070740160f65512010414140d05254440c1024401601c0320300c281c2126600908542000d42414580100c490002a062108010050105100050181c402c20307400c0d4000d400c00340c01921031642214250f0182240a40e0668404500d140104803a2002001c14048080a40e05680d442c50498410301030540070142c0000113070740080c0007400344a0301c5040c0549004140401e20440340f2082e51101404542c4029002139002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 507045638 1250 507044388 507044399
    0x3010b10051c362909061b0f2b0b010e030d05070317010902030103140106060906031a04360543060e1008040b10080a0c 53
    0x40a038500b0082075181885801040a050542010051071030003c10000303060359000c1c102c070f50034046403c81c0d1003050603442020044400740e071081c010342c01c01c0481240000103550341801040f40c43c0b0980d0b501c2140c1d4592850800c0341c1d80140c1051544042c4650b003007164030b08001d5442d191a00220005609844091500b20400162982c0798001070600c07041201ca01c450f41d40c041065032428001c1d01d021500c40c00b841c00c045078040341e540c40c034000c084c03000400416a54030980095060701d00910102c001c0003400141d01e400c8600d240305142c0018400201440340324840c1e0090401054040e150400c90280d00b0000340484e002344081c0131001402c0b002c0414030800401c00714146032202680141c0700034042c0c0342c1a480d079400d000e16401c0445e5500c4001c190483c01c0d038040d5510b44076800c000d007004000180c0680180030724010300700400d12200100a0a10f0850110031000c1156a03824400351221795881c02d4402010b8040c4100c030078014004503080300208110b18550307000d0000e4005141c60076 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 507046888 1250 507045638 507045667
    0x40b1206011103030601140904060b030405030c0616230c030d06050f100509190803030c03060a2106050c0f1303021008010b070305070f020a0603090b180d080603010b1005 75
    0x800048202ea00705004021441c1c0e0002c100060380d01301021101d1b641c01503100050001d02e4250400d0703140c12000b00610007030000010103000c41484010495043e62100000001c1c1040d04080303210002e07a01b00c81070214540d81d022044051412501500d050640581d0aa81150028800240502c1d070f02c1300c04208615051140c9100c4403815681c008007000b01407401031440c4203103001c15024408c0c150809906008121981c001000382c0c00c1a01c0e12420704d200d005406600c19a031480c4210401d2a0200e0481d4800e140c4444c400e49000b60f54440595680d1000c010748401003043c0140e51080c040c070380340c030002d10000740004503c4000142020b41941f040082c1450228840c20401c6612001030180d180e20714200c400154050038540d855251910b4004804902280020340240104034005134443e019080b140e02c00c0d114680c0b40b0455916000c050707049500b0030000100c10350009004c15655030240040075004840a00007288440d410800700b00044007802c400c40c0000d0000449820703c02e0304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 507048138 1250 507046888 507046907
    0x20d021204110127090b0d0204140f0105030601150e0a15200c0d0f11060f07020405090a080414121e07090905060a1805060702012004030c061103040b120601 69
    0x4102c042c2890b00004c1112480040e114002d10520704d584000380c0e65590388051040c80740b2680140203000e0300030011018407030480c090718451140791200c3c0c00403900b4680410881d040c3d0380039000c0d1304000044408121500c1e41450384d6650007039580340700410003006070140300c48042903d8560070b00317980c240188a0300000440c2c0e203040c4da5420000b071190095039508200043c1540081c4809d0681c222818071403d01203508003039591100c0002980001c00c1d03404005446076a000722001c0000b503650900a545458018000414160041000340204c1a01710344507141880094803680ca0114402c142d1841c021205592056078070a5130214108944100544401b62030321070024030140000340d80d5190755400190a840f0b030182c44a034662151710b00c061103411039a40010445503103061801d03004e4000d0000e2103414405840d99010b403009000b07080110303412a940b00300c4619410b40343c200f00711449491400c220303541b404100800240c00c92800090520701480c040c0780c4d61302e07081072000074000010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 507049388 1250 507048138 507048167
    0x130e0601061e0903110918010203100306050c030618090c0301020705010f0c0906020706080601030e0a060e0d05090604030b04080f031501090e010324060803180a120213020d0212041101 81
    0x40000f0148001402440740d800c0401003602e2149298030b480d042c0302007621001c0034400d00c80d0720201c100254041d281501700126402040104541d4403011280101e030700c000c441064011445030810844000c0104510303600000442c20b40300041080c3c0c00103400da900841083e9096919843c00040c0e01c205440380c0d540380300040c1004c0e06114030b080b2002c0c5d00c4004912949062100d00ca00240c00d0303901a42010306c1035104c9000b9034041205070302d0500002c00600001117038030310a244400360a58050411200742c440010803007400d16181d5900c1030314420700284100c4150b60300788100c48004600401841c01000c1a000e5942c4104110340010100519a84040f041e1010700300100086000300c07031400000044814803010100d800e00503200134001e2548804854032002800340c44500242c01344200042d01124aa5512a541d500d03c030030881103680080d600c0340c1d01c040482e203921480d034004c0000d546c940300054182424070b46401c45c8140111402d0340d242000714400f801560b4800d01035101082c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 507050638 1250 507049388 507049397
    0x140d15180e060a2a03140106030203060d1b0b040b0a1403040b13020f03060a0c0315031101080a150311030d2d090b031f0b18130e0601061e 61
    0x8600001d040d5442e100070344141001c42d03550403503800d11035001c41040c6040b10352019181c0d071002580001070081004090603d1011282400400c0301031081c02181e01492006080710404a680d480d1000d5400a0310105d910911008a00007080c140c040003410007400c840d4221030329003000060181005544003520300043c4c804100300070014214002c035a42000c0d50540450f00b884191000c2013010069103030080d4584a848100041550142c2108403072862544c0c007848000c045001a803003582c41400001d02e8440b014046d0f01301941702d9584254000b58150002c52400c4604140c80f0711064a034000390740c03240c0c075120006034a08080148400d40c0d106440c00d01000718215640141130303000e810613205042e00d41460700c00d455200b5002c50001e071101c5840da84e80c90900c5008060403030b86c200c1003251a0b00e8900030000d403a44816080e1246050200214000000b9050400011120400d80d401c5180c0d942c141035a041e6504210190181030f09864040d013440340a10007000824080400c0310800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 507051888 1250 507050638 507050651
    0x6130c0b1c090302010f050408130b1606020a05160507030309061809050c120115140c191e060f0e0c061b01140c040f170607140d1518 59
    0x15181d03040200a4401a000091051503a1070102d000d00000080500401c1c00c1809110a025001000701184441000307004005a901d41c20302605010b060300281140c020300b0411400b0800a40080c6240e0b984d0349402460483d0b00c880c41071800c2084c48003652641d1080900b8801c1542200038440641140d06100c115a18921503e141051032030081c0005180c40e840410300117a05881511600d114403825040a0b40c0c4482030052000c28500050f0b00040f04e0080400d203180c20300c0c0407900426040c01c007a007800e40d83c1400790711140b102400120f81615981e10a0030080c01ca4074640c1800c43c1c407503c004201e412100302c0c40c42c20394005800000168004c054006103d5541ea8100c65148004417000c032100354001d02540d004280640304c4040905c906000c1208102100f1700800c141e405412001c81b4075a00d5030448090b2034440c58001c11540d0208003ca210680100071002104203010142e5140402c0d050401c4140e80c0c0c000c0b11041440c035040824817a041304190140401070342044208040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 507053138 1250 507051888 507051907
    0x702210304110d020d03033b1506010207030b040201120504050309010f031803080c04080601060906030c02070f26101a04051303050c01022104030806012115050306130c0b 75
    0x1140300810090925a803900315007a200015100000d106404070386100e140d00c4523000c2c980d800b283d4032482d0354450169240400d801c4c2e11040046000b40c0c8181c2c0106141820760b510450320481c080c2c0b082e030502030608034920505030240141c61066210724050b544944200c0f001620403100180058181800c10000003102102c1080c200f103416094901f44000c0e44803505020388610941d0021101800345800205c0c0d2a600540ca04003160500ea400304440d8600c0081262141c91900500d8420850b2600802c501d04000d02d0840c241c00d14201203030407007219403090f079162800e1500e561480340d4036102d100c00c21f00c1d0141c060741c02c0c504041c0c0d000d209a1400ba21260000d03080e180005044c020302140c4000450000d40c1580d19040c3e20509503020552550110a26002d0454003100024402c0e0001a5254401c200310720041e08c4030920807002c800c0c07121a00b005052215180d00d078002150320001081d84e0104141c500862841c001c410b15000030741000c4081980303075041600410703020044d400c030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 507054388 1250 507053138 507053149
    0xf0b06040b25080d020a0e030d02030d110c0d0c170403050303070e130c03060501090f03052e060b070b0903070f02090c131716080d050d0608011d160803120702210304110d02 76
    0x802c80300c1150005209040402c0700c02140073b101d108104074498111000b10041e0040d0910300700301c1c087c0d10b00118140401c503a01403c0d12883c04010090380092000c20380d428002c0f10020315401004004443c0586c1041040d0211040340780d8010000e44c6568080005507045203400001c0d00041440d40c05c0e040c06c549805a42c2c04031980900030f4264000d083c5a9101c2c07001802c07409046d18440e0521007a603550070546000c0e00708040c01e85984220380c02080c0b119500004440b140c83c0e001d51480a03201a540070003c8920005105a460042c20014049500e500e0500c20020b8103d80083d0803418007180e007200d03d40141000402c0b0710252185061011020000303900150203003d26081c1c4d9145a05480c0b00007601c02540700c0540e0350300b0702074583d00d04081c1d000819101e441100417603141d40b6000b0203100848403144600d20701508104205124607200407101540f01403103004442000c00311000030401c41903980c180e50803008000c0240810800030405048143d84201d50166294903903400080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 507055638 1250 507054388 507054397
    0xc07050906060903030d020408120703020c010c0813090204140301021228060803090316060c02040b0303070c0e16020607090501080421030f0b06040b25080d020a0e030d0203 76
    0x51060411100041c966914501101c1c0050000307002d03203031180c0e0036030354000294005028000c00383c040e03060020799007002c8100307482595416030300800401c08124015510f698052100341c035480e03410401c0072999001c0400403801070406080069466191074211841514020b0003188640d0040000c1d08aa550602c02c1a40080c0519a024500762140c0041811364104c81200c80701d060034904001071018010024154140054069824250340d0090062004005000f0540440c1024030850b0140c00e09a011514214000d0200d9203020b0f05900c0d6223240c50895440304110f07041040420440c9a0f10352510001c045650009008900300410050701400e0b06000e07080c10840c810b00043c040c0035000a2811030303440780140c40010090f186034002c016181d03018050034030600340300861541e03062900441d0304403003c010f0400d080c050302041e01c4079050a20700800121010b52f81c0d640c00821003260040400101696005079555049103021300000d45450340c8520a41052602e0400160048100c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 507056888 1250 507055638 507055649
    0x4080a06111e0a030e0114010302090709030c1401050c0609030a18060504050d022103091206010f170f161a03090a0b090a05100501060e030d0e0f0114120a0507050c07 73
    0x11030f1070f48401079088004040c260203807410f640c20100d510180480b41c103103403816a4020745a2001c40d68034104140c031700c03500302c1c0702c020034901c52400b08010b040a0f5421101c000501490300c43e10300a420078846150045c1500c0b61080380c0c20005e00030010a8015514580c01000c040840030840d1078080094450b005902c0781501440c02c601c1ca2008558500d09905001242c0e03030410000b55080c1d2030072507525000121620301a18001e84030810710000022100c0c100d41f800100c0541041c00c2c0802040300d000c48004800d0144144d00090303104034420304c824034076402c0c4410f182200c0e518006003480e844440101b2600c100030b04009101400300040340984000c0d8104940001603110008282d1038180c8420000d0700d80d019a04068002d17440d1a0441c034100c884030f949811b00c11102a04054543d480c15401e5408200c552704110514140344020441c907070350504200c11114200c00d015419584920750400c841c020301010040c10181e42d1107030036000003562422506145694101a941e0956400744 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 507058138 1250 507056888 507056947
    0x1403070503180f1e01061a090409120309021f0c1b05041e05070801060207060807030b04051503100b13090f02030d02030706060501050a0f03020a02100204080a0611 72
    0x500300710a0b20205442500e802d0100c0c3d10b040415140140c840558400c800040d80d80e9100640c0304240c140644002d4441c500082040f40c80e100c10301d40f00c10380c0285807090b0460b46a40300ca00102c3c07007035811919200d040b43c0b00032070f00a9044c81000300314414580710a181803217070418814015440a940c2c0c503215442600c40381032800d8450140515881070b8421903000d4100061040700002c5a42400e0000040510500036915082c105680c44903090203040c00581c0052000c00950388100c1c1070f40c2c0c00c94600c2c100003401c0045600400c060307a004403042d0300041140b0300c40350402c1c03e040001c04031000405030b040098007d01400108040c210000760302545495180c11310a005007406200403ca034003c00f158049440d601c0040e441c1d812503403043e0b0350685000030010300e55000c0c504032942050700d40c1c4c0b451500152024181e0003034100c42c2d81841140b0606a2041800c9450300c0144045c0015100078081904545410030aa8081d00440311004801b0300179000030b00c036900c01501112030705544 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 507059388 1250 507058138 507058141
    0xc050d031a12160b0a1b081219050c030603151b070516030f0506010b0301051c061e0e0c03031303060c0c0f0c15020c0306010302041107020d05030a0f1403070503 71
    0x1415850700c80e281c00c2d01103c04003071610024408070b140700207160812164039504c400e100400084280441100409420340c5000c11810340c81c42c0c2d55008441d400070b107002088000140300c10011045a40441e1241146440042407010b41c0c60100300503104080071410240607450580188140e08080e0080703110b00b541c02054403400c2000510544500e200b15840122045035130342080c1e0341130f04c4a01010f48a5010303500000c1a03550b46441100d050310400384c2115008100003540800b40307588800252051695140721603900045141d044030f40301017541c0040351030b10003000201d0516210591a0340b280d8001c001e15803d810107100c041c1c1c1200d804c4100092944509032040d54410443d680050000746002c03c40010042d01046500984d802c203032101390085820740060ba55562250641541603000400400051502e90800000759a64007501800c282e10741c1c0c040340c03800b4000d1204a500e900046402d03600c4a502011740e490402c41c5142240882108141800d03ca2101502e0801003050010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 507060638 1250 507059388 507059419
    0x70e0d0210051c1e0606050331060911100309030206011703090303032401080403051602060d1404060b0910090f110705030d1406300d0c050d031a 64
    0x600c100300034410400f0b00540c03c1c0400101c040052084a84c102c2e68038210020841a2050050b02c1c444c525190100c0000003440603415030b002c2d0f030007111030404200c202100001600d140580079516118581250750090f818007000007044071000003804052a00004002090740000c060341180c02400d00301d400901c4902219046100384c40c20241c0511000050021a080c0070962070031000500302d61001c0c0201c0000111036000c4103a03009400940148202190f6640c041d030441c000030720040c905460090085202c8080d2040846641c210302c074071004110070321202d4041d00c120301c88112203005051414083c591326a100701c2c0101007000790b4070040c3ca1024140c03075100100b42410349109980380c01d0030b881c0c0a5074030740c1f0456244442038101500c80340c070400ca0950003401000010065060701e522440d00805246e942c0103552015590107031800040501407080b8440c401b01642c807240f040c006420010b1410107815102170030503140c000d8241d40d5421503252401504401c6401503040615075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 507061888 1250 507060638 507060667
    0x110c060a050306041d030a0207081506100c0501050a020702090108071a13051804050c010315090b0102030f030406020a0f0e0a030b040f02120c0301060902040b0f1b0a05010203070e0d021005 83
    0xc842004081702c40b0340c0e403005010300000c041c0140c202079608482c115600d40014580311001d18002106803180000403821625200400c2f4807100031501d80b00800940790780741c41d030075120241c40d5a446117500068040c10b40c00e00c220001c0c00b6005610007000003d1a01d00c03140324998004205101c45a008604903042d84001d082d04401054000c04540001c80700c10540740c01010269001c0301c041c8501d445d442c4580d4000c0c01404d004609480325516503e2510400d40c000d003041000e2181107000c200460214200090091404ad80c001da00058680b0303540c40c00640f06091142124003031155180300401640d6a41c04046c050341d9202035030b141d40d5101e0789407609145409400c0294400d110508180203a07000103020390b03050000b10001e111150360340c40b00c1c4007248240d0080e50342000f010001c03d003070b40e01584000c04000452001070b90084544941042c18440c0307940b800c5030207075000024820b9155103c1e10103601d01a00701d40d6030855002940c0061610305001c81c0326030610101050030f10540084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 507063138 1250 507061888 507061901
    0x12180c010201060f1a040314060609070309170f130b0c060906240402090913030810030308040b071404090c1205010b07060c0e060c06060a06030e030a030902031c0c03110c060a05030604 81
    0x121031100c0c0728001c02359141c543c01d045800c036000e00d8103400001c544511a02607441100c4d0400c2c580c4a84218408212190303034006202d01c0c128080c104541d000c204101d44001c402800a222003d4980c2419010b05c0e040c180050200171940d448a410310801c642d81c5213000c0801c0303000c0d0020030985000c541c040ba000e801000c8040d98040c1b800c0b820880e020050f2400004802d1080d0340b24485039807051420022600c2c00d00014000070348045c00030f00042c008958040e0005142c0c05c04040a01e00c110b500403550f449a0843c81c090360325103403141200b13500a521808241d208080510440d8188400702000380138440e4040e0125489180c40007a460003141d940d82000b0000d00070031b07900c02e007418100e030f0340c0c16042c0c84803809080c45010005041d0b20902c1055245040c040140d890100640022800b42c90750040c2aa414002c0b0090042d41c0c20342008101c03ca0015a01c4200d94280e20b410041c111006030400c5180d290010004442c2c1607031100101c56038080756003441c0c2d48a4580c0c0c4041002410f1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 507064388 1250 507063138 507063143
    0x41404110a120606050a0e061b0303070c0501110307050d02090d0605010909020901090902010206160212030a06060e01030b09070c0f06020711090a021602010e0612180c010201060f1a0403 82
    0xd001401490060380024032030344000c00250180a819500d6000f120548150144000000c030094100d0040746090001400203440800740d89208001860034181181c0c0b0940303414001c10003e203c900c1c1009400c2c0076800c0300c4081c8818450039482c1c009070141403403241018900d4101d1780042d03240c0d21651507813004058039400c0301080215607142e4002c040100740c0003005074410803d9000008800c000c90040000441d81a40a80410b848401107403010485904c0c070b01d419030054400781c905500c29640030f07600c500046240840c0c441c0c0b42403000380c4520b5851012904150604071074042d035031034403c2c6568104115262a0311881150309000486206803280182942c0c0001107803014804060110030555008844407600e588660500804034130880741448145400d200702403025600030101c40d8100c0401a107003500d4480e07071245448840b481240e07801a201c0d85030f0a5008010390820400c00e40032002c1c0000c012842c02e00b10031010040c89482100741c1e050f074400502d042460b906003510015075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 507065638 1250 507064388 507064421
    0x20c0a090c021221091f02091525050604200d080a020a0c0b031512060c0304060905030d0501150f140904240e0a0513030806040e0f030702090f0705041404 68
    0x302004110f40320a125003030301c0d41a1006d00c0011a055074207208036110900000c2c510280d0005101030350500d41c00c2184403010258900c0003a002818807041d260301801c0c0304d0340107052146094540004103c46d002047e5500c1090040b03001d02548444d400c003448a600460b2541d11904400380407032808213562002002c0780c400c0c2030001100d0710100003541c001c4c000507000c001c02c10034000c148a81d130071441d21b00080c0c0750b1090713001c10070302090000113541090281c40301051100c42d5450f0217182d58090302e0004010382e50780e0010018503110f403c49006540c1c0a14207070a1400c060400100141d010901c400c1c04800005440802551258080903c2c41c54020146d44030800705a4000000c441034820740c4031040103480003c03241d9419110b40f600c204116404c0c849001015201196a003a00402680e08607584815251491004002014200c1d254200655494445e4814003a95510180800c010903800c0014000502d810105480a0743d01c1c00c0d610f02c032007110050016014002800c400d1400c0e2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 507066888 1250 507065638 507065641
    0xa0b04110906072a06110c030c100c020303040b0414010906080c0403061109091f060c020d060203040c05030712050c0604140d0f0611041d0103021c0c0312020c0a090c021221 76
    0x9540220a003410340b05c02c60103403050148107c00b070548800000c00b031590711040d00c1c01100b001a006000c0042d2144c0003404030303824992600b401140300c0e1f105401c510b00b9080d0900700d0300172a43c1d1203861040540107501e401001d608100400703400c0c030b00a501005000350b464100200c00010301005680a905000b091094981094240d4818002604c404001000d44003180071501e1401058100052580074062582c403185c2a15444000d401c040c20488202031842c070001034941c0c4c05c001c01d02c00341c01e000300b4048422180380b270814038041511031031501903032083c4010803154034402222404000207990010000e4030900e0321200034102040c00401c420301d00502c007020000c2c00000781007502c448844007c03100c1001c2d104c2c4d0154820902c4001c2d807100c0c001d0310704a48004600c5084442074890202074480300c3d260390752803c806180710524801640308085100765460b055404000811700c11804222245070010001d449042c001900148120002510380310b0b01c100c510118244030080344070342c1c0c00e07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 507068138 1250 507066888 507066899
    0xb03060a09170a0c060f2003010803030a05131202070914061c050f010903022107051b010c0b1e011203080601031a041515020106050915060c060a0b04110906072a 71
    0xe0811070303c00c17030b45400d4141f039140e0403410140841781a101c040f0015411a40d0382050b10019040007045580c02c400300301008c1d400200d06105220528107182c014000c1a814988a4011100385191082650188100b804465191100c91480300020030304e80a1000250381030044c5004640c0c40081d5a41d0300c3c007071003281450350114050208401d12161840100210a03211455020b0060b0140c1590401180e9000e4583d1120500c1c1d15180103041c840c007541d60030707160782ea246942203401104454021241714409581601e12074050210034044031034065081d10000d2100c00004e220505250b590f8000c0300c110121042d1856005000400034050100c1a81008509040c0c5201e09400502c10340302404459006001e404207440000e0118008d503a500502080844140015103402c030004000307184030700c401030184c0340c403d43c0f4942c000700f078201801d0309020803140094141c0340031140c00d106030704103550340c1411180000d400002c203114526080c0d02c160f02d00c0020500d004a01d6400c014002031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 507069388 1250 507068138 507068141
    0xc0325060507170610090906030317090d081b090d030e1504080c09061305070f020705010305010b0d0905010e010e1f110405090901020f0a030b03060a09170a0c060f 72
    0x980c8140001d000ca81c544202c1501d41c03003d03014690015140380b00004040d420081d40e20481c00905103042c2c282a55146102c1044a126401c180c001892410743c2114805481c0d400541090049000704a240c00e03c0d180201070541c090826024440c243d02041c00000c1941c0588030b120078000c00c04c56000e140c0c0d290140c8040141c45c000d601600c0030881206400403008140e804130b444c0d03e40a40304580202042050000000b4002a0b0042c5644400441080103119040c41101c0b0380d1102c500302c0700b080d94042c0c03a021050384050704150402e4010f010140b02d40c0c0660b501c0c840400008207000755107140050141866004608041d0701c5c2500c0c1c041c0c06100010044151404040d01104401455003400d05030350304c000d0229900320003008200424104034803641c0d440503200380018103000d000703041d5444550000ca02030000a0b00c642c4145258030f418058190001030040040100040960741c10307020490307002000318003041c007050384802c0b140242201c5111607800b110420421459400300c2c1c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 507070638 1250 507069388 507069457
    0x3090501140103020603010501030902031903210e100e01020c0f01060501090503010b030705060f040312180602061b0f120415050601020f1b0409050a050703060f110f0c03 75
    0x11455801c00d4403101085090705141d070b0507250054221491a802d0a0040d405440006012030b018071510a900075401c00380a80114498807a0b80c55007415000d0a10500104c844050071086035071070304855001c00c104c00545401000e1100318040350a0f5a54000d0038024000e0040140e001d01a15250000007401907000a06960382601c07280c1406480390b042c0f43c00c940c034810b0960f4155120888c140a40c1c64418003416007003a803040b90b6483d0603100e80da200905a00c42c0c00c0760000c1030203001d00f0b4050301050001312010f0440d80c8000c0880e4544420751f0384885c00322400d40802c519000a02c8043c0a070410100ca410581d00300041d0170f281401c4c505100c142850451603032007285000c01180c525880070560340800c4c0d40e103000400c3c41c15581510b003191410700c407004030f5006548407240130011f101030140b007090a010b400a403116602e5030501030217a500d0201880c7c2228903080032040f41c50000300a80e94001c5c016a060354945d002d074000c0c54a5403190398548420081100e4000c07240016510a40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 507071888 1250 507070638 507070643
    0x50106031107020a180b1f0e0d021c060f0606050912010c02030d021621030b010207270609061518060c1b0302060a090806061002031b1c0309 62
    0x200310008071280d25902038002d00000941c82080280c0c20040410750a0b10a6655a840d08002580000c070310001000002c940c00c101c24164000ea0840803515000041d0400b010350580b4100c140d00303503550008501c003419480c02541807610494520501009600c100450aa440c804101741c0ea02c8420103080c40d0802d0710b10342c0c410f0f82c040d1000c00002c1e00c10300400c40d403801680c000303600b4548585250806900007003070000901e4410780c040804a00c100b00800908425501d8400c01c1582c0004014281c40d280c0141a0540d07002000030055480c19030b41c0d0301400d0124202001000302c40300121406090907502041040341024008030b4640300541c0c0004146c0f902c1c0c0c646510b00f1001c0400303856550906e00c914004107000240c10700110315050300c0c00310200d0545880904103a140da00203902030700488a9100014004581031203006001c010041e08003904035000c3e8909542010000c4d500d21030522454041d003594118420410340c2001035200030030450108000c0c801050030b0040060154235001e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 507073138 1250 507071888 507071891
    0x31106070215100b0a0503040311010c030204170d0f05181206060102160e01030f02060d11090a050315060f0a120524070c02010f090308030f040b0606030f0112081603020105010603 79
    0xb10380d240325090400300888044ca4541070400c0070b200e00a03110b0750001403065003808407208141741102d00038415481541011340b00141c42c1d504115609650000809648100380d0280c054420f4036900301d580b4a0300502145800c0d642ca105030801d0f40070000f491641d142d002004031800d42840b003004102e00d84506000c1e070844102e00c0d404011480150075922403040305041d01401440420b124071800b01c1c03a40e0001d042103161102e0003090300b00b200c1c90209142180304001c59500c0c11480c2404c4250010a01100180600304060707900548100740a00124800c5c29079101001103074076448a030b44018500030580c19021010341c00e113281c807043c0b005046012480b0411001582c0f25180502c940102e1490350364280c0c0d492241d005480e1050109600000d0200c0d0000000004e90240021841581c01124081c40c5080a16020300c20b18005001c0c6813160f0350500822462400e805521811504141c5030101c40070200c8c20b06081510503d032104410000c02004c01040c1601500043e040358501c1d0790 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 507074388 1250 507073138 507073141
    0xb0103380307060806092d09190b011205010902090106030c0f11060f1005060c010608010c020111070b0a0b1005070b070806031f0e010e0706030c050405090f04031106070215 76
    0xc0680320300c1c2e030b80662000b040001000c030394035082c41000f065000080b00e00f456040d005032035508480c21a101c1d04101a01d140d0010010308110a000b19080d8041c0300400c00801d011a03920f851444405000e8a50020018603081042c00000d41208440540103000306125503100d51008000d0401c9007070102c04161840c4640c9440c900c1040869105028440503003c591900910260407a0025150302d4210784c0f003035400b00700c0780d031600300425003000f4040c000100d080c0b920207080d00f500c10404008082d039140c500138603211500703003084480d02a4448034414541e43c07031560110007000e00b508030b00d030801808102c8005240d08600140000c50044649208540c0d925500b11080901240c041d509504110002d074010510201406c2c110304207248045031144120701d01d00e0031200004600304007540502c10400c90301d0740621503d00000c0145c03412038503090400c004140e190344064181c8075807086d5140050285482500204401c60703041c0d00341c031001d0801110003556010485d804040d100c900c3c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 507075638 1250 507074388 507074501
    0x20304091107020a050d0311240c030702121c060905040b10050f0f120a05011e050c160519140c0f0d020d0804080f0312130c03060b0103 60
    0x400c2c0c030107803503008100c440414100000c0c40900841250110188600000c5d840f000340030610050104a0800c404803d00281c040002242440f019151110f18002002801360507540032504007041004460700b0396907a450710391400c50002260f15101c1105203098008120b280e134541040e0b00660085c08052581d4950210744411980c8601c1199072001c0c8508400c002400c200943c0e05002d0b40003000d1224422507509460304190385142c04503000d0b5510034041c0c071440042c1c84003400c0d8015003101005a8a045800802d41c0d2007000501c0701500900750b8080200001000121000c0402031641c2d020045035241c14407268024090301c141900030606040039a00f800d451481c203484004080310036203500c80e000d009000c0c0000d0b0007900c07544000c1002066594042000101c0b0303503801001140e80b041205d0b1100e041e408060100c2e0103081c103002280c4046940c41c0403403410f0742d420100c0000c42c1002c1d94016001000c1c200b02c14030510006041c109034103081c11500220070307030342c40d034a2070701d40e020b0390 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 507076888 1250 507075638 507075671
    0x80d2006060a060813020405040b06030105010e040804052e0207210803040204050421020d350a150603061a070206040303032004090c0207091e0b04060b0a02030409 72
    0x300c0d00c090700b00c010381c00104078803442462100d0b0003504c2c034008010b0501064020a00752170088034240c6064064405020450500f40706141c0180140003445450f0300b066580e0140506c610b114851040c820310000c030f000010564004c002c90445002c00e092114004003000c0d4407492140b003043d92400124841e51080320244000c40c54450703010710780e5469070f90303950f003040020a4054019102c103511f034200c90240406040b604500d810841c0c0003056440c45500d07004004126407498a0100f40c245081c14109d1030719552a00b424002110501240307a54038440c0100400700349107010000824842c3c009151a0180d100b4800c0d949542c0b240d450025030015500400d2017042c0700250032030800c2000b040464800d0740100240c101c001c0d48a076140c2060700c3e440c4410b400640100c2e0726642d07600005101c03990100007440091056420134007086444e407050451421004e01100b030340985911402c1100d50b42d550080707002d441110301c01500c921180ca4025aa50800c0c01a001c00301e141c40c130300400740d9968 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 507078138 1250 507076888 507076891
    0xe060a0b03190f0b090739030f0212190e0307032103020d0204090605040b370f030c060219080f0a03180819110c010e0604080d2006 58
    0x32049105012094075222000300b184043c0401007a0369850b40010319030320041c1e074600540a40c1d881080c1d5003044004000d1942440200103412003600c500b45030780d005441000b904040d05800c1c1141c1100d112a001c3c6c4c1010f0304070750090386e4114001480070300e01e06100085280ea01166480c41d842902260506541e0b135280d000c043c180560801002d410f00218500030180d03203000349005428003008401110503608543c03c00d4460640b83d8a003402681401d104040006208a40202e05100d640e035107107401c1e40e10710322920100080d0a01002c0c4001d072003541e100c002e00c1e0403210b81c01200c0da64101050b8807215801401c005001d95440d20007001881810110110340000f00385241441002424400b680819a204103240d11004804240c6a80c1c00d032032001180121521030f580c48003524004001c4804080743e4050200714500c0c4002903100056117906101c0c01c1c2000300c410202c540000d5018055680241d107640b103000c9103144690307440391150250184880d558001203c1460030030351142c50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 507079388 1250 507078138 507078151
    0x1209062c0601051c08041e090b06120105040527030c07330e060c0105091e0606060f0702101e03050108031905090316180b0306040807030e09010e060a0b03 68
    0x840124038013280d022801a03d030003521071055186440c0e603800102c0603030304c5210607040090003000750800513490a40544484a141114024078208076040c2c1c3c2081341806015180c0079581c0c48000401003c100c0c4c0746034282f2642c04441301045103159810742d039260702c0703414002143c2c05030040002d8160001411054201860240820b406c41990266824105002e03444820419114a00c841944400009003958040c120000c20540b1b41070580038500303d514501d44200d07004c0d488142094010103d52103070040400c685aa580d0b01000e050038445000d80d0401a50000e0034902c542c0c1c0042c0c1120b102c00c01c0341c4040034151a150a48035040d400c541003445032504a03001004041042900c59440e04c194061700d09125042540ca038001c8ee00d440310204400b80c003000340c00c509005c01c000c1d04100300e40401100c64240000c1c0f20140102e030f104d40700984005d108071008541101090b00600c00301003200801340407501d6943c0d40399069900d400083e18800e000700d444060201d07000b4041ea088078405c6d130 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 507080638 1250 507079388 507079399
    0x80709090201120e011508030c070e0114060915120f090a020a0e0603070812130b070309030b0c0405030a0b010509060a1401050d02042301141602011209062c060105 72
    0x984200070901030008038880c840217550707540d41602c4801550141c2c2c2c02801c000d800458944851034202c5280c001c0580007580e0341104200100060241c100c4143c0c145034040d03071105c0c0c40d090000041400103001040300c6000c45d40c042141e543c042e003c200500d21481c41c60215500a441e444403098035120308131000b9410031b01400e424407640c0d080a5065801c42c0d4043c1c04c480c00a95914800e9080c4510501070f501600c00000d0744900140e507030350b401d601070401000800d140075125500039284161600c4010442000300000036070031705040b42078400918001c3c050314800d138100c0c07412401400e42402041c2c4100220b00100d02981080c42d07000b025180000d40d50b0881140407001036800360400e0140002c0700c2e40801001c160070a45d00100c02002c480800c0c040303c07455810002403d08258015403600c60300c030500241107080c4100003503a04468080c24001d44010039031007541d000c3c080d4100080c05d26420000c544128408188180b4100c0301166106400d03200c500c48821f44a060a03c186640300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 507081888 1250 507080638 507080657
    0x20112090b040807050a061505190806070f0c080a120f02130302010e040f150602150c0f07140303040f03030b060f03040b0a15030f0314031306090213020f04080709090201 75
    0xd020303400a15815000e00f0440d45801c401d60391f080145c1d50201d140d482044007455040005050480d01c19a070410180b40d0391030301508143d0300c10342d81d15009000740c0802c1080c50600c480240200c0c1d00101c000c0d00080e60a60b03d00e00c000c4045d2808c228103090b19101458105c2040c9944d8561090f20461003203204c0b49221a03180d40c004440e03083c03186030500d600c5603490350b80c1000d01b015840b403a0030b50b1f180306141d40c18044c60322002070705000c110360f10140030001078810441580c1c48001216410740042d0f900e40c1d140d16481c02c100380b260046100030105488004140010310400701c01c4055518402d0f6418403071001c102c010300502d800303468000c007140c0780248081400560a80b46265000d00303018000a60b00207121000c841c0851150300503500016600305403014583d009a407a00702c2000350100704d1450501d85103a4000c0717414000080c242076951503900c011541c03040e25400d040758612001b90344442d0003140702c48041c7d00c01d202d10000c81c822034600180840550040c0d032170351a0141c4420341c92 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 507083138 1250 507081888 507081893
    0x604060605091909141909030912030509040e03091009080d140f03040305041d010320040e01061404060e01031716050613050d08060f04021b0316020112090b04 70
    0x1280340690880f021075001c400040340d818840d1240f0142800680210350250070b2444005800103030066890308810b040007802000320790003d14010854050140e44200071219090456043c050441c109610509040601041420000250a001c4400c880301c1b64840390740b90040d5088901031040818a4100b5042580140e0042d49040081c1e403007035407560715000da04000ba407020b0b48110744c01c402042f4042000d2051006500195007030301400203d0507119415030711052070540e400c010003004201500381c03450054603943c11200b03010600000a03c909611006c412181c0c51050400310701481c501000042e6100410501c02e048942081400d403001c60300b0b1303154081d19840490560b20045030960800009101009190302c030344550482801244501e18145080c1003101c246402000020014004241e07a48140c040160404a500590343e08904100c111460302c1c040454151b400040fa500d0841400003e2401c555172003640c800c403040c80b414580e00e0880e07121110251080c007040000600 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 507084388 1250 507083138 507083149
    0x272a02010e160b091c080307080c04050a180e06040b16051c05220b06040609090b0c0901030b04090f0303060b0a09030f020609131d030a0507062003040b01060206060406060509 77
    0x40d1620217400044e480003040c0c180884031a50000c200d844640c00410002908d81c021525a002040f50345e0030b6103428036110004407503644e14013400800026506081000d00d059038032510314018000242c80c080d2509040503510448110b4400c0c0c8081081c651b941005c0d0310803c1103440c509620001d41d0102e4005101900003080c0c024400c0c0655840022000300852140c181c045125114840341c1c0d0b80f514042040c0310a803226030327003c800124100444100010129200e10b41d0144460780c900f500c1d644013030300480140c444400c5190304940f404552106010301c4d5451229614020748050201c107a841394800e0a502c658004180007950285003407000640300708c2c48000e02c0e40018802c0e401d140704000002c030410300e81914924500d03070300d000c03041c206821391081e007503592a100b02450500018443c040d03c01d00c07400c20002c2629956a01c041c000c026060320282c080400d4042d815204e01d400d01d48882c0200702030152501512540d40060b10f40c1c5003500400c810340b1040c1d0303200707410400c50760b06109 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 507085638 1250 507084388 507084397
    0x6010e060f190c140f07060c1505070e040603052b080c070606090204060305100e0636070f110606061b070b0307020d1206272a02010e160b 61
    0x308950320f12044003081d0401d1081c2d442404070b101904030411030101091618600364041e00070b1006a07210039000c54000008030348c504a0b09a00894a55903100080b10412241481c0540c00f9103480e00101c1484000911070600f00d00c0301e0305480001c1481d080401a06644200280004604c04001154100040007614544c0e10070078011403d0340d158102002660000e40141d00003179558820802e081c0c00c0b00c01c0b4400241251811340d4800e00700800031551100c0311341020900b00e0344a00c1c8070791740220040032800d80162138241401881c02d0944004009aa0b440b902c00e00242291000d059440c4000c144113024210060081c0e11385075020300c0345080c3c41d840e014824018018072400140400c103200c02584505032503400741c1910342d8120313406484007100042d400310b8030745403a0060000800c5101e644d5141989003c0d2074034005010b00c2d0a00c042e000d000702c0140b0010061090741c0c0701c440c40c905000074414541d0001e10502040b00c03000c3d50741d01c1c255100c0003200043c6480c2080a04003140041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 507086888 1250 507085638 507085687
    0x60609060412110d241109060f0c0d0302090a0e01060c0201080613060f0521070302060c070807030b1e040b060108090f19050f070b07060506040b1806010e060f 70
    0xc41040003c0008a200c98214800d0720101c950b00d04a51a00c0d03189a14082280b40411040100106074101c2030594080e030703410280200c50000d061035000040205036052000c40404980c40b0042c105c4000340a900451007081c090041c40388041450854a0f4440c1e042c1e92003607840d00c00b6070303100b41c00464060307802600340354021550032038800c05802076001c2c2c040030b800e8500c1c400080c0c920705028440d000c04400b1134503903001424641c40101070000b041142c101c0b6012105552141130f480016404e004080d030120115214141c1d0005c20003601c4d540301803150003640500401d800c03005403290021802205c0040c0100e5006001994a6008000d21030f04890b0700c200b118604142262a24a40303118040c410002804e00245101003040400c020f0422001032000340c0406840c0111078003460003021801405592240005569521a0350201180c640d0007800d40340c280d2002081c030b481001041c2c03074071400124030030031a03803130344c00c016048584443e000b17400c191820080810450b8114000640c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 507088138 1250 507086888 507086903
    0x1802040911041d0604120306050613080606010215010e100e010e0108010b060307020d0c05070f030602030a06060c15020d0b1309021201050112110402041e0e010f03030504061d040e0c0306060609060412 88
    0x1c1402d0b190500540b0702f40380e01c42609181c1c507082c900311a00c0c0580040c503403811940310150109085005581310f07411246a001c030361f8144c0e02c4140581d50030703207070a4011512030480900000390b90400d0100b00390407625518002c206009203e0b05100b0144002c0369190003580c40103038030700c40e00d40c40350800181c1c1500540c1950300540c1c8907003842c540ca45a070360013a1113541e004024040503800c1171240d000100111305288400d981247d80741450400d100d020021816800b05285042031260f0f04110200340c0000c0000350198050340c44200140030040090b40030b4000080d00040c41041440b800c5d0583d1240101c6d00884012540c0d2800c10486041c165a0495024480002e80030000b90243c4a0440b00640400c9146e05001ca034a80c0c0c1d8005030320420740d00a101c2030400200341c02108590588515182c2000603a45190030340c5100d0b9030309506907800c00d1401c18003000f0f10002242000e2499012404d0315100d85642d01040304034010110840d0740300c0800c0104004407a140d561804890384184039 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 507089388 1250 507088138 507088151
    0x201060b0405061606181a0622090203060c0a02010510051c02032505120d05030c1810080a0f0b03030417120c03090a06020a05101802040911041d06041203 68
    0x4403217041d100e4400302890107440280800040111041c908818600c0b45a4440c00b1454a6030009951100300182542c040e420f0301c105004000c80703a0001031286401800300d92180c00e066807940a2940a03510380380065107024003054400b51140c05a03c01c85070010500d2002c8000120980c041c0c0039000412170b0305104d070050301110035201d5500e000c3c800100c035011007182e929240905c040818401460700d5140c200300180082550001c060342e070012001c0709a00d44449403a0080b4200c3c6110440300e03680a20b80e5544003007680c0e8051f4040d441600c0c8001c3c140a600b400070312140a03a03041940b003d40c9900148405e001c000494207134458040c001c00100c840b0801682e0190401d076000e00ca16288035040081d50350b06038148080444c005000324401005a07145585440391a00484100c1810054540781c070b15141c1880c0b032081422894005004108420152a00c5000c00c0c02c80c4400303500031801c0c0071000320682c240000d03850f9401220b201410b951358031039482900341002d040c17820003410740d03801c1b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 507090638 1250 507089388 507089393
    0xb0603030c100b180c0301030b0a0f14041104060806061005160c150c0f3002010b0301051b0a080c04090c0e13020f0a20010221070201060b04050616 65
    0x302d10041c02200010024589094200b0b110001c109070809207440450709080c0400311940030100ca0440b9000305c08000c841e01c48045003405000c00c0720aa614107414845000010b600d120341f00b41c0aa88142100c41e52402c806042c4429250107214550668020f240050618100141e21869a012078503100b45002010fa09130084400c1c03200c03040e5600914000188455800003211044400d0581004050f00343c040d90394a02c1414007220090100500803950400c00300c0c4484d03c030500300320000c6803082c0300c0e86980e0024000c2808052042c480e6007440b01041e004d0807800c0a40c0d034018449401039242041000e000c1ea40518050500c4080c60790410001031104414401d003480d8420759030f5030341e280f10228002c0102d44180700c3c5004485c50b02c1045040c41369880142202c03030041d101e09090040328903a01818800c1074100415030015400007484154002c2d080340601203000100809280c9502d629504030300f00c0301d040c000c80300703101c0b03003000b00744103d01d050302c0603100929000d40840f4402c541c99 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 507091888 1250 507090638 507090643
    0x180503071a1c2f030c0d02091504060c02091510081312030905150105060405040c090e180f030705064606080a080306010f140a020607140a0801030b0603030c 69
    0x100d042070381e00c0d1144150701420505004402c481502602c3c45142542412950001a4400c0034002e020a03680000c402e03520b506c40c50b032032100f94694805240c1d107a0344c0d00e180c003405480910300c00b24480c607070400000c0d00050041c135010101680161200341b52904401040e43c1405000d003da00c031b00300050812070300003100310350034081c1015995800b10740e5104615180340b030240300c0d8401e03031404180c60300144080d80700e0100fa1000c54004480101d40211020815600c0007000d4110b82c40030540d0404000c144580d111505500002c3c4100b15000d801059110741d07200d0084613801041c0e034000001103940b1456111910f800707000084801d04522120300035400315a4501980c00d0a440e121a2148080030805d11504004040c0c0308007030a03007458541d03604086488010a450b0501ca1801148080140f0a020361001404014409980e8010780341000c1c0d42c81004844140c0060380c0702d2070724498003070840d05442c406865038480454a0b400c558440c00300d100c3c01848650144000d000054492104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 507093138 1250 507091888 507091901
    0x150b040302450105030d0806060a030204050301090c03052a22020304120807050901121d070803030402040501170319110114090609150106030506060702060a180503071a1c 75
    0xc8010700410280c1d007010b0a050440140d110300d01c02e400043d0700d55551030300601ca00340c1c0324500b100c0d01581c40d0000344040d0000e0040740c128039010740c030b04aa10780402840c03403882d10a0f24002c004491510800342604002e0905540f1380090b66203a00c41480d0040c03d101e108016094825543c03850040410484801282c008840644800d041203400114070742d0400c3e4143d800c0009490440e02d080e4035103001800000d0010000c6260396600e0310f07102c0e034070030540a120754400c2c00318055411183c0d0380d5802543d2a0012f42c4c003648158a020000100b0011250500ea84500100d000c1c0d0309200140741002030200d00520b05074140a00b0b884e01070103c00b8280700c0d454000d00e003901070906500300f02050a19100f40100400710360b034040304580008620340c2420350b0464041b86808603140d56034902045950155a200a40141d00410402c00460b00b281d03884400111407c46054459607038401c041c2c0c0c5001d03030b00c0717061000965619000c1c0c42d40e800d580144480704100303882072070a10442c0301d42d901f100c2c0d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 507094388 1250 507093138 507093229
    0x12090609022d010f0203160c0e0103080406120b100c020d02120706080a09031707050706060905090f0106060e13020405030708060912040501021b030a05060f0901150b040302 76
    0xd4070070740c908a0b0a21840100d04407002883c040d4080001803001030759901c5645169003c1078091500d5008000d0403d402001400d5452100081565245001141d0b82c0142c05200301140c0c00d100c1140e00000d043c4107505032003a0061116030b900c4c0b044101030f00c40844c06803060340c210708038003504400b41c1c41d1891486a50400c2c4801010030600d0440c0040001c0340c01b600c0c00000a003810358210120b81e01c0009000d01801a5600d2040c03074a032903c05403401d00c148100102580e0900c4c0001901141543c4040c1c03244000605869040408006150172580207000e10000300d4501c1102c2d5050741008004046484607100c401403902c0e480b040043e00d00400360b88240e00d04e511140070040810800d00071071400c4030305010b0349410542010000703500c400050b14030132181c0080901d144800d540402c010780c0010380000503185242014000105910002c564a44040d820001c1c0c0e1f5030041004c01101e000c4802d104d29041c28a401c6900304800407550720a1095824030f201c1c1c103964650080202c0003403100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 507095638 1250 507094388 507094429
    0x30f1101090813080102160b06010507050a0c091b020d030b0301020403050a11010f0c15020f070b1303081003150207170a0806150403020102060601030b2103040e0c04061209060902 79
    0x411800c080000f01a0707604400d84a9006010351644011840981400e25074042c06080c40c503038074500101d81c83e02440b48060076070702c5a5100901880714400c820070650301502400e01070b10310340000f0b072652921a10303109801030b131007140c1c020b030502d20079070040c40036600c014005854566240c84452824000c00c0d0103641444811541084541c3c200349508814011400c045a0007403d540342c40700b0749454684104200350f00040c8484011000c0012110030940c4502019900d0070501412040041c0d1590110301142c20b8602094000d1503000c07181040320307844804801029128450030019400101003260b02080540b1003882c0105500c0180c11902d15503560101c8502d010410081009400e14a100030704c10b0800040c00980d80c00301e011a400482820b02160490610300461b02c0c1c08120424101801d0340c408001c5200b68002c001041101c5104049030019203d0542e240402d100b203114540100313113504c850341f0205c0000c0d000828284d0203100001103a0072103030007040302d03800d2865103413a0f0340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 507096888 1250 507095638 507095647
    0xc1e030a081c0c17130609060504020315090a170403060204082a090f040309090e0304090e010b010c0201080a23061c0803011a070203071707090b010804030f11010908 73
    0xc180c0250b6924003140308400c24055603410440240c0300d01480080c800458444400103008042d03121204c0c0074895004000f0000e403041c0741032020007064107030780480c464050b60785001030b50044682210700400000700901103410305651240c4903944101e010f07104c0d803c02480004049a081e05c0948000d10107207000d071141c0e8034001000141c04110090001d01c582002d400c01c01c440d122080d0a55100c600103504510030340b100d0506035140106070344086030003820b02010f410595000f0000d08115200394000b0301041c030301405420f003aa03405080782030004035040546c1c070241d0f11908005801c40b0082500140c168020720245071781180c0038202e51202c45513a0103004080c20304950750700c0c01041541500c01c68958558401e0828441031084451484180d1840c070f11149459049800c035a50003020ce4022548c0d5030303000c9150b40f0007480b10125500450307100141c1141c4901540d014041c05070750760300031039a41d41d50548a0b0304101040008022138441c410700041024440c0c00e501c0d81c080c00501c0c1d01c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 507098138 1250 507096888 507096907
    0xe010e030307081e0f0106030b01021c0327110105070305070605010f0311060c060106081005130b122e0914071e08120d0216060203090d0807020c1e030a08 68
    0x7528000700181c04c0c100f91100308900c42a0100b51581036070024640420fa003500640100d240450743c0051a80c0160510501c02240d03402d984407280b44614020140f4440d0400002410703d200403a501070308400041f2030400e12588228014003115101e41081414005079488850485000340c00840100c8507030300007030051169401890408803801c5424900d400343c41c0605580341c44040c86001d003803144e07800205130444650081a006010050950103030300b64150101c102424942c5c220b28011502c045001c08500c0c408a0990420800c0f01d03145205c0d081460880c1550940300171403001c40d295500e40403000194215100031180150038000c101c09030410b04084070803091114411441500440101300f00c20340800e02e0700408038003540b07441c2c990f4014072444004e4031424184080740ca0307000004804102d02d070f0b4043c60081e0440402c8a030148612903065400640a450210140c3e10038455003d0924103d841142100c2c00320181928900320f943c0070a140440781007044031303900340100d801d00c40d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 507099388 1250 507098138 507098161
    0x19170601061407080d0b0f060f250c06080c1b0a020103140112110406080609071d070c020603060a03050d030c1206350712060c080105090a0e010e03030708 68
    0x200d8440010a10720308002903550041602c82c00f11710f1040c40d51645468441640c2e40d46540807540d0707018001c19510301000c032006449500076441c3c8083c01c4242e0360541e000040400341d9042d180d9100041003440307420450107590020005003413400105081040350203500141c0070002c00d0112400040c10036510900c009000d503010362460062019103a00104814905030031181078681d00105ca00844412074400301c1e0140c42550448602403103a003040c05103600b800035412049800741c001d0316410702c0a03080c0325100c10300141e9156000560401204015180840046410040081141810385d41c2c81c0d456904254406035107a000c00da03585103e0104d1604050000e081c41cbc00d1440401906040848100041180146491010140040d120001512003600710281c42101c0103d43e501541e59102d413000b0003a5a101710350b03003400d003080714124034010000281a242c00400c1070f001540c440a104004250030f1031003a6403992220098550004e00740010760041090faaa13542003071a000301e5040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 507100638 1250 507099388 507099407
    0x6050114010309050309060705030c0a03021c0507211101240503070e010324060f0513021911030d091a010b16111210060f050d050a021917060106 64
    0x28141810300f0030000025102004a40c03604000b1140b45855032003a090041c51402607050b000740500ca9210400103042d00007d022205150f05554003a4001408000710344a014041c0018031000110754154070b0f031070300c400e14078207061528900b1900740030711880500c1c2510b0344420614a120b40e0720007012070280000741c410001c0c20065000300220791515020003601d1405100141c028070000210b29800802611500400000207105100d500d45503c00280c420045104a600c1500b4005800c0b03034000007402039030740e1103d1984001405041c0d410041e50742480340800311049001c00c025040d94201248030309104a401541c0941a051821408519600c010303040740c841c82c0010300100d18400034007841e06080303580c4406448003a01300352000c154808070340800e05100d8051122024046d100c40d072300404c21a40c103865908a0141c2e00c9041c00bc00541004000d815078114a03000d40143c28180248007500e09a582e101107040d64900034072000820620217011aa0031041c010405140d1020303403130b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 507101888 1250 507100638 507100679
    0x2010c0207060c0b150a0b09010206130b040f05011104080616020303010b0703031509050a0906050a11040b07080f041d060109050604050906031e07060908060601050703200307060501 80
    0x1010802d08008015100c00c072101c0e0020310810300c1d240041e00340b001c008000f0410001c041e01c4c1c1000a82c8444002c0707100d401403056540148140d200280d0700344900140c1c0044190803135003d94458079a07840b000501114120280c2d0159240d050b4140055600801407006100c0a80500740a0604482c00e814a8000404080031580207000610480444900b1180e41e5585410001040c40d250300020b0042102c5911940c3c41c68a03120802012490540000c0c0d02c032807040d001080305d5610480c00e0022a040300c61040103c1401b0700003805009003400092220501910309541045044201040c00c2d510540001154000200c1070003016095050708640001090922404030303401c01c0b01003200343c0558403555203d05543d02c0810b0543c2c13004e00040549122402c0300144410300c80420503500c1409100f0100002e8040200007805000481d58a0281c001652240c3c40c0010702d0f24100c404820624807501c411070014444505140c08000030015180300b00d001194644c50000009071075040705420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 507103138 1250 507101888 507101893
    0x313050a0801060b03070c0507051c030e042a030605031903020d030209060702061c05270111030a090311070305070f0e07020d080a0902060f0705060106021f050403050906031602010c02 81
    0x18050101300708241c90303006407240b60041144003030341420b9103000255030001c0c0d00a01b40d40307441200c1c58030301200000c40a0280d22410394121025003408110340003010010301000c013100d20340c0c0d0100c0d00600104004003462601084454840d00020305042000103805000725118498a0425405000d00b03042c141241c18118102106500403500503c1480402480b80340001118004c00d640c034800208016400c00c01041980762199840c00b542c40d07268001043d5250900050759040b00500821079104459042241541c032111303161070140c0100c800031000c0c0701c3c0ba01017400a12108101c584025406240142031192600c401080c41b044d80b504582c0c00702c41500304010100750000b9504900000d503282156059941140c0000246000c40009511038000100910211756803806400014005c4041e00c03420b903039441c0160703550050804001400a900c1d8406190010154000c60b8082e0003800c045203021200400184151700172101c2c0400e2100300f0f508000001c2e82442030100100e0236000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 507104388 1250 507103138 507103151
    0xc030601080712030c081336051305030a0302121302030a0f051009050309030105010506120103060c12050c070c080d091a040f0602060901050a0b100e040e0313050a0801 74
    0x541502c51a06001e507030701909034218040101446241135807429508003200b5519640c610208050001e000e200d480b9550840d48403d849a230641400070303101c5030200003840060220515018090b100092150b54503544466174080410f205100414800d070482e5001691906540c10140b0301203006040001c0b0345180034000001030700c0018503612002d400c040840341ea02031034a021071801d510452440b544a0800c1140301c100000040685144030080b0020f1290f0780c1c840d4113200d2039014000d040d228540e18003004101145540c0d104a64030a42490040c84403103502d1003100a66900b5075040303003e4140082c400060010301c01107000500620005054103c000b801c0092100c0c3e0380d801004074038406c4200600b1100841812280140726150301300121aa84003006500c8040880700343c00780c0d508010000d040b094813882249403082c0300030031040c5512601001211001d8490500507005036460940062082c41080903000142d500c041a0302c0b0385051405000b01d40605611220303007681000d9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 507105638 1250 507104388 507104399
    0x14070f030512012115060510051201140321120106090e09010b1f21090525090b01020c04050907060e0102010e19050a06020d020301060f0509030709020306040e0f0d020c030601 77
    0x2404c6103068201c040d490700c24606101400c014071007580601d922400c5160a59412a000b8015204404480e81034035150303079132455002d10604924030080d9060704403414420180300002c0b40b070320010b41c010546908101c0342c040010501c00c03003a000f00e4045003420000b000100000900941d02a03001e0000748003006422000c50040d004c1c1c6868080340c1706036074804010052051254120961030101c94a1041c460511550020141d41c40c4c1551540200a24000c0035490406401c00c42c4c0d10552084000b203241c25010704c0102248100c880c114009d0007880600c6035640d005150189c01c41c0406000482d1410780f0182404a036801d419056906006c07150401f00d402080440c45803582000e006041886490301600744141c003030b0000c0800f40302044282009030f85038051070607120941c45600024016000c00d4402e400b900c2200c984c1580050b600740800603030f503009507410040140010416180c15021a41400e81e0015542403035805140910502d0780d0400c120202020182c0c0613280c2c650514 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 507106888 1250 507105638 507105689
    0x2d080c010c0204051b040b070b091b010c150c11010b0102161a0f03040501050a050f010e18032502030607170403050a180e0f01150f14070f03051201 65
    0x321400b0344500d580d03000041c20040c41d43d810a056002d001011642c5680301e40e002012600403080680d0792480ca000000c0444e030b80010704a5805c1603020000000c3c806400c01141c3e920b070403c004540c40c43c81820030440495960050108c240203540310400801c0b08400303214211b4100444c458119403014208250700c2075803810000943c1c90508100055040380281512513204003c440800c0000001c100400e100041d80417074094480c0400034000358031494071a03403000e80280540300e101c2803002c01041c0c9040788024481c1c0d070030344902e0589041c450320004c190001640d080c20301c0d072001400003d20341180380038086958041400d0501c0000304070000901c0c00d481800400080174040d00207103880155005a0030300e0001c1c0c01d00c20211040725141c21102005c0c00707059a140030001140c1002040d04843c00220300030381d080b10340d41c84c10503980c040c400b01e8690a400d419512501010402500460300503d40c1400240c001c0c3c407165179908251502640604059000c0600b40c0c16000412907a410380 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 507108138 1250 507106888 507106907
    0x9031b072c070f092c040f1b15080603120313110a142209080c01290f010c020301020403060e1009020102071503150906061101150b0a092d080c01 64
    0x2e0380c0002d0200c0f0030881404000c0d124170068000d880c1c520100000c2081c01c0018000d41031054451244c00000c1c6400c0e4988285980178034102d02e141e0520388580140f162442590204008046803c24440034040c0c01c49a0710684880e02151501411a81404030140102140c4c210550b0403941040c1f500341c0c0b03000350300200600705102d01d40b001d1001030b441c3c501c05c1e2001c3c030509030745c4020020881940342c24a0f42e980880c81100240d420690b510002021000c0005000504000e424944000030b1040009020540e008d00341404424034203100561002d02c00740010390700c01c41c00003608a0380050b0075842c21000c41e032002041c5090044840040c0d0b804110fa50031202054401489094841c02c01e90140c985070030702c81182d129a040c0080d20044d0b41c1c10880882d6440c2e100c01d4103049030440c8107030982e031074503041c1d03883d01040c1c040c1040400b00f40c070028010440e851034802912a1107081d05d401031503c52031118003806140350f600000c00300a40301c0c1d0340100200300003040b4254102001a16100a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 507109388 1250 507108138 507108149
    0x40207140c0a0e060607033f050a052403070e0f09071e031101050d0e160b040e04020d03140706050103110904050c1219080d0e01020309031b072c070f09 67
    0x1801804000d0480344000036510540b01101580d80c60350302300e011860500039465104051300c0c109400700741d00244034412540904403003d664044076815030512540e01c10102041c030381500c02c40500051520341d1044943c0510840c1819600504202503034070b19048150300301403444080f0448207040c240e10001901c0c200c07640882c290b00c5900310b10006031401c1c06140c0032007000c0c6040c140c003400745075070200784035800840e0910341360071958032030520040900640c02410381206101002c10050700d8050490816203210b0301d0310f601711440c0c40c407100c1a1904241411551992208018003c120030742050054550060307480c80030b2858681c44250b65400752016060050b0f980c01c0e006403540a05009001040307604031448460080e040c80d204110740c1c0101c1d444460380e8588100d07860b409406000f200d009103084c200450506d40665104120756400e010040c8003481100000511548408075417220826485070b125081d00038081444214003006114404010000700d01c030380c03029040301105043e40c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 507110638 1250 507109388 507109397
    0x80a0f06050604030f06140106050703230c030403060b01020105070504151403071706152502030625031b0f03090606080d141e030402040207140c0a0e06060703 70
    0x4011948900103081a4020301d4000340c0000b00441800000e460600d000c3e07115202c10403010000c41451440c1440038011007000842c10488240400d1084014201541c40c014004450070002e1a1804256100800e45031103900086030820511519108a091258083c0024082441d1180d0002c0052150b40213a07000702d040c4aa150003081c0c031804001500189407000e02d43d60b802c0c600c002a00358040b06007201c000804081c0007030314505000c69001483c013828504642060b80044c103845041ca4081c0c0c860103410709110200000d03079020001503020340c58400d0546404c403800003200c4900c5800a1030341052604064407407000000c2403954881c0641c89207009044880100000c80c0505084ca01c0540b546e8101903001c687e40001240399803510140da02c808044450072002803400d07014454070400d0300c2c081c280c2890707401d031460750056512a10003003005190106982e43d0410070400a88003042d242e00ca202c01d2845800e000c07080c078014008002d41c180075450100b0000d060b9100b641c00080800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 507111888 1250 507110638 507110651
    0x7050906070b0c1e090a0503031603030b031014040b0a140609060103020903100608072903040201030b03060916090b151b120a0206010f0e06041a0402070b06030c030102030601080a 79
    0x2440030010368100070407490400c13101c1c815450b1140c0c901e030808440e480c4070750440d140c0018189400011200884424a2040ea0055054409500030644000103c0c1c060103040c00b11701e60f44c0f01d944902c40c01c8000d28100c5411506083c20407401c034090060961000d40d2504d071756001084690f824440d4420004c495007603850b6905001280a030141e05072154043c4141942041c6030101600408c1c1605c1ca6482110142a60340f003425042540d051802203011520009001501550800450b4407034018180840c00d00380000201c0d1810f01c0454900315660440300c46075041c10741003a400c6008101d000d4051000241e80e02c00148045000b030003520015100241704802c0220f54a91946000310301000d61b01a0480c40c82d0a030615400541c06c00014004d290000c921109070444a42c02e50366060310400f515540c0c0421f1000030040a2082540300c400382184003400d0b503c1e80018511240f20b808100410700f0b264061500e0081c152403014866401172041103040c3e603020700c085038441c104800c04a4031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 507113138 1250 507111888 507111901
    0xe0a051b0f011d0324180c060a03050907030b18011109030c0105031905070908060601080403080c0a1e090504060906050f0616330603120f0509030105071707050906070b 74
    0x1045490710b20343e49006170181c1c080c4030040c010b0000301e209800d01207601e0a43c00b0340c445010f89612120f60b0140c0d1204081c4009105e241c0700b948000d520002e00c10498255a03100c1e201c5116440c401c9403800c02c02810070300405a0030b9000c1c02003e901c2554003292500b0040c0313240000e5211000020703c581042800301c0002c1801c903c0080c00c041806110104110030b051140005200700564018520742c0d220b11000306106510542001d48280e40560351410305440b958001440b55120351030f0701040143c4903071340000d044885810b0218020040c0c55400700240351009000640d980c07a4044100b01d45044070400a50700c555410b0b403120070b81260900c0c0e940180442c3d1100c1c3c0056844040d005815071803505000304d0304c2800010349500032800b00d40000540c2e050460a0720031a01000b400c0c9420300804400007400b440560101039082d0402c2c40c01e2030b07864000b203421a507007191900300080441840c0600010113803880f9400c240c0c189040c1d480c0c0440e18010400a10844900501d00b14031980040c85 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 507114388 1250 507113138 507113143
    0x21030301150c12180b0f030a0504030302210610020f0c090402010210050c0d0509010515060a020703060509160b03010b0415170411030c010201061d06040e0a051b0f011d03 75
    0x14440d5005010305941c1c0340c83c0c00002c1c00c9459035603084c0103d980c02030020510700542020341d004585003504503851561001c2c142406044058011410716400340440c403944000104e4103010211055011000703442c1403410000071030017501e0342e43c081d500300e15018005104007040d805009042070f10540b4242d211440100c1c80c0011102d01d4a950134a00070a02203c540c09000a00502141e000140010303180e10807818200c88040d0307050441c1e46074840d090303070280c00c0145c041d201054490040d43c00703180d600d4031418180c42007110160415000404c0d00c0c990460001c002070040d00100c040b40742150f0400f1421100ba1181e40120300340507240088000b40c540c13044641401c03000c0318240031304441c14545800380c03003440e4050544d4428080c101100c00c295205200302c0c01201c0b50040090024460b0400d00118030401420841e082910751800041c0e1712001c002e0004418402d0000f401111910762100d0b03501030420001134422204151441440e07039100b81c65080b12980c810920002c000350000091 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 507115638 1250 507114388 507114407
    0x307110a0f03060b0f060a020d0806060d06030302070509100e070e240304051b0105092206081c0e0109030b0a0615020d090f0f2106050a0b2103030115 66
    0x8000c5070440e101008110a54120a0300620b06440340486800c04e0010443c05004e40c0400c40d006031700204180403200e1141c80e50980101c00580300c2031501e005514036801751680380e0003e50141e800010200b0541c20a04007180d0701c41c40080b848045a420075850402c15440906650100100e4400d51100b83e910580c00d1107a600c8200c2044200c80c041c1031410b481e94004a50594060203000c040701c05070300c90940030211440d0f05a46840c80c04006000300a40f824007031041d080d8001c21907078000002d2103a4408c02d4041c1a452008101d251316501c0105900f843d041020780c00c0040900c0c41d80207d9030031201500070380f50f00844085450b542c2c4034030b07003000340310551020108910009241001a0f00458034502d008050790740c01502c680c550ba84800140024400d9500b4002100c8040107000040c19840b1100c0c0c0140c8030902f02d40b5800c0d2249020786600b03690002055580340d481052615000c3e80c41c00c004041401c83300920040f901000d43c590005100f08402d01c0038170744d01c004a091165454ac2c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 507116888 1250 507115638 507115649
    0x53303092a0415030201020d030501060807050a02011113030b13030c02010311131e09050c160c0801020f090a0e0f16030b0303041d09060408070609031b0f020109090e0307110a 77
    0xf0401d5a0089a41c0725034403845220a84c0036014250390941c0e864800c0c01800e0507107000e5100c50b1055103981204039000e510010164086558640a54100740358003401050044103131648444160b0440c1042c083d200c6001e440c5281401115405000080c0c002c0009007209409084c00a40c03486110308103007184c03040d2045004a0101d0810200360328404154004422644ca030300c200d06240c448050000f10f0b0002d0b940300158040038002400f0420180c840080000c0c8204c2c40c1c0d0941d140c0e02c0345c00070300f640c2204401b904042c00c0400d07040102d00b0981651030041010316507021540c207002e03890403c1400080e007920614200d10080c10107460103508585000c900c0a02200e80d103603590851031030041c034a002143d060303046000105d04405000181d036030151b60402540c80c07400107503503110001401c00708011414080d0032592865040944180c14038074a004d4140840460351b503100040c000b60664200340e0b080c031b14166403481204000004e503080c55a000790000180d8031003500092a00c161580071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 507118138 1250 507116888 507116891
    0x206130302030a0f0506060118032a090515270c040512061006080f16120911180712020d0207061d2407030b0a053303092a04 55
    0x103c08000302c0184003910300b40180d083c2c48540e03c0d1800110380c80c4001e18901803c03815860401e00c013140b4036101d480780c2010b00440c440c140c481130030207a202c055611303840043c0e250703615410003000850340c200c2d0510030403003141d162445010350f124001d00303054000a05809410401c0003c1c200381c08810484001d03040040c500e0403880e07400c6001c55500c038801c4400003640c50280200051640c0144800da000c1d01c4000308014642d5281413007a402059030700e80d06004c1241102c00c0100311042c0303226191149002c1c0c5040d036810181c400601c041e4083d244252070540707840004100c10300ba4400d10032032030000c02c2800565961240707941503019004299003d01003070720f0a0040e0b00d84001c010941c0340365207031581c00e6942c2c201c0000d0381d10703c62042c2d150030007500b01101b800107107800340b09a000285018005140385d42c01d0b41c40d00003044030f56543c103030101807503610106019604507000c5811504d00e01c603a03a4035841c2d45822070215407500c0400c4582c2c44072008105400818540303c489041c0640e802410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 507119388 1250 507118138 507118153
    0x50406050d24031401140601050f070f0c05090907140d02030102270a12170912101a031216150f0207020f01030203091b010c0204090503040e10030f020613030203 71
    0x4141549001e4401180c054040882c140b0b07129606006071860401c410300c0c4036071b60b560703120015203441d400781a50b40400c800070803005c1d0004100207a1003101d18020080100007034280400e04c000d0360000340042e030160b80010000c004030400c007181d00c0300701c1c1e109071900c0030b00742400c0c800b1a0180c058030178800400340d01c180c0d1082128401c2c428000d0300140403600c2d110000c2e40c661952035440c0d00b51030050300c162501c24501d4a100c83d01c800504104c04041c02c040040506441c50500341405215081034182c3ca910554015078040084002c0d048000c070045c0442c2025000c9005451058034895004480c00800d000180000c000c4404804010032000340200107511420600a5100200c02ca00c03410610700307a041d40d07510034400d492060139110010300380f60b03000c0c2d0f01c2d4583c001441d6448038100a2610719400041e201c0380260308580e44500c0c011070325107050084001003143c2c010400c1d60f4816500d10104003003026942c8400d9504d8050f81d01950380d4008291741c0d40024019007001e03415204084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 507120638 1250 507119388 507119441
    0x30d0207050111040311011809051608060a0803030a0e1e1606030b0906040b24030a180507150915050a08060a05130e0f0a0c0e09010903050406050d 65
    0x80040401078450300c0204091095035a10035000d0140c0c0c04007400c4000d4041d61800d103540903011f00440020f50b10481c0800d43d81d21180c9505852045070907411030001c611010001642058155420404c1110004056420000e23340c2e0759000007031260010680b910703601181480248056991950038a04103a162039180c0c908a94994068030001c01444500d4000038040d44a4400c82140500080c4500c2168a9030000c00c80680208481c0c50350191980013494402d613079801d840a81840c500c26008c0c2c072480e1080c112811582c1c40041d03410031891040340240011000b0400009035100c9041c8801e4a140e0200203c410441c96003282500c0014a01c46a80040d00138000d4811042c503580d0741c0c050f50356054280400022580718844d00040d445092010b9200640c00500c403152041d0122444200091880c610384000c2000544000100081c14840c02c0c03c0402c040e58844602402800380d070034550340003003d42c0b04501c2401d0030010003044900680b411070f01700112200c89021021a203a1289 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 507121888 1250 507120638 507120641
    0x20904090b0c033103120f180b060405040302151b0d0614040c050901030216020d0f02011106040b130201020a050124051806101e0306090e010e060403120608030d 71
    0x1600c50314480d240139000391a40d888604400501d40100161a0560890980c0c3c20740d2145a00d940c090101c0303072903500c005459007070791103032300000c00000a42864140c01402c1c060303c030203006082c0e240a50300303040401020a40011341c5820034400c0b98041e10301a926074441081502904420b60741014000495022002e0b031500442d007504c5100c481424443c20460400003214034401e04030010807028044200380d58001e0303000d420f0441e03240c031070225401c80950018000c0c0455003400c40c0c1c48000b0f001da0600350b5074414802c20045810200422440c1400d80b00d84c1d4010f14001c01d07440075213420002034011648240244444039601800a000c441840e0055980b0507600800308160140100b20009903132a10751081d0000c40700e20b200d94020340e10f8080922504001e401c83c3c06050125608460800300c000c60740f41c101051140d900052240c1c14502e82005452103000404003981c100404801101c1c00800e602c0c1d0456890f041c070070384852450413440090425a403207034030103010201c5e070500c050340907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 507123138 1250 507121888 507121891
    0x309100204080a1401090c06200109080a080f01030819110105090106080606060a051206030304171506040207080306121212010f0f06050d0906110a05130e09030706020904090b0c03 79
    0x2000c03c00644d4416400c4142221500c031000792400030400c5081001d03501520060443c10031142d5480d040502c01c960440c20b40d0420b5804940094001641e42c60050340300301c0141e007104003202e1078091035145483d000c002e0b0081e514100d4207002c0c01407420b12400d00948030350348040d01300c0300207000710314007031003203500070000b603c641106806610001602442c0a0048601100c1d40d80c48071800d00650240400032504014180c64140c0300401001c14150b001c020881200190b4000070300000d507501104000d100c00c054446405140107208100004240c02c0903a0ba000700140c2e040740030018944589807030605595800c03200e800300001d90003060345909445505942090303448480ca40da8032902c1b00e135090901d124040003e8020702030881250b089070041d54a5a0080f5404111078105c003421614560003014a413000c5580043d88001b2008040301c15001081c0d8021b041c100c510b04400800e440b8450306500500103070380010382c0c48455a540d070001c003005070001171960480c5005800b06070075500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 507124388 1250 507123138 507123143
    0x9010306151805090105011d0406080f06010f0602011a040e010908030a02130e13140a021807020f010b010504050d1703070507021c0f080d021c060611031207050309100204080a 77
    0x91400010815084c501c8a00d030480b070f01039640d0704d100171090311110609031042c940f0036801030702e8101c00111a07608020008001c1310b01d0700503003415458070f0b03060b18030b40139a030780000196414084002606511a004442020300c00d840c04038049904004440c01060701040051101001005204007600300c0d41c0070780344041a0a030b80010b03090711024036001d8001c00311105c2e04003c2040c0140d2002072910145810074200313002c2200d18001d00d580c00520003040003191260203185d08810003039096070402c140c1c10021002d8000b04855005080000d002c1e00c92030055a0007050980c41c00d0082010700b647d040480c240c9080348a40301d0518003070041c11a88542c1080c0c0c0720324040300d6140b1154000b60341ea001e101c0d6200311030703008411030f580d60221650402880303002c1c1d0540c00d10440d40014030560702c140c00c00d0b9444030300042031428110042c11600c0b610f00306184070b5000b44070002c820079103e2003c680040807410840d4507035480d610f1051605622403504e6000c90700204000481b000d0000d0509882403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 507125638 1250 507124388 507124427
    0x60503010c0912080f04080a0b100e070903120c02060c060f06120303041e060c0f091505030f04080405030307030c06061a03060d0c120c0510091a0901030615 69
    0x2402004035003102c0640980211544942602d10000d01001e0042c80000800d40a0303905183d84daa0b501c40c00c00d04203030416608040810700b00484c00b409031070007201400340c120340980c060905000042031003c203400f000741410601c1041102907801072000458499000f400c0070b41d100319440b94107403a890146d66001b40003508201080d21882c05003802820548494021415030380c2e43c2d02d90740002d6049001c520050b05401503203802003000750140c10b010b80e0940c0c480100c940742d050401405032425601c46000420460b442c080040d03070081c1200d40280480c282031440c1d440d030b818111302c6440b03245e01250b418800045d080d030402d600708412680c0070f801800c003005419a43c49c03136441020b6428040004050040000559624100c14220382160041c03100e0070001d916400380c083d420880321002d4504600300101080035151461155515070072034a0107003205840c2c5000c1125901c0c025211120544c0041148401c5074843da01c504000c2c00d109410040e00d0307080e40c8000c2c100c1303160440045a400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 507126888 1250 507125638 507125651
    0x1b0c210106060509180406020904090602030402030705100c02010c02120f0f060105010903030807210c030b210604020111031215030c0a05030c06130801020c0d020706031b030e10050103030306050301 87
    0x2d900503400e41d0360860001e40703031a81c0c0c5100b003444403d40090041048070316990a000308542c42d202c3c0d115110441d8031400c0f0040c1d90f400d0a0042501d491202d6014901c5030308502c2500b1030320341c1d0140841d21b2099081c207100c1c103003003280d100060010b080401c9104051040105031121501c00103503646210b20b10f20207552851b41c0f603e00454500f011800b014000c030b400030003ca150240700380c80030b11a00c80b8000300070140e881c0c0040c40c841a244080c1c0d072140003e8482c251410540352580001c03a4840801c4a000307044284922915111760300100080d0500ca5200e070204844030040c8100e030500180c400300b00001c0e107042000c8a4103280718400b010300a1040401c1c403c590b05181c5c0d00c01d01178a400034000c1404000d440f0400a25070310003140304042c143c14031000282003c003400900f01816400c4c010340749801000c08c0091610001d940b0040401d402c01c24180b1000314010400ca03180000d0f481c01107a14103000c40413031714203058a1100100c01d4a00300001040c19030590040c02078071405c42c001d1220 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 507128138 1250 507126888 507126899
    0xc02060d0c0f0507050703150b030111130b13090b2106011a0309120904020d0f06060311030705030a09210e120115140d02271b1b0c210106 61
    0xd600844c1e00090050b444420103201040140e04074250115407004045030a5100f0750209007542d0450004151004021450040e080c41a54460380509111056a4209071070001e442da032100840c8a0340310700640cec03800460025201c20700900202400700c0709801801000d0001c40740d5a04092044200750001005c0c07441c0c00040340c2040b24003500142d00141040350342c62885280a40c08200d209510550800c50001d24a1482c00341c261800912580002c0c00b0385800c80143c00e48061801c02c1c00c811204200b001032071900724081e26002030500e80e000803040c070249061040c25034042e02000e090030880c41899000c0360310551040c41014140e03004503503540c0c2854031509a503514400d00701c02c1007420400340304143e661440c0c4903481d80014044e0598003115000b080d6542c4a0781208140a41003200b0602d42c803140380c8100390409402d01024104864140a055181c0901e04080701030806069803c8560740003009107418450000302040b40300c2c01c1030300300d00000d1042c0c04404d6106509243c0005030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 507129388 1250 507128138 507128147
    0xa02120429090d0e03070f0905090606060906160204060504093009030b060409060e0615030619050a09060f020c0705090c091003110412020102010f050103021c02010c02060d0c0f 78
    0x5000320b0801400d0071800d000c0103680314100c42d580c0744d41521404c4000210800d400c130400004242040f0300042c1e505040959a0500c0801030825002c0d003010403019a25403181030849200e460640e024210343c1c3c1c04e5100213400741190364040c1c1d82c030a003880001000d00000c0341c402c03003c001070241918405d950301504039080300d1012500300045050301000304046003444c010203901180007080029101c0b004c3c1e03500000c0303820040710113032181c6c851020000700102c010301941210b10100c0041081e881c0140010f060002c00d48454070840c0d0312039011400083c055040407821a6004909104501884450200941194100000c00c2c821800c00140340d0604110301c5e1701030036000d070f903d03841c01141505000c0b400148110314010199200a401102120304024001034030b1043d111068800700c0740002420f46491509801519161800400c0140d03902c170310203c05c4820707070211020703400b030700c2c1c00140d80000710208040d40185000403040549142070707120580800f956241c00d0b02c000040102183c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 507130638 1250 507129388 507129391
    0xa0f1b06060518060a09091a0103050708060f191a0d2603010302091807150210061d0402010e1201110c010e1504061505120d0909020a0c08030a02120429 67
    0x244c001c5d8405005000e4419a90131401076540180c400c04040001600c0600020209920079145900461018400b410080c0f180303e81100b40e841606625082841c407000c1003203000052203070f09036a903c8107400d10002c051490489260010685a0b40000c1410810b1044046592008801c0081622120b0500d110002c2e203050780d030040c0c00200b6542c2c91100c48080c0d41c2040000d100e0703620405000066074001e0320107600502603190702520b03100500032500410b0300c920303401403103844101010341a41c09010382c2d21194803a409180046513100b0482c00710315500c0c0c1c0990405155400c100140841d480200c0043c8018a4400c008000011401c8400d0740c41750b05654201109075408004180030800c690401e240381c050f40c440328440c0076030b1140003850b1120450101b0351182c012600d802d14a41d084465800200702c50f03038055207024600b40008040d0542c1e02802400c810010011501d844610341c1130307414100c01c00071400201e05090600900440a207a0122403079035440c00303516005d0f1494400c0b503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 507131888 1250 507130638 507130651
    0x80a0605060c03070b0705040308030c0d1503032f0706030207050f0c0d060510150309030305010e011a0322050a200105030a0203071707030c090b030c0a0f1b06060518 73
    0x39801e2004c03030f83e84e4032801c40c80074000708108401800701201103448000190b000300c07000040e03603a980c0d60b88201401030714024100e00c40c61a65841c41000880c1d0040c20310424400c8101ea000c3c0d8071001140150310500c202d18114145108116010038801e402d0350003040d9131801041290301640e151480b85540740d24032406136402c104071601820001d80303c1e800c9607810201042520000030344071810146481c0d0030790700c1c1c000001c0e117402010701810740521405005d000001d03450300f155810181004c1403554903240c1581400c100000250950781c0e032001070644801c140b030b600e44c1d118aa904107665078110150701610186000c4600d40d401045848060b582c41342e062311480d045980d580c410800a4000900b5030041c411030790120345c4070400d2000682e200e294180c07000540038001c01c400500302c001540005500c18401c100303208540c6100816204650024907204041d905090f100b201d001f440b4107c1d610102d288030454504002c0c1d190050420340d541901c0900c103009408a0030700c113884d42680c44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 507133138 1250 507131888 507131893
    0xf100906080a0212040624050306071202130627080c01210c05031b09060306060702121504060b030102090a050f010e1806030f0303090709180b07080a0605060c 70
    0x10003125006140d4a5030151030404010300703240d1400b80c4040011070840f0102d8010f80c0c0c4220240c255000c902a40c1c038000d10130072031070001509200c003007543c2e150044d140c1d80a100740c030a83c46441c44800e40460307607502d4182c002000030b15030355000900031030141148013001100b240040310a5400710303851013048800a10003030043c000d0800055070042e000c004040031804094100181442c0c0f58000d420103240180c0d59203640745404400090042c1041030783c90b09022007007210190725030b55101a43d401050481d1007965441c002c0c40002c0080c0d101c0c5c0c1124449000301407034080c41c02444070b0f2803482203018040030301c00302d41881c1c2018200d02c52000040d900070300515050045007000e5055422046041c1031225021444070700203140c05d8142004007104901c0b5100f0030140e030a080c060382c1c3c2e5440a610080d819802c00c40305054031004540120310030155101c5050b24880d485860000c0304981141800c400c42c140141c000300341000407280c00c43c40c80e0400c03c0003d100d080c02c2c0308844062402d42c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 507134388 1250 507133138 507133157
    0x6030203120c0a110411130f0b040302060d050a020405120c010906170417090303180a080604080318010b04090305090108090609070e1302180a0b0d0f0213090c0f050f10 74
    0x3c9081380c40701d08058068001d6510304280d07000e103203074400424604a501d001c1078580e600d80550b444401509401c10b140d201c0e0140020401a241d03401521271028050601194603039408014030001e020b1070b801346501a620311a05503404078045402807958030b080c1d0340e20310312540711101505d11448200c120801c01c0c0385a0300190214040e059070041c18140d4010952801048000081c550b03001000d01d80036000c040744000380030346041d104000c01400b08501805062a10352562540c601000300120340d103044405455000d8002903209200c9500b00078000c0040c04c801d410f00a099402550300c2c18042104000401c0d0800d40c0000ca1511404a5200509140f400c0c03211440311008040d01001e40c800c11402c6440051380d075a00003014540d000900d6010620b440c140040a69584034082400b46040d40b0441c0003041c1c511500801c402e0b0182c070003e0741802c604413160014854244054102d005480010501e00d00010548080340c104540403081d4400f45010810700305070b000d91400c0402c3e0317180e8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 507135638 1250 507134388 507134393
    0xc14030a08011205010b0301060b04090e010506011e03020c0102040906050907210e120c01050f01090903020c0906130e0f070614030402040e030d0606031e150b1b0f0106030203120c0a 80
    0x80f00300d94807620030400030a41c000da2401280c01c1d507841d40c00800d10b01d0400311381032122900c2c80c844c1d06500404038000380300c0e03810045c0020340b1b0040c401c41d006081c44002c201016200b80a50100d88800d031154000315919a941c0c0441700003403800340175040c807540c0d5410110741020300c15105180101044071420900c00c04c04100c02c8003d201c41848450540901c00180c0708080200d40513113485034405c0000710b8140f030101e80c0d100700480c0581044101030f10b403107203800210740c1c0002c0240d241c4005440c08000354403488006642000e002c041500d000c1e040c500039802c142c002156140203020074100326448a5220b401c1a15417441e4001e0f2485007880c2071000034090700c0e25400c950000702001069a1401440f1035282c000d4401d030307030070020100b0b40350803407079801d81d43d1000501e00000784880d04000414003200e4242c40746400c2d1161140c044030101c1e84d01560059001c200500c20203001c2250250504021a5070107403105200c07d038030a0103080d0341141c2c941c9130348048070b03440c1090101604d2043c0266 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 507136888 1250 507135638 507135659
    0x170d14040302060a180c1e150903060518190507060c02130b0d050303070c0b07080702030d0c0201060b0d23130f050a02040f0e0c0406061d060705010c0c14030a0801 72
    0x5c08401d05410000c18a040119170038800000c00703070002d600c0281c09081401040c140040e026880380300c080b403600a1600015900a02d498141d0ba0300003c0800c0d03d4851940b400c40030005c180c0b80541d0ba0054401ca030749050381030150301d001c0a100b80242c031412a544e107420f03110a00b070f46070041d41040010010a46d051410390060640b010010f1102d6143c0110b074503046d01c0d50708111043c03000b01d41070809660a110400f400300383d01040358a002100c0b4504060025201d0043c0d2100089440d102c1c50b852071014000e40100019000c0c480d492030f114500b0034061006000c08a20751582c5840c441d8010308400d0502c01c000d8442c0c9640014031031030300300c241c0c0c4144160519081c04e07203043c0103568504d801641d545c0101c00d1407404081c0c0102d0ba060b24601001e061456001c5064829071604c80c04201c082e80120800c9618900c0c90705240310788000c800401c0729840b50b081c0017002540ba2002240b035140d000f0b0030b03038800540148a801e003e07400f0701284980d03d1213600354140108564070300400c00040300703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 507138138 1250 507136888 507136901
    0x5010b1b0d023a0c0b0903090d060e1f020d05060d02011403071701120b060d120c11060301032f1518101229010e0d170d14040302060a 59
    0x207800c039190741c1c68405803008103072441508050b0010340143e20007814003141e044a550010a491b02039890415128000703292001e189a000304425100c1210003c280d6092240101078984608124200c5482c1002d500c000c0d802041004071035480d11021400a003400019485101c1d4180c5600c801c3c0440400d0394070050b00010481c0d000c1040b4203001c10078440e43d6400060091000088502c4500754a25150751400f0005200500410f5005940f9001c11081d1090340070b030414900b045881d0040300d007000c807000c4245a0dd981d41003034000000008004102014141d4151110340085407034036002d401821400f00c1d0400164081820414481c0751a0124010801c030f2048240211105082d84045240800c208460101044010b008461500640d002c1c00c040b03084500090780511095600441c1d05604d852403280c1080f00285418000d80c89900000300d41c260003903401c00181c4c5405002000b00d5000d411000717452400e0903030360300d4021400c20403d4003e940c1034000c0d1075503a0300c0120000c001d040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 507139388 1250 507138138 507138193
    0x1203140f1314030a0f030606030c0e13060302120d0201200a080a0209041404120504050a0b09010c050303010e070e010903030509220c02031305030c1f1205010b1b0d02 73
    0x780c9070708240a0b80380c10802030890301c51507203da1145080b80000641280c4041d40f2010925041c5445000059032001080d000d1002c1290a840b20741403c01c0182c0080820f500b0082d0084494580d010a02c8000500203c5440e0281e00a0004260724041c492a003803691801c0040344005009484c000341c018030265078084407007180182460034100001d0117964030400700720002c0c22041c0c03d1005102510823540381043c42d504082d4a01881c0601081d1864024800c8001e040340104841d22113130b22950120113070f1500310040f640c4035612142c500d1444001a6803001c013288201021208a50107250075004490301a1580350a0412440034841b20600122145044c81071240a9102646852180c030340b200321198000d64039034004030803003644860070390800c911a500880c50000c559807582001240b180e05404000103060f41c4880564035108a0741100c2445400c200000c2020041034015010380d034241c00300c008915851a0f0425100c1b110000084016080407080d40b03915114844001204003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 507140638 1250 507139388 507139403
    0xf1009020d1718040b012003160c090b0f010509040506030f0106170f15040f08040306050408091c020306071803080c071d0708070e030c09041203140f13 67
    0x80345030341c4468006065407081e64141c4004100d0710580d80d10324410715280c03e07003a1020426619640006013444c03903100703058000304144917009020b100003801540c540107003c0581002152035440c00500e43c03881c0d8010030b628689401041c2a0030716101580c12542501a1182c40c07a00c0541014400a0032001304401c0d0180305010b11030a507980c00740305074001880c0d00051180303d000070220030742c20614102903900544c0d0003001c4038564500d8000322035411907404401350004440c9450940b1041c0505d510161002e0b10300420403061210b00c0009112841d022500700c0b1480c0602c40c00c0d15100c2001610294250f400350300060043c82c01440d103e199100040040207407184d4950b2032160660210a0622072500444420040c1d03e40c0000e54480f0110040049030003032070131400082020b20010028010000c6002c108030071914180610040054007130315141c4d140c40c2504000c00380358888070f140c5001078589051984c0c001da84083c0f06000c0c5241e40ea48040a0f09e49603000035001101103401c0c1d9914 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 507141888 1250 507140638 507140659
    0x5042306040306091103161e1a130b040f0302090a090c0b0a0e09130b01050a06021b01030e030a020106170d020714011e0c03090b1216020111040b04170f100902 70
    0x7990200074941d510940011f041d0031540c03c210b440000d11050040c2d04910444400c024052150405084180c04000c20f24541c1c448885480007500c442d529440858a83c50010740800d0241c0c08084440c103980c004e4500c0c0c602912a02060400c458542d500a060b80007480800e03c203402084d00140b01d441c00901d410002c0301141400101e690030b06a4100c114003421048000401262469560060404071617210615207000341c00394481c080f408803203826040011001c195603020340c2c002c86291a41804a1340c413404002e0002e4000d10f5a4080c48051800e121000c01307030003000081e05079100040d5409484a00d1a01c04c1069110f442821a03505201d500340ca9180017900500d410b02081c10300d580d03003a08a401c0c0d0309018125118540107808000020802d064400035405000c41d00507904040e007106003030010604900401c0000369494900348000340000f010704203217000c0c10503510075002304c15001400076581980c4000c214002201d03a00711a114594060241d800080410700103041c02114 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 507143138 1250 507141888 507141923
    0x80603190309091a030c060a05031501260612070f0b030c0903010e0601031e0b06011107030b09030a030b060c07170102120f0f0709061b0302010b09070504230604030609 74
    0x1918060004004c04103403200700005a8038081006810113181501c001e4900706160350010003a20004195525505043c01071584c107900c034007280342010307541000d61084100320071030042c0d0021060320640c4c400d0724043c40c03503545d00d0300100c2c01108031445050311098040ca414019116500000c140c00c1d020a414803542d402910280140a00741598201500c03556045280c200c2d00c1c410130f0519140707810b0070030056100003140c2d1654941c10400900f02004100e0000406a1400703204d900024150a000020b010103081e001026005d01d21141d00c0501c420814201448400c1c001c50301c03a291954808602080030390040108044100007010001d840c2100220500408010950342074580010103c01c016541074540c1c1c505821000600e02500d50601e40300c401068100307884806c07041340400880400404d4000d611108640c400074011000e140f03400e050160160f04144074000c0070b5409084906c80418090014a00101c2c000306250b0610341035840b908014816643c007100d000e980849013680 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 507144388 1250 507143138 507143141
    0xc0c05030f0a02120f04030f021c140c03210c031905091c020d060203130b010308030117060108030d09020111100501090b040207080f0904110406050a0f08060319030909 74
    0x1d014641e02085903858040850080ca007220b03010102c040e0603000e01445803010280021502100c1d04600c940000000b1800090000341c000a4815065401058440c0400c03651051a00d4505000e0301542c0c44030180307600f815214101585004074280c12468010b15444078a0302800c080905241142e040040700c038129a40c81b042c0590030300c0070480c04181c804440c503242c1c10300040100c14041441c030f040041e40c04295a1092524000c00198010000940000e5444035000304503800c100d071804996545c1c1400381e01079100303000300f04001410303048030340900078002907642c1220355040c01545031109d0401c01c45d00910286004a04100322844000001901004102031003c0d525000240551424010700c007102c0c030b51403101e80954014421a000b182150702502e240d4514581d42a035102e444e98000342c0180841310003181e00c100d01040100da10b5074007801a103111802034031000f5000040020644140c603040300c0749945540300d6251803004c50b480309603481c10f132446410169922607c0706143c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 507145638 1250 507144388 507144397
    0x1090c200c12070f06050414010f030b033301150e04140a0c020d08060307060804081201170105010614091201060b0f0a0e0613030b07110d0f020610060906030c0c0503 73
    0x1203041c2e21280f01480a00110700c0004003c0c0b0107800d25502e00340c5840c16000001c2c442c120710506000c450000a004203000707801540c0101d03c001c5c01d81744100c64900325940468100f0840b642912403101c1101c503c3c808543c500d9040c0d0301100d05980503c1d80e101d00480304030284000712030f0480d4442002c3c05418117a81b1030140517458280001c03440080c0c0c0c2e20024601104840e00104020700700c01482040d480129030b440580300c49240040c001e9603542000d5000b446420640c2c60b5083c01c0400000306a08944008546804628024401a680c1c0c2d541251007081d001c440080444003000340c8205071030417030180310a900c05007001203030319580d402c1d01d003886030080f1480c0b040c410400504140c07000d510049103011050220f49050500c01c80000c001c49a40b01408001c00030340e002004958110300828111194500d0101218601946d489004141800b11140307100944145008a25a9041032516205613000c0b585c81d201a0b52134110110050031030221200103118545070040301140c001e00061 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 507146888 1250 507145638 507145669
    0x60209100305061801030804060f14040b12090105010f121b0305030c010e030310150c20040606020a150c090b040b031803041512060504050f0f01090c200c 68
    0x100b034070b002e8060003c00d110000c4240d425558940c01400000c0061068405807843c510f401c80c03078540010303030075104881c0d150801d0141100104000602040802c010000103e002c0305c1d03111641c4035000c03034a0076114203020708a00810744074002d000071029180303260308090040b00e03080d20001c0b007040f080101c003002d07810584603030308001030504442009006803850582c184c4021441c62400c0c214840f5001814000c003000030700040c4070500c2c1c4920800f107d245d0745812035a1501c92880d60382c14028142d840300c003058003460070000c00003009800400d0074144e03d5082850f1180040e42606a0b0000303244110812003800385020010401e0f94920016201405050240d83d07642d0400142c1228200340358601c441c226402044240590150b041c900c000b040c1150030011031048418141c0000740079150000b80e0441d01d4602001009880411041c1c040c5a40106076034060340c0712a50803040c0c0b01e0782c84003500890f080341c0c50717a140c5240c108600c8001300035841c10303141d03040c51840000d89003d080c045031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 507148138 1250 507146888 507146891
    0x209070c1202061503030703080f040804081b0f0103050f0703051009090602070b090105010302060409020f0d1a0a06050f0f0f040b0a0228031e0306031e06060f0509130602091003 78
    0x801000d4141d1503c4d000c140c030b00450046040102590b07004008510080c104c941d06109a00403408100351b01013540c2c00783c1099400e84a10b08008080c9004403e103902c4d0840c840d40c0c1019514210394041d2254a0203032807880700c0303d03040d0340d58402c0a80142c48041e20070420f40200c80400550b00c9014462020030501c61880941e8494407403d00c0c80030303141d0140c280b42040c1d04d01001000180d0f81c0000301d800319280c5846c0035884804203007402889006030b105c40c040090410344a8418016080000c50301c020044841e80c1029441c0d8004581034069400c0d10040c02c82c2c20401000300c0301d5840060403000103180841440c03d5141c00b82c4a80d0340d048119008090781c4015400d202c07100b220305288501070943c903541c050000c00c0c2c0c0c800a00314001c8036500d030304151105c8802038100380310344c00890165800640c0701c3d81004c45141a004440c0c550041950100c1c9800c1000c40d42c94150703c00e036000c5610082c8002c0040d15000d03090140056007110444800d5400c00441c1e50540354a81170b50095512038a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 507149388 1250 507148138 507148141
    0x90f060c07140906180c040510090905090f0d1803080d0624021902030a020a0806150609062521030c030c0c121404080d140c0a0209070c120206 63
    0x510144a0400b220303814440c0070b00e0401c002164035040001220401013040c3d0704403d448480360100340f4826034000d40e402079603460682d040f458100380a0821070700b00c05010012556191503841e190305040e0030b609091f404c48440e034100c01d44541d900c0d4028410038a41da512403030f5260b440c0c1100e40c0c096203081c02e24a0302c0d03031070800c185a00406418186005201550105600c19200a464983b03003400161007100700e11001096427070400c0008841076014050b55a090345a6503940c1c0e46010480c3c0c00c1c031024030203903201c000c10b08000040d5210140068246c5040080084200a06081109505900600311030700e1201003501e0704459400601829125a10161f0251000b000d586034050110b0600d030070715044896003079002010030700d03050308540d82150582003a03604503507940c82440810f03007415000c1004500b800f004101100010b000f5111074031800060a1002c04600608121000030f4020a940d08003608012103125440b4141c0e140c6840f50074403d40d00c200106178030300221001a0300100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 507150638 1250 507149388 507149399
    0x102100e060412171b0f1c060609060c0b0414030304060b0103050a050f0f0a020903031234050309240403090501030b13020d112106011d06090f060c07 66
    0x2c04515207443c080ca000c0540388103441d014464640f0103002c43c4064031842e01c4001e00c4900c1c04007540c0841400d00b0b06030f0395a03080c040c0c0300c00c403109080c10030070703016450010001005030283c100c00085500d940c079038444c0d4510030340718100c00c241c00910a50b07020350743d40d101e0b1104040500085104901c0340702c0000395110301c0d42c001000c89034005c00410500345844107000d100f044107180542e001c076100350440b28507510700010002901440c03014541601c000b01d086d0a03840c030100c0c00c25116611070a6040400b15000c01d19403409140e00707840f01c100980351144c003444a48070b04002c561241c001e6044460907555460b601d00c880100300074102144079940c0600c010558800381c244000d00382440d060060103000c200040c80320701124403105d2030b9680040c125110b811107400c031500313410300407080c0d64076000c21040000c0c0d98492400100d808603503000006101e0360045685141d50a19200c034001190b07440404e20a09512820b00c59a000014000e07102c100d66503400200b60540030680903000540c5000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 507151888 1250 507150638 507150653
    0x6051503101d15181305120f07030f0e130504030809061005011b140d12050f1b090a080d09050105040326130603050609071704020f0102100e0604 64
    0x2500b102005001502c2c2071140d41d40c1518841c0e4009103101802c50b40c031030380000000d8403400e182c481c44292020610402c0304540409902400d07041c0514291000c007000b000c00c13880fa611500c84555240b45090105001280c0710303a10508410f010347c10246410161080090040c9441001001e03403a500c0340c0070042010340c098049500030703100200415641c1020014010741c400c2a006107410080c0000c0d64402d5410404203c52000d904803280454917030f1046030650316185850500c80100c0d2200440b1101c1240c0c0b80300d01440b0720a011100700040e22041c2001840003c0302c4016800c0010a202c01420781d51152150401480403c0060005010640002d0b040311001d9005a05208081c031041020921120303408040d0032440296810071125400b03401c0043c05044103140401120030f50114842da0540d0209028910440d40c2000d0303031380d5504080300e01c1e440010304a507002c0900c4001c1001030030107441e0a425140140140c411441c0420140d400700c417406031001031664091014031040c07002c0d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 507153138 1250 507151888 507151921
    0x9030a210e0d020a051909050c0c240402090a0b040e06090d0207050a0b1b0f030d051008193e0301090506130303020403081804050114031b0406051503 66
    0x10b0300d90705050891900000c402a4803842981c0c06080b01c0c41c5c000701c0d110f21444210001c0d000b120400c000908020ba4500d0042e080740c0e80c1494607102c2d62000c96028076400102c89505440b401d252610396840c1d07400e000740140302501580038991525094401d075030b00c90090140c102c190341c0040c562843c016803001e141a000320810000e540000600b4412070711280d200d841130b1980d5958040d1340e2030400e400490000c0244c00c1c00035035070088820460300c507200800200411034801c04240f1450712000d84100b040e00c00303445100000e41c4182e41041000003005900800540680341244a02007803000744c84800725130800310b01e005204107002e0b08010101c01c80c90986000305038020400810702c0c0e034465642d2100607045e810851079140301c2408152003601124090f5900c2000a0340f614040e11803c501600304244c2a84540c1c03c00f0008141a55070303030091500c42100034010003101c040c030700c1c01c43c2c8005510340d415074200e40c030b1b5440420a51214007410400801410f00c25a603880c01040c142d6480b81c1c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 507154388 1250 507153138 507153167
    0x20a170708060f010305090c120a0605060625030c020a17100203061008090a0503120a0e010c05030a0209010e0901060801051f08061302210114040203060d0809030a21 73
    0x114424801c01d83c40e01c004040c10f002e42030a000031070361034000e00c2500d06a401400c450b8424400300d03c800c2c6180003c600100350b42d100319002e100d01c2c1c0703480c0100a518050356400200c00782d510354010340c0184078800301205140c040e080200c8669001d8001c1a45034006c1e8200a80c244140710070600b414030304100400b0080304ad010304604506044000644c01a030002d00501080400c0c0003242c03008209000c0000019402401c881e40c0c1e009500040801d1501140c041000d80c0c94205a062841d43c1805000041e914a40e80c8501d19a075a200c030380001e4000002c080c1c104080d28080a21684690710740d40c0c00381801e500c581140b50b2510701084078030920454002501000716a000c5d916a4216060980110301100d1060400200c411528000d0040c41d80b00146049483c40700d41014010340030f1941600c485071078480c409622103080c08180d200644505410224100c0c000006c580000c0280042c114001e0694211000c40d4890851946035407002003115030052604200b03480e00200401d10409 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 507155638 1250 507154388 507154397
    0xd110f0411070206070c080114040605070509101409060d270f0f0f1509031b050601050906060403020907050a121a0f03031e1c061206020d020706020a1707 68
    0x90100980c0000c0c0c028542c1c001c0c014000440d5942c03c01105410180c090003900c0c00800850025610742600302c582645d00340c49032440e0001145105101c0c000300e501c841b0000d80801039492038400200c49041c0c100d0311a400341c43c81408025003543d03c0000403c8000c10714900411241080881141120300749108605410001c50000e000034001540f007070011074121121400c5d955890508030130051100340010803140c002445400c550a40d5840100c002d03002e5070321071035050f9404924511600e402c1c400a4070550141004010924003100303c0e6034002d8015100c0c50405a407540861250001038880201149020402d030039059171002003c0b460001d030703c50034003101c0c0f0b0703452400c180c2d000340340c07401d41c01a01d1740e80004546880400441c0d60010007003400080d8082c0c1852400889d801003644080c2d41a0300b03007911117404649028540941e44140000301005410740e40d040300950004e0007000165400b8095500801c0d29072018181103d5152101d036030740310385c0303444004112000518540520 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 507156888 1250 507155638 507155651
    0x30207050d0f110307051e032b0e010807021b0307150504060e0607020f040b04091e17130e090a05010204090218030f070b09060c030313020a08010522110d110f04 71
    0x990316010074960200d00780c040d118907681d01c0d070023107414111504c1d03114051604a9441c6d200b020008880396450411a43d1011042d24101004444482c001c1e40e00d403006034042c1101c108401440c41540d00b00340d83c0101168015541d403c1c2c11100c003008108040e01060700400d0403c030040d0000c0039010045002c582d40f9113800b1159001500000f0412027030b5000da0360714412000e07907450342e0b400940c4c0c0540110004030005405851903003100e80132071040780c900191022030110394030f516054681c0c045806007004105030800308000111000100520410b00c121528200454001e01c01080900200720016982d0101c06203003060800000c11114081d030703c00700500380000c030041100b4080d54080d140a5680c0c41c3e0901c0015058050102003220710b00000050041d00b40e011030851401d40d01c02e50b0a896015541c0b07990608030b900c11104061940104511605c40c030385602401c1e00418030618042a04a000c0404280c0a1300d4004c1d044504c8500141900d0741460302206a1040c032a0803942800350 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 507158138 1250 507156888 507156899
    0x50c03180d12020d0207051209010207060306030b01050d031205090a02361b030109140c0c06150a09090311481804110a0b090d030207050d0f110307 65
    0x40d01109030841c0280d640482c0e80c0329880c41d01d170103c840d10b6170004200c60b00c916086984c1011a885050018094811f42400183d00c50083c0503070003c6a8005802c0b02d01a0b203081c3c01d004000706c00407000ca04100040109000d0b00d1100d214841c080c0c3e2005000b05070340c2c01207105100e24180b00c001010501400510000040d411825000380c081c180d101c03075840c85403104401c4100b01010b990150308466008030022591a1a5074400340c2c0140b00d40c1410001a19401480c517590311401c942141107800441c0010035121041e02039084089003d001518215602c08a61040710a4001c0403000104800390708965504200000e019640461f0000490103140c42c206000701d01c4170200704103035801301da0403840d0070315040c21098442c1c101c041c1c07160640c0342c2c080300081e100c1002103c0880d140b6525018544803800e040d9410f070300343c80fa0b592800b850085020100201900182801c404500c10341c80040703220703255000080e40f03040c070404403058801d5040c6448440c032008078142078026803000c81d04011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 507159388 1250 507158138 507158147
    0xc02030604030c03110a1406070903020a06030c090509090c03010c0216120f1e0318030b04030e0d1502090f100905120319050705010c030b130f020706050c03180d 71
    0x200542c0c10704120707450801501c0c054500191500918645010f06030494080c000c3c42070a00c03124140c0002030350f00079902d80d0380940e40c40c040d074040650000082c0c03200f03100c80c3c0d0180d84411450b1201d418014482ea42d602c0014400c0802191046542d402009180c0f1a40c1000d01580c0e19415882c0007801c4e0309240101d5551400003a0306c40c0090050145c640c1c0700034080001074076450550411900f11041c02241000c4400b654103020031000a0001c4020b842200300d04041c2c031054130340c0040030b400151240c0d282204c84c03081c140e0700940e004600e402c00c82c2c00980714440d10a07454113031880c0503840f0038405080140c21100c0c202a2405041542c4000001c4c6500c0f443c5001510011606c00d5135816100316014618002e0740040701c1340c480d15000c881405604400038240c554411002409009950035044040d5681c0029040e003003a464086840c4070402134101c1311103824010401402c001507916400706a50040d50030080c20034000040c010740701901400d18242c422100024140307107a9a180c000c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 507160638 1250 507159388 507159391
    0x9060b0c0d0e0f041802101110050f0601080c1216030f09050a0204090302030c1501150315090e0307050a060509060709030519110607061d0c0604091a060403051605010c020306 77
    0x14461a0744407240c14000000d49890017a0039000780c809010b810141c0c10203403010350b400ba18115503100d0f10030808081304903401410310482c0443c000314469160003006558505020b00780c0c4a07000300038024000c00b51001c155a92050b0031000c10082414070384140502111007120001050500b448a5100464000960004000c2c0c0c19200003030100d00c1814201d0440c02540390400990040f5210040d501003004591410307030700003414201600a501e4001d8044601c4500301d1124101989010080000309a00613082c0c4110803042e41c0ca13140e0543e4840782030031030003141241c50580e80d10520100704030801082d5400f811074241094101e007035480b0700313907110111124603501e202249050401c0000a08900801c60405000503032514118074181c0701400c0c40c00071b41c1003607a422a08071202030000050741030141001400300d0345454106180040a4110b1154410010fa00b00340e1028903503c4140081c40110b000c2c80180054444115502c940000c250348628100300c05c600003000541c0d00410200e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 507161888 1250 507160638 507160669
    0xb01090e040f061e0203060118080a0209100b041e1a12040c03060203070c050c041802190e072001090c0e06010e06030c0705010b061216050409060b0c0d0e 68
    0x28428240c510709000680b05901e00304130f00360810441d034100d40c100c540145001741c100343c88164151552128900c00380c01d043c42500d1042c0d101c1401640582000b00d403840e041402411802d048540b100401c1207168081d83c0012402c100003501e244131801c030080e55002403e020f10481c106401020340d00c003014040d0030b4080c40c0c80c2cac030000c1c0804d04100d501c01500c0000c6901000039900c0c1d24103480050000c03412080c0035a1280144d60640030b841c074182c8104100ca554910f05a02014000c0e02401440300c8042c6404045000c5501d010800303000c8800d0462140d15075030344002052a210302120f1094040c00c541903040c1e07040600500c00200d001c509075080d610207189520840ea20240122112140300104607044500082801480c3c00443c00804100740114000d002c040e40c5042808981c2c4203003c00b0340d41401d160004180c00d060301e03a83c503841c0070300d6510f0182d0500c0c0d01c882d10034003122443c0d40004840c1900060340b03400f00100384141e41032005503081c400c04103034800000c02d00c0c020001052 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 507163138 1250 507161888 507161903
    0x11d090f120a0309020306130b0a0905120703020705150306030f070b09100216030605160c150209150f120108010b0d2d0809040e03031e040c0503061005040b01090e04 73
    0xc1e940d4243c401d40c851a880d035001012241d041c14107001c14020100c41003c191920000c8000091011482f030081a90311070740300009100041c215130100f1880e820040303049046000d0780b02d0014141c0d444008600300c04022025281d40d90034040100340ca0200c041c5510b0f0500c4d00002e804024003d004801e0310603e000907603800c1c1082c030210404034101040c0e000d40c1e14090a9484010050002c958004d900c10b28100b9940c140a90011030182c170b20a40d0035070300030212400542003040d0030040f50060030241501400313000714214070000152150700034610102c0c000d400842c1300003806460508660040c00414020040c5602d240045a80f141c80780b20041c0041703034070301502030208045031010781100b10142c3c0110104038407403411002944c011242e1074401c40c10301d011824014804004c6070b0250002d0f84c0700200d40751010340406110341d0000d106039400c00100e480021b40d928284502c51140038210300121000d402c00702040126400080303040c2c10017210a40c184000180424400e0300140c01409 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 507164388 1250 507163138 507163147
    0x60603060708151504030605070c03021204081e0106051027030f1b0504181104050105010914030705060d0f0516050418060b070f0507051503040303020a0e0603011d090f12 75
    0x913100050b100d583e00003401035143c07004200141d507011803052040386c0311b6825038110540b0300d0b00924903401280500c0d11a03411403030100351212156509421104220740021402c0c0f540c801c00500156140c14100003c196110740081c01d4203c0d01c03094a07031190102014104950664580104906100700300800003001c1d000080140514003007940d004100090040c040540d19040d211030f0300e00311003130032604040d081c2d0040724070385030a004041c180d03041a900e198031540303810800ca07020b4401c5501d030354140c0100300c03001c6042d84aa0006100b00c60b040b00010401c0d9a0080140b030403103800401c0c0901c500c0985074050280740e8854116402c8451200c60120510fa02d00803800041c1402c0c0e000100120001401d03504102803007058070201d500600503030385560340e10001d20107403034051008034050041c200b00080000707003e0760107070245520b24a06170b0541a5a4400320741e050b0310a0700101d8085001c141001d228411348015190300c200f4450103003403a0205511002d50710341c0540c19200f0140f00206 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 507165638 1250 507164388 507164419
    0x90717031b060f0c07032a0201020f030c0d050d1b09031b05010e01050c011107061e06030503090d03020a061103012105070501031e062909090403050d180506060306070815 75
    0x3041f46040c4401c3c06015022050012608003588810b190490242c0201c5804a90700a000700903a080a000e00020300260100703039804840c654001e002c40c00d882991101c2d01083da11414030a9000707019a91a111881030071410500714182c5111221204910448018410f80e68455102d4031011404e007400ba80760007583c070580380503001008884410310004980c1c1420b000702600000c00c100440c0d03a0000758558140c000c4803d84087d4003000d00240d0040100c0c40305401c007052a100e1103030003032059900a402540e924410380703000c000803554485010005101c08400300c1c0084480000090104450f40700301d64409407181702c7d61107042d05160b80c030100b40b0312202290038468491420881c0400c48192910303c0c440b003055007101c007946000c0c0300412060003003581c4030845130f91071401032451120355030704d980486d81c50b889200d0700075217140c44401c01070110091043c01d0b144036100ea0050051440c0400605180920040502042001d92401c0c03108a0b20030481007032102c1019a01d0089036070303800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 507166888 1250 507165638 507165647
    0x12070b0c0106080a0615292a1509030909040b0604020702090a060609060e010c111201180b06011707030237080c0f040905090717031b060f0c0703 64
    0x107900c0303d6414014901650100f00c02c50340301d03008240c143c61081e05011b440d000340c0700100c0009040007540512070000d1001120b044000750001c220f8000352030001d80400d0000c400c1e0390010b1643c0d2800c0c1e61142640905058003281c2981e48901c800c4029401d0103000780001e111a200a000a0038403980840412032544441d012a0f200c550060306d40c02c0d890a1100b001ca000701102c0c818500020220031001c941c0520807070450300c40710016921000418126122000300e03141080c2015030191840e080740410800a00418040031003082c5004880080d50401d0340c0c0402000308075a0400c901c201d8440052060040c40030740020b40741c680162030794046050b103c1c0c0b600340d5000900e03003040e1040c808261145c0039980c107140d15260340c1c0c8128441c0c0751030440f030410340542c40c1058a02102800b0600601c5580d50246070303c8030110085800141d558042c002d8101c040c1000b09819810000c1d60100d090220f000765400c00c03c0d180300810343c5183c101c3c000220004080d100c003d0350100013500409040c801c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 507168138 1250 507166888 507166901
    0x60a05071d0d05070f0323151f0806130303061715040c0b040308090f031209150f0f0a08011502100b0d060617010e0106151112030c030103030e12070b0c01 68
    0x34280200159200c0c01c3c00303447d44201d00b2809607042844166054080d9010454113404008101b03890f28540761040c125200c850071000100000003142c6c0c00183c5440c1c1041418090b4010400038203880781c107400c005040daa42a04030505030301c42c0440c0380d1420040003a03010712031042100c94001e1610b4614000b80340d4000380e07000b80d04050011501105001034040241080c42c41294881700d400c01170360600d6140c00d80001d844800d1b8034117000881e403500700900c2280c02d11109004180c41e051030002408240d41017080410680c2d04049190428160006c00b0315024021403c03e04a140b00120f10082d524010164407400e001c0d00d45250226989500341d6080805038480414444a510743d00d0f0581c80f4181105492055828407008805613030040c414401514044204400400043c98042e1a001e070040403d4880340f08100c0001c21411459001e1030040740c5100c2d00c1e5589500d1428010700341c6814060583c400c40a11079141410780002400303104981c4080b4000303440d1001c6003447ca004000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 507169388 1250 507168138 507168149
    0x18090114010809070b0f120105010804150c02150928120e13020a020a030801050d02030303060f15070309140a0b03061318030503040204140609040b09010213030302060a05071d0d0507 80
    0x1804071701445443c005401030009922907024003200c48c0e03170741c6004480d48041075401400070390b004814106000c69a412040c0364080c14011100c0d104800304400d803500c1011240c5000580050b4401201c500742c3d0800c0702c0e250f11026040d4030690105481d0f0030440490008210280006540004401e40750310440c442c00250024045459a90141000e915240d11250072000100743c2000071801c1d00c0c011141c100c0c540d0b0007900441c01d580d1040c0c244050842070382d076004c1c2d01c40b01311152966022450001465118800d40d00d520020740b42482c841302c038420080758a03100d0703150340000b449072584403001c2c0e99002c2d00803940c224840984001a0005113842c000c0c2ca200000d00c8984841855000401075000c1d07482910100310700c100203030840c00e0030f070002e540c401c0c0d1048644001c01c0219041096540c1c200c00c2c540001442c1c01e0b44a144e208501c0c645600480c0981c010404100d4414498031840d6880942c0d41002c01c44441427030152080c88200060f0244038019004d03440303040c0202089402e02604 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 507170638 1250 507169388 507169409
    0xd05160c0515070302070b1c050a06170312090616031a03030307021f0b330d0501031202071a07051c0e0a06091202060702030a171809011401080907 65
    0x201d49a5001c00d6002c18001e074050700c00c00707000240310f41407003084230b81880380b00c0d10209407400d030f403800d16002d0700c030282c071005940b41c60b048007103007502c102407115007a800c01c08011655114907903403500c0c024000500000ca140c210310200503c034480c20500c20034100c0907160008416034501d10803940e20318507041880d0140f101008010200d60002280740010075205154122140d40c000c2c8031054501840185802001e80f1a00014000c08050303c1c03800a60705a4601c070b001c82c0000c2590050340c1221240c0316074652101d0040003800140034280390340681501c05400318604010100903010700d00300001921a00000d005410b006080c440040c10758028408007806131102d94000f0044625a0704d154451030755a04001001c40c0140035800c03c8540b8044000000e06558003001615040101e09036018080c00c2c0c3d03080005583c10144081c01407030007104035111400200500d903004800e00420380190004001800644460031b11180259400d103000311040e0b4070f0105031424081c00d540602a81c8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 507171888 1250 507170638 507170659
    0x31c0905060306010519030e0127121e05070b1e1515030405010501031a150405040303091a010915060c060203040606031704030303050a06061d120d050706050106020d05160c05 77
    0x70303945a00881a230b0030000b00280101180e000301c041c2038005a086000919091540ca0070025140c5040c0c404141502e00344281000590380d05a0812020700581d100003c0c8002424001c01c030703d102c3c1c01500030841c0b8100c0e03100510012040d661585025142540c1020071002d498441d55400b01c40f018101070140d02251682001d24006000e060b0a00080300d1000508400c1c11030501c03210011071082200b07c0c440610351000da000e100040c0380c007030b002354109501d0301c4120000c42c201c1c1c110400b542000d00d09008840d132603c074600c0c04a40c1c6c5070701d0b03001000c07000c1c0f5420011540d000a4240300e141c1c0180d001640c0c1d8070745146c00b20007402560f00080414101060401d00d00d0242d90283c4110783c042d4800380440d6941c2008202156914060031010400505014840903030f620611034503082c000d046000c1c0000100039641c68020005014400078400140c03410401c60103009050040c006400140440144001c0c0640316004140322568222003840300c800501c002c4e034011100801c4040d00c80000d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 507173138 1250 507171888 507171937
    0x1a0f063313030204180c09050c07120206070e12030f090604030203070e01060e03061b030a091506050a050604050108061c080f0a0206060306100b0a0e1e031c09050603060105 76
    0x10800d284000d901c128500311400c43c000005d0207604240340d071711403104404903062400c207100811016103610201c050501c040c000240c01400080c00d001c000307130014811841c201100514510007030100340e0182020403011168001c00109940c9007803203840004d07071560840804107107107004560019606124461002455240310303511035059801607900c881ca109900030900d50788501c2900c100c0060396550520080010595024642181c4040d0300814128039540b0781084d40e04044011042c8640e4440c0308100d14a0008100d8008007000ea45440c1054600b10010702450001047d803405240301b9502c4200c0c60008210100c0780c564006041c0e40c580e25940f041d40c107030b600480344940261140c030000c00c200c0e20340041c14920a040d6160a050700c4c0341001035140c216001048400107100c1d44129051550341c40024001c42e5010030502040034507256001c0502e8501704010741a5006586001100302c6503202d81c10806a03403060740c042d5038a8803200012180c52040c5900000480b441c00a0300f0710 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 507174388 1250 507173138 507173167
    0x812090f0f21010b03030d0c080a1104060804050102160c14180c070807080705070302121c14041d04050706080c0901030b0d060f05151c12030b0d1a0f0633 68
    0xd242341d1651800c1c07460f03a410b5840412200c44803598040c00b8001e02007088558840c2200a038854418800541040238001c4040c844001401d42100e071114520028030031440800d04110400314204c680700504255020500c0c03110030b01074480410a9000201c003002d02110504440d080780d4000340712555140d990409684805003800124458082625000e032040800114240d07038a186408d00080410712032000e032580c2550000d2006101c2d014040020074800305102c01c0034001c29141180b07100d1070a45011402d149543c0c00101c00e0080031030502c80040e640e1000c1d80c0d5058003c0c00c0c00a16441500002181704459540052503035041900c11802c1701c1450300201c1c01070030b815280c100d81c0f07c600c00030417406015140e28442048824018040410013800e040e485009850a001608880700408225180c0c40b80509407085405041da0400350906d158199600070a8419030000d941402c00002d058000340c14084162035070713210f1580004801c0c034050017066080180030141d03a40116078406c60b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 507175638 1250 507174388 507174401
    0x10305030909060402120a1e090b06040c0c05150403120c030c030e030a1b02120601380901050307090f170c04050121050102040812090f0f21010b03030d 67
    0x40c041e682c81004038509003003034029201480411929080c0660358208004000c02c00050301c0010f50030080c603c0c03044d50701e0324400c810f2a03d0050441c00103a15102c000d010039140c0503c00b00d000c1255050603800441c2c40481c1050616004400d00340c91901d0320b04003120007020507c004a1402e141031300100750340360154042d401c115002e440600a020303c041c0c0180e101c2c024002c000c80403a24100035900c030f48090402030700c503161009095422840d000030b4402e1500000760010000d010881c8504841d000e000445134140104401c58803040c05440ca4000400b409129109418081c1c0440441d51280c069004003024020701c11558107025034a09100101030300030014555640942c0400101038140390140505940198261b0310000d4242e00d800c0e5a07080d64410152000c0d50b00b80404034444c0410b005843c0300f112420700c00e544545103a42041840300c410605240300b141c0700f4290b00078548804042424048050101c242c5810b000005503000d4294851040c0c0d15000000c0e030341036018000d50102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 507176888 1250 507175638 507175657
    0x5032b020310080c1e01200d020a0201180b0405010e0d020409080301090f0e120715050106080f0c09030c0f21060901150317160b041a061816021501030503 68
    0x7256044c42907402c0c44962100d04500c1c1d03186a50003c1804040d502850729000007020341c241d1003000881c1d4511240c20452201d41c0200140c1040246505640e172140150000001c0c0f502c01d1102d09107030400c03000041c422072290b98123010510704882c0c1c0070f43d120840d030140107401a20620030750809182000f070b01d034402d02615030041e1508081407005440c038446e40c0d0803a5107820040c8034688c1d0621810b1550303001460100e60200c0c0d24800440c0000c018080e02d4000d04040c1c881920303608098450090414004008220f010300a00c01c00200d03680c0041d0380d07411002c0580b80c1c4c00385003415001103900003070769400c50004542d008055090b0038800181461140560000810440390300c80407510b0725180c1c0c0c3c4005000c40301030400c0014003004400080694404042803c0e4a031074681e6a014864a811101170b80d00e04075582203070301c00104ca80c2010354842000c0350038003038030191418080314850001d054840c80e0016270859002d01402000652840c00303103407a22480c20340c1d40c1e28045960f5031001c03960 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 507178138 1250 507176888 507176893
    0xd081b2206120207020a1701020f040608040302010b040506061b0319080f07020601050d060509070509041101021203010609030f0503070803130611070c14040605040c111905032b02031008 82
    0x1582c994580e209581090398024404003a5030314103900151910307403400000c03400e0b546c00c001c01c0441d401d460340140000c0c011916030105521b02420b01908540d1000146030290f8184410400c0e9503032441c04032007402ca10807003015456841004214691300518912a60503c0c2001003140143d4100c6903c51203092100d22001d03072942c650030101e8403038900b840f07519004440c9184c0000061207a420240d030014808045074405079469000602e01103058a0948150030303682e040041c0c95031306100a1f0145104003152600e15490000010030740035076880050000881c103034149033004000d100311102e6a0300b00d69000e8837402c00c208000020002140f08442e00d03458528120902e0a464007950041c43d0032410030040306242680708132240e90081061540299155004181580d0360320411f03404900607500c8609104141c0701440c90000402c08407456001101d01a0b000036000100301c6950440a015200c42440565200b82d1505000000035002c90b00100810091005040250007103801d00d408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 507179388 1250 507178138 507178157
    0x801090b090a020d0213180b09010c031a010c031403040b01260c010f0e0307081e0613020d0f0b01080105060a0501080702060a0e2a0109080d081b2206 66
    0x715569600b02040c02500031603100714400c00340c81e04249010fa91294a080032580700400d171815183c00c000c880c82200e143c40150103101390004244034641071062a400e040080008a802400c60140c00001090400011000308030415204501c0703103202080a0280c0b9442e410b003450102102c040034060315a00c80c801042600d045424400000c0b22801c0a40c00340c000385610000444020900325032400c02d12050400007400323510100032003001880d002c005401c0d651008414003820041d581ea003580309512510610213004101010004c501e81c0c100c565000707490942c40e12401010043c080504507408690000903141410741100307200300344c201c40700c0602948800041d542a6410340303484d001a0300400004690219a5100350800e0030000122010803d50407005561800e1354034a0002c07419035000720760600c1d6040401b0b80d02500351000a07003440302080c2d40081c290480101319440c43c1403c108007006101540c0115001c0106602c0b04c5080100b800f034408045144a104100000f1603001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 507180638 1250 507179388 507179401
    0x40507030209070512131a0c040303030932061617070311030c070203060a0c1b050c0607061d0619020f16060b1305061e0f060c0703030809160b0c0f070801090b 70
    0x1d1f054881c806103895542002d003180c0b002c80c001c041034a001c0340c030300a0720070402c00900c2c41e03814103010303120801001c044407405802089051190203054481c451aa135040340700943d80080c1280142c0700001c0500702c2c0c1d50b40e0f811f001c4001e070600700c080b007200140010074810071a94000082c85a54025002c8580c5900d80401d00c008440f001d4001d9400149034401400841d000708001a05d07a0380110116140b900100b000112540e001460440700150340e4134442442165124004800820850280002d4a4101d0700030322150091703140d0442250340000c41a80c10b030094401d42c1d000c1c2e01c042c941c00a22030418602030b002440d83c3c0700000c0c882c1c50a600508483c8406006452181c0006440c034801c41d501d001810510100d1030180f19407108041d601c6c80d1464032004041c041c2d81f04940000c0014600d1804c0c05807001c07201a107100d00c140c000030300e9541001c0d06031a0303140c1120b44003018507580e8090464880c1c2030644042e8403111071b00505c90b00003900d820540002071610302a4844c03104c1c540300d60 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 507181888 1250 507180638 507180683
    0x1303020706082205011103190b030708060705161703150409050c010e0f040f05040b01080109050705090612060123030321040804080303010f0611030304050703020907051213 76
    0xc0320b03025030000100c5a07088098140001c00c0b468580308200100c0d03d4003c02c200f10f402030700300b00c4440030181d5560f1811001200706008001c00800158060941c0d141033a00345c41e01c0c1c40f0020116010311000103988003a800740c1c10303001105643c009284160351804e0700c16461059009a0302c8403151100000c04080610f06841490300c516801001815006084c20054031a1800901542e138420190b51444205880b9401858852800d0120005842c60649061030030040c060b0081c240c241c3c5402c0221000920028810064903411070701920365550300b17000a06000ba520552510f00c0c0941c0c000000c80c119079070841c4400c2c4c03a001018040e02550303102419a40d02603989100304c0082c14040c2c0e40042d006034035420703400038003410341c0f6880c260b01e44808929541c401e92203180545d54026081010300d61003500740004410700c00c00340d0f01c0c5081a446060780c414403408041c2c0f05d07000000110311420302030390441d00c0100c840b8115410034504a641c004181d423110304143d1398620119010040c14590 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 507183138 1250 507181888 507181891
    0x30c1902150402010f0201020d050a09120c03170a06051e09070e0a0306020904090f03081e040807140c0406031b05010504030804091a0409110112022a0a0b130302070608 74
    0x19440c1081c0655954004566000c4060400019075500b0010881c10410760f01400e4840c0407800d001084190007442d00b081000803508058041203560b00740000000d60001407009031840225080403162900d20900340107028a903c40342d4800006a8045041a80000001c50403d01150809180e68800000381d4900201d00cd01e41d41c402c0307100300305200041690f1301074885080c01810014400b412590303545111400204240d000c0364011041100281c025108a418212560031410709410f040c0e039481102d001c0c0290040882c0c103078107805000700c50208a4002140c070001d00600c05e80b540c900f01109c010814000d8000900c07001c038000b04e0154004d0003103808690b489000140f5042c54500104000c1680c403004282c0707034200c004100107964481c007400045034080c03014800d84010038000504030043d01c0794500c402c1c0d80184100340c0c1c2d0701c814100c8602680c1060300c03189140c501e504603440c20110b505e00d006114415202c203200c9402403204504910f03d100e81c084030006615850f00f1b59690700c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 507184388 1250 507183138 507183163
    0x51608150103020c0111030408070b09031c0506011814040501120203061605070c0b0c01051303050409181502071b03120f0210111c11040e100b030c1902 67
    0x1080c019040d05520036030060442a03800030000907100345140f06442c5c0355000b40c81c243c0d0168000b064060911a0030f003240790308640303140c008525001c8244d00072000401c000004070311aa40d11000a08264026082d01c6140c030742d1400401c82c880e860720121806500d6403030019004a203444008142821003a4104000c00e8000340203050a56491904212804030303403400c202048024400840051540400f146c05020f01007081074445180708a0142110b100503c4d00056900104401000c240c101c01240e042d00c1e425503000c14a0124121b11448520165100078825101d010802e150303081035070f000e400d040e841415060b000c161502240900740640c2d010240c540ca59000140c6025806660000621051401a15100c481103c100412150070071580302190000140302e8070301c400840549082074a600c04100407079507142c6c1811141e402039010b10b41028000130041039a10060303c4004004055203801d039a600e1400800301c9801da00400b00203040745d5228840002a035002064447c270142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 507185638 1250 507184388 507184411
    0x60e010201140c130308070c05040c0c3203070c0306050606030c0405061602060a030e0c0307030309050915120d080c0f120604020c0f1f0203060102030415020c13051608 74
    0xc85143d94071020b5442881d510071003000c951400000a82000d0207022018020351407124078074540b000b80020380d180e140e0120b003004813402403200010f458440801d208882030440e5504010044045000044250f61040e094400865250200210b0f0410b0400780c0f07100e100140306548803001032000500040d6030440b0074031070a000511003418110f029001c2c0c0991070044804d92a460b4011859551140c0c0700074000984a03c4c1c9800203200812203d41115010303001084613500e0761718000c0c0100241c1c0602c5d0302c1101c584c004035000301e40080601501100040a680452074100031a550300d1014140300000705407040c1c000f501c101d00440c00d44240311130360008545804155004025175510081041d54003650034040402e5118081040c3d01003c01904024042c0c0d14a4500032901c414250040702c59036401001041860f0342d0200c207175004c417203000951242e0320440404c16400c1802c40c110711030700444501c4c6109034220310f582055008404104162038240403032803046070701d44011188441000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 507186888 1250 507185638 507185641
    0x10b060408150603031c0f0b011b060b030a06060608012102010c08030a1d01020d140601020a172118070501050f0c150a090c0806090705091816060e01020114 69
    0xe1000c0040f50b01000040035a032a00c2080f0a519140ca103451840310141a40c0f83c00d1404150f04d14807451440e100309003425140c2d00c0080c1c1751540403403203180006041c030303403030701c0041c425510300b0820010407561000060007070503294040181006400d00c50381c549401e15442d070b40380010224000e070325101e406a40302035011415844c1c80b02c4a42c80a0500400190b4a0845134007641c0c95403041041203689000269888150032101d02c140c482c00c01140c0f15003140441400100e0f80c000880c2410158090103144000300d96018020941c00354201d5a40083c030700400f44401000c0c00c2d0001407007450881101440d0403400c072003c80d03980d0042d02a450214004020132418040720102400e11401540103c0d03185001d86016054020015540101d010f03032a500c6500c20020b5141d0301c40094800180180680c0c54101c02444c1e441079507210f214018110a404110403a2030151340c01c00c104060001c80c0d0640c00c1c0c5603220708072140103200d03c000084185200704559031041c01810039040c010a4164801d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 507188138 1250 507186888 507186913
    0x40f0c0f0b0322051e010c031a0906031c030c111c11070b040f03020f060a0206010306090816030806120c0f190f0612051303080a2417010b060408 64
    0x544158251114421003c00001c10015000708022070414005014890220249481d2142901c5a10726040b043c1814403030285500c0314611906040c20004680d00ca140c0d031038503400b0074144940030f000c0c132840401c13034441102c869826070842c100307035090381c1e40d2250600700b5402103030f46942e41e1300b4054001203070140c100083d9500c101451880c0501240545001d00c1d42c2e5000020a98066031028001b82e041420803c15031800d203680742601c03107050317920300d1500320300341c0000392201c00c140001030200359070300e032420309101c030302ca0076070f80c0040c08018800000f14803130602030031421045031018072580ca440e200b102c00e580007040b100c2c0ca004000e40201d0341d00b000302d01004204c607000300c440c400001c65003100140c41d407003021449005183c141c50f5101002c0c0d18250003025110010446d514500b0340041c45800a0303800382406da440311072a0300004034030a00c80740ca100701c85014180d0800c05444140082444003107280060100302154000308491072281c2d082c8621405103200d21a090b81241102e40003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 507189388 1250 507188138 507188161
    0x9030215060f06040f05030c030708030409180b01080a0b0907140d08130b040312020604030c02011b1202030d24120302010b100e03062406090a0905040f0c0f0b03 71
    0x10000070060200d1201c2d411040410f0071604070344d01140f059108440200300034102400401030080b41a8042c2446900f014081c07a0707203210f580700b075220880d5151400007817404200c0c00e5051385a44001c980c00035503910191710360790710f110310020394864517843c010592142000074000108c603180c40c42030400060800410201c5100404141c6056604005041c041c07403c40d100107014105450101d81c9890960400400e8042e4030b519071004e640c0074205010100b5040009402101e80c2440e140b9101e10182c2110740c585c82a15070020020301203980c0d1036489a8008c40a0104107110302c4003084910b600c11005c505100710303080829062345050605000b0010628103401405001c0d0001290a00d018004200bc42c00c0020f901d00005156281e95061850244509900300030511001583c1c1c040c00403450958255082102c0e1043e140010040e800fa00d07050802d90090001c044108a6441d00c3e04102e00c2e00745048000320351070b001052000c1031040c0c18048200607210504052030440d070300d00241c1d24 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 507190638 1250 507189388 507189391
    0xc010908070624140612091c2a0f0b09010f1802060306010323010f151e050d06120609020a051806100e130e071a0f0901091a090a050409030215 63
    0x1c0c1c00803401c105882c01c80060314581805107003200020891500b42c0c41000040071230002c002c81c10085c40d410b540d10107207141c0003042c3e80c8809424508032100900c2c90891007450a60b4001400b0385481d4080154200d819070100c00c1800800c0014002d8592849464000215400009501420900108000354482c0e403045400e2000a0f400e1070703010001207400041c009090703100f080c109100100503c41d881c00300801804c03031812410304e09100d420f2034002c0400e481000d00d07031004110f4081252414043d1a41010000702140ba402d000c020485041000c00b0381504a002e03400381103070801c005118100360b140b6a0507198407411105554031160104105283c6050f84e4104002070302103035140558404140c901c40403424440040d85040c1d40640034100225540701182d0120a0382c0218000d03469a02220032106004e09059901e508040044e01d910103980c200d001c0746100b41c42c41e05054a4560001e0802c0c4008840c0094426543d10400050303400c201d90040c01600040311071603143c001a105035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 507191888 1250 507190638 507190679
    0x2011509020714030403060c020c060c0a0f05030f0406020f010b060a120f381c0b0c0c0a03090303021506011403071103030a060918260c010908070624 66
    0x240711043d20300c050540b440c0c1080d001919003a640c0e6030815009a01000350b138031848000e0f80e0440c200083c544a040c1c54031095240a0041c04906011100f0041c0034401c0b0340d034018184106a03121500c840000b540c400c43c800144015600e040c031b030405903141207400d94064010594800c00e4040c16400494043d00c0c000c000142456100c010110151158605110740c1c0c000a204140c2d00c2e0018202d0380300d52821a0b45414054510350403440c02d100c0c07003074a00c000010f8100107507a102d612480b0600e0320f18815042e81034007a0040c84150801c15130b005103c80708490081d800c8600d942030381c94022aa10505842850110321140c0050040d0800705000d5540a503982c1000800341017a241c00d41d05551045601c080784a80c3c410f000e100800440c8907100448141e0928051000880e9070f914001c0c6c54000c9410030052403484015840100071003c60b00c00c0c3c01800d00a02054140d0300c0c2c15000c0e6003240c5011142c1c9400c140e1390400d850090480c0b409504402c0c051040b10501d84440401d0303081c50b96100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 507193138 1250 507191888 507191903
    0x602010b0306090615012a0f110f091b0c0118140f1906090b070504090c0809300706060e06091005040b031e061b0c070911040504090b09010606020115090207 69
    0x141043e440700d400e40c0d018091f020329500461000a40391613090042041d09d0b081c030a11011500c00829140c041c415a4040d40c410108003a406081c14407190314081c001002c401c540c20074010380101084100601c13481da10801e00310014040801d802601c5015400d10001030380e12a0032049038480c000c0e081c54104c6401800300003251009502d90304514003044407108045500041c082160544e64400c00e00d142c0e500b132500c64260308105440c1611131621b5103880c0040c0c042c07035036428401e943c80d81030b101c5a10701c031824041e9505100c0c42c049007d84241d01c124101c05070039400003440c034200f00340d51520070740b412049544e509040100700001040b441d01d641b50148104840100034259500d0142d1302c4c40c0c103102c024203c9103801000041c0303107080c0c6a00c81a080c038061000b12110b810019215083d25541e11012501100030800d460440c0142e5002c0d0b60b10604101094040c400b42141647c000c3c4100c900a0090a03201c0e0000d1303080e1210030b44280d0030b283c80740c8400c00c15036089501600c4200e11a401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 507194244 1106 507193138 507193187
    0x20316020d1a090c04050a230a0615051c0605090a0c0c080a270612020f07081b070f0f0611010f02040602010b030609061501 55
    0x2000740114140356601081100e00388154403403840300003001886140140740e507950b80c5207030302da0a4001e0745000041498010b8034060108082c1c440c0402c80600501c2604602007a40002d01601c1c0e1183d50304404644001a0440c8041540d401d5075003944444884410b1800f0741101d0780750f89030040ca092401c1215403903404440341d01c80d00302e800000d800c0b41504010f868510710400001d020140021b040703010150010402140354205244090a40801001010064100340280c0380400c941d8505454280e0345a0000d01d41800000ea0241c24400140d032910f001da0440310340302080f03ca1511544405a800f040f1040042c40b640b8540180c6038a0101c040c20107201d903002d8002000b003c810418411402500110303c0b2074580d5074110354503962403200900804421040724402c0c06240e01049034444000340541c010001401d09100d8040f8000c0150f605240211204922140c44d01 = true := by decide +kernel

theorem cover : BRFrame.Cov 507014388 507194244 := by
  have h0 := BRFrame.cov_init 507014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 507014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 507014388 ≤ n) (h2 : n < 507194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
