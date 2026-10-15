-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4394
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:28:45.780774+00:00
-- url     : https://prove2.me/submissions/ca760041-cb83-4d3b-9a35-eed99222c5f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 790107913 ≤ n < 790287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 790109163 1250 790107913 790107917
    0x406120227040608120d0e010e0a0501060f050f180c040f0605030906010b07121110061502100516050d0f020408061f06090302100306090527030f1e1306110606010f080601 75
    0x981d00202c0c1c0c08d014106031414039400b8030900c160f8401f4880c06601c050200c4034040c3c0e41a86c610f41d035005211400400d0340c0c1c515405600a40e0402c19014020030859114049088092910780c541e09169810040c0340c01810000300702108102460301c007000317910301605404e0842c50404655036140d1459000c8091014100b0901410200f001d5004012000070b13441007020501031a51119540510303031000d901c07080f00520802d5001c9034140610720490307004102c08190b45100840d00c00c000d0383d8940c0500100030701c0e0342d1340700100041e90420b40b014102810058024203128148410911300c80440c0e0f149040741581030320720070884c69400801d020103c0740d043d034400d03160601f84d000c140c004102540c41040994200400c008904410045003c039075002d0f0008000c03640001a112075580c0220b0300420301000080000c03148208203880304600300000300703610614000701e00e00000080ca50541c01500410044049103150300740602516510900a10300080c06290407080100a50300290900741 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 790110413 1250 790109163 790109171
    0x201141b090d05120d050a0507030c0221040e0a0c0207080f06161704050147061c0b011710050f0d0c0e0603160305030406120227040608120d 62
    0x204102050209414040e034100f640c5868105e81e80408003d0315048600040c0c143c6410b0014148502a106140948da02e942c020041038960030580d82e5501080c414000c0c0200c1c060000003090021944c0c480d00c102010040030462949441d0003a14204094105503400d07080a058080030100000d41c85912100c844000000da00b07014400717942d01501c42d000d00c0c0c5952264020401441015001807503a041050003d02118000a210180410400c508020800410f5000d00250008134a54040c0a43c0041c44185000182040345602440752a8032040072515060100c0443d038106001803000c5143c07a00c2c0c40e0081c07a180c1c05450341c1440c1750080707520482c210390358400c580d103e800401000c5a44160340864094541c0d0b940b045054088401074401d01c00c5c0500c0d00c04000d40c0c24108800c40340d00c20300a50401d414082c041d10241c80d50901d658400c2e5083c00a042800c00400c00b402500f60305c00e0511a902e000d030070911047e10604d400c20051548114007070002c0d141030030104d03500c20004000c00a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 790111663 1250 790110413 790110439
    0x3080d0c09050d03020f12090d020f0f03151f0b0d1d150f10050105040e0903070614100605160204150b07080d050106020d0c0615150201141b09 63
    0x1890080c420741202d0b4010b01101980000c140d0002803404109014108136000d100d540302483d000b03842481081500310480c50300100050500c4002043e10010082c6032140301008640400d15004001450401500c1c03a80184018800c0303c4809a40ca948003059554034903041a0005200e841506201c0505030f41d243d07100d581d950610804038000c40000740c00c1d150f003250b040504800e0140e0907208284142c070480007049440f086c1240d8881101c0341078650702d06192826800204402c03000b401d0880501041060744006032561084010750302c4030390000442401c00c041c02d05103040d15a0414020300104010400c280304038111000640e950403100031485684082103030102c0e10140c0e0001c048031801150030420814520040d10103003031200c00802c500da0b038800007280d0302d150801c040004948521030910201d0042d4111a44a01541c060420200e40d1500e05103d070290000345140184d5443d103031810494030702d010258100d1501e404541d44680f42c040726901c94441e0f1005503204100c600514 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 790112913 1250 790111663 790111667
    0x1503072a0209150907021e070e010e1f0e1906061b060615091503020a17060d02030a05100c080c090120060a090b0901020313020910030501090807110a03080d0c 70
    0x2400110252950006090008020b581d50002c4500c0078a25030507c600c154151038005038410403101070103056051039180520000044402400407818040c4109614080800845d0240020642112041d00e203240414080540c0001c41d4006191607045c07003410411b80e40d028442010118008000c18804002131a00354002c4c82c01e90b001481d60110307680507006842d0000d100c0801c6865103024003000c450201811403c82c410707070511401107801942d03506001284075074413581c4000d014003c184c0d04403076500040d142501144c002c88031a8011070a811202000740640e52001c00c05003806861814407074218252307406441c600d0b034108401c904045d2010f0031010fa04800140e0400c1c10b66803030b030138260f01c0300c8003a050303e0307005030f0301456400301154882405100301c030322032100e00000c40b01801d101e0342041000c42c4045c000110991a508011020540a01c100c06100d485212050341e1414940740c080c000844203000c1e54450180c00c4001c00115030b41c442140c5a201100b1b00000300f80c1080101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 790114163 1250 790112913 790112941
    0x6030b04150e04211e1b0b100b0c25150c051b010c03030f2003220210030504020415030807030e040510060c0206091503072a0209 57
    0x34002a4614030703400064081003521214019401841861800e0220000c1c41c1d0035041e00285910002c1c05409680320110360000e401c2400300340d40c2c64501e2610800c8800705181d11000001601c031a90b034101802040a00c0e40540c500034051003a44c51b040c014aa5141d0752200f01c010224811050300e084a003d4413548030002c2c0c80074250055400c0c400901e400b070000e200a103c81000c80311441141148242c503800c10400100d44c0070305a4a8004a036019035040300548200c102c040908e5486122500480c0d804d061070b170811904409015480b8a02500804003480c4000111b000002c200d88142000d0784a500160728840c01d0741c240410246c50ba0300c08180244050b9039034142041c00300402008104074040249665402940c0f002c0e03c154544d010041240d405946c025000040220200101030144814038400e500042403e401d104418010409000e800d8000745401600041088401d580002c11307441c410122004000750221a100b24540450614030040d1103002200001001481c2c0201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 790115413 1250 790114163 790114181
    0x1902130e030f0d0b010914017a030927070305070206011e0f0f06110601030213051305010c0e240301090e0f160f0905060a06030b04 58
    0x2048039035030140d540d603076026900420032640030a030070801c000600d0340c420101401940e105040402c0d45007051801543c542c2c2c1c00800d5000c10718a13050720002c00b5051039110f803881e2780508043c180310220701c107005a01d80c1d000015202441d4100d0101703555800000b21b889070100d03400c0002d80a41c0c244134564a146016203000b00341d0000c0c208a441042c00c00c1c080d140c0c91860130f6035540300341030f80f240c14082d010340c0e50031200e00b00141d0100004001203649071006600c201701c41a004004140c884101207581c18003130700210500c0d10441302c1045029800302d9a0004844208060026941141d000038031848540b185049115201c4004c9205003041f5a802d4019542c0b0400801c109404c40f040a00803004a8070040c3c8a10b440652000765008194000d880c020385010740185140e0a089070240107102c02c01c4404014402c10801c0d1004401c1001807402010b0000e00000340c1c01d01e080d808002041607504014020b40c140340902c029929400c5028050f603559080106090b0300c040049002440950 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 790116663 1250 790115413 790115441
    0x50d080702030c0607210b01080a0f140c040620120f0c030d05060f100c020603070c0c0f03120327020303090604090608010e0d0906080402030c0604081e190213 70
    0x220501041d907401541c054440346c1c109601020001c000700c41030b012101e03034584480c00714a960000800074521a03001580c5a41c2100d070000d1100c1c4812820000c0d034804650803c136502c00040c040c8403541d0030201012034401d00800e6110021980c00385282c4420a0121000b1841408103440200035031100c01d50304488204000c0365241c0f04081040c038040d1106850b41c43c050003042d042d84034103041402c404001c03070302c00d134841070445110390b400d00100350700040018007000096001c600c0003c08800d1000300401002f021205280e04508010142e1900d171000a800e03d49031121100322100c0140c11b80358088a0710b003100215010f50b0000c41d08600c41e002860740e00c6140058041503600c0d40340d0010058444501c001c01107040307407614072030b81c64075040c00764008600710341e004001c0c0760322070003000b40e000344003500703070b80703a80c40e180000c90419003150700084215080320248130400c01c900081d1420000c0e007036000300090034000c91006210301e80704401a00500c0b00451491690010b60000f5031404519 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 790117913 1250 790116663 790116673
    0x302040e0903070201090b0a022112010e0a05091605010f090902031812030106091701060902130e13030819110a0f0909061d13050f0d020f010603050d080702030c 71
    0x103100000d071603a0003480101e01040c50706c0c82c04620300c18020180da00c603091940085c120a1040103080e00c40040300500a1541d80c41001440126210389a045000b0710250000034120705003981040c050780c8000300402101d0f8001d06000d00400a107080c80f0f0120740007030030300d102031a00444044803491102e801c85804a40008140141940c0c894102e400c1d0740c8001064603100034008030700750301611081c0710303000001c0e010000a000d002035188081c0403039618640000b40041d81c035003062099030040000c80308402903142080046008412241e5804003640007042d1413a8000e42d07014041c68800b801080c101140d5050440d00c0411765413101020003604001940c6680400340014a023180302580140000c5c40e6540004000c40c550003400d0648907000101c41c110344000514901c02c603402070007408849035010001c2e0210b5000d004032060000c03080050700c50444021000f901e04500085184080c0e80341040070004a0400300d00b4100861083c500900c080c2c4504d40100d00d0341c042c1030105802c501071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 790119163 1250 790117913 790117921
    0x305041815080f010c030218060a0c05010c050d0c0e10050307030603050313030c060c1e0201050706020c0a0c05060903060402040b0619020708011d03090f0a120b01050316080a0308070302040e 84
    0x82c105000c1c3d140600920441c440840308809034010003111086e2031000c288000c0440c0340100182100f850140780c40c4241a140c0c2c0c49031030948000c617542a0124100141d801307504a200d0003258240c080b5420040c80c040c1000c00403a1155480c0360760b80c001c000000c00407400c00c5219411660007103401c0002c032a103032844c1d55200d0080345200e1001321402d42e41540c000a14074007850300c0f0702c10290411140c048800a007106081481e0002c01d04038100a800c02c00301c000242e492000d4a0708948000082c450740d10f0034076040c8842400c9030481482a82c1c144240c0c1c1c02903500081c00384d0f1059065a012429203070707040c0415003902590009480e410700d00d080c80a40c25500041442c01c59109030300900c0544030301c046c084007007491804841016041041011014184240c0c41a1070190240920340c1182d55415060b8041c07540312821104401c0c078200400c20742c035080020315007941c01000703640107251030051015030b5803405013801000e2201a10001d8072580c025030564000b041d21090303c01b0302d850 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 790120413 1250 790119163 790119179
    0x906092e0305160504052505040f0303031e1e020f040b07260403080703030b030a060204090212150904142d150910020903100903081b03040305041815 66
    0x60f041541c1070721110ba41000180038030345401820701800110601d00c01140d0011a0303600d405005e8100041406000c12000650320409446d040045001c1c0d0b8000540400c0200c000d00103890081021480609005200c102030007200150104d5190410300143c0c1ca10284c042c5614602490b406400d0300c1001084d40014040c00284d84281d440d014000a92003c100c4489c1c48168000d038000909001d00c01e00405000034040d60103c504100018120b030f007204003030b0369140180da000740c11448038240c000c00c0c02010019080601a0004038900c18041404521000b158031140010005861902141107004400000780004000e601080c007607040d8400000740111030601071008105418880c130410644004800c881c62805100c40101500481c1c070b100405034041e42000340c80c40d40c1405120509044070103170b4401c2d07140003440307a207c00a00d03191002110301038165440007581c0042d030800801c000698401c048409550080112141004032061303140c00800f02e0900d403403034803a000400800c880d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 790121663 1250 790120413 790120423
    0x9240b090108120d020903012a12060503031806250b09010b0915030f0303010f050907480303050405010b030703020d12050c0712020f0906092e0305 65
    0x8001500d114040340d90b601d14540d03a91035100c1c20030102d90300900408146801d1500100203118008001003030701a00c2c004c408400c592003c0100c00446100c0e6001c1070000d070480212065062561804c1118529140200303899100b02d208182103c440e0b050119103c0c2d942d40241e071f00c603403410880e540858642030f40c2041c0c4000c00d0101519011080e070000b9445043c14010031521a802504402440d01c9207002066540b542408540d41406084548802c101c1c003000514024107080c852100e4003443c090038060442c101500700b00801c0400e0412074040204d100c824a25203507800070340500d40501c6021410160015062903078000c0c280c00b10001810b5141d00418000d81c0110000c119000c004020995102914400250001c6c8040f00003c0851905451030420701502d0400320710f030a1520200905201098102d01c0b10400034180b00002d5080c00d80801c83c200c0002c0d45c540247d8180b00c000900c040c880104006601109202c401d50309815000300b803034048690038003100034607880349041030b211 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 790122913 1250 790121663 790121681
    0xa06020904111812010e030a0320070c03120e040204030305071520180301020a090806010806040b06090622090605090303100501050706242301090501030924 69
    0x950308003000c4681062201007100c51180c03d110180741d40700b501109002d001d075a03108500d1419541c0700c100e0b081814051005000308030303060343c2c00624a5150303a450131055000c0061aa64082c2c1480308600142c0300c189004181e90b04050601a100604403048030801d1440008603005400414008201a000400380c10210b114a00301401004509840e100300c585020300480c1d881c45607105010755a9084001780200c2900e2840441c0115500000c00d007640c0c04a0240700001e803903904200003421040c0704c06800340c09038001400700380c03c064458070704108020708010b11903a5520701080003540c03240100b42000301e10700d841280c00604101114000e011070030054510320b04110000f1074401003c42140e1048111a495142031420440119401d030400350301190001e659003210310a14585500d4800550212490104082d0914002130403260340d240c006604122480450364082c0e0704603114900b0384070207203000100c681d85400e182140300700315220a00005a407024002e4410203a4000c2102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 790124163 1250 790122913 790122919
    0x60504080f060601050a0f26010315050403020703060b0351040b1b0c0705010e030f070b0307120f0e0d0804030516020a0e09060f01061d150c0a060209 66
    0x5560580c03040715071158011243c6500040303007081000b10450040c80a21003400b42450035000c0712100240b0940810405a440b414a0880200400401c8000340303110008082d413140a0205013030940d0040e40d00c00250000910303403511011100303c3c544042054482890607601041d075103442d9000c2030480c0802d038118194194000d8856051400525011340031803603011030039101c241d0b4441d15244210f030405403071544444030402e0440754401060000d04900000d401c0604400c1d0b2904001400d0851400001802a0031103000404600700203d814011550040d001565960300c8500c225801d44a0200842c641881c02a840c10ba00e0041d62014428041042c210781a8219030407080c0c3d00c4103821500240060340401c0b917002262000c4a40300c546920191100e201603440d0740c02c415141104650780582a801441005020b0511041245c01030400e03003081c4c013602d50240c001c6d02c80792981c140150f01920740da11100080340b4100f01201ca9050700382e81a6580030801d80f800c0c0c80a03510000d95544 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 790125413 1250 790124163 790124173
    0x209062206050708040e0a020405060d1b2d02010f090f11010206010b030703150b070303050402150c07031e060c0504060207150f3e0f0601060c021e0a06050408 70
    0x8141d8050021502c070103401c10b03005810580340010324403c40d0380007000c20b92119028172001030240c4900010741000c00300c01c0000304541d000b19040b40c1645d186c023502034040201001240c903441c10020103000e03214121031000850703001602c2007680035151440b443d07183c0383d140c8002201030002e014210b4450a01c5280124200d00b020801241c0d43c6c0000c4c012000c81001c01c1003c01c40d00c034060303840101a1015030360b000c0840d50381e411031a9142d07040ba51040d00460f481c2c000b003104610f441e844150043e10302238940ca04200703100304078558600c1d1a00001b0840c480c424a4589c80071200142080240c0d4818024080540c06160061803034000f40b06900161198600c0846c00b03000003a20a90000311b10307912204100c81d40c02044446c100340c5030b803200384204141c00850f00404440b00300407a44d110085880090400d1150080c904420300d60022203e0304141d00501045034480400319140b601200e03480c40c01e070030b41c0d14030b0300c0001050b030001680074940030b00008103107820402a05c200c41c0c10000b551 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 790126663 1250 790125413 790125419
    0x5010b03090712051c051c09030509062505010c1e02060402060904020c010507020106080f03031512240709080a0b06091512100c050a09120602090622 66
    0x6018003094800306490b8000902c14050090f907444000781041c055002c89580d480c804010090360591800040000b8000140d1411031800e844c20380e007401c001414041000507441c0d24010a00d00135200382d64032032440050001078084003044020084058141800700300c14161400b0b80c020720012101d000428100d5891841428011605030007020f5150003030005541c03a03908000059000c0400950b001d07a080c000300380080402d00c6030521481644d00001511401d11000764038141c100c1c100307240540d02c1003082010842a0b4804250002c10517954007a44160140405007041d8400300744010302da809620189114141d00300707140c020800707a140c1c0718106464860705034550184140181c4000e5001d00455902d00701030303214552000400c07400300c1e400c2c44400005111a0100300341004a81d0103409100d56031030951181ca0100c0300300781803940c038110300010081c001c034030702c0e01c5a01004408600c0d080180b2030a03030101d50240d00001c20065445055540d089a5081400840a00301150034004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 790127913 1250 790126663 790126679
    0x106090504021c050a0f080c01050915100b18010302090d0309030c05040507051204020f030a03050705240a090204151e170a1520030906070822052e0501 67
    0x140c40c9054015010b820f0a10068651a02008101c1000c82d11f11508015960380c90800f0301c40c007400752182901074040745810045035009108058841c0103451156001000402c1100c1c0072514280b2400042c180302001071401138000b80982c0b22050303081041d5140d00703c20150b00440c1441528844c80185404503121018401220310880700180480c03020480b4a1000f000750406a920510041c0090312009120002c2030401840240440c003180c40811240204a018820010000c9504c800260800740c400030513070080f04090300100009035210045070640d100c0750444c00d01c4007000e521030b070100c0d0750312160003082e40d00049141d800c040041101040804d01c4c82150401c440c4214010102c40e605900d840c903e2401003aa10040b1030b540d0103818000300c0d035411500d1030b000512030a20b9103d151002c400350501800800e08801c02589104002440201442c1c2c2c400a00241c840280d9041d01803805a00d4698410701d004e51480110032100016491014038030b0302024080e40910507640c0e1090a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 790129163 1250 790127913 790127959
    0x1203072007121b0b1303021c061107200102250b030c0304151e020f071e0510060b0a03020a0e190504110310050607020a150c06060b09030a080a02030c010609050402 72
    0x50030117000507408101514001102c0704604000032203130740b403904680d606c80c01141c803424610300400341c0c003280c0b24050003c0c01c8600704412541c51100da844500b0b00000030f4495448111680445141801d882086407106d15804050100411311595a0070207922603e000c2d082120100e501489035410722164088902903c2030350480040888002c01882000f84081d42000745c1c070110180081c0000001b0850403400444145450500141c6203da1800c001d802e08202d40300b100340d094103001003005100741d0134048680106603450b00503100d41540700210741e00340c00d100209e0351000c06404d8400400c020144200211281100c00b008580944102c84c4064002191040e0460406034410030880c10884014082d0702c1c4004c05401d02d42d0740341d80c8a50205004400312100051000c01546c0c05c010591103408081c00d0040c00d41824a848440007030b42d501c01000c001440d810700440c141040d24004c00c07e4070761000461000b8081d00d078541e50fa140060404490682c49104612074160b11500c203162 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 790130413 1250 790129163 790129177
    0x1318050f011d1506040b0103020d0f020405091312050d1d070e1e13050708121917060d061b050309010b091009020a090b0c0a03021203072007121b0b 65
    0x2610f155507490007000000c10a8105650605408000305105840340303110700c00c5280c11030700c80182c955003070505001200f14001c00b154454046220340d94045903541c0729000c6803a07400c0c50850f07561008030601d000909010f40c940340c5080210900d1404944002c141d540c10750341480800100c95581302001c09941d52822520300c84040002c0c0440c00040800c3c1d840341d3790740d005004540301103550f044414504105205080340f0b280c40401e150488800c5510504c074880001e20b010240180080c0c00300500d00e0010744014407500030b500e92030342008a0342c0c1120915001003a0a054001c10002c2c02a10580c82140c404006510344001034101c1d20780005041c2c0540100d0055805084c1800c500d00029400000002c05100c01c40388006084200da50042500744408800762206c10500e00c0e0181c80c1c003491516008804c5414810856075551014040400880c000e84405911060114240c10070a01d9001840700d22640308041090011a511032818030260302c407541c054940d1411250444c1c002c2074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 790131663 1250 790130413 790130443
    0x20d0e0606010f050309120309030414010f120509012702030114010b0a050d0609020a0c210503060d020a090f05013305092806020c0402091318050f011d 67
    0x1198400f248107401071035002d4685401c4919a0b00305103d03400d02c82e0400c03242d00703040746e10004042c018162100130050000c1c0c42800c000010984501d40603000b1502d0f0303821490a941e4074000034000b20b409400c03511071a190340c8240811062240000a2044101c0f00140e000c4d6007880d01c1d1001c04115810305074100c56080807020b050007000e50342102c071360307000d01c4402c0452500c5080c04036002100384024069850340351035680c40348180f40303000a54600481429180c44c107039113440310b481c01d407c030b003c4030350181d41150381c1030a22406100003420007040e0380148080610f01599a038a610090b0301880c1610380d0805d0303200304211001c10301c400c41607100406507400002c00100e0751105020300e026003100ea10003800d81c14040759400c1681500443c00b40c2050381410094030400800b901440034840c2e0190070788055140c50032950110300e01c0070390703160b0000c2c03110754911103007940305016440540c0b20f903880816501d060203c121b1039070113008001e1010001c02412440301c2c01e528030000f02d07041d002d1812 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 790132913 1250 790131663 790131677
    0x10030b0d2307180c1701080d030f0b030705061303080f04031a0112020906180a0507080105011103160c030f0c03050d050a020a12140706050f0702030f0f0a0c0213020d0e060601 77
    0xc00d00e80c2c006440d07030880f000140900d02d0f00c050998400001c007a40680400c40090140f2423200500400341d031700b00c590001e0600e28003003200140340c4010a81d407043d1101a58043d40e1134030944181c84800c00f03644d1020382403800c041035292811607808000c200701d81c0280c01140703e00d20414400c40c548202817040c89604200028418018101130503220f602250041540b4109100e020f60700040d481c1c00c40d84488074942e11030421400300d0700701007610b0160000f0301e0300c030584411500e1203569074400c800481d41200c02d00500c6d0f408000c00c284e0200d001d96400503518040b10701915014184e000b00f404100c030b590041e032544100d02d5106006403003554000754001e00b82000e06440d401075402da00f2011004000306c280c2c449a81000580061401030720428001495103001e140ba09043d04d400f41c0f11008642041000302d8124000d102a2072240701400e101c04d83d2001c490308161441880820000d400c03a100f0640400e0f0103d00e40d000c1d100202480c0070500c24442c20149690312a08203c40383c0e404203240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 790134163 1250 790132913 790132949
    0x9030703030e0a0b03010902070308101d0c0903010e070306050105040c0e060a021c052106090403080a1b05070203060f0c04120809130e0f0109030e10030b0d2307 71
    0x104200090710303403401600702510f060b00c945251400768030981041c4040c81d00055410308065106580a41c4842408000d00910b41040401c1015011700b0003c81003801121000c118112060340495260900041c001c101d008858590f05840d00b006d44003e4690f5480d09000081905090084008803040340e03540d04490040c841c1080320319000300c00348208602c140c82000817085403024440060400da6100e2580720f0711075150f024801094201e000303144075600d0092044544880f80000c0d009a418145126a0b40c0c0300e907405001050407540c01c003c1c40490040d2240880e42040c020000180280c05441d81130380c4468481010b004140d80d60010110300f0882000400b411941e8042014400c1c942140741103540c0c1c00080b40d40c200e01c916045c034540c0d65003410921500c00c000c41e81c0341030700c070a00071301c02c1000301d840207170207140e14100e00c5007c0c5400c48800300a0a03c0382c2d0208141c210010110b83c110011400c00c284a4500403401036907014800c0d600713010a100008451045407141d5100514401d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 790135413 1250 790134163 790134167
    0x7061e051b190309140d080a0507210504061b20060d0906050702061617070504090903090501030501050301090b0115090e010617061815190b0d110903070303 69
    0x20141c0201c801d501964152010400b00d20b0b020114443c003c0c0d0f0360150150601c4042c0d482e04034003144092050244000c810300265010041d281e510003642032140d201c00c1141004d085000010251002e043d0146000d000c0650b001805842942e0013a41c034510444034058104803004240d40000e410300100211a10708034070401c90a0030603d102500403800e00544404070000e50b00050011107090342c4400030090103a50400c01c65510107202041041400905540a40120050251882034117080b100042c00710380114200d800a00485108203c42d040d1820000c21008079401070a00081c2000700002d503d260500230803840c2034009207016240d901e041103e22100c03c401360200c0c10f01c6003034240014081020260b0b40c0c02452980c40f0880010303014072904030840c00007001d0b2442a8552520480302d000e21072142c5034002141d80c25a41101e40c0c03c40051600c213052110021540b01d07512002c41c01c480b0820117007890361541c4106228104050001c03050314084c80704060340682c03241c1d0003000803c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 790136663 1250 790135413 790135447
    0x606040f020c011d06060109030206070f060605150702012d1b08040602030d11040b0415020f01021308060a0905060c03040c35070609180b030a0507061e05 68
    0x14003200d10040c5411025a50039094840c90b00e40d8086400030040d4500619806000242d44280246400c41c00325082d980042c00c2402600f8000e400d151101c07022004000056000c50040d180051400d000c1c41a0072a41c20603a9204c00d404900181c1c054a20380100c0052880e2415900310003203170000750840c8500304860310301c40807480e5103110101000d81e40203c0e182400034000340c9525800355555201440110090312481c3d01508240c4000300000c01c004062402624240c0d042a040100c500c500040b0032864501941602640c075440000d154041c43c40b000b0802003100c181c030301940c0d0156203001c10503040311a03c60025085400c0400000c208800f00f130000c0d68058451610505400c1c0c40300343c01000c07000f8008540c40341506400003507a0110503000c0e4116032201200041c0861403d000300205044810701c148111040c0522402c5181071240c0c12011526902034129408404281483c60f91148584151004504104120f2208000175800503524100d2611000e24140211400c4c16500c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 790137913 1250 790136663 790136681
    0x100c030e1c0b040b0f090708030d051e0903180f0609040e12041e090209010c03030203063d0503040507150c0b0a0f11070f0f060b06031f06030509060604 67
    0x20751808040000b070200482180658003940e120b41091501d52111800360030040d02c60142640425030412808000104035841c0c80ca01c10300100312610b91845004d07a442801d0024501d5640550420070042000006080d440d11280203888184002c882846000c8104014058011400300721036061810072350011484071060f1030803074503c0064000003000310b0700701d9001440d0515220600c00520f1000400c41030107414980011031519a0042c0081d0260395110350050a158007c030003e000c03503581c8000c03100c40f4101540f000c20091080441c2485500b11008441c10440246180c02c180d07900c981c00341c03403055134404001d250380c0f41001c00c50801b007100d070181c080400c07104000ba030000800c092010340c012903106e08045440c00c490880481500d4000c0c08105500c0750610007980031942c131a100021703043d080030204003003010074100500030304000c003405608041c00106000e081000c070b400090345441482c441d800c141e034070b401c4102d05450040c1c41802c1190310000115030585040e510038180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 790139163 1250 790137913 790137949
    0x50d0905070e070c020a32130204030b090105070302071502070203160303261b0c1e0607030e03070809060d06051512090d0507030f2a02100c030e 64
    0x20750341d0300d0318101c0880b0021a555000500d100c101c80c011410402c0b049005808000144116131403501c0b20101360046050341b415102e10700d142c00345010f4070740003d00c040812044000b50365070740c2c503401c00c1e128a03c0180c804100c55841c0c4400150300c54420301c2550b56150b4032546031030741d4469141c1400041d401c078140070703641801201940040641042c103001c00a600c03076100e10100d000000c40c1d80c100189249071007403426a50b6002c00c498116040c010700c40d52130003c0700741c584440541100500d080a210060400149601604040f201c2c0004000d480388039165428403c807050b12800540f28043c01038014101c0c401404189840d141510250810060f01203001901603595400108098480ca120109460740025809001510f81b10b1150388122520014500c0c1c1156000040030361007007036400780820040964800c0e2052050003a207960801c040400c88894a61a100d0340014244841c101e11542c41c42c0c42a04005025401c00c100e426015114100b003401c0d4402406015504803d440075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 790140413 1250 790139163 790139173
    0x303031618050114070c090501090905100e1c09050306040804080f0a050c0402031e042901050901060c030207270b030d020a020108150d140c0a080304120c08030c010e060c0a050d0905 80
    0xc3c1d081f05501c92607000344840c1c2d002044040143c10440e091a07104904040c805081503140d4004a800082c1c0498100010080030031400310088202d4030740d1030340e42080ba41170103494107000078098000050016107403058144c658a071082e85419513200c0321914000c000d50000b00c80c40354180b609501450380040d00c040c00d5030b0f0400c0c070805030b141254030807201102d00340b0021098038036100400c0c59091f00442901e01041140d410040020b111840501c00c907410850300c0103004007014400e008103402460122006080c10180320300d000c002541e0b104030110b40030300d0580700207181e1034001004240c884840e0003905007802c194004480c1d00e0b0000b03044403420800c00d21180841d48865107030310a800d018011800c409100e10641034104540c4840a61003060144814440c602021040342c003100c4d00e51700e0400d01a8014a4170411140c3c280c0d001c243c50303010200d60591129012f401183d0700c400410b040e038601d541d592555011034000ca40d188400a2404c1c49500300c0a11194031520015000d1030840d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 790141663 1250 790140413 790140419
    0x21b0607030b180a05060604120311060a020f070807060b0a06080402010f091503110c24010905012616291303030309080c1f0c0201090206160f020303031618050114070c 74
    0x740d07404482481c21000140c4bd0368070226503c0c001c4c8400c5410001c9000c3c19440d0404680414800c0c0c0506a006018900c0001d0010f04120544d44254921200a01441c031107640d503600182030000c00700c5050b40851240d551204c0070b10311134181c501c03d170740400058203060b81a04000701c000349040c2d030f03120200751070400ca00600044204181c052000d01c44640c0410358074203224003000b000040c2d2105056600300130041c01410032070308042d48200c0250307400d6502440304010503403401000b0a0102d01629005e4401704003d0b898100304808204121b00e049185031542e10f4050452140c9400350754042001e2005000103407203070304400450790007001c1090600052210107030618003d80010f082d000c0c2d000b141014882e9030b82c082d808221074580000c2042c09402d40100b003052140042d1100d121103071036600700410561440c003c00c07060b0040d04480d16490800075a901d20203e401501000c2921000d0341c2c445004601009400d4800694401c000040c40021910b113a42220008031888905885c000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 790142913 1250 790141663 790141679
    0x90509120f04062616050f03070f08070f1407030921020a0801050105030d2a0b07020f160b1c0e0d1b0215090301021b0607030b180a05060604 62
    0xd01040341d4189000760ba00c525022001e06034108480d01881040000c0d11a0b25140c8021200300d98000d441030744a03214503184000803607092117141c401d030f50503440c0802400070407540002103002519868960140a440b5018141c1d08043d0a1f4588000070f5281049810203c4d031010180c2006d41c030901301a042280c69103524004c504401000c2c94102444500716800d520701000d66900030407603100208840d50400c0003081e2030365034180724a000c1c0410f0041c0c0003840c400342c21000740d24603000014022010118540100d0941056540301c00510900d81c0c448042c1002144100340d10300300441d04001e05107402c00102c06908031031400c081c0d2010441310007510300404d00030076440180c00000343c403039504400f5001e0110104180401e840c02c44100203000161a04007207201c01e0700c05150800d03103074a00540080e0291191010300540b82041091440040d800003c580d0701907041c0b51004c2c400751000b503052103d271128007440c0b0900d401e074503004112007600b60f0b030010b038000c04c000e016249031544031004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 790144163 1250 790142913 790142917
    0x1106090604020f0a0b0d0b06070246050405041b0e010602240403030e0304052e0203090603150a0b0f121f060305060a121b0801050c030109050912 64
    0x10454254010350204000c52034421120048a070007241d940051a0504a8000d61800381c0840664044e07595000f420b51036660f00184d41501e540104880310034031110110249000b5010000400740e00c682a4400000e045c1d0140054031501e510542c1e92043d141200304406444064000d640481152100050000f410b44821001c1d143c5d0300300b00301d11545041002464944925403100b11039000e425103048013450f482003550400d4062402294070303918490307101c2c210302c669480140d0100b40c8101510f00c1044100c10f4441c081200030342048200c01c9600280d88911600c00c1c0240e011500700001900c80b1404034401011003009042d921805032660800e84141c0d01100c80c003080300c0f901062841402c0688510315034007418070442d99132065450485000010603d008210038507480307800168854458805400040c2401c1072601030a102a080c12107004030410710110a08100b6100403c2c16081409001d014840c0c90880618580ca0300042800070500501000c0c0280181c4410b801d2646100700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 790145413 1250 790144163 790144171
    0x504021306151214060d02031c020d1814011110110d0b0d050d0f050c0604060c080a05060603060f0301090b15030c010905090a05072c090c030420011106 67
    0x41c1c098042081c04005007601c1c10714620a2a102d0070700d605944ca1640c80401c554019009451142070015607100090400352246512203070700d118a5008159158002a043c410340303c652928a03c41020820b80c000d06041c80c0142044c07207410711016031140d40b1400100d0303030b003000c9903040e100d407450700381022401e0714140030700764005010105208070f08440d079125550303c074041159080300e003041c00da5403a600c40c100d0010540901800c0344800644070300400c211202c0c0006202514844c0c0f13003030300e40800240348002c00000051081400219a000e0fa40718807405050004d0400703085950b00381c10408036004075100142c02d0754807080c007080050145561a40103151a41a081c40c0d0900d010030305240518005806040002a000c10041a00c562944507000030306c242c400b08141d624418281d5846003501c486000e00c54004c0e02050542c00e8400c01c90a0747d0300c003215020841e4803000010380b503500050781c000e00b100403110045041100442c5c9000140ca07010f040170a0518250700985040400460b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 790146663 1250 790145413 790145429
    0x5031c111c080601030e030304150e030403060e0a03080f01080a0f031707030608010f0c05070615030803070908060a11120402011b0b0f010501020f0637020c0c220504021306 76
    0x40b06004181d030301030081d6689400c80400460840c9485c0d1240e40c12505030641161300d040d84c40500310080003052044a015582100084c000440c0e400344207a41c07060380050980000f960380001c41d00e6024000e00b11812617481074010007202000d92640340c549403404e2000c50501402101000c1180203002c04184a0360341d541300010420b03e400806400c3d0f54514078101c50f080d10b040383e40152581c0000a540d40c95405c03610004030303000c03400d00580c04440980c1028104034000702c1000701603079002c0e41c00000c0e54440e001b038070b00d0790300d66114403000d4824020245008503010f00624070504121109142cac418014505008581c5c1030320103441c0580d62240069500c5000b800c1040142086101100c0c01400284000c2520700318a504494444001401d502c29000d0320403600c3ca80705009400e41c5402c14410846142841c42e6441c0c030000941c003c0f03020030740c2c0d4000d000f41d443d114030300800d480d0541d50740c401c120207400b80840c440100608000300101c1c0d110b50310000d944100041407269001500c810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 790147913 1250 790146663 790146677
    0x2100c030f14060319140703050a1202161512020d020a0201320a0902031501030b100302091611030f090a090b0a0302060a0c02031c0905031c111c 64
    0x400c0d894280c035074600c801c2424296078814044591800107115a61015101361245c400d075292810803600c03801c06032058007500c20014044140a0082210404140325034180d40040300384020070703611a480c2030a01038488080c1c81040041411420401050016a180840d1003489980011040303811403019115140d43c041b030b4140c0010340912070020440c01003007007020440202c0d0250008a500c00c0e14421a03c60410085400e6000d076400011030540d00901740c07080491802182c50311001c0034402038400c540c1c50408035845182480000040d00d4000e003401045986002e030302100011884401010461020343d1030703a900c0c1d8140054000c1c4000a54440c0c0d4944044003040180c040039040122a2031401c01d01d10120396548100d1070031664107490460b11005038160540f410800c1d4074010f9054056090038405481c001001200c05031880c0d01d503000c00ea40c840c0141981c50002d49072401c00010201075a5543e1405a94400c48050000e000c03201c0701081480d000007030300030814206000c01e43e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 790149163 1250 790147913 790147931
    0xf0b0c040f23040915140f010b03040302060609150a0803040806090303130201080408070b0a15120209041b030f0846050d06061218170a02100c03 64
    0x6801c0e24000a02041d0300c036102d86002c203210030040c2c2c041c07401080d100326654030512003040303080041d1145528411408016000280407004c070a144101c80c000300c0c00342d0620000c240400c0c401d0650b40502d0701903000302200c1e07a403c0c091100410014100d0300d1912005103c50503d40d482c0d4007030102a00240c006142c40d41c0c54104014989800070340381c0c00141c1c1051003044008112540c00f071030303580d4091800b100c03503448a080c458a50301c50040007400036074900d0f08015204072250000d03820032403d00100c081050740d4020160b00c10300c0c17000d402540f0040707800c003181c0880c0040142c09491080c0b4076404000c03590300d80e617881020010810840e1390101c04203201594800080c0c90100c00c1c2e415140c03200c00d081c086081140408000010700780c01201d8607401ca10034912402c19910400d40c40e2504000c040d4641c0409010f800c101540700e16142c0c10640c1443e40d14005d031400c001001d605c644070390f10351200c110f0019010740103072000c4411845050344c56800102e06020b0000405026240010b02d090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 790150413 1250 790149163 790149179
    0x2030c0a17100606050712051612120506130518061f081618060b0408010b0f1806060309010b03011404033b030c04021207110a051203040f0b0c04 64
    0x841c00c2d8014901454018100000c1c0c1c1c01600312000c10768032107240d00003607940c1c20b42a911401031003401054164400070105c1084030410803903600d80d80c40d880c2c040c40c518119021030203543d022070f0f100d9003105181c1c1054043c40b00e541c0102d60040f860300161008400c03040402403401408540c540301c2d00f500040011035449800c500d010240c0a0b0501400d9410103401290044016621410320034194a10113402c080620350301c01001340620300ba46039515603030b452409010f4810607a00c50720420011080c01c006241c1109400d111909030003841840781c0d01c1e042000200d0700014084c015039502e502140c002503800f880f5082221001030b050020398101424010240910021055500300c2039400d00b400130700c2903600300c000121100149042000028006c642080c20f0301c1d226980190012513010030721061807980c103200f0400c554860380c0c1c0001e007003402680c48100030700c054034540044d681d03a82c481010300c00560380300e809509a003801c0c0303905035101400980201c41780107002c10701080030b1000780 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 790151663 1250 790150413 790150423
    0x706020a03140705121801150905102102120a0b160915021b15071115040f090c0309080a0801140f0315100b03010b180103050c0d0902030c0a17 63
    0x102d207880c2c6a130500c0d281d401143c14074580034145080180f01d0f0034901b18060401d400c210384403101d0106041400d0b541d03e41c0180500019503800c0c0d042d000344480441c4404002102446503000420010303144c4610fa024032400d0f2403042c40e140b03000c3c0610070030304000c1042d0860040c05408c00241a21000301803110062807100c0da9007150144402044001d4102a8005982c60070342101645401034014010002042c0c07003048148070030104c1c80860349a0070700c081c020318410441c80545400c01002880c0b4404040d03840349004581644629a40c24041c4440c5540080b00d01142400c000cd8541c0568450482c1038100c4041100000c01c076030018403402c02850070204041a05a0341d1051001c03945000a8a660000312182002e0a9041c0000e290f5200c0c0c070580781c001c0100305a15950380d61105954052980714004291540001200300d171101d520034481d9611544003c1203090500b881d1501d8200a0500040280d034948a4061070348055541c207103800d002002c0c410f07948102480c0a0003014101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 790152913 1250 790151663 790151671
    0x70303050711010f0c060c050c150603150618270606030705040e0c0108060f0406080601030b06030a240b191e140105031008071412010509070501050903030706020a0314 74
    0x10403401c0c60084a141c0107040340300002e5001b0404906924425030454881c011100c13444a90b2180380c40c182c80c108910310003035015071019002d0307800c42d080b40580e10200303e10644250f034101003203103101c9040d04462903040303800001198a440c40c03400d82c041c54800c0e00d040782c54081c685403c100c00b4080d040c942042aa40201b40a403130510a00503c0c01c0c175680c4690f480d0303440c64103108030440040c1041e036940c000640c803405c00030300403c44030b501d54010565402090000f2540e03240000040742640c68002403c48105600402201280a52040d690f404000da4042c039070030a600d4541c1c610090342e9001d250440919807803907040655246c0390880200d022481300b0b074084039109080c01e100494002543d45e810f01400c0c00c00e555aa1600004146248150361000034140280c0708003040210f105010080180340c00c03101c240d80d04030390884040c02c860003940c1d049801e500500301000517500690142c41200001400e0f02d00300b03030b0303a0f84916043e40d028610307a40000350303640c030301080c0c01c00200419500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 790154163 1250 790152913 790152917
    0xa0506040c1b03091701021c0212010512030c060a0c120e06011202012a060b03060f01030b1b03090c030f12121005030d0e0a0602190b0702010e07030305071101 70
    0x1140c0030403001e00b40070700307034100007254100048812040c1401500c00000900c1c0a51003443c0d417480403000b2034000c2d00594194400404001500b0300341504d5030094a0146864040380c0c0040e034a00f4040101e4482c0d07501d4280c405d80014401c412100030103000b8644510003440b404500039400741001040703456000010702d40c3c0d9140c00901c10b80c1c1c4500240440c1941d949030010302000b203007800140d510340201d043c0107810440780c451181510b50101805000310384a001c052002c0c0c2e8061081503202c2904a89043d00300c00f5840040012840104074541c002c810640c00240584c041130554449500c1110405401d50041881d0070450804010310703100080400007424200b071092080d0480c034070441c2c50951041d074601021801204032540f4010086ca80102158000c034107810001d05950444994103205070310048000076000e0010800c10003002e0341c10503907150400305642d101e55042c0c01600f510f04540d40c4905580f82c000c4100884406540a80c03251600e03440c26160200c901b95290340d1080c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 790155413 1250 790154163 790154171
    0x131b050a06090b030a05090726010c030905060402130f020c0f060108070b040b07052e05010f0f05092203080103050d0203040e070c030c0501111206060a02030f18090a02030a050604 79
    0x41581100fa00b030320307042041c008022070a81c680d920301501d0310601d6000154403c0d200b038003014603c5490800440164042c0d0002d02401c241403800f41d04541d42d9450140c41d94200c03400150061030220b032020030240d02203500065a22103d1046800c0360020b100c0c0d42d206900107003c58140b20307010403001c0d00400104009100c400d00740f00c015685401075205610340b005003c125402044000d2090804004508440030800d43e0041e0521114070300180c2e006031924900000400d0111490103010155090b0394095241d00380381070180104410010102240801200070000d13500d50131307004040555000f580c0300b440341d5045003002403d204030040024213550007000f00b0002d00c1d184200303017a440b40050070503c0c1c850805003002d4525104101004007594a001d05920040b40c0d90700c0906944110000068a00da40da141400314911400ba28030000d0380c01030100e42c0003410608014140844a44503030604480c1090104003c00c07401d440f500c24494011042104c1e6031124400d460b03210300304450600c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 790156663 1250 790155413 790155419
    0x6020c03030702101d0306070503010603180209060d0201030f0f02040302090a09110609010c15150e10030627050d0314040201090302060d11040b0c0f031c05131b050a0609 75
    0x2003070790040e20032903c02d0000003110700e000507001c01c51251700d15101400b0383ea0f4038640040000c00350740c000d00685000c680b420126100c02a5130424610741c2030340c0600402d042d17448000c1000440300703034200c0032410140c0350320100c1500b0a060152623040d2030030394000350300c80c0c4c00c5104000d13614000909511902d490b141051020980138022160f800030252949503a6480c2c0800480b0124500c08014281d00c1d441e0b480c42c240d0b184154090724000300349000c0f10200680300c000d400e0a100301074403000c40c0c82c3d201500c01d1001c03581d164403200c4100f0f810340710b022444a1240c003a0500c05121401510075401544000c0c0c4a030f41c160086455403032440c00ca040713151a05900181003141341c2c0c00080d000c0c1001084025100190354010781044c0c16842c0d40f1a212650f070142e07003906600011140c14140641ca9194041503c0001a1034181500002c041040034591070f10000505008124114900003484403501207480720340311494441c01c0140b107030140c40c1001c2c02d000c0300c02c2d4503910000800801d20020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 790157913 1250 790156663 790156669
    0x4030c1208030f0402040b040e0d0f050c0303061509090106051e07121808012f1e1c0507111516030b04110a170c070f080a03150b0406020c03030702 65
    0x60742e1103024400f0b82d0002c0c1d110303030000ca00107000c0482610b40080c500b00c21310b5059400028405000e03091030351a0340aa400b09401201c4038021065901119441032004c50041d1500003c04c2250816040c101402e04190000082100c1e801b81d200f080804c100003003010306890f4080e020303091800751060081c905140b07680c07101042c2e405010090108116032242c02a4100140f02d042e000703081202c0240301170340104410205503184032180001000c10001c8117181c101c0402c081e900c00c41200084d16180300d0a07420071400503480000d4000e280c980725484420488618410280100300c02d90b510381102d24044c83d081d00d0a81003615800c0f034103460030104041d113400703007510200c0300340b8a00d4049100c2c42c014001c00d0141400c028944142d0101180c40c0b1f40071030788059400c104170b166050b180c0d2580c95181c074403545071040d00c4010f00701030091c02c00d05002c60407440041445103994500020409101c0c891300701000303540c0c0c000b0300c8140c00000b0100002d69041005c4580c0c00000c4000d507140403520342c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 790159163 1250 790157913 790157917
    0xc0105060d1205090103091209060809010b011e0903150e152403010e030a2105070503010303081f08010b040b040225080c19030f0807090b16050f0304030c1208 70
    0x20b280700304800010072480b16480703a000a881150b01c4000c041040300c54100c05004012580902400220203900207403000b001409082503150307040c0c695000d0b241c41d0084401c4040700314207803c000d00050500010000707219541e03103a100314103040e0005145130b801845030709156696100c44c282c44801428444214402040fa0000c00172010b112030004500e040030901420480044410078000440c00704001c5401007111034000180303481c9110303890b003540d000b0001c0720810303030300040000e80910060000901540e02c1e290441c81ca4154401c43c01489030701810f05400a411151246e510740d80310300d0380ea04140c001c82107412000c1f07400b9400c1c45002011290100c5503800703410300740e566214041d010321009a04542003408440c0540b00108401011000100d4540c1e0040740040d1030a1b910800031407113210b6090280d0501e6888c00701b141c0c60303d80d002c03403250059001c1c00c1c41c051100d05038100050007004800800e4151401031502e0710710b14204803100c00581d910400c000d203081050310001a0681e02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 790160413 1250 790159163 790159193
    0x110a030206070809070506040902030f0c070503120402040e011a0a0807051318120819061d061504061206080f1005040807060f020702040b010509061b1903050c0105060d 74
    0x30f440b042d0750340e8500704c0d20b2500701160f01058006400007400b150160041e00218404d81c111424000c00d0340702c09241c99554400c514010b0000e4009100803824403c03a481d1440e005070004202146025031003800d0707801c4424681c200d40c0c1e00d95000c82140546e02f0030201e24402001100090711406280001007201400da20480c041b005030b48085400080000c1442c28480c1d44d00240d01c8a1501e01940c009089401c3c283c0f00c00c079081d03003651680380c10a00c5501070203064480c091440ba161502c40140b80c01c005d80e011f4607441c1d00c10708400180400040c080080d01c01402e05903074a50074001c1d04007075034044424640241100d500504141040307124002000e104c0d4492044001030300d075440e8188204207005500700284072a0400242d03444201f180c1d0094071145000b11400c0000e0b035002c0c00151824807803d0782540e0440824070400e0f20001101000c40d01d081080f10a44080c20715032101c0b2400011442d001f1000300700d0100345c140d000c400074418030343e0255044d80c00c241c003a04243c455030400c2600f01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 790161663 1250 790160413 790160417
    0x1507060c020d2109210318020114090307030203011107110a03050706050c010b0a15030e0622050c03030706061a130b0307050715020d240e04080c030415110a03020607 73
    0x301d0412081056204480d213a401c141d104160b0207905810700705041c40c0d8000d480c0040d090805016009a41080d484040780e4140c64003000041240703081990f40d044811100c0c1d160080c01130000c05a1405c0c0205000e0101c1c200007940e6401ca03a25195060005e602010b40c0282c2c00e910042c40094070020306d00f030984c1c43d0380c100b854550302440501c5014080081005401044840700010100460a10001d443d142070301c0c180610141c01c4503a60b40c0311002c69201c3c0840e9135038001842d0000341d100b401004a409030044e01c4070444c802000c40d2131070340301d0501210303155502c45007040080c00c02d0440e003001d0300001840c507240600c0c40f01c448003511828051304640d10000408035030464020f40c01c84000552002d840340074010042100ca0080d0044841e454030b55040204104500c4058800c0d20311280700f6040c4003c9440c1001e401a0b400ca500034012a0f80c0b460070000d8081621040000d48000d00300035441901d220211072004010186075101c42c01c882c3d0080c0c1d43c10340007039008540d079a4405414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 790162913 1250 790161663 790161707
    0xf01200d120e121c09080a0306090212061c050307110a0e071d0f1003050103050c04020405060d0906020f04090b0406060c02061912061e060e090c0702010c021507060c020d 75
    0x407050540c013914070506600001442c00d042c0004002000d030141401140b01d8034100700103540e074071041d0140d11416082c41840d180d01400500c80b07103042a100304c0040f00c1030b032074071003418280c0d07448074a1640074140a0311019040c41e189800c4d0b1070480c040601610514000e2941410035800c0a800000410721030040e0301312f01c0881d10a542c41d03115070a005000020b1201c2c03403050f1000000780c0200402e0206858500a580311500c450034140200d07030132243c0103400989407007002d290380801004c2060040707504903002c01000c00c0c4c40d802c000142015100c400c20005102c0b40c402d0802040315a140e0000c0140b00d004007552015989240c1a50000040611181c5480080d450100c0d001d61005a003e01d155103001c6000c02c0600203a0800e501d40031000d032140318240e84409040d510114860001e6070f0118000700011042d46904000e0015180306042403c000e0445034000b4120410101d003403051401c001c0341e10700602003240a4100007003414006031540d50194a80144030405401d8030107040305003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 790164163 1250 790162913 790162927
    0x8030603030708070b10081f1e02070c090b09190f060e0c0c120c280206040b0c0c19050f031c020f0d0f0207050f01200d120e12 56
    0x60084036152580080d801e680c40096150281c02020159070b15038920728501d00100701f181c00003c10030038819071108003449104140c1040c3c4060132043c2c81550752400e1130030716510403030094006424900e1080214481071803c00d0041d20031903a21415041c8982090820300131050030003040004a01090752001c201d41d29144400806006564081d9000c2074041d010441c001c0c0700040a098882440c006690940307082e150906824001c0200c11a95074220b031203401924002c2032069007000f40e8076000c44c3c107aa9007030f1700044c1007500107521041d440308000407881f0740e240c014408558143c20840d8103030060400c004584407450b615004141c01207000340e40c0400c442e82c0400c5180c03125299030004041280c50b40704003c1d100c424203016051240f0801c0c50100045014040d01102c081d0a64010a02c40f4540070070803000c08000300740e86040c4019400c118a007085031120110722041c8110080403044c010041c0103064104149400c0700340d904e0000381c0b608040010400c002d0780f071505410991141d003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 790165413 1250 790164163 790164169
    0x31e0801140414010b250503160f050a050a03120207111e090109060302150a2304080f060702060601030e0a1b0503031303020102010b0a03121101021c0f0e1504080306 73
    0xd00e00400c0340d0308030070f402c0001707440c1c031140d0001c21505100d12482541e15110700c8000f1004903404170b00070180e4000340541c600710198040128013050058602646001c40c82c5c9074141403030414541980d25030840f8205d03505154101441c1c1400094101046107402d449445100444c400040050b2007103117a0440c036503480c6411080460750480040c0b1600503569107941c0c0302c0c01015944022405502030400009418424505548403030646442c4c0c8a030b1440700c0c0011010203008a03400e11440202440003152110003040f82981030361f02d440041000342003080000e0320b8035900a2200b41014101030029003440030100c0c44581c5180e104d071012145a180c2c800c1c06134900c2c00d03500507540520001c0360104400048101071800c4034000c1c0c00801081805d8014807107100918000a0946111020070117110391003041c000700580c2d680800142040d40320982c6035511404d880864440c0b03138446107000c1e480219841244503c1540800a00f0300b13850307804958180311f40c000c0c0040c14810011001a400391 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 790166663 1250 790165413 790165421
    0x320405040609020d27080702150a0503060a290c01180c060e01140a120908040602010e060f010806070503040503040f0914100503030316030b040507020307031e08011404 74
    0x840010424041c0c02d4641218400139040b41003030707862a40c01d180e0900f1425044441c0200004c9101c65030380b0007032045494464803980205822600090042104140356024901a0010150030b03035906980c0d003443c4081245c01005a00311070800020071281c00c480e0b04400e051481c81124102c561a1141c1c2c04582850060440d10314128144070b495468600b0090400b0044059070b1890316148080810b12004480d221280300305846c10300d0042020514081c082d41742010040700150000c204508141d50380701e110303000341e80304402503174403200c0b6090805000e1006540c00240000500340940c034007000240d40d00d0f40a45028203108001010600b4828240201d07805006820078600302d00f65158007480003000183d0300301c00d850030b10601003260400842041c00440b040200154115181c5490080c1031040240c540380605659502c041d9654603240140c0d446252540c000c7c5031110150705010b01035280d480402c4c1d084003444c007151140c03607800c150900e054880d8401a10321b80380c0f60b5000300f8010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 790167913 1250 790166663 790166669
    0x7052b030f0b12011b050301050303040603240e0108071703040306110d0903081510020c09100e0907140a0e040803060103090827040902010e04050903041d070905013204 74
    0x250100c3d40c031004000054000e0410910421a8898102e19050003195180404c0c01400c0d80740e00108010884144a508851140384001c4d0010304000c1403000e000590304c0d00ca51005090802c08001005039080a00814009060250409000b5080552034603280d119600005004a650300040d61910508400307550110102103001c10412850f4280544402000c803007020b0f18407480181c9202d60b040c1030a1485201206070024282034010004120000a000f85000c3d04007441c0344001804940c4400414001d03034903800030704203050a0112030004280b0340178949000c0c0c6500402049500c60f0030b402964090380001565459464130320048000c2c0c0340c0306401801c041004921a02005040507050b1480e070f080c020314030700d4264a542030000741c0c1c80402002c0e012504411000e078085c286074002980c44401c000c152840c1540300c20707c404040310044010b868a0100078200a0015084a00b54000e4102401d000400c4080f100480d4001c2c1c0c0840c1400c03c1003a14aa0492458001141640c3c06 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 790169163 1250 790167913 790167919
    0xc120405250e04142d1b092403010c030515010c1e050a0c030b060f01031b140f0c06042d02010309030c02091f0906080601030f0c0801020a0507052b030f0b 68
    0x802240540344106452012000700c50081d100011a1150b8012114106e6217000c4c0c500d882960700d18580c9080c0800150401e1130b02c003903020102889175406c0c801da03440b100d0f05407000901400e14289100c195280d1001150600103205611b001240442a4240464090601102030515985003280c146120400c00400c0003070f040c80080200046405028403d02095403110a20400f0780c3c01103054920b00380700034104442c0038500e8202c05110700514640b01c1039124150f440c04078103500c586843d9110213010202900070005101c100451f541000700c0a600c044060486080e01e20725034203c1500654000f4103043c0d4402e0000c00b010702694803903489035001021704080c1d00d4040031942d441c14100c101c810018040c0f40012954804501c6401e0640305036a0040089031b096035107400715070300507030750035034480e40c000fa0001502c14090004054540b00783d82c0b0140c980c026071404c01e19141071540e00102440d8964600910041d01c0102201e094003d45404030304106030a110400800031a40d1484d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 790170413 1250 790169163 790169203
    0x24090b0f242515050705030a0b0f0306040b0610140a1209060e030a12150e062107260d1b0b0f040515100306050c120405250e0414 57
    0x3110074102d0380294200c5001e0007154910b200d85801500c00c84d40211070450102d07a060000c1502101207030f000d000310700340c040d020144181e26400003a00d4490300b1603040324804481c0c401c2015a060040c0c0b0b510302d80d503150030300b055000f6400c0488182e501403001c007070f03080020f1403843d030304498070f1500221178054002108010703641a04021503104d40c0103c41580c0825200c032420004004144201000c000c05e010035034040506100e52000c0c0c55101134001e590046000220500281d01107041505902c9030360020004075142114a251a4299803440d0341d4000400b00c41000c840400319020141013420726110700d8195403008143d03265088030784094900301c1b0303c50801800c03107800070541d4080c9009804450340c2c801100c00c01c0c020700c00200c0d40d041c8d0020300c501c3c0c1040000c1790303a00b005410640c00c244003800d003c031841c40d504100004035400d83d416400040c10800c114404243d4501e0000070b142009041400e080d403400c0010401360008001b4074410740210310803203082c04094140c90361094000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 790171663 1250 790170413 790170457
    0x50d020c07080613050705100338040c0203221205010b0f040b030d210c05091201050601020a240617010c1b060c020124090b0f24 57
    0x381d6511407038000c94807140f1803400070a0308600002d055045095004000740007440c10001030000c00c0c4003101c0760009050311034041c8681c9190307428107204182c251007440c01c002501060203e03111760019844500030340c908400705500f03070b50100032075045070201ca50b4032054041d10070800c92031107220743c02401307000b003069942c800304441034001c0103156104940441241003050b04001c2122000c40c081541584a0300d076060a81e80101c43d0409801541810f80f40480d101c0c0c800d080680303a140a90700001403001401c481603240c81d05284140d400740780000c028500c0e100d0000303941e84220303810190805039440d01001900c8582d2080d03007805950308005202c01940c45140564000b0010004404c80d4202004410658403c962408118a684031840c541e643d40752190802030109092401c00c654940c0e450341000291800b9401000f40d1016004c18043d180102400894600e000a540314003050b40c40510b5943e2651112103102c01c08c0110307074011140c84441d40700c2d6441200099640070b22401412 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 790172913 1250 790171663 790171687
    0x30c0907020706080a0b01050301050d0c030209041515030b1f09060e0106120c12091a0c0d060503010e0a0b10120501090b0109023f09100c050f07060c050d02 69
    0x1d040f18000c0d01c82e0f24041e2102c0480d0300a68460240c00390000b00144010041d81c0392044500d8111070103140b1111149480c0c0e0049024041d0440c0d060350b5180f00f04140003e441e01c14460782500c5d008551440700041d06640e00c001542a0190401a40c0d0344d8203070040b00c0e4541aa600d200060071122000c00c4129034a00501e0400142489100042106410b0075050700c0958000d059030b2048c0c0b070b0748000d4440700001010000384036030081900e50002c08500040b210102c0340c062800307884400801610381003015528003e84555420090083c3d041400070110408001800790815034081c040c41c4440d500c04003180c1c0a54800d60001541ca1004000301c01440419444045900d00460151099a8075201c81c01c00342d10448910700701007900c5008039410b08400c507011000340d003000c1003540c070030003400340c0319400000059580391520b0b041034954450112291043d000101503509100741050348005c2e0b0b03138a0600038820007400b103e884a541c40240c9100d901100d000001048046407284501400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 790174163 1250 790172913 790172923
    0x70f052505071211090a09020418020a1d040602071b0f240e040e010b0a0611060601030c170601140f03090607020712080c01020702061b010b0607030c11030c090702 72
    0x1090715240211400840c15118101112079640e41111880b0341d909403030014400e039080300410783e41c015030340e030001a001681c490166800060640d403200c0e4103001a0b004024401030a940180d144a481221003000c40707881d002616402600554010b80f681c200b42400c1e0015401032145c1400702a848402195400802c2084000e4601400f800780a900f000040044079a00e28000400400c140c1646a0212320f40b94003d4031180d6031700c000100b8400d4030307580403880c00d07141500207038045641141010207444042055641c0958240380038000070410030006000c00b160310701012076420741c000008205900822030014400c0d100f010003940c54011110b900090f81040d258050319008031004580040d10010b403000c20744a000c20400c90a810310342da01c00a6600101c2031300c0065400748a881d0140c0d50b6403000d402c0c0c0100c9a003014446103418a00301c0d08585501e40081d01c520004c2c00440c01084d489068094015803010340c1f41203d00c8504000703071800a0441445600403005c0c2e040040350703a0301041e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 790175413 1250 790174163 790174237
    0x60204050315090d030501120f060609020a050c1204121e05030304240b060f0705011e0605100203131503020702040504061b0507080a08060a08190b0c0c06070f05 71
    0x425a040344c02450303821000c0e20310038031496011000650401011460556010300690b105200000d0f4984d6244090400ea8003c0010b000c0030a80204103030384100c000340850380442e01600702c05460641080b090034282000074078007400c090104403c96540001903242c24580940000450b5180d02d40b503e01000e40c40580c01000303030703002200e000310080400e00340500100340c1c1009216604241c00c1006001e9244c10421040d5802d64a81c40e1f07141d054040d0403164507100d491030304049400741c10441485011403015171104c1c21980100a1f010003990103202d21002c1d50140124400c00c00c003904002c40290085c8180039502c1440d14007070000300040c55109242d801100350112311440020301040d602c6005403440900302140c00c01c8560003883c03003803041c1c561100c002880000712070b447c0e800e01403500090944141e05034049004400c01c2c8150403c01030760109494040034a405003030180c158441b8009014182031020503010034800c24061415103141004c010102c0c08a40701800d12003100c101d04070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 790176663 1250 790175413 790175431
    0x703020a091a180f030703141005161106010b070201120b09070c1106040b0f0d180309080715120e0102091c111002030711010507060f0518030c07050d060204050315 72
    0x103030780740c4e080441d51402680b000030090000580717952907160402001400400c002e0003501c12100000300c0701e01c45d040c00b4501300c00020441c02d0820501601500320901402d842d0791000700100070f460f46480c2241d04a03542840d2040f01c5c413018882180142c1402201145c2c81a610800c200742c0d640d2190a0300c18041c06920502c6031030501d01c5c00d0007660320440c0501c1ca4840000c01003400702d4a5110000d280e0700004440010300415600c5441c0140320ba1350070101d00207041d1a50800c8420030401690019094803088801c5070041540054250030041c54a8130106480d807458440c520390030360664461890141030b900800c140c4d01e03003600710240c0703100003226001556132a02035282032110004100c0c40168004514281e41919640707189013040402031b0401c8410014103002984070f01a03d82c1d0b10380c9180c0042100d04140384a040c0d000c04803144003d207a841448841003101d0009403190880b01c1c141c0c1c1d4505883d1942c14644068400c46c1c224541510070211b203609158101c100003403050b036441d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 790177913 1250 790176663 790176697
    0x1180c0503090705040504080d0e0d23030105010807020f010f0213080d20030702042a020a150b130c273005010603110a0603060e0703020a091a 63
    0x401420385290106440d2040c2070742c002d40050101703040c140e0005421a0180008600300b20010000100361034580003a0710071500071101f044010b40c1c004907404008120075005118180d42c4800d0616103000521a80f410003000402280d500c0c3c1c000e0003000c2403555803c0090040445254cc018003940c40301192401421a02c00006200c640104d9680144507095407107046803c0049602c1c40714070000503501841d80070800003040182c0e2a0b1169200c0000034089100b1072900000d80c41100503d01a001e409640000b41d0080c0028064560015902c01079400019107a0940000c20115503114174a505030b24600070035203814541181c1c2e000494144601da0310440001d45254080410140c4540e07a641101c40c11101051039100750b00590701d028603c144000d02440d0749951b030a440d0716a01c00d4542e074001c400140101e0504d0810030b4058031240c1400d2109600e0b08020798440003008044d5003c044d4007099190000e84038512060003070400e07400a04040b400c0c50b55203032080d071002e580a0091110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 790179163 1250 790177913 790177931
    0x4030807110a0c1a040b0f0c0708150a1a09040b07231b160b03040839011e1a1f0905040b060a0e04180605010806130203070b0d060e0118 60
    0x4d01421179003906e0400c003115007003007410040c0503d6a00314800030191800380b0080810140320401c6030984c0075024201e4004607040640d0104201c445206600740006546540070545484001c1c1036a04254031549010103551401003c569030102e030003420000d03c06a550b90444001c02402404c02000c0c200f6040d4182841e0701e0031240d46807450302034006106912402003101041c1c0350060341d405801804018501850750b820004075821145905000c0c440c000706883c440110800d102a851158030020403101103154145a0f0614568007940401a180c001c40e900c0017100000c960030702000602050390b030b071000840036a203040b62080e2180000d24004000541450140204e031070a00c3d0103042149403540c11001100c8401840c02c441da0841c0e210300003414052000009008114013500c000545541000401403c06101410b80c5408094400003900580c2c0c0210751401103804900066030381d2070400d4101c4028042035480004041121000040c0d0002500070100d00042544810009560 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 790180413 1250 790179163 790179209
    0x1112100807081005040c0e01091b08130209060f030109080c150c07030e0109030c170105060d0215030406090519110d0c05060f0d0203090d111504030807110a0c 70
    0x441e9200e684225400342c18103480703229190b07120a40080c09600080704440d141c0c106100400b0003a48000801e960340d0888400705100803488988030b0001d880d00d506542000d200940c0b84500a00c001313445400e144001c148141e035600c8882d0400f65016000f400034016900b440407541d0801c40c460205d44c0603581e40b90840044412200c2c0c440d0207544000e9060a4194030100c500c0010070880c1418401039441c040b010800075422940100b6010041c1c40002c03e82c00e500e1829580050175890251804004010050f43c481a01c01400c01101c84116129900d50800c40040c11584074058001d0040c01e84a502032002d003c10040414056004020600700b4441031000210a1101c041d200c080c4030a014081ca00d40036000341940381d184c1c140103003001c0c105400c010886e40b082e40d4008660340850280081190080b01c000110b048146c080c3c0001c0081d00d070700c0804180020001030412242000040c01d040c040c5102c00720782d2401500715505420365181401c02020240915044155080003100d5641 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 790181663 1250 790180413 790180423
    0x4080106031b0602030c0d0c031701031b120c06050717031608090c0a0608130827030708031e0d050a050103150c0e12010204031202070f050a052211121008 68
    0x80500c200411480500880880d04c1e50035941c8d041b020440c2a10460b000080f1850055000c0e50190100007184507015803e0402142103900c84424840a0030a603c0401c40440c1e0201c111501c60500f035a40380402e01e400e09045081e0b0200b604e2500010050100f030040040c0042200001d0b41c42e6130260b0303145d2414040e541e078110114158030511180701841028402c032032140e0014903405600c244a501550b0380d42480c0c0044002443c080044110340480001c180341a40c0b0070030302900680303070080c1084c0d105a02c900c52002940030f404061a4101403980c000070803103d0b48528003000300940d05080907544003601c001e10003500c10b00040e0082190340981032142c0300140216850f00f418107040402400704107400c80c02c84590b155402d000010200b00c03041891200c0c030f0b8032940a000c116051909044080351260011800b03203a85400c00c1c040b0340c40b00000124000400d03000c0c6030b080451201440050301251000301410400442d01904010400b05068043c040032290403243e961910b0540d0340d00e03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 790182913 1250 790181663 790181677
    0x3080904201813023001151407081207020601060801050607110f03060906100b070b06010315080d020d031b0212071e030807081f090209040204080106031b060203 71
    0x1a410005100d02c840741d40003503406000054034400041c0300c00180e02e4203d8010303c1c014420810718003089111a098100c1122102100310700407003a650420b0320560b00d20510000c104288021009040fa0303113003607a010340d106958480c0d0020ba941416040c01c00c0800300603541e402c05031140c0c2d80003203070b0349005020b41030686a01820316424800140c45a001c18421002d036150000b40300c01504009031024003030340780305100c0c81000f401d007401d10345130110010030389a202e22600c0320f0a02c4200c00240350044542e81007c42464080340c0455607009454040784a81c1c4541c11500c944100b40380700c0ca401141c0c0001c2d1a2507500c0402060442d0402d40f0031202d1442c034002c0040c4c00254071502d0a8107100040d090050003010f0510000b40350302261b1121580d4801e05502248126082000c0e41d60721056523980070241182a089545501d90103110002c0070b0301500308482d80201d85044140ca96605890082c00010001d002c0140d80f400c0c480c4018501120706a200d0140010120702107000000310750175 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 790184163 1250 790182913 790182971
    0x10903031d01030207081209060f09030406140d090501200c0d0315030c0803030f07020c0130061202030d020313030b1522180308060d03030e030403080904 68
    0xd4081212101540c601da040c1416400d00650010036444c0000d804004007035402804603042030150309140c00350080800d00c42c9040d01041000c03140e40071003502d048862904025200e644054070f606800d0003000c1009070355926051070303681802415000100039001c10a0114607d55166008020510900c00c141070564002d14418805c288290700a040711840d02d9882000c150f101e03030f550421058503030301103913041d4408001c0c40505c007005005160084203500042102800050020380045460341134031500c41e0960300001c0380d43c01010b40041c6103c0381210100091a00c0e082000344510701402c06034001c2c0b04400c880c120050001088030410303000d250310000c01030304c0c41d41c940203900e85c0107100110104070b0840101140d2101c5803d0b1400d40d440d0080c0c040c40340d203041d4040040ba401c4180481d5404540c540700c0021940010789550001e030150340307203c002c55407030a0680203040440769034a918440018000188280380000d41407030b8400711003e1280141240c8814944c3d8100c440c2aa4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 790185413 1250 790184163 790184177
    0xa0314061b0901080c0c01020702190f0b030603102a030e1203010305150a090602041202150a120f1803020607091a0d2a0306080c03060c070308090a02190303020c01090303 75
    0x101d605c1e40242450800100016103010309a0b4003140010341c8910010780000301c0c10b0130030b1016583c655882d002400c4444401c5095252040019507101400c0c11150310b1559164541e0030404030b00e501712140d603a036403140740101c01c00c200710040c001e22841e69100300d18051820403207011040001140c0c12a074108004040841c0d0710204800c3c0c80300003920981c420750b81d603203c800005100b40054401010041a150328504442c01440641d501e1a185000740321403c00c521244140c00101108018001c1d42c00081c460550f010a40001c00c1c064100e00c948c100c44500d03580806600007026849080c240c1c0c2c6199500359581031202e03801003070464a01c0300340d0041c04091680c000711f5115100640710400d4424440149034044440c03c00d076140b03544000b94941105000030582044044948203064009003924503100b502c01880380107044008080001039130224500c0b9000700b200d041e405400524041c3c0480c82514010340a200e140b1089015020710b400c41c40c5030358044c5807204c0449030103403a400c07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 790186663 1250 790185413 790185421
    0x14130c0801060f0e0301050c030f0a0902030d0c170c030714030403020109141f050d0b1906200f03090109080606030601030215040b0408010603110a0b0d05060a0314061b090108 77
    0x640d2840f01c0c005088100112400030095580e07090007441c0c001c90b2180704a40d5241002240607040c0c0b10020a824000343c20f00c102d00c40107071000a80d5100303d040364580700000d40014600340d04003803080042030313602d00743c0841c4111544a01000409080344550030000792614003500058980c050b45c0f201a0204a800c5010000d001050200d051460070041021000c08152211001030100341845140011808100c02d28064560302c01c120b100c2d00c00300c0d00105d500c8828003c02c0310100b4a400f824040101c14244c841ca840b4180c0c800c0c102e8800500d080d0b607410303403080c071a044e52074100452181c00074a1070500000e0102020130703c1400380360041d0180c07601b68210340078031044070314006800d80050420800020340b0340803d4050000703404040000310320645182800421030744a84280d030712402c6068004c1007100c0031902211a070401c000d01c0480c00750b45220005050801544c00640b40581030400070745400000b15055201d00f0f00c00700500492030700c10281402d0b2380a400320300d90101e40030002103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 790187913 1250 790186663 790186667
    0x102706020f0f03070e131a0f030a0f030c0318080a02010c030e0316091407081603090221060f060f090406090c180c08060f09071814130c080106 63
    0x1c1c003405030210040c42c98850408032000c52039204644070000160354022644882c6480e003c54032031501d1890041c00051b441e00b01d8200240c41500d44144140c506264514098805000c03060301c064100f150b05404064904021307000242c8c440c030031000182c000103100c1140c08008821400d65454400801c035041c01a07005607404000c0d22029424002c00c000602c01540d410004251004265080d2008142c9400f24840c00d8500c5034a040b98088440c0c07040140c0b00e40c2c00180380c0e600c43c5000d40c400f042c0480384a42980200341480000c1c0d04041440d54040300826001e000c00081403034039085420355500c10380d1000c1d0041043d1020b030b43c040b0140070250128074009038041c0d0450701541c400911070300a0b6881d007942c1440741d48041c020a8490344d4086003129107118103001001c060401502a240c04000107d4420020001e148941602070200301064414020158494010101008200c0d06c0d004410b00002c5c0c1c52104601c21441444403e44030013403802040003086c1151101c0540783d0800c441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 790189163 1250 790187913 790187917
    0x3060605070813170a032c092d1806010b04060507050309060a0804020117010f09050406021306030b04180b06060306150d02030f010506280210060810270602 69
    0x4106040040c00844c1c1c1000010403408043e85403801886010160b145c013030006500e42108045079500749401c50382d243e10540400e0a0340400b211804c499a40c1c0031a07002070a034911028402d00031150301c00d855003459890549000700344000c030381203a0003210740e01c541e80c2d03d0003401401030b078000500003003100c540a68040c155452066083d00e04014240d00400d006801070078568002032030080030b0006650300300c41c160030071401543d400d40380c540c11b01401ea00540c200b0b219032108981e403040040e0600410b54195003940c500d103076101800e1952024024090421017950030301c00c62410540c1128540c012554040380740c1d000395000300c5980c41ca010026035400050246800c0031010086015070301d00304c002080b0012901c400141c8904089840a507400340c143c0040d401094200000c074500d440006014801c500350190a241000b01c0c01c00407420150f41e80403a00b034040c00c048000c182075101003442c1400d425401c90400442c441e0007400f5066a0070f9040080e40460a4230702c25000c68102d0300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 790190413 1250 790189163 790189177
    0x3030715050c120a0605040b060a050a0c03092103080108011a0d03050f0d0f2306040c0306081f050c070206041202061b100e160e060d020a06110d030606050708 70
    0x1140509003800062181400842200c82180307445d51000244458a014410758030304a6096450720b081500f80300b005003403485001203113020702040107070320000c0604c00c1003c01c0151610780d141d52005100356942c0040210055000c4000c11030280004c0b841850522951343c010302441d0781442241060b2051104000841d0015400c102e020000d140c00104000001d1144440f801d00002c1c84000d201038001c202c2c3c503140c640c0d0b0300c1e403200d000103c261100200031054002900f1200000c07654903001c0c00307400422403035001e521203000302507051403400e012540d01000c80390301a0080c095075880010580c2c0520803c030b0300a52000040c04203101103040381d01660403807031015007210314252011001d0f907482105000042e0792a404840c4075540c005d124022000b500d09140020321640c10b844003c4020380b04140520a01d000c8248000351690351103000b0260500c1e000782c03103074902036290a170007002c1c118040c68002e614416440a4604240300c0d1185404903155513540345d0610b00e4a82d51601640c2c8100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 790191663 1250 790190413 790190431
    0x80d0e100219050c030d06061e050301030305030403050c0109020a08030c0f070609180608060a0603150902060f0a050f030702070e16020303040828021023010b03060d06020a0c020f0303071505 84
    0x300100e107400c5000d2003007d0207041c554640b100111621991030380f19014051500b070800500b4401000081c1c0c10000b80c941155160034626103c40d081c204940c010519058040c3d40009800000516900040020030049400c3c0060340d40125071003904551303408040c13240070000790710580104041e59162001058803495050042811541d030081c0ca45000d81c19214207403003594980040040000e22040007541c412451014003620889030002166801840e1244451801c0013500d04502d61158049405540d104100c1c82e84a04268500a6451b170302400f6100c0100c4459001c02c4031018458170188a0003000e60086255a480e40e49640388d0784c11515860769640101c45041c01c4850044001004c0c1090701d500900c0d2100701d5282490a031000405007813254045d00c150b082c0c01c4a0355006881c152245c0342d20031980d9854400100302e01400b12035016224602c08944881d200d5030042c050b10f1401d0007100c8401e0f814520720105501c0c1d20079000020051030a22a130510400c04d540c021550081900d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 790192913 1250 790191663 790191667
    0xd1805090c1b0307050601140a06020d0801031209080a0f05210324131406040c02030f0901230903071d0610021009060b03061030080d0e100219050c03 66
    0xd0f85d80614150302a000011400c3c3c10769a031000c681040906400288154402000c05803007101000d4040001800050301503035006100c070300058000c10360100104411000c4881c2c250f458200f1a400701c6509000312210301981d04101e0300169082031440242c91a06c0359036143d612070321b90328680a03207000c1c02e44820b010300c9003907032219070b450180c855a000d0340c20340301046034078440d2000d42c00148001e16492195203462191100700e81c2c004203540c100c4440c52072140d80c9030050130050f80d14407564450302030b0000d0445004840c4010050180000a4094084809084e00d440c2c1041100c081d24618084c0d031025640000c01c07500c0c103000f0350b454489840c0103503024090008096416280b00d540161074283c1c0741c02d1005001d0504000d410f900034000144c405c4028100391120003442940d2642200b0f180c40d80e0112a0080031601d080121240c3c8580081d66840c041d140e18405070000001142443c011036000381007405480c0203c0d68400780121100d1103c10040b84140c869400148084805e8882 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 790194163 1250 790192913 790192927
    0xe011707090203010801140603160b0f0903011b03150608060d06060503030309071e0806071421070f17060103180c1707080a1e11030d1805090c1b03 65
    0x182c4000e50103005d00078004140b0122008400e48a440044c00c114001d5100a9000001c5c82c44901c070700c415070304140d680550b61030720030900f216240180442030790f155280107031050003412200b1200f40d19410603207060200300380c05084080800240d10508012580d44800181945844c180c952034607803240e5400124646c0b504040303803942d00200e850119903405400c0510806410400303c0500a00c844001c10b01c66081101040c0c66120140c01001400398105890200c1d000b654142c80044021942040708289012005041c4040942c1e0401c040741846202d4032a0b248034601411560b17400080c0408607446002c011001004000341c203055141e8590071100001d09004903034802051400a82c0000b2000c901200b0b05081855112020790b0380402100000514140000702c0c2495400c4000c0c0300c2c961090031b03c00700c442d6412241a0340342c01040540040c141e00320300e50192051000c40c0e059060380d100d0092200302c0d03405031022102010140010300401030301c44134811204d40214203590420f09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 790195413 1250 790194163 790194179
    0x9031403071a0a1d0c09070c050a060603060b04050601140d06230906060a0c0209070c08070c0e01060c0317040f020d0809041116320c190e011707 64
    0x107000201e10108103000424072549580c01e0244081042c64080402d18450854604c0b960f61090303191390710700070703900c540000e440c55001d040030384650340d0401e00396020a000f901d4404000e020782e0008407245071402400e49410b0074640f0038144100d00686900d02c200d200203003200140d030410110318421716125071011801d207441c90355400b1081154400100082c00610411070034100082107140030304000d0044c07220b810380c4640c1010b080f0b0b8055542d0309007a1507020b0220341d03006000d034018241420002d005020003069042002c1101d00d8044000d100e640c840c0411140000340b24030280000301c4542c580d91003021600d18898215119004500c160100c65020958005001c0c40545480c0760114041000b42450300880e0b00d110700440547c0d181021441402201c145103810242c012240d01808140b00f14145209941c51000c002801c20706041c8050b40e555030703602c074120032801030b241c54000072a42c0500e551101d0079211a600c080c1040d0b0700b0304a454040c09201c42210310705101d03107400054000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 790196663 1250 790195413 790195433
    0x3022109100302130608040c1707030803150a050f0607171603080709051801121103070f030c0f0b0f0a1b0609060b0a05090a0b03010b1503070206090d0903140307 71
    0x100c942c40141c0c5030504444841000401c507400102401002d40c2007100185500300d00b0030039544c0f100c601c03a403410b081301b0025142413095080245014000018031a05400111b00544160801c4503401405901c40c400e114024020118840c2c010000303100500c0001e0f14440c00c7d041700b60704045000d040404001071040c07904004003056002c940c00c901032000b0340341d11241410191900f62400704500441c20100c0c00f60640511584034114000d030800410818000c0081650400050485000c980c40d490b501555220510044401010310303000041e0409540003ca400c40311160442d40c01d102f0340c04c0c4641801d0380525003e504220356802a880c444805c03000101d0b5031800307200c0000d01400903240600403921040039851007030002000c204869a1120b00c0d42d1350000642d0700c0402c401003c28003181c0948801d14885601048030007103641480300b0607000e1031003202e55a0850340a1346030f103040c19894801d40c000003800149100d4052020a00c001034103214051544101e9240079215158081c0003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 790197913 1250 790196663 790196689
    0x606250b010e0c04240e040e010507030614033d024b0903120a08072c0a08030d1e06120609051e1f0903022109 49
    0x8a000d000c018040e00541c840d8480d070008640102a15140c1050040701c1e0f20140405c410810005810411640320b2080107002407400b4080e01c184642e80c02c41c0c813150302030001103035040b0000b4035000b000104585030036a94881700c03201501a01c000500540c1480002d80824049141e82003070340d00c140d00c6552100c41d083c43c05046c2840058881810091215450100c05008186004145080d0482880440c40002a481e030840018145d0240c1940b09403603000d803006456040c041c0c2c45900c00300181c50070041c650030382241c0d5088921382c2c940d5402d03100e403205202c2040e05402c06040d43c0c01c03001d00a5a18403843c940040090404980e41d20348140703180c2c00b417208401e21940711a05040790344000840a0710b545003d5005210482c1003100e005122409010007500c03140c0c907142c55105100040c0b0441700d94154030041c40e0300c0c00c01e0500700d995075282d28403051440103050a510a0f80201d2a111f40300006906602904110540322003c444811006240f5031811808008850070b65070307504080c03400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 790199163 1250 790197913 790197923
    0x219060507020c0604060807030518010204060207080705010c0807060903022a130e19080405060313030e03010c120e070f0f0302030f06070e10170f01050306061008060625 75
    0x12078a03140c0720090500c52180304482c000c8070140014041d05820501080d400307100c2e480d0001d03050b910740800458821901010754080c0d44000340c0800d000e580070503050700362a820030071602d41650359001142c155031020806070903d50180020000540e054108000c001c1c068030459008a0050501c5903001507004211450240e01d981007007200c0c01c2c08035191480150116080144502c15041691103040319140c001060801c0070f075000801c5050f60a94000c0e01010b007000c3c0c1c907407500d40541840f400119806401040f4003100b1034809203014099a5107040d140d40d0740f00ca4070340107010a070303024201003280f140850054080226011820505800090220841a0340024618014181000703000304100d40c83d42c100d802046440f640010740c0c090070400554441880028000c812030300c00030740c19010b0340030402c6801449500704c0041c9010f4180c41c000c0301a50b40a4840100300030b901100c5c07007060070100b034191002800e03900d424000741c40c03281d114a160f203108112283d13038007803600c15401c802c0710303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 790200413 1250 790199163 790199171
    0x915130f08011404030203190903080703171807330905042a200610180504020d0204020c0c0a0b0c070e041110032703020c0a0e0f040201021906 63
    0x551070034020100122542c0010190038205514021344034801c484403c0d0301e0940e000c505500082c81400c072500116002241c0a4440145150003001c02c14005210380d1890100808102004040300400d6801e0841d0707401458900d1509800201c0c2c09050710f000c101c0500d0484172248660800d203425124800d040e91030321156801c003070401c400c0b1503410030010300b952152000d20007103443c4030600010240b106c0c2000403810318200038082946420203211a0030307000e07071824004025508910003041d2499074140640084070503407854101c401c1120069400b840c5036a0890240c1059030040182d80702580684a00c1030041c3c02042100c4c0040c1c0c8044c0f660303040000c506505150500c0124081c11145c4901006810b2a45070b07540000c848810841c81036080c404035825803400b03540a0360340d54540148512485421711205c82041121074029005401148201c000515051440f102031741e00500200040e511241c85203170440100600490641c841c0c043c400c044007600400c010302c4244680380c042 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 790201663 1250 790200413 790200419
    0x2604062003071b0b0909010e090307020a0e0708070c031710080304140a0b040602060a11040f08030a0221041a0c070f03150902180a060f08010c090803070203030915130f 74
    0x30342c00d030f151a031007070303a5042050100300c1495849101181c110346038141e10b443c04d0b40b110404d060030340c82207140003944900025000101c8100140885205112a44540a1640da49581035a80c0b04a0041c000c0000e90b902040190f01c0500700b5009405c2900b8a101e0240703942c403000598619031154001840110003030100802d985403460049014042c3c0e460760505161608001035528407005c0c1404940ea03880e056094080400c81d802d41d0001c0c0b000c1040764a030141d8aa081540b65849203259030014014062031a10341c2000301000c2b1070541700414007030315181c0b03045145500209c0500200070410410005c84443c1e0340100400005001520340c1e559102e865803400180324101c000072951640e0420303070404056510808a69440c6a404030000c103182c0e2010070640060400f41c0111060441008021400c07000550140601880300d840c1c81c0d0410352180081aa20b000e2040700a5256004001c2800070b400d03c402800c500c40102804a030500c002c520b04d15030400340c141c206001d00b10201c2020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 790202913 1250 790201663 790201703
    0x706150803031005030708030408120f0903010212010512162106020d0617070f2c0106020309040f05010305120f040b030a090209070e0906060a0504030b040b04260406200307 76
    0xd0360040c8103607c02103203070a14180c03001d074a40444a09041e44e00d0004985950400140812200d8100b0010001c658030440c0b0f011302e41400d070082c0240340c02516164885441c5207000a8014203515807034510070703c12481d16260405091802611030301095034800d40100045242c0094651490f084101107070b01030414040000c06400c02e40d24040c2c942c040a42003050045801107074059901521410142e0040c64082d660141030030703101c0c98030640d04440002510f80d0301101610904070100c070140f024911006035031081c0c60083c00007504c260054400210b56165100007880150401d01120381042e560713140140385600704444d4400c00581f10074a003402c524240f030360941d00c00c000e4100741d0080707040a80800c94201d00200701a00950000651558103070141007075070015640505003101a1500740303024080c1201c19201158201041c41070410031541c0c0140c4059180c09500000e030509182c41c1c0e08859004038001000c1d8a840580585d156442c2c050000b002d0541c011154144030030013030162 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 790204163 1250 790202913 790202923
    0x602070c0e06010504060e131b170112031d0301091406040302010c091211031204061d0a12030e011b030f0f0203031b0d11130e01090b06070615080303100503 69
    0x1010f0b0400400700014400ca540084105800980644142c030400030f200c42d240004203440b10721b03603007582c0c4c5044001c01400c0e07000d141c4052040054090358400d1340c2c0d605141800007000d100c01400710b1148841c01030b01d0b0400f605100c00c035140090020804d2411a159031301400c070a07000558064010408002c203040c0c090141d0b001c10708551404140c09454114500b81403440044020018102400102c041c3d41e42007000014841c01c04c190340703a80340d5031103101a220420041418031388802c1c41000341c00b00e20340120101d08803500060400b5440701c482d9411142030b4400d060481c1408605506c5420070440003110000c45803003629030410030319262501511740007681c00e510b801c55004104108600c1d401141004109000c00b004d5900c8035214034402c4064000944100701c01d10000c540b40644582d07903c512012100d0027408a0345690300c9803003003400e0b07400400120341c01c03041c20006800051200da020050341412055420020780d140c007880f50665200340c0704e00450550158081c4514038003801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 790205413 1250 790204163 790204171
    0x5130f030f0807090e16020f1e281707050a0809090f0c091e0301020327010c08041502090d030305011403070815090a12020604060501170a1e0602070c0e 67
    0x1400000e42d1720706002c1c2ea943c030900074502080344c00c084050900e000d000f04552501c180c00700080e00c54880c1c2e51800c0060b0501d0070005c824603031003401003080309082000c202e24006100c00c1d400c60b10201c81a20382400c60b000b0b500311071910303200400a10002c11000d00007000241e11035100207503504044420400350b120058034070000c81e0484001d0000d9000c2e0300040741c3da0004290f40010300030390404c40b070703042800030800001d4140d4000410002080c01500c1e69049004120803c1c00288103000d18aa0072a417404002001064100000c40c0c007041c03140d42d21040c2c20000107405850402c0d8040826100729070280110046501d03140180301802c85150076440300d11090f40100003e51600c99800d42d580441c01505524030b481c0c10205415410a000030466650460211030000c2000342000750340c0c82040b10280c800e03900c0d110000c542802100c5035080d040380038100030040244642c444601c003807607034074020380390001c019a0600010388600107840c00303500440078034400f0b62424140ca14400c100130 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 790206663 1250 790205413 790205417
    0x60e0604051608060301020d06170708030a021b060910030b090c090f060a020f0a0f0c0b0313020f012304030501050703021207112103070f020106050a0905130f030f0807 74
    0x81142c207403511210814091210300d0110070356101c0ca000b0900a01c00c0700e00b0003200328107001c404101e00c0c400c000c020f00d031041d6400803035552a654681c0035490b0702501841e44010781028003640c2d88807694031400c3c902c4407402020301c0e24060039600024036520b4401e90840101e901d60450180f28070b0720342ca4a59100e2070192580f450100f400001541c00b00715804614480c40010400d0451301e80308000c56600f00aa03001240d0b100001820304140c076071500181240c40d0b11603918041100360700034056038024105a801e042070b0321055400c102c0407841c499a00390412485580e0142110080c10480c49201c2004031115641c1e801c5041184c2507820041201c0181801000b0210010302c502d9a15584440c591401b20030041c40d4100480c1050f043d19110b2202c0e05540d444040782c001007100540c0182f00984a4074009940060140e080c3e904600c0fa903a031010909004204003505500200c2d400141143c03414020001035660000b029061402075000524403001c0f040351542004805400c17007032038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 790207913 1250 790206663 790206671
    0x6020f0c03010b0102030a050d06030204020c1005070201090308010621110d061e0e09120d060503010c080105031015050301020c0d081b070609030507050601080d020d0c260c030d060e0604 82
    0x220f001035036a02c1244c0e8024100500001c00d01c02c851401d500080c059a4010420355840040340d183c25982c1080c0c04042ca14689004041062540140301e41111785a250f154114607170700e8504156205142d0483d54070340392a04542440400b1850301c100c501000014518a4449014490038002c866440d00400302c00890581000d00100c031028034041290784100c3c900c0161f644050f016401c04000d1420070750400000304825043e100300350010400d51f501500200014201030b2011100340d8404c0c8516078254002c964a105c00c501e0075000711079040301c8c030f07041448a5a51080840d00f2603000d46803106442e0420341307280c40300a40c88103456070001c040030521038016042c0348003035055101d2400c0080401e59103044c410301300f5008605840480e600401a611300b076135181b4000c0c0d1947c485602d148010b0003107000c884141c3e070107005440c2e100d940120103107164040c1c0100400703030403401e001041e43d140002c0c8600e50004408000411075034895032800b013440761400303001017540180a01454406d03420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 790209163 1250 790207913 790207931
    0x30a020f0705030307110a0e1017010c0e090711100f0b010507050304050105130308070b010608090a0b04110a17100b15071218060323040b010b0c100606020f0c0301 72
    0x8000f091700c420329000704400f0900641200015005d00550307210484401ca80c00c01c114407103140000007070444216181c5242080001014203003210a10410000807440301145c0f2070403400c0000032241c0c419540e06041d0403d052048a2501c0d16034004859a9200d45413100c60203000ca450081542d030349020708005080010a9941d00d40701d0046000305c50402c00041008440e1036000c0b4801801140c020b2002581c2e11003c1c10000e007a04400d0040e18040b4005002207503003400f002a03d460344540241000c0d040d6102c540d10700d031001032501025a84610514408180682141c05001603034910400801d01c0300e03102401d0400340c1d07042003151882040b401c0045140e01c174a8500710b601d00b90f44080b046010341c821000c103548032480802c0c1c8400c41132400702c0c0407426981583c040010102d50f0411803010521301c0c01035414015040b038000b410048018010020001600080d019041c0000152640c40c020083c034072086616540c40200180e0118400c0d6845c65418441706200a1098000f840a051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 790210413 1250 790209163 790209169
    0x60f040c050a03020c0c1c0204150b0702120708010e06010e0f07080403120f0606050421120f020c13141b0313020619030b12060106170c070c0305030a020f0705 70
    0x250b0444241415000034031660040d80070b01582e5403440707006001e4400c2c550903441c0e1000ca000c1c1060f040b409580380c1074011b2641c049420f03907842110b0502c0c1c981450300d689c550a014028011109907002c0b403141040c0820960020b014032403054460500406496241c00201c0f10000b41c0503221424101e0502c0502c500d690780001441e07403040e0103041007040c0c0f800c80c0d5581002499100301c00c01c4520724100d004502d2b80c2c0d0000c020030440350341e14070b2301c00a015510002c240d19641d2500040000d8a8451180d01c0c0c2400b49031046007640302801950b4940c03145001244104c10105152a1402e0b42c0b9241039003182d400d84181500046407080260100c2c0f4040303000c0366036110261041840307113001c0c25010110b6950100f00d5019411280068049008044000e009443c451802604c034a08204010990250001d01c1034125007460361000c6001905200184000001400051424100700019000f048650340c03224000c6110310025659444440d20080c28040001d005008541110608100640e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 790211663 1250 790210413 790210417
    0xa05101a07020402340809040e0f15010602011116170714010f0e060601080a2f0a0e061602090a14090a12020a0203070308090301201801090510181d060f040c05 70
    0x6050300c0008605180c01c000d02d2400345146022b60240c4030740604688022011520241250104d400a0040740040ea4651185000e01e1074100d4000300d030303040786801251078424280381d21199002020300c1e00100303440700c00800541d2500d80143c4d070345591616800403001d109400031001048003501c0c06044c8800003c000801c007502145000d07850f016110820070b080c02c201e880260148400d81d081c0280d460301404240c10024140c4040380d203850804400b03050000807540e20184032640071584034141c0c0d00300040040081e0400701e401d603444158001c00c2010030044c0307009003003a1000b000322003d1850681c0161203194030410031900705085030380c0140c60024281003581e03400b010494449103084040b82c0144000c41c91800d604204d20840d00c40c036100400141021107400c0e416158112400d0015202100d540c0304803500804c0007a019004544074000058000c0c0f40b08d8a2070240c982d8400030b4020b41d158400c042d0b0b5807403a082060010741d00d412411a0600d000540e410302c001007281c000030f0054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 790212913 1250 790211663 790211677
    0x809150c1507050d0e0c10030b040c1809050a020403121106011403120702040b09071d040903050d0e01091712090d17040f020406030b0f0a05101a070204023408 70
    0x341c41e4040c0070800745090140300302d00c00001c0e000d004105030400300107019100c03800c103450042d0b1070a519803101d40d1040b03078414020a4100ea50030cc0240c5024a40c50041c200246401000356085c4004400500e89c06038054114488ea40c9118030810b4244085080ca90180c2c45030460441403007030f20985440100b030340030200c50300750107003511205240042000340403400d41c0c0642c00b400c507000f00301501d608024410040c040f08503e110305601b03a0f0080c03104460030040041c1c0030030360510071124501440e810102c082c0c5c1e0040c001040b140e40300e9a8900c0012030a41080d0420400440c03808813401d060340740250f0101c40b450040410010020014195a1504214180e1140c40030300180c1880601c10400826560150042100070340d6824008040c04082d181502c0700000c54000c40e22a103203601859024001000c40a5507030748c501061065038851fa440f040150f44001c0c004500036a80b50310181c088161009a04140c401a2510f044401c669030483c030301c100081e070300000d004607550109542c16 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 790214163 1250 790212913 790212937
    0xe04051911040509011d01080c010801030f0f0b01092711041d03030f070807170f090a0501140601030605060310051309060f0914070b0d02070809150c150705 69
    0x81690744041001c070510580d00000c1e009203500000003480b1030003a001440d146061a222580c99803030340740203910b400e03103c140350340001c0703c0000500105099041010f803403071180c0a05100c0c149959203188143d00c00340e00000e84142da0300e903968516038490600080b041080351480000545c42d0b540c060760800c0b030000e01ca01a96550b5118a03e804d01550341c481c0c640c00d10000c0b00d0b260f02c0d040121454000040318030000240718800400c0c641c501507443c01c03030040e40e00c805440700303603940c40c0694007072010043c148071091240c030501d00003180c0b083c841d101000a136003501d88224034200c400981a22140d0748a0b0380500c40030030410542c1c4402d010700b203040e1101140c04001c918045402c25000d000600005000d8525040d10406019425440560301922403405100ca8501010354207840e03a0b0345d40701b04414078000300411200a03a499004154082c03080400074113011000300440c4135040d4009070b840b04260f0024064110310b20400c1a0000318048160606081c07924000003800e0b40a2140303010302c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 790215413 1250 790214163 790214171
    0x622150c050c070b030a060905160f030b0612090d080408220b180a050a05030712020a08161d0105210c060d060e060a030f030503090a0210050a0e040519 67
    0x840e0301c12802c460b107041014040b1044162208804515984141d4004602034138200000880c92414050786219030b51190351280705629994080d0b400c4c4801800740401c25a07542d80210710f40c0d45803070103004420740301c00481a051418904903331510400b403e05000703100000c0200000100a4801c4480d50032320b10b880038034510040c004c0e0071103d400f2130300280c2c4403403c0825079400040f13440000b101c118004a030004c03d850b42d52010300aa2030414045d0f2505500090014000c402e401140c03100c2582c406840704403065603c201e000d00300040041e0003440000070000c200041400d9000420743c100c02042d0448280d4034100000c0d107402000306481f0501d14100310402210341d4103200c5291703101006018540c0d0b0b0b80c20031070450010310083c01355601402209000c00e403641400180c02007502d5022303500b00c980b901e503614240c541c3d810007030880705e01d881070f040010016102d20449806c030807015260f07581c88401c0c9090103040c0302c2c107480d50903010302d141ca8104210540c3c00000170140c90300340b010001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 790216663 1250 790215413 790215431
    0xb240403021002191202100e060a02160c08010c08071d01080a1409010203061009080a0807020303130b090a290f0d0614040c020a03080f06130c02062215 67
    0xa41071891404d04d50400f5252009404203015020700788060880041e4203a900c0b0000034501c000840d0f444082600ba181d20010000e08120b14541c000d00c502208240488241d0b541c81c3d5401020103400c0c0c0085649035102e81405d0869030300411800d40003185424035580100552540300064502d1144a41c1040104808500e041219511406129880c0080b11741e0070301d0800700081c041d620079500706000d14007184841e0002c0c1d100305012010b440001001d08081903031511940f244d44c200000a07a0301d4002040f21032603010102280400411486206986440017030003041403020311a4003070320074042442c04c0f10740141c010f00e0081050f10309010300380d0f849140c11001a01c0600415041a034142d10302000803941000c0c40440c03240810f07003114140b005c6281d01070700702c2c2c43c0da40340500100454808004610720605c02c0000e2036220002421005c41d8500003401c0b801510202500c843c056003295003031110740d110354640034440065510120406004661b512035985c40700021500100d81d07501d001d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 790217913 1250 790216663 790216667
    0x1c0302090d0f020123070605060409060f140a02040e0a0b0402040b071a0105040911010c060609090b040215040b0a0c020f10111c0c060207061103040812010f030c12170d0b2404030210 80
    0x100480b0382c04c40320401401202d040dc0d04010700c94260354240010750b44000071100d1240b4000c44055901401507040d0f40c1d120324a02e01c001d0314135a95240ea0080c1c0a00001c24505098806040024000c03107400d0401d201c01c40f55218070410603000f281c00341c0c1c1070401c031134040f541026100c0f0700070780203280610030b01c0310300e050a9008041d513800400c28103040400040510084042090080d4022a204100c5000400d1400da00c1e108603c01c4901480040c030001b24854003030b4000403080c5002a14542400c01c0d040001121000144118004034154408031120a6001c100300e0703441141c95200a100085285405000e200803000c0041100d03800084020800c07080741c008071013600d10034a40d59201d09191802010359044181d220b03040340c0e440300000440c8255581d80004490f001104c2c03484d06402e00044d22a0b40700c8001d800d0f40d040310a07060074a120b400a100611706568030000c0020141502c0041213101800d4201038020150040b4488609000308002c072000c484d41110481d00c08525034000b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 790219163 1250 790217913 790217921
    0x601030b060309010b010305060406051807091a04090c080103020307091104050a0e06030f0105040213050c1c020901230301170a05010e060a1d1c0302090d0f0201230706050604 77
    0x6041c0d0001408810300035207080c15040b810f50031209072814419540c9410074402154214402c142d03012041b8859062881145840903403c000c1501d45000144c0d2541c18000c0f586956403031582801d800005c0410480a251080f507240341c3c50f925011055502d182c002956501c2c190043c814669901c00442e090b401c1024126802481d02402a0000c10303914600c4e07601c0148210b400074040d010710a8500808101845500d2003558014990a2520800d4080000804004000c2d022003a41000140ca1012160300c80106401812101580d10a411300004007107040c003c07840040c034803021030007014004412007600e055488408650b20081006d0807010700e0100b68036000f4000e0352070030b50368141c440d001003030907031144160000c248455100e002658020ba4502119040e0b0754106d00d1a43c0414581c03000e00441905040c9000342c20108142c00003250300784441011151110300001748000c55030805040d0603c10404000b00b070000301c1134284c5181511401500a2400f541d410000b02295603e40c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 790220413 1250 790219163 790219181
    0xb1905160c0b0307030b0a080607050f04031e170a0918091a0405070b0c0c1212040609210c0e04030203070b04080c0715050406210c120c03060605090603060103 70
    0x201c1c20070303010382c0c40c401820183c0c426a0100002420200c2c118000d0801c000100304031170050300180f0865944c610119202c0e08203d035002c1c0c4480c0100710010110308180780d07540304c03041c4032200e00701130039032501e80110141c51852400004103401d01c502c20010340c03c04141d20032680c070840c96215003124091070303d0090888060042c12049204072030544030801241d868425445881101c04440c1c4802c21003031180079411842000b5440914001040d040904036007000010520850382c160103410104402c9821035041040000c0c0441c00811118607003140b02c46505820241c81403005002d41c44104000f040c50044100c05c820020115080510820480b070351150001c4001c2c80c5402d05151485583d8031001c0794540910500001040300d0300c0100b80306100c48150307103d051070240b80200c16921044625030300b5200240c00e10b01425900c4050041b1114100c09650714444241c0600b00300b011124440901801c142c42d00c0d90501c18142c2010440f02c0000044440685a0ba29100100d0191010f11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 790221663 1250 790220413 790220423
    0xa030f18150e01051306060603090b0105130603050609100f0c09231306080606090606180a1505070215041d0c160b07090b03040b07260103110a0b190516 67
    0x2c2c104810707101c00e01101c0317a0841c4141c40500c802540d4070011420ba9010b024050103040a20300108214500301c04a006050441440130622a0f540e40f1941d0801703100b110100900d402200039658550980d11842842600c1c0e0a8200040500004c00a040581501900046a601c04900c4400700d00c000540f00080c0401826100368450b1144108082e04403403140308014406c10020507890315007840100e21a03603019015904121079550911440101d0f0b404a07074121a80c14401f0614040740d02c032000031022140c494a0b0b4441440c4180300d090420300e031010031000800d01061164101c845968402031080380d24041503038980140c54071691050030031800625254051000030805290000e512030ba4442d21010805a502d03800616140300440b40105089048000a43c20700d004201d00186280c680029207281c10000c0300d401103022003038205a9503007030b80404c452242c2c9030401d403290151110560740c608000e0181c0303040310481e640303c0d4aa000c0c040081645001400312101c4d80d00516008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 790222913 1250 790221663 790221671
    0xe22060e01031a2205210a0e0609010e062805030103050a060b040e0a0b01090b010e0303190903080f040302090a0e0a02150f1c05090f03040306020f1c020a030f18150e01 74
    0x7490146e54400d2090031150524080032640e020040311002500c0405049441d4040004282e07000c100040e0702041c4c0c22410310242072941407403a15003201400c8400c1078040101c03800d9254228042d03007800140700300000c00c001000140300040707022808144217a0301c1400822881c44400014000d8500030240007100c0c49000c11050503c0b280d8403000d03040b9a05007030b08000400b40c5000440c1c1c6010800e008a40541c4100000c041e801511240303210011140e203000040d00380c40b41c0e039941c1590703c450b0041494801c04201841549080e030f01a6801044401c0708100081ea00c021160320340811803800380c45950407001c412808510202103038180c2342140f005940c0c1c0c10417404944214403144400451592070000000c1184e1800641d00c804020581c006500f050b156980d200065400744007141d00c906020300c40145604001411052078004a010258960b598560003c04403000c0da020707403036034601f468108c0d07584504440310a01c0d10382d00498000c2ea4a540700070a0b0b400b0b41006080c4004d55032078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 790224163 1250 790222913 790222981
    0x809040203041a1b0901081b0a1e020105010609051e0909010905010e0703020607080c07090903030c26010504111908040c0f0605031302010e22060e01031a 68
    0x4052483c020503000204054586600d900311110419040404140240c104a000401e60003814510340c003030100000b00380403c02511624885420280e56000462a1480309080e10380300b4541f109542a0f440c40208072540c50302e400204214218413801e402074020404400709030200800e00070b011130001d0701e040c1050400a410600030b210040d03040d62107500c0c2101d04000e43d100820f2800859030018802c0382490b02e40e0320b50380e0055000c0c02e04000d10388a010710010781540c0030b02a2540d69806030310000b58041200314040c14800c092014880080010300c1c819082c032081c41a52415039030265400646118021008c90240c803c04801e50500d0449040450490382d10281c00341c420751098003610030045d074402d005410881e0b14040c84c00400ca00740300003404500c02d104507032845801403624442102d14540480d485000c03801020300b58020a407e4000340002138080c02c0c005158400d9841110f62640d2150702584030407071a03910100038190301140e5178044101754603042080384200e1070101c200c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 790225413 1250 790224163 790224173
    0x1140910051c02030402060a030e1507033c02030603120408030901030b030607050307080c360d170304060207120e041109030c010f0302041e091802130504080904020304 74
    0x3040c04041c25060b4002e00b914a035140262070145a000d0025401e181c0720307020540c090042c84110185d240b03d0a521080b4804240b1540ca00405681e240042c9100681200c8a0018440d403110740341310548402501080402c00d948810000d4a00d400503100d0f00c0e1130b07001904110049618002c106000701e004101c5600c0880144142c49090302c0400103030b41503034245616041c00b01c907560007081007440090a12405030723000a50180d0002c03d0703d460240380c030305c078140d5541c1030120f403081c2c0c07403801038000000c2488904906102c1d00226145507540039141c1d100a04403640004459450130040080f9081003c1a0141d03085654003039561848484214401400c0402c0200c005e8441d90415130031619800f01c1d901125a4010041e01900041c00084015141040d840341810105903080000041e00c400e489502d070f10f00c440746070b62100503500d17204410f015110118a40c58503c80d84141100040e544c0302101e1840000980e40030549a4450801c40303528080c1c0f80000d50000d0000080101b041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 790226663 1250 790225413 790225417
    0x2316030504030816211a01030b0d0b0a020922060f150e0a030501020a020a0605060a03110409140316020a0b0c0303070f0e03010903090e0906072106030c0e07080c090f0114091005 78
    0x8006ca480405030070540d28011000d80d0725074615641c000d4020318105c0007113444140050362006002402500c1c1039000004180c12140458020064809513041583c05801c140030304801010440c0301144d4103428400c10484030f10402a04100b030045010100c200317903e66204030401560864001c41d1140d2602c0d00207500d40044242c00c8641c1403030034002464070310307100000398240c030b81002c0d850800306035070014000100400003060301d0100680401810134070040008006000325508403030984016803040c40081b0350316400003c40010140240011a080002500d07400500e41ca4040b2a088160505442e1460124000c6030594200004003091503000005902200ca50f80b201d40010b98607611f0313258854a0580da19400689140e100020007003107856075110b0034844000c0004d003144e41c2e594600e0340070302a501100d0070034481b100700400701e6048801140c1c050300c9021000d1a01a0040009405c0c1c0043d05960381032100c01005a081c00d000701d0140c410808000d04400300000403003402811035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 790227913 1250 790226663 790226681
    0x1120b102106180807140708070504020d0f050a1a0402180f060d0c0327170a1101090b070f020f0a031803140606030d0c08041404231603050403081621 66
    0x14142001b10390b20401001a20508840c80030003e05484c900300700401019500c0800010f9209485881401440d0024884d5a00510300c00700009030541d2101a048651914451040c0c40b4078030501c03001c403410301032100603440d0100852b51920000c154500140c514001d03299000e41191070589545d0342c5540540c000321400e6008400440b4007808002401e4150004000c01400761855610b00c0c9a2100050060b00f1200302508000003145000c1d41c07085c1c01c580d4402e9007903c01c00008420700250390b40003000001c06039480d1000c3e02d040169a0003050751003044040090800060050402c16502072101c1080032710b6000818040c0b039500701d24a03569400081e101103109000e0116000f8602d405a2600055180d100341c2140c10207207002400103200442c1c0c41c00d55005515010320b500383c512910920005031021422045c0f05007020010301015003191900c0b20141131908007800003181e00110081e62004010414130998103121104030303240300d08080c55510000d1512460044e07100700b60400c41d15 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 790229163 1250 790227913 790227923
    0x2030a051c2a112814090907060f0c021206040c051f0c050a020a0b130b21090f0714032404140102040e01120b102106180807 55
    0x300c0808690100e485006248920224210b180014000940c000103185403000004140c0a2000d2107940c01c0840e0755080716040701905000c42d8280070903550320f00e036038040400599074070049103000554280d441c445400b40c4801c0c070908031600d0b00310902c00e1004002ca03e502074540241882c0c0074401e9940c40c6004d44040ba10706c3c806180c00729141c10900c1c41c4486040c101e1060041c1d80341907210903100d1000d079150580e41c50282e000c401000d03840d41c15203400144010141680d41e004510300040000106410450103000c080206020045051140c4a031550360b50041d128580c84415a141c0b0f080d08055400b1080d010780103001901c00719607039141605190039019985040d1490307805108802181201403800000d4402203404110165600c941100607140010f26040d2107aa0000c1e503442e00343e100300317940041d00b0b00b02420030031400070300e0303803c4408000d0f08000303107043c25034405050040d418980c941c1320001c22030606110668014910f42540501a000500200d0a1250450f4451481526 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 790230413 1250 790229163 790229177
    0x11190306020d1b02010b0a09150305030a080f102301031409010c1101020c0a08030612010212100e0601020c0919021c1808090409030504230a090c12050402030a051c 72
    0x3c1002c1c018001c0c50211500103000b420103030305202c1e80340e0081450f10340781c0014540300080032000490400c018103060340b43e91a0740342d00b80340880c1006885900203012604410341400100b2540201c036100b00c0140941c102200361000821004030001c0c031400703201c1d02c80180e040e414810480780640c4a40c43c409410303902e241c42e816140a2030760a0744075040c03020140b54001d00c0d845011400480107160400c100070015600d610075a0400740c00d9811a80d44160b100d04a4800e1003064210351003c0c00c006c1002d0a00c00000e40b80c00e00001c1d4469208900d03150040c0d00384000140540d00f82a40da01100314000c404644a140c01c1766a18141801c00300180081482c10021010800d207040d15950360030341c80110b50385809559014070001e000410411424804140320110342e41c001f804014805110ba1480303154103040b5078003003003003003520f030b0b4031000905140c00421a05540c0c0100c62103100c161740d8030f0204042c6c0703a41c400b00c0e00d07100c50724001502e00d0080c100c41d003149000c5080d10140d01c880603510a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 790231663 1250 790230413 790230461
    0x170d0c082b0605040b0f0a0510021e061608090c0906030f0a0303061403071203030c03090215210108030405040908041a0c1c1d04110a11120711190306020d 68
    0x1150310754031b10070140d9021000010030005445e1140c40600084060302c192800340c124882600800c81c491102e00c1c0c0f00350081c80030044240e802d89002c51034190603250410707890500035051610b0700c0b99881100c2c003580c01100000c10a0300e0030005120308000440c1200c2c4a8203560400500800c1300c0e0160048504c4140c50050861800003500410b640d0108031a048100c03a43d41d052b8020002c2000603003c0c16100c13030071400960fa444440f0300d00402c215200554400072007080e03134181401e1229005401204000500c0490030010640c0c0699105a4000a01010a0905180ca401583c0c02a07010310031100254080c102881d0180c01c1c0b4000c80b50403260400c0e9007801e040444c51801c00440002108802c00c01003040390003403040e08900300508001004400650b4012050f4071030702650011a54507003c0a0850700c1c2045021900703200701c038042c0d003000c607695901d0444010421000e44652808000004080c0ca1880d00000641c4d01541c119510051902d0000141010f181c00400c20b40220b0150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 790232913 1250 790231663 790231669
    0xb0709080c030309330f0a080f090606010c0507080706090602240402010e041b030b0a05120a020405100b0307030b010306050108070c140f03030a06170d0c082b0605040b 74
    0x1861348408004d000e100103800c0030781030b83d113000c0300700d134071102d41c840044041d0300800164401001218688107806945884070344000c0c0695201510f01082c04616400300b010200740031072102e8000d14246403480740b0030110b0070b05600c0c040050304905068054034030000750168210074580700710b94058007501e10303082d000c9030408041e0441d00c1c1200c10320400c410010300190301c01e0700d202d4a407110081000aa1404130010500c01680611004011a5031007003c00302078645100404c00504044410380340c5c0c103840d0005507483d0002e07414024095034480002c02c031110928a203410140c0340c12031031580ca0b0320b4011402800f0300b000e04a100c1c0480c3ca00540411554030402c8881d1103904180c44258004e1002e03039614000422042044006000c0d410026012001c244000c5000c0d0413002000324206051900701d000151401c1740c0b00c085a40900c1540900d035412102101e1001e401010003912804500354821b81a82c611501c50b1144400842000c103407500ca0f0f1080d425a08280d4003009a100780400f4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 790234163 1250 790232913 790232917
    0xc0a0219051f020705060a050c030c0c01081f030816021503060915090601120e070927021e0a18020a09050301060f030f0611073005030a05130b0709080c0303 69
    0x110340180c010504c180681c0c00c0c000c000b0043c102592070254548402e4414050940e0030808400d0500e400204d0500d40a6a00c02102074022502d040070b0000f0000032003004600300124800200b030540d006c611008000b10b021107102c0c003941c024041c82c0c07416060b034071010560303072084030500e10030301400011640b080b03111038260602d28000380140485861f900e0040d240c03ca80280c84040c040d89031180003080d00030501c0003500808040c0070200300c9800040e9081c0f40e181d00c0070000310702806600380c0f103409070f95540081581e417160280155024403050010a032510065042094010781400c140443c409055006160102c1c50b69104030800ba1600105070995482d88501401c540780c807a01800070070080742c1400c0c6241d03c1903400140c0705010110200360740d00320503415611a508006001400031008003540d070180341544008088055100d03001d4664003001d0040c82c4030b10342d9040013030f0341201065884403d0741c1e0003150806283c50100340041050f20b6030300408002d80100d0030781b10814100041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 790235413 1250 790234163 790234219
    0x300f010e09150105060304260403021503070e011107051503150d020a0b0f1303050703050616050d02090102010b0d06020a1106040f060b060421230d050c0a021905 71
    0x150220b40e503443e0104110840c0c0001c1e000351903010107170f50309400201d44810b60380c03401c0d40c0349580035032600d203180100262410151004205880204100b0070072a50120240c0041702007400c01c00c0d0805c1c1c5440359280307060300726002103401c1458400440e05090500010390b2140c1c0d0b900c050401201207140a201a031441d4000080d00821507030014016843c0c10406011210600141e06090901205082541e96529401a211504403100c04d00038031500b4803110b49d00001e00d541c0e44161004004000b480e922072040940d007c00d0380440c414441c1d80c400e401c1808880c02c0103000300340c0750b0103070b00f85240294000c0c0d0070000071505d0340070004000310b00403a0146c0315542004043c40c50040c1520303801c000c0c040c00e001c00741e0b100300b0400010407800c2d0990380711102004001807501c02e58a640c0b801030340360911407444100298201d042808812400107012845102c0b500d4100d441d0401c400000e442c0003814240258800d0706e280700380c101c0300c20b40c1e68024211182110707a80c4001c90041c1c15603580f412424 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 790236663 1250 790235413 790235443
    0x60a090905062409010b04081608100f02040e0f010f060c05120703090f06050c0705040204240504120501090b1302101d060c1b030d05300f010e09 64
    0x4400501601c50010f95203c09141c1104503a0700100e4180002c3c82d101d009030400d840c0024082002e200e107410420549501c54181c21301e6012203410a404166541490f013804001d168036003400321030405c641d40641d001490441102002410040320400304501e0902543c9540301c008200040ca247c0700d0824007000940050280040f400c07140c8400e91a58041d010540503ca000000025a80c5c0308009420042000c1e940d200d0701c407140400214200201a4000c5104034014002801148492010102c02c81008100d81c0000014008295814000c65129071070114120004800f03025064201d80b02e410312805103061141e4809101b000c01c40019403010750001220b4240e00c0d21140511020300c0c856168180c10b03054050b4440015006500480c0e0071156604200900044003401152911740c80c40c044003d00000303401702c540148030340520800b110650b0403502d101c1d146022094a681c003000404c6844a2051a0a004210007002c003131062007800312003040000d901742c0c5c0114004110030011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 790237913 1250 790236663 790236673
    0x1021204031514010b1b0c060901050c0f0f1b04150b0d0f112d0307030f0603020a08070f0e01050904020609120109030f0f0206040b0a110d14060a090905 67
    0x41d100d98080c502400c88540308256103d60056542c40c5500000c0e000b80380941205955403040318101d08420300c42011a0041e41c401d00c0261255500d00c7c080d41c00c56942841e100c2d4075014162203403464500b02003d614410301640c041104080c1001c0391014902c0c020b004107c00084141c0d081c0002c442c04200441b8011841907428401c05503480c005082010405401140f400704801042003161844450f00e911610b0001c1d10b03e0f041682c0d444802d841c01005820b03000b10854200103c0720710311008100000b01503031620b401d01c02d02d8035a40440003a41d0003801c02204c01d074840300401d50b110001d0180e41541754610100150b04145429032a0503500003601900384e1381c0326582404001d401ca80861640202016071100b0711034030034810300c180f2038069a035040004140d664003805142103d043e1104542000040002142d4500c04240d0441c41d500b00004140d070300301c850302c119070064240703100745142000d042c1311103d0614050b00740980350880d0302601555035800030008544044100030300356009 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 790239163 1250 790237913 790237919
    0x715020f07060c03090e070c0605060f090c09010207030b0c04141c0209040309090911040b0607030e12030903100f2703200d0201021c050708010308070201050d111801021204 76
    0x4107409800000b403017810610b0000d41c5030f590440048004a54480001c0c070000900802d20425000e8540c10000035200c01e034900c4c140f0b0020804010000b000b25401020018201174140d108218400017580c00600c2d0145a003030807040d400362507101b841503824205e115846403200349031000c0d000e06c03884440081a2000101642030003000c80000700b040c2d00740300030558009000c40c402d000300c0d00c0d03051003115107403a007098641c100002c4400304890603010b201c1c1400300c500040d070086200c60346048101e0301e403500d900c4600c01c2d4903d54400c1c210900d805000b4403a8000f1100e403160820b080300d40807141c00380000344443c07150550400c0761903808202c4440441c491004607028580741142003500200341100071129040369450240898403000040c0e5000640c04501440030b400c0e164a0300002505020600344060010043c00041c000500b0854000412100f10383c020012a2440c41110b0703014040045030b01c5940e446600521004203604500d2109029a0342c80442c03601c00c01121500f005092500b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 790240413 1250 790239163 790239167
    0x80916230312041e090606050c0709230405100207301709071a070b063c18190e1009020126010617011d06030c040903020715020f0706 59
    0xc10205513070498100450214041c809070151a0160a1341d0f110580d8800c24101c01618100303040d4800700440345030484102e462082d00203110b0b520007140001004c581c545040c014203015a0048c1e83d80c24500c00650142000501c9540c51200240f1003c01c04100907a03001080c035080003c45a0000078026100d00c0f90321003001c0d0301c21901319210400700c50f0029120b00c6100b084041c8081403074000704c3d0201d64042046100340304941c0c03090082c0ca002c040040c01040d818050340392004a8601c01d81000000e120340b1019100380d2500d40d0000702161015605e401d018200d100c000d0310030400300400d219203890b2400140c020b0091964022004020a04030b0900d00c400401601e01c0032030411507180d10076006c0110030380b904a2812209020000654074180024210116031000d001c8189461710040060f100d0403164050722210300c0040003007035660b460000341032150b00881281d00621304040041410b6000600c8419134642401c4540c1c90813031a041030340c0e10300980700c031441958098501403060318 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 790241663 1250 790240413 790240439
    0xd080414073209010320030c0a05060322080a08070c0308040605090f0303012d080a02060f160303090b07030204030c030213090c2408040b0708091623031204 69
    0x541806842410202d50000042e03000c071081c2e0040d01c20918030302c00b980411000e9450b0401d4014224010118404c00402280c208201840369a10071000400043e4030081e1000726404800c050b0803908841c0a520307e820a420340007003c000001440034400a000706001c2c400f41c0c4080340e01130b120301c0031543e5603903148005004010f0039484640a039400100710020300304003440c06400701e0700c4000301030030080c000d0880d260320100b40400c00c2000680e040102000c0803402d075007050b406840080d560014681202810700c0b440d50150b45891540e11403038207060740760303009240b4240f0428194002d03440c0c501c030403001d80c0510700010b48040060101000185094140e1809038964003001148195581d11079480115040e4000744040c50405030b209400900e4810000c0c08c803500b07040140c0c00d07042c1a198482e05103002402032051040781c0020941901c010081e03100c960b0207442450f41c1003915003900d00074840d0200201d03d1280d0324200740d8015031501107030252080b46840b00e0b05040c01c1c50061001028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 790242913 1250 790241663 790241729
    0x110d050c04090e07030b1b040b0c0a290f1005060c0a02031c0212130605180a06020106030308010b090d080d27050609010c0e01030902120d08041407 65
    0x551400c000005202c9403900030243c604030408068400c03e80b071400d0505134040b0040000d6116a281e000400e00f03451007005440c2640c0003181055100c085c20485186030540254000e013082602850003801da103245d100d608a54000050405800e403a001d580c0345030080203568190b228120038506202a04201c0302601400d200c2804860081c902c80c1c01103804e105d00c2c00c40c080680c815020030001c802d901046003035a2940700d100880d2130302c24a180d013060030082c1400354100b08900069070354880c1004002c000d00a640c010402d0440664444003c1e00030421480200c0102d0690704c00010040151000d407501c518000d0880c41e06000c81e6664030310381e5842000c461110a5481241d40c1c28040402803d007102c46250501451039160b80c14414944040284200907a80c1012900d22225a1140038089040c3c020300700855071040910001e61250014030400310755200707400c01c4c520000d41c400761b80c03405030380200c082908402a04123059210083c1d4041e04402084d60340310400503100310354142c811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 790244163 1250 790242913 790242931
    0xa020c06070602030601080106050f18180a06090b0a05030319090312020601060e10020a080a02010f2a0206091b150d090c050301060608010e15060f130504110d05 71
    0x44420400600d054100031070580303140d5404402c2050558000015a0141480d400c05600f02404031020100d0351040c9641c0c3c6406a00903501c080c40d580358090460302580c01103c00e04000c0c41c00e90b05040c0140324034460705a54909010481d445414030000c80825240082d000c1c600c0c000d8008a00038402070361403000e0041001110000010070050900322509c1c2c1e500d079028089079490000d00410754424110b032140b00d00c0c811082d1038403c54001a850003d1503100c1001520f43c035192074281d00401141c0301c0b00e801d50b03060901c8114122000b001c0c08a021100d0110702e81c07081070fa69812691103108444402c119407010710307a100c000952001c001c0030044c00500c0300110760541c1450b01e65030f42280c070350f42001e0317500c4020000c204203e80303040c0ca014080950080240318640803000701119018030540140c0f00301d407404212100d040b80034a03241c2240c0580115640c80d6540e01054030381d4800300710b11060f89510100812a071901e03003e609210700100c000c3c581042d04118501000780780280c4a1aa = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 790245413 1250 790244163 790244173
    0x90e0703050a03081b0f0901030b1c11030f0304060203040b030433051f090e0f010903090326090415033c081c140a020318060412050a02 60
    0x24010840c00011903c070340d50f010072030f0510013190044c0340001d00e210500c0e00020702622140d540792005507106400d00741390105101d146840400d4100300404503151071942c0d8202414280401d291440300081c0054003140d4041600300011520f0b4003075030251030010307082000100700301880350b0b0140da00580685000941403200182d4100605440115694544589181205080200d04c00c190748400307010b00700c511001c1d4107c100e802c081203601520160f10b55601c11039002000410990b2400313001900200401050350030003407d00400b074481291040200245002d6520340345000c05440d2060012050078031031032100700005060740b0f06047d01c3e0002c100034000302140b41144403804014038611002d0600c815204110900401c03403612a002d80e42011091000480b08012500c1060f03445003601c2446c05400108809040b5102605a44004e4002400b20300442039004500990112a8181d0000189903c03240c4809040b50090202902c0e81d101c00c0f000c50040c4000d009107226881520 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 790246663 1250 790245413 790245419
    0x80301170f100b03010e210708090a0603060e09010b1833030705030a021e031006060e040506120706030203100f03140111160f020d0b150405010f0e01090e07 69
    0x80ca0b1003403038840c0d009100c0d02d9030801c0c1e0503400d0030302c1912281500400500540e100030062014004082031800041580000d41401404005c205840c130710340d0010420308003150b0710107008028002600a061039602248041015001c0501c500022824050700c40f407414030340c0c20400308042100804000c0104188040030241120580a1103440020512071807001c0c6074034800d046c603048403500100d020f94069030350500583c1e101f0303040e107a80c03075424040c050b6041210303000f00b4101a420752040d00c41c6030400c07001040d42c03900004516915002545e0030061503844d402004190940844c1c000d095400140003404850311070340085500c0f0104644003a095650740e40001e1010905900640d142c44800070407102c0c0c10360038014608461513203400b1504140d00a007030003a800c20350b6500200b0104c1829030401c1151119a2641c040030340082d01e40286250901c5590950295940100e214500d05800411561502468941039408400070f41e812603082050310402002c1c5c81c94100042d101d104400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 790247913 1250 790246663 790246693
    0xe13030813050a0c18060b1803070510020105071412190209030f0601030c06080603062d040b1602010c0507020d050a0212070914070e22060b0a0e0d08030117 69
    0xe10710a80702d1051307040410320b004428002e0848a580740d90760503081c81002c00c00c080c405010390b44c0e940850300210109145075000245085003c0d48825040030a881200312820b4040d8000c5215084d2900d0b04120300c104500100c00303901c50224111803101d810000318840d00007442c00a86c20011841006182c0354910002a02d00200444541032644c020001402009201c10b41c2030b0041c1101d0524000e80d00780f07000060b4442c4001412005194a4402d0b0310400e40d55110005003404034000c10b800312410a41001d82c10b00c1d20448000310181aa101c00e41d02e010b105105941402446907111401c216041e820031000c0e41c42144161074500c9112102c1c0301590f200013022000c2c0611200810840340303002d510b00117952100d3b01c0c90009090820800019a8028002c105200412654080400050a403a00740c200b4071009100244d41303031400110f07211009030004d20342c00a080d1a4400b2880b130b690104600811136600060680e8002c1c00100188100b400121041800c8d100c156010a0a81c00c05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 790249163 1250 790247913 790247923
    0x8281b0f021504080f0601030c060c2609032a010c0203030909010e07120902030c04050a14091015050f04021317070f0509091506040906020c0105060405010e1303081305 74
    0x101070300c100c0006002c100031001000346017440d01065010700090340c556260b011268016104101c00e0054140701c01c0c0070040c4014080350340148803c2408281060307084540a50340003203084a00a1241c0c1d10260345a505031a00a11010b206440f041003805c10000115580200c00300d0032030305880709000c1001c4030396400011902a040c1114078442c1854009402803092402512038142540f0b486080c4001d84c6010070750039081c0d02c0540e0041042e0b181d0750004c0f4000c2000d0411015200443c0e02408a002808150403035544503c2d0401e00a100e22448201c0c103601152046681c4000d0881440c40e150820350050710300380d0461021400120350f41c116160240e02840c007100d44642002009000702c0c03180040c040301400d800e48007a10f203441c0c08a1060360704c1404070901e040c01000c0d1800100b542d40c1d0380d040f400780294040c03002c1d13403a407416558a9001e41002e40f1202d04ca180cd101c0041906c100c6042c4961140300344c10f44042c0b031444c0c41d44082d40e22041c0a021104d100c00c082040780045102048 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 790250413 1250 790249163 790249189
    0xb072d110c0312030a06170607180504140f0a14060d1707030309060f0506011b060e1009060f0c051204050102040b1908011e1e1208281b0f02 62
    0x43d40e40d54a2500034140c00448010350082d40d80082c0c80c80d00c044c40848001440f6034405001d00b0603030305644050640c2100041d0380e07848641e1150a000184180907500401c0707038004c1e05a070556044680b528141030081d40d480c005090321008400000850b40d29203441d0480071540034881142c15400d14004000031341c1d1080c43c0640100e034444600004001c418402e0b82ca01501c0da050030407550801c000000c00c0d1401c42a2101c5903807480c11480e0043c024103501004002110104a81c5442601145400900051316080e10010310f4550b90410380348090103440301044040d500ca6140c00340071303d46a0665040948160b44942d824000803588030601001800016548a90840c40480c2210010f00c2c1801c142c01c00d490120424088020104100303206000340c07440960a0b0303401d4141c10f800c0c0c0030210050f41c0b09080303210b000782c201d2051048e840c00400c13081c003074030710011740e84852004101241d00030043d400c00040c1486007038500b0b1194400b04903a205110300d01d0b40307450681a4000807a0344c03070410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 790251663 1250 790250413 790250443
    0x60604030605240d0f15060e0a0c02070e06060a0c03120606110d1d0609010c0204020a08060117010e01060809012d0f060302090c031801090b072d110c03 67
    0xb8400040c9481c550002c854055800c541e8820340301001d6a1782c4800c0010508001c001249081c0c00021101c4150480006091804a80d03009440c203403d210740900403c00512000d070254003004280c100748005a58030a070707400b92800d494002070060443c1d400c6070080c426400c00c00000750b210031984245c01841c0052410382e03103403042d151580c0402424041c3d031410712410301265081510544103500740c540c110110869085440e11f00c0b003001030754040d4026030b000350b0141c400903401d0076164020100500610007aa21190401c210410742c0c3d86e20b00c020301078002c44008441c01005228130500c1403e80c007000c4500042070010b031024000405d0340e50181b5403a000c00c4442c20507082c5403c03501c98124030540c074a100b40030452031034000c680245000b40c10b5140c3e0307041c0000012502000c50107520b0050401c00020080e005850030a816104015124070300000e02081107039040351100740c44051418101255030708450110720041d184041390f5040300302103000e1110082a1590180074040d0400d90ba2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 790252913 1250 790251663 790251691
    0x201050714060c2701080103030e04020d02160c12030c0209070903080c0109031202040b0f0a0e150a0233061c1505010f0803120a0f0612021305060315060604030605 72
    0x44001a60596000c08491003141380c5442a5210b6a8400380117030459801d82840c00b503814503680810041e10440f0490300710680009050300c030030a084504211401e01070840611718a4454803800d40c001200d100c060005000c2c018410094641070100c1d0760400c000b814580c1455075203503200c800c9500300d4903c546241e5550211642416000703a036441001a200b602149042d0a000084480b03000b1640c1401c0702140c08036030940da00c0d0207180c1054a5242c000e02087c65074038589800c4900c1c1d400645010014060740f555100c000900d07840b400d0000380190082d668034001d4162100840d8001894150300994420082c240d00004c1066810110f004130703042c00ca04007802040c0c400792807040c1e1004c5c1c001c6144001c104000705000c425180c1d1910783d031038410410f8580a5446010708035001440302164640708000a1200302524480c254500c01e848a000c080110306070b080440380c04644a80d095005580548003030b100e20b0749050b500100c010111800c2075120b858000444400300d50807903019140c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 790254163 1250 790252913 790252927
    0xc031203060f0b0f0d0e06010f0f090b1804030c1b052b03110703020604090c0201150b0417012306120102070c0b07060e011b090f080304030201050714060c 68
    0xc0360041c140a0502d40d455074075401e140090894181c40b41041c0501c000030003190640004243d5040300c9852a454400c64046513103500c10448040351070b200d4160101042000010283c1c03040c041d01e8000100105109624501242c0c8e0b00341c0150300820071400c02c601d0034000340c00a22080103903921003240c4514280410b01f00400c2c403d000b00c9135450841c5000c129030100b615621b540401d540f078140d041c0380c1120f0000c00d82545915000054000940c4401e0105000c07884000503070000c1420300f0980d00034084040c2c0948568280d411600034540c8805003080f0902c61241c0b441005481c0c1d42204000190004420a54100301109010465040100001031203002d103000300b21466031102c0c90008502d0281307940e40340314003041544184400312a000c00c040c810f2040c540d000815140e189002441229000e000c0f00003c0c00020a041010030103400001c505000c01416030000d6070310f904019032030710b815078005407407540280b803085a0f924801000c008040c0418852103000c1d558074406580c540388 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 790255413 1250 790254163 790254167
    0x402160c0f060212090d0c0b04030f12030b01020c010f020a151b11030403020f18070e09070c03120510080708030903011b020c1201330e0c180a030c0312 67
    0x141c10350000d400c40d80005080600548180c01312204250700326219025000075140010b04c003907c42c2d03c4040700c803d02240010a0240130103640310014441c001503c0c1240385d072141030341103603540801d56005901030f000720060703035000d298211416010f034011280c1004440e1340710014016000e241e10481c0f92a203ca8140710415800c4200c420341150501042070000c1c803072501d81c0e90182388006841a4006030075142a5202d5510702c1d45190002c141c0c001c42440c2110300944142c003000b00300c3d40103400040000c0d4001e8402c112490700359515507514500950b2101c015005480054140f445500e5000000144118104036420082040f100907584071100c4208041c05c551106501034000c2880303441c242500d50b40450100c914000869400c4e24842e08034008600414004032560204600c0501c10202000c100c400f01c1c0511041541c9200c56030384450442c03d101106a40c600d0b0507440c140220509008406006040020081c10100c9003594076241c0400f0b40000e41d1080e143c206d501c40d500c1c5c1c1425 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 790256663 1250 790255413 790255439
    0x604030819030b0114130b0309010c1d030703030528170f1e071e0908061e0f040809030d12140601090501050d0f0c020c19050603150402160c 62
    0x1a060300b000c0041440b8040041c1400000c01480c100c000400215084c03e13031080350030b05000d403030281011030f26460315060143c000d054640c00800855002da0405202142101ca16808058080c010700209890751790107840c80d81000c440314460300d01c00018450503030b000311034100089002c2c3c0d440c81d1044012905980b8400c5000d07284207960412413040140684040c06c0d50039101c0c44410350301030a580c0310101202d401e007903003110f0601f4040c2d654200c0318541d44440c2a02c2554102010385100c0c0d124081210003004200a0302e0452505410000704420880400c0c02d0340103015002080c5412810390009080403030f500002e5000c81c8100c6191880d0032842c0c4600302c51000c0b0381d8501816810f01d100080c00d540100c1c801c241c1001000161500200b60075003020701c1d001d1a0300c40c00d009440109901070340328641c401c01640500820038a1209449060040d0001c03140081c10031031854940515991038442c0410899421a40800c0b130341c00015503104010784940d01441c01c2800700d504111900f10b0388 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 790257913 1250 790256663 790256707
    0x31201061e0c0807020f041103011809020906040c0c1505011517010509130f0605160203030f1906180917090303030a09050c06030108011a0d050303060904030e06040308 74
    0x250007410748a00c40e060308441804240740d008900c0b59165a107510005482d1404d000390140c00508240f00607400d043e5031405141070340e4010414440b001003e01201003220102107010354020740400c0860700da424241d1281e0840f0a4a01d0000c24059040e00c902c43081d680104400790010b0781d0341d00100020340e014a102c0c2482d06061410412040028852007031840c0180160b0b03200360f2070b82e0042110120725920250099a11110150060801c0d041c002d00400048903480000031602500c240451320100841344035803c8003040a440d92500c107103c4500381c0e41440c10b1a4516522040031400c004614641500540c03007103404030381c120f000d2401c10550103964841c0c038124002800441c49541e0301200341c1c0d52011040100281075003840c1003251500e07081c00907041d0060000030010402082c1034000280a007903a004801c9400320a40c18800341c1c4021210190540d0014400f181580c50080411034005007e407910b06405001400020700386e5005600c112881c81f00000c0108850400d21441400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 790259163 1250 790257913 790257947
    0x141b01050408030d0e0f0a08040816050a06030e031b1b041a090603030d0213060318120c03020a06230c0f300406091e170706060803120106 61
    0x1d242c60840810740c1e030701488420b9039000392a00003851100004000d958000f41d418411204503800130b0501c552140e1040c0155002405031b0b003400b01c041e0741c2031505001120740160500b07000c64a814002c07001841d00114104050100300403160540114220f04581074036103c029049419807041a6125410112026070066051034009032a0310f51160b039000c060031003990098030075550080000e013103105402c40c5164140c40401c041224003100c1903000243c8465403030800c42c0c400b54440100442d00a214018030300c4050640102070103105d201d07030052442c800d0040b1903191525036240303030560340094060890a20451a00d02d40c21541c1d00d1f9a50f00181610107113441c0100c12404450300e44286420040d91a80b4025141400042025034141580414191680c00d003014078010000e4484410151112603042055018040c4542100e0130a640d028182c4985449002c4403a440c94020150645665544000015003900c0070710042100e12851030300c1403115810034601070b008050040c50944 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 790260413 1250 790259163 790259167
    0x9050613150c05101805010c08090d020109050a171314032a0f12060c1b240a0906020409050f091b0607080c101a0f0a0306020304020a03141b0105 64
    0x3c01c2001c2511303420041303104004100564031041e00b901014003990020010b41c0fa244011103410b5004030014001e040c1e14060b1442c40d505c000080707098130710f80c00e005800f80c0c022842c90000200000c00e1070b1184812840c002c0e00340100e501070701076070a005600030000c014031178080200500c1c0c00c0c0b00c0c49141303007440c500190300c030104207103000b814079102c0c2451401000ca41510113400d6603404001103401041000701c40031482c09072a0b03442c082d00400710508448090b180340c2c440b071980200c1d00d406544c00303c50b05d02c0380d42810b03080d15401000e400781007844503613540d044403000f103841d900050029100c006000f0902d030a01003d00401108020144101c540049245130309410064002072044841101c01c2500e6400e141400e800c5031049a41050044c49500c1545a6005c0c040c1c00c0800340c03442c41d0200b0451410742074144a0350005c9100c1465100c0038540080c400219658007542c2c00c10b0015051800c4a62203550b6003040c000c640c03615014aa0020300c5640b41e00c4d02a01d0620004a802e2030003c3c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 790261663 1250 790260413 790260437
    0x6090b0109152403110c0a020a050402120a09060f141005030705011e120e160b0c0a200319050708010204051e04110a0c030314010b190905061315 64
    0x92440d0503103004407101c003440f60300c07202e403118804d800040e00615000c01c0c45980d6020703003002070b50f03603000300c40124003440a02c0e900203680c0c42c00f482070300c03070081c202d515240700c564840860100030004c0a204803602c0e9550622080c00d2003991007041b603054052001020b09050443c000d001101943d403006100c1d5000b04420f0007030b070f640150341d040907003054a00c8001030540c003082035907020040c06040051a1038402551441403000821444010f40d83d02d014141c65110320703c4070842c1c4160303004120543d006982e0715001651666412500d03031074145500801c028a000064204008000d038541114103668001c0700b405018884200140380c3d06c002145042e00d08004030303c004100c188200140032810f0754603104e94031260011529441900071035070341c0c1c44050704043d101c6020b0a07402c1d0002850805028030090f01042028142c42d01c10182c0c03400d182c441c0a5a25a00c21802a200104001c0035400540781c2c44140c050081078030800340f1408014102400075528800f005c13201c00410071540654 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 790262913 1250 790261663 790261679
    0x1403041a0901050717072004180222020c010e030c070f0e06011b020405190f0e0a080a090b1801030e01050f04140f060c07020102120f0f09040906090b010915 69
    0x2d412260f405601d403007424100400f1041c850088031b030041e0001140411b1a0038086403041c60088010085804100c240240c1c41512102e40c03c458009400441420885440240c5400c1070b000391000c003040036150189920020b825600c0800020b0801d9102050891164a0500000300a8411188081540c61503c103180e0710480014019a0505c42c520344101040054182d02014080d0042d105209500300340e81c4059103242c90310010b43c4168504401e0303521103c01c074081d40e0400e030315080052040300802d44034500b031540140756840c141300b04071800107071144411000c4e24002507480210120401c1c20f100140903503e6590040701d640c2d1404c8108124103509a10040d00940c1040d03100c20001500e20f006403805480740030442c4144120410498641c0030f8600a1040c030b03100781d09072400d40d17462a18000345800b460850f110f43c084248145185031070301e5000741404110041c00400e1511035500d03200b003162203855041d1452171040005009c0a01c0c2c60085618140d071a0040b098070317601d00009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 790264163 1250 790262913 790262917
    0x60607051902013207110d0f021314010b03070903051f0609060b0a0e01050d09151d0d03180804060309050105010b09010c020d06090204021209101505011b1403041a090105 75
    0x4000280c0c000418000c083c0000306e403500104042c058100b040071042c600741020302100e0010200d01c01e100c0ba03203040c41c40e1621401a0040f407680c198145500f40d0030180c0030744039500018048810040a280000003040c010003005400c8148240400580c05100f00400188c80842d01308040c40d905000f010400e9148003021124100900e1820700d403000b407000012242032052a0301000e00f1414084c1420610610491403c082c801421042054024190b10020302d01742840c1c150005030040484021824003a03003150314844000741d91580c0d401140d82d101c94968020b074001ca00013a98550b500300c1005000d2181902409807201e400c0d043c403220b8000200003c84990009000e03107900c11001c405c200c61a08002e00855004100f0341d1505a4a406440030342811100c5100500c1640711100c03082c2c8483c0b1844141075a5142c0b02d00c5485e06010054407400c19040e21207107210044004140400e200d0f08e14800c01c0401c0c8400303590340340c0c68203600303002e440c00c0d050000300c0940d0208000d004507030300441 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 790265413 1250 790264163 790264247
    0xf1816030603020f0f041e020a03060e010e010b130305011d0c03060c09060c0102041a07120503040b060d03021c270b07140a080d0c0305070503060a0e06060705190201 73
    0x58111810201d0404103005e00410b881c00140903841c26008281c0d1079082e000b6080c02c0182b69020040b4030341e00c3c0e0b08580c103140284a1485208000c00043c000300c1480002001c0001d01da02d2030b00c0c0050340e20f5450301e003150080400c6100c1d07902003602d140c12810090140e95450035013103000b440281842c50fa079a400d40700391030560303114240014185200d1442034069400400c41d04100452140400c407613054142c0c4662000c417190300c21040103d652074090402c0c0ca0003241c01120101c0c0d2a07a80d4030601012100c0d403c815019031140c030f03a030030180000d0741e041d154500d01d49a8600164440c00c0d40c241103604411440d88200103081d410902c5446400003d982066070007403080801c20b04080122820041c40d9107014203460b10015924010196030303000710310851610b5078200f000f55503005048800340000d03200a07a124080c004e04110354148054501e0b00550001c0c02a0f00d40051559100c0c94002080840740382d0411003400c2c442590381200f80c400c1041c50b0094511012880b4044601400014030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 790266663 1250 790265413 790265419
    0xa05010e190b0307050d080318070e01140a0b1308060109020a02060c160803040c03030206160507020f06040f03060e071d0703150306020301090f0c02010c0c020f0f1816030603020f 79
    0x442c040c1c041d0740400002004203405065103c04082d07130b080018030341d0b0003200c0c00110440701c9020b0074070460740059482c080b1000b00c1c3d064159030b42000500100102142e4505920406004010450404007002058803281040e0400d0b407036460000e0050a051059000000892042c80020030064000c5003950344a1140000c03144e0343d481c10803503204c074083d994201910a442c04006c01c8100445504401d050300d000790210360081d40d07074100b0040f0940540071548000341048c41242c00504001c503e8142c414002040c950030643c81d1075000030b100449074007d0354042d0716421210810f500910291024001080400c03008204500030345130f0710700e40900f10004159441244460b10541000030784040c3d90302104c10b55495035565044009800ea42a43d2208140b03002c5096003494014131545000060035140c0c0883d07a8819000c1040c0394150349a49900300f0603480d040c00041e83c1b0104540c0d0b4880340242c0e510a1401c202d5940041d40d420000240103062404400f400907a5440b5080c076030b08a411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 790267913 1250 790266663 790266671
    0x82d0f040b0708070b01030813090605210c031b091f0302090a02070605040b0a050f0412030c3c0e0a030f020103090209070224010f05010e0d0503120a05010e19 70
    0xa00e081682c030b20030f8003400340250240174000f2003002a0080181113134421201c1341514161a07000590880d941032203120fa01c601186002c5001c0c0c0001006188030038040e40c1904d001003003840200e41021000c90745480001c0031561103041a24002958540105407110761020341c0001c1e1041440450207404040c2c460711240000814805c5160125a00070758860814400e0b4102442e0204600a0603070340c4d842101c0c1010001081c0d0700118014611441e04001c0e252040031b00d0450aa00500003c107400042002100280815450551491118900402c8038810601044c3d410f108001c525650391420081030340e41c11912a601c980c801d0059a802041381a4914010720059000f850706010003901701c1c8000c07003001f240380d0300030403241d00c0c91000706424208200440c00e620420344090041508004090000b40000d5101c0d01901d0b0300f0490140540c2061651510344520315002801800000040c04040014019003800344030300411100c0c40340c07440d90a00c86850502c1c00742600302c4041266907 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 790269163 1250 790267913 790267927
    0x2301030f150606050702100201020c0a02040b0d0c08030c1218101704050d08070e061e0c03041509050f090a09020415090515012a0f082d0f040b 63
    0x4009100e180c1c0d98180401071583e44000242c241d8004c00e200b0391089510b03100c0075403510b0040c000c80c0c0014444074050110200c8581c2000000c0c49411159a0040c854081100c005050700001c0000b40c40060b00071900c1d101c90342103080c030b41042c0b000080c40840c004e004480703580c80090400e481440c01102c0c104103128026000325404690000500d042e070200b18148400d01c100401d49200000f02c07030381da1150769031360302034107480c015100c610f4075400600804c50202c4a820070003a0a04240481041c1c0d40b4001c84c81c50480c3ca95001500320740c82544007d1000c92819801c040c0b424010441510407030780c9100460000f07140044020407182e41d2507241c0702c403402151740303a03808508884195280c2e01c103110f4445104c1d200410088441d9107e040070301803008947d60140d10200c13400d52100320000d20007082407203441d00000f0221821030b140107a0000200c006000c0e040034010400440500007040140c44110384c603480c28140840c0b01c20101004a001c001e0340200466040c1c403840c2e125250340f80e079 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 790270413 1250 790269163 790269173
    0x408030901150b0a17071710090e030408060603060f04150b13020901020c041107030516060c1e08071d01020f0a06060509150a051002010f091202012301030f 69
    0x54078444401500d00002c0002c9004a4018081c0c0308840480d600d40c040700903030710355198a00b81c0c02c1c0c46030404207800c0181e071810b42822040c442c3c1d020640115000c415565100700100f07036551703440c06050302d410100302070081240810066502c20000c80081c111070401842191400d00007030701c0070701314640291045000c1500381d001242d01040180c584151801c80b408140029000600e40c680140034060000d0514907090260880c0309140910aa241507182d0340d081da4141d210b5880141c1d00480c44584a0105016100d10301d2a0390054407840c0fa0031410440c12070003481111600001e0040f100c0621054940c490281c003001706951180414070114800140c4c50200c80c50041c101d580b0809051408000c5942c21410071a10b0507103c040c4c540e119501000d0805480b880d403586c000501140c2040a443c14880c240100c80890000007003030141b0139060000e86481100036a882c04581900705c82660b8240701382e150359041d0b802040c0b001c04404030065810b01c410700c0701400b804820f40740002404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 790271663 1250 790270413 790270421
    0x506070c080a3501090b09010b040605032a041410021507090b04090c0f022a0406051c0b0c041d0702030f18180103020906041a0d03021e01060e0408030901 68
    0x2604072103815121001e03410703d440e603003d0240544450908001c641c0324200310f190305c0c1c16240442d0850b0706107410302c203044030141c00040c050030300385208100c1e13100c0943c94409041c2c08143c0c69484150f0f280c0c20702c81610443c110101e5000e0080e00005144c1d28542c2d808550403c402d14040441c24080d164840110f940e840c49400c10312185000042c0003400c1c1e45030364803e40300031a2684031406640c0c1e10400503600c400a2611a04010f080040d910b05405889400300d8070800d0003d1001070b000342c030b44020900400c4103c03030850004081d802184240104041c2159101c030003004000c1c0fa040c24070a0345180c60f00c00500c4602c00c203004802054110703000b402910b58000061050729259540d072107411900c0128600c00d28092590301020301c0500b194102080c0c140c0350040c1042102d0f0715400e090000414580105540f540c00206640507940da07850b4000c00b800d4003940c02882100c1a07511600e404003400741030035055070303d454003c0003489080450168043c5d0001c0340162281c0c4c44140c0c2034050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 790272913 1250 790271663 790271717
    0x3010609020a0908011a030d11010f020705030a1205010803040e0a020705030703020601030c0f031a180d09060e0406080a0b0403030b040501240201060b0f090301020904020d090506070c080a 83
    0x5036001040012015600403903941c21110714800910005100100d01c001d0386400615141d010f8025514071818640540300698841c011000002420b498040256040b40c0205070121b40c82d400015050801c903a2140150061a014180401407949031841542d42e0b40300e5440307041c61543d0810002038044507a41e0543c1c56064009007500d6540e15103180094503850240000c03a5002904080491040c05034481e074419280c2c440c242100c541420500100342d01d00040500c54070000607402d501d80740340c4c01d02140c00d40c964540c40d200c02d2a1305019016003c40100500507008615280f020002d2000c0000c110313a00a402c515000701a807201e06040300945810440203801c142400e00004280a0050401800b012000c8a9044a04503074008900380c809500ca64079200314103010180305038003448000c000d03446004000600d858070b00c0d40810181d801001400d6416982e401d10710b0284902803022070b2344030500b460a081c024255039a007003514080c2800744c80420600300783c0320886104166200c003007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 790274163 1250 790272913 790272929
    0x51501211e0f020319080d0e0c0d1b06020f0d08131709130c140903010f0f0204030210093506090604031d0609060c01150906051005030105130b030106 66
    0x1103500c49050080c0880d0301004100c0c00391081004243c01e10707007170340c91881d9843d920644240c82e043c22103c55101a2280d074031f614009004050b000c1c5e41c0c0f551002c04604c2294441e180e0032505403449110490716041c1e60f4001415500009459a0505000309031442642420b062104954076805482400803494007070040c910040c2d81135605400c0e000d0b1010300324110b01184c50400303601035401500c00b03440b11380d10b50801051910704d05001d41e0328100301401803040082c000143c211000e204100a840b91203c0c000256a40014140f06500b071041104030b10011078103148207901d148c00c01806600c100d4503044000c5000400e81c0f030000c86420001100004500d030110f4281e4189282c1045e1201c1c000d0310308402082980d1a16401181c01440e601e0035004010000f80c14a40c1100a0106035800100c1c0050b065580c4c5610900c030007588005080604454240000c41a0502040c40b031941184802c007010300906000410050399011040743c0c1c41d501144000c80d030340c2c0502010a000d024641c004100b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 790275413 1250 790274163 790274213
    0x51005030a230f3004090e0601050105090918033108120307030207020a03080703120f2007082b050a050f040602130308040b0d140103050c06031807030f05150121 71
    0x80c94606e02d400403409103c80300103540490340da81006444038411111203a80081c42c2c40000307138050190340d800660a410305015203151003148200c1080e449402d102e400c8100300c26100c0051900410420100901910700007030614482041101c101c46c00001d044004148e00010740380215210010594000c660040c1c8d010b0b116941880c0c0640241e01401036030b00c84500d05001d1001d0481280a1158084131724081d07240c100e44000d1451280d9441a00141c1c2d402c0d0381008460401c1440010124150100c00d0b4101d01c035103680e41140090300d03009004402d0303240c10901400400d160360300d41542c1040d40600016981c1c0119111400840071079400074119140203e0000340c0040601d0040020f0b1103411801c00208084100d402c001880a000107031983d4021011401a402c03c04021034121259040c00e001000b8081030721881c02c0015081110011a00d100c0c2c041040002c0120080c001009440d504d09176040c21400400c02c07011a201c510004061a071020500c860940c04000041c070b9981700f00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 790276663 1250 790275413 790275419
    0x317090c0a14040c031e0f18051f23061906181706040b04020d120216060804110121020c0a02120619051005030a230f3004 54
    0x2d6401018440c5000303504040301c001007a482031064404409803000400c404e800d141807810014102080c40401c2c003a50751280f884411410440c02000a100e00001d040101c0c00c100c203c02c1e850309c403902e018082421300d05100d162a07800700500084502d00103000001d641c1d207600240301c0c030902071b5408801c11950340010401c45da20041000040c40c0ca81d11190541359910b903480348410080300c07092401d400450100300001c0030031042c81d400500003040301e090340340191030300308034943c141089070090f90000607030807a00204d507005100203005c1424071680302d18050711403035000034a041055040000100c410550201c1c0c0e80c9081401c4c0c1c861990454481324030321030b000e40da210103800c10303441071030400703500901c4c2d0720002003691062000719030340d094038241e81c0c42d12005481c0c05401a081a9500580891180c03001c00c0b01d40f2800c1d02482c0340b500d015220f00c001e00390071008c0030b01e00016a00a88001807500130000b441d03140100518040c0008800d11a0500010344060b10100c4035030304c0002000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 790277913 1250 790276663 790276679
    0x904060b0109080d0806130b0306010602030307031a060a3b13110d092409120905060702060717040806040b0105011806111006170c04090317090c0a 65
    0x55141802038940000443c0c58604007036690103010005000100001c0006020f803c104490304405c1200400c085014191100080c0c280f0b0b9090f0010300040e4004410000615810300078031910b0540484907400881030038022800500c130b40389070f1a080c49011740c0c0e5422000340a01c150400300d20b03021484814400d141030100100101c846559201c1c42c00e03804514101c0115108000c004030a5902c440c0c42e04c0c148000301c0d03004d8840d000040c0c802d25107900000d00c1101401001005043e0b0000000590284528003086050320400460040012030300c002d004903202d0f901250b113026012500c0703030346900a40ca043c0900107860303010500d0790714000c0b1b400241e08100066007402184103492003020b51ba2143c004550442e440844146003140503441040414004c0101d818100a454182ea036905160385040090b40c100d503000c0103400161013a54480381e402484101984130003218103101e000810740700149840403207120518101c00d21000308100d07d800b04140300c0c8190018241150081d51100a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 790279163 1250 790277913 790277921
    0x3051b0601090204090f05010e0712060308031018050609180703080f0705100e0604080c0c0d111302091e0d0506071d120a060507180905040c211709090406 68
    0x901d1001401c2503681d08806c541402982d0680d030000b20102d45658680380221340c0000b24030181c800855540364048040703102034000b9440b90b8030040700b40092524084500041c40d9081820300b20880c941014420641e980842c0d05d0b80010260480340c000410316000039090040d240e2004245400020b010305a090703046000d4694070b4061002d403071007504281e81007015206010a210402e411401c00500002c1490020781520300000013100c000300c0203030340420703d0240c901d81c080d03500d03c051910900252901503500d41c991003500340c0c103606150007040810102030b544190540744d40740154400d01e0b103886450140840c0c9400204903221814101400380a15034601110058070322003a400d031000c0e050543c41c83e48030750b85960007400030406030b0b2110030083c8806071880c1c0410040701da90001c0c034600c01d295400585181000092541030901c0c0000b000c00d1960b11007000c000c4004e506c62f9003c0d29000c8180001a0000750018035032900d01a0030340b16100742d19007598003c4e9a00140801d0000c5940 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 790280413 1250 790279163 790279169
    0x6090106030c08071a030a02120711010c0306050d080a030902090f010510080c03070f03060506040828030207030b060a120605061002280828081302060703051b0601090204 75
    0xb08101c81940c0310864152244068040c0950841400801c1e0f218054003800955101c1020310006050901075901725148110a0311f42100042c2062200603194500b03205490000c0000c0c182004024540400301c1e043e0400c800c00a45614008946020082c0c02504690005540180744100914212001d10000b030800e001c1d5500406051a515450300c0c09051250b00403601c1c02261802c6558031801120070500580c545810103468510025140e00c13208003410150800e2005020107000001400501c2c02c489141d00f294540d182800d000845d40100700b100561750030201d00d500f00d83c0ca00c40843c1c81c3e8180d40d4041d84080a1405904080c40b0182e440140901c90440d1005042152003000703d035501c012240c0b001030b007815101c070b030b03550205e444001380c40b00c0d48140400c60800641d00107107107101030f442c0c83e02c0d0300303070424035500d010702d0b542c85104154094100049252168000e4007c03072a2405145001070030701c14001108010405075014850030950401c00316140742d0707120700c00d640213904184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 790281663 1250 790280413 790280423
    0x1b0c09020a09080f070b07020906041119081f05010822030e0f0a0303080c071511070c0b0f04030305160516060318050604260d0606090801022b0e0609010603 69
    0x113038420308468000320755041111440c0000303500340281502041fa28003006042c082c2d016907222925040d054150b4042c00401c210034000300310703081c182040a803003c1d2000788407803514030b100c01444800480c46180c0c4010b59200b803034030030b00d80c2c0d41e4008040c06101c481042d078140c51907282c0da41420036078000302c0c066182e00280e0340141c90b403400c4001d1081035034040c00002c0200f81c81b180054581180d94014000460007254400c0040140354807481c21a4440d20300c0d1090303560000f400c1001d004203010380b00300802c0c408a4072807420814410320b84550046010040402200290b0308003804075000001001c03e805c1010360740d040d950b81d2882e903011042403207010b021a08003540e00c5518551304020180349034105c8050310783c554407692500400c03000e03220841445d0004c61050300c0c160b030540014180018001500140c041d040c8000075042c084580e010301a0740e801006001000c140c0b15440e41048000a40382030826441084500301914aa200c060480d01c948010012110030540104003102c3c010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 790282913 1250 790281663 790281673
    0x6040f0b032d011d090c100215040f170c03160201110d030e060105030109020a050f0126040201030b0904021c14030a020102120603030a1d0a05120a02030114071b0c09020a0908 77
    0x80c113140c5034550012140608075070801407040342181003000840560a0141c416140714000310301140c038291109890950310b05400c2c0c1c102508018150140d007564031b141d0041d1500300690002c01560f207101d0350b0004030510650b4881201164000d820b604c0109404005549154000c004001e0051014081078041c40c4908000010641011300c105030900d90060002003046080105104040001c014902d040080011000e2000d440d48111501502000c2c0604105070400740001000c3d1117aa80f49107201d4420700041c040180d407034840701c0e1078403040401c070100802040e0a080c0c080d641043c903403e4040c0400160300102c158103500030140482c4015035152141c441e0824143e5138000c00c02007102081445604200c855a030b440714150110001340742c41099a1500080b448000b12041c1803a0b4a078008280101180307020b004205084d4040c0010107003510b80b01c00000c0c441e100e514800040109006e50745000d000c090f07022500500640e030030640d0b89000300c46000b0254110352249100038020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 790284163 1250 790282913 790282949
    0xa020a0605030601020c0114390d090816030b06031c030212011406040611030d020a080a05150306060f010c0605070c1703041a07051201090203060a0506040f0b032d01 73
    0x45c450400ea10219480690700341540c14010202800b40e03000c490b4070100c003021349060600000c5084a122940c094007415105201d210081c0071140113030007044cc0f0b42c101c4032203c5076007404001d503281100d402410300c001c1a10341101290400f68040390005203d4981c14107468050b4064005050f28086460450b0052303076aa440c11001c06c5428112940c80441088108011881000c0d46da140c81c084070180ca02e8103500d10782c40800c0364445a00400802e0060040225510640c4140c82d4003441500850903004210070019880d0351009025902c07032007540f81034030502d900c1030051003111584880104283e0030550f40103491b5960f000812140c0d4409045903160250000702564080d5034008844900d0380d268034030560320b1aa0041c41d1104101050145c005500d00300000070703000b40b0890030010b0f5241800c0c4180901513982c1d400c000d0003074808100c00c0040021a80d02e10048a2104000545a072501030f2980d0640f1300c910700078246034070b40100042e00041c030001442c0c102ca149039002900400c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 790285413 1250 790284163 790284167
    0x90f0c080c03030c0606010f1107120b070c020d02012f031201060c0c05041a060a03060e090705061206120a0309140a030b060d2102070819051e0a020a0605030601020c01 74
    0x1085004d01e02d2a600706101240241d40a8100c3e5021a5583d00f0300100000c003803a695844d12140ea40510010780f4000c14690510490040d2241c103d42c0a14040247c083c0a4000c9894821915402030402c00311a400212400e0ec105801005020003030b03a0315528144054a2592500119943c400c2d0305148000040c1c02801440180300d09035103c90a003001c14640000c10000344480c40e2030440003540c8c4000032819580701001805105100d8800040f21070034540345803540e410040c52449550b0010030180010750302d5009a43c0012300355103c00313510b031f039034040070550ba0200e0755650017161060201d008201034104903003d003690005242034400e40184400c015015055100191a5030101d80115110782001140c2540b0a405215032541c0781d0103c8140c02000c5c3c8500d8561070050708000d000b407003407840500c0182842c0400300b070022091a0240c640302c4e01d4140b40540c80e00304100c00428403031a44401c2c000d10b0049900203203088000c1d651144d014003180d000f10b03540c50043c0130305100b0b0300c01c0e98 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 790286663 1250 790285413 790285417
    0x10c0e040f1e0f2012010803041802030901063303180f0302120406111501060206011205010e060c04051309051011040816060914010f030f090f0c080c0303 68
    0x11000206030b80c0b00350b4032110040020001d011030018a60b40b1807415201a8660456030640b000c6001410fa54074000c0b9421012059410f0b08a0b280380e0300100402c110015800c17000c0038041703015410050743c5e034941c2c6c40410300400e030590060700d12403484592100007205c024041500401c00741520080b1402a403011400c17191001d41c40101c07240b00158000c04a400d2000490019100e40101d501c007140802100b8000d070050351180c0c00142007945403500008080c0800840002c8444070022194100340010751034080501401d848640301e0780003c002d102007500a8201d441c0f1610644405051103010b8440541c054042d250007181c60385c00d0340c16241d145125200002d034000c005004410302803503110015002d01e29880ca6464000d000100303207408144070b4400c00b4004600c8000c0510b151980c00752000728560b0104240c0c0b181d020f0500520798000c1e61007800755409203400a04945d066141000406003500c0c00f070030680b5440444010814811995000d81e07010b141154642d20414081540d64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 790287769 1106 790286663 790286681
    0x40e0609070b090f091e250c051203070507060221071707140c0d0807020709061406090409050a03050715050432010c0e040f 55
    0x210020801d010003010000722003402c2c0380444000800b034104a1120754040e00c1e0940c006a861800054030740d40a07085c0c801c00d42120305103001c4503010045d19540c0e00340d020102c0390052000740e0060038070b00300541e03118000300300810507191140d00d6900040c1900c000c0c024144400400240d0a001615580d488100c0e46101c10030212070f03020030401c0260411040c0001892500b100788002c84d04283e004829062841084114a4010485121780c4032448014000e6900400c8101e90201e489400352805500704d4403003a0315803d440c81115060700c14118002e045010101160401e000540540781c0000c00000e8668420317200e090038003094050484c0054800203803c405c0180e100030b4448030845040c01003000c0d240554031007201d0403420444850030701b510b015229a030f21003001100034800c43c4400902980807131110103410b4010307400100748142e04007a0a6800311086108050034 = true := by decide +kernel

theorem cover : BRFrame.Cov 790107913 790287769 := by
  have h0 := BRFrame.cov_init 790107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 790107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 790107913 ≤ n) (h2 : n < 790287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
