-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0722
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:22:28.56975+00:00
-- url     : https://prove2.me/submissions/b30ab05b-a43b-434d-9927-3e1a551cb35b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 129676258 ≤ n < 129856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 129677508 1250 129676258 129676291
    0x7170903191a07080c182e2f010605090414010e01091106030709170102090a0905070f08070c050307060204081b030c010509040b041a030d032c010e06070206 69
    0x110101d01d00843d84038020562090118521003044005000e03d45660b80c1c004040103164030006041109610b00000044516000240c0d074082c03201c00303020001c10600381004400980303a000e01c442c0c02c490404407032003c202c05401f80301204c00d41040c4001c0c00090071203a080d04150030700d80742501000452080130f608040321100195014815040110740000c414501ca481030800c011040c0d00280c05c8070300700f110801c0c01081c0380c404000e0b00c80b400e810b582c000581c1e59640d203046c4100e00b1080e5200c4500140f904c41000304e6103801010b43caa01002a00d4078074110f80e9184c00c11340d04e00c1c01e0000060300c148000726040080109560080c8140c1d9249411161003e8078492286085041c01150b6901502b1021451100d940900b02800c03039400c0003071000c03a030341d0300c5040031804540080f00b4900e400b542caa8030f42030b0181401d0107070071803210161600b40700703100c0303064900581c00049403100b8500c0d034051040c0c40d410b610294459000144401c1c00d580311401c00c0715000f9990358040c0c2d51548008401030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 129678758 1250 129677508 129677543
    0x12030a0309051011070c08120a0c060f051f0b040e0103060504030c0f05060417031b0a121b0e0a080a170d1404050601080a05060a05040f08030910060e010b0717090319 73
    0x40d035134540030140d2303500d540340141c22030f07045600c0303000c14404540c1e003600d6501c01c003201c40302805002c0c40781010300c0000c01c3c00300800c1146840201294400d00070200200818000c80d1102d42d64181500c0d00f103c00410191910715023100c00da21061006080503068107200301c100716010460900030f900509031001e280701c0c0c0c8680c04400e40300039207000009580e048010000500200060001c1903c1420701350001ca44c400c2e1030703406960200305140c0c00d0018051200d500c041e00070034042c0c11601e0548904c1002400d05540710740d01c840c0e0020107403080b20000e07520303410030324002c1c1103a0411400b043d0a002110b0841201204034105035000c94060103440004a00310a00203000e0782d045412100400c00c6171200769000c401080302920565070f0b9503030518160081481c02000754002d92200c4014001c003902264141300b01d82e44c0350085514001c410004201821000050f64242504503189140f615035003852640140718402c4107582500501c9004013041245110340c609032030040c00d1003d4009000c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 129680008 1250 129678758 129678763
    0xf1206040f020306030a1202120406120509061902091507050d12110901110307061d0106090615051b0613021e0d15200c010b12030a0309051011070c08 66
    0x4c85900381c15a001030180c80115508901000351032000d40142c0f06005000700e0510001d0f0b015402070b1000c0381121003003210048440c81000d61020045016002d1170078040e020381004c2d1001d84095020700c1d00814244400c2c0d46180040100b40300440c10b20766030744100e160064640150781e41400c0400e1110103e445480840c2c040c0c122544c3e2148012841d1600c254015204410140c0f2079208600c0203002180004100f8801c000c83c00081191241140000c500c00b2401e540144e000088618103162081100c4280382c052400044201d09207551140700ba21000109034014103003900d61072052105020b280d00341c103460306910a00a0310240101c41020640e00c0c0200d80c1004c046400c0006100e41601061501c0c068018060360660701240f082035040e104104e074500407440b03009800001a449903401400d01c00c048145009503920410349007412084c035142c2c095002104145615400205c041040600072820305942c0baa004100c079181703000000c1e8168020388400c850100d2000d50124200500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 129681258 1250 129680008 129680011
    0x303060603240b0703140c061b0a1707050904060b0306040c080609070309050313030308060f040e100e07030c0b0702192102040b031f050106030e031902030f1206040f0203 75
    0x1181c41c0c2c00307940341a00140b1158801c04041d402c00040c841030142a0061100405a40451000a15032410310042301104600b0210801c80051410841e5004450b089010309550303003214613a040c0140d542201c252298864140c000d030340980741882c080b40584928016500641c2d003554100447d80041a054402031010f492190303004052100288107544a42c0180b41c1c41442007045e41d040c040510b07406500030025410840229500a04001090a01469011400000315011b004c060101c010b41c0e82c03103007800d40020300000c1e05c2d0b100d100281c0700c0800824008603805403088064a40d00c48082c1071170b410401040344908200a0080c03054122200c91409694182c0c1d0103003041080c0007481c2110801c404c0f01260010f4581122003007075034051210a52003040804000130201c0c110756044110385058000100b818038000d100206000000160348580780ca0001800c00702901e00c20680ca103000b1030464003000704002030340110380c03514460780070700401040c2c81c1842800d1001c0b1114099010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 129682508 1250 129681258 129681311
    0x801090606050f070f170f030609060904021e010e0d03110c01031515031416140a09030f0206040312090f0504060308160606080304082b08040201050f0d090303060603 73
    0x1080c840742d004260102c005482d1603120b08030920050441b004002c03402d410400718081e0302903010040003e9400d000d000070f50722003011500e40b0464603280d4002405603143d91100400010740180c06019a405454203044e5450b009101c541520b910b0301d4010111010502007281c5401445078039100f5501078041c4040040c407241c00d003040c0b20f00300b070713024009500c00b41c0d55507007010b84a8440038200c102d04a241400b504c0c081500011011001c5405061210300107440700500100f0890700300076a0340041c00d042500d13440580c1001010403800080d20501854202034128010f42c002d410b01c054000110000711500400c0352301110346e4038010002111640d1001904204080181c501616848180100c2140c0f00303050022b1001c0e02c0e00b030f8207850f40d0010307004400070764802c450500c1d0008040c240040a40d0f01c14080c202070b5280c9490003040c148003e04000d0621101050340c1c8034223111101034501400081204014100403414014050082c034841c010209181c20941c0411500b010702c0010240c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 129683758 1250 129682508 129682537
    0x307032f120a03110304030f0b0727050111011d01140a05040c090b011b03030501090f0207050c04020a110109033b120a0501020f030103172503030b060a080109060605 73
    0x8030701d850540b0904c2c650071030003295000c100000b01c00a8400480c5407413450040c48504020b242428020f801c0c01c800e04048841c200d1a0b510020071404c94141030002e0320070030b01c0d01d9002c49441402031405000c09106100d01050165860316a540f415801011080810204042d083c0c0711806484110f50701500d0242c00001511070034080c900300b07038210b001c0c40081854490080300c804250342583e98051101200025295401000744134454010008401c1c1814021031a0540a99a0507a0364601d442c2d13450245d41c0118100745001e000d07002c6d0b801d00c0b15103240244400c5025207070003801071185110074035001030600200c0b000005580084143c4910750300042440914000800003140300b4005001072912a036094800020420b001030300004440d80c2d0403035107a50443c0703811121725801d80c41500c8244010f2000380640d00c3c3e000c2040e120780d5a603458800e2840142d0600724040e050700011290031560020f04003412590010f0442d0407101422010032990343c4401b01254940301d4107003480e9400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 129685008 1250 129683758 129683773
    0x21150603090c1418011202012d1b060e0d0306050301020a0c060b010507080706020903060a140f10081207021e030303010e060409060c02030a09050a050102070504020309010e060702070e0a090803150307032f12 91
    0x82c0a0719102d1414442b06501401e012016500d44040d100c50b03414075140c5801440c080d58190346c01d0b005d540c0c0680b030214001d50420110080040121016200c003900807500d805c0d01140c07a90140f4110340035035410144190769040729042580196010095880c0244181c4000034030f07011113441f07001e0740ca8440c64607110f5642c9a03800828076000c0058207030740512407000343c0010003d4081003040d0803c0540c101c155222581401048069000300803503a2403450070058503000c60741c0200032030f41518811900c501583d161030002c00c0050028070b100520f420310f4260080d002d1034000016202403c82583c8240c41181c4039000d01440b070220b80700d49405603016040600c8203151640196502c502030000002d040a0614405485c0032410341d00b107805038003c45000d000600c894952603921982805040c4200385540cae0f110390070351000400389880510100c260000555040c4009402960440b03400301301900d4108102d4011020107481c43c80c50f00d42100c001c4000e04000d024100c48260130707001352001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 129686258 1250 129685008 129685097
    0x60901030b180f10061409010303090e101d010e0907050603270a0c082104060311090901031b051503130321150603090c141801120201 59
    0xa6180810b5603440c60064510f83d41c484070040101c14510014040d0215855141c0069604061800c0e000c0c80d01464a00e001480800e4020111408580c42100c2c180b01c907a440312108180da500d48c0d000800300d020106c88010307001101201c540c0c141c80c0048091400c0d070301c1d0710711019139440551141c039070406001d000041c1c035106140c4180c1248100803030407403034126241c1407031811704483307107011500718090701d000307000c4031404120042c900b02e00000e51030340840800c085010603000d81d00c540002c0503200d081d000c0c010f119241c1650450309020303240369a0b958480c07400c3c507100c40c91422001020070404800250301d142039420150250b01200c109440c680b40d0b669400e1503403030200825024480702c0d85441020b0400a0300451800907100400101c1a82c64041510021110791200d010113017820600c1d408600680202400c58a9420900c0030340414040404e42d107040100c00c60f1080300e4400b00000320508410000419140700340d1707034501c0043c280100c83c14905403061400c8003a4151094250782c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 129687508 1250 129686258 129686281
    0x40c0c020f010c050102070c031a150609121b040e070b071401150605070b070c08030a05190204060908070b25030201090209040f0501050705190e12030708070b060901030b 75
    0x42990043c5081030780071100d07032101c0c2e09981c0100f00448070040c1e20304081040c02290802c1d0601c1c1208510710a45030b04001400c218414242c04c001440381d507002401d0007032a551145070f40f56140045094407122601c4200e1020121102c80350140294142070310f400b0100c07000305042060351000034105060442544a1220154001140180782d41d43d031401580528410108100145925645d00d5030314013940c90462800391010301480140901103100400180445003600d42c080d581d08000609035484030001005000c103c28a18119480050041566984031614000390360348642110300c115601ca50301c030124840c940c0c000d03111840c1d4262801c08102c800000c0c41c1d005003c1d20001c075000c045500004c1e820241074a04950901c0311181000c10003800703014aa900900c2410241c1c101980c0303071240240307420b07004d00c10410006400503183c42961034005250792030300000126a260209450008007646c0b0018042d650303c0c0500700080c03800d2412001860580c4d0f445210a180c5840346a139200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 129688758 1250 129687508 129687529
    0xa1b120f2c0f0d0b01030c0803031603020d0902041b030e0303060d12020f0d030902090a050108030a05070c0f030303061701060320060d0f060512010e060f070516060218040c0c02 78
    0xa9100c6041542440b1580d02e01000050180c0140c000140c81d516600c0c010010b1405680541004d402c24010485a1250071400a44029190401503034075a201c00024006010b00c080081d401782c80c084200b003900032910300e043d04401c00c40d02c0811010003903040349941da002c111821503202d12104100b00004140081241c0c802c0200d0040b5420a0341c10180f141c280501690041c00091351881c0000961510040154220403c07100c1000654100404c0ea6102d1203011a030200380700000a80004108038041084001c0814601d942d122680360714004014001d03174880c40d05c0303208810f18140084001032084904136a484814103c4203148122003440c1c04010002030381e400036090003100031010b454040c003030000c00103000c005620b03400c1c14200b06d101200c90411040c136a14040328514503a04c00990300c0c0c2c01000055400c42207503643c10341100c652203031a00344d80901a50f60150420008550080c06404400c05201c0c906003807c10b00b484100e0304000f2426001130310825484002d4180800d589 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 129690008 1250 129688758 129688847
    0x601080c1e0607050f060a0207030905040509061807030c0806250e01140c030c01090201031107020a09090206040b0f0a02061b03070e03030c0f0a0c0b0f0409020a1b120f 74
    0x75001398203405d02c01342c1008070456906d4035981c2c00051135020175a104000c400500f00c21101080781c0e00745103806540c0c0f0040100034001e003e00c5030000fa0440202001410021507010380300d550032075103904801d03858407015901d00c00b05940310000c0807031528403600799160400072682c500ca071078040d040045448004800c012100c0f04000c200701c40012400740000c1440280020010451006600c001000c40380e440004020100c0140301007001665002a004202c484415000c44d140782c00d0b00004159101d42c0e0302083c03101000290703500c041d1402e1000307080742c1c4050f0340907a4425030b640459907104107049400b428101c90104005000c8034000c00b065171524038090100c1e8244180c0c142183e01d0034101910441084d071000b0145001c00183e1403400010b44214250359003080340405100b2100d00031409040c50042c0c0120f100b5224030311680d02140d000b01840e6040d441343e0004d042494140700c0c00c0c000b1100203041030701300281560090101e00d00c00448020030100320408072500008004000700f20 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 129691258 1250 129690008 129690013
    0x60d09020a080c010c060b041803020f0d0201152606130c120209130309030b091e01021602010c0314031602150601050301052202070302032203050c040f090606080601080c1e060705 79
    0x1003503450101e0f1860a4883c1d0010540304a0200c81603150033768160b03c0a00310780c10705000350700c0359031074500301d0040b11543d104030440d040c09140f480001e0000d501440380713280310750010004102c02015803145002c4c0104205c1000640742c40c603840701c0c51101100650407144220100320303a184030a00352441c0340d00a02d413101000d0b441e035440c400508410341d8080856403181c0000400d61541e0100c0894140c0740200861409080f4114201075242e0702c80080e041c010b0841c1c103e4103050080c001960110a18104250350340f500901d02c150f00502405e01c040103100b030f507850070035208461030002d005200c16150340781160328002c10812610144044410200e00401c10025454a5800507002d024465006142c444420404e81e841c80c00d4210451040040c4500003040400c1000c268406540000d403000f10303182c01000c02c00d1001c0c2c8220480140300910f060f00000b032550006c01d02c40e0580b0484800c1c0c6c1c000052900802c0512650580401403d21940000002c07a00e0410000c02040f4170649c203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 129692508 1250 129691258 129691271
    0xc02030a02100509010e0a14040507021513140303060109030b180604050102030601021213090203060d080d06030210211a120a05060a0603030206070c02040b060d09020a080c010c060b04 81
    0x2c5401a8000d07440300700450b001203400b01d01584c0004e02e0484000003038070b191034041d10700268441850950b050041c0203d50b0b07400801d200c01d100788046218010001d4007143d45003490319100d4840b1540307a00c20b980c01c910407aa6074116a4010003201d0252a050759122202c6045858030700c40700c20040d2200462144120034080351071410b0104030f20840c00340000607104c0c03a2281c006030500511a0121084a031708009004607140316401000c01c1c0d5040800058580e0f449501041003e0000038000d0410300d000708150400300000e4200300252442926500a10103224100780c0d80d10309074240c000103419200e1043d42c000103113580540c1e6071481d012000544040c541c0e0200f0101c050507406403140350820010740c01803040030401c03070b0307040003440c542040424038684000303480d640050004400c000c12a81c0707500940d601c80d040125100d400a04099503091000340c814010840590124020702c4810b8001605d00310100d0042c83e0079070182c46031850b6100d940d03100c100400c0705d0040340c0d41c083e54991 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 129693758 1250 129692508 129692513
    0x20a090527330a02030105091f180203070e010807020d0c0606030204060e010306050903030609150a0302130204050a080c060406080a02040905150301051015051605030d150b0f030103030c02030a 85
    0x102c902c219450103494038001c50361020340e00c00015400608203061240100f00401c02d580300c42001c203038081151801445580e6400111000c1c900c2d26900900484040e001020340300306040d40154054a215202ca4400080100040d203040364104e0301b074000758104c030840311500c9000d60700c0030904074892030b00018001d8a07a4002800c0303400b580c0001080307001039001881003103160301c6015007182040e0015415840d04c000090b80d81c0c0070003031421500900f8144800c00e81c1d00d45080003409076600a20700d800b2180034509520084d001445101c0c41603446980001b0190408105200c0382d190180005107480e007040000da441d110082d2035224100ea01300000500b40004d4480c19024102045404c0b000d04000c1003010300399607000e02890500401c03c10104500e4550142000f49292141402d03511890b0302c0045440301c061084025259000c0017441e80480710072584116102050248074440c0c464607030040c44114020100c0c12107111000300011300100b40140e50040d0039a1005040b00c0c0c4030580c55 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 129695008 1250 129693758 129693793
    0x415031e061107060914120d1e050f060f0a0b0301090c02120a0305040605150d0b09030f03090d0906020f120d0605040f150b180402070303060305060c030103020a090527 74
    0x6410130f8030180c0d03403080101c3c00c008298401c51904080c1e40300618000060405032111449654080c0b41c085594403644002c01285400e1a03064400300c070380421151800da02000130380101114030300d12501404103030200918004110000f0303101020413442c250ba0815110340014002850044150b1281629180d1030b007900800074070f5402c0c16540e022880d41030520b0710100392030002e00303e00c40700d104154030952151100f24a4002003a00208048003030348541080034158860700340750561f1004001f08000340800001404181c0c000199501d100c2555610406c0761130301007902481d42c890300030310284007800c1c01c20b00c0178120300b864940c00060090303a1180068119040400072001050b280c40360304044005100c5c0d4200200b010500591074002c0c410800010f80d05110070325071045a010441a0038188240e01c488055507001c01250310700d003049540c0c40b03002d810901c001c0744500c01103100464005c5980c01694001c0d440300004005a90111030514005509500721040c6407040c1200c00403400300c1d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 129696258 1250 129695008 129695017
    0x206190905030316090504050403020c15130e0108060a0207050307030e030726060106210f1103010b0c010e070e010605031801060b0c010b06130506030c0c1b0415031e0611 75
    0x4404668005a04c0c0ba24060050b100700e620192065107800100004031ba00400e80384100c00c4116490209980c0c3e18041c54807034011002c618101c0e00c0404004038480c40b246035054103980381c58045944655882a6030381c00c0c0c9c800e020005095030000d024101c0040e006042034090190000c0581e0310054071380180310f505071894003620340e510700031444008000c90280980c9000d800d40c1e01e0a1b0b18449100e07500045203555100c840340713040e0341c1ca0400c01a44039031940178980c0c88091078000e030f5030307565030340c400d03c0068020050b480031551030110100202d0070005270000841302c2c074154100ea140e203407002c00da030399400040c1541e424240b245811a0890020311405005d4005010360310b4541c04030340401402c41d455003a4580c041d140c20003c0385010b10b000c4101e003046600c129016552540ca1281c044818042e5413590781d40c030301c0380119a020280c1545d8030112001019141007050003044854241d01d60180d01c00541b5850900608007400281b90f0308070500180130310008941010900d400d0320640d8403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 129697508 1250 129696258 129696271
    0x3060b0f0301170d02060c0f040f030c0e0109021804020309011503060501060e01021506150c010f0914010b090f0a020c160501081f050d0c0503030d0914030a02061909050303 76
    0x107100600141001c140e81489540044c1a600d4482c08042d6031020003401c03541030340302c006c200c4081840380107013290081c208810750760105036924a00080c5104042c002c0e444040c15600010503138003454400d4407030842c101004183c040310402d040c48020350003c0d00848165480391541c01c0d010351070141080096218020000e529850315100074044541c082203070f8115003244075821900d081c80f07101c2941000301250062913281000d000f4814a10400f1229040342d401c0807125041c42d4400e0b808a40d0141c00342590328014801c5000c010300301e03004180525480218540803030005191340c800c142d44001107280040c603000c0444002450030fa0403952072104072103582e0302403040d075902080603a000032640701001828004020040c0d480718003409914051140c11901009001a82550000528000d002d81340d40d512000121405021800f0007501e40c083c481201b5500f8a500004584a03005140d000e003030140c444643d07400c010505020440d040da45c9441807000884c0007031004500415 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 129698758 1250 129697508 129697537
    0x403020d140c10020604110a1208030109110403020607030e13020f0c1005060306011e031202030d06050105090d020f0307080106060f1b021005070302100501230a0302150a03060b 78
    0x514089078146800c1c2901001400b5441405501c070620b50001803054016600104200102d110007020400071ba5965021542c031101d880c2c140c0302400300b046d000b98165036041c01c081c032840c4c1c0150200303003007441103200c001d400110800c42c0d840400c2c0b068024010703d000040545000c0e801000c003841c01d0b070b0024559160104400280050411010484041405060401442503143c1580042c2d10380005208a160041d01903808200c941c140407104000b4542c0109451201c16400e90000e550380c00c0300c264002094901100400c03258019800e4403601e410080400d80744140300d500b8003a401440d01d035065014440c0100c045144013081c05a0303000b40c40150785502c60011002001422600742c0d50a030b484150300c0c4521071740980c5a8044c031044915170360400565030349140c5000c82c0b030301020b04100100103282200104c1c008100c800c41e11580440700001d2000c030b071515410842d442c0c1540c40000d41c0040c000602c513070702c1c906040141020a13518180014040e9803480d00c06101c0e400708c0c001d00280c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 129700008 1250 129698758 129698783
    0x30210090f050406050d0b090f0709050106080a0e12090103110a050a090b040b04120206090904140f0601080c1507060c03201204080309010608030f04030b060108090c0402030403050403020d 83
    0xca802400120081c50200c0f42800b81900e804041814100010390292034082498006168810108912140c0417545811100015620005040140790030301a01001418000118041000902134945142503440c0034001c403001c40c1080d610341e43d00007542a8180f50700d414200c0700c81c03e0700d000a40100700d4035440d01943c454546400401c0c0320059000000003040500050044107005c800303580c2521070400389d0044000a5000050042c041c62b01102c0d48523004204001c100000d502001e00c03407800580444044050b80350105031191400d0080700c15540c400c0d10010098644448401c41d05003445541618184245d03c5440660b0b001c90034101c0820b403940c04d641c4000d1200c008056000202d070000703030706200c05140310031403501d07000d8000ba0100c04007002003071000e40294002c100400114003140d994443c4009407818a80041c801600c1403a41203000076110b50040811a203e00d2548014007440441d10702004001d40010b4000e0f41040401d01001c00141c0b250303050110030f24010203070407051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 129701258 1250 129700008 129700019
    0x10f0507020616050315040b03010203040f140a1106161a09070e07120902040f0f1b0c0f030c060f05090109050105072105040501090203010c050a08090a020a09051003021009 76
    0x41610103003d01d52801d0f0104540c0c0822035109065940100440802c1181c0c00b4505001401038040d0560059241d4800402d000803c071023002c8642c8018803501588201d5030b4000d000a480d060f2804014254135600004447ca03860824000c06a0701c500281c2202007500a480e40c08036101c0c406904d150800c10b4405104403003e081000800400c0c0b612520b081d5403078500c5c1c001b8020500f800544a403691a213402804540d05c5410a645a50307490608000c0c0d001c009040c6c2c1c02030900c500d400d8505020f29040c0e150524030030005440e5207a00206c0e880ba044d502a982113030302c8407061100b950380d030b0b0b0341c3c200002001204d030080c1030040e00c0c00000842e0940c81c5003882400c4400281070302061080302103000b289100030400884404035550800119981d982c00c0079405420003000013941540b8206017011034039009009002c40b2501c41c0c0c0c8080c807076500c41710803d540b00c07440d48010b036000481500401903e003680e00400d6010203460100c895040c0e503076011460030700c0084000408511115008c0c400e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 129702508 1250 129701258 129701263
    0x140301091b030c15050405100909050c0a080c0901080c03150d030512090c1f050c0604080c0d0e06120601020a050f01060815010f03060c0203040e0108030901080903070b01140d0203010f050702 84
    0x14020702c0314102e00b44e000c103c0c030107080b034803e91050501450b840c546c0c47d620140101d03030b000d00600592130144040c2c508850f040c480341d40680c504c3e07400320301c261002c0784120000341c0541c0c00c4503a041c0c5600696846024000310303282c1004140c40d40c0b01401030703480909078a40001481180b0f01c66120641c541c07104108018007114010540e541990021900054076510102c0c0328425038004d40307040300f0703c103415902214944375081008141d8030500051108200600d4014494a540d49003502e2481c41e64100484416070b49120003507210000340138803000c0c1c80111b012150000d20500480c3d0441d150369407030508000c9100918200e696540c10204020803052107603010115600c1410f0000c0d42c10315511030380c0030441c0d010203004603039581c0390403d160740200300b201d0291207250800800e035a0b407480f15039587d81c85189a140025029400314a82070000004c2d5000e081c0d10284d080e032241c0c02c0183d0100106141c02c0102e80c450441c0b0000d00140c1c90a120744400c00080a1010a5901d0140320191 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 129703758 1250 129702508 129702533
    0x2010203010320100503060402071410061e2102030d020105090d0e031c14040f14040c0c061a1206040b090601080d03050c0f0406020f01060e10140301091b03 69
    0x400f0001d00544080707681c0ea4901c07600004034400e0801c0c0d516903c07840c0c08100203010380d0100410710407441401607407003240050b0044040b40060001d21083da22500391030944820048045031602342d90350306202c110300f80c509410950714404004241c030141900002e01c6e01540035032040c0940d548009009400d60305010000c060140f5040c001000d40320b520100740e4030340102441001513111412881541ba1040300360b20171100b07503a507815860f2510f90046000140b01442401d0050842514401c0a42403034040c0c10448802c0d9240c082c1441560740302c24000c0c00310111101500402500a0601551802c08402032a402c0100800d2285000e242c20500d01002810040b0b403540700b18010081224001032841030b1014034500860280c50303401800065004503261100b0740d81c0c003c1004609250700240080b004070100c0024440c19503682140c10301c500c02511b0645110700208810700c004461340084065002000e000084c08044684032010756400f90743e01155042c401d10820424020200716070f1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 129705008 1250 129703758 129703793
    0x3270405010f06020c010c060609060803030f0a140105040906091e05070503010203010b09190806071101050601030b030309040e03120a0203010e010b0a02060a0c050702210d02070807051c12020102030103 89
    0x11241403d21101030f541c1c080101d0481d042002c0181050200001da07000a03006000c0f041d03080c044071b074441e041c554403508100d41540d1840d40c0d0400003500c810550007000702c80288009511101c2e400c160038840030b0180c800e0709485113078503402258006152a611140000940c0c25003201108071894290306000700c43d48040d2180c0e00600062007040c90707010868004010072910300041e0030f50f5a4842040c80065440b040050045804018020341c0000c4040c54070741451000b000203548480040d0308845120811640642c014003000980742441e41c08036103198448021207003001e00011102100d288101d40c2d28000a070040300400085546181e4903014062009116007401443c590003503440400130920094181c94001c07080c2028014011144c015401401c5440c180e1110303814006000889048000c040c490710380b000300924400f0800d4000c0d186e2a40203410b21074900810044803c1009101c0d180c1c80a40114181c0024aa00c0b00484130340d045030009600d942c90350800e0800101c0302144ca = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 129706258 1250 129705008 129705029
    0x608030f2a030706050709410a0306060602010506010504030308042004090b01051e0a03110102030c0307050d02070e04050c090403030b0a0f0503061312110327040501 73
    0x11103580c4a0300080e1220102000200c01051206610401c072400003440414442c2c007000501d0701c1882440e82010b482690161614030a0541d5480c00c0714000311082905040325400c043c6c0685000c8080031000c450348440341c07071030426101c0b0b200060055461a031040f6003266403090f0030440c1d80d070280141030b030203a0242800782c00c0a265880203814444000d0006114881803030b44103603a82c0304115034800b282ca0142040100c0809481c002103010703028020070384105e41329450301d0100181444140a40ea42c090f0100040601c0c40d41c0300004440c604114a0541c0402d00c40a5a2414108040c2043c5800790300100840d00380c207900a070034440d154120b1404407264904100c0442e20004480300300c00419500a0341a56a0307042c100c00a0600c26156a803025130070000140c8602c4413040d0000b81c49084081e18656140c11410180515522000404032460a204030f41d52902405003004c000c0120390580c0d143c491121480a030354018003045c0038102404420740920b5040c50311506002d031841820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 129707508 1250 129706258 129706267
    0x5010e220201141204060b03010608030a030203060d02090405100e070b0f030709031b0801051f030b0415050c0c0f010b01021207021f050a021203010302010e011214070207050301060803 81
    0x690203803024110920086034490100008110b9100d40020400340d68941c030280d03251418201c003000740c144191400c0e0b4000c1d05188603124103207810f104550032070b01e20f200114580207903c501034019401c0200070310b42c8002c0e0b5003a00005611140c02c0184101c2c032800c00b50100c518542e0001045a001c1c650100e016402440188020344126088a590001920860340c5079513450604880c10305998200910512038641041340701541c0c0070000c401c2d00c04640090145030364800000b20b1003805115010001c242c5054100085001e000071030341c01c28000c4815903034030b0352140309101c1510b9081e124160140f400103103950305080b00388086c5035507100365402400f8120321040000d551345003030340406050b120000717440c2e02155994270440310052641e006412402d1050000038000f40c001140550140c002e1113070740300e1800d140c601102c8c1602d505840704a6580d80c1280111219180e0310790800c603460366082c004a00101c0161080d10030880750b801804500e0500e02031609403440c80e400791509600921 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 129708758 1250 129707508 129707521
    0x9050109050a02090f0114040906021c02041508101e0308030c070c0e0402220209040e01050703200d050414062502070e180a020909060f01150507030f180e0a05010e 72
    0xb80d182d505503402c2310003003a007400c0c50520b03030b00030b104008014903012800f00000c1d240c00420f401900880d4080341d070140340d00b600c07000c081d2044d50088030301d0f0410086104061007503d40c10381c03000500343c1402c805018825100d56a00701103510550303e243e4540008510f410030407040c50780c0305000d440c041e0b400e2000c901b031030342c0880c3c41050307803480fa4031803003415900c14500e4840e6941682d00c9020028030038000100d841c40c0c120300810040d035607400040d0032b02c58140020310340280c40300508030003150800d14003a603041c0302d10018500500b0444045006200446203281d04200c03003400303080c0780f5004180704220600d06006c2001040200e105642048000300201034100040c150b0240e500968040c0d80c68001c025103062134610030000794444060420300540250000d1750610460000b0a00d20035a40c94003011070614924a1550000500800c850b000091281c002501030307803e01e0070f00485158035940d031101e1100b165084004d0310b05102081242c0f2650701c0c0101401490240d58513012401d008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 129710008 1250 129708758 129708779
    0x403020d02090711030f070506130f0b0c07141e061303031d0708060f0601030b09070516080406051e07020102060115020a150203150a08071202030109050109050a02090f01 75
    0x411001c2d100381c2c0008006030f503450140c3c0d134051820301c800055a94402c80000154259000103500b56114400c2e080042c80c8000920100c400041c0c001e518620101079554880c02030030001094507110340750601046002030304101e080d24076101d880015003d00c21510700170b002900055402e07980e00303500c240284150707074144107040410950185400724a1440f071030400c00c120b2000c0194100140300c2d0b0b0f4000114903002044085c020a00c01000101c282c41d01401107060305c2c078101a10340d0041e20840880d1549000f0700060284107046007404a020000303454540c02c03600540d006034003164000400f0300c00782c0c00c0d04001e480e0440c00c061442e4242501ca400003942d4180c14010b1692804003401001080c40c0200001e008196201c40c3d40d1340d8102c0445e1004010350815188044803d5110740001d0691420510180c03d8801010041c20414038050200801403103020302681c065688140c0c04002c50020b001d518442401540185010030040c0305000742404010301b9070740c102d4a403070014030441000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 129711258 1250 129710008 129710029
    0x150c020c22020403080c07060206090706080f07020f0d030c020d09031a06030a06090f0c050102031e250606211707141902091602070513110406170c040302 68
    0x2011400740c0c0c29120707290101e0080c4600d410262848001040710307000041c00080e07003001c2c6d42c074581c25030320705880f0501d5590f940e1855001e150080382c1600000391050716107806895000e401c41c0b046480a40c000503140d41820140c580c101e0000740ca41e40b49019170b40e01040900d00300500342c9440080302d803464403104000c1700f1140d1403440c0181c5410105030380d075038200004114190000707001c00044103140703041040020040022180b1040d2803a0002c1c040d070001c01030790041194800c10680e03414245400307881562201e40c2e04014900784404588d00388829500800c41d0340d1046030000b8100b400d10401510245c80026800a41196008000002152020f520300070400c0d15448589491191a21a0720040030204a0140b8030850b040c2011101c101c03071132158114000ea13459980398490340d9008145c411480e001002503844024204050b0034100c190140d0801070401c0054034454205048416038810341c03121000480450780103000c402c075070900780c1d04047c10100d01ea242c40d140d6404103081031380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 129712508 1250 129711258 129711289
    0x1707090e010501141e1209010603020f120309010c17040602010b041b0504030305030a06030f0302060a05090303012304020d0509030d0e010b010e04020d09020a17010608150402090a020d0603150c020c 87
    0xc5c903501c0200c40074030090981c0c059241c00041c00640c1d28107013640728000e1505200580c45000190b007041d0440c00e060800503129442e440155181c00c000a0054610908600782202d02c4085000c070711007110360303c030f02400203455198000b00d544ac83d004100016207400d40c594501c0d1410ba100c44c4100d143c0c020702101c0803a9071604100740c813607035400f81803002400c041e8070180140248030191020503a000c248507200da0f161901c20402500ca0885c416503902090180c07071501c60390030f0300801c01c0910455143c7c0d0424402003001d80340c0200c82d01000f00340c545c113030742c072030700582c40450b2028260007039000d00c0010b0300c1d10710020440d560300600001e1012950840c080d00407940042d41c00080055500140030083e0007130320500360103031740e240c1c800845c1481ca01d2111140d4a4075102161020000c1000f03921401400109c0c1402e440315020410214000380643d004203508102c88448c051042c00b60400443c0100038041015001d078a112040e00c18841950007150040b02d2810096915281d2010701c1c280c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 129713758 1250 129712508 129712537
    0x602030a0f0905030307030f17061c23070f1508070305130515060a0e090304090c020709050f06270a020924090a0f0b07030f1707090e01050114 63
    0x907925000303481d00d0003035421094050000044460625400400d00708566002e0b030f44608010002080501065009480141d4031004180d07954200d865a0081c607080180a5407442c070018000740801416004000c400d018103030004002000016007810034400204882031074800b64107000780006102403402416507090643c4e5102141c200845044994400d40e8010210f800544109107050f165117000c0314124450541c80101003a41d2030041c02080c01480a6401142018104528170014240190f0240d00b140706529001889c010203014480c0035040c00304641d070f01401c00700280240c14002601c031038186641e0010146118400b01b41c050b51250f40030b0382c0140c44c3c081c0580015003d0700c001c54400d507918405811010250383c8000184001c48003120502d090a64611031028528a00d2040c0005081e0030f01207039000c02e0050804204200c4e41c1d14008c3c1d0342c600f00440064a81d482510003500041e43c40f4824488000306550b500e001d440d00b42803500092001c032180c400300e03210b0124500c2d10071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 129715008 1250 129713758 129713777
    0x50402030f0a052514221e0e040204090809030d050703140a0206040209090708030a0201020d14010305030708090d0803011202100206060303041a09030a0515070c03080604090201022e060806010602030a 88
    0x4810103426507910000e4445018101b040703004208601c03510310b008400769440490000d0b00c4218080f000703801120545400c202e0141d49036000c11000740310340c41e07007685d102204000d10801907405010740003c08800340c484948541c22410010103851000c40c00c0b03d0180410804140b030b41e90002034840e40260304031800e00d215070320a2a0030b0b040c0b9415900c04480380c400401c420b2002c03a01034010780314120502c8001c0000004a10f480e03800340380c1c28840035141e50020001c210120b80c40e00d004020b0410017074009100d450f403a030b54a85d80395109900014503001451403034011460542030381010398903144010040c500308540001e0300c9116034800c600d49003a00034441d07109851207000382c1c0d800300f000600792199940c0030f08040391139229404960700000e0801c800101d03014025545540a550141c0e82d4130b00c81c0d0388141c240710040240503016410752241c4480e006500a5010a000b05c00d0b041c8920711201c82403040d480019240b0326000b080b038a80148005100380c0e98000700b961143e20152504103180c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 129716258 1250 129715008 129715037
    0xc02010e01021317070308091011060109050114120607030902030a050607080709090e12090f04110c0106050103020c1b01091205010213231504050402030f0a0525 71
    0x104042200321026500104a00c9070b501443c038440700403101002d40d0590041c400c00e07045a20380c01d090100030564082409204a1402c0c00c070800030a00400c0d040811030780e9810005240382c03100c268443c010641c1c480c8018443e02406135601c0403107040c140c0c2c0280c0710b5100070580c5500c80000402032002c1564407003120f001e41d602045000032082d0090240d58403820142d02c002c120f040100d600401080a613080054118918401e45400c9441c503009456002c2c101490420745074050100c0d40e0340600c4841c1c213101c0660742c83c800d81c030300c542a602e405550340591301d003d01e003540c6155100e075050600c1804070b403038003040c0401e040c10f40d030100203528001c400789000140d40c440e1803900030380e108151031800607040020541c000c1503100003c01d80300f03100b80c0d902c42101502490001c6040d80c41c0980d90300da80f00508103102071920209041c00c050341000d4949001c10101e810840c4e030031030049815800e109150400303200d41900105040d0b02c5c5440d40a452681807810910441c0c0141042660841c0001c1c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 129717508 1250 129716258 129716261
    0xe030d0206240d060207020102250302010c1505100f120c05150c0601030506090601090921020304080a030c0204060504050403050708090f130912080709140d06020a3504060c0201 78
    0xa02c40c4000d1802c0703aa1003c41c1000700080d00321420407809442490b8442000955403028054901d1008a440d44050708660045450400f025011142140801c644241c20040c80c0610340c0300b1fa10140d55103007502d141c20400e1036407200583c002c500c2c488940c40c40320b020881e546c000c0410707100240c44031246e51350354094182503441042d180700c0c00c60040500100401c440494614011980502103801c0c0d40d0301c50b89008102c820300c0c14014003041d4055271800303c0060603201400100054010341e03080560301c02000b401c00f140280c048000500b00500342c811454107119840192605a400f00114a080e41d00a00241326000d0302408800c1c0108001c4c0b11503070740b032090070152803001e45003002c04020601024050061160100d074440c0340c026000d8049480380d640b203403040c0810764464040610b464070740e80125002180e685c0d0862a40c003e5007001c1000750000705110007407551080200601455401171446c110034803400e00c1440c1c2e0000076035100311004c140741c0003138100c1c0c00000c03a815141026070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 129718758 1250 129717508 129717571
    0x30909090c04060303020703060b0405010b0910030b0915090a020c070506070f0606060903050c03010c1d0f0d051509030301121401020d050a0608010f02030c04030f1a040b070e030d0206 81
    0x168003d0401c0004001c0540c080b43d450100d0b8800c0c0800d02c4140f040204000645009000b4000c1e1020248010321003460f0551840241d800d0703a040006030403801001003080d0b036404944200d90700307004d04480704050134107003d01d603440200090210309042800b1176541d1150501c0c482e59105003008078400341844101c504001d461a400303a010814940e88000280070003190388000d994070b016100a1550384d090600071018500e285a64204001000c099002d450500020340c03550401080440016031b91107000c101041c00c1e02503c010520f0f4070840104c0e0000b0800141004466001807004228003e4180f42500503517912101c480011000c015050340240030f10f0b40e0500e1914204024003580e8407082d0300a0301652010310007400a810080310380000d030301c0191805c000c5124104400c002040c0c10240180c2c242d4400c40c00741c64101a0403011680c0b9110903102a1002d10a240030300040c1030304208210b4074580150050002c404591030069102c201c01044290341803400e10000110709403058101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 129720008 1250 129718758 129718783
    0x20909070e0a0504120302090f09090f0303010806100f0b070303050408090409200126040501060305060a060e07080105030d0f120c08062110020901030f0e0f070b0a0203090909 77
    0x101c140345000002c034405000151415503400d20a401c400212a100c0d0080342c1c6031035005442130401c03540c5d2605021600350020180d211600510055240c486c5080c00258000c2c900100103041d14208202582101c200d1548954100300c058541084001030140075201444e070181400219a51581081046071140c601c01940c40792a0081c40310401c82a076000035125240b0241c952000810a001075074038000c0c0c50a1107400342e00e2034040c48414031403103801e180d12910030300c00458250350b2aa20f0321300c3d1a03815a00883e105407a800c0a00c80400940c101e9230388040316251105180d403406001c00d846129100c21201044681801c50481601030441104a0740c45218100300040803203000411703500058509510413000008040340100c0008a030441900041010302901c90100008400940c44541c04c02d043c0f41d181e040300350070403241e032107040754040c0000050002d00803404150380c01d00c103542e08002c014550903c642c0c000c05038000140c852560094598040545684070309514212268520 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 129721258 1250 129720008 129720029
    0x70816091715090102162003011404050c060a050906090f0907020307031b12050c010b0406030c030515041509080d02070303020c0601090903020613030e09010806191802090907 77
    0x100740700e40600040d10b00b00c9051003201c401e103503110030003114241d103d031080031100aa0402171072004a00c02c209042011001c491182010070341c1d00307010031b0079161a04200e403040c020000800052000070320030b4000e000c03400c460951070100500c20182c814060140c102d801010042440b44054807021046130130f400c0020010481c601d00587c0095507688440d4003240081d0320008200c2d51b003050b00e0000c0f0a13596000c0405424160300c02000c845540280480903e41d41d20340842c0c550b2038990344141805580a00c1035260410b00b0340c141a480c00340e90303041190300007643d107040101151141c005150324940250b40419000c03080d0400c1d0704c1600880d0705910b500e0744006200030405405034010b00c1d07104625801d44d00e4aa980d0240d000403030b404d0f104042d0140c3c000c1800101a04061005000114402e04101e00c0e00504600071500f0100241c0004045a00031010b00640b05490040c2c00501400d1980901c1041d03180000d40099001504d4000e00807025075001c01c8511800f4043c000140c4545040d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 129722508 1250 129721258 129721289
    0x90b030a02032206020901020c090618042303071103240a06081b010f020a0507060516050d0f080105040e1e0c03150106080105090906070c030e06040311040b0907081609 74
    0x1030090080d030151b16034a0140c4520f03480c0013028100186031070300c2100002e01c4140044030000c1020070b01c02c0000c00c1120100303c0907001007111064000308401030541800207544031005031418441d084840705540b807003540a000b19144c1001e004c07003a201d20480c8000d5034400c685499001d903018101a400c46021800756144814000c0d14240300703101101e030241e9840c004604e100c081030740c881810700009010741e00041824407034107000318000c001450600c010b50600e00142d84a00f030611074540b0541001603159825110000c2e03100980e50b000d06011101040810720400500740c0d0b4000610310011140036618000910301401e000c01d00900c2d0000c4e058464000301c00c016a60035032030034000c880c0450010300021400d42030244095115220030401010030740c548002c10384910b908068110200100c661005109480740405040150b20550401198110340c4082005903140c030407400d40550340d800204040b01b6030000d41640c002d84090654511900401c400301c90305412a08641521004002d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 129723758 1250 129722508 129722513
    0xe0a0909060b0d02010c1e0213020a0807020727021605070e01060315060e0307150e090604020906030103030c0309030f03050a1b0302060606090a0e07050910090b030a020322 76
    0x20404801035218000400c9030100c0c0d40c04015200e804410041d00042c1d00310311050010b410741c0d00e424404000c0c0c1c000c1e924210856030004001c100761401d0000d400e500421409001c50f000480c95030008110300103020003e00304400c0c082210310740e00c2011001d090742d00f000400c07211154115078500303900e403007290143e043c20306040c0c0d40c0764040e1240030b00d107c0c1040c000052240c4640305029049420a8010080a01d00001100d1b200240b4541a40c18080c0100009850444001c8161180076980380c00078203450764800c000c0c8030180100b03e9030107280100070249a940d986000c4905480d0302d8140b4050000c40d81c2001c0760341d1100f03600f0042074104019008000e058000c0080c2c2000d01c815a5000c660301000c161000c2410405c0d2802800740c0e10220200c0c2217031420901800003c540500f011716a035a0720412031682b01d40a80746e84000c104000f4170201903040200e907000c030354001030500015a03464061030680301e10000309454031055010020800328081480146601840b0340b81c18400b038100350 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 129725008 1250 129723758 129723761
    0x14160504090216050d03110d0207140a03020d020705030604211814090c180405061c0c030b010806071209080c03030403090501030b0f0904020904030302070f0311120412060b010e0a09 80
    0x542065130780d4030981584480b010b110f8003400860114440d0b407a4200294880303000c010b0341045408603081070010f0004807200d6401c020038200c40e800ba0b070080480020030307034010303052076842d401550007a0407c0c1e04100205040c91b00040c8080e041040e42083c803ca02c40c0212120384804142030f6441006420009140640c0700300c0d428000021940300c261a1100400e0000c20f2050785107101e111060b0110b9410240341a602855002c44050b00110603400c10a4401d07120300e5400000b204d10b4041580c050041c06125914140500b04200c0100502c1c00c24060107000d50300b03603104d07441407651900c810000b0082400e003a00c0d8942c43c0503040380d850b4103051401130700042c038a01400d80001c0c90109030206924081c20310f0421160045c104442d181c071113400340329030980d000300140d00345034003041240c1c000b5944210000031b450190340c1d54008108180842401c2c480c5410507403094400510003400800c05002c41c51820302d502440004160001d940182c80301900c0c0803000f9803054003079400080c0c06125 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 129726258 1250 129725008 129725047
    0x3020127050705100e0d0c0506040306021c05060102060f090c060304150b0a1203140714030d0510030b01261906060e040309060c14060c07050d03141605040902 70
    0xc0e030980b0315164851082c080103c0c0c4130300090000840b0a903202c1c109007004403488401d18000d0450302030494607400070400039800395100311045a8001425203c030780c50800c1c030702592045094248030904041000039a1000068902400404000046100010108684491240d0180000d901d900d043d003003035071a5040c808540c01a041c2004145061307840c1c00c9880c0029540003140c101c0e00b100250b18112a0303d9150249924020410040b2801080401c40c003860340300c030076070011035a0f081c3c1e001034201a200c0c080c1100b8440b20f42000e003800043c01000e0040d064500204c3c440d4a0303d01385614080740e00c44072000440460007005007010742461030032031208541d80500c4060140395524054100c00c03070030840300503000035030b044402e11005e40305940c1c40200501503400b05180d1810000050704050307081e640c82084c1100010a0401c100c010701030807010710f00d1400c04015800e91050b02142101c00146842441c4401c1358018140500650503a00a0102020708545549490b10800d500100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 129727508 1250 129726258 129726263
    0xf0204050f09030a0f0203090a0f051516060b0f0414061c080a0f050705150f061c080c010f0e0309041103071e110312060406140607020d03020127 64
    0x4000000c1c1200441c01c4456020740b05541c019450b00c0b0903803208461309070712020003c0450104108103c0580d8420f01103c001c0d0406648051040f868442003258086402003400c0d215034060224500040004900803c85604860040f40e8a202480002c4458190703c00c1654440e180c100c40349d00484040c07130303004d1042d5029a40d80b04620040f4104006202c0307245c0005258802c208060000a03204000c00000040385050003800d0808035680c1900704250b004545d10408141e0040101020141c02241d40103141902c0821a03102c28400360f03c0c02d0842014041c05003a8001015000c0c003800354003450048101c00e07010081800d02400140c0c40b6404054114807903410820fa40840000c0c0c403080b01c0c0624810313120b440d2507540e200460a07010b24240095001e0020050f10a100c015050005003c035983c41c140704041442c1c40f10400c411074920360840c40a0300b00416454202c0e4848100300c07000942c04a4101e000d5801300e1400f04d000d080c0d1044000301a4580201d604c60716003d06250a102c90b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 129728758 1250 129727508 129727511
    0x90222090c09020702090103060b0118080120090315040804180e010b03031327060b190201050606070605091c120605220f0e01060602031305030601030308060603220f0204 75
    0x25503802c80340d0306a02480741e01951040542d401000026015400150746000c18108140801001e5000e2001d0f5021640500900e035100e0501e0b50381d203150740403240c1c01034050300d84032820044168040303035950030b110780b8886c0a9034a401c007150a020945044e90002e0040300c5248450f0b141c041c044001810b41c0700040b882e150309210b856502e61030040191a4884100c0c808455034900d003014600103520400401c4401d5031008444008255990042001a203015420300d13950741090b40d01034040f00140d000010440e403400090150700d913120401c55229682001d404603980c0c6585203180d08000050301040842c01c05540794094840c0c00840d80307084107441d80303070409c09695100107111105584c04510040640c0125074000c9640482e401000006104400080d00c0416001920308542c180d41142015900111b1071a1a50148001010140c42c0a40190060b549144e90240440101610107446400007000090782c100e038422000c501d402c51500c1404110031941003e0080100e400b000340d00a0b03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 129730008 1250 129728758 129728783
    0xb0306010e041b0215041106071b060806100311041a0d05040606210c0b07060f09050601081228110303010b030a06060c0f080a090b0c010e0601050a060207060309022209 74
    0xc3d60744205c2e486c8940e40000300c0300078070104c420801c9006e601000c0101c0380c640b2142c540d2990b0f02e600d0044500600820b03251078181d410050100010908404003a00805003880c442c20a07500941054030102c8001c60040c05105000c0801d0142d103000e6840c08207003c624100401c001d1048903004081128280c038561440c01d082400c0d0b41c101d40000a00c007400f51441c1d41410400a44968002c0c006c4030b020b000b000991816003000b150a441c42d01c00e00340e80caa40410014003004806005000300800e40da05614078043c42c01c01584141000001c4506c07550000039813001000740034202c201d9110210105490b92036840c2e5030914030507007040c5c1c0c1484640b0300e00000800c100d40102201e40e600c80c0c0046845810340110758480c072150340070a03100e05c20403d0700400040c1614500018003410540c0741c00105503001c0f424941032802c10141d1040e84919080c510402403c1d0b0045605400d841452074049a495401c3c000300e00c2035110807190014043c00100d0440903031110f58450501c4900c62125802079 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 129731258 1250 129730008 129730033
    0x30313090605191401090512060601020607030c09170a0b070201020403110607050606090a0f38060d2304110310060617061c08030a0b090f010b0306010e041b02 70
    0x40d015002d020403031031004a0611555000c0104c0300c003114030500d0710390005910340c008aa4020300c120480403042d8400c001f4003084c0d68040c06103a51204952034100101603a442c8001c00f03074882449101c655280d190380c4600b00ca03005001e03002409400121008080c101000300034000c1d40280f00c1510060b058184220242c039101c000c42d061203401600030704c00380e120102040325100c2e0203050007101d10740e0303200c2e224151242400359803441c0d01c410501e4282040c1036040c60f450129502131005246003061440e090700d954101c10784040e401c200d8400030384a804080e000450b2488030814003082c00c04001000b08000f29034148000c1c051083d402d603140f1042c46201c0500780c5989010710804665800c0200381c81ca1100305446600c100e00030145007a080c0c84d07008104030014941e209486489002003040100711143c0200d60b14500150b8941010b4980010541c2440a06000d4524495400004520503030701c01d120300e5454100c010810404444145034010954884480a0001d4001c0801e090315 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 129732508 1250 129731258 129731269
    0xd0905030703030815040b09090a020f150412030201091e0221030406030c2105091221040f0c0603060603060905040f020108040312020409050106080f10061d030313090605 75
    0x2120341c580c40300710701031701e5018100708407003041c510054103d0703a50742c0c4504190740d41d183c200b0701481170000549010174135401030000d030b140410042e50040e0300c200088039070003a01100310303401c440e6001500b0100d142e061808a000d40300414001d0004c94261200c0350450f2000039504040b45c3c422104400b00002e402400d409500d09684da040301078005100c100038907030181c4c000381c14855962904140381d400c45d01280e131900003041e5041204550b200c08000c0205000c05c00c0d43e10741e075118034402c0d09062030041110f81c0b1070004084c11681201c008042030070051071400d40f640c529400350600c0300c0c036502c9010040c02010b0510900c00024100600010189030500c68140600d420181c41c3c2e246e9075080e001075510311740240c4100c003004549030360085007034201e20150010340b910880201e010f5141420003400300c1d03805031000800b0602d80341800100e801c000c007600205c82c29804c04c0503000c1c180b01c1244541c420204542c5405000000d0006070040c0318007100ba080d200002d004209245d150010b010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 129733758 1250 129732508 129732523
    0x1803050d0302043b070c0c080303010602011112240603130506071107030b040305120103050c030706050a12050c0412050604050f0c100305060316090f050c03060d02040f020d0c020d090503 82
    0x1300360040c480c48084070340c0c000640d00c40c0c1c0130540b41031071586000e0998030216211000e40c01250950004001805020f170b0a01a0849000000c1005418105070701d90101c580c541c05032000141c102d0701a40f4440c0030b80c8900da4a441480d00625058480c9407001811041c404064070031111400f4042c00100f24900070300c10080215200c03802031218070b0850307842d8640103078007070015030a0007800d00000c0b0317039581801c6080380070354403c001130000045201c00b81440c0c45013940001c800c0c04014400c10303882c503502c40d00c00c50f00110000c0d40814580c403015801000d03440350340c01603c2003c00c0310561105008000940b540101e10a8088903250014003098584500482403520ba12401004043e00f0140c403a41003e0341100009003955024495482840401003060f400481d20581f01c10b00c40310350401074070070154800b00c0c00c041245589445d100040030005030410083c4101d980390000079580080c2d60683e203955404410030000039101400207036440344401002000500f03103a038040f8041c10081840c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 129735008 1250 129733758 129733829
    0x506040b060c1203090c0409030512010f0501080606220909051e030703051b06070c0302010c08041203020f070c030f0203060a0b180c070c090b010e03011b1803050d030204 75
    0x1040c0e804100e09543ca101d5202400350f80ca140b00b000e02c1c0701c02d00d0356103100303001c42c0a100c0d480d00d82d9160404d102e00c00850505900c50018008409400c220598200b84070541c041d408446883d80c5002810b072010314200c9422004003c06840540802e0a0020f40c0c0200c0340740d8002c1084401d0440c80b0300c0c00d02411085501444025001840401c0009016070702400c40f0013406c104003c1c102c1c0d0009155464850121040e200040d01e030002c0340e05064081c802d0100d0007803103181403d01c5140603180d05681c0b04103003060b1010980c5c0060310400450480059843c41030380b0101002071079079a0b0800069040039680c06038401d00404012074446160ba00c1018074040c000380c20f0515030400403603801e0303012100602202100c1c2c0d00b000410b000801d000d02034000f0f861201000140c456600300014850380c910342041e0300a80c900a200c1259101d02d001d03d0084207003074600180411416280b802c507800c010740c40101184260075080c04040e816401500a4507007001164503110000020380030300c0c61804018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 129736258 1250 129735008 129735013
    0x5090307030c020d1401050420030a0201180506070507090c05030411060304060b0402030a0e01060f05061b010207080c0c01030b181801020f0d0b0f0a180b030c0d03030506040b060c 79
    0x500c00080d0003600c030000d0960004008554904254a6000082600c16120b40059554074100b000f007000480c480351001808240807076124410101290f59804c01410103418070084810301414a0004001e010291001030005901c0c1e201a01e042e0b41e90301300328084c201483e8100003201c80070520070b0054a00c41c41e0850017207125842e05406001503a407000e4030980d001602ca10100010b5182d50000714081d01c428100000d07041c0c1f50b8440e007821503403290403d00013180070500c10009650b4000698170071410031b11001002c0f4802802090091151501c010501440450088003444020500c651008000e072800e100c2181024104410714000020340e007002045d40c3c0c0441c01480c100ca905a4860341000001840c10580b204074080603000075008030031007034407000d0440c41428140c049a0b40700200341c0e51400c18074200703501a2074464103000030400b803659592003c00f40c0d907010403084074543c901410001402d0603504009000d0101220014060350400c10480c100381000380440e8800c4140801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 129737508 1250 129736258 129736267
    0x3060f0f0703020a031b0e040609050c09130b19150203040501200a080414040b030d090e04110901090c0e010c0305032206020f1209010506091b12010902041701050903 73
    0x2070507802034000c0701d620000c00d5514000c410300185207440c44034900c20244c88012205e1108020401541c459801c2014480d0034a4180103074011502c041c2d90300c2e660200e5150816019201035000180ba00383c4201e98004160078035440400d03819150780040e1210503446c40400c18017602c0070b0b40c0d64070441c4502800030b2000d10b0540e40c020741c0c91aa99040f00d8600066480020881d11042c082c0c4d0415000402010700c060310340c20161600740304164801e01c00b580038000702c000414001e44288840d01c9441041c9034034900150400c40d200340d441c0c180d85401451003d107943c6503a5100010004041e0100c007040e1000d168030401e60250b900e50340301030313895603603640b4540e54032003031402d038158040d00c14280c1441b100303140000800500244c040f421151440544031440098030109100001c0c0c4401c05992404060000c40d4485a40c040d0740859018642c00501c44000080c14184c4906045444035401040022846100680060089426501100c050120313220915401c85a094966150a510400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 129738758 1250 129737508 129737521
    0x70812070f0303020d0e1c170a090201021c050307090b1c0f060306140406061a0301050603071101140117030c07090f02040f0306020405011d130b2103030603060f0f 72
    0x45071121014868507015090801001d000410b03140b008489000300c2c0c0060b440d03810b0f0300149425000740e44440c1d14100150154402d0811401d0b20040c000103421a2a0310181c0305590007041803290007040c521007182c13100c0782c554000700759810a441d84400608045e00000e02e20024805550500303201d078032204111b034400d180c00030060081880f1184a01e0b1564030000200d4150720030b1421442d5807010003091460f0500c3c1442c01c0b04c17aa50030044c280e541030300a030141d040500b0140d90641e031007a54800c0d0303207441c2d030902581c880980000c110020760814031510130364003020324258100c490041615085210030b007001c0d80c40e03010b140340b420301e0b960007100100315820703040d0010b40d03010001d0180145006e448000811481e017440c0c00135540507800260800043d64886550107005103140e000060010340d03840000c2c0c1e4003451034400011700743c40e00c40d10f0b0000d55135070306200d0524109180c0305004c140b61045c07480d00c9800c12a80d9520a0041c103000822440071003180520926014608002c3c079510756 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 129740008 1250 129738758 129738773
    0x6010e010305040507050312071208090304060e0301020403061113080f030702011b0f0507140301231503010e0f0c04020301050d030f02030f13170a03090504020c0a061b0207081207 79
    0x20000d5401c0d102e805c000090a4500f4404d100030000e1280d480d41d904c0c80c45041c800340058141c014842040b054104200100702c002c0140e4068401c3c030300e0044114064600000d000e4020f98001400d41c0e40741190344098446000c004202900908a613808031503030700e040d00d035203440c11501300346c2941e001084540300540c8122110b40c034503100e010f100f1098000e142c440580700610321008031a658018202404107d0f621034105450300340482c024403146c4440301100d61000c00030b0541c45600d1040c0c2000c0ba05942141c2800701c400e5078042c0082250040f51480d1594544246c1100d6040f4012268040010309050080320706031003002c4c002070000045a0f80403260034501905003011404184082420180c00c90000c160088507400507120342401c120300c0c200c00b0355041c43e48075519444540b403c80001c7e08050341d442154400c07940162588000c05880d4100100008000d14a900c1d2640003405490045400750319812268212a0001c0d1540100d03a070300d18900340001103d52041c4040700005815 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 129741258 1250 129740008 129740011
    0x1140103020c030c0303040c0f051f0c170d060b070203070b0708070c0602010c110115050105030702010f0501030812060604031e080408010e0a02040e010b090118140c0711060306010e010305 83
    0x6140051a1401400d41603003907401856813403a5642000040c4014025603501800240071800d20340740e1110325000000e000a600890b665004240d410b00d141b280c0c3c0e000c0c1c1da80b80303407854001d0801c070004070300803501940b507a10042d007011400c0d00c0c0640120301003203c00140c548107603004e0024070b229424400025010b4000d25003ca660800c02c0020b50009000980790b800204815000844d03884a072070006041010003548162482e07141003003600511904200e14001c4400c20f0030aa680c9440d21141280903009840310b40c01c406061100000402010100500e0002405850000d568555104200042c8503d2002800094640b40310001044403441c05181c1c16115000b0340d071074565100302003400c1d00c11281840040ba089004e0b40c00030b50625015103010354a076034008001b90070281c00021480103041c040d044810b0080e01140c01452002d074060001c80c055100e20200034640881c4400841d4000c0000310b9607141c941042103034038200720054034000d210503143c410703c16907004011401000c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 129742508 1250 129741258 129741299
    0xf03090109031104091a01090c03050601230c0d0e03011109090f131a15040507090e04061112180601030f0803040f06050a020703020c0f06030c0f0904020406030906050a110301 77
    0x55030000000051079014031110000388080f10130b111585400c01080c1150500c4d2790410500d0300700700401074a6071307000d868140d410103000700303545500749441d030000e00e680101d11200602d07218102d2080c04c0c503a04019007480d145c0c0220000e1002c464801501819401085561600308020401141210600c6058568406604080c0310b6140c0e43c9519540441e00714a017034220072032140824008280b01c0c1000c08030300b045050301c0a01103400c099800600c08900d0348110340c000d0426901090030050304d600f0a071201d80a207040c16403030f822032050041e00f404098400e400c0300418102c50091400012500314103c0360844107402e81c1010701d845440d46640300800071602200070640b0100000d0a0b4491075004d98a0a1001a20396039030b0301d0040d181040c4070000f14814107228030300b4030362943c5040840f07901042242c046a01ca0585800f20b4110780110041036500c280041008103815600d0340c800e00c45613004100500060711030300d1204040b14010780355034200d40002c20042c0000004219481030b910b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 129743758 1250 129742508 129742511
    0xf0e030102040f080c0d080a0f020a02060408160f081e010209040606021b04020702030c0114070501051518061f020708060c0403060e030f03040605040c0305150103050f03090109031104 81
    0x40140000d0032039010760003003008461900f0042c0a007841c1000070040d1020f0541e0043da200c840d60300c5040e9240030f440040010402c080314005059403007481070700e6899038041c15064965464404094950304410031b400c0e50103010010001d291000101c3c80000c0700c40c1031000e8600c20410441c101c00201020a41c0f11641d2b408010040c0291503521542000300819806401142582e4542c0300b07004a022003494895030060180d0800b503a800b1990b400081c20034240200e41110041420b4018060948050101c0d40b8010030803190342c00e03051020030380d9a0120340416000750b03514020300003000c01342c82598000e286800a40f140905a901040403582c035401141c200c10381d030314106032a00034122003241440e240807408000b0410355001d500107051049020f5030800e40800c88002250200610242c1929155404141440341c05022840519002000d4442e030710107011450000740e000f03200465951082c0c3c1985001c00c1d1001c801d40d0341e2510141e40300014949151207241308070003c08181781d44607 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 129745008 1250 129743758 129743777
    0x8060906040b07230309010501050306010605181306080d080609060108070e2809020c07060c0803070305040c0308071202100e031204060f090f12020105010608060d03030603121805030c0604060f 85
    0x15842d84020b10720404040b0000305007581800207043c20032030180d0100c0b0501000b40203d0041c200c550e01401444141602c107000201000c603219000b401c1290b10030b4186003e000c0103a0161a0700c2400c00303104400550b003050301615220011100b511007115110b001480220030500c145c41c002d20031f240480704481d0242071000140c07004c1400d1402d2540300904003540000d00c803010b51810700101c1c005008a0074201180f403010385840703d0500c402004a001c059072417000600b0000002e05c22000380d17400070003c540b51718961801c2c0502c450313804040005486100a800d001c03002a01450035404504000b075030500e000d182c201c124095000d0310131590561a082240c1c0c2a40c03003481800d04490040039004403403c0d29040c1404003580d030600240c111790402c40148400354000690300d070061000d54032542c5c0442581021401020945c0009100c1c5581320f60f0349248036403000003660f0b60050b40c00124071480c5c1e41c804040e03845018a1a650300044144270411a403400b4101e8000d0003841c90404c071480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 129746258 1250 129745008 129745067
    0x506150408070f120314030a0207061a01180807090902030127030908190f020117010e1f030b0423030403050307030909020304051209180f0108060906040b07 69
    0x6604180c001d0501940094410051481e01400100003840b0030704851810448986000f0031024643c101c0c49046940003010620300380465044403851600100d0811a1451140c41c0d0b4540d60700c2c1c035036403500003100b0a25040041c108000c2007030882e000c80004048440c58111044080c0004101c103991555a641d0750960300039000c2881201c1d1401d80e8041c025081c844e00d03000e8040c42c0550031600342d9a01c400e210141450800c02401c0c0c5658000c42d840010084601c0100c40b200317143c2801c00c03109811035000080c02600d02c0015405640c8c0101d6031495100501c422400c040054403020b2b1040e081b010104021071074503e12a41c0081d11050802545400f602002d8035640c0320384c0c021076260780001802001c0c994410751400c003502c9804401c1d480e5003401d8440666880c1c429607503000d0750b000055040d0103079a5143d201e03006400303903519590851030024190010032400744075580c2c00e40a01000100714071408541c2c03600c6107601407859036041d290841c00301c602403101005184803148000c1c1c080407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 129747508 1250 129746258 129746299
    0x32407090b070b04050d020a030e01080c0d0e0c03010c0203090d06020c0a02060301120318050108191d01060305010501080304061d01030603020409121103090d03110a02040213140118090506 83
    0x1005401050341654134281880d2151406400380036071811074002c800440000381d8003050014240000f441c16103001c2e19092040007031032041416003042c1501c1c0000b40003101c00f001c00d00c2c1d260389904038000c12202c84060410790f1079100350f5800d103a000c82007072100000180b8680c050510348052804a03941c1003115808104640d2080c1c000e40e009a155414136410180e024a600310002100c03919400341e280f802001038040d08000d41168100103414104250021140d400500510049031400381c1421285000500a024600041e182e80d400c18001262002c000412581141c81030768620341c0c480001d58288404c80b100102c103a0416458034000009a039a034000c1040141c0104407803210303080e007400060a201000d8505604a400500100002d42d80b45a2603550440e09070828560b034180f0010130038209a80002e009510510108801c0c1850312031120303040a56482c5641300e0340c0031080d0001500d070712000c001c0c01c070b00700f001c650b500b84541901134011680185000d040301c124515020328a06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 129748758 1250 129747508 129747517
    0x60601180915030b07120b031504030503151e0102070f050109061202070503181201050411040b030114040501050415020403020d0f050a020a03050606010f03020906090108041406010602011a032407090b 88
    0x3c0004246c0521005410031038411107040e08811001880403008440c0b0345001070704001c0c4054280640400016a4405c0f01c00084255400060410b551145070941d86021040c03034418090051107605004a43e11a840b05010309940058540c031030607d1900100300c401c420403065541e40540c0034002a000500100b002d851200c000108400000004400780901c200c100c1d80e140445a0500c01403002040c146807a000321110140e07004a181502e01d40480e01503c44440c448010070018000c02c000d01c8810340c0720350f01480c4180c100c05140d45901700340c2001d134041d50201960100c50035008500051602c086166407503c00c005070340c5100e5427a000200d841c8860303841907840f500801c0400c2419a03005000f9480b10106090440c2417603040d02c0410040d004201c05a81808409804107040c07201070081914001d00a00c12107005686820000b03000e00320a035100e001c0020810074813941454045601119281c000600e016240b4240306100310301d00c2e001d0305481c14080245008901600c07080000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 129750008 1250 129748758 129748771
    0x21020307080f180103020a0f08090c0d060e07060f0f210203100504050a0213090b150307020705040b090402130f1107050c0310020301050604060e220509060601180915030b 75
    0xd9120b8400700849183c1481400000b0b0400d4070400811080c1c0c0d41201d1510700542017464041d0041c2d44100886107842e05002415900c901d500c0c3e181003c1250542115803a4040c410903603021540c0c1360400c1d25490a45020800400c4d02d0b900e500c0c4c01c852040c6000c1030600e148507442c002209901c4002c0040f640140c0707442c0c0400080a0090000b82001c0c054a40c0194030305008626000e142000d164901800303004c0e549020307482b00b0200505d0390b03652640440300c600c0d542c2c0040c0e0368209040d011356900c000b44100c034003403401c01c82c03110494076000c50070358419074010381904484180d142030503000342140c8940e10000c40c0c2e12002002c00050710300181c20400d00c80c0000300b00d17020003601054a44140c503129490b440e40100018031403a10790800769000c644207400d10884a01d085d1000550340410f0f4100c40b914524011811900741c03010350440c5019620602c1502c0c0036840d8800119041c111031480c13a4000c2c800403408200d0f909099010f00c111182c051203200400c0c2d1290703120300c04444150b919 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 129751258 1250 129750008 129750037
    0xb10050918070609050d080d0603021809010f0b01080a0c0201150b1314012c040f05011404152903090610060e030a030804080c010507050301090b04092102030708 71
    0x460850404002d84070190609082c0941218a03010008950001000004103101000b0400ca80784641c560054030246038024541e2580d40384404040cbd4019008441104440d800e01c59000c035188a14444c0807003e60040c0e685030744998038601020090034502405d0411503603580d03641a00c0d500506d9080014002c07412115070381d000e24655011404c00b894020101c004100a06403240380c1e04848207858400c5945080351140081da8407865914010390b0302a41c1003420076070483c00daa601c0d54400c50507140c4000d1007411102c00ca10a000807034100030701c40c0e140100c1060050041d500d5036110350801035606507031714919480d0149503540c2600300b41c1d06240164000007d100301841113101c0300d40500503a00d03000f901c030712105000035074429a800d809800c0c0000c3c500841c080c4007640701114001282c0e00300900c81810030178002480ca80c0240704003c0d1442c9481c1003200e0b146407c1c06001005034105050701d00400d4400c070b1b000704d007460075000703901035200400903440001c8030003020b000c00d24800b140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 129752508 1250 129751258 129751291
    0x40c050a0e0307120f1407030c060305090105040201090302041e0906020403020f060f03010b030a060b13060e0d050307150e190b0105090108190201030b0a08060a0f05090303040b100509 81
    0x90281402080600301e030701c03a40000702d05003c2c10245141d5000020f0300708889401e002407505220070080b4144805404500030310202109001070301c0c00000444015580c100110b030b90320008507080341c0d416500203000900a00c0100b0151606400070342c0900380120b8001d2250b21036800c0300c0200c0310410812501650040780800a5245c08801c114215030140c03a42c0e0b29115008580c01201d2005004411480c8000300100e2003d408581c0000080d010309070000d640e034445420040140f80d42ca200f008002030b50301e82c1803000383c10324000b0303801e20543c4240110300303000090b6102e07582d95000416504005680c1c0d010864549001c010401d160f55055a070220821101c0c101000e070010140c00460061039030a004010760b5074005481c0394210910003981216203950310048014145070000c481d40a034038180f001c1100c0b400403070081c0c0101c909031000c01c00c82c107110000e0015580d00f02e649104540060000401048403181219031280500e0300d005036664030f0740c000030a07a0b24240e0380d414801d846900b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 129753758 1250 129752508 129752527
    0x415030203060a090506040f030c0c06050c01050108071505090301140f090724030c0903020a06050a0306080c010e090c120a06051207050a0b07080d0509030702150a2a02040c05 77
    0x7180e641c011039040004d21825096481c0d1695070003000e040100201225021041418850801c04c002d4941c80385a508c14a6900c00c40100ba40c0c00c08001010594a40000001d80c1c15000801400f11056180303102040100fa40080e2483d800541105815540f6001c03480040d400c42c094071031203a404010440d442c0d00b40350502c035141070b94a41000001c1d480940090110f01030050306da800c200c1507485c010640c7c0b2a039180c1100c4040240c0d1000b50040145603021880c55040409007503500701d56034040101a43e20840c15030313605414059180401c203604030030203103402c00705005944014100d13401d624020308000e0000c00b940d411282c05503a01d40c0c80406010302d00d40062511000b10548000340b00c0c880c1403000003400d480e220701c00c3e030900881c0001c0c0842044009000c0d0b07882101d05010800c07243c030f40b84070342c0f43e1650700c600004c91080125110b50307084280303010207490b280b1419550304080701c21852420300c81d00c100d40e18005086460001d0220045ea598001c8208110a555990340c8511703558 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 129755008 1250 129753758 129753763
    0x40f1d0d14030408040315090210050318070e010902030705130608010929091816030c050d03020309060d020c010504050a061a280f0605040602070f2d050415030203 72
    0x1840110240304206100c00310b4540800c5c0c4044d00d4000d0203203500481c8151440d0024035240d00001e420210442448800d503412a0141d881a0282c0300c64090424042e200151510b0503409111035020f580030042c410841981d0145a200c3c4513420658606500d01c420a082c1c400340741d0000000614107001441302a040d40110101702c140c000e50460a804c0c0c0720520a24525940403541c0a0541c8500185030151052849110219030740280c44101341460a003140d140d000b40070580301038640200018203420984042840d813905540554100b0948904002c890780c04105600a80d03502444981c601050a21680c0d014520400c000d0045141514248040e9220b40a49070341510260540401c9078480d8103100300c400d0300300509407100040c2090304820510035600322111a0002c2d06000c240c0e240c10800900c00e9940a400715410726544288034110205c6d90f00440250315141c000b1010b0040c00d070103250a48130346a41c1901c10315605c0c0c3c40400d0484015a425007402d60700e6040800560805 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 129756258 1250 129755008 129755027
    0x1509150f03030f030506011202040b031008190b04030c150c0e190513020d18050c040c1706010201091b1706040b0f0406021201030303020d29040f1d0d 66
    0x82180d40d480040c550340703020b0f02140c60000c0510516886200040e101d0b84289030b0500b4980e54401c0440d2034039150b400103546034004640c1c1c81c0254074014004582070400149848001d03405580940d1031021342d0b50360046001e0082e20803000e1040c210703c08000200342c0c0d6031a9010407203110000840301e120401c010030602e00c03154458041c980c55032514030310b2801115010296581510717444100014056984024440d071641080d00c50710b400c8013007403030001d241b45880035180550100e414095600080104a4144030b54032404103404004019240500c1a100346e440700e0140000580d810941d03d80c0040910a0030000b22809900b090900141c0044588010040806401031001e0f03d01562a4900c0b118050603c0f101c103120303a0002010003402d03804481c0703101680b140210712544e491030f014001e5005496141d8940e0f041880030820141602043c0b003d950102c104008040340903c28080240418a403160001c0c0d10348581e00f8011000980047c00b0140d4030b00140a10707108010001c12a070380 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 129757508 1250 129756258 129756269
    0x180a1a130905161d130b03030d0207030f080714070b060f030d030e160b0f030402032406090109090201020d080703060503060c030405060f13111c1a010b0408120706150915 75
    0xc050500d189141c4900c6200c485031745490400050001e1900002403442c01038403401c0341c6013800024840d00301a031181c0450007402494460b07102544840d8030aa03084403403c0e11301d4801e900c00344218004101d00914082d00260b02414400d040c0c0c0040c0d01190400180004c24404a910385030300c189030543c10071403100b40a1031070301e03034000c42c1e400c1201203407580c400d84008540020000c0f0214080d5a814003000f8518070074000515401e44100b50400c41e81ca40c100c0d20302e40b044046100014a10b005400781c0c0556541c141d020b06850b8003100350544071101c0c040d03c2c0004045c2c4d1f805001c40c864034200041c41c028201c501c508c0303880345094075015141c000001c1c00c25074091114001c1c8414180c40b1a107402c0941d601a0105040c0300b10003000c2210340c50340c0c001c2608010142d04a01c014424507810b42e500d1840d440349000300d1a038a44d000c901442c40780f44962015580f000520401031440c0700081c201c403621400703001c5001d4000e104a0a03425107240c0103202125070307400382a4282645400d00f0b00003800c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 129758758 1250 129757508 129757547
    0xd0e0606060a05040e0603070b070302010506210606010804140a0302010515060901082206020a05070201030c05040b090d15020a081009090b040201030f0b0301020f180a1a13090516 79
    0x22611000903c2400389100d40f003603411030031021071030950b1709002c0340d4054403c0040316502c0b4102070038000c0c040c1400341c410b103000c0d86242e8030034102e044d5003168803001100076034000e02c45505c401c4011600c40000400580300d0003440c00c03203100d14400074041d01d51514000d90004c211400c1610000c45801110404a44586020058155142d8100c8052680b028603065001c40340710b1811010040f0040c0384400030105d900c0000c05e6414a504680688480b9000380d074100502100030b03605545911550003600b40380390042c07040170100e2800c245030004040c800c000c06c60035010114003131030580c0c010002c06800300d01c000c020000c40040c0804e2800007000c070200e040c004600e0640b250940903101a10183c101a2980903904046001c0d03003043c10b03040030144c021555100e401e040b23001c0b1500660500411039180c50b89602051070b105030210240d9501c590600408a14540c12a1403548090600c0308130f031028000c0040c84400b80d00ca00c0c6c0c40780c0c542102025010030f0300d941c01880581d0755001c090440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 129760008 1250 129758758 129758767
    0xc0301050a0501050a05091906081308031602010204170d1206030803040209040828110f060112020d0b01120210020102070515061203030a1a01091202090601090b0d0e060606 76
    0x7540c610700c038002228000c2c00c00c1a61007500743d004459034441c0409144d003081c00c00c04001480941000c00100310b540a40e201007880d252640340c44501c1600c840d015100c4241030000c5070082924642050700403150b4000146040c2e43c440c0650000701c2d8440710860b550300403041410089410038ac080d2060a5050010000c071400c1d541c86155a0002800180c000c3c088840000c0411010740122004401c0c0e00c07040140e181103040003050007a501e46441c1001814044229400000010b42c0461056801020302516828600303800703040c1c04c2c0e41000780d9200345085400c00c0464051484903019240060024903524080e005210500f10092128800c5a01c100010300102e40e012900d0b0001d40c22950f402c03100c649921000520b10f40c001541c00b080da001c000305100c0b4170344a030751100380609001010072035900e00c0c407001580e200d240b511a542c440403e4a5070000186800c031116940304e101410909092b9403078140f03015291700030010400c00030361340303020702141580c0801040da444a011186107160 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 129761258 1250 129760008 129760019
    0x506010c05060115030605090a05071101060807050f0a0b120a11090927010c050c06060103060f06030207050718150b0f04030212250608010e06010c0b06040b0a140103050c0301 77
    0xa80b80140702d840e8810002c0c906000c200c2d48a600098010000106000c0190414801d814010130f801c1d1145030104140460071040703681c0600400d8110750510b00580442d9103494180011030300300821040d48244000c0c4c021a0301c04603880900303140300418108130514900300380c5041c03c842c0702192250b070761041031101e00034942c4c4880310381ea4020b464081e09208145611420390b1325040c0f000910415500306980039400581c0f0030f01419040c20028100d6160b40c4171440154122201400396000350400080c0c1440034070b010360014101c1c144503000700c628080d9200200109000c92510500800d91507551000285040d03c40304c1010703000585156141c003980d03540140e138038803070380c80000d000f00c4442080300304101c0300340100390380034002d45c8a10516104940c00e0300160b4580e402810007280240c400171480002c0c08000314030421043e111040c01e21001d80794109990030040141d94001c2d01c80d4419042600e910795042c008081c04080c890040b0b40c2c001c005004d80303000515200d5914000c1c0010000d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 129762508 1250 129761258 129761263
    0xd02070f090902010e10030b04110301080d050304080403050d170901050606031f05040606031410083f04080c040e030d0e03071a150607030815120a150506010c05 71
    0x4449400800150a4410740f006807060004000e402c0d5000300c0317441d800c43c06950980c00410140004480801c1100c079030506642c0580028001c0114652000c00360162140c000c100039600103005450041c14203541e5070300d01c0c0c908450f0700c9500c2c0005200c030010245200f04840c1403a04032040710001c0c07040d4a419408169140401012400780e44d416019000300064003850420160202900c14080d240e140da8020f00034284500b8140d13200b0003000005451060341d00003035025070b03081b8000341c1400b81d0807044604203902c404206501300011034800c10520344000c4c14806d401032420540380d4545280806040c2025994040140130751b082612500c1c4041010040f500000b0032550001841c4100c4010319166015040f0300600e4505a4a020550071100e012245e200700800c016451141701d042040c003540303014541008001c5503854002c21500900e401100703505031030241403100b1803403c1e440c21a107070151140003600e15282c1c000d149a002e001501a280d40f0910038200395124601da9650b095 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 129763758 1250 129762508 129762539
    0x30403080f04151d061810090b180a05010807020606041e050f0a0f140c1312030c0203120f090909030d1508010c02161a0d0608010c0905150714030c0f0d020d0207 71
    0x14484d2002d0314070841c03154050186c00f4054a043d0527196164105a9a000390703919602d5000f5105002030580058158800c0c407140303114000603800f8080c1c43d1140300034480a81000c421444c03100702031042d03000c0c0f080801d1140c0c0744512070780c5043d50010304141d000c0008442c0800039220f182410041114030030b10a545580307400c644054066a590340750060359150151041d003003100b042d101c02685905040d8005107225415008030252880c0711161805c0c8031040c410000801c414030428016100c0d9458178902c01c80c1c1c007000100689103403801020f0418100e4148002c5a45c0e000f204401c14003821000b4825440c1d5011117000400e490480f424410011404a1180d40e0078640462242010b42d981d0800b0f849480344200010b110040d103820201e806424102c1000c4000b0390340c418001000d2a018054083c0b81014482903850619940ca410ba002e82000811107418441001060b03561042000031600115440313026040009d07021100a0170306800c120804110741c0810003d0240400310800c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 129765008 1250 129763758 129763807
    0x3080a0c02030a0804050f06040f030807051314040b030607030e0613030e0d060e060a06030317010b0405010c05010209060c0c21030301150c050601081b03030c030403080f04151d06 79
    0x1404d9940d40d140061400b500c0f0080c4940328083c40080c4401c110110903050415072007078032500ca055a4140c82210701d40a00c90204940041c00c050401204c00d07505d459040c0601f024001080340c1d181280840d1030410155034800001c0e42e10304928515034018000140c000a103860071403e40f00240d1002031604004c211820312541040e01d511082140551001100041e560107a40c0d007450301d611403000a150b0b905c0160080340c00008900c0034001c4c28107900c2c0c140da110301521410700b0f00b4640112140c032a260403c55603590708001003001070703450380098841c48a10000030309005440c54140f18440036030003042d0540c036050002d040c1038070b0004070036241941e0318200d110b00d0b0b40d806180110340007005008060b00f14050403001180d03601022403c15004d003454040901030a034518141941c034807440c80e14041d40d40062000b4400603188000038845041720b03a00250516403034801c4401403400300704001020840c3c694894172445071049082c4031200007101c0060514840c140036190380d100c052a030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 129766258 1250 129765008 129765017
    0x406150e2407030e030a020d0803090c060f0904060e040f02130204050409060c020708070e040b07090305030d02030a060506091f11010f0b0a08030f190c12050703080a0c02030a 77
    0x54482034884007510410741c03800c0d081c268050940c1c2080509194004903040d400940340948252032414002551071000340c0c09090065420200e031101e030440d8101604544543c003a82ea22080150340310f101601c0c650030019032081d039881510040000b114925440100b8000001c402c1201040000d52101407a507010348003c0c1c1818407050480d00244182e40002d50300c00e250850b44800d0017100e601080d580300041d000c40350400c1e241c400866680045104002211030305000240024288210240d048541424451034150b10b80d91001c0c11500104200491207602101300860410a800742c200146001c0e244903251119407400b04007490b4a02d100a01d1341e281880041600603c1980d05c5c601004556008102172a020840c6c20040c2000000081c407a00c0c01840101d06d4890100c1280c042410071a20786241001010f2641f000003c520103120a20590040c08800b181e10140c01d0f0030070140702c4da41e8640d580710364680602040c0000e030070305100a1610000d82c4545400108036030881e07100f03060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 129767508 1250 129766258 129766277
    0x606100e03100917210702070b0f0c0c100503220c060509011814010806030606100c0305130608013206070206160302030c0f0c0a052205090615040615 66
    0x1020134840030021000035200c0d100046001c0d00e25003000c0340c0e0010a440c40000b0300e050b03d5504040340d4410b01402582c0b01a80104511142020030300010486142071906031120001a0300000b01051161601c48000c40c1c0000100112400029075025825059450f99a02050a85c950010f07040550040034144400040c468080c0da010700101424490a000a607040903110010b6000341e00800007464040b90482c0701050203031a001ca40a03100d0400a484200504010030b02221080c06020701070b41440801c2101c0c50a0000107100d41c0d02404540e00c840000e07500d000c01b0101c460003224001400300c0701c0c130b9040043c1103c035694021408001142c50a40700d0155000140151186025807108903450f0328000d001c00d9004400380000c00359070415150000451803a145d104c1c1742c008040c591024803604240710515081c51143c0e00e007032171201c5251444540011140840b682aa0700980c56402201002030b140c0d4640e0709131150080c25101884413600d041c490340141d09038140020700b440072a6a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 129768758 1250 129767508 129767513
    0x806060307020f06150307090603080306060307050f070602180117190e0304080d0806010503040c0302210a0f0b01060221071a0403050d050f0108100c02070510020606100e031009 78
    0x10035400c100d42004113860301810305041c2100180d4852001a019025225001602c96610310803c0c046075041548581303141d68540070001681c0c001842c60043c010140603001c3d0b1140860080c01c140c0b88506401039035000550400c0c0741c0103c000c90820b040011800c030719943c0f81e40b80725400e40c1141c1c691032000780300d200402089014000ea458051100d100118001034a880001108800c42c201c503119403113103459180044625100c202c0d40034000d508a04c8080005003011001400c0621070240400444060912003605100e8004416504012003c01c07071000d21800007141c500404142c0014018449644110300c040c1e8a15540c55000c180041005401d00c10300604418040d40341c41c079543d05c03510b030a280260442e00246881c242c130318a0a00001c02c04070244041605a4415200800c12045400680300c0a41803441020046025030000000c041e1a07400f09041484c0950300541500d01e490811b00016404011071141002260300d03c40c80180c802041c480d180115049000c644c041d141d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 129770008 1250 129768758 129768763
    0x304051f1d03190504030302071406040b1908060108060a03030e03070806010b0408070902070c032003010507020c01030e030a080f0a0608150402100f2106050307150915080606030702 80
    0x2500d6505615660001c10000080101c02800c01e083d00c80b0a00074040400041181c050156010003005644620b0341440028001b4102070641240142014036040c2c41e44c20002c00c0d600094a4072801c08008175000c801180c100c1c0d030055000000b880c100400380303003002c002050310034184005414054002e00244954905100c910064000c001c11038000c2d5945455240441d4028030401d0294040c5030002301318040c00f4021914850303048511060003d046882e50556a0445501c02603507400c01540e41900d900c080c09090f201e4400c94000e0003003500c40e60005410b581c818048140d007034004008010030745400441d9290400c0f5032050000c602c0e40d940541030010041900300000c035101d2008580040300c551500d0f40d11962083d208400501107201054074400303050190000403400c0200048416030b0079840c2c0780c5030041c0010010441e1a51180442e00300742d104d0b0442ca07203541300341b200e542c4040c2d0001111030042000040c50004055403000050000c08041c2081d1310554001007c142d04d01c0c402c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 129771258 1250 129770008 129770021
    0x90209032104140d050a03080105090c0f0a03020903030c010903030501060e01180b210103062a080708150a08010b04060b03100303030b0d0615080706050a0509060a170f0a0f020304051f 81
    0x1001c106c0d05c00e0900c42c100608103040c24401c5e0380c440c10007000043d1a03201a04180da800c21804468141040c96802040c1c02940011160a416202c148480e1020120034050040c5050103500c00103049d506008004003004ca0500c9218144021080642c800f014122a110b0441e24031003411619108601d070251107201c903070340504030000c1d102400030062010315072000d40030030100b4985074078034070207007040c820140d09a80c0c500d000301d4608800071750002e00980e0095404154600d12100c11144c00000500c0020030b6001500300380c0d943d02c80c80005007818401e020180020608a9003546029950054090100c2c04000c0405440c2e030b0003100716840d2281c03d030204542c4000700340b243c0d41c07640d44001042c3c2031a100d01840c6100702d0900092180c080ca00b00c1d00303e4125075480624100d480800d20000e40c0c000602c403020091100907040d580092240c600f0302921139a22031542d076050003400c0d94241c0f80c83d02ca641540c9481003003400006100000d03d055441031086441e5950071101d101c802c002c1c00e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 129772508 1250 129771258 129771263
    0x105070f02010c14070f060c050303130503130b040f051f0c170304150b0406080703030c080f40060309150203151306120822090209032104140d 63
    0xd0a4103540f62045000c240310701502d0f9418135a1031b042e6036651080741c0d6181d0030f8502034025002000401c1c0944107865008141c00d00590450f890142c080d1810300c00c54810b5400b692150320007245c107001004808030760400070007040b81d40009c1c44054a400c4451504205440c2c418000404a50420400442c032075000d0517590b910344d66142d1515040026008010b01d0101c03d20a20703000b0011103c0c5450320400b0291006800108402030541c0d409882e038000c85d0006075444e007401d01030788500c00c2019005001c004104040f40100c0807085c8241da0029440100c1c00c00c250451510108800d859451454100c0b402454007083c00105030411400054505031448071440c000010469841d0b0442c0740184549429182c0c080c6004801d0030480444116010f84800d40054005100c080382c0308801030326848510b006885450401c02105041c9030a0980c800a900c81d000300e640c0c40180707024440340100c00c04251044200541c0500b9071f118500c22409100ca1881340844085415120300100c4c1e40c0c10350b03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 129773758 1250 129772508 129772523
    0x8010b1c0f0504050d0c0506010b070512070c080609070803030601210906020a090816030204050712060e0f0a0c0c03050a0309060f0204090c110d0503060d052b02010204050105070f02010c 82
    0x44840708241c0c040c000480303041c0c906120380c02e21000e50350700c1071000854598110014041e1a420680014081e90000300284c840344502e294085540403084018101644910741306190989085081400c00d000180070442c41d0300581c0341040541400300450364071000910740520b55110541e1403410002c500c9085008180c642050710003045610b9008002c3c00341c254030b506e48050b503100c502547d92502e01da40f50000303004084041006042c290000d58000c00d207402c2054010341e8004c50f07201141c1d4143c0c4925000b078a0f140910966030ba504a28580200c100030091041d80d064410207081e020f040a4001c0070840c0000303101068034800e0f07100001c0c850f8420014800b40038482c090788040d4005004010f040e5240485d01800d0500504e8444040b51b1902c01074155001c00510039245ca404c0101029086603040b9200c400240040c413030010007805108400c0303402481c02d094401107001d0241481e0035a2f1041000340050b81c0c001e015601101d41c48000c08940004600c012244180746200040505 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 129775008 1250 129773758 129773771
    0x7030219081e060604061d0a090209041a0f0708190f02042601020a02070e090c060c0604030801060e0f060d1104032f0d0209060a03021225030308010b1c 67
    0x103150b00000011403405030741103d085449180405c0304446091007903a0030034400260448451007940e400c25403010031102d0004060b161a0086540e01c01f00b250100d0320484400c5182020181250200c1c1e04100180e09200c5289082d8102501c90f54014200880c3c8000710f805050703101f0759a03040114804048071083d52980d940d41050002d608000701c120001414070104409600c01c14820381380e254503280c0c01020700f07611300b1001580700039000d070110001e4011704582e03901680b141c40c0188801203965004103020329150400424040701030308004208041e06040042030f5075941304440094904903040382d5075003500b60203c0d0060a143d0304d00300c0f068501040000c14401c1c80d4200500b9030741c0103800e440490300e00040c3e2252030140445c181c2d82c024910030700751025081204540361b02981c0503009070451b41c6c0340e400140f580d8965462154050f84030703099201e014946440c61000b18410080d210201074195a0050030040c0b0500400c17072900320100742418401c01c22a4507400250100a041248 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 129776258 1250 129775008 129775033
    0x130b100c0201080f090c100e06070b250f030f290901090506091602010b03100213060801180b0307031a040b0108031602011803060f05090613050703021908 68
    0x34060703010819400004621310044031486214a10560151040d014180c0030801580f4807042044d0800c906880589a1070722920000d01308503000b00125101c41c41c00c0440d5600400f03c0d05200840310a5a210860400e46c00c031300f004506210b40d040105081c4864400c20004100a052101e20340f1141408100d100d8011a408008040140c0386042182e88403c15002500d106071074881c1c00888940014541c034182c4a118159080755100118414200310002850001c13100409680c1da0350020f81c49900742240c012040091405081980d665032400f0740803401c1070840300000d01050b4031551199400d07501809100007550703200c0f0321030141031001121100780c1070084400300c0e58103041c10000301d201c44001050768a6050000c40d0f1505a0310251300454040305956864094600e980c82d021002824a00503c4080d101c90704c0d00041d640f614400940c5010350180c000f007080f44a4807203c00c04203001043c20002c1d80d4040c1d40c0d85001d0858020050000342c860342c003220060080b5a0315000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 129777508 1250 129776258 129776267
    0x7030c05040b100903020f18090d030c0f14090d0b01060206040b070915030c02071a07120e09130201020309100c0209070f090e090109050a03021c0905090105130b10 72
    0x3503031015101000054200c200348107500d000c0043d00000315030421000c100514103201d003030481000203060041c2e4401081d0294035000001e555840c010741205240d80f01d800c0d818420403020201d00d2400c20308020010380090485440f1514005c500280002c2c00b0303820b9110103071000902e0780d0041d615121581d41e01402503c4400940e002c4402c03050784070200d44d10b2881803a0721420b40e80072061244515078202d4096000b0102c000c1d502d020350291290004141c400ba8121030507564428258585d80c048628040310074a81203e011014404001c4000499455524540c0e6001407041e01c45000c0d4101400181d286005489c1000d0388490001601c54880e544803026100f010b100740c03880745140d11100015070741814000038000018080f50b10410040546a000a030040300f90400040c40c2040c036252136041014401082c0d016a104604024180704880041050180b051800051141c00c0c000090700002c0188641441002c035a10030354000c2600380c2c448203482030000d0500814140b112006070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 129778758 1250 129777508 129777533
    0x110d050c040e07080114090f070e04090b070f02010615020307030c030e090a06050301050a140c07062007150207030e060d18060b01030b0d2d15060504050903090a030809060c0703 78
    0x28040601b5540c090701c50401c0c00c83d090140788404014051640c90041c00ca80d80a50b107050680d0058130b603544100031030165409a801242c15584000038213021b2100079007912050350040031640040d00716040e5082c0c2c0030040d1240c0310b5142c544040003020b54241100e02e60180001d46a2100c810004e01207050242c0c0c1c0103a0484009030001e111955074410080c2c100c85890103241d0f0a002450002550403110300e00414203184124000108103400d0380d010311000381c400d5414040782400042e100306200816010b06c0341014590000d500d80b1aa0340c2e801444008012107050050001081c60200811035401002c8903a1105034425000100c07030801c1c00141200c45030a0f404640b60800c0030b84523042c08100317115125041200c15403514094010783c2c3e00d82040e8040050b4407400301801c1c800154090060341c0340300204040118069060800301300881758007030080302c15a8410403808210f41c4403081c43d242120b0f007003181e841e01c88400c540070541c1442400c0200501c1d005419020041000c1d0182c8030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 129780008 1250 129778758 129778769
    0x60306070e1212040914090607050c0a0512030402090f040c0b030a0209030f0c01030f090b0f070302070b0c030f060d0f03080a0609090c0e010e01050a0902090102030909090d020c04110d050c040e070801 88
    0x80c40601c10b07166080350484000e0f1f45071450354009400141d076040c0580018030024007208220340b094001d544906091010045034180d010100009200c19880c0c070700030503a003009100382c041e803031410b160f0307100b00c1c4d410907500c281a50500c010000035a407215550540300c0d420b001605036030743d591140d048903448200c2400e03114003203807070400d00c91455219846040e02088d4010600f81c0292501d62011403c1180142040101902082a080010b03045c0302352500680750303080c08680303d05044865401042004004600840400c07900d00040b9900d62400031990b034240c28501c1c0240c0381c20810401501e45e6401c0006e1142c108400342080082e005151030444044900c2514070341d80701c95140003010000e116a0354002d00c5142c05200e607a0250340104082001401181d00c0c02c20344d440492071300d82046409100c190840303c2031710500d03234040c8650407030b1480c02ca030100501d003c500840d01090041e1094118402d0740c4000107401c24592400300c6002e801181d01ca0300480c545048010301514090041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 129781258 1250 129780008 129780011
    0xd0501080f0f1605011805180f0f070c0209040c080609070611010b3703060504020f010c0305040915030c0305010608100905060106051c050403120c08060306070e12120409 75
    0x144078030042d0100e0003103094121500d0900c903c0e480c000046a00d600301802403070807a00007810010305595000c1c1c21008031505000c200034280303041c44811052110040001a030710081c1c0041000721a40100d81e008050342c100c1d82c5c6220b6071180d081540e1090107070f401100345449090280039598100151100440d0240c1e9035012204c000182c842e4280c461400d1081d40000205003081d0344410501c40305c0000321030205c114030b10494003400c0c3d02d88010803a801a5001d0759140280410b504111805401c01002824282d0031018150340007043d5110f90300c540140c8642d2001c14115001050079880020364002c402044215201d083c620300904507413085050b58400e000061243c680240520200b540c1c00002038845686007106c160703a02d80c0040c40c0514550b02600c041c0250700c030140303d114000d5000781d40d094a0390442e0f005d24012a10051546428040b0080811000f6a0001200b5600113000d00c0c10383d1083d2034107004580808441e403502c820368001d145490b8401540d1a01034011503d21100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 129782508 1250 129781258 129781273
    0x60603150801060503031204050f1c03060b0909062b05030a030e0f0a060b010302071b050103050705070213020a05090a091e060303050d0b0303090612061203161202030d0501080f 78
    0x5080c22514544660fa405806c10f10001100090410f0010b0340300b8000c1c403e44290000501200d42405148402040700c1070141c107000e95015414851140640012405945824881d0300016403442c8001e14003840f60030400724060001074406000813400643c00f07900c003402610392411a444e030300012441c10000e46007040000d00d01d41c00043e03001251300d0342d002038042e06101d500d610020f4060503400a041c90307002c004079400600d088261501d10b0b881580685104c905240005041da01701030402810800c092010710096079030101883c90109030303841c0040c1d07907506a000c15640e43c01078200e080c3e40300110341c80014180c4000c0d046541200e1840b040c4100d000214120b5600b150003900000c1c0010b401800300440001a583c00b1010700d00c001802c913400c004401d4002002a0b10401c00e00c00c0c0000c0090030300119040803a2041241150400034504000c003504401010304541207002d815030710468680204540207004a0361006001c500912103582c607880e08650300c0801001d003107285d11070802c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 129783758 1250 129782508 129782519
    0x12150204050d0c150806061204050a0b0a020a020105010e0615030405120f0a090501020102180d03090308030a2004060f0f030609021201031406010302030c0d03050c07300c170109020406060315 84
    0x1c170b0851203050300a016600b0584810b040552044004100710b440e84181c20110000c101c030a2801480350507650009030791750000c1000242075500680c0030280560001090210380d40d64500010750f9101d503005200c0d00e80d511070410604c7c205512078282c20409001038006c4c0c078141c04c40010002d11311581c980c0321220f955072004a08034410f203414a9515101c80c1440d008500c0c000d8180e0f80d0301c41c0a807030801c2583c1e4490301e50078100d46c0142c0b20310241507601e1003800c50707600140d0031010400c0100c101342c0b4241441c10001520010b1108100d20400c9447d41d601302a080c002c0c0d00400150850003c2107450354001c4103644500740003800180c1c0e891418030201e607550040040d803203058a502038050071600d4800c1302800507081c00d000d0300710207001c801e1100076121002045841c0040c5a81003101e02c0f04805e010351202c2e212184000c0101c400c016506d0200401c1d4a440440d0442d2003003012444541842910180146001c0c1002981305043c5000000d00c294036412000f101515110007503c0c0c2503652 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 129785008 1250 129783758 129783767
    0x3060705041d04060b03060a020c0c150d050702190303150e10030206090f0405091c050f0a05070609080705010b0406080102040806010312110d08070801060912150204050d0c15 77
    0x6204401c0340034500d1040340d0302d41e00702c220a203402074401c2a000c9101d003418070009043c4042140c0c022000b560119007400b04d0081007103a2000140196003460030746044996401c1a0710801415484447e1940b0100d0250340c0b0170001e8036490079805443c20120000c44c500100503140700c0c610004008500c1c000481c58142c048034035402418111524104540745034244100d940002001c0c3e0352000c00592400140d480c0d0b4000e9611a5007054060b008440b14038050503003011242c0110401c014007823040d59102110842100c0d548181424025200d80322480c018000c0c003041074000708207240210310b000070840b05410400f00004200c6040c003e55031030300b240c14201c0c004c0b0f10603865103501030700040021695009500b81c014040e403401384c00a0f043300041a2038161041d11074030028950f04c0400110380d5011100d40e015252524010312203901d05030001d121140d2011010300070035030411124144100a90484000300009020b03c00c202915080c0860304603480d01c10b20324400750481c011516603215 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 129786258 1250 129785008 129785017
    0x301030c05100f0c0c0f0b070c091e05040f080d020d050106020c0307030303021b01060f0801050c0306010f0809070807090b01020c040e0712170d0506040b0906060a0c0c0f0803040503060705 83
    0x9030f90f0b00403a00f0803031001300d881e8440e401095405003026000410100a500b110401408501070819550711103482d1642406c219540320300c00c2240380003e804000d04c0c0048034102800040a40802c0c0c0392910b080c002e007600c148640040030203070f000a04090902081d00030f403402d00c0f0703420020403881c2c3c0d80303072801d036100d101001c000b42d416000340c003050000901030381c050300c00200e0803c2400d9034050f65011190840e40c0c03030f402a02492722000401c0041003000d0007403c0d440b07030308100907604509008002900080d055030f0030805206652000508103102013110314010020a411202810f6950000600914041d21314038014054144800c10504017800f8900d080d0034590002e0400c00d02d00326980c0400d070041075049030340c1c00d40c00d4040400b049011001d006408491500021141484400c02003180e195001080c0601601d100700201c2d540c3e8003040d115241c81c141031950b441041450241c01140103900710b040d603180d1a40c400305500b400000a031013030720750603011140280c481d00d505803540c1c001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 129787508 1250 129786258 129786289
    0xf09010605190302041203050c1204140d02010224061504031a07090801050109140a0c020705090a020d05010e07030c05030907090f18030e0f1e04090f02150301030c05 73
    0x10200300070044100e40c0b00703107907452580c586001410551102c54140492424032010b400281000c41c0d030a07170121003407002c58901182e0f005928036003850700d040b920001054415540c49108104040030540e40240510842c2100c00800d0b017020000c1ca040305010600141c030200d0191030039103569200301407030b00d08803000d803034110303400100d035403000d12041032150f000070078210070130040020001d5405c03424050740d40a04001e22001c2000019861240d12002c00202014a09404d1080c020150354010460200f5200d080d01c142d0900d80e905a02003000c0d110346032001148529050001400300c48460000e4001c0029941c1842424209101110307180000c3d00d07215107030303001742404100d407201e2a0b000a484101c03065020401114656607280e501c0c0f01c42c40c00342d0108600154042880c58141c0707126090305c10031500840c5808a14400d511a40140d00c000e500580e994010041480103159903144030540c01803800c8c0c0c4081008401a00780e400070310003110704001d00e9401203018a0401200c0c0e01030003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 129788758 1250 129787508 129787517
    0x406150506090631080606040c0f1205060118121e12180f060e0103060608090a0b1909030c03030b01080103020d06090606051002030c0601050406120210052203020f090106 75
    0x28222a02c4e244202809031480c0f42c698031010000880264000000092030740c90090a030f45d1408a0034071050320b100003c0c0d03c0810982641c1807020300c3d0040300c4800041400c250000725580c402d00140c2c0c1e0700090340c40080f1048102e01c0c000410701800024405490b120380490700300480320082c8004080004140100488004000e804080c0c0c402c60038801525a4031601c44e000c00d681b610030b909189902e4200c000090001541c842040d40c050043e10000d0503140380581042c9040c0b00c5983e1a100760b914010407a0b25030102091801d03070503444148000a048030304020340e801d54900507020040004003100800d003481c0c05030b8255805184401d0481c1e40291510b40c00d11034558503100102084081114116aa004003091a4032501c0290580d602181c0007550740b0f4060f80c0c08240351043c141d01c094030607818980c0520030044800e641d684403035810389a0b10300c8950640010340b1b80c1d0040f85c0321040c2c20101ca90700e0000c0b0040c060440400c0740e0090340c044010b25622400c0c841659001d024620108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 129790008 1250 129788758 129788767
    0x8190201030f140c0c03130f170a2001020708160303091403060a180b040803180c0604030f26070b0f060d110a030c09140708070e010f1704061505060906 67
    0x206810f00240310303010514041d1b9180c42c4100c61046c04c1101e050704000400d61596406000c400d201c101c070800310060050040c804441c055030390b00d440a880783c0144d4040003201c08880d03074603402009000702074030002098036480389078600000070300b83c1d4a1006a000034800c60f800241040000b51010207010f02a020b461181c1d0b400d0740c82d0007d40030380d00c02034001d52000d1456001060920034000d0050f0b20640406a50381880b01d4508040301c1e50070301c1444103801403901802da560b5240101d4040725402040b420007034915003000700030252001c4008000329801c000300c41c194170780a4000e01925114010a00244d1102603a4907080c0301c1c01c45038250070481e542440f01c013085240403001d51081c0c00520340e4414503142e5036121010507403a84480302c5c954448200c40720f17154400321b40d681e100101d454038070444d141200b4014984900c210074141403014503102207401d207200d184042002c00c0740cd01c0c119503904042c07070450018824009100c01700028804080f880380380c15012602d0b5208010491400c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 129791258 1250 129790008 129790021
    0xa0306120302070b03060a0306050703060e060a060e0906031c08010302100305040201020309010c0204110d05090616020d0809070b190e1507081b01180314040e1602010608190201030f14 81
    0x251700242c002584524550700000c0020b00c10300800e44101001d550200311140303002071300f00b909000645150321440c07030208284042c1e90300c0700d401c0c0e0b4514403c90388000035855201c0480d040040000c0710400015200085140345500448054100e92081c0d680215107504ca8408508442059030700900580080118002d0b03503100d00c0041030800e000910006203040009804c100302d911002c48000001c0d207400401880850034010a6440090004504054003000c4002902d885024031100700303100484003c51407054040215070042c008844031695122403188481c4888010650030764002420f11030f400505041034600c41503072214102c0d1181c248082545c890086130840d904071014501103d020542c0b903902402400500c0c1c0c0c8800c0d400089484030708000b020005543c8100c0907500040004110b9001c6071503a10354442c035110a0a00343c0321076100c049000d0000769001e0083c2c2e04c182102691068421a075055a01c1d1003601c00b001104d503c4034a050903200c3ca80300400040080c4000130f0803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 129792508 1250 129791258 129791279
    0x15050408031801060f0f060e060403050d080a02120c07050115060e010c080c1005010512060f07030203041112010c0f0306300b090a060507030b0904032102040801020a030612030207 79
    0x20300c40b9000b4000300b01c141c1c032001c14840c40034080d4400100e00030422800c0144540010084a08040594242d8601829078445596503500030340d050042204020025002c012654103881140111038039011040c1131005c0300d604141c2048005a41c194038000c5065124008040c0b46000c440d01d0b174075035040b601c490900541d018034840009640012040008544010003071042c0f8120400040700001c0761350502d81806248814910a200c060b03118105000503012803c2240ba03100c203103450056501e43c0c90f8a001d030758546595040c10340100d0030b066540c80005041d040541c0c240040da031984406a200c130030490a55800e440340c00118a03114109880a0405c0340100d40004507650000030318101569406440140c05c589219254100100031001c21496006080e004042881c0c14880d1080c50b2000664004002d400102804850248003981d10380291000e0b0341c1c101212401c6480e0b669030003059020390301585140b0006403a000c00858602c090882180f00c02c0e030154010071190341440d10314203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 129793758 1250 129792508 129792541
    0x907020307050313060e031504080f04030209130209060d08031605090303041d0106052b0b030a1104180b01030605070302091c0501060531090c060206041505040803 72
    0x40850004110707103000710b1801c100900100d0b91003041a8041441c24030000c0c9016180150f481c46030300041080e005d8840b08c040c1c510f0300300380c01c00c40070b035030b6281030b4485100d0314451a400290480c5c0100d080044081c1d072800144d8800d070084e01e01800f659030b0752003000910300000c40018100304061010074041902c0040001a10500c0e0500c280351684500c000303447c54215900c6510544c508110306000e0b08410f41809004000c0c9040132030802d401c500200c3d40128100010b0780e030b10700c3d44010921490032a43c00501801c0000f0341610310000a5080510030391018180e10b40c080c60a003601101c940001c01e01a8001c1604800000d0b82c031b90841d86d070000607040140001c0c08154003480310402966030340303034980c2400d2030a6a610560f4405403814600350303901c941c8043e101d100441c2480300541104040d030100400ca00c010100004d50b001c80190080c664548040d08540d201000800d12580000700b03d402103014682600c09286006100c4094400c200e034010300d001c00c24070108810b48150a0b4a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 129795008 1250 129793758 129793771
    0xa240810051519150212090f04060902031305060630010e0706120f0e0706030b0a0e04050610240c140a0b1605090607020d030903240b011d09 62
    0x89090700716000290607815024409410001c10240804c20000c41040368002802e86001400d0f11000e240030031611406048071441c010b40d41c03e0303a4280265500d50280c006000000070443d00e0303003415846c40383c001103448011074481c4a42c1010412030321b4107625180e0b0480a07440c440021030200301c0380c50f0b110022100c1001d400c3d0340b601800101c18400340a8031018220340d80d0340010f803451200e026820303243c2107504255424a030148007040700402041c403009680c1d0728140803c64854890200b00140a6a840151100f01803c248410000046066409400c9a4083c0038041d070300e9429014002802d1074104d081c0b510305c2d0303000010803401a90203140441c01200300c000c1c107100d643c800c02e0500c010302c10b086a00c06004010040100004600391602020500e00241401c2801c800305c2c030366100b402d1010344a6484203980e0780c10144580c14980286901c0100304444009410761070007000d040c1030941d040a81440c01d56001544910513480314240d030080da042c4000304220a0190560020b05003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 129796258 1250 129795008 129795031
    0x606041419140a17070626041a060603131704080a1401060602070305150c0c03040e0a050a1803030506011209030c050c09070504060e0a0e0a24081005 66
    0x20038812114001c0340010700c1d0368120100380c025403104001c05010260003040c0c01d2034030f0500703100a41e0b0000800303105070b03080d50401d409031054444154003a802c2a0000001c07040e400000c01082181c5c401c00c0b5200c64141e03110b6020036480d02c008100c050b01048440a160089001c1850040741c4110303800304c8103407502d404c0a0316040e1100c403000c0c01c2a905102c00d486030900203003070b07404000c0c00b4441c2c0c000030140761010b0080d0500315690103880300c0841c0c401200700e81451000c641945192400c036189103840000f100c0d40d841d0b0300c0c079054003d80d40440300c52611a15050005034458650b000d4042400443d00742c0782c1c5001c0c1c0c2035805034020440075012313504103c0307003001012507a0300c98840c00d14054041d40329254030310443c0c50618a8180c071003c04130b0081902100b44410582c000060710161500c0342400040c1400e5403000c071701d805803140c0c8048450910a001d00a00101d681c1c80b05041c0105040e00380700000d4080b046004222181c0328000c030584c070241d846501c0a82c0b950185400000c6c0401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 129797508 1250 129796258 129796279
    0x1128081908130f090218030706120f0e0303100f0b0304080904020304030e090c040f1203232101080d030e07140105040e0421230f1b0d0e0906060414 65
    0xe20340e20f0425a00b241d00c00715400282e07200d0065054000e0000703c001140140710031820004010b10040303c00c01c48a158a441d0b14405035080c00c40d820402d413281c1d50100300d0303032039143c1007070f00f1b005d2100a4802c02a07181d014203800301c1c40c0c1034200100c0b4804c54210449034039288240c41400025031008105500300501011131102c1c83e507809100600171080402e1a42e00c41c2d00b00203401800060681c07100081c44c0c5030a1041000907044040702200d41078114821240707040c0030031a21601d110312008910040701e005110501002c8500d039a60580700b0210465120010780d01080d400c80d40c102c400c1034140d511001c1c0c02c00030003800101c1d01c8112141031500300c0c24150784a065071540c5106940440741220f90740c2c011082e0001c91034007019000d4003850400f45c0e0302c1100d070401c0841d102d010078145c025080000d0102c0500152800c6400004030364074102c1e02c00c0343c40080030381c496907921003610006200d4084c0012a00d40b81d551140942d1000b021249420300d0310180d695225004c6440e6a0004d00452 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 129798758 1250 129797508 129797519
    0x1e2a011103011a190201061716050603060a0b030702031b15010308030a06030f050106141c02010c03050c0f0f2401050603070c020607030315090e060f04112808190813 73
    0x130340043c4000325030700085507072070820390310010140601000c01e41c25407002c039200302c4519029080d40100d0350f0554416641c0c3e120303280230401d00e1859030801601d10400005011007103500000405a1004011003540308420b1b440c86a51105504445d05465203408801070021070200341c02150031403407140000a00319684d6a45011255070680240c4469648180401020408500000d4010000c4402d43c000358245034114141544e080400ba04001d03040d080001050300079000c039850201c06100f142e01c00311048400540d10b01502800010501510110492110222448011507441145141881d03070900c81445500d402c010070080c1000582442c010141c2c0740c000040c21502d01a5401013400c110701440b85044000640c801c592245c58802103030081395010840c107420403c041c04d800c016840700c0c140802001d0f0324a0307040780d0004040740f020240d03503051044910a040501d0a41f048150b954049680781e02c1a4005000094501e281d154001241c000080c05c0300d40d072101c0714040460f2501d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 129800008 1250 129798758 129798787
    0x2090a0b030f241b18131e020c0c04150302090705040e070c030f0e0a090e010204050108060303130302090403120203010e06040e0105010315021e2a011103011a 70
    0x204204900e90000401c030071007420f0641e0100071100790a410100541401a03040e0340c00e5000c0400081c0d901000f0610480c4a2880020260f00c400020914000d000540000000030f12000700d5280210b82e28a401070507644007402540c0e03181060402070080d8820b00b0b0240300140c40965415890a941003602100582d81c5c0c0300d225005014a03902c036030b112810120040c2c15094003400360814081190041c0c000203074003441c03103002d0f10402d181c1070901006100201313030780e16640d400c1a02c0543c1896607582c0b03251415805001114001d07070754940c1a44580e828180c681c030842c2c078070944190382d0306818405030074000c48450300b00380320385410b0510880c000b094000300d0304280c2140c41240800002e00a981c075040c00740d6401c880222000b08910b500d143c5c1c54a0118100c10a03083c0110b80100700c15801c0014000720381d002c8024016107039903500902d203030700a00e82e0181c3c1100c0a9195142551b61401805100f4894000035a5042c40c0c556428184608281c0204034005072000604005440c200c0c2c0302c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 129801258 1250 129800008 129800023
    0x1b0c050607030915110708060c0301140409020d06050610050301030809300601060806010f0f11010608010603050105040b0c18130204081507090b0a0c140307080f0903070f03020d02090a0b03 83
    0x5545c5031208141405440d50070140c03070354083c00c0107a2210f014403030200c44850449044a1400d03110120866200d001301e00a4130005c80c02039400880558580300340211500030307a224140448030150100c19944058130740c7d020a000c060802e003030500c00c01000f410320480d803200f881505443c50303031f4042e01048010310803450300401020940000d4010044070b0b80011907150400801d0038140c0c1c101d5000040102203440400080c0100500000b00d14002d080c02e44c08500a0074981000340030840d100d09109010b0f01c010b44046401060b541d0004080c01c85101c16152401c024410006440780b03c5d200300501240c0c107030702c4a0360380c0d642040001140c5600300507950710302c0f010524008803071508501c05420150158420407480908000c21220154040c040180003980a241d0b510340446c01302101d442d5006510004295030f2000803010400c1d103146004c2c19000b0300031002c441c2e9140c5c0351100c00300c402d249880020341104803e1244001480e040d40020385c40480c1c0e00001941050444c002b0745440c42 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 129802508 1250 129801258 129801299
    0x40305041a0403120f050306010e0f0409050f10060803161a090f01050c0a02070b1b01060e091b0d060209040f05010b21010803160804091b1b0c0506070309 68
    0x81c0002c0030410840d5040000d5806141c60420700480092038201402034840205254104030f500443c07a6aa5560205d00010f804030280c401c2007035410a20b801d0340d940120680f0700d8003c0c802c80664840b0105180500710680703010001a50038058561440c0610302c004041c100d8002400c41c4555080c100c0346003070a44a48200340c000c0c0500d806410405084900c064a82e06402204000d941c000c250000f80e090100d80a40011594400b2020320380c201804124a0300032030b41d401c00c100050000014803030f45026800d90020303140036481c007249108000c009400015000801010300030040366059000e403c02c4003000e0b00202d0300741c80035030314001243e409801100c100720b0081450700304106401c10320102c03031801c0700d03403400301d5410140b0362039481c0220340c4d034649041101e01103142082540420340b0000c1044800034805c408000780c80101c89040010100e0000b01c030f2008000d0202c0312a030b503800b40641c0202401414030700b0082481403a5100d081d007a401c0c0b00c0500c5001035800c410200e07107250004c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 129803758 1250 129802508 129802559
    0x902130b010e0405040506070c1b0909021915080a0b090901052205071707030b0708161829030411030f03180105031b0d0917040f03060504030504 64
    0x40010380090705508038040c2050149241004000c006080020050307004a0607040c8030400f02d00c10707d000c03003451109130308400901d881c09000155840c110342141c080c0c14801c80703250b400800d48840e070001401182c4103d00e070402400035220100350061000c1c1c0e4111400e440d02180039090070011426031074040c1c0f49240c040c0e54510800104610888524500d91005210b01c250308030591039441d550a1b00d40214902e007040d140f81d03800c01a0b82000400000d55124884a240d881c2c0710030b0241001e0b07812030b4050b0ba402646944256910300c110b80740490030408824044026042400c804040d4452100074590405010204040f1818540c0039510070303840344000c031524000c40018903003041001d002494147e071060081002407010701c0d45180b000f080a1803da5101c0d941c1002e48519009605182022800300040d200d2089a898000f800e00398090140ca010032540a650302000348264400c191841e11403140600005443d900b1a6800502a15200b400c2c00d45650542c0e40030061843c0c1c0d482d07010b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 129805008 1250 129803758 129803771
    0x3020706030e0a02010c083601120c1e1112030411010905090703050901060b03010308090a171e0709020f120702010501030308060d030201091205070605010509040c0612090213 77
    0x840d0706002d00030820402d03078081d119480403580040c00d44100b03844002c00754032022907031144600b0103c40b0352202c140b0801c11250300f00908070380c0700408150000801d0000e2051404601d090029002d9425501c0003961201c18071000d101d00c000310301c20b915040c1001c000c103030025a001028208a480003099184030850b0f52401c1a1910034180d201d80785d0840d051201070b08041020740d503000021580003d003818045541e940c0c41c0307070b820f0050195800004c030902022001006110a00c40a008041000c2e1211038000e84c485201c02c084800008504642e503024250f1304034021500d0021004c0d12803001c0455805540300c1050006076084040507040c0c00d1804503d108140340d1384400030741c2201060000b000700c0e50540c1c80041200c40000c0455002c0c01400c001079040502c02d50084154130380080d41c2d5083c11500c0000104182e02134030080d00c4d89030030040040b400b8a031031910203014540c41000d180c0c0082c40c012050303820140f00011413200c02d5498103c880540c86801c200441008a08030000c1c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 129806258 1250 129805008 129805019
    0xb060a1106060d0c051005041d0a141014030f01061d0c090f0f0d150e070b040806040b07110607051b061605090f060d02040509010b120703110412030207 67
    0x140000101454858503d100700340b000f00d035600412006481c4144d800318041504908261803901c03882c1e2010752030140c414040b0a016460040840c00b40c0d9007501d0621100d01223079100801e980c0140c5001d090028503c10800c1482800085420b5036003014081d10f0034142c10400440c00c668055000380700c144640340c0d03903d001d00300420308268002405c142c02410480b1003c0032031480382c00c10044c240203441c1d19000e9a125502c02e409400001d07030003c8810a62500480028080e1205020100035482150004a00012940d09a0702030700c0081000300200d0784d41d44c407084034104000c2c014030184841d03d101040301060501141c0d2091215031038659030740696014050000b20307e00800d50300c54009005000d0380310301d4a503810a00102030301d0004d8580207140001218400310b5030001e171303100000040e007105203213498010f0b0084403821100418541c0e40d6140e86001e510031500c050b5850300405000502e454020343c02400c0801104030202d003419254640c804014602100507400b50744164000c004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 129807508 1250 129806258 129806263
    0x8010c0305060904110d170a020d02010608190f0807050708010b0f0103060b0706050c090303070302150708060a0b030403020a060519060501050f0d0209062101080c0a150806040b060a11 81
    0x400c04400d80d01c03c3c080d403400d5201c1c41d040d2410360684502c24075a026a140c284461b600035400c0c00f4004a000a0f500d120505010b0f503601054490f000141d4200400051400d2011500140c0c11016a040c0e0064500c141d8440030307030031011303201101d1b004418015000420380402800008e003140500000b0706410520030011405060500d5904242c10a0000d200d4010610156805503034040b60205103600c507650040210700401038640c1e0144800702d00d00b0141580010b09240c3e5100541e40d218503915414411503040f10205c0700310350130509080081243d085040010340d40310b4000d2042d82c40b05510390741c9500c240c03042a074428400c0100c8541c0c50070121010b114000c000d01c001d0030158508000000c11044a000303200040040395800310f0602100e484207000c48000c002d60051081c4240829600124903c00030300540f81c4500c10850410a0781c20203030320250650359101c100304182e0141a10484604000910460300291103503807031161502c0d1000a00100c01183e142d4410304421041d6640c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 129808758 1250 129807508 129807511
    0x813080705060a0f060b19020703060e0c0108160e0105070609020307060309110315150a031707052119051303081908040b0402041d060a05060103050619060e010c0c08010c0305 77
    0xe04510300326042010b54588022140d000101102107d11030405041c1a414441c0300e40c80901210b0500344190031205003c54442c044010903210a0250b440700e40c4074540d01c00e403160251020409940b0084030039809000a0a4503d118480100354400c5030b0303000c6403c2c5083c1d50700c5500400c0e15480f9000801104040d000c0f001c1405500901c0361364800582d0281c0400040c001c01c502d01c000f40a07841040c2c60705115030340910b4000110714001d507a52111803c49600c0007106680314044c9094982d181500d07504000c02840200041c9401d104103080c94900c80c050001000e810701004200700310000034a400303c1001076005240c0142c450142c1e45940c0072001410128808101c00c1104120002e4510f0030103541203a0107035000141c046030700f00c0180f0342044000c1990b1603481003001704620800c46400842c8118000e03a000d100035203070103052008094011000380544031440c8000c1c0551032040032002a00b03081450700c2c1150340b08644550600800d00d070410220799440302000c010340ea8040c0160f5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 129810008 1250 129808758 129808781
    0x1090b0c0703140c03150702010506090412141603030603030206010902070822080604050f011d210415020109060c11070e19061202090702011b0813080705060a 70
    0x1854204099111500c0728200d0000030000100321209a41010081000074800e002c003604480341651300b4003950b411044125000c90042d03082c200005c1590034130003089030080c4c1c0d0102c0a2200f0280c02075040d0784040480700f402d03d11120a111400381e03121242c1c11400c40c10700a4030001145400c2d03090080c1004016003004c0c0c802c6004018a000188401040b25120001059840d0082501201d903842c903244903400300c00940b24080511043c4040844d0b41020301c05010020003844444850b5890280c2007844040700d0780c1c000c01ca110040148260b01844030340c9514680f54905921444921034210800704c045c0d0040c0c1d9102101410055244a42c0d0003600380340c00d1440100040711801c6644041c2805100311104140011588560200e6151008036905010500065440388103046007100744060aa01c200108400300c1c00e542d0040c4246c24480d080d40716030140c8003041c40016100c0c2c0700040c09007544286250800e0000c41c0a5801802d40d191040c400391010f400e0824007030040e54070003140c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 129811258 1250 129810008 129810029
    0xa02090423070b160215041e0602120a110f0d0f020c03060903091003090204050c0c1c020601120f0b070206090f010e0613020d0501050a020d0c050403020d08030402210307020109 78
    0x910010340f90000750b500c0b07100d403000c1090f40c903504c91001c1076100c2c200d0b4210b00701c0183c0104000c00c0c9160685018001c00030300c004101140c0b640c03070004a070b664110060741406200c041000c00e07009132240e028007450344505c900300d84980314481c160501e40708051030090b0000340000400002c060b03041c045142030410071170080c50b803820112070036504c1c0d208000086205007100525901d21034041d800202d07209800900400c220310309056624419030100c000c40e4180d00070b0150440c0342d9828001c180c010940e140c0c4c0104845d030300b0120380b000401e040d542e00351884444207400f07100042107110024481c0d241a0b02510f014280340c0f007914030f001440c0d00355114036410854001c81003440001c0641d4402080f2030150001c240500200e02c00000c880405031081d402c01c01005901e8400350001d1954040d80401046219030035441192140541d00000b58003001c0c00b1400e00202d0395039400341d500a400105480c48408903504001560803901031140f4032900042818020f640e00200c50700d005110b079141 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 129812508 1250 129811258 129811273
    0xa171b0a0b0106032a09030b07030c0905060c010617010c020708120a1b080c0a112202071407063b0d11100203031005030a0209040803090a02090423 65
    0xd44050701201406140201556000c0c0c80303403181c03031240c0300b40513040c50007081c0c89064881480c010910000e80c041a11100300b613001159000e846403041080d00450307a981ca04002d424a4100151607100d0401c0c1e1146640741c1d10302043d40c00c00c000350283d038480d151b0000030b044110303040c02900b804880ea220743c565400c260401320103071800e14101c541c030f03902a1600c00102c01045600303880c28000406d002d412400d010800c200f10344400660504494001d80d200011030440c4400c2042000ac413440c844004c1c1243c89207841c40401d180c01900030f0030f2003605440380e42c08810144514040711a071150300050900720115620401c000d030300c1b0f8980c0001c1c500b00c01c0d200088081c040e5070800c503402110b02800019003a8000d120741407004203a07016004011044400360f00200a40c3c94000381e4a2021040c0100400201880c000409814099000e000a0110755940e240c041540c0c0000303013810218000d5030700200040e51480f909500c59441158014185540c1c0412410389040380044600203500612 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 129813758 1250 129812508 129812513
    0x30105010210020304030201140406090b0f01050307140f060712030b03060f0106230406030f0506040905070506030c0c0a03090608070f0e060c01060902030c030103030219110f030a171b0a 82
    0xc02d200d00401580c005a640e403514501240100343e00e882000ca2034a42e141404100450303608105e584600030000c100c100d4445000003901d0072000e06c2040e40c990701070750b0104040c2c0c062150000f00094000c14400520101202044040d4414001199203482500d010062190148030b60345220005038020881490481d00000e09820103015031028051101540c01104072101403618980310031032080d0361680c0d564100980a080d40004181e076072404c24000407181d0400303103e440e84040d002030050070041d16103002c0c4216948003401c0100c00d040c040240b254500010060008018805d54a88404504d0b10070000d100340c0c0c014191004200390943c500d1a1140e020358890645002100c2c12551034140580701d03401000d070381c2d00160415001104006c00d02c081f44010f94100c0740641c0941d012007042451200180212070b20090092160003501130303444c204085031034072108010b41107443e50b01c513075111001c614141407104203505c2400618008080101e00340c003401031188500802d0000441c0e03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 129815008 1250 129813758 129813763
    0xd020303071d040902040f0b010e0105090d03030c02030c07060203071e05060105040507030b0414070e01111009140f01090c0b0f0301090b030304030c06080a1b050d0b040615080604050603030301050102 88
    0x50303051600c1420750945010300b035511980098a40b039402003040128942c5c240300500600f400c1800c050100d01c649201583d29405902141c0071341c040285004010405640c080d80203045142890045101c00e2195400750502008894054030b5540c00445c0c0f07814840c607001c0030042e5072401941021061a40b94800a140003c0e021f06581c3c0032100480c3e1a50380c0d031012802403041e42c405560260030840d004d11200842058240580045d642e0b2900d40603100b0015a0104465181d142c5036a1206400ea008180b8a030b010041e01c1d0700c9181c20810307550700c2004441c6040308040c2e01c90643d0b5520325038001000100410903009122103c155401d00c01c0300602074009010501c1101c44041c0c0b035629502c01030b5414170444020f1171380300141898030740c0ca07800c00404110302100c01045152504884180d0340d40c2c001c4480804107420784d0360500c0c082d00c100f0120b010307140c46d11030550031580300c01c1c012484403000d00612041c05016507a9081916290301000103440001c0c2001c1e0080c1c00130001030084c3d0340d02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 129816258 1250 129815008 129815027
    0x170a020403051509160f03020f120a06050619140901060f090306050417040e18030301030b0712060902040801020d18020105160c050d030c0212012c070e100302030d02030307 76
    0x20504040004ea50310b10720780d41424008260036483c80c241d210041441d4840e0050300050300d009560041d084100a01401002890251902c1c0e407035118501f50300011b080d43c0c0107540e0102d4050320100540c900b61042081c03c002e1074011426510011a8550b035508004410b1401050b0514001c03d064124603405084001180000340003035494000003028020b041c0c0c4070817690301e04000c64030b0750b030b66441c10014080300b03041e00c0300c0700c860718440d070b2100c004180001a03e040c0c03900003030714200d0b50710b400c1e1089c0e514890034208511003c0d16404005200201440078000401c802d07400540d44815411030303d001c444540e4400300310312181001a4025076405015a640102c8042083c41c030300301d203410046075000243c0e01580d4880040000c1004156100020741d264501c00d40e0650040780c60148203078244c0f00c04940e24561021111840507007085c000c10740a6148000f20155500d2688684501d11910000c880711503060b05402820800c50804001070510300c8094405541107041c0b880005054014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 129817508 1250 129816258 129816283
    0x806280b0a1116030203060109050402060414041d0d0e01020a120c0311070602100609020703080c0a03181218240504120b0f06030106030305030606160b07170a02040305 74
    0x40030601c01001d600400004105800c0c0b030342100c080d14121100382c11102c1041c0412800f034040e400000800c2c3e800c0c1c1c061103000e03d500403d0103003010b091100e0b034502c0007240103030142c1c06902ea0072803000181c000108102e006140c032010f0010b82c081250043c202903200d010b074504661015111001040c0341601405001c900c0f450140340300711442c202218041040b81a20b03506000b515070015a141d000220180850b001c0310082c0201507076a00400202d008208000c1e010030300e503900280440e01500c1c02056074040505001a405030b001c80b20034006000940200d0304240c40030f50702c542c00c0340c01407010080c2813000f5901d12007003030134034810b00c050241010084c010309540c2d0340011a014002d01c180c038050402c40080200c5030300700b824950b07000b14042d9010464598a030f00880d040d4281801030b03070b003071302d8160329010701d15260b000620103660f01031102400c1f03500068901000041d0b22080040c010135a0340c0c0c690400d0000c82c0da80c078100c0070f0060000394919204000c1000025000700b4082c00200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 129818758 1250 129817508 129817529
    0x14010507110d080f03010e100b1c110408070e040611191209080a0201090c06050405060909190903021b01030603020f09180706111507080f0702010204030203030307080628 75
    0x4024904074505000710f40511941000200020600840b518041d034451001b0b41c179232420040e0b944500d14013a129004a000c48d47c0da2200c4c0101c00c4801c140c00003040200c1c41090070789000e654a2400f41800d000713401c40c00c200400d98051105103c40c0740103e0000c41091016585131100c0150703018201c4031202c00320400d01407840c0d2009500e4480760701070300d8503d410001e110381d21840d02c0c034024001c100c03c541c200ca164858140101e56a1300c601c054070b042d140090b00321464200f202080081110005004017441c2000790005902c8070464010558201e01c280c0040c180762422050002c1e030f8902424000f4101440c00a00300056036030040c90b80c68644041d14480001d0305c1356910301d581202000851071a51144a80c00103680da8401a03951800c036030f1406455502c0c00090720104003403025034080000030000004100310141107a55160001d040340001498999242d02103170035500210b44e400c01080c50b100410034641840d500b002c082c4400800c0c80361000d00c40782118202030007240251100813 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 129820008 1250 129818758 129818779
    0x10f0501050a032a03030806011e0818160b032a040506030601050706050108030301080106091109100504030c0605040f08010203040b0c130b0301030b160f021005130218011401050711 80
    0x1340b202034130101110162254a041d203d00b00989140d00c1919054009022891007441d0841e016103202d03c1200c60f681c6131107154442040c0501000c0070503c4541845c014002c2a4003a8000760307071038100814010f0b001548a190a20701081c8556109002a41807201c540400e201c3e451000c0032281901c05c02c0303501a4583e210b12004031400d000d8020004d0401c0d1401700003149940c0000080c5049442e101e000744070355030300c5a0b80300d002e541c030300219440801c4c0c0900c01d009a6151001078405905c0de1803410900f05941c0c0d843e60301c6643d08507400782021800c00101448044c10580100c40540540c2000f546141807507603074100e2064008002581110b03004c00c074a02c0b626070400c1100b0051003040c005d580c4958490130f10302c5099a090350034980b404075030254812154007a1600030014100c2d134002c2c1c040040ca00301d00c40081c0000602d9042d00030000885000180e4904088503024425000c03c5a1950706110920b9a01e640196056040c40b10500c64880081d01e180100c83d8103800c10303101c80050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 129821258 1250 129820008 129820043
    0x120c0a031b03060305060a0e12091f0c0c0e15012304090510050d0213020c0c0d030507060e010b06040519030203150f010b03040f0b090f0118020102010f0501050a03 72
    0x18072500032020501400801c40011159141d000340003602d01400c199038082d00e954410b68100c1b49250344650322070300901e503000c1e81d01c240d410150440090203040051a01ea1800e85020749205410305c00e0042401c0c40815810f0021162049000c0c10503004041580e00300490303040c1c80d500c022640d07039042042401081344118099454075056980c12160b05071546d4a486210020780030440b04440200071078080028a890000020741c003048c0c010b0250590100c5017050800030f503000d10048405441a00d042000e103803906500401030300d01070f90b0b038a03032600c2407031401d40203035218040040116030408150105ca0f13a41d080c2150121030089130440f0300c1150102e04070016020700e40c000b941c035001c0c55200c82154140c111046108190302e4040007081d03030321500e00d402c440c04207580280145040000410004440c0444150480018012540e031540001e031281d00351403520b03400c0c0600105100c140360440d40c0900503107143d91881e02007440b496040102150000406d072001070705c900c20b41d0251070007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 129822508 1250 129821258 129821261
    0x11041a09070207030201110607051209011b090801050a0c0203090f010201090507030f0209160e0f041b02030a0201110c0a03080c0d020f0a08010b030415201308010e03120c0a03 77
    0x81a5902814414440c541a50041e48444036840242e01252000b0880324464101198080c403a03100d507264541045000d01c0038102c9440c00902c403515641d6140165141e074000d0440c520a5680c10f40e4590b0100ca040c03001640c03e64030060007404403503080608182826802100b80c840e20502550a00c16954581c00101e000d8145880301501074051444080705200c0c03004000a4194000d403110070301d545a10407c451602000c04001c80010311039000041c8900c1e04204900421000400100c0c4008440c2180c400700e1851110701c1c070243e0300016020400d55020700884214600041d0080c0c1442c08a550701c5464444c0403900600b00045540068881c1c0d072450169507a01e119140c0c219114041440c160140da400124001e0214007000000200e4525440c05c40e4861580440780d03e034110941c5d00390700047c103803103910fa2000e900b401000c8a056002400a404400701401c03442d154140341c101c50a00f101c01031004040d40350005c1144620071140d80d0401078111702981f1860355200903400c0101d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 129823758 1250 129822508 129822551
    0x106170f062e0801020a11070b03040303150e0901050702060a06060e2b121704030c0b10080a0507030b0106050708180307050d0b060102060709050d0305160209040b040b01080a1104 79
    0x10b61a600401142c910340560243c500002d8548402c0c2122040040c2203a0702c001d94481c610040d9030400000300042e1203500b0505401703100800901d055503c4424605c10040c04a4101107a41e6503107080160b070702e50420120b6000b0b0481030041010707a0802200800890303034542041c2c000e01782c84000580502d00c090a10400145150600240400e5031070039071140b06a001c0d480000401041000c80c1410307000090602030b41e4961290045e00449076030300c2c11403c0c00200401d002040d00200019075a00502009240c54400c0018203940d41c150718142c0310022068000384c08020090102d031000500c1c403070072503a4002904c0181524038007550000391130000d80350403860b0012140c0001d0700030018040354035800390307c090b000d64110b035407a148100e520103090321035103031700c60a8181501c2c00320740108002c1a04850038400180c0341080c03034004c01c019080c180d0301214400c200030104414082c1c009a41c902600fa4600542403001d01a100c041401141c0034045120f2070f601d20703c40c07444116084010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 129825008 1250 129823758 129823831
    0x310091b06180605030f070c1a010906090f0b01080601050304050f121213030905060a1202040b0403051e0a020906060d060902040501031a060a031e09050106170f06 72
    0x42455a407501c0000300050b0b034804003080482c1e0015000710b8600c0c040c3d403d407407181c1440540440c281e613500004507108a0413840c01d441c142e00012181922180c0004032a020700b402c0e58021940d14500b810800403202c000000005980c500074404503640e900c10015600314009107895500c80c1c40b942055401c14103c824000c480e8800c4056a0103011005070181c0700d0040d25a0340000c03075030317502ca006845c1612804001030001e403109905204a10708000a0301c007000803031400419210b131900641003240d215400080c044000801d040042101c20481d90741084841508442c0d111116820541d950f0000e001c02446202c000300000c0c02901c502055401c0f02502c1e02c01805010303274034110000294002e0080350700003800c0c114600c24422940d900c43c02000005050740740781800c8507100700d00610041c0d1801c04504d01021a10000c003005000300c407840b1340140c00010b123182c9080f0303c1107902e1400441c01e8565401550007000d00e20008900320b0f038014035015001810f0340110740e0b0709441c00110080c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 129826258 1250 129825008 129825053
    0xb040c08010906050411010309030c15020c0a05100e120904020a12140a1a030a110402041a040504060e09060a0c0e0307060206101a031902040e0c031e06031009 70
    0x20241800f107036030859800745004802c180d520702c00100044040d01d180b8003028011500d45221400001c4010641c8410880403400060411001c42d02c1e00c0e0030300400000540f082e03401603102c100483c0091007034190786181040105040c201d10780c0640010301600e010f80344104d48c089031200e0440d008042c80765080010700c400b00f100c83c0c1001000c090507001a200b21081510b80184100c0070b40700d0450440c7c0480000b0b004104a58046da981c291070700310100001e0300540c0900c00046c0079100e91800306414290019200e850b182020240000c45d19241d0201501000c41024401c41e480c012807100c0d0841d9040c50086480809024181c420385000510075405102d40600010a9503000c00c1403800307070324480305891145a4035460700142c4201180c581c8012a000c001180a00b21102001d0340c1100441c20054189075075803010b4500d6001c100e80c03181c0311110010405c03108180f40180c0a04a00e40004040c1c545d05107440442c0d41c03164400c0ca03a0382c040d5900c14041080c0940007140e0400c40440e20030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 129827508 1250 129826258 129826271
    0xa082103192f0d14072a020901081b06070f020108060a03021c050606060c03191103040306061701090c0501180509013005190305120f01080f010203130b040c0801 71
    0x11075101d07401400f0402d045490440090852064216107a018100c1550307402c0c03801d00c0003d43c4040009500b10150340c0e4a481202d0b090050300c2d200142c900800d1800007420000b601540107141f480048112140320786010400071000910512000b1541a020319240002d5030314180407413031251640d0070180d448903110703240e480144804001145c03103074400c02c00c0d80c8568a500c81881311600501101c40c440c0c1d00180505c4405504058108003d00003510305806004c0303040c0111410f56000c0d03001a07564a8540005001040940001d10183c1c030190000f00a00c0100762101c3c800c0140c24001d0a04001754801c0b03071140d43c14040407500c003401004000e102956503c075180b1580021040900c00203540c400c454000e21100f400740700d81c1c01504400a0144205141142441001c058004505206042c00401d4001035481d55a40c411010707210303901c20b00c1d41801c0c2d1031460840c58a202214603030040040184151402400c00782550380b21702c0b07003209900c45281030009048030380c00c052082d620b00070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 129828758 1250 129827508 129827591
    0xc031b0c2b021204050603040203030d0e031803190303050c280f110307020405060d1b031502040b04150314040303020304030810120b070203090a08210319 68
    0x124049040e04810031124040c1291074026078954046595002140406000422481c1461402141d20a1004044d6450290074980a00032643c3d01d040341611988040f480038487e80400d84542030166044000340560b080181c01040405003828004080684940100e4808216042610180c000c8000000c0f04070b07000d100c4220940e4407007015840003842480c0702e00415030049890350700700110b0b50301840c5001196024000580006480f1320740101c2c02c4520320010074081110790740350400701e00c402115545581403809081100100d84018948100030420201d1a400b044908440150b14016110b5659190580041403282030b0781c140300200720200003c0650581c011440782d032094440c0c2d001070300d517200000080d80150088003d1000707018454008203d82c00c01e40c82e4000000d104880c40c10802c14081081c0d804c0903445000c4030b502080340c152070703032804002482000e1000c14101c0e0851408200c8080301c0003450400102240e616040c050403400300440c59081d544002441140c0a410748 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 129830008 1250 129828758 129828793
    0x10306080f030d0501060504061b020a051201051005040507120504110901030c061404031a1b0f0d0f021e0d0f022b0c0207061b2a0e0c031b0c 62
    0x12050f4905290400208020303020700c01340ea080e255155150101c001124210305c2c0d000000880c240da001841140008403940c46440840403a0740c40400410f05042500052004e2407071600140d20481c2000300304a9169805902448001c15901010403191124100002d211482040003908401a00c0011040c0700302e2b6200c02088992555403243d40310300385801583c15000e0707404011315204800301c0040032121100781b00c0350041c0108403995481e940f5040d884100b54402208540301c002c0c0414103001c0243c00d840788400000d041d407000d41c40e05840342011184d6040520460311310a070049a481d500300a00d520031088405011811556140c030b0203080e5403200d40c0041880d5902a002440e07041d20f01c0280a45510108103400501340141841030654145c034080140c1003903440c0b001d0fa85c10106e9400388078002d426100101d03060481c1040d00e240a00c0c0c00309a00120103c25010013070000100e25402140c0d0b2040d400140d41c10001d8881c140000148682800311680d032003901c507074402c0d600a8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 129831258 1250 129830008 129830017
    0xc0d02070b09060403110a0c06081801090501360206160510050121050c120c04020f04032d081b01050f090708010605030303010b0d09080703080f010504020f031302010306080f03 78
    0x1d44486c41ca000c018041103644180300e020041810310390003410040c3c1c41c0a180515041480da000d40111301419082c12400c40f06c902d01d003038407560344412154007030b8040d5800c2140c80381c020f0a6040244070076100c4029192000c0c800c0240544000240a240d110507607082c1001c85034410195140c0039008040d00d405800280900c40704d908205421f81a00860310052130701c107681c0700d006022203005040800c048a042100300e01c04901416028003015607561000304806100d050f6902e45403800c41c00c00740214050b900541d00d580f540101b12520890210b6240482c05d580403025641d5003580f003800b906c0455403540c50300320b29828a070070301c1036035101c0c940100c0c4560001400c40b040d041d039032034400342600c1c3c031841141c2d01604200b00501c81110321100501c240d9100d00804141c401c959900c03146c041e400303410305500240034030040c4148036400c003403244d00411045a0940c10010901124074191101910909440c02c1d21900e83d0116406500514000c0810710160390b8144000e0203029201d602 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 129832508 1250 129831258 129831263
    0x909010e0706051c0519020703050c060717010b1c02070303090209090303010524130602070311060304080a0804170d020c07080a0c06080406020405090709050108090a03080c0d02070b090604 83
    0x600e07501007211449801030318480b10003070501d016844003401c3d0110003414042c2c0880e9070540c402184043c0044a030004203101403080c1d481542e01d409000d04c4604010740035044004002400c45024031440b00c2d21005c0c0c0c15038254402c00e55485010361103c0d04000d07624240301403000d00218080d000e140d095030107103001d607000791480c11140d619a681303151207200901516601001c1c1240c061030100b49a48400c1007a102400400d1800201c4094002c02194580c003c6006a06c4203c0900400140c46603003a100941070740c0d42411800d15541b1560303076009220303842080011201c0002d047c8241d448a060041011114066440c1d00c440206400303036214141d07036101481201000205c6400000e440809603401150030800b190420344d048802e031002900c155549a004e01c00454540e944038032007801900c99446d200c214a142000140000d400204454400d0304403c80820109400840466201100782c0b0050b5440d406a200c480c0240a00040509002041e038200003804400242c203a00903070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 129833758 1250 129832508 129832513
    0x1b05040b010305060901060e06070602070c05010f0507030206010e0717070e040b09060619180b03011a0c0d12020705250b03041104051305060a0c0e010c050c0d050c0909010e 76
    0xc6550041d020380700b05542040e000300b105401005050720032040c5450038040104900d1030700041d9115a8103070780000f002510400b000d000d041000e50f8019154034120711182c1004e0b400c02001d41c0303000c0d458010500ca6030540307841100000e558188104c141c5040340c07400351600d42460411003030050085104c2030606000358903091020059203005c0584034400c00c00180400d2625075541c4950b03800d0341d2014446800e0061601e0303c000b03020000c44107000902805101641c9170340c0741010501079040d4000c1d10303602d8010204810705c058080450811142c3d001410145015902c5c00d07011002882515405002d50180100702c2032005540f44125210219481c1490031094650480042d1403000b03860040c003540601301d4481c010704058102d00c0e4060303407042091003120340c40d40310181043d00c22280000f41c0c69444240703a000e203811a000c04d058072001e00e41004108501e545050303642c8407254010307100302d40980d408000c1060070009000c040350040c1083d90142040b050070340c060320354040d0b0b8407040d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 129835008 1250 129833758 129833771
    0x108010608031c020a0302070206340f0308060102031e0d0e06010605070605060d02040509030a11070602030f03341b02060403020402130b190806030d080408161b0504 73
    0x224800419500e90540030fa00c0e04001d41003034420b000083d030280c03078918141a000d02000b409681d512024100071900300b1526481d0320301141103c01c000d0304042d1000c00c1911401c4050002c991869903c00301240d0509200010703403a09001030b451405415803450fa1254a4103020301c0c620b882038041e04080b00f1040042c80340a40c0c0c601015101c44e000d00449000400910580b800f041c00782e04442d40024000e40009285076aa0700481d09a0380101e40c1000c0c0c076800081c00003655035104080308600c000010117840401c0c14204029205d11030551480e08031200480400c0d040040480400210040c2c103c0d903914841a030500a84030f030744246400c0d00450740101c10680c0b03007414440b201910f158000c0c0118645429035007008000c1d000506014142c1000d100007081442a41c4014400030000d080110075004400000500140e0001c101c180660444403400044640080e0170700c2e0050342c001191611116401c021450503154a00b0107452804c803000d001000c0400d041074070003035130026102407140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 129836258 1250 129835008 129835019
    0xf24060604081221070c030e04140112140d02150708060901030305071b090209031b1e0111030a090603050a0e0c12121305090105090c0405090613020a02010501080106 73
    0xca00a51040308100d80100d181e00d4101c6a42d0802400002ca186210041803500004041c4420341e0884106010640205002061580109100445000896003441a0307401e201022034a01410f220b00f610f41d0440308011020003a0050b0000e24000780f0108480289040600013036542c2494261084c0b660300c01800f1881c0b00d842031045a00c1154044d0076010f06134615501200c0d640d01801d004d07036103440300102940c080e40c01c0000c40b1004101d21403000d0380303441d00402054241961020301003d101c110f00f082c0d65035515400030342400004504010580b004a410068036072601045440b111400001031003045a508004408241c55295900b002541d54240c02142140c001d54a0800343c0d078441080e841031494161981001c0440d1a4181d5440c1d600b41e2503030707410710b401407680d13041e140c01401c5042c0b101d030070031b10030607401400200d62070040d03428110700d0031071240301d41c2c000c0f01d004521a0300000d12a848107102c070340c4003410500b4110359504810500900802d420701071021554204940000c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 129837508 1250 129836258 129836269
    0xc03021207060228060c0c050c04060e0a090c0b0c030a031d1f11040b0702041a130c0c0209090a020114040506250221060a060b0703030e0f2406 63
    0x290380d041c3d0010200d100c0e00c030801901c0800c9802400d4100b10025032000006045401400c400c902540c5581c10318031882c0c41c11505180041240703a000c0c0b46032200c04c00141640060349600f00d000310b5070010f1103c0c19428004070008064101c181901d1001841131012200000108030071501070703400300002c00c1d1103240b402d03951015200c005500d42c41400c8000c58010400c038010f4500036040070015464000c400c00f401a50026072280201501c0880e0000640c1098013030b01e510342481030101070f0209020340000f4060540c040e0342c26059a540c3c107414a06602400c0180c45070342d0028502c2c5130900d02194025030314003000c00304a0000b901d407407603840300030010002e41d416141c1c01440c15041001d0030324041c218291500707420904801c01c845440c0507031207080118484074101044078444074088403080e0718026000e85402c0c03206162075010440130700d840c0260380c212a854a000701e000702880b0300301441c114a040c2405134500480040681c0b200010049107012601d001032902560303110020041e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 129838758 1250 129837508 129837523
    0x6120e01110f0903010605030d09030b220f110904060209120d05030604022a03072105040504020a020a141c08061e0a030602040602030d050a1a0402090d0503070c030212 74
    0x8401c0018840340c1c031046090340c00341078248800340002030f0032603958001a02c1c01800704950804581d50180c01d01c240202021001c1d8499064440420718010042c03803510503513030640001d402110201048020056001841103041d14020591205402e060034070070000d600210906220b40450f0710780c0352901c40e003c031b0889031504081d00d900303040d0354035881404060b50000b180d060f00710700c0d4003200800000240c2e04011034020721100558584400d031070041d2001924030100f04c2d00078049000030900c00d42c060121030a50314151005038540008903010392900310038584c003c14840b10f5402100c4c1e80c2c0b2000400c00c4a1a02140b04c0700020003001200780e0740104180c42c900e40100d1080b084021917036500080000262001d08480341a558030380b5004200d0300240c21040c0140c00024003090200864000c65400180d505010440702038802840a90524000c15080c06644c010654070344903510b491200d61003a0700581a40d030350b0100c600d0840a600410b0100328803030703c1048510300d0b0b24640020030b80d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 129840008 1250 129838758 129838781
    0x7080d0204152006070e03010b03060f0604061e0b1305120a0302010c0306030807060e0a02030d08100617070e03010f02070515010902040e010e04050a0c060c0c0608070e011d06030106120e01 83
    0x4100d1901d8200c003c40c2d8149000301001e406649550540600381c2b001c00c507442c410826910b200c6c072a4204981004152400c99121641254041e1505c011300262203d9440c00c417620420000c0e03595003284001d10395000035500080e0b2001001890b000d000c0c0002c910b9140e900e100c1c1e4003c02c80c01c0701c0c180080d030441d00c0303901004d0010300c411f010385000903055600c1940030781c0c101c0080707400a40c1140e001910f40030b21010040f000400c5801804101070300c0c0c46800000d85110300301440b200c40c100001c802112001841002001180039100c1b2568070207501c4209411800a8150741d201e07954206980e4803c15150108604282c4500000f0a00814401e440650303083e001291080e07440c0c213812401d4018080c00070f031600c1c0620a0060005964139001000800064546a0390800d00e410700b00b4044265138001800d100701001001415503002000004090003400c0c081c08200c01800f0025011440c0811076800c510000008201c03150809484460066116401c1c0b01d00032404005e0f50a0b609442100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 129841258 1250 129840008 129840013
    0x4051e03070312060f030c230105120402010c0b01062303100302060307260105040e01090b13050c030706020c1c0c0902070f05060a0e0c1f0507080d02041520 69
    0x4000ba208164003043e81da401c400c0803c1450b10b5013001c403030460143d44102d131107225000c41007100f180509800c081c201035800c543c0e80010036050000e40182700c0d008000303c001140e1800070b021a8080e00c991801140c00070103188042d83c545d0000340c250520035440f10b21071242080c44c07803582545e03242140d1040c00c0d07030010000300d035103190b0038840ba42c2c00c0034004805000031503c074185030000e038884420b1051600301e031240c8254501001d001c111400340c1800c008a0341010500c00220300103514a0343c00800a20026001202d141080f030300306862100820741c9070140303040000700340b80c0c0081c2502010004079007242600c0c500400c8500e01e9200580c00600001e04104208400101a80a003000384d0083c94401e020b03101c0ea980b0942440d80480300e11001b076585401001d2801e0007008400e0321200c00f9101c200c91180010301c000344009942da071580420500080722420020040c0a44202ca04500800e40d1155199415060b004004201120004820440b1000e0300000d040c494030403181c0c113101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 129842508 1250 129841258 129841267
    0x300c0d051509070801050705090f0f0f21120a090501080403020a0320010e1b0402210406020f0408060601180e070c030908100f050c0a020d031e060b0304051e03 70
    0x300340c0d06621000303100307002d0b500894600003081142070007200e1060100c1d40d04c0d0703590b0308542d01c104948028681e00c05406a200034400c1c90603903c0381c1c03801c030030281e03011a240f2800b151090007041046100024074a83c03801030f002c0c0d112801d40200c0107003000e40400d40f26031107615280d00044a000308100c42c0580160700018502c40070034000d80c2e180d403540c1d00708041c070400003062100c9582500d4210000c9400355106d416501c00d00c1c03a00030a410003400b0100c400358500660451196400b003010714050042042c61404141040b65503030403a05c241882c103048585803031b81c43e00c0882d11980102c0709c60380880c90b5500b00f4036082980e02956019503038444011000c83e01c4403502242c55401440c030031402e1015511011071604800c0141c003032170b10707049040440c908050720b0320002900d0000c0c1c035160304d084045c003940003650f4012510160402c2103150009003540c03030f46080e90742c103075801a184030040c1c41d0180204804424200561246025100b194000742d0002d461a001c20040307121a0000d070420310 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 129843758 1250 129842508 129842533
    0x1090e0a03081801110c060f010b04050f06090d140a0c12030503070f020705090a0e101413030c0605070e03151b0d0e0f0a02150408030d020702300c0d05 67
    0x4440041c43d000540000035440c6003036100e102d035540000705110700740e070016040100040400b1006405001103640c064280b500c2c081c0840c10000101a015114042c0441ca641e1a40c898651200304650403120b00140d071030540100c04e84030105034205468004810b0b2011418211100da81060540d050f80c0f280d00e1544c50702012100203486048140460080c4280060141e0340c0c00b100600400f501e800018002d0303102001c95150440243e0484142800d05100c4c11401e2040903003254003c001c00004114007545140c02c8484800800d0024220351a003400c0c4030b034141d4040c209840020040e411103583c5944003080000c101c2c0225085900d2026000018000e803a40201410200314804004960301900c0740f00c00d800d01408840c40041640507400c5d40045d80f514110200e03034461507540d06071400741840d10b02622840b0700040d0754401030300012140115101d030764020411111012200131102005403d400380d41c0c0b061b803131141c0e05106082d01c0c8001440c00e10350500d696644880108103810004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 129845008 1250 129843758 129843781
    0xc0d0203070c141c030305180a0506040303051906030f0c05010c02090a0b0102030702030601090905060106082413020a0306050a0801060605220e01060509010314060607060902060c07090501090e0a0308 88
    0x382143c03a00080700600300b40c01c070101c01007043c107901c0c0700e5100803c5510300400014540003800080c508264441422000030a9001c079089030030642502c1d005c035280c1c3d15030711b01c102d060f907006030340104076460140000288111074004008162040b04c403002c445550b140110341c0d000e10000f000c0c0d849034004011404203c0540e200c0400c48406006817070818100742c00190501c6000d9001488050b11303080c6241c200102807000b031b4050b01080c18456418100008580b403c10341e00305072021780164900900e605580c401c05000c5600d02c5896081d590b0355840080100642070078426503001d600c1140f804160600107019001c151003040e03440504041014801035036082c4800d5203034046d0625203501040202c28060458040d1050740c5405a030303040640c00042c21101072480182060400d80140601d980e6144c040301c02107500408042600e028500006002d48a0441001c60910505100191214003904aa812540140c0b0100402680020740c0f0ba20f4422544000f40080d012a002410640c000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 129846258 1250 129845008 129845039
    0x1501180f180b09060f0c041505040e01171209010c0206030c0c0114070e01020d080402010e01030f060603060512011517070f03030c14070326090d06020c0d0203070c 72
    0x12031004650059040d200c2000e030a1024015650680b9900c10042010420400c82d130f046842c1072022021840e040d0b040c10214040c50140d10442c1c0c902c00f580012451044054078060404000c02d99250b503524606021b60098104190100740140c042c2031118400800c140c1d80e80e8003040c0c4414030488805d5003005200d80c001002036015074800d000c40f040201c0d003481401e1034501c00121903540d07418105406024600700220380f40c11035001e1080042d003a0740c8500c0560f081582820101e900600c984010f030040c0180c0c54640403103070320f000d80006003642c1c1a00002c0803650706071440384116001c0d0984034261282c240c085a180c60343c05100304002c1381c040210b80160341c100d10075100c6450310754224107020078190f40140d00054051044d0400d00c44036000d0f9101450001004100d218a1030740e40385030011120b1460b110b8041d03001803242c084c1800b6012600c0e040c0c0010000340e0000035504e0a040250015a80043c02e846489550801107000000721401c02c3d4000100e0700080380f41c4803841175403050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 129847508 1250 129846258 129846281
    0x90c04150c05030406050403021903080a11100c0e0a0803180d08070501050f0f0903160303020a0909060806010305010e060f0105040b0103022a010b010203040b030402092203050408150118 82
    0x4048072000b198091000e00003410a565900f90350300d155004210b40801000d581d4940d200000781e0800000c1c01c04000c0340c00303480761414480b0003d44181c05141c1400b411b030640703511040c104040002d169a006140501c880d50440d0100085922941402d0383c0380250038102c130320030004641c1080c1314900300318400d09482c03041100615001d010703660345081d1141a50000c2c4050f6030a0180554071074104051a4003910400042d4285413003030b202e40712903a10f134400180600d6400a000510540710740e07041c801400b09000c0c01c0c05006e946550460342c50300e09100a84440d4a800e48101c960240030440d80e00982b407006486400c0d90078401004001d00d81d22805505040d030820084051822a01c00d00103060092186504c4414607034a5503401e60742c0185406046400800c828801044a10181c80c1c00130340594440b1a260b460440c2c2d0b4024503041000581800305000f188070815622000810645103001c0607204245102c6c0c1c41c2e07144494083c0502151440781c01c10443c40f4880700e500c036010041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 129848758 1250 129847508 129847517
    0xe06030a020d0501020408060606090919200d0c0c0308151807020a02100201050105060d050901060f230109050109030209071206150306081b090403020708030d050403020c090c0415 79
    0x80550300242d05406400c0040300c5594000c07404018105040c041c06d40c0c000c60580300c20307181085041c00524042c0d001020305200184060035113800300c44651107207404c0b40210b40f11310050392150140b0b0340b03541c104000c990502820141c1c4001100d228a540c40f50a0f5850b464502075600d03040c4a00207100070740722400d500a6004182111203282c0740c2aa00d00171101c64001d04410380c0b00d80144003070042041400e10a5a0500340100300e182c403808201c4960003042000020b00380c8907031aa490251882d81c0c484d046a00401d5000300300c50741341c0603c840021600d0810403081450110042d60483d01c036105103801b00b00090020005420104516944181146400856132080c860b0100c2258041d800c2086a01911301c003840e502c9401d171107888054206403004201c483d13003031030144d464164001d401c41d00034280b07000404e04150082014001414404055903200d04000e861400101030807142a001881030308070b8001c150030078491140c00341c3c10502400385820300301328601e00000d004503070040412 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 129850008 1250 129848758 129848773
    0x8070e0703021909050f090106201905070f0905060f010c0f0209041218051309050f060f040c120f0206091203130609050618091302120c0a120b010e0603 67
    0x603004124903040f000c0e152144a001800e000601407007414910301c1d2030003aa0b44e40014400f881d00401144d071419441d8032072440b401d01480c01d5906011040300100e00d18039500d04080c003041408901081540d884101c081351032596045c19809480e404d8a0440d04890a03004140c0310f54824031f10124160300400061108492550104050010895041d42c05040400210221f15808540814038003d102020302c1d8050809002907104c413403503010600260b994420301c2c0c0412a061040c40c598200d44000d40340f66240c010901c200650007150300b260400c503001c074082600e03000c3d04110140190402109039400103207500f0b0001071791042c640d0540c003102c41b40c145d0150007000c00080201d4038889241c01c3c0c2e41458100040d088050701e4100c43d00c210001e00c44040701000204400300449411035420009444080c0c07460407101840f80043d401030300e040300e000c4400c100001c0610051074261445044551368440074403249011400c001c2280010000400001c141a1041c41e048030000b420389010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 129851258 1250 129850008 129850027
    0x70503040303060b0d0506041d070b030a0603080409050415063203030403031106060307050d06020f0f0409020a180b04180e031306110705210703060c0203121008070e070302 76
    0x2160017158915118940780c1041040c60b0400e4090003281101094051141c01e1000c042e4544a044038040c1160071003020002030741600040e08481c004582000c40310b641d858075030203624003802046400782c508012104202c521881c20b40b00d440f0807125181c1c805104988143c0030410581c0743c4c07080d10030b9820080b9004c1101c55030f051004100a510985a90940d0307103180d0030717003070030800002c000038400d0f0007564040200e07403540c0d4100c0c40300710390280005987d004202110969800303900ba200140d2100400c0c08910103426900500014846466403041544083c40d0911140720340c1c0a4141d010340240001c00c002c0300c600c5400d21440c0c1002501003003042c00d0002c210700c1e5070001c5003410200445d0354030410160360441c803407020941845c00a8142c1c2820700700421008062100d0b541a0511680503401d00c442086c480400a180d01c902d0a00484105010082d901d401c0584840303400001030300030800b00032240d6125412655018098440f0768605074451011900045c1464141902080841203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 129852508 1250 129851258 129851279
    0x3010902220e03040e04032d0c02091510030b0303120a0b100509010215070c1209061808190c120b01091410030215040e16180b0307050304030306 64
    0x40d8400c05080e2012450300e001030000035102c071040c01c031019800c1004140151800074544d03075882901814117104040140c61590848512000068404d0400b60310400300c2070392082620080d14003c450768109501e4490140c0400711400700d035586d0103010040300000d003601036040501e042400400340c80c10300c19008015417405070304540c0024070f00e56480032104207207014140039100e2003091800d0381c2091694030011b99501e040041e02028410f40b60300140380940700301da180c40100d80c00300200c180c801c494000a050454a40101c00208403c0300300264650181c42c420806c548440004280040850103403103400010f49000b554032030352844001c85c0000310384400c0394001d88078584060b42c40d0b03d400218011241c04081600705960800240300805141e12046030941c3d4040780e41c582140340c404440c1c5414850fa03030020007240f02200401c03031740481880680c24910710782c0d151640014251003c00c6550f050f02e0003096541e00d018400300b01c2480c4984082e60b03001c1d1190600040040c1c9420b00da00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 129853758 1250 129852508 129852529
    0x30c030d0204050102010606021b3109030f02010b010206160905030a0312050105060307050306040b01020f15040209090d0f0f050904020c0d020d0e0f0103020706020d02270607150b03010902 83
    0x103021500000d04020f0f5507424030483d0001c2080c1d00c0607002c0132142209480710103051541e001d210700c2d03040e190604804841c581c0d03201480100d48644e0406070303008034040050403100000f036004c80e544003140b084c7c0318018042d510058005a01a0941e6904d880c6c2f0540d001c200026a0000c00c5140940400d103520b04200d034810180c000d4444503a0000d011001c0700a84105821460094100380180100c0782d07008819642c1008046a000c01c1d43c21442c40100d1800e020a0f4241e003aa01c1908081d407940c44030050840d00950082d00c8034481c66603080b68059a408280c64114005a105074409012611400c4490040d01c0d480c42d1507032409030703004000360980c2c00c0a1100a0140c0045010401c4581c04120301c0c28070017000d0038060203041c064000214510a0344850034181500003402c00100300d00e0fa8115100f01304500401c41d2240d02121780d0441508804c1c090f1a010008594503105078038082041c2c420103540300300e00700d441807440078600018103048903000303800d903485140c81d00040e503c04440c04c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 129855008 1250 129853758 129853777
    0x6020403061104090507031118180712050c0304080306090a09080403080c0d08070f120b0904050a02030d030216021e0d050c0a0f050604090903050d02030907090c0503130212030c03 79
    0x460b00e413410203403200e04407000a85844141482c0181d50300d8a051550195180c40c0b400c044040640d00154000c107101e000304030300c0e140c413100040080064841d04244c1c85941c24484610400c82580c0380b21040303449200030f40f40070744120340a0000603a2881d0803514158854a40500414000056542c00000e41c205810407201e540b000300d40d8004840007001810030302c101c1440c0455440c1814074028110704034101c55102048070801402c401c05c00710b50009494400082d05920041c030381420210b17241c1050803801c80c03080c081c1030a0032015610030300a0307403114103802040c0d031001c070003035400c000304e50022030310109590a1201040075607594115034070810600a1010740751141c500001c03c082c1c1070342500000c0c614244208188555111f060a460940e10312000001d201c0d819824141c030140a8016a0700005000004001102c02d01145500450720501d07802d002030107110743c09030f92902044841050107541d5041030809490045541050080c4c682c0a482c80d14281d80381260940e88032f01c041d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 129856115 1107 129855008 129855041
    0x1503011e0f0b0a14010806180114010c140a03030c0c08040b031b07050703030806180f0a15170616050a0f18090911060313020d0602040306 61
    0xb04030b51100c0140100d00c0d59680c0d0360010008400340f11240e0004100c0800700301d05051088680c0d810b0401c0b240005c41580c2010100b03110340c406040078a040145044402000c0b440d084120300100c10290040c0c01e85080c1e9041c0a400e80d50000a68410003200c0e44840d000f05400d00305560665403550140396a9072034241e00540d410040484103028048000307030003004c00c000003403a00100d07072080d1201c2d001e40d40c6040401400307807500c181c071508a44900001034802004068500c2d40f0410b0910001860444491004050101ca400c85116044c8800300c034042c640e410044c03170360b100500c1150f030328148000c000c000701280600c1250030144010078605220960055480c0c1000c8e107121012085100e9072030b50030300041e000300001030791f400201c1c0d40c0080741e5080c2401106d1081c900016200024601a802d001c80010844019201190b0034403001c00000c40500602e500015000d88 = true := by decide +kernel

theorem cover : BRFrame.Cov 129676258 129856115 := by
  have h0 := BRFrame.cov_init 129676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 129676258 ≤ n) (h2 : n < 129856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
