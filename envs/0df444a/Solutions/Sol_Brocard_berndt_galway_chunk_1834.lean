-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1834
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:50:33.213069+00:00
-- url     : https://prove2.me/submissions/2afca04b-1a3c-45ee-aee2-2d57c303cb51

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 329676258 ≤ n < 329856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 329677508 1250 329676258 329676301
    0x20703030b100804020906041811130b090406020c032b141b1605030c07090b0301020715050402181905010504020f1b1002070b01050102011805060705180a090203 71
    0x40426401d421541024445901c2607040746c0d528199070300c40001500030725003003030b6400051624801100400c420501000740c48042125010395408024084205540040b010079400c40580c801180c00580c8940103448040760401c240ea0402043c126242804401400c042000d949a0301955905204621445008881651140f2038070325001d6080f1880307442c3d100107201d1207480007940190407541c0070b083d01d07500396208090b20fa031410710704c59580d40c034400b90046414507407030000515030529051003290f140c00d90002e591002041480d5440000340300092040c3d800000d02188603d1085030015068032448200001c64044a440901e450884070143c119034010351040001030000c1c08154141d034602009403003100c0c000300300010100c2c10805400b05180c1818000700350360080204150a15050302c100381e00070482140c00e910040c0d80070485000241a079080800407804151080c40200900c00c0d002501c20311402d07040d404110015401d501040740f079540442402003030b00340750418110400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 329678758 1250 329677508 329677519
    0xe03130302100e0604060c0204020d0204060203030907090504050c101704120306050306041a100902070605014403130f0e07090b030604020702120a1a160503061e1201020703030b 78
    0xc12000c013080207442940103010505c03001136a81011955284c0440311042500030b001c0d03464039950803000c0e40d40e400599140d001030141000201e518044c0d88152803013141c21000401e40028203a0030710110140c0544098104403003540f507918561a03080c4030300d025900c01d042d802c03ca45c109032401805c880c482e410071031203904805d05000105405400d0105c8042030000c00340c1c0683c9a40704101c0b05240994042451540042000d2051044548c04a4101ca4400d00141503040700100300302c20b43c05240c100300c090304080720500e5007501103071204820032600c404101c901d03100300d90101c02040021580807540d00100644c040c40040c2c404000160004102d090a4002c00d0034000d1821850100404190081c0e601203502015555034a007141c6880350144280d035101308050a02506c0108206080204000c81201060320488001400800001140c3d152821034a4600810014010317805e4080030705807140c0050400c583d11640b9610b036902842000503555425854040c042d116048543e40c0300d03d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 329680008 1250 329678758 329678777
    0xc01141017060c18130504150902181f080105040507060f0516030509091303140306010f080907030204020408031b01020a0903060c140426010b0a0e0a0e0313030210 72
    0x42000111940c12030f000044a684403421200440c4051150726061a401820b4202003c541e42c019440f1501690051103032280d681c0c6c14003040c8080c0c421214000350000c0c06a1224403840c01801d980c1030b04000c042104400141c00462903c02c100c181d07401c00038a60b507454003031104110042242800410315814041c2140310502009891800b0b0aa8a91801503415090004062150044035518a4001c0400109051625204243d001d00c80c0048020440b040342101d00c6540d0b04007075030711610050703540303445040c40c2c00011282c00700050b0001105200c0c0c00404001030b621400608040c06100f0010341e25860a240070070050003a4030200d0040ea441008048540790744031983c034040d2600404003080032a500901103546000c0c00c1c071204500303000840c01195120410040c00c0c10078031035808600120003102182422a45003404803030f03025036510300800500100080c915400b246804000544040d2140c102d1b007075a10042075a040a8078000e03060086103010700565080e0106882c00b044c61 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 329681258 1250 329680008 329680049
    0xa0f05070f110c120d1814060f040b03011502060a29040207020d05010209010810120803060f280b0f03180a0f0f0201110a030206010b0903010204081603060e1f020f0c011410 76
    0x4007d0080035050080c039000440090850200c000c41e40200310740d08400da1b8940e90303034805c5100c500c60481c01500600840c800301711024a54095018400120075603004000c0003825851030442e154117006800c65024840c11015958400d54035081e41d0140c000543c0d41e05e0780e0400100751301c0300102a40390303946480c0320038071803258503a44401485a0100040380d9980729580015009040551102c3d404a8500c0100ca40308650304c0e42e00e42c03034922100b8514070160f10745003050308501039a11240e011910030300c0043c0c004c50b1140c00541d40c540344181910b04004131600e800c040c10161810540350807c207413503c41d0465078880b00507882c2800c40805004043c00555000f501c43d501171064801e401e0340414008010b541c00e41c1100c1c01402100115181c4154001c02c104220000340300a892103464100198007612000c03640880303043c60b0b94120b0400d21400346449000b500200e03803481195109100803044100300f40b10701203508100b405c1c4d00a042c82c1032518183e0904440e0042031018041c903809401 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 329682508 1250 329681258 329681279
    0x40c0e010e0708040606030209040c0801050703020f25020a030501140705090d23010f0e0d05040b0f03100906060305040512090114070807060606080a0f05070f110c120d18 75
    0x401800320f00c2e0440780d80d281e81c10801c0c05008141c00c041d40c070411110510080040e80101c0004492400c4000e000a56880f80160224082c00043c0303038540000304001540c5e001c0e45004501400010140300c03c1c030300c98640100300343c0310312a041110943c0d59070072148000021048880c2e0b01c082031740703401da2401c41320b080802c05020310400e005015a503200b2240700c0c141c484074010090201c8000c020061075640b03a00810140040b50160302c003600540d8201185988a20100c0d8150361a842d00545007001a071000c03003042e800181a420040135400003c209401107014010040550303540218460030641081814001080c80e848100281003064040c0c40e42c0004034000c440014003511500d40c0c2442c00c05525621a01000410152070044081421368029040ca03029102c0a40100221010150900110741e002e40781c01c4049656600c460008500c14500c00c0a15010341c0f0a462814090201003000f01c40c6602041d1920b4200e1203581c50300c00da02148007010031076800d40d2200020b181240020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 329683758 1250 329682508 329682511
    0x1080a180f0624060806030a0c26100906050108030a0801060f0516030504030b062209050f07091b1403130201050c100c12060e060409082506050124270e040c0e010e 72
    0x348030112051061001c03c030b05005218202c2b203440030307901885440800e2800400106004541040c40c12001003018200002507800c41e0301141c0300d015080c5d08018003521110200c20300c20f41008402c10000240d680d012041c800c25920a45401d5165410f524001e4500207005100602941d42100f4903164224aa826101622102400001d10001034100541000d01e141d00501d22442055400142c0f04240da004210b0f20f020b40111480302042c0200c00c54060180e1018100f6803034050004c01c038618203090324240010310504000d86002160b03c01e0724100800c00300e500d8100740d640e0301c00040031a001510a81c4900e07009004001082c2405410080c482010b0030141c00385a40300c002c1c0c0e0402c41004211103510500555550360204405032500180820000c22500541840000200c6034103e2a01045075145148000009813440200f101d59a62140714800031b03600c6d400352010750009000d03107000a000007990710340e42c0389490b0420343e0a48040b640030860556900300104802071030f20142c03a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 329685008 1250 329683758 329683769
    0x2040209030c06040803212505040315061502010204060c0b041a2a03010305190204060b04080f1c08070806060906120601080a180f0624060806030a0c 66
    0x40c0c5605588000c81e01d000000c04246400840004021544410001c041e120b11b44070440c681c0c003000080f14440f031490070103807000c0c1480c6072181d051a11240a032030080d611ba0010745800f40c02d2a41d80c2d00ca030f0140704032825009400ca41d481c1000d0201e000c010031240044855400250b1402e07240c10001008417810180c00b8100000c81d001083c00c0001c0004035040640f0400e020150740d05142403514400342080010100406914000c00364021b44401520304a0390414081c0461030f444404580f40051410400c99201c4d5840c0004640b034100365000e44040d2940381d00070496200c664041c586000280c2500d074092003030100c1c6804225500c0704205600c04128940f09205858801c04a9002c0c028003009680c8204041003d00f901c488429540b0711800c0b00766500c03007964035038801400443e000311095028a0b020b000980340462180c4a5251200784143d03000500031000903500007003081102403b400d00d10b001c8008014042e44141440c0d00104101c0103060008181c0e81c501903900c1052044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 329686258 1250 329685008 329685011
    0x409080304111c11120a03021501060801120201030c18060201090b0a200a020106030503030f0f0f06100c030215070203130605040807120f1703060315060913051908030709080303090a0204 82
    0x401050322041c008034250729245c000c46c1d407084002d15000e900c800e0252000040c000050f400080c0c031034450b40b03030f40781280d10701ca80c11007810100350011800b80483c3d1140c4410700244000046100080230200301c01081254000100d40203603182544100d18040c1c601482142032100c2c40c040a04084a1410300c00344010705141d0f501c014540c260702400d070319030010707020380004420413075500d81e603002940c4035441d070301c92040c1107540341c10084d41200c109460142e0014440a1503690880c0909150700915000b0b004a400328004a490410743c80c1045807004010b030000700d214145124031810b044081c009900b040f60a150400e070b00590341c0e000e41e100c0c007541c02c1c80345c030fa00c4414081e002c06c00f0783c2000d0704400c100901e40140804020305274415100c42d806440b441d00303240812030380280c4090140324002c12a15060316000c0824180c02c0071800d0940ba0b40c02682d500a11003040b0200398183d0b82d104100c0c0035102d1034003200240005015070f02c420303c260000c00400504100225210b80703c0c5074100d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 329687508 1250 329686258 329686283
    0xf06040506220b1f0e01050f0f030408040816080a020f18130c090207030903061a030d021605120607030905071737061a0409080304111c 60
    0x41c103028040381104240c4603540360001044582c0e9000b0f00d84440d02078411340100d44c02106075032090741608070181c0000d684d0314051441580f25000410104414141c000d09003501c04070100100e5006880841c1e2800c0000341c00c0040c00030901002104480140381028a00c0c54401010388401407048001d02c01d000030010b11b0030958440304454401c00c0c400d880d80800d460034201c10101c010441ea0b050740c00d8400e41100150742015402158540ca5040d5541040286541e45a402511b50a658008070000212007242c1f90344007008020f011203803550003080c4042201500004d62000c50b00301e54064200007810b0718101100242051308000385203000102034195003050740c01c00f5000c0e00244464051107810b060304a04c001425041801c2d03a611514900e40040c552900703282507501d10701e08200d247c22070740300820007941c4095480f400c074400c050b1409d0001c000083c11242e05110481d82c02c000441484180020b6000301103a2000c00d42d401100d000b02c07a1114110341110780c3c3c00805500c000d04 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 329688758 1250 329687508 329687521
    0x106050c0109120f0e0405010b16050f01050f010303110304151134081b100903020402070303020408010c0801140d1106070c031b0b1e12040b0601030b03060f060405 72
    0x50180358001e411600a14501e420f0740300061034080020441d200141c003800c1440e0359031a00d813082c0d0341264518803c2d40d08d40340000c401200c5e4800d042c2419240340c000d8100128420f002030140c00d120700781085000c1c100e5030542c50054000c540c0000305100942c4244800d101032600d005440800c500c00e130414800080610700010b15000000d40c04c48401203c42201c411498138001e00e2000c541441101c41a115403541421555442c1d26150001d907c80c48894803c518100b801c0704170441c4050b07103804414681c03203801180903603208a03800c0300060380c002401c029241d801e10440894007114074000900303501d401c10040e650741346d01b0003091107950403015034800c010b50424800c0d28810082c1115440781403a04055560000c288420385440420401201c42d5031190b003050016690070001840c10085800c2c0c21145464860300803503078032002044120409503510310840c1c03203144030788410103c902d800000182070b1450300010a010381d011000b40040002c0c056046603015400340c40c0014980e5400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 329690008 1250 329688758 329688761
    0x10e0606101e08153a020a17030c06070f09080c0307050108060402040e190b100f0302180415061218020f030a1707050c0d0302030720040c030519140106050c01 70
    0xca03090f07110b440200f0002c49600940317681086101607081c01e41850243d4a20360400102d040c1000354005d40d0104144688880d00303408184265640301140d04200e50b81280c2071508005a4110300811040340070380b0383d019032200b081c00c0640f04040281c0710208482000c40d030f949060b0b000d124140420100042c0450f103c5a050310010305407504049198244071175091a80e00307004c40303038007000c500340001d103d81400c100c003281312110380e00da6a190441700b41d880124005d42162001200303040e1005650301060342d807130084210452807030000b104420f1a01401400f0084003a0b6881c40c00c90902c142d0320406c051200c5140c2c03580b90140ca09400804200c0c001900703141c90040b00400b121003444c03024034080c500b20003400312140301d0421038110101c55400c000d03180c2115035000700180d004000400001342e00081c40d44080e110300401070100256203000400340c441e48014a00081d0740d80007000342c0c0002041400c1e49c901001d03102001424540400c04c0107031a0305000742400e00c01c0000343c0c1c041c0079409 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 329691258 1250 329690008 329690041
    0x1407140a03050a1509091a0601200309100806040e0d050a0507050c0a0e04050d08040f020f030c03030c0d03051005060f070c050d080c0c030111031b0c010e0606101e08 73
    0xc0220a62080d4450b9103217401400d80400668032000c05881a1b0320808040741c2007809000d0503184c203284a0813038450a11a00310411a50507540401c2c040100540c0303400364600700408203030300d4081851400409110403a06030000c811800c1c1d22020a41c15120303000801c603981c1d07409502d02070343e9805c103a04006d40b030801d41c40c40468200b400804005034105042d801a80200e208000740d81c200510740034111a88030056034083c040c003000c514100c0052401d00e890003141003015050307400d001c042c400000d007590450007011b5060780000000c901e04a41c18810642e200c229203003a0305800e070400e0b001c1b4066010b4040e900c26014000101e4000348191482c0c0c400c002d0074020b2804001c02424a410841d40c0c000c10008a01031080e241014240d01c0c06019115a2a40f003101c5142955550f80030081a109944d10707400418100b040680c2440800b8001c40c2189401c00c00140080d0a0010030b01400c01f0440c1285030800400300d030110b00d009a6800d40311105a1545031085160316842064410b2440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 329692508 1250 329691258 329691281
    0x10509010b0a1221051b010507020717100501030809040609200f04090608010f050903031b09010509061303030e10121d0a030f030b061303140109151407140a03050a 72
    0xc0c9083ca100c2e84075840001010035050250106d110040309a0649003a960156545405070300310500c207025502926a9010210400c1030407900800c802c03017011021103a007a00269007405000614042c14105405440018120483d00304540901d031000102d941c594481103004209000403d4441d04190100755000f40c641d900c010450b090b036401d9400d00900c10247d587e800c96080400154440c400031055910031030407402d0380e000c0d45045600d00710080c2d1013200118188103043c81003000640780e02010f850410004905000c2d1982582009000c543c04c1007030061117402e140c200324140c07550008078841e02407105174011800d031000345134052034200d8102c46201d6512401d0590400c2c940d10194500c480d070103d40b4100300d688544420f00c6003e100d941900122003054000400001341e0001400c00e0b1820040000104c40d1116035139400d400001078000c0740305a440340c9151200b50111405250011054280715220690750880c140403406842c465078241503448000a10f05c540e02c2d04800070504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 329693758 1250 329692508 329692553
    0x70206071704030b0f152e050417031c020a0221070c060305130b0406060b070b1506030403080612070302060d020a02011802090c03190203040602070302010509010b0a12 74
    0xd00361085101c5a0704140f0080e941e4001a50101d02070000524685000b54845440c0c100c0c015006400d01050303034002000700f2012900c04a107191940031680b410004143e0355500c86a83e01d25103c41240c0c84c881e02000c60200360810468003803548072440100355003104960000d0f8440d200312900ba42065a40d500c6c200c1009d0340c42d40701b030b801361086c00010096a0311420308403c2c95515010100c0403030703004a4030b405d0007140031038404003c0307907100488940c418410b890200391517880c0c0703001c0c03409030300030880c11101b080129060180c044480070010320081400d4604506500c1e03c0c0c0c6006101c00d9005c0c1c2442d0140314214034084c810f0b1020310500000e1500909003c4c0d4a000d001e00d010000e60015901b00b006520b000c101035019215070360100c07a03480d00181505c14036113035600414a6540050844141240049040c00320015640091403007580182801620741d51582006030964a00800d100c2d800d0f4508003401803036554400c14041502c07941a000703801c809042c5451100c46206052403010340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 329695008 1250 329693758 329693783
    0xf060518010608280b040f0605150c16060215010803160b0c0909180705011e030b0118060e01030b0105070b0c090411040807080f06010b040b031005100c020108090312010b07020607 79
    0x13915203400c540560710054070300700207034003004018a0480d14240240c41d4410400c42c01007000b01c3c203079009400700c440c49a041d11004903900e14200100c901d150b0080000d81c02c00c0e010441c0412aa654440c014001c1e40059850070f403c1c0261040002d18102c0000c229804076000300c0c810880b20800d44002b8203010300b184006003030003209038a02504400345048217115107800881c00e54441c84143c0e003010405d815000368543c1c83c440c180c0241100c00009410400344011100c4001c1400440c00c0c010441d6071140d00d400401200010142c0d80b5146c1d41d18140301e41080214005107441d2003642d408100520f0003a01c2d04000701c0042c001d0300c1c01d00e2070398031404070204d004107103c840401c00c0b000b01e071000300807030f001383d0a1040e481d6243c80c024495414809014041080400a1000210b0b4490810b043d1608040c1d11000002c0d007044500c070640001414406184c411541c1000203550065110002903003031941c0380c030040d107014a0500800e11074802c041111011900e4120941d410b032940021028100f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 329696258 1250 329695008 329695081
    0xe0f2e0c030f0b060a020c040b12030d0f0f0506030c04090507050d0b01180e030d0c0c06090803150a0b071b09050c0c0c18180a08030702010f060518010608 68
    0xd802c1d505045500c05191040185003850500221060039260317030040c2c4002501417003040020401c1e0140190000100d801802000f08140010449140800d0b00000c180c1c2c20220640110b584249000910b5031030310060110070b540c0010f40000c48501110b0100e5212841d14260b418000ca507407041c0e4000020130092010054148011410b860110026001c1c1c078620032078007401c1d03801c2e9003107404c0c00f0b4100b0400d9244900c1c03e6041100c0c20703880ca051080000c0d5850341e07207104848a51100b82e800c0c0c400071080c000a0120040c2985441804544200000d0f0601030301c0003c44c420030300010074201030a20040c40f040b410001107001000302e0b0078204030301e11742a42d8a610a0b4002c0310109281e00807550741000502c2c080e0402604e02020440480d01a9500c40c03400315850030100c1c801802d80319070000040081c80f00d1006502c5040c0300d5002095802c00341c01038500352042070b000544241d8090044210300c244200780303c0c0c110351a903d806182900d610049113080c44c948416543c400820401e00c2c41c9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 329697508 1250 329696258 329696261
    0x2007091517030a0c02060c0c180103020306100f090b03070f1403120f070209060103020d060305070f050103050f0703090f0503070b0103170c060c1803060103050f010e0f2e0c03 77
    0x700c1d1100041c81d007100024581682d103074070405001d60045100c840e107650143c01d040028040e424030800071107900745601000501031500c1c5241c8900b5007640d0b040148114181800581c1e008400041900c0040d0f047c84803a4030045001c2c001d9030502559244c0100c01d65804101003030091080e03602c080313034541d02e440383c0c8203510418501c2140280320340e5070106030300450b072400c0362160340d8441c8580341041d11960030041e0320301010300342070b04040d02440040d130400380324070038031000f144200300411000b8a05110340103180c455510460525241200700b01074210420081540089603180c001002010f034944007021800200018250384030200b40a010080050b0030303507041c0c03406103d40c2100d50010210b000d841d8801c030744140f140c0b60044404107400d5210100070f03010704543c4000a000107941180030070f251102c01d0303009441950001d840caa0b507038102031003080d5074000800c0140a412034081c3d111030303032541444d0705a02d600880302c40664203c02d200c14400405030541034180040e52401d80d0040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 329698758 1250 329697508 329697551
    0x80a0b0904050709050f15060906071e060b011b11010507081b010f090305092101090c090b0a080a080a1205070f031512080306030111040303080901061203200709 71
    0x83c0d030315145c080801c051141c400d0b407162255200444290a01400c01c09111064000c242c8042d00b01400340054000100a0000c65004201c01c41c41c1e61045034041c20104107954021002c01e050180e61846c07441c80f00e040340004450740350486c21200c6440d10700c00040700c079072007410800b601100000c12121a01c0c02000c108407140020003001b1301041a4004100341121041c600080104004110000843c14419081400032071980c1095059030a407002c85421341c2c201d00406c840c2c810304010240300c800c945104100d20850103a80b9080c6681c20320540c5130766003048002c05001014040b4507840c0302071003a046c602c0e00a0394100d0a01650070050b4024000110004031040460704000d50a41c000c0c4c0301034280710407214080312a080414003915111070950020f0070058240d525040184d40d0a01550001d20007180b29a55460541c50010300e802d084405a400a0b01d071280e01c80107808c0406d030f01101043c4d42ca00110340c0403800042c03491445280070346940c001d903081800d103a0301c081035021094030030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 329700008 1250 329698758 329698769
    0x402090f040212071e0504180906022b0e060c0d0b1f1b030e1201060803030412080a060317030a0e1b01140f03040f1a10170a0210080a0b09040507 64
    0x140217003003200c81a02020111802d20009009001c2002001411218901c040b03000d0440080e9481d000c1d207410069a0000da100422041c4020101000565080d00512041200d4000b04070b0386041c20312983c1c071020b0140075040490004a220400c1400c01d41c8000c2c0c4000000304031101d204100729131584210110b9900c000895030981c801401056505505d00100e44d041c3e95511010480408000e00720780030b80500081c965889001140c2000c0c208000c40c010b0f40613000c1e5040780b4005c140010b02052005000d40c8826062800c100005515032444d900d80c0b00c00380341a5038403952074094020042c000842ca01c01341d8403407241003481110f40c0380d1010100403002c0e0313108010319030000b840c0b0b0b055104904028182135000c0000034049071030488c441031170500c40c0c25142c10002c075241c4031100e10002990b02080604030803904020856010302c0d1180444c8000c000b400807514150000340038841022008001d0000490006000d10010703449129005002004258039040a04006a8482d098040d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 329701258 1250 329700008 329700017
    0x705070303090b070c17070f0f090e070305070e0606160c0510091d040c0b030c0301060e010f02030d050603190302031305030705150a0210060b0c07090c09050402090f04021207 77
    0x104002420f0000c48440d25001418a981d50f4070340480300c85042d140314141111402032100102c2c400d0300140d0707404010303c0a9803240c4900d505144c040c2007140d40c0a40c6a05031684041410800520007003800c1e8101c1700202c00050440e41c488001c1903081c403440d021868441c90380b4061070100110105054140e90080d5030b14441000d031444160340003580d0303009a9010219500302e003849080710754101a44030f80305000c1500c004e5640c84001c0c1160308150768180025030b01000500240b82d10040c4e6114a003004d1078020310707010320440c0181d10b9100d1041e044441c1034440b0002001130700c0c20001c1440000740418440007002680c10002d480e5084441035103d00c9400080004840c91700007141d00c186d40000340703080c034601038501440303490394482c00480b000c0d80580f171506004256148160300040c000d0480d00744c0d5406d4400c0b02c0f24105030998022414003071925107030315552588402c80c1c205407107041c1e400680e900f0040c4001260300100b01c6003150f003d8000100b0300543c0c0402d00079640a01015183e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 329702508 1250 329701258 329701277
    0x30d020c030d063602071b060e0d080301120f08030a0b120607140d15060f030c08070e04090609020303220f03050a03120b0306011e060e1005070213020705070303 71
    0x39482002c1050b480030110504c0d12202e04900740740d40001454012034034240042c50b003035180da601e4080304007250b5442401c80501008200017900104807a81b8600708494000b407111156607203c0be60b02060082815087e5032556510070400d03012b2a94039559008540c1d45d840c1d10386108124050b219003110903024013444116603800c04400168a03014000a0b00c5106022949840300c1c05260000f010f0010000e845801e410644008481c1c024040c1c08555600104820300072405019540c038a501301080103103000c1000841644552080340480d0116004940c240789410442c0140042d101e010350701d80000944060b04224520102e000c25450b0300010a4403681c5a03800c0d1160b6406110140180e000042c3d0100080d00c80c00001c04030005014000038040403e03001310380360400036080726904540190180b0000d9044998000081081d4a000580c1d00a030701d000c60f901003841c072060014410041181c0d011941d1380d404824280070320000c02c640f00c101500303000e507840c122407100360003041d41b403070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 329703758 1250 329702508 329702519
    0x10b040605010c050316030909060e0601110a0209060f0102010f050f1008070f090203100b16020a08011a04050c0f0f0405090a020922180803010504050105011e050c030d020c030d06 79
    0x21082c52045402c0006141411086c401d440034100740c0420071030801c007a05a02045100d042e200b2603029058241100c549450044c001400303907204104528000d0b4051284400143d03101c0c0d6036142c1c04602640d8030754a0010210050f4003620000480b0302615050004003c010032840c05200d1040c0031045968820a0343c1e400c0c2c103521484a802001c240d800c8041e024491040b941c0c000b1a0400141c00203007540c180d0f240c103c91b241d5001540c0310701017070140040b1401986131810880b03000c1c0c144c4c94020094440b034802c1404980215201d013500031501c0300005815131281e030003614000e024040100e640c4410780c028000741544030340a210b200e0303c1442c02080410310280309441c80840d014103092807419034150504200c0c509e20400409076502ca00c90100031962040915240c0342c0300c0c10200d81c4a506143c00c000545105800050400045000e015002c20b175400500c0b80c00304d0282003040c1c1d00c4c00000d5030342d03080d403182d02c40391003180340000b6401c81c0305500007004102e071007030785801005001c6d01c41 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 329705008 1250 329703758 329703767
    0xe160806150d0b01121e03020c010908030a1d040f14040501050901021903380414091f0605060f0403061803023c010204060815090403030c0507050f010b04060501 71
    0x2c0041e148507035980050001d145a0003000308124001d12200b0124a042d00340c0980e401c01d481c100710b006030859000341c502c0c0e5802074a00d0000c0e00410010f07500340b01c0d0155000f40002c1081c1c5a45e0811381c1620541400350302c03980c0c844640d440d0440340901c141c4071000e601e1078441c9030a0360101e42541ca49000540102d0040c425224101f070102c024540b01c2104404c11000fa1002d01007650b0642000c0c60304030f01110001800900050685207151800101c02e0100011034150f008481c0d110441c550401038118400b0450401c00da11621006018007200d81000c8000c000d5a001160807050005020001c82c06400241c0100ca101e0f01e81401004501603400304140d824500050150340005501008418088030500700c10a5000000858611404450b1864910341044022076540018240843d903030117420a40d005d860f02d40425a440c0030343c0c0c013240542000400150030942e80d158050f07402da00ca0412111f81c103070000e04172440041d803c40100c3c020070ba0b501450344618580365000801e540503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 329706258 1250 329705008 329705029
    0x3120206100501050a051207091401050403050a17120a05040209060f030d080a0e031306020c150409021602090a331707031205030708060108010305030d0e16080615 72
    0x40071440100d24982401913820750814241082031180074020300400c9400303840700c0742c407500e916503c580e482480d14074140a02c6a203a80c4540c104501044240080368000903038021031917110124000884405c035601c8410300801102c030303540e000c0c41800e000c0300101c2504028099402114481000c2e2950000c00104c541d035004196011b03080a2810408107010b411107560102210601044080d845a10141903038000d0080307082c0b1f0030f00313050184003882c1d0400c01e2007181c00d029207240c00b106042644094050189101d0192160780000301c852034881d10a0002807083d9014001c0741107402d08040c094003400d81c010100e0f00c82c01c1d004101c0e0030041c280c02c40001051165003100d8610703508140c46802c0c95841402c852003903100e01c000010014202e445100610b002c2c65940984904017408002d258950207403c00d41089102d0380184007046020040390480b8503c101e0000b00700c00b02c8080d260801003e024100813188600000140204003c503003070388502c15008052002601840810001014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 329707508 1250 329706258 329706271
    0x60a03021818151902030106050f0903010612150f180f23030a030b03060118020307032c0c120705090910020f1207021f02090103090f05060103120206 66
    0x6100c41680901074828100c0c0c1020040c50000c5610300708940e6a850409101c0b03403105040c041e9020000000d05500d1300d4100d0442d0b080c401d41c915450400000c1007402416190402c0c01c1c00021210060780d825441038009042c9040fa0341c45140d281d090402c0c1c01748480c2c0c003030320700142041c5c9140d00b5900b580c031070807114400b0460060441d51a985464240400c030100403141f9034509008a44802011520308480e600c019005503511030780341da00182a61341d2981d01900030780c0090b00621146559025121082c5004400140c0342da460003412405801c003801220400303061402e00c100442051041074a204210304100d8000c0c088170411710060b42101c43c1902d031170b6081020103014924041c0121508100088212210181020307060307022680021146260300600003600b01d203085144198560101981c00074104110b0040f440800c2032000c20100c02101c0c2d40000c0c0c480050380284e12565140750490700d9105040e0325880c0c120b80d140da003800103944660322030031a648114030008480d4032174013 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 329708758 1250 329707508 329707519
    0xf100203090f070810150504020301140a060807080103030f02030d1109041103040b1302030f030a170f04050d0e0a0801060e09011404081206180901090b0a110f0307020703050d0302030f060a0302 85
    0x1000400d0030300141b2445511518540c131680000844da5a280060b5020341001d400603c90442d501c410010440d80a51140b02404166010080c0180d003007001c0b20b04403901820044a00030a41ca001c9003144078183c22454513900e02906200c42c4600e1001920450405503401c1204e00c054500078040c6020440c1e00502d00c01e50940010415032a0412005500c0c2c03000c0c0032240411400d20701d8900f9604003108000c0000c0c2d0080c044154021088030760b58000400e90300441d400e003026210691600701c0c0e91800720a201440c00414a20b40303558010000802241c40200009074982d0a049880041039540102d0b0b91300340505600f01c0980a90240e004a92195606150030f01c00010484082c40c010802caa0062001040da8000c24000941a1041c2007030000000c5100f12403401c20740c82c034030162802c0b8a4629150000b0040344030b080842e0012800001050340700d03500e0150403072501d80b03d5000100380e801a44808040690540c02450061014403800d0b00146d07541410301601007440d110203036000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 329710008 1250 329708758 329708773
    0x3050d270b190201020c1b1003090b0604150b0c071a04051810030803040f020102011d0c0d1403071a0a02130b07020d0516050102100b03120307020f100203090f0708 72
    0x200d058a001a0110b41070b0001500b0300d22015505070910b0f01c901d007031301096040c18551144920303042041c840d0800c56414100300d01d0b40103440710045400d0051000c0d005503500c0c0c003020102202c02c00044000c110a07400150b98000211610b919950369101c1c0ca000082c606400500041142c421341d000c1d50805800403030000100d042600c9035802c0500b0001d040401c00e00040045211200158452806150101d0f61000d85200090841d0381707011403108034000d81003c0b0600c07507030081003050640e20b08549111a183c080e00b420701012041d41070a4906210005007501000150280d021303a440030030901794203503a200710220701a4800d00f2a5001d0310280703a9010301511010700302130004940090201d4070002d042c3d65820380f500d00c1c0101b203101da0000c0c100b0100019a410000300a134156000414070801d9092400710340d41d4000007080400303080001c00005d0304103108000078640000e40740f0498800c121003050345402540280d4140040b40546284005c1094000070b010b002c50f181e0000600c40c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 329711258 1250 329710008 329710027
    0x406200109030819061e0314070302240904050405061b070b041e050f030306190f120f0501020a08070807030c02150a0207080d0609061502030415030603050d270b 71
    0x480001c03880e14081e03a05c01001c141080c101ca10031030081e00c01b4840100047c1141002040034809a0b10030034560b0101c0401e100681740d0b080c070b4450407041c0ea00302010450701451460840c2c010300b00443e821074039000400050080006299015400d55428200f11002007011507080c0d110f10300c406803d0382c8507440810001103402000c11000010600442007140d070543d20103081c10681071004400c1e03400070090103003524122400e460f07480101d02c02c882c08140340c00b11074043c008461183e81250822292040284610010b0207444281c2c864000c40d5584840360001d03142032816662040010041b10009040c6e60080c8101c059082c4980c000700700b250b1702403484400c07032030006001c2609a40c0038001040010090000f511000115001c0890042c0c2022071202c2103c0c030702d41c04a8501c80340801c0c3c48920b0740e0080220740580346600d04060480303070105003d40c045c00040e4401481441610100d962a0344d111141e1002003c0c05503181002c084912603025041c40340b40150301c1d5054003080100302 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 329712508 1250 329711258 329711281
    0x40803060a050d06060e01090608070b09010512040606030c05060c1c050c1032040b070504050d06020702090c0c0c01180f180c14030604021e04062001090308 69
    0xd00010052014500c0758950010844101046604030f94068503620f041c46408100500d0718050051341508015082c60103040c5a615065486020000440000c181001d80d11910403102a81c10091001060741444d24141000b40003c1c84140d900c44140c0c00040703814541a4225045210441d0062080301101a082d01100c1440c01954091100070004644070000902007090301c18246500015000340380c084510071624510041d565005280f4807030310381e04100c1200280c0290b000b901000c16992140002e6416100b142c0000c0c0e40a02c4101c01ea90030000d03036400401150b4402d8500003040c0e1590368201d4254041c400320f005130380d0803100d60b05445521444c2c0c40c1c0400444160090f42c1507964140b90b40078000d0310741100080f041e880c6c6201c03600c3c1640d4050748020500510303020a10110079000300215002c041e200034496500005d4032007044000c0c2400c0c040300ca10700300358540d0703480d52034401401e891502e204106940c19842100c0c1a0010b041c4548250310b60585c4400350155207040c01c400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 329713758 1250 329712508 329712511
    0x5030c0a0903020909150606040b0a080903071a0601030b09010503060a090f060e070f0f08061501122d020c0712080724050c0a0c06020a020309030a06090b010518040803 74
    0x3007002400800040542d82d1120314600440344c860141c40c41c407404070705624028100900300c1e4042d00e003c0204005400340c420880d851200380e45000d040503244e0740030f4141180724040014083c3c0742d913007411011441031502c16034010482600c04001042c000824002521024030803280e01d6000640061040d80f519040b00549901c985d0745500d00e07903a56a00e05080310800c2040c080e01d940a600140700d201070400317921000e021013020069a052070400016076a4600030050f01e07910881400b02441781e400307007181d00d4100204030b4080c449011210010240040703444286000a00d181c00ea503108041184200c03100131820380701a0330000e042c111003ca030001d0a0a089462450400041c1c0100d40c3e03170b40c5c4076841c155240510444001c900b81e40d000a4a002a04803c00340b201001030143c002c1e000229804140d40c0550003507111041c0300710990031801503484440d018003c1420b5030040001d10380c00303d141c040c40340d0601405070340c8035414440441c80004c050091104d0b00d001041c0460300d40b80255 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 329715008 1250 329713758 329713777
    0x2040506130501031b05010212070318031a0f070c05060a0203130515010e0a0605100c080d110d0c050a08040f0203240405010c030b06072d050d030b030a020105030c 72
    0xa06105024403400c80302e09038800d913050044051181881c50200d01d18800901c030900c02000c002884c0b80b600181c80c800d00d41e00500784203200c0d040c200d07040c0c3c044910000640d00458074000c014400c805404600341c00300c0f9a10244180480002c14207800f8922040d000c5801c00010134a5988492082000b0350002d05a1010140820414800240d04200035151401940c04c032410a51502106400514000e019074544c00d040140500483d12050744170b030402d541d03503d402034902003642003203a00b602c10804c405441c182001c84680d00c20541d40014800144410000c11904031407945c215058015031840344002010780c030102e07010581c1d211484603001c1c0000c06850280100c0c3c0515040b03600f650000541d119460010041031110038070900544544904007406103011680018403144201c000040c0b61100e100c6ca6198009003811a1150f006505c05241014a0305801c1c8140e4610700c0d065030100003811f02400c041d86040c0400d210800942c107171111800c5440b04100e510700c036007282d17050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 329716258 1250 329715008 329715019
    0x5030d0f140c0a0c0810090206030705071b06031d030301080d080903040b0d05040b060d0b010506210c09130b0a06030c1101150807090e030f0c0708160608060909070302040506 77
    0x3140e020a41c00e00007412000d1058000311982c929126905060606c0d0b046c04030402490403296501584404046130307808403c0746001595000c4524100c00d8034100c2c03190701100d850840c6400b264260b0140e1044100f50a120050300e440c03e101c802c043d50740d1009018804040c8c024205500342e450080c1d00164211002606032400c0c0bc0c0c80e23079454031003138005140e454440d50b1107100b408280404010300540120007039440000440c1c5d1522051907031035040c0308030750144100103a440c180705203101c9140d48030320f40399064000d80d040500308500c25412007030701c00307201d80390500041d03000d03a000b0311035800700340009028034003564034100d4140e0040c8181e230440001e02410140203a0402001e204401001d44600c003190201820440e100e0719102045e004200c0072490140e0001082c80b0020030f50b800714203503086459550070b00c0102c0c141405403507070109259100e14a40b031541401d25504150541d0318941c1e0344401680d1f55410030004000c02d0764a00000e8001c1d0340b080c8058182038010030f5010380040d14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 329717508 1250 329716258 329716267
    0x201b1c0b040f0506040302030d0b060a08060613090203090a05010c05041406090a1706041103030a02070b09030109080406020f060a1416020f0a08040e060a0506030c0306010c06050c0a0905030d0f14 86
    0xc819007440c4d4201c1d001c90040c1c000150080c8134441c00c3c460001458000c1d95200c0c00c100f1005006015240080d2500b8401c04011800e020070100130000240a000700c0a400e544909100010307aa6882c400f080448055013400b1101c1040e510541c1500c0494030301d410361180010408060007142c3d8046081d03aa00012914000700b44601c103400010184158000203051911b00307802c1c00250b001c078210b0030130f2194004102c40218558000b4504050300c410703541c11540c3d4408400024010120190010b0442001190000d055900401c01e001629080b2055032035070341c2c072040c034041181c00514a0407400010301020503860345100d6000088003100b030044030a0209406082c03480c1105002c0c0c06c030307100000010b0500c0041c0b942ca41058010361b0071b440003038841d8105000034125001c02481d40c080154003100060740d03a84030340308002000c0d030041410030490070452002c503d1580200400c9000c1107002c036002806040c00119944a0556a41e41120740107102c2070840c0c010f09580324001c4c42703d100b0701 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 329718758 1250 329717508 329717513
    0x50607270303020604020114181507120903140d05031501180f081501061b0303060b030c030103020301050601080c0d020a0903080a0908121315201b1c0b040f 69
    0x2022540607600030b0300208040e01c0d00748001840e0501079004500701c2003041c44901c04203a00b850f121a0300d0b80040b40c03401d5031044003148585c000d02905501400320a00e03403d204800b140c20503807040540e80114001c00500141580382c82d55100417410400c005a030030400984076081840740468030200c145415034402c921060f0200d4200d07c0d541042c400380c0d148550400c901002002210040031041c64038034460341c58010050890300c6042d9040341e600d00502c01440c10940300c5d40c0800090310612103c1754072801c0817000c40c0704540003400300720302070b618041c04118958050000f0521541510841502c1c00c0445401180650400f101203001d0080b40900440012030740d00c007034481c0701413582d12b18000c9854200741c0b625100c260000300810034000c12005500f1304244e40c5100c140c41103c8000d8281010250048400c4010b00d417080e00070ba40c2c03d48500c11118004145000880e00b840801a041c204a00401100824282c19000d2108010048100141401da6484d9100d40141c2e045164071140340c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 329720008 1250 329718758 329718827
    0x2040207021906020114010e0f1f0e01050f030a0c1e031a0717041e03120219020f0d2c0607030306091812080a1b0206010e0105010c050607 61
    0x100e491100c1c40c40342e02400d002050742486441e0796984444074480c655490050384600311000075001c03107245070460001074901d850140d825070481d1400da03014110b1650310789103d8a0310030700b0701072107100350102c0b82c0d400b009103000288405026001140b0008c51481e08100e2003000c1d0b540600301c00d0700b00d05e1380c1b400804900015000e02140403c0584956240b6060000400070110703030360030407000354466081c840401d5120440c10612010008200000342c0c1e0b81c20140c03860960301151040c0e039400003642e080015055020804485016002c54903d200100c080c1520707180c0801017100015a0000700036200f0b140a50001c0142868008454100b98000c000c518541d1000600307802090302d904081180e6011072050088144024a00d00a1489507035540d402520324440803030201700c2544003142e110f5017241e2010001d00602203002c1c04071400440060b450b0f100910405071a0a10302c0000074065001d10035001506034070002070702d80c966910105a58440ca0808030310800440c011420001d145013 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 329721258 1250 329720008 329720029
    0x702010b04020703030902090c03040308014506080f121e0406180e07120203071815030f060303021c0e1306180b03030a0c050f01050c0a080a110409090204020702 71
    0x341e402046c0400b003401441201000030703100c010202c20070400c1001203607002c4a00c0c0d040d20b0800007032417095440c50340301c0c0b200340c0d1784402c003490740180c25000c8003200ca0301a000390070304591900301403207031070344d1070800d5625451642c1c0b014115410041d544034004101c44024501d080345401040d0464851001181250300701e5084503010034210301c40d280b030448240c01440014202000e40c42494509a84018012504540007801ca02d0700840403548003801002c45c408180da8031510201034a9407180700840701000c020544c00031038540704003004110f16901580007543e4054004044240e0500908105082e0340c0e03034440c0030402406006891035880d01c168000d02d0107240c8004c2081820310801544482c0b131518003c505034035143c4a106181c5010003a242540054101260030310305905000d0700f0003009120320b01103940b9000401c4041c0300007102520a21409030742e590a19aa581e1400040702c800d80d45151080d2018002001782c55416000451411301c06000542080d05550126820707811 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 329722508 1250 329721258 329721263
    0x50703120206010f080703030e041109090c030a0c0207030b0601082505070c0605070309090e03070b0f010312090b030411040605180a111218190b01050307060815090702010b040207 79
    0x2070010840d60f9043c4d0315280250640348003511015146079405425048074101e564003481c1c9558141250311040d20a031548000d001c0c003c9490b81c03401001e50340c040d034000c944074100c0b903141038a650b01d0144002010801e0340d038040707034480e15a103070580107440005006002e80081c80f1910b411400030400c03040500c22170b070f14540780d1589a00551030403c1d91420980c028004110341409007102090384079049004a0784010b4000914103594802c00d8114850124040d000409540511a548100e645858100ca0140d1003e4601c1c1c03a801c1e1040703403449002e10504807545418804079020801800c4c05104e80752000f080014501c2d6940d0106041c440300c52991814103080b9000c100d0030219034040c40540c1c94202408a10b0114064230201307000e03201034550052900607502110400c0c208011182c0e1a40e40e0710b60141c6407011a00d06000040340900940c2e02034000d4481c001912401020381c207000305860207044182d03e059034140031400790f0040c0034604542d290400701c0000c1c0c40d00e10041541c1070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 329723758 1250 329722508 329722513
    0x9060604051e011211160303020412030c0b010501030b0114090a18050f0115020312040203030d11041809030e0f0315090102130b09030606011202070215180a1406070507031202 77
    0x442c1c000001d441c3c81d83c1d03e103030100514104070b96070030b50041c18004c8509001c016117071070703015a240f42402c80c02401150003103141031144100300b0041c90b4010303a0b00d251207072142404294030f0380c840b00110155100380030749501182c003170130303030807260b0001603001c0c140c0801c0c0a80000c0b82e29684848050600c00304a50807600340c0d41c2d071000e20a0788a44204070501401c0c6202e90707200480c3d9100380081d0761b481011400388102044001040465800344120780c050700d40100281b000f0581c200e02085a54028441d6003003800c03030784061404ac0201f500882030655090707162041c80481200c103010f41d015103035091541c1401406400d0000f0300e51041c070701c0c0c02100488001078950142c401040070540042e00300300d14101c0700f4440740780b2566000880c83d42c050710a2900341c4506042c03c014402a0003014802075010764003113900b901045810020b81041c900c12551200f0045c5e86c0310a125012000f401251f00b1452000000c03541404c210009202086c030440480c1c481d141d81e5159003902c41c0d40c4920304401038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 329725008 1250 329723758 329723809
    0x813060e040c0305040c1e050a0305011d01091e14011a150408031909030f030c0c090504051011210117060c1c090503030a200a0e0906060405 62
    0x78101481045400451414108018240307500c0744044002c040c82800418a400c262500d04500903403100401003501802100446440c2c4c50918041d08044c40300050001c0310350004065044140034001e03455400080301c100c1d280c03010a901030444550304050303488003041c0e21445080c00007407185160801504400c07121586c0342000300120030780402d8107200b04c0b00b8103000c1808400c6c0040103ca0308803aa074007001610f541e85c664151200ea01542c001b9040c10000c1c0101014107803c05070900310307213101b0b00c000004103440d010194101c0e0000c1e82c0250445e400400012495502540101140310030703441250308146400d01d001490903040c418500310740d40030000401140c0403002040218600342005080d081c5010b98441c2d006000e030600b0000f5014003511005010090780d030109404a8000081e030350703640380000080018040d502d640918042c1c8070340d240450042d010b800d803101040140d54a400b20302c501c40070845400d0011304810f6100204000010313944d501c2080b2220000e05054110052 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 329726258 1250 329725008 329725037
    0x80f1515250203060901090308150118030804090513030518030304091d010f232206020a18180b060c030a0804150605010f1b06020f0d0605060412030804081306 70
    0x1044e8015020b40c025a040040301030000f9000701c1e04542c0217419404083c1040c0c04a801220800003808070681d95004002d0302209200142c1d0003001070b03580d102030a02190700c604001800450044401900041051000185d140c0c40e80b004010403040003000c990030203444281090403107803031120a1120b00000e944020120b80213010b030a98010305100c080008681181e480038150f110340b12810005205040080c200c0000070703410700c0841d510141103522128035480c09074025404490100701203040c0d03000d110f10500d80c0ba503080d03055036295060407031000502041400503040c1599855405a0705200200c09000c0c100054410001ca5686040d0241000c2c00c2c0781e03805210210554441c642071040904c0113036009403554140c0803062418450403a085104135144115a201c010000b50000560000c0030301d05801810603e030745004200310641d87c07281004114800ea114807198684400c402c4808280101201540280901c0006290100954a4000000781604824040340000110404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 329727508 1250 329726258 329726263
    0x30703020f0105040b0f04050a1a0717010302130b0f030f0c1806061602030109050d1e0201020315120f03030106080a0b09100905090c120706080f1515250203 69
    0x250308100c40020003c504040c0c0761100003000003000201e02d12103000209040040c00c000640302c642e00708000081d00e20300708080c102c94034001d59039100040d1880a109061280c4021954101c9600a0000146542c8116250040c11208090660062400e012100d164a043c40200b1103540000081d01d6440350a20030405c07056098018841c1d40d101140802015850303103000c44091501d0044000c2c080304562001a02510307500500416600072250301800d5240c015003044615a14540d40c040410b01c0807104900302e0104603118910152400000503003070070107031121000140e00d030b8296030701070010580b0203245500c2a409000001c01e19010450141100d10400318040800c0741d2a02007410244640ca900b00198025420380303e55a0010400994003004507100441003e8254842e18100c524072540790603252280c1d0707000c0b0740508002142240c2415030365110b01040a2103400c50602c03174041c08600101044c00481c007001c00c100c0b034029947d0b1004400c2c5800c1c2e003c0c21095000303090344140f60 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 329728758 1250 329727508 329727523
    0x5030c061f0612020d14101205071e0e07051206060c06041b05030d050705010b060903060f040309030b0f061f170a0204031e0b011d190f0e03070302 65
    0x81c400c1c0c066000d901c0d000c00300108542120322a190199510590340703003050083c4100406402810319107280b255030134101e844140e1044031503060214855544070000130501c01300400003071640c0c200250900c4508000c060401e0f03002400c20803200792039214012000e9900303056501c440411004508000d01d40744000506501c5031040d6101404c15281a50103a900d68020304001c10350009403e015032140240d40c1070030700502006088506070280b04030050107580c0440425504c55003850426406130501c1d400315102c415000c2c0040c0105e550710520302e9070f14040a0012010044030750000404500441140750050381905030754003480c00c000b410062683c9400313224480d0004801d003890410b0f900180d104109403040188821150348582041c1d0007441150002820349003002c848002c0c90f9040380340304204902c01c0102c12440e90726014465030044403100e0800d04002c04400103815010700d14650046030852080c049049081902503d060383d804213882c0342964000300c4c80d4000d0540c1000342c1c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 329730008 1250 329728758 329728771
    0xb0f0601050418020c011514011d0904030507060b0315070806010c03080c090609030a0602040611061603020c0a140c240301032621060f0102060a0b120a05030c06 71
    0xc0345080c1c54a4007840007500c0c03c505480031568003041204a551080d08a00e0721074294140c1c2c0c800c03042e120810b000f0100d2461018900081200101c0c08100e100e4111108169200a00c0103411703541c0c44d81e0407240d560224808a03a5582c4072402941c0584040000c170340469040c10b40306000b4036004500074041c001c010411410810780d004940f0100c0d812803c0d49130000314414146031340d807440d440030035164816a000e20790035114601a800a0101c0e5601030010390300c03c0d5480980049000500e241c1e100d05c140d90300304c1c41c0d4240c0d0303424075100c134042c1e801401c0382400c0700180d030a101c019071107101d4484a0541c52014035005288405000d1170550f00350010210791301200a54103c12004280b000e000c1400020b05480131071460382111007944810551060035000074582d00e18102c03030070f40c0385088016000d100140000000c240c991030102224a5086410b0780101090396408040b04050080c081c2d4468010400940c1c2c610a00d40070f000c0e10821500420048d5511910510f40c28a0f146005006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 329731258 1250 329730008 329730017
    0x8040f030c14040506090106110a0503030907090501080313061209200f0d05061b1c0b10090503150c1c0b0a080109261306030f0e07060e090405010b0603040b0f0601 72
    0x4110301651b4549400c0c3c103450301c030310740081c29030220380b0360a14212541030042c109100c04001c210034402c0009514041d0350000c4000e01403030f6610350703a2365500d000d001c01c0c6c4910740c140070700d0034030000d4405c01c030f02c0c6040b141640000c155540c1e581c5910607000c80c1440f80300300d1201403541ca550182020304402c440b11034107a40a00c04070442c1c1e216151140006410b030b00b86189030a85c0c0000e0040c02c4001e81d103604e4118800030103407150941c504402070110704803850007403100c1100056000e00030f03c088000ca0703401034003610020721815810207004200501802c141501130202c4e40c03c580d1180e030b1603805d11565920004100200b44108030b5001d05a600100b500c2e0705000c55040069400001035090011250b050340b100046034031003d215000d020b0030561058040000050b0f00d07545a0080c01000e5451903081108407202d50003640c40d00958001c04000c04c070036025070703c07043c1803001e02a644940500000108001490001000c6a2040d40c0c1074170624006002c4c48803200e001c03c80242c0108003400d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 329732508 1250 329731258 329731261
    0xc063905070515041a0712020a0b01090203010e060d031107060306180203130318050312030718060e0d0303090602072409020913060b1012060506090d0f08040f030c140405 75
    0x103840702140309a001700c0c2e800002008030344c0404513440b01607910140d44403015081d242c01b045002580c40c850140b003995900720b00300000402c00311a1080343d040e25220031103543d443c0c2d1141c0a0024105c800d02c801c0741007010f4002c041128200600c10300c0003030301c1c280c0e0f80411654039145c2c1810524221072216040e841c4100f007400201c0c0001002c0100c801c0e81424429400003150ba080340c0f41885070703030010741c05000301480c2401d03225a030801540f00390255280c5101c0000c10040300c0b540346640703014940204034107444504152070000702c24032505104c1c0c540880c1d92043c9a6501d030a0341c10100c01240d030481804075986040b91203100c1031101900d030ba070040281c14459000190310b210081e00b03e4514894a1641d48140440c907009030410441c0505840303c0c2201e400303001022036514446801a1925041c4041010f00c0c0507011140c500c1c4004140a0040790b490715110604003d28134119000c1b42c041000103041031382c0d54005030086001e2a10a0500c41c030341514600702c0070390901800e00c180c1c906070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 329733758 1250 329732508 329732539
    0x702370b0703180b0f040e0708040309180906020c01020306010e060f27180a1b140322050307020f092404110c010510120c0639050705 59
    0x50595180d50b416151642040c0188006500e0780c40305608021000480000e0b0314603011042c00042c811140851007400807a512540e00b241c1d200e4003030740e00500281ca120000c1000c802c2480c181440340030100c0b00020038006c1ea030350301000c0303902c0a201010203940200c1086115a080302e2600c800c00400d039a094581015454011b94a110384011b15000b0400c1c0010400800005403c03a0344900018048840004580c2500841050220382100042e428511201c030300d0300911454106242c03107500c0e01e00b81d038591200841d81540005051100504010940040208404805030040c5009801855075200140103001d04020b84c000040d000e075041030248000b03d00303c15600280303800c580300315840c1c106005000034050301c1c000c144981800c5c40070410f03144c0c080c0e06601c445d010398110a01e08440f96610040c400c02000448006840304925001c01c0111a02941d00800b40e0070041c0d09220840503003038403000402a0204c00c11040450030511201080f20400101d00a44400c8403c40200074044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 329735008 1250 329733758 329733779
    0xc0a030215072f0102210406060b0c031b0f061602010c050405060a11010609050a0b18090604020909121b0f06160c0c050a090b030d080c07060c05070237 67
    0x30340d45040f1505030a840c001c1e048030b0070342c19601e8404800380980c031844103034014079140c0e130402d42c0c0a80d0001e25103c2c000528840d241c00703d40010181c080554200780c2c0480560f0407140200c0b096030741c42c0c001e082d011440400c061000c140300304c0c4841c961580a83e29500000c0c2100d02c204800d07801e0200801050099581d8074065403500c00051606800300b826809555016000e1580454000c500b0001441070005154118004015080e5111020707101c7c00c1019800e1203c043d5045682500400f001c03c0142c207101580750340c0981480108c405880e10681158000e61000701070003200709c5d11403800c015621003440b000142c4c1103400c3c0140046e040070312149080c803512a41c00024403031140d0b1040c00300032402807440000c000007400e1181ca0350b658608100a000f440707156034864001c8405220322035000b00c038a03601035245e2980c810700303242c955a900c1000341001f660031418000103100b40300040e641c0c8105002c40c5581011505000701d80c034500e4001c2c0c1d6041c641d1041d42d03c0401ea000380840c4c1e505 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 329736258 1250 329735008 329735057
    0x20405010c140115060203091315141210020913090201140c070e0412030507090b030c09040e100c0311091e0103020918040c0501031e110c0a03021507 66
    0x540c002500b0340689078098014400c45140b9500b0000c800d070002207064003c0090001c0304010742e24000c80a4060032105c0444000b410300803003407202e00308240300d44542008960001c41001d40302080010f54a1403003440c0145003a00e00e0308442d000075510b074007410704581c80c4021074a001001d01141c0001d50000c1d0058104c000008070748000450500214601002180020f08c04003210800d581081d00300904401c8140d4403c10100781440089200ca13803186c443c0c2811a201003d03040d00356140c41101c00741c0e40d4040e000a03a070254a03407074040342d44402880404d0501444400000e59824821406000c1c1c40d002414288018014017240d902390311001200260b10070205070302072032010854016070081c05030a218940240c01a0764055600892561083c019805103e02c2e40e100b507034420044058941a0319480c0500440701307000104500f140d00725000580c440f140413402c00168030740c0c862502d20508425001644a509500d4075402111000e0b0303080788a91506200d245540702420302251a07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 329737508 1250 329736258 329736263
    0x92107050303070c03091d0412021c031521020307050901060c14011d03070501060f050105073203040501030e0105130209040c030501091505070c05060c09190909030210020405010c 79
    0x940d807181100b01481001d1b200007030001c03e0780302440302c0005c103940c01546004860407200d1a900800c5942c0d01c0b400011282c00303032500b141241c100c1e070342d0244c0d0843c0509080d80c46107040584c00c403004941081e51420910203003400140d020041102801018a0410741c0d41c4068007400d1030304014000150300400300008580c1040707aa40c8401c040c00c03801801000e29884000820001c0b080d62075001e50044000c105050040000740f0100381c0b504001c0c81c0c403141e584602804502c1c200b21010006803100c00001143c44184d0442007000b52a04518030030407040d4880710b0483e000010280304079a090f00c00c0c5103000040a0003004a4501004d1580503810800000791040128400080070010a021040061980840288030000c80c528284800a2003011400e04c5d060070302c3c00041083d03208119401d00c450708a401003c00b80c462300d0300c039155a800314841d282c0004544000e158060f031548412300040c10304030000500031186040c001d08040d00e104198101600401c01007000e40e81c0090170941654 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 329738758 1250 329737508 329737517
    0x905030607200307080a0f02011413050102091201060f0905040b0408130306020a0203030109061508010e0a0b040207051b090c070303020306041e060501020f010204180b0303040b0309210705030307 86
    0x101c40d42e541a40b030505400401c2c061000185000800680c1005000c20320444e440741203c081d04510264240c4200340103490750184000d0005d009007070740c2000c6080f55030085000514080ca46000309440e4072030340d014056980c0d16503008018081c82107150000406010f0403c02450030103a607120700520001c0c4c1701400008001ca000500c458000048100866014400315540c200380038029440e84c0092244d44050ba1408100141c040c0c1c0e1449040d804240310340c2c1c2c01655a00b403181e01c0356841006488a84102d030345081030030850315035200805040303005000400448410a440c01d105240c9030320a00e0103003a070389050002c0401d9000548107010390505000d41c80343d031850013203001031600301d0b890b030203031551030101c0d100404003030780503600751002a400e540221041480c454240d03c19441031149088440d18022085030180e4448820381d10010b00342e270b10305960f0340c1840d1030a80040d564a0320a8208007450740040700801508540c0940c400308007030420f805a02c52a07140e010041c001d50900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 329740008 1250 329738758 329738777
    0xb01050403080d14010906030606060e06030a051012080403050c030d12020d150e060a05220506030c1203040e01060207030f030518030105070309060b2b140607030b010f0905030607 79
    0x103071150844c9000d84a41d4134011055a960450480507048500c0b003a54004d241103000300741d01d480790701902c00c0c2c4880644110300d1502c8103540c4000821006203500c1d96100096400700302c0b450952402e0070024000c01c0180d071100e04500300503040008078102c040c4694000745202400c0e6400a600103801c218169006807500400b100c0722010700520040441038610008000c6410f040d21000107020350b1090340c10280302c0e0785840c24805c1000d40c1400100b41c982c1070a07010b200901107a0800384d0f1144000d0141d40c038001450700400d0f0004040e1550040c15040440c0c01e0000e010a0f100e114010310484c8014490740785143c480b985903901542d000740130000c0c0003842c1100300a00ea0120080701001500070840c514000ca0010014000944203c1c4c40d6403d0405041161800d01d00700825002d000c00520718643e00b0511150f00f4400e0a44221071098080c290240e211000b44000ca21905180c0c80101c5c0f81710301400011304034140321003000700f80310000c0020f1090f91000034465910a1590030712907445c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 329741258 1250 329740008 329740027
    0x1020a030b0306091911034201150c17030106080f06060d020c011506050c0714181f061805090712020f090312090f03070b0706090201090905090d020d02010b0105040308 74
    0x1d10012000750380c1c2601c00c50f0441850701840005038000303024143c1d029009225023186a0441d03d41d00e42c011062404020014803880c0320108450b4052103041c01e01402c248180d949001d80b010083e081110b07a50004401000a560421951503014001e4031550101d440d001e80012428059040c405003407d034089600e21510b05c01b58042000208207000784040603076200d8004020740d020f402e8800300785c002c8500c0015a0040f20914900641c4000e1001e030f8281800102d642044900030443c402d6045a0405c070f100340460580404083c01c03c540ea51000c04598288011030a0410741c00903000302280740c104008241d0282d45824200003020025a0f0344041710185600e038010038464a030700d80103045003070301715000c100010500342c50107452880b04015128101600e07103606100d100c0018208010340400141513601c040b600350700c14103042005030780b40d2040c102160b50485030804c03646d102022800700d442c1c04100a0f03040c082c1510091059000190000384103008510004001c0f50022842008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 329742508 1250 329741258 329741273
    0x40305101503150c021b0f06070602070206040f150f05070209060109050604080705040c0201060501020706232b020a09060804050109080c0307031803080a0e03010906020c01020a030b03060919 84
    0x42d5000302408a001c5210300c030040090040b20110380140c402d103000c0c610400c05002d0a50a90180205203000d01d44024051007075541c020402150030340e908201307040041ea43c5d84060000303803401c1c800f503842e414201180459104186143c84c0c087c0211401d04040300c940c010210743c010759041d240400940c0b590001030f200c641480d04002e511102c00314001c02c0c9480c0018502c011940304076814061a4620380e400d80c00c80e4558010540141c2244d1014000107015400104246404564541d0144110700701004681c00200d000025942135181d021684a01c00c107890f101d502a4040840c034041d040c10001e082c4281030700c600002d1250300000501401001c0d0320000205404c1a160f41d5600011000191240e100800480c0802c115210440e030f14400f09529106680d81b01c0c1b90180f400140c1d640507100003600c001c4640e0301d0b64881070072070b000501034005000e4041c4402c00168580780045006401d540380e480c43c1e0307802039100b4020841ea0420003c0c5007a01400d9400d501d00c541103003814990b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 329743758 1250 329742508 329742551
    0x9100f11010630061826250204060e090c0114030a0c11030301080d090f06081311030d031e02120403080702031303051e01141f0503191704030510 64
    0x404036880d00300321011480301e6202e110300d09881800d6052a9070341c0d4903103590428844031031407122103c0134000c0b40031f289165100720241c404a00d2482c0f01c10105a0b002034290b503556085401211131580a205464000f00403003140c2040c00d00307004608040104104005003c000c10b41548035440c0c580c1d4161580c050034800f00601c600c00d00f80c03556076864007040e5903282c04002801d000a012050300050114040b903010066801682e51200162502c7d440c002600b503c007031007a50001b02d0312600707100300d66040040c940c2203019910040348004110b881d15000071a1007a0300f5070014010440b4031106031400584e503030701581c90305050740d03541c980b034100700c1c5903000e134109001001c14410341c0481444800204292a05001440c03031400300c09010700f40c4d0903036910940341c0030100b040034082924061550901110072003d2104088031030f90b584000307072910113507502c05083c4a41c03402102c000d000d43c3d83c0e220701d590740b4801881841c00d49580d881700d541e5020f40c101800344580d60010204142d245c11513a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 329745008 1250 329743758 329743763
    0x31306150602121312020616060b040b010c110402070c03050601060e040c0c123b040b10092d090203090f0616080a0209100f11010630 59
    0x4004112825645403a00c0150740900c0016108000d01c00d08020194000c0f21007611200744881501c6142c80140c8260010418040364890004e01c100c03031201c0c8000304100078180c025000420b40d0035100060101f1164188040e5041140d03d411071400325080030f24070302d140c3c003003950010303a20101800c20132a078000c0b40c0c000074aa40500d000016030580c1c42001c00300c42c0401210204000c01218405482000700300700014920185440f50740d095900511442c51030321403805000040303c80f0800440503c0300c880e41c00a07105050010052401e0500c0c0c8181514050266100e0f594104111005014180c4500c40c0503800c000c02441c03441ca03641910509800b4005061190143c00d0b15081c58501a400c11541d18155111705960b034030052100140103401807070000005000c1e2035400750110341c0e0000080c044540650204860348454803100c0f00201d40080c3d030360364601c0c01d400362140207012205203810803071260304000040c45641911201540701200310311714004100d51b4034201d85403960100c0d030003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 329746258 1250 329745008 329745011
    0xc1209070b0a110606010305010e0105091b031305070b04080c120709060303080f0f04080a050a0c050f03070b0106050315010509040e0d051801110a03030b031c031b08150402031306 79
    0xc0010607800c070400000f0b0821480507280b140c4d541200440490b0403d100e522202d50605004210509141c8c101903000703070030002214080240180654501c1c1d0050f100c04501c0c41e1400d8011040c003802f4003103800640704e6400b080e45003030720f090341140c0e90b100d020340c020f03106001c1689019101841045000000c010072a01441195900d08028003410f0007290041300d46520580010751ba800a5112507104070342c0701d5005424203011110403a80c94000680c1d40042c06030b881542004182c0411603000d20a0030a001555145500c2c5448004590186c1c00076090200c2441031080b18603d03c172203000310b40d10a2a149490f44090000035010f0506415555081e0091400140b08503074001c000741000100c04ad040340c80540c6090045030f500c034107510382605a401c060b2041000074030a410001c1103410050403640712010201e10000029115510900403d5580010040380d4603405001c42c01c42805090030b040700e15144184d45002400c140466100329400400160502005000c2541c0075030003140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 329747508 1250 329746258 329746267
    0x10b181815070e0a091e0608160b130305062403160e0402060d020310060219150b060f041e0608070503060405100b07030c020a050405010302281805060103060e0c1209070b 75
    0x10220141c071b80403050344d103482c0c00c0c4640850b50800020710301d910030450703401e03600a488c600305d0340c91201e405c0800c4245000341e91120020103d0000c0103458000c8010115030b40ca040e4008021445034000a4405800383d0070100d9007041e5900c00076620000c0303034059042c0c501c040d603407880029030f0391161018001c4064404010302c840041804202802c1c4d8801d5000c07903031907520342140e10340e0060380100300404000d0351160004103240a500a0440c0c26400381c40d00c0c2c10f241c003c80091500f034002d6082001101910503000341c0101c50350150500805040c140f4a00c18100000010405d200090065000e540c40d0008110f8175001c002c0580024030200081e00d484410074a002030200006a4091744502d0f0100e60200300c51405102c1c00c2c0c1201e42c010b107015090004106060002c0a4a034003500e42c0c1c40d81d46c81c001805169203810040914403d140000d45840c1280024044074150780107044a8180002040001a128000c491100000341c1c04804280d803403000452421030560071002e80d0120106 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 329748758 1250 329747508 329747531
    0x40b181b0d1506090819020d05190c0e160e0118080a201f0e06030a0516020c011d041d030a0f08040c0603020c010b181815070e0a09 58
    0xa001c0042c00c84002003001e89141e81d030380202d480180b44d008440c16034010f190049811813100070140c1c100303440508002d80e04c038900d8981c1030a0800704481070000f56010740540d002c220909100c1405030818039049200760030003006480c0b0140d114207a0300144146080d210405038050500171000006264040d20f801c0e80741c1030301e16112442500c0890baa9001c90008840302c0c0d84949407507500810180c086c2c03507014240c5d9a82c1c10511303400355590061203400c804031f075419265000114071500b4550008295403c080c00e0140d0800c034844c48041c11074010801480441c0e9000310581e800d050401c01409035a03001310b0000e00105002404400110310b4607865012008000c005065546200c0d211007020f001c1e00751b000c2d0b5180a00320f0380142014003105090001901a5003d856034030b07011800051040702c108042152889182e11581e03004440808228071260703444000c00042075040090008041384615041d020380019040d0030510880c00d03020070440d1150350303420006142e40385040c0b01c021482e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 329750008 1250 329748758 329748761
    0x7140a03020c0319170313120c0212010c1d15071b0f030b07050307050f070507080c0301061404020304050c060708180a0501050d0f020c01020a0815040b181b0d 70
    0x2000414000d00901e19211400004400071110551708102c039841d000100800107001d40d03200801031800c840c000c00c8800045000f00405042100541d00e64100100c21030040124003032240510009030b80c140a00c44d4040c42c2d000000c180541007418080a0700500000061040c000c0d056420001000204412061000305028900c482c103458000040082e00e48a4899001c2140c2c003001c1c1c0004c0700e060100c2da12a1081004580c000d41c1d5240c0f0a04250162400c0e800785d41c800351095415034020001071001503010310403104a10b9048001300030441c54140841c903182d0308180355a100300d42c0440000c060203800c1c82448400034004004540d6950549440d2700250000503c0342d030303075090100b85200c050a0441e031600a90702f0585869092108103207850011303117540c0020b0118140c00b4082400102800d0014150328a100e03180d1061500c0c00d0030840c0e0803242102c0c1d0b1280705904241c9508207903151071038502041c8541d103049602076034410009418110010007048214080040e0440c4905000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 329751258 1250 329750008 329750023
    0x2309090f0111070c090203040f0f0609140a05070605130501110f060103031d0306060d020d050a0b0106030207060e010603021f090f0b030415110d0903090b0a05040503060a0e07030807140a0302 84
    0x46481128a43d101c510b018101c7c00104c400034000c03001390221202044074040030721103091082e200840c20803010f540340701c2c60000d91480b4592641c426003525080050074050000913010074505917041c1641c0009007014641c0382c1c400c25040c810300e002c0000d2114001c0c0500c2c1000b070f501400320360665030360b032400500c0392000c06810740b140105064800d440340340102d000d5000303210007170400441c14915001c210008404585c111164850034036003000081e56500064001d00751920010f0303c40482e0308002050f200c4130b124003c90342c1d00d440410b000603911006400301e9030b20b030710540100c01100c4a105032200b07201c607000540009001c1030001500081c00c0c0085110ba84501e0740942040d0400341084156088008850b179200c01c00e015000d4921030035440706a17507d010741703028940e0681d580c03185003856000001920004400140504c0582001c00140360401c09c0001704000340c80e0801d40305500e46656010080c01c0c6000014004180402080100010b0210105403081c804a514007c4c0d500d000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 329752508 1250 329751258 329751263
    0x1110102041a0c1002040501050706051e040503030712060f09022d091005031b0901170906010e07050a080106080c040b0d0c020d09030804090b04150806060a2309090f011107 76
    0xc0c0b0b0034801c104c8042c3d0b0095800b01c3d0010b84580d81004120360311003010705402002d20807407444a103004240354500400d05030081c0d0141002c2c0d0390300e007400e920003001b2111001400c43d13a1410040d042001049280c5c90788200e401c00f103801610351160f84260b8001c1c1c9001d82ca00f4400800c03401101a610076000c009290b1140211458125000002011740321740c0411100741480c900d0721940c440202c07007803500802d00110145410400b14910b101c0244980070103030f5120039642d10078401840103101014440b034000b000390401d9401c1c4482d00710014603601c014083c140402000c4400319040c40d050b10706440140c100100000d0300c270050461058028110640860014814111540481c50041240c031085e07d41001040e454a4200082030004c1c2c20030008581e04240c3d80c0440706021901300a0b103401406540014100790308006040141198640d00305000d02030031413403c0240481030b482008194181a10111010b58600d903900d810280306000c840b18a50a1841429034084004000d240310b03403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 329753758 1250 329752508 329752513
    0x30b060d1a37150f06030f140c03070513030c03240225020f1207090c080c160f0c08030a091406250203030f030a1d0c01110102041a0c 59
    0x214804020901d0084501000340c20310b411a405040c58401e500310780ca00c403210608100109546015000004425600a10000380c0d01c00d690700484503140512004a1500d1050b6003032820b001d00c1c40380081c4406001c48050120004007a041269280030f2000215049007241082c03680d01c1c1080d9902c2a07a00f00b040032690000d0038200d08000c0b403880cd4030451010050310380e92082c10f11048e5200c9000d20902030340c0c421340f0103505201c41e64034408034a90340d038508806003902c1c5280c961044151000c1003503910a1028150400c04140018015034110f1014044074034101d01543c1072088000c0000d040180428180080205141c200040101004462903841d03c00c690780e50104204000500020bc0758480410404050f6201018484540c0007642070751780341d81c0e1011a80000e1443c3c0c8540c40403821008044100613940015211f4400154542490884800d808070191a00ca40388401c80c941030050311501444004800d50566000e00510424400502c007401031080c8140c000c07000c40116132 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 329755008 1250 329753758 329753791
    0xc0b06010c03020d03110c06010f061202120c032203090816081c020f010c08070807030911040509010908030f150a1a0a030e0a030903111504030b060d1a 67
    0x1548036014045095402d90701428007015009804c9014206e101c0d08015201001d00000743e40003008d000803402032500798140c0f42e8843c47c2540180c50084800112091341d4410300611610035201c1410700c4d4005103200e035840c4e8a03900c00d42c04185620703c40c0c45a6403003c0c2c580382030300304154000c2140b03406ea0f40103030308880110040c03010215441c4014000c04080d9000401924041e101074840900460f4441c0180c07032200ca03a0704100c40c2151440f12255000498080500114541104190340c02010740d2030280444e04640d203030031403411071030160180a00c0c4d8440c00580e59a074290311440c1c640da44503210540e2801c00d40100c03440c13f0010b90752a04405243c0081600c01c1c83c0c030400f07520490341800b00100300e030010f542103603003160008194201855140c00b40c545800c2018041c3c210b046219071034481406096081000b58a0b2a1400940c018030f1402c0540c240811514250b4040780c3e0300116040503a5140c00108014100221009210040d00000e0b8500002c455104501c1041e40c0e54000030031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 329756258 1250 329755008 329755021
    0xf060405090a11040c030b0303120403030f0203090312040201050d0e0601030605010b1306110a230607030b150310030f051e03070c0501081308030a0209010e06040605160519030c0b 79
    0x1110b15907207006104194410b654182800e041e00b01c00166803060800085d4414030002090540d806018000c81103401a0208400c240d014131508002280b61078003141145051301409560781302c0c05c032000001e291201c0c002811a0b2050381107940c4100e40e10000d0150001d6003450036036810f03081c08100c8940e42018004608000a107003900c41005000611444180c070f801402e64203034007010075802550080002110101d040a80e110f400b80f50310401314590115904482c500300315001c2c001c6800c2505200e400b040039a100c8402e01c00000c041c09040d603481d11060103500c06140290f0004007001031003420b54003803000c0410709520500e104000240302c0b401c0d401e070990b04d0b0300c00c401d001402100b010034107210a51207213030550307440345202c80c21894102c099100c2408a404c102ca480807100c2d00000c0700c12107945c3c4810300114600c4191001d81c10103091500152550203081c10b03406803040349200d40d106000040188a0300620591f28500421080d03080003008500c0f55513003078559001503400f0403003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 329757508 1250 329756258 329756263
    0x2040303090e040c0b0c0309100509270a020d1d1501090204050a03110d0507031115040f0e040807140106090605030d0e04051521060f010b0316050f030f06040509 71
    0x8107943c06900d20144c10309001000c0420f0b04629001c04951109105d050115100c1a02207a541c0c1c0e02a2105620340c480002040311700d10f28150802913255000c6d40c0d495800b40501e07030b003540084844201580f40c582c43e02c2048000c1050710b02000140ea0f01681c80030b000c071800716942f03655020940000d00700346c0e2500d0020060740304d14441c540d00301001e850100003150f001e107400714112500507c45052040e058440380c0c9040321070b810617509645447c03680c0031549400d0703608124040341b0b080300703030304040c0b60000040c445030707181c881c00015a9240002804004000044452544d441418030030b0940040301014000d15050140c10f548910b0701c03002281b00c0c58001801e40c40750b2516038800342840c3c5184107000c017030038001e04400480d41034076000000035601d408130f1000381c1402d60a1040300d4065119050b20309200601601205840311005103ca1b04800703044a61041401c040140c40320740b210300444880c842c00d0a204440d10020043c854204200c044090052008407000d00c22900e8140c03404c0c0c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 329758758 1250 329757508 329757511
    0x1506070609110907021207030306050d14010506030c030c0f01050c0d020c09060d080313020a0b0409050a11030915041b080105041a150f06160f060f09150f150902040303090e 76
    0x240540d120803502c1c40f06c895003000500380705100b441d000c1400c40c0d6034004034110703011544049035200c41c26010354041a00c02d100d05a03024008030020041d40d01c40c03c01007038035080e2120003e40280014900800680d00800c201c4100010860454400c0140043e00039280c56580e82054458000c410100c0c0c102e280100c00e407030026400203500c0d0310f0768803801c103090480050078600300c1c1c0000c03486070001001c0c045000034000410030b0920100d00c034900000c00e40300312000141001035071300c401c0c014445031100029441e003441e0070449680b001360302c03a803c00c80d821800f510980c0130b00001c480000310b0300c0901908694000c81c80b5003411194050690704d078440c1000201c8e0141c600021440c2c3d480d4203407400d00d40025407144080c000780e2a04101d10212107403543d00303810a5175007661a2408104022641c843c50104151403041004004116501d00742030542682441141a880d09900394242d19664404000241c10419035944035131389800714000b03900644003e80100d24107880000b0181560701506 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 329760008 1250 329758758 329758771
    0x30c0d0c0804150f09080d06051503041101051809010f031e051f0f0504030302070326040f06021603020c0a14030d031503080301031506080d020c01030515060706091109 74
    0x103143c584145000c11000384080300c11804815160116100481c042e080102000c1d0404400855018184002d20400100d41800061410000c00c1000081034101c0506070607160240f078440c0e0303142c4d01d2202c6041465224540b07150301544407000025440c00c40000841124440c119000c0c5081143c101c01c4617000b10b880001c0c1250300283d03880882c511052a518106410603400064192003018020045501c103d03021004030b5400a042c409054100c48204180002c111a041440d20300d82c10039586490003400041116401c0c1c90400100801c0ea0166081102101e1005100035158200290f85a00d80e415081c0641a10b8502141c00b2040f000410041c1c44c001c1c0c000c1c42c040c0040c900440051a41c8281000e04204105d0040700103040d0200450003940550070105d103c0c1d43c01c080e000300302c55103070348440c1c01036001c4c0750711481c102e802064407200b0017024200000c4a82e19a803490140030340c9086015880034002a41204018003980203e59080c020740b600e40040c91028244024040180c448 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 329761258 1250 329760008 329760023
    0x5061f020a140a050a050c01020c12070909080c0d1d0a120209040503040b0a050c15240307081207110d0302030d090305040e04060b0f0a06090902070602040b030c0d0c0804 75
    0x80c0c00200b0610425000c0362092502101c625107201e480e2103061880d4a03100700d415800c004564203070f940e410402c040503140f084440c038885120b241940e550b105018070030400721036210000e440500c1030002c03c0e0b907104203041055403196960725000608400990351803060500300d80d95035440b5410305c0003080e410b5501505c01044003400039001c01c40d46400060085805100c00c10011035103034506801f400c040a0140c4035251610190034041d0709201d030405104054004c3c803800c0000c01c0318100449680611030202c00c0348486081004641403030000c1e040700c1d0280c071603603c4008400070170702c00809415016504c2c1c1301c1400c0440003000a0014000c03000b4005a106011402d00c2400d15401341e28014400c1c02c041d4503050fa60600303c40c2100c0100c0c0c040d40c80650355103545285041000010310207100072100302d825207080000150601d486400340000ca1580400c090041100303640c1180c014103030600d82c194aa04d805500d450301548001c1d0074a01603130506280b4030005004664040c01141d100c0e59 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 329762508 1250 329761258 329761273
    0x3200a1215020915030a090501062408042321040302040b1206010611010b0307030321110f0d11120402210307060c021501090e0c010c1e020a030b0a05061f02 69
    0x40704d031026007000d0243c5a01d555280020400240301b403284030010440c19031208a5a4610105840300340200056041813098003002c10002640310001c0140c90040b00c9402e4110f02900342005103845c3d12030340c40441801040741901c0c4c081d40b400c00600102d1b0300c201d4061060005400600c5101c444040012002d88d000500500ca1540902c64400c00d1817030140000400c540154000381c0b81903d1980183d012641b881075104888549500c000303044510030005001e000d41031a10902c40e446602c0780840310400105000b031682d0150382140091242120541c1d841c0e041d44842c42596480540d001c921a000d582071400c0650a0302a81d8241741c0d1070200070f141007948a88400028196050030402140100f58841103180d60404402d4060b002d8007030300040b2500f50b80c0000c0e2812000040090501c1480045000001d8403502c0c600910525401c1003014003c132480070401c1320b120341e00000e000513040707410002c00112a501140c4500c5044030005c400100142012060312040300d09000140c101c81d9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 329763758 1250 329762508 329762539
    0x60703020a0c06050f010509090a11101206081b090f0103170405040e01051501140d0905010e060c070201020d0c0819050c01150509160903200a12150209 67
    0x203026100324400d0b8140070307038000c1581d81c0d484100d9500b01c8002d203021700c0e420018002420a460420742c8480b1902c003c000b40d4895496960302c8070320440c18503100c0d1580202ea100070902c90701501850b00400b42d8103112060300c8009284e2202d0178003048042040060079035280c00e2416140d071340c2c001d200341440c100c00743c0d003103454441036214420300030003031088200710009242c0c4851040480c00b4408000000b800c0c00c0c03180b040309a02c1d1080140d941042050100c4418080c2c00608540c2c5030701c0c4842000031303c0c8440f4034229000d408c03034aa8140082c0134807020407100e2400c0c0002400007134800d07400d685280d11612026918080c0004000d40715034014001402981801e004a0790510700900300241403088100c4142e00351020b04803e440c083c14a01810405401c004044030b80100840705070b06000d00c005407000380a18114400038040403101180310ac101944090001d00f060405000490f407941c940280c178420b01180b04049440702c2d09103603424980c41ca81c3c170a071005600002c054040e0300780c40d030703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 329765008 1250 329763758 329763761
    0x3030f0e041103090c2103220801060b0318010528111b15010509043917011506051804092613090504080712030203060a09020903060703 60
    0x42041d0410b640d011041c9284121402851044403400024199400c1075410b1185845c0c4000c140458203032000b43c2c10068404c084140c440101c2001d00c50845035041149401810000c1c1c0d100e61819480c007400410701d00100001107111f48000c10440d140f89503114020f134203c600444220710207072094446e8405041d0b1558800c01050349076030b00850341d0781c000800b12940340d2080340d4010300a01138011020314114144240b280a4551a140c1501c0d98900004607403640c000610082084a4910b82c2d00041c004030540c0480000c00b0036804064002c441030a200c40302c005006611000c81c80c0c0e41101c0d00400140901c1d41d1f55010f41600c080540d01e0b191040e00d4542141c5901c00f02d201c3d100340c400410b0f881e94419003481900484030180346000e40191103032640d5140c00b1a6803200005c000f0b60a1200341545c4d02d00882d40d0b80a40020b8603540c0b818446614000c0e4040186640310608407800038a0317141d0080c500a4408841c3c4241035913880e1064000c034480d83d4120303a09034002c1400030f0800b80c082d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 329766258 1250 329765008 329765027
    0x501080c0a05070b07020105010f0e0f04080f0408060a02030a0f0902130c03020d0218040c0f0c021005070501020a030911030c01080c0c01060f03050601060e01110a111c050a1a0103030f 81
    0xa061990801d481596001d584c144101d03241300c0180c0d96a001045684031030400b0800805800b5144209800c1c00ca420000c800001007000d00120b000107004d44d0001d01c010f046034024200001690320758200030300c4480c042e60041e2160b1071300508004480403031403c03521a88407441c0c2c0c01000441d03030396400540a001340200451070802d243c0c3c244600021807449000420050580c100301414000b044c104000889600804403810010390f040e5980030190404641143c4540480e5441c664446aa8044807180700f58000188079500200b00c0005480e0035410645009228640744010460705600780741d40c5000403140513000030500d00c0400c8450181a0007001d40c043c00100104999440300a000401c0d0361315407003100c89071b00036001045003c1c0e02440780422040b003440c140781003aa0301801659a080703081c0014004015145401c04181e40f1307040e1030f01040f9400c24143c642e403027003420400c5d1a0550000e0650700c408081c262450902c09000e80541600e0345a12110003150f1981d2040310660403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 329767508 1250 329766258 329766277
    0x2150604020d0c020307050d090e0106030908162001050a020a0308040f02150403060506030303042001120509010f05011401020303040b07090305060f0610091503020f070c0603020c0d090501080c 85
    0x9080014012501c107a0107080303c0140b56030001c658840140c50002d24200c81040000304100f60807406010f41800c07200740504540c1c4c24038011607070a0a9040000540c42917104041c3c02400a0441c030040281480c405041c80558408200301c9516860054603540301d03003c082e00040c2c12088401001a026188d00703034000d17005000030141640f4a40c04104200d01e0381180c1d030b4035a080410104204146d40c021140e000800b0f038007031802c608095980481d03001004111000e1503c580c0d0040290f07074031030700003a00113000c91201030140c3d0a26500050081188412050b42c19041800104004040c0b1030001ca0319a0180c1c003c500e0750780c95895034070032800d01401c3d01040080d105e4000001c51020031007203010394180340030007145081900800042c0d240c4151480140030045904002000d402551011a00075506001da6a0301c080c002e8888688240500108440342d038510100345a64590b024080e4080b400f001c0302e1405029100030b6078a6502c41c8142800241c800d0005520443d07400c024141015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 329768758 1250 329767508 329767511
    0x1053001080c100206012d0e0619060c080c0102190905040b06040e01090e0f1b0117060901030809030f0a1b2306070f081206130603052503050f010b190602150604 71
    0x4072070844a4007e00d0964401140d0305440385c04d10400d481c2c141c072400d011902c03408140312858034251000d0034100b44000041c0101d5070118100c40c0c1c005080d011500c442150005080000b498078201400002c0b807809980c1c000c81c40d06a81d2034250408008840a40c0d03214500030980d0707807900ca00c00001d020003420303444c101c0c02002140e490040041141c0c600701412544003c05d40e1039a2000101441c501002d1204005030030380511420b0384a01098a0541c0d40155a444e6100d09080c013091030000c41c0ba40200d60307480740305901c0c0c00f0300803d107100c180040d984000091426a0707400500c41001450384410407202c26104c0e541100703107086001000344070700c036600307604c14849142c4aa41c05504400f0292080c5805402080700c1860500c115203071042500c50100921f90641e22900c3d698008418001542d40c80b12210f40310200d001c0305104000c59012084131084c020304000c0b07034044e040b4000c41501402182900919803c0e40c042d882003502d60341c1c0d000340f43c80c240c10b646003c503402003e044a600203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 329770008 1250 329768758 329768819
    0x30510022b060305030403030c05010b0405010501050a180b0d0603051506011d010309020a030807050d081314121306030c05091305060d020306070320120601053001080c10020601 78
    0x2c1d03024400b40c4003c6004c0d80f01d000d0072752480d0500341e0035115a44040b038840d624260050265a0300101952451840c6180400510180d4100002c84012a03009250b44038008a8a048101c9580d00300d00103492054081ea21560701008070421440c1c070a54480d800f2401c2c81e409070280724414203401242500500d404204e401040c4c02050b00842030f600140c403542c00004000040c00341c1001a8541a050b5242008062422001106035007541880051513401c20617045a00c00310100170a220400c1140c03001541c5051000c100e000c00481c6100301c10209061450380515a0300500685076102c0019003001424190300244a009110003081a94450190b0403805d0140e00c08018262040650b901c00003a1010158095034901e458007541c210010400c0040203802c4040a14554000b042824400d8807402c0803440c04802204400b05103034019060300ca02083c620200154a04895010055031031079841241030042c4140d16529150259110000400c44080500c00070300c1c80d091244004486d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 329771258 1250 329770008 329770013
    0x1122122405040602071137080f01061e050303030711011d100b121005182505040504110f0103090219061b0b06040c03020409090b01030510022b0603 65
    0x45420607a4156083d0780e010030840d041080c500041e841c2903c00b12240140e4103410844c144004140021114414000358001015200041c009030084e10a40c2d0503580281c11500340580205014410105089014101200400700310041402920f101402841c44c6940f0000d05444c4042130901c2c00340d1035907071500b881c01c00c01e01d100140c0c04010b01c00c5014081c5000025660029105010842c1d84944644080c5000704440020200e0703120385043c0010446a895400421580191905d90781e01c43c05808401d407850100b000014074410320b84810340880d261214207110440c4c108650060200e10403031045015032618a100303450341c810515020544905d6076001c507014903000002e50540840c001c10070b00000e908884940480120304820180c3e1504d0360b01c0b0768915000c0505007e0003240e039a44214059403003070301120083e1504a07810f2000f010580303003000295000348400d480600612445440c0c0d9000c2d40200c070b4a40d0100410108201010840d80554005c0c0c0d1000f1644e00e55240b100100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 329772508 1250 329771258 329771261
    0x1110a0b0403090602011107060b060412080403061a0321130807050a1203050a03020306010306030f030804420f06080307060c18060c020a0911221224 66
    0x11540c460100602242000d15019008032855000700c1c044d641031030310a00074100b0107015552419000040401c5402440c1c010030801c0c0300315044004081301e103465400910490707000600481303210b2a000c004003056040504490300c40c401249509d85c000030000d0107604c0644c82c0d9029042d040c201e03070515045000d01150980503003075020320500d40018004116900c0c180d11801d0050084c8034002e00034500700d540062152103076080107014160302001140340c90340700c1d50040000d1640082da2242a4200f410094123404003150202d44540c03161590140c0a0891280182d40d0f0222541001d000368003609003e003504402c0c4203400c016a603811203015006114090f060060424001039580d0303042c141000c00036101400c41d043c0c280001d0183c00a896202c0c210030354200c1d074045c0780440b00c182a0b8800600b800d01d166000e8030f085030034401e42d18a0701c40e40b103000303141204030316410600c001c4000140152140d01c600c54140b0a038402800e40c1c000c075640c0341c001520b00c00d05000c0c0c040d610240090000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 329773758 1250 329772508 329772523
    0x507021015090b0603040f0b0702160306290307091d0604060903020f12030105010e030a02090a0b0a0e040f060519060312080c030f010306020c1906020c1501060f030b0111 75
    0x7003a201c0000200100c040c24410088003241c1034450030700e1481c064844408940800100414204109001448441c82404801e4503000207020901206a40e400d107040030f490104000c9801c4400411200340610359920341b11510f0034041c026000c2c032460310508000401c00200540c120100401040c01e002c2028420544150300c00c480001d80e040190500a1411702d240542d201d0340d600ca0349002281003018000c2d60704481091a010550321402c40100c0d00b004000c0c036009402034072540600c68940c515800103c0c400c00156022070000e55900d440505103502a0f5019003080015102c00c2c011a034240c102e135911580151603010104c400c080401d04803002c5a000b660403032002d80b851400b82e0307170001000f41c10000b070600032800c60800034116102043c061200520840d800900320f01f2001c13040c0289801003210700c500c039924211038103040e40a50321010080d0014010000b8070150f8807408003000d8141e400369600d03c50400f15400781540208090041c4d5030501104802c03082c1001c1c070402604 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 329775008 1250 329773758 329773781
    0xa0f06020a03051303020c09070c050102181f12090807240b010509090f070306090c0816020f031b03040315090b0601110d0c060212130b0603011107020405070210 71
    0x181d94250a1600a0444a001c0c00282d4909204d9030f041c0f0120340e00295000c0e0480e82140d80008a49a040090b544543da041008113075500100e052820000c48120310440070505603425982c0580104080705020903503944a4007090400640600c129220b42c8a903003000e2207402841d00d02680c80c0c80703100005ea01c01141007201d0941c5400846858650f00804807400304c2070920606280480f4000f480d801c00007040c800b40162190005000301e40320703801c0400206040c800401400d03070902c030f000344240c41c1140e506140f121450300210115100040416034010321402542c10002c0c0c0326880c21b0320030f548401d482410b02c41400080041107200c9100202e89143c4a00000e5511700e40ca000e4810b85002883c2303505003c8a542c080c0c0e010300020814100c08010b900c3d100a01e0351103440d11a0090154442c000d0388918100c041061600b4641c000c861080d0180c0c00d034219a5941c80e04240c261241d0034810f4880c60414823116005050903040250000c42c14010b0720800d59500c9020800c6070f4610035407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 329776258 1250 329775008 329775011
    0x12040b0d0b1504030303090201120e0c01090e100b1606051608090606010509060c010609110405281401020f060a0515010206040b0403111207030302120a0207050705010e030a0f06 78
    0x15201a071280100300002580c03a0440c0c1000c4070340b41c0c0801e014903c4040c00f0706854507601c908580c420801940e01d4013014070700f004001d007c100919aa0a0346296040c082200c040002c580460320000c154803800703062000762002c07404e000310810681c01460b001c0300d5a4150049410004000d405030510400b40002c02030084110303100f00a00895020f403ca0350560810018006666402801c652807000152042503070340f485110400d004044640c8034120140c544848810000f92002c020001c40b481100c07610072150091a054905098441c041200b03107a18503010000c205203a4200360340c116050064504c05031206801c1d5091238422900c0300201b40d552810045843e60901584840c80820310052900b854181e44d52003804030054005014031044040c071418290f810841c4c0b54440c00d00a6003580c542400d461b020780650810784020002591000006810b0344c200c0c401e07a841e03e40c02000804401e0f280c5001995100317000c0705440e805002d011050404959000d035491121417203100d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 329777508 1250 329776258 329776267
    0x1a010c08040f1e0b0a0206061005040905090607020d110a0318030b070306032112020904111908010e090a0609031b110f06040501140f04092a090f061112040b 69
    0x1501c0450482d241c0168101044c14401c80ba11203030300040c5070741e01c000c0a1b2001d0f5030141345110b00b0754450045d98020528503017400700b00103006002280c4140180030680842c0c202e41001c031010390780c01000f02d641d40d1080c0d2010074640d0109108400070400f41182c00c2c4030788452520381c1c4a6444009003140c10801080d1911070405c1048110b65607510b0070401c102d4162a0014184002044134009000040f030140c0c01181c0349600c0c0e034a0b030740070882100254640c0c607078594100044004030484014640d011419240001803240a00350540b4860401a40504081c2d14607a480c2c2e0300034884040e0640800a500305081c90079400750010301034541c050003e03140030040314000c001440c1c9521481c1390203100c05110070802e591700021203400c00b0601c014603039250418a881046039001d268401c2e45650b00380342d610140030405101004140710000403413441a08614010f0307c82403103e200c5d004960075031290030020a4807031502c843c9589070420030b448000403542050039280c1c10030307080418170040008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 329778758 1250 329777508 329777549
    0x70c080d17150d0b092103070e090a020903030c0d080f160c06060e01120c1406030402061e0d09060e010614061308060f0108071211100e040509100c031a010c08040f 72
    0x10310398621b401840c2005195261210000f80f101e0710390030701c00b4080c10319040420268107064040d54a1401c026003240d40301c848010156940c7c401c1c544814002c684180c01003a013081d103804a50388525907620030442d0910b0028800c98241d42c60440503551282e07183d07004164501010055030003442c100182c15580750003800c0903100202e00e42d110b1103120040c2032001d01c45451300419a98003d80444445480f180491482c0108102c41e01191103420000507029106c408503903c48910180204010418403a8843e20300c0e0807101c0a01403101010903c4040140714901000104490000200441c010603510503405140c1503060380c00703052000c2c121005201024007080081c0080c82c482071004c00e03450b0340d40c0b500d001c60032000e9645401441000c2c5901da085000c1e1022003022017024104000901c1c064125a0710341c1080700100c2041400c1150301100d9034032070301030b00c15290600d99810b000340d49500010740780d80090318012241da10003400002841c28904907404000d00311001c0941d184100c84 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 329780008 1250 329778758 329778793
    0x30309010e062a0f03010e07030e01150905060409020301022113030f0c0305090d060902030c010504030b0a05060315040614130f0b0615070c080d17150d0b09 69
    0x10341c2030206982c008001c2008420301c2ca4450448801c00c051640c21588002c20341560901c1061101c0d41e00860002c00020b59620540400b842096199001c01c51445000002801e0700c4591041c020000f1503075400340664a4907a11241c2c011400800c0080c01d40c4265012070b007684c02170080b2030140c0ba581c403e40c40d82c81c4554422103500640100b07248003c0c141550b005001c0450616a640400c10702e0078036402058002c00440300581c00c010b20708880c0c02a00d00e801c5011b4a4551b108900074000c0c4c0c3e07001a26075005030140c0d001d5a44c0310000d91007940c1c4d0b10b85180028080280000c0e454802c1d031450340003a1039000c540f580600d01441c00419056540344145950440c09400d1380580701140c0458000302e1030b010078858015a11081400041d181d140020300b03400480030440d4800350000032440304102000c00d0761000c40b42d0050030359040404400b0243e44807241050705a129604210004448201507009443c0180e40109245c84481c540d807038030704085104582c10400c45d07000729103515007442c10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 329781258 1250 329780008 329780021
    0x8041806050a032018041209050d02040f0f05040c0306050c092b080a1d0406060f050a0323180606030304091a0301091b0b040f12110a03030203030901 66
    0x5945040c022a440d260110300745450a20014000c00340802c05640594102c40d00c05081c40c0005111400031200001e013100081d40965003210014001001c0b40c034164014010700c421520300a1404841c948180c0034440500442508661019603844842070750040074410036000c1e0303014000b03d55000d400c40c54418100e85000d420040c51034414000c0c140282c0e2654846c5040c007550b80402c404000442a2010750401c01c1d6800034116000811041c907119400360607208280c0744d030184016941030762000d010403a11140106070020721002c0030707110f600c0d0162000704420f10075480c3c00903c1200918603000c244020310b6038070f104001c6110512401c1e64034080d11403100c5014801a10f0b0300d04010b80002d9070b9200314403500c204a52100d03c071501d91210402681e140700c0300540280804201707464803c0c0216000140e1002c0803001c150301064401d901d00a803070a0b039506c0d0103007100c498100520301e580ca1341c003104201c82c5014071441011481d1a46503090005520980046480c1e00b44116182c2c2550300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 329782508 1250 329781258 329781299
    0x1030309090501120201030b030102130602010f15030203030712090b040f050a09151413020c010e07060504080a060f06090e01050103020f040e030906070318061e08010b1c020c07030804 81
    0x2e0500600c0b441e10400040c0d460395609090004e8841030103408a03019000f803004170401c00035003100004400d50190006041503202c2c0030308005620034451040840202400040d403d640280181c200150090600040041841c1480040765903039104003030b0b5070750268102241c040d8550310100502d00b0a82c40d402c0c0501402031003801091041030401d02c4428040c8140c0c6807104001800c03900e40d4407820304001c01510501b00641d6104554030080d40030f0051403080c01d060703220b0f6503400190184200213a4080d69505405000b030b00c804c60321440054280c4100c040319690703036150002940b610b10b205602038192420004541580340d80100004144401a0b8901480c2003180c1d1000912001c811140c00080440d105070b210030440c10110340440040b400c0c00600c2400900204942c1c3d080b0b4070075000c481180141040039100d00d2011541498280f080c0c1d020f1020500c0004002448208829000964594014100310000085600d81328280e402038a0007140054184100481100c0c41010100d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 329783758 1250 329782508 329782511
    0x90102070902030105031b15040311032e0f150e0f09010506130216080f040f05010507080901031e06060e09150d0b13020406030b011e050109171f02030103030909 71
    0x40c90000801d40350380301d901384030081c00b00c7d0076541c0c3c4082d40e81e0a00020203084500084d41c8668a900e001d026110908103881d00c00c0c840c03594158044581662058650501c01c14617007440c0700f1344400c210192040c003006a038200c6c0c03510313400c03140c3c2c152010701003005003815425160f850900000002d800b040c042c1007840240d0602040200b03607102c11941c03800d0300001d0107005035200302d03104111912414101005050090010f4409504a0747c000078000340c03040390015003031950b62a0015180c80c8240705005210003814460149158025486065000d000208411801c400e90342c4440440c0c10540000c03000c90401c04004038142004510f15a1108106001130070700e11444002825920255800400c0006020002010076a112200f01d145540c094410b200e030b0b5480303141111444009004105185060010008640315012a00b200700c45042e1103104a0034240a902c0300b0103040d50800b009503116442014040c1250055004412101d0300f0700141c4950651400030a0070206501211229 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 329785008 1250 329783758 329783761
    0x1030b040b060f0c01060e10051003020405010c080702220e07060206190c02120d020a030c1806050903030c07170631170705060402010813030804020d0c150509010207090203 76
    0x3038642c0c2c4212600d58410001c59900d4030800e44040e03014064982080c815800c0100901c074050f87d00a5801080d500100d900d6a11032485410440c02c038062449814001035541c4a01004222004001d12000f0b0000c1c04503100144070750010700500005041c0080240e58444a40c00f0081040c0180c40c0a492144090720250403c20703604004c15500070052401d5960390348034091044d0003045034080207090034000640712403070030000500a4001132100000300c1d0910402a141a108145050800c01485070b0340130b107241031405c200d9068100c00c0c1704e25054030041140103000310003001044010951626812920b1000329440350800030050002c02c0d007000700c0e880b90040104980071001480034031600ca1440c001d804d0502d103007800207500807004050b100080721014040003007040c0d48036900030b807500e88864403107880540310441030144c0a00000c01105c0032500500d0418202d04100740242011802c1d82e8458114404101d18003540c0d0020600000b04c100c102e580500080000b41418a02103055 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 329786258 1250 329785008 329785031
    0x2a090509060f04150605070309210b07030f090f020307090510090c0203090d03080702010c0e0f13060302040204060203030403030e0a1a060d060203070c0c0b0306031906110a0e01030b04 81
    0x14400a0101440b4000c0c0b120588102e440f2540544c02c400740d407032484115165a220044d007640c1c0900030030b82c000740c40100085103103084030b00d500024403401c1c0c841a64034041034030362000002024110208150b01c034080154402c0290181c40742c9503000d80f1007240e5005240c410103161440940c4003004140c00d020402015400480c03045044031301c44c450100700081149801c03411481040d0a4603446001c0b07004030002d0590201840b4400c641d0f5400130410521400c03030139621045402e00782c561000060000d410181401c44130708c960303c0880e22001c03c016480381c1c0020107a8100740c10020040e807012042100b8164103008050380620144003921651030301d40c554440c6e14248420000a003500600030500b0390311001a0b582c90b9a805c0f501c215124104403200070040c0c188041c0c140c42283c446500810249940700c101c0c0d00840000b4005c1902e0346c0360144c10b44280715a10070984070582c0e14061809030701e0200e40200320300c003007a035105004611403034009802c450003168201d000340d280c203401405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 329787508 1250 329786258 329786269
    0x15260124051c06050403050d050709030206041a0d0e01020702031203090c01080408090d0302071409190507021c050301050a08060702061807210204140c0a03020f04092a0905 76
    0x2a00c0040d02c4140310140032121903610350003036003070050005150104120074540e0200181001040e00c100610150320780c1c8104403002592400b0103548094100000c2040640c0c404130711103d00307003032000f20f030401c02617107040422141128540c0805940024150b0214038040c0061030810036a1540941582801051156140c1306144e126051001c46008036040c050104141e0b01e00c02001007580141022600d0300035150300c4184500102c11000c070354145000d1504110301c920400c544800207621508124405d8083c15005c1c042c0c8056000b20410b80c00604514401d080c0c00b102943c950960b254907001c14050a441d96074003030f03003060700600140000c15602098141d00403400c08120302c09040043c280d14100a190b45c0312a1510003421134540e284010f40c048244498000c8808201d0054520a120a20320307007103e0501125a0070821009014080c1d40503180616182151506103a2201e080c1d00840f18059003002e2141c00443c5500d4030704c41d01c1101159101800c0c0b034040c540c189000b01140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 329788758 1250 329787508 329787581
    0xc03070906140d11040b0c0c01080106020f0c040c050405060304061401050d02012c0307080109061802031f061502010b0f011404030312020c01050408120f010605040603152601 77
    0x100359130b03d40e00d000c0c9841c1400303020740300074004c1e10310031075940c030001c0d9000380d0b4914500c0c031102d002c645400000039030140007080f40800070720000d014210b842c5200702000004c111009044007801000d0202046c0f40e110080910b104610404001900100c128880b81003900d05074096440f9070a507038881b10060340e208400e03801006c007001808280032120180308044850901300da582501ca000000580d4039030540141441d42d00840781000f1442069200010125000300c0194159214040000b24007040c5940c41c1c0401e80780ea40c00140d2540c86060136090b40c00c04405410041c0e46902e84054640703081c511034100d800003420990b408021901c08415036018601c8040c040c007000707880e1503410000e2501151042c01c00340d4001c00003485c1600d0b100120ba00301840307500054074203000081d076401714111540d040c0c030200d407181400c041c40c1c00c008a001d0041c0c1c0c0300c08622071540303441c0010092850030345070450484c2d00c080302d007100e00d850703107002c1c00c5070350030743d660344c6081b9a181c540321003070010303856070b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 329790008 1250 329788758 329788777
    0xc0904081c060324150518180a0308010305100519090602160b1b03040b150103020c070303020c03160b07020f0d0b0408030a11030603150a0608060c0307090614 70
    0x200d18401da018540005103501e0340094002400705080c501d618803c880c2d605281d41020034100300e400080780040380445210b0207803036080130044a4084000000042d9542c1c0890702102546032071030101c02e11414035016440442c0803829003001401008401d0010098204008104020034500780c0d400040d84840003072290407065568040c00207004c0c40342c04445c4091203524294100c02c03d40d1805100c004012290042c0707101d89881207c21450000c01103a000326000102191240c451049902180c000c01422034145a400c000300d80a4107002c1c4103080c0250f02a80283c210b0320706400925043c8010039138030038840c1804c202c0510205c2e001c0c0041c0c81031a601a18003052000040c000b040458004240140c0100320b200200b10420069600a5215400c0d543c0c0034013103244a00a0003800380819100194140c10405044080c200100400d0754800420000420216601c112441c14100d090310100b8480302c0010030031003800d402c030042d6801000d0502d0140702902c80c410300800303240140b42c0b44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 329791258 1250 329790008 329790037
    0xc0201211e11090424091401060513032303030f0106020d05130303120b041b030c020109031704051f0603030e0a080c091b04060305060f0d0c03030c05070f08030a0207050307291204080403050c090408 87
    0x30dc0260b142c0045251750590088048030b1752030074114926043d11209220350030040c4a01ea8034900414070440640d080c0d080c80030007002659095036070582d91041020034181c6555518004946240c0e29400781d0b0050b0020b8940c00610300702403280040c269818400781605680c181030170740c800070f54444c0350501f01c0c00e0400180c4606864074545035040c0751900c0404140c8480c01c4040c070442d0300c1d10360701c10b0046070300c00c3e240d0310800020700c0c050241c540024444d0b60400d0300045041c0c0780a0030b1015202342d10903141e071301200b040320601083c0e41c61504150020000a07039101d040100c1c0e800c05e24412400d4140444071401d00468640d81e02001c034825020050030010101110344c200b01c070401019018015450380c0e807000d00e0329510529a250442107503000144103154000400d4100410814280c410354101000000031035000440c0044015000d4020080100200c4c050340c0c0c10039290501440c130500d846a903d514504001d860032000c010054881c11405007400009000c0385d00b00c0f0000b001d200603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 329792508 1250 329791258 329791283
    0x9050a120206070b0f0114031212090a1209090506042f12010e0621061303090302060f0c0f071202010c0201211e1109042409140106051303 61
    0x218040340a1581c005054820200a01c817580f1002d00600b4181c0b1100b0700480b2072501c0c400105a940c068032462201701c50810420701d0010003940c0c4545c0da005040340f046418250195468510000d03da00250001403200d0105020b0690305010300307500304000311801c2c80703000c8111505080c400b605100c4064844a161030087c4404c1540341a40d5070410a41c607500695070b510b60344040b03008001c413a9188200c40c090810041464107401502c00c0030903a034000c0a0b5552080d01030544440d480000341c0c01d02c054904c0010059030380c0c000520059401d640203686a10030300c00c84601d846190600074500390031140d8103020703020f001c10950552a409182108803080103000690702500c1d264103410b090801400e8030190110280c00c02000002d030714688440340403075540100c0c101c0f201743d0550034003c40100324400341442c0035040305590201c204100c020360b82e88002e120b189406140d00c8129502d4075003c02c1521070f540a21603900400417400e0061800d4984c11421494902500000744205001307074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 329793758 1250 329792508 329792513
    0x602010908121008100c030b010314010e092b09050d1104150e0f04142107060b1315050f010c1202031b030c06011205060103080901121406030d09050a12 67
    0x5143c000b8103050060381c0040d00384a810f00080d1480d4510000402d09000481301c0d02e51080c41201c41e60680c1d0b85010110b0703420503504129480000c0e1541d8658850000001c0c0700360010310344c00342e004409030a00c1c0c080c44e54403040a415042d0f1684081c0c820022980618041100180114460710341101e0004480c60f96442d0400d045046402c400c0c5070300e000c48100b20322500e5100006003c1c502074071944210382c119460807a520405482d0600d484016006140c18031114040a01945441000c000c1400000800852070303080030890000080b6495509030705188400316002c00240005903898401d00f001c072000030f0010041e0f098001c1c15070990005a4040071700c00e10640d40c040000c0340c0380c00b03441914607000c507a4940007008003000318042d041c0002103540b1428800c0c0340350f0b680003018107040c0e880c680791700c0c8040e0001c400290500c07100d140c2c1c21081c40c15174813032003002c0c0b144440d481351241402414149000c075086005402c2c400d65081c00d01c690f695505006040350500d90785801070000c1031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 329795008 1250 329793758 329793781
    0x90504080403140d110706050a0c051e06161407030521011805010f03020f06030403180b0307183008160302061e0411031c03050a06060201090812 64
    0x7a0b001a10a0030030850030350100c40003281e0a2540d090a907100072640d07043d4032100e0b031240c120344508804100c080000030b0186010b1184d03604403600031002e8074117100314207210f00c1884200743c0010405800c48001c1110300301041425030080b86e030920b000d41c102c3c1420f900846c1e040c03107481c40c05404e000012400684108450200d0700a11070300d810401c642d0759641401d6484d61024101181400d418680040f1b801801d15010000320fa40050005020610070f9051200b00d91001d8803c0d001c1220034a0b104002e421000c402800402c180d400301541c0c0d181c500030007064000003030150446041c07040410400f580c007001c0c0080e10110854a024446012550703841c040380207051005240032804566840700302c41000d04100101c3c001d40907030340035a494048546104800c00c20100e00c0d40c0c106404030f00410100c0c142d050740e0020180403245406007102540e0200f445404030351000030741354010401100d03458000c502c001c181c640000e00c406440c03541c642219000306400c42c406c11282e01e00058260300c22 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 329796258 1250 329795008 329795017
    0x905030f0d0248030f0604020a0308070206210402041404260c061503010513030c1101030b04050f040c0b0c0714010e100f020106060c0b0a0f020919170609030409050408 74
    0x4185540314249030034003c00c8181401d940c0f154482d00450f00850042c14001c41c030740780710715401048000c0b2641169203c03e99900004816030700901c0501480d0348280e22281500c014045010f4103200915181c4108002e41c1c0305105109541001c5206000c0050301d2500d843e4101c2c40810b1611440c04008a00901c40e80600d5284600714450031042c030140c00c018480c425090340c8154000e11140d038810485c0c0b225031808004c014000f648003503040300843c1403460400010300f01490b001c0303081e00303003800014180c810503102100e034823002d0401c0c00100450000c8001c0240240c0c00c03068184095102225200d14503881490300ca000a010001c6060307100f0700c030f02d001c0c0500081498400030078451004241c140801c901c080034cd0320300f0b440800d003d80551790103000c2c582e010074902501e6880c80000c10280c1a203402540840f42c00b030188005903a1858141c05c8001000802030300454a49030441d0758056201c420781e4159080081442451344002c0122000d50305001804942d549652400d03c0f00d9128 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 329797508 1250 329796258 329796343
    0x6040902010e0d0f0b0907060903060c170106120e01062102030a0b090d02192015031e01150215090705030304030614060f010f14040302060a0905030f0d02 68
    0x107116529410071041c000903410f0617025a002c140503513a030704501640d80f00240641c102054402e0401c100145440c2c00250458400745480081c08000d41d00182c0900402e81013140801c440b240c0d408110300080c803c0c40380a0070000c009210b01440c0c0491030060300400140c034a20718098020a01c2075450801c41c58041e0796002d6544500740c1740542ea413613103852605203400018010042c4c03002003000d10a2202030003507084113250106519103244000e2400c0e80080321038100790310640d17400c680d01014010b548980302154105259014602e2001c0a0140507048800240001030f10001450350001d41c0b003041603040e681c0070b4420b454100703003945030451b645e014560500c00010088100070b4140c0199940d001d162081005030f0700d401040210911030107042d10700040504585c802418400c40d00400c18040c1c010b0502d180907100d8000c1101580040440004242c4000e4104100d08041068404207075800c005040f940e070502e00000d4951040707034481494000000f601840341e14500020031074a02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 329798758 1250 329797508 329797519
    0xf010c020d1205130801090506010b03041a010305010b1014070b0403201509190816150501141905010e040b040c030902030d05070302070510030905060703060306200306040902010e 79
    0x5000e4801403065010803002c000340da00d080c0c00040d4017001402003004499000000d0182a0b0800380701da14103130001041904c0d80d10758a8507001d40300d04000e00b0a33010714051000861500d0307040c1e003170140d000301c4810a0801c0009207288940e039082118250350100b94003035070041c61354403a81012940d01c02042a0309a140741042d00201342e802c1e00090b015440d0641c0494282c5170f0f502ca080c0c05071140450880d01e02c20300c50303680d028000101200002c0041445620886581008645820422500840f0740000280d510310050007582100c0c80038292044084410b401d0320445800381c1e00410f0f94a210312410300c608480306450369a92600440891100508200040908100010003415031100c0c03d034004d00034043e682268038401c41c200d90059400d41c00810700c1c2840d16090103050556640150304050b516101c0b1000a0380500c1140c0c0100030903035000c102e950850a1840803523101880a040c1d40030411100b1600e014404140c9900680466000868001c0c40c001680c4e2001800102c59016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 329800008 1250 329798758 329798783
    0x605090705040e070503150112110d0e070f0812160f060902130b010e01081503060f0702010e010b0d0f03090503030c01020a0e0d0c0314030c03030a020a0f030b0f010c020d 75
    0x2607030090151080390507070ba03003008142c2c5540c0801e0310248000d541d491100c060b88420445294050026240111007800c40007903880503807a103a280c680c1008410f60001ea4848a519441c03d004020080c050242500c00699091138441e480d03135655540000d401c07414101050054400040c0300740c5e40c60158100b010704090400750f2400800800341c50404a1184401d4441e007070102c1c0d22841900050103042e1180caa0b225001d40064a110000030011a02403207891140d411685060044a00400213442d0681c42400c212902a080d40c0748000c80a11070f81c5040000070840c1d03104484079026a81244560740034003120b050440b601c0c403064011070f030140f00000310661309a0341503000303055602060b59031614207072410b010801c10b000c0144000c2c1203201446014808188020120103107942ca240032a80f800c00400305040c11500200c0c0c0520304c0344c1d808035584010f690071016061500c0d080f4603040181c883e035907002030180b000b100102d5040000e482180d00840d11550345070390340c0d10307003009810020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 329801258 1250 329800008 329800021
    0x30406090602010e0106050f3105010e16050406031e060311010314060906090c13150806180106110102040f09062405070305070f0f030903020a150206010b0904060509 73
    0x22540ca2107140010b600c0c0060002d0024018030408095940040c07040654120140810007004161058080443c104030406050031203584030701d05818041e0725000c10b166150403040d0501d0071004202400d040419080014440c0c0e01c401107505440039030030700040c0a102004e200c0d29200d8000d0030610301500c4c00314080103001c29916092030b4078001342c0e82032181d120400201412402c0c10784440d41c21500d0750001c1046403400c0c94500303500103008010300c2d080c2500380c1c40b1030300d00c041242d110720362902c800c904410600790b0000300d40da400700d030944140c801c000480303801d240d60200501c00d000c100070040307000c510026402e4040302c0c01044003204050603141c940200c0e03002082244200303c0707241418107100e100e072032880d080d0205a00d6180c4946007409101d031070541d62603006260481d9044075080002c000610900d01050055010340d544040141c21071050295402d003e4000144010031500c07070100503980001c800f030643d1691411240c46054002c04900070704910b810055000009104100c40c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 329802508 1250 329801258 329801267
    0x160b070206040606050d020a0e0406090b0c04031a04020321190905090702010e070b03071e0e03011d0a02060c0a06020415120b060901110c04060602150f01050d02090a020c030406 78
    0x40d4003c0d1420803445507a482048200c01940354025008200200c08100c0396002c02c0d040c41c2d010740500d40200300406641c0e141d0010520440d00388941410204043c0709010000420f1070005011f400008020308080c0c000076607070180303015000b45407014415079500c400980b1045e00c0800d030800070760030641e0350100006000c440d80c0e405a54010540c8200050003984140510074000005001a040382c81c1001d504082d1544010b01c86001d002c0405401030b1442c80d1400050321150b40b0b603854070710002c0741c0004c06096500d00390100356510300c14800d5400502000c0350500060750704071080c03a62340d2106540c040c1021503101001e17100078804a40050130003020951303c0a89445030741d60650751020f50000c1000c0324441411540c000d40709000188855000d10002a14021408200c0310003220301c1000a081c0e030050f0300400b005070428009246200400207609801c42803842030940658100400f1440c40c070554800030b0300c00c90121020440c505c240b5030445910b40c3e00c0380c069030313a19512400c0150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 329803758 1250 329802508 329802511
    0x3080307270911070f1709061c0f0b0307141f020a3c0f02040606030b0f04020910200609070320010f030b041122120b0c160b070206 58
    0x218080c1400c14440f25582204102d900d80c652180140d44035510a4940c40c0320000900140340404e6004c02c031494056480390040c06003051516803001c604a4003840b07900907105410400204107082c0010f03189203540209003e0266081c01001d045801080c0c2c0000b190303108404942c0f9401125502c82c0007110f41d0201380740304814040d404214078003a500032441c0c49068051420b100c1a103142040d08504416032050ba8020b44c040c0241d58580c2c049500001c044806030382c800c0000c04e82c0c07100300e007949013020484180b075100b04440841c00c0800c410003051038685070003c0041009400c0643c0000420b41e94a045482c8044604448180ca001b240d056a150303071130b0000b5604100c0001424440350382d140580c2c2c01003981a51681d91801c405041a8098031080c00308031781c010307114011421340c0d51081d4003170030703004040401924804545000d0100d61101940185214030610b5000301c01140d10a010150031464851503180d0390010008000d40726051410000c1000c00054240720340707a580003d40c00d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 329805008 1250 329803758 329803769
    0x91e0f02090114070308040b1305160503071a120606040803070308070311040311010f02031c02180108161d04020a081f05010e060f0d051329010308030727 68
    0x2040b403400f4420340c401c458042c018000b4005030745000040c0010b8840d040e00d5806c95407010300c00e90500803581e070707042c10801c0030030705401c011000b00030400c00c5103001c04c003070401441170700750b607031004d1800c03500702c48080c829020490054034170301e4080341443e1a0803044900814240040d20b0701c40d54540303001006032a003520400002820445540000b04002040707404407548000c2e0510494050342c01502d450500c1940002903020911404404226500d0002505042a1070051380c85004151541100d000c0080c42410070514000b0004c8030b5014040075109200030f810010300c450840d502800d048010f8040d080d4010f030020840182d62900007468a000c6c0051090f0813134145114081c4480420803882000d0015800b4a27290f002428904018042407000c80360451500c240458408207844050711812110360000c4418401d014020704580e06c0b00c1c2101c10105d0600c21700801d20200a030303040c0409440502d00101064800b0700508000d2101400c80c041518080790b8a03840d2402910b062046 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 329806258 1250 329805008 329805017
    0x30a0206040b030f0609010e04060902010201091b0e09010903050a110a0501020d021225050a020307021905100201020f040b0c010902030a0b160224040f080f072307091e0f020901 78
    0x40317240c5280084109040e43c1910002c50410b0f40e440d1104006426040e2062f170541d5a500401404604440c2d012a80d227aa2400036100c4645003001e0605805402000300010743d1402d02004000b0f9805400c80300004074a140c280c1003011246465810b0280e5420300814541c4002206252038149801420a9081d00541c0340711300d50b54012441d50042007614502040803403c0c65011650303000f100904041500c03481201e080c041540d02048000041600c080c290b0260801c0810a51801c1250142004140d1000794200b01148207002c8a50050703000340c80e6201c00200b0308444000e002d50003c550303544c0080c115440040d075414007800065060711101000c0380f10b90f620401441c00062480f9404465902006c0d90701c0300e01c0d0000000d0f0350007402c1125180b003150221804070341d80102070841000c04da65010380d036050628083c04034005100343c020031043e041c01c43d50b81001d00815003204841084030007150012040c0b03004180d504001103d502440e20f0800840e41c0703862540d010b400c080000307072079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 329807508 1250 329806258 329806261
    0x109060c09090b030c010305100e01030b1f0f030b06010311130f0f2d0e011e06110307020d060b0a030309030611120a0c030917130501050f07030e030a0206040b030f 72
    0x1054444040c3c0c4103800d64086140ea22a55100354002a0f2041000c00e40b44a0795481d4000c1e501986000e900c1a541100d01c00300340038103403c9000450007420f1005008034180351812801089151181c400030b001c4900d100300050203640240c0144076180c0003c0c00c856a00d40c0d401521442421160180ba507001c21983c00c081a00c1c000030341c6800554840b1480c01000030652807010240588115003080e100808690000b030702c910442d241400303803140180c83e51a0190390409191030620b00d80c4003808200780c3c0902c0000404c1c0100c21603004540648000154109500707250000d043e100120a8000c40307620400003c2c503030b102d00c0050a8170b10400050080380c049100540345070240c0c2c0810040e200061010485058456004407030f0b0840c40e08000c0741c40100340e10303030105195800640c05440c6800240409280114460b580d0242c1302c00d0901c80d080c0b200c1105410102e010703d880040c240849800e66584a590402040340300c244c0c020021035407152151725150b003030742050b0365400907848003c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 329808758 1250 329807508 329807519
    0x303090b041b081b0402090f04090b0f0903070209061201090b100f1509120c05130f0b0406030308060621090f0d0c110f1309060204080f0a0506150109080109060c09 72
    0x20305000100c41080004c1010003555040000a5000c031020035442603039040b040401d0780342c41c0582200e45024020b80e909a10b004982c102d00382c5001880c03065542c0040142900698508035503e0304100e0517180c80d00764089640c9140c2c010800201d0281032a001003042002d021840110441620003240c42c4011144d914480401c0d11000000600c01140e11a08140310690300c1c00c0304841407601410603504071b15501c0340030070010003004000c4480c554403030805d0901d1241500400382c0c0e03040141d030b0030403510f882c6803401800514050a00d6108810000c1d00440d9152201728107200d82c580546120085e0401a810759568541051710710354500a464840d080a03008109403000301d60011654a121109041049034a41140034219801158034680c500300820510564562903c6502b00603952420014110304c0c2401081c105010f90740a161210001100880c03826000010b030264441d15001c55801612001c018ae000807400d07601e400c2032041070100e550030694138413010b41c0700c0d034080d41e0300c90707 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 329810008 1250 329808758 329808763
    0x31f0803030a0f0e0a0f050307060e03090f030c1003150e1602210313030306080d03090b1b0415020a150204140609031b041b120b18040f0303090b041b08 67
    0x130014113a5004400305101203140c0031201c20801d4800c6095a01d081c80d01e668140486902075a6036070f241c1e001240304291400c00108407000c0040c218014101510900300240740166950744542c205911401c0840c0a07501000021000d09140d40007101c40f46003da00902c1d050640c081c0940040c03280ca045215186002da020a10503603401c0312003455030307540c981200681644034404804041d554100020b4189091000c4280310410f950085204d10749030600c034000c070b4006440810019024801130b141d040d061f10455049500300d000d4062000112401682041398804018006418000d081c002e172000e82e600610a0b0784841d1a0b02440100220611529014420640307030554880034550790340c402c00c1d050384144020001e001007010000d8076560610348102100150200c2c2d81c90720003c2480c0494002c468184030f0a88000343e1040541c0031102c0d18910180001d8500ca22969500003494070035000020a503402403042404e6041501d440b0443c280c0c41c0d804039018040100300880c641102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 329811258 1250 329810008 329810021
    0x12061a0a150e061b0c010801090605030307021203070b101a0901050a08090c0a15080906060102030a3207031d091609080106061107090c02030f031f0803030a0f 70
    0x360080070a85440d485410b9510030400078010380c2c000d41c02d1019a01c00c1416400d25201c480451010f00b031080d118a001400304031041c0c00c41100241880402d00158800005a2794815012100c0c03c200031200c080c0c440c2036215882e4090306101c140420040c8401c1f914001d003003198107054618210007031501d00320095002d61002d084c0002c02c04c001180c141d910954003030703800c00313034010540d50100302e1880042c400311050b500510216040d0903c4850080d00301e0b041036400040f540c050207903440c00c80f00007910b80c1b18420f801d0b01449181050158403e8501744a403844214920455102804026003100c0c160840e06080380001c0e2485000c080c10f50600005800780c00e0007900300003058480805000150120040e444200000b82c2400149000300740140700c01001380d40c6a1740c0b554000003002504201254000c3e041d03075401c040d00d850641e5800012211500400c00e180c64403070700e510040b1040b90074015510210041c440d6000300d954040400107600a40080a04010f40c1084142500944a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 329812508 1250 329811258 329811269
    0xf030506010c0809120a0b07020d140d0203073b301002030a02030603070506030c040306051503030724090f11030c0904050a020f060c100b0a12061a0a 66
    0xba400e40e800118020064a5482c074024040a8228152a4000e1600e101c0c00e8003620410390740c10a114800d9010b101c00c1c200350f800c03443c0a2405202094005002e0301c00ca02c00d441900d5400400910083c0c8244401c400031015010a80c44001010104502603500304403400b200400d28541c14260f0b14015059400090742c0351140140c03803800d55550b09100c0c80e41000306999001d003501c0794004600601c011886640c40500c01600e9040070710906142000c26000f060041d081002841070f85000d8900f50784c01c603940000041010780c0e4448075208002c079220022038061101156220400662104070b10340e10f1400e80050005080d0268110292040840301170f01c9a1480101600480e1500b8056a80e55401030100c070f6100c0c100c0c00100310b5403101181d086d01d054000111050452414003520160000304031209810716805c3c0300100c2d243c800d20100d500d03445e0358403001c01e6031684a000c04000202502c1e0403102c90342000d414854060b0816075986d003ca0701c080207a01d24185001400d0605a41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 329813758 1250 329812508 329812517
    0xa0f0509210903070f0305011d1902030c090906040b0903040f061101060b0316020c04050606040909031709030a0810080718140106120c02061b070606030c08010c0f03050601 76
    0x101c4031081510140141c04403440060341c104150070094900f000584010400340f48420b00d402e19500740355085603140040d822640b0038031201045007000010700c84000e420000c9103081e40311842d07c0080d10740704162940320303000281d400c20030482550101e2920b01c15800341c8802e041a0b56450201510b0b13205a015010280703500704028002144503046005080400070300002d44941c03107201d10100754000303c8508606d0b0b136041205003289a1706014056a45200b071358203004c142000350000b9551301840c010031280b95543e50549003494402c6c034180061050100204500f070801c210700f1500c9910990540b00822a030718080b48503000714009a00448250344003800d0385509045005902c0022440e081c000c6607140d00311052040f22105202e4002d10072034a81c00308402c0041d03070102c00d032842084000b00799004042004507200c11050381441d01500c03581010b0740c48034107203025801040c8540010304501038029022440c8901580300015210854882504e00c0030191021000d80702c00310364440c0005c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 329815008 1250 329813758 329813773
    0x30606140c07120501020403020a080d08061203070b091e1c03021615090204060608040209061c0c170f0f0d0513030210082502030301120f1a0a0f0509 66
    0x1009803024080201d003003001e4900081e62591403807035411407840241c5090b50700140c00c00440c58003428050041c032401c00501110080048080d203008001402540030300140898035004050a1085940040d0f104001e03000905000010320b650b0024441d2985005001c0110b456007404002844a00c1d0710b1202c5a031906000a040304030081e411044102c600c4072040360b03507400010764006008001e403020820018409440b03004110a803029035102c1e10511003454207010160300d038807440a178413500c01d4410500256007647c2201c0724880d04e61001d00310b0481c139580451141d00400d080c5d51401e80000444101c040003400e01030715901c88010700c7d5600e520401c048000940120041d014010710140001c1307032243d03217030046080700c1303a050a1200010704080030040072008900b080b1084007100d15804500a617076010184d40c900c010f00444041c035090441e820200140d00c0e0344003411540c003069032480d211320146e81c070301954019140c241510b4100311242c040c2100a21030103200d45403010040c01803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 329816258 1250 329815008 329815037
    0x80c030a2a03050a0b0c2805160b0f09010b01170408040b0403081b1f05180f03030702120a0e09070926010b0307030f0201080916060e010e01030606 65
    0x80c1140c00340005114400d8039084080c1640c0c40a0082d400384000d0f00071400c85150081900700014160b558415084c0281c00e04046403155140412a407413100c11071414010b441078030980280480d80e10912419a01c04081002c0c2600240c010f042225a50071380303450340100c03a426070b841c0940e03150010b41c2080307903c5c284403c2140c8403074000780581182171a05d43c40b10f1b019070650b80107820a80d041306000030028410091a04064a10010f100c0075001c9440003140401d002403040901c4425203407a40003013010507882c46548000707002048100e4050003101c190260f00c1e90400c80c1d40383d0150098145443e50f1880c10400c880c01124580c0d10700da5444d0810041016644002c0c20f40402c004030010081054030425a03003100c83c103000005100c03540c41c0601102e007514a510082030181c0c1144404100107003070542603d1307940c1d0742400d120309280d5540885a00d0150180000700300e081c04a0703400910290070110020b980d50f02a600c54100b15180401941500c1071842010001503c950b0910322 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 329817508 1250 329816258 329816273
    0x10b1309081606090209040f140706020729130501020d050c030702040c0201090213060f05150301050103110d15090e010c021b210d0f08100612060503060a0b0406080c030a 75
    0xb5560320442c40064007810903004203000500c03c917000c0300d4103240c480d603400902025060a07045512810000e00626041680c02903c0b280c3c1417203010b44400b44103503010511016800100d0700300380303100e94154540c400c000000111030a10b2240a0241c003d0440c41000b881c403400c215150b04170207100035454035a2075403c1c44000c2400c48000c4045540c0e69002000503540d516103034842c90010000482c2c0e050030009074580f0100c0c582e010b14070610b07a40c020181d90721021026281158400d0800049054180c00c9080041c032554008001c0306142a0700d40c1800c44240e0500d4003a20701c011001c004940d07419040500301c50704009510301603031100c0c05c510610043c495a4014021010b8100f000c02c070001e403d5080e48064040c114146074101d4402424550361100c0985002345003882c1040712810141a034884004c4140191030070042c281840b003c4080070b83d0009401001c002c1c080350441d103040820100241121a0075500c11400e1500000e544c460000750301d080baa000802070603540200b0340c0d070450b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 329818758 1250 329817508 329817547
    0x7081c080117030412081c06061b030912110d05030a0906140d0c20060603060a0606080f0a02070c0b091003062312010509100615050403150b0909010b130908 69
    0x191032400c01c0154520142240c7d00c0003c2da01080b2030003141041c1000d0000e0503130000e800c90105003c40504006012950001500080300d074004501d0611200f142082482c040820029940200300030001404210001000b4034801c001d0b0303a03032600025142d01d0300702c0d00c0802003074891006800521100790b540020340d02800c01c2401e0f40c01d000c00411022100301129003243e0304040f10300d4010008010423403c2c01d214a60f40110000c0081000c981024805821902d0240841a86440e0800003450501c0030b58101c0d111141c21a20441c42c40b0b66aa901a495600c1000d14a0242c0b403149810744800303000e0b008000c01d880311660a0080440021040c80175954244401d0354400c80d20242d0b202d41000038800c15004a2803072000e820604000da01c0c040c10340d1000d50284a00403c0a0003444100c0d91000030340b070030b90b603000c8860000bc840310035800000d060718800b01c41d030040c0180309001c3d94000c150311181d1408002e40340c549001c10280380381c5045442c64200544894820401c42e2400c40310385003180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 329820008 1250 329818758 329818763
    0x801140f070315080706030e060a110a0f03180b070f0c030203090d020d0602030f0f0907050a14010519050a090618030215071502030f0f042307081c080117030412 71
    0x162080b966515198a002100e91010f40400da940640111000c411303c1012b0740f01c40c188406000b8003c036000d990300103200307500d101010808851805c6801e030f4405d0300b0840c00d84180c1c014080700f1044030b060035008800156960004158408280b820103405822558011350305a0059804d1900f08003d108010407884402c03070b4070913640191600007030818800b440c011040c000d2090720703a01c3c1c0304660600101e0084d204000550021030100080c0d6600b5100034280e82c820428980c20003030000044c3c41d94000c01c107424034484c40d0300102c03480041d84500944290145035498200640c0e81d0482601e842e4007003800300b203906070000300910150a2500000a40010030304003607141c5002911680d03850420b0407081242503030000240301d014200e03d000c03181c03c0407009580c0c0000342850b9071012112404084004200300012001c10700c0c1c604188007000003001c0f00401ea500304103114107800b0014802c1c1014038040741811001040354200221604100200100154507050600070460300140810108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 329821258 1250 329820008 329820041
    0x1407092102041e0c14030402040207020f060c0606010f050903070e0c0f1b120c0624040228230f1c0207050705030105060109120807080a090801140f0703 67
    0x14003005845500c209155400d120038000d400c0341c110001c0f0000d40eaa502c0d0101c007004480350214440070b901030126030f045a41100c00694a04052000c200e0401c1c003074110503130000020800c250000030118ac2148159000d036144140c8180100c1c1c00d03070b01070281c0c900c00c540542c0882c40a000b1402090301003500500542207860904840c500582d880d0340c00f002e01e200010217554030b0b421103048100301090b080c4c070903042407038100346590500740d9403440c00619580b0354020700c92111081e0110031680007200743e800b5006660b940000c00b03911840c46102c6058409540c203500c05080020303c80c42c40e0440354000030001c04d01103c01802e03a16107680144030079640d0503100b08030b50040e6150b4400240c0c200010a000503848281500f051420580158000c5010364100301c20051340d43c2e0302207200820349981350b10710810170300c41d41800c91480c06030b031000808485001620b900d926800644140c100c0b0f252500034004401002510240c2c0c2c02e00b500c440c1940300125001c10700590290300b0410251203a00c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 329822508 1250 329821258 329821319
    0x90602090604081b01021527010501080114060d02010c02090a0b0901060806030f1518030c0109140d090605070b071701030b160e030703060c05070c0308030703140709 73
    0x25540380c2c4141d2000d4500d51100031400b0b0090000364241110401c24006002d2a00d845100000b01041c024440c00302d1884844c180840d10007480d222065129005000b0003843da1510040d5000300b000d010000c1024031880005900c500e418903020043c40d42c180e40c0c18030814981c1d4288905248003405070000c02e51101003620603600c0e0a440d00340280b60550f0b81448504000091509001c5512401d1026400080f80d00c01e0038003605003090703041440032000313099203850710030614114000c002c1b1030580d650034240b882080c0821210644610341800066a5015503410421303184c880b9148980e070301241050003210040b0307032100c0c4030640c81041030500a501c0c6c1c0035000960700d9a0000d81086405000d12000c1c00424640303521001c2c10070300c0f80e0a0100245000d000001d603140d01d21f105c020f00301510382c9182d0120301e00c14130927076030140c4d8000d030508011900c0780740217846030b04211a0040001e140010700100a40c2c08007050340911290f03103410f064103007400d040340304c480040340d018040c4140c00c18 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 329823758 1250 329822508 329822527
    0x706031d010504030201060608070201020712050f1e07141623031f060501030c270e0a020403030f08060616020a171005151f020109080f072a0504090602 67
    0x3502c0e00c60752183c1d00010b581410a04040d1080f00050048000c40e072040c80118002404407080291041203414010307145c41e845000000540704644002040c049426a696013034802d040180215074420800c4600780340b0742e501c0799652250640100c0c3d0007039021060401100742040d040050020b801800900030681c8080486d00d0843c0c640d01005455000c001407000d045058460345014041c2403a040c030034400824401040b00481120361502d08100120148503807109a94140040543c0806094107240c0002d40c40000d40003031001740c010910b6120250f036824840c01900d07200c0c8030b006000303d0902c00000054440400043c2c03081741c00103c0c03000d021403518011070654002c048404001d102002c0c03444407000a030345014040c0c400000c01c50300040000e5503411480a508400014541855000c25008a02502034140054802840007801c14640320608000308916400b840c2c10b500c0c84c3d0050a16840c802c81900054569150414030900c074604c1d09801c410400c0780124405800c000060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 329825008 1250 329823758 329823761
    0x3020c0d03080a1a210a0c080d0f0e06030a0b01030902030102040b0408122104110a03030518010f02030d15050901090605011101020a05160203030d050a0c140c0706031d01 75
    0x280816404070b1142c104000d8280c0c41c034040c5070380283c1c00106140c402c2d0710b003d011034001c16820340002410007415034506030300041040304849243d000750000301043d42e9815225180c9480d4142000013400140c00da00095000e0b00303200050f00310140c4007520315601c501e50f51000704070390010141016200d880b8103026980900290010709003045082e82c0e9203203005a11450b2000724841000100e0f424044c0d5400000a582c0141c40c05281310991282075549251260050401e81e0006500503503520b4003105040d84500034020705d4090382c80d4a04d040c506000192400100514040016030041045928401c003076001003000b080c90022800c1000d0302c0d080058040e840982009614550703801080160b0b681c007070462000814003100842c81d10045d1540100b541c41060400005507d041c8451070840d2030410480721046031443d000c0005007846d1200700064003158610b1000101c0d81c81c4052107284045003186e8015121200402407103141c04015005802001c908900300011044102c04d00c3c8420b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 329826258 1250 329825008 329825029
    0x40b06180108030901030b15090d080403080d0203040b071806110f01050411040c0906050f251a06010504050306040b0a180f03090e040b060f0f122d070603050403020c 73
    0x8900183d40c54180102c0010120b03a0100141032040c00f0342c2d40d030003880c41030f81c4d02103d820301401c0c0d91080030300685041104051180e0b500040c4003480000302d2400344215980070714044c602c250031103c800e40b18600226200301c040b072010349040001e40c41c100142c600611840101c0b02d2100143c641400d04924910b00b12601280e09640c1d246034004080407515040c801c1e1030200c506424a13045080c1030510061036402072005004111000048030307070b0b422500403140b00990100c00300e81d1440501502e0319042d2210109440b0300c01445038404503422b0343c013070007d40b0141c2d003014005014654540d1102c000b03092000d04036158081d500e042c0c4d9620340e01410303c8001d08a00074130714200d511140e40b90003001c0d10746550041c28404c0100d014000026066841244c1000303084a0003081700c162440000c00c10620411180d500064800c2d040d80c81c0840403071a807003100e03e005510000341341010180a19034550346121187da40003070000b8402e160207940490b402c54041e00c11030f00210301c010041000140d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 329827508 1250 329826258 329826269
    0x3010617070806090f0325120507020f09010b0a030f0b060705070f050102010612080c011d010c020705040b01020327100302031909030905010c060b15040519050306040b061801 77
    0x544000d2000c0c000801c5142d4210800600800c0822007040400d0f0306c900032203912a49004140c8010400c46140480313030300741c65801c00034500e40106450006445070b8050441207024003010802d201071450700b951440d048880900070780703181000c40e0004074011f00c4803440d000300b1140c1d1200141c00503140c080140c0303c40c52041c8024001d00d400c0201d1155018140d81c050307411681403030f4041c04a004214174011040380c0c4000556110b001c00d1108501401c003001c0750003a15903082284c2c040c101c10540102035840039607001d407155151a4800d10090b180040d800c03d01590003000711400301d1146480711400140c5001c240994a501440050341038a40ca1820000083c1c02005000445400490180c2030024000e800c2050407465a40600a10000d1152a06000342d811000c001d00906801c8150070060040181480ca51804d00c21040c941142c091280101440a034000c0d20760300820b04803091f110018005c01d401d80e5155070310710141000425480c0c00024100058a02480c000440f40c040e09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 329828758 1250 329827508 329827513
    0x90c030b10090b0d0609030302090d0c05040f02041202090405071211040c050a1706010c0204020c0102030a060b0c0c150d0c0801030213110327030c0601030201030f06080309040b03010617 82
    0x28038044011214080341c02001e64185000c100b00d10310350300c02c0e040c401969404030010446c0300c22410183c000340241001a604400080480010410103160440c166801164100f08181568010360200d004501500080c6501850900003501d0030754406070340b140c400e408031030115031201d51030400c1c408040c0c000c880c86036071040003a80c5840d09015441400f0b8080c50002d00f00b40200c0d000518041141c403121304020440000708210f07902c912202079469030003800542d9640d03030402006000f50700031510849914034200c030100d00a1088003c85001c04005d0004002288045080002d8042c9400082c0c1c80000c04001081c048142800b410000d900c2948400409605d035005110b801c40444000b14045440e100c100d0300010390401c241c9030000712495072a0b212038000b6010205a0748144131030203c40c88041050440c0e0310780003c10505030f070701c00ea03018071541110488400a540c858090011190030034014510142816849007101e4440140003149103a60b03004030721074082d50043c1400b110b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 329830008 1250 329828758 329828761
    0x20f0d02072108070c140a1a0606030420040b0a0909020f040c1706030309090420030a0c050603040609080c010b042702010807120f0509100605030606060c01090c030b 73
    0x2c40069592400c40d2034a129910302001c1501c80101841001041035081c4900001c801c01808a503c0041c11001503050032280e1940b100e0401280440b0001c2c66100100c00a0002418074100081643d00466005031034405008200d8180103150305c42d902e8042d0003d50303a0340414029039405c10800003c0542d0034001540500d42e0051042c0514030809140c003a40c03d10003026460747d80704040d0f032001149880c0140d02507d59800080c02c6102e02d41d00c160340041102c09000600c204034140c00d00102000c100030351101444014151128140d1501606244404000b0495420020001c581c0a48907001c0001c55460540e184200d507044603058010302d81d503646940030182002c1c428804084c04e010015074010071800640c0c1c180c9201c448000f81000a5000806e007018040da62100c02d0482c075510a01c40b440d603100d1900014901107411440c20705c070b003c0b5042444903d80c491041a11005405041030381d94500600c02c3c154050f1001103d29075a40c80c028000c60704400e6604040d5108590b0f20582c1d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 329831258 1250 329830008 329830013
    0x11030604060212070807050409020903120f040f0815071d030d02010204051509030604260d0c09170d031109121b091315140f01030201030507090b0913020f0d0207 71
    0xf04100103101d50305100c4604107224980c1c0e000402d84003160021800036a40d17030030303040c0424188200c4904410302d0036408502c2c0b5a1002c0c000c0b025100380d82d112429082c0c003035569070f100c41d6560209407600c0e45000034000401c00061085a5000d9a0b074441011a080d078000704021900d042d41000d203020050b50701040030310452614030791a0709039082c8041d4107407c165900002a44600f005031005014102d42000c0003030318040100c4c00d603002d03241c2c0342403c0d440c0c13024030705401c01071f004ac46114800500c1040c0003240303861010007594580e4401c02c008042c125008502500205502c4d0001300a44038244038142c5a41c7d941c0008003c509600c0e4094003641c03c421030b461240781494101c0078401c40b101030401071200703010000318072115001900da90050131940c05181c014101ea6841501c0c031070050003048100a5420a2036048034803e0368200007640ea2200b0840c1d43d0f001c10b00404000700703401c10451030a85000742103000c0400c80b085006281070748000c1e505000b42d0140d42001103864012601006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 329832508 1250 329831258 329831287
    0x72d0306260f0a051002030a09020d140d140703030b060c1e0f0a02030d0e010e10020609060906092e0203130510060308030f100503010203090c09092107110306040602 73
    0x10800d00b0040104802c8206907a0503464081c9202c1c0f1341643d5a01000141011000e50420003069402070f05088040646040859481e0b600c0710b80c2412500c6010085440c05100d1610500740b82040f180b11410200950340c12030241003108800c41c1e00002c00d0100161a260903c00c6500d4141c402410120859414072100e05005c40011101c040d0b4110000700b401580300840c0a9a0200e924a03201070001401d000581d1510030180342c01e60042124100b0712102600003400364019072200c0c00310b0354181da990040380d50f1150100d035100c4131a08070080c4404061075000100c0c00034041e0610516401d03500c0545401240c2040310300e4050700d020381b0451810f101b014800b882440e00345071401d00c81c450450300e41c4112440040c101002c401d03040c00001d401320b00910030300400740a00900a42d0b580c1008410385540340e141510462080c50341c0000701d40040b00c005110500003d8107000404886192411031039030741c1003040141c40d4400d00c2c1208104607641405022321541c8100c50051b04c0d590b50b072030002c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 329833758 1250 329832508 329832523
    0x9020f03030a090b0c01020c0102041701150503120703050d15030318030c0e0402010e0d12180e01030303020c25090533060706060e0a05072d030626 65
    0x40c025002080840807039a40600100d0580742c14034140c2e581c03215500c991a0081c445c1500703400003075202040120300c000301d18403050203042d40880248035256100510700ca21100314401d9031381c594403a620240510314a00090309210340a41060f5003003401c0d03010104103640445a03490f660101800c818820190440b0319000031419601078109201d013103541e510410006030040700f000840201c001404c5a201c0d09104004c2803000e804e02c0310b02d1225151052241115510300d502041c890f803140340180700b8a4102c45c003228148001c0c19510707461a00c040d0000d50001d80926280c2c01004a001d829560250f806d484407a2031008042c030707461521000d9001c860000d081a08044140301280111036421082441d51052590044580701103000c0010010310034100c00500c2141004030016001e00300740502071203480c84540510003582c51a00031200081c01802c400000b1003801080ba407100216031010704419803d05000501039200c00c108a0039080c0c20348440350100c1070803100d0020800030b10096 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 329835008 1250 329833758 329833789
    0x708010b030705090f360105030a05070513090812040b0703050402031c05041a090301110708070b040510050c0d0e0f0d03020c0705090112030e0613120311010c030902 73
    0x310304600340020024650702c680290329101381c480f00503050b8903a5416454580518850409410a26243ca0f05001041140003090110706c0d080707000052606000c500c4000705980303c0046e2069038103203070801911041841080340791560302c0b25000002003100c5c1c000c21481800305507003896403900b031810f00303c03164009120401300b5040209110040c1c400040c40a424040040d0002c1005680765049501d0b00a0b03034000c80c00150403c0c400307240703440520000c180008084c0d00078042d2002449402100d4410510010601001001604007040ea4680e5041c4c200c0d11030015a120805034140000a0720819108030a0b004130014514200780c0c02841000503211818018001c280f2108400c640c0340c8a2600c1100c0503d900000ca04092417402e01484c000351100038030000d11540c551082c80c142d88800324003280481c21040601c0c00c40e02e040800d5428207160061010f41d22070400f011114072016011048040c8000300080350b802950a010307110304031880e954000b60680d814010031841ea814140103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 329836258 1250 329835008 329835029
    0x1050601090e010b0c10020a030c08010509010b190306050d060605040b040b060d0b190b0a0206010801050c07080a11060411040c0905030606190e270d0e04051509040b070801 76
    0x200900742e6984591811650400c0030f4540310305040d0541420700c00d04103040544d09100065400031241c066008221050003944e0702041aa00c480502610319000c0c0100d200c511414401915242900c141102100d011442c2c0418800e40e240b0118a40406008003102d5103500c42800b030201381803500c124120850100c44c1440a07440c0c0f000803903020712582002031000c9444641c814102c3d02c80040c046a55034900c0040312415135a4450b000898214240300d40060081e600000f07403c0c00c0500446d03000d01c400d981d019142a03040d90b03454540b03611002a000a0000c40707078003100442020700c4050b1045000d1851514240704203c20041101c40310084030061040000c1d050205840c0060070715440b800540b480c41148185003559404547c203076026071070310702e0314004105402070204250003500314410384031001a0b0040e030445480d0382c42e035486503000900b400d140f5001480c0c103800c00d5400540e58a030348005603100c0c0010500c041402c48082e10180e0203c4280022183d000d8002401880c9003c00d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 329837508 1250 329836258 329836277
    0xb030108011b05071106030a0608060a331202041b0c02010e12060402090a290910030201051207090b040807030506130305030a0e07090c0e0907020d0f051804020f070501050601 77
    0x4661980c01703000800180184000320000d0304004481d400342d4080c092090440e412454500c3c02200030308040034803200c4051040c4000f40310b01400450482d50358142491403104c0c641005241e01c0b082803c244c05036841900ca540514440c1d07450501314148664550300d4104c212400c0c0005401d90004460143c0210703051854032107552004900e440c1c015504689404286c0c603540d1000c2c014200e11012540c200c2000500808a4920002440e156200a807200300c4d41d0341e2149100304280079141310282c040340c81040000d029504550701036503c205103040009003030380ca46c0301c8000309030016005240150300c000018000c0c80001c21101d54444800c5501c08101c442d540da006055010140007081c4198681e0007250a8100a00411015043d03030041009002d42002004040000c0c1e42203642c0100200c9010030450340c03003c120540a09455220101c9014203440700303d6070390303020600142d140e011519103050a5519800200b81c80c07000881803e4450720305040050854401070400380c140001c041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 329838758 1250 329837508 329837513
    0x403120f020615041d010c05070c050307050904080c0f1b09010902091c0305040302090703050a1506050a0f09031403130f120206030c07020a08010e07090509030403110a0b030108011b0507 82
    0x161480c3d0661800d0750b0200d020050000c1400005000d956102c80f42c0d4240303150326034500e612401801445014495102070544e4860034180c682d03500d030107025008020800043e000c80d58410007403082c40b4403102180c0341245800320306410480c25040c0d40303d04842c05120b171440c0380b625414203409801c4101c3c00b189028121030004160442a208010040541c0039400003490300802c20b4800440d006050301429186c0350b00c00800911046484074075907498179440701e40c5161805c900784192805a06c415144c181c400c0016a072010710f209d80041000325440c00440094802c01c0500701c1204a20015521484440252062076505070007074800003080c95420400c0c0310108003180c43d45501621505d0740c0c1c1c0c41d094032400040c462000081d400c8198040f00243d420015800861904045400d44460a445440840070788070203655004e5203500034441840451a40e2500142c4404020180100d00b540d80d441d2a420b0380090f44407048996590028004888514140d00108061841e02607d01505907 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 329840008 1250 329838758 329838781
    0x606090b0f0a030f1b240e0f0405280209031e1207080c06090f0712080f090105070b0915010f061d0a0f12110103050f0c030604020f0403120f0206 64
    0x1840042d108401c400006014441000700000705c00002d200c0c600041c68031070303401140144000550001031140c0000784203125124403d0140c941c1c2000701402c011401001c104405080085c155540e80343e84040382c00040f59020b03000c1000700210346c50140e100c50061041500300b140100c2c00c2d41035400402c08030003e04002049030079100c001610f1468032402141404001d500560034145000d206107014000250300c006042004000401c0c02c440040b0707250204404014480d1074018400383c0c1c20f102d07100e000a00a170190102181c180b41460a000845c0c035101000d603002da450f404240c00a120046805445810320f60240cd08115410140707858110700400d031604580e81901104040107101005580e03c080314401851007000c40594151502039040206190b0041104c0c00c1429411000300c65020b40078440c4114140d20a81c9155581d909402800c0c0e84000c3c0305581c030550802403480b6200c240b401a201441c090030031030380300000b060130280c5110441107008066620035000c008515512 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 329841258 1250 329840008 329840029
    0x1506050703030903051204031101110a0207170c040903170c0304170304060e07062604030c08030702010209060423031b010c080715020a02330c160606090b0f 69
    0x1524000400e0250340c1000c07a0310703004014500f517600c51050207207c2410b41c0080c2101a044100f8000c000f00741e50300240b0b80b03140c401d845103000940c01c4030404104440d1050080042480d00500b40c0300819900c00c0010300b00d444280b02240850044808200300840b00c007400f9900c1040240c1592840c28280c40d5503519035421190300d5a00e000010010b010810540c100300c8a0f180c00100302c5091646460300545200b401d541d207111140c0d04544180340d21f2503900041c0380150f80540f168803010020340c680040c254802012541599020032055103140c459400400050000600a55a0709401d00340b00b1214020b4600041c8a9445011008281d072800c1e01102440e92090801350f480c00003a02d001c088034000c05101030491090410072255050454000740710b072600176400e44010b20841c141e00744c90b4030002803246400901c403c6050180858441503181c00000004103141040e6240036040044044071104944060b26150304200c500803c7c0290b0300031400440d00054545002004560764018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 329842508 1250 329841258 329841263
    0x50705040317070c08011a04060e0f041407080d030c3009060e030307081308040311040615020a1b05031b04090b07020c03160305030d0903030e1f15060507 68
    0xc100e5111644040e102c0c0441c0c0c002079000050410165564811a00030301142440d0b0300d803481141e0600034149800c1c0b2401064a9500b140d0a0068490300403805150700300034012203404d8407110142d1081c07141040210014082c080041082e0341030302400406448000c0e42c85c03003d100344418004d00784801202400c0300f18200c10f20018103521034aa00300003404041c03c000c1d00003850000d40c3c0141c42c8020004500ca40c8040d1210315103602c56842261b0b000c81020406844040107000a100042120141c03008085008002168480d02e41c100c0780d48403031058140401590010144030204140ea4116903250014100031607001458500825185e0001d400c07206010340b80d40c000c482041d03440d80e00c0155541c0d00b0400e0501586400c0c031010350742d421800c03a4240302744562180c0d01c070302e036011b151090b040c2e1398030a01071402c0500d00e0348810701074504032204400307042d00c8000c0301a00c48420040a0305a40414040d04540d2140c01d04500443d03d14010b00c003420480000103002c03040d0400100c844107517 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 329843758 1250 329842508 329842523
    0x6063219030609021503010605030a0203100314030a0f0906021221131a070906030b0102102906040303052703030403060c2c0d0510050112150507050403 67
    0x488900028a4400d00a640404a85038448003100303120495120000381c900c00d440d0644001c8280000d1802c1d400248202c0c40050020400503140402e95009103800055448100c1c007040d0303c9540d403128880184070003100c3e030352001c9299240140d12a805c140301d80038908041c43c025090000094444c03101c007888d041c600b1000144901c21820040d0b120041c0c1700d0a03584000c02e410541030320703d95006000400d540900000300c000700390030402108140a522241c442c1c2d001c0c64a8004290040d0281103a1103040d030140300c030b0b00040303128140100485050707001038140340002d010b8a0114600140c40c1194000c0c1c205000c00e100280e0400101c1e02c4a0482c04c410510380202c1d4000090b858003003105803501400041000030403c0355640045652410a480d01c1c00c8069104d0501d0103802120034002c04d0700d0384281d400404a0418524210210707020f0001d490500e00309041c2c2401361103082e0700209060030b45400201c14440c1c03081e428410b0ba102d444043c8a2414680302c01806c3c3d000e54040030b030000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 329845008 1250 329843758 329843849
    0x1111009240e060123120319030c09090902030a0516051c02030a06020c0304030813050103050f2401020c04050f0412020706090b0306060c0a03020105100b0703080a020903010b1c0606 80
    0x2c05040701790001e101c2009000343d0180c048150354545a070880201402114800410008641d01a0294582101807540c90001d44c610741680040500121003060341c0502503406100e011030f80900c00c90303540141c010720140c003042c5410f092115003038175680416100501c06d100d83e00180e4001c5464044950003ca02607240c2465502540c2940308944c03000b07104240000704144800c88007100401110b00c00d803070070899035464102414803680c0c02c4079084c0c03080b01011410040e10001418428086c00103104940008090380701040444405a0700301c4460f084070710411040054a2103800042c60701032019106052800e01301400c4504c580c0614400c1035070110008507140c458801342c0340400c16075801c894100d141c0c0d0038080e0082500799851074400f00e092402040020140040300c04030340d41552141d45035034407064454000d412100c6034a515540307448850580b584d5051040010440d66031401c2501602803616108507146507011066400030752000d51380000e2245500741d1802c03504a002c0c650b8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 329846258 1250 329845008 329845049
    0xc0c120c0901090903020d0c021c0c120503031b0c03041710020301031a061e060d0e010203160f03060f1403010608062409040b010501111009240e0601 66
    0x3042100845103400104075800003a020035150801c1c90704500940944480c8136480310304540c0034107030340000b0350010000100491401c0a00c001c0201645c094810340020a466542c441200c0314885030940f8a5440402808003000d01041c0180c4510084030060b85403165100b2045c0c1c5034025440b615428a60001c154a850582444010f2107503554450440d039940e140d180c0101070740d5801c20141842e585038000a0a01e0400001d807100244599880c800002402020844598000785404001c59141c10244030900c2c405d00141d4014540032844440c0c49821080003030000040e20054420142040d00410245002c9000f4505903000002214241d901b0040424094151a030200b800781c8141c0d0100504c102c01c85524444110740d118000402c07440100420074044010f075809000d4a09007030042240f90b00485c543c40f801c0c0d0300003095810034282d080c10131040f6203001c00203841740c0604108004030450013241c5010300000d070000810a102122603240c1d5103c005000301c1540c0014002641c50 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 329847508 1250 329846258 329846263
    0x120c0315060a030f0912111614120f01091208010b0318150f01050307050406080705041503080d02090f1c03030b18091615020a080a0509131509020c0c12 67
    0x4c0803251100030301942107589880b00f2460b882e800488001034500d100d1407481d150101d0081c0c0ea98030564458543c02e130503c500d2000e194055040d05038001d0001c0c43d4481c0584062080641d0300b0038060000901d0903071030a00c114000103003105601008030080c0140501002c000039240c00924421410310310380d0b9142c0301d2514003007401d13401807907201e500010401c000c0865190241607403025402c0e6840c1641c6c1d1030901043d2040750244551b66081010284518240b40d0700410100c01200c0314402165500c1d00c13003201561214906140060700000e0f4201c0c1070500d1006000d03111003e4459a0020000c00c41d40100c0301001e02008040584070174040009956004400d58001e040c5071108450b410814500d950310040002182135524143c4030000b0400308102e80041c40440380c0d0080c08405216a942400540c0107136040420b105c0f0074001c000b03071500c2c1c004030800960300c5d000303000503c489134154131805c4071610f9014181c038900410854030506004a58401c034220151066004540641c45050 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 329848758 1250 329847508 329847521
    0x903030203071506270c020a0c1203020c060c0706020607050405031504061b03090506060906010c081309061203020c0307050f0103150518041a13260d02120c0315060a03 74
    0x1580038142c191803c092950302032000080f62600c40030030054241c40030036a200c001406000d42014120030b270808c0711020444410300c1d00c1b8800e205903070724603450b0400124150485640381d5066446070030140015034040103c1c075000451814854241407a01d00040d6a41e49202e545020004411020074100803e54102c150f0310440418800b4031031a00400050050041c040160b0b41880b882d000b164460401041036070244206075250001855030391220005a44082d888031000100c3c05000110380c410380c465a009080d800d50541c0c1c041002d030074000d01d001c09142d01c4030b110750040001000390350340d02c0f411301c1242c00d02800c000c2045001c0c56076013021140d155100c540c100c0c140c2c0c480a0321002c0e03801c035600c3c422841a0b098a51440303d001d200303550290300321221140c0030045800c420108001c5c070792f00704440104800e800802248580305450341e41140e410700807102d401007080a0400d0040005c6944108090075480c15890106040d280900d00c1000c10f50240400085e2440954840c9d000103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 329850008 1250 329848758 329848769
    0xf0d0b0402041502071a0a08090a02090a230c0414010504080109050a14030408060601050f09181008030f0d0905070308070b04021f0c02010f230d0c0903030203071506 73
    0x210b440300e946075510a00c0c80c2d40c41c41204010300800002007451700791b00c5071b41e0944240200390b980c20700c88104030076540710401500351900e5229658000c80180d9501c501c041c894038010304080b47e10405500681c92000c000c1c40072141076903000c0c0c100a5050b410360151001c0710752120b840c14401c241000141d03040d1143d504050010750070003c040007848000143c2d4082188070340f41e2048800e01000400b900c9008500881080d03810800114465600c0350703010340340a105409801c4d06e0b244218000035131405c00f0b84060000340c3c12160404c900c0701c2c00c01d4030740c00050800502a601c2d00ba440c080d1440103204940c240c12040303940f0003040d030078000308001d117001641d844032801c0d6a594250038500c0e1401c40440e801c0748609440700e288480421005040304c000f8540d902c82075405071580d401540c01003104000802007101901039886c0c595031308400d064820a041c20035590710361041c03041e0020303a442848034000b0b01004401c204002035001044803c140d4001500e80708101010005d2070180202d035019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 329851258 1250 329850008 329850011
    0x31802032a04141f030b0a050406180b160c11060c160602030405040f0902010c06050402060f12100609060807050d14010305010e06060913150204030b130b06090c0f0d0b04 75
    0x41054503507595405401960307003030b034013007094402c0c204522407a1100340001412881d580001c00c1800a907600940d401903c62407022030310308000707a001e01e03124064001c145c492503210420301004161a070800a040e2241e80703070501110055443c0d0035151143c100046002c1e04001a000040400c20700903580d4072080c0f8a100c01100d070352414001d40e680c22a0082600c6585440c440e0b0900c02e4aa00c25802c3c40365040c0c40390042030800352127201c028100144141d1b048001040154540b8462500800700a15102156030f10b07030520880d0703450242180e030050424810400d4082c4203c2d40c00010659010504e40381c0190b544080328050b00c0a480342078818040d0070800742c00801001307010340212518500701000c0313840c5603484100b001403e070001d407603205050714801d501d200812120707281111000486100949020740e25030b942d2006407070488a881c49141910b040b10704006011381001d40003141210702c8800307070901c1e0711320004c0c1e0312030760308216085d980001d91030820b5600c5030442a00124001d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 329852508 1250 329851258 329851271
    0x60708071a100519050108060f061303031b0b0c07080705160810060b04150306350a080a050a030b09040b0117060c0d050403170103060b01031802032a04 67
    0x9140108050595000180c00200741011400c2e0030039211241d0385400f119958004c2c0e40c038020040d120000302800701c03074008558180100d041d4580e400203240c190103051014500c18a1424002d0020024016491880506101142c00310f80104080c0340c01418a40e520343c3d40b00035520308140d00c0e100d4010700801d075000349525804400303c43d04680c0d04883c00d22007610702c072810010140003201c0c001c1c000d803030b1966400d000600c01e100b15110880c1c410030085c18000340b01c58a0703903039800507400c2c030f80d003025050349025070422000c0083c00303201c4800e14201d800030f00c01510f0b581c0d91030301c0c6402509444002c000c1d010980148440c841d030072000c0901d50203810440c0c24101400e14488010003400703000440d03c0d03044805c4076203180000b10a0300c83c85800c0682c0b82001002149103001d440060f00940800c041d0b8018000d0002c10461014001c600c517400000b28141000c0000d070550b1800c03c02d4040e0110f1561809005d80c4010034456040113000001d40300d0040e9035003170420500001850305810900e03108 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 329853758 1250 329852508 329852543
    0xf0601170703020306090c03060a03030f0504080f010509011b0c080d1805060703150302010c1b0e070e0103060e0c12091009050c1f02030a08070507081206150c070506070807 76
    0x500030745c0a000255444511550386550b642c06520041ea038054000300c2030b034801c00100b44500400d80d031035003031403806501e010b80d100300592400e8840780701c1c01e081c0d95498050100e005c000341b00c0e000009941d1059400014031801d400f401c05400d80300042c0200000154141c036501060703001000a10192808000415040c10701503a11282111204046407a000074004034581d03481c00c410843e035050b9900c01000c0d080b65078180540103684501d180e8801782c0385006c6335040217954251310844d12039540303010545185000400f9100709500109100182000703020814030702c83d0449404459500e194120394445501651401049070703440c1e52181d02e03000108082100202d0400d071080800c49200300c55181c00030b00d00e01030300280011030015903c10000d10500c64000c41c00294010500e00307140e0709002007501c2e0318119274048100810720b60398031020403255281000c2402800c8070407000c0390341000380185c001e0380d0b80e030854010310348900404140300082205100803144140d5000c40507005034451070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 329855008 1250 329853758 329853761
    0xe09040b100b0c070504020c011d0a0c09020a0c030c15181401060e04141903030f1404050c010c150f050106020d0f050306010e0616030203030118060b030f0601170703 73
    0x98078103601495411800280340780212080e07612110b155400b9048880c42c250800000f50720454142c0d0081d501c0d5910503000141e800b03a04a807030304d8138002034000c031706840c9400c0400120300c0c0c22001e003681c0f041c03000303c0d800381d48a1070240c9990b9050038182040c01150401d00c5040303545001041c003890500075022000c2225109a21301c076031140b1003240c82c40c07121100c11402c1c0c805600030340c0b2400740402c0010b03011a8040f40c96108405600d41912030303e42c4c1e46000950343d141009030030b50101e6250210b030600d0350b501f8071a030044c600c0d016070010181c1c02c090f0f49007500d85c80c803120428104544c05a04409002681000040c00454028200328503411100d1250242c0401d01c07591300907010b0355600d860094004c01100003094004e036200d5185076107580064039054006880d00b60007000070b100b0504138440b182010104940240c00442d120f600d00700e0304884014004416038519428102c003040341856070b070280d903080380c1060016035440e0b4544004030742d10360518001c8240362516209004c00d19816 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 329856115 1107 329855008 329855011
    0x120304030513090c051216210b030307050c010801050303120109090602040306020309072408010b0322060506010206340509101d0102010510060806010e09040b 70
    0x4034000f00e02110a140d03040000f0074800982c0b41c8640491480503903000341e104a9075002c08251003c010545040d101020040030142151003500313007000c1d000395801000183c1200e0b00c1d50103504080d40d41f441010840d50100d00d4840020800b801c01000721000074000e07014400403a4607118403070f80140b00c0c010090354015400e010110005169000560107010a00020f02d8114201225811100301d20300480070f0040220045684175a000103286044604600310f19407203031341c0c0f4076111507007441b40c02400b002810902c18031410450103a001c240102401c0e821a0713290350b0344d6585c903034144810700c050003183c01050881081d44a003104a921a94205280c89402c0200c3c61380412a00c2e4640107110380410811060380c0110b030010300030265065400d20081c0201d042c0810309448010090040108024086000030041d90050078400c00c01c600141955941b4a464100070f02001e0f0b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 329676258 329856115 := by
  have h0 := BRFrame.cov_init 329676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 329676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 329676258 ≤ n) (h2 : n < 329856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
