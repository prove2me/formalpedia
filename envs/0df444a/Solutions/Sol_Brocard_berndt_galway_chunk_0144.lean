-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0144
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:05:08.991771+00:00
-- url     : https://prove2.me/submissions/1e578635-7d8c-4127-98d2-3ec290c2dafa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 25719430 ≤ n < 25899286 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 25720680 1250 25719430 25719437
    0xf0112020408070902040312080603100510050405070e090105030601120311010f0e0a05010605010f0c0807060b1003090b0105030307170c010b0307031118091002070503090405040606031208091b01 86
    0x1500d0b40003151070400302c2c2d0822000e581d8001010307c180b150300000141c601640d464660414909040841d40b01c0b9100d00c0f940010b2521413002c55906031323800c0100d03401360801030420421841e0150008280c034214907000b0b03004550780800400c3c1800c000c40d030941643d12440d9a0b101d907809a503012207881121303246100103950307210400c598889550055a0304061800b008010016007802c04c00d0864055901003414881818400701c243c80d04011250400b5400ca84810344981941c01c007900078001441103140d1000f0001198400140c040d031094010303901400c0d0382c40e0716a81702c2051668900c02c0801c0600314042110046001481d04002030403120004d80011403840904070120b0f1811310950000c40d0a0908104024402c0c141002002c6090701c0c40e058100e0346e41440040b05407500020310000000075000100c0c42d051100401c111907182002400401c01c0b85441c3c1000c000501e8140002c640c4c200900140d07007074140c811013007180101c04031005003030020042070200d04007600310071009051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 25721930 1250 25720680 25720687
    0x60703090305250b0a08010b0a020f060408030108010606091a03040c03051507030507180311060906030c030612030a050a26160809030a0c02040506040212010306090b0604020301050f011202 83
    0x3070301400101260724298107004114204501c81e020264001d400c444201c0c0014841c041180c0d50000481c0e0450f08d40c9400c82e50b81c4c45002004070304140d5070540c611031500c500800c0c4000c001401006504036504030f00200007036a00c1e0801240c000e40248a03411000034102000d259064041006680062140301c205038a07aa403507485a041403100c210911414140d10200082c058043c0156640700e04946007a04107501d9010306505008050300016146c2c0c09042d08144040c1c441d80100c0c2c1c0101c0d0000c02c0e05807641703005480c00c00c2c2e552081701e1450007000f0000e0303000d405000003c240d030000f10140d100c983c20240e080e1402c99030780401040c095401d103000e90345548102585c0b2207441c0a06800f80290b07079400601c00e00588400700103000001c1c25401040302d0282d1984c0f041c042d9201c0e60b070454000c2115200c480002c1c029000d002d000108219008000008100c0603a212045007485006240c5244c3d55034030420089020034801e041d00301d2501e0b42103c05541c404c07403100d07289601102c0010304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 25723180 1250 25721930 25721933
    0x190311030c09070206040201020c011b0f033605060304020d0b0903090d030503390306060403020411070605060904080304062c010e0601050301020403030207060513080d050918040c050607030903 85
    0x811903000d850703500168000e8002c6c0410755a05002441406800b801d00352000f0224240c007040d41e484001014100502050400c010588608042c4100d4412140200c0404016500c50030014185101081c880c0242d44070003d00e1703091503003d0700e10482e0000c20015201c1019240c440030391900804c94241800700304a4800d850391041c0b04221424080d07a04c440d101d242c848148124024802d07040d403a008040161200c0f81c01011603a9040742080407c1c1c1d5072a40c803518045042e41c0515000207501034100003c548588203194007a047c20380c0240d90620440d10340c04240314060000345c0303000d0603054040001174085112600900c070581340004101c4e604400301c080070318840f66518189881030b519400010700b80303c020805607024007800c90085141038034658000c0c2d03442e480c40c814070092120118a140f1a100d10089600080c481e03c42a1030208041650003082e59100380d2040d88100952226108028682d040440c416a03122280210050502c4100041034102090071410014000340c00b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 25724430 1250 25723180 25723189
    0x816051c080c0304090204090b01080408030610140f070506100311100e04050c0c0111090303090906130504210f0207090f021b06011a0307080c0d14071d190311030c 72
    0x10103800c60016144d500f86421300e820380b00c09d048040e0420000710b05100200d4244c404583e0040d00882da007540300440c0210541c1c000d8510200d41c0344510000c1410803a00443d0402880501e00c503a041d980160f903070480f14200070340c0500014000f035803050301410083c100100f1003024188141884400600500000307000c3d00c0341120000e030104001300c0c206548107401d0103070442e040000c0e500c842c2041c1061002c00d560780244404d1520071328100020070840e854141e0100050568008140200c1c5058108920070b50202c40d220001c4880d03202910304400e100d1044200d0a91407940a010f1075441c200100c0050001c1c1f14035031160f00c1d82000414407070380c4e034080401e52400c00e48001d804150b00d8034905e007100740361084003004c0c17401c1c04004008201e07a10440c040d07403140c0d600c1c102503102e040ca100c003400200644040c00d69140040030920120b96005201140140d0044d04680150600074060011040c0480041482800c600d4170900000704110031071009140042e0403034194120150016 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 25725680 1250 25724430 25724437
    0x402040527010606120c08060402070201050405030f0102032401120c050903010f14010603020909040f0f0f050c03120406170406020d020a08071107050f100215010803040816051c080c03 81
    0x72100d9039942d8004001c42e0340c200050008411546404100341c2c000d0f0113015285000080c9881c0c0314540c00107000c0116070003401a14040c0001608403200c3d98a44041300303000f90320039100c0c041070000d040b12111000402902e4120301d03a01c1a95205804a50407079188041d10841c3c0010060000501c850a85500c0903c5021240702d00345001081c516414900400d014006030030000806004004441c3c03161111120550051351001c0400d040704010b0030000c1010104480082500e106249650148000015400000d600071010303101026003c958540082c45584510300118440080014070400519000c60303010340903240141c0307021003040d030460032644184226004100c592080c007074403c0e07025603000c0d0000c02d198001c0074242d08010016140050703683e0154450700114118503a481d1081c000c486242c0c5180e40d08942650311018840e03240d13041800340a00324421040018900d405101d0810b0072980090304017006c45c0c61002c0c08241c4140700e02410745002d4810010f00c8860501080103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 25726930 1250 25725680 25725751
    0x510150c060e03040506040e0c0d060e01090e0604050c040902010210060906060212120f0601200f120711121501060519030c0e04051b0d0b10020703050604020405 71
    0x8180c0c600a4600d0403808940303000302c004070142c3c02408180010345400041320140d8681c00703100030317030f50b500c0101443e558861066400109400d22a0000f1030038052900c040c1171710640f140500c880d50745c046007503070783d44400c44000d800d40e442201c150040381030640c8001809030061040e03030816103400705802c0070798030710398054480b8582c0da040801c8003603414000407000418000c9840d140c02d8504117031903090b04016203c3c0e000e068500000c0350250b80506085402c0c1041302c0194140c0078600c0d54a1502c0703196008101d051802080d01d10b81d009030800040390801548440100090304c40d14050014201d0781c804030309010310540da109808039000340b48450003440241c1c0c45564509841218070403403440c03a400d00303003030508000c142480c068102e003129010440940c0c00081a41c0c805c0c05412010845140d12031908200103000418900306820484020406841800f1101c244a404a0b9504d10701e1101500341d8203c900406c005251540009030080000703088500a8034181280c8000c83d5201c500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 25728180 1250 25726930 25726937
    0x50f06030c0109060f0e0a030f050a110d02030304031709090a05091002030f0a200f04171203070f020a020a060e030706030b01050d020c0a08070f05010f020306060706051015 76
    0x40290500d41040200708400083c41c00c0003c00340f900c58081c0c40000081d0442c0117021005040100507240c90121100030b540001650704403030510b08125881e010501403c4e20084058400c980d078034101302102d01c0b5055030140c0194905459519020b90b074038660700c80360f521345c4c40070000e000c2c1c00c1d40c90019490240b42c0d10700b00090741341014001e007850440c141480300041d5005000b08080c50300d402c100781c1d0f40800c0304034021909001100503040d8480807110000388152010404640750840100030f03009032a18405440786000c448051507641d014000344d8007074103400820002d901e0500c1303100311b482210700600444504420300d500084081c09150031040000d002c10480c04e20710302c2c041019000401c102e04041001c40b4025000910501ca02e2900030286900001e03500682c90b802c201c00303d0401d07004440c060712000b5502c2d000c4490300c61101b041d02c8540c244107a03030990060364400c9074003849000304494900b849a40d42e01000c0d04008049074120700804a0010b0061100004981000455035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 25729430 1250 25728180 25728211
    0x50c07030605190b010f050909090a06060603020405010206010f051c0f15140a1b0e030a060606030203012c060d051c110106060206040203120f04170109060c08040b0615090405 77
    0x83c0c07801c201e84041c22214104840031710308203959a000021900090400e481c0b00004c3d640d00004503141032000c100042c111485d104001820690640c085c0040e1813090382500e901d646d035400c6101c0f14901c2805100d83c0b040e551003803108110b50b9006076002e014816a4052140c0419072158a0b03084003106004040304c2c3c551020424001d1907801d41540403034800700c20410b80e54201034041d80080070040007410721000e004141c40381d540400c292640c203a403048060041c3c4d515040c004001c1e400a03c9903c4031095200021283c0340103400100c0c401c1ca81101c8880d00c2903070f85000b0403014189004c02615140100c500740c003030300b04107a41000c0c031806a640718409e041200070728031800c40e41c01d81e01c41800c540104082c0401070341c01281c45692502c2007010f207030301c52600c10203080140c8207551200d4040e07201c43c001f44600102c103401460866020f043c0400c01c980310114251380c807050845000f001302c5c0f000f200103410707480c4c003c3d0741d030313145200403d1442d043c0700702c0d50040f400b203074002c0d00d003850341d8031520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 25730680 1250 25729430 25729471
    0xa0c0c0609060311070c03080c010b04050112030806060c0318130e0d080907050307050d0203031306080703050a0209091b1c0605030708030a171f090203070807030c0e01050c07030605 80
    0x10302601d080003c40725a490318009035500c1b0303201d0f11440c2d40002002180c00156800304d160382504050341b08040204100500d595807080e040340319034886001c4003c101d5a0700010403510303140095072200800180914070f402c0900300d65200030301060703101036070000e801d040783c081d0801c052145000b07103289540280581001048040c1413640001c14150803540300b84002d1041c1c0d00d0109110003124000c0c1c42c1c2082c280300910020b411360007441030715607250780301d09800507806030300c283c600d80030350b040d1344042100f5200c4048007c1644aa01c42c900e13048403e0700041b41c0049498010414146035041000d1700b800724854843c07541c0112000403010054540d20140000d1600b8401d00300209500d000551620780130303a402505642c10800c01c01160086940058031020700c842d80a040040448286102103442d5a40940250000e807a100c000a6031400040c414a020b44552110b00d4401c2e00c503010090005001102e10394090381c290051030023007420000000710140102ca0040c1000300c070070315014245 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 25731930 1250 25730680 25730687
    0x50f0f09130e03091903060504150b03070302010c03081e0c180a050307061103040302030106180f060b19030e010e0708150103020a05060702010302120403020f160b0f0a0c0c060906 79
    0x1810320301c1d00d0302480c01505400119001048600c40d83c010b6403260850385180c2580e034008416540060000760a020804c0100301008000d86c10100248800700300003030806052540d10189030100a01052a201110006c02d01910100b64043c00034410751800071450248085250400c0d601514101d60208a1216035403031510280b19440042d161036941c40e160000081d5900c40f14172030702d400e100d4500714490900b0000d00890b006150050001d001c0030355142c180920041c00c010139844035034039040c0b421413540d0850140c1c00440d001101040d04020345091207210742d028481b1500140350307031620001c500314404e0054542d40c15a02c0040c091480c81d001c40c05003881900003510b0300340ca11120060005a5880c0569000d4a0007501c0840c0c4071007007803005070000c0c4148904402040303002402c00080603400512850079444500c00d072980c0d0351504c06202c0e40700d240350043da00c4403407040c0100c1d5480310180010b8540b055072441c228442940503140d8000788440c3e50000c83c0014a9400d0030301004c1e80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 25733180 1250 25731930 25731949
    0x210e0d0f0305150609131803030501120b0a0b0d06090506040c150c080d0908180f0d0203250506040914131208040203071a09090604140115050f0f09 65
    0x19a401c0034880340ca0712810000c50b01007100708503840707030b00c02094000c3c841e00c407036109020001404030104503904c8091181030720b009058a0072000641003100102c0d0f2100800101c0c0100343d880103018286480c0c210000c00a8100003034540e4000e2140280317a004280280148002076000707001820080c2054185070008130b5458000c250442c101072016400c095020280844441d00f054020340c4603200c030340240000e031540190142400001203030042044205e00140c8411260031265007000d0020b22081c040720042c074240281d03141c2c0000403045e030404603005004e1911070000b10240806501c0b200020078a4000d0307041118174641e1104c0d000d081c00106c103c201d030010308a886d14079030010159641c808410b1141d69006c108031000b0003040031510100190b00241040e00c00110101d43c00540440c055000491203070320805144001c10303020b0805103d162508003400e801820140e0800f80c004c6400d03c80070044908010b01040100ca2150005015261a00103807448540c0ca14208007048843e21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 25734430 1250 25733180 25733207
    0xa030f02041a15030c070b0906370905070509161209020a05060a0e03060a020706060e010311090c0c0102030408071103072405040906080307020324010501210e0d 71
    0x2401c481010655860205808000240152180d80c968505080292901450038000c003840c9110003801086423021401d20300c80d4400030090540c0500c3d40c0b01034aa00440e880410381050201c12504601150541040d01c4003030040040b503607901c0c0c2d100041000104100c074100d1404e100b0206d05a40d4590103803a4101001080600b0f105140540c3c0024003000b419200d0584902000205c04a4841c01800c0e420000c0500a043c2d03622481c0071200c06001e50300085044948a01d13022010420110000c81e050503a034204c0c90080990f1111004e00c0780c001c801810043c03500708284000a03880c1e0090000358803444c0b1400c2880d0b10b8500c585070090814005010b000d1190700403400900c0240c0720350072507007480a49001c400586903115a02a20030b489180c00848003175040410103c1c809800100800a0794400c0d82110200d019681e03581e0044400c0717034407203602c0c000c840004101750f40c49440a582481010382c100d407811030014512108468450413070b20040d410201900002c2d640140051032440b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 25735680 1250 25734430 25734461
    0xa14010506060d0504060e070f0602010e06010803040605070302070b0f1317060406020901030902060d060f0f030c030303020706020f03130302010507030c08130c05100503090105010506070b0a0b0f0a030f0204 91
    0x2030a080d07000510328000c02c01401d00040e07462001a00f407007130a0f0810045607001c6005d803000e06d5100d0104900c42c19141c0640c01c0550b00384040c3c002d04c08400203000707049603040c002540c03e042c1401c80440d002e41c0204070130b90861044d802d011403160642401460b810710745c150340f1641d602400d600c01c00014510b520024040340000b1545030316039000300301503070300580c41388006039503519190050b0b000381410b500c00394100b4004210104010810b510000c2500c00e51011401042d507101e4001640780c211340001006a08030b01c80c10400203000fa0050210b15228100c09030402401b25011181a00115894a500e41c0e140c0d0702142490340a05c502508014546400c1c041103e060501500402000c2c00c00030094107804617000c14000c40d500000d014140003072018120103880c902c000c1c1a6002a02c10560355440d04000080d60b242080844040c145d00c021240020794640244400400011802c0d039002280c21031044100c2e139482c810034001d50b1054903204206041d50040c482152520305400c442e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 25736930 1250 25735680 25735691
    0x201060906061704151a04050604060b0a030f060e090307020901080118080c030c01020f1201050a060804060506190602070305060f040b04080c0f0607080603100c0e0f01140304050a1401 81
    0x75030140c651107403503490403000a55034445140c100d90b07030545c0410301c446081c80c040750b0507640003045c600e408205c501114140450340380c0394108030031120b0380e120707052161a0800207090030a0003600540d03a0030450b07a20001d40d266a40d18644ca00400440321840c0c642c1000480508610b0542d40082c090001000208035a130f00c3c0c80b40f00900b42090b0040500183c50101d40c00348412410003c0350400801c0c0f800039501d45081000c00080c5801a0a640c41c0742c1700900f0002c2610306051032417104486165880c40303c0b980722529000001c0c80098082600b1808491001c1980742d2086068002010f0650050610030300d1410301d282803003000381889031984e200005000c08034600502c40b54029402c0000d00c0d0380c41c0c0780d070030b00729281c0f140722000ca00540c021a0100a0615044500c1c140300740000d505598610740316201c0401158061030b00342000c80d99140602c3c499003022a00b0b16083c000604004d608440701003d02c45043d0003c4a04030360a40c00300e034500040101ca81320708046035100708000d201 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 25738180 1250 25736930 25736939
    0x203011d06010b090f1005090306181207020103091a010f080c030709022203080306010801050d02011d0307050405010905100605040f0b07060b090709061d09010b07020316060306060201060906 84
    0x201e40406100d100ca0041002c9100503031503840c1d0346200c58002000700240000032202902612a80003401c50368881d014150020f04a4603240c1e0301c00c408030403943c3c081d00d0104600000c095a039000850164105a0f403049200d0001d080002d0b170940b020428862600c196241205d4680300c0e92040d0045541d60708149114038841d00c000a1010585030680300140e2a00cbe8601d001071600e400480050003e0307072205000109110b6054025805000300381d840300d840740c0e00d4000307000c203040c0020703002400a0f40742d012804154922040c0c5040d40c02c0000c042d160200d50300c04c0098241c1d8804c0e00b20441c42070762801408000440362500c070000740b0a90a0031b5040a18020714a0302d148030f540b02e0540110000030344081080b850b64404e80e0f80610051001c1981e00700504002c0ca425018003402c070200740d002c0c002c0200009580840115180001d144d40c0190382000307041c84e00b83d041200200d07094810101c0c9426550b00700103064014201554000a03c2e40c580715000b030a440081c0d22158520340340c20030500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 25739430 1250 25738180 25738183
    0x610080a080f0307030b0306012c0712050403090b070602030604150506120a0603060c020d020607050301080a0807020d02030a0b0f10030b0601030c02100609020d0501050603070207030b100504180203011d 89
    0x1000042c41404050702c0381c1d00c1c4101503002d0506500310562501400001040b00b08081e101e4452410704840665000d98060801c6480c20b4010344000c408550211604010142d4507000554441d1007031418401590b605c0c0d80c6e07024660003000b02250426004000c01c9503504151040a81c00c00f002030481c8040c0e0324000204086201c0c0d050711541c104a503400041841483c2e4004000565200d40c1c1000103144115000303480b44160b400400c010b00440c404180c1e03d5101300c0549040c0c03494003015007088007160341ca8003025800460100c2c0c1191342240994090f80d41408015000b07801042c41c015580740100220002190050103451a541c5d000000d0012540b401c00843d070010080c2800038015104510581ca030040300620010b40d41d0405002180c42c82c010380240844900d0b440d403e2080da42ca8030100211030000301d4680c00140c3c0901402c001241507040c40030b41200342d600c1000a1980c90f03002040584200301810361800c0741e80da5149045090034070410744081f04481072505000040c1a455 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 25740680 1250 25739430 25739437
    0x606070b1305070510030618050411010e030a06050108030a08070c0f031b0f030207090e030415080c04080102040f17010b010e010e01110102030f0105030c010906020307031d0301020307020610080a08 87
    0x10701c0c04a030700c1c5103940e040190400c9881c0c050600140703407900d41051003500802401882c000d00d10303807210610051032200c0d5180505401907a0010401c805d0b61445001100c0072100014030562503c51008a8800700d02e0702d104080c040c0c0200c00c00b40d42e60350f400b00c80281c41e0950145c120030801106440c0e036000f080ea0040800c0041342d140c60b01b0a0307016102c40311181c0c0c880403510040d01c43c42080c0a00810590001420800c03603504090902401921024880c0c5074041c0c1c3c420102001c00303031790065040c20300ca4004964446c0361000103d0902e611540c0ca03500320b8000ba04141c1215110324001c0c8400c103810f503980285a62000c00074880c803511400020520800b100c9214103100803161101c14a0b0b01607200303404030030580790085440f40351136000c00c2e52600c0d082c45240d002c1e005070000c943c681c4d48034140c43c1c016211a60025454070401d0382e4111150440c00480c03504e07051000c0c1d404c410b86c0c0c0d001c2c002540100c40c198010103484c1408601c188140306550310500e010b0b88055a100d0001d0044400e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 25741930 1250 25740680 25740691
    0xb06030709031104020706050703060e01170a06020901031d0a020906220902010e1018080d1b08040b03010303030519021e0903030d0e0a050d0f0914040e010203010b09090606070b 78
    0x640d150a10143d0204000e0300030750708010b00c001d003480f080080080d8580d200500300e40c0035041c101283e07607a9100c4056003403070701c01a505840d00b08000100c04991280c0043c41c0050048c500050040d82c02c1c40d0420100081100d402d00541048a01c0d00c2580703014044190001001c0390910420840448a1610208588021000325844a00c0003040da130003a0400030100c00c005d01401e2520349080e200801104411000c020388c01c00d845004984d25400103003000301c0509544440c010f00841c1c8407030484029100d02c007103a600c9402c01c000700d1072140700000755000b03610a0b2000710340d508101c40245085c40c501a420040d0710f1050010410141d03c012521911842d03012606694446100100e0b0a501c81c9110700c201c06400c0046079840d0700740c00a03000f01c2090242c0140c40a070050b4410440e02c83c41450341c1d501c0051000c2d8400c1c41244004180c0b5440d4010050000a500c00803164080c2640c000741c0c460704800c80040398079100c5040030300d00c095103c2400c9446900c0c082d00c0c0c6e41d90b0076070060050403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 25743180 1250 25741930 25741943
    0x406120507020a081902010501150507030c1b030b070f02120d1104050d0c05030f0105010302011403070309050706080702070801140f0c0c010603060902011d0a0510050d150305010b0603070903 84
    0x480d107068002c0c4818103000d600458101d588004118020415108038044480150b20b440000123052410500c2161906500c0c0c1d0b40910b0f00d141ea0b1811908000b2103102912010b030644041c005d0042154200303402103101d40705409107840c04240281400d40f0248812040d504012001c05103081d014040703403841105040000340903d918003460380240625040290082e00404415040c0080949070004035403044040300c0000708009081800d80b8028072000b404140ca1030500018038038404051036100b4000d20300011101482c2e1103003032070000d041d030010010464900601c52115814009400070b07210340b1009000d50040d002d803210344800010284002e03403c1c5240400d6080340351400300e03203011445034001e00480b0303180e092000080522150803030224416400250b41440161448014154006c100c103881c0381c6028280040a60800c81446c2048010061168080940d2140d2003030742003842d404151036801c520b441821203044103d141c0c401c00381030041140b003030381c04450081640d51040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 25744430 1250 25743180 25743191
    0xf06010c0b013602040504150e0703050703180c030318030c051002030c0a0506010e06040509102a0806150405030d05090d0c0915050f0105070b040507030206030403081605040612 78
    0x301d0f41c107007a080442c5404034040820000c2001d80c154020304180e807000c42d402c1000a0001039013a030120301503c2804c001041c0c2400046a09001e9404540e22000c1c0703040200b00c00e010502c8102c9000507641d001c4460240b041e10a10a06501c082c013490b000d507400310284e04503800c2d603d6003200c42c000b91081e0791040080301c0716422400d20a1040c0d940c400742260480e0900072451500380d468200c00d0040000c0903150a000803200c0c40c141c02100e0103281100040c2201c2085140d00742c0141c1401c0f282d0002e182010714456411002450521800030401d0350381e82c0c0d0f40e040110400c01504000c6269448402c400d0105022941d8046913080c1030010a04105641e004040c002c165441002840604011640c01703002a400d00f4680020907042c1c00c070000580c2c003d440fa802c001c01c2d5614442d105000480610001c00085d50200c10b240c0c025004404545860365280d0018031641d004640440000f42c244041c4a0b046d0303644002d6203d004220f003041401c25003091401413030800c1c045205091f007034540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 25745680 1250 25744430 25744469
    0x91509030c0307060b180906150303040605090f040e1009050615090f04030915030b030d030c050a1206050a06020f0d0305040f02040903170a060f0b1c0509031603080f06010c0b01 78
    0x6c000c9200200310001502d21528010202c1502e4036400c40324814413400c0795800c9400c03868040111415286c003501d480781804010343c02d000419506911f4250483d40d540d104d010303a81c1041010f48420600004086034900300c1e4504a401c3c004003908140c8043c22181c08181540d9615600070b42c010382e800180100c40d0394504040712031075125882500450500d406181000c0c1d4103030000f86410700705038115070248805000490880e5020030704c010019405010701442c1c075200e130440221440d00e0110101d80551104000794496050354042c60169225075600040f1b0142402911003948a81c1810031032442c0a844e022141281c2075402440f03182e40e100c0ca0b108050149050044001600142e26001c1c5002c4040000804c4140280105005240b000080c40f841c010102c0700c1d1386560703100400801111080c41400703480d000d0211190342c0414800800d4085a10f111080654000d1351189007074108500346900c00381001c0d102c981001a14611b01c80840c441000d040d0440310095540152039880 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 25746930 1250 25745680 25745689
    0x3040501030c140a0207030b01050d110f0607051212011d010e06010c05060403080601140a020a0611090d06020d0b0f010f1101150303090e070804030c060506040207060203091509030c0307060b 84
    0xd5450700f00c4032030100e092460180e00040b541d080c0ca11410254100c0d0341c0321400c0284130a00514000c243c56040f0459044a003812488112041805448030341440e400e5a14981414180703601210384034004240001005c0340860b8a50040000b00d42101c1050a0f4148042101005014016a5400c2c601c08150164800d800712851190041c0a851881c2414130300180001000c3d101c0f2400518003110b42200b5000705812a48054180e03002801c00001c3c60383ca000103801400800b036031441040c0903245c4152100031140c50114880c0d00c0042c0e82c4c1100980da041100ca00c21115400b46045290f00b203a981d03005400e0b541d0301c0d0480d0030003030a00900303070b2a414094174041c1040f00d03298209000000800d900907442405440404400c51780380e0b0740c2e804089800714000c5401030001244e01e650003000c03d0696024503000880600f0140c81c00d03000762181e00503640240c841c0f04040e8000b4000c0d06103080d120303141d1900004c280d00a1840c01c5440101d5554034014854058001560323802d503d4110340e00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 25748180 1250 25746930 25746947
    0x3090201050a030b011209060c0201050903180d050102070b0f040c0e010501141b010608010b130507020a0201110f060c0a02012421020d0803010302010906050c1209040e0a05031305011103040501030c 87
    0x2c1031b150a0007036890601d42078015000d4007c0e0900035600b0800411030b4500c0200a5420100c94035115804030f110540c00c020000398405020790b41950b017008483c0100304484040e42c410700b070030a044d980901b424039015640f60140c2d4811849a40540c00500c9141c2e48000d40c0c03a01c15420081258491841c0180c0021f0703001c2078160010170358600300e000a0312601c190803a201402044800e00000d8031524508801e481084905800603004503100000643c0034041c1d2555882a42040b2140e01c0c8906005a14004041c0e40c50307008130310049002101650709000d99503101302600ca0342c8a07414a21884050400d08038010364080401d0b50050454610102081d0300341650001c040e0300b0074003100c0c108850994400c2c0820f9002905032400400c8540c0031b8000c48100c12a500020320078001541343c2c080058001580032a400b9032101c406a501030010407000c5031b40ca0141001d1070b0355900c59000401c001c1141d40c88541809511502144040408419201111000e00380802c03003030041c0f00308481034007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 25749430 1250 25748180 25748207
    0x3030c01050a0b040b0d0206030402040903020313320f150909040c0807060206010b12040f0803091005010906050102030409050705041d06090c0702030604030c0203070504020f1903090201050a030b01 87
    0x1840e0104000c1821000d800c980f803140c0003a6010001d07505100184410504141d10103500090200086001400c1c958400082940a4819071382088038200c410740c1403031681e038044038016203a4900140e403805420500a00520b4101040000b034800e4000704d105006114076151107100401e91100c0c024a21508403005080700402c1c0400510b000d1130310051905150055024031303c240040800e843d03000050850595252905d018107022418110590f01c0c0703c02802280c4180301251f8540028401c2d038007542c0641c61600c06000712500360000d0b2002c845050348070302201c5007444d004020698000c000c0350305030303420300754045800d82e1440340036036441c80360380c3c4109001207d046c61030b40c074001100001409580c04543c50a43e540781c18642d0281c0c0e0256050103907054001402080001e4095a51440c100348083c059420480d900c0c400a4105d800c06030f100500950002010016501e00d918141c0021500b814100000030081d00001c0481c0100300301e442c00d040d901c1b00c00190b0340c1e016040303602008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 25750680 1250 25749430 25749433
    0x20906060417070f0608011802090a0b03010603020711040b0a03060509031306050a02010e0c01140a0e100507030905030303130816080a0e03010f050609070c080f0414031006061d03030c 81
    0x5454842166994008078815601204c2620b440464800c0c0305020550407580800b401c009907145001c10314000750700c80c10015a008031032010000e2f0700010030005e18024551a100140caa13101410a41c1501d03000084c110711551801d150b040f442d65420f82c582042d690002c0c8001180d0340c8031500c17980b942c070400b071003517812010141c0300186c0254400e000f40381000469009021880d9800c2010340d031110809450340c0800d08042440c010b0320151400340c2103c00c40b0381b61a2010300111000320311103c1d405440c04000132400580345003450f070001c86540c0106405d800030351642c5010541c407a4141136034003004100a60004d02c0700040e4000d4030031142950b80022170283d942e000e8400183c0f80b40700d0b006800d8029420089450144040c0d8499148504406020319845980d80003040381d1200b11204104c80e00b2605120700c105610f0000003403c060602c0d9071100c20004000820580360404a600744003a01e42000021b04c5503641c04001481203406045000049151a2000034210b0203034807600200e9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 25751930 1250 25750680 25750709
    0x20c040501120c08030903030a030c02031908060f03061302040e0a1505010906080a020a0603020a0216030501090317070c02010c0f1a0f060109030c03110d0c03110405130308040209060604 82
    0x94039246036503810707248102010b43d245681c0b808501d80b04d000e0340003801d5058109020409000c0d01030f401000403e071061050780d10f4100e044400301c024015401080000510690400080b070408070325618414008a008110501e002801030800659412000b80070b6030300c2e9030216414401c104034481000b030344100c000b5000f2a0100301c59008103000d11810003d2820800005a00310b0041940707034010350080c007000452418808207030040d500207044c80045101c1d01040c40b14960b00110280301941c420400850041e046c0c0c20010588441c4213401b402001660f02844103158210100103011542070030032008052031804c01d4007078420f800f10003030140d456a88200c0106684030041da440340101240c0c0c4030039511341600459481d080d41c04010301210751450240b01184140104c16071859004014008039482503075018241401a801103174803850072040e108451901c0d00900b0b50210580c088000202015240149080b40113440070b405105400c01080b0344e0307104c0b002201c010b0301500c55035a85 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 25753180 1250 25751930 25751939
    0x3060b0d0e0f1509060106110d080c090d0c05040606030506010503010314030702060a080a060e0108100e01090f0c1802071205030a15080a15060b030c0d0b1905040b10020d050901020c040501 83
    0x11940d904403130100403401380e440045101317801140d130f441c030a15054000707100644060740d043d181c0000242c40b5090304c1800b031040900c076a5071175040c001014490800b81050b42d285c03c0500c000d541958200d002494104000c01a5a0340d100007a2411250080801c000f040e0400c910716007036124005010350441c07000508148490780041440d40500011a010820bc650700c0780e815120391020b00618645030010088e51005403803540100e01c10007500c00001074008181c0c0d90340b42c42440d41c118200c1e500040c0350800c01004010421111621040590540c0b0b88003840d604c420314104e8000b4408107000c40032001c10781208650f0321001c00c10f01420b01c0503554036140d500c4030f903886d120704404031a2501140310f101d1040d42c20f40070301c00490700380b101043c0c00d607101c81e0124076140d040341c1200101c499a07051862220390703619041c8103c802a0110225550341090103200581c0e940d41e07125070003045400c960055130b680c00910000421090f03d4820388880b141c030300403030a0030703400b45296074820b050000101c2e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 25754430 1250 25753180 25753213
    0x703030506030c010908031801090806042405090304120501020d0e061b09030c0904020d0507030305030609090a020a03110d020303031e06010c170304022205150103060b0d0e0f 77
    0x240580c00480071a81c4010403140115030645c890b00801146410034440d00255404000c0003458154050502603042c917101c078641031030094100c5003955038050710120948245010806000342c4084001e05005900e8a04641952031249204000701a080081c3c004240442907050311095070040300b05200703091460407003030355034202900c0d0801c400d4010b0080355103103001c8000712051548090090071010712038000704245810010000c2c2d80107036501c40000c0014000b40a1103001c0c51294031001e84a0810000780031920074000d210441691010340281c01680e41c54014904582d88950100b4000c4140f4001c1490207012340c0b40207400d8030000c0107000030201500440c081c00300134808004403550f00c100045900000c003040c09020b44124928152441d101a4000e5500c28005054408a10a9142e081c6101200f25070141100380d0b0301c0c0306000300003400c0b8480040c0c2000900e02400420708100580300b91381b0845014400c226603401544110310814019060740160100580d0500e0f0f02540024 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 25755680 1250 25754430 25754441
    0x7110a11030615180403020a02030d030204090b0d030c1203020c01021c0b01090509040f030201090b040308040506100b04060305042306070806060307091203020a02040c11100209030c15070602070303 87
    0x11032282c0100c20000e0103804040d4011111808001c1002c0c804c040c8409860042d0a00680160110301400c90780001503101003081c80303c81101d03664016070700c034900148141207940350b0210303074400c40880040354086944400303103880c0143c20103012a80d02100340001d500078031a0104d064119400499078000c2d05060403040742c81100806024071002104500449850685000300d5902c45010008280464400d05c0a1441c0901c240000641c3d0f15040c2c541b204c00c008220b8040700059401410401000b409025040c0c005c500e041041040a042c005605e005000f113015400806981c3c0700040d040c0b0148400c0c40c4d0516004039081e46014420085141c1c0f90340301158aa800b003006a00490103904090003100e206102c3c59a4116101d400d106100d40d0310b600459094045104d80155000560388601c00c041e541c1480340c41c3c60b40b01110200301242084800c24107003401d144140301641143c3c40c08500340c02801030440741820b03240d0340000d100c20307540a21140986039500c0800d900c020150558403a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 25756930 1250 25755680 25755713
    0x6040506041b120b09010503071802070807080405040c020604030e0111030714070e15060403080901110105070f030f060302090402010c02010507060c020106051503100b1804051306060e13030807110a 87
    0x188101413444050201da20001c0c800c1d5509580701a20400107484000c4016040c840791100c094035100194442d45100d400890003940d0402001508001a24080c030403071001c44000e001130205840c190310302800341c0e062541c21300d06111101205c1c4d0300b844d030248200c5c3c042075442040c0d01a00031000d01c6040e03551030345005904001c194103020035000500022981408c607002010700c3c0c506425075440a0444d0440c0c0b1195040c00700d40011504401c400780611441104940d6440c145074119110060558616400d10107280707141803018000741c1c4556006503403160702030a040c2c1080d11280700494003440307085805440c50b450b203e40ca40100d9410b4202e40104e40040301c070b0150342014846480310620056030709241a078014801000641208005807000600102d81c90035100401408502568001c50706004200541400701041100303520070340020302180d40e04d588452401c009511408034041401034207000101c03002541991180500c43c590b401c0400035140c8801d401d1a0400d150048a400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 25758180 1250 25756930 25756967
    0xf0204050603060f0c0f0906120901180c2108030901050702060a11031302010201110d0b040f02090306010b030604020d0e0303090601060311070807060908270301090b06040506041b 79
    0x841e100c2d24000420f076001e038200726030342c00e141c0c1c88a0b02e41d031419510011083c46518014001c1d1003550340c40300003811920348540480320340c07460880001801c551040c100440e01000c603400c0d500200d500d480d910002d69044e085a030851800c1d00068004882c1c0c001801003442100004000410b5010740026010340c0154007100d1554035036501d00e1090312184030700398001e00018000501501d8031009080013550041c000006c402c410216110450761213201c3c0d02402541b26a01a1203a081c40d00c03840e981032074902c80c2142080506070000380c881206105081e00000040013242690744c50394100c414001c10040100704030740c07a0303100c0d0f2074503a001102c0701016405550000642d0f503010b40280414460f48140052409119a592011b00c3c0c02215040d604503503030308007890016800500605440c600304005c1c0420110000040d1024042101018000d904144030600054403222206030010400c9230b0101d040e645a00105004001220700301000d110062040004550000d03141c0303814000514 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 25759430 1250 25758180 25758191
    0x80601080705030a05151002010c110c010504051e03060f0103021e030c060a03020c010c0806030f030405010e0904020d0606150905090402090402010503070207090204030317010510120203060303160f0204 89
    0x40040d22020811210503000c5202000001c000006a0380455804103500d00060000c014100c080b58103c034800a1500140c2e54424040000341e8000c4403039415200ba5a005104030802500001e000b4012403082030b01500740c5408081e07100e152050241100040a8102d5070140f0f0f003a2a0340034200000c0c8400d0303005400d06110b0f035004c00d118001e03400850710040d0040c00741c404668103000c2d2561140301080c04159092000003110070080c0290840010903a58900140c1482c1040505204110038803801d240d00401003000140d8118a540948100403034000c207031943d460001c01c03190b15400c0002007600c4d1030800301041380c524044070f068582066943e041011529041030190200c807c0d90042d5000000400140044d03204000541e8080d44900c165001255560b038080e099800c1608210089582c40d402669554440707003016006000440e061307400000305000241861510560714400550000000790140c1c80801c00c6070780241955014800042da075041001c000f0a80002c01c80c030503030400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 25760680 1250 25759430 25759441
    0x4061409030d200307200130150f080c120601050105030c0403021c0b0901090b060405060d0b04080a0f080c0304031d0a0e01031b031a250c060b010206100905040606050a0b070308 78
    0xd1031885445009444074408001841002e041100642914001503275120000c03610282d0360705003004014003a500d1f180060b5030401400c03034104612800c0340c60041d003a00d401f4007141c174400542c03d81126406c0c203025a1343d44030500781c65603520464201a400050b05001481c405ca4048172303403807002e402007030440c040e500d402200c00c2c01ea03a190b101c0035104000d62004280145459440150000002040401c200010b5a22003120b840100c505031400741010801c5480c1d02d40064420015115070701d0007076003510b42482c5403000d50102500c0982001034045207844064000c54842ca04d4100003000208610343e41c03c0c01c21802e54090004550303014000078050151816521308000396a03201241c88030340c801c3c03044240c0c4803030360080c00320541e50500c3e130207071164545401000820a4041ea1101030054680c10a08241d03804007041c2411503014404104494845d1050384003074820159002c0b6560b1107506116000e0211a002603901582c0c503039000400003007c80003001083d1083c1c580c840720741e0381d6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 25761930 1250 25760680 25760687
    0xf030f0e03070b100509040302100507020606010906050c10021801090b0a05121e040f0209090a020906060d0605090c0c0d050403080f070501020c010c020304061409030d2003072001 79
    0x60302400029603100384000400a40070b510421303031214481c41d11065096070361001403071808040d40c083c1c001d40c111580304c8600c90880c2c003d0690000c090b0006020600b0142e00080011030345100b034000304140820341a44612040c0310046549103904001e54032402c660301075414131040700c0c611602050703000c800002c80e90303150015501d2940c1541c07030301d038201262112041d0000c41c00401c480b0300c0361001d003050603500d49800d07040c5002e0f5015101c03965074445a4414800403401c00f811150140e0703c8440d0030700051362908111036100009869031929419a01080c2c0050441a00615808188801088144019100a0700002c1400b07400c076032080c506140140c1d07103840307240006420304004104201000a0120003408024800c44c0010710303001c0040010750031189691424030050f04001400c10800398052485e60110100310303284d42c917080c00200000c1d9500c020f2554135040c07001015a61012000004101804400d0039094030307a50242403921030701c0d03d400b40101d204105292000a00c40c0e510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 25763180 1250 25761930 25761941
    0x5010f02070e151807090e18100e0f0717010617031603050c030d0506030c03010e0a06090302010b0904030c050706080103031211160f0203010e0c010f27060f030f 71
    0xa1490100d0040d85540002c03a09490007036040540000c8900c04102d0b00b08138507013800e48900701d5990f428028a0a00c051040409409000042449010000c460701c10034082041e03250f00791400300002d4050380d2090b055080440c0c40d0f500e00d803180124a4002100c0c507031860010b4140e20048004c20031191250301c81100e02600d2881404154030a0001c1400721404000329070459000e03042943c1000468031906103075034052000c103441c80d5265010b020540c1400c000d0b038603520104800074401060301044883d9a07004100c40505810340340c8075140c0605000b0f500840d2454401341c0901c00350b1030982400b81061640c4c41040390203114004000580030303c12020107051f240d141c3d03220609500c0b11040703507010b03150003111030411034410000302180040010014030503034841c50840d44400f02e18010182113845000041c80c20350451000303038500340c0c1d026081006030031007820700840d5801100b00c0d400c024410082c2c580d0524000f2003010401d5500800440541c4103d50340c140b00d0450440c2001c82a2003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 25764430 1250 25763180 25763189
    0x1203040506010e0702120408010903030c0912020f04020906030106050a09050a0f170c0402030106020a0506060303071113020909040606030605100303050d1e02040b030f011d010303080601020a02100905010f0207 92
    0x700110014408070304160303c1d0720340002c1075104698100c00c00c10b041800c140e21660181030260346d1180408101a05405114208251806e00c0949546002202c01d0b9440c50800000d128040c0710408140070342d541d80c1550000c140c081d214a03182d42c0c442d00098070991084661401059035050005003510349800d0315030a071007080c850895850300c0c1800c407024150b807001a6080718024080c2d202940c4e291032001e0b5008040e507a00030020f00c0b10906045040010140481c0d0084d0002c01082000c02c1c0b1040821410020559848400410003050800240255070485a200c8404000e000070300c0000d42112056078007a14040045490b2968091490012844002c020410a10000d05e00d40384540c05400440280c18040610b100d003860f0100881e4040c1d00308002e0300c0404800d11400070b54504074036004d00b010b0300c0c01e550b05401c0c02d19844d110001c14400241002410400248140d00c280980e20071554090142c10034207600000141c80d14095004081c0000c1510a040180c40d2000603050102d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 25765680 1250 25764430 25764433
    0x604020a0302090601030b1806010f0306080c2101050f0a0f051e060d020d05030711060703140d090605151314040605040f050312011404020703021f0b0a061112030405 73
    0x12850340e8203000345810004c1c00035051542d81c4401d403241d0b8079a80c40602c8091880400004c0f1031508800150241442500480416141c0481031102e0000041c107055032000460701c40785908400c0c00c07003119a502194604c0e40c99400c02043c070044114003010980603a414620902841000191510032108201da40b0340024036402d600d544992040142c480d000800501144050400354001c44c43c400c006042c2242c2540c000903411061113003400d00c1d521841c0084406a242c40403d4030010103007654513440700740020000426016054103540004046079001c0b0b014000d40c0344c0030002500100700c0a009500034005e11512094003e131500c10071055071072031030000302540c079661100070084c0b40050040301c0203001d6030719450200d50108050440021790302e07440b200c01d6041c8240c080780b400c90800030f91b0140380140328940009402007190181101501040d00c00c1940b40045040509200c040301d90b003000183e40c0c00714001d50311001c402c402c85810b07001c89001800c50054087c2e503103c1190040c080b03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 25766930 1250 25765680 25765699
    0x10e030303061302042102040b0a08060408030c0d09030201140127090c0302092706040206040b090a0306060906050312040f030f06020f120106020607020a030e0409080d06030302010207030908060402 87
    0x114580403202a00d0841440001070505869462440710a03d68501664482c01111b14601c114a464015001c00a405a0301c0e040c1492400749500d51325480a03000030003442000c00044c0107400c1100503a170507020755100600600800c0c0c20003030b00800110760200f11250110001240c19199506948614403214130800c21345801d85aa1000030200140111101e1001100c00001340c1d8854031b2090103001c1e411180c070315480c4601e0284400d505e03801c840011a410100c104070150769207400766000c139a00040c3c1941d65240000c0040c4400c0001d8000400603403810402040c045442d81c071038001d0b600b065045850384500542d0b809901e0103035102da21132100c00ca81044c00016101c40c0d9001740684103810250401c6c42c113004a1080741c012114462044001d600104a0a0760400280307402082e2070001c1c1c522001613840013000181c10795440c1b4021506c0b0075642040000c581c1c1100c184d52041c480401c85e10ba200c2c60001e000c2e60060609400040002c40f01084403900800d030035000d04e031b004040554 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 25768180 1250 25766930 25766941
    0xc0f081302010e0402040306020c2103150d0b0103030201020309070801050c07020427060903030c030b03100c172e080606090402011704060606200a080c120a05070c05010e030303 78
    0x40d010240c100890400c8180100c0021035220350010380050b512800c0d0160325a40c03003124161521056030300c4441c506081c5004205204400000c40e90070080d108664024030140c40080382d041c02d140f190081c4040800d0b0b000009140d0f044d8040d60107007811400303440150342d071a000c3c0b40c01d89101303841030b214400c01000b5150040c174041d40000270918200d001030080074448250a40301c028107407003d841803030f104c402c2d000c10541e15100704103400c0d0007400c1c104549040c840c007003030340d6521003400d40d5181c03542c07640d0408026020f0300000c5071200c54010000c1c558507107951b5030b0a40c0323118511514048c4010550746c2d244440b0310f8140c00d05507a1000018001540d8050412101c5580644140e041c0104200c10842c41e003010742205100324006d01000c01e01034a8001c00800f008045490410540a10120381881c402c0200d0741b041001e07000302e50642c5410745004d295040c00d175401f9060642260000707a420f446a04400a010f0790350003007032402d1186a486e80191050343c0f252404550540003040000d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 25769430 1250 25768180 25768201
    0x20a02010e060c010e100b030c0618040504050c0312070c06090803030a050606090a03141015050909100e0d0906090605030601050c011103010801060f080106080307080703050903010c0504030203010c0f08 89
    0x102d0b54060f4000401c043c6035048440d402c2403c0522040ea0842c0c840d15146298202044144030100301600c00f80d00d05991601000102c20030712901610554650b4086824008108204014150010b065540c01d118030013032201e445d8081d050807944a848014000380050040d1020030444a014000c1c500c1d40e43c0e01d0300408000e00c0014a40307580400103204840c4591076030f0000c0000f55214181e0190005040b01d561860b0001c001805e034059420020001100243d4412803800c50f003040d10f80340036580b0b44030708250401440e80e4001c007a103407510040000500c400502c6a504401e170303460380e024440c4c40c0d03481224094842d00500300407131000c00200300780d944030390018580700400e00b0001401c00240200100ca503070007a4800a950381d103c3c1403d00c04184100b000300010041200200201440e01455580340d010f541c40107800c4034008200030b410301d8066811240d14200003002005010315a41c0c014107540c02a02040e8065071070518024070a601030803800c11000c03881d071601032003540c4666078403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 25770680 1250 25769430 25769437
    0x3020606061b031b0f06010501120c050702040f02030601090602010902031b010507060f060503070503030910031d030d0507080c090d020f0d0b0f0105011704030e0f04020c06040b0402030706020a02010e06 89
    0x41c1c41080b81c5807003489810100344094141060700940c0b20700f41ea440864a103240c00034507582120190080001003015a0300150321031009581590b0100b140b81c00050305880c14012401c1c0690480e0501c109a10000660b900542c0b04c0d031000d0b2504003030b160300c0e030340c0032803c03035581460003501a4003184084081c5221102002241d0a05142591030604190740300800d4504c90150005000c1d1144014082e40c0f6051155170003400c0254000c500340403140300000d01c07000031000c0300c50038075079104400e81700b81c403807402d400c407480c2144411255214241500e41000340011030b907040001d0000c0020a488169840840d170801000500301c10740d184054003000303a01d004030491607030f000d04815020b500258401c00000c0c41904000761f40daa05614280c0003404441c1d05c24030f20315240510108020000350888450301c010764082c1e821035281c16068010500921621888000c42d1007410308010070044592501440f4920070382c1604c0740e45554000607031341d420380280005d0200348001041c080c14103010303029 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 25771930 1250 25770680 25770697
    0x1612080d0605040c020f2107080309070807030c09110301050603060f0f0a061e08010305030d020703090b0c0105041403030601020d0309050a02101106010f0e160210061d0606070302060606 82
    0x1801c15038440000301281c03c0e4034880e40141e0001d004030900c1760028402c12515074045041c1c2c1c245030180c40b10540b8540300c0c0034001801410048003244140034100030440251010200703c44055071242441840d111b02e920485000504003041d445002c904401034034104e46000d0310240c150303142da10401c5450300ba16107149402c804000140c4000d6682e83c2202ca000b04a03646408020001d21080103822041c042034030002c7c096018010400107000004031540d440e00324400580740ca60a14080f14044029805281000000720795035815110641c4081d018134815607040c000c40ca1600291501c90000701c03404c901503004190040c05960103604401c2c843c1d8411030035900e81c094203900040511041039010b40010305003a10043c8456820401036001d040500c0c000001946010b01c2800038000091004644210501c1d25060050080182410740409140280189911a0181209094100e42903a10340d044100401e419003005400c17504203e1301503010745017690340e40062020030341c8030140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 25773180 1250 25771930 25771957
    0xc0a0302040e0c06030a06030c080312040b041509060f0e0705010504060309031101020d1b050403050d050a0c05370f02270f0402011e1205070201020d0513020102161208 74
    0xf5440d860365103080082d0301c2900301e542c00003a002c2c11360800380d030300420315000500c0d01e034010408194000d940c54078981d03102d03500c40c0d2200e040d03a450703141c02800001c00035400100c10b030501c00070320b040002c00d4100708000d00c075211080003240c1c00350400b0364ae20046032180b1400700c1d41c1008144101e6119800134100c40f4020300301503003441e903654285800c81e40400307602468580d454000d04807995800c01e001e000c0c4180351a1a908060440e1256070700c621b81c044070481030100001e410145103015940250300150010140c0744a0305007003003600c1c842c40000750303d4035141c549490301000000d094001500c07040d800c8007000a030400b484d400d0003000480d80c800800c00480714071185810162002d0b0080c0702d00e02d07080c042d0a8a0070148009050300481d9000e4800c0313041c504403050350155010f221070180031079002d000724058944030000d07802840340c8c042411486050101700020190f60100b001c901c14400e0b0308031121111806c01c0300300805a1401070310100301165480c00042003420001d090500c0e403c0b00d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 25774430 1250 25773180 25773193
    0x11010207020a030c0e061926060a14100b03011a0903060a06050f040908070204090804090c050405030f0106060807111f050f010510050f0c15190b01020c0a0302040e 72
    0x1000102c611a859208803040c02d0b0621082c4942c0c1500544150030000642c2d48100303080d8841b9165115079120f0103500d000310388254200020703c84003850300b0000003403002170350320714241040c480f00a01600c02d58200101d0118003c0341c4071180c0c00c41002c0031903c01d030020b281140d003803107062100800c01c8a89a08441c4040c00b401506030340c14800c06001e051001c40000b6010714000c00e12003281800f0003030fa4031075450442038201140c0360408644c0565030444000680540c3c03464000c150380255040400b1152030105102641d6400200a10a03107000320200c0c1c3e6000744038a5614242d41e218007a1748001020702000c1100d00b4056030048190b45215015194043c4400070b684a2050f2820501a181ca8888045c040b20990705000140074203421744102d9210504003001070078074418004001a142c2000480044404050140b504640e8450041101505107008610010548184101462450403500b62030641c000a091301160101510203c0000d02d035808010041c610107204984074007808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 25775680 1250 25774430 25774433
    0x2010810080601061e09031707060905010612170702100c0302100f060501110c01020d0509030f030706050915010810050a020d0c050c0114010506030c0c031b030a1106070f11010207 79
    0x18070007a4040c16090b03483c0c5010542e100140402617001200d41310170700408030f00a001103114a05031410103207040144a65451706481e20000034558000080e1003546040340c007003588104c5405d80302541d03000f0300007401e8410405a000280344600c4038000e5106210708240070905004030a000701c441e000f0f0054610507003100f00c0d800f003640c054403c60076000369640414001e56070040c000c0c0f0018080d02c00202031101c0c068002070740e1144c1072560002802000704164007560340c10003600d071149401c40140c0c2d4403111340c1d01d02040540025541c07000e9500407050f5810700c0c4a250606241201d007002e00600b85958058504401844047c5c10070380c82c40d80030885107131640800d0040b400159010380d18240e45000301600303a42118200031466070126000b0004002544d24281600c1e04091101401651044140f020034134600c148694000e020641c45161820f0f0309000c8050030715200d06440e07203841d15051200c425111081243ca110200d803441c6c0c4c1201c1c0c0d540c414407542c00c004656500062910085 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 25776930 1250 25775680 25775683
    0x80c0d061409071d090a0e0f0102030109050906040b0604050c090d050a03020f010614040b0d02030d05070203010501050d0305030f04031b0803090d0906090b0f07080f070c06050c07030201081008 85
    0x200e07044028412407044599150742442c1c03030002c1c0d00a407a454200820050285081110300302c60454078803070b00031880840c55040b0b4035800070140349200011259107100c0ca80100c5d010350024401c03103410700c3c60240010005200424044d20465200e0350845040c1c2c1c0d000100030040001612400b100e02e402d00c100d11050315404400000940140000c00401c0079624000b031800310607881414441e4109542040082004140d100424008580103c1e01c082c1c80d40104844081803403001c0d5052049002d1070a1540c0c1000090201d68001c0d0f00903c0b55a0b269070034003000c1c40300186e004001840400c0058101a480c20711190098803d10703103502d50f003050b0f030741041c1c2d012840c4c0d0302503034246030000603c0a20001000b40410100b51070400c681c1c1e0754a0f100000d085c0301824414107502c2d41c2c000402c0607480c5c40c94411110780580c421400b41e2250707800700600b506c0ea08080c8045174580c1c480c0001141050080d0b00b0707180c003121000008e08170709081d540111070b11240a0100d002e05a040f520129840340c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 25778180 1250 25776930 25776941
    0x5060301060503041716020609040e19060c02010b0904021c1401020d050f0f06010c1e08191d060f09030f030703090b0a0909021605070f050102070e0603060106080c0d 73
    0x41a0b0740e0710344074282400c04041c0e030710407401314010245080007110000c01c400e50b641c11100d80c045460917214402d450101c0e001d41500781403580c403070040301002d62681481e004508009030042c50100511202d03428164202ca40485690398400080d000240041c030b4280e4440314014455401403296644c4c1e42e40e00750701c100000354941c115940100355005031114520403541e104013140c001c1d842e182401e800da181d501d2005042d46040000303400c1e4001c140061603a6440c048044001c00489025050a02e0711454000e83e071000e0804a102400d65541440f1b0039905240791070884100100001d00c80401c4000e5011083d00f0b042d0b2081445140e01a6900303008207800ca248103805180e868110f4030700202031282c19007008804520901140402e20791000c024000e94440755401a59481144440104036140c400010300714843c0440109220300c07042050703070494400307800f2100c00544680c519040440100c800e150558440001000310364403c030600d41d0069079025405160114021804c07080c0ea4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 25779430 1250 25778180 25778189
    0x1207020d0e18010b25030801050a0603051501260c0d050105010c080307200d0908010e0106140904030c1514010b0a080f06120304030309080f01060806010b1305060301 73
    0x20442603a86615640241410140c220129401d4540000c1031520721080c5006006403103038000003158002c4005200700140d01d800e51000d6960610a00925008000c4d003000d014150141221920021302d82d802400b44d58015105c440d41804039000c0040110354000302c401020b00c0d6442d20540402e00c0480000c1c04a00030714040000a80c0c1d60000d00c140750a0b00d8040c0d00c29810022800da80101103503800041e2500684513140000440c2c0704828881c4c541070341008846881c1c011400b0340403441c1e4206a02a0481c2c03842c400a01205501d00c18050880e0340b03d1184078403030151102451342500d415001c4582c003a200741000d54560f2020780f10b4120341e04c2c003c840d0000b0655540d101040c004e01805000d8014007451001e5443c054140100034a10320340030b418200f5024650001c00d0041d52034a0400510040304070459031500d40d40d0038000e1000340301e41720307016050203004920701c150b01c41800303520299510750005104903468a1115000740c0d10080c914692030015002c04205a074070480118000c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 25780680 1250 25779430 25779433
    0x41b060c060b010503090a081318020a0905090115050d11040612060e0712050a110c03090103060b0a080c030a0204030f060203090d0903050c01200a03110d1106010e0c120702 76
    0x110401e00e000001c0700c01503140c85051001c103104000075000300003698903039280c0c0070110a49030190010704c00d18441071904803254400e10351030a00d030142c00682c0a004888140e95480441582e5241800341d4030f50280a442003c0e005081440c85071809400244880c0301e500d6800104814070b8001a00543c00c950002d07000a00c981424616080c428040e0802600356400020000d0030814009044611400310808116449400041d0200b00aa010a4468001c1908940e4800000311655129400120b0b00b0b070101c0e180c0500404c0d204500401d8842ca0316007611600c0b03858550036000800740c0c00003042081c8494007080044001401e00741c4600d4194490240580c49040c00d020780740c184056810715000300100780f00c04201045002131107880816083c2441140802407220654000922180b50070a84c8604441c200405a0052540380034944d4075080d00c01c03a03280050308640c01c1251801d942d000b03074406c0006100c0c0c00c24481410742c205006124044c54202080303c40801d1000490320000035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 25781930 1250 25780680 25780697
    0xa120503090a0e0c0405010c11040c0503090d0e030a080304020d080d0207140109030e01030b240a0806060a050403030f110d09050307120b0a0203040204090803010f03030e0108010509040b041b06 85
    0x1c2c140924a180640100a40c4040c58a0402490f003582e010700d00c91241080b500c4000d001c2401119040c0d4240c2440c060824014139001c0d681c043c005900a46030b1500a100c3d03c03210b600140d218410b43c20110400038040d010417541d03074844055680014005a84c09001050b01c64001400175004009842c0440030150300c45500d404c0c000022960707001c1103941d6034105848100003e50080c003c81d120302e001d0800164941c0490046032545e0400140b59880034030010350441c0ba00404c1c03015007608016640d59142980d038040600a07540221810b01001c10b03003d001c2800001d010704629031001282e0710740109403025080c3c074149042c00742e05502c000309018100c20f01c00c41c1800d0140101074100b0110020703020010313030344d00d44400c0c01c010804141640d010012a046548903000303502090b8011704182d480356100d80c4c100c14041c000b8801100030a08681c0c02050382d50003600c1141c1200c4006201e00c00302ea4072078a030b1500c0b030000280200c40f02002a00c000b4401e0310503c071080054000d0740d650850 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 25783180 1250 25781930 25781947
    0x601060809011508060a15050d08070c05010e0d080c120f07050d02060106020a08030a02090411030a0506010801120809040b04050114030f030f04060f02070e0a051504060f0b07020a120503 82
    0x210741e9192201401c464003460140131030500000e4094000c8409440003071203031300c07401c10030030b9070320140d041213900800002480781400403280107442c034240500e14050650b65204015508100400c0706590048009070404000c80d8404003d0403480d0750b440e00740c404201040508103982d03800340e2000e45c0a40d40100e0751005101003000680301e210103500040810754100400030750345910440c40103115050000024422a1403901500d000107000380c0144148000182c084403260001c0360300000c201e1134000000c4040d072150f030005041302c20a000320310200100703442d420800d0b03002c00c81d45034100d0748a00c80440b0985031032241d24003c00c8108520101c47c0c20035000c25003408543c2c2d030706012a42c0244164000301c40080700700c9003150028181030321442504482170b802d01055034000401c0c001c4c100b00304100404039410091003064000c2d034030755280c0320f04d01c02c0104440407030180d51440007490a0500c4036080c034070003c0030f03664002002818000c0d590800300c15541142a0102d5140d040840c0074032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 25784430 1250 25783180 25783183
    0x703020a05030301180b010806060d09030c140109031211090609030c090109050a0b010810060c050f0703050313120f030e040209090405070302010305090a12051605010c020105070f05070822080601060809 89
    0x201d14403400d1074555843c1c10044001002805031404c0001cbd02555001c5600805008080d480e4031603a115841060080c501030119008290b078600c00d802195079140c0760764081b1542c0c4203c40301c91a01d10401814600c40000307101140d0080d01ca85501032060070030040d0650341c0c03c61960300034117818002252031b1401910b9102540c0a040d00203041c0b0101c0350034040c100c070200e580ca03000d80d125032078140f483e0350f12410800d103040d006c425016036038003030b03118084140301c0040028445e28a68003a03101c90300341d561003c40034000c802d02018000032540a000c10000e44100402c00481b40014805420190301d8800161740b4041501e08071103640c0075000800455806002d0389500c411a0406403065542c2526062106a405822442000380c0090842a030380f000a10301d543e900e40000080150a07621500031b8008d0005070b03554000f04d02c0c0303602400c0780b591190b401c43e41000e80c0300001600304111046a2110010840640c2c24011100c01c40481c4480b4100711940c020200703039480c0b00d8241400200c26 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 25785680 1250 25784430 25784441
    0x917160b040b0306090601090e0f0604060f030209070807110d1d09010302060a0c050114010e0f0108030f09040b03010b031212011e170c10090303080c031b0703020a0503030118 77
    0x1809200c105000c10001c1020050030b0700d81c801d10545000b285942d8600040fa503000241d0030002c240c00c00e035014021910f8898103014411001601e0810005494854141d10300f03a17544002548041d02c0c00014841300c2c0b0840e5076503000005428034a56101c00c25401600f4405103c1216002424041440c0300e030100408200780000b07802d0b200c1203815411500480d00324403803e0700410900c1051000101080f200f540501030000c22803091410550b1910030f10780445030180e4855052951107030000c02c1c000004021261841d020f9400c00389040f03014414031000d40588400a541956605c1402c04141c03818403c0c42c50005c00c0c209070703550300e01600c541c1407003d0b0810f801002011114a50400200b441d4078051000d442103d122840c5152180d810280f4080040c40d140c0d0b08900503507100200c140d0006803201c10740c1c2c442e8645030301b0350391180f4001040b80012611340a408180c075210035079404941000f0144a0701070310598070600903e849403499907200ba4000e5205c100001e00c0001c6000a61244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 25786930 1250 25785680 25785689
    0x20d02060c070305070f050316080406020105060103050702060a090213060305010606020712050c0f12070f080c09060a06080601020709020a050405040f050402030a02040f020913020d0c020d080103030807091716 92
    0x1001c1c10024143c400410034001c2c814020228100750819600303001042095800301403c60040c0e00c090300c590318005106401510a8401541c01c15003c62100d6000f130007030502c82c28081d8001c0c09103995a41d0010040c000c400c8050381c102004000800c5501d001c1e0090b80302030360103140080307285403400900a01d0500340354003240da11a0442c44100c0002d602003001c04003080c1c111401d140051054000503c1c1c00840c030382402180c402c07141c00052100d41c906120003101c160b0400e4560303602d10038040c42007800d011110158000310380748040c480d00c0e01920344180c014030184116800c090711014284100d13440f0000c0c03103000c40e40100e010003052816018001c0d0483c50030900344080d04295010a540d41d2a00000070b21568944642c4003120400798145c90005000070001c2e9280c80c0e41112000080d03225100d030700309003802c1c80c05000c0500e000080d11041e03440c1c5507480d15101c1c2e1175510111000d5602a144038100042c001e00042c602c8002e500416111007000090000000c0700a01307001d18600c564030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 25788180 1250 25786930 25786951
    0x70c0803162d030203060f12010608011508031614030406110715050a0809010e1005010302240a03050a060905041208010609180209030c150309012d090f02030d020d0206 74
    0x3502d401d4880402e0b900740003260603007030141c1c581e100e0400140b85000141019604000003180d00300b03415805400200403504450001c00c00310400a501c000307281601d024202c4180e03c2080984484500c00d040c20000701d000e91740b400c0380882218480c42c20756000c0d62000b0001030703a2413a00d542c6010301f0310401d801812505529061541c020344094154011840a0410300110b940015805417007904619140001142603443e4020300c40c8400000344001c2c00180e000703409000b1a0603080f00440c5480c55103118041555013801c12440044000d46001031400b425161030301d00000c0d001e1100c0c080c80340214442c0711404800c09603034100501c200c170160722031020004001d20401c50403c0c980b90368866000464000345c1e4492507403011030724200841100030342100710844080d5031401000c1c0550b0052041034002e004004003460144442610700b908a20080b0aa02000714050056404219424852071060000d803860b600000e0412000c000c60382c0251300078112400031654180b091540c00f041d01003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 25789430 1250 25788180 25788227
    0x60a03060212181518070302040501061205060607020904021005090a0609080c300f1c0f03090b070806030f01060e060f01020601080d050703090e010801090314090d0b070c080316 78
    0x405903101000c00303490001740f0381210710485960f86042c0040c0c005980c01a1017480b09503501c900003001c070268007128140c81407500d03011542618100741100e0981d90000d0154400752282d408002e450140c0310035803003d0003420002081c5a0b1600c4807a18000c0400b522042c142030b283c0103507a800c1030f40c40b801651080b103030940c429020b02c85220350802c400d40c1c0380d15101c031403031004140c1a141140700040c5000c54401c5003c0100c030481001d1220a15000c3d954a44039181034000d000e50594017104001045205004001040300380705000300b41d400a001012141c1201600000608483d8141c0088440c98200c60030804c060070180c407200c5e4812002c2c0b004200c5036140007401e07515554001104420410000b600205040c402d0102d00080c0211040034481560742d07a04181c0205074450382180811860f4034428450307008903064800740403018244440b41c190565615414800c002d00d82414458107549085c007164443c0c0c05940300795410205d0341e640704070b26030010b0b1070000550700e140ea4060b0140c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 25790680 1250 25789430 25789453
    0x60b0301031104090f08030601020109050304030501050126070501030203040309030b13030e030d12020c03090a0803090a150806010f03060b0a0302090906030d0c110a0e0408030a060f0503030a0503060a0306021218 93
    0x61011140780e60000092901d0b48c5500300104d005d450600703000f404610000c00c0100a10106501c8030707040320784a10b031031404151a5801c8400100024015445c0f50300000c03820003403035000390010b60b400781c0700b4075015046503200c0d40d030040b00403c1520700040000030079207030100b01a0003000c1d992600204400402103072820700001014860080303a0031111a40200c3c0900600305c0030820b5a12450000741301c8000340e500c41c03410316a13a4015007640f80c813420b8078550005500c40e240c0703038800402035240e075602000d9444900550b400180c02909008040c1c0d11000028070070030740409411001c100c6d41d00540da8012410801c04030b40b40240126110341c000481d16104660840d80380100d09070301c44004404403080c6000036100d11419030020f0741c0b048840f01004104040400214803410044a0030072849488140c00110320440b40140c80d0198020440307080c0c8540501d000d5517000074003e0800c4040303500e0342c2c1c401003030343c1204414100812628041c00110000c00340e01c480c40044000040602c0c02c0744 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 25791930 1250 25790680 25790693
    0x130f030e060c0f0d0311041a0705150f060d0c03030503190608010f1d0d110c0306070309060c02120306040207110310021e18040203250f020c0a03020a030b0910060b030103110409 78
    0x42d4805d4501d109084607a0003416800341303089c0d40c803281d00003058a070038072031f00440c030710314000f0032110400151410000100c403071a291180600d0b0503000308190503810f065030303016140e40c2e0020b0f161031184d41039184003030b000c1d0b01c0a001d00c1014203900000400c407000640c03080010b40c2c3c5640c0451844031903518030702c0c20003140007a103980285010724146280d145a100a02e0900001103400c5030540921010020100e80540000b411244103c2d810044149118800c0b03032294034030004000344660400c085441c5190580180501038080c4d4440d012903032030100000c2ca005001c075006c3c4d0f0401d8001c10780101100c0c2c0c0c411389540c081928020300d4600040d079403011000103082c8182500c00d85d070100102d041d030300300c02d071a03081400b200d41b40300b644446a0480241c04009c80200000051245018507003860030000640e4041ba607019003012100c07030650b13490307001c5514000c00f40c40451166100440b40c50542d401900700a0213914030341c070764035419810b0130b5904c480346e42c580030300950801405500040c1c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 25793180 1250 25791930 25791937
    0x1a0f0103021c020702060705060703060f12050a1103010b0405090f010606050a0801090c0e130902100203071104020304030c0507030c0608010f03081602060d02040e01090605010305130f030e060c0f0d0311 89
    0x282e890016075461084c40010080d00a02a01400a01c9400704010035a80c16601803c02e9416000b01d1050103a0b50f00c550b008040d4645d500100716404c00c4c03001900146192210300b0707000078020000b0880501c41004901203820494151249600082d040c11420700d0a2041c60060041441c20ba46031106607040540310002c1171050043c043d54504250350107511840682c00b040c0d000819241c02032131041d18601c080c1648800a0f84a8840d0b000c0440565000008039a00d0590200212080d190150700308002904010300a50a00030341030b0b4400001007080c4840005940b0032442c0903078085c107140c8010102c841c160426140d0100307400e018008101c1b80740070380301070244110795171500f00f1051001c03e03e5400384180054035140081400701d40070070000601c41c140da403444020003038182d56030011029104291190074501c03241c0002400440c068260385000180642480c02c0114004401300f01c45a2115010072641d8015440c2e20500160138882511241503500e005c2c0003201c0440704fe082c0621 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 25794430 1250 25793180 25793227
    0x501020a0b0403031b03150e060a03032001020408060703061a0d020c0c04050106050403020114070b1909020d030c14070503060a020a0908010e01020405031608070504050603101a0f010302 82
    0x310030000140805100b5004217a00b0300201d0081910f000d0340030405409401d40400d05203211070141c03004280c0982076680148541c100a08003880079141d51000c0d2415920b049a0a51024070740c0300741500c102c000d00040006010381c1d4020851841c103160010200c0340030360001c030315142031040450b08500145083d2403074100d02207801640c69402c0b000941c42d040814140c0e54105092100000c0c05c00c2d04040035008890007a05c4800c1c1c10420b0f90074006261040d11001818016040c021a41ca0b5110ba0040901d0006000740040d0044554001496694900c80300714001444506c6850402c11441c40003496521500d000348006800e103400203859074001031444024690210343c0008031441400d0b80001080e0300780080002400e10358105010350702a0203a140a40719210700482032a40009441c411141081d018240712424981080041c14000c0d012903414400e03540180d080d034035640300d2050b03001c4001180008042d171100c01e00010720080540a41854414800d100301e124141c0c400c0324018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 25795680 1250 25794430 25794443
    0x5060409020d0902100918020309190c120602270d020103020310050a0f0303090506030c18010c081908070c020915010c08040303050301080c04061d0612010c050915040501020a 77
    0x596615808400520201c1c50280d17110441d840b184c01c0f00c64000d03100d01c0a5647d555081100c04a94501050030783c44269103020007640b2031081000800503204003048270510610859980310342d540300000740d41c41c4868040e04d1540e8005402120a80d21611032450315610801e2226541140e90000c1c1c1080000c64000e4141600000010b01c203a0070100d5100141900402042000e5151404800903460b40d02084000c56080407004c01c1c02d1030a1000d892103117407e001400d00d4040044500710008114400186c14885080a010001848407000d4024070754500110b000c960303d01c0b00002e000c0307100504101c051116500c006800b580754002c00c6540060001c2603110750308400d0004035000e20b031400d4068407145021401204042d03111005604a507180c104030750040c0c1d00082000100e401034400d84c181c512034070701c012114032840065190b001d5001072004a0440d403c0001500b5181c10b600580c00003040041d40c0301c20392401d21001c81d600203402d9a201d0030f107400c02001035550700b051a03024103c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 25796930 1250 25795680 25795687
    0x3030516050c040914060109060302060418021209030a0906030c0e06130509090f01050c040b0d0507110708010b0103060f0503030306150906161101020105040809010507050f030f040317040506040902 87
    0xa0101c00c000303404140c0c901820401010a582c01d04003443c03940071180303c02ca406000d000251010950003100180c4c4d40080c0000d24083c40e2103c4414078604030800865515000e01031848031099a103a000e208001590203590740303010b180f0008005480d50b0300080e083c1032030190401490341c3d014403136401c10002502d100e5a81d085c2010707038040a441960026910000840070000d1803180800d049103a0900c04000307201c0394440311802807550180780540c14142130f082c800740407007901642056401201c02d00300001107409070407505090610982109440d80e4480004071125613041c07040b48000c02c0e0111a902140d41048000b83d245e11000d0b00003445610050b5030f082e4048602802c131030904000800780c6966140c003415544042200079401c1c5c58416440c007415200354010700403c0e11640c1c1c0000841e19040d507940054900f500008800d41d440d2081e00c0d031015416a08100800064600050443d180e81c83c51620000340d5100d15588580110240410812030725904c040d9403d454003000f0150b103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 25798180 1250 25796930 25796933
    0xb01020f0303040f1a01030201020d031d0703050105090f12121b04030609020103051f150216090506040b03160b09040f14040201020c0607030905060a0302070b01170c01030603030516 80
    0x80c106504640d144140000414041000201c20203a0709481c402c038066000311081480500d0103540910020b80942c12541440410714401ea00c414000d1880400d10940014044185480c0400c01d410441c1e4a0b0341d210700340320900307404110030b00075007400f14000d0040b1165032762080300602a0045040100b0043c0004c42e941c1c4d05105422510300c8142030042d07440d075541c0d003410030180c0307203440d4264042460b02d000305421140c0c90084512038000b007035109015034540101201070160080150046000ea50794000c8008003035902031000700079000010440d403d000f0100701c211240410b00900c44e40c003911107800150381e99886101210000e110241c0c940c410800407801800c50781168111041c034200c1885807007880c00c401740340141c0c000e80c00c84500b420b0300410700019108440b0007402040018000f0070152911000400d07075041c82e89405401d108072561100220082070b001ba01c800700c8182c100300c080f1441040004030f581030918040c02130038955180034080303111b075440c1806401c001061140 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 25799430 1250 25798180 25798183
    0x2010e12030c19060c0c0f11060c0d020304090c020f060103060509120a0f03240302060c0f0105010f170313180605061c2a0c0501060302271008100b0102 67
    0x302c00c08a00001d681d14410510001081c070b0b4952003088034510f150003209a1715601c584007100480c3c3d440349203444500c40b1600c1c4c402010200c2daa110f603014504001c211940402440014604a00b5400860301d4034202680300042e5510074481c413045510090800d0161000026281e0469412900000d10741d110401c1d040d080405004560707055640c0041c03509000359004451000c1410159010410b044d10081c1c00409004134818012559510759014009841c2000041c40d603220f072201100c122081e444034150035140300740d000c07170b83c07001c03242030304000e0030300712884034605c4484440296141c0380d104c40240044130b450303000d01200481e8404151a10200395840340000e81001003e8517161240c1202c450401240030160b445840d0810b1800030746410f0201034041e00000d950000150314001c81002c45209001c0b000640f502d41d240e100010158864201c03c42d10022003c10802d101056640f00016000380035000713000c035021003c802c220ba04004140482d42c0c11030800041a00450140103d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 25800680 1250 25799430 25799437
    0xc090f180303010308040303110f031902160314070909151a0a0b040611070b0a0c02130504080703030506030607080c030a06081501050406060503010303020c04021c0203090604030201051302010e1203 87
    0x180c00d03a2100000200903c50042c0250003101e110b40e45150b944901c0850b815101e4603401882402c503801030108031000140c05001c01100c038070301d104541405c080114007240805031070340140d034040d00288460482031402e01c014005424a0309041c8034900c00d5a40d118002d03040c44c1300c2840190741c0c401c400c502c5025510528203164100400b0714260316100c6c182003007a90300c50300c5018041180082d50600d81c0c040030030120203c456402c0c0741801e01c40800d10940f0424a25201203a00c05c0d107045403070b0107400a034400d0728080d03801000065240d01c084d107009022910064241131103644414204810703154824001c0358401902d2800359142e441d03007642c0b074000d00142c1d00075003918004e502c07004400c2c0c108082a241250070880d0705006c0d00d583e483c0d0903140ba04c4280000750040c1c00070080b519240c2401c0c0c000b8003d00e103e00803001440303401c2000800c00c1b41c04c252034508a50b00454280402c1c1642400f8240d08441d6038039107007407a4036043e030001c0c0024015503a0540107542509500c43c1200c03090081c3c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 25801930 1250 25800680 25800721
    0xc08010203070f0305011502070e1510090806151c03030b0402180306010902040e010909030507020a06020a1b1d040f0b010608011a030f06040e0106051003060e090c090f 74
    0x250344904120801503d060564500302c00000d161500014110590a84003028500907030007406a05081007492000c4283c0182404105803400282c02c8294461a10700c0d28404d150b80d8030304815900f0403111a0074550040c040100c0071001c409070100c42c0c0d41d21154040c0a100303c1344038004c088002e00d4268058200c14142035032007803000c500524a41441c12413514a51000c4060b580c0580c1c84421103000c134050f60041c0c1292161079001401061382d1980090307000c0e80a07003460750500c41170350700040302d05166400820050708104103d00401c01c0345075405100645a07100100307040e042c01001440307041910007003040342019a000c142031058403001050420742001c113680c280c0d03860715800740454000f8491050100410128510355120364401e807400b0b0008404507481c1612448200400f4022b0b40b4410502c81d540c50800150a40d5005100d4181c412280c4012406c6072801100c0040c086c4000d120050300e41002d907601c562a500e0712580766004800c00e640c20b9454580ca11545c647c0c5010448 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 25803180 1250 25801930 25801933
    0x501090b09070303031b020c190302030318040510050105030a0b06070b0f0f15010801050904020103020c010f0501080d020118020904080d02030a020909070e0102070308030717011409060306040305030109090c08 92
    0x244901c941d00800e291040d2806a101809816081c100000348110095840c0c030050300040c2000b8000d1a003213000c000c040c0c04d4002501d060946a40020381142d0140010741841802d01000c5045d50401d800fa07554030001c0c52510780080703880c00c00080c0440c80005c00c000c2c540c6d0350724100d0f540c0c2c607903809080d6844140c1284401c602c52502e03420020f09100d0540308030100100d1440000c04903440c019019000c0300040c0d5641030503910300014051a020003410490500d602801103000c0a0700c240309150341842d0980700403401f54580b0702020304020700d0040d08001c590400d580003030358800c03480140d00071540c150741542e46a40d0f6810b2043c0c00307009550750300e10944e00000500804010079000b401c00c0340000c543c2c1d030140742c0301d040341514002c1002503502d0250f04410b100300003140c0e0322009142e00c4085414103c8480041d48060032544109802000481c0440b03035200556041040c1c00d140c0c0014140c0081c041c2d0f09203603d000d0414001441001905a1141d9101041004429510b4000d242010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 25804430 1250 25803180 25803203
    0x30a020102370605060103110f040521030c060117010c021902010e090108010501030c0905010e070809010204050d03120507030203090307080d09020618041a0117040c051507060e0a0c0b07050109 85
    0x1410f20050641540c1d5140024101841039580c040120203c6600c3c1c1e60a0408624051401041c410219248800c020701e4480c030b41c2c80e001a1040620042c103001494a0150000707604051080c101c0d500c0f2160005c07203da140c2030850781e02e4ec0e0005007801c014076491404c3c5140740000d2004072848581e11085c182c001007103400004100405410046c1a07034400c03c110840252585c80090849401b4860f08103451940720200f5a9a0301441c1e4498100b5602e8002500d03040d1104081000054248000c5000a6600d80090350400103489410703000302451a003949142444c0101958074003c110340580a43d500103600782c0b91a9450748980042d03a0301400c141d031580c0b1800c01e114089104510381a00641c01e020702500b11580349032a5440641c016100c400d10040300e402105510b450003801112480324121000c1150750300c20807640c900c3c24003005040d6460a07030b490008143c1c2c1031088002c0d60b590103408150001a071052a110a80312035031040d680700e842e607040150143c043c0d5000940031901d1607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 25805680 1250 25804430 25804433
    0xb1903150b13062705010c0303090203030f0c060901020a020d0513090c0e03010c0905100e130203040503070201020708060601080a0504051c05040603110711041d010e0109030e030a02010237 83
    0x5218030300490703107076031249469513100300d078120079101c2001060500340034401814442c2c0d40c01101000a0030b40640b800244190260380401e01c0c5a010184542d00c80d403010503045481d9004011140c0e00108490080d41040509d00010350755110300d58900050020200d84440301d946990502401080c01030010311608840b0f1304041c0981030008040b034042d508043e0b445200301d0050380d40d00110b40029080001005180c4401c4034440b92503a4010b5008001000190540e01c00e400514040c50046000d95a07581c503a2001a1904c10281d00164464000d5001c002081c2e8000000703540c49007481700081941d0b9100d280140c208442500b1821183c802488928845980a800b801c1070f207010b03131401c02406000340d4040e0700e2802107502c02000d0070003a00e4018400c1c00c041e00160360b21070040e00d181080c089030070b90140c207491400b406124569992250041416407000f43c61050384015030140070591020b80000752125041210004402c40801950520411815012035580c540a00c0d0ba401041035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 25806930 1250 25805680 25805707
    0x70c06090b1009020703020c0415030501060f09060510020a0f030909090c05010908011401030602090301060e0c03040c060f0503040b090c0315010807170d0c03052703070b1903150b 79
    0x1501d00403840707000842e01280c884030510840307a4050700f40d0000d0902d0000f5800304005401400002081d030020f00340f00100183c000d0154402903c0c0f5200e01c20400c50624054004031102c941c0290700c282d24024070114141d40101e602d03129190025505e000c00c2c50360342020b48002c003082c1d002c64111490000009c0901a080c40c0100544401341d0320401040d582d0100c550036520780d1450164030402d000e0041000403619402040801e2000d00041307080c540d034820140e44640111400f400c0c0c2e0000100304002c0181920841001d4103032800e100101c80b00d1282c000302940001800100500d100001040000c5001c0107110081d410090071103070000480d00000300040303070070720804c03070789104560300032075580c0d0401d0007402140140740081180341601c4204855000b05800e081c2e040c07210070000b01c030041040081b94441205c21b102030152421007030040c0752070701c52503038082042e004042c004115040c4c002c6a602f00d82034880c1c9004a039003e03810704040301c42c1d221944240790300d03640042c0c0800d10810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 25808180 1250 25806930 25806953
    0x50901060f031a031b0d080a02030705010605031203060105131511060f04020607030f031806091101030501051509060904020c07060207060516151d160f0b030402040203070c0609 78
    0x41d5035020f220000c044118050046401c52500303a0503040701344288070000c9065070b0041c407800c004104100d4a181500c0e0420154842d22001c0016040000c0c0b030428000c0c00d0140e0b40040c41c0c240d0040801d03d8501d840b6219a00000d0802c1c0c0c10000005000040501c020a0b103501400020070201d841e00c0d1040c501174000e81400000740103500400000801c0c8901b0344c0d980718403554010788518941081e41d079046446245103074440c014503070780c3d184900000045500808142d80709007400191f001d158105501c1ca182604c640714101401c00c00113000c40c0e00e40c0401409410003016009407203248110019900d8001c103507140350080e101140c03d030340a860025a41c02115115026521000e0b101d00c011601846031a4503500324a01740103110000902980e0340c8aa002d41000c0c00040d00714811050032021060101d42c201d290784000f280d00d81075108105804c0060038040d500c00300143c50058016002c0c0402031001c2d100d20b5000c00003440c1070b4014140c8a40c80c5501000402c404041450940313594030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 25809430 1250 25808180 25808207
    0x2180306010b0a1101060f090207020a0f030506060a0801020324010c02090408041a0f090d06060b030a0f0501140d0209090a1401020304030813030507060507020f030705010209030c0102070b07061505090106 90
    0x4c0c603c60540000f09018440c040a4a417110081d400f03450800755030001a50040004076041003104000041c01403c000031341001d0740c8500050111801c0081c10070840b41d1540d00000003913481001480340e08406403503078100e201c0c0784200324910703802000010303100a40840c0e400b070741180064080104000809000344191200100014442964041c000071140144001d2499001040145004d24a00310602100303c51003080007203941e98403036200c80200d81060350101003480d11181c03400f48261b118090f141c007401c0304108030090202184c0c0040c5014403508cd01900030814080440d00c103c10038003d00582d6500010500102d60a0440a60003903004035400d900150383d1314003040301c032001c2554101c11b00b034043e5101406c100d1661221001000003614101c10b612400c0021f00c0b5065042c009014a10701800005848804000c141810010890754942c110740042d1000c0c403000b1603100c00d490116030030110010b010700800100b00a520455001107901021890000445542c00543ca50616 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 25810680 1250 25809430 25809437
    0x6020303100f0501090308180406060305060315060f150903010903050403060b06031902090f03010e010f0b15070818060409050a0c0305161b0b0703150b04030b06010302180306010b0a 80
    0x41e03075901a03102c0700700a4011540040c80b402020008900d0980c00382c98003141054404458400020000302100e00607445540841d89820400c40d01d840d00384003030b403a4198a080ea505941c40e00d44006030704811301007000e0384a446000105c0e4046c2c0d03410000d5038074201025002304903814a41c100a0320075009440200c4020b400d102802d0f40034200401500d00408115103107810a24a054a18019400100303049400600f42440803585030b50900408011190f0b04000007811243c280c1c04006540769228014015a524551420005588400c0312280740d0460396003501d50606480c403843c84825090b00503440800400c000c06c2641e03841d0b000794003403103140900700032980340c10f40150241c80c0c08496402c540d0000400010019018260240120b142140e001034101030340d03902c01951080c199003020000342c0c0c408001c60342c0c8601c04480310141c9a9840340c142000d24640d9101c1003204000d045504040d004510848142c09141c2c8840742101d009040e90290340c3c640c0d1001150f60403003102d01001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 25811930 1250 25810680 25810711
    0x4090308060901060203040602030301170f0105040303021806041406031b040e1909050a0201030c0504030c090621150b010e03010504060f0c0905010504030209060f0909060f07030c081609090606020303 88
    0x5174000000c41d401c1b118250091820f5030301c1c22106414028510704214614003c0722074410040800b0303c9543d01c0765109850050701c50980d446c406c0d55030407080050b030703004060421051280c00e8035031002d42040c0c0800c690060740c90380da145210548805e0541024003024002c0f5000c034241801d00003040c4a40140105101d64400c4019000d00303540c400e5401400c1a0840203001000d54429044080e50498500b0400d150076030b03d64901030b02d050706030300000c407040ea5038000f4845501c6c0102c454010340712007007001500c1d20031500d9074043d1035500c02005060b160742d00041c10f03480c0d000300c02c054080130008001300302c81d19060400001030126a200440610b140c04030000259001f8020315003900c0069503110300f09800c5a0a04c03035074200281c0740d00e92206c4028452007040d510812400d01c1554180302500f91818100d0000030b16a6019050806160401d000040c060b0b43c8030481c03a900036100103d65243c80c07000103066541c91241c0e0801c1c1c0c00030b82402c07000718445800200550080c4043e1200085 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 25813180 1250 25811930 25811939
    0xa06030b131509020d03030c090803070305090906060406080a050405010605210606060a120506030a0204020f07120e0d02010807210c1106100605220609060e030d0f0c05010204030204090308060901 86
    0x315404024005d5100300044181000700c7e100b03a112007280ca1031814a000415100d00a240c030355003268038114009000080d008000742010094260030100c1500c1350303418a420414058000200100601a01d680e5080001c0074040b003500b02000501c4040c210850714456811000f0000140c191480c031144542d0340407074142c1c101001142c0c006296652106841b109803c800d002404015000c1d5034584209031401c00036035514401460316144880015039902020308d46003e010805400b40000d004540c1d41c80b812940f11000100402c40d824a09840c45984980c001da0300c0002d094180c020b0200142d034a2400c3e00c0e13141d070080d1800841911400034030492441103030b50386d202c00c0740e410101072451041080501e0148014003036420100c88001283c4e807001448101a112940c0900000383c4401410890150001c1200c848060190082d00480007001c0c00980f011320650108401c00602c12020001d010342907055401a540c0288240041d840505004102c3c507000d885880c41100e15030300004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 25814430 1250 25813180 25813223
    0x90204090f0e0607140c0f030409050709060e03070b07080d06081b03030304021f050f030702030406111515010306051203210708070507020103091406040c090606020606090a06030b13 80
    0x5206801a0391140c00c0135660300b90179600c98010807036140b03261040710a1800817103010b0003e000a032010a40000d400d1500d00402880004154000818071542000c4111982c40104105059503002c1000b1551614a86400e019030b100d4030a0452000345080c20100f4141c00100f1400c2030007884c5c81031404240300700f6042540700c0c031007910300030b602040302c0402a101c4082d81e074544420302601c1c10b1280c1071191a400d410f0303440d4801c9034040c0051704001003c2c021945c01c50400423894200400500458002d20160f02020001030b1020103080d0400300e940e01075030305c6900b000c80a0640070340125048442022016a41d411074506030112030038404000040d4044036540612620199442c001241c403212000e646583c4091016410591595206400310f12500164144020300400420152520741480c2d0b850741820b402c00350259003801000c004142d0300040c0a900b080048414804035101c81e400c810060441c1d03400144280d00740340400020501020743e02070914011000951807503200075000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 25815680 1250 25814430 25814443
    0x10e060c040f050f01020a02060705010f051b0706050606040503010609020c120702060a030911040504030c020a2c060301060909050604150501060c030804020117100915080a0813090204090f0e 84
    0x64082c0e1180d4200b0803035031620301d0713401c0c9200b14180191040d00d805a00461043e502c8810203580c03a0f91699844c20304200e0303610034641d0100c06d203882510301440070070303442c5002e00c00d240d0003800e919110b0740410050380d0b400381160001d2500800810640d55034800502c0650002100e844050103160105580a586039013207171101c42c3c1c000c01c4a890204171010070740041c44d50740e40c2a90000c07413031111050540c4444c850240200d019459440041c001c6204010801402c1e410040300c850840c242c40d419402c030400c84070208010452086201e40c0c0d407501190050801c2e034008050070381031000c0715060020101c1d0f010f010320302480007000c07282c014144000c141c1d0020f01c40c400006156402c12030120384105010b82d08648145050309901e07181e2840000c0d01c0c80c1c10b5072015020a50120100b04402e000d200308a4000541440d411110f441c180311541c54014010000c1c00750400024000c0c042c05400b0301d201d000e0000900e0854035141c50300040301c002d00c500800c0413580c0c0c2c07820240500201001400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 25816930 1250 25815680 25815689
    0x150f0617010e0c0406080a060b0d060314010902030712080d0207030306051002030a090308030403050c100b01030c08060d030503040f05060f01050109050913020112020904060b12062b0312020a02010e060c04 90
    0x8540c90245030580c1118010001400c441d604c80d034858001c80c9c00d91900d001410aa104807a010802606504200d1070501081030f0800c000c1e854843c0207401a14003140180c11500c11208810344800b0a0800445a10480001ca503206200050400030940c041c3d104200750b94069901010340b114401c01640c0c0c83c446c2c00b040f4000b042c0c04450410005d0000c500455105100e07280c06810203196400307031403611a0362100b520702551158082429940d15120310000d14100345080030107410203101080c1c0b2086c1e100c4020707007084000000030f0300340245101c000754156406001c0302c11a203410140054005002e00801e030010b80b01840008613458a003189078010003040d2982c0c02c0c2c46200ba4010356011000740e007801005a024480c4180680e181c1c03003144024520102003903920041024100000e0000406c003a20070000c4003e1582e80003c0c0c1441c11481c84601701300034403025a2428107440880c202e40b0840401030000a40005a983c1900040c941c00d1241c403c41c0d409403075524101041340258003c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 25818180 1250 25816930 25816951
    0x516050708090f060c0d030f110405101106010603050f0c0703051812010c030605120105040507170a060519050c040503030d09020402070204111201080703020607020103150f0617010e 80
    0xd04000300701101d008112801d0020300c0500c2d01200c50002c9516900504081c115903040100b5960445030503000e02c042d10901da00041203e800c02d030b020f0b9903050056001da240181c510080c005080790107140000c0308108044215509583c0d02c69000340a40780440c1c00d0312001400310042400d4905281c00c0d01c01c210387c952038103070500c0d404800140e003104144d180f259015078002800d1068000078441c03001005030955001c12003d0070141442103e00158407290901c0e0326104c00c2001280d40401e507030055402c60004800000b40784008a03281c10301392080545143e2030001409551080f0406c0c000e17604030078060521040c0c0c0c502020700c11a00075446140d805801c108581070f01388007198049060749100400060030204150041011030b2016210b04c94142c0d80001e07400d00d181c1d00d51070076a00524030000201607184c210f50102e0710a00598000034185521501c01c91a440b40070541c90004d081d070645060f0402e561900001d01c4404020202d1028410a06c0007040d020008140790380314510012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 25819430 1250 25818180 25818187
    0x6070507060e01051216120501091508030403030503040213020903030f0702031e06060609010915030501061d01020d0e03010219020c0f01031103061207091a01081501091703040b070f06051605 84
    0x6d004001c2d90000850082c100074410040508544042c4200c3c2d0191000c07000014008041c6c0a0b080a003c0b05a000030a4507401844104000703030344002203c2d407040c0d064840c00324484504010340d01a010781030800d94140808a1000d403211040000b82444500840c104c030071074107040006012840401d0a602c0564201000140c990708101d0018013441030180340102d0495a5014400c0d00306075180042c0c00065241c00041108aa02072410009044141c10000e610a08400040e540d14400306596044c0141110304201658003981910740c4206c1200720003c128040e143c0c025200d80c10303500313410310a401c00ca0403880c642d4828880c0800c1d441d0980c0301249507440d6102040548203c3d03448e000c1a6201d84000407440030f11030300818800242d07200400c0a80720800002401d442130091107a00400c402c40c0802106a92141c1000101c80002c0d48544240c03080603040c605504c5550041c800e01c9000103881020003c51410401e8941d020303a800304220749030080000607842c440d50f44032002850a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 25820680 1250 25819430 25819441
    0x1b03070524370f080411010e1219030e0108150103090c05062a01110904020c0304051906090e07021e010b0d0b010f06020a030c030509010c0b01180506040203011203030e030906070507060e010512 85
    0x10300841c0b806030382c0200002aa142030009d510314000e851030380400271041c8402c0c00d500701b5421440300c803000c040034207045089160a628141c01c62580340c1600381010340b6a000d41d03082c001807159001c06450054245a51450703501e007444455600b1030100a0ba007541a80710180d0000e06114100c5409460b26809140000442c01c220103034000b048211400d0004020008440d9644141400e5905481e003040c880036103080805008030b00303560311000d140300c1070404002e5229070101e00c1d00c03103440c4062341490410010510940c014603400c4000ea4215000000f4442413200389404541210b030311900d144580d58a821007281c03a6848150010003062203040d860300040d006030003400300c640040c54001c090150503140d82c00114070a0340128001d20f501c68084520b00c4850050581c401802e59065195500d061036039070b1410070f020070140401d40d55a4102d1802442802264074a000c010241034540d00c0c01d00300651901990300c2001e0104260301006096940210281c030f0f222099503444a1203640e45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 25821930 1250 25820680 25820687
    0x20c1e0613080d0c0611031006120e06070509040e01020c0703020d110904080703270b1309051f0f06050d020313051b03070524370f08041101 62
    0x208481c220040c0c0400da911040041c41c107048941e42d5402408142da0034480d04030f0f08465103d45c0755103010010032005480114901c403c03030301e007441c18951092030002c40c4001001d01341c0002d44540116820310207640c0d0300c80c000d8007810030110340c00c2000340f040c80d0b181404c0f403080310352a81c81c6800c070030350801c0580703000e44001c8030307860103003601c0501c03041c1060009921240489084543c0200402c1c507100741a030208407025050450b100c070b0a4600881c810a003c03884007442001e404250000f054080703044601d0031a0000e2014800620950402000d00d500e9500010081e4828850584000038081c6061421208072400c07600d5162410441d50014400303944010101080140310321404800104104102c001410440030f1031040383c9907140c20035007007402c90707071010788543c02100500d4920900202d0031038030340b401c84041d603a44041e94460042c0c0e1284983c400c41c100480c0040003040c40f1002d80195070b100c10a66200403042881910070380302114241c034003401d041410490703031200307502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 25823180 1250 25821930 25821937
    0x3061419120507090903051e0903060621010e030d050f01060504030f020d0516050a060903170703020a140706020c10020a020906040605130605040b041b08100306050f07020c1e06 78
    0x140058840c81c0c2e13111200348040c1e40e8040703421000110000307001e1388107600e07010340301400c15000201c440c80e29990100182c0d8070200134140c94854104e9100c5000300100b80c0c4489007081800c41d000b4420284401c88003507d980201d0390450300c45081c080014222640202d04e14180c03900d6480b02410203046480b0809000c00d403103012604040140400c001090f8200890b4102c2200407110811442c1413006001d02e80324141d004005110301040117000040058513040840d030804000d02c1d0716031000382400c134940300c1845806001c402a60442110036040480e450301a1002602103a10714401c40003403000c076a091400200068000b40041d0006190801c01c00350008002403021030460f456100061002600141c80e1002d1507032094100001c0c14603001e84108000b00310f80c01c0066003165000d11303810080340d040d00820800300c2400100f8154203014000095500520108664548040306064031201a1102005481100c414104510f0301040904400031101c0c2c03507880c070841400500074070780c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 25824430 1250 25823180 25823183
    0x1306020f03090303040201030b01020708030901030e030702120a05070510050a0f020c100c0204050f0c040302060a0203070b0408210907091a1905010807080f0103080a0309020d030306141912 83
    0x64003081208204850440a14050607a07100616900c1c00c10b88009400ca4940348081c9040d0742003400200712140c00401038840b002420b00b00444d0419101940c5411403040a1000354801203e0799041c2c0d0890000444c906098811000c4886050b102c41c01c000b0350f00280380c41080010b408020004146200c0c004280750607030a80101d9402c07a14010004034180c602404a000140d0320110030300540c582406565040b0441d84402941c034245100b10803001d10460201034041c0d000001c0c09400e140c0700300215404540c00003050140c5003040c0c50451100d074400000311800d41c0c0d20410b40d100110305a00d84078058413801e40204115480c0009072005000b83c3c000c40701441902c801000b0184d2107450f06c40301d04171524660400c40a041000242c202c03400a4038110800450b1001c210b08401da41c50744505403038008006503141c0d036480c0d50072009801346c03940094200d1b80345840041019019001001919841d002004443c0c1d10703003051049c4403013419464038100b0100f5508001050b940c4e505660a40d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 25825680 1250 25824430 25824443
    0x109091505130e010e06061e03030a0c05030705010504080301090b040209030c0f010c0c08030a03060812090d0c09020c0c030708011817040803070305090a0501030605010f080a0b040905030403060f0504050613 91
    0x2243c4080d2075400c462407000c0048039604041c080201a25003402000b2300c0e00e41c18041c203c0960045000320b40c1d40c0c05410b80c40e200740f10680461400340642042902c02c9107502034001d11862070a0301e0092143c0d0002c0c850426401d040c406852140c0c40c041c02600d440900240c000d10103841e241c400c0040380031314500e145040c445001e001c600800c03120340d4464040d04d81c44005660b2181140002411100c3c03544c0421403507000070303010800c0c403a806011166000c000700d42405151051b07040030b103004040d43c1d100c101350038400140601c44200c0401c04c51a2600b0441c152140669038503021f0303003070740d21420503040705920a00e2400d002a02003145c580c28442606142420580c6514820380b07990b1182e98154045640490b80c55058904440c522000c0c100030b103420301c04185424006844014810000001d014132440084d6284110740c2c081d200b005030040003400490458108907407a41d2141c0000d5601a062001c2c40407036039124000d4034041ca82c8071000f0b08184e0303150314900700d07060341c50207040358034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 25826930 1250 25825680 25825691
    0xd030309062003250c060207150903020a0507080c0d060504050307021203030f09070302010801060e120d030c0201050109050408030c070503070203060a061701050403091211040507090302010909150513 88
    0x1000b64904107850410000e40300b180d0b8030b052206002c0481c00d03403a869071014419000c2035821141e401078040001c5580003c000da226811032410102a200c0c101c42401010301d0700e400b0105140d400500c285802d800380c025520699142c920715a00c4004444409401ca000300f0b0007a0300041c0c1d140d1005612034095825070342000c0c1180e0000e0703221008a031440100781d01c0030041c4043c2e150308441d5140c100041600404141c3d00d964006050b1a03814420343c818008545540c1106840b00c4924403c08000719096540059081901600038900303207496400661a023000440c465486c1e00c1101e000d190806103560641c2c0c0d17201c8110481d03501c45c045c201d405000c24000d5800584017004918001d20b44c99a02080182c00d0079000c1c110303001400c088178801c0cdc2c140000d000110740c120740312505071030004d80540008405801e0080140d0800c0300c0150f001341c80d0000304400658008405da054034802d07618000c0303083d41e0b00b480d5001c2e52401068082c605403254000c0000b0b01c3c20341035089903813695400201c0c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 25828180 1250 25826930 25826951
    0x304061115010b0408060f06030c120109020a0b22080316030504030b0108030d0c0507030c0b07050f0d0f05060102070e01121104021605010b0a26030403080301060e0f0402090d03030906 81
    0x5440000c2c0d00030200c403400070805204064040c0401c5910847d1412905040e1a00d503001980c2d848922207468010004041d18042c07808c401c1d045070151035000307000d0010550745d815103400c6961114101020000c04160000c211041000c074840c1104d5240d0025414030703001c1c4254003000040c0203411170074031001304800000a07410319480b40c000c00600700030307503100c185041c1200c082d1002203624001b0814104014000203400c010402c1e00980c00040b0440707d0b68803204180c645204102d007001c00d0038004512720084ad440394000c02c40441211600340f180d61189001039a4824950280082800c02180188400070381504100c5580740109403007011400c00b9004603089a01c0b400079407800401403403a100c1407040900940036205000c4e108001c00e03e14154100e81c140044481410120306201415050f03131100700103a4001e180c00200c5240e8a595483c00584510950101c0034054461902200c109207000d1081ea03441c2d6001030301c0401501e034165401c40c010b000d80c0508417800c40e9942d0b941803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 25829430 1250 25828180 25828213
    0x170c090103080711010504030201051b07080a0506090c0118060302090a0512061b040810180b09071a1305090a0905030a2001020403080702130e0a0b0412020601050303040611 76
    0x180214002e8100a9490741a403c1440f5818049081c082c1405020001000143d9000049581070000003000090300c06140903080d0030103c4960001a55104001000007401004603210380106290403c80d074907040401d006455030301140001842d0403840704010808940a42c001340202c000042004c020107850b54000b40320840500e8414680b0340c850010010b039003002c8698050148005c0100c542802c2c40d040f00d036952924a8200780c00307a180c44822000584000d1140300c04559881210401c0900e000c110f4655201c005100b4004411029011106503028039011140342c110b21349401d5009a00b0041880855080608500c82140d0384c1e00190001c6841032000d802c2c851040d07590340031512007092a551141012040409141e40304000400015540b40308541488ad815221913910035551805107000701b11021010401c0e004d100b85c12000c022400c4101c81c4158416007513007a03180840c9108a075180024010309805600c03c000c1840581d005000b4402e1400701c24044030b9030011a2903050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 25830680 1250 25829430 25829449
    0x4200304050f07120302010c030e1209030c131b0c0c03020409030e0307031506050109050306150d06090c06110a03090302010e1201020d050103050d051905030606091806030d020a0507170c 82
    0x4041c0c4c21083c0081d8400c0550a000d011002c03640d9150521050b118240241c0c1c45414030b01c400b24082d84009184101c0e91818803207100800741c001d00200e400384100c040003001d060340c1160750007111256144c412929014500b4000d9270b540208624480070b080d1f03800d10004095a6001354140012076030307041c015990812551001c0c5105505180c4440b00018809050701d819800203414000c04141c02e02594800040c825448610b13032300800910640c03a00419451108a48054509400c1c4040c0d00c0034004010042c1c400c60350a40e81c0c5810010308038000c684c54035004c0e14010009804680d080025600c24171000b19101c4d0010a070018040c0d11f0031005007242e005594480d00c1c55280e03030042041c04818800d00250121506100b480d007095203c4a1350050241e00d1400207003c804808100c5585945040c1c4000d01d42c00742c50141c0d010b0359900c507a23848810032603040e4403d04c0f0b42c1d003943e00a580301003038000b4102c1d48000204202800c060b6012990301390300245541c1441500c880d200159690801c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 25831930 1250 25830680 25830689
    0x40905041101090602030a02060c0a030e030412050d0c02030a060506030f010207200402030702030307210c020115050604180b040902100c030215240103141e010504200304050f07 78
    0x402901856800140140f4250b078040301c00d5400510000c100244c004c25800d500c08000c542540c1e41c1c0400c0503041e4010495544207070b103d403001280106640441c14400102e203030050003101d509288880301101c451440a03002901900081d2500d40020b100d5001642c0000f0004d049d181e0039490745c1e041d02c2c00c80c0c002c0d01003690130100300848d51a0242c024203500300442c0090394158654070b00000701079600d2102070070042c2040f4000c0c480c3e0128050000740c44090b400800420f1007102c0a03208024041d04c6440d05c0c5030007800100301c1c00142460301d030701104e085400107100c0c48032041682600c1c2d00100103080340701381c1064070303041044016500c100c04044042d50903240e1210410361402c00038a00b44103484c0c06042019020288400032166001c6004240864031951402e4035a02004030003600e81d413290400502540b20600c411460a00525885501d0701c8149a6403a0303610b00400c82550040761104c04003403080011000c0b20304040b4000d560040c091821990143c1c46030300c91510b024040e500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 25833180 1250 25831930 25831943
    0x1050316120f0b091b030d0512040804030803100501020d0207270603080301060203071202060103050a1104090b0703020d0c0507020901050405040c0e070e0913050606062d090102010b0108071407030504090504 91
    0x84140d82544941c80c11422170003540100041d001c031210151071480350305800341c8400e40f100e00040422584504690195a2060545803030381408188998008034601406015000395240e018003103100040d684122280203640f181d809110141048035070045140c000705803a1074440c0800414511030085000305880d81c0111350780c03840d078104043d0101032414070400319000400104041100099141c0f0a140c000f82c1c0c40c2075103680480058000d007401e130001044e464808007000340080d0194042c00c150103642909105440d500607044030244a45030000750b00c200c180005020a05043d842642c0c800e1240c51030060450b01c407185110b20b801c1c2280ca501c0002d25100f081040d5007040004181c00c00400c6c0c01d04010b520f095560241c688500614180c000c00c008202004103002d1111080039070070010501800d880f00e0084200b86940c001a1300354095824041200d5013940f00b940d2551040b0000c0c1d0b50390121140c04844034203640d00140040d403c005060001180b85804c40c403607903029600c03c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 25834430 1250 25833180 25833193
    0x30b030f0c010201061d0f1509070306170a0812070c08030a0c030f020f07020409050c0a061227080a03090602120604060902030105011205040c03050a0c06020601050316120f0b09 78
    0x5000909580940d0071030300348804184100101042c11a04551f0018405144515036640d000140c200c0b00b24060f00003a80403803000140044240c1540c04081602c1d5484486c0c0310b80300305140155070b00d071021078004103526002c0203080e0244034032000d83c1e40c00040714078100341418071503100c00e20fa5401c16984043da050307407071007032815964052180c000c0c0c07020420740960401031441d2910030746024a68001c7e000715102c5100700d0800c1414000d011018100404001ea000d0b01c409004082c50712000607a081285040c2100b4030302c002c0500c41c01c905c04401d41804901c4e4103140d0742d856594010340003c0d8141034031a4203120004056001402841020202e90215458520200020b03592598480c803002e0384104018002640e100041c001068050301c07000c1140d807168a098440d43e9000d07480a0201c0c002c010501d401c10400e04d95034812100b0aa00712041641c944007010385075008015032150000001c1410000142e603001c542d181240560f04103003040384240c0381da00c81c002040b1110722203a00400c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 25835680 1250 25834430 25834453
    0xf03070b03090613020f04021b0102030a061a040503120d021207110c010e1005090609040e0a0311010e0607120b13020a170105090402040e0703051510080c03070306050601030b030f 79
    0x80102d5a4405035950604442c64a10780201d0590315030b44040d103001f9a00000c070510482400d00300c01c9002c440b0200210b6891600001100040100d4000d54030080898610000710107406401c1e6803ea9070010060103804501c101c1c40002d0b40d00c4441c061401c9a000d001000e030110303000d1440380c03040a50f621213030305514102c5040c81c141107202c0e10755418484440300161080c0c442c01000885540b2500340aa45e6400d503200080707030750040810240e8440e0801900340d0310380c940810901100c4c0c0c030a4890807121b000d4201c0b881d007030f24a040c01412060b4003041c005030041d880340d80c0800a549030a603001490032554808600d0002c00007188407080364000411101d46580100c0c0d0301809403142c944a40554107080c00035201c01c2c40a0006071055444442d0901c00c0303041032060300c0084d58080f00f1078007000c3c1c4422847e901050200e5040c5440c0c02c2c1da60300060b03034150128401c000c0d110024003900a140c00e640da030400411001d810141010340d28491120103803401c00104c00702e01800402040d404020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 25836930 1250 25835680 25835683
    0x1230705070302090c03151c020409050a0605090601080c012105100303090b040503030706020a031e0b090609010503030a030c0216060201021201050a03050a030f1b0602030a0507110d0c020f03070b0309 88
    0x250074841e185c0010410011041541045d01e038095008642c4d5280444624405c915821403018001e0b500070305d0002c10004002c3c0016400d0200780c4104003d020a6a43d4030480e911801b0910035503055410044501440e988111642d8540da0a4014810342c0c108500011504992048440000e4024030780014824503420003c0d2000400d03511801d9403800f42000c3c0460b84900598034010074480c2c0100d11250101d02a4010240045060071103100c4058401080406840e0301562240601e01c42000b0621500302410042d0503101e02800661502994074030840c005c02a0316104003c50040e100c04149001c420024440109000e50001d80c07591251003941c916200306a000a10078400100c0800004002162400e010380d05801d08042104030400195035900d00080d4084003040c50658000810180e03a018600450920804004550340c101060395040d00c070001704000b9501403502c031245c00740300300120300043d41f01914240290040b10b000c00c2c40c21300c450b00030341e02c0500040100140b9050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 25838180 1250 25836930 25836949
    0x1030b040203090d0c02120d0c140705011409121e060a05070c02010c170703050d050f060a09200705030309061302130b010203070507030b06040609140601230705070302 74
    0x811201140b035418000300c03155840040026040a01c00b444004400359544c01c119403200c000e81406a0f06680c640f402c000704001801d00c41119540903400c50017414080000300388041d140107844014120100b02d820500d10703045490b500d5441f050013481c1005500040c484404e00c50b80c0c07103070040c83d90503441c141942031a000801400a040c501000c004e0034650001010700c01d0f540a0800003003410f41c9003821481d0783c1c1040003001a02100140500805600000419220002d0f070340410040d103400c6600c1541d11015a1400d51040080d08103000074902d541c802c1601c2c4100295080007034405010a02c0150441d800903281a0008070410007801414030030300c1d51100b200080d151807005103900055241802480c0c184845a0714819140942d00030412512140d40100460341c12503074900d4503005036201210030300d0080741000400034409030039000348408550035007000b10580e80d52800458000c40d41061213103841c02d04400100414000d84020005140a040904200340c01c50051005014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 25839430 1250 25838180 25838201
    0x303061a07080f0306010908120a030e06060306010b09010306030b0c0c010e070b0d0507030608030c060411120a080705031303050a0201030b06030f1302030313080303090c030102040303090608040602070b04110103 93
    0x542045040d0001c0c0c4034000b10f6114034803451680351685c407240c004840c90411600200018820821044207807000c1802605070900c090790207022040e01121100e4030761506580681d0181c0c0110014414980010b02410304c0820624000902c50380d203490b562044202940d4120102ca00055100c008040038065007a0349446200201100d6182200f50145481450550710200b80e441000c20060b030304c650012001031548401300e035200c5003442481515040107440850740c0c0038244951400604280903031b140c032603120401400349a44151181c5410f03034400501241d15000410500702448150390702d6502941c0104024010707205141300160480da040e80c2d4003032180c0000d0040103940410109030b02c0d401882903002e80d100080b203101203440c60141e8034128038401608200032031100000005148280c208004036030900c219881494201e2240b8000540001d40100043c80507501440c3c10541052044e40010311300422612409910300d42035804691802e41501000595030f03050241000c1d14 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 25840680 1250 25839430 25839479
    0x30705030606060301090b150c060610020105011401050f090d030c060b01020a02090408070501091709030705180714040b0706020702010e0406150c020102031201080105100909030e0f0f040603030306 87
    0x5042c07035000100f0b540814030803a50030716200c142d4080203882c1c441101c01c0807003240008648442150b40c403240c4a60341200c200d4011940740109552507881402554102c808c3c184144220800d00030044844e54407084518020b01c0d0700300850075580d00c62585980e8150b009503202c800b4600307146405410b40c1d408405150441d44844091400f5130781d1502e12a4000c0e0740800c0c403543d144024a040d5002d4400c1080203040050802c122009580c0d002c070051034a204100d0607a03c91607180c034200240035409031031041d04070682d136000a00040c00b4420721205a00d0300700c0128102560741c007424402c1d41c00000c00302d42c01c41e000b081d407000b10b503040040c000740c11108481c04d2010609044c800c6074013400501c1c41504000a641c0d40c1c20035640280125003a9111f100d107950303110741c1c6880d022070291800399803481d860341b4044400500d8440038030a036100103038142e80f41071503505900204400c1c034103550740c01c1e9401040c0c00c48084a0350356a20454009501c03944011412500c6c1c0121403440a68820205c00031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 25841930 1250 25840680 25840693
    0xb07090806100e180129040e06040b0609130503040612061410030c0323040209010b0c0304061409100315050303040609031203140a0b030c100206040201080604110a0e03070503 77
    0x801450f03006a070200c003180c004a1084000110640500048507040544102c4103c500ca42080740444507299060103440030701003030502d0504181c0c0c4040454000c1d1081c403002011529500d00410000d41291205c0e28080c02280f143d12280d0440c0d200341c6c480c9002c02e00040f110030125449005107002001c01e8210081e44480c1e20000c10052200710303030000101903076400140c2e40711303000c2e62054917081c40400708950f50304140355000381000401da8081c1d01c1004c1c07840c0000307140b0307a402d0102c0350603045882c0030b10b06291900b4000d413a4544421440c00e0020300520000d60b140e1194107405101054990b00814403280c114208088000d507500528000e0700100410f220b503c0d00300c884581183c0d444428200e070660041d2080340101221406001648080780a01c02c084200b900100b0700c2d82022130950310348a21850421000310205130062016802a44c0064050341c000d00b00c2c140d1107800a000440d5145026800b0016030b44000e0444011032001c00091142d41400c01800f006040d082e00140700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 25843180 1250 25841930 25841939
    0x201020c01080403020712030201061d01050114030709090207060b011403010b0717040803040f09060902030103150c020a0602130609090608060f0403030e0312010303030513020109060e06070b0709080610 89
    0x450303841001645060102d6000880c040620070003200c0c0082641c04000c0c55076040618000380609040d100e00710840815040710840c040441c04118100c44050311f801c00007034500425007095400c010550700a1150b40040060000f055000a04500d403141c1000946110504000b60010840340e13500b680c40e0f0304c20320050003100c1d4410220392006130081c0321a4070800c8482e0f051000e80c0329075048030705203000105000038004618130881096690b074640c103101494a40c03000300202e0000344000f4221303600409080c0500340340fa41c002198070318244152051a07903e43c88003016a88510503400c100322801c50100040341d80155413102505900000340b1050b403405c00801c0d079a04000c0c1c0b00060107405140172600700740c0079500c6140c501c8080c8050b65140c011110030200c12030400d2101303030701003410b0500080c0054042e0500c00740840e4140c48280c80e00b0300305070044900b10f41071054203400200422030f00c0045504407005601c02c20441e42d80052441c10400d8450811030090400d822802d61100c0030300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 25844430 1250 25843180 25843183
    0x230708041211010905030c03122401031806060b0306040c1e0e010504030b01060504060807051e030c0706090b04110307060c1509060f0902121b090402120f0610060c020102 75
    0x54664007a8600803a11030071400502d40101120500184a407000051500f180c07076000c03010f000400b007803a40c009403d40e251048604251507965840001e00000c941740c00301c5600942c8110b02c042c00d5042080740000075543e6800442c1d121350052020100c000c010004186020b000f580e241c0000b0307241548080c8a20206c44003500e882e400d451050048a96540d070309a4418015580210f0700000c40c84070a50391410017401c503502c58003e00c40041c2d0303158000741019003d4422608180300c83e80c034030071107841880c0d08451107401c0a01142d03200c401c01c00580c0f011031010700407958018095103185003242800d15191182280302e01131503000307400c52001040b1007608070380c0801c04250408007601103107074031440c2c110040581050040c500740c80c0c103040c04110180c591260340524400da076510300308112041a0f0f55603c1c907812402d0395079525500c411206d400c21070110b9800500c0a4207001d00310961040075410281ea460f480300c0d840d030141c0200300411040101c000b00409071400c0807403035441c003500002d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 25845680 1250 25844430 25844453
    0x5030604020f19030609152301020304090e0105090105010f0807061d040c02010903020c0a0b18040e07030302060403081b070201030504113c0d02210123070804 70
    0x2148925030204020003103007a00b4003141c82a42c0e02500c0c8100c08840a03502a004000714003ca65030180f8200707a1314072003540307a04014282c03507450100207880307110800400c281000c85459141140001c2c400020b000059016101086007468000f18003842e0044c54a400c680e01684034404012107a0800c0055034008141e0070103403001807400340d030f5884840300c1c1c0306406a504c4a083d5005454428210034159040d800024668829030a491041c04044100818a00a80a000d0040000b0000c600d011100009408605603003e400440c40745019011607041114503481a00903800050410082651220304681e07c4500b0780b03144218503883c02d80000ca01d01a00c000241410b80d41e4000c98280305500b800814118030040078000864003582b803910a449000c10f1610040d05500400805112517010400c8003100160803101e80e00c001350204a00c05507101000025070428517000c0c07070492000c0c002d032a90000143c0d0004410401141e20451015000300980d0400c085c000620001401d2900034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 25846930 1250 25845680 25845691
    0xa0501050307020a02090a020702040b0108040c05010e0109120b10060203040308030c030601030b100e150405030606090c0408010204090204060e03030705060106050309031204050a030207230d060612050106030b07030c0503 97
    0x20394582c0e0761140107a203054940132000c0d51207200d4070104103201c000b940040452600c265001c2c07008003400c0c00195803030a42650006c1c01900003210901c1254811152002943d0051510040c0c15139035011003403031142d40d11030555900340798200304061404070101507001841284001c1d45080d00d1510b038200d10b4040603280880550b000000b041803607200360800200c00d04010607407840c803240904080c001c01c100707806e460300404036400448080000103094404031080640640005d55030036042001450009210038600030040c1301c0424a18070074805480649000074006a0702c60500c84041d10302544001c10350301c030b40c0c01005010700060010800c03504541d56401d10b207407240c850501090450250f1482c40c0d01c40d6002100f0482030140c0011030120160290b000d0300d2089864411251502c440a001c5141083d9902c1c55141e29040400842158600482d00043d82c80c0d154064041320728142c44041d00c042e0744494060007403110401b0002d800000c107050401c04070740011009082801300404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 25848180 1250 25846930 25846937
    0x8010b040603020f0f0a0c060506180f0a1509060e010b0a051b031606020d0605100203040b09030313080a0311030a0e15040b13080105010510080f0601170a0e0f0c0a0501 74
    0x200c03440700d205084251100c8080d19a0840d1b11a6400c900013080301c00c00c1c00b02602d400e410007000c10f840b410418a1260303030003034800d6402d1080e9180e0780396803a4000c02400b40e005150380c94502c40c24a80098548801500c601c00c80030984170728064144400280c10b810403403100c0c1003007240070b00b03c0741c0000440e100f0070f1105480d124943c040c050642e041d4015000520001da45036030420040050943c010b01440c2c0c01e00d003040010a894000744803494100044610260b88204010302900f04500090105e101b401012603160106507121410b0104182d4006215688211103920030190402030900070a411b8900950401311031500082c1310f1402c08402500401c1150352040c0d0340305101c0c00700d502520b070061501d030b84d1b46404420032541c5002031142c912103501e480000303e054a0948020f0f03000313607c103544540300703a00c1e0940c02a1103091b019044034144030070721203003518a0908460003446180c0b02c00002840d072a485c02c09a090510307c0c0048401508000c980350040e80d110002101600c40a01c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 25849430 1250 25848180 25848187
    0x203190809100f06090e010606050a0c08070c090c08060103091110051b07030515010509010b1b0a08090f0301060e0106110f0f07031101051201031e02150409050708010b04060302 78
    0x10030850402010b00c000a02081c1000c0c145040c065158101c20704544a1110800003d55200c036034500301c8506014a0380065800c00c4610b61180c41520380904143c05a80140e180103100d580e56017944013554070002d00d5640b2000148a580d400402c1c0030340c480d40a0906201a0016a682900c9298100c007c0ca02c00e05140c1c8002c1c0000b031080060b038035528580a9141028411031400940d58003091108480520609229400305032407402603504a408c040c0840146900300547c04100e5002017404041e4006806003c105141c020046401c90b18001d02203181d40340702d01014050704412240c000340c040d03810300a04004182e46580c080f41110308a180400c80c0400165005003003c030001c0b040101485a010b42847c244404a864400c491282c107441d080d091100c00151140e004d8005820342c441071000041000c1083c40e04042e42e41c02000b00c8094a1808030760004000071f03414051041c00c40c5e0045000e002d21403091007034907040b5200382801c117560341c07420a402da030600c280c1c000c4608054011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 25850680 1250 25849430 25849441
    0x3070509180a0c0e010501021209090403050d1a040f020a0c080d020c060c041509061e09050409030503040c0e010305030d091a010306051e060604090203130f05060403090602031908 79
    0x81d000180007030120007560011061824030030340c1450180203040000800c0b04c0002059030000a416000003110441182407200f01401c22440040007407054041c08402c1044041c084151f100c0c0c3c181703002180b2040108484d00c4028802158014008441103503c1003103140703002902702200104a5510244240e81d8094400e1038602a00840c490007209104980910050b414040090300940300200c080f50a0b00c45070302d41c1100d4084e6584158030115884034a8040c0310501e04c440400c4030006814100d0704669030341d0114080710403481c0140c1c0098000320a0004120708412a1002400c15034a816100d5041d519050b4603407140e0041100030540e44c100403c1081600402015124900e00d201c0d841d030342e52070401e4809804200c514405c5030040c440d001d41d4281440c08281d0162101809503820142000d140d1002580040c00d07101002c4081c11246000460303006504007868400e001a1403541002d103005404002e0540080080d500240015146150014100415602c00d40b600305140d4640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 25851930 1250 25850680 25850701
    0x9090406060b070c090c02010c090509090f25050a0303090506220905071205012103120c0507051203040f02040b0111120306010e090108030d0203061c06050a06090b03070509 76
    0x1d690100800c50030205580c001c1c001c0040150080b0340300301d8424062054100030807800c07210312420800101d18182030610035801c1c204403190b8071102c83c81c11520301d141c4404684e032a101800a458424051544402c40111010341000004290039920000d4881c210f0341d0107002940d40f8044c0f20b00500d00401c0d031480155500103040c020b8035028403c0603034180c6030040c20020b4102100c00a0224013a500211994a028418035040b01e510104007100c0e6034004010b488a24140f1000350700300000303480205e02c100100d100b011000040b5448103a96051145803c5081103503140e043c0542d0282071007008086003a001c0094890b81d412a40086d41543caa401a5a0400e101d06014a948142c500f01120295060000c50040c0d0090701c400440d5184130f4104080358409009a0505800a100c1004401c4150b0095908130030001d00c40c0043c0f20341c90303880700b854022403101038907115114000c1c0081603101703104000c082c0881c0e210030302c518900741005c01d0343c4080030b102c1c0c2030055180a000825002d43d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 25853180 1250 25851930 25851941
    0x181503020313060e030a03060b07030819060503060c070201091d060402090409081b0609030403020303180102010b0d030c031205060d020d03030b0a03080c06060612071d271501020309090406 83
    0x52000007013184030011002030350750b50080750103540468600714010422042c12003e982a150781940d4910341a0380310001e204114004030300444103141c403810045040d0b5800d0021501c152200c04c003441c0c8504480c0001804042d0320f503c00120250301100600640303001c0d24007958031410540300540d5695001000c01c004040c054005000340202043e402c40600c10304501035034901c0c01c4002c0341c02d191a00c2005a0703c91080c0e00c00290b1551081001070608070a5108411f00048140000a072403a1404080340c1c250005420440010760030b0b652000416070060030024402c401024100000d140040116480c1000d0030000b81c41410840550070805120707401621040002520340300460365a450a14034070340140d02d01054a001e07030000100242400000d85a21041002d01d2142d2900c034100252440c404915140360000c0303010145200f00e0725142c00b4141564011694040f98400030105080320f46c10242070302c84c0044070415070032101d81e800002e584502504403500189911645070410003800b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 25854430 1250 25853180 25853183
    0x1080622060f05090d0e0109030b06031501060804051005010b03070c050c030304140a09020307050f07030e040203160206070f09150c060606020105040201021006052b14010606181503020313 83
    0xa00303001c0c2e076081620b5142c0021307000d403c407070045503090384440c0c1060312003001c02050680001c10700401040800c04000003d904044003805803101f420707908440b8407055901f41c02400214107901d00344000c1020400c0f80ea00c44104d010070400c01c1c1e50401d8480f074860310010300941c081010040380181403000922030482e13692801011240c0d1903640d880381c111442c6414140381d03c500031300600010000020700890b07120754010f95403586050366550091116410045050b010050a12910450394645100030340c020045010b030f42c1c070501c1041c1802132820f0350007000c00c410040e100d46581145a04035038400180e4010074920404500d800004442c2c40007149005170090717060001c002011034040d07014600442c000ea0a403440c03008002004826034006125040d048600d0847e180e80180c1c2c1503255400c0034101099085e0340181503116071012a40d400129207860355a42010000700781c2100d91022445100c00040240c0e92400300e40c40b03100000c4129070402c1c5600040000e0704030141101c0403100c0b6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 25855680 1250 25854430 25854443
    0x3080a020903160512030f0f0f0c0718050703020c0a030305090f1219020303150402032806050102071509030b040c0b0a08070e040e030904090c081207150501080622 72
    0x203c5040d42502d0403424284107050107511140000b03400c01c00040300300c2e02c00a21110f403c0389000075200800c1d08070361102c411058000001d00180d481e0102c24443c4070001c00c2045000046800c02c44140404c0780c0c00035085006240c41080421080c180100f10440e0040d0907090009581c0d40c1e80042c0c1d42802401f400b8404a4050f45001680000804c00645079007200c540d240d5464441d40c10003680d9038882078480c081c40b4011320a0002c22490150000c50b4040e00090010140d0840c08624100800b80c1c0022038110301d4a0b10800c0c0019681007000100900640c61444154510824050040c48090001415080340040020140040f050340b0a0060400c66840c0350390300341004004041078000c1d00d04000155038189008440d1506001c1c060140c080d0070042c0d494166060100402882074101c226030320349004030700240000003440090140c0765404001c03607840165141401d1b00c0030b40f914020061502d04001070205030400909103a101c07802d101c1c07051120380c400684150301035684200400c0d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 25856930 1250 25855680 25855693
    0x19020f04030615050d02061606020f0304110103050a0b1e0409021801030317040209180708030a0c060b040203090706140705011a09070309050d0302090103020403020409030522060c03080a020903 85
    0x420000c0e600c94000c00a2501142180d55150f2041040417655044c000c4d610410600c1440d1000482c0c00745800300303600c54000149040303044010702c04960021a802c1e59440c940e04244a101d5800d4003031503510070441c4d002040f1365040c044c0011000c8100c0c011074003da4100c0300c01c1042c1501d6070780c02460020b070010003a40e030020b60704960601c03054090004800040c80d41e141202d5401210031541c0c0295802488104280c2d10582c0c024212509040160203034481c1302000602c1c0d0200b0b200500f03410b94207945194448519003400004c1d958000f0403640110b1040080203017a110101c1d03a034083c0c81350b0b854580c0c00c4d00c0300c200d10140d071800b82c0b0801805952030300042c0482001c1175418448008070a4a074011541c2c1c50110940495010000180190304500c040030fa070301b4461350050030a00c005040040c1025140d4010038100c030100c5038220b002c1400080c07003005950b04040020300c1120f01c0c0c1c010311440c03170504c80000c1c80c0d41040e03c402018002c070000032880e19016501030f50861000030381111603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 25858180 1250 25856930 25856933
    0x8070f050c070503070e061903020904110d020d0305130f03050a020402090102150a1b0305060d1101050c0a06020903072705060103140406050f07020a17030402180106020f0c0d030819020f0403 84
    0x201b030801690181e126000442c02e8903126031148501108403500100801c55580e03c0da22400144000000010b0340030361214071280042e610864800c42e50b034003954038680c44603105946001c00e502190080c100c807404480f02040000c400150a00c0040e03070658000d6280c1e01c0e004010713407806409800a220201c4030b242040f605101a510984201451030340340c83e2000c00310007041d811240d090b245190820303a14584030002c00ca0002000255038410715110b45401d41c0010002c1c00d06000820455100d60009500d54041c6000c101c1e9801a040586507059244142130309481f4002100e0350390180d5035155130024009030301903480740c8002c076000d11503d21686094501180101740484601441c90740340d0000c1402584000341764820b25500c05072a001401104039990981e8100a00803a8001c020010f0070000c00b050f003a609000f0403c84e0001c0005140400500341040000c1c094640109070030448131004c264001c40300c542119202820071040c03040392850b50064460024461108040001c0000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 25859430 1250 25858180 25858199
    0x7260408010c02060a050c030f1012030801090b03030a0f080a110a1107090213030305031801020a0207080601051e0d02040f02030702070e0c03010f0509190603080406030c08070f050c07050307 84
    0x1042c10b140e090300c0442d9500030045080b0f500660700c000d4455001d00c0040e00c5401140d500075080440311000030003040d510000c0039a0341d42a15001c40000d11803000401118520303014001c405071046000d1400d040000070002c1c880203c00122400b00710546002c140401540e42c05008001d01d1a0b2007a551280b078118054600d0412a040b070116224040300000c3d401d9151007a204043d004006510b142841c41c0c404607180c0d00041c01140303a103014440f154012030700c2407008007620400342c0c014051003480e00e01c4040c1000c005a00c01d9005003010f03189802c03d1910002120020705040301e003080042c02078008240104034000082281e680300000340420a500000c3c580c017240c181036410342084d03407031070003000c800e0100b0f12903404034078803008092000c4c0c0b615a450701e51200006000d1402030741c0071200d01043d034909a10070385103110002424040d03107505000d484103408950504241d18105040e00501c51142e00b080f41c4100301e8041b9031803c0c410410f011070401030100400304e6203e240c032001d618 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 25860680 1250 25859430 25859441
    0x5070c0f060c1e02010504230d052b0203030610050915030a06080703050d0c081215011e0e1c060501090204090b031513021c031809060b0726040801 65
    0xd0f120400c1c502c1c4421520402180c3c0d9250995041e0364880c00d140c5094880c2c102d00c8050703150b400004c0901e01c00110580c9440c01078050640c019401070452103c10401c110903211560741c40710107241e0044245d00c00c15000800c80741c0100c025901800e0200c42d00408540900407580319685c0304502003580c4161100d01c0c00038601071480140c04001940e074580b0b01c1e40c0e44041d03910004105030070020903140c0d0700740030340303044c16074980140c2d10380b807030b002125202c4882268120b032000310300e9003605114131255900968000403103082280400d0808580c3e8005461072460b08001c9204042d4a252615204006a51503c007154044424482561290031400194109000e141407092400021103820700c2c0000c4c200150403102480102c064840c40c2d968040102c901000361382050030f903025001843c0022104040c1540207584035401c4203120100000010560380c060140641040c90078040180040304450449501c0a40b168240d0b6460400c03030b402c1e524107660180b1100020038001001101034004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 25861930 1250 25860680 25860683
    0xe040b0c070305090415090b12070b0c0c0a03050109050c01030209030a2d03020109050607051201060e0303040b040806070905040c0e04090609020306090f06100e01050409060608070603060e0c04050d0305070c0f060c 94
    0x20b11549180e441801611102030044400e0ad40c020141005580c401000030100c1000003001e943c0031100307040c0407851046c80796204a805d80c1d512140c00051080c18800d440300c0b0502481c0c02c2d86040540e00001307070b031080c1da4400940801840740481002240c02a6454520b0f42031503e044201505801c000e8000d1040c2d2009580c1401610001680c0b544240201c0d032200035110035422440c6d08004c1f04540e04061400820303051710040102113882d44600001d88010513200c40240700c98074200030028040281c40c0d0041c3c1c05141040c04803500300350000c000d40c0050310292000a03008c90142401d0026000304040a50140034500c01e10903c40800b046424031200c1d400704070f40e090344842c45040b100200910660342190070101c0180500d01c0c250f084080740310b00441001c5a0241c440c0f111a08103084d0364015404650750748010450449268101c551001459410074109450200420300c01003c19030004c003003010018601c3d040010040d40d20010300301a0805507202c90300e03244054226001c7d07660 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 25863180 1250 25861930 25861949
    0xa1403040306060806040803070809030403150204170c0603150d02090405010b09180d110f01050115020f030c070306110d0608010b04050609090717030c06040c060305010e040b0c070305090415 84
    0xf40800c2c8450006803450040307502868052646d81c880300102c81008001d403410043e03000410001011481d081c065401d00184217100503a9103191a650700c01d51504800c180c4003e800c10341c28501e0036560f6009990780503160a0b000c4030640900b0000032010443c55500a5200007801d0038803051000540c003221f85090b0030341d24104030f07407a15103924030503410081603452140d001b611a5403034035200d0440080304000800482e007014002c2c0000d0b50960700240c0018228160f42c049110081b681000075000485945001d1803400d0a03014429071110341c00d01014100c591941c0c2e0a0f02001e00c044100c81280104500030010540c83c0c11000b400f030001038001300e2040d030420002c40e0322468542203050003003413a5002850380f289448244401000341d03d0781c2c3c813031130700090145010b416424010503204078442c0c4101680d0600b05107001e000c0710300c1a00300c01c140c1000c000410000400704982260054010304601d500d40c029441d0807201c174032684030440d030054204124020f015500d5007103681510718150 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 25864430 1250 25863180 25863191
    0x60f0c0403050303130f05030307020a0215120a050403050f040609030201030f11090d03020715090801140f190f180c0504020306010c02011107030203070e010311010507020607020f030a1403040306 86
    0x264611124011404058415001000801c5607101d041c050a64014410108115146400c0e1503960075500704940c00703809038001411200461800003696114001001e901c2810300502d481074810740c980003031103030500e95510004501894049d0f81510408180040d080c0e64036034440030010091019848200e020034200201580605010f0007604800ca280520702801c124000301040380c540030310311017034040d40103550010920b8040482058035180031900c4204d521032902c60420b0841e1542159241922040b60a004141d201c6d100d06c1504124000385038083c40140c0345800e8002c002c501c000c103071594602914040c02644681c440741013140252407004080b80d844050006a200440340035001400c400b001d040158090789107200d0503041c69003194509a02e80d40413074508103594105c2c0b1031384c1c0910001001044548541c0740c0c80e00c0000e01c0e01c0c0781000c0b9940d000c50f84902070080028840c0250300340d10089070301c0c00c01440d0200c0d0b4010f40303001c0d0902501c14065441e0b601c503020039a07000b0b0401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 25865680 1250 25864430 25864441
    0x7050409030804060203070c060608030a0216031703071817010e1b060c1504060b031c050307050f0c01051f06030504080f16080f130e06100807050c030408060f 70
    0x28451103500a40540702e84809940b1130360350400a5000402120a2203070010406011404601c2440701514007440110750302c11401c078019142004103d0040846503882e0700501c0000c0b01030005024401080000c01e80302c0d00c4644d01035a083e900c40c01a0082c03003071f0040c3e001070400b00008802490b100054020404607200114498580008183c000b08841c4500c40001032800e00c90300420000529509481c0080040448880c1080080e034081c2c600c1c07615154926810314091101030b6450b115034140c1c00140f20400009020341c08010b01d413170284800450840c0324038404008461000900c20020403240c641907041e61884840d1030004e00802c4000d4130007252150103803050078015908801f03003a0400c0c00c405089061030b03206814191666102c0e55400c00050450805081c40f014141201034940300750081c8180f041d403040e84158070401d040c9040c000c041d120b01084289910702032900c40c4540d038039a030094981e489242c0d210091440300040009002d01d002c00c4c2d160241c0c49202c009603c64036003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 25866930 1250 25865680 25865689
    0x100c0804110108070806010f030b030118020109050607120c060615090806010f05060304060207030203040b040303080a0c171501090803040e04050c0102030415030b220b0103050c03090a03031d01060312020705 91
    0x80b110b41c0045170740c80000c2000d641c016151988001094500420803601d240e02082c00d4811300d071030782c84c207424032800c00303508540e00010114040d00c000d0703403400e0a00070243c40c0d0003600c01c03070806003400b40240c4501d60030a10040f500148060324001001b0100b400443c84001e000d000386205210b0640a02ca001040c3c02000078200012520000d021a085440310b0321041d00960140b070081782948820000051b43c0c0320410040c0005600903199980245811404402910101c1c2140c10801c254031440c83c204480c40c04419821401007020103144801c3c8000584104200343c025030114800451f0001d002e070140174919108034880c0090f2881440d10500699907401580a04180c030601c01c50070b500703104d01c254070000c803a00e00284a241c1c601030001302c1d000d507403601c152052119602c1e208040180d5806008068004204c00e40781482c1d450160f103a10b44139200b00400408050b01c68400c210400102800c0980c0844454002c003c919502e18007400f8a520705480e05002d40a05080003945140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 25868180 1250 25866930 25866947
    0xb1b0301171002090a05010806030f060f0703060801090b0426030109020723030f030a140109020711010207050a180e01050f01060f02070612020c030c01090b1f1202010c0203100c08041101 82
    0x25000c5c41d1075504101c019224038500400b015054402c01d1070082807018100304144c050f20814654a5140c1800c800c010150747d1590890a51a8140510700d0009249007107169401508a1044502071100d0749542038440015102d0000e600c00c00700012856100381c2e0300030000d0f94460b03110484401407000c194000c0160201884007030f80c0003400200d01866400c401035034040d03400000050541c0300740e1454040d40600ba08a850030982c08210b40d401c000340a0701c811041c130000d0000741030040c81c1a00088c422906030041c00288209010030501060700c42d0030034810994403400a01c00d41c45d0118034080340034000d201310000100034411f4024a80c1c00416010141d032800d44d41d8101e00504a03001c50040d610122240c0042e100800449000040c288103c1d041103104800c5184035050410001c603280140c820524101d0401910410030752110100b01d00c01d041e03080c240130594a14900000c1d081a544910121055082c1030f01080710551000f400b500c030702c1c400c00c00c1081600203000115112131 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 25869430 1250 25868180 25868197
    0x4091a0d020603040203030c0106030b0402040633020102090a030b0a0b0d030c02010827060f0604110d0506030a150c0210020901020a02012106030b06090112030206040b1b0301171002 80
    0x19400d024140150404400442c0d001e40080d044900c0c10045142c141d00b100c505d50710a0b03452081c0442403004514142c001d0074010402c00c1001c0b140000c01701d04a01074010b0009202c8000c030340400b041e10705c2900079015203020520041c0f00b20b2415960b0706201a181108650b81d280c62072a003c140d0b8158944031154468494140d620042c1140450f0b0054920b2030700505201a005006803a0340a60f4641034040507424003880064066410400d81a1401ca070000d03001070311407414000140024183c00b001e648901000c60004034881e120070340880e007844404100a0304028150300c10513031035006908503031008070880c2e00310342c82c800749000408124011103041c980140c01040e10100950b10400c0b404800c5020b901d6140c04e800825150b003002c480d102c1d802100c0d00300100e41040740510304031020b10b00402e01800e000550340881c3d03400940714403004200070f0503124148041011108541c40e0070110b002140c2e509603a07941c6640b08070000308994011280c040c03217220b40c081640007050090301d02e40c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 25870680 1250 25869430 25869439
    0xb030405060705130e0106020a030914010c020904060204080a081206040b0f1e030105070e0306010503030309070303110c100c110f130b010318060506180c04050f01030b0d0804091a 79
    0x25220382c241110254441c207245244000155004180c07074240560785030017804c20750001c0001f8640c40c43c01a14502041e4022603d40c402940014056608162144010b90781100d0003021580c071894244000d000b603800c886014400c40342c9040c00c00c01c40c24010045061010b11402e415902c01c02000b003a80e4900e03400035085028191100300d582000c44103205403504105100d107c13020841c2c0401c0c00c5440403900c120015074850b40d084182c0c00c060200c6030162006602445c6140761542001e596a016071000400708841c00134a40d80700d1a050103402c00707030785009191488020300c0040041018000d56025241c104540e104020701d4500004201c0f82c2050150800c041000540d4160004048a1040038107058940500140f1220641041c04d402482a40d000a072401c008050186a80c201d03080c83c90b96810032003d01aa02d003411007990110382c0e085602c6c2d1100400900101c0c00b400c90a0341c01900b10718500d01c104104180c810103403040d20840c000800090b804442c2e034203095881d0343c013140d420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 25871930 1250 25870680 25870693
    0x9050114040b031c03050118060b160c030807030203030118090f080d0b0909010c020606030303070801031707020d0c08010b010f05030606070309080a030c060c170f040203071710060b030405 83
    0x940c2066041400000b40007000d80350400b0800c00044280c00b0920080c0c0b000a0352840140a001555510018040041d1500704200e030f01746a41c0d110303944585d80d05900f110f40b4002d69070042152507600d280285510103005a200c8805150207540e0b90401c0c020360a004200c82c01907580030314580304621507a50040000c0450210544603828103070702c450070000e1502d840700018030680d1601c2002d01d0068000e00000039013520100402403c4c41405454184650020814491503590046020341500c0e0031040307624000744040110380c00d034894060000e4001211000c680c060110340b1030040d0403100d603c1c00a0160000200044840c0c02048a0f8500416801d2010a80900344075015000d0345120307042c901d03011500c83d030405241640c80304085001030141d419031010010300740980b00c0e00c0c0030f803820703c0d9104082d100c0300d0500d0f0728002403070311903804000b100240035540c0030441c4a0061000020030003440c00b42d1140c150b00d906002120b6101c7c5c500f01280000c198205508492096401c030010700031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 25873180 1250 25871930 25871969
    0x909050706030b010f0c0312060b0d14040b01140f040f020702090919030302130b19020c0114030403111f0911061905030a020702060a0503010311150f0d020d050709050a090501 77
    0x400080300b031000e40408c20321308002c81c0280c80c10302c6107030080d0140900080c1c40b0303100d54100e1000d0b55001c556080c01051020284400103650300c2c03000c0e040d1071201d400e02c00c038500340c10040340c142040511720503489070070811070300e004440d65030060148500070703100082e0580c0c850004540d20700311844000d0740716806200007000b0034801d278060000b00c100c108040d00c6559035805d110589410003036a21140d2008514041410360301040103440c01c00082c20403456441100741c030410345000080014041c014040c07803c10440070306220301c4562840d2561500e8100c058234140c200200145c410403070b511400381240090701d1401e03400391844a400b03001c1d4407094850b02032044520381c001400c56055550240005001030b59120080c04c1003030440d50310300b0340320b42c0341d401e0116402200c035404030300030340c0703c1107208201c004050126120b01e8144050555a042d07034804c500028402d2545400d0349501c2c000074041d10710341c031004143c201e0b58200c4401d1800390300c81421004450b0280b02d420180c00c4010014103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 25874430 1250 25873180 25873187
    0x6060806061b0a2f0a120204090b100807080102120106140408010c03020a09053c0301050406020a0f1704171213150c0806040905030906040909050706030b010f 70
    0x2d041c45041c84212000680240035182214040d0122007101d0408418043e40201900e540e0f44940d2605001001d80c20b500042843c4201c039014420040904002210a5403129004984140d51107a003411302031514482c0d400700b2041c11b028040300340c040c0c400c1c0050b01020500a42d0070b2981841060f4100c0d0b4a083c5e01550808100c0c240c0890004040c0000210325001303228500300020941c4001d80d46805912008140c100c551300034610422aa111040c0d000540d241440822181c03a088498405440310750409a40d1a400c100c962560920013088200402d0742c0190980c5040b039102c0c0c0c1c012840f980d406035015200701d04aa070103803551f840041d02150700b403035043c1059a00340380f04521300303175107241800c865020480e150700d0040d806801000420003680c180e80b0210a9000b010000d802c80e4039001082c4040203018640b240351524640424403005104503030300180001c1410b42e5895490700c119010301094942034416004a1100281190180c05080a03004059440040e181204035003038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 25875680 1250 25874430 25874437
    0x10b090102010617010e0c0907050a030e010e070807090c03050606030a0c0c020909060f01062313050d051b0405010f09050423031e09091909050102070809040f0606080606 75
    0x8904540d01d82c14005102c0961802146040c010080045401a500b095440c54480090348260088040004101d1403641c4032054814a001514000ca01040141c000c1800340000008040c0180100301c000a40a4000951141201d03d00c0e2003d115101d41903000350222030044419680203802000003030884501607001c2840c0d0203460410f034030350300e00e2600071441e003041c00c03149820103500840900030451070b50501103006202c1445c020840300e940008141c0054020406d6900d10f81c804210080b4004a07802c001c005000090441c09481d580c50038190764544140c00d6054890500048000c030703e0406008180c183d0b03401900140c0510700e0054060000e14000388280c6990103021b05107a503400b4141d02c51041c03514040c004684521400f01c2d4002600c518594045d600c1c10108487c81172616590b07103043d4000b8241425000302074a001c1180c01401400000810652002840804101c508000b0307040401e01500c0810025200d22030504c116045800b60001056075140014241e145c100010b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 25876930 1250 25875680 25875697
    0x603040c030606030c0302030c03010b030c150d0e0c01080108030c0d0e01030906060303080601140915031f0905070e01080f0a02130e010b091212030604050a110703031506090b03010b 80
    0xa0340050355a403105403c0b503041d5001101c5600c01c851040007503141c1000341140c20b45044008000400d2401c0c00213607144001c14240c5d0043c0076169942910040d24400d075a2495070800042c081141030901302a114089101c0b6140414403003000407030611400800d403551f2142c0c00c80100002c0c0311441e825207545468180d4141003503100c003036040001e8a24003880009500c60784965080b0b061080002d841e04d40304440500c54414203100114484d038842103031003d0010722820041d6030352105d0001d5014070740030ba04035449000d000540000c0c0400c0b982d20091080030700d0368a03004001c038010011544a8401c1c1c030700c0100c00805901140c0c8040c069402000007000085091a05565070400101c00d590309a010002641010800e007103142844c061400c0302003e0803000e031010042400344080b8900015144c42c1c0259540d4001808074522940811100d440700c1509548443c41c82c83c00070301230031004401d84522076419400142c213038026150328080d50040d001103070450307003424000c2c0015000401c0303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 25878180 1250 25876930 25876943
    0x8060109180f1202070504111603050c0f0a0209060414070e04020405030f0106090605101b0303200903011406030d030e0109061104090b0303190c0303090b0702010c0905091302060304 80
    0x6681d0014820818a4107035900c10410b00364540d4101d803004e1304002d842c0c0e2155010714241000101c01004000032035900da10420180382c400b43d40c0741022103440c022541e000c03007180702d1420903c00032440000d0b5154000e100702c440c21450b948690034001544c00e40b500e001c0c02d0301c10a0020520306c500980c4150791414000d0001400c0030b9591000a10b40550b4203906502c59640340014403d10040703001740c0001c0d080513180d0741c00003115070390018804a1400c80284400b40031401c18070415100b900701248455440d4040c44242042c941b60003500e5100846191280d0301e4000840340080500e0a050f01ca884010094000e802e0004002e901030181d0a040005a5588006000002d001c0c0e01c02c034040d80d104040721a84640c188a0010101e4040f070086a00c40c0e4414003500b22151043c00c0c41c005010201d14020a00150b0b83ca000c1d00540307010080100440070706001c0080301a4150f0060f04842006e44d6007005055969090019500060740c0e0052060b0035401c8a070003500701500116003081c0304a2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 25879430 1250 25878180 25878221
    0x3060b1503100501081b0415050c0303042a05091503010f02040603060305100212071b050f010506011706030601050603070207090e160918060c030902150301050a060908060109 77
    0x10500d155560044901c102e401001c40018051943d110b8402a8040f4002c2480c43e44180c0314240070045000d20b20aa1800b018280c15415082d413281c415101188035078000c40c1c0d20707030a01c0d141184521074020b8000400d0041c3c800b0b0320350410301c065010710885501a0051740c10340c407030420500b412185100000e0b010343d01c60700c0d015181c540341d00c020002000540d400040b494103501d0300324100201541580c5050f40140042d95014015050190304801d079400c150844904240010a18004205000d8454040c070416142c42c07100c1900076904ca030600366200c442521821089001a8406032005605684964010301450070300c100110341100c014012508041d40d101502d074241d940002042100350042502150701d48580c030f0015001d8100c1c03c0b0140a40100d4440c02c1901601428015060301e440f1109200c256000b0307800101e5440c0c001c0d001c0c250301224031031400b1312644284951805000d80e94800600184920f00040c25503d0384005024244d1a1030707040c6c0080c0130000d05880d212851311 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 25880680 1250 25879430 25879459
    0xf0f0703020c190c08060c0304120c02180708010509130807020607030e03060106020307030206010609120312020c100203041401090f060c02010b120615100504030b09101103090d030207030903060b 86
    0x115032884aa031300c108141320700d0600700324070281003010207001d86090000600c20302000509403203c407622096180f40c81d480220003800042c403c48000c8030140c4d403120096091061003075110b015241680c00c00d8134150090703222245a08008283e141c3c0203000411709016403801868140000c0000701e000c1d01d406c0026900000003e0b041c80c0c0c007070f4004005a80009124030802d90144a00d5004100764100610007500e021034943c4203000040c1c006042003282c2c50051080c440980c144c400d0900782004403000d03648544c2d0711000940c000c4c0c0b41a69007a455400e109580d410500501d14141d038030901040000060356102c2000c2c0159483c400e040d5522240c1c083d4581e15003640e9901d03580c00c50b800626240c100540501901c0f600b480d200d40c013440341174900e90030b03494020701100e088990001604005a0316405864203100400c60b4026600b420004950140050b41c400f45008024000c1642d02e00746041750194124880d1080c0100451400001080403c0c0b16503c440030110005d400f58882d000304 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 25881930 1250 25880680 25880713
    0x140109030f330f02030f0c0a03060e01080c01030e0a030c03050f07050318040509060105030c01050d1103090d140a09140d050a030807020d0e0915030307170a080f0f0703020c 76
    0x8080c4040a00c45191074401e02c6500c0500405043d014600011413660402c246203040d030700c030000c1c048003070843c0004850034022301c1b0383d200c40020301240104404951316a00c0407601c9180a141e443e002038202401c1c075443d03103008180c1c0c1c04429450b07140c9948120351686d054600d034001240040c1c131000705002040c00301d40300340001e03c010890b0248502d003a1002100f00000c1302c0c0041d00d407109070382c0100b00502440e1000034100c51046c01c04d003041515401020104809884010341c4880404404401d100310603500003500c01e0301e501242c42d0f202e4070145460404005004007070408001400321401040584100c40e8869840c00c03014110f62064540764440e03618001c00f00400700d00090703490b01000031190b41804810715000407480d20000c042d000b00001014080090030202401c44154481c032101e0340c0410031140c3c1640d00c5446081421408001c201c0e03590018000c160100b034480001518035110901020302c0f65008500d00c0d2a81c4c2c803451030032002900a4083e00a192256001742d401ca140c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 25883180 1250 25881930 25881983
    0x8040305010e0d0809060906150406030611040f080f030d0c0c0501051005030613030203070206090d1202060405010507030908071407170303010512010509060115021009060f0501140109030f 83
    0x403000610f45640e400c00000e1a10344003c0c681c1c4107a4111a0901090480120308141c00c0301c0800762802c4191a501c00040040809a200609151500310300700d485807007c4001e03004031074501501640c02c642d0784903502c6e201c0c1e800c0d03640d1080c99001044034a1a403c0141d00c903000103042464950308840f2035590341d40c21240162010090f03680c1030003040207180340c2000456070019210100e400060790b540d402a41d02d02074942c2c001c4c4980d001141580107a01c1300c0340030280080e042030075000a03180000019494401c1941c080d00d895003020001100f03580280280c0c1159544400018640b0320035449848220f0344141103400f880c09800300c005500c41c4248012418080a0f10246590b54540420000304454010124103940d04000411410090114a0504454884c002c80c02c1c8032140d40812400c0040c2c1d61992101c040c40e000d10002406030550001d603085055090401050342c84501040c81e00d01e4810400b070000d140900140b001400444900400078072881012002c540c8160703440c2c10840 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 25884430 1250 25883180 25883201
    0xa0f06020f0f190302040b04060c0615030317070e0f01050c01060e07030204180504030e13060506070c03020108061f050901050c030c0c090a021602041d01090c0810020310050405040804030501 84
    0x4000301c3c0c0b004080381282500460301409040841c6072074580842440603010f180304210901514414100900800343c1001c846000468503101c0e4680d213915010b884494040400002c2d040c0400014055501030200c140003258024403e940240c071200045503d0341c071105081200e5503d80900045000740c25107070500510f0540c50242e142c0c1d0900e155800d40c04032039001c10b00c4050600060202080c1c110108941c1da6405860400000c160112840058902540000e8021900248200612104801e1001500c0c800d98071445d903034a44604210040404414042e100321040d0304040e446406140142882c19041c1400381c10b08542900960071500180c5917050a034005e0500b14109203071103d00140c1c0013404281c214101f6290004a0b8141300c0c030000d009000e0780c0d1303600040c80c501d170072600e0403001815140001e00200c04540b4280d050b148980c41051540d2080403c5440301c0840390003503e105003420300c0c0c64a1080d2621017000040c1002500c143d076828010000440030520a0040140c0d00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 25885680 1250 25884430 25884457
    0xb030a0809030f01020906071106040308040321050a080a020307030e06040b0a050108070b120408070204091109010501021b0f1807020f0601120302060403140c0d030b030105060604080a0f06020f 85
    0x1e104403014141031046040b0781c581280d10411150f4029034800e815aa902c2e60440a4140481d480c00c011403280c0c0702d035400c0502250b8000c01c000082011a0f00c1000d886105461103810316409003030155054050300d4040710200300700348000345200040754082d5611070454038000ca0030a0311040c651f401c2010076034068904a100d034040140c1b004040c0039190040541c1e00050942c0c9140001e01d90340b501900c4080c1d140011b604001c0b07001d01c8410003e55195540047c02002009251700d0400010044031460500231010980001800e6001082d0015030305248612898454480c0702000820115100c54540c040301b40c80004208103110312445101d080c0c41d800501103008403c040502e860300581c8440c0605059034401000290b003c1021030b0000c1e0b160400580c2d22526036410740c2180101030714070650340708141c44507042c1136041d001318001581c154000c02c03090f2151300500140f1f10031401205442c2e4840c2025a0028103000c242d084154011800141080141201d811059029014001a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 25886930 1250 25885680 25885687
    0x40f02040b030901140f011e090507030b030c0a0501090e060301060b0f0307030605060703050409020d0608010c0f080109050103050624040203070309020f0108041e030c0209040303020307091703041401030b030a08 93
    0x80c02002d100c0c0405405c450501c0782c4080c64401012128a201401420114801140006044d1081000790b502804494000384075a00d07040c40018001c00c813032495a8428458201c0d00c1095080411004080d94010303910280322904100c92030000c640c0240205400d50745e2004001805c100b030002800038100c0b4581c1c800d03a07034240548010f0640300c03281c220501c44c480811030740700001c0c0c10034121011186a40d5004da19034641005000081c415580441629401d114441c802954080c406a4100920340c8400d10103913201c03e5444110381003400001c00790307403004c40032031110007001140310f0420321004050b418004032013020070241d030819900e18000c6511440f00608600d0712006c142c0382a40c080c0390a944900e080c0e184d4401c03420f5800c080020205440d4900414107102d0740e001c035800c0780c0280bc4141181042e15000b0000d600c22200100007841d0980c000c40d41080d4211100002c0d68000011070401d8104510390441000f450b0030a414035643e400244060348060007003070403913402040103a49 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 25888180 1250 25886930 25886941
    0x50f030f0903060106020102030f0609040f0c0b04090c030b1305090a15050106080601050c1b030705040504080306040501050d05030a030c111b0108070c0c120521070302160b03070e040f02040b03 85
    0xf0f466810b80101d0103590043c01040035000740b0b03e101a5207ea001c8404415a899034180300342c400c0c1084030007900100c0f2a90001c50101c0c48a4000e00031240300520410031654505000c800f00c503050035a103540039064085011240e0101d8000340e0300300e8040c40942ea42140c181d40d68951540c00c1c0d01401c51504c0d1200010411582c02503003407a805882824400c0c034180201c0305107078a6a40380303404540701580101e082c4c000e585081040d000504800b40080000e42401d00b0b2241040d0030441c3c80c580710b40d04000c0040b0f001c0c2401c0d07441d1520341394494000c5041101d606015009401107410031800c005501e84040c4c0d0b40002000002103640c41c038001a0402074800c000100f4a00e8020000005d00036208085000901c64034100780803203142030880187c2c4460351500311700700360031100c0040c05d45860131600121300140b80020404984240c08072881007583e0185808501c1051041c4595240d003032001035940c0e07005145454100c42c00030310008950315494442022a08581c2050b02c003018040208030707 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 25889430 1250 25888180 25888183
    0xa24050112090218040618050c090105010e011713020d06020306040c050301051503040503070203010501060206180105010b090103020309010905010203090c010e0a050904140a051207120f08010909050f030f0903 92
    0x72a05800c00c8400d0004030305036008102890b512a111012020301c80000806002150384003015611100c00308881c070310050f0801550b01e400c944042d5106425101c000151507010b2200e049002d030040c2c44101e40803500818401140000804685202022660700d0780140d6901c2001c0725000d114000c0140c80c0d040c14400d0000b00c50a59400034188101080140304a54030782a00303c0140c0f12048500d90b0fa5a103501c0e0540c2140242c020094040d0300341400031a41580118020303205246da0600c03040c841001258150036100c013131180041d00c407402c200921265202ea0011940040c481c00041290100ca60360203003264000c60b010000e6820940312000e0b150781c80030001440d054201d5400140c40e080000080c0144000307000280340e20f1002001d07541c401001c0c4520b06440c0d4204c400d55901d074005217040a10366020b04402c4032440c2c0d0150b030030f45030a03000f4941403082ca00140d5840085a08000e1007400030091a0420380721403040703c070401c001810810040102800354080c140e1102e01d04001d05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 25890680 1250 25889430 25889447
    0x7060c02131407030e0c0d0c050607030207030602040b0c0f03180418020a0f18090506010504020310030606090207060b0319031b06060f031e030503070507020a080a050c2403010e0a240501 82
    0x680700b404003047c1800400c00b40c0c44103006403542101c03000d684840ca07140582c46d000d050b900c000c00365400410300240c03c440c410090700b02160040156520320850700b40940e224483d501c40180300e00d2002d4030103883e50815038000107180940010010607100f0b150001000703031019902c941025400da60f42400248114040540c4009e2240c5080c05184540c4c2c1c0c4054865205029550081e0748c0480000c2c2c0a62410717050100568101200700044c0340c403940c0e0030000e507201c41400d0707418909044240619040004a0340d2000c04c11620380b0760308840702c0d6021120b0207800b80d50948d98030034020040c00402c4c141e210314401040180c094408643c90b41c23030042c850034803003402c0045a09111034142c02090b00041101d0380050759141181e5503804501c00142c041700d05e42c10252542c490040c40004200001520000a94045030741140c8520407821240c422014803420111940040c4010090320100003000d40e00440d0309400810180b0301c0d11030705082c4084a1580300070318481b854003040310b0358000315131 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 25891930 1250 25890680 25890703
    0x200a08030d0e0d1b110420070c0b0304120e01050f0c010902031c0f050306220f0b040203070207090f0609090b010306110a050702010c0501060509010f031407060c02131407030e 77
    0x907818804c5007040e051480304911801404158003529801e40700c0e500c40c1d2002a010414100a039585c00700051618040e401000c002c9440d40c0d040c01c0e000c260303601d49800f0360b40700b154000038141000040f94004c496044075160740741c1c18007a0522001d8012605074001d070005407102c400010b00500305004040c50010514020181100210101200d4581c0040c0b00d0000b0400b60034803a50f039032121400308000080c48555124074071110142d2103031017141d84d0041d280c44100d50f2400c2c44440501c4c8100000ca100668802c0056030002500304401ea0640e0040c42d2142e40c1d000000400036a00c900d48010b441c41d4440448400d418100140100a0503115222688800c001c0d02d5042030000e40010307115100710080039060007858000d4004100b4250098405418082d2814541b560b40382c3d0130040c480341e1400115032070755524000071100c0400243c10b4003122119540c04103900d004da000d0041c075400f01c1041c141401d849070729803880503080c10320490040440e954001461504440d1041c141082e1160 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 25893180 1250 25891930 25891937
    0x200706051608010e0403020c0d0605090609010c0503011401030605060f030402090c04050a0e0c0c0706051804020306060306120a080c06040b07020a0b04060e0102090a03050106051804200a08030d0e0d 87
    0x1080301c5160b00805960642d0703401201010b00d1744940c04e0603480c150282c82c0d80340e40600c182000504110180d0030050003040c0c0d003070498002c0d444d8844064243c944242caa080064818001000059140c50140400b50410f0600080c019160800300d1400e070301c48400c1c802d00c0714000050204505041c001c0d07079406403501a080d401c0070300b07000002c0e080c01050703c1171349019801603000c01d801d50010022200046a05400c4511441d41c1d12405060f13900040c080c91000c03000c0c031032080c01070708060003100d05c00e44000700000d02e995211400c1007404440081c07070303010500c60100c0e16000641800000d219104030300740100070500c4c01d450400c0d040200182107200b1500000746139000034240030f400d82d41140d4004800b003a26003004419038024020000e2a55100f46084c0000081c403106600080c1030350b41c16100803400c14803210365401c280300d06840060040494003003588007201420060340c8120b2004001a540f04d50300c208036491900184010516250b50709400d01c0144d1003040804103c000303504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 25894430 1250 25893180 25893211
    0x504080f061006180504051b0a0305090705040603110d0501020436020408030304060b011e08040b0903030c0a030b040f0c0809010e0c03030f0306120a03050403030908060606090d050120070605 84
    0x2e6080e0780c444d00c5071103014019900c0340c000c0f800104008207615201c4010681894030b0740000303440140074280544030b0702c0b0140a51030011030b03681418050182030b607800951032260f082d458024080103441d0803005492655080c480454000c40f0800d4004040d90207540c50789622464000e100c80042c0400002019184100010055450f02000b503c1d44581c0203080022001001c400582c1c0c10481b5241030360b400080c5940203d00d0745e07080385030741d0701850007104140501c1d92200f105035601d110a45003104000030500211106512a40082d0141c0d4005040401c0b0f401c800c2c4440741c1076900610850012442d1041000700c091000d200e54070b001501000285911415400882d460b4450a0009142c83d800040020042c6d182c04400312001040c2c0340c1203030100316503810000e00c20f1708940000c0340010020000020010000912540508001080d85180c5440181080781456111a0445140d501e0346a25000c00c20921020b90440c09054441c554035540ca00d010802c0f28802006c00f031603100c0e0807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 25895680 1250 25894430 25894457
    0x206040308180301150303120e03030c0c010f02070c0e1008010507091509050a060c0503190f0206090f070e150a230103020f070209070912210f0c0803070504080f061006 74
    0x145d84040840b501424070441e507515803640100680201004664240320010a01070b216540307000500780048800c0080103480c0302c2061b04002c1c0d12030808060545200351030180303c6c1220050501c0d0300000008428104140e903821450700350380f0200c8030700e404034141000400911a11043d1540720314481e00c0c11030003e6080c0000618050340d240074035004c014400c030790075003000020403c071412140e80000c4114405131052005180307140c0030540c580140030b80b0780418017003100080c14540048103480540b15490074440a402d114000400c041500355480c0300c0705086032150840403000c0c00000300320b5208108004105840103803201000c49c1054810080c58258807803003002e442206a045440c200e0320345941d1011520f10b280b0b9000b41c20000c8003414090104190f01d03490382612034224090302c00e10440c1c04001c0e100d88a642c207000021031180b0581c10001060380c8011940400316050203414644c544030300c01d00c0c000703810040c0303c00d0f46c0c0000b05108001c0754100e8040c006149901c1c2000c180c4141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 25896930 1250 25895680 25895711
    0x901060807080f0901020403050a08041d040305030103020d0809090702070501020d0207050109031412030c190305070203071203180b09190c0603150314030a09050306220f0206040308180301 83
    0x10418a51507011402113000540213404680055401c402212a108480c2c2040030065120703120b0505528600d00c035110314262482c0b0f5003885181c154032071909503032842d000d101c01070540c0002100c0a550400c0f1611040e910b4a0403075003d90032660081a21506000001e0b2512030010801c03804e5603c40b01041005a902031408810f490b84a8080307107411003c00d03800762a180414141d43d5211801004000c05d002d000380242003c007440c0368084008028441d8241e007142d60039100c2100680007080791034041466090a09001100c07407500091075440400d2808012507403210403161001c542e07083c0400c0c2a02005500242e1018444a00071134803950703205803070441140b203a84281500c80f1007030300d1149800114080155000405494034615000c280c0751242e008260003070100b80d200c0e101003454100010b40030312031071034069100c6982c0402e045804035200c2e02e5034115426100e500c03088005840c0c840c00f4000444c032a9a5040d1a4505850381d54084000510003074080c0c1e141c200d200107036100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 25898180 1250 25896930 25896947
    0x70806040605150c01060b1207020c01090e13170a0e010908010b01091e08030f0405040c180b07141005040210050f0403060e010b04110901030b04060503030a0e01020a050118020901060807 82
    0x2035402e18250f54214000c4098003500060b4400c840032603010232041040e409008406226504039400e4a00c5448807000558407803015014180224a2042c0003805510100f07903140a0140162201030003581c5000c049040c40c3d000c4007200e4001034038000b95182c1540c208807518003500103440203000c00007110300004d101205912036901c64020469280d00a01c00c0032401c3d8004d404d41c1030540340e41d0401c612860619a10074815640201e29200c11050700760b02c10102c410b042100294101c086614104210459402c044002e80d01002032401c04101a803042160700c408035040b860104c0d003468035004000040081803140014007204000300b0011f01c0c00c2c5000c840030349601c000001400c03060b900f01503004001c0c100d5034581042c507040c030103450781007004090400c20000340da0510141d911001404251941ca200d00303601a4024020059410302030007010b245202d042c81110034207941c60302d030b181c02c0d201d680400c42c040200118018042d81000d148c250701400a50030481418200701400074a68035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 25899286 1106 25898180 25898209
    0x100513170a031106060a0611030405060d06081c050702010c0c0506130f0f120602031506030c0702030c10080403030c1e090e01050102010c08040b1b040b03070806040605 74
    0x300000781d880c03198038060000c0a0451407c90150f8100080d16100002408240000700302615420003802159170300001c041030080c034040b002c6040c45141d0b4441c924a980d020b5880c00c0c0c564003c0101c2d000c0b03d9080ca040004002d060404200c2010642c0016921a90000c2c820f50759000000c4000259200d81b03070540882561400306030412000340c41110050035040c281a400708042da80556030000b00d101c020502c10703444100040b566441110308004847c2c001c01c0b0700c819803e04010150280005480c0c10074101900756000d00040c4000b4001010151154200040180300d01a00a1510918026400c032070140d0500501101c0c0c403401103500c000361280001403550b1050107102c03602515900c030940251940d440702000910010300791034048022034180c2e0510f0010308020b0005001c407040161307c90900d818001c01c0c80b030010b01120b1007141401e000f8052543e80703460240401 = true := by decide +kernel

theorem cover : BRFrame.Cov 25719430 25899286 := by
  have h0 := BRFrame.cov_init 25719430
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25719430 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 25719430 ≤ n) (h2 : n < 25899286) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
