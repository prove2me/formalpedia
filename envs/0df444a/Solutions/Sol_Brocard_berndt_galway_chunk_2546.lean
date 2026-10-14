-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2546
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:00.15587+00:00
-- url     : https://prove2.me/submissions/676f0e21-75a9-4810-97de-83a6715b7e51

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 457733812 ≤ n < 457913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 457735062 1250 457733812 457733849
    0x7060906050904020d1a010906020d02030f0c0f15041e120f05090a031407090b0904110a051f03050f06010203070b060409020307080a060b1e1c021c02010207 69
    0x102450a180300e400c090000200d00080d00740c0e42c40d0180d0305000da044108210040000005000400710903488034081003030030b8408a41c061001c43c88103280780c3c42e03800452804850041140041d404078100c00340c40e02816041090705a000c0c014407440014400b91103c090a041c00c3c440c1c80080c070030300d11035500104403020900190500901c2c0c814007405082c04144811244401d880c2845500c000c0b950100340c0c9500881084201030060302c0034004d060840d10300b1519040c0c608101e840414034280e10801c04070000300040e600001c04000b560f805481490300582e40c0001c2139040207958580100c60214544840d000c6506101d800d50207699400d02d0fa0305402d045002035200d02c51070740050240212503001585640b6160001c2491039401380440f5400c40d900c140060301c0e52245582180c43c0760030016041c0305441c019030703809021101c80b0612006484071074100840d42000440d20394400c0d0b20100b902015a0750250f204050610b6441c1642d8030b2000d80c4002405d0031060303000490084040d81680 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 457736312 1250 457735062 457735067
    0x50a02120609190513061b09051002010e010c080610020c1f0309081204300e0f040609020306030c03150a1104120c050f0105090306040213020412050102030115020706 73
    0x1540c001e88252001e0202e6154000c0f40300d1203c5450030305280007070602060160300244c08051403540f501688081006e8048149144500440900f80c400012a649000d0000780740140007001104c100e400006040b00f6140c0d500e0303081da0000406040410b40d850200001411f00490b0b015880d20248003401d00c100040e400170b042514280d5550888592883c80f1340391440c081e0340300c0002c0f00d8000b00c1c0d0540300e8200306174102202c2170403603080b01c1b43c20300c8a40d948000c041440c8140540b4240c541c4903c50281c52090840d0782c002c0c1e1424056000e01268819900e40d1114803c04003d000a0b21015030b40c1d260100c181403400540402d0b0034080d80c0011010550030032500103040d013000942c0c9000c5980704032007085508074012070300700c417103015054000351040205002940080b11029250400c41e2001ca01c01034405005240c10f86400d5080500040c3c018501081600f03c54520040b0040c01c00b0740755182d515540d20114030894241c0c0d030000c014020150001c01a03080e9403205d00c010030129080c520300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 457737562 1250 457736312 457736347
    0x30c080402130e0705040e0a0201030608060103050d080a140406060905010f0302152109060f060105030c03180319080a110310062607021b06041d1005030f0d03050a02 73
    0x301c2c4540e070303240429450860706000d0720700206001002404a0340100c10b20948540c0000d00c100e0202c1d00d02040080d8079840894100c0c100c0b50490f000d0041010103032010398915500404015009a9079840d51a82d400300303600c0039010b140039401c0010a6814a00e60604448068015002d40b0212000c10001682c4000664a00d4403940c103040342c40f8000181c81440288030124144ad903aa456000c1209403080001d41c180309040030401c5c41120f40b600d0005480c40e100030388021701030300d604100040c0703803030103051850103a04480300c03c4030b2070445080d16180420017180000c2d40000c6204c010301010f11018010202c0704107038182d180b407850800e00c004000c9041ca500c2030300d0034441c203107502e560313052128200000700544c100400742c2c445c503200c100251a5941a5902c00040030b0103c2800701904001003603905650b05804595520000306104600d48400104418106007400c003010031070f40c40500c10b081000c4c0c2160020451161001c0000e0160380b00104115000c51052280000c50040002c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 457738812 1250 457737562 457737589
    0x22d160503100b0a03060c0507060c030204031502280f08090d0215150a0314150405190f02040c0810090c0516110904140c03010509151009050702070501030c080402 72
    0x800043e0402e0b00000b041420390258030203084240f4102a0121041c0c00a0003001024072a6004021070581c040c400e50032030055002c06046038003100c031307203000c02d440e56030080405211860f00c4800c20060101c070000181c402c10403202c00a1440c40b81840b110750040001074000b20410050040c45015003802540e03040105070701d461400920010070303101c29803208480c0c420140601003020f0151241000c400802c891204620203128441006105001e03103c1e640e070199074000302a00c80c413440300c0c403103044c8064440c409840181c0005071a100580e2148507005242c0b80e01d4650b1107591905d04100e846080b12584242042400d103e042e40c951a8000100d0750021214400141010380342c0c1845841107914480c10750300300980e0014002171060a040c0100c01c400c00754100c0d94480100404d00d400d8840a80b80c0d80415404255004c144c07a400611081d030000606801d6001c243d603e414080c00c1e50025151640907030031100d01403105503418010703050742e001c0c1400e0040040c00d050f400f00b4407030448040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 457740062 1250 457738812 457738843
    0x40b180a020f0c101a03010b0906090903160b1f1203230706051b1206101e0905010e0405160305060f0a0603140a051003030f022d160503 60
    0x103004080a0110090f240c3c2e04030304204480720311484107190b00082c9100c409003050380320000c0c4140b4103860705018030f41c3d410390b000d070514260b9283c62080c09400f00c8041c182d9515030100f44410b0115001441c0380d0b480b00d41c0100b4070300c90300c4d00341115039640c40380d040801400248001c480c2403043c030424040132465a0380c1481d04180000c600004403061800700080c0d18080c036400200c1600344286508900d0290103040c40c10031003900c031500e015101d40b04482d158002602c01d24005800e5142022810741401c00c603041660100001181ea420001c0320318013000045445c81d10140714030350744511814143c19003950108410b08141405c68204681e24280504150b201c000045480c2c8400e103015040100107042d020303006484180c040e000d840c1202a219914800400041c00c50005001e0980030b40340d4807031900c0e182411910202c4618444448a50540c4102c90301034150410f0a1803840440f0840500381190982d048a2542000042e030500f202c0384101d0300e0180465640454140301074880203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 457741312 1250 457740062 457740067
    0x90e19020a27110c070905090a020a0305060405190807060c020703051204240c0314041e090b0103050f01051246050303040b060d060507020c040b180a02 67
    0x6100182001c61682c1001c800000d0281c42c1c00d030b441070a0401c0d41c125144804090007003403880700310800240a1a6406042c0da405860100f0003141d80394081500078100205039913100b940c640118081e0985648101c4455000c04100014044240103000000005c0e49005c6400842500c1c0e120603402040400340445641c0d0320070070200ca00070064030004543c4a0143c414203094084c07240100d4000d403107804040c040740d25500b400500510301d2100c4100c100d4940800e9000640c8007220840ea50081601d1017960402000c91140303024200c034003d0000c200111450f00e8240071450f01070b60040c050ac14185400e1000f80507000c5022501607041d01c1040c0c4505003100c00101e030f10b603e03000c8840013054503445011045102c000800583e018466079000b8400d01c140400354000348104c015400c050001e41091012030700096040031000d03085000104054070b000d40320346840c1d04030f4000340e901c000035a11900308401c6a041c03a014801c003595048400c8502045540c8034074803110780c010603007801c07590f00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 457742562 1250 457741312 457741363
    0x1103041d061305072a02090103060203060d0c0b07021c05070510030f06030c150815040528050105091305030906030402060705070605040501021e0a030e031c03020310090e 75
    0x88955580c000381c01c0c03900c10700c5030341490304005d80080c0480c81804c0091903004070180c00d40b0520240000001d9018082a0316a07195031100c0e40290005403040790b118101c14007841c00300c1c807882d070494050007810002c03c1c0c0d113244520400041a10140f00406100303082940c60002c11400314401e011500c042d640303040040d1414034124010510354030800c03e403a14140c0040107001c0c1c00e401d03040985003040010125000c06030029581120101c81c10b5070702141c078092130102403d0540101c1d130817050402d0050b6070780608000342401078070700308070f0a0885581c41c0b00410003880e00f0300340c180e000b01d51034960428080161b00d40642781e1140383d000c0780c0a0f260000124046440b01c104483c000354000c0d0990b201b03903403034000040103a0300620070346006114a00c2025600e0f21510b00d039047c0c03081030000801c804a030940d070070f540040f450101c280d4136001e1a070308440440307040c080400700c40d800c07550300503030f43c0c901071070340c8100c02c411a04010281c624040ca140300c00f1000042e000301c07007045540c1180c115801c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 457743812 1250 457742562 457742569
    0x50d02070f050a03051e19080c0c01021218150c0c01091401020706031d010204030f050c0405063706020109050f0a0b010302090a0209030703060506041a010e130b0301090f031103041d06 81
    0xe494403426020208071f0340c900203003c1074001502c9030781329807001d591084070303501c004981e11706003d98420b540342e05c03c12030120000f40c868008589804c02901c200410141c0300501d87c070541100421452070380280c01409032969000d580300c40130f06400b49000c4c0b4a41100c4000030340e100d05601803034051555507030b014106140104120380d03000801c1d000035035843d0344034500154205072941088510f80f181c0b00c1082420304c4e003401041e00c240c00181c44001c0c1041d40c1061150303000200d0218004a1045401c25407081c101a0340c10009883c00f0380011414407c0d502e00289081044030084442d6001a02410b0000700309030b103003904490f01247c60380055150030041c140280300e15202d003035261103081c60000801000741c00035441600300311410069030080c4508068000c40c00048680040c0701303202010400c4ca804916141050145000000d0100c941c9011034211050854140e80130980c9515010400d83d018140915204c08000034604052900d8030041d42c034081d602904180211481c00a086030f01d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 457745062 1250 457743812 457743823
    0x7060e01110d030902011805060306040218040e0601080705030a0809040203090f070e1e1b03220503040e100806010b0a1e110105070203070209060f010c050d02070f050a03051e 77
    0x860002610103900d842d65015004103035600040380410103260340c1000c00c1d0303801d94420003280c1c03000e083d05241d641c1d80000c12000354009200c00201401111240c0807640311440b419182c0b1680c070008104a505040705103140090680c80240f280e4032100841000804013002d9941a42d016075025880b0b4a402490b80d0800700c0810110400307104008001035070185010040d03000d8411701c44040091849134900860841080f0f8619480e10600440c00c004c00042200843d03000e094683c040c1a40305c80c034400300e005035000c1a800e6810b6880460240301e40c2144201a03034010300a2190403005a15190b00c40b600c8010501c11261624000701c1c40b080303000d020b4030b1b510a00300c804144900359080f81040c09800026182d454640075881d08001425460000040311543c6800500780c1e031881e40e4a40402a102e03034900c3d290740c100503074800c0c05c90020780d04106004143c0c2258029115003410540542d01100381a407001d4840c12581d10708102061000c18881244800000c07048078070041f64050900e0300c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 457746312 1250 457745062 457745087
    0x1409152d090307080711040b040e150c090d050c130e060f04170c0102130b0f0d2408280201050910020106051003060509010f060801050915030102070b01151107060e01 73
    0x40c1000134020108011b02000000441c07080ba401c00803800c5103000c0c482101e000350242c0e500e82e40f10341090911f000080d681140e11056085003d49071140000c041442c001e98168212000d921141c60103004d0b1a00c05a050006403100300c0c10000b4007040c9030119a10b0102030040c0c115030542c00c012400344086949081c0c03207040600c01a0340d9901c0c00310030082c000c0d40441100080b10080410110300c010260085804401100003801d0505001980460041601c41040c00e2100c400c01300c0009081d16009203480108000be020f80705110741d6803405c8407040d240b04108007898596014500041c2c0e000400d84800c0c0d20240d481802d101c10f580720990040c800d6030805076014015440d01c501302a410703042030040c0c98040c0c8100146036a21018803d00c1007040c0603210100d28804014440340c185100807541c0642003480c100c2510042c4c01c0441d00b2a400102c00382e0781620524014802080791a0104180d0a801d1400c01062442c85800c82e840300300340c0c040c0c0010030000c1d0040ca41681c0c89249d450588 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 457747562 1250 457746312 457746323
    0x50402030706082d011d190b0319080405090f0c030a0203060103150f061403100311130203011202120f0c01050a35010e011d0a1409152d090307 63
    0x715440d500041c0d0031301c0400d2050022004c80724075944541c0f1b84041c4144d00400c0b0300141c0c0f8814040c1482000003401c008284950103110305141c101c469481c4192084c801c0c0c0c010856259204d0401080c4202c26000a00703081c4080b413400248140c40840c241140c0d8021964400161251102e10049010348050545110400c070a84804203442001224001c222811a100c001d08103102281c00d81040c00100c65404108484800c10004102410340d10100440c0c02003040c0c01c080b01c00b02408040781c00a8004e4816041c3d04646a4114102910180b02412040c00241a40d5010f0400c2590b40d550224046c2e0402002082c408080741c0510040042044814248404c5c1c00d60003942e685800580e8080804c030704048400041d5080030200c489041e5510050301840c2201c207402c18154035800989401c01c8640d071800c0c610324840e00d022000b030241000f04041d01900601c40903c52545101a00310406018040b81303030250b018005680041502055140f042e16580312100d490560080346c002524 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 457748812 1250 457747562 457747621
    0x20406080d030507023003040302070314010e0d030203011226070f0c1502070b03040c0f06050c072114010605040905030307080c04050d080d1515090905040203070608 73
    0x10280c00da00000d109040d80c1e400c95505001071004030f500102e60013079500c6c2d00000c0b2511801036010780c030003c6501c14041d0046880640c4c0d40d81d5844842d508016080c41769940d100d0700c1e0700f000ca0060000c3c2c4401905880c0560840d41040d09c12400464a0301000344407d0700400b4a401712046400e00c0600140e501c210705860350700a05119401c0c50280b141201c1034025000b0200e4a00007448841041401d80d17401422004c1c140121140203500c041c00a43e982e80220500040350f82005464001a10460b9161600e0b0801c64140628000c0c19030407148840c0b000c001141b07440840e00b8003441581c0d4000312405485101301180b640100826006903400a040003c1801403140000c0254000c80340c980d03d203a101c0d540c41c0f03c501c0c818040c0f40110703503001d508280704501007414600a440c0b040d000744d100044901a0720f2140950030300c2c661250320901d003c031608003001a0002501030040c0354142c0e09202914095002075203034800d9010b480d0501c60110f01269081448407140c04500b4003110142c203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 457750062 1250 457748812 457748833
    0x1e2a010f0c02060a050d0501090912110705031e010c021c3618090206030726040302010f11070c031b0e0a06030c050d11120c18150a06020d0c02040608 66
    0x902503400108119002407d0100000b8110010720907a0170068005600c503200d4421084200e44212030701030310012a105101c00440c407580d040c000095080c9201d44800900c2c0306ca00507203401e41729015200b80c19500a2514010340701c80b0300110490f4a5101d2901c0e180905800041e40f001298003500a88140b403a00002d083d0000340d00c2c088401c1c0c40d0000450301100d000340c2001d03029200000030003074010800384040340c01c0602070344410301d010303040402c00144808000004056a0300c02c58082d0300513910b03441840c000c05154464580c0c260f021071071503858900b8584450442c00d000344002885600c60708500b04032110113040c5003014091803051a081030500113404006450726010941d48050750724400038052070012510002e5543c080c0e00d90f036801d00040100060800c0c500c80006c00c034058000085e0141d902d103803104190001c200c100300c0240c02c100c4003212105501101c11742c00740f40d42d4041408410307000281ca008807520340c42c0c020050540c0d4070104018251940c0300e2511031181d50a034a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 457751312 1250 457750062 457750067
    0x20f0a180203100b0c030405130902131401120b040212150907081204060815030106150c0b06061204120201020d0f090b060105191101020c1e2a010f0c02060a 69
    0x3180602000760351448a180c4480002e001362142c0100a031082c3d01c108800c0055050204410408125905000403034080316000b255064080e441d0030b1f8500c580d1405260480d04402c440b580c003403e140705255aa00c149642d1b02d50300f60034094406031140552030302d4890456003c03c0b50b071a01d442d03603540d0ba09160078404201643ca41842c002c0c051140140c4d80030001141441042d1401c482c60b40e030b10840c107501c610b84131485040e0711100440d019521402c01086116007111281510f0340b03507555000114456040403c1c041070060204c61042c50700700807c80102c0d8405410941058020b020a800720300c1c642e0f41a4024412440380700449800c0c020402400000381e400b141a0500805922800e550b48070011940c6128908180851801c150301e10b0442e607101e00e040039a07040304540010b10f4044003000c0766150060841e22040c003030300b80c010070000e402c10620142040000074011110301c0d40c4c418020b07072480484049002c0c10002c440701100500b610411100c2c0c4080e801421032030750b551002a00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 457752562 1250 457751312 457751317
    0x90b0406060b0f030604020d0e16090f0e0307080a1115070e040b060409110f0c0102130801021908130204110310060915032f030a0506030a050a020f0a1802 68
    0xc0d10315900d0104009078203281d0b40e08031200c60f501c24010503d0b566840007080004e42101c00784041803940c6040e071300c100700c0042242605401010320f0945c030040c908140d1400b910131801384010520b04000b184402150008151031280741c0c007000c0281c071500700b0102212006014841020148141d200004604251491a074041c01b40c1360b6807032a0607041d160510055860700c00342160084001c000412141015500512200c4003000d5a5071405420790500d001c1500142d00b0140b5a940c002080300e07090211110300c3c001001c22000950415820790001041d0980c288105003e1111502c001094008140c14400700310364010b0042007040552040c00c2d5042c4c10440e140d0028148410011515500030190001124108926108440080340c000c40c0900401d1071210707003407207502d802c9030311643c512001c440b400442c1510302c0340c9a2403ea007800c002d41e580030344014041c1c0c201182078000b0500100d455485a41c05030798501200075100040340403008030360300041070700040e0190560286043d800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 457753812 1250 457752562 457752571
    0x1609020702011b02090f0703020903070b09042702130f1404020301241401020c0312032721090a0602070503390a212604060302090a0504090b 62
    0x80710003141500760703004120b448a0f040069402010380300080c2044002c00c4c2c0c1c09510510324540507041c11440408a0316265080c0c019080c0800301284c0200c0320304062040001d0000b880481c02c0440082040030502c44c045d000740680281c0380380d035408260891035004902c608050707240401c000c1c070700035150321040310060341c00b00d1280d424401c0d00f000850154449540c0c00038281c82484405240988040d008600e50202c50b05502a00034184183c0d5410b1200021405107480080d5807494410b044800041c3c003178010700d02e0b0301080030000c4400100000d800e403001c400e500c0d04402685000381035441e580554400030f640700c204a0400329005034042084011184207400700c4102019030300355079a0315280d010051004805c020460007105000b591140e90403403010b030281514036290b690b8814800180701c080380110b91032074403110400c01c01510036900c0944410f20003035011004584c10340c46214a1203180c041603004203038400c0316550501080c0091030300500c1044502800c0c607082012301070468 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 457755062 1250 457753812 457753817
    0xe101206030b0a05061f051b010905030c031c090c090c20010902090a36050304030303020912070605030c1e0301060309121107050d1b091a0105040b0a050705160902070201 75
    0x24507010600c204c0440e0303981c0441162225030901c1c8c08d03144a101095162800c0003043e42d00c60301c400001c564240300508840c1282c6025540d265203070704090700c2205180310301014962402200d08041900c2641001c140c0f4400714022030314010700c1d80101c5d51944851540008001c1c4200c040d115004c0540c4443c13940c500c01e0700c8035400b0b603680004110880f11402c041441002d40000741541070000703094901a401000a10b00200d010180c99961640c1c10a42049001c0790f40060070207a14034100040b2560000760314000c040d19801e040c002005800080c2210002400214401c80301046549115214a40ca0000070b82c83e580d552400030098040c0d0070342500c08200f01045410100d00c9204100c44081c116401054501e203098113126404825400c05c0c0c8041c41c04240d01c7c440b0004201100000741411040481d0304070164800c1036550300c03016442810b00000304010080840742d1801c0e00c1100703000d8113115440d50320302d00b011401c0070b40703915008080ba002640c0226040300ca03a805411f8050003079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 457756312 1250 457755062 457755079
    0xd02010b0f011803020904080c0114060a0e06011d04180c0f0b04080705060904180b0411010504290c0712150506011e020705040c0207150e101206030b0a0506 69
    0x72005603803910400c2a1800d00c208000d000f440903003842d215094006101301d60151601c8403c01185003195400c00400c3c00380c0c1852030a0251a00d800c000c400003400c00004c010849041070400a4140320f00040341c00307425402c2c406042c60f103580303e038041d0540350a84c4501c030003440200c3c40c206000500500601220300038030400440c004030040d041d503080c0c42c4400d000f001020708050801106400c100b05540d801625030030f200c1c01c18190304840c124660310403034404110782024500b1a5002a28410075410081d06100c00c00c20020000302c20b06551100d00d0b071590024102900040091242c400006a10300ca18040094107284840c459480c250140082060304035021a071603041e00c1e0b00b518818000340703180954010781c0c038920708803110150b0746004460301c0c59a43d00105058510400031240540c1200e8000c02801c80e910001c5121110701c0e00e081388c000c441c603074002a00550801484070800810582d501d400c03c8e0349501c2a000345401511002c55407800c40c0d441070190800315007150141030714 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 457757562 1250 457756312 457756339
    0xe150109180f0b0901180501020309060106050a021902030a020303070507080615010512131b1a030f1810110403140c0915040b0603010308220b070605090f0d02010b 72
    0x812100000156105060801201c160f848480c1c0c80b02d005007028800703560780d07201521010003003508140502d1280001503147d1400074103003401d003841680203030705103c02042381001540d4041000c9501300001d1506900400d07003070001ca0300e00301c45031b58025010321001400d2024054001199411a0301150842d28141d50b050350f120035a4005040c2c85020035000c3c803410002c80500d00c01292310240304010701481c1605603c0300780810501c10446500401d81d000240410400140c1c21b00c3c00d40000107a491841c2064148080704c5d03103005003d00c400b0001000081c82c0c2002c03d010380e034062210390800703000210140040c01d85646c401e100440744030020f1041210f00031404100c1d203240f440c0041c4071007010743d0f400c2484070b045112410348590041d034820009030155a084041c5010f54059483c00341c0300c6003102d00d00c100c22000307240009005c9444d04410081e1001c604100d8215a43c40780011440e920703038044d2986403049980c8050064001d103012558150382c1540304bc2d6807071200300c4021402408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 457758812 1250 457757562 457757591
    0x509010b0906030a0c0c0f08030709091103011a07061b080f16030e0a06020d0c0e0306010b0904110702030a0f0b0a021606020f040b0d060e0703110a0809010e150109 72
    0x300e07030100b50002001d00000c1d000318015808004445010f0500041101ca60356401001c943c0071141210388010100600c400b46522000c4c0324090004160104100c0140303000a603124001440b440e5030040e1048012491020300c0d40c152443e29500110034401420031880450841e403c070f1018800244a110007d058006242e82890292440990b800c0401644040c00c80c064a0224041c8046129108130440010324a1005140c4c2d028800d50014269049407401400b00c0c400240300b5100341d02020040c44440400c004480c4105000c43d800103c580301c0e8407440d00c0300d0240703042c06585030082c03484003001d0014040b144200030b032060354840c41c2665900301c000300300c1c01500d1101e00c50003070414603900011742c554002c001c2403152801581c1000d40c0c03080c1c01805035011420351401c0381c0c0c40308007c00c10361140604454114265040500c8200b95800c542c46107805070221005c01c201e40710f4042a039525007036001c400030030707514070913900c0e001803459401c2d40019082c89100304c40e62030800c02040148 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 457760062 1250 457758812 457758817
    0xb181c0c08010b01050a050d050612121306020a02010801140d0b0705091003020c07030b10080303070906111b19091a0f0405070212070303060b0a0c060f0507121104030515010509010b 80
    0x4030647c6603e030400c442d558861000b040300603e659000941c0c00310300580410200101900d0641001000395038140c1685064003c940a80c481800c0d513114881110041c0c0e0400209819115600201420b240b4801d0001f805c0c404444406892445000d00f4490b500d94418024214150169444001c91409a47c210102d1151458402c0941c00000c004d000003001c891403680c01220440300000155104c071001c03821984250790401c089910305800300001500000d2021803c40284064035aa1102500942d03110f000c1c4150702e48240c2003032000310802113040032460007510680c0c00400079001c041c078040381d40d584c1441c1c516108078200c01c414030303492403e80201480385505030302405030300c0e403a802e00111980008900710141500d50b100440e010342c180700508041c64055950079000d105500b030510441d034001c0103402c01c0a00705010803454980140541040c868560400611030341d889a43e019140203d0b08010800c2c0140c070241c02c0020440200c0605840c0b080b50080c1030f69981d5100c0509a1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 457761312 1250 457760062 457760077
    0x11070b07060c230f16020307061e090602070e0601030f1407110a02100503070203070605040c06092411030403060204030f050708071a090a03050607270b181c0c08010b0105 75
    0x1440e0400c0f02d1001d5504c19409042d407080c9a211900d10b40c0080c2e400203044c4a00754200340c0004001244191002d8405803803d22541c0d82424900d800a0030004d0094940c0c0c2c15000da5000c0c5040c103004545036911980c000900754050950070407901480c101800c0d01000c041e01c40000082010a6002c031b4400c0118001200703a500a0101c0c2e07049040c55070075115038000a2202007035001c18030030907010541602405202c1c03072064442080203401c060001c1c0c5540402d0308000100e002d550360f0b208840c60307802020442e42140d400c0c0383c622072501c0d075602072452240c0d8100030b080b58000300e000401c10059145404400740710b00245c403a010f03103d4800b00c0d80c0c0c1e03185204800019198008000140186200a0030b2030b00307024044000c225141d4480381d01d44101650480001010452100c400f00c4040c00f0400710011020301c1510000c0c40d107103140b23031140114200c200000c50a20445582941c4854100d040801c0d035101d507084031507040c1043c103840b01c1d01e48503141c859400d10342040c0c46c2c3c1d0b20074822a03514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 457762562 1250 457761312 457761377
    0x1501090f0506250f05060603120301060c150609060b07110f060a12110307021501140a0315020910090305010b0a0506070602030907080115062d11070b07060c 69
    0x14200c8804000303140f80035a2000c107004074500d110f03010201e00345100c4c10f141940264011301081c00c2a0080c5440d000c1e880360008440d0000748014000c60740c0c450000781d40c0c42d411000d00c2490b0355481d60118001c0c18141e0006080380e142c0745c03000405594900207441101d004a41603009861914248070b1051403940700783c5d40c0a54104820050980142c005000707c11600e5030000b03141c680120300003ca50720640d40c0c4400340c6d010007056035801c035040aa480c00f520f0b0080d24014420240d001017200351040d070000030f0820b1103180004820b1445581520208107004001e25549000440081e08009050005451a508269001c1c120303040406510040307079809000580b50400c542c669200035000982070b004540102c41c00011460003d001d0010900e04055040c0344003450050302030000d0711061082e452400310796050003418045460144503144090030195860304241e50034a08009154001790752059020892609202583c1e0010f04a6041500c0e842508404216109074242c50480350010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 457763812 1250 457762562 457762567
    0x20c041b110706090b07050705062109010e100c020a06090c05090f0712020a12060b0c0106050d0506060603100b2b1824020301080d030605100215060f091501090f0506 73
    0x40d817160003000704901800f55060701d060a84510000300954031040f0b0182c40140040c900020b1121070529084d0002c20a800800901080401b49134a41809050f2082819a109401040301b402070162913129030740000304202800395481c0c10fa400c0202e07801494024010580010b10165003806003500412603601e8281000f030000031200041d61150035840f04104c62074040301e010080500030100503000101c6426282d4241680042c211a010b501682c440ca800260302000320f48081080360300f081c002d817445a0340795282c50300708200300c16030303404080c5080c40041d02e21650001c1801c3ca0841215103202450070820b50a4120142d030b1030030303800140072401d102501d0005048144940e440704070301c21121124000382d00352042260403d91100344144c00c44025010003507414030030003020300001ca0356480c0700c40510200a6986405204442480c105280401c3e0b0554440510780c200755001448000b82c0d1908600800241220410440c04230b0050100800e112081128040554070082c20150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 457765062 1250 457763812 457763819
    0x51011031014150a0c11040209010c0807061104030305030f10080c130f020c0307050c0105040e0c0702030c0607030210201206120a05060106080106180e0601020c041b11070609 77
    0x100c80d0b02125902a6010502400344003070416100060f04100352552203e014070076a41c20700007980b460914049100703134810081030307046a0300840ca00749501c0d0040d540c2c0c2d40303644191404000070705441801c05484100410700108043c1c0c007000840c8561015141050140c881e03009010b51010715010704403490704820517260443c1020211000e06114101000c41c1c000304203003640d0202c0e80f02c401141c4550700002107003018040c4c2008071030020a000e203442441c1c903140001c40c031041000940a16102030700007844c2401d56604110720b682c81d80c03004007074546d606608d1401950720409101181c0c0220b0a0000a0001010b0044164248925140501d1801d0006000c0030592940140219031040906201c081c03075440c200f241c051840d200704c0040055504114001d0022201640150100102d002543c51400002400e482c21201d5004500420381c40d104010b0f4101420813030100d030864601110303032201d0b100307108000004801c180c46017684002c1089034162a0078160080b100490005442003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 457766312 1250 457765062 457765079
    0x90a0207061409070501030e03040f06140712170601090501051b071a04030317091b040f0e030a09091a0f030a080703170106030e0a021302070602070510110310 70
    0xc003065807103001d000865002c9503001000c00340003510000360507444444180005d58042c03090807034107064000210705042c039101c3c0340400d259035030003114104000c12030254078851560042d80e07100d5512001c82c140c444031400c40101b030458680d0401d90800300d01408219154000c05010080d04c006940d020f140115100d400200100100c482800c0781c0324103040007a00340e6100c4003001034800303a1400c0c01d038bc1b00d1a604000700803012034a2820405280c690900540d0100020308074a00403507108110300e0300b420100020700a003440500c00d103081e0f0402c107004290b08800b01c010001010680c8460021b10780b102d4900c0d04441c40003080c00c12444a004040c2d00610304494940e030345200040494290050541d01c014003034010110841c0451a84035062280308124043c00e03025105a14080017211144c4048036a10218400d019010300035038001000450382c1d80e011100184c0d00a201555a5201d41c41c2140d40c440015420b6071241e440c0402035001c461101045a00613101d12607603001c1c85050080c00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 457767562 1250 457766312 457766317
    0x111c08030c04030b040609050c120303070c0614090c0109140a29070308040507120b0411042d110c030307050a05071a06030d020d0918090803090618010b090a02 70
    0x8400003440000300160100413207500c20f5100700c402041e24103062804600c0e249040c02001c1c0b07d0014070303420358103588000050b6544041145011140100f0504000c40102454900310703036a4a0281c040242415000408224004c003c2c1d9440d50955962412003000340c0e12040c0c0154002808441042240d11f0b03a05950716251500e216101d0b0401c2030038000d20f03d03030301106c0c0071800714680100300424004c00b804110014a4a01000e441d54600ca55842e004908010001824013200402c2c002e103985032a445148000d80181079010003010182401c1d04042020350240041820150401d41e10f100802c00d407904da2101500450450308c1d108816542c40d0040e05250041010030300010340400c604848109003543d1603942003c081c185001450b0510380000c44000c00e55001d020201101544264954201ea80c00c03074180406001406015001c0e1000040281264802100f17220101c003020404902a04101045110105000c607402c5e0070f0361020365034940d21100c0840002c0008034039800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 457768812 1250 457767562 457767571
    0x90703020f06090307121a070804030f020f0d0309051b01140a0e22180302100915020304110126060d0f060905060a0e0316020f0303040f0909111c0803 66
    0x14504040f101800319291803000d921100d00103900b0003040c0103104c0c07080141030704100400301c0e04a0901d41140e003d0300d12580500001c1c00c001c00e40d01d6461005109004034140e03440444262518401c42c030300020040c01d40c3c0c000c02d4032030b806a42e09290f50320028049003c55040181c40e943e000b071614200c000500c1d040030030548248120321410090382c2d030764154114160080e5141c6c200e01d00240046401c111011202214030340026075000201007a00001c224195188408010601d03184c0c501d401d001000207078500001490022040c0001c2240f80740104044010a0782c0b15542d441007142001035502c2c2820080e966058400d0204569051003a511420a4040c802104000c0703074035580c000c1250030340d120a0307849030048818401c81c0021401250340030481440218200362800d1080d120a40b200c0400074811001501d43d030303031a91004c0c000e0790028119101075421140c0c0d65000d000140041c007100302d1300d103501110007056600c0e15240e5200710301407203c012541c08446070ba03140b51b01d510140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 457770062 1250 457768812 457768819
    0x13060323060f091b070f1403030f04080318061302040b010c1a1b0a0801030302010c110c091308030109150e010312110102090a27050903070b0606091c140105090703020f 74
    0x43c01010100740c02e0b40145115442002411283c210030b08024601011034040148248c10400c10701021003a90010140c0080c1c2000c02503550b6201d00540091400030035070194a98040d180411002698070040000c041d4000d13181803007040b004000440c0d0010541000402c91050800b81c03140900d02c00d403550350300c488070400c4114281207800550300c03030f50031110210001906a60040c410158280503940d4129002d00f44400440b4000100b00d44500040480c2c5019000000000303012402c1d43d0303c80c1f01d4107070f08a50344e5030b62075844010490140c900c2160031a921b110000c00010f001400004a5040302e070032000d2060b02d10318600b0222900c1e046034011040e10345d001d01103041740390780302a10301c0018800c0340c4503c280840c0c6840c0d41d0003442112400c21070300901d42410040b103103070302004a4021a6102d20910411340d92080002e00c640114032a06420580810b9a20910f0302020303000c0800300d009000b40c1c0b803005240c220650036550f0032a600f10750783d04202810001800d20440c400740c8020f006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 457771312 1250 457770062 457770091
    0xd050a23070b0a0e030c07060c0213050f1b0a121a1f02060615030106080a060f170c040603120f03060b0a020319080c1e13060323060f09 60
    0x8004000355820030501507070600001d00603c2941c16143c41a8842451031038091411b2088480803070741c5031b1003148070304405d10003051990000c5554000041102d182d22880030482c17410500812091048100c402c00c0c1c4901100304481704a1101001340c45c4892665034031402260305a4640b5006041814008407588400c002060303100c1c0d541c80d044030f0080c044d4055105c101079240c60020b162010141809004211820030100c00321400011a419185941070074211a21503600d9003000309a55804040d00107074140700031450007441100040c5043d50300b022549140802ea08010480380e25101c01000100003510070b00d030403401102c034001400f03030500700003c04030781e19020651241d005441400040e00001850701e000003840440c0505050356242031404d030310345101000b68610800c40c014804c004100e214008440036401287d0210500c6203090301030030b40d113400c05405800b2140488090366040740e111b40030b4508a041d090710620000f4001110154076000344945820b025104881e0310090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 457772562 1250 457771312 457771367
    0x30a0207142a061605060714040b0307180909062c07030b060301020c160501230d18050a03030605150c07050618030604030c0c0e09062e06080907080d050a 68
    0x2a60008001380c0c01203003d04240d00d031010700100326911241403031560031401d000a00c4000060f9090700d074030040341d04201c0c04003180079080740b46403003159220315001c504064a807020031082d40c10501d5003e0080754048004414106c045074040c1400f803000744940e0010b0f4003000400e40b8034007455007041010700018a81045c08458a007060707032018840d4000e04038000d04000700d591084405421740b01c00b01145865094a900361600362042004c074030a89615000b5400d049480030960308042a80b00c4121401502240360180142030144119803003890480841600503405e6021981c000c5d0a00e80074110050800341000800d8019102c86c0d60b4040301001141c0d6103480820605010707074025198690308160520f00280031030200e400c9003500342c0059050002c0503000142c6103402c002e106c03c1e100c3c03c0088402e1042201d84824015400808129070f0014400c0c0d040000c030307030080000000b5a1801611030021564500204526800086d410486003032200d1145c1c801544203403040b000002d04098 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 457773812 1250 457772562 457772587
    0x112200408010605090714040e040309051f03050601030e2e090807110d0c060c052805011a06072301021207080603060601080c13080102030a0207142a06 67
    0x1294006081d541c0d0b42e440180000d181c0101500d50120356171810b00e0f5881c0c07c01c050800640168450401049211804102014043c080b140041c0a010303008a800360300020108801c0443e880882d40424034000104005500c280214145001e503040105501051807c00340a4201188041c05001c40311556442e03040185000d041d640ea03000307a6800740c55009508002416203801c6240902ca130312600315140006421120300303401c0300e9990a0028004005050039420801c503200507400b03500d000071354141200300d5100c2d00b4030001e00420007000900d00325000601026460380549034440707c2845814000380d01e481d0301042181e40d518048542c0320202180354203a8201004040107410101c0410030802c2d4494103456100000324001d0005003081320000e810840301420b00301c020078000800c0290004610082002803800700001c43d03684c6410704a042c0207401c4001c080f44c40611080c00344c0d420781c000180c0d162003500d50f1612003820a10550b500d03440c2406030101d80d030300300c4401e0002660201 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 457775062 1250 457773812 457773817
    0x21c0f11010c02010b151603110c03011d12071505130c080c1f080406020d090b04050f300904140a060f0807080a020f011e0507060c0e011220 62
    0x1d00d10f40000c540c04032200100400c28940d0034140030300b5041800761045c817144003007148203801d800d17040c40342098001c2c241580c10154070441d819015800e010088191703000e12686094415102c0060b00e04518404c0b0044030580701d800c2029191009a4850840151031a032100f50071800e54442d14070a104190f880c004800781d1640050800e800c00c221208450800070303070441c0841d0041035000340b40c026080000d4950749000c0c1c0090840c075800310340e000d04150954001030003160440344416035480e1501d043c0360368100c070300c180c60a140203080768048130b04c002c0c403004851441612001810070075403188000041d00310980785075003d1f072901c2c03061044084c4d880819000b204590f41c045051410411455440300482c2d0000f00c4c1a400b5080070010f5903c04a060100d480e41250780480d02c1d00300d800129694900500c01c56210600844102110f6070040000d1041e2071060308203001c2c40c00c00600648115158481031804a0b94500e114100083e80d0340c070030b1200e400480605030084a800c3e25213202c54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 457776312 1250 457775062 457775081
    0xd0503041407170105150406030f03030c03230603010e03031312120204141827010b060a080a0516050706051009020406030204031704050109180b060a080f07021c0f1101 74
    0x1c4e5510024001d00d01c610305066070802100ba5002e003c00c030324540e00c6030508405080b001d010181c0e9241c030782d14414400d4000c202001e07085904803203140640d015040000c4020340b0540d20942c68203086c081030380c0d00402500e11821580700402000d40c0151520841903e24110700b104112001c1d00c2c4080ea90914030141010f4000034540d4a5240c603c0810f018195951780f0104052040c0c810400c5488555151406400e407070f402d0000d02c1040e4008031080c0035111030b070001680001c01143c03440c00702d0f91114284c0e103d049421420300c416101c803189141c032111050308550000700d040142a0200751103401c210303040380060810360201d650f034500c50b0049030081d4100c80002034001a0400034840d00c030000380120841d031085245060320340000a4950102c074801c0c001c05414030012660641136a600c24024000d002e0807580c1d80e001e4500c3e0003018224211061803100c180c100224440b80c1c0f00150380f0000007280e801a40880032282c038141c0c0c51030b01c1600c00303a0030007980101c5408142028003800004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 457777562 1250 457776312 457776359
    0x80a091212020921101e0c090b07050c1306060c030804051603030e13050606071e081c0c05070b0604020c0c12030c010b09040302030d0203040312090c05040e0d0503041407 75
    0x182c9034107942d818181c6a0417000046800c20300600040650083c1079066500000e0000440c003244240035200c401055201001c0f05030081034800c01e109002c201d40030420000c48000340201c01d0880c0ca10112a45030081383c0020f100000300400103406801d5007908180980101e405100000c1c103201042140e5400481c0000c81c0d0400200c0542010b2540c0040b00f41e150100f801a854400c0124010340030306000a01001900c003501307086501c51128040400e6003001400d80e5030098410054198041d107a4030000241c6404055070354648510300f5149407a91020b0116455140c00c01000b0294000d90006186409034403898920b96464100c02d0f0380d00312a080240d51118807075040c90303003140e03400700d6014041e400b02c1d010040003035808800c4540402d400040141c4944407130804a40ca820b1003540007410914041c1c0b06424000d1428115080700c00841d001c0c404105100491a2207a440c4a8041c011880910100c0c1c002100d5900d42a01d600600040720041c1c3d40ea0018041c8281c00b01c11761108 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 457778812 1250 457777562 457777609
    0x405091b2407120318030e1c0b0f040c0f060806040b0a150e03150c070305030405210c0f120d0e03160b041202030f03010608090115060906080a0912120209 68
    0xc0303c50300750082500000c3c554030141d1000c1100d403005030111074140221846010302c002e1081e1040d1703044402c0340c41c0c540c0254040ba403074a05501403545101d800c1c0d40540e45560308410020312604810b0b190410741c0d081d950380d100d840d1101da0a000c0035200036645c655001140000104090202c0d8800c007444600a07074803c841c038201d2609040c01c140c13100c00301c3c0e41e094010108000580814800b11220581c0c0340c07900c29680c0c1c0d114102a41480040c0041409001030804051b0324040b1810242560140b4002a6102c544010004079900c5902c1c40985400c80341c00d004a0b01e100d10150f100f01e5200b0b29900070740f4070301390b4008502c071034650f000c0307400316881c04075102480240a070442007400d11204030b000942c5044c01c20855000e0380e010520035401004100390014800031400c1d000045002003002905551036216100901100054083d03c000900c41000103143c611903401106030143d0044100c0c0c03400004010200d07174401d09958105151602000b8600c0c0c01e0b2680c80c03a81501c1160403240c0f00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 457780062 1250 457778812 457778843
    0x3030c04030c05030a0b1b0c160603050708090606010c0201030f050f27120c1c053103030f020312010801090b06040b031b0f150301050405091b2407 65
    0x705110700b94014900941c02050307028002040c0e4003000341c0009082d00d00c484082d4081c0107140043c8100b48030420030340204c1034901d071100c2c3d1408881c400d40300303141c50500c01c566501900b11164581200c260078140d208d0004542654010382c01b0040740f9006142c086101c0000c100c1d00c2003580c1d0107842e000030090340300c4108441070246202c0441c070f5004502d91454010802712082d80d03605c0782e41c1450749040000140030103550b5010040740b1000c406175420810030300c07840c800c040c00c0d030703007118a50030b500062100b50b03980c00c1010390b0020303580700c0c108080d442081030954404940340300c2d01110304c0c425880304025800c89252818003207402084040004030f0300080528003403101040240c0346901542c24034203115000d41e008540500e1b011000c03000640e00c190b00d000082d080410043c80190495640c6244c1601c0703009075401503040e1907090389c0902294465a9046a6800d001f105000340d902400d4150241072501c40d5074944030f0038168941e424030800541000250b50302041048800861130308000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 457781312 1250 457780062 457780073
    0x6030d020a0305030103030e0a030605071205060a0f0b0a03110d06060f030504020f0906010e12030322020a1404060306060905091605150714150f06041e05040c0803030c0403 76
    0x26154000510140a892005540242903400180030080034030481010113855912120b054400540d0030404c18802c03802e0880000e009d14501e9411140307a542032000007055810f0119640049030846140010228504201003074190840b80e010b1080544541800902d01d500c00050000c6002030071002907034618081015101481407184401818101810070015a5039414408502c8200f0b40d203800e03440e91240c00403240480100344095101038a00091105c040b8004099403182c00c02c83c1c4243d040c200c3c0101d8681c03400e07501e2075009500104000083c8071240074080c0c01e8003441d030040d002095054503541c903402074a0441c0c0141e40e00e05c0c2e8900422600307680c200304503501c00b01c2c80103110108030b09002c08140c030314442001c2030801d54000076180040005c0c4e00c944a5510071740c00e0540d1641c841c110a02c105d101e01c140c03070421416a41d8800300d07242d0324042c82000c0d51400d8414980d0515400e000014018107001001a2208a540d120004814100748011442408010b0355241d9076030a41c51325 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 457782562 1250 457781312 457781323
    0xf09151306050d1505060922020301061115060f010c140a06090510060302010e040e031605070303080916090c1b05011d030702030303040605282903150c0d060b030603 73
    0x89613403900d058100301a8440e032007118100c80701034400a0100040199041d001c1e030303012011000080c030010001400c658030641005000d44c0a000b076590111100120354400f000075187d050303001101da010650503601841c46006040e1044030800c160070441007115041c041c02100580b513468490362840100030040c0044c000c40014101c0400410f801c0d81c0008000340b4803240401d00540c2d58640b81c0c4d0200c0800c0068070554005c0000d48180701409203415034554029200440c0480d1094001c2046002c4c0450410000c540c14000030400d0391802a9000c050a8400040c80500840c0b682da242c180c0380681a4070302c407a005100125603020b4048040e10300b001d06050810207034205000c06001650080b0031030b42c1140c0c0019002c1030301d032945100344078047d8140003108011403041c3c01c8049060f190f9040340b541d000f440a81d0a8190104988401c2203405000f0b00342d606404c168104084945040741c1690444000000c0e28240030201154000b12140c2c1c0d00f002e00178103008410032001c0d00c0d04010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 457783812 1250 457782562 457782581
    0x3100f080619050910020c03040b030411010e012a020f030d031406060703120b060f0712020705060c03030403121d0f060106021f050c2119020f09151306050d 69
    0x700f040340d450300b401c1c030540360940b01454a0340e45400144c012018141007042d103001e4243c031000b141da24200381c94030400d010303c500703a03e901007400000241929030040841040008c50b10040511079502560400f01501011004980c0b00000b044079044c1034404005201102d00c1c1910b0004501402100c0c10301041401840c0d176200f0003081088000207039000c88001d60f07400718004045402c418000c0040c4260003004c0079a602242d01280440911a410f0040e9402a54079026202d02d40d80b503105110140c8204082c0030300f141c1c01000031400082c07045440d00d20b04d0071010f00000702c0c0e2191980610f540c0b0094010b01ca413552007141d10410102c02400b005006004500080c01244c4c0400724407900f13941c0d08600e40c00320986e03070310000d0314480b0003a08480b841901043e0750301c030401508802e00c002501c00c3c3d4800d0400b40c461991820914035a00c03c03101b01c00c41d10195241041498010042049103845411070301d89000d101000082c0d4440b000d80c8040c0c0141e4807000c3d201c042448001088950692 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 457785062 1250 457783812 457783861
    0x30c17010b030d051b15040308070f18030b06010207090f02040306050c091c03020703080403080406120614130e0a060b09070903020108010513020c15100501020a0804090203100f0806 80
    0x1c0c07045125401200f05c403980305001441c100544040c103540ca0411542241452800c00c1200800c4100755002e4071a61103450191101e11100701000e40464110900411440b43e14070b03070300e100303202003402003400640c0050148100e54a071034607940d42c0e02c00e0b0b17821500c050704010380201e000e2007080041c0c00307101c1d0310041d030240e03050400007203030002043d40c544000341031082e410840300901810f1003400494050354021000d01c3e561680e030704e80103c095200d4458113001481280424140030700c80d00400c0c04a40718551980b0038030f10a20100100c240c0c0d95030301207008940c2c4207121a441c100034807032404158003e03400003c841d080710040c001120030082002e801c1116010f0103000607a000b80f191415582c00f03030742c5290742c210000b840400034811a1411030032803141c41e0100103c056040081c138412011440184c03c3c0136500c80041e6a06d4032148001442120f080c00103000320811a4003860380701d009042c0d03076410301340d444505515412885d00180300e6a0001c1082211054141c100d4807020304408 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 457786312 1250 457785062 457785073
    0x1b09060f080c070602070c030b040c14030a0f030f030f09050c1c050a120e130c020c0a030804090e070513090303151203030c0203090a06080612190f050106030c17010b03 74
    0x205040302e540c400c40f41c004100035400b188a0040c0101c680030718015692008038034913541442d04244404407801d20501051059204460046040200c2d080c28a1940301001a0f0112a103039015180c500c0b0958460301010354a40450755090018000c401c50903010300013030019016480c0500c009040c9084001c10254698101c0600003840090b2603000e040d08903003086035000e0781c00c90480300b10f500303040000e80c410100c4d2040c941d803c031650f20148040a11b602100c840e8800744062010248a61201070315240080c0000c10000c074503a0821842c040c03501c1d0a5400b0a078035480010322503103c007000c588a0696480701c00040582521545072130590308501c80ca800c0c3d1800220343c0c6030f0503600a00074101034403008902c6040713001b0415581d2501c4000c00030103500d030700c800008000401c100d529a1266951800102c081403021454a440c111000720100d110031041d00ca011002d503018004503130745d41d6104400004200c04c02054005409451041c006c044c29a411050940350007042071446030304070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 457787562 1250 457786312 457786321
    0xf03160507170a090509010816170d0e150310090b01020c09060d020f0604150210020901080106181a0705010b0102070b04061202130b0c15060603010b0c011b09060f08 73
    0x800c644090b090780c03a0b4445555411111104403112001035211a810407148800403904a0000c2a42d85903c6001700140050641c0d68100c40203504031031041c1d680641000744026010f5116502e00802200c000d492800e0300f882d481d0f44a03040c0d03070040380d16900c8503132030b11400d04c00b00c1d9050203840c40b8040c0902c001c250500c00c2d0070004041e41001f40c5141d11800c0d100350003201315101c02c0c4d0501d800f4080148090f80300c40e075a42d406003c090b205100040140200c43c01c4607403800c454402e5a91107201071b9a030302c405070f080800940d1140f00700501c900d181c20389031400183c10090362074074800c8491200200e546401d940d10341316007541c01c2c0d000c170386043d908550414131202d809070043e40c0481e00c581c41c00c0c5004001c940c0d00c071402880703420444105405038010110f000d00e90700c0010500700e6441011900b80b400c0c480c9117800e40000c00e40c4c5907640304100f00010005084414064608003010303000000c0e12102c003243d0f8002c403881411a0001040c0e030064200030850b000503a02e80100c6a40c1810000f6180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 457788812 1250 457787562 457787573
    0x909070518060d0614090106050604030f02040506120102040303031d010c12021b030c0114010f0308090114210907090c0806100216030b060f010302090102100f110f03160507 76
    0x15404001c1e031014203074000041c0b040d42d03414000c03107656400c5030003081600d100605810100030100c8010f0030310f6003001c40005030b03814460100c804680d0403042c802054a080d03800c00026003805400e26600080b1b21201c040640d0f420701c0100001c2d032190303d000480c805c216000840b240c40c003800700c245592404044200c0c03a90000c42422854003079100c01a130340e0702c096038204030703020b081445000d840c4000f2804100c40c2c00154090000302c111503410360140d80ea924500200c0802900000b0141a0288007810b810750280300584c048004014409080c5241100521240034070300d0980740c40744e61114148056403801f0b101610103448146001d1020046084000d01007020160006024041c10a19a840d0902c2405099011a4448410b080e401c2d40d9041060302c204003541c4c0d0764850007044a402903150302a200b00d4005a138180c01400445194010104c000c3c0303040346888400613224800399540c240407400410b074810003010029105d0030801003a540c0301c80394401820911500f0045040406d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 457790062 1250 457788812 457788829
    0xf06070b0405192d0201090603020a050403081c0b01050306030717030415080103030f170a090203100e0f0105011a040b0f0405040606050c21180f03100b09090705 71
    0x503002421191140c860b450040c1ca40025141d1082c1040b104504040030405030416402040c1d000101c132111125859018804040500c1c50090105061500420155020760042c3c0720201450801e2800d180d640d48030120140c2c00211002c4220b0380108120211110502c2113080744a420310f0007a046252410200765500702038080c00644070220300050340440c1e0100211400341070640201e08020214207006031190b42c0a000c110041000d98044090a47c85444800d61545061501540076100ca205180080030152001c2e605405503c08411080020380290303080b1081410080ca006044042220308442c41030f0003600a515007100ca126240d14043d068a095541f11901c0c6270761401d10302c0711140c1c180315960010b41c100d0b00b06100010b00c035030400044c0000e5002e100031b941e010f00040714610710300103004401d6011010301388210342101101c4494402c2d010009040300e00c0c403611160029180443d000810b11303640c5c4e02c1d18510a464144000e072a5017150480c0700a0030315505207400501c065 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 457791312 1250 457790062 457790077
    0x12060506090402090f0414041a04050c061804090c06090b03010302060708030709090608031c0b031b0402040305010f05090c010219060c140c1b0d0809040203040f200405060f06 77
    0x81d0340100d0701d00025030705c0c82c100543c0e8200c01001003111040d10244103000140c110350a4514040c5d42d40e2030100c548501d01521300c115403100240c038000002c07004101d032542080e028005400f841c41c900d0290740d1100e01c240305915010f1540c0e10b5030300c0c1c500b640c001c0404259821501d21810248010030040c0c0b00d00c1d05640b009a0720142564403036403040000c031142d48403540b00030822400e00c80d000404c1100440207200544d56214120724074546440c4400a54403081c010a1701a840036940e4124002103424108885400034005850690350751245070a40702c1941e5851542035440c0148400c1d110200041284040c080c0003070314100d91242101c5a904403070900181000381c441e44440300031441036902a09451a410b19a17880f4151240059a00d0700070145280ea40c0020903180b031080e103080740103600340070360180303886261a00700c0c8c1c20310000c0d400140084a00c404c03004110000150300510a0808640c040b41d803104d441103480400054420292071340d402142c0501e00c814480c0c44800445000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 457792562 1250 457791312 457791319
    0x5090d12050403170a05190501050f013b03070f0302090103151b0f0809073f050313050901050d1211010203100501020f0c030a120e040612031206050609 67
    0x4560302ca0500380e5556201080000d60384180d80104806403600c2e510890103030405160008200e5002180242210400e00038103a01c0041584141c103d90720401000304800092114090101040c07400280400c0014026518132640c40b22001804d00b02000300307100070007a031f0001440d00d40c910f80108040800602000d8a100d203848900c96130103e0035082000c48810070361034802c0013803c1003001400b01c074110038074100140305440415019035002910600359031048031666080d26810780b0005840c180078140155a010b101071540da583c0e4281d4000107010702034000707595229000403900b0501a49608220300c11400800107202585840c00c0e80000d643d130100380c6054500c407040081e90841c0761540c0400e810b6000008011a00e4081010072046500030380840c0c19100c1d24a404030344400303040c1d28494050380b0440e072641c04641210b03044001c81100f8103000000303101882c0810150303003840d0840f100b2400320314000002c055105004c5c0c0e0039120300c844200b040c2e504000021341c480c464003030350611 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 457793812 1250 457792562 457792571
    0xf060e1317160803010b07111807030f06030b0f011511061308070210030b150304110d0311030f1803030702030c010f030b0a290f07031b020409051005090d12 69
    0x205840001031108481e0800324444d12983d503039006d20119401202c0031182540e16441c42949414200f50141200c0300c4000205995511180220001c040442d18000060f45070000040420f070341c0940c00b80107525000c406000c84d814240c120402e04180d81d080d20070440007404400113450007103800342c0c021080d15401004000d990901c0c60050040c03600183d0320600d80860034401d90340540c04610b200500383d52550808042004550b806e001c1141c003e404694130072040003032413411054407400144203081407521b60941944091954200b01522180c0c2c0d42d0008a000200c0003540d01b624131044110011442c061465000c80e48074005440d940c0c1c1405000d020010702d050103a00002c10300200035000000c020b6440c400314848440c10401808680c1001014a180620307036401c403409034050b04202850071003281da00310341e4042860b00003001840700a141000581d121700915054030b018030001c151140d07100b602202228000750000582d0340c0071410000889030420a101e0700b50030303030313820025 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 457795062 1250 457793812 457793827
    0x6060f01030e0105090105071101020c10090204140c070c1202060a0815041a09100501080412020a150203040b0c1326030406020f060705070209012102040f060e1317 72
    0x1c0c080c21080e5000020303542000c0403c503200d001540024415070b6039503070301c200003451402c0d506e01300c3c42500790b003075901d4207d00400200c045181c3c01c241ca0b0785101500001b2007809054101d1403011050701d000d80c1d07522000900c4401c3c06840d41048025003c01c1114111a800c00e50004540d03102d0100031f003050021240004104610b41b01a40c0903100010348140610409424030414074020110f0b00391203444808003040112180c07050000940f54180c46007000380c1c480f03403110b24005041c840507038214801c200711800029a840c4640301c050b00c2c07008002d6184d0515190441105100814850150310140102d64050200c00d003040d003150744c0712106006103034815007000040c80320504107054910001070006100f95001074160b0b10806090140c91143d1a2200215641e2003603140c00b82d413020307088006000c1035a40c01d01c122a074904035010b00f4040b0700180d0108065440782d15040c90034940e140d80800002064000d248d5008410901c40000d1040f295030301c10050340ca40a4000128a0114504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 457796312 1250 457795062 457795067
    0x30c020f030d0c0201080f070906111603030905030c03060c031302031e150a0905070303031e060e07020c01030b130b190e010906090905070510050d050406021b0303040506060f01 78
    0x3100e40e54054150741880c460b0460140c081050f044040780001c42d143e00191901c040360b2411070042440d0341d185840907103804421164400c508d01e030001c181c019071b11080e5aa118200f544070003103110352580782455141408050401100b40d4815000e9000031040000703c15040088a500c540c0024a40c0c81104550002c07070300c2c01d0070007211070041100b50715100401c060000350400640b254103528080366903a1503889416100e0104001b0701c150702c03115007480003038041e822040001c00c0c400c6611140c5481900c4180070380d2a030354040804850640244981d032030b410b00458000d40710a081c1400b070041914041405d5440384c03400001544c1e914000300c002640d64506880040e0300038074683c00542e4a9403401d0240c0341d4280b14041c10245001c000190040e4207004150f2440e40260240074103074940400c0c8810500d040c2d440d8001c1200030440c41400084500c5100e0259014180050700c40400c0d40321940e8a0803c0065030f06581d00c1401040002040090b240b41e00c0b00e408c0e01c0244007600f416005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 457797562 1250 457796312 457796329
    0x19051027020c01090209060a0308070204050717070c050c060a05030103080a05090303030a0b0a1202060d0c02032209050c0c070b0f0f0408010c020d0915050f0c06280c0804030c02 78
    0x5000c0031800090000c400441c150410303152280210781d080000d486440030414240c50500c8003c226020503c1170b44050f2805602c01ca41c0100581803400d607200c01111644c5481030100e40440200c1c400300496400d0007400c00000c0248203090f940300c0c2c41e00d40f40c1e07000545680414840200121000500302c0840303845002541d10b00c6c40c0190440707450b0700701611000701a1021000c024000c04680744d000404120fa0410b515120307401411a034a8404142e50781c0000e88440e5081c8004c1d4803041120060310303408500c0103000c20100704032019000b401c2039084000e51303201501c080c52750041440f45441402012422804840d50800c1b0160f951003442c00c95091801008004042d050002c41c00040c0402d064004e07040c0d02d030f50b540c00c0c0c804c80f852000040c1c4000c009400f0705102620545000d22400d4001c000610256007045e0145040286689030b0303901d007010469050981c2d8055210060710400c00041c641e03000700300c8500a2000211030b020003006001c2c000c04c0035007044881407410b4295141c0c4c00c01e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 457798812 1250 457797562 457797629
    0x6090c050a3b070804030e1201020a09050603010311090411130617010527030c06070e1003092001050702092401021605010c03110312190510 62
    0x7454401d030395220061480c80d140401c80b0080c251180c1400c044241690452042191444508407a0700d580d00111a05400108101d040c44400d40515255684030803d07640265120400543e0741c45004d2030041406516500c030a0040c1004e100603c0054140304060400d4201510780c691941d4903403c11102c1000e10307030607035a04103080c520110814121600a541610801e60144407040e04200744242250743c00c850100310040d84441c3c4503004004d810020b0014013265013228141b50381451045d0601e5800c1d0340e150701090440c103d088990411540306180d12500e810100010700c0c240c0c5560a1002c0441c03444c140014941f00411300aa004806894545c0c3e00901031980520704007001d03440e070840103812400c60200d070010820b01507100146481d1000d030320301e0f10303d001103140000540e100c5501003421400d11a0000360190000700c2040500050030f609a030405150800e004003c1040c400420301401c1541088204040c00329010520411a00c00b4031020703661241c189a03860800303041c0d01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 457800062 1250 457798812 457798819
    0xd080304051e0c0109081504060e0a080f19051c05060d1506080622110d0b070e0a122003031902150f06010c030f17011d010b03010b040306090c05 64
    0x2492202c0250000e40c081191800382c0343d01482d07039160300503d41d80f51220806004080c04600c00600098455002040980b41110445400b50307040c0e9240c92864000c4c0ca1030200500010034824490038841c2c80000154445d41405880d00740c8124880e405010b80080c4600320b01d880e90007040950702d50314200100c03150400c001d000180320100c40c030009807d0b1882025031a01c182000f1805484602521205000031031010284440c01a40c1d00f07101c03842010f019640c00040440c1803004031320022040d5204a510759207800c9003080c00010418006103582000004c0d40098490400041d4182c040c409001c8692803d0410700d0701d868006483c40c8280011440c0010343c100725040421340004485455110840c41200baa03610310000c4900007600700c0d1202c1c0050140f01000d8042409103c00c0b0304200705070310300140c401d1441030003010400b8080e800720303d0014104403003507010750040712018050329503c0701051441d49401d140c0100c5008500001e01410340c0d5407a401304010384c60451500034003014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 457801312 1250 457800062 457800103
    0x12d1806091703090d0807080915100b0c100509030304111207090f0c030509030f040303202406030606010905150403171908010b040902070524070318020d08030405 72
    0x1341503a0707100e605d10201e07900071429140110715418020007605104900d40c01c01042403680b00850700740001005083e01110990204012a580495000800820191800510020501080003800c076000104002a580c005005200005404184640c1540002c1710350094440e50100c417181040f040798054801280f41c00c2c0c001e0b10b000700903000424085001d881c20003207552040022900c2e07101d48003007811910b500300003d1000030f01038000081c8088010442e440000c1c48400310520741007503800c00c041d079454603100010154010380d03805c5601840540190440b4108880040c00c0080b643c01140e1003540f01d00c010262514400082e0350046070414540250010604800e10aa910004040c00140045440701a402d40100c1d059412600700c40301091070b0900e000005070094200d8042140c15000d50384000c20a90740400034402901c5a01d6026074032820802c101408480b00c221749036811807070000a900150355134417a40072020750403c001c02d42e41d54a600e040c500b400b14004e02d40c04c080c0e858 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 457802562 1250 457801312 457801321
    0x90402010219150b0d1a0c1608030105090121022206170609070605090d0f141e0f030d0c03090c060203030601031112150103020903012d1806091703 65
    0x2140050343c5605005a4104039500c005402d01494004c015005131030f91000641420b40100c500a00301e0b40202c04050031401e00041e903031803031802c250a0f642515903074000300052040e443c0150070540100104509841e248011045158800c0e00340d560207446030718a100c3d44112a150511840810440356008010254582141150001002490310014070424000981c100c20018106041c1c0d0103680301e0310300b0b1035100da0400070106d04900702240d03c481ca0071084400103021403080140101003074050802582020420001c460b1020502406c6074800c2010f14010000407003141d207040e03400310021a00c01501c1d50306501409143e03800038604107100300700041c00d6601002440c02020b003603034203214103085840c10307491600a89140b681460900000b080c01c200c19600a908030883c103040c0035040919400004e821960031000080f40000440d032501d400000c4625482600f07400030074100403020032100e400c1c903060011840100803540d54070400d4180500380060a0340c0c4100d540850784d5030700d071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 457803812 1250 457802562 457802573
    0x51305040620040e0115022116030f1d10030b0a051206010801110703080705070c232b020607060207170c010c031e0c1403010b0910020a0809090402010219 68
    0x110f0303c01c3c1c04600c4e03008800482c10390081e1020746078200c499070003448580f1000914400b44400880640700c071810804c407100c1b540c4000320114510b54025201e80301c8444a1400107010308071000360fa2041010f5a068081050341c1c3c0104050460302280f0f00001c003648000081341c010b40c0310350400703503002e4124241c10308040400107080341602d40260081c04082d180c1e0b41c16080c1809810030003000329224400203a502c03803245001d03040990246452504080d902d9051042e00d102880c50190000000041d640f40c5040681c5074148408000d002c00700d0540e41c5030f41503001c00d0142d84000f4031aa40001d4404144a01e0f41c041c1d981c40c81d0840f0100700c070724900350982e080541c0540c14a41640d400d210705c0c00500340c0248610720f00c0e025581a05403a00c0c1c072042d80070307004007400c54944013482070444508070040e982001a43c064500000c1d00d42c4d40f001c0762010403400000b07030103c440440d8030041108000441c00c4059446480003900c0320f8586882c0c80c80141d0900c070710b03003010450450941074000c00303005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 457805062 1250 457803812 457803817
    0x2070f0b07021507121412101403150f040503041a1b030304020d02010f0504090e0a0204141605090d08070b01140f09040f060615050a09050103020301051305040620 72
    0x303100700c0d10701a00c419003c8a486103030040e07180107400710480d605001400d0b030243c1e40420309910802c000b1440c10075240c40f840600601542c036042d55008240303043c81031002030303204440c3c0c10304100c00420100d41306440300d80403111300a10600c00004d4005c00f180400904106070387c048c25007003021040d0079140c00101d2049411142d52800d076004020302c4900c00400200450f801107402a04d450101c004540054030091011000002080003c010004016040b0701c145040c46800034094601522140100300036219a81091410b01c94070000703021030b07003242c1081d04455100c0b41c1056602e0f001008005030780002881c5003d00114000101b020130041c49445286c1a41c030781c103911410b5109800107010300c0c45940001c030340d00305d8000c1c4082008150740c0c20042c0030301c510607840462225110034540201c070321250000c0f000b0602c04195207103060f80003140030028110038a01181558134280c0013580c200011445005220b075100c2c080b4003030183c1750b0003004410301210700d0301030000d9501c881c1c8401d1781e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 457806312 1250 457805062 457805077
    0x613030b060306160512040212070f18060e010e1b040e060a0602030a020c0603130203070e04060b090f01230307140a0909020f10030f05070e030105130b0c0a02070f0b 73
    0x901071a000182009071249407044020315640e100b40c1840014080c144941b00041c10a03070b40700900c08020028241c08110140c040d02c0d00c91090315030a0b00d0903020748192000b009801100505002c400c0c0905804401c0c0d81e81140d070301240c50b00c4280c549603000d207a2402c0464110513100c00014001c01d40030030303105103140031b41d100b0745035451041c0d503c04041b0389901a460580b40140c006c000c92880d54608000a150803a002a10450100100b5400245407891a13840b201c2201e905038200410300040c1d00c60000103440c00d17140e80072285404040d09940d00e105001e44e600b1102c510900680d005203681403888804000703811580c604d82c4510640d0100c40f03034224500c1c8078510411001c40c2090080c050f800e500c540c0a00795814950440d000c0040c0206050028410035644c1c4c0c00b60003415486009090052410362038900850004a0034142511402803140c841814111040c00026155001103584188807c120980320143c50b001241030200c00d80c421140e82407410804113400e108400200a803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 457807562 1250 457806312 457806319
    0x303020904140610090305030f090102070504231024030212040c080708010b0d060c050f040308030a06240f020a02090906070f2604060f0f050a0c0c0c140613030b06 72
    0x4c103000c404103c9445203e800000e0083d0005d1001c00000304109020306110071050058034101c1d5200d0000c14202d030703111803400ca60394514144005800741c0134034449801c5121a00401901760520b82c00c1e0a68820260160346041c08200b90401f07407902c00e505659402c600315012161509081c01c0043c5681c010740102842c03800361040014100700144112079030500d0151006020810548800c00103200140d640800c0c02010010920348400880091014500c50200b003500c0307061011095048410300e07007010540d41d0404000c0c0d03048400800716403907003072001d1800790070202402740f0407403c21844040003034110840a042c00f201010214586e440b5250311740d251820b86000e03907421101c0700d0004c0741c5411884008101803410b01c04201c0307100d034014010440400c100d44c0c0303039010004507098900320f0500e1590380da0601c009240070f8000c0d00c00030f41b0f8034031b0710040704411600e854150000b98403410a100381d83c00328205840d142d0741c050710f1020201410562440d55603045c100d8a0903400c0355554030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 457808812 1250 457807562 457807579
    0x90616050a0b19090203190206041d07170606160507051309060e0c06161110030209013203100e07051207080f180c0a06030f0f1404080703030209041406 67
    0x4a090492144c00c249580042c01000d40e1014030040342940c076168102a604007100300004203070b0b05030305050848500180802d0700064176091030010001046919284000141007050103a103641e0300003074454020780303025106408030f203d00e04180f07081010303480113422420703404008a40c0b19055101030f603800d00852081c0034020300400c0d199143c0c1d20b4061000e5005106100004901d02d1642641008900c00d00010001501000010700750f0607254164000180d00014514802e580c0300c00100c01d1003404401005018134241c141d402c808000c218100800807011000540390380084001000900038960549880c5c03e041500401640c020016107400b41d10315804074004a1140716018850700440360080030780c1c1c68401c0b01e10700d0307100741041c42c54440c402d50302d8541403662201030440c0107000a89000503035400f01990f01085d24441182240e4492500c42d801c100c205401160690003603002502540e203070420300d010b070024001c41450a4100e89414910400f01c1105922903000d80c404850303025 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 457810062 1250 457808812 457808851
    0x303050606040509071115040c06110601060e011d09040f230d0807030e06010e01080706030b21070905011d0901050403170606070605090304050f030d05090616050a0b 73
    0x4054802d41c412a034001180c0d0b400501414807a0780082810080002518003041001002d401c40c0071f025a410755152218500030049141c00c4080b801d01c041500000d40042d44c074148018080000000515050003009182607058002c90410340a40c10b100800e41290381c1000c0c2000c5043c40c9003058112a045040c50108600720a550054401c10091100410b0810640070040301d0541001d4403100925844240c01481e0703c000388a4a03000e0030704042035081c07075031401c0d000c0b61400442c1d60040f41810304c4c14130124100e44030040b103d805882200c0c0290300f41014074207600c0c58600c03039502210b2410724110012502400d45140080e8070410078184002d280c843c00b4000307089030001e42d8000c0c04a00c1c0748802c00c040310044102c5e140d0102000b41058184129502c416007900c0c1c0450b244441c0d9000001c5c2400b2a182600521503042c0c4d0540080c5101d04a6500152003441049070861240700041140c40b4410954048922041d41c04400d64400161034a00004070a000f9208540030680c0141020f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 457811312 1250 457810062 457810069
    0x9030207050904050604150605030d110712030e060f0910020a02040510061b06020d020708041a213303071a0f0315030f07140604060e0f040609150303030506 69
    0x30b601454001d0043d01454407580e0355030780c910713014100421410352941000113180e6418000c2040c01f869031344030300072100c402d507910300e060000c2500169540d40101d505071011941c803440d031248140c400c1d103200c3d9a030b1910180801960150904042e4803592443c4c482c60881da020401000c054800c0c1c50034800760325140c0030494010a00c1c003400002075030b00002ea95810101c41100c0c20700314040d00c4010b00c0c1c038600781c0d6000243c0c0e100210036034203503070b00080810116492603410605840941c0d0b1407818005110789507000d040c5c0082c1030328000e1580307001003440d24080004088004880c075140a03c1c1d5006403100081d0a512014028400e002c2c500300020f4880302c1c0c1001c20803250031020b506140011480d40055a604060108003c2480c12400fa00d02510300b00680c0d60400801130041115903d1300f80d0150840035441e501e1406014140300800c0507540241400e88a02001c480110039003180b940450300512032a80b00c0f8050508000c2c41b049420481c4020505580c080e541c203201ca680c503242417 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 457812562 1250 457811312 457811329
    0x80a030c02122704050c07020f15091306182304051905070f120507060516020f010e040f0506130603050d080711072304051015051b010903020705 64
    0x140c110b950000c011001940b40d180141d800d50640c9203901d01101100d220100d002c4801c120b864a503d481c0000c0c0b080c0561400c03014040944074200c0304028070914501005030140179444820303004029100140440305403d400c214050191590800301034030294040602804503451454101c100c5201c0c9004088910b1412610071900b000c02800354010180642a01103402d03c0300b6200c0d4090170f1f134045079060564004100134800c40b0468158400d007408e2040c1000ea2907809201400300c20045500c80e414140d803840c3e13005804a448035022401040160354012801040c02c2c2c0c014541f60b2107000545640d40041e0040c501540d250740741060b130404a100b111007a010113425640489010f0000510803000700f036202886207052451036200d0814107242c10259004201140b10481b030344c4000b8100c0d00140602003404844c140081e0815011103d5800214010030001070703050a80c80d11003a0103042151b000d13281556981c2007a6480072801e81c003d0884000450040c011003000080d2464140e40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 457813812 1250 457812562 457812583
    0xe0d051228020705060309120c0319170103060c110f0607110a03020303180307080406090302030c09010311100201020f0721030e031c0f09121e121104080a080a030c02 73
    0x80c0038042c01d2504220305c0742c1004151010318450325100060046405002d80312043c1000e00940e201c200503008180c0040c2c0d8040d0507420013401041140420307241c19580d60443e90040e10024030644401000c569060742c01000d40da25102c1e030310301000141e10005015110b050156281c1c00881c0f010f11580f9100d00103a240a001a0300034400705800300c10440010f0f0303034504107904807403400e000740d95505120f4005e85e101d580420b040000800030341c10300384101c00203584121985952581141e85043d2100d84e001c1d000c5010f6a900740560304941d000754103c4420440e210a8151074010301d2130b0501c0d12401164034102041845c3d084281500d000f03000f000c052203803400155007011144040d07034464640081610520ba40ca904058a10381c0061140403a0940101089032000200a0016000c03500018110400c3d83e00041500c1403540e00c20100005911a00404512804024150040c5000710341042c4031500035003481004100140c0c0041c040103556441c00d1202c5440d01c00e00307130303103070307020240b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 457815062 1250 457813812 457813817
    0xa080607050d05060a0312110609010b2d06030a06240e0925030209190609050f150a0332010b03040212010606030e120f040302010e0d051228 62
    0x8400180180c6400459100c1001713041c403810240d407501c0d00c0444c18082c1106102207420745900c20403400d42800b503654043c02200007071098005603004259020880d080701601c0c8200c00c540c01803808880d8100c0142441c1c01440e0300d850341010f207020002001e00c3d11a0f01c1c01c40a900100701101d8900c103c910301c0d00301c0310b0b4403807400140002c400d102c003000004190340c11ba60521640e40e0350074608042c00b0600709125a0300180c644000005001c40941d1805038880800d08140f410030040c0d074081000c40130b5078000d9500caa041000b18001c03030b2040d50301c28550b000021000c500c0f416259419449260240a0342c840407051001000410301c51907000c0240c001040d1280c0d00501c10301410400440c1c001e44050b011241c2c2c40c1200b0950350071142d0320b8118800090b1201840c3e00c0c0034008120b034084000c1c00188161a0005403007100d840380c4503900c0028148900203071422050f0340c80803140c6007030b00c1d003204c02c0c2c82301c408070079100c43c7c1a944503a2001c03034140d1900c00c030f42014400f2140302c00644505074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 457816312 1250 457815062 457815067
    0x6010f1e030b07020706030606170c0c01090602120702071703070206070201212a1d0a0803030a0504031d01080a0e0f01090c08100b0303042d03110a08060705 69
    0x34021000111111a40304600000c2800100242900080b90b03c9100d85901500e80103040c54802002d603032141d4012420031000c0003180036148031032205903070808200c104c17565590300030204850240c0005035000d4842813004c43c1e017a103c02e800904651050010b40e007a6031ba11a01c40007090020604440d101065074800e00c00c000060514070010f00c00c290050601c0c9003a1005a0142100707000608500342c00a030300c80c0ea405d044070742c034004c03104844d103000420b10011411441006007481c07020420180c0d5021650602d205648900c5d0351030010344000c400b40d907130300d240c0325044001a01c4180d40031400140d80e50068190665824400c11401c03105a41f08050b6866010600b00649280c0480c48c215018400424031005400d225021600d0f00c0381c040b04104a1401d0020740c00e212185150851070780c00d0041c40d06299401000311340540b00d40c00381d076030500c2410800c0c40b25071194082c02a9103d511b807103c00b00c01e1000c000310b425462402200c0c68441079031501d020740e890b47d00c10380d003030700c0808e000b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 457817562 1250 457816312 457816319
    0x30304050c15160809090a0209041a06070615050405011d0c040e0c030601120507020a150516050a020703151b0c03021b060913020c070f0e07080405011401081c0206010f 74
    0x5209007803007400d0141913103d05025a101c0004d0301d0b0081541e43c0906103500042d1a10581082c2c0500d1505103c2e024003003034083c0310100460700d54841c529004003e150340c0c4803038400c80480c01450401400c000380040001e0340e1240103100084000646540486039580700041d14450403004032015240155041090394564000051080d04003070b000a040c00403004500c555000c0a11516102c0d0341603600400224a817800c1c1083d40c0300c0e800401901c01402d002c00c0014903200209814200304040c41d00d85c0d6a408a80c038120b06040c0e01d500020728185040c0e45080c0041d12581101440b0441d40800c8900018038801c20f90f41904402001000358100034940540a2000380e1051940480a03040704c1c0740c41e00c0003002410940c450485000d450390701142840202c6410031031840980000d10350303011303814101954248d607408014450400c000b880800501000001c0d00400840b4160b0940c0b04529612828200c0c4c41c0e4a54641070003014a500810602d001e03c00242c243c100c0d02c1d001d4010504070308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 457818812 1250 457817562 457817587
    0x31b03090302070b2113020d0606060f090b030c07081201030b070905040510050402030a0b0a0906060908030705070905040606080d0903030305090c010e0f120a030302030114100e040e120408030304050c15 89
    0x80044c040c4180031b00880060b40583c440d90044a80140b143e0800102e00f401d0a0015040513a01030240003080307028081484040da08404498200052110480d255071543c80c0c52981f6205100b01178514042c408000401c100303214215500510b059220701c03440c9078581081c07208a8804456000301c120501200f04080c4c103040d4000c41c0c00040d4268046002c01510001c00d009840e02c0d440421905e903503510402c001580301c072070880a805800017031480e1101e9a201c0075681e10b0f60f4010503008035075a90208007000342e40d80c003035001404540c2c1660b1900f1640d200140c0303480668801035011038101400180300701008100191090016103661450314080e10511120a2411501a030002c504405090300c60b402001018619446a036002d0b07030f44d6042c4084401c08070480299280070781d00300d000070b02280e07401c00c88101046e00c05860008092215140c514644181d4245100c03000c0310028002c88c2c080408070065215a0003074040301e140e45041d400380103510842034090b5481040c1804941351408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 457820062 1250 457818812 457818877
    0x4020306071809020f09030c0a050901090203060406050d03120f0507170a060b03101502070b1206032107060b030a03022a0303160524011203031b03090302070b 70
    0xc0495114460030f0744611002c0300320b900468968030940004503516066240400907000340142c2a900d5540c441c0c541008260400c506000d207482003500800083c11b0b544865110a0040c40c0c024401c0d800b101d01c90902420b05c0d18a0380000c5c0c8100d003005071200c003012007401418000c1da20340c0c1d162503580106141071030f0300440c00707490301044646601c00041c0c2a0007803400356001c0c3c2000200501402d10b841001c405401d44020304406540000000700301030b8804800340c520782c901080080b8050364401c0d00003410015040035107a807002c000d90784011049000300203405440e01c104c000b0400d0304980e9081583d41c4810300740040040c0d1141004030010038100b56040f201c2045441a01c040207040800a411034000c03151015094481c00c010005209042010780103010000311148100c0880c2d0807080740030307c0140a038042c81c580040c2e8500425209510410600562005003d64a03c00c40001006072060440030b400510501e40045000c1010804660304454020034202c80e08030408169801003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 457821312 1250 457820062 457820087
    0x50114060a030f0e061e1b090d0606090630020609031e0c01080a29012105150901060e0f150703080115050406020c060c010624030606080402030607 65
    0x1500d4210340260200d2500807001904da042000d00300c213291101d9404032a2a0481c40b0307034008404a0240408115004000d091204100015940e10422100482c0c9440c400030801000e2601c2c0040005985c1c0c43d9070701860a4486440d0381075020b1085101080c901c21002101c2400150070811410043c0380c408010a680000038041d030388441405c4d03840454207e404410403025030410b01e00720b030301341d0383c42900b81d64440e20008040000f0003001d031650b003079551101c1d8061a03504000c030030309401c0c3e80100701002000c00c40d841c524150260400d58203024003002d40e40344220103080d811020484c0ba02e052541e05a40b0700b0303600d103203003244088200700c001261209903540180d091108810b0305e80b002c0004042d8503000e80c0341c1c503035903501d0510001075038500802c00300200802070005100295004c034900d503416108607802921201e26800c8140108140c0d4060034009840c0d600303083c410740d5068011140303503401e03803001c211265888000391030621007254000c1d810f03007041c8001580e0502030740028112 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 457822562 1250 457821312 457821317
    0xb01050f0109051002012012070c061b180e060310020706020f0a030902120c010516140105190501050301060302010c0f0c0b0c0f070816060807050c030427050114060a 73
    0x38980d88801203410710800d01303040d50041c0d451b03540000d9440038000e05005e0b0402c100d66681e24264440b4400c108524000d403102c410001e1300c9022406021482c0c01c207210306448280c02200c022001040a0814100414641c00580e01e043c400203001c41d2004199101c1d54019001e0108100d01d000b00c0c200952040c0d5040341c94a03802e01161a4889544c03003d001c0c10009903d0006116003d4010856243c0885503918407a503c12800d003c0750380d9220054803501500d149010007100000d1500c8001c01088480c501441c3d8070303180800452019203041c00000080145040003681d8880c02410b00369085030001034003213800b41c900300002402070041c901d011030182d4802c0003000e40307503902100308c0e43c000c2c80540c0d8607602440011511071414007440004100d09002010320020120f04116100351034030414040c0100c420018045602072411030301c46052680c162a9256190302103007494503000c1000003004507606103040c40b1281a441014142d841d5112404203c541000c200301442d400b0b101711404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 457823812 1250 457822562 457822577
    0x61005040b07060915050a0e01050402011b020112090f0b010902030106021207020f0d03030605030106081f1d030c0631080d06050405040b010e1b04051e0613140604030b01050f01 78
    0x12420008060340401071741200420941014201d003c01e646005072159250f924110a100050380c2020b9811020202000c000b1440350141c001031f604203a00b224070030149400e00b020802000000309180c41c816103d041b020120f03903259545d10040b404240106405680318228880003441d0361405001c1541c40100076207424007905002c10840282c0d42e00c100d010039241c0500b44172918081c002c90000c0c0c0012401070040c12500544501111800d01030b48103c2e5a450b02d04000c1c03000e031114680d5098280c602101d80c0c031084151116902e52040300d07920f08100c0110032041400c440141d90f01000c050031100040c185400d80c03910503543d4002000b0540b000e59540c400199512540103140c815806950581c001c0c3d032510081841d00c400040944110003a000710141050f10490207903001c0c2d400c01d0700d0300301c501c0c6d0100441c03a01071490407083c941c1c444000b01c0d0502c2d03200024500d10702a100c00d000d00c1859248914140100b900484c04000e2007018202c0042c405030500e00c80740341d04c06e21705162850703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 457825062 1250 457823812 457823831
    0x303120e010e2802060706020903010e0f150a0509060708070203040504060305010204030506070e01170417071101020c0a081e0703061b1b0807020103020c0a05030c0a0209061005040b0706 82
    0x2400c540c0b40640c000c1c15904804511609004214070a0901c0310408080c0503540c00143c0c005100c03071040440c020091507000c100b07060561001d40c000582920081d00f1643e01628412803160344e0002c0951342c0d80c0f05026240052201f4803140102c0e4020940c03a07004001c2521540c00985003480c0082101085100c140000501680c684c041c0d07c0c0114001c20005070749500b18100a42009001030040081c0504031201d0800d59a2000801c40043d540708140314068686142918900c0303c031000714900c801c07000c00d24000f40242d100304a60502c2d0246c0841c0d8440403000180415001240711340d002035007151019070045d00204004002d103541410035606a19200c3c1d42d0f01c0e0440d2910103c0c08101c0c586003c8801e80700d0380110b81c02069680811180082c0c070307515620010b1034400d0100003410190040b5050403218000c1248051070390748001983d0712034107640b604ca5942d40c42e05405074071500050b408203803642011000d2140c0101c4e90f640e2685414140080c103a43c951040c1d4003101c40e10b50710160074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 457826312 1250 457825062 457825091
    0xa0504180902100903150c0c030c06140a020c0606030106210203010b03060c19030b0a1505070b180c06090d060c0207030c09050f180c04050703150801020a030c0f09030312 75
    0xd120303d062a155884001d096040134400c43c0c1e00500044045031811040c40c540c00d42100c0c0c900002c0f58140740c0b001d858019847c0100c0681b025401c071007250341883c070501401d104541c004e40303075112041007115a150f034ac03c800c1500361440381c030615000c080294143c4d40601c84a01c114043c2d0b5001a00114000c403c6601091514104807801c8501d0080810800c0c0c038a09056582c0c0f420b40c0442c5410b00c895201e0340c00144040c0110300c9061842025500440d6620780604162a000340e084004d80c4034a01d800518500c40511020518403c3e009030342068000d440c000c1c06544812001504181003011540d90f04002018a00e14072801d43c480c2980010000c2c04148840d0040e110600012078181050380c3e2444001001400310800c0180c41045a50b4810380081c2183d1319503003c0701e020900d0786841909800500f0000c2028000b401241c02c040741d8030205400420760102140e40810465051410498010900404900000d413001208002191040020b00c071481d40c1f110b0300085d10900707138095 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 457827562 1250 457826312 457826329
    0xb1513030c0b0d15060215040c0b07060c080912160c05060307020d02010c080603031206010e0a0605040312030608030d0f0b0a27060b091203070c08031c020a0504180902 74
    0x1000407141e00142242c008005400355185521404d00c04071045402c00e00702a40f03a0241d1400c620065146000180511110b41001c000406620465560303802142c2031101c00303800708021072001304942c1c0c004200c2c1d010000404140c25541c03800540e040507115101c0c0101c044020304181c0340c00501c00c6000c00c050b80c0d4500114041c002b15001028102c0c04100d003e425612068080800c1c003c2c0101084910b0b1000b0044400c2080d142c4200c0546030b0340d841c01038030b040350401135142e0884044500440c2d4642c01400401c00e80c0d018084003105041c1400c1c044069030142e01502c216034209002035800748009030807400b180752411901148010050740030590b4000642e005403640b41c1c1c85801c0c0e0a2140055114561200ca480710600105041c1540000140700f10011030340180c2c103070490300ca0030341000e10541e443d0b035134004e0a13400309641e503030011030396504942d084c0070002460313000360204200c80f4070880f0302e40023140c2c58180c1814138029070414a4008070815102c0543c8401d04000181d030340d0b560 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 457828812 1250 457827562 457827569
    0x80c0103110d32240d0524100f05060c1009060603061d031923041a04030f11040f110a0e0f0d0b18012901030b1513030c 53
    0xd0b000e0031042c0e904020f0b243e24203281c0c03540c045444105020340c00c0481c1803040c681d4042002d403c0d8041d00003a020640b0600d22040252144c01401348114242890041c03100f1441d4805002220503204c00403040300004071442202220110a04100000c2c2403071009420440b010034150f1301c50b03d69200d00c0506880520604540c000c1d0f8828060040160074469200094880c900704010707441075040d211380d6482004410244c0000b084034100c1c2103407048001598580200c4a2007007410703001c1c0c58403001600140a503100781c4540050300110185c02d41c09076000c4135006407103124142c3c5036890710105070030091090740d045500d500e50044191514040c003030200d029190031a030b503040b00750401080c180d2001c0340e0070302c996000c19003801d103942d5498220402d150040c902c090192a5030301c41d5a035030540904018895400c0000720b4070740c0c07403094a45002c0105000e0314410b401c1404401101280c80c51450144e1003852401110b007036003806009845185001e012030190543c4a1300c40f194130515652 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 457830062 1250 457828812 457828841
    0xe131403161a0a05040f02040f0f020d020d060501080f19020903160807050402070506041211070603060501120c081b090a0e010f0b0a14070c120305030906010b04080c0103110d 77
    0x2402c0b0080003006241c1a9006030851070130000d509041e659540517a07078540300680719079150b9080843d403d030280e2110301b25100d12542190b07038a2081d86001d000e03405c4182e0000c005031a260700001d180d4000c40c2002c1c4103000944545d2250b40d50904080080401c07845601500e640c03d01501c0c4064404100403842407000d401c011080610f0115040e03c0c221041e000a0302030340c0144001000514009869a00103134450242800da442480040301d031801a40d003551240d115066000440640590040c1d0596038207a881e20760701c0c0031165103507040d0360109000d000060710190000c0c3c40b44c04400501250480008489403070043d42c000002c48090300394001125050400c0c004010780300b41824580010b007141d00d841420a1121003026140b2080c1e41494650715200291300006c000300104d400018140e4101ca007000490203080003445500200c90b041181c0c80b07035100108903445128180d50450b21540c0082559240007801140680109035480920040c00d01298000c0c186074041c280c1a8540079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 457831312 1250 457830062 457830083
    0x32003070c15180609080d1104080c04020f091c0602030117010e0f0c2101021209010c020f060c160c08010b0102070b1c02030411100e0a0e13140316 65
    0x1424003826115403010084407451808503901c1c1912207018040d0315403a013260000503d40c02c203050000152003001c128010807454151100c140e68070420146c0181c42510003100c01c40608502800b080348291065400c540340184441c03071507440c042d07026070071100b00c0750000c03440480142d5400c0180e0b042030700304041056006a044011810922038601c40c655610001c011407030007884925102d6880c0074070706000da00088501d01841d0a0f82c0801b00107a204031000319500d034001c1e0420b00350781c0020394415100d5420701200e400914070004e20304519540000292901c3d031181e00c00e00e4500e80c0070b03001c40d00d0030400e520080700208900000c801c004203616000858034840003000207041030a1a042554042000d001c813180b42040800301c0f2051401484c0700507541d07103030f506062510b0b120380c280752588000d50700300c0c450049502c90940300e40e1100907540800741d5911000e580440c5001200e22034907200c0710010030300c0820300242103070f400d24981000b40c81c40d0000032010159444c14540085c0c0d03010285 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 457832562 1250 457831312 457831337
    0x70b0604110d142e0905071e0503060f061c020a120906051b03040b0c0304080c0a1b052b2a080d091412030f1605010c02010b06070303200307 62
    0x1902150b44128998800d07001c4003480301e481340c22041c4404d005800580c1d6a41c800503a4250007842d14162600c02140f441c06000c6800328020641d84c000c940c10750040e00c625a840280d810f200c8250340517a1803110713051944143c01002c00d0000d4000010403070030440350014075110f0200c00d100e42d09046003d0b48001c100e0340303030011480511400c60500e06440000400400000c03440c07000b800f50308143d10003221a66601d4908111605020b052024a103a02456040104100042c1c0201c541c0000c01008046040d9903403013040568002d04510301200744c00d030b580129014010080c0202c01c50303c42c4400441300c040b5065001300c600c01030342e000f001c4522903c109000580b002c00001d96442e03050700e406960b0604005130f4001c100312003100c0d41e000316061605911400401d205030f5002640604105886181030010780d12085084c500903030341035113450071451140d8411f000700107041e00050061890301880e0b40c0c04130020241340243d80741040e00291602c21442c00800154012800ca07550000803401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 457833812 1250 457832562 457832581
    0x16030b0604050105060307020618033c0c03180a03080a020a05010b1f121119030e1b01110a06050a0207060c020d2c03070f1a070b0604110d14 62
    0x107130003680c0701e220140104140306500145450740003141d2070840782c10781e030000c004918501401c11072103924800c04202c950720f803414100c0d120403a5455a040400f503140d04180d1707402c91041554130402d5810800501010341800881c2c09110100501010307801039481d10f03140100e0704001d0040005801044486062003801d0041d04800c0701c088404084803108540070029844103101c2c0301c0b042c060006a44003040300c1075406080440038910310b060350345003441e4051042424401d002c1010920f0301800b1f1003c8000040d1606c0c8424090007100c094082d110010f484000a08030001400d116034203100340092501d010315402004000350168841e092441c3c90415610024841002c5621001d00d900c8650340c0018030607240c9041c900b0b0304903a0489221741d00d032034100c1d001c00e00350140700340c810000340c003e80388401d01c089820040c0f0f0001801344c4000d00030320328411820040c0c8060b28240107e1628034150348606090802e03079810b10700d841020f10485c4141d4002c170305000e00325548402004ac0c98070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 457835062 1250 457833812 457833821
    0x302010509060c0c060a0c030f05070e10030e060601051303140601030c1409010e0606090a03080a02074e0605090f0114040b130507080a0302160302030c090916030b0604 74
    0x145007906941c14404401c2c41305680b00c200400e212421a15158071103001c5000354065072340c007004144140501d00e840c100241030186420340c1c9500a6020306000c01101c0d110340300d400e94410302032014007050b03115100112844d411080e0100c622090f14080080042d80340c0300d6024030708400901034a00d0350b00d03600f441c805803500c5034000d030414016400c14061583c0c40309007a9066401c140038507440c0ea05c0c2e041c0494a2800f5481105800502e05040401480644030280c80f903c00143d084039061070b26800200c5e658248070000500b405072440c035034510100100202000100c4000c140c0d0007080614000010051807684142e071807a58413024443e52000034490945002c00d840020301c0700442c13564400c0140080180040e02c0d003040d00f00030804410381da9004080c580d40104c1211409034039602000c0d182c500c0788000328094032030307040849103404015828404a0342c00038040c2c40441401402c1c41b552003030040c08902140564000081d4075000701d0b02d0302d0007441c06101c1c0e609043ca814002d020885 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 457836312 1250 457835062 457835071
    0x11422050a20030a320615041a03060112060b18030304080c0405190207080a0e100e090403020115060509030114040b040813030f12030b10120e0309060403030201050906 74
    0x46a4014002c46500000c0c421a504160308160004040580d44038440c0308080b140f03034044481c507518600c0112242203c070484e0080b802114480c00400100d0800034003403040303105942207140150f5042c44001c41407030207541d0040301814030540461002c0740000c1125890b03040003e0300000410880d8609940015016403004280c0c011841c284c2040140c90341c1d0f03003102503103610072915000007034403080056500c07144001a000e0295261a254a00180c80340c2041c9558400100d0110b2011240d1078822a0a94201240d8a0b401201a40e40c024444400e000a1007035055640710b2441c080c400121000e0000100307020790305c0986804402c1c0415080d070301091800401d48480307005000100e00005602a00b1a90006110303507034500ca020001240802c0780d0001e448541480181e1081c4009008a80390441c00d5540400c0002256401c2000391148401d0000c00a0820070000f030212a20394400f01203100c0b204200c1e400d060306500000c100c0c0c1c1c840d810880050351034105001940004000c0103400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 457837562 1250 457836312 457836341
    0x705070e011403010504210210050f0103150501060503150f2e1e0c0309030501020f1c020c0a020108060103061214010b0901120f060b0402130f050609010503011422050a 74
    0x2c9007840c0d05c40d41c01d030410902c81e04d101c00d56090552101c0348c0c020000003400c10600d400c207001c1441c2040303541e8510724091105807000052040b080383c1c82009440342506851081d141c45055480313003813141c2642c41d0001d00964200d1003011400541d55501403a880b100761b02d84000808580804aa04d4207001c1c0e03003841030701440030036001c1c00e500c0c01d0101c100042c00d4400c0c5ca00222088082c0c102250701445907400905194400a0400b02c7c0014500c001c0c0742d41c1000355851b507001f4059402d00300c02c030310840721a200141c02400d8240010762060020705d410810507d40440c040d0385a0040380d01105200b07070304461072a00d07104644042c880c28025001c05642c02c845002c4c40d58903008507034030032028101e401030011007410091010015650b000300144d5002030011034950280c804500e0301018180903920501113101c100169a207001c0080324012a4182e4030181541d00c0d06205044900c5041070641c0e20101081310012020030386680c2041d024840500850385003801902a8100d96a04030070411 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 457838812 1250 457837562 457837571
    0x150d0506160203180607020d150912110d141c05061e0d080c07091a1504060903080309030903012307090303051c0e120d05010509060a1a0705070e01140301 68
    0x207084002100044c821200341c0d1010750780c0c03081b4800901011400c460084c0801000494485018890b5104a500520403040084040003903d800d80f20325044003c1645640c0c0540c8104070060f200b18184000081401c1001c2c1c00c18a002107408141c444c1c175804680356954130000c1141a191501c454081d000d005092000e030f10346010085010700e07140c03120151140d0000220340001001c1001900300811800408108904000c081507072030641000c0b140d0700c00c1494006000d02210004111412101191185214a89150740d480340702e800007005030b0398a010900250000e500c007800741800302e882ea8240d068890107001d21031804d001020b032003001000032116083c030000f0380000841c0c6a9114002c1c0003213400c5d03058101200038200355a828000d034011481443c000c0326044005d411034503582007003400240e0300c500501144500807900e6030fa2000010344204002c4100c00000403604d41c0d00200c0d40d1810007e40c80d22850035070260f010002040b980d000402131a00701030000855213008800920 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 457840062 1250 457838812 457838827
    0x110a02060c1b190203150601051611042408070302012f150a1d07030609030c0b010f0e06030d0c021009081c030c020a0803040b150d0506160203 63
    0xa64489005140703500c28040041c41d8006265450b41200942102034112100385101000d440b0240c3d240100c100d01030302c1140907007400c1c0c52042c00d029100701e03810794800b8103061050b111070801d800155420382c1c06100c2c1c10f404007001e81304c900807809414401e81451440c00ca1b080c0c144065014680d009501c29008400c040c80140c1c0e0088105145d01c0d40002d0211000105c554003542d80c410f14040c154440c4520107103030104018841d000c030300c102c500000400c03050b40950f10310321504a03400d03250282c1c3d822009040c000a0420f5200c0340030a4064078100300400415540c8600d074060a800c510780b80c40f485081003080b011103010480d40120140c0207001c03081202403018000c621529402849103210485d400d8407544140d00150043c070148080b210b89014603e031600348842c0420030140001d0416852a14007400001c0c401400341d0b0000740303c0e1840d0b1781c03500d880d0740b41c1c80302800031501c404040005a81a076a805540001c03140a10080e01850401c0482c41000b004c4800342c80003550014000078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 457841312 1250 457840062 457840067
    0x90a0c121502030402060d0c0e010e03010c02031e09120f1c05271306050418030c11010207090c03020d060e010f121a090a11220b0121090303110a 64
    0x110a070325040980c69841d07a1000480d54000c3c411040b1004d890100303c040c80d00e900404541c02ea103800e803921f1901d40460010f00d800c0c0c43c146a000000742e4400c01080740da0110600c080c0f600c42d50b518004500381014500011500f028405c031148141e848501191004007003031201c18076546070040903c0d915840c1140162180c0100c2219a050449030300c0c0300d4032040000301140d02c0e150030040c15110724075103910300b850040001c0e0140b10f006904d01a40c40c40d803080000c0185c1401e0b40c040e1280e540f90501039450030310700c0043c0301100b81180a0303540e00041910030390043c0800304d8016140540c550706810008070407911150300604103220030340010400940c500c07690038103465481c4460740300e03550315041580c100c0c3d0345c03c00b004052403886410066003103001310b0040101c44c414010b007140c1203d900c0810029641401400045140c82e0030b019003200b90a0344040e6200c00c042c1441d480101c07410300f9821403110f182c032882c00c105844002d4070041540c14031402c40d10260155000d4288050b41200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 457842562 1250 457841312 457841333
    0x41401030b0709061d01020c040c12050c0403030c0803100f03141c0e151b01060501081f05040c210213090e07030b040c080703060b040c3006030b090a0c12 68
    0x881e10381074041144000303e1b0b4824022101c83d614050028014440e140a004058070b02c4100d402c111103140c140402c2d85410f40c081101d04498059492000304da00030b4590440b9640702520703c4940800d400740c000386400b000c0782681d0080d801411003101400e911403040e401d05000700908030301d0107a0b08465525458003c00c1a0044a00a4a40c4401004424078003c0244a0000090440214030509841c0c0c41d20540090040c0c40c42030365803104a0704c603400c80307070f4003034041303601d2150b401c0401d040078401802c1035442060310104034070f007868802c4014010a000c1080343c450300303004582c000a42d1742c820100c2c14210001012071a0f4100400c041d404102c80d00d80c2d07100d000c002e00c1e0b505010042810b0000d0113803680040d00c01c2c10b094486040d5a4130b444802050420310540c015400c007030741e081c07141d401404100041180380034203a00c480313060740c1c2016840d800352482d09011a03540d4004004030301003140e864410b8904c0c000520b00070350142003841d054102940701d80410205105140002588400c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 457843812 1250 457842562 457842587
    0x40b01050f131a0406092003071b1707060c020c030d081605040807120201120204030f0f06180f1a040c090b010e0603040f2f060702030c041401030b070906 68
    0x50020384656000307651250090202c0d4420741c003905020340860545200d910112098007103201f08501d980455402850902040b075410000c0350b404181d8118040101b030304510028400c0008000421541e14941c640340c010340c41c1072320b116a560100712072312601000500c1c0b1700701d422401400d458500e03610052085600400070350070b14550140c80c8044a0064040e1ba02600e03420055400c4903458001d810034400b84104240c0c00580c120100084512a601c01c03601035a8200d070700c400c54100b0a423607600c0d94051007681140d12070350b00c0e9034500c8500e09086e03c417140f60380700b100b4049450f81141450912540c011000e0149180305100740000104170b0250b10089030b140b5980441e20410000058410300c5419408a0300440008100010131a4400410b1400f0b8403070311054036060140f615202c1000d54819071607400d100703a980e03006068500000544280e500c021308845000d692b07400420140c51040c0b030f4104000345d000c8014420440402070450b48004580f41294410340346c450000d041c03800064 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 457845062 1250 457843812 457843849
    0x60e010b0714120a1805060304080409021809010f08011a0612100801090b180c010807030b0402040503030c0303160302190e03010e0607080109060902070c0e0c120f040b01050f 77
    0x5448982c0900d05000c0d55050b0404100003e4550140201c09810f212203807104080d01e051660001c03429180071700941e40140d0b04002c60508003810030a040009502015000c100b803820010704031b10301d80c0e61070985800303002d6140c0c411007054039080400d07080d50718501600c1d410108829000845803a040140c4044090000b40044141c6503908506407564064005003029420940c884090100b1003102c54020756110961350a95078184001e2511003801042403400070f606240480c2c441403003900910910b80c401480146080d540303400207491940f0010007158250004010810509600483c6440100c0e15040039886c0c550307070303080c66040e40070241146400d1180e03181e541480d540f825445440340101d6541101c1c483d0508200c09045150244034814000d0308051001c5003200d864000c1c2c0d821b09078071401c0c508060303080c0511183c032030400920103c42c1c001d09100810100041215203400303408d007404003c0e543d04040c08c101c1c2040005802c214094501189411000c0d1105040048030a1022 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 457846312 1250 457845062 457845083
    0x109081c110d0c09080307110108090f0a06020f0c2a19051507200a0504140609090a0b010306090b0a0e030a081801060f051306061d01050922060e010b07 67
    0x41c0c3c420360700d40c41c46800c01040d034800862064100303c5c000f840004d15400907210908035541d19611250707241401e04094140340c110749105000941c444d000b801500800d040180d052202d9140040e00d001010070342e1100070340d40c0380891600c00043c1210a44ca00300d040d41c40510703402500340000c0c100c10061207614054145056182e90000413401612469036102c3e034100e034000d1066080c821175a0405000602c1401d20240005062419202d005c03066100700300031030100d85d901e500b009202e00c0c00070302117085070144000c008009000e810741540a584504400102400d9904048a06039030007001001030341d280041294103400c0000603150034036002d140c8103181d035498039500b141c6c1c0c42e079042940d001903090540120382d96080030b8040d000d40340d05503020181d610260342c5031015681e15201315004503140d03020928440c884050303100d41c03640040c100302c0d145c4015040414020b880b03801d002d0f8518031075104207502880b0315008003001014a03846400e40355040c00c811214510400310010f1445001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 457847562 1250 457846312 457846331
    0x90f0506030d2615010201050619030308040807080304031206080d080a0b0103060510020d14070308130c0f09050103031b0203031b1014070f020f150405010e0109081c110d 75
    0x64803c1d01c0e21800c210b0000f86141000028a01c1885400e02c5031809542881d002a5250034024100010404a040c54401c1503145480039148618040e100ba190307000d082000b44007103004c1d400154021446544ca417080402d0008064084031036a401400b610b40004e100018600da004804607001100100c00144840e00c503c016001040070f070340500e41051b05d909850002a33008188401101c00a84843c840c01510a00144081c400e5600040c0420030031004601085e1b044201c0001c12440703112401a90340d01d0318030010200000ea44500880c4c0d4880d0014410950701008000c2e801c02010340002ca185655400a626070250700294404010005c0304031002020410980c00c00c00101d0904000d140c0307030003031401a43e4004070359100c0412000245040340d24030008401c820000c1c50000340284c0c4a0350111034040850181050326207648a09985041520a00c2045a4107206640c03d55a59800101d5203417076044143c50113101926048011513200e010008a86054585074800605903a8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 457848812 1250 457847562 457847597
    0x31a070207092414030d03021207050a1809090c0b0703080109020901030b0901090f1112010b070606080114040b07050418090303020f0304111c050c101e0207090f0506030d 75
    0x10311100000380454440c000100000704c52515600c1c4082a0265404071421318070640607449140d01c03900002c100300000450f181e100e40c0203090a42010319052010031840703140201030481e0341c4c0001108980d943d545508002d02e4400b02d10041100094007818040d9940300542011014422007841c190000f0301420b440c1c1c400d82c021181d042c4028020002e65841c0c0e0b400034002c0401c5c04007030080d54640b400306048048070109803100030702c40302c40d58040743c1e081070460a00760700903c030308913845c9071684004070380700d0028042c40a03109003080290314285098280703100407d00150840044c0b142c200828000045000b28001251102d50000b040e000002e02c0c0c102c000f4401e0904500c0840404010300c02041041900c4081603134003201c6002c5444544140b8030025070103800000d103e0780c08850343e181c49080c207030383c1e48000d031419041100940c40701c02d60ba0f801d003500e90120400143c22034601800009801d204440400c000100c08110608e0f10f41c011941d92648645101d041c0040140316280410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 457850062 1250 457848812 457848851
    0x405090c30060111120f040e101203030f0b0d0605060108060a060c0314071b140603061003050901060b030c07051b060304081e1908071715040f020c07031a07020709 72
    0x110a80c00e915a11001c0006c3c10503682c105004c1c0d42c030025241008030b0440003a5046a009030764505014001b4402070340d8013540140408482d01c3d0650b9220010300c00995200d40108050038010700b0085260324080e40014040000100420b1043c40d88031410700034250301841000046a05080c103a5a10051071a080e0b405d000e10b06000f001c4d000304501a00c0e200303e81d03041b114116031001c01144030a800740020400b043c0001c1710003541184000d007590079817910070b070007a6410540c2ea40000506030307101d0380c000001c0d80c02218450a030040000c0c01400b0400f040018100b000c00507407620000350319000014000340b0002e400a4a42c250204441e6001c48641c500c410f41901d0764182c5507503e410480d55142c8644001c1c0d0500e021841080c000388072135000302442143e800c81c008207020a56980c20500540312080e09409170002d50345c0d1a000b5044110b0f200030b143c41c441d00d0004081092543c50b140350032500740520352000442d0f1100348008290005005000e1ba07008020100c0c0303c0e102d0341c2e410750058 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 457851312 1250 457850062 457850083
    0x703020319171303020d030b1804051e0303160311120718080d0f051303050a0c1403030f0f0702010e100c0b01050d030c0b0c0405090c30060111 63
    0x1c0801c190001d4100c0d000422001c0c0701d03500c520400441d984807200403400640d200400344c0960407400c100d400b0b103442540a441d401c017008050b00414a04c1004003100c0003400c0744c04440990003d41d0706d070f1903000103440011300d01c052040114694a0800082050030941c444d01006140d201d807000b01e03004420805035004040348618072600e0789401d1000a09503200d04009a003c141100c20114920700007050b40750948140f520b81e6081d214814008a501ea8845849003002c00c40e20327900480001d105101c00f4002030701400c443c85120b428a184040342000c0740456a100b68010400e24842040010030341e40d00302603e034800c0b600c410050005031510840e0428440c2d00c040d000d24518031403600164000c0005000702451200c6a803100f090018401c0d0342000900030420510003800010900c0c01500c0d446070300761100c507040c180d6030404680004026641511080b07000700d0081c500c1b1003614240ca48180c4841840d0002c8914821622100b00e00949090304204450807051105441000a00b828 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 457852562 1250 457851312 457851337
    0x15031806040503040e06090403080f0a020f1813020901021902040605040203040605040506011403030f0f13030f05100b01050306040914120a081008060f0912070b0708070c0507090207030203 83
    0xe4074141c50410384913407080c0140c0d006505a440131407600d08240c04498412545911801015100c0b0a201d001c000c0c401003070707807503140e17002c11000c40c0640700d0b00d0161100070101071164046181941c2000841d129203000301301490310503c0240102d0b82d000401102c01d1100100002e02c00101c0c3c00410050000e9800080e00540000709010030400f203030344403512881c0904103841c40b40c0d80340c582d107940d19000d20115550591060101062070b900c03000042c81141a20003181d072500f02e0200e4240c43e2045942d0083d240c00202c030914105101c400d100407040c142d070b014000c0160818510018026000140081c0e010b2951000c1c00c100700040c4000f4000f5003003003a003c507808185079110584140d0b0100001d1000a80110701164401c0002070713019080e40d907030a015204e103030baaa80205003d0301004000c004240300d072001108e0a100b60300c0007081558019085e1401614003010080c09006001e00380380e00f0407194200034400f045021407801c1c20b0341c8004001507a20101070808a255014450301d1045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 457853812 1250 457852562 457852573
    0x2130302010806030604081e090a12060510050901090c0c0c0f05030f030906041203031e05060a060c150b1c030306150807140d0902060408010f0e0d0504033f1d150318 73
    0x4601c902f0400740741c03816100342030501007951451280f4584115500c50650403001040044c0300b100010303004125280070741d00c2c10039a60900c82c0c4134031683c22003d81c022880c49410102c144078030b007424004501c40445010040d4500340f6541d000c84c0842c4201e00c209000d0010902040d82014420380016150984803261004211024080200180415100984140c050b150002001030042c41e10b038051540000e0102e405c0d40440003404040c044040ba000e51203000310b48041d0030480403c0924800c14061f41e00050f4190134001c80f6801c218008044000744280c190402c0101a400700720303d1b04804554552944924052074001e0240030199002980600c001c240811800e60542c030103120404403c909100b08404a081c1607207450849080c28001034040100f80007007078810320000b9000340302020001e0380c4440c0e405006215150481808041d140c150701e00d00200364050405407540c0401c0a00000800342040010598440ca01800050710b0021000511004011201406c0703803070100c00350f44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 457855062 1250 457853812 457853819
    0x2210c100c030f0b010c060906110f070b07030902030d0c0c090911090c09090c0c0a06090302031b0d0c1707080c160b03060d0308040f0602130302010806030604081e090a 74
    0x1400740c4034118400c80024900300e0412210303100da005400700307444103844012196800c1d031076800180890000a60f050b9032140305000d0010420802840e00b40010b1490300d44070102e13881c24412034031010742050308050405002c4009a6000700d4541c0000c88075040c05550b010152070898240c2d6401e5100d03c0041c0c0c60100e1440500405019600d40d0ba2400c8070402d00c2c1e40e680c004c0481003406480021500802500006460115140d0042807414400d10485030184c2150ba50300c0140d902141084005800c040303800512900d5019201c421200ea840c003425440c17a0108000384100c051400103840000c0c0c9128104040301410220f880d80e513007150701d0690b513041e0614600e0b561400100d07080720000f1001e00c0010354541074000eaa01071350b402490640c400300765071800c440c608405081500e00f428580360400004420384000d00301802d00351180303000540b95000240090740002d140d903029410a03400c010010300004110380c09c041c0020000e907400d031529001b41030140914450b20f030b004100d41c0800f2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 457856312 1250 457855062 457855093
    0x1060207060207090509030a050a09030204091406100b180a0e010305150c0301051f030f1409190c0e0c1e0414060a08071d0307030f05060f0702210c 65
    0x5030240c031000c2d02180d12480d603900e00703103088076800c4800740d8440d00309100c01c60b902d510602c001c1400403524036100c45003907100d400040032110b1082e42181e0264a0b0791045000342020700105901c400c0d020515011145001405011842505c102000307515a00d40c6c43c50141e5900807009000d01100080c0750346942e161700d4034070f580c3d0903200341e41110205002c4c0081c01e41c02c3c0c1c101c1220305a40002d0001501c1e00c3d0038650704d80e4200b0844030003c0030715890f001c0c5404400050300c03403108a14440403021000e0b08045090a0078407210082d00c80014004410030303404119007150003412201d5207080c0031881d030380d882c030324103c0c60041e0201d55401c880f03080c03000c050301e01c0e0a4000c1d0003541c0702884250a01001b103000c1200510850405101180702c0380c0000b007250b03014482d003601c06200c00044401542d030060000341004100d81080b41c1c4c1c005004a80000d002d0100150b1394444103c8020b034801e41400000a580c88620082024080c1c2a40d991840c00031248002e54204280c41c000b251048103840310316 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 457857562 1250 457856312 457856323
    0x4060501051c021b1b1801140103050c0c03030a06060807020a0b04140c1009060e09160e0f060f03090c0a0305100506010e1020011a121204030b010e0603030a0e06030702070e010602 79
    0x1202d1141d806d00e880803104503a50000641215441a44000041407550054000d030200505804c5014400d21450405c0c075420b10045100f61008600007410351700380300380504002800340568085500629034400025001d0701403503041600100744c03500300c0c4c10f404c0c0c0b03e91070b1034402d2294940080e55841400e6989820541d0403080d1507150300d840e160720050301d0500244060489280428010003551030f010300380035681c1503040c0d020140c1240c024012150104007030b43d00100a4021102d0000200310206000380800d542e5440c1c11501e03400c09902d140c03107007603481d003184c019442c5070742e0f0f03c02c0414240c0c5e00409280341c40c2c05000e01000b03176801c05010060442c01540c03411b50031034120b18182c05803130702042c4144030400c61101100101191128244207010413001103c1805224812040400e24000c90250006600c12120350a056040075000c800b11200a0042070080c1d0007401000240340d000445005400819030f00d0540f82d0307440500807864522581d100003400c020010010a50582c013049 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 457858812 1250 457857562 457857613
    0x804080105070c022d1c060f06060906050f070204050a050421050d090302030f19020f19080304020f0406030c053a02030312130204060501051c021b 65
    0x20400390b69503103015100b07690640c0009611501001e9041809100042c203c2d2461018042100b4203210900108141e03a203030706810085540e0103840c620420825004d600404064851b041c0003580c81c05030090071404181c040d2100340070011841e00100c0000c40c0a94000c00c0d00100288200d0401c1c002c0ea43c02080c043c0e4050326410301b600c40f6042e47c2c0c86220303400758105c0d4035996034902d0b0103030307210401d0f0080049500460071400304000301d21201201c80302600c64040e0201d055260740a2004000e440c20803068501d45664000c000b0b1020f56008804504030002d80041d60343c2e03503a544510000710340c003043c4d41003981e00615001d0013006204900c84003205a844c2900d41e60f12111200b890011141c40e002c00440240e803482500d00000130041041c5a4287d101504807401c1149000f00034480850032104124107a140444450540c50305000b40d100422080c24242e1820400e1788150074114030240e0118205500080c880c1c5806850342c484440b80460841560612000810b038100784502604 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 457860062 1250 457858812 457858829
    0x82206021207050a0c0b060109030b040b100e0106080a020906040801021c0612020a0b0703020f100b01021504080a0f0e3003090d0f1109041401060e100b250804 70
    0x100001c1ca95406101201d0040005403100301171403109a8504030740082c0100030301c1c104950070900000087c40710f5852070141d07100310440c0d0039038941000c244c00702c881c690b4040481500008010800e683e0020602034220090350b0340503039600001804078480748039079444480d056200144034200c800880000d001c24103980d40e800d010256a03140c2d26105072800800280d07101c454900c0400442c280d040007440c54600c03038019203071260b180420180c10040f091684440081d01e0b0800100c032503070706100c0b11541041c1d41d00e402140d0704080d280c3c41c07401d00480940c0000d1110f9803c03440c80060050b0300c0d51000c040000e11204480121034030801d06c10010903031649801058442951880328084150380031740e000580300300740356015500c40090554001c02c0c2035035011210400700b200c588564075072910540c000d070780500131010845c00031030031134841d03a01000701d0350b0480303041c0b2222101c15600d1600b1542d107099041d844940390301d0300025807201801800a134480c8400c0307007001c0203887c101501c1150001c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 457861312 1250 457860062 457860097
    0x10c03200901080a3201050108040317060102070b040f05090c04030222090501050106090806152202040801020d0905070e04170c0a020918010f0e0304030308220602 72
    0x101500502160103036880881406004055440390310400d07480f202c0101e0109500115154424101030210308811103404950f1554410b0030b4144082401000b080c64019124503140d100100f581303140b0201444030641c1e903070100380315078400c0001d50042e002000c0c0c0c417603882c1c1c0e0f20920b012040d1201d105403401859008000755240c0c01e0701d0141d604403900685143d040c90503d1605c0425010121100800c003607541140c80302045007403044501038001516080d000300c0c20100b541e80381ca072009107650a155032206001180752100d0301c54034600313150611040907a41094a505010b07020366007005003290b1010801e08030b10200c580180ea0424014002d40c2d410325101c24546036545801c40e00508214615188030300014203090083c103014030310500352401c10610360300050355a8415141d21114004040d01c071a0449801e200da01d0841548050801004034405400da4881c0102e120180078402c003680000c250038240c101d403040700c0c98000002a0403074083c1c0340c000700079082061040f440341d481 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 457862562 1250 457861312 457861331
    0xd0e03041505041508180706020a030314041110020f062a07080f18030609010f0e030c0606090604021b0d030501061b3017090102030c0f0304170c010c03 67
    0x180b4111410342d5016191003001c08149541a00c0c20f0034040c103a8070740041c0222070408050701c14171812018002c2d42c1d01074401240c0500f00103081c0d03000b0400d0750569112060501000030400d421510403d5030550b400c181c410451202682405519025850035029a20410040d0a6007610307040075000c460101101c82d0b03980030340209145c01840340013080284208005d440460045024001c64160703504c2c010302e0300c1c51040220f410700506a445100030381d1108465003125403d4082c148000f91700c0e000442c01c00d402c02024a503900000ba0060303004a4003076021071201e07211601120500c003100b20245603000c0e10004032564800000c269100000d2600c0008117800d48500c90180f0201030190104041e80e000e600c0d5280c8100d8084040400f10810860513202c54840424030320340c43c403940d01c3d01c4612169441000b10501c0c001007960319682d10410070485e075440030b54151011000c1c940380854aa5560b0315014500c14048005465481000314004103e1030054105000000c1207541c144101c294 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 457863812 1250 457862562 457862567
    0x210402190f051f1205130c060f0e040b0109060311040902040617100e1f17301b010e0a060e0d0e01021c0314041101110d09120303020d0e030415 63
    0x34a03e0a81d4001840704c1144c12000c8990707000390390490701003502c0805402060391b54070b000100c603a03c20030100344542e943e180302c10f801030900c3e07a9a000a4600380720942e640030008000c48218024001855034404c081c4c0e20040200054601400c0c000108542c0c0b503031a50405070102c210b00361800c0c09244a00b00044e200b039400c0341c500044540742000c03c541c03510380690701843c0f2421203000702c0040c00f6010000982070441881d40081c8200d42d00175180d4000d5041250074540480018100214980100e40141900c10300c00c0320f024510244140c0c0c00f17060741640700c40c0504661081c0d0042c51140b4541c1c6001c0c414503501482d850915030b421503411444030714040d545592100710840c0960404101c491880d003070414a145044641c1c075000800b405500c8181703101075029281682c080688491703880403560480001d003030342042c42c40108282c11044d05e00819104042c023440010340c0f40d030503e11007018007d80603070301c62081241c000e00c08904803075205580d83d0007610505549450500d004602d150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 457865062 1250 457863812 457863859
    0x4080f12120f0903130303091403160504020a02031908071b11040c030e061305010e1c140d050f1009020a120c0908031c11210402190f05 60
    0x4528014050865840b8007004611034402094801c1c00c0c082042072480107502d18a419010714400d0310f5001405081010074800401b038003803014025405180440c2010586a04241c00c55a003120003594654907000c080b81103000d2103845c42d03016484800030080098002644c00e1180d4959034554560790094410142903204071100078118a404c807400305a10f003056001169001150300b4082001d101c100b4080c0d242c100b04460000d003105003000a4402c00400303001d5801c400d007400e0700915040c8a0707100041d514105421007981480100c0300d5131000c0318951025105850b0028508001900d028000842911801c84107031005076441d001c003041c424018803d48901a12a0b9504038170800c9850403080201007281241b41802514070f400141c44c1020070091021f1380745641035074507007150700b482401540c000c5001d000d040c041c203000049254000701c2c0c901708000c070308500d00445906d60380046000c940005200b188080701c01500490384078103180300c2c4011101d055500b888558490029641d209 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 457866312 1250 457865062 457865077
    0x2403050c0f090907110313031401051006110703210f0305091b040b04051609050901051030021c0605060306090405030f120a0b0d05100f020f04080f12 66
    0x1003000303000414150070f00c440035aa0080d8141003c1d09605584003800f031460300541d5180541600e89403045c410400e280b07081505c144003443c0284000d0a2902c440360754002c3c0c5002c1e0304d04014184641d05844042040110000c54020740d41201146805041c400e038064a42c19a10103e440c0030500b0720701e6840791280610420403900030b05490102824404413030007400c07039034690080d100c504100280c0d441d4403503203004880000181c1080c4803207607000f80001100b580300310b01c20b00d003080040019403a980319601d514405403524000d5084000c442410b03046160300a0004100011100000c00720b00d0760081140d112403021640d20304170320b0f80800301558801d004081e04513101344042081d03802c090154541041c13061090b28188000003401c4d0700b20390800d00101d0086200325091010030021441882d005140136038000c40841040c0e210b540c2e50382c001c1c0074251a819602e8802c3c403920205503054408d0604c8511800783d889554010540c0c1c0c0e00180d81e4142418043c5411510369161301c1d400311900e5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 457867562 1250 457866312 457866337
    0x60e061f0e01020a0c2c01080703030507230c240706110d02070602030f070e030d05031305070306150608070f0503060a031401140a332403050c 63
    0x5214031400c4564518825034103040d803107030b20b0003440000c1074003001c14081e01a0500004180100c6842d22081000c490341d8400040d14040050140450204101d401d9a402d4281645c0d1131900d45800c0001c1050084481c40807104050214000000407e0b080034011045030078440010300380500380659941103080d061080820009400001d203039402c400400300c0d60341186428860701030300342e409907072100c44115080c50f8004204800141c06a0302c0319080712407480c103100d034001d501005c01d503284072503180d04003441004400109801f01072801315180b90b51190541e89029940e140035005000c0c40310850414517000000424594407684241d4819103641e41d61140b540818074003540c03540d102509007500412070b00c0011010802c3e1090308254201903000014502c2c0c14890602c040708030280000911030305100903960f560020003020605044c50381e20142d80e03501d00008058051505510601c10103031441c10b10605920012050031840406441c18011651008074100c075500c02c02d2440c819 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 457868812 1250 457867562 457867609
    0x41703131104151a1909080d03060608040611090a1706011203020703060f0605090c0703020c10090b03101a030106020c011b03200714040605091312030b0d0303060e06 73
    0x104504912584c0c0040e4002c401251405010007000c2c2c8426614090341c10101c1c40d594820850010100210502d90005103400c005603418404020b04440d800f4002500b0745458400d01402084020200c5810007001030800d022595582c02070440940c070690304c548140030b030400004071034200d940e103c0d071410380c140d01070119942076545a400411064004409440da035000118942c0c90307400e43c1c0341c040e510841d8031540b2840c640c5402464104603101081c01203850f040c51415940c2c00c40b202c4003e9410030303ea40d41d240d5a134035040c0c800c103d110358091580340b0031511066901d085100000c505941055080d10b6500280d00c005440e6150209460301e22203002c607840e440401d20610b10404484803240c6402030002c084088503140c10000e07041101e4071400320712802d1f610701c2e240c86000000d042c01d6441880902d004131841c51200324203d0050072040358081c612442e148680c0c0520042140104050040c031810b09005008005a004e0b1094401e80c250111345940342c1a918000c841c01071880c0ca15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 457870062 1250 457868812 457868819
    0x6090e01092003090f06130204150b030a1d030304030503041a0610030507020c09010806090c0a0503031803030403150b1206190b03030d290a0303090e04170313110415 73
    0x4020303034001030040344c0c00e00441c15201c261039000d05c08103000b2400c42c0c900c42d10329110b5004010271915040a9240115651001005107222031026030b80d0166004000080b40c4040c000c6170074a600022403a0039480c0800401c2008040e0440301440c0601c4c01952001000c000e040564200c1000580c0c120f980501e0761702407480018403c1d0030030341e4801011f10668892190503004a0000f11003a004882075070030210801646940070810f0020301581140c801024602c3d160100c1c0c1c0b240b0402c4005c40040f984c004070401c05072020800c0390011644001100701c20703100c010246005182035910140f00e0408611465044000005c00c030b4012106545441c110f82d03140c441d00001080080102501800148110117080c5c1c07840c81035810110003000340d0b244020b1598003200d92400c481c40210b101d0758440c441400404e5109014101383da0880403003030025150781c01e0140c0f443d03a07040001c044030b1000104022002100c2103a00c0c40d081c0c030894010240c0c60542040000ba100c0e07070516050714881030f40b03081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 457871312 1250 457870062 457870121
    0x303010b0315270702010b030114010b250303020702010201050c0906160c120309080601080a0803010e0a0f020409090c0603060b0a051c1805190317040203070503030406090e0109 78
    0xa8241030014494400c00c0005031808207000c1200b40f4003007800502c802089141a020b00a0381c03200c580481c02013080d111001480b0f072940c0340c18000e00304918008680d400f50340712104510014219448a044182842854000c1c01381d448950201d00550a05d400310b4000c0003031078180c42344003000a009074104941c480c0140f44c0d0201c03085c015202c00c80031640c0000d142c8900030400c952103000b0b503105160a130a042d5040e1400d00181c2c4500c00341c0c1c3c020001d403004101542c1c203884c1541c8104000b84c50380d403501c00110002e41000414050098400900003e01d2481c9178040ca0300710703109060311100346941d8038059044850394400c54070000c00030411400c4161048000344807004c0d04000303501d50b0a840070600d8040300c411350900111501001c85080603c40d00700b04140700400d09100c00d01c1580c2c090380d8000c0007051000a8104503e80c4480820119074050000802030f1a01404580c0c546c0e585007801001002103100f03150034507030a800080f90120080c0200310302d280c2c0c0501c483c81310301d9515070302 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 457872562 1250 457871312 457871341
    0xf041d0937110613080f030313261308010c020c0604122a0e010905090c041d0604030531030b1b07030201060501031109010c080a1101110c0c030303010b03 68
    0x11100c9014510540119070f0302c0e1409015210040c0802c003405600f80806645400d0700e0141c0b03550f55902c00c2c01040f40b07070000351101101103540b12541442d003000d90f140c240101003031080c607804c000304042074451030303403200313040210071100040000d202188030250280d0f160307501101401c2d08036000b0132045c01000e0040c54400d4407544078030301e0030786034024104141c084024070400320303038070580580320800c001e186507120203001d0003001c00100194241590404c0d44d4007601c0412a02a90f15518642c05000a00c4040d17040c0314000c2d03040d5521490640340090181c0d000403c080b8101c0c0703180c800c10b2400b41002160f29601c418000c0c00d8411141107440d41c04024400134800b28803480110b01036490325000c0c401501103903110350000300d602c0e400c140024042e108000c06d402c4030b031141800081c005030303444145003000507044801c1e07036544c00120004564403440f13110480c5496003007034104500704241000429810320000255151502481c0802d41c0302c1c40280b0505403036580c00d02c040350019024420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 457873812 1250 457872562 457872673
    0x6050f0108270703110909030a0504030b0a140a090309140d0605150a060206060307050d0b06040f23180f030f09130905010b0406050f010903080f041d09 67
    0x380400700c0320502a80c039260030144c3e0800c0f54036010902c541e0178a4146114070942204800703000e103084c41510f85000f0f01c0c0d400f50741300190109040101090b5041103035846145400c0c100c151040b403500d071036003100c80500f5000b40118005055028005404800d030b04c5806001a802441ca2207580410f40f40c207005400f000d8155008144040441411580c400c20980c00070710464014107034a00c0c0400c2007504200da1540700038001c81030500c4c0400001e0607060070a0f80079108583c002440d0f011480d8110040c111110f5000c042c000c16411036503521003414000744103c241e0b00900240a24010142d9200d80201d4501ea9090740300388001c402390036104010349005503003e04102161040c85462070142e814101c07007554140d546840000305800e2602419000e0701e81541d100d1f0000000c8000241958031500c006041c00d034010440d01000e247e040120350003040b813140104000700c1c400c018071545038010f881c0b2811910414403c1c040171420401d181100f021001d0311070021402290400070070020b41c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 457875062 1250 457873812 457873861
    0x606031b040b030703050a060b0607080906070c09060801020c01061d0117031e030a0b0f0901061d0a03030201141e060622080106060e0a03020f010c020d0503040306020d06050f0108 79
    0x50050b02183c504214080046014800601004080381851012140301902c1240038103c104410070100f04040111141200c041c0c42895543e0068240049036603400d0700400760203400d14a00003100c2d40150050002c10308a0002008020350b640c2d04010300340703004408201e107452030400401814500300c0c0c8c10300d030344030142d4262842d224031061640c036040210090341c2c030400d90120178003a1407200d80c82111041c50307007a01e41d0354034440654000b900c5a8814400c44042000c0c11240b600d80c02120510800210400380295286503200d25019020b000c3c0000802d0428076644000740c008401e100c0300d5a214072014041d15001d03204c803001d01146520100c400c400b0329400c401441c580d10b01c0304003000c00a041d00300c0009102401c8c800001c0c1000d503441c8415200c0c4a50407001d00c09030380c40c4650341c1001c2409007440003042d090703171000c15100c0b84140b001801c1c5000104001040c458590010401500e0300c260800003181c4a204010044201c443d455001480a9001452005070651188800321941 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 457876312 1250 457875062 457875071
    0x3060621070306020a0503010603060e131104091505040201020c091003080901140c0c150408070b03040c051008060f040911010806120d210e0d031e0207081201080606031b04 76
    0x1c0c3c49150a90303005e24540e0300010000001000055410311a0201814007003c3c07030384803030500b100024030a0740003942c09001e160340c254240711159565440340700e81315403004031070174072007000703413804c4000c0c402150709074054003c00143c110549001c4224921400322030b4280c44460342140c8642000b60040d0202d01e050181210039048500b10500c0038250b150a000010140c1c2c041880034059100c5a42a0381080380b01c0038801409002c00101e05a81a519060380981c4c40b6500d5041c00d8070003591b00c1d400203420100041c2180e4003568080d124070720806007680c894800b0641d0809010417107030415005000000210441d061947c4144043c581002c0010000d5901e1405000628208040c4103d2031002c0f03204c046000c0e15400c40c0c0d01882906040c1c880c02041016000085907452b100032401500400d03540b201805424800402c00502e0315040100464440d88246841121a442240c00e00b28802403000005400440041c3c02031203440c001e0040c0c25036140c450369944018000858181d80652035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 457877562 1250 457876312 457876319
    0xf03090308120406060e0606040302041107060c11070f05010503070f170702030a03050604020403111909020d0f0e0601030312020c01020c0303070206040b0a0c0f050a020c0d080a0e0306062107 84
    0xc1c800030300200c100c00c030203480c8541000e203006011640241d002c0d12600500d401000211740e03030401540c0440790191001f0a41071004180c41042e440340b510000c0001b8585841040c060f94000320002c00b011003d0202c510385a110310060301c0c8518230340310f141e000460410008000c248501a410580469070812010409a210102c00b40d100c0c211080c40c0180e1011402415440e4540603041e041038041c0d504600d06411a102c1d26030201100c03040324000c0c0121460710880400500400b0010000e109086480300a41c0c0e0001d00501896582c404803241000f02600300003d010500e94103e96244e22140405244030002e007000e9001110803403540d56090108080040b410300045200d2009039019007410726103450114404000030300800d481c02c0c90480c000301c405400c500c4101524906080080c1c075252001422840e0520305103119401820407010310b0704000d0f031036014104110300d584480d8501e41c01107090507980d00013150601c0d030000380c032400c04048445d120004050005210705032021a42c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 457878812 1250 457877562 457877573
    0xc030d050d0e0a05012003010e0105040c170906100914150102010e1c11060f060103110702040c0906020f010b03100902060403020a0f050f1203120a23011509050d0f030903 75
    0x25107103829100c030b945805603a10748011084a100c9420311181b012401c550508a160384200d8050080c507001c1e0b652100807462940c0110014401b2040031114041740c0d10b004070036942c03285401d50301c50702440401c0d44040707410100c2d409201c00d40300c24240001c489682d801030344075048005040d480d065541e07440d401c0c5440201400900780c6c61400341d00b42030300343c4c0011000034420b025004103011160811010301a00004507440c05030000c0b400d00e0040780068010301044c8e481d1040b810022750283c9030100c601510754218500d40100c40c065000c0c1d821441d00c16106c40c1c00c0e140c60140d940e5050300705040030b11680c002948410032240c00500307141d003865225070100341d010103280c11108400703030540d50400881c50300300c2100d4628441030310b01800d043d10720701503941c0e01d001d00d590400110b0800313000a0481c20b050f074000c40380405103a111079040190080d1107003044000703000e5a6030240b074262074000c40901800f100f1007211000b4042544840c03454913019000c0c00d012034100d040100107180040441c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 457880062 1250 457878812 457878823
    0xa03030b010e15220609090b0414130b06010206070903240e030318010b0a05040b13020301150e041503081312110f040b01080606131a040303020f0c030d050d0e 70
    0x1603c10035802d540700e500d190700110221070009002c804107030110092080030341c041c0300034049807114140031401c0c1c041100050080c140c40204843c5035080f480030170600e603454004d03c8180320f001e59404449a11803400481e00e44901710380c0000071503000d4604200040e0b4501140c40c8030090001420342040d81c0305074841c01d0314025a150892648088284861740c480a16207584400c0729170020424801d050001c1388180310710344211481555a4004000c441e00c94003e103540c1d822218030304641e250b84401c840d043c0c025a08126000054040455244600740740c49800540c00b02c12000404040c40d690310070550b43d03c010107502e104802d208000400501d1004200d040c1ca11035070041007810015400d02c003903084411000b61065007410120101a6003000a264000348140ca0166032102200d1615200c4100d99004070640e40c40110701d200608c810402030010740344a0350035201a81034800c03120b5501c034505e07071010341c0c50340001c00e1500c1c10601410060481504041c030102d0a1a41007407101e0514 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 457881312 1250 457880062 457880089
    0x1060f031b1b060e150a090308181c02060114120303150303070615091b0c02010e0a050d260307120207031b030c110a06120c030b090103120e0405090a03030b010e 71
    0xfa400703803d00179800180a00c0450b03026643c0318007005400c005850043c840301014103280c02c44240d00507040442c24040c05155032028054030b0f42001d00340b454030005d6550209109100c0c524184012400203450300d01c0d022441020760764003c508580b124042040384441c005001503051004104031740c001900c90160b41000c0111052149483c0e1070f0030301140036034100010f07a8000c100c540d620422296003101010702c441d0b40a180201032b038040480801c5c0141699040580d021140901c168100101d08810b0b078000300c0703d00303040d2100444105144180d80010348240010880f0110310903000041a8090100700d4000c0c0b81501070701010480e1002c0d00c5420800a60014204244103400c4c885a18642c034880e4000303559484c00c0c0d501c3c00c100140103182c1403c0030a0f220b074844085040442c800d4100e20820340e0000c20741d000e2035075a840c1960f07105400000303000c0400d05c8c04000320f86918051103000d10034095003000d04007032903039a51b08600902103111240c1c10720100030f0410340b0548698801c005070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 457882562 1250 457881312 457881341
    0x91011070909050c1f0c0201050c0114040203280605040f060204030503090f030c060409050921041404060f1215231605040e09120a030501060f031b1b06 67
    0x30308103103091141c102184d4080e054011244407030b0303d800c0c941c0800c40d40d640c8084203140040614001e40b004807403038403c2020b0a0501d60820071045002031810b051070340a01c0c400c80c00c4030006030b05c01d2240e080c803010760401c0d00c0c070188201c0702130b5010a0658014640c0b1a00c90381c3c107010b040400b90313a02012600f040e0020f031101d81c00401c14548905240c12030313400d42c50084004100c003181000010f030035446070707025000390070f40c41d400805e4641d00c0411104034200700c48012040b0100c039071000340e15260018820002c074806418150011414144074000c1910204001d0310b080b01e0810714281c4103440714100480724140044c0c000000c00025200362003240f0102d107000b40901341650b900064000000c2c0c06030031241244d407441c1c0c00851300541120210b9914404d10091960741c000050304042d40c20039035000307540740080c4e030b481581e5040d481203042c0e400030f44401a42c040660b0f0220304480d500300c540c003005001c1c0010401c03500c0c003542c807003414008403030210b191010703440d0385031010f4a45e5622203c10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 457883812 1250 457882562 457882571
    0x4060c06150b090f0a032001030605120d090b09030c040c0c0501050726060607030f140a03090b1f03020402220801020d050f09150606040e090f01060603020903030910110709 76
    0x7844e00e414180c46005190440d80c41c0500350460300c030310520021844a160003440a10756850459009410040041800130483e2140090481100d920381144200200020380070310800704141141c60103803200c549015005000300e555500900004000e4402000f040c840e543e0801000141d09001e8030f8070404013541c8521200010700b95961444608081d825a440544003c02070307140c8a400c00c2c3c4410f81d03018504540c1070400001c094410803005101e03043c0309040056022486500354206c400601c0c403800d1916120741e5617001ca407115040502805100381031411003003015151540181038400c6e080060248210707000e82142003181225401100280d40216850322000080e00c01c0941c01542e100300c8400f00d14004070400e84a0355001c202e000982140707004903a00b92140070564000e09030508401c811802c20200c919074900c03040116004c103600300034000c21410310074000d0340c801c18006001581020b26400c1088170180310320b000d510420860408070b512480e03007004254020030b5042c80005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 457885062 1250 457883812 457883827
    0x609061e0608070308030f1018020711092e05030d020a0b07050906030412031e2405030d120e15070215010b03040807153b0304060c06150b 61
    0x29074145502035200307600000d800f040810311003403c5a0f0700c06400560110075540c0c0e1503d0182d80340c1d151b0000b2035411090280c20780c2050055004084d411f0150014440e9040341d44104118080d00b2504004c030200c00c040400c0580342c2d800c03038001d610301e845440805046d803100c0c0821b181c100c2c8421000d0050f0703c8003000b00d0a0084000d62550030540e946009464541088040f60f6580f1000c0c00042032042905106074910703100ea0300c044528064102d103004806405904c5c407000d0f005507082080c8440d4801422040d940c2651035040841d00050041c101c010b404010540b8044420800300455680303989100b400c1c11000c0c81031800c00708900002440908065a0007890318059566002c1505503100040c8019110b036010780c1c1d0b219601102556036800e00d894a4085c020071b00b20300400702030030700800428114514460f9080d003071003068200800f45a40700780c92142200350443c00e4080e041004240030301d03032150705a45541d501401010441000804e50a0480c1840e40e210548480c4080741c0803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 457886312 1250 457885062 457885121
    0xd03050108030f0304140c060304030e030609010e2505030604050703140703110f010c0c03050c01031404020619050f0705030d111201051e13050105010f09030f0f060906 74
    0x2603000d84910310045040c02031400c44081c59100140001d0045c0300404100448158100b003190203000d005031019483e410a803402401c07100100030110b202c0e0040e4400528070b440c052044182c412490002000c2e821002000e0002d1400683d14082c40e41c0103501c004522030320b00b0031800c2d0086d44a600102481491800d000e80780d04c42c098038811300b940101004001080c694000f20300c0681c0304840181403001001d00507264400c6c15a00100080b20384080003045c810f000c100c1030700286080c4c0301407000b48420a07483d0740c819022140254000b10500c8101010340400c809000c10440c28180b1628104500454682035000840200c500d54400100100300ba1024090f0240714005244100d00f03004030342c03e1051192905010f145d00800d03280120004054280c5440c081d80040a4140140e4501c8045c2800290000b40145d90114510742030398682e01c1e00c40e49031802240d80103850302c00f2565065a030300202c00f0b2405c6080c0c4041d901d0b00080c8020a0326445040344000e50408090912000b50320341 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 457887562 1250 457886312 457886321
    0x15040b030319090501180605030c1920012003070e031b18060d0312060b0f070c062d200a1a150405091603051005010801022a0f0607020d03 61
    0x1c60410000703521b200c440c0302d80c10035680c1c00c7e02c0150414944944c0d403411502c8070390007860354081d0320f61003d0388840d5a894100ca12101007455414140c1c0408842c0ca509a0984d0746031045c9100c102d241c07605825803107004074043c5802136034624007582181600e4000918040c03980003c6c042d440c6040409480924184c9407400440100d000705500c2480c2040000c0c883c0d80f80c00a0103030601031038594a401d284910f901100c0640140c0000c0d9889902c0b1200e94007072900112070072a6683d80f01c403004034030503024014461100fa21001c40d00714040c82d08503490340600ba003404560900821140110781300305a18205030314a50001c00500418074681032086452084140c00c2d19104807590502800c035441940e00e40e04c001043e1000b10f00e58444002152070840a0f1100d51212400041c01100300b260100303544030b07001035551003400b4076626101000c0c00c034461111140500c190b5900000c90b00361003000004040c0e0f1140d010f480b02035070a803007031909150049850b50014bc104040e00d21b82c0d9a0180324 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 457888812 1250 457887562 457887569
    0x31106090c0f0906030a020603100e06030703050706180f170616120b0a0e0906010f0b04080601030201080414060405011e05090c0d050709020f09040b010309020915040b03031909 78
    0x81c0462a018000305205050b14840315006000c03190026109841c00c001000c0740300e6001d01041c0d507178585140352014040d01e0f8002c2c500075025070404100e4134a0005828002d880d000009040300a02d402002d68444507040c0317120202e490014030010f401e24001d61440300806840608001100e920300f01c1d82e003000380041a07a60044486401d1008040d40068400050b181c44003002442184200c00118160301585c000f184810484040102960b0701191840c1214185440c0650041d16400404510b0066002e820a280c1c85000104099880f603080b035500140107154241d010010286600c2c103042c0100c42c03c1d50302c1e079169105c07448100d800c001c044e00380c11240107041016003070000e410740e1a045164100340c416180440c0b02e00502a00b44580401084104011541c03030042460b54200c42c0c0010b01001d2081d498030101d001c0ca5406400b521160f190300030180c07400c0e645d4602d145403c45080d01c072610381095a80c0e510210688080005040c400010003c119a1480c0c0d0007000f04401d22540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 457890062 1250 457888812 457888831
    0x100902120105130602091210060608071403040b07030905010903030c1d18090c030703110f0d1208070e06040b09040b03012003130606030b0703050a1104050613080109031106 76
    0x10070084240c10300b0054100f0243d12810251b80e0b440400001261450582d80d4021980103440d50019a41e6059009208031015502c07401800d9807080c200b0344080e121104401031480e000c000040000b41029013055101209040008118086840c1d0a00f143c0c14201d0440c04a80d607a001590390b95041072484480600024454005c2141d00001c1850a00f00b80040c41e003450302c280c00700d0b8142105000c03001040c81c0150480707805a6403400e08903283c003d80c0103005c0c0284159039003458075081840009584c2c5e40c01c0f008500d00788950030780444e221000140420100101810300320043d40d501c000071f00050200c00b07107003500c030f825003000c20040700c95070040c2500c02c1c0e151520041503035070000e0101c4900c24011020a032a595082041d864980381410300a01d540d24100002c001c00c440100c0c000c2c020790361581c040185035580f100d031008460700c1d0030903900003201c20f010800480c544000144558424498926101c903610000b007030039075626610840118180321a0a150042d0030002d03e1b034400da004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 457891312 1250 457890062 457890071
    0xc0105061014130306050903030a0e0a0b01050d14061008010e0307110d080c01050a050f0a090c17030706050109020403051212190b0d060c1d0a05010c0309081009021201 74
    0x140000e010001c40c096491210795003c100c4000c29004490507800450300080180214900b044d0001d4490348105c3e50013803040e00c0c042188801100000b2414a1b29074002c00e904c2c3c481e401c282c20007105074142031044811181c0100103011801c07003403002900458580c0101850181404000703030a690b10f114081c44564814080c640102e0307080784005581060a503a2002840740b00c2c14500b03040e2084400b06031711740d802d1105106400607664045803040c240c109095940d6191039007820b081c5c40c034683d40a070500000e40014800c8100b24041c4a20b5001802c048910f03000c81542d4a006507130090b4030401d01650f001c00c0030000d00a0900c141c1e101002080b01c0d040c5800404102003079042d034042c00c4075898005500c0804500d003030130f0313012000c1028024581d40c200311651800d440a4080341c1d59040000381c40b01100100100d507000038028202c0028031000c0540d003058011218000b000748181c0401400c04400107000341c05004440c02c010741c980d004140c0c0c000c1070050009803c0f9004603104280e140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 457892562 1250 457891312 457891339
    0x3160b0702010c2d1e02030301060e0d0b0601111e0105010501110d0f03050a090501142509090203070c0f080408011409030d1a1801053607091a0c010506 67
    0x340401c80d01c03040401d4510318441345219500f1100582600c0b41c0c220300784202d203000095180c0010145040754041e80e41d00e0b001401040900903904904140105078010319004103500d50700802c0c0c60191007030b001c022a0250780b6032034152512294100b001d120280d54460040c002541d100c1a901031a4845c50300410030911107103130052140041201440c101955000455888940c58100444603030b0010000d000d0b41c00500800700c1c2d070420595654068074007000024000101c2c26a448035407426035219090301c24908101d04010350302c01003000d002c104490a55800061902e4220220913000785402510f072810024518215491484020b040b815401c0030030007041400811200c01a00030340c0d0100c0c03170249024a210301090b195501e1640403900347d002c1c0d103403c1102d4202038106c803401c0310136001e01a100303103191809907010340e2541d628500075110540701000301c18103660402c50130300c1d00300860760780d41c1d0740042c0c065003c812a076a00240000c114038013610902802c0d0300004c086666a440740034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 457893812 1250 457892562 457892597
    0x206060604170309060a120b030f0d080a0e07060804061112070f090305030a180e06030a1b05090103060504020108070206160c061b02030702090a06062003160b0702010c 74
    0x314070031201d41c100c124501d80c02c0c0e000d060003a00c0c02c4d0390028000a454440059002d0041c83c6a06442d424051400b20003035410710b00096210710070213003440505001c2c0c00036207003214110401061340e04c0700b0352113070707040009001304000250081141e0364030301038075050910b0a5010380d05081d8651707000c010240b01500380d05d49a11030031604100941007210040010b4503040c0c2d80761044d5413001e007a50001080c1100416003185803882400c0a4602500100391a8079003101403c000740d4200e07030181c1c040300115000555070200b201c402540c01600c1d2501c0c507038440000d034174664240c01c00c50710240c0310307428001156007054085401c484580082c013082d2902031040e0f95030600d080040c0b0704200c4031900500c284071007a4000c3d98900050200401e00885400010f5901d80c004d03c0124011440200060a031013007a0bc1220159001ca50743c0740c010000303561040d03102c1031011410400d21701042016440080181918181c4107100d4101e6a4151a00c0e52000c2d007110303802000301c0140401c490813100601d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 457895062 1250 457893812 457893817
    0x22020d1a0a020f04060f0201181407060212040918120e1807080c1804050103080426030306191d0406050604061a0d0b271005010e040504020f0d0f02030d02060606 71
    0x40b01c1d841d000200302903805d812030249c4038480c4900140508210b44400340b0a0007005002c899015204a8580c143d8421040741e0b510701142d84030b5402c01050000740511a0700360041c40c482c11001002841c0c3c68040d885506c04401485415004104803c8546140c1d0a00006158500f121011035003400e203812103015016170f50041c0f500003d004005010703815034000b65010b2540b010090400c000942c2c491406941e998440c0c0a5003840400010300501065018500d00c0c0010b103800002d941907032512000e01031046500944100044540400440d210441c5030b00c07490000140c0044070081e081c1800d013202201d00103807403180154246001400400c0b01c0520404082c0c008a030790036a1540300b43c0101008148240e20a0743c0402d216804500c622010742d82c50b045020700510400c07175500c0340318030384403e44400c1c400d035800304507141080c1a4900d01039100950050026000c2105c8030445c2e000103c828058100c01c68408100100d4601035042c200540840e50310b00c0d00042c00a41003583c005005030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 457896312 1250 457895062 457895069
    0x160b13021f1e05030a0c091d01051306120308041a07020c190605040614040e090f070603060e0c0a020f102a0c080a05070f06050402190b0322020d1a0a020f04 69
    0x1503440c0d0740d5501178944511507047c010700b010032035205401e541030b407003581040d420320849118103012421841c03a40094030502040b50003811013110411080d54060b00c640360010829546070100c81aa0701e0000c2207004540d200351000ea0180121011080810501c4501160620945030403040e06000f0140c1050803142961807608150350b2150300d440003204284507c0d00061a03100c0c064007030002e451000680c081c080e10728642036a25107501c541c401c80885180303104919824003d007000c01c088580c0c1d440282220041d5206507138144074540c001300d284c100301e00354803180540d45204080d0302410b2100070303031814030300034400c3c40078100020b8008120f8011420094524880050300d290b8050080045031001948031060246150590400400070807045070140d0042c2504445500c0c0b052800c00900b040d00e21110029007562101c0b002114050140036210005802702075004015a40d14600c000955108404901520841441c5916030100c05003844803280c3c0140721a11001001c081610280c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 457897562 1250 457896312 457896331
    0xc0d0339031a060a0c03080a0b061c200c0f0601081b06160f0204060e1e070908100e1903090302010e130218010201050705160b13021f1e0503 62
    0x8664165100c44450a042e50072940302c5400906074441541280300c0405050190302c800358107503107a81c2000d0903180c02403141d036844041044000c035000049940c065056000c0400014aa948811280e070404460144000c0307802005c16280c04550040141c40480104040a000154076008100340d03100f046c00c007959425918000709810325265281626002d5924040f081c040b100c5c1c41c1402c1a441411003810b0b80280d08002c0c0101d10382100d01352603402507684801e004034010304100002c1000e180034000303070108480d102c000101c4580070440180682c0e107001000940c000000422460086072400c9003401011603059000406d400451b480304807034080c01c00d0040194240005a02c1450300c1c5444801c90340301003180c928580c841e01d16420390038401c0e002003286072a400b105031428015007980310100da1038985e21b040001c07800741200d40c02088005400b00c4e03450080d40083c50030305070382d240101826404015103410b641c1c04a01d980548180701070004c0700a14689c0000c0151000a040d002c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 457898812 1250 457897562 457897571
    0x302060f1c0f110a201009060203061002010c050f0f04050a0303030e0f0304050604090f0603050312070206010501080717150a0f030c0b09030c12030c0d033903 70
    0x4000c8100c0c4100c80d400195403a20700528400c200111004000110300c2002d0245099403a4160034140c000b01c501c0700050303844400301107605000c00c0a8501c42e1040e80781560081a0f03400070b0440c1b01c1c0c0a0340200600c505405038070317890084240102604150640d02c00c5a0600061400e07164012048030b00d8440c002c10320551320554101c81341c81030310440e840541c01001d880000070a160b81036214030f00344050002541c2a0f400403540c1c45540b40a00e0007032541c4000304010401c5202c00f16445010b8000c4800c00100306a039694941c24195009500700c1005446074008210040d54140a0307140506001d003007a00c2d007401d06090040c400d074078000c200d000038812200422511a00140c803050100030090005006e0b0b515100da1007811081480115028404000c000c505010f0300c605503485003901800400312025020204203c1c60000d58001300c85010800584045407001d12000c500e000441c1c4010849040203840500e0090049100040040e41000646085000b003030301141e94011920300882d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 457900062 1250 457898812 457898827
    0x10030f0302011b05040513150b13082b1110090f0f080a020f0f15041502120105120a0302060103060c0210090b090730030e0303180907030213030206 65
    0x2d00400f00d6220703250041c0080000c0c004070301e07407000c02441950001d8411840c2d580200840c00261040104e02c0901d003140d070a018028014500e024150745213221482e030b0441a5100d220f1420039089000004410002c4010f05290700d030760000640c00d40815203025421265040c4d0481e0711104a40c045860082d184c14405e028010340d440c800310141d80103006000c6040c0c281c030b441c02169000342030072800f5010310500d50700d43c818046000b030541000d18018000020b04a940300072610030080c803c88a400750126500b00802d21403014150048400300e04802c554103100c01c1049440c46180780a2942d80f0114007030000035408106181100c0e0310000c00f0801c00c100140603070030070b6015121071248078540724890042c0803c1ca10014000c2400d0300a650040e074840d8464040114454100d1154803001c224603100b903640f51201c194901e00a00c0d00003c48410040040c0c1198019070894020030b0060940c240c1e10700c1c100207185d4020269040c110f00c0c002d807460759190f010380d076444081e01c0b40d40007044a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 457901312 1250 457900062 457900067
    0xe0105130207051510090c0e090c0f0705010c0e06160b0603010b04180b1501021b0d0f0f0b0a05090c09061203030103030f08060316050609012001020706110310030f03 73
    0x45081680c41000d0311076100d00300130050840c4400b02e50b03000d80503030700460009040a19108440403583d003550b400e090a504074081c00131100d00a8800e4128103410080c041074419014042c080385482140042200c1900060080c0f0203004500312503c6554100494220300542e1245641503550015040d216580c03402c0003c0e004203031040f1002e8010b41440c0b412841580484009814644510103068040e20781d650380704e4601045c100320344e0140c1d220081504031625400c60340c0d0210340700103010b040c40c00d00a039201644184048422120705040152250420680c15502c87d840740d81910100f1042c81d20840382c51740d0f00500003405000f001c1100204480d0b84548500d10842c0000404072039423940d49240007030030750120120010000f1198404124103190200d06000d10003444c5400390601c41c181001c00c1802e070b1040c2000ca0500c60501c0012090051000c46502011641400141ca4101508002c1c040d150a01040e00e6030301c50800070082c205000c02141815250060341100c000d22151805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 457902562 1250 457901312 457901317
    0x901050409110310090213090203032502130f18021f12110c15070c02150c06070207060909230c130f050f01020c090601050313080316090f0e01051302 66
    0x11140c150160b1381d0004801c0c089508802c4407a071003560540c441004410030b01c0c040b640100303002949500104211040400c020030a0102000200500c2205055550000d844c180c0c0e41645690301c0c90320383c0e00c0d20744003146602c1081c0100107005000d0100b0041d940c002002c8a501c009901d0000c46103800b003c07101d0340315075074846d040d54041e141044600750107800d00c1d40d03c0d0405066103d040c0704030b0f00548900c449044071075000c0e803a241c5886244a10503401c01110019540c3c0421100c0410300c11840545010407186005000c0c54003d03100b210306003040100a1049500003044241c200451545414000d40a10416200d11400c048403615041003140951064910003254007000d11004212440c0c16444501103500c21540c40200d40b22000042ea00d40d80001650740e0b010080d580010581c0d40140000d5502c00005a10340d102e1081550343c0d552140c1040da001a126070600e40201080351300820f01d10050900d00600d40c2003a45460141000d81d4414000d40c1e000301e010740151415203205805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 457903812 1250 457902562 457902593
    0x90c05130213030507030b010f0e040b0408090d0605011406121603060513141305030a032d140604050103050601170309040203010b0306040b22022206020f0d0207050901050409 77
    0x10b40c404401da40741040e56603100c0c035000644959600900018008201410030b204960092103c040699600e4503624443c1c1002002610144020040b0241d250340386d0340c1c192031380c1d8070070100001d8550400e2040c81c01d01096900060113648108800540b025680b042c0c0d5a000c2d544043c05407440343d550304103c020780200e92007950440000302400415480d103810119148e59150f01d180300741e44d04c0c101c3e803c3c03982c03e1080c0d010f4041e40042092102c11807003a080000c6110100700450000384030105501610076240000c1c10102c1d5a400200341c080d41016150f03500000f00b100d06000c40c4d41181c40f010f844d1201803040030281e0340d0043c1c0c400760046040c019550302c2200240215141d6940d40e81d2544198401c030369680c461898496060943d00e8080c00c60114003840329040c405081c01408040001c1d80f0942d003e0807203404102c50800449407078000035000d014940d01504080d1040e5100500c0c1c00007064901c01990041181884a1b0321b9100050741152000c840c08a450822401c1000020b0040328 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 457905062 1250 457903812 457903837
    0x20c0904050a021c1208010605040b09010e0a08011a0603070207052202120a050703091e0f08030106020f06070915120e070801050105010e0316052716080703090c051302 74
    0x24944040080311011804180a80009205c0003d40201203038030520034080c80c40441c806100a105208001014104280c0c041c10002c0c5103128800015032050095400303400645e444a0704040e00882035945000182000d5907480d040d82001d1001a44070f210a0103000d00a030081c80b002e00455803034030008a240350f0307084800c40d50703214030a0b80900a48012a40c134108103040c003002c81c001d18440d2280708040c0d41c00860b0152401d09404000c28070b04020303401a01d4640c0714448920200701164019802494141c0081c0511051a6281802c0c07100040c0b0034000c2c401268000c019181e5034104030300040b2024541010690b4151801d84002c10060a4501c00740c400d1a201088060055004505a4209881c0d008240009804061740c0306040c102c2c0c1241c2c8a081481006a41400401e1b003a450b544060100815a088a02c00c807034948115840d44691601c0d00042072596040101660448400d15082c44102610b44070450221618851a4090390034101014612160381c0c1c1510320340b54179003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 457906312 1250 457905062 457905079
    0x60109030f050615030d1d0f040e010209030712050a03030902041b0f08090a0302030405120c03030a0f031103090606130b0d05210c1f0b06030f041202010c020c0904050a02 75
    0x2410050354039241113a224004580045004900d072030002501e10a900c903c0c0c2c1d90100044243e4980c8026100d114450340e0005070081c1084001d503107a0140f8600c0c92000d800050312180c020080520341080d0341e0000501040b0010300f10081180410840161500f500b0042801e44051021030010b14541440701c034119400c55004000317540c08407040c0510b0200f0741d82d024558580104040e01c031210000001c0c0540c1c020002040541040300d83e10003100c0000064681d00140301d00402d04603030003000013200044144040c5584140c0500c04c01c1600e00128005a080d807800e074582c16540c81d00175001d00e1050541d00c40242400829030424028402d014100b01c2e440c044900e0040c1e6210100b820b29080d0100010501c11102d801c0c0040c1c42410b8104002030407840d0550540144480c100c19040c085580c80c4c5594003029101c020085000e840041c035071282900c0e20b13090810054005050f14411641888880e8546681c009020280785e14100c5090429458034540340740f801ca00d05800039040040c0c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 457907562 1250 457906312 457906343
    0x70305090d0b06010207060302250c05030304030308011a07030804030c0f02040e030702091303140d0f18030e090c0d02090a0306060914070c0534090e010605010203090f0906010903 79
    0x42c01840b030301401c002c1e000c443d2032646408042d02607000318244400980c03460b080290005103914494220580a22002d42e00640c03140040703410b6030301540098004c900c000c001004880e04c400250140c00d00031100b8241450840c1e40d000344040c00161018007000080c401040912400000094200e50b004004000318003410403500d890342c1100d00182d1080c8044c20010740c0078403e01804540c5598180c2c2c544a00c91200c84000c6242d4008000c0240c14a0b980d4648502501c864401d40f10f25030713810818410901440d280007444004203030801e07030040f40c03580e0a01076112800420380b115440c0b0b203c005a100d00400c1c2c04907100f82c0440c0e00140825042c080005501c00c03580d4080518541c50703030055065503079418016510322980d020014165032008500c19800e2001844507141c2140e0484000804007035040d107030101e000b0355000650507907074503403004507440024856034000300310078006141410500000143c64091583c00113000b0080e402c00101c1c2a88540812400f45a0240044258081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 457908812 1250 457907562 457907573
    0x31a0c160c05040b0d020f0402030c070b15090901022805071e060e060705030109050a0b0904030f02070f05030c040c0c0b042f091911072603040c0b070305090d 70
    0x4980305103409540791009021181c104641700c590265000751001d001e0701c00a205100c000c5d40024100300e0050001e0010100044400404901401b284080461658030b10810090b00640c06070039103e25a10421071030500c8040f00b07101440b944688075801d0480d80c12a5010307519440340d0340b00180b00c03040d03c072034551020240c140800e641c0d9005041c00c00290b0902559070b0741e29007003642d806000c180d003400104080308190300300d254804404000072506010820100da2649001c3d98101d010622000c040d161782da40c1008490010561280303241541807800c0d01080d11000030001352030145840c2c0041c80402e03401581204820f43c1c0c845000310b8603240500301074820700110185040782e029110480420100312158803401501c000b00404419200c10b049040510000442c4500d140d46a90352620a410064050b004072070041100009100ca2030003080403581c0d41c020840780d400411f00c24000030035429981c04041c4d079064011240e82c0d02071800c086d00c1600945001680c0008082822410040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 457910062 1250 457908812 457908833
    0x402130504241418070306050a020409060b090306060f0a060e030f0d020303040c05151606060506031f08070e0103150f050112020f090103150207020a18090318031a0c16 74
    0x15044480c0b08142c407001318400102d42c20011000165100311014400705400d0390115400c910002001442d00d6524400907040d03c645a0210f014858003054182c520300301801495445003040315841662422140081c411150900442c42000b038031904154a907101000390b07940303004117201222803940344901700a649910071241154424083d050001d40340c101450648030300c0200142e203a0138154402d5294003110380601c0d041c4c441076100c000001e1540c50b484001c41c068001070405103d000404030001419200ca0b5011410b5984600400c00c000c0301498403140c15254041484500c04001307070204405403800d08500b41c00146407500004114115147c40314019100350b0700c0420311448007041068500017440050220206078101382942e06050307000b81a0984020190500c0c0c1d915100fa10090b481c0c0c4004216085556030101d40034980c2000141c000c5900d1056071440b03441c01c5541c0c2d0307400c510114005c002d508194102141248080c0c0060380c9214514241018822030075061001082 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 457911312 1250 457910062 457910081
    0xb060c03280201020c12210c0405190308040303050a1119060c020f0a080f0c06010f0503120a05161103030c011b0203070c230a090c17040213050424 65
    0x1180c440c800c800344a4018025201041041005801b50390743c40c10b52070060740e000070010030f026420300400303030007035411090071074001c4a155043d1030b1101d041209000403400348180140350800061001c000242d8150f080345e050740e0b414505075460b02015401074035948680c1032269094040c034504540d21060400003516864001c4d0024001084a514180e03216400c2e0701c10303140241c00c94060140480c044000130171032014648045480d21903850112410000280c110460380c000b04034007000a071030100f20010251440084051402c09200e42c084c3c06480740da110034030740101c4488642e042c001d9201c102c080c00e4070050280d80d82c940d08601e80e0340c000e050b801c01d5800042c0c41610354440a41c400000d64180640c1b0038004007401e801c0900191700110b10070101d407041046580b40c0e0089403510401d0800510001c840030510f0072000c0340142c440740c00c03503110303c451706001420000580d4458103c1c0d05045440e42c00080d25441d5410b10f452413081032148600d0740e0341c3c0702c49031031150821940050b854 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 457912562 1250 457911312 457911367
    0x2070b0f060f0603012103050f04060c050c061c0f0605060414120d05070204022a0d080703180f14010509150612060f0a1503031101050a0e100b060c03 66
    0x80390b075420802401d40800e005a0b4640865200498070f07038628110322079103990003400e10742d00301200303a00c00d00341c26031050700b240c0c002484488049080000030806540e0700101202c1032800d04081d10300b60301c51009665003541c0710700e1f1500005001250181d201001806001e42071540d034a807106a403400c640022001507000b1680c000341c1511008020800c195094407660b80c1c2840e205403502040085c1d000030044070071080810281005164003400003c14661009003d89441c41c0c01103c054101c0f9001046407003454100404071055000440714080402e80c000101c5c001c840035410301002c46170305601d011080358a050240490144001a620000540c411840040d99240c0c014004500b460905880460384000c020440400038003811940c031495000000540f40308071220014401d481d940144c0110310403904500e0320725028012180c0c043e813011414803800346a045080e641f04070700760305c481c0b2050ba0350700c6484a079650341c1c049a1542c00305208403611000b900c2002ca143c00c266850240e81d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 457913669 1107 457912562 457912579
    0x309120c04090302070e01081605040c030e0a031e1403040807140304060512061c0201053f13030525021011061302060d0b010302070b0f06 61
    0x10030b00b80203078000c0c25103d24100c41910913400603003210032642c01072016921002d01d018002c03000c8410641d40011010040c140071401001e0103080302c1141c1c0100d00b0a5410315a0107094034203d803240c0100b404402ca040302d41500ca150080107819034401c400e01c00640400ca603072001e0800036004a45a4071003c825401c0541180c0c401d0b04144042000070031000b001508044034164031401c1921ba0003135044d01c3c24000c8a1401140d4802410418001407203149039000e8030700b01c0c3c2c10b40c00300c042540d850301c03c0144103d03c848601c444400e402c0d5081000404000344101c007400700c581c0584070b941c9070810b90903902c102c80b186a4105400618800343d0300c0016240d280300e00781c4010143d605c03840c0100002c841d407030900f80003030b280348401c00700000c02c00c000da071f600f00448410045003e0f001070f11302aa140180c0c0031340a8840045c14880c94081000305030202480ca00c2c0c42400102c3c1d0307044 = true := by decide +kernel

theorem cover : BRFrame.Cov 457733812 457913669 := by
  have h0 := BRFrame.cov_init 457733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 457733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 457733812 ≤ n) (h2 : n < 457913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
