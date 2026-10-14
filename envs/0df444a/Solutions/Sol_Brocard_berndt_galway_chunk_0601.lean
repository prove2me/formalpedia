-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0601
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:40:20.95598+00:00
-- url     : https://prove2.me/submissions/b7c1d5ae-6653-428f-9827-92c68263b05f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 107913669 ≤ n < 108093525 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 107914919 1250 107913669 107913679
    0x3020117040f0212060a05010503070602102a02060103060c09050904030302070510021803062410030603171206090f0c07060204170c1008090705040e03130609210b0402 74
    0x981e0300c2ca010307140e042810200035405128008040d0b280900003c10601c01d10040b00204001c0c5d0700d80e8101a500c14483c8940401a4418628040410190f40000c02c0720007d1041d0585c081201410b80c85013241065210300050b4000c4004109000b80b6010b10700090003941000901d01f0b0a240114140401c010005024142c00054850420000b000f0050b1a014040c000f19211481c0880b040303040140303082e010303210b845000b001c1f82e9607221682d00343c030f03945c0704001390003d80c020010140961522065549004c0c50f5440100201141e00d81c01185ca028003048020b640e07030389035015040b03d140009001d043c01100d03120100310317580e510340982d07075008101d52501d80c0d20303100e551600c100a0312aa42000f804600c0c440460b851011001416200003179007141c1105401c1c100010440d404807080351500700591011108019509180e03220510507698142528508030700c40040c1c940e00300d0b590303012a00003140c50b50308003c2c003040503800041804242d030f007041c1c4444071900c85842109000d4800382c850 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 107916169 1250 107914919 107914921
    0xc090a03020d110909010b03010f02030c0412080d0f0b090916140a0b12070219051f0e06070e0102010f0204030305270a0b1305010e130f0209030f030706060b030103020117 75
    0xf0250000c405048901e0050035803505181181006010f4500315520500075802c017034100c010390200340203136849130b81008405802c0c01c0c40d0603805140582d075100d007a105080300304026607180903540240345409540081c049000c9001809000603000d00070030100058100c2c80d43c042115103400544002ca540c020204175600b00345170005004200700b50f01c80d07820321b080020b0400008095080d01071056032103400f61424100c0190014901298a007401030840d0465040010f2034410880030201003036a9560024030117002c03580c10b86c5492410f4a034503001c00c80d503032104045076030309001e05000850120380c25030606165a40c05003490203004081c0c819442021540984004130450080d02000002d2440207083c6d960303d0800199401400f45008001c0b030700c2004603540d4000c1e00e094044020252150580d40100e0a24100804440d245548640e40800c4500b8840d5410800182032100000c0a141d1f00d48261401500319100c1d54005c40e914401440100f01503030300302035160f8610810786410303902 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 107917419 1250 107916169 107916173
    0x414010b03071707061812050109020603070e09062202030604180c140904030e04020c01061505121608070c03050c03040f090c020105040b0a020c0c09010602010c080c090a03020d 78
    0x140c24859100d5425208603540010305442c0003600b034078190401c4080c1e40c20b083e1220b8040f16942810302d0440c07484003180a08010982a00d010000c4550040b0000a415845907000508641c000d94082d0001152500c503080e80d49011240c07681c01600031101455014840d9901c41c0f65501c40920868290b03a005c400101d850300c0f16001201f2840500640d00504135003840c0c801035500c1d0501401e480b000b0300081c21003080c10424507440c0296010385500c84001607050822010b1f500c0200010910b548440000401d0b08810048004070700503904da290b05c552180d1035a801c0c4500c010419080f52001c914150005c98122a01942080003864210066101800e098400d8071504044610780d1000050000710000f48480c10829501108014021b19a14003c00c1742a1441030350040d208801c1790b4080360f5404e1040c0d00810b450300c24030b8151205e0011004c00164444826482800540d444041c0d00025940c0040c034907503c07003091031210303041002e180041342c8451030601009001c1c1100c0c00789282 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 107918669 1250 107917419 107917421
    0xb0f06090a20070602040e0a060b070b0705070212030306030c0103061a0901020a0c061d0603070f1b150e0c100509060f04170a1b06080406050408090d030903050606011403041401 78
    0xb106045188003070f0b03846000c1c4c40d100d8000d41c0144200c8200b280c551010642880b503074040c2400b2541d807041010305240150302c940e626120007400030390910800704031003c016103900c85500030303050800014603124503010042c9804e20741d00c18a11810140ba00c60148001e403200e90410b481d2075003491110743c45a2010005030700c4c018040b02e010300420010400010034a0f40490049400100410003006e901c5d00b0b14140403d42c00709998100c0814040c03003600416a108c0d0198491840035044400041100d944035001005501003881c24440c0d105c180070030b51b9640c10803032050001c1d410340c0c0e940680321102c0401400c500881c44100d1064200142d007810101d1810103035009800d01d401d82c00340440c2452040d42e622032100340216004048814540c109030540d031040d0f000c460044d1100c02050b52240e8400d4010302c40108121070002090103403030103a031220014115154401d40303442c06003500b981006458600b0040209040180d290602c115200707128042c0c07a0010340c4420f0741c801042118200c03034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 107919919 1250 107918669 107918711
    0x4090903030207080c160603230735100b0f07060b1507052b11010e16080c0f22110d1d070f061202090901120b0f06090a 53
    0x140c05041d000c11401200b13580840c0e1503106502a00c081445246c0d00d120035410742d40c1c4102e0501200400041c02500302710094030466000c09103192400c2c4c00c807800840d19200701002801140320300c0720b071140d020f40c410040c000a40c2141d03403042c00101e042c1c0fa140e00412588609003c1c991400300208180c4100701d426002904200c200514140b84280442c18003c1e05800624090f02c540c45100c0b0b0401c10100580d00c01d03074440d4482c0842c414400908403065450881d5010a041e035503590300581c0e1a0f1110034842c03a41c491414500103c40d85144c520090b02d0034030b1078942c0d544100c0340c00110b40c44541e55074240c0a01c3c08207000015404034041c003003c800800c001c02c810a240c0d040001c2c40d0f1860040c0c4d41c01401441c040902c03508000000b0071441c2d50b034501e180a0740030748100801040c0030b018007500341810440e90005000d4601510a00030480d65013083e4005440403054048c05c070204102102e503154008004441c0d03007550310300b00c0c0020f1500d250160134115001d03a10032012070502807170a604 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 107921169 1250 107919919 107919923
    0x30325021c0501050703090b01050d14030c0c13020a02060609190e030a021603050a240f091a0421020f06040b0402010212040e190605041401141504090903030207 71
    0x441c0118003019040050780c818012103080d440d100c0014042400782c801d4011058009903084c0c880d031300f048113100c803002d44124283d030084285941182211020070050074010700b144041d2040100c520305101841d2402018690440d00521600d1b007841e600040003988000210f4040c1090b031902da510807920f0583c80500482c25040200050380d1400c008000d0081508640c01c55002d06401e2064041d20809404000d28a410000c01800070030340f0f4072025141c00c4000c610f03240d81d120342e10652604880c0400c074400340103511a0503040c00c3c0880c02200501170f4950820103c198605a035a4040d214030080c2c1400070034810b4219507605900c204041880c640d1140111400750a160034024009441201d04a0042c850603105804000080c016503003142c02018003540c0740d1312581c0d03a840d03041d5500a000708142da80c2e858000f8146e501c1380554001c9100284841100f5410404868504400c5e4208070340181c0c1911120003813030f6240c60840e022143c6442d070024040c0221324044011340301d41140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 107922419 1250 107921169 107921179
    0x5120f0d0c02060f100e060d2108040302070e070804030f02030c1516020a031d011b03030507110c01020717030f030f0106020d0e010c020f03070f091d01060503032502 73
    0x180200d8150002260fa0081458000842460740c0c0c4000b420107100346802106e10041a40300850550700388100308400081c881c40001c00c0c000300d21100609904042411600090880000d22042c1a018404540a1b14040303101000600d065800500700f80e1014000608005807810b6110324980709005031409013144d0403e03250345484144400c28400400d5518000c4001c1c03e40900612500008100c01c50591545428030b103002c5458514400311185143e440c184000c0c24510b4450400030411101424800e4400094a0a00380001030245501a641c0402544520006009680c00080c02000c5801c000300e110301c0080e15015590441c0a0183c04403041d84012051241615541c1c0405050310308a0f0f08030b0f00303003c0d0030800440d0108005420b00d030100300302205034030140c10031880000f1041c201031700312904560740d0240c0d900940920b50103091110365481d00d001d00c00c400040e62030300901c101c60091040c503042200090b22403248001d0203484c21802d0b0114000101d42da60043c1c0401d40043c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 107923669 1250 107922419 107922431
    0x70c170706142e1505070501060906090c110106060813060605091015141602121e070807150807020f1603061103100b0a0302070b131e05120f0d 63
    0x14a410035801d00c8141c00d02180c1c8100f40da90b00100000e540042124680d8201c032016804881040d07945034843d440a0741c15549801022038119414000e85c1c008021803200020007515109004141d0150b001c1003020503414880300304482c59100e0409a0011039030307080030041e44030310326280b4000c084a038001741c0c20055160410042d028084041c0045075a503100a030b1280c080f07180100c605c0d111400003010300c09000e01500170f4040c0302c82c808041041c4086c180741075242e8481c08040c903120300740500e580d40c1c0d4002c40305034100c4241407001800501003407004002e001d05211400100403208200941000030140c00100c400d8420040c080c4500e500c641510a803400c0588501c84440442c00240c03136490514140d82c0a60550b1801c582c80f07991400c4080ba0424100700d40448154005800f22080540a10410000c42c41c0f0310b42d07441c0103c00781000c0202241140c644041d104030b02c44020b80c000f602c40c00c0560081140800c14458403e59120a6a0380d40d480048101d00b03800341c0b001040b04907240003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 107924919 1250 107923669 107923681
    0xc010509070303080f010b071104060302180114010504080606100201090803010f060f050408030a0f09090204120203010b030d050d110d05010603020315040209010f03090c080a0503030f070c17070614 87
    0x1280035010b4074001d070784844895580d000058000e02081c414201414010003000020402c00c1803002c00320903008201148003a42c030b40009040780d4216100c03c00881d03a01d4010048170b05100740c0c8201c0d1490030708042d418145030407180e0380c41c0c007001000980682140108070002074801c7d880091001e9109000c95120350315080c10f4010f000b00c5000e42000309002c04964011140070f031055408644c0303060b00543c0b92040130700003200e00c0c6255480c0002070120000002c55101d0250021700050302c40880750703000b403d84c5401010700b034484505400780260816420054029840303000c8070a500009040443d0740c0140041010300e501c00c2d003800b000c88628100c00420307540d5150700114020240b0312400c080380e252520401080f4843c00c0011800302d42c0ca003d01e00461b1f030094011140c05405001e039100c1082d0348010030b505141550100321281e0700008100086a918003000c135401c0100d52608000700d804c4c990302c841c0481154031407990410004140101040841c4c1c014030340000c02e00c600c41c0782c541401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 107926169 1250 107924919 107924923
    0x31002030f160201060312050703030b0a090b03010b240307020a120905010e03070e011a0706060602010c02061b0306040203090c0301060f1406131202031c02060f2d07050c010509 78
    0x7901c101c5030203420b4104003440070b07105004120680b80c01000c50f001c540c00052040d11282d0051108a00380341d250102a04196504910500200605e81001c038401802700105401c4480703c002c441d02c81d00000c890000c078508081020041d800c20180d034940c1d281c888100603071400c04e00d0b000040803203000f98600321a50b5030218040084a100fa200d45e0044055901055240c07105402404410b54045c03004101c1c03e240c641042070350700b14030081540b501040e6100d16050700d2603600300c080541e44035030744100455410440980d00070550f8000c1c041e83c8910b840980c01790700c00a01100c0c4580d4021001c04c80bc2007080c07000d00d044020060003007203440c1e900c2c2000e81c00558a03100344502d0020400541c40036042003c11140b03000f01140c50441c010f410300d02c01452100622805a815224000d007909505442010814016042d50001e2042e0701e09522a10b110140c01000c12901d10844103800f01e60000380707015504011f104000340c0003d0b9907000c0046801d4059235440003850760805050000310000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 107927419 1250 107926169 107926171
    0x7050f132606060d0303051509010b040608010b0403080d1109040e0a170a050405042c160f080a020409080f0706021902190f030201090c0e0901060608091209031002030f 74
    0x1c1d0000c0c008203080210100e856907403c9502039042009040c0340000284298007040c1c4c0002c182041c84079840b03500002c60386400c82600201403202d0000740034071050b504030101e00c2c014462412420300d49030855503004035034050343c060402c60546644220f1949d490f20341c02d48400c61400703081000303001d4250f00d8443e9514042d01c0c055441080c645410783c0303e031003054111120300129844803072425240c1420f01004002c8a54030507601c0300c040502d0b65031030100d140c0d1a1101c0c90910000e0601b84581400000c0140080d8480b9106003030703d035010042c407400400c40340e0000384c04680000e0903c2d0541407120280c402d064241000c2c1000194200801c2002d03406031078018024841050004200b04007680c0e1041c04609000028400d52610400100c0c0c46410280852280c0b0001ca010966a941c50324148915080384142c002ca042c104011160240314070700090049260008450a04d0800d0544a4004000398074081c0800148440790791410032140c05500e4181e441190b0b28904840d0000403840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 107928669 1250 107927419 107927459
    0xa030c2d11010905010509211009080403210906051b161a1e0f0d020a0305250e1e0d0503070c0e010303022e05011412031207050f13 58
    0x2c0328070010885510074801e40d1122607010f0180480c0302c004100c18000d58604842c01201441004030b08842074140d2b000e031007455441046215169400c41c54103980d84940d40514003014945664a540c109a108803000c04507070382400c0050752454003c0001c0c507000003450748040241700e007480d04040259003403420380403610503e00021514156842d4a011752080c40044194100d006039240d101900c104000c0c02540001080d141c034100000070190140d03040b00c100c50000c40d0ba55400c0141d9015804450005e440040c89403451310034010348042c040d00c0a451059010310500d00880d00303940d40380050020840401490401d0380302a600c0d2039a03990f031101c10101e0355044c0c8000c0000b110b21110856906a80d8181c02404502c0031030030030b86080711030105444134205500b401004180c48107120340c0d400382482c444402d03400c1c4e100409100c040c00c040c1b05100c00652040000d031031234050000703016400100e54038005a0b20481600d410041e0f01032049100c16608144100054560f078110040c00605 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 107929919 1250 107928669 107928677
    0xc011418010f02030c04030327030b1b0a0c03080601050c030c010204141002100b0409151a190b09040603050f010603050106060503010e07030b130c0503180a030c2d1101 74
    0x82e000c141800d050f404140da502507411414441800041d00550880181d111006030314404506c1982d403203018020f45500607502c088106051040003090840609007441d0008285407420100601c002e2600c0160103028040144604c0858072503031250048400f01440c102c1183e48900348240714a00070341c000d10808843d174170242400307102030030420b0030920b00d10256005050b51401480744100588100c141c0c1650103903607040c40c00c00007040c11810100c000c40000000808140348440c1d18042071205040034425105400a0003501d01c4040083d01615032140c0c00c50345a6100710081400f5280c1600002c10b01d005070700760403807040c0381544010100c90195000740840f5540708000d40c1d0030b01c0203002c0e9004071a03007880082c44541c025040031a05450291602d141480f00b2000c43c0111041e001d0102c00003034000082c081e4060b05007040001d10a14030020701030b885090380c3d02805012000d0001441d4210054440030307203d00d183d550300000c105030400d402c020061464038904c400c0c1d1000c1118085 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 107931169 1250 107929919 107929931
    0x2004090803150108090607050309071203020a0b0a021c0b0402091206040c091401060320030108150a020309030a0c0f0515180714040902040207060207030e030609150c0c01141801 78
    0x20358421084c0c0c90141407402c0c00f8020540300c02c041120300e58802422030000741320710341000070400302105620350214000e0303015100c4900326140090803039030080c20b510111801400a1200b181c1d040c2c500040d80710316070000045164000000c280a03018901449502007414080c03846280da01045891099200f200940303803082d15494201c08031507170710382c0010b50b0400e02d41c01441054025400a00c442d024160080c0044a40303800000041e07100f40c10900d10754000d00601c0c80e110b020560595003086418005504500e0003000d840d0f40c03030203400c2441701005528010305013132206040800c60119006020f8681c0c108101d94208559401a1507050000041c081d20150f00f00000c41d8502c25a641240c0346000003840004001c050b210303800c0b081e0f0b0f115a0800c00c001c00071761584020300c44148a91aa114003d0320001014140382c00148403a01c540c00c0089140c0200341840075150b072240840003c0e648800410380f095004041322817000051282d801c0501451103410070305140103040c210001d000c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 107932419 1250 107931169 107931211
    0xc0303110f03041202030c040f0c12020408030a03021e0703030b011d030a080f04080303130618030f050714030309010e060703060302060f07030219080c010b0405070c2004090803 78
    0x1a4181d00102100c542d0010b000a0000f280c141d0762800f00c19000030101c8980d444c490001800711402c0d4203100d60702c15614090000003581002c801e4140c060b184504500b0706241c000c9041c1c61f8800d659082080503400a105504012404240d001e00d5000c461851b499101d2450050001c09840c54580e004c50211740650445002900c5c0c0d040c451035010b0003801e0722441c2d80e60748402c290403180200114400501003c224244100080c61042c20403e41c50811018607042603c00c442140b1161124880102c403680042a040710ba12140001d00b89000c543c1e4001600345651000780d070555541a070302002060066500054010a0101c0400d03010f86266890b91031058040b42c80a2000940000f41481503244490110014181a5000e801564402c0c40c001d01c0180075017000c03800c02c5441d490085181910f8607030903c1942c00003803055030100803034201680c02508100e50402c0080102c0f42c3c401100f150a0548103800c3d030140b2000c2c2050118074054542071a26410880d118034918640d4030000c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 107933669 1250 107932419 107932423
    0x30e04051b1c1d070e130804060503100e0406090201140306030c010804150905060a05070f0804080d15060509030f0105010501080c130b0d020a0305070804150905070f030c030311 78
    0x280600d5420090b4a40100c4444845080022604407a15980e4400350307019110000c12003a6841c6801c10050300005085c14900207030a05c0103000390b10750500b298104c0f000202040115400d5982d41d0400540340d58403440c03500b18484a5400113142d480c00c400c24041000147c0d000440000e1007600e0716560035452030b43d20034282c042200c0840d415801b00d403034500254064901503030028047c000c01090300041d43d02450503219140800c40303c0c1d44c0040e0070849104020b10845421180798502410300c0c088100340202100170140001d04070700c20001d0303415122a46a40015100e19140b0003800c44076039181c2e80540181c1002951034040d02a84803400c51444061107124180c0d58141c6940d203c070f8a601c00e00d1070890b01304070010b2046050b9030340042070008001c00a001d0086260001507944c01c1d40803002025110040c207000288050f11080c00000f81c80b415641e00c0300c2d49c0500b000110700c61241049446d05401c0e80c003124240b480c0c440c0110910407100d07016800d80340207444035900f10301d141440d01c1d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 107934919 1250 107933669 107933701
    0x60509030c101e050c0f07060f0807021c020f070b0310080a0203030f0318030408010b0a0504054501060e060d0c0e0a0b0315010302030d02030405031506040207080403030e0405 77
    0x24000583c1c0409049421110140100c1110400d1800c58185050b07400510703c0e20f0035007034000800703600c50201017104590144c0d448100f601e05250019144c100200c003e50b680380c40d15000d0240032801c0e500c00d842c0c984204400e0300e120780c4032030485070010f40d42d01204070194010b4400325014580722801080d41400098002030f0740b580075004504d0300500c0b08181d0140e40020380f0700c40c21140c0e201d4054001d01ca04201030005091103100004101c0030304c00401c41d0041c0942e2103a40201d0900c03040100b5481d0b040801d0502841c2c4819003203030291141c4ac1203242e04c8007030140101c0216124507290140b40158094030991760f0404400115885102c00c000c400d4000c0302e001000f480480038140b0541c0901300c22581c0084100c0f10100c1c0d079420f581c0003c2e00704480110041c040c00150310040044d441d04000c8040602000d001851800c0e0078000403a445003544014599040404000306410342c903681d04a49506403c080340a072541c0d180d01e8018440d005c8141694030460504004c11514010800c1903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 107936169 1250 107934919 107934949
    0x6030606060a080c0c031b0d030f140403080c040510020a05010f0b0d080903033001061d0111070f030302031305060a0e040903090902030108030c1c080f091204060509030c 75
    0x80f0702d2940c3d5002c00d201031039029020f40d2280380801e10034a95402d42101c00094666100c101038924403e02c181c004044400366506201c02a09101000c01c2e6406000f44190f0013641510307000c02c0984e6099800c4456100b10350180d41c2182c0c059030000e04140e400309003201841e200340024003040224924803c16120034280b4a0303072002c0240e001e0b00c009030303440b4002c01c50f200c00a8241d905000c0c0000c0f4031120041a0390000000c02251a08003c20408007801a40540180c0c204404400743d818070100c0c00b002c2051209060104e034450a644030f4204011541c014440f40070b0081080703841c2d1500039165040b0002090340243c2246000c5107901d080350985000c1e0f60555a4031940207240b1003000045c0400910507400e010322070710301140d012050300095010b003030214020b69454140403082d1b0700d011085004444004125182c3ca0b18495003e60b240c6d4202c8154038404003191100f5000c41c1c02c06100080100f0381c58800a000101c10f40c000c0060100c1e001c0c120166060700404400b07200720300190b8081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 107937419 1250 107936169 107936177
    0x18100c140a0302060c25060f0606030c020c10020615040605060711010206011208030a1e0903180f030c090b03030d020706061505090d0818040f02070b100e0a09080706021206030606060a 81
    0x7031000d001441074401035240646008207422107142350b40d904803a03042d0000c60010f030301c035250111066010040202c0610007600c1544800745442002510303840c0c00b40c103e150014a061003010f06a0b00d0b070300700e00301078100109a242e5412451070300303501c640c0e124540c060150003003200005400c00c4112100c005142c1003060540740d584d82441e418000c040007488507101980c002c41442c0c0d0780d41c0c20310801000038825212409084114180030103024019030106d003c0051091041c0f001501442103281100c00c4010041091800340c80000c2c1140102a0f000320501d2000c80e440003400000d422031012903502140145144400406c03c455912500060381d8120842c12184030008120320000c140013a0030721030004081651070002429100c0d203280f4251040c0e0045408801c0c801d480d103d050b00010007800c0300030001e16100b0415500e440c01018014004d65940540c028480d42a0884603043c0c3e00038030865540c8480f0300340132042c2209980e00e80c000d10908000640c0d40c08e100701281c010700d4058603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 107938669 1250 107937419 107937457
    0x403050606271501110106051c03030e03031003060f0501061e18030506090705041b05090a05060408011401050102011a150c01021b100218100c140a0302060c 69
    0x520405109402c091884007000c0c00310b0300b00c4048500b925601541020307101c04907596028000403d0483e00850190303c0d40d24200d4100115950070003071032904c001034039401c00f007004a41402d07001040e100b00c3d9025180000003c025080e10714950050540e0b220311001c0200d203070301a980d802161000d008800c04914108101400051821600900c4c0c03d602e2802c025038103080900b180c074085607a84103c03500d5001350140540400f05100c0324002d800156010000c640590031200707040303031159099030b00b40b10f00041c02d00000d4480d80350542c050030323000d011190354544d01c910490082006502114402820030000300b8a0f41c4103026510b5818400f02607441e13004110300420101400580841e0355455040044584012b002c3c0082c0512100300c1d1461040e4003081281581080131049404c01c800380304200704030208090401d005c0700480251102180f420718410141d4103c44142005014150008401105c41000003035a4903214881c3c2d080e03510949402c050040300380620800e00d011030902003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 107939919 1250 107938669 107938681
    0x3050909040212073011091005041b1b0c051e120a030f0e090a0b0d061103070210060312080405030d020a031a121c180b0310080304030506 61
    0x854940c0e00980010030b00c440f000c0e9140003440ca00001903020000e5066507100210030030040d50030502c20405540a10548149960303a412542c0020341c1d96240b240e1032410108103c0c0300340703205040241401600402c02100c0c2a003034162244142c4c110480011042d0f465036045402d00408000002d80c002003413400780b801c01d01000115103452410701110043c91850103001e40d07410240c6900e51001c20702030051458981402004600600e244409102140c1d0b16510662200009030b03074000705441000588070f08d508006201100c1074500948a01d0402d201d901d107083c90b09e4001d60044545400300c0d10b118901c50004019120188005808031000301d0404c50028080d0f07415680c0284250140e03858118102909000c90f0012410040001e544074940c0c542d412141e480100341200c110f4100c074021200aa16580e1000a20f028038000300340c00304c2142104e4010b04403415049005000803500c076484150090341508101c985191040c210440020440b102008450030340f41c018018000c203503540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 107941169 1250 107939919 107939929
    0xf1e0302040b01020c1c05120c1002030a091b0e010f0506070b040201020c120c04050c073201020a0509041109030307110a0509010312021e0a0212031e030103030318030509 75
    0x600b19450541c05404803606199641038000c80404200c0c1006500c0b0240c181070040c90404148420460008104940c0c281ca40000440d03030203501d0103a0000d6903903a901d0040d44041c18a04000406070802044034441400e0455040d5040d1081c1d50345440d03160380d85040d1005c94440c0d600c22242c1020003000250085040050995132040c0180115100034051101040040c20060a01413494100807003a0344c09241900402d40c000c104280b1080c1840c41c1c07500e078001d030500780f07980340c0b05215005c0107802c07101b0b154040e641c40ca06042e00f00864441c003000201a18a600c01c0d0003051103039260401ca0804e841c02e41c0c043d144005000780086040070100d41c1d94200800074500b4566020114080018060340c81300c5245000c1c5204444003451054a844043d1501d0500ea88450000d8038044200c40c00180018201c841c03150102c1c1e41c503008003d0801c03100d0031481400040a6024421f02e1000d62244c8444021030403241702e543d0802c1000c004101d454184822018001c001403020804c0010034584 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 107942419 1250 107941169 107941181
    0x9060607061a09011706011202010806130605060d0c08010e0106051c0e070b0910030b031c050c0a050c0306090708100506031006151704021f02030c070b03010f1e030204 74
    0x10910b1111040d24000001906118240d01407004415051030b83d440c2d5043c240040c500608d0b42c01d8900b1030b0b4008a0f40041c0a0f85001800309003e0180a50f049801031042c1e0032a42c01001c0c090505559084800403400241250210301c82c0031600c2540000f50045580b84940e040341c10a0b5101d0741444505602d80034401c0300c001c08038081d6503c0741c450100c550001c2c4010b81c02005607500700c990f19400c0da01480500e901c03080450040c03603d080005141a00c010030481c941c4000e40707000c001d0a50004030103884500400500a04078403400c3e400c7e4040200000396103454810482c129011aa102d04030541c2e96480c6018010081d0010b9861010646058110075040b0200a00f80c582e4000916000e00848109901c030481e1101040340e4982d1250b044445800085040030f081036070340c03034650045110380b0251000510101020314100340441c1c0b081c03090f17502c40c401c030b001919892030303441030036403142e070400c1c001c0142103ca00900080ca503042c0b001c00300221040c05540004d21442c42e001c000c000d0a0f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 107943669 1250 107942419 107942441
    0x5120702011808070f05060a1202090a1206020901080f040312090f020909070612090c05090402040b0a060314060607030e0906031e0304030c0609060c0807051203040b040203010b0906060706 83
    0x2000400c07144400050802030b400742503044024510145030464080040038141d01440c06030b0001c0020480b840d50003183c40ba1003503003890015035192030001c00708a60812070340c000c0342003102c415861010060190000c06442000f60703031703501140d244c0040700d00c03401805480c02008140210185040001da9400002c040c82c0903803d1042e403113100d60041101048101c0d5958030f01c0d0445001401826048100c2c048225003004041110240c10343e128483d100c8180580d40c80340e520400090700315a980e421803c00b101015000c00007007552060054090000a40b0401005020364001101c41c10240180c0301281c0e0140e9813080001e9041041c404580e1024165035050301480a5081203545401c0a58160b05142002955503618600b00500d101360385810080800802404c100f02c0c82d64024009805590031180c01a40c0b000e441c68241e18101200f108044010b40c04030030881808a44c0c511a03201c2d034000d40003400b140d0010810060100c108541160b0301102c18485034011400300d90043d44801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 107944919 1250 107943669 107943677
    0x1d1c020c030111130b090a12260a020d020d0207030611040909030908120910052110140a0602030f210403030618050403270f0b04050a080102030601020703020d081306050306031203040512070201 85
    0x4984803210000c217001040030b100c660000040d10068ac5641000348004035035075480601428026100025101c21440c4405016291107070310f2480c0c0d1440150460b4018180d180c000c125194080c44c01415260052003030251074010000e0000800c0980310458003c400010005400701e40c0f990401d883e1a00000100f48048a01020385805290721079034050280300b0307004140100c540b8200071901d9081d0b80b070903c5030040d1a0340000708405a0008161212201c03048a00c03a2100100004e40200b09103150900c0c0a0204040600c810706401d648044240d640c0369000314411040907040d4404c0c1c1710180d400030000303504008001001c82c040007011403a041074903c0180e0483d92003c1c100058000c503002145580e000007010002071420306c01010040040d00029400c500d82000040d45403a03543c80080c3c0901d8406800c0d00410406a0499410b01e501c86040745d080c0361a040003c125801c129440b80c003074400c0f4101038013a001d0110035a442594808000c20582049411701101d54000c3e80b0224144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 107946169 1250 107944919 107944943
    0x5010c02041e0518121305010c080d09061508030702030d0e0d060501090f0b0102071d0406020418090302070602070308040902180d0305030702011d1c020c030111130b090a12 76
    0x204680107844c003520506100940340200b400d080340c1051040d1311007031019481004201c041119840802c400c0700c1090800031150803103420852494401e01c030101d24041d241485800820406900c011405400c4404a00e0031a440381000c3d40c0d603228408000e0f43c50303400420203481880c840c206540b8000c2c00a801c2e0350a500441d910a400d0312001c0c1c001d0501c2503218048080c94112030b01c40c12800200074401000340ca450001d8210310680c1819414101e80c802d00009000d2107860b80480d80106540c0e00d080b90b1fa4a019101d5000030401270341d0480040c000d0010002e9510320010f580c800350ba410514583c64541b030120b40c00000e5101c1592020200c0c85e5607800c94040e6241c60701b002c1118002d40300d0b9039a0f4640140001d00312641d10300e6080c1d00206009038001d28910026016400c00501c1d00c1200c00c080ea00b104c00e91401103883ea510b5419800c168100d200f80100c80f001c4c0400d81030a0700c40d8450161071b68031410720390180e1031809800526940c003c1112410a207101c1c400a0702605c844188 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 107947419 1250 107946169 107946221
    0x118150b0402092e05070b010303230406020604051c05091e0406060f0e040203040c060309050f160e0f0c0a120207021801080c030109051c020f0303010e100f05010c0204 74
    0xc0c100d5611079241e0010700078021a244018190041904e0340c070710b880e086180200036503d06803140d0042c080501080301c440b407032600f0800c60846800300d040104007683d03125a9500700083d0b507504200d50444c2c80d070241e0005244184c081c6207401030260342d44c1e00c660b41001194014401c42040b5420740c4020070102d1540036100d0b4456104640141c505561aa1103001e590080500000240400380340120300c1082080041402982c1c804140c842600d80494400205d003411342c0b4003450100c1c9117130f00d4012504540f405024201d0100103c0c4c00c5001010559a59842c401c60b40744c008a6414030303d8101044100c0800f0300c1500c90640024200c0f80c01070074000283c0214010642d5a69070b80744400c40c2d0401032240d1001003010031413480b400c078001d00105010340da030107413602c41c1e0b80e1b0f2489141e80c400d500b52940500902241021500c0c0701c0440f0f46940e910940524940c005981c540b0758200c4048005c00c0d10048400c004081d82c41c181c40b00900079116a090200800d0f51100b8000d07046400c01c41158 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 107948669 1250 107947419 107947429
    0x3030a0b1c111203090901060f030905060c03160201050402180403050c1902120a020f150c01021c0b030625030b030f0f01060b0a090b0307021219020118150b040209 72
    0xd840c1c050010054205040802d02c0a83c4048500c800304550040c86031021a07510010a01c1c1500c1c168503210440c0b1240703280c194050814200c000301503018540800050322086c41c051485941c42c10800885513a05440070b03401c8440035200030f5080720540051f018400e04250f00c1c590401d20910f86140b0308003c001000c0d0070a48075000c80a603c50784003a1610643c50581881d849072074440002c1c222016041d40021001e400c0107203090301940310800801c40d441603500076201c0c0814114000c0d03540e500306a00a01592210b11a548592447d0002c0003566060005002e0310450481c1d03000a8082d541c00300c4000300c03802c030700300d69410192200001143c030b8030f0502c400340c5100603404c010400107079240394407400d40310b29400114074110140108480f8580c400c000204488a0f40401903617621029001c90802251202902c80e403d0000b4000040365590040c085110f0b01c81e6000300201d4100700b00c00e9400b0320030883d014009003100c102d031542e040e4050784014042034005000600e070101c08404a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 107949919 1250 107948669 107948719
    0x3080c0f031201050f01031a0f01110a0606300609021f02060f01060503090a030c0507091119081b0310031401020c010b0402030106050f0a0504030b04151d03030a0b 72
    0x4200b9810718010445030030408455283c04400b42414454a50340c001c818245502540c0c0346442510a01e0003103486034000c2480e0648142c10b00240c0e054809030742015405000b03248104080c81119828165404003410690481d103c13200c42e030404090b500c0c2c1c6560018145685069910400c014844d4900b210200d1351101d0150f42900a44001c0ca030105012002c0031050784220705119040080105c079040c0850b28000807a81030800320480e441d14184107150880d035030030003101203151100c5100d14844070005070602d204003107030300e50141c00c0b000b004545004040d1140c081c0c501c44007424900040900001e95030042c0120054a62150b81c1d8481c2d2080c20703850040e2003d00e96000422421189081c0225010001c080e0350a40c65540b411034028102c1c4502040301000d4000072550703524a5104804a03001550402d21002542c2490704001c000d07408420304219605180c1284803401c055410300e210032503401c5401847c00c5640324448000500159040142c2c0a1030140300d88508480440d420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 107951169 1250 107949919 107949937
    0x190203040b060108070305150d051f3606050603011803031d010b090402040914030705070510021f0c02030408011a01030b0307270902130b0f0402070b0103080c0f03 72
    0xc011500b07100002401241d0043c0c2590304050420041103113841c148824042c2e851f2069840000191850400700d00340b41c1e1080e40001d1464220780c00c01e1f00b1108075006955038844068024001e100202411100300e00000c61800485c80782c0c03020300000c603003107920065100101a0000c100c1d000d14420360021030902810481c046a52181e40c107403600e844203010845030078444000c0100c50000b10001c0c038841c41c000d10080c0f1070f40d2502d188034100030408091007030781c052440841c1d0b02c13604a03180c0940c480d0180e0207041e000b400b6030001c000d4007501c0001c050616284200c03480350300f40207540512000d0b00144069506602c02000005040c0e1400d00c5425038007034023119030000701c40509000505179207200304038034401d80c0a0f88003031001011018484c2c024401600c92419504226484400686200000607501c1420b050711040d003107410b6040f4104000c0110359843c032030100c1d40b017040200c0c02100e1b40030700081002d030010300000740604000c10055101000301ca06400100b004030349564031880c48 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 107952419 1250 107951169 107951183
    0xf1002030705160c0e15060d0b0d020d0503030a2a110102090a060309060501060203070503031906120b07270302010503091207080a020d03140a05070903021002010c0e030102090a06050319020304 85
    0x8001c1040302140710b94014001c8031903501111b842c44001240740c0034009864064640d80c4a80400913954880c0f0005026405802c0da0082c0d27103e401c00945076042200d481800b01c0c1002d00008600f02d4110b200e1f41c404d103032140d494081d290064001c0ba0729540c1d54081d400036644c01c000d80c10307540d6209414100140304076940855001903516080c0280c40043c0d2001065620500050000031004000da80d48410455002c40a48154120802c080d00841e030000350081e8840c40315206000494250502c1242e154540c5819410030f04844150040e80204001c101d03028828180010340c030403c01160440c03d120211a103400c0c181d005105e0399845010119030400f00041d4007807070990140848141d040550604100d500000709101802c1d40c001001602c0055030f502c0001c4509000b50b81e07540103903802400407a12403a2044000e8020701c0c505a892000c210340e1561740109240500841e10042405030480c0d440d5440c0c024103803210b420251040b4081c0c40000140425200b9030b101a40c419030003010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 107953669 1250 107952419 107952443
    0x13011031306180521070602070303051608040b072d0504050307060509010903060507110a05012309031b0f120909060105070b040b0a020c0a1b080f100203070516 71
    0x380100403500c40c00741000b03a664904070a1001301d4008160b80f240d00fa0310041010304900c152105803032038805c41c5001040746e032003c00c240b0281581a48003600c40c01043c827801e0190211503805a072010400c54005080003a800c0006104520a96031140c1c00352105066494140324180c0124004020707400203000514085410801440d0400500b40240030710b0400034035001071030000a082d0503107400041c02140d1180701198101d407140700c01c0588103110304150381d00316100340342080c061722070718800760240303c4c4425250030440401c80b401c03801150a54000c601d030411016440e03030780046020182d5014014840101c003115000e011104a510400107000d5030360103203c00708200c02101600351410813405011440000b001804296006034002c60010a19a1140b00c40c2020b4469204241e07070b5406240c4c40c07502006040c0344205007200540030450781c0b1a48480b0306545d103803910823001501d42d000c5000001d94103070079802513030080c0f8507240c10341c50f01814649503402007101440444041e19030781 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 107954919 1250 107953669 107953673
    0x1906052514012003061005070501090c1a0405030a0f0507050901030b04030206070903020d111909090b0f0f070e01050f21010b0406020a081305040c050403110130110313 74
    0x32290b00f0041e03078005600310302c6041200162040b80030003058140038030f02520180100301d008500380d512442e4004024030074410649081454500c1910a160844902d00c41805140072251f0540742a140090b00506c051080b90f114516448100c0310300b5591801030180100352034841008241c040c0d8041c811514550800d450300a01c0d00340c1c000c100030300b0001940c00500c01070391540c881410341381d0444100021a051000024100d50400400c079a00840c3c0840000390100c154020a05050140200c032444ae1b40d5501040701081045510088031080744002500c0c0a00420000303c0c5200103151041c1403810700d0f01c54000591007607081d844841404c1c800301c08100240d00f00d45014120f10400c45081a142c400e010f0358400341ca80c3c004140d03440200d0b0808000d001382c015080289030042084c8074110311901c0c040c04540c02400240c420310300b901a0002294040c0150030704074052002515850398007410881c484a07011001e6583c001e03190301a180043c000d0038082c60056590500f400c112001ca8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 107956169 1250 107954919 107954921
    0x90907051c0b010806060c0708030c070315050c0f0f07080310032102120906070501020d020705160305060112021305070f02190b01090b0a0b04060903030e190605251401 74
    0x511204005007440c0040a0b01d9910440444d004101920410f03200e0601480c3c0d141440c0035600442c0441c4408a0408001c91002031040103d90244202d00300d0230080c60410810355400700c1c0c400700302c0d10742080301003028003e010042ca01040d071041e82c1030404500c0e50b01d040c216801500c2c0312010340c00303029062050040d01201d006a0b212020806031800b21121400ba4540c9480c11824150309804145085140c5036030040761900c40e401b80085640d19126a043d0000b50440341094030b0601c54507810308101b60551001e0f03819030381c1010003030409a00e450440501d03400b8103603049030040e8102d10008501c28403030180300e02600303540c2c44802c02c5241004000303240042401c048242d4982c18048800840c075440308040c10350b9050308010030100d80030300106103041c2c0103602000410800040c00030307103d58040c640340c05903440ba5441c025650445010070881c1802c2e881c1c03100004141d08410030045008600811030490780e8095941f842c00003d804a00301001050180c1c0d000d40080e44074501d5001c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 107957419 1250 107956169 107956207
    0xb04081b0a02030d030e01060f03050703110a081c0912060606081b030103110a032a0f050105030f0a06150503180123040302070f06260105010203070602090609090705 73
    0x600600c40450745400080c4d40d0a01c6144203018166950000c00707220400390080e00242040b4011509a503a403458015519007451206643c40460f0001e103030090300e4041c800c00225141800100808601400d400c8410f020100381541442105200042d0080050030111030441c0079003c0040c03400d14100c3e024004110085c1040c1540038414645800344002c030041d80d06403a04170b120003ca0a940700c01003018058943c0010704201c0000072180f141a40c030301c0f2617080d000401542e45600d00daa941a0300e07a90741c1e1078015140031540500000f00b185002450041d444071100401007545a0356000c400101c3c68600e9032140014400010801c0d0704003a0174142a14051107802003080401e0900c0d1010400401080510b451031080081010b0600c2000b1200c00f0301010940120066030721100540b204e07480e43c01d83c10707051114125502020984040e22070489034103801861910350b290303842100035401b07003030503643c029001c0c060b601294442140301403103900795860726035503600e0b900400001c00f40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 107958669 1250 107957419 107957467
    0x20a030306050306190e12071401060501020a120e0a031721090a020108090c040f090506070914060702011404080c0a0f120b0c09030109050c10080f04080c0a0b0408 72
    0x40504107000c102c0d107401180c036000b07102c0c0c8500000c1b8118980784a50500d14810003118070000040782c650140b0004032046c411002e4000b000704040790360389005a1710f8039030b01540074104441d149481c0300428000c0710681001c68004101e08242d6031a6540c00540c00c04000090004c2070012803402d4070140580742240d84444030300c42a528a190030251b0541d51284540e000341003190110100da203600301000410481000100280201d8000c40a00300080800c034a0940703051243c034011807850b60094001e031040c2c940800e048941d03210b84006029495100260481c1002031020495020304207030b4015001a28942019000c1c0000d10b000300905100540c000034031400216004101000d085c01c1c400000f10351040c4c10310740540e506904618030380511080e241e0103508028140d01001b90208a0144040c0d00320780c1d0840e40c1c601c5c82412074030380f1401c4a0355501c00c2020340102e0040b030b8008006d440c07042e00000483c0c0914120396107080b1143d40076201215044808078501a07820031004d9280c0c1005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 107959919 1250 107958669 107958673
    0x11010b0d02030705040b0d210311031005090907030203060f060a081b100e09090d030c050a090302060903011508071a0903060a360605010602011e0f0219020a0303060503 74
    0x41500003c0e1200d54501c1203030300c540e6880344d40d0205900c1d92078400d041640c200440d03000c9607503080000b81d10f0350801c103080000039203410240e0000d0704805040c3e80c0500344004a940b20b40c4c0c100300501141c2c2d803028180300518480e00c000000160f6081050342d210740d4805400c00e0240c00d105081c8207000e40c09410005903030700005210031140039031407403030b40090404582ca50f189440008081c0c42c91080f240100d070b0001c010004201c02a50000b442480f0301090b69020031254400300d404445600828000d100001c5c9410720030030144c500300000e01500c80004000041d401b8990440b03081181959202c0c180981150004103c800075900b9038a40003160004000d103818080030002c0d848036002001e51910551740c2410f000641d03080d00b950740d00300c00f21007080010f140c010302c0c40f000380c580c2451080391004d0038200003181701132040c0030754020302c1000000c00c00711030510a800b5000e03010b0150300c503910641c00d001c904c1d032400e2001044030a14840750003500034030803a410001c042d200c45030413081c069 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 107961169 1250 107959919 107959939
    0x20c0a080d0b01090b0a1b060c0c0201020c06030105030a02040f020d06060c1202011a100903080a0207050909070317031801050c09040f1e0e0c040f0608060a0902060906091f11010b 79
    0x50b01110046070301807180d52800347c0e044400e0418809108034040d00c09000f0b107140c49a1b00c112950400000444079000340c00700d40100701498204000e0f4442400b03050341680181303904c9801810f1039044136081000e03050002d800c10390420310200c110b0720554011000140e10f40410030030b01205018565001c003551000303000f860b20706001c00f032110100d0b102d858040d906441600107114803c814450280d036000c0a41c50342e80c1d0720382e84020340d1507041303004044c803d401603004203140200000300d000880368042c1982c100b80d0200c000c040d6075038000810403070501141228140c50740000303101e100e22450a2800c0c1c0b64540c4100c8051104030f5038484411100603251551300441e00084048001808000100120b510305e1020189801d20005a6247d500141048201d1032000c1c484d40044056640200486032155105c0c09240c09482d5840400ba40104c0204420384043c20444d0003000c0818000c0c100d040d5040c2e00040d041e00308030350100d1001c0007a15a407445c11501c0028003651604035002c49070840b030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 107962419 1250 107961169 107961179
    0x1c02090d1b0e090a02090405030912011a01030e0d0825030614030610170109301806050f0405120a3302030438060a030f1203020c0a080d0b0109 63
    0x680c00980d103019106e481041c0000e000c002c010021a1a0b1041c01b41040403e204040c0f039142c0641400c070f420074402c2000311807035000355119100b103032403040d08100100f100c0c40300300344203403803410780601440c0b04240030000c1842c2c5003140303e0700317030035640c3c0540d4000030701d2032070007580341c4038070304401d40d0039200e030300440c05100c81110008881c0b41030321005089406d4007003030b00c0d015030b006085401004111028011040c0c8004c141c002c244034108103002c3c44440101007026040740c0c4081d00c0e40303411115880c800814004ea40c4154060501a88510446490a81c4070000142040241c103241c284551000d90940c1c100040d082246d84440024441c1c1c1582e0b0302c070031094003a95000c44000c400d480742e0200000d42840702d150801d4400c11708044c500c0c0070b89034491440c000c029460881c1c80b0306180d4003001082d0380741051801c0c1d5080303d4000003440e050903070a40d142c9910402110080b02090780070311810110103001d0102810451080c207410b6503404e52682e442c3c00742c444030210581480907294003001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 107963669 1250 107962419 107962423
    0x100f0204050609010f110a0b15010201060f09020f090a03051e0309010906110c04060f030317011211030111030c1201050406060c031b0812040b06030606061c02090d1b0e09 75
    0xf810301d6003403e040403000040324007190252001020310a907403107a04d290200344920042d01d01e00602d1207a00400c0d490b0210001603081e60300324411030102c48044042002030580c160b001c1c00104107118019450080500009940442c46030410303551500300e04440100c1e0525080c40341c60252035030000e90704082504001a1003031115103c1d40c420300460030b402d0400d2080922000101450040040001d01c0c1c585e240c5501035900c030700040703010440d24001c002c03400d80b000710454100c1e81d502d100720317420390002e03528110a9910105810340641d22035a00c040483e0701d05004d184507209100215484000c0d41401d405d01d04da06074440d41c0036503d411401c4c406a03038000b048083c641d0b0141000d040341032075000181c02000003078201405005021584c1c099820002025500450003200a138000d42c941a0805803030300c1003640d80302c2e4812070401a45000d800000d00d0700000f4101c000e40182441a498041051a40906c0382200c17400150b82d03d65a05000c81c05030700c406130200e480c3c1c0c14014980100711903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 107964919 1250 107963669 107963677
    0x1022b030207030527031002030f0112080c010c0201050a0b121207080d0507050d0b03010b01020607030c09081b1822020f100206010807140303030c0307090f08100f02040506 76
    0x19040540014000e400d150140003103030702084040403a44043d400280300241225a1301e00c11500c40d0007400400120320b0010b0003640d0203080007280c01103040e4a40760320004138403031014080756000c2c8280510030fa251030a118221106a054002007243e251599200d0116207500d003299225100c44858004007004c0001c515414000c0f1007900c130b0340e501103810700260034058242d44805075424101044000307640103019010348080600c0070300460074010200360903034031426003c500681c070103c00100d415100c6d0f0000102140c031403d00f0384601d030712142c0580c1000d00e40704a0140c1500003032150442c03424000342d40300080d02e0040c40c84540d1b0408002c1000d110707808244c501c07101c500100c10042550f589616080d0801c9005240d1001c0d000740b0340020751160703024841d07818103000354040060300072484140c2e81403441000380951b10310350713452204d88030356040604000e042041c0c0a801080030030709094000c01034882c071070091240c43c5130109118103480d1032400c07010026006210421803078540070192 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 107966169 1250 107964919 107965003
    0x20a030e0d050307140106030209060402121f1208040302030d08010521070e010e06130c171302060313060501060507120507111908010e0c030c090702150f060102 71
    0x80c400a07405090603860f50007000d5001e03041d408001e000d070848000560251040307901c04c0c1c54685807a501c640421049020b8656220a180e403814000340035042c4be00c03007284030400704541c0c21143d00d4450b44c590601c1c1040c0352040b900d000c0005018025840d08100d140360300d4a0a14105a0039810480451318021101c2d643c0f000300310001c0102008084180408005068028591506580d5511002180c420280d50036406407443c900d00e8404545a40034030b0580205c2d50f04d445150440175a4600314003100200301c03d10448410708040c005a0b220002140a010702c00c040c01c80381c10745c90034410304407601a0701010900c2000c00134040020f80c012541e48220a0b5428540d440300114100205c649000f6040641d01c003100585445080403012054415900700c1002044500c40e601d61f16951034480100540c1c0c507900800349440c040c0b401e80c3c3c48652060b241d2040e50303514600f020388034003c09011342c2d05c00c80f000d5582c41040902d590400917070a80b950004101c01140c000c240e0070b42c815031841400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 107967419 1250 107966169 107966179
    0xb010f08090109051f0c0903020901180605030303070c0302061311091905010320030102070209060913120905010f0c0b0c160f05010b1503010f23090f070807020a030e 73
    0x141d6aa4820360020711a1a040819603150740d000213004060752440c0e0001c4524249401004514244590707010404c1ea54080c14441c85e0b80d08001c00070000d6441c4541c035102080e15a107011505403001d10266004600c15280c08440411501d0302174103112008010080c0c0280c000e40c400080f410180a07184103460945010040d911802244094107a0340103024803114200320000040203000305000798111914054944415040c1d41050300741d01c140400a580039030f0a901240f154540002c019401c91100600720403034410544d501110440e40f48520008a0083d99003080a5604510052406c0606183c0508000c0055484d400f610a0207402003030107010105465919107061000c04071480d4102c6450114030f200e40c60640d002c0c00c1400d40e464014040800c06019680419080e28140c0300100c10400c0514108044002802614280554050208070719500035845030480746000d00380c034150922041c580210090800940036040404640c030031000140801d46c40005200e18080c2210 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 107968669 1250 107967419 107967421
    0x11b0c0b030a180302060906090c0a0b0c0703150f1407080403031a13020c0f0f03040b07020301020d050a0f20090f0a090608030406020607030903090608071403010b09130b010f08 78
    0xa610401803444a0a44641e00f03c2c031030390501815000244c41384204030907403ca4105039100c1038119151041c00c0c400b59040300c9400c0c4140031184605020301544525501190340030340c0d0b03a4450729000b8071050a80115a940d0302556550b0b00580d000b101e007008085454a500b906010b00c00601c42c03c001000541015950742c45210100f2001202c6c0e03070f08890061000c01030590b4241001c00940c00400c01c1501881341210a000510010800d0355002c220700014508180c44c1148c0003030305034418141268595401c01c0030104000d00c62003910700801002e18005440d000d20310301c0004690840380d44104020006c80300a030810100340403521101360a450a14a000c0b11802081c8042c40e141c000a0040342401c202142410002014001711015076081f134042d51203c6000742c00310395144030013900040391410705114480c096a46150012001d140500c90410104030140d900c0d0420703040001029800a4202d00c41d02d8040340403100360300c400304100140d89804001900c824851544c0d2414011094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 107969919 1250 107968669 107968681
    0x20303280e0601060210050a0504030c0201080703110316081b09040903020703080c0d080c040609060e01051603030b0a0b03090604111c03091a181207170606011b0c0b03 74
    0x904070000d200d40440442e6800d58480720042d446840d81c2c0b00705c0003a545420001915000c490148500903501602d405800c41c01d00d03001102e20403401090002815194420541d00c000b180008610801c00304c080c4202c910020600241011000703064654180d420007450f54448242a0407182e1121003201c00043c1880c0c02e11341a42480e25a610140030454041782d00d048042000c2140c4052000c0d5a40b60171a56031001e501303c07800e0280c0c0c06071070002252110700303100c100c1c0200381078032003003805040180c24024110b0b09803601910300381080300041c2d00c90102402c3e07402c00070b408401a1401841e070030304507c0d107803d40581d1074100800250036280351490340f4180782c0303440808241e045030900c1402c040360650b0170302508589851190790700c100070701c0c0300990924040d28180d9241704002484201c04101d16800c201c601100ea03484800c10b805000313000111a42011003094080609402a000e94945100050580070b050303140e81c00405903012a41c00000c12110381181650314903188075499844038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 107971169 1250 107969919 107969921
    0x6011e0201150e1b0708070f060b03031903050a060501171302060f03060907030209090f0c090d03020c1014030a0903030b120606030c01020712080706090c0b0a030c02030328 76
    0xc1a00c44558010b0031008503440081c240303c00e00c030b01d0303031031202c0c0c00704494181c1610007512400d107000d0400603050084400148044c4030a0324003c0c060714000c540c028400000905603030000050002101c1c80c0030014242c241c050040c6584055500c004000d514035100c0082c1c003410366410392121206a60001030703100655412081c0140740c0203000d098072030900c4804030b0a154029103000e44a40d0140f4000f0f0052407090080b94000d002c090000c103015100d80c40117450040700a010080442e0060090840d0368442d660106010750007680100001048581030125482141c0500010084c60a03810000b0400860440707401c160001c00000f4507000c90b0400314001c140301c4101580c0306c050303154802c0300410006511805224201c003070320407010100c0010390b90b0706a58400d07510004650712540c030100303400e00c000d04202800f171000414503c5c181c1c5d441d00410002c3d9085109000e4020400300e07006641407082c00c071203480e02d00095143d8100081c4107524402c98407401141483e00601c0340c040c407042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 107972419 1250 107971169 107971181
    0x30c080408030a11070b090d0f03020f010c0c020a120201091707050406030b01050301051806070507111801080d0507080301170a020405010f1a04050f010305060d0c030f1a06011e0201 80
    0x108020340f0345900c0203542c01007026007100d801e144030f4895030b20080b8075000701d002200c02c6414020b0044040f10001c0d590440008402c0905a081d402a1080900791031401c0c01511102401a42c0300c0301e155401d4410005a46661341001459012900b9624010f0741c00c1108401950403d40184200c691194a85131500711305800c11030300036040240000811026580060686070701300c009005590f01d070000303040b5900c2582816510740d4012004508107502a030020444140030f40f904000c10398400300414604403c003484540442c2400c40104031640c020b001d43d9041c040140340003441c0080c280c40741003040c0418003c003411540040b0043c80080000c004420615502a10502166a442e5440390054215101c0d086818003507104c0b01c0c602c0c1c65204212401c2d00d0380148500388a14095004400405000b40245d030030104126060020484500c00c1c403004501c00c200c00c41550085141003030340c0b240c1000400c100100e42000740105030380c1000710950030381980c43d548044014980d100700d000d402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 107973669 1250 107972419 107972429
    0x7060201061437090f0203070e060903010605042309150403031e0c0801090c03020c100207031b06020d110306030a11030102310509060d0f0503090a0e0601020f0d0c030c0804 76
    0x1050804906402d0650b0381000c121604820100130045040c20350a05901c030071225007001278402c0714841d14510703201c0064034142c20098000030310035890310080f4049405a41100440300e45406200c08168001c0d0f100c141d100c880f0601030b0900c45105481210b150401404c01030034540c0b1404500c0700305034a0b1142c4072228a02c08014004204111005050500700380030300700c042810000300c05140b0340240221500a481d44c001401e201581a00403002500802c0c021020011006980000100d000c0011130200c0c0c083d000050b03540643e0200340045880c602801c43c5503c00c2030040240e10b41d008288180e241d60407030001990440142c000a0080c426882c002d40d40882c0502d0b410b5110704060205440c040510251542998444007001240703d411103010398020800c0c110180054290307103090030303280e100c0c2040341e00300341d00400003c49640864218480d0301e2200d80c20400c03d9030781041502c075112b039a000580915012410024400b03e07030301da005030238818000c60107000c1002a20496000702 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 107974919 1250 107973669 107973739
    0xe07090b220f020d0b03060f0705071103030702181504090804050402031e0106031409010213060516061109040b1206130305160302031903020a0504120602120f09070602010614 77
    0x68840d240d450085c81c1c0805458003a10441000851140083c40054003e144a458242c1032018640e1a0750501c01c0c0310708101e070140010f01c440d1006848401c84428468080481407046240c8603103148102c4071040f501360702c2541015000004103003000101c030241c5400751009a075a03982c002d02203400c501d8450308034100c9518000001101d0350300d0b40c0410f4211840318541900380c0c0740c82c0a22400e0740140c21144111440311881040100c0c001c0d00103144444821200e01c42440e220385840040740e0040a40880c10030340001c601039507286c14841c88255840071a20b45a01081045400d60f0740c08000b4401c0d8000981445030301c0031b041c01002507810110038006400342458040c81c00948a03000b85101c2241d420b00e5602d601c107264064001d545000c0210360314541001d00d8000b1808140c4550300b425140d140c0e007000f040790344040310300c2882d01c120501151800ba40c01c14540003403500d81070b940008110391501406008802508810b800b45850854007140040d0b00a03541c1c44c001103c10129641d20 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 107976169 1250 107974919 107974927
    0xf0c0b0f10050906030c040c020f01140114060a020705040c0302070501051501030e0319080403110f0604110102030c15040206090904060504050c040902011b0615090e07090b220f02 79
    0x440010082520800c28034206081d07280d0b84206001c0600000e940c00c541c0342d00070004040041c00c1c02d62101c8615032440c41262030036082c0d03003526401c6036445d21a080c200c46660b0300603c020301d07600d5440f200342d80c400d482503464020b0300b40c0c2c0292205680d01070244100d03222848110154030a0b010342c1c26140c1c0010081101d802c26507115240052002d0001380440d0418840a44400d00131041e81e0a2031114285d900b6009a81402241c010000034022010b0210b01600e42d00c0a507030030456001c0d5a44200700804132428070f07090040741007080744442030440d8010411481e07010400b00380c500d0403c1012115002c143c03038a10010302c85001ea01c00780e40d0000071180400040c015107070007a502850042050b00c014005400901c03090f84d0341250040c0c003140c14218040b180c0550380c8001c04040b401001c0004a580718100c450440f05903035800130551b140c40740e1841d6600030b01803000300300404203072908020b55900480407071320300340011300041101e5030b1f19075080003240c00a0700041102d1440c03100440d55 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 107977419 1250 107976169 107976181
    0x402010816031b05070606050a0506030708071206080a0c0905100605070f050f030304030e0904020901060e0d200a08030c06061210020d0e010f05061e030f07030b040314190f0c0b 78
    0x3250b0804082955107d0400303000040d41e040070f030308481c141c03100a42620b141d90760b03146098954020103010402009690540400201c0c807601c6460090b03c02e00c0d001c0c1c80050014141000300990b40d400c840c044907d44014021913109524941080b0782c01400d00c540c64910328100507403001c40c001070113880350080a803501440306010000710f20807803094031028246461501032000c140411a0029008841180144140ea010300704e2130315819002010315510284940d2070101001141e9038144092110510804451500c00d00c6038014001d4103004506000c03042c4410766441d00003412160090389082803189030351070240450040900d40800c1036540c0c2ca20a49aa00140040c81d0074080b02d5107060b60040c107003982c44c0989401014010b045000c001900003140419401440b21260f00d03103e4202022313401c2c1c40c02d10150700210b000c0c00803255a0700e00760a0151480000308000d5010a00030800000158400030904401402d03502d02288a40a402130035248100d1681c00649007030a40410060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 107978669 1250 107977419 107977427
    0x31c0501050a0f0602030901080a0e100204060f080f0f06150c030301150c0f03030515150a03050108060103030c0803040c050d110a050a031502090a030b07030e0d080402010816031b 79
    0x30485000741d448000c0b4556502141d0780440641c003480006030820070400c1c4880d0700c540119904900743e141c000a07030501d11a0720385c0ca84103840001c00d100326000b080422400350801000040400317a410980500e00c1c00d40c0440342109001003d80d4403002040c80800c0c01c60303c4104101070100014000c095039181145152542d0341c100348201c010b80491130007640701c410701c034421100706030360b0011480303228903000d590580280000411001c0403a8006222154640e94502e440714040758110030255510400140141995016086089568803131001040042c1c2e0002c0700c1807000c0d401481c4162070351103501d0180d01c14811540543c1e071180e030f8202010103012011801c0000040120b452100b605d40c1d500c14405013490705d22015011840345584501700f494039800410352500010319914034980c0326a80c02480341c906980f9440026603031002c6045911080040310281ca82900f4101050f25250b40000c08201c80103000c01603100880300c142c400c1c14065008007030304980a41e510b20401e00e503071078010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 107979919 1250 107978669 107978671
    0x60c03020c0703260a0e090a11130f0f08030f0d4205130e0a0215030f0105040b061603181514040b070b0c0405090c070308070305190e031c05 62
    0x4c116003007a8400d22109244001100d0f40076110351100b01c8411141000c010403100010030761580039855584492914110000501c40c0452807800000c101e07090182c1903c07100c40c60303004a0603040c0418018403108000000382c5103c01003000c0d05a503501001d0b500b88018002e03410050101d05002c100710819402a40918203105046141114907145801d560140c036002ea031140e1508003104010301e0f64054102e4205010180400007100e101d081142c2c045070000740c491003070442d0304001009200c00046040700072401000c044a0906c0701841d8580001e0861107814aa001e2524500f2665800c060003081032207081e0060001d9800b4903540ca044c491040c1002ca0511b10025200c800841c101600c41c5040c1c03015200c410680a00709140c0d0303603072400310900203000b907001c403001800f00207140d54503035070403501c02c1704549505900d503115031a02500d41c010141464003858100410814008011001041004040385020640a84843e0b00c0380c198411409048a2070309400d542c480d81c040c46070006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 107981169 1250 107979919 107979953
    0x311040906090c0f08010b0c1509030405031e0d0507060e06040813050301050906060d05070f09020406140a2c0619020607050403050d2a030e01080a110403060c03020c0703 75
    0xd1068603d0140201e4a0205080ca0b9038081030b40a001800810811400303404042e00c42d408451100155164000464004030f46058480e40002014001402d080c800600322400380b0f1040c11030140d600c9111a00d845c0000b540d5420071002190388020312115400c6041c00d01d40f0310040e0780c00c506250902e2141c9038030500c40d0740c400e80014031000486042c1441080d224080d0322000d00002d4441c8810041d042c4118542658284503640c001f00750001c1c406844002881d103924016a41c900d00300300170700152640642d40116402c180404170302150405a980c40c0866041007140324080001c2c1c4966600e0040045150007a030049000000501c0c0401f11005464142d02203402039942d44a0860b03092103280402416508600c20316030009015000d5a001c00c0340e190546904081041100c03004114201000d5000808084540c3d502d960000c01e803c1d00300e0442c2d00c0901c06074011010003e400e20403171000030042c5682e050307030340442d621940c183c58040503a4010f0344d42c071595070300303040c40398021071204 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 107982419 1250 107981169 107981171
    0x703091e15171e040206090622050a06031107030f030213030311062a03041a0906040b06061e0c03070c030b0108010e0105040209010e0403020a080d0e060603030702010816031104090609 81
    0x210b0a030400d4a0b4603100e110204451106090381d0715400c6c06501d400c02020385402c01410f015a07809c2c5520707103540c8041041022808080700d40340008200124100350b00034014107107820b04c1e00d40c0000c0b052003101c64507505410520406007011400302c0092007501c0c51203096083d0004003004240e40504040c6124103a001107861a03110ba9100c06102d03100a159104c2c41b4864901c51058100018081d50340580660b00903450b00c1c050b10040c40500c07204072a0f88d400e5401040410080001c1116580e802010642c0c10038105181c040e0110420742c404403503401159000301c1c920380d6220701002202d4013654010a00c000c041d580f071030040c00c0c90b0020301a40b001542080f500b81c01c000c90510035a440303107400406c802c0312a441c0c041803581b8100b01400550441c091a443d50002c500180001c0c2440340000c0c07400964852000d41c0c49007481c60190149200b41c208100701d41c050f071f0b401400c4540004545107014603242d4100c0054000f801c0c0c441905881b80d00105000405040c503500c00d8040ba03100d048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 107983669 1250 107982419 107982421
    0x507090c14090d030c08090a141002120d090c050406091b1d04021804090302030408121215060d0c030209040f020310060f030b060d05060a0501050703091e1517 70
    0x41c485668025a00300c0ca80100041d00400301180c0710ba29220f17041c2e4025184103103050315980100701d444616070403111102150392189659410100034481d0400044d201914210400c154a00344622507640d552000359154003c00080c03025290b0074000030310307004004112071a681d820040c05004251200048a09120f10030209140500751214004008850032007e14200230308200c000c2d00546c1d40031000c0401c0000c0030105403100e00c24a01120700a4008540b603d180064051611820380d0a0f076540310014409401c0911800403030325040b034101035545041c1d0b1001e00116005010340002410401d0a12040e845103540590080031462400d0b9001d0002040050424043e0301c02905e408030060004a810030940e841880360000301c0c0c86600d004222290250006002c6400840131115210394a00a009040c90000b5039500181002c0c02c00900b0302c1842d0714003030003980d03440c4908180d40d0450f035141d02c05042c200380e0031400b1b00000700b20350802e050503a00c01001b8186440c14020b03c6c0310804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 107984919 1250 107983669 107983697
    0x140702060c0f030a0c0306030614160e0303090907020c061c06050a060210050c160b01090b010813030e01022407030b0f030309040906020d141605070f080a0c0507090c 73
    0x60846034404106940c2c2465030f1a004880001000f8032881d1004040c0d03222400300000310940503801c1c0c0340b1100310050003107040444480913288910a030741c809120018000007620749010040e00d24034a0304495505a52743c41c080280c4c10501c0201032141c5c070050006442c3c0c000380c2041600e0003e0820008100110380d103036400e214400302c2c0c83c040c181c0940d0045c44d9080f0500c8494004a5012817140b00709410301c99082802c1e02941d101110840760111040014008181d048c0b1902c03440c050246441210350601d0000b0090543c034841014081003c2c0f5401c1e07200c964002c0040301c42901c00d0000ca00c0311201c01c0c000030500f059040d10704070000307400c04030001e00ca85085040401c2004004000e035207024956420407008007001d110444030b1799003c1c8200d2000766120302c501d50000346800d009031440c1c0fa159900d0152008941c02c80c0051000500000c404904861020075403540e000e000185d460341040c100303460301880d11100920038850040b020a8502d071580200c02c1001c441e0f151500f012240d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 107986169 1250 107984919 107984941
    0x3050304060c030314040f14100c05040603050604020327190c14150418230f0703180303020f09090a230f060d0221030a120212060906010905030114070206 68
    0x5d4401401140c690441f901c0401c510001390144071002400300d072510205100030310207481603240344c54046500414100026505030003210b86c005400c5408514510303280003880d03800900c520b41080c240303812002075590b04c04100008030001c4042d201c00e0030311074458079005140700c1d11070207050301714606120b18104c00d041020240f42c80c400c4508031346090508005e00004600240300081405503100c5169501c17503445c6844203240d103d0384030341300740f900c0c0341541605e01052409440c1c03031300709403401c5c1184404c10003002080000301d51610700981d5030343c0301c01680c6c4414051003043c5503100d9414010321500600c254040780c0f1618105550071501c179106051085606411508500300c100c0d041c0000f92540f62003240400180d04c01000300d03220514000528441c3d01c0b044446030800e900020704105840d400000615481c410b09000f5403814030300104001e12504044d00480c0500048030106a250b801400d580000d400003030000c000c113018042c41146a19020f0300c08402500405021544039120 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 107987419 1250 107986169 107986171
    0x8030903060f0604151211060429070813140103090201050702040b06070b04080405010207050a0303120c0e06070302060402150c06011a0f0a02010506040e01150504050a0603050304060c030314 84
    0x40100a00040e03540c0d0b542411000100400c416400f80c0c0d6000c500400c0d002a04468028003410b00b25421114010310f41509140c0d051402107100c2d0754140f00030001d11031040003048820502c41d4a2032718074100d00010701c50714090000010000403000c00c914017140e00c042c0b006003c88003204001070980b8206001502160140c0101900207281040980054101070f0400e0013002000b41c40140343c1315664a0b00000c51b0420b031003c5513800320014040207150303410090180600400c4810040c0c0c1842c5503005448011a000d00c1d40c07410343c41d1001512040c1c040c40300702c400920040d11850340c034130b180d10b00251100c2046900f240b0680c00c562207036000b08074000903503000521084c000e0020380d007040c0c0d070102a003e138101e0b680030040341000307400d000707100c03090107001010940d4001090302e003004010001901c030307895181d01040e8034040f0307480c852072955804030342101e03419100040c3c143c48050124000e010300e90000707441c1d880002000074210b40c1c02007283c48898043e980401540e6240310080c01c590714 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 107988669 1250 107987419 107987437
    0x1a09031507090b0306151903050c4906061b020312180409110f03010c020d031505030a0f0b010b0a0207060f0507060e0d0201060801060b2a10150803 65
    0x18410014850040d070b83d0000d580102c002484401e2980b0711528003191540840f00d01500e0910303003024510816014042d25800c400c3c0300d42118104107241240030000034515154203d030207010780b82001d10800c008146400c0800d010104044804da8191143c041c1c03403107116241c0090f54460401d02c010440380054402654000c003e0308a481c03a01c0d01e5405250010041c4182d0320090f05580b0110b41c0d07a40c440d0070304140c422541c807900710094000304010b0980c01c0c82070034002d905015107001510381c0402d07043c0d42e40020381070000d0202c0e00240074640301074040d080700d40c062013115401824003854a034821090f41c400c1e00648526030b2a840d0a45040c080d5412001c0503034085001801598001c5440041e06005443c101e8200019500e0343e03403d9400d445804511343d000075450075001507080c000d00d009012010024800c0c64500703440d2125900c111182e9050003c104410035a440750102c4103d02040c40d00d0046910540d900d0000200410490201c1307548140040c0340004c0c100c030b010050701c80c0d8034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 107989919 1250 107988669 107988677
    0xe0c0301051302091b0409061706161d03011a09090f0303010905130f0309080105060a0302030a02090705070b070203040617011226071103210409020c071a09031507 72
    0x7400d5030134001c0000b80500900c61005590090500d02c04c0d1500182005010191f000b04000340790000c05085d0412002490f46260403290801117001d5406030b0140c0250703107038602581c0a490800c0392141c0220960a2580c0c594204030390a40c503603200c002c1c10310707074003078101c8481200d40c0741c4804039552880c400089010340d070018401008281095409280e201e07807030490b480300300000c1c1e039240711b090880c0b06811004107200b0081480711110920a25520000c2a966400c8040c10340d00003e94502c84d042c4024402c802c030000060300c3c02d01ca04240c0c1d218a5004219222a0908070000fa49a403c64000c3c45d000a42c50204440d4595a00d6041412103040f440340400c0d400c05510b81e04401030383d410b0315000501d014188100c0032190b80d402070918034090b41c00d01891850003401c01d030410380d010080c90b404281f6081e001042c00811070883d4202c40c00d40c2c0005130b9801c5054601400d0041580c403110001c500421031022a54004000b8840c1c40c0e41282510901d11840c40aa00c1d010019102e8070006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 107991169 1250 107989919 107989951
    0x6050f130506010c080a0c0302160f030b04060b040504050706021c0f120b03100f0b030d0e060a1e050723031b01060806010b071407061209021906030e0c030105 70
    0x94100e41d805990010b206251034044200b0070f07200c840f120f0f48100c4c4003038006052003400c6400d01d42d060159020340c0c0e0115030200304031841c1000890f0a40303d14040503242201d6440402c2c02c01001c1c0d4003041c1500703c080e2080c003483c0350900300355071100194070884001d0b0140c404080c044403820f00401245501c1034581d200038a041c6c05044a0354041148101c040c83d82d1042100d81d41c4e9400c01035520b0502e1455004520139003040101410780d480301d4850307806544a124030404250704000c1c02005400140c608507220040e40104541c160014004000d95489424100c4801a07111004041d0b01e0b00459420001258080e0316441b2185c070040e8900c11500140070a401420581072400d1000c94018000b03d4896114180c1d107040c1802a0300020462400086450401006685000307000c003080d009401100d00e000000b4003841d06410b403040032035940b050850119500c2184450301d034590890034000d07440d01c3d8203015000703000c81e40003910217100340c0821514a207014000e89108120b036010724012 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 107992419 1250 107991169 107991199
    0x203060a0506010c0b040b09010c0203160f0c0f120303050c0726042607060503040b010b1b010905060703150305030702131e020a030f0b010e10121e06050f 68
    0x601d40604010b040022410600c40403030645c03a2054000c2d409840c00c02800c0c18000c04460031119402121401d5400500c00388455210105000302400e402c07240710902d50303130640b60840d8400d120384c2105000301c0d82180041860a0f0200001401910980b005c000316214560560103502507503100509204060a515090300b510708000c03100308034948001414103843e0140b1100c1c0000301003540564500600303281c11400001c100703403002400942089840c608190b01c1c3ca4620100501038001840400a5103012200001c0031410021400308000c101c00b11640c0782040e20386c00e040c2c404000190401c007014114504022955044a034040010b42c43c0102da5400d000c0c3d80e07542c41180d002c60a645001c6400c0500c0c03940c03d1200202512403005940344521071019044405101c80e00c0c941078034107050300c203440e40c001034031242c6000300b1102d48112040341e850440314007617501805003185041c000320380040006d64910f1420905282d1091013010348810500c00c8903a641035545510104a1641d091 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 107993669 1250 107992419 107992421
    0x305070b1c0e0c0604090902090c0307050d0506010210020706020d0b10020304030b060604080a050607020d08071b05010b04020a0c060f09050c01050a020f030307080106110f1213030c090209090a090203060a 90
    0x80c840d100d510683e8050010700b0000f8503540c10a50100310b48585500c500c01c21031034000c82c0b0350361000180c880700d8114208090001c00c640202840800c42e43ea4600200701140e0082090613940700c0b0600007990b0340d40c42c0b80703001c9001c1c0d004460b0761000c0c2810401250381519142425a00c25031942c0d0096080c5455901c5801c0f160354003501817604820200001f140c207000c244207003650340b4020001031410f8285440001d01d4030305186d042c4403c001c108410302c142c5942c03001c150310400c130303246040b80300241c081c1c1407003401003e1416170b03941d00520010740c41403555045014a42c0c3c40307000c0c1d01e041100c442c1e01c001f10801d841807110b0003800364100e228020050342c0100094147ca1030284112084031080000071841c583c01a0342c2040850016401004002d40c04403003038900d808983c0c0500111201d0b5908283d071010412101c030413442e4041010114424000c0c1c00d40000d5070058600301c001c1c1da65800c040025400140c1d02c5010b08000320006044600900810001c10750185c01010b040c0c0e11001028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 107994919 1250 107993669 107993681
    0x30c0f05090604050405070302071502090d030f031d010506010306060305060603010b031f0602100608150117030903100609061d0f0a11070b0901051614180307030503040305070b1c 79
    0x541c0c010b00901001c501038a65200d40d505c82c030720b81d44005035113121030f0034090f100c4603210f2258240c460040101403602e451f0950b00280390390f0316041c407024550101806402a12070800802056401d45040c00d8041d801500310fa80200c400382c0b010400c940c0c40f1013088090341d10845209030081d800300700402120000c4070007964401029681410701a401402940300b07403034136038000b0005031f0080d00c029090062500c100ca00404803100204100c61484080c0e0942c1c3c0c005120b002103200030035101843c2c43c003050045900c401c20003410344030743c100c1242d03815004001038002c0c00500c5142079008212041c040b8810111001140c541c01c003995515404400c440c034000b440146402d49a0b50103103000341074100039101d0030b44102d03007200c954a010200f050860300c0051200f41c280a107010b803401c1c2d403500114564680344c80e0302c246d01d564080031300e0341c0b16403000c0104072190144510b210010034028040f0160051307a119405544110b962081070000c1c0b405030164040000c15031486640718400030350302c44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 107996169 1250 107994919 107994937
    0x309050a171b06090306010906030c0518150a1703040801050901050705040b1c0606050903060c031504020304020d0b011701060b04050609100c02041a010905041404030f1101051e07030c0f05 83
    0x1519000e410001700e801d04400781d000300b41058030740c8010720030403112092160103400309540c251085402100c200c03031804405008082440c0d001c4d454994540c54041d041400b402c5580d13101d40010180da03032050f41d00d034130511541e9080e501c1c000c0812240c0006000312400741d809030ba600e60429041060400d55584000010030142d035214050300010704442c01911700400c06501e44a03119149882170608005000f0a0210b00704020410061075441320000c0c40c00b40d2405030340058480c0d943d4404a003100f00701c071201070951450003000050700c42c1d0020102d0720361150340c0001c1c403006560350001c5015000d2401401c3d4444410701c110255820036070310760384041b034140ca880d600021340380d00428102e0b401416082c00317000b036211a60a00d940c114200000810301600c041141c4080c0000d941c0d1082d201810003001c205a0a204803017962007a0000248c0484040082013141030040c1c2801c1141c1d0007110302c40c0075402c0d81c0c0c0011801c6001c6c1c4034510840c141903d49410040f4001411036441d4044410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 107997419 1250 107996169 107996179
    0x60a060c021201020409140a1a0901060e2b2105030103030819110d0c05040e01030f020a08010e030306010807080402090a0203191b0219050d08060103180309050a171b 73
    0x1004c0045021f041d441404841142d4038a0900300395100c2501d002d5441881d00c461609882c02c019284c00da0b00a04440c9607140035410361044400041c840200301141503040f401c00b10003100800c81c00d9440c00d1419106040300103042850444906180800351024808101c0601c01003000c240111100c2d44d100302520705e01000180c1051700e80046840100c2107103103540010902c00307039000242c0301c3c40f80c3d4a00c403420b05a00746440c01384100c00c0d010050000a18052207920040c0c11500c60302c5e030180c007a2107014000c1c03042c00f220045540c0d89400860b1800c3c00520f001e004030345005e00412542d40540d8004e050880c0a6131502800d401030340c8060703c442060320503224569000c03520741c86900245039059010081c00800000c0092510304180510380c46600c840d2440b400060001230250b8000b82e442c01e00681d13035987d243c0180c000b001121080780c1c011283c0d0401900305580b140c440c1e0191030040755040c54681e29100c60641c801030b08080c19019900c4400001054100000840f049001c0100703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 107998669 1250 107997419 107997427
    0x4052a030115030c0902040503060613022104050d05030f16020c10020a052b030504030309080403080903010606050a090e090304080a0b15010c111e090112030305060a060c02120102 79
    0xc0303070840d01c12807a00000907207200e1051007000030320398140c4001c140b040010b5086c2030500001980310030b03001e800c2c1c0d441130841c48003040d0302070703001d4042e10110041a100c01001d030041407aaa00e5400045a0850b81802004094000e1502070410340703014000300900b400b81e540d1648018a8100b10031010b44040d4407501d000e00025658a140221039180f07103501a03c104106072921078070702030503100002c205002000c601650380d8200c06082101300000d24008c1002e0315036040560084c440d0b40030160085400043c0401400240802031204580940c000c015040d5510011101406078880b0100000d010039020001c000081034140c1e081808601681d1509a0302d081d101d10380346030307643d044841440c0901000030241850040b41f54482081c04e1034291001e2641d5100b5100c5407641a007445201e4005072010b90b210a02d003901c080880181610a41d0750b15058041001c0c0c00516045000a0800000998504007401114112611925a40509149035081100d030710200604046190340c248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 107999919 1250 107998669 107998753
    0x702100e162904090c0806030109170a09050d031e0306050105161403030907060f05090102070b0a0c0210081b090a0308090d080d0603030e0405040c2d1d0f0405 70
    0x1000900081104d604002410000d0350009407a094000742a41d100e645020601c1020403121021400030b00c0c8a00d4055a480e0440b810a64403081c40c0e400c160f03008203680c01601c04140d0486408030407500350664900910301489021801c1c1c450074006d15000403402c1c804100c402240000c02c0f10744601c01d12000aa0621041d00c076451134000b1a104540782d4081401049003d40285806064110364507000d4508421000042c1d41c1304180c0c41404000b010020301d8000c078900c245800304c070403070340141248000021400e005110714020707150070490074805100e180c404640b074401c0f1040b005e0003038240c42990b0b245032100c0203d07410005900c5d03080031032164150001080400100185014841c0002d8a01e0071800c00404207503886025034000c82c80d2000b032101040100d282d800446c1c0001084c8107540c299074400c15000450198240b100f401440f40c0410340040090b00c0c00c00d903110140303040c01c1c15511511000c00054051390040c029412203403038050b120000321800c07180c2c104500100008142c4003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 108001169 1250 107999919 107999999
    0xb09011e05090d06060f05060f0a05090406150201090507120c050913080c101413020f0a0f060207090506010215040602160b150102010b01020705030d0c02180702100e16 74
    0xc503401c4039005c0c1d03901424049025030b0120b000c00b8007000e80d15a401c11660016040311845000d102c401444004a01031409a031660000c1000e040044070850700c800907a1000f0380a061400c804913081e0003848400b02d8a884030b02e4140b02200d400c014031000861520301031228490b0041c0100d9250a15024641c000c500c6c01c600030101c0c44444001401d04c0b0000d90010411100b035071200c1812103000c01d05101d5085075015145d004150100c4041185d44415070008010a9072a40300c903d06003040480061056000314603d4103c0344144814441035550000482c3c590711001c10203043e60215502240210700642e000d003001020200102d94059220b441c0c0700c105450031203001a40d0001d20048214950f820302800e0f0840c2028002890b00900380310000b43c031241c0010a0f201084403824031101503603030388034010b00d40d02610f0580007810304242c0c1c0001c0d200c01240f020344508600381414036400b54000070300d2001006051980901c130b2800c1800095042e40c891640091a50244980e038000340310f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 108002419 1250 108001169 108001189
    0x10b0a0303020706020c060909040209090c041505190608040311070506041205010f05150f010c08070f02090c1c0b030c0405190b04050c0a0e18040308010f0b09011e0509 74
    0x70b4000386243c0d0b00d44000280b4100810990a009038814045041c691303d4840c05144c00c241d044407900c2913a40ca220ba1185800b00d0024101d62103400c25540703051407080c000c0000242e4205981c00041c844502c032141c518010903100d0703400068401d40001d404284540d040050814408040c0d980d5a41e0342c800141440c1c00c2500705480038602402018100b120034492484600c111000501580c41c115544070210030341c40310b5141c0995041d00385241d15030700c203284201009a00000b900d807908598100001c0300703c50b0034001c80c010903a850220b090080c1c100203440745071a40c241e06d409100740a004041c0071b020498010b642600c1502c081c1700305991180180c030b200d000010210070020000030358241c1610343c2681c2c0c0b80d00803407400342400364075170001e01241c5081001e400d1426015003400081400300030410400754018842c0c00502c801c15030310400e281e04031507103205100312507501da840c210405e21406503071f5404503902d021b00052040e85039861203030000240c04c1203801d0a0854010a2080342 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 108003669 1250 108002419 108002423
    0x405030f210a0507030e0a02210307060e03040527130c03021017060a030305030f1008030403052d0a0311011d01020c070605090303120a020f040b03100602011b0809010b0a03 76
    0x30b00d400030492902c0d071500c10f40001c0070641006020b1071085401040039400003d04d0480708000880c0f0302c40b00c249e0100103c5032a10790102c1e042000e408084109901c03034006016540c45180034039201c2c4c1e1150b0180984105241c090070400c00b0369150403211795192212001d0032280c05e4108000003002d0303500c00a100d00580041e8580c1d10605008594003402c00c6002002d15105140707283c0d05001007079102c0c054a6001200e00c82f40400c644070501881115801540203903014440001c010007004801b04000f28100c400220541050429003c0c04202082851944405500035603003140072a2150343c1000440c200714000240702c07815507071141c3e0b011020000c1103205031b40008009008410401c540ca0050501d450f1243c180f40c490750020382c9a204001c0b40030300f0041b0380320101d004000076504461005580114850752150b450743d0a080d50740040720400800c0d0f050403000119140107000b10440901d03100c0c1901d418040e040c5040e01c510b88060030001c070035035036600750100d2500d40c803164401540c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 108004919 1250 108003669 108003671
    0x1a070203070b030901090303060e070c0b062e02160302060d0903030b1306060e030318060c1204181a100507050a05240c040b1602010e0a230105030405030f210a 70
    0x9061f0a000d000d03195a035024100d1180c2c1441001042c950000708050302503801084030025441e1400014001c1440101c00c1c00030915400c1e0004035106494880010380c88690261054441d6480188180c65028480603401400802c001c40074070449512400c4010b2090500103103005180340401c9407017800c07080c1d55040f039999440501009401001803500034408600440c5841040b906100c80c5001c1102c640307003d01030203d040380079864140894152038030071000c1591603960b1250454a03050101e08078040741c1d490206c0004a02c4015080c40142a002914148101c144c42c50110390356400000700f91080d0240228100000c4d00c20b10050b220190000c02002d0a4280d0203450080142d000e041040c440c13404010800c9010503640a41c1c00a8035042d42c180b00d501e40c280010f95800303860b80400c1e94841418500860aa80d101003442c00320000720982d1400300c284400151464482031310050126401071060000303540c01000100940c405c0702d140442c840703a80c4400c41d10a400165040c84200e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 108006169 1250 108004919 108004931
    0x131709040e01090809150d0509070501030606050a020607080c040b0304061d030a1409040f021306110304060c0b04062c010b010e0d020d0c1703221a070203070b030901 73
    0x1850680120740844102100070042600381c0d944a660620611800500a00e020340e4007000d0342c49082e0030b48105e021707900c074184031901d0301c0700d406601c81c012402050b020902d404004a0300300d1051081c0c529010782a0001c0c41c140c1c540c0c4c4000d8884040c000c01c0c001004100b00000700703400c000403000d90701491046e032000c5801d0100000840080071910340084d41548140b060300381040e8008561030714031600c0706900ba96a82005c01280191582604a00016000141c1101d0801441482c001191195a9100702162a03030391044e071248500d11603400040c0c1480c01202c081034845128581180c8103a000040050f41c0c89400d4103a030b080d01d900e070310540f031700301d25044450031080c011031024030b000340b0b8031652106101000074401815044007902620561004008200401e080070000d0315203c08240c605012000c0b04c20b540c3e9200c00b054080c42440020b0a1130300c15514480780d030940c2c03502d130340300043d0688501101602e500440003d03a031511403500005414200079008500901805001141d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 108007419 1250 108006169 108006187
    0xb0a08160504050a090c09020c01140f0609010503030406052a0114150f060d1e0608070305101401180f020f030a0c0c050c1309020303040902030f090609151317 70
    0x31200b0052054181c0750170310006100090f100780b505800c0d00e80e460070042e10740301054021401001038032a85c0d5450704c40d41c0140082401d89030b52036031044200710340c0c0c2d00c9540e03200c40515499004030321408000c00c0f403d100103000085200300007036005100031107101104103580f84d014203403140310304e40303500540104091000c100c1c01201c000300d0348602942c7c1d4401440b00a0b01086041c4100a04014016a112910060070701c0d5142a1040c2c06903581051040e143c0794505079450304840e03c0104c1c1e061140c0f2104d200d00101c1401181040f80200200c030005030b10b040a00c145103060800300a54140d86caa400c40355903403191002d40380c0e503912202115220301d440050b00b4101d443e500c02038018400e20510b01030000e8400900503008035000d0742d085140c2c604207100b44000c0c110307000f8020b41c14080403c3c003140c2c000701640914842c803410080510b442d298044008d4036608241e0780c0c07200d21380202500b56544891710318000d4000c280c05019444421590f03c410b0b8101810500c1103804e8400002c003950 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 108008669 1250 108007419 108007421
    0x30a21020703180602010b0d110d020a062006040b0403050912030f090a060c0f2003060f0708100f2702030a09050601140612060a03120c050d0f020a060b0a08160504 72
    0x3c054203042c0020405112070200080347c5030f4140e10010a6100c6640c0311035180c1e00da80d185e00040980c05031540104907110440a01100540003c0168502c0e5800903013101c2c4c1400928640500d82082c00702801e9100e1340c90446040e48a0f110903078100140c04a019005032007000109014458074000c0d0362515181c3d01000104801c550000e8204003807402c0c1c402c0481c0d024040d20310320980c4241c05c5038654921507404500c610785480e441e03034540141c6017003203034640041c800c0500c26042c47d520700d42d2503581c52100f840241d1240c00780d26040e043d81002800100a0001022280070302c0b04024a1600c00e001104806d9a104980913000035444d18081030400100704800c40c05000c001c441a0032170402d400c0400c1c100d01031100305a034541030300030215603191122080c100155411003c0b41201e0740d03441c80c010303103000d0038070200319042e2140c40854091a8428003040c40142d60703550180010000320380340d10002d4904110810307030180020030005400d6104002103800c400303074540b0800000d80b070082000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 108009919 1250 108008669 108008717
    0x4020d1203051b1219110c0c040b0904081e19020c041401082d01150311060405090402040207170d090c0e0108070314071d190e030a21020703 62
    0x848803400601c80c0400c100300e1031036685d40c040a000007140709010002c2d4001e01034107a84118035620240003070b42000e441d00200c0d90301e102d00000d460030302007a1061401c2c4a415901160081d10000b000c1c8005210340c0c1c1c0c1c0b40c20841441034903648260602d03d1a051b1032008014000c08040907910102d07c0c0f00d11414507019900035000820b54084143d0f1406840d947c4585012803855820001c3c0180300910700c00040c041c41d030000710a0003c0140388031a1840e8000003195000a456210052420b240c071482e00b00c04403000d44d24003400c41c00060301c4581c2408007941003140c0446040d040d1184d5a00c2c80d010300006070402056149010039545014100780b021407a0b00d0b004510360707407580001800300c00310020b07540080b65441442501d800c04501d94250074024590401540d02d03094040c5110096454003445000b40d44018610000e00b00b858085022035940c05035100d1103400a0001400d5203010741c4014802e4090000011400d40c10411000100e80c0302c034804501144200300c003022907405105c1c4207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 108011169 1250 108009919 108009961
    0x6130302100819061a090307030b01060305010303120204050f090a02070f030f12060807062303040606030311060f0406110403020904050303010e010f120b070c0818040c0c170304020d120305 83
    0x4c00c64682050070f100384840c4170301c00b880907480313000540d00c0594400304003910056070442e180d0310003940c4900000700a000300303220541c009840a40745211604941c400c842c2110b40062050f4003021070b070014080c0c0c0480c01006145500da003408403c0c04911070511307402c5028803039600c0c0d00c44040c2203880a454407009209488941e80f0303208041c4030038034000420ba41036400500701181341b01c9950782140d440c4442d41704145141c0d0408424082086595000303407050340c0c420348654802c02202101e052b070364003003141c0c1d80d65400b42180c0401d0104155038405c54440320410025440c141d1070741c0100f044088203072021100c5030300010040140d42000c400c8140507100b081c9400240e50316140c69130300030001022014180f0207011011801c410700400e5640f0246920062040c1c440b40070240c14403000d0342c0400c4160040381411480b08915105010642d1410350242c403a402c04044404e80b002d01c3d0b00b008000301d800c051012489004a04500d0400c0c040c418a644c0c08500344ca480d031006a0441d10303c800e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 108012419 1250 108011169 108011171
    0xc0d08060103051003050618010207022107061e231201030212010e030a030c02160902031006050901050d020d060b0f04060906050a09051c0c180e07031106130302100819 74
    0x45c400070b1004100c06410500e0303408615522860a802c3d140203104003c002035120100640182c03121080043d4451500c1000d4244d038809a030320032050380c610401480a400c6810400130404d85507025210b11840240400b82c81c0c1c80e12813011175800043d5121541300e198801100004208620f4241524100b980c0500700070301642e4610354020303561b07001c0c0f004c250040c107894461440103240b0802c51018003205255500070800c1d929140c140096109980c2c242446640034004a0501d005d941240c0d22000f069490714a0082c03c0c07011039000f034007ea42e00110161b1a4040000d4941d50234003e441c0348000c0c030140700e68a0f03107008009007030080180d01140900034284074000314150000c07030701d00448005580d10101418403100e00640b850401d0300090018614400c003080e040a5483c42c1150740340c00c054104040c005150714a9601c4500744001000d42c003450ac90000706090550142540d04003541c00000b06179241c2d400110241c055502040005503898100007521596600041d44c002154030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 108013669 1250 108012419 108012451
    0x2010b1302040302300a03080a0b0a06210b04020316260f04030302070b040b01081501120303020c10022704020705060114010203070c2409080304050d0303020c0d0806010305 76
    0x10104826020224062004080171080203081e46000040920b100c211001500d80003507403454050f148030401d95035078140510b0940e00007080e04048000c1c030305a524948440c0454100c1c51541a074806051141e071601c1c580b940501c8c00c5c25155400a18064a220322461452464451000700342d840419191603800b010a0307100900d0740d118030691500400102d0f100c4c207082d51142820380107445090002080fa00b001d40030002403046041c0c0d05816209070b501550109452100304411140b402e0248010401400c001200040d0003640248107411041090341c0b0b4641821410b203040b070b002002a1508031400f0a48110300304030000c11051450000c690440c01c00001d0748031103544030414092480b15800c103811401d072680c020003e4a50040c0e10442400055032144100603c1421181c0340100594a0360007803404ca500035600c0c00b00b40d8031100c000f542803500c4c0030304002c2104900e00054042c16401c00040b048003c051040031141d84a0380c44045c403a0030110001001c5402c003c2049281003000c84c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 108014919 1250 108013669 108013673
    0x12060f09060f0c07060e0d030906064a040302070911030903070209090c0d1505060d0b071809020a0518040c14030c09060c10050606070b04150608070602010b13020403 73
    0x4080943c00226040d8010385400d21032801c4070080c2074013260540244203000d484034000d83e2581000303503458800d503800e02820b9a20060052500305510001c00500d480b2440036400401c205402e4a90200b4480416004841d008002e5075004050340d0036001a045940188102400e82c0100449844560b48481c614078100050540703e0043c0364009104218401c007168119904001c04000914000d0440c2c0380790006240908808001038145454203081c000011200d142c1002c5451989401045daa80b86a4401070111408240c00004a450002226021510004502c058080b1094a44a0560f210500d604000c00c00c061903000034819420b002a078008203910404142c2302031740201c4031a88a8440b488241c0041c052214005d41008010070b402103000000940385520310082e5104101c26150300051080c903120f820005020840b01a002c6800107000001291050102c01c20010324181c4403414141084803681c00900180c0d152070300c00b80e2610b00170080080010001030210314280c655 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 108016169 1250 108014919 108014941
    0x8070801030f0c0b1306020c040b0d02190801020703051b0c060a050a03020906070c0e010e06030304030f0311070e100b19140d060b07140a03090905070e12060f0906 72
    0x5010003481c0084414212042101c05180704019000603004c1d591200c120790030485132103003184186801813254518195250400e8480d100364510003800286000d00305800303001c908001c2e4290031114030080100010f01c0c00081c4081c0503543e1003a5030b81a07889807002000540702d0410f03240030b0314642100c1c07004c00440c0c1d2880d0031a0020f00785401c0054440c414488150028040c007100b03250001c1c3c000450204000c1044881d00c10fa8000603000c41050f602e1b00c0f0b11003800041160300c40c3c0c045d030003084180082520801c10040c070501c20b02d4000780d10a41c80f075407181414019408459114118018042480034015104000e0100b4954490400c05101e1991b01e801c0c030415030300400d001c41c0b82012082220b00d0001c68002c1c0c1c0b0082e206021596407450113120542c054141038500c1807074002c003500341000c00329600c8201901507480c00ea0705410484201d0091501501307100034030103c2046007038a9204c0c0c08940c100041ca01001d00207500c0d0061103988001c9004001507966000f8800708002d490070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 108017419 1250 108016169 108016171
    0x806010f0e01090305030d0509010e190803060f13090c05060f0412110904030819090222020c0708030d050c34200a0e060d030c0501060302090c0d05010501080708 71
    0x6600e050001e91140e8001078854101503080603206010008001109440540146000e6039004008201d401c80c0200541e49a15400815aa24081c44901000070407000001f442d00700c00c0060102d581c00c41c103880014001840b00c611211034503140c07880802480b00e06070300f100c01400e09039507130340c500082d43d04c60211510403030041c004030a9042c0394a0b03003841010640780107002005440c0a0250606003009001424100c540e07044041c200c8810440c0c40607140282c0e0750b141ea0107450046070840320f03480760040b400c030b200d8069000d0b43d090010200701c40042002d24000c0c4800c1002c0c40d51603c03d601d0f80e2003502d40040175001c0701c4c2d070704004040145c44003070b0f0720800300090321511050040b0050030741d100c6590b8004001c1e02508100c211040c43d80340d402002e000380c1c14100c80c84007220755200041155031400701d030302d5640010001944404a4003d2201140c11407090000090b19501e075400140c000b00f09969405e0701200200f00c0d1520f4000c14801c0c280942000d080030003407464248801400440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 108018669 1250 108017419 108017447
    0x6010e010f12212007060804080a0c080a030b010207090e1507050d06140909060720070f03030309021914060901170705190306050a031403041203030506040c080601 72
    0x461000e80d400c0c4071034030080c08403aa288240d401c500c9080410010164040b400e50020084000c040090692500207000d004039241604d50340c06075072300d544078443c443d001100e881e424000b013041e807403000508400080142851603140000c1070560580024500131a036089103642518043c3c02942002c0700140c0f005101030f60303801031851035844103001c03a4a0b000e51030440b03683c5401c040002c280d00e11010f804d032940c0c1c9801d50704100395131b0302c030900c46550315820b540305000701c0d045141150400c0d51480d51112103480342c00488640c0c50380c600c10420460300950058002a598030791400451030a0112102c0040c25409080c4443e4185049081d0105815440d244140d00c0090313540116405110070805050b00d00c190b61040d4981441c01800e00c1d8002e90072900322801c8000d0b03a42c0c099001e4030814042d20005030103a402a81141da40c10808017000d10001c2d8980700c113110000b002801170b059000c043e440b0b13076004103160030050180004c0d125010480300911000c0810407074680d9002c006c450f0009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 108019919 1250 108018669 108018689
    0xd0f080d200d150e09060103141605041503020306150a0f03080f0d09050307050106080c0102030a080f06010504031211012306040506040b0607060b0f030606030a080c0709020a030c0206010e010f 85
    0x1405540d900d001c0b840c1d070184400140c007030304111788140d020032000d040740d0080d03401e40300c11890300422984407481101c10405008400000f44298241a4400a4040580c10010030310b245c5070380009140500446554114800c11504c651103030801901400080ca1082a1600000d0541d5180c000368042c600440f007000c1e4000c20f0950304184141c01441103180c01c04d0075250342d140309042590181109025445052003807200010140d4400021112070817265520b94041c4e0f11080c000006e4481c0180015040080034800400411864281c010080e030282e12460750080e03070040214250340398140320307214501040000403480304910003040e40c0f0a00882c0c00084555902d000500140000039280380c002c000440c03040200426984901000c4400712410782a01a4100c10141d584208480c03c9806811582032030780080c0004000d0210004031600b41d60039161034080c0001260401c4030f2030000a034544100300400c40e0148074403400741190400c4d2495541c10405820b1144415101c2d490400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 108021169 1250 108019919 108019931
    0x6020a03020d110102040906080a021005040b090906030f1e100203010608010b0d11030112020a051009030b04031e0509180702060601050f04030203160e0c0301030b13020d0f080d200d 80
    0x20f803003941120094400342c60100100c0352603081c1240c4d9848605030407401040c5090580345a14014400d071401c80b5116a10702d861b102c210414803606100162415425114601c02d24400d804140701c807240280c4070340412142100d00b9181c00340b40078021922405058410001804070941c001182c41c10340303d0100c4020b0359082c0341c08180300182206801017561500c04000800d500d19413900d68820326000311500003045440b00d0412290494880c1e142d004580c0789101040040d0035074031303c50f900502a09101507425160b210383d05019a655044a0000380006540001e900c1c1940c0305c02c1e0000041c6074080454600010065a180e2016050505000000c100d0f1905200c00c4012200603560160540324082a007034a4403402a500303020320400c0710036500000b207181d200201603034100c0340c1280110160351201859040707000300a941c00e0760001f07100841140441d485090802d000f5118a03151543e0306603050200c4200c52100380031502178114110303444103000741791041d2101c00384200360014078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 108022419 1250 108021169 108021197
    0x10804080c0a0305040f0609081018050f03040e15090613240303090b0a021203040f0b07020c09090109020105091201060e0403090303020d0e060d0c12020c010207050706020a03020d 79
    0x14900900914588070711a02c1146420076500c03001910072100110b040100c0241c955005840b00215030140c000994081000d85d041c000b40e42d045034040c40b00c48600c01c24820301a440e060300708060500710803030650000400300200041d4810950380070401601ca82803400c5414001040348030003400e094450040e240c4020301d1212a0341c800d0189844409120041804100070821030221610058011030980720740026015042000c44400340d01c99806040e15007109254500c440d0400351059401c43c501511030000101d510ba00d49020714034039001820110400402c00c40d031004018900070b0581d041051000050f40c1201c19154440d108a40c558090340c1d03003c0c80b240c010000d6901c42d099200b152402d00007030541001d151001e0701c0c020340c00d03600b036045200b8003901d01c240510250740d00204104844601406070b50322000032140c0038540440180c07021403040c03099810204801e00389035400030b480810032400300600310003882240090300c1d4049264801031f4407175040c3c48400c000d0054102e40c0d040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 108023669 1250 108022419 108022433
    0x63c060613030f17030106120c03140f0411040c0203090409020301141e1005060a0509120d0e030c0306010614031509070903110102060411010f02030d1103071d010e010804 75
    0x8954680c1c0311009441692801c10804003042e80c03d09030744168101d034a940030306a5540469060341c1042c5c55501d0440b0400303c4c2a0300500e0400580d50800d0390303e5041c02040d080000089020b42c0110402d000d00c2d0a1a040c0280c1d5020f402480c54819407800c603140c10107580100a5940c48441202c0008020300140003003405080c0b50305e61045490300c03a00400100b4250f1040d2000e155034102e80e000d00a0f42c44010648150f50b189c01083d520680922203000000c2c0300700020450301e0b03005008101401d4510389440c0c501801c0030340d200c0108040202031101030404202441801d40c044004009a5241c00c0d00034020316110400d10008520000005520040c9a44078983c0d15401030184016440d010800623300090741c01308681e5801c000da42c802996200107601c500651300080394489030494580150340142040e00d4031000d43c0418050305580c49264400d082d80c0c190009851550303485d140394020840c600e082d41001501241204d90001e0f0b9a110030880e0003510b00b070902901d00e85079070030a80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 108024919 1250 108023669 108023677
    0x91e06020c331210050f060c01020d05010b0d0b010306030206180303040807060e09090a02090705030702100204030f030f090f03060513081309060812030c0a030617063c0606 76
    0x109541c40d011000c000d1800c1440010030301c058040242c1a40703901c0d6000d00008041d020b10405520200ea0702082541d4a850002000380b100384800050be46200c6404813000d48009a000c1528090f0109091514014901980c84031076030034039080041d18250342c0010300502540c041c2001c0f03a04604c1240005890070411078000d000e41004640c419035842a0003000c0307504240b1003d004078058404101c00c0500040d400500781c0d8001e020000580c1e48000440305500003c10110031842528105403504060b031000300003440c01000d64061030403079400e0103040d00d081029a0010429030304420025510000c44034410b036548004045150384800d0407180344c5040202000d000c801c1e0000304541c41031290b0404078115010700c07000f070004640e240c240b00d4403403141c00003128201104100260003500c1c10001403410400768100003035880e84460540c0410544071003403494507400081804100300c1d25501210045528180401894100c0c22416500c944508034554000301c0c0b24000c9500da0361039005503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 108026169 1250 108024919 108024979
    0x70309021c0618050a110105130f0f170a031b02060a03020d0e060615030907030819030f0c0c0303180b090d030e0615091003060606091e06020c 63
    0xc0d6007002800544501c1d421007100101c42c05403821111282c415080b4000708980d54205014008000458039952040d000810320b00741001010000c08200a20151441010701940350050200c98107268a034040480c01d504000c04961202c1d800840310036000428a5007a9414a42009a0141c03260070034150005010000d40c01000032a0100180b98150302808602d2071001091100361b0301c10070881e40b40d030300595080390002120405c40001c018038000641c0c0281d040011182195640d0312501c8640e0460808501070b880b16000c1c91028a030b040c0074001c0901d2460400f008000d00c61080506a80104100141456160020170200350200c1d03e0b41040d158001146500e0341c64040c2c0d5450310388541e0f0082a000c2031400b000300100c100e0002d11244180c842c412a480c215a001c4200329552100802d010010401d020002c00010100c1c0103001c024640350320341c150100c0c100014038006514804031640c16604041040140c0d65000a1001e01403a05903110160307400c2403201c2041d055081001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 108027419 1250 108026169 108026179
    0x120f06020f0306030d0903050d0c05150a0203071806050703120b0415150302030c03060415090c03020a0801050d02100f02031e071211070b0f07021c140f070e07030902 73
    0x184007880c008401544101822420744041c100007030025030b13040e20180030240040d842542080306041c0a440c40408060140c4211858031968560141d01d02d00200c0c0c0400210380c01006000fa40d64216080050141101000c14640c9080940003009800f40792000ba040150f001c8940c01c0d254480c0e4403002c15500060414041a407000c8400980b0344002e1082c0f1504140058458400c04e100b4400d590044003181c4405140d41c07510b404000c083c100d000f0400004094184c400101d00e85140303c1c029a56185480241c0c490702100301c060314560059009034040d605050300200182e85004031384c0841022800c0c100142003041c80200c2ca5806481c0702c0108054152030404005c2c001c000190007901d10880380b104a070044500111483d03450741141807080d503c845405c0c03054500f0f25016199a00d5000070b018181042c2c0d0f0006014807400c3c1390700c24100c000354030450041c881d0345566a025110340310018400400410005580d500c1e1a10445010098010100f403c19201c0c0e000200c244e500105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 108028669 1250 108027419 108027427
    0xc0f0406030f0320010b01020604080915070b0f010f05010c03030c030b060d090b1612020901020a08030a0c020f340b0c031201050316030605070909050106020d020f06010f120f0602 79
    0x18014160101c00141d40740c1c4181340007405000404140a03045c1c04801c1a0b014100e544c9440d91003122540104018a6100c2c403136010340c0d03000d42058400752144c280a040c680c1c4490800181104001406800400d03100403015020320403a60006a04800705c0ea15103000501c180801c07508400034083c2c540701e0755000d00c00050901c558030468204a10403805414003441e01d4449141c00c001d41e0b4484407104002c91303111025800000150380c0607200000060050f1180b0000c0b503500d550295000320b48824004d950340d0300c0d03811002d80c10054040f260320390200070b007000a040c030040c80080c643c00e540907918a80075180e40203d500e20f11400c400410003040003e4803044660348441d100e40100801d00b108203e6400001218038000070b10680c01903640600801007400c5031240d00190100801041c18001d03903050000d2003000c03511070240280040c5d030241440e8500c0d5040242085101207e500390780e81300d5030052284c49040040581111840e14016103625464640340c50319040d00b00c806041584041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 108029919 1250 108028669 108028673
    0x203070f06170109050907060507032f0105070903151109030d020601031a07090b160f05010606090b0921120408330106110a0501090f02210c0f0406030f 67
    0x7901184074940a10025800c43e030300d820100c4201d035012130f098440b41d030240004200e07140c018001411064002d1030070b0f1850080521001201180782068002c1c005190024003500701002e04c0340325008030441c82c2c00070045182d40c94a5164140180d40c020720743c0d5841d60b101d514811514121078040c48007a0130345d000000d4500010b500c0c0d9000b40300903a20845604070a0a0499920503007501c03c4002d920b0740b0040b03130306010701100c07290442c0c2d9140240041c150400004203141c40b404d81c0701d9170310840009c1242c600b003406c002e1041495a00132000f02c0018407088849035217080880d4405400142c1c1c007811004850001442e28069004a204800000801180a12011030361150710007005803080841c40301c0b90112681010b0a20101210341c0b20381c2c0051104910902c0d804108004000441e80d50303d0903500e5203421211f00b072104803900c0c044900b2200850408858010607050760480522191201c00e00042e11002c1c07140b4000c0c800d0782034118102440d81c031030b8041c001550704140c088124032114 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 108031169 1250 108029919 108029927
    0x1a040603061508060403051606110304140706030e1009050717030901090506090d0201030b190602150601020d050d090c120303090302100e0c0f03070816140324040203070f06 76
    0x112042d401c2800e8804a01440c000400c1070040740c0c543d640f10b00d840c903102104040090100d00844803940c84021803080f080c070300b80245d8011800b85d401d00300c500700d400e0080e07880c101c865400719040c107007400b6500090000c0030500b007a01c18210000400c017030340b1394a0024203002c410b400503c0564241c880d81030b10010000b003c4c00e0911401e0b254042019204d00410030980a104002036010a20900403001948240c001c40f0051502030002514a01a2098074400302c040750030003001a03010f80e0802042c0c0a8441105401003c01c0c00074051403141e507900100103200d2007501e0403c558442002c5020400c4410005000702159144808810090716000300a000825016801489400011803050b402845601035aa8610006009801c2c08105004803510003001444c0e260080880002d184a030a00c59050740c5003078130301000c04c1c2b18145450010001e0159070b21398069401741c040c490004034940c0340c0c001c41d1a40c08004a860740d4451000038a003181d103401001a82c140c400d00010000d400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 108032419 1250 108031169 108031181
    0x4050603190606122417010b040c03140c0705070b0a05041a0a0e04050108030301051003140106020f060c0705031e0705070303020705210303010509100801050c13150806041a04060306 80
    0x1030b01300240041d900c1e042030800c41c0071280c1d010005034541d0000400003001000711030710390310700064000700311160b10100140c12a652000900c0110740c4428485158290341c807040d9a00c020030310318880c00d010079629495651130460140c06000100040e405201034082c4040c1d40c018444070615080030710f018030001e03000d60880207860340400c0d0102603107000f85c0780c00d01440d070682d00d103d4011805e5038a00020803c19071031610508040c540d50b550398004503d038500080d406000140c0041030744841c000201c0c0d1410600400c8a14148014003604002500c08411288000071451501180806101080c042c0b0b11460000510500c54800c0007c109500407032a0004c070f0300211046d40c42421001c0784c0c10203016100c0c0000115130000c0005014501c0c000021540100c1400700c50616191038610450031100c081d0356101c0002000b00790507041e00304140c007400c050041c640318092445400c5402404104010305410b20441e11050341d030084c4c40d003615100701ca4901c0100140708069a0341026001006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 108033669 1250 108032419 108032447
    0x903051002040f08010b0d060209040908191112030406090201110d080a0c05040501050702090c0f070c08010c0f020604020918030a0e031603020901030311030706061d090d0504050603190606 83
    0x50340201c00130f09290706202e100c6007104040c000081104039030361401c000703501800501c1e0f070041e6110012008a441800039103420107900840700580b0810700000340c17400c10040d00582e0658419207030300000400b000c0a480d0030550104020909107110310040c0c1e81d240c40c0403201480c900c524064100c400f640003001c03502070121010300300031009508004442511850161a0101c0d070104000801414580780b1310351700005520215040c008824010b1007198400281a5195040205c00740000b000c00e101c0d01e071003107070142015400c20560340b802079201d40005001034803d100000c009034100866860010090100b83c0c2980d6590301e0300740300544410f1003881038a010740301c2c80007003c5061100c036686c8001d83c4c1d00180041400d80c81e656046901066285000aa40c0014450500040c8113030044ca40501001b00c140865480030100e1044902c400901c100c1d0542e0140280394015074000d81220141c0d1015a10b0540c0c3c3d60710303800101c082001c051000b502c42ea1034480300144503944895a440c280c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 108034919 1250 108033669 108033689
    0x4030801080c1516020a03080715020301030b070819020a0f1206030314070302010e12120a0504111002030415020717010507020c0d0204200c010c080412080403090305100204 76
    0x103600d030422a940e50050711481900070340300c2c0b4205440303404408050140301d02500c070b1031900ba0701c0340d5011541b80304130799000700c60000000c00c500041148410b2070039480120044214115813564844517036200010309440c09000034480810a400300b14620800d0040e0b20301401c1d582c5901c41c8400405003628a8029400181105140c07e0507000500604017181e40656411080c0c4000b0611201c0d503034841007040b0305540da40e030f0700c1c01000034080c0049064021207406c15510303030b0202c00c0214404000104202d0105d4035102c00c0000096076035044e40410f00b000c1c0c4125036070001281e400c0e4918402c07504551a0345c004c0070121014140d0000c2d0742026034400a490080300f4100b241c0c0c5c0b9098a41c240e58800168100c41c2c1c8851182c24100140d03d03045000420201e500c8220003640e480058a00e035240010480002d28070080c80c5003401904582e5100c0d04c0c110315545403540b280c5013182126040c40040018180200303041c1449203205002858011066801c1c401410482000075407062003001410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 108036169 1250 108034919 108034921
    0x402032a030c03010207051b0307080609060105090a020c210f030f160c030906140708030a091b05010903080d0b061c0605040b100305040c080a15050108010b15070213050a05040308 79
    0xf0304041c02607070b194641c0400101980203048064030202c101c46000aa010300c0341d14400600c107802044040e0040300b280700641103d5040c00240003c0e514001d18540c0c3d0940100040050301c800001c40088441c91b91007016800012520040c1d0903205d081a000c01a0b8000b1040c05170079080309005900402d4090710f00d140e1104d5001c0c00f41e0300d800c41d0110140126481213410800a07020310f8a43d080c843d000c900c0c1c80d203402165940c90915801c181d6100e500710303641c0c00c0500300700b00700703046130f03541c9000f01c0420803410710b00e0700c00000d01c41305040c0001030145001042d40c102d64401d03034005020309840142203a45a2945041d0040c840b1016512100310a0504030009142d050074410b4001d403d601601c140070082d507900b01030380070b09001342040300c1d08041e820001031070100600c9402c0c02244910b88002c20113149010344000d8039010b80111545902d480030300076483c0d03140c0c02c440342540303000a20b2a84540302c9000084880d0381650340008060f04103001c0107070070b0f0720740c1d4050380c401d44c866140c10300c5c0703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 108037419 1250 108036169 108036193
    0x100509010b0f030622060c020f0705030f070605070501060302120a1703061810030b160201050c040f050d08040905070509031c0206190e0a03020303090721020103050402032a03 77
    0xc814141c051040c0c03d50080700201d030390f0000f0050039410504203000502d81030451561454202d440c04201880180c0080241252020050107080d006050880040240303405030a43d564a4418910505c01030020001b503507002c1000030f411500056400928840c621314000040b00c2d210b01030120102d41d41c680782c0c1020805c3e41112410b40c0d028410242024a09c4020101c0b041d22044001d0b00d440c061041700400000003c00c0194003034400c40c400552241d00c8200010042d003550301c0504100214002440203010b0340d5195a16002101c001b100e60514500682c00c4c501124840c5800c44840c180c10030040108a0750004010000444240d0888600005080356080c001c0040c02401c00160010404608003256220045001a19601000a00113600b81d41c0d03903d4a8001141103000d60404810841c0107003061040710010b0809001042c9895100354151100c0540124002d05056442000c9401d54800300700101d09000354480c4c2980080800b2540003001d100e0300d500910a124003849108 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 108038669 1250 108037419 108037429
    0x812010b0403050a021e030708010f0e0105011d04140303090a02010e090907050909010608011a01020114090a03050d0204051e040e01020f1606111c1404021305060111100509010b 78
    0x3040300d4005010313108070082c41d42004004d0080380ea82400000c076190250529960500c0600f0040040200010b000001c0c00002400d0b120f180b089003030664900300040150069104e200c84410030703156295243d50b511850140710540300b12107850101c0c440070080203150500060401c0c0124000d0301e507a00e42c00c0b102410401c2c0290201c810285e0780c0c02c00a0200007500305201c0c2e090308401c440c800419030a071100000f5003161960b003490302c02803920921100ca81d58081c443c0c00e02001200040455500d810842c040e590516503400408000000503000c00c8143c40d90b0503100a40b000401800b004000141000d0b0300c2031a000426110303501d40079000740c400f8414421a003408054104950074854040b0441440882409095501649400c2103010362000500205444111200ca5042d0a140c060020045071944540c4100b10681c040612015070f46441550860021102000c2069034614004895003135840040f801c0510a0700d490086214407900708a1044407c04000c21401c268001041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 108039919 1250 108038669 108038677
    0x15040603060f2709030905040f02090f0301090b070c0206041d040b0c1e09040b04050c0301030c0503030a120c03090507081e01090f03050d240815040c060e130203040812010b 76
    0xe003044510f107045020516640e080506214002c0c203291449982c0ea0000c5029075400d01c030000d0109138002034083e06858a4603586403002000e40003004069510369500d0b1030640c0c064420401d009808141e00c0440d030701c1400311070141a42c100c050140d07142c4134141c01c11540050b0b4082311400a0f000014a40c2c1070001c050300e808041c0b20b142d80c0104440c02c1d1027a000da9015041c1e03182c2250f1126401021907d503070082034001c400b0009016075030340c55410002d02101d890342226100350010802e40070102d6001610141180c10400c0002d000360700c07c10194002d03c00400010110300804500240a0780b01052462100520700c044a06801c44103241e24201d461017900102164100c01e0048082841480680500042460b000400388001c15458003410900314611036104c4ea00c40080c00004802c0c000803000c0c1c00ca507552120b9904041d954040441d0490040e00204003110810f600c1c01d90f21074011307a900d225100720441d542d007040d040010065114021030101d840c00b403400000d40e602d9100c125 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 108041169 1250 108039919 108039959
    0x7080d020c2401050f010903060e06010f0803031501110a15020903071e1a04120507030314030f150609150315010f0c03140f1303050606010c0f0b0615040603060f 71
    0x9400b00d0b820081000442e003a0304039018100701c0040340100c0010290301c40c4561180c5c910008040c55032400d07018030304654158010030829003007841808440540e400054091b0542424080c511a40c0e4010b0946008030086001e8920981d50614a24803843d9a004001c0d102c015426aa400c1c0d4036840d061661300a407000d10501284000c40410a09d001c5803030308001c43c001030420601c0c1942c0c514003202039a40c250b00558158006081c2002019044241d41d81c0e0450007420017800c0d0300d801401e452074805d0043c0b1000100701a4000142560340d00f20482d884541c1c02099110319601d590398040711500708541c00081010760311002040b1303600450202a424100e944c4415003455640d900b10364048003450150b401140c01d201444000c40c5030f20103842d82030040002001080c0c03650400e0f51511101502e01c40c144a01d601041d40810f40c80c490b80d800041e00010514090f44801000c5491a40007400d4000d0040022030f000c241c1c45d034560880f5080700e0803e02044065038036005550180e05d15071307440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 108042419 1250 108041169 108041233
    0x3070314160915050702030a08030109050109141501091a0306040e060c070609020409120201050411100f14070803040c030b060f181509010821040305030702060d0207080d020c 77
    0xc03c0346508007245410714614030700d4490700702011540030030b1070320101c08004c507582c000210050280c00410701c00d890051507206010700c0000c110b040040c0e43d49501a00c5010507205000d2418120390040d00000020602d01c055a40043c070860740c3d007006a001610304900c03960810302044e1012400140c418000c0e00c0c41600c8501d00b080682d0bc9000901e040c43c0f08036013058803403d024005c90139161009044180320b40000c201494103103402c1005035048070f0b01c68070500150b00142101d07030740401c1401e070008090074061011600c198850000d8003802078003c00e00e00c0c001041004202051122808591007404900510340720301e010400c50030340581c0450f1f01702c1012a14110600c001319680780e003040d0003c82070310700240c2c44004221140e40c00d0b004180ea9034810790212408441c0c1143d040101d141e6045002d08141c210f07640d01c2e440703104d66000a44100c0d0f0104d0100f00d0102036038111030045521075680740d51800700c403030441e000e90042d8145019a01a203181c9414030381d1903c40c080205e0520400b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 108043669 1250 108042419 108042437
    0x21305060a020601120f02090c030618040b0a2403050106080f0102040b0906070305070609030e0f09010302090a0509100c020105060f04090209010302090a021b0c0a05180f0601030b060307031416 85
    0xa1000c00e404440c845c140c0d100d40800e1003010140c0c4900710128000c03c5a4802c09070390340350940600104207040c900303407600345211400700f00c0450100d2000c1030f001442501c010640c10500555480d2002000622520010032690004100801540010111200902554207800745060014200c0c0120710510032440c00400407681075140141c02480f545111341001410f182e075036110780046032880b04084010904614841c407c41c13a02e0954590a603408a030303030054540c150750101d0304100c0b0140c001c02050752120b01007001c0c268103200700c034040c0d40c5201c010040040d480c07400034041d00c815500e0900484840c82c41d00082d007001d01a0105072034020304042116481c42d070030312402758401814a1040c1c0c1d420300020651844076004106a82e1082c0002d000740c02d010340800007044034660040384507080402800f00b224009201240e0311401c100200c507138681d10b82005070080c02c0034410540d03000f0800004c01450f2a0580d107d04100e451000c2c5014860f0b480304005543d50780381501080204044030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 108044919 1250 108043669 108043679
    0x303110607050901231c05100b070b04170c0304090c05040308162301020d0e060f1308040302181b1c050408040e010608090c0a030c03110102070f0801021305060a020601 74
    0x4080e02400c0302045d4140d440b448604608041c4a8008000140d0403445078241c07245144c20300c2c01215003144c460340c09140d9142c58500c00f401c01d0f106e0b0b0f640c0104006580c20004080c42216040c0402c04955001c649650340c2550395050740725403060040ed54882e141a0754030040c40d2180050318107490f4401c2080f07160410a0343e05001021040381c048408030202030740541180d4410303d00500140e422000562a150340c0c1420106440d4201034640d45d5a1064041140d20f550400c282c0350003d0f414100701c80c0003040c40c24800024451600082e4211000c101032003020a1400499842044440640c0140107400c005c3d400491040302c508030440c550704040c1c101841c030280c0c05a070304507101e16041440c05a03542c04d000c01400c4264001000300360b07a80c080007101c0c13000380036011045030115400f032000c90030340c1e503a11421a0300b400043e0044499050019059000304014005403941c0703044800030715603403003d5038007030750015101b15a2540e45500000e40c60800f24150303004030b1010f0300540402d83c241 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 108046169 1250 108044919 108044927
    0xa080a030e0111040f1409070e090c040515042408011404060f03060b0a090519020f0d05160f02010504080a050307050d020a020d0305280f0905070f0303110607050901 73
    0x340c040c0c00729541c41c0c1e00d10b85090b4110000300300514103084014500c61a0050042c0c1d4038024140490190b00d50904100807142c0c0804c007407982000c1100d16540d10f485a9420741103d018035089640c0141c1011000300c2c007a000c9001400c03c4840c55014400c4e2020605d07101c00260800700b4100c408916814014014940c84107140b42000f00041d00000300e00341d80f40711201d203c3c20a584192041951034100204900b403c0d1500c1c0d0160244150a2065041840c0b50040c0c0c91001e107400070842e94042000c21500d40400200c89074402445000c3c005420150000818006800103001c0400c94071300c07613403010070700600406101d1500400400e0519001080640d400d80c00101920700b0040e04002014100680744080c01801a55500615030443c0c1c8020181c101e540140a850a04128400c52642007000d4590a05216014200803901c6003240360f448000e03003500d036002403d81c01045c002003030740c171808075100c03003260f01a81d00d14081029940810361100003e441c90030006070104401c05441d406 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 108047419 1250 108046169 108046181
    0xe0103030c1419062316080709060e090403050d0e060711151b09030a080909010b04140d0c0801060b09090705090306010e0402130509010906060b0a120e01061a030f0106020a080a03 79
    0x1e02e03580c038174100d8651241044092001c6905208200c0800c0303100810700d511602103540460603040c8110700c5800c0110151010040b08021489880e60030001800c1510401c281c0701542c2e6407500a224011988100d1515100111800000103818450561a140300020321a03c0454240d048070102d40380c00c00c0c034010402c4a0a440916094100310240072a00c00308244494603005841040c2c640d0018820804445010703400801000300c04e2009201411941c883e1154651017169904581c0d4030074508262000010b620000c46940f07004d4000402041e800c000740203010084030b201e80c0391b82d2010015281d0340140303d08941c15a10003030040c0144e000074034181d90414001400f50410408220304041910011180d1080994442c4601030400441e0300402015020300020182030001c0c1c0000180f922311071601540b002d64403075030325602802081d440306001d800117600c0da1284220000341420680d00540b20288402401800054200d101103107001c441a800486a0724020702000b0403009401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 108048669 1250 108047419 108047441
    0x10e0613080f0a0309060c0b0a0b010908010204090e070504060305060609071103030a090203061b0307050f0d020d02040314060c040306020f1b07080f01050c030a090c0e0103030c141906 81
    0x50200120300c044040103202d4a81c2c80c0364000b000790315075924004116060390b0f4495001c2c00085601c2400280c0100142e43d440500c04000144030a44080100c406603496803250755103510000d80851416250381007100016282411110141c0d42ca40520003102c40611000c0c01c03e40080000c900140707084654203800035201c0c03030308140708000220114155441078800001c403a981e107103c181142402c0c00070943c850703c4003a03a101c40c070707049d00d0f00c40d401440010001001c201000a00b0340c1480da01200b80c0301d6900840101710740b00d81ba0154148001c1d40540800c0e100e40d912554201554400010991b20442c00013074070364280380c65580c480f0081d400c40e204900380340c2c5060102c425005141100d14a8461100c00201100d91030b0515071b0341071a000c82c008a04a0f41030500b0010f107010807101f1a034121170103840024603c02d5904041d0352030701c0241c0010200a0100e80000103041c1d1103820301101074014498400a00c3d03103408850f40e00c0e00c080003844040b030584030182c0c0100741c13a688034404100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 108049919 1250 108048669 108048697
    0xc0f0718150e0a020315010309050a110315040b060415060203040302010302030604020d0905100c02190209090a0803010603090c0509060f0411091804050d02010b0a0b130504020a0c03030515010e06 86
    0x80d102d9a106640031003c46034901201d03408000c0104e402d00100c0a0117585c50203080c100503040745a02c680e916030510481c05410944008001c01c1c454504203c9540004020b410003809800d09282c5130045540c1a1a4035214a040412842c51f10480544072411185242c000350718251035540158040e40000f42823580c4603900380286550302805d401210170725403140d000f812940c48003c3c800c2d8111080f03840c0c84c5085500c60421304400840c800403240c0d041e0f8040b83d401c1d030365544203020503180c81e100700700090261034003200009500740c00d41c01c02076034035102e030111080c0e60f601c176020711094400131201594402c071101700c0c0d9441800d050380201400401d2884481c07900030060045251000d0240d014228003629004100605c40180000318580c08944000d03c000c25155000980070140ca0040d4888003800040741841d41c0b80407c031000040801404c2036494018503000509103a807040c81c15008039050800083d0600b07030720441d000502e80140c4464061003083d00c18007400d50010f0002910031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 108051169 1250 108049919 108049961
    0x7050105161403070f020a1709030607050405060909190c0207080606030a0c05011b0602190801050f010905010f0302070507030807030807091811040302090109050402030d09030209060103050423030c0f0718 90
    0x100da4107498008107580c410810641d030740c6030f09c81418a00800201524100324040c00144038607035841d4102c0e0740b580360846018096481e1107038101c0005002c182c80941444c50056120181d94020402104403007a484c1651070340e6a4102c05d0684565452500038003208004400b4800d941c00341301c2103100110b0401d000701c90725509598090403a4840010300940c0302c081004c000c0d1b01540090720601400058880d005610740303110020380001018041c15040c40504901c1c90354a6119506444081d070f0084211184140e80341006d0506510810003a0000b55010f00020440782c090780150003186d08440158003440591000100180f0703a441d4007044045041100001580d919007126029200e5000c0001c1c02e400c00e803040602c0c10301c1c96000c16003480755548082015070381341c1d000181e00035001c0c200030846a0b40c600c1e21044030302c03146e828080500300151120b13002c0d24000001c2c103540300b020404c94541010502070a95103090700d01c01c10200d0000c8034501000301c023481c0c000040c3c014061300c51241d8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 108052419 1250 108051169 108051173
    0xe0108220c030b01210b04062f18091003140f030f0301082406011d0301020d09150e030418060e01080a020117060105030a0e0c0607050105161403070f020a 68
    0x510703990368429503480800000501c0302000410074040380085c0c940b07030a407007180a070b03032800c040010003000988025510084114010703c410311002a04480c000291000b080c040610240c54104485002007400f010f50154140e0030701d400c0e50350045c01407008a45440e482c56680e0b8966180034021a95280981006010a040200041d0025102003445c4039129810b004c0d450b4508030600682c0001170031a0280010600c1e01c0c021141c0d0404070030b00c0d140641d07c2088034114040c02c3c10505080d0550310005001e495800d9030340c824884244118800490744040c1003928007520750701c40d4421b6181e04200810002c0040941402004102d0b1000c0451041d40e15100526144826071220201d80c2012072850110741c4e000c005041a411141038403841410002d000914900006128003036480d500e01c141c030b0161000b00306040c90040c004007541d50b100e0040c98564042c0c98241d8188555181c50f04024800902516030300e03000d04400240309056035944501110802000d90f454002d500601001d180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 108053669 1250 108052419 108052433
    0x20303090607030915050a050409020d020712020d080a0e030f0705010f090305030f16140a090312051e0903150717070507050c01080405030f070201050f0304050a120e010822 76
    0x80e2643c0a030301c80300c105601c3c1042000b140c04030007200710b04001040080b400c0e600c1c0c00c40d0a0b14241e800d1000c00580b50010850998021320423650080e10400111344180c814960000d019003d01d440f580d503002c0350b40ca41e0f000441c00c0d1154400c980110b41c1007400408511b068440241c000207004000120301c03600d02150400031140004801e40015000004001c000300010b010305400042240d407113041182d003540c00a090101d00d0700341050b44540001c4600703000d4800c5000201a46d08000d02c104240c1c4614030140099004200c0303140420f902148050b0429a84000e80e0b0203404090060606841409803030000c0040c028540010b01c01044801d00b0a42d03003402e82e0714454034a03601c40390f981d80c0c3c2904000345803440c22010141045080e504100c00907001000380c82c002100e40f984142c64003001d20040c0c8007402031032481076100401100300400c0c8440015111301310380c020003a640d030b01040c14101321020000c5018042c04542141301046000d040b14007209106130070826089801c84581d60341c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 108054919 1250 108053669 108053677
    0x1050f070c03120c210f050d0e010c0f0e06190e12030d0207061a0109050423130212120306060a0c1401050403030506011b080a0509190905071403130203030906 70
    0x10001034000c090b4100300000f004020910781450600905c42e440b21001c0241404140c0981d0307405c10501003807221051760303643c1044d00c4661800c0020701966103e40401060841c120b42030f90001030b0a0002c5c0105410f080048940c24002000c0203004620740000030b640000005030115001540901404040303d810300280441036012480540d072074019080910944000c0400d0000100d0b100d1201250343e07030440b40b0881200c0041d10041030081d18100500341140c0300d05210f00300c4c42141810800038040c001c1080f80d05d18402c0b01d0440c42e60030801900340c0e80e00303141c412000740004100042030b05450988003910480c401482d1107282c06000e50343d450f050068220480580e40e4640c8140000c0580500496501110a2818a207141c0d00c07000540f000100c04c010182c1140400140c2041c1a031280080790b210017800742504682d420340c0c04444103417400921a0801491030240410b40d1a40700b120a5407009a031384600f03905540701c8544500105841a4003268144005c01084d141600c40344050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 108056169 1250 108054919 108054953
    0x503070e040c0f060215091006140301060801020a1d040f14060a090b0d0201031d0303100905070507030504030b060f040e0a0204060503011112090a02090c090f040b01050f070c03 78
    0xd146800c1a1914124411458009401c810703804801400b030203074001406c0486140071007280c00b045c1c450818007030910100c17280078203c05090000c08605540c0340342c0001c121060a400070422190b41d00301340c900b02d0054100c4a000141c1c07001d84c0c002c0300c0500d42d20503015500020400104562030580c8001140c0703c501c0c105401d0004002007042a14203141c054000380714a403c1440400940000070f03084ca00e41100080c1419a90140074400c2c080b40d40150680104840031a65641801141d03942c003484248244000141000000390169200b24107407644030354907855282c00c1900350b5448808290004011035005088036548034220b6a0f00c4c003c2c0141e074000b400280501822074010301083d10303900c0c2c100030300030382c1030013544040d402051040f9024080900f801c12485d17214000711604118500c1000fa50100f44142484a40d0040030014202d00030b040760702c826158000310500094405006503140418000d01c505010500b01100904600b442014860712054503a9a011042e1040c142c1c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 108057419 1250 108056169 108056189
    0x803040318090f0204080c091005091015120c02070605030106030e0106090204030506040c0f0806070503071107030c05101b02040203070c060222050d0b180f07080c040c05040305280212010c0909090b0619050307 92
    0x2031071003b54054402c81c2c607455414800342c035a0034140003002d0624841071140200b01507542c8540c00c8801802e41c45000030304070b0a01c043d9550759890600560380c407419039064440104000340001e2907120980c4035011104400050280c0307503070f040e1013540d00e50001030031042400703134010400e01c00301c6040c048040035500c12002840f12070f080809000d41454500084d50501503011040303400d800c400800d040c80250304440140c1e4958882d1401c903900141c45100900803030010940c25122280001036000d440b0030110501c16566032182000b40380040840040e00701c05071440890007090b072150f403a001c501e14100c1200d401d8405003119500c2c1c4581a0b2110165400402c01b0100303500e0319000c0c10740f60540354546681818116210261901c80d01d83d401200001281090785043c04040d140400494009228a5150040c00c1d001c2d40a4860321904d0000112010000300c1c441d501c51080041964010904124990301c1c581401003420301500d1265620007014000189a602009000064581e00f19 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 108058669 1250 108057419 108057437
    0x1090312050a020a02030409180503032a0702091f05030703030306031a10090504060f0509010c2d080c0d0603150e0a0803040318090f0204080c091005091015 69
    0x410808a81002d440e82402500401c46542502e50001c144c506031401030800040e4900d50300c110028070426014014105e00002c010060b5082411030300b0401d0710382d0760f44116102e0307024180c00900c51241c100f000354452903480c0840c0208150740d1007007828804161440700e4294039100007070b1910500b035200702c0000780c071164140204049010801100201e0702c04521040c205410320341000139a0740035901a459031640040d0500c00c0c030750040707241000206401c01590612040b07582c06800003600301c102260112401c007042c4116440c101c907040c4203540c4c00480001a94800710303481107000d005542c04000501c0320514001c413074868007009504c0354442401042024006002fa6450030040d6006500920035040114074003600301c81c0d1203541071600131410340c4144103001184195070480d030b481c180380c00c8100c1d42110540d4020000c1e11400022180d00381c8000042040080741100c0255402d03420b06030401c21418030f0864071390031080e0f84809407242c94507010080b0130041440540000903407504 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 108059919 1250 108058669 108058697
    0x5090a030e04090309050d240204090c020a020f1306050301020a0905011407030503070806061b060601030b12030d02090105072906090f1909050102030c040302150c06040312090203010903 82
    0xd18841c4841c105540a0041100742d032801341100c0200c1c807a00780104030301c00c40842003001c80000110b940c48180000a08080004e03643d00003134106010b44d1000c1032400d116644198000038017010003aa000381240084d15030072044c41088080c0c10340190080380c8415000c00d05507028000792809850a80d6100019450030340010040f003481c002400d94540100a00340109a00004403136211956040c40c040a031284804030b40c1c40d1081c1c440e40030003420028004a107984000c04c40c3c5010382d500366410f0298520050030410404040320b4080f030a035000300a8003c00c540d054000d4054448141841401c140c0d940e2261050280240c0e0710b8140840f401035020883c1d03140c07007000394000380140c410034031525109000340082c05c1c0c00b415590240c1301d07480803101c0d0442c543d08814070307280d4410020743d104d083c088503941c915041404202c0c45508001c0020a100070344409a07968100668024202901c0313a84059942010002034454081d4882c00001d016880074042d9090441c030a64078581ca0520503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 108061169 1250 108059919 108059927
    0x4080a03060522050105010801080c040209010903020315070e0a080c040f090b04060207151a210a0c0f060c08040b07080712020c030d05030108150907150906030e19030804051005090a03 81
    0x5802087c180008a40140480800000c210003011010303100107995042450050340c48440c40c0d840258188100c485071095901c81d5038101e4012035039034441440301c680001c00c01002e4003040c02201010b901c40d030441512850f16402c494141c043e0001c0000d407079400d0341c0b260102d064084409444541d00081d1a10400c02c072000d0b10b1030702c0c034041e070b8080080c24250022050395074035419400d4070544c98080b4480a01920390a0607826000b150100d07100320030503207808602203141d84100c165220250300009a4070340200007104c5103a80c4190040c4c074050410404500507003094070140c40c8a0800d0000c00d000408138642c0c00b03118103540e0020f01440e6810400c2514150780c1c242038800b04503080c001001919000100450f600c50384905060030342d9900c949551030402950710510b6031020140005403440d4015898205481c040d1340c007800504181c03030040d45d039022070122140304140382100c103030b010a01c113154068000d80301d0404d49034100030202e408015101e0030b660b220f2190b0000d500d00d000309500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 108062419 1250 108061169 108061171
    0x203180102030315040504031e0c0b010b0f04030305030703020f0a0e0f0f03061602030d050a0501030c09050c0406050307020c0301060320030c03070608070c0b07260f04080a0306052205 81
    0x9200540c9986400c4041c2070000c80b01044d03650180b9164000701d01054042c602001002900c0c950026148644103c01440351f45c4d1684140c4803030001a0000c0740381543c0307004a94450b0ba07200100c510b414a10340d000c42c1c0301e90004080e00c0c00c055082c8000b0b40320806560041c05107010a650b5140402c00c5442003010b001080404244203594403550500591804551150f01000020000c22071b40c500081c2a802d5105d401c044c0c401d410700e404100445d1910300c0e0300c0b80303041ea4050514201c60948a0703c03108100c030000c0d5207810b01c0c420248070400c48988120021a80000d192055607a40c20164000c03134291420354204035000e94000690090386507000452a01900f02140209a11442c1c44c0200c0d41320000c5005407001c120600300010002d90086001c1e01905074000c0b0040d00720300e0180070040501c8600c0c10380d6004ca008524810403609001040303240501e40c607020010317554440e0b54074004664004250035050644810380024035644598141040c0121703040e503a50800e1780da118110454038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 108063669 1250 108062419 108062467
    0x60809010b010903020f0f0a08010504050d0804030905040b0a121103120909130c0509010308030a0506010306030b06010e0301230414120301060e060904061502010509071503050411100203 82
    0x314100c5254101d03a40701210f40100c94055461103100d03112540401d4000f003982500540183c010000040c8038101548030318452070080050381e1030045501000c50720908252400b40008020003024840d03442e260b485034044410080100c46010343d10840c110818207031076000d03504980f5250484460b030600303000340c81c02140740a07802850984c05a0000d201d0050243c01c0901d0303441d00b0700d0010108080309680340c010b8000200a1411581d492401003450f42c0201d43c04003001d424100800c8065000340940415241e000c000c040702a903170f0100456503030b8000b5000c0f590641d203905030359182d003064480e20aa0300c040e0520b07260061400c1e00300380d13070000d0501010305865802240d1290143e031203d400d036415203070316140a4100e41600c400090b042e0181c0c80c81c1c00c0e4450b1901100103210802010741c00350104542d0001d000300e40e00d40c0d0056482c3c0a8030700c0b600802207403a808201c4c21a20a500099205208460346001e82415201040d074031001c034021035015a100140784100b1a0083e100c075282c01d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 108064919 1250 108063669 108063671
    0xf030507170f0703050c07030f0f0c1a070204022a071a0a02061b0d0204090f0e010b090106030c020109120c021810060e0d0b2a0f220f0b030106080901 66
    0x142c4140480754440e106001c2c04101000c80e03070002e40e1a0501c6190004e41d040810f44244601e141005002c500e01c00310200d480350040c80c0005500640c00c60f99000c001c40700708119041002e66004d0001035071020000242803c1e03d044010550000350400650a0105000401640381804a2019190010322040440ba06e0500c58118507550008030f065008460500014024100a010041f1401007910641d20702e40040384c04200d1007615401b60b151022001350501c0000d011440a900700c2d0039058000d504198031400512281d402038001e035888901134800000d60703a407240c03101201ca02d0051020740014406101c203600f546494000c911080c0403404404a450400e400301401d5410603110301c10070300c448104071045c2d5035150101d180000da00480300b0152442c1ca080800c007a460016180054030314110080710301251000180c6810b220030040c0d41d0702e0a01d95a018174407031000030b041d400c42c0f002c07041408107042e9180f5803d50000e0805086403034495040c660007400280c2c0c000c001000366 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 108066169 1250 108064919 108064927
    0xa0e03010b030307021933030b09071812050a020f01020f19060e03130302040e0c010509040f02090a06080609060907020a03140408070617090c011409010c0f03050717 73
    0x30350b000300884a4480e03049800803101d140800114905d1a503c1c1d1220011018040440f001c80206c8814401d030450107010125a09034514004e80480d0070349404160041902c00002d0400d0b405540b518683e66241040840602e9a9000e4003020858589040f261500315012000c00c5040019044038000f4007400a4000703224841107680c1d85000c0960104524a07200e0711074814401d207030740b204081c1141b860a881ea0707021a00b8058032040c18610003280103910f01280c00301058404240b906440c0b02c1655010320342141441008040c1c2090300c01d40c2c3e0384503420400c0d5040c3c4e5071343c001007100a02003615003800c40d1608c40304001d1000801042c090041818070308209607194081040d001e99541030500307503140480c2d50300018050244d6009041d83d07104000c0046070b01504107510208240328802041c0b05a5507000600ea140c0c2c0c411007102e03021489045001442d040990f003d00041041854017000c001ea084d200c400d00c0c252007000a4010420000d030f02d805212002e542e5044003130705144254a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 108067419 1250 108066169 108066191
    0x806040222031704120f031709010b0a150e06030406060f06120b03120d2a02160902040503030306010c05030909010f030203010e0706050d0f0905100219030b060405060703021608030a0e0301 83
    0x8001401c0703400410040c88040810101f50041012020655802038851901c0c0707400c407580f900031310510f4000da1249810060004004090844a0416440a81d41c0c442400912410b000150300007a0007255442c7d114440800c0000d020061403004005a9440050790400b0203510b00c21995008100c9000303410032100c02249070801012142c01c1c850780c4030009810b89c00c40c1c0c1d284079410400384038140082d525150010340c0ca40d0014810001c1250f207205485241d0340c5642c041c0072403255201e0941c2507002400054041d40c040c480c4000d40b0750151059914208800b000503001c040300740c11500ca01802c1c04024019401c00348600f00301070000e10014030700700d41002c2002d40380f4080d10003e42c0c042038940c1891700c50340c451a000640141d500c07a080b1519081d89a0080e00a0b403c290420003070b48100d04d03d4a10194400e0081c034509900103030025141070300f030105000d515030110000740c05510550100c1401046107940290040403040041c2d41c0340c40d01e100d130013000c03034038060a01d80c801c1c0e040242d400c0e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 108068669 1250 108067419 108067439
    0x1e0e0114071106010e0604020d1409010f060320130f020a09050d03091a090310050a27060510050603040309080f0d120f1103040c0617070f0806040222031704 69
    0x130654581049084a95a136400020003a22500c0b964040341810017a0b2080c451811150440c0620280b100034070550501c50090702c112481d910002d009042d580c402e440400c1c204008020210302c0140070704460032200d030b00c0b00054815040c030031010507900240d0214403941c000007030710140c901240d44418504032610000c010004c10b0141d807009910261841c1e5014080ca0200d88402002a090f0780c44035500c40c4e04007000700403c807287c1910505104448840c0c08803024a280314203242130010090759001d80703851004200080c8004c400070800c950108050369040301840c8554805e0362002e01c61401c200d10700e0b08141e0002c1422100fa40900c2e880c080340c58001e994000810301c608400200c0010480140010340781352248582c8055001040c00184100450104151080c6850b0402c07421b0001c481003030a19822980c01c800110014440d403140d40c0704100351500128001c01c0542011440041c03900281c11004031060741c0c0c03940d40c4040042112003846440003000784403440e8241854448050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 108069919 1250 108068669 108068671
    0x7080408070302090a1a01030b190e0a1503050601030b07030b0d081e0c1b031216170301050603070e0a030803011d1803041205150c04030201031d101e0e0114071106 72
    0xa81410b4030b9000e000d40544031004640e8100080ad599440380b195030300004e141900701543c10103181420040306810021031184201c0c12030354410020300880e8699204c0d5458644013520361810107894400034041560380075034814010303008001042d0b580c0c24503000305070720315140c014010080c003003803000c001d9460002c10541a8282c6200001c514482110000fa05000c00312915546800001c2200f115540c548440e5000491042c1c14003001002421841c41090009104070303503000300e0810019032030500c2101c88061900f4003500c002c01403a142d0366003404a0b04260491800c04503c42521045607407000e1156411143c100c4406502101403044251288240d00070240c40c903000c44442020808200004d103030018108041e1903140c02c20541d00c4009900a1000383d0001e402c04150011030300105041c2c10040392284000c05c0240542104c107c0904034040d0040d40c420604020840755000074083c03001c4600d514000011401c040c444500d411801c050802c0d030030840d52282400d6810000a809 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 108071169 1250 108069919 108069971
    0x6030607030c1d01031401062109080a12090b0a051e09060708090709020a020a0201030b01020c0904060b040902090405070618030503040603150b07120e04090f080703030207080408070302090a 84
    0xb02c10703c2c40d4600043c0c01800a261100e80d001148900006a155202385e4040058412021210b0031211005400050b03481e103440140c0205c2d410041002041d01603480e00c0f011000b2a070340071440603078a4495035903980007203030542c800035150400c01c81802a82070803444102d5040d01a4002805c0400300140d995000900e0002400a50004680c00c0c8504000c004010082c196056595041a480081d101d06000d0f6003240403a0400d603c0d0741e40381d070000c01c030b44000c01d030003406218143d0355645603500902094070009411980c0d44011002680700e01c00c501d03209600510051200b54944000103068000440b101d03009520300e100240f0002e400030088504459961030007080e064502e12252032400f00d9613001d2010031000190140c2080300c40481d104214500d0388403101d0a41c0201d0a12043c0d035500c3e03d0050000c0303410318076800064800030241804c80c4c000d00c1c00604100055440c0580b03540b1a03003003c241c9030320a07102001186040040c41c1d900010101080c0001c1080c0c0070302001c46484c11040e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 108072419 1250 108071169 108071207
    0x6030b04020a0203090d080415050409140702100f0e070303050403050f06160507020a0f0608040303050a06120303111b0f06090109021804021f090501080109090201051905070b010e06030607030c 85
    0x69209000350f0b40140c502410401400360900441d1000c050203d0380030788200c50338907003000504003500741200e000e10710802c4290090b2260301c0d60000140f00520302d920ba4104c6143e07480d1420100c041003000708001544c0309440b1503903524103505145260607050401d0a200c2d512100400c254810700c104000310000032400c00c16150780c041d20008243c865035420180c65035404640015960f50301091050140c2c1c080e0b00d0811058842c09140019180ca5010745281d0303040c071140c2040001d1082d80244003840132000135600b40302908500300320364144001080b459601600c4041e0401ca42400f40a8101000360000c00c030181d0560702241120110480740811442c10100007030075500c0c1c4480030441d034629941d020103070021400c0050031000c0f182c040d09000960020003c2010780c014450340c14401c0c0c050b141c103410407920207180f20301c9000715481801004828004280002e21034600c6e207019110901c0c0e0b4814070303e42007042c1882c086004006004040c1001d13080b00a03180c0001600c085010000c40e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 108073669 1250 108072419 108072439
    0x120a080a1b150203040b070903050d050a09150918022106011b060e0c030f060c03091c02010606030b042a020c03060f0402030c010507080301090b011103070c06030b04020a020309 78
    0xc40d001e01c0c0300c0c05501400110100840c02d1181c4020350041d84918400d5900b070603551200c1c0c200321045421800014000c2d44000e40031a100c6008001070140140940381038541c054440104030042c4807806140c00208501070f0050089042c01054400750410b100811400c0c02d25003800381140741c0c8900c1d582001c0358000070100314580d10980301d00d00c507440c0081069440c0112490f044000708095800080280282c40101095140206405400c0406030000b080c8607250809080e07180e50015125982d1445850b40c50441e40240d8481d41c0350f030080036000024070601d8400d020301600c0b01c0d51400b5200301e2170104100d413a215038101c285000303100d100e2500e03220407546d1810303440d2440152025515100300c40410007071190610145108510950980300310f0300c010001500e640c0250307400180948418401801128600d03030191a500c0c00c1454003107036005100d007a0702c2c1594090501030f6061084030406100d4542c050241c0200400e041c0e4085280050b6090b0003901c902aa4100601c40c540d540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 108074919 1250 108073669 108073697
    0xf0503010927110f030111071e02030f07030501050609091009020112020409060f0b09060313030905060f09040606050408030403060f060302060307110f0105070f0f021e0c120a080a 79
    0x28142841c503006102d100d6001c44070306011852080d4001880e00c40c45006000071814141806900b060f083c4800e007071420082c10703030751b118440c6840d0765440c9140340d00d11001d500583c0d0f007004404801074042c400b40401e5400c40c00c0075429510010000da000d50742e002c0030700c03103074100008500c41803204030f2000081400e501e20048412100512100c00960300100300454074070700b241c0c42001210124100303040752aa41c1d07500d80b0b496008000759154004018000079550340340607100500424800c2c50700c040e010b074a07000001c025070041300319200c54280200c0c002025091038403401e0050700f008e09109050a190101c04d40d602e00c540e010080c050380c0ca0760020071029049400c0100516030003025162245401d00c002843c12412210400d0b540c81039841c070042c20081881214043c0115aa5107200c08030a03042c01c2e9101302104014038210701c42c44492031000c9000074241c6001d141c001c00581038402c0280c0810008000303c0f6600700841d0044404280010591402c44844100d03905120001d4a120 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 108076169 1250 108074919 108074951
    0xe0a050103020705100f06060314011a0307050d020304080d0b0d0203060a0b01020c03011d061f0501030218030d02011b0809060f0c1204050a060509030705060703020c1e03030a0c0f05030109 83
    0x1042c5d641c0c001342c20702e01c0600011074950081d100b5a01e50f550100100840007040c2d5110450078032548145009085862036961086001507071701400c0f5003045850a900c414102e81280d10483e415152408081200c0107210000d00940e4419a802c4448001134001c6800103a00c49102070000490b49075100c0e0158500e034028085a40300d114018020440e83c9070905030813000c14291fa070b16085a01070700000400c0d00b210030350041807100c0183d049182907802d0100560096214444201401030f90301d2200d0403e9904020500b4052613950000c00e0803d407030000c03040141024100759040c04132031000c10001d111300040c0a60b204c0c00c4103603840d015444101c2c020103144208140310300c550132000100824400c0001d024001144074a40420440d0740b0751004544902031420024001d410880108000c0d51198025080c104812426950309e071201e07800d907407602a10030704140450b80000c800c1016036425442609807501171030030328a4030354100b2100200700784414011803000035980e69456000b4810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 108077419 1250 108076169 108076183
    0x1303020307180506010203031501050304111c0303051302030303040204090309080709060f050103020a1205180a05070e0c030603060c03070201090c0b070501060503010c0903060504050a0807120e010e0a050103020705 94
    0x6400e4400e207544405000340c100a04000c041501d60070400440c200c3c4d41b00001f101d204400c072201c1080d4000040004540c1548003a00558407041c0e4412041d0722a41c0d00c40d0300e9815942440348031945800a0300c1c016040d00c00040104801c01c2000383c4c1300d00507850100840781d001c0d80c1280c000070b14519902d002d84100003a82c000d0792240c49400c80218001d6207a0340424155401d4490014501360b07140b00443c01c0e84201c041c242d000130640c0240f4840e503102e940040d038100048441c0108003e054070b00143c40d10390824425103c65200380c4041210206811855030001007800c0010318501d81140401c0e52800007825841040d40b0000004803454402c0d0321041c0e003958402612408690780700d80c07400054002050544040d46000400281d07441d05105a034a041144e0301d8000c1064a1600e1f550010200281f082c0e070f1034024280c4100001d2100c90007880702900c03442840d100150024001400380903148000390600c0303440318400c0001c1e601c03c01418122802440c0141c6d550540b86005410514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 108078669 1250 108077419 108077423
    0x5040e0a021614061015210e0a03080f01050f0907020f03070308041a090c060d0905030a0f11120909190c1e0503010b0405210a08071106070201020c01051303 69
    0xb0300105007020440754000030099906040c0490364940c65032818000c1e01d68243c481c105141100c0d92440003540d0280d80c940031051601d03a004044031821240d50000d0703c400e40c616822641000e510302c000c05410203101900410a8003580f8265070600004c200c480c0c610045040c403540c81800042e48103842040300028620100003560f03281c108518014040e01802d8500b01d510365940801e48094001d5034144901c5500114000c129010207941072040342d901a01c20790440c9174407030940102041c4104028640c403c080d0343c0e40c0b413510445040050404100c0201d006003a0050b481c21103001c403029056409030305e01150140d04544a070380e0003462a05480ca298861581050b425810b40740d00800300784034001c03d0704000c00e52500c070000210340612090289451441041c082884141004200e903546050a0516118200c00e451501c46c5000d1fa50311048031420400194401040450348181d0400c4009644c1141800050307030000c0d449a80c1c020713605c0e04008001c40c0070403880380c4689031480195 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 108079919 1250 108078669 108078697
    0x60303071e080c0106030606120209150303090406030809210c042d0b0102122a0f03030c0a0905060a05030a09050313060512090a0f0f05070e0a02120702060705040e0a02 74
    0xb40f0180143d406892544025502d051600c480010f4403642d507200d03184070940c0280f0101e41e50b03032140003512145c0b18610480f0b0305403009000b02c2049480760b02c41c4001a500552026031070342110010000ba803528960a08a6044400e101c04c255210016101003244411500030139280d8041e021070300e4008600005094841c26601c10400701603003135110448000d030a0b400e6a5070301c02d1408002c1e00342d1085201c03042104220706501c483c400c0408202d081d01c480808103984001c22020141803440d00300790385000c0c010000103401c0c421207411860a500618090f1003090030720006200140003400001c00d184140c03500d5071900c0381000f5041c422034649111454401d0b03001500c60700010596001005501d04191964012a444610019041d070007294040e20600c00c692b0a981ca40d1010050070074100d17020300c50340704081900900d44580c0340c4951340c138040050b220900203115840710903014100500303540000050200f42c2c0e502c0801c40d415a00c00d8a640300f00b90311404401c000030700c03400c04811400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 108081169 1250 108079919 108079927
    0x5041a090a060309032d0302030903070c03230d1403062b03090506030609072106060c061406091b0706020d0501150206011508040302010e0610090c020303060303071e08 74
    0x3068042d0b2102c4c91580c000d903141441511001c5401e0004107294800c40c000241ca00401c02d40301744a6001550300a1510b8203403030502d007483c1d0f035441182c2425002100d40040c544004601c460545928288281041d00141b01d1000c8510000e02200041c03175110010b888008002070490b10381c20b41d40e0a4541207814801b03120025020b0742c0b010f4182c511421400103105c400009a60301d807200641c3d015807001031182c0d076140c035640704c1507699602003552144d04e195014046001c0e43c10724491100108981e4840742941940c910f002c00407200103520100b038a4044c0800e020803a21541c07011540501c0c81403481c041c47d885918508264054000002d01d01c0d07000040c8200c1d4060a038100030704032240020400f50501407804145e864210901a00240c0a401044000f1130b51003042042d40040c0617000008a0001104c0300500740f440c00c540149102075580b07000c1020034100e2251554504240c4095800d50811000103030700ea00c94034601034018802c9003c44040403445460081c030403640125403e41d0307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 108082419 1250 108081169 108081179
    0x201050702030d0302270f06210f01030b071b0b0a060e0a06030201020c0a08030901031509090501140105040603050c10020c03100e0d0504030f12030b06181f05041a090a 74
    0x19500042c51b0001e00756009101421001141c005c030b03090500028400c10302011800c040c44030540225134011a108154003140f190140b46042450140f00d420608000035030460402c0c01074000090607000802c8450002240d0000c401e0b04100101035201e400714415486814028003d440c803030b080303c0a6100780341d0900160648503400002102d20031380944107002d00700020005e81654600c0341d803010390402c1003160701c158401d82c03003200001e0200324208504c030748a0020300102c603504481210260b42d10341c469441090810701c8180105000c940504c541c0d42540d0f20035032940c4407460300d14058001102107030f401c54000d11072000407420181c22a0040e00d004008003000c0d1603080141d80250048074450b410b00e071712481c1180d0176240c01045181c2c40d03070000e0313681c0c01080074240f510f2001c00d0355689d41d2a02a5980320018581400001c83d4051044040b408000202680454040e801e490b410920190b5a4110301950100c60a000119108031a0241d00d0803807403042d80041580894401000300d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 108083669 1250 108082419 108082421
    0x60f0e0106050906040e0304120303061715010b09100c05010603020330041505090f03120c1603120503090c1504170c060d0207020604030c0b071203050f0f040201050702030d03 77
    0x40302c030300720f07001e1485450746401d200032150702900740561038004100c1448980384015506c10014442d01d000a0001e0703960304548038020514503603600a40007102980540c0244091042c003520034088200d11b4802c100e0006a40200342070006410300140300300c404107006081d03002600460700030701603030a05030901c1c1f8101c000c000d50240c4c1c103103e0705500c8024546440c200f016101034642c40440410311040b102c9023580d4a4000e45a0035074000450b081079a10b58070280815100c0b0407901c0717182070300c0e001c4219a6034100f0341c4401c0e11801040d4561030030800b00d40402c07002000d45070030f81061641c03512240310b01810706000444058000c90141c1c0c11008812058004000300d4800061401d40241c1d62000a40c5601d00d0262a60780404280100c00c04120303140d0080042510041c03485103415903a81d5041c061118644c0b1041d4000f40c085840da09108007030b02d40700c0c20b525192030b00b00201e2a1507260f1510515014082c81d0307039280124001000c59024a080300c22003a00101200e901894401d4020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 108084919 1250 108083669 108083681
    0x305010c0806120d020c21011b02070522110c01020a020307140f150703020d060b0d06060f0c0809060403080d0501030606050307031a0c0f0c0c0109050604050f0d060f0e01 75
    0x14003d0f04214041c2141c07038408070b0410300320030f000d50103404080e2110301084000c10f0842159608400d2107004c3c6d41c04c09109100d500b00d01040d140c0c070002803c0515a010342824000c0c2d100c02c1c050091540c84040c010301d0700301401c0c07590030010342c0010302d80c0038490380081d079004007002c440c0503600c00180008115000000ba0614a00c1072503140382c0c40d000f00220036120801d00701c6c2d4078200d074001c20300150821096000c0d10340c8003116103001410940c0420701c510070340c0d60075404450400c2c0c0008a5625130381c039500440014014030f00f40141480c5005e1b40c0201a01400640601255004030744513000b0742c0c845003210011a00310035000c0d15402d050b0044802000c0a10040300c64038a44180003e10f03080c0801d001c011030790400f400c005002c0c6421042840084010410010200c00300030100e50240048090909601b0003801070013060013600c0054400880ca8205601c0b46205001c100a0b40d51a0154038940b81d07416240903201515a01d080c801030000d034504001e2480c1026280c2c01c1c18541503210b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 108086169 1250 108084919 108084931
    0xc0e04210206042906041d070f031b0503030a120609050a020c0d02120909090106030c0303050c0c04151e030c0801090b060f0117040c0e0109021b070b0313020a0305010c08 75
    0x20600b119040070341004c0041040104c5280b14405800201245801d40c801104030031601040f2a00030780640105041c11490703040984811100c42050051001803c051a020010182c8200410381082c000950302e004090801e001c0040d091a00011444590030240080880c03510500c03945c10061401c030302a402001c8200828810144451200c510014441500600c0141d03628500340c0743d1400d02100ea030700280400b0a941d2107120000008141c212480c0c0114000d64400d03465590103c1500d00301807072000d000d031042c0d06251040c0c0016101c40120b400700c030720001034655402c035502003460380409280d202a29a03140800000343d8401c040d045100305610424a952080d030781c0e9001c201d40c106880d0000740c0092020410a07054080e0a118030340c000c1d0050000d5581940d55254981030b6040c00d82142415980100309091221000794000101806a00291900a0400c0c0b0308a010780401481036140c14004600c83e8190740b21588030310080c5400200a01000000c10380c05003102e4429902 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 108087419 1250 108086169 108086183
    0x20307050c0f011a0f0402131403070f06050406111903030b121504020625030302040f120f03030f1508030406020601050a080a030e2d010e0a030c0e0421020604 70
    0xc1240c01c1181841019880544d61407010341e82035401e0240100919541240c0d40c010703508205a00d01d0040c00b1500320b00400e1540c0303c010781884544c2c145414071050368000c040306501c4100911a60b40c002080d40c0584880d480c01942040080310310603c1c0080c868802c0c540c0010845d01d4105241c0d15801c9480100307415280c0d014408620313404155a810600070741c500700f2046402140c01403074400001c210101d860a41400001d001c6501e418074170410b0b00f401c802203580007c04124405827050301c1e1008000d48140f40000070300640741c258181c0740322100101016a01c054510b00100c59134800e0140036020240005a80e032a40592580d0341d201e806000050f1003040e0000405182c5204454161081e00c0007520107102c0560b0190380c0710b07540001e00c0303510072200760b490500800503100354410549049c580362020504640050308200c544c0c0e480350301580c003140342400401c068044420880f10000480041544c56081901c004e609034900c000716495080548030920ba40010080d01881c00385c0c0d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 108088669 1250 108087419 108087433
    0x61803090614090f0d030207150e0906010e0d1b0f090509010f0c021009110411030703050603010506011d03030f040e0709090c140a0e030601080307060e060f01050d15020307050c 78
    0x1221486600442c0542507001d210451984c40600703111029504041c400d00481c0c550036103800c400c04d107829161100798000f0f1100e20104604d854074108090300000203080070f59100c001e44000c141d88200050014040070040030300d50b620800c6031503980e0004d022641c40c00b42c2e041e455a0201b8090b08041d1041c01c4550300744003a00400d81c442c2c0c4940c01d148407031074000301000e0894240319400303410b07000c0041d69074201da10751114068945006040d0300c007940b510300c59585d14003c100a422940d024120318000e030724090400c429641c10810800d80541c8840c018900c0451103c0020703d07600c60081201d00c49000132034006050646d5112060240000d900c0360401e46807580e8140f000c8404203100d40e00050345450007070f200f4041000081c100240149408992541c1c0030000c280341c00000c0c4c0c00942c0030f0b800054600284000c5205030703504102118042c1456050010300d0070015a418000c0303903c00e1021000b50010089d0342c481c0030305404981075040d0f4684c03500200281164001d60300349030550083d10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 108089919 1250 108088669 108088697
    0x30a020f24150a030609290c090307051203041502030304150513060e06070e301c031d0a05100b030703020301060906140a0e060108040618030906 64
    0x4522000728000c0054090080d1000c00240408881d002c1d084100703441a401d40c1d125540c0760400780d1005580159070210b400c03160762404814a41150040a445000f80b140c060780d801c590f414200e4000581c2403260703803100c40c3d00c0d0000b82443c0099104592000100011003020040400030300115409280340c1c0c0e4002c156244186c0e06ca00c01220024084900e149e820b08605c0c01a6220311b400a01c400300c0000413800c641e403148101d505001003001e40390b20034001c00c8075069001980250f120790541d0b004000300405032015004100c01880d10021412000901800e0101002041c080500f1600d0f041c83c140e03d00380018005020303c4500417508010b0349030f444c034005030000e95a1862540000107100803400160300500410402c107150b54507001c0d240c0000b0140c0d034240928406450300010010311340b03240900b03110314400070602d50703809104205020014220f20f6103180b0b034402002e00307041d40c050707540f40b41c200003c0800d96070f41c101d4461410f5040c4241640030040405941c9961100d05603101e1071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 108091169 1250 108089919 108089923
    0x8070b040803160f020d03030509060a02040326160614010b0c06180c0d060f0b010c0305041505090607060c080a0e070b0c01110a08071815050c0f030c030a020f 70
    0xa00500c0100c2e03004012100c80c01d8020b0005891982c0110b413110800081c980c002100300807080c10540020fa111310600c5060082401146c0c1c021090100441c501459a0b80d040980504000968000075604a80c0e451640701c0c40104c44060706800090001a8020f2501d50000e00340001c60480d4905170341c0010076030071000c20464035000484c3c2e0040a0741e503200c500780200120390040b0200306010350310b80350040b07840307800b038042040d4810f40c0c02041c02d07601207440c0030490341c201050a0400020048210119070010126010342c3c00ca01d0700c004902020160941e803034400e1002080c1c00072400a6010140b00003540045e15090f804d5640c40320548603c4260404d6450485140840d600044001c102c003001c4d0600620ba41a805400400c0840500380014400e400c103a070050b011031101010424031961002482c000100901c004629403810305416020320f40c00000d0301801d0020016818041c544200412410f00380c13407100301c982d50110000ba0684a42115502d00051301c24005014040440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 108092419 1250 108091169 108091177
    0x50306010903020915031606030e06010302221e09060b0103090203191110030b0102120301030c0510110d0905040f05040f0201051308071409070f1d030705090a050108070b 75
    0x503580c20700218116020003090301009803502101c0200202e4401050f1400c0c0703c2440016440c030000304001d0315080c0c01030142c804c166000e075002c2d04088018801030355140c6080706095404e0071800060720810341d2050040100d45000c14a000c1081048074101c0000e80000040c90700c1080184052100703800158159088003000950507040304000354002101141040d10303042c0102c0100394096080000700d81000340000000c00000c0d1952046105da5804202d60039415891020b19451580f55484034100000760b4091f40d4800e91030aa1581000c0c1c5c41503d000070030907210015500d0004110801134007001d0035100e4940a5030034034003080a1034083e40b0459200f1a00441c08070810034003035004403403a90003042040c0309182005c0020407032900412003000540301c00041e040c4a200c0701410044110002000c480c00c01c0303514094480055401044200c130151401030308a801e071801000a410201d0f160051074120080700100019075115070011412512071101703480d0510348613100e074402441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 108093525 1106 108092419 108092431
    0x1403010306020d053405040902180306060a0e01150c050601090e01110322020301020d0e06150406060906180905090102030402030c1903060905010f1514010503 70
    0x20f00d5114040c1c001420b03c0c0c0c10f90b503c085284043e601591150060701c1141682d14170b20142a0080c000e4402900b1014400d40d11000842ea0100003080c80a08081c0b04c0c0c840d500200d0f1050402a80c0003094800d10910344003540e08005960980c500485800c90800035150f5000e00428400d015085c0030300410140803410500c0102264291002c1c07011081d883c5c0b00c10428130004486455440b47d091107800c40c0070401950038000031b0300a01900640f080b80c01c1c10040560107180300031810034894000d0400e6495003c0036001840101c1d86640508800b16810b40c0c01448424044c203000080f002141c801c0f480700c0394644100a068500c1500c811886a4001c0140021481c09001c05214a00140e402c098036089410404238140028400507240c40c1d80c48007030205021080d00500c0000701600c138144070080300d010080c03024009511900c403070070504e01e00c11a12584510102d9000b04 = true := by decide +kernel

theorem cover : BRFrame.Cov 107913669 108093525 := by
  have h0 := BRFrame.cov_init 107913669
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 107913669 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 107913669 ≤ n) (h2 : n < 108093525) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
