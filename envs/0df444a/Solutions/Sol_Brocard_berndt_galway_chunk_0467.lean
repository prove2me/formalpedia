-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0467
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:57:52.879872+00:00
-- url     : https://prove2.me/submissions/f6672190-cd7a-4557-9fe3-22731ba2e7fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 83812950 ≤ n < 83992807 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 83814200 1250 83812950 83812961
    0x60c04090f0f0c090501021506030a03140f040e071b0809040b0307030206040305030301030201090906260a02150c2b0c17031315091104020d1503200901180b0d06 71
    0x94000c2040541c4c100312550781081220019054900004014208a00042d0329204a04c4c00507007003022010351284046404012070f81003000c5c01c800a0303555a5224a0402214012a07070000071510741d4540a41c000c6040b040e8030405175021000314a04140d042c02c1000500d40003070090740510410001000503220100204003560244004540300d42c91840010180000d0303812000b007050402d170040042c28084c0184446051502440c050500580c1c00c0003454001c0000700a540150340490b444c0100080348004e007502d2415006481d131282d130405410702950407620b43c03451010480540c9180e4a403180c1e41c009000340c498102d0303600706101c40020054641058503243c3d41d40c2c1b911140b59040119841080415500540060001c09030940320784108507499001c0a0085400182c509107014141d44840300c0100c0c01711034a07954580b2804c18040300c142109206500e15500150600300b40303462040c2a0486003c88001c100e5003403030001031409055080102608a2190310101c3d000403182d0080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 83815450 1250 83814200 83814221
    0xe0a080d02120606040f051c0501020a09060305090102121b0705060a0b01031409062a0409020706060603141b090a0303020d0e15070b060a081f0b0102060c04090f0f 72
    0x5600c825500c00d0000030120b01502440c8070300340400040000fa94104008004c50303500319602c0380400d21012812021403000100182154400282451641e400410760300c10340741582c3e010005507503151409801c0344600c80c40a00017449036800a0340e0f031100c01d041d01c0d100d05011200700d41011560b942c0e40f407920b80d0607507803800a10303100c0f000902c555034184a02c03024240c50342d589120606000c0c0c11251184405025140c49016061030702042c94071010044142803810300540d60307070315031700d190a0009410807042124054100000054058802d000324514400d0041c140e841a445111110140041100d06142022410b10401c80a42d0754240020020b5020350060482144a01001011420090b840f41d104030010401500400061401da5065552100040f1940d459180004032001030f194000d41c0cac20300c0b55550191054400c0940351107000610a0240000110310f00160707110441120300d4030740c100050004121815980d0800c410380e198604d0000b41a24a901500c0c0c103644200f0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 83816700 1250 83815450 83815477
    0xa05060403080702061f1202030c03160e06040506030303060105070312050103030905040c080c1605010e030301090b090a060e1302010c0c032901051014040e010e0105010815030d030e0a08 82
    0x20080300c16010301c0500d0b032000d00040f03410b01b111120b8107080b80603103181c0079201c005256406c010b800c5480810500c1c100000007400c0714050711003060034034030403140d50007403c903440d40010105071142064040c40f4000e2500401541c10b541c3ca0600450b100d4014a5080c4c00300451060203003c040c800e4892103010314000d40e105000301d030a060501017030391160003a0b4400c00151004110061a400b0140c40c1019541001e04194000a0130194090951104400c0345070000100009071607440b03501644443c0000c0e10407120a07075416000d10101c412034030a8000d04200480014400420408003c040034414185214050900c1d184c00d64100e00a4000b01c07140740410302100540e4800300d0303040c201255000503161680d81080d0100c2d18003801460b103007050240741700a800005940b4402d90b00a801c001c04a0384a540e903c2017148000c903c00e2043c1800701c0e61082c0416580c030081d56003909203010140040400c1038810504500906184641e12010700481c030f125000142c0c050b0040542c00290301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 83817950 1250 83816700 83816717
    0xc0d0f05130303030c0305060603061509010201060e0901020408010b0a080c040f0f0c020d090f03080706020714030c0d1206061d0102031c1d0f070314011b0f0201062705090a05060403 80
    0x40c0b025088034009082c8c40c1c0300c0e0300c0901c2009000c0e0755440d4080b001011550029480e1200071005034050451504555580da4401382009020f03030056010300110b43d00c030802840a10380135000d014840449004101c2680c0021800600505043d00b08081d001c80354500010740040d40034014045594610300c6c0d10068004a14014126602400b041c002d0700f0f101c010541b015245a4412501e4420b1580084c902034022035620280300c02c84405060300c448909c180c2c0d54a0344403800c490b880d469032000010200e1000d51526801d42c10341c0c4109026194581c070385200000450300d0942c0a80d8a541c280f904500c800c10109054505000e00301000d08801d6802180400f82080261007203031342d00103550750701d501030f12121100c0320700000c01c07d0881c1e420181c001014517040c01e4545c0904401c11800042507500c00c820013000d90f00803030035000c941450303008004094076002c44041070082c060010b11080a003440c0725192201c0c80c0d0205820043c00d00868500001c2503a4040c01d0060840701034000c9000388 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 83819200 1250 83817950 83817971
    0x513030807031106060d022106040819020303060607110a030507120507050d050a0b09120a0906030c0c08090f010c02120a02100206073501030c18020c0d0f0513030303 73
    0x10103c80c0009005101030140e07407511101054400e280000040e00c00c050349400f4100103113100303202580c0c0c2c2c8641010b69110345000d081ca400140e1208110001002c40c26189100b542e1005c42031781c2c040c440003880b03140361540c00c6d110080c103054142c02c04d690110074510008000740080080000034441500b541181c030301607042c0a030400a96521050203102c600dd0380c2000a400802c40d00400740d800300030191140c4810300118500102001802e407600e00004245450640100700c0408451240d601400721120541c1d0440d03070003040c80340c0180103050500c80488145090105c030b00f07070110185030884440886400040310a19401d8800d440b68000c00c0f200740c01c2d81400c0110b401000c80c5800100410300382864000c1c080c04041e40c03e41503030041c1182000e0b003200c85001040040701e142c0fa00b2042540c41e400c280054075581d00c0760820342144a24442680400f500030340c0c851000990103048038001c2c41c00182e4007450048240d600308501000300190020301c80414401460290341e0000300003105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 83820450 1250 83819200 83819207
    0xc1505090f0d0203070b0a020f04030515040b0106031b1d03010203010909021c0c0915051206060901060c08180307080703140709060302030318040e0a11100f05041203051303080703 79
    0x31810002c0c2190420401280810402c1c45583d40000d0b5025005076159001500301066000304d4100170000e00454444e016001d410f07507002030181e4062038020605990354041034080700c0009000088682c45990500c003c0740c0561241c41c5100f02c0038034141440300441000071f003264000d822140c10b02e03540780c43c4d0700158100001c9454007400d4605207080e07030514035210740c98401c0e403520440e04c0080c1c60b15401c540e1484070101030002020090034158014031340b0803105440c0c0000310b032554015039440300000350143c4900e04061000d9000320132079144c58802c581040510145603c0203405101c1d6101c00200032401b0020f6000a6000c4c5400c01c1e4040c00d10700c02d503070030141942c1c42040d016007010814070142e6004800c5650a1071b11068402c402e41c0c044001c80c001d0044102c07032074070900a045183d424003803150344905d41c60004941180d11000f0840003611103c4520030711000159041c072040c4554004001e590a0040c0241011403c040c010ba80c641d1191006400440341148085a40c4040640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 83821700 1250 83820450 83820463
    0x1809010c02060c1b01140a02030a050a05011a0304021f0f0e030d09090905010b041d0601080a0f120905030102040b1210030308130311060f071407020f010c1505090f 72
    0x1440070305258101200c12032020b0003003c3d41d04d103a05140c0100c240388841c0c01d41c49010306143c9441908001e2520b400020000c0d0012580700360399504000000e288a07505210b028141c54984200c2a10394079405490f0b8105e030002042240c00070380c24010303e10722369001c0b4100f1403034081c076940342411105e14800081a003c8440311039802039020400fa0318a00f82c1000406003581c002610006110825003071007800b40030703070348102c6810500c3c0c0005501203042d00c0d01442180d80041e0110b915903603032409441d54849030041d0282440b007500d036074040081c048804c0001080868901803d82c0c2e0785650029003203038071aa015144500300020323118800c400d100c40c02c95100c246000e8018501d03180d92400340c40702c07070018800c81041521805030b204050050340b45072200c002d10310407101d07140750201e040d00c0d490340191101c2c030100d041c00e05010b0b141d6054000722650194060b0040152040c5100103442012031850304441101c24281d401c85d80080340d10030070b44100e00b0440200104da9882018505059 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 83822950 1250 83821700 83821721
    0x10f030501080606040906021b0d09140609190308031005010f0c03090b1309060e0f0c030c0910170f0402010e04110909040201050f040b1e0406020d0f020309180901 72
    0x1030601004000b100800310b03650350f0001082d1808107103245249040c100038803408418070100045080a071404010000b8140c45c0c4980076240e034003006455400101d00305820025403503004074104030783c0040d810524007900315080d03c0d192010b015601c071358444500d604126802503181c250043c00b002150ba004400c5d010303c0845003820305241001c0c3d1801400e001d01b0b0b010300416a01e0010f016826a0307144041d0300000c00485108010040d29005030380701103401503540c00d10101246000c00c1d04041d140040302e0294440034006458550100c3c03d021f101c0045c504108240048a041070b85256988030348540b0a0401040c100107900e41480050610652035000320301907883c1028440720118800e0445900f404104c400c510b0720342c4c0e14401207806218107205408101000b240005004880300b015180740328008121001625000700c8401c8140581e11410780180d01c012403412145002d404c0c1481e100f180ca03c19245084c005030b01103011101d051440c0c4403000d4100c4c0070402c10010a104441928 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 83824200 1250 83822950 83822957
    0x8040f0e061518041a06040902070b0105030102041508060310050108060613110703110705030f06010807050f0901050103051e01061205130507050108091c0507060f060503061f0b0f030402010f 84
    0x100c201d2402019910f101c0e0681c01241d99507a010500c10717501c881c02c0c0340c04030010400ca99440e2118145800b07500329180441d42c2c2c405400c00171800c0e16040c0296401e90382140c00c0030030340d07030a107500c12100c60201800507a054090701000b0a0100d2650003120702030207101c0e008055509000e01071242801c443c61103d10700d186402605c03480000c1040031183c070203402d450000c01c1003181562440c285003036940724951601c02c410900000010100746141258103200541d8400e554900501c81d00b1180c402d44581e001d0407590040c0100d40c044c0d80055000003140141c40015113010100349000031702038011201040c5c00d9900306d544047c04d400307659400007030608603820806240c0ea4140c0c0d9003880c0d009240c103010034140090104103040020403c8000b031101102401074410b240640706500110b410f5a803942004201c03c184c60050040100f1128060010911551040613110084824000c4217a00c074808410000d00e041c103940180c2909150444400d5682c18684009800b22400490280030f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 83825450 1250 83824200 83824207
    0x304060e100e060a11031b0c030a080106020d1815020a0507030b06040605010513050105030702190b10060807022a03060c090a080601030f02012a03172a0708040f0e0615 74
    0x2090740325420740380c200194a5611f07004000340c00380300d07400f4003807202c401c4203a01c07011900641d43c0398003e248504803100c0e13070242c8003040d881ca4401c942c4d00031004001c80b000c07141d101c4100100b00128050704c0144203580305462841580350350b2182050300b04d40c03042e1440646001841403038134151040e00010704007421305515000c0c285800b5904a03400d84203207414000044005080a4005e11500402d0320b009800d5040312151440c14100d8100c00350364032050301c81d410101081260207065260300642468005102d0841030b9103d010441c19502e150709142030001404804a4404104d85030043d25000c0c0869150107200d0103205e100c50b042d600081d00340e400a401000440e01968101942540a04e000440c107a64218805450b12410307102031001a000c000e01c8040c9a400072440e04e5684c609202e41c10030b6100c036907540d852240092a1401d00e1100c02030400402c0203040010810180710300c40341c0d81026968520a012201e80d940030700c00500008040045624140c0180303020301b62450005410b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 83826700 1250 83825450 83825471
    0x5070c1d151c02040506060f0c0f12070503031f05040c02030301080d03060303050a0e0607080d14070305010819050111031609060206070f0c0203010917071a0105060307050304060e100e060a 83
    0xc0c0407120000603021300d545034003084a030380340c40303040341c0504500445050b541c03209000b400c2d5441e401903880c00118001c0d05d443d001d0f5407a41c10100c0ba0200d811500940c02d60703d60340e1a0014500040b1503030030103000802000200c0340c0b00c9000c0e000c150007203500610b84941c5401240f034180180c94403120109407902600f440026044003d403500c00300c0794548038106012080106402d48a00031000d80340900204103688041c495410164907036003120036103110358460100a03401d07500c0078090f80070b854001d204c1d03021081e5090302200030380d0340c0220000300e46100d4542c40c02c0140da0040c2c907094503008031104218441c036008903620000705007520090416143c2040010401c45072014040104070305901c00800b5907409401040c64240c0001d00f500b80d001da8055448001e500852049810584a44d8118803030310302c00c44040d040301c1cac010b000f061855444407400c6503d43e0004004440c1c07290b0311101c40c15032100030040d40748001070f03d100000c0c04c064812040e910b0703c0300c024290390107076082118250 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 83827950 1250 83826700 83826739
    0x3040503120c031905070c030609060f1a01030e03071401060e010b0a021e0a0c140f0a0b030105040b1906050904050127020a020102040503030304081e07050a020105070c1d15 76
    0x101c24013201d2130402e941495107241203406105201d03010b0b040c4a840e890101c103000c041e501c00f82c1c1c4140310300d804000078a40c0c420240d05a48802c8000d0700c007144429561140c5e94069000070510b0030582c000d580ca40017441d03445074440702071080307800420f0799100d000740061500015520701600c44040741504003454150020b40c4e40b580c0c40c042e000340e140f00c000140038080e410090812a690f01800c00510b0795181c182040703101c40c0b8800c003176100700303801c038420748050804000c402d042e03400b0361013104d00c0d6130300300307030500000c0d103014500e094001c4040715001d200e0711901d02c480c03400f521042d6545a5580e1010040005880c01070700322107620500c0c50310411822059085011110344424805070700e031081032000f0703030081c00f0f640d1145400d400000104020000c1c0c9400804554040741c2c041c04200c0c1c8440004103039800f4234200288640d2001070500d01543c016409048171174440c503020302845450b0986494040031081c40d90710307004404028032900c602c2d40b10303a81c0004141901c000800d806c2d10413914 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 83829200 1250 83827950 83827957
    0x406050910120c091a040c0302130b090d0804030614070302090d0b1f0b030a0f050106050a0e13090f02040b010e010207290307090614030c030a020a0c050f03040503120c03 75
    0xd040d10442d20301031004000070041900001c145050741084400000c6004d14138071a5074880d164402ea2910f070a0340c0409004e403080d1442c0d503908285400c0795034108000b66070264001030819134040344615200c400220000d005202071441070740041482c4640e0a030b103110481c4081d042c01d041c1401481908041d0f00c60302440c00459402c4414108962110509182c5a5004031030074010100d041ca0301090407164000158000d0403001c41c00c000c2680d4406011040382c1c1c0c2802407a00107401044003800591007542611088800103203401b0307840812004a82c2220b602c600300300e82c540703130041c01d650a5103001d20412541076002c1c00d1020180c0ca142300000e44170403041c010b800e03003070341c2001c44501c001800404801040041c840311aa0305d04180b20043c09140b110300c47c810004980008202c4400c894070180d274000c078540e42da001d0a45e02c0301c0b0300e0000a90045c1c8a00000c1110206c2c840012074010490340040c114101c010319521401c003411305041076075503c180b010b041c2082110884020740003085 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 83830450 1250 83829200 83829209
    0x1508150906040905010501120b010e010303050f0d0b0315040614090d030207030504090606091a0a1b2a0906091b0c050703080c0714010c210207030f08090406050910 72
    0x11400c6503580c500240040c030080380003500c0380d86060000f00b50700c0713100c000100c1120b00810b91181c080e80ea5201010310103d09000040000c1d6081c007441ca01c070a2410040e041d15002c8050111340c445495001c81e25006880007070680982c0c0c80418001840040d200e0307603450a121150919140ca0300b42e503000c1e95189494001020154009184e0003458402e0003940c1c0601041d4009000f119501c4030000c040d802a400741e42201410b200000e10380444010880d41600c8541d12200b80980402c00c3c100d0340581400700c107903203002041d00c50040341400200801203a510030780a40800c00e06000480d01100c0c40ca0b000b250395985407001c1c5002c2d56030505080c0800d6130991034554100b0700c841c500313030381004040d030310042c0001400302e540300308110042241e909503000c0302c1140c2140d04003040112240c0314800005409142816090010841d00f00c1030441040954011204d415590b55a06101c120080030700741c03498003000c42c0c00404c03840c0c680203c000420003140e042040d4180308010020034a07a911a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 83831700 1250 83830450 83830459
    0x30c0f030904230408130503030d0b09070801060905060304020a03060e07060e01021b040b1f020c010e0f010c02040e010e030409091a190504020409060203070302070b01051507060509030f04030c150815 88
    0x101c0000550807406c2c800b002d8400602601d403070703206032300c41389021740322944080344a560308000017240c141c8902c90090403101c807a41c5200240c1d140005008082e80040c10581c1c01c05002701002c00800c078103004501021070b40070300502c030561a01c1c10041080305088000c0c0d046401c2003c41007400107802d01038404000049030009004081c1c44006004180201030788110b00d07202008051070315801251002440e0000c0c2c07100010b80d2261410030041c2a00d116406000c15003069510000d410b1a074040c403800120b54000140e04160345084902d1500194841e000c06512940c612041103458440c1000309008070000d4800390034000c4601d48611480c05407241002c0d0b07210001000c0d5695a004105000d400031411580c9082c40030009000e58030250090701e43c40940c10000a4500341103c0141180c100001d0345400d16483d566080c0c064007001d44000d40901c800e10800c003a8266400c010b20065210345150f0041d42d14041c5104107008501e12900c050143d80c00030040900010081e48007804000c40c2e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 83832950 1250 83831700 83831707
    0x81f06080603030909040308070306090209090a0507090e13050111090d1202120301090e010b030607270302030d05120705040b040302010c021309140c0d110909030c0f030904230408 79
    0x400b080c5140103503c0c01e00e80c8138400000740b05c14980c202011601902481c0d40510200c0d44900119041c0d2043c0083c1c580c02c10707001c10001d10a00c045600103a00151b05242c503484550b03440700800c1151034107841b04005504858003240811000f440b0700c13141840600c04048c05d11000342c0000c1c42c09640100043d0841ca03030311441028440c801e001c8100d19120802d00c00d522540c5403160800109045640500d55600e03000148a41c0d25000802d00d00c1194241c0c1d801c2030034000700400d2011135040300c03012110403800c07070008801680d09000c001c403e013843d42d0f181c944448400c50365200034070004d02480d007400010407060050426880c115015240c0a0800503800309152000c11201e07070009440c400c01c680384c000c03450100041c519112108101035400c4403c0150940e040014114003010020801c42803d00c0e004028140040340d10b520103042c0040e6030405c00c01011150501801081011550700001120741203440d10b0300c1800f0000c216a2000c0c02d06485882c0610305c0b200000d8000741c1a1000030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 83834200 1250 83832950 83832961
    0x140105090303070b07120c02010504020d03050d06030c0803070b060108011d071b050705040605040c080112050703050a1101170705120a02042304050a0905060420060a0f081f0608 78
    0x30802c5840007135009040f11950f14100000628000e59140180b0001e400c00c084000d2052050044074042c1c1d40003071500c44140c0c000e540c00e64441d0301c001786000300191100c0700080880c1c0b41c985520700400096016503a15a0103140c11007803003c0042845040c01001001031014441d20700308248500051081044551a25a4140c80e286a035012038500c10050710725200801101245070b1003110000d41d424060183c9510030003041d90214204440095620b1004110b04250240301900e0240104150343c1000d4682d00c070b280c203081e05500c06950300f2043d441d07140620750340300418003a01c1100c028150300c6400c0401d0010681e00c10a4010146003508101003600f07034890750b04075401002c0c21980750350345000c0c279039814000000580c4014400c0d490030002961030801402a9452958082c01501c455900e45d55840c0d400b20400c42510750701440020f40d0b01c039546070440144a13202403900c40743d4444c0c0f507083c1d00a00507800180f480e041d035201034590b10380c1425010546029030703034a030400c420b9546d0341 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 83835450 1250 83834200 83834203
    0xe09150a02070b070c02090a060b0a140c0102071b0801050f04030c050c09070c03030f06030215030901020906040b0414010e0306060411070b0109060807080a050601050603041a010605190305011401050903 89
    0x180030000e001d40d2103400c04c0c0300459030841141c0641078070076070303262840c1d0392101445400c0f00c48511075074560041c20007881d81c40d00d1090200901201310b000340035003802d041008a0b401c81c1c10520049518141c42c040d02645181d01d012000c005003440c0700240403e00d0821141c032070720079004d0700040a01c40703101112420084148003000f800803024082b014540b91185008203145000c41090700803030714165407a001c0300d425000e60700503242c01620380021010b00521340015588014941c1115542c00d02684006560b000000c100a204680702e5688450410800c0c2c0d2494a070b12254906010000c0d0a815217500d0200c1c2d0180d02c150b0032100003540380c0b41c0c00c0c0100036030f1141080007000070040c14004203038061180c2c0100300740d40c2c161007140e46c80b5854600042c2e036011000405401c6522244c0108a2450420019a84107100d8920790302e4846d801c0e0790742c0860050a030007440100d08007041c4103030f00000109809031028024a8203214651400100190414000302c10302c5c108240000c00309400c0c0c80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 83836700 1250 83835450 83835457
    0x20d0303110c0609011a03010501080c010c03050c060c070309050306040b04062c030a090b0a080115030603051b010e01030b09010b0901030b090414070509041a060f040c17010e09150a02 81
    0x80750003d030f8030203143c040c0001e4003c05400c0700d40c007842d0071900301d90700703840c1030500c5524141c4050900401211500c00015a044000017a04404110f802c0001000e000da0070b108007805120303584809502c40745240744c0508840301c80c0d08200d000303501040c100400300c0c5509400790340103908400c0c005042001507840954001c0c84160b90400c110284d040c0d00011700b1700100800205000c1c0c5d031800180e030384271048083d15100b02114800007800b5440140030420403002104408600c6e41000980380d07603030307544050070907100c0880b10b244500100c80c503110741d50300010260020402482c041100c1c00b000d00001d005543d060203410959500803a280005900a502c20021410000d2400000d031600385085440b170301e40303000d11407a0b0340901d02000507141050301505004a603c8807561a8090074074011041d9400003d04880d030090304180c000f2043c0c1c90754450601150865511321400c00c070000b51282c1c000c4010f070700c2002c02142d0002000464000420038203007599080322114050780352240c050303000e8007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 83837950 1250 83836700 83836717
    0x7060c0e0418120e0306040305030a0b100206070f080702032205040207050d020d08061305060a0b0310060e030a03080105090a150e0609100e130212030f07020a0909020d030311 77
    0x2e20782030724031500307041c1c120b44444601c1c03040041001079a0040320454030008584030040d09a480403010600082c0581c0c041c6a00004182c400100c0c03880c0d5100103440e0300700c088641d2025801503020b100c00f440d444041c407184c050302c6080220a60500340390080d41c03442403c100d04554401240b00038400780e44114000700170003009200399101c900600f0200e48031030040609030090f00ca00b50091040e6405034181381d11401008200d0729501400030503003401f60a00034100c41d03000199007004160003260901641c0105050748843c2c04241c1040400703081c18140d800c209100381e10030101d5a000a03800081141907480070b40d4102230b9500c9d10541c0c40c0c040c0940c00c600060154190102042103204182c0703183c8541c6046540100e240c0b0b074203010301402026402071070062001ca2000400c0c0d513200c511103c2e21140302a050202c0c00c811014403a065801166018520202c0050301405518003d040b1602412130010201b011300ca043e40010000d41e40150010281b5459100003000b100e85401680c1011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 83839200 1250 83837950 83837959
    0x50d0302160602011401060206040b0417090904030f260109110d0e010203040308010504090b040803090307022d03151902040519050405011403030d0b040603050f06161407060c0e 78
    0x6880e0b04020780641981c5d6100c07034214200c1c100000702284000f40f0140203d81094650b4640d0304c481c2c48507154000500341e000c80c1128108056581d54942e54031451280d80281d54032030f40746500540040a03000e039030a80149240c51050200d0383c0c40d0000028504451180740006580303c6c810080c4042c034000c4241c2825018a0203091001290041d001144aa8426500d000350390b1380712410401100e0309044040c0030f07a048038000400084491000b15044803908085070300349592a4001138072005c8040800364103051074010042d0001c206041c804140d10128080c00701b4400c036440100042d0f8004111034070000703400d002c00e0070400f019412140540400342280e48825141203800640b80600d109550146141000024031507407a11080c50300d6003070003006145000300c0c12814030041d10800d1521540665186070000010700200003040f0441da840001d0440b914201160072050314801d8551001c0c040c800e4200c01d0789104103022103007000c0d03000c0c0300010b0401e006070084641204d00d00301030f03412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 83840450 1250 83839200 83839243
    0x290a080a0812060105190c030509150415020f0a1b030f080a0207050411040504090c0f03050d08060402040f0b070501140907080c030a020108060915060315010305060f0109050d0302 79
    0x1801020381c010580300590204074041e41d128000116520b1207101d204131810401216614102131150042c0f0350518000d20f0414184404e9034006440d000300108481d10303108000400b0890b158052300140e49503807180c0040d22503802900b54007500c60301107200041011842d240110f04c8000c3c00001c60000e15000a044600ea100e00d29001000d584506000000b5209080c800a214034250041c1c085444030750407001d04151a140510020741001da03030490300d07030710130b0b03440400d00c1001c1c82107107802140188000d262829441c00040c2042501034280790050340100014007891140003e841c00312000352060b00c0c4c1d00c40e11410080d0040c800443c2035800f8420180500000420005802082c1c40c8140203490507021020205641c0d000c81001c024007003001400003a41314906800581d92142943d80c0a00180510400248896004840180303500444007090f840c0c43d40c0c50b115090303210205a07000726403441c01e00300180c8010540d02ca0f0780d02c034640f80c900c0b03042094424408044000c6010300803080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 83841700 1250 83840450 83840453
    0xa030215070b042a0807062a0302010b0907080919052d0d030207051b0310091a01120b01091508060114040e0303011505070309030f0f0b0a290a080a 65
    0x10761040c041c501300c0c092110200c0c00343d0a03c40a8408401c0b1140e804c006c100942c03070064103941d034a0f06034884c070300180e00700c01c0c450391810081044404428460307800010f81e190788200704907032070340060704036010031001340100401c10f08002000030454281d004868144943d40c58024907102805051150074181000c1c14060410b0346a026080e01c3c045005a580d41e0356803400480c12402114006007081c0c2c0310340c0e0340c48118400d07400c030559055000390984140100da8840c0100703984520204a03107000c000a1400c0787c102c6402d8000e40135112203d040d125488250300c88004001c418000c028449944050201118000b50100781c001c00d907036402d9965a603950043e00802c0d00c0c2e4400d00d00d0080e030520f260701c42c00300e80120413241a01c02c102d03606000060403047c12100c81e080341404030f0070b1051282d004404115050400800c5900c145518121007203549090300c03041c0b60181c04a030800c0c0c10b10254010089003032555014203c1e41c0c41082c09110b21180005441030f003158480300c038a00540d8000070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 83842950 1250 83841700 83841713
    0x618090203060106050711042a0215010f061e03021c020408010e03040608040b0402150d1d0d140f070b090f0c01080103020607080c100509031806090a030215070b04 72
    0x1021580200c0c01d032041a0ba03500c200741d90511074402d0043c04840f800707500c006640707440d90000ca06a0060503d850503240303440e040c5d0b480d901c05680c210004d640a060032035110b042e404242805080e0711f102d030b944010b16055002e01881d00243d01c00300a00345502e0340603511807080c0d05442820903143c0000c0d400110070490072000354003d008039035065082040111070102c000040794211103090b40c0b244c0311642c442d22850019140078104903413000d00000c003410744102040c00341580d0900b1a60010300190303200f65034000d44803051000c0c1400d811280500c004581c00413810b5156850004090340d5030915000300310401c3c407820100402e0036000d6800e110001000141e0600c0c01e05955003100d0040d1600801560414800d1000943c061010812100007840c1c9001400802010790100c2c2e155444d010400c10541e54100c502c401d03140e00114020044d100011081e4101090680d1490310b001c109902040c44042e0078000603001d180382144a600c0a1038010407101e4058000790320320348504061801c030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 83844200 1250 83842950 83842961
    0x91a0a060e01090902040312120207020604260f030405040b0f09010902070c08030313020d03021c050319020c03030105062203030509100206060d03110a0f05100608030304030e010507060618 83
    0x5000843c0d0003400305a245042c805ca03070a607500811500040425500300311100000c060254034010780034804000143c5448021300081e02542c2900ca407000c402180300c8071651103c8c076503140d40d0792000341c1c244880c517804000c07036043d0344080c1c0b0049803886020022802c0c15142e400c0a030303081058100005183d110a0f80034198003441007020900407030f42c91151550b41c0c0025161489540104d080d0180140b40211031000d01c540b00c1d0041d68101c010544880024003000b400c01004140300000f00903c2c40845500101c0780c01c907012045003042080350520781d407030105015a5024241c001820380d252146c410004088201106000a600e61280b80040c0780e500b00e454018014403480604d104a1400841c03158403c0502920b5800b03510401d803811100078031080790000036030080c0e01007500850103d01c000c655030783c026070040440e5600c0172002011284240e010030b54a801c1031042c000044d502000610501c06d00b40303442500d03a0f007942011001000300c2c1e0b00400300500c0e10340135407624004a4000f03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 83845450 1250 83844200 83844227
    0x6020306010f171501030f050f07020f1605060901031104060518040c0e040b040204053703030903031d0a080f0106090203060d0f11040e03030a0606020c010504091a0a06 74
    0x42c036011002c26401625142e07411004100c100d00c0c00c2c0300150242c2c91103c201000f40f03070145008610b103180d42c40020120381041d56180d80c2000c40208210069030104000d00300545058001d06c0e206001008444410384c003406242c0c0b04420018009041d80c0c8290450350b00c9460040e48545d88541e1044013a1007a400741050201d20400000800076a03c0c0620031650b4150040d2503451520f403074107003000010110381008540c801d600744030200c2c2300d0302ca504006848401c007408113803c1000c40f0741c44071920404c03000d00103006c48011400b1f000090348986102c04680e810f051400b041c0080c181d10050034080d141c0c6254003c0f0340c0388400201c4460004903880c03081e10308402000340d191030b0b2490300140d00c0111046030b0000ca9014280380081c034200311400e522030058461825611803003001030290b504408011199034004000e000d80036006200d048001d088500042c070014801e0000070f0842d004610076201c100f542c030004002034003e100107107810390000a08010704540c407000d0241254510401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 83846700 1250 83845450 83845457
    0xa061a0a1706130305030612100f06090608030406020a120207050d03080f16020c01050a0c0203010603030e03061005010f050901020f070303080a0605010203070c0506030c0409050f15090f06011d0d0602030601 91
    0x4200f403140002c81490603240c050781c40c1ca01c4c40e42c43c4810303c08411015461500140714041050150640c18415800c0c0c410110780085031036032404010206890442e000540513400070002000f00640004010000b81e6000d0b043c2d864139446050701781d0400c0c1203a402290004ca000c806002010343c00f40105104802d4500c21100300d032641466841d003411703c40006409680000010f8189600880181400414034170b4135500d6402241d001c01c4c00d507880c0d5030003200810324040040390540f4042c8005580516103001103140540f405000030300172840c024008090020000d9020010791090150807082840081282c54195484c83c0091060740200e917500240c03072030814040f8083d8404400c07625050b4000721400c20b028200f60410546600181250341c0900d000c200005a0340964010944244000c00b0005500d02e0043c0c11556007869025910f03210b80307000004c00c908444410460343e0080c00c2840c1a09008903500442956000b01d41242076104050240d11000c000c6035400562041901380c0c3e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 83847950 1250 83846700 83846713
    0x50423011d010c021e010f0e0604020301180b1902040e040f03080117060a1a12160e01180506010e041a040b060f04090f090818030615030a061a0a17 65
    0x207402508890184144600580089144c02408003c007640440400d000d00e0001820740070302e444180c21205c0800c006a100d421081c10041035103028800c0907020020600410340d0900296240200001e009150302d04140603100100360750410303075043d14050702d08124041c001b418503082c04a10713803104040c01c400089801d0300219020101d4103600050b145100000d0660382c40c1d88611401801e900c507490356030000300f16036140c2690b844503100000c451105010381118440501d100364001d0140d00400070386241c3c00c00400c2081c8900c0b640c0b003c1d07022010800900c41e103d490040b5403034201d0703140740c075405814103403001d000340ca02c1c0ca104c8050240c200d400f00074a01034101401083c0c0901f4030b10582520301844100409c403440c0e0441c01c01020390450000304a2000c0d41c2c0e000c1c150700f0035003080d680407810b66282c075400d050401215070088042c3c0010f240d040e40401c002036582c10b00704001040301d0381301c4824107003900500000c201d0900b401803030119000c0c0c580213140410140c45503003a14174407800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 83849200 1250 83847950 83848001
    0x50c03190e13060b0f03040203011b0f090f050109090c0212030106210b0105030708090a050607050304061508030f0a090e0c0c100e070320030111030603070f051305042301 75
    0x148a1203040b51210304c80e20f8105021707140c019016400c02013050303806540700c00c81070b40803440f01105d94880048546590740701c2118903200614290040d0018080c7d145041c0082c0026070304421210101c441e21030307000c0b66009004e14120b0071b1064611466001c0d200210010810b6034000584036002c01d4070225189810071806144010b403050449580d000c1141040810f1000d842611400e40c440704160848204001c182c0d00c00c1e180c40750840302c03000002e80c04002c0c40104403250144510304450048506003090070406803940702e208aa0b07000d000514002a0321000c07902501c1c0304002000c0c1a85202c84c94905210319600326030117081d01c040c01c0e015000c2d21581c9042c81d0b06c01c05d2180441789000746417160031035542c00d000890f1405807100040031080c988030b840d902409400c0c690b00100700c0312901c80c20700100b450f16010f0240c1003101c24482000307081c81151170712202c0419002608101098540312030400e04840e00f076685a1020451464102001e0350805401c84020340c4484440006125500c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 83850450 1250 83849200 83849239
    0x20c04020f03011202061204050114090a03120e010b060711090c070f08070606091803022404080a0309050313030c090501140f031207050715080408030106050c03190e 73
    0xa5140d0280072450900051181e900142601c0f41c0d2070b4406400d140c40d1400d940381e035440d20074080b541191281c0d101c113480c500c01031040807816005143e2100402c04003e030f554003d441101c0002803101156515400c8104181c1309400260350101d01a104554030200d600701280c4070141c1e680710300d020f610320354086985c2003102c0d0111201c194200b03106009891041c2d6a50405520181059036000c0c1c0350302c80480c1c0c3c0c519500c118203090041e40368408218083c1d01d0060b049c841e1000e030240805228001e104e40107504001120361181c0d1182c0c040d95103035840c4000360b000305004013000d0710610000c0344a0300c12001020102c81a24010300c200205a0380d200e81c2441668424080c000943c164100b403580a0304205840f2002602c000f4140c400031007003a0040b028681110030165055070200c2c40c10400b48140b9800c1036241c001c0ca2a0503a102c0c81c02e511030440c2840306105603420080c000034800b0144005006840c1e205000122502105200c84001030094035403052251140520360f4802c00c44049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 83851700 1250 83850450 83850457
    0x9070e060a090f0912030b0a150f0c0501060b030106020a0b060a03020d0f06140c0a031404020105040302010c0302030906041701050a0e0d0e120d0206070f02010905061308120c0a020c0402 82
    0x4001c014006441c105004440035200181080000544402e440e50000c0c0c1c00e100c021842c00c2d483d075030024804290300108940b00fa241c0d8890604840340400680c0c13542d5000c01003080b61406803e115100c0c2c0c103a498018010300c82584190903420000c030021074481d40c00318003124000d003d25004240303510741030304100340c054641c80020f6009903072404240000350496548044d00f4041d0200140b2145100844401008121103d4407148000545005859018451070500b000450309005140ca09907001070081d00c19400080d05100c107104145d01010f01c20070032103002e90b00180000761596560492207045601d140c0d4020515402c102c00101c0481171485404680a901740c000c2805101000c802e4a5040c40018000c1d00000e00d030480d048244800c00140c2446c44455004001c07a20307042030001d011000c840103000841e41031409590100d000054165082014241060420846450f02d01250f00c00c071103140f1140c03c0103d00f04201c0c640600090140d003000c0e9000c0c0d400004034502000704070712 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 83852950 1250 83851700 83851711
    0x1090e07081b0915040501020d022a0a03060c030504060e03091e03030f040308031e041101080612060f010810060f090203040201050c070e07090f03020315092409070e 73
    0x201540d0000300200094500300c1d401100042d81580f0f0550300b10007089666815010902c1d690388002010042c1e941d0410203800c020100d440900b021240c2d141000b45e050700760301c2140000024500000455a445418540056a200c2d1007041116403892000e009000d007103406541043c036016030411a03e001008403010628000d0940450701d40a00800344090035002000d900341c4414021900100c500c9002040510301071441c9980301e20740041032141ea0901d00a030512004041300c00d000010300f08800601c14000b090030822913a0382c8810220725802d0035640a04014410f020034003d0080308010101d0695041a00382c4882c914010760500c29141940310b4004913080c001000c0104120030b501840c0c00c248145065482c0030004c400c202e10b00842e68110f008080300500500a03040e0308590010000d25018006940d000d00c2d54000a45505180600c212410300a4001840c1c03000e003844a00c9001544000c011503e99020300c20700c1600c0003c81ea50b140e2807080002c0410071301d028004151240d07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 83854200 1250 83852950 83852957
    0xe010906082d0d0207150201060f090506010c0206040e0a0509060903040608060a09090308100801110706020a0306180903030b090402090601140706020307121815020c0304030501110901090e07 84
    0x1000004807515049000303480e40c0c800740d082c100c0007071410380e0300340305510b0b0080d0345500502059040c03031004183c50030782000560075607251010030800b4100307411011003101c60a6100003003603540c60005031540360500f50700a511000000380454040340b03590400d402107551181c108103d946180140d0759920f02641da0800c598028441084010300c40c80800b903105030b010300008a1241c0d90340340746003950780e400c004402046541d401c00a07051040e0403410003c08081000380450011211921854481c2a801030040342c1c0000304066224001c0d00005c004000701e100e06000340036200041801021421300440003341010004015440c2550039140100d8004160000548400300151502c1020001c00f98942d6030910407000400e10fa4800765101e8402901c0d107100500039598810101d90003104907008001c01c100d1a4000f00308482c00409400c0c1001c900103030385030000a5040d180d8002d9a02c001d06e19800c0106c0001305140c1300c2d003c1d0075a58000e0301c40b44000d07900c401414988010884408001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 83855450 1250 83854200 83854213
    0x40c150e0105040b0d06030503070524041a0c13080102030109060e0f060622030c17150a0209040b041503031107060219030302040e0907030302100e190302031c060e01090608 76
    0x60000a000030040042c1c00c1790000340355070743ca83d200c0c0e046810080301034506801480b00180d034880303032246e4605158603280900d0b10500e0b00e07541e104218551243e0700c88580001e07000040e8111484411299040010414030107060741d03980d8094041d40c024010b4805c0c0f1346c1010400030703000c041074000c00c0c080c1800c0d102e1429a96101e80a1080d59040122842c2d00d503801907501c8000140c45c00c04102c05140070b00403600c0040d00f4402c80000740038041c0850240d40d80503803500b4615501b02000650000404030000d80d840c680100010041c011031004180c4c03281c0f500540d00c180da46c801c0c10382e03021244651594809100e40c924030b1a1204010311031035015030403920032440d1880c3c0343e910150100348a402d00606080d100c80c03541344042c50884001ea010381c400d9a00b4010325404100301c40368400404000d10030003968004040d220791400307402c801e01c020614007841c00c050003801a145e0400c1c0c0300300410310f4004c1c0d44e0101e601400321840703500e030320105003070001c40c0f0000ea9000e9001550b40700d030028003e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 83856700 1250 83855450 83855459
    0x31805010c12090f0803040e06100e010e120111040503190c0909080403080708030405120a02070635010f080d0906050c070503190203062d0a06090203040c150e010504 73
    0x410302c0e8440d50410401c04848000320308004859040f2015150303c0c070086031154108541e41280301e401404843c40f40030a01645c4205079401001d614580e8002c0c64450b102c61104004100091100d0941102039400c00811155400d842c501520440302d04408803030000e4074000102043c90088000540040c102400c2401554929040b40305907621880102c1e00c0c00c0da594a034250307203800401c001c4580c028000180000d124003040040283da9002d00c400303280801199019540f41001c0c4248400e210031042003020410304844010201002300401182d200d030400000303d805034090250154202600c0c1c0045188140041c1c603050129964603011902d40c1400003e031042c2d000383c0c000c020580320b4554046000d49003400401d00f0605c40e614032800c0400544109414898010b00110300000441610701e145110085407154081c003c2c5240089a101c082e03030103018051980220742c00500000034801003180f5000308500b00c401001300c4a6492042c1001112583c000320011400248180020b00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 83857950 1250 83856700 83856713
    0x22a030d140d0c0309060c18061101020c06040302010608070902030f0112210201150905060f0108061305070e0a140f040b19030b01080c100f08060f030a060504031805010c 75
    0x281104070304010541060260b01008082c0c0350160680340000c1c3d121040d010400c04c4034010700a246002d41060020089000300c41207291110340320f00c20401c403001100720a00701d0294102c40308054120162402450607041c080c0c0605214401c000b0280300d2010006001d07452407080e00e0151540c01070300055a46845c00001e810300400c00d042c1c54111504102e20f040414400d80740c480c4542e550008101004402081180700e80558055130855050104100302d69413143c65a50404a0908100e041034030b0b450046206400303181d0040d046546132105000d00c00e90403400c803a10541c01211810742983c0c42e41c40102885886c2014243c00441d882408882840c00c7c1c0c2211001d8000603000e8504142c002c1d00d0f100940c0c50799070090700c44a82c504014041c264045c010b015915005860035540400340460080c4240310f241c14170410084500b001c502284c0e12400c290501e4000182180c400c1da2850034881e00414064804401085803e01600e182220301c6070450102e4005844010162810340c545a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 83859200 1250 83857950 83857967
    0x906180615120f0703060603060501050301051c02030303010b0304050c040e060f04031e0801080d08060303030f0924060111060114091e100e010603051b0c01090b07022a030d 76
    0x245000103115030707240c03a0302c03403410b041c42100000602205030400c0315002d001c45086412610415040c09405d0240fa60000210307030446105540c1c21040105102207aa40720815510003940b501000000059004800002d54080c03802003040e43c0520341d88c4000c2101f1981c0d003051092064101000107152a000048060380c03044c0641480c00c3c0f01408403645071401d81d12b001d106c2c030200322420700620042c8000c0010700c8130a051420019841e00b000000280e882c00010a9000c4030218000000d900107011b101280000040c2010401152440280443c2a1390121411030000d0794481441003000d4001600074102d480c103425000500c807050080c07040c01100284004441c45034181212500858511881d10072940c02142141403420812485028941030344503200b01418081404908200074100455150000c0c40c20390b51064191300040c00340c045444042c0c415a40c01c4100300f5074035000b0620581e840b050000c3d070721940701c111100031040540c00302056010703031180501c48e2a40d4022000f1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 83860450 1250 83859200 83859229
    0x506150a0311030f06091e030a05030f131208071106010303050904020a02030705070e010e0c0f0a120902040603031e0507080a18080304030c031103010c020a170708040b0909061806 79
    0x16a138012244400551900b441600d0741c00c400c2e03021048840c1d0146403580158124058180a5460b00903106401802400082e10780c1d1004201b5001242183d0a003c0385d20320500d9104802c0000e0640c18030002e0040074080310614042601c449020740180b80200d0024180c2c2e41c0741d180e0714240202c1405000c0250001c0c003910703055100030803040010807070400007076004052074401081d0560404003000007040016103460300e051002d114400000c9040030035186d91071038030715040712009210841e4001408c08a034020f9001860070002000341644440170008807502c01c801c5112148103444210b40c2403151800141078000240f0900c090103200c0c003c81c5840c9031020804040190b1154020740c21580a64007c449429036910100200003941110312902e0104400800105010701e0004e51613404030800100029410701c503001100000d407064aa03175981202c06161aa81c80700d0603a00340740e01804801d4800c1205000103106440d0a400030a0744010030350400b040f075216901400000c00c4c0d01d154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 83861700 1250 83860450 83860453
    0x601020f06070e0406030b0a060303030b1e0d230601051504120f0c0305030301120b01050907120905010e0304080f100209011205040312140a0606111b1c030504030506150a031103 78
    0x300001182c0a205d006016040103180001c11030315501cbd01900b200e00b4801514001c11240c4550050100761104448c0001c50070364004800c0941e529000ca601c07082400030904c01c3c2c5600c268044503400c0020702e0b40c141e031010344420a20680401c07081c2d6290080748210f6420f0313081406502c4c0024540d02c81450740c644291083c4000355240da480c1804c41d08260005100704d2400002282800b0880940500501003a41c0628250a01c50703001044e43c80030400304d4130900e44406a10307003040703c25800a005c50103950152516182c40d0408141c485804649810701881140040d2031403003aa44202c03a0280340507100c11120036500700b104000b9001c0100140c06026000a07444101001c03070090010801c60204180c0951501003440f000302d61b0b15400603020080040c0416011b40000203103100664080c410010760f0001400c0040c2215951200300e10f40008090b241c1c0c4101600300010300140ea00c52010303203407a0b03034890f0401106002080710482c0c0c003c030410310400101d8100345519280800c01b40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 83862950 1250 83861700 83861711
    0x71701060e0405060a05010504060e070c050a0b0705120906010b03041b0b03010b03090f0a03050f07020a030c080102071e03140307030b04060806090f0637150603050601020f06070e04 80
    0x507503803556000c04840649403030b00881c0800054440c0341c82111301501c021141040000d003010303c032450f0690014250418000c96554280c240b01d01001035420301548012806468a0003141c000c0098120040b08035142d1034081c0401e02d0f41e40e0118005042c0c072807005c1c155041d42c0c2c45807141d00c10111031628110781c1008400c00441e401195600450280c2012000c0035581c0c2000c80215107080901c121079200d5400c15030440d070010782e020b801c03500d414a111030515103070309d55800010381240c4039610060003158030f10301c0028002e4064014100080c0541004403201905101100140500303100090029600140f200483c001100c05550010050700d4002120b8031000081400c0b600d0079000440140e00200821940510812094071070401c840081c01303190400340207540040382c3d20242800c030510780d0f44c5580e805407000d01d904032410800c5038040c032891204402c894000070090103400c6c00a8200f0700001c01079400001c2c50701c80c0e900c00700010512540c640c03004443c461300da4442540c1c0645c850 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 83864200 1250 83862950 83862959
    0x22517031e0108010203010f060c03080402040b0316080109110d030909050403030e0a050c130207080702062b05010302010206061c0b06040609020c1b1507032106030f0c0905010807170106 82
    0xc0c001c0e1030190010400040e565414480f41400480070342d400813080081303231000040000c0e480722142e50000d030f0648001c2141600750002a00701001000c17640500001014005124401500308685184c02001c484150316001c078184540100007642c040c002c81d0441d0010010842c00f42d1201d5030060203442d00080d5a00c0f022062030800c0c2c040e00301a00d066010000d095040d01c2c0c068841c403c00307020704104500c0c06145544600460003081000b9125100103d000016004042d0710b04006840440c0c1c81407a00b100c10701000010722082c0020f90042c801c0f140041c081c0c0c240030308041038502a406851020f030f0f000d03035a044502c85005041c1900f0070b865110010305513082c4d0000e40700c0140d000019080a10200c185101d400b80003045540c0300e0301c80455580c0501004104407440d07141c00d86072016410f10030511802115824001140c82589400300010034014910a000001481001407500245d07998600d081540c20a0048040300d401940d400c20182d070003441c040200800d1040007040d45640d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 83865450 1250 83864200 83864251
    0xb12030f0a0c021e040f02040f051306030b0705030a050c04120b071e11010513020a0e0903121e16051b120c06190903090506070206190302251703 64
    0x40484000f0130020f05240322544d01d0103015100861300010411814240341410340c0001c25001d1242c82d010700309060101b00c95040c82e4000802968201034640450b0511080003415035008480802c031262400380451041c44456086070219218030707101c8100030142d51201c00358208042d141341c0071b11002003000d80945820328107850f044082c075155640401c2c0b01c16401c5080d1140240380d04510001c0400f2240143d9442810b4400e988130811749003031a5550510b01840c5104113134801a01c0144d48080041465a00141c07541001c2d40704400c100980300c103400705030078014603003802021500a01c002c6150b440d0700c0e440c0090711002c900c119217060452414511465000001c0740c3e00c160000310401550300c0003481c86c0c2c1c56502036580108000c2c0e41c035841c01007c2e81c07103a00a4511900c400203013181035507607503002d80303901c4140300c003282c000c03a615610040d00075030180e2100b4000c200c01940a04a540380480d04810094020070100041c9950107440d80095100420950140c10003242503001c2414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 83866700 1250 83865450 83865469
    0x120906060806061c0b04060c050f0408010218010f170601090e0c0c1c02031912180308060a0b0f030717040f03022b0804060f0c09090b12030f0a0c02 65
    0x5281d8040d28550038603005000d0004251029a6124920011250001840c00a403160300036000b980025944142c100201c50500c41c2006030b2518003408200400c6404041d8003c182880c24100c0d60304540070b001006455221703803040701e000400d00e1800004034840707007038010661146052400f40401911410740807400355040c0c0e40480d0380c10020030340c070413002d804005042c100c031080c2444802150400c1d1000f5070368451a220844401000390208a040340135a11111070150300080c10311204004025280b40d80b204440250005450030f00800d080c0e003410301110059404a813103080c134050035403009240b664005006a0300704120201c15100c03c5504070030301c9000354030590046140c8801d81c14024075100c0d1010041e11100a610340c0c4140030404400f0315400308409003804030303560b0344600340310b00140410003000228500f40394140302c3c040d070b02c001120300b6507110035010040760075030500380600b40b00c121583c40300d41d61042043c12000d840000207420b00c1c099a2405a0344c03403035950301103401e4a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 83867950 1250 83866700 83866709
    0xa020d0c08010f090203010f02070222181202070509010501090302010309050a080c0f0601050616030c02120d0207060221070209151c03030c030c080c070602130806041403090603040312090606 84
    0xb641c81300c42c00110310742030240700540860000198200309064000981480043c8502c1c0c5c501d002110f42000c8440290300503582007003440e00b000402d4001418280d03035000c9480d2002c40140030345100840c01e440d10001c02030684d00103039900c03004240bc1d540150014141c200090b646c51107200807030000030304080f0040284400720005030a4a08005844610700b07030041e007041d44103240501803e03241c41088102695100c3e01454001a050b00d01d00205a20007012008000d0740e00031035100e01d02c90f80c1c000541008039015582120f90003400b0100050025445040c0c11555140c108400005445c080c0c80c0d841c0c000c05a521079900800300da100207040c4c54152400754280401c040140010300d5010301c90704034042c0312030405000040ca402402003444400610103242a2000b05041c800e101c01c96040d100c100a0112040b40d146468255080e692a0120b80480c3c0c074a182800c0086d20b0100803094420b50b942c0507000c1815616203642c01e841d15048028100100c030743e25805003001c2607885c02004000d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 83869200 1250 83867950 83867981
    0xb0a0219030f08070201050103020609041a030f0105010501090803031620031204031d18070212031e0c040f0504021c0203040f0b0a0b06031f050d110103060e090a020d0c0801 76
    0xe42d03402102400000d0020145030940e49844c00410260302c54008880300321000311000240004440742494601021602d0301da01449100780a480181c0c05600040c140c2d04d0980394a00e58030341d9082290740e2448221440710150280b00303151020303103004d104001c00b0340d1908800b10b2859140001e4461071a0040580050014418000d000926070442164078201d01030070103462292a8000205445806048100040600400020b8042c1e0300c01c0c40341e00b03c40380b08540e20603a00c2c01c040007002d0080f0758844541840c00d503800041005042d65804075411600d0304000f10112500d004100802500449510303140e120200c100f103041d13030071113100840c80f9038818030036203c0d88411428241c00c081002080c68001520748443c0c1d0030199100002d0725481943c142101440e680c01d14013044400d0074591005401030640c2c041e84080090700b45124086450a0340c003007100c5aa01c403014440e0900c2a103980034550810b80c4140c0250601040b07001c49036005005200100740e454114500310303100300c40d0b0b00495 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 83870450 1250 83869200 83869217
    0x2031b0304050312070309030e120102041e14120a0314120405060a11040614030a02040b070308010e0c030402090411012a020a05090912130503060f06010f0f090b0a021903 75
    0x104244210a0b5030801d0b080c6ca4100507401070340e60060500f1903030701c2c03d0314804c0141501c4840e180c0d0007501100c001c2e01f00840c10f4144031240c101103070601e086500070006962024004070303201d810400006c080c0f144404004140432482d948043d143c45140c0c0901c0082c0301410404005901003050031070303001d584503a00034000740c5002c860030022200c0240051248050400c0b0030480198001110304013401086800d6942e034075420410002031280c2d9110801c2d1034030200710303130741490f400000542c1210400c01c0c00000304d42d10000c04442c0c03480b00304c400940c000d44032400b26010813610141c0d17000c000b0060400408500d030b40c000031004201407045812995003031464a104500703040884000401c2c041d40c8050860030110350035034a5407001c03a03628400d00c0e404229084c0709074001d4604801000702a094411f00c0c00d056245824441003241c201c0d01203040340c6150b4108502c44d0341c92040dd07044a42c0c61410207800c0000e0741091f0760061080e2003c510880000c40d0204810300c1c810140207101e511610f11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 83871700 1250 83870450 83870467
    0x3021908070e0102150c0d020904090602070b13050d0507050313030501060602070506040e0a0905150f04020a0815011a04080f0604020102010c05031303031d010c031410031502031b03040503 83
    0xb403000111006411034003c0c81e1003403c195100000c0540040c01d143c00180c580720380352818030003401400f41041e800340c00e0136406000d0100e6540100740d410300500e4808020340c2c440c1416201d51400440040c081e5000341001d1001138425006403081038400d0307055030714150144410041c0b840d000c0e001515107940d80d1004024458041202c0001054255041810249440740d9030800d11801000f40c2103403a1203090a20400c4014050f0200f000b0925040d51801d09001c0d01d03294543c0000c980c200e00801c8000d601041510001840011301c2e41d01d44030b00d600383e038288020076819a04030b50b450711452005000114034080c003400440110180c07034005140603e4a400028291858141d2100038020204103002412803886206e4041c5901410702065181c110120554030101d40e070261691540303020450031840c3c5c1d150304050724514040c58502c400b61500c0c5044070544055120003007003040d1813141400706880d00e40140d5440310341440c2c000400c000f014034203142a401268111107507000047d40c140c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 83872950 1250 83871700 83871707
    0x40201210c110c03060609070c0b040b0f0c04030803070f050f0708120c1204030c05120a030507020c041503060f09020405041218030b010b071104060f050406092a0302190807 76
    0x420000440c010481d00000c03c011940320f80300074144e2401850000700003107459000e4805007007259803140c54800685442e0030031004451080e20404008403c41e004035152052000c2a181643d402c82c01d40f910f075484020302500d00da08004001e00a100c002d121054081e200c2501034801c007809182c006035910382003550241c0c40c54005000d000f80030018000f04d0b240313144201e0000d61050b810309183e81d0441e11400c100f844e020080408000b0000001a09400c142e856000a4090300c0702d6000c5072080042d4000702b1040d07854001c017810500d02e59038410408918030b034002b4a40380313595900001d8036000e030350040b505983c1d00710f5058920341081d40f0710440103a403101c00043c1c0710440800b2041d40302c0c01c40c0c0d1008003185040c030a00c00207040c04151401807140520521050a400500402c152030742c440112003091046c0c410b26110300d180000008000d0024050f2a017440c0e02041400c0116807040f4984003411000b04880d42015402d00c40e82200c0b070002050440006441e4507a100036180421004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 83874200 1250 83872950 83872967
    0x10617070e0a1d06150405090a0f020703030b03060a0c050d180c0906060908060103080d050c0c010c02060105040c05030c090616080d0b0a170a02060901140412050c01050c0a0b040201210c 82
    0xda026817400c0410010f01084042038070140d9100b00d6041e0915100c5808107400b8001310100e00020714400656a82019099030282c2400301013502602d0003a80c0703c50440e811194500b02c008041001000140224962540000350078403072078114025102c21501c402c401c0c070410f5004062342c5641c4200c01d002894204882d10003c09210006000c10340c116030303642d4240d020b209403100ca140e4980000c00c000c034240500356400d040300c00c00200050500c0c150001e42e589006e1007820b016514060354070b5501445001100d00c40c01d01d261407945408150810710019910007811403409840c0c541d00940080c0c14400284620a45100e02250400403a41001601e180541c4020b00c01c040382c0040d801034020100d00c000341190101e074101e4645a0b4100180c550410204001c44180710000700480d8025000d1041c00c20ba50090742180d020001d43d0300107441c00d21903412004490342c0440c000d40d0000b030b45540c00c140d005106251000e01000e4001c503503689089141d841199030398844c0c0103224100d6005d0101d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 83875450 1250 83874200 83874211
    0x1140301080318121b0409050f010c080c1303110102010905060a05070f03050603150c040b0a0309060b01020c0306040b09030d020406050a081014150403080c0f15010617070e0a1d 78
    0x4031310080c01e070344415545040462440c1c0c40166010a50032059495a2104540a070000f09644100281d034511034020070007000e8880100301d2100204100000707110580d074511600d00c80e030303486190a584540308410f402ca100141199210342d11400051400c1c025070b802007401d450040f80310300f0080006031a15224000da20100740c507140c20082c0556001801c45c0c0300400800040c507040d03e0303040c01e0388501d204d00d4004075070f51039001400400785d80c0d040d80103541450140038100140001400126228003055403411341c15030040c40460042919164050b8000403008101c0340f600b20342c2c107401c0099070400e50280c0042080494803540b9150000042540041c0d016a21000700c0d0400e0400d03840c521110300380170300800c4142d9407035001c100701004550207550440c002607151040380301e6050391188910070300700060107100d80c01c40c5c5050a103c4410b040e507441b03071212030b0221048040c7d920340007030003090340e81000300d881c4149a060315071b50480750140074024905444001c0c26011740e01d4603030011b4039 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 83876700 1250 83875450 83875459
    0x20d050a0b0711031c0504020a0305030f070212060c03010b0c03040e1501110c060f090a03081201180618020d0b0a080304140f0a06030c021011070c080102130e0601140301080318 78
    0xb4401c250103170744101802e100c0d441c02d40040c00d902c8038000704807a07921a4100070040d100000348406801c01c070300049c2a010f40708032800c0d51030f909480c009985452040d18511880300f170520040c840c248419014014142400c0122030a103607440c0000381510100780e035041510303100e940c00e500081d64080b10f54003025411800500896031008045a4a0300c034651080701d415a0200300c850a5546440e200c0000b56005070000380c0310b55001e00907010206082c1300d02030141f81c1100c418541610540109400c544004944150312402950320340040d612200420704100da40c0d14140510360f07900c275030764005000100002e64540d82031440b034a416000d5003010b5845010f00000191a0380d940d0b04190040d101c0318a40800c41000007101640b4183c111001000b40600b000e47c4d5924190719580540311071809020000e0496030b0710800035080740b2410f4008840e2031880c04081c0b1803105194a91360300050306141c4515011080604410641c00030b801200168200103450300d84641d844040d160103d070700f200d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 83877950 1250 83876700 83876707
    0xd2d2d1109070504030611040915080705010309020402070816050106080c0607060e0106180c02061605070f08220503070506090603010311060f0705030a171003030804020d050a0b071103 81
    0x22500e109250299000e503105402035800660710910410580f0019a440a402c0c045c21100c055000300681180c010098020b00c1c1c40c00703040e01c0d0f410a0414004131192140070b04912070030140110301404050030301740e13009a002c100950016a0240c002c0000d508000c0340f9901085051405e5402c2d1460b49e80600c0f01ba5000320003200d550713540c00c0d04071010b003503100000080000c000c5403c940034100d143c0c001a1120300d90110300080c0c000c50303009104d901c40706500395403055503401144c224081e91250a072740080c90500005c8002001ea1090b9101203005604607400d0000c5051803098044a4417030450b544464108204003600301003151001420040b200c0c06c1c240b620200c04600c16000c1440041c0c2418981c0301d100d07030700d0340307510302140c040412130224140d5070461802c045907a54844081100007030314011909640c0fa09010101e80075000031500c46114503d143c40407541084050016644203140e8030004001410400c96428218480c501c110741a03d0701010150001c0c4210500c90019013081 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 83879200 1250 83877950 83877953
    0x1b100605060c070603180c0f03030f051306050a03060e100509010909020d08070f0813080c030109110409060618090210020d0806090403020a020907080114030c0d2d2d 73
    0x41103c1c020b0310a6482c00052290044c000c42c4511010740c4005400c41c50f1071a00403030303403c09040502050341d0080d1100308501c004c80400711a1840352040e00b181c1e4454640b410300c101440f41005007403440341840c010601c15110395141d0610802500c0e40c01180008000811980c103014420a005206c01d007000c02c0b0305011070700403030500c0c894004000c003007000000355003081081c0c0040b20742c443c98114100035190895070101c262202c9c524020307816076106420545140745014064858450340c09250000b0751000002440058203508404079606515a440030440d10707e0806050703000070710000081450300ca1030050001c99000a040f40d0708541007100161111170300304d01c1254218030705480c0301119680d9418120b0510b034402000940c4081c0768030034011215409410907060719180400e1250741d0040e0010190764000010004c3c0e0007051010343c45010074000c040081a8800d1602000000140b1100c194200701c6800030850b000781780004468100041e850700c4a02602942034080e455802c0c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 83880450 1250 83879200 83879203
    0x180e0a05030a0c02150304050102030711010504030215191104030201090608010b1207030b0301230105060c120c070302030709150506030f04020d1104060e090c0103090312050402061b100605060c 85
    0x1058160b0741440035140c581811511030031a2800d4600c00d03003203000d45074102450500d011b9031066130200001090444032100600b010300c2150300030707035058005190001600380402106e003001030101c9400303500501c070308074503039658050b04120b5240440c10690b60313400e41c40050410032007504020101700756180180580d13040c403401c80300600c000c2e200ca03000b17603078600008901510f413203880b10f0b8040d424903130007604090940107003480120306500c281e07800d60388910a101c0980624003203c6580e0788030368500c1001e410400d00900701d90300090b09840340203031280c0220745401605d40c08a02c00da5074070603581e028481240060000b8040c111101461424029800c40ca1110090f001034440c0d0006080d032010441d460783c032030b40a0400a04184441540c07042c0880302c0007012101000c0d2401105202c5e10305610a1180100b10b03541034980418079000c1035075400c020b00c0300800c103e802010030024403441d00d41c00c1298880d03001c3c0f2000188030200340c00c1303001001d42c0c24541c0034038041e04060200440d04c010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 83881700 1250 83880450 83880457
    0x9060b030115110a020a0b130504020c0307061d0a03020f0c01080c04090b18010f030209090309030a1b0906091d0109051b060904020a0503220209072106180e0a0503 72
    0x140d450410f1241000500035400c00c2011040203501c110b13243d000050383c030401000b03007444668109150300125903841c01e0006a100740050203080342c200708000720029143e0344c403030302d03d030b90340004200041400000501e291030081c1e04181c001d41c2c0176096021030100c0070884444409002e180160080c1805007004940c0c2c02a80590b07030714242c983d5050030142e1200c0940140345030000d4044040b07540e562860745810300c840d01045c1d0150395000005084081d0000403254156009401030103218116141c810380e070342c01480b03140d03148000c00d031002544406500030720001d040d440000062880040260b0f540701c0c0300b0810b00800e181d04040720100402c0c0c002ca84003030032041c0ba025004c0c5105410f00000d04a20444c0c0080c3c0d0b2051011a10340d00b0303254864041c40c400c02c0418800d00c000b0407040c6030790b400403004510003548008407600041c4c240d4829400c2c5000c03c103400940c0b00d0244032a0003640141c42481d00001c1e0440850424000b644046001d40c400b51280754000d009100e405450795038480c413 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 83882950 1250 83881700 83881739
    0x30703030f0509030604030504080115050a090507020a06050a021809070f080a111303170304080a050d11030703091704180507050c0703061a090f060f03030c0a080409060b0301 77
    0x1400d40400701450003502100c50300300e002000c2c0c07201c43c540352901a01503005401241059803030a0b11210040513010003036001d45400034060350640703107020701000c05000002c040008600620420038001080ca015083c056801d0b00d40141c2c54001d0f40740100d0505c0c40c604005442180110203010348140c10010340440303020507280c009a1941c03814001d20150030405450f50b000701c80003841070f00c214055031500c01983d228440b110b110340389600800229000548010308068810000644c1d01409134004110300d8841000100703004403505102a55500112000d001180d00c03500100200018080d020821441010103241400e08202004010b80c401034000d840c05681d600101c0c49150045051382d00100419003200c1d0200c6d00e9103058800750110006072540a00520984201450400012b5104200d0194026582d945040802480c10700750024660503000401c80622000c206100205030ba031b00540e00c03140d130307240742c0306d488400c48045034080000d00c00144018094060791903442005203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 83884200 1250 83882950 83882957
    0xb09070815041503050f0708060402060a050d060e0a0507022104140a080a05030a0f0e0127051203090f04050103031b05030c0102040f090b0906060d110c0105130b07090503070303 78
    0x1081d9002c10010442c68544040115404034000100080001c0550000d682001030310709069403680c0c2035030b61710800d0f5030007580b1110074481700e845a4480d00150034204c0f0804404580b90b070380e43c5400d9900c2001070391280c200039112401c020007070b501085205e1410754480e01a244410a0700500c68582c0118080e51140d1548a4a40c41050b60343c0d50301007024081020030b86121804a2401603647da0000f501030b008241e08441c0c001815014480d140c1000d81d06860303c1701c4001005509114108207590040020001c02c5004126900d89030050060003040800130340d0b6810f28a8100003031442035010561007182000c006000195001c0307040c160395051059800310320701c0145040e038158050340f07005810a43c8080b90000d94107444c01c0385070301160864241000100003580c140b040380c640440d0f589410034010400203480c000650301075900c41d1542682c19040c2075040c0891820b4800543c1c200c0001940314440b1820b1000d00785055400036068102924420314050200c0d84480040c40042c050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 83885450 1250 83884200 83884231
    0x7030f020601060e040c110d090e0114010906080a15030507050102010b0d08090418062d050f010611070e04060f05010b0408060c03060612040f030921020d020103020408060f06040b090708 82
    0x80b4002c22030001c0c04211603041e60004e40423218020510592441500040d45070800009012180001d000004030010f9540e40a160305011080d60564000b0f040801c00b1030740e17628141e00400000001001840c030940c09000e00b45d00e088002425138800fa00348078402c400410316071001641810455442c02030584004c22024499020740d05040b0501401809072814103c10303100e64070000304840e005400300e10001d0440c19040921004507601140da0701052811600140101400391002c1e05601d1050f0084881c2c0c81c0c0c84504004c0c00b100141d8044502c00c1c2c603240851000d8446004080c007420403103010038100362a000c0c3e2159100b00c041d00800421100002050043c2c54160888988a94041800c00c00342020300c0c150000c1c5c0c00c1490180c0000b107180c5008540000d04021031048800003000b07608003590a5000c00c080c680008a0481c14181e0030000014448018080b407031068064080400c032601c1d1181c00c0c0804c0d580b02500c031500ca0400841004030040d00034003800d8201c1c418100d020308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 83886700 1250 83885450 83885471
    0x30c060f15221d0601030303051b16080d0908041406070803010608040606030c03050a11040b010903080313050d02060106020f03070807030804110622050a0b1207020705041107030f020601060e04 85
    0xb41084240f40e08010000c460900e03440000089540c100e074442d0307400300060707601e00d020940441e044803010f01c1c00140801c0300030288034610a0304c0e19030780d000d0f4111620700a2030790032a00465132603501c00c031800100860304100a2000005d501c0c0810410340e08240361568035070b9206285d00c03050084006022119001c02d0030700c4030650000c005140c0c080305582405803030342409581c07034203a101f0454880e513080c075002e4803a041900030101450703410307140ca0403a06d003140c0d6240f603140c00040613100c0030686100c4d02d0001c1003080119800c0c545582d000b414941d41462030084c01e00c01d00642010a59108224100000f030320b11080300c503c5030301403419000c0c43c0c5031894480141403010841c2e6030300c0131010a144d090380b82d8102e1036848104000c074510102954940600480080707a200740d004543e000e115000202d4064619180e201d84e552058548a5403504000740c1151030350350010b0010040850001304041d000440c0c0d1044080d2800100860361600344002d00c550001e8041c2e60017252607804028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 83887950 1250 83886700 83886769
    0xa240603050109060209101d060a020a050141010501080a0e0d02031c060b04050603100801061509080303270c030106030f061404050c01031a03030c060f15 68
    0x203035034031070000e1242c8825810000b01a4000380386044c40707169808105000c1e140124604194011000810100014010100071164000008500943c0204295040001c0081c820b81d85621605d5529070321840d07040110000000e04400d03040402c40010700c8507111541510451030444002346072880155845005a501900251a04000c180710303201c1c890384000c2e0044042c003045031b034000f0703024041e5451805007800d40e649407203100a8054100000d01207810144002c51b4008068101c240c041582c49290340d0848a443d4070111404040d5820803030801d40c0219110001d081b410300450940c2002c04109020560000583c4600e941030605003480010500807200d140000400800042d5074a04015180680808040300d945203030807001d141d100b028101440c06250014000d14030783d40070a00643c0200f4060407080c050720032500c1b01d05c0c0d103650108001c02d404a40c0c2c0b000350110b803e044000c25050b03007000d00250f42e020454485000d10391034002c42d040c0903155031016000741c1c1050f10f0303190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 83889200 1250 83887950 83887961
    0xa0605041a07020c010806030312010909020f06120603011a010e0120031305030f0f030f0c07050a03050a0308100612090804150507050c010507110609010908030a0309140a24 76
    0x303031442a2a0304010803030741c000c280b540c9013104c00c0e02c40034400d070340d08800c0588074428026018142403000c401804203500c25841860510304c00303041e0290701d01c481c2e0700049154100841d03541c40e01c1d080604001941c2800c0c0503800440c03c01d000003601401c000000a89090880d0750702c24100b00c4503e2440080808040540070302d2520481625500d141ca000d5880e0000c1d114001c542c000c1c801c0c11030550012200048050100e80103102035820042d0a44840180c2c3c3d1041814008511803580c021965585002410f802135106400800b55503403540b50150210400400c000e054440f48038007003080c1c5400c4424040304003003413400044d40d00072501d012142c0303000320b030444001455a074040b48a001c1c1c004005090b414042d0044a2000001c5001110f00d8801e08100408444841c3c00041d10703810480003424020405040980c49540c50740e04082c40d41c1c0281c180040080d440b1030540c4140000440302007250351058014001c0c1010070b4552013820101841c40381e03001554074601824929250b03110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 83890450 1250 83889200 83889233
    0x302010b0a150810030506180705060a0503010306051b04051504152001110d0b040906110d0605030f12031305070602060a0606030b010f0f020a06111305120a060504 72
    0xd1401c410b441d4090080c14241507196040481d84070710104503031202040c00f2600320f0f41e00500030031443d5500085c074421041c80e43d08188051240901c04a080d68504015000742c0409583c4e0946a6145003050004e41c6c1029005c100c02da110000a1184030050b0800c5070b055490503038520800703010030742c0741540502c10f0b0b40c030500360b1800b040b13400141c0c01e90000c00b07902d00c0d2400c0299401e8140041c0d00c00c608841048100100c018010048445d024003d40c000ba00da40c00002e000086001040e203030384007580c5502c91550342c00880001c0700d0008414510810300508019402440d0903046c40031061303584c0c014a01000010403010001580e0541040820000180c0c80401d85440c1640c41c040139507100010350b0110689820030b6000b04181e4400e1180800d0000e050b582c00107012090441521304104000900c03085000f0201c200002c54454000c140c0f030800385511944e5980c54a00c986488422030340c00c0144540e621041d415000c4a0000321a0401e540066001405807160714051070f1a010340800d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 83891700 1250 83890450 83890459
    0x100f0806040213180b09090d171e0907180e12031005030d02160911030402130e01060315060e190c0c0f03110f0c030d110c04020f0c07050a0308070204090302010b 71
    0x3c0d10303103140c10f854001c030001c000c00340c40002e01b03602c4090340262208500403490f000a40f0035580681005484080c09400c000703220420881c1c01c10140303001c0100c580880b00c0000c3c0e94468a4100405400302c0d50107543d2420158040001561145180b80c0b03526980c0820140c452020012444200030302e41c080000b0f00740282246c899040c4000041c1d01d0f103110130302000b086030b000da5001030700c1400c0d40220140d00d2002840d0034034607606c5a08000032035820060100b4000ea0300c3e869825140c81c240b003190301460103805c5988021120002c89000d0714202d4000405150008050012041d45e1140444502014440104801c003400074102d403113082111002e481c411b4003d40d030105041d00701410300e54001064098620000111141c43d1707903140b90380c1030b05401d03500c101040c41003540700f8404013140403c04015a502d500e101400542a80c0090086216a13200060244050402008003000402c1c080d12405521461030715500c625001c1c102000c0d01a50307e80303812408141c0b00794410501040c0040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 83892950 1250 83891700 83891729
    0x509090402270f0603010b0a030204021b1902090c1608070809030109060504050c03120a03020c0f030706020301062a081602040504060507030c0206090a020d1b08030306100f0806040213 81
    0x3a0202e61290240e410310031803c582c2d07021502d90304040c001c402100f940641a00301d41440c0d9802d000082d884005c011740407a6020450700c10002091000c1816001f0141c1610f4003000d0238010003080c0c808c00f801d01c28000000700000700d10322420300001441c282e0410302982c1c507107150b8100101d42e8072400e4002a4554a0041d071081004241c0e4880c0740100c0c0030b401150b20010050090542d24002c041501c03400e49001d21220305100c1c440e800400981a18500384d850503050211214516040701008545403078001c00180551940200c1505501103070301c01c0c0c13480c2c02000c00c4040c00d0b0f0300c40498001c2d04011000868401c1c1010010790b0b40e04107030b40035004206c9481c050802e8002080181ca203d0000703420310141e0384082d4800a41d4a0051085074060001020300740e0820170000f0340c4e8141151000c250444804c00c040410f600741c03000340f401c00044c6a691170403404001c1425200c112a206106085101880191b0302c0101c0c164000403c0d900140c3d00c11102d070392507980d41c100c0e50204503d8402003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 83894200 1250 83892950 83893009
    0x6020408071401030902030c120f031804051e0402010c17031603060f05012a08030f04030e0105040b0d05070e1005041a0301080a030503060103021902060906160509090402 75
    0x107420044551030014485048241c1004400351940c41030043e50543c801005c42025103402204c0c0400006039104a0b040078000020081c15034002d042101d006105140208401e070400d80100c81e806401400e030251501d00641140c0710404020700068104440444908100402c0c840908041c14000c0755103500e0703142c5441c107008044001245040003c1c10a54001180c2003601da503c0b041ea40c0584514001e43c20206000125038100c0200f000c40003200d015400c08902c5a0b00154040c03686440000d4441c40c09c0e04000c1e243c180c1104038181003000811041050300b0038042540c0400c826941e002c05d03640c96800c070450b0038000021586501c0609840c0c0040b2546d0400300401c12100c000c954600c0c200c06c00410368030107000920403022a50864000b1000083c400c40045900440505006040000b5183c940c03000000c0c0703015403000769100c034040c085030807030400c051540402c0303a0b5520100500ba00710028003600070048014059440d810105003150340301400d810010308e20319110a000d8100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 83895450 1250 83894200 83894203
    0xc03060a0f0311010207060e010905190306050408130501080106201608031c0504030c0b040501061206050604050a0b030d0f020a0209090d09080114060f040b090a020406020f0615010c05070306020408 87
    0x300b2003c503015110b03921300060664010318401c1d002c0107050311640011031a19084c0103604000307645e0024049038040c00800024054810f080c00341b40503100050b11440c0d69458000713070100300c0d0007281c140480314004200c60355110101d41c2070031410104007400394a00c8910a458030b0040b1000b20302008203006c0c0451400000805071413080044550590380b8000800c02c80304488040e200070f4000340803000010040f0b0000001c075034100c1c1c42400000b030442d40c7c41c0100702002800c0b003c1100d02c03940711828040305180c0b034040e0303a40200300070f0001c022100c008000603503141c0401c180001803003075002d0b0750002a030003071003030402080e009804c503046072616590b030a8450380311544480c01f1445140000c906940c0511400c1c200d00c10070030b5802ca440d140c2008101c030340141c403012640e0103a103e601580403a2526100c890180c0c058040141e11345051030350181c145420400440c1140d0b110f54100305034074404840c44404803000782800095101c190401c5400e118498102a001500014000034003200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 83896700 1250 83895450 83895473
    0x7110d030e040f0b090403050705101a04060e151306050409050d020f030304052a040c020705010305010b120a0b040b030712030801050a14100207090e03121006080c03060a0f03 77
    0x1045a04120b0031600c0307810f01003124140c103650394009081d4800100001c0c000d400074035100380200704458052004d040800c0c01da41d110300b03501120f0400d20800801d01d0819001c0e0340064440c090a0040301d1402050039240c05820ba811184601c81d02c2e0b42020b0081e105070310142c0a091301810074081107440303040641d0755071407584581005200d030714803c003003170003000c41030300c2c020f03036115019101034001074050160404441d01124031248032600900100e0b0394521615442d05030f1030b00540b064900e0280090103c4805a200b12a051002c00200c1061394100240942c052190b4000040300402503004c18000d0a8100c1a036400d8401d5000c0418440380c1c2411100200340700340d0301c0140301d0b80c82c8c0c0c0c01c0c00071200301c500c83d600d46c4c0d1501d03031403600302460000403090900400b44120382c074155891941c4010781d00a0401d0705095000003071079024120700310b074001d64007600c008422000c591400c0d10041200000625070f03200000040003140c41a95040c07008401460340c0345d5940e003150303103a061886038000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 83897950 1250 83896700 83896727
    0x41d100b01120c0c1403030415020d060e070f08070203030118110909040804030c060516060902030f01050c04090f0603110d060207051c020f010509061b0409022208030301080604060207110d03 84
    0x24210317072503003c0201c00001260701c47c3d0f50205c9800e908645541c039030000382d08203915031418035417a0328002c102c2c11643c2440c14460f40140d40c841440c194417500107010305002904007c2103420070801400014100c0d506d02e050b1400309040052200c103190109a4103000e0202c015522107040310601090194042c040c1040d42d02031020302540d903955000c242e402e44240368414000f00c0c805c0660602203901035008001860010b019a00f13200e03e07800b101c40c00c40c2d17811161001c06130008074090003030301d1451140e0220301c80102c0e4204442811500c495003c2c0c5c00404290348201c4ca00c4118100b04111601550f4500d81e100d4100c0d01c20401a10000303010115040d401c40040c4a05008a03484e407205024aa001c0e0100c4000340c4510f484e1000c000b143c140461140e0308410000308400104094184028440c04a000801032185243c0361400b00007400c455101480d2613106000510480002082039504158000b8005940b4042c034a07144141000840d06d43d9806012000441d042c0b603000b83d10811241c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 83899200 1250 83897950 83897963
    0x2505030a060e0d03090b040f05100e07061b0c03080a020a08040f062c0603070302120a0b09060d032c061c05091501030f11150702041d100b01120c0c 65
    0x2c02182008a08845c400130021b07021407010008180030481c003803003442c1907500030310603541e4182d0102c0258003a50003080c2d00b809a07074050381c020459940d0104036030248240c0240e0115000f10951145080c1e16000c3c08040c240c1000028100348090003040032900e11035121602c1138603260b8580c540c000200e902d210b400081088484880901c001040104d001004c060002984003104001440b400303800003072041381415400c0051040c0c0745038150419200b00300c6400c01240001c44402800005040904400d001e0021850300400080d004400364903a84c0c01445003058004038409200c004c44403044c082900040300082e078808125800c1e1300c0b1015109507210a00098488424040d176642050340c81c480003414480041c40003800c0c00714440b1950380904501d44c59a00e038080020b001459842402d4a0043c0018464086040c940512aa100e841c81c0d12480c0c9560414041070b00c0d45503001012140a603100e018201d507a00039011940d81e0901d10800f0002c1d0300c0300c00009090aa0103450940d0748 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 83900450 1250 83899200 83899213
    0x6040c030c0f06050a0e06040b18030705040b130b1503010603020901030501210305070219121b0501080f180601060c2607020603190c030203041a04052505030a060e 72
    0x11285103806250403154584e41c0c3e03a00e0050304000031502406c1452180354000c2c1e0070040042c150484a0281c00240c8680c1004104180948101841c03c82d00d0f038000c9000c0d904200c0c0018440c1d44842014a5401c1140c0c00410309200907000a907000000c60107102003c1004000420450741c9503018000e824803e0302c003040b20340d0b2103c42810181c85c202900000d01c902c07984041d4000b92152024091242c80a005661038414410030522800ea40d50480d01e04c2d05e0726918103a040c421020441c035001100040c2c850440750070304000800c5120000e10707900161030440d01184001c104001c998240508410a4410958485a004090440001003594102d040780b900c209080481400f06040d6130102d0b080f145000c0150342400201e4100800052100c074511440041001d01c5000c0d8008081c02a580144d03a403916141016014441007921815484c80c02c08000010b000001c5c200020000705440085001d0070300008920f28903581c10854240c090f44000d982000f64a4000350340041000003034605 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 83901700 1250 83900450 83900459
    0x50c011401030507091e0204030803060a061821060c020d1202191115090c090901050402031209060903070f080601080d0206060f0a080a1a070306082d06040c030c 71
    0x150380001e00000d0300315004039804000180341039102e14020100c030070f9500303c68442030540c10200d8005034070503500ca00c00001002100d107070100c8568080c10319400c1442150400404201003020070f40900c0301000e04c1804941d80a82045040e0745400360301c0740f010b101300390100da0001e458a06613480c40001c1141c2120000140401c0d000b611484a14020240350080ca11401200c0511220002d440307140201110000403000c000000d5116482d202c00074840e0b2800c00c402d1140d031074001480c000259140505200050341c0210340d45660307011000e01c042d01c41105c00006025841800711155051040d54000905a940180d1b03030b0040390381000c151034582c2e070381354a6a500c4172a00c0070000c005800050000304149043c1c07150301441d50002e404e0f59041c6440d02199807600318510006d075582006c5100043c42403840a010030b07030264140c9010b00500385001041c680d20319480d44000b10306200700500c0000705000c41142c8a014446104503146070a1a0816845c1038006010130b40c4e4000701e0720004038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 83902950 1250 83901700 83901731
    0xe280e011a03040f08070f05030301060f05070203060a15051815011b1401021201080a05071a070f0609022106010e010b09040c0e12010c03051605040308070311030703050c01 76
    0x4140900003640c1501c0c66450340c0c3c400125403451103048844170000d02c844c502046030f0b07c082440700380c42000210340c0d80d4184200035195012481c1d200d800c0000420900340180c8000c02e00301e800030003e28011440720b40c400d030b02120f680a41e81026400090b148042a035001da280980d6004085e20191564240c020b03d00458252405038100050313101c030740d40c070800010000070814100000e0740d0001801d050200c2003030140604c1c00e034045405540644807981c203102052110070010425904281d603000c500a4242509000304440a031000d644e00c1040c1c420310849800846440364010710201074110034180e041000550700b404946584110400480d00c0c2c0c011803035a6041c2e500d146051400c001c501d804100c05040b01c480000308000a04103042c40307945980000303820100b01d1b040080760845031b24000400311000140116614440700c094800501e811100300d8080d079820035002d99440127641030a079401d68418058000910000074550107050307004010b090305000400007400b42030b02c00e01151 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 83904200 1250 83902950 83902979
    0x3060e04080702091305061305060708070206070f210510090b0a270c050c10020921070e01060503010302090606030f150f03030c01060305070b07030504060e280e01 72
    0x10710001c0104064409480e1010724591710910a10044048101e01d50b41c241c2002820380d4007174491404081600704002013072203615030103401c928001241d03140c2500c00958404019102d541030002d60307040710170218803591440203501e03105506030303403803811040040700141811540c11440303040144000ca01020b1b40e003d810101da0f0020499410103040403407440e0080d4440080404402002c09968500c102d64000c4181c44e0090352582ca440f41030002c42107041c08403403000509050700c1000301d2901d0341c3d6000308420b6045010750000c01090301c0c4c0d800203468041160003100161181e6800018015441001141079138802d880782101c1ba2512420310a290009a9480342d02c80010000102c01c903040c0700321034000140c01485a16800140700201e425607212200c01401651114010300c00d0090400c10140244046e8101c0c1d8541045920020540d00070340c021101007068400c45010755a03600ca95240c440c0100f654000c007190a800c0303221011040610a12109038541030002842c88110340c07c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 83905450 1250 83904200 83904203
    0xf160c06022a0f2d010c02010e0c010302040303020a17070b101503050717092113120f03030207030203040e010b09010e0609060403140a080a05040f05100f0f0207170304030303060e04 80
    0x40006588a5109204d02034640052040e4100200d03140d402000003401180c071069540d4000180000f02c90f0f084506000078009460706140c010441000040d90018400c144a604074114001242c0d022043c000c0c648501e510180c5506944000d0020030101440c00404562404040000318045141c050b410755800722841400b08039038071a03441525a98200c03107540407051908bc0c0b043c48060244114001c040400c65411000d404103803a010080402c8c503400c003401900d080d21a00c0c071a00d0355032816940e80342c41c000b420180c022545a0815000300f040d00c3c054002e06407541525078441c065064107800045000340006c0b0f03121021340840c18020116440c01c0c0028103114503240c00c50b12000250106102000d000d0f114025410380842c2e4000c0c0900b40c450300300d580d915503403464898004400e103100e070442c03482004400c140000e0240c103d1805582824182051844030311200416070411001c0d520042141062010090f4041c40210040c410b80f4442e4504022143c0c9849082010b500d04840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 83906700 1250 83905450 83905453
    0x30f081b0301050108090a02040f02090103050108010504050c06160b040b09061f06050f04050a12050f0309010c0605070225061205060d02040902060d0e0a0c050105030f160c06022a0f 80
    0x103000f154170450b0311a6008407010304445860010b9408a03045403003406885036200c0d40483d8421031582d0600580d801000c0c544d00a124078105a101c5988882d0011196803040c1340c0003a00003104c03a941144261200d8125000744103070320f0a41040204200d04540d84591801420700054a80700c05e480c8082800030b543c81542e00c03c1e424140e09a178503070720040080d4452101400700188603902c1d40f40303400c080c16650710709141100761868800e00d499035204001e2501d4106104200c03860b40e21002d001c0e0710300e40002000c1655200d110040c4d040420030000003071209110058400c095207801d007020119080c0e0b40d01c003075070b00700c0d9203201d18201da0050f220305610140d80342580d000340c501070b002210b0081c0002c111078985401c1c02c034100c048406c80d080780682c41c1c010071506814080c500c3c0c008401460282000b03403031444c102e01038584106006182c1d0a1a070f080710342c0ca081c2c2c80d214448242e0303c0d0390300000c00c55131141c0c00210f80c5c03003210320f0201d0003100314902101d9124914000c110521503094140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 83907950 1250 83906700 83906707
    0x307050601031502040305030f0904060609080613080d090609050f070b0d0c050c0609070501090603111c0209060f0408060601020a030504090e1c05090901053c030a030f081b 76
    0x103071100502443c10783c100262640038000440460010720003011185501d01d9150340e0398410324144025940268085424030921460803c800314020440130750007030140c2503400240301186000c0180e80112012000d1307192625180742e007048559400505154040d10859049040017041e40e030b56503640e40104080c5040a003c3c16014400c0741e001004401000e0034081c0c18200c102058034035001040f15008031070342c4208010030076940c00c03d9044000d08028603041c0300e05100510403021a10509020a449114911034490100b6103941030710b8011100030501c2d5960001c1c1265018950480e0041d242a8080c1002140c115170000591031420f59154544501342498420800028102c02d008a041409001740468481800c074a04c01814a040d85640b511482060240545040140c00a50091015000b0042d41200c0d0b50750f2400400318032185059090050051515002e02c0e04240e15098400e1510300000c040d041680289080d1059842918642e42c3d154401100048442021001c24042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 83909200 1250 83907950 83907953
    0x20306030d0c02031005090303070f0e0a0b07020d0204020f2701020a0807060612030f120c02031605070e09070509090604110d0302030c06040501050105040e010b03030f0901090e010603050a0509030705060103 91
    0x12021442e090380000c0940ba10b01680e4a8030009030341c8100d6100301c50303070000010807030500e8001c61102c42c18261803074808181c42e4a1008215510454004c44082940211b41a4210360f201118204981d9010f4030541d00d03543c00540d0401c41350801e40c200c1040c09480c0c0380d80c02060003803c4440703004500507402000401c0c0c007510380b80310700d0340002002da5a2039102c0c58003080c410049129180c2c1c0364070a41e220100c03c3e0340b00030010701e00c5111a42186189041c0340b883c05013140e000054403c800c03241c0d0549010b02a05e40b07421032821509034000000c00041404100c2000c001242c41030868500341e8507000c1540d03924400b103445200c00c40700203100340c9008107465410709165010160080c860f00481e0f02d040e600035601842c04000725000c840b03580d110001800242000d0241104810014000b80034a81105000940700d02036600d038000482c001280b09000eaa100d000c591000b80401000f4011755611444018054034003110601c042c5030400012030756103440002200e0f8401c0d000b502400d92a404e5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 83910450 1250 83909200 83909207
    0x60402040506031603051014070c020108090c031e0106050102071a09060405180103060e0d05030103080c120f070b010b040302060a08090f07080a02030c0405070f080a0906020703030519020306030d 86
    0x30340300b59014401d003800b2404d56980b0407080d0b00a14010740091400c5100710030b00c24241c0752810a055107401f15281403004880d08411481420f40c1d0908002225560300c007130395031400710000c60140d49449012200396034220941d00c1c0d01216035095000340303c0d041e01c400045e0b13640c00c0d451050b542804400c8403003003414159400030f0510741100800d014600791340e9100040104140142c805c16032101c0b0703801002042424403441c2041c07240c3c0380103840d55900704000501207000502c8050030107000090300d0940f000302030051000340052189001e0300d46044130440c0d401500800411101c00c5800310002c1807400f4520155030840354028043c900e041420142100c080c007000d898140356106e00d2010803456041804024003410100005000c8491507004240c40c0040214040340a00d14020600c0002030340984403c0d4605842e042c20882a100c00f829500203140164025101520220f055000c03d9410b811040c0180c0240d424243c500000c0b400100032448140d0b112581980314501e02d07902e4600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 83911700 1250 83910450 83910461
    0x7030c0507020901091b030b1008060f031c0f0c02210c0a0801020c07051f0813050a0b0a0c0e0f040908120c030702060703150303080612100e1e06040204 67
    0x2414a05141000c050754042048200203811041c01c081d150a10a0b0074a042c03103140401c2c0080c0ca20341405592102070108541c840704801400070043c6c1d400000307040391105108100c0e98400130b4100c401000b04100c4401e08121001e918034005400740c81c840412621448040301e00d40c1c0c00400036844000d007982c0c1d103c0d10510100079042a4001c40c10102625640c0d1502d840080c44008009030b5549214000b05080c002c640c1c20445c4030b410403149044981002c59070000440c8900c0c1408402610340700c6195a110524400c000e20758031600b041f400800407040c0459005846002c801e12070541516070655410341440310b090b400440e403c0101c01c4500d0107402044505004070812031810004e400809501401152940c00c00c0100000388100136904200740ca80c450300b50314080040550a0007048206e004605c0040d08000b41c820104001d603039903c41d1801c9210032502200d0004000c541c01401a01b1b070003044011500805440350140381070345000100c0703c4a0faa014001ea03640e550b003080700400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 83912950 1250 83911700 83911721
    0x305041206180c050f0402120606090a080d030b0a080c280f08010203040209010e09030306040c030e0d0c02130c081306060b04030507030605131509020301150b0d0c090e0703 76
    0x241c0b1803040c2c000034003011640c0c07000c150003150b0814806081206000d805a8070383c3c8050b0085104005c1285001c84540000c1e1300b0410440d00e00d039999882200155841c0e9031074003e08002d000d21030010030300e1500341e40b0840c0355a10646800b00700541e07620320780e6282d000d4210300075088204009185640800803048407020054038041c902d00d42e84034a00003035400f81c3d5410282d0aa94000244400e510b401402035006121070aa40d035403611b0480d00345526404054082d030300413071b110342201c07103518025000b2005007042202103500c01c281000d4000d00311843c100f01640126500031042c1500c8600e4040e1504042c141d49480d1700a480d1104440b031031850f000825246541d40c1c0d000803460301c08110050000758000c07401441a2402d41c01c0c800201c078006000d010507002c004080900242d11034814440c1d0b21000d8800050341240360000c40e001d0105e000c2c1e56032280c2880034005c00c9503c128005401488001c003c204221180c6801c00d40b14540b050141c801c4040361100012146446a0407605116 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 83914200 1250 83912950 83912963
    0x40216032f030c0601050319110d060203090c0f06090d0f020a0305011b0305090a030c02040203071808210c060c0319050c03070e0d03050a030b150705030903070e010303050412 77
    0x1c440d144001d4101080d4900205500002400d000040f0200502c5000d40401c9000c0c0c1032030404002030a003108590b103001010710181d501d5086056490340c021180c1c81d60044401c0d541c1e490100d03a440c0d210a840c41c085442000041c0b0150020309081013941c02104020748452002561601c13010511002d5110403a400410001c1c0400024400e006005c11031400d6603055404c201801405019110004c0c80000140e102889450120750b0180c16480d00907015100182d0340c0e15641411501e40c1d1341c1c2808079800c8800c102001907100000200502c0e0702c0c800b542c0d88001446101416074440c4160400c101c4154848004102500d03c2c810080d6000040d0201464051040c50070840595800f201d0701408140003000704500f254001254440135202103030b41d00c82108080d82c0280c0980035100b481410103559540065503030303e0b040080300d00e507029190a035807501e03998a000360342c0340e0000b00500d00038003c036800010f105184040c410f040e641e040d260700d402c00b070400c000544061112601030f940c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 83915450 1250 83914200 83914247
    0xc021522060e01060303110d020a060f090212031c050105060306120f0a0c0f06030504170c0f0a05010b010e1801030308060127030201030c140313060b0a060e03070504021603 76
    0x500300d21542c860001220000714942c5e156040c060810564043e80f825540c000c1d407802c09035607038041006d040d5541e000c0400030b040d803035440315440184600e21009400044441c8901d02000d0000042d0562500708030440c0101001181c201c0240e032400e00c10290451404d00c04100c4514000d00c400280d02d402d1401c41d110101a4100149004030180054528040e1004280070046400c2030700c1c0090012070400780514100381c2d0f41e8140d100490b0301c0f902ea140314049455841e0f0001405018201c03084d16044402d0b0b074095043c010b0007021000020750201d0106802c0300c0309401c0900c011408142843c44000040c2c0c0f8544090340c2c0540010704940c1000004003101a200400c08584010700d145020049001030940c4009021100348172888030500980c0342c10300c42711903044800caa0b4003051203800c581845c01949040c801030b11410781c3c29544140b0105c0085884d603849000c141d000c1000f00e040f108240e54034414002244100450310100d461203829000100b8015070008c03102a00b400401101c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 83916700 1250 83915450 83915453
    0x206030604020f07060504110103050c18030c041406190302060409020d0b04020408010506030f2a0a030b16030f061a030415020d2c0d0c1407060e01030c021522 70
    0x2200d500600017150800c5c0d803075061000380064940c0d020344030705003800e0410180c144403205011706d014900ca81c00b520300254103000400d403000e002c1310f886004040c2c01032120800c1d468220180ca1001c640f0749028144110300c041001ca045d10240040340d07000b07000c26103042d0a1103030441c06035100d901e0300c1040076207a03c21600113442c1c520090004011500c00021141000002c050038644990704110865100040c9440c80120084400844400000e40140b4248400e0040b90132200e1300d60000c1d08071038000301004600da903c041864032028081c0d42c00c0100000c0c10051100311201c60054882c6e508003c500d16551440760001107030028001e08030241400030070440803060b82d0140e08007414054032800e903170080f204041d4410309031422603914004608414003800c5d98511004c40e003041080b40e940c601e10140081c147e045107203001d0387d6090310f0311a91907810183c02d0f0b03071580507520b00180c0780000da54203e40c80440d6256614051040706501c0e44c0b544410710008020b003450700f20120002c40042c1d030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 83917950 1250 83916700 83916727
    0x3120c05100c0806010306050f1002010b0603090105100b040602060a020a110109060209130b060a21090305032e05060a02070e040c05040e0a03020a0f0c1d0f060102070501020a020603060402 83
    0x10300a990100780416480c1664030002d240950140440d418035003031240c103200590310900d007000e1019058401c030a244003201c81c12405440c00404042d0441400002e104140c401900002c0c45140c859042803201907640040c1c203071501c41d9124842c0103821840c08140a086d013900140840c02861404190301d540310802c203070840e9258074084030b0190307000411005d18100306081d410380c0c0c10f0340201049100d00050100d8030340c0c842c00e0441020064084103525000324280b00702e1413120000b81042000c0b8410f490003401e9640165901c012054003120200303035100424a41d2882c0d1241d0020001c5841c0c036003824041ca5401c003020700380941c01411004a0000030540c4401c1c81180140d8032503400628090600c411151002900800383c1c10405001002c03d800013400c1004983c8035183c10f80c0760481d42492008440141c0014500314100f6107520a4101803000f07450040802c001c0c04850340e00c602c0010381c1c1c4c49405119180c096040a45003070054a4503034043d5038010400360002d450721f0129030705103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 83919200 1250 83917950 83917963
    0x40305010510080714011d010c08030c07031202070221010e030d09060b040603021c0602070210020a05010b030619020d020409020c070e010504060e190b061303060b0906010903120c05 80
    0x40040322800c2d2000c0060301d800300401c000800030154071903148008400020000816011150345600740340b04005100c0e40704e10940003000380c005490300c0c2c070b0741004840d48800342c0c81540c0940001d0040d00ca9107001c103500381700321a482e07a4014103006a18610200c2010b0040d035003000c08245550324603032600044070900003440c21802900d000113000890340f03081e1040304d003180240c900035031a003c824401a2504080444070300c0c80d11084414400c03031071410310064407402200a4020b02445100c2007441e400007050400d052040000b48404154074047c1550360704100c440d41c8a4400345400440c070507032554001d00f0420280c1001528154651440c00d040e81d10208031200243d101e44020410600081c1d20280582000c40f030a0000d03604e4480c900c0c04640300a00800c1c0028030385c803070f00684030001e50701c46100c0000c050306454851511240c6c0d0841c1d03007103910064611508080d07002c0c5080c43d00d0070074107110707001c140c54405c045030031070f141c540201403220f096005000204100390301280c010000c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 83920450 1250 83919200 83919211
    0x3180b0a06030b1305060129040b0315031507030b0105070519050d050a020307020120070b04080d020c1c05070f030602071703060a0302040c12050a0204211101080c0403050105 77
    0x801e005140d403800801c00c000082a07840c041811141110010f48040340316411a100c45008845407181d02056103e004c8070038220030803410700003a00148040c1e901c000303903200780880c4140161900c0804285611002111002414040c01c10006034032940694000f8001e010185031050030030125950711440d00c01108146401d101c2d00a4040c401c002d010880808524024034215080c0b805110002c1d41d40d014080000303040c45012a10280c80c6d1400003540e694900e4204110b95005039518541c10342e0764044e000341c000600a840100d40210300015401400c044060072158100030302c0301d000c15107000b04802c21a980e004245002511102c4040c5110203140980c0006a68408070700d0103500f2400c1032100d81003402c17030510404c510f955554000c902120780595021403004d140702411202086900041c450381c40c500424070402032400c1d400f90042d81e002c4020043d4240084c81e03401800341e46020020185c0507191040c1c1034951003003811981080400f5003c605080e229545e460940728100d03003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 83921700 1250 83920450 83920471
    0x213030c0f0e0702030a021f0e0102030a06090e03040b04090207020a05060c060601020c18040f060e0a03021f0501030c0b090607150e071e03030806030307061805010f0b0a0603180b 79
    0xd0500c918100c10102c1504030748a8002503140c1000840069142c0500581003240007071110421503c0000a410036a060480c0800841d80e81c6403c00b50031000b800c5038001c41407514a402658011001e00104507025035440c1003000741001e2900c41500082e600560040360480b9201c000014940c851801030710326001080043c0946150110009203840601003000380714a29049401d81030005c00040705800c6504194903c100700c006040040251403030299807d030a101c1d82034030300c041c03550115280c8103030b40700001847c01c1220350803100c0040c0e40703082c0405410300760038080c00c010040d0b01c10018842e8400181107a810300d1026140c0c24645c28800980e90481d546402901407a01003e000400c0075001958681496040b00741032401d00c031000f400001d09019590000c41c07003c1d5020815900c4107039200c03c0501c8180c081e01d40a6034018141c2c9012500e40d802c11071502d4214503180154841660301500e00da01c0c0e540303003280450117018500c4840d0108a400e000100100c1c4403550050711640c0c250b81d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 83922950 1250 83921700 83921729
    0x1b020601180501030309060302030406200405010908010605060a051b060a09060e06090309010e03160f030c0f141314180706080c09090c0d02030405010b01030f020903060a0213030c 79
    0x500000710300c1d5800034401c255203000014000030340c10150301000d40b400c03440d0058580d80c0300d281880060040700c060070b0480c150001002c3e2a410204020300554030281e8400b0140d69031503003c28240c1d40c0b240074880e80450240090981c251259000c0c0c20103504800010b9002c1c90380111042c100502a500c4284886d2030b84142018070100f80940040d00708070b00010b000503d0038220403070b240d00410010a0400c600400810800ea600300b003006092401031140144480c1d0f03400002881c103400348022904840e69110018584a1410941d0101c951032100c1da82d030000d8100c104501b1401c040111111560741d80e01c444240300034500445d2140c03560241003500c044840c064a80340543c0d0341c0c000e804000c00b010402080c1c03030640c000d60306101c0c800c0c5c43c0d4a0554030751015880e418082c011a04294504c08000c20013030140c15084a400d460007a202009540160709031316040e0710138800100d0305076105034041194481141d004120700c1c041412100803d030b442c1d69030150801c1550784010030004412 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 83924200 1250 83922950 83922959
    0x7030314130609141801030201050d020d1b020607091401050a1b051501080c0f060c030702130504020a0506070206070b0601030e01060602010203160c021c110a080d0f02010204060905131b020601 85
    0x40302c810440104c1180d2440220f1109140440b900c0814000241008008505a81e0000c0c0c513030103403000c101010b0703030038010042280b50340f030005508110701030300520908005c83c0c0c0c981d000e40314450032354a03c5503001084014030001035606034084811901000038080000038041048406001003920803000340c401c100100d1380700d40f4000010381003041c0c26045034090103c076070340740101e400200400340c0300d4984034041d05d002941140581000a03400602510094203101e003190700580c4214421107410f1203032601c9205010507400343c3d94000b90003940420141c40401d50040700103500c090b0524010424420810b03015081d11016400080940e40200a02c001c450500d9106d0500340e890b442e166905085640010310079403201c030500702c1e40780a03069050f02801103142258480c5040075000d201c0c0765580b080881e42d074410240c01000001c6d02150b1456459106000310b074211090303660f40600d8642404200401104801d160204599a900d001c50064900608000c00c0c4010b98010341103940c0342 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 83925450 1250 83924200 83924219
    0xd0c021c030c0909150308030f01030c0e15010309050f121b0f1905010b041104090b010804050c040c0e03060c1c11030408090d0221010e0106030507030314130609 71
    0x24940c11005050401642400380d65002c4103010440b440360101080901884400600c160001d0300f0242c5018000403c00c84c4842c0c2d200c2d501340c1200d2013101c84031300003503036a60f80551040d000c0da42130107118508e0507a070400750700c280c218802840c0990103403081003881c05051864134190b403007199049000802c81d8544c0c6810f801e818408050603101420402c407805100c01e45655003034145800c2c1229552800c0140030003503000703a010003c00781003049069001501c20119403c030340702e8130440318107101444005501c16000d00317002d242d218000b0030b580100c800400001e802e004c0e10714000c1154a12030303404169003c002950103405030344151030344c1d0002d0501c0f14240c0c3c0c007072010269046017050780f8080c03c00407401c1100da22079006074156403180700e820009280740c440c1b40303001b0f940514041041c19405035602458481c11940c04004c01c46511b19010450a031030a030320016080b504854800c00c0401c6c05001c1c00c1c00c454100341146403510700c3d189020843d504c0b21f03800c428001440b1301c9080c0140341a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 83926700 1250 83925450 83925493
    0x2f030106051207030215040905010602011b031a060f28180b03071206030206070506010504061707091a0603072106140f060f070302010227090c0f0d0c02 67
    0x6540400c100b04920111680d221007a1000074064641800c42d40710b08000d030003c0d90042c00b4440002d0005507901c0340024003a00c0c10201c031101062150800903940c50007481040e00541c101d28841ea5030781c0e1124100300c1e1a4100c1d1546620752082004500500020b01498019114849980030b41a5684000c02086803c0c5100c1e4124090041581071051900320001e49502c002146866070641c07103082001806850741d0f0b031000303400c0040801c4503001c01ca408241281611410b44003044650b5655140c554801c500c0e031100405500a0003083c040710005810154201544c0801125142000b2020520944c012580303000000c1070208054611404001c00c085040c00c413407400e004403420304000902c1e041c414a003080c49506565089245622010291903415811096441d155082401d0180c082d40c01825400c10350390031403080d083c0741c4000c80348014402c032000d41100c525503a603022207000c503404020307150601001401460340401c00f5006a461031031150f800383c18281242080880400b2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 83927950 1250 83926700 83926709
    0x3030a09081903020a1202150c03070206060102030a0e04050a0b150c010b150d0b0d05101509180f0c08010c0c150e2107080301080c010908010506031203042f030106 72
    0xd00002d105000c02c0c3c0c005040700e5090340201000d0004139a0703c2c2c040c0c0c03801d10500d94103035095070b42c3d40030071048204000c090352203101250259801551640e004a80307a201741c0c6281c02c046004440304182d00c0c245540300f50b0344010029170010344204404001018850320f0442c82c85100c0001072924010740e03082c001c01024500a8a8a00c004281800086031500070b0700c01c848402c66480300f1000c4195204e04a80c02c500e5000020745865051000c0306002501451500050701a40e5503030000e07000090b841881001403a416902841c128240d484070f08030a000d0b50203449290081c070010452101c2807146040022040c2c4905089031507510b400381401c000c4600c240d0555180c000301d0180d411002c6407840300a07914000a2440d503a400c01e60701646c1c043d40001a140420100c00440c40960020f40c2c0c2408600903226024215074441440d801d0b10012501e4a030190008441e030203100c01800061500070f4419043c42c0507403c2c0c280c18180200007241190b0040c120a0000341e501401d01b80710741740282 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 83929200 1250 83927950 83927983
    0x50c071e08090402070302190302030a02010c09050904060506060c030d050a0606031407050c100504060509060c04060504060e060c060406060509060a06020714180106020d081501080402041a03030a0908 88
    0x21180c031103240c503001d01d182d107500031600040c403c0b04052003807001004101c181d02c3c4601115041e82002545ca8014850f400055864030783c00002d26405900d401d8102c980050542446694694980c0c02400d00508074540210082c802c80071180c8061018100e01010b0083c00185482c04620800a89009a02003424145041000c1483c2407241c5ca03181e17400b52090410959450700e02503201d1810801400384501e0906d040c1c18002040038a0300700500801c00c540841d0525280d0644141083c0700d0ba00c030300c2c1c000c100c0c2000104107442c0105088080b811004141605014940c1c0140d4107000048604071810341c0d854005208624122490340d4001c082940c044100c81e0030900040c1d607412140c01018041a000e1103108075550310104403040f8040d400100e5552542c5da0389010b582c1e83d07250003035030340440c2c00c0c0c1d0f001814401e9510300341200040d05a50700c0640c0d403110340900004044000001c10302d92117001802d446514200000c0015003240da484080316446c0103c40c5d401c0034804140070020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 83930450 1250 83929200 83929253
    0x40902030a020a08030a200d0e01020727060504020c07030b070e040203010b030a0e030a050d020f07050a03110624401401030201021e03040906090219020d09060c0c050301050c07 78
    0x1740c5200196230041030040381071441e1036030202c000603441c0c441540d20807103084503401d0341010b2500c206c0848080881444205002c0151540100000d84c002c6010610840e4170280080003c01e442100032a0402081d0070a0346004081e85d0224041e40c1c0260881c1525000010078400e82d1f400e87d1046001781c140400185040154104000305140700b140191b22480760007085003210313481540100ea0000f50b1050850b031200c04a860041c01d040c2c004040d91800c0d001d01f80008915030329286191140d5405046081d040c411510101f04c2010006480d004041401554a0000c903030015240e912068004002c0400303c1d06160803841a580f800240801071150030004000507600051003d01004008010030241204401c410380b9501480d4009003049007803150000e12403105074018036410a81030750b4143c0548410704181d90b28406000d000c80050041c0c402085201c2c030075019145040d121340381c1c1401065a0784002400c0d204150b64409109000150010400c20040507055508015060f0300d2003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 83931700 1250 83930450 83930507
    0xa090b04200a0b0d02090406090606030c020d03150303030c0509090106030b13090b07080417070602041a0c0604140a0506040506060a0602060106080105040c090521060a0902060702040902030a020a08030a 89
    0x915010741132803250000e401150100607030f6525000200500181c18041081c1550b98400901901e403c100e03c83c05030060301408140c20b07100e40140384420080040c100541403071654110018100300c1042d0302003041c00c4c0301d003d80d140c6d64040101d0003401720307980118410000b081000020309000926021141c0f80c04180c00020303400701c0103154004c0060a0038003541d03540c2c0c03c0000d134646a242c810401203030006141070421800c0e0303000c1c209035140340107003ca061058041c40344162007458944156944407030001000202c0c044101e245006800041e5006101155200d500d0304106540c1101d0030b8211b02c3c10405142000000d0100802c2d0b1440100a83d52606c0c9014100300b506000e0307a402107407910b2281840b180558021001410003a16040b80b00302207085004801c0b0310282c0c1828980126404120881e500d40a00d0070311a8008215502c0d1030a50740c20400101aa10070880e094045c055016002d81d945502d162700a102c0c1030701460761494610300c0109902c00602d82c10010445200f0301c1034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 83932950 1250 83931700 83931719
    0x51906080c09161e080916051c06110a12050a05010f0e04050a120309020a1703040504020c0c040216050118030c02240f07140303010614030a090b04200a 67
    0x260082c0d160518524802c0208a04440c440000d144d51038415030703030140e40600e45501c41c02443c4141c03280c00a40741420450080c80d44140828801c0550110140b010708005134969841440514401e00d0001914542807500c2070154001c4e01d031510202e400318025403080b8419000f156400700028004200c15810701069004211050190f0800d6140000010341002801c100040c1c0b038030b802080b00f5040b01001200103001d8010864100d0003840d086c040011416140d0503004103001705040a18145420502800001e41084440d0300f414441d10800000f1070f00ca40c4000c0804154014410183c0b81d55410203d0079500140b9085503c101070604140c08030342d012003c403041980c100c1d44ca200108851000d80201c903841c3c5102e000054001604002561444005010740307481403540703141c000c111035000c0352240003d100d50000310346071180c89104a00318074001c1d54003001c0784000041444ca192140711040c0e80c1204d0440b40040c550214a14489a907050400d20314030464004009609082041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 83934200 1250 83932950 83932969
    0x8031209030f040f0819080906090307030606120b0c1206090703020c060f01060201060b0c060a0905160308090f03030901020c0f010c08030903030103030f050708040522051906080c 79
    0x42100a418001052919400703100b241c190891000c2070b10f45590b00c5004010300c00301a880340e001d0f513101d107880d100d0082c2003408a4007592078104240600740b1204000340038542d80812125035040c02440b0780400010881d01c80d0701c0250131440c1000404040c00e16012101a2000d4034590861500340325044c008010382403e554419000d56400d9251745407110103401074094003c90110500801d810854a42c1210740b205040b01c0d040c0e4002c2c0b040954604803c8454401c200e1030203400d811503000980c03860700ea604406520f5108500f107409540800c87c904140c0700c403d4208071401440054009030900d00420f600403580400c40c082d6140900c0840042c2d80c440003030081c0b5004103000c6140d40000e0b80180320390804607030000f601740c0d540e180200c130032030722588240400c6005c502c000a4041c0014800c4064503c41503000003002e16003420320007004298582d810a841044e0312420803000d4582c03150064a0184550012021080f0f141c82044030545080d0b80002a0544c800300320b102840e036552002 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 83935450 1250 83934200 83934217
    0x1051c0201050711061803191109060312040b0403170307020a0609051018060e0a0210030e010b1f02071a090613090e0601150903030c0809040617010204030b01050a0803 74
    0x2992000513140c00c0c020500c03140c80321680036002045800306911882603149940b441142a900401043e001005035040c14140c003401d00c4208041419a500b0320b5a9001e0300080002c0c00c6a44a000300c4d1003071040c690040c0c01c840500d903004901001003003441d240700c2500341c2c8007010b12819441c140d20b00035541c0d10039510103003505455801550500206000c88102980701d4001881240c00c1c49100c5a4040301c0c481c0201c034010b14103420044150400325200e04c42682c0149400c0c025040d494007200601070310a0601a507540e18215050b040d540c14002e0b403246445510744001c0305030303240c102905081255024a81880e0440c14421030a80d0b42402c8629001049440544031442c40c4034011002295410941c0c41d10300d050b50340e544405001801504881484004500456810604407040e43d803512006011400c0c0d40f4122001030025001b07809101030281c4002800c940c0d07030300300c1c90211566094401c580d940c00201071080c080304a0003a0b0240c1415541204010b140031071482c2d5900ca501007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 83936700 1250 83935450 83935457
    0x51507020619020d09080406031505060304050d0c0305090301090309031505060901060c030909051f090b060d050a0b0a2709050d0503060105160c05010801061d012001050a0b0901051c0201 82
    0x84e560284042d66019820150300a4030254550b5107171080070303005108070726501e840805244400641490160304580c0b0441c1d010004d0400207244403c1594030107400e6100b101442014041c0c3d034001d86091007403042c4a8060395400c01c00700d28504140ba03c445d008000044c0103802d010400c000d0b40c13150341d59036045030041d2502890005150038102c90601c481d420400c8800d05002c103000c016070005e0150344402c00d219010511007036035100700804561040c0c40c1142c0088081c0190060210541d1085a01c0082440045101802440020490741098121001d03005165001202c09050300b98001108100c0510400026801d41c55144d503950035514110300f04103001001640d1070f44501c054400c80c2042a4041d0390300581740c60a449560007a01a69000641d524000601a44105480c1c4810608903060a00070710004004680f04070742c00c54100b03404d40300030241c10007a06091107490710032140002c00150182c1c0c50020416140010380c0a030b44a81d0040c1c1e9850086e6483e420040500c42d42400c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 83937950 1250 83936700 83936707
    0x20d09050910080304090e0c10090b0d0207050f1507020703030509060a0e0303070303020711040605090a0c030608151b0c03040611070f08101514041107020402040305150702061902 79
    0x244000b40e81e40070390000c40ca40d00001c140000e00121640180510300400b40c00d035101c0c00418414491000380005e5104009a4040d03000c019043c0c507003000f002c4241800d01c003d89000c545071174491802c0c103040c0d01c406d0a0707805404119002413821210541048152010b800e069140d80c6000308075000d10301031a4400c8200164680e180c5010317010152044401800b580d85070000341c24003400940041c403042d58903d1b0a0707d01c6054034030b498495081540c00c01084450151212034034107005084070300082c0b00f07141d507858001c01c0c9030508209a88241c000381400002620306072281c00091444100321100400c01408000340750503012043e14156101e40c03520b64050f99403070007400d20741101503118100100d070b4058007091074480802c14070403010003c0004c3c0508640502c22410408003441414128200403414200a02c1e00717070008424144d10700040e9090420710380018040340d00581c8207e42581c0176109840440011801071340e40003055001a00045c0f03010030a08446007095000000e41700d5000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 83939200 1250 83937950 83937961
    0x3050604060503010903020d02070806071e020a1704030c0e01120210030b0d062c03090d030203070c0b0702100c0203030322060f06061209050706050a0507050a0b010312020d090509 79
    0x5034000c00003850b00800a102070f060341d00b0082e403280d0b44802008014000c542e0b000c00d81110010705a0300441103551440c000c1c10b60080540521249400c1100850281030342034004160100803007030a4040e5803039829915891860000a0f00c030f215880514403032500360040015204408060240c03a4040c0d5003140d460980a808800810b0f400da01690301c50b040d036405d4020f01c8035030340c0b004458560540843e0100c109460049a500d01e400d4444101e50780200010700c803d040c001d0902c150644a401183e040c10f000c3da845001c40c16a50f08010100e00700450240250714103c100d105800b070007800c1041603120f41d900400d89034400140908100200603e61000c400f20303042000701416080041044641008010398000d48441d11070300300000c201e0340d85031440300078031b120b03240009a2040040c0400307446d01c4025201034120380305601c00e01c00103001c00000310340705101002d40580310380c03200d2001d58114644140c0101325020510210350210170790111040d00028240280d0358100c0ba00380041d40c90307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 83940450 1250 83939200 83939209
    0x9030a080c0102030708060f030705060d200c06130b01120309090507020c010305090c0a150c05030f0909150337050606130219050906090d11011205010b0406030506 72
    0x42040042009000040c03603031541030190301035800351038507030b0b2103410796200e0108010310304021001056058204020400c10340c5803d00040440080341480403c1c4586500c81d08004071000d03602e0146610000140924844024018640d008005a0000c9005d040341d032583e090301c14050150340300030740050b6071403014980a4078501006041e4060705210528000c840207488014aa403060f02003410000030440c00c0e0710200f00700710185005004905001d1412501c5614402a4401103050200007070106012403420701c0142110581c0031081c0d582d41700c0407002e0040c0c20303000034070904d0824541c3c640c5103203035a0040f4424000c08800010401004108080c030040b4148050200040e84020702d0890300f000750100d0460302c80d940c101c1c0c071410100d81d14070042041e0f10600d00c00d402c80d000300c0c03000b24840c98021800b0b04078600000d03118504119440000c0b4084540c4018240d680d680000004001c540c2d10a40700c0110502a070703030910655142807100325640c021402000c0c02d142d222400101c2070340343c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 83941700 1250 83940450 83940463
    0x60c09080d1404030611120f0105180604060b03101a090105040501030f110c07060914030303012108070311160503060c1b03070c17030a080105010f03020d1a0f0103110703050903 78
    0x42005d400c100721040c004411032a6031010304012840061140001c5003089100c89460403a40c0142207401c401e90a0035601030121401461558465901c0d500422016102405140708404500c141d282d600d0a00d90342c81040d2401c0c8034071600717011040bc9591100e07644101a501154003e080120350303c07102c8020800542165914041000400300d911100700303000148140031180c8030b44503030145541341c0c1042c1602410b814800f0340c00d58010030041150021022052111031101d04203450280304a039540010f0b68440c800540011348078a58282038100c0034001030286c60300c41861024002e00d0400070a407101402440c40150354400f0507540154117043d1400120241d1400699583c1c5069190029103e03c0038007400c0c00300c141100071038081c00d50010441d010607080c1d4444044680c64400110f07440ca060010400c1056001d2011000c080010300540103108000100c042034964403d050110719400f02200504060070074105045a0091500300d60b0a55018640360b41c0d03900c0e0346d0340428074040303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 83942950 1250 83941700 83941703
    0x120c0903060a0204060e0405040206040323060405030304030305010501020604020a06030507020a1b03050105010f0e150402071a07020d03020711100203091002010506040f0c0e0f0f0406080604060c09080d140403 92
    0x310002c0000042899000703100341d07800368840d42ca8840c040740c14401200d0040b10002e402c00c01c00c20090001c40c003074418032a051a200e00303048e962540b0004081d401c01105450880d0184d0010040c042015007602415014240a100800252425800181c81e140d160f21401040c50350720808603811510a1050502c01e5410480e07801103d2805094003c940c1c209100070744140d403901001190411036070200c60201d0f50340d4924100f142d12008180e03070301c150010075080d50040d800c01c1080001031940340c02d680c1d000284406040145003011000c2e0604017000400d41c10984104500c0c00018030415040030703183d0094590b03800c00c04500c0d03001d91551041513910703544111010400c42240d07074150000d601c20341d0181d03010302c6010b4105140030165103c4003040804200d03007070080c1d07000d42050b001c980c40201c030040c5207180b500500c00100702110090340241200750000810842882805d0151ba00b10f03407501d1401d20300790b41c940030305241c8031550205107000b00200d4000c5409408070b603005440286 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 83944200 1250 83942950 83942953
    0x50625030207050a0e09060105030105091506010302070c0b07020109080105070f2106080607020c040603030f0804030e120c01030b0a05091305070305030d06031412030c070503042402060f0606120c0903 88
    0x15620781180580d404421a10046c01d0300c901c4001103030a00f818001c0700d0103a09030000401c81d1084890503000c0c502c00040c02c117410964244001e10203d920b4444281c010f0280244032591241140001403240c00c964020039900c5c2c0c10704003880101d41d888008610818103515141111000e807619001c0c00c070784902d82284c0d9541c1000c82c041090701e07010070824000c1069400f15185a4026014013060350054400a40410210420411098081c2d0f09903580705101e446c141107034042c180d002a40d41181080c54400c1c0d9407140c3d22144640d41c1620603a0341d030940888010a0781803500f400240980e000074984412509a600008100070040042c507014650102c25a0f8554075a83c1d403540061a2a200549410034080307166403224074041007000307001c5c007061410352455072600002600c0ba404500c080307035248010040001d81c17000586e00d0740c01d103411841a01741e43c10350300c1c41c0003842c040000d0208a05220210b09000003a03641c3c02c101c83c606441c040340c1884a58a01060120501a004000342c05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 83945450 1250 83944200 83944219
    0x1502030c04081c090b0c010e0d08010501021905030304080f070803070c0c120c05100e03070e0109110a0905010f030b0d150c020705010c0602130b070b090705062503020705 75
    0xd048020181058903028000c40f0004466120210345283c9002810710214400c0001404201110310080c422080070a001103620780c10400902d03e0408041e1044000800c0c45005006641c0c0c14803c0d0300d40604e0364802d041d48850b103611010740f03070f2101420050554000007040c62500145105031003005421000164483c505118058402d003009203080b941d004e8500404038586004241c40d580c0c0a401100c0d4440c6103042c0800c0c0507510961105041c207020002010840d0340c0d8007007124401410382c40415003101d524204081d0156120703c0029004401c080c8058801913031701c84461b808507a0240307042070300d0703481c0c0c4c07070f4183c00400044d0040341c5c20001c0039065109200342400d410140310840325041111800300e120403a11810140a203e0000754110310580100e0a140c01908294240c180740e03c00e45955216080d0b42070380003c60440d40002d960742003010318a8140203001c000c0000351035a03841c1000e61142c22240000080840da00000034000c07140525100304a03100140ca40a040c1114 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 83946700 1250 83945450 83945461
    0xa030506010f05040504080d050c0d02040611010c0c030507080904020f0403060903020d090f0e1e070809010e0a0809061315110f01060303090303200604080406020f0c010905040207150203 82
    0x31540c200740201540070290301c50028141c1051301c6518881d0703400142035804d020601c0c10785009031202078091000103009021214850180707200410003005103072500b0740c0c80d06e04446194251200355a280090000040120000c60b4105049824a17a484120350f07641e2071040000030005d000308a1190070b004000314001c410011503900c03801c86140030340c003242c0418041d00c40c212484855070280c4144241050f0741013010400c1c50300e00640101e03401c84c14800d010b10000074540303440c4040340c0540002d4010001c0c011000b200303101d10422107101c4009402030a03800d4864400038868010840d0190780005803004180302000440c6014201541d0344928130040700c10001c00c019088400302e00d0901034445140442c46051080d84101d0f9030503201c84100c1495500c1c01d4a000390010700b01c040c0d189901c0503c030540c1c00180841c81c4542e101d28441c40d1542e003040320092510019140e13840b6507900804070382285a800c02c8030306048490450300541d0ba06494039103076100400c180c1d088204940040f00b07106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 83947950 1250 83946700 83946703
    0x50706030c02100b1f03180b061903030512070e0411091503010e01030f0305040e0f01030b070f0e040b030c040906060806070512040b0a0b09100306060f050604230a0305 74
    0x524145036982207a0700c920a10000780111018104c80c0765015200b4000a21501c4c101c51265924a1445c00c0011318900300030342181202e1800ca404031248101c150800c007807490113041c206421a4590000d0b642241544d9002e41244224210044c0d0b000c1705038001503880b4825401c8020381000a0001d0201100e421020b21017600b040343d13018480d40d1070390001520f80036107200b981c0c126411b8050341412a481c0d512090302c9aa8820002d40c1044400c00000c0307100c09501c0caa850082340e824000c1042036143d42013910b904000070f8401801c000c0c0e5011580c401e06c2c0e01000302c40c0d0242040310300041d40101100000d2526152090240e045400c0c80020801e00038907a002200311407424040d10103e6958003811a0a40f19000101c04800041800709001c10400c0071b003580d00c210349200005084081e540092854041160400e4000a0249040c010010075010b07100040c03141e40d282c1e00780c0c14145400200d46000c1e500401c118100c0c03c04000c1c95401e441040000c480901400a800c01516400c016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 83949200 1250 83947950 83947961
    0x815030a031e0c020105090405042303030f0601030209012007090e010b1806090403140906030c090a050a06090905150402030c040602120304030c15060e07020309040e060601170a0905070603 83
    0x50b81d200c40052880b2080d60040c3d0395920303543c3d13050351107e16008034401080020400036000343d4294920b58041075000d25040c0d443c01c1126003050040d916480c00c09850382103c3d200510881c1054014420b40354140d8001011002218980b15107141c5042210641490f2050030751191606134101078015401610662092803100b4003904c81600004681e190031087c481c003078901c5600312120308001780103c5c0c4101454442c00a11070311503840d103203418000610503002a50243c0d4240000200009076103020503130362000702410707200c55000528101001d44051860301ca00704203152a500000c4a04c102c1c803840241ea044003c0c011510390a010b00651881d4102e0f00448000d482015503e5561300700318002d6070305c100c0d03259880302140c5281d076659540f0100004a0f15503c1038036480c0116003040801c40301071090180354021502c98406030208030581e1040d403202031160300007400380407c0742d030300030000da101256080011180f82c8900300b058009201480c406091801b9516010a9855158100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 83950450 1250 83949200 83949227
    0x3090203100e06012c070c0206070308010504050a090503190302070506010f080610080705120f010501090e120403051e1f090303050f1003120302040f030b0105010f080f070815030a03 80
    0x103c40301a13803a8042c1e44c012114449845c1903020700040380c4c41c1203a04182e0101d03404822450b11001111043c1e021401d9500006000c41c0890801d000622860405114456109104803070501a04200380c0300c2a03100d228044807140d0f11000801c440203000d0103034045580543e0721004407026503a540001109107803c5000305411801614040780816454194000940340c112001e003200760b07d45004c00411035601080742c2c200b03000381829030886080071300c41c00f8001c1c440203901042c20114503825034200703c2480000a25140d0030702090020a80000c0e40382a041f00d080820605640c00c80d41e514074051060b00e11000100c181050180c2c240d08a0f004115107034400c0c0c03814042c07502c41c810710340388100e8115281c007a280501181080800c591500584014026060052410752544020030040390150401c1e41c02e100c820b0010492942d21030030442c04070116140810180c1011820072000180c068080801c00501201080e5241c0e40003000020001c2d0040854103240c615181c040d01c0490038065 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 83951700 1250 83950450 83950453
    0x90c020607091d06040e010515130204030b0615040e13050d0c080702240706020910020102070b04120e060a1709120a1103160b04060f02090a0902090103090203100e 72
    0x1c00c050034001c0991009881000000600460021400c003240c0b00c0010180e40e4425201d400c1110348102c00c1c41440c1c0200341001018200049407010b22070801c410f0b461070551700e881000100081a180403c05410840407140c000a0700d801d41d01d000740038080d80d04000800380c600c0080c40041448840d00c505101d01c501c060341e462982d502c400703540300c12044c900582a81c10400491005162400340f2004070442e000c8131502c68451410401003e030040d45088400715800201032030a8a0000c01101c01041e091009600d00780c850795403c0300c8440082c1c801000407880c103a038201207078018402d0754800c1d0405020203489440001c8003c041c5842d151381e10740004c42c50b03408142c0c01d540c045102144980d103030407428a48110003800312407503901000c0b50b0203103002c14080905011007042d011140c0c41d02030101c09105041c1400c0c6401200c0480c80c41c0450184100b165141c0c41c0c507104603c0e000c903050380c840107888004460050b40a01410f440007907141c0070700d0601d20b1401c400c0790b000030001007c0c4c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 83952950 1250 83951700 83951713
    0x1030b280603110f0d09020307080d0509090919020111031c0501330f0c08190215060307060311130306050a06120206090d0305071b170a021e0103060807090c02 70
    0x19085440c5210f01c0c46141c840900810409464617016004110340e54805030031121401d03902c1a546050112401201000400c0020340f03100614202d0542e50700315404102600c0d41e85604c0c92160f640040300c090003411f018a070401c40d910740f00d0500075200c0000303040c048401d65105806210004040074001c0328440e00ca051118103480008200c074015a00340c40312202c41d0f4980040d0140c03616492044c400d010070191000080000702008054440700b5100095000d040351040c00190618010041c9003412100c0e550800009a03030010304541151b065040000745c00156007040146d034410030f840024481c01c495000410040c01e64800d903c110f011001c10094542c8902c55100c40600581002c0d51140301071100108920309607510880844c4603040c031508c2c04415030303514640315001280c0f0415501042804014040c0240b8071400c203954680042c1908640c6940000d1100c401800b815414003d038101442060340680e100c0006414020201e03580507a840000f40701030003080145074014000d14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 83954200 1250 83952950 83952971
    0x4061202031b09120109050c0a0812220b0c07030b070309030804020906010504050916031107150b0a05040608030c010b010503010f06050901030b040e060702120a090501030b280603 79
    0xd100362402800ba00c209480d90768600319006295801c0b61041070340c05140743e030720000a00320901c1012541ca2103000074001c0c2c440c03070004000c0400050750043c0d4182d040200c0225031121044202d80f1b0804507035055001010110710401103d500c91f4209611801000803a421038080c00240041104d06c0307580c0905c019a1130001c210165030340034800034042075010002c1001860b0148030280d1050042c9401802c00303540f000010100101a52820303410038040291080c41c603414020803620300d1120114614102080d55020301450403886001003050742ca03a0740d106240e48049100c40101002032003400869240d0900c1600c0c0d0380b1503a00c04501c1e40c038282643c0e0595009005907070486072840300c20251a81b40220a40b465070010000360304141d5a0b40b00e0400075a503c1c0700f01000e8807501c1d002820140b40c44000a8540b40c0500007810104c0b10038001e9800750342d400140e42d01598800e00e00450000d0700d00c40403503a14054031002188a012503401164044070742c1d8004000c950030f9950500415225 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 83955450 1250 83954200 83954237
    0x40509010209060414030a02370b03060402160c0801020a0201140424020702060301030b010501032d090c0302030a050d121a0409020d050f100f06050f09060a0315020406 74
    0x1d1501d510f40140342031000704040c0c100142d40428035140502030b60309110f0542d00050007010001c0b8147c80f21450000384140055281c2c521103003032106802c0c0d44071b41c2d50503c0440851804010030144c071a03500080c8101d01c010340c1e1103a50b883c403580301480c0e00175540c6442c180d034040d400045100b00150304c0c00304840450112b01d04484d0089400255904610052600b0326000d2a08607010410b11074003008000c0040c2c6642c8001c500139030203a21100680d5040100040c06e03a0099040b00c1048030004002c043c910350310100c143c440300801c990003c1c2c840201e107800882c040c2c05a001951500500d100c0307605100c0302162403041000d4558400c11301007140c2408908070b40311120408a14846000804030300c2c2055031141c0c4510340000c0950f00903001541e80d052911000e414415410341000c002552525040d0140b14990030f0110400c0c4401070801d0007140020780308a00ca58810a083c101040e103903281c0c420311201558020344c03012501c1403000042000707940544903801c0060310b003034821034000c0351 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 83956700 1250 83955450 83955457
    0xc07060e030c0315040b280c17040b0a1805010f02040306050c040806012709110108071103070206160f050c01120c02030d0c0302210f0610080a0203070c020901060206060405090102 79
    0x612140d0003541c0c5030b40e1107210089030700a07c1c48580b02512544074005103910061341108062101c00401d540d040c511004028103c048070422540301c3c00d4061000140d05544215030003285200001212122460030300440008400060f165520b4001407105110341900103100340c07806400c0501c0151101300341080248280d1080599580001d0014407880b100a000700c4021841d0074a136000c01c1d904010030710103d804020044510b03030040305032001207580000c0b55030344c03260385070401544c00d01d911076940f6243e1184150003403003041c002818504c40280d00c60320040490b00007440904443c400d1400030fa403007a001003800d020452401c807000030002103005603880c00e00e0940c099400d280d1710900e001d016280002800c0203058090160b2400c076014907c4156005244514544450070b002c3c040503d03104000e0701d400d000302c581c1005546002c5d0810342140d00b00c0a01180103030380f595060800c0701d981c4140d10f0300a510040d080000910f20340c0c00602c05000e5401118200550345a00750058201d21 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 83957950 1250 83956700 83956723
    0x105030d180b0a020123060a0303030203040204021e0406030b100c0609050a020907090612020c030301030b0406090b040804030506060f150714120301060906050301030209040204020f0c07060e030c03 87
    0x60116010908092041a03996003400100780078103a01900c415921a5580040340ca01c1c0060303540e00c000380d10705681d020003001d9a0321a14030302019420000041107902480d800064141a00000824215240c03a8110751481c0d400110710086400004c0c2c03043c955501c2417045000082c00e0110b00b1000e440c2240301c032000046142c5074003403180c00399079540c0702909041d0429120fa004111503480907889902c01c40b4401c4e0b10994135902c0340da04250024140c0b000d4080010041881400f94841800740042101c7c1501c0c0c01c010b9440e0141d640e890504094005094014119102e10091000300041d5401a0060b01c0c82042071b5255542e681c01070180042040a00f980d010390074000080c00d00030140c2c02007040e10f000301f884040d04030000c0324042c82d102d5100c2601d42e01e140700000411085901c03840b01000b420f06860104d10359491900000e850080150001c0d214550000c1d0441c00450f00700110389103489064280ea150a66a4001800135014211058001d004003035141e001450089104201407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 83959200 1250 83957950 83957953
    0x40317121305010e010c0203091207050307030b19020708030402040c210c0c0209090a02030c01020303010f09020a050d0e100b0d02030604063801031b020303150105040510091a03010503 81
    0x5036210800c610021140c0c0c04140c501c0e540e1413407418090b80084c010000403032903a80085517108c01880a100d604880d001c600c0d4207d4220141c24407035541c02054140482e504048078030300315110444005409040e4070018200c4500c00a50001048a0305021754410303402103030108140124940300b030324000c0042511440f400a01020b2007115a400d0388485008805860700d44036106040d400b01d205070005550303510080e400100742908600d410410440382c08401c4c4041d50455241201403003800d1414011001c803a6004107440c11200d1003a4280c0380d0540f1294010b100086244480c0743e112031100c02101503280c01c0c603c2c102c40c03505010a00111103640a0000c18240d507a60f202d080007010b106101084038544440c013902c0240c2c0c1d110000b00d80c2140b0003e40301100c402040050112082042070308001510703409080d06064010050340c8e4009102d440e160380d60050080121018403854024503889139055400418540d03000c1030b0142512250301c0118050b40c0c03110b040d060a800309201e0a0b515 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 83960450 1250 83959200 83959237
    0xc0305010e090a060c02241b071203090510090b0601090510020d1805030106030b1609030b0103020904020301060308040b072a0b0f0c0d030c0e040b010905041d0a08040317 75
    0x90319030f070051560040c0c601c140e03501205075103455100c04840c2c101501031102640284038081d4200d80c0007081201c04002c806191400700d0380c480c401d00d0511880e1032b040c156211303410b030f043c4101031020001000c0c2042c000c000b13590303251411000c14401550098005079a80f040803e950905541044c103070701e40c540050083ca5400e100c215800040c840da5a01500c0401c000020191824013031040507500c41c0c501030a443c5044540740000f1445049002c040003036151040021030540b10049040d030750141c070180d0940d41c0d1400440e01401041e40003c004650000f4005050103400d006414224420740c2040794141c04540c9484003001c184960514010560100b0030021041c1e10081038899031000107941854031210390030382000c1d07142c200d49001c0398807105c0013a0b020790b002c3c100e21740b582800c07102080f550107442c00007002302a403401000e00440ea01d21600d25480301d03040340041b018a4440840d207080c413039490240440d03086403004803500708440003000002011001030f200601d5580d803110b41c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 83961700 1250 83960450 83960453
    0x51c17041502090102031b011b0c02061e0c0d0806120f0d050306030703080a0507030905040216080a03150311040e03180f04090602070308060a0504020403050a0b0702010615030c0305010e090a 84
    0x3d600010345a41540f004003e5402c81ea44102810800280c80d1400041e881a1848140010782c900c083e800c01008050803032840180c0d181002d5901c0711501304c03a1107529005144401d2004d200b00c8100b81070500c2040b20803458590300c40e41d01841010243c2d200c3c9900100e8040c1c081c0d5407403100b001789406170400404080304500c95409158418070090886030901e039251100c0640f90700c44075120001940010300c0001345500006c15000a02054404500c0c100300075802005240f01c008006001c08000a00300b010359103c0d07041007030609990f100402c031081c0e991a103202081c2c3ea0340d06042c010f0b410300b4010000d10901000362648110140b500502181100c820444100760f251640ea07802507480b80490085002440036029140c40381e1030300006401c02c0320810a8160307a0741d0009214074010001880000c07800718084498503070010341d10039944c660320001e0303001d000c80350441c10700848110b0f061084168590080c1440098a44040201c0d90321062807005540040341c00900c40d0f80400306850 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 83962950 1250 83961700 83961743
    0xe040b0108010512120301060201141008030d05040c05031005061207080703080a0909050a09140708030702040504020a030602070302030d0608010515010804050f030f0903010f06120b090703051c1704 87
    0x410309071503101505c50400d008039845205e07400a030403800052703544003894610580a4038510742c020b0f18103061310b22090b01c2d0050050782d83c031512200c40245901d40011404000c50312143d100908001020740346001c0c1b4001c0300350010101203038201d21451480f074241c0505040804c0c441c0640b060a405414050301759110100c03203a2144900508010311a5070005001c074040c0f055030302642507003402003082059810848401d0400e101491001d8100000400142e6400021288410b0307050b50080340d26560707400010b000c804194000b070306240c0005840002c05501000811012010340010820743d42c40d13880b51400c865088650311407041c1b49000c0d0200540c0500c02c0b595003c0e104400711900305503130545243c11a0080d03110030315407540119041078285800e00800d514080000403c002080c900b101c007407815402a14050600d88012000c0303603070060140840e50103150000120303034592011491174440089500c0f1003400180d80e03030b0b4186040c0390600e0242d50040340c1080b00b24124004901002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 83964200 1250 83962950 83962969
    0x3020606060c030403080a2c180709091a060d020a08130809040f0b031b100215060f06070c0617070c030f081e09030c0f031c05130818010e040b01080105 67
    0x4424006410230403800c04620441031030781c14450f8a03942d0500b81005d42031164a040200f40346e099820114200070713005a0014228080303d9000c4000314900c0ac403240381810720720012080c1e279000640091007900340a6140c00400f040402540c03084011f0380d400d401c00401c4101130314002c1c002c940800684100c0d00e4075401200308081c6041e0002030300d0981c0000071307150270006145542d0303204c602c4079038084034500b10903030a841900b60b001a0200f10012002000988001440284182e420324188131b03031a01c0d042c0c10b80740e40c4c550040101000c542c03203090240c02030080002c25440d0003178150000340381c18464514000119415201d044042c0c030340210503586014010100300b0303080e004070310090300c625583c45258002d800c600051a5035040c00c410032800c1c6120109804400d91040040c900703200546900000c40c51000d9200244c19291400b04601002c0c4e0481c0240120601183c184175207903a58024401c0c5a0090721703600380c8216504184010384020314080350109020320b00410050030268101c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 83965450 1250 83964200 83964217
    0xe04050601031d0717010b0a21050f03040305010617030d0b0310020a05070203010c0801030b0a051009020417060906071b02030f03030709090b010c0f11010c02040f0903020606060c03040308 83
    0x3c180804500250b00da4001400300c850280e42c0240f104202d50f142c507519410508001c41d0080c03000c0b207a5000413079080421403064446134a0b03450040b000c0c1e00305002103084610352000559201000d02070b0803941d03035049400150340a5107042c80c0064018000c10400d8001e0316070801450809075009283c00061482c15030301505409003083c1130103003207010b00c0100101c1c4401e483e40e03602d440c2c0500606085070003200c8040c0034491161700600c0461014404141c0c480703410080801c19603501049030000310075503031180c21041c0c00840d002c12030040081c0c580030030b10680d9040b51016650001c0381580c03150306403203450200b00e2443c01010802404590b410210f80090121520614100070745440c1d50704c01c40d070510014104074002e01c1100444c0c06141d800d04000d2a04d10074403112a1201c140941444400400328070409040c402c051340100c441022aa4005001300964821401c2c01030192000410450050107120009041d524044041ea032102074200010750400f410356581010b694040c914 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 83966700 1250 83965450 83965457
    0x71806050d060f0f260601030b0a02040905070c2609011412040c0e0901061d04020f03060a0e07050409150b01090308030405010c030c030203040210081008070305030c070f060e04050601 81
    0x1c010403042042e6003c1401440c0200d91500002c0ca448007001c18203170a54050b50611951990207440141d0000d402815240c000c5c1c407024450315210f4820b4020300c80e59008060b014242010840010342040050080b58003d140350212880343c81c5405800c4170701d00440c03201c20f40040c0842c0721207510669054200030010002e040c0360154290f0074448014046504444100c0b81c00410b20120f80340d44403a6401402000007440b516003022040e40d451501452161003c440860010b0195602c603280c0c038400c2d26004c0c003074503002c1c00c0000003100946003003454895a4400e90b18006217500b014407480a80c550000031101c003088401c0382c064054081c0f40f401c2410040c0100002c00817940d0329004601861040000140440d02340c4009400c1e40c50003d56034052620520400016031217064204210802c0c078548401a0394a071000c01c02d0310155a00848281c1c0301c1e6100100801000100801c1d12022140450307400b03542c0c454001c0d100d2100d90040d000014601d014200c03441c00c1035005503400040504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 83967950 1250 83966700 83966711
    0x318020d080f0c25080d1409150c1e0c01020c04090501020c0d020c0a0504051513111209060903070c09020c0c040c0f0e040213030f02040f02031608071806050d 70
    0x81101c0d182444821350070152822120042204541e03450a0030000c005000180c420841c1a500c050840a4084140d140c00d000000d80c10400ea9141d40021400341040e00959480d8114121615030782d030944032140884040e404d01054221400140c14004011b05034000e006105001003800040d1010b40300803170b425074003805071006414042c0324a24401c005540244581c8204400300400140341383d00c060b0280c0d24020a01c4040c030f1549102018411055445a49902101c40904018810070056a02810020604100307c00b0042c2c0c034540181c48074000ca030082c1c0c032100030480d101d1040090043c41c80d01d0700a800c00c80c2c10095006004d105c9411401e0b00c0800d4034600105040d680c070347c4a08400142414000510240c200c50f076040c004005032011810320441500d215a00c40c0300c3d00001d00000600310a500071503072540c014550b1400c09440a544034108114140c40c41c3c00b12565500110381c2031000182c9103849912030340420b9042040b41e07000c2605d002c0080d55a60b1000b808442c000d0b403140f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 83969200 1250 83967950 83967967
    0x61d0d030f0b041d070e0714090a1a090906100507021011030d022101050f0d05031c0504021e06030115021501030503040801060b0f040303030b0109240318020d080f 72
    0x51083c40682d100c06980010440354602d4144d0a08545401090301201b1030802d10194581c4402002281034901d04500e98540403600001c2e80251143d000c1044804402803c00024040700003a010094042d90210019107580003009070940104c0004800500c040c800b180141c68080c00400750311001d828a5140d0101420070181158003001401001580015001844111014009459035148900701081d035041c0000281d01c500c1c0d844205200300700b01c82d40e190a110040c0100c0b041060a41004840c00c140100f0642c090700e01100e0980c41682d506058001041c08e244400c00d90100c010700c414035580c03c01e0824000102c0500d072603011842041d140c01190500c41c083c3d00c1c0030354025002152075900c0e24100c182540d00030340000d94521018002c440c4510503030019103064a40c141004110075106200413510320301a50310606000002c480120040d00d88020140c280c8881c55030144814541000e01c000078070245a80250000321a100440c0400e11401c098654940001e50042c030f00240f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 83970450 1250 83969200 83969209
    0x7140409060e060a05030d0e060333180f04080a0309020d0317060607150203090307020316080d050f1801030e07060201050907080703170d0b06040b0304061d0d030f0b 73
    0xa942000e908201400300340003c518000b5126001000c048000702125a100d01c1c004211810000040340900d80110101e503180d02c3c0d41400c1842c890320142064481d0344100c540310010800752881c280920b0740003078044004820701d822035109264001c910841600c8594580f0640e0340652076440405a81e40e0744000141c0d5500300c0140014004d40e9040344200200e13916540010024000c64403560040146100050041c048901080c040c42c00041c1c89650b01c40402c0d06510a42c070009515028030104001946a185203441c15210700008940c40403030354a60650f2284603203030406c04419410301c9038540300c4001d688031228140c81854041421000c3c0c1e11500d00d030007155001900076035110410440281c0e410000c40000703240c200d0051000e10701d5522010040d08503940000300e210341c009420394081c0741940201c40d54107005071100c0e5a82d80d68400d0a44981c0065404403803080c20611344003a103c100f040050b9100307a031240030780708444060b141a0010044040b800c1081c83c0c40e803418000b90b5a8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 83971700 1250 83970450 83970461
    0xe070e010f0e180c1c0605070e0f0112150321020102090d020402030604151202090903030402090f0c0f041404050604270f020414010303110106060804020904050307050f010b010216080607140409 85
    0x1842e816542c590585d45c03405100340d03030008000000300310081c10541d0680c0d41769200300901407020700740780c2825203814001001510003200e840d1240300e06940000101b0180207111108000100d001c40c0f200d10740198204d0903031080000f641e600481911110000d850300d40e00658001c200200001001001403c0800314909a80c0c0030341661300c4020441d40030350410300c3d00d03d0792042d4250040e40c41c500d01980054084400540b01d03030141121000014052540703c41280c00204210034210345660351060f0070103400745c8501469000d2403c2c0300200341c03182414002d5203000e141400e0341e800d00713125a44208401c8424507005a030420459140310740940c503148a01c140c1c07003110105c091460f41c19820040c0400d00c01e400c0101081c1e240c154100708640c0d00ca005e030750304180e0440b0189002e89503801d09900d14021201301505038041c1c0c00c4810b200c06015408119543c2d800c0c0c003079805d00219010420034126040c42003001607000390000408981c400c40041c0310507440558070070305050b01d940c80b1004851 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 83972950 1250 83971700 83971729
    0x303050405011202030c12071101020f030a0c021f0506040b0409060603120512151809061506070302101104080d09030b0c03060f010f03020d0e070e010f0e180c 70
    0x24400201030150b568040c01d80864a0300b031503c15480c508240d03054105910500e0424815020642c0c0070480891143c4104100840d40c000217544038850504440003c2d401600c0c07411619103450300d1040c04030300101e02c41d08031521034080303030056580600c3d201c0702030040145201d500c26501d034045580c503900c0e44241c01c1c5940c000e0100081c3d090551034000070301e0310344a03480000c0c03000500c60113021001070034030a54031500001c80988403100000100d0380080f6044884130314042d0310410420400c10001b002845003d45844100c0b100001c00c0c18451a44a030880140050700b11a21690750504190845159118100304003481c0503510302c5001d041004d01c2d5000d6000404a01041040c02200c2201d550064041211540396041c0400018000e03200220541d05119102040e0610a4041d031305894002c2d01d008800e000301e0700310409080d210f00070780c018003500d044280c00102c0c0702144452034100703403800d03000d0001047d1103207100440e01e0074030038040c2c000a2140100118903038403000780c0f0704440d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 83974200 1250 83972950 83972957
    0xe100902220617010e1207020301020909130501050610051b0a0804151206140405060a0302040501080a0501050c0304030807050d0912081e090c010c05010e030703020a03180602060127060303 83
    0x741012241c03e64451054070f189440c0e030620740c41c0951403501141411130000240c2c0160398400252002c24060700030052400ea10140c200204000c1c490400580030b4594440d0000304483d580f0315042040200010340f0480c0041c4050080c0300710900703044540c1d0281a0340340112024281940c1d40d20030580c1c81901305444005c101100c01001540252001d4820181d4581c02e00849041c014494140c580f5070441034445c5407034001045c141c1d110440a000a960064000d00907980c45030300550380d0b001c490300c0c00c0302c1a40c40c040014500b074920340705a900840c2c0c1541c950321640c40f00c41c0111052b800040d10101c0140e903e8611030000395188004200c0303d255500c80f65642e03d01400301c4d0725010030301c10020000800400c100043d4440124000d0041c030000d007440100140b440c10228010010f250b035148091000052950030b054002038107022040c420b03a80c444940300e03c0d54520001044a21603400941d20407070042c40001c410001035294a1019521142c051030501e5002080d85d00991003980031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 83975450 1250 83974200 83974211
    0x1030902091602070b030105060304170c0a051b01031e0b0612070c021011100e01140c0711030d090506030705070f0b070828021b07060302030a0f0e10090222 69
    0x1c20f805008240c02450b00c0071601d1b080d0340c136240c00300303030070b07100040c0700800008010b501d241409100d14190354505081c0c0b006c40d410803005161250b0343d582c4c0100ca40f41e66221400840400358842d0146110161002c0640740e8094000708500e00900123100314594070003014000c0c07070343d40c2030107000040c0f05003200d079034102c15407030360f4014040c6c120000b042e00340400881140250b079001c0001094000b00c49551400102045141416801071803655103c48480c0c9042050000f0110785e500a0f0514a000300030091582c0250810941e0301c22341c00065801050142100f084245400405580e101c08941800da151000d25500c3c7c100000700c00d00c088442c200c01c40f00f40b1600c0d5500000c1240d10904060f06800c814480440c12191b21031100c41c5215201d0b00000c0ca50b4020700c1c0c503141008030035090f2080b654180e495400140c082d400844902198618001040d840c0c01c1d00b50040221440600c0d000d004500c514001c040c024218102050303030040c01030304147c1c07a00c099061142d003800c10404030002c3d6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 83976700 1250 83975450 83975491
    0x706020d0b010c0f02090402011b060e0c01030b180c040e0f0711030a02120d11030c032d01050d020d0210020a0302071205060106080406060506031503060601170112020103090209 78
    0x300e074840d03441c0c42d04101c440700341080007400c04e140d07484109030111403051250350380e8401240c05032004000314501c582c001a03c90100500b58020b120719009040a031a071b0200b000e00110120348460b0b01031a032201000066401c1020006145a007090490102d14600b50321050060484181601c2c0505082d129004100301150b01005913596014500f014501d80100c40d24020b50b80d00d80c80c10201c0e001c1d0b4000942075079482030340e0300944030302d04103c41d455264500b00070400d245401c00c480380e16031140e0300e00c5070030680c1c0d51145441c810010692000d2280d070342404240f012240c0083e0040342c01152442a400240e903600341c2680e0341c44c82541c01016078040c18980241050071a40c450f5000c1410100c41000003034010400c6415103807a450b00d2507044d595410204080c160f43c0d0300c408d1304820f000040c825000c041403c0d0143c03514080e01100d07610303180c010044642252020f000c403400c80c00700300144a0003030003d41c96504140145000310720141917400040d41c50606894401d10b00503622907611 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 83977950 1250 83976700 83976727
    0x70602130312030905073605011503110d0f0f091b05060c03040b091801030506040201260601030c030b03120403061803050306010e01110d021018050703020d0512070602 74
    0x2040c02d042803400f8080414143c4d24a66201c0641c014403042155121000b140446000041401c1e0078440e014100040031101c12500204000e010340100410030a00607018540207003c1c1d0700400e80340d0421130b1314051680c0c21071b50050450b012030101c103a444090000f8602d10301e02505c15a80e015030707514034412001c1004006400c10b19485240551018400c4400202020090301e04850585c10f0b0f140da21640c0e24001100c600e04100b9180001d06410008000d1040020784544034900c00c0e03c66080040402d0480e01150301c0c1c040c0d9114082c0504c0000890652080d0054182080c0e2810081114808100001e041c10041d48806ca00e514022404009002c0e0034050a511482c001040321007a40c0c0c103403001485440010a86030602c6070038111030f007a03640704080d0500410f11000659044040402d0025200d54181c0c82c50380d24a4204906a0348504d840030b42d220a0503400001041018a113a080c000b45100414080c1c49a0154808034aa4280e466000b00016407050b00c006170391b00f4001c2d002d81d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 83979200 1250 83977950 83977973
    0x102070b0105190305150c090a0605070320190201021c020105150d02010503070311041d040204060503010e0a0201080a0e0303090a200121110c070f050907050a080c0706021303 77
    0xf00081034504041000c954003050b803542c3c241816036480641d03a50216030615500c82e14100d25041f130b101010004a003030b8408058511b1b18070aa07030390100441041c0c115004540b01440c083c480da00000c000040c2448046080c4480c148103005440410101c214034520500510320342d400507035110360400a440030f140540c604c4940007101d80010b440d415800080060000400040038141e42d40aa4101c1004440035140202228803100300d2000130010048010503094800301c0c011800c0ca030300828030b0b28060103605d96092040c0c004001c84c007416001180e0459014200074801035643c1007020341800c0034030086120300c0251004040700e40312850072502d000c1001e582c1145480401c0034410a50303030701c100f90400c1d00c0d2015420401a0714004081d0005000202c603000c0348840014034017031080703c04600724049490060314006081e5444043c001082411a0000c00244080000d2117680340544001c0da001240b40a800b410620503580d008103e0b440396003070801e4400908000c000700504071464 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 83980450 1250 83979200 83979229
    0xc1d090102040617041104110a120603080d0f060509010602030714060c092707120608010501030f061d0703050102041401030c09060530040302010b01180320030102070b0105 76
    0x710700d001d1415100810307400030012000300142d10301010a090104902800d40b294000403c1001004031034403600b907d942c0030034a01e00102c0e618030601c4003009954810350007180d401070300680c90310401c1283c060003001001b0f4500503241e9115008619600c1c4c0e84c0b5841e01802c0560011030340e6842909201e04202c0c0c442118175016407080e010040034000e90000c0e00c3e00c41d50251400c41015040b01d00412035451405000e69481f80349100300041254064003a111241c2d1000040100c035865000d8107090302e00034040501001084581100028815840500302d040c40c282c0001048a2a4070001e04003002d030381c07094a080e90003040c18400701a0000d85a032040b0700900307003000410b05d0a02c010b001d100c601d205000510002050044010fa070070000c041c0d81d00c40a00d8111500c494074134002c0c104120036542640190303e802c0320818507500071f192400715000b4250071002074a2659a60100842c490b40040300440c072484c0402c11103480074005032203018880c00a034200c540c1004c1c284001340508100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 83981700 1250 83980450 83980453
    0xb0603070c02010e060d0e01050103110613171e0c01031a0f0910051c0510090206030408030606040306090302060412020d0512060f03030a12060e010e06060c0a0c1d09 73
    0x50184180d00990a10708580d42800c28144840102c00001e12038001c03400109410f42c2040d4a0560008040d800b180c107a03407180561000b8588800709000c860b000380c6036001d00198920310305206a59841503c0300c040d2850208032804140403e2841402c124200f00e48001070348010080449903805001310203000c81c64001d8440f0b030505600001d268021a070001c14091085040840c0350603441c2d201a40c003403c0060040e0a0b104068020b6035068031902009854030b0141080c1f2980050f424080c00c06d0454005000358115140ca0725005466400034000642c018010000080003030b0286c0500d000d0a0f02a4024003614030b81414040d00c0141e00500440440d0480030b850182c0a03040000d6440e905481b800c0504950340d042d0100d60380f11218594030364103100c04103240090a134010040300c9070307460504007840200e695401c64481c04c103083c010f820040c071043d800549141000d102400358019030b10f013142c04d149803584540c0e480710310b150455200940d003078510584846110040a41281a090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 83982950 1250 83981700 83981707
    0x2150f04030801050d020409061e0e031206130b1e190803030a0f1104080115290c010f1a031509070e0907080d02100b0102030c100c0c06020301030b0702010b06 70
    0x20740c020100d00b07050044a03c1051403505607401c1d522503500001a4030350141080003646184c1c50385040d01c1c1c07044408603030a1410300700d81d030079105404019144107007210980361002c0e44403c42080215460b04071170b03201c00c0c0d959484081d007c0d507940104030600c04207078011103882c004032014080e4490070241c000040100d420800c1119407000030403203901032880480016426480d035407803000703000e4000081e0440e900114000c203c104065101c100d40d02d8a04030345081559482a400e202803c03a00408801d645a51448000230110700c001440191031420000902003941300b1040b04650f20031501c40007005d1407040d001902c0c1400c100710312a40b2140120748040c2e15201036205d135507020502030f82c03c50110900108114000402c920300140c03140400b0303500c018680080084d6281e1074501103003140c0b400d092249401c0e5001104840c1440f0042015001003841022400041d104c180009000c001d11880c0e080003103842840954041d500c05c100303d402e030b030401c10700c000e0960304002a960b1080b203041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 83984200 1250 83982950 83982953
    0x1090203061c020d1104021b0c0108010806070f0f03060504051807060c02061606021b0a12090305030a030e0f01090b0a05100b030f130609050a12030606050d021b03040602150f04 78
    0x20540030341d040c5c0d000f45640040e8804c900424040e0191503400420030060403070b00501d0801c0418104000e00080e03840000d20f07a40c621a241d034547c0e0030b503074101c08956100c820751074642c40707040c00300c000000606003c58015a1240070908803802121040c54208000810004400301404282c1c010300686c6400b0038005040c2d00003e00520801000541d000d800c120007204201c1d2580603200c503400c102c0e280a049208260700161030b243c0100702202d0000b1449c8190001038081d090f89029a03802600450810503040323000d8000b40700d8008040c500384a140d07140c42c02c030700c4240a03210469100e500c40c40e40c2c50502d010b560f02034071005408081116a00b00c41072081c0c402c07200c162944444088000d00c0c032034039004000b050041849402600040c240400d00051140000c0d0701c008040c490746101194030603104046088035654080d101c0012030400480c80480806d8020b0f201000c290050fa1141200340000e4620316440f50b800400960842c5c0b20142078921100b10342a03004000d1aa0080740703103842d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 83985450 1250 83984200 83984209
    0x70e070c0b18120904090507120606080102030f060d020d051f0f0c0c0f032a120f0e151b0c0a0f12020103020f0c010504060209100c230a05010501090203061c02 70
    0x14240f1009450308082000394141e9030b01e0700410882034001090741c03107064940758400d402210300300c0207890780c6060510024400030140f003100d12582607500070070f42c5526080304224401d10403a40a981c8803a800c1912004034a0a1010041803400420b41030521401891080250f41e403e00386045042d03d811000d108240e00205038000341c550080da48220540c80349810b0f0342180c00d85560754015501001301c40c2a1510761905114503500400b820b0203540c186c1c1c401250440c0c0e80980c020001048107072544040e00340711281c140740c040001945400c246644071a41d43c40540c0b50449291540030307444400d00c0d41080030404000e04440034002001c2420462505280404044000e040650001c0c40c070001140c0701c000c0e2000315004000034005401c0c84c0c200500a5082001d000e07102d00c080002540515000d500c0260702c4941c0006240f1800c080180001121400003c01415600641551000084c8280f041c84e01030001c0c002c00503140d0511109201d02042c8000141000400e01d000c10b0001d070348c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 83986700 1250 83985450 83985463
    0x20307030206070c0f060302180306060d12020c040e01050601030b1f0806130e0708010c111906020c0a03080f01090507051c021306120b03011506050903070e070c0b18 73
    0x101502c00694400e840d2401c09031070451648100c800341260900171030416031680040c2003504078002c0039854901e0010030191211429600c40313522545110b000b100046000300040490b04850041d01c02e080300010120b420b0380c0648400115595480c0c4c00c0065640e0903200f8100315030010f807000707148040303240316054005031051684800e102c01c2500107459560360308543c00084803022810700024901c42045503581b1194065070b040ba5003024007400800f8030a000880799054854000c2400c2c441109a20a80c40b004080c107550040c1c08004d40320300703a9400c210703034146280b10342da5601d600d151080804904d0901a00201c0409041806019207036501c802511901900c42441200224914200b4030003880750943e100c214200f24000010020341100c4140009101548240044900401014200d074100d04078440040030720b01d010300c6280c1c414409049003400250498085a8513110404030701241281c8501c001042c3d1904c99040040c0d030700c03081e40c1020b80000002c010a00940c000b503210302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 83987950 1250 83986700 83986703
    0x108100513110406031a091203060d02010c0f060e030307020607020c09011e030b190605060901050f160209040b090d02010e0d1101060902040b04170601080c150d050c03100602060402030703 83
    0x50682d040101a80d441d5481400103651141500f03605040c0000408140c0c03000710f6925145000301c0c156910f005400c0011603218a10041c15452050001ea0041d1010011007038140c03444810522032800180035031003070b01440c0d982c080080d500c03485c011030000c1c50300700001c0c603134400c540180c413054045803141c1d00014191042e00c840103000103000d40300c40c58000c0f4654006480b203100305041c0000203000b000c25403411014408240030701078445080c4201480703414200c42c0010010000c0351428040c501c040c03c41d8003000d2800200100541e000941004001c2c0d4061310302c0c407542024031030860030070001810b4a9000340002d010000346052803a4443c118205500305000188000d07074800002940910090a01134100f1900c45840c2d100001c1240c026000380c101217505448040318503900051550304850004004050f520340070b10030700441a40d0003441c01402c0c1c8090003164420019406114401c1400030812522854410418201c04d2010f5110f0002d5400100600c80943c60100c1ca175016207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 83989200 1250 83987950 83987963
    0x913020a1d13110a031802090711031905040e0a18170903011401050a050109181d06070f0e0402040305030f03090312010303020f0111040602060402010f0203041802030108100513 78
    0x114031012801d01040d002c4442d01452804000307112003103210300a403201c0b00841c0e6042190f81c11488043c40c071482910300c0a0b41c4540c5100008070300f9841682403801c0511014160307400d0181046d01c5a52041b000e500040c0800c01c003150900c40403680c194551b50040c48441d0034070495040c896185010400b17410003030300c20900411022103d01c43c09048039640b49010300200b100161444411070346c28028011039101e0081501e00040315031240d254013040d120000e007541f4403e18101e0541004000340c500802800e41c44d04100b4201001c1401103d201d00c0f0a915560008400400e000f055038540c8440f0902c924410300092010840000a50704451490317000307a6903d032244025035155010366505010041120740001c0304050340403404104805120000380300e101d003401440c0390039000703600446006a2002c000200990312400c5003800c0480140192031420f9150107003400302203543e42d114680e0b550000010854842c040201764001c03840510100201d0030800b441070840301d032810000d44030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 83990450 1250 83989200 83989247
    0xf06050a06051315060201090209130201090f090507020d0f0c0f060e1204140301051b03071101060801061701060506030112050c030a0605040605060f01020601051512010603020913020a 81
    0x3082965070040000d40002040b410b0a1100794031050701030030540d03040843d803400c580e8000a2131401400b681191542c01802d202031a950102d0f05410700c10155010b9040140d0424001141010300c50307410050050030308042081e280180020385008001c0300e5407800c1142e0707440342c072203c650701644e032040d0384e41d00c014550345042090804101501410180100c00e00401d905940d280645100a000b2198004403500c511001402098204c40040700c1c19070001300ca81149854141a80f802580d0003500350030701358400c0b900003508030f086400d960010f07002c0c2e07995010b00740103201c802d0020204040c03188000344070b41400c240c04624580010700c104500c1c2d0200e4810b083c1040401c0c00a8945c64030081c0c01c5a004c0c1c0604d0234024003070a4103681c1076600a1030000422601c9c202861502c03104001a0000c01490340b034007042c464515201c86841d080b040f4113100380662001031048560081c5000c2d40d0150b1038400041c1000409003212014841840c4108000180c0d00e4101505450410744c1200a810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 83991700 1250 83990450 83990461
    0x206030a02040303081b0a05090a090e03030105031b0f1c060c021f0515010e030a12020303061507030906050d0b0901030f0309061107031203020706050a0615050708030f040c03050304030f1109040f0605 88
    0x500069400116955041800d0441490ce0000246049550480840e07084a484081c000b560401504a035a0130031000071009407503040401c45c104040000024290030650710340c450500311100c07800c00305d00580000c1045154216801d807100c900c141c6c050010402402c00c0c450159a100a4900311410300042c1e850030103250f5070901265040f02e070001076410350680c0458009440b588100c030600d215080001107040d0388034a0100340c40c503a560584602c002c1508100050740d076070f003184010000482e22112084c0e1240c8500440c180254410094248032031414600984200041c0c0c00800402100c1c2e0601c1d000b0190000f100001c403500180d040b407100c58885003c501911414001405103824001171181d11465a4002d008442280400d0314074503801c500200c0b5940700d80d00d40609007142c14408120840e0142002d1500035104d42da02c03549035603585c0d881b60b0444c2c11a83c8169031490141d42e000c0c0074005811190701660700200c90b500361310300e01542d42007007040302d051010b80120350304c400044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 83992807 1107 83991700 83991709
    0x106090b0d0213150605031e09070b0903010f2d022d04050414040606080a080706090311070902040504110906040513090206030a02040303081b0a0509 66
    0x105007158540070002c0c04208004a01022540c80e2001d0003d0400c4510000003031407180c44483d12803809602c5680200344e20600c1039031011045040002981c0085004003d41d10035101894071a090240424010071417000d04500c40e5141c802c68061440d2000c0b20710b00c000c02c0e84900e4444402c405074809080e8043c46101040a8840e8940304210540c411424610b0a0941c155281860341e10000030f4181c9a40c090445a08108403040c0024040540144c0c0094803a000081c10041141d03540c81210f0320808030050b141c59038071400881003500c1503200c0d046000c20380c01296a20381c0c5800d201402580180704462103140ba118128140030015000d031b80600d680140f000c0c0c101071501c01840102001482c40b010340316501d5000000680d140406103005420000300141c49030300b14a8090104000544045034440000190702d014000760800c4500742c1100d0726046848206d00700104 = true := by decide +kernel

theorem cover : BRFrame.Cov 83812950 83992807 := by
  have h0 := BRFrame.cov_init 83812950
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83812950 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 83812950 ≤ n) (h2 : n < 83992807) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
